import * as vscode from "vscode";
import * as path from "path";
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind,
} from "vscode-languageclient";
import { GoalsPanel } from "./GoalsPanel";
import { DomainInfo, GoalsResponse, TheoremStatus } from "../../protocol/types";
import { ProofState } from "../../proofStateUi/types";
import {
  completionsForLine,
  emptyDomainInfo,
  findTacticDoc,
  firstKeywordToken,
  isDomainInfo,
  operatorMatches,
  symbolCompletions,
  tacticHoverMarkdown,
} from "../../languageSupport/features";

let goalsPanel: GoalsPanel | undefined;
let languageClient: LanguageClient | undefined;
let lspStartupError: string | undefined;
let output: vscode.OutputChannel | undefined;
let reqSeq = 0;
let requestEpoch = 0;
let verifiedTheoremDecoration: vscode.TextEditorDecorationType | undefined;

type GoalsRequestResult = {
  state: ProofState;
  theoremStatuses: TheoremStatus[];
};

let domainInfo: DomainInfo = emptyDomainInfo();

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null;
}

function isGoalsResponse(value: unknown): value is GoalsResponse {
  if (!isRecord(value)) return false;
  if (typeof value.reqId !== "string") return false;
  if (!Array.isArray(value.diagnostics)) return false;
  if (value.kind === "ok") {
    return Array.isArray(value.goals);
  }
  if (value.kind === "no_goals") {
    return typeof value.reason === "string";
  }
  if (value.kind === "error") {
    return typeof value.code === "string" && typeof value.message === "string" && Array.isArray(value.goals);
  }
  return false;
}

function isTheoremStatus(value: unknown): value is TheoremStatus {
  return isRecord(value) &&
    typeof value.name === "string" &&
    typeof value.line === "number" &&
    typeof value.verified === "boolean";
}

const semanticTokenTypes = ["keyword", "operator", "comment"] as const;
const semanticLegend = new vscode.SemanticTokensLegend([...semanticTokenTypes], []);

function ensureGoalsPanel(
  context: vscode.ExtensionContext,
  preserveFocus = false
): GoalsPanel {
  if (!goalsPanel || goalsPanel.isDisposed()) {
    goalsPanel = GoalsPanel.createOrShow(context, vscode.ViewColumn.Beside, preserveFocus);
  } else {
    goalsPanel.reveal(vscode.ViewColumn.Beside, preserveFocus);
  }
  return goalsPanel;
}

function hasGoalsPanel(): boolean {
  return !!goalsPanel && !goalsPanel.isDisposed();
}

function isMyPaEditor(editor: vscode.TextEditor | undefined): editor is vscode.TextEditor {
  return !!editor && editor.document.languageId === "mypa";
}

function findMyPaEditor(): vscode.TextEditor | undefined {
  const active = vscode.window.activeTextEditor;
  if (isMyPaEditor(active)) return active;
  return vscode.window.visibleTextEditors.find((e) => e.document.languageId === "mypa");
}

function isMyPaFilename(doc: vscode.TextDocument): boolean {
  return doc.fileName.toLowerCase().endsWith(".mypa");
}

async function ensureMyPaLanguage(doc: vscode.TextDocument): Promise<void> {
  if (doc.languageId === "mypa") return;
  if (!isMyPaFilename(doc)) return;
  await vscode.languages.setTextDocumentLanguage(doc, "mypa");
}

async function startLanguageClient(context: vscode.ExtensionContext) {
  const cfg = vscode.workspace.getConfiguration("mypa");
  const configuredPath = cfg.get<string>("lspServerPath")?.trim();
  const serverModule =
    configuredPath || path.resolve(context.extensionPath, "out", "lsp_server", "src", "server.js");
  output?.appendLine(`[mypa] lsp.serverModule=${serverModule}`);
  if (configuredPath) {
    output?.appendLine("[mypa] lsp.serverModule source=config(mypa.lspServerPath)");
  } else {
    output?.appendLine("[mypa] lsp.serverModule source=default");
  }

  const serverOptions: ServerOptions = {
    run: { module: serverModule, transport: TransportKind.stdio },
    debug: { module: serverModule, transport: TransportKind.stdio },
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: "file", language: "mypa" }],
  };

  languageClient = new LanguageClient("mypa-lsp", "MyPA Language Server", serverOptions, clientOptions);
  context.subscriptions.push(languageClient.start());
  await languageClient.onReady();
}

async function loadDomainInfo(): Promise<void> {
  if (!languageClient) {
    domainInfo = emptyDomainInfo();
    return;
  }
  try {
    const response = await languageClient.sendRequest<unknown>("mypa/domainInfo");
    domainInfo = isDomainInfo(response) ? response : emptyDomainInfo();
  } catch (err) {
    domainInfo = emptyDomainInfo();
    output?.appendLine(`[mypa] domainInfo failed: ${(err as Error).message}`);
  }
}

function applyTheoremDecorations(editor: vscode.TextEditor, statuses: TheoremStatus[]) {
  if (!verifiedTheoremDecoration) {
    return;
  }
  const ranges = statuses
    .filter((status) => status.verified)
    .map((status) => new vscode.Range(status.line, 0, status.line, 0));
  editor.setDecorations(verifiedTheoremDecoration, ranges);
}

async function requestGoals(editor: vscode.TextEditor): Promise<GoalsRequestResult> {
  if (lspStartupError) {
    return {
      state: { goals: [
        {
          id: "lsp:start-error",
          hypotheses: [],
          target: lspStartupError,
        },
      ] },
      theoremStatuses: [],
    };
  }

  if (!languageClient) {
    return {
      state: { goals: [
        {
          id: "lsp:error",
          hypotheses: [],
          target: "Language server is not initialized.",
        },
      ] },
      theoremStatuses: [],
    };
  }

  const pos = editor.selection.active;
  const reqId = `g-${++reqSeq}`;
  output?.appendLine(
    `[mypa] goals.request reqId=${reqId} uri=${editor.document.uri.toString()} line=${pos.line + 1} col=${pos.character + 1}`
  );
  try {
    const request = languageClient.sendRequest<GoalsResponse>("mypa/goals", {
      reqId,
      uri: editor.document.uri.toString(),
      line: pos.line,
      character: pos.character,
    });
    const timeout = new Promise<GoalsResponse>((_, reject) =>
      setTimeout(() => reject(new Error("Goals request timed out after 4000ms.")), 4000)
    );
    const response = await Promise.race([request, timeout]);
    if (!isGoalsResponse(response)) {
      throw new Error(`Invalid goals response shape for reqId=${reqId}`);
    }
    const theoremStatuses = Array.isArray(response.theoremStatuses)
      ? response.theoremStatuses.filter(isTheoremStatus)
      : [];
    output?.appendLine(
      `[mypa] goals.response reqId=${response.reqId} kind=${response.kind} diagnostics=${response.diagnostics.length}`
    );
    if (response.kind === "ok") {
      output?.appendLine(`[mypa] goals.ok reqId=${response.reqId} goalCount=${response.goals.length}`);
      return { state: { goals: response.goals, display: response.display }, theoremStatuses };
    }
    if (response.kind === "no_goals") {
      output?.appendLine(`[mypa] goals.no_goals reqId=${response.reqId} reason=${response.reason}`);
      return {
        state: { goals: [], display: response.display, tone: "normal" },
        theoremStatuses,
      };
    }
    return {
      state: {
        goals: [],
        display: response.display
          ? { ...response.display, status: response.message }
          : {
              title: "",
              status: response.message,
              sections: [],
            },
        tone: "error",
      },
      theoremStatuses,
    };
  } catch (err) {
    output?.appendLine(`[mypa] requestGoals failed: ${(err as Error).stack || String(err)}`);
    void vscode.window.showErrorMessage(`MyPA goals request failed: ${(err as Error).message}`);
    return {
      state: { goals: [
        {
          id: "lsp:error",
          hypotheses: [],
          target: `Goals request failed: ${(err as Error).message}`,
        },
      ], tone: "error" },
      theoremStatuses: [],
    };
  }
}

async function refreshGoalsFromEditor(options: {
  context: vscode.ExtensionContext;
  editor: vscode.TextEditor;
  createPanelIfMissing: boolean;
  revealPanel: boolean;
}) {
  const { context, editor, createPanelIfMissing, revealPanel } = options;
  if (editor.document.languageId !== "mypa") {
    output?.appendLine(`[mypa] goals.skip reason=non_mypa_editor language=${editor.document.languageId}`);
    return;
  }

  if (createPanelIfMissing) {
    ensureGoalsPanel(context, !revealPanel);
  } else if (!hasGoalsPanel()) {
    output?.appendLine("[mypa] goals.skip reason=no_panel");
    return;
  } else if (revealPanel) {
    goalsPanel?.reveal(vscode.ViewColumn.Beside, false);
  }

  const myEpoch = ++requestEpoch;
  const result = await requestGoals(editor);
  if (myEpoch !== requestEpoch) {
    output?.appendLine(`[mypa] goals.drop reason=stale_response epoch=${myEpoch} current=${requestEpoch}`);
    return;
  }
  goalsPanel?.setProofState(result.state);
  applyTheoremDecorations(editor, result.theoremStatuses);
}

async function autoShowForMyPaEditor(
  context: vscode.ExtensionContext,
  editor: vscode.TextEditor | undefined
): Promise<void> {
  if (!editor) {
    return;
  }
  await ensureMyPaLanguage(editor.document);
  if (!isMyPaEditor(editor)) {
    return;
  }
  await refreshGoalsFromEditor({
    context,
    editor,
    createPanelIfMissing: true,
    revealPanel: false,
  });
}

export async function activate(context: vscode.ExtensionContext) {
  output = vscode.window.createOutputChannel("MyPA");
  context.subscriptions.push(output);
  verifiedTheoremDecoration = vscode.window.createTextEditorDecorationType({
    gutterIconPath: vscode.Uri.joinPath(context.extensionUri, "media", "proof-complete.svg"),
    gutterIconSize: "contain",
  });
  context.subscriptions.push(verifiedTheoremDecoration);

  try {
    await startLanguageClient(context);
    await loadDomainInfo();
    lspStartupError = undefined;
    output.appendLine("[mypa] language client started");
  } catch (err) {
    lspStartupError = `LSP startup failed: ${(err as Error).message}`;
    output.appendLine(`[mypa] ${lspStartupError}`);
    output.appendLine(String((err as Error).stack || ""));
    void vscode.window.showErrorMessage(lspStartupError);
  }

  context.subscriptions.push(
    vscode.commands.registerCommand("mypa.showGoals", async () => {
      let ed = findMyPaEditor();
      if (!ed) {
        ensureGoalsPanel(context, true);
        goalsPanel?.setProofState({
          goals: [{ id: "lsp:error", hypotheses: [], target: "No active editor." }],
        });
        return;
      }

      await ensureMyPaLanguage(ed.document);
      ed = findMyPaEditor();
      if (!ed || !isMyPaEditor(ed)) {
        ensureGoalsPanel(context, true);
        goalsPanel?.setProofState({
          goals: [
            {
              id: "lsp:error",
              hypotheses: [],
              target: "Active file is not in MyPA language mode. Use a .mypa file.",
            },
          ],
        });
        return;
      }
      await refreshGoalsFromEditor({
        context,
        editor: ed,
        createPanelIfMissing: true,
        revealPanel: true,
      });
    })
  );

  let timer: NodeJS.Timeout | undefined;
  const scheduleUpdate = () => {
    if (timer) {
      clearTimeout(timer);
    }

    timer = setTimeout(async () => {
      let ed = findMyPaEditor();
      if (!ed) {
        output?.appendLine("[mypa] goals.skip reason=no_editor");
        return;
      }

      await ensureMyPaLanguage(ed.document);
      ed = findMyPaEditor();
      if (!ed || !isMyPaEditor(ed)) {
        // Keep prior state when no MyPA editor is focused; do not clobber with false errors.
        output?.appendLine("[mypa] goals.skip reason=not_mypa_after_language_ensure");
        return;
      }

      await refreshGoalsFromEditor({
        context,
        editor: ed,
        createPanelIfMissing: false,
        revealPanel: false,
      });
    }, 150);
  };

  context.subscriptions.push(
    vscode.window.onDidChangeActiveTextEditor((editor) => {
      void autoShowForMyPaEditor(context, editor);
      scheduleUpdate();
    })
  );

  context.subscriptions.push(
    vscode.window.onDidChangeTextEditorSelection((e) => {
      if (e.textEditor.document.languageId !== "mypa") {
        return;
      }
      scheduleUpdate();
    })
  );

  context.subscriptions.push(
    vscode.workspace.onDidChangeTextDocument((e) => {
      if (e.document.languageId !== "mypa") {
        return;
      }
      scheduleUpdate();
    })
  );

  context.subscriptions.push(
    vscode.workspace.onDidOpenTextDocument((doc) => {
      void ensureMyPaLanguage(doc).then(async () => {
        const editor = vscode.window.visibleTextEditors.find((e) => e.document === doc);
        await autoShowForMyPaEditor(context, editor);
        scheduleUpdate();
      });
    })
  );

  const completionProvider = vscode.languages.registerCompletionItemProvider(
    { language: "mypa" },
    {
      provideCompletionItems(doc, position) {
        const linePrefix = doc.lineAt(position.line).text.slice(0, position.character);

        const lineCompletions = completionsForLine(domainInfo, linePrefix);
        if (lineCompletions.length) {
          return lineCompletions.map((c) => {
            const kind = c.kind === "system" ? vscode.CompletionItemKind.Reference : vscode.CompletionItemKind.Keyword;
            const item = new vscode.CompletionItem(c.label, kind);
            item.insertText = c.insertText;
            item.detail = c.detail;
            if (c.documentation) {
              item.documentation = c.documentation;
            }
            item.range = new vscode.Range(
              position.line,
              c.replaceStartCharacter ?? position.character,
              position.line,
              position.character
            );
            return item;
          });
        }

        const range = doc.getWordRangeAtPosition(position, /\\[\w]*/);
        const prefix = range ? doc.getText(range) : "";

        const items = symbolCompletions(domainInfo, prefix)
          .map((c) => {
            const item = new vscode.CompletionItem(c.label, vscode.CompletionItemKind.Snippet);
            item.insertText = c.insertText;
            item.detail = c.detail;
            if (c.documentation) {
              item.documentation = c.documentation;
            }
            item.range = range;
            return item;
          });
        return items;
      },
    },
    "\\",
    "#",
    " "
  );
  context.subscriptions.push(completionProvider);

  const hoverProvider = vscode.languages.registerHoverProvider({ language: "mypa" }, {
    provideHover(doc, position) {
      const range = doc.getWordRangeAtPosition(position, /[A-Za-z_][A-Za-z0-9_]*/);
      if (!range) return null;
      const word = doc.getText(range).toLowerCase();
      const rule = findTacticDoc(domainInfo, word);
      if (!rule) return null;
      const md = new vscode.MarkdownString();
      md.isTrusted = false;
      md.appendMarkdown(tacticHoverMarkdown(rule));
      return new vscode.Hover(md, range);
    },
  });
  context.subscriptions.push(hoverProvider);

  const semanticProvider = vscode.languages.registerDocumentSemanticTokensProvider(
    { language: "mypa" },
    {
      provideDocumentSemanticTokens(doc) {
        const builder = new vscode.SemanticTokensBuilder(semanticLegend);

        for (let line = 0; line < doc.lineCount; line++) {
          const text = doc.lineAt(line).text;
          const trimmed = text.trim();

          if (trimmed.startsWith("--")) {
            builder.push(line, 0, text.length, semanticTokenTypes.indexOf("comment"), 0);
            continue;
          }

          const keyword = firstKeywordToken(domainInfo, text);
          if (keyword) {
            builder.push(line, keyword.start, keyword.length, semanticTokenTypes.indexOf("keyword"), 0);
          }

          for (const op of operatorMatches(domainInfo, text)) {
            builder.push(line, op.start, op.length, semanticTokenTypes.indexOf("operator"), 0);
          }
        }

        return builder.build();
      },
    },
    semanticLegend
  );
  context.subscriptions.push(semanticProvider);

  // Ensure a first refresh after activation so users do not depend on manual edits.
  void autoShowForMyPaEditor(context, vscode.window.activeTextEditor);
  scheduleUpdate();
}

export async function deactivate() {
  goalsPanel?.dispose();
  goalsPanel = undefined;
  output?.dispose();
  output = undefined;
  if (languageClient) {
    await languageClient.stop();
    languageClient = undefined;
  }
}
