import * as vscode from "vscode";
import * as path from "path";
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind,
} from "vscode-languageclient";
import { GoalsPanel, ProofState } from "./GoalsPanel";

let goalsPanel: GoalsPanel | undefined;
let languageClient: LanguageClient | undefined;
let lspStartupError: string | undefined;
let output: vscode.OutputChannel | undefined;
let reqSeq = 0;
let requestEpoch = 0;
let verifiedTheoremDecoration: vscode.TextEditorDecorationType | undefined;

type Completion = {
  label: string;
  insertText: string;
  detail?: string;
  documentation?: string;
};

type DirectiveCompletion = {
  label: string;
  insertText: string;
  detail?: string;
  documentation?: string;
  kind?: vscode.CompletionItemKind;
};

type GoalsResponse =
  | { kind: "ok"; reqId: string; goals: ProofState["goals"]; diagnostics: unknown[]; display?: ProofState["display"]; theoremStatuses?: TheoremStatus[] }
  | { kind: "no_goals"; reqId: string; reason: string; diagnostics: unknown[]; display?: ProofState["display"]; theoremStatuses?: TheoremStatus[] }
  | {
      kind: "error";
      reqId: string;
      code: string;
      message: string;
      diagnostics: unknown[];
      goals: ProofState["goals"];
      display?: ProofState["display"];
      theoremStatuses?: TheoremStatus[];
    };

type TheoremStatus = {
  name: string;
  line: number;
  verified: boolean;
};

type GoalsRequestResult = {
  state: ProofState;
  theoremStatuses: TheoremStatus[];
};

type RuleHover = {
  title: string;
  display: string;
  latex: string;
};

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

const ruleHovers: Record<string, RuleHover> = {
  ax: {
    title: "Axiom",
    display: "A ⊢ A",
    latex: String.raw`\frac{}{A \vdash A}\ \mathrm{ax}`,
  },
  rlolli: {
    title: "Right Lolli",
    display: "Γ, A ⊢ B, Δ\n────────────── rlolli\nΓ ⊢ A ⊸ B, Δ",
    latex: String.raw`\frac{\Gamma, A \vdash B, \Delta}{\Gamma \vdash A \multimap B, \Delta}\ \mathrm{rlolli}`,
  },
  rtensor: {
    title: "Right Tensor",
    display: "Γ ⊢ A, Δ    Π ⊢ B, Σ\n──────────────────── rtensor\nΓ, Π ⊢ A ⊗ B, Δ, Σ",
    latex: String.raw`\frac{\Gamma \vdash A, \Delta \qquad \Pi \vdash B, \Sigma}{\Gamma, \Pi \vdash A \otimes B, \Delta, \Sigma}\ \mathrm{rtensor}`,
  },
  rwith: {
    title: "Right With",
    display: "Γ ⊢ A, Δ    Γ ⊢ B, Δ\n──────────────────── rwith\nΓ ⊢ A & B, Δ",
    latex: String.raw`\frac{\Gamma \vdash A, \Delta \qquad \Gamma \vdash B, \Delta}{\Gamma \vdash A \mathbin{\&} B, \Delta}\ \mathrm{rwith}`,
  },
  lleft: {
    title: "Left With-1",
    display: "Γ, A ⊢ Δ\n────────── lleft at h\nΓ, A & B ⊢ Δ",
    latex: String.raw`\frac{\Gamma, A \vdash \Delta}{\Gamma, A \mathbin{\&} B \vdash \Delta}\ \mathrm{lleft}`,
  },
  lright: {
    title: "Left With-2",
    display: "Γ, B ⊢ Δ\n────────── lright at h\nΓ, A & B ⊢ Δ",
    latex: String.raw`\frac{\Gamma, B \vdash \Delta}{\Gamma, A \mathbin{\&} B \vdash \Delta}\ \mathrm{lright}`,
  },
  ltensor: {
    title: "Left Tensor",
    display: "Γ, A, B ⊢ Δ\n──────────── ltensor at h\nΓ, A ⊗ B ⊢ Δ",
    latex: String.raw`\frac{\Gamma, A, B \vdash \Delta}{\Gamma, A \otimes B \vdash \Delta}\ \mathrm{ltensor}`,
  },
  lplus: {
    title: "Left Plus",
    display: "Γ, A ⊢ Δ    Γ, B ⊢ Δ\n──────────────────── lplus at h\nΓ, A ⊕ B ⊢ Δ",
    latex: String.raw`\frac{\Gamma, A \vdash \Delta \qquad \Gamma, B \vdash \Delta}{\Gamma, A \oplus B \vdash \Delta}\ \mathrm{lplus}`,
  },
  rplusl: {
    title: "Right Plus-1",
    display: "Γ ⊢ A, Δ\n────────── rplusl\nΓ ⊢ A ⊕ B, Δ",
    latex: String.raw`\frac{\Gamma \vdash A, \Delta}{\Gamma \vdash A \oplus B, \Delta}\ \mathrm{rplusl}`,
  },
  rplusr: {
    title: "Right Plus-2",
    display: "Γ ⊢ B, Δ\n────────── rplusr\nΓ ⊢ A ⊕ B, Δ",
    latex: String.raw`\frac{\Gamma \vdash B, \Delta}{\Gamma \vdash A \oplus B, \Delta}\ \mathrm{rplusr}`,
  },
  rpar: {
    title: "Right Par",
    display: "Γ ⊢ A, B, Δ\n──────────── rpar\nΓ ⊢ A ⅋ B, Δ",
    latex: String.raw`\frac{\Gamma \vdash A, B, \Delta}{\Gamma \vdash A \parr B, \Delta}\ \mathrm{rpar}`,
  },
  llolli: {
    title: "Left Lolli",
    display: "Γ ⊢ A, Δ    Π, B ⊢ Σ\n──────────────────── llolli at h\nΓ, Π, A ⊸ B ⊢ Δ, Σ",
    latex: String.raw`\frac{\Gamma \vdash A, \Delta \qquad \Pi, B \vdash \Sigma}{\Gamma, \Pi, A \multimap B \vdash \Delta, \Sigma}\ \mathrm{llolli}`,
  },
  intro: {
    title: "Implication Introduction",
    display: "A, Γ ⊢ B\n────────── intro h\nΓ ⊢ A ⟶ B",
    latex: String.raw`\frac{A, \Gamma \vdash B}{\Gamma \vdash A \to B}\ \mathrm{intro}`,
  },
  assumption: {
    title: "Assumption",
    display: "A ∈ Γ\n────── assumption h\nΓ ⊢ A",
    latex: String.raw`\frac{}{\,\Gamma \vdash A\,}\ \mathrm{assumption}`,
  },
  constructor: {
    title: "Conjunction Introduction",
    display: "Γ ⊢ A    Γ ⊢ B\n──────────────── constructor\nΓ ⊢ A ∧ B",
    latex: String.raw`\frac{\Gamma \vdash A \qquad \Gamma \vdash B}{\Gamma \vdash A \land B}\ \mathrm{constructor}`,
  },
  left: {
    title: "Left Rule",
    display: "Goal: Γ ⊢ A ∨ B  gives Γ ⊢ A\nHyp: h : A ∧ B gives h : A",
    latex: String.raw`\frac{\Gamma \vdash A}{\Gamma \vdash A \lor B}\ \mathrm{left}`,
  },
  right: {
    title: "Right Rule",
    display: "Goal: Γ ⊢ A ∨ B  gives Γ ⊢ B\nHyp: h : A ∧ B gives h : B",
    latex: String.raw`\frac{\Gamma \vdash B}{\Gamma \vdash A \lor B}\ \mathrm{right}`,
  },
  cases: {
    title: "Disjunction Elimination",
    display: "Γ ⊢ A ∨ B    A, Γ ⊢ C    B, Γ ⊢ C\n──────────────────────────── cases at h as hp hq\nΓ ⊢ C",
    latex: String.raw`\frac{\Gamma \vdash A \lor B \qquad A, \Gamma \vdash C \qquad B, \Gamma \vdash C}{\Gamma \vdash C}\ \mathrm{cases}`,
  },
  apply: {
    title: "Implication Elimination",
    display: "h : A ⟶ B    Goal: B\n──────────── apply h\nNew goal: A",
    latex: String.raw`\frac{\Gamma \vdash A \to B \qquad \Gamma \vdash A}{\Gamma \vdash B}\ \mathrm{apply}`,
  },
  exfalso: {
    title: "Bottom Goal",
    display: "Goal: C\n──────── exfalso\nGoal: ⊥",
    latex: String.raw`\frac{\Gamma \vdash \bot}{\Gamma \vdash C}\ \mathrm{exfalso}`,
  },
  absurd: {
    title: "Bottom Elimination",
    display: "h : ⊥\n────── absurd h\nΓ ⊢ C",
    latex: String.raw`\frac{\Gamma \vdash \bot}{\Gamma \vdash C}\ \mathrm{absurd}`,
  },
  by_contra: {
    title: "Classical Rule",
    display: "(A ⟶ ⊥), Γ ⊢ ⊥\n──────────────── by_contra h\nΓ ⊢ A",
    latex: String.raw`\frac{(\neg A), \Gamma \vdash \bot}{\Gamma \vdash A}\ \mathrm{by\_contra}`,
  },
};

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
    configuredPath || path.resolve(context.extensionPath, "..", "lsp_server", "out", "server.js");
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

  const completions: Completion[] = [
    { label: "\\otimes", insertText: "⊗", detail: "tensor / times" },
    { label: "\\tensor", insertText: "⊗", detail: "tensor / times" },
    { label: "\\lolli", insertText: "⊸", detail: "lollipop / implication" },
    { label: "\\with", insertText: "&", detail: "with" },
    { label: "\\plus", insertText: "⊕", detail: "plus" },
    { label: "\\oplus", insertText: "⊕", detail: "plus" },
    { label: "\\top", insertText: "⊤", detail: "top" },
    { label: "\\bot", insertText: "⊥", detail: "bottom" },
    { label: "\\bottom", insertText: "⊥", detail: "bottom" },
    { label: "\\one", insertText: "1", detail: "one" },
    { label: "\\zero", insertText: "0", detail: "zero" },
    { label: "\\bang", insertText: "!", detail: "of course" },
  ];

  const directiveCompletions: DirectiveCompletion[] = [
    {
      label: "#help",
      insertText: "#help ",
      detail: "Show formal-system help",
      documentation: "Display the language and inference rules for a supported formal system.",
      kind: vscode.CompletionItemKind.Keyword,
    },
  ];

  const helpSystemCompletions: DirectiveCompletion[] = [
    {
      label: "cllp_gentzen",
      insertText: "cllp_gentzen",
      detail: "Classical linear logic, Gentzen sequent calculus",
      documentation: "Urzyczyn-style classical linear propositional calculus in sequent form.",
      kind: vscode.CompletionItemKind.Reference,
    },
    {
      label: "ipc_nd",
      insertText: "ipc_nd",
      detail: "Intuitionistic propositional calculus, natural deduction",
      documentation: "IPC with ∧, ∨, ⟶, and ⊥ in natural deduction.",
      kind: vscode.CompletionItemKind.Reference,
    },
    {
      label: "cpc_nd",
      insertText: "cpc_nd",
      detail: "Classical propositional calculus, natural deduction",
      documentation: "CPC with ∧, ∨, ⟶, and ⊥ in natural deduction.",
      kind: vscode.CompletionItemKind.Reference,
    },
  ];

  const completionProvider = vscode.languages.registerCompletionItemProvider(
    { language: "mypa" },
    {
      provideCompletionItems(doc, position) {
        const linePrefix = doc.lineAt(position.line).text.slice(0, position.character);

        if (linePrefix.startsWith("#help ")) {
          const systemPrefix = linePrefix.slice("#help ".length).trimLeft();
          return helpSystemCompletions
            .filter((c) => !systemPrefix || c.label.startsWith(systemPrefix))
            .map((c) => {
              const item = new vscode.CompletionItem(
                c.label,
                c.kind ?? vscode.CompletionItemKind.Reference
              );
              item.insertText = c.insertText;
              item.detail = c.detail;
              if (c.documentation) {
                item.documentation = c.documentation;
              }
              const startCol = "#help ".length;
              item.range = new vscode.Range(
                position.line,
                startCol,
                position.line,
                position.character
              );
              return item;
            });
        }

        if (/^\s*#\w*$/.test(linePrefix) || /^\s*#$/.test(linePrefix)) {
          const directivePrefix = linePrefix.trimLeft();
          return directiveCompletions
            .filter((c) => !directivePrefix || c.label.startsWith(directivePrefix))
            .map((c) => {
              const item = new vscode.CompletionItem(
                c.label,
                c.kind ?? vscode.CompletionItemKind.Keyword
              );
              item.insertText = c.insertText;
              item.detail = c.detail;
              if (c.documentation) {
                item.documentation = c.documentation;
              }
              const hashCol = linePrefix.indexOf("#");
              item.range = new vscode.Range(
                position.line,
                Math.max(hashCol, 0),
                position.line,
                position.character
              );
              return item;
            });
        }

        const range = doc.getWordRangeAtPosition(position, /\\[\w]*/);
        const prefix = range ? doc.getText(range) : "";

        const items = completions
          .filter((c) => !prefix || c.label.startsWith(prefix))
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
      const rule = ruleHovers[word];
      if (!rule) return null;
      const md = new vscode.MarkdownString();
      md.isTrusted = false;
      md.appendMarkdown(`**${rule.title}**\n\n`);
      md.appendCodeblock(rule.display, "text");
      return new vscode.Hover(md, range);
    },
  });
  context.subscriptions.push(hoverProvider);

  const keywordSet = new Set(
    [
      "theorem",
      "def",
      "using",
      "ax",
      "lx",
      "rx",
      "lleft",
      "lright",
      "ltensor",
      "lplus",
      "lpar",
      "llolli",
      "lneg",
      "lone",
      "lzero",
      "lbottom",
      "lbang",
      "lwhynot",
      "rwith",
      "rtensor",
      "rplusl",
      "rplusr",
      "rpar",
      "rlolli",
      "rneg",
      "rone",
      "rbottom",
      "rtop",
      "rbang",
      "rwhynot",
      "wbang",
      "wwhynot",
      "cbang",
      "cwhynot",
      "cut",
      "type_intro",
      "type_apply",
      "exact",
    ].map((k) => k.toLowerCase())
  );
  const operatorRe = /[⊗⊕&!:]/g;

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

          const firstWord = (trimmed.match(/^([^\s]+)/) || [])[1];
          if (firstWord && keywordSet.has(firstWord.toLowerCase())) {
            const start = text.indexOf(firstWord);
            builder.push(line, start, firstWord.length, semanticTokenTypes.indexOf("keyword"), 0);
          }

          operatorRe.lastIndex = 0;
          let m: RegExpExecArray | null;
          while ((m = operatorRe.exec(text))) {
            builder.push(line, m.index, 1, semanticTokenTypes.indexOf("operator"), 0);
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
