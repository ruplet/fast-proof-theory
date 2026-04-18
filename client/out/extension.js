"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.activate = activate;
exports.deactivate = deactivate;
const vscode = __importStar(require("vscode"));
const path = __importStar(require("path"));
const vscode_languageclient_1 = require("vscode-languageclient");
const GoalsPanel_1 = require("./GoalsPanel");
let goalsPanel;
let languageClient;
let lspStartupError;
let output;
let reqSeq = 0;
let requestEpoch = 0;
let verifiedTheoremDecoration;
function isRecord(value) {
    return typeof value === "object" && value !== null;
}
function isGoalsResponse(value) {
    if (!isRecord(value))
        return false;
    if (typeof value.reqId !== "string")
        return false;
    if (!Array.isArray(value.diagnostics))
        return false;
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
function isTheoremStatus(value) {
    return isRecord(value) &&
        typeof value.name === "string" &&
        typeof value.line === "number" &&
        typeof value.verified === "boolean";
}
const semanticTokenTypes = ["keyword", "operator", "comment"];
const semanticLegend = new vscode.SemanticTokensLegend([...semanticTokenTypes], []);
const ruleHovers = {
    ax: {
        title: "Axiom",
        display: "A ⊢ A",
        latex: String.raw `\frac{}{A \vdash A}\ \mathrm{ax}`,
    },
    rlolli: {
        title: "Right Lolli",
        display: "Γ, A ⊢ B, Δ\n────────────── rlolli\nΓ ⊢ A ⊸ B, Δ",
        latex: String.raw `\frac{\Gamma, A \vdash B, \Delta}{\Gamma \vdash A \multimap B, \Delta}\ \mathrm{rlolli}`,
    },
    rtensor: {
        title: "Right Tensor",
        display: "Γ ⊢ A, Δ    Π ⊢ B, Σ\n──────────────────── rtensor\nΓ, Π ⊢ A ⊗ B, Δ, Σ",
        latex: String.raw `\frac{\Gamma \vdash A, \Delta \qquad \Pi \vdash B, \Sigma}{\Gamma, \Pi \vdash A \otimes B, \Delta, \Sigma}\ \mathrm{rtensor}`,
    },
    rwith: {
        title: "Right With",
        display: "Γ ⊢ A, Δ    Γ ⊢ B, Δ\n──────────────────── rwith\nΓ ⊢ A & B, Δ",
        latex: String.raw `\frac{\Gamma \vdash A, \Delta \qquad \Gamma \vdash B, \Delta}{\Gamma \vdash A \mathbin{\&} B, \Delta}\ \mathrm{rwith}`,
    },
    lleft: {
        title: "Left With-1",
        display: "Γ, A ⊢ Δ\n────────── lleft at h\nΓ, A & B ⊢ Δ",
        latex: String.raw `\frac{\Gamma, A \vdash \Delta}{\Gamma, A \mathbin{\&} B \vdash \Delta}\ \mathrm{lleft}`,
    },
    lright: {
        title: "Left With-2",
        display: "Γ, B ⊢ Δ\n────────── lright at h\nΓ, A & B ⊢ Δ",
        latex: String.raw `\frac{\Gamma, B \vdash \Delta}{\Gamma, A \mathbin{\&} B \vdash \Delta}\ \mathrm{lright}`,
    },
    ltensor: {
        title: "Left Tensor",
        display: "Γ, A, B ⊢ Δ\n──────────── ltensor at h\nΓ, A ⊗ B ⊢ Δ",
        latex: String.raw `\frac{\Gamma, A, B \vdash \Delta}{\Gamma, A \otimes B \vdash \Delta}\ \mathrm{ltensor}`,
    },
    lplus: {
        title: "Left Plus",
        display: "Γ, A ⊢ Δ    Γ, B ⊢ Δ\n──────────────────── lplus at h\nΓ, A ⊕ B ⊢ Δ",
        latex: String.raw `\frac{\Gamma, A \vdash \Delta \qquad \Gamma, B \vdash \Delta}{\Gamma, A \oplus B \vdash \Delta}\ \mathrm{lplus}`,
    },
    rplusl: {
        title: "Right Plus-1",
        display: "Γ ⊢ A, Δ\n────────── rplusl\nΓ ⊢ A ⊕ B, Δ",
        latex: String.raw `\frac{\Gamma \vdash A, \Delta}{\Gamma \vdash A \oplus B, \Delta}\ \mathrm{rplusl}`,
    },
    rplusr: {
        title: "Right Plus-2",
        display: "Γ ⊢ B, Δ\n────────── rplusr\nΓ ⊢ A ⊕ B, Δ",
        latex: String.raw `\frac{\Gamma \vdash B, \Delta}{\Gamma \vdash A \oplus B, \Delta}\ \mathrm{rplusr}`,
    },
    rpar: {
        title: "Right Par",
        display: "Γ ⊢ A, B, Δ\n──────────── rpar\nΓ ⊢ A ⅋ B, Δ",
        latex: String.raw `\frac{\Gamma \vdash A, B, \Delta}{\Gamma \vdash A \parr B, \Delta}\ \mathrm{rpar}`,
    },
    llolli: {
        title: "Left Lolli",
        display: "Γ ⊢ A, Δ    Π, B ⊢ Σ\n──────────────────── llolli at h\nΓ, Π, A ⊸ B ⊢ Δ, Σ",
        latex: String.raw `\frac{\Gamma \vdash A, \Delta \qquad \Pi, B \vdash \Sigma}{\Gamma, \Pi, A \multimap B \vdash \Delta, \Sigma}\ \mathrm{llolli}`,
    },
};
function ensureGoalsPanel(context, preserveFocus = false) {
    if (!goalsPanel || goalsPanel.isDisposed()) {
        goalsPanel = GoalsPanel_1.GoalsPanel.createOrShow(context, vscode.ViewColumn.Beside, preserveFocus);
    }
    else {
        goalsPanel.reveal(vscode.ViewColumn.Beside, preserveFocus);
    }
    return goalsPanel;
}
function hasGoalsPanel() {
    return !!goalsPanel && !goalsPanel.isDisposed();
}
function isMyPaEditor(editor) {
    return !!editor && editor.document.languageId === "mypa";
}
function findMyPaEditor() {
    const active = vscode.window.activeTextEditor;
    if (isMyPaEditor(active))
        return active;
    return vscode.window.visibleTextEditors.find((e) => e.document.languageId === "mypa");
}
function isMyPaFilename(doc) {
    return doc.fileName.toLowerCase().endsWith(".mypa");
}
async function ensureMyPaLanguage(doc) {
    if (doc.languageId === "mypa")
        return;
    if (!isMyPaFilename(doc))
        return;
    await vscode.languages.setTextDocumentLanguage(doc, "mypa");
}
async function startLanguageClient(context) {
    const cfg = vscode.workspace.getConfiguration("mypa");
    const configuredPath = cfg.get("lspServerPath")?.trim();
    const serverModule = configuredPath || path.resolve(context.extensionPath, "..", "lsp_server", "out", "server.js");
    output?.appendLine(`[mypa] lsp.serverModule=${serverModule}`);
    if (configuredPath) {
        output?.appendLine("[mypa] lsp.serverModule source=config(mypa.lspServerPath)");
    }
    else {
        output?.appendLine("[mypa] lsp.serverModule source=default");
    }
    const serverOptions = {
        run: { module: serverModule, transport: vscode_languageclient_1.TransportKind.stdio },
        debug: { module: serverModule, transport: vscode_languageclient_1.TransportKind.stdio },
    };
    const clientOptions = {
        documentSelector: [{ scheme: "file", language: "mypa" }],
    };
    languageClient = new vscode_languageclient_1.LanguageClient("mypa-lsp", "MyPA Language Server", serverOptions, clientOptions);
    context.subscriptions.push(languageClient.start());
    await languageClient.onReady();
}
function applyTheoremDecorations(editor, statuses) {
    if (!verifiedTheoremDecoration) {
        return;
    }
    const ranges = statuses
        .filter((status) => status.verified)
        .map((status) => new vscode.Range(status.line, 0, status.line, 0));
    editor.setDecorations(verifiedTheoremDecoration, ranges);
}
async function requestGoals(editor) {
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
    output?.appendLine(`[mypa] goals.request reqId=${reqId} uri=${editor.document.uri.toString()} line=${pos.line + 1} col=${pos.character + 1}`);
    try {
        const request = languageClient.sendRequest("mypa/goals", {
            reqId,
            uri: editor.document.uri.toString(),
            line: pos.line,
            character: pos.character,
        });
        const timeout = new Promise((_, reject) => setTimeout(() => reject(new Error("Goals request timed out after 4000ms.")), 4000));
        const response = await Promise.race([request, timeout]);
        if (!isGoalsResponse(response)) {
            throw new Error(`Invalid goals response shape for reqId=${reqId}`);
        }
        const theoremStatuses = Array.isArray(response.theoremStatuses)
            ? response.theoremStatuses.filter(isTheoremStatus)
            : [];
        output?.appendLine(`[mypa] goals.response reqId=${response.reqId} kind=${response.kind} diagnostics=${response.diagnostics.length}`);
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
                goals: response.goals.length > 0
                    ? response.goals
                    : [
                        {
                            id: `${response.code}:${response.reqId}`,
                            hypotheses: [],
                            target: response.message,
                        },
                    ],
                display: response.display
                    ? { ...response.display, status: response.message }
                    : undefined,
                tone: "error",
            },
            theoremStatuses,
        };
    }
    catch (err) {
        output?.appendLine(`[mypa] requestGoals failed: ${err.stack || String(err)}`);
        void vscode.window.showErrorMessage(`MyPA goals request failed: ${err.message}`);
        return {
            state: { goals: [
                    {
                        id: "lsp:error",
                        hypotheses: [],
                        target: `Goals request failed: ${err.message}`,
                    },
                ], tone: "error" },
            theoremStatuses: [],
        };
    }
}
async function refreshGoalsFromEditor(options) {
    const { context, editor, createPanelIfMissing, revealPanel } = options;
    if (editor.document.languageId !== "mypa") {
        output?.appendLine(`[mypa] goals.skip reason=non_mypa_editor language=${editor.document.languageId}`);
        return;
    }
    if (createPanelIfMissing) {
        ensureGoalsPanel(context, !revealPanel);
    }
    else if (!hasGoalsPanel()) {
        output?.appendLine("[mypa] goals.skip reason=no_panel");
        return;
    }
    else if (revealPanel) {
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
async function autoShowForMyPaEditor(context, editor) {
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
async function activate(context) {
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
    }
    catch (err) {
        lspStartupError = `LSP startup failed: ${err.message}`;
        output.appendLine(`[mypa] ${lspStartupError}`);
        output.appendLine(String(err.stack || ""));
        void vscode.window.showErrorMessage(lspStartupError);
    }
    context.subscriptions.push(vscode.commands.registerCommand("mypa.showGoals", async () => {
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
    }));
    let timer;
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
    context.subscriptions.push(vscode.window.onDidChangeActiveTextEditor((editor) => {
        void autoShowForMyPaEditor(context, editor);
        scheduleUpdate();
    }));
    context.subscriptions.push(vscode.window.onDidChangeTextEditorSelection((e) => {
        if (e.textEditor.document.languageId !== "mypa") {
            return;
        }
        scheduleUpdate();
    }));
    context.subscriptions.push(vscode.workspace.onDidChangeTextDocument((e) => {
        if (e.document.languageId !== "mypa") {
            return;
        }
        scheduleUpdate();
    }));
    context.subscriptions.push(vscode.workspace.onDidOpenTextDocument((doc) => {
        void ensureMyPaLanguage(doc).then(async () => {
            const editor = vscode.window.visibleTextEditors.find((e) => e.document === doc);
            await autoShowForMyPaEditor(context, editor);
            scheduleUpdate();
        });
    }));
    const completions = [
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
    const directiveCompletions = [
        {
            label: "#help",
            insertText: "#help ",
            detail: "Show formal-system help",
            documentation: "Display the language and inference rules for a supported formal system.",
            kind: vscode.CompletionItemKind.Keyword,
        },
    ];
    const helpSystemCompletions = [
        {
            label: "cllp_gentzen",
            insertText: "cllp_gentzen",
            detail: "Classical linear logic, Gentzen sequent calculus",
            documentation: "Urzyczyn-style classical linear propositional calculus in sequent form.",
            kind: vscode.CompletionItemKind.Reference,
        },
    ];
    const completionProvider = vscode.languages.registerCompletionItemProvider({ language: "mypa" }, {
        provideCompletionItems(doc, position) {
            const linePrefix = doc.lineAt(position.line).text.slice(0, position.character);
            if (linePrefix.startsWith("#help ")) {
                const systemPrefix = linePrefix.slice("#help ".length).trimLeft();
                return helpSystemCompletions
                    .filter((c) => !systemPrefix || c.label.startsWith(systemPrefix))
                    .map((c) => {
                    const item = new vscode.CompletionItem(c.label, c.kind ?? vscode.CompletionItemKind.Reference);
                    item.insertText = c.insertText;
                    item.detail = c.detail;
                    if (c.documentation) {
                        item.documentation = c.documentation;
                    }
                    const startCol = "#help ".length;
                    item.range = new vscode.Range(position.line, startCol, position.line, position.character);
                    return item;
                });
            }
            if (/^\s*#\w*$/.test(linePrefix) || /^\s*#$/.test(linePrefix)) {
                const directivePrefix = linePrefix.trimLeft();
                return directiveCompletions
                    .filter((c) => !directivePrefix || c.label.startsWith(directivePrefix))
                    .map((c) => {
                    const item = new vscode.CompletionItem(c.label, c.kind ?? vscode.CompletionItemKind.Keyword);
                    item.insertText = c.insertText;
                    item.detail = c.detail;
                    if (c.documentation) {
                        item.documentation = c.documentation;
                    }
                    const hashCol = linePrefix.indexOf("#");
                    item.range = new vscode.Range(position.line, Math.max(hashCol, 0), position.line, position.character);
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
    }, "\\", "#", " ");
    context.subscriptions.push(completionProvider);
    const hoverProvider = vscode.languages.registerHoverProvider({ language: "mypa" }, {
        provideHover(doc, position) {
            const range = doc.getWordRangeAtPosition(position, /[A-Za-z_][A-Za-z0-9_]*/);
            if (!range)
                return null;
            const word = doc.getText(range).toLowerCase();
            const rule = ruleHovers[word];
            if (!rule)
                return null;
            const md = new vscode.MarkdownString();
            md.isTrusted = false;
            md.appendMarkdown(`**${rule.title}**\n\n`);
            md.appendCodeblock(rule.display, "text");
            return new vscode.Hover(md, range);
        },
    });
    context.subscriptions.push(hoverProvider);
    const keywordSet = new Set([
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
    ].map((k) => k.toLowerCase()));
    const operatorRe = /[⊗⊕&!:]/g;
    const semanticProvider = vscode.languages.registerDocumentSemanticTokensProvider({ language: "mypa" }, {
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
                let m;
                while ((m = operatorRe.exec(text))) {
                    builder.push(line, m.index, 1, semanticTokenTypes.indexOf("operator"), 0);
                }
            }
            return builder.build();
        },
    }, semanticLegend);
    context.subscriptions.push(semanticProvider);
    // Ensure a first refresh after activation so users do not depend on manual edits.
    void autoShowForMyPaEditor(context, vscode.window.activeTextEditor);
    scheduleUpdate();
}
async function deactivate() {
    goalsPanel?.dispose();
    goalsPanel = undefined;
    output?.dispose();
    output = undefined;
    if (languageClient) {
        await languageClient.stop();
        languageClient = undefined;
    }
}
//# sourceMappingURL=extension.js.map