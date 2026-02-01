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
const GoalsPanel_1 = require("./GoalsPanel");
let goalsPanel;
const semanticTokenTypes = ["keyword", "operator", "comment"];
const semanticLegend = new vscode.SemanticTokensLegend([...semanticTokenTypes], []);
function textUpToCursor(editor) {
    const pos = editor.selection.active;
    const doc = editor.document;
    const range = new vscode.Range(new vscode.Position(0, 0), pos);
    const prefix = doc.getText(range);
    const lineText = doc.lineAt(pos.line).text;
    const atLineEnd = pos.character === lineText.length;
    if (atLineEnd)
        return prefix;
    const lastNl = prefix.lastIndexOf("\n");
    if (lastNl === -1)
        return "";
    return prefix.slice(0, lastNl + 1);
}
function ensureGoalsPanel(context, preserveFocus = false) {
    if (!goalsPanel) {
        goalsPanel = GoalsPanel_1.GoalsPanel.createOrShow(context, vscode.ViewColumn.Beside, preserveFocus);
    }
    else {
        goalsPanel.reveal(vscode.ViewColumn.Beside, preserveFocus);
    }
    return goalsPanel;
}
function isMyPaEditor(editor) {
    return !!editor && editor.document.languageId === "mypa";
}
/**
 * Very small linear logic “kernel” that understands a handful of tactics.
 * File format:
 *   -- comments
 *   theorem <name?>   # optional; starts a fresh context
 *   hyp <name> : <formula>
 *   goal <formula>
 *   <tactic> [args...]  (you can still use the old "tactic <name>" form)
 *
 * Tactics (operate on the first open goal):
 *   init [h]          close if goal matches hypothesis (optionally named)
 *   split             goal A ⊗ B or A & B → two subgoals (for ⊗ you must list hyps for first subgoal)
 *   tensor            alias for split on ⊗
 *   with              alias for split on & (splits into two goals without choosing hyps)
 *   left/right        choose branch for ⊕ goal
 *   bang              goal !A → subgoal A; `bang <h>` keeps !h and adds derelicted h
 *   derelict          remove ! from goal when all assumptions are bangs
 *   intro             introduce `⊸` (lollipop): for goal A ⊸ B, assume A and continue with B
 *   apply <h>         apply hypothesis h : A ⊸ B, consuming h and creating subgoal A
 *   trivial           solves 1 or ⊤
 *   destruct <h>      break a hypothesis: for ⊗ or &: split; for ⊕ acts like `cases` (see below); for ⊸ you can partition hyps
 *   cases <h> <hyps...> split on ⊕ hypothesis into two subgoals; you must list which hypotheses go to the first subgoal (the rest go to the second)
 *   assume <h> : A    introduce a new hypothesis in the current goal
 */
function computeProofStateFromText(text) {
    const tacticNames = new Set([
        "init",
        "axiom",
        "split",
        "tensor",
        "⊗",
        "with",
        "&",
        "intro",
        "apply",
        "derelict",
        "left",
        "inl",
        "plus_left",
        "right",
        "inr",
        "plus_right",
        "bang",
        "!",
        "trivial",
        "destruct",
        "cases",
        "assume",
    ].map((t) => t.toLowerCase()));
    let theoremCounter = 1;
    let currentTheorem = `theorem${theoremCounter}`;
    let engine = new ProofEngine();
    const allGoals = [];
    const flushEngine = () => {
        const res = engine.finalize();
        res.goals.forEach((g) => {
            allGoals.push({
                ...g,
                id: `${currentTheorem}:${g.id ?? ""}`,
            });
        });
    };
    const startNewTheorem = (name) => {
        flushEngine();
        theoremCounter += 1;
        currentTheorem = name || `theorem${theoremCounter}`;
        engine = new ProofEngine();
    };
    const lines = text.split(/\r?\n/);
    lines.forEach((raw, idx) => {
        const line = raw.trim();
        if (!line || line.startsWith("--"))
            return;
        const lineNo = idx + 1;
        const theoremMatch = line.match(/^theorem(?:\s+([A-Za-z_][A-Za-z0-9_]*))?$/i);
        if (theoremMatch) {
            const explicit = theoremMatch[1];
            startNewTheorem(explicit);
            return;
        }
        if (line === "end") {
            startNewTheorem();
            return;
        }
        const hypMatch = line.match(/^hyp\s+([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.+)$/);
        if (hypMatch) {
            try {
                const f = parseFormula(hypMatch[2]);
                engine.addHyp(hypMatch[1], f);
            }
            catch (err) {
                engine.addError(lineNo, err.message);
            }
            return;
        }
        const goalMatch = line.match(/^goal\s+(.+)$/);
        if (goalMatch) {
            try {
                const f = parseFormula(goalMatch[1]);
                engine.addGoal(f);
            }
            catch (err) {
                engine.addError(lineNo, err.message);
            }
            return;
        }
        const tacticMatch = line.match(/^tactic\s+([^\s]+)(?:\s+(.*))?$/);
        if (tacticMatch) {
            engine.applyTactic(tacticMatch[1], tacticMatch[2] ?? "", lineNo);
            return;
        }
        const firstWord = line.split(/\s+/, 1)[0] ?? "";
        if (tacticNames.has(firstWord.toLowerCase())) {
            const rest = line.slice(firstWord.length).trim();
            engine.applyTactic(firstWord, rest, lineNo);
            return;
        }
        engine.addError(lineNo, `Unrecognized line: "${line}"`);
    });
    flushEngine();
    if (allGoals.length === 0) {
        return { goals: [] };
    }
    return { goals: allGoals };
}
function activate(context) {
    // Command: show/reveal goals panel
    context.subscriptions.push(vscode.commands.registerCommand("mypa.showGoals", () => {
        ensureGoalsPanel(context);
        // force an immediate refresh if we have an active MyPA editor
        const ed = vscode.window.activeTextEditor;
        if (isMyPaEditor(ed)) {
            const state = computeProofStateFromText(textUpToCursor(ed));
            goalsPanel.setProofState(state);
        }
    }));
    // Debounced updater (prevents recomputing on every keystroke instantly)
    let timer;
    const scheduleUpdate = () => {
        if (timer)
            clearTimeout(timer);
        timer = setTimeout(() => {
            const ed = vscode.window.activeTextEditor;
            if (!isMyPaEditor(ed))
                return;
            // Ensure panel exists once user starts editing MyPA
            const panel = ensureGoalsPanel(context, true);
            const state = computeProofStateFromText(textUpToCursor(ed));
            panel.setProofState(state);
        }, 150);
    };
    // Update when switching editors
    context.subscriptions.push(vscode.window.onDidChangeActiveTextEditor(() => {
        scheduleUpdate();
    }));
    // Update when changing selection (cursor move)
    context.subscriptions.push(vscode.window.onDidChangeTextEditorSelection((e) => {
        if (e.textEditor.document.languageId !== "mypa")
            return;
        scheduleUpdate();
    }));
    // Update on edits
    context.subscriptions.push(vscode.workspace.onDidChangeTextDocument((e) => {
        if (e.document.languageId !== "mypa")
            return;
        scheduleUpdate();
    }));
    // Optional: update when a MyPA doc opens
    context.subscriptions.push(vscode.workspace.onDidOpenTextDocument((doc) => {
        if (doc.languageId !== "mypa")
            return;
        scheduleUpdate();
    }));
    // Unicode-style completions triggered by a leading backslash (Lean-like UX)
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
    const completionProvider = vscode.languages.registerCompletionItemProvider({ language: "mypa" }, {
        provideCompletionItems(doc, position) {
            const range = doc.getWordRangeAtPosition(position, /\\[\w]*/);
            const prefix = range ? doc.getText(range) : "";
            const items = completions
                .filter((c) => !prefix || c.label.startsWith(prefix))
                .map((c) => {
                const item = new vscode.CompletionItem(c.label, vscode.CompletionItemKind.Snippet);
                item.insertText = c.insertText;
                item.detail = c.detail;
                if (c.documentation)
                    item.documentation = c.documentation;
                item.range = range;
                return item;
            });
            return items;
        },
    }, "\\");
    context.subscriptions.push(completionProvider);
    // Lightweight semantic highlighting (keywords/operators)
    const keywordSet = new Set([
        "theorem",
        "goal",
        "hyp",
        "assume",
        "destruct",
        "cases",
        "init",
        "axiom",
        "split",
        "tensor",
        "with",
        "left",
        "right",
        "trivial",
        "bang",
        "intro",
        "apply",
        "derelict",
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
}
function deactivate() {
    goalsPanel?.dispose();
    goalsPanel = undefined;
}
// ---------- Proof engine ----------
function isAlphaNum(ch) {
    return !!ch && /[A-Za-z0-9_]/.test(ch);
}
class FormulaParser {
    constructor(input) {
        this.input = input;
        this.pos = 0;
    }
    parse() {
        const result = this.parseLolli();
        this.skipWs();
        if (this.pos !== this.input.length) {
            throw new Error(`Unexpected trailing input "${this.input.slice(this.pos)}"`);
        }
        return result;
    }
    parseLolli() {
        const node = this.parseWith();
        if (this.matchSymbol("⊸") || this.matchSymbol("->") || this.matchWord("lolli")) {
            const right = this.parseLolli();
            return { kind: "lolli", left: node, right };
        }
        return node;
    }
    parseWith() {
        let node = this.parsePlus();
        while (true) {
            if (this.matchSymbol("&") || this.matchWord("with")) {
                const right = this.parsePlus();
                node = { kind: "with", left: node, right };
                continue;
            }
            break;
        }
        return node;
    }
    parsePlus() {
        let node = this.parseTensor();
        while (true) {
            if (this.matchSymbol("⊕") || this.matchSymbol("+") || this.matchWord("plus")) {
                const right = this.parseTensor();
                node = { kind: "plus", left: node, right };
                continue;
            }
            break;
        }
        return node;
    }
    parseTensor() {
        let node = this.parseUnary();
        while (true) {
            if (this.matchSymbol("⊗") ||
                this.matchSymbol("*") ||
                this.matchWord("tensor") ||
                this.matchWord("times")) {
                const right = this.parseUnary();
                node = { kind: "tensor", left: node, right };
                continue;
            }
            break;
        }
        return node;
    }
    parseUnary() {
        this.skipWs();
        if (this.matchSymbol("!")) {
            const of = this.parseUnary();
            return { kind: "bang", of };
        }
        if (this.matchWord("bang")) {
            const of = this.parseUnary();
            return { kind: "bang", of };
        }
        return this.parsePrimary();
    }
    parsePrimary() {
        this.skipWs();
        if (this.matchSymbol("(")) {
            const inner = this.parseLolli();
            this.expectSymbol(")");
            return inner;
        }
        if (this.matchSymbol("1") || this.matchWord("one"))
            return { kind: "one" };
        if (this.matchSymbol("⊤") || this.matchWord("top"))
            return { kind: "top" };
        if (this.matchSymbol("0") || this.matchWord("zero"))
            return { kind: "zero" };
        const name = this.parseIdent();
        if (name) {
            const negated = this.matchSymbol("⊥");
            return { kind: "atom", name, negated };
        }
        if (this.matchSymbol("⊥") || this.matchWord("bot"))
            return { kind: "bot" };
        throw new Error("Expected a formula");
    }
    parseIdent() {
        this.skipWs();
        const start = this.pos;
        while (isAlphaNum(this.peek()))
            this.pos++;
        if (this.pos > start)
            return this.input.slice(start, this.pos);
        return null;
    }
    matchSymbol(sym) {
        this.skipWs();
        if (this.input.startsWith(sym, this.pos)) {
            this.pos += sym.length;
            return true;
        }
        return false;
    }
    matchWord(word) {
        this.skipWs();
        if (this.input.startsWith(word, this.pos) &&
            !isAlphaNum(this.input[this.pos + word.length])) {
            this.pos += word.length;
            return true;
        }
        return false;
    }
    expectSymbol(sym) {
        if (!this.matchSymbol(sym)) {
            throw new Error(`Expected "${sym}"`);
        }
    }
    skipWs() {
        while (/\s/.test(this.input[this.pos]))
            this.pos++;
    }
    peek() {
        return this.input[this.pos];
    }
}
function parseFormula(text) {
    const parser = new FormulaParser(text);
    return parser.parse();
}
function formulaEquals(a, b) {
    if (a.kind !== b.kind)
        return false;
    switch (a.kind) {
        case "atom":
            return b.kind === "atom" && a.name === b.name && a.negated === b.negated;
        case "bang":
            return b.kind === a.kind && formulaEquals(a.of, b.of);
        case "tensor":
        case "with":
        case "plus":
        case "lolli":
            return (b.kind === a.kind &&
                formulaEquals(a.left, b.left) &&
                formulaEquals(a.right, b.right));
        default:
            return true;
    }
}
function renderFormula(f, parentPrec = 0) {
    const paren = (prec, inner) => prec < parentPrec ? `(${inner})` : inner;
    switch (f.kind) {
        case "atom":
            return `${f.name}${f.negated ? "⊥" : ""}`;
        case "one":
            return "1";
        case "bot":
            return "⊥";
        case "top":
            return "⊤";
        case "zero":
            return "0";
        case "bang": {
            const inner = renderFormula(f.of, 3);
            return `!${inner}`;
        }
        case "tensor": {
            const left = renderFormula(f.left, 2);
            const right = renderFormula(f.right, 2);
            return paren(2, `${left} ⊗ ${right}`);
        }
        case "lolli": {
            const left = renderFormula(f.left, 0);
            const right = renderFormula(f.right, 0);
            return paren(0, `${left} ⊸ ${right}`);
        }
        case "with": {
            const left = renderFormula(f.left, 1);
            const right = renderFormula(f.right, 1);
            return paren(1, `${left} & ${right}`);
        }
        case "plus": {
            const left = renderFormula(f.left, 1);
            const right = renderFormula(f.right, 1);
            return paren(1, `${left} ⊕ ${right}`);
        }
    }
}
function cloneCtx(ctx) {
    return ctx.map((h) => ({ ...h }));
}
class ProofEngine {
    constructor() {
        this.globalHyps = [];
        this.goals = [];
        this.errors = [];
        this.goalCounter = 0;
    }
    addError(line, msg) {
        this.errors.push(`Line ${line}: ${msg}`);
    }
    addHyp(name, formula) {
        const hyp = {
            name,
            type: renderFormula(formula),
            formula,
        };
        this.globalHyps.push(hyp);
        this.goals.forEach((g) => g.ctx.push({ ...hyp }));
    }
    addGoal(target) {
        const goal = {
            id: `g${++this.goalCounter}`,
            ctx: cloneCtx(this.globalHyps),
            target,
        };
        this.goals.push(goal);
    }
    applyTactic(name, rawArgs, line) {
        if (this.goals.length === 0) {
            this.addError(line, `No goals available for tactic "${name}".`);
            return;
        }
        const normalized = name.toLowerCase();
        const goal = this.goals.shift();
        const ctx = goal.ctx;
        const target = goal.target;
        const mkGoal = (f, updatedCtx = ctx) => ({
            id: `g${++this.goalCounter}`,
            ctx: cloneCtx(updatedCtx),
            target: f,
        });
        const putBack = (newGoals) => {
            this.goals = newGoals.concat(this.goals);
        };
        const ensureHyp = (hypName) => {
            if (!hypName)
                return ctx.find((h) => formulaEquals(h.formula, target));
            return ctx.find((h) => h.name === hypName);
        };
        const argWords = rawArgs
            .split(/\s+/)
            .map((a) => a.trim())
            .filter(Boolean);
        const closeWithHyp = (hypName) => {
            const hyp = ensureHyp(hypName);
            if (!hyp) {
                this.addError(line, hypName
                    ? `Hypothesis "${hypName}" does not match current goal.`
                    : "No hypothesis matches current goal.");
                this.goals.unshift(goal);
                return;
            }
            putBack([]);
        };
        const destructHyp = (hName, choose, extra) => {
            const hypIdx = ctx.findIndex((h) => h.name === hName);
            if (hypIdx === -1) {
                this.addError(line, `Unknown hypothesis "${hName}".`);
                this.goals.unshift(goal);
                return;
            }
            const hyp = ctx[hypIdx];
            // create contexts without mutating the original ctx
            const withoutHyp = ctx.filter((h, i) => i !== hypIdx).map((h) => ({ ...h }));
            const makeFreshName = (existing, base) => {
                let suffix = 1;
                let candidate = `${base}${suffix}`;
                while (existing.some((h) => h.name === candidate)) {
                    suffix += 1;
                    candidate = `${base}${suffix}`;
                }
                return candidate;
            };
            if (hyp.formula.kind === "tensor") {
                const newCtx = withoutHyp.map((h) => ({ ...h }));
                const leftName = makeFreshName(newCtx, `${hName}_left`);
                newCtx.push({ name: leftName, type: renderFormula(hyp.formula.left), formula: hyp.formula.left });
                const rightName = makeFreshName(newCtx, `${hName}_right`);
                newCtx.push({ name: rightName, type: renderFormula(hyp.formula.right), formula: hyp.formula.right });
                putBack([{ ...goal, ctx: cloneCtx(newCtx) }]);
                return;
            }
            if (hyp.formula.kind === "with") {
                // allow branch to be provided as the first extra argument when called like: destruct h left
                let branchChoice = choose;
                if (!branchChoice && extra && extra.length > 0) {
                    const tok = extra[0].toLowerCase();
                    if (tok === "left" || tok === "right")
                        branchChoice = tok;
                }
                if (!branchChoice) {
                    this.addError(line, `destruct on & requires choosing a branch ("left" or "right").`);
                    this.goals.unshift(goal);
                    return;
                }
                const branch = branchChoice === "left" ? hyp.formula.left : hyp.formula.right;
                const newCtx = withoutHyp.map((h) => ({ ...h }));
                const name = makeFreshName(newCtx, `${hName}_${branchChoice}`);
                newCtx.push({ name, type: renderFormula(branch), formula: branch });
                putBack([{ ...goal, ctx: cloneCtx(newCtx) }]);
                return;
            }
            if (hyp.formula.kind === "plus") {
                // cases: split into two subgoals; all existing hypotheses are duplicated to both branches
                const firstCtx = withoutHyp.map((h) => ({ ...h }));
                const secondCtx = withoutHyp.map((h) => ({ ...h }));
                const leftName = makeFreshName(firstCtx, `${hName}_left`);
                firstCtx.push({ name: leftName, type: renderFormula(hyp.formula.left), formula: hyp.formula.left });
                const rightName = makeFreshName(secondCtx, `${hName}_right`);
                secondCtx.push({ name: rightName, type: renderFormula(hyp.formula.right), formula: hyp.formula.right });
                putBack([{ ...goal, ctx: cloneCtx(firstCtx) }, { ...goal, ctx: cloneCtx(secondCtx) }]);
                return;
            }
            if (hyp.formula.kind === "lolli") {
                // destruct implication: user may choose which hypotheses are used to prove the antecedent
                const chosen = new Set();
                const list = extra ?? [];
                for (const n of list) {
                    if (chosen.has(n)) {
                        this.addError(line, `Hypothesis "${n}" listed multiple times.`);
                        this.goals.unshift(goal);
                        return;
                    }
                    chosen.add(n);
                }
                for (const n of chosen) {
                    if (!withoutHyp.some((h) => h.name === n)) {
                        this.addError(line, `Unknown hypothesis "${n}" in destruct.`);
                        this.goals.unshift(goal);
                        return;
                    }
                }
                const firstCtx = withoutHyp.filter((h) => chosen.has(h.name)).map((h) => ({ ...h }));
                const secondCtx = withoutHyp.filter((h) => !chosen.has(h.name)).map((h) => ({ ...h }));
                // add consequent (residual) to secondCtx (applying h to the proved antecedent)
                const resName = makeFreshName(secondCtx, `${hName}_res`);
                secondCtx.push({ name: resName, type: renderFormula(hyp.formula.right), formula: hyp.formula.right });
                putBack([{ id: `g${++this.goalCounter}`, ctx: cloneCtx(firstCtx), target: hyp.formula.left }, { ...goal, ctx: cloneCtx(secondCtx) }]);
                return;
            }
            this.addError(line, `destruct/cases not supported for hypothesis "${hName}".`);
            this.goals.unshift(goal);
        };
        switch (normalized) {
            case "init":
            case "axiom":
                closeWithHyp(argWords[0]);
                return;
            case "split":
            case "tensor":
            case "⊗":
                if (target.kind === "tensor") {
                    // user must list hypothesis names that should be retained in the first subgoal
                    // if no hypotheses listed, the first subgoal gets an empty context
                    const chosen = new Set();
                    for (const n of argWords) {
                        if (chosen.has(n)) {
                            this.addError(line, `Hypothesis "${n}" listed multiple times.`);
                            this.goals.unshift(goal);
                            return;
                        }
                        chosen.add(n);
                    }
                    // validate existence
                    for (const n of chosen) {
                        if (!ctx.some((h) => h.name === n)) {
                            this.addError(line, `Unknown hypothesis "${n}" in split.`);
                            this.goals.unshift(goal);
                            return;
                        }
                    }
                    const firstCtx = ctx.filter((h) => chosen.has(h.name));
                    const secondCtx = ctx.filter((h) => !chosen.has(h.name));
                    putBack([mkGoal(target.left, firstCtx), mkGoal(target.right, secondCtx)]);
                    return;
                }
                // allow `split` to also split a with (&) goal without requiring hypothesis selection
                if (target.kind === "with") {
                    putBack([mkGoal(target.left), mkGoal(target.right)]);
                    return;
                }
                this.addError(line, "Current goal is not a tensor (⊗) or with (&).");
                this.goals.unshift(goal);
                return;
            case "with":
            case "&":
                if (target.kind === "with") {
                    putBack([mkGoal(target.left), mkGoal(target.right)]);
                    return;
                }
                this.addError(line, "Current goal is not a with (&).");
                this.goals.unshift(goal);
                return;
            case "left":
            case "inl":
            case "plus_left":
                if (target.kind === "plus") {
                    putBack([mkGoal(target.left)]);
                    return;
                }
                this.addError(line, "left/inl applies only to ⊕ goals.");
                this.goals.unshift(goal);
                return;
            case "right":
            case "inr":
            case "plus_right":
                if (target.kind === "plus") {
                    putBack([mkGoal(target.right)]);
                    return;
                }
                this.addError(line, "right/inr applies only to ⊕ goals.");
                this.goals.unshift(goal);
                return;
            case "bang":
            case "!":
                // If used with an argument, treat as dereliction on a hypothesis: keep !A and add A
                if (argWords.length > 0) {
                    const hName = argWords[0];
                    const hypIdx = ctx.findIndex((h) => h.name === hName);
                    if (hypIdx === -1) {
                        this.addError(line, `Unknown hypothesis "${hName}".`);
                        this.goals.unshift(goal);
                        return;
                    }
                    const hyp = ctx[hypIdx];
                    if (hyp.formula.kind !== "bang") {
                        this.addError(line, `Hypothesis "${hName}" is not a bang.`);
                        this.goals.unshift(goal);
                        return;
                    }
                    // add a derelicted copy of the hypothesis (A) while keeping the original !A
                    let base = `${hName}_derelict`;
                    let suffix = 1;
                    let candidate = `${base}${suffix}`;
                    while (ctx.some((h) => h.name === candidate)) {
                        suffix += 1;
                        candidate = `${base}${suffix}`;
                    }
                    ctx.push({ name: candidate, type: renderFormula(hyp.formula.of), formula: hyp.formula.of });
                    putBack([{ ...goal, ctx: cloneCtx(ctx) }]);
                    return;
                }
                // otherwise, if goal is !A, reduce it to A
                if (target.kind === "bang") {
                    putBack([mkGoal(target.of)]);
                    return;
                }
                this.addError(line, "bang applies only to ! goals or as `bang <hyp>` for dereliction.");
                this.goals.unshift(goal);
                return;
            case "quest":
            case "?":
                this.addError(line, "Unknown tactic \"?\".");
                this.goals.unshift(goal);
                return;
            case "trivial":
                if (target.kind === "one" || target.kind === "top") {
                    putBack([]);
                    return;
                }
                this.addError(line, "trivial only solves 1 or ⊤.");
                this.goals.unshift(goal);
                return;
            case "derelict":
                // remove a bang in the goal if all hypotheses are bangs
                if (target.kind === "bang") {
                    if (!ctx.every((h) => h.formula.kind === "bang")) {
                        this.addError(line, "derelict requires all assumptions to be bangs.");
                        this.goals.unshift(goal);
                        return;
                    }
                    putBack([mkGoal(target.of)]);
                    return;
                }
                this.addError(line, "derelict applies only to ! goals.");
                this.goals.unshift(goal);
                return;
            case "destruct":
                if (argWords.length < 1) {
                    this.addError(line, "destruct requires a hypothesis name.");
                    this.goals.unshift(goal);
                    return;
                }
                {
                    const name = argWords[0];
                    const extra = argWords.slice(1);
                    destructHyp(name, undefined, extra);
                }
                return;
            case "cases":
                if (argWords.length < 1) {
                    this.addError(line, "cases requires a hypothesis name.");
                    this.goals.unshift(goal);
                    return;
                }
                destructHyp(argWords[0]);
                return;
            case "assume": {
                const assumeMatch = rawArgs.match(/^([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.+)$/);
                if (!assumeMatch) {
                    this.addError(line, 'assume usage: tactic assume <name> : <formula> <hypNames...>');
                    this.goals.unshift(goal);
                    return;
                }
                try {
                    const name = assumeMatch[1];
                    const rest = assumeMatch[2].trim();
                    const tokens = rest.length ? rest.split(/\s+/) : [];
                    let parsed = null;
                    let used = 0;
                    for (let i = tokens.length; i >= 1; i--) {
                        const cand = tokens.slice(0, i).join(" ");
                        try {
                            parsed = parseFormula(cand);
                            used = i;
                            break;
                        }
                        catch (_) {
                            // try shorter prefix
                        }
                    }
                    if (!parsed) {
                        // maybe the whole rest is a formula without extra hyps
                        try {
                            parsed = parseFormula(rest);
                            used = tokens.length;
                        }
                        catch (err) {
                            this.addError(line, err.message);
                            this.goals.unshift(goal);
                            return;
                        }
                    }
                    const chosen = tokens.slice(used);
                    // empty chosen list is allowed: first subgoal gets empty context
                    const chosenSet = new Set();
                    for (const n of chosen) {
                        if (chosenSet.has(n)) {
                            this.addError(line, `Hypothesis "${n}" listed multiple times.`);
                            this.goals.unshift(goal);
                            return;
                        }
                        chosenSet.add(n);
                    }
                    for (const n of chosenSet) {
                        if (!ctx.some((h) => h.name === n)) {
                            this.addError(line, `Unknown hypothesis "${n}" in assume.`);
                            this.goals.unshift(goal);
                            return;
                        }
                    }
                    const firstCtx = ctx.filter((h) => chosenSet.has(h.name)).map((h) => ({ ...h }));
                    const secondCtx = ctx.filter((h) => !chosenSet.has(h.name)).map((h) => ({ ...h }));
                    // add new assumption to secondCtx (fresh name if needed)
                    let base = name;
                    let suffix = 1;
                    let candidate = base;
                    while (secondCtx.some((h) => h.name === candidate)) {
                        suffix += 1;
                        candidate = `${base}${suffix}`;
                    }
                    secondCtx.push({ name: candidate, type: renderFormula(parsed), formula: parsed });
                    putBack([mkGoal(parsed, firstCtx), mkGoal(target, secondCtx)]);
                }
                catch (err) {
                    this.addError(line, err.message);
                    this.goals.unshift(goal);
                }
                return;
            }
            case "intro": {
                // Introduce an implication (lolli) assumption: goal A ⊸ B -> assume A and continue with B
                if (target.kind === "lolli") {
                    // optional name for the introduced hypothesis
                    const hName = argWords[0] || "h";
                    // find a fresh name
                    let base = hName;
                    let suffix = 1;
                    let candidate = base;
                    while (ctx.some((h) => h.name === candidate)) {
                        suffix += 1;
                        candidate = `${base}${suffix}`;
                    }
                    ctx.push({ name: candidate, type: renderFormula(target.left), formula: target.left });
                    putBack([mkGoal(target.right, ctx)]);
                    return;
                }
                this.addError(line, "intro applies only to lollipop (⊸) goals.");
                this.goals.unshift(goal);
                return;
            }
            case "apply": {
                // apply a hypothesis of form A ⊸ B to the current goal B, consuming the hypothesis and producing subgoal A
                if (argWords.length < 1) {
                    this.addError(line, "apply requires a hypothesis name.");
                    this.goals.unshift(goal);
                    return;
                }
                const hName = argWords[0];
                const hIdx = ctx.findIndex((h) => h.name === hName);
                if (hIdx === -1) {
                    this.addError(line, `Unknown hypothesis "${hName}".`);
                    this.goals.unshift(goal);
                    return;
                }
                const hyp = ctx[hIdx];
                if (hyp.formula.kind !== "lolli") {
                    this.addError(line, `Hypothesis "${hName}" is not an implication.`);
                    this.goals.unshift(goal);
                    return;
                }
                if (!formulaEquals(hyp.formula.right, target)) {
                    this.addError(line, `Hypothesis "${hName}" does not conclude the current goal.`);
                    this.goals.unshift(goal);
                    return;
                }
                // consume the hypothesis
                ctx.splice(hIdx, 1);
                putBack([mkGoal(hyp.formula.left, ctx)]);
                return;
            }
            default:
                this.addError(line, `Unknown tactic "${name}".`);
                this.goals.unshift(goal);
        }
    }
    finalize() {
        if (this.errors.length) {
            return {
                goals: [
                    {
                        id: "errors",
                        hypotheses: [],
                        target: this.errors.join("\n"),
                    },
                ],
            };
        }
        if (this.goals.length === 0) {
            return { goals: [] };
        }
        const goals = this.goals.map((g) => ({
            id: g.id,
            hypotheses: g.ctx.map((h) => ({ name: h.name, type: h.type })),
            target: renderFormula(g.target),
        }));
        return { goals };
    }
}
//# sourceMappingURL=extension.js.map