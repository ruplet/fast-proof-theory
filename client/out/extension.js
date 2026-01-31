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
 *   split             goal A ⊗ B or A & B → two subgoals
 *   tensor            alias for split on ⊗
 *   with              alias for split on &
 *   left/right        choose branch for ⊕ goal
 *   par-left/right    choose branch for ⅋ goal
 *   bang / quest      goal !A / ?A → subgoal A
 *   trivial           solves 1 or ⊤
 *   destruct <h>      break ⊗ / & hypothesis into components
 *   cases <h>         case split on ⊕ hypothesis (two subgoals)
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
        "left",
        "inl",
        "plus_left",
        "right",
        "inr",
        "plus_right",
        "par",
        "⅋",
        "par-left",
        "parl",
        "par-right",
        "parr",
        "bang",
        "!",
        "quest",
        "?",
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
        { label: "\\par", insertText: "⅋", detail: "par" },
        { label: "\\with", insertText: "&", detail: "with" },
        { label: "\\plus", insertText: "⊕", detail: "plus" },
        { label: "\\oplus", insertText: "⊕", detail: "plus" },
        { label: "\\top", insertText: "⊤", detail: "top" },
        { label: "\\bot", insertText: "⊥", detail: "bottom" },
        { label: "\\bottom", insertText: "⊥", detail: "bottom" },
        { label: "\\one", insertText: "1", detail: "one" },
        { label: "\\zero", insertText: "0", detail: "zero" },
        { label: "\\bang", insertText: "!", detail: "of course" },
        { label: "\\quest", insertText: "?", detail: "why not" },
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
        "par",
        "trivial",
        "bang",
        "quest",
    ].map((k) => k.toLowerCase()));
    const operatorRe = /[⊗⅋⊕&!?:]/g;
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
        const result = this.parseWith();
        this.skipWs();
        if (this.pos !== this.input.length) {
            throw new Error(`Unexpected trailing input "${this.input.slice(this.pos)}"`);
        }
        return result;
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
        let node = this.parsePar();
        while (true) {
            if (this.matchSymbol("⊕") || this.matchSymbol("+") || this.matchWord("plus")) {
                const right = this.parsePar();
                node = { kind: "plus", left: node, right };
                continue;
            }
            break;
        }
        return node;
    }
    parsePar() {
        let node = this.parseTensor();
        while (true) {
            if (this.matchSymbol("⅋") || this.matchWord("par")) {
                const right = this.parseTensor();
                node = { kind: "par", left: node, right };
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
        if (this.matchSymbol("?")) {
            const of = this.parseUnary();
            return { kind: "quest", of };
        }
        if (this.matchWord("bang")) {
            const of = this.parseUnary();
            return { kind: "bang", of };
        }
        if (this.matchWord("quest")) {
            const of = this.parseUnary();
            return { kind: "quest", of };
        }
        return this.parsePrimary();
    }
    parsePrimary() {
        this.skipWs();
        if (this.matchSymbol("(")) {
            const inner = this.parseWith();
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
        case "quest":
            return b.kind === a.kind && formulaEquals(a.of, b.of);
        case "tensor":
        case "par":
        case "with":
        case "plus":
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
        case "quest": {
            const inner = renderFormula(f.of, 3);
            return `?${inner}`;
        }
        case "tensor": {
            const left = renderFormula(f.left, 2);
            const right = renderFormula(f.right, 2);
            return paren(2, `${left} ⊗ ${right}`);
        }
        case "par": {
            const left = renderFormula(f.left, 2);
            const right = renderFormula(f.right, 2);
            return paren(2, `${left} ⅋ ${right}`);
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
        const destructHyp = (hName, choose) => {
            const hypIdx = ctx.findIndex((h) => h.name === hName);
            if (hypIdx === -1) {
                this.addError(line, `Unknown hypothesis "${hName}".`);
                this.goals.unshift(goal);
                return;
            }
            const hyp = ctx[hypIdx];
            ctx.splice(hypIdx, 1);
            const addFresh = (base, formula) => {
                let suffix = 1;
                let candidate = `${base}${suffix}`;
                while (ctx.some((h) => h.name === candidate)) {
                    suffix += 1;
                    candidate = `${base}${suffix}`;
                }
                ctx.push({
                    name: candidate,
                    type: renderFormula(formula),
                    formula,
                });
            };
            if (hyp.formula.kind === "tensor" || hyp.formula.kind === "with") {
                addFresh(`${hName}_left`, hyp.formula.left);
                addFresh(`${hName}_right`, hyp.formula.right);
                putBack([{ ...goal, ctx: cloneCtx(ctx) }]);
                return;
            }
            if (hyp.formula.kind === "plus") {
                if (!choose) {
                    this.addError(line, `cases on ⊕ requires a branch ("left" or "right").`);
                    this.goals.unshift(goal);
                    return;
                }
                const branch = choose === "left" ? hyp.formula.left : hyp.formula.right;
                addFresh(`${hName}_${choose}`, branch);
                putBack([{ ...goal, ctx: cloneCtx(ctx) }]);
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
                    putBack([mkGoal(target.left), mkGoal(target.right)]);
                    return;
                }
                this.addError(line, "Current goal is not a tensor (⊗).");
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
            case "par":
            case "⅋":
            case "par-left":
            case "parl":
                if (target.kind === "par") {
                    putBack([mkGoal(target.left)]);
                    return;
                }
                this.addError(line, "par-left applies only to ⅋ goals.");
                this.goals.unshift(goal);
                return;
            case "par-right":
            case "parr":
                if (target.kind === "par") {
                    putBack([mkGoal(target.right)]);
                    return;
                }
                this.addError(line, "par-right applies only to ⅋ goals.");
                this.goals.unshift(goal);
                return;
            case "bang":
            case "!":
                if (target.kind === "bang") {
                    putBack([mkGoal(target.of)]);
                    return;
                }
                this.addError(line, "bang applies only to ! goals.");
                this.goals.unshift(goal);
                return;
            case "quest":
            case "?":
                if (target.kind === "quest") {
                    putBack([mkGoal(target.of)]);
                    return;
                }
                this.addError(line, "quest applies only to ? goals.");
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
            case "destruct":
                if (argWords.length < 1) {
                    this.addError(line, "destruct requires a hypothesis name.");
                    this.goals.unshift(goal);
                    return;
                }
                destructHyp(argWords[0]);
                return;
            case "cases":
                if (argWords.length < 1) {
                    this.addError(line, "cases requires a hypothesis name.");
                    this.goals.unshift(goal);
                    return;
                }
                destructHyp(argWords[0], argWords[1] === "right" ? "right" : "left");
                return;
            case "assume": {
                const assumeMatch = rawArgs.match(/^([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.+)$/);
                if (!assumeMatch) {
                    this.addError(line, 'assume usage: tactic assume <name> : <formula>');
                    this.goals.unshift(goal);
                    return;
                }
                try {
                    const f = parseFormula(assumeMatch[2]);
                    ctx.push({
                        name: assumeMatch[1],
                        type: renderFormula(f),
                        formula: f,
                    });
                    putBack([{ ...goal, ctx: cloneCtx(ctx) }]);
                }
                catch (err) {
                    this.addError(line, err.message);
                    this.goals.unshift(goal);
                }
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