"use strict";

const DOMAIN_INFO = {
  symbolCompletions: [
    { label: "\\lolli", insertText: "⊸", detail: "Symbol", documentation: "Linear implication / lolli." },
    { label: "\\imp", insertText: "->", detail: "Symbol", documentation: "Propositional implication." },
    { label: "\\to", insertText: "->", detail: "Symbol", documentation: "Implication ASCII form accepted by MyPA." },
    { label: "\\tensor", insertText: "⊗", detail: "Symbol", documentation: "Tensor / multiplicative conjunction." },
    { label: "\\otimes", insertText: "⊗", detail: "Symbol", documentation: "Tensor / multiplicative conjunction." },
    { label: "\\oplus", insertText: "⊕", detail: "Symbol", documentation: "Plus / additive disjunction." },
    { label: "\\plus", insertText: "⊕", detail: "Symbol", documentation: "Plus / additive disjunction." },
    { label: "\\and", insertText: "∧", detail: "Symbol", documentation: "Propositional conjunction." },
    { label: "\\or", insertText: "∨", detail: "Symbol", documentation: "Propositional disjunction." },
    { label: "\\with", insertText: "&", detail: "Symbol", documentation: "Linear additive conjunction." },
    { label: "\\bang", insertText: "!", detail: "Symbol", documentation: "Linear exponential bang." },
    { label: "\\bot", insertText: "⊥", detail: "Symbol", documentation: "Bottom / falsity." },
  ],
  directives: [
    {
      label: "#help",
      insertText: "#help cllp_gentzen",
      detail: "Directive",
      documentation: "Show available proof-system info.",
    },
  ],
  systems: [
    {
      key: "cllp_gentzen",
      aliases: ["LL", "LL!"],
      title: "Classical Linear Logic (Gentzen)",
      summary: "Linear sequent tactics mapped to FastProofTheory.Proof.LinearLogic constructors.",
      language: ["linear"],
      tactics: [
        { name: "ax", title: "Assumption", display: "ax h", summary: "Close goal using matching hypothesis." },
        { name: "rlolli", title: "⊸ Right", display: "rlolli h", summary: "Introduce antecedent from lolli goal." },
        { name: "rwith", title: "& Right", display: "rwith", summary: "Split goal into two conjunctive goals." },
        { name: "rplusl", title: "⊕ Right Left", display: "rplusl", summary: "Prove left disjunct." },
        { name: "rplusr", title: "⊕ Right Right", display: "rplusr", summary: "Prove right disjunct." },
        { name: "rtensor", title: "⊗ Right", display: "rtensor h", summary: "Split context and prove tensor components." },
      ],
      checkedNow: ["ax", "rlolli", "rwith", "rplusl", "rplusr", "rtensor"],
    },
  ],
  keywords: ["def", "theorem", "using", "in", "with", "by"],
  operators: ["⊸", "⊗", "&", "⊕", "!", "(", ")"],
};

function mkRange(line, start, end) {
  return { start: { line, character: start }, end: { line, character: end } };
}

function diagnostic(line, code, message, severity = 1) {
  return { range: mkRange(line, 0, 1), severity, code, source: "proofAssistant", message };
}

function tokenizeFormula(input) {
  const s = input.trim();
  const tokens = [];
  let i = 0;
  while (i < s.length) {
    const c = s[i];
    if (/\s/.test(c)) {
      i += 1;
      continue;
    }
    if (s.startsWith("->", i)) {
      tokens.push({ t: "op", v: "⊸" });
      i += 2;
      continue;
    }
    if (["(", ")", "⊗", "&", "⊕", "⊸", "!"].includes(c)) {
      tokens.push({ t: c === "(" || c === ")" ? c : "op", v: c });
      i += 1;
      continue;
    }
    if (/[A-Za-z0-9_]/.test(c)) {
      let j = i + 1;
      while (j < s.length && /[A-Za-z0-9_]/.test(s[j])) j += 1;
      tokens.push({ t: "id", v: s.slice(i, j) });
      i = j;
      continue;
    }
    throw new Error(`Unexpected token '${c}' in formula.`);
  }
  return tokens;
}

function parseFormula(text) {
  const tokens = tokenizeFormula(text);
  let i = 0;
  function peek() { return tokens[i]; }
  function consume() { return tokens[i++]; }
  function parseAtom() {
    const tk = peek();
    if (!tk) throw new Error("Unexpected end of formula.");
    if (tk.t === "id") {
      consume();
      return { k: "atom", n: tk.v };
    }
    if (tk.t === "op" && tk.v === "!") {
      consume();
      return { k: "bang", a: parseAtom() };
    }
    if (tk.t === "(") {
      consume();
      const inner = parseLolli();
      if (!peek() || peek().t !== ")") throw new Error("Missing closing ')'.");
      consume();
      return inner;
    }
    throw new Error(`Unexpected token '${tk.v || tk.t}'.`);
  }
  function parseTensor() {
    let left = parseAtom();
    while (peek() && peek().t === "op" && (peek().v === "⊗")) {
      consume();
      const right = parseAtom();
      left = { k: "tensor", l: left, r: right };
    }
    return left;
  }
  function parseWithPlus() {
    let left = parseTensor();
    while (peek() && peek().t === "op" && (peek().v === "&" || peek().v === "⊕")) {
      const op = consume().v;
      const right = parseTensor();
      left = { k: op === "&" ? "with" : "plus", l: left, r: right };
    }
    return left;
  }
  function parseLolli() {
    let left = parseWithPlus();
    if (peek() && peek().t === "op" && peek().v === "⊸") {
      consume();
      const right = parseLolli();
      return { k: "lolli", l: left, r: right };
    }
    return left;
  }
  const out = parseLolli();
  if (i !== tokens.length) throw new Error("Unexpected trailing tokens in formula.");
  return out;
}

function formulaEq(a, b) {
  return JSON.stringify(a) === JSON.stringify(b);
}

function formulaDisplay(f) {
  if (!f) return "?";
  switch (f.k) {
    case "atom":
      return String(f.n);
    case "bang":
      return `!${formulaDisplay(f.a)}`;
    case "tensor":
      return `(${formulaDisplay(f.l)} ⊗ ${formulaDisplay(f.r)})`;
    case "with":
      return `(${formulaDisplay(f.l)} & ${formulaDisplay(f.r)})`;
    case "plus":
      return `(${formulaDisplay(f.l)} ⊕ ${formulaDisplay(f.r)})`;
    case "lolli":
      return `(${formulaDisplay(f.l)} -> ${formulaDisplay(f.r)})`;
    default:
      return "?";
  }
}

function propTokenize(input) {
  const s = input.trim();
  const tokens = [];
  let i = 0;
  while (i < s.length) {
    const c = s[i];
    if (/\s/.test(c)) {
      i += 1;
      continue;
    }
    if (s.startsWith("->", i)) {
      tokens.push({ t: "op", v: "->" });
      i += 2;
      continue;
    }
    if (c === "⊥") {
      tokens.push({ t: "bottom", v: "⊥" });
      i += 1;
      continue;
    }
    if (c === "(" || c === ")") {
      tokens.push({ t: c, v: c });
      i += 1;
      continue;
    }
    if (c === "∨" || c === "∧") {
      tokens.push({ t: "op", v: c });
      i += 1;
      continue;
    }
    if (/[A-Za-z0-9_]/.test(c)) {
      let j = i + 1;
      while (j < s.length && /[A-Za-z0-9_]/.test(s[j])) j += 1;
      tokens.push({ t: "id", v: s.slice(i, j) });
      i = j;
      continue;
    }
    throw new Error(`Unexpected token '${c}' in proposition formula.`);
  }
  return tokens;
}

function parsePropFormula(text) {
  const tokens = propTokenize(text);
  let i = 0;
  function peek() { return tokens[i]; }
  function consume() { return tokens[i++]; }
  function parseAtom() {
    const tk = peek();
    if (!tk) throw new Error("Unexpected end of proposition formula.");
    if (tk.t === "id") {
      consume();
      return { k: "atom", n: tk.v };
    }
    if (tk.t === "bottom") {
      consume();
      return { k: "bottom" };
    }
    if (tk.t === "(") {
      consume();
      const inner = parseImp();
      if (!peek() || peek().t !== ")") throw new Error("Missing closing ')' in proposition formula.");
      consume();
      return inner;
    }
    throw new Error(`Unexpected token '${tk.v || tk.t}' in proposition formula.`);
  }
  function parseAndOr() {
    let left = parseAtom();
    while (peek() && peek().t === "op" && (peek().v === "∨" || peek().v === "∧")) {
      const op = consume().v;
      const right = parseAtom();
      left = { k: op === "∨" ? "or" : "and", l: left, r: right };
    }
    return left;
  }
  function parseImp() {
    let left = parseAndOr();
    if (peek() && peek().t === "op" && peek().v === "->") {
      consume();
      const right = parseImp();
      return { k: "imp", l: left, r: right };
    }
    return left;
  }
  const out = parseImp();
  if (i !== tokens.length) throw new Error("Unexpected trailing proposition tokens.");
  return out;
}

function propDisplay(f) {
  if (!f) return "?";
  switch (f.k) {
    case "atom": return String(f.n);
    case "bottom": return "⊥";
    case "imp": return `(${propDisplay(f.l)} -> ${propDisplay(f.r)})`;
    case "or": return `(${propDisplay(f.l)} ∨ ${propDisplay(f.r)})`;
    case "and": return `(${propDisplay(f.l)} ∧ ${propDisplay(f.r)})`;
    default: return "?";
  }
}

function formulaLean(f) {
  switch (f.k) {
    case "atom": return `LinearFormula.atom ${JSON.stringify(f.n)}`;
    case "bang": return `(LinearFormula.bang ${formulaLean(f.a)})`;
    case "tensor": return `(${formulaLean(f.l)} ⊗ ${formulaLean(f.r)})`;
    case "with": return `(${formulaLean(f.l)} & ${formulaLean(f.r)})`;
    case "plus": return `(${formulaLean(f.l)} ⊕ ${formulaLean(f.r)})`;
    case "lolli": return `(${formulaLean(f.l)} ⊸ ${formulaLean(f.r)})`;
    default: throw new Error("Unsupported formula kind.");
  }
}

function parseDocument(text) {
  const lines = text.split(/\r?\n/);
  const theorems = [];
  const diagnostics = [];
  let i = 0;
  while (i < lines.length) {
    const raw = lines[i];
    const line = raw.trim();
    if (!line || line.startsWith("--") || line.startsWith("#help")) {
      i += 1;
      continue;
    }
    const m = line.match(/^(def|theorem)\s+([A-Za-z_][A-Za-z0-9_]*)\s+using\s+(.+?)\s*:\s*(.+?)\s*:=\s*by\s*$/);
    if (!m) {
      diagnostics.push(diagnostic(i, "PARSE_TOPLEVEL", "Expected theorem header `def/theorem ... := by`."));
      i += 1;
      continue;
    }
    const [, , name, system, statement] = m;
    const tactics = [];
    const startLine = i;
    i += 1;
    while (i < lines.length) {
      const t = lines[i].trim();
      if (!t || t.startsWith("--")) {
        i += 1;
        continue;
      }
      if (/^(def|theorem)\s+/.test(t)) break;
      const firstNonWs = lines[i].search(/\S/);
      tactics.push({ line: i, text: t, startChar: firstNonWs < 0 ? 0 : firstNonWs });
      i += 1;
    }
    theorems.push({ name, system, statement, tactics, line: startLine });
  }
  return { theorems, diagnostics };
}

function parseTactic(line, lineNo) {
  const parts = line.trim().split(/\s+/);
  if (!parts[0]) return { err: diagnostic(lineNo, "TACTIC_EMPTY", "Empty tactic line.") };
  return { name: parts[0], args: parts.slice(1), line: lineNo };
}

function normalizedSystem(system) {
  return system
    .replace(/\s+with\s+.*$/i, "")
    .trim()
    .replace(/\s+/g, " ")
    .toUpperCase();
}

function isLinearExtractableSystem(system) {
  const normalized = normalizedSystem(system);
  return /^(LL|LL!) IN GENTZEN$/.test(normalized);
}

function isKnownSurfaceSystem(system) {
  const normalized = normalizedSystem(system);
  return [
    "LJP",
    "LKP",
    "NJP",
    "NKP",
    "LJ",
    "LK",
    "NJ",
    "NK",
    "SYSTEM_F IN ND",
  ].includes(normalized);
}

function isPropInteractiveSystem(system) {
  const normalized = normalizedSystem(system);
  return ["NJP", "NKP", "LJP", "LKP", "NJ", "NK", "LJ", "LK"].includes(normalized);
}

function isClassicalPropSystem(system) {
  const normalized = normalizedSystem(system);
  return ["NKP", "LKP", "NK", "LK"].includes(normalized);
}

function compileLinear(thm) {
  if (!isLinearExtractableSystem(thm.system)) {
    return { ok: false, error: diagnostic(thm.line, "SYSTEM_UNSUPPORTED", "Only linear `using LL in GENTZEN ...` is extractable.") };
  }
  let target;
  try {
    target = parseFormula(thm.statement);
  } catch (e) {
    return { ok: false, error: diagnostic(thm.line, "FORMULA_PARSE", String(e.message || e)) };
  }
  const root = { ctx: [], target, node: null };
  const goals = [root];
  for (const tacLine of thm.tactics) {
    if (goals.length === 0) return { ok: false, error: diagnostic(tacLine.line, "NO_GOALS", "No open goals for tactic.") };
    const goal = goals.shift();
    const tac = parseTactic(tacLine.text, tacLine.line);
    if (tac.err) return { ok: false, error: tac.err };
    if (tac.name === "rlolli") {
      if (!goal.target || goal.target.k !== "lolli") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rlolli` expects a lolli goal.") };
      const h = tac.args[0] || `h${goal.ctx.length + 1}`;
      const sub = { ctx: [{ n: h, f: goal.target.l }].concat(goal.ctx), target: goal.target.r, node: null };
      goal.node = { k: "lolliRight", sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "ax") {
      const h = tac.args[0];
      if (!h) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", "`ax` requires a hypothesis name.") };
      const found = goal.ctx.find((x) => x.n === h);
      if (!found) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${h}\`.`) };
      if (!formulaEq(found.f, goal.target)) return { ok: false, error: diagnostic(tac.line, "AX_MISMATCH", `Hypothesis \`${h}\` does not match goal.`) };
      if (goal.ctx.length !== 1) {
        return { ok: false, error: diagnostic(tac.line, "LINEAR_CONTEXT", "`ax` requires exactly one linear hypothesis in scope.") };
      }
      goal.node = { k: "assumption", formula: goal.target };
      continue;
    }
    if (tac.name === "rwith") {
      if (goal.target.k !== "with") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rwith` expects `A & B` goal.") };
      const left = { ctx: goal.ctx.slice(), target: goal.target.l, node: null };
      const right = { ctx: goal.ctx.slice(), target: goal.target.r, node: null };
      goal.node = { k: "withRight", left, right };
      goals.unshift(right);
      goals.unshift(left);
      continue;
    }
    if (tac.name === "rplusl") {
      if (goal.target.k !== "plus") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rplusl` expects `A ⊕ B` goal.") };
      const sub = { ctx: goal.ctx.slice(), target: goal.target.l, node: null };
      goal.node = { k: "plusRightLeft", sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "rplusr") {
      if (goal.target.k !== "plus") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rplusr` expects `A ⊕ B` goal.") };
      const sub = { ctx: goal.ctx.slice(), target: goal.target.r, node: null };
      goal.node = { k: "plusRightRight", sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "rtensor") {
      if (goal.target.k !== "tensor") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rtensor` expects `A ⊗ B` goal.") };
      const hint = tac.args[0];
      let leftCtx = [];
      let rightCtx = goal.ctx.slice();
      if (hint) {
        const idx = goal.ctx.findIndex((x) => x.n === hint);
        if (idx < 0) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown split hint \`${hint}\`.`) };
        leftCtx = [goal.ctx[idx]];
        rightCtx = goal.ctx.slice(0, idx).concat(goal.ctx.slice(idx + 1));
      } else if (goal.ctx.length > 2) {
        return { ok: false, error: diagnostic(tac.line, "TACTIC_UNSUPPORTED", "`rtensor` with more than two linear hypotheses requires a split hint.") };
      }
      const left = { ctx: leftCtx, target: goal.target.l, node: null };
      const right = { ctx: rightCtx, target: goal.target.r, node: null };
      goal.node = {
        k: "tensorRight",
        left,
        right,
        goalCtx: goal.ctx.map((x) => x.f),
        leftFormula: goal.target.l,
        rightFormula: goal.target.r,
      };
      goals.unshift(right);
      goals.unshift(left);
      continue;
    }
    return { ok: false, error: diagnostic(tac.line, "TACTIC_UNSUPPORTED", `Unsupported linear tactic \`${tac.name}\`.`) };
  }
  if (goals.length > 0) {
    return { ok: false, error: diagnostic(thm.line, "UNCLOSED_GOALS", "Proof ended before all goals were solved.") };
  }
  return { ok: true, root };
}

function goalsAtCursorLinear(thm, cursorLine, cursorCharacter) {
  if (!isLinearExtractableSystem(thm.system)) {
    return { ok: false, error: diagnostic(thm.line, "SYSTEM_UNSUPPORTED", "Only linear `using LL in GENTZEN ...` is extractable.") };
  }
  let target;
  try {
    target = parseFormula(thm.statement);
  } catch (e) {
    return { ok: false, error: diagnostic(thm.line, "FORMULA_PARSE", String(e.message || e)) };
  }
  const root = { ctx: [], target, node: null };
  const goals = [root];
  for (const tacLine of thm.tactics) {
    if (tacLine.line > cursorLine) break;
    if (tacLine.line === cursorLine && cursorCharacter <= (tacLine.startChar || 0)) break;
    if (goals.length === 0) return { ok: false, error: diagnostic(tacLine.line, "NO_GOALS", "No open goals for tactic.") };
    const goal = goals.shift();
    const tac = parseTactic(tacLine.text, tacLine.line);
    if (tac.err) return { ok: false, error: tac.err };
    if (tac.name === "rlolli") {
      if (!goal.target || goal.target.k !== "lolli") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rlolli` expects a lolli goal.") };
      const h = tac.args[0] || `h${goal.ctx.length + 1}`;
      const sub = { ctx: [{ n: h, f: goal.target.l }].concat(goal.ctx), target: goal.target.r, node: null };
      goal.node = { k: "lolliRight", sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "ax") {
      const h = tac.args[0];
      if (!h) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", "`ax` requires a hypothesis name.") };
      const found = goal.ctx.find((x) => x.n === h);
      if (!found) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${h}\`.`) };
      if (!formulaEq(found.f, goal.target)) return { ok: false, error: diagnostic(tac.line, "AX_MISMATCH", `Hypothesis \`${h}\` does not match goal.`) };
      if (goal.ctx.length !== 1) {
        return { ok: false, error: diagnostic(tac.line, "LINEAR_CONTEXT", "`ax` requires exactly one linear hypothesis in scope.") };
      }
      goal.node = { k: "assumption", formula: goal.target };
      continue;
    }
    if (tac.name === "rwith") {
      if (goal.target.k !== "with") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rwith` expects `A & B` goal.") };
      const left = { ctx: goal.ctx.slice(), target: goal.target.l, node: null };
      const right = { ctx: goal.ctx.slice(), target: goal.target.r, node: null };
      goal.node = { k: "withRight", left, right };
      goals.unshift(right);
      goals.unshift(left);
      continue;
    }
    if (tac.name === "rplusl") {
      if (goal.target.k !== "plus") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rplusl` expects `A ⊕ B` goal.") };
      const sub = { ctx: goal.ctx.slice(), target: goal.target.l, node: null };
      goal.node = { k: "plusRightLeft", sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "rplusr") {
      if (goal.target.k !== "plus") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rplusr` expects `A ⊕ B` goal.") };
      const sub = { ctx: goal.ctx.slice(), target: goal.target.r, node: null };
      goal.node = { k: "plusRightRight", sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "rtensor") {
      if (goal.target.k !== "tensor") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rtensor` expects `A ⊗ B` goal.") };
      const hint = tac.args[0];
      let leftCtx = [];
      let rightCtx = goal.ctx.slice();
      if (hint) {
        const idx = goal.ctx.findIndex((x) => x.n === hint);
        if (idx < 0) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown split hint \`${hint}\`.`) };
        leftCtx = [goal.ctx[idx]];
        rightCtx = goal.ctx.slice(0, idx).concat(goal.ctx.slice(idx + 1));
      } else if (goal.ctx.length > 2) {
        return { ok: false, error: diagnostic(tac.line, "TACTIC_UNSUPPORTED", "`rtensor` with more than two linear hypotheses requires a split hint.") };
      }
      const left = { ctx: leftCtx, target: goal.target.l, node: null };
      const right = { ctx: rightCtx, target: goal.target.r, node: null };
      goal.node = {
        k: "tensorRight",
        left,
        right,
        goalCtx: goal.ctx.map((x) => x.f),
        leftFormula: goal.target.l,
        rightFormula: goal.target.r,
      };
      goals.unshift(right);
      goals.unshift(left);
      continue;
    }
    return { ok: false, error: diagnostic(tac.line, "TACTIC_UNSUPPORTED", `Unsupported linear tactic \`${tac.name}\`.`) };
  }
  return { ok: true, goals };
}

function goalToView(goal, i) {
  return {
    id: `goal:${i + 1}`,
    hypotheses: goal.ctx.map((h) => ({ name: h.n, type: formulaDisplay(h.f) })),
    target: formulaDisplay(goal.target),
  };
}

function propGoalToView(goal, i) {
  return {
    id: `goal:${i + 1}`,
    hypotheses: goal.ctx.map((h) => ({ name: h.n, type: propDisplay(h.f) })),
    target: propDisplay(goal.target),
  };
}

function goalsAtCursorProp(thm, cursorLine, cursorCharacter) {
  if (!isPropInteractiveSystem(thm.system)) {
    return { ok: false, error: diagnostic(thm.line, "SYSTEM_UNSUPPORTED", "Unsupported interactive proposition system.") };
  }
  let target;
  try {
    target = parsePropFormula(thm.statement);
  } catch (e) {
    return { ok: false, error: diagnostic(thm.line, "FORMULA_PARSE", String(e.message || e)) };
  }
  const root = { ctx: [], target };
  const goals = [root];
  for (const tacLine of thm.tactics) {
    if (tacLine.line > cursorLine) break;
    if (tacLine.line === cursorLine && cursorCharacter <= (tacLine.startChar || 0)) break;
    if (goals.length === 0) return { ok: false, error: diagnostic(tacLine.line, "NO_GOALS", "No open goals for tactic.") };
    const goal = goals.shift();
    const tac = parseTactic(tacLine.text, tacLine.line);
    if (tac.err) return { ok: false, error: tac.err };

    if (tac.name === "intro") {
      if (!goal.target || goal.target.k !== "imp") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`intro` expects an implication goal.") };
      const h = tac.args[0] || `h${goal.ctx.length + 1}`;
      goals.unshift({ ctx: [{ n: h, f: goal.target.l }].concat(goal.ctx), target: goal.target.r });
      continue;
    }
    if (tac.name === "cases") {
      const m = tacLine.text.match(/^cases\s+at\s+([A-Za-z_][A-Za-z0-9_]*)\s+as\s+([A-Za-z_][A-Za-z0-9_]*)\s+([A-Za-z_][A-Za-z0-9_]*)$/);
      if (!m) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", "`cases` usage: cases at h as h1 h2") };
      const [, src, leftName, rightName] = m;
      const idx = goal.ctx.findIndex((x) => x.n === src);
      if (idx < 0) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${src}\`.`) };
      const found = goal.ctx[idx];
      if (!found.f || found.f.k !== "or") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`cases` expects a disjunction hypothesis.") };
      const base = goal.ctx.slice(0, idx).concat(goal.ctx.slice(idx + 1));
      const gRight = { ctx: [{ n: rightName, f: found.f.r }].concat(base), target: goal.target };
      const gLeft = { ctx: [{ n: leftName, f: found.f.l }].concat(base), target: goal.target };
      goals.unshift(gRight);
      goals.unshift(gLeft);
      continue;
    }
    if (tac.name === "left") {
      if (!goal.target || goal.target.k !== "or") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`left` expects a disjunction goal.") };
      goals.unshift({ ctx: goal.ctx.slice(), target: goal.target.l });
      continue;
    }
    if (tac.name === "right") {
      if (!goal.target || goal.target.k !== "or") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`right` expects a disjunction goal.") };
      goals.unshift({ ctx: goal.ctx.slice(), target: goal.target.r });
      continue;
    }
    if (tac.name === "assumption") {
      const h = tac.args[0];
      if (!h) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", "`assumption` requires a hypothesis name.") };
      const found = goal.ctx.find((x) => x.n === h);
      if (!found) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${h}\`.`) };
      if (!formulaEq(found.f, goal.target)) return { ok: false, error: diagnostic(tac.line, "ASSUMPTION_MISMATCH", `Hypothesis \`${h}\` does not match goal.`) };
      continue;
    }
    if (tac.name === "apply") {
      const h = tac.args[0];
      if (!h) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", "`apply` requires a hypothesis name.") };
      const found = goal.ctx.find((x) => x.n === h);
      if (!found) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${h}\`.`) };
      if (!found.f || found.f.k !== "imp") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`apply` expects implication hypothesis.") };
      if (!formulaEq(found.f.r, goal.target)) return { ok: false, error: diagnostic(tac.line, "APPLY_MISMATCH", `Conclusion of \`${h}\` does not match goal.`) };
      goals.unshift({ ctx: goal.ctx.slice(), target: found.f.l });
      continue;
    }
    if (tac.name === "by_contra") {
      if (!isClassicalPropSystem(thm.system)) {
        return { ok: false, error: diagnostic(tac.line, "TACTIC_FORBIDDEN", "`by_contra` is only allowed in classical systems (NK/NKP/LK/LKP).") };
      }
      const h = tac.args[0] || `h${goal.ctx.length + 1}`;
      goals.unshift({
        ctx: [{ n: h, f: { k: "imp", l: goal.target, r: { k: "bottom" } } }].concat(goal.ctx),
        target: { k: "bottom" },
      });
      continue;
    }
    return { ok: false, error: diagnostic(tac.line, "TACTIC_UNSUPPORTED", `Unsupported proposition tactic \`${tac.name}\`.`) };
  }
  return { ok: true, goals };
}

function compileProp(thm) {
  if (!isPropInteractiveSystem(thm.system)) {
    return { ok: false, error: diagnostic(thm.line, "SYSTEM_UNSUPPORTED", "Unsupported proposition system.") };
  }
  const snap = goalsAtCursorProp(thm, Number.POSITIVE_INFINITY, 0);
  if (!snap.ok) return { ok: false, error: snap.error };
  if (snap.goals.length > 0) {
    return { ok: false, error: diagnostic(thm.line, "UNCLOSED_GOALS", "Proof ended before all goals were solved.") };
  }
  return { ok: true };
}

function renderNode(node, indent) {
  const pad = " ".repeat(indent);
  if (node.k === "assumption") return `${pad}exact LinearLogic.assumption`;
  if (node.k === "lolliRight") {
    return `${pad}apply LinearLogic.lolliRight\n${renderNode(node.sub.node, indent)}`;
  }
  if (node.k === "withRight") {
    return `${pad}apply LinearLogic.withRight\n${pad}·\n${renderNode(node.left.node, indent + 2)}\n${pad}·\n${renderNode(node.right.node, indent + 2)}`;
  }
  if (node.k === "plusRightLeft") {
    return `${pad}apply LinearLogic.plusRightLeft\n${renderNode(node.sub.node, indent)}`;
  }
  if (node.k === "plusRightRight") {
    return `${pad}apply LinearLogic.plusRightRight\n${renderNode(node.sub.node, indent)}`;
  }
  if (node.k === "tensorRight") {
    const leftAnt = listLean(contextFormulas(node.left.ctx));
    const rightAnt = listLean(contextFormulas(node.right.ctx));
    const body =
      `${pad}apply (LinearLogic.tensorRight ` +
      `(leftAntecedent := ${leftAnt}) ` +
      `(leftSuccedent := []) ` +
      `(rightAntecedent := ${rightAnt}) ` +
      `(rightSuccedent := []) ` +
      `(leftFormula := ${formulaLean(node.leftFormula)}) ` +
      `(rightFormula := ${formulaLean(node.rightFormula)}))\n` +
      `${pad}·\n${renderNode(node.left.node, indent + 2)}\n${pad}·\n${renderNode(node.right.node, indent + 2)}`;
    const built = builtAntecedent(node);
    const expected = node.goalCtx || built;
    return wrapExchangeLeft(body, built, expected, indent);
  }
  throw new Error("Unknown node kind.");
}

function builtAntecedent(node) {
  if (node.k === "assumption") return [node.formula];
  if (node.k === "lolliRight") return builtAntecedent(node.sub.node).slice(1);
  if (node.k === "withRight") return builtAntecedent(node.left.node);
  if (node.k === "plusRightLeft" || node.k === "plusRightRight") return builtAntecedent(node.sub.node);
  if (node.k === "tensorRight") return contextFormulas(node.left.ctx).concat(contextFormulas(node.right.ctx));
  return [];
}

function contextFormulas(ctx) {
  return (ctx || []).map((x) => x.f);
}

function wrapExchangeLeft(body, built, expected, indent) {
  const pad = " ".repeat(indent);
  const b = built.map((x) => JSON.stringify(x)).join("|");
  const e = expected.map((x) => JSON.stringify(x)).join("|");
  if (b === e) return body;
  if (built.length !== expected.length) {
    throw new Error("Internal context mismatch.");
  }
  const plan = bubbleSwapPlan(expected.slice(), built.slice());
  if (!plan) throw new Error("Could not synthesize exchangeLeft normalization.");
  const prefix = plan
    .map(
      (step) =>
        `${pad}apply (LinearLogic.exchangeLeft ` +
        `(leftContext := ${listLean(step.left)}) ` +
        `(rightContext := ${listLean(step.right)}) ` +
        `(firstFormula := ${formulaLean(step.first)}) ` +
        `(secondFormula := ${formulaLean(step.second)}))`
    )
    .join("\n");
  return `${prefix}\n${body}`;
}

function listLean(xs) {
  if (!xs.length) return "[]";
  return `[${xs.map(formulaLean).join(", ")}]`;
}

function bubbleSwapPlan(from, to) {
  const enc = (f) => JSON.stringify(f);
  const arr = from.map(enc);
  const actual = from.slice();
  const tgt = to.map(enc);
  const steps = [];
  for (let i = 0; i < tgt.length; i += 1) {
    const want = tgt[i];
    let j = i;
    while (j < arr.length && arr[j] !== want) j += 1;
    if (j === arr.length) return null;
    while (j > i) {
      steps.push({
        left: actual.slice(0, j - 1),
        first: actual[j],
        second: actual[j - 1],
        right: actual.slice(j + 1),
      });
      const tmp = arr[j];
      arr[j] = arr[j - 1];
      arr[j - 1] = tmp;
      const tf = actual[j];
      actual[j] = actual[j - 1];
      actual[j - 1] = tf;
      j -= 1;
    }
  }
  return steps;
}

function theoremLean(thm, proofRoot) {
  const nm = thm.name.replace(/[^A-Za-z0-9_]/g, "_");
  return [
    "import FastProofTheory.Proof.LinearLogic",
    "",
    "open FastProofTheory.Proof",
    "open LinearFormula",
    "",
    `def ${nm}_extracted : LinearLogic [] [${formulaLean(parseFormula(thm.statement))}] := by`,
    renderNode(proofRoot.node, 2),
    "",
  ].join("\n");
}

function checkDocument(params) {
  const parsed = parseDocument(params.text || "");
  const diagnostics = parsed.diagnostics.slice();
  const theoremStatuses = [];
  for (const thm of parsed.theorems) {
    if (isLinearExtractableSystem(thm.system)) {
      const compiled = compileLinear(thm);
      theoremStatuses.push({ name: thm.name, line: thm.line, verified: !!compiled.ok });
      if (!compiled.ok) diagnostics.push(compiled.error);
      continue;
    }
    if (isPropInteractiveSystem(thm.system)) {
      const compiled = compileProp(thm);
      theoremStatuses.push({ name: thm.name, line: thm.line, verified: !!compiled.ok });
      if (!compiled.ok) diagnostics.push(compiled.error);
      continue;
    }
    theoremStatuses.push({ name: thm.name, line: thm.line, verified: false });
    if (!isKnownSurfaceSystem(thm.system)) {
      diagnostics.push(diagnostic(thm.line, "SYSTEM_UNKNOWN", `Unknown proof system \`${thm.system}\`.`));
    }
  }

  let goals = [];
  const cursorLine = params && params.cursor && Number.isInteger(params.cursor.line)
    ? params.cursor.line
    : null;
  const cursorCharacter = params && params.cursor && Number.isInteger(params.cursor.character)
    ? params.cursor.character
    : 0;
  if (cursorLine !== null) {
    const active = parsed.theorems.find((thm, idx) => {
      const next = parsed.theorems[idx + 1];
      const endLine = next ? next.line - 1 : Number.POSITIVE_INFINITY;
      return cursorLine >= thm.line && cursorLine <= endLine;
    });
    if (active) {
      if (isLinearExtractableSystem(active.system)) {
        const snap = goalsAtCursorLinear(active, cursorLine, cursorCharacter);
        if (snap.ok) {
          goals = snap.goals.map(goalToView);
        } else {
          diagnostics.push(snap.error);
        }
      } else if (isPropInteractiveSystem(active.system)) {
        const snap = goalsAtCursorProp(active, cursorLine, cursorCharacter);
        if (snap.ok) {
          goals = snap.goals.map(propGoalToView);
        } else {
          diagnostics.push(snap.error);
        }
      }
    }
  }

  const seenDiag = new Set();
  const dedupedDiagnostics = [];
  for (const d of diagnostics) {
    const key = `${d.code}|${d.message}|${d.range.start.line}|${d.range.start.character}`;
    if (seenDiag.has(key)) continue;
    seenDiag.add(key);
    dedupedDiagnostics.push(d);
  }

  return {
    diagnostics: dedupedDiagnostics,
    goals,
    display: {
      title: "proofAssistant",
      status: diagnostics.length ? "Errors detected." : "No parser/checker errors.",
      sections: [],
    },
    theoremStatuses,
  };
}

function extractDocument(text, theoremName) {
  const parsed = parseDocument(text);
  if (parsed.diagnostics.length) {
    return { ok: false, error: `Parse failed: ${parsed.diagnostics[0].message}` };
  }
  const thm = parsed.theorems.find((t) => t.name === theoremName);
  if (!thm) return { ok: false, error: `Theorem \`${theoremName}\` not found.` };
  const compiled = compileLinear(thm);
  if (!compiled.ok) return { ok: false, error: compiled.error.message };
  return { ok: true, source: theoremLean(thm, compiled.root) };
}

const mypaExports = {
  domainInfo: DOMAIN_INFO,
  checkDocument,
  extractDocument,
};

if (typeof module !== "undefined" && module.exports) {
  module.exports = mypaExports;
}

if (typeof globalThis !== "undefined") {
  globalThis.__mypaProofAssistant = mypaExports;
}
