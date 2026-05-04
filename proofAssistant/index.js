"use strict";

const DOMAIN_INFO = {
  symbolCompletions: [
    { label: "\\lolli", insertText: "⊸", detail: "Symbol", documentation: "Linear implication / lolli." },
    { label: "\\imp", insertText: "->", detail: "Symbol", documentation: "Propositional implication." },
    { label: "\\tensor", insertText: "⊗", detail: "Symbol", documentation: "Tensor / multiplicative conjunction." },
    { label: "\\par", insertText: "⅋", detail: "Symbol", documentation: "Par / multiplicative disjunction." },
    { label: "\\oplus", insertText: "⊕", detail: "Symbol", documentation: "Plus / additive disjunction." },
    { label: "\\and", insertText: "∧", detail: "Symbol", documentation: "Propositional conjunction." },
    { label: "\\or", insertText: "∨", detail: "Symbol", documentation: "Propositional disjunction." },
    { label: "\\with", insertText: "&", detail: "Symbol", documentation: "Linear additive conjunction." },
    { label: "\\bang", insertText: "!", detail: "Symbol", documentation: "Linear exponential bang." },
    { label: "\\why", insertText: "?", detail: "Symbol", documentation: "Linear exponential why-not." },
    { label: "\\^bot", insertText: "^bot", detail: "Syntax", documentation: "Postfix classical linear negation." },
    { label: "\\one", insertText: "1", detail: "Symbol", documentation: "Linear multiplicative unit." },
    { label: "\\top", insertText: "top", detail: "Symbol", documentation: "Linear additive truth." },
    { label: "\\zero", insertText: "0", detail: "Symbol", documentation: "Linear additive falsity." },
  ],
  directives: [
    {
      label: "#help",
      insertText: "#help CLLp",
      detail: "Directive",
      documentation: "Show available proof-system info.",
    },
  ],
  systems: [
    {
      key: "CLLp",
      aliases: [],
      title: "Classical Linear Logic",
      summary: "Linear sequent tactics mapped to FastProofTheory.Proof.LinearLogic constructors.",
      language: ["linear"],
      tactics: [
        { name: "ax", title: "Assumption", display: "ax h", summary: "Close goal using matching hypothesis." },
        { name: "rlolli", title: "⊸ Right", display: "rlolli h", summary: "Introduce antecedent from lolli goal." },
        { name: "rwith", title: "& Right", display: "rwith", summary: "Split goal into two conjunctive goals." },
        { name: "rplusl", title: "⊕ Right Left", display: "rplusl", summary: "Prove left disjunct." },
        { name: "rplusr", title: "⊕ Right Right", display: "rplusr", summary: "Prove right disjunct." },
        { name: "rtensor", title: "⊗ Right", display: "rtensor h", summary: "Split context and prove tensor components." },
        { name: "rpar", title: "⅋ Right", display: "rpar", summary: "Expose both sides of a par goal on the right." },
        { name: "rbot", title: "bot Right", display: "rbot", summary: "Add bottom on the right using linear negation support." },
        { name: "lwithl", title: "& Left Left", display: "lwithl at h", summary: "Use the left component of an additive conjunction hypothesis." },
        { name: "lwithr", title: "& Left Right", display: "lwithr at h", summary: "Use the right component of an additive conjunction hypothesis." },
        { name: "ltensor", title: "⊗ Left", display: "ltensor at h as h1 h2", summary: "Destructure tensor hypothesis into two linear hypotheses." },
        { name: "lplus", title: "⊕ Left", display: "lplus at h as h1 h2", summary: "Case split on additive disjunction hypothesis." },
        { name: "rone", title: "1 Right", display: "rone", summary: "Close an empty-context multiplicative unit goal." },
        { name: "lone", title: "1 Left", display: "lone at h", summary: "Discard a multiplicative unit hypothesis." },
        { name: "rtop", title: "top Right", display: "rtop", summary: "Close an additive truth goal." },
        { name: "lzero", title: "0 Left", display: "lzero at h", summary: "Close any goal from additive falsity on the left." },
        { name: "lbang", title: "! Left", display: "lbang at h", summary: "Derelict a bang hypothesis to a linear hypothesis." },
        { name: "weakenbang", title: "! Weakening Left", display: "weakenbang at h", summary: "Remove an unused bang hypothesis using exponential weakening." },
        { name: "rbang", title: "! Right", display: "rbang", summary: "Promote goal to bang when context satisfies side condition." },
        { name: "contractbang", title: "! Contraction Left", display: "contractbang at h as h1 h2", summary: "Duplicate a bang hypothesis using the exponential structural rule." },
      ],
      checkedNow: ["ax", "rlolli", "rwith", "rplusl", "rplusr", "rtensor", "rpar", "rbot", "lwithl", "lwithr", "ltensor", "lplus", "rone", "lone", "rtop", "lzero", "lbang", "weakenbang", "rbang", "contractbang"],
    },
    {
      key: "ILLp",
      aliases: [],
      title: "Intuitionistic Linear Logic (propositional fragment)",
      summary: "Single-conclusion linear sequent tactics for the intuitionistic propositional fragment.",
      language: ["linear"],
      tactics: [
        { name: "ax", title: "Assumption", display: "ax h", summary: "Close goal using matching hypothesis." },
        { name: "rlolli", title: "⊸ Right", display: "rlolli h", summary: "Introduce antecedent from lolli goal." },
        { name: "rwith", title: "& Right", display: "rwith", summary: "Split goal into two conjunctive goals." },
        { name: "rplusl", title: "⊕ Right Left", display: "rplusl", summary: "Prove left disjunct." },
        { name: "rplusr", title: "⊕ Right Right", display: "rplusr", summary: "Prove right disjunct." },
        { name: "rtensor", title: "⊗ Right", display: "rtensor h", summary: "Split context and prove tensor components." },
        { name: "lwithl", title: "& Left Left", display: "lwithl at h", summary: "Use the left component of an additive conjunction hypothesis." },
        { name: "lwithr", title: "& Left Right", display: "lwithr at h", summary: "Use the right component of an additive conjunction hypothesis." },
        { name: "ltensor", title: "⊗ Left", display: "ltensor at h as h1 h2", summary: "Destructure tensor hypothesis into two linear hypotheses." },
        { name: "lplus", title: "⊕ Left", display: "lplus at h as h1 h2", summary: "Case split on additive disjunction hypothesis." },
        { name: "rone", title: "1 Right", display: "rone", summary: "Close an empty-context multiplicative unit goal." },
        { name: "lone", title: "1 Left", display: "lone at h", summary: "Discard a multiplicative unit hypothesis." },
        { name: "rtop", title: "top Right", display: "rtop", summary: "Close an additive truth goal." },
        { name: "lzero", title: "0 Left", display: "lzero at h", summary: "Close any goal from additive falsity on the left." },
        { name: "lbang", title: "! Left", display: "lbang at h", summary: "Derelict a bang hypothesis to a linear hypothesis." },
        { name: "weakenbang", title: "! Weakening Left", display: "weakenbang at h", summary: "Remove an unused bang hypothesis using exponential weakening." },
        { name: "rbang", title: "! Right", display: "rbang", summary: "Promote goal to bang when context satisfies side condition." },
        { name: "contractbang", title: "! Contraction Left", display: "contractbang at h as h1 h2", summary: "Duplicate a bang hypothesis using the exponential structural rule." },
      ],
      checkedNow: ["ax", "rlolli", "rwith", "rplusl", "rplusr", "rtensor", "lwithl", "lwithr", "ltensor", "lplus", "rone", "lone", "rtop", "lzero", "lbang", "weakenbang", "rbang", "contractbang"],
    },
  ],
  keywords: ["theorem", "using", "by"],
  operators: ["⊸", "⊗", "⅋", "&", "⊕", "!", "?", "^", "(", ")", "1", "0", "top", "bot"],
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
    if (c === "⊥") {
      tokens.push({ t: "id", v: "⊥" });
      i += 1;
      continue;
    }
    if (["(", ")", "⊗", "⅋", "&", "⊕", "⊸", "!", "?", "^"].includes(c)) {
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
    let base;
    if (tk.t === "id") {
      consume();
      if (tk.v === "1") base = { k: "one" };
      else if (tk.v === "0") base = { k: "zero" };
      else if (/^top$/i.test(tk.v)) base = { k: "top" };
      else if (/^(bot|bottom|⊥)$/i.test(tk.v)) base = { k: "bottom" };
      else base = { k: "atom", n: tk.v };
    } else if (tk.t === "op" && tk.v === "!") {
      consume();
      base = { k: "bang", a: parseAtom() };
    } else if (tk.t === "op" && tk.v === "?") {
      consume();
      base = { k: "whyNot", a: parseAtom() };
    } else if (tk.t === "(") {
      consume();
      base = parseLolli();
      if (!peek() || peek().t !== ")") throw new Error("Missing closing ')'.");
      consume();
    } else {
      throw new Error(`Unexpected token '${tk.v || tk.t}'.`);
    }
    while (peek() && peek().t === "op" && peek().v === "^") {
      consume();
      const suffix = consume();
      if (!suffix || suffix.t !== "id" || !/^(bot|bottom)$/i.test(suffix.v)) {
        throw new Error("Expected `bot` after negation marker `^`.");
      }
      base = { k: "lolli", l: base, r: { k: "bottom" } };
    }
    return base;
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
    let left = parsePar();
    while (peek() && peek().t === "op" && (peek().v === "&" || peek().v === "⊕")) {
      const op = consume().v;
      const right = parsePar();
      left = { k: op === "&" ? "with" : "plus", l: left, r: right };
    }
    return left;
  }
  function parsePar() {
    let left = parseTensor();
    while (peek() && peek().t === "op" && peek().v === "⅋") {
      consume();
      const right = parseTensor();
      left = { k: "par", l: left, r: right };
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
    case "one":
      return "1";
    case "zero":
      return "0";
    case "top":
      return "top";
    case "bottom":
      return "bot";
    case "bang":
      return `!${formulaDisplay(f.a)}`;
    case "whyNot":
      return `?${formulaDisplay(f.a)}`;
    case "tensor":
      return `(${formulaDisplay(f.l)} ⊗ ${formulaDisplay(f.r)})`;
    case "par":
      return `(${formulaDisplay(f.l)} ⅋ ${formulaDisplay(f.r)})`;
    case "with":
      return `(${formulaDisplay(f.l)} & ${formulaDisplay(f.r)})`;
    case "plus":
      return `(${formulaDisplay(f.l)} ⊕ ${formulaDisplay(f.r)})`;
    case "lolli":
      if (f.r && f.r.k === "bottom") return `${formulaDisplayNegatedBase(f.l)}^bot`;
      return `(${formulaDisplay(f.l)} ⊸ ${formulaDisplay(f.r)})`;
    default:
      return "?";
  }
}

function formulaDisplayNegatedBase(f) {
  if (f && (f.k === "atom" || f.k === "one" || f.k === "zero" || f.k === "top" || f.k === "bottom")) {
    return formulaDisplay(f);
  }
  if (f && (f.k === "tensor" || f.k === "par" || f.k === "with" || f.k === "plus")) {
    return formulaDisplay(f);
  }
  if (f && f.k === "lolli") {
    return f.r && f.r.k === "bottom" ? `(${formulaDisplay(f)})` : formulaDisplay(f);
  }
  return `(${formulaDisplay(f)})`;
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

function formulaLean(f, mode = "CLLP") {
  const formulaType = mode === "ILLP" ? "IntuitionisticLinearFormula" : "LinearFormula";
  switch (f.k) {
    case "atom": return `(${formulaType}.atom ${JSON.stringify(f.n)})`;
    case "one": return `${formulaType}.one`;
    case "zero": return `${formulaType}.zero`;
    case "top": return `${formulaType}.top`;
    case "bottom": return "LinearFormula.bottom";
    case "bang": return `(${formulaType}.bang ${formulaLean(f.a, mode)})`;
    case "whyNot": return `(LinearFormula.whyNot ${formulaLean(f.a, mode)})`;
    case "par": return `(LinearFormula.par ${formulaLean(f.l, mode)} ${formulaLean(f.r, mode)})`;
    case "tensor": return `(${formulaType}.tensor ${formulaLean(f.l, mode)} ${formulaLean(f.r, mode)})`;
    case "with": return `(${formulaType}.with ${formulaLean(f.l, mode)} ${formulaLean(f.r, mode)})`;
    case "plus": return `(${formulaType}.plus ${formulaLean(f.l, mode)} ${formulaLean(f.r, mode)})`;
    case "lolli": return `(${formulaType}.lolli ${formulaLean(f.l, mode)} ${formulaLean(f.r, mode)})`;
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
    const m = line.match(/^theorem\s+([A-Za-z_][A-Za-z0-9_]*)\s+using\s+(.+?)\s*:\s*(.+?)\s*:=\s*by\s*$/);
    if (!m) {
      diagnostics.push(diagnostic(i, "PARSE_TOPLEVEL", "Expected theorem header `theorem ... := by`."));
      i += 1;
      continue;
    }
    const [, name, system, statement] = m;
    const tactics = [];
    const startLine = i;
    i += 1;
    while (i < lines.length) {
      const t = lines[i].trim();
      if (!t || t.startsWith("--")) {
        i += 1;
        continue;
      }
      if (/^theorem\s+/.test(t)) break;
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
    .trim()
    .replace(/\s+/g, " ")
    .toUpperCase();
}

function isLinearExtractableSystem(system) {
  return linearSystemMode(system) !== null;
}

function linearSystemMode(system) {
  const normalized = normalizedSystem(system);
  if (normalized === "CLLP") return "CLLP";
  if (normalized === "ILLP") return "ILLP";
  return null;
}

function isKnownSurfaceSystem(system) {
  const normalized = normalizedSystem(system);
  return [
    "CLLP",
    "ILLP",
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

function validateLinearFormulaForSystem(formula, mode) {
  if (mode !== "ILLP") return null;
  function hasForbidden(node) {
    if (!node || typeof node !== "object") return null;
    if (node.k === "par") return "⅋";
    if (node.k === "whyNot") return "?";
    if (node.k === "bottom") return "bot";
    return hasForbidden(node.a) || hasForbidden(node.l) || hasForbidden(node.r);
  }
  const bad = hasForbidden(formula);
  if (!bad) return null;
  return `Formula uses \`${bad}\`, which is outside the currently supported ILLp fragment in MyPA.`;
}

function isPropInteractiveSystem(system) {
  const normalized = normalizedSystem(system);
  return ["NJP", "NKP", "LJP", "LKP", "NJ", "NK", "LJ", "LK"].includes(normalized);
}

function isClassicalPropSystem(system) {
  const normalized = normalizedSystem(system);
  return ["NKP", "LKP", "NK", "LK"].includes(normalized);
}

function parseAtAs(tacLine, tacName) {
  const m = tacLine.text.match(new RegExp(`^${tacName}\\s+at\\s+([A-Za-z_][A-Za-z0-9_]*)\\s+as\\s+([A-Za-z_][A-Za-z0-9_]*)\\s+([A-Za-z_][A-Za-z0-9_]*)$`));
  if (!m) return null;
  return { src: m[1], left: m[2], right: m[3] };
}

function parseAtOnly(tacLine, tacName) {
  const m = tacLine.text.match(new RegExp(`^${tacName}\\s+at\\s+([A-Za-z_][A-Za-z0-9_]*)$`));
  if (!m) return null;
  return { src: m[1] };
}

function ctxAllBang(ctx) {
  return (ctx || []).every((h) => h && h.f && h.f.k === "bang");
}

function makeLinearGoal(ctx, succedent, node = null) {
  const normalizedSuccedent = succedent.slice();
  return { ctx, target: normalizedSuccedent[0] || null, succedent: normalizedSuccedent, node };
}

function goalSuccedent(goal) {
  if (Array.isArray(goal.succedent)) return goal.succedent;
  return goal.target ? [goal.target] : [];
}

function goalTarget(goal) {
  return goalSuccedent(goal)[0] || null;
}

function goalRestSuccedent(goal) {
  return goalSuccedent(goal).slice(1);
}

function compileLinear(thm) {
  const mode = linearSystemMode(thm.system);
  if (!mode) {
    return { ok: false, error: diagnostic(thm.line, "SYSTEM_UNSUPPORTED", "Only linear `using CLLp` or `using ILLp` is extractable.") };
  }
  let target;
  try {
    target = parseFormula(thm.statement);
  } catch (e) {
    return { ok: false, error: diagnostic(thm.line, "FORMULA_PARSE", String(e.message || e)) };
  }
  const formulaSystemError = validateLinearFormulaForSystem(target, mode);
  if (formulaSystemError) {
    return { ok: false, error: diagnostic(thm.line, "FORMULA_SYSTEM_MISMATCH", formulaSystemError) };
  }
  const root = makeLinearGoal([], [target]);
  const goals = [root];
  for (const tacLine of thm.tactics) {
    if (goals.length === 0) return { ok: false, error: diagnostic(tacLine.line, "NO_GOALS", "No open goals for tactic.") };
    const goal = goals.shift();
    const tac = parseTactic(tacLine.text, tacLine.line);
    if (tac.err) return { ok: false, error: tac.err };
    if (tac.name === "rlolli") {
      const target = goalTarget(goal);
      if (!target || target.k !== "lolli") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rlolli` expects a lolli goal.") };
      const h = tac.args[0] || `h${goal.ctx.length + 1}`;
      const sub = makeLinearGoal([{ n: h, f: target.l }].concat(goal.ctx), [target.r].concat(goalRestSuccedent(goal)));
      goal.node = { k: "lolliRight", sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "ax") {
      const h = tac.args[0];
      const target = goalTarget(goal);
      if (!h) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", "`ax` requires a hypothesis name.") };
      const found = goal.ctx.find((x) => x.n === h);
      if (!found) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${h}\`.`) };
      if (!formulaEq(found.f, target)) return { ok: false, error: diagnostic(tac.line, "AX_MISMATCH", `Hypothesis \`${h}\` does not match goal.`) };
      if (goal.ctx.length !== 1) {
        return { ok: false, error: diagnostic(tac.line, "LINEAR_CONTEXT", "`ax` requires exactly one linear hypothesis in scope.") };
      }
      if (goalSuccedent(goal).length !== 1) {
        return { ok: false, error: diagnostic(tac.line, "LINEAR_SUCCEDENT", "`ax` requires exactly one formula on the right.") };
      }
      goal.node = { k: "assumption", formula: target };
      continue;
    }
    if (tac.name === "rwith") {
      const target = goalTarget(goal);
      if (!target || target.k !== "with") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rwith` expects `A & B` goal.") };
      const left = makeLinearGoal(goal.ctx.slice(), [target.l].concat(goalRestSuccedent(goal)));
      const right = makeLinearGoal(goal.ctx.slice(), [target.r].concat(goalRestSuccedent(goal)));
      goal.node = { k: "withRight", left, right };
      goals.unshift(right);
      goals.unshift(left);
      continue;
    }
    if (tac.name === "lwithl" || tac.name === "lwithr") {
      const parsed = parseAtOnly(tacLine, tac.name);
      if (!parsed) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", `\`${tac.name}\` usage: ${tac.name} at h`) };
      const idx = goal.ctx.findIndex((x) => x.n === parsed.src);
      if (idx < 0) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${parsed.src}\`.`) };
      const found = goal.ctx[idx];
      if (!found.f || found.f.k !== "with") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", `\`${tac.name}\` expects a with hypothesis.`) };
      const ctx = goal.ctx.slice();
      ctx[idx] = { n: parsed.src, f: tac.name === "lwithl" ? found.f.l : found.f.r };
      const sub = makeLinearGoal(ctx, goalSuccedent(goal));
      goal.node = {
        k: tac.name === "lwithl" ? "withLeftLeft" : "withLeftRight",
        leftFormula: found.f.l,
        rightFormula: found.f.r,
        baseFormulas: contextFormulas(goal.ctx.slice(0, idx).concat(goal.ctx.slice(idx + 1))),
        goalCtx: contextFormulas(goal.ctx),
        sub,
      };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "rplusl") {
      const target = goalTarget(goal);
      if (!target || target.k !== "plus") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rplusl` expects `A ⊕ B` goal.") };
      const sub = makeLinearGoal(goal.ctx.slice(), [target.l].concat(goalRestSuccedent(goal)));
      goal.node = { k: "plusRightLeft", sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "rplusr") {
      const target = goalTarget(goal);
      if (!target || target.k !== "plus") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rplusr` expects `A ⊕ B` goal.") };
      const sub = makeLinearGoal(goal.ctx.slice(), [target.r].concat(goalRestSuccedent(goal)));
      goal.node = { k: "plusRightRight", sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "rpar") {
      if (mode !== "CLLP") return { ok: false, error: diagnostic(tac.line, "TACTIC_FORBIDDEN", "`rpar` is only available for CLLp.") };
      const target = goalTarget(goal);
      if (!target || target.k !== "par") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rpar` expects `A ⅋ B` goal.") };
      const sub = makeLinearGoal(goal.ctx.slice(), [target.l, target.r].concat(goalRestSuccedent(goal)));
      goal.node = { k: "parRight", leftFormula: target.l, rightFormula: target.r, sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "rbot") {
      if (mode !== "CLLP") return { ok: false, error: diagnostic(tac.line, "TACTIC_FORBIDDEN", "`rbot` is only available for CLLp.") };
      const target = goalTarget(goal);
      if (!target || target.k !== "bottom") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rbot` expects a `bot` goal on the right.") };
      const sub = makeLinearGoal(goal.ctx.slice(), goalRestSuccedent(goal));
      goal.node = { k: "bottomRight", sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "rtensor") {
      const target = goalTarget(goal);
      if (!target || target.k !== "tensor") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rtensor` expects `A ⊗ B` goal.") };
      if (goalRestSuccedent(goal).length !== 0) return { ok: false, error: diagnostic(tac.line, "TACTIC_UNSUPPORTED", "`rtensor` is only supported with a single right-hand goal.") };
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
      const left = makeLinearGoal(leftCtx, [target.l]);
      const right = makeLinearGoal(rightCtx, [target.r]);
      goal.node = {
        k: "tensorRight",
        left,
        right,
        goalCtx: goal.ctx.map((x) => x.f),
        leftFormula: target.l,
        rightFormula: target.r,
      };
      goals.unshift(right);
      goals.unshift(left);
      continue;
    }
    if (tac.name === "ltensor") {
      const parsed = parseAtAs(tacLine, "ltensor");
      if (!parsed) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", "`ltensor` usage: ltensor at h as h1 h2") };
      const idx = goal.ctx.findIndex((x) => x.n === parsed.src);
      if (idx < 0) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${parsed.src}\`.`) };
      const found = goal.ctx[idx];
      if (!found.f || found.f.k !== "tensor") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`ltensor` expects a tensor hypothesis.") };
      const base = goal.ctx.slice(0, idx).concat(goal.ctx.slice(idx + 1));
      const sub = makeLinearGoal([{ n: parsed.left, f: found.f.l }, { n: parsed.right, f: found.f.r }].concat(base), goalSuccedent(goal));
      goal.node = {
        k: "tensorLeft",
        srcName: parsed.src,
        leftFormula: found.f.l,
        rightFormula: found.f.r,
        baseFormulas: contextFormulas(base),
        goalCtx: contextFormulas(goal.ctx),
        sub,
      };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "lplus") {
      const parsed = parseAtAs(tacLine, "lplus");
      if (!parsed) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", "`lplus` usage: lplus at h as h1 h2") };
      const idx = goal.ctx.findIndex((x) => x.n === parsed.src);
      if (idx < 0) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${parsed.src}\`.`) };
      const found = goal.ctx[idx];
      if (!found.f || found.f.k !== "plus") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`lplus` expects a plus hypothesis.") };
      const base = goal.ctx.slice(0, idx).concat(goal.ctx.slice(idx + 1));
      const left = makeLinearGoal([{ n: parsed.left, f: found.f.l }].concat(base), goalSuccedent(goal));
      const right = makeLinearGoal([{ n: parsed.right, f: found.f.r }].concat(base), goalSuccedent(goal));
      goal.node = {
        k: "plusLeft",
        srcName: parsed.src,
        leftFormula: found.f.l,
        rightFormula: found.f.r,
        baseFormulas: contextFormulas(base),
        goalCtx: contextFormulas(goal.ctx),
        left,
        right,
      };
      goals.unshift(right);
      goals.unshift(left);
      continue;
    }
    if (tac.name === "rone") {
      const target = goalTarget(goal);
      if (!target || target.k !== "one") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rone` expects goal `1`.") };
      if (goalRestSuccedent(goal).length !== 0) return { ok: false, error: diagnostic(tac.line, "TACTIC_UNSUPPORTED", "`rone` is only supported with a single right-hand goal.") };
      if (goal.ctx.length !== 0) return { ok: false, error: diagnostic(tac.line, "LINEAR_CONTEXT", "`rone` requires an empty linear context.") };
      goal.node = { k: "oneRight" };
      continue;
    }
    if (tac.name === "lone") {
      const parsed = parseAtOnly(tacLine, "lone");
      if (!parsed) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", "`lone` usage: lone at h") };
      const idx = goal.ctx.findIndex((x) => x.n === parsed.src);
      if (idx < 0) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${parsed.src}\`.`) };
      const found = goal.ctx[idx];
      if (!found.f || found.f.k !== "one") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`lone` expects a `1` hypothesis.") };
      const sub = makeLinearGoal(goal.ctx.slice(0, idx).concat(goal.ctx.slice(idx + 1)), goalSuccedent(goal));
      goal.node = { k: "oneLeft", goalCtx: contextFormulas(goal.ctx), sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "rtop") {
      const target = goalTarget(goal);
      if (!target || target.k !== "top") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rtop` expects goal `top`.") };
      goal.node = { k: "topRight", goalCtx: contextFormulas(goal.ctx) };
      continue;
    }
    if (tac.name === "lzero") {
      const parsed = parseAtOnly(tacLine, "lzero");
      if (!parsed) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", "`lzero` usage: lzero at h") };
      const idx = goal.ctx.findIndex((x) => x.n === parsed.src);
      if (idx < 0) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${parsed.src}\`.`) };
      const found = goal.ctx[idx];
      if (!found.f || found.f.k !== "zero") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`lzero` expects a `0` hypothesis.") };
      goal.node = { k: "zeroLeft", goalCtx: contextFormulas(goal.ctx) };
      continue;
    }
    if (tac.name === "weakenbang") {
      const parsed = parseAtOnly(tacLine, "weakenbang");
      if (!parsed) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", "`weakenbang` usage: weakenbang at h") };
      const idx = goal.ctx.findIndex((x) => x.n === parsed.src);
      if (idx < 0) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${parsed.src}\`.`) };
      const found = goal.ctx[idx];
      if (!found.f || found.f.k !== "bang") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`weakenbang` expects a bang hypothesis.") };
      const sub = makeLinearGoal(goal.ctx.slice(0, idx).concat(goal.ctx.slice(idx + 1)), goalSuccedent(goal));
      goal.node = { k: "bangWeakeningLeft", formula: found.f.a, goalCtx: contextFormulas(goal.ctx), sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "lbang") {
      const parsed = parseAtOnly(tacLine, "lbang");
      if (!parsed) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", "`lbang` usage: lbang at h") };
      const idx = goal.ctx.findIndex((x) => x.n === parsed.src);
      if (idx < 0) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${parsed.src}\`.`) };
      const found = goal.ctx[idx];
      if (!found.f || found.f.k !== "bang") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`lbang` expects a bang hypothesis.") };
      const ctx = goal.ctx.slice();
      ctx[idx] = { n: parsed.src, f: found.f.a };
      const sub = makeLinearGoal(ctx, goalSuccedent(goal));
      goal.node = {
        k: "bangLeft",
        formula: found.f.a,
        baseFormulas: contextFormulas(goal.ctx.slice(0, idx).concat(goal.ctx.slice(idx + 1))),
        goalCtx: contextFormulas(goal.ctx),
        sub,
      };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "rbang") {
      const target = goalTarget(goal);
      if (!target || target.k !== "bang") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rbang` expects a bang goal.") };
      if (goalRestSuccedent(goal).length !== 0) return { ok: false, error: diagnostic(tac.line, "TACTIC_UNSUPPORTED", "`rbang` is only supported with a single right-hand goal.") };
      if (!ctxAllBang(goal.ctx)) {
        return { ok: false, error: diagnostic(tac.line, "TACTIC_SIDE_CONDITION", "`rbang` requires all linear hypotheses to be bang-formulas.") };
      }
      const sub = makeLinearGoal(goal.ctx.slice(), [target.a]);
      goal.node = { k: "bangRight", formula: target.a, sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "contractbang") {
      const parsed = parseAtAs(tacLine, "contractbang");
      if (!parsed) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", "`contractbang` usage: contractbang at h as h1 h2") };
      const idx = goal.ctx.findIndex((x) => x.n === parsed.src);
      if (idx < 0) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${parsed.src}\`.`) };
      const found = goal.ctx[idx];
      if (!found.f || found.f.k !== "bang") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`contractbang` expects a bang hypothesis.") };
      const base = goal.ctx.slice(0, idx).concat(goal.ctx.slice(idx + 1));
      const sub = makeLinearGoal([{ n: parsed.left, f: found.f }, { n: parsed.right, f: found.f }].concat(base), goalSuccedent(goal));
      goal.node = { k: "bangContractionLeft", formula: found.f.a, baseFormulas: contextFormulas(base), goalCtx: contextFormulas(goal.ctx), sub };
      goals.unshift(sub);
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
  const mode = linearSystemMode(thm.system);
  if (!mode) {
    return { ok: false, error: diagnostic(thm.line, "SYSTEM_UNSUPPORTED", "Only linear `using CLLp` or `using ILLp` is extractable.") };
  }
  let target;
  try {
    target = parseFormula(thm.statement);
  } catch (e) {
    return { ok: false, error: diagnostic(thm.line, "FORMULA_PARSE", String(e.message || e)) };
  }
  const formulaSystemError = validateLinearFormulaForSystem(target, mode);
  if (formulaSystemError) {
    return { ok: false, error: diagnostic(thm.line, "FORMULA_SYSTEM_MISMATCH", formulaSystemError) };
  }
  const root = makeLinearGoal([], [target]);
  const goals = [root];
  for (const tacLine of thm.tactics) {
    if (tacLine.line > cursorLine) break;
    if (tacLine.line === cursorLine && cursorCharacter <= (tacLine.startChar || 0)) break;
    if (goals.length === 0) return { ok: false, error: diagnostic(tacLine.line, "NO_GOALS", "No open goals for tactic.") };
    const goal = goals.shift();
    const tac = parseTactic(tacLine.text, tacLine.line);
    if (tac.err) return { ok: false, error: tac.err };
    if (tac.name === "rlolli") {
      const target = goalTarget(goal);
      if (!target || target.k !== "lolli") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rlolli` expects a lolli goal.") };
      const h = tac.args[0] || `h${goal.ctx.length + 1}`;
      const sub = makeLinearGoal([{ n: h, f: target.l }].concat(goal.ctx), [target.r].concat(goalRestSuccedent(goal)));
      goal.node = { k: "lolliRight", sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "ax") {
      const h = tac.args[0];
      const target = goalTarget(goal);
      if (!h) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", "`ax` requires a hypothesis name.") };
      const found = goal.ctx.find((x) => x.n === h);
      if (!found) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${h}\`.`) };
      if (!formulaEq(found.f, target)) return { ok: false, error: diagnostic(tac.line, "AX_MISMATCH", `Hypothesis \`${h}\` does not match goal.`) };
      if (goal.ctx.length !== 1) {
        return { ok: false, error: diagnostic(tac.line, "LINEAR_CONTEXT", "`ax` requires exactly one linear hypothesis in scope.") };
      }
      if (goalSuccedent(goal).length !== 1) {
        return { ok: false, error: diagnostic(tac.line, "LINEAR_SUCCEDENT", "`ax` requires exactly one formula on the right.") };
      }
      goal.node = { k: "assumption", formula: target };
      continue;
    }
    if (tac.name === "rwith") {
      const target = goalTarget(goal);
      if (!target || target.k !== "with") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rwith` expects `A & B` goal.") };
      const left = makeLinearGoal(goal.ctx.slice(), [target.l].concat(goalRestSuccedent(goal)));
      const right = makeLinearGoal(goal.ctx.slice(), [target.r].concat(goalRestSuccedent(goal)));
      goal.node = { k: "withRight", left, right };
      goals.unshift(right);
      goals.unshift(left);
      continue;
    }
    if (tac.name === "lwithl" || tac.name === "lwithr") {
      const parsed = parseAtOnly(tacLine, tac.name);
      if (!parsed) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", `\`${tac.name}\` usage: ${tac.name} at h`) };
      const idx = goal.ctx.findIndex((x) => x.n === parsed.src);
      if (idx < 0) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${parsed.src}\`.`) };
      const found = goal.ctx[idx];
      if (!found.f || found.f.k !== "with") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", `\`${tac.name}\` expects a with hypothesis.`) };
      const ctx = goal.ctx.slice();
      ctx[idx] = { n: parsed.src, f: tac.name === "lwithl" ? found.f.l : found.f.r };
      const sub = makeLinearGoal(ctx, goalSuccedent(goal));
      goal.node = {
        k: tac.name === "lwithl" ? "withLeftLeft" : "withLeftRight",
        leftFormula: found.f.l,
        rightFormula: found.f.r,
        baseFormulas: contextFormulas(goal.ctx.slice(0, idx).concat(goal.ctx.slice(idx + 1))),
        goalCtx: contextFormulas(goal.ctx),
        sub,
      };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "rplusl") {
      const target = goalTarget(goal);
      if (!target || target.k !== "plus") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rplusl` expects `A ⊕ B` goal.") };
      const sub = makeLinearGoal(goal.ctx.slice(), [target.l].concat(goalRestSuccedent(goal)));
      goal.node = { k: "plusRightLeft", sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "rplusr") {
      const target = goalTarget(goal);
      if (!target || target.k !== "plus") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rplusr` expects `A ⊕ B` goal.") };
      const sub = makeLinearGoal(goal.ctx.slice(), [target.r].concat(goalRestSuccedent(goal)));
      goal.node = { k: "plusRightRight", sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "rpar") {
      if (mode !== "CLLP") return { ok: false, error: diagnostic(tac.line, "TACTIC_FORBIDDEN", "`rpar` is only available for CLLp.") };
      const target = goalTarget(goal);
      if (!target || target.k !== "par") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rpar` expects `A ⅋ B` goal.") };
      const sub = makeLinearGoal(goal.ctx.slice(), [target.l, target.r].concat(goalRestSuccedent(goal)));
      goal.node = { k: "parRight", leftFormula: target.l, rightFormula: target.r, sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "rbot") {
      if (mode !== "CLLP") return { ok: false, error: diagnostic(tac.line, "TACTIC_FORBIDDEN", "`rbot` is only available for CLLp.") };
      const target = goalTarget(goal);
      if (!target || target.k !== "bottom") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rbot` expects a `bot` goal on the right.") };
      const sub = makeLinearGoal(goal.ctx.slice(), goalRestSuccedent(goal));
      goal.node = { k: "bottomRight", sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "rtensor") {
      const target = goalTarget(goal);
      if (!target || target.k !== "tensor") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rtensor` expects `A ⊗ B` goal.") };
      if (goalRestSuccedent(goal).length !== 0) return { ok: false, error: diagnostic(tac.line, "TACTIC_UNSUPPORTED", "`rtensor` is only supported with a single right-hand goal.") };
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
      const left = makeLinearGoal(leftCtx, [target.l]);
      const right = makeLinearGoal(rightCtx, [target.r]);
      goal.node = {
        k: "tensorRight",
        left,
        right,
        goalCtx: goal.ctx.map((x) => x.f),
        leftFormula: target.l,
        rightFormula: target.r,
      };
      goals.unshift(right);
      goals.unshift(left);
      continue;
    }
    if (tac.name === "ltensor") {
      const parsed = parseAtAs(tacLine, "ltensor");
      if (!parsed) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", "`ltensor` usage: ltensor at h as h1 h2") };
      const idx = goal.ctx.findIndex((x) => x.n === parsed.src);
      if (idx < 0) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${parsed.src}\`.`) };
      const found = goal.ctx[idx];
      if (!found.f || found.f.k !== "tensor") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`ltensor` expects a tensor hypothesis.") };
      const base = goal.ctx.slice(0, idx).concat(goal.ctx.slice(idx + 1));
      const sub = makeLinearGoal([{ n: parsed.left, f: found.f.l }, { n: parsed.right, f: found.f.r }].concat(base), goalSuccedent(goal));
      goal.node = {
        k: "tensorLeft",
        srcName: parsed.src,
        leftFormula: found.f.l,
        rightFormula: found.f.r,
        baseFormulas: contextFormulas(base),
        goalCtx: contextFormulas(goal.ctx),
        sub,
      };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "lplus") {
      const parsed = parseAtAs(tacLine, "lplus");
      if (!parsed) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", "`lplus` usage: lplus at h as h1 h2") };
      const idx = goal.ctx.findIndex((x) => x.n === parsed.src);
      if (idx < 0) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${parsed.src}\`.`) };
      const found = goal.ctx[idx];
      if (!found.f || found.f.k !== "plus") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`lplus` expects a plus hypothesis.") };
      const base = goal.ctx.slice(0, idx).concat(goal.ctx.slice(idx + 1));
      const left = makeLinearGoal([{ n: parsed.left, f: found.f.l }].concat(base), goalSuccedent(goal));
      const right = makeLinearGoal([{ n: parsed.right, f: found.f.r }].concat(base), goalSuccedent(goal));
      goal.node = {
        k: "plusLeft",
        srcName: parsed.src,
        leftFormula: found.f.l,
        rightFormula: found.f.r,
        baseFormulas: contextFormulas(base),
        goalCtx: contextFormulas(goal.ctx),
        left,
        right,
      };
      goals.unshift(right);
      goals.unshift(left);
      continue;
    }
    if (tac.name === "rone") {
      const target = goalTarget(goal);
      if (!target || target.k !== "one") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rone` expects goal `1`.") };
      if (goalRestSuccedent(goal).length !== 0) return { ok: false, error: diagnostic(tac.line, "TACTIC_UNSUPPORTED", "`rone` is only supported with a single right-hand goal.") };
      if (goal.ctx.length !== 0) return { ok: false, error: diagnostic(tac.line, "LINEAR_CONTEXT", "`rone` requires an empty linear context.") };
      goal.node = { k: "oneRight" };
      continue;
    }
    if (tac.name === "lone") {
      const parsed = parseAtOnly(tacLine, "lone");
      if (!parsed) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", "`lone` usage: lone at h") };
      const idx = goal.ctx.findIndex((x) => x.n === parsed.src);
      if (idx < 0) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${parsed.src}\`.`) };
      const found = goal.ctx[idx];
      if (!found.f || found.f.k !== "one") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`lone` expects a `1` hypothesis.") };
      const sub = makeLinearGoal(goal.ctx.slice(0, idx).concat(goal.ctx.slice(idx + 1)), goalSuccedent(goal));
      goal.node = { k: "oneLeft", goalCtx: contextFormulas(goal.ctx), sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "rtop") {
      const target = goalTarget(goal);
      if (!target || target.k !== "top") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rtop` expects goal `top`.") };
      goal.node = { k: "topRight", goalCtx: contextFormulas(goal.ctx) };
      continue;
    }
    if (tac.name === "lzero") {
      const parsed = parseAtOnly(tacLine, "lzero");
      if (!parsed) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", "`lzero` usage: lzero at h") };
      const idx = goal.ctx.findIndex((x) => x.n === parsed.src);
      if (idx < 0) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${parsed.src}\`.`) };
      const found = goal.ctx[idx];
      if (!found.f || found.f.k !== "zero") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`lzero` expects a `0` hypothesis.") };
      goal.node = { k: "zeroLeft", goalCtx: contextFormulas(goal.ctx) };
      continue;
    }
    if (tac.name === "weakenbang") {
      const parsed = parseAtOnly(tacLine, "weakenbang");
      if (!parsed) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", "`weakenbang` usage: weakenbang at h") };
      const idx = goal.ctx.findIndex((x) => x.n === parsed.src);
      if (idx < 0) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${parsed.src}\`.`) };
      const found = goal.ctx[idx];
      if (!found.f || found.f.k !== "bang") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`weakenbang` expects a bang hypothesis.") };
      const sub = makeLinearGoal(goal.ctx.slice(0, idx).concat(goal.ctx.slice(idx + 1)), goalSuccedent(goal));
      goal.node = { k: "bangWeakeningLeft", formula: found.f.a, goalCtx: contextFormulas(goal.ctx), sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "lbang") {
      const parsed = parseAtOnly(tacLine, "lbang");
      if (!parsed) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", "`lbang` usage: lbang at h") };
      const idx = goal.ctx.findIndex((x) => x.n === parsed.src);
      if (idx < 0) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${parsed.src}\`.`) };
      const found = goal.ctx[idx];
      if (!found.f || found.f.k !== "bang") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`lbang` expects a bang hypothesis.") };
      const ctx = goal.ctx.slice();
      ctx[idx] = { n: parsed.src, f: found.f.a };
      const sub = makeLinearGoal(ctx, goalSuccedent(goal));
      goal.node = {
        k: "bangLeft",
        formula: found.f.a,
        baseFormulas: contextFormulas(goal.ctx.slice(0, idx).concat(goal.ctx.slice(idx + 1))),
        goalCtx: contextFormulas(goal.ctx),
        sub,
      };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "rbang") {
      const target = goalTarget(goal);
      if (!target || target.k !== "bang") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`rbang` expects a bang goal.") };
      if (goalRestSuccedent(goal).length !== 0) return { ok: false, error: diagnostic(tac.line, "TACTIC_UNSUPPORTED", "`rbang` is only supported with a single right-hand goal.") };
      if (!ctxAllBang(goal.ctx)) {
        return { ok: false, error: diagnostic(tac.line, "TACTIC_SIDE_CONDITION", "`rbang` requires all linear hypotheses to be bang-formulas.") };
      }
      const sub = makeLinearGoal(goal.ctx.slice(), [target.a]);
      goal.node = { k: "bangRight", formula: target.a, sub };
      goals.unshift(sub);
      continue;
    }
    if (tac.name === "contractbang") {
      const parsed = parseAtAs(tacLine, "contractbang");
      if (!parsed) return { ok: false, error: diagnostic(tac.line, "TACTIC_ARGS", "`contractbang` usage: contractbang at h as h1 h2") };
      const idx = goal.ctx.findIndex((x) => x.n === parsed.src);
      if (idx < 0) return { ok: false, error: diagnostic(tac.line, "UNKNOWN_HYP", `Unknown hypothesis \`${parsed.src}\`.`) };
      const found = goal.ctx[idx];
      if (!found.f || found.f.k !== "bang") return { ok: false, error: diagnostic(tac.line, "TACTIC_MISMATCH", "`contractbang` expects a bang hypothesis.") };
      const base = goal.ctx.slice(0, idx).concat(goal.ctx.slice(idx + 1));
      const sub = makeLinearGoal([{ n: parsed.left, f: found.f }, { n: parsed.right, f: found.f }].concat(base), goalSuccedent(goal));
      goal.node = { k: "bangContractionLeft", formula: found.f.a, baseFormulas: contextFormulas(base), goalCtx: contextFormulas(goal.ctx), sub };
      goals.unshift(sub);
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
    target: goalSuccedent(goal).map(formulaDisplay).join(", "),
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

function relationLean(mode) {
  return mode === "ILLP" ? "ILL" : "CLL";
}

function renderNode(node, indent, mode = "CLLP") {
  const pad = " ".repeat(indent);
  const relation = relationLean(mode);
  if (node.k === "assumption") return `${pad}exact ${relation}.assumption`;
  if (node.k === "lolliRight") {
    return `${pad}apply ${relation}.lolliRight\n${renderNode(node.sub.node, indent, mode)}`;
  }
  if (node.k === "withRight") {
    return `${pad}apply ${relation}.withRight\n${pad}·\n${renderNode(node.left.node, indent + 2, mode)}\n${pad}·\n${renderNode(node.right.node, indent + 2, mode)}`;
  }
  if (node.k === "withLeftLeft") {
    const body = `${pad}apply (${relation}.withLeftLeft (leftFormula := ${formulaLean(node.leftFormula, mode)}) (rightFormula := ${formulaLean(node.rightFormula, mode)}))\n${renderNode(node.sub.node, indent, mode)}`;
    const built = [{ k: "with", l: node.leftFormula, r: node.rightFormula }].concat(node.baseFormulas || []);
    return wrapExchangeLeft(body, built, node.goalCtx || built, indent, mode);
  }
  if (node.k === "withLeftRight") {
    const body = `${pad}apply (${relation}.withLeftRight (leftFormula := ${formulaLean(node.leftFormula, mode)}) (rightFormula := ${formulaLean(node.rightFormula, mode)}))\n${renderNode(node.sub.node, indent, mode)}`;
    const built = [{ k: "with", l: node.leftFormula, r: node.rightFormula }].concat(node.baseFormulas || []);
    return wrapExchangeLeft(body, built, node.goalCtx || built, indent, mode);
  }
  if (node.k === "plusRightLeft") {
    return `${pad}apply ${relation}.plusRightLeft\n${renderNode(node.sub.node, indent, mode)}`;
  }
  if (node.k === "plusRightRight") {
    return `${pad}apply ${relation}.plusRightRight\n${renderNode(node.sub.node, indent, mode)}`;
  }
  if (node.k === "parRight") {
    return `${pad}apply ${relation}.parRight\n${renderNode(node.sub.node, indent, mode)}`;
  }
  if (node.k === "bottomRight") {
    return `${pad}apply ${relation}.bottomRight\n${renderNode(node.sub.node, indent, mode)}`;
  }
  if (node.k === "plusLeft") {
    const body = `${pad}apply (${relation}.plusLeft (leftFormula := ${formulaLean(node.leftFormula, mode)}) (rightFormula := ${formulaLean(node.rightFormula, mode)}))\n${pad}·\n${renderNode(node.left.node, indent + 2, mode)}\n${pad}·\n${renderNode(node.right.node, indent + 2, mode)}`;
    const built = [{ k: "plus", l: node.leftFormula, r: node.rightFormula }].concat(node.baseFormulas || []);
    return wrapExchangeLeft(body, built, node.goalCtx || built, indent, mode);
  }
  if (node.k === "oneRight") {
    return `${pad}exact ${relation}.oneRight`;
  }
  if (node.k === "oneLeft") {
    const body = `${pad}apply ${relation}.oneLeft\n${renderNode(node.sub.node, indent, mode)}`;
    const built = [{ k: "one" }].concat(contextFormulas(node.sub.ctx));
    return wrapExchangeLeft(body, built, node.goalCtx || built, indent, mode);
  }
  if (node.k === "topRight") {
    return `${pad}exact ${relation}.topRight`;
  }
  if (node.k === "zeroLeft") {
    return `${pad}exact ${relation}.zeroLeft`;
  }
  if (node.k === "tensorRight") {
    const leftAnt = listLean(contextFormulas(node.left.ctx), mode);
    const rightAnt = listLean(contextFormulas(node.right.ctx), mode);
    const body = mode === "ILLP"
      ? `${pad}apply (${relation}.tensorRight ` +
        `(leftAntecedent := ${leftAnt}) ` +
        `(rightAntecedent := ${rightAnt}) ` +
        `(leftFormula := ${formulaLean(node.leftFormula, mode)}) ` +
        `(rightFormula := ${formulaLean(node.rightFormula, mode)}))\n` +
        `${pad}·\n${renderNode(node.left.node, indent + 2, mode)}\n${pad}·\n${renderNode(node.right.node, indent + 2, mode)}`
      : `${pad}apply (${relation}.tensorRight ` +
        `(leftAntecedent := ${leftAnt}) ` +
        `(leftSuccedent := []) ` +
        `(rightAntecedent := ${rightAnt}) ` +
        `(rightSuccedent := []) ` +
        `(leftFormula := ${formulaLean(node.leftFormula, mode)}) ` +
        `(rightFormula := ${formulaLean(node.rightFormula, mode)}))\n` +
        `${pad}·\n${renderNode(node.left.node, indent + 2, mode)}\n${pad}·\n${renderNode(node.right.node, indent + 2, mode)}`;
    const built = builtAntecedent(node);
    const expected = node.goalCtx || built;
    return wrapExchangeLeft(body, built, expected, indent, mode);
  }
  if (node.k === "tensorLeft") {
    const body = `${pad}apply (${relation}.tensorLeft (leftFormula := ${formulaLean(node.leftFormula, mode)}) (rightFormula := ${formulaLean(node.rightFormula, mode)}))\n${renderNode(node.sub.node, indent, mode)}`;
    const built = [{ k: "tensor", l: node.leftFormula, r: node.rightFormula }].concat(node.baseFormulas || []);
    return wrapExchangeLeft(body, built, node.goalCtx || built, indent, mode);
  }
  if (node.k === "bangLeft") {
    const body = `${pad}apply (${relation}.bangLeft (formula := ${formulaLean(node.formula, mode)}))\n${renderNode(node.sub.node, indent, mode)}`;
    const built = [{ k: "bang", a: node.formula }].concat(node.baseFormulas || []);
    return wrapExchangeLeft(body, built, node.goalCtx || built, indent, mode);
  }
  if (node.k === "bangWeakeningLeft") {
    const constructor = mode === "ILLP" ? "bangWeakening" : "bangWeakeningLeft";
    const body = `${pad}apply (${relation}.${constructor} (formula := ${formulaLean(node.formula, mode)}))\n${renderNode(node.sub.node, indent, mode)}`;
    const built = [{ k: "bang", a: node.formula }].concat(contextFormulas(node.sub.ctx));
    return wrapExchangeLeft(body, built, node.goalCtx || built, indent, mode);
  }
  if (node.k === "bangRight") {
    const subAnt = listLean(contextFormulas(node.sub.ctx), mode);
    if (mode === "ILLP") {
      return `${pad}apply (${relation}.bangRight (antecedent := ${subAnt}) (formula := ${formulaLean(node.formula, mode)}))\n${pad}·\n${pad}  trivial\n${pad}·\n${renderNode(node.sub.node, indent + 2, mode)}`;
    }
    return `${pad}apply (${relation}.bangRight (antecedent := ${subAnt}) (succedent := []) (formula := ${formulaLean(node.formula, mode)}))\n${pad}·\n${pad}  trivial\n${pad}·\n${pad}  trivial\n${pad}·\n${renderNode(node.sub.node, indent + 2, mode)}`;
  }
  if (node.k === "bangContractionLeft") {
    const constructor = mode === "ILLP" ? "bangContraction" : "bangContractionLeft";
    const body = `${pad}apply (${relation}.${constructor} (formula := ${formulaLean(node.formula, mode)}))\n${renderNode(node.sub.node, indent, mode)}`;
    const built = [{ k: "bang", a: node.formula }].concat(node.baseFormulas || []);
    return wrapExchangeLeft(body, built, node.goalCtx || built, indent, mode);
  }
  throw new Error("Unknown node kind.");
}

function builtAntecedent(node) {
  if (node.k === "assumption") return [node.formula];
  if (node.k === "lolliRight") return builtAntecedent(node.sub.node).slice(1);
  if (node.k === "withRight") return builtAntecedent(node.left.node);
  if (node.k === "withLeftLeft" || node.k === "withLeftRight") return node.goalCtx || [{ k: "with", l: node.leftFormula, r: node.rightFormula }].concat(builtAntecedent(node.sub.node).slice(1));
  if (node.k === "plusRightLeft" || node.k === "plusRightRight") return builtAntecedent(node.sub.node);
  if (node.k === "parRight" || node.k === "bottomRight") return builtAntecedent(node.sub.node);
  if (node.k === "plusLeft") return node.goalCtx || builtAntecedent(node.left.node).slice(1).concat([{ k: "plus", l: node.leftFormula, r: node.rightFormula }]);
  if (node.k === "oneRight") return [];
  if (node.k === "oneLeft") return node.goalCtx || [{ k: "one" }].concat(builtAntecedent(node.sub.node));
  if (node.k === "topRight") return node.goalCtx || [];
  if (node.k === "zeroLeft") return node.goalCtx || [{ k: "zero" }];
  if (node.k === "tensorRight") return contextFormulas(node.left.ctx).concat(contextFormulas(node.right.ctx));
  if (node.k === "tensorLeft") return node.goalCtx || [{ k: "tensor", l: node.leftFormula, r: node.rightFormula }].concat(builtAntecedent(node.sub.node).slice(2));
  if (node.k === "bangLeft") return node.goalCtx || [{ k: "bang", a: node.formula }].concat(builtAntecedent(node.sub.node).slice(1));
  if (node.k === "bangWeakeningLeft") return node.goalCtx || [{ k: "bang", a: node.formula }].concat(builtAntecedent(node.sub.node));
  if (node.k === "bangRight") return builtAntecedent(node.sub.node);
  if (node.k === "bangContractionLeft") return node.goalCtx || [{ k: "bang", a: node.formula }].concat(builtAntecedent(node.sub.node).slice(2));
  return [];
}

function contextFormulas(ctx) {
  return (ctx || []).map((x) => x.f);
}

function wrapExchangeLeft(body, built, expected, indent, mode = "CLLP") {
  const pad = " ".repeat(indent);
  const relation = relationLean(mode);
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
        `${pad}apply (${relation}.exchangeLeft ` +
        `(leftContext := ${listLean(step.left, mode)}) ` +
        `(rightContext := ${listLean(step.right, mode)}) ` +
        `(firstFormula := ${formulaLean(step.first, mode)}) ` +
        `(secondFormula := ${formulaLean(step.second, mode)}))`
    )
    .join("\n");
  return `${prefix}\n${body}`;
}

function listLean(xs, mode = "CLLP") {
  if (!xs.length) return "[]";
  return `[${xs.map((formula) => formulaLean(formula, mode)).join(", ")}]`;
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
  const mode = linearSystemMode(thm.system) || "CLLP";
  const conclusion = formulaLean(parseFormula(thm.statement), mode);
  const type = mode === "ILLP" ? `ILL [] ${conclusion}` : `CLL [] [${conclusion}]`;
  return [
    "import FastProofTheory.Proof.LinearLogic",
    "",
    "open FastProofTheory.Proof",
    "",
    `theorem ${nm}_extracted : ${type} := by`,
    renderNode(proofRoot.node, 2, mode),
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
