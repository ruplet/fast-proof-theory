"use strict";

const Logic = Object.freeze({ CL: "CL", IL: "IL", CLL: "CLL", ILL: "ILL" });

function Atom(name) { return { k: "Atom", name }; }
function One() { return { k: "One" }; }
function Zero() { return { k: "Zero" }; }
function And(left, right) { return { k: "And", left, right }; }
function Or(left, right) { return { k: "Or", left, right }; }
function Imp(left, right) { return { k: "Imp", left, right }; }
function Not(formula) { return Imp(formula, Zero()); }

function LinAtom(name) { return { k: "Atom", name }; }
function I() { return { k: "I" }; }
function Tensor(left, right) { return { k: "Tensor", left, right }; }
function Bot() { return { k: "Bot" }; }
function Par(left, right) { return { k: "Par", left, right }; }
function Lolli(left, right) { return { k: "Lolli", left, right }; }
function Top() { return { k: "Top" }; }
function With(left, right) { return { k: "With", left, right }; }
function Plus(left, right) { return { k: "Plus", left, right }; }
function Bang(formula) { return { k: "Bang", formula }; }
function Quest(formula) { return { k: "Quest", formula }; }

function sequent(left, right) { return { left: [...left], right: [...right] }; }
function ilSequent(left, right) { return { left: [...left], right }; }
function linearSequent(left, right) { return { left: [...left], right: [...right] }; }
function illSequent(left, right) { return { left: [...left], right }; }
function proof(rule, premises, conclusion) { return { rule, premises: premises || [], conclusion }; }

function stable(value) {
  if (!value || typeof value !== "object") return JSON.stringify(value);
  if (Array.isArray(value)) return `[${value.map(stable).join(",")}]`;
  const keys = Object.keys(value).sort();
  return `{${keys.map((key) => `${JSON.stringify(key)}:${stable(value[key])}`).join(",")}}`;
}

function formulaEq(a, b) { return stable(a) === stable(b); }
function multisetEq(a, b) {
  if (!Array.isArray(a) || !Array.isArray(b) || a.length !== b.length) return false;
  const counts = new Map();
  for (const item of a) {
    const key = stable(item);
    counts.set(key, (counts.get(key) || 0) + 1);
  }
  for (const item of b) {
    const key = stable(item);
    const count = counts.get(key) || 0;
    if (count === 0) return false;
    if (count === 1) counts.delete(key);
    else counts.set(key, count - 1);
  }
  return counts.size === 0;
}
function sameSeq(a, b) { return multisetEq(a.left, b.left) && multisetEq(a.right, b.right); }
function sameISeq(a, b) { return multisetEq(a.left, b.left) && formulaEq(a.right, b.right); }
function add(ctx, ...items) { return ctx.concat(items); }
function removeOne(ctx, item) {
  const out = ctx.slice();
  const idx = out.findIndex((x) => formulaEq(x, item));
  if (idx < 0) return null;
  out.splice(idx, 1);
  return out;
}
function removeMany(ctx, items) {
  let out = ctx.slice();
  for (const item of items) {
    out = removeOne(out, item);
    if (!out) return null;
  }
  return out;
}
function has(ctx, item) { return removeOne(ctx, item) !== null; }
function contextSubset(sub, sup) { return removeMany(sup, sub) !== null; }
function allBang(ctx) { return ctx.every((formula) => formula.k === "Bang"); }
function allQuest(ctx) { return ctx.every((formula) => formula.k === "Quest"); }
function onePremise(premises) { return premises.length === 1 ? premises[0].conclusion : null; }
function twoPremises(premises) { return premises.length === 2 ? premises.map((p) => p.conclusion) : null; }
function threePremises(premises) { return premises.length === 3 ? premises.map((p) => p.conclusion) : null; }
function fail(path, message) { return { ok: false, error: `${path}: ${message}` }; }
function ok() { return { ok: true }; }

function validateShape(logic, seq) {
  if (!seq || !Array.isArray(seq.left)) return false;
  if (logic === Logic.CL) return Array.isArray(seq.right) && seq.left.every(wfPropFormula) && seq.right.every(wfPropFormula);
  if (logic === Logic.CLL) return Array.isArray(seq.right) && seq.left.every(wfCLLFormula) && seq.right.every(wfCLLFormula);
  if (logic === Logic.IL) return seq.right && typeof seq.right === "object" && !Array.isArray(seq.right) && seq.left.every(wfPropFormula) && wfPropFormula(seq.right);
  if (logic === Logic.ILL) return seq.right && typeof seq.right === "object" && !Array.isArray(seq.right) && seq.left.every(wfILLFormula) && wfILLFormula(seq.right);
  return false;
}

function wfPropFormula(formula) {
  if (!formula || typeof formula !== "object") return false;
  switch (formula.k) {
    case "Atom": case "One": case "Zero": return true;
    case "And": case "Or": case "Imp": return wfPropFormula(formula.left) && wfPropFormula(formula.right);
    default: return false;
  }
}
function wfCLLFormula(formula) {
  if (!formula || typeof formula !== "object") return false;
  switch (formula.k) {
    case "Atom": case "I": case "Bot": case "Top": case "Zero": return true;
    case "Tensor": case "Par": case "Lolli": case "With": case "Plus": return wfCLLFormula(formula.left) && wfCLLFormula(formula.right);
    case "Bang": case "Quest": return wfCLLFormula(formula.formula);
    default: return false;
  }
}
function wfILLFormula(formula) {
  if (!formula || typeof formula !== "object") return false;
  switch (formula.k) {
    case "Atom": case "I": case "Top": case "Zero": return true;
    case "Tensor": case "Lolli": case "With": case "Plus": return wfILLFormula(formula.left) && wfILLFormula(formula.right);
    case "Bang": return wfILLFormula(formula.formula);
    default: return false;
  }
}

function checkProof(node, logic, path = "root") {
  if (!node || typeof node !== "object") return fail(path, "proof node must be an object");
  if (!validateShape(logic, node.conclusion)) return fail(path, `invalid ${logic} sequent shape`);
  const premises = node.premises || [];
  for (let i = 0; i < premises.length; i += 1) {
    const checked = checkProof(premises[i], logic, `${path}.premises[${i}]`);
    if (!checked.ok) return checked;
  }
  let checked;
  switch (logic) {
    case Logic.CL: checked = checkCL(node.rule, premises, node.conclusion); break;
    case Logic.IL: checked = checkIL(node.rule, premises, node.conclusion); break;
    case Logic.CLL: checked = checkCLL(node.rule, premises, node.conclusion); break;
    case Logic.ILL: checked = checkILL(node.rule, premises, node.conclusion); break;
    default: return fail(path, `unknown logic ${logic}`);
  }
  return checked.ok ? checked : fail(path, checked.error);
}

function checkCL(rule, premises, c) {
  const p = onePremise(premises);
  const ps2 = twoPremises(premises);
  switch (rule) {
    case "Identity": return premises.length === 0 && c.left.length === 1 && c.right.length === 1 && formulaEq(c.left[0], c.right[0]) ? ok() : { ok: false, error: "Identity requires A |- A" };
    case "IdentityContext": return premises.length === 0 && c.left.some((f) => has(c.right, f)) ? ok() : { ok: false, error: "IdentityContext requires a shared formula occurrence" };
    case "Cut": {
      if (!ps2) return { ok: false, error: "Cut requires two premises" };
      const [l, r] = ps2;
      for (const cut of l.right) {
        const lRight = removeOne(l.right, cut);
        const rLeft = removeOne(r.left, cut);
        if (rLeft && sameSeq(c, sequent(add(l.left, ...rLeft), add(lRight, ...r.right)))) return ok();
      }
      return { ok: false, error: "Cut conclusion does not match any cut formula" };
    }
    case "WeakeningLeft": return p && c.left.length === p.left.length + 1 && contextSubset(p.left, c.left) && multisetEq(c.right, p.right) ? ok() : { ok: false, error: "WeakeningLeft must add exactly one left formula" };
    case "WeakeningRight": return p && c.right.length === p.right.length + 1 && multisetEq(c.left, p.left) && contextSubset(p.right, c.right) ? ok() : { ok: false, error: "WeakeningRight must add exactly one right formula" };
    case "ContractionLeft": return p && multisetEq(c.right, p.right) && contractionOk(p.left, c.left) ? ok() : { ok: false, error: "ContractionLeft must replace A,A by A" };
    case "ContractionRight": return p && multisetEq(c.left, p.left) && contractionOk(p.right, c.right) ? ok() : { ok: false, error: "ContractionRight must replace A,A by A" };
    case "OneRight": return premises.length === 0 && c.left.length === 0 && c.right.length === 1 && c.right[0].k === "One" ? ok() : { ok: false, error: "OneRight requires |- One" };
    case "OneLeft": return p && multisetEq(c.right, p.right) && c.left.length === p.left.length + 1 && has(c.left, One()) && contextSubset(p.left, c.left) ? ok() : { ok: false, error: "OneLeft must add One on the left" };
    case "ZeroLeft": return premises.length === 0 && c.left.length === 1 && c.left[0].k === "Zero" && c.right.length === 0 ? ok() : { ok: false, error: "ZeroLeft requires Zero |-" };
    case "ZeroRight": return p && multisetEq(c.left, p.left) && c.right.length === p.right.length + 1 && has(c.right, Zero()) && contextSubset(p.right, c.right) ? ok() : { ok: false, error: "ZeroRight must add Zero on the right" };
    case "AndLeft1": return p && unaryLeftConnective(p, c, "And", "left") ? ok() : { ok: false, error: "AndLeft1 mismatch" };
    case "AndLeft2": return p && unaryLeftConnective(p, c, "And", "right") ? ok() : { ok: false, error: "AndLeft2 mismatch" };
    case "AndRight": return binaryRightSplit(ps2, c, "And") ? ok() : { ok: false, error: "AndRight mismatch" };
    case "OrLeft": return binaryLeftSplit(ps2, c, "Or") ? ok() : { ok: false, error: "OrLeft mismatch" };
    case "OrRight1": return p && unaryRightConnective(p, c, "Or", "left") ? ok() : { ok: false, error: "OrRight1 mismatch" };
    case "OrRight2": return p && unaryRightConnective(p, c, "Or", "right") ? ok() : { ok: false, error: "OrRight2 mismatch" };
    case "ImpLeft": return binaryLeftImp(ps2, c) ? ok() : { ok: false, error: "ImpLeft mismatch" };
    case "ImpRight": return p && unaryImpRight(p, c) ? ok() : { ok: false, error: "ImpRight mismatch" };
    default: return { ok: false, error: `unknown CL rule ${rule}` };
  }
}

function contractionOk(before, after) {
  if (before.length !== after.length + 1) return false;
  for (const f of before) {
    const reduced = removeMany(before, [f, f]);
    if (reduced && multisetEq(add(reduced, f), after)) return true;
  }
  return false;
}
function unaryLeftConnective(p, c, kind, side) {
  if (!multisetEq(p.right, c.right) || c.left.length !== p.left.length) return false;
  for (const conn of c.left.filter((f) => f.k === kind)) {
    const base = removeOne(c.left, conn);
    const expanded = add(base, conn[side]);
    if (multisetEq(expanded, p.left)) return true;
  }
  return false;
}
function unaryRightConnective(p, c, kind, side) {
  if (!multisetEq(p.left, c.left) || c.right.length !== p.right.length) return false;
  for (const conn of c.right.filter((f) => f.k === kind)) {
    const base = removeOne(c.right, conn);
    const expanded = add(base, conn[side]);
    if (multisetEq(expanded, p.right)) return true;
  }
  return false;
}
function binaryRightSplit(ps, c, kind) {
  if (!ps) return false;
  const [p1, p2] = ps;
  for (const conn of c.right.filter((f) => f.k === kind)) {
    const r = removeOne(c.right, conn);
    const r1 = removeOne(p1.right, conn.left);
    const r2 = removeOne(p2.right, conn.right);
    if (r1 && r2 && multisetEq(c.left, add(p1.left, ...p2.left)) && multisetEq(r, add(r1, ...r2))) return true;
  }
  return false;
}
function binaryLeftSplit(ps, c, kind) {
  if (!ps) return false;
  const [p1, p2] = ps;
  for (const conn of c.left.filter((f) => f.k === kind)) {
    const l = removeOne(c.left, conn);
    const l1 = removeOne(p1.left, conn.left);
    const l2 = removeOne(p2.left, conn.right);
    if (l1 && l2 && multisetEq(l, add(l1, ...l2)) && multisetEq(c.right, add(p1.right, ...p2.right))) return true;
  }
  return false;
}
function binaryLeftImp(ps, c) {
  if (!ps) return false;
  const [p1, p2] = ps;
  for (const imp of c.left.filter((f) => f.k === "Imp" || f.k === "Lolli")) {
    const l = removeOne(c.left, imp);
    const r1 = removeOne(p1.right, imp.left);
    const l2 = removeOne(p2.left, imp.right);
    if (r1 && l2 && multisetEq(l, add(p1.left, ...l2)) && multisetEq(c.right, add(r1, ...p2.right))) return true;
  }
  return false;
}
function unaryImpRight(p, c) {
  for (const imp of c.right.filter((f) => f.k === "Imp" || f.k === "Lolli")) {
    const r = removeOne(c.right, imp);
    const lPrem = removeOne(p.left, imp.left);
    const rPrem = removeOne(p.right, imp.right);
    if (lPrem && rPrem && multisetEq(lPrem, c.left) && multisetEq(rPrem, r)) return true;
  }
  return false;
}

function checkIL(rule, premises, c) {
  const p = onePremise(premises);
  const ps2 = twoPremises(premises);
  const ps3 = threePremises(premises);
  switch (rule) {
    case "Assumption": case "Identity": return premises.length === 0 && has(c.left, c.right) ? ok() : { ok: false, error: "Assumption requires A in context" };
    case "OneIntroduction": return premises.length === 0 && c.right.k === "One" ? ok() : { ok: false, error: "OneIntroduction concludes One" };
    case "AndIntroduction": return ps2 && sameISeq(ps2[0], ilSequent(c.left, c.right.left)) && sameISeq(ps2[1], ilSequent(c.left, c.right.right)) && c.right.k === "And" ? ok() : { ok: false, error: "AndIntroduction mismatch" };
    case "AndElimination1": return p && p.right.k === "And" && sameISeq(c, ilSequent(p.left, p.right.left)) ? ok() : { ok: false, error: "AndElimination1 mismatch" };
    case "AndElimination2": return p && p.right.k === "And" && sameISeq(c, ilSequent(p.left, p.right.right)) ? ok() : { ok: false, error: "AndElimination2 mismatch" };
    case "ImpIntroduction": return p && c.right.k === "Imp" && sameISeq(p, ilSequent(add(c.left, c.right.left), c.right.right)) ? ok() : { ok: false, error: "ImpIntroduction mismatch" };
    case "ImpElimination": case "ModusPonens": return ps2 && ps2[0].right.k === "Imp" && formulaEq(ps2[0].right.right, c.right) && sameISeq(ps2[1], ilSequent(c.left, ps2[0].right.left)) && multisetEq(ps2[0].left, c.left) ? ok() : { ok: false, error: "ImpElimination mismatch" };
    case "ZeroElimination": case "ExFalso": return p && p.right.k === "Zero" && multisetEq(p.left, c.left) ? ok() : { ok: false, error: "ZeroElimination mismatch" };
    case "OrIntroduction1": return p && c.right.k === "Or" && sameISeq(p, ilSequent(c.left, c.right.left)) ? ok() : { ok: false, error: "OrIntroduction1 mismatch" };
    case "OrIntroduction2": return p && c.right.k === "Or" && sameISeq(p, ilSequent(c.left, c.right.right)) ? ok() : { ok: false, error: "OrIntroduction2 mismatch" };
    case "OrElimination": return ps3 && ps3[0].right.k === "Or" && formulaEq(ps3[1].right, c.right) && formulaEq(ps3[2].right, c.right) && multisetEq(ps3[0].left, c.left) && multisetEq(ps3[1].left, add(c.left, ps3[0].right.left)) && multisetEq(ps3[2].left, add(c.left, ps3[0].right.right)) ? ok() : { ok: false, error: "OrElimination mismatch" };
    default: return { ok: false, error: `unknown IL rule ${rule}` };
  }
}

function checkCLL(rule, premises, c) {
  const p = onePremise(premises);
  const ps2 = twoPremises(premises);
  switch (rule) {
    case "Identity": return premises.length === 0 && c.left.length === 1 && c.right.length === 1 && formulaEq(c.left[0], c.right[0]) ? ok() : { ok: false, error: "Identity requires A - A" };
    case "Cut": return checkCL("Cut", premises, c);
    case "IRight": return premises.length === 0 && c.left.length === 0 && c.right.length === 1 && c.right[0].k === "I" ? ok() : { ok: false, error: "IRight requires - I" };
    case "ILeft": return p && c.left.length === p.left.length + 1 && has(c.left, I()) && contextSubset(p.left, c.left) && multisetEq(c.right, p.right) ? ok() : { ok: false, error: "ILeft mismatch" };
    case "BotLeft": return premises.length === 0 && c.left.length === 1 && c.left[0].k === "Bot" && c.right.length === 0 ? ok() : { ok: false, error: "BotLeft requires Bot -" };
    case "BotRight": return p && multisetEq(c.left, p.left) && c.right.length === p.right.length + 1 && has(c.right, Bot()) && contextSubset(p.right, c.right) ? ok() : { ok: false, error: "BotRight mismatch" };
    case "TensorLeft": return p && multisetEq(p.right, c.right) && replaceAlso(p.left, c.left, "Tensor", "right") ? ok() : { ok: false, error: "TensorLeft mismatch" };
    case "TensorRight": return binaryRightSplit(ps2, c, "Tensor") ? ok() : { ok: false, error: "TensorRight mismatch" };
    case "ParLeft": return binaryLeftSplit(ps2, c, "Par") ? ok() : { ok: false, error: "ParLeft mismatch" };
    case "ParRight": return p && binaryRightUnaryBoth(p, c, "Par") ? ok() : { ok: false, error: "ParRight mismatch" };
    case "LolliLeft": return binaryLeftImp(ps2, c) ? ok() : { ok: false, error: "LolliLeft mismatch" };
    case "LolliRight": return p && unaryImpRight(p, c) ? ok() : { ok: false, error: "LolliRight mismatch" };
    case "TopRight": return premises.length === 0 && hasKind(c.right, "Top") ? ok() : { ok: false, error: "TopRight has no premises and must conclude Top on right" };
    case "ZeroLeft": return premises.length === 0 && hasKind(c.left, "Zero") ? ok() : { ok: false, error: "ZeroLeft has no premises and must conclude Zero on left" };
    case "WithLeft1": return p && unaryLeftConnective(p, c, "With", "left") ? ok() : { ok: false, error: "WithLeft1 mismatch" };
    case "WithLeft2": return p && unaryLeftConnective(p, c, "With", "right") ? ok() : { ok: false, error: "WithLeft2 mismatch" };
    case "WithRight": return ps2 && additiveRightSame(ps2, c, "With") ? ok() : { ok: false, error: "WithRight mismatch" };
    case "PlusLeft": return ps2 && additiveLeftSame(ps2, c, "Plus") ? ok() : { ok: false, error: "PlusLeft mismatch" };
    case "PlusRight1": return p && unaryRightConnective(p, c, "Plus", "left") ? ok() : { ok: false, error: "PlusRight1 mismatch" };
    case "PlusRight2": return p && unaryRightConnective(p, c, "Plus", "right") ? ok() : { ok: false, error: "PlusRight2 mismatch" };
    case "BangWeakeningLeft": return p && c.left.length === p.left.length + 1 && c.left.some((f) => f.k === "Bang" && multisetEq(removeOne(c.left, f), p.left)) && multisetEq(c.right, p.right) ? ok() : { ok: false, error: "BangWeakeningLeft mismatch" };
    case "BangContractionLeft": return p && bangContraction(p.left, c.left) && multisetEq(p.right, c.right) ? ok() : { ok: false, error: "BangContractionLeft mismatch" };
    case "BangDerelictionLeft": return p && derelictLeft(p, c, "Bang") ? ok() : { ok: false, error: "BangDerelictionLeft mismatch" };
    case "BangPromotionRight": return p && promoteRight(p, c) ? ok() : { ok: false, error: "BangPromotionRight mismatch or side condition failed" };
    case "QuestWeakeningRight": return p && c.right.length === p.right.length + 1 && c.right.some((f) => f.k === "Quest" && multisetEq(removeOne(c.right, f), p.right)) && multisetEq(c.left, p.left) ? ok() : { ok: false, error: "QuestWeakeningRight mismatch" };
    case "QuestContractionRight": return p && questContraction(p.right, c.right) && multisetEq(p.left, c.left) ? ok() : { ok: false, error: "QuestContractionRight mismatch" };
    case "QuestDerelictionRight": return p && derelictRight(p, c, "Quest") ? ok() : { ok: false, error: "QuestDerelictionRight mismatch" };
    case "QuestPromotionLeft": return p && promoteLeft(p, c) ? ok() : { ok: false, error: "QuestPromotionLeft mismatch or side condition failed" };
    default: return { ok: false, error: `unknown CLL rule ${rule}` };
  }
}

function hasKind(ctx, kind) { return ctx.some((f) => f.k === kind); }
function replaceAlso(pLeft, cLeft, kind, side2) {
  for (const conn of cLeft.filter((f) => f.k === kind)) {
    const base = removeOne(cLeft, conn);
    if (multisetEq(add(base, conn.left, conn[side2]), pLeft)) return true;
  }
  return false;
}
function binaryRightUnaryBoth(p, c, kind) {
  if (!multisetEq(p.left, c.left) || c.right.length !== p.right.length - 1) return false;
  for (const conn of c.right.filter((f) => f.k === kind)) {
    const base = removeOne(c.right, conn);
    if (multisetEq(p.right, add(base, conn.left, conn.right))) return true;
  }
  return false;
}
function additiveRightSame(ps, c, kind) {
  const [p1, p2] = ps;
  for (const conn of c.right.filter((f) => f.k === kind)) {
    const base = removeOne(c.right, conn);
    if (sameSeq(p1, sequent(c.left, add(base, conn.left))) && sameSeq(p2, sequent(c.left, add(base, conn.right)))) return true;
  }
  return false;
}
function additiveLeftSame(ps, c, kind) {
  const [p1, p2] = ps;
  for (const conn of c.left.filter((f) => f.k === kind)) {
    const base = removeOne(c.left, conn);
    if (sameSeq(p1, sequent(add(base, conn.left), c.right)) && sameSeq(p2, sequent(add(base, conn.right), c.right))) return true;
  }
  return false;
}
function bangContraction(before, after) {
  if (before.length !== after.length + 1) return false;
  return before.some((f) => {
    if (f.k !== "Bang") return false;
    const reducedBefore = removeMany(before, [f, f]);
    const reducedAfter = removeOne(after, f);
    return reducedBefore !== null && reducedAfter !== null && multisetEq(reducedBefore, reducedAfter);
  });
}
function questContraction(before, after) {
  if (before.length !== after.length + 1) return false;
  return before.some((f) => {
    if (f.k !== "Quest") return false;
    const reducedBefore = removeMany(before, [f, f]);
    const reducedAfter = removeOne(after, f);
    return reducedBefore !== null && reducedAfter !== null && multisetEq(reducedBefore, reducedAfter);
  });
}
function derelictLeft(p, c, wrapper) {
  if (!multisetEq(p.right, c.right) || p.left.length !== c.left.length) return false;
  for (const f of c.left.filter((x) => x.k === wrapper)) {
    if (multisetEq(add(removeOne(c.left, f), f.formula), p.left)) return true;
  }
  return false;
}
function derelictRight(p, c, wrapper) {
  if (!multisetEq(p.left, c.left) || p.right.length !== c.right.length) return false;
  for (const f of c.right.filter((x) => x.k === wrapper)) {
    if (multisetEq(add(removeOne(c.right, f), f.formula), p.right)) return true;
  }
  return false;
}
function promoteRight(p, c) {
  if (!allBang(p.left) || !allQuest(removeOne(p.right, findNonQuestTarget(p.right)) || [])) return false;
  if (!multisetEq(p.left, c.left) || !allBang(c.left)) return false;
  for (const target of p.right.filter((f) => f.k !== "Quest")) {
    const rest = removeOne(p.right, target);
    if (allQuest(rest) && sameSeq(c, sequent(p.left, add(rest, Bang(target))))) return true;
  }
  return false;
}
function findNonQuestTarget(right) { return right.find((f) => f.k !== "Quest"); }
function promoteLeft(p, c) {
  if (!allQuest(p.right) || !allQuest(c.right)) return false;
  for (const q of c.left.filter((f) => f.k === "Quest")) {
    const base = removeOne(c.left, q);
    if (allBang(base) && sameSeq(p, sequent(add(base, q.formula), c.right))) return true;
  }
  return false;
}

function checkILL(rule, premises, c) {
  const p = onePremise(premises);
  const ps2 = twoPremises(premises);
  switch (rule) {
    case "Identity": return premises.length === 0 && c.left.length === 1 && formulaEq(c.left[0], c.right) ? ok() : { ok: false, error: "Identity requires A - A" };
    case "Cut": {
      if (!ps2) return { ok: false, error: "Cut requires two premises" };
      const [l, r] = ps2;
      const rLeft = removeOne(r.left, l.right);
      return rLeft && formulaEq(r.right, c.right) && multisetEq(c.left, add(l.left, ...rLeft)) ? ok() : { ok: false, error: "Cut mismatch" };
    }
    case "IRight": return premises.length === 0 && c.left.length === 0 && c.right.k === "I" ? ok() : { ok: false, error: "IRight requires - I" };
    case "ILeft": return p && c.left.length === p.left.length + 1 && has(c.left, I()) && contextSubset(p.left, c.left) && formulaEq(c.right, p.right) ? ok() : { ok: false, error: "ILeft mismatch" };
    case "TensorLeft": return p && illUnaryLeftBoth(p, c, "Tensor") ? ok() : { ok: false, error: "TensorLeft mismatch" };
    case "TensorRight": return ps2 && c.right.k === "Tensor" && formulaEq(ps2[0].right, c.right.left) && formulaEq(ps2[1].right, c.right.right) && multisetEq(c.left, add(ps2[0].left, ...ps2[1].left)) ? ok() : { ok: false, error: "TensorRight mismatch" };
    case "LolliLeft": return ps2 && illLolliLeft(ps2, c) ? ok() : { ok: false, error: "LolliLeft mismatch" };
    case "LolliRight": return p && c.right.k === "Lolli" && sameISeq(p, illSequent(add(c.left, c.right.left), c.right.right)) ? ok() : { ok: false, error: "LolliRight mismatch" };
    case "TopRight": return premises.length === 0 && c.right.k === "Top" ? ok() : { ok: false, error: "TopRight concludes Top" };
    case "ZeroLeft": return premises.length === 0 && hasKind(c.left, "Zero") ? ok() : { ok: false, error: "ZeroLeft requires Zero on the left" };
    case "WithLeft1": return p && illUnaryLeft(p, c, "With", "left") ? ok() : { ok: false, error: "WithLeft1 mismatch" };
    case "WithLeft2": return p && illUnaryLeft(p, c, "With", "right") ? ok() : { ok: false, error: "WithLeft2 mismatch" };
    case "WithRight": return ps2 && c.right.k === "With" && sameISeq(ps2[0], illSequent(c.left, c.right.left)) && sameISeq(ps2[1], illSequent(c.left, c.right.right)) ? ok() : { ok: false, error: "WithRight mismatch" };
    case "PlusLeft": return ps2 && illAdditiveLeft(ps2, c, "Plus") ? ok() : { ok: false, error: "PlusLeft mismatch" };
    case "PlusRight1": return p && c.right.k === "Plus" && sameISeq(p, illSequent(c.left, c.right.left)) ? ok() : { ok: false, error: "PlusRight1 mismatch" };
    case "PlusRight2": return p && c.right.k === "Plus" && sameISeq(p, illSequent(c.left, c.right.right)) ? ok() : { ok: false, error: "PlusRight2 mismatch" };
    case "BangWeakening": return p && c.left.length === p.left.length + 1 && c.left.some((f) => f.k === "Bang" && multisetEq(removeOne(c.left, f), p.left)) && formulaEq(c.right, p.right) ? ok() : { ok: false, error: "BangWeakening mismatch" };
    case "BangContraction": return p && bangContraction(p.left, c.left) && formulaEq(p.right, c.right) ? ok() : { ok: false, error: "BangContraction mismatch" };
    case "BangDereliction": return p && derelictLeft({ left: p.left, right: [p.right] }, { left: c.left, right: [c.right] }, "Bang") ? ok() : { ok: false, error: "BangDereliction mismatch" };
    case "BangPromotion": return p && c.right.k === "Bang" && formulaEq(p.right, c.right.formula) && multisetEq(p.left, c.left) && allBang(c.left) ? ok() : { ok: false, error: "BangPromotion mismatch or side condition failed" };
    default: return { ok: false, error: `unknown ILL rule ${rule}` };
  }
}
function illUnaryLeft(p, c, kind, side) {
  if (!formulaEq(p.right, c.right) || p.left.length !== c.left.length) return false;
  for (const conn of c.left.filter((f) => f.k === kind)) {
    if (multisetEq(add(removeOne(c.left, conn), conn[side]), p.left)) return true;
  }
  return false;
}
function illUnaryLeftBoth(p, c, kind) {
  if (!formulaEq(p.right, c.right) || p.left.length !== c.left.length + 1) return false;
  for (const conn of c.left.filter((f) => f.k === kind)) {
    if (multisetEq(add(removeOne(c.left, conn), conn.left, conn.right), p.left)) return true;
  }
  return false;
}
function illLolliLeft(ps, c) {
  const [p1, p2] = ps;
  for (const lolli of c.left.filter((f) => f.k === "Lolli")) {
    const base = removeOne(c.left, lolli);
    const p2Base = removeOne(p2.left, lolli.right);
    if (p2Base && formulaEq(p1.right, lolli.left) && formulaEq(p2.right, c.right) && multisetEq(base, add(p1.left, ...p2Base))) return true;
  }
  return false;
}
function illAdditiveLeft(ps, c, kind) {
  const [p1, p2] = ps;
  for (const conn of c.left.filter((f) => f.k === kind)) {
    const base = removeOne(c.left, conn);
    if (sameISeq(p1, illSequent(add(base, conn.left), c.right)) && sameISeq(p2, illSequent(add(base, conn.right), c.right))) return true;
  }
  return false;
}

function formulaToString(f) {
  switch (f.k) {
    case "Atom": return f.name;
    case "One": return "One";
    case "Zero": return "Zero";
    case "And": return `(${formulaToString(f.left)} & ${formulaToString(f.right)})`;
    case "Or": return `(${formulaToString(f.left)} | ${formulaToString(f.right)})`;
    case "Imp": return `(${formulaToString(f.left)} -> ${formulaToString(f.right)})`;
    case "I": return "I";
    case "Tensor": return `(${formulaToString(f.left)} * ${formulaToString(f.right)})`;
    case "Bot": return "Bot";
    case "Par": return `(${formulaToString(f.left)} par ${formulaToString(f.right)})`;
    case "Lolli": return `(${formulaToString(f.left)} -o ${formulaToString(f.right)})`;
    case "Top": return "Top";
    case "With": return `(${formulaToString(f.left)} & ${formulaToString(f.right)})`;
    case "Plus": return `(${formulaToString(f.left)} + ${formulaToString(f.right)})`;
    case "Bang": return `!${formulaToString(f.formula)}`;
    case "Quest": return `?${formulaToString(f.formula)}`;
    default: return stable(f);
  }
}
function contextToString(ctx) { return ctx.map(formulaToString).join(", "); }
function sequentToString(seq, logic) {
  const turnstile = logic === Logic.CL || logic === Logic.IL ? "|-" : "-";
  const right = Array.isArray(seq.right) ? contextToString(seq.right) : formulaToString(seq.right);
  return `${contextToString(seq.left)} ${turnstile} ${right}`.trim();
}

module.exports = {
  Logic,
  Atom, One, Zero, And, Or, Imp, Not,
  LinAtom, I, Tensor, Bot, Par, Lolli, Top, With, Plus, Bang, Quest,
  sequent, ilSequent, linearSequent, illSequent, proof,
  checkProof, formulaEq, multisetEq, allBang, allQuest, formulaToString, sequentToString,
};
