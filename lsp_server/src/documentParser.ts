import { parseFormula } from "./formulaParser";
import { DocumentIR, Range, TheoremIR } from "./types";

const tacticNames = new Set(
  [
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
  ].map((t) => t.toLowerCase())
);

function mkRange(line: number, start: number, end: number): Range {
  return {
    start: { line, character: start },
    end: { line, character: end },
  };
}

export function parseDocumentToIR(uri: string, version: number, text: string): DocumentIR {
  let theoremCounter = 1;
  let current: TheoremIR = {
    name: `theorem${theoremCounter}`,
    range: mkRange(0, 0, 0),
    hypotheses: [],
    goals: [],
    tactics: [],
  };
  const theorems: TheoremIR[] = [];

  const flush = () => {
    if (current.hypotheses.length || current.goals.length || current.tactics.length) {
      theorems.push(current);
    }
  };

  const startTheorem = (name: string, line: number) => {
    flush();
    theoremCounter += 1;
    current = {
      name: name || `theorem${theoremCounter}`,
      range: mkRange(line, 0, line),
      hypotheses: [],
      goals: [],
      tactics: [],
    };
  };

  const lines = text.split(/\r?\n/);
  lines.forEach((raw, idx) => {
    const line = raw.trim();
    if (!line || line.startsWith("--")) {
      return;
    }

    const theoremMatch = line.match(/^theorem(?:\s+([A-Za-z_][A-Za-z0-9_]*))?$/i);
    if (theoremMatch) {
      startTheorem(theoremMatch[1] ?? "", idx);
      return;
    }

    if (line === "end") {
      startTheorem("", idx);
      return;
    }

    const hypMatch = line.match(/^hyp\s+([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.+)$/);
    if (hypMatch) {
      current.hypotheses.push({
        name: hypMatch[1],
        formula: parseFormula(hypMatch[2]),
        range: mkRange(idx, 0, raw.length),
      });
      return;
    }

    const goalMatch = line.match(/^goal\s+(.+)$/);
    if (goalMatch) {
      current.goals.push({
        formula: parseFormula(goalMatch[1]),
        range: mkRange(idx, 0, raw.length),
      });
      return;
    }

    const tacticMatch = line.match(/^tactic\s+([^\s]+)(?:\s+(.*))?$/);
    if (tacticMatch) {
      const tacticName = tacticMatch[1];
      const argsText = tacticMatch[2] ?? "";
      if (tacticName.toLowerCase() === "assume") {
        const assumeMatch = argsText.match(/^([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.+)$/);
        if (!assumeMatch) {
          throw new Error(`Line ${idx + 1}: assume usage: assume <name> : <formula> [hyp...]`);
        }
        const tokens = assumeMatch[2].trim().split(/\s+/).filter(Boolean);
        let assumeFormulaText = "";
        let used = 0;
        for (let i = tokens.length; i >= 1; i--) {
          const candidate = tokens.slice(0, i).join(" ");
          try {
            parseFormula(candidate);
            assumeFormulaText = candidate;
            used = i;
            break;
          } catch {
            // try shorter prefix
          }
        }
        if (!assumeFormulaText) {
          throw new Error("assume requires a parseable formula");
        }
        current.tactics.push({
          name: tacticName,
          args: tokens.slice(used),
          range: mkRange(idx, 0, raw.length),
          assumeName: assumeMatch[1],
          assumeFormula: parseFormula(assumeFormulaText),
        });
        return;
      }
      current.tactics.push({
        name: tacticName,
        args: argsText
          .split(/\s+/)
          .map((a) => a.trim())
          .filter(Boolean),
        range: mkRange(idx, 0, raw.length),
      });
      return;
    }

    const firstWord = line.split(/\s+/, 1)[0] ?? "";
    if (tacticNames.has(firstWord.toLowerCase())) {
      const rest = line.slice(firstWord.length).trim();
      if (firstWord.toLowerCase() === "assume") {
        const assumeMatch = rest.match(/^([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.+)$/);
        if (!assumeMatch) {
          throw new Error("assume usage: assume <name> : <formula> [hyp...]");
        }
        const tokens = assumeMatch[2].trim().split(/\s+/).filter(Boolean);
        let assumeFormulaText = "";
        let used = 0;
        for (let i = tokens.length; i >= 1; i--) {
          const candidate = tokens.slice(0, i).join(" ");
          try {
            parseFormula(candidate);
            assumeFormulaText = candidate;
            used = i;
            break;
          } catch {
            // try shorter prefix
          }
        }
        if (!assumeFormulaText) {
          throw new Error("assume requires a parseable formula");
        }
        current.tactics.push({
          name: firstWord,
          args: tokens.slice(used),
          range: mkRange(idx, 0, raw.length),
          assumeName: assumeMatch[1],
          assumeFormula: parseFormula(assumeFormulaText),
        });
        return;
      }
      current.tactics.push({
        name: firstWord,
        args: rest
          .split(/\s+/)
          .map((a) => a.trim())
          .filter(Boolean),
        range: mkRange(idx, 0, raw.length),
      });
      return;
    }

    throw new Error(`Line ${idx + 1}: Unrecognized line: "${line}"`);
  });

  flush();
  return { uri, version, theorems };
}
