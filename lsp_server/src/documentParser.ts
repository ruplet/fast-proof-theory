import { parseFormula } from "./formulaParser";
import { DocumentIR, Range, TheoremIR } from "./types";

const tacticNames = new Set(
  [
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
    "translate",
    "translate_to",
  ].map((t) => t.toLowerCase())
);

function mkRange(line: number, start: number, end: number): Range {
  return {
    start: { line, character: start },
    end: { line, character: end },
  };
}

type TheoremProfile = {
  logic: string;
  calculus: string;
};

enum LogicToken {
  LL = "LL",
  IPC = "IPC",
  CPC = "CPC",
  STLC = "STLC",
}

enum CalculusToken {
  ND = "ND",
  GENTZEN = "GENTZEN",
  HILBERT = "HILBERT",
  FREGE = "FREGE",
}

const LOGIC_DEFAULT_CALCULUS: ReadonlyMap<LogicToken, CalculusToken> = new Map([
  [LogicToken.LL, CalculusToken.GENTZEN],
  [LogicToken.IPC, CalculusToken.ND],
  [LogicToken.CPC, CalculusToken.ND],
  [LogicToken.STLC, CalculusToken.ND],
]);

const CALCULUS_DEFAULT_LOGIC: ReadonlyMap<CalculusToken, LogicToken> = new Map([
  [CalculusToken.ND, LogicToken.IPC],
  [CalculusToken.GENTZEN, LogicToken.LL],
  [CalculusToken.HILBERT, LogicToken.CPC],
  [CalculusToken.FREGE, LogicToken.CPC],
]);

const LOGIC_TOKENS: ReadonlyMap<string, LogicToken> = new Map(
  Object.values(LogicToken).map((value) => [value, value])
);

const CALCULUS_TOKENS: ReadonlyMap<string, CalculusToken> = new Map(
  Object.values(CalculusToken).map((value) => [value, value])
);

function parseTheoremProfileSpec(specText: string): TheoremProfile {
  const trimmed = specText.trim();
  if (!trimmed) return { logic: LogicToken.LL, calculus: CalculusToken.GENTZEN };
  const tokens = trimmed.split(/\s+/).filter(Boolean);
  if (!tokens.length) return { logic: LogicToken.LL, calculus: CalculusToken.GENTZEN };

  const first = tokens[0].toUpperCase();

  if (tokens.length === 1) {
    const logic = LOGIC_TOKENS.get(first);
    if (logic) {
      const defaultCalculus = LOGIC_DEFAULT_CALCULUS.get(logic);
      if (!defaultCalculus) throw new Error(`No default calculus for logic "${logic}".`);
      return { logic, calculus: defaultCalculus };
    }

    const calculus = CALCULUS_TOKENS.get(first);
    if (calculus) {
      const defaultLogic = CALCULUS_DEFAULT_LOGIC.get(calculus);
      if (!defaultLogic) throw new Error(`No default logic for calculus "${calculus}".`);
      return { logic: defaultLogic, calculus };
    }

    throw new Error(`Unknown theorem profile token "${tokens[0]}".`);
  }

  if (tokens.length === 2) {
    const logic = LOGIC_TOKENS.get(first);
    const calculus = CALCULUS_TOKENS.get(tokens[1].toUpperCase());
    if (!logic) throw new Error(`Unknown logic token "${tokens[0]}".`);
    if (!calculus) throw new Error(`Unknown calculus token "${tokens[1]}".`);
    return { logic, calculus };
  }

  if (tokens.length === 3) {
    const connector = tokens[1].toLowerCase();
    if (connector !== "in" && connector !== "with" && connector !== "via") {
      throw new Error(`Invalid theorem profile connector "${tokens[1]}". Use in|with|via.`);
    }
    const logic = LOGIC_TOKENS.get(first);
    const calculus = CALCULUS_TOKENS.get(tokens[2].toUpperCase());
    if (!logic) throw new Error(`Unknown logic token "${tokens[0]}".`);
    if (!calculus) throw new Error(`Unknown calculus token "${tokens[2]}".`);
    return { logic, calculus };
  }

  throw new Error(`Invalid theorem profile "${trimmed}".`);
}

export function parseDocumentToIR(uri: string, version: number, text: string): DocumentIR {
  let theoremCounter = 1;
  let current: TheoremIR = {
    name: `theorem${theoremCounter}`,
    logic: LogicToken.LL,
    calculus: CalculusToken.GENTZEN,
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

  const startTheorem = (name: string, profile: TheoremProfile, line: number) => {
    flush();
    theoremCounter += 1;
    current = {
      name: name || `theorem${theoremCounter}`,
      logic: profile.logic,
      calculus: profile.calculus,
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

    const theoremMatch = line.match(/^theorem(?:\s+([A-Za-z_][A-Za-z0-9_]*))?(?:\s+using\s+(.+))?$/i);
    if (theoremMatch) {
      startTheorem(theoremMatch[1] ?? "", parseTheoremProfileSpec(theoremMatch[2] ?? "LL"), idx);
      return;
    }

    if (line === "end") {
      startTheorem("", { logic: LogicToken.LL, calculus: CalculusToken.GENTZEN }, idx);
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
