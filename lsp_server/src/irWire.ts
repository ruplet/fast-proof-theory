import { DocumentIR, Formula, KernelCheckResponse } from "./types";

function escapeField(value: string): string {
  return encodeURIComponent(value);
}

function unescapeField(value: string): string {
  return decodeURIComponent(value);
}

export function documentToKernelWire(doc: DocumentIR): string {
  let out = "";
  out += `DOC ${escapeField(doc.uri)} ${doc.version}\n`;

  let nextFormulaId = 1;
  const formulaIds = new Map<Formula, number>();

  const emitFormula = (f: Formula): number => {
    const cached = formulaIds.get(f);
    if (cached) return cached;

    const id = nextFormulaId++;
    formulaIds.set(f, id);

    switch (f.node) {
      case "atom":
        out += `FORMULA ${id} atom ${escapeField(f.atom.name)} ${f.atom.negated ? 1 : 0}\n`;
        return id;
      case "one":
      case "top":
      case "bot":
      case "zero":
        out += `FORMULA ${id} ${f.node}\n`;
        return id;
      case "bang": {
        const child = emitFormula(f.bang.of);
        out += `FORMULA ${id} bang ${child}\n`;
        return id;
      }
      case "tensor": {
        const left = emitFormula(f.tensor.left);
        const right = emitFormula(f.tensor.right);
        out += `FORMULA ${id} tensor ${left} ${right}\n`;
        return id;
      }
      case "with": {
        const left = emitFormula(f.with.left);
        const right = emitFormula(f.with.right);
        out += `FORMULA ${id} with ${left} ${right}\n`;
        return id;
      }
      case "plus": {
        const left = emitFormula(f.plus.left);
        const right = emitFormula(f.plus.right);
        out += `FORMULA ${id} plus ${left} ${right}\n`;
        return id;
      }
      case "lolli": {
        const left = emitFormula(f.lolli.left);
        const right = emitFormula(f.lolli.right);
        out += `FORMULA ${id} lolli ${left} ${right}\n`;
        return id;
      }
    }
  };

  for (const thm of doc.theorems) {
    out += `THEOREM ${escapeField(thm.name)}\n`;
    for (const h of thm.hypotheses) {
      const fid = emitFormula(h.formula);
      out += `HYP ${escapeField(h.name)} ${fid} ${h.range.start.line} ${h.range.start.character} ${h.range.end.line} ${h.range.end.character}\n`;
    }
    for (const g of thm.goals) {
      const fid = emitFormula(g.formula);
      out += `GOAL ${fid} ${g.range.start.line} ${g.range.start.character} ${g.range.end.line} ${g.range.end.character}\n`;
    }
    for (const t of thm.tactics) {
      const args = t.args.map(escapeField).join(",");
      if (t.name.toLowerCase() === "assume" && t.assumeName && t.assumeFormula) {
        const fid = emitFormula(t.assumeFormula);
        out += `TACTIC_ASSUME ${escapeField(t.name)} ${escapeField(t.assumeName)} ${fid} ${escapeField(args)} ${t.range.start.line} ${t.range.start.character} ${t.range.end.line} ${t.range.end.character}\n`;
      } else {
        out += `TACTIC ${escapeField(t.name)} ${escapeField(args)} ${t.range.start.line} ${t.range.start.character} ${t.range.end.line} ${t.range.end.character}\n`;
      }
    }
    out += "ENDTHEOREM\n";
  }

  out += "END\n";
  return out;
}

export function parseKernelResponse(raw: string): KernelCheckResponse {
  const goals: KernelCheckResponse["goals"] = [];
  const diagnostics: KernelCheckResponse["diagnostics"] = [];
  const protocolError = (message: string) => {
    diagnostics.push({
      range: {
        start: { line: 0, character: 0 },
        end: { line: 0, character: 1 },
      },
      severity: 1,
      code: "KERNEL_PROTOCOL",
      source: "lsp",
      message,
    });
  };
  const parseIntStrict = (value: string | undefined, field: string): number | null => {
    if (value === undefined) {
      protocolError(`Missing field "${field}" in kernel output`);
      return null;
    }
    const n = Number(value);
    if (!Number.isInteger(n)) {
      protocolError(`Invalid integer for "${field}" in kernel output: "${value}"`);
      return null;
    }
    return n;
  };

  const lines = raw.split(/\r?\n/).map((l) => l.trim()).filter(Boolean);
  for (const line of lines) {
    const parts = line.split(" ");
    if (parts[0] === "DIAG") {
      if (parts.length < 9) {
        protocolError(`Malformed DIAG line: ${line}`);
        continue;
      }
      const sl = parseIntStrict(parts[1], "diag.start.line");
      const sc = parseIntStrict(parts[2], "diag.start.character");
      const el = parseIntStrict(parts[3], "diag.end.line");
      const ec = parseIntStrict(parts[4], "diag.end.character");
      const severity = parseIntStrict(parts[5], "diag.severity");
      if (sl === null || sc === null || el === null || ec === null || severity === null) continue;
      diagnostics.push({
        range: {
          start: { line: sl, character: sc },
          end: { line: el, character: ec },
        },
        severity,
        code: unescapeField(parts[6] ?? ""),
        source: unescapeField(parts[7] ?? "kernel"),
        message: unescapeField(parts.slice(8).join(" ")),
      });
      continue;
    }

    if (parts[0] === "GOAL") {
      if (parts.length < 3) {
        protocolError(`Malformed GOAL line: ${line}`);
        continue;
      }
      goals.push({
        id: unescapeField(parts[1] ?? ""),
        target: unescapeField(parts[2] ?? ""),
        hypotheses: [],
      });
      continue;
    }

    if (parts[0] === "HYP") {
      if (!goals.length) {
        protocolError(`HYP line received before GOAL: ${line}`);
        continue;
      }
      if (parts.length < 3) {
        protocolError(`Malformed HYP line: ${line}`);
        continue;
      }
      const goal = goals[goals.length - 1];
      goal.hypotheses.push({
        name: unescapeField(parts[1] ?? ""),
        type: unescapeField(parts.slice(2).join(" ")),
      });
      continue;
    }

    protocolError(`Unknown kernel output line: ${line}`);
  }

  return {
    diagnostics,
    goals,
    display: {
      title: "Legacy Kernel Wire",
      status: "Deprecated response shape",
      sections: [],
    },
    theoremStatuses: [],
  };
}
