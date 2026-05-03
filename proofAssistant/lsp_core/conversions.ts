import { KernelCheckResponse, KernelDiagnostic } from "../protocol/types";

type LspDiagnostic = {
  range: {
    start: { line: number; character: number };
    end: { line: number; character: number };
  };
  severity: 1 | 2 | 3 | 4;
  code?: string;
  source?: string;
  message: string;
};

export function toLspSeverity(s: number): 1 | 2 | 3 | 4 {
  switch (s) {
    case 2:
      return 2;
    case 3:
      return 3;
    case 4:
      return 4;
    default:
      return 1;
  }
}

export function asDiagnostics(result: Pick<KernelCheckResponse, "diagnostics">): LspDiagnostic[] {
  return result.diagnostics.map((d) => ({
    range: {
      start: { line: d.range.start.line, character: d.range.start.character },
      end: { line: d.range.end.line, character: d.range.end.character },
    },
    severity: toLspSeverity(d.severity),
    code: d.code,
    source: d.source || "kernel",
    message: d.message,
  }));
}

export function makeErrorDiagnostic(code: string, message: string, source = "lsp"): KernelDiagnostic {
  return {
    range: { start: { line: 0, character: 0 }, end: { line: 0, character: 1 } },
    severity: 1,
    source,
    code,
    message,
  };
}
