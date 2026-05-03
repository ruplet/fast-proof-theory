import { asDiagnostics, makeErrorDiagnostic } from "./conversions";
import { MyPaService } from "./service";
import { DomainInfo, GoalView, GoalsResponse, KernelDiagnostic, ProofDisplay, TheoremStatus } from "../protocol/types";

export type GoalsRequest = {
  reqId?: string;
  uri: string;
  line: number;
  character: number;
};

export type TextDocumentLike = {
  uri: string;
  version: number;
  lineCount: number;
  getText(): string;
};

export type HandlerHost = {
  getDocument(uri: string): TextDocumentLike | undefined;
  publishDiagnostics(uri: string, diagnostics: KernelDiagnostic[]): void;
  log(message: string): void;
  error(message: string): void;
};

export function isGoalsRequest(value: unknown): value is GoalsRequest {
  if (typeof value !== "object" || value === null) return false;
  const rec = value as Record<string, unknown>;
  return (
    typeof rec.uri === "string" &&
    typeof rec.line === "number" &&
    Number.isInteger(rec.line) &&
    typeof rec.character === "number" &&
    Number.isInteger(rec.character) &&
    (rec.reqId === undefined || typeof rec.reqId === "string")
  );
}

export function goalsFromDiagnostics(diags: { source?: string; code?: string; message: string }[]): GoalView[] {
  return diags.slice(0, 20).map((d, i) => ({
    id: `diagnostic:${i + 1}`,
    hypotheses: [],
    target: `[${d.source || "kernel"}${d.code ? `:${d.code}` : ""}] ${d.message}`,
  }));
}

export function emptyDisplay(): ProofDisplay {
  return { title: "Lean Backend", status: "No proof state available.", sections: [] };
}

export function goalsOk(
  reqId: string,
  goals: GoalView[],
  diagnostics: KernelDiagnostic[],
  display: ProofDisplay,
  theoremStatuses: TheoremStatus[]
): GoalsResponse {
  return { kind: "ok", reqId, goals, diagnostics, display, theoremStatuses };
}

export function goalsNoGoals(
  reqId: string,
  reason: string,
  diagnostics: KernelDiagnostic[],
  display: ProofDisplay,
  theoremStatuses: TheoremStatus[]
): GoalsResponse {
  return { kind: "no_goals", reqId, reason, diagnostics, display, theoremStatuses };
}

export function goalsError(
  reqId: string,
  code: string,
  message: string,
  diagnostics: KernelDiagnostic[],
  goals: GoalView[],
  display: ProofDisplay,
  theoremStatuses: TheoremStatus[]
): GoalsResponse {
  return { kind: "error", reqId, code, message, diagnostics, goals, display, theoremStatuses };
}

export async function evaluateGoalsAtLine(
  service: MyPaService,
  doc: TextDocumentLike,
  line: number,
  character: number,
  reqId: string
): Promise<GoalsResponse> {
  const result = service.checkDocument({
    uri: doc.uri,
    version: doc.version,
    text: doc.getText(),
    cursor: { line, character },
  });

  if (result.goals.length > 0) {
    return goalsOk(reqId, result.goals, result.diagnostics, result.display, result.theoremStatuses);
  }
  if (result.diagnostics.length > 0) {
    const primary = result.diagnostics[0];
    return goalsError(
      reqId,
      primary?.code || "KERNEL_DIAGNOSTIC",
      primary?.message || "Kernel diagnostic.",
      result.diagnostics,
      goalsFromDiagnostics(result.diagnostics.slice(0, 3)),
      result.display,
      result.theoremStatuses
    );
  }
  return goalsNoGoals(reqId, `No open goals at line ${line + 1}.`, [], result.display, result.theoremStatuses);
}

export function createMyPaHandlers(service: MyPaService, host: HandlerHost) {
  function checkAndPublish(doc: TextDocumentLike) {
    const result = service.checkDocument({
      uri: doc.uri,
      version: doc.version,
      text: doc.getText(),
    });
    host.publishDiagnostics(doc.uri, result.diagnostics);
  }

  async function handleGoals(req: unknown): Promise<GoalsResponse> {
    if (!isGoalsRequest(req)) {
      const reqId = `g:${Date.now()}:${Math.random().toString(36).slice(2, 8)}`;
      const diag = makeErrorDiagnostic("BAD_REQUEST", "Goals request has invalid shape.");
      host.error(`[mypa-lsp] goals.request invalid payload=${JSON.stringify(req)}`);
      return goalsError(reqId, "BAD_REQUEST", diag.message, [diag], goalsFromDiagnostics([diag]), emptyDisplay(), []);
    }

    const reqId = req.reqId ?? `g:${Date.now()}:${Math.random().toString(36).slice(2, 8)}`;
    host.log(`[mypa-lsp] goals.request reqId=${reqId} uri=${req.uri} line=${req.line + 1} col=${req.character + 1}`);

    const doc = host.getDocument(req.uri);
    if (!doc) {
      const diag = makeErrorDiagnostic("DOC_NOT_FOUND", `Goals request document not found: ${req.uri}`);
      host.error(`[mypa-lsp] goals.error reqId=${reqId} code=DOC_NOT_FOUND`);
      host.publishDiagnostics(req.uri, [diag]);
      return goalsError(reqId, "DOC_NOT_FOUND", diag.message, [diag], goalsFromDiagnostics([diag]), emptyDisplay(), []);
    }

    if (req.line < 0 || req.line >= doc.lineCount) {
      const diag = makeErrorDiagnostic(
        "LINE_OUT_OF_RANGE",
        `Requested line ${req.line + 1} is outside document line range 1..${doc.lineCount}.`
      );
      host.error(`[mypa-lsp] goals.error reqId=${reqId} code=LINE_OUT_OF_RANGE`);
      return goalsError(reqId, "LINE_OUT_OF_RANGE", diag.message, [diag], goalsFromDiagnostics([diag]), emptyDisplay(), []);
    }

    if (req.character < 0) {
      const diag = makeErrorDiagnostic("CHAR_OUT_OF_RANGE", `Requested character ${req.character} must be >= 0.`);
      host.error(`[mypa-lsp] goals.error reqId=${reqId} code=CHAR_OUT_OF_RANGE`);
      return goalsError(reqId, "CHAR_OUT_OF_RANGE", diag.message, [diag], goalsFromDiagnostics([diag]), emptyDisplay(), []);
    }

    checkAndPublish(doc);

    return evaluateGoalsAtLine(service, doc, req.line, req.character, reqId)
      .then((current) => {
        host.log(`[mypa-lsp] goals.result reqId=${reqId} kind=${current.kind}`);
        return current;
      })
      .catch((err) => {
        const diag = makeErrorDiagnostic("GOALS_REQUEST_FAILED", `Goals request failed: ${String(err)}`);
        host.error(`[mypa-lsp] goals.error reqId=${reqId} code=GOALS_REQUEST_FAILED`);
        host.publishDiagnostics(doc.uri, [diag]);
        return goalsError(reqId, "GOALS_REQUEST_FAILED", diag.message, [diag], goalsFromDiagnostics([diag]), emptyDisplay(), []);
      });
  }

  function handleDomainInfo(): DomainInfo {
    return service.getDomainInfo();
  }

  function handleDidClose(uri: string) {
    host.publishDiagnostics(uri, []);
  }

  return {
    checkAndPublish,
    handleGoals,
    handleDomainInfo,
    handleDidClose,
  };
}

export { asDiagnostics };
