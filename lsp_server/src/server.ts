import {
  createConnection,
  TextDocuments,
  ProposedFeatures,
  InitializeParams,
  TextDocumentSyncKind,
  Diagnostic,
  DiagnosticSeverity,
} from "vscode-languageserver/node";
import { TextDocument } from "vscode-languageserver-textdocument";
import { KernelClient } from "./kernelClient";
import { DomainInfo, GoalView, GoalsResponse, KernelDiagnostic, ProofDisplay, TheoremStatus } from "./types";
import { findProjectRoot } from "./projectRoot";

type GoalsRequest = {
  reqId?: string;
  uri: string;
  line: number;
  character: number;
};

function isGoalsRequest(value: unknown): value is GoalsRequest {
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

function goalsFromDiagnostics(diags: {
  source?: string;
  code?: string;
  message: string;
}[]): GoalView[] {
  return diags.slice(0, 20).map((d, i) => ({
    id: `diagnostic:${i + 1}`,
    hypotheses: [],
    target: `[${d.source || "kernel"}${d.code ? `:${d.code}` : ""}] ${d.message}`,
  }));
}

function makeErrorDiagnostic(code: string, message: string, source = "lsp"): KernelDiagnostic {
  return {
    range: { start: { line: 0, character: 0 }, end: { line: 0, character: 1 } },
    severity: 1,
    source,
    code,
    message,
  };
}

function emptyDisplay(): ProofDisplay {
  return { title: "Lean Backend", status: "No proof state available.", sections: [] };
}

function goalsOk(
  reqId: string,
  goals: GoalView[],
  diagnostics: KernelDiagnostic[],
  display: ProofDisplay,
  theoremStatuses: TheoremStatus[]
): GoalsResponse {
  return { kind: "ok", reqId, goals, diagnostics, display, theoremStatuses };
}

function goalsNoGoals(
  reqId: string,
  reason: string,
  diagnostics: KernelDiagnostic[],
  display: ProofDisplay,
  theoremStatuses: TheoremStatus[]
): GoalsResponse {
  return { kind: "no_goals", reqId, reason, diagnostics, display, theoremStatuses };
}

function goalsError(
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

const connection = createConnection(process.stdin, process.stdout, undefined, ProposedFeatures.all);
const documents = new TextDocuments<any>(TextDocument);
const kernelClient = new KernelClient();

function toLspSeverity(s: number): DiagnosticSeverity {
  switch (s) {
    case 2:
      return DiagnosticSeverity.Warning;
    case 3:
      return DiagnosticSeverity.Information;
    case 4:
      return DiagnosticSeverity.Hint;
    default:
      return DiagnosticSeverity.Error;
  }
}

function asDiagnostics(result: {
  diagnostics: Array<{
    range: { start: { line: number; character: number }; end: { line: number; character: number } };
    severity: number;
    code?: string;
    source?: string;
    message: string;
  }>;
}): Diagnostic[] {
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

function checkAndPublish(doc: TextDocument) {
  const result = kernelClient.checkDocument({
    uri: doc.uri,
    version: doc.version,
    text: doc.getText(),
  });
  connection.sendDiagnostics({ uri: doc.uri, diagnostics: asDiagnostics(result) });
}

async function evaluateGoalsAtLine(
  doc: TextDocument,
  line: number,
  character: number,
  reqId: string
): Promise<GoalsResponse> {
  const result = kernelClient.checkDocument({
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

connection.onInitialize((_params: InitializeParams) => {
  const roots = (_params.workspaceFolders ?? [])
    .map((w: { uri: string }) => w.uri.replace(/^file:\/\//, ""))
    .map((dir: string) => findProjectRoot(dir));
  if (roots.length) {
    connection.console.log(`MyPA project roots: ${roots.join(", ")}`);
  }
  return {
    capabilities: {
      textDocumentSync: TextDocumentSyncKind.Incremental,
    },
  };
});

documents.onDidOpen((e) => checkAndPublish(e.document));
documents.onDidChangeContent((e) => checkAndPublish(e.document));
documents.onDidClose((e) => {
  connection.sendDiagnostics({ uri: e.document.uri, diagnostics: [] });
});

connection.onRequest("mypa/goals", (req: unknown): Promise<GoalsResponse> | GoalsResponse => {
  if (!isGoalsRequest(req)) {
    const reqId = `g:${Date.now()}:${Math.random().toString(36).slice(2, 8)}`;
    const diag = makeErrorDiagnostic("BAD_REQUEST", "Goals request has invalid shape.");
    connection.console.error(`[mypa-lsp] goals.request invalid payload=${JSON.stringify(req)}`);
    return goalsError(reqId, "BAD_REQUEST", diag.message, [diag], goalsFromDiagnostics([diag]), emptyDisplay(), []);
  }

  const reqId = req.reqId ?? `g:${Date.now()}:${Math.random().toString(36).slice(2, 8)}`;
  connection.console.log(
    `[mypa-lsp] goals.request reqId=${reqId} uri=${req.uri} line=${req.line + 1} col=${req.character + 1}`
  );

  const doc = documents.get(req.uri);
  if (!doc) {
    const diag = makeErrorDiagnostic("DOC_NOT_FOUND", `Goals request document not found: ${req.uri}`);
    connection.console.error(`[mypa-lsp] goals.error reqId=${reqId} code=DOC_NOT_FOUND`);
    connection.sendDiagnostics({ uri: req.uri, diagnostics: asDiagnostics({ diagnostics: [diag] }) });
    return goalsError(reqId, "DOC_NOT_FOUND", diag.message, [diag], goalsFromDiagnostics([diag]), emptyDisplay(), []);
  }

  if (req.line < 0 || req.line >= doc.lineCount) {
    const diag = makeErrorDiagnostic(
      "LINE_OUT_OF_RANGE",
      `Requested line ${req.line + 1} is outside document line range 1..${doc.lineCount}.`
    );
    connection.console.error(`[mypa-lsp] goals.error reqId=${reqId} code=LINE_OUT_OF_RANGE`);
    return goalsError(
      reqId,
      "LINE_OUT_OF_RANGE",
      diag.message,
      [diag],
      goalsFromDiagnostics([diag]),
      emptyDisplay(),
      []
    );
  }

  if (req.character < 0) {
    const diag = makeErrorDiagnostic("CHAR_OUT_OF_RANGE", `Requested character ${req.character} must be >= 0.`);
    connection.console.error(`[mypa-lsp] goals.error reqId=${reqId} code=CHAR_OUT_OF_RANGE`);
    return goalsError(reqId, "CHAR_OUT_OF_RANGE", diag.message, [diag], goalsFromDiagnostics([diag]), emptyDisplay(), []);
  }

  checkAndPublish(doc);

  return evaluateGoalsAtLine(doc, req.line, req.character, reqId)
    .then((current) => {
      connection.console.log(`[mypa-lsp] goals.result reqId=${reqId} kind=${current.kind}`);
      return current;
    })
    .catch((err) => {
      const diag = makeErrorDiagnostic("GOALS_REQUEST_FAILED", `Goals request failed: ${String(err)}`);
      connection.console.error(`[mypa-lsp] goals.error reqId=${reqId} code=GOALS_REQUEST_FAILED`);
      connection.sendDiagnostics({ uri: doc.uri, diagnostics: asDiagnostics({ diagnostics: [diag] }) });
      return goalsError(
        reqId,
        "GOALS_REQUEST_FAILED",
        diag.message,
        [diag],
        goalsFromDiagnostics([diag]),
        emptyDisplay(),
        []
      );
    });
});

connection.onRequest("mypa/domainInfo", (): DomainInfo => {
  return kernelClient.getDomainInfo();
});

documents.listen(connection);
connection.listen();
