import * as monaco from "monaco-editor";
import { createMessageConnection } from "vscode-jsonrpc";
import { BrowserMessageReader, BrowserMessageWriter } from "vscode-languageserver-protocol/browser";
import { DomainInfo, GoalsResponse, KernelDiagnostic } from "../../protocol/types";

export type GoalsRequest = {
  uri: string;
  line: number;
  character: number;
  reqId?: string;
};

export type MyPaBrowserClient = {
  sendDidOpen(model: monaco.editor.ITextModel): void;
  sendDidChange(model: monaco.editor.ITextModel): void;
  sendDidClose(model: monaco.editor.ITextModel): void;
  sendGoalsRequest(req: GoalsRequest): Promise<GoalsResponse>;
  sendDomainInfoRequest(): Promise<DomainInfo>;
  dispose(): void;
};

function toMarkerSeverity(severity: number): monaco.MarkerSeverity {
  if (severity === 2) return monaco.MarkerSeverity.Warning;
  if (severity === 3) return monaco.MarkerSeverity.Info;
  if (severity === 4) return monaco.MarkerSeverity.Hint;
  return monaco.MarkerSeverity.Error;
}

export async function startMyPaBrowserLsp(onDiagnostics?: (uri: string, diagnostics: KernelDiagnostic[]) => void): Promise<MyPaBrowserClient> {
  const worker = new Worker(new URL("../../lsp_browser/src/worker.ts", import.meta.url), { type: "module" });
  const connection = createMessageConnection(new BrowserMessageReader(worker), new BrowserMessageWriter(worker));

  connection.onNotification("textDocument/publishDiagnostics", (params: { uri: string; diagnostics: KernelDiagnostic[] }) => {
    const model = monaco.editor.getModel(monaco.Uri.parse(params.uri));
    if (model) {
      monaco.editor.setModelMarkers(
        model,
        "mypa",
        params.diagnostics.map((d) => ({
          startLineNumber: d.range.start.line + 1,
          startColumn: d.range.start.character + 1,
          endLineNumber: d.range.end.line + 1,
          endColumn: d.range.end.character + 1,
          message: d.message,
          severity: toMarkerSeverity(d.severity),
          code: d.code,
          source: d.source,
        }))
      );
    }
    onDiagnostics?.(params.uri, params.diagnostics);
  });

  connection.listen();

  await connection.sendRequest("initialize", {
    processId: null,
    clientInfo: { name: "mypa-web-monaco" },
    rootUri: null,
    capabilities: {},
  });
  connection.sendNotification("initialized", {});

  return {
    sendDidOpen(model) {
      connection.sendNotification("textDocument/didOpen", {
        textDocument: {
          uri: model.uri.toString(),
          languageId: "mypa",
          version: model.getVersionId(),
          text: model.getValue(),
        },
      });
    },
    sendDidChange(model) {
      connection.sendNotification("textDocument/didChange", {
        textDocument: {
          uri: model.uri.toString(),
          version: model.getVersionId(),
        },
        contentChanges: [{ text: model.getValue() }],
      });
    },
    sendDidClose(model) {
      connection.sendNotification("textDocument/didClose", {
        textDocument: { uri: model.uri.toString() },
      });
    },
    sendGoalsRequest(req) {
      return connection.sendRequest("mypa/goals", req);
    },
    sendDomainInfoRequest() {
      return connection.sendRequest("mypa/domainInfo", {});
    },
    dispose() {
      connection.dispose();
      worker.terminate();
    },
  };
}
