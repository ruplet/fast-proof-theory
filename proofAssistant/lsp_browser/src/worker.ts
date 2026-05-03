/// <reference lib="webworker" />
import {
  createConnection,
  ProposedFeatures,
  TextDocumentSyncKind,
  DidOpenTextDocumentParams,
  DidChangeTextDocumentParams,
  DidCloseTextDocumentParams,
} from "vscode-languageserver/browser";
import { BrowserMessageReader, BrowserMessageWriter } from "vscode-languageserver-protocol/browser";
import { proofBackendFromModule } from "../../lsp_core/backend";
import { asDiagnostics, createMyPaHandlers, TextDocumentLike } from "../../lsp_core/handlers";
import { MyPaService } from "../../lsp_core/service";
// @ts-ignore - CommonJS JS module executed by the browser bundler.
import * as proofAssistantModule from "../../index.js";

type MutableDocument = TextDocumentLike & { setText(text: string): void };

function createMutableDocument(uri: string, version: number, text: string): MutableDocument {
  let currentText = text;
  return {
    uri,
    version,
    get lineCount() {
      return currentText.split(/\r?\n/).length;
    },
    getText() {
      return currentText;
    },
    setText(next: string) {
      currentText = next;
    },
  };
}

const workerScope = self as DedicatedWorkerGlobalScope;
const proofAssistantGlobal = (globalThis as typeof globalThis & { __mypaProofAssistant?: unknown }).__mypaProofAssistant;
const connection = createConnection(
  ProposedFeatures.all,
  new BrowserMessageReader(workerScope),
  new BrowserMessageWriter(workerScope),
  undefined
);

const documents = new Map<string, MutableDocument>();
const service = new MyPaService(proofBackendFromModule(proofAssistantModule, proofAssistantGlobal));
const handlers = createMyPaHandlers(service, {
  getDocument: (uri) => documents.get(uri),
  publishDiagnostics: (uri, diagnostics) => {
    connection.sendDiagnostics({ uri, diagnostics: asDiagnostics({ diagnostics }) });
  },
  log: (message) => connection.console.log(message),
  error: (message) => connection.console.error(message),
});

connection.onInitialize(() => ({
  capabilities: {
    textDocumentSync: TextDocumentSyncKind.Full,
  },
}));

connection.onDidOpenTextDocument((params: DidOpenTextDocumentParams) => {
  const d = createMutableDocument(params.textDocument.uri, params.textDocument.version, params.textDocument.text);
  documents.set(d.uri, d);
  handlers.checkAndPublish(d);
});

connection.onDidChangeTextDocument((params: DidChangeTextDocumentParams) => {
  const doc = documents.get(params.textDocument.uri);
  if (!doc) return;
  doc.version = params.textDocument.version;
  for (const change of params.contentChanges) {
    if (typeof change.text === "string") {
      doc.setText(change.text);
    }
  }
  handlers.checkAndPublish(doc);
});

connection.onDidCloseTextDocument((params: DidCloseTextDocumentParams) => {
  documents.delete(params.textDocument.uri);
  handlers.handleDidClose(params.textDocument.uri);
});

connection.onRequest("mypa/goals", handlers.handleGoals);
connection.onRequest("mypa/domainInfo", handlers.handleDomainInfo);

connection.listen();
