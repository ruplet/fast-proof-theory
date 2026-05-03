import {
  createConnection,
  TextDocuments,
  ProposedFeatures,
  InitializeParams,
  TextDocumentSyncKind,
} from "vscode-languageserver/node";
import { TextDocument } from "vscode-languageserver-textdocument";
import { proofBackendFromModule } from "../../lsp_core/backend";
import { asDiagnostics, createMyPaHandlers } from "../../lsp_core/handlers";
import { MyPaService } from "../../lsp_core/service";
// @ts-ignore - CommonJS JS module without bundled type declarations.
import * as proofAssistantModule from "../../index.js";
import { findProjectRoot } from "./projectRoot";

const connection = createConnection(process.stdin, process.stdout, undefined, ProposedFeatures.all);
const documents = new TextDocuments<any>(TextDocument);
const service = new MyPaService(proofBackendFromModule(proofAssistantModule));

const handlers = createMyPaHandlers(service, {
  getDocument: (uri) => documents.get(uri),
  publishDiagnostics: (uri, diagnostics) => {
    connection.sendDiagnostics({ uri, diagnostics: asDiagnostics({ diagnostics }) });
  },
  log: (message) => connection.console.log(message),
  error: (message) => connection.console.error(message),
});

connection.onInitialize((_params: InitializeParams) => {
  const roots = (_params.workspaceFolders ?? [])
    .map((w: { uri: string }) => w.uri.replace(/^file:\/\//, ""))
    .map((dir: string) => findProjectRoot(dir));
  if (roots.length) {
    connection.console.log(`MyPA project roots: ${roots.join(", ")}`);
  }
  return {
    capabilities: {
      textDocumentSync: TextDocumentSyncKind.Full,
    },
  };
});

documents.onDidOpen((e) => handlers.checkAndPublish(e.document));
documents.onDidChangeContent((e) => handlers.checkAndPublish(e.document));
documents.onDidClose((e) => handlers.handleDidClose(e.document.uri));

connection.onRequest("mypa/goals", handlers.handleGoals);
connection.onRequest("mypa/domainInfo", handlers.handleDomainInfo);

documents.listen(connection);
connection.listen();
