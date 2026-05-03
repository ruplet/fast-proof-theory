declare module "vscode-languageserver/node" {
  export const ProposedFeatures: { all: unknown };
  export const TextDocumentSyncKind: { Full: number; Incremental: number };
  export enum DiagnosticSeverity {
    Error = 1,
    Warning = 2,
    Information = 3,
    Hint = 4,
  }
  export type Diagnostic = any;
  export type InitializeParams = any;
  export class TextDocuments<T = any> {
    constructor(TextDocumentCtor: any);
    get(uri: string): T | undefined;
    onDidOpen(handler: (e: { document: T }) => void): void;
    onDidChangeContent(handler: (e: { document: T }) => void): void;
    onDidClose(handler: (e: { document: T }) => void): void;
    listen(connection: any): void;
  }
  export function createConnection(...args: any[]): any;
}

declare module "vscode-languageserver-textdocument" {
  export class TextDocument {
    readonly uri: string;
    readonly version: number;
    getText(range?: any): string;
    offsetAt(pos: { line: number; character: number }): number;
  }
}

declare module "path" {
  export function resolve(...paths: string[]): string;
  export function join(...paths: string[]): string;
  export function dirname(path: string): string;
  export const sep: string;
}

declare module "fs" {
  export function existsSync(path: string): boolean;
}

declare module "child_process" {
  export function spawnSync(command: string, options?: any): any;
}

declare const __dirname: string;
declare const process: any;
