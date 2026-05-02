declare module "vscode-languageclient/node" {
  export const TransportKind: { stdio: number };
  export type ServerOptions = unknown;
  export type LanguageClientOptions = unknown;
  export class LanguageClient {
    constructor(id: string, name: string, serverOptions: unknown, clientOptions: unknown);
    start(): { dispose(): void };
    onReady(): Promise<void>;
    sendRequest(method: string, params?: unknown): Promise<any>;
    stop(): Promise<void>;
  }
}
