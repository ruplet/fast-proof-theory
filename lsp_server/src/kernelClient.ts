import * as path from "path";
import { spawnSync } from "child_process";
import { DocumentIR, KernelCheckResponse } from "./types";

function defaultKernelPath(): string {
  return path.resolve(__dirname, "..", "..", "kernel", "build", "mypa-kernel");
}

function protocolError(message: string): KernelCheckResponse {
  return {
    diagnostics: [
      {
        range: { start: { line: 0, character: 0 }, end: { line: 0, character: 1 } },
        severity: 1,
        code: "KERNEL_PROTOCOL",
        source: "lsp",
        message,
      },
    ],
    goals: [],
  };
}

export class KernelClient {
  constructor(private readonly kernelPath = process.env.PROVER_KERNEL_PATH || defaultKernelPath()) {}

  checkDocument(document: DocumentIR): KernelCheckResponse {
    const requestId = `req:${Date.now()}:${Math.random().toString(36).slice(2, 8)}`;
    const input = JSON.stringify({
      jsonrpc: "2.0",
      id: requestId,
      method: "checkDocument",
      params: { document },
    }) + "\n";

    const result = spawnSync(this.kernelPath, {
      input,
      encoding: "utf8",
      timeout: 2000,
      maxBuffer: 1024 * 1024,
    });

    const hasUsableOutput =
      typeof result.status === "number" && result.status === 0 && typeof result.stdout === "string";
    if (result.error && !hasUsableOutput) {
      return {
        diagnostics: [
          {
            range: { start: { line: 0, character: 0 }, end: { line: 0, character: 0 } },
            severity: 1,
            code: "KERNEL_LAUNCH",
            source: "lsp",
            message: `Kernel launch error: ${result.error.message}`,
          },
        ],
        goals: [],
      };
    }

    if (typeof result.status === "number" && result.status !== 0) {
      return {
        diagnostics: [
          {
            range: { start: { line: 0, character: 0 }, end: { line: 0, character: 0 } },
            severity: 1,
            code: "KERNEL_EXIT",
            source: "lsp",
            message: `Kernel exited with status ${result.status}`,
          },
        ],
        goals: [],
      };
    }

    let payload: any;
    try {
      payload = JSON.parse(result.stdout ?? "");
    } catch (err) {
      return protocolError(`Invalid JSON response from kernel: ${String(err)}`);
    }

    if (!payload || payload.jsonrpc !== "2.0") {
      return protocolError("Kernel response is missing jsonrpc=2.0");
    }

    if (payload.error) {
      const message = typeof payload.error.message === "string" ? payload.error.message : "Kernel RPC error";
      const code = typeof payload.error.code === "number" ? `KERNEL_RPC_${payload.error.code}` : "KERNEL_RPC";
      return {
        diagnostics: [
          {
            range: { start: { line: 0, character: 0 }, end: { line: 0, character: 1 } },
            severity: 1,
            code,
            source: "kernel",
            message,
          },
        ],
        goals: [],
      };
    }

    const rpcResult = payload.result;
    if (!rpcResult || !Array.isArray(rpcResult.diagnostics) || !Array.isArray(rpcResult.goals)) {
      return protocolError("Kernel result is missing diagnostics/goals arrays");
    }

    return {
      diagnostics: rpcResult.diagnostics,
      goals: rpcResult.goals,
    };
  }
}
