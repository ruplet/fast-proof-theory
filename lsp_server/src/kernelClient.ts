import * as path from "path";
import { spawnSync } from "child_process";
import { CheckDocumentParams, DomainInfo, KernelCheckResponse } from "./types";

const emptyDisplay = {
  title: "Lean Backend",
  status: "No proof state available.",
  sections: [],
};

function defaultKernelPath(): string {
  return path.resolve(__dirname, "..", "..", ".lake", "build", "bin", "mypa-lean-kernel");
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
    display: emptyDisplay,
    theoremStatuses: [],
  };
}

function emptyDomainInfo(): DomainInfo {
  return {
    symbolCompletions: [],
    directives: [],
    systems: [],
    keywords: [],
    operators: [],
  };
}

export class KernelClient {
  constructor(private readonly kernelPath = process.env.PROVER_KERNEL_PATH || defaultKernelPath()) {}

  private callKernel(method: string, params?: unknown): unknown {
    const requestId = `req:${Date.now()}:${Math.random().toString(36).slice(2, 8)}`;
    const input = JSON.stringify({
      jsonrpc: "2.0",
      id: requestId,
      method,
      params: params ?? null,
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
        display: emptyDisplay,
        theoremStatuses: [],
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
        display: emptyDisplay,
        theoremStatuses: [],
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
      throw new Error(message);
    }

    return payload.result;
  }

  checkDocument(params: CheckDocumentParams): KernelCheckResponse {
    let rpcResult: any;
    try {
      rpcResult = this.callKernel("checkDocument", params);
    } catch (err) {
      return {
        diagnostics: [
          {
            range: { start: { line: 0, character: 0 }, end: { line: 0, character: 1 } },
            severity: 1,
            code: "KERNEL_RPC",
            source: "kernel",
            message: (err as Error).message,
          },
        ],
        goals: [],
        display: emptyDisplay,
        theoremStatuses: [],
      };
    }

    if (
      !rpcResult ||
      !Array.isArray(rpcResult.diagnostics) ||
      !Array.isArray(rpcResult.goals) ||
      !Array.isArray(rpcResult.theoremStatuses) ||
      !rpcResult.display ||
      typeof rpcResult.display.title !== "string" ||
      typeof rpcResult.display.status !== "string" ||
      !Array.isArray(rpcResult.display.sections)
    ) {
      return protocolError("Kernel result is missing diagnostics/goals/display payload");
    }

    return {
      diagnostics: rpcResult.diagnostics,
      goals: rpcResult.goals,
      display: rpcResult.display,
      theoremStatuses: rpcResult.theoremStatuses,
    };
  }

  getDomainInfo(): DomainInfo {
    let rpcResult: any;
    try {
      rpcResult = this.callKernel("domainInfo");
    } catch {
      return emptyDomainInfo();
    }
    if (
      !rpcResult ||
      !Array.isArray(rpcResult.symbolCompletions) ||
      !Array.isArray(rpcResult.directives) ||
      !Array.isArray(rpcResult.systems) ||
      !Array.isArray(rpcResult.keywords) ||
      !Array.isArray(rpcResult.operators)
    ) {
      return emptyDomainInfo();
    }
    return rpcResult;
  }
}
