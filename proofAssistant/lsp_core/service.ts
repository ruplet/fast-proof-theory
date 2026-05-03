import { CheckDocumentParams, DomainInfo, KernelCheckResponse } from "../protocol/types";

export type ProofBackend = {
  checkDocument: (params: CheckDocumentParams) => KernelCheckResponse;
  getDomainInfo: () => DomainInfo;
};

function emptyDomainInfo(): DomainInfo {
  return {
    symbolCompletions: [],
    directives: [],
    systems: [],
    keywords: [],
    operators: [],
  };
}

export class MyPaService {
  constructor(private readonly backend: ProofBackend) {}

  checkDocument(params: CheckDocumentParams): KernelCheckResponse {
    try {
      return this.backend.checkDocument(params);
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
        display: { title: "proofAssistant", status: "Check failed.", sections: [] },
        theoremStatuses: [],
      };
    }
  }

  getDomainInfo(): DomainInfo {
    try {
      return this.backend.getDomainInfo() || emptyDomainInfo();
    } catch {
      return emptyDomainInfo();
    }
  }
}
