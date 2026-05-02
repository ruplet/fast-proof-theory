import { CheckDocumentParams, DomainInfo, KernelCheckResponse } from "./types";

// eslint-disable-next-line @typescript-eslint/no-var-requires
const proofAssistant: {
  checkDocument: (params: CheckDocumentParams) => KernelCheckResponse;
  domainInfo: DomainInfo;
} = require("../../index.js");

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
  checkDocument(params: CheckDocumentParams): KernelCheckResponse {
    try {
      return proofAssistant.checkDocument(params);
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
      return proofAssistant.domainInfo || emptyDomainInfo();
    } catch {
      return emptyDomainInfo();
    }
  }
}
