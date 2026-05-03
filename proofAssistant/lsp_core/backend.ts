import { CheckDocumentParams, DomainInfo, KernelCheckResponse } from "../protocol/types";
import { ProofBackend } from "./service";

type ProofAssistantModuleShape = {
  checkDocument: (params: CheckDocumentParams) => KernelCheckResponse;
  domainInfo: DomainInfo;
};

function isProofAssistantModule(value: unknown): value is ProofAssistantModuleShape {
  const rec = value as Partial<ProofAssistantModuleShape> | null;
  return !!rec && typeof rec.checkDocument === "function";
}

export function proofBackendFromModule(moduleLike: unknown, fallback?: unknown): ProofBackend {
  const mod = moduleLike as { default?: unknown } | null;
  const resolved = isProofAssistantModule(moduleLike)
    ? moduleLike
    : isProofAssistantModule(mod?.default)
    ? mod.default
    : isProofAssistantModule(fallback)
    ? fallback
    : undefined;

  if (!resolved) {
    throw new Error("Failed to load proofAssistant backend exports.");
  }

  return {
    checkDocument: (params) => resolved.checkDocument(params),
    getDomainInfo: () => resolved.domainInfo,
  };
}
