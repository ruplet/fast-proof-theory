import { ProofState } from "./types";

export type ProofStateHost = {
  requestGoals(): Promise<ProofState>;
  onDidChangeProofState(cb: (state: ProofState) => void): () => void;
};
