import { GoalView, ProofDisplay } from "../protocol/types";

export type ProofStateTone = "normal" | "error";

export type ProofState = {
  goals: GoalView[];
  display?: ProofDisplay;
  tone?: ProofStateTone;
};
