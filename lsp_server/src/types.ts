export type Position = { line: number; character: number };
export type Range = { start: Position; end: Position };

export type Formula =
  | { node: "atom"; atom: { name: string; negated: boolean } }
  | { node: "tensor"; tensor: { left: Formula; right: Formula } }
  | { node: "with"; with: { left: Formula; right: Formula } }
  | { node: "plus"; plus: { left: Formula; right: Formula } }
  | { node: "lolli"; lolli: { left: Formula; right: Formula } }
  | { node: "bang"; bang: { of: Formula } }
  | { node: "one"; one: Record<string, never> }
  | { node: "top"; top: Record<string, never> }
  | { node: "bot"; bot: Record<string, never> }
  | { node: "zero"; zero: Record<string, never> };

export type HypDecl = { name: string; formula: Formula; range: Range };
export type GoalDecl = { formula: Formula; range: Range };
export type TacticStep = {
  name: string;
  args: string[];
  range: Range;
  assumeName?: string;
  assumeFormula?: Formula;
};

export type TheoremIR = {
  name: string;
  logic: string;
  calculus: string;
  range: Range;
  hypotheses: HypDecl[];
  goals: GoalDecl[];
  tactics: TacticStep[];
};

export type DocumentIR = {
  uri: string;
  version: number;
  theorems: TheoremIR[];
};

export type GoalHypothesis = { name: string; type: string };
export type GoalView = { id: string; hypotheses: GoalHypothesis[]; target: string };
export type TheoremStatus = { name: string; line: number; verified: boolean };
export type ProofDisplay = {
  title: string;
  status: string;
  sections: Array<{ title: string; body: string[] }>;
};

export type KernelDiagnostic = {
  range: Range;
  severity: number;
  code: string;
  source: string;
  message: string;
};

export type KernelCheckResponse = {
  diagnostics: KernelDiagnostic[];
  goals: GoalView[];
  display: ProofDisplay;
  theoremStatuses: TheoremStatus[];
};

export type GoalsResponse =
  | {
      kind: "ok";
      reqId: string;
      goals: GoalView[];
      diagnostics: KernelDiagnostic[];
      display: ProofDisplay;
      theoremStatuses: TheoremStatus[];
    }
  | {
      kind: "no_goals";
      reqId: string;
      reason: string;
      diagnostics: KernelDiagnostic[];
      display: ProofDisplay;
      theoremStatuses: TheoremStatus[];
    }
  | {
      kind: "error";
      reqId: string;
      code: string;
      message: string;
      diagnostics: KernelDiagnostic[];
      goals: GoalView[];
      display: ProofDisplay;
      theoremStatuses: TheoremStatus[];
    };
