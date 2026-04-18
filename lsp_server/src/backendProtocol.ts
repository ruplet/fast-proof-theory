export type Position = { line: number; character: number };
export type Range = { start: Position; end: Position };

export type BackendDiagnostic = {
  range: Range;
  severity: number;
  code: string;
  source: string;
  message: string;
};

export type GoalHypothesis = { name: string; type: string };
export type GoalView = { id: string; hypotheses: GoalHypothesis[]; target: string };
export type TheoremStatus = { name: string; line: number; verified: boolean };

export type DisplaySection = {
  title: string;
  body: string[];
};

export type ProofDisplay = {
  title: string;
  status: string;
  sections: DisplaySection[];
};

export type CheckDocumentParams = {
  uri: string;
  version: number;
  text: string;
  cursor?: Position;
};

export type KernelCheckResponse = {
  diagnostics: BackendDiagnostic[];
  goals: GoalView[];
  display: ProofDisplay;
  theoremStatuses: TheoremStatus[];
};
