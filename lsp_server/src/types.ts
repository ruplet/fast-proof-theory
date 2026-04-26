export type Position = { line: number; character: number };
export type Range = { start: Position; end: Position };

export type GoalHypothesis = { name: string; type: string };
export type GoalView = { id: string; hypotheses: GoalHypothesis[]; target: string };
export type TheoremStatus = { name: string; line: number; verified: boolean };
export type DisplaySection = { title: string; body: string[] };
export type ProofDisplay = {
  title: string;
  status: string;
  sections: DisplaySection[];
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

export type CheckDocumentParams = {
  uri: string;
  version: number;
  text: string;
  cursor?: Position;
};

export type SymbolCompletion = {
  label: string;
  insertText: string;
  detail: string;
  documentation: string;
};

export type DirectiveCompletion = {
  label: string;
  insertText: string;
  detail: string;
  documentation: string;
};

export type TacticDoc = {
  name: string;
  title: string;
  display: string;
  summary: string;
};

export type FormalSystemDoc = {
  key: string;
  aliases: string[];
  title: string;
  summary: string;
  language: string[];
  tactics: TacticDoc[];
  checkedNow: string[];
};

export type DomainInfo = {
  symbolCompletions: SymbolCompletion[];
  directives: DirectiveCompletion[];
  systems: FormalSystemDoc[];
  keywords: string[];
  operators: string[];
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
