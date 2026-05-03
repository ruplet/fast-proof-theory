import { DirectiveCompletion, DomainInfo, SymbolCompletion, TacticDoc } from "../protocol/types";

export type CompletionKind = "directive" | "system" | "symbol";

export type CompletionCandidate = {
  kind: CompletionKind;
  label: string;
  insertText: string;
  detail: string;
  documentation?: string;
  replaceStartCharacter?: number;
};

export function emptyDomainInfo(): DomainInfo {
  return {
    symbolCompletions: [],
    directives: [],
    systems: [],
    keywords: [],
    operators: [],
  };
}

export function isStringArray(value: unknown): value is string[] {
  return Array.isArray(value) && value.every((item) => typeof item === "string");
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null;
}

function isSymbolCompletion(value: unknown): value is SymbolCompletion {
  return isRecord(value) &&
    typeof value.label === "string" &&
    typeof value.insertText === "string" &&
    typeof value.detail === "string" &&
    typeof value.documentation === "string";
}

function isDirectiveCompletion(value: unknown): value is DirectiveCompletion {
  return isSymbolCompletion(value);
}

function isTacticDoc(value: unknown): value is TacticDoc {
  return isRecord(value) &&
    typeof value.name === "string" &&
    typeof value.title === "string" &&
    typeof value.display === "string" &&
    typeof value.summary === "string";
}

export function isDomainInfo(value: unknown): value is DomainInfo {
  if (!isRecord(value)) return false;
  return (
    Array.isArray(value.symbolCompletions) &&
    value.symbolCompletions.every(isSymbolCompletion) &&
    Array.isArray(value.directives) &&
    value.directives.every(isDirectiveCompletion) &&
    Array.isArray(value.systems) &&
    value.systems.every((system) =>
      isRecord(system) &&
      typeof system.key === "string" &&
      isStringArray(system.aliases) &&
      typeof system.title === "string" &&
      typeof system.summary === "string" &&
      isStringArray(system.language) &&
      Array.isArray(system.tactics) &&
      system.tactics.every(isTacticDoc) &&
      isStringArray(system.checkedNow)
    ) &&
    isStringArray(value.keywords) &&
    isStringArray(value.operators)
  );
}

export function tacticDocsByName(info: DomainInfo): Map<string, TacticDoc> {
  const docs = new Map<string, TacticDoc>();
  for (const system of info.systems) {
    for (const tactic of system.tactics) {
      docs.set(tactic.name.toLowerCase(), tactic);
    }
  }
  return docs;
}

export function findTacticDoc(info: DomainInfo, word: string): TacticDoc | undefined {
  return tacticDocsByName(info).get(word.toLowerCase());
}

export function completionsForLine(info: DomainInfo, linePrefix: string): CompletionCandidate[] {
  if (linePrefix.startsWith("#help ")) {
    const systemPrefix = linePrefix.slice("#help ".length).trimLeft();
    return info.systems
      .flatMap((system) =>
        [system.key, ...system.aliases].map((name) => ({
          kind: "system" as const,
          label: name,
          insertText: name,
          detail: system.title,
          documentation: system.summary,
          replaceStartCharacter: "#help ".length,
        }))
      )
      .filter((c) => !systemPrefix || c.label.startsWith(systemPrefix));
  }

  if (/^\s*#\w*$/.test(linePrefix) || /^\s*#$/.test(linePrefix)) {
    const directivePrefix = linePrefix.trimLeft();
    const hashColumn = Math.max(linePrefix.indexOf("#"), 0);
    return info.directives
      .filter((c) => !directivePrefix || c.label.startsWith(directivePrefix))
      .map((c) => ({
        kind: "directive",
        label: c.label,
        insertText: c.insertText,
        detail: c.detail,
        documentation: c.documentation,
        replaceStartCharacter: hashColumn,
      }));
  }

  return [];
}

export function symbolCompletions(info: DomainInfo, prefix: string): CompletionCandidate[] {
  return info.symbolCompletions
    .filter((c) => !prefix || c.label.startsWith(prefix))
    .map((c) => ({
      kind: "symbol",
      label: c.label,
      insertText: c.insertText,
      detail: c.detail,
      documentation: c.documentation,
    }));
}

export function escapeRegExp(text: string): string {
  return text.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

export function firstKeywordToken(info: DomainInfo, text: string): { start: number; length: number } | undefined {
  const trimmed = text.trim();
  const firstWord = (trimmed.match(/^([^\s]+)/) || [])[1];
  if (!firstWord) return undefined;
  const keywordSet = new Set(info.keywords.map((k) => k.toLowerCase()));
  if (!keywordSet.has(firstWord.toLowerCase())) return undefined;
  return { start: text.indexOf(firstWord), length: firstWord.length };
}

export function operatorMatches(info: DomainInfo, text: string): { start: number; length: number }[] {
  if (!info.operators.length) return [];
  const operatorRe = new RegExp(info.operators.map(escapeRegExp).join("|"), "g");
  const matches: { start: number; length: number }[] = [];
  let match: RegExpExecArray | null;
  while ((match = operatorRe.exec(text))) {
    matches.push({ start: match.index, length: match[0].length });
  }
  return matches;
}
