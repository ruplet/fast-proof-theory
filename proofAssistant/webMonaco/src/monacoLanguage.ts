import * as monaco from "monaco-editor";
import { DomainInfo } from "../../protocol/types";
import {
  completionsForLine,
  emptyDomainInfo,
  findTacticDoc,
  symbolCompletions,
  tacticHoverMarkdown,
} from "../../languageSupport/features";

let registered = false;
let currentDomainInfo: () => DomainInfo = emptyDomainInfo;

function completionKind(kind: "directive" | "system" | "symbol"): monaco.languages.CompletionItemKind {
  if (kind === "system") return monaco.languages.CompletionItemKind.Reference;
  if (kind === "symbol") return monaco.languages.CompletionItemKind.Snippet;
  return monaco.languages.CompletionItemKind.Keyword;
}

export function configureMyPaTokens(info: DomainInfo = emptyDomainInfo()) {
  const keywords = info.keywords.length ? info.keywords : ["theorem", "using", "by"];
  const operators = info.operators.length ? info.operators : ["⊸", "⊗", "⅋", "⊕", "&", "!", "^", "->"];
  const keywordPattern = new RegExp(`\\b(${keywords.map((k) => k.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")).join("|")})\\b`);
  const operatorPattern = new RegExp(operators.map((op) => op.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")).join("|"));

  monaco.languages.setMonarchTokensProvider("mypa", {
    tokenizer: {
      root: [
        [/--.*/, "comment"],
        [keywordPattern, "keyword"],
        [operatorPattern, "operator"],
        [/[A-Za-z_][A-Za-z0-9_]*/, "identifier"],
      ],
    },
  });
}

export function registerMyPaLanguage(getDomainInfo: () => DomainInfo) {
  currentDomainInfo = getDomainInfo;
  if (registered) {
    configureMyPaTokens(currentDomainInfo());
    return;
  }
  registered = true;

  monaco.languages.register({
    id: "mypa",
    extensions: [".mypa"],
    aliases: ["MyPA"],
  });
  monaco.languages.setLanguageConfiguration("mypa", {
    comments: { lineComment: "--" },
    brackets: [["(", ")"], ["[", "]"], ["{", "}"]],
    autoClosingPairs: [
      { open: "(", close: ")" },
      { open: "[", close: "]" },
      { open: "{", close: "}" },
    ],
  });

  configureMyPaTokens(currentDomainInfo());

  monaco.languages.registerCompletionItemProvider("mypa", {
    triggerCharacters: ["\\", "^", "#", " ", ..."abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"],
    provideCompletionItems(model, position) {
      const linePrefix = model.getLineContent(position.lineNumber).slice(0, position.column - 1);
      const lineItems = completionsForLine(currentDomainInfo(), linePrefix).map((c) => ({
        label: c.label,
        insertText: c.insertText,
        kind: completionKind(c.kind),
        detail: c.detail,
        documentation: c.documentation,
        range: {
          startLineNumber: position.lineNumber,
          startColumn: (c.replaceStartCharacter ?? position.column - 1) + 1,
          endLineNumber: position.lineNumber,
          endColumn: position.column,
        },
      }));
      if (lineItems.length) {
        return { suggestions: lineItems };
      }

      const symbolMatch = linePrefix.match(/\\(?:\^?[\w]*)$/);
      if (!symbolMatch) {
        return { suggestions: [] };
      }
      const prefix = symbolMatch[0];
      const symbolStartColumn = position.column - prefix.length;
      return {
        suggestions: symbolCompletions(currentDomainInfo(), prefix).map((c) => ({
          label: c.label,
          insertText: c.insertText,
          kind: completionKind(c.kind),
          detail: c.detail,
          documentation: c.documentation,
          range: {
            startLineNumber: position.lineNumber,
            startColumn: symbolStartColumn,
            endLineNumber: position.lineNumber,
            endColumn: position.column,
          },
        })),
      };
    },
  });

  monaco.languages.registerHoverProvider("mypa", {
    provideHover(model, position) {
      const word = model.getWordAtPosition(position);
      if (!word) return null;
      const rule = findTacticDoc(currentDomainInfo(), word.word);
      if (!rule) return null;
      return {
        range: new monaco.Range(position.lineNumber, word.startColumn, position.lineNumber, word.endColumn),
        contents: [{ value: tacticHoverMarkdown(rule) }],
      };
    },
  });
}
