import * as monaco from "monaco-editor";
import { DomainInfo } from "../../protocol/types";
import {
  completionsForLine,
  emptyDomainInfo,
  findTacticDoc,
  symbolCompletions,
} from "../../languageSupport/features";

let registered = false;

function completionKind(kind: "directive" | "system" | "symbol"): monaco.languages.CompletionItemKind {
  if (kind === "system") return monaco.languages.CompletionItemKind.Reference;
  if (kind === "symbol") return monaco.languages.CompletionItemKind.Snippet;
  return monaco.languages.CompletionItemKind.Keyword;
}

export function configureMyPaTokens(info: DomainInfo = emptyDomainInfo()) {
  const keywords = info.keywords.length ? info.keywords : ["def", "theorem", "using", "in", "with", "by"];
  const operators = info.operators.length ? info.operators : ["⊸", "⊗", "⊕", "&", "!", "->"];
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
  if (registered) {
    configureMyPaTokens(getDomainInfo());
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

  configureMyPaTokens(getDomainInfo());

  monaco.languages.registerCompletionItemProvider("mypa", {
    triggerCharacters: ["\\", "#", " "],
    provideCompletionItems(model, position) {
      const linePrefix = model.getLineContent(position.lineNumber).slice(0, position.column - 1);
      const lineItems = completionsForLine(getDomainInfo(), linePrefix).map((c) => ({
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

      const symbolMatch = linePrefix.match(/\\[\w]*$/);
      const prefix = symbolMatch ? symbolMatch[0] : "";
      const symbolStartColumn = symbolMatch ? position.column - prefix.length : position.column;
      return {
        suggestions: symbolCompletions(getDomainInfo(), prefix).map((c) => ({
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
      const rule = findTacticDoc(getDomainInfo(), word.word);
      if (!rule) return null;
      return {
        range: new monaco.Range(position.lineNumber, word.startColumn, position.lineNumber, word.endColumn),
        contents: [
          { value: `**${rule.title}**` },
          { value: `\`\`\`text\n${rule.display}\n\`\`\`` },
        ],
      };
    },
  });
}
