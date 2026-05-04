import { useEffect, useRef, useState } from "react";
import * as monaco from "monaco-editor";
import editorWorker from "monaco-editor/esm/vs/editor/editor.worker?worker";
import { configureMyPaTokens, registerMyPaLanguage } from "./monacoLanguage";
import { MyPaBrowserClient, startMyPaBrowserLsp } from "./lspClient";
import { ProofStatePanel } from "./ProofStatePanel";
import { HelpPage } from "./HelpPage";
import { ProofState } from "../../proofStateUi/types";
import { DomainInfo } from "../../protocol/types";
import { emptyDomainInfo, isDomainInfo, symbolCompletions } from "../../languageSupport/features";
import demoText from "../../../demo/ill_examples_from_brauner.mypa?raw";
import "./App.css";

const symbolShortcuts: Record<string, string> = {
  "\\tensor": "⊗",
  "\\par": "⅋",
  "\\oplus": "⊕",
  "\\with": "&",
  "\\lolli": "⊸",
  "\\^bot": "^bot",
};

declare global {
  interface Window {
    MonacoEnvironment?: {
      getWorker?: () => Worker;
    };
    mypaDebug?: {
      setText(text: string): void;
      getText(): string;
      setPosition(lineNumber: number, column: number): void;
      getPosition(): monaco.Position | null;
      markers(): monaco.editor.IMarker[];
      symbolCompletionLabels(prefix: string): string[];
      wordBasedSuggestions(): string;
    };
  }
}

export function App() {
  const editorHostRef = useRef<HTMLDivElement>(null);
  const [proofState, setProofState] = useState<ProofState | null>(null);
  const [domainInfoState, setDomainInfoState] = useState<DomainInfo>(emptyDomainInfo());
  const [showHelp, setShowHelp] = useState(false);

  useEffect(() => {
    window.MonacoEnvironment = {
      getWorker: () => new editorWorker(),
    };
    let domainInfo: DomainInfo = emptyDomainInfo();
    registerMyPaLanguage(() => domainInfo);
    if (!editorHostRef.current) return;

    const uri = monaco.Uri.parse("inmemory://model/main.mypa");
    const model = monaco.editor.createModel(demoText, "mypa", uri);
    const editor = monaco.editor.create(editorHostRef.current, {
      model,
      automaticLayout: true,
      minimap: { enabled: false },
      fontSize: 14,
      theme: "vs",
      wordBasedSuggestions: "off",
    });
    const debugApi = {
      setText(text: string) {
        model.setValue(text);
      },
      getText() {
        return model.getValue();
      },
      setPosition(lineNumber: number, column: number) {
        editor.setPosition({ lineNumber, column });
        editor.focus();
      },
      getPosition() {
        return editor.getPosition();
      },
      markers() {
        return monaco.editor.getModelMarkers({ owner: "mypa", resource: model.uri });
      },
      symbolCompletionLabels(prefix: string) {
        return symbolCompletions(domainInfo, prefix).map((item) => item.label);
      },
      wordBasedSuggestions() {
        return String(editor.getRawOptions().wordBasedSuggestions);
      },
    };
    if (import.meta.env.DEV) {
      window.mypaDebug = debugApi;
    }

    let lspClient: MyPaBrowserClient | undefined;
    let requestEpoch = 0;
    let disposed = false;
    let timer: number | undefined;
    let expandingShortcut = false;

    const expandSymbolShortcutAtPosition = (pos: monaco.Position) => {
      if (expandingShortcut) return;
      const line = model.getLineContent(pos.lineNumber);
      const prefix = line.slice(0, pos.column - 1);
      const match = prefix.match(/\\\^bot$|\\[A-Za-z]+$/);
      if (!match) return;
      const replacement = symbolShortcuts[match[0]];
      if (!replacement) return;
      const startColumn = pos.column - match[0].length;
      const endColumn = startColumn + replacement.length;
      expandingShortcut = true;
      try {
        editor.executeEdits("mypa-symbol-shortcut", [
          {
            range: new monaco.Range(pos.lineNumber, startColumn, pos.lineNumber, pos.column),
            text: replacement,
            forceMoveMarkers: true,
          },
        ], () => [
          new monaco.Selection(pos.lineNumber, endColumn, pos.lineNumber, endColumn),
        ]);
        window.setTimeout(() => {
          const current = editor.getPosition();
          if (!disposed && current?.lineNumber === pos.lineNumber && current.column === pos.column) {
            editor.setSelection(new monaco.Selection(pos.lineNumber, endColumn, pos.lineNumber, endColumn));
          }
        }, 0);
      } finally {
        expandingShortcut = false;
      }
    };

    const isAfterSymbolShortcutPrefix = () => {
      const pos = editor.getPosition();
      if (!pos) return false;
      const line = model.getLineContent(pos.lineNumber);
      return /\\(?:\^?[A-Za-z]*)$/.test(line.slice(0, pos.column - 1));
    };

    const updateGoals = async () => {
      if (!lspClient) return;
      const pos = editor.getPosition();
      if (!pos) return;
      const myEpoch = ++requestEpoch;
      try {
        const response = await lspClient.sendGoalsRequest({
          uri: model.uri.toString(),
          line: pos.lineNumber - 1,
          character: pos.column - 1,
        });
        if (disposed || myEpoch !== requestEpoch) return;
        if (response.kind === "ok") {
          setProofState({ goals: response.goals, display: response.display });
          return;
        }
        if (response.kind === "no_goals") {
          setProofState({ goals: [], display: response.display, tone: "normal" });
          return;
        }
        setProofState({ goals: response.goals, display: response.display, tone: "error" });
      } catch (err) {
        if (disposed || myEpoch !== requestEpoch) return;
        setProofState({
          goals: [
            {
              id: "lsp:error",
              hypotheses: [],
              target: `Goals request failed: ${String(err)}`,
            },
          ],
          tone: "error",
        });
      }
    };

    const scheduleUpdateGoals = () => {
      if (timer !== undefined) {
        window.clearTimeout(timer);
      }
      timer = window.setTimeout(() => {
        timer = undefined;
        void updateGoals();
      }, 150);
    };

    void (async () => {
      lspClient = await startMyPaBrowserLsp();
      if (disposed) {
        lspClient.dispose();
        return;
      }
      lspClient.sendDidOpen(model);
      await updateGoals();
      const info = await lspClient.sendDomainInfoRequest();
      if (isDomainInfo(info)) {
        domainInfo = info;
        setDomainInfoState(info);
        configureMyPaTokens(domainInfo);
      }
    })();

    const changeSub = model.onDidChangeContent((event) => {
      if (!expandingShortcut) {
        const change = event.changes[event.changes.length - 1];
        if (change && change.text) {
          expandSymbolShortcutAtPosition(model.getPositionAt(change.rangeOffset + change.text.length));
        }
      }
      lspClient?.sendDidChange(model);
      scheduleUpdateGoals();
    });

    const cursorSub = editor.onDidChangeCursorPosition(() => {
      scheduleUpdateGoals();
    });

    const typeSub = editor.onDidType(() => {
      if (expandingShortcut || !isAfterSymbolShortcutPrefix()) return;
      void editor.getAction("editor.action.triggerSuggest")?.run();
    });

    return () => {
      disposed = true;
      requestEpoch += 1;
      if (timer !== undefined) {
        window.clearTimeout(timer);
      }
      changeSub.dispose();
      cursorSub.dispose();
      typeSub.dispose();
      if (lspClient) {
        lspClient.sendDidClose(model);
        lspClient.dispose();
      }
      if (window.mypaDebug === debugApi) {
        delete window.mypaDebug;
      }
      editor.dispose();
      model.dispose();
    };
  }, []);

  return (
    <div style={{ height: "100vh", display: "grid", gridTemplateRows: "48px 1fr" }}>
      <div style={{ display: "flex", alignItems: "center", justifyContent: "space-between", padding: "0 12px", borderBottom: "1px solid #d0d7de", background: "#ffffff" }}>
        <strong>MyPA Monaco</strong>
        <div style={{ display: "flex", gap: 8 }}>
          <button
            type="button"
            onClick={() => setShowHelp(false)}
            style={{ border: "1px solid #d0d7de", background: showHelp ? "#ffffff" : "#f6f8fa", borderRadius: 6, padding: "6px 10px", cursor: "pointer" }}
          >
            Editor
          </button>
          <button
            type="button"
            onClick={() => setShowHelp(true)}
            style={{ border: "1px solid #d0d7de", background: showHelp ? "#f6f8fa" : "#ffffff", borderRadius: 6, padding: "6px 10px", cursor: "pointer" }}
          >
            Help
          </button>
        </div>
      </div>
      {showHelp ? (
        <HelpPage info={domainInfoState} />
      ) : null}
      <div className="mypa-workspace" style={{ display: showHelp ? "none" : undefined }}>
        <div ref={editorHostRef} className="mypa-editor-host" />
        <div className="mypa-proof-host">
          <ProofStatePanel state={proofState} />
        </div>
      </div>
    </div>
  );
}
