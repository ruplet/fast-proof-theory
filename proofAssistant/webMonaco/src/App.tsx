import { useEffect, useRef, useState } from "react";
import * as monaco from "monaco-editor";
import editorWorker from "monaco-editor/esm/vs/editor/editor.worker?worker";
import { configureMyPaTokens, registerMyPaLanguage } from "./monacoLanguage";
import { MyPaBrowserClient, startMyPaBrowserLsp } from "./lspClient";
import { ProofStatePanel } from "./ProofStatePanel";
import { ProofState } from "../../proofStateUi/types";
import { DomainInfo } from "../../protocol/types";
import { emptyDomainInfo, isDomainInfo } from "../../languageSupport/features";
import demoText from "../../../demo/quickstart_linear_gentzen.mypa?raw";

declare global {
  interface Window {
    MonacoEnvironment?: {
      getWorker?: () => Worker;
    };
    mypaDebug?: {
      setText(text: string): void;
      markers(): monaco.editor.IMarker[];
    };
  }
}

export function App() {
  const editorHostRef = useRef<HTMLDivElement>(null);
  const [proofState, setProofState] = useState<ProofState | null>(null);

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
    });
    const debugApi = {
      setText(text: string) {
        model.setValue(text);
      },
      markers() {
        return monaco.editor.getModelMarkers({ owner: "mypa", resource: model.uri });
      },
    };
    if (import.meta.env.DEV) {
      window.mypaDebug = debugApi;
    }

    let lspClient: MyPaBrowserClient | undefined;
    let requestEpoch = 0;
    let disposed = false;
    let timer: number | undefined;

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
        configureMyPaTokens(domainInfo);
      }
    })();

    const changeSub = model.onDidChangeContent(() => {
      lspClient?.sendDidChange(model);
      scheduleUpdateGoals();
    });

    const cursorSub = editor.onDidChangeCursorPosition(() => {
      scheduleUpdateGoals();
    });

    return () => {
      disposed = true;
      requestEpoch += 1;
      if (timer !== undefined) {
        window.clearTimeout(timer);
      }
      changeSub.dispose();
      cursorSub.dispose();
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
    <div style={{ height: "100vh", display: "grid", gridTemplateColumns: "1fr 1fr" }}>
      <div ref={editorHostRef} />
      <ProofStatePanel state={proofState} />
    </div>
  );
}
