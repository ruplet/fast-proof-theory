import { useEffect, useRef } from "react";
import { ProofState } from "../../proofStateUi/types";
import "../../proofStateUi/proof-state-renderer.css";
import "../../proofStateUi/proof-state-renderer.js";

declare global {
  interface Window {
    mypaProofStateRenderer: {
      renderProofState(root: HTMLElement, meta: HTMLElement, state: ProofState): void;
      clearProofState(root: HTMLElement, meta: HTMLElement): void;
    };
  }
}

export function ProofStatePanel({ state }: { state: ProofState | null }) {
  const rootRef = useRef<HTMLDivElement>(null);
  const metaRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    if (!rootRef.current || !metaRef.current) return;
    if (!state) {
      window.mypaProofStateRenderer.clearProofState(rootRef.current, metaRef.current);
      return;
    }
    window.mypaProofStateRenderer.renderProofState(rootRef.current, metaRef.current, state);
  }, [state]);

  return (
    <div data-testid="proof-state-panel" style={{ height: "100%", padding: 12, overflow: "auto", borderLeft: "1px solid #d0d7de" }}>
      <div className="header">
        <div className="title">Goals</div>
        <div className="meta" ref={metaRef} />
      </div>
      <div data-testid="proof-state-root" ref={rootRef} className="empty">
        No proof state.
      </div>
    </div>
  );
}
