// GoalsPanel.ts
import * as vscode from "vscode";

export type Hypothesis = {
  name: string;
  type: string;
};

export type Goal = {
  id?: string;
  hypotheses: Hypothesis[];
  target: string;
};

export type ProofState = {
  goals: Goal[];
};

type WebviewMsg =
  | { type: "setState"; state: ProofState }
  | { type: "clear" };

export class GoalsPanel implements vscode.Disposable {
  private panel: vscode.WebviewPanel;
  private disposed = false;

  private constructor(panel: vscode.WebviewPanel, extensionUri: vscode.Uri) {
    this.panel = panel;

    this.panel.webview.options = {
      enableScripts: true,
      localResourceRoots: [extensionUri],
    };

    this.panel.webview.html = this.renderHtml(this.panel.webview, extensionUri);

    this.panel.onDidDispose(() => {
      this.disposed = true;
    });
  }

  /** Create (or reveal) a Goals panel. */
  static createOrShow(
    context: vscode.ExtensionContext,
    viewColumn: vscode.ViewColumn = vscode.ViewColumn.Beside
  ): GoalsPanel {
    const panel = vscode.window.createWebviewPanel(
      "mypaGoals",
      "Goals",
      viewColumn,
      {
        enableScripts: true,
        localResourceRoots: [context.extensionUri],
        retainContextWhenHidden: true,
      }
    );

    return new GoalsPanel(panel, context.extensionUri);
  }

  /** Set the proof state: hypotheses (name:type) and goals. */
  setProofState(state: ProofState) {
    if (this.disposed) return;
    const msg: WebviewMsg = { type: "setState", state };
    void this.panel.webview.postMessage(msg);
  }

  /** Clear the panel UI. */
  clear() {
    if (this.disposed) return;
    const msg: WebviewMsg = { type: "clear" };
    void this.panel.webview.postMessage(msg);
  }

  reveal(viewColumn?: vscode.ViewColumn) {
    if (this.disposed) return;
    this.panel.reveal(viewColumn);
  }

  dispose() {
    if (this.disposed) return;
    this.panel.dispose();
    this.disposed = true;
  }

  private renderHtml(webview: vscode.Webview, _extensionUri: vscode.Uri): string {
    const nonce = getNonce();
    const csp = [
      `default-src 'none'`,
      `img-src ${webview.cspSource} https: data:`,
      `style-src ${webview.cspSource} 'unsafe-inline'`,
      `script-src 'nonce-${nonce}'`,
    ].join("; ");

    return /* html */ `<!doctype html>
<html>
  <head>
    <meta charset="utf-8" />
    <meta http-equiv="Content-Security-Policy" content="${csp}" />
    <meta name="viewport" content="width=device-width, initial-scale=1.0" />
    <title>Goals</title>
    <style>
      body { font-family: var(--vscode-font-family); font-size: 13px; padding: 10px; }
      .header { display:flex; align-items:baseline; justify-content:space-between; margin-bottom:10px; }
      .title { font-weight: 600; font-size: 14px; }
      .meta { opacity: 0.7; }
      .goal { border: 1px solid var(--vscode-editorWidget-border); border-radius: 6px; padding: 10px; margin-bottom: 10px; }
      .goalId { opacity: 0.8; margin-bottom: 6px; font-size: 12px; }
      .sectionTitle { font-weight: 600; margin: 8px 0 6px; }
      .hyp { font-family: var(--vscode-editor-font-family); font-size: 12px; white-space: pre-wrap; }
      .target { font-family: var(--vscode-editor-font-family); font-size: 12px; white-space: pre-wrap; padding-top: 4px; }
      .empty { opacity: 0.7; font-style: italic; padding: 8px 0; }
      ul { margin: 0; padding-left: 18px; }
      li { margin: 2px 0; }
      code { font-family: var(--vscode-editor-font-family); }
    </style>
  </head>
  <body>
    <div class="header">
      <div class="title">Goals</div>
      <div class="meta" id="meta"></div>
    </div>

    <div id="root" class="empty">No proof state.</div>

    <script nonce="${nonce}">
      /** @typedef {{name: string, type: string}} Hypothesis */
      /** @typedef {{id?: string, hypotheses: Hypothesis[], target: string}} Goal */
      /** @typedef {{goals: Goal[]}} ProofState */

      const root = document.getElementById("root");
      const meta = document.getElementById("meta");

      function esc(s) {
        return String(s).replace(/[&<>"']/g, c => ({
          "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;"
        }[c]));
      }

      /** @param {ProofState} state */
      function render(state) {
        const goals = (state && state.goals) ? state.goals : [];
        meta.textContent = goals.length ? (goals.length + " goal" + (goals.length === 1 ? "" : "s")) : "";

        if (!goals.length) {
          root.className = "empty";
          root.innerHTML = "No goals.";
          return;
        }

        root.className = "";
        root.innerHTML = goals.map((g, i) => {
          const gid = g.id ?? ("#" + (i + 1));
          const hyps = g.hypotheses ?? [];
          const hypsHtml = hyps.length
            ? "<ul>" + hyps.map(h => "<li class='hyp'><code>" + esc(h.name) + "</code> : " + esc(h.type) + "</li>").join("") + "</ul>"
            : "<div class='empty'>No hypotheses.</div>";

          return \`
            <div class="goal">
              <div class="goalId"><b>\${esc(gid)}</b></div>
              <div class="sectionTitle">Hypotheses</div>
              \${hypsHtml}
              <div class="sectionTitle">Goal</div>
              <div class="target">\${esc(g.target ?? "")}</div>
            </div>
          \`;
        }).join("");
      }

      window.addEventListener("message", (event) => {
        const msg = event.data || {};
        if (msg.type === "setState") render(msg.state);
        if (msg.type === "clear") {
          meta.textContent = "";
          root.className = "empty";
          root.innerHTML = "No proof state.";
        }
      });
    </script>
  </body>
</html>`;
  }
}

function getNonce(): string {
  const chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
  let out = "";
  for (let i = 0; i < 32; i++) out += chars.charAt(Math.floor(Math.random() * chars.length));
  return out;
}

