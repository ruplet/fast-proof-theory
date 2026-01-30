"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.GoalsPanel = void 0;
// GoalsPanel.ts
const vscode = __importStar(require("vscode"));
class GoalsPanel {
    constructor(panel, extensionUri) {
        this.disposed = false;
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
    static createOrShow(context, viewColumn = vscode.ViewColumn.Beside) {
        const panel = vscode.window.createWebviewPanel("mypaGoals", "Goals", viewColumn, {
            enableScripts: true,
            localResourceRoots: [context.extensionUri],
            retainContextWhenHidden: true,
        });
        return new GoalsPanel(panel, context.extensionUri);
    }
    /** Set the proof state: hypotheses (name:type) and goals. */
    setProofState(state) {
        if (this.disposed)
            return;
        const msg = { type: "setState", state };
        void this.panel.webview.postMessage(msg);
    }
    /** Clear the panel UI. */
    clear() {
        if (this.disposed)
            return;
        const msg = { type: "clear" };
        void this.panel.webview.postMessage(msg);
    }
    reveal(viewColumn) {
        if (this.disposed)
            return;
        this.panel.reveal(viewColumn);
    }
    dispose() {
        if (this.disposed)
            return;
        this.panel.dispose();
        this.disposed = true;
    }
    renderHtml(webview, _extensionUri) {
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
exports.GoalsPanel = GoalsPanel;
function getNonce() {
    const chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
    let out = "";
    for (let i = 0; i < 32; i++)
        out += chars.charAt(Math.floor(Math.random() * chars.length));
    return out;
}
//# sourceMappingURL=GoalsPanel.js.map