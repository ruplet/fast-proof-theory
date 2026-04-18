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
            if (GoalsPanel.currentPanel === this) {
                GoalsPanel.currentPanel = undefined;
            }
        });
    }
    /** Create (or reveal) a Goals panel. */
    static createOrShow(context, viewColumn = vscode.ViewColumn.Beside, preserveFocus = false) {
        const existing = GoalsPanel.currentPanel;
        if (existing && !existing.isDisposed()) {
            existing.reveal(viewColumn, preserveFocus);
            return existing;
        }
        const panel = vscode.window.createWebviewPanel("mypaGoals", "Goals", { viewColumn, preserveFocus }, {
            enableScripts: true,
            localResourceRoots: [context.extensionUri],
            retainContextWhenHidden: true,
        });
        const created = new GoalsPanel(panel, context.extensionUri);
        GoalsPanel.currentPanel = created;
        return created;
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
    isDisposed() {
        return this.disposed;
    }
    reveal(viewColumn, preserveFocus = false) {
        if (this.disposed)
            return;
        this.panel.reveal(viewColumn, preserveFocus);
    }
    dispose() {
        if (this.disposed)
            return;
        this.panel.dispose();
        this.disposed = true;
    }
    renderHtml(webview, _extensionUri) {
        const nonce = getNonce();
        const styleUri = webview.asWebviewUri(vscode.Uri.joinPath(_extensionUri, "media", "proof-state-renderer.css"));
        const scriptUri = webview.asWebviewUri(vscode.Uri.joinPath(_extensionUri, "media", "proof-state-renderer.js"));
        const csp = [
            `default-src 'none'`,
            `img-src ${webview.cspSource} https: data:`,
            `style-src ${webview.cspSource} 'unsafe-inline'`,
            `script-src 'nonce-${nonce}' ${webview.cspSource}`,
        ].join("; ");
        return /* html */ `<!doctype html>
<html>
  <head>
    <meta charset="utf-8" />
    <meta http-equiv="Content-Security-Policy" content="${csp}" />
    <meta name="viewport" content="width=device-width, initial-scale=1.0" />
    <title>Goals</title>
    <link rel="stylesheet" href="${styleUri}" />
  </head>
  <body>
    <div class="header">
      <div class="title">Goals</div>
      <div class="meta" id="meta"></div>
    </div>

    <div id="root" class="empty">No proof state.</div>

    <script nonce="${nonce}" src="${scriptUri}"></script>
    <script nonce="${nonce}">
      const root = document.getElementById("root");
      const meta = document.getElementById("meta");

      window.addEventListener("message", (event) => {
        const msg = event.data || {};
        if (msg.type === "setState") window.mypaProofStateRenderer.renderProofState(root, meta, msg.state);
        if (msg.type === "clear") {
          window.mypaProofStateRenderer.clearProofState(root, meta);
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