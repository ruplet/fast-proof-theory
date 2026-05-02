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

export type DisplaySection = {
  title: string;
  body: string[];
};

export type ProofDisplay = {
  title: string;
  status: string;
  sections: DisplaySection[];
};

export type ProofState = {
  goals: Goal[];
  display?: ProofDisplay;
  tone?: "normal" | "error";
};

type WebviewMsg =
  | { type: "setState"; state: ProofState }
  | { type: "clear" };

export class GoalsPanel implements vscode.Disposable {
  private static currentPanel: GoalsPanel | undefined;
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
      if (GoalsPanel.currentPanel === this) {
        GoalsPanel.currentPanel = undefined;
      }
    });
  }

  /** Create (or reveal) a Goals panel. */
  static createOrShow(
    context: vscode.ExtensionContext,
    viewColumn: vscode.ViewColumn = vscode.ViewColumn.Beside,
    preserveFocus = false
  ): GoalsPanel {
    const existing = GoalsPanel.currentPanel;
    if (existing && !existing.isDisposed()) {
      existing.reveal(viewColumn, preserveFocus);
      return existing;
    }

    const panel = vscode.window.createWebviewPanel(
      "mypaGoals",
      "Goals",
      { viewColumn, preserveFocus },
      {
        enableScripts: true,
        localResourceRoots: [context.extensionUri],
        retainContextWhenHidden: true,
      }
    );

    const created = new GoalsPanel(panel, context.extensionUri);
    GoalsPanel.currentPanel = created;
    return created;
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

  isDisposed(): boolean {
    return this.disposed;
  }

  reveal(viewColumn?: vscode.ViewColumn, preserveFocus = false) {
    if (this.disposed) return;
    this.panel.reveal(viewColumn, preserveFocus);
  }

  dispose() {
    if (this.disposed) return;
    this.panel.dispose();
    this.disposed = true;
  }

  private renderHtml(webview: vscode.Webview, _extensionUri: vscode.Uri): string {
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

function getNonce(): string {
  const chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
  let out = "";
  for (let i = 0; i < 32; i++) out += chars.charAt(Math.floor(Math.random() * chars.length));
  return out;
}
