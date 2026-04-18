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
      body { font-family: var(--vscode-font-family); font-size: 13px; line-height: 1.45; padding: 10px; }
      .header { display:flex; align-items:baseline; justify-content:space-between; margin-bottom:10px; gap: 12px; }
      .title { font-weight: 600; font-size: 14px; }
      .meta { opacity: 0.7; }
      .goal { border: 1px solid var(--vscode-editorWidget-border); border-radius: 6px; padding: 10px; margin-bottom: 10px; }
      .goalError { border-color: var(--vscode-inputValidation-errorBorder); box-shadow: inset 0 0 0 1px color-mix(in srgb, var(--vscode-inputValidation-errorBorder) 40%, transparent); }
      .goalId { opacity: 0.8; margin-bottom: 6px; font-size: 12px; }
      .errorLabel { display: inline-block; margin-bottom: 8px; padding: 2px 8px; border-radius: 999px; border: 1px solid var(--vscode-inputValidation-errorBorder); background: color-mix(in srgb, var(--vscode-inputValidation-errorBackground) 88%, transparent); color: var(--vscode-inputValidation-errorForeground); font-size: 11px; font-weight: 700; letter-spacing: 0.02em; text-transform: uppercase; }
      .sectionTitle { font-weight: 600; margin: 8px 0 6px; }
      .hyp { font-family: var(--vscode-editor-font-family); font-size: 12px; line-height: 1.5; white-space: pre-wrap; }
      .target { font-family: var(--vscode-editor-font-family); font-size: 12px; line-height: 1.5; white-space: pre-wrap; padding-top: 4px; }
      .formula { font-family: var(--vscode-editor-font-family); white-space: pre-wrap; word-break: break-word; }
      .paren-0 { color: #d19a66; }
      .paren-1 { color: #61afef; }
      .paren-2 { color: #98c379; }
      .paren-3 { color: #e06c75; }
      .paren-4 { color: #c678dd; }
      .paren-5 { color: #56b6c2; }
      .op { color: var(--vscode-symbolIcon-operatorForeground, #e5c07b); font-weight: 600; }
      .statusError { margin-top: 6px; padding: 8px 10px; border-radius: 6px; border: 1px solid var(--vscode-inputValidation-errorBorder); background: color-mix(in srgb, var(--vscode-inputValidation-errorBackground) 75%, transparent); color: var(--vscode-inputValidation-errorForeground); font-weight: 600; }
      .sequent { display: grid; grid-template-columns: minmax(0, 1fr) auto minmax(0, 1fr); gap: 10px; align-items: start; margin-top: 8px; }
      .sequentSide { min-width: 0; }
      .turnstile { font-size: 18px; line-height: 1.4; opacity: 0.85; padding-top: 24px; }
      .empty { opacity: 0.7; font-style: italic; padding: 8px 0; }
      ul { margin: 0; padding-left: 18px; }
      li { margin: 3px 0; }
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
      /** @typedef {{title: string, status: string, sections: {title: string, body: string[]}[]}} ProofDisplay */
      /** @typedef {{goals: Goal[], display?: ProofDisplay, tone?: "normal"|"error"}} ProofState */

      const root = document.getElementById("root");
      const meta = document.getElementById("meta");

      function esc(s) {
        return String(s).replace(/[&<>"']/g, c => ({
          "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;"
        }[c]));
      }

      function renderFormulaHtml(input) {
        const text = String(input ?? "");
        let depth = 0;
        let out = "";
        const operatorChars = new Set(["⊗", "⊕", "⊸", "&", "⅋", "!", "?", "⊤", "⊥"]);
        for (const ch of text) {
          if (ch === "(") {
            const cls = "paren-" + (depth % 6);
            out += "<span class='" + cls + "'>(</span>";
            depth += 1;
            continue;
          }
          if (ch === ")") {
            depth = Math.max(depth - 1, 0);
            const cls = "paren-" + (depth % 6);
            out += "<span class='" + cls + "'>)</span>";
            continue;
          }
          if (operatorChars.has(ch)) {
            out += "<span class='op'>" + esc(ch) + "</span>";
            continue;
          }
          out += esc(ch);
        }
        return "<span class='formula'>" + out + "</span>";
      }

      /** @param {ProofState} state */
      function render(state) {
        const goals = (state && state.goals) ? state.goals : [];
        const display = state && state.display ? state.display : null;
        const tone = state && state.tone ? state.tone : "normal";
        const sections = display && Array.isArray(display.sections) ? display.sections : [];
        const rulesSection = sections.find(section => section.title === "Rules");
        const profileSection = sections.find(section => section.title === "Profile");
        const calculusSection = sections.find(section => section.title === "Calculus");
        const logicLabel = rulesSection && Array.isArray(rulesSection.body) && rulesSection.body.length
          ? String(rulesSection.body[0])
          : profileSection && Array.isArray(profileSection.body) && profileSection.body.length
          ? String(profileSection.body[0])
          : "";
        const calculusLabel = calculusSection && Array.isArray(calculusSection.body) && calculusSection.body.length
          ? String(calculusSection.body[0])
          : "";
        const isSequent = /sequent|gentzen/i.test(calculusLabel);
        const countLabel = goals.length
          ? (goals.length + " " + (isSequent ? (goals.length === 1 ? "sequent" : "sequents") : (goals.length === 1 ? "goal" : "goals")))
          : "";
        meta.textContent = [countLabel, calculusLabel].filter(Boolean).join(" · ");
        const visibleSections = sections.filter(section => !["Profile", "Rules", "Calculus", "Language", "Goals"].includes(section.title));
        const statusClass = tone === "error" ? "statusError" : "target";
        const statusHtml = display && tone === "error"
          ? "<div class='" + statusClass + "'>" + esc(display.status) + "</div>"
          : "";
        const hasMeaningfulDisplay = !!display && (
          tone === "error" ||
          !!display.title ||
          !!display.status ||
          visibleSections.length > 0
        );

        if (!goals.length) {
          root.className = hasMeaningfulDisplay ? "" : "empty";
          root.innerHTML = hasMeaningfulDisplay
            ? "<div class='goal " + (tone === "error" ? "goalError" : "") + "'>"
              + (tone === "error" ? "<div class='errorLabel'>Error</div>" : "")
              + (display.title ? "<div class='goalId'><b>" + esc(display.title) + "</b></div>" : "")
              + statusHtml
              + visibleSections.map(section =>
                  "<div class='sectionTitle'>" + esc(section.title) + "</div>"
                  + "<ul>" + (section.body || []).map(item => "<li class='hyp'>" + renderFormulaHtml(item) + "</li>").join("") + "</ul>"
                ).join("")
              + "</div>"
            : "No proof state.";
          return;
        }

        root.className = "";
        const showDisplayCard = !!display && (tone === "error" || visibleSections.length > 0);
        const displayHtml = showDisplayCard
          ? \`
            <div class="goal \${tone === "error" ? "goalError" : ""}">
              \${tone === "error" ? '<div class="errorLabel">Error</div>' : ""}
              \${display && display.title ? \`<div class="goalId"><b>\${esc(display.title)}</b></div>\` : ""}
              \${tone === "error" ? \`<div class="\${statusClass}">\${esc(display.status)}</div>\` : ""}
              \${visibleSections.map(section => \`
                <div class="sectionTitle">\${esc(section.title)}</div>
                <ul>\${(section.body || []).map(item => "<li class='hyp'>" + renderFormulaHtml(item) + "</li>").join("")}</ul>
              \`).join("")}
            </div>
          \`
          : "";
        root.innerHTML = displayHtml + goals.map((g, i) => {
          const hyps = g.hypotheses ?? [];
          const leftTitle = isSequent ? "Left" : "Hypotheses";
          const rightTitle = isSequent ? "Right" : "Goal";
          const hypsHtml = hyps.length
            ? "<ul>" + hyps.map(h => "<li class='hyp'><code>" + esc(h.name) + "</code> : " + renderFormulaHtml(h.type) + "</li>").join("") + "</ul>"
            : "<div class='empty'>" + (isSequent ? "Empty antecedent." : "No hypotheses.") + "</div>";
          const label = isSequent
            ? ("Sequent " + (i + 1))
            : (g.id ? esc(g.id) : ("Goal " + (i + 1)));

          return \`
            <div class="goal">
              <div class="goalId"><b>\${label}</b></div>
              \${isSequent
                ? \`<div class="sequent">
                    <div class="sequentSide">
                      <div class="sectionTitle">\${leftTitle}</div>
                      \${hypsHtml}
                    </div>
                    <div class="turnstile">⊢</div>
                    <div class="sequentSide">
                      <div class="sectionTitle">\${rightTitle}</div>
                      <div class="target">\${renderFormulaHtml(g.target ?? "")}</div>
                    </div>
                  </div>\`
                : \`<div class="sectionTitle">\${leftTitle}</div>
                    \${hypsHtml}
                    <div class="sectionTitle">\${rightTitle}</div>
                    <div class="target">\${renderFormulaHtml(g.target ?? "")}</div>\`}
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
