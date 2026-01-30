// client/src/extension.ts
import * as vscode from "vscode";
import * as net from "net";
import { GoalsPanel, ProofState } from "./GoalsPanel";

let goalsPanel: GoalsPanel | undefined;
let tcpServer: net.Server | undefined;

function ensureGoalsPanel(context: vscode.ExtensionContext): GoalsPanel {
  if (!goalsPanel) {
    goalsPanel = GoalsPanel.createOrShow(context, vscode.ViewColumn.Beside);
  } else {
    goalsPanel.reveal(vscode.ViewColumn.Beside);
  }
  return goalsPanel;
}

/**
 * Starts a localhost TCP server that accepts newline-delimited JSON (NDJSON).
 * Each line must be a ProofState: { "goals": [ ... ] }
 *
 * Example:
 *   printf '%s\n' '{"goals":[{"id":"g1","hypotheses":[{"name":"h","type":"A -> B"}],"target":"B"}]}' | nc 127.0.0.1 17171
 */
function startTcpStateServer(context: vscode.ExtensionContext, port = 17171) {
  tcpServer = net.createServer((socket) => {
    socket.setEncoding("utf8");

    let buffer = "";

    socket.on("data", (chunk) => {
      buffer += chunk;

      while (true) {
        const idx = buffer.indexOf("\n");
        if (idx < 0) break;

        const line = buffer.slice(0, idx).trim();
        buffer = buffer.slice(idx + 1);

        if (!line) continue;

        try {
          const state = JSON.parse(line) as ProofState;
          ensureGoalsPanel(context).setProofState(state);
        } catch (e: any) {
          vscode.window.showErrorMessage(
            `MyPA: invalid JSON proof state: ${e?.message ?? String(e)}`
          );
        }
      }
    });

    socket.on("error", (err) => {
      vscode.window.showErrorMessage(
        `MyPA: TCP socket error: ${String((err as any)?.message ?? err)}`
      );
    });
  });

  tcpServer.on("error", (err: any) => {
    vscode.window.showErrorMessage(
      `MyPA: TCP server error (port ${port}): ${err?.message ?? String(err)}`
    );
  });

  tcpServer.listen(port, "127.0.0.1", () => {
    vscode.window.showInformationMessage(`MyPA: listening on 127.0.0.1:${port}`);
    console.log(`MyPA: listening on 127.0.0.1:${port}`);
  });

  context.subscriptions.push({
    dispose() {
      try {
        tcpServer?.close();
      } finally {
        tcpServer = undefined;
      }
    },
  });
}

export function activate(context: vscode.ExtensionContext) {
  // Command: show goals panel
  context.subscriptions.push(
    vscode.commands.registerCommand("mypa.showGoals", () => {
      ensureGoalsPanel(context);
    })
  );

  // Start terminal -> VS Code proof state bridge
  startTcpStateServer(context, 17171);
}

export function deactivate() {
  try {
    tcpServer?.close();
  } finally {
    tcpServer = undefined;
  }
  goalsPanel?.dispose();
  goalsPanel = undefined;
}
