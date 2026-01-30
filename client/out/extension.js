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
exports.activate = activate;
exports.deactivate = deactivate;
// client/src/extension.ts
const vscode = __importStar(require("vscode"));
const net = __importStar(require("net"));
const GoalsPanel_1 = require("./GoalsPanel");
let goalsPanel;
let tcpServer;
function ensureGoalsPanel(context) {
    if (!goalsPanel) {
        goalsPanel = GoalsPanel_1.GoalsPanel.createOrShow(context, vscode.ViewColumn.Beside);
    }
    else {
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
function startTcpStateServer(context, port = 17171) {
    tcpServer = net.createServer((socket) => {
        socket.setEncoding("utf8");
        let buffer = "";
        socket.on("data", (chunk) => {
            buffer += chunk;
            while (true) {
                const idx = buffer.indexOf("\n");
                if (idx < 0)
                    break;
                const line = buffer.slice(0, idx).trim();
                buffer = buffer.slice(idx + 1);
                if (!line)
                    continue;
                try {
                    const state = JSON.parse(line);
                    ensureGoalsPanel(context).setProofState(state);
                }
                catch (e) {
                    vscode.window.showErrorMessage(`MyPA: invalid JSON proof state: ${e?.message ?? String(e)}`);
                }
            }
        });
        socket.on("error", (err) => {
            vscode.window.showErrorMessage(`MyPA: TCP socket error: ${String(err?.message ?? err)}`);
        });
    });
    tcpServer.on("error", (err) => {
        vscode.window.showErrorMessage(`MyPA: TCP server error (port ${port}): ${err?.message ?? String(err)}`);
    });
    tcpServer.listen(port, "127.0.0.1", () => {
        vscode.window.showInformationMessage(`MyPA: listening on 127.0.0.1:${port}`);
        console.log(`MyPA: listening on 127.0.0.1:${port}`);
    });
    context.subscriptions.push({
        dispose() {
            try {
                tcpServer?.close();
            }
            finally {
                tcpServer = undefined;
            }
        },
    });
}
function activate(context) {
    // Command: show goals panel
    context.subscriptions.push(vscode.commands.registerCommand("mypa.showGoals", () => {
        ensureGoalsPanel(context);
    }));
    // Start terminal -> VS Code proof state bridge
    startTcpStateServer(context, 17171);
}
function deactivate() {
    try {
        tcpServer?.close();
    }
    finally {
        tcpServer = undefined;
    }
    goalsPanel?.dispose();
    goalsPanel = undefined;
}
//# sourceMappingURL=extension.js.map