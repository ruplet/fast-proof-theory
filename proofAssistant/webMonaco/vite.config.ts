import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";
import path from "node:path";

export default defineConfig({
  base: "./",
  plugins: [react()],
  resolve: {
    alias: {
      "vscode-jsonrpc/browser": path.resolve(__dirname, "../../node_modules/vscode-jsonrpc/browser.js"),
      "vscode-jsonrpc": path.resolve(__dirname, "../../node_modules/vscode-jsonrpc"),
      "vscode-languageserver/browser": path.resolve(__dirname, "../../node_modules/vscode-languageserver/browser.js"),
      "vscode-languageserver": path.resolve(__dirname, "../../node_modules/vscode-languageserver"),
      "vscode-languageserver-protocol/browser": path.resolve(
        __dirname,
        "../../node_modules/vscode-languageserver-protocol/browser.js"
      ),
      "vscode-languageserver-protocol": path.resolve(__dirname, "../../node_modules/vscode-languageserver-protocol"),
    },
  },
  server: {
    fs: {
      allow: [path.resolve(__dirname, ".."), path.resolve(__dirname, "../..")],
    },
  },
});
