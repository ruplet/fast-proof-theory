import { copyFileSync, mkdirSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const scriptDir = dirname(fileURLToPath(import.meta.url));
const proofAssistantDir = resolve(scriptDir, "..");
const targetDir = resolve(proofAssistantDir, "extensionVSCode", "proofStateUi");

mkdirSync(targetDir, { recursive: true });

for (const file of ["proof-state-renderer.css", "proof-state-renderer.js"]) {
  copyFileSync(resolve(proofAssistantDir, "proofStateUi", file), resolve(targetDir, file));
}
