"use strict";

const fs = require("fs");
const path = require("path");
const { extractDocument, checkDocument } = require("./index");

function usage() {
  return [
    "usage:",
    "  node proofAssistant/cli.js verify <input.mypa>",
    "  node proofAssistant/cli.js extract <input.mypa> <theoremName> -o <output.lean>",
  ].join("\n");
}

function main(argv) {
  if (argv[0] === "verify" && argv.length === 2) {
    const input = argv[1];
    const text = fs.readFileSync(input, "utf8");
    const result = checkDocument({ uri: input, version: 1, text });
    if (result.diagnostics.length === 0) {
      process.stdout.write("OK\n");
      process.exit(0);
    }
    for (const d of result.diagnostics) {
      process.stdout.write(`${d.range.start.line + 1}: ${d.code}: ${d.message}\n`);
    }
    process.exit(1);
  }

  if (argv[0] === "extract" && argv.length === 5 && argv[3] === "-o") {
    const input = argv[1];
    const theoremName = argv[2];
    const output = argv[4];
    const text = fs.readFileSync(input, "utf8");
    const result = extractDocument(text, theoremName);
    if (!result.ok) {
      console.error(result.error);
      process.exit(1);
    }
    fs.mkdirSync(path.dirname(output), { recursive: true });
    fs.writeFileSync(output, result.source, "utf8");
    process.stdout.write(`Wrote ${output}\n`);
    process.exit(0);
  }

  console.error(usage());
  process.exit(2);
}

if (require.main === module) {
  main(process.argv.slice(2));
}
