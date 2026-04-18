const fs = require("fs");
const path = require("path");
const { spawnSync } = require("child_process");

const rootDir = path.resolve(__dirname, "..");
const inputPath = path.join(__dirname, "demo", "tutorial.md");
const distDir = path.join(rootDir, "build", "myst");
const tempDir = path.join(rootDir, "build", "tmp", "myst");
const exporterPath = path.join(rootDir, ".lake", "build", "bin", "mypa-export-cache");

function escapeHtml(value) {
  return String(value).replace(/[&<>"]/g, (char) => ({
    "&": "&amp;",
    "<": "&lt;",
    ">": "&gt;",
    '"': "&quot;",
  }[char]));
}

function slugify(value) {
  return String(value)
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, "-")
    .replace(/^-+|-+$/g, "") || "demo";
}

function renderInline(text) {
  return escapeHtml(text).replace(/`([^`]+)`/g, "<code>$1</code>");
}

function renderJsonScript(payload) {
  return JSON.stringify(payload)
    .replace(/</g, "\\u003c")
    .replace(/<\/script/gi, "<\\/script");
}

function exportCache(title, source) {
  if (!fs.existsSync(exporterPath)) {
    throw new Error(
      "Missing cache exporter binary. Run `lake build mypa-export-cache` from the repo root first."
    );
  }

  fs.mkdirSync(tempDir, { recursive: true });
  const tempPath = path.join(tempDir, `${slugify(title)}.mypa`);
  fs.writeFileSync(tempPath, source);

  const result = spawnSync(exporterPath, ["--title", title, tempPath], {
    cwd: rootDir,
    encoding: "utf8",
    maxBuffer: 8 * 1024 * 1024,
  });
  fs.rmSync(tempPath, { force: true });

  if (result.status !== 0) {
    throw new Error(result.stderr || result.stdout || `mypa-export-cache exited with status ${result.status}`);
  }

  const payload = JSON.parse(result.stdout);
  if (Array.isArray(payload.documentDiagnostics) && payload.documentDiagnostics.length > 0) {
    const summary = payload.documentDiagnostics
      .map((diag) => `${diag.range.start.line + 1}:${diag.range.start.character + 1} ${diag.code} ${diag.message}`)
      .join("\n");
    throw new Error(`Tutorial block "${title}" is not verified:\n${summary}`);
  }
  return payload;
}

function renderMyPaBlock(title, source, index) {
  const payload = exportCache(title, source);
  const slug = `${String(index + 1).padStart(2, "0")}-${slugify(title)}`;
  const cachePath = path.join(distDir, "cache", `${slug}.json`);
  fs.writeFileSync(cachePath, JSON.stringify(payload, null, 2));

  return `
<section class="mypa-widget">
  <div class="mypa-widget-header">
    <h3>${escapeHtml(title)}</h3>
    <div class="mypa-demo-meta"></div>
  </div>
  <div class="mypa-workbench">
    <div class="mypa-editor-pane">
      <div class="mypa-pane-label">
        <span>Read-only MyPA source</span>
        <span class="mypa-cursor"></span>
      </div>
      <textarea class="mypa-editor" spellcheck="false" aria-label="${escapeHtml(title)} source"></textarea>
    </div>
    <div class="mypa-goals-pane">
      <div class="mypa-goals-header">
        <div class="mypa-goals-title">Proof state</div>
        <div class="mypa-goals-meta"></div>
      </div>
      <div class="mypa-goals-root empty">No proof state.</div>
    </div>
  </div>
  <script type="application/json">${renderJsonScript(payload)}</script>
</section>`;
}

function parseDocument(markdown) {
  const lines = markdown.replace(/\r\n/g, "\n").split("\n");
  const html = [];
  let paragraph = [];
  let listItems = [];
  let blockIndex = 0;
  let heroOpen = false;
  let heroLeadPending = false;

  function closeHeroIfOpen() {
    if (!heroOpen) {
      return;
    }
    html.push("</header>");
    heroOpen = false;
    heroLeadPending = false;
  }

  function flushParagraph() {
    if (!paragraph.length) {
      return;
    }
    const className = heroLeadPending ? ` class="lead"` : "";
    const rendered = `<p${className}>${renderInline(paragraph.join(" "))}</p>`;
    if (heroOpen) {
      html.push(rendered);
      html.push("</header>");
      heroOpen = false;
      heroLeadPending = false;
    } else {
      html.push(rendered);
    }
    paragraph = [];
  }

  function flushList() {
    if (!listItems.length) {
      return;
    }
    html.push(`<ul>${listItems.map((item) => `<li>${renderInline(item)}</li>`).join("")}</ul>`);
    listItems = [];
  }

  for (let i = 0; i < lines.length; i += 1) {
    const line = lines[i];

    if (line.startsWith(":::{mypa}")) {
      flushParagraph();
      flushList();
      closeHeroIfOpen();
      const title = line.slice(":::{mypa}".length).trim() || `Demo ${blockIndex + 1}`;
      const body = [];
      i += 1;
      while (i < lines.length && lines[i] !== ":::") {
        body.push(lines[i]);
        i += 1;
      }
      html.push(renderMyPaBlock(title, body.join("\n"), blockIndex));
      blockIndex += 1;
      continue;
    }

    if (!line.trim()) {
      flushParagraph();
      flushList();
      continue;
    }

    if (line.startsWith("# ")) {
      flushParagraph();
      flushList();
      closeHeroIfOpen();
      html.push(`<header class="hero"><div class="eyebrow">MyST Demo</div><h1>${renderInline(line.slice(2))}</h1>`);
      heroOpen = true;
      heroLeadPending = true;
      continue;
    }

    if (line.startsWith("## ")) {
      flushParagraph();
      flushList();
      closeHeroIfOpen();
      html.push(`<h2>${renderInline(line.slice(3))}</h2>`);
      continue;
    }

    if (line.startsWith("### ")) {
      flushParagraph();
      flushList();
      closeHeroIfOpen();
      html.push(`<h3>${renderInline(line.slice(4))}</h3>`);
      continue;
    }

    if (line.startsWith("- ")) {
      flushParagraph();
      listItems.push(line.slice(2).trim());
      continue;
    }

    if (line.startsWith(":::callout")) {
      flushParagraph();
      flushList();
      closeHeroIfOpen();
      const parts = [];
      i += 1;
      while (i < lines.length && lines[i] !== ":::") {
        parts.push(lines[i]);
        i += 1;
      }
      html.push(`<div class="mypa-callout"><p>${renderInline(parts.join(" "))}</p></div>`);
      continue;
    }

    paragraph.push(line.trim());
  }

  flushParagraph();
  flushList();
  closeHeroIfOpen();
  return html.join("\n");
}

function main() {
  const markdown = fs.readFileSync(inputPath, "utf8");
  fs.rmSync(distDir, { recursive: true, force: true });
  fs.mkdirSync(path.join(distDir, "cache"), { recursive: true });

  const article = parseDocument(markdown);
  fs.copyFileSync(path.join(rootDir, "client", "media", "proof-state-renderer.js"), path.join(distDir, "proof-state-renderer.js"));
  fs.copyFileSync(path.join(rootDir, "client", "media", "proof-state-renderer.css"), path.join(distDir, "proof-state-renderer.css"));
  fs.copyFileSync(path.join(__dirname, "runtime.js"), path.join(distDir, "runtime.js"));
  fs.copyFileSync(path.join(__dirname, "theme.css"), path.join(distDir, "theme.css"));

  const html = `<!doctype html>
<html lang="en">
  <head>
    <meta charset="utf-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1.0" />
    <title>Linear Logic with MyPA</title>
    <link rel="stylesheet" href="./theme.css" />
    <link rel="stylesheet" href="./proof-state-renderer.css" />
  </head>
  <body>
    <main class="page">
      <article class="content">
${article}
      </article>
    </main>
    <script src="./proof-state-renderer.js"></script>
    <script src="./runtime.js"></script>
  </body>
</html>`;

  fs.writeFileSync(path.join(distDir, "tutorial.html"), html);
  console.log(`Wrote ${path.join(distDir, "tutorial.html")}`);
}

main();
