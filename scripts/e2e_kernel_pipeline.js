#!/usr/bin/env node
const fs = require('fs');
const path = require('path');
const cp = require('child_process');

const repoRoot = path.resolve(__dirname, '..');
const parser = require(path.join(repoRoot, 'lsp_server/out/documentParser.js'));

const filePath = path.join(repoRoot, 'demo/e2e_smoke.mypa');
const kernelPath = process.env.PROVER_KERNEL_PATH || path.join(repoRoot, 'kernel/build/mypa-kernel');
const uri = `file://${filePath}`;

function fail(msg) {
  console.error(`FAIL: ${msg}`);
  process.exit(1);
}

function scopedText(fullText, line, character) {
  const lines = fullText.split(/\r?\n/);
  const linePrefix = lines.slice(0, line).join('\n');
  const current = lines[line] || '';
  const prefix = `${line > 0 ? linePrefix + '\n' : ''}${current.slice(0, character)}`;
  const atLineEnd = character >= current.length;
  if (atLineEnd) return prefix;
  const lastNl = prefix.lastIndexOf('\n');
  if (lastNl === -1) return '';
  return prefix.slice(0, lastNl + 1);
}

function checkAt(fullText, line, character) {
  const scoped = scopedText(fullText, line, character);
  const ir = parser.parseDocumentToIR(uri, 1, scoped);
  const request = JSON.stringify({
    jsonrpc: '2.0',
    id: 'e2e',
    method: 'checkDocument',
    params: { document: ir },
  }) + '\n';

  const result = cp.spawnSync(kernelPath, { input: request, encoding: 'utf8', timeout: 5000 });
  const hasUsableOutput = result.status === 0 && typeof result.stdout === 'string';
  if (result.error && !hasUsableOutput) {
    fail(`kernel execution failed at ${kernelPath}: ${result.error.message}`);
  }
  if (typeof result.status === 'number' && result.status !== 0) {
    fail(`kernel exited with status ${result.status}`);
  }
  const stdout = result.stdout ?? '';

  let response;
  try {
    response = JSON.parse(stdout);
  } catch (err) {
    fail(`invalid kernel JSON response: ${err.message}`);
  }

  if (response.error) {
    fail(`kernel rpc error: ${response.error.message || 'unknown'}`);
  }
  return response.result;
}

if (!fs.existsSync(kernelPath)) {
  fail(`kernel binary missing: ${kernelPath}`);
}

const text = fs.readFileSync(filePath, 'utf8');

const afterGoal = checkAt(text, 2, 'goal a'.length);
if (afterGoal.diagnostics.length) {
  fail(`unexpected diagnostics after goal: ${afterGoal.diagnostics.map((d) => d.message).join(' | ')}`);
}
if (afterGoal.goals.length < 1) {
  fail('expected at least one goal after `goal a` line');
}

const afterInit = checkAt(text, 3, 'init h'.length);
if (afterInit.diagnostics.length) {
  fail(`unexpected diagnostics after init: ${afterInit.diagnostics.map((d) => d.message).join(' | ')}`);
}
if (afterInit.goals.length !== 0) {
  fail('expected zero goals after `init h`');
}

console.log('PASS: kernel pipeline e2e checks succeeded');
