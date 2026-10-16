#!/usr/bin/env node
/*
 * Reads every exercise in ../exercises/*.hl, reports format errors and
 * warnings, and runs the same tests as the "Check" button of the website.
 *
 * Usage:
 *   node tools/check-exercises.js              check every exercise
 *   node tools/check-exercises.js swap.hl      check some files
 *   node tools/check-exercises.js -v           also list the passing tests
 *
 * The exit code is 1 when an exercise has an error or a failing test.
 */
'use strict';
const fs = require('fs');
const path = require('path');
const vm = require('vm');

const root = path.resolve(__dirname, '..');
const ctx = { console };
ctx.globalThis = ctx;
vm.createContext(ctx);
for (const f of ['js/logic.js', 'js/format.js', 'js/checker.js']) {
  vm.runInContext(fs.readFileSync(path.join(root, f), 'utf8'), ctx, { filename: f });
}
const HL = ctx.HL;

const args = process.argv.slice(2);
const verbose = args.includes('-v');
const names = args.filter((a) => !a.startsWith('-'));
const dir = path.join(root, 'exercises');
const files = names.length ? names.map((n) => path.basename(n)) : fs.readdirSync(dir).filter((f) => f.endsWith('.hl')).sort();

const stateText = (env) => Object.entries(env).map(([k, v]) => k + ' = ' + HL.valueText(v)).join(', ');

let bad = 0;
const ids = new Map();
for (const file of files) {
  const text = fs.readFileSync(path.join(dir, file), 'utf8');
  const ex = HL.parseExercise(text, file);
  const problems = [];
  ex.errors.forEach((e) => problems.push('  ERROR   line ' + e.line + ': ' + e.msg));
  ex.warnings.forEach((w) => problems.push('  warning line ' + w.line + ': ' + w.msg));
  if (ex.id) {
    if (ids.has(ex.id)) problems.push('  ERROR   the id "' + ex.id + '" is also used by ' + ids.get(ex.id));
    ids.set(ex.id, file);
  }
  const results = HL.Checker.checkExercise(ex);
  let pass = 0, fail = 0, other = 0;
  const lines = [];
  for (const r of results) {
    if (r.ok === true) pass++;
    else if (r.ok === false) fail++;
    else other++;
    const tag = r.ok === true ? 'pass   ' : r.ok === false ? 'FAIL   ' : r.status === 'vacuous' ? 'vacuous' : r.status === 'expected' ? 'expected' : 'skipped';
    if (r.ok === true && !verbose) continue;
    let msg = '  ' + tag + ' [' + r.group + '] ' + r.item;
    if (r.expect === 'fails' && r.ok === false) msg += ' (expected to fail, but no counterexample was found)';
    if (r.reason) msg += '\n            ' + r.reason;
    if (r.cex) msg += '\n            state: ' + stateText(r.cex);
    if (r.final) msg += '\n            final: ' + stateText(r.final);
    if (r.values) msg += '\n            values: ' + r.values.map(HL.valueText).join(' vs ');
    lines.push(msg);
  }
  const hasError = ex.errors.length > 0 || fail > 0;
  if (hasError) bad++;
  console.log((hasError ? '✗ ' : '✓ ') + file + '  (' + (ex.title || 'no title') + ')  ' + pass + ' passed, ' + fail + ' failed, ' + other + ' not conclusive');
  problems.forEach((p) => console.log(p));
  lines.forEach((l) => console.log(l));
}
console.log('\n' + files.length + ' exercise(s), ' + bad + ' with errors or failing tests.');
process.exit(bad ? 1 : 0);
