#!/usr/bin/env node
/*
 * Proves the claims of every exercise and rule example of the test site
 * (test/exercises/*.hl and test/exercises/rules/*.hl) with the SMT solver
 * Z3, using the same code as the website (test/js/smt.js, ivl.js,
 * prover.js).
 *
 * Setup, once:   cd tools && npm install
 * Usage:         node tools/prove-exercises.js [-v] [file.hl ...]
 *
 * For each claim the result is: proved, refuted (with a counterexample
 * that the evaluator of the site confirms), expected (a refuted check in
 * an exercise that says the triple is not valid), not decided, or skipped.
 * The exit code is 1 when a claim gets the wrong answer.
 */
'use strict';
const fs = require('fs');
const path = require('path');
const vm = require('vm');
const { init } = require('z3-solver');

const site = path.resolve(__dirname, '..', 'test');
const ctx = { console };
ctx.globalThis = ctx;
vm.createContext(ctx);
for (const f of ['logic.js', 'format.js', 'checker.js', 'smt.js', 'ivl.js', 'prover.js']) {
  vm.runInContext(fs.readFileSync(path.join(site, 'js', f), 'utf8'), ctx, { filename: f });
}
const HL = ctx.HL;

const args = process.argv.slice(2);
const verbose = args.includes('-v');
const showQuery = args.includes('-q');
const names = args.filter((a) => !a.startsWith('-'));
const dir = path.join(site, 'exercises');
const list = (sub) => fs.readdirSync(path.join(dir, sub)).filter((f) => f.endsWith('.hl')).sort().map((f) => path.join(sub, f));
const files = names.length ? names : list('.').concat(list('rules'));

(async () => {
  const { Z3 } = await init();
  const z3ctx = Z3.mk_context(Z3.mk_config());
  const solver = { run: (text) => Z3.eval_smtlib2_string(z3ctx, text) };
  const totals = { proved: 0, refuted: 0, expected: 0, unknown: 0, skip: 0, error: 0, wrong: 0 };
  const t0 = Date.now();
  for (const file of files) {
    const ex = HL.parseExercise(fs.readFileSync(path.join(dir, file), 'utf8'), file);
    const results = await HL.Prover.proveExercise(ex, solver, { timeout: 4000 });
    const count = {};
    const lines = [];
    for (const r of results) {
      count[r.status] = (count[r.status] || 0) + 1;
      totals[r.status] = (totals[r.status] || 0) + 1;
      if (r.ok === false) totals.wrong++;
      const show = verbose || r.ok === false || r.status === 'unknown' || r.status === 'error' || (r.status === 'refuted' && r.confirmed !== true);
      if (!show) continue;
      let msg = '  ' + (r.ok === false ? 'WRONG   ' : r.status.padEnd(8)) + ' [' + r.group + '] ' + r.item;
      if (r.reason) msg += '\n            ' + r.reason;
      if (showQuery && r.query && r.status !== 'proved') msg += '\n' + r.query.split('\n').map((l) => '            | ' + l).join('\n');
      if (r.state) msg += '\n            state: ' + JSON.stringify(r.state) + (r.confirmed === false ? '  (the evaluator says the claim holds here: prover error)' : r.confirmed == null ? '  (not confirmed: a value is undefined)' : '');
      lines.push(msg);
    }
    const bad = results.some((r) => r.ok === false);
    console.log((bad ? '✗ ' : '✓ ') + file + '  ' + Object.entries(count).map(([k, v]) => v + ' ' + k).join(', '));
    lines.forEach((l) => console.log(l));
  }
  console.log('\n' + Object.entries(totals).map(([k, v]) => v + ' ' + k).join(', ') + '  (' + ((Date.now() - t0) / 1000).toFixed(1) + ' s)');
  process.exit(totals.wrong ? 1 : 0);
})();
