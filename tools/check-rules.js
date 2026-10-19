#!/usr/bin/env node
/*
 * Checks the interactive examples of the Rules page (js/rule-examples.js):
 *   - every formula and triple in the steps can be read;
 *   - the flag "valid" of each example agrees with running the program on
 *     sample states (examples with valid: null are not run).
 *
 * Usage: node tools/check-rules.js
 */
'use strict';
const fs = require('fs');
const path = require('path');
const vm = require('vm');

const root = path.resolve(__dirname, '..');
const ctx = { console };
ctx.globalThis = ctx;
vm.createContext(ctx);
for (const f of ['js/logic.js', 'js/format.js', 'js/checker.js', 'js/content.js', 'js/rule-examples.js']) {
  vm.runInContext(fs.readFileSync(path.join(root, f), 'utf8'), ctx, { filename: f });
}
const HL = ctx.HL;

// The pieces of a text that the site renders as formulas.
function formulas(text) {
  const out = [];
  for (const line of text.split('\n')) {
    const t = line.trim();
    if (t.startsWith('>> ')) {
      const body = t.slice(3);
      if (/\s---\s/.test(body)) {
        const [prem, concl] = body.split(/\s---\s/);
        prem.split(/\s{3,}/).map((x) => x.trim()).filter(Boolean).forEach((x) => out.push(x));
        out.push(concl.trim());
      } else out.push(body);
      continue;
    }
    const re = /\$([^$]+)\$/g;
    let m;
    while ((m = re.exec(t))) {
      let f = m[1].trim();
      if (f.startsWith('\\{') && f.endsWith('\\}')) f = f.slice(2, -2);
      out.push(f);
    }
  }
  return out;
}

let bad = 0;
const ids = new Set(HL.RULES.map((r) => r.id));
for (const id of Object.keys(HL.RULE_EXAMPLES)) {
  if (!ids.has(id)) { console.log('✗ unknown rule ' + id); bad++; }
}
for (const rule of HL.RULES) {
  const list = HL.RULE_EXAMPLES[rule.id] || [];
  if (!list.length) { console.log('✗ ' + rule.id + ': no example'); bad++; }
  for (const ex of list) {
    const problems = [];
    // Formulas that use the placeholder names of the rule schemas (Q, E, I)
    // only need to be readable.
    for (const f of [ex.goal].concat(...ex.steps.map(formulas))) {
      const r = HL.renderLine(f);
      if (!r.ok) problems.push('cannot read "' + f + '": ' + r.error.message);
    }
    let run = 'not run';
    if (ex.valid !== null) {
      const t = HL.parseTriple(ex.goal);
      const r = HL.Checker.checkTriple(t.pre, t.prog, t.post, {});
      const found = r.status === 'pass' ? true : r.status === 'fail' ? false : null;
      run = r.status + (r.cex ? ' at ' + JSON.stringify(r.cex) : '');
      if (found !== ex.valid) problems.push('valid is ' + ex.valid + ' but the test gives ' + run);
    }
    if (problems.length) bad++;
    console.log((problems.length ? '✗ ' : '✓ ') + rule.id + ' / ' + ex.title + ' (' + (ex.derived ? 'green' : 'red') + ', run: ' + run + ')');
    problems.forEach((p) => console.log('    ' + p));
  }
}
console.log(bad ? '\n' + bad + ' problem(s).' : '\nAll examples are consistent.');
process.exit(bad ? 1 : 0);
