/*
 * format.js
 *
 * Reads an exercise written in the ".hl" text format and turns it into an
 * object that the viewer and the checker use. The format is documented in
 * README.md and in the "Write an exercise" page of the website.
 *
 * In short, a file is a list of fields. A field starts at the beginning of
 * a line with "name:". Its value is the rest of that line, followed by the
 * indented lines below it. Steps start with "step:"; every field after a
 * "step:" line belongs to that step, until the next "step:".
 */
(function (root) {
  'use strict';
  const HL = (root.HL = root.HL || {});

  const EXERCISE_FIELDS = new Set(['id', 'title', 'topic', 'level', 'source', 'tags', 'task', 'pre', 'post',
    'program', 'verdict', 'summary', 'range', 'hint', 'example-of', 'derived', 'given', 'scheme']);
  const STEP_FIELDS = new Set(['step', 'part', 'rule', 'focus', 'set', 'text', 'note', 'calc', 'vc', 'why', 'status',
    'counterexample', 'instance', 'assume', 'result']);

  // The rules that a step may name. The names match the rules section.
  const RULES = ['SKIP', 'ASSIGN', 'CONSEQUENCE', 'SEQ', 'IF', 'WHILE', 'WHILE-CONSEQUENCE', 'WHILE-TOTAL',
    'ARRAY-READ', 'ARRAY-ASSIGN', 'WP', 'LOGIC'];
  HL.RULE_NAMES = RULES;

  // Order of the topics in the exercise list.
  HL.TOPIC_ORDER = ['Implications and triples', 'Skip and consequence', 'Assignment', 'Sequential composition',
    'Conditional', 'Loops', 'Loop invariants', 'Arrays'];

  function splitFields(text) {
    const lines = text.replace(/\r\n?/g, '\n').split('\n');
    const fields = [];
    let cur = null;
    const errors = [];
    lines.forEach((line, idx) => {
      const lineNo = idx + 1;
      if (/^#/.test(line)) return; // comment
      const m = line.match(/^([A-Za-z][A-Za-z0-9_-]*)\s*:(.*)$/);
      if (m) {
        cur = { key: m[1].toLowerCase(), inline: m[2].trim(), block: [], line: lineNo };
        fields.push(cur);
        return;
      }
      if (/^\s*$/.test(line)) {
        if (cur) cur.block.push({ text: '', line: lineNo });
        return;
      }
      if (/^\s/.test(line)) {
        if (!cur) {
          errors.push({ line: lineNo, msg: 'This indented line does not belong to any field' });
          return;
        }
        cur.block.push({ text: line, line: lineNo });
        return;
      }
      errors.push({ line: lineNo, msg: 'Expected "field: value" at the start of the line. Text that continues a field must be indented.' });
    });
    // Remove the common indentation and the trailing blank lines of blocks.
    for (const f of fields) {
      while (f.block.length && f.block[f.block.length - 1].text === '') f.block.pop();
      while (f.block.length && f.block[0].text === '') f.block.shift();
      let min = Infinity;
      for (const b of f.block) if (b.text.trim()) min = Math.min(min, b.text.match(/^\s*/)[0].length);
      if (min === Infinity) min = 0;
      f.block = f.block.map((b) => ({ text: b.text.slice(min), line: b.line }));
    }
    return { fields, errors };
  }

  // The full value of a field: the inline part and the block lines, with
  // the line number of each line.
  function valueLines(f) {
    const out = [];
    if (f.inline) out.push({ text: f.inline, line: f.line });
    return out.concat(f.block);
  }
  function valueText(f) {
    return valueLines(f).map((l) => l.text).join('\n');
  }

  function lineOfOffset(lines, offset) {
    // lines: [{text, line}] joined by '\n'
    let pos = 0;
    for (const l of lines) {
      if (offset <= pos + l.text.length) return l.line;
      pos += l.text.length + 1;
    }
    return lines.length ? lines[lines.length - 1].line : 0;
  }

  function parseExercise(text, fileName) {
    const { fields, errors } = splitFields(text);
    const warnings = [];
    const ex = {
      file: fileName || '', id: '', title: '', topic: '', level: 1, source: '', tags: [], task: '', hint: '',
      preSrc: '', postSrc: '', programSrc: '', verdict: '', summary: '', range: null,
      exampleOf: '', derived: null, given: [], scheme: null,
      steps: [], choices: [], errors, warnings
    };
    const err = (line, msg) => errors.push({ line, msg });
    const warn = (line, msg) => warnings.push({ line, msg });
    let step = null;
    let lastVc = null;
    // The proof can offer several choices (for example of invariant). The
    // steps after "choice:" belong to that choice. Without any "choice:",
    // all steps belong to one implicit choice.
    let branch = null;

    for (const f of fields) {
      const key = f.key;
      if (key === 'choice') {
        if (ex.steps.length && !ex.choices.length) {
          err(f.line, 'When the exercise has choices, every step must come after a "choice:" line');
        }
        branch = { title: f.inline || 'Choice ' + (ex.choices.length + 1), outcome: 'proves', steps: [], line: f.line };
        ex.choices.push(branch);
        step = null;
        lastVc = null;
        continue;
      }
      if (key === 'outcome') {
        const w = valueText(f).trim().toLowerCase();
        if (!branch || step) err(f.line, 'The field "outcome" must follow a "choice:" line, before its first step');
        else if (!['proves', 'fails'].includes(w)) err(f.line, 'The outcome must be "proves" or "fails"');
        else branch.outcome = w;
        continue;
      }
      if (key === 'step') {
        step = { title: f.inline || 'Step', line: f.line, part: '', rules: [], focus: [], items: [], sets: [], assume: null };
        if (f.block.length) step.items.push({ kind: 'text', text: f.block.map((b) => b.text).join('\n'), line: f.line });
        (branch ? branch.steps : ex.steps).push(step);
        lastVc = null;
        continue;
      }
      if (EXERCISE_FIELDS.has(key)) {
        if (step && !['verdict', 'summary'].includes(key)) {
          err(f.line, 'The field "' + key + '" belongs to the exercise, so it must appear before the first "step:"');
          continue;
        }
        const v = valueText(f);
        switch (key) {
          case 'id': ex.id = v.trim(); break;
          case 'title': ex.title = v.trim(); break;
          case 'topic': ex.topic = v.trim(); break;
          case 'level': ex.level = Math.max(1, Math.min(3, parseInt(v, 10) || 1)); break;
          case 'source': ex.source = v.trim(); break;
          case 'tags': ex.tags = v.split(',').map((t) => t.trim()).filter(Boolean); break;
          case 'task': ex.task = v; break;
          case 'hint': ex.hint = v; break;
          case 'pre': ex.preSrc = v.trim(); ex.preLine = f.line; ex.preLines = valueLines(f); break;
          case 'post': ex.postSrc = v.trim(); ex.postLine = f.line; ex.postLines = valueLines(f); break;
          case 'program': ex.programSrc = v; ex.programLine = f.line; ex.programLines = valueLines(f); break;
          case 'verdict': {
            const w = v.trim().toLowerCase();
            if (w !== 'valid' && w !== 'invalid') err(f.line, 'The verdict must be "valid" or "invalid"');
            ex.verdict = w;
            break;
          }
          case 'summary': ex.summary = v; break;
          case 'example-of': ex.exampleOf = v.trim().toUpperCase(); break;
          case 'derived': ex.derived = /^(true|yes)$/i.test(v.trim()); break;
          case 'given':
            // One "Label: value" per line, shown with the variables.
            valueLines(f).forEach((l) => {
              const m = l.text.match(/^([^:]+):\s*(.*)$/);
              if (m) ex.given.push([m[1].trim(), m[2].trim()]);
              else if (l.text.trim()) err(l.line, 'Write each given element as "Label: value"');
            });
            break;
          case 'scheme': ex.scheme = parseScheme(valueLines(f), f, err); break;
          case 'range': {
            const n = parseInt(v, 10);
            if (!(n >= 1 && n <= 20)) err(f.line, 'The range must be a number between 1 and 20');
            else ex.range = n;
            break;
          }
          default: break;
        }
        continue;
      }
      if (!STEP_FIELDS.has(key)) {
        err(f.line, 'Unknown field "' + key + '"');
        continue;
      }
      if (!step) {
        err(f.line, 'The field "' + key + '" belongs to a step, so it must appear after a "step:" line');
        continue;
      }
      const v = valueText(f);
      switch (key) {
        case 'part': step.part = v.trim(); break;
        case 'rule':
          v.split(/[,\s]+/).map((r) => r.trim().toUpperCase()).filter(Boolean).forEach((r) => {
            if (!RULES.includes(r)) warn(f.line, 'Unknown rule "' + r + '". The known rules are ' + RULES.join(', '));
            step.rules.push(r);
          });
          break;
        case 'focus':
          v.split(',').map((x) => x.trim()).filter(Boolean).forEach((x) => step.focus.push({ text: x, line: f.line }));
          break;
        case 'set': {
          const m = v.trim().match(/^([A-Za-z][A-Za-z0-9_]*'*)\s*(?::=|=)\s*([\s\S]*)$/);
          if (!m) {
            err(f.line, 'Write "set: NAME = formula", for example "set: R1 = x > 0"');
            break;
          }
          const item = { kind: 'set', name: m[1], src: m[2].trim(), line: f.line };
          try {
            item.f = HL.parseFormula(item.src);
          } catch (e) {
            err(f.line, 'In the formula of ' + m[1] + ': ' + e.message);
          }
          step.items.push(item);
          step.sets.push(item);
          break;
        }
        case 'text':
        case 'note':
        case 'result':
          step.items.push({ kind: key, text: v, line: f.line });
          break;
        case 'assume': {
          try {
            step.assume = HL.parseFormula(v);
            step.assumeSrc = v.trim();
            step.items.push({ kind: 'assume', src: v.trim(), f: step.assume, line: f.line });
          } catch (e) {
            err(f.line, 'In the assumption: ' + e.message);
          }
          break;
        }
        case 'calc':
          step.items.push(parseCalc(valueLines(f), f.line, warn));
          break;
        case 'instance':
          step.items.push(parseInstance(valueLines(f), f, warn));
          break;
        case 'vc': {
          const item = { kind: 'vc', src: v.trim(), line: f.line, why: '', status: 'holds', counterexample: null };
          try {
            item.node = HL.parseStatementLine(item.src);
          } catch (e) {
            warn(f.line, 'The verification condition could not be read, so it is shown as text and not checked: ' + e.message);
          }
          step.items.push(item);
          lastVc = item;
          break;
        }
        case 'why':
        case 'status':
        case 'counterexample':
          if (!lastVc) {
            err(f.line, 'The field "' + key + '" must follow a "vc:" field');
            break;
          }
          if (key === 'why') lastVc.why = v;
          if (key === 'status') {
            const w = v.trim().toLowerCase();
            if (!['holds', 'fails'].includes(w)) err(f.line, 'The status must be "holds" or "fails"');
            else lastVc.status = w;
          }
          if (key === 'counterexample') {
            try {
              lastVc.counterexample = parseState(v);
              lastVc.counterexampleSrc = v.trim();
            } catch (e) {
              err(f.line, 'Write the counterexample as "x = 1, y = -2, a = [4, 0, 9]"');
            }
          }
          break;
        default:
          break;
      }
    }

    // Required fields
    if (!ex.id) err(1, 'The field "id" is missing');
    else if (!/^[A-Za-z0-9][A-Za-z0-9_-]*$/.test(ex.id)) err(1, 'The id may only contain letters, digits, "-" and "_"');
    if (!ex.title) err(1, 'The field "title" is missing');
    if (!ex.preSrc) err(1, 'The field "pre" (the precondition) is missing');
    if (!ex.postSrc) err(1, 'The field "post" (the postcondition) is missing');
    if (!ex.programSrc.trim()) err(1, 'The field "program" is missing');
    if (!ex.choices.length) ex.choices.push({ title: '', outcome: 'proves', steps: ex.steps, line: 1 });
    ex.steps = ex.choices[0].steps;
    const allSteps = [].concat(...ex.choices.map((c) => c.steps));
    if (!allSteps.length) warn(1, 'The exercise has no steps');

    if (ex.preSrc) {
      try { ex.pre = HL.parseFormula(ex.preSrc); } catch (e) { err(ex.preLine, 'In the precondition: ' + e.message); }
    }
    if (ex.postSrc) {
      try { ex.post = HL.parseFormula(ex.postSrc); } catch (e) { err(ex.postLine, 'In the postcondition: ' + e.message); }
    }
    if (ex.programSrc.trim()) {
      try {
        ex.program = HL.parseProgram(ex.programSrc);
      } catch (e) {
        const line = e.pos != null ? lineOfOffset(ex.programLines, e.pos) : ex.programLine;
        err(line, 'In the program: ' + e.message);
      }
    }

    // Slots: assertions in the program that consist of a single name.
    ex.slotNames = [];
    if (ex.program) {
      HL.walkAsserts(ex.program, (a) => {
        if (a.slot && !ex.slotNames.includes(a.slot)) ex.slotNames.push(a.slot);
      });
      const setNames = new Set();
      allSteps.forEach((s) => s.sets.forEach((x) => setNames.add(x.name)));
      ex.slotNames.forEach((n) => {
        if (n !== 'P' && n !== 'Q' && !setNames.has(n)) {
          warn(ex.programLine, 'The assertion {' + n + '} in the program is never given a value with "set: ' + n + ' = ..."');
        }
      });
      // Resolve the focus of every step: statements, and assertion lines
      // given by the name of a slot (P, I, R1) or by their formula.
      const stmts = [];
      HL.walkStmts(ex.program, (s) => stmts.push(s));
      const asserts = [];
      HL.walkAsserts(ex.program, (a) => { a.aid = 'a' + asserts.length; asserts.push(a); });
      allSteps.forEach((s) => {
        s.focusIds = [];
        s.focusAsserts = [];
        s.focus.forEach((fc) => {
          const t = fc.text.trim();
          const bySlot = asserts.filter((a) => a.slot === t);
          if (bySlot.length) { s.focusAsserts.push(...bySlot.map((a) => a.aid)); return; }
          const ids = findStatements(stmts, t);
          if (ids.length) { s.focusIds.push(...ids); return; }
          const canon = HL.canonHead(t);
          const lit = asserts.filter((a) => HL.canonHead(a.src) === canon);
          if (lit.length) { s.focusAsserts.push(...lit.map((a) => a.aid)); return; }
          warn(fc.line, 'The focus "' + t + '" does not match any statement or assertion of the program');
        });
      });
    }
    ex.choices.forEach((c) => numberSteps(c.steps));
    if (!ex.topic) ex.topic = 'Other';
    return ex;
  }

  // Steps of the same part get the numbers n.1, n.2, ... ; a part with a
  // single step, or a step without part, gets the number n.
  function numberSteps(steps) {
    let n = 0;
    let j = 0;
    while (j < steps.length) {
      const part = steps[j].part;
      let k = j + 1;
      while (part && k < steps.length && steps[k].part === part) k++;
      n++;
      for (let i = j; i < k; i++) {
        steps[i].index = i + 1;
        steps[i].number = k - j > 1 ? n + '.' + (i - j + 1) : String(n);
      }
      j = k;
    }
  }
  HL.numberSteps = numberSteps;

  // scheme: the rule with the elements of the exercise. One premise per
  // line, "Part: premise", then a line of dashes and the conclusion. In the
  // premises, «X» stands for the current value of the assertion X, and
  // «formula : label» shows the formula with a label under it.
  function parseScheme(lines, f, err) {
    const premises = [];
    let conclusion = '';
    let afterBar = false;
    let name = f.inline && /^[A-Za-z-]+$/.test(f.inline.trim()) ? f.inline.trim().toUpperCase() : '';
    for (const l of name ? f.block : lines) {
      const t = l.text.trim();
      if (!t) continue;
      if (/^-{3,}$/.test(t)) { afterBar = true; continue; }
      if (afterBar) { conclusion = t; continue; }
      const m = t.match(/^([A-Z][A-Za-z ]*):\s+(.*)$/);
      premises.push(m ? { part: m[1].trim(), src: m[2], line: l.line } : { part: '', src: t, line: l.line });
    }
    if (!conclusion) err(f.line, 'The scheme has no conclusion. Put a line of dashes "---" before the conclusion.');
    return { name, premises, conclusion };
  }

  function findStatements(stmts, text) {
    const byLabel = stmts.filter((s) => s.label && s.label.trim() === text.trim());
    if (byLabel.length) return byLabel.map((s) => s.id);
    const canon = HL.canonHead(text);
    const exact = stmts.filter((s) => HL.canonHead(s.head) === canon);
    if (exact.length) return [exact[0].id];
    const prefix = stmts.filter((s) => HL.canonHead(s.head).startsWith(canon));
    if (prefix.length) return [prefix[0].id];
    return [];
  }

  // calc: a chain of formulas. Every line after the first starts with a
  // relation: "=" or "<=>" (equivalent), "==>" (implies), "<==" (is implied
  // by). A justification can follow "//" at the end of a line.
  const RELATIONS = [['<=>', 'eq'], ['⇔', 'eq'], ['≡', 'eq'], ['===', 'eq'], ['==>', 'imp'], ['⇒', 'imp'], ['=>', 'imp'],
    ['<==', 'rev'], ['⇐', 'rev'], ['==', 'eq'], ['=', 'eq']];

  function parseCalc(lines, fieldLine, warn) {
    const rows = [];
    for (const l of lines) {
      let t = l.text.trim();
      if (!t) continue;
      let why = '';
      const ci = t.indexOf('//');
      if (ci >= 0) {
        why = t.slice(ci + 2).trim();
        t = t.slice(0, ci).trim();
      }
      let rel = null;
      let relSym = '';
      if (rows.length) {
        for (const [sym, kind] of RELATIONS) {
          if (t.startsWith(sym)) {
            rel = kind;
            relSym = sym;
            t = t.slice(sym.length).trim();
            break;
          }
        }
        if (!rel) {
          // A line without a relation continues the previous formula.
          const prev = rows[rows.length - 1];
          prev.src += ' ' + t;
          if (why) prev.why = prev.why ? prev.why + ' ' + why : why;
          continue;
        }
      }
      rows.push({ rel, sym: relSym, src: t, why, line: l.line });
    }
    for (const r of rows) {
      try {
        r.f = HL.parseFormula(r.src);
      } catch (e) {
        r.f = null;
        r.error = e.message;
        warn(r.line, 'This calculation line could not be read, so it is shown as text and not checked: ' + e.message);
      }
    }
    return { kind: 'calc', rows, line: fieldLine };
  }

  // instance: the premises of an inference rule, one per line, then a line
  // made of dashes, then the conclusion.
  function parseInstance(lines, f, warn) {
    const premises = [];
    let conclusion = null;
    let afterBar = false;
    // The inline part of "instance:" may give the rule name.
    let name = '';
    let body = lines;
    if (f.inline && /^[A-Za-z-]+$/.test(f.inline.trim())) {
      name = f.inline.trim().toUpperCase();
      body = f.block;
    }
    for (const l of body) {
      const t = l.text.trim();
      if (!t) continue;
      if (/^-{3,}$/.test(t)) { afterBar = true; continue; }
      const entry = { src: t, line: l.line };
      try {
        entry.node = HL.parseStatementLine(t);
      } catch (e) {
        warn(l.line, 'This line of the rule instance could not be read, so it is shown as text: ' + e.message);
      }
      if (afterBar) conclusion = entry;
      else premises.push(entry);
    }
    if (!conclusion) warn(f.line, 'The instance has no conclusion. Put a line of dashes "---" before the conclusion.');
    return { kind: 'instance', name, premises, conclusion, line: f.line };
  }

  // "x = 1, y = -2, a = [4, 0, 9]"
  function parseState(src) {
    const env = {};
    const re = /\s*([A-Za-z_][A-Za-z0-9_]*'*)\s*=\s*(\[[^\]]*\]|-?\d+|true|false)\s*(,|$)/gy;
    let m;
    let pos = 0;
    const s = src.trim().replace(/′/g, "'").replace(/’/g, "'").replace(/−/g, '-');
    re.lastIndex = 0;
    while (pos < s.length && (m = re.exec(s))) {
      const v = m[2];
      if (v.startsWith('[')) {
        const inner = v.slice(1, -1).trim();
        env[m[1]] = inner ? inner.split(',').map((x) => Number(x.trim())) : [];
      } else if (v === 'true' || v === 'false') env[m[1]] = v === 'true';
      else env[m[1]] = Number(v);
      pos = re.lastIndex;
    }
    if (pos < s.length || !Object.keys(env).length) throw new Error('bad state');
    return env;
  }
  HL.parseState = parseState;
  HL.parseExercise = parseExercise;
})(typeof window !== 'undefined' ? window : globalThis);
