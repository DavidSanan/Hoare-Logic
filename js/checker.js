/*
 * checker.js
 *
 * Tests the claims of an exercise on sample states.
 *
 * A Hoare logic proof is a chain of claims: two formulas are equivalent, one
 * formula implies another, a triple {P} c {Q} holds. The checker does not
 * prove these claims. It evaluates them on many small states (integers
 * between -range and range, short arrays) and reports a state that breaks a
 * claim when it finds one. A passing test is evidence that the claim is
 * right, and a failing test is a definite counterexample.
 *
 * The checker is meant for authors: it catches typing mistakes in
 * intermediate assertions, invariants and verification conditions.
 */
(function (root) {
  'use strict';
  const HL = (root.HL = root.HL || {});

  const ENUM_LIMIT = 40000;
  const RANDOM_SAMPLES = 4000;
  const FUEL = 3000;

  // ------------------------------------------------------------------
  // Variables and their kinds
  // ------------------------------------------------------------------

  function arrayVarsOf(nodes, progs) {
    const arrays = new Set();
    const visit = (n) => {
      if (!n) return;
      if (n.k === 'idx' || n.k === 'store') {
        const a = HL.unparen(n.a);
        if (a.k === 'var') arrays.add(a.name);
      }
      if (n.k === 'call' && ['sizeof', 'length', 'len'].includes(n.f) && n.args[0]) {
        const a = HL.unparen(n.args[0]);
        if (a.k === 'var') arrays.add(a.name);
      }
      if (n.k === 'subst' && HL.unparen(n.by).k === 'store') arrays.add(n.x);
      if (n.k === 'wp') visitProg(n.prog);
      for (const key of ['e', 'l', 'r', 'a', 'i', 'v', 'by', 'body', 'lo', 'hi', 'post']) if (n[key] && typeof n[key] === 'object') visit(n[key]);
      if (n.args) n.args.forEach(visit);
    };
    const visitProg = (p) => {
      if (!p) return;
      if (p.k === 'seq') { p.items.forEach(visitProg); return; }
      if (p.k === 'assert') { visit(p.f); return; }
      if (p.k === 'aassign') { arrays.add(p.a); visit(p.i); visit(p.e); }
      if (p.k === 'assign') visit(p.e);
      if (p.k === 'if') { visit(p.c); visitProg(p.t); visitProg(p.e); }
      if (p.k === 'while') { visit(p.c); visitProg(p.body); }
    };
    nodes.forEach(visit);
    (progs || []).forEach(visitProg);
    return arrays;
  }

  function collectVars(nodes, progs) {
    const vars = new Set();
    nodes.forEach((n) => n && HL.freeVars(n).forEach((v) => vars.add(v)));
    (progs || []).forEach((p) => HL.progVars(p).forEach((v) => vars.add(v)));
    return [...vars].sort();
  }

  // Top-level equalities "v = e" of a formula. The generator uses them to
  // compute the value of v from the other variables, so that states that
  // satisfy the formula are found quickly.
  function topEqualities(f) {
    const out = [];
    const visit = (n) => {
      n = HL.unparen(n);
      if (n.k === 'bin' && n.op === '&&') { visit(n.l); visit(n.r); return; }
      if (n.k === 'chain' && n.ops.length === 1 && n.ops[0] === '=') {
        const l = HL.unparen(n.args[0]);
        const r = HL.unparen(n.args[1]);
        if (l.k === 'var') out.push([l.name, r]);
        if (r.k === 'var') out.push([r.name, l]);
      }
    };
    if (f) visit(f);
    return out;
  }

  function mulberry32(a) {
    return function () {
      a |= 0;
      a = (a + 0x6D2B79F5) | 0;
      let t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  // Generate states for the variables. hyp, when given, guides the
  // generation; the states are not guaranteed to satisfy it.
  function* states(vars, arrays, hyp, range, extra) {
    const R = range || 4;
    const eqs = topEqualities(hyp).filter(([v]) => vars.includes(v) && !arrays.has(v));
    const det = [];
    const deps = new Map();
    for (const [v, e] of eqs) {
      if (deps.has(v)) continue;
      const closure = new Set();
      HL.freeVars(e).forEach((u) => {
        closure.add(u);
        if (deps.has(u)) deps.get(u).forEach((w) => closure.add(w));
      });
      if (closure.has(v)) continue;
      if ([...closure].some((u) => !vars.includes(u))) continue;
      deps.set(v, closure);
      det.push([v, e]);
    }
    const free = vars.filter((v) => !deps.has(v));
    const ints = free.filter((v) => !arrays.has(v));
    const arrs = free.filter((v) => arrays.has(v));
    const valueSet = new Set();
    for (let x = -R; x <= R; x++) valueSet.add(x);
    (extra || []).forEach((x) => valueSet.add(x));
    const values = [...valueSet].sort((a, b) => a - b);

    const complete = (base) => {
      const env = { ...base };
      let pending = det.slice();
      for (let pass = 0; pass <= det.length && pending.length; pass++) {
        const next = [];
        for (const [v, e] of pending) {
          try {
            env[v] = HL.evaluate(e, env);
          } catch (err) {
            next.push([v, e]);
          }
        }
        pending = next;
      }
      return pending.length ? null : env;
    };

    const total = Math.pow(values.length, ints.length);
    if (!arrs.length && total <= ENUM_LIMIT) {
      const idx = new Array(ints.length).fill(0);
      for (let c = 0; c < total; c++) {
        const base = {};
        ints.forEach((v, j) => { base[v] = values[idx[j]]; });
        const env = complete(base);
        if (env) yield env;
        for (let j = 0; j < idx.length; j++) {
          idx[j]++;
          if (idx[j] < values.length) break;
          idx[j] = 0;
        }
      }
      return;
    }
    const rnd = mulberry32(12345);
    const pick = () => values[Math.floor(rnd() * values.length)];
    const maxLen = Math.min(R + 1, 6);
    const elem = Math.min(R, 4);
    for (let c = 0; c < RANDOM_SAMPLES; c++) {
      const base = {};
      ints.forEach((v) => { base[v] = pick(); });
      arrs.forEach((v) => {
        const len = Math.floor(rnd() * (maxLen + 1));
        const a = [];
        for (let j = 0; j < len; j++) a.push(Math.floor(rnd() * (2 * elem + 1)) - elem);
        base[v] = a;
      });
      // Indices are more useful when they fall inside the arrays.
      if (arrs.length && rnd() < 0.6) {
        const len = base[arrs[0]].length;
        ints.forEach((v) => { if (rnd() < 0.7 && len) base[v] = Math.floor(rnd() * len); });
      }
      const env = complete(base);
      if (env) yield env;
    }
  }

  // The constants of the formulas, with their neighbours, are added to the
  // values that are tried, so that a formula such as x > 100 is tested on
  // 100 and 101 and not only on small numbers.
  function interestingValues(nodes, progs, range) {
    const out = new Set();
    const visit = (n) => {
      if (!n || typeof n !== 'object') return;
      if (n.k === 'num' && Number.isInteger(n.v) && Math.abs(n.v) > (range || 4)) {
        [n.v - 1, n.v, n.v + 1, -n.v - 1, -n.v, -n.v + 1].forEach((x) => out.add(x));
      }
      for (const key of ['e', 'l', 'r', 'a', 'i', 'v', 'by', 'body', 'lo', 'hi', 'post', 'c', 't', 'f']) {
        if (n[key] && typeof n[key] === 'object') visit(n[key]);
      }
      if (n.args) n.args.forEach(visit);
      if (n.items) n.items.forEach(visit);
      if (n.k === 'wp') visit(n.prog);
    };
    nodes.forEach(visit);
    (progs || []).forEach(visit);
    return [...out].slice(0, 36);
  }

  function tryEval(f, env) {
    try {
      return { v: HL.evaluate(f, env) };
    } catch (e) {
      if (e instanceof HL.Undefined) return { undef: true };
      throw e;
    }
  }

  function truthy(r) {
    if (r.undef) return undefined;
    try { return HL.truth(r.v); } catch (e) { return undefined; }
  }

  // ------------------------------------------------------------------
  // The three kinds of test
  // ------------------------------------------------------------------

  function checkImplication(h, c, opts) {
    const vars = collectVars([h, c]);
    const arrays = arrayVarsOf([h, c]);
    let tested = 0, sat = 0;
    for (const env of states(vars, arrays, h, opts.range, interestingValues([h, c], null, opts.range))) {
      tested++;
      const hv = truthy(tryEval(h, env));
      if (hv !== true) continue;
      sat++;
      const cr = tryEval(c, env);
      const cv = truthy(cr);
      if (cv === undefined) return { status: 'fail', tested, sat, cex: env, reason: 'The right-hand side has no value in this state (for example an index outside an array).' };
      if (cv === false) return { status: 'fail', tested, sat, cex: env };
    }
    if (!sat) return { status: 'vacuous', tested, sat };
    return { status: 'pass', tested, sat };
  }

  function checkEquiv(a, b, assume, opts) {
    const vars = collectVars([a, b, assume]);
    const arrays = arrayVarsOf([a, b, assume]);
    let tested = 0, compared = 0;
    for (const env of states(vars, arrays, assume, opts.range, interestingValues([a, b, assume], null, opts.range))) {
      tested++;
      if (assume && truthy(tryEval(assume, env)) !== true) continue;
      const ra = tryEval(a, env);
      const rb = tryEval(b, env);
      if (ra.undef || rb.undef) continue;
      compared++;
      let same;
      if (typeof ra.v === 'boolean' || typeof rb.v === 'boolean') same = truthy(ra) === truthy(rb);
      else same = HL.deepEqual(ra.v, rb.v);
      if (!same) return { status: 'fail', tested, sat: compared, cex: env, values: [ra.v, rb.v] };
    }
    if (!compared) return { status: 'vacuous', tested, sat: 0 };
    return { status: 'pass', tested, sat: compared };
  }

  function checkTriple(pre, prog, post, opts) {
    if (HL.hasMeta(prog)) return { status: 'skip', reason: 'The program contains placeholder commands, so it cannot be run.' };
    const vars = collectVars([pre, post], [prog]);
    const arrays = arrayVarsOf([pre, post], [prog]);
    let tested = 0, sat = 0, nonterm = 0;
    for (const env of states(vars, arrays, pre, opts.range, interestingValues([pre, post], [prog], opts.range))) {
      tested++;
      if (truthy(tryEval(pre, env)) !== true) continue;
      sat++;
      let fin;
      try {
        fin = HL.execute(prog, env, { n: FUEL });
      } catch (e) {
        if (e instanceof HL.OutOfFuel) { nonterm++; continue; }
        if (e instanceof HL.Undefined) return { status: 'fail', tested, sat, cex: env, reason: 'The program fails in this state: it reads or writes outside an array, or computes a value that does not exist.' };
        throw e;
      }
      const pv = truthy(tryEval(post, fin));
      if (pv === undefined) return { status: 'fail', tested, sat, cex: env, final: fin, reason: 'The postcondition has no value in the final state.' };
      if (!pv) return { status: 'fail', tested, sat, cex: env, final: fin };
    }
    if (!sat) return { status: 'vacuous', tested, sat, nonterm };
    if (sat === nonterm) return { status: 'vacuous', tested, sat: 0, nonterm, reason: 'The program did not stop within the test budget for any tested state.' };
    return { status: 'pass', tested, sat: sat - nonterm, nonterm };
  }

  function checkCounterexample(node, state) {
    if (node.k === 'triple') {
      const missing = collectVars([node.pre, node.post], [node.prog]).filter((v) => !(v in state));
      if (missing.length) return { ok: false, message: 'The counterexample gives no value to ' + missing.join(', ') + '.' };
      if (truthy(tryEval(node.pre, state)) !== true) return { ok: false, message: 'The precondition is not true in the counterexample.' };
      try {
        const fin = HL.execute(node.prog, state, { n: FUEL });
        if (truthy(tryEval(node.post, fin)) === true) return { ok: false, message: 'The postcondition is true after running the program from the counterexample.' };
        return { ok: true, final: fin };
      } catch (e) {
        if (e instanceof HL.Undefined) return { ok: true, message: 'The program fails in this state.' };
        return { ok: false, message: 'The program does not stop from the counterexample within the test budget.' };
      }
    }
    const f = node.f;
    const missing = collectVars([f]).filter((v) => !(v in state));
    if (missing.length) return { ok: false, message: 'The counterexample gives no value to ' + missing.join(', ') + '.' };
    const fu = HL.unparen(f);
    if (fu.k === 'bin' && fu.op === '==>') {
      if (truthy(tryEval(fu.l, state)) !== true) return { ok: false, message: 'The left-hand side is not true in the counterexample.' };
      if (truthy(tryEval(fu.r, state)) === true) return { ok: false, message: 'The right-hand side is true in the counterexample.' };
      return { ok: true };
    }
    if (truthy(tryEval(f, state)) === true) return { ok: false, message: 'The formula is true in the counterexample.' };
    return { ok: true };
  }

  // ------------------------------------------------------------------
  // Slots
  // ------------------------------------------------------------------

  function resolver(ex, slots) {
    const stateVars = new Set();
    if (ex.program) HL.progVars(ex.program).forEach((v) => stateVars.add(v));
    if (ex.pre) HL.freeVars(ex.pre).forEach((v) => stateVars.add(v));
    if (ex.post) HL.freeVars(ex.post).forEach((v) => stateVars.add(v));
    const unresolved = new Set();
    const resolve = (f, depth = 0) => {
      const go = (n) => {
        if (n.k === 'var' && slots.has(n.name) && !stateVars.has(n.name)) {
          if (depth > 6) { unresolved.add(n.name); return n; }
          return HL.N.paren(resolve(slots.get(n.name), depth + 1));
        }
        if (n.k === 'var' && ex.slotNames && ex.slotNames.includes(n.name) && !stateVars.has(n.name)) {
          unresolved.add(n.name);
          return n;
        }
        if (n.k === 'wp') return { ...n, post: go(n.post) };
        return mapAll(n, go);
      };
      return go(f);
    };
    return { resolve, unresolved };
  }

  function mapAll(n, f) {
    const out = { ...n };
    for (const key of ['e', 'l', 'r', 'a', 'i', 'v', 'by', 'body', 'lo', 'hi', 'post']) {
      if (n[key] && typeof n[key] === 'object' && n[key].k) out[key] = f(n[key]);
    }
    if (n.args) out.args = n.args.map(f);
    return out;
  }

  // Prepare a formula for testing: replace slot names by their formulas and
  // compute every substitution and wp(...) in it.
  function prepare(f, res) {
    if (!f) return { f: null };
    res.unresolved.clear();
    let g = res.resolve(f);
    if (res.unresolved.size) return { skip: 'It mentions ' + [...res.unresolved].join(', ') + ', which has no value at this point.' };
    try {
      g = HL.expand(g);
    } catch (e) {
      return { skip: e.message };
    }
    return { f: g };
  }

  function prepareLine(node, res) {
    if (node.k === 'triple') {
      const pre = prepare(node.pre, res);
      if (pre.skip) return pre;
      const post = prepare(node.post, res);
      if (post.skip) return post;
      const prog = resolveProg(node.prog, res);
      return { node: { k: 'triple', pre: pre.f, prog, post: post.f } };
    }
    const f = prepare(node.f, res);
    if (f.skip) return f;
    return { node: { k: 'formula', f: f.f } };
  }

  function resolveProg(p, res) {
    // Programs only contain program variables; nothing to resolve. Kept as a
    // hook in case programs mention slots in conditions.
    return p;
  }

  function checkLine(node, opts, assume) {
    if (node.k === 'triple') {
      const pre = assume ? HL.N.bin('&&', assume, node.pre) : node.pre;
      return Object.assign({ kind: 'triple' }, checkTriple(pre, node.prog, node.post, opts));
    }
    const f = HL.unparen(node.f);
    if (f.k === 'bin' && f.op === '==>') {
      const h = assume ? HL.N.bin('&&', assume, f.l) : f.l;
      return Object.assign({ kind: 'implication' }, checkImplication(h, f.r, opts));
    }
    if (f.k === 'bin' && f.op === '<=>') return Object.assign({ kind: 'equivalence' }, checkEquiv(f.l, f.r, assume, opts));
    return Object.assign({ kind: 'formula' }, checkImplication(assume || HL.N.bool(true), f, opts));
  }

  // ------------------------------------------------------------------
  // Checking a whole exercise
  // ------------------------------------------------------------------

  function checkExercise(ex) {
    const results = [];
    if (ex.errors.length || !ex.program || !ex.pre || !ex.post) {
      results.push({ group: 'Exercise', item: 'Reading the file', status: 'skip', ok: false, reason: 'The exercise has errors, so it was not tested.' });
      return results;
    }
    const opts = { range: ex.range || 4 };
    const slots = new Map([['P', ex.pre], ['Q', ex.post]]);
    const res = resolver(ex, slots);
    const add = (r) => {
      if (r.status === 'skip' || r.status === 'vacuous' || r.status === 'expected') r.ok = null;
      else r.ok = (r.expect === 'fails') ? r.status === 'fail' : r.status === 'pass';
      results.push(r);
    };

    // 1. The specification itself, by running the program.
    {
      const r = checkTriple(ex.pre, ex.program, ex.post, opts);
      const expect = ex.verdict === 'invalid' ? 'fails' : 'holds';
      add(Object.assign(r, { group: 'Specification', item: 'The triple {pre} program {post}', kind: 'triple', expect, line: ex.programLine }));
    }

    // 2. Every step.
    for (const step of ex.steps) {
      const group = 'Step ' + step.index + ': ' + step.title;
      for (const it of step.items) {
        if (it.kind === 'set' && it.f) slots.set(it.name, it.f);
      }
      const assume = step.assume ? prepare(step.assume, res).f : null;
      let calcNo = 0, vcNo = 0;
      for (const it of step.items) {
        if (it.kind === 'calc') {
          calcNo++;
          for (let j = 1; j < it.rows.length; j++) {
            const a = it.rows[j - 1];
            const b = it.rows[j];
            const where = { group, item: 'Calculation' + (calcNo > 1 ? ' ' + calcNo : '') + ', line ' + (j + 1), line: b.line, expect: 'holds' };
            if (!a.f || !b.f) {
              add(Object.assign(where, { status: 'skip', reason: 'One of the two lines could not be read.' }));
              continue;
            }
            const pa = prepare(a.f, res);
            const pb = prepare(b.f, res);
            if (pa.skip || pb.skip) {
              add(Object.assign(where, { status: 'skip', reason: pa.skip || pb.skip }));
              continue;
            }
            let r;
            if (b.rel === 'eq') r = Object.assign({ kind: 'equivalence' }, checkEquiv(pa.f, pb.f, assume, opts));
            else if (b.rel === 'imp') r = Object.assign({ kind: 'implication' }, checkImplication(assume ? HL.N.bin('&&', assume, pa.f) : pa.f, pb.f, opts));
            else r = Object.assign({ kind: 'implication' }, checkImplication(assume ? HL.N.bin('&&', assume, pb.f) : pb.f, pa.f, opts));
            add(Object.assign(r, where));
          }
        }
        if (it.kind === 'vc') {
          vcNo++;
          const where = { group, item: 'Verification condition ' + vcNo, line: it.line, expect: it.status };
          if (!it.node) {
            add(Object.assign(where, { status: 'skip', reason: 'The condition could not be read.' }));
            continue;
          }
          const p = prepareLine(it.node, res);
          if (p.skip) {
            add(Object.assign(where, { status: 'skip', reason: p.skip }));
            continue;
          }
          const r = checkLine(p.node, opts, assume);
          add(Object.assign(r, where));
          if (it.counterexample) {
            const c = checkCounterexample(p.node, it.counterexample);
            results.push({
              group, item: 'Counterexample of verification condition ' + vcNo, line: it.line, kind: 'counterexample',
              status: c.ok ? 'pass' : 'fail', ok: c.ok, expect: 'holds', reason: c.message, cex: it.counterexample, final: c.final
            });
          }
        }
        if (it.kind === 'instance') {
          const lines = it.premises.map((p, j) => ({ e: p, name: 'premise ' + (j + 1) }));
          if (it.conclusion) lines.push({ e: it.conclusion, name: 'conclusion' });
          for (const { e, name } of lines) {
            const where = { group, item: 'Rule instance, ' + name, line: e.line, expect: 'holds' };
            if (!e.node) {
              add(Object.assign(where, { status: 'skip', reason: 'The line could not be read.' }));
              continue;
            }
            const p = prepareLine(e.node, res);
            if (p.skip) {
              add(Object.assign(where, { status: 'skip', reason: p.skip }));
              continue;
            }
            add(Object.assign(checkLine(p.node, opts, null), where));
          }
        }
      }
    }

    // 3. The annotated program with the final value of every assertion:
    // every pattern {A} statement {B} must be a valid triple, and every
    // pattern {A} {B} must be an implication.
    const outline = [];
    const walk = (seq) => {
      const items = seq.items;
      for (let j = 0; j < items.length; j++) {
        const s = items[j];
        if (s.k === 'if') { walk(s.t); if (s.e) walk(s.e); }
        if (s.k === 'while') walk(s.body);
        if (s.k === 'seq') walk(s);
        if (s.k !== 'assert') continue;
        const n1 = items[j + 1];
        const n2 = items[j + 2];
        if (n1 && n1.k === 'assert') outline.push({ a: s, b: n1 });
        else if (n1 && n2 && n2.k === 'assert') outline.push({ a: s, stmt: n1, b: n2 });
      }
    };
    walk(ex.program);
    for (const o of outline) {
      const label = o.stmt ? '{' + o.a.src + '} ' + HL.progInlineText(o.stmt) + ' {' + o.b.src + '}' : '{' + o.a.src + '} implies {' + o.b.src + '}';
      const where = { group: 'Annotated program', item: label, line: ex.programLine, expect: 'holds' };
      const pa = prepare(o.a.f, res);
      const pb = prepare(o.b.f, res);
      if (pa.skip || pb.skip) {
        add(Object.assign(where, { status: 'skip', reason: pa.skip || pb.skip }));
        continue;
      }
      const r = o.stmt ? Object.assign({ kind: 'triple' }, checkTriple(pa.f, { k: 'seq', items: [o.stmt] }, pb.f, opts))
        : Object.assign({ kind: 'implication' }, checkImplication(pa.f, pb.f, opts));
      Object.assign(r, where);
      if (r.status === 'fail' && ex.verdict === 'invalid') {
        // The triple is not valid, so some link of the outline must break.
        r.status = 'expected';
        r.reason = 'This link breaks, which is expected: the exercise states that the triple is not valid.';
      }
      add(r);
    }
    return results;
  }

  HL.Checker = { checkExercise, checkImplication, checkEquiv, checkTriple, checkCounterexample, collectVars, arrayVarsOf };
})(typeof window !== 'undefined' ? window : globalThis);
