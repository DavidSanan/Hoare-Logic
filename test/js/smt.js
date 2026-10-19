/*
 * smt.js
 *
 * Translates the formulas of the course into SMT-LIB, the input language
 * of SMT solvers such as Z3, and asks the solver whether a formula is
 * valid.
 *
 * A formula F is valid when it is true in every state. The solver is asked
 * whether "not F" has a model:
 *   unsat    no state makes F false: F is proved;
 *   sat      the model is a state that makes F false: a counterexample;
 *   unknown  the solver gave no answer (non-linear arithmetic, recursive
 *            functions, quantifiers, or the time limit).
 *
 * The meaning of every symbol is the one of the course and of the tester
 * (logic.js, function evaluate):
 *   - integers are mathematical integers;
 *   - "div" and "mod" round down: x div y = floor(x / y), and
 *     x mod y = x - y * (x div y);
 *   - an array is a sequence of integers with a length, sizeof(a); it is
 *     encoded as an SMT array (Array Int Int) with a separate length;
 *   - fib, fact and pow follow their definitions on the natural numbers;
 *     outside them their value is left unspecified, so that nothing can be
 *     proved by relying on it;
 *   - sum and prod over a range are defined by recursion on the upper
 *     bound, as in the course.
 *
 * The solver is reached through a small interface, so that the same code
 * runs in the browser (Z3 compiled to WebAssembly) and in Node.js:
 *   solver.run(text) -> Promise<string>   evaluates SMT-LIB commands in one
 *                                         persistent context
 */
(function (root) {
  'use strict';
  const HL = (root.HL = root.HL || {});

  // The definitions of the functions of the course, given to the solver
  // before every query.
  const PRELUDE = [
    '(define-fun hl_div ((a Int) (b Int)) Int (ite (> b 0) (div a b) (div (- a) (- b))))',
    '(define-fun hl_mod ((a Int) (b Int)) Int (- a (* b (hl_div a b))))',
    '(define-fun hl_abs ((a Int)) Int (ite (< a 0) (- a) a))',
    '(define-fun hl_min ((a Int) (b Int)) Int (ite (<= a b) a b))',
    '(define-fun hl_max ((a Int) (b Int)) Int (ite (>= a b) a b))',
    // fib, fact and pow are declared functions. One step of each definition
    // is a function "_step"; the queries unfold the definitions on their
    // own terms (see unfoldCall). Outside the natural numbers the value is
    // the one of an unspecified function "_u".
    '(declare-fun hl_fib (Int) Int)',
    '(declare-fun hl_fib_u (Int) Int)',
    '(define-fun hl_fib_step ((n Int)) Int (ite (< n 0) (hl_fib_u n) (ite (<= n 1) n (+ (hl_fib (- n 1)) (hl_fib (- n 2))))))',
    '(declare-fun hl_fact (Int) Int)',
    '(declare-fun hl_fact_u (Int) Int)',
    '(define-fun hl_fact_step ((n Int)) Int (ite (< n 0) (hl_fact_u n) (ite (= n 0) 1 (* n (hl_fact (- n 1))))))',
    '(declare-fun hl_pow (Int Int) Int)',
    '(declare-fun hl_pow_u (Int Int) Int)',
    '(define-fun hl_pow_step ((a Int) (b Int)) Int (ite (< b 0) (hl_pow_u a b) (ite (= b 0) 1 (* a (hl_pow a (- b 1))))))'
  ].join('\n');

  // The general axioms, used only for terms under a quantifier.
  const AXIOMS = {
    hl_fib: '(assert (forall ((n Int)) (! (= (hl_fib n) (hl_fib_step n)) :pattern ((hl_fib n)))))',
    hl_fact: '(assert (forall ((n Int)) (! (= (hl_fact n) (hl_fact_step n)) :pattern ((hl_fact n)))))',
    hl_pow: '(assert (forall ((a Int) (b Int)) (! (= (hl_pow a b) (hl_pow_step a b)) :pattern ((hl_pow a b)))))'
  };

  class Unsupported extends Error {}

  const sym = (name) => '|' + name + '|';
  const lenSym = (name) => '|len#' + name + '|';

  // Encode a formula. ctx holds the arrays, the bound variables and the
  // definitions of sums and products created along the way.
  function encoder(arrays, depth) {
    const ctx = { arrays, bound: new Map(), defs: [], bigs: new Map(), free: new Set(), unfold: new Set(), bigAxiom: new Map(), needAxiom: new Set() };

    const varTerm = (name) => {
      if (ctx.bound.has(name)) return ctx.bound.get(name);
      ctx.free.add(name);
      return sym(name);
    };

    // An array-valued expression: its content and its length.
    function arr(n) {
      n = HL.unparen(n);
      if (n.k === 'var') {
        if (!arrays.has(n.name)) throw new Unsupported('"' + n.name + '" is used as an array and as a number');
        ctx.free.add(n.name);
        return { a: sym(n.name), len: lenSym(n.name) };
      }
      if (n.k === 'store') {
        const b = arr(n.a);
        return { a: '(store ' + b.a + ' ' + term(n.i) + ' ' + term(n.v) + ')', len: b.len };
      }
      throw new Unsupported('An array was expected here');
    }

    const isArrayValued = (n) => {
      n = HL.unparen(n);
      return n.k === 'store' || (n.k === 'var' && arrays.has(n.name) && !ctx.bound.has(n.name));
    };

    function term(n) {
      switch (n.k) {
        case 'num': return n.v >= 0 ? String(n.v) : '(- ' + (-n.v) + ')';
        case 'bool': return n.v ? 'true' : 'false';
        case 'var': return varTerm(n.name);
        case 'paren': return term(n.e);
        case 'un': return n.op === '!' ? '(not ' + term(n.e) + ')' : '(- ' + term(n.e) + ')';
        case 'bin': {
          const l = term(n.l);
          const r = term(n.r);
          switch (n.op) {
            case '&&': return '(and ' + l + ' ' + r + ')';
            case '||': return '(or ' + l + ' ' + r + ')';
            case '==>': return '(=> ' + l + ' ' + r + ')';
            case '<=>': return '(= ' + l + ' ' + r + ')';
            case '+': return '(+ ' + l + ' ' + r + ')';
            case '-': return '(- ' + l + ' ' + r + ')';
            case '*': return '(* ' + l + ' ' + r + ')';
            case 'div': return '(hl_div ' + l + ' ' + r + ')';
            case 'mod': case '%': return '(hl_mod ' + l + ' ' + r + ')';
            case '^': return powCall(n.l, n.r);
            default: throw new Unsupported('The operator "' + n.op + '" is not supported by the prover');
          }
        }
        case 'chain': {
          const parts = [];
          for (let j = 0; j < n.ops.length; j++) parts.push(compare(n.ops[j], n.args[j], n.args[j + 1]));
          return parts.length === 1 ? parts[0] : '(and ' + parts.join(' ') + ')';
        }
        case 'call': return call(n);
        case 'idx': {
          const b = arr(n.a);
          return '(select ' + b.a + ' ' + term(n.i) + ')';
        }
        case 'quant': {
          const saved = new Map(ctx.bound);
          n.vars.forEach((v) => ctx.bound.set(v, sym(v)));
          const body = term(n.body);
          ctx.bound = saved;
          return '(' + (n.q === 'forall' ? 'forall' : 'exists') + ' (' + n.vars.map((v) => '(' + sym(v) + ' Int)').join(' ') + ') ' + body + ')';
        }
        case 'big': return big(n);
        case 'store': throw new Unsupported('An updated array can only be read or compared');
        default: throw new Unsupported('This kind of formula is not supported by the prover');
      }
    }

    // A call of a recursive function. Its definition is unfolded on the term
    // itself and on the terms that the unfolding creates, to the depth
    // given by "steps": [how far back the definition looks, how many
    // levels]. Under a quantifier the general axiom is used instead.
    function unfoldCall(name, argTerms, steps, levels) {
      const app = '(' + name + ' ' + argTerms.join(' ') + ')';
      if (ctx.bound.size) { ctx.needAxiom.add(name); return app; }
      const [back, d0] = steps;
      const last = argTerms.length - 1;
      const total = levels != null ? levels : Math.max(d0 + back, depth || 0);
      for (let d = 0; d <= total; d++) {
        const k = argTerms.slice();
        k[last] = d ? '(- ' + argTerms[last] + ' ' + d + ')' : argTerms[last];
        ctx.unfold.add('(assert (= (' + name + ' ' + k.join(' ') + ') (' + name + '_step ' + k.join(' ') + ')))');
      }
      return app;
    }

    // a^b: with a constant exponent the definition is unfolded down to 0.
    function powCall(a, b) {
      const bb = HL.unparen(b);
      const levels = bb.k === 'num' && bb.v >= 0 && bb.v <= 12 ? bb.v : null;
      return unfoldCall('hl_pow', [term(a), term(b)], [1, 1], levels);
    }

    function compare(op, a, b) {
      if (op === '=' || op === '!=') {
        if (isArrayValued(a) || isArrayValued(b)) {
          const x = arr(a);
          const y = arr(b);
          const eq = '(and (= ' + x.a + ' ' + y.a + ') (= ' + x.len + ' ' + y.len + '))';
          return op === '=' ? eq : '(not ' + eq + ')';
        }
        return op === '=' ? '(= ' + term(a) + ' ' + term(b) + ')' : '(not (= ' + term(a) + ' ' + term(b) + '))';
      }
      return '(' + op + ' ' + term(a) + ' ' + term(b) + ')';
    }

    function call(n) {
      const args = n.args;
      const one = () => term(args[0]);
      switch (n.f) {
        case 'fib': return unfoldCall('hl_fib', [one()], [2, 1]);
        case 'fact': return unfoldCall('hl_fact', [one()], [1, 1]);
        case 'pow': return powCall(args[0], args[1]);
        case 'abs': return '(hl_abs ' + one() + ')';
        case 'min': case 'max':
          return args.map(term).reduce((a, b) => '(hl_' + n.f + ' ' + a + ' ' + b + ')');
        case 'even': return '(= (hl_mod ' + one() + ' 2) 0)';
        case 'odd': return '(= (hl_mod ' + one() + ' 2) 1)';
        case 'div': return '(hl_div ' + term(args[0]) + ' ' + term(args[1]) + ')';
        case 'mod': return '(hl_mod ' + term(args[0]) + ' ' + term(args[1]) + ')';
        case 'sizeof': case 'length': return arr(args[0]).len;
        case 'def': {
          const r = args[0] && HL.unparen(args[0]);
          if (!r || r.k !== 'idx') throw new Unsupported('def(...) needs an array access');
          const b = arr(r.a);
          const i = term(r.i);
          return '(and (<= 0 ' + i + ') (< ' + i + ' ' + b.len + '))';
        }
        default: throw new Unsupported('The function "' + n.f + '" is not supported by the prover');
      }
    }

    // sum(k, lo, hi, e) and prod(k, lo, hi, e): a recursive function of the
    // bounds and of the free variables of e, defined as in the course:
    //   sum(k, lo, hi, e) = 0 when hi < lo, and
    //   sum(k, lo, hi, e) = sum(k, lo, hi - 1, e) + e[k <- hi] otherwise.
    function big(n) {
      const fv = [...HL.freeVars(n.e)].filter((v) => v !== n.v).sort();
      const key = n.f + '|' + n.v + '|' + HL.toText(n.e) + '|' + fv.map((v) => (ctx.bound.has(v) ? 'b:' : '') + v).join(',');
      let name = ctx.bigs.get(key);
      const params = [];
      const actual = [];
      for (const v of fv) {
        if (arrays.has(v) && !ctx.bound.has(v)) {
          params.push('(' + sym(v) + ' (Array Int Int))', '(' + lenSym(v) + ' Int)');
          actual.push(sym(v), lenSym(v));
          ctx.free.add(v);
        } else {
          params.push('(' + sym(v) + ' Int)');
          actual.push(ctx.bound.has(v) ? ctx.bound.get(v) : (ctx.free.add(v), sym(v)));
        }
      }
      if (!name) {
        name = 'hl_' + n.f + '_' + (ctx.bigs.size + 1);
        ctx.bigs.set(key, name);
        // The body uses the parameters, whose names are those of the free
        // variables, and the parameter hi for the bound variable.
        const saved = ctx.bound;
        ctx.bound = new Map([[n.v, '|hl#hi|']]);
        fv.forEach((v) => { if (!arrays.has(v)) ctx.bound.set(v, sym(v)); });
        const savedFree = ctx.free;
        ctx.free = new Set();
        const e = term(n.e);
        ctx.free = savedFree;
        ctx.bound = saved;
        const unit = n.f === 'sum' ? '0' : '1';
        const op = n.f === 'sum' ? '+' : '*';
        // A declared function, with one step of its definition. It is not
        // given with define-fun-rec, because Z3 crashes when such
        // definitions are given again in successive push/pop scopes (see
        // tools/z3-bugs). The axiom with a pattern is only used for terms
        // under a quantifier (see below).
        const formals = fv.map((v) => (arrays.has(v) ? sym(v) + ' ' + lenSym(v) : sym(v))).join(' ');
        const sorts = ['Int', 'Int'].concat(fv.map((v) => (arrays.has(v) ? '(Array Int Int) Int' : 'Int'))).join(' ');
        const app = '(' + name + ' |hl#lo| |hl#hi|' + (formals ? ' ' + formals : '') + ')';
        const prev = '(' + name + ' |hl#lo| (- |hl#hi| 1)' + (formals ? ' ' + formals : '') + ')';
        ctx.defs.push('(declare-fun ' + name + ' (' + sorts + ') Int)');
        // One step of the definition, as a function of the bounds.
        ctx.defs.push('(define-fun ' + name + '_step ((|hl#lo| Int) (|hl#hi| Int)' + (params.length ? ' ' + params.join(' ') : '') + ') Int ' +
          '(ite (< |hl#hi| |hl#lo|) ' + unit + ' (' + op + ' ' + prev + ' ' + e + ')))');
        ctx.bigAxiom.set(name, '(assert (forall ((|hl#lo| Int) (|hl#hi| Int)' + (params.length ? ' ' + params.join(' ') : '') + ') ' +
          '(! (= ' + app + ' (' + name + '_step |hl#lo| |hl#hi|' + (formals ? ' ' + formals : '') + ')) :pattern (' + app + '))))');
      }
      // The definition is unfolded on the terms of the query: two steps,
      // which is what the proofs of the course use. A term under a
      // quantifier needs the general axiom instead.
      const lo = term(n.lo);
      const hi = term(n.hi);
      const rest = actual.length ? ' ' + actual.join(' ') : '';
      if (ctx.bound.size) ctx.needAxiom.add(name);
      else {
        for (let d = 0; d <= Math.max(1, depth || 0); d++) {
          const h = d ? '(- ' + hi + ' ' + d + ')' : hi;
          ctx.unfold.add('(assert (= (' + name + ' ' + lo + ' ' + h + rest + ') (' + name + '_step ' + lo + ' ' + h + rest + ')))');
        }
      }
      return '(' + name + ' ' + term(n.lo) + ' ' + term(n.hi) + (actual.length ? ' ' + actual.join(' ') : '') + ')';
    }

    return { term, ctx };
  }

  // The SMT-LIB query that asks whether "hyps ==> goal" has a counterexample.
  // opts.depth: how many steps the definitions are unfolded;
  // opts.small: only look for states whose numbers are between -small and
  // small, and whose arrays have at most 8 cells.
  function validityQuery(hyps, goal, opts = {}) {
    const all = hyps.concat([goal]);
    const arrays = new Set(HL.Checker.arrayVarsOf(all));
    // A variable compared with an array is an array too, as in a = a'.
    let grew = true;
    while (grew) {
      grew = false;
      const visit = (n) => {
        if (!n || typeof n !== 'object') return;
        if (n.k === 'chain') {
          n.ops.forEach((op, j) => {
            if (op !== '=' && op !== '!=') return;
            const x = HL.unparen(n.args[j]);
            const y = HL.unparen(n.args[j + 1]);
            const isArr = (t) => t.k === 'store' || (t.k === 'var' && arrays.has(t.name));
            for (const [p, q] of [[x, y], [y, x]]) {
              if (isArr(p) && q.k === 'var' && !arrays.has(q.name)) { arrays.add(q.name); grew = true; }
            }
          });
        }
        for (const key of ['e', 'l', 'r', 'a', 'i', 'v', 'body', 'lo', 'hi']) if (n[key] && n[key].k) visit(n[key]);
        if (n.args) n.args.forEach(visit);
      };
      all.forEach(visit);
    }
    const enc = encoder(arrays, opts.depth);
    const h = hyps.map(enc.term);
    const g = enc.term(goal);
    const free = [...enc.ctx.free].sort();
    const decls = [];
    for (const v of free) {
      if (arrays.has(v)) {
        decls.push('(declare-const ' + sym(v) + ' (Array Int Int))', '(declare-const ' + lenSym(v) + ' Int)', '(assert (>= ' + lenSym(v) + ' 0))');
      } else {
        decls.push('(declare-const ' + sym(v) + ' Int)');
      }
    }
    const body = h.length ? '(=> (and ' + h.join(' ') + ') ' + g + ')' : g;
    const axioms = [...enc.ctx.needAxiom].map((name) => enc.ctx.bigAxiom.get(name) || AXIOMS[name]);
    const bounds = [];
    if (opts.small) {
      for (const v of [...enc.ctx.free]) {
        if (arrays.has(v)) bounds.push('(assert (<= ' + lenSym(v) + ' 8))');
        else bounds.push('(assert (<= (- ' + opts.small + ') ' + sym(v) + ' ' + opts.small + '))');
      }
    }
    const text = decls.concat(enc.ctx.defs).concat(axioms).concat([...enc.ctx.unfold]).concat(bounds).concat(['(assert (not ' + body + '))']).join('\n');
    // With sums and products, the solver only knows the unfolded steps of
    // their definitions: a model may then not be a real counterexample.
    const partial = enc.ctx.unfold.size > 0 || enc.ctx.needAxiom.size > 0;
    return { text, free, arrays, partial };
  }

  // A small reader of the S-expressions printed by the solver.
  function parseSexp(s) {
    let i = 0;
    const out = [];
    const skip = () => { while (i < s.length && /\s/.test(s[i])) i++; };
    function read() {
      skip();
      if (s[i] === '(') {
        i++;
        const list = [];
        for (;;) {
          skip();
          if (i >= s.length) break;
          if (s[i] === ')') { i++; break; }
          list.push(read());
        }
        return list;
      }
      if (s[i] === '|') {
        const j = s.indexOf('|', i + 1);
        const t = s.slice(i, j + 1);
        i = j + 1;
        return t;
      }
      const m = s.slice(i).match(/^[^\s()]+/);
      i += m ? m[0].length : 1;
      return m ? m[0] : '';
    }
    for (;;) {
      skip();
      if (i >= s.length) break;
      out.push(read());
    }
    return out;
  }

  function intValue(v) {
    if (typeof v === 'string') return Number(v);
    if (Array.isArray(v) && v[0] === '-' && v.length === 2) return -intValue(v[1]);
    return NaN;
  }

  // Ask the solver whether "hyps ==> goal" is valid.
  // Result: { status: 'proved' } | { status: 'refuted', state } |
  //         { status: 'unknown', reason } | { status: 'error', reason }
  async function prove(solver, hyps, goal, opts = {}) {
    let q;
    try {
      q = validityQuery(hyps, goal, opts);
    } catch (e) {
      if (e instanceof Unsupported) return { status: 'error', reason: e.message };
      throw e;
    }
    const timeout = opts.timeout || 4000;
    // The definitions of the course's functions are given once, outside
    // the scopes of the queries.
    if (!solver.hlPrelude) {
      await solver.run(PRELUDE);
      solver.hlPrelude = true;
    }
    await solver.run('(push)');
    try {
      const answer = (await solver.run('(set-option :timeout ' + timeout + ')\n' + q.text + '\n(check-sat)')).trim();
      const last = answer.split('\n').pop().trim();
      if (last === 'unsat') return { status: 'proved', query: q.text };
      if (last !== 'sat') {
        const why = await solver.run('(get-info :reason-unknown)');
        return { status: 'unknown', reason: why.replace(/[()":]/g, ' ').replace(/\s+/g, ' ').trim(), query: q.text };
      }
      // A counterexample: the values of the variables, and the cells of the
      // arrays. Long arrays cannot be shown, so the solver is asked first
      // for a counterexample in which every array has at most 8 cells.
      const lensAll = q.free.filter((v) => q.arrays.has(v));
      if (lensAll.length) {
        await solver.run('(push)');
        const small = (await solver.run(lensAll.map((a) => '(assert (<= ' + lenSym(a) + ' 8))').join('\n') + '\n(check-sat)')).trim().split('\n').pop().trim();
        if (small !== 'sat') await solver.run('(pop)');
        else solver.hlSmall = true;
      }
      const state = {};
      const scalars = q.free.filter((v) => !q.arrays.has(v));
      const lens = q.free.filter((v) => q.arrays.has(v));
      const names = scalars.map(sym).concat(lens.map(lenSym));
      if (names.length) {
        const vals = parseSexp(await solver.run('(get-value (' + names.join(' ') + '))'))[0] || [];
        vals.forEach(([k, v]) => {
          const name = k.replace(/^\|/, '').replace(/\|$/, '');
          if (name.startsWith('len#')) state[name] = intValue(v);
          else state[name] = intValue(v);
        });
      }
      for (const a of lens) {
        const n = Math.max(0, Math.min(state['len#' + a] || 0, 64));
        delete state['len#' + a];
        if (!n) { state[a] = []; continue; }
        const cells = [];
        for (let j = 0; j < n; j++) cells.push('(select ' + sym(a) + ' ' + j + ')');
        const vals = parseSexp(await solver.run('(get-value (' + cells.join(' ') + '))'))[0] || [];
        state[a] = vals.map(([, v]) => intValue(v));
      }
      if (solver.hlSmall) { solver.hlSmall = false; await solver.run('(pop)'); }
      return { status: 'refuted', state, query: q.text, partial: q.partial };
    } finally {
      await solver.run('(pop)');
    }
  }

  HL.SMT = { prove, validityQuery, PRELUDE, parseSexp, Unsupported };
})(typeof window !== 'undefined' ? window : globalThis);
