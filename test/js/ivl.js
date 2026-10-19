/*
 * ivl.js
 *
 * An intermediate verification language, used only inside the prover. The
 * student never sees it: the programs, the specifications and the rules
 * stay those of the course. The language has the commands
 *
 *   assert F     F must hold here; the prover checks it
 *   assume F     the paths on which F is false are not considered
 *   havoc V      the variables V get arbitrary values
 *   x := E       assignment;  a := a[I |-> E]  for a write in an array
 *   c1; c2       sequence
 *   c1 [] c2     choice between two paths
 *
 * TRANSLATION OF AN ANNOTATED PROGRAM
 *
 * Every assertion {A} of the annotated program becomes
 *
 *   assert A; havoc ALL; assume A
 *
 * where ALL is the set of all the variables, those of the program and the
 * logical ones. The "havoc ALL" forgets everything known before the
 * assertion, so each check of the proof starts from an assertion alone,
 * exactly as each link of a proof outline is proved in the course: the
 * check of a link {A} c {B} is A ==> wp(c, B), quantified over all the
 * variables, and nothing else. In particular, a loop invariant must contain
 * every fact that its checks need: no fact of the precondition is carried
 * into the loop implicitly.
 *
 *   if B then c1 else c2      (assume B; c1) [] (assume !B; c2)
 *   {I} while B do c          the assertion {I} before the loop is the
 *                             invariant, and the loop becomes
 *                             (assume B; c; assert I; assume false) [] assume !B
 *
 * With the cuts at {I}, the checks of a loop are those of the course:
 * initialisation (the link that reaches {I}), preservation (the links of
 * the body, from I && B, and the end of the body back to I) and conclusion
 * (from I && !B to the next assertion).
 *
 * An assignment that reads an array, x := a[i], is preceded by
 * "assert def(a[i])", as in the rule ARRAY-READ; a write a[i] := E by
 * "assert def(a[i])", as in the rule ARRAY-ASSIGN.
 *
 * GENERATION OF THE CHECKS
 *
 * The checks are computed backwards, with the weakest precondition of
 * each command, keeping one check per assert:
 *   assert F      adds the check "F"
 *   assume F      adds the hypothesis F to every check after it
 *   x := E        substitutes E for x in every check after it
 *   havoc V       renames V in the checks after it, which then hold for
 *                 every value of V; when V contains all the variables of a
 *                 check, the check is closed and nothing before it changes
 *                 it any more
 *   c1 [] c2      the checks of both paths
 */
(function (root) {
  'use strict';
  const HL = (root.HL = root.HL || {});
  const N = HL.N;

  // ------------------------------------------------------------------
  // Translation of an annotated program
  // ------------------------------------------------------------------

  // resolve(assertNode) gives the formula of an assertion of the program,
  // with the values of its named slots. allVars: every variable.
  // A conjunct "n = E" or "E = n" of f, with n not in E: the value to give
  // to n.
  function findWitness(f, n) {
    const conj = [];
    const split = (g) => {
      g = HL.unparen(g);
      if (g.k === 'bin' && g.op === '&&') { split(g.l); split(g.r); } else conj.push(g);
    };
    split(f);
    for (const c of conj) {
      if (c.k !== 'chain' || c.ops.length !== 1 || c.ops[0] !== '=') continue;
      const [l, r] = c.args.map(HL.unparen);
      if (r.k === 'var' && r.name === n && !HL.freeVars(l).has(n)) return l;
      if (l.k === 'var' && l.name === n && !HL.freeVars(r).has(n)) return r;
    }
    return null;
  }

  // outerVars: the variables of the precondition and the postcondition.
  function fromOutline(program, resolve, allVars, outerVars = new Set()) {
    const errors = [];
    const ALL = [...allVars];
    // The first assertion is the precondition: it is assumed, not checked.
    let started = false;
    const cut = (a, f) => {
      const enter = [{ k: 'havoc', vars: ALL }, { k: 'assume', f, cut: a.src }];
      if (!started) { started = true; return { k: 'seq', cs: enter }; }
      return { k: 'seq', cs: [{ k: 'assert', f, to: a.src }].concat(enter) };
    };

    function seq(s) {
      const items = s.k === 'seq' ? s.items : [s];
      const cs = [];
      let prevAssert = null;
      for (const it of items) {
        if (it.k === 'assert') {
          const f = resolve(it);
          if (!f) { errors.push('The assertion {' + it.src + '} has no value'); return null; }
          cs.push(cut(it, f));
          prevAssert = { node: it, f };
          continue;
        }
        if (it.k === 'while') {
          if (!prevAssert) {
            errors.push('The loop "while ' + HL.toText(it.c) + '" has no invariant written just before it in the annotated program');
            return null;
          }
          const body = seq(it.body);
          if (!body) return null;
          // With a variant, the body starts with {I && B && E = n}, where n
          // is the value of the variant when the iteration starts (rule
          // WHILE-TOTAL). The entry into the body chooses that value:
          // n := E. A logical variable of the first assertion of the body
          // that appears nowhere else is such a value.
          const firstIt = (it.body.items || []).find((x) => x.k === 'assert');
          if (firstIt) {
            const f0 = resolve(firstIt);
            const known = new Set([...HL.freeVars(prevAssert.f), ...HL.freeVars(it.c)]);
            HL.progVars(program).forEach((v) => known.add(v));
            outerVars.forEach((v) => known.add(v));
            const fresh = f0 ? [...HL.freeVars(f0)].filter((v) => !known.has(v)) : [];
            for (const n of fresh) {
              const witness = findWitness(f0, n);
              if (witness) body.cs.unshift({ k: 'assign', x: n, e: witness, text: n + ' := ' + HL.toText(witness), hidden: true });
            }
          }
          cs.push({ k: 'choice', cs: [
            { k: 'seq', cs: [
              { k: 'assume', f: it.c, cond: HL.toText(it.c) },
              body,
              { k: 'assert', f: prevAssert.f, to: prevAssert.node.src, back: true },
              { k: 'assume', f: N.bool(false) }
            ] },
            { k: 'assume', f: N.un('!', N.paren(it.c)), cond: '!(' + HL.toText(it.c) + ')' }
          ] });
          prevAssert = null;
          continue;
        }
        const c = stmt(it);
        if (!c) return null;
        cs.push(c);
        prevAssert = null;
      }
      return { k: 'seq', cs };
    }

    function stmt(s) {
      switch (s.k) {
        case 'skip': return { k: 'seq', cs: [] };
        case 'assign': {
          const text = HL.progInlineText({ k: 'seq', items: [s] });
          return { k: 'seq', cs: reads(s.e, text).concat([{ k: 'assign', x: s.x, e: s.e, text }]) };
        }
        case 'aassign': {
          const text = HL.progInlineText({ k: 'seq', items: [s] });
          const defs = reads(s.i, text).concat(reads(s.e, text));
          defs.push({ k: 'assert', f: N.call('def', [N.idx(N.v(s.a), s.i)]), def: text });
          return { k: 'seq', cs: defs.concat([{ k: 'assign', x: s.a, e: N.store(N.v(s.a), s.i, s.e), text }]) };
        }
        case 'if': {
          const t = seq(s.t);
          const e = s.e ? seq(s.e) : { k: 'seq', cs: [] };
          if (!t || !e) return null;
          return { k: 'choice', cs: [
            { k: 'seq', cs: [{ k: 'assume', f: s.c, cond: HL.toText(s.c) }, t] },
            { k: 'seq', cs: [{ k: 'assume', f: N.un('!', N.paren(s.c)), cond: '!(' + HL.toText(s.c) + ')' }, e] }
          ] };
        }
        case 'seq': return seq(s);
        default:
          errors.push('This statement is not supported by the prover');
          return null;
      }
    }

    // The definedness of the reads of an expression, as in ARRAY-READ.
    function reads(e, text) {
      const out = [];
      const walk = (n) => {
        if (!n || typeof n !== 'object') return;
        if (n.k === 'idx') out.push({ k: 'assert', f: N.call('def', [n]), def: text });
        for (const key of ['e', 'l', 'r', 'a', 'i', 'v', 'body', 'lo', 'hi']) if (n[key] && n[key].k) walk(n[key]);
        if (n.args) n.args.forEach(walk);
      };
      walk(e);
      return out;
    }

    const cmd = seq(program);
    return { cmd, errors };
  }

  // ------------------------------------------------------------------
  // Generation of the checks
  // ------------------------------------------------------------------

  let fresh = 0;

  // A check: hypotheses ==> goal, with the information needed to name it.
  //   to      the assertion it reaches (or the access whose definedness it checks)
  //   from    the assertion it starts from (filled in at the cut)
  //   conds   the conditions of the paths taken after that assertion
  //   via     the statements executed after that assertion
  //   closed  true once a "havoc" of all its variables has been passed
  function checks(cmd, after) {
    switch (cmd.k) {
      case 'assert':
        return [{ hyps: [], goal: cmd.f, to: cmd.to, def: cmd.def, back: !!cmd.back, from: null, conds: [], via: [], closed: false }].concat(after);
      case 'assume':
        // An assume that follows a "havoc" of all the variables is a cut:
        // the checks after it start from its formula alone.
        return after.map((o) => {
          if (o.closed) return o;
          // "assume false" ends a path: the checks after it are never reached.
          if (cmd.f.k === 'bool' && cmd.f.v === false) return Object.assign({}, o, { dead: true });
          const r = Object.assign({}, o, { hyps: [cmd.f].concat(o.hyps) });
          if (cmd.cut != null) { r.from = cmd.cut; r.closed = true; }
          if (cmd.cond != null) r.conds = [cmd.cond].concat(o.conds);
          return r;
        });
      case 'assign':
        return after.map((o) => (o.closed ? o : Object.assign({}, o, {
          hyps: o.hyps.map((h) => HL.substituteNode(h, cmd.x, cmd.e)),
          goal: HL.substituteNode(o.goal, cmd.x, cmd.e),
          via: cmd.hidden ? o.via : [cmd.text].concat(o.via),
          conds: cmd.hidden ? [cmd.text.replace(':=', '=')].concat(o.conds) : o.conds
        })));
      case 'havoc':
        return after.map((o) => {
          if (o.closed) return o;
          // Renaming the variables makes the check hold for all their values.
          let hyps = o.hyps;
          let goal = o.goal;
          for (const v of cmd.vars) {
            const nv = N.v(v + '#' + (++fresh));
            hyps = hyps.map((h) => HL.substituteNode(h, v, nv));
            goal = HL.substituteNode(goal, v, nv);
          }
          return Object.assign({}, o, { hyps, goal, renamed: true });
        });
      case 'seq': {
        let out = after;
        for (let j = cmd.cs.length - 1; j >= 0; j--) out = checks(cmd.cs[j], out);
        return out;
      }
      case 'choice': {
        // The checks after the choice are shared by both paths: keep each
        // closed one once.
        const seen = new Set();
        const out = [];
        for (const c of cmd.cs) {
          for (const o of checks(c, after)) {
            if (seen.has(o)) continue;
            seen.add(o);
            out.push(o);
          }
        }
        return out;
      }
      default:
        throw new Error('Unknown command ' + cmd.k);
    }
  }

  // The name of a check, in the terms of the annotated program.
  function describe(o) {
    const from = o.from == null ? 'the start' : '{' + o.from + '}';
    const conds = o.conds.length ? ' with ' + o.conds.join(' and ') : '';
    const via = o.via.length ? ' ' + o.via.join('; ') : '';
    if (o.def) return 'From ' + from + conds + ': the array access of ' + o.def + ' is defined';
    if (o.back) return 'From ' + from + conds + via + ': back to the invariant {' + o.to + '}';
    if (!o.via.length) return from + conds + ' implies {' + o.to + '}';
    return from + conds + via + ' {' + o.to + '}';
  }

  // The checks of an annotated program, closed and named.
  function outlineChecks(program, resolve, allVars, outerVars) {
    fresh = 0;
    const { cmd, errors } = fromOutline(program, resolve, allVars, outerVars);
    if (!cmd) return { errors, checks: [] };
    const list = checks(cmd, []).filter((o) => !o.dead);
    // The checks that start at the beginning of the program (before any
    // assertion) are not part of the proof outline: the first assertion is
    // the precondition.
    const named = list.filter((o) => o.from != null).map((o) => Object.assign(o, { name: describe(o) }));
    const open = list.filter((o) => o.from == null);
    open.forEach((o) => errors.push('A check does not start from an assertion: ' + describe(o)));
    return { errors, checks: named };
  }

  HL.IVL = { fromOutline, checks, outlineChecks, describe };
})(typeof window !== 'undefined' ? window : globalThis);
