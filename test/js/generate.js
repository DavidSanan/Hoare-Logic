/*
 * generate.js
 *
 * Builds the proof of a triple with the weakest precondition calculus, in
 * the exercise format, so that the step viewer can show it. Used by the wp
 * calculator.
 *
 * The proof follows the method of the exercises:
 *   - the weakest precondition is calculated from the last statement
 *     backwards, one statement per step, and every intermediate assertion
 *     R1, R2, ... is written in the annotated program;
 *   - a conditional gets one step per branch and one step that combines
 *     them: (B ==> wp(c1, Q)) && (!B ==> wp(c2, Q));
 *   - a loop needs an invariant I. Its steps are the invariant, the
 *     initialisation (the statements before the loop and P ==> ...), the
 *     preservation ({I && B} body {I}, calculated backwards from I, then
 *     I && B ==> wp(body, I)) and the conclusion (I && !B ==> Q);
 *   - the last step uses the consequence rule: P ==> wp(program, Q).
 *
 * The implications are proved by the prover of the site (prover.js, with
 * Z3) when the viewer shows the proof.
 */
(function (root) {
  'use strict';
  const HL = (root.HL = root.HL || {});

  const T = (n) => HL.toText(n);

  // generateProof(progSrc, preSrc, postSrc, invariantSrcs) returns
  // { ex } with the exercise object, or { error } with a message.
  HL.generateProof = function (progSrc, preSrc, postSrc, invSrcs) {
    let prog, post, pre = null;
    const invs = [];
    try { prog = HL.parseProgram(progSrc); } catch (e) { return { error: 'The program could not be read: ' + e.message }; }
    try { post = HL.parseFormula(postSrc); } catch (e) { return { error: 'The postcondition could not be read: ' + e.message }; }
    if (preSrc.trim()) {
      try { pre = HL.parseFormula(preSrc); } catch (e) { return { error: 'The precondition could not be read: ' + e.message }; }
    }
    for (const src of invSrcs) {
      try { invs.push(HL.parseFormula(src)); } catch (e) { return { error: 'The invariant "' + src + '" could not be read: ' + e.message }; }
    }

    // Number the statements in program order: s1, s2, ...; count the loops.
    let nStmt = 0;
    const loops = [];
    HL.walkStmts(prog, (s) => {
      if (s.k === 'assert') return;
      s.genLabel = 's' + (++nStmt);
      if (s.k === 'while') loops.push(s);
    });
    if (loops.length > invs.length) {
      return { error: 'The program has ' + loops.length + ' loop' + (loops.length > 1 ? 's' : '') + ' but ' + invs.length +
        ' invariant' + (invs.length === 1 ? '' : 's') + ' were given. Give one invariant per loop, in the order of the loops.' };
    }
    loops.forEach((l, j) => {
      l.genInv = invs[j];
      l.genName = loops.length === 1 ? 'I' : 'I' + (j + 1);
    });

    let nSlot = 0;
    const slot = () => 'R' + (++nSlot);

    const stepText = [];
    const step = (o) => {
      const lines = ['step: ' + o.title];
      if (o.part) lines.push('part: ' + o.part);
      if (o.rule) lines.push('rule: ' + o.rule);
      if (o.focus) lines.push('focus: ' + o.focus.join(', '));
      if (o.text) lines.push('text:', ...o.text.split('\n').map((l) => '  ' + l));
      if (o.set0) lines.push('set: ' + o.set0);
      if (o.calc) lines.push('calc:', ...o.calc.map((l) => '  ' + l));
      if (o.set) lines.push('set: ' + o.set);
      // The implication is proved by the prover of the site (Z3) when the
      // proof is shown; its status is not decided here.
      if (o.vc) lines.push('vc: ' + T(o.vc.h) + ' ==> ' + T(o.vc.c));
      return lines.join('\n');
    };

    // The steps are collected in "out". The preservation and conclusion of
    // a loop at the top level wait in "pending" until its initialisation is
    // complete, so that the order is: invariant, initialisation,
    // preservation, conclusion.
    let out = [];
    let pending = null;
    let topLevel = true;
    const simp = (f) => HL.simplify(f);

    // Annotate a sequence for the postcondition (name, formula). Returns the
    // name and formula of its weakest precondition, and its lines.
    function seq(items, postName, postF, depth, partHere) {
      const stmts = items.filter((s) => s.k !== 'assert');
      let cur = { name: postName, f: postF };
      const blocks = [];
      for (let j = stmts.length - 1; j >= 0; j--) {
        const r = stmt(stmts[j], cur, depth, j < stmts.length - 1, partHere);
        blocks.unshift({ pre: r.pre, lines: r.lines, isLoop: r.isLoop });
        cur = r.pre;
      }
      const lines = [];
      blocks.forEach((b, j) => {
        // The loop prints its own invariant before it.
        if (!b.isLoop) lines.push(ind(depth) + '{' + b.pre.name + '}');
        const ls = b.lines.slice();
        if (j < blocks.length - 1) {
          // The ";" goes after the statement, not after the assertions
          // that a loop prints after itself.
          let k = ls.length - 1;
          while (k > 0 && /^\s*\{.*\}\s*$/.test(ls[k])) k--;
          ls[k] = addSemi(ls[k]);
        }
        lines.push(...ls);
      });
      return { pre: cur, lines };
    }

    const ind = (d) => '  '.repeat(d);
    // A ";" goes before the label comment of the last line.
    const addSemi = (line) => {
      const k = line.indexOf('   // ');
      return k < 0 ? line + ';' : line.slice(0, k) + ';' + line.slice(k);
    };

    function part(partHere) {
      if (partHere) return partHere;
      return topLevel && pending ? 'Initialisation' : '';
    }

    function stmt(s, post, depth, notLast, partHere) {
      const lbl = '   // ' + s.genLabel;
      switch (s.k) {
        case 'skip': {
          const name = slot();
          out.push(step({
            title: name + ', the weakest precondition of skip', part: part(partHere), rule: 'SKIP', focus: [s.genLabel],
            text: '`skip` does not change the state, so its weakest precondition is its postcondition $' + post.name + '$.',
            calc: ['wp(skip, ' + post.name + ')', '= ' + T(post.f) + '   // wp(skip, Q) = Q'], set: name + ' = ' + T(post.f)
          }));
          return { pre: { name, f: post.f }, lines: [ind(depth) + 'skip' + lbl] };
        }
        case 'assign':
        case 'aassign': {
          const name = slot();
          const sText = HL.progInlineText({ k: 'seq', items: [s] });
          const raw = HL.wp({ k: 'seq', items: [s] }, post.f);
          const res = simp(raw);
          const isArr = s.k === 'aassign';
          const target = isArr ? s.a + '[' + T(s.i) + ' |-> ' + T(s.e) + ']' : T(s.e);
          const v = isArr ? s.a : s.x;
          const reads = T(raw) !== T(HL.substitute(post.f, v, isArr ? HL.N.store(HL.N.v(s.a), s.i, s.e) : s.e));
          const calc = ['wp(' + sText + ', ' + post.name + ')',
            '= (' + T(post.f) + ')[' + v + ' <- ' + target + ']   // ' + post.name + ' is ' + T(post.f),
            '= ' + T(raw) + '   // ' + v + ' replaced by ' + target + (reads ? ', with the definedness of the array accesses' : '')];
          if (T(res) !== T(raw)) calc.push('= ' + T(res) + '   // simplified');
          out.push(step({
            title: name + ', the weakest precondition of ' + sText, part: part(partHere),
            rule: isArr ? 'ARRAY-ASSIGN' : reads ? 'ASSIGN, ARRAY-READ' : 'ASSIGN', focus: [s.genLabel],
            text: (isArr ? 'We substitute the array $' + v + '$ with the updated array $' + target + '$' : 'We substitute the variable $' + v + '$ with the assignment expression $' + T(s.e) + '$') +
              ' in $' + post.name + '$.',
            calc, set: name + ' = ' + T(res)
          }));
          return { pre: { name, f: res }, lines: [ind(depth) + sText + lbl] };
        }
        case 'if': {
          const t = seq(s.t.items, post.name, post.f, depth + 1, partHere);
          const e = s.e ? seq(s.e.items, post.name, post.f, depth + 1, partHere) : { pre: post, lines: [] };
          const name = slot();
          const comb = HL.N.bin('&&', HL.N.paren(HL.N.bin('==>', s.c, HL.N.v(t.pre.name))), HL.N.paren(HL.N.bin('==>', HL.N.un('!', HL.N.paren(s.c)), HL.N.v(e.pre.name))));
          const val = HL.N.bin('&&', HL.N.paren(HL.N.bin('==>', s.c, HL.N.paren(t.pre.f))), HL.N.paren(HL.N.bin('==>', HL.N.un('!', HL.N.paren(s.c)), HL.N.paren(e.pre.f))));
          const res = simp(val);
          const calc = [T(comb), '= ' + T(val) + '   // ' + t.pre.name + ' and ' + e.pre.name + ' replaced by their values'];
          if (T(res) !== T(val)) calc.push('= ' + T(res) + '   // simplified');
          out.push(step({
            title: name + ', the weakest precondition of the conditional', part: part(partHere), rule: 'IF', focus: [s.genLabel, t.pre.name, e.pre.name],
            text: 'The weakest precondition of `if B then c1 else c2` is $(B ==> wp(c1, Q)) && (!B ==> wp(c2, Q))$. Here $B$ is $' + T(s.c) + '$, $wp(c1, Q)$ is $' +
              t.pre.name + '$' + (s.e ? ' and $wp(c2, Q)$ is $' + e.pre.name + '$.' : ', and the missing else branch behaves as `skip`, so $wp(c2, Q)$ is $' + e.pre.name + '$.'),
            calc, set: name + ' = ' + T(res)
          }));
          const lines = [ind(depth) + 'if ' + T(s.c) + ' then {', ...withPre(t, depth + 1), ind(depth + 1) + '{' + post.name + '}'];
          if (s.e) lines.push(ind(depth) + '} else {', ...withPre(e, depth + 1), ind(depth + 1) + '{' + post.name + '}');
          lines.push(ind(depth) + '}' + lbl);
          return { pre: { name, f: res }, lines };
        }
        case 'while': {
          const I = s.genName;
          const inv = s.genInv;
          const B = T(s.c);
          const invStep = step({
            title: 'The invariant ' + I + ' of the loop', rule: 'WHILE-CONSEQUENCE', focus: [s.genLabel],
            text: 'The invariant of the loop `while ' + B + ' do ...` is given. The loop needs three checks: initialisation, preservation and conclusion.',
            set0: I + ' = ' + T(inv)
          });
          const nested = !topLevel || partHere;
          let presOut;
          const savedOut = out;
          const savedTop = topLevel;
          if (!nested) {
            if (pending) out.push(...pending);
            out.push(invStep);
            presOut = [];
          } else {
            out.push(invStep);
            presOut = out;
          }
          // Preservation: the body, backwards from I.
          out = presOut;
          topLevel = false;
          const body = seq(s.body.items, I, inv, depth + 1, nested ? partHere || 'Preservation' : 'Preservation');
          const IB = I + ' && ' + B;
          out.push(step({
            title: I + ' and B imply ' + body.pre.name, part: nested ? partHere || 'Preservation' : 'Preservation', rule: 'CONSEQUENCE',
            focus: [IB, body.pre.name],
            text: 'By the consequence rule, one iteration keeps the invariant when $' + I + ' && B$ implies $' + body.pre.name + '$.\n>>> «' + I + '» && «' + B + ' : B» ==> «' + body.pre.name + '»',
            vc: { h: HL.N.bin('&&', HL.N.paren(inv), HL.N.paren(s.c)), c: body.pre.f }
          }));
          // Conclusion
          const INB = I + ' && !(' + B + ')';
          out.push(step({
            title: I + ' and not B imply ' + post.name, part: nested ? partHere || 'Preservation' : 'Conclusion', rule: 'CONSEQUENCE',
            focus: [INB, post.name],
            text: 'When the loop stops, $' + I + '$ holds and the condition $B$ is false. This must imply $' + post.name + '$.\n>>> «' + I + '» && «!(' + B + ') : ¬B» ==> «' + post.name + '»',
            vc: { h: HL.N.bin('&&', HL.N.paren(inv), HL.N.un('!', HL.N.paren(s.c))), c: post.f }
          }));
          out = savedOut;
          topLevel = savedTop;
          if (!nested) pending = presOut;
          const lines = [ind(depth) + '{' + I + '}', ind(depth) + 'while ' + B + ' do {', ind(depth + 1) + '{' + IB + '}',
            ...withPre(body, depth + 1), ind(depth + 1) + '{' + I + '}', ind(depth) + '}' + lbl, ind(depth) + '{' + INB + '}'];
          return { pre: { name: I, f: inv }, lines, isLoop: true };
        }
        default:
          throw new Error('Unknown statement');
      }
    }

    // The lines of a sequence, with the assertion before its first statement.
    function withPre(r, depth) {
      return r.lines.length ? r.lines : [ind(depth) + '{' + r.pre.name + '}'];
    }

    let top;
    try {
      top = seq(prog.items || [prog], 'Q', post, 1, '');
    } catch (e) {
      return { error: e.message };
    }
    const progLines = [];
    if (pre) progLines.push('  {P}');
    progLines.push(...top.lines);
    progLines.push('  {Q}');

    if (pre) {
      out.push(step({
        title: 'P implies ' + top.pre.name, part: pending ? 'Initialisation' : '', rule: 'CONSEQUENCE', focus: ['P', top.pre.name],
        text: '$' + top.pre.name + '$ is the weakest precondition of the whole program for $Q$. By the consequence rule, the triple holds when the precondition $P$ implies it.\n>>> «P» ==> «' + top.pre.name + '»',
        vc: { h: pre, c: top.pre.f }
      }));
    }
    if (pending) out.push(...pending);

    const text = [
      'id: wp-calculator',
      'title: Weakest precondition',
      'pre: ' + (pre ? T(pre) : 'true'),
      'post: ' + T(post),
      'program:',
      ...progLines,
      '',
      out.join('\n\n')
    ].join('\n');
    const ex = HL.parseExercise(text, 'wp-calculator');
    ex.noPre = !pre;
    // The result of the last step comes from the proof of its implications.
    ex.generated = true;
    return { ex, text };
  };
})(typeof window !== 'undefined' ? window : globalThis);
