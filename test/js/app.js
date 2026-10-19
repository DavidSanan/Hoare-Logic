/*
 * app.js
 *
 * The user interface of the website: navigation between pages, the text
 * renderer, the rules, the exercise browser and step viewer, the wp
 * calculator and the page for writing exercises.
 */
(function () {
  'use strict';
  const HL = window.HL;
  const esc = HL.esc;
  const $ = (sel, el) => (el || document).querySelector(sel);
  const $$ = (sel, el) => Array.from((el || document).querySelectorAll(sel));

  const store = {
    get(k) { try { return window.localStorage.getItem(k); } catch (e) { return null; } },
    set(k, v) { try { window.localStorage.setItem(k, v); } catch (e) { /* storage unavailable */ } }
  };

  // ------------------------------------------------------------------
  // Text renderer
  // ------------------------------------------------------------------

  function formulaSpan(src) {
    let s = src.trim();
    let open = '', close = '';
    if (s.startsWith('\\{')) { open = '<span class="brace">{</span>'; s = s.slice(2); }
    if (s.endsWith('\\}')) { close = '<span class="brace">}</span>'; s = s.slice(0, -2); }
    const r = HL.renderLine(s);
    return '<span class="m">' + open + r.html + close + '</span>';
  }

  function codeSpan(src) {
    try {
      const p = HL.parseProgram(src);
      if (p.items.length && p.items.every((x) => x.k !== 'assert')) {
        return '<code class="prog">' + HL.progCodeHTML(p) + '</code>';
      }
    } catch (e) { /* not a program: show it as it is */ }
    return '<code>' + esc(src) + '</code>';
  }

  function inline(s) {
    let out = '';
    let i = 0;
    while (i < s.length) {
      const c = s[i];
      if (c === '\\' && i + 1 < s.length && '$`*|'.includes(s[i + 1])) {
        out += esc(s[i + 1]);
        i += 2;
        continue;
      }
      if (c === '$') {
        const j = s.indexOf('$', i + 1);
        if (j > i + 1) { out += formulaSpan(s.slice(i + 1, j)); i = j + 1; continue; }
      }
      if (s.startsWith('``', i)) {
        const j = s.indexOf('``', i + 2);
        if (j > i) { out += '<code class="lit">' + esc(s.slice(i + 2, j)) + '</code>'; i = j + 2; continue; }
      }
      if (c === '`') {
        const j = s.indexOf('`', i + 1);
        if (j > i) { out += codeSpan(s.slice(i + 1, j)); i = j + 1; continue; }
      }
      if (s.startsWith('**', i)) {
        const j = s.indexOf('**', i + 2);
        if (j > i) { out += '<strong>' + inline(s.slice(i + 2, j)) + '</strong>'; i = j + 2; continue; }
      }
      out += esc(c);
      i++;
    }
    return out;
  }

  // Split a table row at "|", except inside formulas and code.
  function splitRow(line) {
    const cells = [];
    let cur = '';
    let inMath = false, inCode = false;
    const t = line.trim().replace(/^\|/, '').replace(/\|$/, '');
    for (let i = 0; i < t.length; i++) {
      const c = t[i];
      if (c === '\\' && t[i + 1] === '|') { cur += '\\|'; i++; continue; }
      // A literal code span ``...`` is copied whole, so that the pipes in
      // it, as in ``||``, do not split the row.
      if (!inMath && !inCode && t.startsWith('``', i)) {
        const j = t.indexOf('``', i + 2);
        if (j > i) { cur += t.slice(i, j + 2); i = j + 1; continue; }
      }
      if (c === '$' && !inCode) inMath = !inMath;
      if (c === '`' && !inMath) inCode = !inCode;
      if (c === '|' && !inMath && !inCode) { cells.push(cur.trim()); cur = ''; continue; }
      cur += c;
    }
    cells.push(cur.trim());
    return cells;
  }

  function ruleFigure(premisesHTML, conclusionHTML, name) {
    return '<div class="rulefig"><div class="rf-body">' +
      '<div class="rf-prem">' + (premisesHTML.length ? premisesHTML.map((p) => '<span class="rf-item">' + p + '</span>').join('') : '<span class="rf-item rf-empty"></span>') + '</div>' +
      '<div class="rf-bar"></div>' +
      '<div class="rf-concl"><span class="rf-item">' + conclusionHTML + '</span></div>' +
      '</div>' + (name ? '<div class="rf-name">[' + esc(name) + ']</div>' : '') + '</div>';
  }

  function ruleFigureFor(rule) {
    return ruleFigure(rule.premises.map((p) => HL.renderLine(p).html), HL.renderLine(rule.conclusion).html, rule.id);
  }

  function displayLine(src) {
    if (/\s---\s/.test(src)) {
      const [prem, concl] = src.split(/\s---\s/);
      const premises = prem.split(/\s{3,}/).map((x) => x.trim()).filter(Boolean).map((x) => HL.renderLine(x).html);
      return ruleFigure(premises, HL.renderLine(concl.trim()).html, '');
    }
    return '<div class="disp">' + formulaSpan(src) + '</div>';
  }

  // A line whose parts carry a label that says where they come from:
  //   {«0 <= x <= 10 : I» && «x < 10 : B»} x := x + 1 {«0 <= x <= 10 : I»}
  // Each «formula : label» is drawn with its label below it. The text
  // between the labelled parts is drawn as braces, connectives and code.
  // While a step is drawn, «X» stands for the current value of the
  // assertion X of the annotated program, labelled X.
  let activeSlots = null;

  function labelPiece(body) {
    const t = body.trim();
    if (activeSlots && /^[A-Za-z][A-Za-z0-9_]*'*$/.test(t)) {
      const v = activeSlots.get(t);
      return '<span class="lab"><span class="lab-f">' + (v ? HL.toHTML(v.f) : HL.varHTML(t)) + '</span>' +
        (v ? '<span class="lab-t">' + HL.varHTML(t) + '</span>' : '') + '</span>';
    }
    const k = body.lastIndexOf(':');
    const f = k < 0 ? body : body.slice(0, k);
    const label = k < 0 ? '' : body.slice(k + 1).trim();
    return '<span class="lab"><span class="lab-f">' + HL.renderLine(f.trim()).html + '</span>' +
      (label ? '<span class="lab-t">' + inline(label) + '</span>' : '') + '</span>';
  }

  function looseSegment(s) {
    const t = s.trim();
    if (!t) return '';
    const ops = { '&&': '∧', '||': '∨', '==>': '⇒', '<=>': '⇔', '<==': '⇐' };
    if (ops[t]) return '<span class="op">' + ops[t] + '</span>';
    // A program is drawn as in the triples; anything else as a formula.
    try {
      const p = HL.parseProgram(t);
      if (p.items.length && p.items.every((x) => x.k !== 'assert')) return '<span class="seg">' + HL.progInlineHTML(p) + '</span>';
    } catch (e) { /* not a program */ }
    return '<span class="seg">' + HL.renderLine(t).html + '</span>';
  }

  function labelledHTML(src) {
    let out = '';
    let rest = src;
    while (rest.length) {
      const a = rest.indexOf('«');
      const b = a < 0 ? -1 : rest.indexOf('»', a);
      const head = a < 0 || b < 0 ? rest : rest.slice(0, a);
      // Braces in the text between labelled parts belong to triples.
      head.split(/([{}])/).forEach((seg) => {
        if (seg === '{' || seg === '}') out += '<span class="brace">' + seg + '</span>';
        else if (seg) out += looseSegment(seg);
      });
      if (a < 0 || b < 0) break;
      out += labelPiece(rest.slice(a + 1, b));
      rest = rest.slice(b + 1);
    }
    return '<div class="disp"><span class="m labelled">' + out + '</span></div>';
  }
  HL.labelledHTML = labelledHTML;

  function codeBlock(body) {
    try {
      const prog = HL.parseProgram(body);
      return '<div class="listing">' + HL.programLines(prog).map((l) => {
        const html = l.type === 'assert'
          ? '<span class="brace">{</span> ' + HL.toHTML(l.node.f) + ' <span class="brace">}</span>'
          : l.html;
        return '<div class="ln ' + (l.type === 'assert' ? 'assert' : '') + '" style="--d:' + l.depth + '">' + html + '</div>';
      }).join('') + '</div>';
    } catch (e) {
      return '<pre class="plain">' + esc(body) + '</pre>';
    }
  }

  const BLOCK_START = /^(#{2,4} |>>> |>> |!! |::rule |\||[-*] |\d+\. |```)/;

  function md(text) {
    if (!text) return '';
    const lines = text.replace(/\r/g, '').split('\n');
    let html = '';
    let i = 0;
    while (i < lines.length) {
      const t = lines[i].trim();
      if (!t) { i++; continue; }
      if (t.startsWith('```')) {
        const lang = t.slice(3).trim();
        const body = [];
        i++;
        while (i < lines.length && !lines[i].trim().startsWith('```')) body.push(lines[i++]);
        i++;
        html += lang === 'text' ? '<pre class="plain">' + esc(body.join('\n')) + '</pre>' : codeBlock(body.join('\n'));
        continue;
      }
      let m = t.match(/^(#{2,4}) (.*)$/);
      if (m) {
        const level = m[1].length + 1;
        const id = 'h-' + m[2].toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-|-$/g, '');
        html += '<h' + level + ' id="' + id + '">' + inline(m[2]) + '</h' + level + '>';
        i++;
        continue;
      }
      if (t.startsWith('>>> ')) {
        let block = '';
        while (i < lines.length && lines[i].trim().startsWith('>>> ')) block += labelledHTML(lines[i++].trim().slice(4));
        html += '<div class="display stack">' + block + '</div>';
        continue;
      }
      if (t.startsWith('>> ')) {
        let block = '';
        let figures = false;
        while (i < lines.length && lines[i].trim().startsWith('>> ')) {
          const src = lines[i++].trim().slice(3);
          if (/\s---\s/.test(src)) figures = true;
          block += displayLine(src);
        }
        html += '<div class="display' + (figures ? '' : ' stack') + '">' + block + '</div>';
        continue;
      }
      if (t.startsWith('!! ')) {
        const para = [t.slice(3)];
        i++;
        while (i < lines.length && lines[i].trim() && !BLOCK_START.test(lines[i].trim())) para.push(lines[i++].trim());
        html += '<aside class="note">' + inline(para.join(' ')) + '</aside>';
        continue;
      }
      if (t.startsWith('::rule ')) {
        const rule = HL.RULES.find((r) => r.id === t.slice(7).trim());
        if (rule) html += '<div class="display">' + ruleFigureFor(rule) + '</div>';
        i++;
        continue;
      }
      if (t.startsWith('|')) {
        const rows = [];
        while (i < lines.length && lines[i].trim().startsWith('|')) {
          const r = lines[i++].trim();
          if (/^\|[\s|:-]+\|$/.test(r)) continue;
          rows.push(splitRow(r));
        }
        html += '<div class="table-wrap"><table><thead><tr>' + rows[0].map((c) => '<th>' + inline(c) + '</th>').join('') +
          '</tr></thead><tbody>' + rows.slice(1).map((r) => '<tr>' + r.map((c) => '<td>' + inline(c) + '</td>').join('') + '</tr>').join('') +
          '</tbody></table></div>';
        continue;
      }
      if (/^[-*] /.test(t) || /^\d+\. /.test(t)) {
        const ordered = /^\d+\. /.test(t);
        const items = [];
        while (i < lines.length) {
          const u = lines[i].trim();
          if (!u) break;
          if ((ordered && /^\d+\. /.test(u)) || (!ordered && /^[-*] /.test(u))) {
            items.push(u.replace(/^([-*]|\d+\.) /, ''));
            i++;
          } else if (!BLOCK_START.test(u)) {
            items[items.length - 1] += ' ' + u;
            i++;
          } else break;
        }
        const tag = ordered ? 'ol' : 'ul';
        html += '<' + tag + '>' + items.map((x) => '<li>' + inline(x) + '</li>').join('') + '</' + tag + '>';
        continue;
      }
      const para = [t];
      i++;
      while (i < lines.length && lines[i].trim() && !BLOCK_START.test(lines[i].trim())) para.push(lines[i++].trim());
      html += '<p>' + inline(para.join(' ')) + '</p>';
    }
    return html;
  }
  HL.md = md;

  // ------------------------------------------------------------------
  // Exercises
  // ------------------------------------------------------------------

  // The exercise files hold the exercises and the examples of the rules.
  const ALL_FILES = (window.HL_EXERCISE_SOURCES || []).map((src) => HL.parseExercise(src.text, src.file));
  const EXERCISES = ALL_FILES.filter((e) => !e.exampleOf);
  const RULE_EXAMPLE_LIST = ALL_FILES.filter((e) => e.exampleOf);
  const byId = new Map(EXERCISES.map((e) => [e.id, e]));

  function topicRank(t) {
    const j = HL.TOPIC_ORDER.indexOf(t);
    return j < 0 ? HL.TOPIC_ORDER.length : j;
  }

  function levelDots(level) {
    let s = '';
    for (let j = 1; j <= 3; j++) s += '<span class="dot' + (j <= level ? ' on' : '') + '"></span>';
    return '<span class="level" title="Difficulty ' + level + ' of 3" aria-label="Difficulty ' + level + ' of 3">' + s + '</span>';
  }

  function slotValuesAt(ex, k) {
    const slots = new Map();
    if (ex.pre) slots.set('P', { f: ex.pre, step: 0 });
    if (ex.post) slots.set('Q', { f: ex.post, step: 0 });
    for (let j = 0; j < Math.min(k, ex.steps.length); j++) {
      for (const it of ex.steps[j].items) if (it.kind === 'set' && it.f) slots.set(it.name, { f: it.f, step: j + 1 });
    }
    return slots;
  }

  // The annotated program after step k. The statement of the step is
  // highlighted; the assertion computed by the step is marked as new, and
  // the assertions that the step uses are marked as used.
  function outlineHTML(ex, k) {
    if (!ex.program) return '<p class="muted">The program could not be read.</p>';
    const slots = slotValuesAt(ex, k);
    const step = k >= 1 && k <= ex.steps.length ? ex.steps[k - 1] : null;
    const focus = new Set(step ? step.focusIds || [] : []);
    const used = new Set(step ? step.focusAsserts || [] : []);
    const lines = HL.programLines(ex.program);
    // The postcondition of a focused statement is used by the step: it is
    // the assertion just after the statement (after its closing line).
    lines.forEach((l, j) => {
      if (l.type !== 'stmt' || !focus.has(l.node.id)) return;
      let end = j;
      if (l.node.k === 'if' || l.node.k === 'while') {
        for (let i = j + 1; i < lines.length; i++) if (lines[i].node === l.node) end = i;
      }
      const next = lines[end + 1];
      if (next && next.type === 'assert') used.add(next.node.aid);
    });
    return '<div class="listing outline">' + lines.map((l) => {
      const d = ' style="--d:' + l.depth + '"';
      if (l.type === 'assert') {
        const a = l.node;
        const mark = used.has(a.aid) ? ' used' : '';
        if (a.slot && (slots.has(a.slot) || ex.slotNames.includes(a.slot))) {
          const v = slots.get(a.slot);
          const tag = '<span class="slot-tag">' + HL.varHTML(a.slot) + '</span>';
          if (!v) return '<div class="ln assert pending' + mark + '"' + d + '>' + tag + '<span class="brace">{</span> <span class="q">?</span> <span class="brace">}</span></div>';
          const fresh = v.step === k && k > 0 ? ' fresh' : mark;
          return '<div class="ln assert' + fresh + '"' + d + '>' + tag + '<span class="brace">{</span> ' + HL.toHTML(v.f) + ' <span class="brace">}</span></div>';
        }
        // An assertion such as {I && x > 0}: the names of the assertions
        // already computed are replaced by their values, and the original
        // text stays in the tag.
        const known = [...HL.freeVars(a.f)].filter((v) => slots.has(v) && ex.slotNames.includes(v) || (v === 'P' || v === 'Q') && slots.has(v));
        if (known.length) {
          let g = a.f;
          for (const v of known) g = HL.substituteNode(g, v, HL.N.paren(slots.get(v).f));
          const tag = '<span class="slot-tag">' + HL.toHTML(a.f) + '</span>';
          return '<div class="ln assert' + mark + '"' + d + '>' + tag + '<span class="brace">{</span> ' + HL.toHTML(HL.simplifyParens(g)) + ' <span class="brace">}</span></div>';
        }
        return '<div class="ln assert' + mark + '"' + d + '><span class="brace">{</span> ' + HL.toHTML(a.f) + ' <span class="brace">}</span></div>';
      }
      const cls = focus.has(l.node.id) && l.type === 'stmt' ? ' focus' : '';
      const label = l.type === 'stmt' && l.node.label ? '<span class="label">' + esc(l.node.label) + '</span>' : '';
      return '<div class="ln ' + l.type + cls + '"' + d + '>' + l.html + label + '</div>';
    }).join('') + '</div>';
  }

  // The elements of the exercise, always shown above the annotated
  // program: the variables of the program, the logical variables, the
  // precondition and the postcondition, and the elements given by the file.
  function givenHTML(ex) {
    if (!ex.program) return '';
    const progVars = [...HL.progVars(ex.program)];
    const logical = [...new Set([...HL.freeVars(ex.pre || HL.N.bool(true)), ...HL.freeVars(ex.post || HL.N.bool(true))])]
      .filter((v) => !progVars.includes(v));
    const row = (label, html) => '<div><dt>' + label + '</dt><dd>' + html + '</dd></div>';
    const vars = (list) => list.map((v) => '<span class="m">' + HL.varHTML(v) + '</span>').join(', ');
    return '<dl class="given">' +
      row('Variables', vars(progVars) || '<span class="muted">none</span>') +
      (logical.length ? row('Logical variables', vars(logical)) : '') +
      (ex.noPre ? '' : row('Precondition P', '<span class="m">' + (ex.pre ? HL.toHTML(ex.pre) : esc(ex.preSrc)) + '</span>')) +
      row('Postcondition Q', '<span class="m">' + (ex.post ? HL.toHTML(ex.post) : esc(ex.postSrc)) + '</span>') +
      ex.given.map(([label, value]) => row(inline(label), inline(value))).join('') +
      '</dl>';
  }

  // The rule with the elements of the exercise. The premise that the
  // current step proves is highlighted; a click goes to its first step.
  function schemeHTML(ex, k) {
    if (!ex.scheme) return '';
    const step = k >= 1 && k <= ex.steps.length ? ex.steps[k - 1] : null;
    activeSlots = slotValuesAt(ex, k);
    const piece = (src) => labelledHTML(src).replace(/^<div class="disp">|<\/div>$/g, '');
    const prem = ex.scheme.premises.map((p) =>
      '<button type="button" class="rx-prem' + (step && p.part && step.part === p.part ? ' hl' : '') + '"' +
      (p.part ? ' data-part="' + esc(p.part) + '"' : '') + '><span class="rx-prem-f">' + piece(p.src) + '</span>' +
      (p.part ? '<span class="rx-prem-t">' + esc(p.part) + '</span>' : '') + '</button>').join('');
    const concl = piece(ex.scheme.conclusion);
    activeSlots = null;
    return '<div class="rx-rule"><span class="kicker">The rule with the elements of the example</span>' +
      '<div class="rulefig"><div class="rf-body"><div class="rf-prem">' + (prem || '<span class="rf-item rf-empty"></span>') +
      '</div><div class="rf-bar"></div><div class="rf-concl"><span class="rf-item">' + concl + '</span></div></div>' +
      (ex.scheme.name ? '<div class="rf-name">[' + esc(ex.scheme.name) + ']</div>' : '') + '</div></div>';
  }

  const REL_DISPLAY = { '<=>': '⇔', '⇔': '⇔', '≡': '≡', '===': '≡', '==>': '⇒', '⇒': '⇒', '=>': '⇒', '<==': '⇐', '⇐': '⇐', '==': '=', '=': '=' };

  function ruleChip(r) {
    return '<button type="button" class="chip rule-chip" data-rule="' + esc(r) + '">' + esc(r) + '</button>';
  }

  function itemHTML(it, step) {
    switch (it.kind) {
      case 'text': return '<div class="prose">' + md(it.text) + '</div>';
      case 'note': return '<aside class="note">' + md(it.text) + '</aside>';
      case 'result': return '<div class="result">' + md(it.text) + '</div>';
      case 'assume': return '<div class="assume"><span class="kicker">We use the assumption</span> ' + formulaSpan(it.src) + '</div>';
      case 'set':
        return '<div class="setline"><span class="kicker">New assertion</span><span class="m">' + HL.varHTML(it.name) +
          ' <span class="op">≡</span> ' + (it.f ? HL.toHTML(it.f) : HL.looseHTML(it.src)) + '</span></div>';
      case 'calc':
        // The last line of a calculation is its result, and is highlighted.
        // The last column shows whether the prover proved the line.
        return '<div class="calc table-wrap"><table>' + it.rows.map((r, j) => '<tr' + (j && j === it.rows.length - 1 ? ' class="last"' : '') + '>' +
          '<td class="rel">' + (j ? (REL_DISPLAY[r.sym] || '=') : '') + '</td>' +
          '<td class="fm"><span class="m">' + (r.f ? HL.toHTML(r.f) : HL.looseHTML(r.src)) + '</span></td>' +
          '<td class="why">' + (r.why ? whyHTML(r.why) : '') + '</td>' +
          '<td class="pst">' + (j ? proofMark(r) : '') + '</td></tr>').join('') + '</table></div>';
      case 'vc': {
        const body = it.node ? (it.node.k === 'triple' ? HL.tripleHTML(it.node) : HL.toHTML(it.node.f)) : HL.looseHTML(it.src);
        // The badge gives the answer of the prover. Before it is known, or
        // when the prover cannot run, it gives the answer of the exercise.
        const pr = proofOf(it);
        let holds, badge;
        if (pr && pr.status === 'proved') { holds = true; badge = '<span class="badge ok">proved</span>'; }
        else if (pr && pr.status === 'refuted' && pr.confirmed) { holds = false; badge = '<span class="badge bad">does not hold</span>'; }
        else if (pr && pr.status === 'pending') { holds = it.status !== 'fails'; badge = '<span class="badge muted-badge">proving…</span>'; }
        else if (pr) { holds = null; badge = '<span class="badge warn">not decided</span>'; }
        else if (activeGenerated) { holds = null; badge = '<span class="badge warn">not proved</span>'; }
        else { holds = it.status !== 'fails'; badge = '<span class="badge ' + (holds ? 'ok' : 'bad') + '">' + (holds ? 'holds' : 'does not hold') + '</span>'; }
        let s = '<div class="vc ' + (holds === false ? 'fails' : holds ? 'holds' : 'open') + '"><div class="vc-head"><span class="kicker">Verification condition</span>' +
          badge + '</div><div class="vc-body"><span class="m">' + body + '</span></div>';
        if (it.why) s += '<div class="prose">' + md(it.why) + '</div>';
        if (pr && pr.status === 'refuted' && pr.confirmed) {
          s += '<div class="cex"><span class="kicker">Counterexample found by Z3</span> ' + stateHTML(pr.state) + '</div>';
        } else if (it.counterexample) {
          s += '<div class="cex"><span class="kicker">Counterexample</span> ' + stateHTML(it.counterexample) + '</div>';
        }
        if (pr && pr.ok === false) s += '<p class="bad small">The prover does not agree with the exercise on this condition.</p>';
        if (pr && (pr.status === 'unknown' || pr.status === 'error' || pr.status === 'skip') && pr.reason) s += '<p class="muted small">' + esc(pr.reason) + '</p>';
        return s + '</div>';
      }
      case 'instance': {
        const prem = it.premises.map((p) => (p.node ? lineHTML(p.node) : HL.looseHTML(p.src)));
        const concl = it.conclusion ? (it.conclusion.node ? lineHTML(it.conclusion.node) : HL.looseHTML(it.conclusion.src)) : '';
        return '<div class="instance"><span class="kicker">Rule applied</span><div class="display">' +
          ruleFigure(prem, concl, it.name || (step.rules[0] || '')) + '</div></div>';
      }
      default: return '';
    }
  }

  // A justification is plain text in which the operators are drawn as
  // symbols, so that "x >= x" reads as in the formulas.
  function whyHTML(t) {
    let s = inline(t);
    const rep = [['&lt;=&gt;', '⇔'], ['==&gt;', '⇒'], ['|-&gt;', '↦'], ['&lt;-', '←'], ['&amp;&amp;', '∧'], ['||', '∨'],
      ['!=', '≠'], ['&lt;=', '≤'], ['&gt;=', '≥'], [' * ', ' · '], ['!(', '¬(']];
    for (const [a, b] of rep) s = s.split(a).join(b);
    return s;
  }

  function lineHTML(node) {
    return node.k === 'triple' ? HL.tripleHTML(node) : HL.toHTML(node.f);
  }

  function stateHTML(env) {
    return '<span class="state">' + Object.entries(env).map(([k, v]) => '<span class="m">' + HL.varHTML(k) + ' = ' +
      (Array.isArray(v) ? '[' + v.join(', ') + ']' : esc(HL.valueText(v)).replace(/^-/, '−')) + '</span>').join(', ') + '</span>';
  }

  function stepCardHTML(ex, step, final) {
    activeSlots = slotValuesAt(ex, step.index);
    activeProofState = proofs.get(ex.orig || ex) || null;
    activeGenerated = !!ex.generated;
    const html = '<article class="step-card">' +
      '<header><span class="kicker">Step ' + esc(step.number || String(step.index)) + (step.part ? ' · ' + esc(step.part) : '') + '</span>' +
      '<h3>' + inline(step.title) + '</h3>' +
      (step.rules.length ? '<div class="chips">' + step.rules.map(ruleChip).join('') + '</div>' : '') + '</header>' +
      step.items.map((it) => itemHTML(it, step)).join('') + (final || '') + '</article>';
    activeSlots = null;
    activeProofState = null;
    activeGenerated = false;
    return html;
  }

  function specHTML(ex) {
    return '<div class="spec">' +
      '<div class="spec-row"><span class="kicker">Precondition</span><span class="m">' + (ex.pre ? HL.toHTML(ex.pre) : esc(ex.preSrc)) + '</span></div>' +
      '<div class="spec-row"><span class="kicker">Postcondition</span><span class="m">' + (ex.post ? HL.toHTML(ex.post) : esc(ex.postSrc)) + '</span></div>' +
      '</div>';
  }

  function problemHTML(ex) {
    const toFind = ex.slotNames.filter((n) => n !== 'P' && n !== 'Q');
    return '<article class="step-card">' +
      '<header><span class="kicker">The problem</span><h3>' + inline(ex.title) + '</h3></header>' +
      '<div class="prose">' + md(ex.task) + '</div>' +
      (toFind.length ? '<p class="muted">The proof fills in ' + (toFind.length === 1 ? 'the assertion ' : 'the assertions ') +
        toFind.map((n) => '<span class="m">' + HL.varHTML(n) + '</span>').join(', ') + ' of the annotated program.</p>' : '') +
      (ex.hint ? '<details class="hint"><summary>Hint</summary><div class="prose">' + md(ex.hint) + '</div></details>' : '') +
      '<p class="muted">Try the exercise yourself first. Then go through the steps of the solution with the arrows or the left and right keys.</p>' +
      '</article>';
  }

  function summaryHTML(ex) {
    const slots = slotValuesAt(ex, ex.steps.length);
    const rules = [];
    ex.steps.forEach((s) => s.rules.forEach((r) => { if (!rules.includes(r)) rules.push(r); }));
    const names = ex.slotNames.filter((n) => slots.has(n));
    let s = '<article class="step-card">' +
      '<header><span class="kicker">Summary</span><h3>' + inline(ex.title) + '</h3></header>';
    if (ex.verdict) {
      s += '<div class="verdict ' + (ex.verdict === 'valid' ? 'ok' : 'bad') + '">' +
        (ex.verdict === 'valid' ? 'The triple is valid.' : 'The triple is not valid.') + '</div>';
    }
    if (names.length) {
      s += '<h4>Assertions of the proof</h4><div class="table-wrap"><table class="slots"><tbody>' + names.map((n) =>
        '<tr><th><span class="m">' + HL.varHTML(n) + '</span></th><td><span class="m">' + HL.toHTML(slots.get(n).f) + '</span></td></tr>').join('') +
        '</tbody></table></div>';
    }
    if (rules.length) s += '<h4>Rules used</h4><div class="chips">' + rules.map(ruleChip).join('') + '</div>';
    if (ex.summary) s += '<div class="prose">' + md(ex.summary) + '</div>';
    const st = proofs.get(ex.orig || ex);
    s += '<div class="test-block proof-block"><h4>Proof of this solution</h4><p class="muted">Every claim of the solution is proved with the SMT solver Z3: every line of every calculation, every verification condition, and every check of the annotated program, which are those of the rules of the course. A proved claim holds in every state.</p>' +
      (st && st.state === 'done' ? proofReportHTML(st.results) : st && st.state === 'error' ? '<p class="bad">' + esc(st.message) + '</p>' : '<p class="muted">The proof is running.</p>') + '</div>';
    s += '<div class="test-block"><h4>Test this solution</h4><p class="muted">The test runs the program and evaluates every claim of the steps on many small states. It does not prove anything: a passing test means that no counterexample was found among the states that were tried.</p>' +
      '<button type="button" class="btn ghost run-tests">Run the tests</button><div class="test-report"></div></div>';
    return s + '</article>';
  }

  // ------------------------------------------------------------------
  // Test report
  // ------------------------------------------------------------------

  function reportHTML(results) {
    const okN = results.filter((r) => r.ok === true).length;
    const badN = results.filter((r) => r.ok === false).length;
    const expN = results.filter((r) => r.status === 'expected').length;
    const otherN = results.length - okN - badN - expN;
    let s = '<div class="report-summary"><span class="badge ok">' + okN + ' passed</span>' +
      (badN ? '<span class="badge bad">' + badN + ' failed</span>' : '') +
      (expN ? '<span class="badge ok">' + expN + ' failed as expected</span>' : '') +
      (otherN ? '<span class="badge warn">' + otherN + ' not conclusive</span>' : '') + '</div>';
    const groups = [];
    for (const r of results) {
      let g = groups.find((x) => x.name === r.group);
      if (!g) groups.push((g = { name: r.group, items: [] }));
      g.items.push(r);
    }
    for (const g of groups) {
      s += '<div class="report-group"><h5>' + esc(g.name) + '</h5><ul>';
      for (const r of g.items) {
        const cls = r.ok === true || r.status === 'expected' ? 'ok' : r.ok === false ? 'bad' : 'warn';
        const icon = r.ok === true || r.status === 'expected' ? '✓' : r.ok === false ? '✗' : '?';
        let detail = '';
        const tested = r.sat != null ? r.sat + ' state' + (r.sat === 1 ? '' : 's') : '';
        if (r.status === 'pass' && r.expect !== 'fails') {
          detail = r.kind === 'counterexample' ? 'The counterexample breaks the claim, as stated.' :
            'No counterexample among ' + tested + (r.kind === 'triple' ? ' that satisfy the precondition.' : r.kind === 'equivalence' ? ' compared.' : ' that satisfy the left-hand side.');
        } else if (r.status === 'fail' && r.expect === 'fails') {
          detail = 'A counterexample was found, as the exercise states: ' + stateHTML(r.cex) + (r.final ? ', which ends in ' + stateHTML(r.final) : '') + '.';
        } else if (r.status === 'fail') {
          detail = (r.reason ? esc(r.reason) + ' ' : '') + (r.cex ? 'State: ' + stateHTML(r.cex) : '') +
            (r.final ? '. Final state: ' + stateHTML(r.final) : '') +
            (r.values ? '. The two lines give ' + r.values.map((v) => esc(HL.valueText(v))).join(' and ') : '') + '.';
        } else if (r.status === 'pass' && r.expect === 'fails') {
          detail = 'The exercise says that this does not hold, but no counterexample was found among ' + tested + '.';
        } else if (r.status === 'expected') {
          detail = esc(r.reason) + (r.cex ? ' State: ' + stateHTML(r.cex) + '.' : '');
        } else if (r.status === 'vacuous') {
          detail = 'Not conclusive: ' + (r.reason ? esc(r.reason) : 'no tested state satisfied the hypothesis, so the test says nothing.');
        } else {
          detail = 'Not tested: ' + esc(r.reason || '');
        }
        s += '<li class="' + cls + '"><span class="icon" aria-hidden="true">' + icon + '</span><div><div class="what">' + esc(r.item) +
          (r.line ? ' <span class="muted">(line ' + r.line + ')</span>' : '') + '</div><div class="detail">' + detail + '</div></div></li>';
      }
      s += '</ul></div>';
    }
    return s;
  }

  // ------------------------------------------------------------------
  // The step viewer
  // ------------------------------------------------------------------

  // ------------------------------------------------------------------
  // The prover: Z3, compiled to WebAssembly, proves the claims of the
  // solution (smt.js, ivl.js, prover.js). Z3 is loaded the first time it is
  // needed. It uses threads, which browsers allow only on pages that are
  // "cross-origin isolated"; on GitHub Pages the service worker
  // coi-serviceworker.js makes the page isolated.
  // ------------------------------------------------------------------

  let solverPromise = null;
  let proofQueue = Promise.resolve();

  function loadScript(src) {
    return new Promise((resolve, reject) => {
      const el = document.createElement('script');
      el.src = src;
      el.onload = resolve;
      el.onerror = () => reject(new Error('The file ' + src + ' could not be loaded'));
      document.head.appendChild(el);
    });
  }

  function getSolver() {
    if (!solverPromise) {
      solverPromise = (async () => {
        if (!window.crossOriginIsolated) {
          throw new Error('The browser does not allow Z3 to run on this page, because the page is not cross-origin isolated. Reload the page once; if the message stays, the browser does not support it.');
        }
        await loadScript('z3/z3-built.js');
        await loadScript('z3/z3-lowlevel.js');
        const Z3 = await window.HLZ3init();
        const ctx = Z3.mk_context(Z3.mk_config());
        return { run: (text) => Z3.eval_smtlib2_string(ctx, text) };
      })();
      solverPromise.catch(() => { solverPromise = null; });
    }
    return solverPromise;
  }

  // The proofs, computed once per exercise, in the background. The state
  // of a proof: { state: 'running' | 'done' | 'error', results, byRef,
  // message }. byRef gives the result of each claim of a step (a line of a
  // calculation, a verification condition, a line of a rule instance).
  const proofs = new WeakMap();
  let activeProofState = null;
  // True while a step of the wp calculator is drawn: its conditions have no
  // answer of their own, only the one of the prover.
  let activeGenerated = false;

  function proofOf(ref) {
    if (!activeProofState) return null;
    if (activeProofState.state === 'running') return activeProofState.byRef.get(ref) || { status: 'pending' };
    return activeProofState.byRef.get(ref) || null;
  }

  function proofMark(row) {
    const pr = proofOf(row);
    if (!pr) return '';
    if (pr.status === 'pending') return '<span class="pmark pending" title="Proving">…</span>';
    if (pr.status === 'proved') return '<span class="pmark ok" title="Proved by Z3">✓</span>';
    if (pr.status === 'refuted' && pr.confirmed) return '<span class="pmark bad" title="Refuted by Z3">✗</span>';
    return '<span class="pmark warn" title="' + esc(pr.reason || 'Not decided') + '">?</span>';
  }

  // Start the proof of an exercise; onChange is called when it progresses
  // and when it ends.
  function ensureProof(ex, onChange) {
    let st = proofs.get(ex);
    if (st) return st;
    st = { state: 'running', results: [], byRef: new Map(), listeners: onChange ? [onChange] : [], viewers: new Set() };
    proofs.set(ex, st);
    const notify = () => st.listeners.forEach((f) => f());
    proofQueue = proofQueue.then(async () => {
      try {
        const solver = await getSolver();
        let last = 0;
        st.results = await HL.Prover.proveExercise(ex, solver, {
          timeout: 4000,
          onProgress: (rs) => {
            rs.forEach((r) => { if (r.ref) st.byRef.set(r.ref, r); });
            st.results = rs;
            if (Date.now() - last > 400) { last = Date.now(); notify(); }
          }
        });
        st.results.forEach((r) => { if (r.ref) st.byRef.set(r.ref, r); });
        st.state = 'done';
      } catch (err) {
        st.state = 'error';
        st.message = err.message;
      }
      notify();
    });
    return st;
  }

  function proofCounts(results) {
    return {
      proved: results.filter((r) => r.status === 'proved').length,
      stated: results.filter((r) => (r.status === 'refuted' && r.ok) || r.status === 'expected').length,
      refuted: results.filter((r) => r.status === 'refuted' && r.confirmed).length,
      wrong: results.filter((r) => r.ok === false).length,
      open: results.filter((r) => r.status === 'unknown' || r.status === 'error').length
    };
  }

  // The line above the steps that says where the proof is.
  function proofStatusHTML(st, generated) {
    if (!st) return '';
    if (st.state === 'running') {
      return '<div class="proof-status running"><span class="spinner" aria-hidden="true"></span>' +
        (solverPromise ? 'Proving every claim with Z3' : 'Loading Z3 (about 32 MB the first time) to prove every claim') +
        (st.results.length ? ': ' + st.results.length + ' done' : '') + '…</div>';
    }
    if (st.state === 'error') {
      return '<div class="proof-status error">The claims were not proved: ' + esc(st.message) + '</div>';
    }
    const c = proofCounts(st.results);
    const parts = [c.proved + ' proved'];
    if (generated) {
      if (c.refuted) parts.push(c.refuted + ' refuted');
    } else if (c.stated) parts.push(c.stated + ' refuted, as the exercise states');
    if (!generated && c.wrong) parts.push(c.wrong + ' where the prover disagrees with the exercise');
    if (c.open) parts.push(c.open + ' not decided');
    const bad = generated ? c.refuted : c.wrong;
    return '<div class="proof-status ' + (bad ? 'bad' : c.open ? 'warn' : 'ok') + '">Proved with Z3: ' + parts.join(', ') + '.</div>';
  }

  function proofReportHTML(results) {
    const proved = results.filter((r) => r.status === 'proved').length;
    const stated = results.filter((r) => (r.status === 'refuted' && r.ok) || r.status === 'expected').length;
    const wrong = results.filter((r) => r.ok === false).length;
    const open = results.filter((r) => r.ok == null && r.status !== 'expected').length;
    let s = '<div class="report-summary"><span class="badge ok">' + proved + ' proved</span>' +
      (stated ? '<span class="badge ok">' + stated + ' refuted, as stated</span>' : '') +
      (wrong ? '<span class="badge bad">' + wrong + ' wrong</span>' : '') +
      (open ? '<span class="badge warn">' + open + ' not decided</span>' : '') + '</div>';
    const groups = [];
    for (const r of results) {
      let g = groups.find((x) => x.name === r.group);
      if (!g) groups.push((g = { name: r.group, items: [] }));
      g.items.push(r);
    }
    for (const g of groups) {
      s += '<div class="report-group"><h5>' + esc(g.name) + '</h5><ul>';
      for (const r of g.items) {
        const good = r.ok === true || r.status === 'expected';
        const cls = good ? 'ok' : r.ok === false ? 'bad' : 'warn';
        const icon = good ? '✓' : r.ok === false ? '✗' : '?';
        let detail;
        if (r.status === 'proved') detail = r.ok ? 'Proved: it holds in every state.' : 'Proved, but the exercise says that it does not hold.';
        else if (r.status === 'refuted') detail = (r.ok ? 'Refuted, as the exercise states. ' : 'Refuted. ') + 'Counterexample: ' + stateHTML(r.state) + '.';
        else if (r.status === 'expected') detail = esc(r.reason) + (r.state ? ' Counterexample: ' + stateHTML(r.state) + '.' : '');
        else if (r.status === 'unknown') detail = 'Not decided by the solver' + (r.reason ? ': ' + esc(r.reason) : '') + '.';
        else detail = esc(r.reason || 'Not proved.');
        s += '<li class="' + cls + '"><span class="icon" aria-hidden="true">' + icon + '</span><div><div class="what">' + esc(r.item) +
          '</div><div class="detail">' + detail + '</div></div></li>';
      }
      s += '</ul></div>';
    }
    return s;
  }

  // The viewer shows an exercise one step at a time. With several choices
  // (for example of invariant), it shows the steps of the chosen one.
  // Options: compact (no header, no summary: used for the examples of the
  // rules and for the wp calculator), onStep (called when the step changes).
  class Viewer {
    constructor(container, opts) {
      this.el = container;
      this.opts = opts || {};
      this.ex = null;
      this.c = 0;
      this.k = 0;
      this.all = false;
      this.el.addEventListener('click', (e) => this.onClick(e));
    }

    // The exercise with the steps of the current choice.
    view() {
      const choice = this.ex.choices[this.c] || this.ex.choices[0];
      return Object.assign({}, this.ex, { steps: choice.steps, choice, orig: this.ex });
    }

    last() {
      return this.view().steps.length + (this.opts.compact ? 0 : 1);
    }

    show(ex, k, c) {
      const same = this.ex === ex;
      this.ex = ex;
      this.c = Math.max(0, Math.min(c != null ? c : same ? this.c : 0, ex.choices.length - 1));
      this.k = Math.max(0, Math.min(k || 0, this.last()));
      this.render();
    }

    go(k) {
      if (!this.ex) return;
      this.k = Math.max(0, Math.min(k, this.last()));
      this.render();
      if (this.opts.onStep) this.opts.onStep(this.ex, this.k, this.c);
      const nav = $('.stepper', this.el);
      if (nav && nav.getBoundingClientRect().top < 0) nav.scrollIntoView({ block: 'start' });
    }

    onClick(e) {
      const b = e.target.closest('button');
      if (!b || !this.el.contains(b)) return;
      if (b.dataset.choice != null) {
        this.c = Number(b.dataset.choice);
        this.k = Math.min(this.k, this.last());
        this.render();
        if (this.opts.onStep) this.opts.onStep(this.ex, this.k, this.c);
      } else if (b.dataset.part != null) {
        const j = this.view().steps.findIndex((s) => s.part === b.dataset.part);
        if (j >= 0) this.go(j + 1);
      } else if (b.dataset.go != null) this.go(Number(b.dataset.go));
      else if (b.classList.contains('prev')) this.go(this.k - 1);
      else if (b.classList.contains('next')) this.go(this.k + 1);
      else if (b.classList.contains('toggle-all')) { this.all = !this.all; this.render(); }
      else if (b.classList.contains('run-tests')) this.runTests(b);

    }

    runTests(button) {
      const out = $('.test-report', button.parentElement);
      button.disabled = true;
      button.textContent = 'Testing…';
      setTimeout(() => {
        try {
          out.innerHTML = reportHTML(HL.Checker.checkExercise(this.ex));
        } catch (err) {
          out.innerHTML = '<p class="bad">The tests stopped with an error: ' + esc(err.message) + '</p>';
        }
        button.disabled = false;
        button.textContent = 'Run the tests again';
      }, 30);
    }

    // The buttons of the steps, grouped by part: 1, 2, 3.1, 3.2, 4, ...
    stepperHTML(ex, k) {
      const n = ex.steps.length;
      const compact = this.opts.compact;
      const btn = (j, label, title) => '<button type="button" data-go="' + j + '" class="sdot' + (label.length < 5 ? ' num' : '') +
        (k === j ? ' cur' : '') + (j > 0 && j < k ? ' done' : '') + '" title="' + esc(title) + '">' + esc(label) + '</button>';
      const parts = [btn(0, 'Problem', 'The problem')];
      let j = 0;
      while (j < n) {
        const part = ex.steps[j].part;
        let e = j + 1;
        while (part && e < n && ex.steps[e].part === part) e++;
        const buttons = [];
        for (let i = j; i < e; i++) buttons.push(btn(i + 1, ex.steps[i].number || String(i + 1), ex.steps[i].title));
        parts.push(part ? '<span class="sgroup' + (k > j && k <= e ? ' cur' : '') + '"><span class="sg-label">' + esc(part) + '</span>' +
          '<span class="sg-btns">' + buttons.join('') + '</span></span>' : buttons.join(''));
        j = e;
      }
      if (!compact) parts.push(btn(n + 1, 'Summary', 'Summary and tests'));
      return '<nav class="stepper" aria-label="Steps of the solution">' +
        '<button type="button" class="btn ghost prev"' + (k === 0 || this.all ? ' disabled' : '') + ' aria-label="Previous step">←</button>' +
        '<div class="sdots">' + parts.join('') + '</div>' +
        '<button type="button" class="btn ghost next"' + (k === this.last() || this.all ? ' disabled' : '') + ' aria-label="Next step">→</button>' +
        (compact ? '' : '<button type="button" class="btn ghost toggle-all">' + (this.all ? 'One step at a time' : 'Show all steps') + '</button>') +
        '</nav>';
    }

    choicesHTML() {
      const ex = this.ex;
      if (ex.choices.length < 2) return '';
      let loops = false;
      if (ex.program) HL.walkStmts(ex.program, (s) => { if (s.k === 'while') loops = true; });
      return '<div class="choice-bar"><span class="kicker">' + (loops ? 'Invariant' : 'Choice') + '</span>' +
        ex.choices.map((c, j) => '<button type="button" class="choice' + (j === this.c ? ' active' : '') + '" data-choice="' + j + '"' +
          (j === this.c ? ' aria-pressed="true"' : ' aria-pressed="false"') + '>' + inline(c.title) + (j === 0 ? ' <span class="muted">(default)</span>' : '') +
          '</button>').join('') + '</div>';
    }

    // In compact mode the last step ends with the outcome, in green when
    // the proof succeeds and in red when it does not.
    finalHTML(ex) {
      if (!this.opts.compact) return '';
      let ok;
      let text;
      if (ex.generated) {
        // The proof of the calculator succeeds when Z3 proves every
        // implication.
        const st = proofs.get(ex.orig || ex);
        const c = st && st.state === 'done' ? proofCounts(st.results) : null;
        if (!st || st.state === 'running') { ok = 'pending'; text = 'Proving the implications with Z3…'; }
        else if (st.state === 'error') { ok = null; text = 'The implications were not proved: ' + st.message; }
        else if (c.refuted) { ok = false; text = '✗ An implication of the proof does not hold: Z3 found a counterexample.'; }
        else if (c.open) { ok = null; text = '? Z3 did not decide every implication of the proof.'; }
        else if (ex.noPre) { ok = true; text = '✓ Every implication of the proof is proved by Z3. The weakest precondition of the program is the first assertion.'; }
        else { ok = true; text = '✓ Every implication of the proof is proved by Z3, so the triple is proved.'; }
      } else if (ex.derived != null && ex.choices.length < 2) {
        ok = ex.derived;
        text = ok ? '✓ The rule derives the triple.' : '✗ The rule does not derive the triple.';
      } else if (ex.choice.outcome === 'fails') {
        ok = false;
        text = '✗ The proof does not succeed with this choice.';
      } else {
        ok = ex.verdict !== 'invalid';
        text = ok ? '✓ The triple is proved.' : '✗ The triple is not valid.';
      }
      const st = proofs.get(ex.orig || ex);
      const report = st && st.state === 'done'
        ? '<details class="proof-details"><summary>All the claims proved by Z3</summary>' + proofReportHTML(st.results) + '</details>' : '';
      if (ok === 'pending') return '<div class="final open">' + text + '</div>';
      return '<div class="final ' + (ok ? 'ok' : ok === false ? 'bad' : 'open') + '">' + text + '</div>' + report;
    }

    render() {
      const ex = this.view();
      const n = ex.steps.length;
      const k = this.k;
      const compact = this.opts.compact;
      const head = compact ? '' : '<header class="ex-head">' +
        '<div class="ex-meta"><span class="topic">' + esc(ex.topic) + '</span>' + levelDots(ex.level) +
        (ex.source ? '<span class="source">' + esc(ex.source) + '</span>' : '') + '</div>' +
        '<h2>' + inline(ex.title) + '</h2>' +
        (ex.tags.length ? '<div class="tags">' + ex.tags.map((t) => '<span class="tag">' + esc(t) + '</span>').join('') + '</div>' : '') +
        '</header>';

      let main;
      let outlineK = k;
      if (this.all) {
        outlineK = n;
        main = problemHTML(ex) + ex.steps.map((s) => stepCardHTML(ex, s)).join('') + summaryHTML(ex);
      } else if (k === 0) main = problemHTML(ex);
      else if (k <= n) main = stepCardHTML(ex, ex.steps[k - 1], k === n ? this.finalHTML(ex) : '');
      else { main = summaryHTML(ex); outlineK = n; }

      const outline = '<aside class="outline-pane">' + givenHTML(ex) +
        '<div class="pane-title"><span class="kicker">Annotated program</span>' +
        '<span class="muted small">' + (outlineK === 0 ? 'before the proof' : outlineK >= n ? 'complete' : 'after step ' + esc(ex.steps[outlineK - 1].number)) + '</span></div>' +
        outlineHTML(ex, outlineK) + '</aside>';

      const problems = ex.errors.length
        ? '<div class="errors"><strong>This exercise has errors:</strong><ul>' + ex.errors.map((e) => '<li>line ' + e.line + ': ' + esc(e.msg) + '</li>').join('') + '</ul></div>'
        : '';
      this.el.innerHTML = head + problems + this.choicesHTML() + schemeHTML(ex, this.all ? 0 : Math.min(k, n)) +
        this.stepperHTML(ex, k) + proofStatusHTML(proofs.get(this.ex), ex.generated) +
        '<div class="ex-body">' + outline + '<div class="step-pane">' + main + '</div></div>';
      // Every claim is proved by default, in the background; the view is
      // drawn again when the proof progresses.
      if (HL.Prover && !this.opts.noProof && !ex.errors.length) {
        const exObj = this.ex;
        const st = ensureProof(exObj);
        if (!st.viewers.has(this)) {
          st.viewers.add(this);
          st.listeners.push(() => { if (this.ex === exObj && this.el.isConnected) this.render(); });
        }
      }
    }
  }

  // ------------------------------------------------------------------
  // Rule dialog
  // ------------------------------------------------------------------

  function openRule(id) {
    const dlg = $('#rule-dialog');
    const rule = HL.RULES.find((r) => r.id === id);
    let html;
    if (rule) {
      html = '<h3>' + esc(rule.name) + ' <span class="muted">[' + esc(rule.id) + ']</span></h3><div class="display">' + ruleFigureFor(rule) + '</div>' +
        '<div class="prose">' + md(rule.says) + '</div>' +
        (rule.wp ? '<p><span class="kicker">Weakest precondition</span><br>' + formulaSpan(rule.wp) + '</p>' : '') +
        '<p><a href="#rule-' + esc(rule.id) + '" class="dlg-link">Read the full explanation</a></p>';
    } else if (HL.PSEUDO_RULES[id]) {
      html = '<h3>' + esc(HL.PSEUDO_RULES[id].name) + '</h3><div class="prose">' + md(HL.PSEUDO_RULES[id].text) + '</div>';
    } else {
      html = '<h3>' + esc(id) + '</h3><p>This rule is not described on this website.</p>';
    }
    $('.dlg-content', dlg).innerHTML = html;
    if (dlg.showModal) dlg.showModal();
    else dlg.setAttribute('open', '');
  }

  function closeRule() {
    const dlg = $('#rule-dialog');
    if (dlg.close) dlg.close();
    else dlg.removeAttribute('open');
  }

  // ------------------------------------------------------------------
  // Pages
  // ------------------------------------------------------------------

  // The Rules page shows one rule at a time, chosen in a scrollable list.
  // A side panel chooses the section of the rule that is shown.
  let currentRule = null;
  let currentSection = 'examples';
  const exampleState = {};

  const RULE_SECTIONS = [
    ['examples', 'Examples'],
    ['semantics', 'Semantics'],
    ['correctness', 'Correctness'],
    ['wp', 'Weakest precondition'],
    ['vcs', 'Verification conditions'],
    ['note', 'Note']
  ];

  function renderRulesPage() {
    $('#page-rules .page-body').innerHTML =
      '<div class="rules-layout">' +
      '<aside class="rule-side">' +
      '<div class="rule-picker"><span class="kicker" id="rule-list-label">Rule</span>' +
      '<div class="rule-list" role="listbox" aria-labelledby="rule-list-label">' +
      HL.RULES.map((r) => '<button type="button" role="option" class="rule-option" data-rule="' + esc(r.id) + '" aria-selected="false">' +
        '<span class="ro-name">' + esc(r.name) + '</span><span class="ro-id">' + esc(r.id) + '</span></button>').join('') +
      '</div></div></aside>' +
      '<div class="rule-view" id="rule-view"></div>' +
      '<nav class="rule-sections" aria-label="Sections of the rule"><span class="kicker">Section</span>' +
      '<div class="rs-list" id="rs-list"></div></nav></div>';
    const page = $('#page-rules');
    page.addEventListener('click', onRulesClick);
    $('.rule-list', page).addEventListener('keydown', (e) => {
      if (e.key !== 'ArrowDown' && e.key !== 'ArrowUp') return;
      e.preventDefault();
      const j = HL.RULES.findIndex((r) => r.id === currentRule) + (e.key === 'ArrowDown' ? 1 : -1);
      if (j < 0 || j >= HL.RULES.length) return;
      location.hash = '#rule-' + HL.RULES[j].id;
      const b = $('.rule-option[data-rule="' + HL.RULES[j].id + '"]');
      if (b) b.focus();
    });
  }

  function onRulesClick(e) {
    const opt = e.target.closest('.rule-option');
    if (opt) { location.hash = '#rule-' + opt.dataset.rule; return; }
    const sec = e.target.closest('.rs-item');
    if (sec) { currentSection = sec.dataset.sec; showRule(currentRule); return; }
    const tab = e.target.closest('.rx-tab');
    if (tab) {
      exampleState[currentRule] = { ex: Number(tab.dataset.ex), k: 1, c: 0 };
      renderExample();
    }
  }

  function sectionHTML(rule, sec) {
    switch (sec) {
      case 'examples': return '<div class="rx" id="rx"></div>';
      case 'semantics': return '<div class="prose">' + md(rule.says) + '</div>';
      case 'correctness': return '<div class="prose">' + md(rule.mechanism) + '</div>';
      case 'wp': return '<div class="display">' + displayLine(rule.wp) + '</div>';
      case 'vcs': return '<div class="prose">' + md(rule.check) + '</div>';
      case 'note': return '<div class="prose">' + md(rule.note) + '</div>';
      default: return '';
    }
  }

  function ruleSections(rule) {
    return RULE_SECTIONS.filter(([k]) => k !== 'wp' || rule.wp);
  }

  function showRule(id) {
    const rule = HL.RULES.find((r) => r.id === id) || HL.RULES[0];
    currentRule = rule.id;
    store.set('hl-rule', rule.id);
    const list = $('.rule-list');
    $$('.rule-option').forEach((b) => {
      const on = b.dataset.rule === rule.id;
      b.setAttribute('aria-selected', on ? 'true' : 'false');
      b.classList.toggle('active', on);
      if (on && list && (b.offsetTop < list.scrollTop || b.offsetTop + b.offsetHeight > list.scrollTop + list.clientHeight)) {
        list.scrollTop = b.offsetTop - list.clientHeight / 2;
      }
    });
    const sections = ruleSections(rule);
    if (!sections.some(([k]) => k === currentSection)) currentSection = 'examples';
    $('#rs-list').innerHTML = sections.map(([k, label]) =>
      '<button type="button" class="rs-item' + (k === currentSection ? ' active' : '') + '" data-sec="' + k + '"' +
      (k === currentSection ? ' aria-current="true"' : '') + '>' + esc(label) + '</button>').join('');
    const title = sections.find(([k]) => k === currentSection)[1];
    const j = HL.RULES.indexOf(rule);
    const prev = HL.RULES[j - 1];
    const next = HL.RULES[j + 1];
    $('#rule-view').innerHTML = '<section class="rule-card">' +
      '<header><h2>' + esc(rule.name) + '</h2><span class="rule-id">' + esc(rule.id) + '</span></header>' +
      '<div class="display">' + ruleFigureFor(rule) + '</div>' +
      '<div class="rg-block"><h3 class="rs-title">' + esc(title) + '</h3>' + sectionHTML(rule, currentSection) + '</div>' +
      '<nav class="rule-pager" aria-label="Other rules">' +
      (prev ? '<a href="#rule-' + esc(prev.id) + '">← ' + esc(prev.name) + '</a>' : '<span></span>') +
      (next ? '<a href="#rule-' + esc(next.id) + '">' + esc(next.name) + ' →</a>' : '<span></span>') +
      '</nav></section>';
    if (currentSection === 'examples') renderExample();
  }

  // ------------------------------------------------------------------
  // Examples of the rules: exercise files with "example-of: RULE", shown
  // with the step viewer in compact mode.
  // ------------------------------------------------------------------

  function renderExample() {
    const box = $('#rx');
    if (!box) return;
    const list = RULE_EXAMPLE_LIST.filter((e) => e.exampleOf === currentRule);
    if (!list.length) { box.innerHTML = '<p class="muted">There is no example for this rule yet.</p>'; return; }
    const st = exampleState[currentRule] || (exampleState[currentRule] = { ex: 0, k: 1, c: 0 });
    box.innerHTML =
      (list.length > 1 ? '<div class="rx-tabs" role="tablist" aria-label="Examples">' + list.map((e, j) =>
        '<button type="button" role="tab" class="rx-tab' + (j === st.ex ? ' active' : '') + '" aria-selected="' + (j === st.ex) +
        '" data-ex="' + j + '">' + inline(e.title) + '</button>').join('') + '</div>' : '') +
      '<div class="rx-viewer"></div>';
    const viewer = new Viewer($('.rx-viewer', box), {
      compact: true,
      onStep: (ex, k, c) => { st.k = k; st.c = c; }
    });
    viewer.show(list[st.ex], st.k, st.c);
  }

  function renderProse(id) {
    $('#page-' + id + ' .page-body').innerHTML = '<div class="prose wide">' + md(HL.PAGES[id]) + '</div>';
  }

  // Exercise list
  let mainViewer;
  let currentFilter = { q: '', topic: '' };

  function renderExerciseList() {
    const list = $('#ex-list-items');
    const q = currentFilter.q.toLowerCase();
    const items = EXERCISES.filter((e) => (!currentFilter.topic || e.topic === currentFilter.topic) &&
      (!q || (e.title + ' ' + e.tags.join(' ') + ' ' + e.topic + ' ' + e.source).toLowerCase().includes(q)));
    const topics = [...new Set(items.map((e) => e.topic))].sort((a, b) => topicRank(a) - topicRank(b));
    const cur = mainViewer && mainViewer.ex ? mainViewer.ex.id : '';
    list.innerHTML = topics.map((t) => '<div class="ex-group"><h4>' + esc(t) + '</h4><ul>' + items.filter((e) => e.topic === t).map((e) =>
      '<li><a href="#ex-' + esc(e.id) + '" class="' + (e.id === cur ? 'active' : '') + '">' +
      '<span class="t">' + inline(e.title) + '</span>' + levelDots(e.level) +
      (e.errors.length ? '<span class="badge bad">errors</span>' : '') + '</a></li>').join('') + '</ul></div>').join('') ||
      '<p class="muted">No exercise matches the search.</p>';
    $('#ex-count').textContent = items.length + ' of ' + EXERCISES.length;
  }

  function renderTopicFilter() {
    const topics = [...new Set(EXERCISES.map((e) => e.topic))].sort((a, b) => topicRank(a) - topicRank(b));
    const sel = $('#ex-topic');
    sel.innerHTML = '<option value="">All topics</option>' + topics.map((t) => '<option>' + esc(t) + '</option>').join('');
  }

  function showExercise(id, k) {
    const ex = byId.get(id);
    if (!ex) {
      $('#ex-view').innerHTML = '<div class="empty"><p>There is no exercise with the id "' + esc(id) + '".</p></div>';
      return;
    }
    if (!mainViewer.ex || mainViewer.ex.id !== id || mainViewer.k !== k) mainViewer.show(ex, k);
    renderExerciseList();
    if (window.matchMedia('(max-width: 900px)').matches) $('#ex-list').open = false;
  }

  function exercisesLanding() {
    const n = EXERCISES.length;
    const topics = [...new Set(EXERCISES.map((e) => e.topic))].sort((a, b) => topicRank(a) - topicRank(b));
    $('#ex-view').innerHTML = '<div class="empty prose">' +
      '<h2>Exercises</h2><p>There are ' + n + ' solved exercises, taken from the exercise lists and quizzes of the module, the slides and the reference HoareLogic.pdf. Each one states everything you need to solve it. Choose one in the list.</p>' +
      '<p>Each solution is shown one step at a time. On the left, the annotated program shows the assertions that are known so far: the named assertions such as $R1$ or $I$ appear when a step computes them, and the statement that the step works on is highlighted. On the right, the step shows the rule that it applies, the calculation, and the verification conditions with their justification.</p>' +
      '<p>The summary of every exercise has a button that tests the solution on sample states.</p>' +
      '<div class="topic-grid">' + topics.map((t) => '<button type="button" class="topic-btn" data-topic="' + esc(t) + '"><span>' + esc(t) + '</span><span class="muted">' +
        EXERCISES.filter((e) => e.topic === t).length + '</span></button>').join('') + '</div></div>';
  }

  // ------------------------------------------------------------------
  // wp calculator
  // ------------------------------------------------------------------

  const WP_EXAMPLES = [
    { name: 'Swap with a temporary variable', prog: 't := x;\nx := y;\ny := t', post: 'x = B && y = A', pre: 'x = A && y = B' },
    { name: 'Maximum of two numbers', prog: 'if x >= y then\n  m := x\nelse\n  m := y', post: 'm >= x && m >= y && (m = x || m = y)', pre: 'true' },
    { name: 'A series of assignments', prog: 'y := y + 10;\nx := x - 5;\nres := x + y', post: '-10 <= res <= 10', pre: '-10 <= x <= 0 && 0 <= y <= 5' },
    { name: 'Two conditionals', prog: 'if x < 0 then x := 0;\nif y < 0 then x := x + 5 else x := x - 5;\nres := x - y', post: '-15 <= res <= 25', pre: '-5 <= y <= 5 && -5 <= x <= 5' },
    { name: 'Writing into an array', prog: 'a[i] := 2 * a[j]', post: 'a[i] = a[j]', pre: '' },
    { name: 'An invalid triple', prog: 'z := z + y;\nx := 3 * z + y', post: 'x = 4 * y', pre: 'y >= z && z >= y' },
    { name: 'A loop that counts down', prog: 'while x > 0 do\n  x := x - 1', post: 'x = 0', pre: 'x = N && N >= 0', inv: 'x >= 0' },
    { name: 'A loop that adds two', prog: 'i := 0;\ns := 0;\nwhile i < n do {\n  s := s + 2;\n  i := i + 1\n}', post: 's = 2 * n', pre: 'n >= 0', inv: 's = 2 * i && 0 <= i <= n' },
    { name: 'A loop with a weak invariant', prog: 'i := 0;\ns := 0;\nwhile i < n do {\n  s := s + 2;\n  i := i + 1\n}', post: 's = 2 * n', pre: 'n >= 0', inv: 's = 2 * i' }
  ];

  function initWp() {
    const sel = $('#wp-example');
    sel.innerHTML = WP_EXAMPLES.map((e, j) => '<option value="' + j + '">' + esc(e.name) + '</option>').join('');
    const load = (j) => {
      const e = WP_EXAMPLES[j];
      $('#wp-prog').value = e.prog;
      $('#wp-post').value = e.post;
      $('#wp-pre').value = e.pre;
      $('#wp-inv').value = e.inv || '';
      computeWp();
    };
    sel.addEventListener('change', () => load(Number(sel.value)));
    $('#wp-form').addEventListener('submit', (e) => { e.preventDefault(); computeWp(); });
    // The first example is computed when the page of the calculator is
    // first shown, so that the other pages do not start the prover.
    loadFirstWp = () => { loadFirstWp = null; load(0); };
  }
  let loadFirstWp = null;

  // The calculator builds the proof with the method of the exercises and
  // shows it with the step viewer.
  let wpViewer = null;

  function computeWp() {
    const out = $('#wp-out');
    const invs = $('#wp-inv').value.split('\n').map((l) => l.trim()).filter(Boolean);
    const r = HL.generateProof($('#wp-prog').value, $('#wp-pre').value, $('#wp-post').value, invs);
    if (r.error) {
      out.innerHTML = '<p class="error-msg">' + esc(r.error) + '</p>';
      wpViewer = null;
      return;
    }
    out.innerHTML = '<div class="wp-viewer"></div>' +
      '<p class="muted small">' + inline('The calculator simplifies only with the laws $(true && A) <=> A$, $(false || A) <=> A$, $(A ==> true) <=> true$ and the arithmetic on constants. Every implication of the proof is proved with the SMT solver Z3; when it does not hold, Z3 gives a counterexample.') + '</p>';
    wpViewer = new Viewer($('.wp-viewer', out), { compact: true });
    wpViewer.show(r.ex, 1);
  }

  // ------------------------------------------------------------------
  // Authoring page
  // ------------------------------------------------------------------

  let authorViewer;
  let authorTimer = null;

  function initAuthor() {
    $('#author-doc').innerHTML = '<div class="prose wide">' + md(HL.PAGES.format) + '</div>';
    const ta = $('#author-src');
    const saved = store.get('hl-author-draft');
    ta.value = saved || HL.TEMPLATE;
    authorViewer = new Viewer($('#author-preview'), {});
    const update = () => {
      store.set('hl-author-draft', ta.value);
      const ex = HL.parseExercise(ta.value, 'draft.hl');
      const msgs = ex.errors.map((e) => ({ t: 'error', ...e })).concat(ex.warnings.map((w) => ({ t: 'warning', ...w })))
        .sort((a, b) => a.line - b.line);
      $('#author-msgs').innerHTML = msgs.length
        ? '<ul>' + msgs.map((m) => '<li class="' + m.t + '"><button type="button" class="linkish" data-line="' + m.line + '">line ' + m.line + '</button> ' +
          (m.t === 'error' ? '<strong>Error.</strong> ' : '<strong>Warning.</strong> ') + esc(m.msg) + '</li>').join('') + '</ul>'
        : '<p class="ok-msg">The exercise reads without errors or warnings.</p>';
      if (ex.program && ex.pre && ex.post) authorViewer.show(ex, authorViewer.ex && authorViewer.ex.id === ex.id ? authorViewer.k : 0);
      else $('#author-preview').innerHTML = '<p class="muted">The preview appears when the precondition, the program and the postcondition can be read.</p>';
    };
    ta.addEventListener('input', () => {
      clearTimeout(authorTimer);
      authorTimer = setTimeout(update, 350);
    });
    $('#author-msgs').addEventListener('click', (e) => {
      const b = e.target.closest('[data-line]');
      if (!b) return;
      const line = Number(b.dataset.line);
      const lines = ta.value.split('\n');
      let start = 0;
      for (let j = 0; j < line - 1 && j < lines.length; j++) start += lines[j].length + 1;
      ta.focus();
      ta.setSelectionRange(start, start + (lines[line - 1] || '').length);
      const lh = parseFloat(getComputedStyle(ta).lineHeight) || 20;
      ta.scrollTop = Math.max(0, (line - 4) * lh);
    });
    $('#author-test').addEventListener('click', () => {
      const out = $('#author-report');
      out.innerHTML = '<p class="muted">Testing…</p>';
      setTimeout(() => {
        try {
          const ex = HL.parseExercise(ta.value, 'draft.hl');
          out.innerHTML = '<h4>Test report</h4><p class="muted small">Every claim was evaluated on small sample states. A passing test is evidence, not a proof.</p>' +
            reportHTML(HL.Checker.checkExercise(ex));
        } catch (err) {
          out.innerHTML = '<p class="error-msg">The tests stopped with an error: ' + esc(err.message) + '</p>';
        }
        out.scrollIntoView({ block: 'start', behavior: 'smooth' });
      }, 30);
    });
    $('#author-template').addEventListener('click', () => {
      ta.value = HL.TEMPLATE;
      update();
    });
    $('#author-download').addEventListener('click', () => {
      const ex = HL.parseExercise(ta.value);
      const name = (ex.id || 'exercise') + '.hl';
      const blob = new Blob([ta.value], { type: 'text/plain' });
      const a = document.createElement('a');
      a.href = URL.createObjectURL(blob);
      a.download = name;
      document.body.appendChild(a);
      a.click();
      setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 1000);
    });
    $('#author-file').addEventListener('change', (e) => {
      const f = e.target.files[0];
      if (!f) return;
      const r = new FileReader();
      r.onload = () => { ta.value = String(r.result); update(); };
      r.readAsText(f);
    });
    $('#author-open').addEventListener('change', (e) => {
      const ex = byId.get(e.target.value);
      if (!ex) return;
      const src = (window.HL_EXERCISE_SOURCES || []).find((s) => s.file === ex.file);
      if (src) { ta.value = src.text; update(); }
      e.target.value = '';
    });
    $('#author-open').innerHTML = '<option value="">Open a copy of an existing exercise…</option>' +
      EXERCISES.map((e) => '<option value="' + esc(e.id) + '">' + esc(e.title) + '</option>').join('');
    update();
  }

  // ------------------------------------------------------------------
  // Routing
  // ------------------------------------------------------------------

  const PAGES = ['intro', 'language', 'rules', 'invariants', 'exercises', 'wp', 'author'];
  let lastPage = null;

  function route() {
    const h = decodeURIComponent(location.hash.replace(/^#/, ''));
    let page = 'intro';
    let target = null;
    let rule = null;
    if (PAGES.includes(h)) page = h;
    else if (h.startsWith('rule-')) { page = 'rules'; rule = h.slice(5); }
    else if (h.startsWith('ex-')) page = 'exercises';
    else if (h.startsWith('h-')) {
      const el = document.getElementById(h);
      const sec = el && el.closest('.page');
      if (sec) { page = sec.id.replace('page-', ''); target = h; }
    }
    const samePage = page === lastPage;
    lastPage = page;
    PAGES.forEach((p) => { $('#page-' + p).hidden = p !== page; });
    if (page === 'rules') showRule(rule || currentRule || store.get('hl-rule') || HL.RULES[0].id);
    if (page === 'wp' && loadFirstWp) loadFirstWp();
    $$('.site-nav a').forEach((a) => a.setAttribute('aria-current', a.getAttribute('href') === '#' + page ? 'page' : 'false'));
    if (page === 'exercises') {
      if (h.startsWith('ex-')) {
        const m = h.slice(3).match(/^(.*?)(?:~(\d+))?$/);
        showExercise(m[1], m[2] ? Number(m[2]) : 0);
      } else {
        mainViewer.ex = null;
        exercisesLanding();
        renderExerciseList();
        $('#ex-list').open = true;
      }
    }
    if (target) {
      const el = document.getElementById(target);
      if (el) setTimeout(() => el.scrollIntoView({ block: 'start' }), 0);
    } else if (page === 'rules' && samePage) {
      // Choosing another rule keeps the list where it is.
    } else if (!h.startsWith('ex-') || !mainViewer.ex) window.scrollTo(0, 0);
  }

  // ------------------------------------------------------------------
  // Theme
  // ------------------------------------------------------------------

  function applyTheme(t) {
    if (t === 'light' || t === 'dark') document.documentElement.setAttribute('data-theme', t);
    else document.documentElement.removeAttribute('data-theme');
    const b = $('#theme-btn');
    b.textContent = t === 'light' ? 'Light' : t === 'dark' ? 'Dark' : 'Auto';
    b.setAttribute('aria-label', 'Colour theme: ' + b.textContent + '. Change the theme.');
  }

  // ------------------------------------------------------------------
  // Start
  // ------------------------------------------------------------------

  function init() {
    renderProse('intro');
    renderProse('language');
    renderProse('invariants');
    renderRulesPage();

    mainViewer = new Viewer($('#ex-view'), {
      onStep: (ex, k) => {
        const h = '#ex-' + ex.id + (k ? '~' + k : '');
        if (location.hash !== h) history.replaceState(null, '', h);
      }
    });
    renderTopicFilter();
    renderExerciseList();
    $('#ex-search').addEventListener('input', (e) => { currentFilter.q = e.target.value; renderExerciseList(); });
    $('#ex-topic').addEventListener('change', (e) => { currentFilter.topic = e.target.value; renderExerciseList(); });
    $('#ex-view').addEventListener('click', (e) => {
      const t = e.target.closest('.topic-btn');
      if (!t) return;
      currentFilter.topic = t.dataset.topic;
      $('#ex-topic').value = t.dataset.topic;
      renderExerciseList();
      $('#ex-list').open = true;
      $('#ex-list').scrollIntoView({ block: 'start' });
    });

    initWp();
    initAuthor();

    document.addEventListener('click', (e) => {
      const chip = e.target.closest('.rule-chip');
      if (chip) { openRule(chip.dataset.rule); return; }
      if (e.target.closest('.dlg-close') || e.target.closest('.dlg-link')) closeRule();
    });
    $('#rule-dialog').addEventListener('click', (e) => { if (e.target.id === 'rule-dialog') closeRule(); });

    document.addEventListener('keydown', (e) => {
      if ($('#page-exercises').hidden || !mainViewer.ex || mainViewer.all) return;
      const tag = (document.activeElement && document.activeElement.tagName) || '';
      if (/INPUT|TEXTAREA|SELECT/.test(tag) || e.altKey || e.ctrlKey || e.metaKey) return;
      if (e.key === 'ArrowRight') { mainViewer.go(mainViewer.k + 1); e.preventDefault(); }
      if (e.key === 'ArrowLeft') { mainViewer.go(mainViewer.k - 1); e.preventDefault(); }
    });

    let theme = store.get('hl-theme') || 'auto';
    applyTheme(theme);
    $('#theme-btn').addEventListener('click', () => {
      theme = theme === 'auto' ? 'light' : theme === 'light' ? 'dark' : 'auto';
      store.set('hl-theme', theme);
      applyTheme(theme);
    });

    window.addEventListener('hashchange', route);
    route();
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
  else init();
})();
