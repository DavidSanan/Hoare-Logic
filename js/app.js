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

  const BLOCK_START = /^(#{2,4} |>> |!! |::rule |\||[-*] |\d+\. |```)/;

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

  const EXERCISES = (window.HL_EXERCISE_SOURCES || []).map((src) => HL.parseExercise(src.text, src.file));
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

  function outlineHTML(ex, k) {
    if (!ex.program) return '<p class="muted">The program could not be read.</p>';
    const slots = slotValuesAt(ex, k);
    const step = k >= 1 && k <= ex.steps.length ? ex.steps[k - 1] : null;
    const focus = new Set(step ? step.focusIds || [] : []);
    return '<div class="listing outline">' + HL.programLines(ex.program).map((l) => {
      const d = ' style="--d:' + l.depth + '"';
      if (l.type === 'assert') {
        const a = l.node;
        if (a.slot && (slots.has(a.slot) || ex.slotNames.includes(a.slot))) {
          const v = slots.get(a.slot);
          const tag = '<span class="slot-tag">' + HL.varHTML(a.slot) + '</span>';
          if (!v) return '<div class="ln assert pending"' + d + '>' + tag + '<span class="brace">{</span> <span class="q">?</span> <span class="brace">}</span></div>';
          const fresh = v.step === k && k > 0 ? ' fresh' : '';
          return '<div class="ln assert' + fresh + '"' + d + '>' + tag + '<span class="brace">{</span> ' + HL.toHTML(v.f) + ' <span class="brace">}</span></div>';
        }
        return '<div class="ln assert"' + d + '><span class="brace">{</span> ' + HL.toHTML(a.f) + ' <span class="brace">}</span></div>';
      }
      const cls = focus.has(l.node.id) && l.type === 'stmt' ? ' focus' : '';
      const label = l.type === 'stmt' && l.node.label ? '<span class="label">' + esc(l.node.label) + '</span>' : '';
      return '<div class="ln ' + l.type + cls + '"' + d + '>' + l.html + label + '</div>';
    }).join('') + '</div>';
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
        return '<div class="calc table-wrap"><table>' + it.rows.map((r, j) => '<tr>' +
          '<td class="rel">' + (j ? (REL_DISPLAY[r.sym] || '=') : '') + '</td>' +
          '<td class="fm"><span class="m">' + (r.f ? HL.toHTML(r.f) : HL.looseHTML(r.src)) + '</span></td>' +
          '<td class="why">' + (r.why ? inline(r.why) : '') + '</td></tr>').join('') + '</table></div>';
      case 'vc': {
        const body = it.node ? (it.node.k === 'triple' ? HL.tripleHTML(it.node) : HL.toHTML(it.node.f)) : HL.looseHTML(it.src);
        const holds = it.status !== 'fails';
        let s = '<div class="vc ' + (holds ? 'holds' : 'fails') + '"><div class="vc-head"><span class="kicker">Verification condition</span>' +
          '<span class="badge ' + (holds ? 'ok' : 'bad') + '">' + (holds ? 'holds' : 'does not hold') + '</span></div>' +
          '<div class="vc-body"><span class="m">' + body + '</span></div>';
        if (it.why) s += '<div class="prose">' + md(it.why) + '</div>';
        if (it.counterexample) s += '<div class="cex"><span class="kicker">Counterexample</span> ' + stateHTML(it.counterexample) + '</div>';
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

  function lineHTML(node) {
    return node.k === 'triple' ? HL.tripleHTML(node) : HL.toHTML(node.f);
  }

  function stateHTML(env) {
    return '<span class="state">' + Object.entries(env).map(([k, v]) => '<span class="m">' + HL.varHTML(k) + ' = ' +
      (Array.isArray(v) ? '[' + v.join(', ') + ']' : esc(HL.valueText(v)).replace(/^-/, '−')) + '</span>').join(', ') + '</span>';
  }

  function stepCardHTML(ex, step) {
    return '<article class="step-card">' +
      '<header><span class="kicker">Step ' + step.index + ' of ' + ex.steps.length + '</span>' +
      '<h3>' + inline(step.title) + '</h3>' +
      (step.rules.length ? '<div class="chips">' + step.rules.map(ruleChip).join('') + '</div>' : '') + '</header>' +
      step.items.map((it) => itemHTML(it, step)).join('') + '</article>';
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
      '<div class="prose">' + md(ex.task) + '</div>' + specHTML(ex) +
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
    s += '<div class="test-block"><h4>Test this solution</h4><p class="muted">The test runs the program and evaluates every claim of the steps on many small states. It does not prove anything: a passing test means that no counterexample was found among the states that were tried.</p>' +
      '<button type="button" class="btn run-tests">Run the tests</button><div class="test-report"></div></div>';
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

  class Viewer {
    constructor(container, opts) {
      this.el = container;
      this.opts = opts || {};
      this.ex = null;
      this.k = 0;
      this.all = false;
      this.el.addEventListener('click', (e) => this.onClick(e));
    }

    show(ex, k) {
      this.ex = ex;
      this.k = Math.max(0, Math.min(k || 0, ex.steps.length + 1));
      this.render();
    }

    go(k) {
      if (!this.ex) return;
      this.k = Math.max(0, Math.min(k, this.ex.steps.length + 1));
      this.render();
      if (this.opts.onStep) this.opts.onStep(this.ex, this.k);
      const nav = $('.stepper', this.el);
      if (nav && nav.getBoundingClientRect().top < 0) nav.scrollIntoView({ block: 'start' });
    }

    onClick(e) {
      const b = e.target.closest('button');
      if (!b || !this.el.contains(b)) return;
      if (b.dataset.go != null) this.go(Number(b.dataset.go));
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

    render() {
      const ex = this.ex;
      const n = ex.steps.length;
      const k = this.k;
      const head = '<header class="ex-head">' +
        '<div class="ex-meta"><span class="topic">' + esc(ex.topic) + '</span>' + levelDots(ex.level) +
        (ex.source ? '<span class="source">' + esc(ex.source) + '</span>' : '') + '</div>' +
        '<h2>' + inline(ex.title) + '</h2>' +
        (ex.tags.length ? '<div class="tags">' + ex.tags.map((t) => '<span class="tag">' + esc(t) + '</span>').join('') + '</div>' : '') +
        '</header>';
      const dots = [];
      dots.push('<button type="button" data-go="0" class="sdot' + (k === 0 ? ' cur' : '') + '" title="The problem">Problem</button>');
      for (let j = 1; j <= n; j++) {
        dots.push('<button type="button" data-go="' + j + '" class="sdot num' + (k === j ? ' cur' : '') + (j < k ? ' done' : '') +
          '" title="' + esc(ex.steps[j - 1].title) + '">' + j + '</button>');
      }
      dots.push('<button type="button" data-go="' + (n + 1) + '" class="sdot' + (k === n + 1 ? ' cur' : '') + '" title="Summary and tests">Summary</button>');
      const stepper = '<nav class="stepper" aria-label="Steps of the solution">' +
        '<button type="button" class="btn ghost prev"' + (k === 0 || this.all ? ' disabled' : '') + ' aria-label="Previous step">←</button>' +
        '<div class="sdots">' + dots.join('') + '</div>' +
        '<button type="button" class="btn ghost next"' + (k === n + 1 || this.all ? ' disabled' : '') + ' aria-label="Next step">→</button>' +
        '<button type="button" class="btn ghost toggle-all">' + (this.all ? 'One step at a time' : 'Show all steps') + '</button>' +
        '</nav>';

      let main;
      let outlineK = k;
      if (this.all) {
        outlineK = n;
        main = problemHTML(ex) + ex.steps.map((s) => stepCardHTML(ex, s)).join('') + summaryHTML(ex);
      } else if (k === 0) main = problemHTML(ex);
      else if (k <= n) main = stepCardHTML(ex, ex.steps[k - 1]);
      else { main = summaryHTML(ex); outlineK = n; }

      const outline = '<aside class="outline-pane"><div class="pane-title"><span class="kicker">Annotated program</span>' +
        '<span class="muted small">' + (outlineK === 0 ? 'before the proof' : outlineK > n || outlineK === n ? 'complete' : 'after step ' + outlineK) + '</span></div>' +
        outlineHTML(ex, outlineK) + '</aside>';

      const problems = ex.errors.length
        ? '<div class="errors"><strong>This exercise has errors:</strong><ul>' + ex.errors.map((e) => '<li>line ' + e.line + ': ' + esc(e.msg) + '</li>').join('') + '</ul></div>'
        : '';
      this.el.innerHTML = head + problems + stepper + '<div class="ex-body">' + outline + '<div class="step-pane">' + main + '</div></div>';
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

  function renderRulesPage() {
    const toc = '<nav class="rule-toc" aria-label="Rules">' + HL.RULES.map((r) => '<a href="#rule-' + r.id + '">' + esc(r.name) + '</a>').join('') + '</nav>';
    const cards = HL.RULES.map((r) => '<section class="rule-card" id="rule-' + r.id + '">' +
      '<header><h2>' + esc(r.name) + '</h2><span class="rule-id">' + esc(r.id) + '</span></header>' +
      '<div class="display">' + ruleFigureFor(r) + '</div>' +
      '<div class="rule-grid">' +
      '<div class="rg-block"><h4>What the rule says</h4><div class="prose">' + md(r.says) + '</div></div>' +
      '<div class="rg-block"><h4>Why it is correct</h4><div class="prose">' + md(r.mechanism) + '</div></div>' +
      '<div class="rg-block"><h4>Example</h4><div class="prose">' + md(r.example) + '</div></div>' +
      (r.wp ? '<div class="rg-block"><h4>Weakest precondition</h4><div class="display">' + displayLine(r.wp) + '</div></div>' : '') +
      '<div class="rg-block"><h4>What you have to check</h4><div class="prose">' + md(r.check) + '</div></div>' +
      '<div class="rg-block"><h4>What it does not tell you</h4><div class="prose">' + md(r.limits) + '</div></div>' +
      '</div></section>').join('');
    $('#page-rules .page-body').innerHTML =
      '<p class="lede">Each rule has a conclusion below the line and premises above it. To use a rule, you prove its premises. The figures use the notation of the slides; the names in brackets are the names used in the steps of the exercises.</p>' +
      '<div class="display summary-rules">' + HL.RULES.slice(0, 6).map(ruleFigureFor).join('') + '</div>' + toc + cards;
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
      '<h2>Exercises</h2><p>There are ' + n + ' solved exercises, taken from the exercise lists and quizzes of the module, the slides and the reference document. Choose one in the list.</p>' +
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
    { name: 'An invalid triple', prog: 'z := z + y;\nx := 3 * z + y', post: 'x = 4 * y', pre: 'y >= z && z >= y' }
  ];

  function initWp() {
    const sel = $('#wp-example');
    sel.innerHTML = WP_EXAMPLES.map((e, j) => '<option value="' + j + '">' + esc(e.name) + '</option>').join('');
    const load = (j) => {
      const e = WP_EXAMPLES[j];
      $('#wp-prog').value = e.prog;
      $('#wp-post').value = e.post;
      $('#wp-pre').value = e.pre;
      computeWp();
    };
    sel.addEventListener('change', () => load(Number(sel.value)));
    $('#wp-form').addEventListener('submit', (e) => { e.preventDefault(); computeWp(); });
    load(0);
  }

  function computeWp() {
    const out = $('#wp-out');
    let prog, post, pre = null;
    try {
      prog = HL.parseProgram($('#wp-prog').value);
    } catch (e) {
      out.innerHTML = '<p class="error-msg">The program could not be read: ' + esc(e.message) + '</p>';
      return;
    }
    try {
      post = HL.parseFormula($('#wp-post').value);
    } catch (e) {
      out.innerHTML = '<p class="error-msg">The postcondition could not be read: ' + esc(e.message) + '</p>';
      return;
    }
    if ($('#wp-pre').value.trim()) {
      try {
        pre = HL.parseFormula($('#wp-pre').value);
      } catch (e) {
        out.innerHTML = '<p class="error-msg">The precondition could not be read: ' + esc(e.message) + '</p>';
        return;
      }
    }
    let trace;
    try {
      trace = HL.wpTrace(prog, post);
    } catch (e) {
      out.innerHTML = '<p class="error-msg">' + esc(e.message) + '. Loops need an invariant; see the exercises on loops.</p>';
      return;
    }
    let s = '<ol class="wp-steps">';
    for (const st of trace.steps) {
      const simp = HL.simplify(st.pre);
      const same = HL.toText(simp) === HL.toText(st.pre);
      s += '<li><div class="wp-rule">' + ruleChip(st.rule) + '</div>' +
        '<div class="m">' + HL.toHTML({ k: 'wp', prog: { k: 'seq', items: [st.stmt] }, post: st.post }) + '</div>' +
        '<div class="m">= ' + HL.toHTML(st.pre) + '</div>' +
        (same ? '' : '<div class="m simp">≡ ' + HL.toHTML(simp) + ' <span class="muted small">(after the simplifications of the calculator)</span></div>') + '</li>';
    }
    s += '</ol>';
    const final = HL.simplify(trace.pre);
    s += '<div class="wp-final"><span class="kicker">Weakest precondition of the program</span><div class="m large">' + HL.toHTML(final) + '</div></div>';
    if (pre) {
      const r = HL.Checker.checkImplication(pre, trace.pre, { range: 5 });
      let msg;
      if (r.status === 'pass') msg = '<span class="badge ok">no counterexample</span> ' + inline('The implication $P ==> wp$ was true in all ' + r.sat + ' tested states that satisfy $P$. This is evidence that the triple is valid. The proof is the implication itself, which you still have to prove.');
      else if (r.status === 'fail') msg = '<span class="badge bad">counterexample</span> In the state ' + stateHTML(r.cex) + ' the precondition is true and the weakest precondition is false. Running the program from this state does not reach the postcondition, so the triple is not valid.';
      else msg = '<span class="badge warn">not conclusive</span> No tested state satisfied the precondition.';
      s += '<div class="wp-check"><span class="kicker">Verification condition</span><div class="m">' + HL.toHTML(HL.N.bin('==>', pre, final)) + '</div><p>' + msg + '</p></div>';
    }
    s += '<p class="muted small">' + inline('The calculator only applies the laws $(true && A) <=> A$, $(false || A) <=> A$, $(A ==> true) <=> true$, the arithmetic on constants, and the select-store axiom when the two indices are written the same way. The other simplifications are left to you, as in the exercises.') + '</p>';
    out.innerHTML = s;
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

  function route() {
    const h = decodeURIComponent(location.hash.replace(/^#/, ''));
    let page = 'intro';
    let target = null;
    if (PAGES.includes(h)) page = h;
    else if (h.startsWith('rule-')) { page = 'rules'; target = h; }
    else if (h.startsWith('ex-')) page = 'exercises';
    else if (h.startsWith('h-')) {
      const el = document.getElementById(h);
      const sec = el && el.closest('.page');
      if (sec) { page = sec.id.replace('page-', ''); target = h; }
    }
    PAGES.forEach((p) => { $('#page-' + p).hidden = p !== page; });
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
