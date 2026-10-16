/*
 * logic.js
 *
 * The engine behind the Hoare Logic website.
 *
 * It contains:
 *   - a tokenizer and a parser for assertions (formulas) and for the
 *     small imperative language of the course
 *       C ::= skip | x := E | a[E] := E | C ; C | if B then C else C | while B do C
 *   - printers that turn the syntax trees into HTML (with the notation of
 *     the slides) and into plain text
 *   - substitution Q[x <- E], including the array update a[I |-> E]
 *   - the weakest precondition calculus for loop-free programs
 *   - an evaluator for formulas and an interpreter for programs, which the
 *     checker uses to test assertions on sample states
 *
 * Everything is attached to the global object HL, so the file works when the
 * page is opened directly from the disk (file://) and when it is loaded in
 * Node for the command-line checks.
 */
(function (root) {
  'use strict';
  const HL = (root.HL = root.HL || {});

  // ------------------------------------------------------------------
  // Errors
  // ------------------------------------------------------------------

  class HLError extends Error {
    constructor(message, pos, end) {
      super(message);
      this.pos = pos == null ? 0 : pos;
      this.end = end == null ? this.pos : end;
    }
  }
  HL.HLError = HLError;

  // Thrown by the evaluator when a value does not exist, for example a read
  // outside an array or an unknown function.
  class Undefined extends Error {}
  HL.Undefined = Undefined;

  // Thrown by the interpreter when a loop runs out of fuel.
  class OutOfFuel extends Error {}
  HL.OutOfFuel = OutOfFuel;

  // ------------------------------------------------------------------
  // Tokenizer
  // ------------------------------------------------------------------

  const SUPERSCRIPTS = {
    '⁰': '0', '¹': '1', '²': '2', '³': '3', '⁴': '4', '⁵': '5', '⁶': '6', '⁷': '7', '⁸': '8', '⁹': '9',
    'ⁿ': 'n', 'ⁱ': 'i'
  };

  // Unicode symbols that the parser accepts, mapped to the ASCII operator
  // that they stand for.
  const UNICODE_OPS = {
    '∧': '&&', '∨': '||', '¬': '!', '⇒': '==>', '⟹': '==>', '→': '==>', '⟶': '==>',
    '⇔': '<=>', '↔': '<=>', '⟺': '<=>', '≡': '<=>', '≤': '<=', '⩽': '<=', '≥': '>=', '⩾': '>=',
    '≠': '!=', '≔': ':=', '←': '<-', '↦': '|->', '·': '*', '⋅': '*', '×': '*', '∗': '*',
    '−': '-', '–': '-', '⇐': '<==', '⟸': '<=='
  };

  const OPS = ['<==>', '==>', '<==', '<=>', '|->', '===', ':=', '==', '!=', '<=', '>=', '=>', '->', '<-',
    '&&', '||', '/\\', '\\/', '<', '>', '=', '+', '-', '*', '/', '%', '^', '!', '(', ')', '[', ']',
    '{', '}', ',', ';', '.', ':', '|'];

  const OP_CANON = { '===': '<=>', '<==>': '<=>', '=>': '==>', '->': '==>', '/\\': '&&', '\\/': '||', '==': '=' };

  const KEYWORDS = new Set(['if', 'then', 'else', 'while', 'do', 'skip', 'true', 'false',
    'forall', 'exists', 'div', 'mod', 'and', 'or', 'not']);
  // These keywords are also recognised in upper case and capitalised, since
  // the slides write SKIP, IF ... THEN ... ELSE and WHILE ... DO.
  const CASELESS_KEYWORDS = new Set(['if', 'then', 'else', 'while', 'do', 'skip', 'true', 'false']);

  function normalizeSource(src) {
    let s = '';
    for (const ch of src) s += SUPERSCRIPTS[ch] !== undefined ? '^' + SUPERSCRIPTS[ch] : ch;
    // NFKC maps mathematical italic letters (as pasted from the slides) to
    // plain letters, subscript digits to digits and the ellipsis to "...".
    return s.normalize('NFKC');
  }

  function tokenize(src) {
    const s = src;
    const toks = [];
    let i = 0;
    const isIdStart = (c) => /[\p{L}_]/u.test(c);
    const isIdChar = (c) => /[\p{L}\p{N}_]/u.test(c);
    while (i < s.length) {
      const c = s[i];
      if (c === ' ' || c === '\t' || c === '\n' || c === '\r' || c === ' ') { i++; continue; }
      if (c === '/' && s[i + 1] === '/') {
        let j = i + 2;
        while (j < s.length && s[j] !== '\n') j++;
        toks.push({ t: 'comment', v: s.slice(i + 2, j).trim(), s: i, e: j });
        i = j;
        continue;
      }
      if (/[0-9]/.test(c)) {
        let j = i;
        while (j < s.length && /[0-9]/.test(s[j])) j++;
        toks.push({ t: 'num', v: s.slice(i, j), s: i, e: j });
        i = j;
        continue;
      }
      if (isIdStart(c)) {
        let j = i;
        while (j < s.length && isIdChar(s[j])) j++;
        let name = s.slice(i, j);
        // primes: x' x′ x’ x''
        while (j < s.length && (s[j] === "'" || s[j] === '′' || s[j] === '’')) { name += "'"; j++; }
        const lower = name.toLowerCase();
        let kind = 'id';
        if (KEYWORDS.has(name)) kind = 'kw';
        else if (CASELESS_KEYWORDS.has(lower) &&
          (name === name.toUpperCase() || name === lower[0].toUpperCase() + lower.slice(1))) {
          kind = 'kw';
          name = lower;
        }
        toks.push({ t: kind, v: name, s: i, e: j });
        i = j;
        continue;
      }
      if (UNICODE_OPS[c]) {
        toks.push({ t: 'op', v: UNICODE_OPS[c], s: i, e: i + 1 });
        i++;
        continue;
      }
      if (c === '∀' || c === '∃') {
        toks.push({ t: 'kw', v: c === '∀' ? 'forall' : 'exists', s: i, e: i + 1 });
        i++;
        continue;
      }
      let matched = null;
      for (const op of OPS) {
        if (s.startsWith(op, i)) { matched = op; break; }
      }
      if (matched) {
        toks.push({ t: 'op', v: OP_CANON[matched] || matched, s: i, e: i + matched.length });
        i += matched.length;
        continue;
      }
      throw new HLError('Unexpected character "' + c + '"', i, i + 1);
    }
    toks.push({ t: 'eof', v: '', s: s.length, e: s.length });
    return toks;
  }

  // ------------------------------------------------------------------
  // Syntax tree constructors
  // ------------------------------------------------------------------

  const N = {
    num: (v) => ({ k: 'num', v }),
    bool: (v) => ({ k: 'bool', v }),
    v: (name) => ({ k: 'var', name }),
    paren: (e) => ({ k: 'paren', e }),
    un: (op, e) => ({ k: 'un', op, e }),
    bin: (op, l, r) => ({ k: 'bin', op, l, r }),
    chain: (ops, args) => ({ k: 'chain', ops, args }),
    cmp: (op, l, r) => ({ k: 'chain', ops: [op], args: [l, r] }),
    call: (f, args) => ({ k: 'call', f, args }),
    idx: (a, i) => ({ k: 'idx', a, i }),
    store: (a, i, v) => ({ k: 'store', a, i, v }),
    subst: (e, x, by) => ({ k: 'subst', e, x, by }),
    quant: (q, vars, body) => ({ k: 'quant', q, vars, body }),
    big: (f, v, lo, hi, e) => ({ k: 'big', f, v, lo, hi, e }),
    and: (list) => list.reduce((a, b) => (a ? N.bin('&&', a, b) : b), null) || N.bool(true)
  };
  HL.N = N;

  // ------------------------------------------------------------------
  // Parser
  // ------------------------------------------------------------------

  class Parser {
    constructor(src) {
      this.src = normalizeSource(src);
      this.toks = tokenize(this.src);
      this.i = 0;
    }
    skipComments() {
      while (this.toks[this.i].t === 'comment') this.i++;
    }
    peek(o = 0) {
      let j = this.i;
      let n = 0;
      for (;;) {
        while (this.toks[j].t === 'comment') j++;
        if (n === o || this.toks[j].t === 'eof') return this.toks[j];
        j++;
        n++;
      }
    }
    next() {
      this.skipComments();
      const t = this.toks[this.i];
      if (t.t !== 'eof') this.i++;
      return t;
    }
    takeComment() {
      if (this.toks[this.i].t === 'comment') return this.toks[this.i++].v;
      return null;
    }
    isOp(v, o = 0) { const t = this.peek(o); return t.t === 'op' && t.v === v; }
    isKw(v, o = 0) { const t = this.peek(o); return t.t === 'kw' && t.v === v; }
    fail(msg, tok) {
      tok = tok || this.peek();
      throw new HLError(msg, tok.s, tok.e);
    }
    expectOp(v, what) {
      if (!this.isOp(v)) this.fail('Expected "' + v + '"' + (what ? ' ' + what : '') + ', found ' + describe(this.peek()));
      return this.next();
    }
    atEnd() { return this.peek().t === 'eof'; }

    // ---- formulas and expressions -------------------------------------

    parseExpr() { return this.parseIff(); }

    parseIff() {
      let l = this.parseImp();
      while (this.isOp('<=>')) {
        this.next();
        l = N.bin('<=>', l, this.parseImp());
      }
      return l;
    }

    parseImp() {
      const l = this.parseOr();
      if (this.isOp('==>')) {
        this.next();
        return N.bin('==>', l, this.parseImp());
      }
      return l;
    }

    parseOr() {
      let l = this.parseAnd();
      while (this.isOp('||') || this.isKw('or')) {
        this.next();
        l = N.bin('||', l, this.parseAnd());
      }
      return l;
    }

    parseAnd() {
      let l = this.parseNot();
      while (this.isOp('&&') || this.isKw('and')) {
        this.next();
        l = N.bin('&&', l, this.parseNot());
      }
      return l;
    }

    parseNot() {
      if (this.isOp('!') || this.isKw('not')) {
        this.next();
        return N.un('!', this.parseNot());
      }
      if (this.isKw('forall') || this.isKw('exists')) return this.parseQuant();
      return this.parseCmp();
    }

    parseQuant() {
      const q = this.next().v;
      const vars = [];
      do {
        const t = this.next();
        if (t.t !== 'id') this.fail('Expected a variable after ' + q, t);
        vars.push(t.v);
      } while (this.isOp(',') && this.next());
      if (this.isOp('.') || this.isOp(':')) this.next();
      else this.fail('Expected "." after the quantified variables');
      return N.quant(q, vars, this.parseExpr());
    }

    parseCmp() {
      const first = this.parseAdd();
      const ops = [];
      const args = [first];
      for (;;) {
        const t = this.peek();
        if (t.t !== 'op') break;
        if (t.v === '<-') {
          // "x<-1" is "x < -1" when it appears in a comparison.
          this.skipComments();
          const tok = this.toks[this.i];
          this.toks.splice(this.i, 1,
            { t: 'op', v: '<', s: tok.s, e: tok.s + 1 },
            { t: 'op', v: '-', s: tok.s + 1, e: tok.e });
          continue;
        }
        if (!['=', '!=', '<', '<=', '>', '>='].includes(t.v)) break;
        this.next();
        ops.push(t.v);
        args.push(this.parseAdd());
      }
      return ops.length ? N.chain(ops, args) : first;
    }

    parseAdd() {
      let l = this.parseMul();
      while (this.isOp('+') || this.isOp('-')) {
        const op = this.next().v;
        l = N.bin(op, l, this.parseMul());
      }
      return l;
    }

    parseMul() {
      let l = this.parseUnary();
      for (;;) {
        if (this.isOp('*') || this.isOp('/') || this.isOp('%')) {
          const op = this.next().v;
          l = N.bin(op, l, this.parseUnary());
        } else if (this.isKw('div') || this.isKw('mod')) {
          const op = this.next().v;
          l = N.bin(op, l, this.parseUnary());
        } else break;
      }
      return l;
    }

    parseUnary() {
      if (this.isOp('-')) {
        this.next();
        return N.un('-', this.parseUnary());
      }
      return this.parsePow();
    }

    parsePow() {
      const b = this.parsePostfix();
      if (this.isOp('^')) {
        this.next();
        return N.bin('^', b, this.parseUnary());
      }
      return b;
    }

    parsePostfix() {
      let e = this.parsePrimary();
      for (;;) {
        if (this.isOp('[')) {
          this.next();
          if (this.peek().t === 'id' && this.isOp('<-', 1)) {
            const x = this.next().v;
            this.next();
            const by = this.parseExpr();
            this.expectOp(']', 'to close the substitution');
            e = N.subst(e, x, by);
            continue;
          }
          const i = this.parseExpr();
          if (this.isOp('|->')) {
            this.next();
            const v = this.parseExpr();
            this.expectOp(']', 'to close the array update');
            e = N.store(e, i, v);
          } else {
            this.expectOp(']', 'to close the array index');
            e = N.idx(e, i);
          }
          continue;
        }
        if (this.isOp('!')) {
          // Postfix "!" is the factorial, as in n!. It is only read as a
          // factorial when it cannot start a negation.
          const after = this.peek(1);
          const startsOperand = after.t === 'num' || after.t === 'id' ||
            (after.t === 'op' && (after.v === '(' || after.v === '!')) ||
            (after.t === 'kw' && ['true', 'false', 'not', 'forall', 'exists'].includes(after.v));
          if (!startsOperand) {
            this.next();
            e = N.call('fact', [e]);
            e.postfix = true;
            continue;
          }
        }
        break;
      }
      return e;
    }

    parsePrimary() {
      const t = this.peek();
      if (t.t === 'num') {
        this.next();
        return N.num(Number(t.v));
      }
      if (t.t === 'kw' && (t.v === 'true' || t.v === 'false')) {
        this.next();
        return N.bool(t.v === 'true');
      }
      if (t.t === 'op' && t.v === '(') {
        this.next();
        const e = this.parseExpr();
        this.expectOp(')', 'to close the parenthesis');
        return N.paren(e);
      }
      if (t.t === 'id') {
        this.next();
        if (this.isOp('(')) {
          this.next();
          if (t.v === 'wp') return this.parseWp(t);
          const args = [];
          if (!this.isOp(')')) {
            do { args.push(this.parseExpr()); } while (this.isOp(',') && this.next());
          }
          this.expectOp(')', 'to close the arguments of ' + t.v);
          const f = t.v;
          if ((f === 'sum' || f === 'prod' || f === 'Sum' || f === 'Prod') && args.length === 4 && args[0].k === 'var') {
            return N.big(f.toLowerCase(), args[0].name, args[1], args[2], args[3]);
          }
          if ((f === 'Sum' || f === 'Prod') && args.length === 2) {
            // Sum(lo, hi) = lo + ... + hi, as written in some solutions.
            return N.big(f.toLowerCase(), 'k', args[0], args[1], N.v('k'));
          }
          return N.call(f, args);
        }
        return N.v(t.v);
      }
      if (t.t === 'eof') this.fail('The formula ends too early');
      this.fail('Expected a value or a formula, found ' + describe(t));
    }

    parseWp(tok) {
      const prog = this.parseSeq();
      this.expectOp(',', 'between the program and the postcondition of wp');
      const post = this.parseExpr();
      this.expectOp(')', 'to close wp(...)');
      return { k: 'wp', prog, post };
    }

    // ---- programs ------------------------------------------------------

    canStartStatement() {
      const t = this.peek();
      if (t.t === 'id') return true;
      if (t.t === 'kw') return ['if', 'while', 'skip'].includes(t.v);
      if (t.t === 'op') return t.v === '{';
      return false;
    }

    parseSeq() {
      const items = [];
      for (;;) {
        if (!this.canStartStatement()) break;
        const st = this.parseStmt();
        items.push(st);
        let label = this.takeComment();
        if (this.isOp(';')) {
          this.next();
          label = label || this.takeComment();
        }
        if (label && st.k !== 'assert' && !st.label) st.label = label;
      }
      return { k: 'seq', items };
    }

    // Decide whether "{ ... }" in statement position is a block of
    // statements or an assertion.
    braceIsBlock() {
      this.skipComments();
      let depth = 0;
      for (let j = this.i; j < this.toks.length; j++) {
        const t = this.toks[j];
        if (t.t === 'op' && t.v === '{') depth++;
        else if (t.t === 'op' && t.v === '}') {
          depth--;
          if (depth === 0) return false;
        } else if (depth >= 1) {
          if (t.t === 'op' && t.v === ':=') return true;
          if (t.t === 'kw' && ['if', 'while', 'skip'].includes(t.v)) return true;
        } else if (t.t === 'eof') return false;
      }
      return false;
    }

    headText(startTok, endTokIndex) {
      const parts = [];
      for (let j = startTok; j < endTokIndex; j++) {
        const t = this.toks[j];
        if (t.t !== 'comment') parts.push(t.v);
      }
      return parts.join(' ');
    }

    parseStmt() {
      this.skipComments();
      const startIndex = this.i;
      const start = this.peek();
      let node;
      if (this.isOp('{')) {
        if (this.braceIsBlock()) {
          this.next();
          node = this.parseSeq();
          node.braces = true;
          this.expectOp('}', 'to close the block');
          return node;
        }
        const open = this.next();
        const f = this.parseExpr();
        const close = this.expectOp('}', 'to close the assertion');
        node = { k: 'assert', f, src: this.src.slice(open.e, close.s).trim() };
        if (f.k === 'var') node.slot = f.name;
        node.pos = open.s;
        node.end = close.e;
        return node;
      }
      if (this.isKw('skip')) {
        this.next();
        node = { k: 'skip' };
      } else if (this.isKw('if')) {
        this.next();
        const c = this.parseExpr();
        if (this.isKw('then')) this.next();
        const headEnd = this.i;
        const t = this.parseBranch();
        let e = null;
        if (this.isKw('else')) {
          this.next();
          e = this.parseBranch();
        }
        node = { k: 'if', c, t, e };
        node.head = this.headText(startIndex, headEnd);
      } else if (this.isKw('while')) {
        this.next();
        const c = this.parseExpr();
        if (this.isKw('do') || this.isKw('then')) this.next();
        const headEnd = this.i;
        const body = this.parseBranch();
        node = { k: 'while', c, body };
        node.head = this.headText(startIndex, headEnd);
      } else if (start.t === 'id') {
        const name = this.next().v;
        if (this.isOp(':=')) {
          this.next();
          node = { k: 'assign', x: name, e: this.parseExpr() };
        } else if (this.isOp('[')) {
          this.next();
          const i = this.parseExpr();
          this.expectOp(']', 'to close the array index');
          this.expectOp(':=', 'in the array assignment');
          node = { k: 'aassign', a: name, i, e: this.parseExpr() };
        } else {
          node = { k: 'meta', name };
        }
      } else {
        this.fail('Expected a statement, found ' + describe(start));
      }
      if (!node.head) node.head = this.headText(startIndex, this.i);
      node.pos = start.s;
      node.end = this.toks[this.i - 1].e;
      return node;
    }

    parseBranch() {
      if (this.isOp('{')) {
        this.next();
        const s = this.parseSeq();
        s.braces = true;
        this.expectOp('}', 'to close the block');
        return s;
      }
      const st = this.parseStmt();
      const label = this.takeComment();
      if (label && !st.label) st.label = label;
      return { k: 'seq', items: [st] };
    }
  }

  function describe(t) {
    if (t.t === 'eof') return 'the end of the text';
    return '"' + t.v + '"';
  }

  function parseFormula(src) {
    const p = new Parser(src);
    if (p.atEnd()) throw new HLError('The formula is empty', 0, 0);
    const f = p.parseExpr();
    if (!p.atEnd()) p.fail('Unexpected ' + describe(p.peek()) + ' after the end of the formula');
    return f;
  }

  function parseProgram(src) {
    const p = new Parser(src);
    const prog = p.parseSeq();
    if (!p.atEnd()) p.fail('Unexpected ' + describe(p.peek()) + ' in the program');
    numberStatements(prog);
    return prog;
  }

  // A triple is written {P} C {Q}. The precondition is the first brace
  // group, and the postcondition is the last one, so the program in the
  // middle may itself contain braces.
  function splitTriple(src) {
    const s = src.trim();
    if (!s.startsWith('{')) return null;
    let depth = 0;
    let preEnd = -1;
    for (let i = 0; i < s.length; i++) {
      if (s[i] === '{') depth++;
      else if (s[i] === '}') {
        depth--;
        if (depth === 0) { preEnd = i; break; }
      }
    }
    if (preEnd < 0 || !s.endsWith('}')) return null;
    depth = 0;
    let postStart = -1;
    for (let i = s.length - 1; i > preEnd; i--) {
      if (s[i] === '}') depth++;
      else if (s[i] === '{') {
        depth--;
        if (depth === 0) { postStart = i; break; }
      }
    }
    if (postStart < 0) return null;
    const prog = s.slice(preEnd + 1, postStart).trim();
    if (!prog) return null;
    return { pre: s.slice(1, preEnd), prog, post: s.slice(postStart + 1, s.length - 1), preOffset: 1, progOffset: preEnd + 1, postOffset: postStart + 1 };
  }

  function parseTriple(src) {
    const parts = splitTriple(src);
    if (!parts) return null;
    return { k: 'triple', pre: parseFormula(parts.pre), prog: parseProgram(parts.prog), post: parseFormula(parts.post) };
  }

  // Parse a line that is either a triple or a formula.
  function parseStatementLine(src) {
    const t = splitTriple(src);
    if (t) {
      try {
        return parseTriple(src);
      } catch (e) {
        // The braces may belong to a formula after all; fall through.
      }
    }
    return { k: 'formula', f: parseFormula(src) };
  }

  let stmtCounter = 0;
  function numberStatements(prog) {
    walkStmts(prog, (s) => { s.id = 's' + (++stmtCounter); });
  }

  function walkStmts(s, fn) {
    if (!s) return;
    if (s.k === 'seq') { s.items.forEach((x) => walkStmts(x, fn)); return; }
    if (s.k === 'assert') return;
    fn(s);
    if (s.k === 'if') { walkStmts(s.t, fn); walkStmts(s.e, fn); }
    if (s.k === 'while') walkStmts(s.body, fn);
  }

  function walkAsserts(s, fn) {
    if (!s) return;
    if (s.k === 'seq') { s.items.forEach((x) => walkAsserts(x, fn)); return; }
    if (s.k === 'assert') { fn(s); return; }
    if (s.k === 'if') { walkAsserts(s.t, fn); walkAsserts(s.e, fn); }
    if (s.k === 'while') walkAsserts(s.body, fn);
  }

  HL.parseFormula = parseFormula;
  HL.parseProgram = parseProgram;
  HL.parseTriple = parseTriple;
  HL.splitTriple = splitTriple;
  HL.parseStatementLine = parseStatementLine;
  HL.walkStmts = walkStmts;
  HL.walkAsserts = walkAsserts;
  HL.normalizeSource = normalizeSource;
  HL.tokenize = (s) => tokenize(normalizeSource(s));

  // Canonical text of a statement head, used to find the statement that a
  // step talks about ("focus: y := t").
  HL.canonHead = function (src) {
    try {
      return tokenize(normalizeSource(src)).filter((t) => t.t !== 'comment' && t.t !== 'eof' &&
        !(t.t === 'op' && t.v === ';')).map((t) => t.v).join(' ');
    } catch (e) {
      return src.replace(/\s+/g, ' ').trim();
    }
  };

  // ------------------------------------------------------------------
  // Generic traversal
  // ------------------------------------------------------------------

  function mapChildren(n, f) {
    switch (n.k) {
      case 'num': case 'bool': case 'var': return n;
      case 'paren': return { ...n, e: f(n.e) };
      case 'un': return { ...n, e: f(n.e) };
      case 'bin': return { ...n, l: f(n.l), r: f(n.r) };
      case 'chain': return { ...n, args: n.args.map(f) };
      case 'call': return { ...n, args: n.args.map(f) };
      case 'idx': return { ...n, a: f(n.a), i: f(n.i) };
      case 'store': return { ...n, a: f(n.a), i: f(n.i), v: f(n.v) };
      case 'subst': return { ...n, e: f(n.e), by: f(n.by) };
      case 'quant': return { ...n, body: f(n.body) };
      case 'big': return { ...n, lo: f(n.lo), hi: f(n.hi), e: f(n.e) };
      case 'wp': return { ...n, post: f(n.post) };
      default: return n;
    }
  }

  function freeVars(n, out = new Set(), bound = new Set()) {
    switch (n.k) {
      case 'var':
        if (!bound.has(n.name)) out.add(n.name);
        return out;
      case 'quant': {
        const b = new Set(bound);
        n.vars.forEach((v) => b.add(v));
        freeVars(n.body, out, b);
        return out;
      }
      case 'big': {
        freeVars(n.lo, out, bound);
        freeVars(n.hi, out, bound);
        const b = new Set(bound);
        b.add(n.v);
        freeVars(n.e, out, b);
        return out;
      }
      case 'subst': {
        // x is not free in e[x <- by], unless "by" mentions it.
        const inner = freeVars(n.e, new Set(), bound);
        inner.delete(n.x);
        inner.forEach((v) => out.add(v));
        freeVars(n.by, out, bound);
        return out;
      }
      case 'wp': {
        const inner = freeVars(n.post, new Set(), bound);
        progAssigned(n.prog).forEach((v) => inner.delete(v));
        inner.forEach((v) => out.add(v));
        progVars(n.prog).forEach((v) => { if (!bound.has(v)) out.add(v); });
        return out;
      }
      default:
        mapChildren(n, (c) => { freeVars(c, out, bound); return c; });
        return out;
    }
  }
  HL.freeVars = (n) => freeVars(n);

  function progVars(s, out = new Set()) {
    if (!s) return out;
    switch (s.k) {
      case 'seq': s.items.forEach((x) => progVars(x, out)); break;
      case 'assign': out.add(s.x); freeVars(s.e, out); break;
      case 'aassign': out.add(s.a); freeVars(s.i, out); freeVars(s.e, out); break;
      case 'if': freeVars(s.c, out); progVars(s.t, out); progVars(s.e, out); break;
      case 'while': freeVars(s.c, out); progVars(s.body, out); break;
      default: break;
    }
    return out;
  }

  function progAssigned(s, out = new Set()) {
    if (!s) return out;
    switch (s.k) {
      case 'seq': s.items.forEach((x) => progAssigned(x, out)); break;
      case 'assign': out.add(s.x); break;
      case 'aassign': out.add(s.a); break;
      case 'if': progAssigned(s.t, out); progAssigned(s.e, out); break;
      case 'while': progAssigned(s.body, out); break;
      default: break;
    }
    return out;
  }
  HL.progVars = progVars;
  HL.progAssigned = progAssigned;

  function hasMeta(s) {
    let found = false;
    walkStmts(s, (x) => { if (x.k === 'meta') found = true; });
    return found;
  }
  HL.hasMeta = hasMeta;

  // ------------------------------------------------------------------
  // Substitution and weakest preconditions
  // ------------------------------------------------------------------

  function isAtomic(e) {
    return ['num', 'bool', 'var', 'paren', 'call', 'idx', 'store', 'big'].includes(e.k) && !(e.k === 'num' && e.v < 0);
  }

  function wrap(e) {
    return isAtomic(e) ? e : N.paren(e);
  }

  function freshName(base, avoid) {
    let i = 1;
    while (avoid.has(base + i)) i++;
    return base + i;
  }

  function renameVar(n, from, to) {
    return substitute(n, from, N.v(to));
  }

  // Q[x <- E]. Substitution nodes and wp nodes inside Q must be expanded
  // first, which expand() does.
  function substitute(n, x, E) {
    switch (n.k) {
      case 'var':
        return n.name === x ? wrap(E) : n;
      case 'quant': {
        if (n.vars.includes(x)) return n;
        const fvE = freeVars(E);
        let vars = n.vars;
        let body = n.body;
        if (vars.some((v) => fvE.has(v))) {
          const avoid = new Set([...fvE, ...freeVars(body), x]);
          vars = vars.map((v) => {
            if (!fvE.has(v)) return v;
            const nv = freshName(v, avoid);
            avoid.add(nv);
            body = renameVar(body, v, nv);
            return nv;
          });
        }
        return { ...n, vars, body: substitute(body, x, E) };
      }
      case 'big': {
        const lo = substitute(n.lo, x, E);
        const hi = substitute(n.hi, x, E);
        if (n.v === x) return { ...n, lo, hi };
        const fvE = freeVars(E);
        let v = n.v;
        let body = n.e;
        if (fvE.has(v)) {
          const avoid = new Set([...fvE, ...freeVars(body), x]);
          const nv = freshName(v, avoid);
          body = renameVar(body, v, nv);
          v = nv;
        }
        return { ...n, v, lo, hi, e: substitute(body, x, E) };
      }
      case 'subst':
      case 'wp':
        return substitute(expand(n), x, E);
      default:
        return mapChildren(n, (c) => substitute(c, x, E));
    }
  }

  // Replace every Q[x <- E] and wp(c, Q) node by its result.
  function expand(n) {
    switch (n.k) {
      case 'subst':
        return substitute(expand(n.e), n.x, expand(n.by));
      case 'wp':
        return wp(n.prog, expand(n.post));
      default:
        return mapChildren(n, expand);
    }
  }

  function readsIn(e, out) {
    // Every array read a[I] in an expression, including reads inside the
    // index of another read.
    const visit = (n) => {
      if (n.k === 'idx') out.push(n);
      mapChildren(n, (c) => { visit(c); return c; });
    };
    visit(e);
    return out;
  }

  function defConditions(exprs) {
    const reads = [];
    exprs.forEach((e) => readsIn(e, reads));
    const seen = new Set();
    const defs = [];
    for (const r of reads) {
      const key = toText(r);
      if (seen.has(key)) continue;
      seen.add(key);
      defs.push(N.call('def', [r]));
    }
    return defs;
  }

  function wp(s, Q) {
    switch (s.k) {
      case 'seq': {
        let R = Q;
        for (let j = s.items.length - 1; j >= 0; j--) {
          if (s.items[j].k !== 'assert') R = wp(s.items[j], R);
        }
        return R;
      }
      case 'skip':
        return Q;
      case 'assign': {
        const R = substitute(Q, s.x, s.e);
        const defs = defConditions([s.e]);
        return defs.length ? N.and([wrapAnd(R), ...defs]) : R;
      }
      case 'aassign': {
        const R = substitute(Q, s.a, N.store(N.v(s.a), s.i, s.e));
        const defs = defConditions([N.idx(N.v(s.a), s.i), s.i, s.e]);
        return N.and([wrapAnd(R), ...defs]);
      }
      case 'if': {
        const w1 = wp(s.t, Q);
        const w2 = s.e ? wp(s.e, Q) : Q;
        return N.bin('&&', N.bin('==>', s.c, w1), N.bin('==>', N.un('!', s.c), w2));
      }
      case 'while':
        throw new HLError('The weakest precondition of a loop needs an invariant, so it is not computed automatically');
      case 'meta':
        throw new HLError('wp cannot be computed for the placeholder command "' + s.name + '"');
      default:
        throw new HLError('Unknown statement');
    }
  }

  function wrapAnd(R) {
    return R.k === 'bin' && (R.op === '||' || R.op === '==>' || R.op === '<=>') ? N.paren(R) : R;
  }

  HL.substitute = (n, x, E) => substitute(expand(n), x, expand(E));
  HL.expand = expand;
  HL.wp = (prog, Q) => wp(prog, expand(Q));

  // The steps of a wp computation for a straight-line program, from the
  // last statement to the first. Used by the wp calculator.
  HL.wpTrace = function (prog, Q) {
    const steps = [];
    const go = (s, post) => {
      switch (s.k) {
        case 'seq': {
          let R = post;
          for (let j = s.items.length - 1; j >= 0; j--) {
            if (s.items[j].k !== 'assert') R = go(s.items[j], R);
          }
          return R;
        }
        case 'if': {
          const w1 = go(s.t, post);
          const w2 = s.e ? go(s.e, post) : post;
          const res = N.bin('&&', N.bin('==>', s.c, w1), N.bin('==>', N.un('!', s.c), w2));
          steps.push({ stmt: s, post, pre: res, rule: 'IF' });
          return res;
        }
        default: {
          const res = wp(s, post);
          steps.push({ stmt: s, post, pre: res, rule: s.k === 'skip' ? 'SKIP' : s.k === 'aassign' ? 'ARRAY-ASSIGN' : 'ASSIGN' });
          return res;
        }
      }
    };
    const pre = go(prog, expand(Q));
    return { pre, steps };
  };

  // ------------------------------------------------------------------
  // A light simplifier, used by the wp calculator. It folds constants and
  // the laws true ∧ A = A, false ∨ A = A, A ⇒ true = true and similar.
  // It never changes the meaning of a formula.
  // ------------------------------------------------------------------

  function simplify(n) {
    n = mapChildren(n, simplify);
    switch (n.k) {
      case 'paren':
        return isAtomic(n.e) || n.e.k === 'paren' ? n.e : n;
      case 'un':
        if (n.op === '!' && n.e.k === 'bool') return N.bool(!n.e.v);
        if (n.op === '-' && n.e.k === 'num') return N.num(-n.e.v);
        if (n.op === '!' && n.e.k === 'paren' && n.e.e.k === 'chain' && n.e.e.ops.length === 1) {
          const neg = { '=': '!=', '!=': '=', '<': '>=', '>=': '<', '>': '<=', '<=': '>' };
          const c = n.e.e;
          return N.chain([neg[c.ops[0]]], c.args);
        }
        return n;
      case 'bin': {
        const l = unparen(n.l);
        const r = unparen(n.r);
        if (['+', '-', '*'].includes(n.op) && l.k === 'num' && r.k === 'num') {
          return N.num(n.op === '+' ? l.v + r.v : n.op === '-' ? l.v - r.v : l.v * r.v);
        }
        if (n.op === '+' && l.k === 'num' && l.v === 0) return n.r;
        if ((n.op === '+' || n.op === '-') && r.k === 'num' && r.v === 0) return n.l;
        if (n.op === '*' && ((l.k === 'num' && l.v === 1))) return n.r;
        if (n.op === '*' && ((r.k === 'num' && r.v === 1))) return n.l;
        if (n.op === '&&') {
          if (l.k === 'bool') return l.v ? n.r : N.bool(false);
          if (r.k === 'bool') return r.v ? n.l : N.bool(false);
          if (toText(l) === toText(r)) return n.l;
        }
        if (n.op === '||') {
          if (l.k === 'bool') return l.v ? N.bool(true) : n.r;
          if (r.k === 'bool') return r.v ? N.bool(true) : n.l;
        }
        if (n.op === '==>') {
          if (l.k === 'bool') return l.v ? n.r : N.bool(true);
          if (r.k === 'bool' && r.v) return N.bool(true);
          if (toText(l) === toText(r)) return N.bool(true);
        }
        return n;
      }
      case 'chain': {
        const args = n.args.map(unparen);
        if (args.every((a) => a.k === 'num')) {
          let ok = true;
          for (let j = 0; j < n.ops.length; j++) ok = ok && compare(n.ops[j], args[j].v, args[j + 1].v);
          return N.bool(ok);
        }
        if (n.ops.length === 1 && toText(args[0]) === toText(args[1])) {
          return N.bool(['=', '<=', '>='].includes(n.ops[0]));
        }
        return n;
      }
      case 'idx': {
        const a = unparen(n.a);
        if (a.k === 'store' && toText(a.i) === toText(n.i)) return a.v;
        return n;
      }
      default:
        return n;
    }
  }

  function unparen(e) {
    while (e.k === 'paren') e = e.e;
    return e;
  }
  HL.simplify = (n) => {
    let prev = '';
    let cur = n;
    for (let j = 0; j < 8; j++) {
      cur = simplify(cur);
      const t = toText(cur);
      if (t === prev) break;
      prev = t;
    }
    return cur;
  };
  HL.unparen = unparen;

  // ------------------------------------------------------------------
  // Evaluation
  // ------------------------------------------------------------------

  function compare(op, a, b) {
    switch (op) {
      case '=': return deepEqual(a, b);
      case '!=': return !deepEqual(a, b);
      case '<': return a < b;
      case '<=': return a <= b;
      case '>': return a > b;
      case '>=': return a >= b;
      default: throw new Undefined();
    }
  }

  function deepEqual(a, b) {
    if (Array.isArray(a) || Array.isArray(b)) {
      if (!Array.isArray(a) || !Array.isArray(b) || a.length !== b.length) return false;
      return a.every((x, j) => deepEqual(x, b[j]));
    }
    if (typeof a === 'number' && typeof b === 'number') return Math.abs(a - b) < 1e-9;
    return a === b;
  }

  function truth(v) {
    if (typeof v === 'boolean') return v;
    if (typeof v === 'number') return v !== 0;
    throw new Undefined();
  }

  function tryTruth(n, env) {
    try {
      return truth(evaluate(n, env));
    } catch (e) {
      if (e instanceof Undefined) return undefined;
      throw e;
    }
  }

  function num(v) {
    if (typeof v === 'number') return v;
    if (typeof v === 'boolean') return v ? 1 : 0;
    throw new Undefined();
  }

  function int(v) {
    const x = num(v);
    if (!Number.isInteger(x)) throw new Undefined();
    return x;
  }

  function floorDiv(a, b) {
    if (b === 0) throw new Undefined();
    return Math.floor(a / b);
  }
  function floorMod(a, b) {
    if (b === 0) throw new Undefined();
    return a - b * Math.floor(a / b);
  }

  function quantWindow(env) {
    let m = 0;
    for (const v of Object.values(env)) {
      if (typeof v === 'number') m = Math.max(m, Math.abs(v));
      else if (Array.isArray(v)) m = Math.max(m, v.length, ...v.map((x) => Math.abs(x)));
    }
    return Math.min(m + 3, 60);
  }

  const FUNCTIONS = {
    fib(n) {
      n = int(n);
      if (n < 0 || n > 90) throw new Undefined();
      let a = 0, b = 1;
      for (let j = 0; j < n; j++) [a, b] = [b, a + b];
      return a;
    },
    fact(n) {
      n = int(n);
      if (n < 0 || n > 25) throw new Undefined();
      let r = 1;
      for (let j = 2; j <= n; j++) r *= j;
      return r;
    },
    pow(a, b) { return power(num(a), int(b)); },
    abs(x) { return Math.abs(num(x)); },
    min(...xs) { return Math.min(...xs.map(num)); },
    max(...xs) { return Math.max(...xs.map(num)); },
    even(x) { return floorMod(int(x), 2) === 0; },
    odd(x) { return floorMod(int(x), 2) === 1; },
    sizeof(a) { if (!Array.isArray(a)) throw new Undefined(); return a.length; },
    div(a, b) { return floorDiv(int(a), int(b)); },
    mod(a, b) { return floorMod(int(a), int(b)); }
  };
  FUNCTIONS.length = FUNCTIONS.sizeof;
  FUNCTIONS.len = FUNCTIONS.sizeof;
  FUNCTIONS.factorial = FUNCTIONS.fact;
  HL.FUNCTIONS = FUNCTIONS;

  function power(a, b) {
    if (b < 0 || b > 60) throw new Undefined();
    let r = 1;
    for (let j = 0; j < b; j++) r *= a;
    return r;
  }

  function evaluate(n, env) {
    switch (n.k) {
      case 'num': return n.v;
      case 'bool': return n.v;
      case 'var':
        if (!(n.name in env)) throw new Undefined();
        return env[n.name];
      case 'paren': return evaluate(n.e, env);
      case 'un':
        if (n.op === '!') return !truth(evaluate(n.e, env));
        return -num(evaluate(n.e, env));
      case 'bin': {
        const op = n.op;
        // A side that cannot be evaluated (for example a read outside an
        // array) does not matter when the other side decides the result:
        // false ∧ ? is false, true ∨ ? is true, ? ⇒ true is true.
        if (op === '&&' || op === '||' || op === '==>') {
          const l = tryTruth(n.l, env);
          const lv = op === '==>' ? (l === undefined ? undefined : !l) : l;
          const decisive = op === '&&' ? false : true;
          if (lv === decisive) return decisive;
          const r = tryTruth(n.r, env);
          if (r === decisive) return decisive;
          if (lv === undefined || r === undefined) throw new Undefined();
          return !decisive;
        }
        if (op === '<=>') return truth(evaluate(n.l, env)) === truth(evaluate(n.r, env));
        const a = num(evaluate(n.l, env));
        const b = num(evaluate(n.r, env));
        switch (op) {
          case '+': return a + b;
          case '-': return a - b;
          case '*': return a * b;
          case '/': if (b === 0) throw new Undefined(); return a / b;
          case '%': case 'mod': return floorMod(int(a), int(b));
          case 'div': return floorDiv(int(a), int(b));
          case '^': return power(a, int(b));
          default: throw new Undefined();
        }
      }
      case 'chain': {
        let prev = evaluate(n.args[0], env);
        for (let j = 0; j < n.ops.length; j++) {
          const cur = evaluate(n.args[j + 1], env);
          if (!compare(n.ops[j], prev, cur)) return false;
          prev = cur;
        }
        return true;
      }
      case 'call': {
        if (n.f === 'def') {
          const r = n.args[0] && unparen(n.args[0]);
          if (!r || r.k !== 'idx') throw new Undefined();
          const a = evaluate(r.a, env);
          if (!Array.isArray(a)) throw new Undefined();
          const i = int(evaluate(r.i, env));
          return i >= 0 && i < a.length;
        }
        const f = FUNCTIONS[n.f];
        if (!f) throw new Undefined();
        return f(...n.args.map((a) => evaluate(a, env)));
      }
      case 'idx': {
        const a = evaluate(n.a, env);
        const i = int(evaluate(n.i, env));
        if (!Array.isArray(a) || i < 0 || i >= a.length) throw new Undefined();
        return a[i];
      }
      case 'store': {
        const a = evaluate(n.a, env);
        const i = int(evaluate(n.i, env));
        if (!Array.isArray(a) || i < 0 || i >= a.length) throw new Undefined();
        const copy = a.slice();
        copy[i] = evaluate(n.v, env);
        return copy;
      }
      case 'subst': case 'wp':
        return evaluate(expand(n), env);
      case 'quant': {
        const w = quantWindow(env);
        const vals = [];
        for (let x = -w; x <= w; x++) vals.push(x);
        const loop = (j, e) => {
          if (j === n.vars.length) return truth(evaluate(n.body, e));
          for (const x of vals) {
            const r = loop(j + 1, { ...e, [n.vars[j]]: x });
            if (n.q === 'forall' && !r) return false;
            if (n.q === 'exists' && r) return true;
          }
          return n.q === 'forall';
        };
        return loop(0, env);
      }
      case 'big': {
        const lo = int(evaluate(n.lo, env));
        const hi = int(evaluate(n.hi, env));
        if (hi - lo > 2000) throw new Undefined();
        let acc = n.f === 'sum' ? 0 : 1;
        for (let x = lo; x <= hi; x++) {
          const v = num(evaluate(n.e, { ...env, [n.v]: x }));
          acc = n.f === 'sum' ? acc + v : acc * v;
        }
        return acc;
      }
      default:
        throw new Undefined();
    }
  }
  HL.evaluate = evaluate;
  HL.truth = truth;
  HL.deepEqual = deepEqual;

  // Run a program. The state is an object from names to values. Loops have
  // a budget of iterations ("fuel"); a run that uses all of it is treated
  // as a run that may not terminate.
  function execute(s, env, fuel = { n: 5000 }) {
    switch (s.k) {
      case 'seq': {
        let e = env;
        for (const it of s.items) if (it.k !== 'assert') e = execute(it, e, fuel);
        return e;
      }
      case 'skip': return env;
      case 'assign': return { ...env, [s.x]: evaluate(s.e, env) };
      case 'aassign': {
        const a = env[s.a];
        const i = int(evaluate(s.i, env));
        if (!Array.isArray(a) || i < 0 || i >= a.length) throw new Undefined();
        const v = evaluate(s.e, env);
        const copy = a.slice();
        copy[i] = v;
        return { ...env, [s.a]: copy };
      }
      case 'if':
        if (truth(evaluate(s.c, env))) return execute(s.t, env, fuel);
        return s.e ? execute(s.e, env, fuel) : env;
      case 'while': {
        let e = env;
        while (truth(evaluate(s.c, e))) {
          if (--fuel.n < 0) throw new OutOfFuel();
          e = execute(s.body, e, fuel);
        }
        return e;
      }
      default:
        throw new Undefined();
    }
  }
  HL.execute = execute;

  // ------------------------------------------------------------------
  // Printing
  // ------------------------------------------------------------------

  const PREC = { '<=>': 1, '==>': 2, '||': 3, '&&': 4, chain: 6, '+': 7, '-': 7, '*': 8, '/': 8, '%': 8, div: 8, mod: 8, '^': 10 };

  function esc(s) {
    return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
  }
  HL.esc = esc;

  const GREEK = { alpha: 'α', beta: 'β', gamma: 'γ', delta: 'δ', sigma: 'σ', tau: 'τ', phi: 'φ', psi: 'ψ', omega: 'ω', Sigma: 'Σ' };

  function varHTML(name) {
    const m = name.match(/^(.*?)('*)$/);
    let base = m[1];
    const primes = '′'.repeat(m[2].length);
    let sub = '';
    let mm = base.match(/^([^_]+)_(.+)$/);
    if (mm) { base = mm[1]; sub = mm[2]; } else {
      mm = base.match(/^([A-Za-z]+)(\d+)$/);
      if (mm) { base = mm[1]; sub = mm[2]; }
    }
    if (GREEK[base]) base = GREEK[base];
    return '<i class="v">' + esc(base) + (sub ? '<sub>' + esc(sub) + '</sub>' : '') + primes + '</i>';
  }
  HL.varHTML = varHTML;

  const HTML_OPS = {
    '+': '+', '-': '−', '*': '·', '/': '/', '%': 'mod', div: 'div', mod: 'mod',
    '&&': '∧', '||': '∨', '==>': '⇒', '<=>': '⇔',
    '=': '=', '!=': '≠', '<': '&lt;', '<=': '≤', '>': '&gt;', '>=': '≥'
  };
  const TEXT_OPS = {
    '+': '+', '-': '-', '*': '*', '/': '/', '%': '%', div: 'div', mod: 'mod',
    '&&': '&&', '||': '||', '==>': '==>', '<=>': '<=>',
    '=': '=', '!=': '!=', '<': '<', '<=': '<=', '>': '>', '>=': '>='
  };

  const UPRIGHT_FUNCS = new Set(['fib', 'even', 'odd', 'min', 'max', 'sizeof', 'length', 'len', 'perm', 'wp', 'gcd', 'sorted']);

  function printer(mode, opts) {
    opts = opts || {};
    const H = mode === 'html';
    const op = (o) => (H ? ' <span class="op">' + HTML_OPS[o] + '</span> ' : ' ' + TEXT_OPS[o] + ' ');
    const V = (name) => (H ? varHTML(name) : name);
    const fn = (f) => (H ? (f === 'def' ? '<i class="fn">def</i>' : UPRIGHT_FUNCS.has(f) ? '<span class="fn">' + esc(f) + '</span>' : '<i class="fn">' + esc(f) + '</i>') : f);
    const P = (s) => '(' + s + ')';
    // Inside brackets and argument lists, a parenthesis adds nothing.
    const inner = (n) => pr(n.k === 'paren' ? n.e : n, 0);

    function pr(n, ctx) {
      let s;
      let p;
      switch (n.k) {
        case 'num':
          return H ? '<span class="n">' + n.v + '</span>' : String(n.v);
        case 'bool':
          return H ? '<span class="c">' + (n.v ? 'true' : 'false') + '</span>' : (n.v ? 'true' : 'false');
        case 'var':
          return V(n.name);
        case 'paren':
          return P(pr(n.e, 0));
        case 'un':
          if (n.op === '!') {
            p = 5;
            s = (H ? '¬' : '!') + pr(n.e, 11);
          } else {
            p = 9;
            s = (H ? '−' : '-') + pr(n.e, 10);
          }
          break;
        case 'bin': {
          p = PREC[n.op];
          if (n.op === '^') {
            s = H ? pr(n.l, 11) + '<sup>' + inner(n.r) + '</sup>' : pr(n.l, 11) + '^' + pr(n.r, 10);
            break;
          }
          const rightAssoc = n.op === '==>';
          s = pr(n.l, rightAssoc ? p + 1 : p) + op(n.op) + pr(n.r, rightAssoc ? p : p + 1);
          break;
        }
        case 'chain': {
          p = 6;
          s = pr(n.args[0], 7);
          for (let j = 0; j < n.ops.length; j++) s += op(n.ops[j]) + pr(n.args[j + 1], 7);
          break;
        }
        case 'call': {
          if (n.f === 'fact' && n.args.length === 1) {
            p = 11;
            s = pr(n.args[0], 11) + '!';
            break;
          }
          if (n.f === 'abs' && n.args.length === 1) return '|' + inner(n.args[0]) + '|';
          if (n.f === 'pow' && n.args.length === 2 && H) {
            p = 10;
            s = pr(n.args[0], 11) + '<sup>' + inner(n.args[1]) + '</sup>';
            break;
          }
          return fn(n.f) + '(' + n.args.map(inner).join(', ') + ')';
        }
        case 'idx':
          return pr(n.a, 11) + '[' + inner(n.i) + ']';
        case 'store':
          return pr(n.a, 11) + '[' + inner(n.i) + (H ? ' ↦ ' : ' |-> ') + inner(n.v) + ']';
        case 'subst':
          return pr(n.e, 11) + '[' + V(n.x) + (H ? ' ← ' : ' <- ') + inner(n.by) + ']';
        case 'quant': {
          p = 0;
          const q = H ? (n.q === 'forall' ? '∀' : '∃') : n.q + ' ';
          s = q + n.vars.map(V).join(', ') + '. ' + pr(n.body, 0);
          break;
        }
        case 'big': {
          p = 8;
          if (H) {
            const sym = n.f === 'sum' ? 'Σ' : 'Π';
            s = '<span class="big"><span class="bigsym">' + sym + '</span><span class="lims"><span class="hi">' +
              pr(n.hi, 0) + '</span><span class="lo">' + V(n.v) + ' = ' + pr(n.lo, 0) + '</span></span></span>' + pr(n.e, 9);
          } else {
            s = n.f + '(' + n.v + ', ' + pr(n.lo, 0) + ', ' + pr(n.hi, 0) + ', ' + pr(n.e, 0) + ')';
            p = 12;
          }
          break;
        }
        case 'wp':
          return fn('wp') + '(' + (H ? '<span class="code-inline">' + progInline(n.prog, true) + '</span>' : progInline(n.prog, false)) + ', ' + pr(n.post, 0) + ')';
        default:
          return '?';
      }
      return p < ctx ? P(s) : s;
    }

    const ASG = H ? (opts.lower ? ' <span class="op">:=</span> ' : ' ≔ ') : ' := ';
    const KW = (w) => (H ? '<span class="kw">' + (opts.lower ? w : w.toUpperCase()) + '</span>' : w);

    function progInline(s) {
      switch (s.k) {
        case 'seq': {
          const items = s.items.filter((x) => x.k !== 'assert');
          if (items.length === 1) return progInline(items[0]);
          const inner = items.map((x) => progInline(x)).join('; ');
          return inner;
        }
        case 'skip': return KW('skip');
        case 'meta': return V(s.name);
        case 'assign': return V(s.x) + ASG + pr(s.e, 0);
        case 'aassign': return V(s.a) + '[' + pr(s.i, 0) + ']' + ASG + pr(s.e, 0);
        case 'if':
          return KW('if') + ' ' + pr(s.c, 0) + ' ' + KW('then') + ' ' + block(s.t) +
            (s.e ? ' ' + KW('else') + ' ' + block(s.e) : '');
        case 'while':
          return KW('while') + ' ' + pr(s.c, 0) + ' ' + KW('do') + ' ' + block(s.body);
        default: return '?';
      }
    }
    function block(s) {
      const items = s.items.filter((x) => x.k !== 'assert');
      if (items.length <= 1) return items.length ? progInline(items[0]) : KW('skip');
      return '(' + progInline(s) + ')';
    }

    return { formula: (n) => pr(n, 0), prog: progInline };
  }

  const HTMLP = printer('html');
  const TEXTP = printer('text');
  const CODEP = printer('html', { lower: true });

  function toHTML(n) { return HTMLP.formula(n); }
  function toText(n) { return TEXTP.formula(n); }
  HL.toHTML = toHTML;
  HL.toText = toText;
  HL.progInlineHTML = (p) => HTMLP.prog(p);
  HL.progInlineText = (p) => TEXTP.prog(p);
  HL.progCodeHTML = (p) => CODEP.prog(p);

  HL.tripleHTML = function (t) {
    return '<span class="brace">{</span>' + toHTML(t.pre) + '<span class="brace">}</span> ' +
      '<span class="prog-inline">' + HTMLP.prog(t.prog) + '</span>' +
      ' <span class="brace">{</span>' + toHTML(t.post) + '<span class="brace">}</span>';
  };

  // Program listing as lines, for the annotated program view.
  HL.programLines = function (prog) {
    const lines = [];
    const kw = (w) => '<span class="kw">' + w + '</span>';
    const assign = (s) => {
      if (s.k === 'assign') return varHTML(s.x) + ' <span class="op">:=</span> ' + toHTML(s.e);
      return toHTML(N.idx(N.v(s.a), s.i)) + ' <span class="op">:=</span> ' + toHTML(s.e);
    };
    const emit = (seq, depth) => {
      const items = seq.items;
      const lastStmt = (() => {
        for (let j = items.length - 1; j >= 0; j--) if (items[j].k !== 'assert') return j;
        return -1;
      })();
      items.forEach((s, j) => {
        const semi = j < lastStmt ? '<span class="semi">;</span>' : '';
        switch (s.k) {
          case 'assert':
            lines.push({ depth, type: 'assert', node: s });
            break;
          case 'skip':
            lines.push({ depth, type: 'stmt', node: s, html: kw('skip') + semi });
            break;
          case 'meta':
            lines.push({ depth, type: 'stmt', node: s, html: varHTML(s.name) + semi });
            break;
          case 'assign': case 'aassign':
            lines.push({ depth, type: 'stmt', node: s, html: assign(s) + semi });
            break;
          case 'if':
            lines.push({ depth, type: 'stmt', node: s, html: kw('if') + ' ' + toHTML(s.c) + ' ' + kw('then') + ' {' });
            emit(s.t, depth + 1);
            if (s.e) {
              lines.push({ depth, type: 'close', node: s, html: '} ' + kw('else') + ' {' });
              emit(s.e, depth + 1);
            }
            lines.push({ depth, type: 'close', node: s, html: '}' + semi });
            break;
          case 'while':
            lines.push({ depth, type: 'stmt', node: s, html: kw('while') + ' ' + toHTML(s.c) + ' ' + kw('do') + ' {' });
            emit(s.body, depth + 1);
            lines.push({ depth, type: 'close', node: s, html: '}' + semi });
            break;
          case 'seq':
            emit(s, depth);
            break;
          default: break;
        }
      });
    };
    emit(prog, 0);
    return lines;
  };

  // Render a formula given as text. If the text cannot be parsed, the
  // operators are still replaced, so the reader sees the notation of the
  // slides, but nothing is checked.
  HL.renderFormulaText = function (src) {
    try {
      return { html: toHTML(parseFormula(src)), ok: true };
    } catch (e) {
      return { html: looseHTML(src), ok: false, error: e };
    }
  };

  HL.renderLine = function (src) {
    try {
      const l = parseStatementLine(src);
      if (l.k === 'triple') return { html: HL.tripleHTML(l), ok: true, node: l };
      return { html: toHTML(l.f), ok: true, node: l };
    } catch (e) {
      return { html: looseHTML(src), ok: false, error: e };
    }
  };

  function looseHTML(src) {
    let s = esc(normalizeSource(src));
    const rep = [['&lt;=&gt;', '⇔'], ['==&gt;', '⇒'], ['=&gt;', '⇒'], [':=', '≔'], ['&lt;-', '←'], ['|-&gt;', '↦'],
      ['&amp;&amp;', '∧'], ['||', '∨'], ['!=', '≠'], ['&lt;=', '≤'], ['&gt;=', '≥'], ['==', '=']];
    for (const [a, b] of rep) s = s.split(a).join(b);
    s = s.replace(/([A-Za-z_][A-Za-z0-9_]*'*)/g, (m) => (/^(if|then|else|while|do|skip|true|false|wp)$/i.test(m) ? m : varHTML(m)));
    return s;
  }
  HL.looseHTML = looseHTML;

  HL.valueText = function valueText(v) {
    if (Array.isArray(v)) return '[' + v.map(valueText).join(', ') + ']';
    if (typeof v === 'number') return Number.isInteger(v) ? String(v) : String(Math.round(v * 1000) / 1000);
    return String(v);
  };
})(typeof window !== 'undefined' ? window : globalThis);
