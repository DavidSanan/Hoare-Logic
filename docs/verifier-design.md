# A verification engine for the Hoare Logic Workbench

Architecture and design, version 3. Versions 1 and 2 were designs; this version describes the engine that is implemented in the test version of the site, and what remains to be done.

Where the code is: the engine lives in the repository of the website (DavidSanan/Hoare-Logic), in the folder `test/`, which is published at https://davidsanan.github.io/Hoare-Logic/test/. It will move to its own repository later. The files are `test/js/smt.js`, `test/js/ivl.js`, `test/js/prover.js` and the changes to `test/js/app.js` and `test/js/generate.js`; Z3 is in `test/z3/`, and `tools/prove-exercises.js` runs the engine from the command line.

## 1. Purpose and guiding rule

The website used to check the claims of a solution by testing them: it evaluated each claim on a few thousand small states and reported a state that broke it. The engine described here proves the claims instead, with the SMT solver Z3 deciding the logical formulas. In the test version of the site, every claim is proved by default: when an exercise, an example of a rule or a proof of the wp calculator is shown, the engine runs in the background and each claim shows its answer.

**Guiding rule: the engine implements the proof system of the course, and nothing else.** For a student, nothing changes at the level of the logic. The programs, the specification language, the triples, the rules, the wp equations, the intermediate assertions, the invariants, the variants and the verification conditions are exactly those of the slides and of the reference document HoareLogic.pdf. The solver only replaces one activity: deciding whether a formula of logic and arithmetic, with no program in it, is valid. Students do this by hand, and the website used to test it.

The engine translates the annotated programs into an internal language with the commands `assert`, `assume` and `havoc` (section 5). This language is used only inside the engine, and its translation is chosen so that the checks it produces are exactly the checks of the course.

The only differences a student can notice are in the status of a claim: "proved" instead of "no counterexample found", "does not hold" with a counterexample found by the solver, and sometimes "not decided" (section 3.3).

## 2. Testing and proving: what each one establishes

**What counts as evidence.** The tester's evidence is a list of evaluations. For an implication $P \Rightarrow Q$ it picks states, keeps those that satisfy $P$, and evaluates $Q$. The prover's evidence is the solver's answer about the same formula, for all values of its variables.

**What each method observes.** The tester observes concrete values: integers between $-4$ and $4$, the constants of the formula and their neighbours, and arrays of up to six cells. The solver observes no values. It reasons symbolically over all mathematical integers and all arrays.

**What the output means.** A failing test is a fact: the state shown breaks the claim, and anyone can check it by hand. A passing test means only that no tried state broke the claim. A proof ("the negation of the formula has no model") means that no state breaks it, provided the formula was built correctly and the solver is correct.

**What can go wrong.** The tester misses counterexamples with large numbers or long arrays. For example, $x * x \neq 2025$ passes every test with $|x| \le 4$ and is false for $x = 45$. The prover cannot miss such a state, but it can answer "not decided", and a bug in the engine could make it check the wrong formula. Section 9 explains how the design guards against the second problem.

**What claim the website can make.** After testing: "no counterexample among the states that were tried". After proving: "valid for every integer state". The website shows which of the two applies to each claim.

The site keeps both methods. The tests remain available in the summary of every exercise, as a second, independent check.

## 3. How an SMT solver decides an implication

### 3.1 Validity through unsatisfiability

An SMT solver answers one question: is there an assignment of values to the variables that makes a formula true? If there is, the formula is **satisfiable**, and the solver returns such an assignment, called a **model**. If there is none, the formula is **unsatisfiable**.

A verification condition (VC) must be **valid**: true for every assignment. A formula $\varphi$ is valid exactly when $\neg \varphi$ has no model. So the engine gives $\neg \varphi$ to the solver.

- **unsat**: no assignment makes $\neg \varphi$ true, so $\varphi$ is true for every assignment. The VC is proved.
- **sat**: the model makes $\varphi$ false. It is a counterexample, in the same sense as the counterexamples that students write by hand.
- **unknown**: the solver stopped without an answer (section 3.3).

### 3.2 A preservation check

Take the loop of the exercise "A loop that adds two in each iteration", with the invariant $s = 2 * i \wedge 0 \le i \le n$. Preservation is the implication $I \wedge B \Rightarrow wp(body, I)$, where the weakest precondition is computed with the assignment rule, as in the lectures:

$$s = 2 * i \wedge 0 \le i \le n \wedge i < n \;\Rightarrow\; s + 2 = 2 * (i + 1) \wedge 0 \le i + 1 \le n$$

The engine sends its negation to the solver, in the SMT-LIB language that Z3 and other solvers read:

```text
(declare-const i Int)
(declare-const s Int)
(declare-const n Int)
(assert (and (= s (* 2 i)) (<= 0 i) (<= i n) (< i n)))
(assert (not (and (= (+ s 2) (* 2 (+ i 1))) (<= 0 (+ i 1)) (<= (+ i 1) n))))
(check-sat)          ; unsat: preservation holds for all integers
```

With the candidate $s = 2 * i$ alone, the exit check $I \wedge \neg B \Rightarrow Q$ fails:

```text
(assert (and (= s (* 2 i)) (not (< i n))))
(assert (not (= s (* 2 n))))
(check-sat)          ; sat
(get-model)          ; for example i = 1, n = 0, s = 2
```

The model is the state that the recipe of the lectures asks students to find: it satisfies $I \wedge \neg B$ and not $Q$, and it shows that the bound $i \le n$ is missing.

The implemented engine sends exactly these queries for this exercise, and Z3 answers as shown; the model it returns for the weak invariant is $i = 1$, $n = 0$, $s = 2$. The wp calculator of the test site shows this counterexample at the conclusion of its example "A loop with a weak invariant".

### 3.3 What the solver can and cannot decide

"Not decided" follows from known limits of logic, and the website says why it happened.

- **Linear integer arithmetic** (sums, constants times variables, comparisons, connectives) is decidable: the solver always answers, given time. Most checks of the course are in this fragment.
- **Non-linear integer arithmetic** (products of variables such as $i * i$) is undecidable: no algorithm answers every such question. Z3 succeeds on the small formulas of the exercises, but it may answer "unknown" on others.
- **Recursive definitions** ($fib$, $fact$, $pow$, $sum$, $prod$) are unfolded a few steps on the terms of each check (section 7.5). A check that needs more steps is not decided.
- **Arrays** with reads and updates form a decidable theory, which corresponds to the select-store axioms of the reference document.

When the solver does not decide, the claim is shown as "not decided", with the reason. The logic is unchanged; only the tool is weaker on that formula.

## 4. Architecture

### 4.1 The pipeline

```text
 exercise (.hl), example of a rule, or proof built by the wp calculator
   │
   ▼
 1. Parser ─────────────► syntax trees (logic.js, format.js: unchanged)
   │
   ▼
 2. Slot resolution ────► the named assertions R1, I, ... replaced by their values
   │                       (checker.js, shared with the tests)
   ├──────────────────────────────┐
   ▼                              ▼
 3a. Claims of the steps         3b. Annotated program ──► internal language
     (calculation lines,             with assert / assume / havoc (ivl.js)
      verification conditions,         │
      rule instances)                  ▼
   │                              4. Checks: one closed implication per
   │                                 assert, with its name in the terms of
   │                                 the annotated program (ivl.js)
   ├──────────────────────────────┘
   ▼
 5. SMT encoder ────────► one SMT-LIB query per claim (smt.js)
   │
   ▼
 6. Z3 ─────────────────► unsat / sat + model / unknown + reason
   │
   ▼
 7. Result interpreter ─► proved / does not hold (model evaluated by logic.js)
   │                       / not decided (prover.js)
   ▼
 8. Step viewer ────────► the answer on every claim (app.js)
```

### 4.2 The components

**1. Parser.** The parser of `logic.js` and the reader of the exercise format, unchanged.

**2. Slot resolution.** The named assertions of an annotated program get their values from the steps, as for the tests. The same function is used, so the engine and the tests check the same formulas.

**3a. Claims of the steps.** Each claim becomes one implication: a calculation line `= B` after `A` under `assume: H` gives $H \Rightarrow (A \Leftrightarrow B)$, a verification condition $P \Rightarrow Q$ is checked as it is, and a triple $\{P\}\ c\ \{Q\}$ without loop gives $P \Rightarrow wp(c, Q)$ with the wp equations of the course.

**3b and 4. Annotated program.** The annotated program is translated into the internal language of section 5, and the checks are generated from it.

**5. SMT encoder.** It translates one implication into an SMT-LIB query (sections 7.4 and 7.5).

**6. Solver.** Z3 is reached through one function, `run(text)`, which evaluates SMT-LIB commands in a persistent context. The same code runs in the browser and in Node.js (section 9).

**7. Result interpreter.** It turns a model into a state, written as in the exercises ($x = 1, a = [4, 0, 9]$), and evaluates the implication in that state with the evaluator of the site, to confirm that the state really breaks it (section 10).

**8. Step viewer.** Every verification condition shows "proved", "does not hold" (with the counterexample found by Z3) or "not decided"; every line of a calculation shows ✓, ✗ or ?; a line above the steps gives the progress and the result; the summary lists every claim.

## 5. The internal verification language

### 5.1 The commands

| Command | Meaning | Effect on the checks (computed backwards) |
|---|---|---|
| `assert F` | $F$ must hold here | adds the check "$F$" |
| `assume F` | the paths on which $F$ is false are not considered | adds the hypothesis $F$ to the checks after it |
| `havoc V` | the variables $V$ get arbitrary values | the checks after it must hold for every value of $V$ |
| `x := E` | assignment | substitutes $E$ for $x$ in the checks after it |
| `c1; c2` | sequence | the checks of $c_2$, then those of $c_1$ |
| `c1 [] c2` | choice between two paths | the checks of both paths |

The checks are computed backwards with the weakest precondition of each command, keeping one check per `assert`. This is the calculus of the course, extended to the three commands that the students never see.

### 5.2 The translation of an annotated program

Every assertion $\{A\}$ of the annotated program becomes

```text
assert A; havoc ALL; assume A
```

where ALL is the set of **all** the variables: those of the program and the logical ones. (The first assertion of the program, the precondition, is only assumed.) The `havoc ALL` forgets everything that was known before the assertion. Each check therefore starts from one assertion alone, as each link of a proof outline is proved in the course:

- two consecutive assertions $\{A\}\ \{B\}$ give the check $A \Rightarrow B$;
- $\{A\}\ s\ \{B\}$, with $s$ without loop, gives $A \Rightarrow wp(s, B)$;

each closed over all the variables, and nothing else.

The statements are translated as follows:

| Statement | Translation |
|---|---|
| `x := E` | `assert def(b[J])` for every read $b[J]$ in $E$ (ARRAY-READ), then `x := E` |
| `a[I] := E` | `assert def(a[I])` and the reads in $I$ and $E$ (ARRAY-ASSIGN), then `a := a[I |-> E]` |
| `if B then c1 else c2` | `(assume B; c1) [] (assume !B; c2)` |
| `{I} while B do c` | `(assume B; c; assert I; assume false) [] assume !B` |

The assertion $\{I\}$ just before a loop is its invariant. With the cuts at the assertions, the checks of a loop are those of the rule with consequence:

- **initialisation:** the link that reaches $\{I\}$, from $P$ or from the assertion before the initialisation code;
- **preservation:** $I \wedge B \Rightarrow$ the first assertion of the body, the links of the body, and the end of the body back to $I$;
- **conclusion:** $I \wedge \neg B \Rightarrow$ the assertion after the loop.

The tests used to check the links inside the body, but not the entry into the body ($I \wedge B \Rightarrow$ first assertion) nor the return to $I$; the engine checks them as well.

### 5.3 Why "havoc ALL" and not only the modified variables

Usual verification tools (Dafny, Why3, Boogie) translate a loop with `havoc M`, where $M$ is the set of variables that the loop modifies. That translation keeps, at every iteration, the facts that the precondition states about the other variables. It is sound, but it accepts invariants that the course rejects: the invariant of the integer division without $y = y'$ is accepted, because $y = y'$ comes from the precondition (section 7.3, last paragraph). Since the checks would then differ from the checks that students prove by hand, the engine forgets all the variables at every assertion. With `havoc ALL`, each check is exactly the closed formula of the course.

### 5.4 Variants

With the rule WHILE-TOTAL, the body of the loop starts with $\{I \wedge B \wedge E = n\}$, where $n$ is the value of the variant when the iteration starts. In the course, the premise holds for every $n$, and the iteration gives $n$ the value of $E$. The engine does the same: a logical variable of the first assertion of the body that appears nowhere else gets, when the body is entered, the value given by a conjunct $E = n$ of that assertion. The check of the entry is then $I \wedge B \Rightarrow (I \wedge B \wedge E = n)[n \leftarrow E]$.

### 5.5 The names of the checks

Every check carries the assertion it starts from, the conditions of the branches taken, the statements executed and the assertion it reaches. The report names it in the terms of the annotated program, for example "{I && x < 10} implies {R1}" or "{R1} x := x + 1 {I}".

## 6. The languages

### 6.1 The programming language

Unchanged: `skip`, `x := E`, `a[I] := E`, sequence, `if B then c1 else c2` (with an optional else) and `while B do c`, with the expressions of the reference document. No new statement is added, since every new statement would need a new rule.

### 6.2 The specification language

Unchanged: preconditions, postconditions, intermediate assertions in proof outlines, loop invariants and variants, logical variables such as $x'$ or $A$. In the exercise format these are `pre`, `post`, the assertions in braces in the annotated program, and `set:` for the named ones.

One point needs a precise statement, since the engine must implement it and the lectures use it implicitly: **logical variables are universally quantified over the whole claim**. A triple with $x'$ claims the property for every value of $x'$, with the same value in the precondition and the postcondition. In a VC, a logical variable is an ordinary variable, and the solver checks the formula for all its values.

### 6.3 The assertion language

The formulas are those that the site already accepts: the arithmetic of the reference document, comparisons, the connectives, $def(a[i])$ and $sizeof(a)$, array updates $a[i \mapsto e]$, substitutions $Q[x \leftarrow E]$, quantifiers, sums and products over ranges, and the functions $fib$, $fact$, $pow$, $even$, $odd$, $abs$, $min$ and $max$.

The engine adds nothing to this language. It needs only that every symbol has one fixed meaning, the same in the lecture notes, in the tester and in the solver. Two symbols need a decision (section 11):

- **Integer division and remainder.** The SMT standard defines $div$ and $mod$ so that the remainder is never negative. The current tester rounds down. C rounds towards zero. The three agree when both operands are positive and differ otherwise, for example on $-7$ divided by $2$. The course must fix one meaning, and the engine encodes that meaning exactly. If the meaning is not the one of the SMT standard, the encoder defines it in terms of the standard one, so that the solver checks the course's definition.
- **Functions that the course defines on part of the integers**, such as $fib(n)$ and $fact(n)$ for $n \ge 0$. The engine uses the course's definition on that part. Outside it, the value is left unspecified, so that no claim can be proved by relying on it.

## 7. The wp equations and the SMT encoding

### 7.1 The wp equations

The engine and the wp calculator use only the equations of the course.

### 7.2 Weakest preconditions

These are the equations of the course, and only these:

| Statement | $wp(c, Q)$ | Rule |
|---|---|---|
| `skip` | $Q$ | SKIP |
| `x := E` | $Q[x \leftarrow E] \wedge def(b[J])$ for every read $b[J]$ in $E$ | ASSIGN, ARRAY-READ |
| `a[I] := E` | $Q[a \leftarrow a[I \mapsto E]] \wedge def(a[I]) \wedge def(b[J])$ for every read $b[J]$ in $E$ | ARRAY-ASSIGN |
| `c1; c2` | $wp(c1, wp(c2, Q))$ | SEQ |
| `if B then c1 else c2` | $(B \Rightarrow wp(c1, Q)) \wedge (\neg B \Rightarrow wp(c2, Q))$ | IF |
| `while B do c`, invariant $I$ | $I \wedge ((B \wedge I) \Rightarrow wp(c, I)) \wedge ((\neg B \wedge I) \Rightarrow Q)$, read as in 7.3 | WHILE-CONSEQUENCE |

The definedness conditions are added only where the course adds them, for reads and writes of arrays. When an expression reads no array, the first rows are exactly the assignment rule. The wp calculator of the site builds its proofs with these equations (`test/js/generate.js`), and the engine computes the weakest precondition of a loop-free triple with the same function (`HL.wp` in `logic.js`).

### 7.3 Loops: how the loop equation is read

The reference document (section 2.7.1.3) gives the loop equation

$$wp(while(B)\{c\}, Post) := I \wedge ((B \wedge I) \Rightarrow wp(c, I)) \wedge ((\neg B \wedge I) \Rightarrow Post)$$

The first conjunct, $I$, is establishment: it must hold in the state where the loop starts. The second conjunct is preservation and the third is exit. These two must hold in every state in which the loop can evaluate its condition, and not only in the state where the loop starts.

The formula does not say this explicitly, and the engine cannot read it literally. If the three conjuncts were all read as statements about the starting state, the check $P \Rightarrow wp(\texttt{while } B \texttt{ do } c, Q)$ would accept false triples. Take the triple $\{i = 0\}$ `while (i < 10) do i := i + 1` $\{false\}$, with the candidate invariant $I \equiv i \le 1$. The literal formula is

$$i \le 1 \wedge (i < 10 \wedge i \le 1 \Rightarrow i + 1 \le 1) \wedge (\neg(i < 10) \wedge i \le 1 \Rightarrow false)$$

In the state $i = 0$ all three conjuncts are true, so $i = 0 \Rightarrow wp$ is valid. The triple is false, since the loop stops with $i = 10$ and no state satisfies $false$. Preservation fails at $i = 1$, a state that the literal formula never looks at.

The engine therefore reads the second and third conjuncts as closed formulas. A closed formula is one with no free variables. Here it is obtained by quantifying universally over all the variables of the conjunct, which is written $\forall(\ldots)$ below:

$$wp(\texttt{while } B \texttt{ do } c, Q) = I \wedge \forall(B \wedge I \Rightarrow wp(c, I)) \wedge \forall(\neg B \wedge I \Rightarrow Q)$$

This is the reading under which the lectures prove preservation as the separate triple $\{I \wedge B\}\ c\ \{I\}$: a triple is valid only if it holds from every state that satisfies its precondition.

Two consequences follow.

- A closed formula is true or false, independently of the state. When the engine computes the weakest precondition of code that comes before the loop, the substitutions change only the conjunct $I$, since a closed formula contains no free variable to substitute. For a program $init;\ \texttt{while } B \texttt{ do } c$, the check $P \Rightarrow wp(init;\ \texttt{while } B \texttt{ do } c,\ Q)$ therefore splits into three verification conditions, which are the three checks of the lectures:
  - **Establishment:** $P \Rightarrow I$, or $P \Rightarrow wp(init, I)$ when initialisation code $init$ comes before the loop.
  - **Preservation:** $\forall(I \wedge B \Rightarrow wp(c, I))$.
  - **Exit:** $\forall(I \wedge \neg B \Rightarrow Q)$.
- The invariant must contain every fact that preservation and exit need, including facts about variables that the loop does not change. In the exercise on integer division, the invariant must contain $y = y'$. Without it, the solver finds the state $x' = 5$, $y' = 3$, $y = 2$, $q = 1$, $r = 2$, which satisfies the invariant and the condition, and from which one iteration breaks the invariant. This is the failure that a student meets by hand, and the reason to add $y = y'$.

**The predicate that the loop passes to the code before it is the invariant.** When preservation and exit are valid, the two closed conjuncts are true, and $wp(\texttt{while } B \texttt{ do } c, Q)$ reduces to $I$. When one of them is not valid, the conjunct is false and the whole formula becomes $false$. In that case the engine reports the failing check with its counterexample, instead of reporting a failure of $P \Rightarrow false$. So the engine never obtains anything weaker than the invariant $I$ that the exercise or the student gives. The loop equation computes the weakest precondition relative to the given invariant, and this can be stronger than the true weakest precondition of the loop.

For example, take `while (i < n) do i := i + 1` with $Q \equiv i \ge n$. Every run that terminates ends with $i \ge n$, so the true weakest precondition is $true$. With the invariant $I \equiv i \le n$, preservation and exit are valid, and the engine passes $i \le n$ to the code before the loop. From the state $i = 7$, $n = 3$, the loop does not run and $Q$ holds, but this state does not satisfy $i \le n$. With the invariant $I \equiv true$, the checks are also valid, and the engine passes $true$.

As a consequence, a failed establishment check, $P \Rightarrow I$ or $P \Rightarrow wp(init, I)$, shows that the given invariant does not fit the precondition. It does not show that the triple is false. The report must say this, and must not present the counterexample as a run of the program that breaks $Q$.

There is a second possible reading, which the engine does not use. The two conjuncts can be quantified only over the variables that the loop assigns, $q$ and $r$ in the division loop. The other variables then stay free, and they receive the facts that $P$ states about them, such as $y = y'$. This is the reading of the usual havoc encoding with the modified variables. It accepts the division invariant without $y = y'$, so it does not match the exercises of the course; the engine uses havoc on all the variables instead (section 5.3).

With a variant $E$, the engine adds the two checks of WHILE-TOTAL, with a fresh logical variable $n$ for the value of $E$ at the start of an iteration:

- $I \wedge B \Rightarrow E \ge 0$
- $I \wedge B \wedge E = n \Rightarrow wp(c, E < n)$

For a loop inside the body $c$ of another loop, computing $wp(c, I)$ applies the same loop equation to the inner loop, with the invariant given for it, and its closed conjuncts become further verification conditions.

### 7.4 The encoding of the symbols

Every symbol has the meaning of the course and of the tests (`logic.js`, function `evaluate`).

| Symbol | Encoding |
|---|---|
| integers, `+`, `-`, `*`, comparisons | the SMT integers (mathematical integers) |
| `x div y`, `x mod y` | round down, as the tests: `hl_div(a, b) = ite(b > 0, div(a, b), div(-a, -b))` and `hl_mod(a, b) = a - b * hl_div(a, b)`; division by 0 is left unspecified |
| an array `a` | an SMT array `(Array Int Int)` and a separate length `len#a >= 0`; `sizeof(a)` is the length, `def(a[i])` is `0 <= i < len#a`, an update keeps the length, and two arrays are equal when their contents and lengths are equal |
| `fib`, `fact`, `pow`, `^` | declared functions with a one-step definition `_step`; outside the natural numbers their value is an unspecified function, so nothing can be proved by relying on it |
| `sum(k, lo, hi, e)`, `prod(...)` | a declared function of the bounds and of the free variables of $e$, with the definition of the course: $0$ (or $1$) when $hi < lo$, and $F(lo, hi - 1) + e[k \leftarrow hi]$ otherwise |
| `forall`, `exists` | the SMT quantifiers over the integers |

Which names are arrays is inferred from their use, as in the tests: a name read as $a[i]$, updated, or passed to `sizeof` is an array, and so is a name compared with an array.

### 7.5 Recursive definitions

The definitions of `fib`, `fact`, `pow`, `sum` and `prod` are unfolded on the terms of each check: for a term $fact(i + 1)$ the query contains $fact(i + 1) = fact\_step(i + 1)$ and the same for $fact(i)$, which is the step that the proofs of the course use. A power with a constant exponent, such as $i^2$, is unfolded down to the exponent $0$. A term under a quantifier, whose arguments are bound, uses instead the general axiom with a pattern, which the solver instantiates on the terms it meets.

Two choices of the first prototype were changed after the tests:

- `define-fun-rec` made the WebAssembly build of Z3 crash when it was used inside the scopes of the queries, and its lazy unfolding did not decide simple checks of the factorial exercise within the time limit. The definitions are now declared functions with their one-step definition, unfolded explicitly.
- A quantified axiom with the pattern $F(lo, hi)$ creates the new term $F(lo, hi - 1)$, which matches the pattern again: the unfolding never stops and the solver reaches its time limit. The explicit unfolding on the terms of the check avoids this loop.

Because the definitions are only partly unfolded, a model can give a recursive function values that its definition does not allow; such a model is not a real counterexample. Every model is therefore evaluated (section 10). When a model is not confirmed, or when the solver gives no answer, the engine searches again for a counterexample among small numbers (between $-10$ and $10$, arrays of at most 8 cells), with the definitions unfolded 12 steps, so that they are exact on those numbers. If that search finds no confirmed counterexample either, the claim is "not decided".

## 8. Results and explanations

### 8.1 The status of a claim

| Status | Meaning |
|---|---|
| Proved | The solver answered `unsat`: the claim holds in every state. |
| Does not hold | The solver gave a model, and evaluating the claim in it confirms that it is false. The state is shown as the counterexample found by Z3. |
| Refuted, as the exercise states | The claim does not hold, and the exercise says so (a verification condition with `status: fails`, a link of an invalid triple, a choice of invariant that does not lead to a proof, or an example of a rule that does not derive the triple). |
| Not decided | The solver did not answer within the limits, or its model is not confirmed and the definitions were only partly unfolded. The reason is given. |
| Prover error | The solver gave a model in which the claim holds, and no recursive definition was involved. This points to a bug in the engine (section 10). |

In an exercise, the answer of the prover is compared with the answer of the exercise; a difference is shown on the claim and counted in the line above the steps. In the wp calculator, the implications have no answer of their own: the result of the last step comes from the prover alone.

### 8.2 What a failing check means

The engine explains a model with the vocabulary of the course, according to the kind of check:

- **Consequence:** a state that satisfies the stronger formula and not the weaker one. For the specification of loop-free code, the engine also runs the program from that state, which shows that the triple is not valid.
- **Initialisation:** a start state that satisfies the precondition and not the invariant. The candidate is too strong, as in the table of the lectures.
- **Preservation:** a state that satisfies the invariant and the condition, from which one iteration leaves the invariant. The candidate is too weak and misses the fact that excludes this state, or the program is wrong.
- **Conclusion:** a state that satisfies the invariant and the negated condition, and not the postcondition. Often the bounds are missing.
- **Variant:** a state in which the variant is negative, or does not decrease.

## 9. Where Z3 runs

Z3 runs in the browser: the npm package `z3-solver` 4.13.0 contains Z3 compiled to WebAssembly (about 32 MB, MIT licence). The site stays a set of static files, there is no server, and nothing leaves the student's computer. The page uses the low-level interface of the package, bundled into `z3/z3-lowlevel.js`, and sends SMT-LIB text to `Z3_eval_smtlib2_string`.

- **Loading.** Z3 is loaded the first time a proof is needed, and then cached by the browser. The wp calculator computes its first example only when its page is opened, so that the other pages do not load Z3 before they need it.
- **Cross-origin isolation.** The WebAssembly build of Z3 uses threads, which browsers allow only on pages that are cross-origin isolated, through two HTTP headers that GitHub Pages does not let a site set. The service worker `coi-serviceworker.js` (MIT licence) adds the headers: on the first visit, the page registers it and reloads once.
- **Order of the queries.** The queries of all the proofs go through one queue, since they share one solver context (each query runs between `push` and `pop`).
- **Command line.** `tools/prove-exercises.js` runs the same code in Node.js with the same package.

Measured times: the whole collection (42 exercises and 22 examples of the rules) is proved in about 9 seconds in Node.js; in the browser, an exercise with a loop is proved in about 2 seconds, including the loading of Z3 from a local server.

## 10. What is trusted, and how it is checked

A proof by the engine is as good as the components that produced it: the parser, the slot resolution, the translation into the internal language, the encoder, and Z3. The design reduces the risk that a bug makes the engine prove a false claim.

1. **The checks are the course's formulas.** The translation produces exactly the links of the proof outline (section 5.2), and each check is named by the assertions it links. An author can read it in the report and check it by hand.
2. **Every model is checked.** A model is turned into a state, and the claim is evaluated in it with the evaluator of the site, which is independent code. A model in which the claim holds is never reported as a counterexample.
3. **A regression suite with known answers.** The 42 exercises and the 22 examples of the rules state, for every claim, whether it holds. The engine agrees with every one of them: 1052 claims proved, 42 refuted where the files say so (each with a confirmed counterexample), none undecided, none wrong. `tools/prove-exercises.js` reports any disagreement and returns an error code.
4. **The tests remain.** The tests on sample states remain available in the summary of every exercise, as a second, independent check.

Still to do: mutation tests that break solutions on purpose (drop a conjunct of an invariant, change a $<$ into $\le$, swap two statements) and verify that the engine rejects each broken solution with the expected kind of failure.

## 11. Decisions

Taken in the implementation, which you can still change:

1. **Where Z3 runs:** in the browser, with the service worker for GitHub Pages.
2. **Implementation language:** plain JavaScript, as the rest of the site.
3. **The meaning of $div$ and $mod$:** rounding down, as the tests. It should be written in the lecture notes.
4. **The domain of $fib$, $fact$ and $pow$:** the natural numbers; outside them the value is unspecified, so a claim that relies on $fib(-1)$ is not proved.

Open:

5. **The quantification in the loop equation.** The reference document and the slides could write the closure of section 7.3 explicitly, $I \wedge \forall(B \wedge I \Rightarrow wp(c, I)) \wedge \forall(\neg B \wedge I \Rightarrow Post)$, so that the equation cannot be read literally.
6. **The repository** where the engine will live.

## 12. Implementation status

- **Phase 0 (solver in the browser):** done.
- **Phase 1 (implications and loop-free programs):** done.
- **Phase 2 (loops, with invariants and variants):** done.
- **Phase 3 (arrays and recursive definitions):** done.
- **Proof by default:** done; every claim is proved when it is shown, and the wp calculator decides its implications only with the prover.
- **Next:** mutation tests (section 10); running Z3 in a Web Worker, so that a long query never blocks the page; a cache of the answers, keyed by the text of the query; and an editor in which a student writes an annotated program and gets one answer per link (phase 4).
