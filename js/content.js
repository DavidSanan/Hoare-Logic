/*
 * content.js
 *
 * The explanatory text of the website: the introduction, the language, the
 * rules and the method for loop invariants. The text uses the same small
 * markup as the exercises (see README.md):
 *
 *   $formula$        a formula, typeset with the notation of the slides
 *   `program`        a piece of program
 *   >> line          a displayed formula or triple, centred
 *   !! text          a note
 *   - item           a list item
 *   | a | b |        a table row (the first row is the header)
 *   ::rule NAME      the inference rule NAME, drawn as a fraction
 *   ## Title         a heading
 *
 * The notation follows the slides of ICT3112 and the reference document
 * HoareLogic.pdf (D. Sanan).
 */
(function (root) {
  'use strict';
  const HL = (root.HL = root.HL || {});

  // ------------------------------------------------------------------
  // Rules
  // ------------------------------------------------------------------

  HL.RULES = [
    {
      id: 'SKIP',
      name: 'Skip',
      premises: [],
      conclusion: '{Q} skip {Q}',
      wp: 'wp(skip, Q) = Q',
      says: 'If $Q$ holds before `skip`, then $Q$ holds after it. The rule is an axiom: it has no premises, so it can be used at any time.',
      mechanism: `
\`skip\` is the command that does nothing. It changes no variable, so the state after it is the state before it. Since an assertion is a property of the state, any assertion that is true before \`skip\` is still true after it.

The command exists for two reasons. First, it is the program that is left when an execution has finished. Second, it fills a missing branch: \`if B then c\` is the same program as \`if B then c else skip\`.`,
      example: `
>> {x > 0} skip {x > 0}

The rule only allows the same assertion on both sides. As a consequence, the rule alone cannot prove $\\{x > 5\\}$ \`skip\` $\\{x > 0\\}$, although this triple is valid. To prove it we also need the consequence rule, which accepts a precondition that implies the postcondition.

The triple $\\{x = 0\\}$ \`skip\` $\\{x = 1\\}$ is not valid. In the state $x = 0$ the precondition holds, \`skip\` does nothing, and $x = 1$ is false after it.`,
      check: 'Nothing. In practice the useful form is the one combined with the consequence rule: to prove $\\{P\\}$ `skip` $\\{Q\\}$, we prove $P ==> Q$.',
      limits: 'The rule does not let the precondition and the postcondition differ. Any difference has to be bridged by the consequence rule.'
    },
    {
      id: 'ASSIGN',
      name: 'Assignment',
      premises: [],
      conclusion: '{Q[x <- E]} x := E {Q}',
      wp: 'wp(x := E, Q) = Q[x <- E]',
      says: 'To make $Q$ true after `x := E`, it is enough that $Q$ with every $x$ replaced by $E$ is true before the assignment.',
      mechanism: `
$Q[x <- E]$ is the formula $Q$ in which every occurrence of the variable $x$ is replaced by the expression $E$. Other variables, including $x'$ or $x0$, are different variables and are not replaced.

The reason is the following. After \`x := E\`, the new value of $x$ is the value that $E$ had before the assignment, and every other variable keeps its value. So a statement about $x$ after the assignment is the same statement about $E$ before it. The substitution rewrites the statement in terms of the state before the assignment.

The rule is applied backwards: we know the postcondition and we compute the precondition. This is why the rule looks reversed the first time one reads it.`,
      example: `
>> {(y = 2)[y <- y + 1]} y := y + 1 {y = 2}
>> {y + 1 = 2} y := y + 1 {y = 2}
>> {y = 1} y := y + 1 {y = 2}

Concretely, if $y = 1$ before the assignment, then $y$ is $1 + 1 = 2$ after it. The substitution found exactly this condition.

With two variables, only the assigned one is replaced:

>> {(y = y' + x' && x = x')[y <- y + x]} y := y + x {y = y' + x' && x = x'}
>> {y + x = y' + x' && x = x'} y := y + x {y = y' + x' && x = x'}

The variable $x$ in the conjunct $x = x'$ is not touched, since the assignment changes $y$ only.`,
      check: 'Nothing. The rule is an axiom. The work is to do the substitution correctly and then to simplify the result.',
      limits: 'The rule gives exactly one precondition, the weakest one. If the specification gives another precondition $P$, we still have to prove $P ==> Q[x <- E]$ with the consequence rule. The rule is only for simple variables; arrays need ARRAY-ASSIGN.'
    },
    {
      id: 'CONSEQUENCE',
      name: 'Consequence',
      premises: ["P ==> P'", "{P'} c {Q'}", "Q' ==> Q"],
      conclusion: '{P} c {Q}',
      wp: '{P} c {Q} holds when P ==> wp(c, Q)',
      says: 'A proved triple stays valid if we make its precondition stronger or its postcondition weaker.',
      mechanism: `
An assertion stands for a set of states. $P ==> P'$ means that every state that satisfies $P$ also satisfies $P'$, so the set of $P$ is included in the set of $P'$. We say that $P$ is stronger than $P'$, and that $P'$ is weaker than $P$.

Suppose we have proved $\\{P'\\}$ \`c\` $\\{Q'\\}$. The triple makes a promise for every start state in $P'$. Since every state of $P$ is in $P'$, the promise also covers every start state of $P$. At the end, every state reached satisfies $Q'$. Since $Q' ==> Q$, it also satisfies $Q$. Hence $\\{P\\}$ \`c\` $\\{Q\\}$.

The two halves can be used alone. Weakening the precondition of the rule (premise $P ==> P'$) is the common case: the rules for assignment and sequence produce the weakest precondition $P'$, and the specification gives a stronger $P$.

>> P ==> P'   {P'} c {Q}   ---   {P} c {Q}
>> {P} c {Q'}   Q' ==> Q   ---   {P} c {Q}`,
      example: `
We want $\\{x > 120\\}$ \`x := x + 1\` $\\{x > 101\\}$. The assignment rule gives $\\{x + 1 > 101\\}$, which is $\\{x > 100\\}$. This is not the precondition of the specification, so we use the consequence rule:

>> x > 120 ==> x > 100   {x > 100} x := x + 1 {x > 101}   ---   {x > 120} x := x + 1 {x > 101}

The first premise is true: every number greater than $120$ is greater than $100$. In terms of sets, $\\{121, 122, ...\\}$ is included in $\\{101, 102, ...\\}$.`,
      check: 'The two implications $P ==> P\'$ and $Q\' ==> Q$. They are formulas of logic and arithmetic, with no program in them. We call them verification conditions.',
      limits: 'The rule never makes a precondition weaker or a postcondition stronger. If $P$ does not imply the computed $P\'$, the rule cannot be used, and the triple may well be invalid. In that case, look for a state that satisfies $P$ but not $P\'$: it is often a counterexample to the triple.'
    },
    {
      id: 'SEQ',
      name: 'Sequential composition',
      premises: ['{P} c1 {R}', '{R} c2 {Q}'],
      conclusion: '{P} c1; c2 {Q}',
      wp: 'wp(c1; c2, Q) = wp(c1, wp(c2, Q))',
      says: 'To prove a sequence, find an intermediate assertion $R$ that is at the same time the postcondition of the first command and the precondition of the second one.',
      mechanism: `
The execution of \`c1; c2\` runs \`c1\` and then runs \`c2\` from the state where \`c1\` stopped. The intermediate assertion $R$ describes these middle states. The first premise says that every middle state satisfies $R$. The second premise says that from any state of $R$, \`c2\` ends in $Q$.

The rule does not say how to find $R$. The weakest precondition calculus gives a systematic choice: $R = wp(c2, Q)$. We compute it from $Q$ and the last command, then we compute the precondition from $R$ and the previous command, and so on, from the end of the program to its start.

For $n$ commands the rule is applied $n - 1$ times, and we need $n - 1$ intermediate assertions:

>> wp(c1; c2; c3, Q) = wp(c1, wp(c2, wp(c3, Q)))`,
      example: `
>> {x = 0} x := x + 1 {x = 1}   {x = 1} x := x + 2 {x = 3}   ---   {x = 0} x := x + 1; x := x + 2 {x = 3}

Here $R$ is $x = 1$. With the wp calculus: $wp(x := x + 2, x = 3) = (x + 2 = 3)$, which is $x = 1$, and $wp(x := x + 1, x = 1) = (x + 1 = 1)$, which is $x = 0$.`,
      check: 'The two triples of the premises. In a backward proof each of them is obtained by the rule of the corresponding command, so the only remaining check is, at the very start, that the precondition of the specification implies the computed weakest precondition.',
      limits: 'A badly chosen $R$ can make one of the premises false even when the sequence is correct. The weakest precondition avoids this problem, since it is the weakest assertion that works for the second command.'
    },
    {
      id: 'IF',
      name: 'Conditional',
      premises: ['{P && B} c1 {Q}', '{P && !B} c2 {Q}'],
      conclusion: '{P} if B then c1 else c2 {Q}',
      wp: 'wp(if B then c1 else c2, Q) = (B ==> wp(c1, Q)) && (!B ==> wp(c2, Q))',
      says: 'Both branches must reach the postcondition. In the then branch we may also use that the condition $B$ is true, and in the else branch that it is false.',
      mechanism: `
Take a start state that satisfies $P$. There are two cases.

- If the state satisfies $B$, the program runs \`c1\`. The state satisfies $P$ and $B$, so the first premise applies, and the final state satisfies $Q$.
- If the state does not satisfy $B$, the program runs \`c2\`. The state satisfies $P$ and $!B$, so the second premise applies.

In both cases the final state satisfies $Q$. The extra knowledge $B$ or $!B$ is often what makes a branch provable.

The weakest precondition expresses the same case split as two implications. A state satisfies it when, in the case where $B$ is true, it satisfies $wp(c1, Q)$, and in the case where $B$ is false, it satisfies $wp(c2, Q)$.`,
      example: `
For \`if x = y then x := y + 1 else x := 1 - x\` with $Q$ equal to $x = y + 1$:

>> wp(x := y + 1, x = y + 1) = (y + 1 = y + 1)
>> wp(x := 1 - x, x = y + 1) = (1 - x = y + 1)

so the weakest precondition of the conditional is

>> (x = y ==> y + 1 = y + 1) && (!(x = y) ==> 1 - x = y + 1)

With the precondition $x + y = 0$ the first implication is trivially true, and the second one holds since $x + y = 0$ gives $1 - x = 1 + y$.

**Missing else branch.** \`if B then c\` means \`if B then c else skip\`. The second premise becomes $\\{P && !B\\}$ \`skip\` $\\{Q\\}$, and with the consequence rule this is the implication $P && !B ==> Q$: when the condition is false, the postcondition must already hold.`,
      check: 'One triple for each branch. With the wp calculus, one implication from the precondition to the formula above.',
      limits: 'Forgetting one branch is the classic mistake: the triple of the else branch is a real obligation, even when the else branch is `skip`.'
    },
    {
      id: 'WHILE',
      name: 'Loop (partial correctness)',
      premises: ['{I && B} c {I}'],
      conclusion: '{I} while B do c {I && !B}',
      wp: 'wp(while B do c, Q) = I && ((B && I) ==> wp(c, I)) && ((!B && I) ==> Q)',
      says: 'If one execution of the body keeps the invariant $I$ true whenever the loop condition holds, then the loop keeps $I$ true, and when it stops the condition is false.',
      mechanism: `
We cannot know in advance how many times the body runs, so we cannot apply SEQ a fixed number of times. Instead we use an argument by induction on the number of iterations. The invariant $I$ is an assertion that is true every time the condition of the loop is evaluated.

- Before the first iteration, $I$ holds, since it is the precondition of the conclusion.
- If $I$ holds at the start of an iteration, the condition $B$ also holds, since the body is running. The premise then says that $I$ holds at the end of the iteration, which is the start of the next one.
- The loop stops only when $B$ is false. At that moment $I$ still holds. So the final state satisfies $I && !B$.

The rule says nothing about termination. If the loop never stops, there is no final state, and the triple is true for any postcondition. This is the meaning of partial correctness.

The weakest precondition formula above assumes that someone gave the invariant $I$. The calculus cannot compute it.`,
      example: `
For \`while x > 0 do x := x - 1\` we take $I$ equal to $x >= 0$.

>> {x >= 0 && x > 0} x := x - 1 {x >= 0}

The assignment rule gives the precondition $x - 1 >= 0$, which is $x >= 1$, and $x >= 0 && x > 0 ==> x >= 1$ holds for integers. So the rule gives

>> {x >= 0} while x > 0 do x := x - 1 {x >= 0 && !(x > 0)}

and the postcondition simplifies to $x = 0$.`,
      check: 'The premise $\\{I && B\\}$ `c` $\\{I\\}$. This is called preservation.',
      limits: 'The rule needs an invariant, and finding it is the hard part of the proof. No algorithm finds invariants for every loop. The rule also gives no guarantee that the loop stops.'
    },
    {
      id: 'WHILE-CONSEQUENCE',
      name: 'Loop with consequence',
      premises: ['P ==> I', '{I && B} c {I}', 'I && !B ==> Q'],
      conclusion: '{P} while B do c {Q}',
      wp: '',
      says: 'This is the loop rule combined with the consequence rule. It is the form that we use in the exercises.',
      mechanism: `
The plain loop rule forces the precondition to be $I$ and the postcondition to be $I && !B$. A specification usually has another precondition $P$ and another postcondition $Q$. The consequence rule links them, and the three premises are the three checks of an invariant:

- **Establishment**, $P ==> I$: the invariant is true when the loop is reached. When the loop comes after some initialisation code, this check is a triple for that code, $\\{P\\}$ \`init\` $\\{I\\}$.
- **Preservation**, $\\{I && B\\}$ \`c\` $\\{I\\}$: one iteration of the body keeps the invariant.
- **Exit**, $I && !B ==> Q$: when the loop stops, the invariant and the negated condition give the postcondition.`,
      example: `
>> {x = 0} while x < 10 do x := x + 1 {x = 10}

With $I$ equal to $0 <= x <= 10$:

- Establishment: $x = 0 ==> 0 <= x <= 10$.
- Preservation: $wp(x := x + 1, I) = (0 <= x + 1 <= 10)$, and $0 <= x <= 10 && x < 10$ implies it.
- Exit: $0 <= x <= 10 && !(x < 10)$ gives $x = 10$.`,
      check: 'The three premises. A failing check comes with a state that breaks it, and this state tells us how to change the candidate invariant (see the page on loop invariants).',
      limits: 'Same as the loop rule: partial correctness only.'
    },
    {
      id: 'WHILE-TOTAL',
      name: 'Loop with a variant (termination)',
      premises: ['{I && B && E = n} c {I && E < n}', 'I && B ==> E >= 0'],
      conclusion: '{I} while B do c {I && !B}',
      wp: '',
      says: 'If an integer expression $E$, the variant, decreases in every iteration and is never negative when an iteration starts, then the loop stops.',
      mechanism: `
$n$ is a logical variable that records the value of $E$ at the start of an iteration. The first premise says that the body keeps the invariant and makes $E$ smaller than it was. The second premise says that $E$ is not negative whenever the body is about to run.

A sequence of integers that are all at least $0$ and that strictly decrease cannot go on for ever. Each iteration lowers $E$ by at least $1$, so after at most as many iterations as the first value of $E$, the condition $B$ must be false and the loop stops.

Typical variants:

- A loop that decreases $i$ while $i > 0$: the variant is $i$.
- A loop that increases $i$ while $i < n$: the variant is $n - i$.`,
      example: `
For \`while i < 10 do i := i + 1\` with invariant $i <= 10$ and variant $10 - i$:

>> {i <= 10 && i < 10 && 10 - i = n} i := i + 1 {i <= 10 && 10 - i < n}

The assignment rule gives $i + 1 <= 10 && 10 - (i + 1) < n$, and the precondition implies it since $10 - (i + 1) = n - 1$.`,
      check: 'Both premises. Together with the three checks of the invariant, they give total correctness: the loop stops and the postcondition holds.',
      limits: 'The variant must be bounded below. A decreasing expression that can become negative, such as $-i$ in a loop that increases $i$ for ever, proves nothing.'
    },
    {
      id: 'ARRAY-READ',
      name: 'Array read',
      premises: [],
      conclusion: '{Q[x <- E] && def(a[I])} x := E {Q}',
      wp: 'wp(x := E, Q) = Q[x <- E] && (def(b[J]) for every read b[J] in E)',
      says: 'An assignment whose expression reads arrays needs, in addition to the usual substitution, one condition for every read: the index must be inside the array.',
      mechanism: `
The rule above shows the case of one read $a[I]$ in $E$. In general we add one condition $def(b[J])$ for every read $b[J]$ that appears in $E$, including the reads inside an index, as in $a[b[j]]$.

>> def(a[I]) <=> 0 <= I < sizeof(a)

The positions of an array go from $0$ to $sizeof(a) - 1$. A read at another position has no value: Java raises an exception, and C has undefined behaviour. In both cases nothing can be promised about the state after the assignment. The condition $def$ removes these states from the precondition, so the triple makes no promise about them.

When $E$ reads no array, there is no condition to add, and the rule is the assignment rule.`,
      example: `
>> {a[i] + a[j] > 0 && def(a[i]) && def(a[j])} x := a[i] + a[j] {x > 0}

With the array $4, 0, 9$, $i = 2$ and $j = 7$, the read $a[j]$ does not exist. The precondition is false in this state, which is correct, since the program fails there.`,
      check: 'Nothing beyond the substitution, as for the assignment rule. Do not forget the definedness conditions when simplifying.',
      limits: 'The rule is for reads. A write into an array changes the whole array and needs ARRAY-ASSIGN.'
    },
    {
      id: 'ARRAY-ASSIGN',
      name: 'Array assignment',
      premises: [],
      conclusion: '{Q[a <- a[I |-> E]] && def(a[I]) && def(b[J])} a[I] := E {Q}',
      wp: 'wp(a[I] := E, Q) = Q[a <- a[I |-> E]] && def(a[I]) && (def(b[J]) for every read b[J] in E)',
      says: 'A write into a cell changes the whole array. So we substitute the updated array $a[I |-> E]$ for the array variable $a$, and never a single cell.',
      mechanism: `
$a[I |-> E]$ is the array that is equal to $a$ everywhere, except that position $I$ holds the value of $E$. It is a value written inside formulas, not a command.

A first idea is to substitute $E$ for the cell $a[I]$, as if the cell were a variable. This naive rule is wrong because of **aliasing**: two different expressions, such as $a[i]$ and $a[j]$, can name the same cell when $i = j$. Substitution works on the text of the formula, and the text $a[j]$ does not contain $a[i]$. For example, the naive rule proves $\\{a[j] = 0\\}$ \`a[i] := 1\` $\\{a[j] = 0\\}$, which is false when $i = j$.

The correct rule replaces every occurrence of $a$ in $Q$. Every read of the updated array is then simplified with the two **select-store axioms**, which force the question "is this the cell that was written?":

>> a[I |-> E][J] = E      when J = I
>> a[I |-> E][J] = a[J]   when J != I

When we cannot know whether $J = I$, we keep both cases: a formula $P(a[I |-> E][J])$ becomes $(J = I && P(E)) || (J != I && P(a[J]))$.

The array $a$ inside $E$ is not replaced. $E$ is evaluated before the write, so it refers to the old array, which is the array of the precondition.`,
      example: `
>> wp(a[i] := 1, a[j] = 0) = (a[i |-> 1][j] = 0) && def(a[i])

The select-store step gives $(j = i && 1 = 0) || (j != i && a[j] = 0)$, which simplifies to $j != i && a[j] = 0$. The condition $j != i$ is exactly what the naive rule missed.`,
      check: 'The three steps: substitution, select-store simplification, and the definedness conditions for the write and for every read in $E$.',
      limits: 'The same idea is the basis for reasoning about pointers, where two pointers can hold the same address. The rule handles one array; if two array variables may be the same array, that aliasing has to be modelled as well.'
    }
  ];

  HL.PSEUDO_RULES = {
    WP: { name: 'Weakest precondition', text: 'The step computes a weakest precondition with the equations of the wp calculus. Each equation corresponds to one rule of Hoare logic.' },
    LOGIC: { name: 'Logic and arithmetic', text: 'The step proves or simplifies a formula with ordinary logic and arithmetic. No rule of Hoare logic is used: the formula contains no program.' }
  };

  // ------------------------------------------------------------------
  // Pages
  // ------------------------------------------------------------------

  HL.PAGES = {};

  HL.PAGES.intro = `
## What a Hoare triple says

A Hoare triple is a claim about a program:

>> {P} C {Q}

$P$ is the precondition, $C$ is the program, and $Q$ is the postcondition. The triple says the following. For every state in which $P$ is true, if we run $C$ from that state and the execution terminates, then $Q$ is true in the final state.

>> {x = 0 && y = 1} x := x + y {x = 1 && y = 1}

This triple is valid: from the only start state allowed by the precondition, $x = 0$ and $y = 1$, the assignment produces $x = 1$ and leaves $y = 1$.

Three details of the definition matter in every exercise.

- The triple says nothing about the states where $P$ is false. A precondition that is false in every state, written $false$, makes every triple valid.
- The triple says nothing about executions that do not terminate. A loop that never stops satisfies any postcondition. This is called **partial correctness**. Termination is proved separately, with a variant.
- A triple is either valid or not valid. Hoare logic is the set of rules that lets us prove that a triple is valid without running the program on every state.

## States and assertions

A **state** gives a value to every variable of the program, for example $x = 3, y = -1$. An **assertion** is a formula about the variables, such as $x >= 0 && y >= 1$. An assertion stands for the set of states in which it is true:

>> x >= 0 && y >= 1

stands for the states $(x = 0, y = 1)$, $(x = 1, y = 1)$, $(x = 0, y = 2)$, and so on.

This view explains the words **stronger** and **weaker**. $P$ is stronger than $P'$ when $P ==> P'$, that is, when every state of $P$ is also a state of $P'$. For example $x > 5$ is stronger than $x > 0$. The strongest assertion is $false$, which stands for no state. The weakest assertion is $true$, which stands for every state.

| Assertion | Set of states | Compared with $x > 0$ |
|---|---|---|
| $x > 5$ | $\\{6, 7, 8, ...\\}$ | stronger, since $x > 5 ==> x > 0$ |
| $x > 0$ | $\\{1, 2, 3, ...\\}$ | the same |
| $x >= 0$ | $\\{0, 1, 2, ...\\}$ | weaker, since $x > 0 ==> x >= 0$ |

## Logical variables

Specifications often need to talk about the value that a variable had at the start. We use **logical variables** for this: names such as $x'$, $A$ or $n$ that the program never assigns. The precondition $x = x' && y = y'$ gives names to the initial values, and the postcondition $x = y' && y = x'$ says that the values were swapped.

!! The variables $x$ and $x'$ are two different variables. When a rule replaces $x$ by an expression, $x'$ stays as it is. This is one of the most frequent mistakes in the course.

## Proving a triple with rules

Hoare logic has one rule for each command of the language, and one more rule, the consequence rule, that links different assertions. A rule has premises above a line and a conclusion below it:

::rule SEQ

To prove the conclusion, we have to prove every premise. A rule without premises is an **axiom**, such as the rules for \`skip\` and for assignment. A proof is a tree of rules, with the triple we want at the root and axioms or facts of logic at the leaves.

The rules come in the section **Rules** of this website. Each one has an explanation of why it is correct, an example, and the formula of the weakest precondition that corresponds to it.

## Reasoning backwards: the weakest precondition

The rules say what to prove, but not how to find the intermediate assertions. The **weakest precondition** calculus, due to Dijkstra, computes them. $wp(C, Q)$ is the weakest assertion such that, from every state that satisfies it, $C$ ends in a state that satisfies $Q$ (if $C$ terminates).

The calculus works backwards, from the postcondition to the start of the program. For a loop-free program, every rule has an equation:

| Command | Weakest precondition |
|---|---|
| \`skip\` | $wp(skip, Q) = Q$ |
| \`x := E\` | $wp(x := E, Q) = Q[x <- E]$ |
| \`c1; c2\` | $wp(c1; c2, Q) = wp(c1, wp(c2, Q))$ |
| \`if B then c1 else c2\` | $wp(if B then c1 else c2, Q) = (B ==> wp(c1, Q)) && (!B ==> wp(c2, Q))$ |

Then the triple $\\{P\\}$ \`C\` $\\{Q\\}$ is valid exactly when $P ==> wp(C, Q)$. This last implication is a **verification condition**: a formula with no program in it, which we prove with logic and arithmetic. The consequence rule is the rule that turns this implication into the triple.

For a loop, the calculus needs an **invariant**, which we must provide ourselves. The page **Loop invariants** explains how to find one.

!! Hoare logic checks that a given triple is valid. The weakest precondition calculus computes, for a given program and postcondition, the precondition that the rules need. The two are used together: the calculus produces the intermediate assertions, and the rules justify each step.

## Frequent mistakes

These are the mistakes that appear most often in quizzes and exams.

- **Going forwards.** The rules are applied from the postcondition up to the precondition. Starting from the precondition and pushing it down does not follow the assignment rule.
- **Mixing $x$ and $x'$.** They are different variables. The substitution $[x <- x - y]$ replaces $x$ only. For example $(x = y' && y = x')[x <- x - y]$ is $x - y = y' && y = x'$, and $x'$ is not changed.
- **Inventing conjuncts.** An intermediate assertion must come from a rule. Adding a conjunct about a variable that is not in the formula, such as $k = k'$, is at best unnecessary and is often wrong.
- **Writing an assertion that no rule produced.** Every assertion in a proof outline must be justified by the rule of the command next to it or by an implication.
- **Sign errors when simplifying.** $x - (x - y)$ is $y$, and not $-y$. Keep the parentheses that a substitution introduces until you have simplified them carefully.
`;

  HL.PAGES.language = `
## The programming language

The programs of the course are written in a small imperative language. It has five commands, plus the array assignment of the section on arrays:

| Command | Meaning |
|---|---|
| \`skip\` | does nothing |
| \`x := E\` | evaluates $E$ and stores the value in $x$ |
| \`a[I] := E\` | stores the value of $E$ at position $I$ of the array $a$ |
| \`c1; c2\` | runs \`c1\`, then \`c2\` |
| \`if B then c1 else c2\` | runs \`c1\` if $B$ is true, and \`c2\` otherwise |
| \`while B do c\` | runs \`c\` again and again while $B$ is true |

Expressions are built from integer constants, variables, array reads $a[I]$, the operations $+$, $-$, $*$, $/$, $mod$ and $div$, comparisons and the logical operators. Following C, a condition that is not a comparison is true when its value is not zero.

!! The assignment is written \`:=\`. The symbol $=$ is equality, both in assertions and in the conditions of \`if\` and \`while\`.

## The specification language

Assertions are formulas of first-order logic over the integers. They may use the program variables, logical variables such as $x'$ or $A$, and the following functions: $fib(n)$, $fact(n)$ (written $n!$), $pow(a, b)$ or $a^b$, $abs(x)$, $even(x)$, $odd(x)$, $min$, $max$, $sizeof(a)$ and $def(a[i])$. Sums and products over a range are written $sum(k, lo, hi, e)$ and $prod(k, lo, hi, e)$, and the quantifiers are $forall k. P$ and $exists k. P$.

## How to type the notation

The exercise files and the calculators accept plain ASCII. The website displays the notation of the slides.

| You type | It is displayed as | Meaning |
|---|---|---|
| \`\`&&\`\` or \`\`/\\\`\` | $A && B$ | and |
| \`\`\|\|\`\` or \`\`\\/\`\` | $A || B$ | or |
| \`\`!\`\` | $!A$ | not |
| \`\`==>\`\` or \`\`=>\`\` | $A ==> B$ | implies |
| \`\`<=>\`\` | $A <=> B$ | if and only if |
| \`\`=\`\` or \`\`==\`\`, \`\`!=\`\` | $x = y$, $x != y$ | equality, difference |
| \`\`<=\`\`, \`\`>=\`\` | $x <= y$, $x >= y$ | comparisons; chains such as \`\`0 <= i <= n\`\` are allowed |
| \`\`x'\`\` | $x'$ | a logical variable |
| \`\`A0\`\`, \`\`x_k\`\` | $A0$, $x_k$ | a name with a subscript |
| \`\`2^n\`\` | $2^n$ | power |
| \`\`fact(n)\`\` or \`\`n!\`\` | $fact(n)$ | factorial |
| \`\`Q[x <- E]\`\` | $Q[x <- E]$ | substitution |
| \`\`a[i \|-> e]\`\` | $a[i |-> e]$ | array $a$ updated at $i$ |
| \`\`sum(k, 0, n-1, a[k])\`\` | $sum(k, 0, n - 1, a[k])$ | $a[0] + ... + a[n - 1]$ |
| \`\`forall k. P\`\` | $forall k. P$ | for every $k$ |
| \`\`wp(x := E, Q)\`\` | $wp(x := E, Q)$ | weakest precondition |
| \`\`x := E\`\` | \`x := E\` | assignment, in programs |

The Unicode symbols of the slides (∧, ∨, ¬, ⇒, ≤, ≥, ≠, ≔, ←) are accepted as well, so formulas can be pasted from the slides.

Multiplication must be written explicitly: \`\`n * (n + 1)\`\`, not \`\`n(n + 1)\`\`, which would be read as a function called $n$.
`;

  HL.PAGES.invariants = `
## What an invariant is

An invariant of a loop is an assertion that is true every time the loop condition is evaluated: before the first iteration, after every iteration, and when the loop stops. A candidate $I$ is an invariant that proves the specification $\\{P\\}$ \`while B do c\` $\\{Q\\}$ when it passes three checks:

- **Establishment.** $I$ is true when the loop is reached: $P ==> I$, or $\\{P\\}$ \`init\` $\\{I\\}$ when the loop comes after initialisation code.
- **Preservation.** One iteration keeps $I$ true: $\\{I && B\\}$ \`c\` $\\{I\\}$. We check it as $I && B ==> wp(c, I)$.
- **Exit.** When the loop stops, the invariant and the negated condition give the postcondition: $I && !B ==> Q$.

For termination we add a **variant** $E$: $I && B ==> E >= 0$, and $\\{I && B && E = n\\}$ \`c\` $\\{E < n\\}$.

!! Finding a candidate and checking it are two different activities. Finding is a heuristic: no algorithm finds the invariant of every loop. Checking is mechanical: each of the three checks is an implication that we can prove, or show to be false with a concrete state.

## A recipe for finding a candidate

The recipe of the lectures has five steps. We follow it on this loop:

\`\`\`
{n >= 0}
i := 0; s := 0;
while i < n do {
  i := i + 1;
  s := s + i
}
{s = n * (n + 1) / 2}
\`\`\`

**Step 1. Start from the postcondition.** Name the progress variable, $i$, which counts the iterations from $0$ to $n$, and the result variable, $s$, whose final value $Q$ constrains.

**Step 2. Trace the values at the loop head.** The invariant must hold at every loop head, so we write down the values there:

| At the loop head | $i$ | $s$ |
|---|---|---|
| before iteration 1 | $0$ | $0$ |
| before iteration 2 | $1$ | $1$ |
| before iteration 3 | $2$ | $3$ |
| before iteration 4 | $3$ | $6$ |

The values of $s$ are $0, 1, 3, 6$, that is $i * (i + 1) / 2$.

**Step 3. Generalise the postcondition.** At a loop head the loop is only part of the way through, so $Q$ is false there. Replace the final value $n$ by the progress variable $i$: $s = n * (n + 1) / 2$ becomes $s = i * (i + 1) / 2$. The result matches the trace, so we found the same formula in two independent ways.

**Step 4. Add the bounds.** When the loop stops, $!B$ only says $i >= n$. With the bound $i <= n$ we get $i = n$, which turns the invariant into $Q$:

>> I = (s = i * (i + 1) / 2 && 0 <= i <= n)

**Step 5. Check.** Establishment, preservation and exit, as above. When a check fails, write down a state that breaks it.

## Other ways to build a candidate

Replacing a constant by the progress variable is the most common way, but there are others.

- **Drop a conjunct** when part of $Q$ is already given by $!B$ at the exit, as in a search loop.
- **Use two progress variables** when the loop works on a range from both ends, as when reversing an array.
- **Add the fact that preservation needs** when a candidate fails preservation because the body uses a variable that the candidate says nothing about, as in the Fibonacci loop where we also need $b = fib(i + 1)$.

## What to do when a check fails

| Failing check | What the state shows | What to do |
|---|---|---|
| Establishment | a real start state that the candidate rejects | the candidate is too strong: weaken it |
| Preservation | a state that the candidate accepts, from which one iteration leaves the candidate | the candidate is too weak: add the fact that rules the state out |
| Exit | a state that satisfies $I && !B$ but not $Q$ | the candidate is too weak: often the bounds are missing |

For example, with the candidate $p = a * i$ for a multiplication loop \`while i < b do (p := p + a; i := i + 1)\`, the state $a = 2, b = 3, i = 4, p = 8$ satisfies $I && !B$ but $p != a * b$. The missing fact is the bound $0 <= i <= b$.
`;

  HL.PAGES.format = `
## How an exercise is written

An exercise is a plain text file with the extension \`\`.hl\`\`. The file is a list of **fields**. A field starts at the beginning of a line with its name and a colon, as in \`\`title: Swapping two variables\`\`. Its value is the rest of the line, followed by the lines below it that are indented. A line that starts with \`\`#\`\` is a comment.

The file has two parts. The first part describes the exercise: the task, the specification and the program. The second part is the solution, as a list of **steps**. Every \`\`step:\`\` line starts a new step, and the fields after it belong to that step.

## Fields of the exercise

| Field | Required | Content |
|---|---|---|
| \`\`id\`\` | yes | a short name made of letters, digits and \`\`-\`\`, used in the address of the page |
| \`\`title\`\` | yes | the title shown in the list |
| \`\`topic\`\` | no | the group in the list, for example \`\`Loops\`\` or \`\`Arrays\`\` |
| \`\`level\`\` | no | the difficulty, from 1 to 3 |
| \`\`source\`\` | no | where the exercise comes from |
| \`\`tags\`\` | no | words for the search, separated by commas |
| \`\`task\`\` | no | the statement given to the student |
| \`\`hint\`\` | no | a hint, hidden until the student opens it |
| \`\`pre\`\` | yes | the precondition |
| \`\`post\`\` | yes | the postcondition |
| \`\`program\`\` | yes | the annotated program (see below) |
| \`\`verdict\`\` | no | \`\`valid\`\` or \`\`invalid\`\`: the answer to "is the triple valid?" |
| \`\`summary\`\` | no | text shown at the end of the solution |
| \`\`range\`\` | no | the largest absolute value used by the tests (4 by default) |

## The annotated program

The program is written in the language of the course. Between the statements, an assertion in braces is part of the proof outline. When the braces contain a single name, such as \`\`{R1}\`\` or \`\`{I}\`\`, the assertion is a **named slot**: it is shown as unknown until a step gives it a value with \`\`set:\`\`. The names \`\`P\`\` and \`\`Q\`\` are given the precondition and the postcondition from the start. Any other formula in braces is shown as it is.

A comment \`\`// i1\`\` at the end of a statement gives it a label that the steps can use.

\`\`\`text
{P}
i := 0;
s := 0;      // init
{I}
while i < n do {
  {I && i < n}
  i := i + 1;
  {R1}
  s := s + 2
  {I}
}
{Q}
\`\`\`

Blocks of more than one statement need braces. Both \`\`if B then ... else ...\`\` and \`\`if (B) { ... } else { ... }\`\` are accepted, and so are \`\`while B do ...\`\` and \`\`while (B) { ... }\`\`.

## Fields of a step

| Field | Content |
|---|---|
| \`\`step\`\` | the title of the step |
| \`\`rule\`\` | the rules that the step applies, separated by commas: SKIP, ASSIGN, CONSEQUENCE, SEQ, IF, WHILE, WHILE-CONSEQUENCE, WHILE-TOTAL, ARRAY-READ, ARRAY-ASSIGN, and WP or LOGIC for a calculation or a proof in logic |
| \`\`focus\`\` | the statement that the step works on: its label, or the beginning of its text, such as \`\`x := y\`\` or \`\`while\`\`. Several statements are separated by commas |
| \`\`set\`\` | gives a value to a named slot of the program: \`\`set: R1 = x = B && t = A\`\`. The first \`\`=\`\` separates the name from the formula |
| \`\`text\`\` | an explanation |
| \`\`note\`\` | an explanation shown in a box |
| \`\`calc\`\` | a calculation, one formula per line (see below) |
| \`\`vc\`\` | a verification condition: an implication or a triple that must be proved |
| \`\`why\`\` | after \`\`vc\`\`: the justification |
| \`\`status\`\` | after \`\`vc\`\`: \`\`holds\`\` (the default) or \`\`fails\`\` |
| \`\`counterexample\`\` | after \`\`vc\`\`: a state that breaks the condition, such as \`\`x = 1, y = 2, a = [4, 0, 9]\`\` |
| \`\`instance\`\` | a rule with its premises and conclusion (see below) |
| \`\`assume\`\` | a formula that the calculations of the step may use, such as the invariant and the loop condition |
| \`\`result\`\` | the conclusion of the step |

The fields of a step are shown in the order in which they are written.

## Calculations

Each line of a \`\`calc\`\` block is a formula. Every line after the first starts with the relation that links it to the previous line: \`\`=\`\` or \`\`<=>\`\` when the two formulas are equivalent, \`\`==>\`\` when the previous line implies this one, and \`\`<==\`\` when this line implies the previous one. A justification can follow \`\`//\`\` at the end of the line.

\`\`\`text
calc:
  wp(y := t, Q)
  = Q[y <- t]
  = (x = B && y = A)[y <- t]
  = x = B && t = A        // only the y of y = A is replaced
\`\`\`

The calculation may use the names of the slots, such as \`\`Q\`\` or \`\`R1\`\`, and the notations \`\`Q[x <- E]\`\` and \`\`wp(c, Q)\`\`. The tests compute them.

## Rule instances

An \`\`instance\`\` block draws a rule with its premises, one per line, a line of dashes, and the conclusion. The name of the rule can follow \`\`instance:\`\`.

\`\`\`text
instance: CONSEQUENCE
  x > 120 ==> x > 100
  {x > 100} x := x + 1 {x > 101}
  ---
  {x > 120} x := x + 1 {x > 101}
\`\`\`

## Text

In \`\`task\`\`, \`\`text\`\`, \`\`note\`\`, \`\`why\`\` and \`\`summary\`\`, write formulas between dollar signs, as in \`\`$x >= 0$\`\`, and program fragments between backquotes, as in \`\`\`x := x + 1\`\`\`. A blank line starts a new paragraph, a line that starts with \`\`- \`\` is a list item, and a line that starts with \`\`>> \`\` is a displayed formula or triple. Write \`\`**text**\`\` for bold text.

## Testing an exercise

The button **Test** above the editor, and the button in the summary of every solution, evaluate the claims of the exercise on many small states: the triple of the specification, every line of every calculation, every verification condition, every rule instance, and every pattern \`\`{A} statement {B}\`\` of the annotated program with the final values of the slots. A failing test shows a state that breaks the claim. This catches most typing mistakes in assertions and invariants.

!! A passing test is not a proof. The tests only try integers between \`\`-range\`\` and \`\`range\`\` and short arrays. For example, a claim that is false only for large numbers passes the tests.

## Adding the exercise to the website

1. Save the file in the folder \`\`website/exercises\`\`. The names of the files decide the order in the list, so start the name with a number, as in \`\`35-my-exercise.hl\`\`.
2. Run \`\`python3 tools/build_exercises.py\`\` in the folder \`\`website\`\`. It collects every \`\`.hl\`\` file into \`\`exercises/bundle.js\`\`, which the page loads.
3. Optionally, run \`\`node tools/check-exercises.js\`\` to run the tests of every exercise from the command line.

The bundle is needed because a browser does not let a page opened from the disk read other files of the disk.
`;

  HL.TEMPLATE = `# A new exercise. Edit the fields below; the preview updates as you type.
id: my-exercise
title: Increment twice
topic: Sequential composition
level: 1
source: My exercise list
tags: assignment, sequence

task:
  Prove that the following triple is valid.

pre: x = 0
post: x = 3

program:
  {P}
  x := x + 1;    // i1
  {R1}
  x := x + 2     // i2
  {Q}

verdict: valid

step: The last statement
rule: ASSIGN, WP
focus: i2
calc:
  wp(x := x + 2, Q)
  = (x = 3)[x <- x + 2]
  = x + 2 = 3
  = x = 1
set: R1 = x = 1

step: The first statement
rule: ASSIGN, WP
focus: i1
calc:
  wp(x := x + 1, R1)
  = (x = 1)[x <- x + 1]
  = x + 1 = 1
  = x = 0

step: Compare with the precondition
rule: CONSEQUENCE
vc: x = 0 ==> x = 0
why:
  The weakest precondition is the precondition itself.
result: The triple is valid.
`;
})(typeof window !== 'undefined' ? window : globalThis);
