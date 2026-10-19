/*
 * rule-examples.js
 *
 * The interactive examples of the Rules page. Each example has:
 *
 *   title    the name shown on its tab
 *   goal     the triple (or implication) that we try to derive
 *   derived  true when the attempt succeeds (shown in green at the end),
 *            false when it fails (shown in red)
 *   valid    true or false: whether the triple itself is valid. It can be
 *            valid even when this rule alone cannot derive it. The command
 *            line tests check it by running the program; null skips the test.
 *   result   the sentence shown at the end
 *   steps    the explanation, one step at a time, in the markup of the site
 */
(function (root) {
  'use strict';
  const HL = (root.HL = root.HL || {});

  HL.RULE_EXAMPLES = {
    SKIP: [
      {
        title: 'Same assertion',
        goal: '{x > 0} skip {x > 0}',
        derived: true,
        valid: true,
        result: 'The rule SKIP derives this triple.',
        steps: [
          `We want to know whether the rule SKIP, on its own, gives this triple.`,
          `The rule SKIP gives every triple of this shape, for any assertion $Q$:

>> {Q} skip {Q}

The same assertion must appear before and after \`skip\`.`,
          `We match the triple with the rule. The postcondition is $x > 0$, so $Q$ is $x > 0$. The rule then gives:

>> {x > 0} skip {x > 0}`,
          `The triple given by the rule is exactly the triple we wanted.`
        ]
      },
      {
        title: 'Stronger precondition',
        goal: '{x > 5} skip {x > 0}',
        derived: false,
        valid: true,
        result: 'The rule SKIP alone cannot derive this triple. The triple is valid, and the consequence rule derives it.',
        steps: [
          `We want to know whether the rule SKIP, on its own, gives this triple.`,
          `The postcondition is $x > 0$, so the rule SKIP gives:

>> {x > 0} skip {x > 0}`,
          `We compare it with the triple we want. The postconditions are the same, but the preconditions are different formulas: $x > 5$ and $x > 0$.`,
          `The rule SKIP only gives triples with the same assertion on both sides, so it cannot give this triple.

The triple is still valid: every state with $x > 5$ also has $x > 0$, and \`skip\` does not change the state. The consequence rule uses exactly this implication, $x > 5 ==> x > 0$.`
        ]
      },
      {
        title: 'Different assertions',
        goal: '{x = 0} skip {x = 1}',
        derived: false,
        valid: false,
        result: 'The rule SKIP cannot derive this triple, and the triple is not valid.',
        steps: [
          `We want to know whether the rule SKIP, on its own, gives this triple.`,
          `The postcondition is $x = 1$, so the rule SKIP gives:

>> {x = 1} skip {x = 1}`,
          `The precondition of the triple we want is $x = 0$, which is a different formula. So the rule SKIP does not give the triple.`,
          `The consequence rule cannot help either: it would need $x = 0 ==> x = 1$, which is false.

The triple is not valid. In the state $x = 0$ the precondition holds, \`skip\` does nothing, and $x = 1$ is false at the end.`
        ]
      }
    ],

    ASSIGN: [
      {
        title: 'Increment',
        goal: '{y = 1} y := y + 1 {y = 2}',
        derived: true,
        valid: true,
        result: 'The rule ASSIGN derives this triple.',
        steps: [
          `We want to know whether the rule ASSIGN gives this triple.`,
          `The rule ASSIGN gives, for any assertion $Q$:

>> {Q[x <- E]} x := E {Q}

The precondition is the postcondition with the assigned variable replaced by the expression.`,
          `We match the triple with the rule. The assigned variable $x$ is $y$, the expression $E$ is $y + 1$, and $Q$ is $y = 2$.`,
          `We compute the precondition that the rule gives:

>> (y = 2)[y <- y + 1]
>> y + 1 = 2
>> y = 1`,
          `The rule gives $\\{y + 1 = 2\\}$ \`y := y + 1\` $\\{y = 2\\}$. For integers, $y + 1 = 2$ and $y = 1$ hold in exactly the same states, so this is the triple we wanted.`
        ]
      },
      {
        title: 'Wrong precondition',
        goal: '{y = 2} y := y + 1 {y = 2}',
        derived: false,
        valid: false,
        result: 'The rule ASSIGN does not derive this triple, and the triple is not valid.',
        steps: [
          `We want to know whether the rule ASSIGN gives this triple.`,
          `We match the triple with the rule: the variable is $y$, the expression is $y + 1$, and $Q$ is $y = 2$. The precondition given by the rule is:

>> (y = 2)[y <- y + 1]
>> y + 1 = 2
>> y = 1`,
          `The rule gives the precondition $y = 1$, but the triple has $y = 2$. These formulas hold in different states, so the rule does not give the triple.`,
          `The triple is not valid. From the state $y = 2$ the assignment gives $y = 3$, and $y = 2$ is false at the end.`
        ]
      },
      {
        title: 'Two variables',
        goal: "{y = y' && x = x'} y := y + x {y = y' + x' && x = x'}",
        derived: true,
        valid: true,
        result: 'The rule ASSIGN derives this triple.',
        steps: [
          `We want to know whether the rule ASSIGN gives this triple. The names $x'$ and $y'$ are logical variables: the program never assigns them.`,
          `We match the triple with the rule. The assigned variable is $y$, the expression is $y + x$, and $Q$ is $y = y' + x' && x = x'$.`,
          `We replace every $y$ in $Q$ by $y + x$. The variables $x$, $x'$ and $y'$ are different variables, so they stay as they are:

>> (y = y' + x' && x = x')[y <- y + x]
>> y + x = y' + x' && x = x'`,
          `We simplify with the second conjunct: since $x = x'$, the first conjunct $y + x = y' + x'$ becomes $y = y'$.

>> y = y' && x = x'`,
          `This is the precondition of the triple we wanted.`
        ]
      }
    ],

    CONSEQUENCE: [
      {
        title: 'Stronger precondition',
        goal: '{x > 120} x := x + 1 {x > 101}',
        derived: true,
        valid: true,
        result: 'The consequence rule derives this triple.',
        steps: [
          `We want to derive this triple. We start with the assignment rule, which gives the weakest precondition of $x > 101$:

>> (x > 101)[x <- x + 1]
>> x + 1 > 101
>> x > 100`,
          `So we have $\\{x > 100\\}$ \`x := x + 1\` $\\{x > 101\\}$. Its precondition, $x > 100$, is not the precondition of the triple we want, $x > 120$.`,
          `The consequence rule links them. Its first premise is the implication from the precondition we want to the precondition we have:

>> x > 120 ==> x > 100

It holds: every number greater than $120$ is greater than $100$.`,
          `The postconditions are the same, so the last premise, $x > 101 ==> x > 101$, holds trivially. All premises hold:

>> x > 120 ==> x > 100   {x > 100} x := x + 1 {x > 101}   ---   {x > 120} x := x + 1 {x > 101}`
        ]
      },
      {
        title: 'Weaker precondition',
        goal: '{x > 90} x := x + 1 {x > 101}',
        derived: false,
        valid: false,
        result: 'The consequence rule cannot derive this triple, and the triple is not valid.',
        steps: [
          `As in the first example, the assignment rule gives:

>> {x > 100} x := x + 1 {x > 101}`,
          `To use the consequence rule we need the implication:

>> x > 90 ==> x > 100`,
          `This implication is false. The state $x = 95$ satisfies $x > 90$ and not $x > 100$. So the premise does not hold, and the rule cannot be applied.`,
          `The state also shows that the triple is not valid: from $x = 95$ the program gives $x = 96$, and $x > 101$ is false at the end.`
        ]
      },
      {
        title: 'Both sides',
        goal: '{2 <= x <= 8} y := x * 10 {0 <= y <= 100}',
        derived: true,
        valid: true,
        result: 'The consequence rule derives this triple.',
        steps: [
          `We use the full rule. We choose a stronger postcondition $Q'$ that is simpler to work with: the values of $y$ that the program can produce from $x$ between $1$ and $9$.

>> 10 <= y <= 90`,
          `The assignment rule gives the precondition for $Q'$:

>> (10 <= y <= 90)[y <- x * 10]
>> 10 <= x * 10 <= 90
>> 1 <= x <= 9

So $P'$ is $1 <= x <= 9$.`,
          `First premise: the precondition we want implies $P'$.

>> 2 <= x <= 8 ==> 1 <= x <= 9

It holds, since every number from 2 to 8 is also between 1 and 9.`,
          `Third premise: $Q'$ implies the postcondition we want.

>> 10 <= y <= 90 ==> 0 <= y <= 100

It holds, since every number from 10 to 90 is also between 0 and 100.`,
          `All three premises hold:

>> 2 <= x <= 8 ==> 1 <= x <= 9   {1 <= x <= 9} y := x * 10 {10 <= y <= 90}   10 <= y <= 90 ==> 0 <= y <= 100   ---   {2 <= x <= 8} y := x * 10 {0 <= y <= 100}`
        ]
      }
    ],

    SEQ: [
      {
        title: 'Two increments',
        goal: '{x = 0} x := x + 1; x := x + 2 {x = 3}',
        derived: true,
        valid: true,
        result: 'The rule SEQ derives this triple.',
        steps: [
          `The rule SEQ needs an intermediate assertion $R$ between the two assignments:

>> {x = 0} x := x + 1 {R}   {R} x := x + 2 {x = 3}   ---   {x = 0} x := x + 1; x := x + 2 {x = 3}`,
          `We compute $R$ backwards, from the second assignment and the postcondition:

>> wp(x := x + 2, x = 3)
>> x + 2 = 3
>> x = 1

So $R$ is $x = 1$, and the second premise holds by the assignment rule.`,
          `We check the first premise, $\\{x = 0\\}$ \`x := x + 1\` $\\{x = 1\\}$, with the assignment rule:

>> (x = 1)[x <- x + 1]
>> x + 1 = 1
>> x = 0

This is the precondition we have.`,
          `Both premises hold:

>> {x = 0} x := x + 1 {x = 1}   {x = 1} x := x + 2 {x = 3}   ---   {x = 0} x := x + 1; x := x + 2 {x = 3}`
        ]
      },
      {
        title: 'No possible R',
        goal: '{x = 0} x := x + 1; x := x * 2 {x = 3}',
        derived: false,
        valid: false,
        result: 'The rule SEQ cannot derive this triple, and the triple is not valid.',
        steps: [
          `We look for an intermediate assertion $R$ and compute it backwards from the postcondition:

>> wp(x := x * 2, x = 3)
>> x * 2 = 3`,
          `No integer $x$ satisfies $2 * x = 3$, so $R$ is $false$: no state before the second assignment leads to $x = 3$.`,
          `The first premise would be $\\{x = 0\\}$ \`x := x + 1\` $\\{false\\}$. Its weakest precondition is $false$, and $x = 0$ does not imply $false$. So the first premise does not hold.`,
          `The triple is not valid. From $x = 0$ the program computes $x = 1$ and then $x = 2$, and $x = 3$ is false at the end.`
        ]
      }
    ],

    IF: [
      {
        title: 'Maximum',
        goal: '{true} if x >= y then m := x else m := y {m >= x && m >= y}',
        derived: true,
        valid: true,
        result: 'The rule IF derives this triple.',
        steps: [
          `The rule IF has one premise per branch. In the then branch we may also assume the condition, and in the else branch its negation:

>> {true && x >= y} m := x {m >= x && m >= y}   {true && !(x >= y)} m := y {m >= x && m >= y}   ---   {true} if x >= y then m := x else m := y {m >= x && m >= y}`,
          `Then branch. The assignment rule gives the precondition:

>> (m >= x && m >= y)[m <- x]
>> x >= x && x >= y

The condition of the branch gives $x >= y$, and $x >= x$ always holds. So the first premise holds.`,
          `Else branch. The assignment rule gives:

>> (m >= x && m >= y)[m <- y]
>> y >= x && y >= y

The negated condition $!(x >= y)$ means $x < y$, which gives $y >= x$. So the second premise holds.`,
          `Both premises hold, so the rule IF gives the triple.`
        ]
      },
      {
        title: 'A branch fails',
        goal: '{true} if x > 0 then y := x else y := 0 {y > 0}',
        derived: false,
        valid: false,
        result: 'The rule IF cannot derive this triple, and the triple is not valid.',
        steps: [
          `The two premises are:

>> {true && x > 0} y := x {y > 0}   {true && !(x > 0)} y := 0 {y > 0}   ---   {true} if x > 0 then y := x else y := 0 {y > 0}`,
          `Then branch. The assignment rule gives $(y > 0)[y <- x]$, that is $x > 0$, which is exactly the condition of the branch. The first premise holds.`,
          `Else branch. The assignment rule gives:

>> (y > 0)[y <- 0]
>> 0 > 0
>> false

The precondition of the branch, $true && !(x > 0)$, does not imply $false$. The second premise does not hold.`,
          `The triple is not valid: from $x = 0$ the else branch sets $y$ to $0$, and $y > 0$ is false at the end.`
        ]
      }
    ],

    WHILE: [
      {
        title: 'A good invariant',
        goal: '{x >= 0} while x > 0 do x := x - 1 {x >= 0 && !(x > 0)}',
        derived: true,
        valid: true,
        result: 'The rule WHILE derives this triple with the invariant x ≥ 0.',
        steps: [
          `We try the invariant $I = (x >= 0)$. The rule WHILE has one premise: one iteration of the body keeps $I$ when the condition holds.

>> {x >= 0 && x > 0} x := x - 1 {x >= 0}   ---   {x >= 0} while x > 0 do x := x - 1 {x >= 0 && !(x > 0)}`,
          `We compute the weakest precondition of the body for $I$:

>> (x >= 0)[x <- x - 1]
>> x - 1 >= 0
>> x >= 1`,
          `The premise holds if $x >= 0 && x > 0$ implies $x >= 1$. For integers, $x > 0$ is the same as $x >= 1$, so the implication holds.`,
          `The premise holds, so the rule gives the triple. Its postcondition $x >= 0 && !(x > 0)$ says that the loop stops with $x = 0$, if it stops.`
        ]
      },
      {
        title: 'A bad invariant',
        goal: '{x > 0} while x > 0 do x := x - 1 {x > 0 && !(x > 0)}',
        derived: false,
        valid: false,
        result: 'The rule WHILE cannot be applied with the invariant x > 0.',
        steps: [
          `We try the invariant $I = (x > 0)$. The premise is:

>> {x > 0 && x > 0} x := x - 1 {x > 0}`,
          `We compute the weakest precondition of the body for $I$:

>> (x > 0)[x <- x - 1]
>> x - 1 > 0
>> x > 1`,
          `The premise holds if $x > 0$ implies $x > 1$. It does not: the state $x = 1$ satisfies $x > 0$, and the body makes it $x = 0$, which leaves the candidate.`,
          `The candidate is not an invariant, since the last iteration takes $x$ from $1$ to $0$. The rule cannot be applied with it. The previous example shows a candidate that works.`
        ]
      }
    ],

    'WHILE-CONSEQUENCE': [
      {
        title: 'Counting to 10',
        goal: '{x = 0} while x < 10 do x := x + 1 {x = 10}',
        derived: true,
        valid: true,
        result: 'The rule derives this triple with the invariant 0 ≤ x ≤ 10.',
        steps: [
          `We try the invariant $I = (0 <= x <= 10)$. The rule has three premises: establishment, preservation and the postcondition at the exit.

>> x = 0 ==> I   {I && x < 10} x := x + 1 {I}   I && !(x < 10) ==> x = 10   ---   {x = 0} while x < 10 do x := x + 1 {x = 10}`,
          `Establishment:

>> x = 0 ==> 0 <= x <= 10

It holds: $0$ is between $0$ and $10$.`,
          `Preservation. The weakest precondition of the body for $I$ is:

>> (0 <= x <= 10)[x <- x + 1]
>> 0 <= x + 1 <= 10

From $0 <= x$ we get $0 <= x + 1$, and from $x < 10$ we get $x + 1 <= 10$. So $I && x < 10$ implies it.`,
          `Exit:

>> 0 <= x <= 10 && !(x < 10) ==> x = 10

$!(x < 10)$ is $x >= 10$, and with $x <= 10$ it gives $x = 10$. All three premises hold.`
        ]
      },
      {
        title: 'Missing bound',
        goal: '{x = 0} while x < 10 do x := x + 1 {x = 10}',
        derived: false,
        valid: true,
        result: 'The rule cannot derive the triple with the invariant 0 ≤ x. The triple is valid, and the invariant 0 ≤ x ≤ 10 works.',
        steps: [
          `We try the invariant $I = (0 <= x)$, without the upper bound.`,
          `Establishment, $x = 0 ==> 0 <= x$, holds. Preservation also holds: the body gives $0 <= x + 1$, which follows from $0 <= x$.`,
          `Exit:

>> 0 <= x && !(x < 10) ==> x = 10

It does not hold. The state $x = 11$ satisfies $0 <= x$ and $x >= 10$, but not $x = 10$.`,
          `The candidate is an invariant, but it is too weak to give the postcondition. The bound $x <= 10$ is the missing fact that turns $x >= 10$ into $x = 10$.`
        ]
      }
    ],

    'WHILE-TOTAL': [
      {
        title: 'A decreasing variant',
        goal: '{i <= 10} while i < 10 do i := i + 1 {i <= 10 && !(i < 10)}',
        derived: true,
        valid: true,
        result: 'The loop stops: the variant 10 − i works.',
        steps: [
          `We use the invariant $I = (i <= 10)$ and try the variant $E = 10 - i$. $n$ is a logical variable for the value of $E$ at the start of an iteration.

>> {i <= 10 && i < 10 && 10 - i = n} i := i + 1 {i <= 10 && 10 - i < n}   i <= 10 && i < 10 ==> 10 - i >= 0   ---   {i <= 10} while i < 10 do i := i + 1 {i <= 10 && !(i < 10)}`,
          `The variant is not negative when an iteration starts:

>> i <= 10 && i < 10 ==> 10 - i >= 0

It holds, since $i < 10$ gives $10 - i > 0$.`,
          `The body keeps the invariant and decreases the variant. The weakest precondition of the postcondition of the first premise is:

>> (i <= 10 && 10 - i < n)[i <- i + 1]
>> i + 1 <= 10 && 10 - (i + 1) < n`,
          `From $i < 10$ we get $i + 1 <= 10$. From $10 - i = n$ we get $10 - (i + 1) = n - 1 < n$. Both premises hold, so the loop stops.`
        ]
      },
      {
        title: 'A loop that never stops',
        goal: '{x >= 0} while x >= 0 do x := x + 1 {x >= 0 && !(x >= 0)}',
        derived: false,
        valid: null,
        result: 'No variant works: this loop never stops.',
        steps: [
          `We use the invariant $I = (x >= 0)$ and look for a variant.`,
          `First try, $E = x$. It is not negative while the loop runs, but the body increases it: from $x = n$ we get $x = n + 1$, which is not smaller than $n$. The first premise fails.`,
          `Second try, $E = -x$. It decreases in every iteration, but it is negative: the state $x = 1$ satisfies $I && x >= 0$, and $-x = -1$. The second premise fails.`,
          `No variant can work, since the loop never stops: $x$ only grows, so the condition $x >= 0$ stays true. The rule for partial correctness still gives the triple, because a loop that never stops satisfies any postcondition.`
        ]
      }
    ],

    'ARRAY-READ': [
      {
        title: 'With the bounds',
        goal: '{a[i] > 0 && 0 <= i < sizeof(a)} x := a[i] {x > 0}',
        derived: true,
        valid: true,
        result: 'The rule ARRAY-READ derives this triple.',
        steps: [
          `The expression $a[i]$ reads the array once, at position $i$. The rule ARRAY-READ substitutes as the assignment rule does, and adds one condition for the read.`,
          `Substitution:

>> (x > 0)[x <- a[i]]
>> a[i] > 0`,
          `Definedness of the read:

>> def(a[i]) <=> 0 <= i < sizeof(a)`,
          `The rule gives the precondition $a[i] > 0 && 0 <= i < sizeof(a)$, which is the precondition we have.`
        ]
      },
      {
        title: 'Without the bounds',
        goal: '{a[i] > 0} x := a[i] {x > 0}',
        derived: false,
        valid: null,
        result: 'The rule ARRAY-READ cannot derive this triple: the read may be outside the array.',
        steps: [
          `The rule gives the precondition $a[i] > 0 && def(a[i])$, as in the previous example.`,
          `To use it, the precondition we have must imply it. In particular it must imply that the read is defined:

>> a[i] > 0 ==> 0 <= i < sizeof(a)`,
          `Nothing in $a[i] > 0$ says that position $i$ exists. Take the array 4, 0, 9 and $i = 7$: the read $a[7]$ has no value. In Java it raises an exception, and in C its behaviour is undefined.`,
          `The precondition does not exclude this state, so the rule cannot derive the triple. Adding $0 <= i < sizeof(a)$ to the precondition repairs it, as in the previous example.`
        ]
      }
    ],

    'ARRAY-ASSIGN': [
      {
        title: 'The correct rule',
        goal: '{j != i && a[j] = 0 && 0 <= i < sizeof(a)} a[i] := 1 {a[j] = 0}',
        derived: true,
        valid: true,
        result: 'The rule ARRAY-ASSIGN derives this triple.',
        steps: [
          `The write is at position $i$ and the value is $1$. The rule replaces the array $a$ in the postcondition by the updated array $a[i |-> 1]$.

>> (a[j] = 0)[a <- a[i |-> 1]]
>> a[i |-> 1][j] = 0`,
          `We do not know whether $j$ is equal to $i$, so the select-store axioms keep both cases:

>> (j = i && 1 = 0) || (j != i && a[j] = 0)`,
          `The first case is $false$, since $1 = 0$ is false. What remains is:

>> j != i && a[j] = 0`,
          `We add the definedness of the write, $0 <= i < sizeof(a)$. The rule gives the precondition $j != i && a[j] = 0 && 0 <= i < sizeof(a)$, which is the precondition we have.`
        ]
      },
      {
        title: 'Forgetting aliasing',
        goal: '{a[j] = 0 && 0 <= i < sizeof(a)} a[i] := 1 {a[j] = 0}',
        derived: false,
        valid: false,
        result: 'The rule ARRAY-ASSIGN does not derive this triple, and the triple is not valid.',
        steps: [
          `This is the precondition that the naive rule gives: it replaces the text $a[i]$ in the postcondition, and $a[j] = 0$ does not contain it.`,
          `The rule ARRAY-ASSIGN gives the precondition $j != i && a[j] = 0 && 0 <= i < sizeof(a)$, as in the previous example. To use it, we need:

>> a[j] = 0 && 0 <= i < sizeof(a) ==> j != i`,
          `This implication is false. Take the array 4, 0, 9 and $i = j = 1$: $a[1] = 0$ and position $1$ exists, but $j = i$.`,
          `The same state shows that the triple is not valid: the write sets $a[1]$ to $1$, so $a[j] = 0$ is false at the end. When $i = j$, $a[i]$ and $a[j]$ are the same cell.`
        ]
      }
    ]
  };
})(typeof window !== 'undefined' ? window : globalThis);
