/*
 * rule-examples.js
 *
 * The interactive examples of the Rules page. Each example has:
 *
 *   title    the name shown on its tab
 *   goal     the triple that we try to derive
 *   derived  true when the attempt succeeds (shown in green at the end),
 *            false when it fails (shown in red)
 *   valid    true or false: whether the triple itself is valid. It can be
 *            valid even when this rule alone cannot derive it. The command
 *            line tests check it by running the program; null skips the test.
 *   result   the sentence shown at the end
 *   given    the elements of the example, always shown under the triple:
 *            a list of [label, value]; a value "{{R}}" shows the named
 *            assertion R once a step has computed it
 *   slots    the named assertions known from the start
 *   rule     the rule with the elements of the example, always shown:
 *            { premises: [{ f, part }], conclusion }. The premise whose
 *            part is the part of the current step is highlighted.
 *   steps    one object per step:
 *              part     the part of the proof (Establishment, ...); the
 *                       navigation groups the steps by part
 *              head     what the step does, in one sentence
 *              show     formulas to display; «formula : label» draws the
 *                       label under the formula, to show where it comes from
 *              calc     lines added to the running calculation, each one
 *                       "= formula // justification"
 *              calcNew  true when the step starts a new calculation
 *              assume   a hypothesis under which the calculation lines of
 *                       the step are equivalent (used by the tests)
 *              set      named assertions computed by the step
 *              text     a short explanation
 *
 * In all the strings, {{R}} is replaced by the value of R when it is known.
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
        given: [['Precondition P', '$x > 0$'], ['Postcondition Q', '$x > 0$']],
        steps: [
          {
            head: 'The rule SKIP gives the triple in which the precondition is the postcondition $Q$.',
            calc: ['wp(skip, x > 0)', '= x > 0 // wp(skip, Q) = Q']
          },
          {
            head: 'The precondition $P$ is the formula given by the rule.',
            show: ['«x > 0 : P» <=> «x > 0 : wp»'],
            text: 'So the rule SKIP gives the triple directly.'
          }
        ]
      },
      {
        title: 'Stronger precondition',
        goal: '{x > 5} skip {x > 0}',
        derived: false,
        valid: true,
        result: 'The rule SKIP alone does not derive this triple. With the consequence rule the triple is derived, so it is valid.',
        given: [['Precondition P', '$x > 5$'], ['Postcondition Q', '$x > 0$']],
        steps: [
          {
            head: 'The rule SKIP gives the triple in which the precondition is the postcondition $Q$.',
            calc: ['wp(skip, x > 0)', '= x > 0 // wp(skip, Q) = Q']
          },
          {
            head: 'The precondition $P$ is a different formula, so the rule SKIP alone does not give the triple.',
            text: 'The consequence rule gives it if $P$ implies the computed precondition.',
            show: ['«x > 5 : P» ==> «x > 0 : wp»']
          },
          {
            head: 'The implication holds: every integer greater than 5 is greater than 0.',
            show: ['«x > 5 : P» ==> «x > 0 : wp»']
          }
        ]
      },
      {
        title: 'Different assertions',
        goal: '{x = 0} skip {x = 1}',
        derived: false,
        valid: false,
        result: 'The rule SKIP does not derive this triple, and the triple is not valid.',
        given: [['Precondition P', '$x = 0$'], ['Postcondition Q', '$x = 1$']],
        steps: [
          {
            head: 'The rule SKIP gives the triple in which the precondition is the postcondition $Q$.',
            calc: ['wp(skip, x = 1)', '= x = 1 // wp(skip, Q) = Q']
          },
          {
            head: 'The precondition $P$ is a different formula. The consequence rule would need this implication:',
            show: ['«x = 0 : P» ==> «x = 1 : wp»']
          },
          {
            head: 'The implication is false in the state $x = 0$.',
            text: 'From this state `skip` does not change $x$, so $x = 1$ is false at the end. The triple is not valid.'
          }
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
        given: [['Assigned variable', '$y$'], ['Assignment expression', '$y + 1$'], ['Postcondition Q', '$y = 2$'], ['Precondition P', '$y = 1$']],
        steps: [
          {
            head: 'The precondition is obtained by substituting the assigned variable ($y$) with the assignment expression ($y + 1$) in $Q$.',
            calc: ['(y = 2)[y <- y + 1]']
          },
          {
            head: 'We apply the substitution: every $y$ in $Q$ becomes $y + 1$.',
            calc: ['= y + 1 = 2 // y replaced by y + 1']
          },
          {
            head: 'We simplify: subtracting 1 from both sides of $y + 1 = 2$ gives $y = 1$.',
            calc: ['= y = 1 // subtract 1 from both sides']
          },
          {
            head: 'The precondition $P$ is the formula we obtained.',
            show: ['«y = 1 : P» <=> «y = 1 : wp»'],
            text: 'Strictly, the rule gives the precondition $y + 1 = 2$. The consequence rule replaces it by $P$, since $y = 1 ==> y + 1 = 2$.'
          }
        ]
      },
      {
        title: 'Wrong precondition',
        goal: '{y = 2} y := y + 1 {y = 2}',
        derived: false,
        valid: false,
        result: 'The rule ASSIGN does not derive this triple, and the triple is not valid.',
        given: [['Assigned variable', '$y$'], ['Assignment expression', '$y + 1$'], ['Postcondition Q', '$y = 2$'], ['Precondition P', '$y = 2$']],
        steps: [
          {
            head: 'The precondition is obtained by substituting the assigned variable ($y$) with the assignment expression ($y + 1$) in $Q$.',
            calc: ['(y = 2)[y <- y + 1]']
          },
          {
            head: 'We apply the substitution: every $y$ in $Q$ becomes $y + 1$.',
            calc: ['= y + 1 = 2 // y replaced by y + 1']
          },
          {
            head: 'We simplify: subtracting 1 from both sides of $y + 1 = 2$ gives $y = 1$.',
            calc: ['= y = 1 // subtract 1 from both sides']
          },
          {
            head: 'The precondition $P$ is a different formula. The consequence rule would need this implication:',
            show: ['«y = 2 : P» ==> «y = 1 : wp»'],
            text: 'It is false in the state $y = 2$. From this state the assignment gives $y = 3$, so $Q$ is false at the end.'
          }
        ]
      },
      {
        title: 'Two variables',
        goal: "{y = y' && x = x'} y := y + x {y = y' + x' && x = x'}",
        derived: true,
        valid: true,
        result: 'The rule ASSIGN derives this triple.',
        given: [['Assigned variable', '$y$'], ['Assignment expression', '$y + x$'], ['Postcondition Q', "$y = y' + x' && x = x'$"],
          ['Precondition P', "$y = y' && x = x'$"], ['Logical variables', "$x'$ and $y'$: the program never assigns them"]],
        steps: [
          {
            head: 'The precondition is obtained by substituting the assigned variable ($y$) with the assignment expression ($y + x$) in $Q$.',
            calc: ["(y = y' + x' && x = x')[y <- y + x]"]
          },
          {
            head: "We apply the substitution. Only $y$ is replaced: $x$, $x'$ and $y'$ are other variables.",
            calc: ["= y + x = y' + x' && x = x' // y replaced by y + x"]
          },
          {
            head: "The second conjunct says $x = x'$, so in the first conjunct we can replace $x'$ by $x$.",
            calc: ["= y + x = y' + x && x = x' // x' replaced by x, using x = x'"]
          },
          {
            head: 'We subtract $x$ from both sides of the first conjunct.',
            calc: ["= y = y' && x = x' // subtract x from both sides"]
          },
          {
            head: 'The precondition $P$ is the formula we obtained.',
            show: ["«y = y' && x = x' : P» <=> «y = y' && x = x' : wp»"],
            text: "Strictly, the rule gives the first formula of the calculation. The consequence rule replaces it by the equivalent formula $P$."
          }
        ]
      }
    ],

    CONSEQUENCE: [
      {
        title: 'Stronger precondition',
        goal: '{x > 120} x := x + 1 {x > 101}',
        derived: true,
        valid: true,
        result: 'The three premises hold, so the consequence rule derives the triple.',
        given: [['Precondition P', '$x > 120$'], ['Program c', '`x := x + 1`'], ['Postcondition Q', '$x > 101$'],
          ["Q'", '$x > 101$, the postcondition $Q$ itself'], ["P'", "{{P'}}"]],
        slots: { "Q'": 'x > 101' },
        rule: {
          premises: [
            { f: "x > 120 ==> {{P'}}", part: 'First premise' },
            { f: "{{{P'}}} x := x + 1 {{{Q'}}}", part: 'Middle premise' },
            { f: "{{Q'}} ==> x > 101", part: 'Last premise' }
          ],
          conclusion: '{x > 120} x := x + 1 {x > 101}'
        },
        steps: [
          {
            part: 'Middle premise',
            head: "We take $Q' = Q$ and compute $P'$ with the rule ASSIGN: we substitute $x$ with $x + 1$ in $Q'$.",
            calc: ['(x > 101)[x <- x + 1]', '= x + 1 > 101 // x replaced by x + 1']
          },
          {
            part: 'Middle premise',
            head: 'We subtract 1 from both sides.',
            calc: ['= x > 100 // subtract 1 from both sides'],
            set: { "P'": 'x > 100' },
            text: "So $P' = x > 100$, and the rule ASSIGN gives the middle premise."
          },
          {
            part: 'First premise',
            calcNew: true,
            head: "The precondition $P$ must imply $P'$.",
            show: ["«x > 120 : P» ==> «x > 100 : P'»"],
            text: 'It holds: every integer greater than 120 is greater than 100.'
          },
          {
            part: 'Last premise',
            head: "$Q'$ must imply $Q$.",
            show: ["«x > 101 : Q'» ==> «x > 101 : Q»"],
            text: 'It holds, since the two formulas are the same.'
          }
        ]
      },
      {
        title: 'Weaker precondition',
        goal: '{x > 90} x := x + 1 {x > 101}',
        derived: false,
        valid: false,
        result: 'The first premise does not hold, so the consequence rule cannot derive the triple. The triple is not valid.',
        given: [['Precondition P', '$x > 90$'], ['Program c', '`x := x + 1`'], ['Postcondition Q', '$x > 101$'],
          ["Q'", '$x > 101$, the postcondition $Q$ itself'], ["P'", "{{P'}}"]],
        slots: { "Q'": 'x > 101' },
        rule: {
          premises: [
            { f: "x > 90 ==> {{P'}}", part: 'First premise' },
            { f: "{{{P'}}} x := x + 1 {{{Q'}}}", part: 'Middle premise' },
            { f: "{{Q'}} ==> x > 101", part: 'Last premise' }
          ],
          conclusion: '{x > 90} x := x + 1 {x > 101}'
        },
        steps: [
          {
            part: 'Middle premise',
            head: "We take $Q' = Q$ and compute $P'$ with the rule ASSIGN: we substitute $x$ with $x + 1$ in $Q'$.",
            calc: ['(x > 101)[x <- x + 1]', '= x + 1 > 101 // x replaced by x + 1']
          },
          {
            part: 'Middle premise',
            head: 'We subtract 1 from both sides.',
            calc: ['= x > 100 // subtract 1 from both sides'],
            set: { "P'": 'x > 100' },
            text: "So $P' = x > 100$, and the rule ASSIGN gives the middle premise."
          },
          {
            part: 'First premise',
            calcNew: true,
            head: "The precondition $P$ must imply $P'$.",
            show: ["«x > 90 : P» ==> «x > 100 : P'»"],
            text: "It is false: the state $x = 95$ satisfies $P$ and not $P'$. From this state the program gives $x = 96$, so $Q$ is false at the end."
          }
        ]
      },
      {
        title: 'Using a known triple',
        goal: '{x = 3} y := x + 1 {y > 0}',
        derived: true,
        valid: true,
        result: 'The three premises hold, so the consequence rule derives the triple from the known triple.',
        given: [['Precondition P', '$x = 3$'], ['Program c', '`y := x + 1`'], ['Postcondition Q', '$y > 0$'],
          ['Known triple', '$\\{x >= 0\\}$ `y := x + 1` $\\{y >= 1\\}$'], ["P'", '$x >= 0$, from the known triple'], ["Q'", '$y >= 1$, from the known triple']],
        slots: { "P'": 'x >= 0', "Q'": 'y >= 1' },
        rule: {
          premises: [
            { f: "x = 3 ==> {{P'}}", part: 'First premise' },
            { f: "{{{P'}}} y := x + 1 {{{Q'}}}", part: 'Middle premise' },
            { f: "{{Q'}} ==> y > 0", part: 'Last premise' }
          ],
          conclusion: '{x = 3} y := x + 1 {y > 0}'
        },
        steps: [
          {
            part: 'Middle premise',
            head: "The middle premise is the known triple. We check it with the rule ASSIGN: we substitute $y$ with $x + 1$ in $Q'$.",
            calc: ['(y >= 1)[y <- x + 1]', '= x + 1 >= 1 // y replaced by x + 1']
          },
          {
            part: 'Middle premise',
            head: 'We subtract 1 from both sides.',
            calc: ['= x >= 0 // subtract 1 from both sides'],
            text: "This is $P'$, so the known triple is given by the rule ASSIGN."
          },
          {
            part: 'First premise',
            calcNew: true,
            head: "The precondition $P$ must imply $P'$.",
            show: ["«x = 3 : P» ==> «x >= 0 : P'»"],
            text: 'It holds: when $x = 3$, $x >= 0$ is true.'
          },
          {
            part: 'Last premise',
            head: "$Q'$ must imply $Q$.",
            show: ["«y >= 1 : Q'» ==> «y > 0 : Q»"],
            text: 'It holds: for integers, $y >= 1$ is the same as $y > 0$.'
          }
        ]
      }
    ],

    SEQ: [
      {
        title: 'Two increments',
        goal: '{x = 0} x := x + 1; x := x + 2 {x = 3}',
        derived: true,
        valid: true,
        result: 'Both premises hold, so the rule SEQ derives the triple.',
        given: [['Precondition P', '$x = 0$'], ['First statement c1', '`x := x + 1`'], ['Second statement c2', '`x := x + 2`'],
          ['Postcondition Q', '$x = 3$'], ['Intermediate assertion R', '{{R}}']],
        rule: {
          premises: [
            { f: '{x = 0} x := x + 1 {{{R}}}', part: 'First premise' },
            { f: '{{{R}}} x := x + 2 {x = 3}', part: 'Second premise' }
          ],
          conclusion: '{x = 0} x := x + 1; x := x + 2 {x = 3}'
        },
        steps: [
          {
            part: 'Second premise',
            head: 'We compute $R$ backwards, from the second statement: we substitute $x$ with $x + 2$ in $Q$.',
            calc: ['(x = 3)[x <- x + 2]', '= x + 2 = 3 // x replaced by x + 2']
          },
          {
            part: 'Second premise',
            head: 'We subtract 2 from both sides.',
            calc: ['= x = 1 // subtract 2 from both sides'],
            set: { R: 'x = 1' },
            text: 'So $R = x = 1$, and the rule ASSIGN gives the second premise.'
          },
          {
            part: 'First premise',
            calcNew: true,
            head: 'We compute the weakest precondition of the first statement for $R$: we substitute $x$ with $x + 1$ in $R$.',
            calc: ['(x = 1)[x <- x + 1]', '= x + 1 = 1 // x replaced by x + 1']
          },
          {
            part: 'First premise',
            head: 'We subtract 1 from both sides.',
            calc: ['= x = 0 // subtract 1 from both sides']
          },
          {
            part: 'First premise',
            head: 'By the consequence rule, the precondition $P$ must imply this formula.',
            show: ['«x = 0 : P» ==> «x = 0 : wp(c1, R)»'],
            text: 'The two formulas are the same, so the first premise holds.'
          }
        ]
      },
      {
        title: 'No possible R',
        goal: '{x = 0} x := x + 1; x := x * 2 {x = 3}',
        derived: false,
        valid: false,
        result: 'The first premise does not hold, so the rule SEQ cannot derive the triple. The triple is not valid.',
        given: [['Precondition P', '$x = 0$'], ['First statement c1', '`x := x + 1`'], ['Second statement c2', '`x := x * 2`'],
          ['Postcondition Q', '$x = 3$'], ['Intermediate assertion R', '{{R}}']],
        rule: {
          premises: [
            { f: '{x = 0} x := x + 1 {{{R}}}', part: 'First premise' },
            { f: '{{{R}}} x := x * 2 {x = 3}', part: 'Second premise' }
          ],
          conclusion: '{x = 0} x := x + 1; x := x * 2 {x = 3}'
        },
        steps: [
          {
            part: 'Second premise',
            head: 'We compute $R$ backwards, from the second statement: we substitute $x$ with $x * 2$ in $Q$.',
            calc: ['(x = 3)[x <- x * 2]', '= x * 2 = 3 // x replaced by x * 2']
          },
          {
            part: 'Second premise',
            head: 'No integer $x$ satisfies $x * 2 = 3$, since $x * 2$ is even and 3 is odd.',
            calc: ['= false // x * 2 is even and 3 is odd'],
            set: { R: 'false' },
            text: 'So $R = false$: no state before the second statement leads to $Q$.'
          },
          {
            part: 'First premise',
            calcNew: true,
            head: 'We compute the weakest precondition of the first statement for $R$: we substitute $x$ with $x + 1$ in $R$.',
            calc: ['(false)[x <- x + 1]', '= false // false contains no x']
          },
          {
            part: 'First premise',
            head: 'By the consequence rule, the precondition $P$ must imply this formula.',
            show: ['«x = 0 : P» ==> «false : wp(c1, R)»'],
            text: 'It is false in the state $x = 0$. From this state the program gives $x = 1$ and then $x = 2$, so $Q$ is false at the end.'
          }
        ]
      }
    ],

    IF: [
      {
        title: 'Maximum',
        goal: '{true} if x >= y then m := x else m := y {m >= x && m >= y}',
        derived: true,
        valid: true,
        result: 'Both premises hold, so the rule IF derives the triple.',
        given: [['Precondition P', '$true$'], ['Condition B', '$x >= y$'], ['Then branch c1', '`m := x`'], ['Else branch c2', '`m := y`'],
          ['Postcondition Q', '$m >= x && m >= y$']],
        rule: {
          premises: [
            { f: '{«true : P» && «x >= y : B»} m := x {«m >= x && m >= y : Q»}', part: 'Then branch' },
            { f: '{«true : P» && «!(x >= y) : ¬B»} m := y {«m >= x && m >= y : Q»}', part: 'Else branch' }
          ],
          conclusion: '{true} if x >= y then m := x else m := y {m >= x && m >= y}'
        },
        steps: [
          {
            part: 'Then branch',
            head: 'We compute the weakest precondition of `m := x` for $Q$: we substitute $m$ with $x$.',
            calc: ['(m >= x && m >= y)[m <- x]', '= x >= x && x >= y // m replaced by x']
          },
          {
            part: 'Then branch',
            head: 'The comparison $x >= x$ is always true.',
            calc: ['= x >= y // x >= x is true, and true && A is A']
          },
          {
            part: 'Then branch',
            head: 'By the consequence rule, the precondition of the branch must imply this formula.',
            show: ['«true : P» && «x >= y : B» ==> «x >= y : wp»'],
            text: 'It holds: the right side is the condition $B$ itself.'
          },
          {
            part: 'Else branch',
            calcNew: true,
            head: 'We compute the weakest precondition of `m := y` for $Q$: we substitute $m$ with $y$.',
            calc: ['(m >= x && m >= y)[m <- y]', '= y >= x && y >= y // m replaced by y']
          },
          {
            part: 'Else branch',
            head: 'The comparison $y >= y$ is always true.',
            calc: ['= y >= x // y >= y is true, and A && true is A']
          },
          {
            part: 'Else branch',
            head: 'By the consequence rule, the precondition of the branch must imply this formula.',
            show: ['«true : P» && «!(x >= y) : ¬B» ==> «y >= x : wp»'],
            text: 'It holds: $!(x >= y)$ means $x < y$, which gives $y >= x$.'
          }
        ]
      },
      {
        title: 'A branch fails',
        goal: '{true} if x > 0 then y := x else y := 0 {y > 0}',
        derived: false,
        valid: false,
        result: 'The second premise does not hold, so the rule IF cannot derive the triple. The triple is not valid.',
        given: [['Precondition P', '$true$'], ['Condition B', '$x > 0$'], ['Then branch c1', '`y := x`'], ['Else branch c2', '`y := 0`'],
          ['Postcondition Q', '$y > 0$']],
        rule: {
          premises: [
            { f: '{«true : P» && «x > 0 : B»} y := x {«y > 0 : Q»}', part: 'Then branch' },
            { f: '{«true : P» && «!(x > 0) : ¬B»} y := 0 {«y > 0 : Q»}', part: 'Else branch' }
          ],
          conclusion: '{true} if x > 0 then y := x else y := 0 {y > 0}'
        },
        steps: [
          {
            part: 'Then branch',
            head: 'We compute the weakest precondition of `y := x` for $Q$: we substitute $y$ with $x$.',
            calc: ['(y > 0)[y <- x]', '= x > 0 // y replaced by x']
          },
          {
            part: 'Then branch',
            head: 'By the consequence rule, the precondition of the branch must imply this formula.',
            show: ['«true : P» && «x > 0 : B» ==> «x > 0 : wp»'],
            text: 'It holds: the right side is the condition $B$ itself.'
          },
          {
            part: 'Else branch',
            calcNew: true,
            head: 'We compute the weakest precondition of `y := 0` for $Q$: we substitute $y$ with $0$.',
            calc: ['(y > 0)[y <- 0]', '= 0 > 0 // y replaced by 0']
          },
          {
            part: 'Else branch',
            head: 'The comparison $0 > 0$ is false.',
            calc: ['= false // 0 > 0 is false']
          },
          {
            part: 'Else branch',
            head: 'By the consequence rule, the precondition of the branch must imply this formula.',
            show: ['«true : P» && «!(x > 0) : ¬B» ==> «false : wp»'],
            text: 'It is false in the state $x = 0$, which satisfies the left side. From this state the else branch sets $y$ to 0, so $Q$ is false at the end.'
          }
        ]
      }
    ],

    WHILE: [
      {
        title: 'A good invariant',
        goal: '{x >= 0} while x > 0 do x := x - 1 {x >= 0 && !(x > 0)}',
        derived: true,
        valid: true,
        result: 'The rule WHILE derives this triple with the invariant $x >= 0$.',
        given: [['Invariant I', '$x >= 0$'], ['Condition B', '$x > 0$'], ['Body c', '`x := x - 1`']],
        rule: {
          premises: [{ f: '{«x >= 0 : I» && «x > 0 : B»} x := x - 1 {«x >= 0 : I»}', part: 'Preservation' }],
          conclusion: '{x >= 0} while x > 0 do x := x - 1 {x >= 0 && !(x > 0)}'
        },
        steps: [
          {
            part: 'Preservation',
            head: 'The only premise is preservation: from a state that satisfies $I$ and $B$, one execution of the body must give a state that satisfies $I$.',
            show: ['{«x >= 0 : I» && «x > 0 : B»} x := x - 1 {«x >= 0 : I»}']
          },
          {
            part: 'Preservation',
            head: 'We compute the weakest precondition of the body for $I$: we substitute $x$ with $x - 1$.',
            calc: ['(x >= 0)[x <- x - 1]', '= x - 1 >= 0 // x replaced by x - 1']
          },
          {
            part: 'Preservation',
            head: 'We add 1 to both sides.',
            calc: ['= x >= 1 // add 1 to both sides']
          },
          {
            part: 'Preservation',
            head: 'By the consequence rule, $I$ and $B$ together must imply this formula.',
            show: ['«x >= 0 : I» && «x > 0 : B» ==> «x >= 1 : wp»'],
            text: 'It holds: for integers, $x > 0$ is the same as $x >= 1$.'
          },
          {
            part: 'Conclusion',
            head: 'The premise holds, so the rule gives its conclusion, which is the triple.',
            text: 'The postcondition $x >= 0 && !(x > 0)$ says that the loop ends with $x = 0$, if it ends.'
          }
        ]
      },
      {
        title: 'A bad invariant',
        goal: '{x > 0} while x > 0 do x := x - 1 {x > 0 && !(x > 0)}',
        derived: false,
        valid: false,
        result: 'Preservation does not hold, so the rule WHILE cannot be applied with the candidate $x > 0$.',
        given: [['Candidate invariant I', '$x > 0$'], ['Condition B', '$x > 0$'], ['Body c', '`x := x - 1`']],
        rule: {
          premises: [{ f: '{«x > 0 : I» && «x > 0 : B»} x := x - 1 {«x > 0 : I»}', part: 'Preservation' }],
          conclusion: '{x > 0} while x > 0 do x := x - 1 {x > 0 && !(x > 0)}'
        },
        steps: [
          {
            part: 'Preservation',
            head: 'The only premise is preservation: from a state that satisfies $I$ and $B$, one execution of the body must give a state that satisfies $I$.',
            show: ['{«x > 0 : I» && «x > 0 : B»} x := x - 1 {«x > 0 : I»}']
          },
          {
            part: 'Preservation',
            head: 'We compute the weakest precondition of the body for $I$: we substitute $x$ with $x - 1$.',
            calc: ['(x > 0)[x <- x - 1]', '= x - 1 > 0 // x replaced by x - 1']
          },
          {
            part: 'Preservation',
            head: 'We add 1 to both sides.',
            calc: ['= x > 1 // add 1 to both sides']
          },
          {
            part: 'Preservation',
            head: 'By the consequence rule, $I$ and $B$ together must imply this formula.',
            show: ['«x > 0 : I» && «x > 0 : B» ==> «x > 1 : wp»'],
            text: 'It is false in the state $x = 1$: the body gives $x = 0$, which does not satisfy $I$. The last iteration always leaves the candidate.'
          }
        ]
      }
    ],

    'WHILE-CONSEQUENCE': [
      {
        title: 'Counting to 10',
        goal: '{x = 0} while x < 10 do x := x + 1 {x = 10}',
        derived: true,
        valid: true,
        result: 'The three premises hold, so the rule derives the triple with the invariant $0 <= x <= 10$.',
        given: [['Precondition P', '$x = 0$'], ['Invariant I', '$0 <= x <= 10$'], ['Condition B', '$x < 10$'], ['Body c', '`x := x + 1`'],
          ['Postcondition Q', '$x = 10$']],
        rule: {
          premises: [
            { f: '«x = 0 : P» ==> «0 <= x <= 10 : I»', part: 'Establishment' },
            { f: '{«0 <= x <= 10 : I» && «x < 10 : B»} x := x + 1 {«0 <= x <= 10 : I»}', part: 'Preservation' },
            { f: '«0 <= x <= 10 : I» && «!(x < 10) : ¬B» ==> «x = 10 : Q»', part: 'Exit' }
          ],
          conclusion: '{x = 0} while x < 10 do x := x + 1 {x = 10}'
        },
        steps: [
          {
            part: 'Establishment',
            head: 'The invariant must hold when the loop starts, so the precondition $P$ must imply $I$.',
            show: ['«x = 0 : P» ==> «0 <= x <= 10 : I»']
          },
          {
            part: 'Establishment',
            head: 'The precondition $P$ says $x = 0$, so we replace $x$ by 0 in $I$.',
            assume: 'x = 0',
            calc: ['0 <= x <= 10', '= 0 <= 0 <= 10 // x = 0, by P']
          },
          {
            part: 'Establishment',
            head: 'Both comparisons are true.',
            assume: 'x = 0',
            calc: ['= true // 0 <= 0 and 0 <= 10'],
            text: 'So $P$ implies $I$, and establishment holds.'
          },
          {
            part: 'Preservation',
            calcNew: true,
            head: 'From a state that satisfies $I$ and $B$, one execution of the body must give a state that satisfies $I$.',
            show: ['{«0 <= x <= 10 : I» && «x < 10 : B»} x := x + 1 {«0 <= x <= 10 : I»}']
          },
          {
            part: 'Preservation',
            head: 'We compute the weakest precondition of the body for $I$: we substitute $x$ with $x + 1$.',
            calc: ['(0 <= x <= 10)[x <- x + 1]', '= 0 <= x + 1 <= 10 // x replaced by x + 1']
          },
          {
            part: 'Preservation',
            head: 'By the consequence rule, $I$ and $B$ together must imply this formula.',
            show: ['«0 <= x <= 10 : I» && «x < 10 : B» ==> «0 <= x + 1 <= 10 : wp»']
          },
          {
            part: 'Preservation',
            head: 'We prove the two bounds of the right side separately.',
            show: ['«0 <= x <= 10 : I» && «x < 10 : B» ==> «0 <= x + 1 <= 10 : wp»'],
            text: '- Lower bound: from $0 <= x$, in $I$, we get $0 <= x + 1$.\n- Upper bound: from $x < 10$, which is $B$, we get $x + 1 <= 10$, since $x$ is an integer.\n\nSo preservation holds.'
          },
          {
            part: 'Exit',
            calcNew: true,
            head: 'When the loop stops, $I$ holds and $B$ is false. Together they must imply $Q$.',
            show: ['«0 <= x <= 10 : I» && «!(x < 10) : ¬B» ==> «x = 10 : Q»']
          },
          {
            part: 'Exit',
            head: 'We simplify the left side.',
            calc: ['0 <= x <= 10 && !(x < 10)', '= 0 <= x <= 10 && x >= 10 // !(x < 10) is x >= 10']
          },
          {
            part: 'Exit',
            head: 'The bounds $x <= 10$ and $x >= 10$ together give $x = 10$.',
            calc: ['= x = 10 // x <= 10 and x >= 10'],
            text: 'The left side is $Q$ itself, so exit holds.'
          }
        ]
      },
      {
        title: 'Missing bound',
        goal: '{x = 0} while x < 10 do x := x + 1 {x = 10}',
        derived: false,
        valid: true,
        result: 'Exit does not hold, so the rule cannot derive the triple with the invariant $0 <= x$. The triple is valid: the invariant $0 <= x <= 10$ of the first example works.',
        given: [['Precondition P', '$x = 0$'], ['Candidate invariant I', '$0 <= x$'], ['Condition B', '$x < 10$'], ['Body c', '`x := x + 1`'],
          ['Postcondition Q', '$x = 10$']],
        rule: {
          premises: [
            { f: '«x = 0 : P» ==> «0 <= x : I»', part: 'Establishment' },
            { f: '{«0 <= x : I» && «x < 10 : B»} x := x + 1 {«0 <= x : I»}', part: 'Preservation' },
            { f: '«0 <= x : I» && «!(x < 10) : ¬B» ==> «x = 10 : Q»', part: 'Exit' }
          ],
          conclusion: '{x = 0} while x < 10 do x := x + 1 {x = 10}'
        },
        steps: [
          {
            part: 'Establishment',
            head: 'The precondition $P$ must imply $I$. $P$ says $x = 0$, so we replace $x$ by 0 in $I$.',
            assume: 'x = 0',
            calc: ['0 <= x', '= 0 <= 0 // x = 0, by P', '= true // 0 <= 0'],
            text: 'Establishment holds.'
          },
          {
            part: 'Preservation',
            calcNew: true,
            head: 'From a state that satisfies $I$ and $B$, one execution of the body must give a state that satisfies $I$.',
            show: ['{«0 <= x : I» && «x < 10 : B»} x := x + 1 {«0 <= x : I»}']
          },
          {
            part: 'Preservation',
            head: 'We compute the weakest precondition of the body for $I$: we substitute $x$ with $x + 1$.',
            calc: ['(0 <= x)[x <- x + 1]', '= 0 <= x + 1 // x replaced by x + 1']
          },
          {
            part: 'Preservation',
            head: 'By the consequence rule, $I$ and $B$ together must imply this formula.',
            show: ['«0 <= x : I» && «x < 10 : B» ==> «0 <= x + 1 : wp»'],
            text: 'It holds: from $0 <= x$ we get $0 <= x + 1$. So preservation holds.'
          },
          {
            part: 'Exit',
            calcNew: true,
            head: 'When the loop stops, $I$ holds and $B$ is false. Together they must imply $Q$.',
            show: ['«0 <= x : I» && «!(x < 10) : ¬B» ==> «x = 10 : Q»']
          },
          {
            part: 'Exit',
            head: 'We simplify the left side.',
            calc: ['0 <= x && !(x < 10)', '= 0 <= x && x >= 10 // !(x < 10) is x >= 10', '= x >= 10 // x >= 10 gives 0 <= x']
          },
          {
            part: 'Exit',
            head: 'The left side, $x >= 10$, does not imply $Q$.',
            text: 'The state $x = 11$ satisfies $x >= 10$ and not $x = 10$. The candidate is an invariant, but it is too weak: the bound $x <= 10$ is missing.'
          }
        ]
      }
    ],

    'WHILE-TOTAL': [
      {
        title: 'A decreasing variant',
        goal: '{i <= 10} while i < 10 do i := i + 1 {i <= 10 && !(i < 10)}',
        derived: true,
        valid: true,
        result: 'Both premises hold, so the loop terminates, with the variant $10 - i$.',
        given: [['Invariant I', '$i <= 10$'], ['Condition B', '$i < 10$'], ['Body c', '`i := i + 1`'], ['Variant E', '$10 - i$'],
          ['n', 'a logical variable for the value of $E$ when an iteration starts']],
        rule: {
          premises: [
            { f: '{«i <= 10 : I» && «i < 10 : B» && «10 - i = n : E = n»} i := i + 1 {«i <= 10 : I» && «10 - i < n : E < n»}', part: 'Body' },
            { f: '«i <= 10 : I» && «i < 10 : B» ==> «10 - i >= 0 : E ≥ 0»', part: 'Variant not negative' }
          ],
          conclusion: '{i <= 10} while i < 10 do i := i + 1 {i <= 10 && !(i < 10)}'
        },
        steps: [
          {
            part: 'Variant not negative',
            head: 'When an iteration starts, the variant must not be negative.',
            show: ['«i <= 10 : I» && «i < 10 : B» ==> «10 - i >= 0 : E ≥ 0»']
          },
          {
            part: 'Variant not negative',
            head: 'We simplify the right side.',
            calc: ['10 - i >= 0', '= i <= 10 // add i to both sides'],
            text: 'The right side is $I$ itself, so the implication holds.'
          },
          {
            part: 'Body',
            calcNew: true,
            head: 'One iteration must keep $I$ and make the variant smaller than its value $n$ at the start of the iteration.',
            show: ['{«i <= 10 : I» && «i < 10 : B» && «10 - i = n : E = n»} i := i + 1 {«i <= 10 : I» && «10 - i < n : E < n»}']
          },
          {
            part: 'Body',
            head: 'We compute the weakest precondition of the body for the postcondition: we substitute $i$ with $i + 1$.',
            calc: ['(i <= 10 && 10 - i < n)[i <- i + 1]', '= i + 1 <= 10 && 10 - (i + 1) < n // i replaced by i + 1']
          },
          {
            part: 'Body',
            head: 'We simplify the two conjuncts.',
            calc: ['= i < 10 && 10 - (i + 1) < n // i + 1 <= 10 is i < 10, for integers', '= i < 10 && 9 - i < n // 10 - (i + 1) = 9 - i']
          },
          {
            part: 'Body',
            head: 'By the consequence rule, the precondition of the triple must imply this formula.',
            show: ['«i <= 10 : I» && «i < 10 : B» && «10 - i = n : E = n» ==> «i < 10 && 9 - i < n : wp»'],
            text: 'The conjunct $i < 10$ is $B$. From $10 - i = n$ we get $9 - i = n - 1$, which is smaller than $n$. So the premise holds.'
          }
        ]
      },
      {
        title: 'A loop that never stops',
        goal: '{x >= 0} while x >= 0 do x := x + 1 {x >= 0 && !(x >= 0)}',
        derived: false,
        valid: null,
        result: 'No variant works: this loop does not terminate.',
        given: [['Invariant I', '$x >= 0$'], ['Condition B', '$x >= 0$'], ['Body c', '`x := x + 1`'], ['Candidate variant E', '{{E}}'],
          ['n', 'a logical variable for the value of $E$ when an iteration starts']],
        rule: {
          premises: [
            { f: '{«x >= 0 : I» && «x >= 0 : B» && «{{E}} = n : E = n»} x := x + 1 {«x >= 0 : I» && «{{E}} < n : E < n»}', part: 'Body' },
            { f: '«x >= 0 : I» && «x >= 0 : B» ==> «{{E}} >= 0 : E ≥ 0»', part: 'Variant not negative' }
          ],
          conclusion: '{x >= 0} while x >= 0 do x := x + 1 {x >= 0 && !(x >= 0)}'
        },
        steps: [
          {
            part: 'Body',
            set: { E: 'x' },
            head: 'First try: $E = x$. We compute the weakest precondition of the body for the postcondition: we substitute $x$ with $x + 1$.',
            calc: ['(x >= 0 && x < n)[x <- x + 1]', '= x + 1 >= 0 && x + 1 < n // x replaced by x + 1']
          },
          {
            part: 'Body',
            head: 'The premise needs $x = n ==> x + 1 < n$, which is false: $x + 1 = n + 1$ is not smaller than $n$.',
            text: 'The body increases $x$, so $E = x$ does not decrease.'
          },
          {
            part: 'Variant not negative',
            calcNew: true,
            set: { E: '-x' },
            head: 'Second try: $E = -x$. It decreases in every iteration, but it must also not be negative when an iteration starts.',
            show: ['«x >= 0 : I» && «x >= 0 : B» ==> «-x >= 0 : E ≥ 0»']
          },
          {
            part: 'Variant not negative',
            head: 'The implication is false in the state $x = 1$, where $-x = -1$.',
            text: 'No variant can work, because the loop never stops: $x$ only grows, so the condition $x >= 0$ stays true.'
          }
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
        given: [['Assigned variable', '$x$'], ['Assignment expression', '$a[i]$'], ['Postcondition Q', '$x > 0$'],
          ['Precondition P', '$a[i] > 0 && 0 <= i < sizeof(a)$']],
        steps: [
          {
            head: 'The precondition is obtained by substituting the assigned variable ($x$) with the assignment expression ($a[i]$) in $Q$.',
            calc: ['(x > 0)[x <- a[i]]', '= a[i] > 0 // x replaced by a[i]']
          },
          {
            calcNew: true,
            head: 'The expression reads the array at position $i$, so the rule ARRAY-READ adds $def(a[i])$: position $i$ must exist.',
            calc: ['def(a[i])', '= 0 <= i < sizeof(a) // the positions of a are 0, ..., sizeof(a) - 1']
          },
          {
            head: 'The precondition given by the rule is the conjunction of the two parts.',
            show: ['«a[i] > 0 : substitution» && «0 <= i < sizeof(a) : def(a[i])»'],
            text: 'This is the precondition $P$, so the rule derives the triple.'
          }
        ]
      },
      {
        title: 'Without the bounds',
        goal: '{a[i] > 0} x := a[i] {x > 0}',
        derived: false,
        valid: null,
        result: 'The rule ARRAY-READ cannot derive this triple: the read may be outside the array.',
        given: [['Assigned variable', '$x$'], ['Assignment expression', '$a[i]$'], ['Postcondition Q', '$x > 0$'], ['Precondition P', '$a[i] > 0$']],
        steps: [
          {
            head: 'The precondition is obtained by substituting the assigned variable ($x$) with the assignment expression ($a[i]$) in $Q$.',
            calc: ['(x > 0)[x <- a[i]]', '= a[i] > 0 // x replaced by a[i]']
          },
          {
            calcNew: true,
            head: 'The expression reads the array at position $i$, so the rule ARRAY-READ adds $def(a[i])$: position $i$ must exist.',
            calc: ['def(a[i])', '= 0 <= i < sizeof(a) // the positions of a are 0, ..., sizeof(a) - 1']
          },
          {
            head: 'By the consequence rule, the precondition $P$ must imply the precondition given by the rule.',
            show: ['«a[i] > 0 : P» ==> «a[i] > 0 && 0 <= i < sizeof(a) : wp»'],
            text: 'Nothing in $P$ says that position $i$ exists. Take the array $a$ with the values 4, 0, 9 and $i = 7$: position 7 does not exist, so the read $a[7]$ has no value.'
          }
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
        given: [['Array', '$a$'], ['Position written', '$i$'], ['Value written', '$1$'], ['Postcondition Q', '$a[j] = 0$'],
          ['Precondition P', '$j != i && a[j] = 0 && 0 <= i < sizeof(a)$']],
        steps: [
          {
            head: 'The rule replaces the array $a$ in $Q$ by the updated array $a[i |-> 1]$, which is $a$ with the value 1 at position $i$.',
            calc: ['(a[j] = 0)[a <- a[i |-> 1]]', '= a[i |-> 1][j] = 0 // a replaced by a[i |-> 1]']
          },
          {
            head: 'We do not know whether $j$ is equal to $i$, so we use the two cases of a read in an updated array: at position $i$ the value is 1, at any other position $j$ it is $a[j]$.',
            calc: ['= (j = i && 1 = 0) || (j != i && a[j] = 0) // read of a[i |-> 1] at position j']
          },
          {
            head: 'The first case is false, since $1 = 0$ is false.',
            calc: ['= j != i && a[j] = 0 // false || A is A']
          },
          {
            head: 'The write is at position $i$, so the rule also adds $def(a[i])$: position $i$ must exist.',
            show: ['«j != i && a[j] = 0 : substitution» && «0 <= i < sizeof(a) : def(a[i])»'],
            text: 'This is the precondition $P$, so the rule derives the triple.'
          }
        ]
      },
      {
        title: 'Forgetting aliasing',
        goal: '{a[j] = 0 && 0 <= i < sizeof(a)} a[i] := 1 {a[j] = 0}',
        derived: false,
        valid: false,
        result: 'The rule ARRAY-ASSIGN does not derive this triple, and the triple is not valid.',
        given: [['Array', '$a$'], ['Position written', '$i$'], ['Value written', '$1$'], ['Postcondition Q', '$a[j] = 0$'],
          ['Precondition P', '$a[j] = 0 && 0 <= i < sizeof(a)$']],
        steps: [
          {
            head: 'The rule replaces the array $a$ in $Q$ by the updated array $a[i |-> 1]$, which is $a$ with the value 1 at position $i$.',
            calc: ['(a[j] = 0)[a <- a[i |-> 1]]', '= a[i |-> 1][j] = 0 // a replaced by a[i |-> 1]']
          },
          {
            head: 'We do not know whether $j$ is equal to $i$, so we use the two cases of a read in an updated array: at position $i$ the value is 1, at any other position $j$ it is $a[j]$.',
            calc: ['= (j = i && 1 = 0) || (j != i && a[j] = 0) // read of a[i |-> 1] at position j']
          },
          {
            head: 'The first case is false, since $1 = 0$ is false.',
            calc: ['= j != i && a[j] = 0 // false || A is A']
          },
          {
            head: 'The write is at position $i$, so the rule also adds $def(a[i])$: position $i$ must exist.',
            show: ['«j != i && a[j] = 0 : substitution» && «0 <= i < sizeof(a) : def(a[i])»']
          },
          {
            head: 'By the consequence rule, the precondition $P$ must imply the precondition given by the rule.',
            show: ['«a[j] = 0 && 0 <= i < sizeof(a) : P» ==> «j != i && a[j] = 0 && 0 <= i < sizeof(a) : wp»'],
            text: 'It is false for the array $a$ with the values 4, 0, 9 and $i = j = 1$: $P$ holds, but $j != i$ does not. Here $a[i]$ and $a[j]$ are the same cell, so the write sets $a[j]$ to 1, and $Q$ is false at the end.'
          }
        ]
      }
    ]
  };
})(typeof window !== 'undefined' ? window : globalThis);
