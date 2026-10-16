# Hoare-Logic
Website to teach Hoare Logic

A static website for the Hoare logic part of ICT3112. It explains how Hoare
logic works, presents every rule, and shows solved exercises one step at a
time. The notation follows the slides of ICT3112 and the reference
document HoareLogic.pdf.

## Opening the site

The site is published with GitHub Pages at
https://davidsanan.github.io/Hoare-Logic/

You can also open `index.html` in a browser. No server and no build step
are needed. The empty file `.nojekyll` tells GitHub Pages to serve the files
as they are.

The pages are:

| Page | Content |
|---|---|
| Introduction | Hoare triples, states and assertions, logical variables, proofs with rules, the weakest precondition, frequent mistakes |
| Language | The commands, the specification language, and how to type the notation |
| Rules | SKIP, ASSIGN, CONSEQUENCE, SEQ, IF, WHILE, WHILE-CONSEQUENCE, WHILE-TOTAL, ARRAY-READ, ARRAY-ASSIGN, each with the reason why it is correct, an example, its weakest precondition and its limits |
| Loop invariants | The three checks, the recipe of the lectures, and what to do when a check fails |
| Exercises | The list of exercises and the step viewer |
| wp calculator | Computes the weakest precondition of a loop-free program, statement by statement |
| Write an exercise | An editor with a live preview, the tests, and the reference of the exercise format |

## The step viewer

An exercise is shown in steps. On the left, the annotated program shows the
assertions known so far: a named assertion such as `R1` or `I` stays as
`{ ? }` until a step computes it, and the statement that the current step
works on is highlighted. On the right, the step shows the rules it applies,
the calculations, the verification conditions with their justification,
and the rule instances drawn as fractions. The summary lists all the
assertions of the proof and has a button that tests the solution.

Links point to a step: `index.html#ex-swap-temp~3` opens step 3 of the
exercise `swap-temp`.

## Adding an exercise

Exercises are plain text files in `exercises/`, with the extension `.hl`.
The full reference of the format is on the page "Write an exercise". A
short example:

```text
id: increment-twice
title: Increment twice
topic: Sequential composition
level: 1
source: My exercise list

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

step: Compare with the precondition
rule: CONSEQUENCE
vc: x = 0 ==> wp(x := x + 1, R1)
why:
  The weakest precondition of the first assignment is $x = 0$.
result: The triple is valid.
```

The fields are:

- the exercise: `id`, `title`, `topic`, `level` (1 to 3), `source`, `tags`,
  `task`, `hint`, `pre`, `post`, `program`, `verdict` (`valid` or
  `invalid`), `summary`, `range`;
- the program: the program of the course, where `{NAME}` is a named
  assertion that a step fills in with `set:`, `{P}` and `{Q}` are the
  precondition and the postcondition, any other `{formula}` is shown as it
  is, and `// label` names a statement;
- each step: `step` (its title), `rule`, `focus`, `set`, `text`, `note`,
  `calc`, `vc` with `why`, `status` and `counterexample`, `instance`,
  `assume`, `result`.

To add the exercise to the website:

1. Write it on the page "Write an exercise", check the preview, and press
   "Test". Then press "Save as .hl file".
2. Put the file in `exercises/`. The file names decide the order inside each
   topic, so start the name with a number, for example `47-my-exercise.hl`.
3. Run `python3 tools/build_exercises.py` from this folder. It writes
   `exercises/bundle.js`, which the page loads. A page opened from the disk
   cannot read other files, which is why the exercises are bundled.
4. Optionally run `node tools/check-exercises.js` to read and test every
   exercise from the command line. It exits with code 1 when an exercise has
   an error or a failing test.

## What the tests do

The tests evaluate the claims of a solution on many small states: integers
between `-range` and `range` (4 by default), the constants of the formulas
and their neighbours, and short arrays. They check the triple of the
specification by running the program, every line of every calculation,
every verification condition, every rule instance, and every pattern
`{A} statement {B}` of the annotated program. A failing test gives a state
that breaks the claim. A passing test is evidence, not a proof.

In the tests, `div` and `mod` are the mathematical integer division and
remainder (rounding down), so `x mod 2` is always 0 or 1.

## Files

| File | Content |
|---|---|
| `index.html`, `css/style.css` | The page and its style |
| `js/logic.js` | Parser, printer, substitution, weakest precondition, evaluator and interpreter |
| `js/format.js` | Reader of the `.hl` format |
| `js/checker.js` | The tests on sample states |
| `js/content.js` | The explanatory text and the rules |
| `js/app.js` | The user interface |
| `exercises/*.hl` | The exercises |
| `exercises/bundle.js` | Generated by `tools/build_exercises.py` |
| `tools/check-exercises.js` | Command-line tests (Node.js) |
