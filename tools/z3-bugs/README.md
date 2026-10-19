# A crash of Z3 with define-fun-rec in push/pop scopes

`define-fun-rec-scopes-crash.smt2` has three queries, each between `(push)`
and `(pop)`, each giving the recursive definitions again with
`define-fun-rec`. Evaluated in one context, in this order, the third query
crashes Z3:

- native Z3 4.13.0 and 5.3.1 (Python package `z3-solver`, function
  `Z3_eval_smtlib2_string`): segmentation fault;
- the WebAssembly build of Z3 4.13.0 (npm package `z3-solver`): "memory
  access out of bounds".

Each query alone, or the third query twice, does not crash. The prover of
the site does not use `define-fun-rec` (see docs/verifier-design.md,
section 7.5).
