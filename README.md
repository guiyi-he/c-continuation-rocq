# Verified c-continuation automata in Rocq

This project implements Definition 7 and the quotient construction from
Champarnaud and Ziadi, *Canonical derivatives, partial derivatives and finite
automaton constructions* (TCS 289, 2002).

It also mechanizes Section 3.1 of `ICFP_2027_Version.pdf`: constrained-word
pairs, executable prefix quotient/join and partial concatenation, constraint
preservation, definedness, least residuals, pair associativity, and the
idempotent-semiring laws for languages of constrained words.  The Rocq comments
in `theories/StringConstraints.v` map each definition and proof paragraph back
to the corresponding PDF page, source-line range, and equation or proposition.

Requirements: Rocq 9.0, OCaml 4.14, Dune 3.x, and GNU Make.

```sh
make          # check the Rocq development and extract the verified core
make cli      # build the command-line program
make test     # proofs, examples, and CLI smoke tests
```

Usage:

```sh
dune exec ccont -- [--automaton ce|quotient|both] \
  [--format text|dot|json] [-o FILE] 'x*(xx+y)*'
```

Atoms are ASCII letters. `0`, `1`, `+`, postfix `*`, parentheses, explicit
`.` concatenation, and implicit concatenation are supported. Whitespace is
ignored.

The trusted Rocq core is generic over a decidable alphabet. The extracted CLI
specializes symbols to character codes. Parsing, diagnostics, and rendering are
ordinary OCaml and are intentionally outside the verified boundary.

The string-constraint results are constructive and executable: partial
operations return `option`, while language equality is pointwise logical
equivalence.  The principal checked results are
`constraint_concat_preservation`,
`constraint_concat_defined_iff_residual`,
`constraint_concat_least_residual`, `constraint_concat_assoc`, and
`constraint_languages_idempotent_semiring`.

The continuation-automaton development proves linearization/erasure
preservation, exact agreement of
the executable transition test with Definition 7, equivalence-relation laws and
right invariance for the quotient, the exact CE state count, and the quotient
state bound. In particular, `build_ce_correct` and `build_quotient_correct`
prove for every regular expression and every word that executable acceptance is
equivalent to the inductive `matches` semantics. Both theorems pass
`Print Assumptions` with a closed global context. The test executable also
evaluates regular expressions independently with Brzozowski derivatives and
compares both generated automata over a bounded regression set.
