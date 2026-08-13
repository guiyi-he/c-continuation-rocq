# Verified c-continuation automata in Rocq

This project implements Definition 7 and the quotient construction from
Champarnaud and Ziadi, *Canonical derivatives, partial derivatives and finite
automaton constructions* (TCS 289, 2002).

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

The development proves linearization/erasure preservation, exact agreement of
the executable transition test with Definition 7, equivalence-relation laws and
right invariance for the quotient, the exact CE state count, and the quotient
state bound. In particular, `build_ce_correct` and `build_quotient_correct`
prove for every regular expression and every word that executable acceptance is
equivalent to the inductive `matches` semantics. Both theorems pass
`Print Assumptions` with a closed global context. The test executable also
evaluates regular expressions independently with Brzozowski derivatives and
compares both generated automata over a bounded regression set.
