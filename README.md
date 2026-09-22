# C-Continuation Automata and REwPLA

This repository accompanies the paper development on c-continuation automata
and regular expressions with positive lookahead (REwPLA). It contains the Rocq
formalization, extracted OCaml code, a command-line interface, regression tests,
and the paper sources.

## Requirements

- Rocq 9.0
- OCaml 4.14
- Dune 3.10 or later
- GNU Make
- opam (used by the CLI build and test commands)

The commands below should be run from the repository root.

## Build and test

Check the Rocq development and regenerate the extracted OCaml core:

```sh
make
```

Build the command-line program:

```sh
make cli
```

Run the complete proof, example, and CLI regression suite:

```sh
make test
```

Remove generated build products:

```sh
make clean
```

## Command-line use

The general form is:

```sh
dune exec ccont -- \
  [--automaton ce|quotient|both|rewpla] \
  [--alphabet SYMBOLS] \
  [--format text|dot|json] \
  [-o FILE] REGEX
```

For ordinary regular expressions, the default constructs both the
c-continuation automaton and its quotient:

```sh
dune exec ccont -- 'x*(xx+y)*'
```

Select one construction and write JSON output to a file:

```sh
dune exec ccont -- \
  --automaton quotient \
  --format json \
  -o _build/quotient.json \
  'x*(xx+y)*'
```

For REwPLA, select `rewpla` and provide the complete finite alphabet:

```sh
dune exec ccont -- \
  --automaton rewpla \
  --alphabet ab \
  --format text \
  'LA(a)+a'
```

The supported syntax is:

- ASCII letters for atoms;
- `0` for the empty language and `1` for epsilon;
- `+` for union and postfix `*` for Kleene star;
- explicit `.` or juxtaposition for concatenation;
- parentheses for grouping;
- `LA(...)` for positive lookahead in REwPLA mode.

Whitespace is ignored. REwPLA text and JSON output are supported; DOT output is
currently available only for the ordinary automata.

## Repository layout

- `theories/` - Rocq definitions, proofs, examples, and extraction entry point.
- `cli/` - OCaml command-line interface and CLI tests.
- `extracted/` - OCaml code generated from the Rocq development.
- `tests/` - regression-test data and auxiliary test scripts.
- `paper/` - paper sources.
- `_CoqProject` - Rocq load path and compilation order.
- `Makefile` - build and test entry points.

For a clean artifact check, run `make test` and confirm that the command exits
successfully.
