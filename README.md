# Automaton for Regular Expression with Positive Lookahead

This repository accompanies the paper *Automaton for Regular Expression with
Positive Lookahead*. It contains the Rocq formalization, an extracted OCaml
core, a command-line tool for constructing automata, regression tests, and the
paper sources.

The paper studies regular expressions with positive lookahead (REwPLA).
Lookahead tests what follows without consuming input. The development gives
these expressions a precise semantics, derives automata from them, and proves
the constructions correct. It also studies c-continuation automata for ordinary
regular expressions and state merging for REwPLA. The CLI exposes these
constructions so that the examples and resulting automata can be reproduced.

## Requirements and build

The project uses Rocq 9.0, OCaml 4.14, Dune 3.10 or later, opam, and GNU Make.
The test target additionally uses Python 3 and standard `diff`, `grep`, and
`tr` utilities. Run commands from the repository root with the appropriate
opam switch active:

```sh
make          # check the Rocq development and regenerate extracted OCaml
make cli      # also build the command-line tool
make test     # run proof, example, and CLI regression checks
```

`make clean` removes generated build products. The checked-in
[`derivative_dfa.txt`](derivative_dfa.txt) is an example output, not a build
prerequisite.

## Command-line interface

```text
opam exec -- dune exec ccont -- \
  [--automaton ce|quotient|both|rewpla] \
  [--alphabet SYMBOLS] \
  [--format text|dot|json] \
  [--no-progress] [--progress-interval SECONDS] \
  [-o FILE] REGEX
```

`REGEX` is one expression, quoted to protect parentheses and `*` from the
shell. Without `-o`, output goes to standard output. The options are:

| Option | Meaning |
| --- | --- |
| `--automaton ce` | Ordinary c-continuation automaton. |
| `--automaton quotient` | Its quotient automaton. |
| `--automaton both` | Both ordinary automata; this is the default. |
| `--automaton rewpla` | Derivative DFA for an expression with positive lookahead. |
| `--alphabet SYMBOLS` | Finite input alphabet, required in `rewpla` mode; for example, `ab` means `{a,b}`. |
| `--format text|dot|json` | Output format; the default is `text`. DOT is available for ordinary automata, while REwPLA supports text and JSON. |
| `--progress` / `--no-progress` | Enable or disable REwPLA progress messages on standard error; progress is enabled by default. |
| `--progress-interval SECONDS` | Minimum interval between progress updates; the default is 5 seconds. |
| `-o FILE` | Write the result to `FILE`. |

The alphabet must include every symbol used by a REwPLA expression and must
not repeat a symbol. The CLI reports an error for a missing symbol or an
unsupported option combination.

### Expression syntax

| Syntax | Meaning |
| --- | --- |
| `a`, `b`, `x`, ... | Single ASCII-letter symbols. |
| `0` / `1` | Empty language / empty word. |
| `r+s` | Union. |
| `rs` or `r.s` | Concatenation; `.` is an operator, not a wildcard. |
| `r*` | Kleene star. |
| `(r)` | Grouping. |
| `LA(r)` | Positive lookahead, in `rewpla` mode. |

Whitespace is ignored. To mean “either `a` or `b`,” write `(a+b)`; there is
no wildcard operator. The CLI does not provide start/end anchors, negative
lookahead, or a general-purpose regex-engine syntax.

### Ordinary regular expressions

Construct both ordinary automata in text form:

```sh
opam exec -- dune exec ccont -- 'x*(xx+y)*'
```

Export one automaton as JSON or Graphviz DOT:

```sh
opam exec -- dune exec ccont -- --automaton quotient --format json \
  -o _build/quotient.json 'x*(xx+y)*'
opam exec -- dune exec ccont -- --automaton ce --format dot \
  -o _build/ce.dot 'x*(xx+y)*'
```

### Positive lookahead

Select `rewpla` and give the finite alphabet:

```sh
opam exec -- dune exec ccont -- --automaton rewpla --alphabet ab \
  --format json 'LA(a)+a'
```

The generic REwPLA construction merges states according to the paper's
proved positive-congruence simplifications. The result is a language-preserving
DFA, but it is not asserted to be a minimal DFA. Text output lists the state
set, alphabet, transition function, initial and final states, a witness word
and continuation for each state, and all transitions. JSON provides the same
automaton in machine-readable form.

REwPLA construction progress is written to standard error, so it remains
visible while `-o` writes a clean text or JSON result. Reports identify the
current phase and, during exploration, show processed, discovered, and pending
state counts. Use `--no-progress` for quiet scripting or change the reporting
frequency with `--progress-interval`.

To reproduce the unanchored two-lookahead example:

```sh
opam exec -- dune exec ccont -- --automaton rewpla --alphabet ab \
  --format text -o ./derivative_dfa.txt \
  'LA((a+b)*a)LA((a+b)*b)(a+b)(a+b)(a+b)(a+b)(a+b)(a+b)(a+b)(a+b)(a+b)*'
```

This expression has eight fixed `(a+b)` factors followed by `(a+b)*`. The
current construction yields **27 states** over `{a,b}`. This is an unanchored
example, so its state count need not match an anchored formulation or another
choice of state representatives. Run `make test` to check the example together
with the rest of the project.

## Repository map

- `paper/`: paper sources.
- `theories/`: Rocq development and extraction entry point.
- `extracted/`: generated OCaml interface and core.
- `cli/`: command-line application and unit tests.
- `tests/`: expected outputs and regression checks.
- `_CoqProject` and `Makefile`: project configuration and reproducible commands.
