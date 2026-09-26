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
make cpp-test # build and test the independent experimental C++ solver
```

`make clean` removes generated build products. The checked-in
[`derivative_dfa.txt`](derivative_dfa.txt) is an example output, not a build
prerequisite.

## Experimental C++ solver

The independent C++17 implementation under [`cpp/`](cpp/) decides
nonemptiness for one REwPLA projected language or for the intersection of
several such languages. Its core is a partial-derivative NFA, an on-the-fly
product search, and shortest-witness reconstruction. It does not link against
or replace the extracted OCaml implementation.

```sh
make cpp-test
./cpp/build/rewpla-solver --alphabet ab 'LA(a)a'
./cpp/build/rewpla-solver --alphabet ab '(a+b)*a' 'b*a'
make cpp-differential  # compare results with the extracted OCaml DFA
make cpp-alignment     # larger fixed-seed Rocq/OCaml alignment suite
make cpp-distance-bench
make cpp-suite-smoke   # validate the paper-oriented benchmark matrix
make cpp-regex-differential
make cpp-redos-bench-smoke # bounded defensive ReDoS case study
make cpp-evaluation-smoke  # logs + CSV + manifest + Markdown summary
make cpp-evaluation        # full repeated publication-oriented profile
```

The C++ solver uses the paper's projected pair-language semantics: a positive
lookahead contributes its least required continuation to the projected word.
For example, `LA(a)` has witness `a`, while `LA(a)b` is empty when `a` and `b`
are distinct. See [`cpp/ALGORITHM.md`](cpp/ALGORITHM.md) for the direct mapping
to the paper equations and Rocq definitions. Resource bounds produce an
explicit `RESOURCE_LIMIT` result and are never reported as `UNSAT`.
The optional real-regex frontend translates a fail-closed positive-lookahead
fragment into the same projected semantics. A separate bounded ReDoS case
study generates worst-case branch-overlap witnesses and probes a standard
engine in timeout-isolated subprocesses; it is a research measurement tool,
not a scanner or exploit facility.
The paper-oriented benchmark matrix, native `distance_n` family, ablations,
metrics, and measurement protocol are specified in
[`cpp/EXPERIMENTS.md`](cpp/EXPERIMENTS.md).
The benchmark's projected-language characterization and even/odd
satisfiability criterion are proved in
[`theories/DistanceBenchmark.v`](theories/DistanceBenchmark.v).

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

### Tight lower-bound family

The CLI recognizes the formally verified tight-family shape

```text
U* a e* (b + c LA((U^k)* x))* d U* h,
U = a+b+c+d+e+x,  k >= 2.
```

For this family it uses the extracted phase/obligation automaton instead of
expanding `U^k` into generic positive-congruence normal forms. For example,
the `k=4` instance can be generated with:

```sh
opam exec -- dune exec ccont -- --automaton rewpla --alphabet abcdexh \
  --format text -o ./tight-k4.txt \
  '(a+b+c+d+e+x)*ae*(b+cLA(((a+b+c+d+e+x)(a+b+c+d+e+x)(a+b+c+d+e+x)(a+b+c+d+e+x))*x))*d(a+b+c+d+e+x)*h'
```

The output identifies the method as `verified-tight-phase-obligations`. The
current reachable table has 3,026 states for `k=4`; its transition closure and
the replay of every state witness are checked before the file is written.
Expressions outside this exact family continue to use the generic verified
construction.

## Repository map

- `paper/`: paper sources.
- `theories/`: Rocq development and extraction entry point.
- `extracted/`: generated OCaml interface and core.
- `cli/`: command-line application and unit tests.
- `cpp/`: independent experimental C++ REwPLA nonemptiness solver.
- `tests/`: expected outputs and regression checks.
- `_CoqProject` and `Makefile`: project configuration and reproducible commands.
