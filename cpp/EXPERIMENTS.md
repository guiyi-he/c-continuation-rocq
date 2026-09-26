# Experimental evaluation plan

The evaluation is organized around this project's claims, not as a reproduction
of another solver's benchmark suite. The extracted Rocq/OCaml implementation
is the semantic oracle; the C++ variants share one transition core so that
performance comparisons isolate representation and search strategy.

## Research questions

1. **RQ1 — semantic agreement.** Does the C++ partial-derivative solver agree
   with the proved/extracted implementation on nonemptiness, shortest
   witnesses, and bounded membership?
2. **RQ2 — lazy intersection.** How many states, transitions, time, and memory
   are avoided by searching the product on demand instead of first constructing
   every component subset DFA?
3. **RQ3 — representation.** What is the effect of compact syntax versus eager
   positive-DNF normalization? Both modes use proved equations and therefore
   must have identical answers.
4. **RQ4 — lookahead structure.** How do the number, nesting depth, constraint
   width, and interaction of positive lookaheads affect partial-derivative and
   product sizes?
5. **RQ5 — application.** On real positive-lookahead regexes, can the solver
   produce useful intersection witnesses for ReDoS analysis within practical
   resource limits?

RQ1--RQ5 are executable. They remain separate evidence layers: the extracted
Rocq/OCaml implementation is the oracle for core projected semantics; Python
`re.search` is a black-box frontend oracle only on a declared common fragment;
and Python `re` timing is an engine-specific ReDoS case study, not evidence for
the solver's semantic correctness.

## Solver variants

| Variant | Component construction | Intersection | Purpose |
|---|---|---|---|
| `lazy-pd/compact` | compact partial derivatives | on-the-fly BFS | proposed default |
| `eager-dfa/compact` | complete reachable subset DFA | product BFS afterwards | search-strategy baseline |
| `lazy-pd/dnf` | eager positive DNF, then partial derivatives | on-the-fly BFS | normalization ablation |
| extracted OCaml | proved deterministic construction | independent oracle product | correctness oracle, not a timing baseline |

The lazy and eager C++ variants call the same `PartialDerivativeNfa::move` and
`final` functions. A result difference is therefore a bug, while a scale
difference is attributable to when subset/product states are materialized.

## Native `distance_n` family

Let `S = (a+b)`, and define

```text
distance_n  = S* a LA(S^n b)
alternating = (ab)*
instance_n  = distance_n intersect alternating
```

Here `S^n` means `n` concatenated copies of `S`; the benchmark generator emits
the core syntax directly. By the paper's projected pair-language semantics,

```text
L_pi(distance_n) = { x a y b | x,y in {a,b}*, |y| = n }.
```

Every nonempty word in `L(alternating)` ends in `b`. The symbol `n+1`
positions before that final `b` is `a` exactly when `n` is even. Therefore:

- `instance_n` is SAT iff `n` is even;
- for even `n`, its unique shortest witness is the alternating word of length
  `n+2`;
- for odd `n`, exhaustion of the alternating product proves UNSAT.

This is a REwPLA-native mechanism benchmark: the lookahead supplies the
required continuation, while the second component prunes the product to one
alternating path. With compact syntax the measured lazy product has `n+2`
configurations. The eager subset construction currently reaches `3 * 2^n`
states for the `distance_n` component; that exact implementation invariant is
regression-tested for `0 <= n <= 8`, while every larger run records the count
rather than assuming it.

The language characterization and SAT/UNSAT parity theorem are machine-checked
in `theories/DistanceBenchmark.v`. In particular,
`distance_instance_nonempty_iff_even` is closed under the global context; the
Rocq proof changes neither extraction nor the existing OCaml solver.
The same file proves the no-lookahead control equivalent at the projected
language level, its parity criterion, and the `n+2` shortest-length bound used
to validate unpruned distance runs. It also proves the exact projected language
and shortest-witness length of the nesting-depth chain used in the topology
experiment.

Run a reproducible CSV sweep with:

```sh
make cpp-distance-bench
cpp/build/rewpla-distance-bench --max-n 18 --warmup 1 --repeat 5 > distance-compact.csv
cpp/build/rewpla-distance-bench --normalization dnf --max-n 12 \
  --warmup 1 --repeat 5 \
  > distance-dnf.csv
```

The executable validates the parity theorem, shortest witness length, and
lazy/eager agreement on every row. A state cap produces `resource_limit`,
never `unsat`.

## Unified benchmark suite

`bench/benchmark_suite.py` materializes the non-application rows of the matrix
below and runs both engines through the same `rewpla-solver` CLI:

```sh
make cpp-suite-smoke
python cpp/bench/benchmark_suite.py cpp/build/rewpla-solver \
  --warmup 1 --repeat 5 --timeout 60 > rewpla-suite.csv
```

The suite is self-checking. Every completed row is checked against its family
invariant, lazy/eager answers and witnesses must agree, and resource limits or
timeouts remain explicit censored outcomes. CSV metadata includes the git
revision and dirty flag, solver/compiler/Python versions, platform, internal
solve time, process wall time, and per-process peak working set on Windows.
It also records an `evidence` field naming the Rocq theorem or derived invariant
behind the expected answer.

The current families are:

- `ordinary`: alphabet-width and nested-star controls without lookahead;
- `distance`: proved positive-lookahead family and a no-lookahead language
  control;
- `selectivity`: the same distance component alone and with a singleton
  pruning component;
- `periodic`: the paper's periodic positive-lookahead conjunction shape;
- `topology`: nested continuation chains, fixed-width assertion constraints,
  and matched ordinary controls;
- `tight`: the formally verified tight lower-bound expression through the
  generic C++ solver;
- `intersection`: increasing numbers of simultaneously solved distance
  constraints, with SAT and UNSAT variants.

## Real-regex frontend and ReDoS case study

The `--syntax regex` frontend accepts conventional alternation and implicit
concatenation, wildcard, explicit character classes, `*`, `+`, `?`, bounded
repeats, ordinary/noncapturing groups, outer anchors, escapes, and positive
lookahead. It rejects unsupported group extensions, negative lookahead,
backreferences, lazy/possessive quantifiers, and predefined classes rather
than approximating them. The finite `--alphabet` defines wildcard and negated
class semantics. The experimental implementation is byte-oriented and has no
Unicode or flag modes; `.` ranges over the supplied alphabet, including any
explicitly supplied newline byte.

Two independent gates cover this layer:

```sh
make cpp-regex-differential
make cpp-redos-bench-smoke
```

The first performs 992 lazy/eager membership checks for 16 supported patterns
against Python `re.search`. The corpus includes positive lookahead, anchors,
classes, repeats, and grouping. It is deliberately a validation of the tested
common search fragment, not a claim that projected REwPLA language equals host
regex acceptance in all contexts. In particular, an end-anchored lookahead can
contribute continuation symbols to the paper's projected witness even though a
host assertion consumes no symbols.

`rewpla-redos` implements a bounded, defensive branch-overlap case study. Given
two ordinary branch regexes `L` and `R`, it uses lazy intersection to find the
shortest nonempty pump word in `L intersect R`. For the generated pattern

```text
^(?=GUARD)(?:(?:L)|(?:R))+$
```

repeating that word `n` times supplies at least `2^n` syntactic branch choices.
A literal suffix is added so the positive guard succeeds while the consuming
body fails. The certificate records branch overlap, guard success, body
failure, and the important projected-target result separately. The tool does
not scan applications, send inputs, or claim an engine vulnerability.

The measurement driver runs each standard-engine match in a fresh process with
a hard timeout and compares three variants: the positive-lookahead pattern,
the same ambiguous body without lookahead, and a positive-lookahead linear
control. The versioned `bench/redos_cases.json` corpus covers unbounded nested
quantifiers, character-class prefix overlap, optional suffixes, equivalent
fixed-word branches, and bounded-repeat overlap. Each descriptor records its
structural category and rationale; `--corpus` accepts an alternative corpus.
A reproducible CSV is produced by:

```sh
python cpp/bench/redos_case_study.py cpp/build/rewpla-redos \
  --min-repetitions 2 --max-repetitions 12 --step 2 \
  --warmup 1 --repeat 3 --timeout 1 > redos-case-study.csv
```

The current five-case engineering pilot shows both positive and negative
signals. With one warm-up and five measured runs, the nested-unbounded and
bounded-repeat cases reach the two-second timeout at subject length 25. The
character-class and optional-suffix cases grow from roughly 0.003 ms to roughly
21 ms by repetition 12, while the fixed-word case grows only to about 0.29 ms,
showing that an engine can substantially optimize a statically ambiguous
candidate. Linear positive-lookahead controls remain near a few microseconds.
These are pilot observations on Python 3.12.8/Windows, not publication
measurements; the checked CSV captures runtime, platform, timeout, exact
pattern, subject, corpus descriptor, certificate metrics, process wall time,
and peak resident memory on Windows.

An initial three-run engineering sweep (not a publication measurement) found
the following useful scale boundaries under a one-million-state eager cap:

| Family/case | Lazy search | Eager component construction |
|---|---:|---:|
| periodic periods `3+5` | 1 configuration | 37,632 states |
| periodic periods `4+5` | 1 configuration | resource limit |
| periodic periods `3+4+5` | 1 configuration | resource limit |
| tight family `k=3` | 9 configurations | 2,562 states |
| tight family `k=4` | 9 configurations | resource limit |

These rows complement `distance_n`: they show the same lazy advantage on two
families already central to this paper, while the ordinary and selectivity
controls reveal when the gain comes from product pruning rather than from the
lookahead syntax alone.

## Benchmark matrix

The final paper evaluation should contain all of the following groups.

| Group | Parameters | Main comparison |
|---|---|---|
| ordinary controls | width, star depth, alphabet size; no `LA` | overhead of REwPLA machinery |
| `distance_n` | `n`, SAT/UNSAT parity | linear lazy product vs eager powerset |
| lookahead topology | count, nesting depth, constraint width | compact vs DNF; cache/AST growth |
| periodic families | moduli count and lcm | general C++ solver vs existing specialized verified construction |
| tight family | paper parameter `k` | behavior near the proved double-exponential lower bound |
| intersections | number of components, overlap selectivity | product pruning and witness length |
| application corpus | regex size and stress-witness repetition count | end-to-end frontend/ReDoS utility |

For the tight family, report both the general solver and the existing
`verified-tight-phase-obligations` construction. They answer different
questions: the former evaluates the generic algorithm; the latter shows how
the proved family structure can be exploited.

## Measurements and protocol

For every run record at least:

- status, witness length, and replay success;
- wall time and peak resident memory;
- distinct partial-expression states observed, cached `(state,symbol)` partial
  derivatives, and hash-consed AST nodes;
- lazy product configurations and symbol steps;
- eager DFA states/transitions per component and product configurations;
- compiler/version, optimization flags, machine, state/memory/time limits, and
  the exact git revision.

Use a fresh process for measured runs, fixed input/alphabet order, one warm-up,
and at least five measured repetitions; report median and interquartile range.
The unified suite implements this protocol with `--warmup 1 --repeat 5`.
Random correctness cases use a committed seed, but should be supplemented by
multiple seeds outside the headline performance tables. Timeout and resource
limit are separate outcomes and must not be counted as UNSAT.

For reproducible artifact capture, `make cpp-evaluation-smoke` and
`make cpp-evaluation` run the gates and experiments as one workflow. Each run
keeps `correctness.log`, compact and DNF solver CSVs, the ReDoS CSV,
`manifest.json` (commands, versions, hashes, revision, durations), and a
generated `SUMMARY.md`. The full profile also runs the repository's complete
Rocq/OCaml regression target and validates compact/DNF status and witness
agreement on their common rows.

## Correctness gates

```sh
make -C cpp test
make cpp-differential
make cpp-alignment
```

`cpp-differential` is the small deterministic gate. `cpp-alignment` adds 200
fixed-seed generated expressions and checks both single-language membership
and intersections against independently materialized extracted-OCaml DFAs.
Before publishing a new benchmark family, add (1) an executable family
invariant and (2) either a Rocq theorem or an explicit statement that the
claim is only test-backed. The `distance_n` family has both: the C++ executable
checks every generated row, and `theories/DistanceBenchmark.v` proves the
projected-language characterization and parity result.
