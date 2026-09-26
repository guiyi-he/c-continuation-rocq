# Experimental C++ REwPLA solver

This is a standalone C++17 nonemptiness solver for the paper's REwPLA
projected language. Its core is a partial-derivative NFA, lazy intersection,
and shortest-witness BFS. See [ALGORITHM.md](ALGORITHM.md) for the exact
paper/Rocq correspondence.

Build with the available GNU C++ compiler:

```sh
make -C cpp
make -C cpp test
```

Or use CMake in an environment where it is installed:

```sh
cmake -S cpp -B cpp/build-cmake
cmake --build cpp/build-cmake
ctest --test-dir cpp/build-cmake
```

Solve one language:

```sh
cpp/build/rewpla-solver --alphabet ab 'LA(a)a'
```

Solve an intersection by supplying several expressions:

```sh
cpp/build/rewpla-solver --alphabet ab '(a+b)*a' 'b*a'
```

Run the eager component-DFA baseline through the same frontend and JSON schema:

```sh
cpp/build/rewpla-solver --engine eager --alphabet ab \
  '(a+b)*aLA((a+b)(a+b)b)' '(ab)*'
```

Use `--json` for machine-readable output. `--max-configurations` and
`--max-ast-nodes` bound an experiment; hitting either bound reports
`RESOURCE_LIMIT`, not `UNSAT`.

Compact concatenation is the default so unions are not expanded to an
exponential DNF before partial-derivative search. The semantically equivalent
`--normalization dnf` mode is available as an experimental ablation.

To compare against the current extracted OCaml construction:

```sh
make -C cpp differential
```

The real-regex frontend has a separate black-box differential gate over the
syntax shared with Python `re`, including positive lookahead and search-mode
anchors:

```sh
make -C cpp regex-differential
```

Use the bounded defensive ReDoS case-study tool to generate branch-overlap
stress witnesses for a positive-lookahead pattern:

```sh
cpp/build/rewpla-redos --alphabet 'a!' --lookahead 'a+!' \
  --left 'a+' --right 'aa+' --reject '!' --json
make -C cpp redos-bench-smoke
```

The result is a static candidate certificate, not an engine-vulnerability
verdict. The accompanying benchmark probes Python `re` in isolated processes
with a timeout and emits CSV. Its default five-case controlled corpus is stored
in `bench/redos_cases.json`; pass `--corpus` to evaluate another descriptor
file without changing the driver. See [EXPERIMENTS.md](EXPERIMENTS.md) for the
semantic boundary between projected REwPLA witnesses and zero-width host-regex
acceptance.

Run the native REwPLA distance-family lazy/eager comparison with:

```sh
make -C cpp distance-bench
cpp/build/rewpla-distance-bench --max-n 18 --repeat 5
```

The full evaluation rationale, benchmark matrix, metrics, and correctness
gates are in [EXPERIMENTS.md](EXPERIMENTS.md).

The unified suite covers ordinary controls, search selectivity, periodic
lookahead conjunctions, the paper's tight family, and growing intersections:

```sh
make -C cpp suite-smoke
python cpp/bench/benchmark_suite.py cpp/build/rewpla-solver \
  --warmup 1 --repeat 5 > rewpla-suite.csv
```

Each CSV row records internal solve time, process wall time, peak resident
memory on Windows, state/transition counters, toolchain and revision metadata,
and the theorem or invariant used to check the expected result.

For an artifact-style run that keeps correctness logs, compact and DNF CSVs,
the ReDoS case-study CSV, hashes/provenance, a generated Markdown summary, and
SVG state-growth/ReDoS-growth figures together:

```sh
make -C cpp evaluation-smoke
make -C cpp evaluation
```

The smoke output is written below `cpp/build/evaluation-smoke`; a full run uses
a fresh UTC-stamped directory unless `--output-dir` is supplied directly to
`bench/run_evaluation.py`.
