#!/usr/bin/env python3
"""Paper-oriented benchmark matrix for the experimental REwPLA solver.

The suite emits tidy CSV (one row per scenario/engine), validates every
completed result against a family invariant, and treats timeout/resource-limit
as censored outcomes rather than UNSAT.
"""

from __future__ import annotations

import argparse
import ctypes
import csv
import json
import os
import platform
import statistics
import subprocess
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


@dataclass(frozen=True)
class Scenario:
    family: str
    case: str
    parameter: str
    alphabet: str
    expressions: tuple[str, ...]
    expected: str
    expected_witness_length: int | None
    evidence: str
    notes: str = ""
    lookahead_depth: int = 0
    constraint_width: int = 0
    star_depth: int = 0


def inclusive_range(text: str) -> range:
    try:
        start_text, end_text = text.split(":", 1)
        start, end = int(start_text), int(end_text)
    except ValueError as error:
        raise argparse.ArgumentTypeError("range must be MIN:MAX") from error
    if start < 0 or end < start:
        raise argparse.ArgumentTypeError("range requires 0 <= MIN <= MAX")
    return range(start, end + 1)


def sigma_power(n: int, sigma: str = "(a+b)") -> str:
    return sigma * n


def distance_expression(n: int) -> str:
    return "(a+b)*aLA(" + sigma_power(n) + "b)"


def ordinary_distance_expression(n: int) -> str:
    return "(a+b)*a" + sigma_power(n) + "b"


def alternating_word(length: int) -> str:
    return "".join("a" if i % 2 == 0 else "b" for i in range(length))


def exact_word_expression(word: str) -> str:
    return word if word else "1"


def distance_scenarios(parameters: Iterable[int]) -> Iterable[Scenario]:
    for n in parameters:
        expected = "sat" if n % 2 == 0 else "unsat"
        witness_length = n + 2 if expected == "sat" else None
        yield Scenario(
            "distance",
            "positive-lookahead",
            str(n),
            "ab",
            (distance_expression(n), "(ab)*"),
            expected,
            witness_length,
            "Rocq:distance_instance_nonempty_iff_even",
            lookahead_depth=1,
            constraint_width=n + 1,
        )
        yield Scenario(
            "ordinary-control",
            "no-lookahead",
            str(n),
            "ab",
            (ordinary_distance_expression(n), "(ab)*"),
            expected,
            witness_length,
            "Rocq:distance_ordinary_instance_nonempty_iff_even",
        )


def selectivity_scenarios(parameters: Iterable[int]) -> Iterable[Scenario]:
    for n in parameters:
        yield Scenario(
            "selectivity",
            "distance-alone",
            str(n),
            "ab",
            (distance_expression(n),),
            "sat",
            n + 2,
            "Rocq:distance_expression_shortest_length",
            "No alternating component; exposes the cost of an unpruned BFS.",
            lookahead_depth=1,
            constraint_width=n + 1,
        )
        if n % 2 == 0:
            witness = alternating_word(n + 2)
            yield Scenario(
                "selectivity",
                "singleton-pruned",
                str(n),
                "ab",
                (distance_expression(n), exact_word_expression(witness)),
                "sat",
                n + 2,
                "Rocq:distance_expression_projected_exact",
                "A singleton component forces one path without using (ab)*.",
                lookahead_depth=1,
                constraint_width=n + 1,
            )


def periodic_expression(periods: tuple[int, ...]) -> str:
    expression = "(a+b)*a"
    for period in periods:
        block = sigma_power(period)
        expression += "LA((" + block + ")*)"
    return expression


def parse_period_sets(text: str) -> list[tuple[int, ...]]:
    result: list[tuple[int, ...]] = []
    for item in text.split(","):
        try:
            periods = tuple(int(value) for value in item.split("+") if value)
        except ValueError as error:
            raise argparse.ArgumentTypeError("invalid --period-sets") from error
        if not periods or any(period <= 0 for period in periods):
            raise argparse.ArgumentTypeError("periods must be positive")
        result.append(periods)
    return result


def periodic_scenarios(period_sets: Iterable[tuple[int, ...]]) -> Iterable[Scenario]:
    for periods in period_sets:
        label = "+".join(str(period) for period in periods)
        yield Scenario(
            "lookahead-topology",
            "periodic-conjunction",
            label,
            "ab",
            (periodic_expression(periods),),
            "sat",
            1,
            "Rocq:PeriodicAutomaton.expression_semantics",
            f"{len(periods)} positive lookahead obligation(s).",
            lookahead_depth=1,
            constraint_width=max(periods),
        )


def nested_lookahead_expression(depth: int) -> str:
    expression = "a"
    for _ in range(depth - 1):
        expression = "aLA(" + expression + ")"
    return "LA(" + expression + ")"


def lookahead_width_expression(width: int) -> str:
    return "LA(" + sigma_power(width) + "a)"


def topology_scenarios(parameters: Iterable[int]) -> Iterable[Scenario]:
    for parameter in parameters:
        if parameter <= 0:
            continue
        yield Scenario(
            "lookahead-topology",
            "nested-chain",
            str(parameter),
            "ab",
            (nested_lookahead_expression(parameter),),
            "sat",
            parameter,
            "Rocq:distance_nested_chain_shortest_length",
            "Each level requires one additional a in the continuation chain.",
            lookahead_depth=parameter,
            constraint_width=parameter,
        )
        yield Scenario(
            "lookahead-topology",
            "constraint-width",
            str(parameter),
            "ab",
            (lookahead_width_expression(parameter),),
            "sat",
            parameter + 1,
            "derived from Rocq:ordinary_lookahead_projected",
            "Single assertion with a fixed-width ordinary constraint.",
            lookahead_depth=1,
            constraint_width=parameter + 1,
        )
        yield Scenario(
            "ordinary-control",
            "fixed-width",
            str(parameter),
            "ab",
            (sigma_power(parameter) + "a",),
            "sat",
            parameter + 1,
            "Rocq:embed_regex_projected",
            "No-lookahead language control for constraint-width.",
            lookahead_depth=0,
            constraint_width=parameter + 1,
        )


def ordinary_star_expression(depth: int) -> str:
    expression = "(a+b)"
    for _ in range(depth):
        expression = "(" + expression + "*)"
    return expression + "a"


def ordinary_scenarios(parameters: Iterable[int]) -> Iterable[Scenario]:
    alphabet_symbols = "abcdefgh"
    for parameter in parameters:
        if parameter <= 0:
            continue
        yield Scenario(
            "ordinary-control",
            "star-depth",
            str(parameter),
            "ab",
            (ordinary_star_expression(parameter),),
            "sat",
            1,
            "derived from Rocq:embed_regex_projected",
            "Nested-star overhead control with a required trailing atom.",
            star_depth=parameter,
        )
        alphabet = alphabet_symbols[: min(parameter, len(alphabet_symbols))]
        sigma = "(" + "+".join(alphabet) + ")"
        yield Scenario(
            "ordinary-control",
            "alphabet-size",
            str(len(alphabet)),
            alphabet,
            (sigma + "*" + alphabet[-1],),
            "sat",
            1,
            "derived from Rocq:embed_regex_projected",
            "Alphabet-width control; parameter is capped at eight ASCII symbols.",
            star_depth=1,
        )


def tight_expression(k: int) -> str:
    sigma = "(a+b+c+d+e+x)"
    phase = sigma_power(k, sigma)
    return (
        sigma
        + "*ae*(b+cLA(("
        + phase
        + ")*x))*d"
        + sigma
        + "*h"
    )


def tight_scenarios(parameters: Iterable[int]) -> Iterable[Scenario]:
    for k in parameters:
        yield Scenario(
            "tight-family",
            "generic-solver",
            str(k),
            "abcdexh",
            (tight_expression(k),),
            "sat",
            3,
            "Rocq:TightLowerBoundFamily+TightAutomaton",
            "The shortest path chooses zero starred factors; eager still builds the full component.",
            lookahead_depth=1,
            constraint_width=k + 1,
        )


def intersection_scenarios(widths: Iterable[int]) -> Iterable[Scenario]:
    for width in widths:
        even_parameters = tuple(2 * i for i in range(width))
        sat_expressions = tuple(distance_expression(n) for n in even_parameters) + (
            "(ab)*",
        )
        yield Scenario(
            "intersection-width",
            "all-even",
            str(width),
            "ab",
            sat_expressions,
            "sat",
            2 * width,
            "derived from Rocq:distance_instance_nonempty_iff_even",
            f"{width} distance components plus the alternating component.",
            lookahead_depth=1,
            constraint_width=2 * (width - 1) + 1,
        )

        odd_parameters = (1,) + even_parameters[: max(0, width - 1)]
        unsat_expressions = tuple(distance_expression(n) for n in odd_parameters) + (
            "(ab)*",
        )
        yield Scenario(
            "intersection-width",
            "contains-odd",
            str(width),
            "ab",
            unsat_expressions,
            "unsat",
            None,
            "derived from Rocq:distance_instance_nonempty_iff_even",
            f"{width} distance components plus the alternating component.",
            lookahead_depth=1,
            constraint_width=max(2 * max(0, width - 2) + 1, 2),
        )


def percentile(values: list[float], fraction: float) -> float:
    ordered = sorted(values)
    if len(ordered) == 1:
        return ordered[0]
    position = fraction * (len(ordered) - 1)
    lower = int(position)
    upper = min(lower + 1, len(ordered) - 1)
    weight = position - lower
    return ordered[lower] * (1.0 - weight) + ordered[upper] * weight


def command_output(command: list[str], cwd: Path) -> str:
    try:
        completed = subprocess.run(
            command,
            cwd=cwd,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            check=True,
        )
        return completed.stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return "unavailable"


def peak_rss_bytes(process: subprocess.Popen[str]) -> int | None:
    """Read per-process peak working set without an optional dependency."""
    if os.name != "nt" or not hasattr(process, "_handle"):
        return None

    from ctypes import wintypes

    class ProcessMemoryCounters(ctypes.Structure):
        _fields_ = [
            ("cb", wintypes.DWORD),
            ("PageFaultCount", wintypes.DWORD),
            ("PeakWorkingSetSize", ctypes.c_size_t),
            ("WorkingSetSize", ctypes.c_size_t),
            ("QuotaPeakPagedPoolUsage", ctypes.c_size_t),
            ("QuotaPagedPoolUsage", ctypes.c_size_t),
            ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t),
            ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
            ("PagefileUsage", ctypes.c_size_t),
            ("PeakPagefileUsage", ctypes.c_size_t),
        ]

    counters = ProcessMemoryCounters()
    counters.cb = ctypes.sizeof(counters)
    get_memory_info = ctypes.windll.psapi.GetProcessMemoryInfo
    get_memory_info.argtypes = [
        wintypes.HANDLE,
        ctypes.POINTER(ProcessMemoryCounters),
        wintypes.DWORD,
    ]
    get_memory_info.restype = wintypes.BOOL
    handle = wintypes.HANDLE(int(process._handle))
    if not get_memory_info(handle, ctypes.byref(counters), counters.cb):
        return None
    return int(counters.PeakWorkingSetSize)


def one_run(
    solver: Path,
    scenario: Scenario,
    engine: str,
    normalization: str,
    max_configurations: int,
    max_dfa_states: int,
    max_ast_nodes: int,
    timeout: float,
) -> tuple[dict[str, Any], float, int | None]:
    command = [
        str(solver),
        "--json",
        "--engine",
        engine,
        "--normalization",
        normalization,
        "--alphabet",
        scenario.alphabet,
        "--max-configurations",
        str(max_configurations),
        "--max-dfa-states",
        str(max_dfa_states),
        "--max-ast-nodes",
        str(max_ast_nodes),
        "--",
        *scenario.expressions,
    ]
    start = time.perf_counter()
    process = subprocess.Popen(
        command,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        process.kill()
        process.communicate()
        peak = peak_rss_bytes(process)
        return (
            {"status": "timeout", "stats": {}, "detail": "process timeout"},
            timeout * 1000.0,
            peak,
        )
    wall_ms = (time.perf_counter() - start) * 1000.0
    peak = peak_rss_bytes(process)
    if process.returncode not in (0, 3):
        raise RuntimeError(
            f"solver failed for {scenario.family}/{scenario.case}/{scenario.parameter} "
            f"({engine}): {stderr.strip()}"
        )
    try:
        result = json.loads(stdout)
    except json.JSONDecodeError as error:
        # Arena limits are raised before a structured solver result exists.
        if process.returncode == 3:
            result = {
                "status": "resource_limit",
                "stats": {},
                "detail": stderr.strip() or "resource limit",
            }
        else:
            raise RuntimeError(f"invalid solver JSON: {stdout!r}") from error
    return result, wall_ms, peak


def validate_result(scenario: Scenario, result: dict[str, Any]) -> None:
    status = result["status"]
    if status in ("resource_limit", "timeout"):
        return
    if status != scenario.expected:
        raise RuntimeError(
            f"{scenario.family}/{scenario.case}/{scenario.parameter}: "
            f"expected {scenario.expected}, got {status}"
        )
    if scenario.expected_witness_length is not None:
        actual = result.get("witness_length")
        if actual != scenario.expected_witness_length:
            raise RuntimeError(
                f"{scenario.family}/{scenario.case}/{scenario.parameter}: "
                f"expected witness length {scenario.expected_witness_length}, got {actual}"
            )


def repeated_run(
    solver: Path,
    scenario: Scenario,
    engine: str,
    args: argparse.Namespace,
) -> tuple[dict[str, Any], list[float], list[float], list[int]]:
    for _ in range(args.warmup):
        warmup, _, _ = one_run(
            solver,
            scenario,
            engine,
            args.normalization,
            args.max_configurations,
            args.max_dfa_states,
            args.max_ast_nodes,
            args.timeout,
        )
        validate_result(scenario, warmup)

    results: list[dict[str, Any]] = []
    wall_times: list[float] = []
    solve_times: list[float] = []
    peak_rss_values: list[int] = []
    for _ in range(args.repeat):
        result, wall_ms, peak = one_run(
            solver,
            scenario,
            engine,
            args.normalization,
            args.max_configurations,
            args.max_dfa_states,
            args.max_ast_nodes,
            args.timeout,
        )
        validate_result(scenario, result)
        results.append(result)
        wall_times.append(wall_ms)
        if "solve_ms" in result:
            solve_times.append(float(result["solve_ms"]))
        if peak is not None:
            peak_rss_values.append(peak)

    statuses = {result["status"] for result in results}
    if len(statuses) != 1:
        raise RuntimeError(
            f"non-deterministic statuses for {scenario.family}/{scenario.case}: {statuses}"
        )
    return results[-1], wall_times, solve_times, peak_rss_values


def result_row(
    scenario: Scenario,
    engine: str,
    normalization: str,
    result: dict[str, Any],
    wall_times: list[float],
    solve_times: list[float],
    peak_rss_values: list[int],
    metadata: dict[str, str],
) -> dict[str, Any]:
    stats = result.get("stats", {})
    components = stats.get("component_dfa_states", [])
    solve_values = solve_times or [float("nan")]
    peak_mib = [value / (1024.0 * 1024.0) for value in peak_rss_values]
    return {
        **metadata,
        "family": scenario.family,
        "case": scenario.case,
        "parameter": scenario.parameter,
        "engine": engine,
        "normalization": normalization,
        "expected": scenario.expected,
        "status": result["status"],
        "witness": result.get("witness", ""),
        "witness_length": result.get("witness_length", ""),
        "witness_replayed": "true" if result["status"] == "sat" else "",
        "solve_ms_median": statistics.median(solve_values),
        "solve_ms_q1": percentile(solve_values, 0.25),
        "solve_ms_q3": percentile(solve_values, 0.75),
        "wall_ms_median": statistics.median(wall_times),
        "wall_ms_q1": percentile(wall_times, 0.25),
        "wall_ms_q3": percentile(wall_times, 0.75),
        "peak_rss_mib_median": statistics.median(peak_mib) if peak_mib else "",
        "peak_rss_mib_q1": percentile(peak_mib, 0.25) if peak_mib else "",
        "peak_rss_mib_q3": percentile(peak_mib, 0.75) if peak_mib else "",
        "alphabet_size": len(scenario.alphabet),
        "alphabet": scenario.alphabet,
        "expression_count": len(scenario.expressions),
        "expressions_json": json.dumps(scenario.expressions, separators=(",", ":")),
        "input_characters": sum(len(expression) for expression in scenario.expressions),
        "lookahead_count": sum(expression.count("LA(") for expression in scenario.expressions),
        "lookahead_depth": scenario.lookahead_depth,
        "constraint_width": scenario.constraint_width,
        "star_depth": scenario.star_depth,
        "component_dfa_states": ";".join(str(value) for value in components),
        "dfa_states_total": stats.get("dfa_states_total", ""),
        "dfa_transitions": stats.get("dfa_transitions", ""),
        "configurations_discovered": stats.get(
            "configurations_discovered",
            stats.get("product_configurations_discovered", ""),
        ),
        "configurations_expanded": stats.get(
            "configurations_expanded",
            stats.get("product_configurations_expanded", ""),
        ),
        "product_symbol_steps": stats.get("product_symbol_steps", ""),
        "partial_states_observed": stats.get("partial_states_observed", ""),
        "partial_derivatives_cached": stats.get("partial_derivatives_cached", ""),
        "ast_nodes": stats.get("ast_nodes", ""),
        "evidence": scenario.evidence,
        "notes": scenario.notes,
        "detail": result.get("detail", ""),
    }


def build_scenarios(args: argparse.Namespace) -> list[Scenario]:
    selected = set(args.families.split(","))
    known = {
        "distance",
        "selectivity",
        "periodic",
        "topology",
        "ordinary",
        "tight",
        "intersection",
    }
    unknown = selected - known
    if unknown:
        raise ValueError(f"unknown families: {','.join(sorted(unknown))}")
    scenarios: list[Scenario] = []
    if "distance" in selected:
        scenarios.extend(distance_scenarios(args.distance_range))
    if "selectivity" in selected:
        scenarios.extend(selectivity_scenarios(args.distance_range))
    if "periodic" in selected:
        scenarios.extend(periodic_scenarios(args.period_sets))
    if "topology" in selected:
        scenarios.extend(topology_scenarios(args.topology_range))
    if "ordinary" in selected:
        scenarios.extend(ordinary_scenarios(args.ordinary_range))
    if "tight" in selected:
        scenarios.extend(tight_scenarios(args.tight_range))
    if "intersection" in selected:
        scenarios.extend(intersection_scenarios(args.intersection_range))
    return scenarios


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("solver", type=Path)
    parser.add_argument(
        "--families",
        default="distance,selectivity,periodic,topology,ordinary,tight,intersection",
    )
    parser.add_argument("--distance-range", type=inclusive_range, default=inclusive_range("0:14"))
    parser.add_argument("--tight-range", type=inclusive_range, default=inclusive_range("2:4"))
    parser.add_argument(
        "--topology-range", type=inclusive_range, default=inclusive_range("1:8")
    )
    parser.add_argument(
        "--ordinary-range", type=inclusive_range, default=inclusive_range("1:8")
    )
    parser.add_argument(
        "--intersection-range", type=inclusive_range, default=inclusive_range("1:5")
    )
    parser.add_argument(
        "--period-sets",
        type=parse_period_sets,
        default=parse_period_sets("2,3,2+3,3+5,4+5,3+4+5"),
    )
    parser.add_argument("--engines", default="lazy,eager")
    parser.add_argument("--normalization", choices=("compact", "dnf"), default="compact")
    parser.add_argument("--warmup", type=int, default=0)
    parser.add_argument("--repeat", type=int, default=1)
    parser.add_argument("--timeout", type=float, default=30.0)
    parser.add_argument("--max-configurations", type=int, default=1_000_000)
    parser.add_argument("--max-dfa-states", type=int, default=1_000_000)
    parser.add_argument("--max-ast-nodes", type=int, default=1_000_000)
    args = parser.parse_args()
    if args.warmup < 0 or args.repeat <= 0 or args.timeout <= 0:
        parser.error("warmup must be nonnegative; repeat and timeout must be positive")
    if args.ordinary_range.stop - 1 > 8:
        parser.error("--ordinary-range currently supports a maximum of 8")
    engines = args.engines.split(",")
    if not engines or any(engine not in ("lazy", "eager") for engine in engines):
        parser.error("--engines must contain lazy and/or eager")
    args.engines = engines
    return args


def main() -> int:
    args = parse_args()
    solver = args.solver.resolve()
    if not solver.is_file():
        raise SystemExit(f"solver not found: {solver}")
    repo = solver.parent.parent.parent
    scenarios = build_scenarios(args)
    timestamp = datetime.now(timezone.utc).isoformat()
    git_revision = command_output(["git", "rev-parse", "HEAD"], repo)
    git_dirty = command_output(["git", "status", "--porcelain"], repo)
    solver_version = command_output([str(solver), "--version"], repo)
    compiler = command_output(["g++", "--version"], repo).splitlines()[0]
    metadata = {
        "suite_version": "3",
        "timestamp_utc": timestamp,
        "git_revision": git_revision,
        "git_dirty": "true" if git_dirty not in ("", "unavailable") else "false",
        "solver_version": solver_version,
        "compiler": compiler,
        "build_flags": os.environ.get(
            "CXXFLAGS",
            "-std=c++17 -O2 -Wall -Wextra -Wpedantic (Makefile default)",
        ),
        "platform": platform.platform(),
        "python": platform.python_version(),
        "warmup_runs": str(args.warmup),
        "measured_runs": str(args.repeat),
        "timeout_seconds": str(args.timeout),
        "max_configurations": str(args.max_configurations),
        "max_dfa_states": str(args.max_dfa_states),
        "max_ast_nodes": str(args.max_ast_nodes),
    }

    rows: list[dict[str, Any]] = []
    for scenario in scenarios:
        completed: dict[str, dict[str, Any]] = {}
        for engine in args.engines:
            result, wall_times, solve_times, peak_rss_values = repeated_run(
                solver, scenario, engine, args
            )
            completed[engine] = result
            rows.append(
                result_row(
                    scenario,
                    engine,
                    args.normalization,
                    result,
                    wall_times,
                    solve_times,
                    peak_rss_values,
                    metadata,
                )
            )
        if "lazy" in completed and "eager" in completed:
            lazy, eager = completed["lazy"], completed["eager"]
            if lazy["status"] not in ("resource_limit", "timeout") and eager[
                "status"
            ] not in ("resource_limit", "timeout"):
                if lazy["status"] != eager["status"] or lazy.get(
                    "witness"
                ) != eager.get("witness"):
                    raise RuntimeError(
                        f"engine disagreement for {scenario.family}/{scenario.case}/"
                        f"{scenario.parameter}"
                    )

    if not rows:
        return 0
    writer = csv.DictWriter(sys.stdout, fieldnames=list(rows[0].keys()), lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
