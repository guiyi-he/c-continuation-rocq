#!/usr/bin/env python3
"""Positive-lookahead ReDoS candidate and engine-growth case study.

The C++ tool provides a language-level branch-overlap certificate and subjects.
Each Python ``re`` measurement runs in a fresh process so catastrophic cases can
be terminated without wedging the benchmark driver.  The timing validates an
engine-specific effect; it is intentionally separate from the REwPLA proof and
solver-correctness claims.
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


@dataclass(frozen=True)
class Case:
    name: str
    category: str
    alphabet: str
    lookahead: str
    left: str
    right: str
    reject: str
    control_body: str
    rationale: str


def load_cases(path: Path) -> tuple[Case, ...]:
    with path.open(encoding="utf-8") as source:
        data = json.load(source)
    required = {field.name for field in Case.__dataclass_fields__.values()}
    cases: list[Case] = []
    names: set[str] = set()
    for index, entry in enumerate(data):
        if set(entry) != required:
            missing = required - set(entry)
            extra = set(entry) - required
            raise ValueError(
                f"corpus entry {index} schema mismatch; missing={sorted(missing)}, "
                f"extra={sorted(extra)}"
            )
        case = Case(**entry)
        if not case.name or case.name in names:
            raise ValueError(f"corpus case names must be nonempty and unique: {case.name!r}")
        names.add(case.name)
        cases.append(case)
    if not cases:
        raise ValueError("corpus must contain at least one case")
    return tuple(cases)


def command_output(command: list[str], cwd: Path) -> str:
    try:
        return subprocess.run(
            command,
            cwd=cwd,
            check=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return "unavailable"


PROBE_PROGRAM = r"""
import json
import re
import sys
import time

compiled = re.compile(sys.argv[1])
subject = sys.argv[2]
start = time.perf_counter_ns()
matched = compiled.fullmatch(subject) is not None
elapsed_ms = (time.perf_counter_ns() - start) / 1_000_000.0
print(json.dumps({"matched": matched, "elapsed_ms": elapsed_ms}))
"""


def percentile(values: list[float], fraction: float) -> float:
    ordered = sorted(values)
    if len(ordered) == 1:
        return ordered[0]
    position = fraction * (len(ordered) - 1)
    lower = int(position)
    upper = min(lower + 1, len(ordered) - 1)
    weight = position - lower
    return ordered[lower] * (1.0 - weight) + ordered[upper] * weight


def generate(
    tool: Path,
    case: Case,
    minimum: int,
    maximum: int,
    step: int,
) -> dict:
    start = time.perf_counter()
    completed = subprocess.run(
        [
            str(tool),
            "--json",
            "--alphabet",
            case.alphabet,
            "--lookahead",
            case.lookahead,
            "--left",
            case.left,
            "--right",
            case.right,
            "--reject",
            case.reject,
            "--min-repetitions",
            str(minimum),
            "--max-repetitions",
            str(maximum),
            "--step",
            str(step),
        ],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode != 0:
        raise RuntimeError(
            f"candidate generator failed for {case.name}: {completed.stderr}"
        )
    wall_ms = (time.perf_counter() - start) * 1000.0
    result = json.loads(completed.stdout)
    if result["status"] != "candidate":
        raise RuntimeError(f"case {case.name} has no certified overlap: {result}")
    result["_generation_wall_ms"] = wall_ms
    return result


def peak_rss_bytes(process: subprocess.Popen[str]) -> int | None:
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


def probe(
    pattern: str, subject: str, timeout: float
) -> tuple[str, float | None, float, int | None]:
    started = time.perf_counter()
    process = subprocess.Popen(
        [sys.executable, "-c", PROBE_PROGRAM, pattern, subject],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        process.kill()
        process.communicate()
        wall_ms = (time.perf_counter() - started) * 1000.0
        return "timeout", None, wall_ms, peak_rss_bytes(process)
    wall_ms = (time.perf_counter() - started) * 1000.0
    peak = peak_rss_bytes(process)
    if process.returncode != 0:
        raise RuntimeError(f"Python re probe failed: {stderr}")
    result = json.loads(stdout)
    if result["matched"]:
        raise AssertionError(
            f"worst-case subject unexpectedly matched pattern={pattern!r}, "
            f"subject={subject!r}"
        )
    return "reject", float(result["elapsed_ms"]), wall_ms, peak


def variants(case: Case, target: str) -> tuple[tuple[str, str], ...]:
    ambiguous_body = f"(?:(?:{case.left})|(?:{case.right}))"
    return (
        ("positive_lookahead", target),
        ("no_lookahead", f"^{ambiguous_body}+$"),
        (
            "linear_control",
            f"^(?=(?:{case.lookahead}))(?:{case.control_body})$",
        ),
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("tool", type=Path)
    parser.add_argument(
        "--corpus",
        type=Path,
        default=Path(__file__).with_name("redos_cases.json"),
    )
    parser.add_argument("--min-repetitions", type=int, default=2)
    parser.add_argument("--max-repetitions", type=int, default=12)
    parser.add_argument("--step", type=int, default=2)
    parser.add_argument("--warmup", type=int, default=0)
    parser.add_argument("--repeat", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=2.0)
    parser.add_argument(
        "--cases",
        default="",
        help="comma-separated case names",
    )
    args = parser.parse_args()
    if min(
        args.min_repetitions,
        args.max_repetitions,
        args.step,
        args.repeat,
    ) <= 0:
        parser.error("repetition bounds, step, and repeat must be positive")
    if args.warmup < 0:
        parser.error("--warmup must be nonnegative")
    if args.max_repetitions < args.min_repetitions:
        parser.error("--max-repetitions must be at least --min-repetitions")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")

    cases = load_cases(args.corpus)
    requested = set(filter(None, args.cases.split(","))) or {
        case.name for case in cases
    }
    known = {case.name for case in cases}
    unknown = requested - known
    if unknown:
        parser.error(f"unknown cases: {','.join(sorted(unknown))}")
    selected = [case for case in cases if case.name in requested]
    tool = args.tool.resolve()
    repo = tool.parent.parent.parent
    metadata = {
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "tool_version": command_output([str(tool), "--version"], repo),
        "git_revision": command_output(["git", "rev-parse", "HEAD"], repo),
        "git_dirty": (
            "true"
            if command_output(["git", "status", "--porcelain"], repo)
            not in {"", "unavailable"}
            else "false"
        ),
        "measurement_repeat": args.repeat,
        "warmup_runs": args.warmup,
    }

    fieldnames = (
        "timestamp_utc",
        "tool_version",
        "git_revision",
        "git_dirty",
        "measurement_repeat",
        "warmup_runs",
        "case",
        "category",
        "rationale",
        "corpus",
        "variant",
        "repetitions",
        "subject_length",
        "pump",
        "pump_length",
        "ambiguity_log2_lower_bound",
        "certificate",
        "guard_accepts",
        "body_rejects",
        "host_rejection_inferred",
        "certified",
        "generation_wall_ms",
        "overlap_solve_ms",
        "certificate_ms",
        "overlap_configurations",
        "overlap_partial_states",
        "projected_target_accepts",
        "host_result",
        "match_ms_median",
        "match_ms_q1",
        "match_ms_q3",
        "probe_wall_ms_median",
        "peak_rss_mib_median",
        "timeout_seconds",
        "measured_runs",
        "pattern",
        "subject",
        "python_version",
        "platform",
        "claim_scope",
    )
    writer = csv.DictWriter(sys.stdout, fieldnames=fieldnames, lineterminator="\n")
    writer.writeheader()

    for case in selected:
        generated = generate(
            tool,
            case,
            args.min_repetitions,
            args.max_repetitions,
            args.step,
        )
        for candidate in generated["candidates"]:
            if not candidate["certified"]:
                raise AssertionError(
                    f"generator emitted uncertified candidate for {case.name}: "
                    f"{candidate}"
                )
            for variant, pattern in variants(case, generated["target_pattern"]):
                measurements: list[float] = []
                wall_measurements: list[float] = []
                peak_measurements: list[float] = []
                status = "reject"
                for _ in range(args.warmup):
                    probe(pattern, candidate["subject"], args.timeout)
                for _ in range(args.repeat):
                    status, elapsed, wall_ms, peak = probe(
                        pattern, candidate["subject"], args.timeout
                    )
                    wall_measurements.append(wall_ms)
                    if peak is not None:
                        peak_measurements.append(peak / (1024.0 * 1024.0))
                    if status == "timeout":
                        measurements.clear()
                        break
                    assert elapsed is not None
                    measurements.append(elapsed)
                writer.writerow(
                    {
                        **metadata,
                        "case": case.name,
                        "category": case.category,
                        "rationale": case.rationale,
                        "corpus": str(args.corpus.resolve()),
                        "variant": variant,
                        "repetitions": candidate["repetitions"],
                        "subject_length": candidate["length"],
                        "pump": generated["pump"],
                        "pump_length": generated["pump_length"],
                        "ambiguity_log2_lower_bound": candidate[
                            "ambiguity_log2_lower_bound"
                        ],
                        "certificate": "branch_overlap+guard_success+body_failure",
                        "guard_accepts": candidate["guard_accepts"],
                        "body_rejects": candidate["body_rejects"],
                        "host_rejection_inferred": candidate[
                            "host_rejection_inferred"
                        ],
                        "certified": candidate["certified"],
                        "generation_wall_ms": f"{generated['_generation_wall_ms']:.6f}",
                        "overlap_solve_ms": generated["overlap_solve_ms"],
                        "certificate_ms": generated["certificate_ms"],
                        "overlap_configurations": generated["overlap_stats"][
                            "configurations_discovered"
                        ],
                        "overlap_partial_states": generated["overlap_stats"][
                            "partial_states_observed"
                        ],
                        "projected_target_accepts": candidate[
                            "projected_target_accepts"
                        ],
                        "host_result": status,
                        "match_ms_median": (
                            f"{statistics.median(measurements):.6f}"
                            if measurements
                            else ""
                        ),
                        "match_ms_q1": (
                            f"{percentile(measurements, 0.25):.6f}"
                            if measurements
                            else ""
                        ),
                        "match_ms_q3": (
                            f"{percentile(measurements, 0.75):.6f}"
                            if measurements
                            else ""
                        ),
                        "probe_wall_ms_median": f"{statistics.median(wall_measurements):.6f}",
                        "peak_rss_mib_median": (
                            f"{statistics.median(peak_measurements):.6f}"
                            if peak_measurements
                            else ""
                        ),
                        "timeout_seconds": args.timeout,
                        "measured_runs": len(measurements),
                        "pattern": pattern,
                        "subject": candidate["subject"],
                        "python_version": platform.python_version(),
                        "platform": platform.platform(),
                        "claim_scope": (
                            "Python re timing is engine-specific; REwPLA provides "
                            "only the static candidate certificate"
                        ),
                    }
                )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
