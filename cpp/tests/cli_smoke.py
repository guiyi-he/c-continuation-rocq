#!/usr/bin/env python3
"""Black-box checks for lazy/eager CLI selection and structured limits."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


def invoke(solver: Path, *arguments: str, expected_code: int = 0) -> dict:
    completed = subprocess.run(
        [str(solver), "--json", *arguments],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode != expected_code:
        raise AssertionError(
            f"expected exit {expected_code}, got {completed.returncode}: "
            f"{completed.stderr}"
        )
    return json.loads(completed.stdout)


def main() -> int:
    if len(sys.argv) != 2:
        raise SystemExit("usage: cli_smoke.py SOLVER")
    solver = Path(sys.argv[1]).resolve()
    expressions = ("(a+b)*aLA((a+b)(a+b)b)", "(ab)*")
    common = ("--alphabet", "ab", "--", *expressions)

    lazy = invoke(solver, "--engine", "lazy", *common)
    eager = invoke(solver, "--engine", "eager", *common)
    if lazy["status"] != "sat" or lazy["witness"] != "abab":
        raise AssertionError(f"unexpected lazy result: {lazy}")
    if eager["status"] != lazy["status"] or eager["witness"] != lazy["witness"]:
        raise AssertionError(f"engine disagreement: lazy={lazy}, eager={eager}")
    if eager["stats"]["component_dfa_states"] != [12, 3]:
        raise AssertionError(f"unexpected eager DFA sizes: {eager}")
    if lazy["engine"] != "lazy" or eager["engine"] != "eager":
        raise AssertionError("engine metadata is missing")
    if not isinstance(lazy["solve_ms"], (int, float)):
        raise AssertionError("solve_ms is not numeric")

    limited = invoke(
        solver,
        "--engine",
        "eager",
        "--max-dfa-states",
        "10",
        *common,
        expected_code=3,
    )
    if limited["status"] != "resource_limit":
        raise AssertionError(f"limit was not structured: {limited}")

    compact = invoke(solver, "--normalization", "compact", *common)
    dnf = invoke(solver, "--normalization", "dnf", *common)
    if compact["status"] != dnf["status"] or compact["witness"] != dnf["witness"]:
        raise AssertionError("normalization modes disagree")

    frontend = invoke(
        solver,
        "--syntax",
        "regex",
        "--alphabet",
        "abcd",
        "--",
        "a(?=b)",
        "^cabd$",
    )
    if frontend["status"] != "sat" or frontend["witness"] != "cabd":
        raise AssertionError(f"regex search frontend failed: {frontend}")
    if frontend["syntax"] != "regex" or frontend["match"] != "search":
        raise AssertionError("regex frontend metadata/default mode is wrong")

    unsupported = subprocess.run(
        [
            str(solver),
            "--syntax",
            "regex",
            "--alphabet",
            "ab",
            "(?!a)",
        ],
        text=True,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
    )
    if unsupported.returncode != 2:
        raise AssertionError("negative lookahead was not rejected")

    invalid = subprocess.run(
        [str(solver), "--engine", "unknown", "--alphabet", "ab", "a"],
        text=True,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
    )
    if invalid.returncode != 2:
        raise AssertionError("invalid engine was accepted")

    print("C++ solver CLI smoke tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
