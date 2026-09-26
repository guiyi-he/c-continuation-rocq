#!/usr/bin/env python3
"""Black-box checks for the bounded branch-overlap ReDoS application."""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path


def invoke(tool: Path, *arguments: str) -> dict:
    completed = subprocess.run(
        [str(tool), "--json", *arguments],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode != 0:
        raise AssertionError(
            f"ReDoS tool returned {completed.returncode}: {completed.stderr}"
        )
    return json.loads(completed.stdout)


def main() -> int:
    if len(sys.argv) != 2:
        raise SystemExit("usage: redos_smoke.py REWPLA_REDOS")
    tool = Path(sys.argv[1]).resolve()
    result = invoke(
        tool,
        "--alphabet",
        "a!",
        "--lookahead",
        "a+!",
        "--left",
        "a+",
        "--right",
        "aa+",
        "--reject",
        "!",
        "--min-repetitions",
        "2",
        "--max-repetitions",
        "4",
        "--step",
        "2",
    )
    if result["status"] != "candidate" or result["pump"] != "aa":
        raise AssertionError(f"unexpected overlap result: {result}")
    expected = ((2, "aaaa!"), (4, "aaaaaaaa!"))
    if len(result["candidates"]) != len(expected):
        raise AssertionError(f"unexpected candidates: {result}")
    for candidate, (repetitions, subject) in zip(result["candidates"], expected):
        if (
            candidate["repetitions"] != repetitions
            or candidate["subject"] != subject
            or candidate["ambiguity_log2_lower_bound"] != repetitions
            or not candidate["certified"]
            or not candidate["host_rejection_inferred"]
            or not candidate["projected_target_accepts"]
        ):
            raise AssertionError(f"bad candidate certificate: {candidate}")
        if re.fullmatch(result["target_pattern"], subject) is not None:
            raise AssertionError("candidate unexpectedly matches in Python re")

    no_overlap = invoke(
        tool,
        "--alphabet",
        "ab!",
        "--lookahead",
        ".*!",
        "--left",
        "a+",
        "--right",
        "b+",
        "--reject",
        "!",
    )
    if no_overlap["status"] != "no_overlap":
        raise AssertionError(f"disjoint branches were not rejected: {no_overlap}")

    unsupported = subprocess.run(
        [
            str(tool),
            "--alphabet",
            "a!",
            "--lookahead",
            "a+!",
            "--left",
            "(?=a)a",
            "--right",
            "a+",
            "--reject",
            "!",
        ],
        text=True,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
    )
    if unsupported.returncode != 2:
        raise AssertionError("lookahead inside an overlap branch was not rejected")

    print("ReDoS candidate generator smoke tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
