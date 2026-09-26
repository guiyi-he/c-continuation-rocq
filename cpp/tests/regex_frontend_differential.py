#!/usr/bin/env python3
"""Compare the supported real-regex search frontend with Python ``re``.

This is deliberately a frontend test, not the semantic oracle for the REwPLA
core.  The latter remains the extracted Rocq/OCaml implementation exercised by
``differential.py``.  Here an anchored exact-word regex turns nonemptiness into
membership, so both engines must agree with Python on the common syntax subset.
"""

from __future__ import annotations

import argparse
import itertools
import json
import random
import re
import subprocess
from pathlib import Path


PATTERNS = (
    "a",
    "a|b",
    "a+",
    "a?b",
    "a{1,2}b",
    "[ab]*a",
    "[^a]+",
    ".b",
    "(?:ab|b)+",
    "a(?=b)",
    "(?=ab)a",
    "a(?=b)b?",
    "^a",
    "b$",
    "^a+b$",
    "(?:ab|ba)",
)


def generated_pattern(rng: random.Random, depth: int) -> str:
    atoms = ("a", "b", ".", "[ab]", "[^a]", "(?:a)")
    if depth <= 0:
        return rng.choice(atoms)
    choice = rng.randrange(5)
    if choice == 0:
        return f"(?:{generated_pattern(rng, depth - 1)})"
    if choice == 1:
        return (
            f"(?:{generated_pattern(rng, depth - 1)}|"
            f"{generated_pattern(rng, depth - 1)})"
        )
    if choice == 2:
        return generated_pattern(rng, depth - 1) + generated_pattern(rng, depth - 1)
    quantifier = rng.choice(("*", "+", "?", "{0,2}", "{1,3}"))
    return f"(?:{generated_pattern(rng, depth - 1)}){quantifier}"


def random_patterns(count: int, seed: int) -> list[str]:
    rng = random.Random(seed)
    result: list[str] = []
    seen = set(PATTERNS)
    while len(result) < count:
        pattern = generated_pattern(rng, 3)
        if pattern in seen:
            continue
        re.compile(pattern)
        seen.add(pattern)
        result.append(pattern)
    return result


def words(alphabet: str, bound: int):
    for length in range(bound + 1):
        for symbols in itertools.product(alphabet, repeat=length):
            yield "".join(symbols)


def solver_accepts(solver: Path, engine: str, pattern: str, word: str) -> bool:
    exact_word = f"^{word}$"
    completed = subprocess.run(
        [
            str(solver),
            "--json",
            "--engine",
            engine,
            "--syntax",
            "regex",
            "--match",
            "search",
            "--alphabet",
            "ab",
            "--",
            pattern,
            exact_word,
        ],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode != 0:
        raise AssertionError(
            f"solver failed for engine={engine}, pattern={pattern!r}, "
            f"word={word!r}: {completed.stderr}"
        )
    result = json.loads(completed.stdout)
    if result["status"] not in {"sat", "unsat"}:
        raise AssertionError(f"unexpected solver status: {result}")
    if result["status"] == "sat" and result["witness"] != word:
        raise AssertionError(
            f"anchored membership returned {result['witness']!r}, expected {word!r}"
        )
    return result["status"] == "sat"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("solver", type=Path)
    parser.add_argument("--word-bound", type=int, default=4)
    parser.add_argument("--random-patterns", type=int, default=0)
    parser.add_argument("--seed", type=int, default=20260926)
    args = parser.parse_args()
    if args.word_bound < 0 or args.random_patterns < 0:
        parser.error("bounds must be nonnegative")
    solver = args.solver.resolve()

    patterns = list(PATTERNS)
    patterns.extend(random_patterns(args.random_patterns, args.seed))
    checks = 0
    for pattern in patterns:
        for word in words("ab", args.word_bound):
            expected = re.search(pattern, word) is not None
            lazy = solver_accepts(solver, "lazy", pattern, word)
            eager = solver_accepts(solver, "eager", pattern, word)
            if lazy != expected or eager != expected:
                raise AssertionError(
                    f"frontend disagreement for pattern={pattern!r}, word={word!r}: "
                    f"python={expected}, lazy={lazy}, eager={eager}"
                )
            checks += 2

    print(
        f"regex frontend differential passed: {len(patterns)} patterns, "
        f"{checks} engine-membership checks"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
