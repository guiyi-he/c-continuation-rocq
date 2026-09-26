#!/usr/bin/env python3
"""Differentially compare the C++ solver with the extracted OCaml DFA.

The OCaml side is deliberately treated as a black-box semantic oracle.  For
each expression it builds the existing proved derivative DFA.  This script
then performs an independent on-the-fly DFA product BFS and requires the C++
solver to return the same SAT result and shortest alphabet-ordered witness.
"""

from __future__ import annotations

import argparse
import collections
import json
import pathlib
import random
import subprocess
import sys
import itertools
from typing import Iterable


ROOT = pathlib.Path(__file__).resolve().parents[2]


def ocaml_command() -> list[str]:
    direct = ROOT / "_build" / "default" / "cli" / "ccont.exe"
    if direct.exists():
        return [str(direct)]
    return ["opam", "exec", "--", "dune", "exec", "ccont", "--"]


def ocaml_dfa(expression: str, alphabet: str) -> dict:
    command = [
        *ocaml_command(),
        "--automaton",
        "rewpla",
        "--alphabet",
        alphabet,
        "--format",
        "json",
        "--no-progress",
        expression,
    ]
    completed = subprocess.run(
        command,
        cwd=ROOT,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return json.loads(completed.stdout)


def product_witness(dfas: Iterable[dict], alphabet: str) -> str | None:
    machines = list(dfas)
    transitions = []
    finals = []
    for machine in machines:
        transitions.append(
            {
                (edge["from"], edge["symbol"]): edge["to"]
                for edge in machine["transitions"]
            }
        )
        finals.append(set(machine["final_states"]))

    initial = tuple(machine["initial"] for machine in machines)
    if all(state in final for state, final in zip(initial, finals)):
        return ""
    todo = collections.deque([(initial, "")])
    seen = {initial}
    while todo:
        states, word = todo.popleft()
        for symbol in alphabet:
            target = tuple(
                transition[(state, symbol)]
                for transition, state in zip(transitions, states)
            )
            candidate = word + symbol
            if all(state in final for state, final in zip(target, finals)):
                return candidate
            if target not in seen:
                seen.add(target)
                todo.append((target, candidate))
    return None


def dfa_accepts(machine: dict, word: str) -> bool:
    transitions = {
        (edge["from"], edge["symbol"]): edge["to"]
        for edge in machine["transitions"]
    }
    state = machine["initial"]
    for symbol in word:
        state = transitions[(state, symbol)]
    return state in set(machine["final_states"])


def words_through(alphabet: str, bound: int) -> Iterable[str]:
    for length in range(bound + 1):
        for letters in itertools.product(alphabet, repeat=length):
            yield "".join(letters)


def cpp_result(solver: pathlib.Path, expressions: list[str], alphabet: str) -> dict:
    command = [str(solver), "--json", "--alphabet", alphabet, *expressions]
    completed = subprocess.run(
        command,
        cwd=ROOT,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return json.loads(completed.stdout)


def random_expression(rng: random.Random, depth: int) -> str:
    if depth == 0:
        return rng.choice(["0", "1", "a", "b"])
    constructor = rng.randrange(7)
    if constructor <= 1:
        return random_expression(rng, 0)
    if constructor == 2:
        return f"LA({random_expression(rng, depth - 1)})"
    if constructor == 3:
        return f"({random_expression(rng, depth - 1)})*"
    left = random_expression(rng, depth - 1)
    right = random_expression(rng, depth - 1)
    if constructor in (4, 5):
        return f"({left}+{right})"
    return f"({left}).({right})"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("solver", type=pathlib.Path)
    parser.add_argument("--random-cases", type=int, default=0)
    parser.add_argument("--seed", type=int, default=20260926)
    parser.add_argument("--word-bound", type=int, default=3)
    args = parser.parse_args()
    solver = args.solver.resolve()

    cases = [
        ("ab", ["0"]),
        ("ab", ["1"]),
        ("ab", ["a+b"]),
        ("ab", ["LA(a)"]),
        ("ab", ["LA(a)a"]),
        ("ab", ["LA(a)b"]),
        ("ab", ["aLA(b)"]),
        ("ab", ["LA(ab)a"]),
        ("ab", ["LA(LA(a))"]),
        ("ab", ["LA(a+ab)"]),
        ("ab", ["(a+b)*a", "b*a"]),
        ("ab", ["(a+b)*a", "(a+b)*b"]),
        ("ab", ["LA(ab)a", "ab"]),
        ("abc", ["(a+b+c)*c", "a*b*c"]),
    ]

    rng = random.Random(args.seed)
    random_sources: list[str] = []
    while len(random_sources) < args.random_cases:
        source = random_expression(rng, rng.choice([1, 2, 3]))
        if source not in random_sources:
            random_sources.append(source)
    cases.extend(("ab", [source]) for source in random_sources)
    # A few random products exercise independent nondeterministic subset
    # evolution, not merely the one-component nonemptiness path.
    for index in range(0, len(random_sources) - 1, 2):
        cases.append(("ab", random_sources[index : index + 2]))

    cache: dict[tuple[str, str], dict] = {}
    for alphabet, expressions in cases:
        machines = []
        for expression in expressions:
            key = (alphabet, expression)
            if key not in cache:
                cache[key] = ocaml_dfa(expression, alphabet)
            machines.append(cache[key])
        expected = product_witness(machines, alphabet)
        actual = cpp_result(solver, expressions, alphabet)
        expected_status = "sat" if expected is not None else "unsat"
        if actual["status"] != expected_status:
            raise AssertionError(
                f"{expressions}: expected {expected_status}, got {actual}"
            )
        if expected is not None and actual.get("witness") != expected:
            raise AssertionError(
                f"{expressions}: expected witness {expected!r}, got {actual}"
            )
        print(f"ok alphabet={alphabet} expressions={expressions} witness={expected!r}")

    membership_checks = 0
    for (alphabet, expression), machine in cache.items():
        for word in words_through(alphabet, args.word_bound):
            singleton = word if word else "1"
            actual = cpp_result(solver, [expression, singleton], alphabet)
            expected_accepts = dfa_accepts(machine, word)
            if expected_accepts:
                if actual["status"] != "sat" or actual.get("witness") != word:
                    raise AssertionError(
                        f"membership mismatch: {expression!r} should accept "
                        f"{word!r}, got {actual}"
                    )
            elif actual["status"] != "unsat":
                raise AssertionError(
                    f"membership mismatch: {expression!r} should reject "
                    f"{word!r}, got {actual}"
                )
            membership_checks += 1

    print(
        f"differential tests passed: {len(cases)} nonemptiness cases, "
        f"{membership_checks} bounded membership checks"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
