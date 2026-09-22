"""Build and minimise an independent automaton for E_n's projected language."""

import argparse
import hashlib
import importlib.util
import itertools
import json
import math
from pathlib import Path
import random
import time

import dfa_growth_model as model


def run(table, alphabet, initial, word):
    q = initial
    for a in word:
        q = table[q][alphabet.index(a)]
    return q


def verify_against_cli(n, alphabet, table, finals, output_dir):
    path = output_dir / f"cli_n{n}.json"
    if not path.exists():
        return None
    cli = json.loads(path.read_text(encoding="utf-8"))
    edges = {(e["from"], e["symbol"]): e["to"] for e in cli["transitions"]}
    pending = [(cli["initial"], 0)]
    seen = set(pending)
    # Product traversal establishes agreement on every word, not a sample.
    for cq, mq in pending:
        assert (cq in cli["final_states"]) == finals[mq], (n, cq, mq)
        for i, a in enumerate(alphabet):
            pair = (edges[cq, a], table[mq][i])
            if pair not in seen:
                seen.add(pair)
                pending.append(pair)
    return len(seen)


def verify_pair_semantics(n):
    spec = importlib.util.spec_from_file_location("growth_pair_oracle", "tests/periodic_dfa.py")
    oracle = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(oracle)
    import functools
    alphabet, _, _ = model.family(n)
    sigma = functools.reduce(lambda a, b: ("plus", a, b), [("atom", c) for c in alphabet])
    factors = [("star", sigma), ("atom", "a")]
    factors += [("plus", ("atom", "b"),
                 ("concat", ("atom", "c"),
                  ("lookahead", ("concat", ("star", sigma), ("atom", x)))))
                for x in model.MARKERS[:n]]
    factors += [("star", sigma)]
    expr = functools.reduce(lambda a, b: ("concat", a, b), factors)
    checked = 0
    def check(word):
        nonlocal checked
        actual = any(oracle.pair_member(expr, word[:j], word[j:])
                     for j in range(len(word) + 1))
        assert actual == model.direct_accept(n, word), (n, word, actual)
        checked += 1
    for length in range(4):
        for chars in itertools.product(alphabet, repeat=length):
            check("".join(chars))
    rng = random.Random(427 + n)
    for _ in range(200):
        check("".join(rng.choice(alphabet) for _ in range(rng.randrange(4, 11))))
    central = list(itertools.combinations(range(n), n // 2))
    # Exhaustive all central-layer collections for n<=4, systematic/random later.
    masks = range(1 << len(central)) if n <= 4 else [0, 1, (1 << len(central)) - 1] + [rng.randrange(1 << len(central)) for _ in range(30)]
    for mask in masks:
        selected = [A for j, A in enumerate(central) if mask >> j & 1]
        prefix = "".join("a" + "".join("c" if i in A else "b" for i in range(n))
                         for A in selected)
        for B in central:
            word = prefix + "".join(model.MARKERS[i] for i in B)
            assert model.direct_accept(n, word) == (B in selected)
            if n <= 3:
                check(word)
    return checked


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, nargs="+", default=[1, 2, 3, 4, 5])
    parser.add_argument("--output-dir", type=Path, default=Path("experiments/dfa_growth"))
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    path = args.output_dir / "model_measurements.json"
    records = json.loads(path.read_text(encoding="utf-8")) if path.exists() else []
    for n in args.n:
        alphabet, expression, width = model.family(n)
        print(json.dumps(dict(event="model_started", n=n)), flush=True)
        started = time.perf_counter()
        _, states, table, finals = model.build(n)
        build_seconds = time.perf_counter() - started
        print(json.dumps(dict(event="model_built", n=n, states=len(states), seconds=build_seconds)), flush=True)
        started = time.perf_counter()
        groups, iterations = model.minimise(table, finals)
        minimise_seconds = time.perf_counter() - started
        minimum = len(set(groups))
        lower_exponent = math.comb(n, n // 2)
        assert minimum >= 1 << lower_exponent
        started = time.perf_counter()
        quotient, quotient_finals, initial = model.verify(n, alphabet, states, table, finals, groups)
        pair_probes = verify_pair_semantics(n)
        agreement_states = verify_against_cli(n, alphabet, table, finals, args.output_dir)
        # Save the complete minimized automaton so exact counts remain auditable.
        artifact = dict(n=n, alphabet=alphabet, initial=initial, state_count=minimum,
                        transitions=quotient, final_states=[i for i, f in enumerate(quotient_finals) if f])
        artifact_path = args.output_dir / f"minimal_projected_n{n}.json"
        artifact_path.write_text(json.dumps(artifact, separators=(",", ":")) + "\n", encoding="utf-8")
        record = dict(n=n, alphabet=alphabet, expression=expression, alphabetic_width=width,
                      expression_characters=len(expression), independent_reachable_states=len(states),
                      minimal_projected_states=minimum, refinement_iterations=iterations,
                      build_seconds=build_seconds, minimise_seconds=minimise_seconds,
                      verification_seconds=time.perf_counter() - started,
                      direct_pair_probes=pair_probes, cli_product_agreement_states=agreement_states,
                      theoretical_lower_bound=str(1 << lower_exponent),
                      theoretical_lower_log2=lower_exponent,
                      automaton_sha256=hashlib.sha256(artifact_path.read_bytes()).hexdigest(),
                      status="complete", formalization="independent experiment; not a Rocq theorem")
        records = [old for old in records if old["n"] != n] + [record]
        records.sort(key=lambda item: item["n"])
        path.write_text(json.dumps(records, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n")
        print(json.dumps(record), flush=True)
        model.clear_marker.cache_clear()
        model.add_requirement.cache_clear()


if __name__ == "__main__":
    main()
