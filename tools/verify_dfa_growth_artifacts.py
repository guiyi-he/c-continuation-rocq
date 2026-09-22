"""Check the saved automata, including targeted nonempty lookahead obligations."""

from collections import deque
import functools
import hashlib
import importlib.util
import json
from pathlib import Path
import random

import dfa_growth_model as model


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments/dfa_growth"


def main():
    spec = importlib.util.spec_from_file_location("growth_oracle", ROOT / "tests/periodic_dfa.py")
    oracle = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(oracle)
    records = json.loads((OUT / "model_measurements.json").read_text(encoding="utf-8"))
    results = []
    for r in records:
        n = r["n"]
        path = OUT / f"minimal_projected_n{n}.json"
        assert hashlib.sha256(path.read_bytes()).hexdigest() == r["automaton_sha256"]
        dfa = json.loads(path.read_text(encoding="utf-8"))
        alphabet, table, initial = dfa["alphabet"], dfa["transitions"], dfa["initial"]
        finals = set(dfa["final_states"])
        assert len(table) == dfa["state_count"] == r["minimal_projected_states"]
        assert all(len(row) == len(alphabet) for row in table)
        assert all(0 <= t < len(table) for row in table for t in row)
        reached, pending = {initial}, deque([initial])
        while pending:
            for t in table[pending.popleft()]:
                if t not in reached:
                    reached.add(t)
                    pending.append(t)
        assert len(reached) == len(table)
        groups, _ = model.minimise(table, [q in finals for q in range(len(table))])
        assert len(set(groups)) == len(table), "Saved quotient is not minimal"
        def accepts(word):
            q = initial
            for a in word:
                q = table[q][alphabet.index(a)]
            return q in finals
        sigma = functools.reduce(lambda a, b: ("plus", a, b), [("atom", c) for c in alphabet])
        factors = [("star", sigma), ("atom", "a")]
        factors += [("plus", ("atom", "b"), ("concat", ("atom", "c"),
                     ("lookahead", ("concat", ("star", sigma), ("atom", x)))))
                    for x in model.MARKERS[:n]]
        factors += [("star", sigma)]
        expr = functools.reduce(lambda a, b: ("concat", a, b), factors)
        probes = 0
        def check_pair(word):
            nonlocal probes
            actual = any(oracle.pair_member(expr, word[:j], word[j:]) for j in range(len(word)+1))
            assert actual == model.direct_accept(n, word) == accepts(word), (n, word)
            probes += 1
        for mask in range(1 << n):
            block = "a" + "".join("c" if mask >> i & 1 else "b" for i in range(n))
            markers = "".join(model.MARKERS[i] for i in range(n) if mask >> i & 1)
            check_pair(block + markers)
            for missing in markers:
                check_pair(block + markers.replace(missing, ""))
            if markers:
                check_pair(markers + block)  # A marker before the block cannot satisfy LA.
        rng = random.Random(1709+n)
        for _ in range(1000):
            word = "".join(rng.choice(alphabet) for _ in range(rng.randrange(101)))
            assert accepts(word) == model.direct_accept(n, word), (n, word)
        cli_path = OUT / f"cli_n{n}.json"
        product_count = None
        if cli_path.exists():
            cli = json.loads(cli_path.read_text(encoding="utf-8"))
            edges = {(e["from"], e["symbol"]): e["to"] for e in cli["transitions"]}
            cli_finals = set(cli["final_states"])
            pairs = [(cli["initial"], initial)]
            seen = set(pairs)
            for cq, mq in pairs:
                assert (cq in cli_finals) == (mq in finals)
                for i, letter in enumerate(alphabet):
                    target = (edges[cq, letter], table[mq][i])
                    if target not in seen:
                        seen.add(target)
                        pairs.append(target)
            product_count = len(seen)
        results.append(dict(n=n, saved_states=len(table), reachable=True, minimal=True,
                            sha256_matches=True, targeted_pair_probes=probes,
                            random_direct_accept_probes=1000, cli_product_states=product_count))
        oracle.pair_member.cache_clear()
        print(json.dumps(results[-1]), flush=True)
    (OUT / "artifact_verification.json").write_text(json.dumps(results, indent=2)+"\n", encoding="utf-8")


if __name__ == "__main__":
    main()
