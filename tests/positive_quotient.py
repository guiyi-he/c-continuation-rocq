"""Check the emitted DFA against an independent reading of the example."""

import itertools
import re
import sys
from pathlib import Path


def main(path: Path) -> None:
    data = path.read_text(encoding="utf-8")
    count = int(re.search(r"^States: (\d+)$", data, re.MULTILINE).group(1))
    finals_text = re.search(r"^F = \{([^}]*)\}$", data, re.MULTILINE).group(1)
    finals = {int(x) for x in finals_text.split(",") if x}
    witnesses = {
        int(state): witness
        for state, witness in re.findall(
            r"^  (\d+): witness=([^ ]*) continuation=", data, re.MULTILINE
        )
    }
    edges = {
        (int(source), symbol): int(target)
        for source, symbol, target in re.findall(
            r"^  (\d+) -([ab])-> (\d+)$", data, re.MULTILINE
        )
    }
    assert count == 27
    assert set(witnesses) == set(range(count))
    assert len(set(witnesses.values())) == count
    assert len(edges) == 2 * count
    assert all(0 <= target < count for target in edges.values())
    assert finals <= set(range(count))

    def run(word: str) -> int:
        state = 0
        for symbol in word:
            state = edges[state, symbol]
        return state

    for state, witness in witnesses.items():
        assert run(witness) == state
    for length in range(11):
        for letters in itertools.product("ab", repeat=length):
            word = "".join(letters)
            expected = length >= 8 and "a" in word and "b" in word
            assert (run(word) in finals) == expected, word
    print(f"checked {count} states, {len(edges)} transitions and all words through length 10")


if __name__ == "__main__":
    main(Path(sys.argv[1]))
