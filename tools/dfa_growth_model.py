"""Independent DFA for the projected language of the E_n example family.

States consist of completed marker requirements and one unfinished b/c block.
This is an experiment model, not a replacement for the Rocq-extracted CLI.
"""

from collections import deque
from functools import lru_cache
import itertools


MARKERS = "xyzdefghijklmnopqrstuvw"


def family(n):
    if not 1 <= n <= len(MARKERS):
        raise ValueError("Unsupported number of distinct single-character markers")
    alphabet = "abc" + MARKERS[:n]
    sigma = "(" + "+".join(alphabet) + ")"
    expression = sigma + "*a" + "".join(
        "(b+cLA(" + sigma + "*" + x + "))" for x in MARKERS[:n]
    ) + sigma + "*"
    return alphabet, expression, n * n + 8 * n + 7


def canonical_requirements(requirements):
    """Drop a conjunction if another conjunction is a subset of it."""
    result = []
    for mask in sorted(set(requirements), key=lambda x: (x.bit_count(), x)):
        if not any((old & mask) == old for old in result):
            result.append(mask)
    return tuple(sorted(result))


@lru_cache(None)
def clear_marker(requirements, bit):
    return canonical_requirements(mask & ~bit for mask in requirements)


@lru_cache(None)
def add_requirement(requirements, mask):
    return canonical_requirements((*requirements, mask))


def state_step(n, state, letter):
    requirements, progress, current = state
    if requirements == (0,):
        return ((0,), -1, 0)
    if letter in MARKERS[:n]:
        bit = 1 << MARKERS.index(letter)
        requirements = clear_marker(requirements, bit)
        return (requirements, -1, 0)
    if letter == "a":
        return (requirements, 0, 0)
    if progress < 0:
        return state
    if letter == "c":
        current |= 1 << progress
    progress += 1
    if progress == n:
        requirements = add_requirement(requirements, current)
        return (requirements, -1, 0)
    return (requirements, progress, current)


def direct_accept(n, word):
    """Scan each candidate a/b/c block, without running state transitions."""
    for start, letter in enumerate(word):
        if letter != "a":
            continue
        block = word[start + 1:start + 1 + n]
        if len(block) != n or any(c not in "bc" for c in block):
            continue
        suffix = word[start + 1 + n:]
        if all(c == "b" or MARKERS[i] in suffix for i, c in enumerate(block)):
            return True
    return False


def build(n):
    alphabet, _, _ = family(n)
    states = [((), -1, 0)]
    ids = {states[0]: 0}
    transitions = []
    for state in states:
        targets = []
        for letter in alphabet:
            target = state_step(n, state, letter)
            if target not in ids:
                ids[target] = len(states)
                states.append(target)
            targets.append(ids[target])
        transitions.append(targets)
    finals = [state[0] == (0,) for state in states]
    return alphabet, states, transitions, finals


def minimise(transitions, finals):
    """Moore refinement using array sorting; returns exact quotient IDs."""
    import numpy as np
    table = np.asarray(transitions, dtype=np.int32)
    groups = np.asarray(finals, dtype=np.int32)
    iterations = 0
    while True:
        signatures = np.column_stack((groups, groups[table]))
        _, updated = np.unique(signatures, axis=0, return_inverse=True)
        updated = updated.astype(np.int32)
        iterations += 1
        if len(np.unique(updated)) == len(np.unique(groups)):
            return updated.tolist(), iterations
        groups = updated


def verify(n, alphabet, states, transitions, finals, groups):
    """Check the original and quotient transition tables and acceptance."""
    assert len(states) == len(set(states)) == len(transitions) == len(finals)
    representatives = {}
    for q, group in enumerate(groups):
        representatives.setdefault(group, q)
    quotient = []
    quotient_finals = []
    for group in range(len(representatives)):
        q = representatives[group]
        quotient.append([groups[t] for t in transitions[q]])
        quotient_finals.append(finals[q])
    for q, state in enumerate(states):
        assert finals[q] == (state[0] == (0,))
        assert finals[q] == quotient_finals[groups[q]]
        assert [groups[t] for t in transitions[q]] == quotient[groups[q]]
        assert all(0 <= t < len(states) for t in transitions[q])
    # All reachable states are added from transitions during build. Check again.
    reached = {0}
    pending = deque([0])
    while pending:
        for t in transitions[pending.popleft()]:
            if t not in reached:
                reached.add(t)
                pending.append(t)
    assert len(reached) == len(states)
    # Exhaustive short words, independent acceptance condition.
    for length in range(min(n + 3, 6) + 1):
        for letters in itertools.product(alphabet, repeat=length):
            word = "".join(letters)
            q = 0
            for a in word:
                q = transitions[q][alphabet.index(a)]
            assert finals[q] == direct_accept(n, word), (n, word)
    return quotient, quotient_finals, groups[0]
