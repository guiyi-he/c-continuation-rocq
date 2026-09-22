"""Independent CLI audit; run with: opam exec -- python tests/periodic_dfa.py.

The oracle evaluates prefix-trigger positions and suffix lengths directly.
It does not call the extracted rotation, union, or fixed Mod15 model.
"""
import collections
import itertools
import json
import math
import functools
import re
import subprocess


def parse_display(text):
    """Parse the actual printed REwPLA, independently of the OCaml parser."""
    position = 0

    def union():
        nonlocal position
        result = concat()
        while position < len(text) and text[position] == "+":
            position += 1
            result = ("plus", result, concat())
        return result

    def concat():
        nonlocal position
        result = repeat()
        while position < len(text) and text[position] == ".":
            position += 1
            result = ("concat", result, repeat())
        return result

    def repeat():
        nonlocal position
        result = atom()
        while position < len(text) and text[position] == "*":
            position += 1
            result = ("star", result)
        return result

    def atom():
        nonlocal position
        if text.startswith("LA(", position):
            position += 3
            result = ("lookahead", union())
            assert text[position] == ")"
            position += 1
            return result
        if text[position] == "(":
            position += 1
            result = union()
            assert text[position] == ")"
            position += 1
            return result
        letter = text[position]
        position += 1
        return ("zero",) if letter == "0" else (
            ("eps",) if letter == "1" else ("atom", letter))

    result = union()
    assert position == len(text)
    return result


@functools.lru_cache(None)
def ordinary_pattern(r):
    if r[0] == "lookahead":
        return None
    if r[0] == "zero":
        return "(?!)"
    if r[0] == "eps":
        return ""
    if r[0] == "atom":
        return re.escape(r[1])
    children = [ordinary_pattern(child) for child in r[1:]]
    if any(child is None for child in children):
        return None
    if r[0] == "star":
        return "(?:" + children[0] + ")*"
    if r[0] == "plus":
        return "(?:" + "|".join(children) + ")"
    return "".join(children)


@functools.lru_cache(None)
def pair_member(r, main, context):
    """Paper Section 3 pair semantics, including the least partial join.

    For concat, both candidate constraints prefix right-main + context.
    Their join equals that target iff at least one candidate is the target.
    This enumerates both cases, without residue arithmetic or derivatives.
    """
    pattern = ordinary_pattern(r)
    if pattern is not None:
        return context == "" and re.fullmatch(pattern, main) is not None
    if r[0] == "plus":
        return pair_member(r[1], main, context) or pair_member(r[2], main, context)
    if r[0] == "lookahead":
        return main == "" and any(
            pair_member(r[1], context[:i], context[i:])
            for i in range(len(context) + 1))
    assert r[0] == "concat", "Only ordinary stars occur in the periodic family"
    for i in range(len(main) + 1):
        left, right = main[:i], main[i:]
        target = right + context
        if pair_member(r[1], left, target) and any(
                pair_member(r[2], right, context[:j])
                for j in range(len(context) + 1)):
            return True
        if pair_member(r[2], right, context) and any(
                pair_member(r[1], left, target[:j])
                for j in range(len(target) + 1)):
            return True
    return False


def period_star_lengths(r):
    if r[0] == "star":
        def width(node):
            if node[0] == "atom":
                return 1
            if node[0] == "plus":
                assert width(node[1]) == width(node[2])
                return width(node[1])
            assert node[0] == "concat"
            return width(node[1]) + width(node[2])
        return [width(r[1])]
    return [p for child in r[1:] if isinstance(child, tuple)
            for p in period_star_lengths(child)]


def union_branches(r):
    if r[0] == "plus":
        return union_branches(r[1]) + union_branches(r[2])
    return [r]


def concat_factors(r):
    if r[0] == "concat":
        return concat_factors(r[1]) + concat_factors(r[2])
    return [r]


def sigma_letters(r):
    if r[0] == "atom":
        return {r[1]}
    assert r[0] == "plus", r
    return sigma_letters(r[1]) | sigma_letters(r[2])


def assertion_descriptor(r, alphabet):
    assert r[0] == "lookahead", r
    factors = concat_factors(r[1])
    assert factors[-1][0] == "star"
    assert all(sigma_letters(factor) == set(alphabet) for factor in factors[:-1])
    block = concat_factors(factors[-1][1])
    assert all(sigma_letters(factor) == set(alphabet) for factor in block)
    return len(block), len(factors) - 1


def context_product_rule(branch):
    """Literal Eq. (20): derivative product and BOTH epsilon-factor terms.

    Track each assertion's period and current residual offset. Epsilon guards
    are evaluated separately for each step, with no subset absorption.
    """
    left, *right = branch
    period, offset = left
    derivative_left = ((period, (offset - 1) % period),)
    if not right:
        return {derivative_left}
    derivative_right = context_product_rule(tuple(right))
    result = {derivative_left + branch for branch in derivative_right}
    if all(offset == 0 for _, offset in right):
        result.add(derivative_left)
    if offset == 0:
        result.update(derivative_right)
    return result


@functools.lru_cache(None)
def rule_expansion(periods, shift):
    branches = {tuple((period, 0) for period in periods)}
    for _ in range(shift):
        branches = {new for branch in branches for new in context_product_rule(branch)}
    return branches


def check_rule_branches(syntax, witness, alphabet, trigger, periods):
    actual = set()
    initial_branches = 0
    for branch in union_branches(syntax):
        factors = concat_factors(branch)
        if factors[0][0] == "star":
            initial_branches += 1
            assert sigma_letters(factors[0][1]) == set(alphabet)
            assert factors[1] == ("atom", trigger)
            assert tuple(assertion_descriptor(r, alphabet) for r in factors[2:]) == tuple(
                (period, 0) for period in periods)
        else:
            actual.add(tuple(assertion_descriptor(r, alphabet) for r in factors))
    assert initial_branches == 1
    expected = set()
    for i, letter in enumerate(witness):
        if letter == trigger:
            expected.update(rule_expansion(tuple(periods), len(witness) - i - 1))
    assert actual == expected, (witness, actual - expected, expected - actual)


def check_text_json(dfa, alphabet, input_expression):
    result = subprocess.run([
        "dune", "exec", "ccont", "--", "--automaton", "rewpla",
        "--alphabet", alphabet, "--format", "text", input_expression,
    ], check=True, capture_output=True, text=True, encoding="utf-8")
    states = re.findall(r"^  (\d+): witness=(.*?) continuation=(.*?) final=(true|false)",
                        result.stdout, re.MULTILINE)
    assert [(int(i), w, expression, final == "true") for i, w, expression, final in states] == [
        (q["id"], q["witness"], q["representative"], q["accepting"]) for q in dfa["states"]]
    edges = re.findall(r"^  (\d+) -(.)-> (\d+)", result.stdout, re.MULTILINE)
    assert [(int(i), a, int(j)) for i, a, j in edges] == [
        (e["from"], e["symbol"], e["to"]) for e in dfa["transitions"]]


def expanded_products(r):
    if r[0] == "plus":
        return expanded_products(r[1]) | expanded_products(r[2])
    if r[0] == "concat":
        return {left + right for left in expanded_products(r[1])
                for right in expanded_products(r[2])}
    return {(r,)}


def audit_generic_products():
    la_eps = ("lookahead", ("eps",))
    cases = [
        ("LA(a).LA(a)", {(la_eps, la_eps)}),
        ("LA(1+a).LA(1+a)", {(la_eps,), (la_eps, la_eps)}),
        ("LA(1+a).LA(1+b)", {(la_eps,)}),
        ("LA(1+a).LA(1+a).LA(1+a)", {
            (la_eps,), (la_eps, la_eps), (la_eps, la_eps, la_eps)}),
        ("LA(a)+a", {(("eps",),), (la_eps,)}),
    ]
    short_words = ["".join(w) for n in range(3) for w in itertools.product("ab", repeat=n)]
    for input_expression, expected_a in cases:
        result = subprocess.run([
            "dune", "exec", "ccont", "--", "--automaton", "rewpla",
            "--alphabet", "ab", "--format", "json", input_expression,
        ], check=True, capture_output=True, text=True, encoding="utf-8")
        dfa = json.loads(result.stdout)
        assert dfa["method"] == "checked-normalized-derivatives"
        check_text_json(dfa, "ab", input_expression)
        original = parse_display(input_expression)
        states = {q["id"]: q for q in dfa["states"]}
        edge_a = next(e for e in dfa["transitions"] if e["from"] == 0 and e["symbol"] == "a")
        after_a = parse_display(states[edge_a["to"]]["representative"])
        assert expanded_products(after_a) == expected_a, (input_expression, after_a)
        components = parse_display(edge_a["main_derivative"] + "+" + edge_a["context_derivative"])
        assert expanded_products(components) - {(("zero",),)} == expected_a
        for q in dfa["states"]:
            syntax = parse_display(q["representative"])
            witness = q["witness"]
            for main in short_words:
                for context in short_words:
                    expected = (pair_member(original, witness + main, context) if main else any(
                        pair_member(original, witness[:i], witness[i:] + context)
                        for i in range(len(witness) + 1)))
                    assert pair_member(syntax, main, context) == expected
            assert pair_member(syntax, "", "") == q["accepting"]
        for edge in dfa["transitions"]:
            source = parse_display(states[edge["from"]]["representative"])
            main_component = parse_display(edge["main_derivative"])
            context_component = parse_display(edge["context_derivative"])
            for main in short_words:
                for context in short_words:
                    assert pair_member(main_component, main, context) == pair_member(
                        source, edge["symbol"] + main, context)
                    assert pair_member(context_component, main, context) == (
                        main == "" and pair_member(source, "", edge["symbol"] + context))
        print(f"generic {input_expression}: literal products, epsilon branches, pair semantics "
              "of every state/component and text/JSON agreement checked")
    pair_member.cache_clear()


def expression(alphabet, trigger, periods):
    sigma = "(" + "+".join(alphabet) + ")"
    return "(" + sigma + "*" + trigger + ")" + "".join(
        "LA((" + sigma * p + ")*)" for p in periods
    )


def direct_residual(witness, trigger, periods, context_length):
    return any(
        a == trigger and any(
            (len(witness) - i - 1 + context_length) % p == 0
            for p in periods
        )
        for i, a in enumerate(witness)
    )


def independent_bfs(alphabet, trigger, periods, modulus):
    def residual(witness):
        return tuple(direct_residual(witness, trigger, periods, i)
                     for i in range(modulus))

    zero = residual("")
    witnesses = [""]
    values = [zero]
    ids = {zero: 0}
    pending = collections.deque([0])
    edges = []
    while pending:
        source = pending.popleft()
        for a in alphabet:
            witness = witnesses[source] + a
            target_bits = residual(witness)
            if target_bits not in ids:
                ids[target_bits] = len(values)
                witnesses.append(witness)
                values.append(target_bits)
                pending.append(ids[target_bits])
            edges.append((source, a, ids[target_bits]))
    return witnesses, values, edges


def audit(alphabet, trigger, periods, expected_count):
    result = subprocess.run([
        "dune", "exec", "ccont", "--", "--automaton", "rewpla",
        "--alphabet", alphabet, "--format", "json",
        expression(alphabet, trigger, periods),
    ], check=True, capture_output=True, text=True, encoding="utf-8")
    dfa = json.loads(result.stdout)
    check_text_json(dfa, alphabet, expression(alphabet, trigger, periods))
    modulus = math.lcm(*periods)
    assert dfa["method"] == "verified-periodic-family"
    assert dfa["modulus"] == modulus
    assert dfa["periods"] == periods
    witnesses, values, edges = independent_bfs(alphabet, trigger, periods, modulus)
    assert dfa["state_count"] == len(values) == expected_count
    assert len(dfa["states"]) == len(values)
    for q, witness, bits in zip(dfa["states"], witnesses, values):
        assert q["witness"] == witness
        assert q["residue_bits"] == "".join("1" if b else "0" for b in bits)
        assert q["accepting"] == bits[0]
        assert q["residues"] == [i for i, bit in enumerate(bits) if bit]
        assert q["derivative_regex"] == q["representative"]
        assert "LA(" in q["representative"]
        assert "+0" not in q["representative"]
        syntax = parse_display(q["representative"])
        assert set(period_star_lengths(syntax)) <= {1, *periods}
        check_rule_branches(syntax, witness, alphabet, trigger, periods)
        mains = {"", *alphabet, *(a + trigger for a in alphabet)}
        for main in mains:
            for letter in alphabet:
                for n in range(2 * modulus + 1):
                    context = letter * n
                    expected = (main.endswith(trigger) and any(n % p == 0 for p in periods)
                                if main else direct_residual(witness, trigger, periods, n))
                    assert pair_member(syntax, main, context) == expected, (
                        witness, main, context, q["representative"])
    assert [q["id"] for q in dfa["states"]] == list(range(len(values)))
    assert dfa["final_states"] == [i for i, bits in enumerate(values) if bits[0]]
    assert [(e["from"], e["symbol"], e["to"]) for e in dfa["transitions"]] == edges
    for e in dfa["transitions"]:
        witness = witnesses[e["from"]]
        main = tuple(e["symbol"] == trigger and any(i % p == 0 for p in periods)
                     for i in range(modulus))
        context = tuple(direct_residual(witness + "\0", trigger, periods, i)
                        for i in range(modulus))
        encode = lambda bits: "".join("1" if bit else "0" for bit in bits)
        assert e["main_derivative"]["residue_bits"] == encode(main)
        assert e["context_derivative"]["residue_bits"] == encode(context)
    transition = {(source, a): target for source, a, target in edges}
    for n in range(8):
        for letters in itertools.product(alphabet, repeat=n):
            word = "".join(letters)
            state = 0
            for a in word:
                state = transition[state, a]
            assert values[state][0] == direct_residual(word, trigger, periods, 0)
    print(f"alphabet={alphabet}, trigger={trigger}, periods={periods}: "
          f"{len(values)} states/{len(edges)} edges, all printed pair semantics, "
          "Eq. (20) branches, entries and words <=7 checked")
    pair_member.cache_clear()


if __name__ == "__main__":
    for case in [
        ("ab", "a", [3, 5], 182),
        ("ab", "b", [2, 3], 14),
        ("xyz", "z", [2, 3], 14),
        ("xyz", "y", [2, 4], 4),
        ("ab", "b", [1, 7], 2),
        ("ab", "a", [3], 8),
        ("a", "a", [2, 3], 3),
        ("ab", "b", [2, 3, 4], 14),
        ("ab", "a", [2, 3, 4, 6], 14),
        ("ab", "a", [2, 2, 3], 14),
    ]:
        audit(*case)
    audit_generic_products()
