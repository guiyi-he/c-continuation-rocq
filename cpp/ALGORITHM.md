# Semantic and algorithmic correspondence

This directory is an independent experimental C++ implementation. It does
not link against, overwrite, or regenerate the Rocq/OCaml implementation. Its
semantic authority remains the paper and the proved definitions under
`../theories`.

## Observed language

The solver decides the projected word language

\[
L_\pi(r)=\{uv\mid(u,v)\in\mathcal M(r)\},
\]

not the host-language behavior of a conventional backtracking regex engine.
Consequently `LA(a)` has the witness `a`: the lookahead has empty *main*
component but contributes the least required continuation to the projection.
Likewise, `LA(a)b` is empty for distinct symbols `a` and `b`, because their
requirements are prefix-incompatible. These choices follow:

- `LookaheadSemantics.rewpla_denote` and `rewpla_language`;
- paper Eq. (9) and the projected-language definition;
- `LookaheadDerivatives.rewpla_acceptb_correct`.

The real-regex frontend is a syntax translation into this language; it does
not silently replace the paper semantics with a host engine's acceptance
semantics. This distinction matters at an end anchor. For example, the
projected language of `^a(?=b)$` contains `ab`, because `b` is the required
continuation, whereas a conventional full-match engine rejects `ab` because
the assertion is zero-width and the consuming part ends after `a`. Search
wrapping agrees with conventional search on the tested common fragment, but
that empirical frontend agreement is not used as a theorem equating these two
semantics.

## Partial derivatives

For each expression `r` and symbol `a`, the implementation computes two
finite sets `PDm_a(r)` and `PDc_a(r)`. Writing `sum(S)` for the union of the
expressions in a set, the intended invariant is

\[
\mathcal M(\operatorname{sum}(PDm_a(r)))=
\mathcal M(\pi_1(D_a(r))),\qquad
\mathcal M(\operatorname{sum}(PDc_a(r)))=
\mathcal M(\pi_2(D_a(r))).
\]

The clauses in `src/partial_derivative.cpp` are the union-flattened form of
paper Eq. (20) and `LookaheadDerivatives.symbol_derivative_core`:

| constructor | main partial derivatives | context partial derivatives |
|---|---|---|
| `0`, `1` | empty | empty |
| `b` | `{1}` if `a=b`, else empty | empty |
| `r+s` | union of component sets | union of component sets |
| `rs` | `PDm(r)s`, `PDc(r)PDm(s)`, and `PDm(s)` if `nullable(r)` | `PDc(r)PDc(s)`, `PDc(r)` if `nullable(s)`, and `PDc(s)` if `nullable(r)` |
| `r*` | `PDm(r)r*` and `PDc(r)PDm(r)r*` | `PDc(r)` |
| `LA(r)` | empty | `LA(sum(PDm(r) union PDc(r)))`, flattened with the proved lookahead laws |

An NFA state is one expression term. A runtime NFA configuration is a sorted
set of such terms. Its transition is the union of main and context partial
derivatives, and it is final when any term satisfies
`LookaheadSemantics.rewpla_nullable`. Thus the NFA simulates the proved merged
derivative without eagerly constructing its deterministic powerset.

## Sound canonicalization

Hash-consing is syntactic; no unproved semantic equality is used. Smart
constructors apply only equations proved for the complete pair language
`M`:

- union ACI and zero, concatenation identity/zero/associativity;
- adjacent positive-lookahead commutativity and idempotence (P10--P11);
- `LA(0)=0`, `LA(1)=1`, nested-lookahead elimination, lookahead distribution
  over union, and leading-constraint lifting.

The corresponding executable/proof sources are
`LookaheadDecision.rewpla_paper_normalize` and
`PositiveCongruenceNormalization.rewpla_positive_normalize`.

The default `Compact` arena deliberately does not apply distributivity below
concatenation: retaining a shared union such as `(a+b)` prevents an eager DNF
blow-up and is the representation expected by the partial-derivative
algorithm.  `NormalizationMode::DistributiveDnf` remains available for an
ablation; it applies the same proved equations, so this choice changes
representation and performance, not semantics.

## On-the-fly intersection and witnesses

For expressions `r_1,...,r_k`, a search configuration is a vector of NFA
state sets. A symbol advances every component; a configuration is accepting
exactly when every component has a nullable term. Breadth-first search creates
only reachable product configurations. Alphabet order is transition order, so
the first result is a shortest witness, with that order as the deterministic
tie-break.

Search has three results:

- `SAT`, with a replay-checked witness;
- `UNSAT`, only after the reachable product is exhausted;
- `RESOURCE_LIMIT`, never conflated with `UNSAT`.

`tests/differential.py` independently builds the existing extracted-OCaml
DFAs, intersects them on the fly, and compares both the result and shortest
witness with the C++ solver. It also enumerates bounded words and checks each
membership result by intersecting the C++ NFA with the corresponding singleton
word expression.
