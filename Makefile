ROCQ=rocq compile -Q theories CCont

.PHONY: all cli test clean

all:
	$(ROCQ) theories/StringConstraints.v
	$(ROCQ) theories/Syntax.v
	$(ROCQ) theories/OrdinaryDerivatives.v
	$(ROCQ) theories/LookaheadSemantics.v
	$(ROCQ) theories/ConstraintExpansion.v
	$(ROCQ) theories/LookaheadDerivatives.v
	$(ROCQ) theories/PaperGuards.v
	$(ROCQ) theories/LookaheadDecision.v
	$(ROCQ) theories/PositiveCongruence.v
	$(ROCQ) theories/PositiveCongruenceNormalization.v
	$(ROCQ) theories/SemanticDFA.v
	$(ROCQ) theories/MiyazakiMinamideComparison.v
	$(ROCQ) theories/DerivativeLowerBound.v
	$(ROCQ) theories/LowerBoundFamily.v
	$(ROCQ) theories/TightLowerBoundFamily.v
	$(ROCQ) theories/TightAutomaton.v
	$(ROCQ) theories/OrdinaryResiduals.v
	$(ROCQ) theories/PeriodicAutomaton.v
	$(ROCQ) theories/PeriodicDisplay.v
	$(ROCQ) theories/Automaton.v
	$(ROCQ) theories/Construction.v
	$(ROCQ) theories/Canonical.v
	$(ROCQ) theories/Correctness.v
	$(ROCQ) theories/Extraction.v

cli: all
	opam exec -- dune build cli/ccont.exe

test: cli
	$(ROCQ) theories/Examples.v
	opam exec -- dune exec cli/core_tests.exe
	opam exec -- dune exec ccont -- --automaton both --format text "x*(xx+y)*" > _build/paper.txt
	opam exec -- dune exec ccont -- --automaton quotient --format json "x*(xx+y)*" | tr -d '\r' > _build/paper.json
	diff -u tests/paper_quotient.json _build/paper.json
	opam exec -- dune exec ccont -- --automaton ce --format dot "x*(xx+y)*" > _build/paper.dot
	opam exec -- dune exec ccont -- --automaton rewpla --alphabet ab --format json "((a+b)*a)LA(((a+b)(a+b)(a+b))*)LA(((a+b)(a+b)(a+b)(a+b)(a+b))*)" > _build/requested_rewpla.json
	opam exec -- dune exec ccont -- --automaton rewpla --alphabet ab --format text -o _build/requested_rewpla.txt "((a+b)*a)LA(((a+b)(a+b)(a+b))*)LA(((a+b)(a+b)(a+b)(a+b)(a+b))*)"
	opam exec -- dune exec ccont -- --automaton rewpla --alphabet ab --format text -o _build/periodic23.txt '((a+b)*b)LA(((a+b)(a+b))*)LA(((a+b)(a+b)(a+b))*)'
	opam exec -- dune exec ccont -- --automaton rewpla --alphabet xyz --format json -o _build/periodic_xyz.json '((x+y+z)*z)LA(((z+x+y)(x+y+z))*)LA(((x+y+z)(y+z+x)(x+y+z))*)'
	opam exec -- dune exec ccont -- --automaton rewpla --alphabet ab --format text -o _build/other_rewpla.txt 'LA(a)+a'
	opam exec -- dune exec ccont -- --automaton rewpla --alphabet ab --format text -o _build/aci_rewpla.txt 'b+a'
	opam exec -- dune exec ccont -- --automaton rewpla --alphabet ab --format text -o _build/aci_merge_rewpla.txt 'a(a+b)+b(b+a)'
	opam exec -- dune exec ccont -- --automaton rewpla --alphabet a --format text -o _build/unit_rewpla.txt '1.a+a.1'
	opam exec -- dune exec ccont -- --automaton rewpla --alphabet ab --format text -o _build/positive_congruence_rewpla.txt 'LA((a+b)*a)LA((a+b)*b)(a+b)(a+b)(a+b)(a+b)(a+b)(a+b)(a+b)(a+b)(a+b)*'
	opam exec -- dune exec ccont -- --automaton rewpla --alphabet abcdexh --format text -o _build/tight_k3.txt '(a+b+c+d+e+x)*ae*(b+cLA(((a+b+c+d+e+x)(a+b+c+d+e+x)(a+b+c+d+e+x))*x))*d(a+b+c+d+e+x)*h'
	opam exec -- dune exec ccont -- --automaton rewpla --alphabet abcdexh --format json -o _build/tight_k4.json '(a+b+c+d+e+x)*ae*(b+cLA(((a+b+c+d+e+x)(a+b+c+d+e+x)(a+b+c+d+e+x)(a+b+c+d+e+x))*x))*d(a+b+c+d+e+x)*h'
	grep -q "States: 5" _build/paper.txt
	grep -q "States: 3" _build/paper.txt
	grep -q "subgraph cluster_ce" _build/paper.dot
	grep -q '"method":"verified-periodic-family"' _build/requested_rewpla.json
	grep -q '"modulus":15,"periods":\[3,5\]' _build/requested_rewpla.json
	grep -q 'States: 14' _build/periodic23.txt
	grep -q '"method":"verified-periodic-family"' _build/periodic_xyz.json
	grep -q '"modulus":6,"periods":\[2,3\],"state_count":14' _build/periodic_xyz.json
	grep -q '"state_count":182' _build/requested_rewpla.json
	grep -q '"derivative_regex"' _build/requested_rewpla.json
	grep -q '"final_states"' _build/requested_rewpla.json
	grep -q 'States: 182' _build/requested_rewpla.txt
	grep -q 'delta: Q x Sigma -> Q' _build/requested_rewpla.txt
	grep -q 'continuation=.*LA(' _build/requested_rewpla.txt
	grep -q 'Transitions:' _build/requested_rewpla.txt
	grep -q '  0: witness= continuation=(a+b)' _build/requested_rewpla.txt
	grep -q '  1: witness=a continuation=.*+LA(' _build/requested_rewpla.txt
	grep -Fq 'LA(((a+b).(a+b).(a+b))*).LA(((a+b).(a+b).(a+b).(a+b).(a+b))*)' _build/requested_rewpla.txt
	! grep -q '  0:.*LA(0)' _build/requested_rewpla.txt
	! grep -q 'LA(1\.' _build/requested_rewpla.txt
	grep -q 'continuation=a+LA(a)' _build/other_rewpla.txt
	grep -q '  0 -a-> 1' _build/other_rewpla.txt
	grep -q 'continuation=a+b' _build/aci_rewpla.txt
	grep -q 'States: 4' _build/aci_merge_rewpla.txt
	grep -q '  0 -a-> 1' _build/aci_merge_rewpla.txt
	grep -q '  0 -b-> 1' _build/aci_merge_rewpla.txt
	grep -q 'continuation=a final=false' _build/unit_rewpla.txt
	grep -q 'States: 27' _build/positive_congruence_rewpla.txt
	grep -q 'positive-congruence classes' _build/positive_congruence_rewpla.txt
	grep -q 'verified tight phase/obligation construction, k=3' _build/tight_k3.txt
	grep -q 'States: 202' _build/tight_k3.txt
	grep -q '"method":"verified-tight-phase-obligations"' _build/tight_k4.json
	grep -q '"k":4,"state_count":3026' _build/tight_k4.json
	python tests/positive_quotient.py _build/positive_congruence_rewpla.txt
	@if opam exec -- dune exec ccont -- "(a+b" >/dev/null 2>&1; then exit 1; else true; fi

clean:
	opam exec -- dune clean
	rocq clean -Q theories CCont theories/StringConstraints.v theories/Syntax.v theories/OrdinaryDerivatives.v theories/LookaheadSemantics.v theories/ConstraintExpansion.v theories/LookaheadDerivatives.v theories/PaperGuards.v theories/LookaheadDecision.v theories/PositiveCongruence.v theories/PositiveCongruenceNormalization.v theories/SemanticDFA.v theories/MiyazakiMinamideComparison.v theories/DerivativeLowerBound.v theories/LowerBoundFamily.v theories/TightLowerBoundFamily.v theories/TightAutomaton.v theories/OrdinaryResiduals.v theories/PeriodicAutomaton.v theories/PeriodicDisplay.v theories/Automaton.v theories/Construction.v theories/Canonical.v theories/Correctness.v theories/Extraction.v theories/Examples.v
