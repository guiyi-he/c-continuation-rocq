ROCQ=rocq compile -Q theories CCont

.PHONY: all cli test clean

all:
	$(ROCQ) theories/Syntax.v
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
	grep -q "States: 5" _build/paper.txt
	grep -q "States: 3" _build/paper.txt
	grep -q "subgraph cluster_ce" _build/paper.dot
	@if opam exec -- dune exec ccont -- "(a+b" >/dev/null 2>&1; then exit 1; else true; fi

clean:
	opam exec -- dune clean
	rocq clean -Q theories CCont theories/Syntax.v theories/Automaton.v theories/Construction.v theories/Canonical.v theories/Correctness.v theories/Extraction.v theories/Examples.v
