CXX ?= g++
CXXFLAGS ?= -std=c++17 -O2 -Wall -Wextra -Wpedantic
CPPFLAGS ?= -Iinclude

ifeq ($(OS),Windows_NT)
EXEEXT := .exe
endif

BUILD := build
LIB_SOURCES := src/ast.cpp src/parser.cpp src/regex_frontend.cpp src/partial_derivative.cpp src/solver.cpp src/eager_solver.cpp
SOLVER := $(BUILD)/rewpla-solver$(EXEEXT)
REDOS := $(BUILD)/rewpla-redos$(EXEEXT)
UNIT := $(BUILD)/rewpla-solver-tests$(EXEEXT)
DISTANCE_BENCH := $(BUILD)/rewpla-distance-bench$(EXEEXT)

.PHONY: all test differential regex-differential alignment distance-bench suite-smoke suite redos-bench redos-bench-smoke evaluation-smoke evaluation clean

all: $(SOLVER) $(REDOS) $(DISTANCE_BENCH)

$(BUILD):
	mkdir -p $(BUILD)

$(SOLVER): $(LIB_SOURCES) src/main.cpp include/rewpla/rewpla.hpp | $(BUILD)
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) $(LIB_SOURCES) src/main.cpp -o $@

$(REDOS): $(LIB_SOURCES) src/redos_main.cpp include/rewpla/rewpla.hpp | $(BUILD)
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) $(LIB_SOURCES) src/redos_main.cpp -o $@

$(UNIT): $(LIB_SOURCES) tests/test_solver.cpp include/rewpla/rewpla.hpp | $(BUILD)
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) $(LIB_SOURCES) tests/test_solver.cpp -o $@

$(DISTANCE_BENCH): $(LIB_SOURCES) bench/distance_bench.cpp include/rewpla/rewpla.hpp | $(BUILD)
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) $(LIB_SOURCES) bench/distance_bench.cpp -o $@

test: $(SOLVER) $(REDOS) $(UNIT)
	$(UNIT)
	python tests/cli_smoke.py $(SOLVER)
	python tests/regex_frontend_differential.py $(SOLVER)
	python tests/redos_smoke.py $(REDOS)

differential: $(SOLVER)
	python tests/differential.py $(SOLVER)

regex-differential: $(SOLVER)
	python tests/regex_frontend_differential.py $(SOLVER)

alignment: $(SOLVER)
	python tests/differential.py $(SOLVER) --random-cases 200 --seed 20260926 --word-bound 4

distance-bench: $(DISTANCE_BENCH)
	$(DISTANCE_BENCH)

suite-smoke: $(SOLVER)
	python bench/benchmark_suite.py $(SOLVER) --families distance,periodic,topology,ordinary,tight,intersection --distance-range 0:3 --period-sets 2,2+3 --topology-range 1:2 --ordinary-range 1:2 --tight-range 2:2 --intersection-range 1:2

suite: $(SOLVER)
	python bench/benchmark_suite.py $(SOLVER)

redos-bench-smoke: $(REDOS)
	python bench/redos_case_study.py $(REDOS) --max-repetitions 4 --repeat 1 --timeout 2

redos-bench: $(REDOS)
	python bench/redos_case_study.py $(REDOS)

evaluation-smoke: $(SOLVER) $(REDOS) $(UNIT) $(DISTANCE_BENCH)
	python bench/run_evaluation.py --repo .. --profile smoke --output-dir cpp/build/evaluation-smoke --overwrite

evaluation: $(SOLVER) $(REDOS) $(UNIT) $(DISTANCE_BENCH)
	python bench/run_evaluation.py --repo .. --profile full

clean:
	rm -rf $(BUILD)
