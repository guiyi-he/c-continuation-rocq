#include "rewpla/rewpla.hpp"

#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {

using rewpla::ExprId;
using rewpla::SolveStatus;
using rewpla::Symbol;

struct Outcome {
  SolveStatus status;
  std::string witness;
};

Outcome solve_eager(const std::string& alphabet,
                    const std::vector<std::string>& sources) {
  rewpla::Arena arena;
  std::vector<ExprId> expressions;
  for (const std::string& source : sources) {
    expressions.push_back(rewpla::Parser(arena, source).parse());
  }
  rewpla::PartialDerivativeNfa nfa(arena);
  std::vector<Symbol> symbols(alphabet.begin(), alphabet.end());
  rewpla::EagerIntersectionSolver solver(arena, nfa, std::move(symbols));
  const rewpla::EagerSolveResult result = solver.solve(expressions);
  return {result.status, result.witness};
}

Outcome solve(const std::string& alphabet,
              const std::vector<std::string>& sources) {
  rewpla::Arena arena;
  std::vector<ExprId> expressions;
  for (const std::string& source : sources) {
    expressions.push_back(rewpla::Parser(arena, source).parse());
  }
  rewpla::PartialDerivativeNfa nfa(arena);
  std::vector<Symbol> symbols(alphabet.begin(), alphabet.end());
  rewpla::IntersectionSolver solver(arena, nfa, std::move(symbols));
  const rewpla::SolveResult result = solver.solve(expressions);
  if (result.status == SolveStatus::Sat) {
    for (ExprId expression : expressions) {
      if (!nfa.accepts(expression, result.witness)) {
        throw std::runtime_error("returned witness failed replay");
      }
    }
  }
  return {result.status, result.witness};
}

bool accepts(const std::string& source, const std::string& word) {
  rewpla::Arena arena;
  const ExprId expression = rewpla::Parser(arena, source).parse();
  rewpla::PartialDerivativeNfa nfa(arena);
  return nfa.accepts(expression, word);
}

bool regex_accepts(const std::string& alphabet, const std::string& source,
                   const std::string& word, rewpla::RegexMatchMode mode) {
  rewpla::Arena arena;
  std::vector<Symbol> symbols(alphabet.begin(), alphabet.end());
  const ExprId expression =
      rewpla::RegexFrontend(arena, source, symbols,
                            rewpla::RegexFrontendOptions{mode, 10'000})
          .parse();
  rewpla::PartialDerivativeNfa nfa(arena);
  return nfa.accepts(expression, word);
}

Outcome solve_regex(const std::string& alphabet, const std::string& source,
                    rewpla::RegexMatchMode mode) {
  rewpla::Arena arena;
  std::vector<Symbol> symbols(alphabet.begin(), alphabet.end());
  const ExprId expression =
      rewpla::RegexFrontend(arena, source, symbols,
                            rewpla::RegexFrontendOptions{mode, 10'000})
          .parse();
  rewpla::PartialDerivativeNfa nfa(arena);
  rewpla::IntersectionSolver solver(arena, nfa, symbols);
  const rewpla::SolveResult result = solver.solve({expression});
  return {result.status, result.witness};
}

std::string distance_expression(std::size_t n) {
  std::string constraint;
  for (std::size_t i = 0; i < n; ++i) {
    constraint += "(a+b)";
  }
  return "(a+b)*aLA(" + constraint + "b)";
}

void expect(const std::string& name, const std::string& alphabet,
            const std::vector<std::string>& sources, SolveStatus status,
            const std::string& witness = "") {
  const Outcome actual = solve(alphabet, sources);
  if (actual.status != status ||
      (status == SolveStatus::Sat && actual.witness != witness)) {
    std::cerr << "FAILED " << name << ": got status="
              << static_cast<int>(actual.status) << " witness='"
              << actual.witness << "'\n";
    std::exit(1);
  }
}

void expect_accepts(const std::string& expression, const std::string& word,
                    bool expected) {
  const bool actual = accepts(expression, word);
  if (actual != expected) {
    std::cerr << "FAILED acceptance: expression=" << expression << " word='"
              << word << "' expected=" << expected << " got=" << actual
              << "\n";
    std::exit(1);
  }
}

void expect_eager_agrees(const std::string& name, const std::string& alphabet,
                         const std::vector<std::string>& sources) {
  const Outcome lazy = solve(alphabet, sources);
  const Outcome eager = solve_eager(alphabet, sources);
  if (lazy.status != eager.status || lazy.witness != eager.witness) {
    std::cerr << "FAILED eager agreement " << name << ": lazy status="
              << static_cast<int>(lazy.status) << " witness='" << lazy.witness
              << "', eager status=" << static_cast<int>(eager.status)
              << " witness='" << eager.witness << "'\n";
    std::exit(1);
  }
}

}  // namespace

int main() {
  expect("zero", "ab", {"0"}, SolveStatus::Unsat);
  expect("epsilon", "ab", {"1"}, SolveStatus::Sat, "");
  expect("atom", "ab", {"a"}, SolveStatus::Sat, "a");
  expect("union alphabet order", "ba", {"a+b"}, SolveStatus::Sat, "b");

  // These cases pin the paper's projected pair-language semantics.  In
  // particular, lookahead contributes its least required continuation to the
  // witness even though its main component is empty.
  expect("lookahead projection", "ab", {"LA(a)"}, SolveStatus::Sat, "a");
  expect("compatible assertion", "ab", {"LA(a)a"}, SolveStatus::Sat, "a");
  expect("incompatible assertion", "ab", {"LA(a)b"}, SolveStatus::Unsat);
  expect("trailing assertion", "ab", {"aLA(b)"}, SolveStatus::Sat, "ab");
  expect("partial assertion consumption", "ab", {"LA(ab)a"},
         SolveStatus::Sat, "ab");
  expect("nested lookahead", "ab", {"LA(LA(a))"}, SolveStatus::Sat, "a");
  expect("constraint union", "ab", {"LA(a+ab)"}, SolveStatus::Sat, "a");

  expect("simple intersection", "ab", {"a+b", "b"}, SolveStatus::Sat,
         "b");
  expect("disjoint atoms", "ab", {"a", "b"}, SolveStatus::Unsat);
  expect("intersection shortest", "ab", {"(a+b)*a", "b*a"},
         SolveStatus::Sat, "a");
  expect("intersection empty", "ab", {"(a+b)*a", "(a+b)*b"},
         SolveStatus::Unsat);
  expect("lookahead intersection", "ab", {"LA(ab)a", "ab"},
         SolveStatus::Sat, "ab");

  expect_eager_agrees("epsilon", "ab", {"1"});
  expect_eager_agrees("lookahead", "ab", {"LA(ab)a", "ab"});
  expect_eager_agrees("unsat", "ab", {"(a+b)*a", "(a+b)*b"});
  expect_eager_agrees("distance even", "ab",
                      {"(a+b)*aLA((a+b)(a+b)b)", "(ab)*"});
  expect_eager_agrees("distance odd", "ab",
                      {"(a+b)*aLA((a+b)b)", "(ab)*"});

  for (std::size_t n = 0; n <= 8; ++n) {
    rewpla::Arena arena;
    const ExprId distance =
        rewpla::Parser(arena, distance_expression(n)).parse();
    const ExprId alternating = rewpla::Parser(arena, "(ab)*").parse();
    rewpla::PartialDerivativeNfa lazy_nfa(arena);
    rewpla::IntersectionSolver lazy_solver(arena, lazy_nfa, {'a', 'b'});
    const rewpla::SolveResult lazy =
        lazy_solver.solve({distance, alternating});
    const SolveStatus expected =
        n % 2 == 0 ? SolveStatus::Sat : SolveStatus::Unsat;
    if (lazy.status != expected ||
        lazy.stats.configurations_discovered != n + 2 ||
        (expected == SolveStatus::Sat && lazy.witness.size() != n + 2)) {
      std::cerr << "FAILED distance-family lazy invariant at n=" << n << '\n';
      return 1;
    }

    rewpla::PartialDerivativeNfa eager_nfa(arena);
    rewpla::EagerIntersectionSolver eager_solver(arena, eager_nfa,
                                                  {'a', 'b'});
    const rewpla::EagerSolveResult eager =
        eager_solver.solve({distance, alternating});
    const std::size_t expected_distance_states =
        std::size_t{3} * (std::size_t{1} << n);
    if (eager.status != lazy.status || eager.witness != lazy.witness ||
        eager.stats.component_dfa_states.size() != 2 ||
        eager.stats.component_dfa_states[0] != expected_distance_states ||
        eager.stats.component_dfa_states[1] != 3) {
      std::cerr << "FAILED distance-family eager invariant at n=" << n << '\n';
      return 1;
    }
  }

  // Both modes use only proved equations and must agree on membership despite
  // very different intermediate representation sizes.
  const std::vector<std::string> normalization_words{
      "", "a", "b", "ab", "aab", "abab", "abba"};
  for (const std::string& word : normalization_words) {
    rewpla::Arena compact;
    const ExprId compact_expression =
        rewpla::Parser(compact, "(a+b)*aLA((a+b)(a+b)b)").parse();
    rewpla::PartialDerivativeNfa compact_nfa(compact);
    rewpla::Arena dnf(1'000'000,
                      rewpla::NormalizationMode::DistributiveDnf);
    const ExprId dnf_expression =
        rewpla::Parser(dnf, "(a+b)*aLA((a+b)(a+b)b)").parse();
    rewpla::PartialDerivativeNfa dnf_nfa(dnf);
    if (compact_nfa.accepts(compact_expression, word) !=
        dnf_nfa.accepts(dnf_expression, word)) {
      std::cerr << "FAILED normalization agreement on word='" << word
                << "'\n";
      return 1;
    }
  }

  expect_accepts("LA(a)", "", false);
  expect_accepts("LA(a)", "a", true);
  expect_accepts("LA(a)", "aa", false);
  expect_accepts("aLA(b)", "ab", true);
  expect_accepts("aLA(b)", "a", false);
  expect_accepts("LA(a)b", "ab", false);
  expect_accepts("(a+b)*", "abba", true);

  const auto projected = rewpla::RegexMatchMode::Projected;
  const auto search = rewpla::RegexMatchMode::Search;
  const Outcome regex_union = solve_regex("ab", "a|b", projected);
  if (regex_union.status != SolveStatus::Sat || regex_union.witness != "a") {
    std::cerr << "FAILED regex alternation frontend\n";
    return 1;
  }
  if (solve_regex("ab", "a?", projected).witness != "" ||
      solve_regex("ab", "a+", projected).witness != "a" ||
      solve_regex("ab", "a{2,3}", projected).witness != "aa" ||
      solve_regex("abc", "[b-c]+", projected).witness != "b" ||
      solve_regex("abc", "[^a]", projected).witness != "b" ||
      solve_regex("ba", ".", projected).witness != "b" ||
      solve_regex("abc", "(?:ab|c){2}", projected).witness != "cc" ||
      solve_regex("ab", "a(?=b)", projected).witness != "ab") {
    std::cerr << "FAILED regex frontend witness translation\n";
    return 1;
  }
  if (!regex_accepts("abcd", "a(?=b)", "cabd", search) ||
      regex_accepts("abcd", "a(?=b)", "cadb", search) ||
      !regex_accepts("ab", "^a", "ab", search) ||
      regex_accepts("ab", "^a", "ba", search) ||
      !regex_accepts("ab", "a$", "ba", search) ||
      regex_accepts("ab", "a$", "ab", search) ||
      !regex_accepts("ab", "^a$", "a", search) ||
      regex_accepts("ab", "^a$", "aa", search) ||
      // This deliberately pins the paper's projected semantics: the required
      // lookahead continuation is part of the projected word even though a
      // host full-match engine treats the assertion as zero-width.
      !regex_accepts("ab", "^a(?=b)$", "ab", projected) ||
      !regex_accepts("abc", "[a-c]{2,3}", "bc", projected)) {
    std::cerr << "FAILED regex frontend membership or anchors\n";
    return 1;
  }

  for (const char* invalid : {"(?!a)", "a*?", "[z]", "^a^", "(a)\\1",
                              "\\b", "\\q"}) {
    try {
      rewpla::Arena arena;
      static_cast<void>(rewpla::RegexFrontend(
          arena, invalid, {'a', 'b'},
          rewpla::RegexFrontendOptions{projected, 10'000})
                            .parse());
      std::cerr << "FAILED unsupported regex was accepted: " << invalid << '\n';
      return 1;
    } catch (const rewpla::ParseError&) {
    }
  }

  try {
    rewpla::Arena arena;
    static_cast<void>(rewpla::Parser(arena, "LA(a").parse());
    std::cerr << "FAILED parser error was not reported\n";
    return 1;
  } catch (const rewpla::ParseError&) {
  }

  std::cout << "all C++ solver unit tests passed\n";
  return 0;
}
