#include "rewpla/rewpla.hpp"

#include <algorithm>
#include <charconv>
#include <chrono>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <string>
#include <unordered_set>
#include <vector>

namespace {

using Clock = std::chrono::steady_clock;

using rewpla::ExprId;
using rewpla::EagerSolveResult;
using rewpla::SolveResult;
using rewpla::SolveStatus;
using rewpla::Symbol;

enum class Engine {
  Lazy,
  Eager,
};

enum class SyntaxMode {
  Core,
  Regex,
};

struct CliOptions {
  std::string alphabet;
  bool json = false;
  Engine engine = Engine::Lazy;
  SyntaxMode syntax = SyntaxMode::Core;
  rewpla::RegexMatchMode match_mode = rewpla::RegexMatchMode::Projected;
  bool match_mode_explicit = false;
  rewpla::NormalizationMode normalization =
      rewpla::NormalizationMode::Compact;
  std::size_t max_configurations = 1'000'000;
  std::size_t max_dfa_states = 1'000'000;
  std::size_t max_ast_nodes = 1'000'000;
  std::size_t max_repeat = 10'000;
  std::vector<std::string> expressions;
};

void usage(std::ostream& out) {
  out <<
      "Usage: rewpla-solver --alphabet SYMBOLS [OPTIONS] REGEX [REGEX ...]\n"
      "\n"
      "Decide nonemptiness of the intersection of one or more REwPLA\n"
      "projected languages and emit a shortest witness when one exists.\n"
      "\n"
      "Options:\n"
      "  --alphabet SYMBOLS          finite alphabet and witness order\n"
      "  --json                      emit one JSON object\n"
      "  --engine MODE               lazy (default) or eager\n"
      "  --syntax MODE               core (default) or regex\n"
      "  --match MODE                projected or search (regex default)\n"
      "  --normalization MODE        compact (default) or dnf\n"
      "  --max-configurations N      product state limit (default 1000000)\n"
      "  --max-dfa-states N          eager per-component limit (default 1000000)\n"
      "  --max-ast-nodes N           hash-consed expression limit (default 1000000)\n"
      "  --max-repeat N              regex quantifier bound (default 10000)\n"
      "  -h, --help                  show this help\n"
      "  --version                   show the experimental solver version\n"
      "\n"
      "Syntax: 0, 1, ASCII letters, +, concatenation (implicit or '.'), *,\n"
      "parentheses, and LA(r). With --syntax regex, use byte-oriented |,\n"
      "implicit concatenation, ., classes, repeats, groups, anchors, and\n"
      "(?=r). Multiple REGEX arguments mean intersection.\n";
}

std::size_t parse_positive_size(const std::string& option,
                                const std::string& text) {
  std::size_t result = 0;
  const char* begin = text.data();
  const char* end = begin + text.size();
  const auto parsed = std::from_chars(begin, end, result);
  if (parsed.ec != std::errc{} || parsed.ptr != end || result == 0) {
    throw std::invalid_argument(option + " requires a positive integer");
  }
  return result;
}

CliOptions parse_cli(int argc, char** argv) {
  CliOptions options;
  bool positional_only = false;
  for (int i = 1; i < argc; ++i) {
    const std::string argument = argv[i];
    if (!positional_only && argument == "--") {
      positional_only = true;
    } else if (!positional_only && (argument == "-h" || argument == "--help")) {
      usage(std::cout);
      std::exit(0);
    } else if (!positional_only && argument == "--version") {
      std::cout << "rewpla-solver 0.5.0-experimental\n";
      std::exit(0);
    } else if (!positional_only && argument == "--json") {
      options.json = true;
    } else if (!positional_only && argument == "--engine") {
      if (++i >= argc) {
        throw std::invalid_argument("--engine requires a value");
      }
      const std::string mode = argv[i];
      if (mode == "lazy") {
        options.engine = Engine::Lazy;
      } else if (mode == "eager") {
        options.engine = Engine::Eager;
      } else {
        throw std::invalid_argument("--engine must be 'lazy' or 'eager'");
      }
    } else if (!positional_only && argument == "--syntax") {
      if (++i >= argc) {
        throw std::invalid_argument("--syntax requires a value");
      }
      const std::string mode = argv[i];
      if (mode == "core") {
        options.syntax = SyntaxMode::Core;
      } else if (mode == "regex") {
        options.syntax = SyntaxMode::Regex;
      } else {
        throw std::invalid_argument("--syntax must be 'core' or 'regex'");
      }
    } else if (!positional_only && argument == "--match") {
      if (++i >= argc) {
        throw std::invalid_argument("--match requires a value");
      }
      const std::string mode = argv[i];
      if (mode == "projected") {
        options.match_mode = rewpla::RegexMatchMode::Projected;
      } else if (mode == "search") {
        options.match_mode = rewpla::RegexMatchMode::Search;
      } else {
        throw std::invalid_argument("--match must be 'projected' or 'search'");
      }
      options.match_mode_explicit = true;
    } else if (!positional_only && argument == "--normalization") {
      if (++i >= argc) {
        throw std::invalid_argument("--normalization requires a value");
      }
      const std::string mode = argv[i];
      if (mode == "compact") {
        options.normalization = rewpla::NormalizationMode::Compact;
      } else if (mode == "dnf") {
        options.normalization = rewpla::NormalizationMode::DistributiveDnf;
      } else {
        throw std::invalid_argument(
            "--normalization must be 'compact' or 'dnf'");
      }
    } else if (!positional_only && argument == "--alphabet") {
      if (++i >= argc) {
        throw std::invalid_argument("--alphabet requires a value");
      }
      options.alphabet = argv[i];
    } else if (!positional_only && argument == "--max-configurations") {
      if (++i >= argc) {
        throw std::invalid_argument("--max-configurations requires a value");
      }
      options.max_configurations =
          parse_positive_size("--max-configurations", argv[i]);
    } else if (!positional_only && argument == "--max-dfa-states") {
      if (++i >= argc) {
        throw std::invalid_argument("--max-dfa-states requires a value");
      }
      options.max_dfa_states =
          parse_positive_size("--max-dfa-states", argv[i]);
    } else if (!positional_only && argument == "--max-ast-nodes") {
      if (++i >= argc) {
        throw std::invalid_argument("--max-ast-nodes requires a value");
      }
      options.max_ast_nodes = parse_positive_size("--max-ast-nodes", argv[i]);
    } else if (!positional_only && argument == "--max-repeat") {
      if (++i >= argc) {
        throw std::invalid_argument("--max-repeat requires a value");
      }
      options.max_repeat = parse_positive_size("--max-repeat", argv[i]);
    } else if (!positional_only && argument.rfind("--", 0) == 0) {
      throw std::invalid_argument("unknown option: " + argument);
    } else {
      options.expressions.push_back(argument);
    }
  }

  if (options.alphabet.empty()) {
    throw std::invalid_argument("--alphabet is required and must be nonempty");
  }
  if (options.expressions.empty()) {
    throw std::invalid_argument("at least one REGEX is required");
  }
  if (options.syntax == SyntaxMode::Regex && !options.match_mode_explicit) {
    options.match_mode = rewpla::RegexMatchMode::Search;
  }
  std::unordered_set<unsigned char> symbols;
  for (unsigned char symbol : options.alphabet) {
    if (!symbols.insert(symbol).second) {
      throw std::invalid_argument("--alphabet must not contain duplicate symbols");
    }
  }
  return options;
}

const char* status_name(SolveStatus status) {
  switch (status) {
    case SolveStatus::Sat:
      return "sat";
    case SolveStatus::Unsat:
      return "unsat";
    case SolveStatus::ResourceLimit:
      return "resource_limit";
  }
  return "internal_error";
}

const char* engine_name(Engine engine) {
  return engine == Engine::Lazy ? "lazy" : "eager";
}

const char* syntax_name(SyntaxMode syntax) {
  return syntax == SyntaxMode::Core ? "core" : "regex";
}

const char* match_name(rewpla::RegexMatchMode mode) {
  return mode == rewpla::RegexMatchMode::Projected ? "projected" : "search";
}

ExprId search_wrap(rewpla::Arena& arena, ExprId expression,
                   const std::vector<Symbol>& alphabet) {
  std::vector<ExprId> alternatives;
  for (Symbol symbol : alphabet) alternatives.push_back(arena.atom(symbol));
  const ExprId sigma_star = arena.star(arena.unite(std::move(alternatives)));
  return arena.concat({sigma_star, expression, sigma_star});
}

void print_json(const CliOptions& options, const SolveResult& result,
                double solve_milliseconds) {
  std::cout << "{\"status\":\"" << status_name(result.status) << "\"";
  if (result.status == SolveStatus::Sat) {
    std::cout << ",\"witness\":\"" << rewpla::json_escape(result.witness)
              << "\",\"witness_length\":" << result.witness.size();
  }
  if (!result.detail.empty()) {
    std::cout << ",\"detail\":\"" << rewpla::json_escape(result.detail) << "\"";
  }
  std::cout << ",\"expression_count\":" << options.expressions.size()
            << ",\"alphabet\":\"" << rewpla::json_escape(options.alphabet)
            << "\",\"engine\":\"" << engine_name(options.engine)
            << "\",\"syntax\":\"" << syntax_name(options.syntax)
            << "\",\"match\":\"" << match_name(options.match_mode)
            << "\",\"solve_ms\":" << std::fixed << std::setprecision(6)
            << solve_milliseconds
            << ",\"normalization\":\""
            << (options.normalization == rewpla::NormalizationMode::Compact
                    ? "compact"
                    : "dnf")
            << "\",\"stats\":{"
            << "\"configurations_discovered\":"
            << result.stats.configurations_discovered
            << ",\"configurations_expanded\":"
            << result.stats.configurations_expanded
            << ",\"product_symbol_steps\":"
            << result.stats.product_symbol_steps
            << ",\"partial_states_observed\":"
            << result.stats.partial_states_observed
            << ",\"partial_derivatives_cached\":"
            << result.stats.partial_derivatives_cached
            << ",\"ast_nodes\":" << result.stats.ast_nodes << "}}\n";
}

void print_json(const CliOptions& options, const EagerSolveResult& result,
                double solve_milliseconds) {
  std::cout << "{\"status\":\"" << status_name(result.status) << "\"";
  if (result.status == SolveStatus::Sat) {
    std::cout << ",\"witness\":\"" << rewpla::json_escape(result.witness)
              << "\",\"witness_length\":" << result.witness.size();
  }
  if (!result.detail.empty()) {
    std::cout << ",\"detail\":\"" << rewpla::json_escape(result.detail) << "\"";
  }
  std::cout << ",\"expression_count\":" << options.expressions.size()
            << ",\"alphabet\":\"" << rewpla::json_escape(options.alphabet)
            << "\",\"engine\":\"" << engine_name(options.engine)
            << "\",\"syntax\":\"" << syntax_name(options.syntax)
            << "\",\"match\":\"" << match_name(options.match_mode)
            << "\",\"solve_ms\":" << std::fixed << std::setprecision(6)
            << solve_milliseconds
            << ",\"normalization\":\""
            << (options.normalization == rewpla::NormalizationMode::Compact
                    ? "compact"
                    : "dnf")
            << "\",\"stats\":{\"component_dfa_states\":[";
  for (std::size_t i = 0; i < result.stats.component_dfa_states.size(); ++i) {
    if (i != 0) {
      std::cout << ',';
    }
    std::cout << result.stats.component_dfa_states[i];
  }
  std::cout << "]"
            << ",\"dfa_states_total\":" << result.stats.dfa_states_total
            << ",\"dfa_transitions\":" << result.stats.dfa_transitions
            << ",\"product_configurations_discovered\":"
            << result.stats.product_configurations_discovered
            << ",\"product_configurations_expanded\":"
            << result.stats.product_configurations_expanded
            << ",\"product_symbol_steps\":"
            << result.stats.product_symbol_steps
            << ",\"partial_states_observed\":"
            << result.stats.partial_states_observed
            << ",\"partial_derivatives_cached\":"
            << result.stats.partial_derivatives_cached
            << ",\"ast_nodes\":" << result.stats.ast_nodes << "}}\n";
}

void print_text(const CliOptions& options, const SolveResult& result,
                double solve_milliseconds) {
  if (result.status == SolveStatus::Sat) {
    std::cout << "SAT\n"
              << "witness: " << rewpla::display_word(result.witness) << "\n"
              << "length: " << result.witness.size() << "\n";
  } else if (result.status == SolveStatus::Unsat) {
    std::cout << "UNSAT\n";
  } else {
    std::cout << "RESOURCE_LIMIT\n" << "detail: " << result.detail << "\n";
  }
  std::cout << "expressions: " << options.expressions.size() << "\n"
            << "alphabet: " << options.alphabet << "\n"
            << "engine: " << engine_name(options.engine) << "\n"
            << "syntax: " << syntax_name(options.syntax) << "\n"
            << "match: " << match_name(options.match_mode) << "\n"
            << "solve-ms: " << std::fixed << std::setprecision(6)
            << solve_milliseconds << "\n"
            << "normalization: "
            << (options.normalization == rewpla::NormalizationMode::Compact
                    ? "compact"
                    : "dnf")
            << "\n"
            << "configurations-discovered: "
            << result.stats.configurations_discovered << "\n"
            << "configurations-expanded: "
            << result.stats.configurations_expanded << "\n"
            << "product-symbol-steps: " << result.stats.product_symbol_steps << "\n"
            << "partial-states-observed: "
            << result.stats.partial_states_observed << "\n"
            << "partial-derivatives-cached: "
            << result.stats.partial_derivatives_cached << "\n"
            << "ast-nodes: " << result.stats.ast_nodes << "\n";
}

void print_text(const CliOptions& options, const EagerSolveResult& result,
                double solve_milliseconds) {
  if (result.status == SolveStatus::Sat) {
    std::cout << "SAT\n"
              << "witness: " << rewpla::display_word(result.witness) << "\n"
              << "length: " << result.witness.size() << "\n";
  } else if (result.status == SolveStatus::Unsat) {
    std::cout << "UNSAT\n";
  } else {
    std::cout << "RESOURCE_LIMIT\n" << "detail: " << result.detail << "\n";
  }
  std::cout << "expressions: " << options.expressions.size() << "\n"
            << "alphabet: " << options.alphabet << "\n"
            << "engine: " << engine_name(options.engine) << "\n"
            << "syntax: " << syntax_name(options.syntax) << "\n"
            << "match: " << match_name(options.match_mode) << "\n"
            << "solve-ms: " << std::fixed << std::setprecision(6)
            << solve_milliseconds << "\n"
            << "normalization: "
            << (options.normalization == rewpla::NormalizationMode::Compact
                    ? "compact"
                    : "dnf")
            << "\ncomponent-dfa-states:";
  for (std::size_t states : result.stats.component_dfa_states) {
    std::cout << ' ' << states;
  }
  std::cout << "\n"
            << "dfa-states-total: " << result.stats.dfa_states_total << "\n"
            << "dfa-transitions: " << result.stats.dfa_transitions << "\n"
            << "product-configurations-discovered: "
            << result.stats.product_configurations_discovered << "\n"
            << "product-configurations-expanded: "
            << result.stats.product_configurations_expanded << "\n"
            << "product-symbol-steps: "
            << result.stats.product_symbol_steps << "\n"
            << "partial-states-observed: "
            << result.stats.partial_states_observed << "\n"
            << "partial-derivatives-cached: "
            << result.stats.partial_derivatives_cached << "\n"
            << "ast-nodes: " << result.stats.ast_nodes << "\n";
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const CliOptions options = parse_cli(argc, argv);
    rewpla::Arena arena(options.max_ast_nodes, options.normalization);
    std::vector<Symbol> alphabet(options.alphabet.begin(), options.alphabet.end());
    std::vector<ExprId> expressions;
    for (std::size_t i = 0; i < options.expressions.size(); ++i) {
      try {
        ExprId expression = arena.zero();
        if (options.syntax == SyntaxMode::Regex) {
          expression = rewpla::RegexFrontend(
              arena, options.expressions[i], alphabet,
              rewpla::RegexFrontendOptions{options.match_mode,
                                            options.max_repeat})
                           .parse();
        } else {
          expression = rewpla::Parser(arena, options.expressions[i]).parse();
          if (options.match_mode == rewpla::RegexMatchMode::Search) {
            expression = search_wrap(arena, expression, alphabet);
          }
        }
        expressions.push_back(expression);
      } catch (const rewpla::ParseError& error) {
        throw std::invalid_argument(
            "expression " + std::to_string(i + 1) +
            ": parse error at character " + std::to_string(error.position()) +
            ": " + error.what());
      }
    }

    const std::unordered_set<Symbol> supplied(options.alphabet.begin(),
                                               options.alphabet.end());
    for (std::size_t i = 0; i < expressions.size(); ++i) {
      for (Symbol atom : arena.atoms(expressions[i])) {
        if (supplied.find(atom) == supplied.end()) {
          throw std::invalid_argument(
              "the supplied alphabet does not contain symbol '" +
              std::string(1, static_cast<char>(atom)) + "' from expression " +
              std::to_string(i + 1));
        }
      }
    }

    rewpla::PartialDerivativeNfa nfa(arena);
    if (options.engine == Engine::Lazy) {
      rewpla::IntersectionSolver solver(
          arena, nfa, std::move(alphabet),
          rewpla::SolveOptions{options.max_configurations});
      const auto start = Clock::now();
      SolveResult result = solver.solve(expressions);
      const auto stop = Clock::now();
      const double solve_milliseconds =
          std::chrono::duration<double, std::milli>(stop - start).count();
      if (options.json) {
        print_json(options, result, solve_milliseconds);
      } else {
        print_text(options, result, solve_milliseconds);
      }
      return result.status == SolveStatus::ResourceLimit ? 3 : 0;
    }
    rewpla::EagerIntersectionSolver solver(
        arena, nfa, std::move(alphabet),
        rewpla::EagerSolveOptions{options.max_dfa_states,
                                  options.max_configurations});
    const auto start = Clock::now();
    EagerSolveResult result = solver.solve(expressions);
    const auto stop = Clock::now();
    const double solve_milliseconds =
        std::chrono::duration<double, std::milli>(stop - start).count();
    if (options.json) {
      print_json(options, result, solve_milliseconds);
    } else {
      print_text(options, result, solve_milliseconds);
    }
    return result.status == SolveStatus::ResourceLimit ? 3 : 0;
  } catch (const rewpla::ResourceLimit& error) {
    std::cerr << "resource limit: " << error.what() << "\n";
    return 3;
  } catch (const std::invalid_argument& error) {
    std::cerr << "error: " << error.what() << "\n\n";
    usage(std::cerr);
    return 2;
  } catch (const std::exception& error) {
    std::cerr << "internal error: " << error.what() << "\n";
    return 1;
  }
}
