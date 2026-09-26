#include "rewpla/rewpla.hpp"

#include <charconv>
#include <chrono>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

namespace {

using rewpla::ExprId;
using rewpla::SolveStatus;
using rewpla::Symbol;
using Clock = std::chrono::steady_clock;

struct Options {
  std::string alphabet;
  std::string lookahead;
  std::string left;
  std::string right;
  std::string reject;
  std::size_t minimum_repetitions = 2;
  std::size_t maximum_repetitions = 12;
  std::size_t step = 2;
  std::size_t max_configurations = 1'000'000;
  std::size_t max_ast_nodes = 1'000'000;
  std::size_t max_candidate_length = 1'000'000;
  bool json = false;
};

void usage(std::ostream& out) {
  out <<
      "Usage: rewpla-redos --alphabet SYMBOLS --lookahead REGEX "
      "--left REGEX --right REGEX --reject TEXT [OPTIONS]\n"
      "\n"
      "Generate branch-overlap ReDoS candidates for the real-regex pattern\n"
      "  ^(?=LOOKAHEAD)(?:(?:LEFT)|(?:RIGHT))+$\n"
      "\n"
      "The solver first finds a shortest nonempty word in LEFT intersect\n"
      "RIGHT. Repeating that pump word gives at least 2^n syntactic branch\n"
      "choices before REJECT makes the consuming body fail. This is a static\n"
      "candidate certificate, not a timing or engine-complexity proof.\n"
      "\n"
      "Options:\n"
      "  --alphabet SYMBOLS          finite alphabet and witness order\n"
      "  --lookahead REGEX           positive-lookahead body over the subject\n"
      "  --left REGEX                first ordinary overlapping branch\n"
      "  --right REGEX               second ordinary overlapping branch\n"
      "  --reject TEXT               literal failing suffix\n"
      "  --min-repetitions N         first pump count (default 2)\n"
      "  --max-repetitions N         last pump count (default 12)\n"
      "  --step N                    pump-count increment (default 2)\n"
      "  --max-configurations N      overlap-product limit (default 1000000)\n"
      "  --max-ast-nodes N           expression arena limit (default 1000000)\n"
      "  --max-candidate-length N    generated subject limit (default 1000000)\n"
      "  --json                      emit one JSON object\n"
      "  -h, --help                  show this help\n"
      "  --version                   show the experimental tool version\n";
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

std::string take_value(int argc, char** argv, int& index,
                       const std::string& option) {
  if (++index >= argc) throw std::invalid_argument(option + " requires a value");
  return argv[index];
}

Options parse_cli(int argc, char** argv) {
  Options options;
  for (int i = 1; i < argc; ++i) {
    const std::string argument = argv[i];
    if (argument == "-h" || argument == "--help") {
      usage(std::cout);
      std::exit(0);
    }
    if (argument == "--version") {
      std::cout << "rewpla-redos 0.5.0-experimental\n";
      std::exit(0);
    } else if (argument == "--json") {
      options.json = true;
    } else if (argument == "--alphabet") {
      options.alphabet = take_value(argc, argv, i, argument);
    } else if (argument == "--lookahead") {
      options.lookahead = take_value(argc, argv, i, argument);
    } else if (argument == "--left") {
      options.left = take_value(argc, argv, i, argument);
    } else if (argument == "--right") {
      options.right = take_value(argc, argv, i, argument);
    } else if (argument == "--reject") {
      options.reject = take_value(argc, argv, i, argument);
    } else if (argument == "--min-repetitions") {
      options.minimum_repetitions = parse_positive_size(
          argument, take_value(argc, argv, i, argument));
    } else if (argument == "--max-repetitions") {
      options.maximum_repetitions = parse_positive_size(
          argument, take_value(argc, argv, i, argument));
    } else if (argument == "--step") {
      options.step = parse_positive_size(
          argument, take_value(argc, argv, i, argument));
    } else if (argument == "--max-configurations") {
      options.max_configurations = parse_positive_size(
          argument, take_value(argc, argv, i, argument));
    } else if (argument == "--max-ast-nodes") {
      options.max_ast_nodes = parse_positive_size(
          argument, take_value(argc, argv, i, argument));
    } else if (argument == "--max-candidate-length") {
      options.max_candidate_length = parse_positive_size(
          argument, take_value(argc, argv, i, argument));
    } else {
      throw std::invalid_argument("unknown option: " + argument);
    }
  }

  if (options.alphabet.empty()) throw std::invalid_argument("--alphabet is required");
  if (options.lookahead.empty()) throw std::invalid_argument("--lookahead is required");
  if (options.left.empty()) throw std::invalid_argument("--left is required");
  if (options.right.empty()) throw std::invalid_argument("--right is required");
  if (options.reject.empty()) throw std::invalid_argument("--reject is required");
  if (options.maximum_repetitions < options.minimum_repetitions) {
    throw std::invalid_argument(
        "--max-repetitions must be at least --min-repetitions");
  }
  std::unordered_set<unsigned char> alphabet;
  for (unsigned char symbol : options.alphabet) {
    if (!alphabet.insert(symbol).second) {
      throw std::invalid_argument("--alphabet must not contain duplicate symbols");
    }
  }
  for (unsigned char symbol : options.reject) {
    if (alphabet.find(symbol) == alphabet.end()) {
      throw std::invalid_argument("--reject contains a symbol outside --alphabet");
    }
  }
  return options;
}

ExprId parse_regex(rewpla::Arena& arena, const std::string& source,
                   const std::vector<Symbol>& alphabet) {
  return rewpla::RegexFrontend(
             arena, source, alphabet,
             rewpla::RegexFrontendOptions{
                 rewpla::RegexMatchMode::Projected, 10'000})
      .parse();
}

bool contains_lookahead(const rewpla::Arena& arena, ExprId expression) {
  const rewpla::Node& node = arena.node(expression);
  if (node.kind == rewpla::Kind::Lookahead) return true;
  for (ExprId child : node.children) {
    if (contains_lookahead(arena, child)) return true;
  }
  return false;
}

void validate_ordinary(const rewpla::Arena& arena, ExprId expression,
                       const std::string& role) {
  if (contains_lookahead(arena, expression)) {
    throw std::invalid_argument(
        role + " must be an ordinary regex; the generated outer guard supplies "
               "the positive lookahead");
  }
}

void validate_alphabet(const rewpla::Arena& arena, ExprId expression,
                       const std::unordered_set<Symbol>& alphabet,
                       const std::string& role) {
  for (Symbol atom : arena.atoms(expression)) {
    if (alphabet.find(atom) == alphabet.end()) {
      throw std::invalid_argument(role + " contains a symbol outside --alphabet");
    }
  }
}

struct Candidate {
  std::size_t repetitions = 0;
  std::string subject;
  bool guard_accepts = false;
  bool body_rejects = false;
  bool projected_target_accepts = false;

  [[nodiscard]] bool certified() const noexcept {
    // Under standard zero-width lookahead semantics, the anchored target
    // rejects whenever its consuming body rejects.  The separate guard check
    // establishes that the positive assertion itself succeeds on the subject.
    return guard_accepts && body_rejects;
  }
};

void print_no_overlap_json(const rewpla::SolveResult& overlap) {
  std::cout << "{\"status\":\"no_overlap\","
            << "\"method\":\"branch_overlap\","
            << "\"configurations_discovered\":"
            << overlap.stats.configurations_discovered << "}\n";
}

void print_resource_json(const rewpla::SolveResult& overlap) {
  std::cout << "{\"status\":\"resource_limit\","
            << "\"method\":\"branch_overlap\","
            << "\"detail\":\"" << rewpla::json_escape(overlap.detail)
            << "\"}\n";
}

void print_json(const Options& options, const std::string& target,
                const std::string& pump, const rewpla::SolveResult& overlap,
                double overlap_solve_ms, double certificate_ms,
                const std::vector<Candidate>& candidates) {
  std::cout << "{\"status\":\"candidate\","
            << "\"method\":\"branch_overlap\","
            << "\"claim_scope\":\"static candidate certificate; not an "
               "engine timing proof\","
            << "\"target_pattern\":\"" << rewpla::json_escape(target)
            << "\",\"alphabet\":\"" << rewpla::json_escape(options.alphabet)
            << "\",\"lookahead\":\""
            << rewpla::json_escape(options.lookahead)
            << "\",\"left\":\"" << rewpla::json_escape(options.left)
            << "\",\"right\":\"" << rewpla::json_escape(options.right)
            << "\",\"reject\":\"" << rewpla::json_escape(options.reject)
            << "\",\"pump\":\"" << rewpla::json_escape(pump)
            << "\",\"pump_length\":" << pump.size()
            << ",\"overlap_solve_ms\":" << overlap_solve_ms
            << ",\"certificate_ms\":" << certificate_ms
            << ",\"overlap_stats\":{\"configurations_discovered\":"
            << overlap.stats.configurations_discovered
            << ",\"configurations_expanded\":"
            << overlap.stats.configurations_expanded
            << ",\"partial_states_observed\":"
            << overlap.stats.partial_states_observed
            << ",\"partial_derivatives_cached\":"
            << overlap.stats.partial_derivatives_cached
            << ",\"ast_nodes\":" << overlap.stats.ast_nodes
            << "},\"candidates\":[";
  for (std::size_t i = 0; i < candidates.size(); ++i) {
    if (i != 0) std::cout << ',';
    const Candidate& candidate = candidates[i];
    std::cout << "{\"repetitions\":" << candidate.repetitions
              << ",\"subject\":\""
              << rewpla::json_escape(candidate.subject)
              << "\",\"length\":" << candidate.subject.size()
              << ",\"ambiguity_log2_lower_bound\":"
              << candidate.repetitions
              << ",\"guard_accepts\":"
              << (candidate.guard_accepts ? "true" : "false")
              << ",\"body_rejects\":"
              << (candidate.body_rejects ? "true" : "false")
              << ",\"host_rejection_inferred\":"
              << (candidate.body_rejects ? "true" : "false")
              << ",\"projected_target_accepts\":"
              << (candidate.projected_target_accepts ? "true" : "false")
              << ",\"certified\":"
              << (candidate.certified() ? "true" : "false") << '}';
  }
  std::cout << "]}\n";
}

void print_text(const Options& options, const std::string& target,
                const std::string& pump, const rewpla::SolveResult& overlap,
                double overlap_solve_ms, double certificate_ms,
                const std::vector<Candidate>& candidates) {
  std::cout << "CANDIDATE\n"
            << "method: branch-overlap\n"
            << "scope: static candidate certificate; not an engine timing proof\n"
            << "target: " << target << "\n"
            << "pump: " << rewpla::display_word(pump) << "\n"
            << "pump-length: " << pump.size() << "\n"
            << "overlap-configurations: "
            << overlap.stats.configurations_discovered << "\n"
            << "overlap-solve-ms: " << overlap_solve_ms << "\n"
            << "certificate-ms: " << certificate_ms << "\n";
  for (const Candidate& candidate : candidates) {
    std::cout << "n=" << candidate.repetitions
              << " length=" << candidate.subject.size()
              << " ambiguity>=2^" << candidate.repetitions
              << " guard=" << (candidate.guard_accepts ? "yes" : "no")
              << " body-rejects=" << (candidate.body_rejects ? "yes" : "no")
              << " projected-target="
              << (candidate.projected_target_accepts ? "accepts" : "rejects")
              << " certified=" << (candidate.certified() ? "yes" : "no")
              << " subject=" << rewpla::display_word(candidate.subject) << '\n';
  }
  static_cast<void>(options);
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const Options options = parse_cli(argc, argv);
    const std::vector<Symbol> alphabet(options.alphabet.begin(),
                                       options.alphabet.end());
    const std::unordered_set<Symbol> alphabet_set(alphabet.begin(),
                                                   alphabet.end());
    rewpla::Arena arena(options.max_ast_nodes);
    const ExprId left = parse_regex(arena, options.left, alphabet);
    const ExprId right = parse_regex(arena, options.right, alphabet);
    const ExprId lookahead_body =
        parse_regex(arena, options.lookahead, alphabet);
    validate_ordinary(arena, left, "--left");
    validate_ordinary(arena, right, "--right");
    validate_ordinary(arena, lookahead_body, "--lookahead");
    validate_alphabet(arena, left, alphabet_set, "--left");
    validate_alphabet(arena, right, alphabet_set, "--right");
    validate_alphabet(arena, lookahead_body, alphabet_set, "--lookahead");
    const ExprId nonempty = parse_regex(arena, ".+", alphabet);
    rewpla::PartialDerivativeNfa nfa(arena);
    rewpla::IntersectionSolver solver(
        arena, nfa, alphabet,
        rewpla::SolveOptions{options.max_configurations});
    const auto overlap_start = Clock::now();
    const rewpla::SolveResult overlap = solver.solve({left, right, nonempty});
    const auto overlap_stop = Clock::now();
    const double overlap_solve_ms =
        std::chrono::duration<double, std::milli>(overlap_stop - overlap_start)
            .count();
    if (overlap.status == SolveStatus::ResourceLimit) {
      if (options.json) {
        print_resource_json(overlap);
      } else {
        std::cout << "RESOURCE_LIMIT\ndetail: " << overlap.detail << '\n';
      }
      return 3;
    }
    if (overlap.status == SolveStatus::Unsat) {
      if (options.json) {
        print_no_overlap_json(overlap);
      } else {
        std::cout << "NO_OVERLAP\n";
      }
      return 0;
    }

    const std::string branch = "(?:(?:" + options.left + ")|(?:" +
                               options.right + "))";
    const std::string guard_pattern =
        "^(?=(?:" + options.lookahead + ")).*$";
    const std::string body_pattern = "^" + branch + "+$";
    const std::string target_pattern =
        "^(?=(?:" + options.lookahead + "))" + branch + "+$";
    const ExprId guard = parse_regex(arena, guard_pattern, alphabet);
    const ExprId body = parse_regex(arena, body_pattern, alphabet);
    const ExprId target = parse_regex(arena, target_pattern, alphabet);

    const auto certificate_start = Clock::now();
    std::vector<Candidate> candidates;
    for (std::size_t repetitions = options.minimum_repetitions;;) {
      if (options.reject.size() > options.max_candidate_length ||
          overlap.witness.size() >
          (options.max_candidate_length - options.reject.size()) /
              repetitions) {
        throw rewpla::ResourceLimit("generated subject exceeds candidate limit");
      }
      Candidate candidate;
      candidate.repetitions = repetitions;
      candidate.subject.reserve(overlap.witness.size() * repetitions +
                                options.reject.size());
      for (std::size_t i = 0; i < repetitions; ++i) {
        candidate.subject += overlap.witness;
      }
      candidate.subject += options.reject;
      candidate.guard_accepts = nfa.accepts(guard, candidate.subject);
      candidate.body_rejects = !nfa.accepts(body, candidate.subject);
      // Projected REwPLA witnesses include the continuation required by a
      // lookahead.  Consequently this value can be true even though a host
      // regex rejects because its zero-width assertion consumes nothing.
      candidate.projected_target_accepts = nfa.accepts(target, candidate.subject);
      candidates.push_back(std::move(candidate));

      if (repetitions >= options.maximum_repetitions ||
          options.step > options.maximum_repetitions - repetitions) {
        break;
      }
      repetitions += options.step;
    }
    const auto certificate_stop = Clock::now();
    const double certificate_ms =
        std::chrono::duration<double, std::milli>(certificate_stop -
                                                  certificate_start)
            .count();

    if (options.json) {
      print_json(options, target_pattern, overlap.witness, overlap,
                 overlap_solve_ms, certificate_ms, candidates);
    } else {
      print_text(options, target_pattern, overlap.witness, overlap,
                 overlap_solve_ms, certificate_ms, candidates);
    }
    return 0;
  } catch (const rewpla::ParseError& error) {
    std::cerr << "error: parse error at character " << error.position() << ": "
              << error.what() << "\n\n";
    usage(std::cerr);
    return 2;
  } catch (const rewpla::ResourceLimit& error) {
    std::cerr << "resource limit: " << error.what() << '\n';
    return 3;
  } catch (const std::invalid_argument& error) {
    std::cerr << "error: " << error.what() << "\n\n";
    usage(std::cerr);
    return 2;
  } catch (const std::exception& error) {
    std::cerr << "internal error: " << error.what() << '\n';
    return 1;
  }
}
