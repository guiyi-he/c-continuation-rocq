#include "rewpla/rewpla.hpp"

#include <algorithm>
#include <charconv>
#include <chrono>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {

using Clock = std::chrono::steady_clock;

struct Options {
  std::size_t min_n = 0;
  std::size_t max_n = 16;
  std::size_t warmups = 0;
  std::size_t repetitions = 1;
  std::size_t max_dfa_states = 1'000'000;
  std::size_t max_configurations = 1'000'000;
  std::size_t max_ast_nodes = 1'000'000;
  rewpla::NormalizationMode normalization =
      rewpla::NormalizationMode::Compact;
};

template <typename Result>
struct Timed {
  Result result;
  double milliseconds = 0.0;
};

std::size_t parse_size(const std::string& option, const std::string& text,
                       bool allow_zero = false) {
  std::size_t value = 0;
  const char* begin = text.data();
  const char* end = begin + text.size();
  const auto parsed = std::from_chars(begin, end, value);
  if (parsed.ec != std::errc{} || parsed.ptr != end ||
      (!allow_zero && value == 0)) {
    throw std::invalid_argument(option + " requires " +
                                (allow_zero ? "a nonnegative" : "a positive") +
                                " integer");
  }
  return value;
}

void usage(std::ostream& out) {
  out <<
      "Usage: rewpla-distance-bench [OPTIONS]\n\n"
      "Compare lazy intersection with eager component determinization on\n"
      "  distance_n = (a+b)* a LA((a+b)^n b)\n"
      "  alternating = (ab)*\n"
      "Their intersection is nonempty exactly when n is even.\n\n"
      "Options:\n"
      "  --min-n N                  first n (default 0)\n"
      "  --max-n N                  last n (default 16)\n"
      "  --warmup N                 unmeasured runs per mode (default 0)\n"
      "  --repeat N                 runs per mode; median time is reported\n"
      "  --normalization MODE       compact (default) or dnf\n"
      "  --max-dfa-states N         per-component eager limit (default 1000000)\n"
      "  --max-configurations N     product limit for both modes (default 1000000)\n"
      "  --max-ast-nodes N          expression arena limit (default 1000000)\n"
      "  -h, --help                 show this help\n";
}

Options parse_cli(int argc, char** argv) {
  Options options;
  for (int i = 1; i < argc; ++i) {
    const std::string argument = argv[i];
    if (argument == "-h" || argument == "--help") {
      usage(std::cout);
      std::exit(0);
    }
    if (argument == "--normalization") {
      if (++i >= argc) {
        throw std::invalid_argument(argument + " requires a value");
      }
      const std::string value = argv[i];
      if (value == "compact") {
        options.normalization = rewpla::NormalizationMode::Compact;
      } else if (value == "dnf") {
        options.normalization = rewpla::NormalizationMode::DistributiveDnf;
      } else {
        throw std::invalid_argument(
            "--normalization must be 'compact' or 'dnf'");
      }
      continue;
    }
    if (++i >= argc) {
      throw std::invalid_argument(argument + " requires a value");
    }
    const std::string value = argv[i];
    if (argument == "--min-n") {
      options.min_n = parse_size(argument, value, true);
    } else if (argument == "--max-n") {
      options.max_n = parse_size(argument, value, true);
    } else if (argument == "--repeat") {
      options.repetitions = parse_size(argument, value);
    } else if (argument == "--warmup") {
      options.warmups = parse_size(argument, value, true);
    } else if (argument == "--max-dfa-states") {
      options.max_dfa_states = parse_size(argument, value);
    } else if (argument == "--max-configurations") {
      options.max_configurations = parse_size(argument, value);
    } else if (argument == "--max-ast-nodes") {
      options.max_ast_nodes = parse_size(argument, value);
    } else {
      throw std::invalid_argument("unknown option: " + argument);
    }
  }
  if (options.min_n > options.max_n) {
    throw std::invalid_argument("--min-n must not exceed --max-n");
  }
  return options;
}

std::string distance_expression(std::size_t n) {
  std::string constraint;
  for (std::size_t i = 0; i < n; ++i) {
    constraint += "(a+b)";
  }
  constraint += 'b';
  return "(a+b)*aLA(" + constraint + ')';
}

const char* status_name(rewpla::SolveStatus status) {
  switch (status) {
    case rewpla::SolveStatus::Sat:
      return "sat";
    case rewpla::SolveStatus::Unsat:
      return "unsat";
    case rewpla::SolveStatus::ResourceLimit:
      return "resource_limit";
  }
  return "internal_error";
}

Timed<rewpla::SolveResult> run_lazy(std::size_t n, const Options& options) {
  rewpla::Arena arena(options.max_ast_nodes, options.normalization);
  const rewpla::ExprId distance =
      rewpla::Parser(arena, distance_expression(n)).parse();
  const rewpla::ExprId alternating =
      rewpla::Parser(arena, "(ab)*").parse();
  rewpla::PartialDerivativeNfa nfa(arena);
  rewpla::IntersectionSolver solver(
      arena, nfa, {'a', 'b'},
      rewpla::SolveOptions{options.max_configurations});
  const auto start = Clock::now();
  rewpla::SolveResult result = solver.solve({distance, alternating});
  const auto stop = Clock::now();
  return {std::move(result),
          std::chrono::duration<double, std::milli>(stop - start).count()};
}

Timed<rewpla::EagerSolveResult> run_eager(std::size_t n,
                                         const Options& options) {
  rewpla::Arena arena(options.max_ast_nodes, options.normalization);
  const rewpla::ExprId distance =
      rewpla::Parser(arena, distance_expression(n)).parse();
  const rewpla::ExprId alternating =
      rewpla::Parser(arena, "(ab)*").parse();
  rewpla::PartialDerivativeNfa nfa(arena);
  rewpla::EagerIntersectionSolver solver(
      arena, nfa, {'a', 'b'},
      rewpla::EagerSolveOptions{options.max_dfa_states,
                                options.max_configurations});
  const auto start = Clock::now();
  rewpla::EagerSolveResult result = solver.solve({distance, alternating});
  const auto stop = Clock::now();
  return {std::move(result),
          std::chrono::duration<double, std::milli>(stop - start).count()};
}

double median(std::vector<double> values) {
  std::sort(values.begin(), values.end());
  const std::size_t middle = values.size() / 2;
  if (values.size() % 2 == 1) {
    return values[middle];
  }
  return (values[middle - 1] + values[middle]) / 2.0;
}

template <typename Runner>
auto repeated(Runner runner, std::size_t warmups, std::size_t repetitions) {
  for (std::size_t i = 0; i < warmups; ++i) {
    static_cast<void>(runner());
  }
  auto sample = runner();
  std::vector<double> times{sample.milliseconds};
  for (std::size_t i = 1; i < repetitions; ++i) {
    auto next = runner();
    times.push_back(next.milliseconds);
    sample.result = std::move(next.result);
  }
  sample.milliseconds = median(std::move(times));
  return sample;
}

void validate(std::size_t n, const rewpla::SolveResult& lazy,
              const rewpla::EagerSolveResult& eager) {
  const rewpla::SolveStatus expected =
      n % 2 == 0 ? rewpla::SolveStatus::Sat : rewpla::SolveStatus::Unsat;
  if (lazy.status != expected) {
    throw std::runtime_error("lazy result violates distance-family parity");
  }
  if (eager.status != rewpla::SolveStatus::ResourceLimit &&
      (eager.status != lazy.status || eager.witness != lazy.witness)) {
    throw std::runtime_error("lazy and eager results disagree");
  }
  if (lazy.status == rewpla::SolveStatus::Sat &&
      lazy.witness.size() != n + 2) {
    throw std::runtime_error("lazy witness is not shortest for distance family");
  }
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const Options options = parse_cli(argc, argv);
    std::cout
        << "normalization,warmup_runs,measured_runs,max_dfa_states,"
           "max_configurations,max_ast_nodes,n,expected,lazy_status,lazy_ms,lazy_configs,lazy_steps,"
           "lazy_partial_states,lazy_derivatives,lazy_ast_nodes,"
           "lazy_witness_length,eager_status,"
           "eager_ms,eager_distance_states,eager_alternating_states,"
           "eager_dfa_states_total,eager_dfa_transitions,eager_product_configs,"
           "eager_product_steps,eager_partial_states,eager_derivatives,"
           "eager_ast_nodes\n";
    std::cout << std::fixed << std::setprecision(3);

    for (std::size_t n = options.min_n;; ++n) {
      const auto lazy = repeated(
          [&] { return run_lazy(n, options); }, options.warmups,
          options.repetitions);
      const auto eager = repeated(
          [&] { return run_eager(n, options); }, options.warmups,
          options.repetitions);
      validate(n, lazy.result, eager.result);

      const auto& ls = lazy.result.stats;
      const auto& es = eager.result.stats;
      const std::size_t distance_states =
          es.component_dfa_states.empty() ? 0 : es.component_dfa_states[0];
      const std::size_t alternating_states =
          es.component_dfa_states.size() < 2 ? 0 : es.component_dfa_states[1];
      std::cout << (options.normalization == rewpla::NormalizationMode::Compact
                        ? "compact"
                        : "dnf")
                << ',' << options.warmups << ',' << options.repetitions << ','
                << options.max_dfa_states << ',' << options.max_configurations
                << ',' << options.max_ast_nodes << ','
                << n << ',' << (n % 2 == 0 ? "sat" : "unsat") << ','
                << status_name(lazy.result.status) << ',' << lazy.milliseconds
                << ',' << ls.configurations_discovered << ','
                << ls.product_symbol_steps << ','
                << ls.partial_states_observed << ','
                << ls.partial_derivatives_cached << ',' << ls.ast_nodes << ','
                << (lazy.result.status == rewpla::SolveStatus::Sat
                        ? lazy.result.witness.size()
                        : 0)
                << ',' << status_name(eager.result.status) << ','
                << eager.milliseconds << ',' << distance_states << ','
                << alternating_states << ',' << es.dfa_states_total << ','
                << es.dfa_transitions << ','
                << es.product_configurations_discovered << ','
                << es.product_symbol_steps << ','
                << es.partial_states_observed << ','
                << es.partial_derivatives_cached << ',' << es.ast_nodes << '\n';

      if (n == options.max_n) {
        break;
      }
    }
    return 0;
  } catch (const rewpla::ResourceLimit& error) {
    std::cerr << "resource limit: " << error.what() << '\n';
    return 3;
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << "\n\n";
    usage(std::cerr);
    return 2;
  }
}
