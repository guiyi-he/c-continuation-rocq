#include "rewpla/rewpla.hpp"

#include <algorithm>

namespace rewpla {
namespace {

std::size_t combine(std::size_t seed, std::size_t value) noexcept {
  return seed ^ (value + static_cast<std::size_t>(0x9e3779b97f4a7c15ULL) +
                 (seed << 6U) + (seed >> 2U));
}

}  // namespace

IntersectionSolver::IntersectionSolver(Arena& arena, PartialDerivativeNfa& nfa,
                                       std::vector<Symbol> alphabet,
                                       SolveOptions options)
    : arena_(arena),
      nfa_(nfa),
      alphabet_(std::move(alphabet)),
      options_(options) {
  if (options_.max_configurations == 0) {
    throw std::invalid_argument("max configurations must be positive");
  }
  if (std::unordered_set<Symbol>(alphabet_.begin(), alphabet_.end()).size() !=
      alphabet_.size()) {
    throw std::invalid_argument("alphabet must not contain duplicates");
  }
}

std::size_t IntersectionSolver::ConfigurationHash::operator()(
    const Configuration& configuration) const noexcept {
  std::size_t seed = configuration.components.size();
  for (const StateSet& component : configuration.components) {
    seed = combine(seed, component.size());
    for (ExprId state : component) {
      seed = combine(seed, state);
    }
    seed = combine(seed, static_cast<std::size_t>(0x51ed270bU));
  }
  return seed;
}

bool IntersectionSolver::accepting(
    const Configuration& configuration) const {
  return std::all_of(configuration.components.begin(),
                     configuration.components.end(),
                     [this](const StateSet& component) {
                       return nfa_.final(component);
                     });
}

std::string IntersectionSolver::witness_for(const std::vector<Entry>& entries,
                                            std::size_t index) const {
  std::string reverse;
  while (!entries[index].root) {
    reverse.push_back(static_cast<char>(entries[index].symbol));
    index = entries[index].parent;
  }
  std::reverse(reverse.begin(), reverse.end());
  return reverse;
}

SolveStats IntersectionSolver::stats(std::size_t discovered,
                                     std::size_t expanded,
                                     std::size_t steps) const {
  return SolveStats{discovered, expanded, steps,
                    nfa_.observed_state_count(),
                    nfa_.cached_transition_count(), arena_.size()};
}

SolveResult IntersectionSolver::solve(
    const std::vector<ExprId>& expressions) {
  if (expressions.empty()) {
    throw std::invalid_argument("at least one expression is required");
  }

  Configuration initial;
  for (ExprId expression : expressions) {
    initial.components.push_back(nfa_.initial(expression));
  }

  std::vector<Entry> entries;
  entries.push_back(Entry{initial, 0, 0, true});
  std::unordered_map<Configuration, std::size_t, ConfigurationHash> seen;
  seen.emplace(initial, 0);
  std::deque<std::size_t> todo{0};
  std::size_t expanded = 0;
  std::size_t steps = 0;

  if (accepting(initial)) {
    return SolveResult{SolveStatus::Sat, "", "",
                       stats(entries.size(), expanded, steps)};
  }

  while (!todo.empty()) {
    const std::size_t source_index = todo.front();
    todo.pop_front();
    const Configuration source = entries[source_index].configuration;
    ++expanded;

    for (Symbol symbol : alphabet_) {
      ++steps;
      Configuration next;
      bool dead = false;
      for (const StateSet& component : source.components) {
        StateSet moved = nfa_.move(component, symbol);
        if (moved.empty()) {
          dead = true;
          break;
        }
        next.components.push_back(std::move(moved));
      }
      if (dead) {
        continue;
      }

      // Check before storing: a valid witness must never be hidden by a
      // diagnostic resource limit.
      if (accepting(next)) {
        std::string witness = witness_for(entries, source_index);
        witness.push_back(static_cast<char>(symbol));
        for (ExprId expression : expressions) {
          if (!nfa_.accepts(expression, witness)) {
            throw std::logic_error("internal witness replay failed");
          }
        }
        return SolveResult{SolveStatus::Sat, std::move(witness), "",
                           stats(entries.size(), expanded, steps)};
      }

      if (seen.find(next) != seen.end()) {
        continue;
      }
      if (entries.size() >= options_.max_configurations) {
        return SolveResult{
            SolveStatus::ResourceLimit,
            "",
            "on-the-fly product configuration limit reached",
            stats(entries.size(), expanded, steps),
        };
      }
      const std::size_t next_index = entries.size();
      entries.push_back(Entry{next, source_index, symbol, false});
      seen.emplace(entries.back().configuration, next_index);
      todo.push_back(next_index);
    }
  }

  return SolveResult{SolveStatus::Unsat, "", "",
                     stats(entries.size(), expanded, steps)};
}

}  // namespace rewpla
