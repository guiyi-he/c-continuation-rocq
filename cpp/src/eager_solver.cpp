#include "rewpla/rewpla.hpp"

#include <algorithm>
#include <deque>
#include <numeric>
#include <unordered_map>
#include <unordered_set>

namespace rewpla {
namespace {

std::size_t combine(std::size_t seed, std::size_t value) noexcept {
  return seed ^ (value + static_cast<std::size_t>(0x9e3779b97f4a7c15ULL) +
                 (seed << 6U) + (seed >> 2U));
}

struct StateSetHash {
  std::size_t operator()(const StateSet& states) const noexcept {
    std::size_t seed = states.size();
    for (ExprId state : states) {
      seed = combine(seed, state);
    }
    return seed;
  }
};

struct ProductHash {
  std::size_t operator()(const std::vector<std::size_t>& states) const noexcept {
    std::size_t seed = states.size();
    for (std::size_t state : states) {
      seed = combine(seed, state);
    }
    return seed;
  }
};

struct Dfa {
  std::vector<std::vector<std::size_t>> transitions;
  std::vector<bool> final;
  std::vector<bool> dead;
};

struct ProductEntry {
  std::vector<std::size_t> states;
  std::size_t parent = 0;
  Symbol symbol = 0;
  bool root = false;
};

std::string witness_for(const std::vector<ProductEntry>& entries,
                        std::size_t index) {
  std::string reverse;
  while (!entries[index].root) {
    reverse.push_back(static_cast<char>(entries[index].symbol));
    index = entries[index].parent;
  }
  std::reverse(reverse.begin(), reverse.end());
  return reverse;
}

bool accepting(const std::vector<std::size_t>& product,
               const std::vector<Dfa>& dfas) {
  for (std::size_t i = 0; i < product.size(); ++i) {
    if (!dfas[i].final[product[i]]) {
      return false;
    }
  }
  return true;
}

}  // namespace

EagerIntersectionSolver::EagerIntersectionSolver(
    Arena& arena, PartialDerivativeNfa& nfa, std::vector<Symbol> alphabet,
    EagerSolveOptions options)
    : arena_(arena),
      nfa_(nfa),
      alphabet_(std::move(alphabet)),
      options_(options) {
  if (options_.max_dfa_states == 0 ||
      options_.max_product_configurations == 0) {
    throw std::invalid_argument("eager state limits must be positive");
  }
  if (std::unordered_set<Symbol>(alphabet_.begin(), alphabet_.end()).size() !=
      alphabet_.size()) {
    throw std::invalid_argument("alphabet must not contain duplicates");
  }
}

EagerSolveResult EagerIntersectionSolver::solve(
    const std::vector<ExprId>& expressions) {
  if (expressions.empty()) {
    throw std::invalid_argument("at least one expression is required");
  }

  EagerSolveResult result;
  std::vector<Dfa> dfas;
  dfas.reserve(expressions.size());

  for (ExprId expression : expressions) {
    std::vector<StateSet> subsets{nfa_.initial(expression)};
    std::unordered_map<StateSet, std::size_t, StateSetHash> ids;
    ids.emplace(subsets.front(), 0);
    Dfa dfa;

    for (std::size_t source = 0; source < subsets.size(); ++source) {
      dfa.final.push_back(nfa_.final(subsets[source]));
      dfa.dead.push_back(subsets[source].empty());
      std::vector<std::size_t> row;
      row.reserve(alphabet_.size());
      for (Symbol symbol : alphabet_) {
        StateSet target = nfa_.move(subsets[source], symbol);
        auto found = ids.find(target);
        if (found == ids.end()) {
          if (subsets.size() >= options_.max_dfa_states) {
            result.status = SolveStatus::ResourceLimit;
            result.detail = "eager component DFA state limit reached";
            result.stats.component_dfa_states.push_back(subsets.size());
            result.stats.dfa_states_total = std::accumulate(
                result.stats.component_dfa_states.begin(),
                result.stats.component_dfa_states.end(), std::size_t{0});
            result.stats.dfa_transitions +=
                dfa.transitions.size() * alphabet_.size() + row.size();
            result.stats.partial_derivatives_cached =
                nfa_.cached_transition_count();
            result.stats.partial_states_observed = nfa_.observed_state_count();
            result.stats.ast_nodes = arena_.size();
            return result;
          }
          const std::size_t id = subsets.size();
          subsets.push_back(std::move(target));
          found = ids.emplace(subsets.back(), id).first;
        }
        row.push_back(found->second);
      }
      dfa.transitions.push_back(std::move(row));
    }

    result.stats.component_dfa_states.push_back(subsets.size());
    result.stats.dfa_states_total += subsets.size();
    result.stats.dfa_transitions += subsets.size() * alphabet_.size();
    dfas.push_back(std::move(dfa));
  }

  std::vector<std::size_t> initial(dfas.size(), 0);
  std::vector<ProductEntry> entries;
  entries.push_back(ProductEntry{initial, 0, 0, true});
  std::unordered_map<std::vector<std::size_t>, std::size_t, ProductHash> seen;
  seen.emplace(initial, 0);
  std::deque<std::size_t> todo{0};

  if (accepting(initial, dfas)) {
    result.status = SolveStatus::Sat;
    result.witness = "";
  } else {
    while (!todo.empty()) {
      const std::size_t source_index = todo.front();
      todo.pop_front();
      const std::vector<std::size_t> source = entries[source_index].states;
      ++result.stats.product_configurations_expanded;

      for (std::size_t symbol_index = 0; symbol_index < alphabet_.size();
           ++symbol_index) {
        ++result.stats.product_symbol_steps;
        std::vector<std::size_t> next;
        next.reserve(dfas.size());
        bool dead = false;
        for (std::size_t component = 0; component < dfas.size(); ++component) {
          const std::size_t target =
              dfas[component].transitions[source[component]][symbol_index];
          if (dfas[component].dead[target]) {
            dead = true;
            break;
          }
          next.push_back(target);
        }
        if (dead) {
          continue;
        }

        if (accepting(next, dfas)) {
          result.status = SolveStatus::Sat;
          result.witness = witness_for(entries, source_index);
          result.witness.push_back(
              static_cast<char>(alphabet_[symbol_index]));
          todo.clear();
          break;
        }
        if (seen.find(next) != seen.end()) {
          continue;
        }
        if (entries.size() >= options_.max_product_configurations) {
          result.status = SolveStatus::ResourceLimit;
          result.detail = "eager product configuration limit reached";
          todo.clear();
          break;
        }
        const std::size_t next_index = entries.size();
        entries.push_back(ProductEntry{next, source_index,
                                       alphabet_[symbol_index], false});
        seen.emplace(entries.back().states, next_index);
        todo.push_back(next_index);
      }
      if (result.status == SolveStatus::Sat ||
          result.status == SolveStatus::ResourceLimit) {
        break;
      }
    }
  }

  result.stats.product_configurations_discovered = entries.size();
  result.stats.partial_states_observed = nfa_.observed_state_count();
  result.stats.partial_derivatives_cached = nfa_.cached_transition_count();
  result.stats.ast_nodes = arena_.size();

  if (result.status == SolveStatus::Sat) {
    for (ExprId expression : expressions) {
      if (!nfa_.accepts(expression, result.witness)) {
        throw std::logic_error("internal eager witness replay failed");
      }
    }
  }
  return result;
}

}  // namespace rewpla
