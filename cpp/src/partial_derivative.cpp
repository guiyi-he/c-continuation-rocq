#include "rewpla/rewpla.hpp"

#include <algorithm>

namespace rewpla {
namespace {

std::size_t mix(std::size_t seed, std::size_t value) noexcept {
  return seed ^ (value + static_cast<std::size_t>(0x9e3779b97f4a7c15ULL) +
                 (seed << 6U) + (seed >> 2U));
}

}  // namespace

std::size_t PartialDerivativeNfa::TransitionKeyHash::operator()(
    const TransitionKey& key) const noexcept {
  return mix(key.expression, key.symbol);
}

void PartialDerivativeNfa::canonicalize(StateSet& states) {
  std::sort(states.begin(), states.end());
  states.erase(std::unique(states.begin(), states.end()), states.end());
}

void PartialDerivativeNfa::add(StateSet& target, ExprId expression,
                               const Arena& arena) {
  const StateSet terms = arena.top_terms(expression);
  target.insert(target.end(), terms.begin(), terms.end());
}

void PartialDerivativeNfa::add_all(StateSet& target, const StateSet& source) {
  target.insert(target.end(), source.begin(), source.end());
}

void PartialDerivativeNfa::add_concat_left(StateSet& target,
                                           const StateSet& left,
                                           ExprId right) {
  for (ExprId expression : left) {
    add(target, arena_.concat({expression, right}), arena_);
  }
}

void PartialDerivativeNfa::add_concat_product(StateSet& target,
                                              const StateSet& left,
                                              const StateSet& right) {
  for (ExprId x : left) {
    for (ExprId y : right) {
      add(target, arena_.concat({x, y}), arena_);
    }
  }
}

StateSet PartialDerivativeNfa::initial(ExprId expression) {
  StateSet states = arena_.top_terms(expression);
  observed_states_.insert(states.begin(), states.end());
  return states;
}

const DerivativePair& PartialDerivativeNfa::derivative(ExprId expression,
                                                       Symbol symbol) {
  observed_states_.insert(expression);
  const TransitionKey key{expression, symbol};
  if (const auto found = memo_.find(key); found != memo_.end()) {
    return found->second;
  }

  // This is the set-valued (Antimirov) lifting of
  // LookaheadDerivatives.symbol_derivative_core / paper Eq. (20).  The union
  // of each returned set denotes exactly the corresponding Rocq component.
  const Node snapshot = arena_.node(expression);
  DerivativePair result;
  switch (snapshot.kind) {
    case Kind::Zero:
    case Kind::Epsilon:
      break;

    case Kind::Atom:
      if (snapshot.atom == symbol) {
        result.main.push_back(arena_.epsilon());
      }
      break;

    case Kind::Union:
      for (ExprId child : snapshot.children) {
        const DerivativePair& d = derivative(child, symbol);
        add_all(result.main, d.main);
        add_all(result.context, d.context);
      }
      break;

    case Kind::Concat: {
      // P9 lets the canonical n-ary word be read as r.s with r its first
      // factor and s the right-associated remaining word.
      const ExprId r = snapshot.children.front();
      std::vector<ExprId> suffix(snapshot.children.begin() + 1,
                                 snapshot.children.end());
      const ExprId s = arena_.concat(std::move(suffix));
      const DerivativePair dr = derivative(r, symbol);
      const DerivativePair ds = derivative(s, symbol);

      // main: r_m s + r_c s_m + lambda(r) s_m
      add_concat_left(result.main, dr.main, s);
      add_concat_product(result.main, dr.context, ds.main);
      if (arena_.nullable(r)) {
        add_all(result.main, ds.main);
      }

      // context: r_c s_c + lambda(s) r_c + lambda(r) s_c
      add_concat_product(result.context, dr.context, ds.context);
      if (arena_.nullable(s)) {
        add_all(result.context, dr.context);
      }
      if (arena_.nullable(r)) {
        add_all(result.context, ds.context);
      }
      break;
    }

    case Kind::Star: {
      const ExprId r = snapshot.children.front();
      const DerivativePair dr = derivative(r, symbol);
      // main: r_m r* + r_c r_m r*; context: r_c
      add_concat_left(result.main, dr.main, expression);
      for (ExprId context : dr.context) {
        for (ExprId main : dr.main) {
          add(result.main, arena_.concat({context, main, expression}), arena_);
        }
      }
      add_all(result.context, dr.context);
      break;
    }

    case Kind::Lookahead: {
      const DerivativePair inner =
          derivative(snapshot.children.front(), symbol);
      StateSet merged = inner.main;
      add_all(merged, inner.context);
      canonicalize(merged);
      std::vector<ExprId> alternatives(merged.begin(), merged.end());
      add(result.context, arena_.lookahead(arena_.unite(std::move(alternatives))),
          arena_);
      break;
    }
  }

  canonicalize(result.main);
  canonicalize(result.context);
  return memo_.emplace(key, std::move(result)).first->second;
}

StateSet PartialDerivativeNfa::move(const StateSet& states, Symbol symbol) {
  StateSet result;
  for (ExprId state : states) {
    const DerivativePair& d = derivative(state, symbol);
    add_all(result, d.main);
    add_all(result, d.context);
  }
  canonicalize(result);
  observed_states_.insert(result.begin(), result.end());
  return result;
}

bool PartialDerivativeNfa::final(const StateSet& states) const {
  return std::any_of(states.begin(), states.end(),
                     [this](ExprId state) { return arena_.nullable(state); });
}

bool PartialDerivativeNfa::accepts(ExprId expression, std::string_view word) {
  StateSet states = initial(expression);
  for (unsigned char symbol : word) {
    states = move(states, symbol);
    if (states.empty()) {
      return false;
    }
  }
  return final(states);
}

}  // namespace rewpla
