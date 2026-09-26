#include "rewpla/rewpla.hpp"

#include <algorithm>
#include <limits>
#include <sstream>

namespace rewpla {
namespace {

std::size_t hash_combine(std::size_t seed, std::size_t value) noexcept {
  // boost::hash_combine, with a 64-bit constant; truncation on 32-bit is safe.
  return seed ^ (value + static_cast<std::size_t>(0x9e3779b97f4a7c15ULL) +
                 (seed << 6U) + (seed >> 2U));
}

int precedence(Kind kind) noexcept {
  switch (kind) {
    case Kind::Union:
      return 1;
    case Kind::Concat:
      return 2;
    case Kind::Star:
      return 3;
    default:
      return 4;
  }
}

}  // namespace

ParseError::ParseError(std::size_t position, const std::string& message)
    : std::runtime_error(message), position_(position) {}

bool Arena::Key::operator==(const Key& other) const noexcept {
  return kind == other.kind && atom == other.atom && children == other.children;
}

std::size_t Arena::KeyHash::operator()(const Key& key) const noexcept {
  std::size_t seed = static_cast<std::size_t>(key.kind);
  seed = hash_combine(seed, key.atom);
  for (ExprId child : key.children) {
    seed = hash_combine(seed, child);
  }
  return seed;
}

Arena::Arena(std::size_t max_nodes, NormalizationMode normalization)
    : max_nodes_(max_nodes), normalization_(normalization) {
  if (max_nodes_ < 2) {
    throw std::invalid_argument("max AST nodes must be at least 2");
  }
  zero_ = intern(Key{Kind::Zero, 0, {}});
  epsilon_ = intern(Key{Kind::Epsilon, 0, {}});
}

const Node& Arena::node(ExprId id) const {
  if (id >= nodes_.size()) {
    throw std::out_of_range("invalid expression id");
  }
  return nodes_[id];
}

ExprId Arena::intern(Key key) {
  const auto found = interner_.find(key);
  if (found != interner_.end()) {
    return found->second;
  }
  if (nodes_.size() >= max_nodes_ ||
      nodes_.size() >= static_cast<std::size_t>(std::numeric_limits<ExprId>::max())) {
    throw ResourceLimit("AST node limit reached");
  }
  const ExprId id = static_cast<ExprId>(nodes_.size());
  Node value{key.kind, key.atom, key.children};
  interner_.emplace(std::move(key), id);
  nodes_.push_back(std::move(value));
  nullable_cache_.push_back(-1);
  constraint_cache_.push_back(-1);
  return id;
}

ExprId Arena::atom(Symbol symbol) {
  return intern(Key{Kind::Atom, symbol, {}});
}

ExprId Arena::unite(std::vector<ExprId> terms) {
  std::vector<ExprId> flat;
  for (ExprId term : terms) {
    const Node& n = node(term);
    if (n.kind == Kind::Zero) {
      continue;
    }
    if (n.kind == Kind::Union) {
      flat.insert(flat.end(), n.children.begin(), n.children.end());
    } else {
      flat.push_back(term);
    }
  }
  std::sort(flat.begin(), flat.end());
  flat.erase(std::unique(flat.begin(), flat.end()), flat.end());
  if (flat.empty()) {
    return zero_;
  }
  if (flat.size() == 1) {
    return flat.front();
  }
  return intern(Key{Kind::Union, 0, std::move(flat)});
}

void Arena::append_factor(std::vector<ExprId>& word, ExprId factor) const {
  const Node& n = node(factor);
  if (n.kind == Kind::Epsilon) {
    return;
  }
  if (n.kind == Kind::Concat) {
    for (ExprId child : n.children) {
      append_factor(word, child);
    }
    return;
  }
  word.push_back(factor);
}

std::optional<std::vector<ExprId>> Arena::normalize_word(
    std::vector<ExprId> word) const {
  std::vector<ExprId> flat;
  for (ExprId factor : word) {
    if (node(factor).kind == Kind::Zero) {
      return std::nullopt;
    }
    append_factor(flat, factor);
  }

  // PositiveCongruenceNormalization.positive_word_normalize: every maximal
  // block of WLookahead factors is sorted and deduplicated (P10--P11).
  std::vector<ExprId> result;
  std::size_t i = 0;
  while (i < flat.size()) {
    if (node(flat[i]).kind != Kind::Lookahead) {
      result.push_back(flat[i]);
      ++i;
      continue;
    }
    std::size_t j = i;
    std::vector<ExprId> block;
    while (j < flat.size() && node(flat[j]).kind == Kind::Lookahead) {
      block.push_back(flat[j]);
      ++j;
    }
    std::sort(block.begin(), block.end());
    block.erase(std::unique(block.begin(), block.end()), block.end());
    result.insert(result.end(), block.begin(), block.end());
    i = j;
  }
  return result;
}

ExprId Arena::build_word(const std::vector<ExprId>& word) {
  if (word.empty()) {
    return epsilon_;
  }
  if (word.size() == 1) {
    return word.front();
  }
  return intern(Key{Kind::Concat, 0, word});
}

ExprId Arena::concat(std::vector<ExprId> factors) {
  // Keeping unions below concatenation avoids materializing an exponential
  // DNF before the partial-derivative search starts.  All equations applied
  // by normalize_word (P9--P11 and the semiring unit/zero laws) are proved for
  // the complete pair semantics.
  if (normalization_ == NormalizationMode::Compact) {
    auto normalized = normalize_word(std::move(factors));
    if (!normalized.has_value()) {
      return zero_;
    }
    return build_word(*normalized);
  }

  // Optional positive-DNF mode applies the proved P7--P8 distributivity laws
  // eagerly.  It is useful as an ablation baseline but is not the solver
  // default because compact syntax can be exponentially smaller.
  std::vector<std::vector<ExprId>> products(1);
  for (ExprId factor : factors) {
    const Node& n = node(factor);
    if (n.kind == Kind::Zero) {
      return zero_;
    }
    std::vector<ExprId> alternatives;
    if (n.kind == Kind::Union) {
      alternatives = n.children;
    } else {
      alternatives.push_back(factor);
    }

    std::vector<std::vector<ExprId>> next;
    for (const auto& prefix : products) {
      for (ExprId alternative : alternatives) {
        std::vector<ExprId> product = prefix;
        append_factor(product, alternative);
        next.push_back(std::move(product));
      }
    }
    products = std::move(next);
  }

  std::vector<ExprId> terms;
  terms.reserve(products.size());
  for (auto& product : products) {
    auto normalized = normalize_word(std::move(product));
    if (normalized.has_value()) {
      terms.push_back(build_word(*normalized));
    }
  }
  return unite(std::move(terms));
}

ExprId Arena::star(ExprId body) {
  const Kind kind = node(body).kind;
  if (kind == Kind::Zero || kind == Kind::Epsilon) {
    return epsilon_;
  }
  return intern(Key{Kind::Star, 0, {body}});
}

ExprId Arena::lookahead(ExprId body) {
  const Node snapshot = node(body);
  if (snapshot.kind == Kind::Zero || snapshot.kind == Kind::Epsilon) {
    return body;
  }
  if (snapshot.kind == Kind::Lookahead) {
    return body;
  }
  // LookaheadDecision.rewpla_lookahead_lift, Eq. (35).
  if (snapshot.kind == Kind::Union) {
    std::vector<ExprId> lifted;
    lifted.reserve(snapshot.children.size());
    for (ExprId child : snapshot.children) {
      lifted.push_back(lookahead(child));
    }
    return unite(std::move(lifted));
  }
  if (snapshot.kind == Kind::Concat && snapshot.children.size() >= 2) {
    const ExprId first = snapshot.children.front();
    if (constraint_expression(first)) {
      std::vector<ExprId> rest(snapshot.children.begin() + 1,
                               snapshot.children.end());
      return concat({first, lookahead(concat(std::move(rest)))});
    }
  }
  return intern(Key{Kind::Lookahead, 0, {body}});
}

bool Arena::nullable(ExprId expression) const {
  if (nullable_cache_[expression] >= 0) {
    return nullable_cache_[expression] != 0;
  }
  const Node& n = node(expression);
  bool result = false;
  switch (n.kind) {
    case Kind::Zero:
    case Kind::Atom:
      result = false;
      break;
    case Kind::Epsilon:
    case Kind::Star:
      result = true;
      break;
    case Kind::Union:
      result = std::any_of(n.children.begin(), n.children.end(),
                           [this](ExprId child) { return nullable(child); });
      break;
    case Kind::Concat:
      result = std::all_of(n.children.begin(), n.children.end(),
                           [this](ExprId child) { return nullable(child); });
      break;
    case Kind::Lookahead:
      result = nullable(n.children.front());
      break;
  }
  nullable_cache_[expression] = result ? 1 : 0;
  return result;
}

bool Arena::constraint_expression(ExprId expression) const {
  if (constraint_cache_[expression] >= 0) {
    return constraint_cache_[expression] != 0;
  }
  const Node& n = node(expression);
  bool result = false;
  switch (n.kind) {
    case Kind::Zero:
    case Kind::Epsilon:
    case Kind::Lookahead:
      result = true;
      break;
    case Kind::Atom:
      result = false;
      break;
    case Kind::Union:
    case Kind::Concat:
      result = std::all_of(n.children.begin(), n.children.end(),
                           [this](ExprId child) {
                             return constraint_expression(child);
                           });
      break;
    case Kind::Star:
      result = constraint_expression(n.children.front());
      break;
  }
  constraint_cache_[expression] = result ? 1 : 0;
  return result;
}

StateSet Arena::top_terms(ExprId expression) const {
  const Node& n = node(expression);
  if (n.kind == Kind::Zero) {
    return {};
  }
  if (n.kind == Kind::Union) {
    return n.children;
  }
  return {expression};
}

std::vector<Symbol> Arena::atoms(ExprId expression) const {
  std::vector<Symbol> result;
  std::vector<ExprId> todo{expression};
  std::unordered_set<ExprId> seen;
  while (!todo.empty()) {
    const ExprId current = todo.back();
    todo.pop_back();
    if (!seen.insert(current).second) {
      continue;
    }
    const Node& n = node(current);
    if (n.kind == Kind::Atom) {
      result.push_back(n.atom);
    }
    todo.insert(todo.end(), n.children.begin(), n.children.end());
  }
  std::sort(result.begin(), result.end());
  result.erase(std::unique(result.begin(), result.end()), result.end());
  return result;
}

std::string Arena::render(ExprId expression) const {
  return render(expression, 0);
}

std::string Arena::render(ExprId expression, int parent_precedence) const {
  const Node& n = node(expression);
  const int own = precedence(n.kind);
  std::string text;
  switch (n.kind) {
    case Kind::Zero:
      text = "0";
      break;
    case Kind::Epsilon:
      text = "1";
      break;
    case Kind::Atom:
      text.assign(1, static_cast<char>(n.atom));
      break;
    case Kind::Union:
      for (std::size_t i = 0; i < n.children.size(); ++i) {
        if (i != 0) text += "+";
        text += render(n.children[i], own);
      }
      break;
    case Kind::Concat:
      for (std::size_t i = 0; i < n.children.size(); ++i) {
        if (i != 0) text += ".";
        text += render(n.children[i], own);
      }
      break;
    case Kind::Star:
      text = render(n.children.front(), own) + "*";
      break;
    case Kind::Lookahead:
      text = "LA(" + render(n.children.front(), 0) + ")";
      break;
  }
  if (own < parent_precedence) {
    return "(" + text + ")";
  }
  return text;
}

std::string display_word(std::string_view word) {
  if (word.empty()) {
    return "<epsilon>";
  }
  std::string result;
  for (unsigned char c : word) {
    if (c == '\\') {
      result += "\\\\";
    } else if (c == '\n') {
      result += "\\n";
    } else if (c == '\r') {
      result += "\\r";
    } else if (c == '\t') {
      result += "\\t";
    } else if (c >= 32 && c <= 126) {
      result.push_back(static_cast<char>(c));
    } else {
      constexpr char digits[] = "0123456789abcdef";
      result += "\\x";
      result.push_back(digits[(c >> 4U) & 0x0fU]);
      result.push_back(digits[c & 0x0fU]);
    }
  }
  return result;
}

std::string json_escape(std::string_view text) {
  std::ostringstream out;
  for (unsigned char c : text) {
    switch (c) {
      case '"':
        out << "\\\"";
        break;
      case '\\':
        out << "\\\\";
        break;
      case '\b':
        out << "\\b";
        break;
      case '\f':
        out << "\\f";
        break;
      case '\n':
        out << "\\n";
        break;
      case '\r':
        out << "\\r";
        break;
      case '\t':
        out << "\\t";
        break;
      default:
        if (c < 0x20) {
          constexpr char digits[] = "0123456789abcdef";
          out << "\\u00" << digits[(c >> 4U) & 0x0fU] << digits[c & 0x0fU];
        } else {
          out << static_cast<char>(c);
        }
    }
  }
  return out.str();
}

}  // namespace rewpla
