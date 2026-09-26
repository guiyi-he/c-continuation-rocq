#pragma once

#include <cstddef>
#include <cstdint>
#include <deque>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace rewpla {

using Symbol = unsigned char;
using ExprId = std::uint32_t;
using StateSet = std::vector<ExprId>;

enum class Kind : std::uint8_t {
  Zero,
  Epsilon,
  Atom,
  Union,
  Concat,
  Star,
  Lookahead,
};

enum class NormalizationMode : std::uint8_t {
  // Preserve union nodes below concatenation.  This is the standard compact
  // representation used by the partial-derivative solver.
  Compact,
  // Apply the proved distributivity laws eagerly and construct positive DNF.
  // Retained for normalization experiments; it can be exponentially larger.
  DistributiveDnf,
};

struct Node {
  Kind kind = Kind::Zero;
  Symbol atom = 0;
  std::vector<ExprId> children;
};

class ResourceLimit : public std::runtime_error {
 public:
  explicit ResourceLimit(const std::string& message) : std::runtime_error(message) {}
};

class ParseError : public std::runtime_error {
 public:
  ParseError(std::size_t position, const std::string& message);
  [[nodiscard]] std::size_t position() const noexcept { return position_; }

 private:
  std::size_t position_;
};

// Hash-consed syntax arena.  Its smart constructors implement only equations
// proved sound for the complete pair semantics M in the Rocq development:
// union ACI/zero, semiring concat laws and distribution, P10--P11 for blocks
// of positive lookaheads, and the proved lookahead-lifting equations.
class Arena {
 public:
  explicit Arena(std::size_t max_nodes = 1'000'000,
                 NormalizationMode normalization = NormalizationMode::Compact);

  [[nodiscard]] ExprId zero() const noexcept { return zero_; }
  [[nodiscard]] ExprId epsilon() const noexcept { return epsilon_; }
  [[nodiscard]] const Node& node(ExprId id) const;
  [[nodiscard]] std::size_t size() const noexcept { return nodes_.size(); }

  ExprId atom(Symbol symbol);
  ExprId unite(std::vector<ExprId> terms);
  ExprId concat(std::vector<ExprId> factors);
  ExprId star(ExprId body);
  ExprId lookahead(ExprId body);

  [[nodiscard]] bool nullable(ExprId expression) const;
  [[nodiscard]] bool constraint_expression(ExprId expression) const;
  [[nodiscard]] StateSet top_terms(ExprId expression) const;
  [[nodiscard]] std::vector<Symbol> atoms(ExprId expression) const;
  [[nodiscard]] std::string render(ExprId expression) const;

 private:
  struct Key {
    Kind kind = Kind::Zero;
    Symbol atom = 0;
    std::vector<ExprId> children;
    bool operator==(const Key& other) const noexcept;
  };

  struct KeyHash {
    std::size_t operator()(const Key& key) const noexcept;
  };

  ExprId intern(Key key);
  void append_factor(std::vector<ExprId>& word, ExprId factor) const;
  [[nodiscard]] std::optional<std::vector<ExprId>> normalize_word(
      std::vector<ExprId> word) const;
  ExprId build_word(const std::vector<ExprId>& word);
  [[nodiscard]] std::string render(ExprId expression, int parent_precedence) const;

  std::size_t max_nodes_;
  NormalizationMode normalization_;
  std::vector<Node> nodes_;
  std::unordered_map<Key, ExprId, KeyHash> interner_;
  mutable std::vector<std::int8_t> nullable_cache_;
  mutable std::vector<std::int8_t> constraint_cache_;
  ExprId zero_ = 0;
  ExprId epsilon_ = 1;
};

class Parser {
 public:
  Parser(Arena& arena, std::string_view input);
  ExprId parse();

 private:
  void skip_space();
  [[nodiscard]] bool starts_with(std::string_view token);
  [[nodiscard]] std::optional<char> peek();
  char take();
  [[noreturn]] void fail(const std::string& message) const;
  ExprId parse_union();
  ExprId parse_concat();
  ExprId parse_repeat();
  ExprId parse_atom();
  [[nodiscard]] static bool is_letter(char c) noexcept;
  [[nodiscard]] bool begins_atom();

  Arena& arena_;
  std::string_view input_;
  std::size_t position_ = 0;
};

enum class RegexMatchMode : std::uint8_t {
  Projected,
  Search,
};

struct RegexFrontendOptions {
  RegexMatchMode match_mode = RegexMatchMode::Search;
  std::size_t max_repeat = 10'000;
};

// Parser/translator for the regular, positive-lookahead fragment of familiar
// regex syntax.  Unsupported non-regular or negative constructs fail closed
// with ParseError rather than being approximated.
class RegexFrontend {
 public:
  RegexFrontend(Arena& arena, std::string_view input,
                std::vector<Symbol> alphabet,
                RegexFrontendOptions options = {});
  ExprId parse();

 private:
  void skip_space();
  [[nodiscard]] bool starts_with(std::string_view token) const;
  [[nodiscard]] std::optional<char> peek() const;
  char take();
  [[noreturn]] void fail(const std::string& message) const;
  ExprId parse_alternation();
  ExprId parse_concatenation();
  ExprId parse_repetition();
  ExprId parse_primary();
  ExprId parse_group();
  ExprId parse_class();
  Symbol parse_escaped_symbol();
  Symbol parse_class_symbol();
  std::size_t parse_decimal(const std::string& role);
  ExprId repeat_exact(ExprId expression, std::size_t count);
  ExprId apply_braced_repeat(ExprId expression);
  [[nodiscard]] bool begins_primary() const;
  [[nodiscard]] bool escaped_final_dollar() const;
  ExprId sigma_star();

  Arena& arena_;
  std::string_view input_;
  std::vector<Symbol> alphabet_;
  std::unordered_set<Symbol> alphabet_set_;
  RegexFrontendOptions options_;
  std::size_t position_ = 0;
  std::size_t limit_ = 0;
  bool anchored_start_ = false;
  bool anchored_end_ = false;
};

struct DerivativePair {
  StateSet main;
  StateSet context;
};

class PartialDerivativeNfa {
 public:
  explicit PartialDerivativeNfa(Arena& arena) : arena_(arena) {}

  [[nodiscard]] StateSet initial(ExprId expression);
  const DerivativePair& derivative(ExprId expression, Symbol symbol);
  StateSet move(const StateSet& states, Symbol symbol);
  [[nodiscard]] bool final(const StateSet& states) const;
  bool accepts(ExprId expression, std::string_view word);
  [[nodiscard]] std::size_t cached_transition_count() const noexcept {
    return memo_.size();
  }
  [[nodiscard]] std::size_t observed_state_count() const noexcept {
    return observed_states_.size();
  }

 private:
  struct TransitionKey {
    ExprId expression = 0;
    Symbol symbol = 0;
    bool operator==(const TransitionKey& other) const noexcept {
      return expression == other.expression && symbol == other.symbol;
    }
  };

  struct TransitionKeyHash {
    std::size_t operator()(const TransitionKey& key) const noexcept;
  };

  static void add(StateSet& target, ExprId expression, const Arena& arena);
  static void add_all(StateSet& target, const StateSet& source);
  static void canonicalize(StateSet& states);
  void add_concat_left(StateSet& target, const StateSet& left, ExprId right);
  void add_concat_product(StateSet& target, const StateSet& left,
                          const StateSet& right);

  Arena& arena_;
  std::unordered_map<TransitionKey, DerivativePair, TransitionKeyHash> memo_;
  std::unordered_set<ExprId> observed_states_;
};

enum class SolveStatus {
  Sat,
  Unsat,
  ResourceLimit,
};

struct SolveOptions {
  std::size_t max_configurations = 1'000'000;
};

struct SolveStats {
  std::size_t configurations_discovered = 0;
  std::size_t configurations_expanded = 0;
  std::size_t product_symbol_steps = 0;
  std::size_t partial_states_observed = 0;
  std::size_t partial_derivatives_cached = 0;
  std::size_t ast_nodes = 0;
};

struct SolveResult {
  SolveStatus status = SolveStatus::Unsat;
  std::string witness;
  std::string detail;
  SolveStats stats;
};

class IntersectionSolver {
 public:
  IntersectionSolver(Arena& arena, PartialDerivativeNfa& nfa,
                     std::vector<Symbol> alphabet, SolveOptions options = {});

  SolveResult solve(const std::vector<ExprId>& expressions);

 private:
  struct Configuration {
    std::vector<StateSet> components;
    bool operator==(const Configuration& other) const noexcept {
      return components == other.components;
    }
  };

  struct ConfigurationHash {
    std::size_t operator()(const Configuration& configuration) const noexcept;
  };

  struct Entry {
    Configuration configuration;
    std::size_t parent = 0;
    Symbol symbol = 0;
    bool root = false;
  };

  [[nodiscard]] bool accepting(const Configuration& configuration) const;
  [[nodiscard]] std::string witness_for(const std::vector<Entry>& entries,
                                        std::size_t index) const;
  [[nodiscard]] SolveStats stats(std::size_t discovered,
                                 std::size_t expanded,
                                 std::size_t steps) const;

  Arena& arena_;
  PartialDerivativeNfa& nfa_;
  std::vector<Symbol> alphabet_;
  SolveOptions options_;
};

// Experimental eager baseline.  Each component NFA is determinized to its
// complete reachable subset DFA before the intersection product is searched.
// It deliberately shares the partial-derivative transition core with the lazy
// solver so that experiments isolate evaluation strategy, not semantics.
struct EagerSolveOptions {
  std::size_t max_dfa_states = 1'000'000;
  std::size_t max_product_configurations = 1'000'000;
};

struct EagerSolveStats {
  std::vector<std::size_t> component_dfa_states;
  std::size_t dfa_states_total = 0;
  std::size_t dfa_transitions = 0;
  std::size_t product_configurations_discovered = 0;
  std::size_t product_configurations_expanded = 0;
  std::size_t product_symbol_steps = 0;
  std::size_t partial_states_observed = 0;
  std::size_t partial_derivatives_cached = 0;
  std::size_t ast_nodes = 0;
};

struct EagerSolveResult {
  SolveStatus status = SolveStatus::Unsat;
  std::string witness;
  std::string detail;
  EagerSolveStats stats;
};

class EagerIntersectionSolver {
 public:
  EagerIntersectionSolver(Arena& arena, PartialDerivativeNfa& nfa,
                          std::vector<Symbol> alphabet,
                          EagerSolveOptions options = {});

  EagerSolveResult solve(const std::vector<ExprId>& expressions);

 private:
  Arena& arena_;
  PartialDerivativeNfa& nfa_;
  std::vector<Symbol> alphabet_;
  EagerSolveOptions options_;
};

[[nodiscard]] std::string display_word(std::string_view word);
[[nodiscard]] std::string json_escape(std::string_view text);

}  // namespace rewpla
