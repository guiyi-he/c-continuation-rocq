#include "rewpla/rewpla.hpp"

#include <algorithm>
#include <cctype>
#include <limits>

namespace rewpla {
namespace {

int hex_value(char c) noexcept {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

}  // namespace

RegexFrontend::RegexFrontend(Arena& arena, std::string_view input,
                             std::vector<Symbol> alphabet,
                             RegexFrontendOptions options)
    : arena_(arena),
      input_(input),
      alphabet_(std::move(alphabet)),
      alphabet_set_(alphabet_.begin(), alphabet_.end()),
      options_(options),
      limit_(input.size()) {
  if (alphabet_.empty()) {
    throw std::invalid_argument("regex frontend alphabet must be nonempty");
  }
  if (alphabet_set_.size() != alphabet_.size()) {
    throw std::invalid_argument("regex frontend alphabet contains duplicates");
  }
  if (options_.max_repeat == 0) {
    throw std::invalid_argument("regex frontend max repeat must be positive");
  }
}

void RegexFrontend::skip_space() {
  // Whitespace is significant in conventional regex syntax.
}

bool RegexFrontend::starts_with(std::string_view token) const {
  return position_ + token.size() <= limit_ &&
         input_.substr(position_, token.size()) == token;
}

std::optional<char> RegexFrontend::peek() const {
  if (position_ >= limit_) return std::nullopt;
  return input_[position_];
}

char RegexFrontend::take() {
  if (position_ >= limit_) fail("unexpected end of regex");
  return input_[position_++];
}

[[noreturn]] void RegexFrontend::fail(const std::string& message) const {
  throw ParseError(position_, message);
}

bool RegexFrontend::escaped_final_dollar() const {
  if (input_.empty() || input_.back() != '$') return false;
  std::size_t slashes = 0;
  for (std::size_t i = input_.size() - 1; i > 0 && input_[i - 1] == '\\'; --i) {
    ++slashes;
  }
  return slashes % 2 == 1;
}

ExprId RegexFrontend::parse() {
  anchored_start_ = !input_.empty() && input_.front() == '^';
  anchored_end_ = !input_.empty() && input_.back() == '$' &&
                  !escaped_final_dollar();
  position_ = anchored_start_ ? 1 : 0;
  limit_ = input_.size() - (anchored_end_ ? 1 : 0);

  ExprId expression = parse_alternation();
  if (position_ != limit_) {
    fail("unexpected regex token");
  }

  if (options_.match_mode == RegexMatchMode::Search) {
    std::vector<ExprId> factors;
    if (!anchored_start_) factors.push_back(sigma_star());
    factors.push_back(expression);
    if (!anchored_end_) factors.push_back(sigma_star());
    expression = arena_.concat(std::move(factors));
  }
  return expression;
}

ExprId RegexFrontend::parse_alternation() {
  std::vector<ExprId> alternatives{parse_concatenation()};
  while (peek().has_value() && *peek() == '|') {
    take();
    alternatives.push_back(parse_concatenation());
  }
  return arena_.unite(std::move(alternatives));
}

bool RegexFrontend::begins_primary() const {
  const std::optional<char> next = peek();
  return next.has_value() && *next != '|' && *next != ')';
}

ExprId RegexFrontend::parse_concatenation() {
  std::vector<ExprId> factors;
  while (begins_primary()) {
    factors.push_back(parse_repetition());
  }
  return arena_.concat(std::move(factors));
}

ExprId RegexFrontend::repeat_exact(ExprId expression, std::size_t count) {
  std::vector<ExprId> factors(count, expression);
  return arena_.concat(std::move(factors));
}

std::size_t RegexFrontend::parse_decimal(const std::string& role) {
  if (!peek().has_value() ||
      !std::isdigit(static_cast<unsigned char>(*peek()))) {
    fail("expected decimal " + role);
  }
  std::size_t value = 0;
  while (peek().has_value() &&
         std::isdigit(static_cast<unsigned char>(*peek()))) {
    const unsigned digit = static_cast<unsigned>(take() - '0');
    if (value > (std::numeric_limits<std::size_t>::max() - digit) / 10) {
      fail("repeat count overflow");
    }
    value = value * 10 + digit;
  }
  if (value > options_.max_repeat) {
    fail("repeat count exceeds --max-repeat");
  }
  return value;
}

ExprId RegexFrontend::apply_braced_repeat(ExprId expression) {
  take();  // {
  const std::size_t minimum = parse_decimal("repeat lower bound");
  if (!peek().has_value()) fail("unterminated repeat");
  if (*peek() == '}') {
    take();
    return repeat_exact(expression, minimum);
  }
  if (take() != ',') fail("expected ',' or '}' in repeat");
  if (!peek().has_value()) fail("unterminated repeat");
  if (*peek() == '}') {
    take();
    return arena_.concat({repeat_exact(expression, minimum),
                          arena_.star(expression)});
  }
  const std::size_t maximum = parse_decimal("repeat upper bound");
  if (maximum < minimum) fail("repeat upper bound is below lower bound");
  if (!peek().has_value() || take() != '}') fail("unterminated repeat");

  std::vector<ExprId> factors;
  factors.push_back(repeat_exact(expression, minimum));
  const ExprId optional = arena_.unite({arena_.epsilon(), expression});
  for (std::size_t i = minimum; i < maximum; ++i) {
    factors.push_back(optional);
  }
  return arena_.concat(std::move(factors));
}

ExprId RegexFrontend::parse_repetition() {
  ExprId expression = parse_primary();
  if (!peek().has_value()) return expression;
  const char quantifier = *peek();
  if (quantifier == '*') {
    take();
    expression = arena_.star(expression);
  } else if (quantifier == '+') {
    take();
    expression = arena_.concat({expression, arena_.star(expression)});
  } else if (quantifier == '?') {
    take();
    expression = arena_.unite({arena_.epsilon(), expression});
  } else if (quantifier == '{') {
    expression = apply_braced_repeat(expression);
  } else {
    return expression;
  }

  if (peek().has_value() &&
      (*peek() == '*' || *peek() == '+' || *peek() == '?' || *peek() == '{')) {
    fail("lazy, possessive, or repeated quantifiers are not supported");
  }
  return expression;
}

Symbol RegexFrontend::parse_escaped_symbol() {
  if (!peek().has_value()) fail("trailing escape");
  const char escaped = take();
  switch (escaped) {
    case 'n': return static_cast<Symbol>('\n');
    case 'r': return static_cast<Symbol>('\r');
    case 't': return static_cast<Symbol>('\t');
    case 'f': return static_cast<Symbol>('\f');
    case 'v': return static_cast<Symbol>('\v');
    case '0': return static_cast<Symbol>('\0');
    case 'x': {
      if (position_ + 2 > limit_) fail("incomplete hexadecimal escape");
      const int high = hex_value(take());
      const int low = hex_value(take());
      if (high < 0 || low < 0) fail("invalid hexadecimal escape");
      return static_cast<Symbol>((high << 4) | low);
    }
    case 'd':
    case 'D':
    case 's':
    case 'S':
    case 'w':
    case 'W':
      fail("predefined character classes are not yet supported; use an explicit class");
    default:
      if (std::isalnum(static_cast<unsigned char>(escaped))) {
        fail("backreference or unsupported alphabetic escape");
      }
      return static_cast<Symbol>(static_cast<unsigned char>(escaped));
  }
}

Symbol RegexFrontend::parse_class_symbol() {
  const char value = take();
  if (value == '\\') return parse_escaped_symbol();
  return static_cast<Symbol>(static_cast<unsigned char>(value));
}

ExprId RegexFrontend::parse_class() {
  take();  // [
  bool negated = false;
  if (peek().has_value() && *peek() == '^') {
    take();
    negated = true;
  }

  std::unordered_set<Symbol> members;
  bool first = true;
  bool closed = false;
  while (peek().has_value()) {
    if (*peek() == ']' && !first) {
      take();
      closed = true;
      break;
    }
    const Symbol begin = parse_class_symbol();
    first = false;
    if (peek().has_value() && *peek() == '-' &&
        position_ + 1 < limit_ && input_[position_ + 1] != ']') {
      take();
      const Symbol end = parse_class_symbol();
      if (begin > end) fail("descending character-class range");
      for (unsigned value = begin; value <= end; ++value) {
        members.insert(static_cast<Symbol>(value));
      }
    } else {
      members.insert(begin);
    }
  }
  if (!closed) fail("unterminated character class");

  std::vector<ExprId> alternatives;
  if (negated) {
    for (Symbol symbol : alphabet_) {
      if (members.find(symbol) == members.end()) {
        alternatives.push_back(arena_.atom(symbol));
      }
    }
  } else {
    for (Symbol symbol : alphabet_) {
      if (members.erase(symbol) != 0) {
        alternatives.push_back(arena_.atom(symbol));
      }
    }
    if (!members.empty()) {
      fail("character class contains a symbol outside --alphabet");
    }
  }
  return arena_.unite(std::move(alternatives));
}

ExprId RegexFrontend::parse_group() {
  take();  // (
  bool lookahead = false;
  if (starts_with("?:")) {
    position_ += 2;
  } else if (starts_with("?=")) {
    position_ += 2;
    lookahead = true;
  } else if (starts_with("?!")) {
    fail("negative lookahead is outside positive REwPLA");
  } else if (peek().has_value() && *peek() == '?') {
    fail("unsupported group extension");
  }

  ExprId body = parse_alternation();
  if (!peek().has_value() || take() != ')') fail("unterminated group");
  return lookahead ? arena_.lookahead(body) : body;
}

ExprId RegexFrontend::parse_primary() {
  const std::optional<char> next = peek();
  if (!next.has_value()) fail("expected regex atom");
  if (*next == '(') return parse_group();
  if (*next == '[') return parse_class();
  if (*next == '.') {
    take();
    std::vector<ExprId> alternatives;
    for (Symbol symbol : alphabet_) alternatives.push_back(arena_.atom(symbol));
    return arena_.unite(std::move(alternatives));
  }
  if (*next == '\\') {
    take();
    return arena_.atom(parse_escaped_symbol());
  }
  if (*next == '^' || *next == '$') {
    fail("anchors are supported only at the outer pattern boundaries");
  }
  if (*next == '*' || *next == '+' || *next == '?' || *next == '{' ||
      *next == '}') {
    fail("quantifier has no preceding atom");
  }
  return arena_.atom(static_cast<Symbol>(static_cast<unsigned char>(take())));
}

ExprId RegexFrontend::sigma_star() {
  std::vector<ExprId> alternatives;
  alternatives.reserve(alphabet_.size());
  for (Symbol symbol : alphabet_) alternatives.push_back(arena_.atom(symbol));
  return arena_.star(arena_.unite(std::move(alternatives)));
}

}  // namespace rewpla
