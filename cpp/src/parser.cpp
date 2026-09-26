#include "rewpla/rewpla.hpp"

#include <cctype>

namespace rewpla {

Parser::Parser(Arena& arena, std::string_view input)
    : arena_(arena), input_(input) {}

bool Parser::is_letter(char c) noexcept {
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');
}

void Parser::skip_space() {
  while (position_ < input_.size()) {
    const char c = input_[position_];
    if (c != ' ' && c != '\t' && c != '\r' && c != '\n') {
      break;
    }
    ++position_;
  }
}

bool Parser::starts_with(std::string_view token) {
  skip_space();
  return input_.substr(position_, token.size()) == token;
}

std::optional<char> Parser::peek() {
  skip_space();
  if (position_ >= input_.size()) {
    return std::nullopt;
  }
  return input_[position_];
}

char Parser::take() {
  const auto c = peek();
  if (!c.has_value()) {
    fail("unexpected end of input");
  }
  ++position_;
  return *c;
}

[[noreturn]] void Parser::fail(const std::string& message) const {
  throw ParseError(position_, message);
}

bool Parser::begins_atom() {
  const auto c = peek();
  return c.has_value() &&
         (is_letter(*c) || *c == '0' || *c == '1' || *c == '(');
}

ExprId Parser::parse() {
  const ExprId result = parse_union();
  if (const auto c = peek(); c.has_value()) {
    fail(std::string("unexpected character '") + *c + "'");
  }
  return result;
}

ExprId Parser::parse_union() {
  std::vector<ExprId> terms{parse_concat()};
  while (true) {
    const auto c = peek();
    if (!c.has_value() || *c != '+') {
      break;
    }
    take();
    terms.push_back(parse_concat());
  }
  return arena_.unite(std::move(terms));
}

ExprId Parser::parse_concat() {
  std::vector<ExprId> factors{parse_repeat()};
  while (true) {
    const auto c = peek();
    if (c.has_value() && *c == '.') {
      take();
      if (!begins_atom()) {
        fail("expected an expression after '.'");
      }
      factors.push_back(parse_repeat());
    } else if (begins_atom()) {
      factors.push_back(parse_repeat());
    } else {
      break;
    }
  }
  return arena_.concat(std::move(factors));
}

ExprId Parser::parse_repeat() {
  ExprId expression = parse_atom();
  while (true) {
    const auto c = peek();
    if (!c.has_value() || *c != '*') {
      break;
    }
    take();
    expression = arena_.star(expression);
  }
  return expression;
}

ExprId Parser::parse_atom() {
  if (starts_with("LA")) {
    position_ += 2;
    if (peek() != std::optional<char>('(')) {
      fail("expected '(' after LA");
    }
    take();
    const ExprId body = parse_union();
    if (peek() != std::optional<char>(')')) {
      fail("expected ')' after LA expression");
    }
    take();
    return arena_.lookahead(body);
  }

  const auto c = peek();
  if (!c.has_value()) {
    fail("expected an expression");
  }
  if (is_letter(*c)) {
    take();
    return arena_.atom(static_cast<Symbol>(*c));
  }
  if (*c == '0') {
    take();
    return arena_.zero();
  }
  if (*c == '1') {
    take();
    return arena_.epsilon();
  }
  if (*c == '(') {
    take();
    const ExprId body = parse_union();
    if (peek() != std::optional<char>(')')) {
      fail("expected ')'");
    }
    take();
    return body;
  }
  fail(std::string("unexpected character '") + *c + "'");
}

}  // namespace rewpla
