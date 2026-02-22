#include "json_rpc.hpp"

#include <cctype>
#include <cmath>
#include <cstdlib>
#include <sstream>

namespace jsonrpc {

Json::Json() : value_(nullptr) {}
Json::Json(std::nullptr_t) : value_(nullptr) {}
Json::Json(bool v) : value_(v) {}
Json::Json(double v) : value_(v) {}
Json::Json(int v) : value_(static_cast<double>(v)) {}
Json::Json(std::string v) : value_(std::move(v)) {}
Json::Json(const char* v) : value_(std::string(v)) {}
Json::Json(array_t v) : value_(std::move(v)) {}
Json::Json(object_t v) : value_(std::move(v)) {}

bool Json::isNull() const { return std::holds_alternative<std::nullptr_t>(value_); }
bool Json::isBool() const { return std::holds_alternative<bool>(value_); }
bool Json::isNumber() const { return std::holds_alternative<double>(value_); }
bool Json::isString() const { return std::holds_alternative<std::string>(value_); }
bool Json::isArray() const { return std::holds_alternative<array_t>(value_); }
bool Json::isObject() const { return std::holds_alternative<object_t>(value_); }

bool Json::asBool() const { return std::get<bool>(value_); }
double Json::asNumber() const { return std::get<double>(value_); }
const std::string& Json::asString() const { return std::get<std::string>(value_); }
const Json::array_t& Json::asArray() const { return std::get<array_t>(value_); }
const Json::object_t& Json::asObject() const { return std::get<object_t>(value_); }

const Json* Json::get(const std::string& key) const {
  if (!isObject()) return nullptr;
  const auto& obj = asObject();
  auto it = obj.find(key);
  if (it == obj.end()) return nullptr;
  return &it->second;
}

Json* Json::get(const std::string& key) {
  if (!isObject()) return nullptr;
  auto& obj = std::get<object_t>(value_);
  auto it = obj.find(key);
  if (it == obj.end()) return nullptr;
  return &it->second;
}

namespace {

class Parser {
 public:
  explicit Parser(const std::string& input) : input_(input) {}

  bool parse(Json& out, std::string& error) {
    skipWs();
    if (!parseValue(out, error)) return false;
    skipWs();
    if (pos_ != input_.size()) {
      error = "Unexpected trailing characters at byte " + std::to_string(pos_);
      return false;
    }
    return true;
  }

 private:
  static void appendUtf8(std::string& out, unsigned codepoint) {
    if (codepoint <= 0x7F) {
      out.push_back(static_cast<char>(codepoint));
      return;
    }
    if (codepoint <= 0x7FF) {
      out.push_back(static_cast<char>(0xC0 | (codepoint >> 6)));
      out.push_back(static_cast<char>(0x80 | (codepoint & 0x3F)));
      return;
    }
    if (codepoint <= 0xFFFF) {
      out.push_back(static_cast<char>(0xE0 | (codepoint >> 12)));
      out.push_back(static_cast<char>(0x80 | ((codepoint >> 6) & 0x3F)));
      out.push_back(static_cast<char>(0x80 | (codepoint & 0x3F)));
      return;
    }
    out.push_back(static_cast<char>(0xF0 | (codepoint >> 18)));
    out.push_back(static_cast<char>(0x80 | ((codepoint >> 12) & 0x3F)));
    out.push_back(static_cast<char>(0x80 | ((codepoint >> 6) & 0x3F)));
    out.push_back(static_cast<char>(0x80 | (codepoint & 0x3F)));
  }

  bool parseHex4(unsigned& out, std::string& error) {
    out = 0;
    for (int i = 0; i < 4; i++) {
      if (pos_ >= input_.size()) {
        error = "Truncated unicode escape";
        return false;
      }
      char c = input_[pos_++];
      out <<= 4;
      if (c >= '0' && c <= '9')
        out |= static_cast<unsigned>(c - '0');
      else if (c >= 'a' && c <= 'f')
        out |= static_cast<unsigned>(10 + c - 'a');
      else if (c >= 'A' && c <= 'F')
        out |= static_cast<unsigned>(10 + c - 'A');
      else {
        error = "Invalid hex digit in unicode escape";
        return false;
      }
    }
    return true;
  }

  bool parseString(std::string& out, std::string& error) {
    if (!consume('"')) {
      error = "Expected string at byte " + std::to_string(pos_);
      return false;
    }

    out.clear();
    while (pos_ < input_.size()) {
      char c = input_[pos_++];
      if (c == '"') return true;
      if (static_cast<unsigned char>(c) < 0x20) {
        error = "Control character in string";
        return false;
      }
      if (c != '\\') {
        out.push_back(c);
        continue;
      }

      if (pos_ >= input_.size()) {
        error = "Truncated escape sequence";
        return false;
      }
      char esc = input_[pos_++];
      switch (esc) {
        case '"':
        case '\\':
        case '/':
          out.push_back(esc);
          break;
        case 'b':
          out.push_back('\b');
          break;
        case 'f':
          out.push_back('\f');
          break;
        case 'n':
          out.push_back('\n');
          break;
        case 'r':
          out.push_back('\r');
          break;
        case 't':
          out.push_back('\t');
          break;
        case 'u': {
          unsigned cp = 0;
          if (!parseHex4(cp, error)) return false;
          appendUtf8(out, cp);
          break;
        }
        default:
          error = "Invalid escape sequence";
          return false;
      }
    }

    error = "Unterminated string";
    return false;
  }

  bool parseNumber(Json& out, std::string& error) {
    size_t start = pos_;
    if (peek() == '-') pos_++;
    if (peek() == '0') {
      pos_++;
    } else {
      if (!std::isdigit(static_cast<unsigned char>(peek()))) {
        error = "Invalid number";
        return false;
      }
      while (std::isdigit(static_cast<unsigned char>(peek()))) pos_++;
    }
    if (peek() == '.') {
      pos_++;
      if (!std::isdigit(static_cast<unsigned char>(peek()))) {
        error = "Invalid fractional part";
        return false;
      }
      while (std::isdigit(static_cast<unsigned char>(peek()))) pos_++;
    }
    if (peek() == 'e' || peek() == 'E') {
      pos_++;
      if (peek() == '+' || peek() == '-') pos_++;
      if (!std::isdigit(static_cast<unsigned char>(peek()))) {
        error = "Invalid exponent";
        return false;
      }
      while (std::isdigit(static_cast<unsigned char>(peek()))) pos_++;
    }

    const std::string text = input_.substr(start, pos_ - start);
    char* end = nullptr;
    const double value = std::strtod(text.c_str(), &end);
    if (!end || *end != '\0' || !std::isfinite(value)) {
      error = "Invalid number value";
      return false;
    }
    out = Json(value);
    return true;
  }

  bool parseArray(Json& out, std::string& error) {
    if (!consume('[')) {
      error = "Expected '['";
      return false;
    }

    Json::array_t arr;
    skipWs();
    if (consume(']')) {
      out = Json(std::move(arr));
      return true;
    }

    while (true) {
      Json item;
      if (!parseValue(item, error)) return false;
      arr.push_back(std::move(item));
      skipWs();
      if (consume(']')) {
        out = Json(std::move(arr));
        return true;
      }
      if (!consume(',')) {
        error = "Expected ',' or ']' in array";
        return false;
      }
      skipWs();
    }
  }

  bool parseObject(Json& out, std::string& error) {
    if (!consume('{')) {
      error = "Expected '{'";
      return false;
    }

    Json::object_t obj;
    skipWs();
    if (consume('}')) {
      out = Json(std::move(obj));
      return true;
    }

    while (true) {
      std::string key;
      if (!parseString(key, error)) return false;
      skipWs();
      if (!consume(':')) {
        error = "Expected ':' in object";
        return false;
      }
      skipWs();
      Json value;
      if (!parseValue(value, error)) return false;
      obj[key] = std::move(value);
      skipWs();
      if (consume('}')) {
        out = Json(std::move(obj));
        return true;
      }
      if (!consume(',')) {
        error = "Expected ',' or '}' in object";
        return false;
      }
      skipWs();
    }
  }

  bool parseValue(Json& out, std::string& error) {
    char c = peek();
    if (c == '"') {
      std::string s;
      if (!parseString(s, error)) return false;
      out = Json(std::move(s));
      return true;
    }
    if (c == '{') return parseObject(out, error);
    if (c == '[') return parseArray(out, error);
    if (c == '-' || std::isdigit(static_cast<unsigned char>(c))) return parseNumber(out, error);

    if (match("true")) {
      out = Json(true);
      return true;
    }
    if (match("false")) {
      out = Json(false);
      return true;
    }
    if (match("null")) {
      out = Json(nullptr);
      return true;
    }

    error = "Unexpected token at byte " + std::to_string(pos_);
    return false;
  }

  void skipWs() {
    while (pos_ < input_.size() && std::isspace(static_cast<unsigned char>(input_[pos_]))) pos_++;
  }

  bool consume(char c) {
    if (peek() == c) {
      pos_++;
      return true;
    }
    return false;
  }

  bool match(const char* text) {
    size_t i = 0;
    while (text[i] != '\0') {
      if (pos_ + i >= input_.size() || input_[pos_ + i] != text[i]) return false;
      i++;
    }
    pos_ += i;
    return true;
  }

  char peek() const { return pos_ < input_.size() ? input_[pos_] : '\0'; }

  const std::string& input_;
  size_t pos_ = 0;
};

std::string escapeString(const std::string& input) {
  std::string out;
  out.reserve(input.size() + 8);
  for (unsigned char c : input) {
    switch (c) {
      case '"':
        out += "\\\"";
        break;
      case '\\':
        out += "\\\\";
        break;
      case '\b':
        out += "\\b";
        break;
      case '\f':
        out += "\\f";
        break;
      case '\n':
        out += "\\n";
        break;
      case '\r':
        out += "\\r";
        break;
      case '\t':
        out += "\\t";
        break;
      default:
        if (c < 0x20) {
          static const char* hex = "0123456789ABCDEF";
          out += "\\u00";
          out.push_back(hex[(c >> 4) & 0x0F]);
          out.push_back(hex[c & 0x0F]);
        } else {
          out.push_back(static_cast<char>(c));
        }
        break;
    }
  }
  return out;
}

void serializeValue(const Json& value, std::string& out) {
  if (value.isNull()) {
    out += "null";
    return;
  }
  if (value.isBool()) {
    out += value.asBool() ? "true" : "false";
    return;
  }
  if (value.isNumber()) {
    std::ostringstream oss;
    oss.precision(15);
    oss << value.asNumber();
    out += oss.str();
    return;
  }
  if (value.isString()) {
    out.push_back('"');
    out += escapeString(value.asString());
    out.push_back('"');
    return;
  }
  if (value.isArray()) {
    out.push_back('[');
    const auto& arr = value.asArray();
    for (size_t i = 0; i < arr.size(); i++) {
      if (i) out.push_back(',');
      serializeValue(arr[i], out);
    }
    out.push_back(']');
    return;
  }

  out.push_back('{');
  bool first = true;
  for (const auto& kv : value.asObject()) {
    if (!first) out.push_back(',');
    first = false;
    out.push_back('"');
    out += escapeString(kv.first);
    out += "\":";
    serializeValue(kv.second, out);
  }
  out.push_back('}');
}

}  // namespace

bool parseJson(const std::string& input, Json& out, std::string& error) {
  Parser parser(input);
  return parser.parse(out, error);
}

std::string serializeJson(const Json& value) {
  std::string out;
  out.reserve(1024);
  serializeValue(value, out);
  return out;
}

bool parseRpcRequest(const std::string& input, RpcRequest& out, std::string& error) {
  Json root;
  if (!parseJson(input, root, error)) return false;
  if (!root.isObject()) {
    error = "JSON-RPC request must be an object";
    return false;
  }

  const Json* jsonrpc = root.get("jsonrpc");
  const Json* id = root.get("id");
  const Json* method = root.get("method");
  const Json* params = root.get("params");

  if (!jsonrpc || !jsonrpc->isString() || jsonrpc->asString() != "2.0") {
    error = "Missing or invalid jsonrpc field";
    return false;
  }
  if (!id) {
    error = "Missing id field";
    return false;
  }
  if (!method || !method->isString()) {
    error = "Missing or invalid method field";
    return false;
  }

  out.id = *id;
  out.method = method->asString();
  out.params = params ? *params : Json(nullptr);
  return true;
}

std::string makeRpcSuccess(const Json& id, const Json& result) {
  Json::object_t root;
  root["jsonrpc"] = Json("2.0");
  root["id"] = id;
  root["result"] = result;
  return serializeJson(Json(std::move(root)));
}

std::string makeRpcError(const Json& id, int code, const std::string& message) {
  Json::object_t err;
  err["code"] = Json(code);
  err["message"] = Json(message);

  Json::object_t root;
  root["jsonrpc"] = Json("2.0");
  root["id"] = id;
  root["error"] = Json(std::move(err));
  return serializeJson(Json(std::move(root)));
}

}  // namespace jsonrpc
