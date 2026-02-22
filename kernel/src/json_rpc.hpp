#pragma once

#include <map>
#include <optional>
#include <string>
#include <variant>
#include <vector>

namespace jsonrpc {

namespace RpcErrorCode {
constexpr int kParseError = -32700;
constexpr int kMethodNotFound = -32601;
constexpr int kInvalidParams = -32602;
}  // namespace RpcErrorCode

class Json {
 public:
  using array_t = std::vector<Json>;
  using object_t = std::map<std::string, Json>;
  using value_t = std::variant<std::nullptr_t, bool, double, std::string, array_t, object_t>;

  Json();
  Json(std::nullptr_t);
  Json(bool v);
  Json(double v);
  Json(int v);
  Json(std::string v);
  Json(const char* v);
  Json(array_t v);
  Json(object_t v);

  bool isNull() const;
  bool isBool() const;
  bool isNumber() const;
  bool isString() const;
  bool isArray() const;
  bool isObject() const;

  bool asBool() const;
  double asNumber() const;
  const std::string& asString() const;
  const array_t& asArray() const;
  const object_t& asObject() const;

  const Json* get(const std::string& key) const;
  Json* get(const std::string& key);

 private:
  value_t value_;
};

struct RpcRequest {
  Json id;
  std::string method;
  Json params;
};

Json parseJson(const std::string& input);
std::string serializeJson(const Json& value);

RpcRequest parseRpcRequest(const std::string& input);
std::string makeRpcSuccess(const Json& id, const Json& result);
std::string makeRpcError(const Json& id, int code, const std::string& message);

}  // namespace jsonrpc
