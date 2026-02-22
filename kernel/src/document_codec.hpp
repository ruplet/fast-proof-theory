#pragma once

#include <string>

#include "json_rpc.hpp"
#include "proof_types.hpp"

class DocumentCodec {
 public:
  static void deserializeDocumentParams(const jsonrpc::Json& params, InputDocument& out);
};
