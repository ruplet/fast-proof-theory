#include "document_codec.hpp"

#include <cctype>
#include <memory>
#include <stdexcept>
#include <string>
#include <utility>

namespace {

using jsonrpc::Json;

std::string toLowerAscii(const std::string& s) {
  std::string out = s;
  for (size_t i = 0; i < out.size(); i++) {
    out[i] = static_cast<char>(std::tolower(static_cast<unsigned char>(out[i])));
  }
  return out;
}

const Json& requireObjectField(const Json& parent, const std::string& field, const std::string& path) {
  if (!parent.isObject()) {
    throw std::invalid_argument(path + " must be an object");
  }
  const Json* out = parent.get(field);
  if (!out) {
    throw std::invalid_argument("Missing field: " + path + "." + field);
  }
  return *out;
}

std::string requireStringField(const Json& parent, const std::string& field, const std::string& path) {
  const Json& node = requireObjectField(parent, field, path);
  if (!node.isString()) {
    throw std::invalid_argument(path + "." + field + " must be string");
  }
  return node.asString();
}

int requireIntField(const Json& parent, const std::string& field, const std::string& path) {
  const Json& node = requireObjectField(parent, field, path);
  if (!node.isNumber()) {
    throw std::invalid_argument(path + "." + field + " must be number");
  }
  double raw = node.asNumber();
  int n = static_cast<int>(raw);
  if (raw != static_cast<double>(n)) {
    throw std::invalid_argument(path + "." + field + " must be integer");
  }
  return n;
}

InputRange parseRange(const Json& node, const std::string& path) {
  InputRange out;
  const Json& start = requireObjectField(node, "start", path);
  const Json& end = requireObjectField(node, "end", path);

  out.sl = requireIntField(start, "line", path + ".start");
  out.sc = requireIntField(start, "character", path + ".start");
  out.el = requireIntField(end, "line", path + ".end");
  out.ec = requireIntField(end, "character", path + ".end");
  return out;
}

std::shared_ptr<Formula> parseFormula(const Json& node, const std::string& path);

std::shared_ptr<Formula> parseBinaryFormula(const Json& node,
                                            const std::string& path,
                                            const std::string& binField,
                                            FormulaKind outKind,
                                            const std::shared_ptr<Formula>& output) {
  const Json& bin = requireObjectField(node, binField, path);
  const Json* left = bin.get("left");
  const Json* right = bin.get("right");
  if (!left || !right) {
    throw std::invalid_argument(path + "." + binField + " needs left and right");
  }

  output->kind = outKind;
  output->left = parseFormula(*left, path + "." + binField + ".left");
  output->right = parseFormula(*right, path + "." + binField + ".right");
  return output;
}

std::shared_ptr<Formula> parseFormula(const Json& node, const std::string& path) {
  if (!node.isObject()) {
    throw std::invalid_argument(path + " must be object");
  }

  std::string kind;
  const Json* nodeTag = node.get("node");
  if (nodeTag) {
    if (!nodeTag->isString()) {
      throw std::invalid_argument(path + ".node must be string");
    }
    kind = nodeTag->asString();
  } else {
    if (node.get("atom"))
      kind = "atom";
    else if (node.get("tensor"))
      kind = "tensor";
    else if (node.get("with"))
      kind = "with";
    else if (node.get("plus"))
      kind = "plus";
    else if (node.get("lolli"))
      kind = "lolli";
    else if (node.get("bang"))
      kind = "bang";
    else if (node.get("one"))
      kind = "one";
    else if (node.get("top"))
      kind = "top";
    else if (node.get("bot"))
      kind = "bot";
    else if (node.get("zero"))
      kind = "zero";
    else
      throw std::invalid_argument(path + ".node missing and formula kind could not be inferred");
  }

  std::shared_ptr<Formula> f = std::make_shared<Formula>();

  if (kind == "atom") {
    const Json& atom = requireObjectField(node, "atom", path);
    f->name = requireStringField(atom, "name", path + ".atom");
    const Json* neg = atom.get("negated");
    if (!neg || !neg->isBool()) {
      throw std::invalid_argument(path + ".atom.negated must be bool");
    }
    f->kind = FormulaKind::Atom;
    f->negated = neg->asBool();
    return f;
  }

  if (kind == "one") {
    f->kind = FormulaKind::One;
    return f;
  }
  if (kind == "top") {
    f->kind = FormulaKind::Top;
    return f;
  }
  if (kind == "bot") {
    f->kind = FormulaKind::Bot;
    return f;
  }
  if (kind == "zero") {
    f->kind = FormulaKind::Zero;
    return f;
  }

  if (kind == "bang") {
    const Json& bang = requireObjectField(node, "bang", path);
    const Json* child = bang.get("of");
    if (!child) {
      throw std::invalid_argument(path + ".bang.of missing");
    }
    f->kind = FormulaKind::Bang;
    f->of = parseFormula(*child, path + ".bang.of");
    return f;
  }

  if (kind == "tensor") return parseBinaryFormula(node, path, "tensor", FormulaKind::Tensor, f);
  if (kind == "with") return parseBinaryFormula(node, path, "with", FormulaKind::With, f);
  if (kind == "plus") return parseBinaryFormula(node, path, "plus", FormulaKind::Plus, f);
  if (kind == "lolli") return parseBinaryFormula(node, path, "lolli", FormulaKind::Lolli, f);

  throw std::invalid_argument(path + ".node unknown formula kind: " + kind);
}

}  // namespace

void DocumentCodec::deserializeDocumentParams(const Json& params, InputDocument& out) {
  if (!params.isObject()) {
    throw std::invalid_argument("params must be object");
  }

  const Json* doc = params.get("document");
  if (!doc) {
    throw std::invalid_argument("params.document missing");
  }
  if (!doc->isObject()) {
    throw std::invalid_argument("params.document must be object");
  }

  out.uri = requireStringField(*doc, "uri", "params.document");
  out.version = requireIntField(*doc, "version", "params.document");

  const Json* theorems = doc->get("theorems");
  if (!theorems || !theorems->isArray()) {
    throw std::invalid_argument("params.document.theorems must be array");
  }

  out.theorems.clear();
  const auto& theoremArray = theorems->asArray();
  for (size_t ti = 0; ti < theoremArray.size(); ti++) {
    const Json& t = theoremArray[ti];
    if (!t.isObject()) {
      throw std::invalid_argument("params.document.theorems[" + std::to_string(ti) + "] must be object");
    }

    InputTheorem theorem;
    const std::string base = "params.document.theorems[" + std::to_string(ti) + "]";
    theorem.name = requireStringField(t, "name", base);
    theorem.proofSystem = "LL";
    const Json* proofSystem = t.get("proofSystem");
    if (proofSystem) {
      if (!proofSystem->isString()) {
        throw std::invalid_argument(base + ".proofSystem must be string");
      }
      theorem.proofSystem = proofSystem->asString();
    }

    const Json* hypotheses = t.get("hypotheses");
    if (!hypotheses || !hypotheses->isArray()) {
      throw std::invalid_argument(base + ".hypotheses must be array");
    }

    const Json* goals = t.get("goals");
    if (!goals || !goals->isArray()) {
      throw std::invalid_argument(base + ".goals must be array");
    }

    const Json* tactics = t.get("tactics");
    if (!tactics || !tactics->isArray()) {
      throw std::invalid_argument(base + ".tactics must be array");
    }

    for (size_t hi = 0; hi < hypotheses->asArray().size(); hi++) {
      const Json& h = hypotheses->asArray()[hi];
      if (!h.isObject()) {
        throw std::invalid_argument(base + ".hypotheses[" + std::to_string(hi) + "] must be object");
      }
      InputHypDecl hyp;
      const std::string hbase = base + ".hypotheses[" + std::to_string(hi) + "]";
      hyp.name = requireStringField(h, "name", hbase);
      const Json* formula = h.get("formula");
      if (!formula) {
        throw std::invalid_argument(hbase + ".formula missing");
      }
      hyp.formula = parseFormula(*formula, hbase + ".formula");
      const Json* range = h.get("range");
      if (!range) {
        throw std::invalid_argument(hbase + ".range missing");
      }
      hyp.range = parseRange(*range, hbase + ".range");
      theorem.hypotheses.push_back(std::move(hyp));
    }

    for (size_t gi = 0; gi < goals->asArray().size(); gi++) {
      const Json& g = goals->asArray()[gi];
      if (!g.isObject()) {
        throw std::invalid_argument(base + ".goals[" + std::to_string(gi) + "] must be object");
      }
      InputGoalDecl goal;
      const std::string gbase = base + ".goals[" + std::to_string(gi) + "]";
      const Json* formula = g.get("formula");
      if (!formula) {
        throw std::invalid_argument(gbase + ".formula missing");
      }
      goal.formula = parseFormula(*formula, gbase + ".formula");
      const Json* range = g.get("range");
      if (!range) {
        throw std::invalid_argument(gbase + ".range missing");
      }
      goal.range = parseRange(*range, gbase + ".range");
      theorem.goals.push_back(std::move(goal));
    }

    for (size_t si = 0; si < tactics->asArray().size(); si++) {
      const Json& s = tactics->asArray()[si];
      if (!s.isObject()) {
        throw std::invalid_argument(base + ".tactics[" + std::to_string(si) + "] must be object");
      }
      InputTactic step;
      const std::string sbase = base + ".tactics[" + std::to_string(si) + "]";
      step.name = requireStringField(s, "name", sbase);
      const Json* args = s.get("args");
      if (!args || !args->isArray()) {
        throw std::invalid_argument(sbase + ".args must be array");
      }
      for (const auto& a : args->asArray()) {
        if (!a.isString()) {
          throw std::invalid_argument(sbase + ".args entries must be strings");
        }
        step.args.push_back(a.asString());
      }
      const Json* range = s.get("range");
      if (!range) {
        throw std::invalid_argument(sbase + ".range missing");
      }
      step.range = parseRange(*range, sbase + ".range");

      const Json* assumeName = s.get("assumeName");
      const Json* assumeFormula = s.get("assumeFormula");
      const std::string tacticKind = toLowerAscii(step.name);
      if (tacticKind == "assume") {
        if (!assumeName || !assumeName->isString() || assumeName->asString().empty() || !assumeFormula ||
            assumeFormula->isNull()) {
          throw std::invalid_argument(sbase + ".assumeName and .assumeFormula must both be present for assume tactic");
        }
        step.assumeName = assumeName->asString();
        step.assumeFormula = parseFormula(*assumeFormula, sbase + ".assumeFormula");
      }

      theorem.tactics.push_back(std::move(step));
    }

    out.theorems.push_back(std::move(theorem));
  }
}
