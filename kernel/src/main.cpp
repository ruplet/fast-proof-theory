#include <algorithm>
#include <cctype>
#include <iostream>
#include <memory>
#include <optional>
#include <sstream>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

#include "json_rpc.hpp"

enum class FormulaKind {
  Atom,
  Tensor,
  With,
  Plus,
  Lolli,
  Bang,
  One,
  Bot,
  Top,
  Zero,
};

struct Formula {
  FormulaKind kind;
  std::string name;
  bool negated = false;
  std::shared_ptr<Formula> left;
  std::shared_ptr<Formula> right;
  std::shared_ptr<Formula> of;
};

struct Hypothesis {
  std::string name;
  std::string type;
};

struct Goal {
  std::string id;
  std::vector<Hypothesis> hypotheses;
  std::string target;
};

struct InternalHypothesis {
  std::string name;
  std::string type;
  std::shared_ptr<Formula> formula;
};

struct GoalNode {
  std::string id;
  std::vector<InternalHypothesis> ctx;
  std::shared_ptr<Formula> target;
};

struct EngineError {
  int line = 0;
  std::string message;
};

struct EngineResult {
  std::vector<Goal> goals;
  std::vector<EngineError> errors;
};

struct Diagnostic {
  int sl = 0;
  int sc = 0;
  int el = 0;
  int ec = 0;
  int severity = 1;
  std::string code;
  std::string source;
  std::string message;
};

struct InputRange {
  int sl = 0;
  int sc = 0;
  int el = 0;
  int ec = 0;
};

struct InputHypDecl {
  std::string name;
  std::shared_ptr<Formula> formula;
  InputRange range;
};

struct InputGoalDecl {
  std::shared_ptr<Formula> formula;
  InputRange range;
};

struct InputTactic {
  std::string name;
  std::vector<std::string> args;
  InputRange range;
  std::string assumeName;
  std::shared_ptr<Formula> assumeFormula;
};

struct InputTheorem {
  std::string name;
  std::vector<InputHypDecl> hypotheses;
  std::vector<InputGoalDecl> goals;
  std::vector<InputTactic> tactics;
};

struct InputDocument {
  std::string uri;
  int version = 0;
  std::vector<InputTheorem> theorems;
};

static std::string toLowerAscii(const std::string& s) {
  std::string out = s;
  std::transform(out.begin(), out.end(), out.begin(), [](unsigned char c) {
    return static_cast<char>(std::tolower(c));
  });
  return out;
}

static bool formulaEquals(const std::shared_ptr<Formula>& a, const std::shared_ptr<Formula>& b) {
  if (!a || !b) return a == b;
  if (a->kind != b->kind) return false;

  switch (a->kind) {
    case FormulaKind::Atom:
      return a->name == b->name && a->negated == b->negated;
    case FormulaKind::Bang:
      return formulaEquals(a->of, b->of);
    case FormulaKind::Tensor:
    case FormulaKind::With:
    case FormulaKind::Plus:
    case FormulaKind::Lolli:
      return formulaEquals(a->left, b->left) && formulaEquals(a->right, b->right);
    default:
      return true;
  }
}

static std::string renderFormula(const std::shared_ptr<Formula>& f, int parentPrec = 0) {
  auto paren = [&](int prec, const std::string& inner) {
    return prec < parentPrec ? "(" + inner + ")" : inner;
  };

  switch (f->kind) {
    case FormulaKind::Atom:
      return f->name + (f->negated ? "⊥" : "");
    case FormulaKind::One:
      return "1";
    case FormulaKind::Bot:
      return "⊥";
    case FormulaKind::Top:
      return "⊤";
    case FormulaKind::Zero:
      return "0";
    case FormulaKind::Bang:
      return "!" + renderFormula(f->of, 3);
    case FormulaKind::Tensor:
      return paren(2, renderFormula(f->left, 2) + " ⊗ " + renderFormula(f->right, 2));
    case FormulaKind::With:
      return paren(1, renderFormula(f->left, 1) + " & " + renderFormula(f->right, 1));
    case FormulaKind::Plus:
      return paren(1, renderFormula(f->left, 1) + " ⊕ " + renderFormula(f->right, 1));
    case FormulaKind::Lolli:
      return paren(0, renderFormula(f->left, 0) + " ⊸ " + renderFormula(f->right, 0));
  }

  return "";
}

class ProofEngine {
 public:
  void addError(int line, const std::string& msg) { errors_.push_back({line, msg}); }

  void addHyp(const std::string& name, const std::shared_ptr<Formula>& formula) {
    InternalHypothesis hyp{name, renderFormula(formula), formula};
    globalHyps_.push_back(hyp);
    for (auto& g : goals_) g.ctx.push_back(hyp);
  }

  void addGoal(const std::shared_ptr<Formula>& target) {
    goals_.push_back({"g" + std::to_string(++goalCounter_), globalHyps_, target});
  }

  void applyTactic(const std::string& name,
                   const std::vector<std::string>& argWords,
                   int line,
                   const std::string& assumeName,
                   const std::shared_ptr<Formula>& assumeFormula) {
    if (goals_.empty()) {
      addError(line, "No goals available for tactic \"" + name + "\".");
      return;
    }

    std::string normalized = toLowerAscii(name);
    GoalNode goal = goals_.front();
    goals_.erase(goals_.begin());
    std::vector<InternalHypothesis> ctx = goal.ctx;
    std::shared_ptr<Formula> target = goal.target;

    auto mkGoal = [&](const std::shared_ptr<Formula>& f,
                      const std::vector<InternalHypothesis>& updatedCtx) {
      return GoalNode{"g" + std::to_string(++goalCounter_), updatedCtx, f};
    };

    auto putBack = [&](const std::vector<GoalNode>& newGoals) {
      std::vector<GoalNode> combined = newGoals;
      combined.insert(combined.end(), goals_.begin(), goals_.end());
      goals_ = std::move(combined);
    };

    auto pushGoalBack = [&]() { goals_.insert(goals_.begin(), goal); };

    auto makeFreshName = [](const std::vector<InternalHypothesis>& existing,
                            const std::string& base) {
      int suffix = 1;
      std::string candidate = base + std::to_string(suffix);
      bool exists = true;
      while (exists) {
        exists = false;
        for (const auto& h : existing) {
          if (h.name == candidate) {
            exists = true;
            suffix += 1;
            candidate = base + std::to_string(suffix);
            break;
          }
        }
      }
      return candidate;
    };

    auto findHypIndex = [&](const std::string& hName) -> int {
      for (size_t i = 0; i < ctx.size(); i++) {
        if (ctx[i].name == hName) return static_cast<int>(i);
      }
      return -1;
    };

    auto closeWithHyp = [&](const std::string& hypName) {
      InternalHypothesis* hyp = nullptr;
      if (hypName.empty()) {
        for (auto& h : ctx) {
          if (formulaEquals(h.formula, target)) {
            hyp = &h;
            break;
          }
        }
      } else {
        for (auto& h : ctx) {
          if (h.name == hypName) {
            hyp = &h;
            break;
          }
        }
      }

      if (!hyp) {
        addError(line,
                 hypName.empty() ? "No hypothesis matches current goal."
                                 : "Hypothesis \"" + hypName + "\" does not match current goal.");
        pushGoalBack();
        return;
      }
      putBack({});
    };

    auto destructHyp = [&](const std::string& hName, const std::vector<std::string>& extra) {
      int hypIdx = findHypIndex(hName);
      if (hypIdx == -1) {
        addError(line, "Unknown hypothesis \"" + hName + "\".");
        pushGoalBack();
        return;
      }

      InternalHypothesis hyp = ctx[static_cast<size_t>(hypIdx)];
      std::vector<InternalHypothesis> withoutHyp;
      for (size_t i = 0; i < ctx.size(); i++) {
        if (static_cast<int>(i) != hypIdx) withoutHyp.push_back(ctx[i]);
      }

      if (hyp.formula->kind == FormulaKind::Tensor) {
        auto newCtx = withoutHyp;
        std::string leftName = makeFreshName(newCtx, hName + "_left");
        newCtx.push_back({leftName, renderFormula(hyp.formula->left), hyp.formula->left});
        std::string rightName = makeFreshName(newCtx, hName + "_right");
        newCtx.push_back({rightName, renderFormula(hyp.formula->right), hyp.formula->right});
        putBack({GoalNode{goal.id, newCtx, goal.target}});
        return;
      }

      if (hyp.formula->kind == FormulaKind::With) {
        if (extra.empty()) {
          addError(line, "destruct on & requires choosing a branch (\"left\" or \"right\").");
          pushGoalBack();
          return;
        }
        std::string branch = toLowerAscii(extra[0]);
        if (branch != "left" && branch != "right") {
          addError(line, "destruct on & requires choosing a branch (\"left\" or \"right\").");
          pushGoalBack();
          return;
        }

        auto selected = branch == "left" ? hyp.formula->left : hyp.formula->right;
        auto newCtx = withoutHyp;
        std::string newName = makeFreshName(newCtx, hName + "_" + branch);
        newCtx.push_back({newName, renderFormula(selected), selected});
        putBack({GoalNode{goal.id, newCtx, goal.target}});
        return;
      }

      if (hyp.formula->kind == FormulaKind::Plus) {
        auto firstCtx = withoutHyp;
        auto secondCtx = withoutHyp;
        std::string leftName = makeFreshName(firstCtx, hName + "_left");
        firstCtx.push_back({leftName, renderFormula(hyp.formula->left), hyp.formula->left});
        std::string rightName = makeFreshName(secondCtx, hName + "_right");
        secondCtx.push_back({rightName, renderFormula(hyp.formula->right), hyp.formula->right});
        putBack({GoalNode{goal.id, firstCtx, goal.target}, GoalNode{goal.id, secondCtx, goal.target}});
        return;
      }

      if (hyp.formula->kind == FormulaKind::Lolli) {
        std::unordered_set<std::string> chosen;
        for (const auto& n : extra) {
          if (chosen.count(n)) {
            addError(line, "Hypothesis \"" + n + "\" listed multiple times.");
            pushGoalBack();
            return;
          }
          chosen.insert(n);
        }

        for (const auto& n : chosen) {
          bool exists = false;
          for (const auto& h : withoutHyp) {
            if (h.name == n) {
              exists = true;
              break;
            }
          }
          if (!exists) {
            addError(line, "Unknown hypothesis \"" + n + "\" in destruct.");
            pushGoalBack();
            return;
          }
        }

        std::vector<InternalHypothesis> firstCtx;
        std::vector<InternalHypothesis> secondCtx;
        for (const auto& h : withoutHyp) {
          if (chosen.count(h.name))
            firstCtx.push_back(h);
          else
            secondCtx.push_back(h);
        }

        std::string resName = makeFreshName(secondCtx, hName + "_res");
        secondCtx.push_back({resName, renderFormula(hyp.formula->right), hyp.formula->right});

        putBack({GoalNode{"g" + std::to_string(++goalCounter_), firstCtx, hyp.formula->left},
                 GoalNode{goal.id, secondCtx, goal.target}});
        return;
      }

      addError(line, "destruct/cases not supported for hypothesis \"" + hName + "\".");
      pushGoalBack();
    };

    if (normalized == "init" || normalized == "axiom") {
      closeWithHyp(argWords.empty() ? "" : argWords[0]);
      return;
    }

    if (normalized == "split" || normalized == "tensor" || normalized == "⊗") {
      if (target->kind == FormulaKind::Tensor) {
        std::unordered_set<std::string> chosen;
        for (const auto& n : argWords) {
          if (chosen.count(n)) {
            addError(line, "Hypothesis \"" + n + "\" listed multiple times.");
            pushGoalBack();
            return;
          }
          chosen.insert(n);
        }

        for (const auto& n : chosen) {
          bool exists = false;
          for (const auto& h : ctx) {
            if (h.name == n) {
              exists = true;
              break;
            }
          }
          if (!exists) {
            addError(line, "Unknown hypothesis \"" + n + "\" in split.");
            pushGoalBack();
            return;
          }
        }

        std::vector<InternalHypothesis> firstCtx;
        std::vector<InternalHypothesis> secondCtx;
        for (const auto& h : ctx) {
          if (chosen.count(h.name))
            firstCtx.push_back(h);
          else
            secondCtx.push_back(h);
        }

        putBack({mkGoal(target->left, firstCtx), mkGoal(target->right, secondCtx)});
        return;
      }

      if (target->kind == FormulaKind::With) {
        putBack({mkGoal(target->left, ctx), mkGoal(target->right, ctx)});
        return;
      }

      addError(line, "Current goal is not a tensor (⊗) or with (&)." );
      pushGoalBack();
      return;
    }

    if (normalized == "with" || normalized == "&") {
      if (target->kind == FormulaKind::With) {
        putBack({mkGoal(target->left, ctx), mkGoal(target->right, ctx)});
        return;
      }
      addError(line, "Current goal is not a with (&).");
      pushGoalBack();
      return;
    }

    if (normalized == "left" || normalized == "inl" || normalized == "plus_left") {
      if (target->kind == FormulaKind::Plus) {
        putBack({mkGoal(target->left, ctx)});
        return;
      }
      addError(line, "left/inl applies only to ⊕ goals.");
      pushGoalBack();
      return;
    }

    if (normalized == "right" || normalized == "inr" || normalized == "plus_right") {
      if (target->kind == FormulaKind::Plus) {
        putBack({mkGoal(target->right, ctx)});
        return;
      }
      addError(line, "right/inr applies only to ⊕ goals.");
      pushGoalBack();
      return;
    }

    if (normalized == "bang" || normalized == "!") {
      if (!argWords.empty()) {
        const std::string hName = argWords[0];
        int idx = findHypIndex(hName);
        if (idx == -1) {
          addError(line, "Unknown hypothesis \"" + hName + "\".");
          pushGoalBack();
          return;
        }
        auto hyp = ctx[static_cast<size_t>(idx)];
        if (hyp.formula->kind != FormulaKind::Bang) {
          addError(line, "Hypothesis \"" + hName + "\" is not a bang.");
          pushGoalBack();
          return;
        }
        std::string newName = makeFreshName(ctx, hName + "_derelict");
        ctx.push_back({newName, renderFormula(hyp.formula->of), hyp.formula->of});
        putBack({GoalNode{goal.id, ctx, goal.target}});
        return;
      }

      if (target->kind == FormulaKind::Bang) {
        putBack({mkGoal(target->of, ctx)});
        return;
      }

      addError(line, "bang applies only to ! goals or as `bang <hyp>` for dereliction.");
      pushGoalBack();
      return;
    }

    if (normalized == "trivial") {
      if (target->kind == FormulaKind::One || target->kind == FormulaKind::Top) {
        putBack({});
        return;
      }
      addError(line, "trivial only solves 1 or ⊤.");
      pushGoalBack();
      return;
    }

    if (normalized == "derelict") {
      if (target->kind != FormulaKind::Bang) {
        addError(line, "derelict applies only to ! goals.");
        pushGoalBack();
        return;
      }

      for (const auto& h : ctx) {
        if (h.formula->kind != FormulaKind::Bang) {
          addError(line, "derelict requires all assumptions to be bangs.");
          pushGoalBack();
          return;
        }
      }

      putBack({mkGoal(target->of, ctx)});
      return;
    }

    if (normalized == "destruct" || normalized == "cases") {
      if (argWords.empty()) {
        addError(line, normalized + " requires a hypothesis name.");
        pushGoalBack();
        return;
      }
      std::vector<std::string> extra(argWords.begin() + 1, argWords.end());
      destructHyp(argWords[0], extra);
      return;
    }

    if (normalized == "assume") {
      if (assumeName.empty() || !assumeFormula) {
        addError(line, "assume requires structured assume_name + assume_formula.");
        pushGoalBack();
        return;
      }

      std::unordered_set<std::string> chosen;
      for (const auto& n : argWords) {
        if (chosen.count(n)) {
          addError(line, "Hypothesis \"" + n + "\" listed multiple times.");
          pushGoalBack();
          return;
        }
        chosen.insert(n);
      }

      for (const auto& n : chosen) {
        bool exists = false;
        for (const auto& h : ctx) {
          if (h.name == n) {
            exists = true;
            break;
          }
        }
        if (!exists) {
          addError(line, "Unknown hypothesis \"" + n + "\" in assume.");
          pushGoalBack();
          return;
        }
      }

      std::vector<InternalHypothesis> firstCtx;
      std::vector<InternalHypothesis> secondCtx;
      for (const auto& h : ctx) {
        if (chosen.count(h.name))
          firstCtx.push_back(h);
        else
          secondCtx.push_back(h);
      }

      std::string fresh = assumeName;
      bool exists = true;
      int suffix = 1;
      while (exists) {
        exists = false;
        for (const auto& h : secondCtx) {
          if (h.name == fresh) {
            exists = true;
            suffix += 1;
            fresh = assumeName + std::to_string(suffix);
            break;
          }
        }
      }

      secondCtx.push_back({fresh, renderFormula(assumeFormula), assumeFormula});
      putBack({mkGoal(assumeFormula, firstCtx), mkGoal(target, secondCtx)});
      return;
    }

    if (normalized == "intro") {
      if (target->kind != FormulaKind::Lolli) {
        addError(line, "intro applies only to lollipop (⊸) goals.");
        pushGoalBack();
        return;
      }

      std::string hName = argWords.empty() ? "h" : argWords[0];
      std::string fresh = hName;
      bool exists = true;
      int suffix = 1;
      while (exists) {
        exists = false;
        for (const auto& h : ctx) {
          if (h.name == fresh) {
            exists = true;
            suffix += 1;
            fresh = hName + std::to_string(suffix);
            break;
          }
        }
      }

      ctx.push_back({fresh, renderFormula(target->left), target->left});
      putBack({mkGoal(target->right, ctx)});
      return;
    }

    if (normalized == "apply") {
      if (argWords.empty()) {
        addError(line, "apply requires a hypothesis name.");
        pushGoalBack();
        return;
      }

      int idx = findHypIndex(argWords[0]);
      if (idx == -1) {
        addError(line, "Unknown hypothesis \"" + argWords[0] + "\".");
        pushGoalBack();
        return;
      }

      auto hyp = ctx[static_cast<size_t>(idx)];
      if (hyp.formula->kind != FormulaKind::Lolli) {
        addError(line, "Hypothesis \"" + argWords[0] + "\" is not an implication.");
        pushGoalBack();
        return;
      }
      if (!formulaEquals(hyp.formula->right, target)) {
        addError(line, "Hypothesis \"" + argWords[0] + "\" does not conclude the current goal.");
        pushGoalBack();
        return;
      }

      ctx.erase(ctx.begin() + idx);
      putBack({mkGoal(hyp.formula->left, ctx)});
      return;
    }

    addError(line, "Unknown tactic \"" + name + "\".");
    pushGoalBack();
  }

  EngineResult finalize() {
    EngineResult out;
    out.errors = errors_;
    if (!errors_.empty()) return out;

    for (const auto& g : goals_) {
      Goal gv;
      gv.id = g.id;
      for (const auto& h : g.ctx) gv.hypotheses.push_back({h.name, h.type});
      gv.target = renderFormula(g.target);
      out.goals.push_back(gv);
    }
    return out;
  }

 private:
  std::vector<InternalHypothesis> globalHyps_;
  std::vector<GoalNode> goals_;
  std::vector<EngineError> errors_;
  int goalCounter_ = 0;
};

namespace {

using jsonrpc::Json;

bool getObject(const Json& parent,
               const std::string& field,
               const Json*& out,
               std::string& err,
               const std::string& path) {
  if (!parent.isObject()) {
    err = path + " must be an object";
    return false;
  }
  out = parent.get(field);
  if (!out) {
    err = "Missing field: " + path + "." + field;
    return false;
  }
  return true;
}

bool getString(const Json& parent,
               const std::string& field,
               std::string& out,
               std::string& err,
               const std::string& path) {
  const Json* node = nullptr;
  if (!getObject(parent, field, node, err, path)) return false;
  if (!node->isString()) {
    err = path + "." + field + " must be string";
    return false;
  }
  out = node->asString();
  return true;
}

bool getInt(const Json& parent,
            const std::string& field,
            int& out,
            std::string& err,
            const std::string& path) {
  const Json* node = nullptr;
  if (!getObject(parent, field, node, err, path)) return false;
  if (!node->isNumber()) {
    err = path + "." + field + " must be number";
    return false;
  }
  double raw = node->asNumber();
  int n = static_cast<int>(raw);
  if (raw != static_cast<double>(n)) {
    err = path + "." + field + " must be integer";
    return false;
  }
  out = n;
  return true;
}

bool parseRange(const Json& node, InputRange& out, std::string& err, const std::string& path) {
  const Json* start = nullptr;
  const Json* end = nullptr;
  if (!getObject(node, "start", start, err, path)) return false;
  if (!getObject(node, "end", end, err, path)) return false;

  if (!getInt(*start, "line", out.sl, err, path + ".start")) return false;
  if (!getInt(*start, "character", out.sc, err, path + ".start")) return false;
  if (!getInt(*end, "line", out.el, err, path + ".end")) return false;
  if (!getInt(*end, "character", out.ec, err, path + ".end")) return false;
  return true;
}

std::shared_ptr<Formula> parseFormula(const Json& node, std::string& err, const std::string& path) {
  if (!node.isObject()) {
    err = path + " must be object";
    return nullptr;
  }

  std::string kind;
  const Json* nodeTag = node.get("node");
  if (nodeTag) {
    if (!nodeTag->isString()) {
      err = path + ".node must be string";
      return nullptr;
    }
    kind = nodeTag->asString();
  } else {
    // Accept protobuf oneof-style payloads that omit the explicit discriminator.
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
    else {
      err = path + ".node missing and formula kind could not be inferred";
      return nullptr;
    }
  }

  auto make = []() { return std::make_shared<Formula>(); };
  auto f = make();

  if (kind == "atom") {
    const Json* atom = nullptr;
    if (!getObject(node, "atom", atom, err, path)) return nullptr;
    if (!getString(*atom, "name", f->name, err, path + ".atom")) return nullptr;
    const Json* neg = atom->get("negated");
    if (!neg || !neg->isBool()) {
      err = path + ".atom.negated must be bool";
      return nullptr;
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
    const Json* bang = nullptr;
    if (!getObject(node, "bang", bang, err, path)) return nullptr;
    const Json* child = bang->get("of");
    if (!child) {
      err = path + ".bang.of missing";
      return nullptr;
    }
    f->kind = FormulaKind::Bang;
    f->of = parseFormula(*child, err, path + ".bang.of");
    return f->of ? f : nullptr;
  }

  auto parseBinary = [&](const std::string& binField, FormulaKind outKind) -> std::shared_ptr<Formula> {
    const Json* bin = nullptr;
    if (!getObject(node, binField, bin, err, path)) return nullptr;
    const Json* left = bin->get("left");
    const Json* right = bin->get("right");
    if (!left || !right) {
      err = path + "." + binField + " needs left and right";
      return nullptr;
    }
    f->kind = outKind;
    f->left = parseFormula(*left, err, path + "." + binField + ".left");
    if (!f->left) return nullptr;
    f->right = parseFormula(*right, err, path + "." + binField + ".right");
    if (!f->right) return nullptr;
    return f;
  };

  if (kind == "tensor") return parseBinary("tensor", FormulaKind::Tensor);
  if (kind == "with") return parseBinary("with", FormulaKind::With);
  if (kind == "plus") return parseBinary("plus", FormulaKind::Plus);
  if (kind == "lolli") return parseBinary("lolli", FormulaKind::Lolli);

  err = path + ".node unknown formula kind: " + kind;
  return nullptr;
}

bool parseDocumentParams(const Json& params, InputDocument& out, std::string& err) {
  if (!params.isObject()) {
    err = "params must be object";
    return false;
  }

  const Json* doc = params.get("document");
  if (!doc) {
    err = "params.document missing";
    return false;
  }
  if (!doc->isObject()) {
    err = "params.document must be object";
    return false;
  }

  if (!getString(*doc, "uri", out.uri, err, "params.document")) return false;
  if (!getInt(*doc, "version", out.version, err, "params.document")) return false;

  const Json* theorems = doc->get("theorems");
  if (!theorems || !theorems->isArray()) {
    err = "params.document.theorems must be array";
    return false;
  }

  out.theorems.clear();
  const auto& theoremArray = theorems->asArray();
  for (size_t ti = 0; ti < theoremArray.size(); ti++) {
    const Json& t = theoremArray[ti];
    if (!t.isObject()) {
      err = "params.document.theorems[" + std::to_string(ti) + "] must be object";
      return false;
    }

    InputTheorem theorem;
    const std::string base = "params.document.theorems[" + std::to_string(ti) + "]";
    if (!getString(t, "name", theorem.name, err, base)) return false;

    const Json* hypotheses = t.get("hypotheses");
    if (!hypotheses || !hypotheses->isArray()) {
      err = base + ".hypotheses must be array";
      return false;
    }

    const Json* goals = t.get("goals");
    if (!goals || !goals->isArray()) {
      err = base + ".goals must be array";
      return false;
    }

    const Json* tactics = t.get("tactics");
    if (!tactics || !tactics->isArray()) {
      err = base + ".tactics must be array";
      return false;
    }

    for (size_t hi = 0; hi < hypotheses->asArray().size(); hi++) {
      const Json& h = hypotheses->asArray()[hi];
      if (!h.isObject()) {
        err = base + ".hypotheses[" + std::to_string(hi) + "] must be object";
        return false;
      }
      InputHypDecl hyp;
      const std::string hbase = base + ".hypotheses[" + std::to_string(hi) + "]";
      if (!getString(h, "name", hyp.name, err, hbase)) return false;
      const Json* formula = h.get("formula");
      if (!formula) {
        err = hbase + ".formula missing";
        return false;
      }
      hyp.formula = parseFormula(*formula, err, hbase + ".formula");
      if (!hyp.formula) return false;
      const Json* range = h.get("range");
      if (!range || !parseRange(*range, hyp.range, err, hbase + ".range")) return false;
      theorem.hypotheses.push_back(std::move(hyp));
    }

    for (size_t gi = 0; gi < goals->asArray().size(); gi++) {
      const Json& g = goals->asArray()[gi];
      if (!g.isObject()) {
        err = base + ".goals[" + std::to_string(gi) + "] must be object";
        return false;
      }
      InputGoalDecl goal;
      const std::string gbase = base + ".goals[" + std::to_string(gi) + "]";
      const Json* formula = g.get("formula");
      if (!formula) {
        err = gbase + ".formula missing";
        return false;
      }
      goal.formula = parseFormula(*formula, err, gbase + ".formula");
      if (!goal.formula) return false;
      const Json* range = g.get("range");
      if (!range || !parseRange(*range, goal.range, err, gbase + ".range")) return false;
      theorem.goals.push_back(std::move(goal));
    }

    for (size_t si = 0; si < tactics->asArray().size(); si++) {
      const Json& s = tactics->asArray()[si];
      if (!s.isObject()) {
        err = base + ".tactics[" + std::to_string(si) + "] must be object";
        return false;
      }
      InputTactic step;
      const std::string sbase = base + ".tactics[" + std::to_string(si) + "]";
      if (!getString(s, "name", step.name, err, sbase)) return false;
      const Json* args = s.get("args");
      if (!args || !args->isArray()) {
        err = sbase + ".args must be array";
        return false;
      }
      for (const auto& a : args->asArray()) {
        if (!a.isString()) {
          err = sbase + ".args entries must be strings";
          return false;
        }
        step.args.push_back(a.asString());
      }
      const Json* range = s.get("range");
      if (!range || !parseRange(*range, step.range, err, sbase + ".range")) return false;

      const Json* assumeName = s.get("assumeName");
      const Json* assumeFormula = s.get("assumeFormula");
      const std::string tacticKind = toLowerAscii(step.name);
      if (tacticKind == "assume") {
        if (!assumeName || !assumeName->isString() || assumeName->asString().empty() || !assumeFormula ||
            assumeFormula->isNull()) {
          err = sbase + ".assumeName and .assumeFormula must both be present for assume tactic";
          return false;
        }
        step.assumeName = assumeName->asString();
        step.assumeFormula = parseFormula(*assumeFormula, err, sbase + ".assumeFormula");
        if (!step.assumeFormula) return false;
      }

      theorem.tactics.push_back(std::move(step));
    }

    out.theorems.push_back(std::move(theorem));
  }

  return true;
}

jsonrpc::Json serializeDiagnostics(const std::vector<Diagnostic>& diagnostics) {
  Json::array_t out;
  for (const auto& d : diagnostics) {
    Json::object_t start;
    start["line"] = Json(d.sl);
    start["character"] = Json(d.sc);
    Json::object_t end;
    end["line"] = Json(d.el);
    end["character"] = Json(d.ec);
    Json::object_t range;
    range["start"] = Json(std::move(start));
    range["end"] = Json(std::move(end));

    Json::object_t item;
    item["range"] = Json(std::move(range));
    item["severity"] = Json(d.severity);
    item["code"] = Json(d.code);
    item["source"] = Json(d.source);
    item["message"] = Json(d.message);
    out.push_back(Json(std::move(item)));
  }
  return Json(std::move(out));
}

jsonrpc::Json serializeGoals(const std::vector<Goal>& goals) {
  Json::array_t out;
  for (const auto& g : goals) {
    Json::array_t hypotheses;
    for (const auto& h : g.hypotheses) {
      Json::object_t hyp;
      hyp["name"] = Json(h.name);
      hyp["type"] = Json(h.type);
      hypotheses.push_back(Json(std::move(hyp)));
    }

    Json::object_t item;
    item["id"] = Json(g.id);
    item["target"] = Json(g.target);
    item["hypotheses"] = Json(std::move(hypotheses));
    out.push_back(Json(std::move(item)));
  }
  return Json(std::move(out));
}

struct EvaluationResult {
  std::vector<Diagnostic> diagnostics;
  std::vector<Goal> goals;
};

EvaluationResult evaluateDocument(const InputDocument& doc) {
  EvaluationResult out;

  for (const auto& theorem : doc.theorems) {
    ProofEngine engine;

    for (const auto& h : theorem.hypotheses) {
      engine.addHyp(h.name, h.formula);
    }

    for (const auto& g : theorem.goals) {
      engine.addGoal(g.formula);
    }

    for (const auto& t : theorem.tactics) {
      engine.applyTactic(t.name, t.args, t.range.sl, t.assumeName, t.assumeFormula);
    }

    EngineResult result = engine.finalize();
    if (!result.errors.empty()) {
      for (const auto& e : result.errors) {
        out.diagnostics.push_back({e.line, 0, e.line, 1, 1, "KERNEL_PROOF", "kernel", e.message});
      }
      continue;
    }

    for (auto& g : result.goals) {
      g.id = theorem.name + ":" + g.id;
      out.goals.push_back(g);
    }
  }

  return out;
}

}  // namespace

int main() {
  std::ios::sync_with_stdio(false);

  std::string input;
  if (!std::getline(std::cin, input)) {
    std::cout << jsonrpc::makeRpcError(jsonrpc::Json(nullptr), -32700, "Parse error: empty request") << "\n";
    return 0;
  }

  jsonrpc::RpcRequest request;
  std::string parseError;
  if (!jsonrpc::parseRpcRequest(input, request, parseError)) {
    std::cout << jsonrpc::makeRpcError(jsonrpc::Json(nullptr), -32700,
                                       "Parse error: " + parseError)
              << "\n";
    return 0;
  }

  if (request.method != "checkDocument") {
    std::cout << jsonrpc::makeRpcError(request.id, -32601,
                                       "Method not found: " + request.method)
              << "\n";
    return 0;
  }

  InputDocument document;
  std::string validationError;
  if (!parseDocumentParams(request.params, document, validationError)) {
    std::cout << jsonrpc::makeRpcError(request.id, -32602,
                                       "Invalid params: " + validationError)
              << "\n";
    return 0;
  }

  EvaluationResult result = evaluateDocument(document);

  Json::object_t payload;
  payload["diagnostics"] = serializeDiagnostics(result.diagnostics);
  payload["goals"] = serializeGoals(result.goals);

  std::cout << jsonrpc::makeRpcSuccess(request.id, Json(std::move(payload))) << "\n";
  return 0;
}
