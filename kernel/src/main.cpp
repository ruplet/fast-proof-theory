#include <algorithm>
#include <cctype>
#include <iostream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "document_codec.hpp"
#include "json_rpc.hpp"
#include "proof_system.hpp"
#include "proof_types.hpp"

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
  LogicId logic;
  CalculusId calculus;
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

static std::string toLowerAscii(const std::string& s) {
  std::string out = s;
  for (size_t i = 0; i < out.size(); i++) {
    out[i] = static_cast<char>(std::tolower(static_cast<unsigned char>(out[i])));
  }
  return out;
}

static std::string parenthesizeIfNeeded(int precedence, int parentPrecedence, const std::string& inner) {
  if (precedence < parentPrecedence) return "(" + inner + ")";
  return inner;
}

static std::string renderFormula(const std::shared_ptr<Formula>& f, int parentPrec = 0) {
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
      return parenthesizeIfNeeded(2, parentPrec,
                                  renderFormula(f->left, 2) + " ⊗ " + renderFormula(f->right, 2));
    case FormulaKind::With:
      return parenthesizeIfNeeded(1, parentPrec,
                                  renderFormula(f->left, 1) + " & " + renderFormula(f->right, 1));
    case FormulaKind::Plus:
      return parenthesizeIfNeeded(1, parentPrec,
                                  renderFormula(f->left, 1) + " ⊕ " + renderFormula(f->right, 1));
    case FormulaKind::Lolli:
      return parenthesizeIfNeeded(0, parentPrec,
                                  renderFormula(f->left, 0) + " ⊸ " + renderFormula(f->right, 0));
  }

  return "";
}

enum class TacticKind {
  InitOrAxiom,
  SplitOrTensor,
  With,
  LeftOrInl,
  RightOrInr,
  Bang,
  Trivial,
  Derelict,
  DestructOrCases,
  Assume,
  Intro,
  Apply,
  Translate,
  Unknown,
};

static TacticKind parseTacticKind(const std::string& normalizedName) {
  static const std::unordered_map<std::string, TacticKind> kDispatchTable = {
      {"init", TacticKind::InitOrAxiom},
      {"axiom", TacticKind::InitOrAxiom},
      {"split", TacticKind::SplitOrTensor},
      {"tensor", TacticKind::SplitOrTensor},
      {"⊗", TacticKind::SplitOrTensor},
      {"with", TacticKind::With},
      {"&", TacticKind::With},
      {"left", TacticKind::LeftOrInl},
      {"inl", TacticKind::LeftOrInl},
      {"plus_left", TacticKind::LeftOrInl},
      {"right", TacticKind::RightOrInr},
      {"inr", TacticKind::RightOrInr},
      {"plus_right", TacticKind::RightOrInr},
      {"bang", TacticKind::Bang},
      {"!", TacticKind::Bang},
      {"trivial", TacticKind::Trivial},
      {"derelict", TacticKind::Derelict},
      {"destruct", TacticKind::DestructOrCases},
      {"cases", TacticKind::DestructOrCases},
      {"assume", TacticKind::Assume},
      {"intro", TacticKind::Intro},
      {"apply", TacticKind::Apply},
      {"translate", TacticKind::Translate},
      {"translate_to", TacticKind::Translate},
  };

  auto it = kDispatchTable.find(normalizedName);
  if (it == kDispatchTable.end()) return TacticKind::Unknown;
  return it->second;
}

static RuleId ruleForTacticKind(TacticKind kind) {
  switch (kind) {
    case TacticKind::InitOrAxiom:
      return RuleId::InitOrAxiom;
    case TacticKind::SplitOrTensor:
      return RuleId::SplitOrTensor;
    case TacticKind::With:
      return RuleId::With;
    case TacticKind::LeftOrInl:
      return RuleId::LeftOrInl;
    case TacticKind::RightOrInr:
      return RuleId::RightOrInr;
    case TacticKind::Bang:
      return RuleId::Bang;
    case TacticKind::Trivial:
      return RuleId::Trivial;
    case TacticKind::Derelict:
      return RuleId::Derelict;
    case TacticKind::DestructOrCases:
      return RuleId::DestructOrCases;
    case TacticKind::Assume:
      return RuleId::Assume;
    case TacticKind::Intro:
      return RuleId::Intro;
    case TacticKind::Apply:
      return RuleId::Apply;
    case TacticKind::Translate:
      return RuleId::Translate;
    case TacticKind::Unknown:
      return RuleId::InitOrAxiom;
  }
  return RuleId::InitOrAxiom;
}

struct TranslateTarget {
  LogicId logic;
  CalculusId calculus;
};

static TranslateTarget parseTranslateTarget(const std::vector<std::string>& args,
                                            LogicId currentLogic,
                                            CalculusId currentCalculus) {
  if (args.empty()) {
    throw std::invalid_argument("translate expects at least one argument.");
  }

  if (args.size() == 1) {
    const std::string& token = args[0];
    try {
      LogicId logic = parseLogicId(token);
      try {
        lookupProofProfile(logic, currentCalculus);
        return {logic, currentCalculus};
      } catch (...) {
        return {logic, defaultCalculusForLogic(logic)};
      }
    } catch (...) {
      // Not a logic token.
    }

    try {
      CalculusId calculus = parseCalculusId(token);
      lookupProofProfile(currentLogic, calculus);
      return {currentLogic, calculus};
    } catch (...) {
      // Not a calculus token or incompatible with current logic.
    }

    throw std::invalid_argument("Unknown translate target \"" + token +
                                "\". Use LOGIC or CALCULUS or LOGIC CALCULUS.");
  }

  if (args.size() == 2) {
    LogicId logic = parseLogicId(args[0]);
    CalculusId calculus = parseCalculusId(args[1]);
    lookupProofProfile(logic, calculus);
    return {logic, calculus};
  }

  if (args.size() == 3) {
    const std::string connector = toLowerAscii(args[1]);
    if (connector != "in" && connector != "with" && connector != "via") {
      throw std::invalid_argument("translate 3-argument form expects connector in|with|via.");
    }
    LogicId logic = parseLogicId(args[0]);
    CalculusId calculus = parseCalculusId(args[2]);
    lookupProofProfile(logic, calculus);
    return {logic, calculus};
  }

  throw std::invalid_argument("translate accepts one, two, or three arguments.");
}

static GoalNode makeGoalNode(int& goalCounter,
                             const std::shared_ptr<Formula>& formula,
                             const std::vector<InternalHypothesis>& ctx,
                             LogicId logic,
                             CalculusId calculus) {
  return GoalNode{"g" + std::to_string(++goalCounter), ctx, formula, logic, calculus};
}

static void prependGoals(std::vector<GoalNode>& goals, const std::vector<GoalNode>& newGoals) {
  std::vector<GoalNode> combined = newGoals;
  combined.insert(combined.end(), goals.begin(), goals.end());
  goals = std::move(combined);
}

static void restoreGoalFront(std::vector<GoalNode>& goals, const GoalNode& goal) {
  goals.insert(goals.begin(), goal);
}

static std::string makeFreshName(const std::vector<InternalHypothesis>& existing, const std::string& base) {
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
}

static int findHypIndex(const std::vector<InternalHypothesis>& ctx, const std::string& hName) {
  for (size_t i = 0; i < ctx.size(); i++) {
    if (ctx[i].name == hName) return static_cast<int>(i);
  }
  return -1;
}

class ProofEngine {
 public:
  explicit ProofEngine(LogicId logic, CalculusId calculus) : defaultLogic_(logic), defaultCalculus_(calculus) {}

  void addError(int line, const std::string& msg) { errors_.push_back({line, msg}); }

  void addHyp(const std::string& name, const std::shared_ptr<Formula>& formula) {
    InternalHypothesis hyp{name, renderFormula(formula), formula};
    globalHyps_.push_back(hyp);
    for (auto& g : goals_) g.ctx.push_back(hyp);
  }

  void addGoal(const std::shared_ptr<Formula>& target) {
    goals_.push_back(
        {"g" + std::to_string(++goalCounter_), globalHyps_, target, defaultLogic_, defaultCalculus_});
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

    GoalNode goal = goals_.front();
    goals_.erase(goals_.begin());
    std::vector<InternalHypothesis> ctx = goal.ctx;
    std::shared_ptr<Formula> target = goal.target;
    LogicId goalLogic = goal.logic;
    CalculusId goalCalculus = goal.calculus;
    const std::string normalized = toLowerAscii(name);
    TacticKind tacticKind = parseTacticKind(normalized);

    if (tacticKind != TacticKind::Unknown &&
        !isRuleAllowed(goalLogic, goalCalculus, ruleForTacticKind(tacticKind))) {
      const ProofChildrenContainerId children =
          lookupProofProfile(goalLogic, goalCalculus).childrenContainer;
      addError(line, "Rule \"" + normalized + "\" is not allowed in proof profile " +
                         proofProfileDisplayName(goalLogic, goalCalculus) + " (children: " +
                         proofChildrenContainerDisplayName(children) + ").");
      restoreGoalFront(goals_, goal);
      return;
    }

    switch (tacticKind) {
      case TacticKind::InitOrAxiom: {
        const std::string hypName = argWords.empty() ? "" : argWords[0];
        InternalHypothesis* hyp = nullptr;
        if (hypName.empty()) {
          for (auto& h : ctx) {
            if (formulaPtrEqual(h.formula, target)) {
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
          restoreGoalFront(goals_, goal);
          return;
        }

        prependGoals(goals_, {});
        return;
      }
      case TacticKind::SplitOrTensor: {
        if (target->kind == FormulaKind::Tensor) {
          std::unordered_set<std::string> chosen;
          for (const auto& n : argWords) {
            if (chosen.count(n)) {
              addError(line, "Hypothesis \"" + n + "\" listed multiple times.");
              restoreGoalFront(goals_, goal);
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
              restoreGoalFront(goals_, goal);
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

          prependGoals(
              goals_,
              {makeGoalNode(goalCounter_, target->left, firstCtx, goalLogic, goalCalculus),
               makeGoalNode(goalCounter_, target->right, secondCtx, goalLogic, goalCalculus)});
          return;
        }

        if (target->kind == FormulaKind::With) {
          prependGoals(goals_,
                       {makeGoalNode(goalCounter_, target->left, ctx, goalLogic, goalCalculus),
                        makeGoalNode(goalCounter_, target->right, ctx, goalLogic, goalCalculus)});
          return;
        }

        addError(line, "Current goal is not a tensor (⊗) or with (&).");
        restoreGoalFront(goals_, goal);
        return;
      }
      case TacticKind::With: {
        if (target->kind == FormulaKind::With) {
          prependGoals(goals_,
                       {makeGoalNode(goalCounter_, target->left, ctx, goalLogic, goalCalculus),
                        makeGoalNode(goalCounter_, target->right, ctx, goalLogic, goalCalculus)});
          return;
        }
        addError(line, "Current goal is not a with (&).");
        restoreGoalFront(goals_, goal);
        return;
      }
      case TacticKind::LeftOrInl: {
        if (target->kind == FormulaKind::Plus) {
          prependGoals(goals_, {makeGoalNode(goalCounter_, target->left, ctx, goalLogic, goalCalculus)});
          return;
        }
        addError(line, "left/inl applies only to ⊕ goals.");
        restoreGoalFront(goals_, goal);
        return;
      }
      case TacticKind::RightOrInr: {
        if (target->kind == FormulaKind::Plus) {
          prependGoals(goals_, {makeGoalNode(goalCounter_, target->right, ctx, goalLogic, goalCalculus)});
          return;
        }
        addError(line, "right/inr applies only to ⊕ goals.");
        restoreGoalFront(goals_, goal);
        return;
      }
      case TacticKind::Bang: {
        if (!argWords.empty()) {
          const std::string& hName = argWords[0];
          int idx = findHypIndex(ctx, hName);
          if (idx == -1) {
            addError(line, "Unknown hypothesis \"" + hName + "\".");
            restoreGoalFront(goals_, goal);
            return;
          }
          InternalHypothesis hyp = ctx[static_cast<size_t>(idx)];
          if (hyp.formula->kind != FormulaKind::Bang) {
            addError(line, "Hypothesis \"" + hName + "\" is not a bang.");
            restoreGoalFront(goals_, goal);
            return;
          }
          std::string newName = makeFreshName(ctx, hName + "_derelict");
          ctx.push_back({newName, renderFormula(hyp.formula->of), hyp.formula->of});
          prependGoals(goals_, {GoalNode{goal.id, ctx, goal.target, goalLogic, goalCalculus}});
          return;
        }

        if (target->kind == FormulaKind::Bang) {
          prependGoals(goals_, {makeGoalNode(goalCounter_, target->of, ctx, goalLogic, goalCalculus)});
          return;
        }

        addError(line, "bang applies only to ! goals or as `bang <hyp>` for dereliction.");
        restoreGoalFront(goals_, goal);
        return;
      }
      case TacticKind::Trivial: {
        if (target->kind == FormulaKind::One || target->kind == FormulaKind::Top) {
          prependGoals(goals_, {});
          return;
        }
        addError(line, "trivial only solves 1 or ⊤.");
        restoreGoalFront(goals_, goal);
        return;
      }
      case TacticKind::Derelict: {
        if (target->kind != FormulaKind::Bang) {
          addError(line, "derelict applies only to ! goals.");
          restoreGoalFront(goals_, goal);
          return;
        }
        for (const auto& h : ctx) {
          if (h.formula->kind != FormulaKind::Bang) {
            addError(line, "derelict requires all assumptions to be bangs.");
            restoreGoalFront(goals_, goal);
            return;
          }
        }
        prependGoals(goals_, {makeGoalNode(goalCounter_, target->of, ctx, goalLogic, goalCalculus)});
        return;
      }
      case TacticKind::DestructOrCases: {
        if (argWords.empty()) {
          addError(line, normalized + " requires a hypothesis name.");
          restoreGoalFront(goals_, goal);
          return;
        }

        const std::string& hName = argWords[0];
        int hypIdx = findHypIndex(ctx, hName);
        if (hypIdx == -1) {
          addError(line, "Unknown hypothesis \"" + hName + "\".");
          restoreGoalFront(goals_, goal);
          return;
        }

        InternalHypothesis hyp = ctx[static_cast<size_t>(hypIdx)];
        std::vector<InternalHypothesis> withoutHyp;
        for (size_t i = 0; i < ctx.size(); i++) {
          if (static_cast<int>(i) != hypIdx) withoutHyp.push_back(ctx[i]);
        }
        std::vector<std::string> extra(argWords.begin() + 1, argWords.end());

        if (hyp.formula->kind == FormulaKind::Tensor) {
          std::vector<InternalHypothesis> newCtx = withoutHyp;
          std::string leftName = makeFreshName(newCtx, hName + "_left");
          newCtx.push_back({leftName, renderFormula(hyp.formula->left), hyp.formula->left});
          std::string rightName = makeFreshName(newCtx, hName + "_right");
          newCtx.push_back({rightName, renderFormula(hyp.formula->right), hyp.formula->right});
          prependGoals(goals_, {GoalNode{goal.id, newCtx, goal.target, goalLogic, goalCalculus}});
          return;
        }

        if (hyp.formula->kind == FormulaKind::With) {
          if (extra.empty()) {
            addError(line, "destruct on & requires choosing a branch (\"left\" or \"right\").");
            restoreGoalFront(goals_, goal);
            return;
          }
          std::string branch = toLowerAscii(extra[0]);
          if (branch != "left" && branch != "right") {
            addError(line, "destruct on & requires choosing a branch (\"left\" or \"right\").");
            restoreGoalFront(goals_, goal);
            return;
          }

          std::shared_ptr<Formula> selected = branch == "left" ? hyp.formula->left : hyp.formula->right;
          std::vector<InternalHypothesis> newCtx = withoutHyp;
          std::string newName = makeFreshName(newCtx, hName + "_" + branch);
          newCtx.push_back({newName, renderFormula(selected), selected});
          prependGoals(goals_, {GoalNode{goal.id, newCtx, goal.target, goalLogic, goalCalculus}});
          return;
        }

        if (hyp.formula->kind == FormulaKind::Plus) {
          std::vector<InternalHypothesis> firstCtx = withoutHyp;
          std::vector<InternalHypothesis> secondCtx = withoutHyp;
          std::string leftName = makeFreshName(firstCtx, hName + "_left");
          firstCtx.push_back({leftName, renderFormula(hyp.formula->left), hyp.formula->left});
          std::string rightName = makeFreshName(secondCtx, hName + "_right");
          secondCtx.push_back({rightName, renderFormula(hyp.formula->right), hyp.formula->right});
          prependGoals(goals_, {GoalNode{goal.id, firstCtx, goal.target, goalLogic, goalCalculus},
                                GoalNode{goal.id, secondCtx, goal.target, goalLogic, goalCalculus}});
          return;
        }

        if (hyp.formula->kind == FormulaKind::Lolli) {
          std::unordered_set<std::string> chosen;
          for (const auto& n : extra) {
            if (chosen.count(n)) {
              addError(line, "Hypothesis \"" + n + "\" listed multiple times.");
              restoreGoalFront(goals_, goal);
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
              restoreGoalFront(goals_, goal);
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

          prependGoals(goals_, {makeGoalNode(goalCounter_, hyp.formula->left, firstCtx, goalLogic, goalCalculus),
                                GoalNode{goal.id, secondCtx, goal.target, goalLogic, goalCalculus}});
          return;
        }

        addError(line, "destruct/cases not supported for hypothesis \"" + hName + "\".");
        restoreGoalFront(goals_, goal);
        return;
      }
      case TacticKind::Assume: {
        if (assumeName.empty() || !assumeFormula) {
          addError(line, "assume requires structured assume_name + assume_formula.");
          restoreGoalFront(goals_, goal);
          return;
        }

        std::unordered_set<std::string> chosen;
        for (const auto& n : argWords) {
          if (chosen.count(n)) {
            addError(line, "Hypothesis \"" + n + "\" listed multiple times.");
            restoreGoalFront(goals_, goal);
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
            restoreGoalFront(goals_, goal);
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
        prependGoals(goals_, {makeGoalNode(goalCounter_, assumeFormula, firstCtx, goalLogic, goalCalculus),
                              makeGoalNode(goalCounter_, target, secondCtx, goalLogic, goalCalculus)});
        return;
      }
      case TacticKind::Intro: {
        if (target->kind != FormulaKind::Lolli) {
          addError(line, "intro applies only to lollipop (⊸) goals.");
          restoreGoalFront(goals_, goal);
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
        prependGoals(goals_, {makeGoalNode(goalCounter_, target->right, ctx, goalLogic, goalCalculus)});
        return;
      }
      case TacticKind::Apply: {
        if (argWords.empty()) {
          addError(line, "apply requires a hypothesis name.");
          restoreGoalFront(goals_, goal);
          return;
        }

        int idx = findHypIndex(ctx, argWords[0]);
        if (idx == -1) {
          addError(line, "Unknown hypothesis \"" + argWords[0] + "\".");
          restoreGoalFront(goals_, goal);
          return;
        }

        InternalHypothesis hyp = ctx[static_cast<size_t>(idx)];
        if (hyp.formula->kind != FormulaKind::Lolli) {
          addError(line, "Hypothesis \"" + argWords[0] + "\" is not an implication.");
          restoreGoalFront(goals_, goal);
          return;
        }
        if (!formulaPtrEqual(hyp.formula->right, target)) {
          addError(line, "Hypothesis \"" + argWords[0] + "\" does not conclude the current goal.");
          restoreGoalFront(goals_, goal);
          return;
        }

        ctx.erase(ctx.begin() + idx);
        prependGoals(goals_, {makeGoalNode(goalCounter_, hyp.formula->left, ctx, goalLogic, goalCalculus)});
        return;
      }
      case TacticKind::Translate: {
        TranslateTarget targetProfile;
        try {
          targetProfile = parseTranslateTarget(argWords, goalLogic, goalCalculus);
        } catch (const std::exception& ex) {
          addError(line, ex.what());
          restoreGoalFront(goals_, goal);
          return;
        }

        std::shared_ptr<Formula> translated;
        try {
          translated = translateFormula(target,
                                        goalLogic,
                                        goalCalculus,
                                        targetProfile.logic,
                                        targetProfile.calculus);
        } catch (const std::exception& ex) {
          addError(line, ex.what());
          restoreGoalFront(goals_, goal);
          return;
        }

        prependGoals(goals_,
                     {GoalNode{goal.id, ctx, translated, targetProfile.logic, targetProfile.calculus}});
        return;
      }
      case TacticKind::Unknown:
      default:
        addError(line, "Unknown tactic \"" + name + "\".");
        restoreGoalFront(goals_, goal);
        return;
    }
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
  LogicId defaultLogic_;
  CalculusId defaultCalculus_;
};

namespace {

using jsonrpc::Json;

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

void resolveTheoremProfile(const InputTheorem& theorem, LogicId& logicOut, CalculusId& calculusOut) {
  const bool hasLogic = !theorem.logic.empty();
  const bool hasCalculus = !theorem.calculus.empty();

  if (hasLogic && hasCalculus) {
    logicOut = parseLogicId(theorem.logic);
    calculusOut = parseCalculusId(theorem.calculus);
    lookupProofProfile(logicOut, calculusOut);
    return;
  }

  if (hasLogic && !hasCalculus) {
    logicOut = parseLogicId(theorem.logic);
    calculusOut = defaultCalculusForLogic(logicOut);
    lookupProofProfile(logicOut, calculusOut);
    return;
  }

  if (!hasLogic && hasCalculus) {
    throw std::invalid_argument("Theorem \"" + theorem.name +
                                "\" sets calculus without logic; provide both.");
  }

  throw std::invalid_argument("Theorem \"" + theorem.name +
                              "\" must define both logic and calculus.");
}

EvaluationResult evaluateDocument(const InputDocument& doc) {
  EvaluationResult out;

  for (const auto& theorem : doc.theorems) {
    LogicId theoremLogic;
    CalculusId theoremCalculus;
    try {
      resolveTheoremProfile(theorem, theoremLogic, theoremCalculus);
    } catch (const std::exception& ex) {
      out.diagnostics.push_back(
          {0, 0, 0, 1, 1, "KERNEL_PROFILE", "kernel", ex.what()});
      continue;
    }

    ProofEngine engine(theoremLogic, theoremCalculus);

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
    std::cout << jsonrpc::makeRpcError(jsonrpc::Json(nullptr), jsonrpc::RpcErrorCode::kParseError,
                                       "Parse error: empty request")
              << "\n";
    return 0;
  }

  jsonrpc::RpcRequest request;
  try {
    request = jsonrpc::parseRpcRequest(input);
  } catch (const std::exception& ex) {
    std::cout << jsonrpc::makeRpcError(jsonrpc::Json(nullptr), jsonrpc::RpcErrorCode::kParseError,
                                       "Parse error: " + std::string(ex.what()))
              << "\n";
    return 0;
  }

  if (request.method != "checkDocument") {
    std::cout << jsonrpc::makeRpcError(request.id, jsonrpc::RpcErrorCode::kMethodNotFound,
                                       "Method not found: " + request.method)
              << "\n";
    return 0;
  }

  InputDocument document;
  try {
    DocumentCodec::deserializeDocumentParams(request.params, document);
  } catch (const std::exception& ex) {
    std::cout << jsonrpc::makeRpcError(request.id, jsonrpc::RpcErrorCode::kInvalidParams,
                                       "Invalid params: " + std::string(ex.what()))
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
