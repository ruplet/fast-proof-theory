#include "proof_system.hpp"

#include <cctype>
#include <stdexcept>
#include <utility>

namespace {

const std::vector<LogicSpec> kLogics = {
    {LogicId::LinearLogic, "LL"},
    {LogicId::IntuitionisticPropositionalLogic, "IPC"},
    {LogicId::ClassicalPropositionalLogic, "CPC"},
    {LogicId::SimplyTypedLambdaCalculus, "STLC"},
};

const std::vector<CalculusSpec> kCalculi = {
    {CalculusId::NaturalDeduction, "ND"},
    {CalculusId::GentzenSequent, "GENTZEN"},
    {CalculusId::Hilbert, "HILBERT"},
    {CalculusId::Frege, "FREGE"},
};

const std::vector<ProofValidatorSpec> kProfiles = {
    {
        LogicId::LinearLogic,
        CalculusId::GentzenSequent,
        "LL/GENTZEN",
        ProofChildrenContainerId::SubproofChildren,
        {
            RuleId::InitOrAxiom,
            RuleId::SplitOrTensor,
            RuleId::With,
            RuleId::LeftOrInl,
            RuleId::RightOrInr,
            RuleId::Bang,
            RuleId::Trivial,
            RuleId::Derelict,
            RuleId::DestructOrCases,
            RuleId::Assume,
            RuleId::Intro,
            RuleId::Apply,
            RuleId::Translate,
        },
    },
    {
        LogicId::IntuitionisticPropositionalLogic,
        CalculusId::NaturalDeduction,
        "IPC/ND",
        ProofChildrenContainerId::SubproofChildren,
        {
            RuleId::InitOrAxiom,
            RuleId::With,
            RuleId::LeftOrInl,
            RuleId::RightOrInr,
            RuleId::Trivial,
            RuleId::DestructOrCases,
            RuleId::Assume,
            RuleId::Intro,
            RuleId::Apply,
            RuleId::Translate,
        },
    },
    {
        LogicId::IntuitionisticPropositionalLogic,
        CalculusId::GentzenSequent,
        "IPC/GENTZEN",
        ProofChildrenContainerId::SubproofChildren,
        {
            RuleId::InitOrAxiom,
            RuleId::With,
            RuleId::LeftOrInl,
            RuleId::RightOrInr,
            RuleId::Trivial,
            RuleId::DestructOrCases,
            RuleId::Assume,
            RuleId::Intro,
            RuleId::Apply,
            RuleId::Translate,
        },
    },
    {
        LogicId::IntuitionisticPropositionalLogic,
        CalculusId::Hilbert,
        "IPC/HILBERT",
        ProofChildrenContainerId::ReferencedLineChildren,
        {
            RuleId::InitOrAxiom,
            RuleId::Apply,
            RuleId::Translate,
        },
    },
    {
        LogicId::IntuitionisticPropositionalLogic,
        CalculusId::Frege,
        "IPC/FREGE",
        ProofChildrenContainerId::ReferencedLineChildren,
        {
            RuleId::InitOrAxiom,
            RuleId::Apply,
            RuleId::Translate,
        },
    },
    {
        LogicId::ClassicalPropositionalLogic,
        CalculusId::NaturalDeduction,
        "CPC/ND",
        ProofChildrenContainerId::SubproofChildren,
        {
            RuleId::InitOrAxiom,
            RuleId::With,
            RuleId::LeftOrInl,
            RuleId::RightOrInr,
            RuleId::Trivial,
            RuleId::DestructOrCases,
            RuleId::Assume,
            RuleId::Intro,
            RuleId::Apply,
            RuleId::Translate,
        },
    },
    {
        LogicId::ClassicalPropositionalLogic,
        CalculusId::GentzenSequent,
        "CPC/GENTZEN",
        ProofChildrenContainerId::SubproofChildren,
        {
            RuleId::InitOrAxiom,
            RuleId::With,
            RuleId::LeftOrInl,
            RuleId::RightOrInr,
            RuleId::Trivial,
            RuleId::DestructOrCases,
            RuleId::Assume,
            RuleId::Intro,
            RuleId::Apply,
            RuleId::Translate,
        },
    },
    {
        LogicId::ClassicalPropositionalLogic,
        CalculusId::Hilbert,
        "CPC/HILBERT",
        ProofChildrenContainerId::ReferencedLineChildren,
        {
            RuleId::InitOrAxiom,
            RuleId::Apply,
            RuleId::Translate,
        },
    },
    {
        LogicId::ClassicalPropositionalLogic,
        CalculusId::Frege,
        "CPC/FREGE",
        ProofChildrenContainerId::ReferencedLineChildren,
        {
            RuleId::InitOrAxiom,
            RuleId::Apply,
            RuleId::Translate,
        },
    },
    {
        LogicId::SimplyTypedLambdaCalculus,
        CalculusId::NaturalDeduction,
        "STLC/ND",
        ProofChildrenContainerId::SubproofChildren,
        {
            RuleId::InitOrAxiom,
            RuleId::Assume,
            RuleId::Intro,
            RuleId::Apply,
            RuleId::Translate,
        },
    },
};

std::shared_ptr<Formula> cloneFormula(const std::shared_ptr<Formula>& src) {
  if (!src) return nullptr;

  std::shared_ptr<Formula> out = std::make_shared<Formula>();
  out->kind = src->kind;
  out->name = src->name;
  out->negated = src->negated;
  out->left = cloneFormula(src->left);
  out->right = cloneFormula(src->right);
  out->of = cloneFormula(src->of);
  return out;
}

std::shared_ptr<Formula> makeBottom() {
  std::shared_ptr<Formula> out = std::make_shared<Formula>();
  out->kind = FormulaKind::Bot;
  return out;
}

std::shared_ptr<Formula> makeNot(const std::shared_ptr<Formula>& f) {
  std::shared_ptr<Formula> out = std::make_shared<Formula>();
  out->kind = FormulaKind::Lolli;
  out->left = cloneFormula(f);
  out->right = makeBottom();
  return out;
}

std::shared_ptr<Formula> makeDoubleNegation(const std::shared_ptr<Formula>& f) {
  return makeNot(makeNot(f));
}

std::string toUpperAscii(std::string s) {
  for (size_t i = 0; i < s.size(); i++) {
    s[i] = static_cast<char>(std::toupper(static_cast<unsigned char>(s[i])));
  }
  return s;
}

}  // namespace

LogicId parseLogicId(const std::string& text) {
  const std::string normalized = toUpperAscii(text);
  for (const LogicSpec& spec : kLogics) {
    if (spec.canonicalName == normalized) return spec.id;
  }
  throw std::invalid_argument("Unknown logic \"" + text + "\".");
}

CalculusId parseCalculusId(const std::string& text) {
  const std::string normalized = toUpperAscii(text);
  for (const CalculusSpec& spec : kCalculi) {
    if (spec.canonicalName == normalized) return spec.id;
  }
  throw std::invalid_argument("Unknown calculus \"" + text + "\".");
}

const LogicSpec& lookupLogic(LogicId id) {
  for (const LogicSpec& spec : kLogics) {
    if (spec.id == id) return spec;
  }
  throw std::invalid_argument("Logic id not registered.");
}

const CalculusSpec& lookupCalculus(CalculusId id) {
  for (const CalculusSpec& spec : kCalculi) {
    if (spec.id == id) return spec;
  }
  throw std::invalid_argument("Calculus id not registered.");
}

const std::string& logicDisplayName(LogicId id) {
  return lookupLogic(id).canonicalName;
}

const std::string& calculusDisplayName(CalculusId id) {
  return lookupCalculus(id).canonicalName;
}

const std::string& proofChildrenContainerDisplayName(ProofChildrenContainerId id) {
  static const std::string kSubproofChildren = "subproof-children";
  static const std::string kReferencedLineChildren = "referenced-line-children";
  switch (id) {
    case ProofChildrenContainerId::SubproofChildren:
      return kSubproofChildren;
    case ProofChildrenContainerId::ReferencedLineChildren:
      return kReferencedLineChildren;
  }
  throw std::invalid_argument("Unknown proof children container id.");
}

std::string proofProfileDisplayName(LogicId logic, CalculusId calculus) {
  return logicDisplayName(logic) + "/" + calculusDisplayName(calculus);
}

const ProofValidatorSpec& lookupProofProfile(LogicId logic, CalculusId calculus) {
  for (const ProofValidatorSpec& spec : kProfiles) {
    if (spec.logic == logic && spec.calculus == calculus) return spec;
  }

  throw std::invalid_argument("Unsupported proof profile: " + proofProfileDisplayName(logic, calculus) + ".");
}

CalculusId defaultCalculusForLogic(LogicId logic) {
  switch (logic) {
    case LogicId::LinearLogic:
      return CalculusId::GentzenSequent;
    case LogicId::IntuitionisticPropositionalLogic:
    case LogicId::ClassicalPropositionalLogic:
    case LogicId::SimplyTypedLambdaCalculus:
      return CalculusId::NaturalDeduction;
  }
  throw std::invalid_argument("No default calculus for unknown logic.");
}

LogicId defaultLogicForCalculus(CalculusId calculus) {
  switch (calculus) {
    case CalculusId::NaturalDeduction:
      return LogicId::IntuitionisticPropositionalLogic;
    case CalculusId::GentzenSequent:
      return LogicId::LinearLogic;
    case CalculusId::Hilbert:
    case CalculusId::Frege:
      return LogicId::ClassicalPropositionalLogic;
  }
  throw std::invalid_argument("No default logic for unknown calculus.");
}

bool isRuleAllowed(LogicId logicId, CalculusId calculusId, RuleId ruleId) {
  const ProofValidatorSpec& spec = lookupProofProfile(logicId, calculusId);
  return spec.rules.find(ruleId) != spec.rules.end();
}

bool canTranslateProof(LogicId fromLogic,
                       CalculusId fromCalculus,
                       LogicId toLogic,
                       CalculusId toCalculus) {
  try {
    lookupProofProfile(fromLogic, fromCalculus);
    lookupProofProfile(toLogic, toCalculus);
  } catch (...) {
    return false;
  }

  if (fromLogic == toLogic && fromCalculus == toCalculus) {
    return true;
  }

  if (fromLogic == toLogic) {
    return true;
  }

  if (fromLogic == LogicId::IntuitionisticPropositionalLogic &&
      toLogic == LogicId::ClassicalPropositionalLogic) {
    return true;
  }

  if (fromLogic == LogicId::ClassicalPropositionalLogic &&
      toLogic == LogicId::IntuitionisticPropositionalLogic) {
    return true;
  }

  return false;
}

std::shared_ptr<Formula> translateFormula(const std::shared_ptr<Formula>& formula,
                                          LogicId fromLogic,
                                          CalculusId fromCalculus,
                                          LogicId toLogic,
                                          CalculusId toCalculus) {
  if (!formula) {
    throw std::invalid_argument("Cannot translate null formula.");
  }

  lookupProofProfile(fromLogic, fromCalculus);
  lookupProofProfile(toLogic, toCalculus);

  if (!canTranslateProof(fromLogic, fromCalculus, toLogic, toCalculus)) {
    throw std::invalid_argument("No registered translation from " +
                                proofProfileDisplayName(fromLogic, fromCalculus) + " to " +
                                proofProfileDisplayName(toLogic, toCalculus) + ".");
  }

  if (fromLogic == toLogic) {
    return cloneFormula(formula);
  }

  if (fromLogic == LogicId::IntuitionisticPropositionalLogic &&
      toLogic == LogicId::ClassicalPropositionalLogic) {
    return cloneFormula(formula);
  }

  if (fromLogic == LogicId::ClassicalPropositionalLogic &&
      toLogic == LogicId::IntuitionisticPropositionalLogic) {
    return makeDoubleNegation(formula);
  }

  throw std::logic_error("Unsupported translation path.");
}
