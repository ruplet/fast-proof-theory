#include "proof_system.hpp"

#include <stdexcept>
#include <utility>

namespace {

const std::vector<ProofSystemSpec> kSystems = {
    {
        ProofSystemId::LinearLogic,
        "LL",
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
        ProofSystemId::IntuitionisticPropositionalLogic,
        "IPC",
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
        ProofSystemId::ClassicalPropositionalLogic,
        "CPC",
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
        ProofSystemId::SimplyTypedLambdaCalculus,
        "STLC",
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

}  // namespace

ProofSystemId parseProofSystemId(const std::string& text) {
  for (const ProofSystemSpec& spec : kSystems) {
    if (spec.canonicalName == text) return spec.id;
  }
  throw std::invalid_argument("Unknown proof system \"" + text + "\".");
}

const std::string& proofSystemDisplayName(ProofSystemId id) {
  return lookupProofSystem(id).canonicalName;
}

const ProofSystemSpec& lookupProofSystem(ProofSystemId id) {
  for (const ProofSystemSpec& spec : kSystems) {
    if (spec.id == id) return spec;
  }
  throw std::invalid_argument("Proof system id not registered.");
}

bool isRuleAllowed(ProofSystemId systemId, RuleId ruleId) {
  const ProofSystemSpec& spec = lookupProofSystem(systemId);
  return spec.rules.find(ruleId) != spec.rules.end();
}

bool canTranslateProof(ProofSystemId from, ProofSystemId to) {
  if (from == to) return true;
  if (from == ProofSystemId::IntuitionisticPropositionalLogic &&
      to == ProofSystemId::ClassicalPropositionalLogic) {
    return true;
  }
  if (from == ProofSystemId::ClassicalPropositionalLogic &&
      to == ProofSystemId::IntuitionisticPropositionalLogic) {
    return true;
  }
  return false;
}

std::shared_ptr<Formula> translateFormula(const std::shared_ptr<Formula>& formula,
                                          ProofSystemId from,
                                          ProofSystemId to) {
  if (!formula) {
    throw std::invalid_argument("Cannot translate null formula.");
  }

  if (!canTranslateProof(from, to)) {
    throw std::invalid_argument("No registered translation from " + proofSystemDisplayName(from) +
                                " to " + proofSystemDisplayName(to) + ".");
  }

  if (from == to) return cloneFormula(formula);

  if (from == ProofSystemId::IntuitionisticPropositionalLogic &&
      to == ProofSystemId::ClassicalPropositionalLogic) {
    return cloneFormula(formula);
  }

  if (from == ProofSystemId::ClassicalPropositionalLogic &&
      to == ProofSystemId::IntuitionisticPropositionalLogic) {
    return makeDoubleNegation(formula);
  }

  throw std::logic_error("Unsupported translation path.");
}
