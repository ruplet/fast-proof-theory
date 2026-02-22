#pragma once

#include <memory>
#include <string>
#include <unordered_set>
#include <vector>

#include "proof_types.hpp"

enum class RuleId {
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
};

enum class ProofSystemId {
  LinearLogic,
  IntuitionisticPropositionalLogic,
  ClassicalPropositionalLogic,
  SimplyTypedLambdaCalculus,
};

struct ProofSystemSpec {
  ProofSystemId id;
  std::string canonicalName;
  std::unordered_set<RuleId> rules;
};

ProofSystemId parseProofSystemId(const std::string& text);
const std::string& proofSystemDisplayName(ProofSystemId id);
const ProofSystemSpec& lookupProofSystem(ProofSystemId id);
bool isRuleAllowed(ProofSystemId systemId, RuleId ruleId);

bool canTranslateProof(ProofSystemId from, ProofSystemId to);
std::shared_ptr<Formula> translateFormula(const std::shared_ptr<Formula>& formula,
                                          ProofSystemId from,
                                          ProofSystemId to);
