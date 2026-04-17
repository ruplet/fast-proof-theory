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

enum class LogicId {
  LinearLogic,
  IntuitionisticPropositionalLogic,
  ClassicalPropositionalLogic,
  SimplyTypedLambdaCalculus,
};

enum class CalculusId {
  NaturalDeduction,
  GentzenSequent,
  Hilbert,
  Frege,
};

enum class ProofChildrenContainerId {
  SubproofChildren,
  ReferencedLineChildren,
};

struct LogicSpec {
  LogicId id;
  std::string canonicalName;
};

struct CalculusSpec {
  CalculusId id;
  std::string canonicalName;
};

struct ProofValidatorSpec {
  LogicId logic;
  CalculusId calculus;
  std::string canonicalName;
  ProofChildrenContainerId childrenContainer;
  std::unordered_set<RuleId> rules;
};

LogicId parseLogicId(const std::string& text);
CalculusId parseCalculusId(const std::string& text);

const std::string& logicDisplayName(LogicId id);
const std::string& calculusDisplayName(CalculusId id);
const std::string& proofChildrenContainerDisplayName(ProofChildrenContainerId id);
std::string proofProfileDisplayName(LogicId logic, CalculusId calculus);

const LogicSpec& lookupLogic(LogicId id);
const CalculusSpec& lookupCalculus(CalculusId id);
const ProofValidatorSpec& lookupProofProfile(LogicId logic, CalculusId calculus);
CalculusId defaultCalculusForLogic(LogicId logic);
LogicId defaultLogicForCalculus(CalculusId calculus);
bool isRuleAllowed(LogicId logicId, CalculusId calculusId, RuleId ruleId);

bool canTranslateProof(LogicId fromLogic, CalculusId fromCalculus, LogicId toLogic, CalculusId toCalculus);
std::shared_ptr<Formula> translateFormula(const std::shared_ptr<Formula>& formula,
                                          LogicId fromLogic,
                                          CalculusId fromCalculus,
                                          LogicId toLogic,
                                          CalculusId toCalculus);
