#pragma once

#include <memory>
#include <string>
#include <vector>

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

inline bool operator==(const Formula& lhs, const Formula& rhs);

inline bool formulaPtrEqual(const std::shared_ptr<Formula>& lhs, const std::shared_ptr<Formula>& rhs) {
  if (!lhs || !rhs) return lhs == rhs;
  return *lhs == *rhs;
}

inline bool operator==(const Formula& lhs, const Formula& rhs) {
  if (lhs.kind != rhs.kind) return false;

  switch (lhs.kind) {
    case FormulaKind::Atom:
      return lhs.name == rhs.name && lhs.negated == rhs.negated;
    case FormulaKind::Bang:
      return formulaPtrEqual(lhs.of, rhs.of);
    case FormulaKind::Tensor:
    case FormulaKind::With:
    case FormulaKind::Plus:
    case FormulaKind::Lolli:
      return formulaPtrEqual(lhs.left, rhs.left) && formulaPtrEqual(lhs.right, rhs.right);
    default:
      return true;
  }
}

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
  std::string proofSystem;
  std::vector<InputHypDecl> hypotheses;
  std::vector<InputGoalDecl> goals;
  std::vector<InputTactic> tactics;
};

struct InputDocument {
  std::string uri;
  int version = 0;
  std::vector<InputTheorem> theorems;
};
