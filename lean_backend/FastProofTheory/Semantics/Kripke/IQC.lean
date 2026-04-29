import Logic.Rules

namespace FastProofTheory.Semantics.Kripke.IQC

/-
First-order intuitionistic Kripke semantics is not implemented yet in this
codebase. This module provides a stable namespace entry point for that future
work while exposing the existing first-order formula language.
-/
abbrev Formula := Rules.Formula
abbrev Term := Rules.Term

end FastProofTheory.Semantics.Kripke.IQC
