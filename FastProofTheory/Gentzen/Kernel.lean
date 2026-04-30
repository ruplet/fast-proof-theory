import FastProofTheory.Rules
import FastProofTheory.Core.Kernel

namespace FastProofTheory.Gentzen

open Rules

/--
Trusted generic data model for Gentzen-style sequent certificates.

Certificates are untrusted data. No constructor may contain a function or rule
implementation. All rule semantics live in checker-side code.
-/

abbrev Formula := Rules.Formula
abbrev Context := List Formula

structure Sequent where
  persistent : Context
  assumptions : Context
  conclusion : Formula

structure RuleSystemSpec where
  displayName : String
  allowsFormula : Formula → Bool

structure RuleSystem (RuleId RuleParams : Type) where
  displayName : RuleId → String
  allowsRule : RuleId → Bool
  premises : RuleId → RuleParams → Sequent → Except String (List Sequent)

inductive Certificate (RuleId RuleParams : Type) where
  | byRule (rule : RuleId) (params : RuleParams) (premises : List (Certificate RuleId RuleParams))

inductive KernelError where
  | ruleNotAllowed (system : String) (rule : String)
  | unsupportedFormula (system : String) (formula : Formula)
  | wrongPremiseCount (rule : String) (expected : Nat) (actual : Nat)
  | ruleRejected (rule : String) (detail : String)

def renderKernelError : KernelError → String
  | .ruleNotAllowed system rule => s!"Rule `{rule}` is not allowed in system {system}."
  | .unsupportedFormula system _ => s!"Formula is not supported in system {system}."
  | .wrongPremiseCount rule expected actual =>
      s!"Rule `{rule}` expected {expected} premise certificate(s), but got {actual}."
  | .ruleRejected rule detail => s!"Rule `{rule}` rejected the sequent: {detail}"

end FastProofTheory.Gentzen
