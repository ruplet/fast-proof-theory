import Mathlib.ModelTheory.Syntax

open FirstOrder

namespace FastProofTheory.Proof

universe u v w

variable {L : FirstOrder.Language.{u, v}}
variable {α : Type w}

def neg (formula : L.Formula α) : L.Formula α :=
  formula.imp (⊥ : L.Formula α)

scoped prefix:max "¬' " => neg

def instantiateQuantifierBody
    (formulaWithOneBoundVariable : L.BoundedFormula α 1)
    (term : L.Term α) :
    L.Formula α :=
  formulaWithOneBoundVariable.toFormula.subst
    (fun variableFromFormulaOrBoundVariable =>
      match variableFromFormulaOrBoundVariable with
      | Sum.inl freeVariable =>
          (FirstOrder.Language.Term.var freeVariable : L.Term α)
      | Sum.inr _ =>
          term)

def variableDoesNotOccurFreeInFormula [DecidableEq α]
    (eigenvariable : α)
    (formula : L.Formula α) :
    Prop :=
  eigenvariable ∉ formula.freeVarFinset

def variableDoesNotOccurFreeInEveryFormula [DecidableEq α]
    (eigenvariable : α)
    (formulas : List (L.Formula α)) :
    Prop :=
  ∀ formula ∈ formulas, variableDoesNotOccurFreeInFormula eigenvariable formula

end FastProofTheory.Proof
