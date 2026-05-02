import FastProofTheory.Proof.Common

open FirstOrder

namespace FastProofTheory.Proof

universe u v w

variable {L : FirstOrder.Language.{u, v}}
variable {α : Type w}
variable [DecidableEq α]

inductive NJ : List (L.Formula α) → L.Formula α → Prop where
  | hypothesis {assumptions formula} :
      formula ∈ assumptions →
      NJ assumptions formula

  | andIntroduction {assumptions leftFormula rightFormula} :
      NJ assumptions leftFormula →
      NJ assumptions rightFormula →
      NJ assumptions (leftFormula ⊓ rightFormula)

  | andEliminationLeft {assumptions leftFormula rightFormula} :
      NJ assumptions (leftFormula ⊓ rightFormula) →
      NJ assumptions leftFormula

  | andEliminationRight {assumptions leftFormula rightFormula} :
      NJ assumptions (leftFormula ⊓ rightFormula) →
      NJ assumptions rightFormula

  | orIntroductionLeft {assumptions leftFormula rightFormula} :
      NJ assumptions leftFormula →
      NJ assumptions (leftFormula ⊔ rightFormula)

  | orIntroductionRight {assumptions leftFormula rightFormula} :
      NJ assumptions rightFormula →
      NJ assumptions (leftFormula ⊔ rightFormula)

  | orElimination {assumptions leftFormula rightFormula conclusion} :
      NJ assumptions (leftFormula ⊔ rightFormula) →
      NJ (leftFormula :: assumptions) conclusion →
      NJ (rightFormula :: assumptions) conclusion →
      NJ assumptions conclusion

  | implicationIntroduction {assumptions antecedent consequent} :
      NJ (antecedent :: assumptions) consequent →
      NJ assumptions (antecedent.imp consequent)

  | implicationElimination {assumptions antecedent consequent} :
      NJ assumptions (antecedent.imp consequent) →
      NJ assumptions antecedent →
      NJ assumptions consequent

  | falseElimination {assumptions formula} :
      NJ assumptions (⊥ : L.Formula α) →
      NJ assumptions formula

  | universalIntroduction {assumptions formulaBody eigenvariable} :
      variableDoesNotOccurFreeInEveryFormula eigenvariable assumptions →
      NJ assumptions (instantiateQuantifierBody formulaBody (FirstOrder.Language.Term.var eigenvariable)) →
      NJ assumptions formulaBody.all

  | universalElimination {assumptions formulaBody term} :
      NJ assumptions formulaBody.all →
      NJ assumptions (instantiateQuantifierBody formulaBody term)

  | existentialIntroduction {assumptions formulaBody term} :
      NJ assumptions (instantiateQuantifierBody formulaBody term) →
      NJ assumptions formulaBody.ex

  | existentialElimination {assumptions formulaBody conclusion eigenvariable} :
      variableDoesNotOccurFreeInEveryFormula eigenvariable assumptions →
      variableDoesNotOccurFreeInFormula eigenvariable conclusion →
      NJ assumptions formulaBody.ex →
      NJ ((instantiateQuantifierBody formulaBody (FirstOrder.Language.Term.var eigenvariable)) :: assumptions) conclusion →
      NJ assumptions conclusion

end FastProofTheory.Proof
