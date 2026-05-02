import FastProofTheory.Proof.Common

open FirstOrder

namespace FastProofTheory.Proof

universe u v w

variable {L : FirstOrder.Language.{u, v}}
variable {α : Type w}
variable [DecidableEq α]

inductive LJ : List (L.Formula α) → L.Formula α → Prop where
  | assumption {formula} :
      LJ [formula] formula

  | weakeningLeft {antecedent succedent formula} :
      LJ antecedent succedent →
      LJ (formula :: antecedent) succedent

  | contractionLeft {antecedent succedent formula} :
      LJ (formula :: formula :: antecedent) succedent →
      LJ (formula :: antecedent) succedent

  | exchangeLeft {antecedent succedent firstFormula secondFormula} :
      LJ (firstFormula :: secondFormula :: antecedent) succedent →
      LJ (secondFormula :: firstFormula :: antecedent) succedent

  | cut {leftAntecedent rightAntecedent succedent cutFormula} :
      LJ leftAntecedent cutFormula →
      LJ (cutFormula :: rightAntecedent) succedent →
      LJ (leftAntecedent ++ rightAntecedent) succedent

  | andRight {antecedent leftFormula rightFormula} :
      LJ antecedent leftFormula →
      LJ antecedent rightFormula →
      LJ antecedent (leftFormula ⊓ rightFormula)

  | andLeftLeft {antecedent succedent leftFormula rightFormula} :
      LJ (leftFormula :: antecedent) succedent →
      LJ ((leftFormula ⊓ rightFormula) :: antecedent) succedent

  | andLeftRight {antecedent succedent leftFormula rightFormula} :
      LJ (rightFormula :: antecedent) succedent →
      LJ ((leftFormula ⊓ rightFormula) :: antecedent) succedent

  | orRightLeft {antecedent leftFormula rightFormula} :
      LJ antecedent leftFormula →
      LJ antecedent (leftFormula ⊔ rightFormula)

  | orRightRight {antecedent leftFormula rightFormula} :
      LJ antecedent rightFormula →
      LJ antecedent (leftFormula ⊔ rightFormula)

  | orLeft {antecedent succedent leftFormula rightFormula} :
      LJ (leftFormula :: antecedent) succedent →
      LJ (rightFormula :: antecedent) succedent →
      LJ ((leftFormula ⊔ rightFormula) :: antecedent) succedent

  | implicationRight {antecedent antecedentFormula consequentFormula} :
      LJ (antecedentFormula :: antecedent) consequentFormula →
      LJ antecedent (antecedentFormula.imp consequentFormula)

  | implicationLeft {leftAntecedent rightAntecedent succedent antecedentFormula consequentFormula} :
      LJ leftAntecedent antecedentFormula →
      LJ (consequentFormula :: rightAntecedent) succedent →
      LJ ((antecedentFormula.imp consequentFormula) :: (leftAntecedent ++ rightAntecedent)) succedent

  | falseLeft {antecedent formula} :
      LJ ((⊥ : L.Formula α) :: antecedent) formula

  | universalRight {antecedent formulaBody eigenvariable} :
      variableDoesNotOccurFreeInEveryFormula eigenvariable antecedent →
      LJ antecedent (instantiateQuantifierBody formulaBody (FirstOrder.Language.Term.var eigenvariable)) →
      LJ antecedent formulaBody.all

  | universalLeft {antecedent succedent formulaBody term} :
      LJ ((instantiateQuantifierBody formulaBody term) :: antecedent) succedent →
      LJ (formulaBody.all :: antecedent) succedent

  | existentialRight {antecedent formulaBody term} :
      LJ antecedent (instantiateQuantifierBody formulaBody term) →
      LJ antecedent formulaBody.ex

  | existentialLeft {antecedent succedent formulaBody eigenvariable} :
      variableDoesNotOccurFreeInEveryFormula eigenvariable antecedent →
      variableDoesNotOccurFreeInFormula eigenvariable succedent →
      LJ ((instantiateQuantifierBody formulaBody (FirstOrder.Language.Term.var eigenvariable)) :: antecedent) succedent →
      LJ (formulaBody.ex :: antecedent) succedent

end FastProofTheory.Proof
