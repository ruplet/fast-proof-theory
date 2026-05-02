import FastProofTheory.Proof.LJ

open FirstOrder

namespace FastProofTheory.Proof

universe u v w

variable {L : FirstOrder.Language.{u, v}}
variable {α : Type w}
variable [DecidableEq α]

inductive LKp : List (L.Formula α) → List (L.Formula α) → Prop where
  | fromLJp {antecedent formula} :
      LJp antecedent formula →
      LKp antecedent [formula]

  | weakeningLeft {antecedent succedent formula} :
      LKp antecedent succedent →
      LKp (formula :: antecedent) succedent

  | weakeningRight {antecedent succedent formula} :
      LKp antecedent succedent →
      LKp antecedent (formula :: succedent)

  | contractionLeft {antecedent succedent formula} :
      LKp (formula :: formula :: antecedent) succedent →
      LKp (formula :: antecedent) succedent

  | contractionRight {antecedent succedent formula} :
      LKp antecedent (formula :: formula :: succedent) →
      LKp antecedent (formula :: succedent)

  | exchangeLeft {antecedent succedent firstFormula secondFormula} :
      LKp (firstFormula :: secondFormula :: antecedent) succedent →
      LKp (secondFormula :: firstFormula :: antecedent) succedent

  | exchangeRight {antecedent succedent firstFormula secondFormula} :
      LKp antecedent (firstFormula :: secondFormula :: succedent) →
      LKp antecedent (secondFormula :: firstFormula :: succedent)

  | cut {leftAntecedent leftSuccedent rightAntecedent rightSuccedent cutFormula} :
      LKp leftAntecedent (cutFormula :: leftSuccedent) →
      LKp (cutFormula :: rightAntecedent) rightSuccedent →
      LKp (leftAntecedent ++ rightAntecedent) (leftSuccedent ++ rightSuccedent)

  | andRight {antecedent succedent leftFormula rightFormula} :
      LKp antecedent (leftFormula :: succedent) →
      LKp antecedent (rightFormula :: succedent) →
      LKp antecedent ((leftFormula ⊓ rightFormula) :: succedent)

  | andLeftLeft {antecedent succedent leftFormula rightFormula} :
      LKp (leftFormula :: antecedent) succedent →
      LKp ((leftFormula ⊓ rightFormula) :: antecedent) succedent

  | andLeftRight {antecedent succedent leftFormula rightFormula} :
      LKp (rightFormula :: antecedent) succedent →
      LKp ((leftFormula ⊓ rightFormula) :: antecedent) succedent

  | orRightLeft {antecedent succedent leftFormula rightFormula} :
      LKp antecedent (leftFormula :: succedent) →
      LKp antecedent ((leftFormula ⊔ rightFormula) :: succedent)

  | orRightRight {antecedent succedent leftFormula rightFormula} :
      LKp antecedent (rightFormula :: succedent) →
      LKp antecedent ((leftFormula ⊔ rightFormula) :: succedent)

  | orLeft {antecedent succedent leftFormula rightFormula} :
      LKp (leftFormula :: antecedent) succedent →
      LKp (rightFormula :: antecedent) succedent →
      LKp ((leftFormula ⊔ rightFormula) :: antecedent) succedent

  | implicationRight {antecedent succedent antecedentFormula consequentFormula} :
      LKp (antecedentFormula :: antecedent) (consequentFormula :: succedent) →
      LKp antecedent ((antecedentFormula.imp consequentFormula) :: succedent)

  | implicationLeft {leftAntecedent leftSuccedent rightAntecedent rightSuccedent antecedentFormula consequentFormula} :
      LKp leftAntecedent (antecedentFormula :: leftSuccedent) →
      LKp (consequentFormula :: rightAntecedent) rightSuccedent →
      LKp ((antecedentFormula.imp consequentFormula) :: (leftAntecedent ++ rightAntecedent))
        (leftSuccedent ++ rightSuccedent)

inductive LK : List (L.Formula α) → List (L.Formula α) → Prop where
  | fromLKp {antecedent succedent} :
      LKp antecedent succedent →
      LK antecedent succedent

  | fromLJ {antecedent formula} :
      LJ antecedent formula →
      LK antecedent [formula]

  | weakeningLeft {antecedent succedent formula} :
      LK antecedent succedent →
      LK (formula :: antecedent) succedent

  | weakeningRight {antecedent succedent formula} :
      LK antecedent succedent →
      LK antecedent (formula :: succedent)

  | contractionLeft {antecedent succedent formula} :
      LK (formula :: formula :: antecedent) succedent →
      LK (formula :: antecedent) succedent

  | contractionRight {antecedent succedent formula} :
      LK antecedent (formula :: formula :: succedent) →
      LK antecedent (formula :: succedent)

  | exchangeLeft {antecedent succedent firstFormula secondFormula} :
      LK (firstFormula :: secondFormula :: antecedent) succedent →
      LK (secondFormula :: firstFormula :: antecedent) succedent

  | exchangeRight {antecedent succedent firstFormula secondFormula} :
      LK antecedent (firstFormula :: secondFormula :: succedent) →
      LK antecedent (secondFormula :: firstFormula :: succedent)

  | cut {leftAntecedent leftSuccedent rightAntecedent rightSuccedent cutFormula} :
      LK leftAntecedent (cutFormula :: leftSuccedent) →
      LK (cutFormula :: rightAntecedent) rightSuccedent →
      LK (leftAntecedent ++ rightAntecedent) (leftSuccedent ++ rightSuccedent)

  | andRight {antecedent succedent leftFormula rightFormula} :
      LK antecedent (leftFormula :: succedent) →
      LK antecedent (rightFormula :: succedent) →
      LK antecedent ((leftFormula ⊓ rightFormula) :: succedent)

  | andLeftLeft {antecedent succedent leftFormula rightFormula} :
      LK (leftFormula :: antecedent) succedent →
      LK ((leftFormula ⊓ rightFormula) :: antecedent) succedent

  | andLeftRight {antecedent succedent leftFormula rightFormula} :
      LK (rightFormula :: antecedent) succedent →
      LK ((leftFormula ⊓ rightFormula) :: antecedent) succedent

  | orRightLeft {antecedent succedent leftFormula rightFormula} :
      LK antecedent (leftFormula :: succedent) →
      LK antecedent ((leftFormula ⊔ rightFormula) :: succedent)

  | orRightRight {antecedent succedent leftFormula rightFormula} :
      LK antecedent (rightFormula :: succedent) →
      LK antecedent ((leftFormula ⊔ rightFormula) :: succedent)

  | orLeft {antecedent succedent leftFormula rightFormula} :
      LK (leftFormula :: antecedent) succedent →
      LK (rightFormula :: antecedent) succedent →
      LK ((leftFormula ⊔ rightFormula) :: antecedent) succedent

  | implicationRight {antecedent succedent antecedentFormula consequentFormula} :
      LK (antecedentFormula :: antecedent) (consequentFormula :: succedent) →
      LK antecedent ((antecedentFormula.imp consequentFormula) :: succedent)

  | implicationLeft {leftAntecedent leftSuccedent rightAntecedent rightSuccedent antecedentFormula consequentFormula} :
      LK leftAntecedent (antecedentFormula :: leftSuccedent) →
      LK (consequentFormula :: rightAntecedent) rightSuccedent →
      LK ((antecedentFormula.imp consequentFormula) :: (leftAntecedent ++ rightAntecedent))
        (leftSuccedent ++ rightSuccedent)

  | universalRight {antecedent succedent formulaBody eigenvariable} :
      variableDoesNotOccurFreeInEveryFormula eigenvariable antecedent →
      variableDoesNotOccurFreeInEveryFormula eigenvariable succedent →
      LK antecedent ((instantiateQuantifierBody formulaBody (FirstOrder.Language.Term.var eigenvariable)) :: succedent) →
      LK antecedent (formulaBody.all :: succedent)

  | universalLeft {antecedent succedent formulaBody term} :
      LK ((instantiateQuantifierBody formulaBody term) :: antecedent) succedent →
      LK (formulaBody.all :: antecedent) succedent

  | existentialRight {antecedent succedent formulaBody term} :
      LK antecedent ((instantiateQuantifierBody formulaBody term) :: succedent) →
      LK antecedent (formulaBody.ex :: succedent)

  | existentialLeft {antecedent succedent formulaBody eigenvariable} :
      variableDoesNotOccurFreeInEveryFormula eigenvariable antecedent →
      variableDoesNotOccurFreeInEveryFormula eigenvariable succedent →
      LK ((instantiateQuantifierBody formulaBody (FirstOrder.Language.Term.var eigenvariable)) :: antecedent) succedent →
      LK (formulaBody.ex :: antecedent) succedent

end FastProofTheory.Proof
