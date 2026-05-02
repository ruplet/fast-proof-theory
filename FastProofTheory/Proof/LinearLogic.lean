namespace FastProofTheory.Proof

inductive LinearFormula where
  | atom : String → LinearFormula
  | tensor : LinearFormula → LinearFormula → LinearFormula
  | par : LinearFormula → LinearFormula → LinearFormula
  | with : LinearFormula → LinearFormula → LinearFormula
  | plus : LinearFormula → LinearFormula → LinearFormula
  | lolli : LinearFormula → LinearFormula → LinearFormula
  | bang : LinearFormula → LinearFormula
  | whyNot : LinearFormula → LinearFormula
  | one : LinearFormula
  | zero : LinearFormula
  | top : LinearFormula
  | bottom : LinearFormula
deriving Inhabited, Repr, DecidableEq

namespace LinearFormula

scoped infixr:70 " ⊗ " => LinearFormula.tensor
scoped infixr:65 " ⅋ " => LinearFormula.par
scoped infixr:60 " & " => LinearFormula.with
scoped infixr:55 " ⊕ " => LinearFormula.plus
scoped infixr:50 " ⊸ " => LinearFormula.lolli
scoped notation "⊤ₗ" => LinearFormula.top
scoped notation "⊥ₗ" => LinearFormula.bottom

def neg (formula : LinearFormula) : LinearFormula :=
  formula ⊸ ⊥ₗ

scoped prefix:max "~" => neg

end LinearFormula

open LinearFormula

abbrev LinearContext := List LinearFormula

private def allBang : LinearContext → Prop
  | [] => True
  | .bang _ :: rest => allBang rest
  | _ => False

private def allWhyNot : LinearContext → Prop
  | [] => True
  | .whyNot _ :: rest => allWhyNot rest
  | _ => False

inductive LinearLogic : LinearContext → LinearContext → Prop where
  | assumption {formula} :
      LinearLogic [formula] [formula]

  | exchangeLeft {leftContext rightContext succedent firstFormula secondFormula} :
      LinearLogic (leftContext ++ firstFormula :: secondFormula :: rightContext) succedent →
      LinearLogic (leftContext ++ secondFormula :: firstFormula :: rightContext) succedent

  | exchangeRight {antecedent leftContext rightContext firstFormula secondFormula} :
      LinearLogic antecedent (leftContext ++ firstFormula :: secondFormula :: rightContext) →
      LinearLogic antecedent (leftContext ++ secondFormula :: firstFormula :: rightContext)

  | cut {leftAntecedent leftSuccedent rightAntecedent rightSuccedent cutFormula} :
      LinearLogic leftAntecedent (cutFormula :: leftSuccedent) →
      LinearLogic (cutFormula :: rightAntecedent) rightSuccedent →
      LinearLogic (leftAntecedent ++ rightAntecedent) (leftSuccedent ++ rightSuccedent)

  | withLeftLeft {antecedent succedent leftFormula rightFormula} :
      LinearLogic (leftFormula :: antecedent) succedent →
      LinearLogic ((leftFormula & rightFormula) :: antecedent) succedent

  | withLeftRight {antecedent succedent leftFormula rightFormula} :
      LinearLogic (rightFormula :: antecedent) succedent →
      LinearLogic ((leftFormula & rightFormula) :: antecedent) succedent

  | withRight {antecedent succedent leftFormula rightFormula} :
      LinearLogic antecedent (leftFormula :: succedent) →
      LinearLogic antecedent (rightFormula :: succedent) →
      LinearLogic antecedent ((leftFormula & rightFormula) :: succedent)

  | tensorLeft {antecedent succedent leftFormula rightFormula} :
      LinearLogic (leftFormula :: rightFormula :: antecedent) succedent →
      LinearLogic ((leftFormula ⊗ rightFormula) :: antecedent) succedent

  | tensorRight {leftAntecedent leftSuccedent rightAntecedent rightSuccedent leftFormula rightFormula} :
      LinearLogic leftAntecedent (leftFormula :: leftSuccedent) →
      LinearLogic rightAntecedent (rightFormula :: rightSuccedent) →
      LinearLogic (leftAntecedent ++ rightAntecedent) ((leftFormula ⊗ rightFormula) :: (leftSuccedent ++ rightSuccedent))

  | plusLeft {antecedent succedent leftFormula rightFormula} :
      LinearLogic (leftFormula :: antecedent) succedent →
      LinearLogic (rightFormula :: antecedent) succedent →
      LinearLogic ((leftFormula ⊕ rightFormula) :: antecedent) succedent

  | plusRightLeft {antecedent succedent leftFormula rightFormula} :
      LinearLogic antecedent (leftFormula :: succedent) →
      LinearLogic antecedent ((leftFormula ⊕ rightFormula) :: succedent)

  | plusRightRight {antecedent succedent leftFormula rightFormula} :
      LinearLogic antecedent (rightFormula :: succedent) →
      LinearLogic antecedent ((leftFormula ⊕ rightFormula) :: succedent)

  | parLeft {leftAntecedent leftSuccedent rightAntecedent rightSuccedent leftFormula rightFormula} :
      LinearLogic leftAntecedent (leftFormula :: leftSuccedent) →
      LinearLogic (rightFormula :: rightAntecedent) rightSuccedent →
      LinearLogic ((leftFormula ⅋ rightFormula) :: (leftAntecedent ++ rightAntecedent)) (leftSuccedent ++ rightSuccedent)

  | parRight {antecedent succedent leftFormula rightFormula} :
      LinearLogic antecedent (leftFormula :: rightFormula :: succedent) →
      LinearLogic antecedent ((leftFormula ⅋ rightFormula) :: succedent)

  | lolliLeft {leftAntecedent leftSuccedent rightAntecedent rightSuccedent antecedentFormula consequentFormula} :
      LinearLogic leftAntecedent (antecedentFormula :: leftSuccedent) →
      LinearLogic (consequentFormula :: rightAntecedent) rightSuccedent →
      LinearLogic ((antecedentFormula ⊸ consequentFormula) :: (leftAntecedent ++ rightAntecedent))
        (leftSuccedent ++ rightSuccedent)

  | lolliRight {antecedent succedent antecedentFormula consequentFormula} :
      LinearLogic (antecedentFormula :: antecedent) (consequentFormula :: succedent) →
      LinearLogic antecedent ((antecedentFormula ⊸ consequentFormula) :: succedent)

  | oneLeft {antecedent succedent} :
      LinearLogic antecedent succedent →
      LinearLogic (.one :: antecedent) succedent

  | oneRight :
      LinearLogic [] [.one]

  | zeroLeft {antecedent succedent} :
      LinearLogic (.zero :: antecedent) succedent

  | topRight {antecedent succedent} :
      LinearLogic antecedent (⊤ₗ :: succedent)

  | bottomLeft {antecedent succedent} :
      LinearLogic (⊥ₗ :: antecedent) succedent

  | bottomRight {antecedent succedent} :
      LinearLogic antecedent succedent →
      LinearLogic antecedent (⊥ₗ :: succedent)

  | bangLeft {antecedent succedent formula} :
      LinearLogic (formula :: antecedent) succedent →
      LinearLogic ((.bang formula) :: antecedent) succedent

  | bangRight {antecedent succedent formula} :
      allBang antecedent →
      allWhyNot succedent →
      LinearLogic antecedent (formula :: succedent) →
      LinearLogic antecedent ((.bang formula) :: succedent)

  | whyNotLeft {antecedent succedent formula} :
      allBang antecedent →
      allWhyNot succedent →
      LinearLogic (formula :: antecedent) succedent →
      LinearLogic ((.whyNot formula) :: antecedent) succedent

  | whyNotRight {antecedent succedent formula} :
      LinearLogic antecedent (formula :: succedent) →
      LinearLogic antecedent ((.whyNot formula) :: succedent)

end FastProofTheory.Proof
