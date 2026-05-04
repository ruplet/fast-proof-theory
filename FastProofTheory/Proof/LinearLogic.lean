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

end LinearFormula

inductive IntuitionisticLinearFormula where
  | atom : String → IntuitionisticLinearFormula
  | tensor : IntuitionisticLinearFormula → IntuitionisticLinearFormula → IntuitionisticLinearFormula
  | with : IntuitionisticLinearFormula → IntuitionisticLinearFormula → IntuitionisticLinearFormula
  | plus : IntuitionisticLinearFormula → IntuitionisticLinearFormula → IntuitionisticLinearFormula
  | lolli : IntuitionisticLinearFormula → IntuitionisticLinearFormula → IntuitionisticLinearFormula
  | bang : IntuitionisticLinearFormula → IntuitionisticLinearFormula
  | one : IntuitionisticLinearFormula
  | zero : IntuitionisticLinearFormula
  | top : IntuitionisticLinearFormula
deriving Inhabited, Repr, DecidableEq

namespace IntuitionisticLinearFormula

scoped infixr:70 " ⊗ᵢ " => IntuitionisticLinearFormula.tensor
scoped infixr:60 " &ᵢ " => IntuitionisticLinearFormula.with
scoped infixr:55 " ⊕ᵢ " => IntuitionisticLinearFormula.plus
scoped infixr:50 " ⊸ᵢ " => IntuitionisticLinearFormula.lolli
scoped notation "⊤ᵢ" => IntuitionisticLinearFormula.top

end IntuitionisticLinearFormula

open LinearFormula

abbrev LinearContext := List LinearFormula
abbrev IntuitionisticLinearContext := List IntuitionisticLinearFormula

private def allBang : LinearContext → Prop
  | [] => True
  | .bang _ :: rest => allBang rest
  | _ => False

private def allWhyNot : LinearContext → Prop
  | [] => True
  | .whyNot _ :: rest => allWhyNot rest
  | _ => False

private def allBangIntuitionistic : IntuitionisticLinearContext → Prop
  | [] => True
  | .bang _ :: rest => allBangIntuitionistic rest
  | _ => False

inductive CLL : LinearContext → LinearContext → Prop where
  | assumption {formula} :
      CLL [formula] [formula]

  | exchangeLeft {leftContext rightContext succedent firstFormula secondFormula} :
      CLL (leftContext ++ firstFormula :: secondFormula :: rightContext) succedent →
      CLL (leftContext ++ secondFormula :: firstFormula :: rightContext) succedent

  | exchangeRight {antecedent leftContext rightContext firstFormula secondFormula} :
      CLL antecedent (leftContext ++ firstFormula :: secondFormula :: rightContext) →
      CLL antecedent (leftContext ++ secondFormula :: firstFormula :: rightContext)

  | cut {leftAntecedent leftSuccedent rightAntecedent rightSuccedent cutFormula} :
      CLL leftAntecedent (cutFormula :: leftSuccedent) →
      CLL (cutFormula :: rightAntecedent) rightSuccedent →
      CLL (leftAntecedent ++ rightAntecedent) (leftSuccedent ++ rightSuccedent)

  | tensorLeft {antecedent succedent leftFormula rightFormula} :
      CLL (leftFormula :: rightFormula :: antecedent) succedent →
      CLL ((leftFormula ⊗ rightFormula) :: antecedent) succedent

  | tensorRight {leftAntecedent leftSuccedent rightAntecedent rightSuccedent leftFormula rightFormula} :
      CLL leftAntecedent (leftFormula :: leftSuccedent) →
      CLL rightAntecedent (rightFormula :: rightSuccedent) →
      CLL (leftAntecedent ++ rightAntecedent) ((leftFormula ⊗ rightFormula) :: (leftSuccedent ++ rightSuccedent))

  | oneLeft {antecedent succedent} :
      CLL antecedent succedent →
      CLL (.one :: antecedent) succedent

  | oneRight :
      CLL [] [.one]

  | parLeft {leftAntecedent leftSuccedent rightAntecedent rightSuccedent leftFormula rightFormula} :
      CLL (leftFormula :: leftAntecedent) leftSuccedent →
      CLL (rightFormula :: rightAntecedent) rightSuccedent →
      CLL ((leftFormula ⅋ rightFormula) :: (leftAntecedent ++ rightAntecedent)) (leftSuccedent ++ rightSuccedent)

  | parRight {antecedent succedent leftFormula rightFormula} :
      CLL antecedent (leftFormula :: rightFormula :: succedent) →
      CLL antecedent ((leftFormula ⅋ rightFormula) :: succedent)

  | bottomLeft :
      CLL [.bottom] []

  | bottomRight {antecedent succedent} :
      CLL antecedent succedent →
      CLL antecedent (.bottom :: succedent)

  | lolliLeft {leftAntecedent leftSuccedent rightAntecedent rightSuccedent antecedentFormula consequentFormula} :
      CLL leftAntecedent (antecedentFormula :: leftSuccedent) →
      CLL (consequentFormula :: rightAntecedent) rightSuccedent →
      CLL ((antecedentFormula ⊸ consequentFormula) :: (leftAntecedent ++ rightAntecedent))
        (leftSuccedent ++ rightSuccedent)

  | lolliRight {antecedent succedent antecedentFormula consequentFormula} :
      CLL (antecedentFormula :: antecedent) (consequentFormula :: succedent) →
      CLL antecedent ((antecedentFormula ⊸ consequentFormula) :: succedent)

  | withLeftLeft {antecedent succedent leftFormula rightFormula} :
      CLL (leftFormula :: antecedent) succedent →
      CLL ((leftFormula & rightFormula) :: antecedent) succedent

  | withLeftRight {antecedent succedent leftFormula rightFormula} :
      CLL (rightFormula :: antecedent) succedent →
      CLL ((leftFormula & rightFormula) :: antecedent) succedent

  | withRight {antecedent succedent leftFormula rightFormula} :
      CLL antecedent (leftFormula :: succedent) →
      CLL antecedent (rightFormula :: succedent) →
      CLL antecedent ((leftFormula & rightFormula) :: succedent)

  | topRight {antecedent succedent} :
      CLL antecedent (.top :: succedent)

  | plusLeft {antecedent succedent leftFormula rightFormula} :
      CLL (leftFormula :: antecedent) succedent →
      CLL (rightFormula :: antecedent) succedent →
      CLL ((leftFormula ⊕ rightFormula) :: antecedent) succedent

  | plusRightLeft {antecedent succedent leftFormula rightFormula} :
      CLL antecedent (leftFormula :: succedent) →
      CLL antecedent ((leftFormula ⊕ rightFormula) :: succedent)

  | plusRightRight {antecedent succedent leftFormula rightFormula} :
      CLL antecedent (rightFormula :: succedent) →
      CLL antecedent ((leftFormula ⊕ rightFormula) :: succedent)

  | zeroLeft {antecedent succedent} :
      CLL (.zero :: antecedent) succedent

  | bangWeakeningLeft {antecedent succedent formula} :
      CLL antecedent succedent →
      CLL ((.bang formula) :: antecedent) succedent

  | bangContractionLeft {antecedent succedent formula} :
      CLL ((.bang formula) :: (.bang formula) :: antecedent) succedent →
      CLL ((.bang formula) :: antecedent) succedent

  | bangLeft {antecedent succedent formula} :
      CLL (formula :: antecedent) succedent →
      CLL ((.bang formula) :: antecedent) succedent

  | bangRight {antecedent succedent formula} :
      allBang antecedent →
      allWhyNot succedent →
      CLL antecedent (formula :: succedent) →
      CLL antecedent ((.bang formula) :: succedent)

  | whyNotWeakeningRight {antecedent succedent formula} :
      CLL antecedent succedent →
      CLL antecedent ((.whyNot formula) :: succedent)

  | whyNotContractionRight {antecedent succedent formula} :
      CLL antecedent ((.whyNot formula) :: (.whyNot formula) :: succedent) →
      CLL antecedent ((.whyNot formula) :: succedent)

  | whyNotRight {antecedent succedent formula} :
      CLL antecedent (formula :: succedent) →
      CLL antecedent ((.whyNot formula) :: succedent)

  | whyNotLeft {antecedent succedent formula} :
      allBang antecedent →
      allWhyNot succedent →
      CLL (formula :: antecedent) succedent →
      CLL ((.whyNot formula) :: antecedent) succedent

open IntuitionisticLinearFormula

inductive ILL : IntuitionisticLinearContext → IntuitionisticLinearFormula → Prop where
  | assumption {formula} :
      ILL [formula] formula

  | exchangeLeft {leftContext rightContext firstFormula secondFormula conclusion} :
      ILL (leftContext ++ firstFormula :: secondFormula :: rightContext) conclusion →
      ILL (leftContext ++ secondFormula :: firstFormula :: rightContext) conclusion

  | cut {leftAntecedent rightAntecedent cutFormula conclusion} :
      ILL leftAntecedent cutFormula →
      ILL (cutFormula :: rightAntecedent) conclusion →
      ILL (leftAntecedent ++ rightAntecedent) conclusion

  | oneRight :
      ILL [] .one

  | oneLeft {antecedent conclusion} :
      ILL antecedent conclusion →
      ILL (.one :: antecedent) conclusion

  | tensorRight {leftAntecedent rightAntecedent leftFormula rightFormula} :
      ILL leftAntecedent leftFormula →
      ILL rightAntecedent rightFormula →
      ILL (leftAntecedent ++ rightAntecedent) (.tensor leftFormula rightFormula)

  | tensorLeft {antecedent conclusion leftFormula rightFormula} :
      ILL (leftFormula :: rightFormula :: antecedent) conclusion →
      ILL ((.tensor leftFormula rightFormula) :: antecedent) conclusion

  | lolliRight {antecedent antecedentFormula consequentFormula} :
      ILL (antecedentFormula :: antecedent) consequentFormula →
      ILL antecedent (.lolli antecedentFormula consequentFormula)

  | lolliLeft {leftAntecedent rightAntecedent antecedentFormula consequentFormula conclusion} :
      ILL leftAntecedent antecedentFormula →
      ILL (consequentFormula :: rightAntecedent) conclusion →
      ILL ((.lolli antecedentFormula consequentFormula) :: (leftAntecedent ++ rightAntecedent)) conclusion

  | topRight {antecedent} :
      ILL antecedent .top

  | zeroLeft {antecedent conclusion} :
      ILL (.zero :: antecedent) conclusion

  | withLeftLeft {antecedent conclusion leftFormula rightFormula} :
      ILL (leftFormula :: antecedent) conclusion →
      ILL ((.with leftFormula rightFormula) :: antecedent) conclusion

  | withLeftRight {antecedent conclusion leftFormula rightFormula} :
      ILL (rightFormula :: antecedent) conclusion →
      ILL ((.with leftFormula rightFormula) :: antecedent) conclusion

  | withRight {antecedent leftFormula rightFormula} :
      ILL antecedent leftFormula →
      ILL antecedent rightFormula →
      ILL antecedent (.with leftFormula rightFormula)

  | plusLeft {antecedent conclusion leftFormula rightFormula} :
      ILL (leftFormula :: antecedent) conclusion →
      ILL (rightFormula :: antecedent) conclusion →
      ILL ((.plus leftFormula rightFormula) :: antecedent) conclusion

  | plusRightLeft {antecedent leftFormula rightFormula} :
      ILL antecedent leftFormula →
      ILL antecedent (.plus leftFormula rightFormula)

  | plusRightRight {antecedent leftFormula rightFormula} :
      ILL antecedent rightFormula →
      ILL antecedent (.plus leftFormula rightFormula)

  | bangWeakening {antecedent formula conclusion} :
      ILL antecedent conclusion →
      ILL ((.bang formula) :: antecedent) conclusion

  | bangContraction {antecedent formula conclusion} :
      ILL ((.bang formula) :: (.bang formula) :: antecedent) conclusion →
      ILL ((.bang formula) :: antecedent) conclusion

  | bangLeft {antecedent formula conclusion} :
      ILL (formula :: antecedent) conclusion →
      ILL ((.bang formula) :: antecedent) conclusion

  | bangRight {antecedent formula} :
      allBangIntuitionistic antecedent →
      ILL antecedent formula →
      ILL antecedent (.bang formula)

abbrev LinearLogic := CLL

end FastProofTheory.Proof
