import Logic.Rules

namespace FastProofTheory.Gentzen.Rules.Propositional

open Rules

abbrev Formula := Rules.Formula

inductive RuleKind where
  | assumption
  | impIntro
  | impElim
  | andIntro
  | andLeft
  | andRight
  | orLeft
  | orRight
  | orElim
  | bottomElim
  | classical
deriving BEq, DecidableEq, Inhabited, Repr

def RuleKind.displayName : RuleKind → String
  | .assumption => "assumption"
  | .impIntro => "impIntro"
  | .impElim => "impElim"
  | .andIntro => "andIntro"
  | .andLeft => "andLeft"
  | .andRight => "andRight"
  | .orLeft => "orLeft"
  | .orRight => "orRight"
  | .orElim => "orElim"
  | .bottomElim => "bottomElim"
  | .classical => "classical"

structure RuleSystemSpec where
  displayName : String
  allowsFormula : Formula → Bool
  allowsRule : RuleKind → Bool := fun _ => true

partial def allowsPropositionalFormula : Formula → Bool
  | .atom _ => true
  | .imp a b => allowsPropositionalFormula a && allowsPropositionalFormula b
  | .and a b => allowsPropositionalFormula a && allowsPropositionalFormula b
  | .or a b => allowsPropositionalFormula a && allowsPropositionalFormula b
  | .bot => true
  | _ => false

def intuitionistic : RuleSystemSpec :=
  {
    displayName := "intuitionistic propositional Gentzen"
    allowsFormula := allowsPropositionalFormula
    allowsRule := fun
      | .classical => false
      | _ => true
  }

def classical : RuleSystemSpec :=
  {
    displayName := "classical propositional Gentzen"
    allowsFormula := allowsPropositionalFormula
  }

end FastProofTheory.Gentzen.Rules.Propositional
