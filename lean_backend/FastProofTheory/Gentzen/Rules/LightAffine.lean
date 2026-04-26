import FastProofTheory.Gentzen.Rules.Propositional

namespace FastProofTheory.Gentzen.Rules.LightAffine

abbrev RuleKind := FastProofTheory.Gentzen.Rules.Propositional.RuleKind

abbrev RuleSystemSpec := FastProofTheory.Gentzen.Rules.Propositional.RuleSystemSpec

def lightAffine : RuleSystemSpec :=
  {
    displayName := "light affine propositional Gentzen"
    allowsFormula := FastProofTheory.Gentzen.Rules.Propositional.allowsPropositionalFormula
    allowsRule := fun
      | .classical => false
      | _ => true
  }

end FastProofTheory.Gentzen.Rules.LightAffine
