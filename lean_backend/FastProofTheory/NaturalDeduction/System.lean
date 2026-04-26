import Logic.Rules

namespace FastProofTheory.NaturalDeduction

open Rules

abbrev Formula := Rules.Formula

inductive PropositionalFragment where
  | imp
  | full
deriving BEq, DecidableEq, Inhabited, Repr

inductive System where
  | njp (fragment : PropositionalFragment)
  | nkp (fragment : PropositionalFragment)
  | systemF
deriving BEq, DecidableEq, Inhabited, Repr

def PropositionalFragment.displayName : PropositionalFragment → String
  | .imp => "IMP"
  | .full => "FULL"

def System.displayName : System → String
  | .njp .imp => "NJp with IMP"
  | .njp .full => "NJp"
  | .nkp .imp => "NKp with IMP"
  | .nkp .full => "NKp"
  | .systemF => "SYSTEM_F"

def PropositionalFragment.allowsFormula : PropositionalFragment → Formula → Bool
  | .imp, .atom _ => true
  | .imp, .imp a b => PropositionalFragment.allowsFormula .imp a && PropositionalFragment.allowsFormula .imp b
  | .imp, .bot => true
  | .imp, _ => false
  | .full, .atom _ => true
  | .full, .imp a b => PropositionalFragment.allowsFormula .full a && PropositionalFragment.allowsFormula .full b
  | .full, .and a b => PropositionalFragment.allowsFormula .full a && PropositionalFragment.allowsFormula .full b
  | .full, .or a b => PropositionalFragment.allowsFormula .full a && PropositionalFragment.allowsFormula .full b
  | .full, .bot => true
  | .full, _ => false

def System.allowsFormula : System → Formula → Bool
  | .njp fragment, formula => fragment.allowsFormula formula
  | .nkp fragment, formula => fragment.allowsFormula formula
  | .systemF, .atom _ => true
  | .systemF, .imp a b => System.allowsFormula .systemF a && System.allowsFormula .systemF b
  | .systemF, .bot => true
  | .systemF, .all _ body => System.allowsFormula .systemF body
  | .systemF, _ => false

def System.isNJp : System → Bool
  | .njp _ => true
  | _ => false

def System.isNKp : System → Bool
  | .nkp _ => true
  | _ => false

def System.isSystemF : System → Bool
  | .systemF => true
  | _ => false

def System.hasValidConfiguration : System → Bool
  | .njp .imp => true
  | .njp .full => true
  | .nkp .full => true
  | .systemF => true
  | .nkp .imp => false

end FastProofTheory.NaturalDeduction
