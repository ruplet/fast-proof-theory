import FastProofTheory.Rules
import FastProofTheory.Gentzen.Rules.Linear

namespace FastProofTheory.Gentzen

open Rules

abbrev Formula := Rules.Formula

inductive LinearLogic where
  | ll
  | llBang
deriving BEq, DecidableEq, Inhabited, Repr

inductive System where
  | linearLogic (logic : LinearLogic)
deriving BEq, DecidableEq, Inhabited, Repr

def LinearLogic.displayName : LinearLogic → String
  | .ll => "LL"
  | .llBang => "LL!"

def LinearLogic.allowsExponentials : LinearLogic → Bool
  | .ll => false
  | .llBang => true

partial def LinearLogic.allowsFormula : LinearLogic → Formula → Bool
  | .ll, .atom _ => true
  | .ll, .pred _ _ => false
  | .ll, .tensor a b => LinearLogic.allowsFormula .ll a && LinearLogic.allowsFormula .ll b
  | .ll, .with a b => LinearLogic.allowsFormula .ll a && LinearLogic.allowsFormula .ll b
  | .ll, .plus a b => LinearLogic.allowsFormula .ll a && LinearLogic.allowsFormula .ll b
  | .ll, .lolli a b => LinearLogic.allowsFormula .ll a && LinearLogic.allowsFormula .ll b
  | .ll, .bang _ => false
  | .ll, .one => true
  | .ll, .zero => true
  | .ll, .top => true
  | .ll, .bottom => true
  | .ll, _ => false
  | .llBang, .atom _ => true
  | .llBang, .pred _ _ => false
  | .llBang, .tensor a b => LinearLogic.allowsFormula .llBang a && LinearLogic.allowsFormula .llBang b
  | .llBang, .with a b => LinearLogic.allowsFormula .llBang a && LinearLogic.allowsFormula .llBang b
  | .llBang, .plus a b => LinearLogic.allowsFormula .llBang a && LinearLogic.allowsFormula .llBang b
  | .llBang, .lolli a b => LinearLogic.allowsFormula .llBang a && LinearLogic.allowsFormula .llBang b
  | .llBang, .bang a => LinearLogic.allowsFormula .llBang a
  | .llBang, .one => true
  | .llBang, .zero => true
  | .llBang, .top => true
  | .llBang, .bottom => true
  | .llBang, _ => false

def LinearLogic.allowsRule : LinearLogic → FastProofTheory.Gentzen.Rules.Linear.RuleKind → Bool
  | .ll, .bangIntro => false
  | .ll, .bangLeft => false
  | _, _ => true

def System.displayName : System → String
  | .linearLogic logic => logic.displayName

def System.allowsFormula : System → Formula → Bool
  | .linearLogic logic, formula => logic.allowsFormula formula

def System.allowsRule : System → FastProofTheory.Gentzen.Rules.Linear.RuleKind → Bool
  | .linearLogic logic, rule => logic.allowsRule rule

def System.linearLogic? : System → Option LinearLogic
  | .linearLogic logic => some logic

end FastProofTheory.Gentzen
