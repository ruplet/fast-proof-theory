import Logic.Rules

namespace Logic.IPC

open Rules

inductive Fragment where
  | implicational
  | propositional
  | full
deriving DecidableEq, Repr

abbrev Formula := Rules.Formula

def Formula.InFragment : Fragment → Formula → Prop
  | .implicational, .atom _ => True
  | .implicational, .imp a b => Formula.InFragment .implicational a ∧ Formula.InFragment .implicational b
  | .implicational, .bot => True
  | .implicational, _ => False
  | .propositional, .atom _ => True
  | .propositional, .and a b => Formula.InFragment .propositional a ∧ Formula.InFragment .propositional b
  | .propositional, .or a b => Formula.InFragment .propositional a ∧ Formula.InFragment .propositional b
  | .propositional, .bot => True
  | .propositional, _ => False
  | .full, .atom _ => True
  | .full, .imp a b => Formula.InFragment .full a ∧ Formula.InFragment .full b
  | .full, .and a b => Formula.InFragment .full a ∧ Formula.InFragment .full b
  | .full, .or a b => Formula.InFragment .full a ∧ Formula.InFragment .full b
  | .full, .bot => True
  | .full, _ => False

def Formula.IsIPC : Formula → Prop :=
  Formula.InFragment .full

abbrev WellFormed (fragment : Fragment) := { A : Formula // A.InFragment fragment }

def atom (name : String) : WellFormed fragment :=
  ⟨.atom name, by cases fragment <;> trivial⟩

end Logic.IPC
