import FastProofTheory.Rules
import FastProofTheory.IPC.Syntax

namespace FastProofTheory.IPC

inductive Fragment where
  | implicational
  | propositional
  | full
deriving DecidableEq, Repr

def Formula.InFragment {α : Type} : Fragment -> Formula α -> Prop
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

def Formula.IsIPC {α : Type} : Formula α -> Prop :=
  Formula.InFragment .full

abbrev WellFormed (α : Type) (fragment : Fragment) := { A : Formula α // A.InFragment fragment }

def atom {α : Type} (name : α) : WellFormed α fragment :=
  ⟨.atom name, by cases fragment <;> trivial⟩

end FastProofTheory.IPC
