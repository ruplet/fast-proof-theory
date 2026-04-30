namespace FastProofTheory.IPC

variable (α : Type v)

inductive Formula where
  | atom : α -> Formula
  | bot : Formula
  | imp : Formula -> Formula -> Formula
  | and : Formula -> Formula -> Formula
  | or : Formula -> Formula -> Formula
deriving DecidableEq, Repr

abbrev Context := List (Formula α)

def Formula.neg (A : Formula α) : Formula α :=
  Formula.imp A Formula.bot

scoped notation "⊥" => Formula.bot
scoped infixr:60 " -> " => Formula.imp
scoped infixr:55 " ∧ " => Formula.and
scoped infixr:50 " ∨ " => Formula.or
scoped prefix:70 "¬" => Formula.neg

end FastProofTheory.IPC
