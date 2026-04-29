namespace Logic.IPC

inductive Formula where
  | atom : String -> Formula
  | bot : Formula
  | imp : Formula -> Formula -> Formula
  | and : Formula -> Formula -> Formula
  | or : Formula -> Formula -> Formula
deriving DecidableEq, Repr

abbrev Context := List Formula

def Formula.neg (A : Formula) : Formula :=
  Formula.imp A Formula.bot

scoped notation "⊥" => Formula.bot
scoped infixr:60 " -> " => Formula.imp
scoped infixr:55 " ∧ " => Formula.and
scoped infixr:50 " ∨ " => Formula.or
scoped prefix:70 "¬" => Formula.neg

end Logic.IPC
