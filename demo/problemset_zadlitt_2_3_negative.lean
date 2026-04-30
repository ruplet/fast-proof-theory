import FastProofTheory.IPC.Countermodel

namespace Demo.ZadlittProblem2_3.Negative

open FastProofTheory.IPC
open FastProofTheory.IPC.Countermodel

inductive Atom where
  | p
deriving DecidableEq, Repr

def p : Formula Atom := .atom .p

private def frame : FiniteFrame where
  n := 1
  le := fun _ _ => true
  refl := by intro w; decide
  trans := by intro u v w huv hvw; decide

private def model : FiniteModel Atom where
  toFiniteFrame := frame
  val := fun _ _ => false
  mono := by
    intro atom u v huv hp
    simp at hp

def counterP : Countermodel Atom where
  M := model
  root := ⟨0, by decide⟩
  formula := p
  refutes := by
    unfold FastProofTheory.IPC.Countermodel.eval
    simp [model, frame]
    intro h
    cases h

theorem p_not_derivable :
    ¬ Nonempty (Derivation [] p) := by
  exact countermodel_not_derivable counterP

end Demo.ZadlittProblem2_3.Negative
