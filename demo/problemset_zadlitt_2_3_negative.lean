import Logic.IPC.Countermodel

namespace Demo.ZadlittProblem2_3.Negative

open Logic.IPC
open Logic.IPC.Countermodel

def p : Formula := .atom "p"

private def frame : FiniteFrame where
  n := 1
  le := fun _ _ => true
  refl := by intro w; decide
  trans := by intro u v w huv hvw; decide

private def model : FiniteModel where
  toFiniteFrame := frame
  val := fun _ _ => false
  mono := by
    intro p u v huv hp
    simp at hp

def counterP : Countermodel where
  M := model
  root := ⟨0, by decide⟩
  formula := p
  refutes := by
    unfold Logic.IPC.Countermodel.eval
    simp [model, frame]
    intro h
    cases h

theorem p_not_derivable :
    ¬ Nonempty (Derivation [] p) := by
  exact countermodel_not_derivable counterP

end Demo.ZadlittProblem2_3.Negative
