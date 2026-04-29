import FastProofTheory.IPC.Examples
import Logic.IPC.Countermodel
import Logic.IPC.Soundness

namespace FastProofTheory.IPC.Audit

open Logic.IPC
open Logic.IPC.Kripke
open Logic.IPC.Countermodel

def p : Formula := .atom "p"
def q : Formula := .atom "q"

def neg (A : Formula) : Formula := .imp A .bot

def p_imp_p : Derivation [] (p -> p) :=
  .impRight (.init (by decide))

def and_comm : Derivation [] ((p ∧ q) -> (q ∧ p)) :=
  .impRight (.andLeft (.andRight (.init (by decide)) (.init (by decide))))

def or_comm : Derivation [] ((p ∨ q) -> (q ∨ p)) :=
  .impRight (
    .orLeft
      (.orRightRight (.init (by decide)))
      (.orRightLeft (.init (by decide))))

private def atomFalseFrame : FiniteFrame where
  n := 1
  le := fun _ _ => true
  refl := by intro w; decide
  trans := by intro u v w huv hvw; decide

private def atomFalseVal : String → Fin 1 → Bool :=
  fun _ _ => false

private def atomFalseMono :
    ∀ pName u v, atomFalseFrame.le u v = true → atomFalseVal pName u = true → atomFalseVal pName v = true := by
  intro pName u v huv hv
  simp [atomFalseVal] at hv ⊢

private def atomFalseModel : FiniteModel where
  toFiniteFrame := atomFalseFrame
  val := atomFalseVal
  mono := atomFalseMono

theorem root_not_forces_p : ¬ Forces (toModel atomFalseModel) (0 : Fin 1) p := by
  intro h
  cases h

theorem p_not_derivable : Not (Nonempty (Derivation [] p)) := by
  intro h
  rcases h with ⟨d⟩
  have hp : Forces (toModel atomFalseModel) (0 : Fin 1) p := by
    exact sound d (M := toModel atomFalseModel) (w := (0 : Fin 1)) (by intro v hv A hA; cases hA)
  exact root_not_forces_p hp

end FastProofTheory.IPC.Audit
