import FastProofTheory.IPC.Soundness

namespace FastProofTheory.IPC.Countermodel

open FastProofTheory.IPC
open FastProofTheory.IPC.Kripke

structure FiniteFrame where
  n : Nat
  le : Fin n → Fin n → Bool
  refl : ∀ w, le w w = true
  trans : ∀ u v w, le u v = true → le v w = true → le u w = true

structure FiniteModel (α : Type) extends FiniteFrame where
  val : α → Fin n → Bool
  mono : ∀ p u v, le u v = true → val p u = true → val p v = true

def toModel {α : Type} (M : FiniteModel α) : Kripke.Model α where
  World := Fin M.n
  le := fun u v => M.le u v = true
  refl := by
    intro w
    exact M.refl w
  trans := by
    intro u v w huv hvw
    exact M.trans u v w huv hvw
  forces := fun w p => M.val p w = true
  mono := by
    intro p u v huv hv
    exact M.mono p u v huv hv

noncomputable def eval {α : Type} (M : FiniteModel α) (w : Fin M.n) (A : Formula α) : Bool := by
  classical
  exact if Forces (toModel M) w A then true else false

theorem eval_correct {α : Type} (M : FiniteModel α) (w : Fin M.n) (A : Formula α) :
    eval M w A = true ↔ Forces (toModel M) w A := by
  unfold eval
  by_cases h : Forces (toModel M) w A <;> simp [h]

structure Countermodel (α : Type) where
  M : FiniteModel α
  root : Fin M.n
  formula : Formula α
  refutes : eval M root formula = false

theorem countermodel_not_derivable {α : Type} (c : Countermodel α) :
    Not (Nonempty (FastProofTheory.IPC.Derivation [] c.formula)) := by
  intro d
  rcases d with ⟨d⟩
  have hforces : Forces (toModel c.M) c.root c.formula := by
    have h := FastProofTheory.IPC.sound d (M := toModel c.M) (w := c.root) (by intro v hv A hA; nomatch hA)
    exact h
  have heval : eval c.M c.root c.formula = true := by
    exact (eval_correct c.M c.root c.formula).2 hforces
  rw [c.refutes] at heval
  cases heval

end FastProofTheory.IPC.Countermodel
