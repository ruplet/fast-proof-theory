import Logic.IPC.Soundness

namespace Logic.IPC.Countermodel

open Logic.IPC
open Logic.IPC.Kripke

structure FiniteFrame where
  n : Nat
  le : Fin n → Fin n → Bool
  refl : ∀ w, le w w = true
  trans : ∀ u v w, le u v = true → le v w = true → le u w = true

structure FiniteModel extends FiniteFrame where
  val : String → Fin n → Bool
  mono : ∀ p u v, le u v = true → val p u = true → val p v = true

def toModel (M : FiniteModel) : Kripke.Model where
  World := Fin M.n
  le := fun u v => M.le u v = true
  refl := by
    intro w
    exact M.refl w
  trans := by
    intro u v w huv hvw
    exact M.trans u v w huv hvw
  val := fun p w => M.val p w = true
  mono := by
    intro p u v huv hv
    exact M.mono p u v huv hv

noncomputable def eval (M : FiniteModel) (w : Fin M.n) (A : Formula) : Bool := by
  classical
  exact if Forces (toModel M) w A then true else false

theorem eval_correct (M : FiniteModel) (w : Fin M.n) (A : Formula) :
    eval M w A = true ↔ Forces (toModel M) w A := by
  unfold eval
  by_cases h : Forces (toModel M) w A <;> simp [h]

structure Countermodel where
  M : FiniteModel
  root : Fin M.n
  formula : Formula
  refutes : eval M root formula = false

theorem countermodel_not_derivable (c : Countermodel) :
    Not (Nonempty (Logic.IPC.Derivation [] c.formula)) := by
  intro d
  rcases d with ⟨d⟩
  have hforces : Forces (toModel c.M) c.root c.formula := by
    have h := Logic.IPC.sound d (M := toModel c.M) (w := c.root) (by intro v hv A hA; nomatch hA)
    exact h
  have heval : eval c.M c.root c.formula = true := by
    exact (eval_correct c.M c.root c.formula).2 hforces
  rw [c.refutes] at heval
  cases heval

end Logic.IPC.Countermodel
