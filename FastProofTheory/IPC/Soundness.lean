import FastProofTheory.IPC.Derivation
import FastProofTheory.IPC.Kripke

namespace FastProofTheory.IPC

theorem forces_ctx_exchange
    {M : Kripke.Model α} {w : M.World}
    {Γ₁ Γ₂ : Context α} {A B : Formula α}
    (hΓ : Kripke.ForcesCtx M w (Γ₁ ++ A :: B :: Γ₂)) :
    Kripke.ForcesCtx M w (Γ₁ ++ B :: A :: Γ₂) := by
  intro v hv C hC
  exact hΓ hv (by
    simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using hC)

theorem sound
    {Γ : Context α} {A : Formula α}
    (p : Derivation Γ A) :
    ∀ {M : Kripke.Model α} {w : M.World}, Kripke.ForcesCtx M w Γ → Kripke.Forces M w A := by
  intro M w hΓ
  induction p generalizing M w with
  | init hmem =>
      exact hΓ (M.refl w) hmem
  | botLeft hbot =>
      exact False.elim (hΓ (M.refl w) hbot)
  | exchange body ih =>
      exact ih (forces_ctx_exchange hΓ)
  | impRight body ih =>
      intro v hv hA
      exact ih (Kripke.forces_ctx_cons hv hΓ hA)
  | impLeft left right ihLeft ihRight =>
      have hA := ihLeft (Kripke.forces_ctx_tail hΓ)
      have hImp := hΓ (M.refl w) (List.mem_cons.2 (Or.inl rfl))
      have hB := hImp w (M.refl w) hA
      exact ihRight (Kripke.forces_ctx_cons (M.refl w) (Kripke.forces_ctx_tail hΓ) hB)
  | andRight left right ihLeft ihRight =>
      exact ⟨ihLeft hΓ, ihRight hΓ⟩
  | andLeft body ih =>
      have hAB := hΓ (M.refl w) (List.mem_cons.2 (Or.inl rfl))
      exact ih (Kripke.forces_ctx_cons (M.refl w) (Kripke.forces_ctx_cons (M.refl w) (Kripke.forces_ctx_tail hΓ) hAB.2) hAB.1)
  | orRightLeft body ih =>
      exact Or.inl (ih hΓ)
  | orRightRight body ih =>
      exact Or.inr (ih hΓ)
  | orLeft left right ihLeft ihRight =>
      have hOr := hΓ (M.refl w) (List.mem_cons.2 (Or.inl rfl))
      cases hOr with
      | inl hA =>
          exact ihLeft (Kripke.forces_ctx_cons (M.refl w) (Kripke.forces_ctx_tail hΓ) hA)
      | inr hB =>
          exact ihRight (Kripke.forces_ctx_cons (M.refl w) (Kripke.forces_ctx_tail hΓ) hB)

end FastProofTheory.IPC
