import FastProofTheory.IPC.Syntax

namespace FastProofTheory.IPC.Kripke

universe u v

variable (α : Type v)

structure Model where
  World : Type u
  le : World → World → Prop
  refl : ∀ w, le w w
  trans : ∀ {u v w}, le u v → le v w → le u w
  forces : World → α → Prop
  mono : ∀ {p : α} {w v : World}, le w v → forces w p → forces v p

namespace Model

def Forces {α} (M : Model α) : M.World → FastProofTheory.IPC.Formula α → Prop
  | w, .atom p => M.forces w p
  | _, .bot => False
  | w, .imp A B => ∀ v, M.le w v → Forces M v A → Forces M v B
  | w, .and A B => Forces M w A ∧ Forces M w B
  | w, .or A B => Forces M w A ∨ Forces M w B


namespace Forces
theorem mono {α}
    {M : Model α} {w v : M.World} {A : FastProofTheory.IPC.Formula α}
    (hwv : M.le w v) :
    Forces M w A -> Forces M v A := by
  induction A generalizing w v with
  | atom p =>
      intro h
      exact M.mono hwv h
  | bot =>
      intro h
      exact False.elim h
  | imp A B ihA ihB =>
      intro h
      intro u huv hA
      exact h u (M.trans hwv huv) hA
  | and A B ihA ihB =>
      intro h
      exact ⟨ihA hwv h.1, ihB hwv h.2⟩
  | or A B ihA ihB =>
      intro h
      cases h with
      | inl hA => exact Or.inl (ihA hwv hA)
      | inr hB => exact Or.inr (ihB hwv hB)

def Contex (M : Model α) (w : M.World) (Γ : FastProofTheory.IPC.Context α) : Prop :=
  ∀ {v : M.World}, M.le w v → ∀ {A : FastProofTheory.IPC.Formula α}, A ∈ Γ → Forces M v A

-- theorem forces_ctx_tail
--     {M : Model α} {w : M.World} {A : FastProofTheory.IPC.Formula α} {Γ : FastProofTheory.IPC.Context α}
--     (hΓ : ForcesCtx M w (A :: Γ)) :
--     ForcesCtx M w Γ := by
--   intro v hv B hB
--   exact hΓ hv (List.mem_cons_of_mem _ hB)

-- theorem forces_ctx_cons
--     {M : Model} {w v : M.World} {A : FastProofTheory.IPC.Formula} {Γ : FastProofTheory.IPC.Context}
--     (hwv : M.le w v)
--     (hΓ : ForcesCtx M w Γ)
--     (hA : Forces M v A) :
--     ForcesCtx M v (A :: Γ) := by
--   intro u hu B hB
--   rcases List.mem_cons.1 hB with rfl | hB
--   · exact forces_mono hu hA
--   · exact hΓ (M.trans hwv hu) hB

-- def ValidAt (M : Model) (w : M.World) (A : FastProofTheory.IPC.Formula) : Prop :=
--   Forces M w A

-- def GloballyValid (M : Model) (A : FastProofTheory.IPC.Formula) : Prop :=
--   ∀ w, Forces M w A

-- def Entails (M : Model) (Γ : FastProofTheory.IPC.Context) (A : FastProofTheory.IPC.Formula) : Prop :=
--   ∀ w, ForcesCtx M w Γ → Forces M w A


end Forces
end Model

abbrev Forces {α} (M : Model α) (w : M.World) (A : FastProofTheory.IPC.Formula α) : Prop :=
  Model.Forces M w A

abbrev ForcesCtx {α} (M : Model α) (w : M.World) (Γ : FastProofTheory.IPC.Context α) : Prop :=
  Model.Forces.Contex α M w Γ

theorem forces_ctx_tail {α}
    {M : Model α} {w : M.World} {A : FastProofTheory.IPC.Formula α}
    {Γ : FastProofTheory.IPC.Context α}
    (hΓ : ForcesCtx M w (A :: Γ)) :
    ForcesCtx M w Γ := by
  intro v hv B hB
  exact hΓ hv (List.mem_cons_of_mem A hB)

theorem forces_ctx_cons {α}
    {M : Model α} {w v : M.World} {A : FastProofTheory.IPC.Formula α}
    {Γ : FastProofTheory.IPC.Context α}
    (hwv : M.le w v)
    (hΓ : ForcesCtx M w Γ)
    (hA : Forces M v A) :
    ForcesCtx M v (A :: Γ) := by
  intro u hu B hB
  rcases List.mem_cons.1 hB with rfl | hB
  · exact Model.Forces.mono hu hA
  · exact hΓ (M.trans hwv hu) hB


end FastProofTheory.IPC.Kripke
