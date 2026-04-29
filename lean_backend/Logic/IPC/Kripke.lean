import Logic.IPC.Syntax

namespace Logic.IPC.Kripke

universe u

structure Frame where
  World : Type u
  le : World → World → Prop
  refl : ∀ w, le w w
  trans : ∀ {u v w}, le u v → le v w → le u w

structure Model extends Frame where
  val : String → World → Prop
  mono : ∀ {p : String} {w v : World}, le w v → val p w → val p v

def Forces (M : Model) : M.World → Logic.IPC.Formula → Prop
  | w, .atom p => M.val p w
  | _, .bot => False
  | w, .imp A B => ∀ v, M.le w v → Forces M v A → Forces M v B
  | w, .and A B => Forces M w A ∧ Forces M w B
  | w, .or A B => Forces M w A ∨ Forces M w B

theorem forces_mono
    {M : Model} {w v : M.World} {A : Logic.IPC.Formula}
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

def ForcesCtx (M : Model) (w : M.World) (Γ : Logic.IPC.Context) : Prop :=
  ∀ {v : M.World}, M.le w v → ∀ {A : Logic.IPC.Formula}, A ∈ Γ → Forces M v A

theorem forces_ctx_tail
    {M : Model} {w : M.World} {A : Logic.IPC.Formula} {Γ : Logic.IPC.Context}
    (hΓ : ForcesCtx M w (A :: Γ)) :
    ForcesCtx M w Γ := by
  intro v hv B hB
  exact hΓ hv (List.mem_cons_of_mem _ hB)

theorem forces_ctx_cons
    {M : Model} {w v : M.World} {A : Logic.IPC.Formula} {Γ : Logic.IPC.Context}
    (hwv : M.le w v)
    (hΓ : ForcesCtx M w Γ)
    (hA : Forces M v A) :
    ForcesCtx M v (A :: Γ) := by
  intro u hu B hB
  rcases List.mem_cons.1 hB with rfl | hB
  · exact forces_mono hu hA
  · exact hΓ (M.trans hwv hu) hB

def ValidAt (M : Model) (w : M.World) (A : Logic.IPC.Formula) : Prop :=
  Forces M w A

def GloballyValid (M : Model) (A : Logic.IPC.Formula) : Prop :=
  ∀ w, Forces M w A

def Entails (M : Model) (Γ : Logic.IPC.Context) (A : Logic.IPC.Formula) : Prop :=
  ∀ w, ForcesCtx M w Γ → Forces M w A

end Logic.IPC.Kripke
