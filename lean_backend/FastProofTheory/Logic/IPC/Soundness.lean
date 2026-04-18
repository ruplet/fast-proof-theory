import FastProofTheory.Logic.IPC.PropositionalND
import FastProofTheory.Logic.IPC.Kripke

namespace FastProofTheory.Logic.IPC

open FastProofTheory.Logic.IPC.Kripke
open FastProofTheory.Logic.IPC.PropositionalND

namespace PropositionalND

def HoldsCtx (M : Model) (w : M.World) (Γ : Context) : Prop :=
  ∀ ⦃v : M.World⦄, M.le w v → ∀ ⦃A : Formula⦄, A ∈ Γ → Forces M v A.1

private theorem forces_mono
    {M : Model} {w v : M.World} {A : Rules.Formula}
    (hwv : M.le w v) :
    Forces M w A → Forces M v A := by
  induction A generalizing w v with
  | atom name =>
      intro h
      exact M.mono hwv h
  | bot =>
      intro h
      exact False.elim h
  | and A B ihA ihB =>
      intro h
      exact ⟨ihA hwv h.1, ihB hwv h.2⟩
  | or A B ihA ihB =>
      intro h
      cases h with
      | inl hA => exact Or.inl (ihA hwv hA)
      | inr hB => exact Or.inr (ihB hwv hB)
  | imp A B ihA ihB =>
      intro hImp u hvu hA
      exact hImp u (M.trans hwv hvu) hA
  | _ =>
      intro h
      exact False.elim h

private theorem holdsCtx_exchange
    {M : Model} {w : M.World}
    {Γ₁ Γ₂ : Context} {A B : Formula}
    (hΓ : HoldsCtx M w (Γ₁ ++ B :: A :: Γ₂)) :
    HoldsCtx M w (Γ₁ ++ A :: B :: Γ₂) := by
  intro v hv C hC
  exact hΓ hv (by simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using hC)

private theorem holdsCtx_tail
    {M : Model} {w : M.World}
    {A : Formula} {Γ : Context}
    (hΓ : HoldsCtx M w (A :: Γ)) :
    HoldsCtx M w Γ := by
  intro v hv C hC
  exact hΓ hv (List.mem_cons_of_mem _ hC)

private theorem holdsCtx_contract
    {M : Model} {w : M.World}
    {A : Formula} {Γ : Context}
    (hΓ : HoldsCtx M w (A :: Γ)) :
    HoldsCtx M w (A :: A :: Γ) := by
  intro v hv C hC
  rcases List.mem_cons.1 hC with hC | hC
  · cases hC
    exact hΓ hv (List.mem_cons.2 (Or.inl rfl))
  · exact hΓ hv hC

private theorem holdsCtx_cons
    {M : Model} {w v : M.World}
    {A : Formula} {Γ : Context}
    (hv : M.le w v)
    (hΓ : HoldsCtx M w Γ)
    (hA : Forces M v A.1) :
    HoldsCtx M v (A :: Γ) := by
  intro u hu C hC
  rcases List.mem_cons.1 hC with hC | hC
  · cases hC
    exact forces_mono hu hA
  · exact hΓ (M.trans hv hu) hC

theorem sound
    {Γ : Context}
    {A : Formula}
    (p : Derivation Γ A) :
    ∀ {M : Model} {w : M.World}, HoldsCtx M w Γ → Forces M w A.1 := by
  induction p with
  | hyp hmem =>
      intro M w hΓ
      exact hΓ (M.refl w) hmem
  | exchange p ih =>
      intro M w hΓ
      exact ih (holdsCtx_exchange hΓ)
  | weaken p ih =>
      intro M w hΓ
      exact ih (holdsCtx_tail hΓ)
  | contract p ih =>
      intro M w hΓ
      exact ih (holdsCtx_contract hΓ)
  | impIntro p ih =>
      intro M w hΓ
      intro v hv hA
      exact ih (holdsCtx_cons hv hΓ hA)
  | impElim p q ihP ihQ =>
      intro M w hΓ
      exact (ihP hΓ) w (M.refl w) (ihQ hΓ)
  | andIntro p q ihP ihQ =>
      intro M w hΓ
      exact ⟨ihP hΓ, ihQ hΓ⟩
  | andLeft p ih =>
      intro M w hΓ
      exact (ih hΓ).1
  | andRight p ih =>
      intro M w hΓ
      exact (ih hΓ).2
  | orLeft p ih =>
      intro M w hΓ
      exact Or.inl (ih hΓ)
  | orRight p ih =>
      intro M w hΓ
      exact Or.inr (ih hΓ)
  | orElim p q r ihP ihQ ihR =>
      intro M w hΓ
      cases ihP hΓ with
      | inl hLeft =>
          exact ihQ (holdsCtx_cons (M.refl w) hΓ hLeft)
      | inr hRight =>
          exact ihR (holdsCtx_cons (M.refl w) hΓ hRight)
  | bottomElim p ih =>
      intro M w hΓ
      exact False.elim (ih hΓ)

end PropositionalND

namespace Countermodels

inductive TwoWorld where
  | root
  | future
deriving DecidableEq, Repr

open TwoWorld

def twoLe : TwoWorld → TwoWorld → Prop
  | .root, _ => True
  | .future, .future => True
  | .future, .root => False

def twoFrame : Kripke.Frame where
  World := TwoWorld
  le := twoLe
  refl := by
    intro w
    cases w <;> trivial
  trans := by
    intro u v w huv hvw
    cases u <;> cases v <;> cases w <;> trivial

def emVal (name : String) : TwoWorld → Prop
  | .root => False
  | .future => name = "p"

theorem emValMono :
    ∀ {p : String} {w v : TwoWorld}, twoLe w v → emVal p w → emVal p v := by
  intro p w v h
  cases w <;> cases v <;> intro hv <;> trivial

def emModel : Kripke.Model where
  toFrame := twoFrame
  val := emVal
  mono := emValMono

def p : PropositionalND.Formula := PropositionalND.atom "p"

def excludedMiddle : PropositionalND.Formula :=
  PropositionalND.or p (PropositionalND.imp p PropositionalND.bot)

theorem root_not_forces_p :
    ¬ Kripke.Forces emModel .root p.1 := by
  intro hp
  exact hp

theorem root_not_forces_not_p :
    ¬ Kripke.Forces emModel .root (PropositionalND.imp p PropositionalND.bot).1 := by
  intro hnp
  have hpFuture : Kripke.Forces emModel .future p.1 := by
    show emVal "p" .future
    rfl
  have hbot : Kripke.Forces emModel .future PropositionalND.bot.1 := hnp .future trivial hpFuture
  exact hbot

theorem root_refutes_excluded_middle :
    ¬ Kripke.Forces emModel .root excludedMiddle.1 := by
  intro hem
  cases hem with
  | inl hp => exact root_not_forces_p hp
  | inr hnp => exact root_not_forces_not_p hnp

theorem excluded_middle_not_provable :
    ¬ PropositionalND.Theorem excludedMiddle := by
  intro hp
  rcases hp with ⟨p⟩
  have hforces := PropositionalND.sound p (M := emModel) (w := .root) (by
    intro v hv A hA
    cases hA)
  exact root_refutes_excluded_middle hforces

end Countermodels

end FastProofTheory.Logic.IPC
