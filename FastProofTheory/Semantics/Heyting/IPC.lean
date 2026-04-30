import FastProofTheory.IPC.Language

namespace FastProofTheory.IPC.Heyting

open FastProofTheory.IPC

universe u

structure Algebra where
  Carrier : Type u
  top : Carrier
  bot : Carrier
  inf : Carrier → Carrier → Carrier
  sup : Carrier → Carrier → Carrier
  imp : Carrier → Carrier → Carrier

abbrev Valuation (α : Type) (H : Algebra) := α → H.Carrier
abbrev Formula := FastProofTheory.IPC.Formula

def Eval {α : Type} (H : Algebra) (v : Valuation α H) : Formula α → H.Carrier
  | .atom p => v p
  | .bot => H.bot
  | .and a b => H.inf (Eval H v a) (Eval H v b)
  | .or a b => H.sup (Eval H v a) (Eval H v b)
  | .imp a b => H.imp (Eval H v a) (Eval H v b)

def Satisfies {α : Type} (H : Algebra) (v : Valuation α H) (A : FastProofTheory.IPC.WellFormed α fragment) : Prop :=
  Eval H v A.1 = H.top

def Valid {α : Type} (H : Algebra) (A : FastProofTheory.IPC.WellFormed α fragment) : Prop :=
  ∀ v, Satisfies H v A

def Entails {α : Type} (H : Algebra) (Γ : List (FastProofTheory.IPC.WellFormed α fragment)) (A : FastProofTheory.IPC.WellFormed α fragment) : Prop :=
  ∀ v, (∀ B ∈ Γ, Satisfies H v B) → Satisfies H v A

def TheoryValid {α : Type} (Hs : List Algebra) (A : FastProofTheory.IPC.WellFormed α fragment) : Prop :=
  ∀ H ∈ Hs, Valid H A

end FastProofTheory.IPC.Heyting
