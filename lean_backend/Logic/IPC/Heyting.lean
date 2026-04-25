import Logic.IPC.Language

namespace Logic.IPC.Heyting

open Rules
open Logic.IPC

universe u

structure Algebra where
  Carrier : Type u
  top : Carrier
  bot : Carrier
  inf : Carrier → Carrier → Carrier
  sup : Carrier → Carrier → Carrier
  imp : Carrier → Carrier → Carrier

abbrev Valuation (H : Algebra) := String → H.Carrier
abbrev Formula := Rules.Formula

def Eval (H : Algebra) (v : Valuation H) : Formula → H.Carrier
  | .atom p => v p
  | .bot => H.bot
  | .and a b => H.inf (Eval H v a) (Eval H v b)
  | .or a b => H.sup (Eval H v a) (Eval H v b)
  | .imp a b => H.imp (Eval H v a) (Eval H v b)
  | _ => H.bot

def Satisfies (H : Algebra) (v : Valuation H) (A : WellFormed fragment) : Prop :=
  Eval H v A.1 = H.top

def Valid (H : Algebra) (A : WellFormed fragment) : Prop :=
  ∀ v, Satisfies H v A

def Entails (H : Algebra) (Γ : List (WellFormed fragment)) (A : WellFormed fragment) : Prop :=
  ∀ v, (∀ B ∈ Γ, Satisfies H v B) → Satisfies H v A

def TheoryValid (Hs : List Algebra) (A : WellFormed fragment) : Prop :=
  ∀ H ∈ Hs, Valid H A

end Logic.IPC.Heyting
