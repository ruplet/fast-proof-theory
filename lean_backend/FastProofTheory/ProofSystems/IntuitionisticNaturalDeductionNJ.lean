import Logic.Rules

namespace NJ

open Rules

inductive System where

instance : HasExchange System := ⟨⟩
instance : HasWeakening System := ⟨⟩
instance : HasContraction System := ⟨⟩
instance : HasBottomElim System := ⟨⟩

abbrev Proof := NDProof System
abbrev Judgment (Γ : Context) (A : Formula) : Type := Proof Γ A
abbrev Theorem (A : Formula) : Type := Proof [] A

end NJ
