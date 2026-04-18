import Lean4TPIL.Rules

namespace Linear

open Rules

inductive System where

instance : HasUnrestrictedExchange System := ⟨⟩
instance : HasUnrestrictedWeakening System := ⟨⟩
instance : HasUnrestrictedContraction System := ⟨⟩
instance : HasLinearExchange System := ⟨⟩

abbrev Proof := LinearNDProof System
abbrev Theorem (A : Formula) : Type := Proof [] [] A
abbrev Equivalent (A B : Formula) : Type := Theorem ((A ⊸ B) & (B ⊸ A))

def swap {Δ : Unrestricted} {A B C : Formula} :
    Proof Δ [A, B] C -> Proof Δ [B, A] C := by
  intro p
  simpa using (LinearNDProof.lExchange (Γ₁ := []) (Γ₂ := []) p)

def tensorCases {Δ : Unrestricted} {X A B C : Formula} :
    Proof Δ [X] (A ⊗ B) -> Proof Δ [A, B] C -> Proof Δ [X] C := by
  intro p q
  simpa using (LinearNDProof.tensorElim (Γ₁ := [X]) (Γ₂ := []) p q)

def plusCases {Δ : Unrestricted} {X A B C : Formula} :
    Proof Δ [X] (A ⊕ B) -> Proof Δ [A] C -> Proof Δ [B] C -> Proof Δ [X] C := by
  intro p qA qB
  simpa using (LinearNDProof.plusElim (Γ₁ := [X]) (Γ₂ := []) p qA qB)

def plusCasesWith {Δ : Unrestricted} {X K A B C : Formula} :
    Proof Δ [X] (A ⊕ B) -> Proof Δ [A, K] C -> Proof Δ [B, K] C -> Proof Δ [X, K] C := by
  intro p qA qB
  simpa using (LinearNDProof.plusElim (Γ₁ := [X]) (Γ₂ := [K]) p qA qB)

def useBang {Δ : Unrestricted} {X A B : Formula} :
    Proof Δ [X] (.bang A) -> Proof (A :: Δ) [] B -> Proof Δ [X] B := by
  intro p q
  simpa using (LinearNDProof.bangElim (Γ₁ := [X]) (Γ₂ := []) p q)

def useBangWith {Δ : Unrestricted} {X K A B : Formula} :
    Proof Δ [X] (.bang A) -> Proof (A :: Δ) [K] B -> Proof Δ [X, K] B := by
  intro p q
  simpa using (LinearNDProof.bangElim (Γ₁ := [X]) (Γ₂ := [K]) p q)

-- Example proofs formerly kept here are now maintained in:
--   demo/linear_from_lean.mypa
-- This keeps the interactive MyPA proofs as the canonical versions.

end Linear
