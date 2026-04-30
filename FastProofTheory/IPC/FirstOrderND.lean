import FastProofTheory.Rules

namespace FastProofTheory.IPC.FirstOrderND

open Rules

abbrev Formula := Rules.Formula
abbrev Context := List Formula

inductive Derivation : Context → Formula → Type where
  | hyp : A ∈ Γ → Derivation Γ A
  | exchange :
      Derivation (Γ₁ ++ A :: B :: Γ₂) C →
      Derivation (Γ₁ ++ B :: A :: Γ₂) C
  | weaken :
      Derivation Γ A →
      Derivation (B :: Γ) A
  | contract :
      Derivation (A :: A :: Γ) B →
      Derivation (A :: Γ) B
  | impIntro :
      Derivation (A :: Γ) B →
      Derivation Γ (.imp A B)
  | impElim :
      Derivation Γ (.imp A B) →
      Derivation Γ A →
      Derivation Γ B
  | andIntro :
      Derivation Γ A →
      Derivation Γ B →
      Derivation Γ (.and A B)
  | andLeft :
      Derivation Γ (.and A B) →
      Derivation Γ A
  | andRight :
      Derivation Γ (.and A B) →
      Derivation Γ B
  | orLeft :
      Derivation Γ A →
      Derivation Γ (.or A B)
  | orRight :
      Derivation Γ B →
      Derivation Γ (.or A B)
  | orElim :
      Derivation Γ (.or A B) →
      Derivation (A :: Γ) C →
      Derivation (B :: Γ) C →
      Derivation Γ C
  | bottomElim :
      Derivation Γ .bot →
      Derivation Γ A
  | forallIntro :
      Derivation Γ A →
      Derivation Γ (.all x A)
  | forallElim :
      Derivation Γ (.all x A) →
      Derivation Γ (substFormula x t A)
  | existsIntro :
      Derivation Γ (substFormula x t A) →
      Derivation Γ (.ex x A)
  | existsElim :
      Derivation Γ (.ex x A) →
      Derivation ((substFormula x (.var y) A) :: Γ) B →
      Derivation Γ B

abbrev Theorem (A : Formula) : Prop := Nonempty (Derivation [] A)

end FastProofTheory.IPC.FirstOrderND
