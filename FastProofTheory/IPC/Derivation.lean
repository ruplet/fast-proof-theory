import FastProofTheory.IPC.Syntax

namespace FastProofTheory.IPC

/--
Single-succedent sequent derivations for intuitionistic propositional logic.

This is the propositional fragment of the calculus usually called G3i/G3ip
in the proof-theory literature: weakening, contraction, and cut are intended
to be admissible meta-theorems rather than primitive rules.
-/
inductive Derivation : Context α -> Formula α -> Type where
  | init {Γ : Context α} {A : Formula α} :
      A ∈ Γ →
      Derivation Γ A
  | botLeft {Γ : Context α} {A : Formula α} :
        -- TODO: don't use ∈ in rules. use exchange rule and add weaken and contraction explicitly. fix all the proofs we have to account for that
        -- then prove a theorem, and add a tactic, that performs the automation - if formula α ∈ Context α, then we can generate the appropriat enumber of xchg / weaken etc. rules to simulate begin ∈
      .bot ∈ Γ →
      Derivation Γ A
  | exchange {Γ₁ Γ₂ : Context α} {A B C : Formula α} :
      Derivation (Γ₁ ++ A :: B :: Γ₂) C →
      Derivation (Γ₁ ++ B :: A :: Γ₂) C
  | impRight {Γ : Context α} {A B : Formula α} :
      Derivation (A :: Γ) B →
      Derivation Γ (.imp A B)
  | impLeft {Γ : Context α} {A B C : Formula α} :
        -- here i think that (.imp A B) should be in context α on the left
      Derivation Γ A →
      Derivation (B :: Γ) C →
      Derivation (.imp A B :: Γ) C
  | andRight {Γ : Context α} {A B : Formula α} :
      Derivation Γ A →
      Derivation Γ B →
      Derivation Γ (.and A B)
  | andLeft {Γ : Context α} {A B C : Formula α} :
      Derivation (A :: B :: Γ) C →
      Derivation (.and A B :: Γ) C
  | orRightLeft {Γ : Context α} {A B : Formula α} :
      Derivation Γ A →
      Derivation Γ (.or A B)
  | orRightRight {Γ : Context α} {A B : Formula α} :
      Derivation Γ B →
      Derivation Γ (.or A B)
  | orLeft {Γ : Context α} {A B C : Formula α} :
      Derivation (A :: Γ) C →
      Derivation (B :: Γ) C →
      Derivation (.or A B :: Γ) C

end FastProofTheory.IPC
