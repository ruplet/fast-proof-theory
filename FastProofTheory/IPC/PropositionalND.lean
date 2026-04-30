import FastProofTheory.IPC.Language

namespace FastProofTheory.IPC.PropositionalND

open Rules
open FastProofTheory.IPC

abbrev Formula (α : Type) := FastProofTheory.IPC.WellFormed α .full
abbrev Context (α : Type) := List (Formula α)

def atom {α : Type} (name : α) : Formula α :=
  ⟨.atom name, trivial⟩

def bot {α : Type} : Formula α :=
  ⟨.bot, trivial⟩

def imp {α : Type} (A B : Formula α) : Formula α :=
  ⟨.imp A.1 B.1, ⟨A.2, B.2⟩⟩

def and {α : Type} (A B : Formula α) : Formula α :=
  ⟨.and A.1 B.1, ⟨A.2, B.2⟩⟩

def or {α : Type} (A B : Formula α) : Formula α :=
  ⟨.or A.1 B.1, ⟨A.2, B.2⟩⟩

inductive Derivation {α : Type} : Context α → Formula α → Type where
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
      Derivation Γ (imp A B)
  | impElim :
      Derivation Γ (imp A B) →
      Derivation Γ A →
      Derivation Γ B
  | andIntro :
      Derivation Γ A →
      Derivation Γ B →
      Derivation Γ (and A B)
  | andLeft :
      Derivation Γ (and A B) →
      Derivation Γ A
  | andRight :
      Derivation Γ (and A B) →
      Derivation Γ B
  | orLeft :
      Derivation Γ A →
      Derivation Γ (or A B)
  | orRight :
      Derivation Γ B →
      Derivation Γ (or A B)
  | orElim :
      Derivation Γ (or A B) →
      Derivation (A :: Γ) C →
      Derivation (B :: Γ) C →
      Derivation Γ C
  | bottomElim :
      Derivation Γ bot →
      Derivation Γ A

abbrev Theorem {α : Type} (A : Formula α) : Prop := Nonempty (Derivation [] A)

end FastProofTheory.IPC.PropositionalND
