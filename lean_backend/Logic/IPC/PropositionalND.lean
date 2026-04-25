import Logic.IPC.Language

namespace Logic.IPC.PropositionalND

open Rules
open Logic.IPC

abbrev Formula := WellFormed .full
abbrev Context := List Formula

def atom (name : String) : Formula :=
  ⟨.atom name, trivial⟩

def bot : Formula :=
  ⟨.bot, trivial⟩

def imp (A B : Formula) : Formula :=
  ⟨.imp A.1 B.1, ⟨A.2, B.2⟩⟩

def and (A B : Formula) : Formula :=
  ⟨.and A.1 B.1, ⟨A.2, B.2⟩⟩

def or (A B : Formula) : Formula :=
  ⟨.or A.1 B.1, ⟨A.2, B.2⟩⟩

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

abbrev Theorem (A : Formula) : Prop := Nonempty (Derivation [] A)

end Logic.IPC.PropositionalND
