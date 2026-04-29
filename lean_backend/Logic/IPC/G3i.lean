import Logic.IPC.Syntax

namespace Logic.IPC

inductive Derivation : Context -> Formula -> Type where
  | init {Γ : Context} {A : Formula} :
      A ∈ Γ →
      Derivation Γ A
  | botLeft {Γ : Context} {A : Formula} :
      Formula.bot ∈ Γ →
      Derivation Γ A
  | exchange {Γ₁ Γ₂ : Context} {A B C : Formula} :
      Derivation (Γ₁ ++ A :: B :: Γ₂) C →
      Derivation (Γ₁ ++ B :: A :: Γ₂) C
  | impRight {Γ : Context} {A B : Formula} :
      Derivation (A :: Γ) B →
      Derivation Γ (Formula.imp A B)
  | impLeft {Γ : Context} {A B C : Formula} :
      Derivation Γ A →
      Derivation (B :: Γ) C →
      Derivation (Formula.imp A B :: Γ) C
  | andRight {Γ : Context} {A B : Formula} :
      Derivation Γ A →
      Derivation Γ B →
      Derivation Γ (Formula.and A B)
  | andLeft {Γ : Context} {A B C : Formula} :
      Derivation (A :: B :: Γ) C →
      Derivation (Formula.and A B :: Γ) C
  | orRightLeft {Γ : Context} {A B : Formula} :
      Derivation Γ A →
      Derivation Γ (Formula.or A B)
  | orRightRight {Γ : Context} {A B : Formula} :
      Derivation Γ B →
      Derivation Γ (Formula.or A B)
  | orLeft {Γ : Context} {A B C : Formula} :
      Derivation (A :: Γ) C →
      Derivation (B :: Γ) C →
      Derivation (Formula.or A B :: Γ) C

end Logic.IPC
