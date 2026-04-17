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

def tensorPlusDistrib {A B C : Formula} :
    Equivalent (A ⊗ (B ⊕ C)) ((A ⊗ B) ⊕ (A ⊗ C)) := by
  apply LinearNDProof.withIntro
  · apply LinearNDProof.linearImpIntro
    exact tensorCases LinearNDProof.hyp <|
      swap <|
        plusCasesWith LinearNDProof.hyp
          (swap <| LinearNDProof.plusLeft <|
            LinearNDProof.tensorIntro LinearNDProof.hyp LinearNDProof.hyp)
          (swap <| LinearNDProof.plusRight <|
            LinearNDProof.tensorIntro LinearNDProof.hyp LinearNDProof.hyp)
  · apply LinearNDProof.linearImpIntro
    exact plusCases LinearNDProof.hyp
      (tensorCases LinearNDProof.hyp <|
        LinearNDProof.tensorIntro LinearNDProof.hyp (LinearNDProof.plusLeft LinearNDProof.hyp))
      (tensorCases LinearNDProof.hyp <|
        LinearNDProof.tensorIntro LinearNDProof.hyp (LinearNDProof.plusRight LinearNDProof.hyp))

def plusTensorDistrib {A B C : Formula} :
    Equivalent ((A ⊕ B) ⊗ C) ((A ⊗ C) ⊕ (B ⊗ C)) := by
  apply LinearNDProof.withIntro
  · apply LinearNDProof.linearImpIntro
    exact tensorCases LinearNDProof.hyp <|
      plusCasesWith LinearNDProof.hyp
        (LinearNDProof.plusLeft <| LinearNDProof.tensorIntro LinearNDProof.hyp LinearNDProof.hyp)
        (LinearNDProof.plusRight <| LinearNDProof.tensorIntro LinearNDProof.hyp LinearNDProof.hyp)
  · apply LinearNDProof.linearImpIntro
    exact plusCases LinearNDProof.hyp
      (tensorCases LinearNDProof.hyp <|
        LinearNDProof.tensorIntro (LinearNDProof.plusLeft LinearNDProof.hyp) LinearNDProof.hyp)
      (tensorCases LinearNDProof.hyp <|
        LinearNDProof.tensorIntro (LinearNDProof.plusRight LinearNDProof.hyp) LinearNDProof.hyp)

def linearImpWithDistrib {A B C : Formula} :
    Equivalent (A ⊸ (B & C)) ((A ⊸ B) & (A ⊸ C)) := by
  apply LinearNDProof.withIntro
  · apply LinearNDProof.linearImpIntro
    apply LinearNDProof.withIntro
    · apply LinearNDProof.linearImpIntro
      exact swap <| LinearNDProof.withLeft <|
        LinearNDProof.linearImpElim LinearNDProof.hyp LinearNDProof.hyp
    · apply LinearNDProof.linearImpIntro
      exact swap <| LinearNDProof.withRight <|
        LinearNDProof.linearImpElim LinearNDProof.hyp LinearNDProof.hyp
  · apply LinearNDProof.linearImpIntro
    apply LinearNDProof.linearImpIntro
    apply LinearNDProof.withIntro
    · exact swap <| LinearNDProof.linearImpElim
        (LinearNDProof.withLeft LinearNDProof.hyp) LinearNDProof.hyp
    · exact swap <| LinearNDProof.linearImpElim
        (LinearNDProof.withRight LinearNDProof.hyp) LinearNDProof.hyp

def plusLinearImpDistrib {A B C : Formula} :
    Equivalent ((A ⊕ B) ⊸ C) ((A ⊸ C) & (B ⊸ C)) := by
  apply LinearNDProof.withIntro
  · apply LinearNDProof.linearImpIntro
    apply LinearNDProof.withIntro
    · apply LinearNDProof.linearImpIntro
      exact swap <| LinearNDProof.linearImpElim
        LinearNDProof.hyp (LinearNDProof.plusLeft LinearNDProof.hyp)
    · apply LinearNDProof.linearImpIntro
      exact swap <| LinearNDProof.linearImpElim
        LinearNDProof.hyp (LinearNDProof.plusRight LinearNDProof.hyp)
  · apply LinearNDProof.linearImpIntro
    apply LinearNDProof.linearImpIntro
    exact plusCasesWith LinearNDProof.hyp
      (swap <| LinearNDProof.linearImpElim
        (LinearNDProof.withLeft LinearNDProof.hyp) LinearNDProof.hyp)
      (swap <| LinearNDProof.linearImpElim
        (LinearNDProof.withRight LinearNDProof.hyp) LinearNDProof.hyp)

def bangWithDistrib {A B : Formula} :
    Equivalent (.bang (A & B)) (.bang A ⊗ .bang B) := by
  apply LinearNDProof.withIntro
  · apply LinearNDProof.linearImpIntro
    exact useBang LinearNDProof.hyp <|
      LinearNDProof.tensorIntro
        (LinearNDProof.bangIntro <| LinearNDProof.withLeft <|
          LinearNDProof.unrestricted (A := A & B) (by simp))
        (LinearNDProof.bangIntro <| LinearNDProof.withRight <|
          LinearNDProof.unrestricted (A := A & B) (by simp))
  · apply LinearNDProof.linearImpIntro
    exact tensorCases LinearNDProof.hyp <|
      useBangWith LinearNDProof.hyp <|
        useBang LinearNDProof.hyp <|
          LinearNDProof.bangIntro <|
            LinearNDProof.withIntro
              (LinearNDProof.unrestricted (A := A) (by simp))
              (LinearNDProof.unrestricted (A := B) (by simp))

end Linear
