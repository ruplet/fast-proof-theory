import FastProofTheory.ProofSystems.Rules

namespace FastProofTheory.ProofSystems.LinearSequentUrzyczyn

open Rules

abbrev Antecedent := List Formula
abbrev Succedent := List Formula

def AllBang : Antecedent -> Prop
  | [] => True
  | .bang _ :: rest => AllBang rest
  | _ => False

def AllWhyNot : Succedent -> Prop
  | [] => True
  | .whyNot _ :: rest => AllWhyNot rest
  | _ => False

inductive Proof : Antecedent -> Succedent -> Type where
  | axiom {Γ Δ : Antecedent} {A : Formula} :
      Proof (A :: Γ) (A :: Δ)

  | exchangeL {Γ₁ Γ₂ : Antecedent} {Δ : Succedent} {A B : Formula} :
      Proof (Γ₁ ++ A :: B :: Γ₂) Δ ->
      Proof (Γ₁ ++ B :: A :: Γ₂) Δ

  | exchangeR {Γ : Antecedent} {Δ₁ Δ₂ : Succedent} {A B : Formula} :
      Proof Γ (Δ₁ ++ A :: B :: Δ₂) ->
      Proof Γ (Δ₁ ++ B :: A :: Δ₂)

  | cut {Γ Γ' : Antecedent} {Δ Δ' : Succedent} {A : Formula} :
      Proof Γ (A :: Δ) ->
      Proof (A :: Γ') Δ' ->
      Proof (Γ ++ Γ') (Δ ++ Δ')

  | withL₁ {Γ : Antecedent} {Δ : Succedent} {A B : Formula} :
      Proof (A :: Γ) Δ ->
      Proof ((A & B) :: Γ) Δ

  | withL₂ {Γ : Antecedent} {Δ : Succedent} {A B : Formula} :
      Proof (B :: Γ) Δ ->
      Proof ((A & B) :: Γ) Δ

  | tensorL {Γ : Antecedent} {Δ : Succedent} {A B : Formula} :
      Proof (A :: B :: Γ) Δ ->
      Proof ((A ⊗ B) :: Γ) Δ

  | plusL {Γ : Antecedent} {Δ : Succedent} {A B : Formula} :
      Proof (A :: Γ) Δ ->
      Proof (B :: Γ) Δ ->
      Proof ((A ⊕ B) :: Γ) Δ

  | parL {Γ Γ' : Antecedent} {Δ Δ' : Succedent} {A B : Formula} :
      Proof Γ (A :: Δ) ->
      Proof (B :: Γ') Δ' ->
      Proof ((A ⅋ B) :: (Γ ++ Γ')) (Δ ++ Δ')

  | lolliL {Γ Γ' : Antecedent} {Δ Δ' : Succedent} {A B : Formula} :
      Proof Γ (A :: Δ) ->
      Proof (B :: Γ') Δ' ->
      Proof ((A ⊸ B) :: (Γ ++ Γ')) (Δ ++ Δ')

  | negL {Γ : Antecedent} {Δ : Succedent} {A : Formula} :
      Proof Γ (A :: Δ) ->
      Proof ((neg A) :: Γ) Δ

  | oneL {Γ : Antecedent} {Δ : Succedent} :
      Proof Γ Δ ->
      Proof (Formula.one :: Γ) Δ

  | zeroL {Γ : Antecedent} {Δ : Succedent} :
      Proof (Formula.zero :: Γ) Δ

  | bottomL {Γ : Antecedent} {Δ : Succedent} :
      Proof (Formula.bottom :: Γ) Δ

  | ofCourseL {Γ : Antecedent} {Δ : Succedent} {A : Formula} :
      Proof (A :: Γ) Δ ->
      Proof ((Formula.bang A) :: Γ) Δ

  | whyNotL {Γ : Antecedent} {Δ : Succedent} {A : Formula} :
      AllBang Γ ->
      AllWhyNot Δ ->
      Proof (A :: Γ) Δ ->
      Proof ((Formula.whyNot A) :: Γ) Δ

  | withR {Γ : Antecedent} {Δ : Succedent} {A B : Formula} :
      Proof Γ (A :: Δ) ->
      Proof Γ (B :: Δ) ->
      Proof Γ ((A & B) :: Δ)

  | tensorR {Γ Γ' : Antecedent} {Δ Δ' : Succedent} {A B : Formula} :
      Proof Γ (A :: Δ) ->
      Proof Γ' (B :: Δ') ->
      Proof (Γ ++ Γ') ((A ⊗ B) :: (Δ ++ Δ'))

  | plusR₁ {Γ : Antecedent} {Δ : Succedent} {A B : Formula} :
      Proof Γ (A :: Δ) ->
      Proof Γ ((A ⊕ B) :: Δ)

  | plusR₂ {Γ : Antecedent} {Δ : Succedent} {A B : Formula} :
      Proof Γ (B :: Δ) ->
      Proof Γ ((A ⊕ B) :: Δ)

  | parR {Γ : Antecedent} {Δ : Succedent} {A B : Formula} :
      Proof Γ (A :: B :: Δ) ->
      Proof Γ ((A ⅋ B) :: Δ)

  | lolliR {Γ : Antecedent} {Δ : Succedent} {A B : Formula} :
      Proof (A :: Γ) (B :: Δ) ->
      Proof Γ ((A ⊸ B) :: Δ)

  | negR {Γ : Antecedent} {Δ : Succedent} {A : Formula} :
      Proof (A :: Γ) Δ ->
      Proof Γ ((neg A) :: Δ)

  | oneR :
      Proof [] [Formula.one]

  | bottomR {Γ : Antecedent} {Δ : Succedent} :
      Proof Γ Δ ->
      Proof Γ (Formula.bottom :: Δ)

  | topR {Γ : Antecedent} {Δ : Succedent} :
      Proof Γ (Formula.top :: Δ)

  | ofCourseR {Γ : Antecedent} {Δ : Succedent} {A : Formula} :
      AllBang Γ ->
      AllWhyNot Δ ->
      Proof Γ (A :: Δ) ->
      Proof Γ ((Formula.bang A) :: Δ)

  | whyNotR {Γ : Antecedent} {Δ : Succedent} {A : Formula} :
      Proof Γ (A :: Δ) ->
      Proof Γ ((Formula.whyNot A) :: Δ)

  | weakenBang {Γ : Antecedent} {Δ : Succedent} {A : Formula} :
      Proof Γ Δ ->
      Proof ((Formula.bang A) :: Γ) Δ

  | weakenWhyNot {Γ : Antecedent} {Δ : Succedent} {A : Formula} :
      Proof Γ Δ ->
      Proof Γ ((Formula.whyNot A) :: Δ)

  | contractBang {Γ : Antecedent} {Δ : Succedent} {A : Formula} :
      Proof ((Formula.bang A) :: (Formula.bang A) :: Γ) Δ ->
      Proof ((Formula.bang A) :: Γ) Δ

  | contractWhyNot {Γ : Antecedent} {Δ : Succedent} {A : Formula} :
      Proof Γ ((Formula.whyNot A) :: (Formula.whyNot A) :: Δ) ->
      Proof Γ ((Formula.whyNot A) :: Δ)

end FastProofTheory.ProofSystems.LinearSequentUrzyczyn
