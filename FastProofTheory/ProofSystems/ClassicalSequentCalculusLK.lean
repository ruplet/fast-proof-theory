import Lean4TPIL.Rules

namespace LK

open Rules

inductive System where

instance : HasLeftWeakeningSC System := ⟨⟩
instance : HasRightWeakeningSC System := ⟨⟩
instance : HasLeftContractionSC System := ⟨⟩
instance : HasRightContractionSC System := ⟨⟩
instance : HasLeftPermutationSC System := ⟨⟩
instance : HasRightPermutationSC System := ⟨⟩
instance : HasCutSC System := ⟨⟩

abbrev Proof := SequentProof System
abbrev Sequent (Γ : Antecedent) (Δ : Succedent) : Type := Proof Γ Δ

def identity {A : Formula} : Sequent [A] [A] :=
  SequentProof.axiom

def weakeningExample {A B : Formula} : Sequent [A] [A, B] :=
  SequentProof.rightPermutation (Δ₁ := []) (Δ₂ := [])
    (SequentProof.rightWeakening (A := B) identity)

def modusPonensSequent {A B : Formula} : Sequent [A ⟶ B, A] [B] := by
  apply SequentProof.impLeft (Γ := [A]) (Γ' := []) (Δ := []) (Δ' := [B])
  · exact SequentProof.axiom
  · exact SequentProof.axiom

def excludedMiddleSequent {A : Formula} : Sequent [] [A, ¬A] := by
  apply SequentProof.rightPermutation (Δ₁ := []) (Δ₂ := [])
  apply SequentProof.impRight
  exact SequentProof.rightWeakening (A := ⊥) SequentProof.axiom

def quantifierExample {x : String} {t : Term} :
    Sequent [Formula.all x (.pred "p" [Term.var x])]
      [Formula.ex x (.pred "p" [Term.var x])] := by
  apply SequentProof.existsRight (t := t)
  apply SequentProof.forallLeft (t := t)
  exact SequentProof.axiom

end LK
