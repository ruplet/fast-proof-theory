import FastProofTheory.ProofSystems.Rules

namespace LJ

open Rules

inductive System where

instance : HasLeftWeakeningSC System := ⟨⟩
instance : HasLeftContractionSC System := ⟨⟩
instance : HasLeftPermutationSC System := ⟨⟩
instance : HasCutSC System := ⟨⟩

abbrev Proof := IntuitionisticSequentProof System
abbrev Sequent (Γ : Antecedent) (C : SingleSuccedent) : Type := Proof Γ C
abbrev Theorem (A : Formula) : Type := Sequent [] (.some A)

def identity {A : Formula} : Sequent [A] (.some A) :=
  IntuitionisticSequentProof.axiom

def modusPonensSequent {A B : Formula} : Sequent [A ⟶ B, A] (.some B) := by
  apply IntuitionisticSequentProof.impLeft (Γ := [A]) (Γ' := [])
  · exact IntuitionisticSequentProof.axiom
  · exact IntuitionisticSequentProof.axiom

def quantifierExample {x : String} {t : Term} :
    Sequent [Formula.all x (.pred "p" [Term.var x])]
      (.some (Formula.ex x (.pred "p" [Term.var x]))) := by
  apply IntuitionisticSequentProof.existsRight (t := t)
  apply IntuitionisticSequentProof.forallLeft (t := t)
  exact IntuitionisticSequentProof.axiom

def gentzenExample1 {A B : Formula} :
    Theorem ((Formula.and (neg A) (neg B)) ⟶ neg (A ∨ B)) := by
  apply IntuitionisticSequentProof.impRight
  apply IntuitionisticSequentProof.impRight
  apply IntuitionisticSequentProof.orLeft
  · apply IntuitionisticSequentProof.leftPermutation (Γ₁ := []) (Γ₂ := [])
    apply IntuitionisticSequentProof.andLeft₁
    apply IntuitionisticSequentProof.impLeft (Γ := [A]) (Γ' := [])
    · exact IntuitionisticSequentProof.axiom
    · exact IntuitionisticSequentProof.axiom
  · apply IntuitionisticSequentProof.leftPermutation (Γ₁ := []) (Γ₂ := [])
    apply IntuitionisticSequentProof.andLeft₂
    apply IntuitionisticSequentProof.impLeft (Γ := [B]) (Γ' := [])
    · exact IntuitionisticSequentProof.axiom
    · exact IntuitionisticSequentProof.axiom

def gentzenExample2Part1 {A : Formula} :
    Theorem (A ⟶ neg (neg A)) := by
  apply IntuitionisticSequentProof.impRight
  apply IntuitionisticSequentProof.impRight
  apply IntuitionisticSequentProof.impLeft (Γ := [A]) (Γ' := [])
  · exact IntuitionisticSequentProof.axiom
  · exact IntuitionisticSequentProof.axiom

def gentzenExample3 {A : Formula} :
    Theorem (neg (neg ((neg (neg A)) ⟶ A))) := by
  apply IntuitionisticSequentProof.impRight
  apply IntuitionisticSequentProof.leftContraction
  apply IntuitionisticSequentProof.impLeft (Γ := [(((neg (neg A)) ⟶ A) ⟶ ⊥)]) (Γ' := [])
  · apply IntuitionisticSequentProof.impRight
    apply IntuitionisticSequentProof.impLeft (Γ := [(((neg (neg A)) ⟶ A) ⟶ ⊥)]) (Γ' := [])
    · apply IntuitionisticSequentProof.impRight
      apply IntuitionisticSequentProof.leftPermutation (Γ₁ := []) (Γ₂ := [])
      apply IntuitionisticSequentProof.impLeft (Γ := [A]) (Γ' := [])
      · apply IntuitionisticSequentProof.impRight
        apply IntuitionisticSequentProof.leftPermutation (Γ₁ := []) (Γ₂ := [])
        exact IntuitionisticSequentProof.axiom
      · exact IntuitionisticSequentProof.axiom
    · apply IntuitionisticSequentProof.botLeft
  · exact IntuitionisticSequentProof.axiom

def gentzenNodeExample {A B : Formula} :
    Sequent [neg (neg A), Formula.and A B] (.some B) := by
  apply IntuitionisticSequentProof.leftPermutation (Γ₁ := []) (Γ₂ := [])
  apply IntuitionisticSequentProof.andLeft₂
  exact IntuitionisticSequentProof.axiom

end LJ
