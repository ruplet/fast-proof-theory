import FastProofTheory.ProofTheory.Sequent.IPC.LJ
import Lean.Elab.Tactic

open Lean PrettyPrinter Delaborator SubExpr Elab Tactic
open Rules

namespace LJ

syntax:max term " ⊢ᴸᴶ " term : term
syntax:max term " ⊢ᴸᴶ " "∅" : term

macro:max Γ:term " ⊢ᴸᴶ " A:term : term => `(LJ.Sequent $Γ (.some $A))
macro:max Γ:term " ⊢ᴸᴶ " "∅" : term => `(LJ.Sequent $Γ none)

@[app_unexpander LJ.Sequent] def unexpandSequent : Unexpander
| `($_ $Γ (Option.some $A)) => `($Γ ⊢ᴸᴶ $A)
| `($_ $Γ Option.none) => `($Γ ⊢ᴸᴶ ∅)
| _ => throw ()

syntax "axiom" : tactic
syntax "andLeft1" : tactic
syntax "andLeft2" : tactic
syntax "orLeft" : tactic
syntax "impRight" : tactic
syntax "negLeft" : tactic
syntax "negRight" : tactic
syntax "botLeft" : tactic
syntax "leftWeakening" : tactic
syntax "leftContraction" : tactic
syntax "leftPermutation" "(" term ", " term ")" : tactic
syntax "impLeft" "(" term ", " term ")" : tactic
syntax "forallLeft" term : tactic
syntax "forallRight" term : tactic
syntax "existsLeft" term : tactic
syntax "existsRight" term : tactic
syntax "cut" term : tactic

macro "axiom" : tactic => `(tactic| exact IntuitionisticSequentProof.axiom)
macro "andLeft1" : tactic => `(tactic| apply IntuitionisticSequentProof.andLeft₁)
macro "andLeft2" : tactic => `(tactic| apply IntuitionisticSequentProof.andLeft₂)
macro "orLeft" : tactic => `(tactic| apply IntuitionisticSequentProof.orLeft)
macro "impRight" : tactic => `(tactic| apply IntuitionisticSequentProof.impRight)
macro "negLeft" : tactic => `(tactic| apply IntuitionisticSequentProof.negLeft)
macro "negRight" : tactic => `(tactic| apply IntuitionisticSequentProof.negRight)
macro "botLeft" : tactic => `(tactic| apply IntuitionisticSequentProof.botLeft)
macro "leftWeakening" : tactic => `(tactic| apply IntuitionisticSequentProof.leftWeakening)
macro "leftContraction" : tactic => `(tactic| apply IntuitionisticSequentProof.leftContraction)
macro "leftPermutation" "(" Γ₁:term ", " Γ₂:term ")" : tactic =>
  `(tactic| apply IntuitionisticSequentProof.leftPermutation (Γ₁ := $Γ₁) (Γ₂ := $Γ₂))
macro "impLeft" "(" Γ:term ", " Γ':term ")" : tactic =>
  `(tactic| apply IntuitionisticSequentProof.impLeft (Γ := $Γ) (Γ' := $Γ'))
macro "forallLeft" t:term : tactic =>
  `(tactic| apply IntuitionisticSequentProof.forallLeft (t := $t))
macro "forallRight" y:term : tactic =>
  `(tactic| apply IntuitionisticSequentProof.forallRight (y := $y))
macro "existsLeft" y:term : tactic =>
  `(tactic| apply IntuitionisticSequentProof.existsLeft (y := $y))
macro "existsRight" t:term : tactic =>
  `(tactic| apply IntuitionisticSequentProof.existsRight (t := $t))
macro "cut" A:term : tactic =>
  `(tactic| apply IntuitionisticSequentProof.cut (A := $A))

def tacticStyleAndExample {A B : Formula} : [Formula.and A B] ⊢ᴸᴶ A := by
  andLeft1
  axiom

def tacticStyleImpExample {A B : Formula} : [A ⟶ B, A] ⊢ᴸᴶ B := by
  impLeft([A], [])
  · axiom
  · axiom

end LJ
