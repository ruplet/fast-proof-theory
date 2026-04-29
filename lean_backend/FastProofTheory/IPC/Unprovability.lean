import FastProofTheory.IPC.RG3IED

namespace FastProofTheory.IPC

open Lean
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Meta
open Logic.IPC
open Logic.IPC.Countermodel

syntax (name := finishUnprovable) "finish_unprovable" : tactic
syntax (name := finishUnprovableUsing) "finish_unprovable_using " term : tactic

private def elaborateGeneratedTerm (src : String) (expectedType : Expr) : TacticM Expr := do
  let env ← getEnv
  let stx ←
    match Lean.Parser.runParserCategory env `term src with
    | Except.ok stx => pure stx
    | Except.error msg => throwError "failed to parse generated countermodel term:\n{msg}"
  Lean.Elab.Tactic.elabTerm stx (some expectedType)

elab_rules : tactic
  | `(tactic| finish_unprovable) => do
      let goal ← getMainGoal
      let goalTy ← Lean.instantiateMVars (← goal.getType)
      let formula ← Lean.Elab.Tactic.liftMetaMAtMain (fun _ => FastProofTheory.IPC.RG3IED.extractFormula goalTy)
      let name := s!"rg3ied_{String.hash (FastProofTheory.IPC.RG3IED.renderJtwFormula formula)}"
      let result ← liftM <| FastProofTheory.IPC.RG3IED.searchCountermodel name formula
      match result with
      | Except.error msg =>
          throwError "countermodel search failed:\n{msg}"
      | Except.ok model =>
          let termSrc := FastProofTheory.IPC.RG3IED.renderCountermodelTerm formula model
          let term ← elaborateGeneratedTerm termSrc goalTy
          closeMainGoal `finish_unprovable term

  | `(tactic| finish_unprovable_using $c:term) => do
      let cExpr ← Lean.Elab.Tactic.elabTerm c (some (mkConst ``Logic.IPC.Countermodel.Countermodel))
      let term := mkApp (mkConst ``Logic.IPC.Countermodel.countermodel_not_derivable) cExpr
      closeMainGoal `finish_unprovable_using term

namespace Demo

def p : Formula := .atom "p"

private def frame : FiniteFrame where
  n := 1
  le := fun _ _ => true
  refl := by intro w; decide
  trans := by intro u v w huv hvw; decide

private def model : FiniteModel where
  toFiniteFrame := frame
  val := fun _ _ => false
  mono := by
    intro p u v huv hv
    simp at hv

private def c : Countermodel where
  M := model
  root := ⟨0, by decide⟩
  formula := p
  refutes := by
    unfold Logic.IPC.Countermodel.eval
    simp [model, frame]
    intro h
    cases h

example : Not (Nonempty (Derivation [] p)) := by
  finish_unprovable_using c

end Demo

end FastProofTheory.IPC
