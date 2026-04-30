import FastProofTheory.ProofTheory.Sequent.Linear.Tactics.Interface

namespace FastProofTheory.Linear.Tactics

open FastProofTheory.Linear

def solveNp : ProofSearchTactic where
  name := "solve_np"
  run := fun _snapshot goal =>
    .error s!"solve_np is not implemented yet for {goal.id}. Hook the NP certificate search here."

end FastProofTheory.Linear.Tactics
