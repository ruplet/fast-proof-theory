import FastProofTheory.ProofTheory.Sequent.Linear.Engine
import FastProofTheory.ProofTheory.Sequent.Linear.Kernel

namespace FastProofTheory.Linear.Tactics

open FastProofTheory.Linear

structure TacticResult where
  goalId : String
  certificate : Certificate
  summary : String

structure ProofSearchTactic where
  name : String
  run : Snapshot -> EngineGoal -> Except String TacticResult

end FastProofTheory.Linear.Tactics
