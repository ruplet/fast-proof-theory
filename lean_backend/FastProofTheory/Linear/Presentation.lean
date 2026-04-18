import FastProofTheory.Linear.Engine
import FastProofTheory.Server.Protocol

namespace FastProofTheory.Linear

open FastProofTheory.Server

private def splitHypothesis (hyp : String) : GoalHypothesis :=
  match hyp.splitOn " : " with
  | [] => { name := hyp, type := "" }
  | [name] => { name := name, type := "" }
  | name :: rest => { name := name, type := String.intercalate " : " rest }

def renderGoals (state : EngineState) : List GoalView :=
  state.goals.map fun goal =>
    {
      id := goal.id
      hypotheses := goal.hypotheses.map splitHypothesis
      target := goal.target
    }

def renderDisplay (snapshot : Snapshot) (state : EngineState) : ProofDisplay :=
  match snapshot.theorem? with
  | none =>
      {
        title := ""
        status := ""
        sections := []
      }
  | some thm =>
      let profileLabel := thm.profile?.map (·.displayName) |>.getD thm.profileText
      let calculusLabel := thm.profile?.map (·.calculusName) |>.getD "Natural Deduction"
      {
        title := thm.name
        status := state.status
        sections := [
          { title := "Profile", body := [profileLabel] },
          { title := "Calculus", body := [calculusLabel] },
          { title := "Goals", body := if state.goals.isEmpty then ["No open goals."] else state.goals.map (·.target) }
        ]
      }

end FastProofTheory.Linear
