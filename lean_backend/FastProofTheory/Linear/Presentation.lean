import FastProofTheory.Linear.Engine
import FastProofTheory.Linear.Export
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
      let systemLabel := thm.declaredSystem?.map (·.displayName) |>.getD thm.systemText
      let languageLabel := thm.declaredSystem?.map (·.languageName) |>.getD ""
      let exportSection :=
        if state.verified then
          match Export.exportIPCTheorem? thm with
          | some source =>
              [{ title := "Lean Export", body := source.splitOn "\n" }]
          | none => []
        else
          []
      {
        title := thm.name
        status := state.status
        sections := [
          { title := "System", body := [systemLabel] },
          { title := "Language", body := [languageLabel] },
          { title := "Goals", body := if state.goals.isEmpty then ["No open goals."] else state.goals.map (·.target) }
        ] ++ exportSection
      }

end FastProofTheory.Linear
