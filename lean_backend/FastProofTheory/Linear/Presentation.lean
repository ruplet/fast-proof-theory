import FastProofTheory.Linear.Engine
import FastProofTheory.Server.Protocol

namespace FastProofTheory.Linear

open FastProofTheory.Server

def renderGoals (state : EngineState) : List GoalView :=
  state.goals.map fun goal =>
    {
      id := goal.id
      hypotheses := goal.hypotheses.map fun hyp => { name := hyp, type := hyp }
      target := goal.target
    }

def renderDisplay (snapshot : Snapshot) (state : EngineState) : ProofDisplay :=
  match snapshot.theorem? with
  | none =>
      {
        title := "Lean Backend"
        status := state.status
        sections := [{ title := "Backend", body := ["Proof state is owned by the Lean backend."] }]
      }
  | some thm =>
      let calculusLabel :=
        if thm.profileText.toUpper.contains "GENTZEN" then
          "Sequent Calculus"
        else
          "Natural Deduction"
      {
        title := thm.name
        status := state.status
        sections := [
          { title := "Profile", body := [thm.profile?.map (·.displayName) |>.getD thm.profileText] },
          { title := "Calculus", body := [calculusLabel] },
          { title := "Goals", body := if state.goals.isEmpty then ["No open goals."] else state.goals.map (·.target) }
        ]
      }

end FastProofTheory.Linear
