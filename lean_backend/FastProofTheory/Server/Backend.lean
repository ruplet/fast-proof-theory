import FastProofTheory.Server.Protocol
import FastProofTheory.Server.Domain
import FastProofTheory.Linear.Engine
import FastProofTheory.Linear.Presentation

namespace FastProofTheory.Server

export FastProofTheory.Server.Domain (domainInfo)

private def trimLine (line : String) : String :=
  FastProofTheory.Linear.trimLine line

private def lineAt? (lines : List String) (idx : Nat) : Option String :=
  match lines, idx with
  | [], _ => none
  | line :: _, 0 => some line
  | _ :: rest, idx + 1 => lineAt? rest idx

private def helpDirectiveAtCursor? (text : String) (cursorLine : Nat) : Option String :=
  match lineAt? (text.splitOn "\n") cursorLine with
  | some line =>
      let trimmed := trimLine line
      if trimmed.startsWith "#help " then
        some (trimLine (String.ofList (trimmed.toList.drop 6)))
      else
        none
  | none => none

private def dedupeErrors (errors : List FastProofTheory.Linear.EngineError) :
    List FastProofTheory.Linear.EngineError :=
  let rec loop
      (remaining : List FastProofTheory.Linear.EngineError)
      (seen : List (Nat × Nat × String × String))
      (acc : List FastProofTheory.Linear.EngineError) :=
    match remaining with
    | [] => acc.reverse
    | err :: rest =>
        let key := (err.line, err.severity, err.code, err.message)
        if seen.contains key then
          loop rest seen acc
        else
          loop rest (key :: seen) (err :: acc)
  loop errors [] []

def checkDocument (params : CheckDocumentParams) : CheckDocumentResult :=
  let cursorLine := params.cursor.map (·.line) |>.getD 0
  match helpDirectiveAtCursor? params.text cursorLine with
  | some name =>
      {
        diagnostics := []
        goals := []
        display := FastProofTheory.Server.Domain.systemHelpDisplay name
        theoremStatuses := []
      }
  | none =>
  let cursorCharacter := params.cursor.map (·.character) |>.getD 0
  let parsed := FastProofTheory.Linear.parseDocument params.text
  let snapshot := FastProofTheory.Linear.snapshotAtCursor params.text cursorLine cursorCharacter
  let state := FastProofTheory.Linear.evaluate snapshot
  let theoremDiagnostics :=
    match params.cursor with
    | some _ => []
    | none => FastProofTheory.Linear.diagnosticsForTheorems parsed.theorems
  let theoremStatuses := FastProofTheory.Linear.theoremStatusesForTheorems parsed.theorems
  let cursorDiagnostics :=
    match params.cursor with
    | some _ => FastProofTheory.Linear.diagnosticsForSnapshot snapshot
    | none => []
  let parseDiagnostics :=
    match params.cursor with
    | some _ => parsed.errors.filter (fun err => err.line ≤ cursorLine)
    | none => parsed.errors
  let diagnostics :=
    dedupeErrors (parseDiagnostics ++ theoremDiagnostics ++ cursorDiagnostics) |>.map fun err =>
      mkDiagnostic err.line 0 1 err.severity err.code "lean-backend" err.message
  {
    diagnostics
    goals := FastProofTheory.Linear.renderGoals state
    display := FastProofTheory.Linear.renderDisplay snapshot state
    theoremStatuses := theoremStatuses.map fun thm =>
      { name := thm.name, line := thm.line, verified := thm.verified }
  }

end FastProofTheory.Server
