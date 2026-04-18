import FastProofTheoryBackend
import Lean.Data.Json

open Lean
open FastProofTheory.Server

structure CachedProofState where
  goals : List GoalView
  display : ProofDisplay
  tone : Option String := none
deriving ToJson

structure CachedCursorState where
  line : Nat
  character : Nat
  kind : String
  state : CachedProofState
  diagnostics : List Diagnostic
  theoremStatuses : List TheoremStatus
deriving ToJson

structure CachedDocument where
  title : String
  source : String
  initialLine : Nat
  initialCharacter : Nat
  documentDiagnostics : List Diagnostic
  theoremStatuses : List TheoremStatus
  positions : List CachedCursorState
deriving ToJson

private def usage : String :=
  "usage: lake exe mypa-export-cache [--title <title>] <file.mypa>|-"

private def parseArgs : List String → Except String (String × String)
  | "--title" :: title :: path :: [] => pure (title, path)
  | path :: [] => pure ("MyPA Demo", path)
  | "--title" :: _ :: [] => .error s!"Missing input path.\n{usage}"
  | _ => .error usage

private def readInput (path : String) : IO String := do
  if path = "-" then
    (← IO.getStdin).readToEnd
  else
    IO.FS.readFile path

private def normalizeResult (result : CheckDocumentResult) (line character : Nat) : CachedCursorState :=
  if !result.goals.isEmpty then
    {
      line := line
      character := character
      kind := "ok"
      state := {
        goals := result.goals
        display := result.display
      }
      diagnostics := result.diagnostics
      theoremStatuses := result.theoremStatuses
    }
  else
    match result.diagnostics.head? with
    | some diag =>
        {
          line := line
          character := character
          kind := "error"
          state := {
            goals := []
            display := { result.display with status := diag.message }
            tone := some "error"
          }
          diagnostics := result.diagnostics
          theoremStatuses := result.theoremStatuses
        }
    | none =>
        {
          line := line
          character := character
          kind := "no_goals"
          state := {
            goals := []
            display := result.display
            tone := some "normal"
          }
          diagnostics := []
          theoremStatuses := result.theoremStatuses
        }

private def linePositions (fullText : String) (line : Nat) (lineText : String) : List CachedCursorState :=
  let charCount := lineText.length
  (List.range (charCount + 1)).map fun character =>
    normalizeResult
      (checkDocument {
        uri := "memory://myst/block"
        version := 1
        text := fullText
        cursor := some { line := line, character := character }
      })
      line
      character

private def allPositions (text : String) : List CachedCursorState :=
  let lines := text.splitOn "\n"
  let rec loop (remaining : List String) (line : Nat) : List CachedCursorState :=
    match remaining with
    | [] => []
    | lineText :: rest => linePositions text line lineText ++ loop rest (line + 1)
  loop lines 0

def main (args : List String) : IO UInt32 := do
  let (title, path) <- match parseArgs args with
    | .ok parsed => pure parsed
    | .error msg =>
        IO.eprintln msg
        return 2
  let source <- readInput path
  let documentResult := checkDocument {
    uri := if path = "-" then "stdin://mypa" else s!"file://{path}"
    version := 1
    text := source
  }
  let payload : CachedDocument := {
    title := title
    source := source
    initialLine := 0
    initialCharacter := 0
    documentDiagnostics := documentResult.diagnostics
    theoremStatuses := documentResult.theoremStatuses
    positions := allPositions source
  }
  IO.println (toJson payload).compress
  return 0
