import FastProofTheory.App.Backend

open FastProofTheory.Server

private def printDiagnostic (diag : Diagnostic) : IO Unit := do
  let line := diag.range.start.line + 1
  let col := diag.range.start.character + 1
  let sev :=
    match diag.severity with
    | 1 => "error"
    | 2 => "warning"
    | 3 => "info"
    | _ => "hint"
  IO.println s!"{line}:{col}: {sev} {diag.code}: {diag.message}"

def main (args : List String) : IO UInt32 := do
  let path <- match args with
    | path :: _ => pure path
    | [] =>
        IO.eprintln "usage: lake exe mypa-check <file.mypa>|-"
        return 2
  let text <- if path = "-" then do
      let stdin ← IO.getStdin
      stdin.readToEnd
    else
      IO.FS.readFile path
  let uri := if path = "-" then "stdin://mypa" else s!"file://{path}"
  let result := checkDocument { uri := uri, version := 1, text := text }
  if result.diagnostics.isEmpty then
    IO.println "OK"
    return 0
  for diag in result.diagnostics do
    printDiagnostic diag
  return 1
