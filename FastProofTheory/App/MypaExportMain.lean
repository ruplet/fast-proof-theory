import FastProofTheory.App.Backend

open FastProofTheory.Linear.Export

private def usage : String :=
  "usage: lake exe mypa-export <file.mypa> <theorem-name> -o <output.lean>"

private def parseArgs : List String → Except String (String × String × String)
  | file :: theoremName :: "-o" :: output :: [] => pure (file, theoremName, output)
  | _ :: _ :: _ :: "-o" :: [] =>
      .error s!"Missing path after `-o`.\n{usage}"
  | _ => .error usage

def main (args : List String) : IO UInt32 := do
  let (inputPath, theoremName, outputPath) <- match parseArgs args with
    | .ok parsed => pure parsed
    | .error msg =>
        IO.eprintln msg
        return 2
  let text <- IO.FS.readFile inputPath
  let source <- match exportTheoremFromDocument text theoremName with
    | .ok source => pure source
    | .error msg =>
        IO.eprintln msg
        return 1
  IO.FS.writeFile outputPath source
  IO.println s!"Wrote {outputPath}"
  return 0
