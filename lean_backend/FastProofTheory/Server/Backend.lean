import FastProofTheory.Server.Protocol
import FastProofTheory.Linear.Engine
import FastProofTheory.Linear.Presentation

namespace FastProofTheory.Server

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

private def helpDisplay? (name : String) : Option ProofDisplay :=
  let normalized := (trimLine name).toLower
  if normalized = "cllp_gentzen" || normalized = "ll_gentzen" then
    some {
      title := s!"Help: {name}"
      status := ""
      sections := [
        {
          title := "System"
          body := ["Classical linear propositional calculus in Urzyczyn-style sequent calculus."]
        },
        {
          title := "Language"
          body := [
            "Formulas: A, B ::= p | A ⊗ B | A & B | A ⊕ B | A ⅋ B | A ⊸ B | !A | 1 | 0 | ⊤ | ⊥",
            "Sequents are displayed as Left ⊢ Right."
          ]
        },
        {
          title := "Tactics And Rules"
          body := [
            "ax: identity / axiom",
            "lx: left exchange",
            "rx: right exchange",
            "cut: cut rule",
            "lleft at h: left with, first conjunct",
            "lright at h: left with, second conjunct",
            "ltensor at h: left tensor",
            "lplus at h: left plus",
            "lpar at h: left par",
            "llolli at h: left lolli",
            "rwith: right with",
            "rtensor: right tensor",
            "rplusl: right plus, first injection",
            "rplusr: right plus, second injection",
            "rpar: right par",
            "rlolli: right lolli",
            "lone at h, lzero at h, lbottom at h: left unit rules",
            "rone, rbottom, rtop: right unit rules",
            "lbang at h, lwhynot at h, rbang, rwhynot: exponential rules",
            "wbang at h, wwhynot at h, cbang at h, cwhynot at h: exponential structural rules"
          ]
        },
        {
          title := "Checked Now"
          body := ["ax", "rlolli", "rtensor", "rwith", "rplusl", "rplusr", "lleft", "lright", "ltensor", "lplus", "llolli", "lbang", "rbang"]
        }
      ]
    }
  else if normalized = "ipc_nd" then
    some {
      title := s!"Help: {name}"
      status := ""
      sections := [
        {
          title := "System"
          body := ["Intuitionistic propositional calculus in natural deduction."]
        },
        {
          title := "Language"
          body := [
            "Formulas: A, B ::= p | A ∧ B | A ∨ B | A ⟶ B | ⊥",
            "Proof state is displayed as hypotheses together with a single current target."
          ]
        },
        {
          title := "Tactics And Rules"
          body := [
            "intro h: implication introduction",
            "assumption h: close goal from a matching hypothesis",
            "constructor: conjunction introduction",
            "left: left disjunction introduction",
            "right: right disjunction introduction",
            "left at h as hp: first conjunction elimination from hypothesis h",
            "right at h as hq: second conjunction elimination from hypothesis h",
            "cases at h as hp hq: disjunction elimination on hypothesis h",
            "apply h: implication elimination using hypothesis h",
            "exfalso: change the current target to ⊥",
            "absurd h: close the goal from a hypothesis h : ⊥"
          ]
        },
        {
          title := "Checked Now"
          body := ["intro", "assumption", "constructor", "left", "right", "cases", "apply", "exfalso", "absurd"]
        }
      ]
    }
  else if normalized = "cpc_nd" then
    some {
      title := s!"Help: {name}"
      status := ""
      sections := [
        {
          title := "System"
          body := ["Classical propositional calculus in natural deduction."]
        },
        {
          title := "Language"
          body := [
            "Formulas: A, B ::= p | A ∧ B | A ∨ B | A ⟶ B | ⊥",
            "This extends IPC in ND with one classical tactic."
          ]
        },
        {
          title := "Tactics And Rules"
          body := [
            "All IPC ND tactics",
            "by_contra h: classical reasoning by assuming h : A ⟶ ⊥ and proving ⊥"
          ]
        },
        {
          title := "Checked Now"
          body := ["intro", "assumption", "constructor", "left", "right", "cases", "apply", "exfalso", "absurd", "by_contra"]
        }
      ]
    }
  else
    some {
      title := s!"Help: {name}"
      status := s!"Unknown formal system `{name}`."
      sections := [
        {
          title := "Known Systems"
          body := ["cllp_gentzen", "ipc_nd", "cpc_nd"]
        }
      ]
    }

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
        display := (helpDisplay? name).getD {
          title := "Help"
          status := "No help available."
          sections := []
        }
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
