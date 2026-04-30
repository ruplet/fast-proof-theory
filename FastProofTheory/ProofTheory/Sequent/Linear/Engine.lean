import FastProofTheory.DeclaredSystem
import FastProofTheory.ProofTheory.Sequent.Linear.Kernel
import FastProofTheory.Language.Linear.Syntax
import FastProofTheory.ProofTheory.Natural.Kernel
import FastProofTheory.Language.SystemF.Syntax
import FastProofTheory.SystemF.Typing

namespace FastProofTheory.Linear

open FastProofTheory.Linear.Syntax

structure SourceLine where
  number : Nat
  text : String
deriving Inhabited, Repr

structure NumberedText where
  line : Nat
  text : String
deriving Inhabited, Repr

structure ParsedTheorem where
  name : String := "theorem"
  systemText : String := "LL"
  declaredSystem? : Option DeclaredSystem := some (.gentzen (.linearLogic .ll))
  statement? : Option NumberedText := none
  headerError? : Option String := none
  hypotheses : List NumberedText := []
  goals : List NumberedText := []
  tactics : List NumberedText := []
  firstLine : Nat := 0
  lastLine : Nat := 0
deriving Inhabited, Repr

structure Snapshot where
  theorem? : Option ParsedTheorem := none
  sourceLines : List SourceLine := []
deriving Inhabited, Repr

structure EngineGoal where
  id : String
  hypotheses : List String
  target : String
deriving Inhabited, Repr

structure EngineState where
  snapshot : Snapshot
  goals : List EngineGoal
  status : String
  verified : Bool := false
deriving Inhabited, Repr

structure TheoremStatus where
  name : String
  line : Nat
  verified : Bool
deriving Inhabited, Repr

structure NamedHyp where
  name : String
  formula : Formula
  sourceLine : Nat

structure ParsedTactic where
  name : String
  args : List String
  sourceLine : Nat

structure GoalState where
  id : String
  unrestricted : List NamedHyp
  linear : List NamedHyp
  target : Formula
  sourceLine : Nat

inductive WorkItem where
  | goal (goal : GoalState)
  | finishTensor (goal : GoalState) (split : SplitWitness)
  | finishWith (goal : GoalState)
  | finishLolli (goal : GoalState)
  | finishPlusLeft (goal : GoalState)
  | finishPlusRight (goal : GoalState)
  | finishBang (goal : GoalState)
  | finishWithLeft1 (goal : GoalState) (focus : HypFocus)
  | finishWithLeft2 (goal : GoalState) (focus : HypFocus)
  | finishTensorLeft (goal : GoalState) (focus : LinearFocus)
  | finishPlusLeftElim (goal : GoalState) (focus : LinearFocus)
  | finishLolliLeft (goal : GoalState) (focus : LinearFocus) (split : SplitWitness)
  | finishBangLeft (goal : GoalState) (focus : LinearFocus)

structure ExecutionState where
  work : List WorkItem
  solved : List CheckedCertificate
  nextGoalIndex : Nat

structure EngineError where
  line : Nat
  severity : Nat := 1
  code : String := "LINEAR_ENGINE"
  message : String
deriving Inhabited, Repr

structure ParseResult where
  theorems : List ParsedTheorem
  errors : List EngineError
deriving Inhabited, Repr

private def trimLeftChars (chars : List Char) : List Char :=
  chars.dropWhile Char.isWhitespace

private def trimRightChars (chars : List Char) : List Char :=
  (chars.reverse.dropWhile Char.isWhitespace).reverse

def trimLine (line : String) : String :=
  String.ofList (trimRightChars (trimLeftChars line.toList))

def splitWords (line : String) : List String :=
  line.splitOn " " |>.filter (not ·.isEmpty)

def isCommentOrBlank (line : String) : Bool :=
  let trimmed := trimLine line
  trimmed.isEmpty || trimmed.startsWith "--"

def isTacticKeyword (word : String) : Bool :=
  word ∈ [
    "ax", "lx", "rx", "lleft", "lright", "ltensor", "lplus", "lpar", "llolli", "lneg",
    "lone", "lzero", "lbottom", "lbang", "lwhynot",
    "rwith", "rtensor", "rplusl", "rplusr", "rpar", "rlolli", "rneg", "rone", "rbottom",
    "rtop", "rbang", "rwhynot", "wbang", "wwhynot", "cbang", "cwhynot", "cut",
    "intro", "assumption", "constructor", "left", "right", "cases", "apply", "exfalso",
    "absurd", "by_contra", "type_intro", "type_apply", "exact",
    "translate", "translate_to", "tactic", "solve_np"
  ]

private def dropPrefix (text : String) (count : Nat) : String :=
  String.ofList (text.toList.drop count)

private def consumeBalancedPrefix (text : String) (openCh closeCh : Char) : Option String × String :=
  let chars := text.toList
  match chars with
  | c :: rest =>
      if c != openCh then
        (none, text)
      else
        let rec loop (depth : Nat) (remaining acc : List Char) :=
          match remaining with
          | [] => (none, text)
          | ch :: tail =>
              if ch = openCh then
                loop (depth + 1) tail (ch :: acc)
              else if ch = closeCh then
                if depth = 0 then
                  (some (String.ofList acc.reverse), String.ofList tail)
                else
                  loop (depth - 1) tail (ch :: acc)
              else
                loop depth tail (ch :: acc)
        loop 0 rest []
  | [] => (none, text)

private def splitAtTopLevelColon (text : String) : Option (String × String) :=
  let rec loop (remaining : List Char) (braceDepth parenDepth : Nat) (acc : List Char) :=
    match remaining with
    | [] => none
    | c :: rest =>
        if c = '{' then
          loop rest (braceDepth + 1) parenDepth (c :: acc)
        else if c = '}' then
          loop rest (braceDepth - 1) parenDepth (c :: acc)
        else if c = '(' then
          loop rest braceDepth (parenDepth + 1) (c :: acc)
        else if c = ')' then
          loop rest braceDepth (parenDepth - 1) (c :: acc)
        else if c = ':' && braceDepth = 0 && parenDepth = 0 then
          some (String.ofList acc.reverse, String.ofList rest)
        else
          loop rest braceDepth parenDepth (c :: acc)
  loop text.toList 0 0 []

private def stripBySuffix (text : String) : String :=
  let trimmed := trimLine text
  if trimmed.endsWith ":= by" then
    trimLine (String.ofList (trimmed.toList.take (trimmed.length - 5)))
  else if trimmed.endsWith ":=by" then
    trimLine (String.ofList (trimmed.toList.take (trimmed.length - 4)))
  else
    trimmed

private def isGentzenProfileText (text : String) : Bool :=
  let upper := text.toUpper
  upper.contains "GENTZEN"

def theoremHeader? (line : String) : Option (String × String × Option DeclaredSystem × Option String × Option String) :=
  let trimmed := trimLine line
  let shortHeader? :=
    if trimmed.contains ':' then
      none
    else
      match splitWords trimmed with
      | "theorem" :: [] =>
          some ("theorem", "", none, none, some "Theorem statement must be written explicitly in the header.")
      | "theorem" :: name :: [] =>
          some (name, "", none, none, some "Theorem statement must be written explicitly in the header.")
      | "theorem" :: name :: "using" :: systemTokens =>
          let systemText := String.intercalate " " systemTokens
          match parseDeclaredSystemTokens systemTokens with
          | .ok declaredSystem =>
              let headerError? := declaredSystem.validationMessage?
              some (name, systemText, some declaredSystem, none, headerError? <|> some "Theorem statement must be written explicitly in the header.")
          | .error err =>
              some (name, systemText, none, none, some err)
      | _ => none
  match shortHeader? with
  | some header => some header
  | none =>
      let head? :=
        if trimmed.startsWith "theorem " then
          some ("theorem", trimLine (dropPrefix trimmed 8))
        else if trimmed.startsWith "def " then
          some ("def", trimLine (dropPrefix trimmed 4))
        else
          none
      match head? with
      | none => none
      | some (_, restAfterKeyword) =>
          match splitWords restAfterKeyword with
          | [] => none
          | name :: _ =>
              let afterName := trimLine (dropPrefix restAfterKeyword name.length)
              if afterName.startsWith "{" || afterName.startsWith "(" then
                some (name, "", none, none, some "Theorem binders are not supported yet. Write all arguments explicitly in the theorem statement.")
              else
                match splitAtTopLevelColon afterName with
              | none => none
              | some (beforeColon, afterColon) =>
                  let beforeTokens := splitWords (trimLine beforeColon)
                  let (systemText, declaredSystem?, systemError?) :=
                    match beforeTokens with
                    | "using" :: tokens =>
                        let txt := String.intercalate " " tokens
                        match parseDeclaredSystemTokens tokens with
                        | .ok system => (txt, some system, none)
                        | .error err => (txt, none, some err)
                    | _ => ("", none, none)
                  let statementText := stripBySuffix afterColon
                  let headerError? :=
                    if systemText.isEmpty then
                      some "Declare the full logic explicitly, for example `using NJp`, `using NJp with IMP`, `using NKp`, `using LL in GENTZEN with LL`, or `using SYSTEM_F in ND`."
                    else if let some err := systemError? then
                      some err
                    else
                      match declaredSystem? with
                      | some declaredSystem => declaredSystem.validationMessage?
                      | none => none
                  some (name, systemText, declaredSystem?, some statementText, headerError?)

def tacticDecl? (line : String) : Option String :=
  let trimmed := trimLine line
  if trimmed.startsWith "tactic " then
    some trimmed
  else
    match splitWords trimmed with
    | head :: _ => if isTacticKeyword head then some trimmed else none
    | [] => none

private def helpDirectiveTarget? (line : String) : Option String :=
  let trimmed := trimLine line
  if trimmed.startsWith "#help " then
    some (trimLine (String.ofList (trimmed.toList.drop 6)))
  else
    none

private def updateCurrent (current : ParsedTheorem) (lineNo : Nat) : ParsedTheorem :=
  { current with lastLine := lineNo }

def parseDocument (text : String) : ParseResult :=
  let lines := text.splitOn "\n"
  let rec loop
      (remaining : List String)
      (lineNo : Nat)
      (current? : Option ParsedTheorem)
      (errors : List EngineError)
      (theorems : List ParsedTheorem) : ParseResult :=
    match remaining with
    | [] =>
        let theorems :=
          match current? with
          | some current => theorems.reverse ++ [current]
          | none => theorems.reverse
        { theorems, errors := errors.reverse }
    | raw :: rest =>
        let trimmed := trimLine raw
        if isCommentOrBlank raw then
          loop rest (lineNo + 1) current? errors theorems
        else
          match theoremHeader? raw with
          | some (name, systemText, declaredSystem?, statementText?, headerError?) =>
              let theorems :=
                match current? with
                | some current => theorems ++ [current]
                | none => theorems
              let current : ParsedTheorem := {
                name := name
                systemText := systemText
                declaredSystem? := declaredSystem?
                statement? := statementText?.map fun text => { line := lineNo, text := text }
                headerError? := headerError?
                firstLine := lineNo
                lastLine := lineNo
              }
              loop rest (lineNo + 1) (some current) errors theorems
          | none =>
              if trimmed = "end" then
                let theorems :=
                  match current? with
                  | some current => theorems ++ [updateCurrent current lineNo]
                  | none => theorems
                loop rest (lineNo + 1) none errors theorems
              else
                match current? with
                | none =>
                    match helpDirectiveTarget? trimmed with
                    | some _ =>
                        loop rest (lineNo + 1) none errors theorems
                    | none =>
                        let err :=
                          if trimmed.startsWith "#" then
                            {
                              line := lineNo
                              severity := 1
                              code := "LEAN_BACKEND_DIRECTIVE"
                              message := "Unknown top-level directive. Supported directives: `#help <system>`."
                            }
                          else
                            { line := lineNo, message := "Content must appear inside a theorem block." }
                        loop rest (lineNo + 1) none (err :: errors) theorems
                | some current =>
                    let current := updateCurrent current lineNo
                    if trimmed.startsWith "#" then
                      let err := {
                        line := lineNo
                        severity := 1
                        code := "LEAN_BACKEND_DIRECTIVE"
                        message := "Directives like `#help` are only allowed at top scope, outside theorem definitions."
                      }
                      loop rest (lineNo + 1) (some current) (err :: errors) theorems
                    else if trimmed.startsWith "hyp " || trimmed.startsWith "goal " then
                      let err := {
                        line := lineNo
                        severity := 1
                        code := "LEAN_BACKEND_LEGACY_SYNTAX"
                        message := "Legacy `hyp`/`goal` declarations are no longer supported. Write the whole theorem statement explicitly in the header."
                      }
                      loop rest (lineNo + 1) (some current) (err :: errors) theorems
                    else
                      match tacticDecl? raw with
                      | some tactic =>
                          loop rest (lineNo + 1)
                            (some { current with tactics := current.tactics ++ [{ line := lineNo, text := tactic }] })
                            errors theorems
                      | none =>
                          let err := {
                            line := lineNo
                            severity := 1
                            code := "LEAN_BACKEND_PARSE"
                            message := s!"Unrecognized command: {trimmed}"
                          }
                          loop rest (lineNo + 1) (some current) (err :: errors) theorems
  loop lines 0 none [] []

def theoremAtCursor (cursorLine : Nat) (theorems : List ParsedTheorem) : Option ParsedTheorem :=
  theorems.find? (fun thm => thm.firstLine ≤ cursorLine && cursorLine ≤ thm.lastLine)

private def lineVisibleAtCursor (cursorLine cursorCharacter : Nat) (sourceLines : List SourceLine) (entry : NumberedText) : Bool :=
  if entry.line < cursorLine then
    true
  else if entry.line > cursorLine then
    false
  else
    match sourceLines.find? (fun line => line.number = entry.line) with
    | some line =>
        let threshold :=
          if line.text.isEmpty then
            0
          else
            line.text.length - 1
        cursorCharacter >= threshold
    | none => false

private def takeVisibleEntries (cursorLine cursorCharacter : Nat) (sourceLines : List SourceLine) (entries : List NumberedText) : List NumberedText :=
  entries.filter (lineVisibleAtCursor cursorLine cursorCharacter sourceLines)

def scopeTheoremToCursor (cursorLine cursorCharacter : Nat) (sourceLines : List SourceLine) (thm : ParsedTheorem) : ParsedTheorem :=
  {
    thm with
    hypotheses := takeVisibleEntries cursorLine cursorCharacter sourceLines thm.hypotheses
    goals := takeVisibleEntries cursorLine cursorCharacter sourceLines thm.goals
    tactics := takeVisibleEntries cursorLine cursorCharacter sourceLines thm.tactics
    lastLine := Nat.min thm.lastLine cursorLine
  }

def snapshotAtCursor (text : String) (cursorLine cursorCharacter : Nat) : Snapshot :=
  let parsed := parseDocument text
  let rec collectSourceLines (remaining : List String) (idx : Nat) : List SourceLine :=
    match remaining with
    | [] => []
    | line :: rest => { number := idx, text := line } :: collectSourceLines rest (idx + 1)
  let sourceLines := collectSourceLines (text.splitOn "\n") 0
  let theorem? :=
    match theoremAtCursor cursorLine parsed.theorems with
    | some thm => some (scopeTheoremToCursor cursorLine cursorCharacter sourceLines thm)
    | none => none
  { theorem?, sourceLines }

private def parseHypothesisLine (system : DeclaredSystem) (entry : NumberedText) : Except EngineError NamedHyp := do
  let trimmed := trimLine entry.text
  let after := trimLine (String.ofList (trimmed.toList.drop 3))
  let parts := after.splitOn ":"
  match parts with
  | [lhs, rhs] =>
      let name := trimLine lhs
      let formulaText := trimLine rhs
      match parseFormula system formulaText with
      | .ok formula => pure { name, formula, sourceLine := entry.line }
      | .error err =>
          throw {
            line := entry.line
            severity := 1
            code := "LEAN_BACKEND_FORMULA"
            message := s!"Invalid hypothesis formula `{formulaText}`: {err}"
          }
  | _ =>
      throw {
        line := entry.line
        severity := 1
        code := "LEAN_BACKEND_HYP"
        message := "Hypothesis must have the form `hyp <name> : <formula>`."
      }

private def parseGoalLine (system : DeclaredSystem) (entry : NumberedText) : Except EngineError Formula := do
  let trimmed := trimLine entry.text
  let formulaText := trimLine (String.ofList (trimmed.toList.drop 4))
  match parseFormula system formulaText with
  | .ok formula => pure formula
  | .error err =>
      throw {
        line := entry.line
        severity := 1
        code := "LEAN_BACKEND_FORMULA"
        message := s!"Invalid goal formula `{formulaText}`: {err}"
      }

private def parseStatementGoal (system : DeclaredSystem) (entry : NumberedText) : Except EngineError Formula := do
  match parseTheoremStatement system entry.text with
  | Except.ok formula => pure formula
  | Except.error err =>
      throw {
        line := entry.line
        severity := 1
        code := "LEAN_BACKEND_THEOREM"
        message := s!"Invalid theorem statement `{entry.text}`: {err}"
      }

private def parseTacticLine (entry : NumberedText) : ParsedTactic :=
  let trimmed := trimLine entry.text
  let words := splitWords trimmed
  match words with
  | "tactic" :: name :: args => { name, args, sourceLine := entry.line }
  | name :: args => { name, args, sourceLine := entry.line }
  | [] => { name := "", args := [], sourceLine := entry.line }

private def initialGoals (thm : ParsedTheorem) (hyps : List NamedHyp) (goals : List (Nat × Formula)) :
    List WorkItem :=
  let rec build (remaining : List (Nat × Formula)) (idx : Nat) : List WorkItem :=
    match remaining with
    | [] => []
    | (line, target) :: rest =>
        WorkItem.goal {
          id := s!"{thm.name}:g{idx}"
          unrestricted := []
          linear := hyps
          target := target
          sourceLine := line
        } :: build rest (idx + 1)
  build goals 1

private def goalToKernel (goal : GoalState) : Goal :=
  {
    unrestricted := goal.unrestricted.map (·.formula)
    linear := goal.linear.map (·.formula)
    target := goal.target
  }

private def goalToView (goal : GoalState) : EngineGoal :=
  {
    id := goal.id
    hypotheses :=
      goal.unrestricted.map (fun hyp => s!"(u) {hyp.name} : {renderFormula hyp.formula}") ++
      goal.linear.map (fun hyp => s!"{hyp.name} : {renderFormula hyp.formula}")
    target := renderFormula goal.target
  }

private inductive ContextKind where
  | unrestricted
  | linear

private def extractNamedHyp
    (ctx : List NamedHyp)
    (name : String) :
    Option (List NamedHyp × NamedHyp × List NamedHyp) := Id.run do
  let rec loop (beforeAcc : List NamedHyp) (rest : List NamedHyp) :=
    match rest with
    | [] => none
    | hyp :: tail =>
        if hyp.name = name then
          some (beforeAcc.reverse, hyp, tail)
        else
          loop (hyp :: beforeAcc) tail
  loop [] ctx

private def lookupGoalHyp
    (goal : GoalState)
    (name : String) :
    Option (ContextKind × List NamedHyp × NamedHyp × List NamedHyp) :=
  match extractNamedHyp goal.linear name with
  | some (before, hyp, after) => some (.linear, before, hyp, after)
  | none =>
      match extractNamedHyp goal.unrestricted name with
      | some (before, hyp, after) => some (.unrestricted, before, hyp, after)
      | none => none

private def formulaMatches (a b : Formula) : Bool :=
  formulaEq a b

private def parseAtClause
    (tactic : ParsedTactic) :
    Except EngineError (String × List String) := do
  match tactic.args with
  | "at" :: name :: rest => pure (name, rest)
  | name :: rest => pure (name, rest)
  | [] =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := "LEAN_BACKEND_TACTIC_ARGS"
        message := s!"Tactic `{tactic.name}` requires `at <hypothesis>`."
      }

private def parseAsOne (rest : List String) : Option String :=
  match rest with
  | "as" :: name :: _ => some name
  | _ => none

private def parseAsTwo (rest : List String) : Option (String × String) :=
  match rest with
  | "as" :: left :: right :: _ => some (left, right)
  | _ => none

private def parseUsingAndAs
    (rest : List String) :
    (List String × Option String) :=
  match rest with
  | "using" :: tail =>
      let rec takeUsing (remaining : List String) (usingAcc : List String) :=
        match remaining with
        | [] => (usingAcc.reverse, none)
        | "as" :: name :: _ => (usingAcc.reverse, some name)
        | token :: more => takeUsing more (token :: usingAcc)
      takeUsing tail []
  | "as" :: name :: _ => ([], some name)
  | _ => ([], none)

private def replaceHypInGoal
    (goal : GoalState)
    (kind : ContextKind)
    (before : List NamedHyp)
    (replacement : List NamedHyp)
    (after : List NamedHyp) :
    GoalState :=
  match kind with
  | .linear =>
      { goal with linear := before ++ replacement ++ after }
  | .unrestricted =>
      { goal with unrestricted := before ++ replacement ++ after }

private def mkLinearFocus (before : List NamedHyp) (focused : NamedHyp) (after : List NamedHyp) : LinearFocus :=
  { before := before.map (·.formula), focused := focused.formula, after := after.map (·.formula) }

private def mkHypFocus
    (kind : ContextKind)
    (before : List NamedHyp)
    (focused : NamedHyp)
    (after : List NamedHyp) : HypFocus :=
  match kind with
  | .linear => .linear { before := before.map (·.formula), focused := focused.formula, after := after.map (·.formula) }
  | .unrestricted => .unrestricted { before := before.map (·.formula), focused := focused.formula, after := after.map (·.formula) }

private def splitGoalByNames (goal : GoalState) (names : List String) :
    Except EngineError (GoalState × GoalState × SplitWitness) := do
  match goal.target with
  | .tensor leftTarget rightTarget =>
      let unique := names.eraseDups
      if unique.length != names.length then
        throw {
          line := goal.sourceLine
          severity := 1
          code := "LEAN_BACKEND_SPLIT"
          message := "split received duplicate hypothesis names."
        }
      let rec partition
          (remaining : List NamedHyp)
          (leftAcc rightAcc : List NamedHyp) :
          Except EngineError (List NamedHyp × List NamedHyp) :=
        match remaining with
        | [] => pure (leftAcc.reverse, rightAcc.reverse)
        | hyp :: rest =>
            if hyp.name ∈ unique then
              partition rest (hyp :: leftAcc) rightAcc
            else
              partition rest leftAcc (hyp :: rightAcc)
      let (leftHyps, rightHyps) <- partition goal.linear [] []
      for name in unique do
        unless goal.linear.any (fun hyp => hyp.name = name) do
          throw {
            line := goal.sourceLine
            severity := 1
            code := "LEAN_BACKEND_SPLIT"
            message := s!"Unknown hypothesis `{name}` in split."
          }
      let split := SplitWitness.explicit (leftHyps.map (·.formula)) (rightHyps.map (·.formula))
      pure (
        { goal with id := s!"{goal.id}.L", target := leftTarget, linear := leftHyps },
        { goal with id := s!"{goal.id}.R", target := rightTarget, linear := rightHyps },
        split
      )
  | _ =>
      throw {
        line := goal.sourceLine
        severity := 1
        code := "LEAN_BACKEND_SPLIT"
        message := "split applies only to tensor goals."
      }

private def resolveAxiomCertificate (goal : GoalState) (args : List String) :
    Except EngineError Certificate := do
  let arg? := args.head?
  match arg? with
  | some name =>
      match goal.linear.find? (fun hyp => hyp.name = name) with
      | some hyp =>
          if formulaMatches hyp.formula goal.target then
            pure .assumption
          else
            throw {
              line := goal.sourceLine
              severity := 1
              code := "LEAN_BACKEND_AX"
              message := s!"Hypothesis `{name}` does not match the current goal."
            }
      | none =>
          match goal.unrestricted.find? (fun hyp => hyp.name = name) with
          | some hyp =>
              if formulaMatches hyp.formula goal.target then
                pure .useUnrestricted
              else
                throw {
                  line := goal.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_AX"
                  message := s!"Hypothesis `{name}` does not match the current goal."
                }
          | none =>
              throw {
                line := goal.sourceLine
                severity := 1
                code := "LEAN_BACKEND_AX"
                message := s!"Unknown hypothesis `{name}`."
              }
  | none =>
      throw {
        line := goal.sourceLine
        severity := 1
        code := "LEAN_BACKEND_AX"
        message := "ax requires a hypothesis name."
      }

private def rewriteWithTactic
    (goal : GoalState)
    (tactic : ParsedTactic)
    (useLeft : Bool) :
    Except EngineError GoalState := do
  let (name, rest) <- parseAtClause tactic
  let alias := (parseAsOne rest).getD name
  match lookupGoalHyp goal name with
  | some (kind, before, hyp, after) =>
      match hyp.formula with
      | .with left right =>
          let replacement := { name := alias, formula := if useLeft then left else right, sourceLine := tactic.sourceLine }
          pure <| replaceHypInGoal goal kind before [replacement] after
      | _ =>
          throw {
            line := tactic.sourceLine
            severity := 1
            code := if useLeft then "LEAN_BACKEND_LLEFT" else "LEAN_BACKEND_LRIGHT"
            message := s!"Tactic `{tactic.name}` applies only to `A & B` hypotheses."
          }
  | none =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := if useLeft then "LEAN_BACKEND_LLEFT" else "LEAN_BACKEND_LRIGHT"
        message := s!"Unknown hypothesis `{name}`."
      }

private def tensorLeftGoal
    (goal : GoalState)
    (tactic : ParsedTactic) :
    Except EngineError GoalState := do
  let (name, rest) <- parseAtClause tactic
  let (leftName, rightName) :=
    match parseAsTwo rest with
    | some pair => pair
    | none => (s!"{name}.1", s!"{name}.2")
  match lookupGoalHyp goal name with
  | some (.linear, before, hyp, after) =>
      match hyp.formula with
      | .tensor left right =>
          let repl := [
            { name := leftName, formula := left, sourceLine := tactic.sourceLine },
            { name := rightName, formula := right, sourceLine := tactic.sourceLine }
          ]
          pure <| replaceHypInGoal goal .linear before repl after
      | _ =>
          throw {
            line := tactic.sourceLine
            severity := 1
            code := "LEAN_BACKEND_LTENSOR"
            message := "ltensor applies only to `A ⊗ B` hypotheses."
          }
  | some (.unrestricted, _, _, _) =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := "LEAN_BACKEND_LTENSOR"
        message := "ltensor applies only to linear hypotheses."
      }
  | none =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := "LEAN_BACKEND_LTENSOR"
        message := s!"Unknown hypothesis `{name}`."
      }

private def plusLeftGoals
    (goal : GoalState)
    (tactic : ParsedTactic) :
    Except EngineError (GoalState × GoalState) := do
  let (name, rest) <- parseAtClause tactic
  let (leftName, rightName) :=
    match parseAsTwo rest with
    | some pair => pair
    | none => (s!"{name}.L", s!"{name}.R")
  match lookupGoalHyp goal name with
  | some (.linear, before, hyp, after) =>
      match hyp.formula with
      | .plus left right =>
          let leftGoal :=
            replaceHypInGoal goal .linear before [{ name := leftName, formula := left, sourceLine := tactic.sourceLine }] after
          let rightGoal :=
            replaceHypInGoal goal .linear before [{ name := rightName, formula := right, sourceLine := tactic.sourceLine }] after
          pure ({ leftGoal with id := s!"{goal.id}.plusL" }, { rightGoal with id := s!"{goal.id}.plusR" })
      | _ =>
          throw {
            line := tactic.sourceLine
            severity := 1
            code := "LEAN_BACKEND_LPLUS"
            message := "lplus applies only to `A ⊕ B` hypotheses."
          }
  | some (.unrestricted, _, _, _) =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := "LEAN_BACKEND_LPLUS"
        message := "lplus applies only to linear hypotheses."
      }
  | none =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := "LEAN_BACKEND_LPLUS"
        message := s!"Unknown hypothesis `{name}`."
      }

private def lolliLeftGoals
    (goal : GoalState)
    (tactic : ParsedTactic) :
    Except EngineError (GoalState × GoalState) := do
  let (name, rest) <- parseAtClause tactic
  let (usingNames, alias?) := parseUsingAndAs rest
  match lookupGoalHyp goal name with
  | some (.linear, before, hyp, after) =>
      match hyp.formula with
      | .lolli premise consequence =>
          let alias := alias?.getD name
          let remaining := before ++ after
          let usingSet := usingNames.eraseDups
          if usingSet.length != usingNames.length then
            throw {
              line := tactic.sourceLine
              severity := 1
              code := "LEAN_BACKEND_LLOLLI"
              message := "llolli received duplicate hypothesis names in `using`."
            }
          for used in usingSet do
            unless remaining.any (fun item => item.name = used) do
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_LLOLLI"
                message := s!"Unknown hypothesis `{used}` in llolli split."
              }
          let leftHyps := remaining.filter (fun item => item.name ∈ usingSet)
          let rightHyps := remaining.filter (fun item => item.name ∉ usingSet)
          let premiseGoal : GoalState := {
            goal with
            id := s!"{goal.id}.llolliL"
            linear := leftHyps
            target := premise
          }
          let consequenceGoal : GoalState := {
            goal with
            id := s!"{goal.id}.llolliR"
            linear := { name := alias, formula := consequence, sourceLine := tactic.sourceLine } :: rightHyps
          }
          pure (premiseGoal, consequenceGoal)
      | _ =>
          throw {
            line := tactic.sourceLine
            severity := 1
            code := "LEAN_BACKEND_LLOLLI"
            message := "llolli applies only to `A ⊸ B` hypotheses."
          }
  | some (.unrestricted, _, _, _) =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := "LEAN_BACKEND_LLOLLI"
        message := "llolli applies only to linear hypotheses."
      }
  | none =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := "LEAN_BACKEND_LLOLLI"
        message := s!"Unknown hypothesis `{name}`."
      }

private def bangLeftGoal
    (goal : GoalState)
    (tactic : ParsedTactic) :
    Except EngineError GoalState := do
  let (name, rest) <- parseAtClause tactic
  let alias := (parseAsOne rest).getD name
  match lookupGoalHyp goal name with
  | some (.linear, before, hyp, after) =>
      match hyp.formula with
      | .bang body =>
          pure {
            (replaceHypInGoal goal .linear before [] after) with
            unrestricted := goal.unrestricted ++ [{ name := alias, formula := body, sourceLine := tactic.sourceLine }]
          }
      | _ =>
          throw {
            line := tactic.sourceLine
            severity := 1
            code := "LEAN_BACKEND_LBANG"
            message := "lbang applies only to `!A` hypotheses."
          }
  | some (.unrestricted, _, _, _) =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := "LEAN_BACKEND_LBANG"
        message := "lbang applies only to linear hypotheses."
      }
  | none =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := "LEAN_BACKEND_LBANG"
        message := s!"Unknown hypothesis `{name}`."
      }

private def bangRightGoal
    (goal : GoalState)
    (tactic : ParsedTactic) :
    Except EngineError GoalState := do
  match goal.target with
  | .bang body =>
      if !goal.linear.isEmpty then
        throw {
          line := tactic.sourceLine
          severity := 1
          code := "LEAN_BACKEND_RBANG"
          message := "rbang requires an empty linear context. Move `!A` assumptions with `lbang` first."
        }
      pure { goal with id := s!"{goal.id}.bang", target := body }
  | _ =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := "LEAN_BACKEND_RBANG"
        message := "rbang applies only to `!A` succedent goals."
      }

private def introGoal (goal : GoalState) (args : List String) :
    Except EngineError GoalState := do
  match goal.target with
  | .lolli premise target =>
      let hypName := args.head?.getD s!"h{goal.linear.length + goal.unrestricted.length + 1}"
      if goal.linear.any (fun hyp => hyp.name = hypName) || goal.unrestricted.any (fun hyp => hyp.name = hypName) then
        throw {
          line := goal.sourceLine
          severity := 1
          code := "LEAN_BACKEND_INTRO"
          message := s!"Hypothesis name `{hypName}` is already in scope."
        }
      pure {
        goal with
        id := s!"{goal.id}.body"
        linear := goal.linear ++ [{ name := hypName, formula := premise, sourceLine := goal.sourceLine }]
        target := target
      }
  | _ =>
      throw {
        line := goal.sourceLine
        severity := 1
        code := "LEAN_BACKEND_INTRO"
        message := "intro applies only to linear implication goals."
      }

private partial def normalize (logic : FastProofTheory.Gentzen.LinearLogic) (state : ExecutionState) :
    Except EngineError ExecutionState := do
  match state.work with
  | WorkItem.finishTensor goal split :: rest =>
      match state.solved with
      | right :: left :: solvedRest =>
          let certificate := Certificate.tensorIntro split left.certificate right.certificate
          match checkCertificate logic (goalToKernel goal) certificate with
          | .ok checked =>
              normalize logic { state with work := rest, solved := checked :: solvedRest }
          | .error err =>
              throw {
                line := goal.sourceLine
                severity := 1
                code := "LEAN_BACKEND_KERNEL"
                message := renderKernelError err
              }
      | _ =>
          throw {
            line := goal.sourceLine
            severity := 1
            code := "LEAN_BACKEND_INTERNAL"
            message := "tensor completion frame is missing solved subproofs."
          }
  | WorkItem.finishWith goal :: rest =>
      match state.solved with
      | right :: left :: solvedRest =>
          let certificate := Certificate.withIntro left.certificate right.certificate
          match checkCertificate logic (goalToKernel goal) certificate with
          | .ok checked =>
              normalize logic { state with work := rest, solved := checked :: solvedRest }
          | .error err =>
              throw {
                line := goal.sourceLine
                severity := 1
                code := "LEAN_BACKEND_KERNEL"
                message := renderKernelError err
              }
      | _ =>
          throw {
            line := goal.sourceLine
            severity := 1
            code := "LEAN_BACKEND_INTERNAL"
            message := "with completion frame is missing solved subproofs."
          }
  | WorkItem.finishLolli goal :: rest =>
      match state.solved with
      | body :: solvedRest =>
          let certificate := Certificate.lolliIntro body.certificate
          match checkCertificate logic (goalToKernel goal) certificate with
          | .ok checked =>
              normalize logic { state with work := rest, solved := checked :: solvedRest }
          | .error err =>
              throw {
                line := goal.sourceLine
                severity := 1
                code := "LEAN_BACKEND_KERNEL"
                message := renderKernelError err
              }
      | _ =>
          throw {
            line := goal.sourceLine
            severity := 1
            code := "LEAN_BACKEND_INTERNAL"
            message := "lolli completion frame is missing a solved subproof."
          }
  | WorkItem.finishPlusLeft goal :: rest =>
      match state.solved with
      | body :: solvedRest =>
          let certificate := Certificate.plusLeft body.certificate
          match checkCertificate logic (goalToKernel goal) certificate with
          | .ok checked =>
              normalize logic { state with work := rest, solved := checked :: solvedRest }
          | .error err =>
              throw {
                line := goal.sourceLine
                severity := 1
                code := "LEAN_BACKEND_KERNEL"
                message := renderKernelError err
              }
      | _ =>
          throw {
            line := goal.sourceLine
            severity := 1
            code := "LEAN_BACKEND_INTERNAL"
            message := "plus-left completion frame is missing a solved subproof."
          }
  | WorkItem.finishPlusRight goal :: rest =>
      match state.solved with
      | body :: solvedRest =>
          let certificate := Certificate.plusRight body.certificate
          match checkCertificate logic (goalToKernel goal) certificate with
          | .ok checked =>
              normalize logic { state with work := rest, solved := checked :: solvedRest }
          | .error err =>
              throw {
                line := goal.sourceLine
                severity := 1
                code := "LEAN_BACKEND_KERNEL"
                message := renderKernelError err
              }
      | _ =>
          throw {
            line := goal.sourceLine
            severity := 1
            code := "LEAN_BACKEND_INTERNAL"
            message := "plus-right completion frame is missing a solved subproof."
          }
  | WorkItem.finishBang goal :: rest =>
      match state.solved with
      | body :: solvedRest =>
          let certificate := Certificate.bangIntro body.certificate
          match checkCertificate logic (goalToKernel goal) certificate with
          | .ok checked =>
              normalize logic { state with work := rest, solved := checked :: solvedRest }
          | .error err =>
              throw {
                line := goal.sourceLine
                severity := 1
                code := "LEAN_BACKEND_KERNEL"
                message := renderKernelError err
              }
      | _ =>
          throw {
            line := goal.sourceLine
            severity := 1
            code := "LEAN_BACKEND_INTERNAL"
            message := "bang completion frame is missing a solved subproof."
          }
  | WorkItem.finishWithLeft1 goal focus :: rest =>
      match state.solved with
      | body :: solvedRest =>
          let certificate := Certificate.withLeft1 focus body.certificate
          match checkCertificate logic (goalToKernel goal) certificate with
          | .ok checked =>
              normalize logic { state with work := rest, solved := checked :: solvedRest }
          | .error err =>
              throw {
                line := goal.sourceLine
                severity := 1
                code := "LEAN_BACKEND_KERNEL"
                message := renderKernelError err
              }
      | _ =>
          throw {
            line := goal.sourceLine
            severity := 1
            code := "LEAN_BACKEND_INTERNAL"
            message := "with-left-1 completion frame is missing a solved subproof."
          }
  | WorkItem.finishWithLeft2 goal focus :: rest =>
      match state.solved with
      | body :: solvedRest =>
          let certificate := Certificate.withLeft2 focus body.certificate
          match checkCertificate logic (goalToKernel goal) certificate with
          | .ok checked =>
              normalize logic { state with work := rest, solved := checked :: solvedRest }
          | .error err =>
              throw {
                line := goal.sourceLine
                severity := 1
                code := "LEAN_BACKEND_KERNEL"
                message := renderKernelError err
              }
      | _ =>
          throw {
            line := goal.sourceLine
            severity := 1
            code := "LEAN_BACKEND_INTERNAL"
            message := "with-left-2 completion frame is missing a solved subproof."
          }
  | WorkItem.finishTensorLeft goal focus :: rest =>
      match state.solved with
      | body :: solvedRest =>
          let certificate := Certificate.tensorLeft focus body.certificate
          match checkCertificate logic (goalToKernel goal) certificate with
          | .ok checked =>
              normalize logic { state with work := rest, solved := checked :: solvedRest }
          | .error err =>
              throw {
                line := goal.sourceLine
                severity := 1
                code := "LEAN_BACKEND_KERNEL"
                message := renderKernelError err
              }
      | _ =>
          throw {
            line := goal.sourceLine
            severity := 1
            code := "LEAN_BACKEND_INTERNAL"
            message := "tensor-left completion frame is missing a solved subproof."
          }
  | WorkItem.finishPlusLeftElim goal focus :: rest =>
      match state.solved with
      | right :: left :: solvedRest =>
          let certificate := Certificate.plusLeftElim focus left.certificate right.certificate
          match checkCertificate logic (goalToKernel goal) certificate with
          | .ok checked =>
              normalize logic { state with work := rest, solved := checked :: solvedRest }
          | .error err =>
              throw {
                line := goal.sourceLine
                severity := 1
                code := "LEAN_BACKEND_KERNEL"
                message := renderKernelError err
              }
      | _ =>
          throw {
            line := goal.sourceLine
            severity := 1
            code := "LEAN_BACKEND_INTERNAL"
            message := "plus-left completion frame is missing solved subproofs."
          }
  | WorkItem.finishLolliLeft goal focus split :: rest =>
      match state.solved with
      | right :: left :: solvedRest =>
          let certificate := Certificate.lolliLeft focus split left.certificate right.certificate
          match checkCertificate logic (goalToKernel goal) certificate with
          | .ok checked =>
              normalize logic { state with work := rest, solved := checked :: solvedRest }
          | .error err =>
              throw {
                line := goal.sourceLine
                severity := 1
                code := "LEAN_BACKEND_KERNEL"
                message := renderKernelError err
              }
      | _ =>
          throw {
            line := goal.sourceLine
            severity := 1
            code := "LEAN_BACKEND_INTERNAL"
            message := "lolli-left completion frame is missing solved subproofs."
          }
  | WorkItem.finishBangLeft goal focus :: rest =>
      match state.solved with
      | body :: solvedRest =>
          let certificate := Certificate.bangLeft focus body.certificate
          match checkCertificate logic (goalToKernel goal) certificate with
          | .ok checked =>
              normalize logic { state with work := rest, solved := checked :: solvedRest }
          | .error err =>
              throw {
                line := goal.sourceLine
                severity := 1
                code := "LEAN_BACKEND_KERNEL"
                message := renderKernelError err
              }
      | _ =>
          throw {
            line := goal.sourceLine
            severity := 1
            code := "LEAN_BACKEND_INTERNAL"
            message := "bang-left completion frame is missing a solved subproof."
          }
  | _ => pure state

private def applyTactic (logic : FastProofTheory.Gentzen.LinearLogic) (tactic : ParsedTactic) (state : ExecutionState) :
    Except EngineError ExecutionState := do
  let state <- normalize logic state
  match state.work with
  | WorkItem.goal goal :: rest =>
      match tactic.name with
      | "ax" =>
          let cert <- resolveAxiomCertificate goal tactic.args
          match checkCertificate logic (goalToKernel goal) cert with
          | .ok checked => normalize logic { state with work := rest, solved := checked :: state.solved }
          | .error err =>
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_KERNEL"
                message := renderKernelError err
              }
      | "rwith" =>
          match goal.target with
          | .with leftTarget rightTarget =>
              let leftGoal : GoalState := { goal with id := s!"{goal.id}.L", target := leftTarget }
              let rightGoal : GoalState := { goal with id := s!"{goal.id}.R", target := rightTarget }
              pure {
                state with
                work := WorkItem.goal leftGoal :: WorkItem.goal rightGoal :: WorkItem.finishWith goal :: rest
              }
          | _ =>
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_RWITH"
                message := "rwith applies only to `A & B` succedent goals."
              }
      | "rtensor" =>
          match goal.target with
          | .tensor _ _ =>
              let (leftGoal, rightGoal, split) <- splitGoalByNames goal tactic.args
              pure {
                state with
                work := WorkItem.goal leftGoal :: WorkItem.goal rightGoal :: WorkItem.finishTensor goal split :: rest
              }
          | _ =>
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_RTENSOR"
                message := "rtensor applies only to `A ⊗ B` succedent goals."
              }
      | "rlolli" =>
          let bodyGoal <- introGoal goal tactic.args
          pure {
            state with
            work := WorkItem.goal bodyGoal :: WorkItem.finishLolli goal :: rest
          }
      | "rplusl" =>
          match goal.target with
          | .plus leftTarget _ =>
              pure {
                state with
                work := WorkItem.goal { goal with id := s!"{goal.id}.plusl", target := leftTarget }
                  :: WorkItem.finishPlusLeft goal :: rest
              }
          | _ =>
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_RPLUSL"
                message := "rplusl applies only to `A ⊕ B` succedent goals."
              }
      | "rplusr" =>
          match goal.target with
          | .plus _ rightTarget =>
              pure {
                state with
                work := WorkItem.goal { goal with id := s!"{goal.id}.plusr", target := rightTarget }
                  :: WorkItem.finishPlusRight goal :: rest
              }
          | _ =>
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_RPLUSR"
                message := "rplusr applies only to `A ⊕ B` succedent goals."
              }
      | "rbang" =>
          let bodyGoal <- bangRightGoal goal tactic
          pure {
            state with
            work := WorkItem.goal bodyGoal :: WorkItem.finishBang goal :: rest
          }
      | "lleft" =>
          let (name, _) <- parseAtClause tactic
          let nextGoal <- rewriteWithTactic goal tactic true
          let focus <-
            match lookupGoalHyp goal name with
            | some (kind, before, hyp, after) => pure <| mkHypFocus kind before hyp after
            | none =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_LLEFT"
                  message := s!"Unknown hypothesis `{name}`."
                }
          pure {
            state with
            work := WorkItem.goal { nextGoal with id := s!"{goal.id}.lleft" } :: WorkItem.finishWithLeft1 goal focus :: rest
          }
      | "lright" =>
          let (name, _) <- parseAtClause tactic
          let nextGoal <- rewriteWithTactic goal tactic false
          let focus <-
            match lookupGoalHyp goal name with
            | some (kind, before, hyp, after) => pure <| mkHypFocus kind before hyp after
            | none =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_LRIGHT"
                  message := s!"Unknown hypothesis `{name}`."
                }
          pure {
            state with
            work := WorkItem.goal { nextGoal with id := s!"{goal.id}.lright" } :: WorkItem.finishWithLeft2 goal focus :: rest
          }
      | "ltensor" =>
          let (name, _) <- parseAtClause tactic
          let nextGoal <- tensorLeftGoal goal tactic
          let focus <-
            match lookupGoalHyp goal name with
            | some (.linear, before, hyp, after) => pure <| mkLinearFocus before hyp after
            | some (.unrestricted, _, _, _) =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_LTENSOR"
                  message := "ltensor applies only to linear hypotheses."
                }
            | none =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_LTENSOR"
                  message := s!"Unknown hypothesis `{name}`."
                }
          pure {
            state with
            work := WorkItem.goal { nextGoal with id := s!"{goal.id}.ltensor" } :: WorkItem.finishTensorLeft goal focus :: rest
          }
      | "lplus" =>
          let (name, _) <- parseAtClause tactic
          let (leftGoal, rightGoal) <- plusLeftGoals goal tactic
          let focus <-
            match lookupGoalHyp goal name with
            | some (.linear, before, hyp, after) => pure <| mkLinearFocus before hyp after
            | some (.unrestricted, _, _, _) =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_LPLUS"
                  message := "lplus applies only to linear hypotheses."
                }
            | none =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_LPLUS"
                  message := s!"Unknown hypothesis `{name}`."
                }
          pure {
            state with
            work := WorkItem.goal leftGoal :: WorkItem.goal rightGoal :: WorkItem.finishPlusLeftElim goal focus :: rest
          }
      | "llolli" =>
          let (name, restArgs) <- parseAtClause tactic
          let (premiseGoal, consequenceGoal) <- lolliLeftGoals goal tactic
          let (usingNames, _) := parseUsingAndAs restArgs
          let focusAndSplit <-
            match lookupGoalHyp goal name with
            | some (.linear, before, hyp, after) =>
                let tailHyps := before ++ after
                let usingSet := usingNames.eraseDups
                let leftHyps := tailHyps.filter (fun item => item.name ∈ usingSet)
                let rightHyps := tailHyps.filter (fun item => item.name ∉ usingSet)
                pure (mkLinearFocus before hyp after, SplitWitness.explicit (leftHyps.map (·.formula)) (rightHyps.map (·.formula)))
            | some (.unrestricted, _, _, _) =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_LLOLLI"
                  message := "llolli applies only to linear hypotheses."
                }
            | none =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_LLOLLI"
                  message := s!"Unknown hypothesis `{name}`."
                }
          let (focus, split) := focusAndSplit
          pure {
            state with
            work := WorkItem.goal premiseGoal :: WorkItem.goal consequenceGoal :: WorkItem.finishLolliLeft goal focus split :: rest
          }
      | "lbang" =>
          let (name, _) <- parseAtClause tactic
          let nextGoal <- bangLeftGoal goal tactic
          let focus <-
            match lookupGoalHyp goal name with
            | some (.linear, before, hyp, after) => pure <| mkLinearFocus before hyp after
            | some (.unrestricted, _, _, _) =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_LBANG"
                  message := "lbang applies only to linear hypotheses."
                }
            | none =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_LBANG"
                  message := s!"Unknown hypothesis `{name}`."
                }
          pure {
            state with
            work := WorkItem.goal { nextGoal with id := s!"{goal.id}.lbang" } :: WorkItem.finishBangLeft goal focus :: rest
          }
      | other =>
          throw {
            line := tactic.sourceLine
            severity := 1
            code := "LEAN_BACKEND_UNSUPPORTED_TACTIC"
            message := s!"Tactic `{other}` is not implemented in the checked linear engine yet."
          }
  | [] =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := "LEAN_BACKEND_EXTRA_TACTIC"
        message := s!"No open goals remain for tactic `{tactic.name}`."
      }
  | _ =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := "LEAN_BACKEND_INTERNAL"
        message := "Internal work stack expected a goal before applying a tactic."
      }

private def openGoalsFromWork (work : List WorkItem) : List EngineGoal :=
  work.foldr
    (fun item acc =>
      match item with
      | WorkItem.goal goal => goalToView goal :: acc
      | _ => acc)
    []

structure NDGoalState where
  id : String
  hypotheses : List NamedHyp
  target : Formula
  sourceLine : Nat

private def ndGoalToView (goal : NDGoalState) : EngineGoal :=
  {
    id := goal.id
    hypotheses := goal.hypotheses.map (fun hyp => s!"{hyp.name} : {renderFormula hyp.formula}")
    target := renderFormula goal.target
  }

private def parseCasesAsTwo (tactic : ParsedTactic) : Except EngineError (String × String × String) := do
  match tactic.args with
  | "at" :: hypName :: "as" :: leftName :: rightName :: _ =>
      pure (hypName, leftName, rightName)
  | _ =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := "LEAN_BACKEND_CASES"
        message := "cases requires `at <hypothesis> as <leftName> <rightName>`."
      }

private def ndLookupHyp
    (goal : NDGoalState)
    (name : String) :
    Option (List NamedHyp × NamedHyp × List NamedHyp) :=
  extractNamedHyp goal.hypotheses name

private def ndReplaceHyp
    (goal : NDGoalState)
    (before : List NamedHyp)
    (replacement : List NamedHyp)
    (after : List NamedHyp) :
    NDGoalState :=
  { goal with hypotheses := before ++ replacement ++ after }

private def ndIntroGoal (goal : NDGoalState) (tactic : ParsedTactic) :
    Except EngineError NDGoalState := do
  match goal.target with
  | .imp premise target =>
      let hypName := tactic.args.head?.getD s!"h{goal.hypotheses.length + 1}"
      if goal.hypotheses.any (fun hyp => hyp.name = hypName) then
        throw {
          line := tactic.sourceLine
          severity := 1
          code := "LEAN_BACKEND_ND_INTRO"
          message := s!"Hypothesis name `{hypName}` is already in scope."
        }
      pure {
        goal with
        id := s!"{goal.id}.body"
        hypotheses := { name := hypName, formula := premise, sourceLine := tactic.sourceLine } :: goal.hypotheses
        target := target
      }
  | _ =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := "LEAN_BACKEND_ND_INTRO"
        message := "intro applies only to implication goals."
      }

private def ndAssumptionCloses (goal : NDGoalState) (tactic : ParsedTactic) :
    Except EngineError Unit := do
  let name <-
    match tactic.args.head? with
    | some n => pure n
    | none =>
        throw {
          line := tactic.sourceLine
          severity := 1
          code := "LEAN_BACKEND_ND_ASSUMPTION"
          message := "assumption requires a hypothesis name."
        }
  match goal.hypotheses.find? (fun hyp => hyp.name = name) with
  | some hyp =>
      unless formulaMatches hyp.formula goal.target do
        throw {
          line := tactic.sourceLine
          severity := 1
          code := "LEAN_BACKEND_ND_ASSUMPTION"
          message := s!"Hypothesis `{name}` does not match the current goal."
        }
  | none =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := "LEAN_BACKEND_ND_ASSUMPTION"
        message := s!"Unknown hypothesis `{name}`."
      }

private def ndConstructorGoals (goal : NDGoalState) (tactic : ParsedTactic) :
    Except EngineError (NDGoalState × NDGoalState) := do
  match goal.target with
  | .and left right =>
      pure (
        { goal with id := s!"{goal.id}.left", target := left },
        { goal with id := s!"{goal.id}.right", target := right }
      )
  | _ =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := "LEAN_BACKEND_ND_CONSTRUCTOR"
        message := "constructor applies only to conjunction goals."
      }

private def ndOrIntroGoal (goal : NDGoalState) (tactic : ParsedTactic) (useLeft : Bool) :
    Except EngineError NDGoalState := do
  match goal.target with
  | .or left right =>
      pure { goal with id := s!"{goal.id}.{if useLeft then "left" else "right"}", target := if useLeft then left else right }
  | _ =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := if useLeft then "LEAN_BACKEND_ND_LEFT" else "LEAN_BACKEND_ND_RIGHT"
        message := s!"Tactic `{tactic.name}` applies only to disjunction goals."
      }

private def ndAndProjectionGoal (goal : NDGoalState) (tactic : ParsedTactic) (useLeft : Bool) :
    Except EngineError NDGoalState := do
  let (name, rest) <- parseAtClause tactic
  let alias := (parseAsOne rest).getD name
  match ndLookupHyp goal name with
  | some (before, hyp, after) =>
      match hyp.formula with
      | .and left right =>
          pure <| ndReplaceHyp goal before [{ name := alias, formula := if useLeft then left else right, sourceLine := tactic.sourceLine }] after
      | _ =>
          throw {
            line := tactic.sourceLine
            severity := 1
            code := if useLeft then "LEAN_BACKEND_ND_LEFT" else "LEAN_BACKEND_ND_RIGHT"
            message := s!"Tactic `{tactic.name}` with `at` applies only to conjunction hypotheses."
          }
  | none =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := if useLeft then "LEAN_BACKEND_ND_LEFT" else "LEAN_BACKEND_ND_RIGHT"
        message := s!"Unknown hypothesis `{name}`."
      }

private def ndCasesGoals (goal : NDGoalState) (tactic : ParsedTactic) :
    Except EngineError (NDGoalState × NDGoalState) := do
  let (name, leftName, rightName) <- parseCasesAsTwo tactic
  match ndLookupHyp goal name with
  | some (before, hyp, after) =>
      match hyp.formula with
      | .or left right =>
          let leftGoal :=
            ndReplaceHyp goal before [{ name := leftName, formula := left, sourceLine := tactic.sourceLine }] after
          let rightGoal :=
            ndReplaceHyp goal before [{ name := rightName, formula := right, sourceLine := tactic.sourceLine }] after
          pure ({ leftGoal with id := s!"{goal.id}.casesL" }, { rightGoal with id := s!"{goal.id}.casesR" })
      | _ =>
          throw {
            line := tactic.sourceLine
            severity := 1
            code := "LEAN_BACKEND_ND_CASES"
            message := "cases applies only to disjunction hypotheses."
          }
  | none =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := "LEAN_BACKEND_ND_CASES"
        message := s!"Unknown hypothesis `{name}`."
      }

private def ndApplyGoal (goal : NDGoalState) (tactic : ParsedTactic) :
    Except EngineError NDGoalState := do
  let name <-
    match tactic.args.head? with
    | some n => pure n
    | none =>
        throw {
          line := tactic.sourceLine
          severity := 1
          code := "LEAN_BACKEND_ND_APPLY"
          message := "apply requires a hypothesis name."
        }
  match goal.hypotheses.find? (fun hyp => hyp.name = name) with
  | some hyp =>
      match hyp.formula with
      | .imp premise conclusion =>
          if formulaMatches conclusion goal.target then
            pure { goal with id := s!"{goal.id}.apply", target := premise }
          else
            throw {
              line := tactic.sourceLine
              severity := 1
              code := "LEAN_BACKEND_ND_APPLY"
              message := s!"Hypothesis `{name}` does not conclude the current goal."
            }
      | _ =>
          throw {
            line := tactic.sourceLine
            severity := 1
            code := "LEAN_BACKEND_ND_APPLY"
            message := "apply requires an implication hypothesis."
          }
  | none =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := "LEAN_BACKEND_ND_APPLY"
        message := s!"Unknown hypothesis `{name}`."
      }

private def ndExfalsoGoal (goal : NDGoalState) : NDGoalState :=
  { goal with id := s!"{goal.id}.exfalso", target := .bot }

private def ndAbsurdCloses (goal : NDGoalState) (tactic : ParsedTactic) :
    Except EngineError Unit := do
  let name <-
    match tactic.args.head? with
    | some n => pure n
    | none =>
        throw {
          line := tactic.sourceLine
          severity := 1
          code := "LEAN_BACKEND_ND_ABSURD"
          message := "absurd requires a hypothesis name."
        }
  match goal.hypotheses.find? (fun hyp => hyp.name = name) with
  | some hyp =>
      unless formulaMatches hyp.formula .bot do
        throw {
          line := tactic.sourceLine
          severity := 1
          code := "LEAN_BACKEND_ND_ABSURD"
          message := s!"Hypothesis `{name}` is not ⊥."
        }
  | none =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := "LEAN_BACKEND_ND_ABSURD"
        message := s!"Unknown hypothesis `{name}`."
      }

private def ndByContraGoal (system : FastProofTheory.ProofTheory.Natural.System) (goal : NDGoalState) (tactic : ParsedTactic) :
    Except EngineError NDGoalState := do
  unless system.isNKp do
    throw {
      line := tactic.sourceLine
      severity := 1
      code := "LEAN_BACKEND_ND_BY_CONTRA"
      message := "by_contra is available only in NKp."
    }
  let hypName := tactic.args.head?.getD s!"h{goal.hypotheses.length + 1}"
  if goal.hypotheses.any (fun hyp => hyp.name = hypName) then
    throw {
      line := tactic.sourceLine
      severity := 1
      code := "LEAN_BACKEND_ND_BY_CONTRA"
      message := s!"Hypothesis name `{hypName}` is already in scope."
    }
  pure {
    goal with
    id := s!"{goal.id}.contra"
    hypotheses := { name := hypName, formula := .imp goal.target .bot, sourceLine := tactic.sourceLine } :: goal.hypotheses
    target := .bot
  }

private def applyNDTactic (ndSystem : FastProofTheory.ProofTheory.Natural.System) (tactic : ParsedTactic) (goals : List NDGoalState) :
    Except EngineError (List NDGoalState) := do
  match goals with
  | [] =>
      throw {
        line := tactic.sourceLine
        severity := 1
        code := "LEAN_BACKEND_EXTRA_TACTIC"
        message := s!"No open goals remain for tactic `{tactic.name}`."
      }
  | goal :: rest =>
      match tactic.name with
      | "intro" =>
          let next <- ndIntroGoal goal tactic
          pure (next :: rest)
      | "assumption" =>
          let _ <- ndAssumptionCloses goal tactic
          pure rest
      | "constructor" =>
          let (leftGoal, rightGoal) <- ndConstructorGoals goal tactic
          pure (leftGoal :: rightGoal :: rest)
      | "left" =>
          if tactic.args.any (· = "at") then
            let next <- ndAndProjectionGoal goal tactic true
            pure (next :: rest)
          else
            let next <- ndOrIntroGoal goal tactic true
            pure (next :: rest)
      | "right" =>
          if tactic.args.any (· = "at") then
            let next <- ndAndProjectionGoal goal tactic false
            pure (next :: rest)
          else
            let next <- ndOrIntroGoal goal tactic false
            pure (next :: rest)
      | "cases" =>
          let (leftGoal, rightGoal) <- ndCasesGoals goal tactic
          pure (leftGoal :: rightGoal :: rest)
      | "apply" =>
          let next <- ndApplyGoal goal tactic
          pure (next :: rest)
      | "exfalso" =>
          pure (ndExfalsoGoal goal :: rest)
      | "absurd" =>
          let _ <- ndAbsurdCloses goal tactic
          pure rest
      | "by_contra" =>
          let next <- ndByContraGoal ndSystem goal tactic
          pure (next :: rest)
      | other =>
          throw {
            line := tactic.sourceLine
            severity := 1
            code := "LEAN_BACKEND_UNSUPPORTED_TACTIC"
            message := s!"Tactic `{other}` is not implemented in the checked ND engine yet."
          }

structure NDCertGoal where
  context : List FastProofTheory.ProofTheory.Natural.Binding
  target : Formula
  finish : FastProofTheory.ProofTheory.Natural.Certificate → FastProofTheory.ProofTheory.Natural.Certificate := id

private def ndFindBinding? (ctx : List FastProofTheory.ProofTheory.Natural.Binding) (name : String) :
    Option FastProofTheory.ProofTheory.Natural.Binding :=
  ctx.find? (fun binding => binding.name = name)

private def ndReplaceBinding?
    (ctx : List FastProofTheory.ProofTheory.Natural.Binding)
    (name : String)
    (replacement : FastProofTheory.ProofTheory.Natural.Binding) :
    Option (List FastProofTheory.ProofTheory.Natural.Binding) := Id.run do
  let rec loop
      (acc : List FastProofTheory.ProofTheory.Natural.Binding)
      (rest : List FastProofTheory.ProofTheory.Natural.Binding) :
      Option (List FastProofTheory.ProofTheory.Natural.Binding) :=
    match rest with
    | [] => none
    | binding :: tail =>
        if binding.name = name then
          some (acc.reverse ++ replacement :: tail)
        else
          loop (binding :: acc) tail
  loop [] ctx

private partial def buildNDCertificate (goal : NDCertGoal) (tactics : List ParsedTactic) :
    Except EngineError (FastProofTheory.ProofTheory.Natural.Certificate × List ParsedTactic) := do
  match tactics with
  | [] =>
      throw {
        line := 0
        severity := 1
        code := "LEAN_BACKEND_ND_CERTIFICATE"
        message := "The proof ends before all goals are closed by a certificate."
      }
  | tactic :: rest =>
      match tactic.name with
      | "intro" =>
          match goal.target with
          | .imp premise body =>
              let name := tactic.args.head?.getD s!"h{goal.context.length + 1}"
              let subgoal : NDCertGoal := {
                context := { name, formula := premise } :: goal.context
                target := body
                finish := goal.finish ∘ FastProofTheory.ProofTheory.Natural.Certificate.impIntro name premise
              }
              buildNDCertificate subgoal rest
          | _ =>
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_ND_CERTIFICATE"
                message := "Cannot certify theorem: `intro` was used on a non-implication goal."
              }
      | "assumption" =>
          let name <- match tactic.args.head? with
            | some name => pure name
            | none =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_ND_CERTIFICATE"
                  message := "Cannot certify theorem: `assumption` requires a hypothesis name."
                }
          match ndFindBinding? goal.context name with
          | some binding =>
              if formulaMatches binding.formula goal.target then
                pure (goal.finish (.hyp name), rest)
              else
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_ND_CERTIFICATE"
                  message := s!"Cannot certify theorem: hypothesis `{name}` does not match the current goal."
                }
          | none =>
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_ND_CERTIFICATE"
                message := s!"Cannot certify theorem: unknown hypothesis `{name}`."
              }
      | "constructor" =>
          match goal.target with
          | .and left right =>
              let (leftCert, rest') <- buildNDCertificate { goal with target := left, finish := id } rest
              let (rightCert, rest'') <- buildNDCertificate { goal with target := right, finish := id } rest'
              pure (goal.finish (.andIntro leftCert rightCert), rest'')
          | _ =>
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_ND_CERTIFICATE"
                message := "Cannot certify theorem: `constructor` was used on a non-conjunction goal."
              }
      | "left" =>
          if tactic.args.any (· = "at") then
            let (name, restArgs) <- parseAtClause tactic
            let alias := (parseAsOne restArgs).getD name
            match ndFindBinding? goal.context name with
            | some binding =>
                match binding.formula with
                | .and leftFormula _ =>
                    match ndReplaceBinding? goal.context name { name := alias, formula := leftFormula } with
                    | some ctx =>
                        let (body, rest') <- buildNDCertificate { goal with context := ctx, finish := id } rest
                        pure (goal.finish (.andLeftAt name alias body), rest')
                    | none => throw {
                        line := tactic.sourceLine
                        severity := 1
                        code := "LEAN_BACKEND_ND_CERTIFICATE"
                        message := s!"Cannot certify theorem: unknown hypothesis `{name}`."
                      }
                | _ => throw {
                    line := tactic.sourceLine
                    severity := 1
                    code := "LEAN_BACKEND_ND_CERTIFICATE"
                    message := "Cannot certify theorem: `left at` applies only to conjunction hypotheses."
                  }
            | none => throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_ND_CERTIFICATE"
                message := s!"Cannot certify theorem: unknown hypothesis `{name}`."
              }
          else
            match goal.target with
            | .or left _ =>
                let (body, rest') <- buildNDCertificate { goal with target := left, finish := id } rest
                pure (goal.finish (.orLeft body), rest')
            | _ =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_ND_CERTIFICATE"
                  message := "Cannot certify theorem: `left` was used on a non-disjunction goal."
                }
      | "right" =>
          if tactic.args.any (· = "at") then
            let (name, restArgs) <- parseAtClause tactic
            let alias := (parseAsOne restArgs).getD name
            match ndFindBinding? goal.context name with
            | some binding =>
                match binding.formula with
                | .and _ rightFormula =>
                    match ndReplaceBinding? goal.context name { name := alias, formula := rightFormula } with
                    | some ctx =>
                        let (body, rest') <- buildNDCertificate { goal with context := ctx, finish := id } rest
                        pure (goal.finish (.andRightAt name alias body), rest')
                    | none => throw {
                        line := tactic.sourceLine
                        severity := 1
                        code := "LEAN_BACKEND_ND_CERTIFICATE"
                        message := s!"Cannot certify theorem: unknown hypothesis `{name}`."
                      }
                | _ => throw {
                    line := tactic.sourceLine
                    severity := 1
                    code := "LEAN_BACKEND_ND_CERTIFICATE"
                    message := "Cannot certify theorem: `right at` applies only to conjunction hypotheses."
                  }
            | none => throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_ND_CERTIFICATE"
                message := s!"Cannot certify theorem: unknown hypothesis `{name}`."
              }
          else
            match goal.target with
            | .or _ right =>
                let (body, rest') <- buildNDCertificate { goal with target := right, finish := id } rest
                pure (goal.finish (.orRight body), rest')
            | _ =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_ND_CERTIFICATE"
                  message := "Cannot certify theorem: `right` was used on a non-disjunction goal."
                }
      | "cases" =>
          let (name, leftName, rightName) <- parseCasesAsTwo tactic
          match ndFindBinding? goal.context name with
          | some binding =>
              match binding.formula with
              | .or leftFormula rightFormula =>
                  let (leftBody, rest') <- buildNDCertificate {
                    goal with
                    context := { name := leftName, formula := leftFormula } :: goal.context
                    finish := id
                  } rest
                  let (rightBody, rest'') <- buildNDCertificate {
                    goal with
                    context := { name := rightName, formula := rightFormula } :: goal.context
                    finish := id
                  } rest'
                  pure (
                    goal.finish
                      (.orElim
                        (.hyp name)
                        leftName leftFormula leftBody
                        rightName rightFormula rightBody),
                    rest''
                  )
              | _ =>
                  throw {
                    line := tactic.sourceLine
                    severity := 1
                    code := "LEAN_BACKEND_ND_CERTIFICATE"
                    message := "Cannot certify theorem: `cases` applies only to disjunction hypotheses."
                  }
          | none =>
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_ND_CERTIFICATE"
                message := s!"Cannot certify theorem: unknown hypothesis `{name}`."
              }
      | "apply" =>
          let name <- match tactic.args.head? with
            | some name => pure name
            | none =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_ND_CERTIFICATE"
                  message := "Cannot certify theorem: `apply` requires a hypothesis name."
                }
          match ndFindBinding? goal.context name with
          | some binding =>
              match binding.formula with
              | .imp premise conclusion =>
                  if formulaMatches conclusion goal.target then
                    let (argCert, rest') <- buildNDCertificate { goal with target := premise, finish := id } rest
                    pure (goal.finish (.impElim premise (.hyp name) argCert), rest')
                  else
                    throw {
                      line := tactic.sourceLine
                      severity := 1
                      code := "LEAN_BACKEND_ND_CERTIFICATE"
                      message := s!"Cannot certify theorem: hypothesis `{name}` does not conclude the current goal."
                    }
              | _ =>
                  throw {
                    line := tactic.sourceLine
                    severity := 1
                    code := "LEAN_BACKEND_ND_CERTIFICATE"
                    message := "Cannot certify theorem: `apply` requires an implication hypothesis."
                  }
          | none =>
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_ND_CERTIFICATE"
                message := s!"Cannot certify theorem: unknown hypothesis `{name}`."
              }
      | "exfalso" =>
          let (body, rest') <- buildNDCertificate { goal with target := .bot, finish := id } rest
          pure (goal.finish (.bottomElim body), rest')
      | "absurd" =>
          let name <- match tactic.args.head? with
            | some name => pure name
            | none =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_ND_CERTIFICATE"
                  message := "Cannot certify theorem: `absurd` requires a hypothesis name."
                }
          pure (goal.finish (.bottomElim (.hyp name)), rest)
      | "by_contra" =>
          let hypName := tactic.args.head?.getD s!"h{goal.context.length + 1}"
          let (body, rest') <- buildNDCertificate {
            context := { name := hypName, formula := .imp goal.target .bot } :: goal.context
            target := .bot
            finish := id
          } rest
          pure (goal.finish (.classical hypName goal.target body), rest')
      | other =>
          throw {
            line := tactic.sourceLine
            severity := 1
            code := "LEAN_BACKEND_ND_CERTIFICATE"
            message := s!"Cannot certify theorem: unsupported tactic `{other}`."
          }

private def certifyNDTheorem
    (ndSystem : FastProofTheory.ProofTheory.Natural.System)
    (target : Formula)
    (tactics : List ParsedTactic) :
    Except EngineError FastProofTheory.ProofTheory.Natural.CheckedCertificate := do
  let (certificate, remaining) <- buildNDCertificate { context := [], target } tactics
  unless remaining.isEmpty do
    let extraLine := remaining.head?.map (·.sourceLine) |>.getD 0
    throw {
      line := extraLine
      severity := 1
      code := "LEAN_BACKEND_ND_CERTIFICATE"
      message := "The certificate closed before all tactic lines were consumed."
    }
  match FastProofTheory.ProofTheory.Natural.checkClosedTheorem ndSystem target certificate with
  | .ok checked => pure checked
  | .error err =>
      throw {
        line := 0
        severity := 1
        code := "LEAN_BACKEND_ND_KERNEL"
        message := FastProofTheory.ProofTheory.Natural.renderKernelError err
      }

private abbrev SystemFTy := FastProofTheory.SystemF.Ty
private abbrev SystemFTm := FastProofTheory.SystemF.Tm
private abbrev SystemFTyContext := FastProofTheory.SystemF.TyContext
private abbrev SystemFContext := FastProofTheory.SystemF.Context
private abbrev SystemFHasType := FastProofTheory.SystemF.HasType

private def systemFLabel (name : String) : FastProofTheory.SystemF.Label :=
  name

private structure SystemFGoal where
  tyContext : SystemFTyContext
  context : SystemFContext
  term : SystemFTm
  target : SystemFTy

private partial def renderSystemFTy : SystemFTy → String
  | .var name => toString name
  | .arr a b => s!"({renderSystemFTy a} -> {renderSystemFTy b})"
  | .all name body => s!"forall {name}. {renderSystemFTy body}"

private partial def renderSystemFTm : SystemFTm → String
  | .var name => toString name
  | .lam name ty body => s!"(\\{name} : {renderSystemFTy ty}. {renderSystemFTm body})"
  | .app fn arg => s!"({renderSystemFTm fn} {renderSystemFTm arg})"
  | .tyLam name body => s!"(Λ{name}. {renderSystemFTm body})"
  | .tyApp fn ty => s!"({renderSystemFTm fn} [{renderSystemFTy ty}])"

private def renderSystemFTyContext (Δ : SystemFTyContext) : String :=
  if Δ.isEmpty then "·" else String.intercalate ", " (Δ.map toString)

private def renderSystemFContext (Γ : SystemFContext) : String :=
  if Γ.isEmpty then "·" else String.intercalate ", " (Γ.map (fun (name, ty) => s!"{name} : {renderSystemFTy ty}"))

private def systemFGoalToEngineGoal (goal : SystemFGoal) : EngineGoal :=
  {
    id := "systemf"
    hypotheses := [s!"Δ = {renderSystemFTyContext goal.tyContext}", s!"Γ = {renderSystemFContext goal.context}"]
    target := s!"{renderSystemFTyContext goal.tyContext} ; {renderSystemFContext goal.context} ⊢ {renderSystemFTm goal.term} : {renderSystemFTy goal.target}"
  }

inductive SystemFElabOutcome where
  | closed
  | pending (goal : SystemFGoal)

private partial def buildSystemFCertificate
    (goal : SystemFGoal)
    (tactics : List ParsedTactic) :
    Except EngineError (SystemFElabOutcome × List ParsedTactic) := do
  match tactics with
  | [] => pure (.pending goal, [])
  | tactic :: rest =>
      let handleVarLike (kind : String) : Except EngineError (SystemFElabOutcome × List ParsedTactic) := do
        let name <- match tactic.args.head? with
          | some name => pure name
          | none =>
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_SYSTEM_F"
                message := s!"Cannot certify theorem: `{kind}` requires a variable name."
              }
        match goal with
        | { term := .var termName, .. } =>
            if systemFLabel name = termName then
              if goal.context.lookup? (systemFLabel name) = some goal.target then
                pure (.closed, rest)
              else
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_SYSTEM_F"
                  message := s!"Cannot certify theorem: variable `{name}` is missing or has the wrong type."
                }
            else
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_SYSTEM_F"
                message := s!"Cannot certify theorem: `{kind}` must name the current variable `{termName}`."
              }
        | _ =>
            throw {
              line := tactic.sourceLine
              severity := 1
              code := "LEAN_BACKEND_SYSTEM_F"
              message := s!"Cannot certify theorem: `{kind}` was used on a non-variable goal."
            }
      if tactic.name = "var" then
        handleVarLike "var"
      else if tactic.name = "exact" then
        handleVarLike "exact"
      else if tactic.name = "assumption" then
        handleVarLike "assumption"
      else match tactic.name with
      | "intro" =>
          let name <- match tactic.args.head? with
            | some name => pure name
            | none =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_SYSTEM_F"
                  message := "Cannot certify theorem: `intro` requires a binder name."
                }
          match goal with
          | { term := .lam binder ty body, target := .arr premise conclusion, .. } =>
              unless systemFLabel name = binder do
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_SYSTEM_F"
                  message := s!"Cannot certify theorem: `intro` must introduce the term binder `{binder}`."
                }
              if ty = premise then
                let (outcome, remaining) <- buildSystemFCertificate {
                  tyContext := goal.tyContext
                  context := (binder, premise) :: goal.context
                  term := body
                  target := conclusion
                } rest
                match outcome with
                | SystemFElabOutcome.closed =>
                    pure (.closed, remaining)
                | SystemFElabOutcome.pending openGoal =>
                    pure (.pending openGoal, remaining)
              else
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_SYSTEM_F"
                  message := s!"Cannot certify theorem: lambda binder `{binder}` has the wrong type annotation."
                }
          | _ =>
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_SYSTEM_F"
                message := "Cannot certify theorem: `intro` was used on a non-lambda goal."
              }
      | "type_intro" =>
          let name <- match tactic.args.head? with
            | some name => pure name
            | none =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_SYSTEM_F"
                  message := "Cannot certify theorem: `type_intro` requires a type-variable name."
                }
          match goal with
          | { term := .tyLam binder body, target := .all targetBinder bodyTy, .. } =>
              unless systemFLabel name = binder do
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_SYSTEM_F"
                  message := s!"Cannot certify theorem: `type_intro` must introduce the term binder `{binder}`."
                }
              if binder = targetBinder then
                if binder ∈ goal.context.freeTyVars then
                  throw {
                    line := tactic.sourceLine
                    severity := 1
                    code := "LEAN_BACKEND_SYSTEM_F"
                    message := s!"Cannot certify theorem: type variable `{binder}` occurs free in the context."
                  }
                else
              let (outcome, remaining) <- buildSystemFCertificate {
                tyContext := binder :: goal.tyContext
                context := goal.context
                term := body
                target := bodyTy
              } rest
              match outcome with
              | SystemFElabOutcome.closed =>
                  pure (.closed, remaining)
              | SystemFElabOutcome.pending openGoal =>
                  pure (.pending openGoal, remaining)
              else
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_SYSTEM_F"
                  message := s!"Cannot certify theorem: the target type binder `{targetBinder}` must match `{binder}`."
                }
          | _ =>
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_SYSTEM_F"
                message := "Cannot certify theorem: `type_intro` was used on a non-type-lambda goal."
              }
      | "apply" =>
          let tyText := String.intercalate " " tactic.args
          if tyText.isEmpty then
            throw {
              line := tactic.sourceLine
              severity := 1
              code := "LEAN_BACKEND_SYSTEM_F"
              message := "Cannot certify theorem: `apply` requires a type argument."
            }
          match FastProofTheory.SystemF.Syntax.parseType tyText with
          | .error msg =>
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_SYSTEM_F"
                message := s!"Cannot certify theorem: invalid type argument: {msg}"
              }
          | .ok tyArg =>
              match goal with
              | { term := .app fn arg, .. } =>
                  let (outcomeFn, remainingFn) <- buildSystemFCertificate {
                    tyContext := goal.tyContext
                    context := goal.context
                    term := fn
                    target := .arr tyArg goal.target
                  } rest
                  match outcomeFn with
                  | SystemFElabOutcome.closed =>
                      let (outcomeArg, remainingArg) <- buildSystemFCertificate {
                        tyContext := goal.tyContext
                        context := goal.context
                        term := arg
                        target := tyArg
                      } remainingFn
                      match outcomeArg with
                      | SystemFElabOutcome.closed =>
                          pure (.closed, remainingArg)
                      | SystemFElabOutcome.pending openGoal =>
                          pure (.pending openGoal, remainingArg)
                  | SystemFElabOutcome.pending openGoal =>
                      pure (.pending openGoal, remainingFn)
              | _ =>
                  throw {
                    line := tactic.sourceLine
                    severity := 1
                    code := "LEAN_BACKEND_SYSTEM_F"
                    message := "Cannot certify theorem: `apply` was used on a non-application goal."
                  }
      | "type_apply" =>
          let binderText <- match tactic.args.head? with
            | some binder => pure binder
            | none =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_SYSTEM_F"
                  message := "Cannot certify theorem: `type_apply` requires a type variable name."
                }
          let tyText := String.intercalate " " (tactic.args.drop 1)
          if tyText.isEmpty then
            throw {
              line := tactic.sourceLine
              severity := 1
              code := "LEAN_BACKEND_SYSTEM_F"
              message := "Cannot certify theorem: `type_apply` requires a type argument."
            }
          match FastProofTheory.SystemF.Syntax.parseType tyText with
          | .error msg =>
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_SYSTEM_F"
                message := s!"Cannot certify theorem: invalid type argument: {msg}"
              }
          | .ok bodyTy =>
              match goal with
              | { term := .tyApp fn tyArg, .. } =>
                  let binder := systemFLabel binderText
                  match FastProofTheory.SystemF.Ty.subst? binder tyArg bodyTy with
                  | .ok instantiated =>
                      if instantiated = goal.target then
                        let (outcome, remaining) <- buildSystemFCertificate {
                          tyContext := goal.tyContext
                          context := goal.context
                          term := fn
                          target := .all binder bodyTy
                        } rest
                        match outcome with
                        | SystemFElabOutcome.closed =>
                            pure (.closed, remaining)
                        | SystemFElabOutcome.pending openGoal =>
                            pure (.pending openGoal, remaining)
                      else
                        throw {
                          line := tactic.sourceLine
                          severity := 1
                          code := "LEAN_BACKEND_SYSTEM_F"
                          message := s!"Cannot certify theorem: instantiated type `{renderSystemFTy instantiated}` does not match the current goal."
                        }
                  | .error msg =>
                      throw {
                        line := tactic.sourceLine
                        severity := 1
                        code := "LEAN_BACKEND_SYSTEM_F"
                        message := s!"Cannot certify theorem: invalid type application: {msg}"
                      }
              | _ =>
                  throw {
                    line := tactic.sourceLine
                    severity := 1
                    code := "LEAN_BACKEND_SYSTEM_F"
                    message := "Cannot certify theorem: `type_apply` was used on a non-type-application goal."
                  }
      | other =>
          throw {
            line := tactic.sourceLine
            severity := 1
            code := "LEAN_BACKEND_SYSTEM_F"
            message := s!"Cannot certify theorem: unsupported tactic `{other}`."
          }

private def certifySystemFTheorem
    (goal : SystemFGoal)
    (tactics : List ParsedTactic) :
    Except EngineError (SystemFElabOutcome × List ParsedTactic) := do
  buildSystemFCertificate goal tactics

private def evaluateNDTheorem (thm : ParsedTheorem) :
    EngineState × List EngineError := Id.run do
  match thm.headerError? with
  | some msg =>
      let err := {
        line := thm.firstLine
        severity := 1
        code := "LEAN_BACKEND_THEOREM_HEADER"
        message := msg
      }
      return ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
  | none =>
      match thm.declaredSystem? with
      | none =>
          let err := {
            line := thm.firstLine
            severity := 1
            code := "LEAN_BACKEND_UNSUPPORTED_SYSTEM"
            message := "Every theorem must declare a complete supported logic specification."
          }
          return ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
      | some declaredSystem =>
          match declaredSystem.toNDSystem? with
          | none =>
            let err := {
              line := thm.firstLine
              severity := 1
              code := "LEAN_BACKEND_UNSUPPORTED_SYSTEM"
              message := "Only `NJp`, `NJp with IMP`, and `NKp` are accepted by the checked ND engine."
            }
            ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
          | some ndSystem =>
            let goalEntries := thm.statement?.map List.singleton |>.getD []
            let goalsE := goalEntries.map (fun entry =>
              match parseStatementGoal declaredSystem entry with
              | Except.ok f => Except.ok (entry.line, f)
              | Except.error e => Except.error e)
            let tactics := thm.tactics.map parseTacticLine
            match goalsE.findSome? (fun r => match r with | Except.error e => some e | _ => none) with
            | some err =>
                ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
            | none =>
                let goals := goalsE.filterMap (fun | Except.ok g => some g | Except.error _ => none)
                match goals.find? (fun (_, target) => !declaredSystem.allowsFormula target) with
                | some (line, _) =>
                    let err := {
                      line := line
                      severity := 1
                      code := "LEAN_BACKEND_ND_FORMULA"
                      message := s!"The theorem statement is not in the language of {declaredSystem.displayName}."
                    }
                    ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
                | none =>
                let rec buildInitialGoals (remaining : List (Nat × Formula)) (idx : Nat) : List NDGoalState :=
                  match remaining with
                  | [] => []
                  | (line, target) :: rest =>
                      { id := s!"{thm.name}:g{idx}", hypotheses := [], target, sourceLine := line } :: buildInitialGoals rest (idx + 1)
                let initialGoals : List NDGoalState := buildInitialGoals goals 1
                let rec runTactics (stateGoals : List NDGoalState) (remaining : List ParsedTactic) :
                    List NDGoalState × Option EngineError :=
                  match remaining with
                  | [] => (stateGoals, none)
                  | tactic :: rest =>
                      match applyNDTactic ndSystem tactic stateGoals with
                      | .ok next => runTactics next rest
                      | .error err => (stateGoals, some err)
                let (openGoalsState, tacticErr?) := runTactics initialGoals tactics
                let openGoals := openGoalsState.map ndGoalToView
                match tacticErr? with
                | some err =>
                    ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := openGoals, status := err.message, verified := false }, [err])
                | none =>
                    let verified := openGoals.isEmpty
                    if verified then
                      match goals with
                      | [(_, target)] =>
                          match certifyNDTheorem ndSystem target tactics with
                          | .ok _ =>
                              let status := s!"Theorem {thm.name} verified in system {declaredSystem.displayName}."
                              ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := openGoals, status, verified := true }, [])
                          | .error err =>
                              ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := openGoals, status := err.message, verified := false }, [err])
                      | _ =>
                          let err := {
                            line := thm.firstLine
                            severity := 1
                            code := "LEAN_BACKEND_ND_CERTIFICATE"
                            message := "Natural-deduction certificate checking expects exactly one theorem statement goal."
                          }
                          ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := openGoals, status := err.message, verified := false }, [err])
                    else
                      let status := s!"Theorem {thm.name} in system {declaredSystem.displayName}. Open goals: {openGoals.length}."
                      let warnings := [{
                        line := goalEntries.head?.map (·.line) |>.getD thm.firstLine
                        severity := 1
                        code := "LEAN_BACKEND_OPEN_GOALS"
                        message := s!"Theorem `{thm.name}` contains open goals and is not checked as complete."
                      }]
                      ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := openGoals, status, verified := false }, warnings)

private def evaluateLinearTheorem (thm : ParsedTheorem) :
    EngineState × List EngineError := Id.run do
  match thm.headerError? with
  | some msg =>
      let err := {
        line := thm.firstLine
        severity := 1
        code := "LEAN_BACKEND_THEOREM_HEADER"
        message := msg
      }
      return ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
  | none =>
      match thm.declaredSystem? with
      | none =>
          let err := {
            line := thm.firstLine
            severity := 1
            code := "LEAN_BACKEND_UNSUPPORTED_SYSTEM"
            message := "Every theorem must declare a complete supported logic specification."
          }
          return ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
      | some declaredSystem =>
          match declaredSystem with
          | .gentzen (.linearLogic logic) =>
              let hypsE := thm.hypotheses.map (parseHypothesisLine declaredSystem)
              let goalEntries :=
                if thm.goals.isEmpty then
                  thm.statement?.map List.singleton |>.getD []
                else
                  thm.goals
              let goalsE := goalEntries.map (fun entry =>
                match parseGoalLine declaredSystem entry with
                | Except.ok f => Except.ok (entry.line, f)
                | Except.error e => Except.error e)
              let goalsE :=
                if thm.goals.isEmpty then
                  goalEntries.map (fun entry =>
                    match parseStatementGoal declaredSystem entry with
                    | Except.ok f => Except.ok (entry.line, f)
                    | Except.error e => Except.error e)
                else goalsE
              let tactics := thm.tactics.map parseTacticLine
              match hypsE.findSome? (fun r => match r with | Except.error e => some e | _ => none) with
              | some err =>
                  ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
              | none =>
                  match goalsE.findSome? (fun r => match r with | Except.error e => some e | _ => none) with
                  | some err =>
                      ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
                  | none =>
                      let hyps := hypsE.filterMap (fun | Except.ok h => some h | Except.error _ => none)
                      let goals := goalsE.filterMap (fun | Except.ok g => some g | Except.error _ => none)
                      let initial : ExecutionState := { work := initialGoals thm hyps goals, solved := [], nextGoalIndex := goals.length + 1 }
                      let rec runTactics (state : ExecutionState) (remaining : List ParsedTactic) :
                          ExecutionState × Option EngineError :=
                        match remaining with
                        | [] => (state, none)
                        | tactic :: rest =>
                            match applyTactic logic tactic state with
                            | Except.ok next => runTactics next rest
                            | Except.error err => (state, some err)
                      let (preFinal, tacticErr?) := runTactics initial tactics
                      match tacticErr? with
                      | some err =>
                          let openGoals := openGoalsFromWork preFinal.work
                          ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := openGoals, status := err.message, verified := false }, [err])
                      | none =>
                          match normalize logic preFinal with
                          | Except.error err =>
                              let openGoals := openGoalsFromWork preFinal.work
                              ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := openGoals, status := err.message, verified := false }, [err])
                          | Except.ok st =>
                              let openGoals := openGoalsFromWork st.work
                              let verified := openGoals.isEmpty
                              let status :=
                                if verified then
                                  s!"Theorem {thm.name} verified in system {declaredSystem.displayName}."
                                else
                                  s!"Theorem {thm.name} in system {declaredSystem.displayName}. Open goals: {openGoals.length}."
                              let warnings :=
                                if verified then
                                  []
                                else
                                  [{
                                    line := goalEntries.head?.map (·.line) |>.getD thm.firstLine
                                    severity := 1
                                    code := "LEAN_BACKEND_OPEN_GOALS"
                                    message := s!"Theorem `{thm.name}` contains open goals and is not checked as complete."
                                  }]
                              ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := openGoals, status, verified }, warnings)
          | _ =>
            let err := {
              line := thm.firstLine
              severity := 1
              code := "LEAN_BACKEND_UNSUPPORTED_SYSTEM"
              message := "Accepted declarations are `LL in GENTZEN with LL` and `LL! in GENTZEN with LL!`."
            }
            return ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
              -- linear branch handled above

private def evaluateSystemFTheorem (thm : ParsedTheorem) :
    EngineState × List EngineError := Id.run do
  match thm.headerError? with
  | some msg =>
      let err := {
        line := thm.firstLine
        severity := 1
        code := "LEAN_BACKEND_THEOREM_HEADER"
        message := msg
      }
      return ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
  | none =>
      match thm.declaredSystem? with
      | none =>
          let err := {
            line := thm.firstLine
            severity := 1
            code := "LEAN_BACKEND_UNSUPPORTED_SYSTEM"
            message := "Every theorem must declare a complete supported logic specification."
          }
          return ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
      | some .systemF =>
            match thm.statement? with
            | none =>
                let err := {
                  line := thm.firstLine
                  severity := 1
                  code := "LEAN_BACKEND_SYSTEM_F"
                  message := "System F theorems must declare a `term has_type type` judgment in the header."
                }
                ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
            | some statement =>
                match FastProofTheory.SystemF.Syntax.parseJudgment statement.text with
                | .error msg =>
                    let err := {
                      line := statement.line
                      severity := 1
                      code := "LEAN_BACKEND_SYSTEM_F"
                      message := s!"Invalid System F judgment: {msg}"
                    }
                    ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
                | .ok judgment =>
                    let tactics := thm.tactics.map parseTacticLine
                    let goal : SystemFGoal := {
                      tyContext := []
                      context := []
                      term := judgment.term
                      target := judgment.ty
                    }
                    match certifySystemFTheorem goal tactics with
                    | .error err =>
                        let diag := {
                          line := tactics.head?.map (·.sourceLine) |>.getD statement.line
                          severity := 1
                          code := "LEAN_BACKEND_SYSTEM_F"
                          message := err.message
                        }
                        ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := diag.message, verified := false }, [diag])
                    | .ok (.pending openGoal, remaining) =>
                        unless remaining.isEmpty do
                          let extraLine := remaining.head?.map (·.sourceLine) |>.getD statement.line
                          let err := {
                            line := extraLine
                            severity := 1
                            code := "LEAN_BACKEND_SYSTEM_F"
                            message := "The proof ended before all tactic lines were consumed."
                          }
                          return ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
                        let goals := [systemFGoalToEngineGoal openGoal]
                        ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals, status := "Open goals.", verified := false }, [])
                    | .ok (.closed, remaining) =>
                        unless remaining.isEmpty do
                          let extraLine := remaining.head?.map (·.sourceLine) |>.getD statement.line
                          let err := {
                            line := extraLine
                            severity := 1
                            code := "LEAN_BACKEND_SYSTEM_F"
                            message := "The proof ended before all tactic lines were consumed."
                          }
                          return ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
                        let status := s!"Theorem {thm.name} verified in system SYSTEM_F."
                        ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status, verified := true }, [])
      | some _ =>
          let err := {
            line := thm.firstLine
            severity := 1
            code := "LEAN_BACKEND_UNSUPPORTED_SYSTEM"
            message := "Only `SYSTEM_F in ND` is accepted by the System F natural-deduction checker."
          }
          ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])

private def evaluateTheorem (thm : ParsedTheorem) :
    EngineState × List EngineError :=
  match thm.declaredSystem? with
  | some declaredSystem =>
      if declaredSystem.isLinearGentzen && declaredSystem.hasValidConfiguration then
        evaluateLinearTheorem thm
      else if declaredSystem.isSystemF && declaredSystem.hasValidConfiguration then
        evaluateSystemFTheorem thm
      else if declaredSystem.toNDSystem?.isSome && declaredSystem.hasValidConfiguration then
        evaluateNDTheorem thm
      else
        let err := {
          line := thm.firstLine
          severity := 1
          code := "LEAN_BACKEND_UNSUPPORTED_SYSTEM"
          message := s!"System `{thm.systemText}` is not supported by the checked engines."
        }
        ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
  | none =>
      let err := {
        line := thm.firstLine
        severity := 1
        code := "LEAN_BACKEND_UNSUPPORTED_SYSTEM"
        message := "Every theorem must declare a complete supported logic specification."
      }
      ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])

def evaluate (snapshot : Snapshot) : EngineState :=
  match snapshot.theorem? with
  | none =>
      { snapshot, goals := [], status := "No active theorem." }
  | some thm =>
      let (state, _) := evaluateTheorem thm
      { state with snapshot := snapshot }

private def theoremFailureDiagnostic (thm : ParsedTheorem) (errors : List EngineError) : List EngineError :=
  match errors.find? (fun err => err.severity = 1) with
  | none => []
  | some err =>
      [{
        line := thm.firstLine
        severity := 1
        code := "LEAN_BACKEND_THEOREM_FAILED"
        message := s!"Theorem `{thm.name}` failed: {err.message}"
      }]

def currentGoals (snapshot : Snapshot) : List EngineGoal :=
  (evaluate snapshot).goals

def diagnosticsForSnapshot (snapshot : Snapshot) : List EngineError :=
  match snapshot.theorem? with
  | none => []
  | some thm =>
      let (_, diags) := evaluateTheorem thm
      diags ++ theoremFailureDiagnostic thm diags

def diagnosticsForTheorems (theorems : List ParsedTheorem) : List EngineError :=
  let rec loop (remaining : List ParsedTheorem) : List EngineError :=
    match remaining with
    | [] => []
    | thm :: rest =>
        let (_, diags) := evaluateTheorem thm
        diags ++ theoremFailureDiagnostic thm diags ++ loop rest
  loop theorems

def theoremStatusesForTheorems (theorems : List ParsedTheorem) : List TheoremStatus :=
  theorems.map fun thm =>
    let (state, _) := evaluateTheorem thm
    { name := thm.name, line := thm.firstLine, verified := state.verified }

end FastProofTheory.Linear
