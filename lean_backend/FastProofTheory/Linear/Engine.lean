import FastProofTheory.Linear.Profile
import FastProofTheory.Linear.Kernel
import FastProofTheory.Linear.Syntax

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
  profileText : String := "LL"
  profile? : Option Profile := some .withoutExponentials
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

inductive Command where
  | requestState (cursorLine : Nat)
  | applyTactic (goalId : String) (name : String) (args : List String := [])
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
    "absurd", "by_contra",
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

private def inferProfileText (profile : Profile) : String :=
  profile.displayName

private def isGentzenProfileText (text : String) : Bool :=
  let upper := text.toUpper
  upper.contains "GENTZEN"

def theoremHeader? (line : String) : Option (String × String × Option Profile × Option String × Option String) :=
  let trimmed := trimLine line
  let shortHeader? :=
    if trimmed.contains ':' then
      none
    else
      match splitWords trimmed with
      | "theorem" :: [] =>
          some ("theorem", "LL", some .withoutExponentials, none, some "Theorem statement must be written explicitly in the header.")
      | "theorem" :: name :: [] =>
          some (name, "LL", some .withoutExponentials, none, some "Theorem statement must be written explicitly in the header.")
      | "theorem" :: name :: "using" :: profileTokens =>
          some (name, String.intercalate " " profileTokens, parseSupportedProfileTokens? profileTokens, none, some "Theorem statement must be written explicitly in the header.")
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
                some (name, "LL", some Profile.withoutExponentials, none, some "Theorem binders are not supported yet. Write all arguments explicitly in the theorem statement.")
              else
                match splitAtTopLevelColon afterName with
              | none => none
              | some (beforeColon, afterColon) =>
                  let beforeTokens := splitWords (trimLine beforeColon)
                  let (profileText, profile?) :=
                    match beforeTokens with
                    | "using" :: tokens =>
                        let txt := String.intercalate " " tokens
                        (txt, parseSupportedProfileTokens? tokens)
                    | _ => ("", none)
                  let statementText := stripBySuffix afterColon
                  match parseTheoremStatement statementText with
                  | Except.ok formula =>
                      let finalProfile := profile?.orElse (fun _ => some (inferProfileForFormula formula))
                      let finalText := if profileText.isEmpty then inferProfileText finalProfile.get! else profileText
                      let headerError? :=
                        if profileText.isEmpty then
                          some "Declare the proof style explicitly in the header, for example `using LL in GENTZEN` or `using IPC in ND`."
                        else
                          none
                      some (name, finalText, finalProfile, some statementText, headerError?)
                  | Except.error _ =>
                      let fallbackText := if profileText.isEmpty then "LL" else profileText
                      let headerError? :=
                        if profileText.isEmpty then
                          some "Declare the proof style explicitly in the header, for example `using LL in GENTZEN` or `using IPC in ND`."
                        else
                          none
                      some (name, fallbackText, profile?.orElse (fun _ => some Profile.withoutExponentials), some statementText, headerError?)

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
          | some (name, profileText, profile?, statementText?, headerError?) =>
              let theorems :=
                match current? with
                | some current => theorems ++ [current]
                | none => theorems
              let current : ParsedTheorem := {
                name := name
                profileText := profileText
                profile? := profile?
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

private def parseHypothesisLine (entry : NumberedText) : Except EngineError NamedHyp := do
  let trimmed := trimLine entry.text
  let after := trimLine (String.ofList (trimmed.toList.drop 3))
  let parts := after.splitOn ":"
  match parts with
  | [lhs, rhs] =>
      let name := trimLine lhs
      let formulaText := trimLine rhs
      match parseFormula formulaText with
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

private def parseGoalLine (entry : NumberedText) : Except EngineError Formula := do
  let trimmed := trimLine entry.text
  let formulaText := trimLine (String.ofList (trimmed.toList.drop 4))
  match parseFormula formulaText with
  | .ok formula => pure formula
  | .error err =>
      throw {
        line := entry.line
        severity := 1
        code := "LEAN_BACKEND_FORMULA"
        message := s!"Invalid goal formula `{formulaText}`: {err}"
      }

private def parseStatementGoal (entry : NumberedText) : Except EngineError Formula := do
  match parseTheoremStatement entry.text with
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
  renderFormula a = renderFormula b

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

private partial def normalize (profile : Profile) (state : ExecutionState) :
    Except EngineError ExecutionState := do
  match state.work with
  | WorkItem.finishTensor goal split :: rest =>
      match state.solved with
      | right :: left :: solvedRest =>
          let certificate := Certificate.tensorIntro split left.certificate right.certificate
          match checkCertificate profile (goalToKernel goal) certificate with
          | .ok checked =>
              normalize profile { state with work := rest, solved := checked :: solvedRest }
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
          match checkCertificate profile (goalToKernel goal) certificate with
          | .ok checked =>
              normalize profile { state with work := rest, solved := checked :: solvedRest }
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
          match checkCertificate profile (goalToKernel goal) certificate with
          | .ok checked =>
              normalize profile { state with work := rest, solved := checked :: solvedRest }
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
          match checkCertificate profile (goalToKernel goal) certificate with
          | .ok checked =>
              normalize profile { state with work := rest, solved := checked :: solvedRest }
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
          match checkCertificate profile (goalToKernel goal) certificate with
          | .ok checked =>
              normalize profile { state with work := rest, solved := checked :: solvedRest }
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
          match checkCertificate profile (goalToKernel goal) certificate with
          | .ok checked =>
              normalize profile { state with work := rest, solved := checked :: solvedRest }
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
          match checkCertificate profile (goalToKernel goal) certificate with
          | .ok checked =>
              normalize profile { state with work := rest, solved := checked :: solvedRest }
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
          match checkCertificate profile (goalToKernel goal) certificate with
          | .ok checked =>
              normalize profile { state with work := rest, solved := checked :: solvedRest }
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
          match checkCertificate profile (goalToKernel goal) certificate with
          | .ok checked =>
              normalize profile { state with work := rest, solved := checked :: solvedRest }
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
          match checkCertificate profile (goalToKernel goal) certificate with
          | .ok checked =>
              normalize profile { state with work := rest, solved := checked :: solvedRest }
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
          match checkCertificate profile (goalToKernel goal) certificate with
          | .ok checked =>
              normalize profile { state with work := rest, solved := checked :: solvedRest }
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
          match checkCertificate profile (goalToKernel goal) certificate with
          | .ok checked =>
              normalize profile { state with work := rest, solved := checked :: solvedRest }
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

private def applyTactic (profile : Profile) (tactic : ParsedTactic) (state : ExecutionState) :
    Except EngineError ExecutionState := do
  let state <- normalize profile state
  match state.work with
  | WorkItem.goal goal :: rest =>
      match tactic.name with
      | "ax" =>
          let cert <- resolveAxiomCertificate goal tactic.args
          match checkCertificate profile (goalToKernel goal) cert with
          | .ok checked => normalize profile { state with work := rest, solved := checked :: state.solved }
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

private partial def ndFormulaAllowed : Formula → Bool
  | .atom _ => true
  | .imp a b => ndFormulaAllowed a && ndFormulaAllowed b
  | .and a b => ndFormulaAllowed a && ndFormulaAllowed b
  | .or a b => ndFormulaAllowed a && ndFormulaAllowed b
  | .bot => true
  | .bottom => true
  | _ => false

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

private def ndByContraGoal (profile : Profile) (goal : NDGoalState) (tactic : ParsedTactic) :
    Except EngineError NDGoalState := do
  unless profile.logic = .cpc do
    throw {
      line := tactic.sourceLine
      severity := 1
      code := "LEAN_BACKEND_ND_BY_CONTRA"
      message := "by_contra is available only in CPC."
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

private def applyNDTactic (profile : Profile) (tactic : ParsedTactic) (goals : List NDGoalState) :
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
          let next <- ndByContraGoal profile goal tactic
          pure (next :: rest)
      | other =>
          throw {
            line := tactic.sourceLine
            severity := 1
            code := "LEAN_BACKEND_UNSUPPORTED_TACTIC"
            message := s!"Tactic `{other}` is not implemented in the checked ND engine yet."
          }

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
      match thm.profile? with
      | none =>
          let err := {
            line := thm.firstLine
            severity := 1
            code := "LEAN_BACKEND_UNSUPPORTED_PROFILE"
            message := s!"Profile `{thm.profileText}` is not supported by the checked ND engine."
          }
          return ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
      | some profile =>
          if !(profile.isNaturalDeduction && (profile.logic = .ipc || profile.logic = .cpc)) then
            let err := {
              line := thm.firstLine
              severity := 1
              code := "LEAN_BACKEND_UNSUPPORTED_PROFILE"
              message := "Only `IPC in ND` and `CPC in ND` are supported by the checked ND engine."
            }
            ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
          else
            let goalEntries := thm.statement?.map List.singleton |>.getD []
            let goalsE := goalEntries.map (fun entry =>
              match parseStatementGoal entry with
              | Except.ok f => Except.ok (entry.line, f)
              | Except.error e => Except.error e)
            let tactics := thm.tactics.map parseTacticLine
            match goalsE.findSome? (fun r => match r with | Except.error e => some e | _ => none) with
            | some err =>
                ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
            | none =>
                let goals := goalsE.filterMap (fun | Except.ok g => some g | Except.error _ => none)
                match goals.find? (fun (_, target) => !ndFormulaAllowed target) with
                | some (line, _) =>
                    let err := {
                      line := line
                      severity := 1
                      code := "LEAN_BACKEND_ND_FORMULA"
                      message := "The checked ND engine currently supports only atoms, ∧, ∨, ⟶, and ⊥."
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
                      match applyNDTactic profile tactic stateGoals with
                      | .ok next => runTactics next rest
                      | .error err => (stateGoals, some err)
                let (openGoalsState, tacticErr?) := runTactics initialGoals tactics
                let openGoals := openGoalsState.map ndGoalToView
                match tacticErr? with
                | some err =>
                    ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := openGoals, status := err.message, verified := false }, [err])
                | none =>
                    let verified := openGoals.isEmpty
                    let status :=
                      if verified then
                        s!"Theorem {thm.name} verified in profile {profile.displayName}."
                      else
                        s!"Theorem {thm.name} in profile {profile.displayName}. Open goals: {openGoals.length}."
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
      match thm.profile? with
  | none =>
      let err := {
        line := thm.firstLine
        severity := 1
        code := "LEAN_BACKEND_UNSUPPORTED_PROFILE"
        message := s!"Profile `{thm.profileText}` is not supported by the checked linear engine."
      }
      return ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
  | some profile =>
      let hypsE := thm.hypotheses.map parseHypothesisLine
      let goalEntries :=
        if thm.goals.isEmpty then
          thm.statement?.map List.singleton |>.getD []
        else
          thm.goals
      let goalsE := goalEntries.map (fun entry =>
        match parseGoalLine entry with
        | Except.ok f => Except.ok (entry.line, f)
        | Except.error e => Except.error e)
      let goalsE :=
        if thm.goals.isEmpty then
          goalEntries.map (fun entry =>
            match parseStatementGoal entry with
            | Except.ok f => Except.ok (entry.line, f)
            | Except.error e => Except.error e)
        else goalsE
      let tactics := thm.tactics.map parseTacticLine
      match hypsE.findSome? (fun r => match r with | Except.error e => some e | _ => none) with
      | some err => ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
      | none =>
          match goalsE.findSome? (fun r => match r with | Except.error e => some e | _ => none) with
          | some err => ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
          | none =>
              let hyps := hypsE.filterMap (fun | Except.ok h => some h | Except.error _ => none)
              let goals := goalsE.filterMap (fun | Except.ok g => some g | Except.error _ => none)
              let initial : ExecutionState := { work := initialGoals thm hyps goals, solved := [], nextGoalIndex := goals.length + 1 }
              let rec runTactics (state : ExecutionState) (remaining : List ParsedTactic) :
                  ExecutionState × Option EngineError :=
                match remaining with
                | [] => (state, none)
                | tactic :: rest =>
                    match applyTactic profile tactic state with
                    | Except.ok next => runTactics next rest
                    | Except.error err => (state, some err)
              let (preFinal, tacticErr?) := runTactics initial tactics
              match tacticErr? with
              | some err =>
                  let openGoals := openGoalsFromWork preFinal.work
                  ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := openGoals, status := err.message, verified := false }, [err])
              | none =>
                  match normalize profile preFinal with
                  | Except.error err =>
                      let openGoals := openGoalsFromWork preFinal.work
                      ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := openGoals, status := err.message, verified := false }, [err])
                  | Except.ok st =>
                      let openGoals := openGoalsFromWork st.work
                      let verified := openGoals.isEmpty
                      let status :=
                        if verified then
                          s!"Theorem {thm.name} verified in profile {profile.displayName}."
                        else
                          s!"Theorem {thm.name} in profile {profile.displayName}. Open goals: {openGoals.length}."
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

private def evaluateTheorem (thm : ParsedTheorem) :
    EngineState × List EngineError :=
  match thm.profile? with
  | some profile =>
      if profile.isLinearGentzen then
        evaluateLinearTheorem thm
      else if profile.isNaturalDeduction then
        evaluateNDTheorem thm
      else
        let err := {
          line := thm.firstLine
          severity := 1
          code := "LEAN_BACKEND_UNSUPPORTED_PROFILE"
          message := s!"Profile `{thm.profileText}` is not supported by the checked engines."
        }
        ({ snapshot := { theorem? := some thm, sourceLines := [] }, goals := [], status := err.message, verified := false }, [err])
  | none =>
      evaluateLinearTheorem thm

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
