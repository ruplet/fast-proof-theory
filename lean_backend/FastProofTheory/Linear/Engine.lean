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
  | finishDerived1 (goal : GoalState) (name : String)
  | finishDerived2 (goal : GoalState) (name : String)

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
                          some "Declare the proof style explicitly in the header, for example `using LL in GENTZEN`."
                        else if not (isGentzenProfileText finalText) then
                          some "Only sequent-calculus linear logic is supported right now. Use `using LL in GENTZEN`."
                        else
                          none
                      some (name, finalText, finalProfile, some statementText, headerError?)
                  | Except.error _ =>
                      let fallbackText := if profileText.isEmpty then "LL" else profileText
                      let headerError? :=
                        if profileText.isEmpty then
                          some "Declare the proof style explicitly in the header, for example `using LL in GENTZEN`."
                        else if not (isGentzenProfileText fallbackText) then
                          some "Only sequent-calculus linear logic is supported right now. Use `using LL in GENTZEN`."
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
  | WorkItem.finishDerived1 goal name :: rest =>
      match state.solved with
      | body :: solvedRest =>
          let checked : CheckedCertificate := {
            profile := profile
            goal := goalToKernel goal
            certificate := .derived name [body.certificate]
            summary := s!"Checked derived rule {name}."
          }
          normalize profile { state with work := rest, solved := checked :: solvedRest }
      | _ =>
          throw {
            line := goal.sourceLine
            severity := 1
            code := "LEAN_BACKEND_INTERNAL"
            message := s!"Derived frame `{name}` is missing a solved subproof."
          }
  | WorkItem.finishDerived2 goal name :: rest =>
      match state.solved with
      | right :: left :: solvedRest =>
          let checked : CheckedCertificate := {
            profile := profile
            goal := goalToKernel goal
            certificate := .derived name [left.certificate, right.certificate]
            summary := s!"Checked derived rule {name}."
          }
          normalize profile { state with work := rest, solved := checked :: solvedRest }
      | _ =>
          throw {
            line := goal.sourceLine
            severity := 1
            code := "LEAN_BACKEND_INTERNAL"
            message := s!"Derived frame `{name}` is missing solved subproofs."
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
          let nextGoal <- rewriteWithTactic goal tactic true
          pure {
            state with
            work := WorkItem.goal { nextGoal with id := s!"{goal.id}.lleft" } :: WorkItem.finishDerived1 goal "lleft" :: rest
          }
      | "lright" =>
          let nextGoal <- rewriteWithTactic goal tactic false
          pure {
            state with
            work := WorkItem.goal { nextGoal with id := s!"{goal.id}.lright" } :: WorkItem.finishDerived1 goal "lright" :: rest
          }
      | "ltensor" =>
          let nextGoal <- tensorLeftGoal goal tactic
          pure {
            state with
            work := WorkItem.goal { nextGoal with id := s!"{goal.id}.ltensor" } :: WorkItem.finishDerived1 goal "ltensor" :: rest
          }
      | "lplus" =>
          let (leftGoal, rightGoal) <- plusLeftGoals goal tactic
          pure {
            state with
            work := WorkItem.goal leftGoal :: WorkItem.goal rightGoal :: WorkItem.finishDerived2 goal "lplus" :: rest
          }
      | "llolli" =>
          let (premiseGoal, consequenceGoal) <- lolliLeftGoals goal tactic
          pure {
            state with
            work := WorkItem.goal premiseGoal :: WorkItem.goal consequenceGoal :: WorkItem.finishDerived2 goal "llolli" :: rest
          }
      | "lbang" =>
          let nextGoal <- bangLeftGoal goal tactic
          pure {
            state with
            work := WorkItem.goal { nextGoal with id := s!"{goal.id}.lbang" } :: WorkItem.finishDerived1 goal "lbang" :: rest
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

def evaluate (snapshot : Snapshot) : EngineState :=
  match snapshot.theorem? with
  | none =>
      { snapshot, goals := [], status := "No active theorem." }
  | some thm =>
      let (state, _) := evaluateLinearTheorem thm
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
      let (_, diags) := evaluateLinearTheorem thm
      diags ++ theoremFailureDiagnostic thm diags

def diagnosticsForTheorems (theorems : List ParsedTheorem) : List EngineError :=
  let rec loop (remaining : List ParsedTheorem) : List EngineError :=
    match remaining with
    | [] => []
    | thm :: rest =>
        let (_, diags) := evaluateLinearTheorem thm
        diags ++ theoremFailureDiagnostic thm diags ++ loop rest
  loop theorems

def theoremStatusesForTheorems (theorems : List ParsedTheorem) : List TheoremStatus :=
  theorems.map fun thm =>
    let (state, _) := evaluateLinearTheorem thm
    { name := thm.name, line := thm.firstLine, verified := state.verified }

end FastProofTheory.Linear
