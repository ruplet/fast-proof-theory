import FastProofTheory.Linear.Engine

namespace FastProofTheory.Linear.Export

open FastProofTheory.Linear
open FastProofTheory.Linear.Syntax
open Rules

structure Binding where
  name : String
  formula : Formula

inductive Proof where
  | hyp (name : String)
  | impIntro (name : String) (premise : Formula) (body : Proof)
  | impElim (fnProof : Proof) (argProof : Proof)
  | andIntro (left right : Proof)
  | orLeft (proof : Proof)
  | orRight (proof : Proof)
  | orElim (scrutinee : Proof) (leftName : String) (leftFormula : Formula)
      (leftBody : Proof) (rightName : String) (rightFormula : Formula) (rightBody : Proof)
  | bottomElim (proof : Proof)

structure Goal where
  context : List Binding
  target : Formula
  finish : Proof → Proof := id

private def findBinding? (ctx : List Binding) (name : String) : Option Binding :=
  ctx.find? (fun binding => binding.name = name)

private def replaceBinding
    (ctx : List Binding)
    (name : String)
    (replacement : Binding) : Option (List Binding) := Id.run do
  let rec loop (acc : List Binding) (rest : List Binding) : Option (List Binding) :=
    match rest with
    | [] => none
    | binding :: tail =>
        if binding.name = name then
          some (acc.reverse ++ replacement :: tail)
        else
          loop (binding :: acc) tail
  loop [] ctx

private def parseTacticLine (entry : NumberedText) : ParsedTactic :=
  let trimmed := trimLine entry.text
  let words := splitWords trimmed
  match words with
  | "tactic" :: name :: args => { name, args, sourceLine := entry.line }
  | name :: args => { name, args, sourceLine := entry.line }
  | [] => { name := "", args := [], sourceLine := entry.line }

private def parseStatementGoal (system : DeclaredSystem) (entry : NumberedText) : Except EngineError Formula := do
  match parseTheoremStatement system entry.text with
  | .ok formula => pure formula
  | .error err =>
      throw {
        line := entry.line
        severity := 1
        code := "LEAN_BACKEND_THEOREM"
        message := s!"Invalid theorem statement `{entry.text}`: {err}"
      }

private def parseAtClause (tactic : ParsedTactic) : Except EngineError (String × List String) := do
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

private def parseAsTwo (rest : List String) : Option (String × String) :=
  match rest with
  | "as" :: left :: right :: _ => some (left, right)
  | _ => none

partial def buildProof (goal : Goal) (tactics : List ParsedTactic) :
    Except EngineError (Proof × List ParsedTactic) := do
  match tactics with
  | [] =>
      throw {
        line := 0
        severity := 1
        code := "LEAN_BACKEND_EXPORT"
        message := "The proof ends before all goals are closed."
      }
  | tactic :: rest =>
      match tactic.name with
      | "intro" =>
          match goal.target with
          | .imp premise body =>
              let name := tactic.args.head?.getD s!"h{goal.context.length + 1}"
              if goal.context.any (fun binding => binding.name = name) then
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_EXPORT"
                  message := s!"Cannot export theorem: hypothesis name `{name}` is already in scope."
                }
              let subgoal : Goal := {
                context := { name, formula := premise } :: goal.context
                target := body
                finish := goal.finish ∘ Proof.impIntro name premise
              }
              buildProof subgoal rest
          | _ =>
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_EXPORT"
                message := "Cannot export theorem: `intro` was used on a non-implication goal."
              }
      | "assumption" =>
          let name <- match tactic.args.head? with
            | some name => pure name
            | none =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_EXPORT"
                  message := "Cannot export theorem: `assumption` requires a hypothesis name."
                }
          match findBinding? goal.context name with
          | some binding =>
              if formulaEq binding.formula goal.target then
                pure (goal.finish (.hyp name), rest)
              else
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_EXPORT"
                  message := s!"Cannot export theorem: hypothesis `{name}` does not match the current goal."
                }
          | none =>
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_EXPORT"
                message := s!"Cannot export theorem: unknown hypothesis `{name}`."
              }
      | "constructor" =>
          match goal.target with
          | .and left right =>
              let (leftProof, rest') <- buildProof { goal with target := left, finish := id } rest
              let (rightProof, rest'') <- buildProof { goal with target := right, finish := id } rest'
              pure (goal.finish (.andIntro leftProof rightProof), rest'')
          | _ =>
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_EXPORT"
                message := "Cannot export theorem: `constructor` was used on a non-conjunction goal."
              }
      | "left" =>
          if tactic.args.any (· = "at") then
            throw {
              line := tactic.sourceLine
              severity := 1
              code := "LEAN_BACKEND_EXPORT_UNSUPPORTED"
              message := "Export does not support `left at ...` yet."
            }
          else
            match goal.target with
            | .or left _ =>
                let (proof, rest') <- buildProof { goal with target := left, finish := id } rest
                pure (goal.finish (.orLeft proof), rest')
            | _ =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_EXPORT"
                  message := "Cannot export theorem: `left` was used on a non-disjunction goal."
                }
      | "right" =>
          if tactic.args.any (· = "at") then
            throw {
              line := tactic.sourceLine
              severity := 1
              code := "LEAN_BACKEND_EXPORT_UNSUPPORTED"
              message := "Export does not support `right at ...` yet."
            }
          else
            match goal.target with
            | .or _ right =>
                let (proof, rest') <- buildProof { goal with target := right, finish := id } rest
                pure (goal.finish (.orRight proof), rest')
            | _ =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_EXPORT"
                  message := "Cannot export theorem: `right` was used on a non-disjunction goal."
                }
      | "cases" =>
          let (name, restArgs) <- parseAtClause tactic
          let (leftName, rightName) <- match parseAsTwo restArgs with
            | some names => pure names
            | none =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_EXPORT"
                  message := "Cannot export theorem: `cases` requires `at <hypothesis> as <leftName> <rightName>`."
                }
          match findBinding? goal.context name with
          | some binding =>
              match binding.formula with
              | .or left right =>
                  let leftCtx <- match replaceBinding goal.context name { name := leftName, formula := left } with
                    | some ctx => pure ctx
                    | none =>
                        throw {
                          line := tactic.sourceLine
                          severity := 1
                          code := "LEAN_BACKEND_EXPORT"
                          message := s!"Cannot export theorem: unknown hypothesis `{name}`."
                        }
                  let rightCtx <- match replaceBinding goal.context name { name := rightName, formula := right } with
                    | some ctx => pure ctx
                    | none =>
                        throw {
                          line := tactic.sourceLine
                          severity := 1
                          code := "LEAN_BACKEND_EXPORT"
                          message := s!"Cannot export theorem: unknown hypothesis `{name}`."
                        }
                  let (leftProof, rest') <- buildProof { context := leftCtx, target := goal.target, finish := id } rest
                  let (rightProof, rest'') <- buildProof { context := rightCtx, target := goal.target, finish := id } rest'
                  pure (goal.finish (.orElim (.hyp name) leftName left leftProof rightName right rightProof), rest'')
              | _ =>
                  throw {
                    line := tactic.sourceLine
                    severity := 1
                    code := "LEAN_BACKEND_EXPORT"
                    message := "Cannot export theorem: `cases` applies only to disjunction hypotheses."
                  }
          | none =>
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_EXPORT"
                message := s!"Cannot export theorem: unknown hypothesis `{name}`."
              }
      | "apply" =>
          let name <- match tactic.args.head? with
            | some name => pure name
            | none =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_EXPORT"
                  message := "Cannot export theorem: `apply` requires a hypothesis name."
                }
          match findBinding? goal.context name with
          | some binding =>
              match binding.formula with
              | .imp premise conclusion =>
                  if formulaEq conclusion goal.target then
                    let (argProof, rest') <- buildProof { goal with target := premise, finish := id } rest
                    pure (goal.finish (.impElim (.hyp name) argProof), rest')
                  else
                    throw {
                      line := tactic.sourceLine
                      severity := 1
                      code := "LEAN_BACKEND_EXPORT"
                      message := s!"Cannot export theorem: hypothesis `{name}` does not conclude the current goal."
                    }
              | _ =>
                  throw {
                    line := tactic.sourceLine
                    severity := 1
                    code := "LEAN_BACKEND_EXPORT"
                    message := "Cannot export theorem: `apply` requires an implication hypothesis."
                  }
          | none =>
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_EXPORT"
                message := s!"Cannot export theorem: unknown hypothesis `{name}`."
              }
      | "exfalso" =>
          let (proof, rest') <- buildProof { goal with target := .bot, finish := id } rest
          pure (goal.finish (.bottomElim proof), rest')
      | "absurd" =>
          let name <- match tactic.args.head? with
            | some name => pure name
            | none =>
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_EXPORT"
                  message := "Cannot export theorem: `absurd` requires a hypothesis name."
                }
          match findBinding? goal.context name with
          | some binding =>
              if formulaEq binding.formula .bot then
                pure (goal.finish (.bottomElim (.hyp name)), rest)
              else
                throw {
                  line := tactic.sourceLine
                  severity := 1
                  code := "LEAN_BACKEND_EXPORT"
                  message := s!"Cannot export theorem: hypothesis `{name}` is not ⊥."
                }
          | none =>
              throw {
                line := tactic.sourceLine
                severity := 1
                code := "LEAN_BACKEND_EXPORT"
                message := s!"Cannot export theorem: unknown hypothesis `{name}`."
              }
      | "by_contra" =>
          throw {
            line := tactic.sourceLine
            severity := 1
            code := "LEAN_BACKEND_EXPORT_UNSUPPORTED"
            message := "Export currently targets NJp proofs only; NKp `by_contra` is not supported."
          }
      | other =>
          throw {
            line := tactic.sourceLine
            severity := 1
            code := "LEAN_BACKEND_EXPORT_UNSUPPORTED"
            message := s!"Export does not support tactic `{other}` yet."
          }

private partial def collectAtoms : Formula → List String
  | .atom name => [name]
  | .imp left right => collectAtoms left ++ collectAtoms right
  | .and left right => collectAtoms left ++ collectAtoms right
  | .or left right => collectAtoms left ++ collectAtoms right
  | .bot => []
  | _ => []

private def sanitizeIdent (text : String) : String :=
  let chars := text.toList
  let mapped := chars.map fun c =>
    if c.isAlphanum || c = '_' then c else '_'
  let base := String.ofList mapped
  if base.isEmpty then
    "exported"
  else if base.front.isAlpha || base.front = '_' then
    base
  else
    s!"x_{base}"

private def atomIdent (name : String) : String :=
  s!"atom_{sanitizeIdent name}"

private partial def renderFormulaExpr : Formula → String
  | .atom name => atomIdent name
  | .imp left right => s!"imp ({renderFormulaExpr left}) ({renderFormulaExpr right})"
  | .and left right => s!"and ({renderFormulaExpr left}) ({renderFormulaExpr right})"
  | .or left right => s!"or ({renderFormulaExpr left}) ({renderFormulaExpr right})"
  | .bot => "bot"
  | _ => "bot"

private def membershipProof (ctx : List Binding) (name : String) : String :=
  let rec loop (remaining : List Binding) : String :=
    match remaining with
    | [] => "False.elim (by contradiction)"
    | binding :: tail =>
        if binding.name = name then
          "List.mem_cons.2 (Or.inl rfl)"
        else
          s!"List.mem_cons.2 (Or.inr {loop tail})"
  loop ctx

private def indent (n : Nat) : String :=
  String.ofList (List.replicate n ' ')

private partial def renderProofLines (ctx : List Binding) (target : Formula) (proof : Proof) (baseIndent : Nat) :
    List String :=
  match proof with
  | .hyp name =>
      [
        s!"{indent baseIndent}apply Derivation.hyp",
        s!"{indent baseIndent}exact {membershipProof ctx name}"
      ]
  | .impIntro name premise body =>
      s!"{indent baseIndent}apply Derivation.impIntro" ::
      renderProofLines ({ name, formula := premise } :: ctx) target body baseIndent
  | .impElim fnProof argProof =>
      s!"{indent baseIndent}apply Derivation.impElim" ::
      s!"{indent baseIndent}·" ::
      renderProofLines ctx target fnProof (baseIndent + 2) ++
      (s!"{indent baseIndent}·" ::
      renderProofLines ctx target argProof (baseIndent + 2))
  | .andIntro left right =>
      s!"{indent baseIndent}apply Derivation.andIntro" ::
      s!"{indent baseIndent}·" ::
      renderProofLines ctx target left (baseIndent + 2) ++
      (s!"{indent baseIndent}·" ::
      renderProofLines ctx target right (baseIndent + 2))
  | .orLeft body =>
      s!"{indent baseIndent}apply Derivation.orLeft" ::
      renderProofLines ctx target body baseIndent
  | .orRight body =>
      s!"{indent baseIndent}apply Derivation.orRight" ::
      renderProofLines ctx target body baseIndent
  | .orElim scrutinee leftName leftFormula leftBody rightName rightFormula rightBody =>
      s!"{indent baseIndent}apply Derivation.orElim" ::
      s!"{indent baseIndent}·" ::
      renderProofLines ctx target scrutinee (baseIndent + 2) ++
      (s!"{indent baseIndent}·" ::
      renderProofLines ({ name := leftName, formula := leftFormula } :: ctx) target leftBody (baseIndent + 2)) ++
      (s!"{indent baseIndent}·" ::
      renderProofLines ({ name := rightName, formula := rightFormula } :: ctx) target rightBody (baseIndent + 2))
  | .bottomElim body =>
      s!"{indent baseIndent}apply Derivation.bottomElim" ::
      renderProofLines ctx target body baseIndent

private def renderExport (theoremName : String) (target : Formula) (proof : Proof) : String :=
  let atoms := (collectAtoms target).eraseDups
  let theoremIdent := sanitizeIdent theoremName
  let atomLines := atoms.map fun atom =>
    s!"def {atomIdent atom} : Formula := atom {reprStr atom}"
  let lines :=
    [
      "import Logic",
      "",
      "open Logic.IPC.PropositionalND",
      "",
      "namespace FastProofTheory.Exported",
      ""
    ] ++ atomLines ++
    (if atomLines.isEmpty then [] else [""]) ++
    [
      s!"theorem {theoremIdent} : Theorem ({renderFormulaExpr target}) := by",
      "  refine ⟨?_⟩"
    ] ++
    renderProofLines [] target proof 2 ++
    [
      "",
      "end FastProofTheory.Exported"
    ]
  String.intercalate "\n" lines

def exportIPCTheorem? (thm : ParsedTheorem) : Option String :=
  match thm.headerError?, thm.declaredSystem?, thm.statement? with
  | none, some declaredSystem, some statement =>
      if !(declaredSystem.isNaturalDeduction && declaredSystem.isNJp && declaredSystem.hasValidConfiguration) then
        none
      else
        match parseStatementGoal declaredSystem statement with
        | .error _ => none
        | .ok target =>
            let tactics := thm.tactics.map parseTacticLine
            match buildProof { context := [], target } tactics with
            | .error _ => none
            | .ok (proof, remaining) =>
                if remaining.isEmpty then
                  some (renderExport thm.name target proof)
                else
                  none
  | _, _, _ => none

def exportTheoremFromDocument (text theoremName : String) : Except String String := do
  let parsed := parseDocument text
  let thm <- match parsed.theorems.find? (fun thm => thm.name = theoremName) with
    | some thm => pure thm
    | none => throw s!"Theorem `{theoremName}` was not found."
  let state := evaluate { theorem? := some thm, sourceLines := [] }
  unless state.verified do
    throw s!"Theorem `{theoremName}` is not verified and cannot be exported. {state.status}"
  match exportIPCTheorem? thm with
  | some source => pure source
  | none =>
      throw s!"Theorem `{theoremName}` is not exportable. Only verified `NJp` theorems using the supported export tactics can be written as Lean files right now."

end FastProofTheory.Linear.Export
