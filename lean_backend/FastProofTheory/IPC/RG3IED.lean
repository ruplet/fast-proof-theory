import Lean.Elab.Tactic
import Logic.IPC.Countermodel

open Lean
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Meta

namespace FastProofTheory.IPC.RG3IED

open Logic.IPC
open Logic.IPC.Countermodel

syntax (name := rg3iedCountermodel) "rg3ied_countermodel" : tactic

structure RawNode where
  id : Nat
  labels : List String
  children : List RawNode
deriving Repr

structure ParsedModel where
  root : RawNode

private def skipWs : List Char → List Char
  | [] => []
  | c :: cs =>
      if c.isWhitespace then skipWs cs else c :: cs

private def startsWith : List Char → String → Bool
  | cs, s => s.toList.isPrefixOf cs

private partial def dropToNode : List Char → List Char
  | [] => []
  | cs =>
      if startsWith cs "node{" then
        cs
      else
        dropToNode (cs.drop 1)

private def consume (cs : List Char) (s : String) : Except String (List Char) := do
  if startsWith cs s then
    pure (cs.drop s.length)
  else
    throw s!"expected `{s}`"

private def parseNat (cs : List Char) : Except String (Nat × List Char) := do
  let cs := skipWs cs
  let rec go (acc : Nat) : List Char → Except String (Nat × List Char)
    | c :: rest =>
        if c.isDigit then
          go (acc * 10 + c.toNat - '0'.toNat) rest
        else
          pure (acc, c :: rest)
    | [] => pure (acc, [])
  match cs with
  | c :: rest =>
      if c.isDigit then
        go (c.toNat - '0'.toNat) rest
      else
        throw "expected a natural number"
  | [] => throw "unexpected end of input"

private def takeUntil (cs : List Char) (stop : Char) : Except String (String × List Char) := do
  let rec go (acc : List Char) : List Char → Except String (String × List Char)
    | [] => throw s!"expected `{stop}`"
    | c :: rest =>
        if c = stop then
          pure (String.ofList acc.reverse, rest)
        else
          go (c :: acc) rest
  go [] cs

private def parseLabels (s : String) : List String :=
  s.splitOn "," |>.map (fun t => t.trimAscii.toString) |>.filter (fun t => t ≠ "")

private partial def parseTree : List Char → Except String (RawNode × List Char)
  | cs => do
      let cs := skipWs cs
      let cs ← consume cs "node{"
      let (id, cs) ← parseNat cs
      let cs ← consume (skipWs cs) ":"
      let (labels, cs) ← takeUntil cs '}'
      let labels := parseLabels labels
      let rec loop (acc : List RawNode) : List Char → Except String (List RawNode × List Char)
        | cs => do
            let cs := skipWs cs
            if startsWith cs "child{" then
              let cs ← consume cs "child{"
              let (child, cs) ← parseTree cs
              let cs := skipWs cs
              let cs ← consume cs "}"
              loop (child :: acc) cs
            else
              pure (acc.reverse, cs)
      let (children, cs) ← loop [] cs
      pure ({ id, labels, children }, cs)

def parseModelTex (content : String) : Except String ParsedModel := do
  let cs := dropToNode content.toList
  let (root, rest) ← parseTree cs
  let rest := skipWs rest
  let rest := if rest.head? = some ';' then rest.tail else rest
  if skipWs rest = [] then
    pure { root }
  else
    pure { root }

private def maxId : RawNode → Nat
  | .mk id _ children => children.foldl (fun acc child => Nat.max acc (maxId child)) id

private def collectNodes : RawNode → List (Nat × List String)
  | .mk id labels children =>
      (id, labels) :: List.flatMap collectNodes children

private def collectPairs : RawNode → List Nat → List (Nat × Nat)
  | .mk id _ children, ancestors =>
      let selfPairs : List (Nat × Nat) := (id, id) :: ancestors.map (fun a => (a, id))
      selfPairs ++ List.flatMap (fun child => collectPairs child (id :: ancestors)) children

private def renderLeanFormula : Formula → String
  | .atom s => s!".atom {toString (repr s)}"
  | .bot => ".bot"
  | .imp a b => s!"(.imp {renderLeanFormula a} {renderLeanFormula b})"
  | .and a b => s!"(.and {renderLeanFormula a} {renderLeanFormula b})"
  | .or a b => s!"(.or {renderLeanFormula a} {renderLeanFormula b})"

def renderJtwFormula : Formula → String
  | .atom s => s
  | .bot => "false"
  | .imp a b => s!"({renderJtwFormula a} -> {renderJtwFormula b})"
  | .and a b => s!"({renderJtwFormula a} & {renderJtwFormula b})"
  | .or a b => s!"({renderJtwFormula a} | {renderJtwFormula b})"

private def renderStringLit (s : String) : String := toString (repr s)

private def renderLeTable (pairs : List (Nat × Nat)) : String :=
  let rows :=
    pairs.map (fun (u, v) => s!"  | {u}, {v} => true")
  String.intercalate "\n"
    ("fun u v =>\n  match u.1, v.1 with" :: rows ++ ["  | _, _ => false"])

private def renderValTable (nodes : List (Nat × List String)) : String :=
  let rows :=
    nodes.map fun (id, labels) =>
      let tests :=
        labels.reverse.foldl
          (fun acc atom => s!"if h : p = {renderStringLit atom} then true else {acc}")
          "false"
      s!"  | {id} => {tests}"
  String.intercalate "\n" ("fun p w =>\n  match w.1 with" :: rows ++ ["  | _ => false"])

def renderCountermodelTerm (formula : Formula) (model : ParsedModel) : String :=
  let nodes := collectNodes model.root
  let pairs := collectPairs model.root []
  let n := maxId model.root + 1
  let formulaStr := renderLeanFormula formula
  String.intercalate "\n" [
    "by",
    "  let frame : Logic.IPC.Countermodel.FiniteFrame := by",
    "    refine {",
    s!"      n := {n},",
    s!"      le := {renderLeTable pairs},",
    "      refl := by native_decide,",
    "      trans := by native_decide",
    "    }",
    "  let model : Logic.IPC.Countermodel.FiniteModel := by",
    "    refine {",
    "      toFiniteFrame := frame,",
    s!"      val := {renderValTable nodes},",
    "      mono := by",
    "        intro p u v huv hp",
    "        cases u using Fin.cases <;> cases v using Fin.cases <;> simp at huv hp ⊢ <;> try contradiction <;> try native_decide",
    "    }",
    "  let c : Logic.IPC.Countermodel.Countermodel := by",
    "    refine {",
    "      M := model,",
    "      root := ⟨0, by decide⟩,",
    s!"      formula := {formulaStr},",
    "      refutes := by",
    "        have hnf : ¬ Logic.IPC.Kripke.Forces (Logic.IPC.Countermodel.toModel model) ⟨0, by decide⟩",
    s!"            ({formulaStr}) := by",
    "          decide",
    "        simpa [Logic.IPC.Countermodel.eval, hnf]",
    "    }",
    "  exact Logic.IPC.Countermodel.countermodel_not_derivable c"
  ]

def renderCountermodelSnippet (name : String) (formula : Formula) (model : ParsedModel) : String :=
  let term := renderCountermodelTerm formula model
  String.intercalate "\n" [
    "import Logic.IPC.Countermodel",
    "",
    "open Logic.IPC",
    "open Logic.IPC.Countermodel",
    "",
    "-- generated by rg3ied",
    "",
    s!"def {name}_countermodel_proof : Not (Nonempty (Logic.IPC.Derivation [] {renderLeanFormula formula})) := {term}"
  ]

private partial def exprToFormula : Lean.Expr → Lean.Meta.MetaM Formula
  | .const ``Logic.IPC.Formula.bot _ => pure .bot
  | .app (.const ``Logic.IPC.Formula.atom _) (.lit (.strVal s)) => pure (.atom s)
  | .app (.app (.const ``Logic.IPC.Formula.imp _) a) b => do
      pure (.imp (← exprToFormula a) (← exprToFormula b))
  | .app (.app (.const ``Logic.IPC.Formula.and _) a) b => do
      pure (.and (← exprToFormula a) (← exprToFormula b))
  | .app (.app (.const ``Logic.IPC.Formula.or _) a) b => do
      pure (.or (← exprToFormula a) (← exprToFormula b))
  | e => do
      let fmt ← Lean.Meta.ppExpr e
      throwError m!"unsupported formula expression: {fmt}"

partial def extractFormula (e : Lean.Expr) : Lean.Meta.MetaM Formula := do
  let e ← whnf e
  match e with
  | .forallE _ dom body _ =>
      let body ← whnf body
      if body.isConstOf ``False then
        extractWitnessFormula dom e
      else
        throwError m!"expected a negated goal ending in `False`, got: {← ppExpr e}"
  | _ =>
      extractWitnessFormula e e
where
  extractWitnessFormula (inner : Lean.Expr) (whole : Lean.Expr) : Lean.Meta.MetaM Formula := do
    let inner ← whnf inner
    match inner.getAppFn with
    | .const ``Nonempty _ =>
        let args := inner.getAppArgs
        if args.size ≠ 1 then
          throwError "expected `Nonempty` to have one argument"
        extractWitnessFormula args[0]! whole
    | .const ``Logic.IPC.Derivation _ =>
        let args := inner.getAppArgs
        if args.size ≠ 2 then
          throwError "expected `Derivation` to have two arguments"
        let ctx := args[0]!
        let ctx ← whnf ctx
        if !ctx.isAppOf ``List.nil then
          throwError "only empty-context goals are supported"
        exprToFormula args[1]!
    | .const ``Logic.IPC.Kripke.Forces _ =>
        let args := inner.getAppArgs
        if args.size ≠ 3 then
          throwError "expected `Forces` to have three arguments"
        exprToFormula args[2]!
    | _ =>
        throwError m!"unsupported goal shape: {← Lean.Meta.ppExpr whole}"

def searchCountermodel (name : String) (formula : Formula) : IO (Except String ParsedModel) := do
  let script := "tools/jtabwb-rg3ied-model.sh"
  let formulaStr := renderJtwFormula formula
  let proc ← IO.Process.output {
    cmd := script
    args := #[name, formulaStr]
  }
  if proc.exitCode = 0 then
    let modelPath := s!"countermodels/jtabwb/{name}.model.tex"
    try
      let content ← IO.FS.readFile modelPath
      pure <| parseModelTex content
    catch e =>
      pure <| Except.error s!"rg3ied succeeded, but `{modelPath}` was not produced: {e.toString}"
  else
    pure <| Except.error (proc.stderr ++ proc.stdout)

elab_rules : tactic
  | `(tactic| rg3ied_countermodel) => do
      let goal ← Lean.Elab.Tactic.getMainGoal
      let goalTy ← Lean.instantiateMVars (← goal.getType)
      let formula ← Lean.Elab.Tactic.liftMetaMAtMain (fun _ => extractFormula goalTy)
      let name := s!"rg3ied_{String.hash (renderJtwFormula formula)}"
      let result ← liftM <| searchCountermodel name formula
      match result with
      | Except.error msg =>
          throwError "rg3ied countermodel search failed:\n{msg}"
      | Except.ok model =>
          let snippet := renderCountermodelSnippet name formula model
          logInfo m!"rg3ied countermodel candidate:\n{snippet}"
          pure ()

end FastProofTheory.IPC.RG3IED
