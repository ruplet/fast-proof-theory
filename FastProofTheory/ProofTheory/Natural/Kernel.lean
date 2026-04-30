import FastProofTheory.Rules
import FastProofTheory.Core.Kernel
import FastProofTheory.ProofTheory.Natural.System

namespace FastProofTheory.ProofTheory.Natural

open Rules

/--
Trusted kernel for NJp/NKp natural-deduction proofs.

Audit guide:

* `Certificate` below is the complete proof language accepted by this kernel.
* `checkCore` is the only recursive checker for those certificates.
* `checkClosedTheorem` accepts a theorem only by checking a certificate for an
  empty context and the requested target formula.
* The UI and tactic engine may construct certificates, but they cannot mark a
  theorem verified without passing through this file.
-/

structure Binding where
  name : String
  formula : Formula

abbrev Context := List Binding

structure Goal where
  context : Context
  target : Formula

inductive Certificate where
  | hyp (name : String)
  | impIntro (name : String) (premise : Formula) (body : Certificate)
  | impElim (premise : Formula) (fnProof : Certificate) (argProof : Certificate)
  | andIntro (left right : Certificate)
  | andLeftAt (source alias : String) (body : Certificate)
  | andRightAt (source alias : String) (body : Certificate)
  | orLeft (proof : Certificate)
  | orRight (proof : Certificate)
  | orElim
      (scrutinee : Certificate)
      (leftName : String) (leftFormula : Formula) (leftBody : Certificate)
      (rightName : String) (rightFormula : Formula) (rightBody : Certificate)
  | bottomElim (proof : Certificate)
  | forallIntro (name : Label) (body : Certificate)
  | forallElim (binder : Label) (arg : Formula) (body : Formula) (proof : Certificate)
  | classical (name : String) (target : Formula) (body : Certificate)

abbrev CheckedCertificate :=
  FastProofTheory.Core.CheckedCertificate FastProofTheory.ProofTheory.Natural.System Goal Certificate

inductive KernelError where
  | ruleNotAllowed (system : String) (rule : String)
  | unsupportedFormula (system : String) (formula : Formula)
  | unknownHypothesis (name : String)
  | hypothesisMismatch (name : String) (expected actual : Formula)
  | expectedTarget (rule : String) (target : Formula)
  | malformedCertificate (detail : String)

mutual
  private def termEq : Rules.Term → Rules.Term → Bool
    | .var x, .var y => x = y
    | .fn f xs, .fn g ys => f = g && listTermEq xs ys
    | _, _ => false

  private def listTermEq : List Rules.Term → List Rules.Term → Bool
    | [], [] => true
    | x :: xs, y :: ys => termEq x y && listTermEq xs ys
    | _, _ => false
end

private partial def formulaEq : Formula → Formula → Bool
  | .atom a, .atom b => a = b
  | .pred p xs, .pred q ys => p = q && listTermEq xs ys
  | .imp a₁ b₁, .imp a₂ b₂ => formulaEq a₁ a₂ && formulaEq b₁ b₂
  | .and a₁ b₁, .and a₂ b₂ => formulaEq a₁ a₂ && formulaEq b₁ b₂
  | .or a₁ b₁, .or a₂ b₂ => formulaEq a₁ a₂ && formulaEq b₁ b₂
  | .bot, .bot => true
  | .all x a, .all y b => x = y && formulaEq a b
  | .ex x a, .ex y b => x = y && formulaEq a b
  | _, _ => false

private def lookup? (ctx : Context) (name : String) : Option Binding :=
  ctx.find? (fun binding => binding.name = name)

private def replaceBinding?
    (ctx : Context)
    (name : String)
    (replacement : Binding) : Option Context := Id.run do
  let rec loop (acc : Context) (rest : Context) : Option Context :=
    match rest with
    | [] => none
    | binding :: tail =>
        if binding.name = name then
          some (acc.reverse ++ replacement :: tail)
        else
          loop (binding :: acc) tail
  loop [] ctx

private def ensureSystem (system : FastProofTheory.ProofTheory.Natural.System) : Except KernelError Unit := do
  unless system.hasValidConfiguration do
    throw (.ruleNotAllowed system.displayName "ND")

private partial def ensureFormulaAllowed (system : FastProofTheory.ProofTheory.Natural.System) (formula : Formula) :
    Except KernelError Unit := do
  unless system.allowsFormula formula do
    throw (.unsupportedFormula system.displayName formula)

private def ensureGoalSupported (system : FastProofTheory.ProofTheory.Natural.System) (goal : Goal) :
    Except KernelError Unit := do
  ensureFormulaAllowed system goal.target
  goal.context.forM (fun binding => ensureFormulaAllowed system binding.formula)

private def formulaFreeVars : Formula → List Label
  | .atom name => [name]
  | .pred _ args => args.flatMap Rules.Term.freeVars |>.eraseDups
  | .imp a b => (formulaFreeVars a ++ formulaFreeVars b).eraseDups
  | .and a b => (formulaFreeVars a ++ formulaFreeVars b).eraseDups
  | .or a b => (formulaFreeVars a ++ formulaFreeVars b).eraseDups
  | .bot => []
  | .all name body => (formulaFreeVars body).erase name
  | .ex name body => (formulaFreeVars body).erase name
  | .tensor a b => (formulaFreeVars a ++ formulaFreeVars b).eraseDups
  | .par a b => (formulaFreeVars a ++ formulaFreeVars b).eraseDups
  | .with a b => (formulaFreeVars a ++ formulaFreeVars b).eraseDups
  | .plus a b => (formulaFreeVars a ++ formulaFreeVars b).eraseDups
  | .lolli a b => (formulaFreeVars a ++ formulaFreeVars b).eraseDups
  | .bang body => formulaFreeVars body
  | .whyNot body => formulaFreeVars body
  | .one => []
  | .zero => []
  | .top => []
  | .bottom => []

private def formulaAllNames : Formula → List Label
  | .atom name => [name]
  | .pred _ args => args.flatMap Rules.Term.allNames |>.eraseDups
  | .imp a b => (formulaAllNames a ++ formulaAllNames b).eraseDups
  | .and a b => (formulaAllNames a ++ formulaAllNames b).eraseDups
  | .or a b => (formulaAllNames a ++ formulaAllNames b).eraseDups
  | .bot => []
  | .all name body => (name :: formulaAllNames body).eraseDups
  | .ex name body => (name :: formulaAllNames body).eraseDups
  | .tensor a b => (formulaAllNames a ++ formulaAllNames b).eraseDups
  | .par a b => (formulaAllNames a ++ formulaAllNames b).eraseDups
  | .with a b => (formulaAllNames a ++ formulaAllNames b).eraseDups
  | .plus a b => (formulaAllNames a ++ formulaAllNames b).eraseDups
  | .lolli a b => (formulaAllNames a ++ formulaAllNames b).eraseDups
  | .bang body => formulaAllNames body
  | .whyNot body => formulaAllNames body
  | .one => []
  | .zero => []
  | .top => []
  | .bottom => []

private def contextFreeVars (ctx : Context) : List Label :=
  ctx.map (·.formula) |>.flatMap formulaFreeVars |>.eraseDups

private partial def freshName (base : Label) (avoid : List Label) : Label :=
  let rec loop (candidate : Label) : Label :=
    if candidate ∈ avoid then loop (FreshLabel.next candidate) else candidate
  loop base

private partial def renameTermVar (old new : Label) : Rules.Term → Rules.Term
  | .var x => if x = old then .var new else .var x
  | .fn f args => .fn f (args.map (renameTermVar old new))

private partial def renameFormulaVarScoped (old new : Label) : Formula → Formula
  | .atom name => if name = old then .atom new else .atom name
  | .pred p args => .pred p (args.map (renameTermVar old new))
  | .imp a b => .imp (renameFormulaVarScoped old new a) (renameFormulaVarScoped old new b)
  | .and a b => .and (renameFormulaVarScoped old new a) (renameFormulaVarScoped old new b)
  | .or a b => .or (renameFormulaVarScoped old new a) (renameFormulaVarScoped old new b)
  | .bot => .bot
  | .all binder body =>
      if binder = old then
        .all binder body
      else
        .all binder (renameFormulaVarScoped old new body)
  | .ex binder body =>
      if binder = old then
        .ex binder body
      else
        .ex binder (renameFormulaVarScoped old new body)
  | .tensor a b => .tensor (renameFormulaVarScoped old new a) (renameFormulaVarScoped old new b)
  | .par a b => .par (renameFormulaVarScoped old new a) (renameFormulaVarScoped old new b)
  | .with a b => .with (renameFormulaVarScoped old new a) (renameFormulaVarScoped old new b)
  | .plus a b => .plus (renameFormulaVarScoped old new a) (renameFormulaVarScoped old new b)
  | .lolli a b => .lolli (renameFormulaVarScoped old new a) (renameFormulaVarScoped old new b)
  | .bang body => .bang (renameFormulaVarScoped old new body)
  | .whyNot body => .whyNot (renameFormulaVarScoped old new body)
  | .one => .one
  | .zero => .zero
  | .top => .top
  | .bottom => .bottom

private partial def substFormulaAvoidCapture (name : Label) (replacement : Formula) : Formula → Formula
  | .atom atom => if atom = name then replacement else .atom atom
  | .pred p args => .pred p (args.map (fun t => t))
  | .imp a b => .imp (substFormulaAvoidCapture name replacement a) (substFormulaAvoidCapture name replacement b)
  | .and a b => .and (substFormulaAvoidCapture name replacement a) (substFormulaAvoidCapture name replacement b)
  | .or a b => .or (substFormulaAvoidCapture name replacement a) (substFormulaAvoidCapture name replacement b)
  | .bot => .bot
  | .all binder body =>
      if binder = name then
        .all binder body
      else if binder ∈ formulaFreeVars replacement then
        let avoid := (formulaAllNames body ++ formulaAllNames replacement ++ [name, binder]).eraseDups
        let fresh := freshName binder avoid
        let renamed := renameFormulaVarScoped binder fresh body
        .all fresh (substFormulaAvoidCapture name replacement renamed)
      else
        .all binder (substFormulaAvoidCapture name replacement body)
  | .ex binder body =>
      if binder = name then
        .ex binder body
      else if binder ∈ formulaFreeVars replacement then
        let avoid := (formulaAllNames body ++ formulaAllNames replacement ++ [name, binder]).eraseDups
        let fresh := freshName binder avoid
        let renamed := renameFormulaVarScoped binder fresh body
        .ex fresh (substFormulaAvoidCapture name replacement renamed)
      else
        .ex binder (substFormulaAvoidCapture name replacement body)
  | .tensor a b => .tensor (substFormulaAvoidCapture name replacement a) (substFormulaAvoidCapture name replacement b)
  | .par a b => .par (substFormulaAvoidCapture name replacement a) (substFormulaAvoidCapture name replacement b)
  | .with a b => .with (substFormulaAvoidCapture name replacement a) (substFormulaAvoidCapture name replacement b)
  | .plus a b => .plus (substFormulaAvoidCapture name replacement a) (substFormulaAvoidCapture name replacement b)
  | .lolli a b => .lolli (substFormulaAvoidCapture name replacement a) (substFormulaAvoidCapture name replacement b)
  | .bang body => .bang (substFormulaAvoidCapture name replacement body)
  | .whyNot body => .whyNot (substFormulaAvoidCapture name replacement body)
  | .one => .one
  | .zero => .zero
  | .top => .top
  | .bottom => .bottom

private def ensureFreshForAllIntro (system : FastProofTheory.ProofTheory.Natural.System) (goal : Goal) (binder : Label) :
    Except KernelError Unit := do
  let avoid := contextFreeVars goal.context
  unless binder ∉ avoid do
    throw (.malformedCertificate s!"forallIntro binder `{binder}` must be fresh in the context for {system.displayName}.")

private partial def checkCore (system : FastProofTheory.ProofTheory.Natural.System) (goal : Goal) (certificate : Certificate) :
    Except KernelError Unit := do
  ensureGoalSupported system goal
  match certificate with
  | .hyp name =>
      match lookup? goal.context name with
      | some binding =>
          unless formulaEq binding.formula goal.target do
            throw (.hypothesisMismatch name goal.target binding.formula)
      | none => throw (.unknownHypothesis name)
  | .impIntro name premise body =>
      match goal.target with
      | .imp expectedPremise target =>
          unless formulaEq premise expectedPremise do
            throw (.malformedCertificate "impIntro premise does not match the target premise.")
          checkCore system {
            context := { name, formula := premise } :: goal.context
            target := target
          } body
      | _ => throw (.expectedTarget "impIntro" goal.target)
  | .impElim premise fnProof argProof =>
      checkCore system { goal with target := .imp premise goal.target } fnProof
      checkCore system { goal with target := premise } argProof
  | .andIntro left right =>
      match goal.target with
      | .and a b =>
          checkCore system { goal with target := a } left
          checkCore system { goal with target := b } right
      | _ => throw (.expectedTarget "andIntro" goal.target)
  | .andLeftAt source alias body =>
      match lookup? goal.context source with
      | some binding =>
          match binding.formula with
          | .and a _ =>
              match replaceBinding? goal.context source { name := alias, formula := a } with
              | some ctx => checkCore system { goal with context := ctx } body
              | none => throw (.unknownHypothesis source)
          | _ => throw (.expectedTarget "andLeftAt" binding.formula)
      | none => throw (.unknownHypothesis source)
  | .andRightAt source alias body =>
      match lookup? goal.context source with
      | some binding =>
          match binding.formula with
          | .and _ b =>
              match replaceBinding? goal.context source { name := alias, formula := b } with
              | some ctx => checkCore system { goal with context := ctx } body
              | none => throw (.unknownHypothesis source)
          | _ => throw (.expectedTarget "andRightAt" binding.formula)
      | none => throw (.unknownHypothesis source)
  | .orLeft proof =>
      match goal.target with
      | .or a _ => checkCore system { goal with target := a } proof
      | _ => throw (.expectedTarget "orLeft" goal.target)
  | .orRight proof =>
      match goal.target with
      | .or _ b => checkCore system { goal with target := b } proof
      | _ => throw (.expectedTarget "orRight" goal.target)
  | .orElim scrutinee leftName leftFormula leftBody rightName rightFormula rightBody =>
      checkCore system { goal with target := .or leftFormula rightFormula } scrutinee
      checkCore system {
        context := { name := leftName, formula := leftFormula } :: goal.context
        target := goal.target
      } leftBody
      checkCore system {
        context := { name := rightName, formula := rightFormula } :: goal.context
        target := goal.target
      } rightBody
  | .bottomElim proof =>
      checkCore system { goal with target := .bot } proof
  | .forallIntro name bodyCert =>
      match goal.target with
      | .all binder body =>
          unless name = binder do
            throw (.malformedCertificate s!"forallIntro must introduce binder `{binder}`.")
          ensureFreshForAllIntro system goal binder
          checkCore system { goal with target := body } bodyCert
      | _ => throw (.expectedTarget "forallIntro" goal.target)
  | .forallElim binder arg body proof =>
      checkCore system { goal with target := .all binder body } proof
      let instantiated := substFormulaAvoidCapture binder arg body
      unless formulaEq instantiated goal.target do
        throw (.malformedCertificate "forallElim instantiation does not match the current goal.")
  | .classical name target body =>
      unless system.isNKp do
        throw (.ruleNotAllowed system.displayName "classical")
      unless formulaEq target goal.target do
        throw (.malformedCertificate "classical certificate target does not match the goal.")
      checkCore system {
        context := { name, formula := .imp goal.target .bot } :: goal.context
        target := .bot
      } body

def renderKernelError : KernelError → String
  | .ruleNotAllowed system rule => s!"Rule `{rule}` is not allowed in system {system}."
  | .unsupportedFormula system _ => s!"Formula is not supported in system {system}."
  | .unknownHypothesis name => s!"Unknown hypothesis `{name}`."
  | .hypothesisMismatch name _ _ => s!"Hypothesis `{name}` does not match the current goal."
  | .expectedTarget rule _ => s!"Current goal does not match the target shape required by `{rule}`."
  | .malformedCertificate detail => s!"Malformed certificate: {detail}"

private def checkCertificateRaw (system : FastProofTheory.ProofTheory.Natural.System) (goal : Goal) (certificate : Certificate) :
    Except KernelError CheckedCertificate := do
  ensureSystem system
  checkCore system goal certificate
  pure {
    system := system
    goal
    certificate
    summary := s!"Checked natural-deduction certificate for {system.displayName}."
  }

instance : FastProofTheory.Core.ProofKernel FastProofTheory.ProofTheory.Natural.System Goal Certificate KernelError where
  kind := .naturalDeduction
  check := checkCertificateRaw
  renderError := renderKernelError

def checkCertificate (system : FastProofTheory.ProofTheory.Natural.System) (goal : Goal) (certificate : Certificate) :
    Except KernelError CheckedCertificate :=
  FastProofTheory.Core.checkCertificate system goal certificate

def checkClosedTheorem (system : FastProofTheory.ProofTheory.Natural.System) (target : Formula) (certificate : Certificate) :
    Except KernelError CheckedCertificate :=
  checkCertificate system { context := [], target } certificate

end FastProofTheory.ProofTheory.Natural
