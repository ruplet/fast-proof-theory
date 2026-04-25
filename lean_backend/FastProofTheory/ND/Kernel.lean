import Logic.Rules
import FastProofTheory.Core.Kernel
import FastProofTheory.Linear.Profile

namespace FastProofTheory.ND

open Rules
open FastProofTheory.Linear

abbrev Formula := Rules.Formula

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
  | classical (name : String) (target : Formula) (body : Certificate)

abbrev CheckedCertificate :=
  FastProofTheory.Core.CheckedCertificate Profile Goal Certificate

inductive KernelError where
  | ruleNotAllowed (profile : String) (rule : String)
  | unsupportedFormula (profile : String) (formula : Formula)
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

private def ensureProfile (profile : Profile) : Except KernelError Unit := do
  unless profile.isNaturalDeduction && (profile.isIPC || profile.isCPC) && profile.hasValidConfiguration do
    throw (.ruleNotAllowed profile.displayName "ND")

private partial def ensureFormulaAllowed (profile : Profile) (formula : Formula) :
    Except KernelError Unit := do
  unless profile.allowsFormula formula do
    throw (.unsupportedFormula profile.displayName formula)

private def ensureGoalSupported (profile : Profile) (goal : Goal) :
    Except KernelError Unit := do
  ensureFormulaAllowed profile goal.target
  goal.context.forM (fun binding => ensureFormulaAllowed profile binding.formula)

private partial def checkCore (profile : Profile) (goal : Goal) (certificate : Certificate) :
    Except KernelError Unit := do
  ensureGoalSupported profile goal
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
          checkCore profile {
            context := { name, formula := premise } :: goal.context
            target := target
          } body
      | _ => throw (.expectedTarget "impIntro" goal.target)
  | .impElim premise fnProof argProof =>
      checkCore profile { goal with target := .imp premise goal.target } fnProof
      checkCore profile { goal with target := premise } argProof
  | .andIntro left right =>
      match goal.target with
      | .and a b =>
          checkCore profile { goal with target := a } left
          checkCore profile { goal with target := b } right
      | _ => throw (.expectedTarget "andIntro" goal.target)
  | .andLeftAt source alias body =>
      match lookup? goal.context source with
      | some binding =>
          match binding.formula with
          | .and a _ =>
              match replaceBinding? goal.context source { name := alias, formula := a } with
              | some ctx => checkCore profile { goal with context := ctx } body
              | none => throw (.unknownHypothesis source)
          | _ => throw (.expectedTarget "andLeftAt" binding.formula)
      | none => throw (.unknownHypothesis source)
  | .andRightAt source alias body =>
      match lookup? goal.context source with
      | some binding =>
          match binding.formula with
          | .and _ b =>
              match replaceBinding? goal.context source { name := alias, formula := b } with
              | some ctx => checkCore profile { goal with context := ctx } body
              | none => throw (.unknownHypothesis source)
          | _ => throw (.expectedTarget "andRightAt" binding.formula)
      | none => throw (.unknownHypothesis source)
  | .orLeft proof =>
      match goal.target with
      | .or a _ => checkCore profile { goal with target := a } proof
      | _ => throw (.expectedTarget "orLeft" goal.target)
  | .orRight proof =>
      match goal.target with
      | .or _ b => checkCore profile { goal with target := b } proof
      | _ => throw (.expectedTarget "orRight" goal.target)
  | .orElim scrutinee leftName leftFormula leftBody rightName rightFormula rightBody =>
      checkCore profile { goal with target := .or leftFormula rightFormula } scrutinee
      checkCore profile {
        context := { name := leftName, formula := leftFormula } :: goal.context
        target := goal.target
      } leftBody
      checkCore profile {
        context := { name := rightName, formula := rightFormula } :: goal.context
        target := goal.target
      } rightBody
  | .bottomElim proof =>
      checkCore profile { goal with target := .bot } proof
  | .classical name target body =>
      unless profile.isCPC do
        throw (.ruleNotAllowed profile.displayName "classical")
      unless formulaEq target goal.target do
        throw (.malformedCertificate "classical certificate target does not match the goal.")
      checkCore profile {
        context := { name, formula := .imp goal.target .bot } :: goal.context
        target := .bot
      } body

def renderKernelError : KernelError → String
  | .ruleNotAllowed profile rule => s!"Rule `{rule}` is not allowed in profile {profile}."
  | .unsupportedFormula profile _ => s!"Formula is not supported in profile {profile}."
  | .unknownHypothesis name => s!"Unknown hypothesis `{name}`."
  | .hypothesisMismatch name _ _ => s!"Hypothesis `{name}` does not match the current goal."
  | .expectedTarget rule _ => s!"Current goal does not match the target shape required by `{rule}`."
  | .malformedCertificate detail => s!"Malformed certificate: {detail}"

private def checkCertificateRaw (profile : Profile) (goal : Goal) (certificate : Certificate) :
    Except KernelError CheckedCertificate := do
  ensureProfile profile
  checkCore profile goal certificate
  pure {
    profile
    goal
    certificate
    summary := s!"Checked natural-deduction certificate for {profile.displayName}."
  }

instance : FastProofTheory.Core.ProofKernel Profile Goal Certificate KernelError where
  kind := .naturalDeduction
  check := checkCertificateRaw
  renderError := renderKernelError

def checkCertificate (profile : Profile) (goal : Goal) (certificate : Certificate) :
    Except KernelError CheckedCertificate :=
  FastProofTheory.Core.checkCertificate profile goal certificate

def checkClosedTheorem (profile : Profile) (target : Formula) (certificate : Certificate) :
    Except KernelError CheckedCertificate :=
  checkCertificate profile { context := [], target } certificate

end FastProofTheory.ND
