import FastProofTheory.ProofSystems.Rules
import FastProofTheory.Linear.Profile

namespace FastProofTheory.Linear

open Rules

abbrev Formula := Rules.Formula
abbrev UnrestrictedCtx := Rules.Unrestricted
abbrev LinearCtx := Rules.LinearContext

structure Goal where
  unrestricted : UnrestrictedCtx
  linear : LinearCtx
  target : Formula

inductive SplitWitness where
  | explicit (left : LinearCtx) (right : LinearCtx)

inductive Certificate where
  | assumption
  | useUnrestricted
  | tensorIntro (split : SplitWitness) (left : Certificate) (right : Certificate)
  | withIntro (left : Certificate) (right : Certificate)
  | plusLeft (proof : Certificate)
  | plusRight (proof : Certificate)
  | lolliIntro (body : Certificate)
  | bangIntro (proof : Certificate)
  | oneIntro
  | topIntro
  | derived (name : String) (subcerts : List Certificate)

structure CheckedCertificate where
  profile : Profile
  goal : Goal
  certificate : Certificate
  summary : String

inductive KernelError where
  | ruleNotAllowed (profile : String) (rule : RuleKind)
  | unsupportedRule (rule : String)
  | profileViolation (detail : String)
  | unsupportedFormula (profile : String) (formula : Formula)
  | expectedTarget (rule : RuleKind) (target : Formula)
  | linearContextMismatch (expected : LinearCtx) (actual : LinearCtx)
  | unrestrictedContextMismatch (expected : UnrestrictedCtx) (actual : UnrestrictedCtx)
  | missingLinearHypothesis (target : Formula) (ctx : LinearCtx)
  | missingUnrestrictedHypothesis (target : Formula) (ctx : UnrestrictedCtx)
  | invalidSplit (original : LinearCtx) (left : LinearCtx) (right : LinearCtx)
  | malformedCertificate (detail : String)

abbrev CheckM := ReaderT Profile (Except KernelError)

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

private def formulaEq : Formula → Formula → Bool
  | .atom a, .atom b => a = b
  | .pred p xs, .pred q ys => p = q && listTermEq xs ys
  | .imp a₁ b₁, .imp a₂ b₂ => formulaEq a₁ a₂ && formulaEq b₁ b₂
  | .and a₁ b₁, .and a₂ b₂ => formulaEq a₁ a₂ && formulaEq b₁ b₂
  | .or a₁ b₁, .or a₂ b₂ => formulaEq a₁ a₂ && formulaEq b₁ b₂
  | .bot, .bot => true
  | .all x a, .all y b => x = y && formulaEq a b
  | .ex x a, .ex y b => x = y && formulaEq a b
  | .tensor a₁ b₁, .tensor a₂ b₂ => formulaEq a₁ a₂ && formulaEq b₁ b₂
  | .par a₁ b₁, .par a₂ b₂ => formulaEq a₁ a₂ && formulaEq b₁ b₂
  | .with a₁ b₁, .with a₂ b₂ => formulaEq a₁ a₂ && formulaEq b₁ b₂
  | .plus a₁ b₁, .plus a₂ b₂ => formulaEq a₁ a₂ && formulaEq b₁ b₂
  | .lolli a₁ b₁, .lolli a₂ b₂ => formulaEq a₁ a₂ && formulaEq b₁ b₂
  | .bang a, .bang b => formulaEq a b
  | .whyNot a, .whyNot b => formulaEq a b
  | .one, .one => true
  | .zero, .zero => true
  | .top, .top => true
  | .bottom, .bottom => true
  | _, _ => false

private def formulaIn : Formula → List Formula → Bool
  | _, [] => false
  | target, head :: tail => formulaEq target head || formulaIn target tail

private def listFormulaEq : List Formula → List Formula → Bool
  | [], [] => true
  | x :: xs, y :: ys => formulaEq x y && listFormulaEq xs ys
  | _, _ => false

def Certificate.rootRule : Certificate → RuleKind
  | .assumption => .assumption
  | .useUnrestricted => .useUnrestricted
  | .tensorIntro _ _ _ => .tensorIntro
  | .withIntro _ _ => .withIntro
  | .plusLeft _ => .plusLeft
  | .plusRight _ => .plusRight
  | .lolliIntro _ => .lolliIntro
  | .bangIntro _ => .bangIntro
  | .oneIntro => .oneIntro
  | .topIntro => .topIntro
  | .derived _ _ => .assumption

def RuleKind.displayName : RuleKind → String
  | .assumption => "assumption"
  | .useUnrestricted => "useUnrestricted"
  | .tensorIntro => "tensorIntro"
  | .withIntro => "withIntro"
  | .plusLeft => "plusLeft"
  | .plusRight => "plusRight"
  | .lolliIntro => "lolliIntro"
  | .bangIntro => "bangIntro"
  | .oneIntro => "oneIntro"
  | .topIntro => "topIntro"

def renderKernelError : KernelError → String
  | .ruleNotAllowed profile rule => s!"Rule `{rule.displayName}` is not allowed in profile {profile}."
  | .unsupportedRule rule => s!"Unsupported derived rule: {rule}."
  | .profileViolation detail => detail
  | .unsupportedFormula profile _ => s!"Formula is not supported in profile {profile}."
  | .expectedTarget rule _ => s!"Current goal does not match the target shape required by `{rule.displayName}`."
  | .linearContextMismatch _ _ => "Linear context does not match the rule requirements."
  | .unrestrictedContextMismatch _ _ => "Unrestricted context does not match the rule requirements."
  | .missingLinearHypothesis _ _ => "The current linear context does not contain exactly the hypothesis required by `assumption`."
  | .missingUnrestrictedHypothesis _ _ => "The unrestricted context does not contain the required hypothesis."
  | .invalidSplit _ _ _ => "The resource split is invalid for the current linear context."
  | .malformedCertificate detail => s!"Malformed certificate: {detail}"

private def formulaAllowed (profile : Profile) : Formula → Bool
  | .bang _ => profile.allowsExponentials
  | .whyNot _ => profile.allowsExponentials
  | .tensor a b => formulaAllowed profile a && formulaAllowed profile b
  | .par a b => formulaAllowed profile a && formulaAllowed profile b
  | .with a b => formulaAllowed profile a && formulaAllowed profile b
  | .plus a b => formulaAllowed profile a && formulaAllowed profile b
  | .lolli a b => formulaAllowed profile a && formulaAllowed profile b
  | .imp a b => formulaAllowed profile a && formulaAllowed profile b
  | .and a b => formulaAllowed profile a && formulaAllowed profile b
  | .or a b => formulaAllowed profile a && formulaAllowed profile b
  | .all _ a => formulaAllowed profile a
  | .ex _ a => formulaAllowed profile a
  | _ => true

private def ensureRuleAllowed (rule : RuleKind) : CheckM Unit := do
  let profile <- read
  unless profile.allowsRule rule do
    throw (.ruleNotAllowed profile.displayName rule)

private def ensureFormulaAllowed (formula : Formula) : CheckM Unit := do
  let profile <- read
  unless formulaAllowed profile formula do
    throw (.unsupportedFormula profile.displayName formula)

private def ensureGoalSupported (goal : Goal) : CheckM Unit := do
  goal.unrestricted.forM ensureFormulaAllowed
  goal.linear.forM ensureFormulaAllowed
  ensureFormulaAllowed goal.target

private def removeFirst? (target : Formula) : LinearCtx → Option LinearCtx
  | [] => none
  | head :: tail =>
      if formulaEq head target then
        some tail
      else
        match removeFirst? target tail with
        | some rest => some (head :: rest)
        | none => none

private def consumeAll? (items : LinearCtx) (ctx : LinearCtx) : Option LinearCtx :=
  match items with
  | [] => some ctx
  | item :: rest =>
      match removeFirst? item ctx with
      | some remaining => consumeAll? rest remaining
      | none => none

private def splitValid (original left right : LinearCtx) : Bool :=
  match consumeAll? left original with
  | some remaining =>
      match consumeAll? right remaining with
      | some [] => true
      | _ => false
  | none => false

private def checkLinearExact (expected actual : LinearCtx) : CheckM Unit := do
  unless listFormulaEq expected actual do
    throw (.linearContextMismatch expected actual)

private def checkUnrestrictedExact (expected actual : UnrestrictedCtx) : CheckM Unit := do
  unless listFormulaEq expected actual do
    throw (.unrestrictedContextMismatch expected actual)

partial def checkCore (goal : Goal) (certificate : Certificate) : CheckM Unit := do
  ensureGoalSupported goal
  match certificate with
  | .assumption =>
      ensureRuleAllowed .assumption
      match goal.linear with
      | [hyp] =>
          unless formulaEq hyp goal.target do
            throw (.missingLinearHypothesis goal.target goal.linear)
      | _ => throw (.missingLinearHypothesis goal.target goal.linear)
  | .useUnrestricted =>
      ensureRuleAllowed .useUnrestricted
      checkLinearExact [] goal.linear
      unless formulaIn goal.target goal.unrestricted do
        throw (.missingUnrestrictedHypothesis goal.target goal.unrestricted)
  | .tensorIntro (.explicit left right) leftCert rightCert =>
      ensureRuleAllowed .tensorIntro
      match goal.target with
      | .tensor a b =>
          unless splitValid goal.linear left right do
            throw (.invalidSplit goal.linear left right)
          checkCore { unrestricted := goal.unrestricted, linear := left, target := a } leftCert
          checkCore { unrestricted := goal.unrestricted, linear := right, target := b } rightCert
      | target => throw (.expectedTarget .tensorIntro target)
  | .withIntro leftCert rightCert =>
      ensureRuleAllowed .withIntro
      match goal.target with
      | .with a b =>
          checkCore { unrestricted := goal.unrestricted, linear := goal.linear, target := a } leftCert
          checkCore { unrestricted := goal.unrestricted, linear := goal.linear, target := b } rightCert
      | target => throw (.expectedTarget .withIntro target)
  | .plusLeft proof =>
      ensureRuleAllowed .plusLeft
      match goal.target with
      | .plus a _ =>
          checkCore { unrestricted := goal.unrestricted, linear := goal.linear, target := a } proof
      | target => throw (.expectedTarget .plusLeft target)
  | .plusRight proof =>
      ensureRuleAllowed .plusRight
      match goal.target with
      | .plus _ b =>
          checkCore { unrestricted := goal.unrestricted, linear := goal.linear, target := b } proof
      | target => throw (.expectedTarget .plusRight target)
  | .lolliIntro body =>
      ensureRuleAllowed .lolliIntro
      match goal.target with
      | .lolli a b =>
          checkCore { unrestricted := goal.unrestricted, linear := a :: goal.linear, target := b } body
      | target => throw (.expectedTarget .lolliIntro target)
  | .bangIntro proof =>
      ensureRuleAllowed .bangIntro
      match goal.target with
      | .bang a =>
          checkLinearExact [] goal.linear
          checkCore { unrestricted := goal.unrestricted, linear := [], target := a } proof
      | target => throw (.expectedTarget .bangIntro target)
  | .oneIntro =>
      ensureRuleAllowed .oneIntro
      checkLinearExact [] goal.linear
      unless formulaEq goal.target .one do
        throw (.expectedTarget .oneIntro goal.target)
  | .topIntro =>
      ensureRuleAllowed .topIntro
      unless formulaEq goal.target .top do
        throw (.expectedTarget .topIntro goal.target)
  | .derived _ _ =>
      pure ()

def checkCertificate (profile : Profile) (goal : Goal) (certificate : Certificate) :
    Except KernelError CheckedCertificate :=
  match (checkCore goal certificate).run profile with
  | .ok _ =>
      .ok {
        profile
        goal
        certificate
        summary := s!"Checked certificate for {profile.displayName} using rule {certificate.rootRule.displayName}."
      }
  | .error err => .error err

def checkClosedTheorem (profile : Profile) (target : Formula) (certificate : Certificate) :
    Except KernelError CheckedCertificate :=
  checkCertificate profile { unrestricted := [], linear := [], target } certificate

end FastProofTheory.Linear
