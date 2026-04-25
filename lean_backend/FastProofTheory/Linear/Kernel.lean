import Logic.Rules
import FastProofTheory.Core.Kernel
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

structure LinearFocus where
  before : LinearCtx
  focused : Formula
  after : LinearCtx

structure UnrestrictedFocus where
  before : UnrestrictedCtx
  focused : Formula
  after : UnrestrictedCtx

inductive HypFocus where
  | linear (focus : LinearFocus)
  | unrestricted (focus : UnrestrictedFocus)

inductive SplitWitness where
  | explicit (left : LinearCtx) (right : LinearCtx)

inductive Certificate where
  | assumption
  | useUnrestricted
  | withLeft1 (focus : HypFocus) (body : Certificate)
  | withLeft2 (focus : HypFocus) (body : Certificate)
  | tensorLeft (focus : LinearFocus) (body : Certificate)
  | plusLeftElim (focus : LinearFocus) (left : Certificate) (right : Certificate)
  | lolliLeft (focus : LinearFocus) (split : SplitWitness) (premise : Certificate) (body : Certificate)
  | bangLeft (focus : LinearFocus) (body : Certificate)
  | tensorIntro (split : SplitWitness) (left : Certificate) (right : Certificate)
  | withIntro (left : Certificate) (right : Certificate)
  | plusLeft (proof : Certificate)
  | plusRight (proof : Certificate)
  | lolliIntro (body : Certificate)
  | bangIntro (proof : Certificate)
  | oneIntro
  | topIntro

abbrev CheckedCertificate :=
  FastProofTheory.Core.CheckedCertificate Profile Goal Certificate

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
  | .withLeft1 _ _ => .withLeft1
  | .withLeft2 _ _ => .withLeft2
  | .tensorLeft _ _ => .tensorLeft
  | .plusLeftElim _ _ _ => .plusLeftElim
  | .lolliLeft _ _ _ _ => .lolliLeft
  | .bangLeft _ _ => .bangLeft
  | .tensorIntro _ _ _ => .tensorIntro
  | .withIntro _ _ => .withIntro
  | .plusLeft _ => .plusLeft
  | .plusRight _ => .plusRight
  | .lolliIntro _ => .lolliIntro
  | .bangIntro _ => .bangIntro
  | .oneIntro => .oneIntro
  | .topIntro => .topIntro

def RuleKind.displayName : RuleKind → String
  | .assumption => "assumption"
  | .useUnrestricted => "useUnrestricted"
  | .withLeft1 => "withLeft1"
  | .withLeft2 => "withLeft2"
  | .tensorLeft => "tensorLeft"
  | .plusLeftElim => "plusLeftElim"
  | .lolliLeft => "lolliLeft"
  | .bangLeft => "bangLeft"
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

private def ensureRuleAllowed (rule : RuleKind) : CheckM Unit := do
  let profile <- read
  unless profile.allowsRule rule do
    throw (.ruleNotAllowed profile.displayName rule)

private def ensureFormulaAllowed (formula : Formula) : CheckM Unit := do
  let profile <- read
  unless profile.allowsFormula formula do
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

private def sameLinearMultiset (a b : LinearCtx) : Bool :=
  match consumeAll? a b with
  | some [] =>
      match consumeAll? b a with
      | some [] => true
      | _ => false
  | _ => false

private def removeFirstUnrestricted? (target : Formula) : UnrestrictedCtx → Option UnrestrictedCtx
  | [] => none
  | head :: tail =>
      if formulaEq head target then
        some tail
      else
        match removeFirstUnrestricted? target tail with
        | some rest => some (head :: rest)
        | none => none

private def sameUnrestrictedMultiset : UnrestrictedCtx → UnrestrictedCtx → Bool
  | [], [] => true
  | x :: xs, ys =>
      match removeFirstUnrestricted? x ys with
      | some rest => sameUnrestrictedMultiset xs rest
      | none => false
  | _, _ => false

private def focusedLinear? (ctx : LinearCtx) (focus : LinearFocus) : Option (Formula × LinearCtx) :=
  match removeFirst? focus.focused ctx with
  | some remaining =>
      if sameLinearMultiset remaining (focus.before ++ focus.after) then
        some (focus.focused, remaining)
      else
        none
  | none => none

private def focusedUnrestricted? (ctx : UnrestrictedCtx) (focus : UnrestrictedFocus) : Option (Formula × UnrestrictedCtx) :=
  match removeFirstUnrestricted? focus.focused ctx with
  | some remaining =>
      if sameUnrestrictedMultiset remaining (focus.before ++ focus.after) then
        some (focus.focused, remaining)
      else
        none
  | none => none

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
  | .withLeft1 focus body =>
      ensureRuleAllowed .withLeft1
      match focus with
      | .linear f =>
          match focusedLinear? goal.linear f with
          | some (.with a _, _) =>
              checkCore { unrestricted := goal.unrestricted, linear := f.before ++ a :: f.after, target := goal.target } body
          | some (target, _) => throw (.expectedTarget .withLeft1 target)
          | none => throw (.malformedCertificate "Invalid linear focus for withLeft1.")
      | .unrestricted f =>
          match focusedUnrestricted? goal.unrestricted f with
          | some (.with a _, _) =>
              checkCore { unrestricted := f.before ++ a :: f.after, linear := goal.linear, target := goal.target } body
          | some (target, _) => throw (.expectedTarget .withLeft1 target)
          | none => throw (.malformedCertificate "Invalid unrestricted focus for withLeft1.")
  | .withLeft2 focus body =>
      ensureRuleAllowed .withLeft2
      match focus with
      | .linear f =>
          match focusedLinear? goal.linear f with
          | some (.with _ b, _) =>
              checkCore { unrestricted := goal.unrestricted, linear := f.before ++ b :: f.after, target := goal.target } body
          | some (target, _) => throw (.expectedTarget .withLeft2 target)
          | none => throw (.malformedCertificate "Invalid linear focus for withLeft2.")
      | .unrestricted f =>
          match focusedUnrestricted? goal.unrestricted f with
          | some (.with _ b, _) =>
              checkCore { unrestricted := f.before ++ b :: f.after, linear := goal.linear, target := goal.target } body
          | some (target, _) => throw (.expectedTarget .withLeft2 target)
          | none => throw (.malformedCertificate "Invalid unrestricted focus for withLeft2.")
  | .tensorLeft focus body =>
      ensureRuleAllowed .tensorLeft
      match focusedLinear? goal.linear focus with
      | some (.tensor a b, _) =>
          checkCore { unrestricted := goal.unrestricted, linear := focus.before ++ a :: b :: focus.after, target := goal.target } body
      | some (target, _) => throw (.expectedTarget .tensorLeft target)
      | none => throw (.malformedCertificate "Invalid linear focus for tensorLeft.")
  | .plusLeftElim focus left right =>
      ensureRuleAllowed .plusLeftElim
      match focusedLinear? goal.linear focus with
      | some (.plus a b, _) =>
          let leftLinear := focus.before ++ a :: focus.after
          let rightLinear := focus.before ++ b :: focus.after
          checkCore { unrestricted := goal.unrestricted, linear := leftLinear, target := goal.target } left
          checkCore { unrestricted := goal.unrestricted, linear := rightLinear, target := goal.target } right
      | some (target, _) => throw (.expectedTarget .plusLeftElim target)
      | none => throw (.malformedCertificate "Invalid linear focus for plusLeftElim.")
  | .lolliLeft focus (.explicit leftCtx rightCtx) premise body =>
      ensureRuleAllowed .lolliLeft
      match focusedLinear? goal.linear focus with
      | some (.lolli a b, _) =>
          let remaining := focus.before ++ focus.after
          unless splitValid remaining leftCtx rightCtx do
            throw (.invalidSplit remaining leftCtx rightCtx)
          checkCore { unrestricted := goal.unrestricted, linear := leftCtx, target := a } premise
          checkCore { unrestricted := goal.unrestricted, linear := b :: rightCtx, target := goal.target } body
      | some (target, _) => throw (.expectedTarget .lolliLeft target)
      | none => throw (.malformedCertificate "Invalid linear focus for lolliLeft.")
  | .bangLeft focus body =>
      ensureRuleAllowed .bangLeft
      match focusedLinear? goal.linear focus with
      | some (.bang a, _) =>
          checkCore { unrestricted := a :: goal.unrestricted, linear := focus.before ++ focus.after, target := goal.target } body
      | some (target, _) => throw (.expectedTarget .bangLeft target)
      | none => throw (.malformedCertificate "Invalid linear focus for bangLeft.")
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

private def checkCertificateRaw (profile : Profile) (goal : Goal) (certificate : Certificate) :
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

instance : FastProofTheory.Core.ProofKernel Profile Goal Certificate KernelError where
  kind := .gentzenSequent
  check := checkCertificateRaw
  renderError := renderKernelError

def checkCertificate (profile : Profile) (goal : Goal) (certificate : Certificate) :
    Except KernelError CheckedCertificate :=
  FastProofTheory.Core.checkCertificate profile goal certificate

def checkClosedTheorem (profile : Profile) (target : Formula) (certificate : Certificate) :
    Except KernelError CheckedCertificate :=
  checkCertificate profile { unrestricted := [], linear := [], target } certificate

end FastProofTheory.Linear
