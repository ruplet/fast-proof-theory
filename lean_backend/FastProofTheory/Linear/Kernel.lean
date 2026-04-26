import FastProofTheory.Core.Kernel
import FastProofTheory.Gentzen.System

namespace FastProofTheory.Linear

open Rules
open FastProofTheory.Gentzen.Rules.Linear

/--
Linear logic as a data-only Gentzen certificate language.

Certificates are untrusted data. All rule semantics are fixed here in the
checker; no constructor stores a function or executable rule body.
-/

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

abbrev CheckedCertificate := FastProofTheory.Core.CheckedCertificate FastProofTheory.Gentzen.LinearLogic Goal Certificate

inductive KernelError where
  | ruleNotAllowed (system : String) (rule : String)
  | unsupportedFormula (system : String) (formula : Formula)
  | wrongPremiseCount (rule : String) (expected : Nat) (actual : Nat)
  | ruleRejected (rule : String) (detail : String)

abbrev CheckM := ReaderT FastProofTheory.Gentzen.LinearLogic (Except KernelError)

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

private def focusedLinear? (ctx : LinearCtx) (focus : LinearFocus) : Option Formula :=
  match removeFirst? focus.focused ctx with
  | some remaining =>
      if sameLinearMultiset remaining (focus.before ++ focus.after) then
        some focus.focused
      else
        none
  | none => none

private def focusedUnrestricted? (ctx : UnrestrictedCtx) (focus : UnrestrictedFocus) : Option Formula :=
  match removeFirstUnrestricted? focus.focused ctx with
  | some remaining =>
      if sameUnrestrictedMultiset remaining (focus.before ++ focus.after) then
        some focus.focused
      else
        none
  | none => none

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

private def ensureFormulaAllowed (formula : Formula) : CheckM Unit := do
  let logic <- read
  unless logic.allowsFormula formula do
    throw (.unsupportedFormula logic.displayName formula)

private def ensureSequentSupported (goal : Goal) : CheckM Unit := do
  goal.unrestricted.forM ensureFormulaAllowed
  goal.linear.forM ensureFormulaAllowed
  ensureFormulaAllowed goal.target

private def ruleError (detail : String) : Except String (List Goal) :=
  .error detail

private def ruleAssumption (goal : Goal) : Except String (List Goal) :=
  match goal.linear with
  | [hyp] =>
      if formulaEq hyp goal.target then .ok [] else ruleError "The only linear hypothesis must match the target."
  | _ => ruleError "Assumption requires exactly one linear hypothesis."

private def ruleUseUnrestricted (goal : Goal) : Except String (List Goal) :=
  if listFormulaEq [] goal.linear && formulaIn goal.target goal.unrestricted then
    .ok []
  else
    ruleError "The target must be available in the unrestricted context and the linear context must be empty."

private def ruleWithLeft1 (focus : HypFocus) (goal : Goal) : Except String (List Goal) :=
  match focus with
  | .linear f =>
      match focusedLinear? goal.linear f with
      | some (.with a _) => .ok [{ goal with linear := f.before ++ a :: f.after }]
      | some _ => ruleError "Focused linear hypothesis is not an additive conjunction."
      | none => ruleError "Invalid linear focus for withLeft1."
  | .unrestricted f =>
      match focusedUnrestricted? goal.unrestricted f with
      | some (.with a _) => .ok [{ goal with unrestricted := f.before ++ a :: f.after }]
      | some _ => ruleError "Focused unrestricted hypothesis is not an additive conjunction."
      | none => ruleError "Invalid unrestricted focus for withLeft1."

private def ruleWithLeft2 (focus : HypFocus) (goal : Goal) : Except String (List Goal) :=
  match focus with
  | .linear f =>
      match focusedLinear? goal.linear f with
      | some (.with _ b) => .ok [{ goal with linear := f.before ++ b :: f.after }]
      | some _ => ruleError "Focused linear hypothesis is not an additive conjunction."
      | none => ruleError "Invalid linear focus for withLeft2."
  | .unrestricted f =>
      match focusedUnrestricted? goal.unrestricted f with
      | some (.with _ b) => .ok [{ goal with unrestricted := f.before ++ b :: f.after }]
      | some _ => ruleError "Focused unrestricted hypothesis is not an additive conjunction."
      | none => ruleError "Invalid unrestricted focus for withLeft2."

private def ruleTensorLeft (focus : LinearFocus) (goal : Goal) : Except String (List Goal) :=
  match focusedLinear? goal.linear focus with
  | some (.tensor a b) => .ok [{ goal with linear := focus.before ++ a :: b :: focus.after }]
  | some _ => ruleError "Focused hypothesis is not a tensor."
  | none => ruleError "Invalid linear focus for tensorLeft."

private def rulePlusLeftElim (focus : LinearFocus) (goal : Goal) : Except String (List Goal) :=
  match focusedLinear? goal.linear focus with
  | some (.plus a b) =>
      .ok [
        { goal with linear := focus.before ++ a :: focus.after },
        { goal with linear := focus.before ++ b :: focus.after }
      ]
  | some _ => ruleError "Focused hypothesis is not an additive disjunction."
  | none => ruleError "Invalid linear focus for plusLeftElim."

private def ruleLolliLeft (focus : LinearFocus) (split : SplitWitness) (goal : Goal) :
    Except String (List Goal) :=
  match split with
  | .explicit leftCtx rightCtx =>
      match focusedLinear? goal.linear focus with
      | some (.lolli a b) =>
          let remaining := focus.before ++ focus.after
          if splitValid remaining leftCtx rightCtx then
            .ok [
              { goal with linear := leftCtx, target := a },
              { goal with linear := b :: rightCtx }
            ]
          else
            ruleError "Invalid resource split for lolliLeft."
      | some _ => ruleError "Focused hypothesis is not a linear implication."
      | none => ruleError "Invalid linear focus for lolliLeft."

private def ruleBangLeft (focus : LinearFocus) (goal : Goal) : Except String (List Goal) :=
  match focusedLinear? goal.linear focus with
  | some (.bang a) =>
      .ok [{ goal with unrestricted := a :: goal.unrestricted, linear := focus.before ++ focus.after }]
  | some _ => ruleError "Focused hypothesis is not an exponential."
  | none => ruleError "Invalid linear focus for bangLeft."

private def ruleTensorIntro (split : SplitWitness) (goal : Goal) : Except String (List Goal) :=
  match split, goal.target with
  | .explicit left right, .tensor a b =>
      if splitValid goal.linear left right then
        .ok [
          { goal with linear := left, target := a },
          { goal with linear := right, target := b }
        ]
      else
        ruleError "Invalid resource split for tensor introduction."
  | _, _ => ruleError "Target is not a tensor."

private def ruleWithIntro (goal : Goal) : Except String (List Goal) :=
  match goal.target with
  | .with a b =>
      .ok [
        { goal with target := a },
        { goal with target := b }
      ]
  | _ => ruleError "Target is not an additive conjunction."

private def rulePlusLeft (goal : Goal) : Except String (List Goal) :=
  match goal.target with
  | .plus a _ => .ok [{ goal with target := a }]
  | _ => ruleError "Target is not an additive disjunction."

private def rulePlusRight (goal : Goal) : Except String (List Goal) :=
  match goal.target with
  | .plus _ b => .ok [{ goal with target := b }]
  | _ => ruleError "Target is not an additive disjunction."

private def ruleLolliIntro (goal : Goal) : Except String (List Goal) :=
  match goal.target with
  | .lolli a b => .ok [{ goal with linear := a :: goal.linear, target := b }]
  | _ => ruleError "Target is not a linear implication."

private def ruleBangIntro (goal : Goal) : Except String (List Goal) :=
  match goal.target with
  | .bang a =>
      if listFormulaEq [] goal.linear then
        .ok [{ goal with linear := [], target := a }]
      else
        ruleError "Exponential introduction requires an empty linear context."
  | _ => ruleError "Target is not an exponential."

private def ruleOneIntro (goal : Goal) : Except String (List Goal) :=
  if listFormulaEq [] goal.linear && formulaEq goal.target .one then
    .ok []
  else
    ruleError "Unit introduction requires target 1 and an empty linear context."

private def ruleTopIntro (goal : Goal) : Except String (List Goal) :=
  if formulaEq goal.target .top then
    .ok []
  else
    ruleError "Top introduction requires target top."

mutual
  partial def checkPremises
      (kind : RuleKind)
      (premises : List Goal)
      (subcertificates : List Certificate) : CheckM Unit := do
    unless premises.length = subcertificates.length do
      throw (.wrongPremiseCount kind.displayName premises.length subcertificates.length)
    let rec loop : List Goal → List Certificate → CheckM Unit
      | [], [] => pure ()
      | premise :: restPremises, certificate :: restCertificates => do
          checkCore premise certificate
          loop restPremises restCertificates
      | _, _ => pure ()
    loop premises subcertificates

  partial def checkRule
      (kind : RuleKind)
      (rule : Goal → Except String (List Goal))
      (goal : Goal)
      (subcertificates : List Certificate) : CheckM Unit := do
    let logic <- read
    unless logic.allowsRule kind do
      throw (.ruleNotAllowed logic.displayName kind.displayName)
    match rule goal with
    | .ok premises => checkPremises kind premises subcertificates
    | .error detail => throw (.ruleRejected kind.displayName detail)

  partial def checkCore (goal : Goal) (certificate : Certificate) : CheckM Unit := do
    ensureSequentSupported goal
    match certificate with
    | .assumption => checkRule .assumption ruleAssumption goal []
    | .useUnrestricted => checkRule .useUnrestricted ruleUseUnrestricted goal []
    | .withLeft1 focus body => checkRule .withLeft1 (ruleWithLeft1 focus) goal [body]
    | .withLeft2 focus body => checkRule .withLeft2 (ruleWithLeft2 focus) goal [body]
    | .tensorLeft focus body => checkRule .tensorLeft (ruleTensorLeft focus) goal [body]
    | .plusLeftElim focus left right => checkRule .plusLeftElim (rulePlusLeftElim focus) goal [left, right]
    | .lolliLeft focus split premise body =>
        checkRule .lolliLeft (ruleLolliLeft focus split) goal [premise, body]
    | .bangLeft focus body => checkRule .bangLeft (ruleBangLeft focus) goal [body]
    | .tensorIntro split left right => checkRule .tensorIntro (ruleTensorIntro split) goal [left, right]
    | .withIntro left right => checkRule .withIntro ruleWithIntro goal [left, right]
    | .plusLeft proof => checkRule .plusLeft rulePlusLeft goal [proof]
    | .plusRight proof => checkRule .plusRight rulePlusRight goal [proof]
    | .lolliIntro body => checkRule .lolliIntro ruleLolliIntro goal [body]
    | .bangIntro proof => checkRule .bangIntro ruleBangIntro goal [proof]
    | .oneIntro => checkRule .oneIntro ruleOneIntro goal []
    | .topIntro => checkRule .topIntro ruleTopIntro goal []
end

private def checkCertificateRaw (logic : FastProofTheory.Gentzen.LinearLogic) (goal : Goal) (certificate : Certificate) :
    Except KernelError CheckedCertificate :=
  match (checkCore goal certificate).run logic with
  | .ok _ =>
      .ok {
        system := logic
        goal
        certificate
        summary := s!"Checked Linear certificate for {logic.displayName} using rule {certificate.rootRule.displayName}."
      }
  | .error err => .error err

def renderKernelError : KernelError → String
  | .ruleNotAllowed system rule => s!"Rule `{rule}` is not allowed in system {system}."
  | .unsupportedFormula system _ => s!"Formula is not supported in system {system}."
  | .wrongPremiseCount rule expected actual =>
      s!"Rule `{rule}` expected {expected} premise certificate(s), but got {actual}."
  | .ruleRejected rule detail => s!"Rule `{rule}` rejected the sequent: {detail}"

instance : FastProofTheory.Core.ProofKernel FastProofTheory.Gentzen.LinearLogic Goal Certificate KernelError where
  kind := .gentzenSequent
  check := checkCertificateRaw
  renderError := renderKernelError

def checkCertificate (logic : FastProofTheory.Gentzen.LinearLogic) (goal : Goal) (certificate : Certificate) :
    Except KernelError CheckedCertificate :=
  FastProofTheory.Core.checkCertificate logic goal certificate

def checkClosedTheorem (logic : FastProofTheory.Gentzen.LinearLogic) (target : Formula) (certificate : Certificate) :
    Except KernelError CheckedCertificate :=
  checkCertificate logic { unrestricted := [], linear := [], target } certificate

end FastProofTheory.Linear
