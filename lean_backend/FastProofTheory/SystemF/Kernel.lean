import Logic.SystemF.Typing
import FastProofTheory.Core.Kernel

namespace FastProofTheory.SystemF

abbrev SFTy := Logic.SystemF.Ty
abbrev SFTm := Logic.SystemF.Tm
abbrev SFContext := Logic.SystemF.Context

structure Profile where
  name : String := "SYSTEM_F"

structure Goal where
  context : SFContext
  target : SFTy

abbrev Certificate := SFTm

abbrev CheckedCertificate :=
  FastProofTheory.Core.CheckedCertificate Profile Goal Certificate

inductive KernelError where
  | unknownTermVariable (name : String)
  | expectedFunction (actual : SFTy)
  | expectedForall (actual : SFTy)
  | typeMismatch (expected actual : SFTy)
  | typeSubstitutionError (message : String)
  | typeVariableEscapesContext (name : String)

private partial def renderTy : SFTy → String
  | .var name => name
  | .arr a b => s!"({renderTy a} -> {renderTy b})"
  | .all name body => s!"forall {name}. {renderTy body}"

private partial def inferType (ctx : SFContext) : SFTm → Except KernelError SFTy
  | .var x =>
      match ctx.lookup? x with
      | some ty => pure ty
      | none => throw (.unknownTermVariable x)
  | .lam x ty body => do
      let bodyTy <- inferType ((x, ty) :: ctx) body
      pure (.arr ty bodyTy)
  | .app fn arg => do
      let fnTy <- inferType ctx fn
      match fnTy with
      | .arr premise result =>
          let argTy <- inferType ctx arg
          unless Logic.SystemF.Ty.eq premise argTy do
            throw (.typeMismatch premise argTy)
          pure result
      | other => throw (.expectedFunction other)
  | .tyLam p body => do
      if p ∈ ctx.freeTyVars then
        throw (.typeVariableEscapesContext p)
      let bodyTy <- inferType ctx body
      pure (.all p bodyTy)
  | .tyApp fn ty => do
      let fnTy <- inferType ctx fn
      match fnTy with
      | .all p body =>
          match Logic.SystemF.Ty.subst? p ty body with
          | .ok instantiated => pure instantiated
          | .error err => throw (.typeSubstitutionError err)
      | other => throw (.expectedForall other)

private def checkCertificateRaw (_profile : Profile) (goal : Goal) (certificate : Certificate) :
    Except KernelError CheckedCertificate := do
  let actual <- inferType goal.context certificate
  unless Logic.SystemF.Ty.eq goal.target actual do
    throw (.typeMismatch goal.target actual)
  pure {
    profile := {}
    goal
    certificate
    summary := "Checked System F typing certificate."
  }

def renderKernelError : KernelError → String
  | .unknownTermVariable name => s!"Unknown term variable `{name}`."
  | .expectedFunction _ => "Expected a term of function type."
  | .expectedForall _ => "Expected a term of polymorphic forall type."
  | .typeMismatch expected actual => s!"System F type mismatch: expected {renderTy expected}, got {renderTy actual}."
  | .typeSubstitutionError message => s!"Invalid type substitution: {message}"
  | .typeVariableEscapesContext name => s!"Type variable `{name}` occurs free in the context."

instance : FastProofTheory.Core.ProofKernel Profile Goal Certificate KernelError where
  kind := .naturalDeduction
  check := checkCertificateRaw
  renderError := renderKernelError

def checkCertificate (profile : Profile) (goal : Goal) (certificate : Certificate) :
    Except KernelError CheckedCertificate :=
  FastProofTheory.Core.checkCertificate profile goal certificate

def checkClosedTheorem (target : SFTy) (certificate : Certificate) :
    Except KernelError CheckedCertificate :=
  checkCertificate {} { context := [], target } certificate

end FastProofTheory.SystemF
