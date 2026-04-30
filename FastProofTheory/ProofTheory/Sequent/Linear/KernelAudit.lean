import FastProofTheory.DeclaredSystem
import FastProofTheory.ProofTheory.Natural.Kernel
import FastProofTheory.ProofTheory.Sequent.Linear.Kernel

namespace FastProofTheory.Linear.KernelAudit

open Rules
open FastProofTheory.Gentzen

def isError {α β} : Except α β → Bool
  | .ok _ => false
  | .error _ => true

def p : Formula := .atom "p"

def atomGoal : Goal :=
  { unrestricted := [], linear := [p], target := p }

def bangGoal : Goal :=
  { unrestricted := [], linear := [], target := .bang p }

def tensorGoal : Goal :=
  { unrestricted := [], linear := [p, p], target := .tensor p p }

example : DeclaredSystem.toGentzenSystem? (.njp .imp) = none := by
  rfl

def notP : Formula := .imp p .bot

def nestedCaptureFormula : Formula :=
  .all "z" (.all "y" (.all "y'" (.pred "P" [.var "x", .var "y'"])))

def nestedCaptureSubst : Formula :=
  Rules.substFormula "x" (.var "y") nestedCaptureFormula

example : Rules.Formula.allNames nestedCaptureSubst = [("z" : Label), "y''", "y'", "y"] := by
  native_decide

def classicalProof : FastProofTheory.ProofTheory.Natural.Certificate :=
  FastProofTheory.ProofTheory.Natural.Certificate.impIntro "h" (.imp notP .bot)
    (FastProofTheory.ProofTheory.Natural.Certificate.classical "na" p
      (FastProofTheory.ProofTheory.Natural.Certificate.impElim notP
        (FastProofTheory.ProofTheory.Natural.Certificate.hyp "h")
        (FastProofTheory.ProofTheory.Natural.Certificate.hyp "na")))

def badFreshProof : FastProofTheory.ProofTheory.Natural.Certificate :=
  FastProofTheory.ProofTheory.Natural.Certificate.impIntro "hp" (.atom "p")
    (FastProofTheory.ProofTheory.Natural.Certificate.forallIntro "p"
      (FastProofTheory.ProofTheory.Natural.Certificate.hyp "hp"))

example : isError (FastProofTheory.ProofTheory.Natural.checkClosedTheorem .systemF (.imp (.atom "p") (.all "p" (.atom "p"))) badFreshProof) = true := by
  native_decide

def forallElimCaptureProof : FastProofTheory.ProofTheory.Natural.Certificate :=
  FastProofTheory.ProofTheory.Natural.Certificate.impIntro "h"
    (.all "x" (.all "y" (.all "y'" (.imp (.atom "x") (.imp (.atom "y") (.atom "y'"))))))
    (FastProofTheory.ProofTheory.Natural.Certificate.forallElim "x" (.atom "y")
      (.all "y" (.all "y'" (.imp (.atom "x") (.imp (.atom "y") (.atom "y'")))))
      (FastProofTheory.ProofTheory.Natural.Certificate.hyp "h"))

example :
    isError (FastProofTheory.ProofTheory.Natural.checkClosedTheorem .systemF
      (.imp
        (.all "x" (.all "y" (.all "y'" (.imp (.atom "x") (.imp (.atom "y") (.atom "y'"))))))
        (.all "y''" (.all "y'" (.imp (.atom "y") (.imp (.atom "y''") (.atom "y'"))))))
      forallElimCaptureProof) = false := by
  native_decide

example : isError (FastProofTheory.ProofTheory.Natural.checkClosedTheorem (.nkp .full) (.imp (.imp notP .bot) p) classicalProof) = false := by
  native_decide

example : isError (FastProofTheory.ProofTheory.Natural.checkClosedTheorem (.njp .full) (.imp (.imp notP .bot) p) classicalProof) = true := by
  native_decide

example : isError (checkCertificate .ll atomGoal Certificate.assumption) = false := by
  native_decide

example : isError (checkCertificate .ll bangGoal (Certificate.bangIntro Certificate.oneIntro)) = true := by
  native_decide

example : isError (checkCertificate .ll tensorGoal (Certificate.tensorIntro (.explicit [] []) Certificate.assumption Certificate.assumption)) = true := by
  native_decide

end FastProofTheory.Linear.KernelAudit
