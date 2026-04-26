import FastProofTheory.DeclaredSystem
import FastProofTheory.ND.Kernel
import FastProofTheory.Linear.Kernel

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

example : Rules.Formula.allNames nestedCaptureSubst = ["z", "y''", "y'", "y"] := by
  native_decide

def classicalProof : FastProofTheory.ND.Certificate :=
  FastProofTheory.ND.Certificate.impIntro "h" (.imp notP .bot)
    (FastProofTheory.ND.Certificate.classical "na" p
      (FastProofTheory.ND.Certificate.impElim notP
        (FastProofTheory.ND.Certificate.hyp "h")
        (FastProofTheory.ND.Certificate.hyp "na")))

def badFreshProof : FastProofTheory.ND.Certificate :=
  FastProofTheory.ND.Certificate.impIntro "hp" (.atom "p")
    (FastProofTheory.ND.Certificate.forallIntro "p"
      (FastProofTheory.ND.Certificate.hyp "hp"))

example : isError (FastProofTheory.ND.checkClosedTheorem .systemF (.imp (.atom "p") (.all "p" (.atom "p"))) badFreshProof) = true := by
  native_decide

def forallElimCaptureProof : FastProofTheory.ND.Certificate :=
  FastProofTheory.ND.Certificate.impIntro "h"
    (.all "x" (.all "y" (.all "y'" (.imp (.atom "x") (.imp (.atom "y") (.atom "y'"))))))
    (FastProofTheory.ND.Certificate.forallElim "x" (.atom "y")
      (.all "y" (.all "y'" (.imp (.atom "x") (.imp (.atom "y") (.atom "y'")))))
      (FastProofTheory.ND.Certificate.hyp "h"))

example :
    isError (FastProofTheory.ND.checkClosedTheorem .systemF
      (.imp
        (.all "x" (.all "y" (.all "y'" (.imp (.atom "x") (.imp (.atom "y") (.atom "y'"))))))
        (.all "y''" (.all "y'" (.imp (.atom "y") (.imp (.atom "y''") (.atom "y'"))))))
      forallElimCaptureProof) = false := by
  native_decide

example : isError (FastProofTheory.ND.checkClosedTheorem (.nkp .full) (.imp (.imp notP .bot) p) classicalProof) = false := by
  native_decide

example : isError (FastProofTheory.ND.checkClosedTheorem (.njp .full) (.imp (.imp notP .bot) p) classicalProof) = true := by
  native_decide

example : isError (checkCertificate .ll atomGoal Certificate.assumption) = false := by
  native_decide

example : isError (checkCertificate .ll bangGoal (Certificate.bangIntro Certificate.oneIntro)) = true := by
  native_decide

example : isError (checkCertificate .ll tensorGoal (Certificate.tensorIntro (.explicit [] []) Certificate.assumption Certificate.assumption)) = true := by
  native_decide

end FastProofTheory.Linear.KernelAudit
