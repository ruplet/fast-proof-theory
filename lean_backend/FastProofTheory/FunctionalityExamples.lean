import FastProofTheory.ProofSystems.IntuitionisticSequentCalculusLJMeta
import Logic
import Logic.SystemF.Typing

/-!
Concise source-level examples for the deep embeddings that are not all exposed
through the MyPA surface checker yet.
-/

namespace FastProofTheory.FunctionalityExamples

open Rules

namespace SystemF

open Logic.SystemF

def p : Ty := .var "p"
def q : Ty := .var "q"

def constTerm : Tm :=
  .tyLam "p" (.tyLam "q" (.lam "x" p (.lam "y" q (.var "x"))))

def constType : Ty :=
  .all "p" (.all "q" (.arr p (.arr q p)))

def constHasType : HasType [] [] constTerm constType := by
  apply HasType.tyLam
  · native_decide
  apply HasType.tyLam
  · native_decide
  apply HasType.lam
  apply HasType.lam
  apply HasType.var
  simp [Context.lookup?]

end SystemF

namespace FirstOrder

open Logic.IPC.FirstOrderND

def px : Rules.Formula := .pred "P" [.var "x"]
def allPx : Rules.Formula := .all "x" px

def instantiateUniversal : Derivation [allPx] (Rules.substFormula "x" (.fn "c" []) px) := by
  exact Derivation.forallElim
    (x := "x")
    (t := .fn "c" [])
    (A := px)
    (Derivation.hyp (by simp [allPx]))

def introduceExistentialFromWitness :
    Derivation [Rules.substFormula "x" (.fn "c" []) px] (.ex "x" px) := by
  exact Derivation.existsIntro
    (x := "x")
    (t := .fn "c" [])
    (A := px)
    (Derivation.hyp (by simp))

end FirstOrder

namespace IntuitionisticGentzen

def projectLeft {A B : Formula} : [Formula.and A B] ⊢ᴸᴶ A := by
  andLeft1
  axiom

def modusPonens {A B : Formula} : [A ⟶ B, A] ⊢ᴸᴶ B := by
  impLeft([A], [])
  · axiom
  · axiom

end IntuitionisticGentzen

namespace LK2

open Logic.LK2

private inductive PredName where
  | p
deriving DecidableEq

private def sig : Signature where
  NumFn := Empty
  StrFn := Empty
  Pred := PredName
  numFnArity := Empty.elim
  strFnArity := Empty.elim
  predArity := fun
    | .p => (1, 0)

private def P (t : NTerm sig) : Formula sig :=
  .pred .p [t] []

def implicationIdentity : Proof sig [] [Formula.imp (P (.var "n")) (P (.var "n"))] := by
  apply Proof.impRight
  exact Proof.axiom

private def atom : Formula sig := P (.var "n")
private def axiomFormula : NonLogicalAxiom sig := .formula atom

def anchoredCut : Proof sig [] [atom] :=
  Proof.cut (Proof.nonLogicalAxiom axiomFormula) Proof.axiom

private theorem anchoredCutNonLogical :
    Proof.nonLogicalAxiomFormulas anchoredCut = [atom] := by
  simp [anchoredCut, Proof.nonLogicalAxiomFormulas, axiomFormula, NonLogicalAxiom.toSequent]

example : Proof.IsAnchored (p := anchoredCut) := by
  intro A h
  simp [anchoredCut, Proof.cutFormulas] at h
  cases h
  rw [anchoredCutNonLogical]
  simp

namespace SingleSorted

def names : Logic.LK2.SingleSorted.Names sig where
  numFn := Empty.elim
  strFn := Empty.elim
  pred := fun
    | .p => "P"

def translatedForallNIdentity : Rules.Formula :=
  Logic.LK2.SingleSorted.toFOFormula names
    (Formula.forallN "x" (Formula.imp (P (.var "x")) (P (.var "x"))))

end SingleSorted

end LK2

end FastProofTheory.FunctionalityExamples
