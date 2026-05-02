import FastProofTheory
import FastProofTheory.IPC.Countermodel
import FastProofTheory.IPC.Soundness
import FastProofTheory.ProofTheory.Sequent.IPC.LJMeta
import FastProofTheory.SystemF.Typing

/-!
Consolidated examples migrated from `demo/*.lean` and
`demo/UrzyczynProblemSet/Problem6.lean`.
-/

namespace Demo.FunctionalityExamples

open Rules

namespace SystemF

open FastProofTheory.SystemF

def p : Ty := .var "p"
def q : Ty := .var "q"

def constTerm : Tm :=
  .tyLam "p" (.tyLam "q" (.lam "x" p (.lam "y" q (.var "x"))))

def constType : Ty :=
  .all "p" (.all "q" (.arr p (.arr q p)))

def constHasType : HasType FastProofTheory.SystemF.Label [] [] constTerm constType := by
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

open FastProofTheory.IPC.FirstOrderND

private def x : Label := "x"
private def c : Label := "c"
private def predP : Label := "P"

def px : Rules.Formula := .pred predP [.var x]
def allPx : Rules.Formula := .all x px

def instantiateUniversal : Derivation [allPx] (Rules.substFormula x (.fn c []) px) := by
  exact Derivation.forallElim
    (x := x)
    (t := .fn c [])
    (A := px)
    (Derivation.hyp (by simp [allPx]))

def introduceExistentialFromWitness :
    Derivation [Rules.substFormula x (.fn c []) px] (.ex x px) := by
  exact Derivation.existsIntro
    (x := x)
    (t := .fn c [])
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

open FastProofTheory.LK2

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

def names : FastProofTheory.LK2.SingleSorted.Names sig where
  numFn := Empty.elim
  strFn := Empty.elim
  pred := fun
    | .p => "P"

def translatedForallNIdentity : Rules.Formula :=
  FastProofTheory.LK2.SingleSorted.toFOFormula names
    (Formula.forallN "x" (Formula.imp (P (.var "x")) (P (.var "x"))))

end SingleSorted

end LK2

end Demo.FunctionalityExamples

namespace Demo.Problemset.IPC

open FastProofTheory.IPC

inductive Atom where
  | p
  | q
deriving DecidableEq, Repr

def p : Formula Atom := .atom .p
def q : Formula Atom := .atom .q

def neg (A : Formula Atom) : Formula Atom := .imp A .bot

def pOrNotP : Formula Atom := p ∨ neg p

def p_imp_p : Derivation [] (p -> p) :=
  .impRight (.init (by decide))

def and_comm : Derivation [] ((p ∧ q) -> (q ∧ p)) :=
  .impRight (.andLeft (.andRight (.init (by decide)) (.init (by decide))))

def or_comm : Derivation [] ((p ∨ q) -> (q ∨ p)) :=
  .impRight (
    .orLeft
      (.orRightRight (.init (by decide)))
      (.orRightLeft (.init (by decide))))

end Demo.Problemset.IPC

namespace FastProofTheory.IPC.ZadlittProblem1Negative

open FastProofTheory.IPC
open FastProofTheory.IPC.Kripke

inductive Atom where
  | a
  | b
  | c
deriving DecidableEq, Repr

def a : Formula Atom := .atom .a
def b : Formula Atom := .atom .b
def c : Formula Atom := .atom .c

inductive W where
  | root
  | left
  | right
deriving DecidableEq, Repr

def branchLe : W → W → Prop
  | .root, _ => True
  | .left, .left => True
  | .right, .right => True
  | _, _ => False

private def abcForces : W → Atom → Prop
  | .left, .a => True
  | .right, .a => True
  | .left, .b => True
  | .right, .c => True
  | _, _ => False

private def abcModel : Model Atom where
  World := W
  le := branchLe
  refl := by
    intro w
    cases w <;> trivial
  trans := by
    intro u v w huv hvw
    cases u <;> cases v <;> cases w <;> trivial
  forces := abcForces
  mono := by
    intro atom u v huv hp
    cases atom <;> cases u <;> cases v <;> simp [abcForces, branchLe] at huv hp ⊢

private theorem abc_root_forces_antecedent :
    Forces abcModel W.root (a -> (b ∨ c)) := by
  intro v hv ha
  cases v with
  | root =>
      have hfalse : False := by
        simpa [abcModel, abcForces, branchLe] using ha
      exact False.elim hfalse
  | left =>
      exact Or.inl trivial
  | right =>
      exact Or.inr trivial

private theorem abc_root_not_forces_a_imp_b :
    ¬ Forces abcModel W.root (a -> b) := by
  intro h
  have ha : Forces abcModel W.right a := by
    change abcForces W.right Atom.a
    simp [abcForces]
  have hb := h W.right trivial ha
  change False at hb
  exact hb

private theorem abc_root_not_forces_a_imp_c :
    ¬ Forces abcModel W.root (a -> c) := by
  intro h
  have ha : Forces abcModel W.left a := by
    change abcForces W.left Atom.a
    simp [abcForces]
  have hc := h W.left trivial ha
  change False at hc
  exact hc

theorem abc_root_refutes :
    ¬ Forces abcModel W.root ((a -> (b ∨ c)) -> ((a -> b) ∨ (a -> c))) := by
  intro h
  have hcons : Forces abcModel W.root ((a -> b) ∨ (a -> c)) :=
    h W.root trivial abc_root_forces_antecedent
  cases hcons with
  | inl hb => exact abc_root_not_forces_a_imp_b hb
  | inr hc => exact abc_root_not_forces_a_imp_c hc

theorem problem1a_not_derivable :
    Not (Nonempty (Derivation [] ((a -> (b ∨ c)) -> ((a -> b) ∨ (a -> c))))) := by
  intro h
  rcases h with ⟨d⟩
  have hforces : Forces abcModel W.root ((a -> (b ∨ c)) -> ((a -> b) ∨ (a -> c))) :=
    sound d (M := abcModel) (w := W.root) (by intro v hv A hA; cases hA)
  exact abc_root_refutes hforces

private def triForces : W → Atom → Prop
  | .left, .a => True
  | _, _ => False

private def triModel : Model Atom where
  World := W
  le := branchLe
  refl := by
    intro w
    cases w <;> trivial
  trans := by
    intro u v w huv hvw
    cases u <;> cases v <;> cases w <;> trivial
  forces := triForces
  mono := by
    intro atom u v huv hp
    cases atom <;> cases u <;> cases v <;> simp [triForces, branchLe] at huv hp ⊢

private theorem tri_left_forces_double_neg :
    Forces triModel W.left (((a -> ⊥) -> ⊥)) := by
  intro v hv hna
  cases v with
  | root =>
      have hfalse : False := by
        simpa [triModel, triForces, branchLe] using hv
      exact False.elim hfalse
  | left =>
      exact hna W.left trivial (by change triForces W.left Atom.a; trivial)
  | right =>
      have hfalse : False := by
        simpa [triModel, triForces, branchLe] using hv
      exact False.elim hfalse

private theorem tri_right_forces_neg :
    Forces triModel W.right (a -> ⊥) := by
  intro v hv ha
  cases v with
  | root =>
      have hfalse : False := by
        simpa [triModel, triForces, branchLe] using hv
      exact False.elim hfalse
  | left =>
      have hfalse : False := by
        simpa [triModel, triForces, branchLe] using hv
      exact False.elim hfalse
  | right =>
      have hfalse : False := by
        simpa [triModel, triForces, branchLe] using ha
      exact False.elim hfalse

private theorem tri_root_not_double_neg :
    ¬ Forces triModel W.root (((a -> ⊥) -> ⊥)) := by
  intro h
  exact h W.right trivial tri_right_forces_neg

private theorem tri_root_not_triple_neg :
    ¬ Forces triModel W.root ((((a -> ⊥) -> ⊥) -> ⊥)) := by
  intro h
  exact h W.left trivial tri_left_forces_double_neg

theorem tri_root_refutes :
    ¬ Forces triModel W.root ((((a -> ⊥) -> ⊥) ∨ (((a -> ⊥) -> ⊥) -> ⊥))) := by
  intro h
  cases h with
  | inl h1 => exact tri_root_not_double_neg h1
  | inr h2 => exact tri_root_not_triple_neg h2

theorem problem1d_not_derivable :
    Not (Nonempty (Derivation [] ((((a -> ⊥) -> ⊥) ∨ (((a -> ⊥) -> ⊥) -> ⊥))))) := by
  intro h
  rcases h with ⟨d⟩
  have hforces : Forces triModel W.root ((((a -> ⊥) -> ⊥) ∨ (((a -> ⊥) -> ⊥) -> ⊥))) :=
    sound d (M := triModel) (w := W.root) (by intro v hv A hA; cases hA)
  exact tri_root_refutes hforces

end FastProofTheory.IPC.ZadlittProblem1Negative

namespace Demo.ZadlittProblem2_3.Negative

open FastProofTheory.IPC
open FastProofTheory.IPC.Countermodel

inductive Atom where
  | p
deriving DecidableEq, Repr

def p : Formula Atom := .atom .p

private def frame : FiniteFrame where
  n := 1
  le := fun _ _ => true
  refl := by intro w; decide
  trans := by intro u v w huv hvw; decide

private def model : FiniteModel Atom where
  toFiniteFrame := frame
  val := fun _ _ => false
  mono := by
    intro atom u v huv hp
    simp at hp

def counterP : Countermodel Atom where
  M := model
  root := ⟨0, by decide⟩
  formula := p
  refutes := by
    unfold FastProofTheory.IPC.Countermodel.eval
    simp [model, frame]
    intro h
    cases h

theorem p_not_derivable :
    ¬ Nonempty (Derivation [] p) := by
  exact countermodel_not_derivable counterP

end Demo.ZadlittProblem2_3.Negative

namespace Demo.UrzyczynProblemSet.Problem6

open FastProofTheory.IPC
open FastProofTheory.IPC.Kripke

inductive Atom where
  | p
  | q
deriving DecidableEq, Repr

def p : Formula Atom := .atom .p
def q : Formula Atom := .atom .q

def hosoi : Formula Atom := .or p (.or (.imp q .bot) (.imp p q))

private inductive World where
  | root
  | qBranch
  | pBranch
deriving DecidableEq, Repr

private def le : World → World → Prop
  | .root, _ => True
  | .qBranch, .qBranch => True
  | .pBranch, .pBranch => True
  | _, _ => False

private def atomForces : World → Atom → Prop
  | .qBranch, .q => True
  | .pBranch, .p => True
  | _, _ => False

private def model : Model Atom where
  World := World
  le := le
  refl := by
    intro w
    cases w <;> trivial
  trans := by
    intro u v w huv hvw
    cases u <;> cases v <;> cases w <;> trivial
  forces := atomForces
  mono := by
    intro atom u v huv hp
    cases u <;> cases v <;> simp [le, atomForces] at huv hp ⊢ <;> assumption

private theorem root_not_forces_hosoi :
    ¬ Forces model World.root hosoi := by
  intro h
  rcases h with hp | hnq | hpq
  · exact hp
  · exact hnq World.qBranch trivial trivial
  · exact hpq World.pBranch trivial trivial

theorem hosoi_not_derivable :
    ¬ Nonempty (Derivation [] hosoi) := by
  intro h
  rcases h with ⟨d⟩
  have hforces : Forces model World.root hosoi :=
    sound d (M := model) (w := World.root) (by intro v hv A hA; cases hA)
  exact root_not_forces_hosoi hforces

end Demo.UrzyczynProblemSet.Problem6
