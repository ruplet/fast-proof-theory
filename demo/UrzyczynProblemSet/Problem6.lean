import FastProofTheory.IPC.Soundness

namespace Demo.UrzyczynProblemSet.Problem6

open FastProofTheory.IPC
open FastProofTheory.IPC.Kripke

inductive Atom where
  | p
  | q
deriving DecidableEq, Repr

def p : Formula Atom := .atom .p
def q : Formula Atom := .atom .q

/-- Problem 6(a), Hosoi's formula: `p ∨ ¬q ∨ (p → q)`. -/
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
