import FastProofTheory.IPC.Soundness

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
