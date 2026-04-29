import Logic.IPC.Soundness

namespace FastProofTheory.IPC.ZadlittProblem1Negative

open Logic.IPC
open Logic.IPC.Kripke

def a : Formula := .atom "a"
def b : Formula := .atom "b"
def c : Formula := .atom "c"

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

def branchFrame : Frame where
  World := W
  le := branchLe
  refl := by
    intro w
    cases w <;> trivial
  trans := by
    intro u v w huv hvw
    cases u <;> cases v <;> cases w <;> trivial

private def abcVal : String → W → Prop
  | "a", .left => True
  | "a", .right => True
  | "b", .left => True
  | "c", .right => True
  | _, _ => False

private def abcModel : Model where
  toFrame := branchFrame
  val := abcVal
  mono := by
    intro p u v huv hp
    by_cases hpa : p = "a"
    · subst hpa
      cases u <;> cases v <;> simp [abcVal, branchLe] at hp ⊢ <;> try contradiction <;> try trivial
    · by_cases hpb : p = "b"
      · subst hpb
        cases u <;> cases v <;> simp [abcVal, branchLe] at hp ⊢ <;> try contradiction <;> try trivial
      · by_cases hpc : p = "c"
        · subst hpc
          cases u <;> cases v <;> simp [abcVal, branchLe] at hp ⊢ <;> try contradiction <;> try trivial
        · cases u <;> cases v <;> simp [abcVal, branchLe, hpa, hpb, hpc] at hp ⊢ <;> try contradiction <;> try trivial

private theorem abc_root_forces_antecedent :
    Forces abcModel W.root (a -> (b ∨ c)) := by
  intro v hv ha
  cases v with
  | root =>
      have hfalse : False := by
        simpa [abcModel, abcVal, branchLe] using ha
      exact False.elim hfalse
  | left =>
      exact Or.inl trivial
  | right =>
      exact Or.inr trivial

private theorem abc_root_not_forces_a_imp_b :
    ¬ Forces abcModel W.root (a -> b) := by
  intro h
  have ha : Forces abcModel W.right a := by
    change abcVal "a" W.right
    simp [abcVal]
  have hb := h W.right trivial ha
  change False at hb
  exact hb

private theorem abc_root_not_forces_a_imp_c :
    ¬ Forces abcModel W.root (a -> c) := by
  intro h
  have ha : Forces abcModel W.left a := by
    change abcVal "a" W.left
    simp [abcVal]
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

private def triVal : String → W → Prop
  | "a", .left => True
  | _, _ => False

private def triModel : Model where
  toFrame := branchFrame
  val := triVal
  mono := by
    intro p u v huv hp
    by_cases hpa : p = "a"
    · subst hpa
      cases u <;> cases v <;> simp [triVal, branchLe] at hp ⊢ <;> try contradiction <;> try trivial
    · cases u <;> cases v <;> simp [triVal, branchLe, hpa] at hp ⊢ <;> try contradiction <;> try trivial

private theorem tri_left_forces_double_neg :
    Forces triModel W.left (((a -> ⊥) -> ⊥)) := by
  intro v hv hna
  cases v with
  | root =>
      have hfalse : False := by
        simpa [triModel, triVal, branchLe] using hv
      exact False.elim hfalse
  | left =>
      exact hna W.left trivial (by change triVal "a" W.left; trivial)
  | right =>
      have hfalse : False := by
        simpa [triModel, triVal, branchLe] using hv
      exact False.elim hfalse

private theorem tri_right_forces_neg :
    Forces triModel W.right (a -> ⊥) := by
  intro v hv ha
  cases v with
  | root =>
      have hfalse : False := by
        simpa [triModel, triVal, branchLe] using hv
      exact False.elim hfalse
  | left =>
      have hfalse : False := by
        simpa [triModel, triVal, branchLe] using hv
      exact False.elim hfalse
  | right =>
      have hfalse : False := by
        simpa [triModel, triVal, branchLe] using ha
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
