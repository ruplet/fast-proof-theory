import FastProofTheory.Proof.NJ

open FirstOrder

namespace FastProofTheory.Proof

universe u v w

variable {L : FirstOrder.Language.{u, v}}
variable {α : Type w}
variable [DecidableEq α]

inductive NKp : List (L.Formula α) → L.Formula α → Prop where
  | fromNJp {assumptions formula} :
      NJp assumptions formula →
      NKp assumptions formula

  | excludedMiddle {assumptions formula} :
      NKp assumptions (formula ⊔ neg formula)

inductive NK : List (L.Formula α) → L.Formula α → Prop where
  | fromNKp {assumptions formula} :
      NKp assumptions formula →
      NK assumptions formula

  | fromNJ {assumptions formula} :
      NJ assumptions formula →
      NK assumptions formula

  | excludedMiddle {assumptions formula} :
      NK assumptions (formula ⊔ neg formula)

end FastProofTheory.Proof
