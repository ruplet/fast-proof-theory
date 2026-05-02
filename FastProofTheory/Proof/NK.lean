import FastProofTheory.Proof.NJ

open FirstOrder

namespace FastProofTheory.Proof

universe u v w

variable {L : FirstOrder.Language.{u, v}}
variable {α : Type w}
variable [DecidableEq α]

inductive NK : List (L.Formula α) → L.Formula α → Prop where
  | fromNJ {assumptions formula} :
      NJ assumptions formula →
      NK assumptions formula

  | excludedMiddle {assumptions formula} :
      NK assumptions (formula ⊔ neg formula)

end FastProofTheory.Proof
