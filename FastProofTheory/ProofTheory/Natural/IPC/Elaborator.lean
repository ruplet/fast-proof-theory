import FastProofTheory.ProofTheory.Natural.IPC.Certificate

namespace FastProofTheory.ProofTheory.Natural.IPC

inductive Error where
  | initMismatch
  | botLeftMissing
  | exchangeExpectedPair
  | impRightExpectedImplication
  | impLeftExpectedImplication
  | andLeftExpectedConjunction
  | orLeftExpectedDisjunction
deriving Repr

def elaborate [DecidableEq α] (Γ : FastProofTheory.IPC.Context α) (A : FastProofTheory.IPC.Formula α) :
    Certificate -> Except Error (FastProofTheory.IPC.Derivation Γ A)
  | .init =>
      if h : A ∈ Γ then
        .ok (.init h)
      else
        .error .initMismatch
  | .botLeft =>
      if h : FastProofTheory.IPC.Formula.bot ∈ Γ then
        .ok (.botLeft h)
      else
        .error .botLeftMissing
  | .exchange body =>
      match Γ with
      | b :: a :: Γ' =>
          do
            let d ← elaborate (a :: b :: Γ') A body
            .ok (FastProofTheory.IPC.Derivation.exchange (Γ₁ := []) (Γ₂ := Γ') (A := a) (B := b) (C := A) d)
      | _ =>
          .error .exchangeExpectedPair
  | .impRight body =>
      match A with
      | .imp a b =>
          do
            let d ← elaborate (a :: Γ) b body
            .ok (.impRight d)
      | _ =>
          .error .impRightExpectedImplication
  | .impLeft premise body =>
      match Γ with
      | .imp a b :: Γ' =>
          do
            let dp ← elaborate Γ' a premise
            let db ← elaborate (b :: Γ') A body
            .ok (.impLeft dp db)
      | _ =>
          .error .impLeftExpectedImplication
  | .andRight left right =>
      match A with
      | .and a b =>
          do
            let dl ← elaborate Γ a left
            let dr ← elaborate Γ b right
            .ok (.andRight dl dr)
      | _ =>
          .error .andLeftExpectedConjunction
  | .andLeft body =>
      match Γ with
      | .and a b :: Γ' =>
          do
            let d ← elaborate (a :: b :: Γ') A body
            .ok (.andLeft d)
      | _ =>
          .error .andLeftExpectedConjunction
  | .orRightLeft body =>
      match A with
      | .or a _ =>
          do
            let d ← elaborate Γ a body
            .ok (.orRightLeft d)
      | _ =>
          .error .orLeftExpectedDisjunction
  | .orRightRight body =>
      match A with
      | .or _ b =>
          do
            let d ← elaborate Γ b body
            .ok (.orRightRight d)
      | _ =>
          .error .orLeftExpectedDisjunction
  | .orLeft left right =>
      match Γ with
      | .or a b :: Γ' =>
          do
            let dl ← elaborate (a :: Γ') A left
            let dr ← elaborate (b :: Γ') A right
            .ok (.orLeft dl dr)
      | _ =>
          .error .orLeftExpectedDisjunction

def check [DecidableEq α] (Γ : FastProofTheory.IPC.Context α) (A : FastProofTheory.IPC.Formula α) (c : Certificate) :
    Except Error Unit := do
  let _ ← elaborate Γ A c
  pure ()

end FastProofTheory.ProofTheory.Natural.IPC
