import FastProofTheory.IPC.Derivation

namespace FastProofTheory.ProofTheory.Natural.IPC

inductive Certificate where
  | init
  | botLeft
  | exchange (body : Certificate)
  | impRight (body : Certificate)
  | impLeft (premise : Certificate) (body : Certificate)
  | andRight (left right : Certificate)
  | andLeft (body : Certificate)
  | orRightLeft (body : Certificate)
  | orRightRight (body : Certificate)
  | orLeft (left right : Certificate)
deriving Repr

end FastProofTheory.ProofTheory.Natural.IPC
