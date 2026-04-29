import Logic.IPC.G3i

namespace FastProofTheory.IPC

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

end FastProofTheory.IPC
