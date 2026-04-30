import FastProofTheory.ProofTheory.Natural.IPC.Elaborator

namespace FastProofTheory.ProofTheory.Natural.IPC.Examples

open FastProofTheory.IPC

inductive Atom where
  | p
  | q
  | r
deriving DecidableEq, Repr

def p : Formula Atom := .atom .p
def q : Formula Atom := .atom .q
def r : Formula Atom := .atom .r

def pImpP : Certificate :=
  .impRight .init

def swapAnd : Certificate :=
  .impRight (.andLeft (.andRight .init .init))

end FastProofTheory.ProofTheory.Natural.IPC.Examples
