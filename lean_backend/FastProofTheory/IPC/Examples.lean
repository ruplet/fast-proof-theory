import FastProofTheory.IPC.Elaborator

namespace FastProofTheory.IPC.Examples

open Logic.IPC

def p : Formula := .atom "p"
def q : Formula := .atom "q"
def r : Formula := .atom "r"

def pImpP : Certificate :=
  .impRight .init

def swapAnd : Certificate :=
  .impRight (.andLeft (.andRight .init .init))

end FastProofTheory.IPC.Examples
