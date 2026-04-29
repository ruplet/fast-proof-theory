import Logic.IPC.Countermodel

namespace Demo.Problemset.IPC

open Logic.IPC

def p : Formula := .atom "p"
def q : Formula := .atom "q"

def neg (A : Formula) : Formula := .imp A .bot

-- Problem 1(a): countermodel
def pOrNotP : Formula := p ∨ neg p

-- Problem 1(b): theorem
def p_imp_p : Derivation [] (p -> p) :=
  .impRight (.init (by decide))

-- Problem 1(c): theorem
def and_comm : Derivation [] ((p ∧ q) -> (q ∧ p)) :=
  .impRight (.andLeft (.andRight (.init (by decide)) (.init (by decide))))

-- Problem 1(d): theorem
def or_comm : Derivation [] ((p ∨ q) -> (q ∨ p)) :=
  .impRight (
    .orLeft
      (.orRightRight (.init (by decide)))
      (.orRightLeft (.init (by decide))))

end Demo.Problemset.IPC
