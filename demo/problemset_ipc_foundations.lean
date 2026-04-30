import FastProofTheory.IPC.Countermodel

namespace Demo.Problemset.IPC

open FastProofTheory.IPC

inductive Atom where
  | p
  | q
deriving DecidableEq, Repr

def p : Formula Atom := .atom .p
def q : Formula Atom := .atom .q

def neg (A : Formula Atom) : Formula Atom := .imp A .bot

-- Problem 1(a): countermodel
def pOrNotP : Formula Atom := p ∨ neg p

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
