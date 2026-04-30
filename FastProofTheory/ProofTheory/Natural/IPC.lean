import FastProofTheory.IPC.PropositionalND
import FastProofTheory.IPC.FirstOrderND
import FastProofTheory.ProofTheory.Natural.IPC.Certificate
import FastProofTheory.ProofTheory.Natural.IPC.Elaborator

namespace FastProofTheory.ProofTheory.Natural.IPC

abbrev PropositionalDerivation (α : Type) := FastProofTheory.IPC.PropositionalND.Derivation (α := α)
abbrev FirstOrderDerivation := FastProofTheory.IPC.FirstOrderND.Derivation

end FastProofTheory.ProofTheory.Natural.IPC
