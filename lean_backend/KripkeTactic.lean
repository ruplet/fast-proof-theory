import FastProofTheory.IPC.Unprovability
import Logic.IPC.Countermodel

namespace KripkeTactic.IPC

open scoped Logic.IPC

abbrev Formula := Logic.IPC.Formula
abbrev Context := Logic.IPC.Context
abbrev Derivation := Logic.IPC.Derivation
abbrev Countermodel := Logic.IPC.Countermodel.Countermodel

abbrev Unprovable (A : Formula) : Prop :=
  Not (Nonempty (Derivation [] A))

theorem countermodel_not_derivable (c : Countermodel) :
    Unprovable c.formula :=
  Logic.IPC.Countermodel.countermodel_not_derivable c

end KripkeTactic.IPC
