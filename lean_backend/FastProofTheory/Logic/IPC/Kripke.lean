import FastProofTheory.Logic.IPC.Language

namespace FastProofTheory.Logic.IPC.Kripke

open Rules
open FastProofTheory.Logic.IPC

universe u

structure Frame where
  World : Type u
  le : World → World → Prop
  refl : ∀ w, le w w
  trans : ∀ {u v w}, le u v → le v w → le u w

structure Model extends Frame where
  val : String → World → Prop
  mono :
    ∀ {p : String} {w v : World},
      le w v → val p w → val p v

abbrev Formula := Rules.Formula

def Forces (M : Model) : M.World → Formula → Prop
  | w, .atom p => M.val p w
  | _, .bot => False
  | w, .and a b => Forces M w a ∧ Forces M w b
  | w, .or a b => Forces M w a ∨ Forces M w b
  | w, .imp a b => ∀ v, M.le w v → Forces M v a → Forces M v b
  | _, _ => False

def Refutes (M : Model) (w : M.World) (A : Formula) : Prop :=
  ¬ Forces M w A

def ValidAt (M : Model) (w : M.World) (A : WellFormed fragment) : Prop :=
  Forces M w A.1

def GloballyValid (M : Model) (A : WellFormed fragment) : Prop :=
  ∀ w, ValidAt M w A

def Entails (M : Model) (Γ : List (WellFormed fragment)) (A : WellFormed fragment) : Prop :=
  ∀ w, (∀ B ∈ Γ, ValidAt M w B) → ValidAt M w A

def ValidOnFrame (F : Frame) (A : WellFormed fragment) : Prop :=
  ∀ (val : String → F.World → Prop)
    (mono : ∀ {p : String} {w v : F.World}, F.le w v → val p w → val p v),
      let M : Model := { toFrame := F, val := val, mono := mono }
      GloballyValid M A

end FastProofTheory.Logic.IPC.Kripke
