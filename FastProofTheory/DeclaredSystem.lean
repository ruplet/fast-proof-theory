import FastProofTheory.Gentzen.System
import FastProofTheory.ProofTheory.Natural.System

namespace FastProofTheory

inductive DeclaredSystem where
  | gentzen (system : FastProofTheory.Gentzen.System)
  | njp (fragment : FastProofTheory.ProofTheory.Natural.PropositionalFragment)
  | nkp (fragment : FastProofTheory.ProofTheory.Natural.PropositionalFragment)
  | ljp
  | lkp
  | nj
  | nk
  | lj
  | lk
  | systemF
deriving BEq, DecidableEq, Inhabited, Repr

def DeclaredSystem.displayName : DeclaredSystem → String
  | .gentzen system => system.displayName
  | .njp .imp => "NJp with IMP"
  | .njp .full => "NJp"
  | .nkp .imp => "NKp with IMP"
  | .nkp .full => "NKp"
  | .ljp => "LJp"
  | .lkp => "LKp"
  | .nj => "NJ"
  | .nk => "NK"
  | .lj => "LJ"
  | .lk => "LK"
  | .systemF => "SYSTEM_F"

def DeclaredSystem.languageName : DeclaredSystem → String
  | .gentzen (.linearLogic .ll) => "LL"
  | .gentzen (.linearLogic .llBang) => "LL!"
  | .njp .imp => "NJp with IMP"
  | .njp .full => "NJp"
  | .nkp .imp => "NKp with IMP"
  | .nkp .full => "NKp"
  | .ljp => "LJp"
  | .lkp => "LKp"
  | .nj => "NJ"
  | .nk => "NK"
  | .lj => "LJ"
  | .lk => "LK"
  | .systemF => "SYSTEM_F"

def DeclaredSystem.allowsFormula : DeclaredSystem → FastProofTheory.Gentzen.Formula → Bool
  | .gentzen system, formula => system.allowsFormula formula
  | .njp fragment, formula => FastProofTheory.ProofTheory.Natural.System.njp fragment |>.allowsFormula formula
  | .nkp fragment, formula => FastProofTheory.ProofTheory.Natural.System.nkp fragment |>.allowsFormula formula
  | .ljp, _ => false
  | .lkp, _ => false
  | .nj, _ => false
  | .nk, _ => false
  | .lj, _ => false
  | .lk, _ => false
  | .systemF, formula => FastProofTheory.ProofTheory.Natural.System.systemF.allowsFormula formula

def DeclaredSystem.isLinearGentzen : DeclaredSystem → Bool
  | .gentzen (.linearLogic _) => true
  | _ => false

def DeclaredSystem.isNaturalDeduction : DeclaredSystem → Bool
  | .njp _ => true
  | .nkp _ => true
  | .nj => true
  | .nk => true
  | .systemF => true
  | _ => false

def DeclaredSystem.isNJp : DeclaredSystem → Bool
  | .njp _ => true
  | _ => false

def DeclaredSystem.isNKp : DeclaredSystem → Bool
  | .nkp _ => true
  | _ => false

def DeclaredSystem.isSystemF : DeclaredSystem → Bool
  | .systemF => true
  | _ => false

def DeclaredSystem.hasValidConfiguration : DeclaredSystem → Bool
  | .gentzen (.linearLogic .ll) => true
  | .gentzen (.linearLogic .llBang) => true
  | .njp fragment => (FastProofTheory.ProofTheory.Natural.System.njp fragment).hasValidConfiguration
  | .nkp fragment => (FastProofTheory.ProofTheory.Natural.System.nkp fragment).hasValidConfiguration
  | .systemF => true
  | _ => false

def DeclaredSystem.toLinearLogic? : DeclaredSystem → Option FastProofTheory.Gentzen.LinearLogic
  | .gentzen (.linearLogic logic) => some logic
  | _ => none

def DeclaredSystem.toNDSystem? : DeclaredSystem → Option FastProofTheory.ProofTheory.Natural.System
  | .njp fragment => some (.njp fragment)
  | .nkp fragment => some (.nkp fragment)
  | _ => none

def DeclaredSystem.toGentzenSystem? : DeclaredSystem → Option FastProofTheory.Gentzen.System
  | .gentzen sys => some sys
  | _ => none

private def unavailableMessage : DeclaredSystem → String
  | .ljp => "System `LJp` is recognized, but the sequent-script checker is not wired up yet."
  | .lkp => "System `LKp` is recognized, but the sequent-script checker is not wired up yet."
  | .nj => "System `NJ` is recognized, but first-order quantifier checking is not available yet. Use `NJp` for propositional proofs."
  | .nk => "System `NK` is recognized, but first-order quantifier checking is not available yet. Use `NKp` for propositional proofs."
  | .lj => "System `LJ` is recognized, but first-order quantifier checking is not available yet."
  | .lk => "System `LK` is recognized, but first-order quantifier checking is not available yet."
  | .nkp .imp => "System `NKp with IMP` is not supported yet."
  | _ => "This system is not available yet."

def DeclaredSystem.validationMessage? : DeclaredSystem → Option String
  | system =>
      if system.hasValidConfiguration then none
      else some (unavailableMessage system)

def parseDeclaredSystemTokens (tokens : List String) : Except String DeclaredSystem :=
  match tokens.map String.toUpper with
  | [] =>
      .error "Unsupported logic specification."
  | "LL" :: "IN" :: "GENTZEN" :: "WITH" :: "LL" :: [] =>
      .ok (.gentzen (.linearLogic .ll))
  | "LL!" :: "IN" :: "GENTZEN" :: "WITH" :: "LL!" :: [] =>
      .ok (.gentzen (.linearLogic .llBang))
  | "LL_BANG" :: "IN" :: "GENTZEN" :: "WITH" :: "LL_BANG" :: [] =>
      .ok (.gentzen (.linearLogic .llBang))
  | "NJP" :: [] =>
      .ok (.njp .full)
  | "NJP" :: "WITH" :: "IMP" :: [] =>
      .ok (.njp .imp)
  | "NKP" :: [] =>
      .ok (.nkp .full)
  | "LJP" :: [] =>
      .ok .ljp
  | "LKP" :: [] =>
      .ok .lkp
  | "NJ" :: [] =>
      .ok .nj
  | "NK" :: [] =>
      .ok .nk
  | "LJ" :: [] =>
      .ok .lj
  | "LK" :: [] =>
      .ok .lk
  | "NJ" :: "WITH" :: _ =>
      .error "Use `NJp` for propositional natural deduction; `NJ` does not accept a fragment suffix."
  | "NK" :: "WITH" :: _ =>
      .error "Use `NKp` for propositional natural deduction; `NK` does not accept a fragment suffix."
  | "LJ" :: "WITH" :: _ =>
      .error "Use `LJp` for propositional sequent calculus; `LJ` does not accept a fragment suffix."
  | "LK" :: "WITH" :: _ =>
      .error "Use `LKp` for propositional sequent calculus; `LK` does not accept a fragment suffix."
  | "IPC" :: _ =>
      .error "Use `NJp` or `NKp` instead of the old `IPC` syntax."
  | "CPC" :: _ =>
      .error "Use `NKp` instead of the old `CPC` syntax."
  | name :: _ =>
      if name.startsWith "G3" then
        .error "G3 systems are not available in the product docs or checker yet."
      else if name = "SYSTEM_F" || name = "SYSTEMF" then
        match tokens.map String.toUpper with
        | "SYSTEM_F" :: "IN" :: "ND" :: [] => .ok .systemF
        | "SYSTEMF" :: "IN" :: "ND" :: [] => .ok .systemF
        | "SYSTEM_F" :: "IN" :: "ND" :: "WITH" :: "SYSTEM_F" :: [] => .ok .systemF
        | "SYSTEMF" :: "IN" :: "ND" :: "WITH" :: "SYSTEMF" :: [] => .ok .systemF
        | _ => .error "Use `SYSTEM_F in ND` for System F."
      else
        .error s!"Unsupported logic specification `{String.intercalate " " tokens}`."

def parseDeclaredSystemTokens? (tokens : List String) : Option DeclaredSystem :=
  match parseDeclaredSystemTokens tokens with
  | .ok system => some system
  | .error _ => none

end FastProofTheory
