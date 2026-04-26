namespace FastProofTheory.Core

inductive CheckerKind where
  | naturalDeduction
  | gentzenSequent
deriving BEq, DecidableEq, Repr

def CheckerKind.displayName : CheckerKind → String
  | .naturalDeduction => "natural deduction"
  | .gentzenSequent => "Gentzen sequent calculus"

/--
The uniform result type returned by trusted proof-kernel checks.

`System`, `Goal`, and `Certificate` are intentionally parameters. A logic may
have its own judgment shape and certificate syntax, but a successful check always
means that a certificate was accepted for a goal under a selected system.
-/
structure CheckedCertificate
    (System : Type u)
    (Goal : Type v)
    (Certificate : Type w) where
  system : System
  goal : Goal
  certificate : Certificate
  summary : String

/--
A proof system becomes trusted by implementing this interface.

The rest of the assistant may parse scripts, run tactics, and search for proofs,
but completion must be justified by calling `check` here. This is the shared
kernel boundary for linear logic, natural deduction systems, System F, and future
systems.
-/
class ProofKernel
    (System : Type u)
    (Goal : Type v)
    (Certificate : Type w)
    (Error : Type x) where
  kind : CheckerKind
  check :
    System →
    Goal →
    Certificate →
    Except Error (CheckedCertificate System Goal Certificate)
  renderError : Error → String

def checkCertificate
    {System : Type u}
    {Goal : Type v}
    {Certificate : Type w}
    {Error : Type x}
    [ProofKernel System Goal Certificate Error]
    (system : System)
    (goal : Goal)
    (certificate : Certificate) :
    Except Error (CheckedCertificate System Goal Certificate) :=
  ProofKernel.check system goal certificate

def checkerKind
    {System : Type u}
    {Goal : Type v}
    {Certificate : Type w}
    {Error : Type x}
    [ProofKernel System Goal Certificate Error] :
    CheckerKind :=
  ProofKernel.kind
    (System := System)
    (Goal := Goal)
    (Certificate := Certificate)
    (Error := Error)

def renderKernelError
    {System : Type u}
    {Goal : Type v}
    {Certificate : Type w}
    {Error : Type x}
    [ProofKernel System Goal Certificate Error]
    (err : Error) : String :=
  ProofKernel.renderError
    (System := System)
    (Goal := Goal)
    (Certificate := Certificate)
    (Error := Error)
    err

end FastProofTheory.Core
