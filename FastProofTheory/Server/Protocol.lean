import Lean.Data.Json

namespace FastProofTheory.Server

open Lean

structure Position where
  line : Nat
  character : Nat
deriving Inhabited, Repr, ToJson, FromJson

structure Range where
  start : Position
  «end» : Position
deriving Inhabited, Repr, ToJson, FromJson

structure Diagnostic where
  range : Range
  severity : Nat
  code : String
  source : String
  message : String
deriving Inhabited, Repr, ToJson, FromJson

structure GoalHypothesis where
  name : String
  type : String
deriving Inhabited, Repr, ToJson, FromJson

structure GoalView where
  id : String
  hypotheses : List GoalHypothesis
  target : String
deriving Inhabited, Repr, ToJson, FromJson

structure TheoremStatus where
  name : String
  line : Nat
  verified : Bool
deriving Inhabited, Repr, ToJson, FromJson

structure DisplaySection where
  title : String
  body : List String
deriving Inhabited, Repr, ToJson, FromJson

structure ProofDisplay where
  title : String
  status : String
  sections : List DisplaySection
deriving Inhabited, Repr, ToJson, FromJson

structure Cursor where
  line : Nat
  character : Nat
deriving Inhabited, Repr, ToJson, FromJson

structure CheckDocumentParams where
  uri : String
  version : Nat
  text : String
  cursor : Option Cursor := none
deriving Inhabited, Repr, ToJson, FromJson

structure CheckDocumentResult where
  diagnostics : List Diagnostic
  goals : List GoalView
  display : ProofDisplay
  theoremStatuses : List TheoremStatus := []
deriving Inhabited, Repr, ToJson, FromJson

structure JsonRpcRequest where
  jsonrpc : String
  id : Json
  method : String
  params : Json := Json.null
deriving Inhabited, ToJson, FromJson

structure JsonRpcError where
  code : Int
  message : String
deriving Inhabited, Repr, ToJson, FromJson

structure JsonRpcSuccess where
  jsonrpc : String := "2.0"
  id : Json
  result : Json
deriving Inhabited, ToJson

structure JsonRpcFailure where
  jsonrpc : String := "2.0"
  id : Json
  error : JsonRpcError
deriving Inhabited, ToJson

def mkPos (line character : Nat) : Position :=
  { line, character }

def mkRange (line start stop : Nat) : Range :=
  { start := mkPos line start, «end» := mkPos line stop }

def mkDiagnostic (line start stop severity : Nat) (code source message : String) : Diagnostic :=
  { range := mkRange line start stop, severity, code, source, message }

end FastProofTheory.Server
