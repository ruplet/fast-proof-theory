import Lean.Data.Json

open Lean

structure JsonRpcRequest where
  jsonrpc : String
  id : Json
  method : String
  params : Json := Json.null
deriving FromJson

structure JsonRpcError where
  code : Int
  message : String
deriving ToJson

structure JsonRpcFailure where
  id : Json
  jsonrpc : String := "2.0"
  error : JsonRpcError
deriving ToJson

structure JsonRpcSuccess where
  id : Json
  jsonrpc : String := "2.0"
  result : Json
deriving ToJson

private def usage : String := String.intercalate "\n" [
  "usage: lake exe fast-proof-theory <command>",
  "",
  "commands:",
  "  kernel      read one JSON-RPC request from stdin",
  "  proof-info  print available Lean proof systems"
]

private def proofInfo : Json :=
  Json.mkObj [
    ("systems", Json.arr (#[ "FastProofTheory.Proof.NJp", "FastProofTheory.Proof.NKp", "FastProofTheory.Proof.LJp", "FastProofTheory.Proof.LKp", "FastProofTheory.Proof.NJ", "FastProofTheory.Proof.NK", "FastProofTheory.Proof.LJ", "FastProofTheory.Proof.LK", "FastProofTheory.Proof.LinearLogic" ].map Json.str)),
    ("syntax", Json.str "NJp/NKp/LJp/LKp are propositional fragments; NJ/NK/LJ/LK extend them with first-order quantifier rules; LinearLogic uses FastProofTheory.Proof.LinearFormula.")
  ]

private def emitFailure (id : Json) (code : Int) (message : String) : IO Unit := do
  IO.println (toJson ({ id, error := { code, message } } : JsonRpcFailure)).compress

private def emitSuccess (id : Json) (result : Json) : IO Unit := do
  IO.println (toJson ({ id, result } : JsonRpcSuccess)).compress

private def runKernelRpc : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  let json ← match Json.parse input with
    | .ok json => pure json
    | .error err =>
        emitFailure Json.null (-32700) s!"Invalid JSON: {err}"
        return 1
  let request ← match fromJson? (α := JsonRpcRequest) json with
    | .ok request => pure request
    | .error err =>
        emitFailure Json.null (-32600) s!"Invalid request: {err}"
        return 1
  if request.jsonrpc != "2.0" then
    emitFailure request.id (-32600) "Expected jsonrpc=2.0"
    return 1
  match request.method with
  | "domainInfo" | "proofInfo" =>
      emitSuccess request.id proofInfo
      return 0
  | "checkDocument" =>
      emitSuccess request.id <| Json.mkObj [
        ("diagnostics", Json.arr #[]),
        ("goals", Json.arr #[]),
        ("display", Json.mkObj [
          ("title", Json.str "FastProofTheory"),
          ("status", Json.str "The old Lean MyPA checker has been removed; this executable now exposes proof-system metadata only."),
          ("sections", Json.arr #[])
        ]),
        ("theoremStatuses", Json.arr #[])
      ]
      return 0
  | _ =>
      emitFailure request.id (-32601) s!"Unsupported method: {request.method}"
      return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["kernel"] => runKernelRpc
  | ["proof-info"] =>
      IO.println proofInfo.compress
      return 0
  | [] =>
      IO.println usage
      return 0
  | command :: _ =>
      IO.eprintln s!"Unknown command `{command}`.\n{usage}"
      return 2
