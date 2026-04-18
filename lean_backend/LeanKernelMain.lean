import FastProofTheoryBackend
import Lean.Data.Json

open Lean
open FastProofTheory.Server

private def emitFailure (id : Json) (code : Int) (message : String) : IO Unit := do
  let payload : JsonRpcFailure := {
    id := id
    error := { code := code, message := message }
  }
  IO.println (toJson payload).compress

private def emitSuccess (id : Json) (result : CheckDocumentResult) : IO Unit := do
  let payload : JsonRpcSuccess := {
    id := id
    result := result
  }
  IO.println (toJson payload).compress

def main : IO Unit := do
  let input <- (← IO.getStdin).readToEnd
  let json <- match Json.parse input with
    | Except.ok json => pure json
    | Except.error err =>
        emitFailure Json.null (-32700) s!"Invalid JSON: {err}"
        return
  let request <- match fromJson? (α := JsonRpcRequest) json with
    | Except.ok req => pure req
    | Except.error err =>
        emitFailure Json.null (-32600) s!"Invalid request: {err}"
        return
  if request.jsonrpc != "2.0" then
    emitFailure request.id (-32600) "Expected jsonrpc=2.0"
    return
  if request.method != "checkDocument" then
    emitFailure request.id (-32601) s!"Unsupported method: {request.method}"
    return
  emitSuccess request.id (checkDocument request.params)
