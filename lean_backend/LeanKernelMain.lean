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

private def emitSuccess (id : Json) (result : Json) : IO Unit := do
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
  match request.method with
  | "checkDocument" =>
      let params <- match fromJson? (α := CheckDocumentParams) request.params with
        | Except.ok params => pure params
        | Except.error err =>
            emitFailure request.id (-32602) s!"Invalid checkDocument params: {err}"
            return
      emitSuccess request.id (toJson (checkDocument params))
  | "domainInfo" =>
      emitSuccess request.id (toJson domainInfo)
  | _ =>
      emitFailure request.id (-32601) s!"Unsupported method: {request.method}"
      return
