import * as path from "path";
import * as protobuf from "protobufjs";
import { DocumentIR } from "./types";

let rootPromise: Promise<protobuf.Root> | undefined;

function loadRoot(): Promise<protobuf.Root> {
  if (!rootPromise) {
    const protoDir = path.resolve(__dirname, "..", "..", "proto");
    rootPromise = protobuf.load([
      path.join(protoDir, "common.proto"),
      path.join(protoDir, "document_ir.proto"),
      path.join(protoDir, "kernel_rpc.proto"),
    ]);
  }
  return rootPromise;
}

export async function encodeDocumentDelimited(doc: DocumentIR): Promise<Uint8Array> {
  const root = await loadRoot();
  const t = root.lookupType("prover.DocumentIR");
  const err = t.verify(doc);
  if (err) {
    throw new Error(`DocumentIR verify failed: ${err}`);
  }
  return t.encodeDelimited(t.create(doc)).finish();
}

export async function decodeDocumentDelimited(bytes: Uint8Array): Promise<DocumentIR> {
  const root = await loadRoot();
  const t = root.lookupType("prover.DocumentIR");
  const msg = t.decodeDelimited(bytes);
  return t.toObject(msg, { defaults: true }) as DocumentIR;
}
