module

import Ix.Sharing.Exact
import Ix.Ixon

/-! Byte-to-byte canonical-sharing receipts for the existing fixed corpora.
No candidate implementation or alternate limits are selected. This boundary
includes each record's decode, ordinary canonical normalization, serialization,
hashing and receipt IO, matching the Rust example's canonical receipt mode. -/

public section

private def normalizeBytes (bytes : ByteArray) : Except String ByteArray := do
  let constant ← Ixon.deConstant bytes
  let output ← (Ix.Sharing.Exact.normalizeConstantSharingTiered .tagN constant {}).mapError toString
  pure (Ixon.serConstant output)

def main (args : List String) : IO Unit := do
  let [input, receipt] := args
    | throw (IO.userError "expected corpus and new receipt path")
  let environment ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile input))
  let records := environment.consts.toArray.qsort fun a b => Address.cmpBytes a.1 b.1 == .lt
  let output ← IO.FS.Handle.mk receipt .writeNew
  output.putStrLn "canonical\tv1\trule=sharing-k16-greedy-v1\tK=16\tAPI=normalizeConstantSharingTiered\tlimits=default\ttiming=includes-decode-serialization-hash-receipt-IO"
  output.flush
  let mut total := 0
  for (address, stored) in records do
    let bytes := stored.rawBytes
    let start ← IO.monoNanosNow
    output.putStrLn s!"begin\t{address}\tinput_bytes={bytes.size}\tinput_hash={Address.blake3 bytes}"
    output.flush
    IO.eprintln s!"[CANONICAL] BEGIN {address}"
    let encoded ← IO.ofExcept (← IO.lazyPure fun _ => normalizeBytes bytes)
    unless encoded == bytes do
      throw (IO.userError s!"canonical bytes differ at {address}")
    output.putStrLn s!"output\t{address}\tbytes={encoded.size}\tinput_equal=true\thash={Address.blake3 encoded}"
    let elapsed := (← IO.monoNanosNow) - start
    total := total + elapsed
    output.putStrLn s!"end\t{address}\tok-canonical\tns={elapsed}"
    output.flush
    IO.eprintln s!"[CANONICAL] END {address} ok-canonical"
  IO.println s!"canonical PASS records={records.size} aggregate_ns={total}"
