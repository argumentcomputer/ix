import Ix.MultiStark.Keccak
import Ix.Aiur.Compiler
import Ix.Aiur.Protocol
import Ix.Keccak

open Aiur

def hb (x : UInt8) : String := let s := String.ofList (Nat.toDigits 16 x.toNat); if s.length == 1 then "0" ++ s else s
def toHex (b : ByteArray) : String := b.data.foldl (fun s x => s ++ hb x) ""

def runK (c : CompiledToplevel) (input : ByteArray) : Except String ByteArray := do
  let idx := c.getFuncIdx `keccak256_test |>.get!
  let io : IOBuffer := (default : IOBuffer).extend #[Aiur.G.ofNat 0] (input.data.map .ofUInt8)
  match c.bytecode.execute idx #[] io with
  | .error e => .error e
  | .ok (out, _, _) => .ok ⟨out.map (fun g => UInt8.ofNat (g.n % 256))⟩

def main : IO Unit := do
  let compiled ← match MultiStark.keccakToplevel with
    | .error g => IO.println s!"merge fail {g}"; return
    | .ok t => match t.compile with
      | .error e => IO.println s!"compile fail {e}"; return
      | .ok c => pure c
  IO.println "compiled ok"
  let inputs : List ByteArray :=
    [ "".toUTF8, "abc".toUTF8, "The quick brown fox jumps over the lazy dog".toUTF8,
      (ByteArray.mk (Array.range 100 |>.map (fun n => UInt8.ofNat n))),
      (ByteArray.mk (Array.range 135 |>.map (fun n => UInt8.ofNat n))),
      (ByteArray.mk (Array.range 136 |>.map (fun n => UInt8.ofNat n))),
      (ByteArray.mk (Array.range 200 |>.map (fun n => UInt8.ofNat n))),
      (ByteArray.mk (Array.range 272 |>.map (fun n => UInt8.ofNat (n % 251)))) ]
  for inp in inputs do
    let expected := Keccak.hash inp
    match runK compiled inp with
    | .error e => IO.println s!"  [{inp.size}B] exec err: {e}"
    | .ok got =>
      let tag := if got == expected then "MATCH   " else "MISMATCH"
      IO.println s!"  [{inp.size}B] {tag}  aiur={toHex got}  ref={toHex expected}"
