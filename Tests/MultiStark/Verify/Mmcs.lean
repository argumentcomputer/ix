module
import Tests.Ixby.Common
import Ix.MultiStark.Verify.Mmcs
import Blake3.Rust

namespace Tests.MultiStark.Verify.Mmcs

open _root_.MultiStark.Verify
open Tests.Ixby (Check runChecks)

private instance : Inhabited Digest := ⟨Mmcs.hashRow #[]⟩

private def f (n : Nat) : Field := Ix.Ixby.Goldilocks.reduce n
private def rows (index : Nat) : Array (Array Field) :=
  #[#[f (index + 1)], #[f (50 + index / 4)], #[f (100 + index)]]

private def checks : IO (List Check) := do
  let dims : Array Mmcs.Dimension := #[⟨3, 1⟩, ⟨1, 1⟩, ⟨3, 1⟩]
  let leaves := (Array.range 8).map fun i => Mmcs.hashRow #[f (i + 1), f (100 + i)]
  let pairs := (Array.range 4).map fun i => Mmcs.compress leaves[i * 2]! leaves[i * 2 + 1]!
  let quarters := (Array.range 2).map fun i =>
    Mmcs.compress (Mmcs.compress pairs[i * 2]! pairs[i * 2 + 1]!) (Mmcs.hashRow #[f (50 + i)])
  let cap := #[Mmcs.compress quarters[0]! quarters[1]!]
  let indices := #[6, 1, 2, 1]
  let opening : BatchOpening := ⟨indices.map rows, #[leaves[0]!, leaves[3]!, leaves[7]!, pairs[2]!]⟩
  let accepted := Mmcs.check 0 dims cap indices opening
  let duplicate := { opening with
    values := opening.values.modify 3 fun query =>
      query.modify 2 fun row => row.modify 0 (·.add 1) }
  let group := { opening with
    values := opening.values.modify 2 fun query =>
      query.modify 1 fun row => row.modify 0 (·.add 1) }
  let boundaries := { opening with
    values := opening.values.map fun query => #[#[], query[1]!, query[0]! ++ query[2]!] }
  let single := Mmcs.hashRow #[f 9]
  let bytes := Codec.Wire.littleEndian 8 1 ++ Codec.Wire.littleEndian 8 100
  return [
    ("native BLAKE3 leaf word order", leaves[0]!.bytes == (Blake3.Rust.hash ⟨bytes⟩).val.data),
    ("native BLAKE3 left/right compression", cap[0]!.bytes ==
      (Blake3.Rust.hash ⟨quarters[0]!.bytes ++ quarters[1]!.bytes⟩).val.data),
    (s!"mixed-height shared frontier ({repr accepted})", accepted.isOk),
    ("non-root cap authenticates all injection layers", (Mmcs.check 1 dims quarters indices opening).isOk),
    ("cap cannot cut off a shorter matrix injection", !(Mmcs.check 2 dims pairs indices opening).isOk),
    ("empty query set admits an empty frontier", (Mmcs.check 0 dims cap #[] ⟨#[], #[]⟩).isOk),
    ("empty query set rejects extra hashes", !(Mmcs.check 0 dims cap #[] ⟨#[], #[single]⟩).isOk),
    ("zero matrices rejected", !(Mmcs.check 0 #[] cap #[] ⟨#[], #[]⟩).isOk),
    ("out-of-range matrix height rejected", !(Mmcs.check 0 #[⟨33, 1⟩] cap #[] ⟨#[], #[]⟩).isOk),
    ("wrong cap length rejected", !(Mmcs.check 0 dims quarters indices opening).isOk),
    ("missing cap rejected", !(Mmcs.check 0 dims #[] indices opening).isOk),
    ("wrong cap digest rejected", !(Mmcs.check 0 dims #[single] indices opening).isOk),
    ("original query count checked", !(Mmcs.check 0 dims cap indices.pop opening).isOk),
    ("matrix count checked before flattening", !(Mmcs.check 0 dims cap indices
      { opening with values := opening.values.map Array.pop }).isOk),
    ("same-height row boundaries are pinned by verifier widths", !(Mmcs.check 0 dims cap indices boundaries).isOk),
    ("conflicting duplicate query rejected", !(Mmcs.check 0 dims cap indices duplicate).isOk),
    ("conflicting rows at a later mixed-height merge rejected", !(Mmcs.check 0 dims cap indices group).isOk),
    ("indices come from verifier, not proof", !(Mmcs.check 0 dims cap #[6, 0, 2, 0] opening).isOk),
    ("out-of-range index rejected", !(Mmcs.check 0 dims cap #[8, 1, 2, 1] opening).isOk),
    ("missing boundary rejected", !(Mmcs.check 0 dims cap indices
      { opening with frontier := opening.frontier.pop }).isOk),
    ("extra boundary rejected", !(Mmcs.check 0 dims cap indices
      { opening with frontier := opening.frontier.push single }).isOk),
    ("boundary order is authenticated", !(Mmcs.check 0 dims cap indices
      { opening with frontier := opening.frontier.reverse }).isOk),
    ("single-row tree needs no fabricated padding", (Mmcs.check 0 #[⟨0, 1⟩] #[single]
      #[0] ⟨#[#[#[f 9]]], #[]⟩).isOk),
    ("single-row tree shortens a configured cap", (Mmcs.check 10 #[⟨0, 1⟩] #[single]
      #[0] ⟨#[#[#[f 9]]], #[]⟩).isOk),
    ("leaf-level cap needs no authentication path", (Mmcs.check 3 #[⟨3, 2⟩] leaves
      #[2] ⟨#[#[#[f 3, f 102]]], #[]⟩).isOk),
    ("leaf-level cap still checks the row", !(Mmcs.check 3 #[⟨3, 2⟩] leaves
      #[2] ⟨#[#[#[f 3, f 103]]], #[]⟩).isOk)
  ]

public def suite : IO UInt32 := runChecks "stage2-mmcs" checks

end Tests.MultiStark.Verify.Mmcs
