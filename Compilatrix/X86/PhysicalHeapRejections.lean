import Compilatrix.X86.PhysicalHeapExamples

namespace Compilatrix.X86.PhysicalHeap.Examples
open Ixon IxIR2

private def withRoot (artifact : Wire.Artifact) (definition : IxIR2.Function) : Wire.Artifact :=
  { artifact with program := { artifact.program with declarations := [(root, .fn definition)] } }

def rejections : List (String × Wire.Artifact) := Id.run do
  let base := artifact "leaf-switch"
  let one := fun instructions terminator => withRoot base (function #[.shared]
    #[block #[.owned .shared] instructions terminator])
  let ret := IxIR2.Terminator.ret (.reg 0)
  let ctor2 : CtorId := ⟨Address.replicate 0xd4, 0, 0⟩
  let secondLayout : Wire.Layout :=
    let bytes := "different-leaf-layout/1".toUTF8
    ⟨Address.blake3 bytes, bytes⟩
  let wrongLayout := one #[.alloc .unique cid #[.lit (.nat 0)], .takeUnique (.reg 1) cid,
    .allocWith 0 .unique ctor2 #[.reg 2], .dropUnique (.reg 3)] ret
  let wide := one #[.alloc .unique cid #[.lit (.nat 0), .lit (.nat 1), .lit (.nat 2)], .dropUnique (.reg 1)] ret
  let borrowed := withRoot base {
    signature := { params := #[⟨.shared, .borrowed⟩], result := .shared, papSafe := false }
    blocks := #[block #[.borrowed .shared .caller] #[] (.ret (.lit (.nat 0)))] }
  let mut expansion := #[]
  for index in [:13] do
    let start := index * 3
    expansion := expansion ++ #[
      block #[.owned .shared] #[] (.switchValue (.reg 0) #[]
        (some ⟨edge (start + 1) #[.reg 0], edge (start + 2) #[.reg 0]⟩)),
      block #[.owned .shared] #[] (.jump (edge (start + 3) #[.reg 0])),
      block #[.scalar, .owned .shared] #[.releaseShared (.reg 1)] (.jump (edge (start + 3) #[.reg 0]))]
  let expanded := withRoot base (function #[.shared] (expansion.push (block #[.owned .shared] #[] ret)))
  return [
    ("arena-overflow", artifact "arena-overflow"),
    ("shared-node-retain", one #[.alloc .shared cid #[.reg 0], .retainShared (.reg 1),
      .releaseShared (.reg 1), .releaseShared (.reg 2)] (.ret (.lit (.nat 0)))),
    ("nested-heap-field", one #[.alloc .unique cid #[.lit (.nat 0)], .alloc .unique cid #[.reg 1], .dropUnique (.reg 2)] ret),
    ("borrowed-parameter", borrowed),
    ("three-field-leaf", { wide with schemas := wide.schemas.map fun schema =>
      { schema with definition := { schema.definition with fields := Array.replicate 3 schema.world } } }),
    ("missing-schema", { base with schemas := #[] }),
    ("missing-callee", one #[.call helper #[.reg 0]] (.ret (.reg 1))),
    ("recursive-call", one #[.call root #[.reg 0]] (.ret (.reg 1))),
    ("cyclic-block", one #[] (.jump (edge 0 #[.reg 0]))),
    ("value-slots", one (Array.replicate 16 (.move (.reg 0))) ret),
    ("duplicate-owner", one #[.alloc .unique cid #[.lit (.nat 0)], .move (.reg 1), .dropUnique (.reg 1), .dropUnique (.reg 2)] ret),
    ("duplicate-credit", one #[.alloc .unique cid #[.lit (.nat 0)], .takeUnique (.reg 1) cid,
      .allocWith 0 .unique cid #[.reg 2], .dropUnique (.reg 3), .allocWith 0 .unique cid #[.lit (.nat 0)], .dropUnique (.reg 4)] ret),
    ("reuse-layout", { wrongLayout with
      layouts := wrongLayout.layouts.push secondLayout
      schemas := wrongLayout.schemas.push ⟨.unique, ctor2, ⟨secondLayout.identity, #[.unique]⟩⟩ }),
    ("nat-overflow", one #[] (.ret (.lit (.nat UInt64.size)))),
    ("pap-in-body", one #[.papp helper #[]] ret),
    ("higher-order-apply", one #[.apply (.reg 0) #[]] (.ret (.reg 1))),
    ("external-call", one #[.extern helper #[.reg 0]] (.ret (.reg 1))),
    ("edge-copies", withRoot base (function #[.shared] #[
      block #[.owned .shared] #[] (.jump (edge 1 (Array.replicate 13 (.reg 0)))),
      block (Array.replicate 13 (.owned .shared)) #[] ret])),
    ("cfg-expansion", expanded)]

end Compilatrix.X86.PhysicalHeap.Examples
