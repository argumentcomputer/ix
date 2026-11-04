module

public import Ix.Ixon

@[expose] public section

namespace Ix.KernelFidelity

/-- An ordered view of input records, without retaining their decoded bodies.
Authentication belongs to the caller: `ofParts` uses the result of the existing
verified lazy loader; `ofStore` also supports deliberately altered fixtures. -/
structure RecordAccess where
  addresses : Array Address
  tag : Address → Except String Ixon.ConstTag
  get : Address → Except String Ixon.Constant
  blobs : List (Address × ByteArray)

def recordTag (c : Ixon.Constant) : Ixon.ConstTag :=
  match c.info with
  | .defn _ => .defn | .recr _ => .recr | .axio _ => .axio | .quot _ => .quot
  | .muts _ => .muts | .iPrj _ => .iPrj | .cPrj _ => .cPrj
  | .rPrj _ => .rPrj | .dPrj _ => .dPrj

/-- A requested body must exist, decode, and agree with its earlier tag.
An access error is not an absent record or omitted fidelity coverage. -/
def RecordAccess.read (v : RecordAccess) (a : Address) (tag : Ixon.ConstTag) :
    Except String Ixon.Constant := do
  let c ← (v.get a).mapError fun e => s!"fidelity: record {a}: {e}"
  unless recordTag c == tag do throw s!"fidelity: record tag changed at {a}"
  return c

/-- The existing eager store's exact enumeration order. -/
def RecordAccess.ofStore (store : Std.HashMap Address Ixon.Constant)
    (blobs : List (Address × ByteArray)) : RecordAccess :=
  let get (a : Address) : Except String Ixon.Constant :=
    match store[a]? with
    | some c => .ok c
    | none => .error s!"missing record {a}"
  { addresses := store.toList.toArray.map (·.1), get,
    tag := fun a => recordTag <$> get a, blobs }

/-- Keep the input's windows into one backing image. Rebuild only the key
map in `ReaderFidelity.Input.ofEnv`'s insertion order, so its enumeration
matches the eager store even when hash buckets collide. No record or named
metadata is materialized here, and no raw-byte window is copied. -/
def RecordAccess.ofParts (parts : Ixon.LazyEnvParts) : RecordAccess := Id.run do
  let consts := parts.env.consts
  let mut keys : Std.HashMap Address Unit := {}
  for (a, _) in consts.toList do keys := keys.insert a ()
  let lookup (a : Address) : Except String Ixon.LazyConstant :=
    match consts[a]? with
    | some c => .ok c
    | none => .error s!"missing record {a}"
  return {
    addresses := keys.toList.toArray.map (·.1)
    tag := fun a => (lookup a).bind Ixon.LazyConstant.peekTag
    get := fun a => (lookup a).bind Ixon.LazyConstant.get
    blobs := parts.env.blobs.toList }

end Ix.KernelFidelity
