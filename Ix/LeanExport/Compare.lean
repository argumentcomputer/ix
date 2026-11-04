/-
  `Ix.LeanExport.Compare`: compare an environment compiled from a Lean export
  (`Ix.LeanExport`) with the native compile of the same declarations.

  An export carries every declaration's content exactly, but not all of its
  metadata (see `Ix.LeanExport`). So the comparison has two parts.
  - **Content, compared exactly:** the published names, the address and the
    exact reducibility hints of each, the constants (address and bytes), the
    per-address hints, and the role binding (its address and table bytes, so
    the evidence too).
  - **Metadata, counted and reported, never compared:** named metadata (binder
    names and binder info, `mdata`), the blobs and name components that hold
    it, and the reverse address-to-name index.
-/
module

public import Ix.Ixon

public section

namespace Ix.LeanExport

/-- How a compile of an export differs from the native compile. -/
structure Comparison where
  /-- Names the native compile publishes and the export's does not. -/
  onlyNative : Array Ix.Name := #[]
  /-- Names the export's compile publishes and the native one does not. -/
  onlyExport : Array Ix.Name := #[]
  /-- Names published at different addresses. -/
  addressDiffers : Array Ix.Name := #[]
  /-- Names with different exact reducibility hints. -/
  hintsDiffer : Array Ix.Name := #[]
  /-- Constant addresses in one compile only. -/
  constsOnlyNative : Nat := 0
  constsOnlyExport : Nat := 0
  /-- Constants at one address with different bytes. -/
  constsDiffer : Nat := 0
  /-- The per-address hints differ. -/
  anonHintsDiffer : Bool := false
  /-- The role bindings differ (address or table bytes). -/
  bindingDiffers : Bool := false
  /-- The bundle root or the assumptions differ. -/
  bundleDiffers : Bool := false
  /-- Metadata: names whose metadata differs. -/
  metadataDiffers : Nat := 0
  /-- Metadata: blobs in one compile only. -/
  blobsOnlyNative : Nat := 0
  blobsOnlyExport : Nat := 0
  /-- Metadata: name components in one compile only. -/
  namesOnlyNative : Nat := 0
  namesOnlyExport : Nat := 0
  /-- Metadata: addresses whose reverse-index name differs. -/
  addrToNameDiffers : Nat := 0
  deriving Inhabited

/-- Whether the content is exactly equal. -/
def Comparison.contentExact (c : Comparison) : Bool :=
  c.onlyNative.isEmpty && c.onlyExport.isEmpty && c.addressDiffers.isEmpty &&
  c.hintsDiffer.isEmpty && c.constsOnlyNative == 0 && c.constsOnlyExport == 0 &&
  c.constsDiffer == 0 && !c.anonHintsDiffer && !c.bindingDiffers && !c.bundleDiffers

/-- Keys of `a` that `b` lacks. -/
private def missing {α β γ : Type} [BEq α] [Hashable α]
    (a : Std.HashMap α β) (b : Std.HashMap α γ) : Nat :=
  a.fold (init := 0) fun n k _ => if b.contains k then n else n + 1

/-- Compare `exported`, compiled from an export, with `native`. -/
def compare (native exported : Ixon.Env) : Comparison := Id.run do
  let mut c : Comparison := {}
  for (name, n) in native.named.toList do
    match exported.named[name]? with
    | none => c := { c with onlyNative := c.onlyNative.push name }
    | some e =>
      if n.addr != e.addr then c := { c with addressDiffers := c.addressDiffers.push name }
      if n.hints != e.hints then c := { c with hintsDiffer := c.hintsDiffer.push name }
      if n.constMeta != e.constMeta || n.original != e.original then
        c := { c with metadataDiffers := c.metadataDiffers + 1 }
  for (name, _) in exported.named.toList do
    unless native.named.contains name do c := { c with onlyExport := c.onlyExport.push name }
  let mut differ := 0
  for (address, lc) in native.consts.toList do
    if let some other := exported.consts[address]? then
      unless lc.rawBytes == other.rawBytes do differ := differ + 1
  let anonHintsDiffer := native.anonHints.size != exported.anonHints.size ||
    native.anonHints.toList.any fun (a, h) => exported.anonHints[a]? != some h
  let addrToNameDiffers := native.addrToName.fold (init := 0) fun n a name =>
    if exported.addrToName[a]? == some name then n else n + 1
  return { c with
    constsOnlyNative := missing native.consts exported.consts
    constsOnlyExport := missing exported.consts native.consts
    constsDiffer := differ
    anonHintsDiffer
    bindingDiffers := native.roleBinding != exported.roleBinding
    bundleDiffers := native.main != exported.main ||
      native.assumptions.size != exported.assumptions.size ||
      native.assumptions.toList.any (!exported.assumptions.contains ·)
    blobsOnlyNative := missing native.blobs exported.blobs
    blobsOnlyExport := missing exported.blobs native.blobs
    namesOnlyNative := missing native.names exported.names
    namesOnlyExport := missing exported.names native.names
    addrToNameDiffers }

/-- The report, one line per finding; differences in content first. -/
def Comparison.report (c : Comparison) (native exported : Ixon.Env) : List String :=
  let names (what : String) (xs : Array Ix.Name) : List String :=
    if xs.isEmpty then [] else
      s!"{what}: {xs.size}" :: (xs.toList.take 8).map (s!"  {·}")
  let count (what : String) (n : Nat) : List String := if n == 0 then [] else [s!"{what}: {n}"]
  let content :=
    names "names only in the native compile" c.onlyNative ++
    names "names only in the export's compile" c.onlyExport ++
    names "names at different addresses" c.addressDiffers ++
    names "names with different hints" c.hintsDiffer ++
    count "constants only in the native compile" c.constsOnlyNative ++
    count "constants only in the export's compile" c.constsOnlyExport ++
    count "constants with different bytes" c.constsDiffer ++
    (if c.anonHintsDiffer then ["the per-address hints differ"] else []) ++
    (if c.bindingDiffers then ["the role bindings differ"] else []) ++
    (if c.bundleDiffers then ["the bundle roots or assumptions differ"] else [])
  let verdict := if c.contentExact then
      s!"content exact: {native.named.size} names, {native.consts.size} constants, \
        the role binding{if native.roleBinding.isSome then "" else " (none)"} and every address equal"
    else "content differs"
  [verdict] ++ content ++
  [s!"metadata (reported, not compared): {c.metadataDiffers} names with different metadata; \
    blobs {c.blobsOnlyNative} only native, {c.blobsOnlyExport} only export \
    (of {native.blobs.size} and {exported.blobs.size}); \
    name components {c.namesOnlyNative} only native, {c.namesOnlyExport} only export; \
    {c.addrToNameDiffers} reverse-index names differ"]

end Ix.LeanExport

end
