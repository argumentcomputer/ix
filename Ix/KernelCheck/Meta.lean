module

public import Ix.KernelCheck.Step
public import Ix.KernelDisplay.MetaNames

/-! Shared host-side metadata/display helpers. Their existing declaration
names and bodies are preserved; the erasure runner remains in Benchmarks. -/

@[expose] public section

namespace Benchmarks.Kernel.CheckIxeMeta

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader
open Benchmarks.Kernel.CheckIxeStep

/-! ## The display table -/

/-- Lean's name (Ix's copy) as the kernel's, component by component. -/
def kernelName : Ix.Name → Ix.Kernel.Name
  | .anonymous _ => .anonymous
  | .str p s _ => .str (kernelName p) s
  | .num p n _ => .num (kernelName p) n

/-- The level parameters' names the metadata gives a constant (none when the
metadata is not loaded, as in the streaming load). -/
def levelNamesOf (env : Ixon.Env) (m : Ixon.ConstantMeta) : List Ix.Kernel.Name :=
  let lvls : Array Address := match m.info with
    | .defn _ l .. | .axio _ l .. | .quot _ l .. | .indc _ l .. | .ctor _ l .. | .recr _ l .. => l
    | _ => #[]
  lvls.toList.filterMap fun a => (env.names[a]?).map kernelName

/-- **The display table** of an environment, keyed by the keys a reading with
the context `cx` gives the addresses the environment's names map to. -/
def displayTable (env : Ixon.Env) (cx : Ctx md) : DisplayTable md := Id.run do
  let mut t : DisplayTable md := {}
  for (name, named) in env.named.toList do
    let some k := cx.keys.byAddress[named.addr]? <|> keyOfAddress cx.store cx.roles named.addr
      | continue
    let (d, _) := t.getD k ({}, named.addr)
    let lvls := if d.levelNames.isEmpty then levelNamesOf env named.constMeta else d.levelNames
    t := t.insert k ({ d with names := d.names ++ [kernelName name], levelNames := lvls }, named.addr)
  -- an alias fiber's names in a fixed order
  return t.map fun _ (d, a) =>
    ({ d with names := (d.names.toArray.qsort (toString · < toString ·)).toList }, a)

/-! ## The meta reader -/

/-- The keys a declaration declares. -/
def declaredKeys : Ix.Kernel.Declaration md → List (CName md)
  | .axiomDecl cv | .defnDecl cv _ _ | .thmDecl cv _ | .opaqueDecl cv _ | .quotDecl _ cv => [cv.name]
  | .indDecl block _ => block.map (·.name)
  | .basisDecl _ => []

/-- **The meta reader's last step**: the display of the keys the reading
declares, from the table. -/
def withDisplay (t : DisplayTable .meta) (rd : Read .meta) : Read .meta :=
  { rd with display := (rd.decls.toList.flatMap declaredKeys).filterMap fun k =>
      (t[k]?).map fun (d, _) => (k, d) }

/-- The reader context and the table's evidence at `.meta`, over a setup's
store and with its hints: what `CheckIxeStep.setup` builds at `.anon`. -/
def metaContext (s : Setup) (blobs : Address → Option ByteArray) (t : Ix.Kernel.RoleTable)
    (pre : Prelude .meta) (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint) :
    Ctx .meta × Ix.Kernel.Evidences .meta :=
  let blobs' : Address → Option ByteArray := fun a =>
    blobs a <|> (pre.blobs.find? (·.1 == a)).map (·.2)
  let evidence : Std.HashMap Address Ixon.Constant := pre.evidence.foldl
    (fun m (a, c) => if s.store.contains a then m else m.insert a c) {}
  let look : Address → Option Ixon.Constant := fun a => s.store[a]? <|> evidence[a]?
  let cx : Ctx .meta := contextWith look blobs' t s.store.toArray hint
    (Ix.Kernel.Admission.projectionAddress Address.blake3 look)
  (cx, evidenceOf cx pre.state t)

/-- A `.meta` tier declaration's binders named from the metadata (as
`Ix.KernelDisplay.nameRead` names a reading). -/
def nameTier (c : Ix.KernelDisplay.NameCx) (d : Ix.Kernel.Tier.TierDecl .meta)
    (names : Std.HashMap Address Ix.Kernel.Name) :
    Ix.Kernel.Tier.TierDecl .meta × Ix.KernelDisplay.Coverage × Std.HashMap Address Ix.Kernel.Name :=
  match d with
  | .defs s ms =>
    let (ms, st) := (ms.mapM fun (cv, v) => Ix.KernelDisplay.nameValue c cv v).run { names }
    (.defs s ms, st.coverage, st.names)
  | .unsafeOpaque cv v =>
    let ((cv, v), st) := (Ix.KernelDisplay.nameValue c cv v).run { names }
    (.unsafeOpaque cv v, st.coverage, st.names)
  | .unsafeAxiom cv =>
    let (cv, st) := (Ix.KernelDisplay.nameVal c cv).run { names }
    (.unsafeAxiom cv, st.coverage, st.names)

end Benchmarks.Kernel.CheckIxeMeta
