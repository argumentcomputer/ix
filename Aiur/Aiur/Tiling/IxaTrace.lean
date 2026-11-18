import Aiur.Tiling.Ixa
import Aiur.Trace.Export

/-!
# The trace section, decoded completely and re-encoded

`Ixa.getPackage` reads the chips of a trace section and skips its population
plans, groups and depth metadata. This file reads all of it (`getTrace`) into
an `ITrace` and writes an `ITrace` back with the writer's own primitives
(`ITrace.write`: `Trace.withNodesWithEncoding`, `Trace.internPolynomial`,
`Trace.listP`), so an export can check that the trace section of a file is
exactly the encoding of what was decoded (`checkTrace`).

The chip records are written by `putIChip`, and `putChip_eq` proves that the
compiler's `Trace.putChip` writes `IChip.ofChip c` through it: after the
compiler's two checks, `putChip encode c` *is* `putIChip encode (IChip.ofChip c)`.
The plan, depth and group records are written by mirrors of
`Trace.putFunctionOf`, `Trace.putDepth` and `Trace.putGroup`.

What the check establishes. The compiler wrote the section as `W(S)` from its
system `S`; `checkTrace` establishes `ITrace.write t = W(S)` for the decoded
`t`. If `ITrace.write` is injective (the grammar is unambiguous: every item is
length- or tag-prefixed, TagN is bijective and the node pool lists distinct
nodes in first-completion order) and the mirrors agree with the compiler's
plan and group writers, then `t` is the abstraction of `S`, so its chips are
`IChip.ofChip` of the system's chips. The decoder is then outside the trusted
base: a decoder bug either reproduces the file (and the chips are the ones the
file encodes) or fails the check.
-/

namespace Aiur.Tiling.Ixa

open Aiur.Ixon Aiur.Circuit Aiur.Trace Aiur.Execution

/-! ## Writing -/

section Put

variable {F : Type} (encode : F → Nat)

def putIOp : IOp F → PoolM Unit
  | .assign dest values => do u8 0; nats dest; listP values (putPolynomial encode)
  | .inverse dest value => do u8 1; nat dest; putPolynomial encode value
  | .choose dest tests => do u8 2; nats dest; listP tests (listP · (putPolynomial encode))
  | .failure dest differences => do u8 3; nats dest; listP differences (putPolynomial encode)
  | .call name args dest => do u8 4; str name; listP args (putPolynomial encode); nats dest
  | .store type values dest => do u8 5; putTy type; listP values (putPolynomial encode); nat dest
  | .load type address dest => do u8 6; putTy type; putPolynomial encode address; nats dest
  | .hint channel pc type keyType key dest => do
      u8 7; str channel; nat pc; putTy type; putTy keyType
      listP key (putPolynomial encode); nats dest

def putIPlan (p : IPlan F) : PoolM Unit := do
  str p.name
  str p.representative
  nat p.roles
  nats p.inputs
  nats p.outputs
  listP p.steps fun (guard, op) => do putPolynomial encode guard; putIOp encode op
  listP p.writes fun (column, id, guard) => do nat column; nat id; putPolynomial encode guard

/-- The chip record of `Trace.putChip`, from its written form. -/
def putIChip (x : IChip F) : PoolM Unit := do
  let poly := putPolynomial encode
  str x.name
  nat x.width
  nat x.activation
  nats x.inputs
  listP x.output poly
  listP x.constraints poly
  listP x.sends fun send => do
    str send.channel
    listP send.args poly
    nats send.result
    poly send.enable
  listP x.memory fun cell => do
    putTy cell.type
    poly cell.address
    listP cell.values poly
    poly cell.enable

def putIDepth (d : IDepth) : PutM Unit := do
  option d.column nat
  nat d.rank
  list d.slots fun (kind, column) => do
    u8 kind.toUInt8
    if 2 ≤ kind then nat (column.getD 0)

def putIGroup (g : IGroup F) : PoolM Unit := do
  let poly := putPolynomial encode
  str g.name
  nat g.width
  poly g.activation
  listP g.constraints poly
  listP g.receive poly
  listP g.sends fun (enable, args) => do poly enable; listP args poly
  listP g.members fun m => do
    str m.name
    array m.columns nat
    nat m.selector
    listP m.writes fun (column, value) => do nat column; poly value

/-- The trace section `t` encodes to, laid out as
`Trace.exportPreparedPlanWithEncoding` lays it out. -/
def ITrace.write (t : ITrace F) : Except String ByteArray :=
  let encoding : FieldEncoding := if t.wide then .wide else .narrow
  Ixon.run do
    nat planVersion
    encoding.putModulus t.modulus
    nats t.limbs
    withNodesWithEncoding encoding (modulus := some t.modulus) do
      listP t.plans (putIPlan encode)
      listP t.chips fun (x, d) => do putIChip encode x; putIDepth d
      listP t.groups (putIGroup encode)

end Put

/-! ## `putChip` writes `IChip.ofChip` -/

section Agree

variable {F : Type} [Field F] [DecidableEq F] (encode : F → Nat)

private theorem listP_map {α β : Type} (xs : List α) (f : α → β) (item : β → PoolM Unit) :
    listP (xs.map f) item = listP xs (item ∘ f) := by
  simp [listP, List.forIn_map, List.foldlM_map]

/-- After its two checks, the compiler's chip writer is `putIChip` of the
written form. -/
theorem putChip_eq (c : Chip F) :
    putChip encode c = (do
      let chip := Optimized.Activation.compile c
      unless chip.wellFormed do throw s!"invalid activated circuit {c.name}"
      unless chip.stats.maxConstraintDegree ≤ max 2 c.stats.maxConstraintDegree &&
          chip.maxLookupGuardDegree ≤ max 1 c.maxLookupGuardDegree do
        throw s!"activation increased the degree budget in {c.name}"
      putIChip encode (IChip.ofChip c)) := by
  simp only [putChip, putIChip, IChip.ofChip, listP_map]
  rfl

/-- The data `Trace.putGroup` writes for a checked group. -/
def IGroup.ofLayout (g : Optimized.Grouping.Layout F) : IGroup F where
  name := g.name
  width := g.width
  activation := g.activation
  constraints := g.constraints
  receive := g.receive
  sends := g.sends.map fun s => (s.enable, s.args)
  members := g.members.map fun m => ⟨m.name, m.columns, m.selector, m.writes⟩

theorem putGroup_eq (g : Optimized.Grouping.Layout F) :
    putGroup encode g = putIGroup encode (IGroup.ofLayout g) := by
  simp only [putGroup, putIGroup, IGroup.ofLayout, listP_map]
  rfl

/-- The slot code `Trace.putDepth` writes. -/
def slotCode : Optimized.Depth.SlotKind → Nat
  | .plain => 0
  | .exact => 1
  | .gap => 2
  | .external => 3

/-- The data `Trace.putDepth` writes for a source chip. -/
def IDepth.of (cfg : Optimized.Depth.Config) (source : Chip F) : IDepth where
  column := if (cfg.plan source.name).recursive then some source.numVars else none
  rank := cfg.rank source.name
  slots := (slotColumns cfg.limbs ((cfg.plan source.name).base source) (cfg.plan source.name).slots).map
    fun (kind, column) => (slotCode kind, if 2 ≤ slotCode kind then some column else none)

private theorem list_map_eq {α β : Type} (xs : List α) (h : α → β) (f : β → PutM Unit)
    (g : α → PutM Unit) (pt : ∀ a, f (h a) = g a) : Ixon.list (xs.map h) f = Ixon.list xs g := by
  have : (fun a => f (h a)) = g := funext pt
  subst this
  simp [Ixon.list, List.forIn_map, List.foldlM_map]

theorem putDepth_eq (cfg : Optimized.Depth.Config) (source : Chip F) :
    putDepth cfg source = putIDepth (IDepth.of cfg source) := by
  simp only [putDepth, putIDepth, IDepth.of]
  congr 1
  funext _
  congr 1
  funext _
  refine (list_map_eq _ _ _ _ ?_).symm
  intro a
  obtain ⟨kind, column⟩ := a
  cases kind <;> simp [slotCode]

end Agree

/-- The package's trace section (`pkg.trace`, from which `pkg.chips` and
`pkg.groups` are read) re-encodes to exactly the trace bytes of the file. -/
def checkTrace {F : Type} (encode : F → Nat) (bytes : ByteArray) (pkg : Package F) :
    Except String Unit := do
  let again ← pkg.trace.write encode
  unless again.data == (bytes.extract pkg.traceStart bytes.size).data do
    throw "the trace section does not re-encode to its bytes"

/-- The whole file `pkg` decodes to, written by the compiler's package writer:
the program section by `Export.putProgramWithEncoding` itself, the trace
section by `ITrace.write`. -/
def Package.write {F : Type} (encode : F → Nat) (pkg : Package F) : Except String ByteArray := do
  let trace ← pkg.trace.write encode
  Ixon.run (Artifact.putPackageWithEncoding (if pkg.wide then .wide else .narrow) pkg.program
    pkg.modulus encode (some trace))

/-- `decodePackage`, accepted only if the decoded package re-encodes to
exactly the file's bytes: the trace section through `checkTrace`, and the
whole file through `Package.write`. -/
def decodeChecked {F : Type} [NatCast F] (modulus : Nat) (encode : F → Nat) (bytes : ByteArray) :
    Except String (Package F) := do
  let pkg ← decodePackage modulus bytes
  checkTrace encode bytes pkg
  let again ← pkg.write encode
  unless again.data == bytes.data do throw "the package does not re-encode to its bytes"
  return pkg

end Aiur.Tiling.Ixa
