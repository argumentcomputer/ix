module
public import Ix.Ixon
public import Ix.Compile.ExactKey
import all Ix.Common
import all IxC.Address.Core
import all Init.Data.ByteArray.Basic

public section

namespace Ix.Compile.OriginalData

open Ix.Compile.ExactKey (ExactName)

private theorem bytes_beq_iff (a b : ByteArray) : (a == b) = true ↔ a = b := by
  cases a with
  | mk a =>
    cases b with
    | mk b =>
      show ByteArray.beq ⟨a⟩ ⟨b⟩ = true ↔ _
      simp [ByteArray.beq]

local instance : LawfulBEq ByteArray where
  eq_of_beq := (bytes_beq_iff _ _).mp
  rfl := (bytes_beq_iff _ _).mpr rfl

private theorem address_beq_iff (a b : Address) : (a == b) = true ↔ a = b := by
  cases a with
  | mk a =>
    cases b with
    | mk b =>
      show (a == b) = true ↔ Address.mk a = Address.mk b
      simp

local instance : LawfulBEq Address where
  eq_of_beq := (address_beq_iff _ _).mp
  rfl := (address_beq_iff _ _).mpr rfl

/-- One successful publication's raw original. The outer hint option records
availability; `some none` is a known absence, not a request to infer hints.
The publication address prevents a rebound name from inheriting an old receipt.
Projection blocks share the same immutable byte buffer across their receipts. -/
structure Receipt where
  name : Ix.Name
  published : Address
  original : Ixon.RawBlob
  hints : Option (Option Lean.ReducibilityHints)
  block? : Option Ixon.RawBlob := none

abbrev OriginalStaging := Array Receipt
abbrev ByteTable := Std.HashMap Address ByteArray

structure Tables where
  originals : Std.HashMap Address Ixon.LazyConstant := {}
  hints : Std.HashMap Ix.Name (Option Lean.ReducibilityHints) := {}

/-- Equal keys only select bytes to compare; they never prove byte equality. -/
def insertBytes (table : ByteTable) (a : Address) (bytes : ByteArray) :
    Except String ByteTable := do
  if let some old := table[a]? then
    unless old == bytes do throw s!"original data: conflicting captured bytes at {a}"
    return table
  return table.insert a bytes

theorem insertBytes_existing {table : ByteTable} {a : Address} {old bytes : ByteArray}
    {out : ByteTable} (stored : table[a]? = some old)
    (accepted : insertBytes table a bytes = .ok out) : old = bytes ∧ out = table := by
  simp only [insertBytes, stored, bind, Except.bind, pure, Except.pure] at accepted
  split at accepted
  · rename_i same
    cases accepted
    exact ⟨beq_iff_eq.mp same, rfl⟩
  · cases accepted

theorem insertBytes_self {table : ByteTable} {a : Address} {bytes : ByteArray}
    {out : ByteTable} (accepted : insertBytes table a bytes = .ok out) :
    out[a]? = some bytes := by
  cases stored : table[a]? with
  | some old =>
    obtain ⟨rfl, rfl⟩ := insertBytes_existing stored accepted
    exact stored
  | none =>
    simp only [insertBytes, stored, pure, Except.pure, Except.ok.injEq] at accepted
    subst out
    simp

theorem insertBytes_keeps {table : ByteTable} {a k : Address} {bytes value : ByteArray}
    {out : ByteTable} (accepted : insertBytes table a bytes = .ok out)
    (stored : table[k]? = some value) : out[k]? = some value := by
  cases atAddress : table[a]? with
  | some old =>
    obtain ⟨_, rfl⟩ := insertBytes_existing atAddress accepted
    exact stored
  | none =>
    simp only [insertBytes, atAddress, pure, Except.pure, Except.ok.injEq] at accepted
    subst out
    rw [Std.HashMap.getElem?_insert]
    split
    · rename_i same
      have eq : a = k := beq_iff_eq.mp same
      subst k
      simp [atAddress] at stored
    · exact stored

/-- Compact member information; no decoded expression is retained. -/
inductive MemberShape where
  | defn (kind : Ix.DefKind)
  | indc (constructors : Nat)
  | recr

inductive ProjectionKind where
  | defn | indc | recr
  | ctor (index : Nat)

inductive Shape where
  | plain
  | defn (kind : Ix.DefKind)
  | block (members : Array MemberShape)
  | projection (block : Address) (index : Nat) (kind : ProjectionKind)

/-- Validate once per distinct address, then discard the structured constant. -/
def inspect (a : Address) (bytes : ByteArray) : Except String Shape := do
  unless Address.admissionHash bytes == a do throw s!"original data: hash mismatch at {a}"
  let c ← Ixon.deConstantExact bytes
  unless Ixon.serConstant c == bytes do throw s!"original data: noncanonical bytes at {a}"
  return match c.info with
    | .defn d => .defn d.kind
    | .dPrj p => .projection p.block p.idx.toNat .defn
    | .iPrj p => .projection p.block p.idx.toNat .indc
    | .cPrj p => .projection p.block p.idx.toNat (.ctor p.cidx.toNat)
    | .rPrj p => .projection p.block p.idx.toNat .recr
    | .muts members => .block (members.map fun member => match member with
        | .defn d => .defn d.kind
        | .indc i => .indc i.ctors.size
        | .recr _ => .recr)
    | _ => .plain

/-- Check the actual projection/member pairing, then derive whether the
original declaration kind requires a definition hint. Known absent hints
remain valid for theorem/opaque definitions and the other declaration kinds. -/
def requiresHint (views : Std.HashMap Address Shape) (name : Ix.Name)
    (rows : Array Receipt) : Shape → Except String Bool
  | .projection block index kind => do
    if rows.any (fun row => row.block?.isNone) then
      throw s!"original data: missing projection block for {name.pretty}"
    if rows.any (fun row => row.block?.map (·.addr) != some block) then
      throw s!"original data: mismatched projection block for {name.pretty}"
    let some (.block members) := views[block]? |
      throw s!"original data: projection block is not mutual for {name.pretty}"
    let some member := members[index]? |
      throw s!"original data: projection index out of range for {name.pretty}"
    match kind, member with
    | .defn, .defn k => return k == .defn
    | .indc, .indc _ | .recr, .recr => return false
    | .ctor i, .indc count =>
      unless i < count do throw s!"original data: constructor index out of range for {name.pretty}"
      return false
    | _, _ => throw s!"original data: projection member kind mismatch for {name.pretty}"
  | shape => do
    if rows.any (fun row => row.block?.isSome) then
      throw s!"original data: unexpected projection block for {name.pretty}"
    return match shape with | .defn k => k == .defn | _ => false

def matchesPublication (row : Receipt) (named : Ixon.Named) : Bool :=
  named.addr == row.published && named.original.map Prod.fst == some row.original.addr

/-- Recompute the two unchecked tables from matching successful receipts.
The phases and sorted address/name keys make refusal selection independent
of worker completion order. Stale receipts contribute neither bytes nor hints.
The exact-name index does not identify distinct raw names by their digest. -/
def prepare (staging : OriginalStaging) (base : Ixon.Env) : Except String Tables := do
  let targets : Std.HashMap ExactName Ixon.Named := base.named.fold
    (fun m name named => if named.original.isSome then m.insert name named else m) {}
  let mut byName : Std.HashMap ExactName (Array Receipt) := {}
  let mut payloads : Array Ixon.RawBlob := #[]
  for row in staging do
    if let some named := targets.get? row.name then
      if matchesPublication row named then
        byName := byName.insert row.name ((byName.get? row.name).getD #[] |>.push row)
        payloads := payloads.push row.original
        if let some block := row.block? then payloads := payloads.push block
  -- Check all captured duplicates before decoding or comparing to consts.
  -- In particular, the first of two conflicting records cannot pick the error.
  let mut bytes : ByteTable := {}
  for raw in payloads.qsort (fun a b => Ixon.addrLt a.addr b.addr) do
    bytes ← insertBytes bytes raw.addr raw.bytes
  let mut views : Std.HashMap Address Shape := {}
  let mut out : Tables := {}
  for (a, raw) in bytes.toArray.qsort (fun a b => Ixon.addrLt a.1 b.1) do
    if let some stored := base.consts[a]? then
      unless stored.rawBytes == raw do
        throw s!"original data: conflicting canonical bytes at {a}"
    let shape ← inspect a raw
    views := views.insert a shape
    if !base.consts.contains a then
      out := { out with originals := out.originals.insert a (Ixon.LazyConstant.ofSlice raw 0 raw.size) }
  for (name, named) in targets.toArray.qsort (fun a b => (Ix.nameCompareExact a.1 b.1).isLT) do
    let rows := (byName[name]?).getD #[]
    let some first := rows[0]? | throw s!"original data: missing receipt for {name.pretty}"
    let some shape := views[first.original.addr]? |
      throw s!"original data: missing captured record for {name.pretty}"
    if rows.any (fun row => row.hints.isNone) then
      throw s!"original data: unavailable original hints for {name.pretty}"
    let hint := first.hints.getD none
    let needsHint ← requiresHint views name rows shape
    if needsHint && rows.any (fun row => row.hints == some none) then
      throw s!"original data: missing definition hints for {name.pretty}"
    if rows.any (fun row => row.hints != some hint) then
      throw s!"original data: conflicting original hints for {name.pretty}"
    if hint != named.hints then out := { out with hints := out.hints.insert name hint }
  return out

/-- Populate only unchecked original data; no compiler driver calls this yet. -/
def finalizeOriginals (staging : OriginalStaging) (base : Ixon.Env) : Except String Ixon.Env := do
  let tables ← prepare staging base
  return { base with originals := tables.originals, originalHintOverrides := tables.hints }

/-- Every pre-existing environment field, including the canonical name lookup,
is independent of original-data finalization. This grants no judgment to originals. -/
structure OldFields (base out : Ixon.Env) : Prop where
  consts : out.consts = base.consts
  named : out.named = base.named
  blobs : out.blobs = base.blobs
  names : out.names = base.names
  comms : out.comms = base.comms
  addrToName : out.addrToName = base.addrToName
  main : out.main = base.main
  assumptions : out.assumptions = base.assumptions
  anonHints : out.anonHints = base.anonHints

theorem finalizeOriginals_frame {staging : OriginalStaging} {base out : Ixon.Env}
    (accepted : finalizeOriginals staging base = .ok out) : OldFields base out := by
  unfold finalizeOriginals at accepted
  cases prepared : prepare staging base with
  | error error => simp [prepared, bind, Except.bind] at accepted
  | ok tables =>
    simp only [prepared, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
    subst out
    constructor <;> rfl

end Ix.Compile.OriginalData

end
