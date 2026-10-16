import IxC.Kernel.Admission
import IxC.Kernel.Tier.Check

/-! # The tiered Ixon entry: the logical check, then the typing tier

`checkBytesTiered hash binding` is `checkBytes` over the logical records,
followed by the typing tier (`Ix.Kernel.Tier.checkTierC`) over the tier
records, against the accepted logical environment:

    byte stage (all records) → admitBinding → preludeFor → decodeRecords
      → partitionTier → (fence) → checkConstantsWith (logical records)
      → readTier (tier records) → checkTierC

* **The byte stage runs over every record**: the batch limits, key
  uniqueness, authentication and canonical decoding are those of
  `checkBytes`, so every record, tier records included, is authenticated.
* **The partition** (`partitionTier`) sends to the tier a definition record
  whose safety is not safe (`partial` or `unsafe`, of any kind), an unsafe
  axiom, a definition block with such a member, and the definition
  projections of such a block; every other record stays on the logical
  side, unsafe inductive pieces included, where the reader declines them as
  `checkBytes` does. The partition decides coverage only: a record
  misrouted to the tier gets the weaker verdict, and a tier record left on
  the logical side is declined.
* **The logical part is `checkConstantsWith`, unchanged**, over the logical
  records. Every theorem about it applies to the accepted environment as
  stated (`Ix.Kernel.Admission.TierTheorems`).
* **The fence.** A logical record that names a tier record is refused
  before the logical check, with the reason (`TierError.fence`). Without
  that test it would still be refused: the logical store does not have the
  tier record, and the fold resolves every term it stores.
* **The tier reader** (`readTierRecord`) reads a tier record with the
  reader's own member reader, in a context over **all** the records
  (`streamContext`), so a key is the one the logical reading gives it. It
  skips the projection rewrite and the hints: a tier constant never
  unfolds. It reads an unsafe opaque as itself and an unsafe axiom as its
  header; it declines a block whose members are not all definitions of one
  safety, and a theorem with a safety that is not safe or an opaque with
  safety `partial` (no Lean declaration has those shapes).
* **The tier** runs at the index of the accepted logical environment, one
  `mkFEnv`, staged as Lean's lattice (`Tier.staged`). Every tier failure is
  a decline.

The existing entries (`checkBytes`, `checkConstantsWith`) are unchanged and
still decline every tier record: they remain the entries whose accept is
model-backed in full. -/

namespace Ix.Kernel.Admission

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader
open Ix.Kernel.Tier (TierDecl TierConst)

/-- Failures of the tiered entry, kept apart. -/
inductive TierError where
  /-- the logical entry's: bytes, binding, prelude, reader, fold -/
  | entry (error : Error)
  /-- a logical record (at `address`) names a tier record (`tier`) -/
  | fence (address : Address) (tier : Address)
  /-- the tier reader, at a record's position -/
  | read (position : Nat) (error : ReadError)
  /-- the tier fold, at the failing declaration's record position -/
  | tier (error : Ix.Kernel.CheckError .anon) (position : Nat)

instance : ToString TierError where
  toString
    | .entry e => toString e
    | .fence a t => s!"fence: the record {a} names the tier record {t}"
    | .read p e => s!"tier read at {p}: {e}"
    | .tier e p => s!"tier at {p}: {e}"

/-- How a caller classifies a failure of the tiered entry: the logical
entry's classification, a malformed tier record rejects, and everything
else declines (a fence violation, and every tier verdict: IxC cannot tell an
ill-typed tier declaration from one that types only by unfolding a tier
definition, which the tier refuses). -/
def TierError.outcome : TierError → Outcome
  | .entry e => e.outcome
  | .fence .. => .declined
  | .read _ (.malformed _) => .rejected
  | .read _ (.declined _) => .declined
  | .tier .. => .declined

/-- Whether a definition's safety puts it in the tier: anything but safe. -/
def tierSafety? : Ix.DefinitionSafety → Option Ix.Kernel.Tier.Safety
  | .part => some .part
  | .unsaf => some .unsaf
  | .safe => none

/-- Whether a record's info is a tier record: a definition whose safety is
not safe (of any kind: a theorem or an opaque with `partial`, which no Lean
declaration has, goes to the tier, which declines it), an unsafe axiom, or a
definition block with such a member. Unsafe inductive pieces are not: they
stay logical, where the reader declines them. -/
def isTierInfo : Ixon.ConstantInfo → Bool
  | .defn d => (tierSafety? d.safety).isSome
  | .axio a => a.isUnsafe
  | .muts ms => ms.any fun
    | .defn d => (tierSafety? d.safety).isSome
    | _ => false
  | _ => false

/-- **The partition** of decoded records: the logical records, in order, and
the tier records with their positions, in order. A tier block's definition
projections go with it. -/
def partitionTier (constants : List (Address × Ixon.Constant)) :
    List (Address × Ixon.Constant) × Array (Nat × Address × Ixon.Constant) := Id.run do
  let mut owners : Std.HashSet Address := {}
  for (a, c) in constants do
    if isTierInfo c.info then owners := owners.insert a
  let mut logical : Array (Address × Ixon.Constant) := #[]
  let mut tier : Array (Nat × Address × Ixon.Constant) := #[]
  for ((a, c), i) in constants.zipIdx do
    let isTier := isTierInfo c.info || match c.info with
      | .dPrj p => owners.contains p.block
      | _ => false
    if isTier then tier := tier.push (i, a, c) else logical := logical.push (a, c)
  return (logical.toList, tier)

/-- The fence's test: the first logical record that names a tier record, and
the tier record it names. -/
def fenceOf (logical : List (Address × Ixon.Constant)) (tier : Array (Nat × Address × Ixon.Constant)) :
    Option (Address × Address) :=
  let tierAddresses : Std.HashSet Address := tier.foldl (fun s (_, a, _) => s.insert a) {}
  logical.findSome? fun (a, c) => (c.refs.find? tierAddresses.contains).map (a, ·)

/-- A tier block member's header and value: a definition (`defn`) of the
block's safety `s`. A theorem or an opaque with that safety matches no Lean
declaration (Lean has no unsafe theorem, and a block never holds an
opaque), and a member of another safety makes a mixed-safety block: both
decline. -/
def tierMember (cx : Ctx md) (mr : MemberReader md) (ref : ConstRef Address)
    (s : Ix.DefinitionSafety) (d : Ixon.Definition) : ReadM (CVal md × CExpr md) := do
  unless d.safety == s do
    declined s!"tier: a {safetyWord s} block with a member of safety '{safetyWord d.safety}'"
  unless d.kind == .defn do
    declined s!"tier: a theorem or an opaque with safety '{safetyWord d.safety}'"
  let cv : CVal md := ⟨← cx.memberKey ref, List.range d.lvls.toNat, ← mr.read d.typ⟩
  pure (cv, ← mr.read d.value)

/-- **A tier record's declaration**, read against `cx`: a partial or unsafe
definition, or a block of them, as a definition block of that safety; an
unsafe opaque as itself; an unsafe axiom, its header; a definition
projection of a tier block, checked as the reader checks one, yields none.
The projection rewrite and the hints are skipped: a tier constant never
unfolds. -/
def readTierRecord (cx : Ctx md) (owner : Address) (c : Ixon.Constant) :
    ReadM (Option (TierDecl md)) := do
  match c.info with
  | .dPrj _ =>
    if (resolveSource cx.store owner c).isNone then
      malformed "projection record has invalid tables, owner, kind, or position"
    pure none
  | .defn d =>
    let self : Nat → Option (ReadM (CName md)) := fun i =>
      if i == 0 then some (cx.memberKey (.member owner 0)) else none
    let mr := MemberReader.mk' cx c id self
    let some s := tierSafety? d.safety | malformed "not a tier record"
    if d.kind == .opaq && s == .unsaf then
      let cv : CVal md := ⟨← cx.memberKey (.member owner 0), List.range d.lvls.toNat, ← mr.read d.typ⟩
      pure (some (.unsafeOpaque cv (← mr.read d.value)))
    else
      let m ← tierMember cx mr (.member owner 0) d.safety d
      pure (some (.defs s [m]))
  | .axio a =>
    unless a.isUnsafe do malformed "not a tier record"
    let mr := MemberReader.mk' cx c id (fun _ => none)
    let cv : CVal md := ⟨← cx.memberKey (.member owner 0), List.range a.lvls.toNat, ← mr.read a.typ⟩
    pure (some (.unsafeAxiom cv))
  | .muts ms =>
    let self : Nat → Option (ReadM (CName md)) := fun i =>
      if i < ms.size then some (cx.memberKey (.member owner i)) else none
    let mr := MemberReader.mk' cx c id self
    let some (Ixon.MutConst.defn d₀) := ms[0]?
      | declined "tier: a block that mixes definitions with other kinds"
    let some s := tierSafety? d₀.safety
      | declined s!"tier: a block of safety '{safetyWord d₀.safety}' with a member that is not safe"
    let mut members : Array (CVal md × CExpr md) := #[]
    for (m, i) in ms.zipIdx do
      let .defn d := m | declined "tier: a block that mixes definitions with other kinds"
      members := members.push (← tierMember cx mr (.member owner i) d₀.safety d)
    pure (some (.defs s members.toList))
  | _ => malformed "not a tier record"

/-- The tier records' declarations, each with its record's position. -/
def readTier (cx : Ctx md) (tier : Array (Nat × Address × Ixon.Constant)) :
    Except (Nat × ReadError) (Array (Nat × TierDecl md)) := do
  let mut out : Array (Nat × TierDecl md) := #[]
  for (i, a, c) in tier do
    match readTierRecord cx a c with
    | .error e => throw (i, e)
    | .ok none => pure ()
    | .ok (some d) => out := out.push (i, d)
  return out

/-- **The tiered entry over decoded records**: the partition, the fence,
`checkConstantsWith` over the logical records, then the tier reader and the
tier fold at the accepted environment's index. -/
def checkConstantsTiered (hash : ByteArray → Address) (t : Ix.Kernel.RoleTable) (pre : Prelude .anon)
    (constants : List (Address × Ixon.Constant)) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except TierError (Ix.Kernel.Env .anon × List (TierConst .anon)) := do
  let (logical, tier) := partitionTier constants
  if let some (a, r) := fenceOf logical tier then throw (.fence a r)
  let env ← (checkConstantsWith hash t pre logical blobs hint).mapError .entry
  let tds ← (readTier (streamContext hash t pre constants blobs hint) tier).mapError
    fun (i, e) => .read i e
  match Ix.Kernel.Tier.checkTierC (Ix.Kernel.mkFEnv env) (tds.toList.map (·.2)) with
  | .ok (_, ts) => pure (env, ts)
  | .error (e, k) => throw (.tier e ((tds[k]?.map (·.1)).getD k))

/-- **The tiered Ixon entry**: the byte stage over every record (batch
limits, key uniqueness, authentication), the role table's admission, the
committed prelude read under it, canonical decoding, and then
`checkConstantsTiered`. The result is the logical environment, model-backed
as `checkBytes`'s, and the tier constants, typed with every tier constant
opaque (`Ix.Kernel.Admission.checkBytesTiered_ok`). -/
def checkBytesTieredUsing (prelude : Ix.Kernel.RoleTable → Except String (Prelude .anon))
    (hash : ByteArray → Address) (binding : Binding) (limits : Limits)
    (records : Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except TierError (Ix.Kernel.Env .anon × List (TierConst .anon)) := do
  (preflight limits records blobs).mapError (.entry ∘ Error.ofBytes)
  (uniqueKeys records blobs).mapError (.entry ∘ Error.ofBytes)
  (authenticate hash records blobs).mapError (.entry ∘ Error.ofBytes)
  let t ← (admitBinding hash binding).mapError (.entry ∘ .binding)
  let pre ← (prelude t).mapError (.entry ∘ .prelude)
  let constants ← (decodeRecords limits records).mapError (.entry ∘ Error.ofBytes)
  checkConstantsTiered hash t pre constants blobs hint

/-- **The tiered Ixon entry** behind the committed prelude read under the
admitted table (`checkBytesTieredUsing preludeFor`; the theorems are stated
over the prelude source, so that no proof unfolds the committed data). -/
def checkBytesTiered (hash : ByteArray → Address) (binding : Binding) (limits : Limits)
    (records : Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except TierError (Ix.Kernel.Env .anon × List (TierConst .anon)) :=
  checkBytesTieredUsing preludeFor hash binding limits records blobs hint

end Ix.Kernel.Admission
