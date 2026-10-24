/-
  Ix.AuxGen.Report: the acceptance table of the generated auxiliaries, as the
  compile report carries it (AuxGen M5; the plan is `auxgen-m5.md` §13).

  **What has a row.** The rows cover the promotion route and changed blocks'
  regenerated auxiliaries:
  * every name the compile driver promoted with an original form (the compile
    of Lean's own form of a generated auxiliary, grafted into its
    `Named.original` at the original-form promotion), with its byte identity;
  * every regenerated auxiliary of a changed block, under the display name it
    is published at (Pass 3 moves a changed block's Ix auxiliaries to `_ix`
    names), with the aux tail's Source verdict and no identity (it has no
    original form).

  **Pass 3's images under Lean names have no row, by design.** A changed
  block's Lean auxiliary names denote Pass 3's images, whose `Named.original`
  Pass 3's image blocks graft. They are classified by the changed set as
  `imageHead`, and as `regenerated` by its rule over this table
  (`regenerated` iff the name has an original form, is in the input, and is
  not `identical` here): a name without a row is never `identical`, so it is
  in the set (fail closed). Their own acceptance is not this table's: they
  are changed cones, validated by the CQ5.4 route.

  Each row has the auxiliary's kind and its verdict:
  * `identical`: the published record's bytes are the original form's (and,
    for a projection, so are its block's), decided by the driver where both
    records are in hand; the record is unchanged. Only the promotion route
    decides it: the row carries the address of the record the driver compared
    (`AuxRow.addr`), and a tail verdict of `identical` is refused (AuxGen B9d);
  * `accepted`: regenerated, and Source mode accepted it at generation;
  * `exempt`: outside every statement (an unsafe block's auxiliary, or one
    blocked behind an unsafe constant);
  * `refused`: regenerated, and Source mode refused it or did not check it.

  The table is a function of the facts the compile gathers (`AuxTable.ofFacts`).
  Its rows are sorted by `Ix.Name.cmpRaw`, the structural order on names
  (`.eq` exactly on equal names), and `AuxTable.verdict?` looks a name up by
  it: no stored hash decides a lookup. This module imports only
  `Ix.Environment`, so a consumer (the changed set's classifier) reads the
  table without importing the compiler. Nothing here is serialized.
-/
module
public import Ix.Environment
public section

namespace Ix.AuxGen

/-- **A generated auxiliary's kind** (AuxGen M5). -/
inductive GeneratedKind where
  | recursor
  | casesOnDef
  | recOnDef
  /-- a Type-level `.below` definition -/
  | belowDef
  /-- a Prop-level `.below` family: its inductives and constructors -/
  | belowFamily
  /-- a Prop-level `.below` family's generated recursor -/
  | belowRecursor
  | brecOnDef
  | brecOnGo
  | brecOnEq
  /-- a promoted name no aux tail reported generating -/
  | other
  deriving BEq, Inhabited, Repr

instance : ToString GeneratedKind where
  toString
    | .recursor => "rec"
    | .casesOnDef => "casesOn"
    | .recOnDef => "recOn"
    | .belowDef => "below"
    | .belowFamily => "below (Prop family)"
    | .belowRecursor => "below.rec"
    | .brecOnDef => "brecOn"
    | .brecOnGo => "brecOn.go"
    | .brecOnEq => "brecOn.eq"
    | .other => "other"

/-- **A generated auxiliary's verdict at generation** (AuxGen M5). -/
inductive AuxVerdict where
  /-- the published record's bytes are the bytes of the compile of Lean's own
  form under the same name (and, for a projection, so are its block's): the
  record is unchanged, and the input's Source acceptance covers it -/
  | identical
  /-- regenerated (other bytes), and Source mode accepted it at generation -/
  | accepted
  /-- outside every statement: an unsafe block's auxiliary -/
  | exempt (why : String)
  /-- regenerated, and Source mode refused it or did not check it -/
  | refused (why : String)
  deriving BEq, Inhabited, Repr

/-- One row of the acceptance table. -/
structure AuxRow where
  /-- the published name (a key of the artifact's `named`) -/
  name : Name
  kind : GeneratedKind
  verdict : AuxVerdict
  /-- AuxGen B9d: a promoted name's row, the address of the published record the
  driver compared with the original form (`Named.addr` at the promotion); `none`
  for a displayed auxiliary's row (it has no original form) -/
  addr : Option Address := none
  deriving Inhabited, BEq, Repr

/-! ## Name-sorted arrays -/

/-- The entries sorted by `Ix.Name.cmpRaw`, the first of each name kept. -/
def sortByName {β : Type} (xs : Array (Name × β)) : Array (Name × β) := Id.run do
  let sorted := xs.qsort fun a b => Name.cmpRaw a.1 b.1 == .lt
  let mut out : Array (Name × β) := #[]
  for e in sorted do
    match out.back? with
    | some last => if Name.cmpRaw last.1 e.1 != .eq then out := out.push e
    | none => out := out.push e
  return out

/-- The element whose key is `n` in an array sorted by its keys under
`Ix.Name.cmpRaw`, by binary search (fuel: the array's size, which bounds the
steps). -/
def findSorted? {α : Type} (xs : Array α) (key : α → Name) (n : Name) : Option α :=
  go 0 xs.size (xs.size + 1)
where
  go (lo hi : Nat) : Nat → Option α
    | 0 => none
    | fuel + 1 =>
      if lo < hi then
        let mid := (lo + hi) / 2
        match xs[mid]? with
        | none => none
        | some x =>
          match Name.cmpRaw n (key x) with
          | .lt => go lo mid fuel
          | .gt => go (mid + 1) hi fuel
          | .eq => some x
      else none

/-- The entry of `n` in an array sorted by `sortByName`. -/
def findByName? {β : Type} (xs : Array (Name × β)) (n : Name) : Option β :=
  (findSorted? xs (·.1) n).map (·.2)

/-! ## The table -/

/-- **The acceptance table** (AuxGen M5): one row per promoted name, sorted by
`Ix.Name.cmpRaw`. -/
structure AuxTable where
  rows : Array AuxRow := #[]
  deriving Inhabited

namespace AuxTable

/-- Why a regenerated auxiliary of a block whose layout is Lean's has no
acceptance: the aux tail admits only flat and nested blocks' auxiliaries
(`auxgen-m5.md` §2.1 (a)). -/
def lateReason : String := "not admitted at generation (Lean layout)"

/-- The prefix of the exempt reason of a tail whose own block Source mode does
not accept (AuxGen M5b). -/
def notAcceptedPrefix : String := "block not Source-accepted: "

/-- Why a tail verdict of `identical` is refused (AuxGen B9d): identity is
decided on bytes at the original-form promotion, never by a tail, so a row is
`identical` only on the promotion route, at the address it compared. -/
def admittedIdenticalReason : String :=
  "identical admitted by a tail (identity is decided only at the original-form promotion)"

/-- **A tail's verdicts given its block's Source status** (AuxGen M5b;
`AuxOracle.blockStatus`): unchanged for a block Source mode accepts (`none`), so
a refusal there stays a refusal (the stop rule); for a block it does not accept,
every generated auxiliary of the block (`names`) is exempt with the status. That
block's input is outside `SourceAccepts`, so there is no acceptance claim to
make, and a changed-set classifier still puts a non-identical exempt row in the
set (`regenerated`). -/
def withBlockStatus (status : Option String) (names : Array Name)
    (verdicts : Array (Name × AuxVerdict)) : Array (Name × AuxVerdict) :=
  match status with
  | none => verdicts
  | some why => names.map fun n => (n, .exempt s!"{notAcceptedPrefix}{why}")

/-- The table of the facts a compile gathers:
* `identity`: each promoted name, whether its published record is
  byte-identical to its original form's, and the address of the published
  record the driver compared (AuxGen B9d);
* `generated`: each generated auxiliary's kind;
* `admitted`: the verdict on each auxiliary an aux tail checked (`accepted`,
  `refused` with Source mode's reason, or `exempt` when blocked behind an
  unsafe constant);
* `exempt`: the auxiliaries of an unsafe block's tail, with the reason;
* `display`: each generated auxiliary of a changed block that Pass 3 moved to
  a display name, with the name it is published at.

A promoted name's row is `identical` when the bytes agree, and carries the
compared address; otherwise, as a displayed auxiliary's row (under its display
name, with the generated name's kind): `exempt` for an unsafe block's
auxiliary, else the tail's verdict (a tail's `identical` refused,
`admittedIdenticalReason`), else refused as late (`lateReason`). So a row is
`identical` only on the promotion route. -/
def ofFacts (identity : Array (Name × Bool × Address)) (generated : Array (Name × GeneratedKind))
    (admitted : Array (Name × AuxVerdict)) (exempt : Array (Name × String))
    (display : Array (Name × Name) := #[]) : AuxTable :=
  let generated := sortByName generated
  let admitted := sortByName admitted
  let exempt := sortByName exempt
  let checked (n : Name) : AuxVerdict :=
    match findByName? exempt n with
    | some why => .exempt why
    | none =>
      match findByName? admitted n with
      | some .identical => .refused admittedIdenticalReason
      | some v => v
      | none => .refused lateReason
  let promoted : Array (Name × AuxRow) := identity.map fun (n, same, a) =>
    (n, { name := n, kind := (findByName? generated n).getD .other
          verdict := if same then .identical else checked n, addr := some a })
  let displayed : Array (Name × AuxRow) := display.map fun (n, d) =>
    (d, { name := d, kind := (findByName? generated n).getD .other, verdict := checked n })
  { rows := (sortByName (promoted ++ displayed)).map (·.2) }

/-- `n`'s verdict, by binary search on `Ix.Name.cmpRaw`. -/
def verdict? (t : AuxTable) (n : Name) : Option AuxVerdict :=
  (findSorted? t.rows (·.name) n).map (·.verdict)

/-- AuxGen B9d: the address `n`'s row carries (the published record the
driver compared at the promotion), by binary search on `Ix.Name.cmpRaw`;
`none` without a row or for a displayed auxiliary's row. -/
def addr? (t : AuxTable) (n : Name) : Option Address :=
  (findSorted? t.rows (·.name) n).bind (·.addr)

/-- **Whether `n`'s published record is the compile of Lean's own form**,
decided on bytes by the driver: the evidence a changed-set classifier reads for
the `regenerated` cause. A name without a row is not identical (fail closed). -/
def identical (t : AuxTable) (n : Name) : Bool :=
  t.verdict? n == some .identical

/-- The rows' counts by verdict: identical, accepted, exempt (and of those, the
ones whose block Source mode does not accept), refused, and of the refused those
refused as late. -/
structure Counts where
  identical : Nat := 0
  accepted : Nat := 0
  exempt : Nat := 0
  notAccepted : Nat := 0
  refused : Nat := 0
  late : Nat := 0
  deriving Inhabited, BEq, Repr

def counts (t : AuxTable) : Counts :=
  t.rows.foldl (init := {}) fun c r => match r.verdict with
    | .identical => { c with identical := c.identical + 1 }
    | .accepted => { c with accepted := c.accepted + 1 }
    | .exempt why =>
      { c with exempt := c.exempt + 1
               notAccepted := c.notAccepted + (if why.startsWith notAcceptedPrefix then 1 else 0) }
    | .refused why =>
      { c with refused := c.refused + 1, late := c.late + (if why == lateReason then 1 else 0) }

/-- One line. -/
def Counts.line (c : Counts) : String :=
  s!"{c.identical} identical, {c.accepted} accepted, {c.exempt} exempt ({c.notAccepted} of a block \
    Source does not accept), {c.refused} refused ({c.late} late)"

/-- The counts by kind and verdict, as `kind | verdict: n` lines in a fixed
order. -/
def byKind (t : AuxTable) : Array String := Id.run do
  let verdictOf : AuxVerdict → String
    | .identical => "identical"
    | .accepted => "accepted"
    | .exempt _ => "exempt"
    | .refused why => if why == lateReason then "refused (late)" else "refused"
  let mut keys : Array String := #[]
  let mut counts : Array Nat := #[]
  for r in t.rows do
    let k := s!"{r.kind} | {verdictOf r.verdict}"
    match keys.findIdx? (· == k) with
    | some i => counts := counts.modify i (· + 1)
    | none =>
      keys := keys.push k
      counts := counts.push 1
  let lines := (keys.zip counts).map fun (k, n) => s!"{k}: {n}"
  return lines.qsort (· < ·)

/-- The first `cap` refused rows, as `name: reason`. -/
def refusals (t : AuxTable) (cap : Nat := 16) : Array String :=
  let refused := t.rows.filter fun r => match r.verdict with | .refused _ => true | _ => false
  (refused.extract 0 cap).map fun r => match r.verdict with
      | .refused why => s!"{r.name.pretty} ({r.kind}): {why}"
      | _ => r.name.pretty

end AuxTable

/-! ## The identity rows against the artifact (AuxGen B9d) -/

/-- **The identity rows against the published names** (AuxGen B9d), as the
compile report prints them:
* the rows, and the names they cover;
* the names with more than one row (an original-form promotion can reach a
  name another promotion reached), and of those the ones whose rows disagree,
  on identity or on the compared address;
* the `identical` rows checked against the artifact's final `named`, and of
  those the ones whose name is published at another address (`stale`: a later
  merge overwrote it) or not at all (a later block failure withdrew it).

The statements lane's decided check refuses a report with a disagreeing
duplicate, or with a stale or unpublished `identical` row. -/
structure IdentityStats where
  rows : Nat := 0
  names : Nat := 0
  duplicated : Nat := 0
  disagreeing : Nat := 0
  checked : Nat := 0
  stale : Nat := 0
  unpublished : Nat := 0
  deriving Inhabited, BEq, Repr

namespace IdentityStats

/-- A run of one name's rows closed: its count and whether they all agree. -/
def close (s : IdentityStats) (count : Nat) (agree : Bool) : IdentityStats :=
  { s with names := s.names + 1
           duplicated := s.duplicated + (if count > 1 then 1 else 0)
           disagreeing := s.disagreeing + (if agree then 0 else 1) }

/-- No duplicate disagrees and every `identical` row is published at its
compared address. -/
def ok (s : IdentityStats) : Bool := s.disagreeing == 0 && s.stale == 0 && s.unpublished == 0

/-- One line. -/
def line (s : IdentityStats) : String :=
  s!"{s.rows} rows over {s.names} names; {s.duplicated} names with more than one row \
    ({s.disagreeing} disagreeing); {s.checked} identical rows against the final named: \
    {s.stale} at another address, {s.unpublished} unpublished"

end IdentityStats

/-- The identity rows' statistics (`IdentityStats`) against `published?`, the
artifact's final `named` address of a name. Duplicates are found on the rows
sorted by `Ix.Name.cmpRaw` (`.eq` exactly on equal names). -/
def identityStats (identity : Array (Name × Bool × Address))
    (published? : Name → Option Address) : IdentityStats := Id.run do
  let sorted := identity.qsort fun a b => Name.cmpRaw a.1 b.1 == .lt
  let mut st : IdentityStats := { rows := identity.size }
  -- the current run: its name, its first row's identity and address, its count,
  -- whether every row so far agrees with the first
  let mut cur : Option (Name × Bool × Address × Nat × Bool) := none
  for (n, same, a) in sorted do
    match cur with
    | some (m, s0, a0, k, agree) =>
      if Name.cmpRaw m n == .eq then
        cur := some (m, s0, a0, k + 1, agree && same == s0 && a == a0)
      else
        st := st.close k agree
        cur := some (n, same, a, 1, true)
    | none => cur := some (n, same, a, 1, true)
  if let some (_, _, _, k, agree) := cur then st := st.close k agree
  for (n, same, a) in identity do
    if same then
      st := { st with checked := st.checked + 1 }
      match published? n with
      | none => st := { st with unpublished := st.unpublished + 1 }
      | some a' => if a' != a then st := { st with stale := st.stale + 1 }
  return st

end Ix.AuxGen

end
