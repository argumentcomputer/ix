module

public import Ix.Cli.ConstsFile
public import Ix.KernelCheck.Meta
public import Ix.Ixon.Projection

@[expose] public section

/-! Subject selection and observed-key coverage for the host record checker.
These helpers neither authenticate bytes nor establish aggregate admission.
The adapter must supply an authenticated input and record observations from
its actual run. Display-only name truncation is never used for selection. -/

namespace Ix.Cli.CheckLeanTargets

open Ix.Kernel Ix.Kernel.Reader
open Benchmarks.Kernel.CheckIxeStep

/-- An explicit empty request is different from requesting all subjects. -/
inductive Selection where
  | all
  | only (labels : Array String)

inductive Error where
  | selector (message : String)
  | input (label : String) (error : ReadError)
  | coverage (label message : String)

/-- Input labels are kept separately from fail-file labels (`#hex` versus
bare hex anonymously). A virtual source is only a derived projection. -/
structure Candidate where
  label : String
  fileLabel : String
  address : Address
  source : Option Ixon.Constant
  issue : Option ReadError := none

def Candidate.isContainer (c : Candidate) : Bool :=
  match c.source with | some { info := .muts _, .. } => true | _ => false

/-- Complete named inventory, including aliases. Container labels remain
available for a precise explicit-selector error, but are not declarations. -/
def namedCandidates (store : RecordStore) (names : Array (String × Address)) : Array Candidate :=
  (names.map fun (label, address) => ⟨label, label, address, store[address]?, none⟩).qsort
    (fun a b => a.label < b.label)

/-- Anonymous declarations include omitted member/constructor projections,
whose exact records are derived from the physical blocks. Supplied malformed
projections remain candidates, and an exact-key conflict is never hidden.
This inventories subjects only: it does not reconstruct the reader store,
so a body needing an omitted record still receives the reader's failure. -/
def anonymousCandidates (store : RecordStore) : Except Error (Array Candidate) := do
  let mut candidates : Std.HashMap Address Candidate := store.fold (init := {}) fun m a c =>
    m.insert a ⟨s!"#{a}", toString a, a, some c, none⟩
  for request in Ixon.Projection.requests store.toList do
    let record ← (Egress.writeProjection request.layout request.reference).mapError fun _ =>
      Error.input (toString request.reference.block) (.malformed "cannot encode member projection")
    let address := Ixon.Projection.address Address.blake3 record
    match candidates[address]? with
    | some old =>
      if !(old.source.any (Ixon.Projection.matchesRecord request)) then
        candidates := candidates.insert address
          { old with issue := some (.malformed "derived projection conflicts with the record at its address") }
    | none => candidates := candidates.insert address ⟨s!"#{address}", toString address, address, some record, none⟩
  return (candidates.toArray.map (·.2)).qsort (fun a b => a.address.cmpBytes b.address == .lt)

structure Target where
  label : String
  fileLabel : String
  address : Address
  reference : ConstRef Address
  key : Key .anon
  /-- The primary read that actually emits this declaration. A recursor's
  physical record can instead receive a borrowed row from this producer. -/
  producer : Address

/-- Resolve against the actual reader context, including projection table,
kind, position and constructor-index checks. An indexed recursor is emitted
by its inductive producer, not by its own empty standalone/stub reading. -/
def bindCandidate (s : Setup) (c : Candidate) : Except Error Target := do
  if let some e := c.issue then throw (.input c.label e)
  if c.isContainer then
    throw (.selector s!"{c.label}: physical block container; select a declaration member")
  let some source := c.source | throw (.input c.label (.malformed "selected record is missing"))
  let some reference := resolveSource s.cx.store c.address source
    | throw (.input c.label (.malformed "selected projection has invalid tables, owner, kind, or position"))
  let key ← (s.cx.memberKey reference).mapError (.input c.label)
  let mut producer := reference.block
  if let .member block i := reference then
    let some owner := s.cx.store block
      | throw (.input c.label (.malformed "selected declaration's owner is missing"))
    if (recursorMembers owner).any (·.1 == i) then
      let some entry := s.cx.index.recs[reference]?
        | throw (.input c.label (.declined "selected recursor has no indexed inductive producer"))
      producer := entry.block
  return { label := c.label, fileLabel := c.fileLabel, address := c.address, reference, key, producer }

/-- Direct selectors accept `#hex` as well as fail-file bare hex. Name
normalization is the existing shared `«»`-insensitive spelling rule. -/
def selectorKey (label : String) : String :=
  ConstsFile.normalizeName (if label.startsWith "#" then (label.drop 1).toString else label)

structure CandidateIndex where
  exact : Std.HashMap String (Array Candidate) := {}
  normalized : Std.HashMap String (Array Candidate) := {}

/-- Build once for a request list, retaining every ambiguous match. -/
def candidateIndex (inventory : Array Candidate) : CandidateIndex := Id.run do
  let mut index : CandidateIndex := {}
  for c in inventory do
    let exact := index.exact.insert c.label ((index.exact.getD c.label #[]).push c)
    let exact := if c.fileLabel == c.label then exact else
      exact.insert c.fileLabel ((exact.getD c.fileLabel #[]).push c)
    let key := selectorKey c.label
    let normalized := index.normalized.insert key ((index.normalized.getD key #[]).push c)
    index := { exact, normalized }
  return index

/-- Prefer exact spelling; otherwise require a unique normalized match.
Never select an arbitrary member of a flattened-name ambiguity. -/
def findIndexed (index : CandidateIndex) (label : String) : Except Error Candidate := do
  if label.startsWith "#" && (Address.fromString (label.drop 1).toString).isNone then
    throw (.selector s!"{label}: anonymous selector requires a 64-digit hexadecimal address")
  let exact := index.exact.getD label #[]
  let matched := if exact.isEmpty then index.normalized.getD (selectorKey label) #[] else exact
  match matched.toList with
  | [] => throw (.selector s!"{label}: no declaration matched")
  | [c] => pure c
  | cs => throw (.selector s!"{label}: ambiguous selector; matches {cs.map (·.label)}")

def findCandidate (inventory : Array Candidate) (label : String) : Except Error Candidate :=
  findIndexed (candidateIndex inventory) label

structure Plan where
  targets : Array Target
  /-- Number of resolved selected labels before the producer cap. -/
  requested : Nat
  omitted : Array String
  producers : Array Address
  /-- Complete check order, including supporting records and prelude. -/
  addresses : Array Address

/-- Include the dependencies of recursors read with an inductive and make
their producer edges explicit. CheckOrder then supplies the same iterative
postorder; cap only subjects, never this supporting dependency closure. -/
def dependencyEdges (s : Setup) : Std.HashMap Address (Array Address) := Id.run do
  let mut edges := s.extra
  for (a, source) in s.store do
    if owner a source == a then
      let deps := dependencies s.store s.cx.index s.extra a source
      edges := edges.insert a ((edges.getD a #[]) ++ deps)
  for (reference, entry) in s.cx.index.recs do
    if reference.block != entry.block then
      edges := edges.insert reference.block ((edges.getD reference.block #[]).push entry.block)
  return edges

/-- Resolve all explicit labels before applying the cap. Aliases count as
separate subjects while sharing one producer. `maxGroups` keeps whole
producer groups, including every selected alias of a retained producer. -/
def select (s : Setup) (preludeRoots : Array Address) (inventory : Array Candidate)
    (selection : Selection) (maxGroups : Option Nat := none) : Except Error Plan := do
  if maxGroups == some 0 then throw (.selector "--max must be greater than zero")
  let candidates ← match selection with
    | .all => pure (inventory.filter fun c => c.issue.isSome || !c.isContainer)
    | .only labels => do
      if labels.isEmpty then throw (.selector "explicit selector is empty")
      let index := candidateIndex inventory
      let mut out := #[]
      let mut seen : Std.HashSet String := {}
      for label in labels do
        let c ← findIndexed index label
        unless seen.contains c.label do
          seen := seen.insert c.label
          out := out.push c
      pure out
  if candidates.isEmpty then throw (.selector "no declaration subjects selected")
  let targets ← candidates.mapM (bindCandidate s)
  let mut groups : Array Address := #[]
  let mut groupSet : Std.HashSet Address := {}
  for t in targets do
    unless groupSet.contains t.producer do
      groupSet := groupSet.insert t.producer
      groups := groups.push t.producer
  let producers := match maxGroups with
    | none => groups
    | some n => groups.extract 0 (min n groups.size)
  let producerSet := producers.foldl (fun (set : Std.HashSet Address) a => set.insert a) {}
  let kept := targets.filter fun t => producerSet.contains t.producer
  let omitted := (targets.filter fun t => !producerSet.contains t.producer).map (·.label)
  let addresses := closure s.store (dependencyEdges s) (preludeRoots ++ producers)
  let ordered := addresses.foldl (fun (set : Std.HashSet Address) a => set.insert a) {}
  for t in kept do
    unless ordered.contains t.producer do
      throw (.input t.label (.malformed "selected producer is absent from the check order"))
  return { targets := kept, requested := targets.size, omitted, producers, addresses }

/-- Keys observed in the actual reading for each producer. A caller starts
with an empty map for each run and records only the Read/TierDecl it hands
to that run; this is untrusted execution evidence, not a theorem premise. -/
abbrev Produced := Std.HashMap Address (Std.HashSet (Key .anon))

def noteKeys (seen : Produced) (producer : Address) (keys : List (Key .anon)) : Produced :=
  seen.insert producer (keys.foldl (·.insert ·) {})

def noteRead (erase : Key md → Key .anon) (seen : Produced) (producer : Address) (rd : Read md) : Produced :=
  noteKeys seen producer ((rd.decls.toList.flatMap Benchmarks.Kernel.CheckIxeMeta.declaredKeys).map erase)

def noteTier (erase : Key md → Key .anon) (seen : Produced) (producer : Address)
    (decl : Tier.TierDecl md) : Produced :=
  noteKeys seen producer (decl.names.map erase)

structure TargetResult where
  target : Target
  outcome : String
  reason : String
  /-- The producing record's checker time; aliases share it, so sums must
  deduplicate producer addresses. Preparation/support time stays separate. -/
  micros : Nat

/-- Project actual producer rows to every selected label. A successful
owner row alone is insufficient: its exact selected key must have been
emitted. Missing/duplicate producer rows and absent keys fail closed. Reject,
decline and blocked rows retain their original classification and cause. -/
def results (plan : Plan) (rows : Array Row) (produced : Produced) : Except Error (Array TargetResult) := do
  if plan.targets.isEmpty then throw (.coverage "" "no selected declaration subjects")
  let mut byAddress : Std.HashMap Address Row := {}
  for row in rows do
    if byAddress.contains row.address then
      throw (.coverage (toString row.address) "duplicate producer outcome row")
    byAddress := byAddress.insert row.address row
  plan.targets.mapM fun t => do
    let some row := byAddress[t.producer]?
      | throw (.coverage t.label "selected producer has no outcome row")
    unless ["accept", "typed", "reject", "decline", "blocked"].contains row.outcome do
      throw (.coverage t.label s!"unknown producer outcome {row.outcome}")
    if row.outcome == "accept" || row.outcome == "typed" then
      unless (produced.getD t.producer {}).contains t.key do
        throw (.coverage t.label "selected key was not emitted by its actual producer")
    return { target := t, outcome := row.outcome, reason := row.reason, micros := row.micros }

end Ix.Cli.CheckLeanTargets
