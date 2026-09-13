import Compilatrix.Modular.Assemble

/-! Deterministic dependency scheduling and reuse of already checked units. -/

namespace Compilatrix.Modular

open Ixon (Address)

structure Cache (policy : Policy) where
  units : List (CheckedUnit policy) := []

inductive Action where
  | produced
  | reused
  | checkedRecord
  deriving BEq, Repr

def Action.name : Action → String
  | .produced => "produced"
  | .reused => "reused"
  | .checkedRecord => "checked-record"

structure Observation where
  name : String
  key : Address
  action : Action
  candidates : Nat
  proofObligations : Nat
  contextConstants : Nat
  importBindings : Nat
  sourceNodeWork : Nat
  queryBytes : Nat
  outputBytes : Nat
  deriving Repr

def observation {policy} (unit : CheckedUnit policy) (action : Action) : Observation :=
  let owned := Ixon.Work.programStats unit.input.constants
  let context := Ixon.Work.programStats unit.context.constants
  { name := unit.input.name, key := unit.key, action
    candidates := owned.certificateCandidates
    proofObligations := Modular.proofObligations unit.input.constants
    contextConstants := context.constants
    importBindings := context.constants + unit.context.blobs.length + unit.context.declarations.length
    sourceNodeWork := proofWork unit.input.constants unit.context.constants
    queryBytes := unit.query.size
    outputBytes := (IxIR.Encoding.list targetEntryBytes unit.output).size }

structure Built (policy : Policy) where
  units : List (CheckedUnit policy)
  cache : Cache policy
  observations : List Observation

/-- The typed cache is process-local. Disk records enter it only through
`restore`, which checks every record independently in dependency order. -/
def Cache.find? {policy} (cache : Cache policy) (input : Input)
    (imports : List (CheckedUnit policy)) (prepared : Context) : Option (CheckedUnit policy) := do
  let interfaces := imports.map (·.interface)
  let query := queryBytes policy input interfaces
  let key := Address.blake3 query
  let unit ← cache.units.find? fun unit => unit.key == key && unit.query == query
  if unit.input ≠ input || unit.interfaces ≠ interfaces ||
      unit.context.constants ≠ prepared.constants || unit.context.blobs ≠ prepared.blobs ||
      unit.context.natBlock ≠ prepared.natBlock then none
  else
    let declarations ← (unionEntries (unit.output ++ prepared.declarations)).toOption
    if unit.context.declarations = declarations then some unit else none

def Cache.insert {policy} (cache : Cache policy) (unit : CheckedUnit policy) : Cache policy :=
  ⟨unit :: cache.units.filter (fun old => old.input.name != unit.input.name)⟩

/-- A canonical-address hit still compares complete owned constants. The
ordinary certificate lookup separately checks all current input, interface,
literal, policy, and target-context bindings. -/
def Cache.addressEvidence? {policy} (cache : Cache policy) (input : Input) :
    Option (PLift (AddressEvidence input.constants)) :=
  cache.units.findSome? fun unit =>
    if unit.input.name == input.name then unit.addressEvidence? input.constants else none

/-- Consumer-supplied partitions retain each Ixon mutual constant intact.
Cross-unit cycles are rejected; a recursive SCC must belong to one unit. -/
def preflightInputs (limits : Limits) (policy : Policy) (inputs : List Input) : Except String Unit := do
  ensure (!inputs.isEmpty && inputs.length ≤ limits.maxUnits) "aggregate unit count limit"
  let names := inputs.map (·.name)
  ensure (names.eraseDups == names) "duplicate unit name"
  let count := inputs.foldl (fun total input => total + input.constants.length) 0
  ensure (count ≤ limits.maxConstants) "aggregate source constant limit"
  let constants := inputs.flatMap (·.constants)
  let addresses := constants.map (·.1)
  ensure (addresses.eraseDups == addresses) "duplicate ownership of a source constant"
  let stats := Ixon.Work.programStats constants
  ensure (proofObligations constants ≤ limits.maxCandidates &&
    stats.expandedExpressionUnits ≤ limits.maxExpandedUnits) "aggregate source size limit"
  for input in inputs do
    ensure (input.imports.all names.contains) "unit import names an absent dependency"
    preflightUnit policy input.constants

private def lookupImports {policy} (done : List (CheckedUnit policy)) (input : Input) :
    Option (List (CheckedUnit policy)) :=
  input.imports.mapM fun name => done.find? (fun unit => unit.input.name == name)

private def charge (limits : Limits) (policy : Policy) (input : Input) (prepared : Context)
    (usedBindings usedWork usedBytes : Nat) (imports : List (CheckedUnit policy)) :
    Except String (Nat × Nat × Nat) := do
  let own := Ixon.Work.programStats input.constants
  -- Erasure may add declarations; the source-derived counter bounds them
  -- before either the producer or certificate checker is called.
  let bindings := usedBindings + prepared.constants.length + prepared.blobs.length +
    prepared.declarations.length + own.erasedDeclarations
  let work := usedWork + proofWork input.constants prepared.constants
  let bytes := usedBytes + (queryBytes policy input (imports.map (·.interface))).size
  ensure (bindings ≤ limits.maxImportBindings) "aggregate import binding limit"
  ensure (work ≤ limits.maxCertificateWork) "aggregate certificate work limit"
  ensure (bytes ≤ limits.maxBytes) "aggregate source query byte limit"
  return (bindings, work, bytes)

/-- `records = some ...` is strict recovery, so stale, missing, or malformed
evidence rejects the run. Ordinary builds can reuse checked objects or produce
new evidence. No cache lookup returns an unchecked proof. -/
private def schedule (limits : Limits) (policy : Policy)
    (records : Option (List (String × Record))) :
    Nat → List Input → List (CheckedUnit policy) → Cache policy →
      List Observation → Nat → Nat → Nat → Except String (Built policy)
  | _, [], done, cache, observations, _, _, _ =>
      .ok ⟨done.reverse, cache, observations.reverse⟩
  | 0, _ :: _, _, _, _, _, _, _ => .error "cross-unit dependency cycle; keep the recursive group in one unit"
  | rounds + 1, pending, done, cache, observations, usedBindings, usedWork, usedBytes => do
      let mut next := []
      let mut completed := done
      let mut retained := cache
      let mut observed := observations
      let mut bindings := usedBindings
      let mut work := usedWork
      let mut bytes := usedBytes
      let mut progress := false
      for input in pending do
        match lookupImports completed input with
        | none => next := input :: next
        | some imports =>
            let known := match records with
              | some _ => none
              | none => retained.addressEvidence? input
            let prepared ← (prepareChecked limits policy input imports known).mapError
              (fun message => s!"{input.name}: {message}")
            let (nextBindings, nextWork, nextBytes) ← charge limits policy input prepared.context
              bindings work bytes imports
            let (unit, action) ← match records with
              | some supplied => do
                  let some (_, record) := supplied.find? (fun entry => entry.1 == input.name)
                    | throw s!"missing retained source certificate for {input.name}"
                  let unit ← (checkUnitPrepared limits policy input imports prepared record).mapError
                    (fun message => s!"{input.name}: {message}")
                  pure (unit, Action.checkedRecord)
              | none =>
                  match retained.find? input imports prepared.context with
                  | some unit => pure (unit, Action.reused)
                  | none => do
                      let unit ← (produceUnitPrepared limits policy input imports prepared).mapError
                        (fun message => s!"{input.name}: {message}")
                      pure (unit, Action.produced)
            let outputBytes := (IxIR.Encoding.list targetEntryBytes unit.output).size
            ensure (nextBytes + outputBytes ≤ limits.maxBytes) "aggregate certificate byte limit"
            bindings := nextBindings
            work := nextWork
            bytes := nextBytes + outputBytes
            completed := unit :: completed
            retained := retained.insert unit
            observed := observation unit action :: observed
            progress := true
      if !progress then throw "cross-unit dependency cycle; keep the recursive group in one unit"
      schedule limits policy records rounds next.reverse completed retained observed bindings work bytes

private def run (limits : Limits) (policy : Policy) (inputs : List Input)
    (cache : Cache policy) (records : Option (List (String × Record))) : Except String (Built policy) := do
  preflightInputs limits policy inputs
  ensure (cache.units.length ≤ limits.maxUnits) "checked source cache entry limit"
  let mut cacheBytes := 0
  let mut cacheBindings := 0
  for unit in cache.units do
    cacheBytes := cacheBytes + (← unit.record.preflight limits)
    cacheBindings := cacheBindings + unit.context.constants.length +
      unit.context.blobs.length + unit.context.declarations.length
    ensure (cacheBytes ≤ limits.maxBytes) "checked source cache byte limit"
    ensure (cacheBindings ≤ limits.maxImportBindings) "checked source cache binding limit"
  if let some supplied := records then
    ensure (supplied.length == inputs.length &&
      (supplied.map (·.1)).eraseDups.length == supplied.length)
      "missing, duplicate, or extra retained unit records"
  let built ← schedule limits policy records (inputs.length + 1) inputs [] cache [] 0 0 0
  -- Preserve the caller's source order for exact monolithic artifact comparisons.
  let units ← inputs.mapM fun input =>
    match built.units.find? (fun unit => unit.input.name == input.name) with
    | some unit => pure unit
    | none => throw "internal: scheduled source unit is absent"
  let _ ← programOf limits policy units
  return { built with units, cache := ⟨units⟩ }

def build (limits : Limits) (policy : Policy) (inputs : List Input)
    (cache : Cache policy := {}) : Except String (Built policy) :=
  run limits policy inputs cache none

def restore (limits : Limits) (policy : Policy) (inputs : List Input)
    (records : List (String × Record)) : Except String (Built policy) :=
  run limits policy inputs {} (some records)

end Compilatrix.Modular
