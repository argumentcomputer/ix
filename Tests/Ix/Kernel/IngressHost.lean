/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Ingress
import Ix.Kernel.Egress
import Ix.Ixon.Admission
import Ix.Ixon.Projection
import Ix.Ixon.BlockOrder
import Ix.CompileDriver
import Ix.Meta
import Tests.Ix.Kernel.TutorialDefs

/-! Host integration only: compile existing tutorial inputs through
`Ix.CompileM`, serialize and load them with the ordinary host codec, then
submit their dependency-ordered records to `Ix.Kernel.checkEnv`. The loader,
ordering, compiler, and names are untrusted producers of in-memory input.
Every case also submits canonical record bytes to `Ix.Ixon.Admission.checkBytes`
and checks exact decoding plus the same verdict and reason as in-memory
admission. Both verdicts come from the certified checker. Each case separately
round-trips through the certified reader/writer and the production encoder.
-/

open Ix.Kernel

namespace Tests.Ix.Kernel.IngressHost

abbrev Store := Std.HashMap Address Ixon.Constant

def owner (address : Address) (source : Ixon.Constant) : Address :=
  match source.info with
  | .dPrj p => p.block
  | .iPrj p => p.block
  | .rPrj p => p.block
  | .cPrj p => p.block
  | _ => address

structure OrderState where
  active : Std.HashSet Address := {}
  done : Std.HashSet Address := {}
  ordered : Array (Address × Ixon.Constant) := #[]

/-- Host scheduling cannot authorize acceptance; `checkEnv` still validates
every reference against the installed prefix. -/
partial def visit (store : Store) (address : Address) : StateT OrderState (Except String) Unit := do
  let some source := store[address]? | throw s!"missing input constant {address}"
  let root := owner address source
  if root != address then return ← visit store root
  let state ← get
  if state.done.contains root then return
  if state.active.contains root then throw s!"cycle between primary blocks at {root}"
  modify fun state => { state with active := state.active.insert root }
  for ref in source.refs do
    if let some target := store[ref]? then
      if owner ref target != root then visit store ref
  modify fun state => { state with
    active := state.active.erase root
    done := state.done.insert root
    ordered := state.ordered.push (root, source) }

def orderedInput (env : Ixon.Env) (roots : List Lean.Name) : Except String Ingress.Constants := do
  let mut store : Store := {}
  for (address, lazyConst) in env.consts.toList do
    let source ← lazyConst.get
    store := store.insert address source
  let action := roots.forM fun name => do
    let some entry := env.named[Ix.Name.fromLeanName name]? | throw s!"missing compiled name {name}"
    visit store entry.addr
  let (_, state) ← action.run {}
  let projections := store.toArray.filter fun (address, source) =>
    Ingress.isProjection source.info && state.done.contains (owner address source)
  let projections := projections.qsort fun a b => a.1.cmpBytes b.1 == .lt
  return state.ordered.toList ++ projections.toList

structure Case where
  label : String
  seeds : List Lean.Name
  expected : String := "accept"
  mutateRecursor : Option (Ixon.Recursor → Ixon.Recursor) := none

def cases : List Case :=
  let basics := [`basicDef, `arrowType, `dependentType, `constType,
    `betaReduction, `betaReduction2, `forallSortWhnf, `levelParams, `inferVar]
  let families := [`False, `True, `And, `Or, `Nat, `List, `Eq, `Prod]
  basics.map (fun name => { label := name.toString, seeds := [name] }) ++
  families.map (fun name => { label := name.toString, seeds := [name, name ++ `rec] }) ++
  [ { label := "proof-irrelevance", seeds := [`proofIrrelevance] },
    { label := "K-reduction", seeds := [`ruleK] },
    { label := "natural-literal", seeds := [`natOfNatLit] },
    { label := "bad-sort", seeds := [`badDef], expected := "decline" },
    { label := "bad-declared-type", seeds := [`nonTypeType], expected := "decline" },
    { label := "tampered-Nat-rec-rule", seeds := [`Nat, `Nat.rec], expected := "decline",
      mutateRecursor := some fun r => { r with rules := r.rules.modify 0 fun rule => { rule with rhs := .var 0 } } },
    { label := "tampered-Nat-rec-fields", seeds := [`Nat, `Nat.rec], expected := "decline",
      mutateRecursor := some fun r => { r with rules := r.rules.modify 0 fun rule => { rule with fields := 1 } } },
    { label := "tampered-Nat-rec-header", seeds := [`Nat, `Nat.rec], expected := "decline",
      mutateRecursor := some fun r => { r with motives := 0, minors := r.minors + 1 } },
    { label := "tampered-Nat-rec-K", seeds := [`Nat, `Nat.rec], expected := "reject",
      mutateRecursor := some fun r => { r with k := true } } ]

def prepare (leanEnv : Lean.Environment) (test : Case) : IO (Ingress.Constants × Ingress.Blobs ×
    Option (ConstRef Address)) := do
  let raw := TutorialMeta.getRawConsts leanEnv
  let extras := raw.foldl (fun out ci => out.insert ci.name ci)
    (Std.HashMap.emptyWithCapacity raw.size)
  for name in test.seeds do
    unless (leanEnv.constants.find? name).isSome || extras.contains name do
      throw (IO.userError s!"{test.label}: missing source declaration {name}")
  let (needed, closed) := TutorialMeta.collectDepsWithExtras leanEnv extras test.seeds
  let extra := raw.toList.filterMap fun ci =>
    if needed.contains ci.name && !closed.any (·.1 == ci.name) then some (ci.name, ci) else none
  let compiled ← match ← Ix.CompileM.compileLeanConsts (closed ++ extra) (numWorkers := 1) with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"{test.label}: Lean compilation failed: {error}")
  let loaded ← match Ixon.deEnv compiled.bytes with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"{test.label}: host loading failed: {error}")
  let input ← match orderedInput loaded test.seeds with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"{test.label}: host ordering failed: {error}")
  let family := (loaded.named[Ix.Name.fromLeanName `Nat]?).bind fun named =>
    Ingress.reference input named.addr
  return (input, loaded.blobs.toList, family)

def egressRoundtrip (input : Ingress.Constants) (blobs : Ingress.Blobs)
    (family : Option (ConstRef Address)) : Except String Unit := do
  let records ← (Egress.readRecords input blobs family ({} : Config).fuel input).mapError reprStr
  let output ← (Egress.writeRecords input blobs family ({} : Config).fuel records).mapError reprStr
  unless output == input do throw "egress changed an address, record position, or constant field"
  let encoded := input.map fun (address, source) => (address, Ixon.serConstant source)
  let reencoded := output.map fun (address, source) => (address, Ixon.serConstant source)
  unless reencoded == encoded do throw "egress changed production Ixon bytes"

def byteLimits : Ix.Ixon.Admission.Limits :=
  ⟨1024, 1024, 16 * 1024 * 1024, 4 * 1024 * 1024, 1024 * 1024⟩

def maxProjections : Nat := 4096

def sameStore (left right : Ingress.Constants) : Bool :=
  (left.all fun (key, record) =>
    match Ingress.lookup right key with | some value => value == record | none => false) &&
  (right.all fun (key, record) =>
    match Ingress.lookup left key with | some value => value == record | none => false)

def referenceJson : ConstRef Address → Lean.Json
  | .member address index => Lean.Json.mkObj [
    ("kind", Lean.toJson "member"), ("block", Lean.toJson (toString address)),
    ("member", Lean.toJson index)]
  | .ctor address index ctor => Lean.Json.mkObj [
    ("kind", Lean.toJson "ctor"), ("block", Lean.toJson (toString address)),
    ("member", Lean.toJson index), ("constructor", Lean.toJson ctor)]

def run (leanEnv : Lean.Environment) (test : Case) : IO Bool := do
  let (input, blobs, family) ← prepare leanEnv test
  let input ← match test.mutateRecursor with
    | none => pure input
    | some mutate => do
      let mut changed := 0
      let mut output := #[]
      for (address, source) in input do
        let info := match source.info with
          | .recr recursor => .recr (mutate recursor)
          | info => info
        if let .recr _ := source.info then changed := changed + 1
        output := output.push (address, { source with info })
      unless changed == 1 do
        throw (IO.userError s!"{test.label}: mutation requires exactly one standalone recursor; found {changed}")
      pure output.toList
  let cfg : Config := {}
  let result := checkEnv.{1} cfg input blobs family
  let (outcome, reason) := match result with
    | .ok _ => ("accept", "")
    | .error (.rejected reason) => ("reject", reason)
    | .error (.declined reason) => ("decline", reason)
  let records := input.map fun (address, source) => (address, Ixon.serConstant source)
  let byteDecodeExact := match Ix.Ixon.Admission.decodeRecords byteLimits records with
    | .ok decoded => decoded == input
    | .error _ => false
  let (byteOutcome, byteReason) := match Ix.Ixon.Admission.checkBytes.{1} byteLimits cfg records blobs family with
    | .ok _ => ("accept", "")
    | .error (.kernel (.rejected reason)) => ("reject", reason)
    | .error (.kernel (.declined reason)) => ("decline", reason)
    | .error (.limit resource) => ("limit", reprStr resource)
    | .error (.decode position address reason) => ("decode", s!"record {position} at {address}: {reason}")
  let (egressExact, egressReason) := match egressRoundtrip input blobs family with
    | .ok _ => (true, "")
    | .error reason => (false, reason)
  -- Omit every projection: the new route must derive their exact physical
  -- keys and payloads, while preserving the original primary order.
  let primaryInput := Ix.Ixon.Projection.primaries input
  let primaryRecords := primaryInput.map fun (key, record) => (key, Ixon.serConstant record)
  let reconstructionExact := match Ix.Ixon.Projection.reconstruct maxProjections primaryInput with
    | .error _ => false
    | .ok reconstructed => sameStore reconstructed input &&
      Ix.Ixon.Projection.primaries reconstructed == primaryInput
  let (projectionOutcome, projectionReason) := match Ix.Ixon.Projection.checkBytes.{1}
      maxProjections byteLimits cfg primaryRecords blobs family with
    | .ok _ => ("accept", "")
    | .error (.admission (.kernel (.rejected reason))) => ("reject", reason)
    | .error (.admission (.kernel (.declined reason))) => ("decline", reason)
    | .error reason => ("projection-error", reprStr reason)
  let projectionsAgree := reconstructionExact && projectionOutcome == outcome && projectionReason == reason
  let orderLimits : Ix.Ixon.BlockOrder.Limits := {}
  let (orderOutcome, orderReason) := match Ix.Ixon.BlockOrder.checkBytes.{1}
      maxProjections byteLimits orderLimits cfg primaryRecords blobs family with
    | .ok _ => ("accept", "")
    | .error (.admission (.kernel (.rejected reason))) => ("reject", reason)
    | .error (.admission (.kernel (.declined reason))) => ("decline", reason)
    | .error reason => ("order-error", reprStr reason)
  let orderAgrees := orderOutcome == outcome && orderReason == reason
  let bytesAgree := byteOutcome == outcome && byteReason == reason && byteDecodeExact
  let passed := outcome == test.expected && bytesAgree && projectionsAgree && orderAgrees && egressExact
  let constantJson := records.map fun (address, bytes) => Lean.Json.mkObj [
    ("address", Lean.toJson (toString address)),
    ("ixonHex", Lean.toJson (hexOfBytes bytes))]
  let blobJson := blobs.map fun (address, bytes) => Lean.Json.mkObj [
    ("address", Lean.toJson (toString address)), ("hex", Lean.toJson (hexOfBytes bytes))]
  IO.println (Lean.Json.mkObj [
    ("case", Lean.toJson test.label), ("expected", Lean.toJson test.expected),
    ("fuel", Lean.toJson cfg.fuel), ("literalFamily", family.elim Lean.Json.null referenceJson),
    ("outcome", Lean.toJson outcome), ("reason", Lean.toJson reason),
    ("byteOutcome", Lean.toJson byteOutcome), ("byteReason", Lean.toJson byteReason),
    ("byteDecodeExact", Lean.toJson byteDecodeExact),
    ("maxProjections", Lean.toJson maxProjections),
    ("reconstructionExact", Lean.toJson reconstructionExact),
    ("projectionOutcome", Lean.toJson projectionOutcome),
    ("projectionReason", Lean.toJson projectionReason),
    ("orderOutcome", Lean.toJson orderOutcome), ("orderReason", Lean.toJson orderReason),
    ("comparisonLimit", Lean.toJson orderLimits.comparison),
    ("refinementLimit", Lean.toJson orderLimits.refinement),
    ("projectionInput", Lean.toJson (primaryRecords.map fun (key, bytes) => Lean.Json.mkObj [
      ("address", Lean.toJson (toString key)), ("ixonHex", Lean.toJson (hexOfBytes bytes))])),
    ("byteLimits", Lean.Json.mkObj [
      ("maxRecords", Lean.toJson byteLimits.maxRecords),
      ("maxBlobs", Lean.toJson byteLimits.maxBlobs),
      ("maxTotalBytes", Lean.toJson byteLimits.maxTotalBytes),
      ("maxRecordBytes", Lean.toJson byteLimits.maxRecordBytes),
      ("maxRecordUnivNodes", Lean.toJson byteLimits.maxRecordUnivNodes)]),
    ("egressExact", Lean.toJson egressExact), ("egressReason", Lean.toJson egressReason),
    ("passed", Lean.toJson passed), ("leanVersion", Lean.toJson Lean.versionString),
    ("constants", Lean.toJson constantJson), ("blobs", Lean.toJson blobJson)]).compress
  if outcome != test.expected then
    IO.eprintln s!"{test.label}: expected {test.expected}, got {outcome}: {reason}"
  if !bytesAgree then
    IO.eprintln s!"{test.label}: byte admission disagrees: {byteOutcome}: {byteReason}; exact decoding: {byteDecodeExact}"
  if !egressExact then IO.eprintln s!"{test.label}: egress failed: {egressReason}"
  if !projectionsAgree then
    IO.eprintln s!"{test.label}: projection reconstruction disagrees: {projectionOutcome}: {projectionReason}; exact store: {reconstructionExact}"
  if !orderAgrees then IO.eprintln s!"{test.label}: canonical block order disagrees: {orderOutcome}: {orderReason}"
  return passed

def main : IO UInt32 := do
  let leanEnv ← getCompileEnv #[`Tests.Ix.Kernel.TutorialDefs]
  let mut failed := 0
  for test in cases do
    unless ← run leanEnv test do failed := failed + 1
  IO.eprintln s!"Certified Ixon ingress, byte admission, and exact egress: {cases.length - failed}/{cases.length} host cases passed."
  return if failed == 0 then 0 else 1

end Tests.Ix.Kernel.IngressHost

def main : IO UInt32 := Tests.Ix.Kernel.IngressHost.main
