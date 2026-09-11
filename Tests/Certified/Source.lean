/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Certified.FeatureCases
import Ix.Kernel.Certified
import Ix.Certified.Suggest

/-! Actual lazy Ixon environments, empty/cached TcM runs, full declaration
subjects and hostile cache/state/selection inputs for C5. -/

namespace Tests.Certified.Source

open Ix.Theory Ix.Theory.Certified Ix.Certified Ix.Kernel Serialize
open Lean (toJson)

set_option maxRecDepth 32768
set_option maxHeartbeats 32000000

def cases : List Case :=
  (Corpus.positive.map fun c => {
    name := c.name, profile := Fixtures.profile,
    target := c.target, blobs := c.blobs, literals := [], references := [],
    blocks := c.blobs.map fun (a, _) => (0, a) }) ++
  Features.positive.filterMap fun s => make? s.name s.signature s.input

#guard cases.length = 42

def selection (c : Case) : InputSelection := ⟨c.blobs.map Prod.fst, c.literals.map Prod.fst⟩

/-- All constants are real offset windows with no materialized cache. -/
def source (c : Case) : Ixon.Env := Id.run do
  let mut env : Ixon.Env := { main := some c.target }
  for (a, bytes) in c.blobs do
    let backing := (ByteArray.mk #[17, 19]) ++ bytes ++ (ByteArray.mk #[23])
    env := { env with consts := env.consts.insert a (Ixon.LazyConstant.ofSlice backing 2 bytes.size) }
  for (a, bytes) in c.literals do env := { env with blobs := env.blobs.insert a bytes }
  return env

def subjects (c : Case) : List Address :=
  c.blocks.map Prod.snd

def accepted (c : Case) : Bool :=
  let env := source c
  (suggestSource? 6400 env c.profile c.target (selection c)).any fun w =>
    acceptsCertifiedSource.{0} 6400 env c.profile c.target (selection c) w

def storeAccepted (c : Case) : Bool :=
  let env := source c
  (suggestStore? 6400 env c.profile (subjects c) (selection c)).any fun w =>
    acceptsCertifiedStoreSource.{0} 6400 env c.profile (subjects c) (selection c) w

#guard cases.all accepted
#guard cases.all storeAccepted

/-- A forged legacy equivalence, type cache, block verdict and inference-only
flag are carried through the actual TcM state. Certified checking is full and
independent of each of these fields. -/
def poisonedChecker (c : Case) : TcState .anon :=
  let state := TcState.ofEnvAnon {}
  let lhs : KExpr .anon := KExpr.mkNatLit 0
  let rhs : KExpr .anon := KExpr.mkConst ⟨c.profile.falseType, ()⟩ #[]
  { state with
    inferOnly := true, eagerReduce := true, recFuel := 0, noAccel := false,
    equivManager := state.equivManager.addEquiv ⟨lhs.addr, state.ctxId, 0, 0⟩ ⟨rhs.addr, state.ctxId, 0, 0⟩,
    env := { state.env with
      inferCache := state.env.inferCache.insert (lhs.addr, state.ctxId) rhs,
      inferOnlyCache := state.env.inferOnlyCache.insert (lhs.addr, state.ctxId) rhs,
      whnfCache := state.env.whnfCache.insert (lhs.addr, state.ctxId) rhs,
      defEqCache := state.env.defEqCache.insert (lhs.addr, rhs.addr, state.ctxId) true,
      blockCheckResults := state.env.blockCheckResults.insert ⟨c.target, ()⟩ (.ok ()) } }

def warmAndRollback (c : Case) : Bool := Id.run do
  let env := source c
  let count := c.blobs.length + c.literals.length
  let some w := suggestSource? 6400 env c.profile c.target (selection c) | return false
  let .ok _ cold := (certifiedStep.{0} 6400 env c.profile c.target (selection c) w).run initialCertifiedState | return false
  if cold.inputCache.misses != count || cold.inputCache.hits != 0 then return false
  let start := { cold with checker := poisonedChecker c }
  let .ok _ warm := (certifiedStep.{0} 6400 env c.profile c.target (selection c) w).run start | return false
  if warm.inputCache.hits != count || warm.inputCache.misses != count then return false
  if !warm.checker.inferOnly || warm.checker.recFuel != 0 then return false
  let bad := { w with proofWitness := .sort }
  let .error _ failed := (certifiedStep.{0} 6400 env c.profile c.target (selection c) bad).run warm | return false
  if failed.inputCache.hits != warm.inputCache.hits || failed.inputCache.misses != warm.inputCache.misses then return false
  let .error _ exhausted := (certifiedStep.{0} 0 env c.profile c.target (selection c) w).run failed | return false
  if exhausted.inputCache.hits != warm.inputCache.hits || exhausted.inputCache.misses != warm.inputCache.misses then return false
  let .ok _ retry := (certifiedStep.{0} 6400 env c.profile c.target (selection c) w).run exhausted | return false
  return retry.inputCache.hits == 2 * count && retry.inputCache.misses == count

#guard cases.all warmAndRollback

def loadedIxe? (c : Case) : Option (ByteArray × Ixon.Env) := do
  let bytes ← (Ixon.serEnv (source c)).toOption
  let parts ← (Ixon.deEnvVerifiedLazy bytes).toOption
  return (bytes, parts.env)

def ixeAccepted (c : Case) : Bool := Id.run do
  let some (_, env) := loadedIxe? c | return false
  let some target := env.consts.get? c.target | return false
  if target.cache.isSome || target.buf.size ≤ target.len then return false
  let some w := suggestSource? 6400 env c.profile c.target (selection c) | return false
  return acceptsCertifiedSource.{0} 6400 env c.profile c.target (selection c) w

#guard cases.all ixeAccepted

def extraMalformed : Address := Address.blake3 "C5-unvisited-malformed-constant".toUTF8

def lazyOnlySelected (c : Case) : Bool := Id.run do
  let raw := source c
  let env := { raw with
    consts := raw.consts.insert extraMalformed
      (Ixon.LazyConstant.ofSlice (ByteArray.mk #[255, 254]) 0 2) }
  let some w := suggestSource? 6400 env c.profile c.target (selection c) | return false
  return env.consts.size > c.blobs.length &&
    acceptsCertifiedSource.{0} 6400 env c.profile c.target (selection c) w &&
    !acceptsCertifiedSource.{0} 6400 env c.profile c.target
      ⟨extraMalformed :: (selection c).objects, (selection c).naturals⟩ w

#guard cases.all lazyOnlySelected

def materializedCacheIgnored (c : Case) : Bool := Id.run do
  let raw := source c
  let some entry := raw.consts.get? c.target | return false
  let bogus : Ixon.Constant := ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.zero]⟩
  let env := { raw with consts := raw.consts.insert c.target { entry with cache := some bogus } }
  let some w := suggestSource? 6400 env c.profile c.target (selection c) | return false
  return acceptsCertifiedSource.{0} 6400 env c.profile c.target (selection c) w

#guard cases.all materializedCacheIgnored

/-- Warm byte caches must not hide changed source bytes, windows, pins,
missing dependencies, or a modified selection. -/
def hostileSource (c : Case) : Bool := Id.run do
  let env := source c
  let some w := suggestSource? 6400 env c.profile c.target (selection c) | return false
  let .ok _ warm := (certifiedStep.{0} 6400 env c.profile c.target (selection c) w).run initialCertifiedState | return false
  let some entry := env.consts.get? c.target | return false
  let changed := { env with
    consts := env.consts.insert c.target
      (Ixon.LazyConstant.ofSlice (entry.rawBytes.push 0) 0 (entry.rawBytes.size + 1)) }
  let .error _ _ := (certifiedStep.{0} 6400 changed c.profile c.target (selection c) w).run warm | return false
  let outside := { env with consts := env.consts.insert c.target { entry with off := entry.buf.size + 1 } }
  let .error _ _ := (certifiedStep.{0} 6400 outside c.profile c.target (selection c) w).run warm | return false
  let truncated := { env with consts := env.consts.insert c.target { entry with len := entry.buf.size + 1 } }
  let .error _ _ := (certifiedStep.{0} 6400 truncated c.profile c.target (selection c) w).run warm | return false
  let missing := { (selection c) with objects := (selection c).objects.filter (· != c.target) }
  let .error _ _ := (certifiedStep.{0} 6400 env c.profile c.target missing w).run warm | return false
  let duplicate := { (selection c) with objects := c.target :: (selection c).objects }
  let .error _ _ := (certifiedStep.{0} 6400 env c.profile c.target duplicate w).run warm | return false
  let badProfile := { c.profile with falseType := c.profile.falseElim, falseElim := c.profile.falseType }
  let .error _ _ := (certifiedStep.{0} 6400 env badProfile c.target (selection c) w).run warm | return false
  let reordered := { (selection c) with objects := (selection c).objects.reverse, naturals := (selection c).naturals.reverse }
  let .ok _ _ := (certifiedStep.{0} 6400 env c.profile c.target reordered w).run warm | return false
  return true

#guard cases.all hostileSource

def rejectsMutation (m : Features.Mutation) : Bool := Id.run do
  let some c := make? m.name m.signature m.altered | return false
  let some p := repaired? c m.original | return false
  let some w := Ix.Theory.Certificate.proofWitness? 6400 p.signature p.input | return false
  return acceptsCertified.{0,0} 6400 p.signature p.input w &&
    !acceptsCertifiedSource.{0} 6400 (source c) c.profile c.target (selection c) w

#guard Features.mutatedSources.all rejectsMutation


def rejectsStoreMutation (m : Features.Mutation) : Bool := Id.run do
  let some c := make? m.name m.signature m.altered | return false
  let some p := repaired? c m.original | return false
  let some w := Ix.Theory.Certificate.proofWitness? 6400 p.signature p.input | return false
  return acceptsStoreCertified.{0,0} 6400 p.signature p.input.store [.member c.target 0] w.declarations &&
    !acceptsCertifiedStoreSource.{0} 6400 (source c) c.profile [c.target] (selection c) w.declarations

#guard Features.mutatedSources.all rejectsStoreMutation

def rejectsIngressMutation (m : Features.IngressMutation) : Bool :=
  m.altered.any fun c =>
    match readSnapshot? 6400 (source c) (selection c) {} with
    | none => true
    | some (snapshot, _) => (snapshot.prepare? 6400 c.profile c.target).isNone

#guard Features.ingressMutations.all rejectsIngressMutation

def naturalState : Bool := Id.run do
  let some c := Features.naturalCase | return false
  let env := source c
  let some w := suggestSource? 6400 env c.profile c.target (selection c) | return false
  let .ok _ warm := (certifiedStep.{0} 6400 env c.profile c.target (selection c) w).run initialCertifiedState | return false
  for alter in [Features.missingPin, Features.wrongPin] do
    let other := alter c
    let .error _ _ := (certifiedStep.{0} 6400 env other.profile c.target (selection c) w).run warm | return false
  let some (literal, bytes) := c.literals.head? | return false
  let changed := { env with blobs := env.blobs.insert literal (bytes.push 1) }
  let .error _ _ := (certifiedStep.{0} 6400 changed c.profile c.target (selection c) w).run warm | return false
  let missing := { env with blobs := env.blobs.erase literal }
  let .error _ _ := (certifiedStep.{0} 6400 missing c.profile c.target (selection c) w).run warm | return false
  let some recursor := reference c.references (.member 201 0) | return false
  let thin := { (selection c) with objects := (selection c).objects.filter (· != recursor) }
  let assumed := { env with assumptions := env.assumptions.insert recursor }
  let .error _ _ := (certifiedStep.{0} 6400 assumed c.profile c.target thin w).run warm | return false
  let reversed := { w with declarations := w.declarations.reverse }
  let .error _ _ := (certifiedStep.{0} 6400 env c.profile c.target (selection c) reversed).run warm | return false
  return true

#guard naturalState

def storeRollback (c : Case) : Bool := Id.run do
  let env := source c
  let some w := suggestStore? 6400 env c.profile (subjects c) (selection c) | return false
  let .ok _ cold := (certifiedStoreStep.{0} 6400 env c.profile (subjects c) (selection c) w).run initialCertifiedState | return false
  let start := { cold with checker := poisonedChecker c }
  let .ok _ warm := (certifiedStoreStep.{0} 6400 env c.profile (subjects c) (selection c) w).run start | return false
  let .error _ failed := (certifiedStoreStep.{0} 6400 env c.profile (subjects c) (selection c) []).run warm | return false
  if failed.inputCache.hits != warm.inputCache.hits || failed.inputCache.misses != warm.inputCache.misses then return false
  let .ok _ retry := (certifiedStoreStep.{0} 6400 env c.profile (subjects c) (selection c) w).run failed | return false
  return retry.inputCache.misses == cold.inputCache.misses

#guard cases.all storeRollback

def emptyBlockRejected : Bool := Id.run do
  let empty := Fixtures.encode ⟨.muts #[], #[], #[], #[]⟩
  let c : Case := {
    name := "empty-source-block", profile := Fixtures.profile, target := empty.1,
    blobs := Fixtures.prelude ++ [empty], literals := [], references := [], blocks := [] }
  return !acceptsCertifiedStoreSource.{0} 6400 (source c) c.profile [empty.1] (selection c) []

#guard emptyBlockRejected

def writeCase (directory : System.FilePath) (c : Case) : IO Unit := do
  let some (bytes, _) := loadedIxe? c | throw (IO.userError s!"cannot serialize source case: {c.name}")
  let directory := directory / c.name
  IO.FS.createDirAll directory
  IO.FS.writeBinFile (directory / "source.ixe") bytes
  let request := Lean.Json.mkObj [
    ("target", toJson (hexOfBytes c.target.hash)),
    ("subjects", toJson ((subjects c).map fun a => hexOfBytes a.hash)),
    ("falseType", toJson (hexOfBytes c.profile.falseType.hash)),
    ("falseElim", toJson (hexOfBytes c.profile.falseElim.hash)),
    ("natType", toJson (c.profile.natType.map fun a => hexOfBytes a.hash)),
    ("objects", toJson ((selection c).objects.map fun a => hexOfBytes a.hash)),
    ("naturals", toJson ((selection c).naturals.map fun a => hexOfBytes a.hash))]
  IO.FS.writeFile (directory / "request.json") (request.pretty ++ "\n")

def run (directory : Option System.FilePath) : IO Unit := do
  for c in cases do
    for (name, test) in [("proof", accepted), ("declarations", storeAccepted),
        ("cache-and-rollback", warmAndRollback), ("ixe", ixeAccepted),
        ("lazy-selection", lazyOnlySelected), ("materialized-cache", materializedCacheIgnored),
        ("hostile-source", hostileSource), ("store-rollback", storeRollback)] do
      unless test c do throw (IO.userError s!"{name} failed: {c.name}")
    if let some directory := directory then writeCase directory c
  for m in Features.mutatedSources do
    unless rejectsMutation m && rejectsStoreMutation m do
      throw (IO.userError s!"source mutation escaped a TcM gate: {m.name}")
  for m in Features.ingressMutations do
    unless rejectsIngressMutation m do throw (IO.userError s!"ingress mutation escaped: {m.name}")
  unless naturalState && emptyBlockRejected do throw (IO.userError "profile/dependency or empty-block rejection failed")
  IO.println <| (Lean.Json.mkObj [
    ("proofAccepted", toJson cases.length), ("storesAccepted", toJson cases.length),
    ("ixeAccepted", toJson cases.length), ("warmProofScenarios", toJson cases.length),
    ("warmStoreScenarios", toJson cases.length), ("lazySelectionScenarios", toJson cases.length),
    ("materializedCacheScenarios", toJson cases.length), ("hostileSourceScenarios", toJson cases.length),
    ("proofSourceMutationsRejected", toJson Features.mutatedSources.length),
    ("storeSourceMutationsRejected", toJson Features.mutatedSources.length),
    ("ingressMutationsRejected", toJson Features.ingressMutations.length),
    ("naturalStateScenario", toJson true), ("emptyBlockRejected", toJson true),
    ("unexpectedErrors", toJson (0 : Nat))]).compress

end Tests.Certified.Source
