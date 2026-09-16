module

public import Ix.Resource.Addressed

public section

namespace Tests.ResourceAddressed

open Ixon Ix.Resource

abbrev E := Ixon.Expr

def store (env : Ixon.Env) (c : Constant) : Ixon.Env × Address :=
  let address := Addressed.commit c
  (env.storeConst address c, address)

def unitBlock : Constant := {
  info := .muts #[.indc ⟨false, 0, 0, 0, .sort 0,
    #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩]⟩]
  sharing := #[], refs := #[], univs := #[.zero] }

def unitEnv : Ixon.Env × Address := Id.run do
  let (env, block) := store {} unitBlock
  let (env, type) := store env (Addressed.wrapper (.iPrj ⟨0, block⟩))
  let (env, _) := store env (Addressed.constructorWrapper block 0 0)
  return (env, type)

def linearLocal : Ixon.BinderContract := ⟨.linear, .localShared⟩

def identity (unit : Address) (input : Ixon.BinderContract := linearLocal)
    (result : ValueContract := .localShared) : Constant := {
  info := .defn ⟨.defn, .safe, 0,
    .all input result (.ref 0 #[]) (.ref 0 #[]),
    .lam input (.ref 0 #[]) (.share 0)⟩
  sharing := #[.var 0], refs := #[unit], univs := #[] }

def fixtures : Array (String × Constant) := Id.run do
  let (_, unit) := unitEnv
  return #[ ("unit", unitBlock), ("identity", identity unit),
    ("identity_unique", identity unit ⟨.linear, .unique⟩ .unique) ]

def check (label : String) (result : Except String α) (accept : Bool) : IO Unit := do
  unless result.toOption.isSome == accept do
    let diagnostic := match result with | .error e => e | .ok _ => "accepted"
    throw <| IO.userError s!"addressed resource {label}: expected {accept}, got {diagnostic}"

def get (label : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error e => throw <| IO.userError s!"addressed resource {label}: {e}"

def run : IO Unit := do
  let (base, unit) := unitEnv
  let profile : Profile := { natType := some unit, shareableTypes := #[unit] }
  let fixture ← IO.FS.readFile "Tests/Fixtures/ixon-v3/addressed.tsv"
  let lines := fixture.splitOn "\n"
  for (label, constant) in fixtures do
    let line := s!"{label}\t{Addressed.commit constant}\t{hexOfBytes (serConstant constant)}"
    unless lines.contains line do throw <| IO.userError s!"addressed fixture differs: {label}"
  let profileAddress ← get "profile address" profile.address
  unless lines.contains s!"profile\t{profileAddress}\t{hexOfBytes profile.bytes}" do
    throw <| IO.userError "addressed profile fixture differs"
  let decoded ← get "profile roundtrip" (Profile.ofBytes profile.bytes)
  unless decoded.bytes == profile.bytes do throw <| IO.userError "profile roundtrip differs"
  for length in [:profile.bytes.size] do
    check "truncated profile" (Profile.ofBytes (profile.bytes.extract 0 length)) false
  check "profile trailing bytes" (Profile.ofBytes (profile.bytes.push 0)) false
  check "wrong validator" (Profile.ofBytes (profile.bytes.set! 0 0)) false
  let (env, id) := store base (identity unit)
  let prepared ← get "valid identity" (Addressed.checkResources env profile)
  unless prepared.program.declarations.size == 3 && prepared.program.groups.size == 1 do
    throw <| IO.userError "addressed resource: nominal block flattening"
  check "unrestricted result cannot hide local input"
    (Addressed.checkResources (store base (identity unit linearLocal .shared)).1 profile) false
  check "profile bytes canonical" ({ profile with shareableTypes := #[unit, unit] }.address) false
  check "selection assumption required" ({ profile with choices := #[id] }.address) false
  check "literal nominal kind" (Addressed.prepare env { profile with natType := some id }) false
  check "missing typed dependency" (Addressed.prepare (store {} (identity unit)).1 profile) false
  let bogus := Address.blake3 ⟨#[9]⟩
  check "raw hash mismatch" (Addressed.prepare (env.storeConst bogus (identity unit)) profile) false
  let raw := (serConstant (identity unit)).push 0
  let trailing : Ixon.Env := { base with
    consts := base.consts.insert (Address.blake3 raw) (LazyConstant.ofSlice raw 0 raw.size) }
  check "whole-object trailing bytes" (Addressed.prepare trailing profile) false
  let honest := LazyConstant.ofConstant (identity unit)
  let forged := { honest with cache := some unitBlock }
  let resolved ← get "ignore forged materialized cache"
    (Addressed.prepare { env with consts := env.consts.insert id forged } profile)
  unless resolved.addresses == prepared.addresses do
    throw <| IO.userError "addressed adapter trusted a materialized cache"
  let orphan := Addressed.wrapper (.iPrj ⟨99, Addressed.commit unitBlock⟩)
  check "out-of-range projection" (Addressed.prepare (store env orphan).1 profile) false
  let cprj := Addressed.commit (Addressed.constructorWrapper (Addressed.commit unitBlock) 0 0)
  check "missing constructor wrapper"
    (Addressed.prepare { env with consts := env.consts.erase cprj } profile) false
  let wrongWrapper := { Addressed.wrapper (.iPrj ⟨0, Addressed.commit unitBlock⟩) with univs := #[.zero] }
  check "nonempty projection tables" (Addressed.prepare (store env wrongWrapper).1 profile) false
  let extern : Constant := {
    info := .axio ⟨false, 0, .all linearLocal .shared (.ref 0 #[]) (.ref 0 #[])⟩
    sharing := #[], refs := #[unit], univs := #[] }
  let (externalEnv, external) := store base extern
  check "unadmitted external interface" (Addressed.checkResources externalEnv profile) false
  check "explicit external assumption"
    (Addressed.checkResources externalEnv { profile with assumptions := #[external] }) true
  let mut blobEnv := base
  let mut literalDecls := #[]
  for byte in #[0, 1] do
    let (next, blob) := blobEnv.storeBlob ⟨#[byte]⟩
    let c : Constant := {
      info := .defn ⟨.defn, .safe, 0, .ref 0 #[], .nat 1⟩
      sharing := #[], refs := #[unit, blob], univs := #[] }
    let (next, address) := store next c
    blobEnv := next
    literalDecls := literalDecls.push address
  let resolved ← get "literal identities" (Addressed.prepare blobEnv profile)
  let literalBodies := resolved.program.declarations.filterMap (·.body)
  unless literalBodies.size == 2 && literalBodies[0]! != literalBodies[1]! do
    throw <| IO.userError "literal identities collided across local reference tables"
  let badBlob := { blobEnv with blobs := blobEnv.blobs.insert bogus ⟨#[0]⟩ }
  check "blob integrity" (Addressed.prepare badBlob profile) false
  let recursiveType := Ixon.Expr.all ⟨.linear, .unique⟩ .unique (.ref 0 #[]) (.ref 0 #[])
  let recursive : Constant := {
    info := .muts #[
      .defn ⟨.defn, .safe, 0, recursiveType,
        .lam ⟨.linear, .unique⟩ (.ref 0 #[]) (.app (.recur 1 #[]) (.var 0))⟩,
      .defn ⟨.defn, .safe, 0, recursiveType,
        .lam ⟨.linear, .unique⟩ (.ref 0 #[]) (.app (.recur 0 #[]) (.var 0))⟩]
    sharing := #[], refs := #[unit], univs := #[] }
  let (recEnv, block) := store base recursive
  let (recEnv, _) := store recEnv (Addressed.wrapper (.dPrj ⟨0, block⟩))
  let (recEnv, _) := store recEnv (Addressed.wrapper (.dPrj ⟨1, block⟩))
  check "mutual recursive interface checking" (Addressed.checkResources recEnv profile) true
  let recursor : Constant := {
    info := .recr ⟨false, false, 0, 0, 0, 0, 0, .ref 0 #[],
      #[⟨0, .lam linearLocal (.ref 0 #[]) (.var 0)⟩]⟩
    sharing := #[], refs := #[unit], univs := #[] }
  let (recEnv, recAddr) := store base recursor
  check "annotated recursor rules are relevant" (Addressed.checkResources recEnv profile) false
  check "profile-bound recursor" (Addressed.checkResources recEnv { profile with assumptions := #[recAddr] }) true
  -- These are adapter/resource tests; the synthetic recursor and literal
  -- type profile are intentionally not claims of ordinary kernel typing.
  let fieldType := Ixon.Expr.all ⟨.many, .unique⟩ .unique (.ref 0 #[]) (.recur 0 #[])
  let aggregate : Constant := {
    info := .muts #[.indc ⟨false, 0, 0, 0, .sort 0,
      #[⟨false, 0, 0, 0, 1, fieldType⟩]⟩]
    sharing := #[], refs := #[unit], univs := #[.zero] }
  let (fieldEnv, block) := store base aggregate
  let (fieldEnv, nominal) := store fieldEnv (Addressed.wrapper (.iPrj ⟨0, block⟩))
  let (fieldEnv, _) := store fieldEnv (Addressed.constructorWrapper block 0 0)
  let resolved ← get "derived fields" (Addressed.checkResources fieldEnv profile)
  unless resolved.program.fields.size == 1 &&
      resolved.addresses[resolved.program.fields[0]!.typeRef.toNat]? == some nominal &&
      resolved.program.fields[0]!.contract == .unique do
    throw <| IO.userError "field rule did not come from the addressed constructor"
  IO.println "Addressed resources: integrity, profile codecs, fixtures, fields, and dependency checks passed"

end Tests.ResourceAddressed

end
