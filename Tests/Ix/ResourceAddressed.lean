module

public import Ix.Resource.Addressed

public section

namespace Tests.ResourceAddressed

open Ixon Ix.Resource

abbrev E := Ixon.Expr

def store (env : Ixon.Env) (c : Constant) : Ixon.Env × Address :=
  let address := Addressed.commit c
  (env.storeConst address c, address)

/-- The unit fixture in a chosen sort. `Sort 0` makes it a proposition, whose
values are erased when passed as call arguments. -/
def unitBlockIn (sort : Ixon.Univ) : Constant := {
  info := .muts #[.indc ⟨false, 0, 0, 0, .sort 0,
    #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩]⟩]
  sharing := #[], refs := #[], univs := #[sort] }

def unitBlock : Constant := unitBlockIn .zero

def unitEnvIn (sort : Ixon.Univ) : Ixon.Env × Address := Id.run do
  let (env, block) := store {} (unitBlockIn sort)
  let (env, type) := store env (Addressed.wrapper (.iPrj ⟨0, block⟩))
  let (env, _) := store env (Addressed.constructorWrapper block 0 0)
  return (env, type)

def unitEnv : Ixon.Env × Address := unitEnvIn .zero

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

/-- The profile the shared fixture pins. -/
def fixtureProfile : Profile :=
  let (_, unit) := unitEnv
  { natType := some unit, shareableTypes := #[unit] }

/-- The extended profile the shared fixture pins (`profile-cases`): case
behavior and one admitted interface. -/
def casesProfile : Profile :=
  let (_, unit) := unitEnv
  { fixtureProfile with
    assumptions := #[unit], cases := true
    interfaces := #[(unit, ⟨#[packAllContract ⟨.linear, .localShared⟩ .shared]⟩)] }

/-- The profile with unfolding equations the shared fixture pins
(`profile-equations`): the equality type and one `(definition, theorem)` pair. -/
def equationsProfile : Profile :=
  let (_, unit) := unitEnv
  { fixtureProfile with eqType := some unit, equations := #[(unit, unit)] }

/-- The profile with case definitions the shared fixture pins
(`profile-case-definitions`): case behavior and one bound case definition. -/
def caseDefinitionsProfile : Profile :=
  let (_, unit) := unitEnv
  { fixtureProfile with cases := true, caseDefinitions := #[unit] }

/-- The profile with plain-data crossing the shared fixture pins
(`profile-plain-crossing`): crossing and one opted-out (`linear`) type. -/
def plainCrossingProfile : Profile :=
  let (_, unit) := unitEnv
  { fixtureProfile with crossing := true, linearTypes := #[unit] }

/-- One `addressed.tsv` row: a constant's address and canonical bytes. -/
def fixtureLine (label : String) (constant : Constant) : String :=
  s!"{label}\t{Addressed.commit constant}\t{hexOfBytes (serConstant constant)}"

/-- The shared `addressed.tsv` fixture, also read by the Rust resource
validator. `lake exe ixon-v4-tests --export-fixtures` writes it. -/
def fixtureText : Except String String := do
  let profileAddress ← fixtureProfile.address
  let rows := fixtures.map fun (label, constant) => fixtureLine label constant
  let rows := rows.push s!"profile\t{profileAddress}\t{hexOfBytes fixtureProfile.bytes}"
  let casesAddress ← casesProfile.address
  let rows := rows.push s!"profile-cases\t{casesAddress}\t{hexOfBytes casesProfile.bytes}"
  let equationsAddress ← equationsProfile.address
  let rows := rows.push s!"profile-equations\t{equationsAddress}\t{hexOfBytes equationsProfile.bytes}"
  let caseAddress ← caseDefinitionsProfile.address
  let rows := rows.push s!"profile-case-definitions\t{caseAddress}\t{hexOfBytes caseDefinitionsProfile.bytes}"
  let plainAddress ← plainCrossingProfile.address
  let rows := rows.push s!"profile-plain-crossing\t{plainAddress}\t{hexOfBytes plainCrossingProfile.bytes}"
  return rows.foldl (fun text row => text ++ row ++ "\n") "# name\taddress\tcanonical bytes\n"

def run : IO Unit := do
  let (base, unit) := unitEnv
  let profile := fixtureProfile
  let fixture ← IO.FS.readFile "Tests/Fixtures/ixon-v4/addressed.tsv"
  let lines := fixture.splitOn "\n"
  for (label, constant) in fixtures do
    unless lines.contains (fixtureLine label constant) do
      throw <| IO.userError s!"addressed fixture differs: {label}"
  let profileAddress ← get "profile address" profile.address
  unless lines.contains s!"profile\t{profileAddress}\t{hexOfBytes profile.bytes}" do
    throw <| IO.userError "addressed profile fixture differs"
  unless fixture == (← get "fixture text" fixtureText) do
    throw <| IO.userError "addressed fixture differs from its producer; regenerate it with \
      `lake exe ixon-v4-tests --export-fixtures`"
  let decoded ← get "profile roundtrip" (Profile.ofBytes profile.bytes)
  unless decoded.bytes == profile.bytes do throw <| IO.userError "profile roundtrip differs"
  for length in [:profile.bytes.size] do
    check "truncated profile" (Profile.ofBytes (profile.bytes.extract 0 length)) false
  check "profile trailing bytes" (Profile.ofBytes (profile.bytes.push 0)) false
  check "wrong validator" (Profile.ofBytes (profile.bytes.set! 0 0)) false
  -- The optional extension: case behavior and admitted interfaces.
  let extended : Profile := casesProfile
  let extendedAddress ← get "extended profile address" extended.address
  let extendedLine := s!"profile-cases\t{extendedAddress}\t{hexOfBytes extended.bytes}"
  unless lines.contains extendedLine do
    throw <| IO.userError s!"addressed extended profile fixture differs; expected line:\n{extendedLine}"
  let decoded ← get "extended profile roundtrip" (Profile.ofBytes extended.bytes)
  unless decoded.bytes == extended.bytes && decoded.cases && decoded.interfaces.size == 1 do
    throw <| IO.userError "extended profile roundtrip differs"
  let unextended : Profile := { extended with cases := false, interfaces := #[] }
  for length in [unextended.bytes.size + 1:extended.bytes.size] do
    check "truncated profile extension" (Profile.ofBytes (extended.bytes.extract 0 length)) false
  check "empty profile extension" (Profile.ofBytes (profile.bytes ++ ⟨#[0, 0]⟩)) false
  check "unknown profile behavior" (Profile.ofBytes (profile.bytes ++ ⟨#[2, 0]⟩)) false
  check "admitted interface must be assumed" ({ extended with assumptions := #[] }.address) false
  check "invalid interface contract" ({ extended with interfaces := #[(unit, ⟨#[64]⟩)] }.address) false
  -- Unfolding equations and the equality type travel in the same extension.
  let withEquations : Profile := equationsProfile
  let equationsAddress ← get "equations profile address" withEquations.address
  let equationsLine := s!"profile-equations\t{equationsAddress}\t{hexOfBytes withEquations.bytes}"
  unless lines.contains equationsLine do
    throw <| IO.userError s!"addressed equations profile fixture differs; expected line:\n{equationsLine}"
  let decoded ← get "equations profile roundtrip" (Profile.ofBytes withEquations.bytes)
  unless decoded.bytes == withEquations.bytes && decoded.equations.size == 1 do
    throw <| IO.userError "equations profile roundtrip differs"
  check "equations need the equality type" ({ withEquations with eqType := none }.address) false
  check "the equality type needs equations" ({ profile with eqType := some unit }.address) false
  check "empty equation list" (Profile.ofBytes (profile.bytes ++ ⟨#[2, 0]⟩ ++ unit.hash ++ ⟨#[0]⟩)) false
  -- Case definitions travel in the same extension, after the equations.
  let withCases : Profile := caseDefinitionsProfile
  let caseAddress ← get "case definitions profile address" withCases.address
  let caseLine := s!"profile-case-definitions\t{caseAddress}\t{hexOfBytes withCases.bytes}"
  unless lines.contains caseLine do
    throw <| IO.userError s!"addressed case definitions profile fixture differs; expected line:\n{caseLine}"
  let decoded ← get "case definitions profile roundtrip" (Profile.ofBytes withCases.bytes)
  unless decoded.bytes == withCases.bytes && decoded.caseDefinitions == #[unit] do
    throw <| IO.userError "case definitions profile roundtrip differs"
  check "case definitions need case behavior" ({ withCases with cases := false }.address) false
  check "case definitions are strictly increasing"
    ({ withCases with caseDefinitions := #[unit, unit] }.address) false
  check "empty case definition list" (Profile.ofBytes (profile.bytes ++ ⟨#[5, 0, 0]⟩)) false
  check "unknown profile behavior bit" (Profile.ofBytes (profile.bytes ++ ⟨#[32, 0]⟩)) false
  -- Plain-data crossing (bit 3, no data) and opted-out types (bit 4, a list).
  let withPlain : Profile := plainCrossingProfile
  let plainAddress ← get "plain crossing profile address" withPlain.address
  let plainLine := s!"profile-plain-crossing\t{plainAddress}\t{hexOfBytes withPlain.bytes}"
  unless lines.contains plainLine do
    throw <| IO.userError s!"addressed plain crossing profile fixture differs; expected line:\n{plainLine}"
  let decodedPlain ← get "plain crossing profile roundtrip" (Profile.ofBytes withPlain.bytes)
  unless decodedPlain.bytes == withPlain.bytes && decodedPlain.crossing &&
      decodedPlain.linearTypes == #[unit] do
    throw <| IO.userError "plain crossing profile roundtrip differs"
  let crossingOnly ← get "crossing bit alone" (Profile.ofBytes (profile.bytes ++ ⟨#[8, 0]⟩))
  unless crossingOnly.crossing && crossingOnly.linearTypes.isEmpty do
    throw <| IO.userError "the crossing bit alone does not decode"
  check "linear types are strictly increasing"
    ({ withPlain with linearTypes := #[unit, unit] }.address) false
  check "empty linear type list" (Profile.ofBytes (profile.bytes ++ ⟨#[16, 0, 0]⟩)) false
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
  -- Linear unique resources must live in a type, not a proposition.
  let (typeBase, typeUnit) := unitEnvIn (.succ .zero)
  let typeProfile : Profile := { natType := some typeUnit, shareableTypes := #[typeUnit] }
  let recursiveType := Ixon.Expr.all ⟨.linear, .unique⟩ .unique (.ref 0 #[]) (.ref 0 #[])
  let recursive : Constant := {
    info := .muts #[
      .defn ⟨.defn, .safe, 0, recursiveType,
        .lam ⟨.linear, .unique⟩ (.ref 0 #[]) (.app (.recur 1 #[]) (.var 0))⟩,
      .defn ⟨.defn, .safe, 0, recursiveType,
        .lam ⟨.linear, .unique⟩ (.ref 0 #[]) (.app (.recur 0 #[]) (.var 0))⟩]
    sharing := #[], refs := #[typeUnit], univs := #[] }
  let (recEnv, block) := store typeBase recursive
  let (recEnv, _) := store recEnv (Addressed.wrapper (.dPrj ⟨0, block⟩))
  let (recEnv, _) := store recEnv (Addressed.wrapper (.dPrj ⟨1, block⟩))
  check "mutual recursive interface checking" (Addressed.checkResources recEnv typeProfile) true
  -- The same recursion over a proposition passes erased proofs: the linear
  -- binder is never consumed.
  let (propEnv, propBlock) := store base { recursive with refs := #[unit] }
  let (propEnv, _) := store propEnv (Addressed.wrapper (.dPrj ⟨0, propBlock⟩))
  let (propEnv, _) := store propEnv (Addressed.wrapper (.dPrj ⟨1, propBlock⟩))
  check "proof arguments have no demand" (Addressed.checkResources propEnv profile) false
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
  -- A parameterised structure `Duo α β` (fields `fst : α`, `snd : β`): its
  -- field rules stay open over the parameters and the earlier fields, and a
  -- projection takes its type from the projected value's type arguments.
  let duoCtor : E := .all .many .shared (.sort 0) (.all .many .shared (.sort 0)
    (.all .many .shared (.var 1) (.all .many .shared (.var 1)
      (.app (.app (.recur 0 #[]) (.var 3)) (.var 2)))))
  let duo : Constant := {
    info := .muts #[.indc ⟨false, 0, 2, 0,
      .all .many .shared (.sort 0) (.all .many .shared (.sort 0) (.sort 0)),
      #[⟨false, 0, 0, 2, 2, duoCtor⟩]⟩]
    sharing := #[], refs := #[], univs := #[.succ .zero] }
  let (duoEnv, duoBlock) := store base duo
  let (duoEnv, duoType) := store duoEnv (Addressed.wrapper (.iPrj ⟨0, duoBlock⟩))
  let (duoEnv, _) := store duoEnv (Addressed.constructorWrapper duoBlock 0 0)
  let inner : E := .app (.app (.ref 0 #[]) (.ref 1 #[])) (.ref 1 #[])
  let outer : E := .app (.app (.ref 0 #[]) (.ref 1 #[])) inner
  let second (result : E) : Constant := {
    info := .defn ⟨.defn, .safe, 0, .all ⟨.linear, .shared⟩ .shared outer result,
      .lam ⟨.linear, .shared⟩ outer (.prj 0 1 (.var 0))⟩
    sharing := #[], refs := #[duoType, unit], univs := #[] }
  let resolved ← get "parameterised fields" (Addressed.checkResources (store duoEnv (second inner)).1 profile)
  let duoFields := resolved.program.fields.filter fun f =>
    resolved.addresses[f.typeRef.toNat]? == some duoType
  unless duoFields.map (·.binders) == #[2, 3] && duoFields.map (·.type) == #[.var 1, .var 1] do
    throw <| IO.userError "parameterised field rules are not open over their telescope"
  check "an instantiated field type is still checked"
    (Addressed.checkResources (store duoEnv (second (.ref 1 #[]))).1 profile) false
  -- Case-split shapes come from addressed recursors, under a `cases` profile:
  -- `B` with `e : B` and `f : unit → B`, and `B.rec` in the same block.
  let caseType : E := .all .many .shared (.all .many .shared (.recur 0 #[]) (.sort 0))
    (.all .many .shared (.app (.var 0) (.var 0))
      (.all .many .shared (.all .many .shared (.ref 0 #[]) (.app (.var 2) (.var 0)))
        (.all .many .shared (.recur 0 #[]) (.app (.var 3) (.var 0)))))
  let caseBlock : Constant := {
    info := .muts #[
      .indc ⟨false, 0, 0, 0, .sort 0, #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩,
        ⟨false, 0, 1, 0, 1, .all .many .shared (.ref 0 #[]) (.recur 0 #[])⟩]⟩,
      .recr ⟨false, false, 0, 0, 0, 1, 2, caseType,
        #[⟨0, .lam .many (.sort 0) (.var 0)⟩, ⟨1, .lam .many (.sort 0) (.var 0)⟩]⟩]
    sharing := #[], refs := #[unit], univs := #[.succ .zero] }
  let (caseEnv, caseAddress) := store base caseBlock
  let (caseEnv, _) := store caseEnv (Addressed.wrapper (.iPrj ⟨0, caseAddress⟩))
  let (caseEnv, _) := store caseEnv (Addressed.constructorWrapper caseAddress 0 0)
  let (caseEnv, fieldCtor) := store caseEnv (Addressed.constructorWrapper caseAddress 0 1)
  let (caseEnv, recAddress) := store caseEnv (Addressed.wrapper (.rPrj ⟨1, caseAddress⟩))
  let resolved ← get "case recursors" (Addressed.prepare caseEnv { profile with cases := true })
  let shapes := resolved.program.recursors.map fun r =>
    (resolved.addresses[r.index.toNat]? == some recAddress, r.params, r.motives, r.minors, r.indices,
      r.fields, r.binders)
  unless shapes == #[(true, 0, 1, 2, 0, #[0, 1], #[0, 1])] && resolved.program.cases do
    throw <| IO.userError "addressed recursor did not give its case-split shape"
  let overridden ← get "case constructor overlay" (Addressed.prepare caseEnv {
    profile with cases := true, assumptions := #[fieldCtor], interfaces := #[(fieldCtor, ⟨#[packAllContract ⟨.many, .unique⟩ .unique]⟩)] })
  unless overridden.program.recursors.isEmpty do
    throw <| IO.userError "constructor overlay retained a plain-data recursor"
  let raw : Program := {
    declarations := #[
    { type := .sort 0, kind := .typeConstructor },
    { type := .all .many .shared (.ref 0 #[]) (.ref 0 #[]), kind := .constructor }],
    interfaces := #[(1, .all ⟨.many, .unique⟩ .unique (.ref 0 #[]) (.ref 0 #[]))] }
  let fields ← match Addressed.fields raw {} 0 1 0 1 with
    | .ok fields => pure fields
    | .error e => throw <| IO.userError s!"effective fields: {repr e}"
  unless fields.map (·.contract) == #[.unique] do
    throw <| IO.userError "projection fields ignored the effective constructor interface"
  let ordinary ← get "no case behavior" (Addressed.prepare caseEnv profile)
  unless ordinary.program.recursors.isEmpty && !ordinary.program.cases do
    throw <| IO.userError "case-split shapes without case behavior"
  IO.println "Addressed resources: integrity, profile codecs, fixtures, fields, and dependency checks passed"

end Tests.ResourceAddressed

end
