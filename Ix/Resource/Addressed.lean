module

public import Ix.Resource.Admit

/-!
# Addressed resource interfaces

This boundary reads canonical bytes and ignores presentation metadata. It
resolves each constant's local tables to one program, derives nominal kinds
and supported projection fields, and binds every external rule to an explicit
profile address. Resource admission still requires a separate erased typing
check of these same bytes; `prepare` is deliberately not a certificate.
-/

@[expose] public section

namespace Ix.Resource

open Ixon

def validatorId : String := "ixon-v3/resource-v1"

structure Profile where
  assumptions : Array Address := #[]
  shareableTypes : Array Address := #[]
  choices : Array Address := #[]
  natType : Option Address := none
  stringType : Option Address := none
  limits : Limits := {}
  deriving Inhabited, Repr

def Profile.validate (profile : Profile) : Except String Unit := do
  for addresses in #[profile.assumptions, profile.shareableTypes, profile.choices] do
    let mut previous : Option Address := none
    for address in addresses do
      if address.hash.size != 32 then throw "resource profile: invalid address length"
      if let some before := previous then
        unless Address.cmpBytes before address == .lt do
          throw "resource profile: address lists must be strictly increasing"
      previous := some address
  for address in #[profile.natType, profile.stringType] do
    if let some address := address then
      if address.hash.size != 32 then throw "resource profile: invalid literal type address"
  for choice in profile.choices do
    unless profile.assumptions.contains choice do
      throw "resource profile: selection primitive must be an explicit assumption"
  if profile.limits.depth == 0 || profile.limits.steps == 0 ||
      profile.limits.depth >= UInt64.size || profile.limits.steps >= UInt64.size then
    throw "resource profile: invalid checker limits"

/-- Canonical, domain-separated profile bytes, including the checker limits.
Lists are validated before these bytes are used as a commitment. -/
def Profile.bytes (profile : Profile) : ByteArray :=
  (validatorId ++ "/profile\x00").toUTF8 ++ runPut do
    for addresses in #[profile.assumptions, profile.shareableTypes, profile.choices] do
      putTag0 ⟨addresses.size.toUInt64⟩
      for address in addresses do Serialize.put address
    for address in #[profile.natType, profile.stringType] do
      match address with
      | none => putU8 0
      | some address => putU8 1; Serialize.put address
    putTag0 ⟨profile.limits.depth.toUInt64⟩
    putTag0 ⟨profile.limits.steps.toUInt64⟩

def Profile.address (profile : Profile) : Except String Address := do
  profile.validate
  return Address.blake3 profile.bytes

def Profile.ofBytes (bytes : ByteArray) : Except String Profile := do
  let profile : Profile ← runGetExact (do
    let header := (validatorId ++ "/profile\x00").toUTF8
    unless (← getBytes header.size) == header do throw "resource profile: wrong validator identifier"
    let list : GetM (Array Address) := do
      let count := (← getTag0).size.toNat
      let state ← get
      if count > (state.bytes.size - state.idx) / 32 then throw "resource profile: impossible address count"
      let mut result := #[]
      for _ in [:count] do result := result.push (← Serialize.get)
      return result
    let optional : GetM (Option Address) := do
      match (← getU8) with
      | 0 => pure none
      | 1 => some <$> Serialize.get
      | _ => throw "resource profile: invalid optional address tag"
    let assumptions ← list
    let shareableTypes ← list
    let choices ← list
    let natType ← optional
    let stringType ← optional
    let depth := (← getTag0).size.toNat
    let steps := (← getTag0).size.toNat
    return { assumptions, shareableTypes, choices, natType, stringType, limits := { depth, steps } }) bytes
  profile.validate
  return profile

structure AddressedProgram where
  program : Program
  policy : Policy
  addresses : Array Address
  profileAddress : Address
  deriving Inhabited

namespace Addressed

structure Pending where
  address : Address
  constant : Constant
  members : Array Address
  declaration : Declaration
  auxiliary : Array Ixon.Expr := #[]
  deriving Inhabited

def wrapper (info : Ixon.ConstantInfo) : Constant := ⟨info, #[], #[], #[]⟩

def commit (constant : Constant) : Address := Address.blake3 (serConstant constant)

def memberWrapper (block : Address) (index : UInt64) : MutConst → Constant
  | .defn _ => wrapper (.dPrj ⟨index, block⟩)
  | .indc _ => wrapper (.iPrj ⟨index, block⟩)
  | .recr _ => wrapper (.rPrj ⟨index, block⟩)

def constructorWrapper (block : Address) (index ctor : UInt64) : Constant :=
  wrapper (.cPrj ⟨index, ctor, block⟩)

def definition (d : Definition) : Declaration := {
  type := d.typ, body := some d.value
  kind := if d.safety == .safe then .definition else .assumption }

def recursor (d : Recursor) : Declaration := {
  type := d.typ, kind := .assumption }

def requireWrapper (constants : Std.HashMap Address Constant) (expected : Constant) :
    Except String Address := do
  let address := commit expected
  let some actual := constants[address]?
    | throw s!"resource adapter: missing canonical projection {address}"
  unless actual == expected do throw s!"resource adapter: invalid projection wrapper {address}"
  return address

def index (indices : Std.HashMap Address UInt64) (address : Address) : Except String UInt64 :=
  match indices[address]? with
  | some i => .ok i
  | none => .error s!"resource adapter: missing typed interface {address}"

structure Tables where
  refs : Array Address
  members : Array Address
  indices : Std.HashMap Address UInt64
  kinds : Array DeclKind
  blobs : Std.HashMap Address UInt64
  univCount : Nat
  shareCount : Nat
  shareOffset : Nat
  deriving Inhabited

def checkedUInt (n : Nat) : Except String UInt64 :=
  if n < UInt64.size then .ok n.toUInt64
  else .error "resource adapter: index overflow"

def Tables.reference (tables : Tables) (i : UInt64) : Except String Address :=
  match tables.refs[i.toNat]? with
  | some a => .ok a
  | none => .error "resource adapter: reference index out of bounds"

def Tables.universes (tables : Tables) (levels : Array UInt64) : Except String Unit := do
  for level in levels do
    if level.toNat >= tables.univCount then throw "resource adapter: universe index out of bounds"

/-- Resolve every local reference namespace, including blob identities. The
global sharing table still contains open expressions; analysis expands them
in the context of each use. This remapping has no contextual validity cache. -/
def remap (tables : Tables) : Nat → Ixon.Expr → Except String Ixon.Expr
  | 0, _ => .error "resource adapter: expression depth exceeded"
  | fuel + 1, e => do
    match e with
    | .var _ => return e
    | .sort level =>
      if level.toNat >= tables.univCount then throw "resource adapter: universe index out of bounds"
      return e
    | .ref i levels =>
      tables.universes levels
      return .ref (← index tables.indices (← tables.reference i)) levels
    | .recur i levels =>
      tables.universes levels
      let some address := tables.members[i.toNat]?
        | throw "resource adapter: recursive index out of bounds"
      return .ref (← index tables.indices address) levels
    | .nat i | .str i =>
      let address ← tables.reference i
      let some id := tables.blobs[address]?
        | throw s!"resource adapter: missing literal blob {address}"
      match e with
      | .nat _ => return .nat id
      | _ => return .str id
    | .share i =>
      if i.toNat >= tables.shareCount then throw "resource adapter: sharing index out of bounds"
      return .share (← checkedUInt (tables.shareOffset + i.toNat))
    | .prj i field value =>
      let typeId ← index tables.indices (← tables.reference i)
      unless tables.kinds[typeId.toNat]? == some .typeConstructor do
        throw "resource adapter: projection owner is not an inductive type"
      return .prj typeId field (← remap tables fuel value)
    | .app fn arg => return .app (← remap tables fuel fn) (← remap tables fuel arg)
    | .lam c type body => return .lam c (← remap tables fuel type) (← remap tables fuel body)
    | .all c r type body => return .all c r (← remap tables fuel type) (← remap tables fuel body)
    | .letE c type value body =>
      return .letE c (← remap tables fuel type) (← remap tables fuel value) (← remap tables fuel body)

def closed (program : Program) : Nat → Nat → Ixon.Expr → CheckM Bool
  | 0, _, _ => throw .budget
  | fuel + 1, depth, e => do
    tick
    match e with
    | .var i => return i.toNat < depth
    | .share i => closed program fuel depth (← expansion program i)
    | .recur .. => return false
    | .app f a => return (← closed program fuel depth f) && (← closed program fuel depth a)
    | .lam _ t b | .all _ _ t b =>
      return (← closed program fuel depth t) && (← closed program fuel (depth + 1) b)
    | .letE _ t v b =>
      return (← closed program fuel depth t) && (← closed program fuel depth v) &&
        (← closed program fuel (depth + 1) b)
    | .prj _ _ v => closed program fuel depth v
    | _ => return true

/-- Initial transparent projection rule: a single constructor with no
parameters/indices, closed field types, and unrestricted field quantities.
Finite-use and dependent fields require a richer elimination rule. Omitting
a rule makes every attempted resource projection fail closed. -/
def fields (program : Program) (limits : Limits) (typeId ctorId : UInt64) (count : Nat) :
    Except Error (Array Field) := runCheck limits do
  let mut type := (← declaration program ctorId).type
  let mut fields := #[]
  for i in [:count] do
    type ← whnf program limits.depth type
    let .all input _ domain body := type | throw (.unsupported "constructor field telescope")
    unless input.uses == .many && (← closed program limits.depth 0 domain) do
      throw (.unsupported "dependent or finite-use projection field")
    fields := fields.push { typeRef := typeId, index := i.toUInt64, type := domain, contract := input.value }
    type := body
  return fields

def prepare (env : Ixon.Env) (profile : Profile := {}) : Except String AddressedProgram := do
  let profileAddress ← profile.address
  let entries := env.consts.toArray.qsort fun a b => Address.cmpBytes a.1 b.1 == .lt
  let mut constants : Std.HashMap Address Constant := {}
  for (address, lazy) in entries do
    if address.hash.size != 32 then throw "resource adapter: invalid constant address"
    let raw := lazy.rawBytes
    unless Address.blake3 raw == address do throw s!"resource adapter: constant hash mismatch {address}"
    -- Parse the bounded raw bytes even if a caller supplied a materialized cache.
    let constant ← (runGetExact getConstant raw).mapError fun e => s!"resource adapter: {address}: {e}"
    unless serConstant constant == raw do throw s!"resource adapter: noncanonical constant {address}"
    constants := constants.insert address constant
  let mut pending : Array Pending := #[]
  let mut groups : Array (Array Address) := #[]
  let mut fieldSpecs : Array (Address × Address × Nat) := #[]
  for (address, _) in entries do
    let constant := constants[address]!
    match constant.info with
    | .defn d =>
      pending := pending.push ⟨address, constant, #[address], definition d, #[]⟩
    | .recr r =>
      pending := pending.push ⟨address, constant, #[address], recursor r, r.rules.map (·.rhs)⟩
    | .axio a =>
      pending := pending.push ⟨address, constant, #[], { type := a.typ, kind := .assumption }, #[]⟩
    | .quot q =>
      pending := pending.push ⟨address, constant, #[], { type := q.typ, kind := .assumption }, #[]⟩
    | .muts members =>
      if members.isEmpty then throw "resource adapter: empty mutual block"
      let mut addresses := #[]
      for i in [:members.size] do
        addresses := addresses.push (← requireWrapper constants (memberWrapper address i.toUInt64 members[i]!))
      let mut group := addresses
      for i in [:members.size] do
        let member := addresses[i]!
        match members[i]! with
        | .defn d =>
          pending := pending.push ⟨member, constant, addresses, definition d, #[]⟩
        | .recr r =>
          pending := pending.push ⟨member, constant, addresses, recursor r, r.rules.map (·.rhs)⟩
        | .indc ind =>
          pending := pending.push ⟨member, constant, addresses,
            { type := ind.typ, kind := .typeConstructor }, #[]⟩
          for j in [:ind.ctors.size] do
            let ctor := ind.ctors[j]!
            let ctorAddr ← requireWrapper constants (constructorWrapper address i.toUInt64 j.toUInt64)
            unless ctor.cidx.toNat == j && ctor.params == ind.params && ctor.lvls == ind.lvls do
              throw "resource adapter: inconsistent constructor header"
            pending := pending.push ⟨ctorAddr, constant, addresses,
              { type := ctor.typ, kind := if ctor.isUnsafe then .assumption else .constructor }, #[]⟩
            group := group.push ctorAddr
            if !ind.isUnsafe && !ctor.isUnsafe && ind.params == 0 && ind.indices == 0 && ind.ctors.size == 1 then
              fieldSpecs := fieldSpecs.push (member, ctorAddr, ctor.fields.toNat)
          if ind.isUnsafe then
            -- Unsafe nominal representations need an explicit profile assumption.
            let k := pending.size - ind.ctors.size - 1
            let p := pending[k]!
            pending := pending.set! k { p with declaration := { p.declaration with kind := .assumption } }
      groups := groups.push group
    | _ => pure ()
  pending := pending.qsort fun a b => Address.cmpBytes a.address b.address == .lt
  let mut indices : Std.HashMap Address UInt64 := {}
  let mut addresses := #[]
  for i in [:pending.size] do
    let address := pending[i]!.address
    if indices.contains address then throw "resource adapter: duplicate resolved declaration"
    indices := indices.insert address (← checkedUInt i)
    addresses := addresses.push address
  for (address, _) in entries do
    match constants[address]!.info with
    | .dPrj _ | .iPrj _ | .rPrj _ | .cPrj _ =>
      unless indices.contains address do throw s!"resource adapter: invalid or orphan projection {address}"
    | _ => pure ()
  let mut blobs : Std.HashMap Address UInt64 := {}
  for (address, bytes) in env.blobs.toArray.qsort (fun a b => Address.cmpBytes a.1 b.1 == .lt) do
    unless address.hash.size == 32 && Address.blake3 bytes == address do
      throw s!"resource adapter: blob hash mismatch {address}"
    blobs := blobs.insert address (← checkedUInt blobs.size)
  let kinds := pending.map (·.declaration.kind)
  let mut program : Program := { declarations := #[] }
  -- One remapped sharing table per distinct parent constant.
  let mut offsets : Std.HashMap Address Nat := {}
  for p in pending do
    let parent := commit p.constant
    let tables : Tables := {
      refs := p.constant.refs, members := p.members, indices, kinds, blobs
      univCount := p.constant.univs.size, shareCount := p.constant.sharing.size
      shareOffset := offsets[parent]?.getD program.sharing.size }
    if !offsets.contains parent then
      offsets := offsets.insert parent tables.shareOffset
      for expression in p.constant.sharing do
        program := { program with sharing := program.sharing.push (← remap tables profile.limits.depth expression) }
    let d := p.declaration
    let type ← remap tables profile.limits.depth d.type
    let body ← d.body.mapM (remap tables profile.limits.depth)
    let i := program.declarations.size
    program := { program with declarations := program.declarations.push { d with type, body } }
    for expression in p.auxiliary do
      program := { program with auxiliary := program.auxiliary.push (i, ← remap tables profile.limits.depth expression) }
  for group in groups do
    let group ← group.mapM fun a => return (← index indices a).toNat
    program := { program with groups := program.groups.push group }
  let resolveList := fun (list : Array Address) => list.mapM (index indices)
  let assumptions ← resolveList profile.assumptions
  let shareable ← resolveList profile.shareableTypes
  let choices ← resolveList profile.choices
  let literalType := fun (address : Address) => do
    let i ← index indices address
    unless kinds[i.toNat]? == some .typeConstructor do
      throw "resource adapter: literal type must be a checked nominal type"
    pure (Ixon.Expr.ref i #[])
  program := { program with
    natType := ← profile.natType.mapM literalType
    stringType := ← profile.stringType.mapM literalType
    shareableTypes := shareable, choices }
  for (typeAddr, ctorAddr, count) in fieldSpecs do
    if let .ok derived := fields program profile.limits (← index indices typeAddr) (← index indices ctorAddr) count then
      program := { program with fields := program.fields ++ derived }
  return {
    program, addresses, profileAddress
    policy := {
      assumptions := assumptions.map UInt64.toNat
      shareableTypes := shareable.map UInt64.toNat, choices := choices.map UInt64.toNat } }

/-- Resource-only validation of addressed bytes. Erased typechecking and
claim construction belong to the combined validator, not this helper. -/
def checkResources (env : Ixon.Env) (profile : Profile := {}) : Except String AddressedProgram := do
  let resolved ← prepare env profile
  (admitProgram resolved.program resolved.policy profile.limits).mapError fun error =>
    let location := error.declaration.bind fun i => resolved.addresses[i]?
    s!"resource admission {location}: {repr error.error}"
  return resolved

end Addressed

end Ix.Resource

end
