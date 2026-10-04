module
public import Ix.Resource.Addressed
public import Ix.Resource.Transport.Validate
public import Ix.Tc.Primitive

/-! Reconstruct the logical source independently of resource-profile
overlays. The caller has already authenticated and erased-checked these
same raw constants. Local universe namespaces are retained and globalized,
and every indexed family and recursor rule is represented. -/
@[expose] public section
namespace Ix.Resource.Transport
open Ixon

structure Source where
  constant : Constant
  members : Array Address
  type : Ixon.Expr
  body : Option Ixon.Expr := none
  kind : Kind
  levels : Nat
  unsafePrimitive : Bool := false
  inductiveInfo : Option Ixon.Inductive := none
  constructorInfo : Option (Address × Ixon.Constructor) := none
  recursorInfo : Option Ixon.Recursor := none
  deriving Inhabited

def sourceDefinition (constant : Constant) (members : Array Address) (d : Definition) : Source := {
  constant, members, type := d.typ, body := some d.value, levels := d.lvls.toNat
  kind := if d.safety != .safe || d.kind == .opaq then .opaqueDecl
    else if d.kind == .thm then .theorem else .definition }

def sourceRecursor (constant : Constant) (members : Array Address) (r : Ixon.Recursor) : Source := {
  constant, members, type := r.typ, levels := r.lvls.toNat, kind := .recursor
  unsafePrimitive := r.isUnsafe
  recursorInfo := some r }

def source (constants : Std.HashMap Address Constant) (address : Address) : Except String Source := do
  let some c := constants[address]? | throw "transport adapter: missing source constant"
  match c.info with
  | .defn d => return sourceDefinition c #[address] d
  | .recr r => return sourceRecursor c #[address] r
  | .axio a => return {
      constant := c, members := #[], type := a.typ, levels := a.lvls.toNat
      kind := .axiomDecl (standardAxioms.contains address) }
  | .quot q => return { constant := c, members := #[], type := q.typ, levels := q.lvls.toNat, kind := .quotient }
  | _ =>
    let (block, idx, ctor) ← match c.info with
      | .dPrj p => pure (p.block, p.idx, none)
      | .iPrj p => pure (p.block, p.idx, none)
      | .rPrj p => pure (p.block, p.idx, none)
      | .cPrj p => pure (p.block, p.idx, some p.cidx)
      | _ => throw "transport adapter: unexpected source wrapper"
    let some parent := constants[block]? | throw "transport adapter: missing mutual parent"
    let .muts members := parent.info | throw "transport adapter: invalid mutual parent"
    let addresses := members.mapIdx fun i member =>
      Addressed.commit (Addressed.memberWrapper block i.toUInt64 member)
    let some member := members[idx.toNat]? | throw "transport adapter: invalid mutual member"
    match member, ctor with
    | .defn d, none => return sourceDefinition parent addresses d
    | .recr r, none => return sourceRecursor parent addresses r
    | .indc ind, none => return {
        constant := parent, members := addresses, type := ind.typ, levels := ind.lvls.toNat
        kind := .inductiveType, inductiveInfo := some ind, unsafePrimitive := ind.isUnsafe }
    | .indc ind, some j =>
      let some ctor := ind.ctors[j.toNat]? | throw "transport adapter: invalid constructor ordinal"
      return {
        constant := parent, members := addresses, type := ctor.typ, levels := ctor.lvls.toNat
        kind := .constructor, constructorInfo := some (addresses[idx.toNat]!, ctor)
        unsafePrimitive := ctor.isUnsafe || ind.isUnsafe }
    | _, _ => throw "transport adapter: wrapper kind mismatch"

/-- Shares are indexed in the same declaration order as Addressed.prepare;
only universes differ. Local universe argument IDs become global IDs. -/
def remapSource (tables : Addressed.Tables) (levelOffset : Nat) :
    Nat → Ixon.Expr → Except String Ixon.Expr
  | 0, _ => throw "transport adapter: expression depth exceeded"
  | fuel + 1, e => do
    let level := fun i => do
      unless i.toNat < tables.univs.size do throw "transport adapter: universe index out of bounds"
      Addressed.checkedUInt (levelOffset + i.toNat)
    match e with
    | .sort i => return .sort (← level i)
    | .ref i levels =>
      return .ref (← Addressed.index tables.indices (← tables.reference i)) (← levels.mapM level)
    | .recur i levels =>
      let some address := tables.members[i.toNat]? | throw "transport adapter: recursive index out of bounds"
      return .ref (← Addressed.index tables.indices address) (← levels.mapM level)
    | .app f a => return .app (← remapSource tables levelOffset fuel f) (← remapSource tables levelOffset fuel a)
    | .lam c a b => return .lam c (← remapSource tables levelOffset fuel a) (← remapSource tables levelOffset fuel b)
    | .all c r a b => return .all c r (← remapSource tables levelOffset fuel a) (← remapSource tables levelOffset fuel b)
    | .letE c a v b =>
      return .letE c (← remapSource tables levelOffset fuel a)
        (← remapSource tables levelOffset fuel v) (← remapSource tables levelOffset fuel b)
    | .prj i f v =>
      return .prj (← Addressed.index tables.indices (← tables.reference i)) f
        (← remapSource tables levelOffset fuel v)
    | _ => Addressed.remap tables (fuel + 1) e

def prepare (env : Ixon.Env) (resolved : AddressedProgram) (limits : Limits) :
    Except String (Program × Metadata) := do
  let mut constants : Std.HashMap Address Constant := {}
  for (address, lazy) in env.consts.toArray do
    let c ← (runGetExact getConstant lazy.rawBytes).mapError fun e => s!"transport adapter: {e}"
    unless Addressed.commit c == address && serConstant c == lazy.rawBytes do
      throw "transport adapter: noncanonical source constant"
    constants := constants.insert address c
  let mut indices : Std.HashMap Address UInt64 := {}
  for i in [:resolved.addresses.size] do
    indices := indices.insert resolved.addresses[i]! (← Addressed.checkedUInt i)
  let mut blobs : Std.HashMap Address UInt64 := {}
  let mut metadata : Metadata := {}
  for (address, bytes) in env.blobs.toArray.qsort (fun a b => Address.cmpBytes a.1 b.1 == .lt) do
    let index ← Addressed.checkedUInt blobs.size
    blobs := blobs.insert address index
    metadata := { metadata with naturals := metadata.naturals.push (index, Nat.fromBytesLE bytes.data) }
  let primitive := Tc.PrimAddrs.canonical
  metadata := { metadata with
    natType := indices[primitive.nat]?.map (fun i => .ref i #[])
    stringType := indices[primitive.string]?.map (fun i => .ref i #[])
    eqType := indices[primitive.eq]? }
  let kinds := resolved.program.declarations.map (·.kind)
  let mut p : Program := { declarations := #[], groups := resolved.program.groups }
  let mut offsets : Std.HashMap Address (Nat × Nat) := {}
  let mut recursors : Array (Nat × Ixon.Recursor × Addressed.Tables × Nat) := #[]
  for i in [:resolved.addresses.size] do
    let address := resolved.addresses[i]!
    let s ← source constants address
    if s.unsafePrimitive then
      metadata := { metadata with unsafePrimitives := metadata.unsafePrimitives.push i }
    let parent := Addressed.commit s.constant
    let (shareOffset, levelOffset) := offsets[parent]?.getD (p.sharing.size, metadata.universes.size)
    let tables : Addressed.Tables := {
      refs := s.constant.refs, members := s.members, indices, kinds, blobs, univs := s.constant.univs
      shareCount := s.constant.sharing.size, shareOffset }
    if !offsets.contains parent then
      offsets := offsets.insert parent (shareOffset, levelOffset)
      metadata := { metadata with universes := metadata.universes ++ s.constant.univs }
      for expression in s.constant.sharing do
        p := { p with sharing := p.sharing.push (← remapSource tables levelOffset limits.depth expression) }
    let type ← remapSource tables levelOffset limits.depth s.type
    let body ← s.body.mapM (remapSource tables levelOffset limits.depth)
    p := { p with declarations := p.declarations.push {
      type, body, kind := resolved.program.declarations[i]!.kind } }
    metadata := { metadata with kinds := metadata.kinds.push s.kind, levelArities := metadata.levelArities.push s.levels }
    if let some ind := s.inductiveInfo then
      let mut constructors := #[]
      for j in [:ind.ctors.size] do
        let ctorAddress := Addressed.commit (Addressed.constructorWrapper parent
          ((s.members.findIdx? (· == address)).getD 0).toUInt64 j.toUInt64)
        constructors := constructors.push (← Addressed.index indices ctorAddress)
      metadata := { metadata with inductives := metadata.inductives.push {
        index := i.toUInt64, params := ind.params.toNat, indices := ind.indices.toNat, constructors } }
    if let some (owner, ctor) := s.constructorInfo then
      metadata := { metadata with constructors := metadata.constructors.push {
        index := i.toUInt64, family := ← Addressed.index indices owner, position := ctor.cidx.toNat
        params := ctor.params.toNat, fields := ctor.fields.toNat } }
    if let some rec := s.recursorInfo then
      recursors := recursors.push (i, rec, tables, levelOffset)
      for rule in rec.rules do
        p := { p with auxiliary := p.auxiliary.push (i, ← remapSource tables levelOffset limits.depth rule.rhs) }
  p := sourceProgram metadata p
  for (i, rec, tables, levelOffset) in recursors do
    let family ← (runTyping metadata limits do
      let mut type := p.declarations[i]!.type
      for _ in [: (rec.params + rec.motives + rec.minors + rec.indices).toNat] do
        let (_, _, _, body) ← arrow p metadata limits.depth type
        type := body
      let (_, _, major, _) ← arrow p metadata limits.depth type
      let (head, _) ← splitApp p limits.depth (← whnf p metadata limits.depth major) []
      let .ref family _ := head | throw (.unsupported "transport: recursor major family not exposed")
      return family).mapError (fun error => s!"transport adapter: {repr error}")
    let rules ← rec.rules.mapM fun rule => do
      return { fields := rule.fields.toNat, rhs := ← remapSource tables levelOffset limits.depth rule.rhs : Rule }
    metadata := { metadata with recursors := metadata.recursors.push {
      index := i.toUInt64, family, k := rec.k, params := rec.params.toNat, motives := rec.motives.toNat
      minors := rec.minors.toNat, indices := rec.indices.toNat, rules } }
  metadata := { metadata with resourceSensitive := ← (resourceSensitivity p resolved.program limits).mapError reprStr }
  return (p, metadata)

/-- Internal final phase of combined validation. The caller must have
successfully run ownership admission and same-byte erased validation.
Coverage follows precisely the branches that ownership admission visited;
profile assumptions and equation replacements never count as original-body
coverage. This helper alone is not the combined admission API. -/
def checkAdmitted (env : Ixon.Env) (resolved : AddressedProgram) (limits : Limits) :
    Except String Unit := do
  let marked ← (relevance resolved.program limits).mapError reprStr
  let (logical, metadata) ← prepare env resolved limits
  let roots := (List.range metadata.resourceSensitive.size).toArray.filter (metadata.resourceSensitive[·]!)
  let covered := roots.filter fun i => marked[i]?.getD false &&
    resolved.program.declarations[i]!.kind == .definition &&
    !resolved.policy.assumptions.contains i &&
    !(resolved.program.equations.any fun equation => equation.1.toNat == i)
  (validate logical resolved.program metadata {
    roots, runtimeCovered := covered, assumptions := resolved.policy.assumptions
    equations := resolved.policy.equations } limits).mapError fun failure =>
      let location := failure.declaration.bind (resolved.addresses[·]?)
      s!"resource admission {location}: {repr failure.error}"

end Ix.Resource.Transport
end
