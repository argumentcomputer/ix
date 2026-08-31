import Ix.Compile.Verify.IxonValue
import Ix.Compile.Verify.Codec
import Std.Data.HashMap.Lemmas

/-!
# Immutable compiler catalog and representation well-formedness

This module states the X1 representation boundary without running Ix.Tc.  It
separates content-address integrity, finite immutable lookup support, logical
environment views, wire representability, and expression-table resolution.

`ExprTableWF` gives sharing indices a decreasing table bound.  Consequently a
well-formed sharing entry may refer only to an earlier entry: forward edges
and cycles have no derivation.  This is stricter than mere in-range lookup and
matches the canonical sharing order expected from compiler output.
-/

namespace Ix.Compile.Verify

/-- A partial function has finite support when one concrete list contains
every successful key.  Duplicates are harmless. -/
def FinitelySupported {α : Type u} {β : Type v}
    (lookup : α → Option β) : Prop :=
  ∃ keys : List α, ∀ ⦃key value⦄, lookup key = some value → key ∈ keys

namespace FinitelySupported

theorem none : FinitelySupported (fun _ : α => (none : Option β)) :=
  ⟨[], fun {_ _} h => by simp at h⟩

theorem mono {left right : α → Option β}
    (hright : FinitelySupported right)
    (hsub : ∀ {key value}, left key = some value → right key = some value) :
    FinitelySupported left := by
  obtain ⟨keys, hkeys⟩ := hright
  exact ⟨keys, fun {_ _} h => hkeys (hsub h)⟩

/-- Finiteness transports across lookups with different result types when
every successful left key also succeeds on the right. -/
theorem keyMono {left : α → Option β} {right : α → Option γ}
    (hright : FinitelySupported right)
    (hsub : ∀ {key value}, left key = some value →
      ∃ other, right key = some other) :
    FinitelySupported left := by
  obtain ⟨keys, hkeys⟩ := hright
  exact ⟨keys, fun {_ _} h => by obtain ⟨_, hr⟩ := hsub h; exact hkeys hr⟩

end FinitelySupported

/-- A digest-keyed map is faithful on lookup when every queried key returned
by the map is structurally the stored key, not merely `BEq`-equal to it.  Ix
intentionally omits `LawfulBEq` for digest-keyed names and addresses; this
premise is the explicit finite collision boundary. -/
def HashMapKeyFaithful [BEq α] [Hashable α]
    (map : Std.HashMap α β) : Prop :=
  ∀ {key value}, map.get? key = some value →
    ∃ stored, (stored, value) ∈ map.toList ∧ stored = key

namespace FinitelySupported

/-- A concrete map has finite structural support under explicit key
faithfulness. -/
theorem hashMap [BEq α] [Hashable α] (map : Std.HashMap α β)
    (hfaithful : HashMapKeyFaithful map) : FinitelySupported map.get? := by
  refine ⟨map.toList.map (·.1), fun {key value} hget => ?_⟩
  obtain ⟨stored, hstored, rfl⟩ := hfaithful hget
  apply List.mem_map.mpr
  exact ⟨(stored, value), hstored, rfl⟩

end FinitelySupported

/-! ## Logical catalog views -/

/-- Canonical bytes and semantic literal payloads. -/
structure CanonicalPayloadView where
  constants : Address → Option Ixon.Constant
  semanticBlobs : Address → Option ByteArray

/-- Operational data consumed by anonymous ingress/checking but excluded from
constant identity. -/
structure AnonOperationalView where
  anonHints : Address → Option Lean.ReducibilityHints

/-- Source-facing naming and metadata lookup. -/
structure MetaSidecarView where
  named : Ix.Name → Option Ixon.Named
  names : Address → Option Ix.Name
  metaBlobs : Address → Option ByteArray

/-- Decompile-only links.  At this first boundary they are projected from the
named registry; later M3 work refines their internal components. -/
structure DecompileExtensionView where
  named : Ix.Name → Option Ixon.Named

def Catalog.canonicalView (catalog : Catalog) : CanonicalPayloadView :=
  { constants := catalog.constants, semanticBlobs := catalog.blobs }

def Catalog.operationalView (catalog : Catalog) : AnonOperationalView :=
  { anonHints := catalog.anonHints }

def Catalog.sidecarView (catalog : Catalog) : MetaSidecarView :=
  { named := catalog.named, names := catalog.names, metaBlobs := catalog.blobs }

def Catalog.decompileView (catalog : Catalog) : DecompileExtensionView :=
  { named := catalog.named }

/-- The four proof-facing views are projections of one immutable catalog.
This records role separation without claiming that physically shared blobs
belong to only one role. -/
structure Catalog.Factorization (catalog : Catalog) : Prop where
  canonical : Catalog.canonicalView catalog =
    { constants := catalog.constants, semanticBlobs := catalog.blobs }
  operational : Catalog.operationalView catalog =
    { anonHints := catalog.anonHints }
  sidecar : Catalog.sidecarView catalog =
    { named := catalog.named, names := catalog.names, metaBlobs := catalog.blobs }
  decompile : Catalog.decompileView catalog = { named := catalog.named }

theorem Catalog.factorization (catalog : Catalog) : catalog.Factorization :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Wire representability -/

end Ix.Compile.Verify

namespace Ixon
namespace Expr

def appCount : Ixon.Expr → Nat
  | .app fn _ => fn.appCount + 1
  | _ => 0

def lamCount : Ixon.Expr → Nat
  | .lam _ _ body => body.lamCount + 1
  | _ => 0

def allCount : Ixon.Expr → Nat
  | .all _ _ _ body => body.allCount + 1
  | _ => 0

/-- Every structural count emitted through a `UInt64` is representable. -/
def wireWF : Ixon.Expr → Prop
  | .sort _ | .var _ | .str _ | .nat _ | .share _ => True
  | .ref _ idxs | .recur _ idxs => idxs.size < UInt64.size
  | .prj _ _ value => value.wireWF
  | .app fn arg =>
    fn.wireWF ∧ arg.wireWF ∧ fn.appCount + 1 < UInt64.size
  | .lam _ ty body =>
    ty.wireWF ∧ body.wireWF ∧ body.lamCount + 1 < UInt64.size
  | .all _ _ ty body =>
    ty.wireWF ∧ body.wireWF ∧ body.allCount + 1 < UInt64.size
  | .letE _ ty value body => ty.wireWF ∧ value.wireWF ∧ body.wireWF

end Expr

def Definition.exprs (definition : Definition) : List Expr :=
  [definition.typ, definition.value]

def Recursor.exprs (recursor : Recursor) : List Expr :=
  recursor.typ :: recursor.rules.toList.map (·.rhs)

def Axiom.exprs (axiomInfo : Axiom) : List Expr := [axiomInfo.typ]

def Quotient.exprs (quotient : Quotient) : List Expr := [quotient.typ]

def Constructor.exprs (constructor : Constructor) : List Expr :=
  [constructor.typ]

def Inductive.exprs (indInfo : Inductive) : List Expr :=
  indInfo.typ :: indInfo.ctors.toList.flatMap Constructor.exprs

def MutConst.exprs : MutConst → List Expr
  | .defn definition => definition.exprs
  | .indc indInfo => indInfo.exprs
  | .recr recursor => recursor.exprs

def ConstantInfo.exprs : ConstantInfo → List Expr
  | .defn definition => definition.exprs
  | .recr recursor => recursor.exprs
  | .axio axiomInfo => axiomInfo.exprs
  | .quot quotient => quotient.exprs
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => []
  | .muts members => members.toList.flatMap MutConst.exprs

def Definition.wireWF (definition : Definition) : Prop :=
  definition.typ.wireWF ∧ definition.value.wireWF

def RecursorRule.wireWF (rule : RecursorRule) : Prop := rule.rhs.wireWF

def Recursor.wireWF (recursor : Recursor) : Prop :=
  recursor.typ.wireWF ∧
  recursor.rules.size < UInt64.size ∧
  ∀ rule ∈ recursor.rules, rule.wireWF

def Axiom.wireWF (axiomInfo : Axiom) : Prop := axiomInfo.typ.wireWF

def Quotient.wireWF (quotient : Quotient) : Prop := quotient.typ.wireWF

def Constructor.wireWF (constructor : Constructor) : Prop :=
  constructor.typ.wireWF

def Inductive.wireWF (indInfo : Inductive) : Prop :=
  indInfo.typ.wireWF ∧
  indInfo.ctors.size < UInt64.size ∧
  ∀ constructor ∈ indInfo.ctors, constructor.wireWF

def MutConst.wireWF : MutConst → Prop
  | .defn definition => definition.wireWF
  | .indc indInfo => indInfo.wireWF
  | .recr recursor => recursor.wireWF

def ConstantInfo.wireWF : ConstantInfo → Prop
  | .defn definition => definition.wireWF
  | .recr recursor => recursor.wireWF
  | .axio axiomInfo => axiomInfo.wireWF
  | .quot quotient => quotient.wireWF
  | .cPrj projection => projection.block.hash.size = 32
  | .rPrj projection => projection.block.hash.size = 32
  | .iPrj projection => projection.block.hash.size = 32
  | .dPrj projection => projection.block.hash.size = 32
  | .muts members =>
    members.size < UInt64.size ∧ ∀ member ∈ members, member.wireWF

/-- Complete production-codec domain for a constant: every serialized count is
representable, every expression and universe payload has a lossless telescope
count, and every address payload contains the 32 bytes consumed by the reader. -/
def Constant.wireWF (constant : Constant) : Prop :=
  constant.info.wireWF ∧
  constant.sharing.size < UInt64.size ∧
  (∀ expr ∈ constant.sharing, expr.wireWF) ∧
  constant.refs.size < UInt64.size ∧
  (∀ ref ∈ constant.refs, ref.hash.size = 32) ∧
  constant.univs.size < UInt64.size ∧
  (∀ univ ∈ constant.univs,
    Ix.Compile.Verify.Codec.Ixon.Univ.WireWF univ)

end Ixon

namespace Ix.Compile.Verify

/-! ## Resolved expression tables and canonical sharing order -/

/-- Syntactic/table well-formedness of one Ixon expression.  The sharing
limit decreases at every `.share` edge, making the relation well founded even
though sharing expansions are stored outside the expression tree. -/
inductive ExprTableWF (catalog : Catalog) (ctx : DecodeCtx) :
    Nat → Ixon.Expr → Prop where
  | var {limit idx} : ExprTableWF catalog ctx limit (.var idx)
  | sort {limit idx univ} :
    ctx.univs[idx.toNat]? = some univ →
    ExprTableWF catalog ctx limit (.sort idx)
  | ref {limit refIdx univIdxs addr constant} :
    ctx.refs[refIdx.toNat]? = some addr →
    catalog.constants addr = some constant →
    (∀ idx ∈ univIdxs, ∃ univ, ctx.univs[idx.toNat]? = some univ) →
    ExprTableWF catalog ctx limit (.ref refIdx univIdxs)
  | recur {limit recIdx univIdxs addr constant} :
    ctx.mutAddrs[recIdx.toNat]? = some addr →
    catalog.constants addr = some constant →
    (∀ idx ∈ univIdxs, ∃ univ, ctx.univs[idx.toNat]? = some univ) →
    ExprTableWF catalog ctx limit (.recur recIdx univIdxs)
  | prj {limit typeRefIdx field value addr constant} :
    ctx.refs[typeRefIdx.toNat]? = some addr →
    catalog.constants addr = some constant →
    ExprTableWF catalog ctx limit value →
    ExprTableWF catalog ctx limit (.prj typeRefIdx field value)
  | str {limit refIdx addr bytes} :
    ctx.refs[refIdx.toNat]? = some addr →
    catalog.blobs addr = some bytes →
    ExprTableWF catalog ctx limit (.str refIdx)
  | nat {limit refIdx addr bytes} :
    ctx.refs[refIdx.toNat]? = some addr →
    catalog.blobs addr = some bytes →
    ExprTableWF catalog ctx limit (.nat refIdx)
  | app {limit fn arg} :
    ExprTableWF catalog ctx limit fn →
    ExprTableWF catalog ctx limit arg →
    ExprTableWF catalog ctx limit (.app fn arg)
  | lam {limit uses ty body} :
    ExprTableWF catalog ctx limit ty →
    ExprTableWF catalog ctx limit body →
    ExprTableWF catalog ctx limit (.lam uses ty body)
  | all {limit uses owned ty body} :
    ExprTableWF catalog ctx limit ty →
    ExprTableWF catalog ctx limit body →
    ExprTableWF catalog ctx limit (.all uses owned ty body)
  | letE {limit nonDep ty value body} :
    ExprTableWF catalog ctx limit ty →
    ExprTableWF catalog ctx limit value →
    ExprTableWF catalog ctx limit body →
    ExprTableWF catalog ctx limit (.letE nonDep ty value body)
  | share {limit idx expansion} :
    idx.toNat < limit →
    ctx.sharing[idx.toNat]? = some expansion →
    ExprTableWF catalog ctx idx.toNat expansion →
    ExprTableWF catalog ctx limit (.share idx)

namespace ExprTableWF

/-- Increasing the permitted sharing prefix preserves well-formedness. -/
theorem mono {catalog : Catalog} {ctx : DecodeCtx} {small large : Nat}
    {expr : Ixon.Expr} (hbound : small ≤ large)
    (h : ExprTableWF catalog ctx small expr) :
    ExprTableWF catalog ctx large expr := by
  induction h with
  | var => exact .var
  | sort hidx => exact .sort hidx
  | ref href hconstant hunivs => exact .ref href hconstant hunivs
  | recur href hconstant hunivs => exact .recur href hconstant hunivs
  | prj href hconstant _ ih => exact .prj href hconstant (ih hbound)
  | str href hblob => exact .str href hblob
  | nat href hblob => exact .nat href hblob
  | app _ _ ihfn iharg => exact .app (ihfn hbound) (iharg hbound)
  | lam _ _ ihty ihbody => exact .lam (ihty hbound) (ihbody hbound)
  | all _ _ ihty ihbody => exact .all (ihty hbound) (ihbody hbound)
  | letE _ _ _ ihty ihvalue ihbody =>
    exact .letE (ihty hbound) (ihvalue hbound) (ihbody hbound)
  | share hidx hexpansion hexp =>
    exact .share (Nat.lt_of_lt_of_le hidx hbound) hexpansion hexp

end ExprTableWF

/-- Every sharing entry is well formed against the strict prefix before it. -/
def DecodeCtx.SharingWF (catalog : Catalog) (ctx : DecodeCtx) : Prop :=
  ∀ ⦃idx expansion⦄, ctx.sharing[idx]? = some expansion →
    ExprTableWF catalog ctx idx expansion

/-- A root may use the complete sharing table, whose entries themselves are
strictly ordered. -/
structure DecodeCtx.RootWF (catalog : Catalog) (ctx : DecodeCtx)
    (expr : Ixon.Expr) : Prop where
  sharing : ctx.SharingWF catalog
  root : ExprTableWF catalog ctx ctx.sharing.size expr

/-! ## Constant and catalog integrity -/

def Catalog.mutAddrsFor (catalog : Catalog) (self : Address) : Array Address :=
  (catalog.memberAddrs self).getD #[]

def DecodeCtx.ofConstant (catalog : Catalog) (self : Address)
    (constant : Ixon.Constant) : DecodeCtx :=
  { refs := constant.refs
    univs := constant.univs
    sharing := constant.sharing
    mutAddrs := catalog.mutAddrsFor self }

/-- Projection payloads point to a block member of the expected shape. -/
def ConstantProjectionWF (catalog : Catalog) :
    Ixon.ConstantInfo → Prop
  | .iPrj projection =>
    ∃ block members indInfo,
      catalog.constants projection.block = some block ∧
      block.info = .muts members ∧
      members[projection.idx.toNat]? = some (.indc indInfo)
  | .cPrj projection =>
    ∃ block members indInfo ctorInfo,
      catalog.constants projection.block = some block ∧
      block.info = .muts members ∧
      members[projection.idx.toNat]? = some (.indc indInfo) ∧
      indInfo.ctors[projection.cidx.toNat]? = some ctorInfo
  | .rPrj projection =>
    ∃ block members recursor,
      catalog.constants projection.block = some block ∧
      block.info = .muts members ∧
      members[projection.idx.toNat]? = some (.recr recursor)
  | .dPrj projection =>
    ∃ block members definition,
      catalog.constants projection.block = some block ∧
      block.info = .muts members ∧
      members[projection.idx.toNat]? = some (.defn definition)
  | _ => True

/-- One stored constant is wire-representable, content-addressed, has ordered
sharing, resolves every expression table index, and has valid projection
shape. -/
structure ConstantWF (catalog : Catalog) (self : Address)
    (constant : Ixon.Constant) : Prop where
  wire : constant.wireWF
  address : self = Address.blake3 (Ixon.serConstant constant)
  sharing : (DecodeCtx.ofConstant catalog self constant).SharingWF catalog
  bodies : ∀ expr ∈ constant.info.exprs,
    ExprTableWF catalog (DecodeCtx.ofConstant catalog self constant)
      constant.sharing.size expr
  projection : ConstantProjectionWF catalog constant.info

/-- Concrete finite witnesses for every stored lookup role. -/
structure Catalog.Finite (catalog : Catalog) : Prop where
  constants : FinitelySupported catalog.constants
  blobs : FinitelySupported catalog.blobs
  named : FinitelySupported catalog.named
  names : FinitelySupported catalog.names
  anonHints : FinitelySupported catalog.anonHints
  memberAddrs : FinitelySupported catalog.memberAddrs

/-- X1 in-memory catalog integrity.  This is representation
well-formedness, not Lean4Lean `VEnv.WF`. -/
structure Catalog.WF (catalog : Catalog) : Prop where
  finite : catalog.Finite
  constants : ∀ {addr constant}, catalog.constants addr = some constant →
    ConstantWF catalog addr constant
  blobs : ∀ {addr bytes}, catalog.blobs addr = some bytes →
    addr = Address.blake3 bytes
  named : ∀ {name entry}, catalog.named name = some entry →
    ∃ constant, catalog.constants entry.addr = some constant
  names : ∀ {addr name}, catalog.names addr = some name → addr = name.getHash
  members : ∀ {block addrs}, catalog.memberAddrs block = some addrs →
    ∀ addr ∈ addrs, ∃ constant, catalog.constants addr = some constant

def Catalog.empty : Catalog where
  nameOf := fun _ => none
  blobs := fun _ => none

theorem Catalog.empty_finite : Catalog.empty.Finite :=
  ⟨FinitelySupported.none, FinitelySupported.none, FinitelySupported.none,
    FinitelySupported.none, FinitelySupported.none, FinitelySupported.none⟩

theorem Catalog.empty_wf : Catalog.empty.WF := by
  refine ⟨Catalog.empty_finite, ?_, ?_, ?_, ?_, ?_⟩
  · intro addr constant h
    change (none : Option Ixon.Constant) = some constant at h
    cases h
  · intro addr bytes h
    change (none : Option ByteArray) = some bytes at h
    cases h
  · intro name entry h
    change (none : Option Ixon.Named) = some entry at h
    cases h
  · intro addr name h
    change (none : Option Ix.Name) = some name at h
    cases h
  · intro block addrs h
    change (none : Option (Array Address)) = some addrs at h
    cases h

/-- Immutable view of a concrete `Ixon.Env`.  `nameOf` and mutual member
addresses remain explicit semantic inputs because the wire environment stores
Ix names and projection constants, not Lean4Lean names or a redundant member
array. -/
def Catalog.ofEnv (env : Ixon.Env)
    (nameOf : Address → Option Lean.Name)
    (memberAddrs : Address → Option (Array Address) := fun _ => none) :
    Catalog where
  nameOf := nameOf
  constants := env.getConst?
  blobs := env.getBlob?
  named := env.getNamed?
  names := env.names.get?
  anonHints := env.anonHints.get?
  memberAddrs := memberAddrs

/-- Collision/key-faithfulness premises for the finite physical maps of one
concrete environment.  This is run-scoped data, not a global digest axiom. -/
structure EnvLookupFaithful (env : Ixon.Env) : Prop where
  consts : HashMapKeyFaithful env.consts
  blobs : HashMapKeyFaithful env.blobs
  named : HashMapKeyFaithful env.named
  names : HashMapKeyFaithful env.names
  anonHints : HashMapKeyFaithful env.anonHints

/-- Concrete environment maps give finite support automatically; only the
proof-only mutual-member view needs an explicit finite witness.  Structural
key faithfulness is explicit because these maps use digest equality. -/
theorem Catalog.ofEnv_finite (env : Ixon.Env)
    (nameOf : Address → Option Lean.Name)
    (memberAddrs : Address → Option (Array Address))
    (hlookup : EnvLookupFaithful env)
    (hmembers : FinitelySupported memberAddrs) :
    (Catalog.ofEnv env nameOf memberAddrs).Finite := by
  refine ⟨?_, FinitelySupported.hashMap env.blobs hlookup.blobs,
    FinitelySupported.hashMap env.named hlookup.named,
    FinitelySupported.hashMap env.names hlookup.names,
    FinitelySupported.hashMap env.anonHints hlookup.anonHints, hmembers⟩
  apply FinitelySupported.keyMono
    (FinitelySupported.hashMap env.consts hlookup.consts)
  intro addr constant hconstant
  change (env.consts.get? addr).bind Ixon.LazyConstant.get? =
    some constant at hconstant
  obtain ⟨entry, hentry, _⟩ := Option.bind_eq_some_iff.mp hconstant
  exact ⟨entry, hentry⟩

end Ix.Compile.Verify
