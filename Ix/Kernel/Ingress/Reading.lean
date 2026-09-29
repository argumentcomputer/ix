/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Types
import Ix.Kernel.Const

/-! # Exact readings of anonymous Ixon input

These relations describe the supplied tables and expression constructors,
independently of the bounded reader. Addresses are opaque keys; byte/hash
authentication is a separate contract. Only the ordinary Lean binder modes
have a reading at K3. Sharing is read against a strictly earlier prefix.
-/

namespace Ix.Kernel.Ingress

abbrev Constants := List (Address × Ixon.Constant)
abbrev Blobs := List (Address × ByteArray)

def isProjection : Ixon.ConstantInfo → Bool
  | .dPrj _ | .iPrj _ | .rPrj _ | .cPrj _ => true
  | _ => false

/-- First lookup in the supplied finite store. The environment driver checks
key uniqueness before reading declarations. -/
def lookup (store : List (Address × α)) (address : Address) : Option α :=
  match store with
  | [] => none
  | (key, value) :: rest => if key = address then some value else lookup rest address

/-- Exact structural universe reading; no normalization changes its spelling. -/
def levelTree : Ixon.Univ → VLevel
  | .zero => .zero
  | .succ u => .succ (levelTree u)
  | .max u v => .max (levelTree u) (levelTree v)
  | .imax u v => .imax (levelTree u) (levelTree v)
  | .var i => .param i.toNat

/-- Little-endian natural-number payload, including the empty encoding of zero.
Canonical byte spelling is a separate K4 condition. -/
def natural (bytes : ByteArray) : Nat :=
  bytes.data.toList.foldr (fun byte rest => byte.toNat + 256 * rest) 0

/-- A projection constant carries no expression tables. -/
def emptyTables (source : Ixon.Constant) : Bool :=
  source.sharing.isEmpty && source.refs.isEmpty && source.univs.isEmpty

/-- Resolve a supplied record, checking its projection owner, variant, member
position, and constructor position. The source need not already be in the
store; the writer uses this to validate newly reconstructed projections. -/
def referenceSource (store : Constants) (address : Address) (source : Ixon.Constant) :
    Option (ConstRef Address) :=
  match source.info with
  | .defn _ | .recr _ | .axio _ | .quot _ => some (.member address 0)
  | .muts _ => none
  | .dPrj p => do
    if !emptyTables source then none else do
    let owner ← lookup store p.block
    let .muts members := owner.info | none
    let .defn _ ← members[p.idx.toNat]? | none
    return .member p.block p.idx.toNat
  | .iPrj p => do
    if !emptyTables source then none else do
    let owner ← lookup store p.block
    let .muts members := owner.info | none
    let .indc _ ← members[p.idx.toNat]? | none
    return .member p.block p.idx.toNat
  | .rPrj p => do
    if !emptyTables source then none else do
    let owner ← lookup store p.block
    let .muts members := owner.info | none
    let .recr _ ← members[p.idx.toNat]? | none
    return .member p.block p.idx.toNat
  | .cPrj p => do
    if !emptyTables source then none else do
    let owner ← lookup store p.block
    let .muts members := owner.info | none
    let .indc ind ← members[p.idx.toNat]? | none
    let ctor ← ind.ctors[p.cidx.toNat]?
    if ctor.cidx = p.cidx then return .ctor p.block p.idx.toNat p.cidx.toNat
    else none

/-- Resolve one stored address. A mutual block itself is not a constant
reference. No projection address is reconstructed by hashing. -/
def reference (store : Constants) (address : Address) : Option (ConstRef Address) := do
  let source ← lookup store address
  referenceSource store address source

/-- Tables and finite input stores for one declaration. The literal family is
an explicit choice; the kernel subsequently checks its natural-number fact. -/
structure Context where
  constants : Constants
  blobs : Blobs
  owner : Address
  source : Ixon.Constant
  natFamily : Option (ConstRef Address) := none

namespace Context

def level (ctx : Context) (index : UInt64) : Option VLevel :=
  (ctx.source.univs[index.toNat]?).map levelTree

def levels (ctx : Context) (indices : List UInt64) : Option (List VLevel) :=
  indices.mapM ctx.level

def external (ctx : Context) (index : UInt64) : Option (ConstRef Address) := do
  let address ← ctx.source.refs[index.toNat]?
  reference ctx.constants address

/-- Recursive references name positions of this block, never positions of a
different owner. Only definition and recursor singletons may refer to self. -/
def recursive (ctx : Context) (index : UInt64) : Option (ConstRef Address) :=
  match ctx.source.info with
  | .muts members =>
    if index.toNat < members.size then some (.member ctx.owner index.toNat) else none
  | .defn _ | .recr _ =>
    if index = 0 then some (.member ctx.owner 0) else none
  | _ => none

def blob (ctx : Context) (index : UInt64) : Option ByteArray := do
  let address ← ctx.source.refs[index.toNat]?
  lookup ctx.blobs address

end Context

/-- A constructor-by-constructor reading, including all table resolutions and
the exact accepted binder contracts. A let's contract (its dependency bit,
value or shared-borrow kind, and binder contract) is erased, as at upstream
`Ix.Tc`'s erased typing boundary: the dependent kernel let syntax checks the
type regardless, and the egress layout retains the contract. -/
inductive ExprReads (ctx : Context) : Nat → Ixon.Expr → VExpr Address → Prop where
  | var : ExprReads ctx limit (.var i) (.bvar i.toNat)
  | sort : ctx.level i = some level → ExprReads ctx limit (.sort i) (.sort level)
  | ref : ctx.external i = some ref → ctx.levels us.toList = some levels →
      ExprReads ctx limit (.ref i us) (.const ref levels)
  | recur : ctx.recursive i = some ref → ctx.levels us.toList = some levels →
      ExprReads ctx limit (.recur i us) (.const ref levels)
  | nat : ctx.blob i = some bytes → ctx.natFamily = some family →
      ExprReads ctx limit (.nat i) (.natLit family (natural bytes))
  | app : ExprReads ctx limit f f' → ExprReads ctx limit a a' →
      ExprReads ctx limit (.app f a) (.app f' a')
  | lam : ExprReads ctx limit type type' → ExprReads ctx limit body body' →
      ExprReads ctx limit (.lam .many type body) (.lam type' body')
  | all : ExprReads ctx limit type type' → ExprReads ctx limit body body' →
      ExprReads ctx limit (.all .many .shared type body) (.forallE type' body')
  | letE : ExprReads ctx limit type type' → ExprReads ctx limit value value' →
      ExprReads ctx limit body body' →
      ExprReads ctx limit (.letE contract type value body) (.letE type' value' body')
  | prj : ctx.external i = some ref → ExprReads ctx limit value value' →
      ExprReads ctx limit (.prj i field value) (.proj ref field.toNat value')
  | share : i.toNat < limit → ctx.source.sharing[i.toNat]? = some value →
      ExprReads ctx i.toNat value value' → ExprReads ctx limit (.share i) value'

/-- The table reading is independent of reader fuel or search strategy. -/
theorem ExprReads.deterministic {ctx : Context} {limit : Nat} {input : Ixon.Expr}
    {left right : VExpr Address} (h : ExprReads ctx limit input left)
    (other : ExprReads ctx limit input right) : left = right := by
  induction h generalizing right <;> cases other <;> simp_all
  all_goals repeat first | apply And.intro | apply_assumption

def safety : Ix.DefinitionSafety → Safety
  | .safe => .safe
  | .unsaf => .unsafe
  | .part => .partial

def unsafeFlag (flag : Bool) : Safety := if flag then .unsafe else .safe

def kind : Ix.DefKind → DefKind
  | .defn => .definition
  | .opaq => .opaque
  | .thm => .theorem

def quotientKind : Ix.QuotKind → QuotKind
  | .type => .type
  | .ctor => .ctor
  | .lift => .lift
  | .ind => .ind

abbrev ExpressionReads (ctx : Context) := ExprReads ctx ctx.source.sharing.size

inductive DefinitionReads (ctx : Context) (source : Ixon.Definition) : Const Address → Prop where
  | mk : ExpressionReads ctx source.typ type → ExpressionReads ctx source.value value →
      DefinitionReads ctx source
        (.defn source.lvls.toNat (kind source.kind) type value (safety source.safety))

/-- The stored constructor index must equal its position in the owner's
constructor array. All remaining fields have an exact structural reading. -/
def ConstructorReads (ctx : Context) (source : Ixon.Constructor × Nat)
    (target : Ctor Address) : Prop :=
  source.1.cidx.toNat = source.2 ∧
  target.uvars = source.1.lvls.toNat ∧ target.nparams = source.1.params.toNat ∧
  target.nfields = source.1.fields.toNat ∧ target.safety = unsafeFlag source.1.isUnsafe ∧
  ExpressionReads ctx source.1.typ target.type

def RuleReads (ctx : Context) (source : Ixon.RecursorRule) (target : RecRule Address) : Prop :=
  target.nfields = source.fields.toNat ∧ ExpressionReads ctx source.rhs target.rhs

inductive RecursorReads (ctx : Context) (source : Ixon.Recursor) : Const Address → Prop where
  | mk : ExpressionReads ctx source.typ type →
      Forall₂ (RuleReads ctx) source.rules.toList rules →
      RecursorReads ctx source (.recursor source.lvls.toNat source.params.toNat
        source.indices.toNat source.motives.toNat source.minors.toNat type rules
        source.k (unsafeFlag source.isUnsafe))

inductive InductiveReads (ctx : Context) (source : Ixon.Inductive) : Const Address → Prop where
  | mk : ExpressionReads ctx source.typ type →
      Forall₂ (ConstructorReads ctx) source.ctors.toList.zipIdx ctors →
      InductiveReads ctx source (.induct source.lvls.toNat source.params.toNat
        source.indices.toNat type ctors (unsafeFlag source.isUnsafe))

inductive MemberReads (ctx : Context) : Ixon.MutConst → Const Address → Prop where
  | defn : DefinitionReads ctx d c → MemberReads ctx (.defn d) c
  | indc : InductiveReads ctx d c → MemberReads ctx (.indc d) c
  | recr : RecursorReads ctx d c → MemberReads ctx (.recr d) c

/-- Exact declaration fields and ordered member identities. Projection records
name declarations in their owning block and are validated separately. -/
inductive InfoReads (ctx : Context) : Ixon.ConstantInfo → Block Address → Prop where
  | defn : DefinitionReads ctx d c → InfoReads ctx (.defn d) ⟨[c]⟩
  | recr : RecursorReads ctx d c → InfoReads ctx (.recr d) ⟨[c]⟩
  | axio : ExpressionReads ctx d.typ type →
      InfoReads ctx (.axio d) ⟨[.axiom d.lvls.toNat type (unsafeFlag d.isUnsafe)]⟩
  | quot : ExpressionReads ctx d.typ type →
      InfoReads ctx (.quot d) ⟨[.quot (quotientKind d.kind) d.lvls.toNat type]⟩
  | muts : Forall₂ (MemberReads ctx) members.toList constants →
      InfoReads ctx (.muts members) ⟨constants⟩

abbrev BlockReads (ctx : Context) := InfoReads ctx ctx.source.info

end Ix.Kernel.Ingress
