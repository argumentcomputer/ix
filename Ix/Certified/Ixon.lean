/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon
import Ix.Theory.Certified

/-!
# Ixon input adapter for the certified profile

This adapter checks table indices, projection ownership/kinds, ordinary Lean
binder modes, and bounded sharing expansion. It preserves block/member
positions and constructor metadata, including checked constructor positions.
Natural literals use a separately authenticated canonical blob table.
Lets and strings are not enabled here. Semantic admission independently
restricts inductive shapes. Byte authentication and the public claim binding
are separate from this structural adapter.
-/

namespace Ix.Certified

open Ix.Theory
open Ix.Theory.Certified

instance addressDecidableEq : DecidableEq Address := fun a b =>
  if h : a.hash = b.hash then
    .isTrue (by cases a; cases b; cases h; rfl)
  else .isFalse (fun he => h (congrArg Address.hash he))

def lookup (entries : List (Address × α)) (address : Address) : Option α :=
  match entries with
  | [] => none
  | (key, value) :: rest => if address = key then some value else lookup rest address

theorem lookup_isSome (entries : List (Address × α)) (address : Address) :
    (lookup entries address).isSome ↔ address ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [lookup]
  | cons entry rest ih =>
    obtain ⟨key, value⟩ := entry
    by_cases h : address = key <;> simp_all [lookup]

def readLevel : Ixon.Univ → VLevel
  | .zero => .zero
  | .succ u => .succ (readLevel u)
  | .max u v => .max (readLevel u) (readLevel v)
  | .imax u v => .imax (readLevel u) (readLevel v)
  | .var i => .param i.toNat

abbrev Objects := List (Address × Ixon.Constant)
abbrev Naturals := List (Address × Nat)

def mutMember? (objects : Objects) (block : Address) (index : UInt64) : Option Ixon.MutConst := do
  let source ← lookup objects block
  let .muts members := source.info | none
  members[index.toNat]?

/-- Projection wrappers must refer to the matching source member kind. -/
def resolveReference? (objects : Objects) (address : Address) : Option (ConstRef Address) := do
  let source ← lookup objects address
  match source.info with
  | .defn _ | .recr _ | .axio _ | .quot _ => some (.member address 0)
  | .iPrj projection => do
    let .indc _ ← mutMember? objects projection.block projection.idx | none
    return .member projection.block projection.idx.toNat
  | .rPrj projection => do
    let .recr _ ← mutMember? objects projection.block projection.idx | none
    return .member projection.block projection.idx.toNat
  | .dPrj projection => do
    let .defn _ ← mutMember? objects projection.block projection.idx | none
    return .member projection.block projection.idx.toNat
  | .cPrj projection => do
    let .indc family ← mutMember? objects projection.block projection.idx | none
    let _ ← family.ctors[projection.cidx.toNat]?
    return .ctor projection.block projection.idx.toNat projection.cidx.toNat
  | .muts _ => none

def readLevels? (source : Ixon.Constant) (indices : Array UInt64) : Option (List VLevel) :=
  indices.toList.mapM fun index => (source.univs[index.toNat]?).map readLevel

def readExpr? (fuel : Nat) (objects : Objects) (naturals : Naturals) (block : Address) (source : Ixon.Constant) :
    Ixon.Expr → Option (VExpr Address) :=
  match fuel with
  | 0 => fun _ => none
  | fuel + 1 => fun expression =>
    match expression with
    | .var index => some (.bvar index.toNat)
    | .sort index => (source.univs[index.toNat]?).map (VExpr.sort ∘ readLevel)
    | .ref index levels => do
      let address ← source.refs[index.toNat]?
      let reference ← resolveReference? objects address
      let levels ← readLevels? source levels
      return .const reference levels
    | .recur index levels => do
      let levels ← readLevels? source levels
      return .const (.member block index.toNat) levels
    | .app f a => do
      let f ← readExpr? fuel objects naturals block source f
      let a ← readExpr? fuel objects naturals block source a
      return .app f a
    | .lam .many A b => do
      let A ← readExpr? fuel objects naturals block source A
      let b ← readExpr? fuel objects naturals block source b
      return .lam A b
    | .all .many .shared A B => do
      let A ← readExpr? fuel objects naturals block source A
      let B ← readExpr? fuel objects naturals block source B
      return .forallE A B
    | .prj owner field value => do
      let address ← source.refs[owner.toNat]?
      let ownerSource ← lookup objects address
      let .iPrj _ := ownerSource.info | none
      let reference ← resolveReference? objects address
      let value ← readExpr? fuel objects naturals block source value
      return .proj reference field.toNat value
    | .nat index => do
      let address ← source.refs[index.toNat]?
      return .natLit (← lookup naturals address)
    | .share index => do
      let shared ← source.sharing[index.toNat]?
      readExpr? fuel objects naturals block source shared
    | _ => none

def readSafety : Ix.DefinitionSafety → Safety
  | .safe => .safe
  | .unsaf => .unsafe
  | .part => .partial

def readDefKind : Ix.DefKind → Ix.Theory.DefKind
  | .defn => .definition
  | .thm => .theorem
  | .opaq => .opaque

def readQuotKind : Ix.QuotKind → Ix.Theory.QuotKind
  | .type => .type
  | .ctor => .ctor
  | .lift => .lift
  | .ind => .ind

def readDefinition? (fuel : Nat) (objects : Objects) (naturals : Naturals) (block : Address)
    (source : Ixon.Constant) (definition : Ixon.Definition) : Option (Const Address) := do
  let type ← readExpr? fuel objects naturals block source definition.typ
  let body ← readExpr? fuel objects naturals block source definition.value
  return .defn definition.lvls.toNat (readDefKind definition.kind) type body
    (readSafety definition.safety)

def readRecursor? (fuel : Nat) (objects : Objects) (naturals : Naturals) (block : Address)
    (source : Ixon.Constant) (recursor : Ixon.Recursor) : Option (Const Address) := do
  let type ← readExpr? fuel objects naturals block source recursor.typ
  let rules ← recursor.rules.toList.mapM fun rule => do
    let rhs ← readExpr? fuel objects naturals block source rule.rhs
    return (⟨rule.fields.toNat, rhs⟩ : RecRule Address)
  return .recursor recursor.lvls.toNat recursor.params.toNat recursor.indices.toNat
    recursor.motives.toNat recursor.minors.toNat type rules recursor.k
    (if recursor.isUnsafe then .unsafe else .safe)

def readInductive? (fuel : Nat) (objects : Objects) (naturals : Naturals) (block : Address)
    (source : Ixon.Constant) (family : Ixon.Inductive) : Option (Const Address) := do
  let type ← readExpr? fuel objects naturals block source family.typ
  let constructors ← family.ctors.toList.zipIdx.mapM fun (ctor, index) => do
    if ctor.cidx.toNat != index then none else do
      let type ← readExpr? fuel objects naturals block source ctor.typ
      return (⟨ctor.lvls.toNat, ctor.params.toNat, ctor.fields.toNat, type,
        if ctor.isUnsafe then .unsafe else .safe⟩ : Ctor Address)
  return .induct family.lvls.toNat family.params.toNat family.indices.toNat
    type constructors (if family.isUnsafe then .unsafe else .safe)

def readMutualMember? (fuel : Nat) (objects : Objects) (naturals : Naturals) (block : Address)
    (source : Ixon.Constant) : Ixon.MutConst → Option (Const Address)
  | .defn definition => readDefinition? fuel objects naturals block source definition
  | .recr recursor => readRecursor? fuel objects naturals block source recursor
  | .indc family => readInductive? fuel objects naturals block source family

def readBlock? (fuel : Nat) (objects : Objects) (naturals : Naturals) (block : Address)
    (source : Ixon.Constant) : Option (Block Address) :=
  match source.info with
  | .defn definition => do return ⟨[← readDefinition? fuel objects naturals block source definition]⟩
  | .recr recursor => do return ⟨[← readRecursor? fuel objects naturals block source recursor]⟩
  | .axio declaration => do
    let type ← readExpr? fuel objects naturals block source declaration.typ
    return ⟨[.axiom declaration.lvls.toNat type (if declaration.isUnsafe then .unsafe else .safe)]⟩
  | .quot quotient => do
    let type ← readExpr? fuel objects naturals block source quotient.typ
    return ⟨[.quot (readQuotKind quotient.kind) quotient.lvls.toNat type]⟩
  | .muts members => do
    return ⟨← members.toList.mapM (readMutualMember? fuel objects naturals block source)⟩
  | _ => none

def isProjection : Ixon.ConstantInfo → Bool
  | .iPrj _ | .rPrj _ | .dPrj _ | .cPrj _ => true
  | _ => false

def readBlocks? (fuel : Nat) (objects : Objects) (naturals : Naturals) :
    Objects → Option (List (Address × Block Address))
  | [] => some []
  | (address, source) :: rest => do
    if isProjection source.info then
      let _ ← resolveReference? objects address
      readBlocks? fuel objects naturals rest
    else
      let block ← readBlock? fuel objects naturals address source
      let rest ← readBlocks? fuel objects naturals rest
      return (address, block) :: rest

def readStore? (fuel : Nat) (objects : Objects) (naturals : Naturals := []) : Option (Store Address) := do
  if (objects.map Prod.fst).Nodup then
    let blocks ← readBlocks? fuel objects naturals objects
    if h : (blocks.map Prod.fst).Nodup then
      return ⟨blocks.map Prod.fst, h, lookup blocks, lookup_isSome blocks⟩
    else none
  else none

def readProofInput? (fuel : Nat) (objects : Objects) (target : Address)
    (naturals : Naturals := []) :
    Option (ProofInput Address) := do
  let store ← readStore? fuel objects naturals
  let reference ← resolveReference? objects target
  let declaration ← store.lookup reference
  if declaration.uvars ≤ fuel then
    return ⟨store, declaration.uvars, .const reference (VLevel.params declaration.uvars),
      declaration.type⟩
  else none

end Ix.Certified
