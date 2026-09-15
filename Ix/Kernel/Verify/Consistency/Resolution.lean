/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Environment
import Ix.Kernel.Verify.Consistency.SourceAgreement
import Ix.Kernel.Verify.Consistency.Literals
import Ix.Certified.Ixon
import Ix.Compile.Verify.QSort

/-!
# Canonical model references derived from the source environment

`Ixon.Env.resolve` maps a source address to its model coordinate using only
the constants stored in the source environment, following the certified
adapter's convention (`Ix.Certified.resolveReference?`, proved to agree below):

* a standalone constant (definition, recursor, axiom, quotient) is a
  one-member block at its own address, `.member addr 0`, exactly as the
  production loader registers it (`insertStandaloneEntries`) and as the
  certified reader stores it (`Ix.Certified.readBlocks?`);
* a projection record `⟨idx, block⟩` resolves to `.member block idx` when the
  Muts constant at `block` stores a member of the matching kind at `idx`, and a
  constructor projection resolves to `.ctor block idx cidx` when that
  constructor exists;
* Muts blocks themselves, absent addresses, and records that do not
  materialize resolve to nothing.

The map is injective on standalone coordinates and, whenever every stored
projection record sits at its generated address (`ProjectionsCanonical`), on
its whole domain. Under the finite source contract `SourceMaterializes`, the
standalone items enumerated by `buildAnonWork` are exactly the addresses with
a standalone coordinate, and the generated projection addresses of a stored
block resolve to their member and constructor coordinates when the block's
projection records are stored (`ProjectionsStored`). Source prediction of a
standalone declaration determines its coordinate, so the static bindings
`StandaloneModelBinding` and `PrimitiveNatBinding` are derived from the
source, and the environment theorems are restated with `β := Address` and
`resolve := env.resolve`: their `resolved`, `fresh`, and `installed` premises
become proofs.

The compiler's catalog (`Ix.Compile.Verify.Catalog`) keeps `resolve` as an
explicit input. The intended agreement, not proved here because that module
currently reaches the retired named specification, is that under
`Catalog.WF (Catalog.ofEnv env env.resolve members)` every stored projection
record is resolved by `env.resolve` to the coordinate its payload names:
`ConstantProjectionWF` is exactly the member-kind check performed by
`Ixon.Env.resolveInfo`.
-/

namespace Ixon

namespace ConstantInfo

/-- Records the production driver checks as their own single-member block. -/
def Standalone : ConstantInfo → Prop
  | .defn _ | .recr _ | .axio _ | .quot _ => True
  | _ => False

/-- Records that project one member or constructor of a Muts block. -/
def Projection : ConstantInfo → Prop
  | .dPrj _ | .rPrj _ | .iPrj _ | .cPrj _ => True
  | _ => False

/-- A record is never both standalone and a projection. -/
theorem not_projection_of_standalone {info : ConstantInfo} (standalone : info.Standalone) :
    ¬ info.Projection := by
  cases info <;> simp_all [Standalone, Projection]

end ConstantInfo

namespace Env

open Ix.Theory

/-- The member stored at `index` of the Muts constant at `block`. -/
def mutMember? (env : Env) (block : Address) (index : UInt64) : Option MutConst :=
  match env.getConst? block with
  | none => none
  | some source =>
    match source.info with
    | .muts members => members[index.toNat]?
    | _ => none

/-- The coordinate of a record stored at `addr`. Projection payloads must name
a member of the matching kind, as in `Ix.Certified.resolveReference?`. -/
def resolveInfo (env : Env) (addr : Address) : ConstantInfo → Option (ConstRef Address)
  | .defn _ | .recr _ | .axio _ | .quot _ => some (.member addr 0)
  | .dPrj projection =>
    match env.mutMember? projection.block projection.idx with
    | some (.defn _) => some (.member projection.block projection.idx.toNat)
    | _ => none
  | .rPrj projection =>
    match env.mutMember? projection.block projection.idx with
    | some (.recr _) => some (.member projection.block projection.idx.toNat)
    | _ => none
  | .iPrj projection =>
    match env.mutMember? projection.block projection.idx with
    | some (.indc _) => some (.member projection.block projection.idx.toNat)
    | _ => none
  | .cPrj projection =>
    match env.mutMember? projection.block projection.idx with
    | some (.indc family) =>
      match family.ctors[projection.cidx.toNat]? with
      | some _ => some (.ctor projection.block projection.idx.toNat projection.cidx.toNat)
      | none => none
    | _ => none
  | .muts _ => none

/-- The canonical model reference of a source address: a pure function of the
stored constants. Standalones are one-member blocks at their own address;
projections resolve through their payload into the owning Muts block. -/
def resolve (env : Env) (addr : Address) : Option (ConstRef Address) :=
  match env.getConst? addr with
  | none => none
  | some source => env.resolveInfo addr source.info

/-- The stored records that determine a coordinate. -/
inductive Locates (env : Env) : Address → ConstRef Address → Prop
  | standalone {addr : Address} {constant : Constant} :
      env.getConst? addr = some constant → constant.info.Standalone →
      Locates env addr (.member addr 0)
  | defn {addr : Address} {constant : Constant} {projection : DefinitionProj}
      {definition : Definition} :
      env.getConst? addr = some constant → constant.info = .dPrj projection →
      env.mutMember? projection.block projection.idx = some (.defn definition) →
      Locates env addr (.member projection.block projection.idx.toNat)
  | recr {addr : Address} {constant : Constant} {projection : RecursorProj}
      {recursor : Recursor} :
      env.getConst? addr = some constant → constant.info = .rPrj projection →
      env.mutMember? projection.block projection.idx = some (.recr recursor) →
      Locates env addr (.member projection.block projection.idx.toNat)
  | indc {addr : Address} {constant : Constant} {projection : InductiveProj}
      {family : Inductive} :
      env.getConst? addr = some constant → constant.info = .iPrj projection →
      env.mutMember? projection.block projection.idx = some (.indc family) →
      Locates env addr (.member projection.block projection.idx.toNat)
  | ctor {addr : Address} {constant : Constant} {projection : ConstructorProj}
      {family : Inductive} {constructor : Constructor} :
      env.getConst? addr = some constant → constant.info = .cPrj projection →
      env.mutMember? projection.block projection.idx = some (.indc family) →
      family.ctors[projection.cidx.toNat]? = some constructor →
      Locates env addr (.ctor projection.block projection.idx.toNat projection.cidx.toNat)

/-- Resolution reads the stored record. -/
theorem resolve_stored {env : Env} {addr : Address} {constant : Constant}
    (stored : env.getConst? addr = some constant) :
    env.resolve addr = env.resolveInfo addr constant.info := by
  unfold resolve
  rw [stored]

/-- Resolution is exactly location by stored records. -/
theorem resolve_eq_some_iff {env : Env} {addr : Address} {ref : ConstRef Address} :
    env.resolve addr = some ref ↔ env.Locates addr ref := by
  constructor
  · intro resolved
    obtain ⟨constant, stored, resolved⟩ : ∃ constant, env.getConst? addr = some constant ∧
        env.resolveInfo addr constant.info = some ref := by
      unfold resolve at resolved
      revert resolved
      cases stored : env.getConst? addr with
      | none => intro resolved; cases resolved
      | some constant => intro resolved; exact ⟨constant, rfl, resolved⟩
    revert resolved
    cases info : constant.info with
    | defn _ | recr _ | axio _ | quot _ =>
      simp only [resolveInfo]
      intro resolved
      cases resolved
      exact .standalone stored (by rw [info]; trivial)
    | muts _ => simp [resolveInfo]
    | dPrj projection =>
      simp only [resolveInfo]
      cases member : env.mutMember? projection.block projection.idx with
      | none => simp
      | some found =>
        cases found with
        | defn definition =>
          intro resolved
          cases resolved
          exact .defn stored info member
        | indc _ | recr _ => simp
    | rPrj projection =>
      simp only [resolveInfo]
      cases member : env.mutMember? projection.block projection.idx with
      | none => simp
      | some found =>
        cases found with
        | recr recursor =>
          intro resolved
          cases resolved
          exact .recr stored info member
        | indc _ | defn _ => simp
    | iPrj projection =>
      simp only [resolveInfo]
      cases member : env.mutMember? projection.block projection.idx with
      | none => simp
      | some found =>
        cases found with
        | indc family =>
          intro resolved
          cases resolved
          exact .indc stored info member
        | recr _ | defn _ => simp
    | cPrj projection =>
      simp only [resolveInfo]
      cases member : env.mutMember? projection.block projection.idx with
      | none => simp
      | some found =>
        cases found with
        | indc family =>
          dsimp only
          intro resolved
          split at resolved
          · rename_i found constructor
            cases resolved
            exact .ctor stored info member constructor
          · cases resolved
        | recr _ | defn _ => simp
  · intro located
    cases located with
    | @standalone constant stored standalone =>
      rw [resolve_stored stored]
      cases info : constant.info <;> simp_all [resolveInfo, ConstantInfo.Standalone]
    | defn stored info member => simp [resolve, resolveInfo, stored, info, member]
    | recr stored info member => simp [resolve, resolveInfo, stored, info, member]
    | indc stored info member => simp [resolve, resolveInfo, stored, info, member]
    | ctor stored info member constructor =>
      simp [resolve, resolveInfo, stored, info, member, constructor]

/-- A stored standalone record resolves to its own one-member block. -/
theorem resolve_standalone {env : Env} {addr : Address} {constant : Constant}
    (stored : env.getConst? addr = some constant) (standalone : constant.info.Standalone) :
    env.resolve addr = some (.member addr 0) :=
  resolve_eq_some_iff.mpr (.standalone stored standalone)

/-- Only Muts blocks have members. -/
theorem mutMember?_some {env : Env} {block : Address} {index : UInt64} {member : MutConst}
    (found : env.mutMember? block index = some member) :
    ∃ constant members, env.getConst? block = some constant ∧
      constant.info = .muts members ∧ members[index.toNat]? = some member := by
  obtain ⟨constant, stored, found⟩ : ∃ constant, env.getConst? block = some constant ∧
      (match constant.info with
        | .muts members => members[index.toNat]?
        | _ => none) = some member := by
    unfold mutMember? at found
    revert found
    cases stored : env.getConst? block with
    | none => intro found; cases found
    | some constant => intro found; exact ⟨constant, rfl, found⟩
  revert found
  cases info : constant.info with
  | muts members => intro found; exact ⟨constant, members, stored, info, found⟩
  | _ => simp

/-- Every located address is stored. -/
theorem Locates.stored {env : Env} {addr : Address} {ref : ConstRef Address}
    (located : env.Locates addr ref) : ∃ constant, env.getConst? addr = some constant := by
  cases located <;> exact ⟨_, by assumption⟩

/-- The block of every coordinate is stored. -/
theorem Locates.block_stored {env : Env} {addr : Address} {ref : ConstRef Address}
    (located : env.Locates addr ref) : ∃ constant, env.getConst? ref.block = some constant := by
  cases located with
  | standalone stored _ => exact ⟨_, stored⟩
  | defn _ _ member | recr _ _ member | indc _ _ member | ctor _ _ member _ =>
    obtain ⟨constant, _, stored, _, _⟩ := mutMember?_some member
    exact ⟨constant, stored⟩

/-- The standalone coordinate of an address is reached only by its own
standalone record: a projection cannot name a standalone as its block. -/
theorem resolve_member_self_iff {env : Env} {addr : Address} :
    env.resolve addr = some (.member addr 0) ↔
      ∃ constant, env.getConst? addr = some constant ∧ constant.info.Standalone := by
  constructor
  · intro resolved
    generalize target : (ConstRef.member addr 0 : ConstRef Address) = ref at resolved
    cases resolve_eq_some_iff.mp resolved with
    | standalone stored standalone => exact ⟨_, stored, standalone⟩
    | defn stored info member | recr stored info member | indc stored info member =>
      obtain ⟨blockConstant, members, blockStored, blockInfo, _⟩ := mutMember?_some member
      rw [← (ConstRef.member.inj target).1] at blockStored
      cases Option.some.inj (stored.symm.trans blockStored)
      rw [info] at blockInfo
      cases blockInfo
    | ctor => cases target
  · rintro ⟨constant, stored, standalone⟩
    exact resolve_standalone stored standalone

/-- The projection record that resolves to a reference, determined by the
member found at that reference. -/
def recordOf (env : Env) : ConstRef Address → Option ConstantInfo
  | .member block index =>
    match env.mutMember? block index.toUInt64 with
    | some (.defn _) => some (.dPrj ⟨index.toUInt64, block⟩)
    | some (.recr _) => some (.rPrj ⟨index.toUInt64, block⟩)
    | some (.indc _) => some (.iPrj ⟨index.toUInt64, block⟩)
    | none => none
  | .ctor block index cidx =>
    match env.mutMember? block index.toUInt64 with
    | some (.indc family) =>
      match family.ctors[cidx.toUInt64.toNat]? with
      | some _ => some (.cPrj ⟨index.toUInt64, cidx.toUInt64, block⟩)
      | none => none
    | _ => none

/-- A located address stores either the standalone record of its own block or
the unique projection record of its coordinate. -/
theorem Locates.standalone_or_record {env : Env} {addr : Address} {ref : ConstRef Address}
    (located : env.Locates addr ref) :
    (ref = .member addr 0 ∧ ∃ constant, env.getConst? addr = some constant ∧
        constant.info.Standalone) ∨
      (∃ constant, env.getConst? addr = some constant ∧ constant.info.Projection ∧
        env.recordOf ref = some constant.info) := by
  cases located with
  | standalone stored standalone => exact .inl ⟨rfl, _, stored, standalone⟩
  | @defn constant projection _ stored info member =>
    refine .inr ⟨constant, stored, by rw [info]; trivial, ?_⟩
    simp only [recordOf, Nat.toUInt64_eq, UInt64.ofNat_toNat, member, info]
  | @recr constant projection _ stored info member =>
    refine .inr ⟨constant, stored, by rw [info]; trivial, ?_⟩
    simp only [recordOf, Nat.toUInt64_eq, UInt64.ofNat_toNat, member, info]
  | @indc constant projection _ stored info member =>
    refine .inr ⟨constant, stored, by rw [info]; trivial, ?_⟩
    simp only [recordOf, Nat.toUInt64_eq, UInt64.ofNat_toNat, member, info]
  | @ctor constant projection _ _ stored info member constructor =>
    refine .inr ⟨constant, stored, by rw [info]; trivial, ?_⟩
    simp only [recordOf, Nat.toUInt64_eq, UInt64.ofNat_toNat, member, constructor, info]

/-- A record for a member coordinate needs a member at that coordinate. -/
theorem recordOf_member_some {env : Env} {block : Address} {index : Nat} {record : ConstantInfo}
    (found : env.recordOf (.member block index) = some record) :
    ∃ member, env.mutMember? block index.toUInt64 = some member := by
  simp only [recordOf] at found
  revert found
  cases env.mutMember? block index.toUInt64 with
  | none => intro found; cases found
  | some member => intro _; exact ⟨member, rfl⟩

/-- A standalone record cannot own members. -/
theorem Standalone.no_member {env : Env} {addr : Address} {constant : Constant}
    {index : UInt64} {member : MutConst}
    (stored : env.getConst? addr = some constant) (standalone : constant.info.Standalone)
    (found : env.mutMember? addr index = some member) : False := by
  obtain ⟨blockConstant, members, blockStored, blockInfo, _⟩ := mutMember?_some found
  cases Option.some.inj (stored.symm.trans blockStored)
  rw [blockInfo] at standalone
  exact standalone

/-- Two addresses with one coordinate are equal or store identical projection records. -/
theorem Locates.same_ref {env : Env} {addr addr' : Address} {ref : ConstRef Address}
    (left : env.Locates addr ref) (right : env.Locates addr' ref) :
    addr = addr' ∨ ∃ constant constant', env.getConst? addr = some constant ∧
      env.getConst? addr' = some constant' ∧ constant.info.Projection ∧
      constant.info = constant'.info := by
  rcases left.standalone_or_record with ⟨same, constant, stored, standalone⟩ |
      ⟨constant, stored, projection, record⟩
  · subst same
    rcases right.standalone_or_record with ⟨same', _⟩ | ⟨_, _, _, record'⟩
    · exact .inl (ConstRef.member.inj same').1
    · obtain ⟨member, found⟩ := recordOf_member_some record'
      exact (Standalone.no_member stored standalone found).elim
  · rcases right.standalone_or_record with ⟨same', constant', stored', standalone'⟩ |
        ⟨constant', stored', projection', record'⟩
    · subst same'
      obtain ⟨member, found⟩ := recordOf_member_some record
      exact (Standalone.no_member stored' standalone' found).elim
    · exact .inr ⟨constant, constant', stored, stored', projection,
        Option.some.inj (record.symm.trans record')⟩

/-- Resolution is injective on standalone coordinates. -/
theorem resolve_standalone_injective {env : Env} {addr addr' : Address}
    (left : env.resolve addr = some (.member addr 0))
    (right : env.resolve addr' = some (.member addr 0)) : addr' = addr := by
  rcases Locates.same_ref (resolve_eq_some_iff.mp left) (resolve_eq_some_iff.mp right) with
    same | ⟨constant, _, stored, _, projection, _⟩
  · exact same.symm
  · obtain ⟨found, foundStored, standalone⟩ := resolve_member_self_iff.mp left
    cases Option.some.inj (stored.symm.trans foundStored)
    exact absurd projection (ConstantInfo.not_projection_of_standalone standalone)

end Env

end Ixon

namespace Ixon.LazyConstant

/-- Materialization that surfaces no error also succeeds silently. -/
theorem get?_of_get {lazy : LazyConstant} {constant : Constant} (materialized : lazy.get = .ok constant) :
    lazy.get? = some constant := by
  unfold get at materialized
  unfold get?
  cases cache : lazy.cache with
  | none =>
    rw [cache] at materialized
    simp only [materialized]
    rfl
  | some cached =>
    rw [cache] at materialized
    cases materialized
    rfl

end Ixon.LazyConstant

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe v

private instance : LawfulBEq ByteArray where
  eq_of_beq {left right} h := by
    cases left
    cases right
    exact congrArg ByteArray.mk (eq_of_beq h)
  rfl {bytes} := beq_self_eq_true bytes.data

private instance : LawfulBEq Address where
  eq_of_beq {left right} h := by
    cases left
    cases right
    exact congrArg Address.mk (eq_of_beq h)
  rfl {addr} := by
    cases addr
    exact beq_self_eq_true (α := ByteArray) _

private instance : LawfulHashable Address where
  hash_eq left right h := by rw [eq_of_beq h]

/-! ### Stored records -/

/-- A materialized constant comes from a stored lazy entry. -/
theorem lazy_of_getConst? {env : Ixon.Env} {addr : Address} {constant : Ixon.Constant}
    (stored : env.getConst? addr = some constant) :
    ∃ lazy, env.consts[addr]? = some lazy ∧ lazy.get? = some constant := by
  simp only [Ixon.Env.getConst?, Std.HashMap.get?_eq_getElem?] at stored
  revert stored
  cases lookup : env.consts[addr]? with
  | none => intro stored; cases stored
  | some lazy => intro stored; exact ⟨lazy, rfl, stored⟩

/-- A stored lazy entry that materializes is the source constant. -/
theorem getConst?_of_lazy {env : Ixon.Env} {addr : Address} {lazy : Ixon.LazyConstant}
    {constant : Ixon.Constant} (lookup : env.consts[addr]? = some lazy)
    (materialized : lazy.get = .ok constant) : env.getConst? addr = some constant := by
  simp only [Ixon.Env.getConst?, Std.HashMap.get?_eq_getElem?, lookup, Option.bind_some]
  exact Ixon.LazyConstant.get?_of_get materialized

/-- Every stored constant is a source key. -/
theorem mem_keys_of_getConst? {env : Ixon.Env} {addr : Address} {constant : Ixon.Constant}
    (stored : env.getConst? addr = some constant) : addr ∈ env.consts.keys := by
  obtain ⟨lazy, lookup, _⟩ := lazy_of_getConst? stored
  rw [Std.HashMap.mem_keys, ← Std.HashMap.isSome_getElem?_iff_mem, lookup]
  rfl

/-- Every resolved address is a source key. -/
theorem resolve_mem_keys {env : Ixon.Env} {addr : Address} {ref : ConstRef Address}
    (resolved : env.resolve addr = some ref) : addr ∈ env.consts.keys := by
  obtain ⟨constant, stored⟩ := (Ixon.Env.resolve_eq_some_iff.mp resolved).stored
  exact mem_keys_of_getConst? stored

/-- The block of every coordinate is a source key. -/
theorem resolve_block_mem_keys {env : Ixon.Env} {addr : Address} {ref : ConstRef Address}
    (resolved : env.resolve addr = some ref) : ref.block ∈ env.consts.keys := by
  obtain ⟨constant, stored⟩ := (Ixon.Env.resolve_eq_some_iff.mp resolved).block_stored
  exact mem_keys_of_getConst? stored

/-! ### Agreement with the certified adapter -/

/-- The certified adapter's coordinate function is the canonical map whenever
its object list agrees with the environment's stored constants. -/
theorem certified_resolveReference?_eq {env : Ixon.Env} {objects : Ix.Certified.Objects}
    (agree : ∀ addr, Ix.Certified.lookup objects addr = env.getConst? addr) (addr : Address) :
    Ix.Certified.resolveReference? objects addr = env.resolve addr := by
  have member : ∀ block index,
      Ix.Certified.mutMember? objects block index = env.mutMember? block index := by
    intro block index
    simp only [Ix.Certified.mutMember?, Ixon.Env.mutMember?, agree, Option.bind_eq_bind]
    cases env.getConst? block with
    | none => rfl
    | some source =>
      simp only [Option.bind_some]
      cases source.info <;> rfl
  simp only [Ix.Certified.resolveReference?, Ixon.Env.resolve, agree, Option.bind_eq_bind]
  cases env.getConst? addr with
  | none => rfl
  | some source =>
    simp only [Option.bind_some]
    cases source.info with
    | defn _ | recr _ | axio _ | quot _ | muts _ => rfl
    | dPrj projection =>
      simp only [Ixon.Env.resolveInfo, member]
      cases env.mutMember? projection.block projection.idx with
      | none => rfl
      | some found => cases found <;> rfl
    | rPrj projection =>
      simp only [Ixon.Env.resolveInfo, member]
      cases env.mutMember? projection.block projection.idx with
      | none => rfl
      | some found => cases found <;> rfl
    | iPrj projection =>
      simp only [Ixon.Env.resolveInfo, member]
      cases env.mutMember? projection.block projection.idx with
      | none => rfl
      | some found => cases found <;> rfl
    | cPrj projection =>
      simp only [Ixon.Env.resolveInfo, member]
      cases env.mutMember? projection.block projection.idx with
      | none => rfl
      | some found =>
        cases found with
        | indc family =>
          simp only [Option.bind_some]
          cases family.ctors[projection.cidx.toNat]? <;> rfl
        | defn _ | recr _ => rfl

/-! ### Standalone classification -/

/-- The loader's block routing is absent exactly at standalone records. -/
theorem ingressBlockAddr?_eq_none_iff {addr : Address} {info : Ixon.ConstantInfo} :
    ingressBlockAddr? addr info = none ↔ info.Standalone := by
  cases info <;> simp [ingressBlockAddr?, Ixon.ConstantInfo.Standalone]

/-- The driver emits a standalone item exactly at standalone records. -/
theorem ofConstantInfo_standalone_iff {addr : Address} {info : Ixon.ConstantInfo} :
    AnonWorkItem.ofConstantInfo addr info = some (.standalone addr) ↔ info.Standalone := by
  cases info with
  | muts members =>
    simp only [AnonWorkItem.ofConstantInfo, Ixon.ConstantInfo.Standalone, iff_false]
    split <;> simp
  | _ => simp [AnonWorkItem.ofConstantInfo, Ixon.ConstantInfo.Standalone]

/-- The verified loader returns the stored constant. -/
theorem getConst?_of_verified {env : Ixon.Env} {addr : Address} {constant : Ixon.Constant}
    (verified : getConstVerified env addr true = .ok (some constant)) :
    env.getConst? addr = some constant := by
  unfold getConstVerified at verified
  revert verified
  cases lookup : env.consts[addr]? with
  | none => intro verified; cases verified
  | some lazy =>
    simp only [Bool.true_or, if_true]
    by_cases mismatch : (Address.blake3 lazy.rawBytes != addr) = true
    · simp only [mismatch, if_true]
      intro verified
      cases verified
    · simp only [mismatch, Bool.false_eq_true, if_false]
      cases materialized : lazy.get with
      | error err => intro verified; cases verified
      | ok found =>
        intro verified
        simp only [Pure.pure, Except.pure, Except.ok.injEq,
          Option.some.injEq] at verified
        subst verified
        exact getConst?_of_lazy lookup materialized

/-- A predicted standalone declaration has the canonical standalone coordinate. -/
theorem resolve_of_predictStandalone? {env : Ixon.Env} {addr : Address} {expected : KConst .anon}
    (predicted : predictStandalone? env addr = .ok (some expected)) :
    env.resolve addr = some (.member addr 0) := by
  obtain ⟨constant, verified, standalone, _⟩ := predictStandalone?_some predicted
  exact Ixon.Env.resolve_standalone (getConst?_of_verified verified)
    (ingressBlockAddr?_eq_none_iff.mp standalone)

/-! ### Injectivity -/

/-- The address the compiler stores and the kernel computes for a projection record. -/
def projectionAddr? : Ixon.ConstantInfo → Option Address
  | .dPrj projection => some (defnProjAddr projection.block projection.idx)
  | .rPrj projection => some (recrProjAddr projection.block projection.idx)
  | .iPrj projection => some (indcProjAddr projection.block projection.idx)
  | .cPrj projection => some (ctorProjAddr projection.block projection.idx projection.cidx)
  | _ => none

/-- Every stored projection record sits at its generated address, as the
compiler stores it. -/
def ProjectionsCanonical (env : Ixon.Env) : Prop :=
  ∀ ⦃addr : Address⦄ ⦃constant : Ixon.Constant⦄ ⦃generated : Address⦄,
    env.getConst? addr = some constant → projectionAddr? constant.info = some generated →
    addr = generated

theorem projectionAddr?_of_projection {info : Ixon.ConstantInfo} (projection : info.Projection) :
    ∃ generated, projectionAddr? info = some generated := by
  cases info <;> simp_all [projectionAddr?, Ixon.ConstantInfo.Projection]

/-- With canonical projection addresses, resolution is injective on its domain. -/
theorem resolve_injective {env : Ixon.Env} (canonical : ProjectionsCanonical env)
    {addr addr' : Address} {ref : ConstRef Address}
    (left : env.resolve addr = some ref) (right : env.resolve addr' = some ref) : addr = addr' := by
  rcases Ixon.Env.Locates.same_ref (Ixon.Env.resolve_eq_some_iff.mp left)
      (Ixon.Env.resolve_eq_some_iff.mp right) with
    same | ⟨constant, constant', stored, stored', projection, same⟩
  · exact same
  · obtain ⟨generated, address⟩ := projectionAddr?_of_projection projection
    rw [canonical stored address, canonical stored' (same ▸ address)]

/-! ### Enumeration -/

/-- Every stored key materializes, with the cheap tag naming its record. This
finite source contract relates the driver's tag dispatch to the stored records. -/
def SourceMaterializes (env : Ixon.Env) : Prop :=
  ∀ ⦃addr : Address⦄ ⦃lazy : Ixon.LazyConstant⦄, env.consts[addr]? = some lazy →
    ∃ constant, lazy.get = .ok constant ∧ lazy.peekTag = .ok (constantInfoTag constant.info)

/-- Finite preflight for `SourceMaterializes`. -/
def sourceMaterializesCheck (env : Ixon.Env) : Bool :=
  env.consts.toList.all fun (_, lazy) =>
    match lazy.get, lazy.peekTag with
    | .ok constant, .ok tag => decide (tag = constantInfoTag constant.info)
    | _, _ => false

theorem SourceMaterializes.ofCheck {env : Ixon.Env} (checked : sourceMaterializesCheck env = true) :
    SourceMaterializes env := by
  intro addr lazy stored
  have row := List.all_eq_true.mp checked (addr, lazy)
    (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr stored)
  dsimp only at row
  revert row
  cases materialized : lazy.get with
  | error err => simp
  | ok constant =>
    cases tag : lazy.peekTag with
    | error err => simp
    | ok found =>
      simp only [decide_eq_true_eq]
      intro row
      exact ⟨constant, rfl, by rw [row]⟩

/-- A materializing standalone key is classified as its own standalone item. -/
theorem buildAnonWorkItem_of_standalone {env : Ixon.Env} {addr : Address}
    {lazy : Ixon.LazyConstant} {constant : Ixon.Constant}
    (materializes : SourceMaterializes env) (lookup : env.consts[addr]? = some lazy)
    (materialized : lazy.get = .ok constant) (standalone : constant.info.Standalone) :
    buildAnonWorkItem env addr = .ok (some (.standalone addr)) := by
  obtain ⟨found, foundMaterialized, tag⟩ := materializes lookup
  cases Except.ok.inj (materialized.symm.trans foundMaterialized)
  unfold buildAnonWorkItem
  simp only [Std.HashMap.get?_eq_getElem?, lookup, tag]
  cases info : constant.info <;> simp_all [constantInfoTag, Ixon.ConstantInfo.Standalone,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A standalone item is emitted only at a materializing standalone key, which
then has the canonical standalone coordinate. -/
theorem buildAnonWorkItem_standalone {env : Ixon.Env} {addr item : Address}
    (materializes : SourceMaterializes env)
    (built : buildAnonWorkItem env addr = .ok (some (.standalone item))) :
    item = addr ∧ env.resolve addr = some (.member addr 0) := by
  unfold buildAnonWorkItem at built
  revert built
  cases lookup : env.consts.get? addr with
  | none => intro built; cases built
  | some lazy =>
    obtain ⟨constant, materialized, tag⟩ := materializes lookup
    have stored := getConst?_of_lazy lookup materialized
    simp only [tag]
    cases info : constant.info with
    | defn _ | recr _ | axio _ | quot _ =>
      simp only [constantInfoTag, Bind.bind, Except.bind, Pure.pure, Except.pure,
        Except.ok.injEq, Option.some.injEq, AnonWorkItem.standalone.injEq]
      intro same
      exact ⟨same.symm, Ixon.Env.resolve_standalone stored (by rw [info]; trivial)⟩
    | iPrj _ | cPrj _ | rPrj _ | dPrj _ =>
      simp [constantInfoTag, Bind.bind, Except.bind, Pure.pure, Except.pure]
    | muts members =>
      simp only [constantInfoTag, materialized, info, AnonWorkItem.ofConstantInfo, Bind.bind,
        Except.bind, Pure.pure, Except.pure]
      split <;> simp

private theorem filterMapM_ok_mem {α β : Type} {f : α → Except IngressErr (Option β)} :
    ∀ {xs : List α} {ys : List β}, xs.filterMapM f = .ok ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok (some y)
  | [], ys, run, y, mem => by
      simp only [List.filterMapM_nil] at run
      cases run
      cases mem
  | x :: xs, ys, run, y, mem => by
      rw [List.filterMapM_cons] at run
      revert run
      cases step : f x with
      | error err => intro run; cases run
      | ok optional =>
        cases optional with
        | none =>
          intro run
          obtain ⟨x', mem', run'⟩ := filterMapM_ok_mem run y mem
          exact ⟨x', List.mem_cons_of_mem _ mem', run'⟩
        | some b =>
          simp only [Bind.bind, Except.bind]
          revert mem
          cases rest : xs.filterMapM f with
          | error err => intro mem run; cases run
          | ok rest' =>
            intro mem run
            cases run
            rcases List.mem_cons.mp mem with rfl | mem'
            · exact ⟨x, List.mem_cons_self .., step⟩
            · obtain ⟨x', mem', run'⟩ := filterMapM_ok_mem rest y mem'
              exact ⟨x', List.mem_cons_of_mem _ mem', run'⟩

private theorem filterMapM_ok_of_mem {α β : Type} {f : α → Except IngressErr (Option β)} :
    ∀ {xs : List α} {ys : List β}, xs.filterMapM f = .ok ys → ∀ x ∈ xs, ∀ y, f x = .ok (some y) →
      y ∈ ys
  | [], _, _, _, mem, _, _ => by cases mem
  | x :: xs, ys, run, x', mem, y, step => by
      rw [List.filterMapM_cons] at run
      revert run
      rcases List.mem_cons.mp mem with rfl | mem'
      · rw [step]
        simp only [Bind.bind, Except.bind]
        cases rest : xs.filterMapM f with
        | error err => intro run; cases run
        | ok rest' =>
          intro run
          cases run
          exact List.mem_cons_self ..
      · cases first : f x with
        | error err => intro run; cases run
        | ok optional =>
          cases optional with
          | none =>
            intro run
            exact filterMapM_ok_of_mem run x' mem' y step
          | some b =>
            simp only [Bind.bind, Except.bind]
            cases rest : xs.filterMapM f with
            | error err => intro run; cases run
            | ok rest' =>
              intro run
              cases run
              exact List.mem_cons_of_mem _ (filterMapM_ok_of_mem rest x' mem' y step)

/-- The production enumeration is the list enumeration in key order. -/
private theorem buildAnonWork_list {env : Ixon.Env} {work : Array AnonWorkItem}
    (enumerated : buildAnonWork env = .ok work) :
    (orderedAnonConstAddrs env).toList.filterMapM (buildAnonWorkItem env) = .ok work.toList := by
  unfold buildAnonWork at enumerated
  rw [← Array.toArray_toList (xs := orderedAnonConstAddrs env), List.filterMapM_toArray]
    at enumerated
  revert enumerated
  cases run : (orderedAnonConstAddrs env).toList.filterMapM (buildAnonWorkItem env) with
  | error err => intro enumerated; cases enumerated
  | ok items =>
    intro enumerated
    cases enumerated
    rfl

/-- A standalone item of the enumerated work has the canonical standalone coordinate. -/
theorem resolve_of_work_standalone {env : Ixon.Env} {work : Array AnonWorkItem} {addr : Address}
    (materializes : SourceMaterializes env) (enumerated : buildAnonWork env = .ok work)
    (listed : AnonWorkItem.standalone addr ∈ work) :
    env.resolve addr = some (.member addr 0) := by
  obtain ⟨source, _, built⟩ := filterMapM_ok_mem (buildAnonWork_list enumerated) _
    (Array.mem_def.mp listed)
  obtain ⟨same, resolved⟩ := buildAnonWorkItem_standalone materializes built
  subst same
  exact resolved

/-- Every source key is visited by the ordered enumeration. -/
theorem mem_orderedAnonConstAddrs {env : Ixon.Env} {addr : Address} :
    addr ∈ orderedAnonConstAddrs env ↔ addr ∈ env.consts.keys := by
  rw [orderedAnonConstAddrs, (Ix.Compile.Verify.QSort.qsort_perm _ _ _ _).mem_iff,
    List.mem_toArray]

/-- An address with the canonical standalone coordinate is enumerated as a standalone item. -/
theorem work_standalone_of_resolve {env : Ixon.Env} {work : Array AnonWorkItem} {addr : Address}
    (materializes : SourceMaterializes env) (enumerated : buildAnonWork env = .ok work)
    (resolved : env.resolve addr = some (.member addr 0)) :
    AnonWorkItem.standalone addr ∈ work := by
  obtain ⟨constant, stored, standalone⟩ := Ixon.Env.resolve_member_self_iff.mp resolved
  obtain ⟨lazy, lookup, materialized⟩ := lazy_of_getConst? stored
  obtain ⟨found, foundMaterialized, _⟩ := materializes lookup
  have same : found = constant :=
    Option.some.inj ((Ixon.LazyConstant.get?_of_get foundMaterialized).symm.trans materialized)
  subst same
  have ordered : addr ∈ (orderedAnonConstAddrs env).toList := by
    rw [← Array.mem_def, mem_orderedAnonConstAddrs]
    exact mem_keys_of_getConst? stored
  exact Array.mem_def.mpr (filterMapM_ok_of_mem (buildAnonWork_list enumerated) addr ordered _
    (buildAnonWorkItem_of_standalone materializes lookup foundMaterialized standalone))

/-- Under the finite source contract, the enumerated standalone items are
exactly the addresses with a standalone coordinate. -/
theorem work_standalone_iff {env : Ixon.Env} {work : Array AnonWorkItem} {addr : Address}
    (materializes : SourceMaterializes env) (enumerated : buildAnonWork env = .ok work) :
    AnonWorkItem.standalone addr ∈ work ↔ env.resolve addr = some (.member addr 0) :=
  ⟨resolve_of_work_standalone materializes enumerated,
    work_standalone_of_resolve materializes enumerated⟩

/-- A work position lists its item. -/
theorem WorkPosition.mem {work : Array AnonWorkItem} {item : AnonWorkItem}
    (position : WorkPosition work item) : item ∈ work := by
  rw [Array.mem_def, position.split]
  simp

/-! ### Block members -/

/-- The projection record generated for a block member. -/
def memberRecord (block : Address) (index : UInt64) : Ixon.MutConst → Ixon.ConstantInfo
  | .defn _ => .dPrj ⟨index, block⟩
  | .recr _ => .rPrj ⟨index, block⟩
  | .indc _ => .iPrj ⟨index, block⟩

/-- The projection address generated for a block member, the head of
`anonMemberTargets`. -/
def memberAddr (block : Address) (index : UInt64) : Ixon.MutConst → Address
  | .defn _ => defnProjAddr block index
  | .recr _ => recrProjAddr block index
  | .indc _ => indcProjAddr block index

/-- Every generated projection address of a stored block stores its own
record, as the compiler emits them. -/
structure ProjectionsStored (env : Ixon.Env) : Prop where
  member : ∀ ⦃block : Address⦄ ⦃constant : Ixon.Constant⦄ ⦃members : Array Ixon.MutConst⦄
    ⦃index : UInt64⦄ ⦃member : Ixon.MutConst⦄,
    env.getConst? block = some constant → constant.info = .muts members →
    members[index.toNat]? = some member →
    ∃ record, env.getConst? (memberAddr block index member) = some record ∧
      record.info = memberRecord block index member
  ctor : ∀ ⦃block : Address⦄ ⦃constant : Ixon.Constant⦄ ⦃members : Array Ixon.MutConst⦄
    ⦃index : UInt64⦄ ⦃family : Ixon.Inductive⦄ ⦃cidx : UInt64⦄ ⦃constructor : Ixon.Constructor⦄,
    env.getConst? block = some constant → constant.info = .muts members →
    members[index.toNat]? = some (.indc family) → family.ctors[cidx.toNat]? = some constructor →
    ∃ record, env.getConst? (ctorProjAddr block index cidx) = some record ∧
      record.info = .cPrj ⟨index, cidx, block⟩

/-- A stored block's members are found through `mutMember?`. -/
theorem mutMember?_of_stored {env : Ixon.Env} {block : Address} {constant : Ixon.Constant}
    {members : Array Ixon.MutConst} {index : UInt64} {member : Ixon.MutConst}
    (stored : env.getConst? block = some constant) (info : constant.info = .muts members)
    (found : members[index.toNat]? = some member) :
    env.mutMember? block index = some member := by
  simp [Ixon.Env.mutMember?, stored, info, found]

/-- The generated member address resolves to the member coordinate. -/
theorem resolve_memberAddr {env : Ixon.Env} (projections : ProjectionsStored env)
    {block : Address} {constant : Ixon.Constant} {members : Array Ixon.MutConst}
    {index : UInt64} {member : Ixon.MutConst}
    (stored : env.getConst? block = some constant) (info : constant.info = .muts members)
    (found : members[index.toNat]? = some member) :
    env.resolve (memberAddr block index member) = some (.member block index.toNat) := by
  obtain ⟨record, recordStored, recordInfo⟩ := projections.member stored info found
  have located := mutMember?_of_stored stored info found
  apply Ixon.Env.resolve_eq_some_iff.mpr
  cases member with
  | defn _ => exact .defn recordStored recordInfo located
  | recr _ => exact .recr recordStored recordInfo located
  | indc _ => exact .indc recordStored recordInfo located

/-- The generated constructor address resolves to the constructor coordinate. -/
theorem resolve_ctorProjAddr {env : Ixon.Env} (projections : ProjectionsStored env)
    {block : Address} {constant : Ixon.Constant} {members : Array Ixon.MutConst}
    {index : UInt64} {family : Ixon.Inductive} {cidx : UInt64} {constructor : Ixon.Constructor}
    (stored : env.getConst? block = some constant) (info : constant.info = .muts members)
    (found : members[index.toNat]? = some (.indc family))
    (ctorFound : family.ctors[cidx.toNat]? = some constructor) :
    env.resolve (ctorProjAddr block index cidx) = some (.ctor block index.toNat cidx.toNat) := by
  obtain ⟨record, recordStored, recordInfo⟩ := projections.ctor stored info found ctorFound
  exact Ixon.Env.resolve_eq_some_iff.mpr
    (.ctor recordStored recordInfo (mutMember?_of_stored stored info found) ctorFound)

private theorem toUInt64_toNat_of_lt {index : Nat} (bound : index < UInt64.size) :
    index.toUInt64.toNat = index := by
  simp [bound]

/-- Every enumerated target of a stored block resolves into that block. Index
bounds are the arithmetic run assumptions of the projection payloads. -/
theorem resolve_anonBlockTargets {env : Ixon.Env} (projections : ProjectionsStored env)
    {block : Address} {constant : Ixon.Constant} {members : Array Ixon.MutConst}
    (stored : env.getConst? block = some constant) (info : constant.info = .muts members)
    (bounded : members.size ≤ UInt64.size)
    (ctorsBounded : ∀ family, .indc family ∈ members → family.ctors.size ≤ UInt64.size) :
    ∀ target ∈ anonBlockTargets block members, ∃ ref, env.resolve target = some ref ∧
      ref.block = block := by
  intro target listed
  obtain ⟨index, inRange, listed⟩ := Array.mem_flatMap.mp listed
  have indexLt : index < members.size := Array.mem_range.mp inRange
  have indexBound : index < UInt64.size := Nat.lt_of_lt_of_le indexLt bounded
  rw [getElem!_pos members index indexLt] at listed
  have found : members[index.toUInt64.toNat]? = some members[index] := by
    rw [toUInt64_toNat_of_lt indexBound]
    exact Array.getElem?_eq_some_iff.mpr ⟨indexLt, rfl⟩
  have familyMem : ∀ family, members[index] = .indc family → Ixon.MutConst.indc family ∈ members := by
    intro family same
    rw [← same]
    exact Array.getElem_mem indexLt
  revert listed found familyMem
  cases member : members[index] with
  | defn definition =>
    intro listed found _
    simp only [anonMemberTargets, Array.mem_singleton] at listed
    subst listed
    exact ⟨_, resolve_memberAddr projections stored info found, rfl⟩
  | recr recursor =>
    intro listed found _
    simp only [anonMemberTargets, Array.mem_singleton] at listed
    subst listed
    exact ⟨_, resolve_memberAddr projections stored info found, rfl⟩
  | indc family =>
    intro listed found familyMem
    simp only [anonMemberTargets, Array.mem_append, Array.mem_singleton, Array.mem_map,
      Array.mem_range] at listed
    rcases listed with same | ⟨cidx, cidxLt, same⟩
    · subst same
      exact ⟨_, resolve_memberAddr projections stored info found, rfl⟩
    · subst same
      have cidxBound : cidx < UInt64.size :=
        Nat.lt_of_lt_of_le cidxLt (ctorsBounded family (familyMem family rfl))
      have ctorFound : family.ctors[cidx.toUInt64.toNat]? = some family.ctors[cidx] := by
        rw [toUInt64_toNat_of_lt cidxBound]
        exact Array.getElem?_eq_some_iff.mpr ⟨cidxLt, rfl⟩
      exact ⟨_, resolve_ctorProjAddr projections stored info found ctorFound, rfl⟩

/-! ### Derived static bindings -/

/-- A standalone model binding under the canonical map needs only the source
prediction, the admitted entry, and the reading of the predicted type. -/
def StandaloneModelBinding.ofSource {source : Ixon.Env} {entries : Model.Environment Address}
    {id : KId .anon} {entry : ConstantEntry Address} (constant : KConst .anon)
    (predicted : predictStandalone? source id.addr = .ok (some constant))
    (found : entries (.member id.addr 0) = some entry)
    (universes : constant.lvls.toNat = entry.universes)
    (reading : readScopedExpr? source.resolve [] constant.ty = some entry.type.erase) :
    StandaloneModelBinding source source.resolve entries id (.member id.addr 0) entry :=
  { constant, predicted, resolved := resolve_of_predictStandalone? predicted, found, universes,
    reading }

/-- The primitive `Nat` binding under the canonical map, from the stored
records locating the primitive address. -/
def PrimitiveNatBinding.ofLocated {source : Ixon.Env} {m : Mode}
    {entries : Model.Environment Address} {prims : Primitives m} {ref : ConstRef Address}
    (located : source.Locates prims.nat.addr ref) (entry : ConstantEntry Address)
    (zero succ : ConstRef Address) (level : VLevel) (found : entries ref = some entry)
    (natural : .natural zero succ ∈ entry.facts) (monomorphic : entry.universes = 0)
    (typeSort : entry.type = .sort level) (closed : level.WF 0) :
    PrimitiveNatBinding source.resolve entries prims :=
  { ref, entry, zero, succ, level, resolved := Ixon.Env.resolve_eq_some_iff.mpr located, found,
    natural, monomorphic, typeSort, closed }

/-- The primitive `Nat` address stores a standalone record. -/
def PrimitiveNatBinding.ofStandalone {source : Ixon.Env} {m : Mode}
    {entries : Model.Environment Address} {prims : Primitives m} {constant : Ixon.Constant}
    (stored : source.getConst? prims.nat.addr = some constant)
    (standalone : constant.info.Standalone) (entry : ConstantEntry Address)
    (zero succ : ConstRef Address) (level : VLevel)
    (found : entries (.member prims.nat.addr 0) = some entry)
    (natural : .natural zero succ ∈ entry.facts) (monomorphic : entry.universes = 0)
    (typeSort : entry.type = .sort level) (closed : level.WF 0) :
    PrimitiveNatBinding source.resolve entries prims :=
  .ofLocated (.standalone stored standalone) entry zero succ level found natural monomorphic
    typeSort closed

/-- The primitive `Nat` address stores an inductive projection into a block
member. -/
def PrimitiveNatBinding.ofInductive {source : Ixon.Env} {m : Mode}
    {entries : Model.Environment Address} {prims : Primitives m} {constant : Ixon.Constant}
    {projection : Ixon.InductiveProj} {family : Ixon.Inductive}
    (stored : source.getConst? prims.nat.addr = some constant)
    (info : constant.info = .iPrj projection)
    (member : source.mutMember? projection.block projection.idx = some (.indc family))
    (entry : ConstantEntry Address) (zero succ : ConstRef Address) (level : VLevel)
    (found : entries (.member projection.block projection.idx.toNat) = some entry)
    (natural : .natural zero succ ∈ entry.facts) (monomorphic : entry.universes = 0)
    (typeSort : entry.type = .sort level) (closed : level.WF 0) :
    PrimitiveNatBinding source.resolve entries prims :=
  .ofLocated (.indc stored info member) entry zero succ level found natural monomorphic
    typeSort closed

/-! ### Environment theorems with the canonical map -/

/-- A declaration's reference is its canonical standalone coordinate. -/
def AxiomSpec.Canonical (spec : AxiomSpec Address) : Prop :=
  spec.ref = .member spec.id.addr 0

def DefinitionSpec.Canonical (spec : DefinitionSpec Address) : Prop :=
  spec.ref = .member spec.input.id.addr 0

/-- Every entry of an interface is at a canonical coordinate whose address is
not among the pending declarations. -/
def CanonicalOutside (entries : Model.Environment Address) (pending : List Address) : Prop :=
  ∀ ref entry, entries ref = some entry → ∃ addr, ref = .member addr 0 ∧ addr ∉ pending

/-- Canonical axiom interfaces contain only canonical coordinates. -/
theorem axiomEnvironment_canonical {axioms : List (AxiomSpec Address)}
    (canonical : ∀ spec ∈ axioms, spec.Canonical) {ref : ConstRef Address}
    {entry : ConstantEntry Address} (present : axiomEnvironment axioms ref = some entry) :
    ∃ spec ∈ axioms, ref = .member spec.id.addr 0 := by
  induction axioms with
  | nil => cases present
  | cons spec rest ih =>
    simp only [axiomEnvironment, Model.Environment.insert] at present
    split at present
    · rename_i same
      exact ⟨spec, List.mem_cons_self .., same.trans (canonical spec (List.mem_cons_self ..))⟩
    · obtain ⟨found, listed, same⟩ := ih (fun other listed => canonical other
        (List.mem_cons_of_mem _ listed)) present
      exact ⟨found, List.mem_cons_of_mem _ listed, same⟩

/-- With distinct addresses, every listed canonical axiom keeps its own entry. -/
theorem axiomEnvironment_installed {axioms : List (AxiomSpec Address)}
    (canonical : ∀ spec ∈ axioms, spec.Canonical)
    (distinct : (axioms.map (·.id.addr)).Nodup) {spec : AxiomSpec Address}
    (listed : spec ∈ axioms) : axiomEnvironment axioms spec.ref = some spec.entry := by
  induction axioms with
  | nil => cases listed
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at distinct
    rcases List.mem_cons.mp listed with same | later
    · subst same
      exact Model.Environment.insert_same ..
    · have different : spec.ref ≠ first.ref := by
        intro same
        rw [canonical spec listed, canonical first (List.mem_cons_self ..)] at same
        exact distinct.1 ⟨spec, later, (ConstRef.member.inj same).1⟩
      simp only [axiomEnvironment, Model.Environment.insert, if_neg different]
      exact ih (fun other listed => canonical other (List.mem_cons_of_mem _ listed)) distinct.2
        later

/-- Definitions in dependency order under the canonical map. The reference of
every definition is forced to its standalone coordinate; the freshness of that
coordinate and its resolution are derived, not assumed. -/
inductive ResolvedDefinitionPlan (env : Ixon.Env) (cfg : CheckCfg) (work : Array AnonWorkItem) :
    Model.Environment Address → List (DefinitionSpec Address) → Model.Environment Address → Prop
  | nil (entries) : ResolvedDefinitionPlan env cfg work entries [] entries
  | cons {before after : Model.Environment Address} {rest : List (DefinitionSpec Address)}
      (spec : DefinitionSpec Address) (canonical : spec.Canonical)
      (position : WorkPosition work (.standalone spec.input.id.addr))
      (run : AtomicDefinitionRun env.resolve before spec.input
        (position.state env cfg).checker spec.body spec.type)
      (tail : ResolvedDefinitionPlan env cfg work (before.insert spec.ref spec.entry) rest after) :
      ResolvedDefinitionPlan env cfg work before (spec :: rest) after

/-- A canonical plan over distinct addresses is an atomic plan for the
canonical map: resolution follows from enumeration of the work position, and
freshness from the distinctness of the pending addresses. -/
theorem ResolvedDefinitionPlan.atomic {env : Ixon.Env} {cfg : CheckCfg} {work : Array AnonWorkItem}
    {before after : Model.Environment Address} {definitions : List (DefinitionSpec Address)}
    (plan : ResolvedDefinitionPlan env cfg work before definitions after)
    (materializes : SourceMaterializes env) (enumerated : buildAnonWork env = .ok work)
    (bound : CanonicalOutside before (definitions.map (·.input.id.addr)))
    (distinct : (definitions.map (·.input.id.addr)).Nodup) :
    AtomicDefinitionPlan env cfg work env.resolve before definitions after := by
  induction plan with
  | nil entries => exact .nil entries
  | @cons before after rest spec canonical position run tail ih =>
    simp only [List.map_cons, List.nodup_cons] at distinct
    have resolved : env.resolve spec.input.id.addr = some spec.ref := by
      rw [canonical]
      exact resolve_of_work_standalone materializes enumerated position.mem
    have fresh : before spec.ref = none := by
      cases present : before spec.ref with
      | none => rfl
      | some entry =>
        obtain ⟨addr, same, absent⟩ := bound spec.ref entry present
        rw [canonical] at same
        obtain ⟨same, _⟩ := ConstRef.member.inj same
        subst same
        exact (absent (List.mem_map.mpr ⟨spec, List.mem_cons_self .., rfl⟩)).elim
    refine .cons spec resolved fresh position run (ih ?_ distinct.2)
    intro ref entry present
    by_cases same : ref = spec.ref
    · subst same
      exact ⟨spec.input.id.addr, canonical, distinct.1⟩
    · have old : before ref = some entry := by
        simpa only [Model.Environment.insert, if_neg same] using present
      obtain ⟨addr, refEq, absent⟩ := bound ref entry old
      exact ⟨addr, refEq, fun listed => absent (List.mem_cons_of_mem _ listed)⟩

/-- Syntactic provenance of an axiom at a work position, with its reference
forced to the canonical coordinate. -/
structure ResolvedAxiomObservation (env : Ixon.Env) (cfg : CheckCfg) (work : Array AnonWorkItem)
    (spec : AxiomSpec Address) where
  position : WorkPosition work (.standalone spec.id.addr)
  path : StandalonePrefix spec.id (position.state env cfg).checker spec.constant
  reads : readExpr? env.resolve spec.sourceType = some spec.type.erase

/-- Resolution and installation of a canonical axiom are derived. -/
def ResolvedAxiomObservation.atomic {env : Ixon.Env} {cfg : CheckCfg} {work : Array AnonWorkItem}
    {spec : AxiomSpec Address} (observation : ResolvedAxiomObservation env cfg work spec)
    (materializes : SourceMaterializes env) (enumerated : buildAnonWork env = .ok work)
    (canonical : spec.Canonical) {entries : Model.Environment Address}
    (installed : entries spec.ref = some spec.entry) :
    AxiomObservation env cfg work env.resolve entries spec :=
  { position := observation.position, path := observation.path,
    resolved := by
      rw [canonical]
      exact resolve_of_work_standalone materializes enumerated observation.position.mem
    installed, reads := observation.reads }

/-- The production environment fragment with every reference forced to its
canonical coordinate. Compared with `AtomicEnvironmentFragment`, the reference
map is `env.resolve`, and the resolution, freshness, and installation premises
are replaced by the finite source contract and distinctness of the listed
addresses. -/
structure ResolvedEnvironmentFragment (env : Ixon.Env) (cfg : CheckCfg) where
  work : Array AnonWorkItem
  enumerated : buildAnonWork env = .ok work
  materializes : SourceMaterializes env
  axioms : List (AxiomSpec Address)
  definitions : List (DefinitionSpec Address)
  entries : Model.Environment Address
  canonical : ∀ spec ∈ axioms, spec.Canonical
  distinct : (axioms.map (·.id.addr) ++ definitions.map (·.input.id.addr)).Nodup
  axiomRuns : ∀ spec ∈ axioms, Nonempty (ResolvedAxiomObservation env cfg work spec)
  plan : ResolvedDefinitionPlan env cfg work (axiomEnvironment axioms) definitions entries
  sourceCovered : ∀ addr ∈ env.consts.keys, .standalone addr ∈ work
  workCovered : ∀ item ∈ work,
    (∃ spec ∈ axioms, item = .standalone spec.id.addr) ∨
      (∃ spec ∈ definitions, item = .standalone spec.input.id.addr)

/-- The canonical fragment is an atomic fragment for `env.resolve`. -/
def ResolvedEnvironmentFragment.atomic {env : Ixon.Env} {cfg : CheckCfg}
    (fragment : ResolvedEnvironmentFragment env cfg) :
    AtomicEnvironmentFragment env cfg env.resolve where
  work := fragment.work
  enumerated := fragment.enumerated
  axioms := fragment.axioms
  definitions := fragment.definitions
  entries := fragment.entries
  axiomRuns spec listed :=
    let ⟨observation⟩ := fragment.axiomRuns spec listed
    ⟨observation.atomic fragment.materializes fragment.enumerated (fragment.canonical spec listed)
      (axiomEnvironment_installed fragment.canonical
        (List.nodup_append.mp fragment.distinct).1 listed)⟩
  plan := fragment.plan.atomic fragment.materializes fragment.enumerated
    (by
      intro ref entry present
      obtain ⟨spec, listed, same⟩ := axiomEnvironment_canonical fragment.canonical present
      refine ⟨spec.id.addr, same, fun pending => ?_⟩
      exact (List.nodup_append.mp fragment.distinct).2.2 _ (List.mem_map.mpr ⟨spec, listed, rfl⟩)
        _ pending rfl)
    (List.nodup_append.mp fragment.distinct).2.1
  sourceCovered := fragment.sourceCovered
  workCovered := fragment.workCovered

/-- A successful `checkEnvAnon` run in the canonical fragment extends every
model of its axiom set while preserving all axiom interpretations. -/
theorem checkEnvAnon_preserves_model_resolved {env : Ixon.Env} {cfg : CheckCfg}
    (fragment : ResolvedEnvironmentFragment env cfg)
    (wellFormed : (axiomEnvironment fragment.axioms).WF)
    {results : Array CheckResult} (accepted : checkEnvAnon env cfg = .ok results)
    (succeeded : ∀ result ∈ results, result.err? = none) :
    fragment.entries.WF ∧
      PreservesModels.{0,v} (axiomEnvironment fragment.axioms) fragment.entries :=
  checkEnvAnon_atomic_preserves_model fragment.atomic wellFormed accepted succeeded

/-- Every source address receives the interface entry at its canonical
standalone coordinate, reading the declaration reached by production lookup. -/
theorem checkEnvAnon_represents_source_resolved {env : Ixon.Env} {cfg : CheckCfg}
    (fragment : ResolvedEnvironmentFragment env cfg)
    (wellFormed : (axiomEnvironment fragment.axioms).WF)
    {results : Array CheckResult} (accepted : checkEnvAnon env cfg = .ok results)
    (succeeded : ∀ result ∈ results, result.err? = none) :
    ∀ addr ∈ env.consts.keys, ∃ entry, fragment.entries (.member addr 0) = some entry ∧
      ∃ concrete : KConst .anon,
        (∃ before after, TcM.checkConst (⟨addr, ()⟩ : KId .anon) before = .ok () after ∧
          Nonempty (StandalonePrefix (⟨addr, ()⟩ : KId .anon) before concrete)) ∧
        DeclarationReading env.resolve concrete entry := by
  intro addr present
  obtain ⟨ref, entry, resolved, installed, rest⟩ :=
    checkEnvAnon_atomic_represents_source fragment.atomic wellFormed accepted succeeded addr present
  have canonical := resolve_of_work_standalone fragment.materializes fragment.enumerated
    (fragment.sourceCovered addr present)
  cases Option.some.inj (resolved.symm.trans canonical)
  exact ⟨entry, installed, rest⟩

/-- No declaration can inhabit an axiom type interpreted as empty. -/
theorem checkEnvAnon_no_false_resolved {env : Ixon.Env} {cfg : CheckCfg}
    (fragment : ResolvedEnvironmentFragment env cfg)
    (wellFormed : (axiomEnvironment fragment.axioms).WF)
    {results : Array CheckResult} (accepted : checkEnvAnon env cfg = .ok results)
    (succeeded : ∀ result ∈ results, result.err? = none)
    {V : Type v} [SetTheory V] (axiomValues : Assignment Address V)
    (axiomModel : Realizes axiomValues (axiomEnvironment fragment.axioms))
    {falseAddr : Address} {falseEntry : ConstantEntry Address}
    (hasFalse : axiomEnvironment fragment.axioms (.member falseAddr 0) = some falseEntry)
    (falseEmpty : axiomValues (.member falseAddr 0) [] = SetTheory.empty)
    {ref : ConstRef Address} {entry : ConstantEntry Address}
    (present : fragment.entries ref = some entry)
    (isFalse : entry.type.erase = .const (.member falseAddr 0) []) : False :=
  checkEnvAnon_atomic_no_false fragment.atomic wellFormed accepted succeeded axiomValues
    axiomModel hasFalse falseEmpty present isFalse

end Ix.Kernel.Consistency
