/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Inductive.Shape
import Ix.Kernel.Check

/-!
# Production inductive block checks as execution traces

`checkInductiveBlockImpl` first classifies every stored member, inferring the
untouched stored type of each family and constructor, then validates every
family header with its constructors, then re-validates each constructor
against its parent. The traces below retain exactly the production calls made
on the success path, in order, with the concrete declarations returned by
lookup. Later modules consume the retained type-inference runs; the
inductive-specific checks are recorded so their consequences can be extracted
without re-executing the checker.
-/

namespace Ix.Kernel.Consistency.Inductive

open Theory

private theorem bind_success {α β : Type} {x : TcM .anon α} {k : α → TcM .anon β}
    {before after : TcState .anon} {value : β}
    (accepted : EStateM.bind x k before = .ok value after) :
    ∃ intermediate state, x before = .ok intermediate state ∧
      k intermediate state = .ok value after := by
  rw [EStateM.bind] at accepted
  cases run : x before with
  | error err state => rw [run] at accepted; contradiction
  | ok intermediate state =>
      rw [run] at accepted
      exact ⟨intermediate, state, rfl, accepted⟩

/-! ### Member classification -/

/-- One member of the classification pass: reset, lookup, validation, type
inference of the untouched stored type, and its sort check. -/
structure MemberTypeRun (member : KId .anon) (methods : Methods .anon) (before : TcState .anon) where
  concrete : KConst .anon
  reset : TcState .anon
  loaded : TcState .anon
  validated : TcState .anon
  inferred : KExpr .anon
  typeState : TcState .anon
  level : KUniv .anon
  after : TcState .anon
  resetRun : TcM.reset before = .ok () reset
  getRun : TcM.getConst member reset = .ok concrete loaded
  validationRun : (RecM.validateConstWellScoped concrete).run methods loaded = .ok () validated
  typeRun : (RecM.infer concrete.ty).run methods validated = .ok inferred typeState
  sortRun : (RecM.ensureSortDirect inferred).run methods typeState = .ok level after

/-- Whether a loaded declaration is a family. -/
def isInductiveDecl : KConst .anon → Bool
  | .indc .. => true
  | _ => false

/-- Whether a loaded declaration is a constructor. -/
def isConstructorDecl : KConst .anon → Bool
  | .ctor .. => true
  | _ => false

/-- The classification pass over the remaining members with the accumulated
family and constructor identifiers. -/
inductive ClassifyTrace (block : KId .anon) (methods : Methods .anon) :
    List (KId .anon) → Array (KId .anon) → Array (KId .anon) → TcState .anon →
      Array (KId .anon) × Array (KId .anon) → TcState .anon → Type
  | nil (inds ctors : Array (KId .anon)) (state : TcState .anon) :
      ClassifyTrace block methods [] inds ctors state (inds, ctors) state
  | indc {member : KId .anon} {members : List (KId .anon)} {inds ctors : Array (KId .anon)}
      {before : TcState .anon} {result : Array (KId .anon) × Array (KId .anon)} {after : TcState .anon}
      (run : MemberTypeRun member methods before) (kind : isInductiveDecl run.concrete = true)
      (tail : ClassifyTrace block methods members (inds.push member) ctors run.after result after) :
      ClassifyTrace block methods (member :: members) inds ctors before result after
  | ctor {member : KId .anon} {members : List (KId .anon)} {inds ctors : Array (KId .anon)}
      {before : TcState .anon} {result : Array (KId .anon) × Array (KId .anon)} {after : TcState .anon}
      (run : MemberTypeRun member methods before) (kind : isConstructorDecl run.concrete = true)
      (tail : ClassifyTrace block methods members inds (ctors.push member) run.after result after) :
      ClassifyTrace block methods (member :: members) inds ctors before result after

theorem classify_trace {block : KId .anon} {methods : Methods .anon} :
    ∀ {members : List (KId .anon)} {inds ctors : Array (KId .anon)} {before : TcState .anon}
      {result : Array (KId .anon) × Array (KId .anon)} {after : TcState .anon},
      (RecM.classifyInductiveBlockMembers block members inds ctors).run methods before =
        .ok result after →
      Nonempty (ClassifyTrace block methods members inds ctors before result after)
  | [], inds, ctors, before, result, after, h => by
      simp only [RecM.classifyInductiveBlockMembers, ReaderT.run_pure] at h
      change EStateM.Result.ok (inds, ctors) before = _ at h
      cases h
      exact ⟨.nil inds ctors before⟩
  | member :: members, inds, ctors, before, result, after, h => by
      unfold RecM.classifyInductiveBlockMembers at h
      simp only [ReaderT.run_bind, ReaderT.run_monadLift] at h
      change EStateM.bind TcM.reset _ before = _ at h
      obtain ⟨⟨⟩, reset, resetRun, h⟩ := bind_success h
      change EStateM.bind (TcM.getConst member) _ reset = _ at h
      obtain ⟨concrete, loaded, getRun, h⟩ := bind_success h
      change EStateM.bind ((RecM.validateConstWellScoped concrete).run methods) _ loaded = _ at h
      obtain ⟨⟨⟩, validated, validationRun, h⟩ := bind_success h
      revert h
      cases concrete
      case indc name levelParams lvls params indices isUnsafe indBlock memberIdx ty ctorIds leanAll =>
          intro h
          simp only [ReaderT.run_bind] at h
          change EStateM.bind ((RecM.infer ty).run methods) _ validated = _ at h
          obtain ⟨inferred, typeState, typeRun, h⟩ := bind_success h
          change EStateM.bind ((RecM.ensureSortDirect inferred).run methods) _ typeState = _ at h
          obtain ⟨level, sortState, sortRun, h⟩ := bind_success h
          obtain ⟨tail⟩ := classify_trace h
          exact ⟨.indc ⟨_, reset, loaded, validated, inferred, typeState, level, sortState, resetRun,
            getRun, validationRun, typeRun, sortRun⟩ rfl tail⟩
      case ctor name levelParams isUnsafe lvls induct cidx params fields ty =>
          intro h
          simp only [ReaderT.run_bind] at h
          change EStateM.bind ((RecM.infer ty).run methods) _ validated = _ at h
          obtain ⟨inferred, typeState, typeRun, h⟩ := bind_success h
          change EStateM.bind ((RecM.ensureSortDirect inferred).run methods) _ typeState = _ at h
          obtain ⟨level, sortState, sortRun, h⟩ := bind_success h
          obtain ⟨tail⟩ := classify_trace h
          exact ⟨.ctor ⟨_, reset, loaded, validated, inferred, typeState, level, sortState, resetRun,
            getRun, validationRun, typeRun, sortRun⟩ rfl tail⟩
      all_goals
        intro h
        change EStateM.Result.error _ validated = _ at h
        cases h

/-! ### Constructor validation -/

/-- The successful header agreement of a stored constructor with its parent,
as returned by production lookup. -/
theorem ctorMetadata_success {ctorId inductId : KId .anon} {expectedCidx indParams : Nat}
    {indLvls : UInt64} {indIsUnsafe : Bool} {methods : Methods .anon} {before after : TcState .anon}
    {ctorTy : KExpr .anon} {ctorFields : Nat}
    (h : (RecM.checkCtorMetadataAgainstParent ctorId inductId expectedCidx indParams indLvls
      indIsUnsafe).run methods before = .ok (ctorTy, ctorFields) after) :
    ∃ name levelParams isUnsafe lvls induct cidx params fields,
      TcM.getConst ctorId before =
        .ok (KConst.ctor name levelParams isUnsafe lvls induct cidx params fields ctorTy) after ∧
      (induct != inductId) = false ∧ lvls = indLvls ∧ isUnsafe = indIsUnsafe ∧
      params.toNat = indParams ∧ cidx.toNat = expectedCidx ∧ ctorFields = fields.toNat := by
  unfold RecM.checkCtorMetadataAgainstParent at h
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at h
  change EStateM.bind (TcM.getConst ctorId) _ before = _ at h
  obtain ⟨concrete, loaded, getRun, h⟩ := bind_success h
  revert h
  cases concrete
  case ctor name levelParams isUnsafe lvls induct cidx params fields ty =>
      intro h
      simp only [ReaderT.run_bind] at h
      change EStateM.bind (pure _) _ loaded = _ at h
      obtain ⟨_, _, hpure, h⟩ := bind_success h
      change EStateM.Result.ok _ loaded = _ at hpure
      cases hpure
      by_cases hinduct : (induct != inductId) = true
      · simp only [hinduct, if_true] at h
        change EStateM.Result.error _ loaded = _ at h
        cases h
      · simp only [hinduct, Bool.false_eq_true, if_false] at h
        by_cases hlvls : (lvls != indLvls) = true
        · simp only [hlvls, if_true] at h
          change EStateM.Result.error _ loaded = _ at h
          cases h
        · simp only [hlvls, Bool.false_eq_true, if_false] at h
          by_cases hunsafe : (isUnsafe != indIsUnsafe) = true
          · simp only [hunsafe, if_true] at h
            change EStateM.Result.error _ loaded = _ at h
            cases h
          · simp only [hunsafe, Bool.false_eq_true, if_false] at h
            by_cases hparams : (params.toNat != indParams) = true
            · simp only [hparams, if_true] at h
              change EStateM.Result.error _ loaded = _ at h
              cases h
            · simp only [hparams, Bool.false_eq_true, if_false] at h
              by_cases hcidx : (cidx.toNat != expectedCidx) = true
              · simp only [hcidx, if_true] at h
                change EStateM.Result.error _ loaded = _ at h
                cases h
              · simp only [hcidx, Bool.false_eq_true, if_false] at h
                change EStateM.Result.ok (ty, fields.toNat) loaded = _ at h
                cases h
                refine ⟨name, levelParams, isUnsafe, lvls, induct, cidx, params, fields, getRun,
                  Bool.eq_false_iff.mpr hinduct, ?_, ?_, ?_, ?_, rfl⟩
                · simpa using Bool.eq_false_iff.mpr hlvls
                · simpa using Bool.eq_false_iff.mpr hunsafe
                · simpa using Bool.eq_false_iff.mpr hparams
                · simpa using Bool.eq_false_iff.mpr hcidx
  all_goals
    intro h
    simp only [ReaderT.run_bind] at h
    change EStateM.Result.error _ loaded = _ at h
    cases h

/-- The A1–A4 runs of one constructor against its resolved parent. -/
structure ConstructorCheckRun (ctorId inductId : KId .anon) (expectedCidx indParams indIndices : Nat)
    (indLvls : UInt64) (indIsUnsafe : Bool) (indTy : KExpr .anon) (indLevel : KUniv .anon)
    (blockAddrs : Array Address) (methods : Methods .anon) (before : TcState .anon) where
  ctorTy : KExpr .anon
  ctorFields : Nat
  headerState : TcState .anon
  headerRun : (RecM.checkCtorMetadataAgainstParent ctorId inductId expectedCidx indParams indLvls
    indIsUnsafe).run methods before = .ok (ctorTy, ctorFields) headerState
  agreementState : TcState .anon
  agreementRun : (RecM.checkParamAgreement indTy ctorTy indParams).run methods headerState =
    .ok () agreementState
  positivityState : TcState .anon
  positivityRun : indIsUnsafe = false →
    (RecM.checkPositivity ctorTy indParams blockAddrs).run methods agreementState = .ok () positivityState
  positivitySkipped : indIsUnsafe = true → positivityState = agreementState
  universesState : TcState .anon
  universesRun : (RecM.checkFieldUniverses ctorTy indParams indLevel).run methods positivityState =
    .ok () universesState
  after : TcState .anon
  returnRun : (RecM.checkCtorReturnType ctorTy indParams indIndices ctorFields inductId.addr indLvls
    blockAddrs).run methods universesState = .ok () after

theorem constructor_check_run {ctorId inductId : KId .anon} {expectedCidx indParams indIndices : Nat}
    {indLvls : UInt64} {indIsUnsafe : Bool} {indTy : KExpr .anon} {indLevel : KUniv .anon}
    {blockAddrs : Array Address} {methods : Methods .anon} {before after : TcState .anon}
    (h : (RecM.checkInductiveConstructor ctorId inductId expectedCidx indParams indIndices indLvls
      indIsUnsafe indTy indLevel blockAddrs).run methods before = .ok () after) :
    ∃ run : ConstructorCheckRun ctorId inductId expectedCidx indParams indIndices indLvls indIsUnsafe
      indTy indLevel blockAddrs methods before, run.after = after := by
  unfold RecM.checkInductiveConstructor at h
  simp only [ReaderT.run_bind] at h
  change EStateM.bind ((RecM.checkCtorMetadataAgainstParent ctorId inductId expectedCidx indParams
    indLvls indIsUnsafe).run methods) _ before = _ at h
  obtain ⟨⟨ctorTy, ctorFields⟩, headerState, headerRun, h⟩ := bind_success h
  change EStateM.bind ((RecM.checkParamAgreement indTy ctorTy indParams).run methods) _ headerState =
    _ at h
  obtain ⟨⟨⟩, agreementState, agreementRun, h⟩ := bind_success h
  cases indIsUnsafe with
  | false =>
      simp only [Bool.not_false, if_true] at h
      change EStateM.bind ((RecM.checkPositivity ctorTy indParams blockAddrs).run methods) _
        agreementState = _ at h
      obtain ⟨⟨⟩, positivityState, positivityRun, h⟩ := bind_success h
      change EStateM.bind ((RecM.checkFieldUniverses ctorTy indParams indLevel).run methods) _
        positivityState = _ at h
      obtain ⟨⟨⟩, universesState, universesRun, h⟩ := bind_success h
      exact ⟨⟨ctorTy, ctorFields, headerState, headerRun, agreementState, agreementRun,
        positivityState, (fun _ => positivityRun), (fun contra => by cases contra), universesState,
        universesRun, after, h⟩, rfl⟩
  | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false, ReaderT.run_bind] at h
      change EStateM.bind ((RecM.checkFieldUniverses ctorTy indParams indLevel).run methods) _
        agreementState = _ at h
      obtain ⟨⟨⟩, universesState, universesRun, h⟩ := bind_success h
      exact ⟨⟨ctorTy, ctorFields, headerState, headerRun, agreementState, agreementRun,
        agreementState, (fun contra => by cases contra), (fun _ => rfl), universesState,
        universesRun, after, h⟩, rfl⟩

/-- The source-ordered constructor traversal of one resolved family header. -/
inductive ConstructorsTrace (inductId : KId .anon) (indParams indIndices : Nat) (indLvls : UInt64)
    (indIsUnsafe : Bool) (indTy : KExpr .anon) (indLevel : KUniv .anon) (blockAddrs : Array Address)
    (methods : Methods .anon) : List (KId .anon) → Nat → TcState .anon → TcState .anon → Type
  | nil (expectedCidx : Nat) (state : TcState .anon) :
      ConstructorsTrace inductId indParams indIndices indLvls indIsUnsafe indTy indLevel blockAddrs
        methods [] expectedCidx state state
  | cons {ctorId : KId .anon} {ctorIds : List (KId .anon)} {expectedCidx : Nat}
      {before after : TcState .anon}
      (run : ConstructorCheckRun ctorId inductId expectedCidx indParams indIndices indLvls indIsUnsafe
        indTy indLevel blockAddrs methods before)
      (tail : ConstructorsTrace inductId indParams indIndices indLvls indIsUnsafe indTy indLevel
        blockAddrs methods ctorIds (expectedCidx + 1) run.after after) :
      ConstructorsTrace inductId indParams indIndices indLvls indIsUnsafe indTy indLevel blockAddrs
        methods (ctorId :: ctorIds) expectedCidx before after

theorem constructors_trace {inductId : KId .anon} {indParams indIndices : Nat} {indLvls : UInt64}
    {indIsUnsafe : Bool} {indTy : KExpr .anon} {indLevel : KUniv .anon} {blockAddrs : Array Address}
    {methods : Methods .anon} :
    ∀ {ctorIds : List (KId .anon)} {expectedCidx : Nat} {before after : TcState .anon},
      (RecM.checkInductiveConstructors inductId indParams indIndices indLvls indIsUnsafe indTy indLevel
        blockAddrs ctorIds expectedCidx).run methods before = .ok () after →
      Nonempty (ConstructorsTrace inductId indParams indIndices indLvls indIsUnsafe indTy indLevel
        blockAddrs methods ctorIds expectedCidx before after)
  | [], expectedCidx, before, after, h => by
      simp only [RecM.checkInductiveConstructors, ReaderT.run_pure] at h
      change EStateM.Result.ok () before = _ at h
      cases h
      exact ⟨.nil expectedCidx before⟩
  | ctorId :: ctorIds, expectedCidx, before, after, h => by
      unfold RecM.checkInductiveConstructors at h
      simp only [ReaderT.run_bind] at h
      change EStateM.bind ((RecM.checkInductiveConstructor ctorId inductId expectedCidx indParams
        indIndices indLvls indIsUnsafe indTy indLevel blockAddrs).run methods) _ before = _ at h
      obtain ⟨⟨⟩, middle, headRun, h⟩ := bind_success h
      obtain ⟨run, rfl⟩ := constructor_check_run headRun
      obtain ⟨tail⟩ := constructors_trace h
      exact ⟨.cons run tail⟩

/-! ### Family header validation -/

/-- The execution of one resolved family header check: block discovery, the
result sort, peer agreement, the constructor traversal, and recursor
generation. -/
structure ResolvedMemberRun (id : KId .anon) (params indices lvls : UInt64) (ctors : Array (KId .anon))
    (block : KId .anon) (isUnsafe : Bool) (ty : KExpr .anon) (methods : Methods .anon)
    (before : TcState .anon) where
  blockInds : Array (KId .anon)
  discovered : TcState .anon
  discoverRun : (RecM.discoverBlockInductives block).run methods before = .ok blockInds discovered
  arity : UInt64
  arityState : TcState .anon
  arityRun : (RecM.checkedMetadataSum "inductive params + indices" #[params, indices]).run methods
    discovered = .ok arity arityState
  level : KUniv .anon
  levelState : TcState .anon
  levelRun : (RecM.getResultSortLevel ty arity.toNat).run methods arityState = .ok level levelState
  peerState : TcState .anon
  peerRun : (RecM.checkInductivePeerAgreement id block params lvls isUnsafe ty level blockInds).run
    methods levelState = .ok () peerState
  ctorState : TcState .anon
  constructors : ConstructorsTrace id params.toNat indices.toNat lvls isUnsafe ty level
    (blockInds.map (·.addr)) methods ctors.toList 0 peerState ctorState
  after : TcState .anon
  recursorRun : (RecM.ensureInductiveRecursors block).run methods ctorState = .ok () after

theorem resolved_member_run {id : KId .anon} {params indices lvls : UInt64} {ctors : Array (KId .anon)}
    {block : KId .anon} {isUnsafe : Bool} {ty : KExpr .anon} {methods : Methods .anon}
    {before after : TcState .anon}
    (h : (RecM.checkResolvedInductiveMember id params indices lvls ctors block isUnsafe ty).run
      methods before = .ok () after) :
    ∃ run : ResolvedMemberRun id params indices lvls ctors block isUnsafe ty methods before,
      run.after = after := by
  unfold RecM.checkResolvedInductiveMember at h
  simp only [ReaderT.run_bind] at h
  change EStateM.bind ((RecM.discoverBlockInductives block).run methods) _ before = _ at h
  obtain ⟨blockInds, discovered, discoverRun, h⟩ := bind_success h
  change EStateM.bind ((RecM.checkedMetadataSum "inductive params + indices" #[params, indices]).run
    methods) _ discovered = _ at h
  obtain ⟨arity, arityState, arityRun, h⟩ := bind_success h
  change EStateM.bind ((RecM.getResultSortLevel ty arity.toNat).run methods) _ arityState = _ at h
  obtain ⟨level, levelState, levelRun, h⟩ := bind_success h
  change EStateM.bind ((RecM.checkInductivePeerAgreement id block params lvls isUnsafe ty level
    blockInds).run methods) _ levelState = _ at h
  obtain ⟨⟨⟩, peerState, peerRun, h⟩ := bind_success h
  change EStateM.bind ((RecM.checkInductiveConstructors id params.toNat indices.toNat lvls isUnsafe ty
    level (blockInds.map (·.addr)) ctors.toList 0).run methods) _ peerState = _ at h
  obtain ⟨⟨⟩, ctorState, ctorRun, h⟩ := bind_success h
  obtain ⟨constructors⟩ := constructors_trace ctorRun
  exact ⟨⟨blockInds, discovered, discoverRun, arity, arityState, arityRun, level, levelState, levelRun,
    peerState, peerRun, ctorState, constructors, after, h⟩, rfl⟩

/-- The member check of one family identifier: lookup of the stored family
declaration and its resolved header check. -/
structure MemberImplRun (id : KId .anon) (methods : Methods .anon) (before : TcState .anon) where
  name : Mode.anon.F Name
  levelParams : Mode.anon.F (Array Name)
  lvls : UInt64
  params : UInt64
  indices : UInt64
  isUnsafe : Bool
  block : KId .anon
  memberIdx : UInt64
  ty : KExpr .anon
  ctors : Array (KId .anon)
  leanAll : Mode.anon.F (Array (KId .anon))
  loaded : TcState .anon
  getRun : TcM.getConst id before =
    .ok (.indc name levelParams lvls params indices isUnsafe block memberIdx ty ctors leanAll) loaded
  resolved : ResolvedMemberRun id params indices lvls ctors block isUnsafe ty methods loaded

theorem member_impl_run {id : KId .anon} {methods : Methods .anon} {before after : TcState .anon}
    (h : (RecM.checkInductiveMemberImpl id).run methods before = .ok () after) :
    ∃ run : MemberImplRun id methods before, run.resolved.after = after := by
  unfold RecM.checkInductiveMemberImpl at h
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at h
  change EStateM.bind (TcM.getConst id) _ before = _ at h
  obtain ⟨concrete, loaded, getRun, h⟩ := bind_success h
  revert h
  cases concrete
  case indc name levelParams lvls params indices isUnsafe block memberIdx ty ctors leanAll =>
      intro h
      simp only [ReaderT.run_bind] at h
      change EStateM.bind (pure _) _ loaded = _ at h
      obtain ⟨_, _, hpure, h⟩ := bind_success h
      change EStateM.Result.ok _ loaded = _ at hpure
      cases hpure
      obtain ⟨resolved, hafter⟩ := resolved_member_run h
      exact ⟨⟨name, levelParams, lvls, params, indices, isUnsafe, block, memberIdx, ty, ctors, leanAll,
        loaded, getRun, resolved⟩, hafter⟩
  all_goals
    intro h
    simp only [ReaderT.run_bind] at h
    change EStateM.Result.error _ loaded = _ at h
    cases h

/-- The source-ordered family member checks. -/
inductive MembersTrace (methods : Methods .anon) :
    List (KId .anon) → TcState .anon → TcState .anon → Type
  | nil (state : TcState .anon) : MembersTrace methods [] state state
  | cons {id : KId .anon} {ids : List (KId .anon)} {before reset after : TcState .anon}
      (resetRun : TcM.reset before = .ok () reset)
      (run : MemberImplRun id methods reset)
      (tail : MembersTrace methods ids run.resolved.after after) :
      MembersTrace methods (id :: ids) before after

theorem members_trace {methods : Methods .anon} :
    ∀ {ids : List (KId .anon)} {before after : TcState .anon},
      (RecM.checkInductiveMembers ids).run methods before = .ok () after →
      Nonempty (MembersTrace methods ids before after)
  | [], before, after, h => by
      simp only [RecM.checkInductiveMembers, ReaderT.run_pure] at h
      change EStateM.Result.ok () before = _ at h
      cases h
      exact ⟨.nil before⟩
  | id :: ids, before, after, h => by
      unfold RecM.checkInductiveMembers at h
      simp only [ReaderT.run_bind, ReaderT.run_monadLift] at h
      change EStateM.bind TcM.reset _ before = _ at h
      obtain ⟨⟨⟩, reset, resetRun, h⟩ := bind_success h
      change EStateM.bind ((RecM.checkInductiveMemberImpl id).run methods) _ reset = _ at h
      obtain ⟨⟨⟩, middle, implRun, h⟩ := bind_success h
      obtain ⟨run, rfl⟩ := member_impl_run implRun
      obtain ⟨tail⟩ := members_trace h
      exact ⟨.cons resetRun run tail⟩

/-! ### Constructor member re-validation -/

/-- The standalone re-validation of each constructor against its stored parent
identifier; a non-constructor member is skipped by production. -/
inductive ConstructorMembersTrace (methods : Methods .anon) :
    List (KId .anon) → TcState .anon → TcState .anon → Type
  | nil (state : TcState .anon) : ConstructorMembersTrace methods [] state state
  | ctor {id : KId .anon} {ids : List (KId .anon)} {before loaded reset checked after : TcState .anon}
      {name : Mode.anon.F Name} {levelParams : Mode.anon.F (Array Name)} {isUnsafe : Bool}
      {lvls : UInt64} {induct : KId .anon} {cidx params fields : UInt64} {ty : KExpr .anon}
      (getRun : TcM.getConst id before =
        .ok (.ctor name levelParams isUnsafe lvls induct cidx params fields ty) loaded)
      (resetRun : TcM.reset loaded = .ok () reset)
      (checkRun : (RecM.checkCtorAgainstInductiveMemberImpl id induct).run methods reset = .ok () checked)
      (tail : ConstructorMembersTrace methods ids checked after) :
      ConstructorMembersTrace methods (id :: ids) before after
  | skip {id : KId .anon} {ids : List (KId .anon)} {before loaded after : TcState .anon}
      {concrete : KConst .anon}
      (getRun : TcM.getConst id before = .ok concrete loaded) (kind : isConstructorDecl concrete = false)
      (tail : ConstructorMembersTrace methods ids loaded after) :
      ConstructorMembersTrace methods (id :: ids) before after

theorem constructor_members_trace {methods : Methods .anon} :
    ∀ {ids : List (KId .anon)} {before after : TcState .anon},
      (RecM.checkInductiveConstructorMembers ids).run methods before = .ok () after →
      Nonempty (ConstructorMembersTrace methods ids before after)
  | [], before, after, h => by
      simp only [RecM.checkInductiveConstructorMembers, ReaderT.run_pure] at h
      change EStateM.Result.ok () before = _ at h
      cases h
      exact ⟨.nil before⟩
  | id :: ids, before, after, h => by
      unfold RecM.checkInductiveConstructorMembers at h
      simp only [ReaderT.run_bind, ReaderT.run_monadLift] at h
      change EStateM.bind (TcM.getConst id) _ before = _ at h
      obtain ⟨concrete, loaded, getRun, h⟩ := bind_success h
      revert h
      cases concrete
      case ctor name levelParams isUnsafe lvls induct cidx params fields ty =>
          intro h
          simp only [ReaderT.run_bind, ReaderT.run_monadLift] at h
          change EStateM.bind TcM.reset _ loaded = _ at h
          obtain ⟨⟨⟩, reset, resetRun, h⟩ := bind_success h
          change EStateM.bind ((RecM.checkCtorAgainstInductiveMemberImpl id induct).run methods) _
            reset = _ at h
          obtain ⟨⟨⟩, checked, checkRun, h⟩ := bind_success h
          obtain ⟨tail⟩ := constructor_members_trace h
          exact ⟨.ctor getRun resetRun checkRun tail⟩
      all_goals
        intro h
        obtain ⟨tail⟩ := constructor_members_trace h
        exact ⟨.skip getRun rfl tail⟩

/-! ### The whole block check -/

/-- The three phases of a successful inductive block check. -/
structure InductiveBlockTrace (block : KId .anon) (members : Array (KId .anon))
    (methods : Methods .anon) (before : TcState .anon) where
  indIds : Array (KId .anon)
  ctorIds : Array (KId .anon)
  classified : TcState .anon
  classify : ClassifyTrace block methods members.toList #[] #[] before (indIds, ctorIds) classified
  membersChecked : TcState .anon
  familyChecks : MembersTrace methods indIds.toList classified membersChecked
  after : TcState .anon
  constructorChecks : ConstructorMembersTrace methods ctorIds.toList membersChecked after

theorem inductive_block_trace {block : KId .anon} {members : Array (KId .anon)}
    {methods : Methods .anon} {before after : TcState .anon}
    (h : (RecM.checkInductiveBlockImpl block members).run methods before = .ok () after) :
    ∃ trace : InductiveBlockTrace block members methods before, trace.after = after := by
  unfold RecM.checkInductiveBlockImpl at h
  simp only [ReaderT.run_bind] at h
  change EStateM.bind ((RecM.classifyInductiveBlockMembers block members.toList #[] #[]).run methods)
    _ before = _ at h
  obtain ⟨⟨indIds, ctorIds⟩, classified, classifyRun, h⟩ := bind_success h
  change EStateM.bind ((RecM.checkInductiveMembers indIds.toList).run methods) _ classified = _ at h
  obtain ⟨⟨⟩, membersChecked, membersRun, h⟩ := bind_success h
  obtain ⟨classify⟩ := classify_trace classifyRun
  obtain ⟨familyChecks⟩ := members_trace membersRun
  obtain ⟨constructorChecks⟩ := constructor_members_trace h
  exact ⟨⟨indIds, ctorIds, classified, classify, membersChecked, familyChecks, after,
    constructorChecks⟩, rfl⟩

end Ix.Kernel.Consistency.Inductive
