import IxVMRefinement.Assembly.PointLoads
import IxVMRefinement.Assembly.PointReads
import IxVMRefinement.Assembly.PointStage
import IxVMRefinement.Assembly.PointCtors

/-! # The refinement of a block's arm on the constructors-only route

The walked checks of the members of a block on the modeled branch (two or more inductive types,
or one with a nested occurrence) give the one-point interface `PointBlock` at every prefix the
fold hands the step, with formers and constructors that are the block's readings.

* `pointFormerList`, `pointCtorList`: the formers (member `i`, in order) and the constructors
  (slot `j` of member `i`, in order) of the block as lists, each at the reading of its record
  over the step's store and the canonical annotation of that reading (a placeholder where a
  reading fails: never, at a walked block);
* `point_former_facts`: a member's former at the prefix (`pointFormer_of_member`), with its
  reading over the run's store (`point_member_reads`);
* `point_ctor_annot`: a constructor's stored type annotates its reading (the slot's load,
  `ctor_load_canon`);
* `point_names_nodup`: the keys of the formers and constructors are distinct
  (`point_keys_distinct`);
* `pointEvidenceK_of_members`: the evidence (`PointEvidenceK`), from the stage of the formers
  (`pointStage_coreFacts`) and each member's constructor loop at it (`pointCtors_of_member`);
* `unitStep_pointBlock_of_members`: the unit step with the evidence and the load facts
  discharged.

`PointEvidenceK` is `PointEvidence` with the prefix's store clause `HashKeyed` among the premises:
the stage of the formers asks that no projection marker's key be stored
(`stagedLoads_append_formers`), which the prefix invariant alone does not give and the carried
clause does.
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)
open IxVM.Refinement.Decl.Point

universe u

set_option linter.unusedVariables false

/-! ## The formers and constructors as lists -/

/-- The value of a reading, or a placeholder where it fails. -/
def pointReadOr (r : Ix.Kernel.Reader.ReadM (Ix.Kernel.Expr .anon)) : Ix.Kernel.Expr .anon :=
  match r with
  | .ok e => e
  | .error _ => .bvar 0

/-- The value of an annotation, or a placeholder where it is undefined. -/
def pointAnnOr (o : Option (Ix.Kernel.Expr .anon)) : Ix.Kernel.Expr .anon :=
  o.getD (.bvar 0)

theorem pointReadOr_of_ok {r : Ix.Kernel.Reader.ReadM (Ix.Kernel.Expr .anon)}
    {e : Ix.Kernel.Expr .anon} (h : r = .ok e) : pointReadOr r = e := by
  subst h
  rfl

theorem pointAnnOr_of_some {o : Option (Ix.Kernel.Expr .anon)} {e : Ix.Kernel.Expr .anon}
    (h : o = some e) : pointAnnOr o = e := by
  subst h
  rfl

section Lists

variable (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (B : _root_.Address) (cb : Ixon.Constant)
  (ms : Array Ixon.MutConst)

/-- The reading of an inductive member's type over the store `E`. -/
noncomputable def pointMemberType (ind : Ixon.Inductive) : Ix.Kernel.Expr .anon :=
  pointReadOr (blockRead t E B cb ms ind.typ)

/-- The canonical annotation of member `i`'s reading. -/
noncomputable def pointMemberAnn (i : Nat) (ind : Ixon.Inductive) : Ix.Kernel.Expr .anon :=
  pointAnnOr (LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
    ((L1.mutsRootOffset ms.toList i : Nat) : F) ind.typ (pointMemberType t E B cb ms ind))

/-- The former of member `i`, at the empty capability record, where member `i` is an inductive. -/
noncomputable def pointFormerSlot (i : Nat) : Option FormerRec :=
  match ms[i]? with
  | some (.indc ind) =>
    some (pointFormer t B i ind (pointMemberType t E B cb ms ind) {} (pointMemberAnn t E B cb ms i ind))
  | _ => none

/-- **The formers of the block**, member by member. -/
noncomputable def pointFormerList : List FormerRec :=
  (List.range ms.size).filterMap (pointFormerSlot t E B cb ms)

/-- The reading of a constructor's type over the store `E`. -/
noncomputable def pointCtorType (ct : Ixon.Constructor) : Ix.Kernel.Expr .anon :=
  pointReadOr (blockRead t E B cb ms ct.typ)

/-- The canonical annotation of the reading of constructor `j` of member `i`. -/
noncomputable def pointCtorAnn (i j : Nat) (ct : Ixon.Constructor) : Ix.Kernel.Expr .anon :=
  pointAnnOr (LoadedReads.canonAnn cb (List.range ct.lvls.toNat)
    (((L1.mutsRootOffset ms.toList i : Nat) : F) + 1 + ((j : Nat) : F)) ct.typ
    (pointCtorType t E B cb ms ct))

/-- Constructor `j` of member `i`, where the member has one. -/
noncomputable def pointCtorSlot (i : Nat) (ind : Ixon.Inductive) (j : Nat) : Option CtorRec :=
  match ind.ctors[j]? with
  | some ct =>
    some (pointCtor t B i j ct (pointCtorType t E B cb ms ct) (pointCtorAnn t E B cb ms i j ct))
  | none => none

/-- The constructors of member `i`, slot by slot. -/
noncomputable def pointMemberCtors (i : Nat) : List CtorRec :=
  match ms[i]? with
  | some (.indc ind) => (List.range ind.ctors.size).filterMap (pointCtorSlot t E B cb ms i ind)
  | _ => []

/-- **The constructors of the block**, member by member, slot by slot. -/
noncomputable def pointCtorList : List CtorRec :=
  (List.range ms.size).flatMap (pointMemberCtors t E B cb ms)

end Lists

section Membership

variable {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {B : _root_.Address} {cb : Ixon.Constant}
  {ms : Array Ixon.MutConst}

theorem pointFormerSlot_eq {i : Nat} {f : FormerRec}
    (h : pointFormerSlot t E B cb ms i = some f) :
    ∃ ind : Ixon.Inductive, ms[i]? = some (.indc ind) ∧
      f = pointFormer t B i ind (pointMemberType t E B cb ms ind) {}
        (pointMemberAnn t E B cb ms i ind) := by
  cases hm : ms[i]? with
  | none => simp [pointFormerSlot, hm] at h
  | some m =>
    rcases m with d | ind | rc
    · simp [pointFormerSlot, hm] at h
    · simp only [pointFormerSlot, hm, Option.some.injEq] at h
      exact ⟨ind, hm, h.symm⟩
    · simp [pointFormerSlot, hm] at h

theorem mem_pointFormerList {f : FormerRec} :
    f ∈ pointFormerList t E B cb ms ↔ ∃ (i : Nat) (ind : Ixon.Inductive),
      ms[i]? = some (.indc ind) ∧
      f = pointFormer t B i ind (pointMemberType t E B cb ms ind) {}
        (pointMemberAnn t E B cb ms i ind) := by
  unfold pointFormerList
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨i, -, hi⟩
    obtain ⟨ind, hm, rfl⟩ := pointFormerSlot_eq hi
    exact ⟨i, ind, hm, rfl⟩
  · rintro ⟨i, ind, hm, rfl⟩
    refine ⟨i, List.mem_range.mpr (Array.getElem?_eq_some_iff.mp hm).1, ?_⟩
    simp only [pointFormerSlot, hm]

theorem pointCtorSlot_eq {i : Nat} {ind : Ixon.Inductive} {j : Nat} {c : CtorRec}
    (h : pointCtorSlot t E B cb ms i ind j = some c) :
    ∃ ct : Ixon.Constructor, ind.ctors[j]? = some ct ∧
      c = pointCtor t B i j ct (pointCtorType t E B cb ms ct) (pointCtorAnn t E B cb ms i j ct) := by
  cases hct : ind.ctors[j]? with
  | none => simp [pointCtorSlot, hct] at h
  | some ct =>
    simp only [pointCtorSlot, hct, Option.some.injEq] at h
    exact ⟨ct, hct, h.symm⟩

theorem pointMemberCtors_of_mem {i : Nat} {ind : Ixon.Inductive}
    (hm : ms[i]? = some (.indc ind)) :
    pointMemberCtors t E B cb ms i =
      (List.range ind.ctors.size).filterMap (pointCtorSlot t E B cb ms i ind) := by
  simp only [pointMemberCtors, hm]

theorem pointMemberCtors_of_none {i : Nat} (hm : ms[i]? = none) :
    pointMemberCtors t E B cb ms i = [] := by
  simp only [pointMemberCtors, hm]

theorem mem_pointMemberCtors {i : Nat} {c : CtorRec} :
    c ∈ pointMemberCtors t E B cb ms i ↔ ∃ (ind : Ixon.Inductive) (j : Nat) (ct : Ixon.Constructor),
      ms[i]? = some (.indc ind) ∧ ind.ctors[j]? = some ct ∧
      c = pointCtor t B i j ct (pointCtorType t E B cb ms ct) (pointCtorAnn t E B cb ms i j ct) := by
  constructor
  · intro hc
    cases hm : ms[i]? with
    | none => simp [pointMemberCtors, hm] at hc
    | some m =>
      rcases m with d | ind | rc
      · simp [pointMemberCtors, hm] at hc
      · rw [pointMemberCtors_of_mem hm, List.mem_filterMap] at hc
        obtain ⟨j, -, hj⟩ := hc
        obtain ⟨ct, hct, rfl⟩ := pointCtorSlot_eq hj
        exact ⟨ind, j, ct, hm, hct, rfl⟩
      · simp [pointMemberCtors, hm] at hc
  · rintro ⟨ind, j, ct, hm, hct, rfl⟩
    rw [pointMemberCtors_of_mem hm, List.mem_filterMap]
    refine ⟨j, List.mem_range.mpr (Array.getElem?_eq_some_iff.mp hct).1, ?_⟩
    simp only [pointCtorSlot, hct]

theorem mem_pointCtorList {c : CtorRec} :
    c ∈ pointCtorList t E B cb ms ↔ ∃ (i : Nat) (ind : Ixon.Inductive) (j : Nat)
      (ct : Ixon.Constructor), ms[i]? = some (.indc ind) ∧ ind.ctors[j]? = some ct ∧
      c = pointCtor t B i j ct (pointCtorType t E B cb ms ct) (pointCtorAnn t E B cb ms i j ct) := by
  unfold pointCtorList
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨i, -, hc⟩
    obtain ⟨ind, j, ct, hm, hct, rfl⟩ := mem_pointMemberCtors.mp hc
    exact ⟨i, ind, j, ct, hm, hct, rfl⟩
  · rintro ⟨i, ind, j, ct, hm, hct, rfl⟩
    exact ⟨i, List.mem_range.mpr (Array.getElem?_eq_some_iff.mp hm).1,
      mem_pointMemberCtors.mpr ⟨ind, j, ct, hm, hct, rfl⟩⟩

end Membership

/-! ## The keys are distinct -/

section Names

variable {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {B : _root_.Address} {cb : Ixon.Constant}
  {ms : Array Ixon.MutConst}

/-- The constructors of one member have distinct keys. -/
theorem pointMemberCtors_names_nodup (ht : t.check = .ok ())
    (hrec : ModeledBlockRecord E₀ B cb ms) (hsize : ms.size < 2 ^ 39)
    (hbnd : ∀ (i : Nat) (ind : Ixon.Inductive), ms[i]? = some (.indc ind) →
      ind.ctors.size < 2 ^ 56) (i : Nat) :
    ((pointMemberCtors t E B cb ms i).map (·.cv.name)).Nodup := by
  obtain ⟨-, hC, -⟩ := point_keys_distinct ht hrec hsize
  cases hm : ms[i]? with
  | none =>
    rw [pointMemberCtors_of_none hm]
    exact List.nodup_nil
  | some m =>
    obtain ⟨ind, rfl⟩ := hrec.inds i m hm
    rw [pointMemberCtors_of_mem hm, List.map_filterMap]
    refine List.Pairwise.filterMap _ (fun j j' hne a ha a' ha' heq => ?_) List.nodup_range
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp ha'
    obtain ⟨ct, hct, rfl⟩ := pointCtorSlot_eq hc
    obtain ⟨ct', hct', rfl⟩ := pointCtorSlot_eq hc'
    have hj := (Array.getElem?_eq_some_iff.mp hct).1
    have hj' := (Array.getElem?_eq_some_iff.mp hct').1
    have hb := hbnd i ind hm
    have e : UInt64.size = 18446744073709551616 := rfl
    exact hne (hC i i j j' ind ind hm hm hj hj' (by omega) (by omega) heq).2

/-- **The formers' and constructors' keys are distinct.** -/
theorem point_names_nodup (ht : t.check = .ok ()) (hrec : ModeledBlockRecord E₀ B cb ms)
    (hsize : ms.size < 2 ^ 39)
    (hbnd : ∀ (i : Nat) (ind : Ixon.Inductive), ms[i]? = some (.indc ind) →
      ind.ctors.size < 2 ^ 56) :
    ((pointFormerList t E B cb ms).map (·.cv.name) ++
      (pointCtorList t E B cb ms).map (·.cv.name)).Nodup := by
  obtain ⟨hI, hC, hX⟩ := point_keys_distinct ht hrec hsize
  have h64 : ∀ (i j : Nat) (ind : Ixon.Inductive) (ct : Ixon.Constructor),
      ms[i]? = some (.indc ind) → ind.ctors[j]? = some ct →
      j < ind.ctors.size ∧ j < UInt64.size := by
    intro i j ind ct hm hct
    have hj := (Array.getElem?_eq_some_iff.mp hct).1
    have hb := hbnd i ind hm
    have e : UInt64.size = 18446744073709551616 := rfl
    exact ⟨hj, by omega⟩
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · unfold pointFormerList
    rw [List.map_filterMap]
    refine List.Pairwise.filterMap _ (fun i i' hne a ha a' ha' heq => ?_) List.nodup_range
    obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨f', hf', rfl⟩ := Option.map_eq_some_iff.mp ha'
    obtain ⟨ind, hm, rfl⟩ := pointFormerSlot_eq hf
    obtain ⟨ind', hm', rfl⟩ := pointFormerSlot_eq hf'
    exact hne (hI i i' ind ind' hm hm' heq)
  · unfold pointCtorList
    rw [List.map_flatMap]
    refine List.pairwise_flatMap.mpr
      ⟨fun i _ => pointMemberCtors_names_nodup ht hrec hsize hbnd i, ?_⟩
    refine List.Pairwise.imp (fun {i i'} hne x hx y hy hxy => ?_) List.nodup_range
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hy
    obtain ⟨ind, j, ct, hm, hct, rfl⟩ := mem_pointMemberCtors.mp hc
    obtain ⟨ind', j', ct', hm', hct', rfl⟩ := mem_pointMemberCtors.mp hc'
    obtain ⟨hj, hj64⟩ := h64 i j ind ct hm hct
    obtain ⟨hj', hj64'⟩ := h64 i' j' ind' ct' hm' hct'
    exact hne (hC i i' j j' ind ind' hm hm' hj hj' hj64 hj64' hxy).1
  · intro a ha b hb hab
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, ind, hm, rfl⟩ := mem_pointFormerList.mp hf
    obtain ⟨i', ind', j, ct, hm', hct, rfl⟩ := mem_pointCtorList.mp hc
    exact hX i i' j ind ind' hm hm' (Array.getElem?_eq_some_iff.mp hct).1 hab

end Names

/-! ## A member's former and a constructor's annotation -/

section Facts

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E₀ E : Ixon.Env}
  {bAddr B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {n : Nat}

/-- **A member's former at a prefix the step is handed**: the reading of its type over the step's
store and its canonical annotation (`FormerRead`), the annotation's relation to the reading, the
front door at the prefix, the telescope into a sort with the member's binder count, the reading
over the run's store at its projection address, and the member's counts below `2 ^ 56`. -/
theorem point_former_facts (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hst : StepStore calls t E₀ E) (hrec : ModeledBlockRecord E₀ B cb ms)
    (hchk : ∀ k < ms.size, MutsMemberCheckedAtFullAt calls bAddr t B ms k n)
    (hmod : ModeledAt E B) {env : Ix.Kernel.Env .anon}
    (hinv : Decl.PrefixInv.{u} E t (some n) env) (hstored : Decl.UsedRefsStored t env cb)
    (hfresh : ∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none)
    (hid : ∀ x, ConstAddrOf B cb x → keyOf t x = .id x)
    {i : Nat} {ind : Ixon.Inductive} (hmem : ms[i]? = some (.indc ind)) :
    FormerRead t E B cb ms i ind (pointMemberType t E B cb ms ind)
        (pointMemberAnn t E B cb ms i ind) ∧
      Annotates (pointMemberAnn t E B cb ms i ind) (pointMemberType t E B cb ms ind) ∧
      Ix.Kernel.Semantics.ConstantValRunJ Ix.Kernel.Model.rulesJ env
        ⟨Core.keyOf t (Core.iprjAddr B i), List.range ind.lvls.toNat,
          pointMemberType t E B cb ms ind⟩
        (pointMemberAnn t E B cb ms i ind) ∧
      (∃ l, (pointMemberAnn t E B cb ms i ind).resultSort = some l) ∧
      (pointMemberAnn t E B cb ms i ind).piArity = ind.params.toNat + ind.indices.toNat ∧
      (∀ caps : IndCaps .anon, Reads t E₀ (Core.iprjAddr B i)
        (.indInfo ⟨Core.keyOf t (Core.iprjAddr B i), List.range ind.lvls.toNat,
          pointMemberType t E B cb ms ind⟩ caps)) ∧
      ind.params.toNat < 2 ^ 56 ∧ ind.indices.toNat < 2 ^ 56 ∧ ind.ctors.size < 2 ^ 56 := by
  obtain ⟨ty₀, hty, -, hlbb, hdef, hfv, hnp, hni, hnc, hreads⟩ :=
    point_member_reads ht hS hst hrec hchk hmem
  have hT : pointMemberType t E B cb ms ind = ty₀ := pointReadOr_of_ok hty
  have hiAddr : ConstAddrOf B cb (Core.iprjAddr B i) :=
    Or.inr ⟨ms, i, .indc ind, hrec.muts, hmem, Or.inl rfl⟩
  have hfreshM : ∀ (k : Nat) (ind' : Ixon.Inductive), ms[k]? = some (.indc ind') →
      env.find? (Core.keyOf t (Core.iprjAddr B k)) = none := fun k ind' hk =>
    hfresh (Core.iprjAddr B k) (Or.inr ⟨ms, k, .indc ind', hrec.muts, hk, Or.inl rfl⟩)
  have hidI : Core.keyOf t (Core.iprjAddr B i) = .id (Core.iprjAddr B i) :=
    hid (Core.iprjAddr B i) hiAddr
  have hfree : Decl.KeyFree (Core.keyOf t (Core.iprjAddr B i)) := by
    rw [hidI]
    exact keyFree_id _
  obtain ⟨ty', hcanon, hann, hcheck, -, hsort, harity⟩ :=
    pointFormer_of_member ht hst hinv (hst.held hrec.record) hrec.muts hmem
      (fun k ind' hk => hst.held (hrec.former k ind' hk)) hrec.inds
      (hchk i (Array.getElem?_eq_some_iff.mp hmem).1) hmod hty hlbb hdef hfv hstored hfreshM
      hfree
  have hA : pointMemberAnn t E B cb ms i ind = ty' :=
    pointAnnOr_of_some (by rw [hT]; exact hcanon)
  obtain ⟨type', hrun, hcv⟩ := hcheck
  have htype : type' = ty' := (congrArg Ix.Kernel.ConstantVal.type hcv).symm
  rw [htype] at hrun
  rw [hT, hA]
  exact ⟨⟨hty, hlbb, hdef, hcanon⟩, hann, hrun, hsort, harity, hreads, hnp, hni, hnc⟩

/-- **A constructor's stored type annotates its reading**: the slot's load in the member's walked
check represents the canonical annotation of the reading, which annotates it. -/
theorem point_ctor_annot (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hst : StepStore calls t E₀ E) (hrec : ModeledBlockRecord E₀ B cb ms)
    (hchk : ∀ k < ms.size, MutsMemberCheckedAtFullAt calls bAddr t B ms k n)
    {i : Nat} {ind : Ixon.Inductive} (hmem : ms[i]? = some (.indc ind))
    {j : Nat} (hj : j < ind.ctors.size) {ct : Ixon.Constructor} (hct : ind.ctors[j]? = some ct)
    {cty₀ cty' : Ix.Kernel.Expr .anon} (hread : CtorRead t E B cb ms i j ct cty₀ cty') :
    Annotates cty' cty₀ := by
  have hbound : Bounded calls := (hst.good Ix.Kernel.Env.empty none).2
  have hchki := hchk i (Array.getElem?_eq_some_iff.mp hmem).1
  have hi39 := member_idx_lt hbound hmem hchki
  obtain ⟨b, hb, hlv, hnp, hnc, hslots⟩ := ctorSlots_at hbound hS hrec hmem hchki
  obtain ⟨bp, ptr, h, h', m₁, m₂, cs, cs₂, nl, ty, pb, mi, sl, np, nf, us, v₂, ev, hsub, hbp, hld,
    hsl, hnl, hnpv, hext₁, evS, hmemS⟩ := hslots j hj
  have hg : Core.Good ⟨E, Ix.Kernel.Env.empty, t, none⟩ cs :=
    (hst.good Ix.Kernel.Env.empty none).sub hsub
  have hz : ZMod.val ((i : Nat) : F) = i :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  have hjv : ZMod.val ((j : Nat) : F) = j :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  obtain ⟨hcidx, hty, hlbb, hdef, hcanon⟩ := hread
  have hblock_b : recordOf E (Core.ixAddr b) = some cb := by
    rw [hb]
    exact hst.held hrec.record
  have hmemF : ms[ZMod.val ((i : Nat) : F)]? = some (.indc ind) := by
    rw [hz]
    exact hmem
  have hctF : ind.ctors[ZMod.val ((j : Nat) : F)]? = some ct := by
    rw [hjv]
    exact hct
  have hcidxF : ct.cidx.toNat = ZMod.val ((j : Nat) : F) := by
    rw [hjv]
    exact hcidx
  have htyB : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t (Core.ixAddr b) ms)).read ct.typ = .ok cty₀ := by
    rw [hb]
    exact hty
  obtain ⟨tyPtr, blkPtr, b', ty', R', -, -, -, -, -, -, hcanon', -, hann, -, -⟩ :=
    LoadedReads.ctor_load_canon ht hg.1 hg.2 hbp ev hblock_b hrec.muts hmemF hctF hcidxF htyB
      hlbb hdef
  rw [hz] at hcanon'
  have hty' : ty' = cty' := Option.some.inj (hcanon'.symm.trans hcanon)
  rw [← hty']
  exact hann

end Facts

/-! ## The stage of the formers -/

/-- A key the prefix does not store, and no former carries, is not stored at the stage. -/
theorem pointStage_find_none {env : Ix.Kernel.Env .anon} {formers : List FormerRec}
    {k : Ix.Kernel.Key .anon} (henv : env.find? k = none)
    (hnot : ∀ f ∈ formers, f.cv.name ≠ k) :
    (Decl.Point.stage env formers).find? k = none := by
  cases hf : (Decl.Point.stage env formers).find? k with
  | none => rfl
  | some x =>
    exfalso
    rcases find?_append_cases (env := env) ((formers.map (·.stored)).reverse) hf with hm | ho
    · obtain ⟨f, hf', rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hm)
      exact hnot f hf' (Ix.Kernel.Semantics.Env.find?_name hf)
    · rw [henv] at ho
      cases ho

/-! ## The evidence -/

/-- **The refinement of the block's arm, as the step reads it** (`PointEvidence` with the
prefix's store clause `HashKeyed` among the premises): at every environment that satisfies the
prefix invariant at the limit of the members' checks, keys its constants at addresses of
32 bytes, stores what the block uses and none of its constant addresses, keys them as input keys
and stores the `PUnit` pin, the one-point interface holds with formers and constructors that are
the block's readings over the step's store, every constant address of the block has a reading
over the run's store among the block's declared constants, and the members' counts are below
`2 ^ 56`. Producer: `pointEvidenceK_of_members`. -/
def PointEvidenceK (t : Ix.Kernel.RoleTable) (E₀ E : Ixon.Env) (B : _root_.Address)
    (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (n : Nat) : Prop :=
  ∀ env : Ix.Kernel.Env .anon, Decl.PrefixInv.{u} E t (some n) env → HashKeyed t env →
    Decl.UsedRefsStored t env cb →
    (∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none) →
    (∀ x, ConstAddrOf B cb x → keyOf t x = .id x) → PUnitPin env →
    ∃ (formers : List FormerRec) (ctors : List CtorRec) (blk : List (ConstantInfo .anon)),
      PointBlock env blk formers ctors ∧ PointReads t E B cb ms formers ctors ∧
      (∀ x, ConstAddrOf B cb x → ∃ ci₀ ∈ blk, ci₀.name = keyOf t x ∧ Reads t E₀ x ci₀) ∧
      ∀ (i : Nat) (ind : Ixon.Inductive), ms[i]? = some (.indc ind) →
        ind.params.toNat < 2 ^ 56 ∧ ind.indices.toNat < 2 ^ 56 ∧ ind.ctors.size < 2 ^ 56

section Evidence

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E₀ E : Ixon.Env}
  {bAddr B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {n : Nat}

/-- **The evidence, from the walked checks of the block's members.** The block's shape
(`hgate`) routes the dispatch to the modeled branch in every good run; the formers are the
members' (`point_former_facts`), stored at the stage (`pointStage_coreFacts`), where each
member's constructor loop types its constructors (`pointCtors_of_member`). -/
theorem pointEvidenceK_of_members (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hst : StepStore calls t E₀ E) (hrec : ModeledBlockRecord E₀ B cb ms)
    (hchk : ∀ k < ms.size, MutsMemberCheckedAtFullAt calls bAddr t B ms k n)
    (hP : HashedBlockProjectionsHeld E) (hgate : PointShape E B ms) :
    PointEvidenceK.{u} t E₀ E B cb ms n := by
  intro env hinv hkeys hstored hfresh hid hpin
  have hbound : Bounded calls := (hst.good env none).2
  have hsize : ms.size < 2 ^ 39 := by
    rcases Nat.eq_zero_or_pos ms.size with h0 | hpos
    · omega
    · exact mutsMemberAt_size_lt hbound (hchk 0 hpos)
  have hrecAt : Ix.Cert.recordAt E B = some cb :=
    recordAt_of_recordOf hst.decoded (hst.held hrec.record)
  have hmod : ModeledAt E B := PointShape.modeledAt hinv hrecAt hrec.muts hgate
  have hF := fun (i : Nat) (ind : Ixon.Inductive) (hm : ms[i]? = some (.indc ind)) =>
    point_former_facts ht hS hst hrec hchk hmod hinv hstored hfresh hid hm
  have hbnd : ∀ (i : Nat) (ind : Ixon.Inductive), ms[i]? = some (.indc ind) →
      ind.ctors.size < 2 ^ 56 := fun i ind hm => (hF i ind hm).2.2.2.2.2.2.2.2
  have hnd := point_names_nodup (E := E) ht hrec hsize hbnd
  obtain ⟨-, -, hX⟩ := point_keys_distinct ht hrec hsize
  -- the stage of the formers
  have hPin : PointStageInput E env t B cb ms (pointFormerList t E B cb ms) :=
    { check := ht
      decoded := hst.decoded
      held := hP
      block := hst.held hrec.record
      muts := hrec.muts
      inds := hrec.inds
      formerRec := fun i ind hm => hst.held (hrec.former i ind hm)
      used := hstored
      ctorRead := fun i ind hm k ct hk => by
        obtain ⟨ct', cty₀, hct', hcidx, -, -, -, -, hty, -, hlbb, hdef, -, -⟩ :=
          point_ctor_reads ht hS hst hrec hchk hm (Array.getElem?_eq_some_iff.mp hk).1
        rw [hk] at hct'
        obtain rfl := Option.some.inj hct'
        exact ⟨hcidx, cty₀, hty, hlbb, hdef⟩
      formerOf := fun f hf => by
        obtain ⟨i, ind, hm, rfl⟩ := mem_pointFormerList.mp hf
        exact ⟨i, ind, _, _, {}, hm, rfl, (hF i ind hm).1⟩
      formerAt := fun i ind hm =>
        ⟨_, _, {}, mem_pointFormerList.mpr ⟨i, ind, hm, rfl⟩, (hF i ind hm).1⟩
      nodup := (List.nodup_append.mp hnd).1
      front := fun f hf => by
        obtain ⟨i, ind, hm, rfl⟩ := mem_pointFormerList.mp hf
        exact (hF i ind hm).2.2.1
      key := fun f hf => by
        obtain ⟨i, ind, hm, rfl⟩ := mem_pointFormerList.mp hf
        exact ⟨Core.iprjAddr B i,
          hid (Core.iprjAddr B i) (Or.inr ⟨ms, i, .indc ind, hrec.muts, hm, Or.inl rfl⟩)⟩
      sort := fun f hf => by
        obtain ⟨i, ind, hm, rfl⟩ := mem_pointFormerList.mp hf
        exact (hF i ind hm).2.2.2.1 }
  have hstage := pointStage_coreFacts (lim := some n) hinv hkeys hPin hgate
  have hformers : ∀ (k : Nat) (ind' : Ixon.Inductive), ms[k]? = some (.indc ind') →
      ∃ f ∈ pointFormerList t E B cb ms, f.cv.name = Core.keyOf t (Core.iprjAddr B k) :=
    fun k ind' hk => ⟨_, mem_pointFormerList.mpr ⟨k, ind', hk, rfl⟩, rfl⟩
  have hfreshC : ∀ (i : Nat) (ind : Ixon.Inductive), ms[i]? = some (.indc ind) →
      ∀ j < ind.ctors.size, (Decl.Point.stage env (pointFormerList t E B cb ms)).find?
        (Core.keyOf t (Core.cprjAddr B i j)) = none := by
    intro i ind hm j hj
    refine pointStage_find_none (hfresh (Core.cprjAddr B i j)
      (Or.inr ⟨ms, i, .indc ind, hrec.muts, hm, Or.inr ⟨ind, j, rfl, hj, rfl⟩⟩)) ?_
    intro f hf hname
    obtain ⟨k, indk, hk, rfl⟩ := mem_pointFormerList.mp hf
    exact hX k i j indk ind hk hm hj hname
  have hidC : ∀ (i : Nat) (ind : Ixon.Inductive), ms[i]? = some (.indc ind) →
      ∀ j < ind.ctors.size, ∃ a, Core.keyOf t (Core.cprjAddr B i j) = .id a :=
    fun i ind hm j hj => ⟨Core.cprjAddr B i j, hid (Core.cprjAddr B i j)
      (Or.inr ⟨ms, i, .indc ind, hrec.muts, hm, Or.inr ⟨ind, j, rfl, hj, rfl⟩⟩)⟩
  -- each constructor at the stage
  have hC : ∀ (i : Nat) (ind : Ixon.Inductive) (j : Nat) (ct : Ixon.Constructor),
      ms[i]? = some (.indc ind) → ind.ctors[j]? = some ct →
      CtorRead t E B cb ms i j ct (pointCtorType t E B cb ms ct)
          (pointCtorAnn t E B cb ms i j ct) ∧
        Ix.Kernel.Semantics.ConstantValRunJ Ix.Kernel.Model.rulesJ
          (Decl.Point.stage env (pointFormerList t E B cb ms))
          ⟨Core.keyOf t (Core.cprjAddr B i j), List.range ct.lvls.toNat,
            pointCtorType t E B cb ms ct⟩
          (pointCtorAnn t E B cb ms i j ct) ∧
        (∃ us, Decl.Point.EndsHead (Core.keyOf t (Core.iprjAddr B i)) us
          (ind.params.toNat + ind.indices.toNat) (pointCtorAnn t E B cb ms i j ct)) ∧
        Annotates (pointCtorAnn t E B cb ms i j ct) (pointCtorType t E B cb ms ct) := by
    intro i ind j ct hm hct
    have hj : j < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hct).1
    obtain ⟨ct', cty₀, cty', hct', hread, -, -, hrun, us, hends⟩ :=
      pointCtors_of_member ht hS hst (hst.held hrec.record) hrec.muts hm
        (hst.held (hrec.former i ind hm)) hrec.inds (hchk i (Array.getElem?_eq_some_iff.mp hm).1)
        hmod hstage hstored hformers (hfreshC i ind hm) (hidC i ind hm) j hj
    rw [hct] at hct'
    obtain rfl := Option.some.inj hct'
    have hann := point_ctor_annot ht hS hst hrec hchk hm hj hct hread
    obtain ⟨hcidx, hty, hlbb, hdef, hcanon⟩ := hread
    have hT : pointCtorType t E B cb ms ct = cty₀ := pointReadOr_of_ok hty
    have hA : pointCtorAnn t E B cb ms i j ct = cty' :=
      pointAnnOr_of_some (by rw [hT]; exact hcanon)
    rw [hT, hA]
    exact ⟨⟨hcidx, hty, hlbb, hdef, hcanon⟩, hrun, ⟨us, hends⟩, hann⟩
  refine ⟨pointFormerList t E B cb ms, pointCtorList t E B cb ms,
    (pointFormerList t E B cb ms).map (·.declared) ++ (pointCtorList t E B cb ms).map (·.declared),
    ?_, ?_, ?_, fun i ind hm =>
      ⟨(hF i ind hm).2.2.2.2.2.2.1, (hF i ind hm).2.2.2.2.2.2.2.1,
        (hF i ind hm).2.2.2.2.2.2.2.2⟩⟩
  · -- the one-point interface
    exact
      { members := fun ci => List.mem_append
        nodup := hnd
        keyF := fun f hf => by
          obtain ⟨i, ind, hm, rfl⟩ := mem_pointFormerList.mp hf
          exact ⟨Core.iprjAddr B i,
            hid (Core.iprjAddr B i) (Or.inr ⟨ms, i, .indc ind, hrec.muts, hm, Or.inl rfl⟩)⟩
        keyC := fun c hc => by
          obtain ⟨i, ind, j, ct, hm, hct, rfl⟩ := mem_pointCtorList.mp hc
          exact hidC i ind hm j (Array.getElem?_eq_some_iff.mp hct).1
        formerFront := fun f hf => by
          obtain ⟨i, ind, hm, rfl⟩ := mem_pointFormerList.mp hf
          exact (hF i ind hm).2.2.1
        formerAnnot := fun f hf => by
          obtain ⟨i, ind, hm, rfl⟩ := mem_pointFormerList.mp hf
          exact (hF i ind hm).2.1
        formerSort := fun f hf => by
          obtain ⟨i, ind, hm, rfl⟩ := mem_pointFormerList.mp hf
          exact (hF i ind hm).2.2.2.1
        ctorFront := fun c hc => by
          obtain ⟨i, ind, j, ct, hm, hct, rfl⟩ := mem_pointCtorList.mp hc
          exact (hC i ind j ct hm hct).2.1
        ctorAnnot := fun c hc => by
          obtain ⟨i, ind, j, ct, hm, hct, rfl⟩ := mem_pointCtorList.mp hc
          exact (hC i ind j ct hm hct).2.2.2
        ctorResult := fun c hc => by
          obtain ⟨i, ind, j, ct, hm, hct, rfl⟩ := mem_pointCtorList.mp hc
          obtain ⟨us, hends⟩ := (hC i ind j ct hm hct).2.2.1
          refine ⟨_, mem_pointFormerList.mpr ⟨i, ind, hm, rfl⟩, us, ?_⟩
          show Decl.Point.EndsHead (Core.keyOf t (Core.iprjAddr B i)) us
            (pointMemberAnn t E B cb ms i ind).piArity (pointCtorAnn t E B cb ms i j ct)
          rw [(hF i ind hm).2.2.2.2.1]
          exact hends
        pin := hpin }
  · -- the readings
    exact
      { formerOf := fun f hf => by
          obtain ⟨i, ind, hm, rfl⟩ := mem_pointFormerList.mp hf
          exact ⟨i, ind, _, _, {}, hm, rfl, (hF i ind hm).1⟩
        formerAt := fun i ind hm =>
          ⟨_, _, {}, mem_pointFormerList.mpr ⟨i, ind, hm, rfl⟩, (hF i ind hm).1⟩
        ctorOf := fun c hc => by
          obtain ⟨i, ind, j, ct, hm, hct, rfl⟩ := mem_pointCtorList.mp hc
          exact ⟨i, ind, j, ct, _, _, hm, hct, rfl, (hC i ind j ct hm hct).1⟩
        ctorAt := fun i ind j hm hj => by
          obtain ⟨ct, hct⟩ : ∃ ct, ind.ctors[j]? = some ct :=
            ⟨_, Array.getElem?_eq_some_iff.mpr ⟨hj, rfl⟩⟩
          exact ⟨ct, _, _, hct, mem_pointCtorList.mpr ⟨i, ind, j, ct, hm, hct, rfl⟩,
            (hC i ind j ct hm hct).1⟩ }
  · -- every constant address has a reading among the declared constants
    intro x hx
    rcases hx with ⟨-, hsa⟩ | ⟨ms', i, m, hms', hm, hx⟩
    · exfalso
      rcases hsa with ⟨d, hd⟩ | ⟨rc, hd⟩ | ⟨ax, hd⟩ | ⟨q, hd⟩ <;>
        (rw [hrec.muts] at hd; cases hd)
    · have hms : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hrec.muts)
      subst hms
      obtain ⟨ind, rfl⟩ := hrec.inds i m hm
      rcases hx with rfl | ⟨ind', j, hind, hj, rfl⟩
      · exact ⟨_, List.mem_append_left _
          (List.mem_map_of_mem (mem_pointFormerList.mpr ⟨i, ind, hm, rfl⟩)), rfl,
          (hF i ind hm).2.2.2.2.2.1 {}⟩
      · obtain rfl := Ixon.MutConst.indc.inj hind
        obtain ⟨ct, hct⟩ : ∃ ct, ind.ctors[j]? = some ct :=
          ⟨_, Array.getElem?_eq_some_iff.mpr ⟨hj, rfl⟩⟩
        obtain ⟨ct', cty₀, hct', -, -, -, -, -, hty, -, -, -, -, hreads⟩ :=
          point_ctor_reads ht hS hst hrec hchk hm hj
        rw [hct] at hct'
        obtain rfl := Option.some.inj hct'
        have hT : pointCtorType t E B cb ms ct = cty₀ := pointReadOr_of_ok hty
        refine ⟨_, List.mem_append_right _
          (List.mem_map_of_mem (mem_pointCtorList.mpr ⟨i, ind, j, ct, hm, hct, rfl⟩)), rfl, ?_⟩
        show Reads t E₀ (Core.cprjAddr B i j)
          (.ctorInfo ⟨Core.keyOf t (Core.cprjAddr B i j), List.range ct.lvls.toNat,
            pointCtorType t E B cb ms ct⟩ ct.params.toNat ct.fields.toNat)
        rw [hT]
        exact hreads

end Evidence

/-! ## The unit step without the evidence -/

/-- **`UnitStep` for a block on the constructors-only route, from the walked checks of its
members.** The evidence is `pointEvidenceK_of_members`, the load facts `pointLoadsFrom`. The
named hypotheses left are the block's shape (`hgate`) and the unstored roles (`hunb`). -/
theorem unitStep_pointBlock_of_members {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {R E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon} {lim : Option Nat}
    {bAddr B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {n : Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hshape : TableShape.{u} t (fun _ => True) R envT)
    (hrec : ModeledBlockRecord E₀ B cb ms)
    (hchk : ∀ k < ms.size, MutsMemberCheckedAtFullAt calls bAddr t B ms k n)
    (hlim : lim = some n)
    (hgate : PointShape E B ms)
    (hunb : ∀ x, ConstAddrOf B cb x → ∀ r, ¬ StoredRole r → t.addressOf? r ≠ some x)
    (hP : HashedBlockProjectionsHeld E)
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb) :
    UnitStep.{u} (PointX.{u} t E) t envT E₀ E lim B cb := by
  subst hlim
  intro env hext hnd hinv hXe href hfresh
  obtain ⟨⟨⟨hreg, hkeys⟩, haux⟩, hlv⟩ := hXe
  have htwf : t.wf = true := hinv.tableWf
  have hstored : Decl.UsedRefsStored t env cb :=
    usedRefsStored_of_cover (hcover env ⟨hext, href, hfresh⟩) hinert
  have hid : ∀ x, ConstAddrOf B cb x → keyOf t x = .id x := fun x hx =>
    key_id_of_fresh htwf hshape hext hnd (hfresh x hx) (hunb x hx)
  have hpin : PUnitPin env := punitPin_of_shape hshape hext hnd
  obtain ⟨formers, ctors, blk, hb, hR, hreads, hbounds⟩ :=
    pointEvidenceK_of_members ht hS hst hrec hchk hP hgate env hinv hkeys hstored hfresh hid hpin
  have hblockE : recordOf E B = some cb := hst.held hrec.record
  have hrecAt : Ix.Cert.recordAt E B = some cb := recordAt_of_recordOf hst.decoded hblockE
  have hmod : ModeledAt E B := PointShape.modeledAt hinv hrecAt hrec.muts hgate
  have heq : installed env formers ctors = ⟨newConsts formers ctors ++ env.consts⟩ :=
    installed_eq env formers ctors
  have hextN : Ix.Kernel.EnvExt env ⟨newConsts formers ctors ++ env.consts⟩ := by
    have h := hb.envExt
    rw [heq] at h
    exact h
  -- the install, as the store reads it
  have hI : PointInstall ⟨E, env, t, some n⟩ (newConsts formers ctors) B cb ms :=
    { check := ht
      decoded := hst.decoded
      held := hP
      block := hblockE
      muts := hrec.muts
      inds := hrec.inds
      formerRec := fun i ind hm => hst.held (hrec.former i ind hm)
      ctorRec := fun i ind hm j hj => hst.held (hrec.ctors i ind hm j hj)
      bounds := hbounds
      used := fun i hi x hx => by
        obtain ⟨ci, hci⟩ := hstored i hi x hx
        exact ⟨ci, hextN.find hci⟩
      former := fun i ind hm => by
        obtain ⟨ty₀, ty', caps, hf, hread, hlbb, hdef, hcanon⟩ := hR.formerAt i ind hm
        exact ⟨ty₀, ty', hread, hlbb, hdef, hcanon, hb.find_pointFormer hf⟩
      ctor := fun i ind hm j hj => by
        obtain ⟨ct, cty₀, cty', hct, hc, hcidx, hread, hlbb, hdef, hcanon⟩ :=
          hR.ctorAt i ind j hm hj
        exact ⟨ct, cty₀, cty', hct, hcidx, hread, hlbb, hdef, hcanon, hb.find_pointCtor hc⟩
      newName := hR.newName hb
      newFind := fun ci hci => by
        have h := hb.find_new hci
        rw [heq] at h
        exact h }
  -- the prefix invariant after the install
  have hinv₂ : Decl.PrefixInv.{u} E t (some n) (installed env formers ctors) :=
    hb.prefixInv hinv (pointLoadsFrom.{u} t E B cb ms n env _ hI hinv haux
      (fun k ind hk => hfresh (Core.iprjAddr B k)
        (Or.inr ⟨ms, k, .indc ind, hrec.muts, hk, Or.inl rfl⟩)) hgate)
  rw [heq] at hinv₂
  -- the carried clause after the install
  have hreg₂ : LateRegistry.{u} t E (installed env formers ctors) := by
    refine hb.lateRegistry hreg (fun P cm ip hP' hcm hinfo => ?_)
    obtain ⟨f, hf, hname⟩ := hP'
    obtain ⟨i, ind, ty₀, ty', caps, hm, rfl, -⟩ := hR.formerOf f hf
    have hPx : P = Core.iprjAddr B i :=
      Core.keyOf_inj htwf (a₁ := P) (a₂ := Core.iprjAddr B i) hname.symm
    subst hPx
    have hrecP : Ix.Cert.recordAt E (Core.iprjAddr B i) =
        some (memberProjection B i (.indc ind)) :=
      recordAt_of_recordOf hst.decoded (hst.held (hrec.former i ind hm))
    rw [hrecP] at hcm
    obtain rfl := Option.some.inj hcm
    rw [memberProjection_info] at hinfo
    injection hinfo with hip
    rw [← hip]
    exact hmod
  have hkeys₂ : HashKeyed t (installed env formers ctors) := by
    refine hb.hashKeyed htwf hkeys (fun x hx => ?_)
    rcases hR.newName hb x hx with ⟨i, ind, hm, hname⟩ | ⟨i, ind, j, hm, hj, hname⟩
    · exact ⟨_, hname, address_size_of_record hS (hrec.former i ind hm)⟩
    · exact ⟨_, hname, address_size_of_record hS (hrec.ctors i ind hm j hj)⟩
  have haux₂ := hb.auxRootSynced haux
  have hlv₂ := hb.lvClauses hlv
  rw [heq] at hreg₂ hkeys₂ haux₂ hlv₂
  refine ⟨newConsts formers ctors, hb.freshChain.nodup, hb.freshChain.fresh, hinv₂,
    ⟨⟨⟨hreg₂, hkeys₂⟩, haux₂⟩, hlv₂⟩, ?_, ?_⟩
  · -- every constant address holds a new constant storing a reading of it
    intro x hx
    obtain ⟨ci₀, hci₀, hname₀, hread₀⟩ := hreads x hx
    obtain ⟨ci, hfind, hsto⟩ := hb.stored ci₀ hci₀
    have hnm : ci.name = keyOf t x := (Ix.Kernel.Semantics.Env.find?_name hfind).trans hname₀
    have hmem : ci ∈ newConsts formers ctors := by
      rcases hb.find_cases hfind with h | ⟨f, hf, rfl⟩ | ⟨c, hc, rfl⟩
      · rw [hname₀, hfresh x hx] at h
        cases h
      · exact hb.mem_new_former hf
      · exact hb.mem_new_ctor hc
    exact ⟨ci, hmem, ci₀, hnm, hread₀, hsto⟩
  · intro ci hci
    left
    rcases hR.newName hb ci hci with ⟨i, ind, hm, hname⟩ | ⟨i, ind, j, hm, hj, hname⟩
    · exact ⟨Core.iprjAddr B i, Or.inr ⟨ms, i, .indc ind, hrec.muts, hm, Or.inl rfl⟩, hname⟩
    · exact ⟨Core.cprjAddr B i j,
        Or.inr ⟨ms, i, .indc ind, hrec.muts, hm, Or.inr ⟨ind, j, rfl, hj, rfl⟩⟩, hname⟩

end IxVM.Refinement.Typing
