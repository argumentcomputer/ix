import IxVMRefinement.Assembly.NativeFormerLength
import IxVMRefinement.Assembly.PointUseSites
import IxVMRefinement.Assembly.FamilyArm
import IxVMRefinement.Assembly.TypingRecLatePins
import IxVMRefinement.Assembly.TypingDefnBlock
import IxVMRefinement.Claim.TopRec
import IxVMRefinement.Claim.TopCheckFacts
import IxVMRefinement.L1.TraceRecords

/-! # The circuit's dispatch on a block, in a run and at a store

`KernelModeled::block_is_modeled` decides whether a block is checked as one ordinary inductive
family (answer `0`) or against a model (any other answer). Three predicates read that answer:
`NativeRouteAt calls B` and `ModeledRouteAt calls B` (every observation of the dispatch on `B`
in the run answers `0`, or answers non-zero; both hold where the run has no observation), and
the store-level `NativeAt E B` (some good run answers `0`) with its negation `ModeledAt E B`.

They are tied together where the answer is a function of the store's records. Goodness of a
run is relative to a store: nothing relates the bytes two separate runs hash at an address the
store does not hold. So the functionality that can be asked is `BlockRouteFunctional E`: two
good observations at one block agree where the store holds every canonical record the first
one hashed (`L1.CanonicalHashCoverage`). A step's store covers its run, so one observation in
the run fixes the answer of every other observation in the run and of every good run:

* `Claim.induct_dispatch_obs`, `Claim.MemberCheckedLimAt.dispatch`: the walk's check of an
  inductive member of a block observes the dispatch on the block;
* `nativeRouteAt_of_obs`, `modeledRouteAt_of_obs`, `modeledAt_of_obs`, `route_cases`: from one
  observation in the run, under `BlockRouteFunctional`;
* `oneTypeBlock_route_cases`, `modeled_of_not_nativeRoute`: a top-walked block of one inductive
  type is on the native route in the run and at the store, or on the modeled route in the run
  and at the store;
* `modeledAt_of_route`: the bridge from the run-level modeled route to the store-level one;
* `modeledRouteAt_of_multi`: a block of two or more inductive types is on the modeled route,
  with no functionality premise (the dispatch's specification);
* `Claim.TopWalkCore.otherBlock_cases`: a top-walked block that is no block of definitions and
  no block of one inductive type is a block of two or more inductive types or a block of
  recursors (a block of mixed kinds is refused: `TopWalkCore.uniform`);
* `RecFamilyAt`, `RecFamilyAt.unique`, `RecFamilyAt.native_of_parent`,
  `Claim.TopWalkCore.recFamily_nativeRoute`: the family of a standalone recursor record, read
  off the record and the store, and that a recursor whose check found a native parent has that
  family on the native route.
-/

universe u

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

/-- **Every check of an inductive value dispatches on its block**: `check_const` on an `Induct`
value observes `KernelModeled::block_is_modeled` on the value's block pointer, among its
calls, at an extension of its heap. -/
theorem induct_dispatch_obs
    {rc nl typePtr np ni nc safety blockArg index addr result : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (observed : ObsFn Obs.W "KernelCheck::check_const"
      [rc, .construct "KernelTypes::KConstantInfo" "Induct"
        [nl, typePtr, np, ni, nc, safety, blockArg, index], addr] h result h' calls) :
    ∃ (before : Heap F) (value : SourceValue F) (after : Heap F) (children : List (Call F)),
      ObsFn Obs.W "KernelModeled::block_is_modeled" [blockArg] before value after children ∧
      Heap.Extends h before ∧ ∀ call ∈ children, call ∈ calls := by
  match Obs.«KernelCheck::check_const».obs observed with
  | .Axiom_n1 (hv37 := shape) ..
  | .Axiom_other_n0 (hv37 := shape) ..
  | .Axiom_other_other (hv37 := shape) ..
  | .Defn (hv269 := shape) ..
  | .Thm (hv526 := shape) ..
  | .Opaque (hv825 := shape) ..
  | .Quot (hv1076 := shape) .. =>
    injection shape with _ tag _
    exact absurd tag (by decide)
  | .Ctor_n0_n0 (hne1984 := notInduct) ..
  | .Ctor_n0_other (hne1984 := notInduct) ..
  | .Ctor_other_n0 (hne1984 := notInduct) ..
  | .Ctor_other_other (hne1984 := notInduct) ..
  | .Rec_n0 (hne1984 := notInduct) ..
  | .Rec_other (hne1984 := notInduct) .. =>
    exact (notInduct [_, _, _, _, _, _, _, _] rfl rfl).elim
  | .Induct_other_n0 (m1470 := before) (m1492 := after) (v1491 := value) (cs1503 := children)
      (hv1240 := fields) (ev1505 := modeRun) (hc1974 := allCalls) ..
  | .Induct_other_other (m1470 := before) (m1492 := after) (v1491 := value) (cs1503 := children)
      (hv1240 := fields) (ev1505 := modeRun) (hc1983 := allCalls) .. =>
    injection fields with _ _ fields
    injection fields with _ fields
    injection fields with _ fields
    injection fields with _ fields
    injection fields with _ fields
    injection fields with _ fields
    injection fields with _ fields
    injection fields with blockEq _
    subst blockEq
    have member : (⟨"KernelModeled::block_is_modeled", [blockArg], before⟩ : Call F) ∈ calls := by
      rw [allCalls]; simp
    exact ⟨before, value, after, children, modeRun, (observed.call_heap_bounds member).1,
      fun call inside => by rw [allCalls]; simp [inside]⟩
  | .Induct_n0 (m1470 := modeBefore) (m1492 := before) (cs1503 := modeCalls)
      (hv1240 := fields) (ev1505 := modeRun) (hc1634 := allCalls) .. =>
    injection fields with _ _ fields
    injection fields with _ fields
    injection fields with _ fields
    injection fields with _ fields
    injection fields with _ fields
    injection fields with _ fields
    injection fields with _ fields
    injection fields with blockEq _
    subst blockEq
    have member : (⟨"KernelModeled::block_is_modeled", [blockArg], modeBefore⟩ : Call F) ∈
        calls := by
      rw [allCalls]; simp
    exact ⟨modeBefore, .field 0, before, modeCalls, modeRun,
      (observed.call_heap_bounds member).1, fun call inside => by rw [allCalls]; simp [inside]⟩

/-- **The walk's check of a member of a block of inductive types dispatched on the block**: an
observation of `KernelModeled::block_is_modeled` on a pointer to the block's address, within
the run. The member's projection record is the one `projection_addr` hashed (the run store
makes the bytes at its address unique), so the loaded value is an `Induct` value naming the
block. -/
theorem MemberCheckedLimAt.dispatch {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) {t : Ix.Kernel.RoleTable} {bAddr B : _root_.Address}
    {lim : Option Nat} {ms : Array Ixon.MutConst} {i : Nat}
    (hall : ∀ m ∈ ms.toList, ∃ ind, m = Ixon.MutConst.indc ind)
    (hchk : MemberCheckedLimAt calls bAddr t B ms i lim) :
    ∃ (bp r : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (b : Bytes.Address),
      ObsFn Core.W "KernelModeled::block_is_modeled" [bp] h r h' cs ∧
      (∀ cl ∈ cs, cl ∈ calls) ∧ Bytes.RepAddressRef Core.addrTy h b bp ∧
      Core.ixAddr b = B := by
  obtain ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmem, hblk, ev_pa, -, hsub_pa,
    -, -, ev_ld, -, hsub_ld, hld, ev_chk, -, hsub_chk⟩ := hchk
  obtain ⟨b', hb', rfl⟩ := hblk
  obtain ⟨-, -, -, mc, a', hget', ha', hproj, hhashed⟩ :=
    L1.projection_addr_hashed_spec hmem hb' ev_pa
  obtain ⟨iv, hiv⟩ : ∃ iv, ((i : F)).val = iv := ⟨_, rfl⟩
  rw [hiv] at hget' hproj hhashed
  obtain ⟨ind, rfl⟩ := hall mc (List.mem_of_getElem? hget')
  -- the projection record the walk loaded is the one `projection_addr` hashed
  obtain ⟨raw, cp, hsz, hh, hba, hx, -, hhead⟩ := get_ci_head ha' ev_ld
  have hX : Address.blake3Pure (Ixon.serConstant
      ⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b') iv (.indc ind), #[], #[], #[], #[]⟩) =
      Core.ixAddr a' := hproj.symm
  have hraw : raw = Ixon.serConstant
      ⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b') iv (.indc ind), #[], #[], #[], #[]⟩ :=
    hS.hashed_inj (Core.hashed_mono hsub_ld hh) (Core.hashed_mono hsub_pa hhashed)
      (hba.trans hX.symm)
  have hwf : (⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b') iv (.indc ind),
      #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF :=
    L1.projConstant_wireWF_iPrj iv.toUInt64 b'
  rw [hraw, Ixon.Verify.deConstantExact_serConstant _ hwf] at hx
  injection hx with hcp
  subst hcp
  obtain ⟨cb, ms', ind', -, -, -, nl, ty, np, ni, x_blk, b, hldI, hbrep, hbeq⟩ :=
    hhead.iPrj _ _ rfl
  rw [hld] at hldI
  injection hldI with hv
  subst hv
  obtain ⟨before, value, after, children, obs, hext, hsubc⟩ := induct_dispatch_obs ev_chk
  exact ⟨x_blk, value, before, after, children, b, obs,
    fun cl hcl => hsub_chk cl (hsubc cl hcl),
    Bytes.repAddressRef_heapMono₂ Core.addrTy hext hbrep, hbeq⟩

section Walk

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
  {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}

/-- An array of one element. -/
theorem array_of_size_one {α : Type} (ms : Array α) (h : ms.size = 1) : ∃ m, ms = #[m] := by
  obtain ⟨l⟩ := ms
  cases l with
  | nil =>
    have h2 : ([] : List α).length = 1 := h
    simp at h2
  | cons m l' =>
    cases l' with
    | nil => exact ⟨m, rfl⟩
    | cons m' l'' =>
      have h2 : (m :: m' :: l'').length = 1 := h
      simp only [List.length_cons] at h2
      omega

/-- **The kinds of a top-walked block that is no block of definitions and no block of one
inductive type**: a block of two or more inductive types, or a block of recursors. A block
that mixes kinds is refused by the check of its first member (`TopWalkCore.uniform`), and an
empty block is a block of definitions. -/
theorem TopWalkCore.otherBlock_cases
    (hW : TopWalkCore calls bAddr t seeds E₀ lim Top rank) {B : _root_.Address}
    {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hT : Top B) (hc : recordOf E₀ B = some c) (hcm : c.info = .muts ms)
    (hnd : ¬ Typing.DefnBlock ms) (hone : ∀ ind : Ixon.Inductive, ms ≠ #[.indc ind]) :
    (2 ≤ ms.size ∧ ∀ m ∈ ms.toList, ∃ i, m = Ixon.MutConst.indc i) ∨
      (0 < ms.size ∧ ∀ m ∈ ms.toList, ∃ r, m = Ixon.MutConst.recr r) := by
  have hmem : ∀ (i : Nat) (m : Ixon.MutConst), ms[i]? = some m → m ∈ ms.toList := by
    intro i m hm
    have h1 : ms.toList[i]? = some m := by
      rw [Array.getElem?_toList]
      exact hm
    exact List.mem_of_getElem? h1
  have hpos : 0 < ms.size := by
    rcases Nat.eq_zero_or_pos ms.size with h0 | hp
    · exact (hnd fun i m hm => absurd (Array.getElem?_eq_some_iff.mp hm).1 (by omega)).elim
    · exact hp
  rcases hW.uniform B c ms hT hc hcm with hd | hi | hr
  · exact (hnd fun i m hm => hd m (hmem i m hm)).elim
  · left
    refine ⟨?_, hi⟩
    rcases Nat.lt_or_ge ms.size 2 with hlt | hge
    · exfalso
      obtain ⟨m, rfl⟩ := array_of_size_one ms (by omega)
      obtain ⟨ind, rfl⟩ := hi m (by simp)
      exact hone ind rfl
    · exact hge
  · exact Or.inr ⟨hpos, hr⟩

/-- **The five kinds of a top-walked block record**: an empty block; a non-empty block of
definitions; a block of one inductive type; a block of two or more inductive types; a
non-empty block of recursors. An empty block has no constant address, so it is no unit of the
fold and its step installs nothing (`Typing.unitStep_emptyBlock`). -/
theorem TopWalkCore.block_cases
    (hW : TopWalkCore calls bAddr t seeds E₀ lim Top rank) {B : _root_.Address}
    {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hT : Top B) (hc : recordOf E₀ B = some c) (hcm : c.info = .muts ms) :
    ms.size = 0 ∨ (0 < ms.size ∧ Typing.DefnBlock ms) ∨
      (∃ ind : Ixon.Inductive, ms = #[.indc ind]) ∨
      (2 ≤ ms.size ∧ ∀ m ∈ ms.toList, ∃ i, m = Ixon.MutConst.indc i) ∨
      (0 < ms.size ∧ ∀ m ∈ ms.toList, ∃ r, m = Ixon.MutConst.recr r) := by
  rcases Nat.eq_zero_or_pos ms.size with h0 | hp
  · exact Or.inl h0
  · by_cases hd : Typing.DefnBlock ms
    · exact Or.inr (Or.inl ⟨hp, hd⟩)
    · by_cases hone : ∃ ind : Ixon.Inductive, ms = #[.indc ind]
      · exact Or.inr (Or.inr (Or.inl hone))
      · exact Or.inr (Or.inr (Or.inr
          (hW.otherBlock_cases hT hc hcm hd (fun ind h => hone ⟨ind, h⟩))))

end Walk

end IxVM.Refinement.Claim

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)

/-! ## The dispatch as a function of the store -/

/-- **The dispatch's answer is a function of the store's records**: two observations of
`KernelModeled::block_is_modeled` at one block, each bounded and hashing no collision with the
store `E`, answer alike where `E` holds every canonical record the first one hashed. -/
def BlockRouteFunctional (E : Ixon.Env) : Prop :=
  ∀ (bq₁ bq₂ : SourceValue F) (h₁ h₁' h₂ h₂' : Heap F) (cs₁ cs₂ : List (Call F))
    (bb₁ bb₂ : Bytes.Address) (r₁ r₂ : SourceValue F),
    ObsFn Core.W "KernelModeled::block_is_modeled" [bq₁] h₁ r₁ h₁' cs₁ →
    ObsFn Core.W "KernelModeled::block_is_modeled" [bq₂] h₂ r₂ h₂' cs₂ →
    ¬ View.HashedCollision { env := E } [] cs₁ → Bounded cs₁ →
    L1.CanonicalHashCoverage E cs₁ →
    ¬ View.HashedCollision { env := E } [] cs₂ → Bounded cs₂ →
    Bytes.RepAddressRef Core.addrTy h₁ bb₁ bq₁ → Bytes.RepAddressRef Core.addrTy h₂ bb₂ bq₂ →
    Core.ixAddr bb₁ = Core.ixAddr bb₂ → r₁ = r₂

/-- A store that covers a run's canonical records covers those of a part of the run. -/
theorem canonicalHashCoverage_sub {E : Ixon.Env} {cs calls : List (Call F)}
    (hsub : ∀ cl ∈ cs, cl ∈ calls) (h : L1.CanonicalHashCoverage E calls) :
    L1.CanonicalHashCoverage E cs :=
  fun bytes value hh hsz hx => h bytes value (Core.hashed_mono hsub hh) hsz hx

section Route

variable {c : Core.Ctx} {calls : List (Call F)}

/-- **One native observation in the run puts the block on the native route**: every other
observation of the dispatch on the block in the run answers `0`. -/
theorem nativeRouteAt_of_obs (hfun : BlockRouteFunctional c.E) (hg : Core.Good c calls)
    (hcov : L1.CanonicalHashCoverage c.E calls) {B : _root_.Address}
    (hobs : Claim.NativeObsAt calls B) : NativeRouteAt calls B := by
  obtain ⟨bp, h, h', cs, b, ev, hsub, hb, rfl⟩ := hobs
  intro bp' r' h₂ h₂' cs' b' ev' hsub' hb' hB
  have g₁ := hg.sub hsub
  have g₂ := hg.sub hsub'
  exact (hfun bp bp' h h' h₂ h₂' cs cs' b b' (.field 0) r' ev ev' g₁.1 g₁.2
    (canonicalHashCoverage_sub hsub hcov) g₂.1 g₂.2 hb hb' hB.symm).symm

/-- **One modeled observation in the run puts the block on the modeled route.** -/
theorem modeledRouteAt_of_obs (hfun : BlockRouteFunctional c.E) (hg : Core.Good c calls)
    (hcov : L1.CanonicalHashCoverage c.E calls) {bp r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} {b : Bytes.Address}
    (ev : ObsFn Core.W "KernelModeled::block_is_modeled" [bp] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) (hb : Bytes.RepAddressRef Core.addrTy h b bp)
    (hne : r ≠ .field 0) : ModeledRouteAt calls (Core.ixAddr b) := by
  intro bp' r' h₂ h₂' cs' b' ev' hsub' hb' hB
  have g₁ := hg.sub hsub
  have g₂ := hg.sub hsub'
  have e := hfun bp bp' h h' h₂ h₂' cs cs' b b' r r' ev ev' g₁.1 g₁.2
    (canonicalHashCoverage_sub hsub hcov) g₂.1 g₂.2 hb hb' hB.symm
  rw [← e]
  exact hne

/-- **One modeled observation in the run makes the block modeled at the store**: no good run
answers `0` on it. -/
theorem modeledAt_of_obs (hfun : BlockRouteFunctional c.E) (hg : Core.Good c calls)
    (hcov : L1.CanonicalHashCoverage c.E calls) {bp r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} {b : Bytes.Address}
    (ev : ObsFn Core.W "KernelModeled::block_is_modeled" [bp] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) (hb : Bytes.RepAddressRef Core.addrTy h b bp)
    (hne : r ≠ .field 0) : ModeledAt c.E (Core.ixAddr b) := by
  rintro ⟨bq, h₂, h₂', cs', bb, ev', hnc', hbd', hrep', hB⟩
  have g₁ := hg.sub hsub
  exact hne (hfun bp bq h h' h₂ h₂' cs cs' b bb r (.field 0) ev ev' g₁.1 g₁.2
    (canonicalHashCoverage_sub hsub hcov) hnc' hbd' hb hrep' hB.symm)

/-- **The two routes of a block the run dispatched on**: native in the run and at the store,
or modeled in the run and at the store. -/
theorem route_cases (hfun : BlockRouteFunctional c.E) (hg : Core.Good c calls)
    (hcov : L1.CanonicalHashCoverage c.E calls) {B : _root_.Address}
    (hobs : ∃ (bp r : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (b : Bytes.Address),
      ObsFn Core.W "KernelModeled::block_is_modeled" [bp] h r h' cs ∧
      (∀ cl ∈ cs, cl ∈ calls) ∧ Bytes.RepAddressRef Core.addrTy h b bp ∧
      Core.ixAddr b = B) :
    (NativeRouteAt calls B ∧ NativeAt c.E B) ∨ (ModeledRouteAt calls B ∧ ModeledAt c.E B) := by
  obtain ⟨bp, r, h, h', cs, b, ev, hsub, hb, rfl⟩ := hobs
  by_cases hr : r = .field 0
  · subst hr
    exact Or.inl ⟨nativeRouteAt_of_obs hfun hg hcov ⟨bp, h, h', cs, b, ev, hsub, hb, rfl⟩,
      nativeAt_of_route ev hsub hg hb⟩
  · exact Or.inr ⟨modeledRouteAt_of_obs hfun hg hcov ev hsub hb hr,
      modeledAt_of_obs hfun hg hcov ev hsub hb hr⟩

/-- **The bridge from the run-level modeled route to the store-level one**: where the run
observed the dispatch on the block and every observation in the run answers non-zero, no good
run answers `0`. -/
theorem modeledAt_of_route (hfun : BlockRouteFunctional c.E) (hg : Core.Good c calls)
    (hcov : L1.CanonicalHashCoverage c.E calls) {B : _root_.Address}
    (hroute : ModeledRouteAt calls B)
    (hobs : ∃ (bp r : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (b : Bytes.Address),
      ObsFn Core.W "KernelModeled::block_is_modeled" [bp] h r h' cs ∧
      (∀ cl ∈ cs, cl ∈ calls) ∧ Bytes.RepAddressRef Core.addrTy h b bp ∧
      Core.ixAddr b = B) : ModeledAt c.E B := by
  obtain ⟨bp, r, h, h', cs, b, ev, hsub, hb, rfl⟩ := hobs
  exact modeledAt_of_obs hfun hg hcov ev hsub hb (hroute bp r h h' cs b ev hsub hb rfl)

/-- **A block that is modeled at the store is on the modeled route in every run that is good
for the store**, with no functionality premise. -/
theorem modeledRouteAt_of_modeledAt (hg : Core.Good c calls) {B : _root_.Address}
    (hm : ModeledAt c.E B) : ModeledRouteAt calls B := by
  intro bp r h h' cs b ev hsub hb hB hr
  subst hr
  subst hB
  exact hm (nativeAt_of_route ev hsub hg hb)

end Route

/-! ## A top-walked block -/

section Blocks

variable {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
  {bAddr B : _root_.Address} {cb : Ixon.Constant} {lim : Option Nat}

/-- **The two routes of a top-walked block of one inductive type**: the walk's check of its
member observed the dispatch, so the block is native in the run and at the step's store, or
modeled in the run and at the step's store. The premises are those a top-walked unit is
handed. -/
theorem oneTypeBlock_route_cases (hfun : BlockRouteFunctional E)
    (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hcov : L1.CanonicalHashCoverage E calls) {ind : Ixon.Inductive}
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : (∃ ms, cb.info = .muts ms ∧
        ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t B ms k lim) ∨
      Claim.CheckedLimAt calls bAddr t B lim) :
    (NativeRouteAt calls B ∧ NativeAt E B) ∨ (ModeledRouteAt calls B ∧ ModeledAt E B) := by
  have hm : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim :=
    Claim.membersChecked_of_block hS hrec.record hrec.muts hchk 0 (by simp)
  have hobs := Claim.MemberCheckedLimAt.dispatch hS (ms := #[.indc ind])
    (fun m hmem => ⟨ind, by simpa using hmem⟩) hm
  exact route_cases (c := ⟨E, Ix.Kernel.Env.empty, t, none⟩) hfun
    (hst.good Ix.Kernel.Env.empty none) hcov hobs

/-- **A top-walked block of one inductive type that is off the native route is on the modeled
route**, in the run and at the step's store. -/
theorem modeled_of_not_nativeRoute (hfun : BlockRouteFunctional E)
    (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hcov : L1.CanonicalHashCoverage E calls) {ind : Ixon.Inductive}
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : (∃ ms, cb.info = .muts ms ∧
        ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t B ms k lim) ∨
      Claim.CheckedLimAt calls bAddr t B lim)
    (hnn : ¬ NativeRouteAt calls B) : ModeledRouteAt calls B ∧ ModeledAt E B := by
  rcases oneTypeBlock_route_cases hfun hS hst hcov hrec hchk with ⟨hn, -⟩ | hm
  · exact absurd hn hnn
  · exact hm

/-- **A block of two or more inductive types is on the modeled route**, in the run and at the
step's store: the dispatch's specification answers `1` there. No functionality premise. -/
theorem modeledRouteAt_of_multi (ht : t.check = .ok ()) (hst : StepStore calls t E₀ E)
    {ms : Array Ixon.MutConst} (hc : recordOf E₀ B = some cb) (hcm : cb.info = .muts ms)
    (hsize : 2 ≤ ms.size) (hall : ∀ m ∈ ms.toList, ∃ i, m = Ixon.MutConst.indc i) :
    ModeledRouteAt calls B ∧ ModeledAt E B := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  have hfilter : ms.toList.filter Core.isIndc = ms.toList := by
    apply List.filter_eq_self.mpr
    intro m hm
    obtain ⟨i, rfl⟩ := hall m hm
    rfl
  have hmulti : MultiAt E B := by
    refine ⟨cb, ms, hst.runRecord B cb hc, hcm, ?_⟩
    rw [hfilter, Array.length_toList]
    exact hsize
  have hmod : ModeledAt E B :=
    modeledAt_of_multi (Decl.prefixInv_empty.{0} hst.decoded htwf) hmulti
  exact ⟨modeledRouteAt_of_modeledAt (c := ⟨E, Ix.Kernel.Env.empty, t, none⟩)
    (hst.good Ix.Kernel.Env.empty none) hmod, hmod⟩

end Blocks

/-- **The step of an empty block installs nothing**, for every carried clause and at every
limit: an empty block has no constant address, so the environment the step is asked at is
the environment after it. -/
theorem unitStep_emptyBlock {X : Ix.Kernel.Env .anon → Prop} {t : Ix.Kernel.RoleTable}
    {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env} {lim : Option Nat} {A : _root_.Address}
    {c : Ixon.Constant} {ms : Array Ixon.MutConst} (hc : c.info = .muts ms)
    (h0 : ms.size = 0) : UnitStep.{u} X t envT E₀ E lim A c := by
  intro env hext hnd hinv hXe href hfresh
  have hno : ∀ x, ¬ ConstAddrOf A c x := by
    intro x hx
    rcases hx with ⟨-, hs⟩ | ⟨ms', i, m, hms, hm, -⟩
    · rcases hs with ⟨d, hd⟩ | ⟨rc, hr⟩ | ⟨ax, ha⟩ | ⟨q, hq⟩
      · rw [hc] at hd
        cases hd
      · rw [hc] at hr
        cases hr
      · rw [hc] at ha
        cases ha
      · rw [hc] at hq
        cases hq
    · have e : ms = ms' := Ixon.ConstantInfo.muts.inj (hc.symm.trans hms)
      subst e
      have := (Array.getElem?_eq_some_iff.mp hm).1
      omega
  exact ⟨[], by simp, by simp, hinv, hXe, fun x hx => (hno x hx).elim, by simp⟩

/-! ## The family of a standalone recursor record -/

/-- **The family of a standalone recursor record, read off the record and a store.** The key
of the address `P` heads the domain of the major premise in the reading of the record's type
(`RecMajorTie`, over the run's store `E₀`), and the store `S` holds at `P` the inductive
projection record `ip`: the family is member `ip.idx` of the block `ip.block`. -/
def RecFamilyAt (t : Ix.Kernel.RoleTable) (E₀ S : Ixon.Env) (A : _root_.Address)
    (c : Ixon.Constant) (rc : Ixon.Recursor) (P : _root_.Address) (ip : Ixon.InductiveProj) :
    Prop :=
  RecMajorTie t E₀ A c rc P ∧ ∃ cm, Ix.Cert.recordAt S P = some cm ∧ cm.info = .iPrj ip

/-- **The address heading the major premise is a function of the record.** -/
theorem RecMajorTie.unique {t : Ix.Kernel.RoleTable} (htwf : t.wf = true) {E₀ : Ixon.Env}
    {A : _root_.Address} {c : Ixon.Constant} {rc : Ixon.Recursor} {P₁ P₂ : _root_.Address}
    (h₁ : RecMajorTie t E₀ A c rc P₁) (h₂ : RecMajorTie t E₀ A c rc P₂) : P₁ = P₂ := by
  obtain ⟨ty₁, E₁, hr₁, ha₁, hk₁⟩ := h₁
  obtain ⟨ty₂, E₂, hr₂, ha₂, hk₂⟩ := h₂
  have e : ty₁ = ty₂ := Except.ok.inj (hr₁.symm.trans hr₂)
  subst e
  have hk := majorKey_annotates_eq (rc := rc) ha₁ ha₂
  rw [hk₁, hk₂] at hk
  exact Core.keyOf_inj htwf (Option.some.inj hk)

/-- **The family is a function of the record and the store.** -/
theorem RecFamilyAt.unique {t : Ix.Kernel.RoleTable} (htwf : t.wf = true) {E₀ S : Ixon.Env}
    {A : _root_.Address} {c : Ixon.Constant} {rc : Ixon.Recursor} {P₁ P₂ : _root_.Address}
    {ip₁ ip₂ : Ixon.InductiveProj}
    (h₁ : RecFamilyAt t E₀ S A c rc P₁ ip₁) (h₂ : RecFamilyAt t E₀ S A c rc P₂ ip₂) :
    P₁ = P₂ ∧ ip₁ = ip₂ := by
  obtain ⟨hm₁, cm₁, hrec₁, hi₁⟩ := h₁
  obtain ⟨hm₂, cm₂, hrec₂, hi₂⟩ := h₂
  have eP : P₁ = P₂ := RecMajorTie.unique htwf hm₁ hm₂
  subst eP
  have ec : cm₁ = cm₂ := Option.some.inj (hrec₁.symm.trans hrec₂)
  subst ec
  have ei : Ixon.ConstantInfo.iPrj ip₁ = .iPrj ip₂ := hi₁.symm.trans hi₂
  exact ⟨rfl, Ixon.ConstantInfo.iPrj.inj ei⟩

/-- **The parent the check found is the recursor's family.** -/
theorem RecParent.family {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {A P : _root_.Address} {c : Ixon.Constant}
    {rc : Ixon.Recursor} {ip : Ixon.InductiveProj}
    (hp : RecParent t E env P ip) (htie : RecMajorTie t E₀ A c rc P) :
    RecFamilyAt t E₀ E A c rc P ip :=
  ⟨htie, hp.2.2.1⟩

/-- **A recursor whose check found a native parent has its family on the native route at the
store**: the parent is the family (`RecFamilyAt.unique`), and the check answered `0` on its
block. So a standalone recursor record whose family block is modeled at the store
(`ModeledAt`) has no native parent at any environment. -/
theorem RecFamilyAt.native_of_parent {t : Ix.Kernel.RoleTable} (htwf : t.wf = true)
    {E₀ E : Ixon.Env} {env : Ix.Kernel.Env .anon} {A P P' : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor} {ip ip' : Ixon.InductiveProj}
    (hfam : RecFamilyAt t E₀ E A c rc P ip)
    (hp : RecParent t E env P' ip') (htie : RecMajorTie t E₀ A c rc P') :
    NativeAt E ip.block := by
  obtain ⟨-, e⟩ := RecFamilyAt.unique htwf hfam (RecParent.family hp htie)
  rw [e]
  exact hp.2.2.2

end IxVM.Refinement.Typing

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

/-- **The family block of a top-walked standalone recursor record is on the native route**, in
the run and at a store the run is good for and that covers it, at every limit: the check
computed the block, its dispatch answered `0` (`TopWalkCore.recFamilyNative`), and the answer
is a function of the store. The block is the run store's, with exactly one inductive
member. -/
theorem TopWalkCore.recFamily_nativeRoute {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address} {E₀ : Ixon.Env}
    {lim : Option Nat} {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    {c : Core.Ctx} (hfun : Typing.BlockRouteFunctional c.E) (hg : Core.Good c calls)
    (hcov : L1.CanonicalHashCoverage c.E calls)
    (hW : TopWalkCore calls bAddr t seeds E₀ lim Top rank) {A : _root_.Address}
    {c₀ : Ixon.Constant} {rc : Ixon.Recursor}
    (hT : Top A) (hc : recordOf E₀ A = some c₀) (hinfo : c₀.info = .recr rc) :
    ∃ (B : _root_.Address) (cb : Ixon.Constant) (ms : Array Ixon.MutConst),
      RecFamilyNativeObs calls A B ∧ Typing.NativeRouteAt calls B ∧ Typing.NativeAt c.E B ∧
      recordOf E₀ B = some cb ∧ cb.info = .muts ms ∧
      (ms.toList.filter Specs.Callees.isIndc).length = 1 := by
  obtain ⟨B, cb, ms, hobs, hrec, hcm, hcount, -⟩ := hW.recFamilyNative hT hc hinfo
  exact ⟨B, cb, ms, hobs, Typing.nativeRouteAt_of_obs hfun hg hcov hobs.nativeObs,
    hobs.nativeObs.nativeAt hg, hrec, hcm, hcount⟩

end IxVM.Refinement.Claim
