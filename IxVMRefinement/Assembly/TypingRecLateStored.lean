import IxVMRefinement.Assembly.TypingRecParentArm

/-! # The stored recursor of the late step, and the member check's counts

**The stored constant is not `canonRec`.** The late relation stores the recursor with the
rules `sumRules`, whose install bits (`fire`, `k`, `eta`, `paramsBlind`, the parameter count) are
the kernel's; `LoadedReads.canonRec`, the constant `reloadsAs_recr_cons` reloads, keeps the
reader's placeholders (`fire = .inert`, no `eta`, not `paramsBlind`) and the record's K flag and
parameter count. A load does not see those bits: a rule is represented by its position, its
field count and its right-hand side (`Core.RuleRep`), and the K flag only asks, where it is set,
for one rule with its K bit and the parameter count (`Core.CIRep.recr`). So a reload transfers
to any rule list that agrees on field counts and right-hand sides and on the K clause, at any
environment that stores the same keys:

* `stored_κ_congr`: the prefix keying depends on the environment only through which keys it
  stores;
* `rulesRep_congr`, `ciRep_recr_rules`, `reloadsAs_recr_rules`: the transfer;
* `find_isSome_cons_congr`: consing one of two constants of one name stores the same keys.

**The member check's counts.** `native_rec_member_full`: the route of `check_recursor_member`
(as `native_rec_route_calls`) with what the check asserts of the record's counts against the
parent's (`n_p = parent_np`, `n_i = parent_ni`: the record is no auxiliary recursor, its block
being its own record), the rule list's length run answering the parent's constructor count,
the K flag the `compute_k_target` verdict, and the run of `check_recursor_canonical_full`, each
run within the check's calls and at a heap after the parent's load.
-/

universe u

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal Key RecRule)

/-! ## The prefix keying depends on the stored keys only -/

theorem stored_κ_congr {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {env₁ env₂ : Ix.Kernel.Env .anon}
    (h : ∀ k, (env₁.find? k).isSome = (env₂.find? k).isSome) :
    (Core.Ctx.stored ⟨E, env₁, t, lim⟩).κ = (Core.Ctx.stored ⟨E, env₂, t, lim⟩).κ := by
  have key : ∀ k, (∃ ci, env₁.find? k = some ci) ↔ (∃ ci, env₂.find? k = some ci) := by
    intro k
    rw [← Option.isSome_iff_exists, ← Option.isSome_iff_exists, h k]
  have hres : Core.Ctx.resolvesOver ⟨E, env₁, t, lim⟩ env₁ =
      Core.Ctx.resolvesOver ⟨E, env₂, t, lim⟩ env₂ := by
    funext a
    apply propext
    show ((∃ ci, env₁.find? (Core.keyOf t a) = some ci) ∨
        ∃ y, a = Core.projMarker y ∧ ∃ ci, env₁.find? (Core.keyOf t y) = some ci) ↔
      ((∃ ci, env₂.find? (Core.keyOf t a) = some ci) ∨
        ∃ y, a = Core.projMarker y ∧ ∃ ci, env₂.find? (Core.keyOf t y) = some ci)
    simp only [key]
  rw [Core.Ctx.stored_κ, Core.Ctx.stored_κ]
  show Core.resKey t (Core.Ctx.resolvesOver ⟨E, env₁, t, lim⟩ env₁) =
    Core.resKey t (Core.Ctx.resolvesOver ⟨E, env₂, t, lim⟩ env₂)
  rw [hres]

/-- Consing one of two constants of one name stores the same keys. -/
theorem find_isSome_cons_congr {env : Ix.Kernel.Env .anon} {cn cn' : ConstantInfo .anon}
    (hname : cn.name = cn'.name) (k : Key .anon) :
    ((⟨cn :: env.consts⟩ : Ix.Kernel.Env .anon).find? k).isSome =
      ((⟨cn' :: env.consts⟩ : Ix.Kernel.Env .anon).find? k).isSome := by
  rw [Ix.Kernel.Env.find?_cons, Ix.Kernel.Env.find?_cons, hname]
  split_ifs <;> rfl

/-! ## A reload transfers along the rules' install bits -/

/-- Rules agreeing on field counts and right-hand sides are represented by the same list. -/
theorem rulesRep_congr {κ : _root_.Address → Core.KKey} {h : Heap F}
    {ps : List Ix.Kernel.LevelParam} {j : Nat} {p : SourceValue F} {rls : List (RecRule .anon)}
    (hr : Core.RulesRep κ h ps j p rls) :
    ∀ {rls' : List (RecRule .anon)},
      List.Forall₂ (fun rl rl' : RecRule .anon => rl'.nfields = rl.nfields ∧ rl'.rhs = rl.rhs)
        rls rls' →
      Core.RulesRep κ h ps j p rls' := by
  induction hr with
  | nil cell =>
    intro rls' hf
    cases hf
    exact .nil cell
  | cons cell hr _ ih =>
    intro rls' hf
    cases hf with
    | cons hh ht =>
      obtain ⟨hn, hrhs⟩ := hh
      obtain ⟨rhs, hv, hlt, htm⟩ := hr
      exact .cons cell ⟨rhs, by rw [hn]; exact hv, by rw [hn]; exact hlt,
        by rw [hrhs]; exact htm⟩ (ih ht)

/-- **A loaded recursor represents every rule list with the same field counts and right-hand
sides**, where a K rule of the one represented is a K rule, with its parameter count, of the
other. -/
theorem ciRep_recr_rules {κ : _root_.Address → Core.KKey} {h : Heap F} {v : SourceValue F}
    {cv : ConstantVal .anon} {mI rP : Nat} {rls rls' : List (RecRule .anon)}
    (hr : Core.CIRep κ h v (.recInfo cv mI rP rls))
    (hrules : List.Forall₂
      (fun rl rl' : RecRule .anon => rl'.nfields = rl.nfields ∧ rl'.rhs = rl.rhs) rls rls')
    (hk : ∀ rl rl', rls = [rl] → rls' = [rl'] → rl.k = true →
      rl'.k = true ∧ rl'.ctorParams = rl.ctorParams) :
    Core.CIRep κ h v (.recInfo cv mI rP rls') := by
  cases hr with
  | recr hv hnp hni hnm hnmi hrP hmI hcounts hrules0 hk0 hkey =>
    refine .recr hv hnp hni hnm hnmi hrP hmI hcounts (rulesRep_congr hrules0 hrules) ?_ hkey
    intro hk1
    obtain ⟨rl, hrl, hrlk, hrlp⟩ := hk0 hk1
    subst hrl
    cases hrules with
    | cons hh ht =>
      cases ht
      obtain ⟨hk', hp'⟩ := hk rl _ rfl rfl hrlk
      exact ⟨_, rfl, hk', hp'.trans hrlp⟩

/-- **A reload of a recursor transfers** to an environment storing the same keys and to a rule
list with the same field counts and right-hand sides, its K rule a K rule with the parameter
count. -/
theorem reloadsAs_recr_rules {E : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {env₁ env₂ : Ix.Kernel.Env .anon} {cv : ConstantVal .anon} {mI rP : Nat}
    {rls rls' : List (RecRule .anon)}
    (h : Decl.ReloadsAs E t env₁ (.recInfo cv mI rP rls))
    (hfind : ∀ k, (env₁.find? k).isSome = (env₂.find? k).isSome)
    (hrules : List.Forall₂
      (fun rl rl' : RecRule .anon => rl'.nfields = rl.nfields ∧ rl'.rhs = rl.rhs) rls rls')
    (hk : ∀ rl rl', rls = [rl] → rls' = [rl'] → rl.k = true →
      rl'.k = true ∧ rl'.ctorParams = rl.ctorParams) :
    Decl.ReloadsAs E t env₂ (.recInfo cv mI rP rls') := by
  intro addr ptr hh hh' cs a ev hgood ha hkey
  obtain ⟨v, hld, hrep⟩ := h addr ptr hh hh' cs a ev hgood ha hkey
  rw [← stored_κ_congr (lim := none) hfind]
  exact ⟨v, hld, ciRep_recr_rules hrep hrules hk⟩

/-! ## The member check's counts -/

/-- **The member check of a recursor record, with its counts**: the route (scan, parent load,
native verdict), the record's parameter and index counts the parent's, the rule list's length
the parent's constructor count, the K flag the `compute_k_target` verdict, and the canonical
comparison's run; each run within the check's calls, the later ones at heaps after the parent's
load. -/
theorem native_rec_member_full
    {rc address levels type parameters indices motives minors rules k unsafeFlag block position
      result : SourceValue F}
    {heap final : Heap F} {calls : List (Call F)}
    (observed : ObsFn Obs.W "KernelCheck::check_recursor_member"
      [rc, .construct "KernelTypes::KConstantInfo" "Rec"
        [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block,
          position], address]
      heap result final calls) :
    ∃ (parent pointer : SourceValue F) (scanHeap loadedHeap routedHeap : Heap F)
      (scanCalls loadCalls routeCalls : List (Call F))
      (parentLevels parentType parentParams parentIndices constructors parentUnsafe parentBlock
        parentIndex : SourceValue F)
      (lenHeap lenAfter kHeap kAfter canonHeap : Heap F) (len kTarget : SourceValue F)
      (lenCalls kCalls canonCalls : List (Call F)),
      ObsFn Obs.W "KernelCheck::rec_to_parent_addr" [type, parameters, motives, minors, indices]
        heap parent scanHeap scanCalls ∧
      (∀ cl ∈ scanCalls, cl ∈ calls) ∧
      ObsFn Obs.W "Ingress::get_ci" [parent] scanHeap pointer loadedHeap loadCalls ∧
      (∀ cl ∈ loadCalls, cl ∈ calls) ∧
      loadValue loadedHeap pointer = .ok (.construct "KernelTypes::KConstantInfo" "Induct"
        [parentLevels, parentType, parentParams, parentIndices, constructors, parentUnsafe,
          parentBlock, parentIndex]) ∧
      ObsFn Obs.W "KernelModeled::block_is_modeled" [parentBlock]
        loadedHeap (.field 0) routedHeap routeCalls ∧
      (∀ cl ∈ routeCalls, cl ∈ calls) ∧
      parameters = parentParams ∧ indices = parentIndices ∧
      Heap.Extends loadedHeap lenHeap ∧
      ObsFn Obs.W Obs.Names.«Lists::length<KernelTypes::KRecRule>» [rules] lenHeap len lenAfter
        lenCalls ∧
      (∀ cl ∈ lenCalls, cl ∈ calls) ∧ len = constructors ∧
      Heap.Extends loadedHeap kHeap ∧
      ObsFn Obs.W "KernelCheck::compute_k_target"
        [rc, .construct "KernelTypes::KConstantInfo" "Induct"
          [parentLevels, parentType, parentParams, parentIndices, constructors, parentUnsafe,
            parentBlock, parentIndex], parent] kHeap kTarget kAfter kCalls ∧
      (∀ cl ∈ kCalls, cl ∈ calls) ∧ k = kTarget ∧
      Heap.Extends loadedHeap canonHeap ∧
      ObsFn Obs.W "KernelCheck::check_recursor_canonical_full"
        [rc, .construct "KernelTypes::KConstantInfo" "Rec"
          [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block,
            position], address,
          .construct "KernelTypes::KConstantInfo" "Induct"
            [parentLevels, parentType, parentParams, parentIndices, constructors, parentUnsafe,
              parentBlock, parentIndex], parent] canonHeap result final canonCalls ∧
      (∀ cl ∈ canonCalls, cl ∈ calls) := by
  match Obs.«KernelCheck::check_recursor_member».obs observed with
  | .run (v72 := parent) (m73 := scanHeap) (p134 := pointer) (m127 := loadedHeap)
      (cs83 := scanCalls) (cs140 := loadCalls) (x__parent_nlvls := parentLevels)
      (w167 := parentType) (x_parent_np := parentParams) (x_parent_ni := parentIndices)
      (x_num_ctors := constructors) (w168 := parentUnsafe) (x_parent_block_addr := parentBlock)
      (x_parent_ind_idx := parentIndex) (m223 := routedHeap) (cs231 := routeCalls)
      (m250 := lenHeap) (v369 := len) (m372 := lenAfter) (cs380 := lenCalls)
      (m664 := kHeap) (v672 := kTarget) (m673 := kAfter) (cs683 := kCalls)
      (m769 := canonHeap) (cs825 := canonCalls)
      (hv15 := input) (ev85 := scan) (ev142 := load) (ld136 := parentInfo)
      (ev233 := route) (heq248 := native) (ev278 := muts₁) (ev292 := muts₂) (ev314 := sameBlock)
      (heq357 := notAux) (ev382 := lenRun) (heq398 := lenEq) (ev412 := peelRun)
      (ev477 := scopeRun) (sg671 := seg) (ev685 := kRun) (heq737 := kEq)
      (ev751 := shapeRun) (ev781 := letsRun) (ev827 := canonRun)
      (hc868 := children) .. =>
    injection input with _ _ fields
    simp only [List.cons.injEq, and_true] at fields
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := fields
    rw [native] at route
    have eLen : Heap.Extends loadedHeap lenHeap :=
      route.heap_extends.trans (muts₁.heap_extends.trans (muts₂.heap_extends.trans
        sameBlock.heap_extends))
    match seg with
    | .n1 (hv533 := isAux) .. =>
      exact absurd (Value.field.inj (isAux.symm.trans notAux)) one_ne_zero
    | .other (heq570 := npEq) (heq598 := niEq) (ev604 := spineRun) .. =>
      have eK : Heap.Extends loadedHeap kHeap :=
        eLen.trans (lenRun.heap_extends.trans (peelRun.heap_extends.trans
          (scopeRun.heap_extends.trans spineRun.heap_extends)))
      have eC : Heap.Extends loadedHeap canonHeap :=
        eK.trans (kRun.heap_extends.trans (shapeRun.heap_extends.trans letsRun.heap_extends))
      refine ⟨parent, pointer, scanHeap, loadedHeap, routedHeap, scanCalls, loadCalls,
        routeCalls, parentLevels, parentType, parentParams, parentIndices, constructors,
        parentUnsafe, parentBlock, parentIndex, lenHeap, lenAfter, kHeap, kAfter, canonHeap,
        len, kTarget, lenCalls, kCalls, canonCalls, scan, ?_, load, ?_, parentInfo, route, ?_,
        npEq, niEq, eLen, lenRun, ?_, lenEq, eK, kRun, ?_, kEq, eC, canonRun, ?_⟩
      · intro call member; rw [children]; simp [member]
      · intro call member; rw [children]; simp [member]
      · intro call member; rw [children]; simp [member]
      · intro call member; rw [children]; simp [member]
      · intro call member; rw [children]; simp [member]
      · intro call member; rw [children]; simp [member]

end IxVM.Refinement.Typing
