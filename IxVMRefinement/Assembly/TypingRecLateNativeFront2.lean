import IxVMRefinement.Assembly.TypingRecLateNativeAux
import IxVMRefinement.Assembly.TypingRecLateK
import IxVMRefinement.Assembly.TypingRecLateKeying
import IxVMRefinement.Assembly.TypingRecLateOut
import IxVMRefinement.Assembly.NativeBlockFormer
import IxVMRefinement.Assembly.BareState
import IxVMRefinement.L1.AnnotationCorrespondence
import IxVMRefinement.StatementRel.ReadsMono
import IxVMRefinement.StatementRel.LoadedReadsCanonRec
import IxVMRefinement.Decl.NativeRecRules
import IxVMRefinement.Decl.NativeRecCheck
import IxVMRefinement.Decl.Modeled

/-! # The circuit side of a late recursor's step: the pieces

The late recursor record `c` at `A` (`c.info = .recr rc`) is checked by `check_const`'s `Rec`
arm: the scope check and the sort check of its type, then the member check, whose canonical
comparison runs `nat_rec_check` against the tied parent. This module gives the pieces the
front theorem (`TypingRecLateNativeFront.lean`) assembles:

* `RecFrontAt`, `rec_front_arm`: the arm at the tied parent, keeping what `RecArmAt` drops: the
  record's own load (its blobs, binder tree, the type's binder plan), the scope run and the sort
  run on the type pointer, and the member check's scan of the type (`rec_to_parent_addr`);
* `front_type_canon`: the type read under level parameters `ps`, well scoped, has a canonical
  annotation, exactly represented under the prefix keying (the type has no `recur` address);
* `front_constantValCheck`: the declared recursor checked at the step's environment;
* `front_rules_canon`: the rules read under `ps` have canonical rules, represented under the rule
  keying `lateRuleKey` (a used reference is stored; the only `recur` address is the recursor's);
* `front_parent_former`: the parent's loaded type is the stored former's;
* `front_ctor_loads_count`: the constructor loads of the member, as the comparison reads them
  (`NatCtorLoadT`);
* `Decl.front_maj`: the level arguments of the head of the major premise's domain, from the
  member check's scan of the type and the comparison's level clause.
-/

universe u

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (Expr Level LevelParam ConstantVal ConstantInfo RecRule Declaration)

/-! ## The head of the major premise's domain -/

theorem front_collect_spine_exact_head {κ : _root_.Address → KKey} {d : Nat}
    {Γ : Nat → KExpr} :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelTypes::collect_spine" →
      ∀ (k : Nat) (E : KExpr) (x_e x_head x_sp : SourceValue F),
        args = [x_e] → r = .tuple [x_head, x_sp] →
        TmExact κ d Γ h k E x_e →
        ∃ H,
          E.getAppFn = H.getAppFn ∧
          TmExact κ d Γ h' k H x_head ∧
          (∀ h₂ a ls, Heap.Extends h' h₂ →
            AppHeadConstLvls h₂ a ls x_head → AppHeadConstLvls h₂ a ls x_e) :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' _ => fname = "KernelTypes::collect_spine" →
      ∀ (k : Nat) (E : KExpr) (x_e x_head x_sp : SourceValue F),
        args = [x_e] → r = .tuple [x_head, x_sp] →
        TmExact κ d Γ h k E x_e →
        ∃ H,
          E.getAppFn = H.getAppFn ∧
          TmExact κ d Γ h' k H x_head ∧
          (∀ h₂ a ls, Heap.Extends h' h₂ →
            AppHeadConstLvls h₂ a ls x_head → AppHeadConstLvls h₂ a ls x_e))
    (fun fname args h r h' _ ev _ hfn k E x_e x_head x_sp hargs hr htm => by
      subst hfn hargs hr
      obtain ⟨ps, hch, -, -⟩ := Core.collect_spine_chain_tup ev
      have haux :
          ∀ {e hd : SourceValue F} {ps : List (SourceValue F)},
            Core.SpineChain h' e hd ps →
            ∀ {E : KExpr}, TmExact κ d Γ h' k E e →
              ∃ H,
                E.getAppFn = H.getAppFn ∧
                TmExact κ d Γ h' k H hd ∧
                (∀ h₂ a ls, Heap.Extends h' h₂ →
                  AppHeadConstLvls h₂ a ls hd → AppHeadConstLvls h₂ a ls e) := by
        intro e hd ps sc
        induction sc with
        | head _ _ =>
          intro E hE
          exact ⟨E, rfl, hE, fun _ _ _ _ hh => hh⟩
        | app ld _ ih =>
          intro E hE
          cases hE with
          | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _
          | const cell _ _ | lam cell _ _ _ | forallE cell _ _ _
          | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _
          | proj cell _ _ =>
            exact (load_cell_ne cell ld (by decide)).elim
          | app cell rf _ =>
            obtain ⟨-, hxs⟩ := load_cell cell ld
            injection hxs with hxf _
            rw [hxf] at rf
            obtain ⟨H, hfn_f, hH, hwrap⟩ := ih rf
            exact ⟨H, hfn_f, hH, fun h₂ a ls ext₂ hh =>
              .app (ext₂.getElem?_eq cell) (by rw [hxf]; exact hwrap h₂ a ls ext₂ hh)⟩
      exact haux (hch.mono ev.heap_extends) (htm.mono ev.heap_extends))

theorem front_peel_n_foralls_exact {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (m : Nat) {n : F} {x_e r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
      {k : Nat} {T : KExpr},
      ZMod.val n = m →
      TmExact κ d Γ h k T x_e →
      ObsFn W "KernelCheck::peel_n_foralls" [x_e, .field n] h r h' calls →
      h' = h ∧ ∃ (bs : List (KExpr × Ix.Kernel.BinderMeta)) (B : KExpr),
        T.stripPis m = some (bs, B) ∧ TmExact κ d Γ h (k + m) B r ∧
        (∀ h₂ a ls, Heap.Extends h h₂ →
          ForallRightHeadLvls h₂ a ls 0 r → ForallRightHeadLvls h₂ a ls m x_e)
  | 0, n, x_e, r, h, h', _, k, T, hval, hT, ev => by
    have hn0 : n = 0 := (ZMod.val_eq_zero n).mp hval
    rw [hn0] at ev
    cases Obs.«KernelCheck::peel_n_foralls».obs ev with
    | n0 _ hr hh _ =>
      subst hr hh
      exact ⟨rfl, [], T, rfl, by simpa using hT, fun _ _ _ _ hh => hh⟩
    | other _ _ _ _ _ hne19 _ _ _ _ =>
      exact (hne19 rfl).elim
  | m + 1, n, x_e, r, h, h', _, k, T, hval, hT, ev => by
    have hn0 : n ≠ 0 := by intro e; rw [e] at hval; simp at hval
    cases Obs.«KernelCheck::peel_n_foralls».obs ev with
    | n0 hv14 _ _ _ =>
      exact (hn0 (Value.field.inj hv14)).elim
    | other _ x_body _ _ v66 _ ld34 op87 ev64 _ =>
      cases hT with
      | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _
      | const cell _ _ | app cell _ _ | lam cell _ _ _
      | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _
      | proj cell _ _ =>
        exact (load_cell_ne cell ld34 (by decide)).elim
      | @forallE _ _ _ _ _ T_p _ ℓ_p cell _ rb _ =>
        obtain ⟨-, hxs⟩ := load_cell cell ld34
        injection hxs with _ hxs; injection hxs with hxb _
        rw [hxb] at rb
        have hv66 : v66 = .field (n - 1) := by
          simp only [evalBinOp, Except.ok.injEq] at op87
          exact op87.symm
        rw [hv66] at ev64
        have hval' : ZMod.val (n - 1) = m := by
          have hs := Lib.val_sub_one hn0
          omega
        obtain ⟨rfl, bs, B, hstrip, hB, hwrap⟩ := front_peel_n_foralls_exact m hval' rb ev64
        refine ⟨rfl, (T_p, bmeta ℓ_p) :: bs, B, ?_, ?_, fun h₂ a ls ext₂ hh =>
          .succ (ext₂.getElem?_eq cell) (by rw [hxb]; exact hwrap h₂ a ls ext₂ hh)⟩
        · simp [Ix.Kernel.Expr.stripPis, hstrip]
        · rwa [show k + (m + 1) = k + 1 + m by omega]

theorem front_getAppFn_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ (e : KExpr),
      (e.instantiateLevelParams ks us).getAppFn =
        e.getAppFn.instantiateLevelParams ks us
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _
  | .lam _ _ _ | .forallE _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ => rfl
  | .app f _ => front_getAppFn_instantiateLevelParams ks us f

/-- **`rec_to_parent_addr` reads the head of the major premise's domain**: the scanned type has
`np + nm + nmi + ni` literal `Forall`s and then a `Forall` whose domain is a literal application
spine over a `Const` cell at `a_d` with levels `ls_d`; at the represented term that domain is
headed by the constant `κ a_d` at `ls_d`. -/
theorem front_rec_to_parent_addr_head_lvls {κ : _root_.Address → KKey}
    {np nm nmi ni : Nat} {E : KExpr} {x_ty r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hsum_lt : np + nm + nmi + ni < 18446744069414584321)
    (hT : TmExact κ 0 (fun _ => default) h 0 E x_ty)
    (ev : ObsFn W "KernelCheck::rec_to_parent_addr"
      [x_ty, .field (np : F), .field (nm : F), .field (nmi : F), .field (ni : F)]
      h r h' calls) :
    ∃ a_d ls_d,
      ForallRightHeadLvls h' a_d ls_d (np + nm + nmi + ni) x_ty ∧
      ∀ bs dom B bm,
        E.stripPis (np + nm + nmi + ni) = some (bs, .forallE dom B bm) →
        dom.getAppFn = .const (κ (ixAddr a_d)) ls_d := by
  obtain ⟨v1, x9, x17, v37, m38, _, x_major_ty, _, _, m104, _, x_head, w132, x_caddr,
    w162, op32, op24, op16, ev50, ld78, ev117, ld154, _, he175, _⟩ :=
    Obs.«KernelCheck::rec_to_parent_addr».obs ev
  have hx17 : x17 = .field ((np + nm : Nat) : F) := by
    simp only [evalBinOp, Except.ok.injEq, Nat.cast_add] at op32 ⊢; exact op32.symm
  rw [hx17] at op24
  have hx9 : x9 = .field ((np + nm + nmi : Nat) : F) := by
    simp only [evalBinOp, Except.ok.injEq, Nat.cast_add] at op24 ⊢; exact op24.symm
  rw [hx9] at op16
  have hv1 : v1 = .field ((np + nm + nmi + ni : Nat) : F) := by
    simp only [evalBinOp, Except.ok.injEq, Nat.cast_add] at op16 ⊢; exact op16.symm
  rw [hv1] at ev50
  have hval : ZMod.val (((np + nm + nmi + ni : Nat) : F)) = np + nm + nmi + ni :=
    ZMod.val_natCast_of_lt hsum_lt
  obtain ⟨rfl, bs₀, B_peel, hstrip₀, hB_peel, hwrap_peel⟩ :=
    front_peel_n_foralls_exact (np + nm + nmi + ni) hval hT ev50
  cases hB_peel with
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _
  | const cell _ _ | app cell _ _ | lam cell _ _ _
  | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _
  | proj cell _ _ =>
    exact (load_cell_ne cell ld78 (by decide)).elim
  | forallE cell_maj rt_maj _ _ =>
    obtain ⟨-, hxs⟩ := load_cell cell_maj ld78
    injection hxs with hxm _
    rw [hxm] at rt_maj
    obtain ⟨H, hfn_dom, hH, hwrap_sp⟩ :=
      front_collect_spine_exact_head _ _ _ _ _ _ ev117 rfl _ _ x_major_ty x_head w132 rfl rfl
        rt_maj
    cases hH with
    | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _
    | app cell _ _ | lam cell _ _ _ | forallE cell _ _ _
    | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _
    | proj cell _ _ =>
      exact (load_cell_ne cell ld154 (by decide)).elim
    | const cell_c ra_c rls_c =>
      have hhead_m104 : AppHeadConstLvls m104 _ _ x_major_ty :=
        hwrap_sp m104 _ _ (Heap.Extends.refl _) (.const cell_c ra_c rls_c)
      have hzero_m104 : ForallRightHeadLvls m104 _ _ 0 (.ptr (.enum kexprEnum) _) :=
        .zero (ev117.heap_extends.getElem?_eq cell_maj) (by rwa [hxm])
      have hpeel_m104 := hwrap_peel m104 _ _ ev117.heap_extends hzero_m104
      rw [← he175] at hpeel_m104
      refine ⟨_, _, hpeel_m104, ?_⟩
      intro bs dom B bm hs
      rw [hstrip₀] at hs
      injection hs with hp_eq
      have hB_eq := congrArg Prod.snd hp_eq
      dsimp only at hB_eq
      injection hB_eq with hdom_eq _ _
      rw [← hdom_eq]
      exact hfn_dom

/-- **The level arguments of the head of the major premise's domain** (the legacy `hmaj_lvls`):
from the member check's scan of the declared type (represented at positions `rlps`) and the
comparison's level clause on the same pointer, the domain of binder `np + 1 + nmi + ni` of the
declared type is headed by a constant at the family's level parameters `List.range k`. -/
theorem front_maj {κ : _root_.Address → KKey} {k : Nat} {large : Bool} {np nmi ni : Nat}
    {tyC : KExpr} {x_ty r : SourceValue F} {h h' h₂ : Heap F} {cs : List (Call F)}
    (hsum : np + 1 + nmi + ni < 18446744069414584321)
    (hT : TmExact κ 0 (fun _ => default) h 0
      (posOf (if large then k :: List.range k else List.range k) tyC) x_ty)
    (ev : ObsFn W "KernelCheck::rec_to_parent_addr"
      [x_ty, .field (np : F), .field ((1 : Nat) : F), .field (nmi : F), .field (ni : F)]
      h r h' cs)
    (ext : Heap.Extends h' h₂)
    (hlv : ∀ a_d ls_d, ForallRightHeadLvls h₂ a_d ls_d (np + 1 + nmi + ni) x_ty →
      ls_d = (List.range k).map (fun i => Level.param ((if large then 1 else 0) + i))) :
    ∀ bs dom B m, tyC.stripPis (np + 1 + nmi + ni) = some (bs, .forallE dom B m) →
      ∃ K, dom.getAppFn = .const K ((List.range k).map .param) := by
  obtain ⟨a_d, ls_d, hright, hdom_pos⟩ := front_rec_to_parent_addr_head_lvls (by omega) hT ev
  have hls_d := hlv a_d ls_d (hright.mono ext)
  let rlps' := if large then k :: List.range k else List.range k
  intro bs dom B bm hs
  have hs_pos := ilp_stripPis rlps' (posLevels rlps') (np + 1 + nmi + ni) hs
  have hfn_pos := hdom_pos _ (posOf rlps' dom) (posOf rlps' B) _ hs_pos
  have hfn_pos' : posOf rlps' dom.getAppFn =
      posOf rlps' (.const (κ (ixAddr a_d)) ((List.range k).map .param)) := by
    unfold posOf at hfn_pos ⊢
    rw [← front_getAppFn_instantiateLevelParams, hfn_pos, hls_d]
    simpa [rlps', Expr.instantiateLevelParams] using
      congrArg (Expr.const (κ (ixAddr a_d))) (clvls_eq_subst_params k large)
  have hinv := congrArg
    (fun e => e.instantiateLevelParams (List.range rlps'.length) (rlps'.map .param))
    hfn_pos'
  rw [posOf_perm_inv (rlps_perm k large), posOf_perm_inv (rlps_perm k large)] at hinv
  exact ⟨κ (ixAddr a_d), hinv⟩

end IxVM.Refinement.Decl

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (NativeFam NativeFamStored)
open Ix.Kernel.Model (rulesJ)

/-! ## Small facts -/

/-- The level parameters a late recursor declares, written out. -/
theorem front_recLps_eq (large : Bool) (k : Nat) :
    Ix.Kernel.Reader.recLps large (List.range k) =
      if large then k :: List.range k else List.range k := by
  cases large <;> simp [Ix.Kernel.Reader.recLps]

/-- An entry of the comparison's constructor entries is a stored constructor's. -/
theorem front_lateCtorsInfo_getElem? {fam : NativeFam .anon} {j : Nat}
    {info : Core.KKey × Nat × Core.KExpr × Core.KExpr × List Nat}
    (h : (lateCtorsInfo fam)[j]? = some info) :
    ∃ cA ks, fam.ctorsA[j]? = some cA ∧ fam.p.kinds[j]? = some ks ∧
      info = (cA.1.name, cA.2, cA.1.type, cA.1.type, Ix.Kernel.recIdxOf ks) := by
  unfold lateCtorsInfo at h
  obtain ⟨cA, ks, h1, h2, h3⟩ := List.getElem?_zipWith_eq_some.mp h
  exact ⟨cA, ks, h1, h2, h3.symm⟩

/-- A `Forall₂` whose right-hand entries all meet `p` carries `p` on each pair. -/
theorem front_forall₂_and_right {α β : Type} {R : α → β → Prop} {p : β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → (∀ b ∈ l₂, p b) →
      List.Forall₂ (fun a b => R a b ∧ p b) l₁ l₂
  | _, _, .nil, _ => .nil
  | _, _, .cons hr hs, hp =>
    .cons ⟨hr, hp _ (List.mem_cons.mpr (Or.inl rfl))⟩
      (front_forall₂_and_right hs (fun b hb => hp b (List.mem_cons.mpr (Or.inr hb))))

/-- The references a recursor record's rules use are references the record uses. -/
theorem recr_rule_usedRefs {c : Ixon.Constant} {rc : Ixon.Recursor} (hinfo : c.info = .recr rc)
    {ru : Ixon.RecursorRule} (hru : ru ∈ rc.rules.toList) :
    ∀ i, i ∈ exprRefIdxs ru.rhs → i ∈ usedRefIdxs c := by
  intro i hi
  unfold usedRefIdxs
  rw [hinfo]
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨ru, hru, hi⟩))

/-! ## The arm, in full -/

/-- **The `Rec` arm at the tied parent, in full**: `RecArmAt` with the record's own load (its
blobs, its binder tree, the type's binder plan), the scope run and the sort run on the type
pointer, and the member check's scan of the type; the record's address and block field and the
heaps from the record's load (`ldHeap`) on. -/
def RecFrontAt (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env)
    (lim : Option Nat) (A : _root_.Address) (c : Ixon.Constant)
    (rc : Ixon.Recursor) (P : _root_.Address) (ip : Ixon.InductiveProj)
    (ind : Ixon.Inductive) : Prop :=
  ∃ (rcv apv parentV tyPtr rulesPtr blkPtr tyPtrP unsP blkPtrP pointer result scopeResult
      sortResult : SourceValue F)
    (bA bR bT bP : Bytes.Address) (blobs : List (_root_.Address × ByteArray))
    (tree : L1.BinderTreeData) (planT : List Core.KLevel)
    (ldHeap scopeBefore scopeAfter sortAfter memberHeap scanHeap loadedHeap canonHeap
      final : Heap F)
    (ldCalls scopeCalls sortCalls scanCalls loadCalls canonCalls : List (Call F)),
    Core.RCRep t lim ldHeap rcv ∧
    Bytes.RepAddressRef Core.addrTy ldHeap bA apv ∧ Core.ixAddr bA = A ∧
    Bytes.RepAddressRef Core.addrTy ldHeap bR blkPtr ∧ Core.ixAddr bR = A ∧
    L1.HashedPairs ldCalls blobs ∧ (∀ cl ∈ ldCalls, cl ∈ calls) ∧
    (∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs) ∧
    L1.BinderTreeBuilt (L1.binderLeavesData c.binders.toList) tree ∧
    L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs ldHeap 4294967295
      rc.typ tyPtr ∧
    L1.binderRootPlan tree c.sharing.toList 0 rc.typ = some planT ∧
    L1.HeapBinderLevels ldHeap tyPtr planT ∧
    L1.RulesTraceRep c.refs.toList [A] c.univs.toList c.sharing.toList blobs tree ldHeap 0
      (0 + 1) rc.rules.toList rulesPtr ∧
    rc.rules.size < 8589934592 ∧ ip.idx.toNat < 72057594037927936 ∧
    rc.lvls.toNat < 4294967296 ∧ rc.params.toNat < 72057594037927936 ∧
    rc.indices.toNat < 72057594037927936 ∧ rc.motives.toNat < 72057594037927936 ∧
    rc.minors.toNat < 72057594037927936 ∧
    ind.lvls.toNat < 4294967296 ∧ ind.params.toNat < 72057594037927936 ∧
    ind.indices.toNat < 72057594037927936 ∧ ind.ctors.size < 72057594037927936 ∧
    Heap.Extends ldHeap scopeBefore ∧
    ObsFn Obs.W "KernelCheck::validate_expr_well_scoped"
      [tyPtr, .field 0, .field (rc.lvls.toNat : F)] scopeBefore scopeResult scopeAfter
      scopeCalls ∧
    (⟨"KernelCheck::validate_expr_well_scoped", [tyPtr, .field 0, .field (rc.lvls.toNat : F)],
      scopeBefore⟩ : Call F) ∈ calls ∧
    ObsFn Obs.W "KernelInfer::k_ensure_sort"
      [rcv, tyPtr, .ptr (.enum Core.kexprListEnum) scopeAfter.length]
      (scopeAfter ++ [.construct Core.kexprListEnum "Nil" []]) sortResult sortAfter sortCalls ∧
    (∀ cl ∈ sortCalls, cl ∈ calls) ∧
    Heap.Extends sortAfter memberHeap ∧
    ObsFn Obs.W "KernelCheck::rec_to_parent_addr"
      [tyPtr, .field (rc.params.toNat : F), .field (rc.motives.toNat : F),
        .field (rc.minors.toNat : F), .field (rc.indices.toNat : F)]
      memberHeap parentV scanHeap scanCalls ∧
    (∀ cl ∈ scanCalls, cl ∈ calls) ∧
    Bytes.RepAddressRef Core.addrTy scanHeap bT parentV ∧ Core.ixAddr bT = P ∧
    Bytes.RepAddressRef Core.addrTy loadedHeap bP blkPtrP ∧ Core.ixAddr bP = ip.block ∧
    Heap.Extends scanHeap loadedHeap ∧
    ObsFn Obs.W "Ingress::get_ci" [parentV] scanHeap pointer loadedHeap loadCalls ∧
    (∀ cl ∈ loadCalls, cl ∈ calls) ∧
    loadValue loadedHeap pointer = .ok (.construct "KernelTypes::KConstantInfo" "Induct"
      [.field (ind.lvls.toNat : F), tyPtrP, .field (ind.params.toNat : F),
        .field (ind.indices.toNat : F), .field (ind.ctors.size : F), unsP, blkPtrP,
        .field (ip.idx.toNat : F)]) ∧
    Heap.Extends loadedHeap canonHeap ∧
    ObsFn Obs.W "KernelCheck::check_recursor_canonical_full"
      [rcv, .construct "KernelTypes::KConstantInfo" "Rec"
        [.field (rc.lvls.toNat : F), tyPtr, .field (rc.params.toNat : F),
          .field (rc.indices.toNat : F), .field (rc.motives.toNat : F),
          .field (rc.minors.toNat : F), rulesPtr, L1.repBoolField rc.k,
          L1.repBoolField rc.isUnsafe, blkPtr, .field ((0 : Nat) : F)], apv,
        .construct "KernelTypes::KConstantInfo" "Induct"
          [.field (ind.lvls.toNat : F), tyPtrP, .field (ind.params.toNat : F),
            .field (ind.indices.toNat : F), .field (ind.ctors.size : F), unsP, blkPtrP,
            .field (ip.idx.toNat : F)], parentV]
      canonHeap result final canonCalls ∧
    (∀ cl ∈ canonCalls, cl ∈ calls)

/-- **The arm at the tied parent, in full** (the derivation of `rec_arm_of_arm`, with
`check_const_rec_arm` in place of `check_const_rec_route`, keeping the record's load). -/
theorem rec_front_arm {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc)
    (hnat : RecArmRun calls t A lim) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} {cm : Ixon.Constant}
    (hcm : Ix.Cert.recordAt E P = some cm) (hcmi : cm.info = .iPrj ip)
    (htie : RecMajorTie t E₀ A c rc P)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hcb : Ix.Cert.recordAt E ip.block = some cb) (hms : cb.info = .muts ms)
    (hind : ms[ip.idx.toNat]? = some (.indc ind)) :
    RecFrontAt calls t E₀ lim A c rc P ip ind := by
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  have hgood : Core.Good ⟨E, env, t, lim⟩ calls := hst.good env lim
  have hbound : Bounded calls := hgood.2
  have hrec₀ : Ix.Cert.recordAt E₀ A = some c := (hS.recordOf_eq_recordAt A).symm.trans hc
  have hstored : Decl.UsedRefsStored t env c :=
    usedRefsStored_of_cover (hcover env ⟨hstep.ext, hstep.refs, hstep.fresh⟩) hinert
  obtain ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, kf, uns, block, position, cs_load, cs_chk, -, hrcM, ha_pre, -, ev_ld, hsub_ld,
    hld, ev_chk, hsub_chk, hfr⟩ := hnat
  obtain ⟨rawB, cB, hszB, hhB, hbaB, hexB⟩ := get_ci_bytes_bound ha_pre ev_ld
  have hcB : cB = c := hS.record_eq hrec₀ (Core.hashed_mono hsub_ld hhB) hbaB hexB
  subst cB
  have hrules_lt := recr_rules_size_lt hszB hexB hinfo
  obtain ⟨a', ha'_ref, haA⟩ := ha_pre
  subst haA
  obtain ⟨rawBytes, c', hh, hba, hex, -, hres'⟩ :=
    L1.get_ci_block_trace_spec (hgood.sub hsub_ld).2 ha'_ref ev_ld
  have hcc : c' = c := hS.record_eq hrec₀ (Core.hashed_mono hsub_ld hh) hba hex
  subst c'
  unfold L1.GetCIBlockTraceResult at hres'
  rw [hinfo] at hres'
  obtain ⟨blobs, tree, v, hhp, built, hldv, htr⟩ := hres'
  rw [hld] at hldv
  obtain ⟨hlvls, hp56, hi56, hm56, hmi56, -, tyPtr, rulesPtr, blkPtr, bR, planT, hbR, hblkR, hv,
    rty, hpT, hlT, hrulesTr⟩ := htr
  subst hv
  injection hldv with hv'
  injection hv' with _ _ hfields
  simp only [List.cons.injEq, and_true] at hfields
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hfields
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hhx' : Hashed cs_load bs := hhx
    have hxa' : Address.blake3Pure bs = x := hxa
    have hrun := hS.blobs bs (Core.hashed_mono hsub_ld hhx')
    rw [hxa'] at hrun
    exact hrun
  obtain ⟨tyP, htyP⟩ := LoadedReads.exprReader_read_ok (t := t)
    (blob := fun x => E₀.blobs.get? x) ht (param := id) (self := soloSelf t (Core.ixAddr a'))
    rty (fun i x hx => by simp at hx) hblob
  obtain ⟨-, sB, sA, sortAfter, mH, sR, sortR, sCs, sortCs, mCs, hextS, evS, hmemS, evSort,
    -, hsubSort, hextSM, evM, hsubM⟩ := check_const_rec_arm ev_chk hfr
  obtain ⟨-, hlbb, hdef⟩ := Assembly.validate_expr_well_scoped_spec
    (cx := readCtx t (fun x => E₀.blobs.get? x)) (self := soloSelf t (Core.ixAddr a'))
    hbound hlvls rty hextS htyP evS (hsub_chk _ hmemS)
  have hrd : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t (fun x => E₀.blobs.get? x)) c
      (Ix.Kernel.Reader.recParam (List.range rc.lvls.toNat))
      (soloSelf t (Core.ixAddr a'))).read rc.typ = .ok tyP := by
    rw [Assembly.recParam_range]
    exact htyP
  obtain ⟨E', hann, htm⟩ := rty.toTmC (κ := Core.keyOf t) (ps := List.range rc.lvls.toNat)
    (by simp) (by simpa using hlvls) (LoadedReads.readCtx_keyAt_inv ht _)
    (fun i x m k hx => by simp at hx) hblob hrd hlbb hdef
  have htmS := Decl.tmC_stored_of_usedRefs (E₀ := E) (env := env) (lim := lim) rty
    (recr_typ_usedRefs hinfo) hstored htm
  rw [Decl.posOf_range] at htmS
  have hextM : Heap.Extends m_chk mH :=
    hextS.trans (evS.heap_extends.trans ((Heap.Extends.snoc _ _).trans
      (evSort.heap_extends.trans hextSM)))
  have hsum : ZMod.val ((rc.params.toNat : F) + (rc.motives.toNat : F) + (rc.minors.toNat : F) +
      (rc.indices.toNat : F)) =
      rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat := by
    rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
    exact ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  obtain ⟨parent, pointer, scanHeap, loadedHeap, routedHeap, scanCalls, loadCalls, routeCalls,
    nl, pty, np, ni, nc, pu, blk, idx, lenHeap, lenAfter, kHeap, kAfter, canonHeap, len, kTarget,
    lenCalls, kCalls, canonCalls, canonResult, canonFinal, evScan, hsScan, evLoad, hsLoad, hldP,
    evRoute, hsRoute, hnp, hni, eLen, evLen, hsLen, hlenEq, eK, evK, hsK, hkEq, eC, evCanon,
    hsCanon⟩ :=
    native_rec_member_full evM
  have hsScan' : ∀ x ∈ scanCalls, x ∈ calls := fun x hx => hsub_chk x (hsubM x (hsScan x hx))
  have hsLoad' : ∀ x ∈ loadCalls, x ∈ calls := fun x hx => hsub_chk x (hsubM x (hsLoad x hx))
  let cS : Core.ScopedCtx := Core.Ctx.stored ⟨E, env, t, lim⟩
  have hcS : Core.ScopedCoreFacts cS := hstep.inv.scopedCoreFacts
  have htmM := htmS.mono hextM
  obtain ⟨a, dom, us, ha, hpi, hhead⟩ := Decl.scopedCalleesSpec cS hcS .rec_to_parent_addr _ _ _
    _ _ evScan _ _ _ _ _ rfl (Core.CoreGood.ofRaw (hgood.sub hsScan') (fun _ _ => trivial)) E' htmM
  have hkr : Core.KeysResolved E' := (htmM 0 (fun _ => .sort .zero)).keysResolved
  have hne : cS.κ (Core.ixAddr a) ≠ Core.unresolvedKey :=
    keysResolved_getAppFn (keysResolved_piDomAt _ hkr hpi) hhead
  have hkey : cS.κ (Core.ixAddr a) = Core.keyOf t (Core.ixAddr a) := cS.key_eq hne
  have hhead' := hhead
  rw [hkey] at hhead'
  have hmajA : majorKey rc E' = some (keyOf t (Core.ixAddr a)) :=
    majorKey_of_piDomAt (by rw [← hsum]; exact hpi) hhead'
  obtain ⟨tyP', E'', htyP', hann', hmajP⟩ := htie
  have htyEq : tyP' = tyP := Except.ok.inj (htyP'.symm.trans htyP)
  subst htyEq
  have hkeys : keyOf t P = keyOf t (Core.ixAddr a) :=
    Option.some.inj (hmajP.symm.trans ((majorKey_annotates_eq (rc := rc) hann' hann).trans hmajA))
  have hPa : P = Core.ixAddr a := keyOf_inj hroles hkeys
  subst hPa
  have hgL : Core.Good ⟨E, env, t, lim⟩ loadCalls := hgood.sub hsLoad'
  obtain ⟨rawP, cP, hhP, hbaP, hexP, -, hresP⟩ := L1.get_ci_block_trace_spec hgL.2 ha evLoad
  have hrecP : recordOf E (Core.ixAddr a) = some cm := by
    rw [recordOf_eq_recordAt_of_decoded hst.decoded]
    exact hcm
  obtain ⟨lc, hget, hdec⟩ := LoadedReads.recordOf_inv hrecP
  have hbP : rawP = lc.rawBytes := Core.load_escape hget hgL.1 rawP hhP hbaP
  have hcP : cP = cm := by
    rw [hbP, hdec] at hexP
    exact (Except.ok.inj hexP).symm
  subst hcP
  unfold L1.GetCIBlockTraceResult at hresP
  rw [hcmi] at hresP
  obtain ⟨-, blkBytes, cb', ms', ind', blobs', tree', plan', v₀, hhB', haB', hexB', hcb', hms',
    -, -, -, hld₀, hraw, -⟩ := hresP
  have hrecB : recordOf E ip.block = some cb := by
    rw [recordOf_eq_recordAt_of_decoded hst.decoded]
    exact hcb
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hrecB
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hgL.1 blkBytes hhB' haB'
  have hcbEq : cb' = cb := by
    rw [hbB, hdecB] at hexB'
    exact (Except.ok.inj hexB').symm
  subst hcbEq
  have hmsEq : ms' = ms := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hms)
  subst hmsEq
  have hlist : ms'.toList[ip.idx.toNat]? = ms'[ip.idx.toNat]? := by simp
  rw [hlist, hind] at hms'
  have hindEq : ind = ind' := Ixon.MutConst.indc.inj (Option.some.inj hms')
  subst hindEq
  obtain ⟨hlvlsP, hpP, hiP, hcP56, hidxP, tyPtrP, blkPtrP, bP, hbPa, hblkP, hvP, -⟩ := hraw
  subst hvP
  have hldP0 := hld₀
  rw [hld₀] at hldP
  injection hldP with hvP'
  injection hvP' with _ _ hpf
  simp only [List.cons.injEq, and_true] at hpf
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpf
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, a', bR, a, bP, blobs, tree, planT,
    m_chk, sB, sA, sortAfter, mH, scanHeap, loadedHeap, canonHeap, canonFinal,
    cs_load, sCs, sortCs, scanCalls, loadCalls, canonCalls,
    hrcM, Bytes.repAddressRef_heapMono₂ Core.addrTy ev_ld.heap_extends ha'_ref, rfl,
    hblkR, hbR, hhp, hsub_ld, hblob, built, rty, hpT, hlT, hrulesTr,
    hrules_lt, hidxP, hlvls, hp56, hi56, hm56, hmi56, hlvlsP, hpP, hiP, hcP56,
    hextS, evS, hsub_chk _ hmemS, evSort, fun x hx => hsub_chk x (hsubSort x hx), hextSM,
    evScan, hsScan', ha, rfl, hblkP, hbPa, evLoad.heap_extends, evLoad, hsLoad', hldP0,
    eC, evCanon, fun x hx => hsub_chk x (hsubM x (hsCanon x hx))⟩

/-! ## The type -/

/-- **The type read under `ps`, canonically annotated, at the prefix's keying**: the record's
converted type (no `recur` address) represents the canonical annotation of its reading under
`ps` exactly, under the keying of the prefix that stores the references the record uses. -/
theorem front_type_canon {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {E₀ E : Ixon.Env} {env : Ix.Kernel.Env .anon} {lim : Option Nat}
    {A : _root_.Address} {c : Ixon.Constant} {rc : Ixon.Recursor}
    (hinfo : c.info = .recr rc) (hstored : Decl.UsedRefsStored t env c)
    (hrunBlob : ∀ a b, E₀.blobs.get? a = some b → E.blobs.get? a = some b)
    {ps : List Ix.Kernel.LevelParam} (hperm : ps.Perm (List.range ps.length))
    (hps : ps.length < 4294967296)
    {blobs : List (_root_.Address × ByteArray)} {tree : L1.BinderTreeData}
    {planT : List Core.KLevel} {h : Heap F} {tyPtr : SourceValue F}
    (hagree : L1.BlobReadAgreement (readCtx t (fun x => E.blobs.get? x)).blob blobs)
    (built : L1.BinderTreeBuilt (L1.binderLeavesData c.binders.toList) tree)
    (rty : L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h 4294967295
      rc.typ tyPtr)
    (hpT : L1.binderRootPlan tree c.sharing.toList 0 rc.typ = some planT)
    (hlT : L1.HeapBinderLevels h tyPtr planT)
    {ty : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E₀.blobs.get? x) c (Ix.Kernel.Reader.recParam ps)
      (soloSelf t A)).read rc.typ = .ok ty)
    (hlbb : ty.looseBVarsBounded 0 = true) (hdef : ty.allLevelParamsDefined ps = true) :
    ∃ tyC : Ix.Kernel.Expr .anon,
      LoadedReads.canonAnn c ps 0 rc.typ ty = some tyC ∧ Annotates tyC ty ∧
      Decl.TmCExact (Core.Ctx.stored ⟨E, env, t, lim⟩).κ h (Core.posOf ps tyC) tyPtr := by
  have hty' : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t (fun x => E.blobs.get? x)) c
      (Ix.Kernel.Reader.recParam ps) (soloSelf t A)).read rc.typ = .ok ty :=
    ReaderReads.exprReader_mono hrunBlob hty
  obtain ⟨tyC, hann, htm, htrace⟩ :=
    rty.toTmCExactTrace_of_blobAgreement (κ := Core.keyOf t) (ps := ps) hperm hps
      (LoadedReads.readCtx_keyAt_inv ht _) (fun i x m k hx => by simp at hx) hagree hty'
      hlbb hdef
  have hap := htrace planT hlT []
  rw [List.append_nil] at hap
  refine ⟨tyC, ?_, hann, ?_⟩
  · unfold LoadedReads.canonAnn
    rw [LoadedReads.canonTree_eq built, hpT]
    show (L1.applyBinderTrace (fun level => Core.bmeta (L1.invPosLevel ps level)) ty
      planT).map Prod.fst = some tyC
    rw [hap]
    rfl
  · refine TmCExact.rekey htm (fun a hin => ?_) (fun a hp _ => ?_)
    · rcases rty.addrIn_used a hin with hu | hr
      · obtain ⟨i, hi | ⟨s, hs, his⟩, hr⟩ := hu
        · obtain ⟨ci, hci⟩ := hstored i (recr_typ_usedRefs hinfo i hi) _ hr
          exact Core.Ctx.stored_key_of_find (c := ⟨E, env, t, lim⟩) hci
        · have hmem : i ∈ usedRefIdxs c := by
            unfold usedRefIdxs
            exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, his⟩)
          obtain ⟨ci, hci⟩ := hstored i hmem _ hr
          exact Core.Ctx.stored_key_of_find (c := ⟨E, env, t, lim⟩) hci
      · simp at hr
    · obtain ⟨i, hi | ⟨s, hs, his⟩, hr⟩ := rty.projIn_used a hp
      · obtain ⟨ci, hci⟩ := hstored i (recr_typ_usedRefs hinfo i hi) _ hr
        exact Core.Ctx.stored_projPermitted_of_find (c := ⟨E, env, t, lim⟩) hci
      · have hmem : i ∈ usedRefIdxs c := by
          unfold usedRefIdxs
          exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, his⟩)
        obtain ⟨ci, hci⟩ := hstored i hmem _ hr
        exact Core.Ctx.stored_projPermitted_of_find (c := ⟨E, env, t, lim⟩) hci

/-- **The declared recursor checked at the step's environment**: the scope run and the sort run
on the type pointer, where the pointer represents the canonical annotation exactly under the
prefix's keying. -/
theorem front_constantValCheck {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {lim : Option Nat} (hinv : Decl.PrefixInv.{u} E t lim env)
    (hlv : LvClauses env) {A : _root_.Address} {ps : List Ix.Kernel.LevelParam}
    {ty tyC : Ix.Kernel.Expr .anon} {nlv : Nat}
    (hnl : ps.length = nlv) (hps : ps.length < 4294967296)
    (hperm : ps.Perm (List.range ps.length))
    (hann : Annotates tyC ty) (hlbb : ty.looseBVarsBounded 0 = true)
    (hfv : ty.hasFvar = false) (hfresh : env.find? (keyOf t A) = none)
    (hbasis : Ix.Kernel.reservedBasisNames.contains (keyOf t A) = false)
    {h h₁ h₃ : Heap F} {tyPtr rcv r₁ r₂ : SourceValue F} {cs₁ cs₂ : List (Call F)}
    (htm : Decl.TmCExact (Core.Ctx.stored ⟨E, env, t, lim⟩).κ h (Core.posOf ps tyC) tyPtr)
    (ev_ws : ObsFn Obs.W "KernelCheck::validate_expr_well_scoped"
      [tyPtr, .field 0, .field (nlv : F)] h r₁ h₁ cs₁)
    (hrc : Core.RCRep t lim (h₁ ++ [.construct Core.kexprListEnum "Nil" []]) rcv)
    (hgood : Core.Good ⟨E, env, t, lim⟩ cs₂)
    (ev_sort : ObsFn Obs.W "KernelInfer::k_ensure_sort"
      [rcv, tyPtr, .ptr (.enum Core.kexprListEnum) h₁.length]
      (h₁ ++ [.construct Core.kexprListEnum "Nil" []]) r₂ h₃ cs₂) :
    Ix.Kernel.Semantics.ConstantValCheckJ rulesJ env ⟨keyOf t A, ps, ty⟩ ⟨keyOf t A, ps, tyC⟩ :=
  (constantValCheckJ_of_prefix_lv (c := Core.Ctx.stored ⟨E, env, t, lim⟩)
    (Γ := fun _ => default)
    (cv := ⟨keyOf t A, ps, ty⟩) (cv' := ⟨keyOf t A, ps, tyC⟩) hinv hlv ⟨rfl, rfl, hann⟩
    ⟨by
      show (Value.field ((nlv : Nat) : F) : SourceValue F) = Value.field ((ps.length : Nat) : F)
      rw [hnl], hps, hperm, htm⟩ hlbb hfv hfresh hbasis
    (Decl.isProjFnShape_of_isBaseKey (Decl.isBaseKey_keyOf t _)) ev_ws
    (ev_ws.heap_extends.trans (Heap.Extends.snoc _ _)) hrc
    (Decl.typesRep_alloc_nil _ _ _) hinv.scopedCoreFacts.1 hinv.loads
    (Core.CoreGood.ofRaw hgood (fun _ _ => trivial)) ev_sort).1

/-! ## The rules -/

/-- **The rules read under `ps`, canonically annotated, at the rule keying**: the record's
traced rules represent their canonical rules under `lateRuleKey`, where every reference the
record uses is stored and the only `recur` address is the recursor's own. -/
theorem front_rules_canon {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {E₀ E : Ixon.Env} {env : Ix.Kernel.Env .anon} {lim : Option Nat}
    {A : _root_.Address} {c : Ixon.Constant} {rc : Ixon.Recursor}
    (hinfo : c.info = .recr rc) (hstored : Decl.UsedRefsStored t env c)
    (hrunBlob : ∀ a b, E₀.blobs.get? a = some b → E.blobs.get? a = some b)
    {ps : List Ix.Kernel.LevelParam} (hperm : ps.Perm (List.range ps.length))
    (hps : ps.length < 4294967296)
    {blobs : List (_root_.Address × ByteArray)} {tree : L1.BinderTreeData}
    {h : Heap F} {rulesPtr : SourceValue F}
    (hagree : L1.BlobReadAgreement (readCtx t (fun x => E.blobs.get? x)).blob blobs)
    (built : L1.BinderTreeBuilt (L1.binderLeavesData c.binders.toList) tree)
    (hrulesTr : L1.RulesTraceRep c.refs.toList [A] c.univs.toList c.sharing.toList blobs tree h
      0 (0 + 1) rc.rules.toList rulesPtr)
    {rules : List (Ix.Kernel.RecRule .anon)}
    (hrd : List.Forall₂ (fun ru rl₀ => rl₀.nfields = ru.fields.toNat ∧
      (exprReader t (fun x => E₀.blobs.get? x) c (Ix.Kernel.Reader.recParam ps)
        (soloSelf t A)).read ru.rhs = .ok rl₀.rhs ∧
      rl₀.rhs.looseBVarsBounded 0 = true ∧ rl₀.rhs.allLevelParamsDefined ps = true)
      rc.rules.toList rules) :
    ∃ rlsC : List (Ix.Kernel.RecRule .anon),
      LoadedReads.canonRules c ps rc.k rc.params.toNat (0 + 1) rc.rules.toList rules =
        some rlsC ∧
      List.Forall₂ RuleStored rlsC rules ∧
      Core.RulesRep (lateRuleKey ⟨E, env, t, lim⟩ A) h ps 0 rulesPtr rlsC := by
  have hrd' : List.Forall₂ (fun ru rl₀ => rl₀.nfields = ru.fields.toNat ∧
      (exprReader t (fun x => E.blobs.get? x) c (Ix.Kernel.Reader.recParam ps)
        (soloSelf t A)).read ru.rhs = .ok rl₀.rhs ∧
      rl₀.rhs.looseBVarsBounded 0 = true ∧ rl₀.rhs.allLevelParamsDefined ps = true)
      rc.rules.toList rules :=
    hrd.imp (fun _ _ hx => ⟨hx.1, ReaderReads.exprReader_mono hrunBlob hx.2.1, hx.2.2⟩)
  have hselfk : ∀ i x m k, ([A] : List _root_.Address)[i]? = some x →
      soloSelf t A i = some m → m = .ok k → k = Core.keyOf t x :=
    LoadedReads.soloSelf_key t A
  have hre : ∀ ru ∈ rc.rules.toList, ∀ (q : SourceValue F) (X : Core.KExpr),
      L1.RawConvExpr c.refs.toList [A] c.univs.toList c.sharing.toList blobs h 4294967295
        ru.rhs q → Core.TmC (Core.keyOf t) h X q →
        Core.TmC (lateRuleKey ⟨E, env, t, lim⟩ A) h X q := by
    intro ru hru q X raw rep
    have used : ∀ x, L1.RefUsed c.refs.toList c.sharing.toList ru.rhs x →
        ∃ ci, env.find? (Core.keyOf t x) = some ci := by
      intro x hu
      obtain ⟨i, hi | ⟨s, hs, his⟩, hr⟩ := hu
      · exact hstored i (recr_rule_usedRefs hinfo hru i hi) x hr
      · have hmem : i ∈ usedRefIdxs c := by
          unfold usedRefIdxs
          exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, his⟩)
        exact hstored i hmem x hr
    refine raw.tmC_rekey rep (fun x hu => ?_) (fun x hu => ?_)
    · rcases hu with hu | hr
      · obtain ⟨ci, hci⟩ := used x hu
        have hκ := Core.Ctx.stored_key_of_find (c := ⟨E, env, t, lim⟩) hci
        have hne : (Core.Ctx.stored ⟨E, env, t, lim⟩).κ x ≠ Core.unresolvedKey := by
          rw [hκ]; exact Core.Resolved.ne
        rw [lateRuleKey_keep _ A x hne, hκ]
      · have hxA : x = A := by simpa using hr
        rw [hxA]
        exact lateRuleKey_self _ A
    · obtain ⟨ci, hci⟩ := used x hu
      exact Core.ProjPermitted.of_keep (lateRuleKey_keep _ A)
        (Core.Ctx.stored_projPermitted_of_find (c := ⟨E, env, t, lim⟩) hci)
  obtain ⟨rls, hcR, hstR, hrr, -⟩ := LoadedReads.rules_canon ht hperm hps hselfk hagree built
    (lateRuleKey ⟨E, env, t, lim⟩ A) rc.k rc.params.toNat hrulesTr hre hrd'
  exact ⟨rls, hcR, hstR, hrr⟩

/-! ## The parent's type and the constructor loads -/

/-- **The parent's loaded type is the stored former's**: the scoped `get_ci` at the parent
answers the stored former, whose type at positions the pointer represents. Nothing is said of
the family's telescope constant: the comparison reads it through the recorded binders. -/
theorem front_parent_former {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {lim : Option Nat}
    (hcS : Core.ScopedCoreFacts (Core.Ctx.stored ⟨E, env, t, lim⟩))
    {fam : NativeFam .anon} (hfam : NativeFamStored env fam)
    (hlps : fam.cvS.levelParams = fam.p.cvT.levelParams) {P : _root_.Address}
    (hname : fam.p.cvT.name = keyOf t P) {k : Nat}
    (hk : fam.p.cvT.levelParams = List.range k)
    {parentV pointer : SourceValue F} {bT : Bytes.Address} (hbT' : Core.ixAddr bT = P)
    {scanHeap loadedHeap : Heap F} {loadCalls : List (Call F)}
    (hgL : Core.Good ⟨E, env, t, lim⟩ loadCalls)
    (hbT : Bytes.RepAddressRef Core.addrTy scanHeap bT parentV)
    (evLoad : ObsFn Obs.W "Ingress::get_ci" [parentV] scanHeap pointer loadedHeap loadCalls)
    {nl tyPtrP np ni nc u blk idx : SourceValue F}
    (hldP : loadValue loadedHeap pointer = .ok (.construct "KernelTypes::KConstantInfo" "Induct"
      [nl, tyPtrP, np, ni, nc, u, blk, idx])) :
    Core.TmC (Core.Ctx.stored ⟨E, env, t, lim⟩).κ loadedHeap fam.cvS.type tyPtrP := by
  let cS : Core.ScopedCtx := Core.Ctx.stored ⟨E, env, t, lim⟩
  have hformer : env.find? (Core.keyOf t P) =
      some (.indInfo fam.cvS (Ix.Kernel.nativeCaps fam.p)) := by
    rw [LoadedReads.keyOf_eq, ← hname]
    exact hfam.former
  have hκP : cS.κ P = Core.keyOf t P :=
    Core.Ctx.stored_key_of_find (c := ⟨E, env, t, lim⟩) hformer
  obtain ⟨ci, hfind, hptr⟩ := Core.get_ci_step cS hcS evLoad parentV bT rfl trivial
    (by rw [hbT', hκP]; exact Core.Resolved.ne)
    (Core.CoreGood.ofRaw hgL (fun _ _ => trivial)) hbT
  rw [hbT', hκP] at hfind
  have hci : ci = .indInfo fam.cvS (Ix.Kernel.nativeCaps fam.p) :=
    Option.some.inj (hfind.symm.trans hformer)
  subst hci
  obtain ⟨v, hv, hrep⟩ := hptr
  rw [hldP] at hv
  injection hv with hv
  subst hv
  obtain ⟨cv, caps, hcv, hval⟩ := ciRep_induct_fields hrep
  obtain ⟨hcvEq, -⟩ := Ix.Kernel.ConstantInfo.indInfo.inj hcv
  subst hcvEq
  obtain ⟨-, -, -, htm⟩ := hval
  rw [hlps, hk, Decl.posOf_range] at htm
  exact htm

/-- **The constructor loads of the member, as the comparison reads them**: every scoped
`get_ci_cprj` load of constructor `j` of member `idx` of the block at `bP`, within calls good
for the step's store, answers the stored constructor `j` of the family: its key, its field count
with the bound the load contract keeps (`Core.CIRep.ctor_fields`), and its stored type at
positions. The member index and the constructor count are asked at what the parent's load
gives. -/
theorem front_ctor_loads_count {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {lim : Option Nat}
    (hcS : Core.ScopedCoreFacts (Core.Ctx.stored ⟨E, env, t, lim⟩))
    {fam : NativeFam .anon} (hfam : NativeFamStored env fam) {k : Nat}
    (hk : fam.p.cvT.levelParams = List.range k)
    {bP : Bytes.Address} {idx : Nat} (hidx : idx < 72057594037927936)
    (hlen : fam.ctorsA.length < 72057594037927936)
    (hnames : ∀ (j : Nat) (cA : ConstantVal .anon × Nat), fam.ctorsA[j]? = some cA →
      cA.1.name = keyOf t (Core.cprjAddr (Core.ixAddr bP) idx j))
    {x_block : SourceValue F} {cs : List (Call F)}
    (hgood : Core.Good ⟨E, env, t, lim⟩ cs) :
    Decl.NatCtorLoadT (Core.Ctx.stored ⟨E, env, t, lim⟩).κ bP idx k (lateCtorsInfo fam)
      x_block cs := by
  intro j hj p9 h m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50 hsub hb ev hld info hinfo
  obtain ⟨cA, ks, hcA, hks, rfl⟩ := front_lateCtorsInfo_getElem? hinfo
  have hjlt : j < fam.ctorsA.length := (List.getElem?_eq_some_iff.mp hcA).1
  obtain ⟨hfindN, hlpsC, -⟩ := hfam.ctor j cA hcA
  rw [hnames j cA hcA, ← LoadedReads.keyOf_eq] at hfindN
  have hκ : (Core.Ctx.stored ⟨E, env, t, lim⟩).κ (Core.cprjAddr (Core.ixAddr bP) idx j) =
      Core.keyOf t (Core.cprjAddr (Core.ixAddr bP) idx j) :=
    Core.Ctx.stored_key_of_find (c := ⟨E, env, t, lim⟩) hfindN
  have hidxv : ZMod.val ((idx : Nat) : F) = idx :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  have hjv : ZMod.val ((j : Nat) : F) = j :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  have hfind' : (Core.Ctx.stored ⟨E, env, t, lim⟩).env.find?
      ((Core.Ctx.stored ⟨E, env, t, lim⟩).κ (Core.cprjAddr (Core.ixAddr bP)
        (ZMod.val ((idx : Nat) : F)) (ZMod.val ((j : Nat) : F)))) =
      some (.ctorInfo cA.1 fam.p.nP cA.2) := by
    rw [hidxv, hjv, hκ]
    exact hfindN
  obtain ⟨-, hctor⟩ := Core.get_ci_cprj_step _ hcS.base ev x_block ((idx : Nat) : F)
    ((j : Nat) : F) bP rfl trivial (Or.inr ⟨_, _, _, _, hfind'⟩)
    (Core.CoreGood.ofRaw (hgood.sub hsub) (fun _ _ => trivial)) hb
  obtain ⟨v, hv, hrep⟩ := hctor _ _ _ hfind'
  rw [hld] at hv
  injection hv with hv
  rw [← hv] at hrep
  obtain ⟨cv', nP', nF', hci, hvr, -, hnf', hcounts, -⟩ := Core.CIRep.ctor_fields hrep
  obtain ⟨rfl, rfl, rfl⟩ := Ix.Kernel.ConstantInfo.ctorInfo.inj hci
  obtain ⟨-, -, -, htmC⟩ := hvr
  rw [hlpsC, hk] at htmC
  refine ⟨?_, hnf', hcounts.2, htmC 0 (fun _ => default)⟩
  show cA.1.name = (Core.Ctx.stored ⟨E, env, t, lim⟩).κ
    (Core.cprjAddr (Core.ixAddr bP) idx j)
  rw [hκ, hnames j cA hcA, LoadedReads.keyOf_eq]

end IxVM.Refinement.Typing
