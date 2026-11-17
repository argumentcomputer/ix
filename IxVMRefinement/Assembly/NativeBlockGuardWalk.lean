import IxVMRefinement.Assembly.NativeBlockGuardSyn
import IxVMRefinement.Assembly.NativeBlockStage
import IxVMRefinement.Assembly.NativeBlockNewFacts
import IxVMRefinement.Infer.Proj
import IxVMRefinement.Decl.NativeRec
import IxVMRefinement.Decl.Common
import IxVMRefinement.Decl.NativeFront
import IxVMRefinement.L1.Stream
import IxC.Kernel.Verify.Inductives.StructBody

/-! # A functional spec of the circuit's projection guard

`KernelInfer::proj_guard(rc, block, idx, fidx)` loads constructor `0` of member `idx` of the block
(`Ingress::get_ci_cprj`), peels its `np` parameter binders (`peel_n_foralls_with_types`) and then
walks the field binders (`proj_guard_walk`): at field `j ≤ fidx` it computes the sort
`s_j = k_ensure_sort(rc, dom_j, ctx)` of the field's domain, opened at the parameters and the
earlier fields; below `fidx` it keeps `s_j` when `expr_has_bvar_at(body, 0)` answers `1`; and it
joins the kept sorts onto `s_fidx` in field order (`proj_guard_fold`). `ProjAux.proj_guard_rep`
gives only a represented level; this file gives the level itself, in the shape of IxC's
`structProjGuards`, with a derivation of each field sort.

The sorts are read at a context that has `ScopedCoreFacts`: the constructor stage
`Decl.ctorStage ⟨E, env, t, some n⟩ cvS capsS` (the former stored over the prefix). Its keying
resolves every reference the block's record uses (stored in the prefix) and the former's
projection address, the block's only recursive address; that is all the canonical constructor
load needs (`LoadedReads.get_ci_cprj_load_canon_at`, `get_ci_cprj_load_at` with the canonical
annotation named).

* `Core.GuardWalk.peel_open`, `Core.GuardWalk.walk_open`: the two walks over a heap term read
  twice: opened at the next depth at each binder (IxC's `openPisAtFvars`, for the sorts), and raw
  at local depth the number of binders passed (IxC's `stripPis`, for the occurrence test of
  `structUsedLater`). Every cell on a run's path is a `Forall` cell, so the two readings advance
  together; the peel stops early only at a cell that is no `Forall`, where the walk cannot start.
* `Core.GuardWalk.proj_guard_open`: the spec at any scoped context, given that the constructor
  load represents a constructor whose level parameters are positions.
* `projGuard_fieldSorts`: the spec at the constructor stage of a native block's install, for the
  constructor the environment after the install stores at the block's constructor key.
* `projGuardWalkAt_of_install`: the same as `ProjGuardWalkAt` (`NativeBlockGuardSyn.lean`) at a
  one-constructor install.
-/

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IxVM.Refinement.LoadedReads

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency

section At

variable {t : Ix.Kernel.RoleTable}

/-- **`get_ci_cprj_load_at` with the canonical annotation named**: a direct constructor load on a
held block represents, at any keying that agrees with the table's on the references the block
uses and on the block's member addresses, the constructor whose type is the canonical annotation
of the slot's reading. -/
theorem get_ci_cprj_load_canon_at (ht : t.check = .ok ()) {E : Ixon.Env} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbound : Bounded cs)
    {b : Aiur.Library.Bytes.Address} {blkArg ptr : SourceValue F} {i j : F} {h h' : Heap F}
    (hb : Aiur.Library.Bytes.RepAddressRef Core.addrTy h b blkArg)
    (ev : ObsFn Core.W "Ingress::get_ci_cprj" [blkArg, .field i, .field j] h ptr h' cs)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hblock : recordOf E (Core.ixAddr b) = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[i.val]? = some (.indc ind))
    (hctys : ∀ (k : Nat) (ct : Ixon.Constructor), ind.ctors[k]? = some ct →
      ct.cidx.toNat = k ∧ ∃ cty : Ix.Kernel.Expr .anon,
        (exprReader t (fun x => E.blobs.get? x) cb id
          (blockSelf t (Core.ixAddr b) ms)).read ct.typ = .ok cty ∧
        cty.looseBVarsBounded 0 = true ∧
        cty.allLevelParamsDefined (List.range ct.lvls.toNat) = true) :
    ∃ (ct : Ixon.Constructor) (cty ty' : Ix.Kernel.Expr .anon), ind.ctors[j.val]? = some ct ∧
      (exprReader t (fun x => E.blobs.get? x) cb id
        (blockSelf t (Core.ixAddr b) ms)).read ct.typ = .ok cty ∧
      canonAnn cb (List.range ct.lvls.toNat)
        (((L1.mutsRootOffset ms.toList i.val : Nat) : F) + 1 + ((j.val : Nat) : F))
        ct.typ cty = some ty' ∧
      ∀ κ : _root_.Address → Core.KKey,
        (∀ i ∈ usedRefIdxs cb, ∀ x, cb.refs.toList[i]? = some x →
          κ x = Core.keyOf t x ∧ Core.ProjPermitted κ x) →
        (∀ x ∈ L1.blockRecurAddrs (Core.ixAddr b) ms.toList, κ x = Core.keyOf t x) →
        Core.CIPtrRep κ h' ptr
          (.ctorInfo ⟨κ (Core.cprjAddr (Core.ixAddr b) i.val j.val),
            List.range ct.lvls.toNat, ty'⟩ ct.params.toNat ct.fields.toNat) := by
  obtain ⟨-, -, -, blkBytes, cb', ms', ind', ct, blobs, v, hhB, haB, hexB, -, hcb, hms, hcts,
    hhp, hld, hraw, tree, plan, built, planned, hlev⟩ := L1.get_ci_cprj_origin_spec hbound hb ev
  rw [← ZMod.natCast_zmod_val j] at planned
  obtain ⟨lcB, hgetB, hdecB⟩ := recordOf_inv hblock
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hnc blkBytes hhB haB
  have hcB : cb = cb' := by
    rw [hbB, hdecB] at hexB
    exact Except.ok.inj hexB
  subst hcB
  have hmsEq : ms = ms' := Ixon.ConstantInfo.muts.inj (hmuts.symm.trans hcb)
  subst hmsEq
  have hms' : ms[i.val]? = some (.indc ind') := by
    rw [← Array.getElem?_toList]
    exact hms
  have hiEq : ind = ind' := Ixon.MutConst.indc.inj (Option.some.inj (hmem.symm.trans hms'))
  subst hiEq
  have hct : ind.ctors[j.val]? = some ct := by
    rw [← Array.getElem?_toList]
    exact hcts
  have hctm : ct ∈ ind.ctors.toList := List.mem_of_getElem? hcts
  obtain ⟨hcidx, cty, hty, hty_lbb, hty_def⟩ := hctys j.val ct hct
  have hagree := blobReadAgreement_of_noCollision hnc hhp t
  obtain ⟨ty', hcT, -, hrepS⟩ :=
    ctor_value_at ht hmuts hmem hctm hcidx hagree built planned hraw hlev hty hty_lbb hty_def
  exact ⟨ct, cty, ty', hct, hty, hcT, fun κ hused hrecur => ⟨_, hld, hrepS κ hused hrecur⟩⟩

end At

end IxVM.Refinement.LoadedReads

namespace IxVM.Refinement.Core.GuardWalk

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red Infer)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)

/-! ## The guard's fold -/

/-- **The levels a guard joins**: the entries of `lus` at the positions `flags` marks, in
order. -/
def selDeps : List KLevel → List Bool → List KLevel
  | _, [] => []
  | ls, b :: bs => (if b then [ls.headD .zero] else []) ++ selDeps ls.tail bs

/-- **`structProjGuards`' fold is the fold of the joined levels.** -/
theorem foldl_range_selDeps :
    ∀ (flags : List Bool) (lus : List KLevel) (acc : KLevel),
      (List.range flags.length).foldl
          (fun acc j => if flags.getD j false then Ix.Kernel.Level.max acc (lus.getD j .zero)
            else acc) acc =
        (selDeps lus flags).foldl (fun a b => Ix.Kernel.Level.max a b) acc
  | [], lus, acc => rfl
  | b :: bs, lus, acc => by
    rw [List.length_cons, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    cases lus with
    | nil =>
      cases b
      · exact foldl_range_selDeps bs [] acc
      · exact foldl_range_selDeps bs [] (Ix.Kernel.Level.max acc .zero)
    | cons l ls =>
      cases b
      · exact foldl_range_selDeps bs ls acc
      · exact foldl_range_selDeps bs ls (Ix.Kernel.Level.max acc l)

private theorem klevel_node_eq' :
    Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» =
      IxVM.Refinement.KernelLevels.klevelListEnum := by decide +kernel

/-- **`proj_guard_fold` joins the list onto the accumulator, in order.** -/
theorem fold_eq :
    ∀ {ls : List KLevel} {h h' : Heap F} {x_acc x_deps r : SourceValue F}
      {calls : List (Call F)} {acc : KLevel},
      ObsFn W "KernelInfer::proj_guard_fold" [x_acc, x_deps] h r h' calls →
      RepKLevel h acc x_acc → RepKLevelList h ls x_deps →
      RepKLevel h' (ls.foldl (fun a b => Ix.Kernel.Level.max a b) acc) r := by
  intro ls
  induction ls with
  | nil =>
    intro h h' x_acc x_deps r calls acc ev hacc hls
    rcases Obs.«KernelInfer::proj_guard_fold».obs ev with
      ⟨_, he21, he22, _⟩ |
      ⟨x_d, x_rest, cs44, m50, ld12, _, _, _⟩
    · subst he21 he22
      exact hacc
    · rw [klevel_node_eq'] at ld12
      cases hls with
      | nil cell => exact (load_cell_ne cell ld12 (by decide)).elim
  | cons d0 ls' ih =>
    intro h h' x_acc x_deps r calls acc ev hacc hls
    rcases Obs.«KernelInfer::proj_guard_fold».obs ev with
      ⟨ld12, _, _, _⟩ |
      ⟨x_d, x_rest, cs44, m50, ld12, hm58, ev46, _⟩
    · rw [klevel_node_eq'] at ld12
      cases hls with
      | cons cell _ _ => exact (load_cell_ne cell ld12 (by decide)).elim
    · rw [klevel_node_eq'] at ld12
      obtain ⟨d1, ls1, heq, hd, hrest⟩ := RepList.cons_of_load hls ld12
      injection heq with hd_eq hls_eq
      subst hd_eq hls_eq hm58
      have ext := Heap.Extends.snoc h (.construct "KernelTypes::KLevelNode" "Max" [x_acc, x_d])
      have hmax : RepKLevel (h ++ [.construct "KernelTypes::KLevelNode" "Max" [x_acc, x_d]])
          (.max acc d0) (.ptr (.enum "KernelTypes::KLevelNode") h.length) :=
        .max List.getElem?_concat_length (hacc.mono ext) (hd.mono ext)
      exact ih ev46 hmax (RepKLevelList.mono hrest ext)

/-! ## Telescope steps -/

theorem openPisAtFvars_succ_forallE {n : Nat} {D B : KExpr} {m : Ix.Kernel.BinderMeta} {i : Nat}
    {xs : List KExpr} {body : KExpr}
    (h : Ix.Kernel.openPisAtFvars (n + 1) (.forallE D B m) i = some (xs, body)) :
    ∃ fvs, xs = .fvar i D :: fvs ∧
      Ix.Kernel.openPisAtFvars n (B.instantiate1 (.fvar i D)) (i + 1) = some (fvs, body) := by
  simp only [Ix.Kernel.openPisAtFvars] at h
  split at h
  · next fvs' e' h' =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fvs', rfl, h'⟩
  · exact nomatch h

theorem openPisAtFvars_succ_forallE_of {n : Nat} {D B : KExpr} {m : Ix.Kernel.BinderMeta}
    {i : Nat} {fvs : List KExpr} {body : KExpr}
    (h : Ix.Kernel.openPisAtFvars n (B.instantiate1 (.fvar i D)) (i + 1) = some (fvs, body)) :
    Ix.Kernel.openPisAtFvars (n + 1) (.forallE D B m) i = some (.fvar i D :: fvs, body) := by
  first
    | (simp only [Ix.Kernel.openPisAtFvars, h]; done)
    | (simp [Ix.Kernel.openPisAtFvars, h]; done)
    | (simp only [Ix.Kernel.openPisAtFvars]; rw [h])

theorem stripPis_succ_forallE {k : Nat} {D B : KExpr} {m : Ix.Kernel.BinderMeta}
    {bs : List (KExpr × Ix.Kernel.BinderMeta)} {rest : KExpr}
    (h : (Ix.Kernel.Expr.forallE D B m).stripPis (k + 1) = some (bs, rest)) :
    ∃ bs', B.stripPis k = some (bs', rest) := by
  simp only [Ix.Kernel.Expr.stripPis, Option.map_eq_some_iff] at h
  obtain ⟨⟨bs', rest'⟩, h', heq⟩ := h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨-, rfl⟩ := heq
  exact ⟨bs', h'⟩

theorem stripPis_succ_forallE_of {k : Nat} {D B : KExpr} {m : Ix.Kernel.BinderMeta}
    {bs : List (KExpr × Ix.Kernel.BinderMeta)} {rest : KExpr}
    (h : B.stripPis k = some (bs, rest)) :
    (Ix.Kernel.Expr.forallE D B m).stripPis (k + 1) = some ((D, m) :: bs, rest) := by
  first
    | (simp only [Ix.Kernel.Expr.stripPis, h, Option.map_some']; done)
    | (simp [Ix.Kernel.Expr.stripPis, h]; done)
    | (rw [Ix.Kernel.Expr.stripPis, h]; rfl)

/-! ## The parameter peel, read twice -/

/-- **`peel_n_foralls_with_types` read opened and raw**: on a heap term read opened at depth `d`
(`E`) and raw at local depth `kr` (`R`), the peel passes `m' ≤ m` binders; the result is read
opened at depth `d + m'` as IxC's `openPisAtFvars m' E d` residual and raw at local depth
`kr + m'` as `R.stripPis m'`'s; if it passes fewer than `m`, the result's cell is no `Forall`. -/
theorem peel_open (c : ScopedCtx) (Γ0 : Nat → KExpr) :
    ∀ (m : Nat) {x_e x_types x_after x_ctx : SourceValue F} {h h' : Heap F}
      {calls : List (Call F)} (n : F), ZMod.val n = m →
      ObsFn W "KernelCheck::peel_n_foralls_with_types" [x_e, .field n, x_types] h
        (.tuple [x_after, x_ctx]) h' calls →
      ∀ (d : Nat) (Γ : Nat → KExpr) (E : KExpr) (kr : Nat) (R : KExpr),
        c.types Γ h d x_types → c.tm d Γ h E x_e → Tm c.κ 0 Γ0 h kr R x_e →
        ∃ (m' : Nat) (Γ' : Nat → KExpr) (E' R' : KExpr) (fvs : List KExpr)
          (bs : List (KExpr × Ix.Kernel.BinderMeta)),
          m' ≤ m ∧ c.types Γ' h' (d + m') x_ctx ∧ c.tm (d + m') Γ' h' E' x_after ∧
          Tm c.κ 0 Γ0 h' (kr + m') R' x_after ∧
          Ix.Kernel.openPisAtFvars m' E d = some (fvs, E') ∧ R.stripPis m' = some (bs, R') ∧
          (m' < m → ∃ v, loadValue h' x_after = .ok v ∧
            ∀ vs : List (SourceValue F), vs.length = 3 →
              v ≠ .construct "KernelTypes::KExprNode" "Forall" vs) := by
  intro m
  induction m with
  | zero =>
    intro x_e x_types x_after x_ctx h h' calls n hn ev d Γ E kr R htypes hE hR
    have hn0 : n = 0 := (ZMod.val_eq_zero n).mp hn
    subst hn0
    rcases Obs.«KernelCheck::peel_n_foralls_with_types».obs ev with
      ⟨_, he19, he34, _⟩ |
      ⟨x_dom, x_body, w59, m76, cs109, v113, hne36, ld51, hm86, op135, ev111, hc144⟩ |
      ⟨v40, hne36, ld51, hne145, he153, he168, _⟩
    · simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he19
      obtain ⟨rfl, rfl⟩ := he19
      subst he34
      exact ⟨0, Γ, E, R, [], [], Nat.le_refl 0, htypes, hE, hR, rfl, rfl,
        fun hlt => absurd hlt (Nat.lt_irrefl 0)⟩
    · exact absurd rfl hne36
    · exact absurd rfl hne36
  | succ m ih =>
    intro x_e x_types x_after x_ctx h h' calls n hn ev d Γ E kr R htypes hE hR
    have hn0 : n ≠ 0 := by
      intro e
      rw [e, ZMod.val_zero] at hn
      omega
    rcases Obs.«KernelCheck::peel_n_foralls_with_types».obs ev with
      ⟨hv14, _, _, _⟩ |
      ⟨x_dom, x_body, w59, m76, cs109, v113, _, ld51, hm86, op135, ev111, hc144⟩ |
      ⟨v40, _, ld51, hne145, he153, he168, _⟩
    · exact absurd (Value.field.inj hv14) hn0
    · subst hm86
      have hv113 : v113 = .field (n - 1) := NatAux.sub_ok op135
      subst hv113
      have hnv : ZMod.val (n - 1) = m := by
        have := NatAux.val_sub_one hn0
        omega
      obtain ⟨D, B, ℓ, rfl, hD, hB, -⟩ := hE.forallE_of_load ld51
      obtain ⟨RD, RB, ℓr, rfl, -, hRB, -⟩ := hR.forallE_of_load ld51
      have ext := Heap.Extends.snoc h (.construct kexprListEnum "Cons" [x_dom, x_types])
      have htypes' := ProjAux.types_extend htypes hD
      have hbody := Tm.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D)
        (Tm.mono ext hB)
      obtain ⟨m', Γ', E', R', fvs, bs, hm', ht', hE', hR', hop, hst, hstop⟩ :=
        ih (n - 1) hnv ev111 (d + 1) _ _ (kr + 1) RB htypes' hbody (Tm.mono ext hRB)
      refine ⟨m' + 1, Γ', E', R', .fvar d D :: fvs, (RD, bmeta ℓr) :: bs, by omega, ?_, ?_, ?_,
        openPisAtFvars_succ_forallE_of hop, stripPis_succ_forallE_of hst,
        fun hlt => hstop (by omega)⟩
      · rw [show d + (m' + 1) = d + 1 + m' by omega]
        exact ht'
      · rw [show d + (m' + 1) = d + 1 + m' by omega]
        exact hE'
      · rw [show kr + (m' + 1) = kr + 1 + m' by omega]
        exact hR'
    · simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he153
      obtain ⟨rfl, rfl⟩ := he153
      subst he168
      exact ⟨0, Γ, E, R, [], [], Nat.zero_le _, htypes, hE, hR, rfl, rfl,
        fun _ => ⟨v40, ld51, hne145⟩⟩

/-! ## The field walk, read twice -/

/-- **`proj_guard_walk` read opened and raw**: on a heap term read opened at depth `d` (`E`) and
raw at local depth `kr` (`R`), with `K = fidx` fields left, the walk computes the fold of
`ls ++ selDeps lus flags` onto `lus[K]`, where `lus[j]` is semantically the sort of a full-grade
derivation of the `j`-th domain IxC's `openPisAtFvars` opens from `E` at `d`, and `flags[j]` is
set wherever the raw body after the `j`-th binder of `R` has a loose occurrence of its
variable. The walk starts at a `Forall` cell. -/
theorem walk_open (c : ScopedCtx) (hc : ScopedCoreFacts c) (Γ0 : Nat → KExpr) :
    ∀ (K : Nat) {x_rc x_ty x_ctx x_deps r : SourceValue F} {h h' : Heap F}
      {calls : List (Call F)} (k : F), ZMod.val k = K → CoreGood c calls →
      ObsFn W "KernelInfer::proj_guard_walk" [x_rc, x_ty, x_ctx, .field k, x_deps] h r h' calls →
      ∀ (d : Nat) (Γ : Nat → KExpr) (E : KExpr) (kr : Nat) (R : KExpr) (ls : List KLevel),
        c.rc h x_rc → c.types Γ h d x_ctx → c.tm d Γ h E x_ty → Tm c.κ 0 Γ0 h kr R x_ty →
        RepKLevelList h ls x_deps →
        (∃ x y z, loadValue h x_ty = .ok (.construct "KernelTypes::KExprNode" "Forall" [x, y, z])) ∧
        ∃ (lus : List KLevel) (flags : List Bool), lus.length = K + 1 ∧ flags.length = K ∧
          RepKLevel h' ((ls ++ selDeps lus flags).foldl (fun a b => Ix.Kernel.Level.max a b)
            (lus.getD K .zero)) r ∧
          (∀ (n : Nat) (xFvs : List KExpr) (body : KExpr), K + 1 ≤ n →
            Ix.Kernel.openPisAtFvars n E d = some (xFvs, body) →
            ∀ j, j ≤ K → ∃ (x T : KExpr) (u : KLevel), xFvs[j]? = some x ∧
              Infer c.env .full (d + j) x.fvarTypeD T ∧ Red c.env (d + j) T (.sort u) ∧
              LvEq u (lus.getD j .zero)) ∧
          (∀ j, j < K → flags.getD j false = false →
            ∀ (bs : List (KExpr × Ix.Kernel.BinderMeta)) (rest : KExpr),
              R.stripPis (j + 1) = some (bs, rest) → rest.hasLooseBVar 0 = false) := by
  intro K
  induction K with
  | zero =>
    intro x_rc x_ty x_ctx x_deps r h h' calls k hk good ev d Γ E kr R ls hrc htypes hE hR hls
    have hk0 : k = 0 := (ZMod.val_eq_zero k).mp hk
    subst hk0
    rcases Obs.«KernelInfer::proj_guard_walk».obs ev with
      ⟨x_dom, x_body, w16, v32, m33, cs43, cs87, ld11, ev45, _, ev89, hc106⟩ |
      ⟨x_dom, x_body, w16, v32, m33, cs43, v176, m177, cs179, cs188, v194, m211,
        ld11, ev45, hne107, sg184, hm219, op252, ev190, hc261⟩
    · subst hc106
      obtain ⟨D, B, ℓ0, rfl, hD, -, -⟩ := hE.forallE_of_load ld11
      have g43 : CoreGood c cs43 := good.sub fun x hx => by simp [hx]
      obtain ⟨stype, u, ℓ, hinf, hred, hℓ, heq⟩ :=
        Decl.scoped_core_ensure_sort hrc htypes.1 htypes.2 hc.env hc.loads g43 ev45 hD
      have e45 := ObsFn.heap_extends ev45
      refine ⟨⟨_, _, _, ld11⟩, [ℓ], [], rfl, rfl, ?_, ?_, ?_⟩
      · have hf := fold_eq ev89 hℓ (RepKLevelList.mono hls e45)
        have e1 : selDeps [ℓ] [] = [] := rfl
        have e2 : ([ℓ] : List KLevel).getD 0 .zero = ℓ := rfl
        rw [e1, e2, List.append_nil]
        exact hf
      · intro n xFvs body hn hop j hj
        have hj0 : j = 0 := by omega
        subst hj0
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        obtain ⟨fvs, rfl, -⟩ := openPisAtFvars_succ_forallE hop
        exact ⟨.fvar d D, stype, u, rfl, hinf, hred, heq⟩
      · intro j hj
        exact absurd hj (Nat.not_lt_zero j)
    · exact absurd rfl hne107
  | succ K ih =>
    intro x_rc x_ty x_ctx x_deps r h h' calls k hk good ev d Γ E kr R ls hrc htypes hE hR hls
    have hk0 : k ≠ 0 := by
      intro e
      rw [e, ZMod.val_zero] at hk
      omega
    rcases Obs.«KernelInfer::proj_guard_walk».obs ev with
      ⟨x_dom, x_body, w16, v32, m33, cs43, cs87, ld11, ev45, hv83, ev89, hc106⟩ |
      ⟨x_dom, x_body, w16, v32, m33, cs43, v176, m177, cs179, cs188, v194, m211,
        ld11, ev45, hne107, sg184, hm219, op252, ev190, hc261⟩
    · exact absurd (Value.field.inj hv83) hk0
    · subst hc261
      obtain ⟨D, B, ℓ0, rfl, hD, hB, -⟩ := hE.forallE_of_load ld11
      obtain ⟨RD, RB, ℓr, rfl, -, hRB, -⟩ := hR.forallE_of_load ld11
      have g43 : CoreGood c cs43 := good.sub fun x hx => by simp [hx]
      obtain ⟨stype, u, ℓ, hinf, hred, hℓ, heq⟩ :=
        Decl.scoped_core_ensure_sort hrc htypes.1 htypes.2 hc.env hc.loads g43 ev45 hD
      have e45 := ObsFn.heap_extends ev45
      -- the flag of this field and the levels kept so far
      obtain ⟨b, ls', hls177, e33_177, hb, hbflag⟩ : ∃ (b : Bool) (ls' : List KLevel),
          RepKLevelList m177 ls' v176 ∧ Heap.Extends m33 m177 ∧
          ls' = ls ++ (if b then [ℓ] else []) ∧ (b = false → RB.hasLooseBVar 0 = false) := by
        rcases sg184 with
          ⟨m112, cs123, cs148, ev125, ev150, hc167⟩ |
          ⟨v111, m112, cs123, ev125, hne168, he173, he174, hc175⟩
        · have e125 := ObsFn.heap_extends ev125
          have e150 := ObsFn.heap_extends ev150
          refine ⟨true, ls ++ [ℓ],
            ProjAux.lv_snoc ev150 (RepKLevelList.mono (RepKLevelList.mono hls e45) e125)
              (hℓ.mono e125),
            e125.trans e150, ?_, fun hf => by cases hf⟩
          first | rfl | simp
        · subst he173 he174 hc175
          have e125 := ObsFn.heap_extends ev125
          have g123 : CoreGood c cs123 := good.sub fun x hx => by simp [hx]
          obtain ⟨-, h01, -⟩ := SubstAux.gall c.κ .expr_has_bvar_at _ _ _ _ _ ev125 x_body 0 rfl
            g123.bounded
          have hv0 : v111 = .field 0 := h01.resolve_right hne168
          subst hv0
          have hno := (Decl.expr_has_bvar_at_zero_spec (k := kr + 1) (j := 0) (by omega)
            (by decide) g123.bounded (Tm.mono e45 hRB) (by rw [Nat.cast_zero]; exact ev125)).1
          refine ⟨false, ls, RepKLevelList.mono (RepKLevelList.mono hls e45) e125, e125, ?_,
            fun _ => hno⟩
          first | rfl | simp
      subst hm219
      have hv194 : v194 = .field (k - 1) := NatAux.sub_ok op252
      subst hv194
      have hkv : ZMod.val (k - 1) = K := by
        have := NatAux.val_sub_one hk0
        omega
      have e211 := Heap.Extends.snoc m177 (.construct kexprListEnum "Cons" [x_dom, x_ctx])
      have E177 : Heap.Extends h m177 := e45.trans e33_177
      have E211 : Heap.Extends h _ := E177.trans e211
      have htypes211 := ProjAux.types_extend (types_mono E177 htypes) (Tm.mono E177 hD)
      have hbody211 := Tm.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D)
        (Tm.mono E211 hB)
      have g188 : CoreGood c cs188 := good.sub fun x hx => by simp [hx]
      obtain ⟨-, lus', flags', hlen1, hlen2, hfold, hpos, hflag⟩ :=
        ih (k - 1) hkv g188 ev190 (d + 1) _ _ (kr + 1) RB ls' (RCRep.mono E211 hrc)
          htypes211 hbody211 (Tm.mono E211 hRB) (RepKLevelList.mono hls177 e211)
      refine ⟨⟨_, _, _, ld11⟩, ℓ :: lus', b :: flags', by simp [hlen1], by simp [hlen2], ?_, ?_,
        ?_⟩
      · have e1 : ls ++ selDeps (ℓ :: lus') (b :: flags') = ls' ++ selDeps lus' flags' := by
          show ls ++ ((if b then [ℓ] else []) ++ selDeps lus' flags') = ls' ++ selDeps lus' flags'
          rw [hb, List.append_assoc]
        rw [e1]
        exact hfold
      · intro n xFvs body hn hop j hj
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        obtain ⟨fvs, rfl, hop'⟩ := openPisAtFvars_succ_forallE hop
        cases j with
        | zero => exact ⟨.fvar d D, stype, u, rfl, hinf, hred, heq⟩
        | succ j =>
          obtain ⟨x, T, u', hx, hi, hr, hq⟩ := hpos n' fvs body (by omega) hop' j (by omega)
          refine ⟨x, T, u', hx, ?_, ?_, hq⟩
          · rw [show d + (j + 1) = d + 1 + j by omega]
            exact hi
          · rw [show d + (j + 1) = d + 1 + j by omega]
            exact hr
      · intro j hj hfl bs rest hst
        obtain ⟨bs', hst'⟩ := stripPis_succ_forallE hst
        cases j with
        | zero =>
          have h0 : (some ([], RB) : Option (List (KExpr × Ix.Kernel.BinderMeta) × KExpr)) =
              some (bs', rest) := hst'
          obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h0)
          exact hbflag hfl
        | succ j => exact hflag j (by omega) hfl bs' rest hst'

/-! ## The guard -/

/-- **The projection guard, functionally**, at a scoped context with its core facts: when the
constructor load of the run represents a constructor of type `T` at positional level
parameters, with `nP` parameters and `nF` fields, and the field index is below `nF`, the guard
level is `structProjGuards`' fold of represented levels `lus` under `flags`; each `lus[j]`,
`j ≤ fidx`, is semantically the sort of a full-grade derivation, at the context's environment,
of the `j`-th field domain IxC's constructor stage opens; and every earlier field a later binder
uses (`structUsedLater`) is flagged. -/
theorem proj_guard_open (c : ScopedCtx) (hc : ScopedCoreFacts c)
    {x_rc bp r : SourceValue F} {i f : F} {h h' : Heap F} {calls : List (Call F)}
    (good : CoreGood c calls)
    (ev : ObsFn W "KernelInfer::proj_guard" [x_rc, bp, .field i, .field f] h r h' calls)
    (hrc : c.rc h x_rc)
    {nm : KKey} {k : Nat} {T : KExpr} {nP nF : Nat}
    (hload : ∀ (ptr : SourceValue F) (m : Heap F) (cs : List (Call F)),
      ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field 0] h ptr m cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      CIPtrRep c.κ m ptr (.ctorInfo ⟨nm, List.range k, T⟩ nP nF))
    (hf : ZMod.val f < nF)
    {g : KLevel} (hg : RepKLevel h' g r) :
    ∃ (lus : List KLevel) (flags : List Bool),
      g = (List.range (ZMod.val f)).foldl
          (fun acc j => if flags.getD j false then Ix.Kernel.Level.max acc (lus.getD j .zero)
            else acc) (lus.getD (ZMod.val f) .zero) ∧
      (∀ (fvsP : List KExpr) (crest : KExpr) (xFvs : List KExpr) (body : KExpr),
        Ix.Kernel.openPisAtFvars nP T 0 = some (fvsP, crest) →
        Ix.Kernel.openPisAtFvars nF crest nP = some (xFvs, body) →
        ∀ j, j ≤ ZMod.val f → ∃ (x U : KExpr) (u : KLevel), xFvs[j]? = some x ∧
          Infer c.env .full (nP + j) x.fvarTypeD U ∧ Red c.env (nP + j) U (.sort u) ∧
          LvEq u (lus.getD j .zero)) ∧
      (∀ j, j < ZMod.val f → Ix.Kernel.structUsedLater T nP j = true →
        flags.getD j false = true) ∧
      lus.length = ZMod.val f + 1 ∧ flags.length = ZMod.val f := by
  rcases Obs.«KernelInfer::proj_guard».obs ev with
    ⟨m2, p9, cs15, w44, x_cty, w45, w46, w47, x_np, w48, w49, m91, cs101, m122,
      x_after, x_ctx, cs150, m187, ev17, ld11, hm130, ev103, hm195, ev152, hc199⟩
  subst hc199 hm130 hm195
  -- the loaded constructor
  obtain ⟨v, hldv, hci⟩ := hload p9 m2 cs15 ev17 (fun x hx => by simp [hx])
  rw [ld11] at hldv
  injection hldv with hv
  subst hv
  obtain ⟨cv, nP', nF', hci_eq, hval, hnp_eq, -, hnP_lt, -, -⟩ := WhnfAux.ctor_inv hci
  injection hci_eq with hcv hnP hnF
  subst hcv hnP hnF hnp_eq
  let Γ0 : Nat → KExpr := fun _ => .sort .zero
  have hT0 : Tm c.κ 0 Γ0 m2 0 T x_cty := by
    have h1 : Tm c.κ 0 Γ0 m2 0 (posOf (List.range k) T) x_cty := hval.2.2.2 0 Γ0
    rwa [Decl.posOf_range] at h1
  -- the parameter peel
  have e17 := ObsFn.heap_extends ev17
  have e122 := Heap.Extends.snoc m2 (.construct kexprListEnum "Nil" [])
  have hnil_ctx : c.types Γ0 (m2 ++ [.construct kexprListEnum "Nil" []]) 0
      (.ptr (.enum kexprListEnum) m2.length) :=
    ⟨.nil List.getElem?_concat_length, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  have hT122 := Tm.mono e122 hT0
  have hnPv : ZMod.val (nP : F) = nP := ZMod.val_natCast_of_lt (Nat.lt_trans hnP_lt (by decide))
  obtain ⟨m', Γ', E', R', fvs, bs, hm'le, htypesP, hEP, hRP, hopP, hstP, hstop⟩ :=
    peel_open c Γ0 nP (nP : F) hnPv ev103 0 Γ0 T 0 T hnil_ctx hT122 hT122
  rw [Nat.zero_add] at htypesP hEP hRP
  -- the field walk
  have e103 := ObsFn.heap_extends ev103
  have e187 := Heap.Extends.snoc m91
    (.construct Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» "Nil" [])
  have hnil_deps : RepKLevelList
      (m91 ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» "Nil" []]) []
      (.ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>») m91.length) := by
    rw [klevel_node_eq']
    exact .nil List.getElem?_concat_length
  have E187 : Heap.Extends h _ := e17.trans (e122.trans (e103.trans e187))
  have g150 : CoreGood c cs150 := good.sub fun x hx => by simp [hx]
  obtain ⟨⟨xa, ya, za, hldF⟩, lus, flags, hlen1, hlen2, hfold, hpos, hflag⟩ :=
    walk_open c hc Γ0 (ZMod.val f) f rfl g150 ev152 m' Γ' E' m' R' []
      (RCRep.mono E187 hrc) (types_mono e187 htypesP) (Tm.mono e187 hEP) (Tm.mono e187 hRP)
      hnil_deps
  -- the peel passed every parameter: the walk starts at a `Forall` cell
  have hm'eq : nP = m' := by
    by_contra hne
    obtain ⟨vv, hldv', hnf⟩ := hstop (by omega)
    have hl := L1.loadValue_extend e187 hldv'
    rw [hl] at hldF
    injection hldF with hvv
    exact hnf [xa, ya, za] rfl hvv
  subst hm'eq
  have hgEq : g = ([] ++ selDeps lus flags).foldl (fun a b => Ix.Kernel.Level.max a b)
      (lus.getD (ZMod.val f) .zero) := hg.det hfold
  refine ⟨lus, flags, ?_, ?_, ?_, hlen1, hlen2⟩
  · rw [hgEq, List.nil_append]
    have hfr := foldl_range_selDeps flags lus (lus.getD (ZMod.val f) .zero)
    rw [hlen2] at hfr
    exact hfr.symm
  · intro fvsP crest xFvs body hP hF j hj
    have hcr : E' = crest := (Prod.mk.inj (Option.some.inj (hopP.symm.trans hP))).2
    subst hcr
    exact hpos nF xFvs body (by omega) hF j hj
  · intro j hj
    cases hfl : flags.getD j false with
    | true => intro _; rfl
    | false =>
      intro hU
      exfalso
      have hno : Ix.Kernel.structUsedLater T nP j = false := by
        cases hs : T.stripPis (nP + j + 1) with
        | none => simp only [Ix.Kernel.structUsedLater, hs]
        | some p =>
          obtain ⟨bsU, rest⟩ := p
          simp only [Ix.Kernel.structUsedLater, hs]
          rw [show nP + j + 1 = nP + (j + 1) by omega] at hs
          obtain ⟨bU₁, midU, bU₂, hUP, hUmid, -, -⟩ := Decl.stripPis_split nP (j + 1) hs
          have hmid : midU = R' := (Prod.mk.inj (Option.some.inj (hUP.symm.trans hstP))).2
          subst hmid
          rw [Ix.Kernel.Expr.hasLooseBVarB_eq]
          exact hflag j hj hfl bU₂ rest hUmid
      rw [hno] at hU
      exact Bool.false_ne_true hU

end IxVM.Refinement.Core.GuardWalk

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)

/-- **The projection guard at a native block's install, functionally** (module docstring). The
sorts are derived at the constructor stage `⟨.indInfo cvS capsS :: env.consts⟩` (the former
stored over the prefix, at any capability record), whose scoped core facts are the input
`hcore` (`ctorStageCoreFacts_of_block`); `hstored` and `hfreshT` are the step's. The constructor
is the one the environment after the install stores at the block's constructor key `0`. -/
theorem projGuard_fieldSorts {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {n : Nat} {new : List (ConstantInfo .anon)} {B : _root_.Address}
    {cb : Ixon.Constant} {ind : Ixon.Inductive} {caps : IndCaps .anon}
    (hI : BlockInstall ⟨E, env, t, some n⟩ new B cb ind caps) (hpos : 0 < ind.ctors.size)
    (hstored : Decl.UsedRefsStored t env cb)
    (hfreshT : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none)
    {cvS : ConstantVal .anon} {capsS : IndCaps .anon}
    (hcvS : cvS.name = Core.keyOf t (Core.iprjAddr B 0))
    (hcore : Core.ScopedCoreFacts (Decl.ctorStage ⟨E, env, t, some n⟩ cvS capsS))
    {i f : F} {rc bp' rg : SourceValue F} {hg hg' : Heap F} {csg : List (Call F)}
    {g : Core.KLevel} {b : Bytes.Address} {cvC : ConstantVal .anon} {nP nF : Nat}
    (hi : ZMod.val i = 0)
    (hC : (appCtx ⟨E, env, t, some n⟩ new).env.find?
        ((appCtx ⟨E, env, t, some n⟩ new).stored.κ (Core.cprjAddr B 0 0)) =
      some (.ctorInfo cvC nP nF))
    (hf : ZMod.val f < nF)
    (ev : ObsFn Core.W "KernelInfer::proj_guard" [rc, bp', .field i, .field f] hg rg hg' csg)
    (hgood : Core.Good (appCtx ⟨E, env, t, some n⟩ new) csg)
    (hrc : Core.RCRep t (some n) hg rc)
    (hb : Bytes.RepAddressRef Core.addrTy hg b bp') (hbB : Core.ixAddr b = B)
    (hgR : IxVM.Refinement.KernelLevels.RepKLevel hg' g rg) :
    ∃ (lus : List Core.KLevel) (flags : List Bool),
      g = (List.range (ZMod.val f)).foldl
          (fun acc j => if flags.getD j false then Ix.Kernel.Level.max acc (lus.getD j .zero)
            else acc) (lus.getD (ZMod.val f) .zero) ∧
      (∀ (fvsP : List (Ix.Kernel.Expr .anon)) (crest : Ix.Kernel.Expr .anon)
          (xFvs : List (Ix.Kernel.Expr .anon)) (body : Ix.Kernel.Expr .anon),
        Ix.Kernel.openPisAtFvars nP cvC.type 0 = some (fvsP, crest) →
        Ix.Kernel.openPisAtFvars nF crest nP = some (xFvs, body) →
        ∀ j, j ≤ ZMod.val f → ∃ (x T : Ix.Kernel.Expr .anon) (u : Ix.Kernel.Level),
          xFvs[j]? = some x ∧
          Ix.Kernel.Rules.Infer ⟨.indInfo cvS capsS :: env.consts⟩ .full (nP + j)
            x.fvarTypeD T ∧
          Ix.Kernel.Rules.Red ⟨.indInfo cvS capsS :: env.consts⟩ (nP + j) T (.sort u) ∧
          Core.LvEq u (lus.getD j .zero)) ∧
      (∀ j, j < ZMod.val f → Ix.Kernel.structUsedLater cvC.type nP j = true →
        flags.getD j false = true) ∧
      lus.length = ZMod.val f + 1 ∧ flags.length = ZMod.val f := by
  subst hbB
  -- the stored constructor `0`
  obtain ⟨ct, cty, cty', hct0, hcidx0, hread, hlbb, hdef, hcanon, hfind⟩ := hI.ctor 0 hpos
  have hκC := appCtx_key_of_find (c := ⟨E, env, t, some n⟩) (new := new) hfind
  rw [hκC] at hC
  have hCeq := Option.some.inj (hC.symm.trans hfind)
  injection hCeq with hcv hnP hnF
  subst hcv hnP hnF
  -- the constructor stage's keying on the block's cells
  have hfreshS : env.find? cvS.name = none := by
    rw [hcvS]
    exact hfreshT
  have hnt : ∀ T : Core.KKey, cvS.name ≠ Ix.Kernel.projTableName T := by
    intro T
    rw [hcvS]
    exact Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf t _)
  have hused : ∀ i ∈ usedRefIdxs cb, ∀ x, cb.refs.toList[i]? = some x →
      (Decl.ctorStage ⟨E, env, t, some n⟩ cvS capsS).κ x = Core.keyOf t x ∧
        Core.ProjPermitted (Decl.ctorStage ⟨E, env, t, some n⟩ cvS capsS).κ x := by
    intro i hi x hx
    obtain ⟨ci, hci⟩ := hstored i hi x hx
    exact ctorStage_of_find hfreshS hnt hci
  have hrecur : ∀ x ∈ L1.blockRecurAddrs (Core.ixAddr b)
      (#[.indc ind] : Array Ixon.MutConst).toList,
      (Decl.ctorStage ⟨E, env, t, some n⟩ cvS capsS).κ x = Core.keyOf t x := by
    intro x hx
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
    obtain ⟨m, hm, rfl⟩ := LoadedReads.blockRecurAddrs_get hk
    have hk0 : k = 0 := by
      have hlt : k < 1 := (Array.getElem?_eq_some_iff.mp hm).1
      omega
    subst hk0
    have hmm : m = .indc ind := by simpa using hm.symm
    subst hmm
    rw [LoadedReads.memberAddr_indc]
    exact ctorStage_former hcvS
  -- every constructor slot of the record has its position and a reading
  have hctys : ∀ (k : Nat) (ct' : Ixon.Constructor), ind.ctors[k]? = some ct' →
      ct'.cidx.toNat = k ∧ ∃ cty₁ : Ix.Kernel.Expr .anon,
        (exprReader t (fun x => E.blobs.get? x) cb id
          (blockSelf t (Core.ixAddr b) #[.indc ind])).read ct'.typ = .ok cty₁ ∧
        cty₁.looseBVarsBounded 0 = true ∧
        cty₁.allLevelParamsDefined (List.range ct'.lvls.toNat) = true := by
    intro k ct' hk
    have hks : k < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hk).1
    obtain ⟨ct₂, cty₂, -, hct₂, hcidx₂, hty₂, hlbb₂, hdef₂, -, -⟩ := hI.ctor k hks
    have e : ct₂ = ct' := Option.some.inj (hct₂.symm.trans hk)
    subst e
    exact ⟨hcidx₂, cty₂, hty₂, hlbb₂, hdef₂⟩
  have hmem : (#[.indc ind] : Array Ixon.MutConst)[i.val]? = some (.indc ind) := by
    rw [hi]
    rfl
  -- the run's constructor load, at the stage's keying
  have hload : ∀ (ptr : SourceValue F) (m : Heap F) (cs : List (Call F)),
      ObsFn Core.W "Ingress::get_ci_cprj" [bp', .field i, .field 0] hg ptr m cs →
      (∀ cl ∈ cs, cl ∈ csg) →
      Core.CIPtrRep (Decl.ctorStage ⟨E, env, t, some n⟩ cvS capsS).κ m ptr
        (.ctorInfo ⟨(Decl.ctorStage ⟨E, env, t, some n⟩ cvS capsS).κ
            (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) (ZMod.val (0 : F))),
          List.range ct.lvls.toNat, cty'⟩ ct.params.toNat ct.fields.toNat) := by
    intro ptr m cs hev hsub
    have g' := hgood.sub hsub
    obtain ⟨ct₁, cty₁, ty₁, hct₁, hread₁, hcanon₁, hrep⟩ :=
      LoadedReads.get_ci_cprj_load_canon_at hI.check g'.1 g'.2 hb hev hI.block hI.muts hmem
        hctys
    rw [ZMod.val_zero] at hct₁
    have e1 : ct₁ = ct := Option.some.inj (hct₁.symm.trans hct0)
    subst e1
    have e2 : cty₁ = cty := Except.ok.inj (hread₁.symm.trans hread)
    subst e2
    rw [hi, ZMod.val_zero] at hcanon₁
    have e3 : ty₁ = cty' := Option.some.inj (hcanon₁.symm.trans hcanon)
    subst e3
    exact hrep _ hused hrecur
  have good : Core.CoreGood (Decl.ctorStage ⟨E, env, t, some n⟩ cvS capsS) csg :=
    Core.CoreGood.ofRaw ⟨hgood.1, hgood.2⟩ (fun _ _ => trivial)
  exact Core.GuardWalk.proj_guard_open (Decl.ctorStage ⟨E, env, t, some n⟩ cvS capsS) hcore
    good ev hrc hload hf hgR

/-- **The circuit's guard runs at a one-constructor install, in IxC's terms** (`ProjGuardWalkAt`),
with the sorts derived at the constructor stage `⟨.indInfo cvS capsS :: env.consts⟩`, whose
scoped core facts are the input `hcore`. -/
theorem projGuardWalkAt_of_install {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {n : Nat}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {blk : List (ConstantInfo .anon)} {p₀ p : Ix.Kernel.NativeParts .anon}
    {new : List (ConstantInfo .anon)} {ty' : Ix.Kernel.Expr .anon}
    {ctorsA : List (ConstantVal .anon × Nat)} {caps : IndCaps .anon}
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps)
    (hsize : ind.ctors.size = 1)
    (hstored : Decl.UsedRefsStored t env cb)
    (hfreshT : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none)
    {cvS : ConstantVal .anon} {capsS : IndCaps .anon}
    (hcvS : cvS.name = Core.keyOf t (Core.iprjAddr B 0))
    (hcore : Core.ScopedCoreFacts (Decl.ctorStage ⟨E, env, t, some n⟩ cvS capsS)) :
    ∀ cA ∈ ctorsA,
      ProjGuardWalkAt E env t n new B ⟨.indInfo cvS capsS :: env.consts⟩ cA p.nP := by
  intro cA hcA
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hcA
  have hjlt : j < ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
  have hj0 : j = 0 := by
    rw [hO.lenA, hsize] at hjlt
    omega
  subst hj0
  obtain ⟨ct, cty', hct, -, -, hA⟩ := hO.ctors 0 (by omega)
  rw [hA] at hj
  injection hj with hj
  subst hj
  have hfindA := hO.ctorFind _ hcA
  have hκC : (appCtx ⟨E, env, t, some n⟩ new).stored.κ (Core.cprjAddr B 0 0) =
      Core.keyOf t (Core.cprjAddr B 0 0) :=
    appCtx_key_of_find (c := ⟨E, env, t, some n⟩) (new := new) hfindA
  unfold ProjGuardWalkAt
  intro i f rc bp' rg hg hg' csg g b hi hf ev good hrc hb hbB hgr
  have hC : (appCtx ⟨E, env, t, some n⟩ new).env.find?
      ((appCtx ⟨E, env, t, some n⟩ new).stored.κ (Core.cprjAddr B 0 0)) =
      some (.ctorInfo ⟨Core.keyOf t (Core.cprjAddr B 0 0), List.range ct.lvls.toNat, cty'⟩
        p.nP ct.fields.toNat) := by
    rw [hκC]
    exact hfindA
  obtain ⟨lus, flags, h1, h2, h3, -, -⟩ :=
    projGuard_fieldSorts hO.install (by omega) hstored hfreshT hcvS hcore hi hC hf ev good hrc
      hb hbB hgr
  exact ⟨lus, flags, h1, h2, h3⟩

/-! ## The constructor stage's core facts at the install -/

/-- **A checked constant's type is closed, bounded, defined at its level parameters and resolved
in the environment** (`ConstantValRunJ`; the annotation keeps closedness and boundedness). -/
theorem typeShape_of_constantValCheckJ {env : Ix.Kernel.Env .anon} {cv cv' : ConstantVal .anon}
    {lps : List Ix.Kernel.LevelParam}
    (h : Ix.Kernel.Semantics.ConstantValCheckJ Ix.Kernel.Model.rulesJ env cv cv')
    (hlp : cv.levelParams = lps) :
    cv'.type.hasFvar = false ∧ cv'.type.allLevelParamsDefined lps = true ∧
      cv'.type.constsResolve env = true ∧ cv'.type.looseBVarsBounded 0 = true := by
  subst hlp
  obtain ⟨type', ⟨-, -, -, -, hlbb, hfv, hann, hlpd, hcr, -⟩, rfl⟩ := h
  obtain ⟨hfv', hb'⟩ := (Ix.Kernel.Model.judgeFrames_rulesJ env).annot_syntax hann hfv hlbb
  exact ⟨hfv', hlpd, hcr, hb'⟩

/-- **The scoped core facts of the constructor stage of a native block's install**, at the
install's former and capability record (`ctorStageCoreFacts_of_block`): the former's checked type
and its telescope are IxC's former stage's (`SumIndRunJ` in `NativeNoRecFacts`), and the install's
capability record is the stage's (`nativeCaps p = nativeCapsAt p₁ isRec`). -/
theorem ctorStageCoreFacts_of_install {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {n : Nat}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {blk : List (ConstantInfo .anon)} {p₀ p : Ix.Kernel.NativeParts .anon}
    {new : List (ConstantInfo .anon)} {ty' : Ix.Kernel.Expr .anon}
    {ctorsA : List (ConstantVal .anon × Nat)} {caps : IndCaps .anon}
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps)
    (hinv : Decl.PrefixInv E t (some n) env) (hkeys : HashKeyed t env)
    (hstored : Decl.UsedRefsStored t env cb)
    (hfreshT : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none) :
    Core.ScopedCoreFacts (Decl.ctorStage ⟨E, env, t, some n⟩
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ caps) := by
  have hI := hO.install
  obtain ⟨ty₀, ty'', hty, hlbb, hdef, hcanon, hfind⟩ := hI.former
  have hty'' : ty'' = ty' := by
    have h := Option.some.inj (hfind.symm.trans hO.formerFind)
    injection h with hcv hcaps
    injection hcv with h1 h2 h3
    first | exact h3 | skip
  subst hty''
  obtain ⟨-, -, isRec, cvS, cvTa, capsF, p₁, p', ctorsA', sortss, kinds, tfvs, trest, isorts,
    hfam, hInd, -, -, -, hcaps, -, -, -, -, -⟩ := hO.facts
  injection hfam with hp hcvS hcvTa hctorsA
  subst hp hcvS hcvTa
  obtain ⟨cvTa₀, s, bs, cvS', hchk0, hor, hstrip, -, hp1, -⟩ := hInd
  subst hp1
  have htype : ty''.hasFvar = false ∧
      ty''.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧
      ty''.constsResolve env = true ∧ ty''.looseBVarsBounded 0 = true := by
    rcases hor with hEq | ⟨ty₁, hchk1⟩
    · subst hEq
      exact typeShape_of_constantValCheckJ hchk0 hO.cvT₀.2
    · exact typeShape_of_constantValCheckJ hchk1 hO.cvT₀.2
  have hctys : ∀ (k : Nat) (ct' : Ixon.Constructor), ind.ctors[k]? = some ct' →
      ct'.cidx.toNat = k ∧ ∃ cty₁ : Ix.Kernel.Expr .anon,
        (exprReader t (fun x => E.blobs.get? x) cb id
          (blockSelf t B #[.indc ind])).read ct'.typ = .ok cty₁ ∧
        cty₁.looseBVarsBounded 0 = true ∧
        cty₁.allLevelParamsDefined (List.range ct'.lvls.toNat) = true := by
    intro k ct' hk
    have hks : k < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hk).1
    obtain ⟨ct₂, cty₂, -, hct₂, hcidx₂, hty₂, hlbb₂, hdef₂, -, -⟩ := hI.ctor k hks
    have e : ct₂ = ct' := Option.some.inj (hct₂.symm.trans hk)
    subst e
    exact ⟨hcidx₂, cty₂, hty₂, hlbb₂, hdef₂⟩
  have hcapsEq : caps = Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort s) isRec :=
    hO.caps_eq.trans hcaps
  have hunit : ind.indices.toNat = 0 → ind.ctors.size = 1 →
      (∀ ct, ind.ctors[0]? = some ct → ct.fields.toNat = 0) →
      (Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort s) isRec).unitlike = true ∧
        (Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort s) isRec).unitParams =
          ind.params.toNat := by
    rw [← hcapsEq]
    exact hI.unit
  rw [hcapsEq]
  exact ctorStageCoreFacts_of_block (t := t) (E := E) (env := env) (lim := some n)
    (p := p₀.toInductiveShape.withSort s) (isRec := isRec)
    hI.check hinv hI.decoded hI.held hkeys hI.block hI.muts hI.formerRec hI.bounds hty hlbb hdef
    hctys hstored hcanon hfreshT hunit hI.free htype hstrip

/-- **The constructor stage's environment keeps the prefix's lookups** when the stored former's
name is fresh in the prefix. -/
theorem ctorStageEnv_find {env : Ix.Kernel.Env .anon} {cvS : ConstantVal .anon}
    {capsS : IndCaps .anon} (hfresh : env.find? cvS.name = none) :
    ∀ (k : Core.KKey) (ci : ConstantInfo .anon), env.find? k = some ci →
      (⟨.indInfo cvS capsS :: env.consts⟩ : Ix.Kernel.Env .anon).find? k = some ci := by
  intro k ci hf
  rw [Ix.Kernel.Env.find?_cons]
  have hne : ¬ (ConstantInfo.indInfo cvS capsS).name = k := by
    intro h
    have hk : k = cvS.name := h.symm
    rw [hk, hfresh] at hf
    cases hf
  rw [ite_eq_right hne]
  exact hf

/-- **The circuit's guard runs at a one-constructor install, in IxC's terms, from the step's
data**: `projGuardWalkAt_of_install` at the install's constructor stage
(`ctorStageCoreFacts_of_install`). The stage's environment keeps the prefix's lookups
(`ctorStageEnv_find`). -/
theorem projGuardWalkAt_of_step {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {n : Nat}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {blk : List (ConstantInfo .anon)} {p₀ p : Ix.Kernel.NativeParts .anon}
    {new : List (ConstantInfo .anon)} {ty' : Ix.Kernel.Expr .anon}
    {ctorsA : List (ConstantVal .anon × Nat)} {caps : IndCaps .anon}
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps)
    (hsize : ind.ctors.size = 1)
    (hinv : Decl.PrefixInv E t (some n) env) (hkeys : HashKeyed t env)
    (hstored : Decl.UsedRefsStored t env cb)
    (hfreshT : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none) :
    ∀ cA ∈ ctorsA, ProjGuardWalkAt E env t n new B
      ⟨.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ caps ::
        env.consts⟩ cA p.nP :=
  projGuardWalkAt_of_install
    (cvS := ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩) (capsS := caps)
    hO hsize hstored hfreshT rfl (ctorStageCoreFacts_of_install hO hinv hkeys hstored hfreshT)

end IxVM.Refinement.Typing
