import IxVMRefinement.Binding.FamilyReconModel
import IxVMRefinement.Core.LoadedExact
import IxVMRefinement.Core.RomBound
import IxVMRefinement.Subst.Steps
import IxVMRefinement.Obs.KernelCheck

/-! # Open exact terms, builders, and level instantiation for family reconstruction

The reconstruction (`KernelCheck::build_rec_type`, `populate_rules`) builds open terms whose
loose bound variables are local (`TmOExact`: represented at opening depth `0` and some local
depth with exact syntactic universe levels). This module provides:

* `tmExact_depth_le`, `TmOExact`, `TmOExact.ofTmExact`, `TmOExact.ofTmCExact`, `TmOExact.mono`,
  `tmOExact_heapMono₂`, `tmOExactList_mono`;
* `wrap_foralls_spec` (`wrapForalls`), `wrap_lams_spec` (`wrapLams`), `apply_spine_expr_spec`
  (`appSpine`);
* `expr_inst_levels_exact` and `expr_inst_levels_tmOExact` (`exprInstLevels`, exact
  `substLevel` instantiation on `TmExact` / `TmOExact`). -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core (KExpr KLevel KKey bmeta Tm kexprEnum kexprListEnum klevelListEnum
  klevelListEnum_eq addrTy ixAddr Resolved ProjPermitted LvEqList)
open IxVM.Refinement.Decl (TmExact TmCExact)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂ substLevel
  substLevelList)
open IxVM.Refinement.Binding.FamilyFlat (exprInstLevelsWalk exprInstLevels)
open IxVM (F)

set_option linter.unusedVariables false

/-! ## Open exact terms at opening depth `0` -/

/-- The ghost context of a term with no opened variable (at opening depth `0` none is read). -/
abbrev ghost0 : Nat → KExpr := fun _ => .sort .zero

/-- **An exact term represented at a local depth is represented at every larger one** (at opening
depth `0`, where no variable is opened). -/
theorem tmExact_depth_le {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F} {k : Nat}
    {E : KExpr} {p : SourceValue F} (rep : TmExact κ 0 Γ h k E p) :
    ∀ k', k ≤ k' → TmExact κ 0 Γ h k' E p := by
  induction rep with
  | bvarLocal cell hs hi => intro k' hk; exact .bvarLocal cell hs (by omega)
  | bvarFree _ _ _ hd => intro _ _; exact absurd hd (by omega)
  | sort cell rl => intro _ _; exact .sort cell rl
  | const cell ra rls => intro _ _; exact .const cell ra rls
  | app cell _ _ ihf iha => intro k' hk; exact .app cell (ihf k' hk) (iha k' hk)
  | lam cell _ _ rl iht ihb =>
    intro k' hk; exact .lam cell (iht k' hk) (ihb (k' + 1) (by omega)) rl
  | forallE cell _ _ rl iht ihb =>
    intro k' hk; exact .forallE cell (iht k' hk) (ihb (k' + 1) (by omega)) rl
  | letE cell _ _ _ iht ihv ihb =>
    intro k' hk; exact .letE cell (iht k' hk) (ihv k' hk) (ihb (k' + 1) (by omega))
  | litNat cell rl hc => intro _ _; exact .litNat cell rl hc
  | litStr cell rb hs => intro _ _; exact .litStr cell rb hs
  | proj cell ra _ ihe => intro k' hk; exact .proj cell ra (ihe k' hk)

/-- **The heap value `p` represents the open term `E` with exact syntactic universe levels**:
at opening depth `0`, at some local depth (every loose bound variable of `E` is local). -/
def TmOExact (κ : _root_.Address → KKey) (h : Heap F) (E : KExpr) (p : SourceValue F) : Prop :=
  ∃ k, TmExact κ 0 ghost0 h k E p

theorem TmOExact.ofTmExact {κ : _root_.Address → KKey} {h : Heap F} {k : Nat} {E : KExpr}
    {p : SourceValue F} (rep : TmExact κ 0 ghost0 h k E p) : TmOExact κ h E p :=
  ⟨k, rep⟩

theorem TmOExact.ofTmCExact {κ : _root_.Address → KKey} {h : Heap F} {E : KExpr}
    {p : SourceValue F} (rep : TmCExact κ h E p) : TmOExact κ h E p :=
  ⟨0, rep 0 ghost0⟩

theorem TmOExact.mono {κ : _root_.Address → KKey} {h₁ h₂ : Heap F} {E : KExpr}
    {p : SourceValue F} (ext : Heap.Extends h₁ h₂) (rep : TmOExact κ h₁ E p) :
    TmOExact κ h₂ E p :=
  let ⟨k, r⟩ := rep
  ⟨k, r.mono ext⟩

theorem tmOExact_heapMono₂ {κ : _root_.Address → KKey} : HeapMono₂ (TmOExact κ) :=
  fun _ _ _ _ ext rep => rep.mono ext

theorem tmOExactList_mono {κ : _root_.Address → KKey} {h₁ h₂ : Heap F} {xs : List KExpr}
    {p : SourceValue F} (ext : Heap.Extends h₁ h₂)
    (hl : RepList kexprListEnum (TmOExact κ) h₁ xs p) :
    RepList kexprListEnum (TmOExact κ) h₂ xs p :=
  repList_heapMono₂ kexprListEnum tmOExact_heapMono₂ ext hl

/-! ## Building terms -/

section Builders

variable {κ : _root_.Address → KKey}

/-- **`KernelCheck::wrap_foralls(body, doms, dl)`** is `wrapForalls`: the binders `doms`,
outermost first, over `body`, each with the datum of `dl`. -/
theorem wrap_foralls_spec {l : KLevel} {xb xdl : SourceValue F} {B : KExpr} (Ds : List KExpr) :
    ∀ {xds r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn Obs.W "KernelCheck::wrap_foralls" [xb, xds, xdl] h r h' cs →
      TmOExact κ h B xb → RepList kexprListEnum (TmOExact κ) h Ds xds → RepKLevel h l xdl →
      TmOExact κ h' (wrapForalls B Ds l) r := by
  induction Ds with
  | nil =>
    intro xds r h h' cs ev hB hD hl
    rcases Obs.«KernelCheck::wrap_foralls».obs ev with
      ⟨ld, rfl, rfl, -⟩ | ⟨x_dom, x_rest, v, m, cs', ld, -, -, -, -⟩
    · exact hB
    · obtain ⟨z, zs, hzs, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hD ld
      cases hzs
  | cons D Ds ih =>
    intro xds r h h' cs ev hB hD hl
    rcases Obs.«KernelCheck::wrap_foralls».obs ev with
      ⟨ld, -, -, -⟩ | ⟨x_dom, x_rest, v, m, cs', ld, rfl, rfl, ev', -⟩
    · cases IxVM.Refinement.Core.RepList.nil_of_load hD ld
    · obtain ⟨z, zs, hzs, hz, hzs'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hD ld
      injection hzs with hz1 hz2
      subst hz1 hz2
      have ext : Heap.Extends h m := ObsFn.heap_extends ev'
      have ext' : Heap.Extends m
          (m ++ [.construct "KernelTypes::KExprNode" "Forall" [x_dom, v, xdl]]) :=
        Heap.Extends.snoc _ _
      obtain ⟨k₁, r₁⟩ := hz.mono ext
      obtain ⟨k₂, r₂⟩ := ih ev' hB hzs' hl
      exact ⟨max k₁ k₂, .forallE (by simp)
        (tmExact_depth_le (r₁.mono ext') _ (Nat.le_max_left _ _))
        (tmExact_depth_le (r₂.mono ext') _ (by omega)) ((hl.mono ext).mono ext')⟩

/-- **`KernelCheck::wrap_lams(body, doms, dl)`** is `wrapLams`: the λs `doms`, outermost first,
over `body`, each with the datum of `dl`. -/
theorem wrap_lams_spec {l : KLevel} {xb xdl : SourceValue F} {B : KExpr} (Ds : List KExpr) :
    ∀ {xds r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn Obs.W "KernelCheck::wrap_lams" [xb, xds, xdl] h r h' cs →
      TmOExact κ h B xb → RepList kexprListEnum (TmOExact κ) h Ds xds → RepKLevel h l xdl →
      TmOExact κ h' (wrapLams B Ds l) r := by
  induction Ds with
  | nil =>
    intro xds r h h' cs ev hB hD hl
    rcases Obs.«KernelCheck::wrap_lams».obs ev with
      ⟨ld, rfl, rfl, -⟩ | ⟨x_dom, x_rest, v, m, cs', ld, -, -, -, -⟩
    · exact hB
    · obtain ⟨z, zs, hzs, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hD ld
      cases hzs
  | cons D Ds ih =>
    intro xds r h h' cs ev hB hD hl
    rcases Obs.«KernelCheck::wrap_lams».obs ev with
      ⟨ld, -, -, -⟩ | ⟨x_dom, x_rest, v, m, cs', ld, rfl, rfl, ev', -⟩
    · cases IxVM.Refinement.Core.RepList.nil_of_load hD ld
    · obtain ⟨z, zs, hzs, hz, hzs'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hD ld
      injection hzs with hz1 hz2
      subst hz1 hz2
      have ext : Heap.Extends h m := ObsFn.heap_extends ev'
      have ext' : Heap.Extends m
          (m ++ [.construct "KernelTypes::KExprNode" "Lam" [x_dom, v, xdl]]) :=
        Heap.Extends.snoc _ _
      obtain ⟨k₁, r₁⟩ := hz.mono ext
      obtain ⟨k₂, r₂⟩ := ih ev' hB hzs' hl
      exact ⟨max k₁ k₂, .lam (by simp)
        (tmExact_depth_le (r₁.mono ext') _ (Nat.le_max_left _ _))
        (tmExact_depth_le (r₂.mono ext') _ (by omega)) ((hl.mono ext).mono ext')⟩

/-- **`KernelCheck::apply_spine_expr(head, args)`** is `appSpine`: the head applied to the
arguments in order. -/
theorem apply_spine_expr_spec (As : List KExpr) :
    ∀ {xh xas r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {H : KExpr},
      ObsFn Obs.W "KernelCheck::apply_spine_expr" [xh, xas] h r h' cs →
      TmOExact κ h H xh → RepList kexprListEnum (TmOExact κ) h As xas →
      TmOExact κ h' (appSpine H As) r := by
  induction As with
  | nil =>
    intro xh xas r h h' cs H ev hH hA
    rcases Obs.«KernelCheck::apply_spine_expr».obs ev with
      ⟨ld, rfl, rfl, -⟩ | ⟨x_a, x_rest, cs', m, ld, -, -, -⟩
    · exact hH
    · obtain ⟨z, zs, hzs, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hA ld
      cases hzs
  | cons A As ih =>
    intro xh xas r h h' cs H ev hH hA
    rcases Obs.«KernelCheck::apply_spine_expr».obs ev with
      ⟨ld, -, -, -⟩ | ⟨x_a, x_rest, cs', m, ld, rfl, ev', -⟩
    · cases IxVM.Refinement.Core.RepList.nil_of_load hA ld
    · obtain ⟨z, zs, hzs, hz, hzs'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hA ld
      injection hzs with hz1 hz2
      subst hz1 hz2
      have ext : Heap.Extends h (h ++ [.construct "KernelTypes::KExprNode" "App" [xh, x_a]]) :=
        Heap.Extends.snoc _ _
      obtain ⟨k₁, r₁⟩ := hH
      obtain ⟨k₂, r₂⟩ := hz
      have happ : TmOExact κ (h ++ [.construct "KernelTypes::KExprNode" "App" [xh, x_a]])
          (.app H A) (.ptr (.enum "KernelTypes::KExprNode") h.length) :=
        ⟨max k₁ k₂, .app (by simp)
          (tmExact_depth_le (r₁.mono ext) _ (Nat.le_max_left _ _))
          (tmExact_depth_le (r₂.mono ext) _ (Nat.le_max_right _ _))⟩
      exact ih ev' happ (tmOExactList_mono ext hzs')

end Builders

/-! ## Exact level instantiation (`KernelLevels::expr_inst_levels`) -/

private theorem exprInstLevelsWalk_liftLooseBVars (us : List KLevel) :
    ∀ (e : KExpr) (n c : Nat),
      exprInstLevelsWalk us (e.liftLooseBVars n c) =
        (exprInstLevelsWalk us e).liftLooseBVars n c
  | .bvar i, n, c => by simp only [Ix.Kernel.Expr.liftLooseBVars, exprInstLevelsWalk]; split <;> rfl
  | .fvar _ _, _, _ => rfl
  | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, n, c => by
    simp only [Ix.Kernel.Expr.liftLooseBVars, exprInstLevelsWalk,
      exprInstLevelsWalk_liftLooseBVars us f n c, exprInstLevelsWalk_liftLooseBVars us a n c]
  | .lam t b _, n, c => by
    simp only [Ix.Kernel.Expr.liftLooseBVars, exprInstLevelsWalk,
      exprInstLevelsWalk_liftLooseBVars us t n c, exprInstLevelsWalk_liftLooseBVars us b n (c + 1)]
  | .forallE t b _, n, c => by
    simp only [Ix.Kernel.Expr.liftLooseBVars, exprInstLevelsWalk,
      exprInstLevelsWalk_liftLooseBVars us t n c, exprInstLevelsWalk_liftLooseBVars us b n (c + 1)]
  | .letE t v b _, n, c => by
    simp only [Ix.Kernel.Expr.liftLooseBVars, exprInstLevelsWalk,
      exprInstLevelsWalk_liftLooseBVars us t n c, exprInstLevelsWalk_liftLooseBVars us v n c,
      exprInstLevelsWalk_liftLooseBVars us b n (c + 1)]
  | .proj _ _ e, n, c => by
    simp only [Ix.Kernel.Expr.liftLooseBVars, exprInstLevelsWalk,
      exprInstLevelsWalk_liftLooseBVars us e n c]

private theorem exprInstLevelsWalk_instantiate1Lift (us : List KLevel) (v : KExpr) :
    ∀ (b : KExpr) (j : Nat),
      exprInstLevelsWalk us (b.instantiate1Lift v j) =
        (exprInstLevelsWalk us b).instantiate1Lift (exprInstLevelsWalk us v) j
  | .bvar i, j => by
    simp only [Ix.Kernel.Expr.instantiate1Lift, exprInstLevelsWalk]
    split
    · exact exprInstLevelsWalk_liftLooseBVars us v j 0
    · split <;> rfl
  | .fvar _ ty, j => by
    simp only [Ix.Kernel.Expr.instantiate1Lift, exprInstLevelsWalk]
  | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, j => by
    simp only [Ix.Kernel.Expr.instantiate1Lift, exprInstLevelsWalk,
      exprInstLevelsWalk_instantiate1Lift us v f j, exprInstLevelsWalk_instantiate1Lift us v a j]
  | .lam t b _, j => by
    simp only [Ix.Kernel.Expr.instantiate1Lift, exprInstLevelsWalk,
      exprInstLevelsWalk_instantiate1Lift us v t j,
      exprInstLevelsWalk_instantiate1Lift us v b (j + 1)]
  | .forallE t b _, j => by
    simp only [Ix.Kernel.Expr.instantiate1Lift, exprInstLevelsWalk,
      exprInstLevelsWalk_instantiate1Lift us v t j,
      exprInstLevelsWalk_instantiate1Lift us v b (j + 1)]
  | .letE t w b _, j => by
    simp only [Ix.Kernel.Expr.instantiate1Lift, exprInstLevelsWalk,
      exprInstLevelsWalk_instantiate1Lift us v t j,
      exprInstLevelsWalk_instantiate1Lift us v w j,
      exprInstLevelsWalk_instantiate1Lift us v b (j + 1)]
  | .proj _ _ e, j => by
    simp only [Ix.Kernel.Expr.instantiate1Lift, exprInstLevelsWalk,
      exprInstLevelsWalk_instantiate1Lift us v e j]

private theorem exprInstLevels_of_ne_nil {us : List KLevel} (hne : us ≠ []) (e : KExpr) :
    exprInstLevels us e = exprInstLevelsWalk us e := by
  cases us with
  | nil => exact absurd rfl hne
  | cons _ _ => rfl

private theorem expr_inst_levels_exact_aux (κ : _root_.Address → KKey) :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn Obs.W fname args h r h' cs → IxVM.Consistency.Bounded cs →
      ((fname = "KernelLevels::expr_inst_levels" →
        ∀ (pe pus : SourceValue F) (Γ : Nat → KExpr) (k : Nat) (E : KExpr) (us : List KLevel),
          args = [pe, pus] → TmExact κ 0 Γ h k E pe → RepKLevelList h us pus →
          TmExact κ 0 Γ h' k (exprInstLevels us E) r) ∧
       (fname = "KernelLevels::expr_inst_levels_walk" →
        ∀ (pe pus : SourceValue F) (Γ : Nat → KExpr) (k : Nat) (E : KExpr) (us : List KLevel),
          args = [pe, pus] → us ≠ [] → TmExact κ 0 Γ h k E pe → RepKLevelList h us pus →
          TmExact κ 0 Γ h' k (exprInstLevelsWalk us E) r)) :=
  ObsFn.strong_induction (world := Obs.W)
    (fun fname args h r h' cs => IxVM.Consistency.Bounded cs →
      ((fname = "KernelLevels::expr_inst_levels" →
        ∀ (pe pus : SourceValue F) (Γ : Nat → KExpr) (k : Nat) (E : KExpr) (us : List KLevel),
          args = [pe, pus] → TmExact κ 0 Γ h k E pe → RepKLevelList h us pus →
          TmExact κ 0 Γ h' k (exprInstLevels us E) r) ∧
       (fname = "KernelLevels::expr_inst_levels_walk" →
        ∀ (pe pus : SourceValue F) (Γ : Nat → KExpr) (k : Nat) (E : KExpr) (us : List KLevel),
          args = [pe, pus] → us ≠ [] → TmExact κ 0 Γ h k E pe → RepKLevelList h us pus →
          TmExact κ 0 Γ h' k (exprInstLevelsWalk us E) r)))
    (fun fname args h r h' cs ev ih bd => by
      have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
        fun hs => RomBound.bounded_mono bd hs
      refine ⟨fun hfn pe pus Γ k E us hargs hE hus => ?_,
        fun hfn pe pus Γ k E us hargs hne hE hus => ?_⟩
      · subst hfn hargs
        match Obs.«KernelLevels::expr_inst_levels».obs ev with
        | .Nil (ld12 := ld) (he21 := hr) (he22 := he) .. =>
          subst hr he
          have hus' : RepList klevelListEnum RepKLevel _ us pus := by rwa [klevelListEnum_eq]
          obtain rfl := IxVM.Refinement.Core.RepList.nil_of_load hus' ld
          exact hE
        | .other (ld12 := ld) (hne24 := hne24) (ev33 := e1) (hc50 := hc) .. =>
          subst hc
          have hne : us ≠ [] := by
            rintro rfl
            have hus' : RepList klevelListEnum RepKLevel _ [] pus := by rwa [klevelListEnum_eq]
            cases hus' with
            | nil cell =>
              rw [Lib.load_enum_cell cell] at ld
              injection ld with hv
              exact hne24 [] rfl hv.symm
          rw [exprInstLevels_of_ne_nil hne]
          exact (ih _ _ _ _ _ _ (by simp) e1 (sub fun c hc' => by simp [hc'])).2
            rfl pe pus Γ k E us rfl hne hE hus
      · subst hfn hargs
        match Obs.«KernelLevels::expr_inst_levels_walk».obs ev with
        | .BVar (ld12 := ld) (he29 := hr) (hm28 := hm) .. =>
          subst hr hm
          obtain ⟨i, rfl, hsm, hcase⟩ := hE.bvar_of_load ld
          rcases hcase with ⟨hlt, rfl⟩ | ⟨_, hd, _⟩
          · exact .bvarLocal (by simp) hsm hlt
          · omega
        | .Srt (ld12 := ld) (ev74 := e1) (he58 := hr) (hm57 := hm) (hc91 := hc) .. =>
          subst hc hr hm
          obtain ⟨l, rfl, rl⟩ := hE.sort_of_load ld
          obtain ⟨-, rl', -⟩ :=
            IxVM.Refinement.Levels.levelInstParams_obs e1 (sub fun c hc' => by simp [hc']) rl hus
          exact .sort (by simp) (rl'.mono (Heap.Extends.snoc _ _))
        | .Const (ld12 := ld) (ev137 := e1) (he113 := hr) (hm112 := hm) (hc154 := hc) .. =>
          subst hc hr hm
          obtain ⟨a, ls, rfl, ra, rls⟩ := hE.const_of_load ld
          have : Resolved _ := ⟨hE.toTm.const_key_ne⟩
          obtain ⟨-, rls', ext⟩ :=
            IxVM.Refinement.Levels.levelListInst_obs e1 (sub fun c hc' => by simp [hc']) rls hus
          have ext' : Heap.Extends _ _ := Heap.Extends.snoc _ _
          exact .const (by simp) (Bytes.repAddressRef_heapMono₂ addrTy (ext.trans ext') ra)
            (rls'.mono ext')
        | .App (ld12 := ld) (he176 := hr) (hm175 := hm) (ev193 := e1) (ev221 := e2)
            (hc238 := hc) .. =>
          subst hc hr hm
          obtain ⟨Ef, Ea, rfl, hf, ha⟩ := hE.app_of_load ld
          have sf := (ih _ _ _ _ _ _ (by simp) e1
            (sub fun c hc' => by simp [hc'])).1 rfl _ _ Γ k Ef us rfl hf hus
          have sa := (ih _ _ _ _ _ _ (by simp; omega) e2
            (sub fun c hc' => by simp [hc'])).1 rfl _ _ Γ k Ea us rfl
            (ha.mono e1.heap_extends) (hus.mono e1.heap_extends)
          rw [exprInstLevels_of_ne_nil hne] at sf sa
          have ext' : Heap.Extends _ _ := Heap.Extends.snoc _ _
          exact .app (by simp) ((sf.mono e2.heap_extends).mono ext') (sa.mono ext')
        | .Lam (ld12 := ld) (he265 := hr) (hm264 := hm) (ev283 := e1) (ev311 := e2)
            (ev339 := e3) (hc356 := hc) .. =>
          subst hc hr hm
          obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := hE.lam_of_load ld
          have st := (ih _ _ _ _ _ _ (by simp) e1
            (sub fun c hc' => by simp [hc'])).1 rfl _ _ Γ k T us rfl ht hus
          have sb := (ih _ _ _ _ _ _ (by simp; omega) e2
            (sub fun c hc' => by simp [hc'])).1 rfl _ _ Γ (k + 1) B us rfl
            (hb.mono e1.heap_extends) (hus.mono e1.heap_extends)
          rw [exprInstLevels_of_ne_nil hne] at st sb
          have ext12 := e1.heap_extends.trans e2.heap_extends
          obtain ⟨-, rl', -⟩ := IxVM.Refinement.Levels.levelInstParams_obs e3
            (sub fun c hc' => by simp [hc']) (hl.mono ext12) (hus.mono ext12)
          have ext' : Heap.Extends _ _ := Heap.Extends.snoc _ _
          show TmExact κ 0 Γ _ k (.lam (exprInstLevelsWalk us T) (exprInstLevelsWalk us B)
            { bmeta ℓ with pw := Ix.Kernel.Level.substPW (List.range us.length) us (bmeta ℓ).pw }) _
          rw [IxVM.Refinement.Core.SubstAux.bmeta_subst (LvEqList.refl us)]
          exact .lam (by simp)
            ((st.mono (e2.heap_extends.trans e3.heap_extends)).mono ext')
            ((sb.mono e3.heap_extends).mono ext') (rl'.mono ext')
        | .Forall (ld12 := ld) (he383 := hr) (hm382 := hm) (ev401 := e1) (ev429 := e2)
            (ev457 := e3) (hc474 := hc) .. =>
          subst hc hr hm
          obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := hE.forallE_of_load ld
          have st := (ih _ _ _ _ _ _ (by simp) e1
            (sub fun c hc' => by simp [hc'])).1 rfl _ _ Γ k T us rfl ht hus
          have sb := (ih _ _ _ _ _ _ (by simp; omega) e2
            (sub fun c hc' => by simp [hc'])).1 rfl _ _ Γ (k + 1) B us rfl
            (hb.mono e1.heap_extends) (hus.mono e1.heap_extends)
          rw [exprInstLevels_of_ne_nil hne] at st sb
          have ext12 := e1.heap_extends.trans e2.heap_extends
          obtain ⟨-, rl', -⟩ := IxVM.Refinement.Levels.levelInstParams_obs e3
            (sub fun c hc' => by simp [hc']) (hl.mono ext12) (hus.mono ext12)
          have ext' : Heap.Extends _ _ := Heap.Extends.snoc _ _
          show TmExact κ 0 Γ _ k (.forallE (exprInstLevelsWalk us T) (exprInstLevelsWalk us B)
            { bmeta ℓ with pw := Ix.Kernel.Level.substPW (List.range us.length) us (bmeta ℓ).pw }) _
          rw [IxVM.Refinement.Core.SubstAux.bmeta_subst (LvEqList.refl us)]
          exact .forallE (by simp)
            ((st.mono (e2.heap_extends.trans e3.heap_extends)).mono ext')
            ((sb.mono e3.heap_extends).mono ext') (rl'.mono ext')
        | .Let (ld12 := ld) (he501 := hr) (hm500 := hm) (ev519 := e1) (ev547 := e2)
            (ev575 := e3) (hc592 := hc) .. =>
          subst hc hr hm
          obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := hE.letE_of_load ld
          have st := (ih _ _ _ _ _ _ (by simp) e1
            (sub fun c hc' => by simp [hc'])).1 rfl _ _ Γ k T us rfl ht hus
          have sv := (ih _ _ _ _ _ _ (by simp; omega) e2
            (sub fun c hc' => by simp [hc'])).1 rfl _ _ Γ k V us rfl
            (hv.mono e1.heap_extends) (hus.mono e1.heap_extends)
          have ext12 := e1.heap_extends.trans e2.heap_extends
          have sb := (ih _ _ _ _ _ _ (by simp; omega) e3
            (sub fun c hc' => by simp [hc'])).1 rfl _ _ Γ (k + 1) B us rfl
            (hb.mono ext12) (hus.mono ext12)
          rw [exprInstLevels_of_ne_nil hne] at st sv sb
          have ext' : Heap.Extends _ _ := Heap.Extends.snoc _ _
          rw [show exprInstLevelsWalk us (IxVM.Refinement.Core.instShift V 0 B) =
              IxVM.Refinement.Core.instShift (exprInstLevelsWalk us V) 0
                (exprInstLevelsWalk us B) from exprInstLevelsWalk_instantiate1Lift us V B 0]
          exact .letE (by simp)
            (((st.mono e2.heap_extends).mono e3.heap_extends).mono ext')
            ((sv.mono e3.heap_extends).mono ext') (sb.mono ext')
        | .Lit (ld12 := ld) (he609 := hr) (hm608 := hm) .. =>
          subst hr hm
          have ext' : Heap.Extends _ _ := Heap.Extends.snoc _ _
          rcases hE.toTm.lit_of_load ld with ⟨_, limbs, rfl, rl, hc, rfl⟩ |
            ⟨_, bs, s, rfl, rb, hs, rfl⟩
          · exact .litNat (by simp) (repList_heapMono₂ _ repU64_heapMono₂ ext' rl) hc
          · exact .litStr (by simp) (Bytes.repByteStream_heapMono₂ _ ext' rb) hs
        | .Proj (ld12 := ld) (he648 := hr) (hm647 := hm) (ev680 := e1) (hc697 := hc) .. =>
          subst hc hr hm
          obtain ⟨a, i, Es, rfl, rfl, ra, hes⟩ := hE.proj_of_load ld
          have : Resolved _ := ⟨hE.toTm.proj_key_ne⟩
          have : ProjPermitted _ _ := hE.toTm.proj_permitted ld ra
          have se := (ih _ _ _ _ _ _ (by simp) e1
            (sub fun c hc' => by simp [hc'])).1 rfl _ _ Γ k Es us rfl hes hus
          rw [exprInstLevels_of_ne_nil hne] at se
          have ext' : Heap.Extends _ _ := Heap.Extends.snoc _ _
          exact .proj (by simp)
            (Bytes.repAddressRef_heapMono₂ addrTy (e1.heap_extends.trans ext') ra) (se.mono ext'))

/-- **`KernelLevels::expr_inst_levels(e, us)`** on an exact term at opening depth `0` produces
`exprInstLevels us E` with exact syntactic universe levels. -/
theorem expr_inst_levels_exact {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {k : Nat}
    {E : KExpr} {us : List KLevel} {pe pus r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (bd : IxVM.Consistency.Bounded cs)
    (hE : TmExact κ 0 Γ h k E pe) (hus : RepKLevelList h us pus)
    (ev : ObsFn Obs.W "KernelLevels::expr_inst_levels" [pe, pus] h r h' cs) :
    TmExact κ 0 Γ h' k (exprInstLevels us E) r :=
  (expr_inst_levels_exact_aux κ _ _ _ _ _ _ ev bd).1 rfl pe pus Γ k E us rfl hE hus

/-- **`KernelLevels::expr_inst_levels(e, us)`** on `TmOExact` produces `exprInstLevels us E`. -/
theorem expr_inst_levels_tmOExact {κ : _root_.Address → KKey} {E : KExpr} {us : List KLevel}
    {pe pus r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (bd : IxVM.Consistency.Bounded cs) (hE : TmOExact κ h E pe) (hus : RepKLevelList h us pus)
    (ev : ObsFn Obs.W "KernelLevels::expr_inst_levels" [pe, pus] h r h' cs) :
    TmOExact κ h' (exprInstLevels us E) r :=
  let ⟨k, rE⟩ := hE
  ⟨k, expr_inst_levels_exact bd rE hus ev⟩

end IxVM.Refinement.Binding.FamilyRecon
