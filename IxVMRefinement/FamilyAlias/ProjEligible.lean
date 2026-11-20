import IxVMRefinement.Obs.KernelModeled9
import IxVMRefinement.Obs.KernelWhnf
import IxVMRefinement.Obs.KernelCheck
import IxVMRefinement.Assembly.GuardRawInst
import IxVMRefinement.L1.CanonicalRawAnnotation
import IxVMRefinement.L1.HashedBlock
import IxVMRefinement.StatementRel.LoadedReadsCanonInd
import IxVMRefinement.StatementRel.LoadedReadsCanonCtor
import IxVMRefinement.Binding.FamilyReconWhnf
import IxVMRefinement.Callees.RouteScan
import IxVMRefinement.Decl.ModeledTele
import IxVMRefinement.Lib.Words
import IxVMRefinement.Lib.Lists

/-! # Refinement and determinism of `KernelModeled::modeled_proj_eligible`

Proves two foundational facts for certified `.proj` on modeled inductive blocks:

1. **`modeled_proj_eligible_one_facts`**: whenever `KernelModeled::modeled_proj_eligible(block, i)`
   returns `1` on a block `B` with `BlockCanonReadings`, member `i` is a 1-constructor, 0-index
   inductive with at least 1 field, matching constructor universe/parameter counts, and a syntactic
   never-zero result sort.
2. **`modeled_proj_eligible_det`**: any two bounded, collision-free runs of
   `KernelModeled::modeled_proj_eligible(block, i)` on the same block `B` and member index `i`
   (even across different stores `E₁`, `E₂` sharing `BlockCanonReadings`) return the exact same
   bit (`0` or `1`).

Both results run directly over `Decl.RawExprRep` (retaining raw `Let` cells and exact universe
syntax), avoiding any conflation between a raw `Let` node and its ζ-reduced body. -/

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core (W KExpr KLevel KKey kexprEnum addrTy addrListEnum ixAddr)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList substLevel)
open IxVM.Consistency
open IxVM (F)
open IxVM.Refinement.Binding.FamilyRecon (field_natCast_eq_zero field_natCast_ne_zero
  evalBinOp_sub_succ)

set_option maxHeartbeats 2400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Open raw exact terms (`RawOExact`) -/

/-- The heap value `p` represents the raw open term `R` (retaining `Let` nodes and exact universe
levels) at some local de Bruijn bound. -/
def RawOExact (κ : _root_.Address → KKey) (h : Heap F) (R : KExpr) (p : SourceValue F) : Prop :=
  ∃ k, Decl.RawExprRep κ h k R p

private theorem RawOExact.mono {κ : _root_.Address → KKey} {h₁ h₂ : Heap F} {R : KExpr}
    {p : SourceValue F} (ext : Heap.Extends h₁ h₂) (hR : RawOExact κ h₁ R p) :
    RawOExact κ h₂ R p :=
  let ⟨k, r⟩ := hR
  ⟨k, r.mono ext⟩

private theorem RawOExact.forallE_of_load {κ : _root_.Address → KKey} {h : Heap F} {R : KExpr}
    {p tp bp lp : SourceValue F} (hR : RawOExact κ h R p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Forall" [tp, bp, lp])) :
    ∃ RT RB ℓ, R = .forallE RT RB (Core.bmeta ℓ) ∧ RawOExact κ h RT tp ∧ RawOExact κ h RB bp ∧
      RepKLevel h ℓ lp := by
  obtain ⟨k, E, rep⟩ := hR
  obtain ⟨RT, RB, T, B, ℓ, hReq, -, hRT, hRB, hℓ⟩ := rep.raw_forallE_view ld
  exact ⟨RT, RB, ℓ, hReq, ⟨k, T, hRT⟩, ⟨k + 1, B, hRB⟩, hℓ⟩

private theorem RawOExact.lam_of_load {κ : _root_.Address → KKey} {h : Heap F} {R : KExpr}
    {p tp bp lp : SourceValue F} (hR : RawOExact κ h R p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Lam" [tp, bp, lp])) :
    ∃ RT RB ℓ, R = .lam RT RB (Core.bmeta ℓ) ∧ RawOExact κ h RT tp ∧ RawOExact κ h RB bp ∧
      RepKLevel h ℓ lp := by
  obtain ⟨k, E, rep⟩ := hR
  obtain ⟨RT, RB, T, B, ℓ, hReq, -, hRT, hRB, hℓ⟩ := rep.raw_lam_view ld
  exact ⟨RT, RB, ℓ, hReq, ⟨k, T, hRT⟩, ⟨k + 1, B, hRB⟩, hℓ⟩

private theorem RawOExact.letE_of_load {κ : _root_.Address → KKey} {h : Heap F} {R : KExpr}
    {p xt xv xb : SourceValue F} (hR : RawOExact κ h R p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Let" [xt, xv, xb])) :
    ∃ RT RV RB, R = .letE RT RV RB default ∧ RawOExact κ h RT xt ∧ RawOExact κ h RV xv ∧
      RawOExact κ h RB xb := by
  obtain ⟨k, E, rep⟩ := hR
  obtain ⟨RT, RV, RB, T, V, B, hReq, -, hRT, hRV, hRB⟩ := rep.raw_let_view ld
  exact ⟨RT, RV, RB, hReq, ⟨k, T, hRT⟩, ⟨k, V, hRV⟩, ⟨k + 1, B, hRB⟩⟩

private theorem RawOExact.app_of_load {κ : _root_.Address → KKey} {h : Heap F} {R : KExpr}
    {p fp ap : SourceValue F} (hR : RawOExact κ h R p)
    (ld : loadValue h p = .ok (.construct kexprEnum "App" [fp, ap])) :
    ∃ Rf Ra, R = .app Rf Ra ∧ RawOExact κ h Rf fp ∧ RawOExact κ h Ra ap := by
  obtain ⟨k, E, rep⟩ := hR
  obtain ⟨Rf, Ra, Ef, Ea, hReq, -, hRf, hRa⟩ := rep.raw_app_view ld
  exact ⟨Rf, Ra, hReq, ⟨k, Ef, hRf⟩, ⟨k, Ea, hRa⟩⟩

private theorem RawOExact.const_of_load {κ : _root_.Address → KKey} {h : Heap F} {R : KExpr}
    {p ap lsp : SourceValue F} (hR : RawOExact κ h R p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Const" [ap, lsp])) :
    ∃ a ls, R = .const (κ (ixAddr a)) ls ∧ Bytes.RepAddressRef addrTy h a ap ∧
      RepKLevelList h ls lsp := by
  obtain ⟨k, E, rep⟩ := hR
  obtain ⟨a, ls, hReq, -, ha, hls⟩ := rep.raw_const_view ld
  exact ⟨a, ls, hReq, ha, hls⟩

private theorem RawOExact.sort_of_load {κ : _root_.Address → KKey} {h : Heap F} {R : KExpr}
    {p lp : SourceValue F} (hR : RawOExact κ h R p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Srt" [lp])) :
    ∃ u, R = .sort u ∧ RepKLevel h u lp := by
  obtain ⟨k, E, rep⟩ := hR
  obtain ⟨u, hReq, -, hu⟩ := rep.raw_sort_view ld
  exact ⟨u, hReq, hu⟩

private theorem RawOExact.proj_of_load {κ : _root_.Address → KKey} {h : Heap F} {R : KExpr}
    {p ap xi xe : SourceValue F} (hR : RawOExact κ h R p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Proj" [ap, xi, xe])) :
    ∃ (a : Bytes.Address) (idx : F) (RI : KExpr),
      R = .proj (κ (ixAddr a)) idx.val RI ∧ xi = .field idx ∧
      Bytes.RepAddressRef addrTy h a ap ∧ RawOExact κ h RI xe := by
  obtain ⟨k, E, rep⟩ := hR
  obtain ⟨a, idx, RI, I, hReq, -, hxi, ha, hRI⟩ := rep.raw_proj_view ld
  exact ⟨a, idx, RI, hReq, hxi, ha, ⟨k, I, hRI⟩⟩

private theorem RawOExact.inst1 {κ : _root_.Address → KKey} {h h' : Heap F}
    {B V : KExpr} {pb pv r : SourceValue F} {cs : List (Call F)}
    (hbd : Bounded cs) (hB : RawOExact κ h B pb) (hV : RawOExact κ h V pv)
    (ev : ObsFn W "KernelSubst::expr_inst1" [pb, pv, .field 0] h r h' cs) :
    RawOExact κ h' (B.instantiate1Lift V 0) r := by
  obtain ⟨kb, rb⟩ := hB
  obtain ⟨kv, rv⟩ := hV
  let n := max kb kv
  have rb' : Decl.RawExprRep κ h (n + ZMod.val (0 : F) + 1) B pb :=
    rb.weaken (by rw [ZMod.val_zero]; omega)
  have rv' : Decl.RawExprRep κ h n V pv := rv.weaken (by omega)
  have hr := Decl.RawExprRep.inst1 rb' rv' hbd ev
  rw [ZMod.val_zero] at hr
  exact ⟨n + 0 + 1, hr⟩

/-! ## `KernelWhnf::type_sort_never` (syntactic, no `let`) -/

/-- Pure syntactic mirror of `KernelWhnf::type_sort_never`: `n` leading `∀` binders ending in a
sort whose instantiation at `us` is never zero. -/
def typeSortNeverNoLet : KExpr → Nat → List KLevel → Bool
  | .forallE _ b _, n + 1, us => typeSortNeverNoLet b n us
  | .sort l, 0, us => (substLevel l us).isNeverZero
  | _, _, _ => false

theorem typeSortNeverNoLet_eq_true_iff :
    ∀ (E : KExpr) (n : Nat) (us : List KLevel),
      typeSortNeverNoLet E n us = true ↔
        ∃ bs l, E.stripPis n = some (bs, .sort l) ∧ (substLevel l us).isNeverZero = true
  | .forallE d b m, n + 1, us => by
    simp only [typeSortNeverNoLet, Ix.Kernel.Expr.stripPis]
    rw [typeSortNeverNoLet_eq_true_iff b n us]
    constructor
    · rintro ⟨bs, l, hs, hnz⟩
      exact ⟨(d, m) :: bs, l, by rw [hs]; rfl, hnz⟩
    · rintro ⟨bs, l, hs, hnz⟩
      cases h : b.stripPis n with
      | none => rw [h] at hs; simp at hs
      | some p =>
        rw [h] at hs
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        exact ⟨p.1, l, congrArg some (Prod.ext rfl hs.2), hnz⟩
  | .sort l, 0, us => by
    simp [typeSortNeverNoLet, Ix.Kernel.Expr.stripPis]
  | .forallE _ _ _, 0, _ => by simp [typeSortNeverNoLet, Ix.Kernel.Expr.stripPis]
  | .sort _, _ + 1, _ => by simp [typeSortNeverNoLet, Ix.Kernel.Expr.stripPis]
  | .bvar _, 0, _ | .bvar _, _ + 1, _
  | .fvar _ _, 0, _ | .fvar _ _, _ + 1, _
  | .const _ _, 0, _ | .const _ _, _ + 1, _
  | .app _ _, 0, _ | .app _ _, _ + 1, _
  | .lam _ _ _, 0, _ | .lam _ _ _, _ + 1, _
  | .letE _ _ _ _, 0, _ | .letE _ _ _ _, _ + 1, _
  | .lit _, 0, _ | .lit _, _ + 1, _
  | .proj _ _ _, 0, _ | .proj _ _ _, _ + 1, _ => by
    simp [typeSortNeverNoLet, Ix.Kernel.Expr.stripPis]

private theorem typeSortNeverNoLet_not_forall_not_sort {κ : _root_.Address → KKey} {h : Heap F}
    {R : KExpr} {p v : SourceValue F} (hR : RawOExact κ h R p) (ld : loadValue h p = .ok v)
    (hf : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Forall" vs)
    (hs : ∀ vs : List (SourceValue F), vs.length = 1 → v ≠ .construct kexprEnum "Srt" vs)
    (n : Nat) (us : List KLevel) : typeSortNeverNoLet R n us = false := by
  obtain ⟨k, E, rep⟩ := hR
  cases rep with
  | forallE cell _ _ _ =>
    have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv
    exact (hf _ rfl hv).elim
  | sort cell _ =>
    have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv
    exact (hs _ rfl hv).elim
  | bvarFree _ _ _ hd => omega
  | _ => cases n <;> simp [typeSortNeverNoLet]

/-- **`KernelWhnf::type_sort_never`** decides `typeSortNeverNoLet R n us` bidirectionally on
`RawOExact`. -/
theorem type_sort_never_rawOExact {κ : _root_.Address → KKey} {R : KExpr} {n : Nat}
    {us : List KLevel} {xty xlvls r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hn : n < 18446744069414584321) (hR : RawOExact κ h R xty) (hus : RepKLevelList h us xlvls)
    (hbnd : Bounded cs)
    (ev : ObsFn W "KernelWhnf::type_sort_never" [xty, .field (n : F), xlvls] h r h' cs) :
    r = .field (if typeSortNeverNoLet R n us then 1 else 0) := by
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → Bounded cs' :=
    fun hs => Core.bounded_sub hs hbnd
  match Obs.«KernelWhnf::type_sort_never».obs ev with
  | .Forall_n0 (ld12 := ld) (hv50 := hv) (he51 := hr) .. =>
    subst hr
    obtain ⟨D, B, ℓ, rfl, -, -, -⟩ := RawOExact.forallE_of_load hR ld
    have hn0 : n = 0 := field_natCast_eq_zero hn hv
    subst hn0; rfl
  | .Forall_other (x_body := xbody) (cs61 := cs1) (v65 := vn)
      (ld12 := ld) (hne54 := hne) (op87 := op) (ev63 := e1) (hc96 := hc) .. =>
    obtain ⟨D, B, ℓ, rfl, -, hB, -⟩ := RawOExact.forallE_of_load hR ld
    have hnz : n ≠ 0 := field_natCast_ne_zero hn hne
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain rfl := evalBinOp_sub_succ m op
    have hlt : cs1.length < cs.length := by rw [hc]; simp
    exact type_sort_never_rawOExact (n := m) (by omega) hB hus
      (sub fun c hc' => by rw [hc]; simp [hc']) e1
  | .Srt_n0 (x_l := xl) (v129 := vl) (m131 := m1)
      (cs139 := cs1) (cs126 := cs2) (ld12 := ld) (hv122 := hv)
      (ev141 := e1) (ev128 := e2) (hc158 := hc) .. =>
    obtain ⟨l, rfl, rl⟩ := RawOExact.sort_of_load hR ld
    have hn0 : n = 0 := field_natCast_eq_zero hn hv
    subst hn0
    obtain ⟨-, rl', -⟩ := IxVM.Refinement.Levels.levelInstParams_obs e1
      (sub fun c hc' => by rw [hc]; simp [hc']) rl hus
    obtain ⟨hr, -⟩ := IxVM.Refinement.Levels.levelIsNotZero_step e2 vl rfl (substLevel l us) rl'
    exact hr
  | .Srt_other (ld12 := ld) (hne159 := hne) (he163 := hr) .. =>
    subst hr
    obtain ⟨l, rfl, -⟩ := RawOExact.sort_of_load hR ld
    have hnz : n ≠ 0 := field_natCast_ne_zero hn hne
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rfl
  | .other (v1 := v) (ld12 := ld) (hne97 := hnf) (hne166 := hns) (he170 := hr) .. =>
    subst hr
    rw [typeSortNeverNoLet_not_forall_not_sort hR ld hnf hns n us]
    rfl
termination_by cs.length

/-! ## `KernelWhnf::se_mentions` on `RawOExact` -/

/-- Pure mirror of `KernelWhnf::se_mentions` on `KExpr` with a list of target keys. -/
def exprMentionsAny (ks : List KKey) : KExpr → Bool
  | .const n _ => ks.contains n
  | .app f a => exprMentionsAny ks f || exprMentionsAny ks a
  | .lam t b _ => exprMentionsAny ks t || exprMentionsAny ks b
  | .forallE t b _ => exprMentionsAny ks t || exprMentionsAny ks b
  | .letE t v b _ => exprMentionsAny ks t || exprMentionsAny ks v || exprMentionsAny ks b
  | .proj _ _ e => exprMentionsAny ks e
  | _ => false

private theorem contains_map_keyOf {t : Ix.Kernel.RoleTable} (hwf : t.wf = true)
    (a : _root_.Address) (ms : List _root_.Address) :
    (ms.map (Core.keyOf t)).contains (Core.keyOf t a) = Route.memB ms a := by
  by_cases hmem : a ∈ ms
  · rw [Route.memB_pos hmem]
    exact List.contains_iff_exists_mem_beq.mpr ⟨Core.keyOf t a, List.mem_map_of_mem hmem, beq_self_eq_true _⟩
  · rw [Route.memB_neg hmem]
    cases hc : (ms.map (Core.keyOf t)).contains (Core.keyOf t a)
    · rfl
    · obtain ⟨k, hk, hbeq⟩ := List.contains_iff_exists_mem_beq.mp hc
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk
      have heq : a = b := Core.keyOf_inj hwf (eq_of_beq hbeq)
      exact (hmem (heq ▸ hb)).elim

/-- **`KernelWhnf::se_mentions`** decides `exprMentionsAny` bidirectionally on `RawOExact (Core.keyOf t)`
when `t.wf = true`. -/
theorem se_mentions_rawOExact {t : Ix.Kernel.RoleTable} (hwf : t.wf = true)
    {ms : List Bytes.Address} {R : KExpr} {p xs r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (hR : RawOExact (Core.keyOf t) h R p)
    (hms : RepList addrListEnum (Bytes.RepAddressRef addrTy) h ms xs)
    (ev : ObsFn W "KernelWhnf::se_mentions" [p, xs] h r h' cs) :
    r = .field (if exprMentionsAny (ms.map (fun b => Core.keyOf t (ixAddr b))) R then 1 else 0) ∧
      h' = h := by
  rcases Obs.«KernelWhnf::se_mentions».obs ev with
    ⟨x_a, w20, cs34, ld12, ev36, hc53⟩ |
    ⟨x_f, x_x, m72, cs83, ld12, ev85, he106, he107, hc108⟩ |
    ⟨x_f, x_x, v71, m72, cs83, cs116, ld12, ev85, hne109, ev118, hc135⟩ |
    ⟨x_t, x_b, w143, m160, cs171, ld12, ev173, he194, he195, hc196⟩ |
    ⟨x_t, x_b, w143, v159, m160, cs171, cs204, ld12, ev173, hne197, ev206, hc223⟩ |
    ⟨x_t, x_b, w231, m248, cs259, ld12, ev261, he282, he283, hc284⟩ |
    ⟨x_t, x_b, w231, v247, m248, cs259, cs292, ld12, ev261, hne285, ev294, hc311⟩ |
    ⟨x_t, x_v, x_b, m335, cs346, ld12, ev348, he369, he370, hc371⟩ |
    ⟨x_t, x_v, x_b, v334, m335, cs346, m377, cs388, ld12, ev348, hne372, ev390, he411, he412, hc413⟩ |
    ⟨x_t, x_v, x_b, v334, m335, cs346, v376, m377, cs388, cs421, ld12, ev348, hne372, ev390,
      hne414, ev423, hc440⟩ |
    ⟨w448, w449, x_inner, cs468, ld12, ev470, hc487⟩ |
    ⟨v1, ld12, hne54, hne136, hne224, hne312, hne441, hne488, he492, he493, hc494⟩
  · -- Const
    obtain ⟨a, us, rfl, ha, -⟩ := RawOExact.const_of_load hR ld12
    obtain ⟨hr, hh⟩ := Route.se_addr_in_exact ha hms ev36
    refine ⟨?_, hh⟩
    rw [hr]
    simp only [exprMentionsAny, Route.bit]
    have hmap : ms.map (fun b => Core.keyOf t (ixAddr b)) = (ms.map ixAddr).map (Core.keyOf t) := by
      rw [List.map_map]; rfl
    simp only [hmap, contains_map_keyOf hwf]
  · -- App, fn = 1
    obtain ⟨Rf, Ra, rfl, hf, ha⟩ := RawOExact.app_of_load hR ld12
    have hlt : cs83.length < cs.length := by rw [hc108]; simp
    obtain ⟨hr1, hh1⟩ := se_mentions_rawOExact hwf hf hms ev85
    have hm1 : exprMentionsAny (ms.map (fun b => Core.keyOf t (ixAddr b))) Rf = true := by
      cases hb : exprMentionsAny (ms.map (fun b => Core.keyOf t (ixAddr b))) Rf
      · rw [hb] at hr1; simp at hr1
      · rfl
    exact ⟨by rw [he106]; simp [exprMentionsAny, hm1], he107.trans hh1⟩
  · -- App, fn ≠ 1
    obtain ⟨Rf, Ra, rfl, hf, ha⟩ := RawOExact.app_of_load hR ld12
    have hlt1 : cs83.length < cs.length := by rw [hc135]; simp [List.length_append]
    have hlt2 : cs116.length < cs.length := by rw [hc135]; simp [List.length_append]; omega
    obtain ⟨hr1, hh1⟩ := se_mentions_rawOExact hwf hf hms ev85
    subst hh1
    have hm1 : exprMentionsAny (ms.map (fun b => Core.keyOf t (ixAddr b))) Rf = false := by
      cases hb : exprMentionsAny (ms.map (fun b => Core.keyOf t (ixAddr b))) Rf
      · rfl
      · rw [hb] at hr1; exact (hne109 hr1).elim
    obtain ⟨hr2, hh2⟩ := se_mentions_rawOExact hwf ha hms ev118
    exact ⟨by simp [exprMentionsAny, hm1, hr2], hh2⟩
  · -- Lam, ty = 1
    obtain ⟨Rt, Rb, ℓ, rfl, ht, hb, -⟩ := RawOExact.lam_of_load hR ld12
    have hlt : cs171.length < cs.length := by rw [hc196]; simp
    obtain ⟨hr1, hh1⟩ := se_mentions_rawOExact hwf ht hms ev173
    have hm1 : exprMentionsAny (ms.map (fun b => Core.keyOf t (ixAddr b))) Rt = true := by
      cases h' : exprMentionsAny (ms.map (fun b => Core.keyOf t (ixAddr b))) Rt
      · rw [h'] at hr1; simp at hr1
      · rfl
    exact ⟨by rw [he194]; simp [exprMentionsAny, hm1], he195.trans hh1⟩
  · -- Lam, ty ≠ 1
    obtain ⟨Rt, Rb, ℓ, rfl, ht, hb, -⟩ := RawOExact.lam_of_load hR ld12
    have hlt1 : cs171.length < cs.length := by rw [hc223]; simp [List.length_append]
    have hlt2 : cs204.length < cs.length := by rw [hc223]; simp [List.length_append]; omega
    obtain ⟨hr1, hh1⟩ := se_mentions_rawOExact hwf ht hms ev173
    subst hh1
    have hm1 : exprMentionsAny (ms.map (fun b => Core.keyOf t (ixAddr b))) Rt = false := by
      cases h' : exprMentionsAny (ms.map (fun b => Core.keyOf t (ixAddr b))) Rt
      · rfl
      · rw [h'] at hr1; exact (hne197 hr1).elim
    obtain ⟨hr2, hh2⟩ := se_mentions_rawOExact hwf hb hms ev206
    exact ⟨by simp [exprMentionsAny, hm1, hr2], hh2⟩
  · -- Forall, ty = 1
    obtain ⟨Rt, Rb, ℓ, rfl, ht, hb, -⟩ := RawOExact.forallE_of_load hR ld12
    have hlt : cs259.length < cs.length := by rw [hc284]; simp
    obtain ⟨hr1, hh1⟩ := se_mentions_rawOExact hwf ht hms ev261
    have hm1 : exprMentionsAny (ms.map (fun b => Core.keyOf t (ixAddr b))) Rt = true := by
      cases h' : exprMentionsAny (ms.map (fun b => Core.keyOf t (ixAddr b))) Rt
      · rw [h'] at hr1; simp at hr1
      · rfl
    exact ⟨by rw [he282]; simp [exprMentionsAny, hm1], he283.trans hh1⟩
  · -- Forall, ty ≠ 1
    obtain ⟨Rt, Rb, ℓ, rfl, ht, hb, -⟩ := RawOExact.forallE_of_load hR ld12
    have hlt1 : cs259.length < cs.length := by rw [hc311]; simp [List.length_append]
    have hlt2 : cs292.length < cs.length := by rw [hc311]; simp [List.length_append]; omega
    obtain ⟨hr1, hh1⟩ := se_mentions_rawOExact hwf ht hms ev261
    subst hh1
    have hm1 : exprMentionsAny (ms.map (fun b => Core.keyOf t (ixAddr b))) Rt = false := by
      cases h' : exprMentionsAny (ms.map (fun b => Core.keyOf t (ixAddr b))) Rt
      · rfl
      · rw [h'] at hr1; exact (hne285 hr1).elim
    obtain ⟨hr2, hh2⟩ := se_mentions_rawOExact hwf hb hms ev294
    exact ⟨by simp [exprMentionsAny, hm1, hr2], hh2⟩
  · -- Let, ty = 1
    obtain ⟨Rt, Rv, Rb, rfl, ht, hv, hb⟩ := RawOExact.letE_of_load hR ld12
    have hlt : cs346.length < cs.length := by rw [hc371]; simp
    obtain ⟨hr1, hh1⟩ := se_mentions_rawOExact hwf ht hms ev348
    have hm1 : exprMentionsAny (ms.map (fun b => Core.keyOf t (ixAddr b))) Rt = true := by
      cases h' : exprMentionsAny (ms.map (fun b => Core.keyOf t (ixAddr b))) Rt
      · rw [h'] at hr1; simp at hr1
      · rfl
    exact ⟨by rw [he369]; simp [exprMentionsAny, hm1], he370.trans hh1⟩
  · -- Let, ty ≠ 1, val = 1
    obtain ⟨Rt, Rv, Rb, rfl, ht, hv, hb⟩ := RawOExact.letE_of_load hR ld12
    have hlt1 : cs346.length < cs.length := by rw [hc413]; simp [List.length_append]
    have hlt2 : cs388.length < cs.length := by rw [hc413]; simp [List.length_append]; omega
    obtain ⟨hr1, hh1⟩ := se_mentions_rawOExact hwf ht hms ev348
    subst hh1
    obtain ⟨hr2, hh2⟩ := se_mentions_rawOExact hwf hv hms ev390
    have hm2 : exprMentionsAny (ms.map (fun b => Core.keyOf t (ixAddr b))) Rv = true := by
      cases h' : exprMentionsAny (ms.map (fun b => Core.keyOf t (ixAddr b))) Rv
      · rw [h'] at hr2; simp at hr2
      · rfl
    exact ⟨by rw [he411]; simp [exprMentionsAny, hm2], he412.trans hh2⟩
  · -- Let, ty ≠ 1, val ≠ 1
    obtain ⟨Rt, Rv, Rb, rfl, ht, hv, hb⟩ := RawOExact.letE_of_load hR ld12
    have hlt1 : cs346.length < cs.length := by rw [hc440]; simp [List.length_append]
    have hlt2 : cs388.length < cs.length := by rw [hc440]; simp [List.length_append]; omega
    have hlt3 : cs421.length < cs.length := by rw [hc440]; simp [List.length_append]; omega
    obtain ⟨hr1, hh1⟩ := se_mentions_rawOExact hwf ht hms ev348
    subst hh1
    have hm1 : exprMentionsAny (ms.map (fun b => Core.keyOf t (ixAddr b))) Rt = false := by
      cases h' : exprMentionsAny (ms.map (fun b => Core.keyOf t (ixAddr b))) Rt
      · rfl
      · rw [h'] at hr1; exact (hne372 hr1).elim
    obtain ⟨hr2, hh2⟩ := se_mentions_rawOExact hwf hv hms ev390
    subst hh2
    have hm2 : exprMentionsAny (ms.map (fun b => Core.keyOf t (ixAddr b))) Rv = false := by
      cases h' : exprMentionsAny (ms.map (fun b => Core.keyOf t (ixAddr b))) Rv
      · rfl
      · rw [h'] at hr2; exact (hne414 hr2).elim
    obtain ⟨hr3, hh3⟩ := se_mentions_rawOExact hwf hb hms ev423
    exact ⟨by simp [exprMentionsAny, hm1, hm2, hr3], hh3⟩
  · -- Proj
    obtain ⟨_, _, Ri, rfl, -, -, hi⟩ := RawOExact.proj_of_load hR ld12
    have hlt : cs468.length < cs.length := by rw [hc487]; simp
    simp only [exprMentionsAny]
    exact se_mentions_rawOExact hwf hi hms ev470
  · -- Other (BVar, Sort, Lit)
    subst he492; subst he493
    refine ⟨?_, rfl⟩
    obtain ⟨k, E, rep⟩ := hR
    cases rep with
    | bvarLocal _ _ _ | sort _ _ | litNat _ _ _ | litStr _ _ _ => rfl
    | bvarFree _ _ _ hd => omega
    | const cell _ _ =>
      have hld := Lib.load_enum_cell cell; rw [ld12] at hld; injection hld with hv
      exact (hne54 _ rfl hv).elim
    | app cell _ _ =>
      have hld := Lib.load_enum_cell cell; rw [ld12] at hld; injection hld with hv
      exact (hne136 _ rfl hv).elim
    | lam cell _ _ _ =>
      have hld := Lib.load_enum_cell cell; rw [ld12] at hld; injection hld with hv
      exact (hne224 _ rfl hv).elim
    | forallE cell _ _ _ =>
      have hld := Lib.load_enum_cell cell; rw [ld12] at hld; injection hld with hv
      exact (hne312 _ rfl hv).elim
    | letE cell _ _ _ =>
      have hld := Lib.load_enum_cell cell; rw [ld12] at hld; injection hld with hv
      exact (hne441 _ rfl hv).elim
    | proj cell _ _ =>
      have hld := Lib.load_enum_cell cell; rw [ld12] at hld; injection hld with hv
      exact (hne488 _ rfl hv).elim
termination_by cs.length

/-! ## Two-run determinism of `peel_n_foralls_zeta`, `field_has_neg`, and `fields_have_neg` -/

private theorem rawOExact_not_forall_of_let {κ : _root_.Address → KKey} {h₁ h₂ : Heap F}
    {R : KExpr} {p₁ p₂ d₁ b₁ ℓ₁ t₂ v₂ b₂ : SourceValue F}
    (hR₁ : RawOExact κ h₁ R p₁) (hR₂ : RawOExact κ h₂ R p₂)
    (ld₁ : loadValue h₁ p₁ = .ok (.construct kexprEnum "Forall" [d₁, b₁, ℓ₁]))
    (ld₂ : loadValue h₂ p₂ = .ok (.construct kexprEnum "Let" [t₂, v₂, b₂])) : False := by
  obtain ⟨_, _, _, h1, -, -, -⟩ := RawOExact.forallE_of_load hR₁ ld₁
  obtain ⟨_, _, _, h2, -, -, -⟩ := RawOExact.letE_of_load hR₂ ld₂
  rw [h1] at h2; cases h2

private theorem rawOExact_not_forall_of_other {κ : _root_.Address → KKey} {h₁ h₂ : Heap F}
    {R : KExpr} {p₁ p₂ d₁ b₁ ℓ₁ v₂ : SourceValue F}
    (hR₁ : RawOExact κ h₁ R p₁) (hR₂ : RawOExact κ h₂ R p₂)
    (ld₁ : loadValue h₁ p₁ = .ok (.construct kexprEnum "Forall" [d₁, b₁, ℓ₁]))
    (ld₂ : loadValue h₂ p₂ = .ok v₂)
    (hne : ∀ vs : List (SourceValue F), vs.length = 3 → v₂ ≠ .construct kexprEnum "Forall" vs) :
    False := by
  obtain ⟨D, B, m, hReq, -, -, -⟩ := RawOExact.forallE_of_load hR₁ ld₁
  obtain ⟨k, E, rep⟩ := hR₂
  cases rep with
  | forallE cell _ _ _ =>
    have hld := Lib.load_enum_cell cell; rw [ld₂] at hld; injection hld with hv
    exact hne _ rfl hv
  | _ => cases hReq

private theorem rawOExact_not_let_of_other {κ : _root_.Address → KKey} {h₁ h₂ : Heap F}
    {R : KExpr} {p₁ p₂ t₁ v₁ b₁ v₂ : SourceValue F}
    (hR₁ : RawOExact κ h₁ R p₁) (hR₂ : RawOExact κ h₂ R p₂)
    (ld₁ : loadValue h₁ p₁ = .ok (.construct kexprEnum "Let" [t₁, v₁, b₁]))
    (ld₂ : loadValue h₂ p₂ = .ok v₂)
    (hne : ∀ vs : List (SourceValue F), vs.length = 3 → v₂ ≠ .construct kexprEnum "Let" vs) :
    False := by
  obtain ⟨T, V, B, hReq, -, -, -⟩ := RawOExact.letE_of_load hR₁ ld₁
  obtain ⟨k, E, rep⟩ := hR₂
  cases rep with
  | letE cell _ _ _ =>
    have hld := Lib.load_enum_cell cell; rw [ld₂] at hld; injection hld with hv
    exact hne _ rfl hv
  | _ => cases hReq

/-- Two bounded runs of `KernelCheck::peel_n_foralls_zeta` on the same raw `KExpr` and count
return representations of the exact same raw `KExpr`. -/
theorem peel_n_foralls_zeta_det {κ : _root_.Address → KKey}
    {R : KExpr} {n : F} {p₁ p₂ r₁ r₂ : SourceValue F} {h₁ h₁' h₂ h₂' : Heap F}
    {cs₁ cs₂ : List (Call F)}
    (hR₁ : RawOExact κ h₁ R p₁) (hR₂ : RawOExact κ h₂ R p₂)
    (hb₁ : Bounded cs₁) (hb₂ : Bounded cs₂)
    (ev₁ : ObsFn W "KernelCheck::peel_n_foralls_zeta" [p₁, .field n] h₁ r₁ h₁' cs₁)
    (ev₂ : ObsFn W "KernelCheck::peel_n_foralls_zeta" [p₂, .field n] h₂ r₂ h₂' cs₂) :
    ∃ R', RawOExact κ h₁' R' r₁ ∧ RawOExact κ h₂' R' r₂ := by
  match Obs.«KernelCheck::peel_n_foralls_zeta».obs ev₁ with
  | .n0 (hv_fdljvuxp := hv1) (he_whiproaa := hr1) (he_bzwoglyf := hh1) .. =>
    subst hr1; subst hh1
    match Obs.«KernelCheck::peel_n_foralls_zeta».obs ev₂ with
    | .n0 (he_whiproaa := hr2) (he_bzwoglyf := hh2) .. =>
      subst hr2; subst hh2; exact ⟨R, hR₁, hR₂⟩
    | .other_Forall (hne_xjnibfzs := hne2) .. | .other_Let (hne_xjnibfzs := hne2) .. =>
      exact (hne2 hv1).elim
  | .other_Forall (x_body := xb1) (cs_eadgpktx := cs1') (v_fpjmyxdi := vn1)
      (hne_xjnibfzs := hne1) (ld_hdultwxn := ld1) (op_czjgbwao := op1)
      (ev_imkwftmt := e1) (hc_ydqmxojp := hc1) .. =>
    match Obs.«KernelCheck::peel_n_foralls_zeta».obs ev₂ with
    | .n0 (hv_fdljvuxp := hv2) .. => exact (hne1 hv2).elim
    | .other_Forall (x_body := xb2) (cs_eadgpktx := cs2') (v_fpjmyxdi := vn2)
        (ld_hdultwxn := ld2) (op_czjgbwao := op2) (ev_imkwftmt := e2) (hc_ydqmxojp := hc2) .. =>
      obtain ⟨D1, B1, m1, h1, -, hB1, -⟩ := RawOExact.forallE_of_load hR₁ ld1
      obtain ⟨D2, B2, m2, h2, -, hB2, -⟩ := RawOExact.forallE_of_load hR₂ ld2
      rw [h1] at h2; injection h2 with _ hBeq _; subst hBeq
      obtain rfl := Lib.sub_one_inv op1
      obtain rfl := Lib.sub_one_inv op2
      have hlt : cs1'.length < cs₁.length := by rw [hc1]; simp
      exact peel_n_foralls_zeta_det hB1 hB2
        (Core.bounded_sub (fun c hc => by rw [hc1]; simp [hc]) hb₁)
        (Core.bounded_sub (fun c hc => by rw [hc2]; simp [hc]) hb₂)
        e1 e2
    | .other_Let (ld_hdultwxn := ld2) .. =>
      exact (rawOExact_not_forall_of_let hR₁ hR₂ ld1 ld2).elim
  | .other_Let (x_v := xv1) (x_b := xb1) (cs_webebuuu := cs1') (v_qsxgsldq := v1')
      (m_vopdadin := m1') (cs_cuwzkjio := csi1) (hne_xjnibfzs := hne1) (ld_hdultwxn := ld1)
      (ev_mtsqvowg := ei1) (ev_vgbqehni := e1) (hc_thparjte := hc1) .. =>
    match Obs.«KernelCheck::peel_n_foralls_zeta».obs ev₂ with
    | .n0 (hv_fdljvuxp := hv2) .. => exact (hne1 hv2).elim
    | .other_Forall (ld_hdultwxn := ld2) .. =>
      exact (rawOExact_not_forall_of_let hR₂ hR₁ ld2 ld1).elim
    | .other_Let (x_v := xv2) (x_b := xb2) (cs_webebuuu := cs2') (v_qsxgsldq := v2')
        (m_vopdadin := m2') (cs_cuwzkjio := csi2) (ld_hdultwxn := ld2)
        (ev_mtsqvowg := ei2) (ev_vgbqehni := e2) (hc_thparjte := hc2) .. =>
      obtain ⟨T1, V1, B1, h1, -, hV1, hB1⟩ := RawOExact.letE_of_load hR₁ ld1
      obtain ⟨T2, V2, B2, h2, -, hV2, hB2⟩ := RawOExact.letE_of_load hR₂ ld2
      rw [h1] at h2; injection h2 with _ hVeq hBeq _; subst hVeq; subst hBeq
      have hR1' := RawOExact.inst1
        (Core.bounded_sub (fun c hc => by rw [hc1]; simp [hc]) hb₁) hB1 hV1 ei1
      have hR2' := RawOExact.inst1
        (Core.bounded_sub (fun c hc => by rw [hc2]; simp [hc]) hb₂) hB2 hV2 ei2
      have hlt : cs1'.length < cs₁.length := by rw [hc1]; simp [List.length_append]; omega
      exact peel_n_foralls_zeta_det hR1' hR2'
        (Core.bounded_sub (fun c hc => by rw [hc1]; simp [hc]) hb₁)
        (Core.bounded_sub (fun c hc => by rw [hc2]; simp [hc]) hb₂)
        e1 e2
termination_by cs₁.length

/-- Two bounded runs of `KernelModeled::field_has_neg` on the same raw `KExpr` and member
addresses agree on the returned bit (`0` or `1`). -/
theorem field_has_neg_det {t : Ix.Kernel.RoleTable} (hwf : t.wf = true)
    {R : KExpr} {ms₁ ms₂ : List Bytes.Address} {p₁ p₂ xs₁ xs₂ r₁ r₂ : SourceValue F}
    {h₁ h₁' h₂ h₂' : Heap F} {cs₁ cs₂ : List (Call F)}
    (hmsEq : ms₁.map ixAddr = ms₂.map ixAddr)
    (hR₁ : RawOExact (Core.keyOf t) h₁ R p₁) (hR₂ : RawOExact (Core.keyOf t) h₂ R p₂)
    (hms₁ : RepList addrListEnum (Bytes.RepAddressRef addrTy) h₁ ms₁ xs₁)
    (hms₂ : RepList addrListEnum (Bytes.RepAddressRef addrTy) h₂ ms₂ xs₂)
    (hb₁ : Bounded cs₁) (hb₂ : Bounded cs₂)
    (ev₁ : ObsFn W "KernelModeled::field_has_neg" [p₁, xs₁] h₁ r₁ h₁' cs₁)
    (ev₂ : ObsFn W "KernelModeled::field_has_neg" [p₂, xs₂] h₂ r₂ h₂' cs₂) :
    r₁ = r₂ ∧ (r₁ = .field 0 ∨ r₁ = .field 1) := by
  have hkeysEq : ms₁.map (fun b => Core.keyOf t (ixAddr b)) =
      ms₂.map (fun b => Core.keyOf t (ixAddr b)) := by
    have h1 : ms₁.map (fun b => Core.keyOf t (ixAddr b)) = (ms₁.map ixAddr).map (Core.keyOf t) := by
      rw [List.map_map]; rfl
    have h2 : ms₂.map (fun b => Core.keyOf t (ixAddr b)) = (ms₂.map ixAddr).map (Core.keyOf t) := by
      rw [List.map_map]; rfl
    rw [h1, h2, hmsEq]
  match Obs.«KernelModeled::field_has_neg».obs ev₁ with
  | .Forall_n1 (ld_bolbylmd := ld1) (ev_cruxjzov := em1) (he_aimigplr := hr1) .. =>
    subst hr1
    obtain ⟨D1, B1, m1, h1, hD1, -, -⟩ := RawOExact.forallE_of_load hR₁ ld1
    obtain ⟨hm1, -⟩ := se_mentions_rawOExact hwf hD1 hms₁ em1
    match Obs.«KernelModeled::field_has_neg».obs ev₂ with
    | .Forall_n1 (he_aimigplr := hr2) .. => exact ⟨hr2.symm, Or.inr rfl⟩
    | .Forall_other (ld_bolbylmd := ld2) (ev_cruxjzov := em2) (hne_oaofvnuw := hne2) .. =>
      obtain ⟨D2, B2, m2, h2, hD2, -, -⟩ := RawOExact.forallE_of_load hR₂ ld2
      rw [h1] at h2; injection h2 with hDeq _ _; subst hDeq
      obtain ⟨hm2, -⟩ := se_mentions_rawOExact hwf hD2 hms₂ em2
      rw [← hkeysEq, ← hm1] at hm2
      exact (hne2 hm2).elim
    | .Let (ld_bolbylmd := ld2) .. => exact (rawOExact_not_forall_of_let hR₁ hR₂ ld1 ld2).elim
    | .other (ld_bolbylmd := ld2) (hne_pgoqiggy := hne2) .. =>
      exact (rawOExact_not_forall_of_other hR₁ hR₂ ld1 ld2 hne2).elim
  | .Forall_other (cs_uhzdxezv := cs1') (ld_bolbylmd := ld1) (ev_cruxjzov := em1)
      (hne_oaofvnuw := hne1) (ev_tvrcbkdj := er1) (hc_hkhtpxta := hc1) .. =>
    obtain ⟨D1, B1, m1, h1, hD1, hB1, -⟩ := RawOExact.forallE_of_load hR₁ ld1
    obtain ⟨hm1, hh1⟩ := se_mentions_rawOExact hwf hD1 hms₁ em1
    subst hh1
    match Obs.«KernelModeled::field_has_neg».obs ev₂ with
    | .Forall_n1 (ld_bolbylmd := ld2) (ev_cruxjzov := em2) .. =>
      obtain ⟨D2, B2, m2, h2, hD2, -, -⟩ := RawOExact.forallE_of_load hR₂ ld2
      rw [h1] at h2; injection h2 with hDeq _ _; subst hDeq
      obtain ⟨hm2, -⟩ := se_mentions_rawOExact hwf hD2 hms₂ em2
      rw [hkeysEq, ← hm2] at hm1
      exact (hne1 hm1).elim
    | .Forall_other (cs_uhzdxezv := cs2') (ld_bolbylmd := ld2) (ev_cruxjzov := em2)
        (ev_tvrcbkdj := er2) (hc_hkhtpxta := hc2) .. =>
      obtain ⟨D2, B2, m2, h2, hD2, hB2, -⟩ := RawOExact.forallE_of_load hR₂ ld2
      rw [h1] at h2; injection h2 with _ hBeq _; subst hBeq
      obtain ⟨-, hh2⟩ := se_mentions_rawOExact hwf hD2 hms₂ em2
      subst hh2
      have hlt : cs1'.length < cs₁.length := by rw [hc1]; simp [List.length_append]; omega
      exact field_has_neg_det hwf hmsEq hB1 hB2 hms₁ hms₂
        (Core.bounded_sub (fun c hc => by rw [hc1]; simp [hc]) hb₁)
        (Core.bounded_sub (fun c hc => by rw [hc2]; simp [hc]) hb₂)
        er1 er2
    | .Let (ld_bolbylmd := ld2) .. => exact (rawOExact_not_forall_of_let hR₁ hR₂ ld1 ld2).elim
    | .other (ld_bolbylmd := ld2) (hne_pgoqiggy := hne2) .. =>
      exact (rawOExact_not_forall_of_other hR₁ hR₂ ld1 ld2 hne2).elim
  | .Let (cs_urbymnde := cs1') (ld_bolbylmd := ld1) (ev_gemvpjgn := ei1)
      (ev_twjxaozh := er1) (hc_qubwlzze := hc1) .. =>
    obtain ⟨T1, V1, B1, h1, -, hV1, hB1⟩ := RawOExact.letE_of_load hR₁ ld1
    match Obs.«KernelModeled::field_has_neg».obs ev₂ with
    | .Forall_n1 (ld_bolbylmd := ld2) .. | .Forall_other (ld_bolbylmd := ld2) .. =>
      exact (rawOExact_not_forall_of_let hR₂ hR₁ ld2 ld1).elim
    | .Let (cs_urbymnde := cs2') (ld_bolbylmd := ld2) (ev_gemvpjgn := ei2)
        (ev_twjxaozh := er2) (hc_qubwlzze := hc2) .. =>
      obtain ⟨T2, V2, B2, h2, -, hV2, hB2⟩ := RawOExact.letE_of_load hR₂ ld2
      rw [h1] at h2; injection h2 with _ hVeq hBeq _; subst hVeq; subst hBeq
      have hR1' := RawOExact.inst1
        (Core.bounded_sub (fun c hc => by rw [hc1]; simp [hc]) hb₁) hB1 hV1 ei1
      have hR2' := RawOExact.inst1
        (Core.bounded_sub (fun c hc => by rw [hc2]; simp [hc]) hb₂) hB2 hV2 ei2
      have hms₁' := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ei1.heap_extends hms₁
      have hms₂' := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ei2.heap_extends hms₂
      have hlt : cs1'.length < cs₁.length := by rw [hc1]; simp [List.length_append]; omega
      exact field_has_neg_det hwf hmsEq hR1' hR2' hms₁' hms₂'
        (Core.bounded_sub (fun c hc => by rw [hc1]; simp [hc]) hb₁)
        (Core.bounded_sub (fun c hc => by rw [hc2]; simp [hc]) hb₂)
        er1 er2
    | .other (ld_bolbylmd := ld2) (hne_ttotnwna := hne2) .. =>
      exact (rawOExact_not_let_of_other hR₁ hR₂ ld1 ld2 hne2).elim
  | .other (ld_bolbylmd := ld1) (hne_pgoqiggy := hnf1) (hne_ttotnwna := hnl1)
      (he_vpckpvxl := hr1) .. =>
    subst hr1
    match Obs.«KernelModeled::field_has_neg».obs ev₂ with
    | .Forall_n1 (ld_bolbylmd := ld2) .. | .Forall_other (ld_bolbylmd := ld2) .. =>
      exact (rawOExact_not_forall_of_other hR₂ hR₁ ld2 ld1 hnf1).elim
    | .Let (ld_bolbylmd := ld2) .. =>
      exact (rawOExact_not_let_of_other hR₂ hR₁ ld2 ld1 hnl1).elim
    | .other (he_vpckpvxl := hr2) .. => exact ⟨hr2.symm, Or.inl rfl⟩
termination_by cs₁.length

/-- Two bounded runs of `KernelModeled::fields_have_neg` on the same raw `KExpr`, field count, and
member addresses agree on the returned bit (`0` or `1`). -/
theorem fields_have_neg_det {t : Ix.Kernel.RoleTable} (hwf : t.wf = true)
    {R : KExpr} {nf : F} {ms₁ ms₂ : List Bytes.Address} {p₁ p₂ xs₁ xs₂ r₁ r₂ : SourceValue F}
    {h₁ h₁' h₂ h₂' : Heap F} {cs₁ cs₂ : List (Call F)}
    (hmsEq : ms₁.map ixAddr = ms₂.map ixAddr)
    (hR₁ : RawOExact (Core.keyOf t) h₁ R p₁) (hR₂ : RawOExact (Core.keyOf t) h₂ R p₂)
    (hms₁ : RepList addrListEnum (Bytes.RepAddressRef addrTy) h₁ ms₁ xs₁)
    (hms₂ : RepList addrListEnum (Bytes.RepAddressRef addrTy) h₂ ms₂ xs₂)
    (hb₁ : Bounded cs₁) (hb₂ : Bounded cs₂)
    (ev₁ : ObsFn W "KernelModeled::fields_have_neg" [p₁, .field nf, xs₁] h₁ r₁ h₁' cs₁)
    (ev₂ : ObsFn W "KernelModeled::fields_have_neg" [p₂, .field nf, xs₂] h₂ r₂ h₂' cs₂) :
    r₁ = r₂ ∧ (r₁ = .field 0 ∨ r₁ = .field 1) := by
  match Obs.«KernelModeled::fields_have_neg».obs ev₁ with
  | .n0 (hv_fdljvuxp := hv1) (he_daqahcdl := hr1) .. =>
    subst hr1
    match Obs.«KernelModeled::fields_have_neg».obs ev₂ with
    | .n0 (he_daqahcdl := hr2) .. => exact ⟨hr2.symm, Or.inl rfl⟩
    | .other_Forall_n1 (hne_xjnibfzs := hne2) ..
    | .other_Forall_other (hne_xjnibfzs := hne2) ..
    | .other_Let (hne_xjnibfzs := hne2) ..
    | .other_other (hne_xjnibfzs := hne2) .. => exact (hne2 hv1).elim
  | .other_Forall_n1 (hne_xjnibfzs := hne1) (ld_hdultwxn := ld1) (ev_qhhqeiyl := ef1)
      (he_gxcgrrut := hr1) (hc_tuoftutr := hc1) .. =>
    subst hr1
    obtain ⟨D1, B1, m1, h1, hD1, -, -⟩ := RawOExact.forallE_of_load hR₁ ld1
    match Obs.«KernelModeled::fields_have_neg».obs ev₂ with
    | .n0 (hv_fdljvuxp := hv2) .. => exact (hne1 hv2).elim
    | .other_Forall_n1 (he_gxcgrrut := hr2) .. => exact ⟨hr2.symm, Or.inr rfl⟩
    | .other_Forall_other (ld_hdultwxn := ld2) (ev_qhhqeiyl := ef2) (hne_ndgjrece := hne2)
        (hc_iklcezni := hc2) .. =>
      obtain ⟨D2, B2, m2, h2, hD2, -, -⟩ := RawOExact.forallE_of_load hR₂ ld2
      rw [h1] at h2; injection h2 with hDeq _ _; subst hDeq
      have ⟨heq, _⟩ := field_has_neg_det hwf hmsEq hD1 hD2 hms₁ hms₂
        (Core.bounded_sub (fun c hc => by rw [hc1]; simp [hc]) hb₁)
        (Core.bounded_sub (fun c hc => by rw [hc2]; simp [hc]) hb₂)
        ef1 ef2
      exact (hne2 heq.symm).elim
    | .other_Let (ld_hdultwxn := ld2) .. =>
      exact (rawOExact_not_forall_of_let hR₁ hR₂ ld1 ld2).elim
    | .other_other (ld_hdultwxn := ld2) (hne_ljsnsmib := hne2) .. =>
      exact (rawOExact_not_forall_of_other hR₁ hR₂ ld1 ld2 hne2).elim
  | .other_Forall_other (cs_czazwgkf := cs1') (hne_xjnibfzs := hne1) (ld_hdultwxn := ld1)
      (ev_qhhqeiyl := ef1) (hne_ndgjrece := hne1f) (op_fckxizsz := op1)
      (ev_ctfmwuvf := er1) (hc_iklcezni := hc1) .. =>
    obtain ⟨D1, B1, m1, h1, hD1, hB1, -⟩ := RawOExact.forallE_of_load hR₁ ld1
    match Obs.«KernelModeled::fields_have_neg».obs ev₂ with
    | .n0 (hv_fdljvuxp := hv2) .. => exact (hne1 hv2).elim
    | .other_Forall_n1 (ld_hdultwxn := ld2) (ev_qhhqeiyl := ef2) (hc_tuoftutr := hc2) .. =>
      obtain ⟨D2, B2, m2, h2, hD2, -, -⟩ := RawOExact.forallE_of_load hR₂ ld2
      rw [h1] at h2; injection h2 with hDeq _ _; subst hDeq
      have ⟨heq, _⟩ := field_has_neg_det hwf hmsEq hD1 hD2 hms₁ hms₂
        (Core.bounded_sub (fun c hc => by rw [hc1]; simp [hc]) hb₁)
        (Core.bounded_sub (fun c hc => by rw [hc2]; simp [hc]) hb₂)
        ef1 ef2
      exact (hne1f heq).elim
    | .other_Forall_other (cs_czazwgkf := cs2') (ld_hdultwxn := ld2) (ev_qhhqeiyl := ef2)
        (op_fckxizsz := op2) (ev_ctfmwuvf := er2) (hc_iklcezni := hc2) .. =>
      obtain ⟨D2, B2, m2, h2, hD2, hB2, -⟩ := RawOExact.forallE_of_load hR₂ ld2
      rw [h1] at h2; injection h2 with _ hBeq _; subst hBeq
      obtain rfl := Lib.sub_one_inv op1
      obtain rfl := Lib.sub_one_inv op2
      have hB1' := hB1.mono ef1.heap_extends
      have hB2' := hB2.mono ef2.heap_extends
      have hms₁' := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ef1.heap_extends hms₁
      have hms₂' := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ef2.heap_extends hms₂
      have hlt : cs1'.length < cs₁.length := by rw [hc1]; simp [List.length_append]; omega
      exact fields_have_neg_det hwf hmsEq hB1' hB2' hms₁' hms₂'
        (Core.bounded_sub (fun c hc => by rw [hc1]; simp [hc]) hb₁)
        (Core.bounded_sub (fun c hc => by rw [hc2]; simp [hc]) hb₂)
        er1 er2
    | .other_Let (ld_hdultwxn := ld2) .. =>
      exact (rawOExact_not_forall_of_let hR₁ hR₂ ld1 ld2).elim
    | .other_other (ld_hdultwxn := ld2) (hne_ljsnsmib := hne2) .. =>
      exact (rawOExact_not_forall_of_other hR₁ hR₂ ld1 ld2 hne2).elim
  | .other_Let (cs_euqjmqdb := cs1') (hne_xjnibfzs := hne1) (ld_hdultwxn := ld1)
      (ev_mtsqvowg := ei1) (ev_uvywvire := er1) (hc_thparjte := hc1) .. =>
    obtain ⟨T1, V1, B1, h1, -, hV1, hB1⟩ := RawOExact.letE_of_load hR₁ ld1
    match Obs.«KernelModeled::fields_have_neg».obs ev₂ with
    | .n0 (hv_fdljvuxp := hv2) .. => exact (hne1 hv2).elim
    | .other_Forall_n1 (ld_hdultwxn := ld2) .. | .other_Forall_other (ld_hdultwxn := ld2) .. =>
      exact (rawOExact_not_forall_of_let hR₂ hR₁ ld2 ld1).elim
    | .other_Let (cs_euqjmqdb := cs2') (ld_hdultwxn := ld2) (ev_mtsqvowg := ei2)
        (ev_uvywvire := er2) (hc_thparjte := hc2) .. =>
      obtain ⟨T2, V2, B2, h2, -, hV2, hB2⟩ := RawOExact.letE_of_load hR₂ ld2
      rw [h1] at h2; injection h2 with _ hVeq hBeq _; subst hVeq; subst hBeq
      have hR1' := RawOExact.inst1
        (Core.bounded_sub (fun c hc => by rw [hc1]; simp [hc]) hb₁) hB1 hV1 ei1
      have hR2' := RawOExact.inst1
        (Core.bounded_sub (fun c hc => by rw [hc2]; simp [hc]) hb₂) hB2 hV2 ei2
      have hms₁' := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ei1.heap_extends hms₁
      have hms₂' := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ei2.heap_extends hms₂
      have hlt : cs1'.length < cs₁.length := by rw [hc1]; simp [List.length_append]; omega
      exact fields_have_neg_det hwf hmsEq hR1' hR2' hms₁' hms₂'
        (Core.bounded_sub (fun c hc => by rw [hc1]; simp [hc]) hb₁)
        (Core.bounded_sub (fun c hc => by rw [hc2]; simp [hc]) hb₂)
        er1 er2
    | .other_other (ld_hdultwxn := ld2) (hne_vuprrkrb := hne2) .. =>
      exact (rawOExact_not_let_of_other hR₁ hR₂ ld1 ld2 hne2).elim
  | .other_other (hne_xjnibfzs := hne1) (ld_hdultwxn := ld1) (hne_ljsnsmib := hnf1)
      (hne_vuprrkrb := hnl1) (he_lhxtzule := hr1) .. =>
    subst hr1
    match Obs.«KernelModeled::fields_have_neg».obs ev₂ with
    | .n0 (hv_fdljvuxp := hv2) .. => exact (hne1 hv2).elim
    | .other_Forall_n1 (ld_hdultwxn := ld2) .. | .other_Forall_other (ld_hdultwxn := ld2) .. =>
      exact (rawOExact_not_forall_of_other hR₂ hR₁ ld2 ld1 hnf1).elim
    | .other_Let (ld_hdultwxn := ld2) .. =>
      exact (rawOExact_not_let_of_other hR₂ hR₁ ld2 ld1 hnl1).elim
    | .other_other (he_lhxtzule := hr2) .. => exact ⟨hr2.symm, Or.inl rfl⟩
termination_by cs₁.length

/-! ## Canonical raw loads of a block's members and constructors -/

/-- A store `E` holding the block `cb` (members `ms`) at `B` with well-scoped reader expressions
`indTy₀ i` and `ctorTy₀ i j` for every inductive member and constructor. -/
structure BlockCanonReadings (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (B : _root_.Address)
    (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
    (indTy₀ : Nat → KExpr) (ctorTy₀ : Nat → Nat → KExpr) : Prop where
  check : t.check = .ok ()
  record : recordOf E B = some cb
  muts : cb.info = .muts ms
  indcs : ∀ m ∈ ms.toList, ∃ ind, m = .indc ind
  ind : ∀ i ind, i < UInt64.size → ms[i]? = some (.indc ind) →
    (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t B ms)).read
      ind.typ = .ok (indTy₀ i) ∧
    (indTy₀ i).looseBVarsBounded 0 = true ∧
    (indTy₀ i).allLevelParamsDefined (List.range ind.lvls.toNat) = true
  ctor : ∀ i ind j ct, i < UInt64.size → j < UInt64.size →
    ms[i]? = some (.indc ind) → ind.ctors[j]? = some ct →
    ct.cidx.toNat = j ∧
    (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t B ms)).read
      ct.typ = .ok (ctorTy₀ i j) ∧
    (ctorTy₀ i j).looseBVarsBounded 0 = true ∧
    (ctorTy₀ i j).allLevelParamsDefined (List.range ct.lvls.toNat) = true

private theorem val_lt_u64 (x : F) : ZMod.val x < UInt64.size := by
  have hlt := ZMod.val_lt x
  change ZMod.val x < 18446744069414584321 at hlt
  have : UInt64.size = 18446744073709551616 := rfl
  omega

/-- `Ingress::get_ci_iprj` on a block with `BlockCanonReadings` returns an `Induct` value whose
type pointer is `RawOExact` of the canonical raw annotation of `indTy₀ i.val`. -/
theorem get_ci_iprj_rawOExact {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {B : _root_.Address}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {indTy₀ : Nat → KExpr} {ctorTy₀ : Nat → Nat → KExpr}
    (hR : BlockCanonReadings t E B cb ms indTy₀ ctorTy₀)
    {b : Bytes.Address} {bp ptr : SourceValue F} {i : F} {h h' : Heap F} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbd : Bounded cs)
    (hb : Bytes.RepAddressRef addrTy h b bp) (hbB : ixAddr b = B)
    (ev : ObsFn W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' cs) :
    ∃ (ind : Ixon.Inductive) (raw : KExpr) (tyPtr blkPtr : SourceValue F),
      ms[i.val]? = some (.indc ind) ∧
      ind.lvls.toNat < 4294967296 ∧ ind.params.toNat < 72057594037927936 ∧
      ind.indices.toNat < 72057594037927936 ∧ ind.ctors.size < 72057594037927936 ∧
      loadValue h' ptr = .ok (.construct Core.kciEnum "Induct"
        [.field (ind.lvls.toNat : F), tyPtr, .field (ind.params.toNat : F),
          .field (ind.indices.toNat : F), .field (ind.ctors.size : F),
          .field (if ind.isUnsafe then 1 else 0), blkPtr, .field (i.val : F)]) ∧
      L1.canonicalRawAnnotation cb (List.range ind.lvls.toNat)
        ((L1.mutsRootOffset ms.toList i.val : Nat) : F) ind.typ (indTy₀ i.val) = some raw ∧
      raw.eraseMeta = (indTy₀ i.val).eraseMeta ∧
      RawOExact (Core.keyOf t) h' raw tyPtr := by
  obtain ⟨-, -, blkBytes, cb', ms', ind', blobs, v, hhB, haB, hexB, -, hcb, hms, hhp, hld,
    hraw, tree, plan, built, planned, hlev⟩ := L1.get_ci_iprj_origin_spec hbd hb ev
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hR.record
  have hbB' : blkBytes = lcB.rawBytes := Core.load_escape hgetB hnc blkBytes hhB (haB.trans hbB)
  have hcB : cb = cb' := by rw [hbB', hdecB] at hexB; exact Except.ok.inj hexB
  subst hcB
  have hmsEq : ms = ms' := Ixon.ConstantInfo.muts.inj (hR.muts.symm.trans hcb)
  subst hmsEq
  have hmem : ms[i.val]? = some (.indc ind') := by rw [← Array.getElem?_toList]; exact hms
  obtain ⟨hty, hlbb, hdef⟩ := hR.ind i.val ind' (val_lt_u64 i) hmem
  have hagree := LoadedReads.blobReadAgreement_of_noCollision hnc hhp t
  obtain ⟨hlvls, hp56, hi56, hc56, hidx56, tyPtr, blkPtr, b', -, -, hv, rty⟩ := hraw
  subst hv
  obtain ⟨count, typePtr, fields, shape, trace⟩ := hlev
  injection shape with _ _ hargs
  injection hargs with _ hrest
  injection hrest with htp _
  subst htp
  have hread' : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t (fun x => E.blobs.get? x))
      cb (Ix.Kernel.Reader.recParam (List.range ind'.lvls.toNat))
      (blockSelf t B ms)).read ind'.typ = .ok (indTy₀ i.val) := by
    rw [Assembly.recParam_range]; exact hty
  have hselfk : ∀ idx x m k, (L1.blockRecurAddrs B ms.toList)[idx]? = some x →
      blockSelf t B ms idx = some m → m = .ok k → k = Core.keyOf t x :=
    LoadedReads.blockSelf_key t B ms
  have rtyB : L1.RawConvExpr cb.refs.toList (L1.blockRecurAddrs B ms.toList) cb.univs.toList
      cb.sharing.toList blobs h' 4294967295 ind'.typ tyPtr := by
    rw [← hbB]; exact rty
  obtain ⟨raw, sem, -, hrep, -, htrace⟩ :=
    rtyB.toRawTmCExactTrace_of_blobAgreement (κ := Core.keyOf t) (ps := List.range ind'.lvls.toNat)
      (by simp) (by simpa using hlvls)
      (LoadedReads.readCtx_keyAt_inv hR.check _) hselfk hagree hread' hlbb hdef
  have htr := htrace plan trace []
  rw [List.append_nil] at htr
  have hcan : L1.canonicalRawAnnotation cb (List.range ind'.lvls.toNat)
      ((L1.mutsRootOffset ms.toList i.val : Nat) : F) ind'.typ (indTy₀ i.val) = some raw := by
    unfold L1.canonicalRawAnnotation
    rw [L1.canonicalRawTree_of_built built, planned]
    change (L1.applyRawBinderTrace (fun level => Core.bmeta (L1.invPosLevel (List.range ind'.lvls.toNat) level))
      (indTy₀ i.val) plan).bind (fun result => some result.1) = some raw
    rw [htr]; rfl
  have herase : raw.eraseMeta = (indTy₀ i.val).eraseMeta :=
    L1.applyRawBinderTrace_eraseMeta (indTy₀ i.val) htr
  have hraw_eq : Core.posOf (List.range ind'.lvls.toNat) raw = raw :=
    Decl.posOf_range ind'.lvls.toNat raw
  have hrep0 := hrep 0 (fun _ => default)
  rw [hraw_eq] at hrep0
  exact ⟨ind', raw, tyPtr, blkPtr, hmem, hlvls, hp56, hi56, hc56, hld, hcan, herase, ⟨0, _, hrep0⟩⟩

/-- `Ingress::get_ci_cprj` on a block with `BlockCanonReadings` returns a `Ctor` value whose
type pointer is `RawOExact` of the canonical raw annotation of `ctorTy₀ i.val j.val`. -/
theorem get_ci_cprj_rawOExact {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {B : _root_.Address}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {indTy₀ : Nat → KExpr} {ctorTy₀ : Nat → Nat → KExpr}
    (hR : BlockCanonReadings t E B cb ms indTy₀ ctorTy₀)
    {b : Bytes.Address} {bp ptr : SourceValue F} {i j : F} {h h' : Heap F} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbd : Bounded cs)
    (hb : Bytes.RepAddressRef addrTy h b bp) (hbB : ixAddr b = B)
    (ev : ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field j] h ptr h' cs) :
    ∃ (ind : Ixon.Inductive) (ct : Ixon.Constructor) (raw : KExpr) (tyPtr blkPtr : SourceValue F),
      ms[i.val]? = some (.indc ind) ∧ ind.ctors[j.val]? = some ct ∧
      ct.lvls.toNat < 4294967296 ∧ ct.params.toNat < 72057594037927936 ∧
      ct.fields.toNat < 72057594037927936 ∧
      loadValue h' ptr = .ok (.construct Core.kciEnum "Ctor"
        [.field (ct.lvls.toNat : F), tyPtr, blkPtr, .field (i.val : F), .field (ct.cidx.toNat : F),
          .field (ct.params.toNat : F), .field (ct.fields.toNat : F),
          .field (if ct.isUnsafe then 1 else 0)]) ∧
      L1.canonicalRawAnnotation cb (List.range ct.lvls.toNat)
        (((L1.mutsRootOffset ms.toList i.val : Nat) : F) + 1 + ((j.val : Nat) : F))
        ct.typ (ctorTy₀ i.val j.val) = some raw ∧
      RawOExact (Core.keyOf t) h' raw tyPtr := by
  obtain ⟨-, -, -, blkBytes, cb', ms', ind', ct', blobs, v, hhB, haB, hexB, -, hcb, hms, hcts,
    hhp, hld, hraw, tree, plan, built, planned, hlev⟩ := L1.get_ci_cprj_origin_spec hbd hb ev
  rw [← ZMod.natCast_zmod_val j] at planned
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hR.record
  have hbB' : blkBytes = lcB.rawBytes := Core.load_escape hgetB hnc blkBytes hhB (haB.trans hbB)
  have hcB : cb = cb' := by rw [hbB', hdecB] at hexB; exact Except.ok.inj hexB
  subst hcB
  have hmsEq : ms = ms' := Ixon.ConstantInfo.muts.inj (hR.muts.symm.trans hcb)
  subst hmsEq
  have hmem : ms[i.val]? = some (.indc ind') := by rw [← Array.getElem?_toList]; exact hms
  have hct : ind'.ctors[j.val]? = some ct' := by rw [← Array.getElem?_toList]; exact hcts
  obtain ⟨hcidx, hty, hlbb, hdef⟩ :=
    hR.ctor i.val ind' j.val ct' (val_lt_u64 i) (val_lt_u64 j) hmem hct
  have hagree := LoadedReads.blobReadAgreement_of_noCollision hnc hhp t
  obtain ⟨hlvls, hcidx56, hp56, hf56, hidx56, tyPtr, blkPtr, b', -, -, hv, rty⟩ := hraw
  subst hv
  obtain ⟨count, typePtr, fields, shape, trace⟩ := hlev
  injection shape with _ _ hargs
  injection hargs with _ hrest
  injection hrest with htp _
  subst htp
  have hread' : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t (fun x => E.blobs.get? x))
      cb (Ix.Kernel.Reader.recParam (List.range ct'.lvls.toNat))
      (blockSelf t B ms)).read ct'.typ = .ok (ctorTy₀ i.val j.val) := by
    rw [Assembly.recParam_range]; exact hty
  have hselfk : ∀ idx x m k, (L1.blockRecurAddrs B ms.toList)[idx]? = some x →
      blockSelf t B ms idx = some m → m = .ok k → k = Core.keyOf t x :=
    LoadedReads.blockSelf_key t B ms
  have rtyB : L1.RawConvExpr cb.refs.toList (L1.blockRecurAddrs B ms.toList) cb.univs.toList
      cb.sharing.toList blobs h' 4294967295 ct'.typ tyPtr := by
    rw [← hbB]; exact rty
  obtain ⟨raw, sem, -, hrep, -, htrace⟩ :=
    rtyB.toRawTmCExactTrace_of_blobAgreement (κ := Core.keyOf t) (ps := List.range ct'.lvls.toNat)
      (by simp) (by simpa using hlvls)
      (LoadedReads.readCtx_keyAt_inv hR.check _) hselfk hagree hread' hlbb hdef
  have htr := htrace plan trace []
  rw [List.append_nil] at htr
  have hcan : L1.canonicalRawAnnotation cb (List.range ct'.lvls.toNat)
      (((L1.mutsRootOffset ms.toList i.val : Nat) : F) + 1 + ((j.val : Nat) : F))
      ct'.typ (ctorTy₀ i.val j.val) = some raw := by
    unfold L1.canonicalRawAnnotation
    rw [L1.canonicalRawTree_of_built built, planned]
    change (L1.applyRawBinderTrace (fun level => Core.bmeta (L1.invPosLevel (List.range ct'.lvls.toNat) level))
      (ctorTy₀ i.val j.val) plan).bind (fun result => some result.1) = some raw
    rw [htr]; rfl
  have hraw_eq : Core.posOf (List.range ct'.lvls.toNat) raw = raw :=
    Decl.posOf_range ct'.lvls.toNat raw
  have hrep0 := hrep 0 (fun _ => default)
  rw [hraw_eq] at hrep0
  exact ⟨ind', ct', raw, tyPtr, blkPtr, hmem, hct, hlvls, hp56, hf56, hld, hcan, ⟨0, _, hrep0⟩⟩

/-! ## Determinism of `ctors_have_neg`, `members_have_neg`, `block_has_neg_occ`, and `modeled_proj_eligible` -/

private theorem ctors_seg_det {t : Ix.Kernel.RoleTable} (hwf : t.wf = true)
    {R : KExpr} {nf : F} {ms₁ ms₂ : List Bytes.Address}
    {p₁ p₂ cty₁ cty₂ np₁ np₂ blk₁ blk₂ pos₁ pos₂ nc₁ nc₂ xs₁ xs₂ cidx₁ cidx₂ r₁ r₂ : SourceValue F}
    {h₁ h₁' h₂ h₂' : Heap F} {cs₁ cs₂ : List (Call F)}
    (hmsEq : ms₁.map ixAddr = ms₂.map ixAddr)
    (hR₁ : RawOExact (Core.keyOf t) h₁ R p₁) (hR₂ : RawOExact (Core.keyOf t) h₂ R p₂)
    (hms₁ : RepList addrListEnum (Bytes.RepAddressRef addrTy) h₁ ms₁ xs₁)
    (hms₂ : RepList addrListEnum (Bytes.RepAddressRef addrTy) h₂ ms₂ xs₂)
    (hb₁ : Bounded cs₁) (hb₂ : Bounded cs₂)
    (sg₁ : Obs.«KernelModeled::ctors_have_neg».Seg_azhodmri p₁ cty₁ np₁ (.field nf) blk₁ pos₁ nc₁ xs₁ cidx₁ h₁ r₁ h₁' cs₁)
    (sg₂ : Obs.«KernelModeled::ctors_have_neg».Seg_azhodmri p₂ cty₂ np₂ (.field nf) blk₂ pos₂ nc₂ xs₂ cidx₂ h₂ r₂ h₂' cs₂) :
    r₁ = r₂ ∧ (r₁ = .field 0 ∨ r₁ = .field 1) := by
  have hkeysEq : ms₁.map (fun b => Core.keyOf t (ixAddr b)) =
      ms₂.map (fun b => Core.keyOf t (ixAddr b)) := by
    have h1 : ms₁.map (fun b => Core.keyOf t (ixAddr b)) = (ms₁.map ixAddr).map (Core.keyOf t) := by
      rw [List.map_map]; rfl
    have h2 : ms₂.map (fun b => Core.keyOf t (ixAddr b)) = (ms₂.map ixAddr).map (Core.keyOf t) := by
      rw [List.map_map]; rfl
    rw [h1, h2, hmsEq]
  match sg₁ with
  | .n0 (ev_nliglvbu := em1) (he_abspvrfw := hr1) .. =>
    subst hr1
    obtain ⟨hm1, -⟩ := se_mentions_rawOExact hwf hR₁ hms₁ em1
    match sg₂ with
    | .n0 (he_abspvrfw := hr2) .. => exact ⟨hr2.symm, Or.inl rfl⟩
    | .other (ev_nliglvbu := em2) (hne_iyikxncy := hne2) .. =>
      obtain ⟨hm2, -⟩ := se_mentions_rawOExact hwf hR₂ hms₂ em2
      rw [← hkeysEq, ← hm1] at hm2
      exact (hne2 hm2).elim
  | .other (ev_nliglvbu := em1) (hne_iyikxncy := hne1) (ev_gcuxfpiu := ef1)
      (hc_dxlbntdp := hc1) .. =>
    obtain ⟨hm1, hh1⟩ := se_mentions_rawOExact hwf hR₁ hms₁ em1
    subst hh1
    match sg₂ with
    | .n0 (ev_nliglvbu := em2) .. =>
      obtain ⟨hm2, -⟩ := se_mentions_rawOExact hwf hR₂ hms₂ em2
      rw [hkeysEq, ← hm2] at hm1
      exact (hne1 hm1).elim
    | .other (ev_nliglvbu := em2) (ev_gcuxfpiu := ef2) (hc_dxlbntdp := hc2) .. =>
      obtain ⟨-, hh2⟩ := se_mentions_rawOExact hwf hR₂ hms₂ em2
      subst hh2
      exact fields_have_neg_det hwf hmsEq hR₁ hR₂ hms₁ hms₂
        (Core.bounded_sub (fun c hc => by rw [hc1]; simp [hc]) hb₁)
        (Core.bounded_sub (fun c hc => by rw [hc2]; simp [hc]) hb₂)
        ef1 ef2

private theorem ctors_have_neg_det {t : Ix.Kernel.RoleTable} {E₁ E₂ : Ixon.Env}
    {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {indTy₀ : Nat → KExpr} {ctorTy₀ : Nat → Nat → KExpr}
    (hR₁ : BlockCanonReadings t E₁ B cb ms indTy₀ ctorTy₀)
    (hR₂ : BlockCanonReadings t E₂ B cb ms indTy₀ ctorTy₀)
    {b₁ b₂ : Bytes.Address} (hb₁B : ixAddr b₁ = B) (hb₂B : ixAddr b₂ = B)
    {pos nct cidx : F} {ms₁ ms₂ : List Bytes.Address} {bp₁ bp₂ xs₁ xs₂ r₁ r₂ : SourceValue F}
    {h₁ h₁' h₂ h₂' : Heap F} {cs₁ cs₂ : List (Call F)}
    (hmsEq : ms₁.map ixAddr = ms₂.map ixAddr)
    (hbp₁ : Bytes.RepAddressRef addrTy h₁ b₁ bp₁) (hbp₂ : Bytes.RepAddressRef addrTy h₂ b₂ bp₂)
    (hms₁ : RepList addrListEnum (Bytes.RepAddressRef addrTy) h₁ ms₁ xs₁)
    (hms₂ : RepList addrListEnum (Bytes.RepAddressRef addrTy) h₂ ms₂ xs₂)
    (hnc₁ : ¬ View.HashedCollision { env := E₁ } [] cs₁) (hbd₁ : Bounded cs₁)
    (hnc₂ : ¬ View.HashedCollision { env := E₂ } [] cs₂) (hbd₂ : Bounded cs₂)
    (ev₁ : ObsFn W "KernelModeled::ctors_have_neg" [bp₁, .field pos, .field nct, xs₁, .field cidx] h₁ r₁ h₁' cs₁)
    (ev₂ : ObsFn W "KernelModeled::ctors_have_neg" [bp₂, .field pos, .field nct, xs₂, .field cidx] h₂ r₂ h₂' cs₂) :
    r₁ = r₂ ∧ (r₁ = .field 0 ∨ r₁ = .field 1) := by
  have hwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [hR₁.check]; rfl
  match Obs.«KernelModeled::ctors_have_neg».obs ev₁ with
  | .n0 (op_mmyajoju := op1) (he_daqahcdl := hr1) .. =>
    subst hr1
    match Obs.«KernelModeled::ctors_have_neg».obs ev₂ with
    | .n0 (he_daqahcdl := hr2) .. => exact ⟨hr2.symm, Or.inl rfl⟩
    | .other_n1 (op_mmyajoju := op2) (hne_xjnibfzs := hne2) ..
    | .other_other (op_mmyajoju := op2) (hne_xjnibfzs := hne2) .. =>
      rw [op1] at op2; injection op2 with he; exact (hne2 he.symm).elim
  | .other_n1 (op_mmyajoju := op1) (hne_xjnibfzs := hne1) (ev_fmlfsvfr := ec1)
      (ld_cwtqaeih := ld1) (ev_njgdsfcw := ep1) (sg_gkdtuzjn := sg1)
      (he_yyywwiyz := hr1) (hc_ahbbsdfg := hc1) .. =>
    subst hr1
    match Obs.«KernelModeled::ctors_have_neg».obs ev₂ with
    | .n0 (op_mmyajoju := op2) .. =>
      rw [op1] at op2; injection op2 with he; exact (hne1 he).elim
    | .other_n1 (he_yyywwiyz := hr2) .. => exact ⟨hr2.symm, Or.inr rfl⟩
    | .other_other (ev_fmlfsvfr := ec2) (ld_cwtqaeih := ld2) (ev_njgdsfcw := ep2)
        (sg_gkdtuzjn := sg2) (hne_arcdkpuy := hne2) (hc_bmwtsztg := hc2) .. =>
      obtain ⟨ind1, ct1, raw1, tyP1, _, hm1, hct1, _, _, _, hld1, hcan1, hRaw1⟩ :=
        get_ci_cprj_rawOExact hR₁
          (fun hc => hnc₁ (Core.collision_mono (fun c h => by rw [hc1]; simp [h]) hc))
          (Core.bounded_sub (fun c h => by rw [hc1]; simp [h]) hbd₁) hbp₁ hb₁B ec1
      obtain ⟨ind2, ct2, raw2, tyP2, _, hm2, hct2, _, _, _, hld2, hcan2, hRaw2⟩ :=
        get_ci_cprj_rawOExact hR₂
          (fun hc => hnc₂ (Core.collision_mono (fun c h => by rw [hc2]; simp [h]) hc))
          (Core.bounded_sub (fun c h => by rw [hc2]; simp [h]) hbd₂) hbp₂ hb₂B ec2
      have eind : ind1 = ind2 := Ixon.MutConst.indc.inj (Option.some.inj (hm1.symm.trans hm2))
      subst eind
      have ect : ct1 = ct2 := Option.some.inj (hct1.symm.trans hct2)
      subst ect
      have eraw : raw1 = raw2 := Option.some.inj (hcan1.symm.trans hcan2)
      subst eraw
      rw [hld1] at ld1; injection ld1 with hv1
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hv1
      obtain ⟨-, rfl, -, -, -, rfl, rfl, -⟩ := hv1
      rw [hld2] at ld2; injection ld2 with hv2
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hv2
      obtain ⟨-, rfl, -, -, -, rfl, rfl, -⟩ := hv2
      obtain ⟨R', hR1', hR2'⟩ := peel_n_foralls_zeta_det hRaw1 hRaw2
        (Core.bounded_sub (fun c h => by rw [hc1]; simp [h]) hbd₁)
        (Core.bounded_sub (fun c h => by rw [hc2]; simp [h]) hbd₂) ep1 ep2
      have hms₁' := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
        (ec1.heap_extends.trans ep1.heap_extends) hms₁
      have hms₂' := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
        (ec2.heap_extends.trans ep2.heap_extends) hms₂
      have ⟨heq, _⟩ := ctors_seg_det hwf hmsEq hR1' hR2' hms₁' hms₂'
        (Core.bounded_sub (fun c h => by rw [hc1]; simp [h]) hbd₁)
        (Core.bounded_sub (fun c h => by rw [hc2]; simp [h]) hbd₂) sg1 sg2
      exact (hne2 heq.symm).elim
  | .other_other (cs_urtwagyl := cs1') (op_mmyajoju := op1) (hne_xjnibfzs := hne1)
      (ev_fmlfsvfr := ec1) (ld_cwtqaeih := ld1) (ev_njgdsfcw := ep1) (sg_gkdtuzjn := sg1)
      (hne_arcdkpuy := hne1s) (op_mjdaellc := op1a) (ev_aarfidnn := er1)
      (hc_bmwtsztg := hc1) .. =>
    match Obs.«KernelModeled::ctors_have_neg».obs ev₂ with
    | .n0 (op_mmyajoju := op2) .. =>
      rw [op1] at op2; injection op2 with he; exact (hne1 he).elim
    | .other_n1 (ev_fmlfsvfr := ec2) (ld_cwtqaeih := ld2) (ev_njgdsfcw := ep2)
        (sg_gkdtuzjn := sg2) (hc_ahbbsdfg := hc2) .. =>
      obtain ⟨ind1, ct1, raw1, tyP1, _, hm1, hct1, _, _, _, hld1, hcan1, hRaw1⟩ :=
        get_ci_cprj_rawOExact hR₁
          (fun hc => hnc₁ (Core.collision_mono (fun c h => by rw [hc1]; simp [h]) hc))
          (Core.bounded_sub (fun c h => by rw [hc1]; simp [h]) hbd₁) hbp₁ hb₁B ec1
      obtain ⟨ind2, ct2, raw2, tyP2, _, hm2, hct2, _, _, _, hld2, hcan2, hRaw2⟩ :=
        get_ci_cprj_rawOExact hR₂
          (fun hc => hnc₂ (Core.collision_mono (fun c h => by rw [hc2]; simp [h]) hc))
          (Core.bounded_sub (fun c h => by rw [hc2]; simp [h]) hbd₂) hbp₂ hb₂B ec2
      have eind : ind1 = ind2 := Ixon.MutConst.indc.inj (Option.some.inj (hm1.symm.trans hm2))
      subst eind
      have ect : ct1 = ct2 := Option.some.inj (hct1.symm.trans hct2)
      subst ect
      have eraw : raw1 = raw2 := Option.some.inj (hcan1.symm.trans hcan2)
      subst eraw
      rw [hld1] at ld1; injection ld1 with hv1
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hv1
      obtain ⟨-, rfl, -, -, -, rfl, rfl, -⟩ := hv1
      rw [hld2] at ld2; injection ld2 with hv2
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hv2
      obtain ⟨-, rfl, -, -, -, rfl, rfl, -⟩ := hv2
      obtain ⟨R', hR1', hR2'⟩ := peel_n_foralls_zeta_det hRaw1 hRaw2
        (Core.bounded_sub (fun c h => by rw [hc1]; simp [h]) hbd₁)
        (Core.bounded_sub (fun c h => by rw [hc2]; simp [h]) hbd₂) ep1 ep2
      have hms₁' := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
        (ec1.heap_extends.trans ep1.heap_extends) hms₁
      have hms₂' := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
        (ec2.heap_extends.trans ep2.heap_extends) hms₂
      have ⟨heq, _⟩ := ctors_seg_det hwf hmsEq hR1' hR2' hms₁' hms₂'
        (Core.bounded_sub (fun c h => by rw [hc1]; simp [h]) hbd₁)
        (Core.bounded_sub (fun c h => by rw [hc2]; simp [h]) hbd₂) sg1 sg2
      exact (hne1s heq).elim
    | .other_other (cs_urtwagyl := cs2') (ev_fmlfsvfr := ec2) (ev_njgdsfcw := ep2)
        (sg_gkdtuzjn := sg2) (op_mjdaellc := op2a) (ev_aarfidnn := er2)
        (hc_bmwtsztg := hc2) .. =>
      simp only [evalBinOp, Except.ok.injEq] at op1a op2a
      subst op1a; subst op2a
      have ext1 : Heap.Extends h₁ _ := ec1.heap_extends.trans (ep1.heap_extends.trans (match sg1 with
        | .n0 (ev_nliglvbu := ev) (he_ilwwyerm := hh) .. => hh ▸ ev.heap_extends
        | .other (ev_nliglvbu := ev) (ev_gcuxfpiu := ef) .. => ev.heap_extends.trans ef.heap_extends))
      have ext2 : Heap.Extends h₂ _ := ec2.heap_extends.trans (ep2.heap_extends.trans (match sg2 with
        | .n0 (ev_nliglvbu := ev) (he_ilwwyerm := hh) .. => hh ▸ ev.heap_extends
        | .other (ev_nliglvbu := ev) (ev_gcuxfpiu := ef) .. => ev.heap_extends.trans ef.heap_extends))
      have hlt : cs1'.length < cs₁.length := by rw [hc1]; simp [List.length_append]; omega
      exact ctors_have_neg_det hR₁ hR₂ hb₁B hb₂B hmsEq
        (Bytes.repAddressRef_heapMono₂ addrTy ext1 hbp₁)
        (Bytes.repAddressRef_heapMono₂ addrTy ext2 hbp₂)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext1 hms₁)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext2 hms₂)
        (fun hc => hnc₁ (Core.collision_mono (fun c h => by rw [hc1]; simp [h]) hc))
        (Core.bounded_sub (fun c h => by rw [hc1]; simp [h]) hbd₁)
        (fun hc => hnc₂ (Core.collision_mono (fun c h => by rw [hc2]; simp [h]) hc))
        (Core.bounded_sub (fun c h => by rw [hc2]; simp [h]) hbd₂)
        er1 er2
termination_by cs₁.length

private theorem ctorList_length_spec {xs : List Ixon.Constructor} {l r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<Ixon::Constructor>» [l] h r h' cs)
    (hl : RepList L1.constructorListEnum L1.RepConstructor h xs l) :
    r = .field (xs.length : F) ∧ h' = h := by
  rw [← Obs.Names.«Lists::length<Ixon::Constructor>».symbol] at ev
  have hl' : RepList (Instance.mk "Lists::Node" [.named "Ixon::Constructor" []]).symbol
      L1.RepConstructor h xs l := by
    rw [Obs.Names.«Lists::Node<Ixon::Constructor>».symbol]
    exact hl
  exact Lib.Lists.length_spec ev hl'

private theorem members_have_neg_det {t : Ix.Kernel.RoleTable} {E₁ E₂ : Ixon.Env}
    {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {indTy₀ : Nat → KExpr} {ctorTy₀ : Nat → Nat → KExpr}
    (hR₁ : BlockCanonReadings t E₁ B cb ms indTy₀ ctorTy₀)
    (hR₂ : BlockCanonReadings t E₂ B cb ms indTy₀ ctorTy₀)
    {b₁ b₂ : Bytes.Address} (hb₁B : ixAddr b₁ = B) (hb₂B : ixAddr b₂ = B) :
    ∀ (rem : List Ixon.MutConst) {pos : F} {ms₁ ms₂ : List Bytes.Address}
      {bp₁ bp₂ xm₁ xm₂ xs₁ xs₂ r₁ r₂ : SourceValue F} {h₁ h₁' h₂ h₂' : Heap F}
      {cs₁ cs₂ : List (Call F)},
      ms₁.map ixAddr = ms₂.map ixAddr →
      Bytes.RepAddressRef addrTy h₁ b₁ bp₁ → Bytes.RepAddressRef addrTy h₂ b₂ bp₂ →
      RepList L1.mutConstListEnum L1.RepMutConst h₁ rem xm₁ →
      RepList L1.mutConstListEnum L1.RepMutConst h₂ rem xm₂ →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h₁ ms₁ xs₁ →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h₂ ms₂ xs₂ →
      ¬ View.HashedCollision { env := E₁ } [] cs₁ → Bounded cs₁ →
      ¬ View.HashedCollision { env := E₂ } [] cs₂ → Bounded cs₂ →
      ObsFn W "KernelModeled::members_have_neg" [bp₁, xm₁, .field pos, xs₁] h₁ r₁ h₁' cs₁ →
      ObsFn W "KernelModeled::members_have_neg" [bp₂, xm₂, .field pos, xs₂] h₂ r₂ h₂' cs₂ →
      r₁ = r₂ ∧ (r₁ = .field 0 ∨ r₁ = .field 1)
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hrm₁, hrm₂, _, _, _, _, _, _, ev₁, ev₂ => by
    match Obs.«KernelModeled::members_have_neg».obs ev₁ with
    | .Nil (he_jxbhhcax := hr1) .. =>
      subst hr1
      match Obs.«KernelModeled::members_have_neg».obs ev₂ with
      | .Nil (he_jxbhhcax := hr2) .. => exact ⟨hr2.symm, Or.inl rfl⟩
      | .Cons_Indc_n1 (ld_bolbylmd := ld2) ..
      | .Cons_Indc_other (ld_bolbylmd := ld2) ..
      | .Cons_other (ld_bolbylmd := ld2) .. =>
        obtain ⟨_, _, heq, -, -⟩ := Core.RepList.cons_of_load hrm₂ ld2; cases heq
    | .Cons_Indc_n1 (ld_bolbylmd := ld1) ..
    | .Cons_Indc_other (ld_bolbylmd := ld1) ..
    | .Cons_other (ld_bolbylmd := ld1) .. =>
      obtain ⟨_, _, heq, -, -⟩ := Core.RepList.cons_of_load hrm₁ ld1; cases heq
  | m :: rem, pos, ms₁, ms₂, bp₁, bp₂, xm₁, xm₂, xs₁, xs₂, r₁, r₂, h₁, h₁', h₂, h₂', cs₁, cs₂,
      hmsEq, hbp₁, hbp₂, hrm₁, hrm₂, hms₁, hms₂, hnc₁, hbd₁, hnc₂, hbd₂, ev₁, ev₂ => by
    match Obs.«KernelModeled::members_have_neg».obs ev₁ with
    | .Nil (ld_bolbylmd := ld1) .. => cases Core.RepList.nil_of_load hrm₁ ld1
    | .Cons_Indc_n1 (ld_bolbylmd := ld1) (ev_vealajrg := el1) (ev_ednqswlb := ec1)
        (he_grnsygdh := hr1) (hc_qgdlktwu := hc1) .. =>
      subst hr1
      obtain ⟨m1, rest1, heq1, hm1, hrest1⟩ := Core.RepList.cons_of_load hrm₁ ld1
      injection heq1 with hm1eq hr1eq; subst hm1eq; subst hr1eq
      cases m with
      | defn _ => obtain ⟨_, hv, -⟩ := hm1; injection hv with _ hc; exact absurd hc (by decide)
      | recr _ => obtain ⟨_, hv, -⟩ := hm1; injection hv with _ hc; exact absurd hc (by decide)
      | indc ind =>
        obtain ⟨iv1, hv1, _, _, hv1i, -, hct1⟩ := hm1
        injection hv1 with _ _ harg1; injection harg1 with hiv1; subst hiv1
        injection hv1i with _ _ hfields1
        simp only [List.cons.injEq, and_true] at hfields1
        obtain ⟨-, -, -, -, -, rfl⟩ := hfields1
        obtain ⟨hlen1, hh1⟩ := ctorList_length_spec el1 hct1
        subst hlen1; subst hh1
        match Obs.«KernelModeled::members_have_neg».obs ev₂ with
        | .Nil (ld_bolbylmd := ld2) .. => cases Core.RepList.nil_of_load hrm₂ ld2
        | .Cons_Indc_n1 (he_grnsygdh := hr2) .. => exact ⟨hr2.symm, Or.inr rfl⟩
        | .Cons_Indc_other (ld_bolbylmd := ld2) (ev_vealajrg := el2) (ev_ednqswlb := ec2)
            (hne_gmzyzqlk := hne2) (hc_ikoquvaw := hc2) .. =>
          obtain ⟨m2, rest2, heq2, hm2, -⟩ := Core.RepList.cons_of_load hrm₂ ld2
          injection heq2 with hm2eq _; subst hm2eq
          obtain ⟨iv2, hv2, _, _, hv2i, -, hct2⟩ := hm2
          injection hv2 with _ _ harg2; injection harg2 with hiv2; subst hiv2
          injection hv2i with _ _ hfields2
          simp only [List.cons.injEq, and_true] at hfields2
          obtain ⟨-, -, -, -, -, rfl⟩ := hfields2
          obtain ⟨hlen2, hh2⟩ := ctorList_length_spec el2 hct2
          subst hlen2; subst hh2
          have ⟨heq, _⟩ := ctors_have_neg_det hR₁ hR₂ hb₁B hb₂B hmsEq hbp₁ hbp₂ hms₁ hms₂
            (fun hc => hnc₁ (Core.collision_mono (fun c h => by rw [hc1]; simp [h]) hc))
            (Core.bounded_sub (fun c h => by rw [hc1]; simp [h]) hbd₁)
            (fun hc => hnc₂ (Core.collision_mono (fun c h => by rw [hc2]; simp [h]) hc))
            (Core.bounded_sub (fun c h => by rw [hc2]; simp [h]) hbd₂) ec1 ec2
          exact (hne2 heq.symm).elim
        | .Cons_other (ld_bolbylmd := ld2) (hne_aysnjoth := hne2) .. =>
          obtain ⟨m2, rest2, heq2, hm2, -⟩ := Core.RepList.cons_of_load hrm₂ ld2
          injection heq2 with hm2eq _; subst hm2eq
          obtain ⟨iv2, hv2, -⟩ := hm2
          exact (hne2 [iv2] rfl hv2).elim
    | .Cons_Indc_other (ld_bolbylmd := ld1) (ev_vealajrg := el1) (ev_ednqswlb := ec1)
        (hne_gmzyzqlk := hne1) (op_bchvmgub := op1) (ev_rmebdfbu := er1)
        (hc_ikoquvaw := hc1) .. =>
      obtain ⟨m1, rest1, heq1, hm1, hrest1⟩ := Core.RepList.cons_of_load hrm₁ ld1
      injection heq1 with hm1eq hr1eq; subst hm1eq; subst hr1eq
      cases m with
      | defn _ => obtain ⟨_, hv, -⟩ := hm1; injection hv with _ hc; exact absurd hc (by decide)
      | recr _ => obtain ⟨_, hv, -⟩ := hm1; injection hv with _ hc; exact absurd hc (by decide)
      | indc ind =>
        obtain ⟨iv1, hv1, _, _, hv1i, -, hct1⟩ := hm1
        injection hv1 with _ _ harg1; injection harg1 with hiv1; subst hiv1
        injection hv1i with _ _ hfields1
        simp only [List.cons.injEq, and_true] at hfields1
        obtain ⟨-, -, -, -, -, rfl⟩ := hfields1
        obtain ⟨hlen1, hh1⟩ := ctorList_length_spec el1 hct1
        subst hlen1; subst hh1
        match Obs.«KernelModeled::members_have_neg».obs ev₂ with
        | .Nil (ld_bolbylmd := ld2) .. => cases Core.RepList.nil_of_load hrm₂ ld2
        | .Cons_Indc_n1 (ld_bolbylmd := ld2) (ev_vealajrg := el2) (ev_ednqswlb := ec2)
            (hc_qgdlktwu := hc2) .. =>
          obtain ⟨m2, rest2, heq2, hm2, -⟩ := Core.RepList.cons_of_load hrm₂ ld2
          injection heq2 with hm2eq _; subst hm2eq
          obtain ⟨iv2, hv2, _, _, hv2i, -, hct2⟩ := hm2
          injection hv2 with _ _ harg2; injection harg2 with hiv2; subst hiv2
          injection hv2i with _ _ hfields2
          simp only [List.cons.injEq, and_true] at hfields2
          obtain ⟨-, -, -, -, -, rfl⟩ := hfields2
          obtain ⟨hlen2, hh2⟩ := ctorList_length_spec el2 hct2
          subst hlen2; subst hh2
          have ⟨heq, _⟩ := ctors_have_neg_det hR₁ hR₂ hb₁B hb₂B hmsEq hbp₁ hbp₂ hms₁ hms₂
            (fun hc => hnc₁ (Core.collision_mono (fun c h => by rw [hc1]; simp [h]) hc))
            (Core.bounded_sub (fun c h => by rw [hc1]; simp [h]) hbd₁)
            (fun hc => hnc₂ (Core.collision_mono (fun c h => by rw [hc2]; simp [h]) hc))
            (Core.bounded_sub (fun c h => by rw [hc2]; simp [h]) hbd₂) ec1 ec2
          exact (hne1 heq).elim
        | .Cons_Indc_other (ld_bolbylmd := ld2) (ev_vealajrg := el2) (ev_ednqswlb := ec2)
            (op_bchvmgub := op2) (ev_rmebdfbu := er2) (hc_ikoquvaw := hc2) .. =>
          obtain ⟨m2, rest2, heq2, hm2, hrest2⟩ := Core.RepList.cons_of_load hrm₂ ld2
          injection heq2 with hm2eq hr2eq; subst hm2eq; subst hr2eq
          obtain ⟨iv2, hv2, _, _, hv2i, -, hct2⟩ := hm2
          injection hv2 with _ _ harg2; injection harg2 with hiv2; subst hiv2
          injection hv2i with _ _ hfields2
          simp only [List.cons.injEq, and_true] at hfields2
          obtain ⟨-, -, -, -, -, rfl⟩ := hfields2
          obtain ⟨hlen2, hh2⟩ := ctorList_length_spec el2 hct2
          subst hlen2; subst hh2
          simp only [evalBinOp, Except.ok.injEq] at op1 op2
          subst op1; subst op2
          exact members_have_neg_det hR₁ hR₂ hb₁B hb₂B rem hmsEq
            (Bytes.repAddressRef_heapMono₂ addrTy ec1.heap_extends hbp₁)
            (Bytes.repAddressRef_heapMono₂ addrTy ec2.heap_extends hbp₂)
            (RepLinkedList.mono L1.repMutConst_heapMono₂ ec1.heap_extends hrest1)
            (RepLinkedList.mono L1.repMutConst_heapMono₂ ec2.heap_extends hrest2)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ec1.heap_extends hms₁)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ec2.heap_extends hms₂)
            (fun hc => hnc₁ (Core.collision_mono (fun c h => by rw [hc1]; simp [h]) hc))
            (Core.bounded_sub (fun c h => by rw [hc1]; simp [h]) hbd₁)
            (fun hc => hnc₂ (Core.collision_mono (fun c h => by rw [hc2]; simp [h]) hc))
            (Core.bounded_sub (fun c h => by rw [hc2]; simp [h]) hbd₂) er1 er2
        | .Cons_other (ld_bolbylmd := ld2) (hne_aysnjoth := hne2) .. =>
          obtain ⟨m2, rest2, heq2, hm2, -⟩ := Core.RepList.cons_of_load hrm₂ ld2
          injection heq2 with hm2eq _; subst hm2eq
          obtain ⟨iv2, hv2, -⟩ := hm2
          exact (hne2 [iv2] rfl hv2).elim
    | .Cons_other (ld_bolbylmd := ld1) (hne_aysnjoth := hne1) (op_isgyxdoe := op1)
        (ev_tuaompyc := er1) (hc_jqfriqni := hc1) .. =>
      obtain ⟨m1, rest1, heq1, hm1, hrest1⟩ := Core.RepList.cons_of_load hrm₁ ld1
      injection heq1 with hm1eq hr1eq; subst hm1eq; subst hr1eq
      match Obs.«KernelModeled::members_have_neg».obs ev₂ with
      | .Nil (ld_bolbylmd := ld2) .. => cases Core.RepList.nil_of_load hrm₂ ld2
      | .Cons_Indc_n1 (ld_bolbylmd := ld2) .. | .Cons_Indc_other (ld_bolbylmd := ld2) .. =>
        obtain ⟨m2, rest2, heq2, hm2, -⟩ := Core.RepList.cons_of_load hrm₂ ld2
        injection heq2 with hm2eq _; subst hm2eq
        cases m with
        | defn _ => obtain ⟨_, hv, -⟩ := hm2; injection hv with _ hc; exact absurd hc (by decide)
        | recr _ => obtain ⟨_, hv, -⟩ := hm2; injection hv with _ hc; exact absurd hc (by decide)
        | indc _ => obtain ⟨iv1, hv1, -⟩ := hm1; exact (hne1 [iv1] rfl hv1).elim
      | .Cons_other (ld_bolbylmd := ld2) (op_isgyxdoe := op2) (ev_tuaompyc := er2)
          (hc_jqfriqni := hc2) .. =>
        obtain ⟨m2, rest2, heq2, -, hrest2⟩ := Core.RepList.cons_of_load hrm₂ ld2
        injection heq2 with _ hr2eq; subst hr2eq
        simp only [evalBinOp, Except.ok.injEq] at op1 op2
        subst op1; subst op2
        exact members_have_neg_det hR₁ hR₂ hb₁B hb₂B rem hmsEq hbp₁ hbp₂ hrest1 hrest2 hms₁ hms₂
          (fun hc => hnc₁ (Core.collision_mono (fun c h => by rw [hc1]; simp [h]) hc))
          (Core.bounded_sub (fun c h => by rw [hc1]; simp [h]) hbd₁)
          (fun hc => hnc₂ (Core.collision_mono (fun c h => by rw [hc2]; simp [h]) hc))
          (Core.bounded_sub (fun c h => by rw [hc2]; simp [h]) hbd₂) er1 er2

private theorem repMutConst_toMutShape {h : Heap F} {m : Ixon.MutConst} {v : SourceValue F}
    (hm : L1.RepMutConst h m v) : Core.Specs.Callees.MutShape h m v := by
  cases m with
  | defn _ => obtain ⟨x, rfl, -⟩ := hm; exact ⟨x, rfl⟩
  | indc _ => obtain ⟨x, rfl, -⟩ := hm; exact ⟨x, rfl⟩
  | recr _ => obtain ⟨x, rfl, -⟩ := hm; exact ⟨x, rfl⟩

private theorem repList_mutShape_of_repMutConst {h : Heap F} {ms : List Ixon.MutConst}
    {v : SourceValue F} (hr : RepList L1.mutConstListEnum L1.RepMutConst h ms v) :
    Core.Specs.Callees.MembersRep h ms v := by
  induction hr with
  | nil cell => exact .nil cell
  | cons cell hhd _ ih => exact .cons cell (repMutConst_toMutShape hhd) ih

/-- Two bounded collision-free runs of `KernelModeled::block_has_neg_occ` on the same block
`B` (under stores `E₁`, `E₂` with `BlockCanonReadings`) agree on the returned bit (`0` or `1`). -/
theorem block_has_neg_occ_det {t : Ix.Kernel.RoleTable} {E₁ E₂ : Ixon.Env}
    {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {indTy₀ : Nat → KExpr} {ctorTy₀ : Nat → Nat → KExpr}
    (hR₁ : BlockCanonReadings t E₁ B cb ms indTy₀ ctorTy₀)
    (hR₂ : BlockCanonReadings t E₂ B cb ms indTy₀ ctorTy₀)
    {b₁ b₂ : Bytes.Address} {bp₁ bp₂ r₁ r₂ : SourceValue F} {h₁ h₁' h₂ h₂' : Heap F}
    {cs₁ cs₂ : List (Call F)}
    (hbp₁ : Bytes.RepAddressRef addrTy h₁ b₁ bp₁) (hb₁B : ixAddr b₁ = B)
    (hbp₂ : Bytes.RepAddressRef addrTy h₂ b₂ bp₂) (hb₂B : ixAddr b₂ = B)
    (hnc₁ : ¬ View.HashedCollision { env := E₁ } [] cs₁) (hbd₁ : Bounded cs₁)
    (hnc₂ : ¬ View.HashedCollision { env := E₂ } [] cs₂) (hbd₂ : Bounded cs₂)
    (ev₁ : ObsFn W "KernelModeled::block_has_neg_occ" [bp₁] h₁ r₁ h₁' cs₁)
    (ev₂ : ObsFn W "KernelModeled::block_has_neg_occ" [bp₂] h₂ r₂ h₂' cs₂) :
    r₁ = r₂ ∧ (r₁ = .field 0 ∨ r₁ = .field 1) := by
  have decodeBlk : ∀ {E : Ixon.Env}, recordOf E B = some cb →
      ∀ {b : Bytes.Address} {bp r : SourceValue F} {h m : Heap F} {cs : List (Call F)},
      Bytes.RepAddressRef addrTy h b bp → ixAddr b = B →
      ¬ View.HashedCollision { env := E } [] cs →
      ObsFn W "Ingress::load_verified_constant" [bp] h r m cs →
      Heap.Extends h m ∧ L1.RepConstant m cb r := by
    intro E hrec b bp r h m cs hbp hbB hnc ev
    obtain ⟨ext, bytes, c', -, hh, ha, hex, -, -, -, -, -, -, hrep⟩ :=
      L1.load_verified_constant_decode_bounded hbp ev
    obtain ⟨lc, hget, hdec⟩ := LoadedReads.recordOf_inv hrec
    have hb_eq : (⟨bytes.toArray⟩ : ByteArray) = lc.rawBytes :=
      Core.load_escape hget hnc _ hh (ha.trans hbB)
    rw [hb_eq, hdec] at hex
    have hc_eq : cb = c' := Except.ok.inj hex
    subst hc_eq
    exact ⟨ext, hrep⟩
  match Obs.«KernelModeled::block_has_neg_occ».obs ev₁ with
  | .other (ev_crkizsgj := el1) (hne_odfbwlsl := hne1) (hc_kjrxaxhl := hc1) .. =>
    obtain ⟨_, infoV, _, _, _, _, hv1, hinfo1, -⟩ := decodeBlk hR₁.record hbp₁ hb₁B
      (fun hc => hnc₁ (Core.collision_mono (fun c h => by rw [hc1]; simp [h]) hc)) el1
    injection hv1 with _ _ hargs1; injection hargs1 with hi1 _; subst hi1
    rw [hR₁.muts] at hinfo1
    obtain ⟨msP, hmsV, -⟩ := hinfo1
    exact (hne1 [msP] rfl hmsV).elim
  | .Muts (m_iqfdzjtt := m1l) (x_members := xm1) (ev_crkizsgj := el1) (ev_tuguejhl := eb1)
      (ev_omvqbspw := em1) (hc_sopanwkp := hc1) .. =>
    obtain ⟨ext1l, infoV1, _, _, _, _, hv1, hinfo1, -⟩ := decodeBlk hR₁.record hbp₁ hb₁B
      (fun hc => hnc₁ (Core.collision_mono (fun c h => by rw [hc1]; simp [h]) hc)) el1
    injection hv1 with _ _ hargs1; injection hargs1 with hi1 _; subst hi1
    rw [hR₁.muts] at hinfo1
    obtain ⟨msP1, hmsV1, hms1_rep⟩ := hinfo1
    injection hmsV1 with _ _ hmsA1; injection hmsA1 with hmsEq1; subst hmsEq1
    have hbp1' := Bytes.repAddressRef_heapMono₂ addrTy ext1l hbp₁
    have hmems1 : Core.Specs.Callees.MembersRep m1l ms.toList xm1 :=
      repList_mutShape_of_repMutConst hms1_rep
    obtain ⟨ext1b, as1, has1, hmap1⟩ := L1.build_recur_addrs_spec hmems1 hbp1' eb1
    match Obs.«KernelModeled::block_has_neg_occ».obs ev₂ with
    | .other (ev_crkizsgj := el2) (hne_odfbwlsl := hne2) (hc_kjrxaxhl := hc2) .. =>
      obtain ⟨_, infoV2, _, _, _, _, hv2, hinfo2, -⟩ := decodeBlk hR₂.record hbp₂ hb₂B
        (fun hc => hnc₂ (Core.collision_mono (fun c h => by rw [hc2]; simp [h]) hc)) el2
      injection hv2 with _ _ hargs2; injection hargs2 with hi2 _; subst hi2
      rw [hR₂.muts] at hinfo2
      obtain ⟨msP2, hmsV2, -⟩ := hinfo2
      exact (hne2 [msP2] rfl hmsV2).elim
    | .Muts (m_iqfdzjtt := m2l) (x_members := xm2) (ev_crkizsgj := el2) (ev_tuguejhl := eb2)
        (ev_omvqbspw := em2) (hc_sopanwkp := hc2) .. =>
      obtain ⟨ext2l, infoV2, _, _, _, _, hv2, hinfo2, -⟩ := decodeBlk hR₂.record hbp₂ hb₂B
        (fun hc => hnc₂ (Core.collision_mono (fun c h => by rw [hc2]; simp [h]) hc)) el2
      injection hv2 with _ _ hargs2; injection hargs2 with hi2 _; subst hi2
      rw [hR₂.muts] at hinfo2
      obtain ⟨msP2, hmsV2, hms2_rep⟩ := hinfo2
      injection hmsV2 with _ _ hmsA2; injection hmsA2 with hmsEq2; subst hmsEq2
      have hbp2' := Bytes.repAddressRef_heapMono₂ addrTy ext2l hbp₂
      have hmems2 : Core.Specs.Callees.MembersRep m2l ms.toList xm2 :=
        repList_mutShape_of_repMutConst hms2_rep
      obtain ⟨ext2b, as2, has2, hmap2⟩ := L1.build_recur_addrs_spec hmems2 hbp2' eb2
      have hmapEq : as1.map ixAddr = as2.map ixAddr := by
        rw [hmap1, hmap2, hb₁B, hb₂B]
      exact members_have_neg_det hR₁ hR₂ hb₁B hb₂B ms.toList hmapEq
        (Bytes.repAddressRef_heapMono₂ addrTy ext1b hbp1')
        (Bytes.repAddressRef_heapMono₂ addrTy ext2b hbp2')
        (RepLinkedList.mono L1.repMutConst_heapMono₂ ext1b hms1_rep)
        (RepLinkedList.mono L1.repMutConst_heapMono₂ ext2b hms2_rep)
        has1 has2
        (fun hc => hnc₁ (Core.collision_mono (fun c h => by rw [hc1]; simp [h]) hc))
        (Core.bounded_sub (fun c h => by rw [hc1]; simp [h]) hbd₁)
        (fun hc => hnc₂ (Core.collision_mono (fun c h => by rw [hc2]; simp [h]) hc))
        (Core.bounded_sub (fun c h => by rw [hc2]; simp [h]) hbd₂) em1 em2

private theorem field_sub_one_mul_eq_one_iff {a b : Nat} (ha : a < 72057594037927936)
    (hb : b < 72057594037927936)
    {x y v_sub r : SourceValue F} {h m1 m2 : Heap F} {cs1 cs2 : List (Call F)}
    (ez1 : ObsFn W "Fields::is_zero" [.field (a : F)] h x m1 cs1)
    (opsub : evalBinOp .sub (.field (b : F)) (.field 1) = .ok v_sub)
    (ez2 : ObsFn W "Fields::is_zero" [v_sub] m1 y m2 cs2)
    (opmul : evalBinOp .mul x y = .ok r) :
    r = .field (if a = 0 ∧ b = 1 then 1 else 0) ∧ m2 = h := by
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  obtain ⟨rfl, rfl⟩ := Lib.is_zero_field ez1
  simp only [evalBinOp, Except.ok.injEq] at opsub
  rw [← opsub] at ez2
  obtain ⟨rfl, rfl⟩ := Lib.is_zero_field ez2
  simp only [evalBinOp, Except.ok.injEq] at opmul
  rw [← opmul]
  refine ⟨?_, rfl⟩
  have ha0 : ((a : F) = 0) ↔ a = 0 := by
    constructor
    · intro h0
      have hv := congrArg ZMod.val h0
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv
      exact hv
    · intro h0; subst h0; simp
  have hb1 : ((b : F) - 1 = 0) ↔ b = 1 := by
    rw [sub_eq_zero]
    constructor
    · intro h1
      have hv := congrArg ZMod.val h1
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_one] at hv
      exact hv
    · intro h1; subst h1; simp
  by_cases h1 : a = 0 <;> by_cases h2 : b = 1 <;> simp [ha0, hb1, h1, h2]

private theorem ctor_ok_field_eq {cnl nl cnp np cnf : Nat}
    (hcnl : cnl < 4294967296) (hnl : nl < 4294967296)
    (hcnp : cnp < 72057594037927936) (hnp : np < 72057594037927936)
    (hcnf : cnf < 72057594037927936)
    {v1 x1 v2 y1 xy y2 y2' r : SourceValue F} {h m1 m2 m3 : Heap F} {cs1 cs2 cs3 : List (Call F)}
    (op1 : evalBinOp .sub (.field (cnl : F)) (.field (nl : F)) = .ok v1)
    (ez1 : ObsFn W "Fields::is_zero" [v1] h x1 m1 cs1)
    (op2 : evalBinOp .sub (.field (cnp : F)) (.field (np : F)) = .ok v2)
    (ez2 : ObsFn W "Fields::is_zero" [v2] m1 y1 m2 cs2)
    (opm1 : evalBinOp .mul x1 y1 = .ok xy)
    (ez3 : ObsFn W "Fields::is_zero" [.field (cnf : F)] m2 y2 m3 cs3)
    (op3 : evalBinOp .sub (.field 1) y2 = .ok y2')
    (opm2 : evalBinOp .mul xy y2' = .ok r) :
    r = .field (if cnl = nl ∧ cnp = np ∧ 0 < cnf then 1 else 0) ∧ m3 = h := by
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  simp only [evalBinOp, Except.ok.injEq] at op1 op2
  rw [← op1] at ez1
  rw [← op2] at ez2
  obtain ⟨rfl, rfl⟩ := Lib.is_zero_field ez1
  obtain ⟨rfl, rfl⟩ := Lib.is_zero_field ez2
  obtain ⟨rfl, rfl⟩ := Lib.is_zero_field ez3
  simp only [evalBinOp, Except.ok.injEq] at opm1 op3
  rw [← opm1, ← op3] at opm2
  simp only [evalBinOp, Except.ok.injEq] at opm2
  rw [← opm2]
  refine ⟨?_, rfl⟩
  have h1 : ((cnl : F) - (nl : F) = 0) ↔ cnl = nl := by
    rw [sub_eq_zero]
    constructor
    · intro h
      have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv; exact hv
    · intro h; subst h; rfl
  have h2 : ((cnp : F) - (np : F) = 0) ↔ cnp = np := by
    rw [sub_eq_zero]
    constructor
    · intro h
      have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv; exact hv
    · intro h; subst h; rfl
  have h3 : ((cnf : F) = 0) ↔ cnf = 0 := by
    constructor
    · intro h
      have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv; exact hv
    · intro h; subst h; simp
  by_cases ha : cnl = nl <;> by_cases hb : cnp = np <;> by_cases hc : cnf = 0 <;>
    simp [h1, h2, h3, ha, hb, hc, Nat.pos_iff_ne_zero]

private theorem eval_sub_one_bit {y r : SourceValue F}
    (hy : y = .field 0 ∨ y = .field 1) (op : evalBinOp .sub (.field 1) y = .ok r) :
    (y = .field 0 ∧ r = .field 1) ∨ (y = .field 1 ∧ r = .field 0) := by
  rcases hy with rfl | rfl
  · simp only [evalBinOp, sub_zero, Except.ok.injEq] at op; exact Or.inl ⟨rfl, op.symm⟩
  · simp only [evalBinOp, sub_self, Except.ok.injEq] at op; exact Or.inr ⟨rfl, op.symm⟩

private theorem level_isNeverZero_iff_eval_zero (l : KLevel) :
    l.isNeverZero = true ↔ 0 < l.eval (fun _ => 0) := by
  induction l with
  | zero => simp [Ix.Kernel.Level.isNeverZero, Ix.Kernel.Level.eval]
  | param _ => simp [Ix.Kernel.Level.isNeverZero, Ix.Kernel.Level.eval]
  | succ _ _ => simp [Ix.Kernel.Level.isNeverZero, Ix.Kernel.Level.eval]
  | max a b iha ihb =>
    simp [Ix.Kernel.Level.isNeverZero, Ix.Kernel.Level.eval, iha, ihb]
  | imax a b iha ihb =>
    simp only [Ix.Kernel.Level.isNeverZero, Ix.Kernel.Level.eval, ihb]
    by_cases hb : b.eval (fun _ => 0) = 0
    · simp [hb]
    · simp [hb, Nat.pos_iff_ne_zero]

private theorem eval_substLevel_range {n : Nat} (l : KLevel) (φ : Ix.Kernel.LevelParam → Nat) :
    (substLevel l ((List.range n).map Ix.Kernel.Level.param)).eval φ = l.eval φ := by
  induction l with
  | zero => rfl
  | succ u ih => simp [substLevel, Ix.Kernel.Level.eval, ih]
  | max a b iha ihb =>
    simp [substLevel, IxVM.Refinement.KernelLevels.eval_levelMax, Ix.Kernel.Level.eval, iha, ihb]
  | imax a b iha ihb =>
    simp [substLevel, IxVM.Refinement.KernelLevels.eval_levelIMax, Ix.Kernel.Level.eval, iha, ihb]
  | param p =>
    simp only [substLevel]
    by_cases hp : p < n
    · simp [List.getElem?_map, hp]
    · have hnone : ((List.range n).map Ix.Kernel.Level.param)[p]? = none := by
        simp [List.getElem?_eq_none, hp]
      rw [hnone]; rfl

private theorem isNeverZero_of_substLevel_range {n : Nat} {l : KLevel}
    (h : (substLevel l ((List.range n).map Ix.Kernel.Level.param)).isNeverZero = true) :
    l.isNeverZero = true := by
  rw [level_isNeverZero_iff_eval_zero] at h ⊢
  rwa [eval_substLevel_range] at h

private theorem stripPis_sort_of_eraseMeta_eq :
    ∀ (n : Nat) {R E : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {u : KLevel},
      R.eraseMeta = E.eraseMeta →
      R.stripPis n = some (bs, .sort u) →
      ∃ bs', E.stripPis n = some (bs', .sort u)
  | 0, R, E, bs, u, he, hs => by
    simp only [Ix.Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    cases E with
    | sort v =>
      simp only [Ix.Kernel.Expr.eraseMeta, Ix.Kernel.Expr.sort.injEq] at he
      subst he
      exact ⟨[], rfl⟩
    | _ => simp [Ix.Kernel.Expr.eraseMeta] at he
  | n + 1, R, E, bs, u, he, hs => by
    cases R with
    | forallE d b m =>
      cases E with
      | forallE d' b' m' =>
        simp only [Ix.Kernel.Expr.eraseMeta, Ix.Kernel.Expr.forallE.injEq] at he
        simp only [Ix.Kernel.Expr.stripPis] at hs ⊢
        cases h : b.stripPis n with
        | none => rw [h] at hs; simp at hs
        | some p =>
          rw [h] at hs
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨bs', hbs'⟩ := stripPis_sort_of_eraseMeta_eq n he.2.1 (by rw [← hs.2]; exact h)
          exact ⟨(d', m') :: bs', by rw [hbs']; rfl⟩
      | _ => simp [Ix.Kernel.Expr.eraseMeta] at he
    | _ => simp [Ix.Kernel.Expr.stripPis] at hs

/-- **Syntactic facts extracted from `modeled_proj_eligible = 1`**: the member has 0 indices, 1
constructor, syntactic never-zero result sort `indTy₀ i.val`, matching constructor universe and
parameter counts, and at least 1 field. -/
theorem modeled_proj_eligible_one_facts {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {indTy₀ : Nat → KExpr} {ctorTy₀ : Nat → Nat → KExpr}
    (hR : BlockCanonReadings t E B cb ms indTy₀ ctorTy₀)
    {b : Bytes.Address} {bp : SourceValue F} {i : F} {h h' : Heap F} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbd : Bounded cs)
    (hb : Bytes.RepAddressRef addrTy h b bp) (hbB : ixAddr b = B)
    (ev : ObsFn W "KernelModeled::modeled_proj_eligible" [bp, .field i] h (.field 1) h' cs) :
    ∃ (ind : Ixon.Inductive) (ct : Ixon.Constructor) (bs : List (KExpr × Ix.Kernel.BinderMeta))
      (u : KLevel),
      ms[i.val]? = some (.indc ind) ∧ ind.ctors[0]? = some ct ∧
      ind.indices.toNat = 0 ∧ ind.ctors.size = 1 ∧
      ct.lvls.toNat = ind.lvls.toNat ∧ ct.params.toNat = ind.params.toNat ∧ 0 < ct.fields.toNat ∧
      (indTy₀ i.val).stripPis ind.params.toNat = some (bs, .sort u) ∧ u.isNeverZero = true := by
  match Obs.«KernelModeled::modeled_proj_eligible».obs ev with
  | .Induct_n1_n1_Ctor_n1 (ev_tliihgbk := ei) (ld_bolbylmd := ldi)
      (ev_mtlatnxp := ezni) (op_osmnocjv := opsub1) (ev_frqifqhn := eznc) (op_ejqwptvm := opm1)
      (ev_idsjtbpn := elvls) (ev_fymcedtv := etsn) (ev_gspektsu := ec) (ld_teypdjah := ldc)
      (op_cicnbfzu := opcnl) (ev_zytstztu := ezcnl) (op_hjgzcroj := opcnp) (ev_wfmqflen := ezcnp)
      (op_bnykfhku := opm2) (ev_csdrfiwf := ezcnf) (op_wljsdgui := opsub2) (op_tbwdtilp := opm3)
      (hc_cikgdszz := hc) .. =>
    obtain ⟨ind, raw, tyP, blkP, hmem, hnl, hnp, hni, hnc_lt, hldi, -, herase, hRawI⟩ :=
      get_ci_iprj_rawOExact hR
        (fun hcol => hnc (Core.collision_mono (fun c h => by rw [hc]; simp [h]) hcol))
        (Core.bounded_sub (fun c h => by rw [hc]; simp [h]) hbd) hb hbB ei
    rw [hldi] at ldi; injection ldi with hvi
    simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hvi
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -, -, -⟩ := hvi
    obtain ⟨h1eq, hheq1⟩ := field_sub_one_mul_eq_one_iff hni hnc_lt ezni opsub1 eznc opm1
    have hni0_nc1 : ind.indices.toNat = 0 ∧ ind.ctors.size = 1 := by
      by_contra hnot; rw [ite_eq_right hnot] at h1eq; exact absurd (Value.field.inj h1eq) (by decide)
    have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
    have hlvls := Decl.build_param_lvls_range_spec
      (by rw [ZMod.val_natCast_of_lt (by omega)]; exact hnl) elvls
    rw [ZMod.val_natCast_of_lt (by omega)] at hlvls
    have hRawI' := hRawI.mono (hheq1 ▸ elvls.heap_extends)
    have htsn := type_sort_never_rawOExact (n := ind.params.toNat) (by omega) hRawI' hlvls
      (Core.bounded_sub (fun c h => by rw [hc]; simp [h]) hbd) etsn
    have htsn_true : typeSortNeverNoLet raw ind.params.toNat
        ((List.range ind.lvls.toNat).map Ix.Kernel.Level.param) = true := by
      cases h : typeSortNeverNoLet raw ind.params.toNat
          ((List.range ind.lvls.toNat).map Ix.Kernel.Level.param)
      · rw [h] at htsn; exact absurd (Value.field.inj htsn) (by decide)
      · rfl
    obtain ⟨bsR, u, hstripR, hnz'⟩ := (typeSortNeverNoLet_eq_true_iff ..).mp htsn_true
    have hnz : u.isNeverZero = true := isNeverZero_of_substLevel_range hnz'
    obtain ⟨bs, hstrip⟩ := stripPis_sort_of_eraseMeta_eq ind.params.toNat herase hstripR
    have ext_to_c : Heap.Extends h _ :=
      ei.heap_extends.trans ((hheq1 ▸ elvls.heap_extends).trans etsn.heap_extends)
    obtain ⟨ind', ct, _, _, _, hmem', hct, hcnl, hcnp, hcnf, hldc, -, -⟩ :=
      get_ci_cprj_rawOExact hR
        (fun hcol => hnc (Core.collision_mono (fun c h => by rw [hc]; simp [h]) hcol))
        (Core.bounded_sub (fun c h => by rw [hc]; simp [h]) hbd)
        (Bytes.repAddressRef_heapMono₂ addrTy ext_to_c hb) hbB ec
    have eind : ind = ind' := Ixon.MutConst.indc.inj (Option.some.inj (hmem.symm.trans hmem'))
    subst eind
    rw [ZMod.val_zero] at hct
    rw [hldc] at ldc; injection ldc with hvc
    simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hvc
    obtain ⟨rfl, -, -, -, -, rfl, rfl, -⟩ := hvc
    obtain ⟨h2eq, -⟩ := ctor_ok_field_eq hcnl hnl hcnp hnp hcnf
      opcnl ezcnl opcnp ezcnp opm2 ezcnf opsub2 opm3
    have hc_ok : ct.lvls.toNat = ind.lvls.toNat ∧ ct.params.toNat = ind.params.toNat ∧
        0 < ct.fields.toNat := by
      by_contra hnot; rw [ite_eq_right hnot] at h2eq; exact absurd (Value.field.inj h2eq) (by decide)
    exact ⟨ind, ct, bs, u, hmem, hct, hni0_nc1.1, hni0_nc1.2, hc_ok.1, hc_ok.2.1, hc_ok.2.2,
      hstrip, hnz⟩
  | .Induct_n1_n1_Ctor_other (he_ylswoobp := hr) ..
  | .Induct_n1_n1_other (he_agycgyff := hr) ..
  | .Induct_n1_other (he_mlzuxdhu := hr) ..
  | .Induct_other (he_pospgcez := hr) ..
  | .other (he_vpckpvxl := hr) .. =>
    exact absurd (Value.field.inj hr) (by decide)

/-- **Two-run determinism of `KernelModeled::modeled_proj_eligible`**: any two bounded
collision-free runs on the same block `B` and member index `i` — even across different stores
`E₁`, `E₂` sharing `BlockCanonReadings` — return the exact same bit (`0` or `1`). -/
theorem modeled_proj_eligible_det {t : Ix.Kernel.RoleTable} {E₁ E₂ : Ixon.Env}
    {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {indTy₀ : Nat → KExpr} {ctorTy₀ : Nat → Nat → KExpr}
    (hR₁ : BlockCanonReadings t E₁ B cb ms indTy₀ ctorTy₀)
    (hR₂ : BlockCanonReadings t E₂ B cb ms indTy₀ ctorTy₀)
    {b₁ b₂ : Bytes.Address} {bp₁ bp₂ r₁ r₂ : SourceValue F} {i : F}
    {h₁ h₁' h₂ h₂' : Heap F} {cs₁ cs₂ : List (Call F)}
    (hbp₁ : Bytes.RepAddressRef addrTy h₁ b₁ bp₁) (hb₁B : ixAddr b₁ = B)
    (hbp₂ : Bytes.RepAddressRef addrTy h₂ b₂ bp₂) (hb₂B : ixAddr b₂ = B)
    (hnc₁ : ¬ View.HashedCollision { env := E₁ } [] cs₁) (hbd₁ : Bounded cs₁)
    (hnc₂ : ¬ View.HashedCollision { env := E₂ } [] cs₂) (hbd₂ : Bounded cs₂)
    (ev₁ : ObsFn W "KernelModeled::modeled_proj_eligible" [bp₁, .field i] h₁ r₁ h₁' cs₁)
    (ev₂ : ObsFn W "KernelModeled::modeled_proj_eligible" [bp₂, .field i] h₂ r₂ h₂' cs₂) :
    r₁ = r₂ ∧ (r₁ = .field 0 ∨ r₁ = .field 1) := by
  -- Helper: classify a single `modeled_proj_eligible` run into either `Induct_n1_n1_Ctor_n1`
  -- (producing `block_has_neg_occ`) or `r = .field 0` with one of the pure guards failing.
  have classify : ∀ {E : Ixon.Env} (hR : BlockCanonReadings t E B cb ms indTy₀ ctorTy₀)
      {b : Bytes.Address} {bp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
      (hbp : Bytes.RepAddressRef addrTy h b bp) (hbB : ixAddr b = B)
      (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbd : Bounded cs)
      (ev : ObsFn W "KernelModeled::modeled_proj_eligible" [bp, .field i] h r h' cs),
      ∃ (ind : Ixon.Inductive) (raw : KExpr), ms[i.val]? = some (.indc ind) ∧
        L1.canonicalRawAnnotation cb (List.range ind.lvls.toNat)
          ((L1.mutsRootOffset ms.toList i.val : Nat) : F) ind.typ (indTy₀ i.val) = some raw ∧
      ((ind.indices.toNat = 0 ∧ ind.ctors.size = 1 ∧
        typeSortNeverNoLet raw ind.params.toNat
          ((List.range ind.lvls.toNat).map Ix.Kernel.Level.param) = true ∧
        ∃ ct, ind.ctors[0]? = some ct ∧ ct.lvls.toNat = ind.lvls.toNat ∧
          ct.params.toNat = ind.params.toNat ∧ 0 < ct.fields.toNat ∧
        ∃ (m : Heap F) (y : SourceValue F) (csb : List (Call F)),
          Heap.Extends h m ∧
          (∀ c ∈ csb, c ∈ cs) ∧
          ObsFn W "KernelModeled::block_has_neg_occ" [bp] m y h' csb ∧
          evalBinOp .sub (.field 1) y = .ok r) ∨
       (r = .field 0 ∧
        ¬ (ind.indices.toNat = 0 ∧ ind.ctors.size = 1 ∧
           typeSortNeverNoLet raw ind.params.toNat
             ((List.range ind.lvls.toNat).map Ix.Kernel.Level.param) = true ∧
           ∃ ct, ind.ctors[0]? = some ct ∧ ct.lvls.toNat = ind.lvls.toNat ∧
             ct.params.toNat = ind.params.toNat ∧ 0 < ct.fields.toNat))) := by
    intro E hR b bp r h h' cs hbp hbB hnc hbd ev
    match Obs.«KernelModeled::modeled_proj_eligible».obs ev with
    | .Induct_n1_n1_Ctor_n1 (ev_tliihgbk := ei) (ld_bolbylmd := ldi)
        (ev_mtlatnxp := ezni) (op_osmnocjv := opsub1) (ev_frqifqhn := eznc) (op_ejqwptvm := opm1)
        (ev_idsjtbpn := elvls) (ev_fymcedtv := etsn) (ev_gspektsu := ec) (ld_teypdjah := ldc)
        (op_cicnbfzu := opcnl) (ev_zytstztu := ezcnl) (op_hjgzcroj := opcnp) (ev_wfmqflen := ezcnp)
        (op_bnykfhku := opm2) (ev_csdrfiwf := ezcnf) (op_wljsdgui := opsub2) (op_tbwdtilp := opm3)
        (ev_ppyohbpe := ebno) (op_adcmgklu := opsubr) (hc_cikgdszz := hc) .. =>
      obtain ⟨ind, raw, _, _, hmem, hnl, hnp, hni, hnc_lt, hldi, hcan, -, hRawI⟩ :=
        get_ci_iprj_rawOExact hR
          (fun hcol => hnc (Core.collision_mono (fun c h => by rw [hc]; simp [h]) hcol))
          (Core.bounded_sub (fun c h => by rw [hc]; simp [h]) hbd) hbp hbB ei
      rw [hldi] at ldi; injection ldi with hvi
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hvi
      obtain ⟨rfl, rfl, rfl, rfl, rfl, -, -, -⟩ := hvi
      obtain ⟨h1eq, hheq1⟩ := field_sub_one_mul_eq_one_iff hni hnc_lt ezni opsub1 eznc opm1
      have hni0_nc1 : ind.indices.toNat = 0 ∧ ind.ctors.size = 1 := by
        by_contra hnot; rw [ite_eq_right hnot] at h1eq; exact absurd (Value.field.inj h1eq) (by decide)
      have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
      have hlvls := Decl.build_param_lvls_range_spec
        (by rw [ZMod.val_natCast_of_lt (by omega)]; exact hnl) elvls
      rw [ZMod.val_natCast_of_lt (by omega)] at hlvls
      have htsn := type_sort_never_rawOExact (n := ind.params.toNat) (by omega)
        (hRawI.mono (hheq1 ▸ elvls.heap_extends)) hlvls
        (Core.bounded_sub (fun c h => by rw [hc]; simp [h]) hbd) etsn
      have htsn_true : typeSortNeverNoLet raw ind.params.toNat
          ((List.range ind.lvls.toNat).map Ix.Kernel.Level.param) = true := by
        cases h' : typeSortNeverNoLet raw ind.params.toNat
            ((List.range ind.lvls.toNat).map Ix.Kernel.Level.param)
        · rw [h'] at htsn; exact absurd (Value.field.inj htsn) (by decide)
        · rfl
      have ext_c : Heap.Extends h _ :=
        ei.heap_extends.trans ((hheq1 ▸ elvls.heap_extends).trans etsn.heap_extends)
      obtain ⟨ind', ct, _, _, _, hmem', hct, hcnl, hcnp, hcnf, hldc, -, -⟩ :=
        get_ci_cprj_rawOExact hR
          (fun hcol => hnc (Core.collision_mono (fun c h => by rw [hc]; simp [h]) hcol))
          (Core.bounded_sub (fun c h => by rw [hc]; simp [h]) hbd)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_c hbp) hbB ec
      have eind : ind = ind' := Ixon.MutConst.indc.inj (Option.some.inj (hmem.symm.trans hmem'))
      subst eind
      rw [ZMod.val_zero] at hct
      rw [hldc] at ldc; injection ldc with hvc
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hvc
      obtain ⟨rfl, -, -, -, -, rfl, rfl, -⟩ := hvc
      obtain ⟨h2eq, hheq2⟩ := ctor_ok_field_eq hcnl hnl hcnp hnp hcnf
        opcnl ezcnl opcnp ezcnp opm2 ezcnf opsub2 opm3
      have hc_ok : ct.lvls.toNat = ind.lvls.toNat ∧ ct.params.toNat = ind.params.toNat ∧
          0 < ct.fields.toNat := by
        by_contra hnot; rw [ite_eq_right hnot] at h2eq; exact absurd (Value.field.inj h2eq) (by decide)
      refine ⟨ind, raw, hmem, hcan, Or.inl ⟨hni0_nc1.1, hni0_nc1.2, htsn_true, ct, hct, hc_ok.1,
        hc_ok.2.1, hc_ok.2.2, _, _, _, ?_, fun c hc' => by rw [hc]; simp [hc'], ebno, opsubr⟩⟩
      exact ext_c.trans (hheq2 ▸ ec.heap_extends)
    | .Induct_n1_n1_Ctor_other (ev_tliihgbk := ei) (ld_bolbylmd := ldi)
        (ev_mtlatnxp := ezni) (op_osmnocjv := opsub1) (ev_frqifqhn := eznc) (op_ejqwptvm := opm1)
        (ev_idsjtbpn := elvls) (ev_fymcedtv := etsn) (ev_gspektsu := ec) (ld_teypdjah := ldc)
        (op_cicnbfzu := opcnl) (ev_zytstztu := ezcnl) (op_hjgzcroj := opcnp) (ev_wfmqflen := ezcnp)
        (op_bnykfhku := opm2) (ev_csdrfiwf := ezcnf) (op_wljsdgui := opsub2) (op_tbwdtilp := opm3)
        (hne_saepnfjz := hne) (he_ylswoobp := hr) (hc_fkxcinlh := hc) .. =>
      subst hr
      obtain ⟨ind, raw, _, _, hmem, hnl, hnp, hni, hnc_lt, hldi, hcan, -, -⟩ :=
        get_ci_iprj_rawOExact hR
          (fun hcol => hnc (Core.collision_mono (fun c h => by rw [hc]; simp [h]) hcol))
          (Core.bounded_sub (fun c h => by rw [hc]; simp [h]) hbd) hbp hbB ei
      rw [hldi] at ldi; injection ldi with hvi
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hvi
      obtain ⟨rfl, rfl, rfl, rfl, rfl, -, -, -⟩ := hvi
      obtain ⟨-, hheq1⟩ := field_sub_one_mul_eq_one_iff hni hnc_lt ezni opsub1 eznc opm1
      have ext_c : Heap.Extends h _ :=
        ei.heap_extends.trans ((hheq1 ▸ elvls.heap_extends).trans etsn.heap_extends)
      obtain ⟨ind', ct, _, _, _, hmem', hct, hcnl, hcnp, hcnf, hldc, -, -⟩ :=
        get_ci_cprj_rawOExact hR
          (fun hcol => hnc (Core.collision_mono (fun c h => by rw [hc]; simp [h]) hcol))
          (Core.bounded_sub (fun c h => by rw [hc]; simp [h]) hbd)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_c hbp) hbB ec
      have eind : ind = ind' := Ixon.MutConst.indc.inj (Option.some.inj (hmem.symm.trans hmem'))
      subst eind
      rw [ZMod.val_zero] at hct
      rw [hldc] at ldc; injection ldc with hvc
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hvc
      obtain ⟨rfl, -, -, -, -, rfl, rfl, -⟩ := hvc
      obtain ⟨h2eq, -⟩ := ctor_ok_field_eq hcnl hnl hcnp hnp hcnf
        opcnl ezcnl opcnp ezcnp opm2 ezcnf opsub2 opm3
      refine ⟨ind, raw, hmem, hcan, Or.inr ⟨rfl, fun ⟨_, _, _, ct', hct', h1, h2, h3⟩ => ?_⟩⟩
      have ect : ct = ct' := Option.some.inj (hct.symm.trans hct')
      subst ect
      rw [ite_eq_left ⟨h1, h2, h3⟩] at h2eq
      exact hne h2eq
    | .Induct_n1_n1_other (ev_tliihgbk := ei) (ld_bolbylmd := ldi)
        (ev_mtlatnxp := ezni) (op_osmnocjv := opsub1) (ev_frqifqhn := eznc) (op_ejqwptvm := opm1)
        (ev_idsjtbpn := elvls) (ev_fymcedtv := etsn) (ev_gspektsu := ec) (ld_teypdjah := ldc)
        (hne_garxcwhx := hne) (hc_ndpzhnsg := hc) .. =>
      obtain ⟨ind, _, _, _, hmem, _, _, hni, hnc_lt, hldi, -, -, -⟩ :=
        get_ci_iprj_rawOExact hR
          (fun hcol => hnc (Core.collision_mono (fun c h => by rw [hc]; simp [h]) hcol))
          (Core.bounded_sub (fun c h => by rw [hc]; simp [h]) hbd) hbp hbB ei
      rw [hldi] at ldi; injection ldi with hvi
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hvi
      obtain ⟨rfl, rfl, rfl, rfl, rfl, -, -, -⟩ := hvi
      obtain ⟨-, hheq1⟩ := field_sub_one_mul_eq_one_iff hni hnc_lt ezni opsub1 eznc opm1
      have ext_c : Heap.Extends h _ :=
        ei.heap_extends.trans ((hheq1 ▸ elvls.heap_extends).trans etsn.heap_extends)
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hldc, -, -⟩ :=
        get_ci_cprj_rawOExact hR
          (fun hcol => hnc (Core.collision_mono (fun c h => by rw [hc]; simp [h]) hcol))
          (Core.bounded_sub (fun c h => by rw [hc]; simp [h]) hbd)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_c hbp) hbB ec
      rw [hldc] at ldc; injection ldc with hv
      exact (hne _ rfl hv.symm).elim
    | .Induct_n1_other (ev_tliihgbk := ei) (ld_bolbylmd := ldi)
        (ev_mtlatnxp := ezni) (op_osmnocjv := opsub1) (ev_frqifqhn := eznc) (op_ejqwptvm := opm1)
        (ev_idsjtbpn := elvls) (ev_fymcedtv := etsn) (hne_gdjfpofg := hne)
        (he_mlzuxdhu := hr) (hc_laomofds := hc) .. =>
      subst hr
      obtain ⟨ind, raw, _, _, hmem, hnl, hnp, hni, hnc_lt, hldi, hcan, -, hRawI⟩ :=
        get_ci_iprj_rawOExact hR
          (fun hcol => hnc (Core.collision_mono (fun c h => by rw [hc]; simp [h]) hcol))
          (Core.bounded_sub (fun c h => by rw [hc]; simp [h]) hbd) hbp hbB ei
      rw [hldi] at ldi; injection ldi with hvi
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hvi
      obtain ⟨rfl, rfl, rfl, rfl, rfl, -, -, -⟩ := hvi
      obtain ⟨-, hheq1⟩ := field_sub_one_mul_eq_one_iff hni hnc_lt ezni opsub1 eznc opm1
      have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
      have hlvls := Decl.build_param_lvls_range_spec
        (by rw [ZMod.val_natCast_of_lt (by omega)]; exact hnl) elvls
      rw [ZMod.val_natCast_of_lt (by omega)] at hlvls
      have htsn := type_sort_never_rawOExact (n := ind.params.toNat) (by omega)
        (hRawI.mono (hheq1 ▸ elvls.heap_extends)) hlvls
        (Core.bounded_sub (fun c h => by rw [hc]; simp [h]) hbd) etsn
      refine ⟨ind, raw, hmem, hcan, Or.inr ⟨rfl, fun ⟨_, _, ht, _⟩ => ?_⟩⟩
      rw [ht] at htsn; exact hne htsn
    | .Induct_other (ev_tliihgbk := ei) (ld_bolbylmd := ldi)
        (ev_mtlatnxp := ezni) (op_osmnocjv := opsub1) (ev_frqifqhn := eznc) (op_ejqwptvm := opm1)
        (hne_vjkuyern := hne) (he_pospgcez := hr) (hc_srgjgvgd := hc) .. =>
      subst hr
      obtain ⟨ind, raw, _, _, hmem, _, _, hni, hnc_lt, hldi, hcan, -, -⟩ :=
        get_ci_iprj_rawOExact hR
          (fun hcol => hnc (Core.collision_mono (fun c h => by rw [hc]; simp [h]) hcol))
          (Core.bounded_sub (fun c h => by rw [hc]; simp [h]) hbd) hbp hbB ei
      rw [hldi] at ldi; injection ldi with hvi
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hvi
      obtain ⟨rfl, rfl, rfl, rfl, rfl, -, -, -⟩ := hvi
      obtain ⟨h1eq, -⟩ := field_sub_one_mul_eq_one_iff hni hnc_lt ezni opsub1 eznc opm1
      refine ⟨ind, raw, hmem, hcan, Or.inr ⟨rfl, fun ⟨h1, h2, _⟩ => ?_⟩⟩
      rw [ite_eq_left ⟨h1, h2⟩] at h1eq; exact hne h1eq
    | .other (ev_tliihgbk := ei) (ld_bolbylmd := ldi) (hne_aubkumng := hne)
        (hc_kjrxaxhl := hc) .. =>
      obtain ⟨_, _, _, _, _, _, _, _, _, hldi, -, -, -⟩ :=
        get_ci_iprj_rawOExact hR
          (fun hcol => hnc (Core.collision_mono (fun c h => by rw [hc]; simp [h]) hcol))
          (Core.bounded_sub (fun c h => by rw [hc]; simp [h]) hbd) hbp hbB ei
      rw [hldi] at ldi; injection ldi with hv
      exact (hne _ rfl hv.symm).elim
  obtain ⟨ind1, raw1, hm1, hcan1, hcls1⟩ := classify hR₁ hbp₁ hb₁B hnc₁ hbd₁ ev₁
  obtain ⟨ind2, raw2, hm2, hcan2, hcls2⟩ := classify hR₂ hbp₂ hb₂B hnc₂ hbd₂ ev₂
  have eind : ind1 = ind2 := Ixon.MutConst.indc.inj (Option.some.inj (hm1.symm.trans hm2))
  subst eind
  have eraw : raw1 = raw2 := Option.some.inj (hcan1.symm.trans hcan2)
  subst eraw
  rcases hcls1 with ⟨h1, h2, h3, ct1, hct1, h4, h5, h6, m1, y1, csb1, ext1, hsub1, ebno1, opsub1⟩ |
      ⟨rfl, hnot1⟩
  · rcases hcls2 with ⟨_, _, _, _, _, _, _, _, m2, y2, csb2, ext2, hsub2, ebno2, opsub2⟩ |
        ⟨_, hnot2⟩
    · obtain ⟨hyEq, hyBit⟩ := block_has_neg_occ_det hR₁ hR₂
        (Bytes.repAddressRef_heapMono₂ addrTy ext1 hbp₁) hb₁B
        (Bytes.repAddressRef_heapMono₂ addrTy ext2 hbp₂) hb₂B
        (fun hc => hnc₁ (Core.collision_mono hsub1 hc)) (Core.bounded_sub hsub1 hbd₁)
        (fun hc => hnc₂ (Core.collision_mono hsub2 hc)) (Core.bounded_sub hsub2 hbd₂) ebno1 ebno2
      subst hyEq
      rcases eval_sub_one_bit hyBit opsub1 with ⟨ry, hr1⟩ | ⟨ry, hr1⟩
      · subst ry; subst hr1
        simp only [evalBinOp, sub_zero, Except.ok.injEq] at opsub2
        exact ⟨opsub2, Or.inr rfl⟩
      · subst ry; subst hr1
        simp only [evalBinOp, sub_self, Except.ok.injEq] at opsub2
        exact ⟨opsub2, Or.inl rfl⟩
    · exact (hnot2 ⟨h1, h2, h3, ct1, hct1, h4, h5, h6⟩).elim
  · rcases hcls2 with ⟨h1, h2, h3, ct2, hct2, h4, h5, h6, _⟩ | ⟨rfl, _⟩
    · exact (hnot1 ⟨h1, h2, h3, ct2, hct2, h4, h5, h6⟩).elim
    · exact ⟨rfl, Or.inl rfl⟩

end IxVM.Refinement.Typing.FamilyAlias
