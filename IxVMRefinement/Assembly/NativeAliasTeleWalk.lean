import IxVMRefinement.Decl.NativeFront
import IxVMRefinement.Assembly.TypingRecLateElim
import IxVMRefinement.Infer.Close
import IxVMRefinement.Core.CallHeaps

/-! # The telescope a former declared at a definition is read at, as the circuit builds it

`KernelCheck::former_tele_at(rc, ty, k, types, s)` keeps a syntactic `Forall` cell of `ty`,
head-normalizes (`KernelWhnf::whnf`) a position that is not one, and after `k` binders allocates
`Srt(s)`. The term is built on the heap, not loaded, so its exact reading is read off the cells:

* pointer-level shapes: `ForallCells` (`m` syntactic `Forall` cells), `TeleShape` (`n` `Forall`
  cells, then the sort cell `Srt(s)`), `TeleCells` (two spines whose first `m` `Forall` cells carry
  the same domain and binder-data pointers);
* `former_tele_at_spec`: at a scoped context, the built term is represented (`Tm`), has the
  telescope's shape, and repeats the declared type's first `m ≤ k` cells where those are
  syntactic `Forall` cells;
* `check_param_agreement_go_cells`, `check_inductive_shape_ctors_param_cells`: the constructor
  loop, at a family with a constructor, walks the declared type's first `nP` cells as syntactic
  `Forall` cells;
* exact readings: `Tm.exactify` (a represented pointer has an exact reading), `TmExact.det` (it
  is unique), `TeleShape.stripPis_exact`, `TeleCells.prefixEq` and `PrefixEq.openPisAtFvars`
  (two exact readings that share their first `m` cells open their first `m` binders to the same
  variables).
-/

universe u

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (ConstantInfo ConstantVal Declaration Expr Level LevelParam)
open Ix.Kernel.Rules (Red DefEq Infer)

/-! ## Pointer-level shapes -/

/-- `m` syntactic `Forall` cells from `p`, each the body of the one before. -/
def ForallCells (h : Heap F) : Nat → SourceValue F → Prop
  | 0, _ => True
  | m + 1, p => ∃ d b bm, loadValue h p = .ok (.construct kexprEnum "Forall" [d, b, bm]) ∧
      ForallCells h m b

/-- `n` `Forall` cells from `p`, then the sort cell `Srt(s)`. -/
def TeleShape (h : Heap F) : Nat → SourceValue F → SourceValue F → Prop
  | 0, p, s => loadValue h p = .ok (.construct kexprEnum "Srt" [s])
  | n + 1, p, s => ∃ d b bm, loadValue h p = .ok (.construct kexprEnum "Forall" [d, b, bm]) ∧
      TeleShape h n b s

/-- The first `m` cells of `p` and `q` are `Forall` cells with the same domain and binder-data
pointers. -/
def TeleCells (h : Heap F) : Nat → SourceValue F → SourceValue F → Prop
  | 0, _, _ => True
  | m + 1, p, q => ∃ d b b' bm,
      loadValue h p = .ok (.construct kexprEnum "Forall" [d, b, bm]) ∧
      loadValue h q = .ok (.construct kexprEnum "Forall" [d, b', bm]) ∧ TeleCells h m b b'

theorem ForallCells.mono {h h' : Heap F} (ext : Heap.Extends h h') :
    ∀ {m : Nat} {p : SourceValue F}, ForallCells h m p → ForallCells h' m p
  | 0, _, _ => trivial
  | _ + 1, _, ⟨d, b, bm, hl, hr⟩ => ⟨d, b, bm, ext.loadValue_eq hl, ForallCells.mono ext hr⟩

theorem TeleShape.mono {h h' : Heap F} (ext : Heap.Extends h h') :
    ∀ {n : Nat} {p s : SourceValue F}, TeleShape h n p s → TeleShape h' n p s
  | 0, _, _, hl => ext.loadValue_eq hl
  | _ + 1, _, _, ⟨d, b, bm, hl, hr⟩ => ⟨d, b, bm, ext.loadValue_eq hl, TeleShape.mono ext hr⟩

theorem TeleCells.mono {h h' : Heap F} (ext : Heap.Extends h h') :
    ∀ {m : Nat} {p q : SourceValue F}, TeleCells h m p q → TeleCells h' m p q
  | 0, _, _, _ => trivial
  | _ + 1, _, _, ⟨d, b, b', bm, hp, hq, hr⟩ =>
    ⟨d, b, b', bm, ext.loadValue_eq hp, ext.loadValue_eq hq, TeleCells.mono ext hr⟩

/-- A cell appended to a heap is loaded at the heap's old length. -/
theorem loadValue_snoc_cell (h : Heap F) (c : String) (xs : List (SourceValue F)) :
    loadValue (h ++ [.construct kexprEnum c xs]) (.ptr (.enum kexprEnum) h.length) =
      .ok (.construct kexprEnum c xs) :=
  loadValue_enum_cell (by simp)

/-! ## The walk -/

/-- **`former_tele_at` at a scoped context**: from a represented `ty` (at opening depth `d`,
under the context `types`), the built term is represented, has `n` `Forall` cells ending in
`Srt(s)`, and wherever `ty` starts with `m ≤ n` syntactic `Forall` cells (read at any later
heap), the built term's first `m` cells carry the same domain and binder-data pointers. -/
theorem former_tele_at_spec {c : ScopedCtx} :
    ∀ (n : Nat) {d : Nat} {Γ : Nat → KExpr} {E : KExpr} {ℓ : KLevel}
      {rc pe types ps r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 18446744069414584321 →
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h d types →
      GhostScoped Γ d →
      CoreEnvFacts c.toCtx →
      ScopedLoadFacts c →
      CoreGood c cs →
      Tm c.κ d Γ h 0 E pe →
      RepKLevel h ℓ ps →
      ObsFn W "KernelCheck::former_tele_at" [rc, pe, .field (n : F), types, ps] h r h' cs →
      (∃ R, Tm c.κ d Γ h' 0 R r) ∧ TeleShape h' n r ps ∧
        ∀ (m : Nat) (H : Heap F), m ≤ n → Heap.Extends h' H → ForallCells H m pe →
          TeleCells H m pe r
  | 0, d, Γ, E, ℓ, rc, pe, types, ps, r, h, h', cs, _, hrc, hty, hsc, hef, hlf, hgood, hE, hℓ,
      ev => by
    match Obs.«KernelCheck::former_tele_at».obs ev with
    | .n0 (he19 := hr) (hm18 := hh) .. =>
      subst hr hh
      have cell : (h ++ [(.construct kexprEnum "Srt" [ps] : SourceValue F)])[h.length]? =
          some (.construct kexprEnum "Srt" [ps]) := by simp
      refine ⟨⟨.sort ℓ, .sort cell (hℓ.mono (Heap.Extends.snoc _ _)) (LvEq.refl ℓ)⟩,
        loadValue_snoc_cell h "Srt" [ps], ?_⟩
      intro m H hm _ _
      obtain rfl : m = 0 := by omega
      trivial
    | .other_Forall (hne32 := hne) .. => exact absurd rfl hne
    | .other_other (hne32 := hne) .. => exact absurd rfl hne
  | n + 1, d, Γ, E, ℓ, rc, pe, types, ps, r, h, h', cs, hlt, hrc, hty, hsc, hef, hlf, hgood, hE,
      hℓ, ev => by
    match Obs.«KernelCheck::former_tele_at».obs ev with
    | .n0 (hv14 := hv) .. => exact absurd hv (succ_field_ne_zero_bounded hlt)
    | .other_Forall (x_d := xd) (x_b := xb) (x_m := xm) (v79 := vb) (m89 := mb) (cs97 := csb)
        (m135 := m1) (ld47 := ld) (he74 := hr) (hm73 := hh) (op132 := op) (hm143 := hm1)
        (ev99 := evb) (hc177 := hc) .. =>
      subst hc hr hh
      have hgb : CoreGood c csb := hgood.sub (fun x hx => by simp [hx])
      obtain ⟨T, B, ℓm, rfl, hT, hB, hℓm⟩ := hE.forallE_of_load ld
      obtain ⟨ext_push, hty', hsc'⟩ := push_binder_types hT hty hsc
      rw [← hm1] at ext_push hty'
      have hB_open : Tm c.κ (d + 1) (Ghost.extend Γ d T) m1 0 (B.instantiate1 (.fvar d T)) xb :=
        (hB.open_body (Ghost.extend_at Γ d T) (Ghost.extend_below Γ d T)).mono ext_push
      rw [evalBinOp_sub_succ n op] at evb
      obtain ⟨⟨Rb, hRb⟩, hshape, hcells⟩ := former_tele_at_spec n (by omega)
        (hrc.mono ext_push) hty' hsc' hef hlf hgb hB_open (hℓ.mono ext_push) evb
      have ext_b : Heap.Extends m1 mb := evb.heap_extends
      have ext_f : Heap.Extends mb
          (mb ++ [(.construct kexprEnum "Forall" [xd, vb, xm] : SourceValue F)]) :=
        Heap.Extends.snoc _ _
      have ext_all : Heap.Extends h
          (mb ++ [(.construct kexprEnum "Forall" [xd, vb, xm] : SourceValue F)]) :=
        ext_push.trans (ext_b.trans ext_f)
      have cell : (mb ++ [(.construct kexprEnum "Forall" [xd, vb, xm] : SourceValue F)])[mb.length]?
          = some (.construct kexprEnum "Forall" [xd, vb, xm]) := by simp
      refine ⟨⟨.forallE T (Rb.abstract1 d 0) (bmeta ℓm),
          .forallE cell (hT.mono ext_all) ((Tm.close (Ghost.extend_below Γ d T) hRb).mono ext_f)
            (hℓm.mono ext_all)⟩,
        ⟨xd, vb, xm, loadValue_snoc_cell mb "Forall" [xd, vb, xm], hshape.mono ext_f⟩, ?_⟩
      intro m H hm hH hfc
      cases m with
      | zero => trivial
      | succ m =>
        obtain ⟨d', b', bm', hl', hfc'⟩ := hfc
        have hl := (ext_all.trans hH).loadValue_eq ld
        rw [hl] at hl'
        injection hl' with hl''
        injection hl'' with _ _ hargs
        simp only [List.cons.injEq, and_true] at hargs
        obtain ⟨rfl, rfl, rfl⟩ := hargs
        exact ⟨xd, xb, vb, xm, hl, hH.loadValue_eq
          (loadValue_snoc_cell mb "Forall" [xd, vb, xm]),
          hcells m H (by omega) (ext_f.trans hH) hfc'⟩
    | .other_other (v36 := v0) (x_d := xd) (x_b := xb) (x_m := xm) (v241 := vb) (m251 := mb)
        (cs259 := csb) (cs196 := csw) (m183 := mw) (p190 := pw) (m297 := m1)
        (ld47 := ld) (hne178 := hnf) (ev198 := evw) (ld192 := ldw) (he236 := hr) (hm235 := hh)
        (op294 := op) (hm305 := hm1) (ev261 := evb) (hc339 := hc) .. =>
      subst hc hr hh
      have hgw : CoreGood c csw := hgood.sub (fun x hx => by simp [hx])
      have hgb : CoreGood c csb := hgood.sub (fun x hx => by simp [hx])
      obtain ⟨E', hE', -⟩ := Core.GuardData.head_rep ⟨hef, hlf⟩ hgw hE evw
      obtain ⟨T, B, ℓm, rfl, hT, hB, hℓm⟩ := hE'.forallE_of_load ldw
      have ext_w : Heap.Extends h mw := evw.heap_extends
      obtain ⟨ext_push, hty', hsc'⟩ := push_binder_types hT (hty.mono ext_w) hsc
      rw [← hm1] at ext_push hty'
      have hB_open : Tm c.κ (d + 1) (Ghost.extend Γ d T) m1 0 (B.instantiate1 (.fvar d T)) xb :=
        (hB.open_body (Ghost.extend_at Γ d T) (Ghost.extend_below Γ d T)).mono ext_push
      rw [evalBinOp_sub_succ n op] at evb
      obtain ⟨⟨Rb, hRb⟩, hshape, -⟩ := former_tele_at_spec n (by omega)
        (hrc.mono (ext_w.trans ext_push)) hty' hsc' hef hlf hgb hB_open
        (hℓ.mono (ext_w.trans ext_push)) evb
      have ext_b : Heap.Extends m1 mb := evb.heap_extends
      have ext_f : Heap.Extends mb
          (mb ++ [(.construct kexprEnum "Forall" [xd, vb, xm] : SourceValue F)]) :=
        Heap.Extends.snoc _ _
      have ext_all : Heap.Extends mw
          (mb ++ [(.construct kexprEnum "Forall" [xd, vb, xm] : SourceValue F)]) :=
        ext_push.trans (ext_b.trans ext_f)
      have cell : (mb ++ [(.construct kexprEnum "Forall" [xd, vb, xm] : SourceValue F)])[mb.length]?
          = some (.construct kexprEnum "Forall" [xd, vb, xm]) := by simp
      refine ⟨⟨.forallE T (Rb.abstract1 d 0) (bmeta ℓm),
          .forallE cell (hT.mono ext_all) ((Tm.close (Ghost.extend_below Γ d T) hRb).mono ext_f)
            (hℓm.mono ext_all)⟩,
        ⟨xd, vb, xm, loadValue_snoc_cell mb "Forall" [xd, vb, xm], hshape.mono ext_f⟩, ?_⟩
      intro m H hm hH hfc
      cases m with
      | zero => trivial
      | succ m =>
        exfalso
        obtain ⟨d', b', bm', hl', -⟩ := hfc
        have hl := ((ext_w.trans ext_all).trans hH).loadValue_eq ld
        rw [hl] at hl'
        injection hl' with hv
        exact hnf [d', b', bm'] rfl hv

/-! ## The constructor loop walks the parameters syntactically -/

/-- **The parameter agreement walks `m` syntactic `Forall` cells** of its first argument (read at
its final heap). -/
theorem check_param_agreement_go_cells :
    ∀ (m : Nat) {rc pta ptb types r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      m < 18446744069414584321 →
      ObsFn W "KernelCheck::check_param_agreement_go" [rc, pta, ptb, .field (m : F), types]
        h r h' cs →
      ForallCells h' m pta
  | 0, _, _, _, _, _, _, _, _, _, _ => trivial
  | m + 1, rc, pta, ptb, types, r, h, h', cs, hlt, ev => by
    match Obs.«KernelCheck::check_param_agreement_go».obs ev with
    | .n0 (hv14 := hv) .. => exact absurd hv (succ_field_ne_zero_bounded hlt)
    | .other (x_da := xda) (x_ba := xba) (w43 := w) (m95 := m95) (m168 := m168) (ld35 := ld)
        (ev107 := evq) (hm178 := hm) (op243 := op) (ev203 := evr) .. =>
      rw [evalBinOp_sub_succ m op] at evr
      have e2 : Heap.Extends m95 m168 := by
        rw [hm]
        exact Heap.Extends.snoc _ _
      have ext : Heap.Extends h h' := evq.heap_extends.trans (e2.trans evr.heap_extends)
      exact ⟨xda, xba, w, ext.loadValue_eq ld, check_param_agreement_go_cells m (by omega) evr⟩

/-- **At a family with a constructor, the constructor loop walks the family's declared type's
first `nP` cells as syntactic `Forall` cells** (the first constructor's parameter agreement),
read at a heap after the loop's start. -/
theorem check_inductive_shape_ctors_param_cells {rc ty nI numLvls blk idx lvl uns r :
      SourceValue F} {nP N : Nat} {h h' : Heap F} {cs : List (Call F)}
    (hN : N ≠ 0) (hNb : N < 18446744069414584321) (hP : nP < 18446744069414584321)
    (ev : ObsFn W "KernelCheck::check_inductive_shape_ctors"
      [rc, ty, .field (nP : F), nI, .field (N : F), numLvls, blk, idx, lvl, uns, .field 0]
      h r h' cs) :
    ∃ H, Heap.Extends h H ∧ ForallCells H nP ty := by
  match Obs.«KernelCheck::check_inductive_shape_ctors».obs ev with
  | .n0 (op17 := op) .. =>
    exfalso
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    simp only [evalBinOp] at op
    injection op with hv
    rw [sub_zero] at hv
    exact succ_field_ne_zero_bounded hNb hv
  | .other (x_cty := cty) (m400 := m400) (ev442 := evpa) (hc794 := hc) .. =>
    have hmem : (⟨"KernelCheck::check_param_agreement", [rc, ty, cty, .field (nP : F)], m400⟩ :
        Call F) ∈ cs := by
      rw [hc]
      simp
    have e1 : Heap.Extends h m400 := (ev.call_heap_bounds hmem).1
    match Obs.«KernelCheck::check_param_agreement».obs evpa with
    | .run (m41 := m41) (hm49 := hm41) (ev6 := evgo) .. =>
      exact ⟨_, e1.trans evpa.heap_extends, check_param_agreement_go_cells nP hP evgo⟩

/-! ## Exact readings -/

/-- **A represented pointer has an exact reading.** -/
theorem Tm.exactify {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F} (rep : Tm κ d Γ h k E p) :
    ∃ E', TmExact κ d Γ h k E' p := by
  induction rep with
  | bvarLocal cell hs hi => exact ⟨_, .bvarLocal cell hs hi⟩
  | bvarFree cell hs hk hd => exact ⟨_, .bvarFree cell hs hk hd⟩
  | sort cell rl _ => exact ⟨_, .sort cell rl⟩
  | @const k addr ap lsp a ls us res cell ra rls hus => exact ⟨_, .const cell ra rls⟩
  | app cell _ _ ihf iha =>
    obtain ⟨_, hf⟩ := ihf
    obtain ⟨_, ha⟩ := iha
    exact ⟨_, .app cell hf ha⟩
  | lam cell _ _ rl iht ihb =>
    obtain ⟨_, ht⟩ := iht
    obtain ⟨_, hb⟩ := ihb
    exact ⟨_, .lam cell ht hb rl⟩
  | forallE cell _ _ rl iht ihb =>
    obtain ⟨_, ht⟩ := iht
    obtain ⟨_, hb⟩ := ihb
    exact ⟨_, .forallE cell ht hb rl⟩
  | letE cell _ _ _ iht ihv ihb =>
    obtain ⟨_, ht⟩ := iht
    obtain ⟨_, hv⟩ := ihv
    obtain ⟨_, hb⟩ := ihb
    exact ⟨_, .letE cell ht hv hb⟩
  | litNat cell rl hc => exact ⟨_, .litNat cell rl hc⟩
  | litStr cell rb hs => exact ⟨_, .litStr cell rb hs⟩
  | @proj k addr ap ep a i E res perm cell ra _ ihe =>
    obtain ⟨_, he⟩ := ihe
    exact ⟨_, .proj cell ra he⟩

/-- **An exact reading is unique.** -/
theorem TmExact.det {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E₁ E₂ : KExpr} {p : SourceValue F} (r₁ : TmExact κ d Γ h k E₁ p)
    (r₂ : TmExact κ d Γ h k E₂ p) : E₁ = E₂ := by
  induction r₁ generalizing E₂ with
  | bvarLocal cell _ hi =>
    cases r₂ with
    | bvarLocal cell' _ _ =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq,
        Value.field.injEq, and_true, true_and] at this; subst this; rfl
    | bvarFree cell' _ hk _ =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq,
        Value.field.injEq, and_true, true_and] at this; subst this; omega
    | sort cell' _ | const cell' _ _ | app cell' _ _ | lam cell' _ _ _ | forallE cell' _ _ _
    | letE cell' _ _ _ | litNat cell' _ _ | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | bvarFree cell _ hk hd =>
    cases r₂ with
    | bvarLocal cell' _ hi =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq,
        Value.field.injEq, and_true, true_and] at this; subst this; omega
    | bvarFree cell' _ _ _ =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq,
        Value.field.injEq, and_true, true_and] at this; subst this; rfl
    | sort cell' _ | const cell' _ _ | app cell' _ _ | lam cell' _ _ _ | forallE cell' _ _ _
    | letE cell' _ _ _ | litNat cell' _ _ | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | sort cell rl =>
    cases r₂ with
    | sort cell' rl' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; subst this
      have := rl.det rl'; subst this; rfl
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | const cell' _ _ | app cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _
    | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | const cell ra rls =>
    cases r₂ with
    | const cell' ra' rls' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; obtain ⟨rfl, rfl⟩ := this
      have := addr_det ra ra'; subst this
      have := rls.det rls'; subst this
      rfl
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ | app cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _
    | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | app cell _ _ ihf iha =>
    cases r₂ with
    | app cell' rf' ra' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; obtain ⟨rfl, rfl⟩ := this
      rw [ihf rf', iha ra']
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ | const cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _
    | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | lam cell _ _ rl iht ihb =>
    cases r₂ with
    | lam cell' rt' rb' rl' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; obtain ⟨rfl, rfl, rfl⟩ := this
      have := rl.det rl'; subst this
      rw [iht rt', ihb rb']
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ | const cell' _ _ | app cell' _ _
    | forallE cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _ | litStr cell' _ _
    | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | forallE cell _ _ rl iht ihb =>
    cases r₂ with
    | forallE cell' rt' rb' rl' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; obtain ⟨rfl, rfl, rfl⟩ := this
      have := rl.det rl'; subst this
      rw [iht rt', ihb rb']
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ | const cell' _ _ | app cell' _ _
    | lam cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _ | litStr cell' _ _
    | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | letE cell _ _ _ iht ihv ihb =>
    cases r₂ with
    | letE cell' rt' rv' rb' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; obtain ⟨rfl, rfl, rfl⟩ := this
      rw [ihv rv', ihb rb']
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ | const cell' _ _ | app cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | litNat cell' _ _ | litStr cell' _ _
    | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | litNat cell rl _ =>
    cases r₂ with
    | litNat cell' rl' _ =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; subst this
      have := limbsVal_det rl rl'; subst this; rfl
    | litStr cell' _ _ =>
      have := cell_eq cell cell'; simp at this
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ | const cell' _ _ | app cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | litStr cell rb hs =>
    cases r₂ with
    | litStr cell' rb' hs' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; subst this
      have := bytes_det rb rb'; subst this
      rw [StrBytes] at hs hs'; rw [hs] at hs'; injection hs' with hs'; subst hs'; rfl
    | litNat cell' _ _ =>
      have := cell_eq cell cell'; simp at this
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ | const cell' _ _ | app cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | proj cell ra _ ihe =>
    cases r₂ with
    | proj cell' ra' re' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq,
        Value.field.injEq, and_true, true_and] at this; obtain ⟨rfl, rfl, rfl⟩ := this
      have := addr_det ra ra'; subst this
      rw [ihe re']
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ | const cell' _ _ | app cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _
    | litStr cell' _ _ =>
      have := cell_eq cell cell'; simp at this

/-- **The exact reading of a telescope's cells** is a syntactic telescope of their length
ending in the sort of the last cell's level. -/
theorem TeleShape.stripPis_exact {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} :
    ∀ (n : Nat) {k : Nat} {E : KExpr} {p s : SourceValue F},
      TeleShape h n p s → TmExact κ d Γ h k E p →
      ∃ bs l, E.stripPis n = some (bs, .sort l) ∧ RepKLevel h l s
  | 0, k, E, p, s, hl, hE => by
    obtain ⟨l, rfl, hl'⟩ := hE.sort_of_load hl
    exact ⟨[], l, rfl, hl'⟩
  | n + 1, k, E, p, s, ⟨dp, bp, bm, hl, hr⟩, hE => by
    obtain ⟨T, B, ℓ, rfl, -, hB, -⟩ := hE.forallE_of_load hl
    obtain ⟨bs, l, hst, hl'⟩ := TeleShape.stripPis_exact n hr hB
    exact ⟨(T, bmeta ℓ) :: bs, l, by simp [Expr.stripPis, hst], hl'⟩

/-- The first `m` binders of two terms are syntactic `∀`s with the same domains and binder
data. -/
def PrefixEq : Nat → KExpr → KExpr → Prop
  | 0, _, _ => True
  | m + 1, .forallE T B bm, .forallE T' B' bm' => T = T' ∧ bm = bm' ∧ PrefixEq m B B'
  | _ + 1, _, _ => False

/-- **Two exact readings of spines that share their first `m` cells** have the same first `m`
binders. -/
theorem TeleCells.prefixEq {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} :
    ∀ (m : Nat) {k : Nat} {E R : KExpr} {p q : SourceValue F},
      TeleCells h m p q → TmExact κ d Γ h k E p → TmExact κ d Γ h k R q → PrefixEq m E R
  | 0, _, _, _, _, _, _, _, _ => trivial
  | m + 1, k, E, R, p, q, ⟨dp, b, b', bm, hp, hq, hr⟩, hE, hR => by
    obtain ⟨T, B, ℓ, rfl, hT, hB, hℓ⟩ := hE.forallE_of_load hp
    obtain ⟨T', B', ℓ', rfl, hT', hB', hℓ'⟩ := hR.forallE_of_load hq
    have hTT := hT.det hT'
    have hℓℓ := hℓ.det hℓ'
    subst hTT hℓℓ
    exact ⟨rfl, rfl, TeleCells.prefixEq m hr hB hB'⟩

theorem PrefixEq.instantiate1 {v : KExpr} :
    ∀ (m : Nat) {E R : KExpr} (j : Nat), PrefixEq m E R →
      PrefixEq m (E.instantiate1 v j) (R.instantiate1 v j)
  | 0, _, _, _, _ => trivial
  | m + 1, .forallE T B bm, .forallE T' B' bm', j, ⟨hT, hbm, hr⟩ => by
    subst hT hbm
    simp only [Expr.instantiate1]
    exact ⟨rfl, rfl, PrefixEq.instantiate1 m (j + 1) hr⟩
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _ _, _, _, h | _ + 1, .sort _, _, _, h
  | _ + 1, .const _ _, _, _, h | _ + 1, .app _ _, _, _, h | _ + 1, .lam _ _ _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, h | _ + 1, .lit _, _, _, h | _ + 1, .proj _ _ _, _, _, h => by
    simp [PrefixEq] at h
  | _ + 1, .forallE _ _ _, .bvar _, _, h | _ + 1, .forallE _ _ _, .fvar _ _, _, h
  | _ + 1, .forallE _ _ _, .sort _, _, h | _ + 1, .forallE _ _ _, .const _ _, _, h
  | _ + 1, .forallE _ _ _, .app _ _, _, h | _ + 1, .forallE _ _ _, .lam _ _ _, _, h
  | _ + 1, .forallE _ _ _, .letE _ _ _ _, _, h | _ + 1, .forallE _ _ _, .lit _, _, h
  | _ + 1, .forallE _ _ _, .proj _ _ _, _, h => by
    simp [PrefixEq] at h

/-- **Terms with the same first `m` binders open them to the same variables.** -/
theorem PrefixEq.openPisAtFvars :
    ∀ (m : Nat) {E R : KExpr} {i : Nat} {tfvs : List KExpr} {r₁ : KExpr}, PrefixEq m E R →
      Ix.Kernel.openPisAtFvars m E i = some (tfvs, r₁) →
      ∃ r₂, Ix.Kernel.openPisAtFvars m R i = some (tfvs, r₂)
  | 0, E, R, i, tfvs, r₁, _, h => by
    simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨R, rfl⟩
  | m + 1, .forallE T B bm, .forallE T' B' bm', i, tfvs, r₁, ⟨hT, hbm, hr⟩, h => by
    subst hT hbm
    simp only [Ix.Kernel.openPisAtFvars] at h ⊢
    split at h
    · next fvs e hrec =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨r₂, hr₂⟩ := PrefixEq.openPisAtFvars m (PrefixEq.instantiate1 m 0 hr) hrec
      rw [hr₂]
      exact ⟨r₂, rfl⟩
    · exact nomatch h
  | _ + 1, .bvar _, _, _, _, _, hp, _ | _ + 1, .fvar _ _, _, _, _, _, hp, _
  | _ + 1, .sort _, _, _, _, _, hp, _ | _ + 1, .const _ _, _, _, _, _, hp, _
  | _ + 1, .app _ _, _, _, _, _, hp, _ | _ + 1, .lam _ _ _, _, _, _, _, hp, _
  | _ + 1, .letE _ _ _ _, _, _, _, _, hp, _ | _ + 1, .lit _, _, _, _, _, hp, _
  | _ + 1, .proj _ _ _, _, _, _, _, hp, _ => by
    simp [PrefixEq] at hp
  | _ + 1, .forallE _ _ _, .bvar _, _, _, _, hp, _
  | _ + 1, .forallE _ _ _, .fvar _ _, _, _, _, hp, _
  | _ + 1, .forallE _ _ _, .sort _, _, _, _, hp, _
  | _ + 1, .forallE _ _ _, .const _ _, _, _, _, hp, _
  | _ + 1, .forallE _ _ _, .app _ _, _, _, _, hp, _
  | _ + 1, .forallE _ _ _, .lam _ _ _, _, _, _, hp, _
  | _ + 1, .forallE _ _ _, .letE _ _ _ _, _, _, _, hp, _
  | _ + 1, .forallE _ _ _, .lit _, _, _, _, hp, _
  | _ + 1, .forallE _ _ _, .proj _ _ _, _, _, _, hp, _ => by
    simp [PrefixEq] at hp

end IxVM.Refinement.Decl
