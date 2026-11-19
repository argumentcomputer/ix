import IxVMRefinement.Binding.FamilyReconMember
import IxVMRefinement.Binding.FamilyReconAnswers
import IxVMRefinement.TwinFamily.ProducerRow
import IxVMRefinement.Obs.KernelCheck7
import IxVMRefinement.Obs.KernelCheck8
import IxVMRefinement.Obs.KernelTypes0

/-! # A member of the family record against the reconstruction, outside a group's validation

Outside a group's validation `KernelCheck::canonical_rules_at_pos` accepts a declared type that is
the reconstruction (`kexpr_struct_eq`) or its full consumption (`wrap_rel(1, ·, ·)`), and threads
a form state through the members of the record (`KernelModeled::check_recs`, started at `0` by
`check_family`): `0` while every member is both, `1` once one is the reconstruction only, `2`
once one is the full consumption only; a member of the other kind is then refused. The rules are
compared as under validation (`compare_rules`, against the declared type; no role context and no
form reaches it).

* `LetFree`, `TmLF`: a heap term with no `Let` cell.
* `collect_spine_letFree_spec`: `KernelTypes::collect_spine` on such a term is `getAppFn`,
  `getAppArgs`.
* `lam_first_arity_one`: `KernelCheck::lam_first_arity` returning `(1, k)` is `lamFirstArity`.
* `DefnAtAnswers` (`defnAtAnswers_of_run`), `ArityRefusals`: the loads against the store's
  definitions (`defnAt`), and the refusals of `lam_first_arity` against `lamFirstArity`.
* `consume_wrapper_spec`: `KernelCheck::consume_wrapper` is `consumeAt (wrapAt t E)`, in both
  directions, a consumed wrapper observed among the calls (`WrapperObserved`).
* **`wrap_rel_full_spec`**: `wrap_rel(1, g, d) = 1` is `FullConsObs (wrapAt t E)
  (WrapperObserved calls t) g d`, where the heap term of `g` has no `Let` cell.
* `FormStep`, **`canonical_rules_at_pos_form_spec`**, **`check_recursor_canonical_at_form_spec`**:
  the member check under any role context: a step of the form in which the declared type is the
  reconstructed type or its full consumption, and the rules follow the reconstructed bodies.
* `memberRecon_of_canonical_rel`: `MemberRecon` at a relation of the types.
* **`recordForm_of_members`**: the form state leaves a record in one form at all its members:
  `RFormS t E B rb ∨ RecordFullConsObs calls t E B rb`.
* `FullCons.consumeAt_none`, `FullCons.forallE_dom_none`, `FullCons.not_refl_of_consumable`: a
  full consumption keeps no consumable ∀ domain.

Remaining hypotheses. `ArityRefusals`: `lam_first_arity` tests a λ's datum against `Succ(Zero)`
and `lamFirstArity` its zero-ness; they agree on a converted value, whose never-zero data are
stored as `Succ(Zero)`. `build_rec_type_letFree`: the reconstructed type's heap term has no `Let`
cell. `wrap_rel` compares a `Let` cell part by part and a domain that is a `Let` cell whole,
consuming nothing at the head of the term the cell represents, whereas `FullCons` is stated on
the represented terms (a `Let` cell represents its expansion); where the expansion of a `Let`
cell is, or exposes at a binder domain, a wrapper applied to its arity, `wrap_rel(1, ·, ·)`
accepts a declared type that is no full consumption (`FullCons.forallE_dom_none`). The builders'
specifications are taken at the member check's arguments, as under validation. -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Binding.FamilyFlat
open IxVM.Consistency (blockSelf)
open IxVM.Refinement.Core (W KExpr KLevel KKey bmeta kexprEnum kexprListEnum addrTy ixAddr
  ExprLvEq LvEq LvEqList)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open IxVM.Refinement.Typing.TwinFamily (FullConsObs ConsumesObs WrapperObserved RecordFullConsObs)
open Ix.Kernel.Semantics (lamFirstArity)
open IxVM (F)

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Heap terms without a `let` cell -/

/-- **The heap term at `p` has no `Let` cell**: every cell reached from `p` through the parts of
an application, a binder or a projection is an application, a binder, a projection or a leaf
(a variable, a sort, a constant, a literal). -/
inductive LetFree (h : Heap F) : SourceValue F → Prop
  | app {p xf xa : SourceValue F}
      (ld : loadValue h p = .ok (.construct kexprEnum "App" [xf, xa])) :
      LetFree h xf → LetFree h xa → LetFree h p
  | lam {p xt xb xm : SourceValue F}
      (ld : loadValue h p = .ok (.construct kexprEnum "Lam" [xt, xb, xm])) :
      LetFree h xt → LetFree h xb → LetFree h p
  | forallE {p xt xb xm : SourceValue F}
      (ld : loadValue h p = .ok (.construct kexprEnum "Forall" [xt, xb, xm])) :
      LetFree h xt → LetFree h xb → LetFree h p
  | proj {p xs xi xe : SourceValue F}
      (ld : loadValue h p = .ok (.construct kexprEnum "Proj" [xs, xi, xe])) :
      LetFree h xe → LetFree h p
  | leaf {p v : SourceValue F} (ld : loadValue h p = .ok v)
      (hleaf : ∀ (tag : String) (vs : List (SourceValue F)), v = .construct kexprEnum tag vs →
        tag = "BVar" ∨ tag = "Srt" ∨ tag = "Const" ∨ tag = "Lit") : LetFree h p

theorem LetFree.mono {h h' : Heap F} {p : SourceValue F} (ext : Heap.Extends h h')
    (hl : LetFree h p) : LetFree h' p := by
  induction hl with
  | app ld _ _ ihf iha => exact .app (loadValue_mono ext ld) ihf iha
  | lam ld _ _ iht ihb => exact .lam (loadValue_mono ext ld) iht ihb
  | forallE ld _ _ iht ihb => exact .forallE (loadValue_mono ext ld) iht ihb
  | proj ld _ ihe => exact .proj (loadValue_mono ext ld) ihe
  | leaf ld hleaf => exact .leaf (loadValue_mono ext ld) hleaf

theorem LetFree.not_let_val {h : Heap F} {p v : SourceValue F} (hl : LetFree h p)
    (ld : loadValue h p = .ok v) :
    ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Let" vs := by
  intro vs _ hv
  subst hv
  cases hl with
  | app ld' _ _ => rw [ld] at ld'; simp at ld'
  | lam ld' _ _ => rw [ld] at ld'; simp at ld'
  | forallE ld' _ _ => rw [ld] at ld'; simp at ld'
  | proj ld' _ => rw [ld] at ld'; simp at ld'
  | leaf ld' hleaf =>
    rw [ld] at ld'
    injection ld' with hv
    rcases hleaf _ _ hv.symm with h1 | h1 | h1 | h1 <;> simp at h1

theorem LetFree.notLet {h : Heap F} {p : SourceValue F} (hl : LetFree h p) : NotLet h p := by
  cases hl with
  | app ld hf ha => exact ⟨_, ld, (LetFree.app ld hf ha).not_let_val ld⟩
  | lam ld ht hb => exact ⟨_, ld, (LetFree.lam ld ht hb).not_let_val ld⟩
  | forallE ld ht hb => exact ⟨_, ld, (LetFree.forallE ld ht hb).not_let_val ld⟩
  | proj ld he => exact ⟨_, ld, (LetFree.proj ld he).not_let_val ld⟩
  | leaf ld hleaf => exact ⟨_, ld, (LetFree.leaf ld hleaf).not_let_val ld⟩

theorem LetFree.app_inv {h : Heap F} {p xf xa : SourceValue F} (hl : LetFree h p)
    (ld : loadValue h p = .ok (.construct kexprEnum "App" [xf, xa])) :
    LetFree h xf ∧ LetFree h xa := by
  cases hl with
  | app ld' hf ha =>
    rw [ld] at ld'
    simp only [Except.ok.injEq, Value.construct.injEq, List.cons.injEq, and_true, true_and]
      at ld'
    obtain ⟨rfl, rfl⟩ := ld'
    exact ⟨hf, ha⟩
  | lam ld' _ _ => rw [ld] at ld'; simp at ld'
  | forallE ld' _ _ => rw [ld] at ld'; simp at ld'
  | proj ld' _ => rw [ld] at ld'; simp at ld'
  | leaf ld' hleaf =>
    rw [ld] at ld'
    injection ld' with hv
    rcases hleaf _ _ hv.symm with h1 | h1 | h1 | h1 <;> simp at h1

theorem LetFree.lam_inv {h : Heap F} {p xt xb xm : SourceValue F} (hl : LetFree h p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Lam" [xt, xb, xm])) :
    LetFree h xt ∧ LetFree h xb := by
  cases hl with
  | lam ld' ht hb =>
    rw [ld] at ld'
    simp only [Except.ok.injEq, Value.construct.injEq, List.cons.injEq, and_true, true_and]
      at ld'
    obtain ⟨rfl, rfl, -⟩ := ld'
    exact ⟨ht, hb⟩
  | app ld' _ _ => rw [ld] at ld'; simp at ld'
  | forallE ld' _ _ => rw [ld] at ld'; simp at ld'
  | proj ld' _ => rw [ld] at ld'; simp at ld'
  | leaf ld' hleaf =>
    rw [ld] at ld'
    injection ld' with hv
    rcases hleaf _ _ hv.symm with h1 | h1 | h1 | h1 <;> simp at h1

theorem LetFree.forallE_inv {h : Heap F} {p xt xb xm : SourceValue F} (hl : LetFree h p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Forall" [xt, xb, xm])) :
    LetFree h xt ∧ LetFree h xb := by
  cases hl with
  | forallE ld' ht hb =>
    rw [ld] at ld'
    simp only [Except.ok.injEq, Value.construct.injEq, List.cons.injEq, and_true, true_and]
      at ld'
    obtain ⟨rfl, rfl, -⟩ := ld'
    exact ⟨ht, hb⟩
  | app ld' _ _ => rw [ld] at ld'; simp at ld'
  | lam ld' _ _ => rw [ld] at ld'; simp at ld'
  | proj ld' _ => rw [ld] at ld'; simp at ld'
  | leaf ld' hleaf =>
    rw [ld] at ld'
    injection ld' with hv
    rcases hleaf _ _ hv.symm with h1 | h1 | h1 | h1 <;> simp at h1

theorem LetFree.proj_inv {h : Heap F} {p xs xi xe : SourceValue F} (hl : LetFree h p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Proj" [xs, xi, xe])) : LetFree h xe := by
  cases hl with
  | proj ld' he =>
    rw [ld] at ld'
    simp only [Except.ok.injEq, Value.construct.injEq, List.cons.injEq, and_true, true_and]
      at ld'
    obtain ⟨-, -, rfl⟩ := ld'
    exact he
  | app ld' _ _ => rw [ld] at ld'; simp at ld'
  | lam ld' _ _ => rw [ld] at ld'; simp at ld'
  | forallE ld' _ _ => rw [ld] at ld'; simp at ld'
  | leaf ld' hleaf =>
    rw [ld] at ld'
    injection ld' with hv
    rcases hleaf _ _ hv.symm with h1 | h1 | h1 | h1 <;> simp at h1
/-- **An exact open term whose heap term has no `Let` cell.** -/
def TmLF (κ : _root_.Address → KKey) (h : Heap F) (E : KExpr) (p : SourceValue F) : Prop :=
  TmOExact κ h E p ∧ LetFree h p

theorem tmLF_heapMono₂ {κ : _root_.Address → KKey} : HeapMono₂ (TmLF κ) :=
  fun _ _ _ _ ext rep => ⟨rep.1.mono ext, rep.2.mono ext⟩

/-! ## `collect_spine` on a term without a `let` cell -/

private theorem kexprList_names_o :
    kexprListEnum = (Instance.mk "Lists::Node" [.ptr (.named "KernelTypes::KExprNode" [])]).symbol :=
  Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol.symm

private theorem kexprSnoc_names_o :
    Obs.Names.«Lists::snoc<&KernelTypes::KExprNode>» =
      (Instance.mk "Lists::snoc" [.ptr (.named "KernelTypes::KExprNode" [])]).symbol :=
  Obs.Names.«Lists::snoc<&KernelTypes::KExprNode>».symbol.symm

/-- **`KernelTypes::collect_spine`** on an exact open term whose heap term has no `Let` cell: the
head and the arguments of the term (`getAppFn`, `getAppArgs`), each again without a `Let` cell.
(At a `Let` cell the function stops, where the term the cell represents may be an application.) -/
theorem collect_spine_letFree_spec {κ : _root_.Address → KKey} {h h' : Heap F}
    {E : KExpr} {p hd args : SourceValue F} {cs : List (Call F)}
    (hp : TmOExact κ h E p) (hlf : LetFree h p)
    (ev : ObsFn W "KernelTypes::collect_spine" [p] h (.tuple [hd, args]) h' cs) :
    TmOExact κ h' E.getAppFn hd ∧ LetFree h' hd ∧
      RepList kexprListEnum (TmLF κ) h' E.getAppArgs args := by
  match Obs.«KernelTypes::collect_spine».obs ev with
  | .App (x_f := xf) (x_a := xa) (m31 := m1) (cs41 := cs1) (x_head := xhd) (x_args := xargs)
      (v68 := vsnoc) (m78 := m2) (cs86 := cs2) (ld12 := ld) (ev43 := e1) (he69 := hres)
      (ev88 := e2) (he105 := hh) (hc106 := hc) =>
    injection hres with hpair
    injection hpair with hhd hpair2
    injection hpair2 with hargs
    subst hhd hargs hh
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := TmOExact.app_of_load hp ld
    obtain ⟨lf, la⟩ := hlf.app_inv ld
    have hlt : cs1.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨hfn, hnl, hlist⟩ := collect_spine_letFree_spec hf lf e1
    have hlist' : RepList
        (Instance.mk "Lists::Node" [.ptr (.named "KernelTypes::KExprNode" [])]).symbol
        (TmLF κ) m1 Ef.getAppArgs xargs := by
      rwa [← kexprList_names_o]
    rw [kexprSnoc_names_o] at e2
    have hsnoc := Lib.Lists.snoc_spec (tmLF_heapMono₂ (κ := κ)) e2 hlist'
      (⟨ha.mono e1.heap_extends, la.mono e1.heap_extends⟩ : TmLF κ m1 Ea xa)
    rw [← kexprList_names_o] at hsnoc
    exact ⟨hfn.mono e2.heap_extends, hnl.mono e2.heap_extends, hsnoc⟩
  | .other (v1 := v) (m124 := m1) (ld12 := ld) (hne107 := hneApp) (he115 := hres)
      (hm132 := hm1) (he136 := hh) .. =>
    injection hres with hpair
    injection hpair with hhd hpair2
    injection hpair2 with hargs
    subst hhd hargs hh hm1
    obtain ⟨hfn, hargs⟩ := not_app_of_notLet hp ld hneApp (hlf.not_let_val ld)
    rw [hfn, hargs]
    have ext : Heap.Extends h
        (h ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []]) :=
      Heap.Extends.snoc _ _
    have hnil : RepList kexprListEnum (TmLF κ)
        (h ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []]) []
        (.ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») h.length) :=
      .nil (by simp)
    exact ⟨hp.mono ext, hlf.mono ext, hnil⟩
termination_by cs.length

/-! ## `lam_first_arity` -/

private theorem tm_lam_descent_o {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p w20 xb xm : SourceValue F} {steps : Nat}
    (hE : Core.Tm κ d Γ h k E p)
    (ld : loadValue h p = .ok (.construct Core.kexprEnum "Lam" [w20, xb, xm]))
    (hdesc : IxVM.Refinement.RomBound.HeapDescent h (.enum Core.kexprEnum) xb steps) :
    IxVM.Refinement.RomBound.HeapDescent h (.enum Core.kexprEnum) p (steps + 1) := by
  cases hE with
  | @lam _ addr tp bp lp _ _ _ cell _ _ _ =>
    obtain ⟨_, hxs⟩ := Core.load_cell cell ld
    injection hxs with h1 hxs; injection hxs with h2 _
    subst h1 h2
    exact .down cell (by simp [Value.type]) (by simp [IxVM.Refinement.RomBound.cellArgs]) hdesc
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
  | app cell _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ | proj cell _ _ =>
    exact False.elim (Core.load_cell_ne cell ld (by decide))

private theorem tm_ptr_descent_zero_o {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p : SourceValue F}
    (hE : Core.Tm κ d Γ h k E p) :
    IxVM.Refinement.RomBound.HeapDescent h (.enum Core.kexprEnum) p 0 := by
  cases hE with
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
  | app cell _ _ | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _
  | litNat cell _ _ | litStr cell _ _ | proj cell _ _ =>
    exact .here cell (by simp [Value.type])

/-- **`KernelCheck::lam_first_arity` returning `(1, k)`** on an exact open term, at the count `n`
of λs passed: the term is `λ … λ, x` under `k - n` further λs of datum `never`, `x` the first of
the `k` (`lamFirstArity`); the function allocates nothing, and `k` is `n` plus a descent of the
heap term. -/
theorem lam_first_arity_one {κ : _root_.Address → KKey} :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelCheck::lam_first_arity" →
      ∀ (n : Nat) (E : KExpr) (xv xk : SourceValue F),
        args = [xv, .field (n : F)] → r = .tuple [.field 1, xk] →
        (∀ steps, IxVM.Refinement.RomBound.HeapDescent h (.enum Core.kexprEnum) xv steps →
          n + steps < 549755813888) →
        TmOExact κ h E xv →
        ∃ k_out steps : Nat,
          xk = .field (k_out : F) ∧
          k_out = n + steps ∧
          IxVM.Refinement.RomBound.HeapDescent h (.enum Core.kexprEnum) xv steps ∧
          lamFirstArity E n = some k_out ∧
          h' = h :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => fname = "KernelCheck::lam_first_arity" →
      ∀ (n : Nat) (E : KExpr) (xv xk : SourceValue F),
        args = [xv, .field (n : F)] → r = .tuple [.field 1, xk] →
        (∀ steps, IxVM.Refinement.RomBound.HeapDescent h (.enum Core.kexprEnum) xv steps →
          n + steps < 549755813888) →
        TmOExact κ h E xv →
        ∃ k_out steps : Nat,
          xk = .field (k_out : F) ∧
          k_out = n + steps ∧
          IxVM.Refinement.RomBound.HeapDescent h (.enum Core.kexprEnum) xv steps ∧
          lamFirstArity E n = some k_out ∧
          h' = h)
    (fun fname args h r h' cs ev ih hfn n E xv xk hargs hr hbnd_desc hE => by
      subst hfn hargs hr
      have hTm : ∃ k, Core.Tm κ 0 ghost0 h k E xv := by
        obtain ⟨k, rep⟩ := hE
        exact ⟨k, rep.toTm⟩
      obtain ⟨kd, hTm⟩ := hTm
      match Obs.«KernelCheck::lam_first_arity».obs ev with
      | .Lam_Succ_other (he118 := he) .. =>
        injection he with hxs; injection hxs with h01 _
        exact absurd (Value.field.inj h01) one_ne_zero
      | .Lam_other (he141 := he) .. =>
        injection he with hxs; injection hxs with h01 _
        exact absurd (Value.field.inj h01) one_ne_zero
      | .BVar_n0 (he186 := he) .. =>
        injection he with hxs; injection hxs with h01 _
        exact absurd (Value.field.inj h01) one_ne_zero
      | .BVar_other_other (he264 := he) .. =>
        injection he with hxs; injection hxs with h01 _
        exact absurd (Value.field.inj h01) one_ne_zero
      | .other (he287 := he) .. =>
        injection he with hxs; injection hxs with h01 _
        exact absurd (Value.field.inj h01) one_ne_zero
      | .Lam_Succ_Zero (w20 := w20) (x_b := xb) (x_m := xm) (x_z := xz)
          (cs82 := cs82) (v86 := v86)
          (ld12 := ld12) (ld47 := ld47) (ld71 := ld71)
          (op107 := op107) (ev84 := ev84) (hc109 := hc109) =>
        subst hc109
        obtain ⟨T, B, ℓ, rfl, _, hB, hℓ⟩ := hE.lam_of_load ld12
        obtain ⟨u, rfl, hu⟩ := IxVM.Refinement.Levels.rep_succ_of_load hℓ ld47
        obtain rfl := IxVM.Refinement.Levels.rep_zero_of_load hu ld71
        have hv86 : v86 = .field ((n + 1 : Nat) : F) :=
          IxVM.Refinement.Decl.evalBinOp_add_one n op107
        rw [hv86] at ev84
        have hbnd_b : ∀ steps,
            IxVM.Refinement.RomBound.HeapDescent h (.enum Core.kexprEnum) xb steps →
            (n + 1) + steps < 549755813888 := by
          intro steps hdb
          have hdp := tm_lam_descent_o hTm ld12 hdb
          have hlt := hbnd_desc (steps + 1) hdp
          omega
        obtain ⟨k_out, steps, hxk, hk_eq, hdb, hlam, hh⟩ :=
          ih _ _ _ _ _ _ (by simp only [List.length_cons, List.length_append]; omega)
            ev84 rfl (n + 1) B xb xk rfl rfl hbnd_b hB
        refine ⟨k_out, steps + 1, hxk, by omega, tm_lam_descent_o hTm ld12 hdb, ?_, hh⟩
        simpa [lamFirstArity, Core.bmeta, Ix.Kernel.Level.zeronessOf] using hlam
      | .BVar_other_n0 (x_i := xi) (y215 := y215)
          (ld12 := ld12) (hne201 := hne201) (op230 := op230) (op221 := op221)
          (he240 := he240) (he254 := he254) .. =>
        injection he240 with hxs; injection hxs with _ hxs; injection hxs with hxk _
        have hxk' : xk = .field (n : F) := hxk
        cases n with
        | zero => exact absurd rfl hne201
        | succ m =>
          have hy215 : y215 = .field (m : F) := IxVM.Refinement.Decl.evalBinOp_sub_succ m op230
          obtain ⟨i_f, rfl, _, rfl⟩ := hE.bvar_of_load ld12
          rw [hy215] at op221
          simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
            Except.ok.injEq, Value.field.injEq] at op221
          have hif : i_f = (m : F) := sub_eq_zero.mp op221
          have hn_lt : m + 1 < 549755813888 := by
            have := hbnd_desc 0 (tm_ptr_descent_zero_o hTm)
            omega
          have hval_i : ZMod.val i_f = m := by
            rw [hif]
            exact ZMod.val_natCast_of_lt (Nat.lt_trans (by omega : m < 549755813888) (by decide))
          refine ⟨m + 1, 0, hxk', by omega, tm_ptr_descent_zero_o hTm, ?_, he254⟩
          simp [lamFirstArity, hval_i])

/-! ## The store's wrappers, as the loads answer them -/

/-- **`Ingress::get_ci` against the store's definition at the address** (`defnAt`), for a load
that is one of the calls `calls` and whose own calls are among them: the store reads a definition
or none at the loaded address; where it reads a definition, the load returned a `Defn` with its
level count and a value pointer representing the value exactly, as the open loaded form; where it
reads none, the load returned no `Defn`. -/
def DefnAtAnswers (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E : Ixon.Env) : Prop :=
  ∀ {xa p ci : SourceValue F} {h m : Heap F} {cs : List (Call F)} {a : Bytes.Address},
    Bytes.RepAddressRef addrTy h a xa →
    ObsFn W "Ingress::get_ci" [xa] h p m cs →
    (⟨"Ingress::get_ci", [xa], h⟩ : Call F) ∈ calls → (∀ c ∈ cs, c ∈ calls) →
    loadValue m p = .ok ci →
    ∃ X : Option (Nat × KExpr), defnAt t E (ixAddr a) = some X ∧
      (∀ n v, X = some (n, v) → ∃ (xty xval xsf xh : SourceValue F),
        ci = .construct "KernelTypes::KConstantInfo" "Defn"
          [.field (n : F), xty, xval, xsf, xh] ∧
        n < 4294967296 ∧ TmOExact (Core.keyOf t) m v xval) ∧
      (X = none → ∀ vs : List (SourceValue F),
        ci ≠ .construct "KernelTypes::KConstantInfo" "Defn" vs)

/-- **`DefnAtAnswers` of a run**: among the calls of a bounded run with its store, where the
readings at the loaded addresses mention only their level parameters (`defnAt_of_load`). -/
theorem defnAtAnswers_of_run {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    (ht : t.check = .ok ())
    (hS : IxVM.Refinement.LoadedReads.RunStore calls E₀)
    (hH : IxVM.Refinement.LoadedReads.HashedRecordsStored calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hlv : LoadedLevelsDefined t E₀ calls) :
    DefnAtAnswers calls t E₀ :=
  fun ha ev hself hsub hld => defnAt_of_load ht hS hH hbd (hlv hself ha) ha ev hsub hld

/-- **A definition value `lam_first_arity` refuses is no wrapper value in the canonical reading**,
for a load that is one of the calls `calls`: where `Ingress::get_ci` returned a definition the
store reads with the value `v`, and `KernelCheck::lam_first_arity` on the value pointer did not
return `(1, k)`, the reading `v` is not `λ x₁ … xₖ, x₁` with every datum `never`
(`lamFirstArity v 0 = none`). The function tests a λ's datum against `Succ(Zero)` syntactically
and `lamFirstArity` tests its zero-ness; the two agree where every datum of the loaded value that
is never zero is stored as `Succ(Zero)`, as the conversion's `binder_level` stores it. -/
def ArityRefusals (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E : Ixon.Env) : Prop :=
  ∀ {xa p xnl xty xval xsf xh r : SourceValue F} {h m m' : Heap F} {cs cs' : List (Call F)}
    {a : Bytes.Address} {n : Nat} {v : KExpr},
    Bytes.RepAddressRef addrTy h a xa →
    ObsFn W "Ingress::get_ci" [xa] h p m cs →
    (⟨"Ingress::get_ci", [xa], h⟩ : Call F) ∈ calls → (∀ c ∈ cs, c ∈ calls) →
    loadValue m p = .ok (.construct "KernelTypes::KConstantInfo" "Defn"
      [xnl, xty, xval, xsf, xh]) →
    defnAt t E (ixAddr a) = some (some (n, v)) →
    ObsFn W "KernelCheck::lam_first_arity" [xval, .field 0] m r m' cs' →
    (⟨"KernelCheck::lam_first_arity", [xval, .field 0], m⟩ : Call F) ∈ calls →
    (∀ xk, r ≠ .tuple [.field 1, xk]) → lamFirstArity v 0 = none

theorem DefnAtAnswers.mono {calls calls' : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E : Ixon.Env} (hsub : ∀ c ∈ calls', c ∈ calls) (h : DefnAtAnswers calls t E) :
    DefnAtAnswers calls' t E :=
  fun ha ev hself hs hld => h ha ev (hsub _ hself) (fun c hc => hsub c (hs c hc)) hld

theorem ArityRefusals.mono {calls calls' : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E : Ixon.Env} (hsub : ∀ c ∈ calls', c ∈ calls) (h : ArityRefusals calls t E) :
    ArityRefusals calls' t E :=
  fun ha ev hself hs hld hX evl hml hnt =>
    h ha ev (hsub _ hself) (fun c hc => hsub c (hs c hc)) hld hX evl (hsub _ hml) hnt

/-- The wrapper arity at the key of an address with no definition is none. -/
theorem wrapAt_of_none {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) {E : Ixon.Env}
    {a : _root_.Address} (h : defnAt t E a = some none) :
    wrapAt t E (Core.keyOf t a) = some none := by
  unfold wrapAt
  rw [show keyAddr t (Core.keyOf t a) = some a from keyAddr_keyOf hwf a]
  simp only [h]

/-- The wrapper arity at the key of an address with a definition is its value's. -/
theorem wrapAt_of_some {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) {E : Ixon.Env}
    {a : _root_.Address} {n : Nat} {v : KExpr} (h : defnAt t E a = some (some (n, v))) :
    wrapAt t E (Core.keyOf t a) = some (lamFirstArity v 0) := by
  unfold wrapAt
  rw [show keyAddr t (Core.keyOf t a) = some a from keyAddr_keyOf hwf a]
  simp only [h]

/-- `consume_wrapper`'s model at a term whose head is a constant applied to an argument. -/
theorem consumeAt_of_spine {Wr : KKey → Option (Option Nat)} {T A : KExpr} {w : KKey}
    {us : List KLevel} {rest : List KExpr} {k : Option Nat}
    (hfn : T.getAppFn = .const w us) (hargs : T.getAppArgs = A :: rest) (hw : Wr w = some k) :
    consumeAt Wr T = some (if k = some (rest.length + 1) then some A else none) := by
  unfold consumeAt appHead
  rw [hfn, hargs]
  simp only [consumeOf, hw, Option.map_some]

theorem appHead_of_const {T : KExpr} {w : KKey} {us : List KLevel}
    (hfn : T.getAppFn = .const w us) : appHead T = some w := by
  unfold appHead
  rw [hfn]

/-! ## `consume_wrapper` -/

/-- **`KernelCheck::consume_wrapper`** on an exact open term whose heap term has no `Let` cell,
against the store's wrappers (`wrapAt`, `consumeAt`), in both directions: where it returns
`(1, a)`, the term is a wrapper applied to exactly its arity and `a` its first argument, the
wrapper's load and arity observed among the calls (`WrapperObserved`); where it does not, nothing
is consumed (`consumeAt` answers `some none`). -/
theorem consume_wrapper_spec {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) {E : Ixon.Env}
    {root : List (Call F)} (hD : DefnAtAnswers root t E) (hA : ArityRefusals root t E)
    {T : KExpr} {xt r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::consume_wrapper" [xt] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (hT : TmOExact (Core.keyOf t) h T xt) (hlf : LetFree h xt) :
    (∀ xa, r = .tuple [.field 1, xa] →
      ∃ (A : KExpr) (w : KKey) (n : Nat), consumeAt (wrapAt t E) T = some (some A) ∧
        appHead T = some w ∧ wrapAt t E w = some (some n) ∧ WrapperObserved root t w n ∧
        TmOExact (Core.keyOf t) h' A xa ∧ LetFree h' xa) ∧
    ((∀ xa, r ≠ .tuple [.field 1, xa]) → consumeAt (wrapAt t E) T = some none) := by
  have refuse : r = .tuple [.field 0, xt] → ∀ xa, r ≠ .tuple [.field 1, xa] := by
    intro he xa hr
    rw [he] at hr
    injection hr with hxs; injection hxs with h01 _
    exact absurd (Value.field.inj h01) zero_ne_one
  -- the shared reading of the spine, the load and the arity
  have arity : ∀ {m2 m96 m157 m224 : Heap F} {x_h x_args x_w w55 x_a x_rest p104 w127 w128 x_v
      w129 w130 x_k y214 x222 : SourceValue F} {cs12 cs110 cs168 cs233 : List (Call F)},
      ObsFn W "KernelTypes::collect_spine" [xt] h (.tuple [x_h, x_args]) m2 cs12 →
      loadValue m2 x_h = .ok (.construct "KernelTypes::KExprNode" "Const" [x_w, w55]) →
      loadValue m2 x_args =
        .ok (.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Cons" [x_a, x_rest]) →
      ObsFn W "Ingress::get_ci" [x_w] m2 p104 m96 cs110 →
      loadValue m96 p104 = .ok (.construct "KernelTypes::KConstantInfo" "Defn"
        [w127, w128, x_v, w129, w130]) →
      ObsFn W "KernelCheck::lam_first_arity" [x_v, .field 0] m96 (.tuple [.field 1, x_k]) m157
        cs168 →
      ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [x_rest] m157 x222 m224 cs233 →
      evalBinOp .add x222 (.field 1) = .ok y214 →
      (⟨"Ingress::get_ci", [x_w], m2⟩ : Call F) ∈ cs → (∀ c ∈ cs110, c ∈ cs) →
      (⟨"KernelCheck::lam_first_arity", [x_v, .field 0], m96⟩ : Call F) ∈ cs →
      (∀ c ∈ cs168, c ∈ cs) →
      (⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [x_rest], m157⟩ : Call F) ∈ cs →
      ∃ (aw : Bytes.Address) (us : List KLevel) (A : KExpr) (rest : List KExpr) (k : Nat),
        T.getAppFn = .const (Core.keyOf t (ixAddr aw)) us ∧ T.getAppArgs = A :: rest ∧
        wrapAt t E (Core.keyOf t (ixAddr aw)) = some (some k) ∧
        WrapperObserved root t (Core.keyOf t (ixAddr aw)) k ∧
        TmOExact (Core.keyOf t) m224 A x_a ∧ LetFree m224 x_a ∧
        x_k = .field (k : F) ∧ y214 = .field ((rest.length + 1 : Nat) : F) ∧
        k < 549755813888 ∧ rest.length < 549755813888 := by
    intro m2 m96 m157 m224 x_h x_args x_w w55 x_a x_rest p104 w127 w128 x_v w129 w130 x_k y214
      x222 cs12 cs110 cs168 cs233 ev14 ld47 ld77 ev112 ld106 ev170 ev235 op229 hm1 hs1 hm2 hs2
      hm3
    obtain ⟨hH, hHl, hAs⟩ := collect_spine_letFree_spec hT hlf ev14
    obtain ⟨aw, us, hfn, haw, -⟩ := hH.const_of_load ld47
    obtain ⟨A, rest, hargs, hA', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hAs ld77
    obtain ⟨X, hX, hsome, hnone⟩ := hD haw ev112 (hroot _ hm1)
      (fun c hc' => hroot c (hs1 c hc')) ld106
    cases X with
    | none => exact absurd rfl (hnone rfl _)
    | some nv =>
      obtain ⟨n, v⟩ := nv
      obtain ⟨xty, xval, xsf, xh, hci, -, htm⟩ := hsome n v rfl
      have hargs' := (Value.construct.inj hci).2.2
      simp only [List.cons.injEq, and_true] at hargs'
      obtain ⟨-, -, rfl, -, -⟩ := hargs'
      have hbnd_la : ∀ steps,
          IxVM.Refinement.RomBound.HeapDescent m96 (.enum Core.kexprEnum) x_v steps →
          0 + steps < 549755813888 := by
        intro steps hdesc
        have hlt := IxVM.Refinement.RomBound.bounded_descent_lt hbnd
          (c := ⟨"KernelCheck::lam_first_arity", [x_v, .field 0], m96⟩) hm2
          List.mem_cons_self hdesc
        simpa using hlt
      obtain ⟨k_out, steps, hxk, hk_steps, hdesc, hlam, hm157⟩ :=
        lam_first_arity_one _ _ _ _ _ _ ev170 rfl 0 v x_v x_k rfl rfl hbnd_la htm
      have hk_lt : k_out < 549755813888 := by
        have := hbnd_la steps hdesc
        omega
      have e_ci := ev112.heap_extends
      have hrest157 : RepList kexprListEnum (TmLF (Core.keyOf t)) m157 rest x_rest := by
        rw [hm157]
        exact repList_heapMono₂ kexprListEnum tmLF_heapMono₂ e_ci hrest
      have hlen_lt : rest.length < 549755813888 :=
        IxVM.Refinement.RomBound.bounded_length_lt hbnd
          (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [x_rest], m157⟩) hm3
          List.mem_cons_self hrest157
      obtain ⟨hx222, hm224⟩ := kexpr_length ev235 hrest157
      rw [hx222] at op229
      have hy214 : y214 = .field ((rest.length + 1 : Nat) : F) :=
        IxVM.Refinement.Decl.evalBinOp_add_one rest.length op229
      have hw : wrapAt t E (Core.keyOf t (ixAddr aw)) = some (some k_out) := by
        rw [wrapAt_of_some hwf hX, hlam]
      have ext : Heap.Extends m2 m224 := by
        rw [hm224, hm157]; exact e_ci
      refine ⟨aw, us, A, rest, k_out, hfn, hargs, hw, ?_, hA'.1.mono ext, hA'.2.mono ext, hxk,
        hy214, hk_lt, hlen_lt⟩
      exact ⟨aw, x_w, p104, _, _, x_v, _, _, m2, m96, m157, cs110, cs168, rfl, haw, ev112,
        fun c hc' => hroot c (hs1 c hc'), ld106, hroot _ hm2, hxk ▸ ev170,
        fun c hc' => hroot c (hs2 c hc'), hk_lt⟩
  match Obs.«KernelCheck::consume_wrapper».obsx ev with
  | .other (ev14 := ev14) (ld47 := ld47) (hne363 := hne) (he371 := he) .. =>
    obtain ⟨hH, hHl, hAs⟩ := collect_spine_letFree_spec hT hlf ev14
    refine ⟨fun xa hr => absurd hr (refuse he xa), fun _ => ?_⟩
    have hnc := tmOExact_not_const hH hHl.notLet ld47 hne
    unfold consumeAt appHead
    cases hfn : Ix.Kernel.Expr.getAppFn T with
    | const w us => exact absurd hfn (hnc w us)
    | _ => rfl
  | .Const_other (ev14 := ev14) (ld47 := ld47) (ld77 := ld77) (hne339 := hne) (he347 := he) .. =>
    obtain ⟨hH, hHl, hAs⟩ := collect_spine_letFree_spec hT hlf ev14
    refine ⟨fun xa hr => absurd hr (refuse he xa), fun _ => ?_⟩
    obtain ⟨aw, us, hfn, haw, -⟩ := hH.const_of_load ld47
    have hnil : Ix.Kernel.Expr.getAppArgs T = [] := by
      cases hl : Ix.Kernel.Expr.getAppArgs T with
      | nil => rfl
      | cons z zs =>
        rw [hl] at hAs
        cases hAs with
        | cons cell _ _ =>
          have hld := Lib.load_enum_cell cell
          rw [ld77] at hld
          injection hld with hv
          exact absurd hv (hne _ rfl)
    unfold consumeAt appHead
    rw [hfn, hnil]
    rfl
  | .Const_Cons_other (ev14 := ev14) (ld47 := ld47) (ld77 := ld77) (ev112 := ev112)
      (ld106 := ld106) (hne315 := hne) (he323 := he) (hc338 := hc) .. =>
    obtain ⟨hH, hHl, hAs⟩ := collect_spine_letFree_spec hT hlf ev14
    refine ⟨fun xa hr => absurd hr (refuse he xa), fun _ => ?_⟩
    obtain ⟨aw, us, hfn, haw, -⟩ := hH.const_of_load ld47
    obtain ⟨A, rest, hargs, hA', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hAs ld77
    obtain ⟨X, hX, hsome, hnone⟩ := hD haw ev112 (hroot _ (by rw [hc]; simp))
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) ld106
    cases X with
    | some nv =>
      obtain ⟨n, v⟩ := nv
      obtain ⟨_, _, _, _, hci, -⟩ := hsome n v rfl
      exact absurd hci (hne _ rfl)
    | none =>
      rw [consumeAt_of_spine hfn hargs (wrapAt_of_none hwf hX)]
      simp
  | .Const_Cons_Defn_other (ev14 := ev14) (ld47 := ld47) (ld77 := ld77) (ev112 := ev112)
      (ld106 := ld106) (ev170 := ev170) (he299 := he) (hc314 := hc) (hnt0 := hnt) .. =>
    obtain ⟨hH, hHl, hAs⟩ := collect_spine_letFree_spec hT hlf ev14
    refine ⟨fun xa hr => absurd hr (refuse he xa), fun _ => ?_⟩
    obtain ⟨aw, us, hfn, haw, -⟩ := hH.const_of_load ld47
    obtain ⟨A, rest, hargs, hA', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hAs ld77
    obtain ⟨X, hX, hsome, hnone⟩ := hD haw ev112 (hroot _ (by rw [hc]; simp))
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) ld106
    cases X with
    | none => exact absurd rfl (hnone rfl _)
    | some nv =>
      obtain ⟨n, v⟩ := nv
      have hno := hA haw ev112 (hroot _ (by rw [hc]; simp))
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) ld106 hX ev170
        (hroot _ (by rw [hc]; simp)) hnt
      rw [consumeAt_of_spine hfn hargs (wrapAt_of_some hwf hX), hno]
      simp
  | .Const_Cons_Defn_n1_bind_other (ev14 := ev14) (ld47 := ld47) (ld77 := ld77) (ev112 := ev112)
      (ld106 := ld106) (ev170 := ev170) (ev235 := ev235) (op229 := op229) (op220 := op220)
      (hne268 := hne) (he276 := he) (hc291 := hc) .. =>
    refine ⟨fun xa hr => absurd hr (refuse he xa), fun _ => ?_⟩
    obtain ⟨aw, us, A, rest, k, hfn, hargs, hw, -, -, -, rfl, rfl, hk, hlen⟩ :=
      arity ev14 ld47 ld77 ev112 ld106 ev170 ev235 op229 (by rw [hc]; simp)
        (fun c hc' => by rw [hc]; simp [hc']) (by rw [hc]; simp)
        (fun c hc' => by rw [hc]; simp [hc']) (by rw [hc]; simp)
    rw [consumeAt_of_spine hfn hargs hw]
    have hkne : k ≠ rest.length + 1 := by
      intro heq
      have hv := evalBinOp_sub_field op220
      rw [heq, sub_self] at hv
      exact hne hv
    simp [hkne]
  | .Const_Cons_Defn_n1_bind_n0 (ev14 := ev14) (ld47 := ld47) (ld77 := ld77) (ev112 := ev112)
      (ld106 := ld106) (ev170 := ev170) (ev235 := ev235) (op229 := op229) (op220 := op220)
      (he252 := he) (he266 := hh) (hc267 := hc) .. =>
    obtain ⟨aw, us, A, rest, k, hfn, hargs, hw, hobs, hA1, hA2, rfl, rfl, hk, hlen⟩ :=
      arity ev14 ld47 ld77 ev112 ld106 ev170 ev235 op229 (by rw [hc]; simp)
        (fun c hc' => by rw [hc]; simp [hc']) (by rw [hc]; simp)
        (fun c hc' => by rw [hc]; simp [hc']) (by rw [hc]; simp)
    have hkeq : k = rest.length + 1 := binop_sub_eq_zero_nat (by omega) (by omega) op220
    refine ⟨fun xa hr => ?_, fun hnt => absurd he (hnt _)⟩
    rw [he] at hr
    injection hr with hxs; injection hxs with _ hxs; injection hxs with hxa _
    subst hxa hh
    refine ⟨A, _, k, ?_, appHead_of_const hfn, hw, hobs, hA1, hA2⟩
    rw [consumeAt_of_spine hfn hargs hw]
    simp [hkeq]

/-! ## `wrap_rel` at full consumption -/

/-- A leaf of the heap term (no application, binder, projection or `let` cell) is related to
itself. -/
theorem fullConsObs_leaf {κ : _root_.Address → KKey} {Wr : KKey → Option (Option Nat)}
    {O : KKey → Nat → Prop} {h : Heap F} {G : KExpr} {p v : SourceValue F}
    (hG : TmOExact κ h G p) (ld : loadValue h p = .ok v)
    (hApp : ∀ vs : List (SourceValue F), vs.length = 2 → v ≠ .construct kexprEnum "App" vs)
    (hLam : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Lam" vs)
    (hAll : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Forall" vs)
    (hProj : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Proj" vs)
    (hLet : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Let" vs) :
    FullConsObs Wr O G G := by
  obtain ⟨k, rep⟩ := hG
  cases rep with
  | bvarLocal _ _ _ => exact .bvar _
  | bvarFree _ _ _ hd => omega
  | sort _ _ => exact .sort (LvEq.refl _)
  | const _ _ _ => exact .const (LvEqList.refl _)
  | litNat _ _ _ => exact .lit _
  | litStr _ _ _ => exact .lit _
  | app cell _ _ =>
    have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv
    exact (hApp _ rfl hv).elim
  | lam cell _ _ _ =>
    have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv
    exact (hLam _ rfl hv).elim
  | forallE cell _ _ _ =>
    have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv
    exact (hAll _ rfl hv).elim
  | letE cell _ _ _ =>
    have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv
    exact (hLet _ rfl hv).elim
  | proj cell _ _ =>
    have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv
    exact (hProj _ rfl hv).elim

private theorem wrap_full_family {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) {E : Ixon.Env}
    {root : List (Call F)} (hD : DefnAtAnswers root t E) (hA : ArityRefusals root t E) :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → r = .field 1 → IxVM.Consistency.Bounded cs →
      (∀ c ∈ cs, c ∈ root) →
      ((fname = "KernelCheck::wrap_rel" →
        ∀ (G D : KExpr) (xg xd : SourceValue F),
          args = [.field 1, xg, xd] → TmOExact (Core.keyOf t) h G xg → LetFree h xg →
          TmOExact (Core.keyOf t) h D xd →
          FullConsObs (wrapAt t E) (WrapperObserved root t) G D) ∧
       (fname = "KernelCheck::wrap_dom" →
        ∀ (T T2 : KExpr) (xt xt2 : SourceValue F),
          args = [.field 1, xt, xt2] → TmOExact (Core.keyOf t) h T xt → LetFree h xt →
          TmOExact (Core.keyOf t) h T2 xt2 →
          ∃ c : KExpr, ConsumesObs (wrapAt t E) (WrapperObserved root t) T c ∧
            consumeAt (wrapAt t E) c = some none ∧
            FullConsObs (wrapAt t E) (WrapperObserved root t) c T2) ∧
       (fname = "KernelCheck::wrap_binder" →
        ∀ (T B T2 B2 : KExpr) (ℓ ℓ2 : KLevel) (xt xb xm xt2 xb2 xm2 : SourceValue F),
          args = [.field 1, xt, xb, xm, xt2, xb2, xm2] →
          TmOExact (Core.keyOf t) h T xt → LetFree h xt →
          TmOExact (Core.keyOf t) h B xb → LetFree h xb → RepKLevel h ℓ xm →
          TmOExact (Core.keyOf t) h T2 xt2 → TmOExact (Core.keyOf t) h B2 xb2 →
          RepKLevel h ℓ2 xm2 →
          (bmeta ℓ).pw = (bmeta ℓ2).pw ∧
          (∃ c : KExpr, ConsumesObs (wrapAt t E) (WrapperObserved root t) T c ∧
            consumeAt (wrapAt t E) c = some none ∧
            FullConsObs (wrapAt t E) (WrapperObserved root t) c T2) ∧
          FullConsObs (wrapAt t E) (WrapperObserved root t) B B2)) :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => r = .field 1 → IxVM.Consistency.Bounded cs →
      (∀ c ∈ cs, c ∈ root) →
      ((fname = "KernelCheck::wrap_rel" →
        ∀ (G D : KExpr) (xg xd : SourceValue F),
          args = [.field 1, xg, xd] → TmOExact (Core.keyOf t) h G xg → LetFree h xg →
          TmOExact (Core.keyOf t) h D xd →
          FullConsObs (wrapAt t E) (WrapperObserved root t) G D) ∧
       (fname = "KernelCheck::wrap_dom" →
        ∀ (T T2 : KExpr) (xt xt2 : SourceValue F),
          args = [.field 1, xt, xt2] → TmOExact (Core.keyOf t) h T xt → LetFree h xt →
          TmOExact (Core.keyOf t) h T2 xt2 →
          ∃ c : KExpr, ConsumesObs (wrapAt t E) (WrapperObserved root t) T c ∧
            consumeAt (wrapAt t E) c = some none ∧
            FullConsObs (wrapAt t E) (WrapperObserved root t) c T2) ∧
       (fname = "KernelCheck::wrap_binder" →
        ∀ (T B T2 B2 : KExpr) (ℓ ℓ2 : KLevel) (xt xb xm xt2 xb2 xm2 : SourceValue F),
          args = [.field 1, xt, xb, xm, xt2, xb2, xm2] →
          TmOExact (Core.keyOf t) h T xt → LetFree h xt →
          TmOExact (Core.keyOf t) h B xb → LetFree h xb → RepKLevel h ℓ xm →
          TmOExact (Core.keyOf t) h T2 xt2 → TmOExact (Core.keyOf t) h B2 xb2 →
          RepKLevel h ℓ2 xm2 →
          (bmeta ℓ).pw = (bmeta ℓ2).pw ∧
          (∃ c : KExpr, ConsumesObs (wrapAt t E) (WrapperObserved root t) T c ∧
            consumeAt (wrapAt t E) c = some none ∧
            FullConsObs (wrapAt t E) (WrapperObserved root t) c T2) ∧
          FullConsObs (wrapAt t E) (WrapperObserved root t) B B2)))
    (fun fname args h r h' cs ev ih hr hbnd hroot => by
      subst hr
      have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
        fun hs => RomBound.bounded_mono hbnd hs
      refine ⟨fun hfn G D xg xd hargs hG hGl hD => ?_,
        fun hfn T T2 xt xt2 hargs hT hTl hT2 => ?_,
        fun hfn T B T2 B2 ℓ ℓ2 xt xb xm xt2 xb2 xm2 hargs hT hTl hB hBl hℓ hT2 hB2 hℓ2 => ?_⟩
      · subst hfn hargs
        match Obs.«KernelCheck::wrap_rel».obs ev with
        | .other_other_App_App_other (he351 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .other_other_App_other (he358 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .other_other_Lam_other (he476 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .other_other_Forall_other (he594 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .other_other_Proj_Proj_other (he746 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .other_other_Proj_other (he753 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .Let_Let_n1_other (he166 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .Let_Let_other (he173 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .Let_other (he180 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .other_Let (he224 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .Let_Let_n1_n1 (ld12 := ld12) .. =>
          exact (hGl.not_let_val ld12 _ rfl rfl).elim
        | .other_other_App_App_n1 (x_f := xf) (x_a := xa) (x_f2 := xf2) (x_a2 := xa2)
            (ld242 := ldg) (ld271 := ldd) (ev303 := ev1) (ev329 := ev2) (hc346 := hc) .. =>
          subst hc
          obtain ⟨Ef, Ea, rfl, hEf, hEa⟩ := hG.app_of_load ldg
          obtain ⟨Ef2, Ea2, rfl, hEf2, hEa2⟩ := hD.app_of_load ldd
          obtain ⟨lf, la⟩ := hGl.app_inv ldg
          have e1 := ev1.heap_extends
          exact .app
            ((ih _ _ _ _ _ _ (by simp only [List.length_cons, List.length_append]; omega) ev1 rfl
              (sub fun z hz => by simp [hz]) (fun z hz => hroot z (by simp [hz]))).1 rfl
              Ef Ef2 xf xf2 rfl hEf lf hEf2)
            ((ih _ _ _ _ _ _ (by simp only [List.length_cons, List.length_append]; omega) ev2 rfl
              (sub fun z hz => by simp [hz]) (fun z hz => hroot z (by simp [hz]))).1 rfl
              Ea Ea2 xa xa2 rfl (hEa.mono e1) (la.mono e1) (hEa2.mono e1))
        | .other_other_Lam_Lam (x_t := xt) (x_b := xb) (x_m := xm)
            (x_t2 := xt2) (x_b2 := xb2) (x_m2 := xm2)
            (ld242 := ldg) (ld394 := ldd) (ev422 := ev1) (hc471 := hc) .. =>
          subst hc
          obtain ⟨T, B, ℓ, rfl, hT, hB, hℓ⟩ := hG.lam_of_load ldg
          obtain ⟨T2, B2, ℓ2, rfl, hT2, hB2, hℓ2⟩ := hD.lam_of_load ldd
          obtain ⟨lt, lb⟩ := hGl.lam_inv ldg
          obtain ⟨hpw, ⟨c, hcs, hstop, hdom⟩, hbody⟩ :=
            (ih _ _ _ _ _ _ (by simp only [List.length_cons, List.length_append]; omega) ev1 rfl
              (sub fun z hz => by simp [hz]) (fun z hz => hroot z (by simp [hz]))).2.2 rfl
              T B T2 B2 ℓ ℓ2 xt xb xm xt2 xb2 xm2 rfl hT lt hB lb hℓ hT2 hB2 hℓ2
          exact .lam hpw hcs hstop hdom hbody
        | .other_other_Forall_Forall (x_t := xt) (x_b := xb) (x_m := xm)
            (x_t2 := xt2) (x_b2 := xb2) (x_m2 := xm2)
            (ld242 := ldg) (ld512 := ldd) (ev540 := ev1) (hc589 := hc) .. =>
          subst hc
          obtain ⟨T, B, ℓ, rfl, hT, hB, hℓ⟩ := hG.forallE_of_load ldg
          obtain ⟨T2, B2, ℓ2, rfl, hT2, hB2, hℓ2⟩ := hD.forallE_of_load ldd
          obtain ⟨lt, lb⟩ := hGl.forallE_inv ldg
          obtain ⟨hpw, ⟨c, hcs, hstop, hdom⟩, hbody⟩ :=
            (ih _ _ _ _ _ _ (by simp only [List.length_cons, List.length_append]; omega) ev1 rfl
              (sub fun z hz => by simp [hz]) (fun z hz => hroot z (by simp [hz]))).2.2 rfl
              T B T2 B2 ℓ ℓ2 xt xb xm xt2 xb2 xm2 rfl hT lt hB lb hℓ hT2 hB2 hℓ2
          exact .forallE hpw hcs hstop hdom hbody
        | .other_other_Proj_Proj_n1 (x_s := xs) (x_i := xi) (x_e := xe)
            (x_s2 := xs2) (x_i2 := xi2) (x_e2 := xe2) (m654 := m604)
            (x662 := x612) (y663 := y613) (m664 := m614) (v698 := v648)
            (ld242 := ldg) (ld630 := ldd) (ev675 := ev625) (op712 := op662)
            (ev697 := ev647) (op669 := op619) (ev724 := ev674) (hc741 := hc) .. =>
          subst hc
          obtain ⟨sa, fa, Ea, rfl, rfl, hsa, hEa⟩ := hG.proj_of_load ldg
          obtain ⟨sb, fb, Eb, rfl, rfl, hsb, hEb⟩ := hD.proj_of_load ldd
          have le := hGl.proj_inv ldg
          obtain ⟨haddr, rfl⟩ := Lib.address_eq_spec ev625 hsa hsb
          obtain ⟨hiz, rfl⟩ := Lib.is_zero_spec ev647
          have hs_eq : sa = sb := by
            by_cases hab : sa = sb
            · exact hab
            · rw [ite_eq_right hab] at haddr
              rw [haddr, hiz] at op619
              simp [evalBinOp, bind, Except.bind, pure, Except.pure] at op619
          subst hs_eq
          have hv648 : v648 = .field 0 := by
            by_cases h0 : v648 = .field 0
            · exact h0
            · rw [hiz, ite_eq_right h0, haddr] at op619
              simp [evalBinOp, bind, Except.bind, pure, Except.pure] at op619
          rw [hv648] at op662
          simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
            Except.ok.injEq, Value.field.injEq] at op662
          have hfeq : fa = fb := sub_eq_zero.mp op662
          subst hfeq
          exact .proj
            ((ih _ _ _ _ _ _ (by simp only [List.length_cons, List.length_append]; omega) ev674
              rfl (sub fun z hz => by simp [hz]) (fun z hz => hroot z (by simp [hz]))).1 rfl
              Ea Eb xe xe2 rfl hEa le hEb)
        | .other_other_other (ld12 := ld12) (hne183 := hLet) (ld242 := ldg) (hne361 := hApp)
            (hne479 := hLam) (hne597 := hAll) (hne756 := hProj) (ev765 := evq) .. =>
          obtain rfl := kexpr_struct_eq_tmOExact hG hD evq
          rw [ld12] at ldg
          injection ldg with hv
          subst hv
          exact fullConsObs_leaf hG ld12 hApp hLam hAll hProj hLet
      · subst hfn hargs
        match Obs.«KernelCheck::wrap_dom».obsx ev with
        | .Let (ld12 := ld12) .. => exact (hTl.not_let_val ld12 _ rfl rfl).elim
        | .other_n0_n1 (hv_fnfqvmln := hsm) .. =>
          exact absurd (Value.field.inj hsm) one_ne_zero
        | .other_n0_other_n1_bind (hv_fnfqvmln := hsm) .. =>
          exact absurd (Value.field.inj hsm) one_ne_zero
        | .other_n0_other_other (hv_fnfqvmln := hsm) .. =>
          exact absurd (Value.field.inj hsm) one_ne_zero
        | .other_other_n1_bind (m108 := m108) (x_a := xa) (ev121 := evc) (ev153 := evd)
            (hc170 := hc) .. =>
          subst hc
          obtain ⟨hyes, -⟩ := consume_wrapper_spec hwf hD hA evc (sub fun z hz => by simp [hz])
            (fun z hz => hroot z (by simp [hz])) hT hTl
          obtain ⟨A, w, n, hcons, hhead, hw, hobs, hA', hAl⟩ := hyes xa rfl
          obtain ⟨c, hcs, hstop, hfull⟩ :=
            (ih _ _ _ _ _ _ (by simp only [List.length_cons, List.length_append]; omega) evd rfl
              (sub fun z hz => by simp [hz]) (fun z hz => hroot z (by simp [hz]))).2.1 rfl
              A T2 xa xt2 rfl hA' hAl (hT2.mono evc.heap_extends)
          exact ⟨c, .step hcons hhead hw hobs hcs, hstop, hfull⟩
        | .other_other_other (m108 := m108) (ev121 := evc) (ev_sarmpwvb := evr) (hc176 := hc)
            (hnt0 := hnt) .. =>
          subst hc
          obtain ⟨-, hno⟩ := consume_wrapper_spec hwf hD hA evc (sub fun z hz => by simp [hz])
            (fun z hz => hroot z (by simp [hz])) hT hTl
          have e1 := evc.heap_extends
          have hfull :=
            (ih _ _ _ _ _ _ (by simp only [List.length_cons, List.length_append]; omega) evr rfl
              (sub fun z hz => by simp [hz]) (fun z hz => hroot z (by simp [hz]))).1 rfl
              T T2 xt xt2 rfl (hT.mono e1) (hTl.mono e1) (hT2.mono e1)
          exact ⟨T, .refl T, hno hnt, hfull⟩
      · subst hfn hargs
        match Obs.«KernelCheck::wrap_binder».obs ev with
        | .n1_other (he98 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .other (he105 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .n1_n1 (m2 := m2) (m37 := m37) (ev15 := ev15) (ev50 := ev50) (ev76 := ev76)
            (hc93 := hc) .. =>
          subst hc
          have hpw : (bmeta ℓ).pw = (bmeta ℓ2).pw := IxVM.Refinement.Decl.pw_eq_one hℓ hℓ2 ev15
          have e1 := ev15.heap_extends
          have e2 := ev50.heap_extends
          have hdom :=
            (ih _ _ _ _ _ _ (by simp only [List.length_cons, List.length_append]; omega) ev50 rfl
              (sub fun z hz => by simp [hz]) (fun z hz => hroot z (by simp [hz]))).2.1 rfl
              T T2 xt xt2 rfl (hT.mono e1) (hTl.mono e1) (hT2.mono e1)
          have hbody :=
            (ih _ _ _ _ _ _ (by simp only [List.length_cons, List.length_append]; omega) ev76 rfl
              (sub fun z hz => by simp [hz]) (fun z hz => hroot z (by simp [hz]))).1 rfl
              B B2 xb xb2 rfl (hB.mono (e1.trans e2)) (hBl.mono (e1.trans e2))
              (hB2.mono (e1.trans e2))
          exact ⟨hpw, hdom, hbody⟩)

/-- **`KernelCheck::wrap_rel(1, g, d)` returning `1`** on a generated term `g` whose heap term has
no `Let` cell and a declared term `d`, both exact and open: `d` is the full consumption of `g`
under the store's wrappers (`FullConsObs (wrapAt t E)`), every consumed wrapper's load and arity
observed among the calls (`WrapperObserved`). -/
theorem wrap_rel_full_spec {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) {E : Ixon.Env}
    {root : List (Call F)} (hD : DefnAtAnswers root t E) (hA : ArityRefusals root t E)
    {G D : KExpr} {xg xd : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::wrap_rel" [.field 1, xg, xd] h (.field 1) h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (hG : TmOExact (Core.keyOf t) h G xg) (hGl : LetFree h xg)
    (hDt : TmOExact (Core.keyOf t) h D xd) :
    FullConsObs (wrapAt t E) (WrapperObserved root t) G D :=
  (wrap_full_family hwf hD hA _ _ _ _ _ _ ev rfl hbnd hroot).1 rfl G D xg xd rfl hG hGl hDt

/-! ## The form state of a family record -/

/-- **One member's step of the form state** (`canonical_rules_at_pos`): from the form `a` of the
members before it to the form `b` with it, where `eq` says its declared type is the reconstruction
and `full` that it is the reconstruction's full consumption. The form is `0` while every member is
both, `1` once one is the reconstruction only, `2` once one is the full consumption only; a form
`1` or `2` is kept. -/
structure FormStep (a b : Nat) (eq full : Prop) : Prop where
  le : b ≤ 2
  zero : b = 0 → a = 0 ∧ eq ∧ full
  one : b = 1 → eq
  two : b = 2 → full
  keep1 : a = 1 → b = 1
  keep2 : a = 2 → b = 2

theorem form_field_eq {a : Nat} (c : Nat) (ha : a ≤ 2) (hc : c ≤ 2)
    (h : (a : F) = ((c : Nat) : F)) : a = c :=
  natCast_inj_small (by omega) (by omega) h

/-- **`KernelCheck::canonical_rules_at_pos` under any role context**, at the position `k` of the
flattened family `es` and the form `a` of the members before this one: with the reconstructed
type `R` at `k` (`build_rec_type`), the form `b` it returns is a step from `a` (`FormStep`) in
which the declared type `ty` is `R` (`kexpr_struct_eq`) or the full consumption of `R` under the
store's wrappers, every consumed wrapper observed among the calls (`wrap_rel(1, R, ty)`,
`wrap_rel_full_spec`); and every stored rule follows the reconstructed body under the λs of the
declared type (`populate_rules`, `compare_rules`), as under a group's validation. The builders'
and the comparison's results are taken at this call's arguments, on any heap extending the
call's; the reconstructed type's heap term is taken without a `Let` cell
(`build_rec_type_letFree`), which `wrap_rel` is sound for. -/
theorem canonical_rules_at_pos_form_spec {t : Ix.Kernel.RoleTable} (hwf : t.wf = true)
    {E : Ixon.Env} {V : ReconView}
    {es : List FlatEntry} {fop : List Nat} {off nP nMot nMin nl k a : Nat} {ty : KExpr}
    {peers : List _root_.Address} {stored : List (Nat × Nat × KExpr)} {self : IndData}
    {ba : Bytes.Address} {NF : _root_.Address → Nat → Nat → Nat → Prop}
    {x_rc x_flat x_nc x_pblk x_pidx x_np x_lvls x_peers x_fop x_rules x_ty x_pty
      x_pnl x_pni x_elim x_uo r : SourceValue F} {h h' : Heap F}
    {cs root : List (Call F)}
    (ev : ObsFn W "KernelCheck::canonical_rules_at_pos"
      [x_rc, x_flat, .field (k : F), x_nc, x_pblk, x_pidx, x_np, .field (nMot : F), .field (nMin : F), x_lvls, x_peers,
        x_fop, x_rules, x_ty, x_pty, x_pnl, x_pni, x_elim, x_uo, .field (a : F)] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (hD : DefnAtAnswers root t E) (hA : ArityRefusals root t E) (ha : a ≤ 2)
    (hes : RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h es x_flat)
    (hk : k < es.length) (hlen : es.length < 2 ^ 39)
    (hnMot : nMot < 4294967296) (hnMin : nMin < 4294967296)
    (hty : TmOExact (Core.keyOf t) h ty x_ty)
    (build_rec_type : ∀ {m m' : Heap F} {v : SourceValue F} {cs' : List (Call F)},
      ObsFn W "KernelCheck::build_rec_type"
        [x_rc, x_pty, x_pnl, x_np, x_pni, x_elim, x_uo, x_flat, x_fop, .field (k : F)]
        m v m' cs' → Heap.Extends h m → IxVM.Consistency.Bounded cs' → (∀ c ∈ cs', c ∈ root) →
      Heap.Extends m m' ∧ ∃ R, TmOExact (Core.keyOf t) m' R v ∧
        Eventually fun f => recTypeAt V f es off nP k = some R)
    (build_rec_type_letFree : ∀ {m m' : Heap F} {v : SourceValue F} {cs' : List (Call F)},
      ObsFn W "KernelCheck::build_rec_type"
        [x_rc, x_pty, x_pnl, x_np, x_pni, x_elim, x_uo, x_flat, x_fop, .field (k : F)]
        m v m' cs' → Heap.Extends h m → LetFree m' v)
    (build_all_minors : ∀ {m m' : Heap F} {v : SourceValue F} {cs' : List (Call F)},
      ObsFn W "KernelCheck::build_all_minors"
        [x_rc, x_flat, x_fop, x_np, .field (es.length : F), x_np, x_elim] m v m' cs' →
      Heap.Extends h m → IxVM.Consistency.Bounded cs' → (∀ c ∈ cs', c ∈ root) →
      Heap.Extends m m' ∧ ∃ Ms, RepList kexprListEnum (TmOExact (Core.keyOf t)) m' Ms v ∧
        Eventually fun f =>
          allMinors V f es fop nP es.length nP (elimLevel off) es 0 0 = some Ms)
    (rules_at_pos : ∀ {h₀ h₁ h₂ h₃ : Heap F} {vcb vcanon v w x_aux x_sp x_ou : SourceValue F}
      {cs₁ cs₂ cs₃ : List (Call F)} (e : FlatEntry) (Ms : List KExpr),
      ObsFn W "KernelCheck::ctors_before_pos" [x_flat, .field (k : F), .field 0] h₀ vcb h₁ cs₁ →
      ObsFn W "KernelCheck::populate_rules"
        [x_rc, x_nc, vcb, x_pblk, x_pidx, x_np, .field (nMot : F), .field (nMin : F), x_ou,
          x_lvls, x_flat, x_peers, x_fop, x_aux, x_sp, .field 0, x_elim] h₁ vcanon h₂ cs₂ →
      ObsFn W "KernelCheck::compare_rules"
        [x_rules, vcanon, x_np, .field (nMot : F), .field (nMin : F), x_pblk, x_pidx, x_nc,
          .field 0, x_elim, x_ty, vcb] h₂ v h₃ cs₃ →
      Heap.Extends h h₀ → IxVM.Consistency.Bounded cs₂ → IxVM.Consistency.Bounded cs₃ →
      (∀ c ∈ cs₁, c ∈ root) → (∀ c ∈ cs₂, c ∈ root) → (∀ c ∈ cs₃, c ∈ root) →
      es[k]? = some e → FlatEntryRepExact (Core.keyOf t) h₀ e (.tuple [w, x_aux, x_sp, x_ou]) →
      nMot = es.length → nMin = Ms.length →
      (Eventually fun f =>
        allMinors V f es fop nP es.length nP (elimLevel off) es 0 0 = some Ms) →
      Heap.Extends h₀ h₁ ∧ Heap.Extends h₁ h₂ ∧ Heap.Extends h₂ h₃ ∧
        ∃ (cbk : Nat) (bodies : List KExpr), ctorsBefore V es k = some cbk ∧
          (Eventually fun f => ruleBodiesAt V f es off nP nMot nMin nl k peers = some bodies) ∧
          stored.length ≤ self.nctors ∧
          ∀ (c : Nat) (ru : Nat × Nat × KExpr), stored[c]? = some ru →
            ru.1 = c ∧ c < self.nctors ∧ NF (ixAddr ba) self.idx c ru.2.1 ∧
              ∃ cb, bodies[c]? = some cb ∧
                RuleFollows ty nP nMot nMin (cbk + c) ru.2.1 (elimLevel off) ru.2.2 cb) :
    Heap.Extends h h' ∧
    ∃ (R : KExpr) (b : Nat) (Ms : List KExpr) (cbk : Nat) (bodies : List KExpr),
      r = .field (b : F) ∧
      FormStep a b (R = ty) (FullConsObs (wrapAt t E) (WrapperObserved root t) R ty) ∧
      nMot = es.length ∧ nMin = Ms.length ∧
      (Eventually fun f =>
        allMinors V f es fop nP es.length nP (elimLevel off) es 0 0 = some Ms) ∧
      (Eventually fun f => recTypeAt V f es off nP k = some R) ∧
      ctorsBefore V es k = some cbk ∧
      (Eventually fun f => ruleBodiesAt V f es off nP nMot nMin nl k peers = some bodies) ∧
      stored.length ≤ self.nctors ∧
      ∀ (c : Nat) (ru : Nat × Nat × KExpr), stored[c]? = some ru →
        ru.1 = c ∧ c < self.nctors ∧ NF (ixAddr ba) self.idx c ru.2.1 ∧
          ∃ cb, bodies[c]? = some cb ∧
            RuleFollows ty nP nMot nMin (cbk + c) ru.2.1 (elimLevel off) ru.2.2 cb := by
  refine ⟨ObsFn.heap_extends ev, ?_⟩
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono hbnd hs
  match Obs.«KernelCheck::canonical_rules_at_pos».obs ev with
  | .run (m2 := m2) (m60 := m60) (v59 := v59) (v259 := v259) (m_uszksxrg := m3) (m224 := m224) (m261 := m261)
      (m246 := m246) (v384 := v384) (m385 := m385) (v421 := v421) (m422 := m422)
      (v_htewcxgp := vseg) (cs_vcbgkffy := csSeg)
      (ev15 := evMem) (ev72 := evBRT) (sg_xtajopni := sg) (ev236 := evLen1) (ev271 := evBAM)
      (ev258 := evLen2) (heq355 := heqMot) (heq383 := heqMin) (ev397 := evCBP) (ev434 := evPR) (ev_fswvniux := evCR)
      (he_kcelgdaj := hres0) (hc671 := hc) .. =>
    obtain ⟨hm2, e, hek, he⟩ := flat_member_at_spec es k hk (by omega) evMem hes
    have ext0 : Heap.Extends h m2 := hm2 ▸ Heap.Extends.refl _
    have ext1 : Heap.Extends h m60 := ext0.trans (ObsFn.heap_extends evBRT)
    obtain ⟨-, R, hR, hRec⟩ := build_rec_type evBRT ext0
      (sub fun c hc' => by rw [hc]; simp [hc']) (fun c hc' => hroot c (by rw [hc]; simp [hc']))
    have hRl : LetFree m60 v59 := build_rec_type_letFree evBRT ext0
    have hsegsub : ∀ c ∈ csSeg, c ∈ cs := fun c hc' => by rw [hc]; simp [hc']
    -- the form step
    have hsg : ∃ b : Nat, vseg = .field (b : F) ∧
        FormStep a b (R = ty) (FullConsObs (wrapAt t E) (WrapperObserved root t) R ty) ∧
        Heap.Extends m60 m3 := by
      cases sg with
      | n1_n1 m1 cs1 evEq hform hr hh hcs =>
        have heq := kexpr_struct_eq_tmOExact hR (hty.mono ext1) evEq
        have ha1 : a = 1 := form_field_eq 1 ha (by omega) (by simpa using hform)
        refine ⟨1, by rw [hr]; simp, ⟨by omega, by omega, fun _ => heq, by omega, fun _ => rfl,
          by omega⟩, ?_⟩
        subst hh; exact ObsFn.heap_extends evEq
      | n1_other_n1 m1 cs1 m2' cs2 evEq hne evW hr hh hcs =>
        have heq := kexpr_struct_eq_tmOExact hR (hty.mono ext1) evEq
        have e1 := ObsFn.heap_extends evEq
        have hfull := wrap_rel_full_spec hwf hD hA evW
          (sub fun c hc' => hsegsub c (by rw [hcs]; simp [hc']))
          (fun c hc' => hroot c (hsegsub c (by rw [hcs]; simp [hc'])))
          (hR.mono e1) (hRl.mono e1) (hty.mono (ext1.trans e1))
        refine ⟨a, hr, ⟨ha, fun h0 => ⟨h0, heq, hfull⟩, fun _ => heq, fun _ => hfull, id, id⟩,
          ?_⟩
        subst hh; exact e1.trans (ObsFn.heap_extends evW)
      | n1_other_other m1 cs1 vw m2' cs2 evEq hne evW hneV hform hr hh hcs =>
        have heq := kexpr_struct_eq_tmOExact hR (hty.mono ext1) evEq
        have ha0 : a = 0 := form_field_eq 0 ha (by omega) (by simpa using hform)
        refine ⟨1, by rw [hr]; simp, ⟨by omega, by omega, fun _ => heq, by omega, by omega,
          by omega⟩, ?_⟩
        subst hh; exact (ObsFn.heap_extends evEq).trans (ObsFn.heap_extends evW)
      | other v1 m1 cs1 v2 m2' cs2 v3 m3' cs3 v4 m4 cs4 v5 evEq hne evVG hvg evW hW op evZ hZ hr
          hh hcs =>
        subst hW
        have e1 := (ObsFn.heap_extends evEq).trans (ObsFn.heap_extends evVG)
        have hfull := wrap_rel_full_spec hwf hD hA evW
          (sub fun c hc' => hsegsub c (by rw [hcs]; simp [hc']))
          (fun c hc' => hroot c (hsegsub c (by rw [hcs]; simp [hc'])))
          (hR.mono e1) (hRl.mono e1) (hty.mono (ext1.trans e1))
        have hane : a ≠ 1 := by
          intro ha1
          subst ha1
          have hv := evalBinOp_sub_field op
          have hv0 : v5 = .field 0 := by rw [hv]; simp
          obtain ⟨hz, -⟩ := Lib.is_zero_spec evZ
          rw [hv0, hZ] at hz
          simp at hz
        refine ⟨2, by rw [hr]; simp, ⟨by omega, by omega, by omega, fun _ => hfull,
          fun h1 => absurd h1 hane, fun _ => rfl⟩, ?_⟩
        subst hh
        exact e1.trans ((ObsFn.heap_extends evW).trans (ObsFn.heap_extends evZ))
    obtain ⟨b, hb, hstep, ext2⟩ := hsg
    obtain ⟨hv223, hm224⟩ := flat_length' evLen1 (flatList_mono (ext1.trans ext2) hes)
    subst hv223 hm224
    have hnMotEq : nMot = es.length :=
      natCast_inj_small (by omega) (by omega) (Value.field.inj heqMot)
    obtain ⟨-, Ms, hMs, hMsE⟩ := build_all_minors evBAM (ext1.trans ext2)
      (sub fun c hc' => by rw [hc]; simp [hc']) (fun c hc' => hroot c (by rw [hc]; simp [hc']))
    have hMsLen : Ms.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbnd
        (show (⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [v259], m261⟩ : Call F) ∈ cs
          by rw [hc]; simp) (by simp) hMs
    obtain ⟨hv245, -⟩ := kexpr_length evLen2 hMs
    subst hv245
    have hnMinEq : nMin = Ms.length :=
      natCast_inj_small (by omega) (by omega) (Value.field.inj heqMin)
    have ext3 : Heap.Extends h m246 :=
      ext1.trans (ext2.trans ((ObsFn.heap_extends evBAM).trans (ObsFn.heap_extends evLen2)))
    obtain ⟨-, -, -, cbk, bodies, hrest⟩ := rules_at_pos e Ms evCBP evPR evCR ext3
      (sub fun c hc' => by rw [hc]; simp [hc']) (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hek (he.mono ext3) hnMotEq hnMinEq hMsE
    exact ⟨R, b, Ms, cbk, bodies, by rw [hres0, hb], hstep, hnMotEq, hnMinEq, hMsE, hRec, hrest⟩

/-! ## The whole member check, under any role context -/

private theorem field_mul_bool_o {b₁ b₂ : Bool} {v : SourceValue F}
    (op : evalBinOp .mul (.field (if b₁ then 1 else 0)) (.field (if b₂ then 1 else 0)) = .ok v) :
    v = .field (if (b₁ && b₂) then 1 else 0) := by
  cases b₁ <;> cases b₂ <;> (simp only [evalBinOp, Bool.and_false, Bool.and_true, Bool.false_and,
    Bool.true_and, ↓reduceIte] at op ⊢; injection op with hv; rw [← hv]; simp)

private theorem is_muts_block_bool_o {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::is_muts_block" [x] h r h' cs) :
    ∃ b : Bool, r = .field (if b then 1 else 0) := by
  match Obs.«KernelCheck::is_muts_block».obs ev with
  | .Muts (he90 := hr) .. => exact ⟨true, hr⟩
  | .other (he97 := hr) .. => exact ⟨false, hr⟩

private theorem one_sub_bool_o {b : Bool} {v : SourceValue F}
    (op : evalBinOp .sub (.field 1) (.field (if b then (1 : F) else 0)) = .ok v) :
    v = .field (if (!b) then 1 else 0) := by
  cases b <;> (simp only [evalBinOp, Except.ok.injEq] at op; subst op; simp)

private theorem field_nat_eq_one_o {off : Nat} (hoff : off ≤ 1) :
    (.field (off : F) : SourceValue F) = .field 1 ↔ off = 1 := by
  interval_cases off <;> simp

/-- **`KernelCheck::check_recursor_canonical_at` under any role context**, on recursor `k` of a
family record whose major premise is over entry `k` of a flattened family `es` of different
entries, at the form `a` of the members before it: the position it finds for the major premise's
type is `k` (as under a group's validation, `check_recursor_canonical_at_spec`), so
`canonical_rules_at_pos` compares the recursor with the reconstruction at `k`
(`canonical_rules_at_pos_form_spec`): the form `b` it returns is a step from `a` in which its
declared type is the reconstructed type `R` or the full consumption of `R`, and its rules follow
the reconstructed bodies. The record's builders and the comparison are taken at this call's
arguments. -/
theorem check_recursor_canonical_at_form_spec {t : Ix.Kernel.RoleTable} (hwf : t.wf = true)
    {E : Ixon.Env}
    (hinj : Function.Injective (Core.keyOf t)) {V : ReconView} {es : List FlatEntry}
    (hd : FlatDistinct es)
    {off nP nI nMot nMin nl k a : Nat} {e : FlatEntry} (hek : es[k]? = some e) {ty : KExpr}
    {peers : List _root_.Address} {stored : List (Nat × Nat × KExpr)} {self : IndData}
    {ba : Bytes.Address} {NF : _root_.Address → Nat → Nat → Nat → Prop}
    {arb apb apar : Bytes.Address}
    {x_rc x_ty x_rules x_k x_uns x_rb x_idx x_pnl x_pty x_pnp x_pni x_nc x_w x_pblk x_pidx
      x_addr x_par x_bnl r : SourceValue F} {h h' : Heap F} {cs root : List (Call F)}
    (ev : ObsFn W "KernelCheck::check_recursor_canonical_at"
      [x_rc,
        .construct "KernelTypes::KConstantInfo" "Rec"
          [.field (nl : F), x_ty, .field (nP : F), .field (nI : F), .field (nMot : F),
            .field (nMin : F), x_rules, x_k, x_uns, x_rb, x_idx],
        x_addr,
        .construct "KernelTypes::KConstantInfo" "Induct"
          [x_pnl, x_pty, x_pnp, x_pni, x_nc, x_w, x_pblk, x_pidx],
        x_par, .field (off : F), x_bnl, (.field (a : F))] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (hoff : off ≤ 1) (hnl : nl < 4294967296)
    (hnMot : nMot < 4294967296) (hnMin : nMin < 4294967296)
    (hty : TmOExact (Core.keyOf t) h ty x_ty)
    (hpar : Bytes.RepAddressRef addrTy h apar x_par) (hpar_eq : ixAddr apar = e.addr)
    (hrb : Bytes.RepAddressRef addrTy h arb x_rb)
    (hpb : Bytes.RepAddressRef addrTy h apb x_pblk)
    (haux : e.aux = true → arb ≠ apb)
    (hD : DefnAtAnswers root t E) (hA : ArityRefusals root t E) (ha : a ≤ 2)
    (is_muts_block : e.aux = true → ∀ {m m' : Heap F} {x v : SourceValue F}
      {cs' : List (Call F)}, x = x_rb ∨ x = x_pblk →
      ObsFn W "KernelCheck::is_muts_block" [x] m v m' cs' → Heap.Extends h m →
      (∀ c ∈ cs', c ∈ root) → v = .field 1)
    (build_flat_block : ∀ {m m' : Heap F} {v : SourceValue F} {cs' : List (Call F)},
      ObsFn W "KernelCheck::build_flat_block" [x_rb, x_pblk, .field (off : F)] m v m' cs' →
      Heap.Extends h m → IxVM.Consistency.Bounded cs' → (∀ c ∈ cs', c ∈ root) →
      RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) m' es v)
    (build_peer_recs : ∀ {m m' : Heap F} {v x_flat : SourceValue F} {cs' : List (Call F)},
      ObsFn W "KernelCheck::build_peer_recs" [x_flat, x_rb, x_addr] m v m' cs' →
      Heap.Extends h m → IxVM.Consistency.Bounded cs' → (∀ c ∈ cs', c ∈ root) →
      RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) m es x_flat →
      ∃ as : List Bytes.Address,
        RepList IxVM.Refinement.Core.addrListEnum (Bytes.RepAddressRef addrTy) m' as v ∧
          as.map ixAddr = peers)
    (build_flat_own_params : ∀ {m m' : Heap F} {v x_flat : SourceValue F}
      {cs' : List (Call F)},
      ObsFn W "KernelCheck::build_flat_own_params" [x_flat] m v m' cs' →
      Heap.Extends h m → IxVM.Consistency.Bounded cs' → (∀ c ∈ cs', c ∈ root) →
      RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) m es x_flat →
      Heap.Extends m m' ∧ ∃ ns, flatOwnParams V es = some ns ∧
        RepList fieldListEnum RepNatField m' ns v)
    (extract_aux_spec_params_from_rec : ∀ {m m' : Heap F} {v : SourceValue F}
      {cs' : List (Call F)},
      ObsFn W "KernelCheck::extract_aux_spec_params_from_rec"
        [.construct "KernelTypes::KConstantInfo" "Rec"
          [.field (nl : F), x_ty, .field (nP : F), .field (nI : F), .field (nMot : F),
            .field (nMin : F), x_rules, x_k, x_uns, x_rb, x_idx], x_pnp] m v m' cs' →
      Heap.Extends h m → IxVM.Consistency.Bounded cs' → (∀ c ∈ cs', c ∈ root) →
      ∃ sp, RepList kexprListEnum (TmOExact (Core.keyOf t)) m' sp v ∧ (e.aux = true → sp = e.params))
    (extract_aux_occ_us : ∀ {m m' : Heap F} {v : SourceValue F} {cs' : List (Call F)},
      ObsFn W "KernelCheck::extract_aux_occ_us"
        [.construct "KernelTypes::KConstantInfo" "Rec"
          [.field (nl : F), x_ty, .field (nP : F), .field (nI : F), .field (nMot : F),
            .field (nMin : F), x_rules, x_k, x_uns, x_rb, x_idx]] m v m' cs' →
      Heap.Extends h m → IxVM.Consistency.Bounded cs' → (∀ c ∈ cs', c ∈ root) →
      ∃ us, RepKLevelList m' us v ∧ (e.aux = true → us = e.levels))
    (build_rec_type : ∀ {m m' : Heap F} {v x_flat x_peers x_fop x_lvls x_elim : SourceValue F}
      {cs' : List (Call F)} {fop : List Nat},
      ObsFn W "KernelCheck::build_rec_type"
        [x_rc, x_pty, x_pnl, .field (nP : F), x_pni, x_elim, .field (off : F), x_flat, x_fop,
          .field (k : F)] m v m' cs' →
      CanonArgs (Core.keyOf t) V es peers fop off nl m x_flat x_peers x_fop x_lvls x_elim →
      IxVM.Consistency.Bounded cs' → (∀ c ∈ cs', c ∈ root) →
      Heap.Extends m m' ∧ ∃ R, TmOExact (Core.keyOf t) m' R v ∧
        Eventually fun f => recTypeAt V f es off nP k = some R)
    (build_rec_type_letFree : ∀ {m m' : Heap F}
      {v x_flat x_peers x_fop x_lvls x_elim : SourceValue F}
      {cs' : List (Call F)} {fop : List Nat},
      ObsFn W "KernelCheck::build_rec_type"
        [x_rc, x_pty, x_pnl, .field (nP : F), x_pni, x_elim, .field (off : F), x_flat, x_fop,
          .field (k : F)] m v m' cs' →
      CanonArgs (Core.keyOf t) V es peers fop off nl m x_flat x_peers x_fop x_lvls x_elim → LetFree m' v)
    (build_all_minors : ∀ {m m' : Heap F} {v x_flat x_peers x_fop x_lvls x_elim : SourceValue F}
      {cs' : List (Call F)} {fop : List Nat},
      ObsFn W "KernelCheck::build_all_minors"
        [x_rc, x_flat, x_fop, .field (nP : F), .field (es.length : F), .field (nP : F), x_elim]
        m v m' cs' →
      CanonArgs (Core.keyOf t) V es peers fop off nl m x_flat x_peers x_fop x_lvls x_elim →
      IxVM.Consistency.Bounded cs' → (∀ c ∈ cs', c ∈ root) →
      Heap.Extends m m' ∧ ∃ Ms, RepList kexprListEnum (TmOExact (Core.keyOf t)) m' Ms v ∧
        Eventually fun f =>
          allMinors V f es fop nP es.length nP (elimLevel off) es 0 0 = some Ms)
    (rules_at_pos : ∀ {h₀ h₁ h₂ h₃ : Heap F}
      {vcb vcanon v w x_aux x_sp x_ou x_flat x_peers x_fop x_lvls x_elim : SourceValue F}
      {cs₁ cs₂ cs₃ : List (Call F)} {fop : List Nat} (Ms : List KExpr),
      ObsFn W "KernelCheck::ctors_before_pos" [x_flat, .field (k : F), .field 0] h₀ vcb h₁ cs₁ →
      ObsFn W "KernelCheck::populate_rules"
        [x_rc, x_nc, vcb, x_pblk, x_pidx, .field (nP : F), .field (nMot : F), .field (nMin : F),
          x_ou, x_lvls, x_flat, x_peers, x_fop, x_aux, x_sp, .field 0, x_elim] h₁ vcanon h₂ cs₂ →
      ObsFn W "KernelCheck::compare_rules"
        [x_rules, vcanon, .field (nP : F), .field (nMot : F), .field (nMin : F), x_pblk, x_pidx,
          x_nc, .field 0, x_elim, x_ty, vcb] h₂ v h₃ cs₃ →
      Heap.Extends h h₀ →
      CanonArgs (Core.keyOf t) V es peers fop off nl h₀ x_flat x_peers x_fop x_lvls x_elim →
      IxVM.Consistency.Bounded cs₂ → IxVM.Consistency.Bounded cs₃ →
      (∀ c ∈ cs₁, c ∈ root) → (∀ c ∈ cs₂, c ∈ root) → (∀ c ∈ cs₃, c ∈ root) →
      FlatEntryRepExact (Core.keyOf t) h₀ e (.tuple [w, x_aux, x_sp, x_ou]) →
      nMot = es.length → nMin = Ms.length →
      (Eventually fun f =>
        allMinors V f es fop nP es.length nP (elimLevel off) es 0 0 = some Ms) →
      Heap.Extends h₀ h₁ ∧ Heap.Extends h₁ h₂ ∧ Heap.Extends h₂ h₃ ∧
        ∃ (cbk : Nat) (bodies : List KExpr), ctorsBefore V es k = some cbk ∧
          (Eventually fun f => ruleBodiesAt V f es off nP nMot nMin nl k peers = some bodies) ∧
          stored.length ≤ self.nctors ∧
          ∀ (c : Nat) (ru : Nat × Nat × KExpr), stored[c]? = some ru →
            ru.1 = c ∧ c < self.nctors ∧ NF (ixAddr ba) self.idx c ru.2.1 ∧
              ∃ cb, bodies[c]? = some cb ∧
                RuleFollows ty nP nMot nMin (cbk + c) ru.2.1 (elimLevel off) ru.2.2 cb) :
    Heap.Extends h h' ∧
    ∃ (R : KExpr) (b : Nat) (fop : List Nat) (Ms : List KExpr) (cbk : Nat)
      (bodies : List KExpr),
      r = .field (b : F) ∧
      FormStep a b (R = ty) (FullConsObs (wrapAt t E) (WrapperObserved root t) R ty) ∧
      flatOwnParams V es = some fop ∧ nMot = es.length ∧ nMin = Ms.length ∧
      (Eventually fun f =>
        allMinors V f es fop nP es.length nP (elimLevel off) es 0 0 = some Ms) ∧
      (Eventually fun f => recTypeAt V f es off nP k = some R) ∧
      ctorsBefore V es k = some cbk ∧
      (Eventually fun f => ruleBodiesAt V f es off nP nMot nMin nl k peers = some bodies) ∧
      stored.length ≤ self.nctors ∧
      ∀ (c : Nat) (ru : Nat × Nat × KExpr), stored[c]? = some ru →
        ru.1 = c ∧ c < self.nctors ∧ NF (ixAddr ba) self.idx c ru.2.1 ∧
          ∃ cb, bodies[c]? = some cb ∧
            RuleFollows ty nP nMot nMin (cbk + c) ru.2.1 (elimLevel off) ru.2.2 cb := by
  refine ⟨ObsFn.heap_extends ev, ?_⟩
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono hbnd hs
  have hklt : k < es.length := (List.getElem?_eq_some_iff.mp hek).1
  -- everything up to the position, shared by the two arms that reach `canonical_rules_at_pos`
  have common : ∀ {x_nlvls x_ty' x_n_p x_n_i x_n_mot x_n_min x_rules' x_k' x_uns' x_rb' x_idx'
      x_pnl' x_pty' x_pnp' x_pni' x_nc' x_w' x_pblk' x_pidx' v209 v218 v247 v285 v323 x361 y362
      x353 y398 y354 v345 v477 v_so v486 : SourceValue F}
      {m210 m219 m248 m286 m324 m363 m355 m346 m478 m_yr m487 : Heap F}
      {cs212 cs229 cs258 cs296 cs334 cs372 cs386 cs408 cs480 cs_jq cs497 : List (Call F)},
      (.construct "KernelTypes::KConstantInfo" "Rec"
          [.field (nl : F), x_ty, .field (nP : F), .field (nI : F), .field (nMot : F),
            .field (nMin : F), x_rules, x_k, x_uns, x_rb, x_idx] : SourceValue F) =
        .construct "KernelTypes::KConstantInfo" "Rec"
          [x_nlvls, x_ty', x_n_p, x_n_i, x_n_mot, x_n_min, x_rules', x_k', x_uns', x_rb',
            x_idx'] →
      (.construct "KernelTypes::KConstantInfo" "Induct"
          [x_pnl, x_pty, x_pnp, x_pni, x_nc, x_w, x_pblk, x_pidx] : SourceValue F) =
        .construct "KernelTypes::KConstantInfo" "Induct"
          [x_pnl', x_pty', x_pnp', x_pni', x_nc', x_w', x_pblk', x_pidx'] →
      «Obs».«KernelCheck::check_recursor_canonical_at».SegX1 x_pnl' x_pty' x_pnp' x_pni' x_nc'
        x_pblk' x_pidx' x_nlvls x_ty' x_n_p x_n_i x_n_mot x_n_min x_rules' x_k' x_uns' x_rb'
        x_idx' x_rc
        (.construct "KernelTypes::KConstantInfo" "Rec"
          [.field (nl : F), x_ty, .field (nP : F), .field (nI : F), .field (nMot : F),
            .field (nMin : F), x_rules, x_k, x_uns, x_rb, x_idx]) x_addr
        (.construct "KernelTypes::KConstantInfo" "Induct"
          [x_pnl, x_pty, x_pnp, x_pni, x_nc, x_w, x_pblk, x_pidx])
        x_par (.field (off : F)) x_bnl (.field (a : F)) h v209 m210 cs212 →
      ObsFn W "KernelCheck::build_rec_lvls_list" [x_nlvls, .field 0] m210 v218 m219 cs229 →
      ObsFn W "KernelCheck::build_flat_block" [x_rb', x_pblk', .field (off : F)]
        m219 v247 m248 cs258 →
      ObsFn W "KernelCheck::build_peer_recs" [v247, x_rb', x_addr] m248 v285 m286 cs296 →
      ObsFn W "KernelCheck::build_flat_own_params" [v247] m286 v323 m324 cs334 →
      ObsFn W "KernelCheck::is_muts_block" [x_rb'] m324 x361 m363 cs372 →
      ObsFn W "KernelCheck::is_muts_block" [x_pblk'] m363 y362 m355 cs386 →
      evalBinOp .mul x361 y362 = .ok x353 →
      ObsFn W "Bytes::address_eq" [x_rb', x_pblk'] m355 y398 m346 cs408 →
      evalBinOp .sub (.field 1) y398 = .ok y354 →
      evalBinOp .mul x353 y354 = .ok v345 →
      «Obs».«KernelCheck::check_recursor_canonical_at».SegX2 v345 v323 v285 v247 v218 v209
        x_pnl' x_pty' x_pnp' x_pni' x_nc' x_pblk' x_pidx' x_nlvls x_ty' x_n_p x_n_i x_n_mot
        x_n_min x_rules' x_k' x_uns' x_rb' x_idx' x_rc
        (.construct "KernelTypes::KConstantInfo" "Rec"
          [.field (nl : F), x_ty, .field (nP : F), .field (nI : F), .field (nMot : F),
            .field (nMin : F), x_rules, x_k, x_uns, x_rb, x_idx]) x_addr
        (.construct "KernelTypes::KConstantInfo" "Induct"
          [x_pnl, x_pty, x_pnp, x_pni, x_nc, x_w, x_pblk, x_pidx])
        x_par (.field (off : F)) x_bnl (.field (a : F)) m346 v477 m478 cs480 →
      «Obs».«KernelCheck::check_recursor_canonical_at».SegX_aowwkmcx v477 v345 v323 v285 v247
        v218 v209 x_pnl' x_pty' x_pnp' x_pni' x_nc' x_pblk' x_pidx' x_nlvls x_ty' x_n_p x_n_i
        x_n_mot x_n_min x_rules' x_k' x_uns' x_rb' x_idx' x_rc
        (.construct "KernelTypes::KConstantInfo" "Rec"
          [.field (nl : F), x_ty, .field (nP : F), .field (nI : F), .field (nMot : F),
            .field (nMin : F), x_rules, x_k, x_uns, x_rb, x_idx]) x_addr
        (.construct "KernelTypes::KConstantInfo" "Induct"
          [x_pnl, x_pty, x_pnp, x_pni, x_nc, x_w, x_pblk, x_pidx])
        x_par (.field (off : F)) x_bnl (.field (a : F)) m478 v_so m_yr cs_jq →
      ObsFn W "KernelCheck::flat_find_pos_kind" [v247, x_par, v345, v477, v_so, .field 0]
        m_yr v486 m487 cs497 →
      (∀ c ∈ cs212 ++ cs229 ++ cs258 ++ cs296 ++ cs334 ++ cs372 ++ cs386 ++ cs408 ++ cs480 ++
          cs_jq ++ cs497, c ∈ cs) →
      (⟨"KernelCheck::build_flat_own_params", [v247], m286⟩ : Call F) ∈ cs →
      (x_ty' = x_ty ∧ x_n_p = .field (nP : F) ∧ x_n_mot = .field (nMot : F) ∧
          x_n_min = .field (nMin : F) ∧ x_rules' = x_rules ∧ x_pty' = x_pty ∧ x_pnl' = x_pnl ∧
          x_pni' = x_pni ∧ x_nc' = x_nc ∧ x_pblk' = x_pblk ∧ x_pidx' = x_pidx) ∧
        Heap.Extends h m487 ∧ es.length < 2 ^ 39 ∧
        (∃ fop, CanonArgs (Core.keyOf t) V es peers fop off nl m487 v247 v285 v323 v218 v209) ∧
        ∃ (aux' : Bool) (sp : List KExpr) (us : List KLevel),
          (e.aux = true → aux' = true ∧ sp = e.params ∧ us = e.levels) ∧
          match flatFindPosKind es e.addr aux' sp us with
          | some j => v486 = .tuple [.field 1, .field ((j : Nat) : F)]
          | none => v486 = .tuple [.field 0, .field 0] := by
    intro x_nlvls x_ty' x_n_p x_n_i x_n_mot x_n_min x_rules' x_k' x_uns' x_rb' x_idx'
      x_pnl' x_pty' x_pnp' x_pni' x_nc' x_w' x_pblk' x_pidx' v209 v218 v247 v285 v323 x361 y362
      x353 y398 y354 v345 v477 v_so v486 m210 m219 m248 m286 m324 m363 m355 m346 m478 m_yr m487
      cs212 cs229 cs258 cs296 cs334 cs372 cs386 cs408 cs480 cs_jq cs497
      hrec hind sg1 evL evF evP evFop evM1 evM2 op1 evAeq op2 op3 sg2 sg3 evK hsubs hmemFop
    injection hrec with _ _ hargs
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, -, rfl, rfl, rfl, -, -, rfl, -⟩ := hargs
    injection hind with _ _ hargs
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -, rfl, rfl⟩ := hargs
    have hin : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs212 ++ cs229 ++ cs258 ++ cs296 ++
        cs334 ++ cs372 ++ cs386 ++ cs408 ++ cs480 ++ cs_jq ++ cs497) → ∀ c ∈ cs', c ∈ cs :=
      fun hs c hc' => hsubs c (hs c hc')
    -- the elimination level
    have helim : RepKLevel m210 (elimLevel off) v209 ∧ Heap.Extends h m210 := by
      cases sg1 with
      | n1 hv hr hm _ =>
        have ho : off = 1 := (field_nat_eq_one_o hoff).mp hv
        subst hr hm ho
        refine ⟨?_, Heap.Extends.snoc _ _⟩
        have := (RepKLevel.allocParam h (n := 0) (by decide)).1
        simpa [elimLevel] using this
      | other hne hr hm _ =>
        have ho : off ≠ 1 := fun ho => hne ((field_nat_eq_one_o hoff).mpr ho)
        subst hr hm
        refine ⟨?_, Heap.Extends.snoc _ _⟩
        have := (RepKLevel.allocZero h).1
        simpa [elimLevel, ho] using this
    obtain ⟨helim, e1⟩ := helim
    have hlv := IxVM.Refinement.Decl.build_rec_lvls_list_spec hnl evL
    have e2 : Heap.Extends h m219 := e1.trans (ObsFn.heap_extends evL)
    have hflat := build_flat_block evF e2 (sub (hin fun c hc' => by simp [hc']))
      (fun c hc' => hroot c (hin (fun c hc' => by simp [hc']) c hc'))
    have e3 : Heap.Extends h m248 := e2.trans (ObsFn.heap_extends evF)
    obtain ⟨as, has, hmap⟩ := build_peer_recs evP e3 (sub (hin fun c hc' => by simp [hc']))
      (fun c hc' => hroot c (hin (fun c hc' => by simp [hc']) c hc')) hflat
    have x1 : Heap.Extends m248 m286 := ObsFn.heap_extends evP
    have x2 : Heap.Extends m286 m324 := ObsFn.heap_extends evFop
    obtain ⟨-, fop, hfopEq, hfopRep⟩ := build_flat_own_params evFop (e3.trans x1)
      (sub (hin fun c hc' => by simp [hc']))
      (fun c hc' => hroot c (hin (fun c hc' => by simp [hc']) c hc')) (flatList_mono x1 hflat)
    have x3 : Heap.Extends m324 m363 := ObsFn.heap_extends evM1
    have x4 : Heap.Extends m363 m355 := ObsFn.heap_extends evM2
    have e7 : Heap.Extends h m355 := e3.trans (x1.trans (x2.trans (x3.trans x4)))
    have hflat286 := flatList_mono x1 hflat
    have hlen : es.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbnd hmemFop (by simp) hflat286
    -- whether the recursor is an auxiliary's
    obtain ⟨b1, rfl⟩ := is_muts_block_bool_o evM1
    obtain ⟨b2, rfl⟩ := is_muts_block_bool_o evM2
    have hx353 := field_mul_bool_o op1
    subst hx353
    obtain ⟨hy398, hm346⟩ := Lib.address_eq_spec evAeq
      (Bytes.repAddressRef_heapMono₂ addrTy e7 hrb) (Bytes.repAddressRef_heapMono₂ addrTy e7 hpb)
    subst hm346
    have hy398' : y398 = .field (if decide (arb = apb) then 1 else 0) := by
      rw [hy398]; by_cases hq : arb = apb <;> simp [hq]
    subst hy398'
    have hy354 := one_sub_bool_o op2
    subst hy354
    have hv345 := field_mul_bool_o op3
    have haux' : e.aux = true → (b1 && b2 && !decide (arb = apb)) = true := by
      intro hea
      have h1 := is_muts_block hea (Or.inl rfl) evM1
        (e3.trans (x1.trans x2)) (fun c hc' => hroot c (hin (fun c hc' => by simp [hc']) c hc'))
      have h2 := is_muts_block hea (Or.inr rfl) evM2
        (e3.trans (x1.trans (x2.trans x3)))
        (fun c hc' => hroot c (hin (fun c hc' => by simp [hc']) c hc'))
      have hb1 : b1 = true := by
        cases b1
        · exact absurd (Value.field.inj h1) (by decide)
        · rfl
      have hb2 : b2 = true := by
        cases b2
        · exact absurd (Value.field.inj h2) (by decide)
        · rfl
      simp [hb1, hb2, haux hea]
    -- the recursor's parameters and levels
    have hsp : ∃ sp, RepList kexprListEnum (TmOExact (Core.keyOf t)) m478 sp v477 ∧
        (e.aux = true → sp = e.params) ∧ Heap.Extends m346 m478 := by
      cases sg2 with
      | n1 cs444 hv evX hc' =>
        subst hc'
        have hs444 : ∀ c ∈ cs444, c ∈ cs := hin (fun c hcc => by simp [hcc])
        obtain ⟨sp, hsp, hspe⟩ := extract_aux_spec_params_from_rec evX e7 (sub hs444)
          (fun c hcc => hroot c (hs444 c hcc))
        exact ⟨sp, hsp, hspe, ObsFn.heap_extends evX⟩
      | other hne hr hm _ =>
        subst hr hm
        refine ⟨[], .nil (by simp), ?_, Heap.Extends.snoc _ _⟩
        intro hea
        rw [hv345, haux' hea] at hne
        exact absurd rfl hne
    obtain ⟨sp, hsp, hspe, x6⟩ := hsp
    have hus : ∃ us, RepKLevelList m_yr us v_so ∧ (e.aux = true → us = e.levels) ∧
        Heap.Extends m478 m_yr := by
      cases sg3 with
      | n1 csj hv evX hc' =>
        subst hc'
        have hsj : ∀ c ∈ csj, c ∈ cs := hin (fun c hcc => by simp [hcc])
        obtain ⟨us, hus, huse⟩ := extract_aux_occ_us evX (e7.trans x6) (sub hsj)
          (fun c hcc => hroot c (hsj c hcc))
        exact ⟨us, hus, huse, ObsFn.heap_extends evX⟩
      | other hne hr hm _ =>
        subst hr hm
        rw [← IxVM.Refinement.Levels.klevelList_names]
        refine ⟨[], .nil (by simp), ?_, Heap.Extends.snoc _ _⟩
        intro hea
        rw [hv345, haux' hea] at hne
        exact absurd rfl hne
    obtain ⟨us, hus, huse, x7⟩ := hus
    have e9 : Heap.Extends h m_yr := e7.trans (x6.trans x7)
    have ext248 : Heap.Extends m248 m_yr := x1.trans (x2.trans (x3.trans (x4.trans (x6.trans x7))))
    have evK' : ObsFn W "KernelCheck::flat_find_pos_kind"
        [v247, x_par, auxVal (b1 && b2 && !decide (arb = apb)), v477, v_so,
          .field ((0 : Nat) : F)] m_yr v486 m487 cs497 := by
      have h0 : (.field 0 : SourceValue F) = .field ((0 : Nat) : F) := by simp
      rw [hv345, h0] at evK; exact evK
    obtain ⟨x8, hfind⟩ := flat_find_pos_kind_spec hinj es 0 evK'
      (sub (hin fun c hc' => by simp [hc'])) (root := cs497) (fun c hc' => hc')
      (flatList_mono ext248 hflat) (Bytes.repAddressRef_heapMono₂ addrTy e9 hpar)
      (tmOExactList_mono x7 hsp) hus
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, e9.trans x8, hlen, ?_,
      (b1 && b2 && !decide (arb = apb)), sp, us,
      fun hea => ⟨haux' hea, hspe hea, huse hea⟩, ?_⟩
    · have ext286 : Heap.Extends m286 m487 :=
        x2.trans (x3.trans (x4.trans (x6.trans (x7.trans x8))))
      exact ⟨fop, flatList_mono (ext248.trans x8) hflat,
        ⟨as, repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ addrTy) ext286 has, hmap⟩,
        hfopEq, fieldList_mono (x3.trans (x4.trans (x6.trans (x7.trans x8)))) hfopRep,
        hlv.mono ((ObsFn.heap_extends evF).trans (ext248.trans x8)),
        helim.mono ((ObsFn.heap_extends evL).trans ((ObsFn.heap_extends evF).trans
          (ext248.trans x8)))⟩
    · rw [hpar_eq] at hfind
      cases hf : flatFindPosKind es e.addr (b1 && b2 && !decide (arb = apb)) sp us with
      | none => rw [hf] at hfind; exact hfind
      | some j => rw [hf] at hfind; simpa using hfind
  -- the position is `k`, and the comparison there
  have finish : ∀ {x_self_pos v209 v218 v247 v285 v323 : SourceValue F} {m : Heap F}
      {cs' : List (Call F)} {fop : List Nat},
      ObsFn W "KernelCheck::canonical_rules_at_pos"
        [x_rc, v247, x_self_pos, x_nc, x_pblk, x_pidx, .field (nP : F), .field (nMot : F),
          .field (nMin : F), v218, v285, v323, x_rules, x_ty, x_pty, x_pnl, x_pni, v209,
          .field (off : F), (.field (a : F))] m r h' cs' →
      x_self_pos = .field (k : F) → Heap.Extends h m → es.length < 2 ^ 39 →
      CanonArgs (Core.keyOf t) V es peers fop off nl m v247 v285 v323 v218 v209 → (∀ c ∈ cs', c ∈ cs) →
      ∃ (R : KExpr) (b : Nat) (fop : List Nat) (Ms : List KExpr) (cbk : Nat)
        (bodies : List KExpr),
        r = .field (b : F) ∧
        FormStep a b (R = ty) (FullConsObs (wrapAt t E) (WrapperObserved root t) R ty) ∧
        flatOwnParams V es = some fop ∧ nMot = es.length ∧ nMin = Ms.length ∧
        (Eventually fun f =>
          allMinors V f es fop nP es.length nP (elimLevel off) es 0 0 = some Ms) ∧
        (Eventually fun f => recTypeAt V f es off nP k = some R) ∧
        ctorsBefore V es k = some cbk ∧
        (Eventually fun f => ruleBodiesAt V f es off nP nMot nMin nl k peers = some bodies) ∧
        stored.length ≤ self.nctors ∧
        ∀ (c : Nat) (ru : Nat × Nat × KExpr), stored[c]? = some ru →
          ru.1 = c ∧ c < self.nctors ∧ NF (ixAddr ba) self.idx c ru.2.1 ∧
            ∃ cb, bodies[c]? = some cb ∧
              RuleFollows ty nP nMot nMin (cbk + c) ru.2.1 (elimLevel off) ru.2.2 cb := by
    intro x_self_pos v209 v218 v247 v285 v323 m cs' fop evC hpos ext hlen args hcs'
    subst hpos
    obtain ⟨R, b, Ms, cbk, bodies, hb0, hstep, h1, h2, h3, h4⟩ :=
      (canonical_rules_at_pos_form_spec hwf (E := E) (root := root) (fop := fop) (self := self)
      (ba := ba)
      (NF := NF) (stored := stored) (peers := peers) (nl := nl) evC (sub hcs')
      (fun c hc' => hroot c (hcs' c hc')) hD hA ha args.flat hklt hlen hnMot hnMin
      (hty.mono ext)
      (fun evv ext' hb hr => build_rec_type evv (args.mono ext') hb hr)
      (fun evv ext' => build_rec_type_letFree evv (args.mono ext'))
      (fun evv ext' hb hr => build_all_minors evv (args.mono ext') hb hr)
      (fun e' Ms ev1 ev2 ev3 ext' hb2 hb3 hr1 hr2 hr3 he' hrep hm1 hm2 hms => by
        rw [hek] at he'
        obtain rfl := Option.some.inj he'
        exact rules_at_pos Ms ev1 ev2 ev3 (ext.trans ext') (args.mono ext') hb2 hb3 hr1 hr2 hr3
          hrep hm1 hm2 hms)).2
    exact ⟨R, b, fop, Ms, cbk, bodies, hb0, hstep, args.fopEq, h1, h2, h3, h4⟩
  match Obs.«KernelCheck::check_recursor_canonical_at».obsx ev with
  | .Induct_n1_bind (hv15 := hrec) (hv86 := hind) (sg217 := sg1) (ev231 := evL) (ev260 := evF)
      (ev298 := evP) (ev336 := evFop) (ev374 := evM1) (ev388 := evM2) (op368 := op1)
      (ev410 := evAeq) (op404 := op2) (op360 := op3) (sg485 := sg2) (sg_berdancy := sg3)
      (ev499 := evK) (ev572 := evC) (hc725 := hc) .. =>
    obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ext, hlen, ⟨fop, args⟩, aux', sp,
        us, hauxe, hfind⟩ := common hrec hind sg1 evL evF evP evFop evM1 evM2 op1 evAeq op2 op3
      sg2 sg3 evK (fun c hc' => by
        rw [hc]
        simp only [List.mem_append, List.mem_cons] at hc' ⊢
        rcases hc' with (((((((((( h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) <;>
          simp [h]) (by rw [hc]; simp)
    refine finish evC ?_ ext hlen args (fun c hc' => by rw [hc]; simp [hc'])
    cases hea : e.aux with
    | true =>
      obtain ⟨rfl, rfl, rfl⟩ := hauxe hea
      rw [flatFindPosKind_aux hd hek hea] at hfind
      injection hfind with hl; injection hl with _ hl; injection hl with hl
    | false =>
      cases aux' with
      | true =>
        rw [flatFindPosKind_own_none hd hek hea] at hfind
        injection hfind with hl; injection hl with hl
        exact absurd (Value.field.inj hl) (by decide)
      | false =>
        rw [flatFindPosKind_own hd hek hea] at hfind
        injection hfind with hl; injection hl with _ hl; injection hl with hl
  | .Induct_other (v247 := vflat) (m487 := m487) (m730 := m730) (cs741 := cs741)
      (x_self_pos := xpos) (hv15 := hrec) (hv86 := hind) (sg217 := sg1) (ev231 := evL)
      (ev260 := evF) (ev298 := evP) (ev336 := evFop) (ev374 := evM1) (ev388 := evM2)
      (op368 := op1) (ev410 := evAeq) (op404 := op2) (op360 := op3) (sg485 := sg2)
      (sg_berdancy := sg3) (ev499 := evK) (ev743 := evFP) (ev790 := evC) (hc943 := hc)
      (hnt0 := hnt) .. =>
    obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ext, hlen, ⟨fop, args⟩, aux', sp,
        us, hauxe, hfind⟩ := common hrec hind sg1 evL evF evP evFop evM1 evM2 op1 evAeq op2 op3
      sg2 sg3 evK (fun c hc' => by
        rw [hc]
        simp only [List.mem_append, List.mem_cons] at hc' ⊢
        rcases hc' with (((((((((( h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) <;>
          simp [h]) (by rw [hc]; simp)
    have evFP' : ObsFn W "KernelCheck::flat_find_pos" [vflat, x_par, .field ((0 : Nat) : F)]
        m487 (.tuple [.field 1, xpos]) m730 cs741 := by
      have h0 : (.field 0 : SourceValue F) = .field ((0 : Nat) : F) := by simp
      rw [h0] at evFP; exact evFP
    obtain ⟨hm730, hpos⟩ := flat_find_pos_spec es 0 evFP' (root := cs) (fun c hc' => by
      rw [hc]; simp [hc']) args.flat (Bytes.repAddressRef_heapMono₂ addrTy ext hpar)
    subst hm730
    refine finish evC ?_ ext hlen args (fun c hc' => by rw [hc]; simp [hc'])
    rw [hpar_eq] at hpos
    cases hea : e.aux with
    | true =>
      obtain ⟨rfl, rfl, rfl⟩ := hauxe hea
      rw [flatFindPosKind_aux hd hek hea] at hfind
      exact absurd hfind (hnt _)
    | false =>
      cases aux' with
      | true =>
        rw [flatFindPos_own hd hek hea] at hpos
        injection hpos with hl; injection hl with _ hl; injection hl with hl
        simpa using hl
      | false =>
        rw [flatFindPosKind_own hd hek hea] at hfind
        exact absurd hfind (hnt _)
  | .other (hne944 := hne) .. => exact absurd rfl (hne _ rfl)

/-! ## The member-level form, at a relation of the types -/

/-- **A recursor of the family record is `MemberRecon` at its position from what its check gives,
at any relation of the declared type to the reconstructed one** (`memberRecon_of_canonical` is
this at the declared type being the reconstructed one): at every fuel of head normalization from
some one on. -/
theorem memberRecon_of_canonical_rel {TyRel : KExpr → KExpr → Prop} {t : Ix.Kernel.RoleTable}
    {E : Ixon.Env} {rb : _root_.Address}
    {crb : Ixon.Constant} {rs : Array Ixon.MutConst} {es : List FlatEntry} {off k : Nat}
    {r : Ixon.Recursor} {ty : KExpr} {stored : List (Nat × Nat × KExpr)}
    (hty : loadedAt t (fun x => E.blobs.get? x) crb (blockSelf t rb rs) r.lvls.toNat
      (mutsRoot rs k) r.typ = some ty)
    (hrules : ∀ (c : Nat) (ru : Ixon.RecursorRule), r.rules[c]? = some ru →
      ∃ (rhs : KExpr) (cidx : Nat),
        loadedAt t (fun x => E.blobs.get? x) crb (blockSelf t rb rs) r.lvls.toNat
          (mutsRoot rs k + 1 + ((c : Nat) : IxVM.F)) ru.rhs = some rhs ∧
        stored[c]? = some (cidx, ru.fields.toNat, rhs))
    (hcanon : ∃ (R : KExpr) (cbk : Nat) (bodies : List KExpr),
      (Eventually fun f =>
        recTypeAt (ReconView.ofStore t E) f es off r.params.toNat k = some R) ∧
      TyRel ty R ∧
      ctorsBefore (ReconView.ofStore t E) es k = some cbk ∧
      (Eventually fun f =>
        ruleBodiesAt (ReconView.ofStore t E) f es off r.params.toNat r.motives.toNat
          r.minors.toNat r.lvls.toNat k (recAddrs rb rs) = some bodies) ∧
      ∀ (c : Nat) (ru : Nat × Nat × KExpr), stored[c]? = some ru →
        ∃ cb, bodies[c]? = some cb ∧
          RuleFollows ty r.params.toNat r.motives.toNat r.minors.toNat (cbk + c) ru.2.1
            (elimLevel off) ru.2.2 cb) :
    Eventually fun fuel => MemberRecon TyRel t E rb crb rs es off fuel k r := by
  obtain ⟨R, cbk, bodies, ⟨a₁, h₁⟩, hrel, hcb, ⟨a₂, h₂⟩, hfol⟩ := hcanon
  refine ⟨max a₁ a₂, fun fuel hf => ?_⟩
  refine ⟨ty, R, bodies, cbk, hty, h₁ _ (by omega), hrel, h₂ _ (by omega), hcb, ?_⟩
  intro c ru hru
  obtain ⟨rhs, cidx, hrhs, hrule⟩ := hrules c ru hru
  obtain ⟨cb, hcbd, hrf⟩ := hfol c _ hrule
  exact ⟨rhs, cb, hrhs, hcbd, hrf⟩

/-! ## The record: one form at all its members -/

theorem eventually_forall_lt {P : Nat → Nat → Prop} :
    ∀ (n : Nat), (∀ k, k < n → Eventually (P k)) → Eventually fun f => ∀ k, k < n → P k f
  | 0, _ => ⟨0, fun _ _ k hk => absurd hk (Nat.not_lt_zero k)⟩
  | n + 1, h => by
    obtain ⟨a, ha⟩ := eventually_forall_lt n (fun k hk => h k (by omega))
    obtain ⟨b, hb⟩ := h n (by omega)
    refine ⟨max a b, fun f hf k hk => ?_⟩
    by_cases hkn : k = n
    · subst hkn; exact hb f (by omega)
    · exact ha f (by omega) k (by omega)

/-- **The form state leaves a family record in one form at all its members**: where the forms
`form k` before each member start at `0` (`check_family` hands `check_recs` the form `0`), every
recursor `k` of the record is `MemberRecon` at a step of the form from `form k` to `form (k + 1)`
(`check_recursor_canonical_at_form_spec`, `memberRecon_of_canonical_rel`), and a member that is
no recursor leaves the form, the record is in the reconstruction's form (`RFormS`: every declared
type is the reconstruction) or in the observed full-consumption form (`RecordFullConsObs`: every
declared type is the reconstruction's full consumption). A form `1` or `2` is kept by every later
member, and a member whose step ends at `0` is in both. -/
theorem recordForm_of_members {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {B rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {es : List FlatEntry} {off : Nat}
    (hrb : IxVM.Consistency.recordOf E rb = some crb) (hrs : crb.info = .muts rs)
    (hRF : RecordFlat t E rb crb rs es) (hBD : BlockDerivedFlat t E B off es)
    (form : Nat → Nat) (h0 : form 0 = 0)
    (hskip : ∀ k, k < rs.size → (∀ r, rs[k]? ≠ some (.recr r)) → form (k + 1) = form k)
    (hM : ∀ (k : Nat) (r : Ixon.Recursor), rs[k]? = some (.recr r) →
      Eventually fun fuel =>
        MemberRecon (fun ty R => FormStep (form k) (form (k + 1)) (R = ty)
          (FullConsObs (wrapAt t E) (WrapperObserved calls t) R ty))
          t E rb crb rs es off fuel k r) :
    RFormS t E B rb ∨ RecordFullConsObs calls t E B rb := by
  -- one fuel for all the members
  have hall : Eventually fun fuel => ∀ k, k < rs.size → ∀ r, rs[k]? = some (.recr r) →
      MemberRecon (fun ty R => FormStep (form k) (form (k + 1)) (R = ty)
        (FullConsObs (wrapAt t E) (WrapperObserved calls t) R ty))
        t E rb crb rs es off fuel k r := by
    refine eventually_forall_lt (P := fun k fuel => ∀ r, rs[k]? = some (.recr r) →
      MemberRecon (fun ty R => FormStep (form k) (form (k + 1)) (R = ty)
        (FullConsObs (wrapAt t E) (WrapperObserved calls t) R ty))
        t E rb crb rs es off fuel k r) rs.size (fun k _ => ?_)
    by_cases hr : ∃ r, rs[k]? = some (.recr r)
    · obtain ⟨r0, hr0⟩ := hr
      obtain ⟨a, ha⟩ := hM k r0 hr0
      refine ⟨a, fun f hf r hr' => ?_⟩
      rw [hr0] at hr'
      have : r0 = r := by
        injection hr' with h1
        injection h1
      subst this
      exact ha f hf
    · exact ⟨0, fun f _ r hr' => absurd ⟨r, hr'⟩ hr⟩
  obtain ⟨fuel, hfuel⟩ := hall
  have hmem : ∀ (k : Nat) (r : Ixon.Recursor), rs[k]? = some (.recr r) →
      k < rs.size ∧ MemberRecon (fun ty R => FormStep (form k) (form (k + 1)) (R = ty)
        (FullConsObs (wrapAt t E) (WrapperObserved calls t) R ty))
        t E rb crb rs es off fuel k r := by
    intro k r hr
    have hk : k < rs.size := by
      by_contra hge
      rw [Array.getElem?_eq_none (by omega)] at hr
      cases hr
    exact ⟨hk, hfuel fuel (Nat.le_refl _) k hk r hr⟩
  have hstepOf : ∀ (k : Nat) (r : Ixon.Recursor), rs[k]? = some (.recr r) →
      ∃ eq full : Prop, FormStep (form k) (form (k + 1)) eq full := by
    intro k r hr
    obtain ⟨ty, R, bodies, cbk, -, -, hrel, -⟩ := (hmem k r hr).2
    exact ⟨_, _, hrel⟩
  -- a form `1` or `2` is kept
  have hkeep : ∀ k, k < rs.size →
      (form k = 1 → form (k + 1) = 1) ∧ (form k = 2 → form (k + 1) = 2) := by
    intro k hk
    by_cases hr : ∃ r, rs[k]? = some (.recr r)
    · obtain ⟨r, hr⟩ := hr
      obtain ⟨eq, full, hs⟩ := hstepOf k r hr
      exact ⟨hs.keep1, hs.keep2⟩
    · have hsk := hskip k hk (fun r hr' => hr ⟨r, hr'⟩)
      rw [hsk]
      exact ⟨id, id⟩
  have hkeepN : ∀ (d j : Nat), j + d ≤ rs.size →
      (form j = 1 → form (j + d) = 1) ∧ (form j = 2 → form (j + d) = 2) := by
    intro d
    induction d with
    | zero => intro j _; exact ⟨id, id⟩
    | succ d ih =>
      intro j hj
      obtain ⟨i1, i2⟩ := ih j (by omega)
      obtain ⟨k1, k2⟩ := hkeep (j + d) (by omega)
      exact ⟨fun h => k1 (i1 h), fun h => k2 (i2 h)⟩
  by_cases hex : ∃ (k : Nat) (r : Ixon.Recursor), rs[k]? = some (.recr r) ∧ form (k + 1) = 2
  · -- one member is the full consumption only: every member is the full consumption
    obtain ⟨k0, r0, hr0, hf0⟩ := hex
    have hk0 := (hmem k0 r0 hr0).1
    refine Or.inr ⟨crb, rs, es, off, fuel, hrb, hrs, hRF, hBD, fun k r hr => ?_⟩
    obtain ⟨hk, hm⟩ := hmem k r hr
    have hne1 : form (k + 1) ≠ 1 := by
      intro h1
      by_cases hle : k ≤ k0
      · have := (hkeepN (k0 - k) (k + 1) (by omega)).1 h1
        rw [show k + 1 + (k0 - k) = k0 + 1 by omega] at this
        omega
      · have := (hkeepN (k - k0) (k0 + 1) (by omega)).2 hf0
        rw [show k0 + 1 + (k - k0) = k + 1 by omega] at this
        omega
    refine MemberRecon.mono (fun ty R (hs : FormStep (form k) (form (k + 1)) (R = ty) _) => ?_) hm
    have hle := hs.le
    by_cases hz : form (k + 1) = 0
    · exact (hs.zero hz).2.2
    · exact hs.two (by omega)
  · -- no member is the full consumption only: every member is the reconstruction
    refine Or.inl ⟨crb, rs, es, off, fuel, hrb, hrs, hRF, hBD, fun k r hr => ?_⟩
    obtain ⟨hk, hm⟩ := hmem k r hr
    have hne2 : form (k + 1) ≠ 2 := fun h2 => hex ⟨k, r, hr, h2⟩
    refine MemberRecon.mono (fun ty R (hs : FormStep (form k) (form (k + 1)) (R = ty) _) => ?_) hm
    have hle := hs.le
    have heq : R = ty := by
      by_cases hz : form (k + 1) = 0
      · exact (hs.zero hz).2.1
      · exact hs.one (by omega)
    rw [heq]
    exact ExprLvEq.refl ty

/-! ## What full consumption forces of the declared type -/

/-- Full consumption relates terms with one head constant and as many arguments. -/
theorem FullCons.spine {Wr : KKey → Option (Option Nat)} {g d : KExpr} (h : FullCons Wr g d) :
    appHead g = appHead d ∧
      (Ix.Kernel.Expr.getAppArgs g).length = (Ix.Kernel.Expr.getAppArgs d).length := by
  induction h with
  | app _ _ ihf _ =>
    refine ⟨ihf.1, ?_⟩
    simp only [Ix.Kernel.Expr.getAppArgs, List.length_append, ihf.2, List.length_cons,
      List.length_nil]
  | bvar => exact ⟨rfl, rfl⟩
  | fvar _ => exact ⟨rfl, rfl⟩
  | sort _ => exact ⟨rfl, rfl⟩
  | const _ => exact ⟨rfl, rfl⟩
  | lit => exact ⟨rfl, rfl⟩
  | lam _ _ _ _ _ _ _ => exact ⟨rfl, rfl⟩
  | forallE _ _ _ _ _ _ _ => exact ⟨rfl, rfl⟩
  | letE _ _ _ _ _ _ => exact ⟨rfl, rfl⟩
  | proj _ _ => exact ⟨rfl, rfl⟩

theorem consumeOf_none_of_length {Wr : KKey → Option (Option Nat)} (hd : Option KKey) :
    ∀ {l l' : List KExpr}, l.length = l'.length → consumeOf Wr hd l = some none →
      consumeOf Wr hd l' = some none
  | [], [], _, h => h
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | a :: rest, a' :: rest', hl, h => by
    cases hd with
    | none => rfl
    | some w =>
      have hlen : rest.length = rest'.length := by simpa using hl
      simp only [consumeOf] at h ⊢
      cases hw : Wr w with
      | none => rw [hw] at h; simp at h
      | some k =>
        rw [hw] at h
        simp only [Option.map_some, Option.some.injEq] at h ⊢
        by_cases hk : k = some (rest.length + 1)
        · rw [ite_eq_left hk] at h; cases h
        · rw [ite_eq_right (by rw [← hlen]; exact hk)]

/-- **A term that is the full consumption of one nothing is consumed from is itself one nothing
is consumed from.** -/
theorem FullCons.consumeAt_none {Wr : KKey → Option (Option Nat)} {c T : KExpr}
    (h : FullCons Wr c T) (hc : consumeAt Wr c = some none) : consumeAt Wr T = some none := by
  obtain ⟨hhd, hlen⟩ := h.spine
  show consumeOf Wr (appHead T) (Ix.Kernel.Expr.getAppArgs T) = some none
  rw [← hhd]
  exact consumeOf_none_of_length (appHead c) hlen hc

/-- **Every ∀ domain of a full consumption is one nothing is consumed from**: the declared type
keeps no wrapper applied to its arity at a binder domain. (`wrap_rel(1, ·, ·)` compares a domain
that is a `Let` cell, and the parts of any `Let` cell, without consuming at the head of the term
the cell represents; so it accepts declared types this refuses, where the reconstruction's heap
term has a `Let` cell. `wrap_rel_full_spec` takes the heap term without one.) -/
theorem FullCons.forallE_dom_none {Wr : KKey → Option (Option Nat)} {t b T b' : KExpr}
    {m m' : Ix.Kernel.BinderMeta} (h : FullCons Wr (.forallE t b m) (.forallE T b' m')) :
    consumeAt Wr T = some none := by
  cases h with
  | forallE _ _ hstop hdom _ => exact hdom.consumeAt_none hstop

/-- **Full consumption is not reflexive at a consumable domain**: a ∀ whose domain is a wrapper
applied to its arity is not the full consumption of itself. -/
theorem FullCons.not_refl_of_consumable {Wr : KKey → Option (Option Nat)} {T a b b' : KExpr}
    {m m' : Ix.Kernel.BinderMeta} (hT : consumeAt Wr T = some (some a)) :
    ¬ FullCons Wr (.forallE T b m) (.forallE T b' m') := by
  intro h
  have := h.forallE_dom_none
  rw [hT] at this
  cases this

end IxVM.Refinement.Binding.FamilyRecon
