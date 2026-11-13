import IxVMRefinement.Core.Steps.Whnf
import IxVMRefinement.Nat.Basic
import IxVMRefinement.Obs.KernelInfer0
import IxVMRefinement.Obs.KernelInferOnly0

/-! # Step lemmas of the projection helpers of `KernelInfer` and `KernelInferOnly`

The helpers `k_infer_proj` and the io lane's projection arm call, against their registered specs:

* **Telescopes.** `peel_params_subst` (and `io_peel_params_subst`) instantiates the first `n`
  binders of a constructor type by the parameters (`instPis`), one `expr_inst1` per binder.
  `peel_field_loop` (and `io_peel_field_loop`) walks the field telescope from field `current` to
  field `target`, instantiating each field passed by its projection: the `Proj` node the circuit
  stores is the image `.proj (κ s) current val` (`fieldTypeAt`). The counters are field elements;
  below the target `current + 1` does not wrap, and at `target - current = 0` they are equal.
* **Head reduction through binders.** `peel_n_alls_whnf` head-normalizes and opens a `∀` at the
  next depth, under the ghost context extended by its domain; the freshly stored context cell is
  the context list one longer (`PeelRed`).
* **`Prop` structures.** `is_inductive_prop` reads the sort the inductive's type reduces to; its
  answer `1` comes from `level_equal(u, Zero) = 1` at a freshly stored `Zero`, its answer `0` from
  the positive certificate `level_may_be_nonzero(u) = 1` (a `succ` or a parameter is nonzero at
  some assignment, a `max` when either side is, an `imax` when its right side is). The guards
  (`check_prop_field_if_prop`, `check_no_dep_data_field_if_prop`, `io_prop_field_guard`) read
  `level_equal(u, Zero) = 1` the same way, and `expr_lbr(body) = 0` as a body without loose bound
  variables.
* **Arity.** `proj_shape_ok` reads two `Lists::length` answers; a level list represented up to
  semantic equality has the length of the list the heap holds. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red)
open IxVM.Refinement.KernelLevels (RepKLevel)

set_option linter.unusedVariables false

namespace ProjAux

/-! ## Helpers -/

/-- **The context list reads the ghost context below its depth only.** -/
theorem typesRep_congr_ghost {κ : _root_.Address → KKey} {Γ Γ' : Nat → KExpr} {h : Heap F}
    {d : Nat} {p : SourceValue F} (rep : TypesRep κ Γ h d p) :
    (∀ j, j < d → Γ' j = Γ j) → TypesRep κ Γ' h d p := by
  induction rep with
  | nil cell => exact fun _ => .nil cell
  | @cons d addr tp rest cell rt rr ih =>
    intro hΓ
    have hΓ' : ∀ j, j < d → Γ' j = Γ j := fun j hj => hΓ j (by omega)
    refine .cons cell ?_ (ih hΓ')
    have e : Γ' d = Γ d := hΓ d (Nat.lt_succ_self d)
    rw [e]
    exact Tm.congr_ghost hΓ' rt

/-- `Lists::length` of a represented term list. -/
theorem exprs_length {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {As : List KExpr} {l r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [l] h r h' cs)
    (hl : c.tml d Γ h As l) : r = .field (As.length : F) ∧ h' = h :=
  Lib.Lists.length_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) (R := TmE c.κ d Γ)
    (by rw [Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)

/-- `Lists::length` of a level list represented up to semantic equality: the length of the list
the heap holds, which is the represented list's. -/
theorem levels_length {us : List KLevel} {l r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KLevelNode>» [l] h r h' cs)
    (hl : LvListRep h us l) : r = .field (us.length : F) ∧ h' = h := by
  obtain ⟨ls, rls, hus⟩ := hl
  have hlen : us.length = ls.length := Ix.Kernel.Level.EvalEqList.length_eq (hus fun _ => 0)
  rw [hlen]
  exact Lib.Lists.length_spec (t := .ptr (.named "KernelTypes::KLevelNode" [])) (R := RepKLevel)
    (xs := ls)
    (by rw [Obs.Names.«Lists::length<&KernelTypes::KLevelNode>».symbol]; exact ev)
    (by
      first
        | (rw [Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol]
           have e : Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» =
               IxVM.Refinement.KernelLevels.klevelListEnum := klevelListEnum_eq
           rw [e]
           exact rls)
        | exact rls)

/-! ### Levels read off a loaded cell -/

theorem lv_succ_of_load {h : Heap F} {l : KLevel} {p x : SourceValue F} (rep : RepKLevel h l p)
    (hl : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "Succ" [x])) :
    ∃ v, l = .succ v := by
  cases rep with
  | succ cell _ => exact ⟨_, rfl⟩
  | zero cell | max cell _ _ | imax cell _ _ | param _ cell =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem lv_param_of_load {h : Heap F} {l : KLevel} {p x : SourceValue F} (rep : RepKLevel h l p)
    (hl : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "Param" [x])) :
    ∃ n, l = .param n := by
  cases rep with
  | param _ _ => exact ⟨_, rfl⟩
  | zero cell | succ cell _ | max cell _ _ | imax cell _ _ =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem lv_max_of_load {h : Heap F} {l : KLevel} {p x y : SourceValue F} (rep : RepKLevel h l p)
    (hl : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "Max" [x, y])) :
    ∃ u v, l = .max u v ∧ RepKLevel h u x ∧ RepKLevel h v y := by
  cases rep with
  | max cell ru rv =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx hrest; injection hrest with hy
    subst hx hy; exact ⟨_, _, rfl, ru, rv⟩
  | zero cell | succ cell _ | imax cell _ _ | param _ cell =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem lv_imax_of_load {h : Heap F} {l : KLevel} {p x y : SourceValue F} (rep : RepKLevel h l p)
    (hl : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "IMax" [x, y])) :
    ∃ u v, l = .imax u v ∧ RepKLevel h u x ∧ RepKLevel h v y := by
  cases rep with
  | imax cell ru rv =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx hrest; injection hrest with hy
    subst hx hy; exact ⟨_, _, rfl, ru, rv⟩
  | zero cell | succ cell _ | max cell _ _ | param _ cell =>
    exact (load_cell_ne cell hl (by decide)).elim

/-! ### Non-zero levels -/

theorem eval_succ_ne_zero (φ : Nat → Nat) (a : KLevel) :
    Ix.Kernel.Level.eval φ (.succ a) ≠ 0 := by
  have h1 : Ix.Kernel.Level.eval φ (.succ a) = Ix.Kernel.Level.eval φ a + 1 := by
    first | rfl | simp only [Ix.Kernel.Level.eval]
  omega

theorem not_all_zero_param (n : Nat) :
    ¬ ∀ φ : Nat → Nat, Ix.Kernel.Level.eval φ (.param n) = 0 := by
  intro hall
  have h2 : Ix.Kernel.Level.eval (fun _ => 1) (.param n) = 0 := hall _
  have h1 : Ix.Kernel.Level.eval (fun _ => 1) (.param n) = 1 := by
    first | rfl | simp [Ix.Kernel.Level.eval]
  exact Nat.one_ne_zero (h1.symm.trans h2)

theorem eval_max_eq (φ : Nat → Nat) (a b : KLevel) :
    Ix.Kernel.Level.eval φ (.max a b) =
      Max.max (Ix.Kernel.Level.eval φ a) (Ix.Kernel.Level.eval φ b) := by
  first | rfl | simp only [Ix.Kernel.Level.eval]

theorem eval_max_ne_zero_left {φ : Nat → Nat} {a b : KLevel}
    (ha : Ix.Kernel.Level.eval φ a ≠ 0) : Ix.Kernel.Level.eval φ (.max a b) ≠ 0 := by
  have h1 := eval_max_eq φ a b
  have h2 := Nat.le_max_left (Ix.Kernel.Level.eval φ a) (Ix.Kernel.Level.eval φ b)
  omega

theorem eval_max_ne_zero_right {φ : Nat → Nat} {a b : KLevel}
    (hb : Ix.Kernel.Level.eval φ b ≠ 0) : Ix.Kernel.Level.eval φ (.max a b) ≠ 0 := by
  have h1 := eval_max_eq φ a b
  have h2 := Nat.le_max_right (Ix.Kernel.Level.eval φ a) (Ix.Kernel.Level.eval φ b)
  omega

/-- `imax a b` is nonzero where `b` is. -/
theorem eval_imax_ne_zero {φ : Nat → Nat} {a b : KLevel}
    (hb : Ix.Kernel.Level.eval φ b ≠ 0) : Ix.Kernel.Level.eval φ (.imax a b) ≠ 0 := by
  have e : Ix.Kernel.Level.eval φ (.imax a b) =
      if Ix.Kernel.Level.eval φ b = 0 then 0
      else Max.max (Ix.Kernel.Level.eval φ a) (Ix.Kernel.Level.eval φ b) := by
    first | rfl | simp only [Ix.Kernel.Level.eval]
  have hb' : ¬ (Ix.Kernel.Level.eval φ b = 0) := hb
  have h1 : Ix.Kernel.Level.eval φ (.imax a b) =
      Max.max (Ix.Kernel.Level.eval φ a) (Ix.Kernel.Level.eval φ b) := by
    rw [e, ite_eq_right hb']
  have h2 := Nat.le_max_right (Ix.Kernel.Level.eval φ a) (Ix.Kernel.Level.eval φ b)
  omega

/-- **The answer `1` of `level_equal(l, Zero)`**: `l` is zero at every assignment, so is every
level semantically equal to it. -/
theorem eval_zero_of_answer {u l : KLevel} (hul : LvEq u l)
    (hr : (Value.field (1 : F) : SourceValue F) =
      .field (if IxVM.Refinement.KernelLevels.levelEqual l .zero then 1 else 0)) :
    ∀ φ, Ix.Kernel.Level.eval φ u = 0 := by
  have hle : IxVM.Refinement.KernelLevels.levelEqual l .zero = true := by
    by_contra hn
    rw [ite_eq_right hn] at hr
    exact field_one_ne_zero hr
  intro φ
  have h1 := hul φ
  have h2 := IxVM.Refinement.KernelLevels.levelEqual_eq_true_sound hle φ
  have h3 : Ix.Kernel.Level.eval φ Ix.Kernel.Level.zero = 0 := by
    first | rfl | simp [Ix.Kernel.Level.eval]
  exact h1.trans (h2.trans h3)

/-- **`level_equal(p, Zero) = 1` at a freshly stored `Zero` cell**: the level `p` represents is
zero at every assignment. -/
theorem zero_of_level_equal {c : Ctx} {calls : List (Call F)} (ih : IH c calls) {m m' : Heap F}
    {u : KLevel} {p : SourceValue F} {cs : List (Call F)} (hu : LvRep m u p)
    (ev : ObsFn W "KernelLevels::level_equal" [p, .ptr (.enum "KernelTypes::KLevelNode") m.length]
      (m ++ [.construct "KernelTypes::KLevelNode" "Zero" []]) (.field 1) m' cs)
    (hlt : cs.length < calls.length) (hb : IxVM.Consistency.Bounded cs) :
    ∀ φ, Ix.Kernel.Level.eval φ u = 0 := by
  obtain ⟨l, rl, hul⟩ := hu
  obtain ⟨hr, -⟩ := ih.get (.levelOps .level_equal) hlt ev _ _ rfl hb l .zero
    (rl.mono (Heap.Extends.snoc _ _)) (IxVM.Refinement.KernelLevels.RepKLevel.allocZero m).1
  exact eval_zero_of_answer hul hr

/-- **The loop counters**: with `current ≤ target` as naturals and `target - current ≠ 0` in the
field, `current + 1` does not wrap and stays at or below the target. -/
theorem counter_step {t0 c0 : F} (hle : ZMod.val c0 ≤ ZMod.val t0)
    (hne : (Value.field (t0 - c0) : SourceValue F) ≠ .field 0) :
    ZMod.val (c0 + 1) = ZMod.val c0 + 1 ∧ ZMod.val c0 + 1 ≤ ZMod.val t0 := by
  have hne' : t0 ≠ c0 := fun e => hne (by rw [e, sub_self])
  have hlt : ZMod.val c0 < ZMod.val t0 := by
    rcases Nat.lt_or_eq_of_le hle with h1 | h1
    · exact h1
    · exact absurd (ZMod.val_injective _ h1).symm hne'
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  have hlt0 := ZMod.val_lt t0
  exact ⟨NatAux.val_add_one (by omega), by omega⟩

/-- At `target - current = 0` the counters are equal. -/
theorem counter_eq {t0 c0 : F}
    (op : evalBinOp .sub (.field t0 : SourceValue F) (.field c0) = .ok (.field 0)) : t0 = c0 :=
  sub_eq_zero.mp (NatAux.field_inj (NatAux.sub_ok op)).symm

end ProjAux

/-! ## `peel_params_subst` -/

/-- `KernelInfer::peel_params_subst` instantiates the first `n` binders by the parameters. -/
theorem peel_params_subst_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::peel_params_subst" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.peel_params_subst c args h r h' calls := by
  intro ty sp np hargs good n hn d Γ T As hT hAs
  subst hargs hn
  rcases Obs.«KernelInfer::peel_params_subst».obs ev with
    ⟨hv14, he16, he17, hc18⟩ |
    ⟨w42, x_body, w43, x_arg, x_rest, v88, m89, cs99, cs128, v133, hne19, ld34, ld70, ev101,
      op161, ev130, hc163⟩
  · -- no parameter left
    have hn0 : n = 0 := NatAux.field_inj hv14
    subst hn0 he16 he17
    exact ⟨T, hT, by first | rfl | simp [Specs.Infer.instPis]⟩
  · -- one binder instantiated by the first parameter
    subst hc163
    obtain ⟨T0, B, ℓ, rfl, -, hB, -⟩ := hT.forallE_of_load ld34
    obtain ⟨A, As', rfl, hA, hAs'⟩ := RepList.cons_of_load hAs ld70
    have hinst := ih.get (.subst .expr_inst1) (by lt_calls) ev101 _ _ 0 rfl
      (good.sub fun x hx => by simp [hx]) d Γ B A (by simpa using hB) hA
    simp only [ZMod.val_zero] at hinst
    have ext := ObsFn.heap_extends ev101
    have hv : v133 = .field (n - 1) := NatAux.sub_ok op161
    subst hv
    obtain ⟨T', hT', hpi⟩ := ih.get (.infer .peel_params_subst) (by lt_calls) ev130 _ _ _ rfl
      (good.sub fun x hx => by simp [hx]) _ rfl d Γ _ As' hinst (tml_mono ext hAs')
    have hn0 := NatAux.field_ne_zero_val hne19
    have hn1 := NatAux.val_sub_one (x := n) (fun e => hne19 (by rw [e]))
    have hval : ZMod.val n = ZMod.val (n - 1) + 1 := by omega
    refine ⟨T', hT', ?_⟩
    rw [hval]
    first
      | exact hpi
      | simpa only [Specs.Infer.instPis] using hpi

/-- `KernelInferOnly::io_peel_params_subst`: as `peel_params_subst`. -/
theorem io_peel_params_subst_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInferOnly::io_peel_params_subst" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.io_peel_params_subst c args h r h' calls := by
  intro ty sp np hargs good n hn d Γ T As hT hAs
  subst hargs hn
  rcases Obs.«KernelInferOnly::io_peel_params_subst».obs ev with
    ⟨hv14, he16, he17, hc18⟩ |
    ⟨w42, x_body, w43, x_arg, x_rest, v88, m89, cs99, cs128, v133, hne19, ld34, ld70, ev101,
      op161, ev130, hc163⟩
  · have hn0 : n = 0 := NatAux.field_inj hv14
    subst hn0 he16 he17
    exact ⟨T, hT, by first | rfl | simp [Specs.Infer.instPis]⟩
  · subst hc163
    obtain ⟨T0, B, ℓ, rfl, -, hB, -⟩ := hT.forallE_of_load ld34
    obtain ⟨A, As', rfl, hA, hAs'⟩ := RepList.cons_of_load hAs ld70
    have hinst := ih.get (.subst .expr_inst1) (by lt_calls) ev101 _ _ 0 rfl
      (good.sub fun x hx => by simp [hx]) d Γ B A (by simpa using hB) hA
    simp only [ZMod.val_zero] at hinst
    have ext := ObsFn.heap_extends ev101
    have hv : v133 = .field (n - 1) := NatAux.sub_ok op161
    subst hv
    obtain ⟨T', hT', hpi⟩ := ih.get (.infer .io_peel_params_subst) (by lt_calls) ev130 _ _ _ rfl
      (good.sub fun x hx => by simp [hx]) _ rfl d Γ _ As' hinst (tml_mono ext hAs')
    have hn0 := NatAux.field_ne_zero_val hne19
    have hn1 := NatAux.val_sub_one (x := n) (fun e => hne19 (by rw [e]))
    have hval : ZMod.val n = ZMod.val (n - 1) + 1 := by omega
    refine ⟨T', hT', ?_⟩
    rw [hval]
    first
      | exact hpi
      | simpa only [Specs.Infer.instPis] using hpi

/-! ## `proj_shape_ok` -/

/-- `KernelInfer::proj_shape_ok` asserts no indices and the two counts. -/
theorem proj_shape_ok_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::proj_shape_ok" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.proj_shape_ok c args h r h' calls := by
  intro ni sp np lvls nl hargs good d Γ As us hAs hus
  subst hargs
  obtain ⟨v39, m42, cs50, v80, m83, cs91, heq27, ev52, heq68, ev93, heq109, he112, he113, hc114⟩ :=
    Obs.«KernelInfer::proj_shape_ok».obs ev
  obtain ⟨hv39, hm42⟩ := ProjAux.exprs_length ev52 hAs
  subst hm42
  obtain ⟨hv80, hm83⟩ := ProjAux.levels_length ev93 hus
  exact ⟨heq27, heq68.symm.trans hv39, heq109.symm.trans hv80, he113.trans hm83⟩

/-! ## `level_may_be_nonzero` -/

/-- `KernelInfer::level_may_be_nonzero` answers `1` only on a level nonzero at some assignment. -/
theorem level_may_be_nonzero_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::level_may_be_nonzero" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.level_may_be_nonzero c args h r h' calls := by
  intro x u hargs good hu
  subst hargs
  obtain ⟨l, rl, hul⟩ := hu
  refine (fun (H : h' = h ∧ (r = .field 1 → ¬ ∀ φ, Ix.Kernel.Level.eval φ l = 0)) =>
    ⟨H.1, fun h1 hall => H.2 h1 fun φ => (hul φ).symm.trans (hall φ)⟩) ?_
  rcases Obs.«KernelInfer::level_may_be_nonzero».obs ev with
    ⟨ld12, he20, he21, hc22⟩ |
    ⟨w30, ld12, he36, he37, hc38⟩ |
    ⟨w46, ld12, he52, he53, hc54⟩ |
    ⟨x_a, x_b, m73, cs84, ld12, ev86, he99, he100, hc101⟩ |
    ⟨x_a, x_b, v72, m73, cs84, cs109, ld12, ev86, hne102, ev111, hc120⟩ |
    ⟨w128, x_b, cs142, ld12, ev144, hc153⟩
  · -- `zero`: answer `0`
    subst he20
    exact ⟨he21, fun h1 => absurd h1.symm field_one_ne_zero⟩
  · -- `succ`
    obtain ⟨v, rfl⟩ := ProjAux.lv_succ_of_load rl ld12
    exact ⟨he37, fun _ hall => ProjAux.eval_succ_ne_zero (fun _ => 0) v (hall _)⟩
  · -- a parameter
    obtain ⟨p, rfl⟩ := ProjAux.lv_param_of_load rl ld12
    exact ⟨he53, fun _ => ProjAux.not_all_zero_param p⟩
  · -- `max`, its left side certified
    obtain ⟨la, lb, rfl, ra, rb⟩ := ProjAux.lv_max_of_load rl ld12
    subst hc101
    obtain ⟨hm, hnz⟩ := ih.get (.infer .level_may_be_nonzero) (by lt_calls) ev86 _ la rfl
      (good.sub fun x hx => by simp [hx]) ⟨la, ra, LvEq.refl la⟩
    refine ⟨he100.trans hm, fun _ hall => hnz rfl fun φ => ?_⟩
    by_contra hne
    exact ProjAux.eval_max_ne_zero_left (b := lb) hne (hall φ)
  · -- `max`, its right side's answer
    obtain ⟨la, lb, rfl, ra, rb⟩ := ProjAux.lv_max_of_load rl ld12
    subst hc120
    obtain ⟨hm, -⟩ := ih.get (.infer .level_may_be_nonzero) (by lt_calls) ev86 _ la rfl
      (good.sub fun x hx => by simp [hx]) ⟨la, ra, LvEq.refl la⟩
    subst hm
    obtain ⟨hm', hnz⟩ := ih.get (.infer .level_may_be_nonzero) (by lt_calls) ev111 _ lb rfl
      (good.sub fun x hx => by simp [hx]) ⟨lb, rb, LvEq.refl lb⟩
    refine ⟨hm', fun h1 hall => hnz h1 fun φ => ?_⟩
    by_contra hne
    exact ProjAux.eval_max_ne_zero_right (a := la) hne (hall φ)
  · -- `imax`: its right side's answer
    obtain ⟨la, lb, rfl, ra, rb⟩ := ProjAux.lv_imax_of_load rl ld12
    subst hc153
    obtain ⟨hm, hnz⟩ := ih.get (.infer .level_may_be_nonzero) (by lt_calls) ev144 _ lb rfl
      (good.sub fun x hx => by simp [hx]) ⟨lb, rb, LvEq.refl lb⟩
    refine ⟨hm, fun h1 hall => hnz h1 fun φ => ?_⟩
    by_contra hne
    exact ProjAux.eval_imax_ne_zero (a := la) hne (hall φ)

/-! ## `peel_n_alls_whnf` -/

/-- `KernelInfer::peel_n_alls_whnf` head-normalizes and opens at most `n` `∀`-binders. -/
theorem peel_n_alls_whnf_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::peel_n_alls_whnf" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.peel_n_alls_whnf c args h r h' calls := by
  intro rc ee ns types hargs good hrc n hn d Γ htypes E hE
  subst hargs hn
  rcases Obs.«KernelInfer::peel_n_alls_whnf».obs ev with
    ⟨cs18, hv14, ev20, hc45⟩ |
    ⟨v50, m51, cs61, x_dom, x_body, w107, m124, cs157, v162, hne46, ev63, ld99, hm134, op191,
      ev159, hc200⟩ |
    ⟨v50, m51, cs61, v88, hne46, ev63, ld99, hne201, he206, he207, hc208⟩
  · -- no binder left: head-normalize
    subst hc45
    obtain ⟨E', hE', hred⟩ := ih.get (.whnf .whnf) (by lt_calls) ev20 _ _ _ rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes E hE
    exact ⟨0, Γ, E', Nat.zero_le _, fun _ _ => rfl, hE', .done hred⟩
  · -- a `∀` after head normalization: open it under the extended ghost context and go on
    subst hc200 hm134
    obtain ⟨E', hE', hred⟩ := ih.get (.whnf .whnf) (by lt_calls) ev63 _ _ _ rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes E hE
    obtain ⟨D, B, ℓ, rfl, hD, hB, -⟩ := hE'.forallE_of_load ld99
    have hv : v162 = .field (n - 1) := NatAux.sub_ok op191
    subst hv
    have e0 := ObsFn.heap_extends ev63
    have e1 : Heap.Extends m51 (m51 ++ [.construct kexprListEnum "Cons" [x_dom, types]]) :=
      Heap.Extends.snoc _ _
    have hsc : GhostScoped Γ d := htypes.2
    obtain ⟨Γ'', hat, hbelow, hsc''⟩ : ∃ Γ'' : Nat → KExpr, Γ'' d = D ∧
        (∀ j, j < d → Γ'' j = Γ j) ∧ GhostScoped Γ'' (d + 1) :=
      ⟨Ghost.extend Γ d D, Ghost.extend_at Γ d D, Ghost.extend_below Γ d D,
        GhostScoped.extend hsc (Tm.wscopedB hsc hD)⟩
    have htypes' : c.types Γ'' (m51 ++ [.construct kexprListEnum "Cons" [x_dom, types]]) (d + 1)
        (.ptr (.enum kexprListEnum) m51.length) := by
      refine ⟨TypesRep.cons (tp := x_dom) (by simp) ?_
        (ProjAux.typesRep_congr_ghost ((htypes.1.mono e0).mono e1) hbelow), hsc''⟩
      rw [hat]
      exact Tm.congr_ghost hbelow (Tm.mono e1 hD)
    have hB1 : Tm c.κ d Γ m51 1 B x_body := hB
    have hbody := Tm.open_body hat hbelow (Tm.mono e1 hB1)
    obtain ⟨k, Γ', R, hk, hag, hR, hpeel⟩ := ih.get (.infer .peel_n_alls_whnf) (by lt_calls)
      ev159 _ _ _ _ rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono (e0.trans e1) hrc) _ rfl
      (d + 1) Γ'' htypes' _ hbody
    have hΓd : Γ' d = D := (hag d (Nat.lt_succ_self d)).trans hat
    have hn0 := NatAux.field_ne_zero_val hne46
    have hn1 := NatAux.val_sub_one (x := n) (fun e => hne46 (by rw [e]))
    have h1 : Red c.env d E (.forallE (Γ' d) B (bmeta ℓ)) := by rw [hΓd]; exact hred
    have h2 : Specs.Infer.PeelRed c.env Γ' (d + 1) (B.instantiate1 (.fvar d (Γ' d))) k R := by
      rw [hΓd]; exact hpeel
    refine ⟨k + 1, Γ', R, by omega, fun j hj => (hag j (by omega)).trans (hbelow j hj), ?_,
      .step h1 h2⟩
    have e : d + (k + 1) = d + 1 + k := by omega
    rw [e]
    exact hR
  · -- not a `∀`: stop at the head-normal form
    subst hc208 he206 he207
    obtain ⟨E', hE', hred⟩ := ih.get (.whnf .whnf) (by lt_calls) ev63 _ _ _ rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes E hE
    exact ⟨0, Γ, E', Nat.zero_le _, fun _ _ => rfl, hE', .done hred⟩

/-! ## `is_inductive_prop` -/

/-- `KernelInfer::is_inductive_prop` decides whether the inductive's sort is zero, both ways. -/
theorem is_inductive_prop_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::is_inductive_prop" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.is_inductive_prop c args h r h' calls := by
  intro rc ity lvls ns types hargs good hrc n hn d Γ htypes I us hI hus
  subst hargs hn
  rcases Obs.«KernelInfer::is_inductive_prop».obs ev with
    ⟨v1, m2, cs12, v31, m32, cs42, x_l, m102, cs113, m126, ev14, ev44, ld88, hm134, ev115, he142,
      he143, hc144⟩ |
    ⟨v1, m2, cs12, v31, m32, cs42, x_l, v101, m102, cs113, m126, v160, m163, cs171, ev14, ev44,
      ld88, hm134, ev115, hne145, ev173, heq188, he189, he190, hc191⟩
  · -- `level_equal(u, Zero) = 1`: answer `1`
    subst hc144 hm134 he142
    have hinst := ih.get (.subst .expr_inst_levels) (by lt_calls) ev14 _ _ rfl
      (good.sub fun x hx => by simp [hx]) Γ 0 I us (hI 0 Γ) hus
    have e0 := ObsFn.heap_extends ev14
    obtain ⟨k, Γ', R, hk, hag, hR, hpeel⟩ := ih.get (.infer .peel_n_alls_whnf) (by lt_calls) ev44
      _ _ _ _ rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) _ rfl d Γ
      (types_mono e0 htypes) _ (Tm.of_depth_zero hinst d)
    obtain ⟨u, rfl, hu⟩ := hR.sort_of_load ld88
    have g113 : Good c cs113 := good.sub fun x hx => by simp [hx]
    exact ⟨k, Γ', u, hk, hag, hpeel, .inl rfl,
      fun _ => ProjAux.zero_of_level_equal ih hu ev115 (by lt_calls) g113.2,
      fun h0 => absurd h0 field_one_ne_zero⟩
  · -- `level_may_be_nonzero(u) = 1`: answer `0`
    subst hc191 hm134 he189 heq188
    have hinst := ih.get (.subst .expr_inst_levels) (by lt_calls) ev14 _ _ rfl
      (good.sub fun x hx => by simp [hx]) Γ 0 I us (hI 0 Γ) hus
    have e0 := ObsFn.heap_extends ev14
    obtain ⟨k, Γ', R, hk, hag, hR, hpeel⟩ := ih.get (.infer .peel_n_alls_whnf) (by lt_calls) ev44
      _ _ _ _ rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) _ rfl d Γ
      (types_mono e0 htypes) _ (Tm.of_depth_zero hinst d)
    obtain ⟨u, rfl, hu⟩ := hR.sort_of_load ld88
    have e2 : Heap.Extends m32 m102 :=
      (Heap.Extends.snoc _ _).trans (ObsFn.heap_extends ev115)
    obtain ⟨-, hnz⟩ := ih.get (.infer .level_may_be_nonzero) (by lt_calls) ev173 _ u rfl
      (good.sub fun x hx => by simp [hx]) (LvRep.mono e2 hu)
    exact ⟨k, Γ', u, hk, hag, hpeel, .inr rfl, fun h1 => absurd h1.symm field_one_ne_zero,
      fun _ => hnz rfl⟩

/-! ## The `Prop`-structure guards -/

/-- `KernelInfer::check_prop_field_if_prop`: at a `Prop` structure the field's sort is zero. -/
theorem check_prop_field_if_prop_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::check_prop_field_if_prop" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.check_prop_field_if_prop c args h r h' calls := by
  intro rc ip dom types hargs good hrc hip d Γ htypes D hD
  subst hargs
  rcases Obs.«KernelInfer::check_prop_field_if_prop».obs ev with
    ⟨hv14, he17, he18, hc19⟩ |
    ⟨v24, m25, cs35, v73, m76, cs84, m97, hne20, ev37, hm105, ev86, heq115, he118, he119, hc120⟩
  · exact absurd hv14 hip
  · subst hc120 hm105 heq115
    obtain ⟨T, u, hinf, hred, hu⟩ := ih.get (.infer .k_ensure_sort) (by lt_calls) ev37 _ _ _ rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes D hD
    have g84 : Good c cs84 := good.sub fun x hx => by simp [hx]
    exact ⟨T, u, hinf, hred, ProjAux.zero_of_level_equal ih hu ev86 (by lt_calls) g84.2⟩

/-- `KernelInfer::check_no_dep_data_field_if_prop`: at a `Prop` structure a field passed is a
proposition or the rest of the telescope has no loose bound variable. -/
theorem check_no_dep_data_field_if_prop_step (c : Ctx) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::check_no_dep_data_field_if_prop" args h r h' calls)
    (ih : IH c calls) :
    Specs.Infer.check_no_dep_data_field_if_prop c args h r h' calls := by
  intro rc ip dom body types hargs good hrc hip d Γ htypes D B hD hB
  subst hargs
  rcases Obs.«KernelInfer::check_no_dep_data_field_if_prop».obs ev with
    ⟨hv14, he17, he18, hc19⟩ |
    ⟨v24, m25, cs35, m63, cs74, m87, hne20, ev37, hm95, ev76, he105, he106, hc107⟩ |
    ⟨v24, m25, cs35, v62, m63, cs74, m87, v123, m126, cs134, hne20, ev37, hm95, ev76, hne108,
      ev136, heq151, he154, he155, hc156⟩
  · exact absurd hv14 hip
  · -- the field is a proposition
    subst hc107 hm95
    obtain ⟨T, u, hinf, hred, hu⟩ := ih.get (.infer .k_ensure_sort) (by lt_calls) ev37 _ _ _ rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes D hD
    have g74 : Good c cs74 := good.sub fun x hx => by simp [hx]
    exact .inl ⟨T, u, hinf, hred, ProjAux.zero_of_level_equal ih hu ev76 (by lt_calls) g74.2⟩
  · -- the rest of the telescope has no loose bound variable
    subst hc156 hm95 heq151
    have ext : Heap.Extends h m63 :=
      (ObsFn.heap_extends ev37).trans ((Heap.Extends.snoc _ _).trans (ObsFn.heap_extends ev76))
    obtain ⟨-, hlbr⟩ := ih.get (.subst .expr_lbr) (by lt_calls) ev136 _ rfl
      (good.sub fun x hx => by simp [hx])
    obtain ⟨b, hb, hbi, -, -, -, hle⟩ := hlbr d Γ 1 B (Tm.mono ext hB)
    have hb0 : b = 0 := by
      have e := NatAux.field_inj hb
      have hbi' : b ≤ 9223372036854775808 := hbi
      exact (NatAux.natCast_eq_zero_iff (by omega)).mp e.symm
    subst hb0
    exact .inr (hle (Nat.zero_le 1)).1

/-- `KernelInferOnly::io_prop_field_guard`: at a `Prop` structure the field's io-grade sort is
zero. -/
theorem io_prop_field_guard_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInferOnly::io_prop_field_guard" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.io_prop_field_guard c args h r h' calls := by
  intro rc ip ft types hargs good hrc hip d Γ htypes FT hFT
  subst hargs
  rcases Obs.«KernelInferOnly::io_prop_field_guard».obs ev with
    ⟨hv14, he17, he18, hc19⟩ |
    ⟨v35, m38, cs46, v49, m52, cs60, m88, hne20, ev62, hm96, ev48, heq106, he109, he110, hc111⟩
  · exact absurd hv14 hip
  · subst hc111 hm96 heq106
    obtain ⟨T, u, hinf, hred, hu⟩ := ih.get (.infer .ensure_sort_only) (by lt_calls) ev62 _ _ _
      rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes FT hFT
    have g46 : Good c cs46 := good.sub fun x hx => by simp [hx]
    exact ⟨T, u, hinf, hred, ProjAux.zero_of_level_equal ih hu ev48 (by lt_calls) g46.2⟩

/-! ## The field telescope -/

/-- `KernelInfer::peel_field_loop`: the projected field's type, the fields passed instantiated by
their projections, with the `Prop`-structure guards. -/
theorem peel_field_loop_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::peel_field_loop" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.peel_field_loop c args h r h' calls := by
  intro rc ty tg cu sa val ip types hargs good hrc t0 c0 htg hcu hle d Γ htypes T a PE hT ha hPE
  subst hargs htg hcu
  rcases Obs.«KernelInfer::peel_field_loop».obs ev with
    ⟨x_dom, x_body, w20, v59, m60, cs70, ld12, op52, ev72, he106, he107, hc108⟩ |
    ⟨x_dom, x_body, w20, v36, v113, m114, cs124, m168, v206, m207, cs217, cs246, v252, ld12, op52,
      hne109, ev126, hm178, ev219, op291, ev248, hc321⟩
  · -- the target field: its domain, with the field's guard
    subst hc108 he106 he107
    obtain ⟨D, B, ℓ, rfl, hD, hB, -⟩ := hT.forallE_of_load ld12
    have htc : t0 = c0 := ProjAux.counter_eq op52
    subst htc
    refine ⟨0, D, by omega, Tm.mono (ObsFn.heap_extends ev72) hD,
      by first | rfl | simp [Specs.Infer.fieldTypeAt], fun hip => ?_⟩
    have hg : Specs.Infer.SortZero c.env .full d D :=
      ih.get (.infer .check_prop_field_if_prop) (by lt_calls) ev72 _ _ _ _ rfl
        (good.sub fun x hx => by simp [hx]) hrc hip d Γ htypes D hD
    first
      | exact hg
      | (simp only [Specs.Infer.PropGuards]; exact hg)
  · -- a field passed: guard it, instantiate it by its projection, go on
    subst hc321 hm178
    obtain ⟨D, B, ℓ, rfl, hD, hB, -⟩ := hT.forallE_of_load ld12
    have hv36 : v36 = .field (t0 - c0) := NatAux.sub_ok op52
    subst hv36
    have hv252 : v252 = .field (c0 + 1) := NatAux.add_ok op291
    subst hv252
    obtain ⟨hc1, hle1⟩ := ProjAux.counter_step hle hne109
    have e1 := ObsFn.heap_extends ev126
    have e2 : Heap.Extends m114
        (m114 ++ [.construct "KernelTypes::KExprNode" "Proj" [sa, .field c0, val]]) :=
      Heap.Extends.snoc _ _
    have e12 := e1.trans e2
    have ext := e12.trans (ObsFn.heap_extends ev219)
    have hP : Tm c.κ d Γ (m114 ++ [.construct "KernelTypes::KExprNode" "Proj" [sa, .field c0, val]])
        0 (.proj (c.κ (ixAddr a)) (ZMod.val c0) PE) (.ptr (.enum kexprEnum) m114.length) :=
      Tm.proj (by simp) (Bytes.repAddressRef_heapMono₂ addrTy e12 ha) (Tm.mono e12 hPE)
    have hinst := ih.get (.subst .expr_inst1) (by lt_calls) ev219 _ _ 0 rfl
      (good.sub fun x hx => by simp [hx]) d Γ B _ (by simpa using Tm.mono e12 hB) hP
    simp only [ZMod.val_zero] at hinst
    obtain ⟨n, FT, hn, hFT, hfield, hguards⟩ := ih.get (.infer .peel_field_loop) (by lt_calls)
      ev248 _ _ _ _ _ _ _ _ rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) t0
      (c0 + 1) rfl rfl (by omega) d Γ (types_mono ext htypes) _ a PE hinst
      (Bytes.repAddressRef_heapMono₂ addrTy ext ha) (Tm.mono ext hPE)
    rw [hc1] at hfield hguards
    refine ⟨n + 1, FT, by omega, hFT, ?_, fun hip => ?_⟩
    · first
        | exact hfield
        | simpa only [Specs.Infer.fieldTypeAt] using hfield
    · have hg : Specs.Infer.SortZero c.env .full d D ∨ B.looseBVarsBounded 0 = true :=
        ih.get (.infer .check_no_dep_data_field_if_prop) (by lt_calls) ev126 _ _ _ _ _ rfl
          (good.sub fun x hx => by simp [hx]) hrc hip d Γ htypes D B hD (by simpa using hB)
      first
        | exact And.intro hg (hguards hip)
        | (simp only [Specs.Infer.PropGuards]; exact ⟨hg, hguards hip⟩)

/-- `KernelInferOnly::io_peel_field_loop`: the projected field's type, without guards. -/
theorem io_peel_field_loop_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInferOnly::io_peel_field_loop" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.io_peel_field_loop c args h r h' calls := by
  intro ty tg cu sa val hargs good t0 c0 htg hcu hle d Γ T a PE hT ha hPE
  subst hargs htg hcu
  rcases Obs.«KernelInferOnly::io_peel_field_loop».obs ev with
    ⟨x_dom, x_body, w20, ld12, op52, he60, he61, hc62⟩ |
    ⟨x_dom, x_body, w20, v36, m68, v106, m107, cs117, cs146, v151, ld12, op52, hne63, hm78, ev119,
      op181, ev148, hc197⟩
  · -- the target field: its domain
    subst he60 he61
    obtain ⟨D, B, ℓ, rfl, hD, hB, -⟩ := hT.forallE_of_load ld12
    have htc : t0 = c0 := ProjAux.counter_eq op52
    subst htc
    exact ⟨0, D, by omega, hD, by first | rfl | simp [Specs.Infer.fieldTypeAt]⟩
  · -- a field passed: instantiate it by its projection, go on
    subst hc197 hm78
    obtain ⟨D, B, ℓ, rfl, hD, hB, -⟩ := hT.forallE_of_load ld12
    have hv36 : v36 = .field (t0 - c0) := NatAux.sub_ok op52
    subst hv36
    have hv151 : v151 = .field (c0 + 1) := NatAux.add_ok op181
    subst hv151
    obtain ⟨hc1, hle1⟩ := ProjAux.counter_step hle hne63
    have e1 : Heap.Extends h
        (h ++ [.construct "KernelTypes::KExprNode" "Proj" [sa, .field c0, val]]) :=
      Heap.Extends.snoc _ _
    have ext := e1.trans (ObsFn.heap_extends ev119)
    have hP : Tm c.κ d Γ (h ++ [.construct "KernelTypes::KExprNode" "Proj" [sa, .field c0, val]])
        0 (.proj (c.κ (ixAddr a)) (ZMod.val c0) PE) (.ptr (.enum kexprEnum) h.length) :=
      Tm.proj (by simp) (Bytes.repAddressRef_heapMono₂ addrTy e1 ha) (Tm.mono e1 hPE)
    have hinst := ih.get (.subst .expr_inst1) (by lt_calls) ev119 _ _ 0 rfl
      (good.sub fun x hx => by simp [hx]) d Γ B _ (by simpa using Tm.mono e1 hB) hP
    simp only [ZMod.val_zero] at hinst
    obtain ⟨n, FT, hn, hFT, hfield⟩ := ih.get (.infer .io_peel_field_loop) (by lt_calls) ev148
      _ _ _ _ _ rfl (good.sub fun x hx => by simp [hx]) t0 (c0 + 1) rfl rfl (by omega) d Γ _ a
      PE hinst (Bytes.repAddressRef_heapMono₂ addrTy ext ha) (Tm.mono ext hPE)
    rw [hc1] at hfield
    refine ⟨n + 1, FT, by omega, hFT, ?_⟩
    first
      | exact hfield
      | simpa only [Specs.Infer.fieldTypeAt] using hfield

end IxVM.Refinement.Core
