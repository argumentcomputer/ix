import IxVMRefinement.Infer.Basic
import IxVMRefinement.Infer.Close
import IxVMRefinement.Infer.ProjBody
import IxVMRefinement.Whnf.Proj
import IxVMRefinement.Obs.KernelCheck1

/-! # Step lemmas of the projection helpers of `KernelInfer` and `KernelInferOnly`

The helpers `k_infer_proj` and the io lane's projection arm call, against their registered specs,
together with `k_infer_proj_step` and the shared projection derivation (`infer_proj_common`):

* **Telescopes.** `peel_params_subst` (and `io_peel_params_subst`) instantiates the first `n`
  binders of a constructor type by the parameters (`instPis`), one `expr_inst1` per binder.
  `peel_field_loop` walks the field telescope from field `current` to field `target`, instantiating
  each field passed by its projection: the `Proj` node the circuit stores is the image
  `.proj (κ s) current val` (`fieldTypeAt`). The counters are field elements; below the target
  `current + 1` does not wrap, and at `target - current = 0` they are equal.
* **Head reduction through binders.** `peel_n_alls_whnf` head-normalizes and opens a `∀` at the
  next depth, under the ghost context extended by its domain; the freshly stored context cell is
  the context list one longer (`PeelRed`).
* **`Prop` structures.** `is_inductive_prop` reads the sort the inductive's declared type reduces
  to from depth `0`; its answer `1` comes from `level_equal(u, Zero) = 1` at a freshly stored
  `Zero`, its answer `0` from the positive certificate `level_may_be_nonzero(u) = 1` (a `succ` or
  a parameter is nonzero at some assignment, a `max` when either side is, an `imax` when its right
  side is).
* **Arity.** `proj_shape_ok` reads two `Lists::length` answers; a level list represented up to
  semantic equality has the length of the list the heap holds.
* **Projection guard and `Infer.proj`.** `proj_guard` computes a represented positional guard level
  by opening the constructor's parameter and field telescopes (`peel_n_foralls_with_types`,
  `proj_guard_walk`, `proj_guard_fold`), and `prop_guard_ok` certifies that the guard instantiated
  at the use-site levels evaluates to zero whenever the structure is in `Prop` (`FireSem`). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red Infer)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)

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
      rw [Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol]
      have e : Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» =
          IxVM.Refinement.KernelLevels.klevelListEnum := klevelListEnum_eq
      rw [e]
      exact rls)

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
  have h1 : Ix.Kernel.Level.eval φ (.succ a) = Ix.Kernel.Level.eval φ a + 1 := rfl
  omega

theorem not_all_zero_param (n : Nat) :
    ¬ ∀ φ : Nat → Nat, Ix.Kernel.Level.eval φ (.param n) = 0 := by
  intro hall
  have h2 : Ix.Kernel.Level.eval (fun _ => 1) (.param n) = 0 := hall _
  have h1 : Ix.Kernel.Level.eval (fun _ => 1) (.param n) = 1 := rfl
  exact Nat.one_ne_zero (h1.symm.trans h2)

theorem eval_max_eq (φ : Nat → Nat) (a b : KLevel) :
    Ix.Kernel.Level.eval φ (.max a b) =
      Max.max (Ix.Kernel.Level.eval φ a) (Ix.Kernel.Level.eval φ b) := rfl

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
      else Max.max (Ix.Kernel.Level.eval φ a) (Ix.Kernel.Level.eval φ b) := rfl
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
  have h3 : Ix.Kernel.Level.eval φ Ix.Kernel.Level.zero = 0 := rfl
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
    exact ⟨T, hT, rfl⟩
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
    exact hpi

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
    exact ⟨T, hT, rfl⟩
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
    exact hpi

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

/-- `KernelInfer::is_inductive_prop` decides whether the inductive's declared sort is zero, both
ways. -/
theorem is_inductive_prop_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::is_inductive_prop" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.is_inductive_prop c args h r h' calls := by
  intro rc ity ns hargs good hrc n hn I hI
  subst hargs hn
  have ext := Heap.Extends.snoc h (.construct kexprListEnum "Nil" [])
  have hnil : c.types (fun _ => .sort .zero) (h ++ [.construct kexprListEnum "Nil" []]) 0
      (.ptr (.enum kexprListEnum) h.length) :=
    ⟨.nil List.getElem?_concat_length, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  rcases Obs.«KernelInfer::is_inductive_prop».obs ev with
    ⟨v1, m2, cs12, m41, x_l, m78, cs89, m102, hm49, ev14, ld64, hm110, ev91, he118, he119,
      hc120⟩ |
    ⟨v1, m2, cs12, m41, x_l, v77, m78, cs89, m102, v136, m139, cs147, hm49, ev14, ld64, hm110,
      ev91, hne121, ev149, heq164, he165, he166, hc167⟩
  · -- `level_equal(u, Zero) = 1`: answer `1`
    subst hc120 hm49 hm110 he118
    obtain ⟨k, Γ', R, hk, -, hR, hpeel⟩ := ih.get (.infer .peel_n_alls_whnf) (by lt_calls) ev14
      _ _ _ _ rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) _ rfl 0
      (fun _ => .sort .zero) hnil I (Tm.mono ext (hI 0 (fun _ => .sort .zero)))
    obtain ⟨u, rfl, hu⟩ := hR.sort_of_load ld64
    have g89 : Good c cs89 := good.sub fun x hx => by simp [hx]
    exact ⟨k, Γ', u, hk, hpeel, .inl rfl,
      fun _ => ProjAux.zero_of_level_equal ih hu ev91 (by lt_calls) g89.2,
      fun h0 => absurd h0 field_one_ne_zero⟩
  · -- `level_may_be_nonzero(u) = 1`: answer `0`
    subst hc167 hm49 hm110 he165 heq164
    obtain ⟨k, Γ', R, hk, -, hR, hpeel⟩ := ih.get (.infer .peel_n_alls_whnf) (by lt_calls) ev14
      _ _ _ _ rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) _ rfl 0
      (fun _ => .sort .zero) hnil I (Tm.mono ext (hI 0 (fun _ => .sort .zero)))
    obtain ⟨u, rfl, hu⟩ := hR.sort_of_load ld64
    have e2 : Heap.Extends m2 m78 :=
      (Heap.Extends.snoc _ _).trans (ObsFn.heap_extends ev91)
    obtain ⟨-, hnz⟩ := ih.get (.infer .level_may_be_nonzero) (by lt_calls) ev149 _ u rfl
      (good.sub fun x hx => by simp [hx]) (LvRep.mono e2 hu)
    exact ⟨k, Γ', u, hk, hpeel, .inr rfl, fun h1 => absurd h1.symm field_one_ne_zero,
      fun _ => hnz rfl⟩

/-! ## The field telescope -/

/-- `KernelInfer::peel_field_loop`: the projected field's type, the fields passed instantiated by
their projections. -/
theorem peel_field_loop_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::peel_field_loop" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.peel_field_loop c args h r h' calls := by
  intro ty tg cu sa val hargs good t0 c0 htg hcu hle d Γ T a PE hT ha hPE
  subst hargs htg hcu
  rcases Obs.«KernelInfer::peel_field_loop».obs ev with
    ⟨x_dom, x_body, w20, ld12, op52, he60, he61, hc62⟩ |
    ⟨x_dom, x_body, w20, v36, m68, v106, m107, cs117, cs146, v151, ld12, op52, hne63, hm78, ev119,
      op181, ev148, hc197⟩
  · -- the target field: its domain
    subst he60 he61
    obtain ⟨D, B, ℓ, rfl, hD, hB, -⟩ := hT.forallE_of_load ld12
    have htc : t0 = c0 := ProjAux.counter_eq op52
    subst htc
    exact ⟨0, D, by omega, hD, rfl⟩
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
    obtain ⟨n, FT, hn, hFT, hfield⟩ := ih.get (.infer .peel_field_loop) (by lt_calls) ev148
      _ _ _ _ _ rfl (good.sub fun x hx => by simp [hx]) t0 (c0 + 1) rfl rfl (by omega) d Γ _ a
      PE hinst (Bytes.repAddressRef_heapMono₂ addrTy ext ha) (Tm.mono ext hPE)
    rw [hc1] at hfield
    refine ⟨n + 1, FT, by omega, hFT, ?_⟩
    exact hfield

/-! ## Projection guard and `k_infer_proj` -/

namespace ProjAux

theorem val_toUInt64_toNat (i : F) : ((ZMod.val i).toUInt64).toNat = ZMod.val i := by
  simp only [UInt64.toNat_ofNat', Nat.toUInt64_eq]
  have : ZMod.val i < 18446744069414584321 := ZMod.val_lt i
  rw [Nat.mod_eq_of_lt (by omega)]

theorem tml_lbb {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {As : List KExpr} {p : SourceValue F} (hAs : TmL κ d Γ h As p) :
    ∀ a ∈ As, a.looseBVarsBounded 0 = true := by
  induction hAs with
  | nil _ => intro a ha; cases ha
  | cons _ hx _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Tm.looseBVarsBounded hx
    · exact ih a ha

theorem types_extend {c : Ctx} {Γ : Nat → KExpr} {h : Heap F} {d : Nat}
    {types tp : SourceValue F} {T : KExpr}
    (htypes : c.types Γ h d types) (hT : c.tm d Γ h T tp) :
    c.types (Ghost.extend Γ d T) (h ++ [.construct kexprListEnum "Cons" [tp, types]]) (d + 1)
      (.ptr (.enum kexprListEnum) h.length) := by
  have ext := Heap.Extends.snoc h (.construct kexprListEnum "Cons" [tp, types])
  refine ⟨TypesRep.cons List.getElem?_concat_length ?_
    ((typesRep_congr_ghost htypes.1 (Ghost.extend_below Γ d T)).mono ext),
    GhostScoped.extend htypes.2 (Tm.wscopedB htypes.2 hT)⟩
  rw [Ghost.extend_at]
  exact (Tm.congr_ghost (Ghost.extend_below Γ d T) hT).mono ext

private theorem klevel_node_eq :
    Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» =
      IxVM.Refinement.KernelLevels.klevelListEnum := by decide +kernel

theorem lv_snoc {ls : List KLevel} {l : KLevel} {lp vp r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::snoc<&KernelTypes::KLevelNode>» [lp, vp] h r h' cs)
    (hl : RepKLevelList h ls lp) (hx : RepKLevel h l vp) :
    RepKLevelList h' (ls ++ [l]) r := by
  have ev' : ObsFn W (Instance.mk "Lists::snoc" [.ptr (.named "KernelTypes::KLevelNode" [])]).symbol
      [lp, vp] h r h' cs := by
    rw [Obs.Names.«Lists::snoc<&KernelTypes::KLevelNode>».symbol]; exact ev
  have hl' : RepList (Instance.mk "Lists::Node" [.ptr (.named "KernelTypes::KLevelNode" [])]).symbol
      RepKLevel h ls lp := by
    rw [Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol, klevel_node_eq]; exact hl
  have hres := Lib.Lists.snoc_spec IxVM.Refinement.KernelLevels.repKLevel_heapMono₂ ev' hl' hx
  rw [Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol, klevel_node_eq] at hres
  exact hres

theorem ind_params_eq (c : Ctx) (hc : CoreFacts c)
    {addr ptr nl ty ni nc u blk : SourceValue F} {h1 h2 : Heap F} {cs : List (Call F)}
    {s b : Bytes.Address} {nPS nP : Nat} {i : F}
    (ev : ObsFn W "Ingress::get_ci" [addr] h1 ptr h2 cs) (good : Good c cs)
    (hs : Bytes.RepAddressRef addrTy h1 s addr)
    (ld : loadValue h2 ptr = .ok (.construct kciEnum "Induct"
      [nl, ty, .field (nPS : F), ni, nc, u, blk, .field i]))
    (hb : Bytes.RepAddressRef addrTy h2 b blk)
    (hnPS : nPS < 72057594037927936) (hnP : nP < 72057594037927936)
    (hnP_ind : ∀ cb xs ind, Ix.Cert.recordAt c.E (ixAddr b) = some cb → cb.info = .muts xs →
      xs[ZMod.val i]? = some (.indc ind) → nP = ind.params.toNat) :
    nPS = nP := by
  obtain ⟨cm, b', i', hcm, hb', hi', hinfo⟩ :=
    hc.loads.inductRecord addr ptr h1 h2 cs s nl ty (.field (nPS : F)) ni nc u blk (.field i)
      ev good hs ld
  have hi_eq : i' = i := (NatAux.field_inj hi').symm
  subst i'
  have hb_eq : b' = b := IxVMRep.repAddressRef_det U32.Goldilocks.compatible hb' hb
  subst b'
  obtain ⟨cb, xs, ind, hcb, hmuts, hindc⟩ :=
    hc.loads.inductBlock addr ptr h1 h2 cs s b nl ty (.field (nPS : F)) ni nc u blk i ev good hs ld hb
  have hidx : ((ZMod.val i).toUInt64).toNat = ZMod.val i := val_toUInt64_toNat i
  obtain ⟨nl', ty', u', blk', b'', hld', -, -, -, -⟩ :=
    hc.loads.indRecord addr ptr h1 h2 cs s cm cb ⟨(ZMod.val i).toUInt64, ixAddr b⟩ xs ind
      ev good hs hcm hinfo hcb hmuts (by simpa [hidx] using hindc)
  rw [ld] at hld'
  injection hld' with hld'
  injection hld' with _ _ hxs
  simp only [List.cons.injEq] at hxs
  obtain ⟨-, -, hnp_eq, -⟩ := hxs
  have hnP_eq : nP = ind.params.toNat := hnP_ind cb xs ind hcb hmuts hindc
  rw [← hnP_eq] at hnp_eq
  exact (NatAux.natCast_inj (by omega) (by omega)).mp (NatAux.field_inj hnp_eq)

theorem peel_n_foralls_with_types_rep (c : Ctx) (N : Nat) :
    ∀ {x_e x_n x_types r x_after x_ctx : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      calls.length < N →
      ObsFn W "KernelCheck::peel_n_foralls_with_types" [x_e, x_n, x_types] h r h' calls →
      r = .tuple [x_after, x_ctx] →
      ∀ (n : F) (d : Nat) (Γ : Nat → KExpr) (E : KExpr),
        x_n = .field n → c.types Γ h d x_types → c.tm d Γ h E x_e →
        ∃ (d' : Nat) (Γ' : Nat → KExpr) (T' : KExpr),
          c.types Γ' h' d' x_ctx ∧ c.tm d' Γ' h' T' x_after := by
  induction N with
  | zero => intro _ _ _ _ _ _ _ _ _ hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ N ihN =>
    intro x_e x_n x_types r x_after x_ctx h h' calls hlt ev hr n d Γ E hn htypes hE
    subst hn
    rcases Obs.«KernelCheck::peel_n_foralls_with_types».obs ev with
      ⟨_, he19, he34, _⟩ |
      ⟨x_dom, x_body, w59, m76, cs109, v113, _, ld51, hm86, op135, ev111, hc144⟩ |
      ⟨v40, _, _, _, he153, he168, _⟩
    · rw [hr] at he19
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he19
      obtain ⟨rfl, rfl⟩ := he19
      subst he34
      exact ⟨d, Γ, E, htypes, hE⟩
    · subst hc144 hm86
      obtain ⟨D, B, ℓ, rfl, hD, hB, -⟩ := hE.forallE_of_load ld51
      have hv113 : v113 = .field (n - 1) := NatAux.sub_ok op135
      have ext := Heap.Extends.snoc h (.construct kexprListEnum "Cons" [x_dom, x_types])
      have htypes' := types_extend htypes hD
      have hbody := Tm.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D) (Tm.mono ext hB)
      exact ihN (by simp only [List.length_cons] at hlt; omega) ev111 hr (n - 1) (d + 1) _ _
        hv113 htypes' hbody
    · rw [hr] at he153
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he153
      obtain ⟨rfl, rfl⟩ := he153
      subst he168
      exact ⟨d, Γ, E, htypes, hE⟩

theorem proj_guard_fold_rep {ls : List KLevel} :
    ∀ {h h' : Heap F} {x_acc x_deps r : SourceValue F} {calls : List (Call F)} {acc : KLevel},
      ObsFn W "KernelInfer::proj_guard_fold" [x_acc, x_deps] h r h' calls →
      RepKLevel h acc x_acc → RepKLevelList h ls x_deps →
      ∃ g : KLevel, RepKLevel h' g r := by
  induction ls with
  | nil =>
    intro h h' x_acc x_deps r calls acc ev hacc hls
    rcases Obs.«KernelInfer::proj_guard_fold».obs ev with
      ⟨_, he21, he22, _⟩ |
      ⟨x_d, x_rest, cs44, m50, ld12, _, _, _⟩
    · subst he21 he22
      exact ⟨acc, hacc⟩
    · rw [klevel_node_eq] at ld12
      cases hls with
      | nil cell => exact (load_cell_ne cell ld12 (by decide)).elim
  | cons d0 ls' ih =>
    intro h h' x_acc x_deps r calls acc ev hacc hls
    rcases Obs.«KernelInfer::proj_guard_fold».obs ev with
      ⟨ld12, _, _, _⟩ |
      ⟨x_d, x_rest, cs44, m50, ld12, hm58, ev46, _⟩
    · rw [klevel_node_eq] at ld12
      cases hls with
      | cons cell _ _ => exact (load_cell_ne cell ld12 (by decide)).elim
    · rw [klevel_node_eq] at ld12
      obtain ⟨d1, ls1, heq, hd, hrest⟩ := RepList.cons_of_load hls ld12
      injection heq with hd_eq hls_eq
      subst hd_eq hls_eq hm58
      have ext := Heap.Extends.snoc h (.construct "KernelTypes::KLevelNode" "Max" [x_acc, x_d])
      have hmax : RepKLevel (h ++ [.construct "KernelTypes::KLevelNode" "Max" [x_acc, x_d]])
          (.max acc d0) (.ptr (.enum "KernelTypes::KLevelNode") h.length) :=
        .max List.getElem?_concat_length (hacc.mono ext) (hd.mono ext)
      exact ih ev46 hmax (RepKLevelList.mono hrest ext)

theorem proj_guard_walk_rep (c : Ctx) {calls0 : List (Call F)} (ih : IH c calls0) (N : Nat) :
    ∀ {x_rc x_ty x_ctx x_k x_deps r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      calls.length < N → calls.length < calls0.length → Good c calls →
      ObsFn W "KernelInfer::proj_guard_walk" [x_rc, x_ty, x_ctx, x_k, x_deps] h r h' calls →
      ∀ (k : F) (d : Nat) (Γ : Nat → KExpr) (T : KExpr) (ls : List KLevel),
        x_k = .field k → c.rc h x_rc → c.types Γ h d x_ctx → c.tm d Γ h T x_ty →
        RepKLevelList h ls x_deps →
        ∃ g : KLevel, RepKLevel h' g r := by
  induction N with
  | zero => intro _ _ _ _ _ _ _ _ _ hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ N ihN =>
    intro x_rc x_ty x_ctx x_k x_deps r h h' calls hlt hlt0 good ev k d Γ T ls hk hrc htypes hT hls
    subst hk
    rcases Obs.«KernelInfer::proj_guard_walk».obs ev with
      ⟨x_dom, x_body, w16, v32, m33, cs43, cs87, ld11, ev45, _, ev89, hc106⟩ |
      ⟨x_dom, x_body, w16, v32, m33, cs43, v176, m177, cs179, cs188, v194, m211,
        ld11, ev45, _, sg184, hm219, op252, ev190, hc261⟩
    · subst hc106
      obtain ⟨D, B, ℓ, rfl, hD, -, -⟩ := hT.forallE_of_load ld11
      have g43 : Good c cs43 := good.sub fun x hx => by simp [hx]
      obtain ⟨_, u, -, -, lu, hlu, -⟩ := ih.get (.infer .k_ensure_sort)
        (by simp only [List.length_cons, List.length_append] at hlt0; omega)
        ev45 x_rc x_dom x_ctx rfl g43 hrc d Γ htypes D hD
      have e45 := ObsFn.heap_extends ev45
      exact proj_guard_fold_rep ev89 hlu (RepKLevelList.mono hls e45)
    · subst hc261
      obtain ⟨D, B, ℓ, rfl, hD, hB, -⟩ := hT.forallE_of_load ld11
      have g43 : Good c cs43 := good.sub fun x hx => by simp [hx]
      obtain ⟨_, u, -, -, lu, hlu, -⟩ := ih.get (.infer .k_ensure_sort)
        (by simp only [List.length_cons, List.length_append] at hlt0; omega)
        ev45 x_rc x_dom x_ctx rfl g43 hrc d Γ htypes D hD
      have e45 := ObsFn.heap_extends ev45
      obtain ⟨ls', hls177, e33_177⟩ :
          ∃ ls', RepKLevelList m177 ls' v176 ∧ Heap.Extends m33 m177 := by
        rcases sg184 with
          ⟨m112, cs123, cs148, ev125, ev150, _⟩ |
          ⟨v111, m112, cs123, ev125, _, he173, he174, _⟩
        · have e125 := ObsFn.heap_extends ev125
          have e150 := ObsFn.heap_extends ev150
          exact ⟨ls ++ [lu],
            lv_snoc ev150 (RepKLevelList.mono (RepKLevelList.mono hls e45) e125) (hlu.mono e125),
            e125.trans e150⟩
        · subst he173 he174
          have e125 := ObsFn.heap_extends ev125
          exact ⟨ls, RepKLevelList.mono (RepKLevelList.mono hls e45) e125, e125⟩
      subst hm219
      have hv194 : v194 = .field (k - 1) := NatAux.sub_ok op252
      have e211 := Heap.Extends.snoc m177 (.construct kexprListEnum "Cons" [x_dom, x_ctx])
      have E177 : Heap.Extends h m177 := e45.trans e33_177
      have E211 : Heap.Extends h _ := E177.trans e211
      have htypes211 := types_extend (types_mono E177 htypes) (Tm.mono E177 hD)
      have hbody211 := Tm.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D)
        (Tm.mono E211 hB)
      have g188 : Good c cs188 := good.sub fun x hx => by simp [hx]
      exact ihN
        (by simp only [List.length_cons, List.length_append] at hlt; omega)
        (by simp only [List.length_cons, List.length_append] at hlt0; omega)
        g188 ev190 (k - 1) (d + 1) _ _ ls' hv194
        (RCRep.mono E211 hrc) htypes211 hbody211 (RepKLevelList.mono hls177 e211)

theorem proj_guard_rep (c : Ctx) {calls0 : List (Call F)} (ih : IH c calls0)
    {x_rc x_block x_idx x_fidx r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hlt0 : calls.length < calls0.length) (good : Good c calls)
    (ev : ObsFn W "KernelInfer::proj_guard" [x_rc, x_block, x_idx, x_fidx] h r h' calls)
    {b : Bytes.Address} {i f : F} (hrc : c.rc h x_rc)
    (hb : Bytes.RepAddressRef addrTy h b x_block) (hi : x_idx = .field i)
    (hf : x_fidx = .field f) :
    ∃ g : KLevel, RepKLevel h' g r := by
  subst hi hf
  rcases Obs.«KernelInfer::proj_guard».obs ev with
    ⟨m2, p9, cs15, w44, x_cty, w45, w46, w47, x_np, w48, w49, m91, cs101, m122,
      x_after, x_ctx, cs150, m187, ev17, ld11, hm130, ev103, hm195, ev152, hc199⟩
  subst hc199 hm130 hm195
  have g15 : Good c cs15 := good.sub fun x hx => by simp [hx]
  obtain ⟨ci, -, v, hld, hci⟩ := ih.get (.callees .get_ci_cprj)
    (by simp only [List.length_cons, List.length_append] at hlt0; omega)
    ev17 x_block i 0 b rfl g15 hb
  rw [ld11] at hld
  injection hld with hv
  subst hv
  obtain ⟨cv, nP, nF, rfl, ⟨-, -, -, hcty⟩, hnp_eq, -, -, -, -⟩ := WhnfAux.ctor_inv hci
  have e17 := ObsFn.heap_extends ev17
  have e122 := Heap.Extends.snoc m2 (.construct kexprListEnum "Nil" [])
  have hnil_ctx : c.types (fun _ => .sort .zero)
      (m2 ++ [.construct kexprListEnum "Nil" []]) 0 (.ptr (.enum kexprListEnum) m2.length) :=
    ⟨.nil List.getElem?_concat_length, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  obtain ⟨d', Γ', T_after, htypes91, hT91⟩ :=
    peel_n_foralls_with_types_rep c (cs101.length + 1) (Nat.lt_succ_self _) ev103 rfl
      (nP : F) 0 (fun _ => .sort .zero) (posOf cv.levelParams cv.type) hnp_eq hnil_ctx
      (Tm.mono e122 (hcty 0 (fun _ => .sort .zero)))
  have e103 := ObsFn.heap_extends ev103
  have e187 := Heap.Extends.snoc m91
    (.construct Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» "Nil" [])
  have hnil_deps : RepKLevelList
      (m91 ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» "Nil" []]) []
      (.ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>») m91.length) := by
    rw [klevel_node_eq]
    exact .nil List.getElem?_concat_length
  have E187 : Heap.Extends h _ := e17.trans (e122.trans (e103.trans e187))
  have g150 : Good c cs150 := good.sub fun x hx => by simp [hx]
  exact proj_guard_walk_rep c ih (cs150.length + 1) (Nat.lt_succ_self _)
    (by simp only [List.length_cons, List.length_append] at hlt0; omega)
    g150 ev152 f d' Γ' T_after [] rfl (RCRep.mono E187 hrc)
    (types_mono e187 htypes91) (Tm.mono e187 hT91) hnil_deps

theorem prop_guard_ok_zero {c : Ctx} {calls0 : List (Call F)} (ih : IH c calls0)
    {x_guard x_lvls x_is_prop r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hlt0 : calls.length < calls0.length) (good : Good c calls)
    (ev : ObsFn W "KernelInfer::prop_guard_ok" [x_guard, x_lvls, x_is_prop] h r h' calls)
    {g : KLevel} {ls : List KLevel}
    (hg : RepKLevel h g x_guard) (hls : RepKLevelList h ls x_lvls)
    (hprop : x_is_prop ≠ .field 0) :
    ∀ φ, Ix.Kernel.Level.eval φ (IxVM.Refinement.KernelLevels.substLevel g ls) = 0 := by
  rcases Obs.«KernelInfer::prop_guard_ok».obs ev with
    ⟨hv14, _, _, _⟩ |
    ⟨v35, m38, cs46, v49, m52, cs60, m80, _, ev62, hm88, ev48, heq98, _, _, hc103⟩
  · exact absurd hv14 hprop
  · subst hc103 hm88 heq98
    have g60 : Good c cs60 := good.sub fun x hx => by simp [hx]
    have g46 : Good c cs46 := good.sub fun x hx => by simp [hx]
    obtain ⟨-, hinst, -⟩ := ih.get (.levelOps .level_inst_params)
      (by simp only [List.length_cons, List.length_append] at hlt0; omega)
      ev62 x_guard x_lvls rfl g60.2 g ls hg hls
    exact zero_of_level_equal ih ⟨_, hinst, LvEq.refl _⟩ ev48
      (by simp only [List.length_cons, List.length_append] at hlt0; omega) g46.2

end ProjAux

/-- **Shared projection inference step** at grade `g` (`.full` for `k_infer_proj`, `.io` for
`k_infer_only_core`'s `.Proj` arm). -/
theorem infer_proj_common (c : Ctx) (hc : CoreFacts c)
    {g : Ix.Kernel.Rules.Grade} {calls : List (Call F)} (ih : IH c calls) (good : Good c calls)
    {x_rc x_struct_addr x_fidx x_e1 x_types r : SourceValue F} {h h' : Heap F}
    {d : Nat} {Γ : Nat → KExpr} {s : Bytes.Address} {fi : F} {PE : KExpr}
    (hrc : c.rc h x_rc) (hfi : x_fidx = .field fi) (htypes : c.types Γ h d x_types)
    (hs : Bytes.RepAddressRef addrTy h s x_struct_addr) (hPE : c.tm d Γ h PE x_e1)
    {c0 c_peel : Call F}
    {v1 : SourceValue F} {m2 : Heap F} {cs12 : List (Call F)}
    {v39 : SourceValue F} {m40 : Heap F} {cs50 : List (Call F)}
    {m78 : Heap F} {cs89 : List (Call F)}
    {x_head x_args x_head_addr x_lvls : SourceValue F}
    {v156 : SourceValue F} {m159 : Heap F} {cs167 : List (Call F)}
    {m194 : Heap F} {p201 : SourceValue F} {cs207 : List (Call F)}
    {x_ind_nlvls x_ind_ty x_n_params x_n_indices x_num_ctors w234 x_block_addr x_ind_idx :
      SourceValue F}
    {v302 : SourceValue F} {m303 : Heap F} {cs313 : List (Call F)}
    {m357 : Heap F} {p364 : SourceValue F} {cs370 : List (Call F)}
    {x_ctor_nlvls x_ctor_ty w405 w406 w407 w408 w409 w410 : SourceValue F}
    {v479 : SourceValue F} {m480 : Heap F} {cs490 : List (Call F)}
    {v509 : SourceValue F} {m510 : Heap F} {cs520 : List (Call F)}
    {v547 : SourceValue F} {m548 : Heap F} {cs558 : List (Call F)}
    {v600 : SourceValue F} {m601 : Heap F} {cs611 : List (Call F)}
    {v614 v616 : SourceValue F} {m618 : Heap F} {cs626 : List (Call F)}
    {m669 : Heap F} {cs677 : List (Call F)} {v_nskip : SourceValue F}
    (hc_calls : calls = c0 :: (cs12 ++
      (⟨"KernelWhnf::whnf", [x_rc, v1, x_types], m2⟩ :: (cs50 ++
      (⟨"KernelTypes::collect_spine", [v39], m40⟩ :: (cs89 ++
      (⟨"Bytes::address_eq", [x_head_addr, x_struct_addr], m78⟩ :: (cs167 ++
      (⟨"Ingress::get_ci", [x_head_addr], m159⟩ :: (cs207 ++
      (⟨"KernelInfer::proj_shape_ok", [x_n_indices, x_args, x_n_params, x_lvls, x_ind_nlvls], m194⟩ :: (cs313 ++
      (⟨"KernelModeled::proj_ctor", [x_block_addr, x_ind_idx], m303⟩ :: (cs370 ++
      (⟨"KernelLevels::expr_inst_levels", [x_ctor_ty, x_lvls], m357⟩ :: (cs490 ++
      (c_peel :: (cs520 ++
      (⟨"KernelInfer::peel_field_loop", [v509, x_fidx, .field 0, x_struct_addr, x_e1], m510⟩ :: (cs558 ++
      (⟨"KernelInfer::proj_guard", [x_rc, x_block_addr, x_ind_idx, x_fidx], m548⟩ :: (cs626 ++
      (⟨"KernelInfer::is_inductive_prop", [x_rc, x_ind_ty, v_nskip], m618⟩ :: (cs677 ++
      (⟨"KernelInfer::prop_guard_ok", [v614, x_lvls, v616], m669⟩ :: cs611)))))))))))))))))))))))))
    (hinf1 : ∃ TPE, c.tm d Γ m2 TPE v1 ∧ Infer c.env g d PE TPE ∧ Heap.Extends h m2)
    (ev52 : ObsFn W "KernelWhnf::whnf" [x_rc, v1, x_types] m2 v39 m40 cs50)
    (ev91 : ObsFn W "KernelTypes::collect_spine" [v39] m40 (.tuple [x_head, x_args]) m78 cs89)
    (ld127 : loadValue m78 x_head =
      .ok (.construct "KernelTypes::KExprNode" "Const" [x_head_addr, x_lvls]))
    (ev169 : ObsFn W "Bytes::address_eq" [x_head_addr, x_struct_addr] m78 v156 m159 cs167)
    (heq192 : v156 = .field 1)
    (ev209 : ObsFn W "Ingress::get_ci" [x_head_addr] m159 p201 m194 cs207)
    (ld203 : loadValue m194 p201 = .ok (.construct "KernelTypes::KConstantInfo" "Induct"
      [x_ind_nlvls, x_ind_ty, x_n_params, x_n_indices, x_num_ctors, w234, x_block_addr, x_ind_idx]))
    (ev315 : ObsFn W "KernelInfer::proj_shape_ok"
      [x_n_indices, x_args, x_n_params, x_lvls, x_ind_nlvls] m194 v302 m303 cs313)
    (ev372 : ObsFn W "KernelModeled::proj_ctor" [x_block_addr, x_ind_idx] m303 p364 m357 cs370)
    (ld366 : loadValue m357 p364 = .ok (.construct "KernelTypes::KConstantInfo" "Ctor"
      [x_ctor_nlvls, x_ctor_ty, w405, w406, w407, w408, w409, w410]))
    (heq478 : x_ctor_nlvls = x_ind_nlvls)
    (ev492 : ObsFn W "KernelLevels::expr_inst_levels" [x_ctor_ty, x_lvls] m357 v479 m480 cs490)
    (hpeel : ∀ (n : F) (T : KExpr) (As : List KExpr),
      x_n_params = .field n → c.tm d Γ m480 T v479 → c.tml d Γ m480 As x_args →
      ∃ T_after, c.tm d Γ m510 T_after v509 ∧
        Specs.Infer.instPis (ZMod.val n) T As = some T_after ∧ Heap.Extends m480 m510)
    (ev560 : ObsFn W "KernelInfer::peel_field_loop"
      [v509, x_fidx, .field 0, x_struct_addr, x_e1] m510 v547 m548 cs558)
    (ev628 : ObsFn W "KernelInfer::proj_guard"
      [x_rc, x_block_addr, x_ind_idx, x_fidx] m548 v614 m618 cs626)
    (hnskip : ∀ n : F, x_n_params = .field n → x_n_indices = .field 0 → v_nskip = .field n)
    (ev679 : ObsFn W "KernelInfer::is_inductive_prop" [x_rc, x_ind_ty, v_nskip] m618 v616 m669 cs677)
    (ev613 : ObsFn W "KernelInfer::prop_guard_ok" [v614, x_lvls, v616] m669 v600 m601 cs611)
    (hr : r = v547) (hh' : h' = m601) :
    ∃ T, c.tm d Γ h' T r ∧ Infer c.env g d (.proj (c.κ (ixAddr s)) (ZMod.val fi) PE) T := by
  subst hc_calls hfi heq192
  subst v547 m601
  have h39 : (2 : Nat) ^ 39 = 549755813888 := by norm_num
  -- 1. Infer and head-normalize the scrutinee's type
  obtain ⟨TPE, hTPE, hInferPE, e14⟩ := hinf1
  obtain ⟨TW, hTW, hRedTW⟩ := ih.get (.whnf .whnf) (by lt_calls) ev52 x_rc v1 x_types rfl
    (good.sub fun x hx => by simp [hx]) (RCRep.mono e14 hrc) d Γ (types_mono e14 htypes) TPE hTPE
  have e52 := ObsFn.heap_extends ev52
  obtain ⟨hd', sp', H, Args, htup, hH, hArgs, hTWeq⟩ := ih.get (.subst .collect_spine)
    (by lt_calls) ev91 v39 rfl (good.sub fun x hx => by simp [hx]) d Γ 0 TW hTW
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
  obtain ⟨rfl, rfl⟩ := htup
  have e91 := ObsFn.heap_extends ev91
  have E78 : Heap.Extends h m78 := e14.trans (e52.trans e91)
  obtain ⟨ha_addr, us, rfl, hha, ls, hls, hEq⟩ := hH.const_of_load ld127
  -- 2. Match head constant address against projected structure address
  obtain ⟨hae, -⟩ := Lib.address_eq_spec ev169 hha (Bytes.repAddressRef_heapMono₂ addrTy E78 hs)
  have hha_s : ha_addr = s := by
    by_contra hne
    rw [ite_eq_right hne] at hae
    exact field_one_ne_zero hae
  subst ha_addr
  have e169 := ObsFn.heap_extends ev169
  -- 3. Load the structure inductive
  have g207 : Good c cs207 := good.sub fun x hx => by simp [hx]
  have hs159 : Bytes.RepAddressRef addrTy m159 s x_head_addr :=
    Bytes.repAddressRef_heapMono₂ addrTy e169 hha
  obtain ⟨ciS, hfindS, vS, hldS, hciS⟩ := ih.get (.callees .get_ci) (by lt_calls) ev209
    x_head_addr s rfl g207 hs159
  rw [ld203] at hldS
  injection hldS with hvS
  subst hvS
  obtain ⟨cvS, caps, nPS, nIS, nCS, rfl, ⟨hsnl, hslt, hsperm, hsty⟩, hp_eq, hi_eq, hc_eq,
    hnPS, hnIS, hnCS, bS, iS, hbS, hidx_eq, hnameS⟩ := WhnfAux.ind_inv hciS
  have e209 := ObsFn.heap_extends ev209
  have e78_194 : Heap.Extends m78 m194 := e169.trans e209
  have E194 : Heap.Extends h m194 := E78.trans e78_194
  -- 4. Shape check: no indices, parameter and level counts
  have hArgs194 : c.tml d Γ m194 Args x_args := tml_mono e78_194 hArgs
  have hls194 : RepKLevelList m194 ls x_lvls := RepKLevelList.mono hls e78_194
  have hlenA_lt : Args.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
    (c := ⟨"KernelInfer::proj_shape_ok",
      [x_n_indices, x_args, x_n_params, x_lvls, x_ind_nlvls], m194⟩)
    (by simp) (by simp) hArgs194
  have hlenL_lt : ls.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
    (c := ⟨"KernelInfer::proj_shape_ok",
      [x_n_indices, x_args, x_n_params, x_lvls, x_ind_nlvls], m194⟩)
    (by simp) (by simp) hls194
  obtain ⟨hni0, hnpA, hnlU, hm303⟩ := ih.get (.infer .proj_shape_ok) (by lt_calls) ev315
    _ _ _ _ _ rfl (good.sub fun x hx => by simp [hx]) d Γ Args us hArgs194 ⟨ls, hls194, hEq⟩
  subst m303
  have hus_ls : us.length = ls.length := Ix.Kernel.Level.EvalEqList.length_eq (hEq fun _ => 0)
  have hArgs_nPS : Args.length = nPS :=
    ((NatAux.natCast_inj (by omega) (by omega)).mp (NatAux.field_inj (hp_eq.symm.trans hnpA))).symm
  have hus_nlS : us.length = cvS.levelParams.length :=
    ((NatAux.natCast_inj (by omega) (by omega)).mp (NatAux.field_inj (hsnl.symm.trans hnlU))).symm
  -- 5. Load the structure's constructor via `proj_ctor` and projection table
  have g370 : Good c cs370 := good.sub fun x hx => by simp [hx]
  have ev372' : ObsFn W "KernelModeled::proj_ctor" [x_block_addr, .field iS] m194 p364 m357 cs370 :=
    hidx_eq ▸ ev372
  obtain ⟨-, ciC, hfindC, vC, hldC, hciC⟩ := ih.get (.callees .proj_ctor) (by lt_calls) ev372'
    x_block_addr iS bS rfl g370 hbS
  rw [ld366] at hldC
  injection hldC with hvC
  subst hvC
  obtain ⟨cvC, nP, nF, rfl, ⟨hcnl, hclt, hcperm, hcty⟩, -, -, hnP, hnF, -⟩ :=
    WhnfAux.ctor_inv hciC
  have hlpCS : cvC.levelParams.length = cvS.levelParams.length :=
    (NatAux.natCast_inj (by omega) (by omega)).mp
      (NatAux.field_inj (hcnl.symm.trans (heq478.trans hsnl)))
  have husC : us.length = cvC.levelParams.length := hus_nlS.trans hlpCS.symm
  have e372 := ObsFn.heap_extends ev372
  have E357 : Heap.Extends h m357 := E194.trans e372
  obtain ⟨tbl, htbl, hsn, hctor, hnPt, hnFt, hlpt, hnP_ind, hent, hbodies, -,
    bsC, bodyC, hstripC, -⟩ :=
    hc.loads.projTables x_block_addr x_ind_idx p364 m194 m357 cs370 bS iS
      ev372 g370 hbS hidx_eq 0 cvC nP nF hfindC
  obtain ⟨hteleC, hguard_eq⟩ :=
    hc.loads.projTablesGuard x_block_addr x_ind_idx p364 m194 m357 cs370 bS iS
      ev372 g370 hbS hidx_eq 0 cvC nP nF tbl hfindC htbl
  have ld203' : loadValue m194 p201 = .ok (.construct kciEnum "Induct"
      [x_ind_nlvls, x_ind_ty, .field (nPS : F), x_n_indices, x_num_ctors, w234,
        x_block_addr, .field iS]) := by
    rw [← hp_eq, ← hidx_eq]
    exact ld203
  have hnPS_eq : nPS = nP :=
    ProjAux.ind_params_eq c hc ev209 g207 hs159 ld203' hbS hnPS hnP hnP_ind
  rw [hnPS_eq] at hp_eq hArgs_nPS
  -- 6. Level instantiation, parameter substitution, and field peeling
  have hls357 : RepKLevelList m357 ls x_lvls := RepKLevelList.mono hls194 e372
  have hinst0 := ih.get (.subst .expr_inst_levels) (by lt_calls) ev492 x_ctor_ty x_lvls rfl
    (good.sub fun x hx => by simp [hx]) Γ 0 (posOf cvC.levelParams cvC.type) us
    (hcty 0 Γ) ⟨ls, hls357, hEq⟩
  rw [WhnfAux.posOf_ilp_perm hcperm husC] at hinst0
  have hinstd : c.tm d Γ m480 (cvC.type.instantiateLevelParams cvC.levelParams us) v479 :=
    Tm.of_depth_zero hinst0 d
  have e492 := ObsFn.heap_extends ev492
  have E480 : Heap.Extends h m480 := E357.trans e492
  have hArgs480 : c.tml d Γ m480 Args x_args := tml_mono (e372.trans e492) hArgs194
  obtain ⟨T_after, hT_after, hpis, e522⟩ := hpeel (nP : F) _ Args hp_eq hinstd hArgs480
  rw [NatAux.val_natCast (n := nP) (by omega)] at hpis
  have E510 : Heap.Extends h m510 := E480.trans e522
  obtain ⟨nf_step, FT, hnf_step, hFT, hfield⟩ := ih.get (.infer .peel_field_loop) (by lt_calls)
    ev560 v509 (.field fi) (.field 0) x_struct_addr x_e1 rfl
    (good.sub fun x hx => by simp [hx]) fi 0 rfl rfl (by rw [ZMod.val_zero]; exact Nat.zero_le _)
    d Γ T_after s PE hT_after (Bytes.repAddressRef_heapMono₂ addrTy E510 hs) (Tm.mono E510 hPE)
  rw [ZMod.val_zero, Nat.zero_add] at hnf_step
  subst nf_step
  rw [ZMod.val_zero] at hfield
  have e560 := ObsFn.heap_extends ev560
  have E548 : Heap.Extends h m548 := E510.trans e560
  -- 7. Field index in range and projected type agreement
  have hltF : ZMod.val fi < nF := ProjBody.lt_of_ctorTeleOk_instPis_fieldTypeAt
    (ProjBody.ctorTeleOk_instantiateLevelParams cvC.levelParams us hteleC) hArgs_nPS hpis hfield
  have hkS : c.κ (ixAddr s) = c.κ (iprjAddr (ixAddr bS) (ZMod.val iS)) :=
    (WhnfAux.name_of_find hfindS).symm.trans hnameS
  have hsn_s : tbl.structName = c.κ (ixAddr s) := hsn.trans hkS.symm
  have hclC : cvC.type.looseBVarsBounded 0 = true :=
    (hc.env.store.wf _ (List.mem_of_find?_eq_some hfindC)).2.2.2.1
  have hstripC_some : (cvC.type.stripPis (nP + nF)).isSome = true := by rw [hstripC]; rfl
  have hFT_eq : FT = (tbl.entry (ZMod.val fi)).typeAt us Args PE :=
    ProjBody.fieldTypeAt_eq_typeAt hbodies hnPt hstripC_some hclC hltF hArgs_nPS
      (ProjAux.tml_lbb hArgs) hPE.looseBVarsBounded (by rwa [hlpt]) (by rwa [hsn_s])
  -- 8. Projection guard and Prop guard (`FireSem`)
  have e194_548 : Heap.Extends m194 m548 := e372.trans (e492.trans (e522.trans e560))
  have g626 : Good c cs626 := good.sub fun x hx => by simp [hx]
  have hrc548 : c.rc m548 x_rc := RCRep.mono E548 hrc
  have hbS548 : Bytes.RepAddressRef addrTy m548 bS x_block_addr :=
    Bytes.repAddressRef_heapMono₂ addrTy e194_548 hbS
  obtain ⟨g_lvl, hg_lvl⟩ := ProjAux.proj_guard_rep c ih (by lt_calls) g626 ev628
    hrc548 hbS548 hidx_eq rfl
  have e628 := ObsFn.heap_extends ev628
  have E618 : Heap.Extends h m618 := E548.trans e628
  have ev628' : ObsFn W "KernelInfer::proj_guard"
      [x_rc, x_block_addr, .field iS, .field fi] m548 v614 m618 cs626 := hidx_eq ▸ ev628
  have e194_618 : Heap.Extends m194 m618 := e194_548.trans e628
  have hsty618 : c.tmc m618 (posOf cvS.levelParams cvS.type) x_ind_ty :=
    fun d' Γ' => Tm.mono e194_618 (hsty d' Γ')
  obtain ⟨k_p, Γ_p, u_ind, hk_p, hpeel_p, -, -, hnz_p⟩ :=
    ih.get (.infer .is_inductive_prop) (by lt_calls) ev679 x_rc x_ind_ty v_nskip rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono E618 hrc) (nP : F)
      (hnskip (nP : F) hp_eq hni0) (posOf cvS.levelParams cvS.type) hsty618
  rw [NatAux.val_natCast (n := nP) (by omega)] at hk_p
  have e679 := ObsFn.heap_extends ev679
  have e613 := ObsFn.heap_extends ev613
  obtain ⟨hfp, -, -, -, ⟨cvT, capsT, hT, hlT, bsT, hsT⟩, -⟩ := hent (ZMod.val fi) hltF
  have hT' := hT
  rw [show (tbl.entry (ZMod.val fi)).structName = c.κ (ixAddr s) from hsn_s, hfindS] at hT'
  injection hT' with hT'
  injection hT' with hcvT _
  subst cvT
  have hTWargs : TW.getAppArgs = Args := by rw [hTWeq, getAppArgs_mkAppN]; rfl
  refine ⟨FT, Tm.mono (e628.trans (e679.trans e613)) hFT, ?_⟩
  rw [hFT_eq, ← hTWargs]
  refine Infer.proj (entry := tbl.entry (ZMod.val fi)) (us := us) hInferPE hRedTW ?_ ?_ ?_ ?_ ?_
  · rw [hTWeq, getAppFn_mkAppN]; rfl
  · rw [← hsn_s]; exact hfp
  · show TW.getAppArgs.length = tbl.numParams
    rw [hTWargs, hnPt, hArgs_nPS]
  · show us.length = tbl.levelParams.length
    rw [hlpt, husC]
  · intro heqv φ
    have hz0 : ∀ ψ, Ix.Kernel.Level.eval ψ tbl.structSort = 0 :=
      fun ψ => (Ix.Kernel.Level.isEquiv_sound heqv ψ).trans rfl
    have hsT' : cvS.type.stripPis nP = some (bsT, .sort tbl.structSort) := by
      simpa [Ix.Kernel.ProjTable.entry, hnPt] using hsT
    obtain ⟨⟨bsT', resT'⟩, hsT_pos⟩ := Option.isSome_iff_exists.mp
      (Ix.Kernel.Expr.stripPis_instantiateLevelParams_isSome cvS.levelParams
        (posLevels cvS.levelParams) nP (by rw [hsT']; rfl))
    obtain ⟨hres_eq, -⟩ := Ix.Kernel.Expr.stripPis_instantiateLevelParams_eq cvS.levelParams
      (posLevels cvS.levelParams) nP hsT' hsT_pos
    rw [hres_eq] at hsT_pos
    have hu_eq : u_ind = Ix.Kernel.Level.subst cvS.levelParams (posLevels cvS.levelParams)
        tbl.structSort :=
      ProjBody.peelRed_stripPis_sort nP hsT_pos hpeel_p hk_p
    have hv_nz : v616 ≠ .field 0 := by
      intro hv0
      refine hnz_p hv0 (fun ψ => ?_)
      rw [hu_eq, Ix.Kernel.Level.eval_subst]
      exact hz0 _
    have g611 : Good c cs611 := good.sub fun x hx => by simp [hx]
    have hg669 : RepKLevel m669 g_lvl v614 := hg_lvl.mono e679
    have hls669 : RepKLevelList m669 ls x_lvls :=
      RepKLevelList.mono hls357 (e492.trans (e522.trans (e560.trans (e628.trans e679))))
    have hg0 := ProjAux.prop_guard_ok_zero ih (by lt_calls) g611 ev613 hg669 hls669 hv_nz
    have husT : us.length = tbl.levelParams.length := by
      rw [hlpt]; exact husC
    have hg0_us : ∀ ψ, Ix.Kernel.Level.eval ψ
        (Ix.Kernel.Level.subst (List.range us.length) us g_lvl) = 0 :=
      fun ψ => (WhnfAux.lvEq_subst_range (fun _ => rfl) hEq ψ).trans (hg0 ψ)
    exact hguard_eq heqv fi x_rc x_block_addr v614 m548 m618 cs626 g_lvl us hltF husT
      ev628' g626 hrc548 hbS548 hg_lvl hg0_us φ

/-- `KernelInfer::k_infer_proj`: full-grade projection inference (`Infer.proj`). -/
theorem k_infer_proj_step (c : Ctx) (hc : CoreFacts c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::k_infer_proj" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.k_infer_proj c args h r h' calls := by
  intro rc sa fi e1 types hargs good hrc i hfi d Γ htypes a PE ha hPE
  subst hargs
  rcases Obs.«KernelInfer::k_infer_proj».obs ev with
    ⟨v1, m2, cs12, v39, m40, cs50, m78, cs89, x_head, x_args, x_head_addr, x_lvls,
      v156, m159, cs167, m194, p201, cs207, x_ind_nlvls, x_ind_ty, x_n_params, x_n_indices,
      x_num_ctors, w234, x_block_addr, x_ind_idx, v302, m303, cs313, m357, p364, cs370,
      x_ctor_nlvls, x_ctor_ty, w405, w406, w407, w408, w409, w410, v479, m480, cs490,
      v509, m510, cs520, v547, m548, cs558, v600, m601, cs611, v614, v616, m618, cs626,
      m669, cs677, v682,
      ev14, ev52, ev91, ld127, ev169, heq192, ev209, ld203, _, ev315, ev372, ld366, heq478,
      ev492, ev522, ev560, ev628, op710, ev679, ev613, he714, he715, hc716⟩
  have hlt12 : cs12.length < calls.length := by rw [hc716]; lt_calls
  have g12 : Good c cs12 := good.sub fun x hx => by rw [hc716]; simp [hx]
  have hlt520 : cs520.length < calls.length := by rw [hc716]; lt_calls
  have g520 : Good c cs520 := good.sub fun x hx => by rw [hc716]; simp [hx]
  refine infer_proj_common c hc ih good hrc hfi htypes ha hPE hc716 ?_ ev52 ev91 ld127
    ev169 heq192 ev209 ld203 ev315 ev372 ld366 heq478 ev492 ?_ ev560 ev628 ?_ ev679 ev613
    he714 he715
  · obtain ⟨TPE, hTPE, hinf⟩ := ih.get (.infer .k_infer) hlt12 ev14 rc e1 types rfl g12
      hrc d Γ htypes PE hPE
    exact ⟨TPE, hTPE, hinf, ObsFn.heap_extends ev14⟩
  · intro n T As hnp hT hAs
    obtain ⟨T_after, hT_after, hpis⟩ := ih.get (.infer .peel_params_subst) hlt520 ev522
      v479 x_args x_n_params rfl g520 n hnp d Γ T As hT hAs
    exact ⟨T_after, hT_after, hpis, ObsFn.heap_extends ev522⟩
  · intro n hnp hni
    rw [hnp, hni] at op710
    rw [NatAux.add_ok op710, add_zero]

end IxVM.Refinement.Core
