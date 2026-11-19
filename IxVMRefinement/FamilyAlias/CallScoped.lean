import IxVMRefinement.Assembly.ProjSafe
import IxVMRefinement.Obs.KernelModeled5
import IxVMRefinement.Obs.KernelCheck3
import IxVMRefinement.Obs.KernelLevels2

/-! # Heap-level well-scopedness transport across `rename` and `kexpr_struct_eq`

`KernelModeled::member_val` checks each member's converted type against its advice model by
asserting `kexpr_struct_eq(rename(ty, src, dst), mty) = 1`. The advice model's type `mty` was
already validated well-scoped by `check_advice_record` (`validate_expr_well_scoped`), whereas
`member_val` does not run `validate_expr_well_scoped` directly on `ty`. Because `rename`
preserves bound-variable indices and universe levels, and `kexpr_struct_eq` checks syntactic
equality of both, well-scopedness transfers backwards from `mty` to `ty`:

* `HeapLevelScoped`, `HeapLevelListScoped`, `HeapExprScoped`: structural well-scopedness
  predicates directly on heap pointers (`loadValue`);
* `heapExprScoped_of_rawConvExpr`: any `RawConvExpr` whose reading is well-scoped satisfies
  `HeapExprScoped`;
* `heapExprScoped_of_kexpr_struct_eq`: `kexpr_struct_eq = 1` pulls `HeapExprScoped` back from the
  right argument to the left;
* `heapExprScoped_of_rename`: `KernelModeled::rename` pulls `HeapExprScoped` back from its output
  to its input;
* `rawConvExpr_scoped_of_heapExprScoped`: any `RawConvExpr` satisfying `HeapExprScoped` reads to
  a closed expression with all level parameters in `List.range nlvls`. -/

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Refinement.Core

set_option linter.unusedVariables false

private theorem u56_lt_modulus : (72057594037927936 : Nat) < Aiur.Library.U32.Goldilocks.modulus := by
  decide

private theorem nat_eq_of_field_eq_u56 {a b : Nat} (ha : a < 72057594037927936)
    (hb : b < 72057594037927936) (h : (a : F) = (b : F)) : a = b := by
  have h1 := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt (Nat.lt_trans ha u56_lt_modulus),
       ZMod.val_natCast_of_lt (Nat.lt_trans hb u56_lt_modulus)] at h1

private theorem sub_zero_eq {x y : SourceValue F}
    (h : evalBinOp .sub x y = .ok (.field 0)) : x = y := by
  cases x with
  | field fx =>
    cases y with
    | field fy =>
      simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at h
      exact congrArg Value.field (sub_eq_zero.mp h)
    | _ => simp [evalBinOp] at h
  | _ => simp [evalBinOp] at h

private theorem loadValue_mono {h₁ h₂ : Heap F} {p v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hld : loadValue h₁ p = .ok v) : loadValue h₂ p = .ok v := by
  cases p with
  | ptr ty idx =>
    simp only [loadValue] at hld ⊢
    cases hg : h₁[idx]? with
    | none => simp [hg] at hld
    | some val =>
      rw [hg] at hld
      rw [ext.getElem?_eq hg]
      exact hld
  | _ => simp [loadValue] at hld

private theorem loadValue_enum_cell' {h : Heap F} {addr : Nat} {eName tag : String}
    {args : List (SourceValue F)}
    (cell : h[addr]? = some (.construct eName tag args)) :
    loadValue h (.ptr (.enum eName) addr) = .ok (.construct eName tag args) := by
  simp [loadValue, cell, Value.type, PointerType.valueType]

private theorem loadValue_snoc_enum {h : Heap F} {eName tag : String}
    {args : List (SourceValue F)} :
    loadValue (h ++ [.construct eName tag args]) (.ptr (.enum eName) h.length) =
      .ok (.construct eName tag args) :=
  loadValue_enum_cell' (by simp)

private theorem except_bind_eq_ok' {α β ε : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-! ## Heap-level well-scopedness predicates -/

/-- A heap `KLevel` pointer whose `Param` indices are all `< nl` (and `< 2^56`). -/
inductive HeapLevelScoped (h : Heap F) (nl : Nat) : SourceValue F → Prop where
  | zero {p} :
      loadValue h p = .ok (.construct klevelEnum "Zero" []) →
      HeapLevelScoped h nl p
  | succ {p x} :
      loadValue h p = .ok (.construct klevelEnum "Succ" [x]) →
      HeapLevelScoped h nl x →
      HeapLevelScoped h nl p
  | max {p x y} :
      loadValue h p = .ok (.construct klevelEnum "Max" [x, y]) →
      HeapLevelScoped h nl x → HeapLevelScoped h nl y →
      HeapLevelScoped h nl p
  | imax {p x y} :
      loadValue h p = .ok (.construct klevelEnum "IMax" [x, y]) →
      HeapLevelScoped h nl x → HeapLevelScoped h nl y →
      HeapLevelScoped h nl p
  | param {p} {i : Nat} :
      i < nl → i < 72057594037927936 →
      loadValue h p = .ok (.construct klevelEnum "Param" [.field (i : F)]) →
      HeapLevelScoped h nl p

theorem HeapLevelScoped.mono {h₁ h₂ : Heap F} {nl : Nat} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hs : HeapLevelScoped h₁ nl p) : HeapLevelScoped h₂ nl p := by
  induction hs with
  | zero ld => exact .zero (loadValue_mono ext ld)
  | succ ld _ ih => exact .succ (loadValue_mono ext ld) ih
  | max ld _ _ ihx ihy => exact .max (loadValue_mono ext ld) ihx ihy
  | imax ld _ _ ihx ihy => exact .imax (loadValue_mono ext ld) ihx ihy
  | param hi h56 ld => exact .param hi h56 (loadValue_mono ext ld)

/-- A heap `List<KLevel>` pointer whose elements all satisfy `HeapLevelScoped h nl`. -/
inductive HeapLevelListScoped (h : Heap F) (nl : Nat) : SourceValue F → Prop where
  | nil {p} :
      loadValue h p = .ok (.construct klevelListEnum "Nil" []) →
      HeapLevelListScoped h nl p
  | cons {p x rest} :
      loadValue h p = .ok (.construct klevelListEnum "Cons" [x, rest]) →
      HeapLevelScoped h nl x → HeapLevelListScoped h nl rest →
      HeapLevelListScoped h nl p

theorem HeapLevelListScoped.mono {h₁ h₂ : Heap F} {nl : Nat} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hs : HeapLevelListScoped h₁ nl p) : HeapLevelListScoped h₂ nl p := by
  induction hs with
  | nil ld => exact .nil (loadValue_mono ext ld)
  | cons ld hx _ ihr => exact .cons (loadValue_mono ext ld) (hx.mono ext) ihr

/-- A heap `KExpr` pointer whose `BVar` indices are `< k` (and `< 2^56`) and whose universe levels
all satisfy `HeapLevelScoped h nl`. -/
inductive HeapExprScoped (h : Heap F) (nl : Nat) : Nat → SourceValue F → Prop where
  | bvar {k : Nat} {p} {i : Nat} :
      i < k → i < 72057594037927936 →
      loadValue h p = .ok (.construct kexprEnum "BVar" [.field (i : F)]) →
      HeapExprScoped h nl k p
  | srt {k : Nat} {p lp} :
      loadValue h p = .ok (.construct kexprEnum "Srt" [lp]) →
      HeapLevelScoped h nl lp →
      HeapExprScoped h nl k p
  | const {k : Nat} {p ap lsp} :
      loadValue h p = .ok (.construct kexprEnum "Const" [ap, lsp]) →
      HeapLevelListScoped h nl lsp →
      HeapExprScoped h nl k p
  | app {k : Nat} {p fp ap} :
      loadValue h p = .ok (.construct kexprEnum "App" [fp, ap]) →
      HeapExprScoped h nl k fp → HeapExprScoped h nl k ap →
      HeapExprScoped h nl k p
  | lam {k : Nat} {p tp bp lp} :
      loadValue h p = .ok (.construct kexprEnum "Lam" [tp, bp, lp]) →
      HeapExprScoped h nl k tp → HeapExprScoped h nl (k + 1) bp →
      HeapExprScoped h nl k p
  | forallE {k : Nat} {p tp bp lp} :
      loadValue h p = .ok (.construct kexprEnum "Forall" [tp, bp, lp]) →
      HeapExprScoped h nl k tp → HeapExprScoped h nl (k + 1) bp →
      HeapExprScoped h nl k p
  | letE {k : Nat} {p tp vp bp} :
      loadValue h p = .ok (.construct kexprEnum "Let" [tp, vp, bp]) →
      HeapExprScoped h nl k tp → HeapExprScoped h nl k vp → HeapExprScoped h nl (k + 1) bp →
      HeapExprScoped h nl k p
  | lit {k : Nat} {p lv} :
      loadValue h p = .ok (.construct kexprEnum "Lit" [lv]) →
      HeapExprScoped h nl k p
  | proj {k : Nat} {p sp fi ep} :
      loadValue h p = .ok (.construct kexprEnum "Proj" [sp, fi, ep]) →
      HeapExprScoped h nl k ep →
      HeapExprScoped h nl k p

theorem HeapExprScoped.mono {h₁ h₂ : Heap F} {nl k : Nat} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hs : HeapExprScoped h₁ nl k p) : HeapExprScoped h₂ nl k p := by
  induction hs with
  | bvar hi h56 ld => exact .bvar hi h56 (loadValue_mono ext ld)
  | srt ld hl => exact .srt (loadValue_mono ext ld) (hl.mono ext)
  | const ld hls => exact .const (loadValue_mono ext ld) (hls.mono ext)
  | app ld _ _ ihf iha => exact .app (loadValue_mono ext ld) ihf iha
  | lam ld _ _ iht ihb => exact .lam (loadValue_mono ext ld) iht ihb
  | forallE ld _ _ iht ihb => exact .forallE (loadValue_mono ext ld) iht ihb
  | letE ld _ _ _ iht ihv ihb => exact .letE (loadValue_mono ext ld) iht ihv ihb
  | lit ld => exact .lit (loadValue_mono ext ld)
  | proj ld _ ihe => exact .proj (loadValue_mono ext ld) ihe

/-! ## `level_struct_eq`, `level_list_struct_eq`, `kexpr_struct_eq`, and `rename` pull back scope -/

private theorem level_struct_eq_bool :
    ∀ {pa pb r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelLevels::level_struct_eq" [pa, pb] h r h' cs →
      (r = .field 0 ∨ r = .field 1) ∧ h' = h := by
  intro pa pb r h h' cs ev
  match Obs.«KernelLevels::level_struct_eq».obs ev with
  | .Zero_Zero (he39 := hr) (he40 := hh) .. => exact ⟨Or.inr hr, hh⟩
  | .Zero_other (he46 := hr) (he47 := hh) .. => exact ⟨Or.inl hr, hh⟩
  | .Succ_Succ (ev90 := ev1) (hc107 := hc) .. => exact level_struct_eq_bool ev1
  | .Succ_other (he112 := hr) (he113 := hh) .. => exact ⟨Or.inl hr, hh⟩
  | .Max_Max (ev174 := ev1) (ev196 := ev2) (op168 := op) (hc213 := hc) .. =>
    obtain ⟨hb1, rfl⟩ := level_struct_eq_bool ev1
    obtain ⟨hb2, rfl⟩ := level_struct_eq_bool ev2
    rcases hb1 with rfl | rfl <;> rcases hb2 with rfl | rfl <;>
      (simp only [evalBinOp, Except.ok.injEq] at op; subst op; simp)
  | .Max_other (he218 := hr) (he219 := hh) .. => exact ⟨Or.inl hr, hh⟩
  | .IMax_IMax (ev280 := ev1) (ev302 := ev2) (op274 := op) (hc319 := hc) .. =>
    obtain ⟨hb1, rfl⟩ := level_struct_eq_bool ev1
    obtain ⟨hb2, rfl⟩ := level_struct_eq_bool ev2
    rcases hb1 with rfl | rfl <;> rcases hb2 with rfl | rfl <;>
      (simp only [evalBinOp, Except.ok.injEq] at op; subst op; simp)
  | .IMax_other (he324 := hr) (he325 := hh) .. => exact ⟨Or.inl hr, hh⟩
  | .Param_Param_n0 (he386 := hr) (he387 := hh) .. => exact ⟨Or.inr hr, hh⟩
  | .Param_Param_other (he393 := hr) (he394 := hh) .. => exact ⟨Or.inl hr, hh⟩
  | .Param_other (he400 := hr) (he401 := hh) .. => exact ⟨Or.inl hr, hh⟩
termination_by _ _ _ _ _ cs _ => cs.length
decreasing_by
  all_goals (simp only [hc, List.length_cons, List.length_append]; omega)

private theorem mul_one_of_bool {x y : SourceValue F}
    (hx : x = .field 0 ∨ x = .field 1) (hy : y = .field 0 ∨ y = .field 1)
    (hop : evalBinOp .mul x y = .ok (.field 1)) : x = .field 1 ∧ y = .field 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · simp [evalBinOp] at hop
  · simp [evalBinOp] at hop
  · simp [evalBinOp] at hop
  · exact ⟨rfl, rfl⟩

/-- `level_struct_eq(pa, pb) = 1` pulls `HeapLevelScoped` back from `pb` to `pa`. -/
theorem heapLevelScoped_of_struct_eq {nl : Nat} :
    ∀ {pa pb : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      HeapLevelScoped h nl pb →
      ObsFn W "KernelLevels::level_struct_eq" [pa, pb] h (.field 1) h' cs →
      HeapLevelScoped h nl pa ∧ h' = h := by
  intro pa pb h h' cs hpb ev
  match Obs.«KernelLevels::level_struct_eq».obs ev with
  | .Zero_Zero (ld12 := lda) (he40 := hh) .. => exact ⟨.zero lda, hh⟩
  | .Zero_other (he46 := hr) .. | .Succ_other (he112 := hr) ..
  | .Max_other (he218 := hr) .. | .IMax_other (he324 := hr) ..
  | .Param_Param_other (he393 := hr) .. | .Param_other (he400 := hr) .. =>
    exact absurd (Value.field.inj hr) one_ne_zero
  | .Succ_Succ (ld12 := lda) (ld72 := ldb) (ev90 := ev1) (hc107 := hc) .. =>
    cases hpb with
    | succ ldb' hxb =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ _ h2; injection h2 with hxy
      subst hxy
      obtain ⟨hxa, hh⟩ := heapLevelScoped_of_struct_eq hxb ev1
      exact ⟨.succ lda hxa, hh⟩
    | zero ldb' | max ldb' _ _ | imax ldb' _ _ | param _ _ ldb' =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | .Max_Max (ld12 := lda) (ld143 := ldb) (ev174 := ev1) (ev196 := ev2) (op168 := op)
      (hc213 := hc) .. =>
    obtain ⟨hb1, rfl⟩ := level_struct_eq_bool ev1
    obtain ⟨hb2, rfl⟩ := level_struct_eq_bool ev2
    obtain ⟨rfl, rfl⟩ := mul_one_of_bool hb1 hb2 op
    cases hpb with
    | max ldb' h1 h2 =>
      rw [ldb] at ldb'; injection ldb' with hEq; injection hEq with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain ⟨ha1, -⟩ := heapLevelScoped_of_struct_eq h1 ev1
      obtain ⟨ha2, -⟩ := heapLevelScoped_of_struct_eq h2 ev2
      exact ⟨.max lda ha1 ha2, rfl⟩
    | zero ldb' | succ ldb' _ | imax ldb' _ _ | param _ _ ldb' =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | .IMax_IMax (ld12 := lda) (ld249 := ldb) (ev280 := ev1) (ev302 := ev2) (op274 := op)
      (hc319 := hc) .. =>
    obtain ⟨hb1, rfl⟩ := level_struct_eq_bool ev1
    obtain ⟨hb2, rfl⟩ := level_struct_eq_bool ev2
    obtain ⟨rfl, rfl⟩ := mul_one_of_bool hb1 hb2 op
    cases hpb with
    | imax ldb' h1 h2 =>
      rw [ldb] at ldb'; injection ldb' with hEq; injection hEq with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain ⟨ha1, -⟩ := heapLevelScoped_of_struct_eq h1 ev1
      obtain ⟨ha2, -⟩ := heapLevelScoped_of_struct_eq h2 ev2
      exact ⟨.imax lda ha1 ha2, rfl⟩
    | zero ldb' | succ ldb' _ | max ldb' _ _ | param _ _ ldb' =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | .Param_Param_n0 (ld12 := lda) (ld350 := ldb) (op379 := op) (he387 := hh) .. =>
    cases hpb with
    | param hi h56 ldb' =>
      rw [ldb] at ldb'; injection ldb' with hEq; injection hEq with _ _ hargs
      injection hargs with hij
      subst hij
      rw [sub_zero_eq op] at lda
      exact ⟨.param hi h56 lda, hh⟩
    | zero ldb' | succ ldb' _ | max ldb' _ _ | imax ldb' _ _ =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
termination_by _ _ _ _ cs _ _ => cs.length
decreasing_by
  all_goals (simp only [hc, List.length_cons, List.length_append]; omega)

/-- `level_list_struct_eq(pa, pb) = 1` pulls `HeapLevelListScoped` back from `pb` to `pa`. -/
theorem heapLevelListScoped_of_struct_eq {nl : Nat} :
    ∀ {pa pb : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      HeapLevelListScoped h nl pb →
      ObsFn W "KernelCheck::level_list_struct_eq" [pa, pb] h (.field 1) h' cs →
      HeapLevelListScoped h nl pa ∧ h' = h := by
  intro pa pb h h' cs hpb ev
  rcases Obs.«KernelCheck::level_list_struct_eq».obs ev with
    ⟨lda, _, _, hh, _⟩ |
    ⟨_, _, _, _, hr, _, _⟩ |
    ⟨_, _, _, _, hr, _, _⟩ |
    ⟨_, _, _, _, _, _, _, lda, ldb, ev1, ev2, hc⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, hr, _, _⟩
  · exact ⟨.nil lda, hh⟩
  · exact absurd (Value.field.inj hr) one_ne_zero
  · exact absurd (Value.field.inj hr) one_ne_zero
  · cases hpb with
    | nil ldb' =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
    | cons ldb' hhd htl =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain ⟨ha1, rfl⟩ := heapLevelScoped_of_struct_eq hhd ev1
      obtain ⟨ha2, hh⟩ := heapLevelListScoped_of_struct_eq htl ev2
      exact ⟨.cons lda ha1 ha2, hh⟩
  · exact absurd (Value.field.inj hr) one_ne_zero
termination_by _ _ _ _ cs _ _ => cs.length
decreasing_by
  simp only [hc, List.length_cons, List.length_append]; omega

/-- `kexpr_struct_eq(pa, pb) = 1` pulls `HeapExprScoped` back from `pb` to `pa` at the output heap. -/
theorem heapExprScoped_of_kexpr_struct_eq {nl : Nat} :
    ∀ {k : Nat} {pa pb : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      HeapExprScoped h nl k pb →
      ObsFn W "KernelCheck::kexpr_struct_eq" [pa, pb] h (.field 1) h' cs →
      HeapExprScoped h' nl k pa := by
  intro k pa pb h h' cs hpb ev
  match Obs.«KernelCheck::kexpr_struct_eq».obs ev with
  | .BVar_BVar_n0 (ld12 := lda) (ld36 := ldb) (op65 := op) (he73 := hh) .. =>
    subst hh
    cases hpb with
    | bvar hi h56 ldb' =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ _ hargs; injection hargs with hij
      subst hij
      rw [sub_zero_eq op] at lda
      exact .bvar hi h56 lda
    | srt ldb' _ | const ldb' _ | app ldb' _ _ | lam ldb' _ _ | forallE ldb' _ _
    | letE ldb' _ _ _ | lit ldb' | proj ldb' _ =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | .BVar_BVar_other (he79 := hr) .. | .BVar_other (he86 := hr) ..
  | .Srt_other (he152 := hr) .. | .Const_Const_other (he263 := hr) ..
  | .Const_other (he270 := hr) .. | .App_App_other (he381 := hr) ..
  | .App_other (he388 := hr) .. | .Lam_other (he506 := hr) ..
  | .Forall_other (he624 := hr) .. | .Let_Let_n1_other (he780 := hr) ..
  | .Let_Let_other (he787 := hr) .. | .Let_other (he794 := hr) ..
  | .Lit_other (he860 := hr) .. | .Proj_Proj_n1_other (he1004 := hr) ..
  | .Proj_Proj_other (he1011 := hr) .. | .Proj_other (he1018 := hr) .. =>
    exact absurd (Value.field.inj hr) one_ne_zero
  | .Srt_Srt (ld12 := lda) (ld112 := ldb) (ev130 := ev1) .. =>
    cases hpb with
    | srt ldb' hl =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ _ hargs; injection hargs with hlp
      subst hlp
      obtain ⟨hla, hh⟩ := heapLevelScoped_of_struct_eq hl ev1
      subst hh
      exact .srt lda hla
    | bvar _ _ ldb' | const ldb' _ | app ldb' _ _ | lam ldb' _ _ | forallE ldb' _ _
    | letE ldb' _ _ _ | lit ldb' | proj ldb' _ =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | .Const_Const_n1 (ld12 := lda) (ld183 := ldb) (ev215 := evAddr) (ev241 := evLls) .. =>
    cases hpb with
    | const ldb' hls =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, rfl⟩ := hargs
      obtain ⟨hla, hh⟩ := heapLevelListScoped_of_struct_eq (hls.mono evAddr.heap_extends) evLls
      subst hh
      exact .const (loadValue_mono evAddr.heap_extends lda) hla
    | bvar _ _ ldb' | srt ldb' _ | app ldb' _ _ | lam ldb' _ _ | forallE ldb' _ _
    | letE ldb' _ _ _ | lit ldb' | proj ldb' _ =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | .App_App_n1 (ld12 := lda) (ld301 := ldb) (ev333 := ev1) (ev359 := ev2) (hc376 := hc) .. =>
    cases hpb with
    | app ldb' hf ha =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      have hfa := heapExprScoped_of_kexpr_struct_eq hf ev1
      have haa := heapExprScoped_of_kexpr_struct_eq (ha.mono ev1.heap_extends) ev2
      exact .app (loadValue_mono (ev1.heap_extends.trans ev2.heap_extends) lda)
        (hfa.mono ev2.heap_extends) haa
    | bvar _ _ ldb' | srt ldb' _ | const ldb' _ | lam ldb' _ _ | forallE ldb' _ _
    | letE ldb' _ _ _ | lit ldb' | proj ldb' _ =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | .Lam_Lam (ld12 := lda) (ld424 := ldb) (ev452 := evB) (hc501 := hc) .. =>
    cases hpb with
    | lam ldb' ht hb =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      match Obs.«KernelCheck::kexpr_binder_struct_eq».obs evB with
      | .n1_n1 (ev15 := evPw) (ev50 := evT) (ev76 := evBd) (hc93 := hcB) .. =>
        have hta := heapExprScoped_of_kexpr_struct_eq (ht.mono evPw.heap_extends) evT
        have hba := heapExprScoped_of_kexpr_struct_eq
          (hb.mono (evPw.heap_extends.trans evT.heap_extends)) evBd
        exact .lam (loadValue_mono (evPw.heap_extends.trans (evT.heap_extends.trans evBd.heap_extends)) lda)
          (hta.mono evBd.heap_extends) hba
      | .n1_other (he98 := hr) .. | .other (he105 := hr) .. =>
        exact absurd (Value.field.inj hr) one_ne_zero
    | bvar _ _ ldb' | srt ldb' _ | const ldb' _ | app ldb' _ _ | forallE ldb' _ _
    | letE ldb' _ _ _ | lit ldb' | proj ldb' _ =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | .Forall_Forall (ld12 := lda) (ld542 := ldb) (ev570 := evB) (hc619 := hc) .. =>
    cases hpb with
    | forallE ldb' ht hb =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      match Obs.«KernelCheck::kexpr_binder_struct_eq».obs evB with
      | .n1_n1 (ev15 := evPw) (ev50 := evT) (ev76 := evBd) (hc93 := hcB) .. =>
        have hta := heapExprScoped_of_kexpr_struct_eq (ht.mono evPw.heap_extends) evT
        have hba := heapExprScoped_of_kexpr_struct_eq
          (hb.mono (evPw.heap_extends.trans evT.heap_extends)) evBd
        exact .forallE
          (loadValue_mono (evPw.heap_extends.trans (evT.heap_extends.trans evBd.heap_extends)) lda)
          (hta.mono evBd.heap_extends) hba
      | .n1_other (he98 := hr) .. | .other (he105 := hr) .. =>
        exact absurd (Value.field.inj hr) one_ne_zero
    | bvar _ _ ldb' | srt ldb' _ | const ldb' _ | app ldb' _ _ | lam ldb' _ _
    | letE ldb' _ _ _ | lit ldb' | proj ldb' _ =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | .Let_Let_n1_n1 (ld12 := lda) (ld660 := ldb) (ev697 := evT) (ev732 := evV) (ev758 := evB)
      (hc775 := hc) .. =>
    cases hpb with
    | letE ldb' ht hv hb =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      have hta := heapExprScoped_of_kexpr_struct_eq ht evT
      have hva := heapExprScoped_of_kexpr_struct_eq (hv.mono evT.heap_extends) evV
      have hba := heapExprScoped_of_kexpr_struct_eq
        (hb.mono (evT.heap_extends.trans evV.heap_extends)) evB
      exact .letE (loadValue_mono (evT.heap_extends.trans (evV.heap_extends.trans evB.heap_extends)) lda)
        (hta.mono (evV.heap_extends.trans evB.heap_extends)) (hva.mono evB.heap_extends) hba
    | bvar _ _ ldb' | srt ldb' _ | const ldb' _ | app ldb' _ _ | lam ldb' _ _
    | forallE ldb' _ _ | lit ldb' | proj ldb' _ =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | .Lit_Lit (ld12 := lda) (ev838 := evL) .. =>
    exact .lit (loadValue_mono evL.heap_extends lda)
  | .Proj_Proj_n1_n0 (ld12 := lda) (ld896 := ldb) (ev933 := evAddr) (ev982 := evE) (hc999 := hc) .. =>
    cases hpb with
    | proj ldb' he =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, -, rfl⟩ := hargs
      have hea := heapExprScoped_of_kexpr_struct_eq (he.mono evAddr.heap_extends) evE
      exact .proj (loadValue_mono (evAddr.heap_extends.trans evE.heap_extends) lda) hea
    | bvar _ _ ldb' | srt ldb' _ | const ldb' _ | app ldb' _ _ | lam ldb' _ _
    | forallE ldb' _ _ | letE ldb' _ _ _ | lit ldb' =>
      rw [ldb] at ldb'; injection ldb' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
termination_by _ _ _ _ _ cs _ _ => cs.length
decreasing_by
  all_goals
    try simp only [hc, hcB, List.length_cons, List.length_append]
    try simp only [hc, List.length_cons, List.length_append]
    omega

/-- `KernelModeled::rename` pulls `HeapExprScoped` back from its output to its input at any
super-heap extending the rename's output heap. -/
theorem heapExprScoped_of_rename {nl : Nat} :
    ∀ {e src dst ren : SourceValue F} {h h' hSup : Heap F} {cs : List (Call F)} {k : Nat},
      ObsFn W "KernelModeled::rename" [e, src, dst] h ren h' cs →
      Heap.Extends h' hSup →
      HeapExprScoped hSup nl k ren →
      HeapExprScoped hSup nl k e := by
  intro e src dst ren h h' hSup cs k ev ext hren
  match Obs.«KernelModeled::rename».obs ev with
  | .Const (ld12 := lde) (he34 := hr) (hm33 := hm) (ev51 := evA) .. =>
    subst hr hm
    have ldSup : loadValue hSup (.ptr (.enum kexprEnum) _) =
        .ok (.construct kexprEnum "Const" [_, _]) :=
      loadValue_mono ext loadValue_snoc_enum
    cases hren with
    | const ldb hls =>
      rw [ldSup] at ldb; injection ldb with h1; injection h1 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, rfl⟩ := hargs
      exact .const (loadValue_mono (evA.heap_extends.trans ((Heap.Extends.snoc _ _).trans ext)) lde) hls
    | bvar _ _ ldb | srt ldb _ | app ldb _ _ | lam ldb _ _ | forallE ldb _ _
    | letE ldb _ _ _ | lit ldb | proj ldb _ =>
      rw [ldSup] at ldb; injection ldb with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | .App (ld12 := lde) (he105 := hr) (hm104 := hm) (ev122 := evF) (ev158 := evX) (hc183 := hc) .. =>
    subst hr hm
    have ldSup : loadValue hSup (.ptr (.enum kexprEnum) _) =
        .ok (.construct kexprEnum "App" [_, _]) :=
      loadValue_mono ext loadValue_snoc_enum
    cases hren with
    | app ldb hf hx =>
      rw [ldSup] at ldb; injection ldb with h1; injection h1 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      have e1 : Heap.Extends _ hSup := (Heap.Extends.snoc _ _).trans ext
      have hf' := heapExprScoped_of_rename evF (evX.heap_extends.trans e1) hf
      have hx' := heapExprScoped_of_rename evX e1 hx
      exact .app (loadValue_mono (evF.heap_extends.trans (evX.heap_extends.trans e1)) lde) hf' hx'
    | bvar _ _ ldb | srt ldb _ | const ldb _ | lam ldb _ _ | forallE ldb _ _
    | letE ldb _ _ _ | lit ldb | proj ldb _ =>
      rw [ldSup] at ldb; injection ldb with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | .Lam (ld12 := lde) (he210 := hr) (hm209 := hm) (ev228 := evT) (ev264 := evB) (hc296 := hc) .. =>
    subst hr hm
    have ldSup : loadValue hSup (.ptr (.enum kexprEnum) _) =
        .ok (.construct kexprEnum "Lam" [_, _, _]) :=
      loadValue_mono ext loadValue_snoc_enum
    cases hren with
    | lam ldb ht hb =>
      rw [ldSup] at ldb; injection ldb with h1; injection h1 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, -⟩ := hargs
      have e1 : Heap.Extends _ hSup := (Heap.Extends.snoc _ _).trans ext
      have ht' := heapExprScoped_of_rename evT (evB.heap_extends.trans e1) ht
      have hb' := heapExprScoped_of_rename evB e1 hb
      exact .lam (loadValue_mono (evT.heap_extends.trans (evB.heap_extends.trans e1)) lde) ht' hb'
    | bvar _ _ ldb | srt ldb _ | const ldb _ | app ldb _ _ | forallE ldb _ _
    | letE ldb _ _ _ | lit ldb | proj ldb _ =>
      rw [ldSup] at ldb; injection ldb with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | .Forall (ld12 := lde) (he323 := hr) (hm322 := hm) (ev341 := evT) (ev377 := evB) (hc409 := hc) .. =>
    subst hr hm
    have ldSup : loadValue hSup (.ptr (.enum kexprEnum) _) =
        .ok (.construct kexprEnum "Forall" [_, _, _]) :=
      loadValue_mono ext loadValue_snoc_enum
    cases hren with
    | forallE ldb ht hb =>
      rw [ldSup] at ldb; injection ldb with h1; injection h1 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, -⟩ := hargs
      have e1 : Heap.Extends _ hSup := (Heap.Extends.snoc _ _).trans ext
      have ht' := heapExprScoped_of_rename evT (evB.heap_extends.trans e1) ht
      have hb' := heapExprScoped_of_rename evB e1 hb
      exact .forallE (loadValue_mono (evT.heap_extends.trans (evB.heap_extends.trans e1)) lde) ht' hb'
    | bvar _ _ ldb | srt ldb _ | const ldb _ | app ldb _ _ | lam ldb _ _
    | letE ldb _ _ _ | lit ldb | proj ldb _ =>
      rw [ldSup] at ldb; injection ldb with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | .Let (ld12 := lde) (he436 := hr) (hm435 := hm) (ev454 := evT) (ev490 := evV) (ev526 := evB)
      (hc551 := hc) .. =>
    subst hr hm
    have ldSup : loadValue hSup (.ptr (.enum kexprEnum) _) =
        .ok (.construct kexprEnum "Let" [_, _, _]) :=
      loadValue_mono ext loadValue_snoc_enum
    cases hren with
    | letE ldb ht hv hb =>
      rw [ldSup] at ldb; injection ldb with h1; injection h1 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      have e1 : Heap.Extends _ hSup := (Heap.Extends.snoc _ _).trans ext
      have ht' := heapExprScoped_of_rename evT (evV.heap_extends.trans (evB.heap_extends.trans e1)) ht
      have hv' := heapExprScoped_of_rename evV (evB.heap_extends.trans e1) hv
      have hb' := heapExprScoped_of_rename evB e1 hb
      exact .letE
        (loadValue_mono (evT.heap_extends.trans (evV.heap_extends.trans (evB.heap_extends.trans e1))) lde)
        ht' hv' hb'
    | bvar _ _ ldb | srt ldb _ | const ldb _ | app ldb _ _ | lam ldb _ _
    | forallE ldb _ _ | lit ldb | proj ldb _ =>
      rw [ldSup] at ldb; injection ldb with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | .Proj (ld12 := lde) (he578 := hr) (hm577 := hm) (ev596 := evA) (ev639 := evX) (hc664 := hc) .. =>
    subst hr hm
    have ldSup : loadValue hSup (.ptr (.enum kexprEnum) _) =
        .ok (.construct kexprEnum "Proj" [_, _, _]) :=
      loadValue_mono ext loadValue_snoc_enum
    cases hren with
    | proj ldb hx =>
      rw [ldSup] at ldb; injection ldb with h1; injection h1 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, -, rfl⟩ := hargs
      have e1 : Heap.Extends _ hSup := (Heap.Extends.snoc _ _).trans ext
      have hx' := heapExprScoped_of_rename evX e1 hx
      exact .proj (loadValue_mono (evA.heap_extends.trans (evX.heap_extends.trans e1)) lde) hx'
    | bvar _ _ ldb | srt ldb _ | const ldb _ | app ldb _ _ | lam ldb _ _
    | forallE ldb _ _ | letE ldb _ _ _ | lit ldb =>
      rw [ldSup] at ldb; injection ldb with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | .other (he670 := hr) .. =>
    subst hr; exact hren
termination_by _ _ _ _ _ _ _ cs _ _ _ _ => cs.length
decreasing_by
  all_goals (simp only [hc, List.length_cons, List.length_append]; omega)

/-! ## Bridge between `RawConvExpr` / `exprReader` and `HeapExprScoped` -/

private theorem heapLevelScoped_of_rawKLevel {h : Heap F} {nl : Nat} {l : Core.KLevel}
    {p : SourceValue F} (rl : L1.RawKLevel h l p)
    (hdef : l.allParamsDefined (List.range nl) = true) :
    HeapLevelScoped h nl p := by
  induction rl with
  | zero cell => exact .zero (loadValue_enum_cell' cell)
  | succ cell _ ih => exact .succ (loadValue_enum_cell' cell) (ih hdef)
  | max cell _ _ ih1 ih2 =>
    simp only [Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true] at hdef
    exact .max (loadValue_enum_cell' cell) (ih1 hdef.1) (ih2 hdef.2)
  | imax cell _ _ ih1 ih2 =>
    simp only [Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true] at hdef
    exact .imax (loadValue_enum_cell' cell) (ih1 hdef.1) (ih2 hdef.2)
  | param hn cell =>
    simp only [Ix.Kernel.Level.allParamsDefined, List.contains_iff_mem, List.mem_range] at hdef
    exact .param hdef hn (loadValue_enum_cell' cell)

private theorem heapLevelListScoped_of_rawKLevelList {h : Heap F} {nl : Nat}
    {ls : List Core.KLevel} {p : SourceValue F} (rls : L1.RawKLevelList h ls p)
    (hdef : ls.all (Ix.Kernel.Level.allParamsDefined (List.range nl)) = true) :
    HeapLevelListScoped h nl p := by
  induction rls with
  | nil cell => exact .nil (loadValue_enum_cell' cell)
  | cons cell hhd _ ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hdef
    exact .cons (loadValue_enum_cell' cell)
      (heapLevelScoped_of_rawKLevel hhd hdef.1) (ih hdef.2)

private theorem rawKLevel_allParamsDefined_of_scoped {h hSup : Heap F} {nl : Nat}
    {l : Core.KLevel} {p : SourceValue F}
    (ext : Heap.Extends h hSup) (rl : L1.RawKLevel h l p) (hs : HeapLevelScoped hSup nl p) :
    l.allParamsDefined (List.range nl) = true := by
  induction rl with
  | zero cell => rfl
  | succ cell _ ih =>
    have ld := loadValue_enum_cell' (ext.getElem?_eq cell)
    cases hs with
    | succ ld' hx =>
      rw [ld] at ld'; injection ld' with h1; injection h1 with _ _ hargs; injection hargs with hEq
      subst hEq; exact ih hx
    | zero ld' | max ld' _ _ | imax ld' _ _ | param _ _ ld' =>
      rw [ld] at ld'; injection ld' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | max cell _ _ ih1 ih2 =>
    have ld := loadValue_enum_cell' (ext.getElem?_eq cell)
    cases hs with
    | max ld' h1 h2 =>
      rw [ld] at ld'; injection ld' with hEq; injection hEq with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      simp [Ix.Kernel.Level.allParamsDefined, ih1 h1, ih2 h2]
    | zero ld' | succ ld' _ | imax ld' _ _ | param _ _ ld' =>
      rw [ld] at ld'; injection ld' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | imax cell _ _ ih1 ih2 =>
    have ld := loadValue_enum_cell' (ext.getElem?_eq cell)
    cases hs with
    | imax ld' h1 h2 =>
      rw [ld] at ld'; injection ld' with hEq; injection hEq with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      simp [Ix.Kernel.Level.allParamsDefined, ih1 h1, ih2 h2]
    | zero ld' | succ ld' _ | max ld' _ _ | param _ _ ld' =>
      rw [ld] at ld'; injection ld' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | param hn cell =>
    have ld := loadValue_enum_cell' (ext.getElem?_eq cell)
    cases hs with
    | param hi h56 ld' =>
      rw [ld] at ld'; injection ld' with hEq; injection hEq with _ _ hargs
      injection hargs with hf
      have hni := nat_eq_of_field_eq_u56 hn h56 (Value.field.inj hf)
      subst hni
      simp [Ix.Kernel.Level.allParamsDefined, List.contains_iff_mem, List.mem_range, hi]
    | zero ld' | succ ld' _ | max ld' _ _ | imax ld' _ _ =>
      rw [ld] at ld'; injection ld' with h1; injection h1 with _ ht _; exact absurd ht (by decide)

private theorem rawKLevelList_allParamsDefined_of_scoped {h hSup : Heap F} {nl : Nat}
    {ls : List Core.KLevel} {p : SourceValue F}
    (ext : Heap.Extends h hSup) (rls : L1.RawKLevelList h ls p)
    (hs : HeapLevelListScoped hSup nl p) :
    ls.all (Ix.Kernel.Level.allParamsDefined (List.range nl)) = true := by
  induction rls with
  | nil cell => rfl
  | cons cell hhd _ ih =>
    have ld := loadValue_enum_cell' (ext.getElem?_eq cell)
    cases hs with
    | nil ld' =>
      rw [ld] at ld'; injection ld' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
    | cons ld' h1 h2 =>
      rw [ld] at ld'; injection ld' with hEq; injection hEq with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      simp [rawKLevel_allParamsDefined_of_scoped ext hhd h1, ih h2]

private theorem mapM_univs_eq {univs : List Ixon.Univ} {uIdxs : List UInt64}
    {ls₁ ls₂ : List Core.KLevel}
    (h1 : uIdxs.mapM (fun i => univs[i.toNat]?.map (Ix.Kernel.Reader.convUniv id)) = some ls₁)
    (h2 : Ix.Kernel.Reader.readUnivs (univs.toArray.map (Ix.Kernel.Reader.convUniv id)) uIdxs =
      .ok ls₂) :
    ls₁ = ls₂ := by
  induction uIdxs generalizing ls₁ ls₂ with
  | nil =>
    simp [Option.bind, pure, Option.pure, Ix.Kernel.Reader.readUnivs] at h1 h2
    rw [← h1, ← h2]
  | cons i rest ih =>
    simp only [List.mapM_cons, Ix.Kernel.Reader.readUnivs] at h1 h2
    cases hget : univs[i.toNat]? with
    | none =>
      simp [hget] at h1
    | some u =>
      simp only [hget, Option.map_some, Option.bind_some] at h1
      have hgetA : (univs.toArray.map (Ix.Kernel.Reader.convUniv id))[i.toNat]? =
          some (Ix.Kernel.Reader.convUniv id u) := by
        rw [Array.getElem?_map, ← Array.getElem?_toList, List.toArray_toList, hget]
        rfl
      simp only [hgetA, Bind.bind, Except.bind] at h2
      cases hm : rest.mapM (fun j => univs[j.toNat]?.map (Ix.Kernel.Reader.convUniv id)) with
      | none => simp [hm] at h1
      | some tl₁ =>
        simp only [hm, Option.bind_some, pure, Option.pure, Option.some.injEq] at h1
        cases hr : Ix.Kernel.Reader.readUnivs (univs.toArray.map (Ix.Kernel.Reader.convUniv id)) rest with
        | error _ => simp [hr] at h2
        | ok tl₂ =>
          simp only [hr, pure, Except.pure, Except.ok.injEq] at h2
          subst h1 h2
          exact congrArg _ (ih hm hr)

private theorem heapExprScoped_of_rawConvExpr_go
    {ecx : Ix.Kernel.Reader.ECx .anon}
    {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    (hunivs : ecx.univs = univs.toArray.map (Ix.Kernel.Reader.convUniv id))
    {h₀ : Heap F} {nl : Nat} {bound : Nat} {e : Ixon.Expr} {kp : SourceValue F}
    (raw : L1.RawConvExpr refs recurAddrs univs sharing blobs h₀ bound e kp) :
    ∀ {n k : Nat} {E_rd : Core.KExpr},
      n ≤ sharing.length →
      (bound ≤ n ∨ n = sharing.length) →
      Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (sharing.take n)) e = .ok E_rd →
      E_rd.looseBVarsBounded k = true →
      E_rd.allLevelParamsDefined (List.range nl) = true →
      HeapExprScoped h₀ nl k kp := by
  induction raw with
  | @var _ addr idx hidx cell =>
    intro n k E_rd _ _ hconv hlbb _
    simp only [Ix.Kernel.Reader.convExpr, pure, Except.pure, Except.ok.injEq] at hconv
    subst hconv
    rw [Ix.Kernel.Expr.mkBvar_eq] at hlbb
    simp only [Ix.Kernel.Expr.looseBVarsBounded, decide_eq_true_eq] at hlbb
    exact .bvar hlbb hidx (loadValue_enum_cell' cell)
  | @sort _ addr uIdx u lp huIdx hu rl cell =>
    intro n k E_rd _ _ hconv _ hdef
    have hget : ecx.univs[uIdx.toNat]? = some (Ix.Kernel.Reader.convUniv id u) := by
      rw [hunivs, Array.getElem?_map, ← Array.getElem?_toList, List.toArray_toList, hu]; rfl
    simp only [Ix.Kernel.Reader.convExpr, hget, pure, Except.pure, Except.ok.injEq] at hconv
    subst hconv
    rw [Ix.Kernel.Expr.mkSort_eq] at hdef
    exact .srt (loadValue_enum_cell' cell) (heapLevelScoped_of_rawKLevel rl hdef)
  | @ref _ addr rIdx uIdxs a d ap lsp ls hrIdx href hd ra hls rls cell =>
    intro n k E_rd _ _ hconv _ hdef
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    cases hkey : ecx.keyRef rIdx.toNat with
    | error _ => simp [hkey, Bind.bind, Except.bind] at hconv
    | ok nm =>
      simp only [hkey, Bind.bind, Except.bind] at hconv
      cases hru : Ix.Kernel.Reader.readUnivs ecx.univs uIdxs.toList with
      | error _ => simp [hru] at hconv
      | ok ls₂ =>
        simp only [hru, pure, Except.pure, Except.ok.injEq] at hconv
        subst hconv
        rw [hunivs] at hru
        have hleq := mapM_univs_eq hls hru
        subst hleq
        rw [Ix.Kernel.Expr.mkConst_eq] at hdef
        exact .const (loadValue_enum_cell' cell) (heapLevelListScoped_of_rawKLevelList rls hdef)
  | @recur _ addr rIdx uIdxs a d ap lsp ls hrIdx hrec hd ra hls rls cell =>
    intro n k E_rd _ _ hconv _ hdef
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    cases hkey : ecx.keyRecur rIdx.toNat with
    | error _ => simp [hkey, Bind.bind, Except.bind] at hconv
    | ok nm =>
      simp only [hkey, Bind.bind, Except.bind] at hconv
      cases hru : Ix.Kernel.Reader.readUnivs ecx.univs uIdxs.toList with
      | error _ => simp [hru] at hconv
      | ok ls₂ =>
        simp only [hru, pure, Except.pure, Except.ok.injEq] at hconv
        subst hconv
        rw [hunivs] at hru
        have hleq := mapM_univs_eq hls hru
        subst hleq
        rw [Ix.Kernel.Expr.mkConst_eq] at hdef
        exact .const (loadValue_enum_cell' cell) (heapLevelListScoped_of_rawKLevelList rls hdef)
  | prj _ _ _ _ _ _ cell ih =>
    intro n k E_rd hn hbnd hconv hlbb hdef
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    cases hkey : ecx.keyRef _ with
    | error _ => simp [hkey, Bind.bind, Except.bind] at hconv
    | ok nm =>
      simp only [hkey, Bind.bind, Except.bind] at hconv
      obtain ⟨Ei, hEi, hret⟩ := except_bind_eq_ok' hconv
      injection hret with hE; subst hE
      rw [Ix.Kernel.Expr.mkProj_eq] at hlbb hdef
      exact .proj (loadValue_enum_cell' cell) (ih hn hbnd hEi hlbb hdef)
  | str _ _ _ _ _ cell =>
    intro _ _ _ _ _ _ _ _; exact .lit (loadValue_enum_cell' cell)
  | nat _ _ _ _ _ _ _ cell =>
    intro _ _ _ _ _ _ _ _; exact .lit (loadValue_enum_cell' cell)
  | app _ _ cell ihf iha =>
    intro n k E_rd hn hbnd hconv hlbb hdef
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨Ef, hEf, h1⟩ := except_bind_eq_ok' hconv
    obtain ⟨Ea, hEa, hret⟩ := except_bind_eq_ok' h1
    injection hret with hE; subst hE
    rw [Ix.Kernel.Expr.mkApp_eq] at hlbb hdef
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Ix.Kernel.Expr.allLevelParamsDefined,
      Bool.and_eq_true] at hlbb hdef
    exact .app (loadValue_enum_cell' cell)
      (ihf hn hbnd hEf hlbb.1 hdef.1) (iha hn hbnd hEa hlbb.2 hdef.2)
  | lam _ _ _ cell iht ihb =>
    intro n k E_rd hn hbnd hconv hlbb hdef
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨Et, hEt, h1⟩ := except_bind_eq_ok' hconv
    obtain ⟨Eb, hEb, hret⟩ := except_bind_eq_ok' h1
    injection hret with hE; subst hE
    rw [Ix.Kernel.Expr.mkLam_eq] at hlbb hdef
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Ix.Kernel.Expr.allLevelParamsDefined,
      Bool.and_eq_true] at hlbb hdef
    exact .lam (loadValue_enum_cell' cell)
      (iht hn hbnd hEt hlbb.1 hdef.1) (ihb hn hbnd hEb hlbb.2 hdef.2)
  | all _ _ _ cell iht ihb =>
    intro n k E_rd hn hbnd hconv hlbb hdef
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨Et, hEt, h1⟩ := except_bind_eq_ok' hconv
    obtain ⟨Eb, hEb, hret⟩ := except_bind_eq_ok' h1
    injection hret with hE; subst hE
    rw [Ix.Kernel.Expr.mkForall_eq] at hlbb hdef
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Ix.Kernel.Expr.allLevelParamsDefined,
      Bool.and_eq_true] at hlbb hdef
    exact .forallE (loadValue_enum_cell' cell)
      (iht hn hbnd hEt hlbb.1 hdef.1) (ihb hn hbnd hEb hlbb.2 hdef.2)
  | letE _ _ _ cell iht ihv ihb =>
    intro n k E_rd hn hbnd hconv hlbb hdef
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨Et, hEt, h1⟩ := except_bind_eq_ok' hconv
    obtain ⟨Ev, hEv, h2⟩ := except_bind_eq_ok' h1
    obtain ⟨Eb, hEb, hret⟩ := except_bind_eq_ok' h2
    injection hret with hE; subst hE
    rw [Ix.Kernel.Expr.mkLet_eq] at hlbb hdef
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Ix.Kernel.Expr.allLevelParamsDefined,
      Bool.and_eq_true] at hlbb hdef
    exact .letE (loadValue_enum_cell' cell)
      (iht hn hbnd hEt hlbb.1.1 hdef.1.1)
      (ihv hn hbnd hEv hlbb.1.2 hdef.1.2)
      (ihb hn hbnd hEb hlbb.2 hdef.2)
  | @share bnd idx s _ hidx hsh_get _ ih =>
    intro n k E_rd hn hbnd hconv hlbb hdef
    have hi_len : idx.toNat < sharing.length := (List.getElem?_eq_some_iff.mp hsh_get).1
    have hi_n : idx.toNat < n := by rcases hbnd with hb | rfl <;> omega
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    rw [L1.buildShareTbl_take_getElem? ecx sharing hi_n hsh_get] at hconv
    exact ih (Nat.le_of_lt hi_len) (Or.inl (Nat.le_refl _)) hconv hlbb hdef

/-- Any `RawConvExpr` whose `MemberReader` reading is closed and level-scoped in `List.range nl`
satisfies `HeapExprScoped h₀ nl 0 kp`. -/
theorem heapExprScoped_of_rawConvExpr
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {h₀ : Heap F} {nl : Nat} {e : Ixon.Expr} {kp : SourceValue F} {E_rd : Core.KExpr}
    (raw : L1.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h₀ 4294967295 e kp)
    (hread : (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read e = .ok E_rd)
    (hlbb : E_rd.looseBVarsBounded 0 = true)
    (hdef : E_rd.allLevelParamsDefined (List.range nl) = true) :
    HeapExprScoped h₀ nl 0 kp := by
  obtain ⟨hecx, htbl⟩ := L1.memberReader_mk'_eq cx src id self
  unfold Ix.Kernel.Reader.MemberReader.read at hread
  rw [hecx, htbl, ← List.take_length (l := src.sharing.toList)] at hread
  exact heapExprScoped_of_rawConvExpr_go (by simp) raw (Nat.le_refl _) (Or.inr rfl)
    hread hlbb hdef

private theorem rawConvExpr_scoped_of_heapExprScoped_go
    {ecx : Ix.Kernel.Reader.ECx .anon}
    {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    (hunivs : ecx.univs = univs.toArray.map (Ix.Kernel.Reader.convUniv id))
    {h₀ hSup : Heap F} (ext : Heap.Extends h₀ hSup) {nl : Nat}
    {bound : Nat} {e : Ixon.Expr} {kp : SourceValue F}
    (raw : L1.RawConvExpr refs recurAddrs univs sharing blobs h₀ bound e kp) :
    ∀ {n k : Nat} {E_rd : Core.KExpr},
      n ≤ sharing.length →
      (bound ≤ n ∨ n = sharing.length) →
      Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (sharing.take n)) e = .ok E_rd →
      HeapExprScoped hSup nl k kp →
      E_rd.looseBVarsBounded k = true ∧ E_rd.allLevelParamsDefined (List.range nl) = true := by
  induction raw with
  | @var _ addr idx hidx cell =>
    intro n k E_rd _ _ hconv hs
    simp only [Ix.Kernel.Reader.convExpr, pure, Except.pure, Except.ok.injEq] at hconv
    subst hconv
    have ld := loadValue_enum_cell' (ext.getElem?_eq cell)
    cases hs with
    | bvar hi h56 ld' =>
      rw [ld] at ld'; injection ld' with h1; injection h1 with _ _ hargs; injection hargs with hf
      have heq := nat_eq_of_field_eq_u56 hidx h56 (Value.field.inj hf)
      subst heq
      rw [Ix.Kernel.Expr.mkBvar_eq]
      exact ⟨by simp [Ix.Kernel.Expr.looseBVarsBounded, hi], rfl⟩
    | srt ld' _ | const ld' _ | app ld' _ _ | lam ld' _ _ | forallE ld' _ _
    | letE ld' _ _ _ | lit ld' | proj ld' _ =>
      rw [ld] at ld'; injection ld' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | @sort _ addr uIdx u lp huIdx hu rl cell =>
    intro n k E_rd _ _ hconv hs
    have hget : ecx.univs[uIdx.toNat]? = some (Ix.Kernel.Reader.convUniv id u) := by
      rw [hunivs, Array.getElem?_map, ← Array.getElem?_toList, List.toArray_toList, hu]; rfl
    simp only [Ix.Kernel.Reader.convExpr, hget, pure, Except.pure, Except.ok.injEq] at hconv
    subst hconv
    have ld := loadValue_enum_cell' (ext.getElem?_eq cell)
    cases hs with
    | srt ld' hl =>
      rw [ld] at ld'; injection ld' with h1; injection h1 with _ _ hargs; injection hargs with hlp
      subst hlp
      rw [Ix.Kernel.Expr.mkSort_eq]
      exact ⟨rfl, rawKLevel_allParamsDefined_of_scoped ext rl hl⟩
    | bvar _ _ ld' | const ld' _ | app ld' _ _ | lam ld' _ _ | forallE ld' _ _
    | letE ld' _ _ _ | lit ld' | proj ld' _ =>
      rw [ld] at ld'; injection ld' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | @ref _ addr rIdx uIdxs a d ap lsp ls hrIdx href hd ra hls rls cell =>
    intro n k E_rd _ _ hconv hs
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    cases hkey : ecx.keyRef rIdx.toNat with
    | error _ => simp [hkey, Bind.bind, Except.bind] at hconv
    | ok nm =>
      simp only [hkey, Bind.bind, Except.bind] at hconv
      cases hru : Ix.Kernel.Reader.readUnivs ecx.univs uIdxs.toList with
      | error _ => simp [hru] at hconv
      | ok ls₂ =>
        simp only [hru, pure, Except.pure, Except.ok.injEq] at hconv
        subst hconv
        rw [hunivs] at hru
        have hleq := mapM_univs_eq hls hru
        subst hleq
        have ld := loadValue_enum_cell' (ext.getElem?_eq cell)
        cases hs with
        | const ld' hls' =>
          rw [ld] at ld'; injection ld' with h1; injection h1 with _ _ hargs
          simp only [List.cons.injEq, and_true] at hargs
          obtain ⟨-, rfl⟩ := hargs
          rw [Ix.Kernel.Expr.mkConst_eq]
          exact ⟨rfl, rawKLevelList_allParamsDefined_of_scoped ext rls hls'⟩
        | bvar _ _ ld' | srt ld' _ | app ld' _ _ | lam ld' _ _ | forallE ld' _ _
        | letE ld' _ _ _ | lit ld' | proj ld' _ =>
          rw [ld] at ld'; injection ld' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | @recur _ addr rIdx uIdxs a d ap lsp ls hrIdx hrec hd ra hls rls cell =>
    intro n k E_rd _ _ hconv hs
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    cases hkey : ecx.keyRecur rIdx.toNat with
    | error _ => simp [hkey, Bind.bind, Except.bind] at hconv
    | ok nm =>
      simp only [hkey, Bind.bind, Except.bind] at hconv
      cases hru : Ix.Kernel.Reader.readUnivs ecx.univs uIdxs.toList with
      | error _ => simp [hru] at hconv
      | ok ls₂ =>
        simp only [hru, pure, Except.pure, Except.ok.injEq] at hconv
        subst hconv
        rw [hunivs] at hru
        have hleq := mapM_univs_eq hls hru
        subst hleq
        have ld := loadValue_enum_cell' (ext.getElem?_eq cell)
        cases hs with
        | const ld' hls' =>
          rw [ld] at ld'; injection ld' with h1; injection h1 with _ _ hargs
          simp only [List.cons.injEq, and_true] at hargs
          obtain ⟨-, rfl⟩ := hargs
          rw [Ix.Kernel.Expr.mkConst_eq]
          exact ⟨rfl, rawKLevelList_allParamsDefined_of_scoped ext rls hls'⟩
        | bvar _ _ ld' | srt ld' _ | app ld' _ _ | lam ld' _ _ | forallE ld' _ _
        | letE ld' _ _ _ | lit ld' | proj ld' _ =>
          rw [ld] at ld'; injection ld' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | prj _ _ _ _ _ _ cell ih =>
    intro n k E_rd hn hbnd hconv hs
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    cases hkey : ecx.keyRef _ with
    | error _ => simp [hkey, Bind.bind, Except.bind] at hconv
    | ok nm =>
      simp only [hkey, Bind.bind, Except.bind] at hconv
      obtain ⟨Ei, hEi, hret⟩ := except_bind_eq_ok' hconv
      injection hret with hE; subst hE
      have ld := loadValue_enum_cell' (ext.getElem?_eq cell)
      cases hs with
      | proj ld' hi =>
        rw [ld] at ld'; injection ld' with h1; injection h1 with _ _ hargs
        simp only [List.cons.injEq, and_true] at hargs
        obtain ⟨-, -, rfl⟩ := hargs
        rw [Ix.Kernel.Expr.mkProj_eq]
        exact ih hn hbnd hEi hi
      | bvar _ _ ld' | srt ld' _ | const ld' _ | app ld' _ _ | lam ld' _ _
      | forallE ld' _ _ | letE ld' _ _ _ | lit ld' =>
        rw [ld] at ld'; injection ld' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | str _ _ _ _ _ cell =>
    intro n k E_rd _ _ hconv _
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    cases hbl : ecx.readStr _ with
    | error _ => simp [hbl, Bind.bind, Except.bind] at hconv
    | ok s =>
      simp only [hbl, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hconv
      subst hconv
      rw [Ix.Kernel.Expr.mkLit_eq]
      exact ⟨rfl, rfl⟩
  | nat _ _ _ _ _ _ _ cell =>
    intro n k E_rd _ _ hconv _
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    cases hbl : ecx.readNat _ with
    | error _ => simp [hbl, Bind.bind, Except.bind] at hconv
    | ok v =>
      simp only [hbl, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hconv
      subst hconv
      rw [Ix.Kernel.Expr.mkLit_eq]
      exact ⟨rfl, rfl⟩
  | app _ _ cell ihf iha =>
    intro n k E_rd hn hbnd hconv hs
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨Ef, hEf, h1⟩ := except_bind_eq_ok' hconv
    obtain ⟨Ea, hEa, hret⟩ := except_bind_eq_ok' h1
    injection hret with hE; subst hE
    have ld := loadValue_enum_cell' (ext.getElem?_eq cell)
    cases hs with
    | app ld' hf ha =>
      rw [ld] at ld'; injection ld' with hEq; injection hEq with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain ⟨lf, df⟩ := ihf hn hbnd hEf hf
      obtain ⟨la, da⟩ := iha hn hbnd hEa ha
      rw [Ix.Kernel.Expr.mkApp_eq]
      exact ⟨by simp [Ix.Kernel.Expr.looseBVarsBounded, lf, la],
             by simp [Ix.Kernel.Expr.allLevelParamsDefined, df, da]⟩
    | bvar _ _ ld' | srt ld' _ | const ld' _ | lam ld' _ _ | forallE ld' _ _
    | letE ld' _ _ _ | lit ld' | proj ld' _ =>
      rw [ld] at ld'; injection ld' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | lam _ _ _ cell iht ihb =>
    intro n k E_rd hn hbnd hconv hs
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨Et, hEt, h1⟩ := except_bind_eq_ok' hconv
    obtain ⟨Eb, hEb, hret⟩ := except_bind_eq_ok' h1
    injection hret with hE; subst hE
    have ld := loadValue_enum_cell' (ext.getElem?_eq cell)
    cases hs with
    | lam ld' ht hb =>
      rw [ld] at ld'; injection ld' with hEq; injection hEq with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, -⟩ := hargs
      obtain ⟨lt, dt⟩ := iht hn hbnd hEt ht
      obtain ⟨lb, db⟩ := ihb hn hbnd hEb hb
      rw [Ix.Kernel.Expr.mkLam_eq]
      exact ⟨by simp [Ix.Kernel.Expr.looseBVarsBounded, lt, lb],
             by simp [Ix.Kernel.Expr.allLevelParamsDefined, dt, db]⟩
    | bvar _ _ ld' | srt ld' _ | const ld' _ | app ld' _ _ | forallE ld' _ _
    | letE ld' _ _ _ | lit ld' | proj ld' _ =>
      rw [ld] at ld'; injection ld' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | all _ _ _ cell iht ihb =>
    intro n k E_rd hn hbnd hconv hs
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨Et, hEt, h1⟩ := except_bind_eq_ok' hconv
    obtain ⟨Eb, hEb, hret⟩ := except_bind_eq_ok' h1
    injection hret with hE; subst hE
    have ld := loadValue_enum_cell' (ext.getElem?_eq cell)
    cases hs with
    | forallE ld' ht hb =>
      rw [ld] at ld'; injection ld' with hEq; injection hEq with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, -⟩ := hargs
      obtain ⟨lt, dt⟩ := iht hn hbnd hEt ht
      obtain ⟨lb, db⟩ := ihb hn hbnd hEb hb
      rw [Ix.Kernel.Expr.mkForall_eq]
      exact ⟨by simp [Ix.Kernel.Expr.looseBVarsBounded, lt, lb],
             by simp [Ix.Kernel.Expr.allLevelParamsDefined, dt, db]⟩
    | bvar _ _ ld' | srt ld' _ | const ld' _ | app ld' _ _ | lam ld' _ _
    | letE ld' _ _ _ | lit ld' | proj ld' _ =>
      rw [ld] at ld'; injection ld' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | letE _ _ _ cell iht ihv ihb =>
    intro n k E_rd hn hbnd hconv hs
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨Et, hEt, h1⟩ := except_bind_eq_ok' hconv
    obtain ⟨Ev, hEv, h2⟩ := except_bind_eq_ok' h1
    obtain ⟨Eb, hEb, hret⟩ := except_bind_eq_ok' h2
    injection hret with hE; subst hE
    have ld := loadValue_enum_cell' (ext.getElem?_eq cell)
    cases hs with
    | letE ld' ht hv hb =>
      rw [ld] at ld'; injection ld' with hEq; injection hEq with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain ⟨lt, dt⟩ := iht hn hbnd hEt ht
      obtain ⟨lv, dv⟩ := ihv hn hbnd hEv hv
      obtain ⟨lb, db⟩ := ihb hn hbnd hEb hb
      rw [Ix.Kernel.Expr.mkLet_eq]
      exact ⟨by simp [Ix.Kernel.Expr.looseBVarsBounded, lt, lv, lb],
             by simp [Ix.Kernel.Expr.allLevelParamsDefined, dt, dv, db]⟩
    | bvar _ _ ld' | srt ld' _ | const ld' _ | app ld' _ _ | lam ld' _ _
    | forallE ld' _ _ | lit ld' | proj ld' _ =>
      rw [ld] at ld'; injection ld' with h1; injection h1 with _ ht _; exact absurd ht (by decide)
  | @share bnd idx s _ hidx hsh_get _ ih =>
    intro n k E_rd hn hbnd hconv hs
    have hi_len : idx.toNat < sharing.length := (List.getElem?_eq_some_iff.mp hsh_get).1
    have hi_n : idx.toNat < n := by rcases hbnd with hb | rfl <;> omega
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    rw [L1.buildShareTbl_take_getElem? ecx sharing hi_n hsh_get] at hconv
    exact ih (Nat.le_of_lt hi_len) (Or.inl (Nat.le_refl _)) hconv hs

/-- Any `RawConvExpr` whose heap pointer satisfies `HeapExprScoped hSup nl 0 kp` at a super-heap
`hSup` reads to a closed expression with all level parameters in `List.range nl`. -/
theorem rawConvExpr_scoped_of_heapExprScoped
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {h₀ hSup : Heap F} {nl : Nat} {e : Ixon.Expr} {kp : SourceValue F} {E_rd : Core.KExpr}
    (raw : L1.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h₀ 4294967295 e kp)
    (ext : Heap.Extends h₀ hSup)
    (hread : (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read e = .ok E_rd)
    (hs : HeapExprScoped hSup nl 0 kp) :
    E_rd.looseBVarsBounded 0 = true ∧ E_rd.allLevelParamsDefined (List.range nl) = true := by
  obtain ⟨hecx, htbl⟩ := L1.memberReader_mk'_eq cx src id self
  unfold Ix.Kernel.Reader.MemberReader.read at hread
  rw [hecx, htbl, ← List.take_length (l := src.sharing.toList)] at hread
  exact rawConvExpr_scoped_of_heapExprScoped_go (by simp) ext raw (Nat.le_refl _) (Or.inr rfl)
    hread hs

end IxVM.Refinement.Typing.FamilyAlias
