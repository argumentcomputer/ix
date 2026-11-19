import IxVMRefinement.Binding.FamilyFlatRecord
import IxVMRefinement.Binding.FamilyReconAnswers

/-! # `build_flat_block` on a represented family record

`KernelCheck::build_flat_block` against its model over the canonical reading
(`FamilyFlatRecord.recordFlatAt`), function by function.

* `PeelTo`, `HeadOf`, `MajorConst`: the cells `peel_n_foralls` and `collect_spine` walk to reach
  the constant heading a recursor's major premise, as a relation on the heap alone. It is
  functional and preserved by heap extension, so the three readers of one recursor type
  (`rec_to_parent_addr`, `extract_aux_spec_params`, `extract_aux_occ_us`) read one head.
* `rec_to_parent_addr_major`, `extract_aux_occ_us_spec`,
  `extract_aux_spec_params_from_rec_spec`: the three readers.
* `aux_already_in_spec`: `KernelCheck::aux_already_in` is `FamilyFlat.auxEntryIn`.
* `indInfo_of_load`, `recMember_load`: the two loads of the walk against the store of a bounded
  run: a load at any address against `FamilyFlat.indInfoAt`, and the load of a recursor of the
  family record, whose type pointer represents the canonical reading (`FamilyFlat.loadedAt`)
  where the reading mentions only the recursor's level parameters (`RecLevelsDefined`).
* `walk_seg_spec`, `walk_prefix`, `aux_from_recrs_walk_ex_spec`: the walk is
  `FamilyFlatRecord.auxWalk` of the record's contributions.
* `param_lvls_range_spec`, `flat_originals_walk_spec`, `build_flat_originals_spec`: the types of a
  block of the store at an offset are `FamilyFlat.originals` of the block's members.
* `first_recr_parent_block_spec`, `primary_parent_block_of_spec`: the primary block is
  `FamilyFlatRecord.primaryAt`, a block record of the store.
* `build_flat_block_spec`: an observed `build_flat_block` returns `recordFlatAt`, represented
  exactly, as the primary block's types followed by auxiliary entries only;
  `build_flat_block_at_block` where the primary block is the block itself.
* `primaryAt_of_origHead`: the primary block is the block where the first recursor's major premise
  is over the block's first type. `recLevelsDefined_of_call`: `RecLevelsDefined` of the family
  record of an observed family check.

The circuit reads the major premise with `peel_n_foralls` and `collect_spine`, which do not step
through a `Let` cell, while the model reads the represented term, a `let` being its reduct. They
agree on every observed call: a reader that meets a `Let` cell where it needs a `Forall` or a
`Const` cell has no derivation (`rec_to_parent_addr` matches the head against `Const` alone), and
the two later readers are tied to the cells the first one walked (`MajorConst`).
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option autoImplicit false

namespace IxVM.Refinement.Binding.FamilyFlatBuild

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Consistency
open IxVM.Refinement.Binding.FamilyFlat
open IxVM.Refinement.Binding.FamilyOf
open IxVM.Refinement.Binding.FamilyFlatRecord
open IxVM.Refinement.Binding.FamilyRecon
open IxVM.Refinement.Typing
open IxVM.Refinement.Core (W KExpr KLevel KKey kexprEnum kexprListEnum addrTy ixAddr)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open IxVM (F)

/-! ## The cells a reader of the major premise walks -/

/-- The pointer `n` `Forall` cells below `p`, each step to the cell's body. -/
def PeelTo (h : Heap F) : Nat → SourceValue F → SourceValue F → Prop
  | 0, p, q => q = p
  | n + 1, p, q => ∃ d b l,
    loadValue h p = .ok (.construct kexprEnum "Forall" [d, b, l]) ∧ PeelTo h n b q

theorem PeelTo.mono {h h' : Heap F} (ext : Heap.Extends h h') :
    ∀ (n : Nat) {p q : SourceValue F}, PeelTo h n p q → PeelTo h' n p q
  | 0, _, _, hp => hp
  | n + 1, _, _, ⟨d, b, l, ld, hp⟩ => ⟨d, b, l, loadValue_mono ext ld, PeelTo.mono ext n hp⟩

theorem PeelTo.det {h : Heap F} :
    ∀ (n : Nat) {p q q' : SourceValue F}, PeelTo h n p q → PeelTo h n p q' → q = q'
  | 0, _, _, _, h1, h2 => h1.trans h2.symm
  | n + 1, _, _, _, ⟨d, b, l, ld, hp⟩, ⟨d', b', l', ld', hp'⟩ => by
    rw [ld] at ld'
    injection ld' with hv
    injection hv with _ _ hargs
    injection hargs with _ hargs
    injection hargs with hb _
    subst hb
    exact PeelTo.det n hp hp'

/-- **The cells peeled represent the term's leading binders.** -/
theorem PeelTo.sem {κ : _root_.Address → KKey} {h : Heap F} :
    ∀ (n : Nat) {p q : SourceValue F} {E : KExpr}, PeelTo h n p q → TmOExact κ h E p →
      ∃ E', peelForalls n E = some E' ∧ TmOExact κ h E' q
  | 0, _, _, E, hp, hE => ⟨E, rfl, by rw [show _ = _ from hp]; exact hE⟩
  | n + 1, _, _, E, ⟨d, b, l, ld, hp⟩, hE => by
    obtain ⟨T, B, ℓ, rfl, -, hb, -⟩ := hE.forallE_of_load ld
    obtain ⟨E', h1, h2⟩ := PeelTo.sem n hp hb
    exact ⟨E', by simp only [peelForalls]; exact h1, h2⟩

/-- **`KernelCheck::peel_n_foralls`** walks `n` `Forall` cells and allocates nothing. -/
theorem peel_n_foralls_peelTo :
    ∀ (n : Nat) {kp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 288230376151711744 →
      ObsFn W "KernelCheck::peel_n_foralls" [kp, .field (n : F)] h r h' cs →
      h' = h ∧ PeelTo h n kp r
  | 0, kp, r, h, h', cs, _, ev => by
    match Obs.«KernelCheck::peel_n_foralls».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh
      exact ⟨rfl, rfl⟩
    | .other (hne19 := hne) .. => exact (hne (by simp)).elim
  | n + 1, kp, r, h, h', cs, hlt, ev => by
    have hne0 : (.field ((n + 1 : Nat) : F) : SourceValue F) ≠ .field 0 := by
      intro he
      have hv := congrArg ZMod.val (Value.field.inj he)
      rw [FamilyOfCall.val_cast_lt_u58 hlt] at hv
      simp at hv
    match Obs.«KernelCheck::peel_n_foralls».obs ev with
    | .n0 (hv14 := hv) .. => exact (hne0 hv).elim
    | .other (v66 := v66) (ld34 := ld) (op87 := op) (ev64 := ev64) .. =>
      have hv66 : v66 = .field (n : F) := by
        simp only [evalBinOp, Except.ok.injEq] at op
        rw [← op]
        push_cast
        ring_nf
      subst hv66
      obtain ⟨hh, hp⟩ := peel_n_foralls_peelTo n (by omega) ev64
      exact ⟨hh, _, _, _, ld, hp⟩

/-- The head of the application spine at `p`: the first cell along the function positions that is
no `App`. -/
inductive HeadOf (h : Heap F) : SourceValue F → SourceValue F → Prop
  | here {p v : SourceValue F} (ld : loadValue h p = .ok v)
      (hne : ∀ vs : List (SourceValue F), vs.length = 2 → v ≠ .construct kexprEnum "App" vs) :
      HeadOf h p p
  | app {p f a hd : SourceValue F}
      (ld : loadValue h p = .ok (.construct kexprEnum "App" [f, a])) (hf : HeadOf h f hd) :
      HeadOf h p hd

theorem HeadOf.mono {h h' : Heap F} (ext : Heap.Extends h h') {p hd : SourceValue F}
    (hh : HeadOf h p hd) : HeadOf h' p hd := by
  induction hh with
  | here ld hne => exact .here (loadValue_mono ext ld) hne
  | app ld _ ih => exact .app (loadValue_mono ext ld) ih

theorem HeadOf.det {h : Heap F} {p hd hd' : SourceValue F} (h1 : HeadOf h p hd)
    (h2 : HeadOf h p hd') : hd = hd' := by
  induction h1 with
  | here ld hne =>
    cases h2 with
    | here _ _ => rfl
    | app ld' _ =>
      rw [ld] at ld'
      injection ld' with hv
      exact (hne _ rfl hv).elim
  | app ld hf ih =>
    cases h2 with
    | here ld' hne =>
      rw [ld] at ld'
      injection ld' with hv
      exact (hne _ rfl hv.symm).elim
    | app ld' hf' =>
      rw [ld] at ld'
      injection ld' with hv
      injection hv with _ _ hargs
      injection hargs with hfe _
      subst hfe
      exact ih hf'

/-- **A spine whose head cell is a constant represents that constant applied.** -/
theorem HeadOf.sem {κ : _root_.Address → KKey} {h : Heap F} {p hd xa xls : SourceValue F}
    (hh : HeadOf h p hd)
    (ldc : loadValue h hd = .ok (.construct kexprEnum "Const" [xa, xls])) :
    ∀ {E : KExpr}, TmOExact κ h E p →
      ∃ (a : Bytes.Address) (ls : List KLevel) (As : List KExpr),
        E = Ix.Kernel.Expr.mkAppN (.const (κ (ixAddr a)) ls) As ∧
        Bytes.RepAddressRef addrTy h a xa ∧ RepKLevelList h ls xls := by
  induction hh with
  | here ld hne =>
    intro E hE
    obtain ⟨a, ls, rfl, ra, rls⟩ := hE.const_of_load ldc
    exact ⟨a, ls, [], rfl, ra, rls⟩
  | app ld hf ih =>
    intro E hE
    obtain ⟨Ef, Ea, rfl, hEf, -⟩ := hE.app_of_load ld
    obtain ⟨a, ls, As, rfl, ra, rls⟩ := ih ldc hEf
    exact ⟨a, ls, As ++ [Ea], (IxVM.Refinement.Core.SubstAux.mkAppN_snoc As _ Ea).symm, ra, rls⟩

/-- **`KernelTypes::collect_spine`** returns the head of the spine. -/
theorem collect_spine_headOf {p hd sp : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelTypes::collect_spine" [p] h (.tuple [hd, sp]) h' cs) : HeadOf h p hd := by
  match Obs.«KernelTypes::collect_spine».obs ev with
  | .App (cs41 := cs41) (x_head := xh) (ld12 := ld) (ev43 := e1) (he69 := hr) (hc106 := hc) .. =>
    injection hr with hl
    injection hl with hhd _
    have hlt : cs41.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    rw [hhd]
    exact .app ld (collect_spine_headOf e1)
  | .other (ld12 := ld) (hne107 := hne) (he115 := hr) .. =>
    injection hr with hl
    injection hl with hhd _
    rw [hhd]
    exact .here ld hne
termination_by cs.length

/-- **The major premise of the type at `x_ty` is headed by a constant cell**: past `N` `Forall`
cells, the binder's domain `xm` has a spine whose head cell is `Const(xa, xls)`. -/
def MajorConst (h : Heap F) (x_ty : SourceValue F) (N : Nat) (xm xa xls : SourceValue F) : Prop :=
  ∃ q w1 w2 hd, PeelTo h N x_ty q ∧
    loadValue h q = .ok (.construct kexprEnum "Forall" [xm, w1, w2]) ∧ HeadOf h xm hd ∧
    loadValue h hd = .ok (.construct kexprEnum "Const" [xa, xls])

theorem MajorConst.mono {h h' : Heap F} (ext : Heap.Extends h h') {x_ty xm xa xls : SourceValue F}
    {N : Nat} (hM : MajorConst h x_ty N xm xa xls) : MajorConst h' x_ty N xm xa xls := by
  obtain ⟨q, w1, w2, hd, hp, ld, hh, ldc⟩ := hM
  exact ⟨q, w1, w2, hd, hp.mono ext N, loadValue_mono ext ld, hh.mono ext, loadValue_mono ext ldc⟩

/-- **What `MajorConst` says of the represented type**: its major premise's type is a constant
applied, the constant's address and levels the head cell's. -/
theorem MajorConst.sem {κ : _root_.Address → KKey} {h : Heap F} {x_ty xm xa xls : SourceValue F}
    {N : Nat} (hM : MajorConst h x_ty N xm xa xls) {ty : KExpr} (hty : TmOExact κ h ty x_ty) :
    ∃ (d : KExpr) (a : Bytes.Address) (ls : List KLevel) (As : List KExpr),
      binderDomAfter N ty = some d ∧
      d = Ix.Kernel.Expr.mkAppN (.const (κ (ixAddr a)) ls) As ∧ TmOExact κ h d xm ∧
      Bytes.RepAddressRef addrTy h a xa ∧ RepKLevelList h ls xls := by
  obtain ⟨q, w1, w2, hd, hp, ld, hh, ldc⟩ := hM
  obtain ⟨E', hpe, hE'⟩ := hp.sem N hty
  obtain ⟨T, B, ℓ, rfl, hT, -, -⟩ := hE'.forallE_of_load ld
  obtain ⟨a, ls, As, hTe, ra, rls⟩ := hh.sem ldc hT
  refine ⟨T, a, ls, As, ?_, hTe, hT, ra, rls⟩
  unfold binderDomAfter
  rw [hpe]

/-- A reader's `peel_n_foralls` reaches the major premise's binder. -/
theorem MajorConst.peel {h : Heap F} {x_ty xm xa xls : SourceValue F} {N : Nat}
    (hM : MajorConst h x_ty N xm xa xls) (hN : N < 288230376151711744)
    {p xm' w1 w2 : SourceValue F} {h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::peel_n_foralls" [x_ty, .field (N : F)] h p h' cs)
    (ld : loadValue h' p = .ok (.construct kexprEnum "Forall" [xm', w1, w2])) :
    h' = h ∧ xm' = xm := by
  obtain ⟨q, w1', w2', hd, hp, ldq, -, -⟩ := hM
  obtain ⟨hh, hp'⟩ := peel_n_foralls_peelTo N hN ev
  subst hh
  have hq := PeelTo.det N hp' hp
  subst hq
  rw [ldq] at ld
  injection ld with hv
  injection hv with _ _ hargs
  injection hargs with hx _
  exact ⟨rfl, hx.symm⟩

/-- A reader's `collect_spine` on the major premise's type returns the constant cell. -/
theorem MajorConst.head {h : Heap F} {x_ty xm xa xls : SourceValue F} {N : Nat}
    (hM : MajorConst h x_ty N xm xa xls)
    {hd sp : SourceValue F} {h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelTypes::collect_spine" [xm] h (.tuple [hd, sp]) h' cs) :
    loadValue h' hd = .ok (.construct kexprEnum "Const" [xa, xls]) := by
  obtain ⟨q, w1, w2, hd', -, -, hh, ldc⟩ := hM
  have he := HeadOf.det (collect_spine_headOf ev) hh
  rw [he]
  exact loadValue_mono ev.heap_extends ldc

/-- The sum of a recursor's four binder counts, as the circuit adds them. -/
theorem sum4_ok {a b c d : Nat} {x17 x9 v1 : SourceValue F}
    (op32 : evalBinOp .add (.field (a : F) : SourceValue F) (.field (b : F)) = .ok x17)
    (op24 : evalBinOp .add x17 (.field (c : F)) = .ok x9)
    (op16 : evalBinOp .add x9 (.field (d : F)) = .ok v1) :
    v1 = .field ((a + b + c + d : Nat) : F) := by
  simp only [evalBinOp, Except.ok.injEq] at op32
  subst op32
  simp only [evalBinOp, Except.ok.injEq] at op24
  subst op24
  simp only [evalBinOp, Except.ok.injEq] at op16
  rw [← op16]
  push_cast
  rfl

/-- **`KernelCheck::rec_to_parent_addr`** returns the address of the constant cell heading the
major premise's type (`MajorConst`). -/
theorem rec_to_parent_addr_major {np nmot nmin ni : Nat}
    (hN : np + nmot + nmin + ni < 288230376151711744)
    {x_ty r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::rec_to_parent_addr"
      [x_ty, .field (np : F), .field (nmot : F), .field (nmin : F), .field (ni : F)] h r h' cs) :
    Heap.Extends h h' ∧ ∃ xm xls, MajorConst h' x_ty (np + nmot + nmin + ni) xm r xls := by
  obtain ⟨v1, x9, x17, v37, m38, cs48, x_major_ty, w86, w87, m104, cs115, x_head, w132, x_caddr,
    w162, op32, op24, op16, ev50, ld78, ev117, ld154, hr_eq, hh_eq, _⟩ :=
    Obs.«KernelCheck::rec_to_parent_addr».obs ev
  subst hr_eq hh_eq
  have hv1 := sum4_ok op32 op24 op16
  subst hv1
  obtain ⟨hh, hp⟩ := peel_n_foralls_peelTo _ hN ev50
  subst hh
  have ext := ev117.heap_extends
  exact ⟨ext, x_major_ty, w162, v37, w86, w87, x_head, hp.mono ext _, loadValue_mono ext ld78,
    (collect_spine_headOf ev117).mono ext, ld154⟩

/-- The major premise's binder, as a reader's `peel_n_foralls` reaches it. -/
theorem MajorConst.peel_load {h : Heap F} {x_ty xm xa xls : SourceValue F} {N : Nat}
    (hM : MajorConst h x_ty N xm xa xls) (hN : N < 288230376151711744)
    {p : SourceValue F} {h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::peel_n_foralls" [x_ty, .field (N : F)] h p h' cs) :
    h' = h ∧ ∃ w1 w2, loadValue h p = .ok (.construct kexprEnum "Forall" [xm, w1, w2]) := by
  obtain ⟨q, w1', w2', hd, hp, ldq, -, -⟩ := hM
  obtain ⟨hh, hp'⟩ := peel_n_foralls_peelTo N hN ev
  have hq := PeelTo.det N hp' hp
  subst hq
  exact ⟨hh, w1', w2', ldq⟩

/-! ## The readers of an auxiliary's levels and parameters -/

/-- **`KernelCheck::extract_aux_occ_us`** on a recursor whose major premise is headed by a
constant cell (`MajorConst`) returns that cell's levels. -/
theorem extract_aux_occ_us_spec {np nmot nmin ni : Nat}
    (hN : np + nmot + nmin + ni < 288230376151711744)
    {x_ty xm xa xls w17 w18 w19 w20 w21 w22 r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (hM : MajorConst h x_ty (np + nmot + nmin + ni) xm xa xls)
    (ev : ObsFn W "KernelCheck::extract_aux_occ_us"
      [.construct "KernelTypes::KConstantInfo" "Rec"
        [w17, x_ty, .field (np : F), .field (ni : F), .field (nmot : F), .field (nmin : F),
          w18, w19, w20, w21, w22]] h r h' cs) :
    r = xls ∧ Heap.Extends h h' := by
  match Obs.«KernelCheck::extract_aux_occ_us».obs ev with
  | .Rec_Forall_Const (hv15 := hv) (op109 := o1) (op101 := o2) (op93 := o3) (ev131 := evP)
      (ld125 := ld) (ev185 := evS) (ld222 := ldc) (he242 := hr) (he243 := hh) .. =>
    have hargs := (Value.construct.inj hv).2.2
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl, -⟩ := hargs
    have hv1 := sum4_ok o1 o2 o3
    subst hv1
    obtain ⟨hm, hxm⟩ := hM.peel hN evP ld
    subst hm hxm
    have ldc' := hM.head evS
    rw [ldc'] at ldc
    injection ldc with hvv
    injection hvv with _ _ hl
    injection hl with _ hl
    injection hl with hus _
    rw [hr, hh]
    exact ⟨hus.symm, evS.heap_extends⟩
  | .Rec_Forall_other (hv15 := hv) (op109 := o1) (op101 := o2) (op93 := o3) (ev131 := evP)
      (ld125 := ld) (ev185 := evS) (ld222 := ldc) (hne245 := hne) .. =>
    have hargs := (Value.construct.inj hv).2.2
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl, -⟩ := hargs
    have hv1 := sum4_ok o1 o2 o3
    subst hv1
    obtain ⟨hm, hxm⟩ := hM.peel hN evP ld
    subst hm hxm
    have ldc' := hM.head evS
    rw [ldc'] at ldc
    injection ldc with hvv
    exact (hne _ rfl hvv.symm).elim
  | .Rec_other (hv15 := hv) (op109 := o1) (op101 := o2) (op93 := o3) (ev131 := evP)
      (ld125 := ld) (hne259 := hne) .. =>
    have hargs := (Value.construct.inj hv).2.2
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl, -⟩ := hargs
    have hv1 := sum4_ok o1 o2 o3
    subst hv1
    obtain ⟨hm, w1, w2, ldq⟩ := hM.peel_load hN evP
    subst hm
    rw [ldq] at ld
    injection ld with hvv
    exact (hne _ rfl hvv.symm).elim
  | .other (hne272 := hne) .. => exact (hne _ rfl rfl).elim

theorem repList_imp' {α : Type} {en : String} {R S : Heap F → α → SourceValue F → Prop}
    {h : Heap F} (hRS : ∀ x p, R h x p → S h x p) {xs : List α} {p : SourceValue F}
    (hl : RepList en R h xs p) : RepList en S h xs p := by
  induction hl with
  | nil cell => exact .nil cell
  | cons cell hx _ ih => exact .cons cell (hRS _ _ hx) ih

/-- **`KernelCheck::extract_aux_spec_params_from_rec`** on a recursor whose type is represented
exactly and whose major premise is headed by a constant cell: the major premise's first `pnp`
arguments, lowered past the motives, minors and indices (`FamilyFlat.occParamsLower`). -/
theorem extract_aux_spec_params_from_rec_spec {κ : _root_.Address → KKey}
    {np nmot nmin ni pnp : Nat}
    (hN : np + nmot + nmin + ni < 288230376151711744) (hpnp : pnp < 288230376151711744)
    {ty : KExpr} {x_ty xm xa xls w17 w18 w19 w20 w21 w22 r : SourceValue F} {h h' : Heap F}
    {cs root : List (Call F)}
    (hM : MajorConst h x_ty (np + nmot + nmin + ni) xm xa xls) (hty : TmOExact κ h ty x_ty)
    (ev : ObsFn W "KernelCheck::extract_aux_spec_params_from_rec"
      [.construct "KernelTypes::KConstantInfo" "Rec"
        [w17, x_ty, .field (np : F), .field (ni : F), .field (nmot : F), .field (nmin : F),
          w18, w19, w20, w21, w22], .field (pnp : F)] h r h' cs)
    (hbd : Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root) :
    Heap.Extends h h' ∧ ∃ d ys, binderDomAfter (np + nmot + nmin + ni) ty = some d ∧
      occParamsLower ((Ix.Kernel.Expr.getAppArgs d).take pnp) (nmot + nmin + ni) = some ys ∧
      RepList kexprListEnum (TmOExact κ) h' ys r := by
  match Obs.«KernelCheck::extract_aux_spec_params_from_rec».obs ev with
  | .other (hne133 := hne) .. => exact (hne _ rfl rfl).elim
  | .Rec (cs81 := cs81) (hv15 := hv) (ev83 := ev1) (hc132 := hc) .. =>
    have hargs := (Value.construct.inj hv).2.2
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl, -⟩ := hargs
    obtain ⟨v1, x9, x17, v37, m38, cs48, x_major_ty, w86, w87, m104, cs115, x__head, x_args,
      cs145, v148, v149, m151, cs159, x184, op32, op24, op16, ev50, ld78, ev117, ev161, op199,
      op191, ev147, hc203⟩ := Obs.«KernelCheck::extract_aux_spec_params».obs ev1
    have hv1 := sum4_ok op32 op24 op16
    subst hv1
    obtain ⟨hm, hxm⟩ := hM.peel hN ev50 ld78
    subst hm hxm
    obtain ⟨d, a, ls, As, hdom, hdeq, ⟨k, hd_tm⟩, -, -⟩ := hM.sem hty
    obtain ⟨hd, sp, H, As', htup, hH, hAs, hdE⟩ :=
      IxVM.Refinement.Decl.collect_spine_exact ev117 hd_tm
    injection htup with hl
    injection hl with h1 hl
    injection hl with h2 _
    subst h1 h2
    obtain ⟨a', ls', hHe, -, -⟩ := TmOExact.const_of_load ⟨k, hH⟩ (hM.head ev117)
    have hargsd : Ix.Kernel.Expr.getAppArgs d = As' := by
      rw [hdE, hHe, IxVM.Refinement.Decl.getAppArgs_mkAppN]
      rfl
    have hAs' : RepList kexprListEnum (TmOExact κ) m104 As' x_args :=
      repList_imp' (fun x p hx => ⟨k, hx⟩) hAs
    have hval : ((pnp : F)).val = pnp := FamilyOfCall.val_cast_lt_u58 hpnp
    have htake := Lib.Lists.take_spec (t := .ptr (.named "KernelTypes::KExprNode" []))
      (tmOExact_heapMono₂ (κ := κ))
      (by rw [Obs.Names.«Lists::take<&KernelTypes::KExprNode>».symbol]; exact ev161)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hAs')
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol, hval] at htake
    obtain ⟨-, htk⟩ := htake
    have hlow : v149 = .field ((nmot + nmin + ni : Nat) : F) := by
      simp only [evalBinOp, Except.ok.injEq] at op199
      subst op199
      simp only [evalBinOp, Except.ok.injEq] at op191
      rw [← op191]
      push_cast
      rfl
    subst hlow
    have bL : Bounded cs145 :=
      RomBound.bounded_mono hbd fun c hc' => by rw [hc, hc203]; simp [hc']
    obtain ⟨ext, ys, hys, hrep⟩ := spec_params_lower_spec (root := root) (by omega) _ htk ev147 bL
      (fun c hc' => hroot c (by rw [hc, hc203]; simp [hc']))
    refine ⟨ev117.heap_extends.trans (ev161.heap_extends.trans ext), d, ys, hdom, ?_, hrep⟩
    rw [hargsd]
    exact hys

/-! ## `aux_already_in` -/

theorem auxEntryIn_cons (e : FlatEntry) (es : List FlatEntry) (a : _root_.Address)
    (sp : List KExpr) (us : List KLevel) :
    auxEntryIn (e :: es) a sp us =
      ((e.aux && e.addr == a && e.params == sp && e.levels == us) || auxEntryIn es a sp us) := by
  simp [auxEntryIn]

theorem mul_ite_eq_one {P Q : Prop} [Decidable P] [Decidable Q] {v : SourceValue F}
    (op : evalBinOp .mul (.field (if P then 1 else 0) : SourceValue F)
      (.field (if Q then 1 else 0)) = .ok v) :
    v = .field 1 ↔ (P ∧ Q) := by
  simp only [evalBinOp, Except.ok.injEq] at op
  subst op
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

/-- **`KernelCheck::aux_already_in`** is `FamilyFlat.auxEntryIn`: whether an auxiliary entry has
the address, the parameters and the levels, on exactly represented entries at an injective
keying. -/
theorem aux_already_in_spec {κ : _root_.Address → KKey} (hinj : Function.Injective κ) :
    ∀ (acc : List FlatEntry) {a : Bytes.Address} {sp : List KExpr} {us : List KLevel}
      {xflat xa xsp xus r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelCheck::aux_already_in" [xflat, xa, xsp, xus] h r h' cs → Bounded cs →
      RepList flatListEnum (FlatEntryRepExact κ) h acc xflat →
      Bytes.RepAddressRef addrTy h a xa →
      RepList kexprListEnum (TmOExact κ) h sp xsp → RepKLevelList h us xus →
      r = .field (if auxEntryIn acc (ixAddr a) sp us then 1 else 0) ∧ Heap.Extends h h' := by
  intro acc
  induction acc with
  | nil =>
    intro a sp us xflat xa xsp xus r h h' cs ev _ hes _ _ _
    match Obs.«KernelCheck::aux_already_in».obs ev with
    | .Nil (he20 := hr) (he21 := hh) .. =>
      rw [hr, hh]
      exact ⟨rfl, Heap.Extends.refl _⟩
    | .Cons_n1_n1_n1 (ld12 := ld) .. | .Cons_n1_n1_other (ld12 := ld) ..
    | .Cons_n1_other (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hcons
  | cons e es ih =>
    intro a sp us xflat xa xsp xus r h h' cs ev hbd hes ra rsp rus
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → Bounded cs' :=
      fun hs => RomBound.bounded_mono hbd hs
    match Obs.«KernelCheck::aux_already_in».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    | .Cons_other (ld12 := ld) (hne233 := hne) (ev242 := evR) (hc267 := hc) .. =>
      obtain ⟨e', es', h1, he', hes'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with he1 hes1
      subst he1 hes1
      obtain ⟨xm', xsp', xou', ae, htup, rae, hae, hsp, hou⟩ := he'
      injection htup with hl
      injection hl with h1 hl
      injection hl with h2 hl
      have haux : e.aux = false := by
        cases hx : e.aux with
        | false => rfl
        | true => exact (hne (h2.trans (auxVal_eq_one.mpr hx))).elim
      obtain ⟨hr, ext⟩ := ih evR (sub fun c hc' => by rw [hc]; simp [hc']) hes' ra rsp rus
      refine ⟨?_, ext⟩
      rw [hr, auxEntryIn_cons, haux]
      simp
    | .Cons_n1_other (ld12 := ld) (ev104 := evA) (hne198 := hne) (ev207 := evR)
        (hc232 := hc) .. =>
      obtain ⟨e', es', h1, he', hes'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with he1 hes1
      subst he1 hes1
      obtain ⟨xm', xsp', xou', ae, htup, rae, hae, hsp, hou⟩ := he'
      injection htup with hl
      injection hl with h1 hl
      subst h1
      obtain ⟨hv, hm⟩ := Lib.address_eq_spec evA rae ra
      subst hm
      have hna : e.addr ≠ ixAddr a := by
        intro heq
        have : ae = a := ixAddr_inj (hae.trans heq)
        rw [ite_eq_left this] at hv
        exact hne hv
      obtain ⟨hr, ext⟩ := ih evR (sub fun c hc' => by rw [hc]; simp [hc']) hes' ra rsp rus
      refine ⟨?_, ext⟩
      rw [hr, auxEntryIn_cons, beq_eq_false_iff_ne.mpr hna]
      simp
    | .Cons_n1_n1_other (ld12 := ld) (ev104 := evA) (ev_bdqzbgud := evZ) (ev_purmzcuq := evL)
        (op_irtiosum := op) (hne163 := hne) (ev172 := evR) (hc197 := hc) .. =>
      obtain ⟨e', es', h1, he', hes'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with he1 hes1
      subst he1 hes1
      obtain ⟨xm', xsp', xou', ae, htup, rae, hae, hsp, hou⟩ := he'
      injection htup with hl
      injection hl with h1 hl
      injection hl with h2 hl
      injection hl with h3 hl
      injection hl with h4 _
      subst h1 h3 h4
      obtain ⟨-, hm⟩ := Lib.address_eq_spec evA rae ra
      subst hm
      have hx := spec_params_zeta_eq_exact hinj hsp rsp
        (sub fun c hc' => by rw [hc]; simp [hc']) evZ
      have ext1 := evZ.heap_extends
      obtain ⟨hy, hm2⟩ := level_list_struct_eq_exact (hou.mono ext1) (rus.mono ext1) evL
      subst hm2 hx hy
      have hnot := (not_congr (mul_ite_eq_one op)).mp hne
      obtain ⟨hr, ext⟩ := ih evR (sub fun c hc' => by rw [hc]; simp [hc'])
        (flatList_mono ext1 hes') (Bytes.repAddressRef_heapMono₂ addrTy ext1 ra)
        (tmOExactList_mono ext1 rsp) (rus.mono ext1)
      refine ⟨?_, ext1.trans ext⟩
      have hb : (e.params == sp && e.levels == us) = false := by
        cases hb : (e.params == sp && e.levels == us) with
        | false => rfl
        | true =>
          simp only [Bool.and_eq_true, beq_iff_eq] at hb
          exact (hnot hb).elim
      rw [hr, auxEntryIn_cons, Bool.and_assoc, hb]
      simp
    | .Cons_n1_n1_n1 (ld12 := ld) (ev104 := evA) (ev_bdqzbgud := evZ) (ev_purmzcuq := evL)
        (op_irtiosum := op) (he160 := hr) (he161 := hh) (hc162 := hc) .. =>
      obtain ⟨e', es', h1, he', hes'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with he1 hes1
      subst he1 hes1
      obtain ⟨xm', xsp', xou', ae, htup, rae, hae, hsp, hou⟩ := he'
      injection htup with hl
      injection hl with h1 hl
      injection hl with h2 hl
      injection hl with h3 hl
      injection hl with h4 _
      subst h1 h3 h4
      have haux : e.aux = true := auxVal_eq_one.mp h2.symm
      obtain ⟨hv, hm⟩ := Lib.address_eq_spec evA rae ra
      subst hm
      have hae' : ae = a := by
        by_contra hna
        rw [ite_eq_right hna] at hv
        exact absurd (Value.field.inj hv) (by decide)
      have hx := spec_params_zeta_eq_exact hinj hsp rsp
        (sub fun c hc' => by rw [hc]; simp [hc']) evZ
      have ext1 := evZ.heap_extends
      obtain ⟨hy, hm2⟩ := level_list_struct_eq_exact (hou.mono ext1) (rus.mono ext1) evL
      subst hm2 hx hy
      obtain ⟨hp, hl⟩ := (mul_ite_eq_one op).mp rfl
      rw [hr, hh]
      refine ⟨?_, ext1⟩
      rw [auxEntryIn_cons, haux, ← hae, hae', hp, hl]
      simp

/-! ## The loads of the walk, against the store -/

section Run

variable {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}

/-- **A load of a run against the store's reading of an inductive type** (`indInfoAt`): among
the calls of a bounded run with its store, a load that returns an `Induct` is the store's
inductive at the address, with its level and parameter counts and its block; a load that returns
another constant is a record of another kind. -/
theorem indInfo_of_load (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀) (hbd : Bounded calls)
    {xa p ci : SourceValue F} {h m : Heap F} {cs : List (Call F)} {a : Bytes.Address}
    (ha : Bytes.RepAddressRef addrTy h a xa)
    (ev : ObsFn W "Ingress::get_ci" [xa] h p m cs) (hsub : ∀ c ∈ cs, c ∈ calls)
    (hld : loadValue m p = .ok ci) :
    (∀ xnl xty xnp xni xnc xrec xblk xidx,
      ci = .construct "KernelTypes::KConstantInfo" "Induct"
        [xnl, xty, xnp, xni, xnc, xrec, xblk, xidx] →
      ∃ (i : IndInfo) (ba : Bytes.Address),
        indInfoAt E₀ (ixAddr a) = some (some i) ∧
        i.nl < 4294967296 ∧ i.np < 72057594037927936 ∧
        xnl = .field (i.nl : F) ∧ xnp = .field (i.np : F) ∧
        ixAddr ba = i.blk ∧ Bytes.RepAddressRef addrTy m ba xblk) ∧
    ((∀ vs : List (SourceValue F), vs.length = 8 →
        ci ≠ .construct "KernelTypes::KConstantInfo" "Induct" vs) →
      indInfoAt E₀ (ixAddr a) = some none) := by
  obtain ⟨c, hrec, raw⟩ := Guard.get_ci_rawCIRep_runStore hS hH
    (Guard.loadParentsHeld_of_runStore hS hH) (RomBound.bounded_mono hbd hsub) hsub ha ev hld
  by_cases hip : ∃ ip, c.info = .iPrj ip
  · obtain ⟨ip, hinfo⟩ := hip
    have raw' := raw
    unfold L1.RawCIRep at raw'
    rw [hinfo] at raw'
    obtain ⟨-, lcB, cb, ms, ind, blobs, -, -, hrecB, -, -, hcb, hm, -, hraw⟩ := raw'
    have hrecB' : recordOf E₀ ip.block = some cb := hS.recordOf_of_recordAt hrecB
    have hmem : ms[ip.idx.toNat]? = some (.indc ind) := by
      rw [← Array.getElem?_toList]; exact hm
    obtain ⟨hl, hnp, hni, hnc, hii, tyPtr, blkPtr, b, hbaddr, hbrep, hv, rty⟩ := hraw
    have hdata := indInfoAt_of_iPrj hrec hinfo hrecB' hcb hmem
    constructor
    · intro xnl xty xnp xni xnc xrec xblk xidx hci
      rw [hci] at hv
      have hargs := (Value.construct.inj hv).2.2
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨e1, e2, e3, e4, e5, -, e7, e8⟩ := hargs
      exact ⟨_, b, hdata, hl, hnp, e1, e3, hbaddr, e7 ▸ hbrep⟩
    · intro hne
      exact absurd hv (hne _ rfl)
  · constructor
    · intro xnl xty xnp xni xnc xrec xblk xidx hci
      rw [hci] at raw
      have htag := rawCIRep_tag raw
      cases hinfo : c.info with
      | iPrj ip => exact absurd ⟨ip, hinfo⟩ hip
      | defn d => rw [hinfo] at htag; simp at htag
      | dPrj _ => rw [hinfo] at htag; simp at htag
      | axio _ => rw [hinfo] at htag; simp at htag
      | quot _ => rw [hinfo] at htag; simp at htag
      | recr _ => rw [hinfo] at htag; simp at htag
      | rPrj _ => rw [hinfo] at htag; simp at htag
      | cPrj _ => rw [hinfo] at htag; simp at htag
      | muts _ => rw [hinfo] at htag; exact htag.elim
    · intro _
      unfold indInfoAt
      rw [hrec]
      cases hinfo : c.info with
      | iPrj ip => exact absurd ⟨ip, hinfo⟩ hip
      | _ => simp only [hinfo]

/-- **The types of a family record's recursors mention only their own level parameters**: the
reading of recursor `k`'s type over the store's blobs mentions no level parameter at or above
its level count. -/
def RecLevelsDefined (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (rb : _root_.Address)
    (crb : Ixon.Constant) (rs : Array Ixon.MutConst) : Prop :=
  ∀ (k : Nat) (rc : Ixon.Recursor) (v : KExpr), rs[k]? = some (.recr rc) →
    (exprReader t (fun x => E.blobs.get? x) crb id (blockSelf t rb rs)).read rc.typ = .ok v →
    v.allLevelParamsDefined (List.range rc.lvls.toNat) = true

/-- **A load of a run at a recursor of a family record**: among the calls of a bounded run with
its store, the load at the projection address of member `k` returns a `Rec` with the recursor's
counts and a type pointer representing, exactly and open, the canonical reading of its type
(`FamilyFlat.loadedAt`). -/
theorem recMember_load (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hR : FamRecRecord E₀ rb crb rs) (hlv : RecLevelsDefined t E₀ rb crb rs)
    {k : Nat} {rc : Ixon.Recursor} (hk_u64 : k < UInt64.size) (hrk : rs[k]? = some (.recr rc))
    {xa p ci : SourceValue F} {h m : Heap F} {cs : List (Call F)} {aRec : Bytes.Address}
    (haRec_eq : ixAddr aRec = IxVM.Refinement.Core.rprjAddr rb k)
    (ha : Bytes.RepAddressRef addrTy h aRec xa)
    (ev : ObsFn W "Ingress::get_ci" [xa] h p m cs) (hsub : ∀ c ∈ cs, c ∈ calls)
    (hld : loadValue m p = .ok ci) :
    ∃ (ty : KExpr) (xty w1 w2 w3 w4 w5 : SourceValue F),
      ci = .construct "KernelTypes::KConstantInfo" "Rec"
        [.field (rc.lvls.toNat : F), xty, .field (rc.params.toNat : F),
          .field (rc.indices.toNat : F), .field (rc.motives.toNat : F),
          .field (rc.minors.toNat : F), w1, w2, w3, w4, w5] ∧
      loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
        (mutsRoot rs k) rc.typ = some ty ∧
      TmOExact (keyOf t) m ty xty ∧
      rc.params.toNat < 72057594037927936 ∧ rc.indices.toNat < 72057594037927936 ∧
      rc.motives.toNat < 72057594037927936 ∧ rc.minors.toNat < 72057594037927936 := by
  obtain ⟨_, cRec, hhRec, hbaRec, hexRec, -, htrRec⟩ :=
    L1.get_ci_block_trace_spec (RomBound.bounded_mono hbd hsub) ha ev
  have hrecAtRec : Ix.Cert.recordAt E₀ (ixAddr aRec) =
      some (memberProjection rb k (.recr rc)) := by
    rw [← hS.recordOf_eq_recordAt, haRec_eq, ← LoadedReads.memberAddr_recr]
    exact hR.members k (.recr rc) hrk
  have hcRec_eq : cRec = memberProjection rb k (.recr rc) :=
    hS.record_eq hrecAtRec (IxVM.Refinement.Core.hashed_mono hsub hhRec) hbaRec hexRec
  subst hcRec_eq
  unfold L1.GetCIBlockTraceResult at htrRec
  simp only [memberProjection] at htrRec
  obtain ⟨_, _, crb', rs', rc', blobs, tree, vRec, hhBlk, hbaBlk, hexBlk, hmuts', hrk', hhp,
      built, hldv, hrepRec⟩ := htrRec
  have hcrb_eq : crb' = crb :=
    hS.record_eq ((hS.recordOf_eq_recordAt rb).symm.trans hR.record)
      (IxVM.Refinement.Core.hashed_mono hsub hhBlk) hbaBlk hexBlk
  subst crb'
  have hrs_eq : rs' = rs := Ixon.ConstantInfo.muts.inj (hmuts'.symm.trans hR.muts)
  subst rs'
  have hk_toNat : k.toUInt64.toNat = k := toUInt64_toNat_of_lt hk_u64
  rw [hk_toNat, Array.getElem?_toList, hrk] at hrk'
  have hrc_eq : rc' = rc := Ixon.MutConst.recr.inj (Option.some.inj hrk').symm
  subst rc'
  rw [hk_toNat] at hrepRec
  obtain ⟨hlvls_lt, hnp_lt, hni_lt, hnmot_lt, hnmin_lt, hk_lt, tyPtr, rulesPtr, blkPtr, bBlk,
      planT, hbBlk_eq, hbBlk_ref, hvRec_eq, rty, hpT, hlT, hrlsTrace⟩ := hrepRec
  have hci : vRec = ci := Except.ok.inj (hldv.symm.trans hld)
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hrun := hS.blobs bs (IxVM.Refinement.Core.hashed_mono hsub hhx)
    rwa [hxa] at hrun
  obtain ⟨tyA, hloaded, htm⟩ := loadedAt_tmOExact (t := t) (blob := fun x => E₀.blobs.get? x)
    (self := blockSelf t rb rs) (recurAddrs := []) ht hlvls_lt
    (fun _ _ _ _ hx => by simp at hx) (fun _ _ hx => by simp at hx) hblob rty built hpT hlT
    (fun v hv => hlv k rc v hrk hv)
  exact ⟨tyA, tyPtr, _, _, _, _, _, hci ▸ hvRec_eq, hloaded, htm, hnp_lt, hni_lt, hnmot_lt,
    hnmin_lt⟩

/-! ## The walk over the recursors -/

theorem getAppFn_const_mkAppN (k : KKey) (ls : List KLevel) (As : List KExpr) :
    Ix.Kernel.Expr.getAppFn (Ix.Kernel.Expr.mkAppN (.const k ls) As) = .const k ls := by
  rw [IxVM.Refinement.Decl.getAppFn_mkAppN]
  rfl

/-- What a major premise headed by the constant at `a` adds, when the store reads no inductive
type at `a` or one of the primary block: nothing. -/
theorem auxOfMajor_none (htwf : t.wf = true) {prim a : _root_.Address} {ls : List KLevel}
    {As : List KExpr} {low : Nat} {x : Option IndInfo}
    (hci : indInfoAt E₀ a = some x) (hx : ∀ i, x = some i → i.blk = prim) :
    auxOfMajor (FlatView.ofStore t E₀) prim low
      (Ix.Kernel.Expr.mkAppN (.const (keyOf t a) ls) As) = some none := by
  have hadr : (FlatView.ofStore t E₀).addr (keyOf t a) = some a := keyAddr_keyOf htwf a
  have hci' : (FlatView.ofStore t E₀).ci a = some x := hci
  cases x with
  | none => simp only [auxOfMajor, getAppFn_const_mkAppN, constOf, hadr, hci']
  | some i =>
    have hdec : decide (i.blk = prim) = true := decide_eq_true (hx i rfl)
    simp only [auxOfMajor, getAppFn_const_mkAppN, constOf, hadr, hci', hdec]

/-- What a major premise headed by an inductive type outside the primary block adds: its entry at
the head's levels and the lowered parameters. -/
theorem auxOfMajor_some (htwf : t.wf = true) {prim a : _root_.Address} {ls : List KLevel}
    {As ys : List KExpr} {low : Nat} {i : IndInfo}
    (hci : indInfoAt E₀ a = some (some i)) (hblk : i.blk ≠ prim)
    (hys : occParamsLower ((Ix.Kernel.Expr.getAppArgs
      (Ix.Kernel.Expr.mkAppN (.const (keyOf t a) ls) As)).take i.np) low = some ys) :
    auxOfMajor (FlatView.ofStore t E₀) prim low
      (Ix.Kernel.Expr.mkAppN (.const (keyOf t a) ls) As) = some (some ⟨a, true, ys, ls⟩) := by
  have hadr : (FlatView.ofStore t E₀).addr (keyOf t a) = some a := keyAddr_keyOf htwf a
  have hci' : (FlatView.ofStore t E₀).ci a = some (some i) := hci
  have hdec : decide (i.blk = prim) = false := decide_eq_false hblk
  simp only [auxOfMajor, getAppFn_const_mkAppN, constOf, hadr, hci', hdec, hys]

/-- **The walk's classification of one recursor** (`entry_opt`): on a recursor's loaded payload
whose type is represented exactly, the major premise's type is a constant applied, whose address
the classification returns; it is flagged (`b`) exactly when the store reads at that address an
inductive type outside the primary block, and then with that type's parameter count. -/
theorem walk_seg_spec (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {ty : KExpr} {np nmot nmin ni : Nat}
    (hN : np + nmot + nmin + ni < 288230376151711744)
    {x_ty w0 w1 w2 w3 w4 w5 xwrap xm xrest xall xcur xrb xprim xuo xacc xpos res : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} {prim : Bytes.Address}
    (hty : TmOExact (keyOf t) h ty x_ty) (hprim : Bytes.RepAddressRef addrTy h prim xprim)
    (sg : Obs.«KernelCheck::aux_from_recrs_walk_ex».SegX1
      (.construct "KernelTypes::KConstantInfo" "Rec"
        [w0, x_ty, .field (np : F), .field (ni : F), .field (nmot : F), .field (nmin : F),
          w1, w2, w3, w4, w5])
      xwrap xm xrest xall xcur xrb xprim xuo xacc xpos h res h' cs)
    (hsub : ∀ c ∈ cs, c ∈ calls) :
    Heap.Extends h h' ∧
    ∃ (d : KExpr) (a : Bytes.Address) (ls : List KLevel) (As : List KExpr)
      (xmaj xpar xls w xpnp xpnl : SourceValue F) (b : Bool),
      res = .tuple [.field (if b then 1 else 0), xpar, w, xpnp, xpnl] ∧
      binderDomAfter (np + nmot + nmin + ni) ty = some d ∧
      d = Ix.Kernel.Expr.mkAppN (.const (keyOf t (ixAddr a)) ls) As ∧
      MajorConst h' x_ty (np + nmot + nmin + ni) xmaj xpar xls ∧
      Bytes.RepAddressRef addrTy h' a xpar ∧ RepKLevelList h' ls xls ∧
      (b = false → ∀ low,
        auxOfMajor (FlatView.ofStore t E₀) (ixAddr prim) low d = some none) ∧
      (b = true → ∃ i : IndInfo, indInfoAt E₀ (ixAddr a) = some (some i) ∧
        i.blk ≠ ixAddr prim ∧ xpnp = .field (i.np : F) ∧ i.np < 72057594037927936) := by
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  match sg with
  | .other (hne513 := hne) .. => exact (hne _ rfl rfl).elim
  | .Rec_Induct_n1 (cs214 := cs214) (cs271 := cs271) (hv140 := hv) (ev216 := evP) (ev273 := evG)
      (ld267 := ld) (ev357 := evA) (he385 := hr) (he419 := hh) (hc420 := hc) .. =>
    have hargs := (Value.construct.inj hv).2.2
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl, -⟩ := hargs
    obtain ⟨ext1, xmaj, xls, hM⟩ := rec_to_parent_addr_major hN evP
    obtain ⟨d, a, ls, As, hdom, hdeq, -, ra, rls⟩ := hM.sem (hty.mono ext1)
    have hsubG : ∀ c ∈ cs271, c ∈ calls := fun c hc' => hsub c (by rw [hc]; simp [hc'])
    obtain ⟨i, ba, hinfo, hnl, hnpb, e1, e3, hba, rba⟩ :=
      (indInfo_of_load hS hH hbd ra evG hsubG ld).1 _ _ _ _ _ _ _ _ rfl
    have ext2 := evG.heap_extends
    obtain ⟨hv1, hm⟩ := Lib.address_eq_spec evA rba
      (Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans ext2) hprim)
    have hbp : ba = prim := by
      by_contra hna
      rw [ite_eq_right hna] at hv1
      exact absurd (Value.field.inj hv1) (by decide)
    subst hm hh
    refine ⟨ext1.trans ext2, d, a, ls, As, xmaj, _, xls, _, _, _, false, hr, hdom, hdeq,
      hM.mono ext2, Bytes.repAddressRef_heapMono₂ addrTy ext2 ra, rls.mono ext2, ?_, ?_⟩
    · intro _ low
      rw [hdeq]
      exact auxOfMajor_none htwf hinfo (fun j hj => by
        cases hj
        rw [← hba, hbp])
    · intro hb
      cases hb
  | .Rec_Induct_other (cs214 := cs214) (cs271 := cs271) (hv140 := hv) (ev216 := evP)
      (ev273 := evG) (ld267 := ld) (ev357 := evA) (hne421 := hne) (he432 := hr) (he466 := hh)
      (hc467 := hc) .. =>
    have hargs := (Value.construct.inj hv).2.2
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl, -⟩ := hargs
    obtain ⟨ext1, xmaj, xls, hM⟩ := rec_to_parent_addr_major hN evP
    obtain ⟨d, a, ls, As, hdom, hdeq, -, ra, rls⟩ := hM.sem (hty.mono ext1)
    have hsubG : ∀ c ∈ cs271, c ∈ calls := fun c hc' => hsub c (by rw [hc]; simp [hc'])
    obtain ⟨i, ba, hinfo, hnl, hnpb, e1, e3, hba, rba⟩ :=
      (indInfo_of_load hS hH hbd ra evG hsubG ld).1 _ _ _ _ _ _ _ _ rfl
    have ext2 := evG.heap_extends
    obtain ⟨hv1, hm⟩ := Lib.address_eq_spec evA rba
      (Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans ext2) hprim)
    have hbp : ba ≠ prim := by
      intro heq
      rw [ite_eq_left heq] at hv1
      exact hne hv1
    subst hm hh
    refine ⟨ext1.trans ext2, d, a, ls, As, xmaj, _, xls, _, _, _, true, hr, hdom, hdeq,
      hM.mono ext2, Bytes.repAddressRef_heapMono₂ addrTy ext2 ra, rls.mono ext2, ?_, ?_⟩
    · intro hb
      cases hb
    · intro _
      exact ⟨i, hinfo, fun heq => hbp (ixAddr_inj (hba.trans heq)), e3, hnpb⟩
  | .Rec_other (cs214 := cs214) (cs271 := cs271) (hv140 := hv) (ev216 := evP) (ev273 := evG)
      (ld267 := ld) (hne468 := hne) (he479 := hr) (he511 := hh) (hc512 := hc) .. =>
    have hargs := (Value.construct.inj hv).2.2
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl, -⟩ := hargs
    obtain ⟨ext1, xmaj, xls, hM⟩ := rec_to_parent_addr_major hN evP
    obtain ⟨d, a, ls, As, hdom, hdeq, -, ra, rls⟩ := hM.sem (hty.mono ext1)
    have hsubG : ∀ c ∈ cs271, c ∈ calls := fun c hc' => hsub c (by rw [hc]; simp [hc'])
    have hinfo := (indInfo_of_load hS hH hbd ra evG hsubG ld).2 hne
    have ext2 := evG.heap_extends
    subst hh
    refine ⟨ext1.trans ext2, d, a, ls, As, xmaj, _, xls, _, _, _, false, hr, hdom, hdeq,
      hM.mono ext2, Bytes.repAddressRef_heapMono₂ addrTy ext2 ra, rls.mono ext2, ?_, ?_⟩
    · intro _ low
      rw [hdeq]
      exact auxOfMajor_none htwf hinfo (fun j hj => by cases hj)
    · intro hb
      cases hb

private abbrev flatEntryTy : Generic.Ty :=
  .tuple [.ptr (.array .field 32), .field,
    .ptr (.named "Lists::Node" [.ptr (.named "KernelTypes::KExprNode" [])]),
    .ptr (.named "Lists::Node" [.ptr (.named "KernelTypes::KLevelNode" [])])]

private theorem flatListEnum_eq :
    (Instance.mk "Lists::Node" [flatEntryTy]).symbol = flatListEnum :=
  Obs.Names.«Lists::Node<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol

theorem keyOf_injective' (htwf : t.wf = true) : Function.Injective (keyOf t) :=
  fun _ _ h => IxVM.Refinement.Core.keyOf_inj htwf h

/-- **One recursor of the walk, up to its classification**: the projection address of member `k`,
its load and `entry_opt`. The recursor's type is represented exactly; its major premise's type
`d` is a constant applied; what the recursor adds in the model (`contribAt`) is `auxOfMajor` of
`d`; and the classification's flag and counts are as `walk_seg_spec` gives them. -/
theorem walk_prefix (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hR : FamRecRecord E₀ rb crb rs) (hlv : RecLevelsDefined t E₀ rb crb rs)
    (hrs_lt : rs.size < 8589934592) {bR prim : Bytes.Address} (hbR : ixAddr bR = rb)
    {k : Nat} {rc : Ixon.Recursor} (hrk : rs[k]? = some (.recr rc))
    {x_all x_rb x_prim x_uo x_cur x_acc xm xrest xpos v63 p109 v101 res : SourceValue F}
    {h m64 m102 m559 : Heap F} {cs74 cs115 cs561 : List (Call F)}
    (hall : RepList L1.mutConstListEnum L1.RepMutConst h rs.toList x_all)
    (hrb : Bytes.RepAddressRef addrTy h bR x_rb)
    (hprim : Bytes.RepAddressRef addrTy h prim x_prim)
    (ev76 : ObsFn W "Ingress::projection_addr" [x_all, x_rb, .field (k : F)] h v63 m64 cs74)
    (ev117 : ObsFn W "Ingress::get_ci" [v63] m64 p109 m102 cs115)
    (ld111 : loadValue m102 p109 = .ok v101)
    (sg : Obs.«KernelCheck::aux_from_recrs_walk_ex».SegX1 v101 v63 xm xrest x_all x_cur x_rb
      x_prim x_uo x_acc xpos m102 res m559 cs561)
    (hsub115 : ∀ c ∈ cs115, c ∈ calls) (hsub561 : ∀ c ∈ cs561, c ∈ calls) :
    Heap.Extends h m559 ∧
    ∃ (ty d : KExpr) (a : Bytes.Address) (ls : List KLevel) (As : List KExpr)
      (x_ty w0 w1 w2 w3 w4 w5 xmaj xpar xls w xpnp xpnl : SourceValue F) (b : Bool),
      v101 = .construct "KernelTypes::KConstantInfo" "Rec"
        [w0, x_ty, .field (rc.params.toNat : F), .field (rc.indices.toNat : F),
          .field (rc.motives.toNat : F), .field (rc.minors.toNat : F), w1, w2, w3, w4, w5] ∧
      res = .tuple [.field (if b then 1 else 0), xpar, w, xpnp, xpnl] ∧
      rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat <
        288230376151711744 ∧
      TmOExact (keyOf t) m559 ty x_ty ∧
      binderDomAfter (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
        ty = some d ∧
      d = Ix.Kernel.Expr.mkAppN (.const (keyOf t (ixAddr a)) ls) As ∧
      MajorConst m559 x_ty
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) xmaj xpar xls ∧
      Bytes.RepAddressRef addrTy m559 a xpar ∧ RepKLevelList m559 ls xls ∧
      contribAt t E₀ rb crb rs (ixAddr prim) k =
        auxOfMajor (FlatView.ofStore t E₀) (ixAddr prim)
          (rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) d ∧
      (b = false → ∀ low,
        auxOfMajor (FlatView.ofStore t E₀) (ixAddr prim) low d = some none) ∧
      (b = true → ∃ i : IndInfo, indInfoAt E₀ (ixAddr a) = some (some i) ∧
        i.blk ≠ ixAddr prim ∧ xpnp = .field (i.np : F) ∧ i.np < 72057594037927936) := by
  have hklt : k < rs.size := (Array.getElem?_eq_some_iff.mp hrk).1
  have hkval : ((k : F)).val = k := FamilyOfCall.val_cast_lt_u58 (by omega)
  obtain ⟨ext1, -, -, mc, aW, hget, haW, haW_eq⟩ :=
    L1.projection_addr_spec (Route.membersRep_of_repMutConstList hall) hrb ev76
  rw [hkval, Array.getElem?_toList, hrk] at hget
  have hmc : mc = .recr rc := (Option.some.inj hget).symm
  subst hmc
  rw [hkval, hbR, ← LoadedReads.memberAddr_eq_projAddr, LoadedReads.memberAddr_recr] at haW_eq
  obtain ⟨ty, x_ty, w1, w2, w3, w4, w5, hci, hloaded, htm, hnp, hni, hnmot, hnmin⟩ :=
    recMember_load ht hbd hS hR hlv (Nat.lt_trans hklt (Nat.lt_trans hrs_lt (by decide))) hrk
      haW_eq haW ev117 hsub115 ld111
  subst hci
  have hN : rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat <
      288230376151711744 := by omega
  have ext2 := ev117.heap_extends
  obtain ⟨ext3, d, a, ls, As, xmaj, xpar, xls, w, xpnp, xpnl, b, hres, hdom, hdeq, hM, ra, rls,
    hb0, hb1⟩ := walk_seg_spec ht hbd hS hH hN htm
      (Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans ext2) hprim) sg hsub561
  refine ⟨ext1.trans (ext2.trans ext3), ty, d, a, ls, As, x_ty, _, w1, w2, w3, w4, w5, xmaj, xpar,
    xls, w, xpnp, xpnl, b, rfl, hres, hN, htm.mono ext3, hdom, hdeq, hM, ra, rls, ?_, hb0, hb1⟩
  simp only [contribAt, majorAt, hrk, hloaded, hdom]

/-- **`KernelCheck::aux_from_recrs_walk_ex`** over the recursors from position `k` is
`FamilyFlatRecord.auxWalk` of the record's contributions (`contribAt`): each recursor's auxiliary
appended unless already an entry. -/
theorem aux_from_recrs_walk_ex_spec (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hR : FamRecRecord E₀ rb crb rs) (hlv : RecLevelsDefined t E₀ rb crb rs)
    (hrs_lt : rs.size < 8589934592) {bR prim : Bytes.Address} (hbR : ixAddr bR = rb)
    {x_all x_rb x_prim x_uo : SourceValue F} :
    ∀ (cur : List Ixon.MutConst) (k : Nat) (acc : List FlatEntry)
      {x_cur x_acc r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      (∀ j m, cur[j]? = some m → rs[k + j]? = some m) →
      RepList L1.mutConstListEnum L1.RepMutConst h rs.toList x_all →
      RepList L1.mutConstListEnum L1.RepMutConst h cur x_cur →
      Bytes.RepAddressRef addrTy h bR x_rb → Bytes.RepAddressRef addrTy h prim x_prim →
      RepList flatListEnum (FlatEntryRepExact (keyOf t)) h acc x_acc →
      ObsFn W "KernelCheck::aux_from_recrs_walk_ex"
        [x_all, x_cur, x_rb, x_prim, x_uo, x_acc, .field (k : F)] h r h' cs →
      (∀ c ∈ cs, c ∈ calls) →
      Heap.Extends h h' ∧
      ∃ es, auxWalk (contribAt t E₀ rb crb rs (ixAddr prim)) cur.length k acc = some es ∧
        RepList flatListEnum (FlatEntryRepExact (keyOf t)) h' es r := by
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  have hinj := keyOf_injective' htwf
  intro cur
  induction cur with
  | nil =>
    intro k acc x_cur x_acc r h h' cs _ _ hcur _ _ hacc ev _
    match Obs.«KernelCheck::aux_from_recrs_walk_ex».obsx ev with
    | .Nil (he21 := hr) (he22 := hh) .. =>
      rw [hr, hh]
      exact ⟨Heap.Extends.refl _, acc, rfl, hacc⟩
    | .Cons_Recr_n0_other_other_other_other (ld12 := ld) ..
    | .Cons_Recr_other_bind_other_bind_bind_n1 (ld12 := ld) ..
    | .Cons_Recr_other_bind_other_bind_bind_other (ld12 := ld) ..
    | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hcur ld
      cases he
  | cons m rest ih =>
    intro k acc x_cur x_acc r h h' cs hsuf hall hcur hrb hprim hacc ev hsub
    have hm0 : rs[k]? = some m := by simpa using hsuf 0 m rfl
    obtain ⟨rc, rfl⟩ := hR.recrs m (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hm0))
    have hsuf' : ∀ j m', rest[j]? = some m' → rs[k + 1 + j]? = some m' := fun j m' hj => by
      have := hsuf (j + 1) m' (by simpa using hj)
      rwa [show k + (j + 1) = k + 1 + j by omega] at this
    have bsub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → Bounded cs' :=
      fun hs => RomBound.bounded_mono hbd fun c hc => hsub c (hs c hc)
    match Obs.«KernelCheck::aux_from_recrs_walk_ex».obsx ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hcur ld
    | .Cons_other (ld12 := ld) (hne1022 := hne) .. =>
      obtain ⟨m', rest', he, hm, hrest⟩ := Lib.rep_cons_of_load hcur ld
      injection he with h1 h2
      subst h1 h2
      obtain ⟨rv, hrv, -⟩ := hm
      exact absurd hrv (hne [rv] rfl)
    | .Cons_Recr_n0_other_other_other_other (cs115 := cs115) (cs561 := cs561) (cs617 := cs617)
        (ld12 := ld) (ev76 := ev76) (ev117 := ev117) (ld111 := ld111) (sg566 := sg)
        (op682 := op) (ev619 := evR) (hc684 := hc) .. =>
      obtain ⟨m', rest', he, hm, hrest⟩ := Lib.rep_cons_of_load hcur ld
      injection he with h1 h2
      subst h1 h2
      obtain ⟨ext, ty, d, a, ls, As, x_ty, w0, w1, w2, w3, w4, w5, xmaj, xpar, xls, w, xpnp, xpnl,
        b, hci, hres, hN, htm, hdom, hdeq, hM, ra, rls, hcon, hb0, hb1⟩ :=
        walk_prefix ht hbd hS hH hR hlv hrs_lt hbR hm0 hall hrb hprim ev76 ev117 ld111 sg
          (fun c hc' => hsub c (by rw [hc]; simp [hc']))
          (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      have hb : b = false := by
        cases b with
        | false => rfl
        | true =>
          injection hres with hl
          injection hl with hf _
          exact absurd (Value.field.inj hf) (by decide)
      obtain rfl := binop_add_one_nat op
      obtain ⟨ext', es, hes, hrep⟩ := ih (k + 1) acc hsuf'
        (RepLinkedList.mono L1.repMutConst_heapMono₂ ext hall)
        (RepLinkedList.mono L1.repMutConst_heapMono₂ ext hrest)
        (Bytes.repAddressRef_heapMono₂ addrTy ext hrb)
        (Bytes.repAddressRef_heapMono₂ addrTy ext hprim) (flatList_mono ext hacc) evR
        (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      refine ⟨ext.trans ext', es, ?_, hrep⟩
      simp only [List.length_cons, auxWalk, hcon, hb0 hb]
      exact hes
    | .Cons_Recr_other_bind_other_bind_bind_n1 (cs115 := cs115) (cs561 := cs561)
        (cs729 := cs729) (cs759 := cs759) (cs782 := cs782) (cs816 := cs816)
        (ld12 := ld) (ev76 := ev76) (ev117 := ev117) (ld111 := ld111) (sg566 := sg)
        (ev731 := evSP) (ev761 := evOU) (ev784 := evIn) (op881 := op) (ev818 := evR)
        (hc883 := hc) (hnt0 := hnt) .. =>
      obtain ⟨m', rest', he, hm, hrest⟩ := Lib.rep_cons_of_load hcur ld
      injection he with h1 h2
      subst h1 h2
      obtain ⟨ext, ty, d, a, ls, As, x_ty, w0, w1, w2, w3, w4, w5, xmaj, xpar, xls, w, xpnp, xpnl,
        b, hci, hres, hN, htm, hdom, hdeq, hM, ra, rls, hcon, hb0, hb1⟩ :=
        walk_prefix ht hbd hS hH hR hlv hrs_lt hbR hm0 hall hrb hprim ev76 ev117 ld111 sg
          (fun c hc' => hsub c (by rw [hc]; simp [hc']))
          (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      have hb : b = true := by
        cases b with
        | true => rfl
        | false => exact (hnt _ _ _ _ hres).elim
      injection hres with hl
      injection hl with _ hl
      injection hl with e2 hl
      injection hl with _ hl
      injection hl with e4 _
      subst e2 e4 hci
      obtain ⟨i, hinfo, hblk, hxp, hnpb⟩ := hb1 hb
      subst hxp
      obtain ⟨ext3, d', ys, hdom', hys, hrepys⟩ :=
        extract_aux_spec_params_from_rec_spec (root := calls) hN (by omega) hM htm evSP
          (bsub fun c hc' => by rw [hc]; simp [hc'])
          (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      have hdd : d' = d := Option.some.inj (hdom'.symm.trans hdom)
      subst hdd
      obtain ⟨hus, ext4⟩ := extract_aux_occ_us_spec hN (hM.mono ext3) evOU
      subst hus
      have ext34 := ext3.trans ext4
      obtain ⟨hin, ext5⟩ := aux_already_in_spec hinj acc evIn
        (bsub fun c hc' => by rw [hc]; simp [hc']) (flatList_mono (ext.trans ext34) hacc)
        (Bytes.repAddressRef_heapMono₂ addrTy ext34 ra) (tmOExactList_mono ext4 hrepys)
        (rls.mono ext34)
      have hinT : auxEntryIn acc (ixAddr a) ys ls = true := by
        cases hx : auxEntryIn acc (ixAddr a) ys ls with
        | true => rfl
        | false =>
          rw [hx] at hin
          exact absurd (Value.field.inj hin) (by decide)
      have extAll := ext.trans (ext34.trans ext5)
      obtain rfl := binop_add_one_nat op
      obtain ⟨ext', es, hes, hrep⟩ := ih (k + 1) acc hsuf'
        (RepLinkedList.mono L1.repMutConst_heapMono₂ extAll hall)
        (RepLinkedList.mono L1.repMutConst_heapMono₂ extAll hrest)
        (Bytes.repAddressRef_heapMono₂ addrTy extAll hrb)
        (Bytes.repAddressRef_heapMono₂ addrTy extAll hprim) (flatList_mono extAll hacc) evR
        (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      refine ⟨extAll.trans ext', es, ?_, hrep⟩
      rw [hdeq] at hys hcon
      have hau := auxOfMajor_some (t := t) (E₀ := E₀) htwf hinfo hblk hys
      simp only [List.length_cons, auxWalk, hcon, hau, hinT, ↓reduceIte]
      exact hes
    | .Cons_Recr_other_bind_other_bind_bind_other (cs115 := cs115) (cs561 := cs561)
        (cs729 := cs729) (cs759 := cs759) (cs782 := cs782) (cs899 := cs899) (cs953 := cs953)
        (m771 := m771) (v718 := v718) (v748 := v748) (ld12 := ld) (ev76 := ev76) (ev117 := ev117) (ld111 := ld111) (sg566 := sg)
        (ev731 := evSP) (ev761 := evOU) (ev784 := evIn) (hne884 := hneIn) (ev901 := evSn)
        (op1018 := op) (ev955 := evR) (hc1020 := hc) (hnt0 := hnt) .. =>
      obtain ⟨m', rest', he, hm, hrest⟩ := Lib.rep_cons_of_load hcur ld
      injection he with h1 h2
      subst h1 h2
      obtain ⟨ext, ty, d, a, ls, As, x_ty, w0, w1, w2, w3, w4, w5, xmaj, xpar, xls, w, xpnp, xpnl,
        b, hci, hres, hN, htm, hdom, hdeq, hM, ra, rls, hcon, hb0, hb1⟩ :=
        walk_prefix ht hbd hS hH hR hlv hrs_lt hbR hm0 hall hrb hprim ev76 ev117 ld111 sg
          (fun c hc' => hsub c (by rw [hc]; simp [hc']))
          (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      have hb : b = true := by
        cases b with
        | true => rfl
        | false => exact (hnt _ _ _ _ hres).elim
      injection hres with hl
      injection hl with _ hl
      injection hl with e2 hl
      injection hl with _ hl
      injection hl with e4 _
      subst e2 e4 hci
      obtain ⟨i, hinfo, hblk, hxp, hnpb⟩ := hb1 hb
      subst hxp
      obtain ⟨ext3, d', ys, hdom', hys, hrepys⟩ :=
        extract_aux_spec_params_from_rec_spec (root := calls) hN (by omega) hM htm evSP
          (bsub fun c hc' => by rw [hc]; simp [hc'])
          (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      have hdd : d' = d := Option.some.inj (hdom'.symm.trans hdom)
      subst hdd
      obtain ⟨hus, ext4⟩ := extract_aux_occ_us_spec hN (hM.mono ext3) evOU
      subst hus
      have ext34 := ext3.trans ext4
      obtain ⟨hin, ext5⟩ := aux_already_in_spec hinj acc evIn
        (bsub fun c hc' => by rw [hc]; simp [hc']) (flatList_mono (ext.trans ext34) hacc)
        (Bytes.repAddressRef_heapMono₂ addrTy ext34 ra) (tmOExactList_mono ext4 hrepys)
        (rls.mono ext34)
      have hinF : auxEntryIn acc (ixAddr a) ys ls = false := by
        cases hx : auxEntryIn acc (ixAddr a) ys ls with
        | false => rfl
        | true =>
          rw [hx] at hin
          exact absurd hin hneIn
      have ext345 := ext34.trans ext5
      have hentry : FlatEntryRepExact (keyOf t) m771 (⟨ixAddr a, true, ys, ls⟩ : FlatEntry)
          (.tuple [_, .field 1, v718, v748]) :=
        ⟨_, _, _, a, rfl, Bytes.repAddressRef_heapMono₂ addrTy ext345 ra, rfl,
          tmOExactList_mono (ext4.trans ext5) hrepys, rls.mono ext345⟩
      have hacc5 : RepList (Instance.mk "Lists::Node" [flatEntryTy]).symbol
          (FlatEntryRepExact (keyOf t)) m771 acc x_acc := by
        rw [flatListEnum_eq]
        exact flatList_mono (ext.trans ext345) hacc
      have hsn := Lib.Lists.snoc_spec (t := flatEntryTy)
        (flatEntryRepExact_heapMono₂ (κ := keyOf t))
        (by rw [Obs.Names.«Lists::snoc<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol]; exact evSn)
        hacc5 hentry
      rw [flatListEnum_eq] at hsn
      have extAll := ext.trans (ext345.trans evSn.heap_extends)
      obtain rfl := binop_add_one_nat op
      obtain ⟨ext', es, hes, hrep⟩ := ih (k + 1) (acc ++ [⟨ixAddr a, true, ys, ls⟩]) hsuf'
        (RepLinkedList.mono L1.repMutConst_heapMono₂ extAll hall)
        (RepLinkedList.mono L1.repMutConst_heapMono₂ extAll hrest)
        (Bytes.repAddressRef_heapMono₂ addrTy extAll hrb)
        (Bytes.repAddressRef_heapMono₂ addrTy extAll hprim) hsn evR
        (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      refine ⟨extAll.trans ext', es, ?_, hrep⟩
      rw [hdeq] at hys hcon
      have hau := auxOfMajor_some (t := t) (E₀ := E₀) htwf hinfo hblk hys
      simp only [List.length_cons, auxWalk, hcon, hau, hinF, Bool.false_eq_true, ↓reduceIte]
      exact hes

/-! ## The primary block's types -/

section LevelRange

open IxVM.Refinement.Core
open Ix.Kernel (Level)

/-- `KernelCheck::build_param_lvls_range(start, count, idx)`: the level parameters
`start + idx, …, start + count - 1`. -/
theorem build_param_lvls_range_at (rem : Nat) :
    ∀ {start count idx : F} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val count = ZMod.val idx + rem →
      ZMod.val start + ZMod.val count < 4294967296 →
      ObsFn W "KernelCheck::build_param_lvls_range" [.field start, .field count, .field idx]
        h r h' cs →
      RepKLevelList h'
        ((List.range rem).map fun k => .param (ZMod.val start + ZMod.val idx + k)) r := by
  induction rem with
  | zero =>
    intro start count idx r h h' cs hrem _ ev
    rcases Obs.«KernelCheck::build_param_lvls_range».obs ev with ⟨_, rfl, rfl, _⟩ |
      ⟨v1, _, _, _, _, _, _, op17, hne, _, _, _, _, _, _, _⟩
    · obtain ⟨repN, _⟩ := RepKLevelList.allocNil h
      rw [IxVM.Refinement.Levels.klevelList_names] at repN
      simpa using repN
    · rw [SubstAux.sub_ok op17] at hne
      have hv : ZMod.val (count - idx) = 0 := by rw [SubstAux.val_sub (by omega)]; omega
      have hcz : count - idx = 0 := ZMod.val_injective _ (by simpa using hv)
      exact absurd (congrArg Value.field hcz) hne
  | succ rem ih =>
    intro start count idx r h h' cs hrem hlt ev
    rcases Obs.«KernelCheck::build_param_lvls_range».obs ev with ⟨op17, _, _, _⟩ |
      ⟨_, v46, m48, v60, m78, _, v91, op17, _, rfl, rfl, rfl, op74, op119, ev_rec, _⟩
    · have hsub := SubstAux.sub_ok op17
      injection hsub with h0
      have hv : ZMod.val (count - idx) = rem + 1 := by rw [SubstAux.val_sub (by omega)]; omega
      rw [← h0, ZMod.val_zero] at hv; omega
    · rw [SubstAux.add_ok op74] at ev_rec
      rw [SubstAux.add_ok op119] at ev_rec
      have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
      have hval1 : ZMod.val (1 : F) = 1 := rfl
      have hsi_val : ZMod.val (start + idx) = ZMod.val start + ZMod.val idx :=
        SubstAux.val_add (by omega)
      have hsi_cast : ((ZMod.val start + ZMod.val idx : Nat) : F) = start + idx := by
        rw [← hsi_val, ZMod.natCast_zmod_val]
      have hparam : RepKLevel (h ++ [.construct klevelEnum "Param" [.field (start + idx)]])
          (.param (ZMod.val start + ZMod.val idx)) (.ptr (.enum klevelEnum) h.length) :=
        .param (by omega) (by rw [hsi_cast]; simp)
      have hi1 : ZMod.val (idx + 1) = ZMod.val idx + 1 := SubstAux.val_add (by omega)
      have htail := ih (start := start) (count := count) (idx := idx + 1)
        (by omega) hlt ev_rec
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      have htail_eq :
          ((List.range rem).map
            ((fun k => Level.param (ZMod.val start + ZMod.val idx + k)) ∘ (· + 1))) =
            (List.range rem).map (fun k => .param (ZMod.val start + ZMod.val (idx + 1) + k)) := by
        apply List.map_congr_left
        intro k _
        exact congrArg (fun n : Nat => Level.param n)
          (show (ZMod.val start + ZMod.val idx + (k + 1) : Nat) =
              ZMod.val start + ZMod.val (idx + 1) + k by
            rw [hi1]; omega)
      rw [Nat.add_zero, htail_eq]
      obtain ⟨repC, _⟩ := RepKLevelList.allocCons (hparam.mono ev_rec.heap_extends) htail
      rw [IxVM.Refinement.Levels.klevelList_names] at repC
      exact repC

end LevelRange

/-- **`KernelCheck::build_param_lvls_range(off, nl, 0)`**: the level parameters `off + j` for
`j < nl`, the levels `build_flat_originals` gives a type of the block. -/
theorem param_lvls_range_spec {off nl : Nat} (hlt : off + nl < 4294967296)
    {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::build_param_lvls_range"
      [.field (off : F), .field (nl : F), .field 0] h r h' cs) :
    RepKLevelList h' ((List.range nl).map fun j => Ix.Kernel.Level.param (off + j)) r := by
  have ho : ((off : F)).val = off := FamilyOfCall.val_cast_lt_u58 (by omega)
  have hn : ((nl : F)).val = nl := FamilyOfCall.val_cast_lt_u58 (by omega)
  have h1 := build_param_lvls_range_at nl (start := (off : F)) (count := (nl : F)) (idx := 0)
    (by rw [hn, ZMod.val_zero, Nat.zero_add]) (by rw [ho, hn]; exact hlt) ev
  rw [ho, ZMod.val_zero] at h1
  simpa using h1

/-- **The store's reading of a type of a block whose projection record the run hashed.** -/
theorem member_indInfo (hH : LoadedReads.HashedRecordsStored calls E₀)
    {bP : Bytes.Address} {cP : Ixon.Constant} {mP : Array Ixon.MutConst}
    (hcP : recordOf E₀ (ixAddr bP) = some cP) (hmP : cP.info = .muts mP)
    {k : Nat} {ind : Ixon.Inductive} (hk : mP[k]? = some (.indc ind)) (hklt : k < UInt64.size)
    (hh : Hashed calls (Ixon.serConstant
      ⟨Core.Specs.Callees.memberProjInfo (ixAddr bP) k (.indc ind), #[], #[], #[], #[]⟩)) :
    indInfoAt E₀ (memberAddr (ixAddr bP) k (.indc ind)) =
      some (some ⟨ind.lvls.toNat, ind.params.toNat, ind.ctors.size, ixAddr bP, k⟩) := by
  have hwf : (⟨Core.Specs.Callees.memberProjInfo (ixAddr bP) k (.indc ind), #[], #[], #[],
      #[]⟩ : Ixon.Constant).wireWF := L1.projConstant_wireWF_iPrj k.toUInt64 bP
  have hrecraw := Claim.recordOf_of_hashed hH hh (serConstant_iprj_size_lt k.toUInt64 bP)
    (Ixon.Verify.deConstantExact_serConstant _ hwf)
  have hrec : recordOf E₀ (memberAddr (ixAddr bP) k (.indc ind)) =
      some (memberProjection (ixAddr bP) k (.indc ind)) := by
    rw [LoadedReads.memberAddr_eq_projAddr]
    exact hrecraw
  have h := indInfoAt_of_iPrj (p := ⟨k.toUInt64, ixAddr bP⟩) hrec rfl hcP hmP
    (by rw [toUInt64_toNat_of_lt hklt]; exact hk)
  rw [toUInt64_toNat_of_lt hklt] at h
  exact h

/-- **`KernelCheck::flat_originals_walk`** over the members of a block of the store from position
`k` is `FamilyFlat.originals` of their addresses at the offset: each inductive type of the block
at the levels `param (off + j)`, with no parameters. -/
theorem flat_originals_walk_spec (hbd : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    {bP : Bytes.Address} {cP : Ixon.Constant} {mP : Array Ixon.MutConst}
    (hcP : recordOf E₀ (ixAddr bP) = some cP) (hmP : cP.info = .muts mP)
    (hsz : mP.size < 8589934592) {off : Nat}
    (hoff : ∀ (j : Nat) (ind : Ixon.Inductive), mP[j]? = some (Ixon.MutConst.indc ind) →
      off + ind.lvls.toNat < 4294967296)
    {x_all x_blk : SourceValue F} :
    ∀ (cur : List Ixon.MutConst) (k : Nat) {x_cur r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      (∀ j m, cur[j]? = some m → mP[k + j]? = some m) →
      RepList L1.mutConstListEnum L1.RepMutConst h mP.toList x_all →
      RepList L1.mutConstListEnum L1.RepMutConst h cur x_cur →
      Bytes.RepAddressRef addrTy h bP x_blk →
      ObsFn W "KernelCheck::flat_originals_walk"
        [x_all, x_cur, x_blk, .field (off : F), .field (k : F)] h r h' cs →
      (∀ c ∈ cs, c ∈ calls) →
      Heap.Extends h h' ∧
      ∃ os, originals (FlatView.ofStore t E₀) off (indcAddrs (ixAddr bP) k cur) = some os ∧
        RepList flatListEnum (FlatEntryRepExact (keyOf t)) h' os r := by
  intro cur
  induction cur with
  | nil =>
    intro k x_cur r h h' cs _ _ hcur _ ev _
    match Obs.«KernelCheck::flat_originals_walk».obs ev with
    | .Nil (he24 := hr) (hm23 := hh) .. =>
      rw [hr, hh]
      exact ⟨Heap.Extends.snoc _ _, [], rfl, Lib.rep_store_nil h⟩
    | .Cons_Indc (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hcur ld
      cases he
  | cons m rest ih =>
    intro k x_cur r h h' cs hsuf hall hcur hb ev hsub
    have hm0 : mP[k]? = some m := by simpa using hsuf 0 m rfl
    have hklt : k < mP.size := (Array.getElem?_eq_some_iff.mp hm0).1
    have hsuf' : ∀ j m', rest[j]? = some m' → mP[k + 1 + j]? = some m' := fun j m' hj => by
      have := hsuf (j + 1) m' (by simpa using hj)
      rwa [show k + (j + 1) = k + 1 + j by omega] at this
    match Obs.«KernelCheck::flat_originals_walk».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hcur ld
    | .Cons_other (cs382 := cs382) (ld12 := ld) (hne375 := hne) (op431 := op) (ev384 := evR)
        (hc433 := hc) .. =>
      obtain ⟨m', rest', he, hm, hrest⟩ := Lib.rep_cons_of_load hcur ld
      injection he with h1 h2
      subst h1 h2
      obtain rfl := binop_add_one_nat op
      have hrec := ih (k + 1) hsuf' hall hrest hb evR
        (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      cases m with
      | indc ind =>
        obtain ⟨iv, hiv, -⟩ := hm
        exact absurd hiv (hne [iv] rfl)
      | defn d => simpa only [indcAddrs] using hrec
      | recr rc => simpa only [indcAddrs] using hrec
    | .Cons_Indc (v68 := v68) (cs79 := cs79) (v106 := v106) (m107 := m107) (cs120 := cs120)
        (v213 := v213) (m214 := m214) (v222 := v222) (m223 := m223) (v268 := v268)
        (m295 := m295) (m315 := m315) (cs323 := cs323)
        (ld12 := ld) (ev81 := e1) (ev122 := e2) (ld116 := ld116) (sg221 := sg) (ev235 := e3)
        (he263 := hr) (hm262 := hh) (hm303 := hm3) (op372 := op) (ev325 := evR)
        (hc374 := hc) .. =>
      obtain ⟨m', rest', he, hm, hrest⟩ := Lib.rep_cons_of_load hcur ld
      injection he with h1 h2
      subst h1 h2
      cases m with
      | defn d => obtain ⟨_, hmv, -⟩ := hm; simp at hmv
      | recr rc => obtain ⟨_, hmv, -⟩ := hm; simp at hmv
      | indc ind =>
        have hkval : ((k : F)).val = k := FamilyOfCall.val_cast_lt_u58 (by omega)
        obtain ⟨ext1, -, -, mc, a, hget, ha_rep, ha_eq, hhash⟩ :=
          L1.projection_addr_hashed_spec (Route.membersRep_of_repMutConstList hall) hb e1
        rw [hkval, Array.getElem?_toList, hm0] at hget
        have hmc : mc = .indc ind := (Option.some.inj hget).symm
        subst hmc
        rw [hkval] at ha_eq hhash
        have hci : indInfoAt E₀ (memberAddr (ixAddr bP) k (.indc ind)) =
            some (some ⟨ind.lvls.toNat, ind.params.toNat, ind.ctors.size, ixAddr bP, k⟩) :=
          member_indInfo hH hcP hmP hm0 (Nat.lt_trans hklt (Nat.lt_trans hsz (by decide)))
            (IxVM.Refinement.Core.hashed_mono
              (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hhash)
        have hsub120 : ∀ c ∈ cs120, c ∈ calls := fun c hc' => hsub c (by rw [hc]; simp [hc'])
        obtain ⟨ext2, -, blkBytes, cb, ms, ind', blobs, v, hhB, haB, hexB, -, hcbi, hmem, -, hldv,
          hraw⟩ := L1.get_ci_iprj_spec (RomBound.bounded_mono hbd hsub120)
            (Bytes.repAddressRef_heapMono₂ addrTy ext1 hb) e2
        have hcb : cb = cP := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hcP)
          (IxVM.Refinement.Core.hashed_mono hsub120 hhB) haB hexB
        subst hcb
        have hms : ms = mP := Ixon.ConstantInfo.muts.inj (hcbi.symm.trans hmP)
        subst hms
        rw [hkval, Array.getElem?_toList, hm0] at hmem
        have hind : ind' = ind := (Ixon.MutConst.indc.inj (Option.some.inj hmem)).symm
        subst hind
        obtain ⟨hl, -, -, -, -, tyPtr, blkPtr, b, -, -, hv, -⟩ := hraw
        have hv106 : v106 = v := Except.ok.inj (ld116.symm.trans hldv)
        have hseg : v213 = .field (ind'.lvls.toNat : F) ∧ m214 = m107 := by
          match sg with
          | .Induct (hv153 := hvi) (he203 := hrs) (he204 := hhs) .. =>
            rw [hv106, hv] at hvi
            have hargs := (Value.construct.inj hvi).2.2
            simp only [List.cons.injEq, and_true] at hargs
            exact ⟨hrs.trans hargs.1.symm, hhs⟩
          | .other (hne206 := hnei) .. => exact (hnei _ rfl (hv106.trans hv)).elim
        obtain ⟨hv213, hm214⟩ := hseg
        subst hv213 hm214
        have hlv := param_lvls_range_spec (hoff k ind' hm0) e3
        subst hm3
        obtain rfl := binop_add_one_nat op
        have ext3 := e3.heap_extends
        have ext4 : Heap.Extends m223
            (m223 ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []]) :=
          Heap.Extends.snoc _ _
        have extR := ext1.trans (ext2.trans (ext3.trans ext4))
        obtain ⟨ext5, os, hos, hrep⟩ := ih (k + 1) hsuf'
          (RepLinkedList.mono L1.repMutConst_heapMono₂ extR hall)
          (RepLinkedList.mono L1.repMutConst_heapMono₂ extR hrest)
          (Bytes.repAddressRef_heapMono₂ addrTy extR hb) evR
          (fun c hc' => hsub c (by rw [hc]; simp [hc']))
        rw [hr, hh]
        have hnil : RepList kexprListEnum (TmOExact (keyOf t))
            (m223 ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []]) []
            (.ptr (.enum kexprListEnum) m223.length) := Lib.rep_store_nil m223
        have hentry : FlatEntryRepExact (keyOf t) m315
            (⟨memberAddr (ixAddr bP) k (.indc ind'), false, [],
              (List.range ind'.lvls.toNat).map fun j => .param (off + j)⟩ : FlatEntry)
            (.tuple [v68, .field 0,
              .ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m223.length, v222]) :=
          ⟨v68, _, _, a, rfl,
            Bytes.repAddressRef_heapMono₂ addrTy (ext2.trans (ext3.trans (ext4.trans ext5))) ha_rep,
            by rw [ha_eq, LoadedReads.memberAddr_eq_projAddr],
            tmOExactList_mono ext5 hnil, hlv.mono (ext4.trans ext5)⟩
        refine ⟨extR.trans (ext5.trans (Heap.Extends.snoc _ _)), _ :: os, ?_,
          Lib.rep_store_cons flatEntryRepExact_heapMono₂ hentry hrep⟩
        have hci' : (FlatView.ofStore t E₀).ci (memberAddr (ixAddr bP) k (.indc ind')) =
            some (some ⟨ind'.lvls.toNat, ind'.params.toNat, ind'.ctors.size, ixAddr bP, k⟩) := hci
        simp only [indcAddrs, originals, hci', hos]

/-! ## The primary block -/

/-- The block of an inductive type the store reads is a block record of the store. -/
theorem indInfoAt_block {E : Ixon.Env} {a : _root_.Address} {i : IndInfo}
    (h : indInfoAt E a = some (some i)) :
    ∃ cb ms, recordOf E i.blk = some cb ∧ cb.info = .muts ms := by
  unfold indInfoAt at h
  cases hc : recordOf E a with
  | none => simp [hc] at h
  | some c =>
    simp only [hc] at h
    cases hi : c.info with
    | iPrj p =>
      simp only [hi] at h
      cases hcb : recordOf E p.block with
      | none => simp [hcb] at h
      | some cb =>
        simp only [hcb] at h
        cases hm : cb.info with
        | muts ms =>
          simp only [hm] at h
          cases hk : ms[p.idx.toNat]? with
          | none => simp [hk] at h
          | some m =>
            cases m with
            | indc ind =>
              simp only [hk, Option.some.injEq] at h
              subst h
              exact ⟨cb, ms, hcb, hm⟩
            | defn _ => simp [hk] at h
            | recr _ => simp [hk] at h
        | defn _ => simp [hm] at h
        | recr _ => simp [hm] at h
        | axio _ => simp [hm] at h
        | quot _ => simp [hm] at h
        | cPrj _ => simp [hm] at h
        | rPrj _ => simp [hm] at h
        | iPrj _ => simp [hm] at h
        | dPrj _ => simp [hm] at h
    | defn _ => simp [hi] at h
    | recr _ => simp [hi] at h
    | axio _ => simp [hi] at h
    | quot _ => simp [hi] at h
    | cPrj _ => simp [hi] at h
    | rPrj _ => simp [hi] at h
    | dPrj _ => simp [hi] at h
    | muts _ => simp [hi] at h

/-- **The projection address of a recursor of the record and its load**: the payload is a `Rec`
with the recursor's counts, its type pointer representing the canonical reading exactly. -/
theorem recLoad_prefix (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hR : FamRecRecord E₀ rb crb rs) (hlv : RecLevelsDefined t E₀ rb crb rs)
    (hrs_lt : rs.size < 8589934592) {bR : Bytes.Address} (hbR : ixAddr bR = rb)
    {k : Nat} {rc : Ixon.Recursor} (hrk : rs[k]? = some (.recr rc))
    {x_all x_rb v63 p109 v101 : SourceValue F}
    {h m64 m102 : Heap F} {cs74 cs115 : List (Call F)}
    (hall : RepList L1.mutConstListEnum L1.RepMutConst h rs.toList x_all)
    (hrb : Bytes.RepAddressRef addrTy h bR x_rb)
    (ev76 : ObsFn W "Ingress::projection_addr" [x_all, x_rb, .field (k : F)] h v63 m64 cs74)
    (ev117 : ObsFn W "Ingress::get_ci" [v63] m64 p109 m102 cs115)
    (ld111 : loadValue m102 p109 = .ok v101)
    (hsub115 : ∀ c ∈ cs115, c ∈ calls) :
    Heap.Extends h m102 ∧
    ∃ (ty : KExpr) (x_ty w0 w1 w2 w3 w4 w5 : SourceValue F),
      v101 = .construct "KernelTypes::KConstantInfo" "Rec"
        [w0, x_ty, .field (rc.params.toNat : F), .field (rc.indices.toNat : F),
          .field (rc.motives.toNat : F), .field (rc.minors.toNat : F), w1, w2, w3, w4, w5] ∧
      loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
        (mutsRoot rs k) rc.typ = some ty ∧
      TmOExact (keyOf t) m102 ty x_ty ∧
      rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat <
        288230376151711744 := by
  have hklt : k < rs.size := (Array.getElem?_eq_some_iff.mp hrk).1
  have hkval : ((k : F)).val = k := FamilyOfCall.val_cast_lt_u58 (by omega)
  obtain ⟨ext1, -, -, mc, aW, hget, haW, haW_eq⟩ :=
    L1.projection_addr_spec (Route.membersRep_of_repMutConstList hall) hrb ev76
  rw [hkval, Array.getElem?_toList, hrk] at hget
  have hmc : mc = .recr rc := (Option.some.inj hget).symm
  subst hmc
  rw [hkval, hbR, ← LoadedReads.memberAddr_eq_projAddr, LoadedReads.memberAddr_recr] at haW_eq
  obtain ⟨ty, x_ty, w1, w2, w3, w4, w5, hci, hloaded, htm, hnp, hni, hnmot, hnmin⟩ :=
    recMember_load ht hbd hS hR hlv (Nat.lt_trans hklt (Nat.lt_trans hrs_lt (by decide))) hrk
      haW_eq haW ev117 hsub115 ld111
  exact ⟨ext1.trans ev117.heap_extends, ty, x_ty, _, w1, w2, w3, w4, w5, hci, hloaded, htm,
    by omega⟩

/-- **`KernelCheck::first_recr_parent_block`** on the members of a family record is
`FamilyFlatRecord.primaryAt`: the block of the inductive type heading the first recursor's major
premise, the fallback for an empty record or a major premise over no inductive type. The block it
returns is a block record of the store. -/
theorem first_recr_parent_block_spec (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hR : FamRecRecord E₀ rb crb rs) (hlv : RecLevelsDefined t E₀ rb crb rs)
    (hrs_lt : rs.size < 8589934592) {bR bB : Bytes.Address} (hbR : ixAddr bR = rb)
    {cB : Ixon.Constant} {mB : Array Ixon.MutConst}
    (hcB : recordOf E₀ (ixAddr bB) = some cB) (hmB : cB.info = .muts mB)
    {x_all x_rb x_fb r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hall : RepList L1.mutConstListEnum L1.RepMutConst h rs.toList x_all)
    (hrb : Bytes.RepAddressRef addrTy h bR x_rb) (hfb : Bytes.RepAddressRef addrTy h bB x_fb)
    (ev : ObsFn W "KernelCheck::first_recr_parent_block"
      [x_all, x_all, x_rb, .field ((0 : Nat) : F), x_fb] h r h' cs)
    (hsub : ∀ c ∈ cs, c ∈ calls) :
    Heap.Extends h h' ∧
    ∃ (P : Bytes.Address) (cP : Ixon.Constant) (mP : Array Ixon.MutConst),
      primaryAt t E₀ rb crb rs (ixAddr bB) = some (ixAddr P) ∧
      Bytes.RepAddressRef addrTy h' P r ∧
      recordOf E₀ (ixAddr P) = some cP ∧ cP.info = .muts mP := by
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  have hhead : ∀ {m : Ixon.MutConst} {rest : List Ixon.MutConst}, rs.toList = m :: rest →
      ∃ rc, m = .recr rc ∧ rs[0]? = some (.recr rc) := by
    intro m rest he
    obtain ⟨rc, rfl⟩ := hR.recrs m (by rw [he]; exact List.mem_cons_self ..)
    exact ⟨rc, rfl, by rw [← Array.getElem?_toList, he]; rfl⟩
  match Obs.«KernelCheck::first_recr_parent_block».obs ev with
  | .Nil (ld12 := ld) (he21 := hr) (he22 := hh) .. =>
    have hnil := Lib.rep_nil_of_load hall ld
    have h0 : rs[0]? = none := by rw [← Array.getElem?_toList, hnil]; rfl
    rw [hr, hh]
    exact ⟨Heap.Extends.refl _, bB, cB, mB, by simp only [primaryAt, h0], hfb, hcB, hmB⟩
  | .Cons_other (ld12 := ld) (hne365 := hne) .. =>
    obtain ⟨m, rest, he, hm, -⟩ := Lib.rep_cons_of_load hall ld
    obtain ⟨rc, rfl, -⟩ := hhead he
    obtain ⟨rv, hrv, -⟩ := hm
    exact absurd hrv (hne [rv] rfl)
  | .Cons_Recr_other (cs115 := cs115) (ld12 := ld) (ev76 := e1) (ev117 := e2) (ld111 := ld1)
      (hne357 := hne) (hc364 := hc) .. =>
    obtain ⟨m, rest, he, hm, -⟩ := Lib.rep_cons_of_load hall ld
    obtain ⟨rc, rfl, h0⟩ := hhead he
    obtain ⟨-, ty, x_ty, w0, w1, w2, w3, w4, w5, hci, -⟩ :=
      recLoad_prefix ht hbd hS hR hlv hrs_lt hbR h0 hall hrb e1 e2 ld1
        (fun c hc' => hsub c (by rw [hc]; simp [hc']))
    exact (hne _ rfl hci).elim
  | .Cons_Recr_Rec_Induct (cs115 := cs115) (cs271 := cs271) (ld12 := ld) (ev76 := e1)
      (ev117 := e2) (ld111 := ld1) (ev216 := evP) (ev273 := evG) (ld267 := ld2) (he346 := hr)
      (he347 := hh) (hc348 := hc) .. =>
    obtain ⟨m, rest, he, hm, -⟩ := Lib.rep_cons_of_load hall ld
    obtain ⟨rc, rfl, h0⟩ := hhead he
    obtain ⟨ext, ty, x_ty, w0, w1, w2, w3, w4, w5, hci, hloaded, htm, hN⟩ :=
      recLoad_prefix ht hbd hS hR hlv hrs_lt hbR h0 hall hrb e1 e2 ld1
        (fun c hc' => hsub c (by rw [hc]; simp [hc']))
    have hargs := (Value.construct.inj hci).2.2
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl, -⟩ := hargs
    obtain ⟨ext3, xmaj, xls, hM⟩ := rec_to_parent_addr_major hN evP
    obtain ⟨d, a, ls, As, hdom, hdeq, -, ra, -⟩ := hM.sem (htm.mono ext3)
    obtain ⟨i, ba, hinfo, -, -, -, -, hba, rba⟩ :=
      (indInfo_of_load hS hH hbd ra evG (fun c hc' => hsub c (by rw [hc]; simp [hc'])) ld2).1
        _ _ _ _ _ _ _ _ rfl
    obtain ⟨cP, mP, hcP, hmP⟩ := indInfoAt_block hinfo
    rw [hr, hh]
    refine ⟨ext.trans (ext3.trans evG.heap_extends), ba, cP, mP, ?_, rba,
      by rw [hba]; exact hcP, hmP⟩
    have hmaj : majorAt t E₀ rb crb rs 0 =
        some (d, rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) := by
      simp only [majorAt, h0, hloaded, hdom]
    have hfn : Ix.Kernel.Expr.getAppFn d = .const (keyOf t (ixAddr a)) ls := by
      rw [hdeq]
      exact getAppFn_const_mkAppN _ _ _
    simp only [primaryAt, h0, hmaj, hfn, constOf, keyAddr_keyOf htwf, hinfo]
    rw [hba]
  | .Cons_Recr_Rec_other (cs115 := cs115) (cs271 := cs271) (ld12 := ld) (ev76 := e1)
      (ev117 := e2) (ld111 := ld1) (ev216 := evP) (ev273 := evG) (ld267 := ld2) (hne349 := hne)
      (he354 := hr) (he355 := hh) (hc356 := hc) .. =>
    obtain ⟨m, rest, he, hm, -⟩ := Lib.rep_cons_of_load hall ld
    obtain ⟨rc, rfl, h0⟩ := hhead he
    obtain ⟨ext, ty, x_ty, w0, w1, w2, w3, w4, w5, hci, hloaded, htm, hN⟩ :=
      recLoad_prefix ht hbd hS hR hlv hrs_lt hbR h0 hall hrb e1 e2 ld1
        (fun c hc' => hsub c (by rw [hc]; simp [hc']))
    have hargs := (Value.construct.inj hci).2.2
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl, -⟩ := hargs
    obtain ⟨ext3, xmaj, xls, hM⟩ := rec_to_parent_addr_major hN evP
    obtain ⟨d, a, ls, As, hdom, hdeq, -, ra, -⟩ := hM.sem (htm.mono ext3)
    have hinfo :=
      (indInfo_of_load hS hH hbd ra evG (fun c hc' => hsub c (by rw [hc]; simp [hc'])) ld2).2 hne
    have extAll := ext.trans (ext3.trans evG.heap_extends)
    rw [hr, hh]
    refine ⟨extAll, bB, cB, mB, ?_, Bytes.repAddressRef_heapMono₂ addrTy extAll hfb, hcB, hmB⟩
    have hmaj : majorAt t E₀ rb crb rs 0 =
        some (d, rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) := by
      simp only [majorAt, h0, hloaded, hdom]
    have hfn : Ix.Kernel.Expr.getAppFn d = .const (keyOf t (ixAddr a)) ls := by
      rw [hdeq]
      exact getAppFn_const_mkAppN _ _ _
    simp only [primaryAt, h0, hmaj, hfn, constOf, keyAddr_keyOf htwf, hinfo]

/-- **`KernelCheck::primary_parent_block_of`** on a family record and a fallback block is
`FamilyFlatRecord.primaryAt`; the block it returns is a block record of the store. -/
theorem primary_parent_block_of_spec (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hR : FamRecRecord E₀ rb crb rs) (hlv : RecLevelsDefined t E₀ rb crb rs)
    {bR bB : Bytes.Address} (hbR : ixAddr bR = rb)
    {cB : Ixon.Constant} {mB : Array Ixon.MutConst}
    (hcB : recordOf E₀ (ixAddr bB) = some cB) (hmB : cB.info = .muts mB)
    {x_rb x_fb r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrb : Bytes.RepAddressRef addrTy h bR x_rb) (hfb : Bytes.RepAddressRef addrTy h bB x_fb)
    (ev : ObsFn W "KernelCheck::primary_parent_block_of" [x_rb, x_fb] h r h' cs)
    (hsub : ∀ c ∈ cs, c ∈ calls) :
    Heap.Extends h h' ∧
    ∃ (P : Bytes.Address) (cP : Ixon.Constant) (mP : Array Ixon.MutConst),
      primaryAt t E₀ rb crb rs (ixAddr bB) = some (ixAddr P) ∧
      Bytes.RepAddressRef addrTy h' P r ∧
      recordOf E₀ (ixAddr P) = some cP ∧ cP.info = .muts mP := by
  have hrec : recordOf E₀ (ixAddr bR) = some crb := by rw [hbR]; exact hR.record
  match Obs.«KernelCheck::primary_parent_block_of».obs ev with
  | .Muts (cs12 := csL) (cs92 := csW) (ev14 := evL) (ev94 := evW) (hc134 := hc) .. =>
    obtain ⟨msPtr, hxm, hlist, hlt⟩ := Decl.load_block_info hS hrb evL
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hrec hR.muts
    have hxe := (List.cons.inj (Value.construct.inj hxm).2.2).1
    subst hxe
    have extL := evL.heap_extends
    obtain ⟨ext, res⟩ := first_recr_parent_block_spec ht hbd hS hH hR hlv hlt hbR hcB hmB hlist
      (Bytes.repAddressRef_heapMono₂ addrTy extL hrb)
      (Bytes.repAddressRef_heapMono₂ addrTy extL hfb) (by simpa using evW)
      (fun c hc' => hsub c (by rw [hc]; simp [hc']))
    exact ⟨extL.trans ext, res⟩
  | .other (cs12 := csL) (ev14 := evL) (hne135 := hne) (hc142 := hc) .. =>
    obtain ⟨msPtr, hxm, -, -⟩ := Decl.load_block_info hS hrb evL
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hrec hR.muts
    exact absurd hxm (hne [msPtr] rfl)

/-- **`KernelCheck::build_flat_originals`** on a block record of the store is
`FamilyFlat.originals` of the block's member addresses (`membersAt`) at the offset. -/
theorem build_flat_originals_spec (hbd : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    {bP : Bytes.Address} {cP : Ixon.Constant} {mP : Array Ixon.MutConst}
    (hcP : recordOf E₀ (ixAddr bP) = some cP) (hmP : cP.info = .muts mP) {off : Nat}
    (hoff : ∀ (j : Nat) (ind : Ixon.Inductive), mP[j]? = some (Ixon.MutConst.indc ind) →
      off + ind.lvls.toNat < 4294967296)
    {x_blk r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hb : Bytes.RepAddressRef addrTy h bP x_blk)
    (ev : ObsFn W "KernelCheck::build_flat_originals" [x_blk, .field (off : F)] h r h' cs)
    (hsub : ∀ c ∈ cs, c ∈ calls) :
    Heap.Extends h h' ∧
    ∃ os, originals (FlatView.ofStore t E₀) off (indcAddrs (ixAddr bP) 0 mP.toList) = some os ∧
      RepList flatListEnum (FlatEntryRepExact (keyOf t)) h' os r := by
  match Obs.«KernelCheck::build_flat_originals».obs ev with
  | .Muts (cs12 := csL) (cs92 := csW) (ev14 := evL) (ev94 := evW) (hc134 := hc) .. =>
    obtain ⟨msPtr, hxm, hlist, hlt⟩ := Decl.load_block_info hS hb evL
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hcP hmP
    have hxe := (List.cons.inj (Value.construct.inj hxm).2.2).1
    subst hxe
    have extL := evL.heap_extends
    obtain ⟨ext, res⟩ := flat_originals_walk_spec (t := t) hbd hS hH hcP hmP hlt hoff mP.toList 0
      (fun j m hj => by rw [Nat.zero_add, ← Array.getElem?_toList]; exact hj) hlist hlist
      (Bytes.repAddressRef_heapMono₂ addrTy extL hb) (by simpa using evW)
      (fun c hc' => hsub c (by rw [hc]; simp [hc']))
    exact ⟨extL.trans ext, res⟩
  | .other_Induct (cs12 := csL) (ev14 := evL) (hne135 := hne) (hc332 := hc) .. =>
    obtain ⟨msPtr, hxm, -, -⟩ := Decl.load_block_info hS hb evL
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hcP hmP
    exact absurd hxm (hne [msPtr] rfl)
  | .other_other (cs12 := csL) (ev14 := evL) (hne135 := hne) (hc345 := hc) .. =>
    obtain ⟨msPtr, hxm, -, -⟩ := Decl.load_block_info hS hb evL
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hcP hmP
    exact absurd hxm (hne [msPtr] rfl)

/-- **`KernelCheck::detect_aux_from_recrs_ex`** on a family record is the walk over all its
recursors (`FamilyFlatRecord.auxWalk` from position `0`). -/
theorem detect_aux_from_recrs_ex_spec (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hR : FamRecRecord E₀ rb crb rs) (hlv : RecLevelsDefined t E₀ rb crb rs)
    {bR prim : Bytes.Address} (hbR : ixAddr bR = rb) {os : List FlatEntry}
    {x_rb x_prim x_uo x_os r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrb : Bytes.RepAddressRef addrTy h bR x_rb)
    (hprim : Bytes.RepAddressRef addrTy h prim x_prim)
    (hos : RepList flatListEnum (FlatEntryRepExact (keyOf t)) h os x_os)
    (ev : ObsFn W "KernelCheck::detect_aux_from_recrs_ex" [x_rb, x_prim, x_uo, x_os] h r h' cs)
    (hsub : ∀ c ∈ cs, c ∈ calls) :
    Heap.Extends h h' ∧
    ∃ es, auxWalk (contribAt t E₀ rb crb rs (ixAddr prim)) rs.size 0 os = some es ∧
      RepList flatListEnum (FlatEntryRepExact (keyOf t)) h' es r := by
  have hrec : recordOf E₀ (ixAddr bR) = some crb := by rw [hbR]; exact hR.record
  match Obs.«KernelCheck::detect_aux_from_recrs_ex».obs ev with
  | .Muts (cs12 := csL) (cs92 := csW) (ev14 := evL) (ev94 := evW) (hc150 := hc) .. =>
    obtain ⟨msPtr, hxm, hlist, hlt⟩ := Decl.load_block_info hS hrb evL
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hrec hR.muts
    have hxe := (List.cons.inj (Value.construct.inj hxm).2.2).1
    subst hxe
    have extL := evL.heap_extends
    obtain ⟨ext, es, hes, hrep⟩ := aux_from_recrs_walk_ex_spec ht hbd hS hH hR hlv hlt hbR
      rs.toList 0 os (fun j m hj => by rw [Nat.zero_add, ← Array.getElem?_toList]; exact hj)
      hlist hlist (Bytes.repAddressRef_heapMono₂ addrTy extL hrb)
      (Bytes.repAddressRef_heapMono₂ addrTy extL hprim) (flatList_mono extL hos)
      (by simpa using evW) (fun c hc' => hsub c (by rw [hc]; simp [hc']))
    rw [Array.length_toList] at hes
    exact ⟨extL.trans ext, es, hes, hrep⟩
  | .other (cs12 := csL) (ev14 := evL) (hne151 := hne) (hc158 := hc) .. =>
    obtain ⟨msPtr, hxm, -, -⟩ := Decl.load_block_info hS hrb evL
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hrec hR.muts
    exact absurd hxm (hne [msPtr] rfl)

end Run

/-! ## The walk appends auxiliaries only -/

theorem auxOfMajor_aux {V : FlatView} {prim : _root_.Address} {low : Nat} {d : KExpr}
    {e : FlatEntry} (h : auxOfMajor V prim low d = some (some e)) : e.aux = true := by
  unfold auxOfMajor at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [Option.some.injEq] at h; rw [← h])

theorem contribAt_aux {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {rb : _root_.Address}
    {crb : Ixon.Constant} {rs : Array Ixon.MutConst} {prim : _root_.Address} {k : Nat}
    {e : FlatEntry} (h : contribAt t E rb crb rs prim k = some (some e)) : e.aux = true := by
  unfold contribAt at h
  cases hm : majorAt t E rb crb rs k with
  | none => simp [hm] at h
  | some x =>
    obtain ⟨d, low⟩ := x
    simp only [hm] at h
    exact auxOfMajor_aux h

/-- **The walk extends its entries by auxiliaries only**, when every contribution is one. -/
theorem auxWalk_aux (c : Nat → Option (Option FlatEntry))
    (hc : ∀ k e, c k = some (some e) → e.aux = true) :
    ∀ (n k : Nat) (acc res : List FlatEntry), auxWalk c n k acc = some res →
      ∃ xs, res = acc ++ xs ∧ ∀ e ∈ xs, e.aux = true := by
  intro n
  induction n with
  | zero =>
    intro k acc res h
    simp only [auxWalk, Option.some.injEq] at h
    exact ⟨[], by simp [h], by simp⟩
  | succ n ih =>
    intro k acc res h
    simp only [auxWalk] at h
    cases hck : c k with
    | none => simp [hck] at h
    | some x =>
      cases x with
      | none =>
        simp only [hck] at h
        exact ih (k + 1) acc res h
      | some e =>
        simp only [hck] at h
        cases hin : auxEntryIn acc e.addr e.params e.levels with
        | true =>
          simp only [hin, ↓reduceIte] at h
          exact ih (k + 1) acc res h
        | false =>
          simp only [hin, Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨xs, hxs, hall⟩ := ih (k + 1) (acc ++ [e]) res h
          refine ⟨e :: xs, by rw [hxs, List.append_assoc]; rfl, ?_⟩
          intro e' he'
          rcases List.mem_cons.mp he' with rfl | hmem
          · exact hc k _ hck
          · exact hall e' hmem

/-! ## `build_flat_block` -/

section Top

variable {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}

/-- **`KernelCheck::build_flat_block(rb, B, off)`** on a family record of a bounded run's store is
its model `FamilyFlatRecord.recordFlatAt`, represented exactly. The list is the types of the
primary block `P` (`primaryAt`) at the offset (`FamilyFlat.originals` of the block's members)
followed by auxiliary entries only (`es = os ++ xs`), the walk's (`auxWalk`).

Taken: the fallback block `B` is a block record of the store (`hcB`, `hmB`); the recursors' types
mention only their own level parameters (`hlv`); and the levels `param (off + j)` of the primary
block's types are below `2^32` (`hoff`). -/
theorem build_flat_block_spec (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hR : FamRecRecord E₀ rb crb rs) (hlv : RecLevelsDefined t E₀ rb crb rs)
    {bR bB : Bytes.Address} (hbR : ixAddr bR = rb)
    {cB : Ixon.Constant} {mB : Array Ixon.MutConst}
    (hcB : recordOf E₀ (ixAddr bB) = some cB) (hmB : cB.info = .muts mB) {off : Nat}
    (hoff : ∀ (P : _root_.Address) (cP : Ixon.Constant) (mP : Array Ixon.MutConst) (j : Nat)
      (ind : Ixon.Inductive), primaryAt t E₀ rb crb rs (ixAddr bB) = some P →
      recordOf E₀ P = some cP → cP.info = .muts mP → mP[j]? = some (Ixon.MutConst.indc ind) →
      off + ind.lvls.toNat < 4294967296)
    {x_rb x_b r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrb : Bytes.RepAddressRef addrTy h bR x_rb) (hb : Bytes.RepAddressRef addrTy h bB x_b)
    (ev : ObsFn W "KernelCheck::build_flat_block" [x_rb, x_b, .field (off : F)] h r h' cs)
    (hsub : ∀ c ∈ cs, c ∈ calls) :
    Heap.Extends h h' ∧
    ∃ (P : _root_.Address) (as : List _root_.Address) (os es xs : List FlatEntry),
      primaryAt t E₀ rb crb rs (ixAddr bB) = some P ∧
      membersAt E₀ P = some as ∧
      originals (FlatView.ofStore t E₀) off as = some os ∧
      auxWalk (contribAt t E₀ rb crb rs P) rs.size 0 os = some es ∧
      recordFlatAt t E₀ rb crb rs (ixAddr bB) off = some es ∧
      es = os ++ xs ∧ (∀ e ∈ xs, e.aux = true) ∧
      RepList flatListEnum (FlatEntryRepExact (keyOf t)) h' es r := by
  have hrec : recordOf E₀ (ixAddr bR) = some crb := by rw [hbR]; exact hR.record
  match Obs.«KernelCheck::build_flat_block».obs ev with
  | .n0 (cs73 := csM) (ev14 := evP) (ev44 := evO) (ev75 := evM) (hc91 := hc) .. =>
    have h1 := is_muts_block_of_muts hS
      (Bytes.repAddressRef_heapMono₂ addrTy (evP.heap_extends.trans evO.heap_extends) hrb)
      hrec hR.muts evM (fun c hc' => hsub c (by rw [hc]; simp [hc']))
    exact absurd (Value.field.inj h1) (by decide)
  | .other (cs12 := csP) (cs42 := csO) (cs73 := csM) (cs99 := csD) (ev14 := evP) (ev44 := evO)
      (ev75 := evM) (ev101 := evD) (hc134 := hc) .. =>
    obtain ⟨ext1, P, cP, mP, hprim, rP, hcP, hmP⟩ :=
      primary_parent_block_of_spec ht hbd hS hH hR hlv hbR hcB hmB hrb hb evP
        (fun c hc' => hsub c (by rw [hc]; simp [hc']))
    obtain ⟨ext2, os, hos, hrepO⟩ := build_flat_originals_spec (t := t) hbd hS hH hcP hmP
      (fun j ind hj => hoff _ cP mP j ind hprim hcP hmP hj) rP evO
      (fun c hc' => hsub c (by rw [hc]; simp [hc']))
    have ext3 := evM.heap_extends
    obtain ⟨ext4, es, hes, hrepE⟩ := detect_aux_from_recrs_ex_spec ht hbd hS hH hR hlv hbR
      (Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans (ext2.trans ext3)) hrb)
      (Bytes.repAddressRef_heapMono₂ addrTy (ext2.trans ext3) rP) (flatList_mono ext3 hrepO) evD
      (fun c hc' => hsub c (by rw [hc]; simp [hc']))
    obtain ⟨xs, hxs, haux⟩ := auxWalk_aux _ (fun k e hk => contribAt_aux hk) _ _ _ _ hes
    refine ⟨ext1.trans (ext2.trans (ext3.trans ext4)), ixAddr P, _, os, es, xs, hprim,
      membersAt_of hcP hmP, hos, hes, ?_, hxs, haux, hrepE⟩
    simp only [recordFlatAt, hprim, membersAt_of hcP hmP, hos, hes]

/-- **`build_flat_block` where the primary block is the block itself**: the list is the block's
own types at the offset followed by auxiliary entries only. -/
theorem build_flat_block_at_block (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hR : FamRecRecord E₀ rb crb rs) (hlv : RecLevelsDefined t E₀ rb crb rs)
    {bR bB : Bytes.Address} (hbR : ixAddr bR = rb)
    {cB : Ixon.Constant} {mB : Array Ixon.MutConst}
    (hcB : recordOf E₀ (ixAddr bB) = some cB) (hmB : cB.info = .muts mB) {off : Nat}
    (hprim : primaryAt t E₀ rb crb rs (ixAddr bB) = some (ixAddr bB))
    (hoff : ∀ (j : Nat) (ind : Ixon.Inductive), mB[j]? = some (Ixon.MutConst.indc ind) →
      off + ind.lvls.toNat < 4294967296)
    {x_rb x_b r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrb : Bytes.RepAddressRef addrTy h bR x_rb) (hb : Bytes.RepAddressRef addrTy h bB x_b)
    (ev : ObsFn W "KernelCheck::build_flat_block" [x_rb, x_b, .field (off : F)] h r h' cs)
    (hsub : ∀ c ∈ cs, c ∈ calls) :
    Heap.Extends h h' ∧
    ∃ (as : List _root_.Address) (os es xs : List FlatEntry),
      membersAt E₀ (ixAddr bB) = some as ∧
      originals (FlatView.ofStore t E₀) off as = some os ∧
      recordFlatAt t E₀ rb crb rs (ixAddr bB) off = some es ∧
      es = os ++ xs ∧ (∀ e ∈ xs, e.aux = true) ∧
      RepList flatListEnum (FlatEntryRepExact (keyOf t)) h' es r := by
  obtain ⟨ext, P, as, os, es, xs, hP, hmem, hos, -, hmodel, hxs, haux, hrep⟩ :=
    build_flat_block_spec ht hbd hS hH hR hlv hbR hcB hmB
      (fun P cP mP j ind hP hcP hmP hj => by
        have hPB : P = ixAddr bB := Option.some.inj (hP.symm.trans hprim)
        subst hPB
        have e1 : cP = cB := Option.some.inj (hcP.symm.trans hcB)
        subst e1
        have e2 : mP = mB := Ixon.ConstantInfo.muts.inj (hmP.symm.trans hmB)
        subst e2
        exact hoff j ind hj) hrb hb ev hsub
  have hPB : P = ixAddr bB := Option.some.inj (hP.symm.trans hprim)
  subst hPB
  exact ⟨ext, as, os, es, xs, hmem, hos, hmodel, hxs, haux, hrep⟩

/-! ## The hypotheses, from the record and its family check -/

/-- **The primary block of a record whose first recursor is over the block's first type is the
block itself**: the first recursor's major premise is headed by the first type of `B`. -/
theorem primaryAt_of_origHead {B rb : _root_.Address} {cb crb : Ixon.Constant}
    {ms rs : Array Ixon.MutConst} (ht : t.check = .ok ())
    (hB : FamBlockRecord E₀ B cb ms) (hR : FamRecRecord E₀ rb crb rs) (hpos : 0 < ms.size)
    (horigHead : ∀ (r : Ixon.Recursor) (ind : Ixon.Inductive),
      rs[0]? = some (Ixon.MutConst.recr r) → ms[0]? = some (Ixon.MutConst.indc ind) →
      ∃ ty d ls, loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) r.lvls.toNat
          (mutsRoot rs 0) r.typ = some ty ∧
        binderDomAfter (r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat) ty =
          some d ∧
        Ix.Kernel.Expr.getAppFn d = .const (keyOf t (memberAddr B 0 (.indc ind))) ls) :
    primaryAt t E₀ rb crb rs B = some B := by
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  unfold primaryAt
  cases h0 : rs[0]? with
  | none => rfl
  | some m0 =>
    obtain ⟨r0, rfl⟩ := hR.recrs m0
      (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact h0))
    have hm0 : ms[0]? = some ms[0] := Array.getElem?_eq_getElem hpos
    obtain ⟨ind0, hind0⟩ := hB.indcs _
      (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hm0))
    rw [hind0] at hm0
    obtain ⟨ty, d, ls, hty, hd, hfn⟩ := horigHead r0 ind0 h0 hm0
    have hmaj : majorAt t E₀ rb crb rs 0 =
        some (d, r0.motives.toNat + r0.minors.toNat + r0.indices.toNat) := by
      simp only [majorAt, h0, hty, hd]
    simp only [hmaj, hfn, constOf, keyAddr_keyOf htwf, indInfoAt_member hB hm0 (by decide)]

open IxVM.Refinement.Core in
/-- **The types of the recursors of the family record of an observed family check mention only
their own level parameters** (`KernelModeled::check_recs` validates each one's scoping). -/
theorem recLevelsDefined_of_call {bAddr : _root_.Address} {B rb : _root_.Address}
    {lim : Option Nat} {cs : List (Call F)} (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs)
    {crb : Ixon.Constant} {rs : Array Ixon.MutConst} (hR : FamRecRecord E₀ rb crb rs) :
    RecLevelsDefined t E₀ rb crb rs := by
  obtain ⟨h, h', rcV, xb, xrb, r, -, ⟨bB, hbB, rfl⟩, ⟨bR, hbR, rfl⟩, ev, -, hsub⟩ := hfc
  obtain ⟨C⟩ := FamilyAlias.checkFamily_chain ev
  have ext_0_453 : Heap.Extends h C.m453 :=
    (check_family_seg1_extends C.sg112).trans C.ext_m105_m453
  have ext_501_652 : Heap.Extends C.m501 C.m652 :=
    C.evLenMem.extends.trans (C.evIndcCnt.extends.trans C.evNParams.extends)
  have ext_674_784 : Heap.Extends C.m674 C.m784 :=
    C.evTypeMods.extends.trans (C.evCtors.extends.trans
      (C.evLenCtors.extends.trans C.evCtorMods.extends))
  have ext_0_784 : Heap.Extends h C.m784 :=
    ext_0_453.trans (C.evLoadBlk.extends.trans (ext_501_652.trans
      (C.evTypes.extends.trans ext_674_784)))
  have hbR784 : Bytes.RepAddressRef addrTy C.m784 bR xrb :=
    Bytes.repAddressRef_heapMono₂ addrTy ext_0_784 hbR
  have hsubRecs : ∀ cl ∈ C.evRecs.cs, cl ∈ calls :=
    fun cl hcl => hsub cl (C.evRecs.sub cl hcl)
  obtain ⟨as_rc, has_rc, hmap_rc⟩ :=
    FamilyAlias.family_recs_list hH hbR784 C.evRecs.obs hsubRecs hR
  have hrsz := FamilyAlias.family_recs_bound hS hH hbR784 C.evRecs.obs hsubRecs hR
  have ext_840_978 : Heap.Extends C.m840 C.m978 :=
    C.evNoRole.extends.trans (C.evNoTypeRole.extends.trans (C.evLenRecs.extends.trans
      (C.evRecMods.extends.trans (C.evSrcTail.extends.trans (C.evSrc.extends.trans
        (C.evDstTail.extends.trans C.evDst.extends))))))
  have ext_840_1293 : Heap.Extends C.m840 C.m1293 := ext_840_978.trans C.ext_m978_m1293
  have has_rc1293 := repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ addrTy)
    ext_840_1293 has_rc
  have hsubLoop : FamilyAlias.CallSub C.evCheckRecs.cs calls :=
    fun cl hcl => hsub cl (C.evCheckRecs.sub cl hcl)
  intro k rc v hrk hread
  have hklt : k < rs.size := (Array.getElem?_eq_some_iff.mp hrk).1
  have hkL : rs.toList[k]? = some (.recr rc) := by rw [Array.getElem?_toList]; exact hrk
  have h1 : (as_rc.map ixAddr)[k]? = some (rprjAddr (ixAddr bR) k) := by
    rw [hmap_rc, List.getElem?_mapIdx, hkL]
    rfl
  rw [List.getElem?_map] at h1
  obtain ⟨aRec, ha_k, haRec_eq⟩ := Option.map_eq_some_iff.mp h1
  obtain ⟨recs', models', s', kV', form', r', h1, h1', cs1, C', ext1, hsub1, haRec_rep⟩ :=
    FamilyOfCall.checkRecs_member as_rc has_rc1293 C.evCheckRecs.obs k aRec ha_k
  have hsubC : FamilyAlias.CallSub cs1 calls := fun cl hcl => hsubLoop cl (hsub1 cl hcl)
  have hk_u64 : k < UInt64.size := Nat.lt_trans hklt (Nat.lt_trans hrsz (by decide))
  have hsub_getRec : FamilyAlias.CallSub C'.evGetRec.cs calls :=
    fun cl hcl => hsubC cl (C'.evGetRec.sub cl hcl)
  obtain ⟨_, cRec, hhRec, hbaRec, hexRec, -, htrRec⟩ :=
    L1.get_ci_block_trace_spec (bounded_sub hsub_getRec hbd) haRec_rep C'.evGetRec.obs
  have hrecAtRec : Ix.Cert.recordAt E₀ (ixAddr aRec) =
      some (memberProjection (ixAddr bR) k (.recr rc)) := by
    rw [← hS.recordOf_eq_recordAt, haRec_eq, ← LoadedReads.memberAddr_recr]
    exact hR.members k (.recr rc) hrk
  have hcRec_eq : cRec = memberProjection (ixAddr bR) k (.recr rc) :=
    hS.record_eq hrecAtRec (Core.hashed_mono hsub_getRec hhRec) hbaRec hexRec
  subst hcRec_eq
  unfold L1.GetCIBlockTraceResult at htrRec
  simp only [memberProjection] at htrRec
  obtain ⟨_, _, crb', rs', rc', blobs, tree, vRec, hhBlk, hbaBlk, hexBlk, hmuts', hrk', hhp,
      built, hldv, hrepRec⟩ := htrRec
  have hcrb_eq : crb' = crb :=
    hS.record_eq ((hS.recordOf_eq_recordAt (ixAddr bR)).symm.trans hR.record)
      (Core.hashed_mono hsub_getRec hhBlk) hbaBlk hexBlk
  subst crb'
  have hrs_eq : rs' = rs := Ixon.ConstantInfo.muts.inj (hmuts'.symm.trans hR.muts)
  subst rs'
  have hk_toNat : k.toUInt64.toNat = k := toUInt64_toNat_of_lt hk_u64
  rw [hk_toNat, Array.getElem?_toList, hrk] at hrk'
  have hrc_eq : rc' = rc := Ixon.MutConst.recr.inj (Option.some.inj hrk').symm
  subst rc'
  rw [hk_toNat] at hrepRec
  obtain ⟨hlvls_lt, hnp_lt, hni_lt, hnmot_lt, hnmin_lt, hk_lt, tyPtr, rulesPtr, blkPtr, bBlk,
      planT, hbBlk_eq, hbBlk_ref, hvRec_eq, rty, hpT, hlT, hrlsTrace⟩ := hrepRec
  have hvRec_ld := Except.ok.inj (C'.ldRec.symm.trans hldv)
  rw [hvRec_eq] at hvRec_ld
  injection hvRec_ld with _ _ hargs_r
  injection hargs_r with hnl_eq hargs_r
  injection hargs_r with hty_eq hargs_r
  subst hty_eq
  have hcall_scope : (⟨"KernelCheck::validate_expr_well_scoped",
      [C'.ty, .field 0, .field (rc.lvls.toNat : F)], C'.m473⟩ : Call F) ∈ calls := by
    rw [← hnl_eq]; exact hsubC _ C'.evScope.mem
  have evScope' : ObsFn Obs.W "KernelCheck::validate_expr_well_scoped"
      [C'.ty, .field 0, .field (rc.lvls.toNat : F)] C'.m473 C'.vScope C'.m511 C'.evScope.cs := by
    rw [← hnl_eq]; exact C'.evScope.obs
  obtain ⟨_, -, hdef⟩ :=
    Assembly.validate_expr_well_scoped_spec hbd hlvls_lt rty
      (C'.ext391.trans C'.evCarriers.extends) hread evScope' hcall_scope
  exact hdef

end Top

end IxVM.Refinement.Binding.FamilyFlatBuild
