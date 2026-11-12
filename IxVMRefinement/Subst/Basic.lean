import IxVMRefinement.Core.Registry
import IxVMRefinement.Core.Open
import IxVMRefinement.Core.Window
import IxVMRefinement.Lib.Lists
import IxVMRefinement.Obs.KernelSubst0
import IxVMRefinement.Obs.KernelSubst1
import IxVMRefinement.Obs.UInt320
import Ix.IxVM.Refinement.KernelLevels
import IxC.Kernel.Verify.Subst
import IxC.Kernel.Verify.InstList
import IxC.Kernel.Verify.InstLevels

/-! # Substitution: field arithmetic, heap indices, kernel algebra

The facts the substitution package's step lemmas share.

* **Fields.** IxVM computes indices, depths and shifts in the field; every value the step
  lemmas read is below `2^63` or compared by `UInt32::less_than_fields`, which bounds both sides
  by `2^32` (`ltf`), so the field arithmetic is the natural one.
* **Heap indices.** `IdxAll` is read and built at a loaded cell (`idxAll_*_inv`,
  `idxAll_*_of_load`) and weakened with an offset (`idxAll_imp`). A represented term's indices
  are below `2^63` and below `k + n + d` under `n` binders (`tm_idxAll`); its image's loose
  bound variables are below any `lo` no heap index lies in `[lo, k)` of (`tm_lbb`); and a heap
  bound `b ≤ k` gives `LbrLe` (`lbrLe_of_idxLt`). `NoIdxF` is `NoIdx` for a represented term
  whose window ends at least `2^63` below the field's size (`noIdx_of_noIdxF_tm`).
* **Kernel algebra.** A `Let` node's image is `instShift` (the kernel's `instantiate1Lift`):
  its bounds (`lbb_instShift0`, `hasFvar_instShift`) and its commutation with
  `instantiate1`, `instantiateList` (closed values) and level instantiation.
* **Stores.** A new node of represented components is represented (`tm_store_*`), and a leaf
  node copied to a new cell is represented at every reading (`tm_copy_*`). -/

namespace IxVM.Refinement.Core.SubstAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open Specs.Subst (IdxAll IdxLt NoIdx NoIdxF BVarIm idxBound)

set_option linter.unusedVariables false

/-! ## Field values -/

theorem natCast_val (x : F) : ((ZMod.val x : Nat) : F) = x := ZMod.natCast_zmod_val x

theorem val_natCast {n : Nat} (hn : n < Aiur.Library.U32.Goldilocks.modulus) :
    ZMod.val (n : F) = n :=
  ZMod.val_natCast_of_lt hn

theorem val_one : ZMod.val (1 : F) = 1 := by
  have := ZMod.val_natCast_of_lt (n := Aiur.Library.U32.Goldilocks.modulus) (a := 1) (by decide)
  simpa using this

theorem val_add {x y : F} (h : ZMod.val x + ZMod.val y < Aiur.Library.U32.Goldilocks.modulus) :
    ZMod.val (x + y) = ZMod.val x + ZMod.val y :=
  ZMod.val_add_of_lt h

/-- `x + 1`, read as a natural, is `x + 1` or wraps to `0`. -/
theorem val_add_one_cases (x : F) :
    (ZMod.val x + 1 < Aiur.Library.U32.Goldilocks.modulus ∧ ZMod.val (x + 1) = ZMod.val x + 1) ∨
      (ZMod.val x + 1 = Aiur.Library.U32.Goldilocks.modulus ∧ ZMod.val (x + 1) = 0) := by
  have hv := ZMod.val_add x 1
  rw [val_one] at hv
  have := ZMod.val_lt x
  by_cases h : ZMod.val x + 1 < Aiur.Library.U32.Goldilocks.modulus
  · exact .inl ⟨h, by rw [hv, Nat.mod_eq_of_lt h]⟩
  · refine .inr ⟨by omega, ?_⟩
    rw [hv, show ZMod.val x + 1 = Aiur.Library.U32.Goldilocks.modulus by omega, Nat.mod_self]

theorem val_add_one {x : F} (h : ZMod.val x + 1 < Aiur.Library.U32.Goldilocks.modulus) :
    ZMod.val (x + 1) = ZMod.val x + 1 := by
  rcases val_add_one_cases x with ⟨_, e⟩ | ⟨e, _⟩
  · exact e
  · omega

theorem val_sub {x y : F} (h : ZMod.val y ≤ ZMod.val x) :
    ZMod.val (x - y) = ZMod.val x - ZMod.val y :=
  ZMod.val_sub h

/-! ## Binary operations -/

theorem binop_fields {op : BinOp} {a b r : SourceValue F} (hop : evalBinOp op a b = .ok r) :
    ∃ x y : F, a = .field x ∧ b = .field y := by
  cases a <;> cases b <;> first | exact ⟨_, _, rfl, rfl⟩ | cases hop

theorem add_ok {a b : F} {r : SourceValue F}
    (hop : evalBinOp .add (.field a : SourceValue F) (.field b) = .ok r) : r = .field (a + b) :=
  (Except.ok.inj hop).symm

theorem sub_ok {a b : F} {r : SourceValue F}
    (hop : evalBinOp .sub (.field a : SourceValue F) (.field b) = .ok r) : r = .field (a - b) :=
  (Except.ok.inj hop).symm

theorem binop_field {op : BinOp} {a b r : SourceValue F} (hop : evalBinOp op a b = .ok r) :
    ∃ z : F, r = .field z := by
  obtain ⟨x, y, rfl, rfl⟩ := binop_fields hop
  cases op with
  | add => exact ⟨_, (Except.ok.inj hop).symm⟩
  | sub => exact ⟨_, (Except.ok.inj hop).symm⟩
  | mul => exact ⟨_, (Except.ok.inj hop).symm⟩
  | div =>
    by_cases hy : y = 0
    · simp [evalBinOp, hy] at hop
    · simp [evalBinOp, hy] at hop; exact ⟨_, hop.symm⟩

/-! ## `UInt32::less_than_fields` -/

/-- **An observed comparison**: both sides are field elements below `2^32`, the answer is
`1` exactly on `<`, and the heap is unchanged. -/
theorem ltf {a b r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt32::less_than_fields" [a, b] h r h' cs) :
    ∃ x y : F, a = .field x ∧ b = .field y ∧ ZMod.val x < 4294967296 ∧
      ZMod.val y < 4294967296 ∧ r = .field (if ZMod.val x < ZMod.val y then 1 else 0) ∧
      h' = h := by
  have fields : ∃ x y : F, a = .field x ∧ b = .field y := by
    match Obs.«UInt32::less_than_fields».obs ev with
    | .run (op219 := hadd) (op211 := hsub) .. =>
      obtain ⟨_, y, -, rfl⟩ := binop_fields hadd
      obtain ⟨_, x, -, rfl⟩ := binop_fields hsub
      exact ⟨x, y, rfl, rfl⟩
  obtain ⟨x, y, rfl, rfl⟩ := fields
  have e : EvalFn W "UInt32::less_than_fields"
      [.field ((ZMod.val x : Nat) : F), .field ((ZMod.val y : Nat) : F)] h r h' := by
    simpa only [natCast_val] using ev.erase
  obtain ⟨hx, hy, hr, hh⟩ := KernelLevels.u32LessThanFields_bounded (ZMod.val_lt x) (ZMod.val_lt y) e
  exact ⟨x, y, rfl, rfl, hx, hy, hr, hh⟩

/-- The comparison answered `1`. -/
theorem ltf_one {x y : F} (hr : (Value.field (if ZMod.val x < ZMod.val y then 1 else 0) :
    SourceValue F) = .field 1) : ZMod.val x < ZMod.val y := by
  split at hr
  · assumption
  · injection hr with hr; exact absurd hr (by decide)

/-- The comparison answered `0`. -/
theorem ltf_zero {x y : F} (hr : (Value.field (if ZMod.val x < ZMod.val y then 1 else 0) :
    SourceValue F) = .field 0) : ¬ ZMod.val x < ZMod.val y := by
  split at hr
  · injection hr with hr; exact absurd hr (by decide)
  · assumption

/-! ## Loads -/

/-- **A load that returns a cell reads a pointer to it.** -/
theorem load_ptr {heap : Heap F} {p : SourceValue F} {en c : String} {xs : List (SourceValue F)}
    (hl : loadValue heap p = .ok (.construct en c xs)) :
    ∃ addr, p = .ptr (.enum en) addr ∧ heap[addr]? = some (.construct en c xs) := by
  cases p with
  | field | tuple | construct => cases hl
  | ptr t addr =>
    cases found : heap[addr]? with
    | none => simp [loadValue, found] at hl
    | some stored =>
      by_cases ht : stored.type = t
      · have hs : stored = .construct en c xs := by
          simpa [loadValue, found, ht, bind, Except.bind, pure, Except.pure] using hl
        subst hs
        simp only [Value.type] at ht
        subst ht
        exact ⟨addr, rfl, found⟩
      · simp [loadValue, found, ht] at hl

/-! ## Heap indices -/

/-- **Weakening with an offset.** -/
theorem idxAll_imp {h : Heap F} {P Q : Nat → F → Prop} :
    ∀ {m : Nat} {p : SourceValue F}, IdxAll h P m p →
      ∀ {m' : Nat}, (∀ n i, P (m + n) i → Q (m' + n) i) → IdxAll h Q m' p := by
  intro m p hp
  induction hp with
  | bvar cell hP =>
    intro m' hPQ; exact .bvar cell (by simpa using hPQ 0 _ (by simpa using hP))
  | sort cell => intro m' _; exact .sort cell
  | const cell => intro m' _; exact .const cell
  | lit cell => intro m' _; exact .lit cell
  | app cell _ _ ihf iha => intro m' hPQ; exact .app cell (ihf hPQ) (iha hPQ)
  | @lam m addr tp bp lp cell _ _ iht ihb =>
    intro m' hPQ
    refine .lam cell (iht hPQ) (ihb ?_)
    intro n i hi
    have := hPQ (n + 1) i (by rwa [show m + (n + 1) = m + 1 + n by omega])
    rwa [show m' + (n + 1) = m' + 1 + n by omega] at this
  | @forallE m addr tp bp lp cell _ _ iht ihb =>
    intro m' hPQ
    refine .forallE cell (iht hPQ) (ihb ?_)
    intro n i hi
    have := hPQ (n + 1) i (by rwa [show m + (n + 1) = m + 1 + n by omega])
    rwa [show m' + (n + 1) = m' + 1 + n by omega] at this
  | @letE m addr tp vp bp cell _ _ _ iht ihv ihb =>
    intro m' hPQ
    refine .letE cell (iht hPQ) (ihv hPQ) (ihb ?_)
    intro n i hi
    have := hPQ (n + 1) i (by rwa [show m + (n + 1) = m + 1 + n by omega])
    rwa [show m' + (n + 1) = m' + 1 + n by omega] at this
  | proj cell _ ihe => intro m' hPQ; exact .proj cell (ihe hPQ)

/-- Weakening at the same offset. -/
theorem idxAll_mono {h : Heap F} {P Q : Nat → F → Prop} {m : Nat} {p : SourceValue F}
    (hp : IdxAll h P m p) (hPQ : ∀ n i, P n i → Q n i) : IdxAll h Q m p :=
  idxAll_imp hp (fun n i hi => hPQ _ _ hi)

/-- **Two facts about every index give their conjunction.** -/
theorem idxAll_and {h : Heap F} {P Q : Nat → F → Prop} :
    ∀ {m : Nat} {p : SourceValue F}, IdxAll h P m p → IdxAll h Q m p →
      IdxAll h (fun n i => P n i ∧ Q n i) m p := by
  intro m p hp
  induction hp with
  | bvar cell hP =>
    intro hq
    cases hq with
    | bvar cell' hQ =>
      rw [cell] at cell'
      injection cell' with hc; injection hc with _ _ hxs; injection hxs with hx
      injection hx with hx; subst hx
      exact .bvar cell ⟨hP, hQ⟩
    | sort cell' | const cell' | lit cell' | app cell' _ _ | lam cell' _ _ | forallE cell' _ _
    | letE cell' _ _ _ | proj cell' _ =>
      rw [cell] at cell'; injection cell' with hc; injection hc with _ hc; exact absurd hc (by decide)
  | sort cell => intro _; exact .sort cell
  | const cell => intro _; exact .const cell
  | lit cell => intro _; exact .lit cell
  | app cell _ _ ihf iha =>
    intro hq
    cases hq with
    | app cell' hf ha =>
      rw [cell] at cell'
      injection cell' with hc; injection hc with _ _ hxs
      injection hxs with hx hrest; injection hrest with hy
      subst hx hy
      exact .app cell (ihf hf) (iha ha)
    | bvar cell' _ | sort cell' | const cell' | lit cell' | lam cell' _ _ | forallE cell' _ _
    | letE cell' _ _ _ | proj cell' _ =>
      rw [cell] at cell'; injection cell' with hc; injection hc with _ hc; exact absurd hc (by decide)
  | lam cell _ _ iht ihb =>
    intro hq
    cases hq with
    | lam cell' ht hb =>
      rw [cell] at cell'
      injection cell' with hc; injection hc with _ _ hxs
      injection hxs with hx hrest; injection hrest with hy
      subst hx hy
      exact .lam cell (iht ht) (ihb hb)
    | bvar cell' _ | sort cell' | const cell' | lit cell' | app cell' _ _ | forallE cell' _ _
    | letE cell' _ _ _ | proj cell' _ =>
      rw [cell] at cell'; injection cell' with hc; injection hc with _ hc; exact absurd hc (by decide)
  | forallE cell _ _ iht ihb =>
    intro hq
    cases hq with
    | forallE cell' ht hb =>
      rw [cell] at cell'
      injection cell' with hc; injection hc with _ _ hxs
      injection hxs with hx hrest; injection hrest with hy
      subst hx hy
      exact .forallE cell (iht ht) (ihb hb)
    | bvar cell' _ | sort cell' | const cell' | lit cell' | app cell' _ _ | lam cell' _ _
    | letE cell' _ _ _ | proj cell' _ =>
      rw [cell] at cell'; injection cell' with hc; injection hc with _ hc; exact absurd hc (by decide)
  | letE cell _ _ _ iht ihv ihb =>
    intro hq
    cases hq with
    | letE cell' ht hv hb =>
      rw [cell] at cell'
      injection cell' with hc; injection hc with _ _ hxs
      injection hxs with hx hrest; injection hrest with hy hrest'; injection hrest' with hz
      subst hx hy hz
      exact .letE cell (iht ht) (ihv hv) (ihb hb)
    | bvar cell' _ | sort cell' | const cell' | lit cell' | app cell' _ _ | lam cell' _ _
    | forallE cell' _ _ | proj cell' _ =>
      rw [cell] at cell'; injection cell' with hc; injection hc with _ hc; exact absurd hc (by decide)
  | proj cell _ ihe =>
    intro hq
    cases hq with
    | proj cell' he =>
      rw [cell] at cell'
      injection cell' with hc; injection hc with _ _ hxs
      injection hxs with hx hrest; injection hrest with hy hrest'; injection hrest' with hz
      subst hz
      exact .proj cell (ihe he)
    | bvar cell' _ | sort cell' | const cell' | lit cell' | app cell' _ _ | lam cell' _ _
    | forallE cell' _ _ | letE cell' _ _ _ =>
      rw [cell] at cell'; injection cell' with hc; injection hc with _ hc; exact absurd hc (by decide)

section Inv
variable {h : Heap F} {P : Nat → F → Prop} {m : Nat} {p : SourceValue F}

theorem idxAll_bvar_inv {x : SourceValue F} (hp : IdxAll h P m p)
    (ld : loadValue h p = .ok (.construct kexprEnum "BVar" [x])) : ∃ i : F, x = .field i ∧ P m i := by
  cases hp with
  | bvar cell hP =>
    obtain ⟨-, hxs⟩ := load_cell cell ld
    injection hxs with hx; exact ⟨_, hx.symm, hP⟩
  | sort cell | const cell | lit cell | app cell _ _ | lam cell _ _ | forallE cell _ _
  | letE cell _ _ _ | proj cell _ => exact (load_cell_ne cell ld (by decide)).elim

theorem idxAll_app_inv {x y : SourceValue F} (hp : IdxAll h P m p)
    (ld : loadValue h p = .ok (.construct kexprEnum "App" [x, y])) :
    IdxAll h P m x ∧ IdxAll h P m y := by
  cases hp with
  | app cell hf ha =>
    obtain ⟨-, hxs⟩ := load_cell cell ld
    injection hxs with hx hrest; injection hrest with hy
    subst hx hy; exact ⟨hf, ha⟩
  | bvar cell _ | sort cell | const cell | lit cell | lam cell _ _ | forallE cell _ _
  | letE cell _ _ _ | proj cell _ => exact (load_cell_ne cell ld (by decide)).elim

theorem idxAll_lam_inv {x y z : SourceValue F} (hp : IdxAll h P m p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Lam" [x, y, z])) :
    IdxAll h P m x ∧ IdxAll h P (m + 1) y := by
  cases hp with
  | lam cell ht hb =>
    obtain ⟨-, hxs⟩ := load_cell cell ld
    injection hxs with hx hrest; injection hrest with hy
    subst hx hy; exact ⟨ht, hb⟩
  | bvar cell _ | sort cell | const cell | lit cell | app cell _ _ | forallE cell _ _
  | letE cell _ _ _ | proj cell _ => exact (load_cell_ne cell ld (by decide)).elim

theorem idxAll_forallE_inv {x y z : SourceValue F} (hp : IdxAll h P m p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Forall" [x, y, z])) :
    IdxAll h P m x ∧ IdxAll h P (m + 1) y := by
  cases hp with
  | forallE cell ht hb =>
    obtain ⟨-, hxs⟩ := load_cell cell ld
    injection hxs with hx hrest; injection hrest with hy
    subst hx hy; exact ⟨ht, hb⟩
  | bvar cell _ | sort cell | const cell | lit cell | app cell _ _ | lam cell _ _
  | letE cell _ _ _ | proj cell _ => exact (load_cell_ne cell ld (by decide)).elim

theorem idxAll_letE_inv {x y z : SourceValue F} (hp : IdxAll h P m p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Let" [x, y, z])) :
    IdxAll h P m x ∧ IdxAll h P m y ∧ IdxAll h P (m + 1) z := by
  cases hp with
  | letE cell ht hv hb =>
    obtain ⟨-, hxs⟩ := load_cell cell ld
    injection hxs with hx hrest; injection hrest with hy hrest'; injection hrest' with hz
    subst hx hy hz; exact ⟨ht, hv, hb⟩
  | bvar cell _ | sort cell | const cell | lit cell | app cell _ _ | lam cell _ _
  | forallE cell _ _ | proj cell _ => exact (load_cell_ne cell ld (by decide)).elim

theorem idxAll_proj_inv {x y z : SourceValue F} (hp : IdxAll h P m p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Proj" [x, y, z])) : IdxAll h P m z := by
  cases hp with
  | proj cell he =>
    obtain ⟨-, hxs⟩ := load_cell cell ld
    injection hxs with hx hrest; injection hrest with hy hrest'; injection hrest' with hz
    subst hz; exact he
  | bvar cell _ | sort cell | const cell | lit cell | app cell _ _ | lam cell _ _
  | forallE cell _ _ | letE cell _ _ _ => exact (load_cell_ne cell ld (by decide)).elim

theorem idxAll_bvar_of_load {i : F} (ld : loadValue h p = .ok (.construct kexprEnum "BVar" [.field i]))
    (hP : P m i) : IdxAll h P m p := by
  obtain ⟨addr, rfl, cell⟩ := load_ptr ld; exact .bvar cell hP

theorem idxAll_sort_of_load {x : SourceValue F}
    (ld : loadValue h p = .ok (.construct kexprEnum "Srt" [x])) : IdxAll h P m p := by
  obtain ⟨addr, rfl, cell⟩ := load_ptr ld; exact .sort cell

theorem idxAll_const_of_load {x y : SourceValue F}
    (ld : loadValue h p = .ok (.construct kexprEnum "Const" [x, y])) : IdxAll h P m p := by
  obtain ⟨addr, rfl, cell⟩ := load_ptr ld; exact .const cell

theorem idxAll_lit_of_load {x : SourceValue F}
    (ld : loadValue h p = .ok (.construct kexprEnum "Lit" [x])) : IdxAll h P m p := by
  obtain ⟨addr, rfl, cell⟩ := load_ptr ld; exact .lit cell

theorem idxAll_app_of_load {x y : SourceValue F}
    (ld : loadValue h p = .ok (.construct kexprEnum "App" [x, y]))
    (hx : IdxAll h P m x) (hy : IdxAll h P m y) : IdxAll h P m p := by
  obtain ⟨addr, rfl, cell⟩ := load_ptr ld; exact .app cell hx hy

theorem idxAll_lam_of_load {x y z : SourceValue F}
    (ld : loadValue h p = .ok (.construct kexprEnum "Lam" [x, y, z]))
    (hx : IdxAll h P m x) (hy : IdxAll h P (m + 1) y) : IdxAll h P m p := by
  obtain ⟨addr, rfl, cell⟩ := load_ptr ld; exact .lam cell hx hy

theorem idxAll_forallE_of_load {x y z : SourceValue F}
    (ld : loadValue h p = .ok (.construct kexprEnum "Forall" [x, y, z]))
    (hx : IdxAll h P m x) (hy : IdxAll h P (m + 1) y) : IdxAll h P m p := by
  obtain ⟨addr, rfl, cell⟩ := load_ptr ld; exact .forallE cell hx hy

theorem idxAll_letE_of_load {x y z : SourceValue F}
    (ld : loadValue h p = .ok (.construct kexprEnum "Let" [x, y, z]))
    (hx : IdxAll h P m x) (hy : IdxAll h P m y) (hz : IdxAll h P (m + 1) z) : IdxAll h P m p := by
  obtain ⟨addr, rfl, cell⟩ := load_ptr ld; exact .letE cell hx hy hz

theorem idxAll_proj_of_load {x y z : SourceValue F}
    (ld : loadValue h p = .ok (.construct kexprEnum "Proj" [x, y, z]))
    (hz : IdxAll h P m z) : IdxAll h P m p := by
  obtain ⟨addr, rfl, cell⟩ := load_ptr ld; exact .proj cell hz

end Inv

/-- A binder body's fact at offset `1`, as a fact at offset `0` one binder deeper. -/
theorem idxAll_body {h : Heap F} {P : Nat → F → Prop} {p : SourceValue F}
    (hp : IdxAll h P 1 p) : IdxAll h (fun n i => P (n + 1) i) 0 p :=
  idxAll_imp hp (fun n i hi => by simpa [Nat.add_comm] using hi)

/-- The converse of `idxAll_body`. -/
theorem idxAll_unbody {h : Heap F} {P : Nat → F → Prop} {p : SourceValue F}
    (hp : IdxAll h (fun n i => P (n + 1) i) 0 p) : IdxAll h P 1 p :=
  idxAll_imp hp (fun n i hi => by simpa [Nat.add_comm] using hi)

/-! ## Kernel algebra -/

section Kernel
open Ix.Kernel

theorem lbb_mono {k k' : Nat} (hk : k ≤ k') {e : KExpr} (he : e.looseBVarsBounded k = true) :
    e.looseBVarsBounded k' = true :=
  Expr.looseBVarsBounded_mono hk he

/-- **A `Let`'s image keeps a bound**: with the value below `b` and the body below `b + 1`. -/
theorem lbb_instShift0 {v e : KExpr} {b : Nat} (hv : v.looseBVarsBounded b = true)
    (he : e.looseBVarsBounded (b + 1) = true) : (instShift v 0 e).looseBVarsBounded b = true :=
  looseBVarsBounded_instantiate1Lift (Nat.zero_le b) he (by simpa using hv)

theorem hasFvar_lift (s : Nat) : ∀ (e : KExpr) (c : Nat), (e.liftLooseBVars s c).hasFvar = e.hasFvar := by
  intro e
  induction e with
  | bvar i => intro c; simp only [Expr.liftLooseBVars]; split <;> rfl
  | fvar i ty _ => intro c; rfl
  | sort u => intro c; rfl
  | const n us => intro c; rfl
  | app f a ihf iha => intro c; simp [Expr.liftLooseBVars, Expr.hasFvar, ihf, iha]
  | lam ty body m iht ihb => intro c; simp [Expr.liftLooseBVars, Expr.hasFvar, iht, ihb]
  | forallE ty body m iht ihb => intro c; simp [Expr.liftLooseBVars, Expr.hasFvar, iht, ihb]
  | letE ty val body m iht ihv ihb =>
    intro c; simp [Expr.liftLooseBVars, Expr.hasFvar, iht, ihv, ihb]
  | lit l => intro c; rfl
  | proj s i e ihe => intro c; simp [Expr.liftLooseBVars, Expr.hasFvar, ihe]

/-- **A `Let`'s image has no opened variable** when its value and body have none. -/
theorem hasFvar_instShift {v : KExpr} (hv : v.hasFvar = false) :
    ∀ (e : KExpr) (j : Nat), e.hasFvar = false → (instShift v j e).hasFvar = false := by
  intro e
  induction e with
  | bvar i =>
    intro j _
    simp only [instShift, Expr.instantiate1Lift]
    split
    · rw [hasFvar_lift]; exact hv
    · split <;> rfl
  | fvar i ty _ => intro j he; exact he
  | sort u => intro j _; rfl
  | const n us => intro j _; rfl
  | app f a ihf iha =>
    intro j he
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at he
    simp only [instShift, Expr.instantiate1Lift, Expr.hasFvar, Bool.or_eq_false_iff]
    exact ⟨ihf j he.1, iha j he.2⟩
  | lam ty body m iht ihb =>
    intro j he
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at he
    simp only [instShift, Expr.instantiate1Lift, Expr.hasFvar, Bool.or_eq_false_iff]
    exact ⟨iht j he.1, ihb (j + 1) he.2⟩
  | forallE ty body m iht ihb =>
    intro j he
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at he
    simp only [instShift, Expr.instantiate1Lift, Expr.hasFvar, Bool.or_eq_false_iff]
    exact ⟨iht j he.1, ihb (j + 1) he.2⟩
  | letE ty val body m iht ihv ihb =>
    intro j he
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at he
    simp only [instShift, Expr.instantiate1Lift, Expr.hasFvar, Bool.or_eq_false_iff]
    exact ⟨⟨iht j he.1.1, ihv j he.1.2⟩, ihb (j + 1) he.2⟩
  | lit l => intro j _; rfl
  | proj s i e ihe =>
    intro j he
    simp only [Expr.hasFvar] at he
    simp only [instShift, Expr.instantiate1Lift, Expr.hasFvar]
    exact ihe j he

/-- **Instantiating a `Let`'s image at a closed value**: the value and the body are
instantiated, the body one binder deeper. -/
theorem instShift_instantiate1 {A : KExpr} (hA : A.looseBVarsBounded 0 = true) (V B : KExpr)
    (j : Nat) : (instShift V 0 B).instantiate1 A j =
      instShift (V.instantiate1 A j) 0 (B.instantiate1 A (j + 1)) := by
  have := Expr.instantiate1Lift_instantiate1 (a := V) hA B 0 j
  rw [show (0 : Nat) + j = j from Nat.zero_add j, show (0 : Nat) + 1 + j = j + 1 by omega] at this
  exact this

theorem instShift_instantiateList : ∀ (As : List KExpr), (∀ A ∈ As, A.looseBVarsBounded 0 = true) →
    ∀ (V B : KExpr) (j : Nat), (instShift V 0 B).instantiateList As j =
      instShift (V.instantiateList As j) 0 (B.instantiateList As (j + 1))
  | [], _, V, B, j => by simp only [Expr.instantiateList_nil]
  | A :: As, hAs, V, B, j => by
    simp only [Expr.instantiateList_cons]
    rw [instShift_instantiateList As (fun x hx => hAs x (List.mem_cons_of_mem _ hx)) V B (j + 1),
      instShift_instantiate1 (hAs A (by simp))]

theorem ilp_lift (ks : List LevelParam) (us : List Level) (s : Nat) :
    ∀ (e : KExpr) (c : Nat), (e.liftLooseBVars s c).instantiateLevelParams ks us =
      (e.instantiateLevelParams ks us).liftLooseBVars s c := by
  intro e
  induction e with
  | bvar i =>
    intro c
    by_cases hc : c ≤ i
    · simp [Expr.liftLooseBVars, Expr.instantiateLevelParams, hc]
    · simp [Expr.liftLooseBVars, Expr.instantiateLevelParams, hc]
  | fvar i ty _ => intro c; simp [Expr.liftLooseBVars, Expr.instantiateLevelParams]
  | sort u => intro c; simp [Expr.liftLooseBVars, Expr.instantiateLevelParams]
  | const n us' => intro c; simp [Expr.liftLooseBVars, Expr.instantiateLevelParams]
  | app f a ihf iha => intro c; simp [Expr.liftLooseBVars, Expr.instantiateLevelParams, ihf, iha]
  | lam ty body m iht ihb =>
    intro c; simp [Expr.liftLooseBVars, Expr.instantiateLevelParams, iht, ihb]
  | forallE ty body m iht ihb =>
    intro c; simp [Expr.liftLooseBVars, Expr.instantiateLevelParams, iht, ihb]
  | letE ty val body m iht ihv ihb =>
    intro c; simp [Expr.liftLooseBVars, Expr.instantiateLevelParams, iht, ihv, ihb]
  | lit l => intro c; simp [Expr.liftLooseBVars, Expr.instantiateLevelParams]
  | proj s' i e ihe => intro c; simp [Expr.liftLooseBVars, Expr.instantiateLevelParams, ihe]

theorem ilp_instShift (ks : List LevelParam) (us : List Level) (v : KExpr) :
    ∀ (e : KExpr) (j : Nat), (instShift v j e).instantiateLevelParams ks us =
      instShift (v.instantiateLevelParams ks us) j (e.instantiateLevelParams ks us) := by
  intro e
  induction e with
  | bvar i =>
    intro j
    by_cases hij : i = j
    · subst hij; simp [instShift, Expr.instantiate1Lift, Expr.instantiateLevelParams, ilp_lift]
    · by_cases hlt : j < i
      · simp [instShift, Expr.instantiate1Lift, Expr.instantiateLevelParams, hij, hlt]
      · simp [instShift, Expr.instantiate1Lift, Expr.instantiateLevelParams, hij, hlt]
  | fvar i ty _ => intro j; simp [instShift, Expr.instantiate1Lift, Expr.instantiateLevelParams]
  | sort u => intro j; simp [instShift, Expr.instantiate1Lift, Expr.instantiateLevelParams]
  | const n us' => intro j; simp [instShift, Expr.instantiate1Lift, Expr.instantiateLevelParams]
  | app f a ihf iha => intro j; simp [instShift, Expr.instantiate1Lift, Expr.instantiateLevelParams, ihf, iha]
  | lam ty body m iht ihb => intro j; simp [instShift, Expr.instantiate1Lift, Expr.instantiateLevelParams, iht, ihb]
  | forallE ty body m iht ihb => intro j; simp [instShift, Expr.instantiate1Lift, Expr.instantiateLevelParams, iht, ihb]
  | letE ty val body m iht ihv ihb =>
    intro j; simp [instShift, Expr.instantiate1Lift, Expr.instantiateLevelParams, iht, ihv, ihb]
  | lit l => intro j; simp [instShift, Expr.instantiate1Lift, Expr.instantiateLevelParams]
  | proj s i e ihe => intro j; simp [instShift, Expr.instantiate1Lift, Expr.instantiateLevelParams, ihe]

theorem mkAppN_snoc : ∀ (As : List KExpr) (H A : KExpr),
    Expr.mkAppN H (As ++ [A]) = .app (Expr.mkAppN H As) A
  | [], _, _ => rfl
  | B :: As, H, A => mkAppN_snoc As (.app H B) A

end Kernel

/-! ## Represented terms: index facts -/

/-- `Specs.Subst.LbrLe` at the keying `κ` (`LbrLe c` is `LbrLeK c.κ`). -/
def LbrLeK (κ : _root_.Address → KKey) (h : Heap F) (p : SourceValue F) (k : Nat) (E : KExpr)
    (b : Nat) : Prop :=
  b ≤ k → E.looseBVarsBounded b = true ∧ E.hasFvar = false ∧
    ∀ d' Γ' k', b ≤ k' → Tm κ d' Γ' h k' E p

section TmFacts
variable {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}

/-- **Every index of a represented term is below the seam's bound and below `k + n + d` under
`n` binders.** -/
theorem tm_idxAll {k : Nat} {E : KExpr} {p : SourceValue F} (rep : Tm κ d Γ h k E p) :
    IdxAll h (fun n i => ZMod.val i < 9223372036854775808 ∧ ZMod.val i < k + n + d) 0 p := by
  induction rep with
  | bvarLocal cell hs hi => exact .bvar cell ⟨hs, by omega⟩
  | bvarFree cell hs hk hd => exact .bvar cell ⟨hs, by omega⟩
  | sort cell _ _ => exact .sort cell
  | const cell _ _ _ => exact .const cell
  | app cell _ _ ihf iha => exact .app cell ihf iha
  | lam cell _ _ _ iht ihb =>
    exact .lam cell iht (idxAll_imp ihb (fun n i hi => ⟨hi.1, by have := hi.2; omega⟩))
  | forallE cell _ _ _ iht ihb =>
    exact .forallE cell iht (idxAll_imp ihb (fun n i hi => ⟨hi.1, by have := hi.2; omega⟩))
  | letE cell _ _ _ iht ihv ihb =>
    exact .letE cell iht ihv (idxAll_imp ihb (fun n i hi => ⟨hi.1, by have := hi.2; omega⟩))
  | litNat cell _ _ => exact .lit cell
  | litStr cell _ _ => exact .lit cell
  | proj cell _ _ ihe => exact .proj cell ihe

/-- **The image's loose bound variables are below `lo`** when no heap index is in `[lo, k)`
(under `n` binders, `[lo + n, k + n)`): the local indices of the image are the heap's below
`k`. -/
theorem tm_lbb {k : Nat} {E : KExpr} {p : SourceValue F} (rep : Tm κ d Γ h k E p) :
    ∀ {lo : Nat}, lo ≤ k →
      IdxAll h (fun n i => ZMod.val i < lo + n ∨ k + n ≤ ZMod.val i) 0 p →
      E.looseBVarsBounded lo = true := by
  induction rep with
  | bvarLocal cell hs hi =>
    intro lo hlo hn
    obtain ⟨i', hx, hP⟩ := idxAll_bvar_inv hn (loadValue_enum_cell cell)
    injection hx with hx; subst hx
    simp only [Ix.Kernel.Expr.looseBVarsBounded, decide_eq_true_eq]
    simp only [Nat.add_zero] at hP; omega
  | bvarFree => intro lo _ _; rfl
  | sort => intro lo _ _; rfl
  | const => intro lo _ _; rfl
  | app cell _ _ ihf iha =>
    intro lo hlo hn
    obtain ⟨hf, ha⟩ := idxAll_app_inv hn (loadValue_enum_cell cell)
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨ihf hlo hf, iha hlo ha⟩
  | lam cell _ _ _ iht ihb =>
    intro lo hlo hn
    obtain ⟨ht, hb⟩ := idxAll_lam_inv hn (loadValue_enum_cell cell)
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iht hlo ht, ihb (by omega) (idxAll_imp hb (fun n i hi => by omega))⟩
  | forallE cell _ _ _ iht ihb =>
    intro lo hlo hn
    obtain ⟨ht, hb⟩ := idxAll_forallE_inv hn (loadValue_enum_cell cell)
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iht hlo ht, ihb (by omega) (idxAll_imp hb (fun n i hi => by omega))⟩
  | letE cell _ _ _ iht ihv ihb =>
    intro lo hlo hn
    obtain ⟨ht, hv, hb⟩ := idxAll_letE_inv hn (loadValue_enum_cell cell)
    exact lbb_instShift0 (ihv hlo hv) (ihb (by omega) (idxAll_imp hb (fun n i hi => by omega)))
  | litNat => intro lo _ _; rfl
  | litStr => intro lo _ _; rfl
  | proj cell _ _ ihe =>
    intro lo hlo hn
    simp only [Ix.Kernel.Expr.looseBVarsBounded]
    exact ihe hlo (idxAll_proj_inv hn (loadValue_enum_cell cell))

/-- **A heap bound gives `LbrLe`** (`LbrLeK`, at the keying `κ`; `Specs.Subst.LbrLe c` is
`LbrLeK c.κ`): at most `k`, the image has its loose bound variables below the bound and no
opened variable, and is read the same at every depth and context and every local depth at or
above the bound. -/
theorem lbrLe_of_idxLt {k : Nat} {E : KExpr} {p : SourceValue F}
    (rep : Tm κ d Γ h k E p) : ∀ {b : Nat}, IdxLt h b p → LbrLeK κ h p k E b := by
  induction rep with
  | bvarLocal cell hs hi =>
    intro b hb hbk
    obtain ⟨i', hx, hP⟩ := idxAll_bvar_inv hb (loadValue_enum_cell cell)
    injection hx with hx; subst hx
    simp only [Nat.add_zero] at hP
    refine ⟨?_, rfl, fun d' Γ' k' hk' => .bvarLocal cell hs (by omega)⟩
    simp only [Ix.Kernel.Expr.looseBVarsBounded, decide_eq_true_eq]; exact hP
  | bvarFree cell hs hk hd =>
    intro b hb hbk
    obtain ⟨i', hx, hP⟩ := idxAll_bvar_inv hb (loadValue_enum_cell cell)
    injection hx with hx; subst hx
    simp only [Nat.add_zero] at hP; omega
  | sort cell rl hu => intro b _ _; exact ⟨rfl, rfl, fun d' Γ' k' _ => .sort cell rl hu⟩
  | const cell ra rls hus => intro b _ _; exact ⟨rfl, rfl, fun d' Γ' k' _ => .const cell ra rls hus⟩
  | app cell _ _ ihf iha =>
    intro b hb hbk
    obtain ⟨hf, ha⟩ := idxAll_app_inv hb (loadValue_enum_cell cell)
    obtain ⟨f1, f2, f3⟩ := ihf hf hbk
    obtain ⟨a1, a2, a3⟩ := iha ha hbk
    refine ⟨?_, ?_, fun d' Γ' k' hk' => .app cell (f3 d' Γ' k' hk') (a3 d' Γ' k' hk')⟩
    · simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true]; exact ⟨f1, a1⟩
    · simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff]; exact ⟨f2, a2⟩
  | lam cell _ _ rl iht ihb =>
    intro b hb hbk
    obtain ⟨ht, hbd⟩ := idxAll_lam_inv hb (loadValue_enum_cell cell)
    obtain ⟨t1, t2, t3⟩ := iht ht hbk
    obtain ⟨b1, b2, b3⟩ := ihb (b := b + 1) (idxAll_imp hbd (fun n i hi => by omega)) (by omega)
    refine ⟨?_, ?_, fun d' Γ' k' hk' => .lam cell (t3 d' Γ' k' hk') (b3 d' Γ' (k' + 1) (by omega)) rl⟩
    · simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true]; exact ⟨t1, b1⟩
    · simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff]; exact ⟨t2, b2⟩
  | forallE cell _ _ rl iht ihb =>
    intro b hb hbk
    obtain ⟨ht, hbd⟩ := idxAll_forallE_inv hb (loadValue_enum_cell cell)
    obtain ⟨t1, t2, t3⟩ := iht ht hbk
    obtain ⟨b1, b2, b3⟩ := ihb (b := b + 1) (idxAll_imp hbd (fun n i hi => by omega)) (by omega)
    refine ⟨?_, ?_,
      fun d' Γ' k' hk' => .forallE cell (t3 d' Γ' k' hk') (b3 d' Γ' (k' + 1) (by omega)) rl⟩
    · simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true]; exact ⟨t1, b1⟩
    · simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff]; exact ⟨t2, b2⟩
  | letE cell _ _ _ iht ihv ihb =>
    intro b hb hbk
    obtain ⟨ht, hv, hbd⟩ := idxAll_letE_inv hb (loadValue_enum_cell cell)
    obtain ⟨t1, t2, t3⟩ := iht ht hbk
    obtain ⟨v1, v2, v3⟩ := ihv hv hbk
    obtain ⟨b1, b2, b3⟩ := ihb (b := b + 1) (idxAll_imp hbd (fun n i hi => by omega)) (by omega)
    exact ⟨lbb_instShift0 v1 b1, hasFvar_instShift v2 _ 0 b2,
      fun d' Γ' k' hk' => .letE cell (t3 d' Γ' k' hk') (v3 d' Γ' k' hk') (b3 d' Γ' (k' + 1) (by omega))⟩
  | litNat cell rl hc => intro b _ _; exact ⟨rfl, rfl, fun d' Γ' k' _ => .litNat cell rl hc⟩
  | litStr cell rb hs => intro b _ _; exact ⟨rfl, rfl, fun d' Γ' k' _ => .litStr cell rb hs⟩
  | proj cell ra _ ihe =>
    intro b hb hbk
    obtain ⟨e1, e2, e3⟩ := ihe (idxAll_proj_inv hb (loadValue_enum_cell cell)) hbk
    exact ⟨e1, e2, fun d' Γ' k' hk' => .proj cell ra (e3 d' Γ' k' hk')⟩

/-- **A represented term's heap indices are below `k + d`.** -/
theorem tm_idxLt {k : Nat} {E : KExpr} {p : SourceValue F} (rep : Tm κ d Γ h k E p) :
    IdxLt h (k + d) p :=
  idxAll_mono (tm_idxAll rep) (fun n i hi => by omega)

/-- **`NoIdxF` is `NoIdx` for a represented term** when the window ends at most `2^63` below
the field's size: an index is below `2^63`, so where the window's end has passed the field's
size the index is below the window's start. -/
theorem noIdx_of_noIdxF_tm {k : Nat} {E : KExpr} {p : SourceValue F} (rep : Tm κ d Γ h k E p)
    {lo hi : Nat} (hhi : hi + 9223372036854775808 ≤ Aiur.Library.U32.Goldilocks.modulus)
    (hf : NoIdxF h lo hi p) : NoIdx h lo hi p := by
  have both := idxAll_and (tm_idxAll rep) hf
  refine idxAll_mono both (fun n i hi' => ?_)
  obtain ⟨⟨hs, -⟩, hw⟩ := hi'
  by_cases hlt : hi + n < Aiur.Library.U32.Goldilocks.modulus
  · exact hw hlt
  · left; omega

end TmFacts

/-! ## Stores and copies -/

section Store
variable {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}

theorem store_get {h : Heap F} {v : SourceValue F} : (h ++ [v])[h.length]? = some v := by simp

theorem tm_store_bvarLocal {h : Heap F} {k : Nat} {i : F}
    (hs : ZMod.val i < 9223372036854775808) (hi : ZMod.val i < k) :
    Tm κ d Γ (h ++ [.construct kexprEnum "BVar" [.field i]]) k (.bvar (ZMod.val i))
      (.ptr (.enum kexprEnum) h.length) :=
  .bvarLocal store_get hs hi

theorem tm_store_bvarFree {h : Heap F} {k : Nat} {i : F}
    (hs : ZMod.val i < 9223372036854775808) (hk : k ≤ ZMod.val i) (hd : ZMod.val i - k < d) :
    Tm κ d Γ (h ++ [.construct kexprEnum "BVar" [.field i]]) k
      (.fvar (fvIdx d k (ZMod.val i)) (Γ (fvIdx d k (ZMod.val i))))
      (.ptr (.enum kexprEnum) h.length) :=
  .bvarFree store_get hs hk hd

theorem tm_store_lam {h : Heap F} {k : Nat} {T B : KExpr} {ℓ : KLevel} {tp bp lp : SourceValue F}
    (rt : Tm κ d Γ h k T tp) (rb : Tm κ d Γ h (k + 1) B bp) (rl : RepKLevel h ℓ lp) :
    Tm κ d Γ (h ++ [.construct kexprEnum "Lam" [tp, bp, lp]]) k (.lam T B (bmeta ℓ))
      (.ptr (.enum kexprEnum) h.length) := by
  have ext := Heap.Extends.snoc h (.construct kexprEnum "Lam" [tp, bp, lp])
  exact .lam store_get (rt.mono ext) (rb.mono ext) (rl.mono ext)

theorem tm_store_forallE {h : Heap F} {k : Nat} {T B : KExpr} {ℓ : KLevel}
    {tp bp lp : SourceValue F}
    (rt : Tm κ d Γ h k T tp) (rb : Tm κ d Γ h (k + 1) B bp) (rl : RepKLevel h ℓ lp) :
    Tm κ d Γ (h ++ [.construct kexprEnum "Forall" [tp, bp, lp]]) k (.forallE T B (bmeta ℓ))
      (.ptr (.enum kexprEnum) h.length) := by
  have ext := Heap.Extends.snoc h (.construct kexprEnum "Forall" [tp, bp, lp])
  exact .forallE store_get (rt.mono ext) (rb.mono ext) (rl.mono ext)

theorem tm_store_letE {h : Heap F} {k : Nat} {T V B : KExpr} {tp vp bp : SourceValue F}
    (rt : Tm κ d Γ h k T tp) (rv : Tm κ d Γ h k V vp) (rb : Tm κ d Γ h (k + 1) B bp) :
    Tm κ d Γ (h ++ [.construct kexprEnum "Let" [tp, vp, bp]]) k (instShift V 0 B)
      (.ptr (.enum kexprEnum) h.length) := by
  have ext := Heap.Extends.snoc h (.construct kexprEnum "Let" [tp, vp, bp])
  exact .letE store_get (rt.mono ext) (rv.mono ext) (rb.mono ext)

theorem tm_store_proj {h : Heap F} {k : Nat} {a : Bytes.Address} {i : F} {E : KExpr}
    {ap ep : SourceValue F} (ra : Bytes.RepAddressRef addrTy h a ap) (re : Tm κ d Γ h k E ep) :
    Tm κ d Γ (h ++ [.construct kexprEnum "Proj" [ap, .field i, ep]]) k
      (.proj (κ (ixAddr a)) (ZMod.val i) E) (.ptr (.enum kexprEnum) h.length) := by
  have ext := Heap.Extends.snoc h (.construct kexprEnum "Proj" [ap, .field i, ep])
  exact .proj store_get (Bytes.repAddressRef_heapMono₂ addrTy ext ra) (re.mono ext)

theorem tm_store_sort {h : Heap F} {k : Nat} {u l : KLevel} {lp : SourceValue F}
    (rl : RepKLevel h l lp) (hu : LvEq u l) :
    Tm κ d Γ (h ++ [.construct kexprEnum "Srt" [lp]]) k (.sort u) (.ptr (.enum kexprEnum) h.length) :=
  .sort store_get (rl.mono (Heap.Extends.snoc _ _)) hu

theorem tm_store_const {h : Heap F} {k : Nat} {a : Bytes.Address} {ls us : List KLevel}
    {ap lsp : SourceValue F} (ra : Bytes.RepAddressRef addrTy h a ap)
    (rls : RepKLevelList h ls lsp) (hus : LvEqList us ls) :
    Tm κ d Γ (h ++ [.construct kexprEnum "Const" [ap, lsp]]) k (.const (κ (ixAddr a)) us)
      (.ptr (.enum kexprEnum) h.length) := by
  have ext := Heap.Extends.snoc h (.construct kexprEnum "Const" [ap, lsp])
  exact .const store_get (Bytes.repAddressRef_heapMono₂ addrTy ext ra) (rls.mono ext) hus

/-- A copied `Srt` node is represented at every reading. -/
theorem tm_copy_sort {d' : Nat} {Γ' : Nat → KExpr} {h m : Heap F} {k k' : Nat} {E : KExpr}
    {p x : SourceValue F} (rep : Tm κ d Γ h k E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Srt" [x])) (ext : Heap.Extends h m) :
    Tm κ d' Γ' (m ++ [.construct kexprEnum "Srt" [x]]) k' E (.ptr (.enum kexprEnum) m.length) := by
  obtain ⟨u, rfl, l, rl, hu⟩ := Tm.sort_of_load rep ld
  exact tm_store_sort (rl.mono ext) hu

/-- A copied `Const` node is represented at every reading. -/
theorem tm_copy_const {d' : Nat} {Γ' : Nat → KExpr} {h m : Heap F} {k k' : Nat} {E : KExpr}
    {p x y : SourceValue F} (rep : Tm κ d Γ h k E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Const" [x, y])) (ext : Heap.Extends h m) :
    Tm κ d' Γ' (m ++ [.construct kexprEnum "Const" [x, y]]) k' E
      (.ptr (.enum kexprEnum) m.length) := by
  obtain ⟨a, us, rfl, ra, ls, rls, hus⟩ := Tm.const_of_load rep ld
  exact tm_store_const (Bytes.repAddressRef_heapMono₂ addrTy ext ra) (rls.mono ext) hus

/-- A copied `Lit` node is represented at every reading. -/
theorem tm_copy_lit {d' : Nat} {Γ' : Nat → KExpr} {h m : Heap F} {k k' : Nat} {E : KExpr}
    {p x : SourceValue F} (rep : Tm κ d Γ h k E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Lit" [x])) (ext : Heap.Extends h m) :
    Tm κ d' Γ' (m ++ [.construct kexprEnum "Lit" [x]]) k' E (.ptr (.enum kexprEnum) m.length) := by
  have ext' := ext.trans (Heap.Extends.snoc m (.construct kexprEnum "Lit" [x]))
  rcases Tm.lit_of_load rep ld with ⟨lp, limbs, rfl, rl, hc, rfl⟩ | ⟨bp, bytes, s, rfl, rb, hs, rfl⟩
  · exact .litNat store_get (repList_heapMono₂ _ repU64_heapMono₂ ext' rl) hc
  · exact .litStr store_get (Bytes.repByteStream_heapMono₂ _ ext' rb) hs

end Store

end IxVM.Refinement.Core.SubstAux
