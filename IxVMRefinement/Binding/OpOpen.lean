import IxVMRefinement.Core.Open
import IxVMRefinement.Lib.Bytes
import IxVMRefinement.Obs.KernelSubst1
import IxVMRefinement.Obs.KernelRoles3
import IxC.Kernel.Verify.BridgeWfImp
import IxVMRefinement.Decl.ModeledRules

/-! # Opening an operation's equation sides and replacing the operation by its value

The specifications of the circuit functions `KernelRoles::validate_op_equations` applies to an
operation's rendered equation sides:

* `subst_const_spec`: **`KernelSubst::subst_const(e, a, v)`** on a represented term `X` and a
  closed value `val` represents `Expr.substConstAll (κ a) val X`, at the same local depth,
  opening depth and ghost context, when the keying is injective at `a`. An occurrence of the
  operation with universe levels takes the circuit's `assert_eq!(0, 1)` path: no run.
  A `let` cell's image is its ζ-reduct, so the replacement commutes with the capture-avoiding
  instantiation on a closed value (`substConstAll_instantiate1Lift`).
* `substConstAll_eq_substConst0`: on binder-free terms the replacement everywhere is the
  kernel's spine replacement `Expr.substConst0`; both sides of every recurrence of
  `natOpEquations 0 c` are binder-free (`natOpEquations_binderFree`).
* `open_two_lams_spec`: **`KernelRoles::open_two_lams(e)`** on a closed `λ x y, B` gives `B`
  opened at depth 2 (`open₂`) and the context list of the two binder types, innermost first.
* `op_equation_side_spec`: the two together, on a rendered side `λ (x y : Nat), L` with
  `open₂ L = l` for a side `l` of `natOpEquations 0 c`: the result represents
  `Expr.substConst0 c val l` at depth 2 under the ghost context of two `Nat` variables.
* `open_foralls_spec`: **`KernelRoles::open_foralls(e, acc)`** on a `∀`-telescope whose first
  `n` binders the kernel opens (`openPisAtFvars`) along `Forall` cells (`ForallSpine`, kept by
  `subst_const`: `subst_const_forallSpine`) gives the body at depth `d + n` and the context
  list extended by the binder types, innermost first.
* `apply_bvars_desc_spec`, `mkAppN_fvars_divModCertApplied`: **`apply_spine(p,
  bvars_desc(d, d))`** represents the term applied to the opened variables `0, …, d - 1`, which
  for a certificate is `divModCertApplied`.
-/

namespace IxVM.Refinement.Binding.OpOpen

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open Ix.Kernel (Expr)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

local macro "lt_calls" : term =>
  `(by simp only [List.length_cons, List.length_append, List.length_nil] <;> omega)

/-! ## Closed terms at any local depth -/

/-- A term represented at opening depth `0` and local depth `k` is represented at every larger
local depth: its bound variables are all bound inside it or below `k`. -/
theorem tm_raise_closed {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F} {k : Nat}
    {E : KExpr} {p : SourceValue F} (rep : Tm κ 0 Γ h k E p) :
    ∀ k', k ≤ k' → Tm κ 0 Γ h k' E p := by
  induction rep with
  | bvarLocal cell hs hi => intro k' hk; exact .bvarLocal cell hs (by omega)
  | bvarFree _ _ _ hd => exact absurd hd (by omega)
  | sort cell rl hu => intro _ _; exact .sort cell rl hu
  | const cell ra rls hus => intro _ _; exact .const cell ra rls hus
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

/-- **A closed term is represented at every opening depth, ghost context and local depth.** -/
theorem tmC_atLocal {κ : _root_.Address → KKey} {h : Heap F} {E : KExpr} {p : SourceValue F}
    (hv : TmC κ h E p) (d : Nat) (Γ : Nat → KExpr) (k : Nat) : Tm κ d Γ h k E p :=
  (tm_raise_closed (hv 0 Γ) k (Nat.zero_le k)).of_depth_zero d

/-! ## The replacement everywhere, on closed values -/

theorem substConstAll_const_self (n : KKey) (r : KExpr) :
    Expr.substConstAll n r (.const n []) = r := by
  simp [Expr.substConstAll]

theorem substConstAll_const_ne {n k : KKey} (r : KExpr) (us : List KLevel) (hk : k ≠ n) :
    Expr.substConstAll n r (.const k us) = .const k us := by
  simp [Expr.substConstAll, hk]

/-- Replacing a constant by a closed value commutes with lifting loose bound variables. -/
theorem substConstAll_liftLooseBVars {n : KKey} {r : KExpr} (hr : r.looseBVarsBounded 0 = true) :
    ∀ (e : KExpr) (m c : Nat),
      Expr.substConstAll n r (e.liftLooseBVars m c) =
        (Expr.substConstAll n r e).liftLooseBVars m c := by
  intro e
  induction e with
  | bvar i =>
    intro m c
    show Expr.substConstAll n r (Expr.liftLooseBVars m c (.bvar i)) =
      Expr.liftLooseBVars m c (.bvar i)
    simp only [Expr.liftLooseBVars]
    by_cases hc : i ≥ c
    · rw [ite_eq_left hc]; try rfl
    · rw [ite_eq_right hc]; try rfl
  | fvar _ _ _ => intro m c; rfl
  | sort _ => intro m c; rfl
  | lit _ => intro m c; rfl
  | const k us =>
    intro m c
    show Expr.substConstAll n r (.const k us) = (Expr.substConstAll n r (.const k us)).liftLooseBVars m c
    by_cases hc : k = n ∧ us = []
    · obtain ⟨rfl, rfl⟩ := hc
      rw [substConstAll_const_self]
      exact (Expr.liftLooseBVars_eq_self (Expr.looseBVarsBounded_mono (Nat.zero_le c) hr)).symm
    · have hk : ¬ (k = n ∧ us = []) := hc
      have e : Expr.substConstAll n r (.const k us) = .const k us := by
        simp only [Expr.substConstAll]
        exact ite_eq_right hk
      rw [e]; rfl
  | app f a ihf iha =>
    intro m c
    simp only [Expr.liftLooseBVars, Expr.substConstAll, ihf, iha]
  | lam ty body bm iht ihb =>
    intro m c
    simp only [Expr.liftLooseBVars, Expr.substConstAll, iht, ihb]
  | forallE ty body bm iht ihb =>
    intro m c
    simp only [Expr.liftLooseBVars, Expr.substConstAll, iht, ihb]
  | letE ty v body lm iht ihv ihb =>
    intro m c
    simp only [Expr.liftLooseBVars, Expr.substConstAll, iht, ihv, ihb]
  | proj s i e ih =>
    intro m c
    simp only [Expr.liftLooseBVars, Expr.substConstAll, ih]

/-- **Replacing a constant by a closed value commutes with the capture-avoiding
instantiation** (`Expr.instantiate1Lift`, the image of a `let`). -/
theorem substConstAll_instantiate1Lift {n : KKey} {r : KExpr}
    (hr : r.looseBVarsBounded 0 = true) :
    ∀ (e V : KExpr) (j : Nat),
      Expr.substConstAll n r (e.instantiate1Lift V j) =
        (Expr.substConstAll n r e).instantiate1Lift (Expr.substConstAll n r V) j := by
  intro e
  induction e with
  | bvar i =>
    intro V j
    show Expr.substConstAll n r (Expr.instantiate1Lift (.bvar i) V j) =
      Expr.instantiate1Lift (.bvar i) (Expr.substConstAll n r V) j
    simp only [Expr.instantiate1Lift]
    by_cases h1 : i = j
    · rw [ite_eq_left h1, ite_eq_left h1]
      exact substConstAll_liftLooseBVars hr V j 0
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : i > j
      · rw [ite_eq_left h2]; try rfl
      · rw [ite_eq_right h2]; try rfl
  | fvar _ _ _ => intro V j; rfl
  | sort _ => intro V j; rfl
  | lit _ => intro V j; rfl
  | const k us =>
    intro V j
    show Expr.substConstAll n r (.const k us) =
      (Expr.substConstAll n r (.const k us)).instantiate1Lift (Expr.substConstAll n r V) j
    by_cases hc : k = n ∧ us = []
    · obtain ⟨rfl, rfl⟩ := hc
      rw [substConstAll_const_self]
      exact (Expr.instantiate1Lift_eq_self (Expr.looseBVarsBounded_mono (Nat.zero_le j) hr)).symm
    · have e : Expr.substConstAll n r (.const k us) = .const k us := by
        simp only [Expr.substConstAll]
        exact ite_eq_right hc
      rw [e]; rfl
  | app f a ihf iha =>
    intro V j
    simp only [Expr.instantiate1Lift, Expr.substConstAll, ihf, iha]
  | lam ty body bm iht ihb =>
    intro V j
    simp only [Expr.instantiate1Lift, Expr.substConstAll, iht, ihb]
  | forallE ty body bm iht ihb =>
    intro V j
    simp only [Expr.instantiate1Lift, Expr.substConstAll, iht, ihb]
  | letE ty v body lm iht ihv ihb =>
    intro V j
    simp only [Expr.instantiate1Lift, Expr.substConstAll, iht, ihv, ihb]
  | proj s i e ih =>
    intro V j
    simp only [Expr.instantiate1Lift, Expr.substConstAll, ih]

/-- The image of a `let` cell, with the operation replaced by a closed value. -/
theorem substConstAll_instShift {n : KKey} {r : KExpr} (hr : r.looseBVarsBounded 0 = true)
    (V B : KExpr) :
    Expr.substConstAll n r (instShift V 0 B) =
      instShift (Expr.substConstAll n r V) 0 (Expr.substConstAll n r B) :=
  substConstAll_instantiate1Lift hr B V 0

/-! ## `KernelSubst::subst_const` -/

private theorem ext_snoc {h h' : Heap F} {x : SourceValue F} (hm : h' = h ++ [x]) :
    Heap.Extends h h' := by
  rw [hm]; exact Heap.Extends.snoc _ _

private theorem load_ptr_cell {h : Heap F} {addr : Nat} {c : String}
    {xs : List (SourceValue F)} {v1 : SourceValue F}
    (cell : h[addr]? = some (.construct kexprEnum c xs))
    (ld : loadValue h (.ptr (.enum kexprEnum) addr) = .ok v1) :
    v1 = .construct kexprEnum c xs := by
  rw [loadValue_enum_cell cell] at ld
  injection ld with e
  exact e.symm

/-- A represented term whose cell is none of the nodes `subst_const` rebuilds (a variable, a
sort, a literal) is unchanged by the replacement. -/
private theorem substConstAll_other {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {X : KExpr} {e v1 : SourceValue F} (n : KKey) (val : KExpr)
    (hX : Tm κ d Γ h k X e) (ld : loadValue h e = .ok v1)
    (n1 : ∀ vs : List (SourceValue F), vs.length = 2 →
      v1 ≠ .construct "KernelTypes::KExprNode" "Const" vs)
    (n2 : ∀ vs : List (SourceValue F), vs.length = 2 →
      v1 ≠ .construct "KernelTypes::KExprNode" "App" vs)
    (n3 : ∀ vs : List (SourceValue F), vs.length = 3 →
      v1 ≠ .construct "KernelTypes::KExprNode" "Lam" vs)
    (n4 : ∀ vs : List (SourceValue F), vs.length = 3 →
      v1 ≠ .construct "KernelTypes::KExprNode" "Forall" vs)
    (n5 : ∀ vs : List (SourceValue F), vs.length = 3 →
      v1 ≠ .construct "KernelTypes::KExprNode" "Let" vs)
    (n6 : ∀ vs : List (SourceValue F), vs.length = 3 →
      v1 ≠ .construct "KernelTypes::KExprNode" "Proj" vs) :
    Expr.substConstAll n val X = X := by
  cases hX with
  | bvarLocal => rfl
  | bvarFree => rfl
  | sort => rfl
  | litNat => rfl
  | litStr => rfl
  | const cell => exact absurd (load_ptr_cell cell ld) (n1 _ rfl)
  | app cell => exact absurd (load_ptr_cell cell ld) (n2 _ rfl)
  | lam cell => exact absurd (load_ptr_cell cell ld) (n3 _ rfl)
  | forallE cell => exact absurd (load_ptr_cell cell ld) (n4 _ rfl)
  | letE cell => exact absurd (load_ptr_cell cell ld) (n5 _ rfl)
  | proj cell => exact absurd (load_ptr_cell cell ld) (n6 _ rfl)

private theorem subst_const_aux (κ : _root_.Address → KKey) (d : Nat) (Γ : Nat → KExpr)
    (a v : SourceValue F) (b : Bytes.Address) (val : KExpr)
    (hinj : ∀ b', κ (ixAddr b') = κ (ixAddr b) → b' = b) :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)), ObsFn W fname args h r h' cs →
      fname = "KernelSubst::subst_const" → ∀ (e : SourceValue F) (k : Nat) (X : KExpr),
        args = [e, a, v] → Tm κ d Γ h k X e → Bytes.RepAddressRef addrTy h b a →
        TmC κ h val v → Tm κ d Γ h' k (Expr.substConstAll (κ (ixAddr b)) val X) r :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => fname = "KernelSubst::subst_const" →
      ∀ (e : SourceValue F) (k : Nat) (X : KExpr),
        args = [e, a, v] → Tm κ d Γ h k X e → Bytes.RepAddressRef addrTy h b a →
        TmC κ h val v → Tm κ d Γ h' k (Expr.substConstAll (κ (ixAddr b)) val X) r)
    (fun fname args h r h' cs ev ih hfn e k X hargs hX ha hv => by
      subst hfn hargs
      match Obs.«KernelSubst::subst_const».obs ev with
      | .Const_n1_Nil (ld12 := ld) (ev44 := aeq) (ld76 := ldn) (he85 := hr) (he86 := hh) .. =>
        subst hr hh
        obtain ⟨a', us, hXe, ra, ls, rls, hus⟩ := hX.const_of_load ld
        subst hXe
        obtain ⟨h1, hm⟩ := Lib.address_eq_spec aeq ra ha
        subst hm
        by_cases hab : a' = b
        · have e : Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» =
              KernelLevels.klevelListEnum := klevelListEnum_eq
          rw [e] at ldn
          have hls : ls = [] := Core.RepList.nil_of_load rls ldn
          subst hls
          have hus' : us = [] :=
            List.eq_nil_of_length_eq_zero (Ix.Kernel.Level.EvalEqList.length_eq (hus fun _ => 0))
          subst hus' hab
          rw [substConstAll_const_self]
          exact tmC_atLocal hv d Γ k
        · rw [ite_eq_right hab] at h1
          exact absurd (Value.field.inj h1) one_ne_zero
      | .Const_n1_Cons (heq132 := h01) .. =>
        exact absurd (Value.field.inj h01) zero_ne_one
      | .Const_other (ld12 := ld) (ev44 := aeq) (hne138 := hne) (he143 := hr) (he144 := hh) .. =>
        subst hr hh
        obtain ⟨a', us, hXe, ra, -⟩ := hX.const_of_load ld
        subst hXe
        obtain ⟨h1, hm⟩ := Lib.address_eq_spec aeq ra ha
        subst hm h1
        have hab : a' ≠ b := fun hab => hne (by rw [ite_eq_left hab])
        rw [substConstAll_const_ne val us (fun hk => hab (hinj a' hk))]
        exact hX
      | .App (ld12 := ld) (he167 := hr) (hm166 := hm) (ev184 := e1) (ev220 := e2)
          (hc245 := hc) .. =>
        subst hc hr hm
        obtain ⟨Ef, Ea, hXe, hf, hx⟩ := hX.app_of_load ld
        subst hXe
        have ext1 := e1.heap_extends
        have x1 := ih _ _ _ _ _ _ lt_calls e1 rfl _ k Ef rfl hf ha hv
        have x2 := ih _ _ _ _ _ _ lt_calls e2 rfl _ k Ea rfl (hx.mono ext1)
          (Bytes.repAddressRef_heapMono₂ addrTy ext1 ha) (hv.mono ext1)
        exact Tm.store_app (x1.mono e2.heap_extends) x2
      | .Lam (ld12 := ld) (he272 := hr) (hm271 := hm) (ev290 := e1) (ev326 := e2)
          (hc358 := hc) .. =>
        have ext3 := ext_snoc hm
        subst hc hr hm
        obtain ⟨T, B, ℓ, hXe, ht, hb, hl⟩ := hX.lam_of_load ld
        subst hXe
        have ext1 := e1.heap_extends
        have ext2 := e2.heap_extends
        have x1 := ih _ _ _ _ _ _ lt_calls e1 rfl _ k T rfl ht ha hv
        have x2 := ih _ _ _ _ _ _ lt_calls e2 rfl _ (k + 1) B rfl (hb.mono ext1)
          (Bytes.repAddressRef_heapMono₂ addrTy ext1 ha) (hv.mono ext1)
        show Tm κ d Γ _ k (.lam (Expr.substConstAll (κ (ixAddr b)) val T)
          (Expr.substConstAll (κ (ixAddr b)) val B) (bmeta ℓ)) _
        exact .lam (by simp) ((x1.mono ext2).mono ext3) (x2.mono ext3)
          (hl.mono ((ext1.trans ext2).trans ext3))
      | .Forall (ld12 := ld) (he385 := hr) (hm384 := hm) (ev403 := e1) (ev439 := e2)
          (hc471 := hc) .. =>
        have ext3 := ext_snoc hm
        subst hc hr hm
        obtain ⟨T, B, ℓ, hXe, ht, hb, hl⟩ := hX.forallE_of_load ld
        subst hXe
        have ext1 := e1.heap_extends
        have ext2 := e2.heap_extends
        have x1 := ih _ _ _ _ _ _ lt_calls e1 rfl _ k T rfl ht ha hv
        have x2 := ih _ _ _ _ _ _ lt_calls e2 rfl _ (k + 1) B rfl (hb.mono ext1)
          (Bytes.repAddressRef_heapMono₂ addrTy ext1 ha) (hv.mono ext1)
        show Tm κ d Γ _ k (.forallE (Expr.substConstAll (κ (ixAddr b)) val T)
          (Expr.substConstAll (κ (ixAddr b)) val B) (bmeta ℓ)) _
        exact .forallE (by simp) ((x1.mono ext2).mono ext3) (x2.mono ext3)
          (hl.mono ((ext1.trans ext2).trans ext3))
      | .Let (ld12 := ld) (he498 := hr) (hm497 := hm) (ev516 := e1) (ev552 := e2) (ev588 := e3)
          (hc613 := hc) .. =>
        have ext4 := ext_snoc hm
        subst hc hr hm
        obtain ⟨T, V, B, hXe, ht, hvv, hb⟩ := hX.letE_of_load ld
        subst hXe
        have hvc : val.looseBVarsBounded 0 = true := Tm.looseBVarsBounded (hv 0 Γ)
        have ext1 := e1.heap_extends
        have ext2 := e2.heap_extends
        have ext3 := e3.heap_extends
        have x1 := ih _ _ _ _ _ _ lt_calls e1 rfl _ k T rfl ht ha hv
        have x2 := ih _ _ _ _ _ _ lt_calls e2 rfl _ k V rfl (hvv.mono ext1)
          (Bytes.repAddressRef_heapMono₂ addrTy ext1 ha) (hv.mono ext1)
        have x3 := ih _ _ _ _ _ _ lt_calls e3 rfl _ (k + 1) B rfl (hb.mono (ext1.trans ext2))
          (Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans ext2) ha) (hv.mono (ext1.trans ext2))
        rw [substConstAll_instShift hvc]
        exact .letE (by simp) (((x1.mono ext2).mono ext3).mono ext4) ((x2.mono ext3).mono ext4)
          (x3.mono ext4)
      | .Proj (ld12 := ld) (he640 := hr) (hm639 := hm) (ev672 := e1) (hc697 := hc) .. =>
        have ext2 := ext_snoc hm
        subst hc hr hm
        obtain ⟨s, i, Es, hxi, hXe, ra, hes⟩ := hX.proj_of_load ld
        subst hXe hxi
        have : Resolved (κ (ixAddr s)) := ⟨hX.proj_key_ne⟩
        have : ProjPermitted κ (ixAddr s) := hX.proj_permitted ld ra
        have ext1 := e1.heap_extends
        have x1 := ih _ _ _ _ _ _ lt_calls e1 rfl _ k Es rfl hes ha hv
        show Tm κ d Γ _ k (.proj (κ (ixAddr s)) (ZMod.val i)
          (Expr.substConstAll (κ (ixAddr b)) val Es)) _
        exact .proj (by simp) (Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans ext2) ra)
          (x1.mono ext2)
      | .other (ld12 := ld) (hne146 := n1) (hne246 := n2) (hne359 := n3) (hne472 := n4)
          (hne614 := n5) (hne698 := n6) (he703 := hr) (he704 := hh) .. =>
        subst hr hh
        rw [substConstAll_other (κ (ixAddr b)) val hX ld n1 n2 n3 n4 n5 n6]
        exact hX)

/-- **`KernelSubst::subst_const(e, a, v)`**: on a term `X` represented at any local depth,
opening depth and ghost context, the address `b` that `a` holds, and a closed value `val`
that `v` represents, a successful run represents `X` with every occurrence of the constant
`κ (ixAddr b)` at no universe levels replaced by `val` (`Expr.substConstAll`), at the same
depths, when no other address has the key of `b`. -/
theorem subst_const_spec {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h h' : Heap F} {k : Nat} {X val : KExpr} {e a v r : SourceValue F} {b : Bytes.Address}
    {cs : List (Call F)}
    (hinj : ∀ b', κ (ixAddr b') = κ (ixAddr b) → b' = b)
    (ha : Bytes.RepAddressRef addrTy h b a) (hv : TmC κ h val v)
    (hX : Tm κ d Γ h k X e)
    (ev : ObsFn W "KernelSubst::subst_const" [e, a, v] h r h' cs) :
    Tm κ d Γ h' k (Expr.substConstAll (κ (ixAddr b)) val X) r ∧ Heap.Extends h h' :=
  ⟨subst_const_aux κ d Γ a v b val hinj _ _ _ _ _ _ ev rfl e k X rfl hX ha hv,
    ev.heap_extends⟩

/-! ## Binder-free terms: the two replacements agree -/

/-- **A binder-free term**: built from constants, applications, variables, sorts and literals. -/
def binderFree : KExpr → Bool
  | .const _ _ | .fvar _ _ | .bvar _ | .sort _ | .lit _ => true
  | .app f a => binderFree f && binderFree a
  | _ => false

/-- **On a binder-free term the replacement everywhere is the spine replacement.** -/
theorem substConstAll_eq_substConst0 (n : KKey) (r : KExpr) :
    ∀ e : KExpr, binderFree e = true → Expr.substConstAll n r e = Expr.substConst0 n r e := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro he
    simp only [binderFree, Bool.and_eq_true] at he
    simp only [Expr.substConstAll, Expr.substConst0, ihf he.1, iha he.2]
  | const k us => intro _; simp only [Expr.substConstAll, Expr.substConst0]
  | bvar _ => intro _; rfl
  | fvar _ _ _ => intro _; rfl
  | sort _ => intro _; rfl
  | lit _ => intro _; rfl
  | lam _ _ _ _ _ => intro he; simp [binderFree] at he
  | forallE _ _ _ _ _ => intro he; simp [binderFree] at he
  | letE _ _ _ _ _ _ _ => intro he; simp [binderFree] at he
  | proj _ _ _ _ => intro he; simp [binderFree] at he

/-- **Both sides of every recurrence of a structural operation are binder-free.** -/
theorem natOpEquations_binderFree (c : KKey) :
    (Ix.Kernel.natOpEquations 0 c).all (fun eq => binderFree eq.1 && binderFree eq.2) = true := by
  simp only [Ix.Kernel.natOpEquations]
  repeat' split
  all_goals rfl

theorem natOpEquations_sides_binderFree {c : KKey} {eq : KExpr × KExpr}
    (heq : eq ∈ Ix.Kernel.natOpEquations 0 c) :
    binderFree eq.1 = true ∧ binderFree eq.2 = true := by
  have h := List.all_eq_true.mp (natOpEquations_binderFree c) eq heq
  simpa only [Bool.and_eq_true] using h

/-- **On the sides of a recurrence the two replacements agree.** -/
theorem substConstAll_eq_substConst0_of_natOpEquations {c n : KKey} {r : KExpr}
    {eq : KExpr × KExpr} (heq : eq ∈ Ix.Kernel.natOpEquations 0 c) :
    Expr.substConstAll n r eq.1 = Expr.substConst0 n r eq.1 ∧
      Expr.substConstAll n r eq.2 = Expr.substConst0 n r eq.2 :=
  ⟨substConstAll_eq_substConst0 n r eq.1 (natOpEquations_sides_binderFree heq).1,
    substConstAll_eq_substConst0 n r eq.2 (natOpEquations_sides_binderFree heq).2⟩

/-! ## `KernelRoles::open_two_lams` -/

/-- **The body of `λ x y, B` opened at depth 2**: the outer variable `x` (`.bvar 1` in `B`)
becomes `.fvar 0 T₁`, the inner `y` (`.bvar 0`) becomes `.fvar 1 T₂'` with `T₂'` the inner
domain opened at `x` (`T₂` itself when it is closed). The kernel's opening, binder by binder
(`Expr.instantiate1`, as `Tm.open`). -/
def open₂ (T₁ T₂ B : KExpr) : KExpr :=
  (B.instantiate1 (.fvar 0 T₁) 1).instantiate1 (.fvar 1 (T₂.instantiate1 (.fvar 0 T₁))) 0

/-- **`KernelRoles::open_two_lams(e)`** on a closed `λ (x : T₁) (y : T₂), B`: the result is the
pair of the body, represented at opening depth 2 as `open₂ T₁ T₂ B`, and the context list of
the two binder types, innermost first, under a ghost context giving `x` the type `T₁` and `y`
the type `T₂` opened at `x`. -/
theorem open_two_lams_spec {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h h' : Heap F}
    {e r : SourceValue F} {cs : List (Call F)} {T₁ T₂ B : KExpr}
    {m₁ m₂ : Ix.Kernel.BinderMeta}
    (hE : TmC κ h (.lam T₁ (.lam T₂ B m₂) m₁) e)
    (hΓ0 : Γ 0 = T₁) (hΓ1 : Γ 1 = T₂.instantiate1 (.fvar 0 T₁))
    (ev : ObsFn W "KernelRoles::open_two_lams" [e] h r h' cs) :
    ∃ body types, r = .tuple [body, types] ∧ Tm κ 2 Γ h' 0 (open₂ T₁ T₂ B) body ∧
      TypesRep κ Γ h' 2 types ∧ Heap.Extends h h' := by
  match Obs.«KernelRoles::open_two_lams».obs ev with
  | .run (x_t1 := xt1) (x_t2 := xt2) (x_body := xbody) (m84 := m84) (m106 := m106)
      (m128 := m128) (ld12 := ld1) (ld47 := ld2) (he75 := hr) (hm92 := hm84) (hm114 := hm106)
      (hm136 := hm128) (he140 := hh) .. =>
    subst hr
    rw [hh]
    obtain ⟨T, B', ℓ, hEq, ht1, hin, -⟩ := (hE 0 Γ).lam_of_load ld1
    injection hEq with e1 e2 e3
    subst e1 e2
    obtain ⟨T', B'', ℓ', hEq', ht2, hbody, -⟩ := hin.lam_of_load ld2
    injection hEq' with e4 e5 e6
    subst e4 e5
    have c0 : m128[h.length]? = some (.construct kexprListEnum "Nil" []) := by
      rw [hm128]; simp
    have c1 : m106[m128.length]? = some (.construct kexprListEnum "Cons"
        [xt1, .ptr (.enum kexprListEnum) h.length]) := by
      rw [hm106]; simp
    have c2 : m84[m106.length]? = some (.construct kexprListEnum "Cons"
        [xt2, .ptr (.enum kexprListEnum) m128.length]) := by
      rw [hm84]; simp
    have x0 : Heap.Extends h m128 := ext_snoc hm128
    have x1 : Heap.Extends m128 m106 := ext_snoc hm106
    have x2 : Heap.Extends m106 m84 := ext_snoc hm84
    have ext : Heap.Extends h m84 := x0.trans (x1.trans x2)
    have hΓnil : ∀ j, j < 0 → Γ j = Γ j := fun _ _ => rfl
    refine ⟨xbody, _, rfl, ?_, ?_, ext⟩
    · have b1 := hbody.open (d := 0) (Γ' := Γ) hΓ0 hΓnil 1 rfl
      have b2 := b1.open (d := 1) (Γ' := Γ) hΓ1 (fun _ _ => rfl) 0 rfl
      exact b2.mono ext
    · refine .cons c2 ?_ (.cons (x2.getElem?_eq c1) ?_ (.nil ((x1.trans x2).getElem?_eq c0)))
      · rw [hΓ1]
        exact (ht2.open (d := 0) (Γ' := Γ) hΓ0 hΓnil 0 rfl).mono ext
      · rw [hΓ0]
        exact ht1.mono ext

/-! ## A rendered equation side, opened and with the operation replaced -/

/-- The type of the natural numbers. -/
abbrev natTy : KExpr := .const (Ix.Kernel.natName : KKey) []

/-- The ghost context of two `Nat` variables is scoped. -/
theorem ghostScoped_natTy (d : Nat) : GhostScoped (fun _ => natTy) d :=
  fun _ _ => Ix.Kernel.wscopedB_of_not_hasFvar rfl

/-- **One side of an operation's recurrence, opened and with the operation replaced by its
value**: when the rendered side `e` represents the closed `λ (x y : Nat), L` whose opening is
the side `l` of an equation of `natOpEquations 0 c`, `open_two_lams(e)` followed by
`subst_const(body, a, v)` represents `Expr.substConst0 c val l` at depth 2, with the context
list of the two `Nat` variables, under a scoped ghost context. -/
theorem op_equation_side_spec {κ : _root_.Address → KKey} {h h₁ h₂ : Heap F}
    {e a v body types r : SourceValue F} {cs₁ cs₂ : List (Call F)} {b : Bytes.Address}
    {c : KKey} {val L l : KExpr} {m₁ m₂ : Ix.Kernel.BinderMeta} {eq : KExpr × KExpr}
    (heq : eq ∈ Ix.Kernel.natOpEquations 0 c) (hl : l = eq.1 ∨ l = eq.2)
    (hE : TmC κ h (.lam natTy (.lam natTy L m₂) m₁) e) (hL : open₂ natTy natTy L = l)
    (hc : κ (ixAddr b) = c) (hinj : ∀ b', κ (ixAddr b') = κ (ixAddr b) → b' = b)
    (ha : Bytes.RepAddressRef addrTy h b a) (hv : TmC κ h val v)
    (ev₁ : ObsFn W "KernelRoles::open_two_lams" [e] h (.tuple [body, types]) h₁ cs₁)
    (ev₂ : ObsFn W "KernelSubst::subst_const" [body, a, v] h₁ r h₂ cs₂) :
    Tm κ 2 (fun _ => natTy) h₂ 0 (Expr.substConst0 c val l) r ∧
      TypesRep κ (fun _ => natTy) h₂ 2 types ∧ GhostScoped (fun _ => natTy) 2 ∧
      Heap.Extends h h₂ := by
  obtain ⟨body', types', htup, hbody, htypes, ext₁⟩ :=
    open_two_lams_spec (Γ := fun _ => natTy) hE rfl rfl ev₁
  cases htup
  rw [hL] at hbody
  obtain ⟨hr, ext₂⟩ := subst_const_spec hinj (Bytes.repAddressRef_heapMono₂ addrTy ext₁ ha)
    (hv.mono ext₁) hbody ev₂
  have hbf : binderFree l = true := by
    rcases hl with rfl | rfl
    · exact (natOpEquations_sides_binderFree heq).1
    · exact (natOpEquations_sides_binderFree heq).2
  rw [hc, substConstAll_eq_substConst0 c val l hbf] at hr
  exact ⟨hr, htypes.mono ext₂, ghostScoped_natTy 2, ext₁.trans ext₂⟩

/-! ## `KernelRoles::open_foralls` -/

/-- **The first `n` cells of the `∀`-spine of `e` are `Forall` cells.** The term relation reads a
`Let` cell as its ζ-reduct, which may be a `∀`; `open_foralls` stops at such a cell. This
predicate states that it does not stop within the first `n` binders. -/
inductive ForallSpine (h : Heap F) : Nat → SourceValue F → Prop where
  | zero (e : SourceValue F) : ForallSpine h 0 e
  | succ {n : Nat} {e t b l : SourceValue F}
      (ld : loadValue h e = .ok (.construct kexprEnum "Forall" [t, b, l]))
      (rest : ForallSpine h n b) : ForallSpine h (n + 1) e

theorem ForallSpine.mono {h₁ h₂ : Heap F} {n : Nat} {e : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (sp : ForallSpine h₁ n e) : ForallSpine h₂ n e := by
  induction sp with
  | zero e => exact .zero e
  | succ ld _ ih => exact .succ (ext.loadValue_eq ld) ih

private theorem load_ctor_ne {h : Heap F} {p : SourceValue F} {c c' : String}
    {xs ys : List (SourceValue F)}
    (l1 : loadValue h p = .ok (.construct kexprEnum c xs))
    (l2 : loadValue h p = .ok (.construct kexprEnum c' ys)) (hne : c ≠ c') : False := by
  rw [l1] at l2
  injection l2 with l2
  injection l2 with _ hc
  exact hne hc

private theorem load_ctor_eq {h : Heap F} {p v1 : SourceValue F} {c : String}
    {xs : List (SourceValue F)}
    (l1 : loadValue h p = .ok (.construct kexprEnum c xs)) (l2 : loadValue h p = .ok v1) :
    v1 = .construct kexprEnum c xs := by
  rw [l1] at l2
  injection l2 with l2
  exact l2.symm

/-- **`subst_const` keeps a `Forall` spine**: it rebuilds a `Forall` cell as a `Forall` cell. -/
theorem subst_const_forallSpine :
    ∀ (n : Nat) {e a v r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ForallSpine h n e → ObsFn W "KernelSubst::subst_const" [e, a, v] h r h' cs →
      ForallSpine h' n r := by
  intro n
  induction n with
  | zero => intro e a v r h h' cs _ _; exact .zero r
  | succ n ih =>
    intro e a v r h h' cs sp ev
    cases sp with
    | succ ld rest =>
      match Obs.«KernelSubst::subst_const».obs ev with
      | .Forall (x_bl := xbl) (v389 := w1) (v390 := w2) (ld12 := l2) (he385 := hr)
          (hm384 := hm) (ev403 := e1) (ev439 := e2) .. =>
        have ext3 := ext_snoc hm
        have l' : loadValue h' r = .ok (.construct kexprEnum "Forall" [w1, w2, xbl]) := by
          rw [hm, hr]; exact loadValue_enum_cell (by simp)
        have hc := load_ctor_eq ld l2
        injection hc with _ _ hxs
        injection hxs with _ hxs
        injection hxs with hb
        subst hb
        have sp' := ih (rest.mono e1.heap_extends) e2
        exact .succ l' (sp'.mono ext3)
      | .Const_n1_Nil (ld12 := l2) .. => exact (load_ctor_ne ld l2 (by decide)).elim
      | .Const_n1_Cons (ld12 := l2) .. => exact (load_ctor_ne ld l2 (by decide)).elim
      | .Const_other (ld12 := l2) .. => exact (load_ctor_ne ld l2 (by decide)).elim
      | .App (ld12 := l2) .. => exact (load_ctor_ne ld l2 (by decide)).elim
      | .Lam (ld12 := l2) .. => exact (load_ctor_ne ld l2 (by decide)).elim
      | .Let (ld12 := l2) .. => exact (load_ctor_ne ld l2 (by decide)).elim
      | .Proj (ld12 := l2) .. => exact (load_ctor_ne ld l2 (by decide)).elim
      | .other (ld12 := l2) (hne472 := n4) .. => exact (n4 _ rfl (load_ctor_eq ld l2)).elim

/-- One binder of `Ix.Kernel.openPisAtFvars`. -/
theorem openPisAtFvars_succ_inv {n d : Nat} {E body : KExpr} {fvs : List KExpr}
    (hop : Ix.Kernel.openPisAtFvars (n + 1) E d = some (fvs, body)) :
    ∃ T B m fvs', E = .forallE T B m ∧ fvs = .fvar d T :: fvs' ∧
      Ix.Kernel.openPisAtFvars n (B.instantiate1 (.fvar d T)) (d + 1) = some (fvs', body) := by
  match E, hop with
  | .forallE T B m, hop =>
    simp only [Ix.Kernel.openPisAtFvars] at hop
    cases hq : Ix.Kernel.openPisAtFvars n (B.instantiate1 (.fvar d T)) (d + 1) with
    | none => rw [hq] at hop; cases hop
    | some q =>
      rw [hq] at hop
      obtain ⟨fvs', body'⟩ := q
      simp only [Option.some.injEq, Prod.mk.injEq] at hop
      obtain ⟨rfl, rfl⟩ := hop
      exact ⟨T, B, m, fvs', rfl, rfl, hq⟩
  | .bvar _, hop => cases hop
  | .fvar _ _, hop => cases hop
  | .sort _, hop => cases hop
  | .const _ _, hop => cases hop
  | .app _ _, hop => cases hop
  | .lam _ _ _, hop => cases hop
  | .letE _ _ _ _, hop => cases hop
  | .lit _, hop => cases hop
  | .proj _ _ _, hop => cases hop

/-- **`KernelRoles::open_foralls(e, acc)`**: on a term `E` represented at opening depth `d` whose
first `n` binders the kernel opens at the variables `d, …, d + n - 1` typed by the ghost context
(`openPisAtFvars`), to a body that is not a `∀`, along a spine of `Forall` cells, and on a
context list `acc` ending at `d`, the result is the body represented at depth `d + n` and the
context list extended by the `n` binder types, innermost first. -/
theorem open_foralls_spec {κ : _root_.Address → KKey} {Γ : Nat → KExpr} :
    ∀ (n : Nat) {d : Nat} {E body : KExpr} {fvs : List KExpr} {e acc r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      Ix.Kernel.openPisAtFvars n E d = some (fvs, body) →
      fvs = (List.range n).map (fun j => .fvar (d + j) (Γ (d + j))) →
      (∀ T B m, body ≠ .forallE T B m) →
      ForallSpine h n e → Tm κ d Γ h 0 E e → TypesRep κ Γ h d acc →
      ObsFn W "KernelRoles::open_foralls" [e, acc] h r h' cs →
      ∃ bodyp typesp, r = .tuple [bodyp, typesp] ∧ Tm κ (d + n) Γ h' 0 body bodyp ∧
        TypesRep κ Γ h' (d + n) typesp ∧ Heap.Extends h h' := by
  intro n
  induction n with
  | zero =>
    intro d E body fvs e acc r h h' cs hop hfvs hnf sp hE hacc ev
    simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨-, rfl⟩ := hop
    match Obs.«KernelRoles::open_foralls».obs ev with
    | .Forall (ld12 := ld) .. =>
      obtain ⟨T, B, ℓ, hEq, -⟩ := hE.forallE_of_load ld
      exact (hnf _ _ _ hEq).elim
    | .other (he89 := hr) (he104 := hh) .. =>
      subst hr hh
      exact ⟨e, acc, rfl, hE, hacc, Heap.Extends.refl _⟩
  | succ n ih =>
    intro d E body fvs e acc r h h' cs hop hfvs hnf sp hE hacc ev
    obtain ⟨T, B, m, fvs', rfl, rfl, hop'⟩ := openPisAtFvars_succ_inv hop
    rw [List.range_succ_eq_map, List.map_cons, List.map_map] at hfvs
    injection hfvs with hhd hrest
    injection hhd with _ hT
    have hT' : Γ d = T := hT.symm
    have hfvs' : fvs' = (List.range n).map (fun j => .fvar (d + 1 + j) (Γ (d + 1 + j))) := by
      rw [hrest]
      apply List.map_congr_left
      intro j _
      have e' : d + (j + 1) = d + 1 + j := by omega
      simp only [Function.comp_apply, Nat.succ_eq_add_one, e']
    cases sp with
    | succ ld rest =>
      match Obs.«KernelRoles::open_foralls».obs ev with
      | .Forall (x_t := xt) (m52 := m52) (ld12 := l2) (hm60 := hm) (ev41 := er) .. =>
        have hcell := load_ctor_eq ld l2
        injection hcell with _ _ hxs
        injection hxs with ht hxs
        injection hxs with hb
        subst ht hb
        have ext := ext_snoc hm
        obtain ⟨T₀, B₀, ℓ, hEq, htT, hbB, -⟩ := hE.forallE_of_load ld
        injection hEq with e1 e2 e3
        subst e1 e2
        have rt : Tm κ d Γ (h ++ [.construct kexprListEnum "Cons" [xt, acc]]) 0 (Γ d) xt := by
          rw [hT']; exact htT.mono (Heap.Extends.snoc _ _)
        have hacc' : TypesRep κ Γ m52 (d + 1) (.ptr (.enum kexprListEnum) h.length) := by
          rw [hm]
          exact .cons (by simp) rt (hacc.mono (Heap.Extends.snoc _ _))
        have hbody := (hbB.open (d := d) (Γ' := Γ) hT' (fun _ _ => rfl) 0 rfl).mono ext
        obtain ⟨bodyp, typesp, hr, hb, ht, hx⟩ :=
          ih hop' hfvs' hnf (rest.mono ext) hbody hacc' er
        have e' : d + 1 + n = d + (n + 1) := by omega
        rw [e'] at hb ht
        exact ⟨bodyp, typesp, hr, hb, ht, ext.trans hx⟩
      | .other (ld12 := l2) (hne81 := n4) .. => exact (n4 _ rfl (load_ctor_eq ld l2)).elim

/-! ## The applied certificate proof -/

theorem repList_imp {α : Type} {en : String} {R S : Heap F → α → SourceValue F → Prop}
    (hRS : ∀ h x v, R h x v → S h x v) {h : Heap F} {xs : List α} {p : SourceValue F}
    (rep : RepList en R h xs p) : RepList en S h xs p := by
  induction rep with
  | nil cell => exact .nil cell
  | cons cell hx _ ih => exact .cons cell (hRS _ _ _ hx) ih

/-- **`apply_spine(p, bvars_desc(d, d))`**: the term `p` represents, applied to the `d` opened
variables in order (`BVar(d - 1)` … `BVar(0)` at depth `d`, the variables `0, …, d - 1`). -/
theorem apply_bvars_desc_spec {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {d : Nat} {top : F}
    {P : KExpr} {p sp r : SourceValue F} {h h₁ h₂ : Heap F} {cs₁ cs₂ : List (Call F)}
    (htop : ZMod.val top = d) (hd : d < 4611686018427387904) (hP : Tm κ d Γ h 0 P p)
    (ev₁ : ObsFn W "KernelModeled::bvars_desc" [.field top, .field top] h sp h₁ cs₁)
    (ev₂ : ObsFn W "KernelWhnf::apply_spine" [p, sp] h₁ r h₂ cs₂) :
    Tm κ d Γ h₂ 0 (Expr.mkAppN P ((List.range d).map fun m => .fvar m (Γ m))) r ∧
      Heap.Extends h h₂ := by
  have hsp := Decl.bvars_desc_exact_wide (κ := κ) (Γ := Γ) (d := d) (Nat.le_refl _)
    (Nat.le_of_eq htop) hd ev₁
  simp only [htop, Nat.sub_self, Nat.zero_add] at hsp
  have hsp' : RepList kexprListEnum (fun h A p => Tm κ d Γ h 0 A p) h₁
      ((List.range d).map fun m => .fvar m (Γ m)) sp :=
    repList_imp (fun _ _ _ x => Decl.TmExact.toTm x) hsp
  exact ⟨Decl.apply_spine_tm ev₂ (hP.mono ev₁.heap_extends) hsp',
    ev₁.heap_extends.trans ev₂.heap_extends⟩

/-- **The variables applied are the certificate's**: under a ghost context giving `x`, `y` the
type `Nat` and the hypotheses their statements, the proof applied to the `2 + n` opened
variables is `divModCertApplied`. -/
theorem mkAppN_fvars_divModCertApplied {Γ : Nat → KExpr} {P : KExpr} {hyps : List KExpr}
    (h0 : Γ 0 = natTy) (h1 : Γ 1 = natTy)
    (hh : ∀ i (hi : i < hyps.length), Γ (2 + i) = hyps[i])
    (hlen : hyps.length = 1 ∨ hyps.length = 2) :
    Expr.mkAppN P ((List.range (2 + hyps.length)).map fun m => .fvar m (Γ m)) =
      Ix.Kernel.divModCertApplied P hyps := by
  match hyps, hh, hlen with
  | [a], hh, _ =>
    have ha : Γ 2 = a := hh 0 (by simp)
    show Expr.mkAppN P [.fvar 0 (Γ 0), .fvar 1 (Γ 1), .fvar 2 (Γ 2)] = _
    rw [h0, h1, ha]
    rfl
  | [a, b], hh, _ =>
    have ha : Γ 2 = a := hh 0 (by simp)
    have hb : Γ 3 = b := hh 1 (by simp)
    show Expr.mkAppN P [.fvar 0 (Γ 0), .fvar 1 (Γ 1), .fvar 2 (Γ 2), .fvar 3 (Γ 3)] = _
    rw [h0, h1, ha, hb]
    rfl
  | [], _, hlen => simp only [List.length_nil] at hlen; omega
  | _ :: _ :: _ :: _, _, hlen => simp only [List.length_cons] at hlen; omega

end IxVM.Refinement.Binding.OpOpen
