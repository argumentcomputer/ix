import IxVMRefinement.Binding.FamilyReconObs
import IxVMRefinement.Binding.FamilyFlat
import IxVMRefinement.Core.Open

/-! # Exact substitution specs on open terms (`TmExact` / `TmOExact`)

Direct `TmExact` specifications for `KernelSubst::expr_lift`, `KernelSubst::expr_lower`,
`KernelSubst::expr_inst1`, and `KernelSubst::has_bvar_in_range`, lifted to opening depth `0`
(`TmOExact`) via dummy variable opening/closing (`openDummies`, `closeDummies`):

* `tmExact_congr_ghost`, `tmExact_open`, `tmExact_close`, `tmExact_of_idxLt`;
* `expr_lift_exact`, `expr_lower_exact`, `expr_inst1_exact` (general opening depth `d`);
* `expr_lift_local_exact`, `expr_lift_tmOExact` (`liftLooseBVars`);
* `expr_inst1_local_exact`, `expr_inst1_tmOExact` (`instantiate1Lift`);
* `hasBVarIn_false_of_noIdx_tmExact`, `has_bvar_in_range_zero_tmOExact`;
* `expr_lower_local_exact`, `expr_lower_tmOExact` (`lowerBVars`). -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.Core.Specs.Subst (IdxAll IdxLt NoIdx NoIdxF BVarIm idxBound)
open IxVM.Refinement.Decl (TmExact)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open IxVM.Refinement.Binding.FamilyFlat (hasBVarIn)
open Ix.Kernel (Expr Level)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

local macro "rsubst_lt_calls" : term =>
  `(by simp only [List.length_cons, List.length_append, List.length_nil] <;> omega)

local macro "rsubst_sub_calls" : term =>
  `(fun _ hx => by simp [hx])

/-! ## `TmExact` opening, closing, ghost congruence, and index bounds -/

theorem tmExact_congr_ghost {κ : _root_.Address → KKey} {d : Nat} {Γ₁ Γ₂ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p : SourceValue F} (hΓ : ∀ j < d, Γ₁ j = Γ₂ j)
    (rep : TmExact κ d Γ₁ h k E p) : TmExact κ d Γ₂ h k E p := by
  induction rep with
  | bvarLocal cell hs hi => exact .bvarLocal cell hs hi
  | @bvarFree k' addr i cell hs hk hd =>
    have hlt : fvIdx d k' (ZMod.val i) < d := by unfold fvIdx; omega
    rw [hΓ _ hlt]
    exact .bvarFree cell hs hk hd
  | sort cell rl => exact .sort cell rl
  | const cell ra rls => exact .const cell ra rls
  | app cell _ _ ihf iha => exact .app cell ihf iha
  | lam cell _ _ rl iht ihb => exact .lam cell iht ihb rl
  | forallE cell _ _ rl iht ihb => exact .forallE cell iht ihb rl
  | letE cell _ _ _ iht ihv ihb => exact .letE cell iht ihv ihb
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | proj cell ra _ ihe => exact .proj cell ra ihe

theorem tmExact_open {κ : _root_.Address → KKey} {d : Nat} {Γ Γ' : Nat → KExpr} {h : Heap F}
    {T : KExpr} (hT : Γ' d = T) (hΓ : ∀ j, j < d → Γ' j = Γ j) {k' : Nat} {E : KExpr}
    {p : SourceValue F} (rep : TmExact κ d Γ h k' E p) :
    ∀ k, k' = k + 1 → TmExact κ (d + 1) Γ' h k (E.instantiate1 (.fvar d T) k) p := by
  induction rep with
  | @bvarLocal k₁ addr i cell hs hi =>
    intro k hk; subst hk
    simp only [Expr.instantiate1]
    by_cases hik : ZMod.val i = k
    · rw [ite_eq_left hik]
      have hf := TmExact.bvarFree (κ := κ) (d := d + 1) (Γ := Γ') (k := k) cell hs (by omega)
        (by omega)
      have e : fvIdx (d + 1) k (ZMod.val i) = d := by unfold fvIdx; omega
      rw [e, hT] at hf
      exact hf
    · rw [ite_eq_right hik, ite_eq_right (by omega)]
      exact .bvarLocal cell hs (by omega)
  | @bvarFree k₁ addr i cell hs hk hd =>
    intro k hk'; subst hk'
    simp only [Expr.instantiate1]
    have hf := TmExact.bvarFree (κ := κ) (d := d + 1) (Γ := Γ') (k := k) cell hs (by omega)
      (by omega)
    have e : fvIdx (d + 1) k (ZMod.val i) = fvIdx d (k + 1) (ZMod.val i) := by
      unfold fvIdx; omega
    rw [e, hΓ _ (by unfold fvIdx; omega)] at hf
    exact hf
  | sort cell rl => intro _ _; exact .sort cell rl
  | const cell ra rls => intro _ _; exact .const cell ra rls
  | app cell _ _ ihf iha =>
    intro k hk; simp only [Expr.instantiate1]; exact .app cell (ihf k hk) (iha k hk)
  | lam cell _ _ rl iht ihb =>
    intro k hk; simp only [Expr.instantiate1]
    exact .lam cell (iht k hk) (ihb (k + 1) (by omega)) rl
  | forallE cell _ _ rl iht ihb =>
    intro k hk; simp only [Expr.instantiate1]
    exact .forallE cell (iht k hk) (ihb (k + 1) (by omega)) rl
  | @letE k₁ addr tp vp bp T₀ V B cell _ _ _ iht ihv ihb =>
    intro k hk
    have hcomm := Expr.instantiate1Lift_instantiate1 (a := V) (s := (.fvar d T : KExpr))
      (by simp [Expr.looseBVarsBounded]) B 0 k
    simp only [Nat.zero_add] at hcomm
    rw [show (instShift V 0 B).instantiate1 (.fvar d T) k =
        (B.instantiate1Lift V 0).instantiate1 (.fvar d T) k from rfl, hcomm, Nat.add_comm 1 k]
    exact .letE cell (iht k hk) (ihv k hk) (ihb (k + 1) (by omega))
  | litNat cell rl hc => intro _ _; exact .litNat cell rl hc
  | litStr cell rb hs => intro _ _; exact .litStr cell rb hs
  | proj cell ra _ ihe =>
    intro k hk; simp only [Expr.instantiate1]; exact .proj cell ra (ihe k hk)

private theorem liftLooseBVars_abstract1 (j d : Nat) :
    ∀ (e : KExpr) (k c : Nat),
      (e.liftLooseBVars j c).abstract1 d (k + j + c) =
        (e.abstract1 d (k + c)).liftLooseBVars j c
  | .bvar m, k, c => by
    by_cases hmc : m ≥ c <;> simp [Expr.liftLooseBVars, Expr.abstract1, hmc]
  | .fvar idx ty, k, c => by
    by_cases hidx : idx = d
    · subst hidx
      simp [Expr.liftLooseBVars, Expr.abstract1, show k + c ≥ c by omega]; omega
    · simp [Expr.liftLooseBVars, Expr.abstract1, hidx]
  | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, k, c => by
    simp [Expr.liftLooseBVars, Expr.abstract1,
      liftLooseBVars_abstract1 j d f k c, liftLooseBVars_abstract1 j d a k c]
  | .lam t b _, k, c => by
    simp only [Expr.liftLooseBVars, Expr.abstract1]
    rw [liftLooseBVars_abstract1 j d t k c,
      show k + j + c + 1 = k + j + (c + 1) by omega,
      show k + c + 1 = k + (c + 1) by omega,
      liftLooseBVars_abstract1 j d b k (c + 1)]
  | .forallE t b _, k, c => by
    simp only [Expr.liftLooseBVars, Expr.abstract1]
    rw [liftLooseBVars_abstract1 j d t k c,
      show k + j + c + 1 = k + j + (c + 1) by omega,
      show k + c + 1 = k + (c + 1) by omega,
      liftLooseBVars_abstract1 j d b k (c + 1)]
  | .letE t v b _, k, c => by
    simp only [Expr.liftLooseBVars, Expr.abstract1]
    rw [liftLooseBVars_abstract1 j d t k c, liftLooseBVars_abstract1 j d v k c,
      show k + j + c + 1 = k + j + (c + 1) by omega,
      show k + c + 1 = k + (c + 1) by omega,
      liftLooseBVars_abstract1 j d b k (c + 1)]
  | .proj _ _ e, k, c => by
    simpa [Expr.liftLooseBVars, Expr.abstract1] using liftLooseBVars_abstract1 j d e k c

private theorem instantiate1Lift_abstract1 (v : KExpr) (d k : Nat) :
    ∀ (b : KExpr) (j : Nat),
      (b.instantiate1Lift v j).abstract1 d (k + j) =
        (b.abstract1 d (k + j + 1)).instantiate1Lift (v.abstract1 d k) j
  | .bvar i, j => by
    by_cases hij : i = j
    · subst i
      simp [Expr.instantiate1Lift, Expr.abstract1]
      simpa using liftLooseBVars_abstract1 j d v k 0
    · by_cases hgt : i > j <;> simp [Expr.instantiate1Lift, Expr.abstract1, hij, hgt]
  | .fvar idx ty, j => by
    by_cases hidx : idx = d
    · subst hidx
      simp [Expr.instantiate1Lift, Expr.abstract1,
        show k + j + 1 ≠ j by omega, show k + j + 1 > j by omega]
    · simp [Expr.instantiate1Lift, Expr.abstract1, hidx]
  | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, j => by
    simp [Expr.instantiate1Lift, Expr.abstract1,
      instantiate1Lift_abstract1 v d k f j, instantiate1Lift_abstract1 v d k a j]
  | .lam t b _, j => by
    simp only [Expr.instantiate1Lift, Expr.abstract1]
    rw [instantiate1Lift_abstract1 v d k t j,
      show k + j + 1 = k + (j + 1) by omega,
      instantiate1Lift_abstract1 v d k b (j + 1)]
  | .forallE t b _, j => by
    simp only [Expr.instantiate1Lift, Expr.abstract1]
    rw [instantiate1Lift_abstract1 v d k t j,
      show k + j + 1 = k + (j + 1) by omega,
      instantiate1Lift_abstract1 v d k b (j + 1)]
  | .letE t w b _, j => by
    simp only [Expr.instantiate1Lift, Expr.abstract1]
    rw [instantiate1Lift_abstract1 v d k t j, instantiate1Lift_abstract1 v d k w j,
      show k + j + 1 = k + (j + 1) by omega,
      instantiate1Lift_abstract1 v d k b (j + 1)]
  | .proj _ _ e, j => by
    simpa [Expr.instantiate1Lift, Expr.abstract1] using instantiate1Lift_abstract1 v d k e j

/-- Close one opened variable at `d` back into local binder `k` on `TmExact`. -/
theorem tmExact_close {κ : _root_.Address → KKey} {d : Nat} {Γ Γ' : Nat → KExpr} {h : Heap F}
    (hΓ : ∀ j, j < d → Γ' j = Γ j) {k : Nat} {E : KExpr} {p : SourceValue F}
    (rep : TmExact κ (d + 1) Γ h k E p) :
    TmExact κ d Γ' h (k + 1) (E.abstract1 d k) p := by
  induction rep with
  | @bvarLocal k₁ addr i cell hs hi => exact .bvarLocal cell hs (by omega)
  | @bvarFree k₁ addr i cell hs hk hd =>
    simp only [Expr.abstract1]
    by_cases hik : ZMod.val i = k₁
    · have hf_eq : fvIdx (d + 1) k₁ (ZMod.val i) = d := by unfold fvIdx; omega
      rw [ite_eq_left hf_eq, ← hik]
      exact .bvarLocal cell hs (by omega)
    · have hf_ne : fvIdx (d + 1) k₁ (ZMod.val i) ≠ d := by unfold fvIdx; omega
      rw [ite_eq_right hf_ne]
      have hf_eq : fvIdx (d + 1) k₁ (ZMod.val i) = fvIdx d (k₁ + 1) (ZMod.val i) := by
        unfold fvIdx; omega
      rw [hf_eq, ← hΓ _ (by unfold fvIdx; omega)]
      exact .bvarFree cell hs (by omega) (by omega)
  | sort cell rl => exact .sort cell rl
  | const cell ra rls => exact .const cell ra rls
  | app cell _ _ ihf iha => exact .app cell ihf iha
  | lam cell _ _ rl iht ihb => exact .lam cell iht ihb rl
  | forallE cell _ _ rl iht ihb => exact .forallE cell iht ihb rl
  | @letE k₁ addr tp vp bp T₀ V B cell _ _ _ iht ihv ihb =>
    have hcomm := instantiate1Lift_abstract1 V d k₁ B 0
    simp only [Nat.add_zero] at hcomm
    rw [show (instShift V 0 B).abstract1 d k₁ = (B.instantiate1Lift V 0).abstract1 d k₁ from rfl,
      hcomm]
    exact .letE cell iht ihv ihb
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | proj cell ra _ ihe => exact .proj cell ra ihe

/-- If every `BVar` index in `e` lies strictly below `b` (with `b ≤ k`), `TmExact` holds at any
target opening depth `(d', Γ')` and any local depth `k' ≥ b`. -/
private theorem tmExact_of_idxLt_aux {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {b : Nat} :
    ∀ {k₀ m : Nat} {E : KExpr} {e : SourceValue F},
      TmExact κ d Γ h k₀ E e →
      b + m ≤ k₀ →
      IdxAll h (fun n i => ZMod.val i < b + n) m e →
      ∀ d' Γ' k', b ≤ k' → TmExact κ d' Γ' h (k' + m) E e := by
  intro k₀ m E e rep
  induction rep generalizing m with
  | @bvarLocal _ addr i cell hs hi =>
    intro _ hidx d' Γ' k' hk'
    obtain ⟨i', hx, hlt⟩ := SubstAux.idxAll_bvar_inv hidx (loadValue_enum_cell cell)
    injection hx with hx; subst hx
    exact .bvarLocal cell hs (by omega)
  | @bvarFree _ addr i cell hs hk hd =>
    intro hle hidx
    exfalso
    obtain ⟨i', hx, hlt⟩ := SubstAux.idxAll_bvar_inv hidx (loadValue_enum_cell cell)
    injection hx with hx; subst hx
    omega
  | sort cell rl => intro _ _ _ _ _ _; exact .sort cell rl
  | const cell ra rls => intro _ _ _ _ _ _; exact .const cell ra rls
  | app cell _ _ ihf iha =>
    intro hle hidx d' Γ' k' hk'
    obtain ⟨nf, na⟩ := SubstAux.idxAll_app_inv hidx (loadValue_enum_cell cell)
    exact .app cell (ihf hle nf d' Γ' k' hk') (iha hle na d' Γ' k' hk')
  | lam cell _ _ rl iht ihb =>
    intro hle hidx d' Γ' k' hk'
    obtain ⟨nt, nb⟩ := SubstAux.idxAll_lam_inv hidx (loadValue_enum_cell cell)
    have hb' := ihb (m := m + 1) (by omega) nb d' Γ' k' hk'
    rw [show k' + (m + 1) = k' + m + 1 by omega] at hb'
    exact .lam cell (iht hle nt d' Γ' k' hk') hb' rl
  | forallE cell _ _ rl iht ihb =>
    intro hle hidx d' Γ' k' hk'
    obtain ⟨nt, nb⟩ := SubstAux.idxAll_forallE_inv hidx (loadValue_enum_cell cell)
    have hb' := ihb (m := m + 1) (by omega) nb d' Γ' k' hk'
    rw [show k' + (m + 1) = k' + m + 1 by omega] at hb'
    exact .forallE cell (iht hle nt d' Γ' k' hk') hb' rl
  | letE cell _ _ _ iht ihv ihb =>
    intro hle hidx d' Γ' k' hk'
    obtain ⟨nt, nv, nb⟩ := SubstAux.idxAll_letE_inv hidx (loadValue_enum_cell cell)
    have hb' := ihb (m := m + 1) (by omega) nb d' Γ' k' hk'
    rw [show k' + (m + 1) = k' + m + 1 by omega] at hb'
    exact .letE cell (iht hle nt d' Γ' k' hk') (ihv hle nv d' Γ' k' hk') hb'
  | litNat cell rl hc => intro _ _ _ _ _ _; exact .litNat cell rl hc
  | litStr cell rb hs => intro _ _ _ _ _ _; exact .litStr cell rb hs
  | proj cell ra _ ihe =>
    intro hle hidx d' Γ' k' hk'
    exact .proj cell ra
      (ihe hle (SubstAux.idxAll_proj_inv hidx (loadValue_enum_cell cell)) d' Γ' k' hk')

theorem tmExact_of_idxLt {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k b : Nat} {E : KExpr} {e : SourceValue F}
    (rep : TmExact κ d Γ h k E e) (hbk : b ≤ k) (hidx : IdxLt h b e) :
    ∀ d' Γ' k', b ≤ k' → TmExact κ d' Γ' h k' E e := by
  intro d' Γ' k' hk'
  simpa using tmExact_of_idxLt_aux (b := b) (m := 0) rep (by omega) hidx d' Γ' k' hk'

/-! ## Store and copy helpers for `TmExact` -/

private theorem tmExact_store_bvarLocal {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {i : F}
    (hs : ZMod.val i < 9223372036854775808) (hi : ZMod.val i < k) :
    TmExact κ d Γ (h ++ [.construct kexprEnum "BVar" [.field i]]) k (.bvar (ZMod.val i))
      (.ptr (.enum kexprEnum) h.length) :=
  .bvarLocal (by simp) hs hi

private theorem tmExact_store_bvarFree_eq {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {i : F} {j : Nat}
    (hs : ZMod.val i < 9223372036854775808) (hk : k ≤ ZMod.val i) (hd : ZMod.val i - k < d)
    (hj : fvIdx d k (ZMod.val i) = j) :
    TmExact κ d Γ (h ++ [.construct kexprEnum "BVar" [.field i]]) k (.fvar j (Γ j))
      (.ptr (.enum kexprEnum) h.length) := by
  subst hj; exact .bvarFree (by simp) hs hk hd

private theorem tmExact_store_app {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {Ef Ea : KExpr} {fp ap : SourceValue F}
    (rf : TmExact κ d Γ h k Ef fp) (ra : TmExact κ d Γ h k Ea ap) :
    TmExact κ d Γ (h ++ [.construct kexprEnum "App" [fp, ap]]) k (.app Ef Ea)
      (.ptr (.enum kexprEnum) h.length) :=
  let ext : Heap.Extends h (h ++ [.construct kexprEnum "App" [fp, ap]]) := Heap.Extends.snoc _ _
  .app (by simp) (rf.mono ext) (ra.mono ext)

private theorem tmExact_store_lam {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {T B : KExpr} {ℓ : KLevel} {tp bp lp : SourceValue F}
    (rt : TmExact κ d Γ h k T tp) (rb : TmExact κ d Γ h (k + 1) B bp) (rl : RepKLevel h ℓ lp) :
    TmExact κ d Γ (h ++ [.construct kexprEnum "Lam" [tp, bp, lp]]) k (.lam T B (bmeta ℓ))
      (.ptr (.enum kexprEnum) h.length) :=
  let ext : Heap.Extends h (h ++ [.construct kexprEnum "Lam" [tp, bp, lp]]) := Heap.Extends.snoc _ _
  .lam (by simp) (rt.mono ext) (rb.mono ext) (rl.mono ext)

private theorem tmExact_store_forallE {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {T B : KExpr} {ℓ : KLevel} {tp bp lp : SourceValue F}
    (rt : TmExact κ d Γ h k T tp) (rb : TmExact κ d Γ h (k + 1) B bp) (rl : RepKLevel h ℓ lp) :
    TmExact κ d Γ (h ++ [.construct kexprEnum "Forall" [tp, bp, lp]]) k (.forallE T B (bmeta ℓ))
      (.ptr (.enum kexprEnum) h.length) :=
  let ext : Heap.Extends h (h ++ [.construct kexprEnum "Forall" [tp, bp, lp]]) :=
    Heap.Extends.snoc _ _
  .forallE (by simp) (rt.mono ext) (rb.mono ext) (rl.mono ext)

private theorem tmExact_store_letE {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {T V B : KExpr} {tp vp bp : SourceValue F}
    (rt : TmExact κ d Γ h k T tp) (rv : TmExact κ d Γ h k V vp)
    (rb : TmExact κ d Γ h (k + 1) B bp) :
    TmExact κ d Γ (h ++ [.construct kexprEnum "Let" [tp, vp, bp]]) k (instShift V 0 B)
      (.ptr (.enum kexprEnum) h.length) :=
  let ext : Heap.Extends h (h ++ [.construct kexprEnum "Let" [tp, vp, bp]]) := Heap.Extends.snoc _ _
  .letE (by simp) (rt.mono ext) (rv.mono ext) (rb.mono ext)

private theorem tmExact_store_proj {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {a : Bytes.Address} [Resolved (κ (ixAddr a))]
    [ProjPermitted κ (ixAddr a)] {i : F} {E : KExpr} {ap ep : SourceValue F}
    (ra : Bytes.RepAddressRef addrTy h a ap) (re : TmExact κ d Γ h k E ep) :
    TmExact κ d Γ (h ++ [.construct kexprEnum "Proj" [ap, .field i, ep]]) k
      (.proj (κ (ixAddr a)) (ZMod.val i) E) (.ptr (.enum kexprEnum) h.length) :=
  let ext : Heap.Extends h (h ++ [.construct kexprEnum "Proj" [ap, .field i, ep]]) :=
    Heap.Extends.snoc _ _
  .proj (by simp) (Bytes.repAddressRef_heapMono₂ addrTy ext ra) (re.mono ext)

private theorem tmExact_copy_sort {κ : _root_.Address → KKey} {d d' : Nat} {Γ Γ' : Nat → KExpr}
    {h : Heap F} {k k' : Nat} {E : KExpr} {e lp : SourceValue F}
    (hE : TmExact κ d Γ h k E e) (ld : loadValue h e = .ok (.construct kexprEnum "Srt" [lp])) :
    TmExact κ d' Γ' (h ++ [.construct kexprEnum "Srt" [lp]]) k' E
      (.ptr (.enum kexprEnum) h.length) := by
  obtain ⟨l, rfl, rl⟩ := hE.sort_of_load ld
  exact .sort (by simp) (rl.mono (Heap.Extends.snoc _ _))

private theorem tmExact_copy_const {κ : _root_.Address → KKey} {d d' : Nat} {Γ Γ' : Nat → KExpr}
    {h : Heap F} {k k' : Nat} {E : KExpr} {e ap lsp : SourceValue F}
    (hE : TmExact κ d Γ h k E e)
    (ld : loadValue h e = .ok (.construct kexprEnum "Const" [ap, lsp])) :
    TmExact κ d' Γ' (h ++ [.construct kexprEnum "Const" [ap, lsp]]) k' E
      (.ptr (.enum kexprEnum) h.length) := by
  obtain ⟨a, ls, rfl, ra, rls⟩ := hE.const_of_load ld
  have : Resolved _ := ⟨hE.toTm.const_key_ne⟩
  have ext : Heap.Extends h (h ++ [.construct kexprEnum "Const" [ap, lsp]]) := Heap.Extends.snoc _ _
  exact .const (by simp) (Bytes.repAddressRef_heapMono₂ addrTy ext ra) (rls.mono ext)

private theorem tmExact_copy_lit {κ : _root_.Address → KKey} {d d' : Nat} {Γ Γ' : Nat → KExpr}
    {h : Heap F} {k k' : Nat} {E : KExpr} {e lp : SourceValue F}
    (hE : TmExact κ d Γ h k E e) (ld : loadValue h e = .ok (.construct kexprEnum "Lit" [lp])) :
    TmExact κ d' Γ' (h ++ [.construct kexprEnum "Lit" [lp]]) k' E
      (.ptr (.enum kexprEnum) h.length) := by
  have ext : Heap.Extends h (h ++ [.construct kexprEnum "Lit" [lp]]) := Heap.Extends.snoc _ _
  rcases hE.toTm.lit_of_load ld with ⟨_, limbs, rfl, rl, hc, rfl⟩ |
    ⟨_, bs, s, rfl, rb, hs, rfl⟩
  · exact .litNat (by simp) (repList_heapMono₂ _ repU64_heapMono₂ ext rl) hc
  · exact .litStr (by simp) (Bytes.repByteStream_heapMono₂ _ ext rb) hs

/-! ## General `TmExact` specs for `expr_lift`, `expr_lower`, and `expr_inst1` -/

private def LiftSpec (κ : _root_.Address → KKey) (args : List (SourceValue F)) (h : Heap F)
    (r : SourceValue F) (h' : Heap F) : Prop :=
  ∀ (e : SourceValue F) (s c : F), args = [e, .field s, .field c] →
    ZMod.val s < 4611686018427387904 →
    ∀ s₁ s₂, ZMod.val s = s₁ + s₂ → ∀ d Γ E,
      TmExact κ d Γ h (ZMod.val c) E e → TmExact κ (d + s₂) Γ h' (ZMod.val c + s₁) E r

private def LiftWalkSpec (κ : _root_.Address → KKey) (args : List (SourceValue F)) (h : Heap F)
    (r : SourceValue F) (h' : Heap F) : Prop :=
  ∀ (e : SourceValue F) (s c : F), args = [e, .field s, .field c] →
    ZMod.val s < 4611686018427387904 → ZMod.val c < 4294967296 →
    ∀ s₁ s₂, ZMod.val s = s₁ + s₂ → ∀ d Γ E,
      TmExact κ d Γ h (ZMod.val c) E e → TmExact κ (d + s₂) Γ h' (ZMod.val c + s₁) E r

private def LiftLetSpec (κ : _root_.Address → KKey) (args : List (SourceValue F)) (h : Heap F)
    (r : SourceValue F) (h' : Heap F) : Prop :=
  ∀ (ty val body : SourceValue F) (s c : F), args = [ty, val, body, .field s, .field c] →
    ZMod.val s < 4611686018427387904 → ZMod.val c < 4294967296 →
    ∀ s₁ s₂, ZMod.val s = s₁ + s₂ → ∀ d Γ T V B,
      TmExact κ d Γ h (ZMod.val c) T ty → TmExact κ d Γ h (ZMod.val c) V val →
      TmExact κ d Γ h (ZMod.val c + 1) B body →
      TmExact κ (d + s₂) Γ h' (ZMod.val c + s₁) (instShift V 0 B) r

private def LiftBVarSpec (κ : _root_.Address → KKey) (args : List (SourceValue F))
    (r : SourceValue F) (h' : Heap F) : Prop :=
  ∀ (i s c : F), args = [.field i, .field s, .field c] →
    ZMod.val s < 4611686018427387904 →
    ∀ s₁ s₂, ZMod.val s = s₁ + s₂ → ∀ d Γ E,
      BVarIm d Γ (ZMod.val c) (ZMod.val i) E → TmExact κ (d + s₂) Γ h' (ZMod.val c + s₁) E r

private def LowerSpec (κ : _root_.Address → KKey) (args : List (SourceValue F)) (h : Heap F)
    (r : SourceValue F) (h' : Heap F) : Prop :=
  ∀ (e : SourceValue F) (s c : F), args = [e, .field s, .field c] →
    ∀ s₁ s₂, ZMod.val s = s₁ + s₂ → s₁ ≤ ZMod.val c → ∀ d Γ E, s₂ ≤ d →
      TmExact κ d Γ h (ZMod.val c) E e →
      NoIdx h (ZMod.val c - s₁) (ZMod.val c + s₂) e →
      TmExact κ (d - s₂) Γ h' (ZMod.val c - s₁) E r

private def LowerWalkSpec (κ : _root_.Address → KKey) (args : List (SourceValue F)) (h : Heap F)
    (r : SourceValue F) (h' : Heap F) : Prop :=
  ∀ (e : SourceValue F) (s c : F), args = [e, .field s, .field c] →
    ZMod.val c < 4294967296 → ¬ IdxLt h (ZMod.val c) e →
    ∀ s₁ s₂, ZMod.val s = s₁ + s₂ → s₁ ≤ ZMod.val c → ∀ d Γ E, s₂ ≤ d →
      TmExact κ d Γ h (ZMod.val c) E e →
      NoIdx h (ZMod.val c - s₁) (ZMod.val c + s₂) e →
      TmExact κ (d - s₂) Γ h' (ZMod.val c - s₁) E r

private def LowerLetSpec (κ : _root_.Address → KKey) (args : List (SourceValue F)) (h : Heap F)
    (r : SourceValue F) (h' : Heap F) : Prop :=
  ∀ (ty val body : SourceValue F) (s c : F), args = [ty, val, body, .field s, .field c] →
    ZMod.val c < 4294967296 →
    ∀ s₁ s₂, ZMod.val s = s₁ + s₂ → s₁ ≤ ZMod.val c → ∀ d Γ T V B, s₂ ≤ d →
      TmExact κ d Γ h (ZMod.val c) T ty → TmExact κ d Γ h (ZMod.val c) V val →
      TmExact κ d Γ h (ZMod.val c + 1) B body →
      NoIdx h (ZMod.val c - s₁) (ZMod.val c + s₂) ty →
      NoIdx h (ZMod.val c - s₁) (ZMod.val c + s₂) val →
      NoIdx h (ZMod.val c + 1 - s₁) (ZMod.val c + 1 + s₂) body →
      TmExact κ (d - s₂) Γ h' (ZMod.val c - s₁) (instShift V 0 B) r

private def Inst1Spec (κ : _root_.Address → KKey) (args : List (SourceValue F)) (h : Heap F)
    (r : SourceValue F) (h' : Heap F) : Prop :=
  ∀ (e arg : SourceValue F) (j : F), args = [e, arg, .field j] →
    ∀ d Γ B A, TmExact κ d Γ h (ZMod.val j + 1) B e → TmExact κ d Γ h 0 A arg →
      TmExact κ d Γ h' (ZMod.val j) (B.instantiate1 A (ZMod.val j)) r

private def Inst1WalkSpec (κ : _root_.Address → KKey) (args : List (SourceValue F)) (h : Heap F)
    (r : SourceValue F) (h' : Heap F) : Prop :=
  ∀ (e arg : SourceValue F) (j : F), args = [e, arg, .field j] →
    ZMod.val j < 4294967296 →
    ∀ d Γ B A, TmExact κ d Γ h (ZMod.val j + 1) B e → TmExact κ d Γ h 0 A arg →
      TmExact κ d Γ h' (ZMod.val j) (B.instantiate1 A (ZMod.val j)) r

private def Inst1LetSpec (κ : _root_.Address → KKey) (args : List (SourceValue F)) (h : Heap F)
    (r : SourceValue F) (h' : Heap F) : Prop :=
  ∀ (ty val body arg : SourceValue F) (j : F), args = [ty, val, body, arg, .field j] →
    ZMod.val j < 4294967296 →
    ∀ d Γ T V B A,
      TmExact κ d Γ h (ZMod.val j + 1) T ty → TmExact κ d Γ h (ZMod.val j + 1) V val →
      TmExact κ d Γ h (ZMod.val j + 2) B body → TmExact κ d Γ h 0 A arg →
      TmExact κ d Γ h' (ZMod.val j) ((instShift V 0 B).instantiate1 A (ZMod.val j)) r

private def Inst1BVarSpec (κ : _root_.Address → KKey) (args : List (SourceValue F)) (h : Heap F)
    (r : SourceValue F) (h' : Heap F) : Prop :=
  ∀ (i : F) (arg : SourceValue F) (j : F), args = [.field i, arg, .field j] →
    ∀ d Γ B A, BVarIm d Γ (ZMod.val j + 1) (ZMod.val i) B → TmExact κ d Γ h 0 A arg →
      TmExact κ d Γ h' (ZMod.val j) (B.instantiate1 A (ZMod.val j)) r

private def SubstExactBundle (κ : _root_.Address → KKey) (fname : String)
    (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F) (h' : Heap F)
    (cs : List (Call F)) : Prop :=
  IxVM.Consistency.Bounded cs →
    (fname = "KernelSubst::expr_lift" → LiftSpec κ args h r h') ∧
    (fname = "KernelSubst::expr_lift_walk" → LiftWalkSpec κ args h r h') ∧
    (fname = "KernelSubst::expr_lift_let" → LiftLetSpec κ args h r h') ∧
    (fname = "KernelSubst::expr_lift_bvar" → LiftBVarSpec κ args r h') ∧
    (fname = "KernelSubst::expr_lower" → LowerSpec κ args h r h') ∧
    (fname = "KernelSubst::expr_lower_walk" → LowerWalkSpec κ args h r h') ∧
    (fname = "KernelSubst::expr_lower_let" → LowerLetSpec κ args h r h') ∧
    (fname = "KernelSubst::expr_inst1" → Inst1Spec κ args h r h') ∧
    (fname = "KernelSubst::expr_inst1_walk" → Inst1WalkSpec κ args h r h') ∧
    (fname = "KernelSubst::expr_inst1_let" → Inst1LetSpec κ args h r h') ∧
    (fname = "KernelSubst::expr_inst1_bvar" → Inst1BVarSpec κ args h r h')

private theorem subst_exact_bundle (κ : _root_.Address → KKey) :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn Obs.W fname args h r h' cs → SubstExactBundle κ fname args h r h' cs :=
  ObsFn.strong_induction (world := Obs.W) (SubstExactBundle κ) fun fname args h r h' cs ev ih bd => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- expr_lift
      intro hfn e s c hargs hs s₁ s₂ hsum d Γ E hE
      subst hfn hargs
      match Obs.«KernelSubst::expr_lift».obs ev with
      | .n0 (hv14 := hv) (he16 := hr) (he17 := he) .. =>
        subst hr he; injection hv with hv; subst hv
        rw [ZMod.val_zero] at hsum
        obtain ⟨rfl, rfl⟩ : s₁ = 0 ∧ s₂ = 0 := by omega
        exact hE
      | .other_n0 (ev36 := e1) (ev59 := e2) (he81 := hr) (he82 := he) (hc83 := hc) .. =>
        subst hc hr he
        obtain ⟨rfl, sl⟩ := SubstAux.gall κ .expr_lbr _ _ _ _ _ e1 _ rfl
          (bounded_sub rsubst_sub_calls bd)
        obtain ⟨c', y, hc', hy, -, -, hltf, rfl⟩ := SubstAux.ltf e2
        injection hc' with hc'; subst hc'
        have hge := SubstAux.ltf_zero hltf.symm
        obtain ⟨b, hb, b1, -, b3, -, -⟩ := sl d Γ (ZMod.val c) E hE.toTm
        rw [hb] at hy; injection hy with hy; subst hy
        rw [SubstAux.val_natCast (SubstAux.lt_mod_of_le_idx b1)] at hge
        exact tmExact_of_idxLt hE (by omega) b3 (d + s₂) Γ (ZMod.val c + s₁) (by omega)
      | .other_n1 (ev36 := e1) (ev59 := e2) (ev94 := e3) (hc119 := hc) .. =>
        subst hc
        obtain ⟨rfl, -⟩ := SubstAux.gall κ .expr_lbr _ _ _ _ _ e1 _ rfl
          (bounded_sub rsubst_sub_calls bd)
        obtain ⟨c', _, hc', _, hc32, -, -, rfl⟩ := SubstAux.ltf e2
        injection hc' with hc'; subst hc'
        exact (ih _ _ _ _ _ _ rsubst_lt_calls e3 (bounded_sub rsubst_sub_calls bd)).2.1
          rfl e s c rfl hs hc32 s₁ s₂ hsum d Γ E hE
    · -- expr_lift_walk
      intro hfn e s c hargs hs hc0 s₁ s₂ hsum d Γ E hE
      subst hfn hargs
      match Obs.«KernelSubst::expr_lift_walk».obs ev with
      | .BVar (ld12 := ld) (ev30 := e1) (hc55 := hc) .. =>
        subst hc
        obtain ⟨i, rfl, hsm, hbc⟩ := hE.bvar_of_load ld
        exact (ih _ _ _ _ _ _ rsubst_lt_calls e1 (bounded_sub rsubst_sub_calls bd)).2.2.2.1
          rfl i s c rfl hs s₁ s₂ hsum d Γ E ⟨hsm, hbc⟩
      | .Srt (ld12 := ld) (he72 := hr) (hm71 := hm) .. =>
        subst hr hm; exact tmExact_copy_sort hE ld
      | .Const (ld12 := ld) (he106 := hr) (hm105 := hm) .. =>
        subst hr hm; exact tmExact_copy_const hE ld
      | .Lit (ld12 := ld) (he554 := hr) (hm553 := hm) .. =>
        subst hr hm; exact tmExact_copy_lit hE ld
      | .App (ld12 := ld) (he148 := hr) (hm147 := hm) (ev165 := e1) (ev201 := e2)
          (hc226 := hc) .. =>
        subst hc hr hm
        obtain ⟨Ef, Ea, rfl, hf, ha⟩ := hE.app_of_load ld
        have sf := (ih _ _ _ _ _ _ rsubst_lt_calls e1 (bounded_sub rsubst_sub_calls bd)).1
          rfl _ s c rfl hs s₁ s₂ hsum d Γ Ef hf
        have sa := (ih _ _ _ _ _ _ rsubst_lt_calls e2 (bounded_sub rsubst_sub_calls bd)).1
          rfl _ s c rfl hs s₁ s₂ hsum d Γ Ea (ha.mono e1.heap_extends)
        exact tmExact_store_app (sf.mono e2.heap_extends) sa
      | .Lam (ld12 := ld) (he253 := hr) (hm252 := hm) (ev271 := e1) (op338 := op) (ev307 := e2)
          (hc347 := hc) .. =>
        subst hc hr hm; rw [SubstAux.add_ok op] at e2
        obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := hE.lam_of_load ld
        have st := (ih _ _ _ _ _ _ rsubst_lt_calls e1 (bounded_sub rsubst_sub_calls bd)).1
          rfl _ s c rfl hs s₁ s₂ hsum d Γ T ht
        have sb := (ih _ _ _ _ _ _ rsubst_lt_calls e2 (bounded_sub rsubst_sub_calls bd)).1
          rfl _ s (c + 1) rfl hs s₁ s₂ hsum d Γ B
          (by rw [SubstAux.val_succ32 hc0]; exact hb.mono e1.heap_extends)
        rw [SubstAux.val_succ32 hc0, show ZMod.val c + 1 + s₁ = ZMod.val c + s₁ + 1 by omega] at sb
        exact tmExact_store_lam (st.mono e2.heap_extends) sb
          (hl.mono (e1.heap_extends.trans e2.heap_extends))
      | .Forall (ld12 := ld) (he374 := hr) (hm373 := hm) (ev392 := e1) (op459 := op) (ev428 := e2)
          (hc468 := hc) .. =>
        subst hc hr hm; rw [SubstAux.add_ok op] at e2
        obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := hE.forallE_of_load ld
        have st := (ih _ _ _ _ _ _ rsubst_lt_calls e1 (bounded_sub rsubst_sub_calls bd)).1
          rfl _ s c rfl hs s₁ s₂ hsum d Γ T ht
        have sb := (ih _ _ _ _ _ _ rsubst_lt_calls e2 (bounded_sub rsubst_sub_calls bd)).1
          rfl _ s (c + 1) rfl hs s₁ s₂ hsum d Γ B
          (by rw [SubstAux.val_succ32 hc0]; exact hb.mono e1.heap_extends)
        rw [SubstAux.val_succ32 hc0, show ZMod.val c + 1 + s₁ = ZMod.val c + s₁ + 1 by omega] at sb
        exact tmExact_store_forallE (st.mono e2.heap_extends) sb
          (hl.mono (e1.heap_extends.trans e2.heap_extends))
      | .Let (ld12 := ld) (ev496 := e1) (hc537 := hc) .. =>
        subst hc
        obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := hE.letE_of_load ld
        exact (ih _ _ _ _ _ _ rsubst_lt_calls e1 (bounded_sub rsubst_sub_calls bd)).2.2.1
          rfl _ _ _ s c rfl hs hc0 s₁ s₂ hsum d Γ T V B ht hv hb
      | .Proj (ld12 := ld) (he593 := hr) (hm592 := hm) (ev625 := e1) (hc650 := hc) .. =>
        subst hc hr hm
        obtain ⟨a, i, Es, rfl, rfl, ra, hes⟩ := hE.proj_of_load ld
        have : Resolved _ := ⟨hE.toTm.proj_key_ne⟩
        have : ProjPermitted _ _ := hE.toTm.proj_permitted ld ra
        exact tmExact_store_proj (Bytes.repAddressRef_heapMono₂ addrTy e1.heap_extends ra)
          ((ih _ _ _ _ _ _ rsubst_lt_calls e1 (bounded_sub rsubst_sub_calls bd)).1
            rfl _ s c rfl hs s₁ s₂ hsum d Γ Es hes)
    · -- expr_lift_let
      intro hfn ty val body s c hargs hs hc0 s₁ s₂ hsum d Γ T V B ht hv hb
      subst hfn hargs
      match Obs.«KernelSubst::expr_lift_let».obs ev with
      | .run (he5 := hr) (hm4 := hm) (ev23 := e1) (ev59 := e2) (op126 := op) (ev95 := e3)
          (hc128 := hc) .. =>
        subst hc hr hm; rw [SubstAux.add_ok op] at e3
        have x1 := (ih _ _ _ _ _ _ rsubst_lt_calls e1 (bounded_sub rsubst_sub_calls bd)).1
          rfl _ s c rfl hs s₁ s₂ hsum d Γ T ht
        have x2 := (ih _ _ _ _ _ _ rsubst_lt_calls e2 (bounded_sub rsubst_sub_calls bd)).1
          rfl _ s c rfl hs s₁ s₂ hsum d Γ V (hv.mono e1.heap_extends)
        have x3 := (ih _ _ _ _ _ _ rsubst_lt_calls e3 (bounded_sub rsubst_sub_calls bd)).1
          rfl _ s (c + 1) rfl hs s₁ s₂ hsum d Γ B
          (by rw [SubstAux.val_succ32 hc0]; exact hb.mono (e1.heap_extends.trans e2.heap_extends))
        rw [SubstAux.val_succ32 hc0, show ZMod.val c + 1 + s₁ = ZMod.val c + s₁ + 1 by omega] at x3
        exact tmExact_store_letE ((x1.mono e2.heap_extends).mono e3.heap_extends)
          (x2.mono e3.heap_extends) x3
    · -- expr_lift_bvar
      intro hfn i s c hargs hs s₁ s₂ hsum d Γ E hcase
      subst hfn hargs
      obtain ⟨hsm, hbc⟩ := hcase
      cases Obs.«KernelSubst::expr_lift_bvar».obs ev with
      | n1 m2 cs13 ev15 he40 hm39 hc52 =>
        obtain ⟨i', c', hi', hc', -, -, hltf, rfl⟩ := SubstAux.ltf ev15
        injection hi' with hi'; injection hc' with hc'; subst hi' hc' he40 hm39
        have hlt := SubstAux.ltf_one hltf.symm
        rcases hbc with ⟨_, rfl⟩ | ⟨hk, _, _⟩
        · exact tmExact_store_bvarLocal hsm (by omega)
        · omega
      | n0 m2 cs13 v66 ev15 he62 hm61 op80 hc83 =>
        obtain ⟨i', c', hi', hc', hi32, -, hltf, rfl⟩ := SubstAux.ltf ev15
        injection hi' with hi'; injection hc' with hc'; subst hi' hc' he62 hm61
        have hge := SubstAux.ltf_zero hltf.symm
        rw [SubstAux.add_ok op80]
        have hv : ZMod.val (i + s) = ZMod.val i + ZMod.val s :=
          SubstAux.val_add (by
            have : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl; omega)
        rcases hbc with ⟨hlt, _⟩ | ⟨hk, hd, rfl⟩
        · omega
        · exact tmExact_store_bvarFree_eq (by omega) (by omega) (by omega)
            (by rw [hv]; unfold fvIdx; omega)
    · -- expr_lower
      intro hfn e s c hargs s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn
      subst hfn hargs
      match Obs.«KernelSubst::expr_lower».obs ev with
      | .n0 (hv14 := hv) (he16 := hr) (he17 := he) .. =>
        subst hr he; injection hv with hv; subst hv
        rw [ZMod.val_zero] at hsum
        obtain ⟨rfl, rfl⟩ : s₁ = 0 ∧ s₂ = 0 := by omega
        exact hE
      | .other_n0 (ev36 := e1) (ev59 := e2) (he81 := hr) (he82 := he) (hc83 := hc) .. =>
        subst hc hr he
        obtain ⟨rfl, sl⟩ := SubstAux.gall κ .expr_lbr _ _ _ _ _ e1 _ rfl
          (bounded_sub rsubst_sub_calls bd)
        obtain ⟨c', y, hc', hy, -, -, hltf, rfl⟩ := SubstAux.ltf e2
        injection hc' with hc'; subst hc'
        have hge := SubstAux.ltf_zero hltf.symm
        obtain ⟨b, hb, b1, -, b3, -, -⟩ := sl d Γ (ZMod.val c) E hE.toTm
        rw [hb] at hy; injection hy with hy; subst hy
        rw [SubstAux.val_natCast (SubstAux.lt_mod_of_le_idx b1)] at hge
        have hI : IdxLt h' (ZMod.val c - s₁) r :=
          SubstAux.idxAll_mono (SubstAux.idxAll_and b3 hn)
            (fun n i hi => by obtain ⟨h1, h2⟩ := hi; omega)
        exact tmExact_of_idxLt hE (by omega) hI (d - s₂) Γ (ZMod.val c - s₁) (Nat.le_refl _)
      | .other_n1 (ev36 := e1) (ev59 := e2) (ev94 := e3) (hc119 := hc) .. =>
        subst hc
        obtain ⟨rfl, sl⟩ := SubstAux.gall κ .expr_lbr _ _ _ _ _ e1 _ rfl
          (bounded_sub rsubst_sub_calls bd)
        obtain ⟨c', y, hc', hy, hc32, -, hltf, rfl⟩ := SubstAux.ltf e2
        injection hc' with hc'; subst hc'
        have hlt := SubstAux.ltf_one hltf.symm
        obtain ⟨b, hb, b1, -, -, bmin, -⟩ := sl d Γ (ZMod.val c) E hE.toTm
        rw [hb] at hy; injection hy with hy; subst hy
        rw [SubstAux.val_natCast (SubstAux.lt_mod_of_le_idx b1)] at hlt
        exact (ih _ _ _ _ _ _ rsubst_lt_calls e3 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.2.1
          rfl e s c rfl hc32 (bmin _ hlt) s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn
    · -- expr_lower_walk
      intro hfn e s c hargs hc0 hnlt s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn
      subst hfn hargs
      match Obs.«KernelSubst::expr_lower_walk».obs ev with
      | .BVar (ld12 := ld) (he29 := hr) (hm28 := hm) (op47 := op) (hc50 := hc) .. =>
        subst hc hr hm
        obtain ⟨i, rfl, hsm, hbc⟩ := hE.bvar_of_load ld
        have hge : ZMod.val c ≤ ZMod.val i := by
          apply Nat.le_of_not_lt; intro hlt
          exact hnlt (SubstAux.idxAll_bvar_of_load ld (by show ZMod.val i < ZMod.val c + 0; omega))
        obtain ⟨i', hx, hw⟩ := SubstAux.idxAll_bvar_inv hn ld
        injection hx with hx; subst hx
        have hw' : ZMod.val c + s₂ ≤ ZMod.val i := by
          have : ZMod.val i < ZMod.val c - s₁ + 0 ∨ ZMod.val c + s₂ + 0 ≤ ZMod.val i := hw
          omega
        rcases hbc with ⟨hlt, _⟩ | ⟨hk, hd, rfl⟩
        · omega
        · rw [SubstAux.sub_ok op]
          have hv : ZMod.val (i - s) = ZMod.val i - ZMod.val s := SubstAux.val_sub (by omega)
          exact tmExact_store_bvarFree_eq (by omega) (by omega) (by omega)
            (by rw [hv]; unfold fvIdx; omega)
      | .Srt (ld12 := ld) (he67 := hr) (hm66 := hm) .. =>
        subst hr hm; exact tmExact_copy_sort hE ld
      | .Const (ld12 := ld) (he101 := hr) (hm100 := hm) .. =>
        subst hr hm; exact tmExact_copy_const hE ld
      | .Lit (ld12 := ld) (he549 := hr) (hm548 := hm) .. =>
        subst hr hm; exact tmExact_copy_lit hE ld
      | .App (ld12 := ld) (he143 := hr) (hm142 := hm) (ev160 := e1) (ev196 := e2)
          (hc221 := hc) .. =>
        subst hc hr hm
        obtain ⟨Ef, Ea, rfl, hf, ha⟩ := hE.app_of_load ld
        obtain ⟨nf, na⟩ := SubstAux.idxAll_app_inv hn ld
        have sf := (ih _ _ _ _ _ _ rsubst_lt_calls e1 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.1
          rfl _ s c rfl s₁ s₂ hsum hs₁ d Γ Ef hs₂ hf nf
        have sa := (ih _ _ _ _ _ _ rsubst_lt_calls e2 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.1
          rfl _ s c rfl s₁ s₂ hsum hs₁ d Γ Ea hs₂ (ha.mono e1.heap_extends)
          (SubstAux.idxAll_heap e1.heap_extends na)
        exact tmExact_store_app (sf.mono e2.heap_extends) sa
      | .Lam (ld12 := ld) (he248 := hr) (hm247 := hm) (ev266 := e1) (op333 := op) (ev302 := e2)
          (hc342 := hc) .. =>
        subst hc hr hm; rw [SubstAux.add_ok op] at e2
        obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := hE.lam_of_load ld
        obtain ⟨nt, nb⟩ := SubstAux.idxAll_lam_inv hn ld
        have st := (ih _ _ _ _ _ _ rsubst_lt_calls e1 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.1
          rfl _ s c rfl s₁ s₂ hsum hs₁ d Γ T hs₂ ht nt
        have sb := (ih _ _ _ _ _ _ rsubst_lt_calls e2 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.1
          rfl _ s (c + 1) rfl s₁ s₂ hsum (by rw [SubstAux.val_succ32 hc0]; omega) d Γ B hs₂
          (by rw [SubstAux.val_succ32 hc0]; exact hb.mono e1.heap_extends)
          (by rw [SubstAux.val_succ32 hc0]
              exact SubstAux.noIdx_unbody (SubstAux.idxAll_heap e1.heap_extends nb)
                (by omega) (by omega))
        rw [SubstAux.val_succ32 hc0, show ZMod.val c + 1 - s₁ = ZMod.val c - s₁ + 1 by omega] at sb
        exact tmExact_store_lam (st.mono e2.heap_extends) sb
          (hl.mono (e1.heap_extends.trans e2.heap_extends))
      | .Forall (ld12 := ld) (he369 := hr) (hm368 := hm) (ev387 := e1) (op454 := op) (ev423 := e2)
          (hc463 := hc) .. =>
        subst hc hr hm; rw [SubstAux.add_ok op] at e2
        obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := hE.forallE_of_load ld
        obtain ⟨nt, nb⟩ := SubstAux.idxAll_forallE_inv hn ld
        have st := (ih _ _ _ _ _ _ rsubst_lt_calls e1 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.1
          rfl _ s c rfl s₁ s₂ hsum hs₁ d Γ T hs₂ ht nt
        have sb := (ih _ _ _ _ _ _ rsubst_lt_calls e2 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.1
          rfl _ s (c + 1) rfl s₁ s₂ hsum (by rw [SubstAux.val_succ32 hc0]; omega) d Γ B hs₂
          (by rw [SubstAux.val_succ32 hc0]; exact hb.mono e1.heap_extends)
          (by rw [SubstAux.val_succ32 hc0]
              exact SubstAux.noIdx_unbody (SubstAux.idxAll_heap e1.heap_extends nb)
                (by omega) (by omega))
        rw [SubstAux.val_succ32 hc0, show ZMod.val c + 1 - s₁ = ZMod.val c - s₁ + 1 by omega] at sb
        exact tmExact_store_forallE (st.mono e2.heap_extends) sb
          (hl.mono (e1.heap_extends.trans e2.heap_extends))
      | .Let (ld12 := ld) (ev491 := e1) (hc532 := hc) .. =>
        subst hc
        obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := hE.letE_of_load ld
        obtain ⟨nt, nv, nb⟩ := SubstAux.idxAll_letE_inv hn ld
        exact (ih _ _ _ _ _ _ rsubst_lt_calls e1 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.2.2.1
          rfl _ _ _ s c rfl hc0 s₁ s₂ hsum hs₁ d Γ T V B hs₂ ht hv hb nt nv
          (SubstAux.noIdx_unbody nb (by omega) (by omega))
      | .Proj (ld12 := ld) (he588 := hr) (hm587 := hm) (ev620 := e1) (hc645 := hc) .. =>
        subst hc hr hm
        obtain ⟨a, i, Es, rfl, rfl, ra, hes⟩ := hE.proj_of_load ld
        have : Resolved _ := ⟨hE.toTm.proj_key_ne⟩
        have : ProjPermitted _ _ := hE.toTm.proj_permitted ld ra
        exact tmExact_store_proj (Bytes.repAddressRef_heapMono₂ addrTy e1.heap_extends ra)
          ((ih _ _ _ _ _ _ rsubst_lt_calls e1 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.1
            rfl _ s c rfl s₁ s₂ hsum hs₁ d Γ Es hs₂ hes (SubstAux.idxAll_proj_inv hn ld))
    · -- expr_lower_let
      intro hfn ty val body s c hargs hc0 s₁ s₂ hsum hs₁ d Γ T V B hs₂ ht hv hb nt nv nb
      subst hfn hargs
      match Obs.«KernelSubst::expr_lower_let».obs ev with
      | .run (he5 := hr) (hm4 := hm) (ev23 := e1) (ev59 := e2) (op126 := op) (ev95 := e3)
          (hc128 := hc) .. =>
        subst hc hr hm; rw [SubstAux.add_ok op] at e3
        have x1 := (ih _ _ _ _ _ _ rsubst_lt_calls e1 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.1
          rfl _ s c rfl s₁ s₂ hsum hs₁ d Γ T hs₂ ht nt
        have x2 := (ih _ _ _ _ _ _ rsubst_lt_calls e2 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.1
          rfl _ s c rfl s₁ s₂ hsum hs₁ d Γ V hs₂ (hv.mono e1.heap_extends)
          (SubstAux.idxAll_heap e1.heap_extends nv)
        have x3 := (ih _ _ _ _ _ _ rsubst_lt_calls e3 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.1
          rfl _ s (c + 1) rfl s₁ s₂ hsum (by rw [SubstAux.val_succ32 hc0]; omega) d Γ B hs₂
          (by rw [SubstAux.val_succ32 hc0]; exact hb.mono (e1.heap_extends.trans e2.heap_extends))
          (by rw [SubstAux.val_succ32 hc0]
              exact SubstAux.idxAll_heap (e1.heap_extends.trans e2.heap_extends) nb)
        rw [SubstAux.val_succ32 hc0, show ZMod.val c + 1 - s₁ = ZMod.val c - s₁ + 1 by omega] at x3
        exact tmExact_store_letE ((x1.mono e2.heap_extends).mono e3.heap_extends)
          (x2.mono e3.heap_extends) x3
    · -- expr_inst1
      intro hfn e arg j hargs d Γ B A hB hA
      subst hfn hargs
      match Obs.«KernelSubst::expr_inst1».obs ev with
      | .n0 (ev14 := e1) (ev37 := e2) (he59 := hr) (he60 := he) (hc61 := hc) .. =>
        subst hc hr he
        obtain ⟨rfl, sl⟩ := SubstAux.gall κ .expr_lbr _ _ _ _ _ e1 _ rfl
          (bounded_sub rsubst_sub_calls bd)
        obtain ⟨j', y, hj', hy, -, -, hltf, rfl⟩ := SubstAux.ltf e2
        injection hj' with hj'; subst hj'
        have hge := SubstAux.ltf_zero hltf.symm
        obtain ⟨b, hb, b1, -, b3, -, lb⟩ := sl d Γ (ZMod.val j + 1) B hB.toTm
        rw [hb] at hy; injection hy with hy; subst hy
        rw [SubstAux.val_natCast (SubstAux.lt_mod_of_le_idx b1)] at hge
        obtain ⟨l1, -, -⟩ := lb (by omega)
        rw [Expr.instantiate1_eq_self (SubstAux.lbb_mono (by omega) l1)]
        exact tmExact_of_idxLt hB (by omega) b3 d Γ (ZMod.val j) (by omega)
      | .n1_n1 (ev14 := e1) (ev37 := e2) (ev81 := e3) (ev107 := e4) (hc132 := hc) .. =>
        subst hc
        obtain ⟨rfl, -⟩ := SubstAux.gall κ .expr_lbr _ _ _ _ _ e1 _ rfl
          (bounded_sub rsubst_sub_calls bd)
        obtain ⟨j', _, hj', -, hj32, -, -, rfl⟩ := SubstAux.ltf e2
        injection hj' with hj'; subst hj'
        obtain ⟨rfl, -⟩ := SubstAux.gall κ .expr_has_bvar_at _ _ _ _ _ e3 _ _ rfl
          (bounded_sub rsubst_sub_calls bd)
        exact (ih _ _ _ _ _ _ rsubst_lt_calls e4 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.2.2.2.2.1
          rfl e arg j rfl hj32 d Γ B A hB hA
      | .n1_other (ev14 := e1) (ev37 := e2) (ev81 := e3) (hne133 := hne) (op172 := op)
          (ev142 := e4) (hc174 := hc) .. =>
        subst hc
        rw [SubstAux.add_ok op] at e4
        obtain ⟨rfl, -⟩ := SubstAux.gall κ .expr_lbr _ _ _ _ _ e1 _ rfl
          (bounded_sub rsubst_sub_calls bd)
        obtain ⟨j', _, hj', -, hj32, -, -, rfl⟩ := SubstAux.ltf e2
        injection hj' with hj'; subst hj'
        obtain ⟨rfl, h01, sn⟩ := SubstAux.gall κ .expr_has_bvar_at _ _ _ _ _ e3 _ _ rfl
          (bounded_sub rsubst_sub_calls bd)
        have hn := sn (SubstAux.zero_of_ne_one h01 hne) d Γ (ZMod.val j + 1) B hB.toTm
        have hlow :=
          (ih _ _ _ _ _ _ rsubst_lt_calls e4 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.1
            rfl e (1 : F) (j + 1) rfl 1 0
            (by rw [SubstAux.val_one]) (by rw [SubstAux.val_succ32 hj32]; omega) d Γ B
            (Nat.zero_le _) (by rw [SubstAux.val_succ32 hj32]; exact hB)
            (by rw [SubstAux.val_succ32 hj32, Nat.add_sub_cancel, Nat.add_zero]; exact hn)
        rw [SubstAux.val_succ32 hj32, Nat.add_sub_cancel, Nat.sub_zero] at hlow
        rw [Expr.instantiate1_eq_self (SubstAux.tm_lbb hB.toTm (Nat.le_succ _) hn)]
        exact hlow
    · -- expr_inst1_walk
      intro hfn e arg j hargs hj0 d Γ B A hB hA
      subst hfn hargs
      match Obs.«KernelSubst::expr_inst1_walk».obs ev with
      | .BVar (ld12 := ld) (ev30 := e1) (hc55 := hc) .. =>
        subst hc
        obtain ⟨i, rfl, hsm, hbc⟩ := hB.bvar_of_load ld
        exact (ih _ _ _ _ _ _ rsubst_lt_calls e1 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.2.2.2.2.2.2
          rfl i arg j rfl d Γ B A ⟨hsm, hbc⟩ hA
      | .Srt (ld12 := ld) (he72 := hr) (hm71 := hm) .. =>
        subst hr hm
        obtain ⟨l, rfl, -⟩ := hB.sort_of_load ld
        exact tmExact_copy_sort hB ld
      | .Const (ld12 := ld) (he106 := hr) (hm105 := hm) .. =>
        subst hr hm
        obtain ⟨a, us, rfl, -, -⟩ := hB.const_of_load ld
        exact tmExact_copy_const hB ld
      | .Lit (ld12 := ld) (he554 := hr) (hm553 := hm) .. =>
        subst hr hm
        rcases hB.toTm.lit_of_load ld with ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ <;>
          exact tmExact_copy_lit hB ld
      | .App (ld12 := ld) (he148 := hr) (hm147 := hm) (ev165 := e1) (ev201 := e2)
          (hc226 := hc) .. =>
        subst hc hr hm
        obtain ⟨Ef, Ea, rfl, hf, ha⟩ := hB.app_of_load ld
        have sf :=
          (ih _ _ _ _ _ _ rsubst_lt_calls e1 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.2.2.2.1
            rfl _ arg j rfl d Γ Ef A hf hA
        have sa :=
          (ih _ _ _ _ _ _ rsubst_lt_calls e2 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.2.2.2.1
            rfl _ arg j rfl d Γ Ea A (ha.mono e1.heap_extends) (hA.mono e1.heap_extends)
        exact tmExact_store_app (sf.mono e2.heap_extends) sa
      | .Lam (ld12 := ld) (he253 := hr) (hm252 := hm) (ev271 := e1) (op338 := op) (ev307 := e2)
          (hc347 := hc) .. =>
        subst hc hr hm; rw [SubstAux.add_ok op] at e2
        obtain ⟨T, Bo, ℓ, rfl, ht, hb, hl⟩ := hB.lam_of_load ld
        have st :=
          (ih _ _ _ _ _ _ rsubst_lt_calls e1 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.2.2.2.1
            rfl _ arg j rfl d Γ T A ht hA
        have sb :=
          (ih _ _ _ _ _ _ rsubst_lt_calls e2 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.2.2.2.1
            rfl _ arg (j + 1) rfl d Γ Bo A
            (by rw [SubstAux.val_succ32 hj0]; exact hb.mono e1.heap_extends)
            (hA.mono e1.heap_extends)
        rw [SubstAux.val_succ32 hj0] at sb
        exact tmExact_store_lam (st.mono e2.heap_extends) sb
          (hl.mono (e1.heap_extends.trans e2.heap_extends))
      | .Forall (ld12 := ld) (he374 := hr) (hm373 := hm) (ev392 := e1) (op459 := op) (ev428 := e2)
          (hc468 := hc) .. =>
        subst hc hr hm; rw [SubstAux.add_ok op] at e2
        obtain ⟨T, Bo, ℓ, rfl, ht, hb, hl⟩ := hB.forallE_of_load ld
        have st :=
          (ih _ _ _ _ _ _ rsubst_lt_calls e1 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.2.2.2.1
            rfl _ arg j rfl d Γ T A ht hA
        have sb :=
          (ih _ _ _ _ _ _ rsubst_lt_calls e2 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.2.2.2.1
            rfl _ arg (j + 1) rfl d Γ Bo A
            (by rw [SubstAux.val_succ32 hj0]; exact hb.mono e1.heap_extends)
            (hA.mono e1.heap_extends)
        rw [SubstAux.val_succ32 hj0] at sb
        exact tmExact_store_forallE (st.mono e2.heap_extends) sb
          (hl.mono (e1.heap_extends.trans e2.heap_extends))
      | .Let (ld12 := ld) (ev496 := e1) (hc537 := hc) .. =>
        subst hc
        obtain ⟨T, V, Bo, rfl, ht, hv, hb⟩ := hB.letE_of_load ld
        exact (ih _ _ _ _ _ _ rsubst_lt_calls e1 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.2.2.2.2.2.1
          rfl _ _ _ arg j rfl hj0 d Γ T V Bo A ht hv hb hA
      | .Proj (ld12 := ld) (he593 := hr) (hm592 := hm) (ev625 := e1) (hc650 := hc) .. =>
        subst hc hr hm
        obtain ⟨a, i, Es, rfl, rfl, ra, hes⟩ := hB.proj_of_load ld
        have : Resolved _ := ⟨hB.toTm.proj_key_ne⟩
        have : ProjPermitted _ _ := hB.toTm.proj_permitted ld ra
        exact tmExact_store_proj (Bytes.repAddressRef_heapMono₂ addrTy e1.heap_extends ra)
          ((ih _ _ _ _ _ _ rsubst_lt_calls e1 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.2.2.2.1
            rfl _ arg j rfl d Γ Es A hes hA)
    · -- expr_inst1_let
      intro hfn ty val body arg j hargs hj0 d Γ T V B A ht hv hb hA
      subst hfn hargs
      match Obs.«KernelSubst::expr_inst1_let».obs ev with
      | .run (he5 := hr) (hm4 := hm) (ev23 := e1) (ev59 := e2) (op126 := op) (ev95 := e3)
          (hc128 := hc) .. =>
        subst hc hr hm; rw [SubstAux.add_ok op] at e3
        have x1 :=
          (ih _ _ _ _ _ _ rsubst_lt_calls e1 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.2.2.2.1
            rfl _ arg j rfl d Γ T A ht hA
        have x2 :=
          (ih _ _ _ _ _ _ rsubst_lt_calls e2 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.2.2.2.1
            rfl _ arg j rfl d Γ V A (hv.mono e1.heap_extends) (hA.mono e1.heap_extends)
        have x3 :=
          (ih _ _ _ _ _ _ rsubst_lt_calls e3 (bounded_sub rsubst_sub_calls bd)).2.2.2.2.2.2.2.1
            rfl _ arg (j + 1) rfl d Γ B A
            (by rw [SubstAux.val_succ32 hj0, show ZMod.val j + 1 + 1 = ZMod.val j + 2 by omega]
                exact hb.mono (e1.heap_extends.trans e2.heap_extends))
            (hA.mono (e1.heap_extends.trans e2.heap_extends))
        rw [SubstAux.val_succ32 hj0] at x3
        rw [SubstAux.instShift_instantiate1 hA.toTm.looseBVarsBounded]
        exact tmExact_store_letE ((x1.mono e2.heap_extends).mono e3.heap_extends)
          (x2.mono e3.heap_extends) x3
    · -- expr_inst1_bvar
      intro hfn i arg j hargs d Γ B A hB hA
      subst hfn hargs
      obtain ⟨hsm, hcase⟩ := hB
      match Obs.«KernelSubst::expr_inst1_bvar».obs ev with
      | .n1 (ev15 := e1) (he40 := hr) (hm39 := hm) .. =>
        obtain ⟨i', j', hi', hj', -, -, hr', rfl⟩ := SubstAux.ltf e1
        injection hi' with hi'; injection hj' with hj'; subst hi' hj' hr hm
        have hlt := SubstAux.ltf_one hr'.symm
        rcases hcase with ⟨_, rfl⟩ | ⟨hk, _, _⟩
        · rw [SubstAux.inst1_bvar_lt hlt]; exact tmExact_store_bvarLocal hsm hlt
        · omega
      | .n0_n0 (ev15 := e1) (op74 := op) (ev86 := e2) (hc110 := hc) .. =>
        subst hc
        obtain ⟨i', j', hi', hj', -, hj32, hr', rfl⟩ := SubstAux.ltf e1
        injection hi' with hi'; injection hj' with hj'; subst hi' hj'
        have hij : i = j := by
          have := SubstAux.sub_ok op; injection this with h0; exact sub_eq_zero.mp h0.symm
        subst hij
        rcases hcase with ⟨_, rfl⟩ | ⟨hk, hd, _⟩
        · rw [SubstAux.inst1_bvar_self]
          have hlift := (ih _ _ _ _ _ _ rsubst_lt_calls e2 (bounded_sub rsubst_sub_calls bd)).1
            rfl arg i 0 rfl (by omega) (ZMod.val i) 0 (by omega) d Γ A
            (by rw [ZMod.val_zero]; exact hA)
          rw [ZMod.val_zero, Nat.zero_add] at hlift
          exact hlift
        · omega
      | .n0_other (ev15 := e1) (op74 := op) (hne111 := hne) (he119 := hr) (hm118 := hm)
          (op137 := op2) (hc139 := hc) .. =>
        subst hc hr hm
        obtain ⟨i', j', hi', hj', hi32, hj32, hr', rfl⟩ := SubstAux.ltf e1
        injection hi' with hi'; injection hj' with hj'; subst hi' hj'
        have hge := SubstAux.ltf_zero hr'.symm
        have hij : i ≠ j := fun hij => hne (by rw [SubstAux.sub_ok op, hij, sub_self])
        have hv : ZMod.val i ≠ ZMod.val j := fun hv => hij (ZMod.val_injective _ hv)
        rw [SubstAux.sub_ok op2]
        have hv1 : ZMod.val (i - 1) = ZMod.val i - 1 := by
          rw [SubstAux.val_sub (by rw [SubstAux.val_one]; omega), SubstAux.val_one]
        rcases hcase with ⟨hlt, _⟩ | ⟨hk, hd, rfl⟩
        · omega
        · exact tmExact_store_bvarFree_eq (by omega) (by omega) (by omega)
            (by rw [hv1]; unfold fvIdx; omega)

theorem expr_lift_exact {κ : _root_.Address → KKey} {e r : SourceValue F} {s c : F}
    {h h' : Heap F} {cs : List (Call F)} (bd : IxVM.Consistency.Bounded cs)
    (hs : ZMod.val s < 4611686018427387904) {s₁ s₂ : Nat} (hsum : ZMod.val s = s₁ + s₂)
    {d : Nat} {Γ : Nat → KExpr} {E : KExpr}
    (ev : ObsFn Obs.W "KernelSubst::expr_lift" [e, .field s, .field c] h r h' cs)
    (hE : TmExact κ d Γ h (ZMod.val c) E e) :
    TmExact κ (d + s₂) Γ h' (ZMod.val c + s₁) E r :=
  (subst_exact_bundle κ _ _ _ _ _ _ ev bd).1 rfl e s c rfl hs s₁ s₂ hsum d Γ E hE

theorem expr_lower_exact {κ : _root_.Address → KKey} {e r : SourceValue F} {s c : F}
    {h h' : Heap F} {cs : List (Call F)} (bd : IxVM.Consistency.Bounded cs)
    {s₁ s₂ : Nat} (hsum : ZMod.val s = s₁ + s₂) (hs₁ : s₁ ≤ ZMod.val c)
    {d : Nat} {Γ : Nat → KExpr} {E : KExpr} (hs₂ : s₂ ≤ d)
    (ev : ObsFn Obs.W "KernelSubst::expr_lower" [e, .field s, .field c] h r h' cs)
    (hE : TmExact κ d Γ h (ZMod.val c) E e)
    (hn : NoIdx h (ZMod.val c - s₁) (ZMod.val c + s₂) e) :
    TmExact κ (d - s₂) Γ h' (ZMod.val c - s₁) E r :=
  (subst_exact_bundle κ _ _ _ _ _ _ ev bd).2.2.2.2.1 rfl e s c rfl s₁ s₂ hsum hs₁ d Γ E hs₂ hE hn

theorem expr_inst1_exact {κ : _root_.Address → KKey} {e arg r : SourceValue F} {j : F}
    {h h' : Heap F} {cs : List (Call F)} (bd : IxVM.Consistency.Bounded cs)
    {d : Nat} {Γ : Nat → KExpr} {B A : KExpr}
    (ev : ObsFn Obs.W "KernelSubst::expr_inst1" [e, arg, .field j] h r h' cs)
    (hB : TmExact κ d Γ h (ZMod.val j + 1) B e) (hA : TmExact κ d Γ h 0 A arg) :
    TmExact κ d Γ h' (ZMod.val j) (B.instantiate1 A (ZMod.val j)) r :=
  (subst_exact_bundle κ _ _ _ _ _ _ ev bd).2.2.2.2.2.2.2.1 rfl e arg j rfl d Γ B A hB hA

/-! ## Dummy opening and closing for local depth (`TmOExact`) -/

/-- Every free variable in `e` has index `< d` (ignoring fvar types). -/
def fvarIdxLt (d : Nat) : KExpr → Bool
  | .fvar idx _ => decide (idx < d)
  | .app f a => fvarIdxLt d f && fvarIdxLt d a
  | .lam t b _ => fvarIdxLt d t && fvarIdxLt d b
  | .forallE t b _ => fvarIdxLt d t && fvarIdxLt d b
  | .letE t v b _ => fvarIdxLt d t && fvarIdxLt d v && fvarIdxLt d b
  | .proj _ _ e => fvarIdxLt d e
  | _ => true

private theorem lbb_instantiate1_fvar (d : Nat) (ty : KExpr) :
    ∀ (e : KExpr) (j : Nat),
      e.looseBVarsBounded (j + 1) = true →
      (e.instantiate1 (.fvar d ty) j).looseBVarsBounded j = true
  | .bvar i, j, hb => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.instantiate1]
    by_cases hij : i = j
    · simp [hij, Expr.looseBVarsBounded]
    · by_cases hgt : i > j
      · simp only [ite_eq_right hij, ite_eq_left hgt, Expr.looseBVarsBounded, decide_eq_true_eq]
        omega
      · simp only [ite_eq_right hij, ite_eq_right hgt, Expr.looseBVarsBounded, decide_eq_true_eq]
        omega
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, j, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.instantiate1, Expr.looseBVarsBounded,
      lbb_instantiate1_fvar d ty f j hb.1, lbb_instantiate1_fvar d ty a j hb.2]
  | .lam t b _, j, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.instantiate1, Expr.looseBVarsBounded,
      lbb_instantiate1_fvar d ty t j hb.1, lbb_instantiate1_fvar d ty b (j + 1) hb.2]
  | .forallE t b _, j, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.instantiate1, Expr.looseBVarsBounded,
      lbb_instantiate1_fvar d ty t j hb.1, lbb_instantiate1_fvar d ty b (j + 1) hb.2]
  | .letE t v b _, j, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.instantiate1, Expr.looseBVarsBounded,
      lbb_instantiate1_fvar d ty t j hb.1.1, lbb_instantiate1_fvar d ty v j hb.1.2,
      lbb_instantiate1_fvar d ty b (j + 1) hb.2]
  | .proj _ _ e, j, hb => by
    simp only [Expr.looseBVarsBounded] at hb
    simpa [Expr.instantiate1, Expr.looseBVarsBounded] using lbb_instantiate1_fvar d ty e j hb

private theorem fvarIdxLt_liftLooseBVars (d : Nat) :
    ∀ (e : KExpr) (n c : Nat), fvarIdxLt d (e.liftLooseBVars n c) = fvarIdxLt d e
  | .bvar _, n, c => by simp only [Expr.liftLooseBVars]; split <;> rfl
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, n, c => by
    simp [Expr.liftLooseBVars, fvarIdxLt,
      fvarIdxLt_liftLooseBVars d f n c, fvarIdxLt_liftLooseBVars d a n c]
  | .lam t b _, n, c => by
    simp [Expr.liftLooseBVars, fvarIdxLt,
      fvarIdxLt_liftLooseBVars d t n c, fvarIdxLt_liftLooseBVars d b n (c + 1)]
  | .forallE t b _, n, c => by
    simp [Expr.liftLooseBVars, fvarIdxLt,
      fvarIdxLt_liftLooseBVars d t n c, fvarIdxLt_liftLooseBVars d b n (c + 1)]
  | .letE t v b _, n, c => by
    simp [Expr.liftLooseBVars, fvarIdxLt,
      fvarIdxLt_liftLooseBVars d t n c, fvarIdxLt_liftLooseBVars d v n c,
      fvarIdxLt_liftLooseBVars d b n (c + 1)]
  | .proj _ _ e, n, c => by
    simpa [Expr.liftLooseBVars, fvarIdxLt] using fvarIdxLt_liftLooseBVars d e n c

private theorem fvarIdxLt_instantiate1Lift {d : Nat} {v : KExpr} (hv : fvarIdxLt d v = true) :
    ∀ (e : KExpr) (j : Nat), fvarIdxLt d e = true → fvarIdxLt d (e.instantiate1Lift v j) = true
  | .bvar i, j, _ => by
    simp only [Expr.instantiate1Lift]
    split
    · rw [fvarIdxLt_liftLooseBVars]; exact hv
    · split <;> rfl
  | .fvar _ _, _, h => h
  | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, j, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, fvarIdxLt, Bool.and_eq_true]
    exact ⟨fvarIdxLt_instantiate1Lift hv f j h.1, fvarIdxLt_instantiate1Lift hv a j h.2⟩
  | .lam t b _, j, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, fvarIdxLt, Bool.and_eq_true]
    exact ⟨fvarIdxLt_instantiate1Lift hv t j h.1, fvarIdxLt_instantiate1Lift hv b (j + 1) h.2⟩
  | .forallE t b _, j, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, fvarIdxLt, Bool.and_eq_true]
    exact ⟨fvarIdxLt_instantiate1Lift hv t j h.1, fvarIdxLt_instantiate1Lift hv b (j + 1) h.2⟩
  | .letE t w b _, j, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, fvarIdxLt, Bool.and_eq_true]
    exact ⟨⟨fvarIdxLt_instantiate1Lift hv t j h.1.1, fvarIdxLt_instantiate1Lift hv w j h.1.2⟩,
      fvarIdxLt_instantiate1Lift hv b (j + 1) h.2⟩
  | .proj _ _ e, j, h => by
    simp only [fvarIdxLt] at h
    simpa [Expr.instantiate1Lift, fvarIdxLt] using fvarIdxLt_instantiate1Lift hv e j h

theorem tmExact_fvarIdxLt {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F} (rep : TmExact κ d Γ h k E p) :
    fvarIdxLt d E = true := by
  induction rep with
  | bvarLocal _ _ _ | sort _ _ | const _ _ _ | litNat _ _ _ | litStr _ _ _ => rfl
  | @bvarFree k₁ _ i _ _ hk hd =>
    simp only [fvarIdxLt, decide_eq_true_eq]; unfold fvIdx; omega
  | app _ _ _ ihf iha => simp [fvarIdxLt, ihf, iha]
  | lam _ _ _ _ iht ihb => simp [fvarIdxLt, iht, ihb]
  | forallE _ _ _ _ iht ihb => simp [fvarIdxLt, iht, ihb]
  | letE _ _ _ _ _ ihv ihb => exact fvarIdxLt_instantiate1Lift ihv _ 0 ihb
  | proj _ _ _ ihe => simpa [fvarIdxLt] using ihe

theorem abstract1_instantiate1_cancel {d : Nat} (ty : KExpr) :
    ∀ {e : KExpr} (k : Nat),
      fvarIdxLt d e = true → e.looseBVarsBounded (k + 1) = true →
      (e.instantiate1 (.fvar d ty) k).abstract1 d k = e
  | .bvar i, k, _, hb => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.instantiate1]
    by_cases hik : i = k
    · subst hik; simp [Expr.abstract1]
    · rw [ite_eq_right hik, ite_eq_right (by omega)]; rfl
  | .fvar idx fty, k, hf, _ => by
    simp only [fvarIdxLt, decide_eq_true_eq] at hf
    simp [Expr.instantiate1, Expr.abstract1, Nat.ne_of_lt hf]
  | .sort _, _, _, _ | .const _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .app f a, k, hf, hb => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp [Expr.instantiate1, Expr.abstract1,
      abstract1_instantiate1_cancel ty k hf.1 hb.1,
      abstract1_instantiate1_cancel ty k hf.2 hb.2]
  | .lam t b _, k, hf, hb => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp [Expr.instantiate1, Expr.abstract1,
      abstract1_instantiate1_cancel ty k hf.1 hb.1,
      abstract1_instantiate1_cancel ty (k + 1) hf.2 hb.2]
  | .forallE t b _, k, hf, hb => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp [Expr.instantiate1, Expr.abstract1,
      abstract1_instantiate1_cancel ty k hf.1 hb.1,
      abstract1_instantiate1_cancel ty (k + 1) hf.2 hb.2]
  | .letE t v b _, k, hf, hb => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp [Expr.instantiate1, Expr.abstract1,
      abstract1_instantiate1_cancel ty k hf.1.1 hb.1.1,
      abstract1_instantiate1_cancel ty k hf.1.2 hb.1.2,
      abstract1_instantiate1_cancel ty (k + 1) hf.2 hb.2]
  | .proj _ _ e, k, hf, hb => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded] at hf hb
    simpa [Expr.instantiate1, Expr.abstract1] using abstract1_instantiate1_cancel ty k hf hb

private def openDummies : Nat → Nat → Nat → KExpr → KExpr
  | 0, _, _, e => e
  | m + 1, d, c, e => openDummies m (d + 1) c (e.instantiate1 (.fvar d (.sort .zero)) (c + m))

private def closeDummies : Nat → Nat → Nat → KExpr → KExpr
  | 0, _, _, e => e
  | m + 1, d, c', e => (closeDummies m (d + 1) c' e).abstract1 d (c' + m)

private theorem tmExact_openDummies {κ : _root_.Address → KKey} {h : Heap F} :
    ∀ (m d c : Nat) {E : KExpr} {p : SourceValue F},
      TmExact κ d (fun _ => .sort .zero) h (c + m) E p →
      TmExact κ (d + m) (fun _ => .sort .zero) h c (openDummies m d c E) p
  | 0, d, c, _, _, rep => by simpa [openDummies] using rep
  | m + 1, d, c, E, p, rep => by
    have hop := tmExact_open (Γ' := fun _ => .sort .zero) (T := .sort .zero)
      rfl (fun _ _ => rfl) rep (c + m) (by omega)
    have ih := tmExact_openDummies m (d + 1) c hop
    rwa [show d + 1 + m = d + (m + 1) by omega] at ih

private theorem tmExact_closeDummies {κ : _root_.Address → KKey} {h : Heap F} :
    ∀ (m d c' : Nat) {E : KExpr} {p : SourceValue F},
      TmExact κ (d + m) (fun _ => .sort .zero) h c' E p →
      TmExact κ d (fun _ => .sort .zero) h (c' + m) (closeDummies m d c' E) p
  | 0, d, c', _, _, rep => by simpa [closeDummies] using rep
  | m + 1, d, c', E, p, rep => by
    rw [show d + (m + 1) = (d + 1) + m by omega] at rep
    have ih := tmExact_closeDummies m (d + 1) c' rep
    have hcl := tmExact_close (Γ' := fun _ => .sort .zero) (fun _ _ => rfl) ih
    simpa [closeDummies, Nat.add_assoc] using hcl

private theorem liftLooseBVars_of_bounded (shift : Nat) :
    ∀ {e : KExpr} (c : Nat),
      e.looseBVarsBounded c = true → e.liftLooseBVars shift c = e
  | .bvar i, c, hb => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.liftLooseBVars, ite_eq_right (show ¬ c ≤ i by omega)]
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, c, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.liftLooseBVars, liftLooseBVars_of_bounded shift c hb.1,
      liftLooseBVars_of_bounded shift c hb.2]
  | .lam t b _, c, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.liftLooseBVars, liftLooseBVars_of_bounded shift c hb.1,
      liftLooseBVars_of_bounded shift (c + 1) hb.2]
  | .forallE t b _, c, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.liftLooseBVars, liftLooseBVars_of_bounded shift c hb.1,
      liftLooseBVars_of_bounded shift (c + 1) hb.2]
  | .letE t v b _, c, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.liftLooseBVars, liftLooseBVars_of_bounded shift c hb.1.1,
      liftLooseBVars_of_bounded shift c hb.1.2, liftLooseBVars_of_bounded shift (c + 1) hb.2]
  | .proj _ _ e, c, hb => by
    simp only [Expr.looseBVarsBounded] at hb
    simpa [Expr.liftLooseBVars] using liftLooseBVars_of_bounded shift c hb

private theorem fvarIdxLt_mono {d₁ d₂ : Nat} (hle : d₁ ≤ d₂) :
    ∀ {e : KExpr}, fvarIdxLt d₁ e = true → fvarIdxLt d₂ e = true
  | .fvar idx _, h => by simp only [fvarIdxLt, decide_eq_true_eq] at h ⊢; omega
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h ⊢
    exact ⟨fvarIdxLt_mono hle h.1, fvarIdxLt_mono hle h.2⟩
  | .lam t b _, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h ⊢
    exact ⟨fvarIdxLt_mono hle h.1, fvarIdxLt_mono hle h.2⟩
  | .forallE t b _, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h ⊢
    exact ⟨fvarIdxLt_mono hle h.1, fvarIdxLt_mono hle h.2⟩
  | .letE t v b _, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h ⊢
    exact ⟨⟨fvarIdxLt_mono hle h.1.1, fvarIdxLt_mono hle h.1.2⟩, fvarIdxLt_mono hle h.2⟩
  | .proj _ _ e, h => by simp only [fvarIdxLt] at h ⊢; exact fvarIdxLt_mono hle h

private theorem fvarIdxLt_instantiate1_fvar {d : Nat} :
    ∀ {e : KExpr} (j : Nat), fvarIdxLt d e = true →
      fvarIdxLt (d + 1) (e.instantiate1 (.fvar d (.sort .zero)) j) = true
  | .bvar i, j, _ => by
    simp only [Expr.instantiate1]
    split
    · simp [fvarIdxLt]
    · split <;> rfl
  | .fvar idx ty, _, h => fvarIdxLt_mono (Nat.le_succ d) h
  | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, j, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp [Expr.instantiate1, fvarIdxLt,
      fvarIdxLt_instantiate1_fvar j h.1, fvarIdxLt_instantiate1_fvar j h.2]
  | .lam t b _, j, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp [Expr.instantiate1, fvarIdxLt,
      fvarIdxLt_instantiate1_fvar j h.1, fvarIdxLt_instantiate1_fvar (j + 1) h.2]
  | .forallE t b _, j, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp [Expr.instantiate1, fvarIdxLt,
      fvarIdxLt_instantiate1_fvar j h.1, fvarIdxLt_instantiate1_fvar (j + 1) h.2]
  | .letE t v b _, j, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp [Expr.instantiate1, fvarIdxLt,
      fvarIdxLt_instantiate1_fvar j h.1.1, fvarIdxLt_instantiate1_fvar j h.1.2,
      fvarIdxLt_instantiate1_fvar (j + 1) h.2]
  | .proj _ _ e, j, h => by
    simp only [fvarIdxLt] at h
    simpa [Expr.instantiate1, fvarIdxLt] using fvarIdxLt_instantiate1_fvar j h

private theorem abstract1_lift_instantiate1_step (d shift : Nat) :
    ∀ {e : KExpr} (c m : Nat),
      fvarIdxLt d e = true → e.looseBVarsBounded (c + m + 1) = true →
      ((e.instantiate1 (.fvar d (.sort .zero)) (c + m)).liftLooseBVars shift c).abstract1 d
        (c + shift + m) = e.liftLooseBVars shift c
  | .bvar i, c, m, _, hb => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.instantiate1]
    by_cases him : i = c + m
    · subst him
      simp [Expr.instantiate1, Expr.liftLooseBVars, Expr.abstract1, show c + m ≥ c by omega]; omega
    · rw [ite_eq_right him, ite_eq_right (by omega)]
      by_cases hic : i ≥ c <;> simp [Expr.liftLooseBVars, Expr.abstract1, hic]
  | .fvar idx ty, c, m, hf, _ => by
    simp only [fvarIdxLt, decide_eq_true_eq] at hf
    simp [Expr.instantiate1, Expr.liftLooseBVars, Expr.abstract1, Nat.ne_of_lt hf]
  | .sort _, _, _, _, _ | .const _ _, _, _, _, _ | .lit _, _, _, _, _ => rfl
  | .app f a, c, m, hf, hb => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp [Expr.instantiate1, Expr.liftLooseBVars, Expr.abstract1,
      abstract1_lift_instantiate1_step d shift c m hf.1 hb.1,
      abstract1_lift_instantiate1_step d shift c m hf.2 hb.2]
  | .lam t b _, c, m, hf, hb => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp only [Expr.instantiate1, Expr.liftLooseBVars, Expr.abstract1]
    rw [abstract1_lift_instantiate1_step d shift c m hf.1 hb.1]
    have hb' : b.looseBVarsBounded ((c + 1) + m + 1) = true := by
      rw [show (c + 1) + m + 1 = c + m + 1 + 1 by omega]; exact hb.2
    have step_b := abstract1_lift_instantiate1_step d shift (c + 1) m hf.2 hb'
    rw [show c + 1 + m = c + m + 1 by omega,
      show c + 1 + shift + m = c + shift + m + 1 by omega] at step_b
    rw [step_b]
  | .forallE t b _, c, m, hf, hb => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp only [Expr.instantiate1, Expr.liftLooseBVars, Expr.abstract1]
    rw [abstract1_lift_instantiate1_step d shift c m hf.1 hb.1]
    have hb' : b.looseBVarsBounded ((c + 1) + m + 1) = true := by
      rw [show (c + 1) + m + 1 = c + m + 1 + 1 by omega]; exact hb.2
    have step_b := abstract1_lift_instantiate1_step d shift (c + 1) m hf.2 hb'
    rw [show c + 1 + m = c + m + 1 by omega,
      show c + 1 + shift + m = c + shift + m + 1 by omega] at step_b
    rw [step_b]
  | .letE t v b _, c, m, hf, hb => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp only [Expr.instantiate1, Expr.liftLooseBVars, Expr.abstract1]
    rw [abstract1_lift_instantiate1_step d shift c m hf.1.1 hb.1.1,
      abstract1_lift_instantiate1_step d shift c m hf.1.2 hb.1.2]
    have hb' : b.looseBVarsBounded ((c + 1) + m + 1) = true := by
      rw [show (c + 1) + m + 1 = c + m + 1 + 1 by omega]; exact hb.2
    have step_b := abstract1_lift_instantiate1_step d shift (c + 1) m hf.2 hb'
    rw [show c + 1 + m = c + m + 1 by omega,
      show c + 1 + shift + m = c + shift + m + 1 by omega] at step_b
    rw [step_b]
  | .proj _ _ e, c, m, hf, hb => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded] at hf hb
    simpa [Expr.instantiate1, Expr.liftLooseBVars, Expr.abstract1] using
      abstract1_lift_instantiate1_step d shift c m hf hb

private theorem closeDummies_openDummies (shift : Nat) :
    ∀ (m d c : Nat) {e : KExpr},
      fvarIdxLt d e = true → e.looseBVarsBounded (c + m) = true →
      closeDummies m d (c + shift) (openDummies m d c e) = e.liftLooseBVars shift c
  | 0, d, c, e, _, hb => by
    simp only [openDummies, closeDummies, Nat.add_zero] at hb ⊢
    exact (liftLooseBVars_of_bounded shift c hb).symm
  | m + 1, d, c, e, hf, hb => by
    simp only [openDummies, closeDummies]
    have hf' := fvarIdxLt_instantiate1_fvar (c + m) hf
    have hb' := lbb_instantiate1_fvar d (.sort .zero) e (c + m)
      (by rwa [show c + m + 1 = c + (m + 1) by omega])
    rw [closeDummies_openDummies shift m (d + 1) c hf' hb']
    exact abstract1_lift_instantiate1_step d shift c m hf
      (by rwa [show c + m + 1 = c + (m + 1) by omega])

/-- **`KernelSubst::expr_lift(pe, shift, cut)`** on `TmExact` at `d = 0` and local depth `k ≥ cut`
produces `E.liftLooseBVars shift cut` at local depth `k + shift`. -/
theorem expr_lift_local_exact {κ : _root_.Address → KKey} {Γ₀ : Nat → KExpr}
    {k shift cut : Nat} {E : KExpr} {pe r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hcut_le : cut ≤ k) (hshift_lt : shift < 4611686018427387904)
    (hcut_lt : cut < 4611686018427387904)
    (hbnd : IxVM.Consistency.Bounded cs) (hE : TmExact κ 0 Γ₀ h k E pe)
    (ev : ObsFn Obs.W "KernelSubst::expr_lift" [pe, .field (shift : F), .field (cut : F)] h r h'
      cs) :
    TmExact κ 0 Γ₀ h' (k + shift) (E.liftLooseBVars shift cut) r := by
  let m := k - cut
  have hk_eq : k = cut + m := by omega
  have hE₀ : TmExact κ 0 (fun _ => .sort .zero) h (cut + m) E pe := by
    rw [← hk_eq]; exact tmExact_congr_ghost (fun _ hj => by omega) hE
  have hop : TmExact κ m (fun _ => .sort .zero) h cut (openDummies m 0 cut E) pe := by
    simpa using tmExact_openDummies m 0 cut hE₀
  have hval_s : ZMod.val (shift : F) = shift :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hshift_lt (by decide))
  have hval_c : ZMod.val (cut : F) = cut :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hcut_lt (by decide))
  have hlift := expr_lift_exact hbnd (by rw [hval_s]; exact hshift_lt) (s₁ := shift) (s₂ := 0)
    (by rw [hval_s]; omega) ev (by rwa [hval_c])
  rw [hval_c, Nat.add_zero] at hlift
  have hcl : TmExact κ 0 (fun _ => .sort .zero) h' (cut + shift + m)
      (closeDummies m 0 (cut + shift) (openDummies m 0 cut E)) r :=
    tmExact_closeDummies m 0 (cut + shift) (by simpa using hlift)
  rw [closeDummies_openDummies shift m 0 cut (tmExact_fvarIdxLt hE₀) hE₀.toTm.looseBVarsBounded,
    show cut + shift + m = k + shift by omega] at hcl
  exact tmExact_congr_ghost (fun _ hj => by omega) hcl

/-- **`KernelSubst::expr_lift(e, shift, cut)`** on `TmOExact` is `liftLooseBVars shift cut`. -/
theorem expr_lift_tmOExact {κ : _root_.Address → KKey} {E : KExpr} {pe r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} {shift cut : Nat}
    (hshift : shift < 4611686018427387904) (hcut : cut < 4611686018427387904)
    (hbnd : IxVM.Consistency.Bounded cs) (hE : TmOExact κ h E pe)
    (ev : ObsFn Obs.W "KernelSubst::expr_lift" [pe, .field (shift : F), .field (cut : F)] h r h'
      cs) :
    TmOExact κ h' (E.liftLooseBVars shift cut) r := by
  obtain ⟨k, hk⟩ := hE
  exact ⟨_, expr_lift_local_exact (Nat.le_max_right k cut) hshift hcut hbnd
    (tmExact_depth_le hk (max k cut) (Nat.le_max_left _ _)) ev⟩

/-! ## `expr_inst1` at local depth -/

private theorem closeDummies_inst1_openDummies :
    ∀ (m d : Nat) {B A : KExpr}, fvarIdxLt d B = true → fvarIdxLt d A = true →
      B.looseBVarsBounded (1 + m) = true → A.looseBVarsBounded m = true →
      closeDummies m d 0 ((openDummies m d 1 B).instantiate1 (openDummies m d 0 A) 0) =
        B.instantiate1Lift A 0
  | 0, d, B, A, _, _, _, hA => by
    simp only [openDummies, closeDummies]
    exact (Expr.instantiate1Lift_eq_instantiate1 hA B 0).symm
  | m + 1, d, B, A, hfB, hfA, hbB, hbA => by
    have hB1 : B.looseBVarsBounded (1 + m + 1) = true := by
      rwa [show 1 + m + 1 = 1 + (m + 1) by omega]
    have ih := closeDummies_inst1_openDummies m (d + 1)
      (fvarIdxLt_instantiate1_fvar (1 + m) hfB) (fvarIdxLt_instantiate1_fvar m hfA)
      (lbb_instantiate1_fvar d (.sort .zero) B (1 + m) hB1)
      (lbb_instantiate1_fvar d (.sort .zero) A m hbA)
    simp only [openDummies, closeDummies, Nat.zero_add]
    rw [ih]
    have hc := instantiate1Lift_abstract1 (A.instantiate1 (.fvar d (.sort .zero)) m) d m
      (B.instantiate1 (.fvar d (.sort .zero)) (1 + m)) 0
    simp only [Nat.add_zero] at hc
    rw [hc, show m + 1 = 1 + m by omega,
      abstract1_instantiate1_cancel (d := d) (.sort .zero) (1 + m) hfB hB1,
      abstract1_instantiate1_cancel (d := d) (.sort .zero) m hfA hbA]

/-- **`KernelSubst::expr_inst1(body, arg, 0)`** on `TmExact` at `d = 0` is `instantiate1Lift`. -/
theorem expr_inst1_local_exact {κ : _root_.Address → KKey} {m : Nat} {B A : KExpr}
    {pb pa r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hbnd : IxVM.Consistency.Bounded cs)
    (hB : TmExact κ 0 ghost0 h (m + 1) B pb) (hA : TmExact κ 0 ghost0 h m A pa)
    (ev : ObsFn Obs.W "KernelSubst::expr_inst1" [pb, pa, .field 0] h r h' cs) :
    TmExact κ 0 ghost0 h' m (B.instantiate1Lift A 0) r := by
  have hB' : TmExact κ 0 (fun _ => .sort .zero) h (1 + m) B pb := by rw [Nat.add_comm]; exact hB
  have hA' : TmExact κ 0 (fun _ => .sort .zero) h (0 + m) A pa := by rw [Nat.zero_add]; exact hA
  have hopB : TmExact κ m (fun _ => .sort .zero) h 1 (openDummies m 0 1 B) pb := by
    simpa using tmExact_openDummies m 0 1 hB'
  have hopA : TmExact κ m (fun _ => .sort .zero) h 0 (openDummies m 0 0 A) pa := by
    simpa using tmExact_openDummies m 0 0 hA'
  have hinst := expr_inst1_exact hbnd ev (by simpa using hopB) hopA
  simp only [ZMod.val_zero] at hinst
  have hcl : TmExact κ 0 (fun _ => .sort .zero) h' (0 + m)
      (closeDummies m 0 0 ((openDummies m 0 1 B).instantiate1 (openDummies m 0 0 A) 0)) r :=
    tmExact_closeDummies m 0 0 (by simpa using hinst)
  rw [Nat.zero_add, closeDummies_inst1_openDummies m 0 (tmExact_fvarIdxLt hB) (tmExact_fvarIdxLt hA)
    (by rw [Nat.add_comm]; exact hB.toTm.looseBVarsBounded) hA.toTm.looseBVarsBounded] at hcl
  exact hcl

/-- **`KernelSubst::expr_inst1(body, arg, 0)`** on `TmOExact` is `instantiate1Lift` at `0`. -/
theorem expr_inst1_tmOExact {κ : _root_.Address → KKey} {B A : KExpr} {pb pa r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hbnd : IxVM.Consistency.Bounded cs)
    (hB : TmOExact κ h B pb) (hA : TmOExact κ h A pa)
    (ev : ObsFn Obs.W "KernelSubst::expr_inst1" [pb, pa, .field 0] h r h' cs) :
    TmOExact κ h' (B.instantiate1Lift A 0) r := by
  obtain ⟨kB, rB⟩ := hB
  obtain ⟨kA, rA⟩ := hA
  exact ⟨_, expr_inst1_local_exact hbnd (tmExact_depth_le rB (max kB kA + 1) (by omega))
    (tmExact_depth_le rA (max kB kA) (Nat.le_max_right _ _)) ev⟩

/-! ## `has_bvar_in_range` and `expr_lower` at local depth -/

private theorem hasBVarIn_liftLooseBVars_false {lo hi : Nat} :
    ∀ {v : KExpr} (d k : Nat), hasBVarIn (lo + k) (hi + k) v = false →
      hasBVarIn (lo + d + k) (hi + d + k) (v.liftLooseBVars d k) = false
  | .bvar i, d, k, hv => by
    simp only [hasBVarIn, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hv
    simp only [Expr.liftLooseBVars]
    split <;> simp only [hasBVarIn, Bool.and_eq_false_iff, decide_eq_false_iff_not] <;> omega
  | .fvar _ _, _, _, _ | .sort _, _, _, _ | .const _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .app f a, d, k, hv => by
    simp only [hasBVarIn, Bool.or_eq_false_iff] at hv
    simp only [Expr.liftLooseBVars, hasBVarIn, Bool.or_eq_false_iff]
    exact ⟨hasBVarIn_liftLooseBVars_false d k hv.1, hasBVarIn_liftLooseBVars_false d k hv.2⟩
  | .lam t b _, d, k, hv => by
    simp only [hasBVarIn, Bool.or_eq_false_iff] at hv
    have hb := hasBVarIn_liftLooseBVars_false (lo := lo) (hi := hi) d (k + 1)
      (by rw [show lo + (k + 1) = lo + k + 1 by omega, show hi + (k + 1) = hi + k + 1 by omega]
          exact hv.2)
    rw [show lo + d + (k + 1) = lo + d + k + 1 by omega,
      show hi + d + (k + 1) = hi + d + k + 1 by omega] at hb
    simp only [Expr.liftLooseBVars, hasBVarIn, Bool.or_eq_false_iff]
    exact ⟨hasBVarIn_liftLooseBVars_false d k hv.1, hb⟩
  | .forallE t b _, d, k, hv => by
    simp only [hasBVarIn, Bool.or_eq_false_iff] at hv
    have hb := hasBVarIn_liftLooseBVars_false (lo := lo) (hi := hi) d (k + 1)
      (by rw [show lo + (k + 1) = lo + k + 1 by omega, show hi + (k + 1) = hi + k + 1 by omega]
          exact hv.2)
    rw [show lo + d + (k + 1) = lo + d + k + 1 by omega,
      show hi + d + (k + 1) = hi + d + k + 1 by omega] at hb
    simp only [Expr.liftLooseBVars, hasBVarIn, Bool.or_eq_false_iff]
    exact ⟨hasBVarIn_liftLooseBVars_false d k hv.1, hb⟩
  | .letE t w b _, d, k, hv => by
    simp only [hasBVarIn, Bool.or_eq_false_iff] at hv
    have hb := hasBVarIn_liftLooseBVars_false (lo := lo) (hi := hi) d (k + 1)
      (by rw [show lo + (k + 1) = lo + k + 1 by omega, show hi + (k + 1) = hi + k + 1 by omega]
          exact hv.2)
    rw [show lo + d + (k + 1) = lo + d + k + 1 by omega,
      show hi + d + (k + 1) = hi + d + k + 1 by omega] at hb
    simp only [Expr.liftLooseBVars, hasBVarIn, Bool.or_eq_false_iff]
    exact ⟨⟨hasBVarIn_liftLooseBVars_false d k hv.1.1,
      hasBVarIn_liftLooseBVars_false d k hv.1.2⟩, hb⟩
  | .proj _ _ e, d, k, hv => by
    simp only [hasBVarIn] at hv
    simp only [Expr.liftLooseBVars, hasBVarIn]
    exact hasBVarIn_liftLooseBVars_false d k hv

private theorem hasBVarIn_instantiate1Lift_false {lo hi : Nat} {v : KExpr}
    (hv : hasBVarIn lo hi v = false) :
    ∀ {b : KExpr} (d : Nat), hasBVarIn (lo + d + 1) (hi + d + 1) b = false →
      hasBVarIn (lo + d) (hi + d) (b.instantiate1Lift v d) = false
  | .bvar i, d, hb => by
    simp only [hasBVarIn, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hb
    simp only [Expr.instantiate1Lift]
    by_cases hid : i = d
    · subst hid
      rw [ite_eq_left rfl]
      simpa using hasBVarIn_liftLooseBVars_false (lo := lo) (hi := hi) i 0 (by simpa using hv)
    · rw [ite_eq_right hid]
      by_cases hgt : i > d
      · rw [ite_eq_left hgt]
        simp only [hasBVarIn, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      · rw [ite_eq_right hgt]
        simp only [hasBVarIn, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, d, hb => by
    simp only [hasBVarIn, Bool.or_eq_false_iff] at hb
    simp only [Expr.instantiate1Lift, hasBVarIn, Bool.or_eq_false_iff]
    exact ⟨hasBVarIn_instantiate1Lift_false hv d hb.1, hasBVarIn_instantiate1Lift_false hv d hb.2⟩
  | .lam t b _, d, hb => by
    simp only [hasBVarIn, Bool.or_eq_false_iff] at hb
    have hb' := hasBVarIn_instantiate1Lift_false hv (d + 1)
      (by rw [show lo + (d + 1) + 1 = lo + d + 1 + 1 by omega,
              show hi + (d + 1) + 1 = hi + d + 1 + 1 by omega]; exact hb.2)
    rw [show lo + (d + 1) = lo + d + 1 by omega, show hi + (d + 1) = hi + d + 1 by omega] at hb'
    simp only [Expr.instantiate1Lift, hasBVarIn, Bool.or_eq_false_iff]
    exact ⟨hasBVarIn_instantiate1Lift_false hv d hb.1, hb'⟩
  | .forallE t b _, d, hb => by
    simp only [hasBVarIn, Bool.or_eq_false_iff] at hb
    have hb' := hasBVarIn_instantiate1Lift_false hv (d + 1)
      (by rw [show lo + (d + 1) + 1 = lo + d + 1 + 1 by omega,
              show hi + (d + 1) + 1 = hi + d + 1 + 1 by omega]; exact hb.2)
    rw [show lo + (d + 1) = lo + d + 1 by omega, show hi + (d + 1) = hi + d + 1 by omega] at hb'
    simp only [Expr.instantiate1Lift, hasBVarIn, Bool.or_eq_false_iff]
    exact ⟨hasBVarIn_instantiate1Lift_false hv d hb.1, hb'⟩
  | .letE t w b _, d, hb => by
    simp only [hasBVarIn, Bool.or_eq_false_iff] at hb
    have hb' := hasBVarIn_instantiate1Lift_false hv (d + 1)
      (by rw [show lo + (d + 1) + 1 = lo + d + 1 + 1 by omega,
              show hi + (d + 1) + 1 = hi + d + 1 + 1 by omega]; exact hb.2)
    rw [show lo + (d + 1) = lo + d + 1 by omega, show hi + (d + 1) = hi + d + 1 by omega] at hb'
    simp only [Expr.instantiate1Lift, hasBVarIn, Bool.or_eq_false_iff]
    exact ⟨⟨hasBVarIn_instantiate1Lift_false hv d hb.1.1,
      hasBVarIn_instantiate1Lift_false hv d hb.1.2⟩, hb'⟩
  | .proj _ _ e, d, hb => by
    simp only [hasBVarIn] at hb
    simp only [Expr.instantiate1Lift, hasBVarIn]
    exact hasBVarIn_instantiate1Lift_false hv d hb

/-- `NoIdx h lo hi e` on a closed-opening `TmExact κ 0 Γ h k E e` certifies
`hasBVarIn lo hi E = false`. -/
theorem hasBVarIn_false_of_noIdx_tmExact {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {h : Heap F} :
    ∀ {k lo hi m : Nat} {E : KExpr} {e : SourceValue F},
      TmExact κ 0 Γ h k E e →
      IdxAll h (fun n i => ZMod.val i < lo + n ∨ hi + n ≤ ZMod.val i) m e →
      hasBVarIn (lo + m) (hi + m) E = false := by
  intro k lo hi m E e rep
  induction rep generalizing m with
  | @bvarLocal _ addr i cell hs hi' =>
    intro hn
    obtain ⟨i', hx, hw⟩ := SubstAux.idxAll_bvar_inv hn (loadValue_enum_cell cell)
    injection hx with hx; subst hx
    simp only [hasBVarIn, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
  | bvarFree _ _ _ hd => exact nomatch hd
  | sort _ _ | const _ _ _ | litNat _ _ _ | litStr _ _ _ => intro _; rfl
  | app cell _ _ ihf iha =>
    intro hn
    obtain ⟨nf, na⟩ := SubstAux.idxAll_app_inv hn (loadValue_enum_cell cell)
    simp only [hasBVarIn, Bool.or_eq_false_iff]; exact ⟨ihf nf, iha na⟩
  | lam cell _ _ _ iht ihb =>
    intro hn
    obtain ⟨nt, nb⟩ := SubstAux.idxAll_lam_inv hn (loadValue_enum_cell cell)
    have hb := ihb (m := m + 1) nb
    rw [show lo + (m + 1) = lo + m + 1 by omega, show hi + (m + 1) = hi + m + 1 by omega] at hb
    simp only [hasBVarIn, Bool.or_eq_false_iff]; exact ⟨iht nt, hb⟩
  | forallE cell _ _ _ iht ihb =>
    intro hn
    obtain ⟨nt, nb⟩ := SubstAux.idxAll_forallE_inv hn (loadValue_enum_cell cell)
    have hb := ihb (m := m + 1) nb
    rw [show lo + (m + 1) = lo + m + 1 by omega, show hi + (m + 1) = hi + m + 1 by omega] at hb
    simp only [hasBVarIn, Bool.or_eq_false_iff]; exact ⟨iht nt, hb⟩
  | letE cell _ _ _ _ ihv ihb =>
    intro hn
    obtain ⟨_, nv, nb⟩ := SubstAux.idxAll_letE_inv hn (loadValue_enum_cell cell)
    have hb := ihb (m := m + 1) nb
    rw [show lo + (m + 1) = lo + m + 1 by omega, show hi + (m + 1) = hi + m + 1 by omega] at hb
    simpa using hasBVarIn_instantiate1Lift_false (ihv nv) 0 (by simpa using hb)
  | proj cell _ _ ihe =>
    intro hn; exact ihe (SubstAux.idxAll_proj_inv hn (loadValue_enum_cell cell))

/-- **`KernelSubst::has_bvar_in_range(pe, lo, hi)` returning `0`** on `TmOExact` gives
`NoIdx h lo hi pe` and `hasBVarIn lo hi E = false`, with no heap allocation. -/
theorem has_bvar_in_range_zero_tmOExact {κ : _root_.Address → KKey} {E : KExpr}
    {pe : SourceValue F} {lo hi : Nat} {h h' : Heap F} {cs : List (Call F)}
    (hlo : lo < 4611686018427387904) (hhi : hi < 4611686018427387904)
    (hbnd : IxVM.Consistency.Bounded cs) (hE : TmOExact κ h E pe)
    (ev : ObsFn Obs.W "KernelSubst::has_bvar_in_range"
      [pe, .field (lo : F), .field (hi : F)] h (.field 0) h' cs) :
    h' = h ∧ NoIdx h lo hi pe ∧ hasBVarIn lo hi E = false := by
  obtain ⟨k, rE⟩ := hE
  obtain ⟨hh, -, hnF⟩ := SubstAux.gall κ .has_bvar_in_range _ _ _ _ _ ev pe (lo : F) (hi : F)
    rfl hbnd
  have hval_lo : ZMod.val (lo : F) = lo :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hlo (by decide))
  have hval_hi : ZMod.val (hi : F) = hi :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hhi (by decide))
  have hnf := hnF rfl 0 ghost0 k E rE.toTm
  rw [hval_lo, hval_hi] at hnf
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  have hn : NoIdx h lo hi pe := SubstAux.noIdx_of_noIdxF_tm rE.toTm (by omega) hnf
  have hhb : hasBVarIn lo hi E = false := by
    simpa using hasBVarIn_false_of_noIdx_tmExact (lo := lo) (hi := hi) (m := 0) rE hn
  exact ⟨hh, hn, hhb⟩

private theorem lbb_of_hasBVarIn_false {c shift : Nat} :
    ∀ {e : KExpr}, e.looseBVarsBounded (c + shift) = true → hasBVarIn c (c + shift) e = false →
      e.looseBVarsBounded c = true
  | .bvar i, hb, hh => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb ⊢
    simp only [hasBVarIn, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hh
    omega
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, hb, hh => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    simp only [hasBVarIn, Bool.or_eq_false_iff] at hh
    exact ⟨lbb_of_hasBVarIn_false hb.1 hh.1, lbb_of_hasBVarIn_false hb.2 hh.2⟩
  | .lam t b _, hb, hh => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    simp only [hasBVarIn, Bool.or_eq_false_iff] at hh
    have hb2 : b.looseBVarsBounded ((c + 1) + shift) = true := by
      rw [show (c + 1) + shift = c + shift + 1 by omega]; exact hb.2
    have hh2 : hasBVarIn (c + 1) ((c + 1) + shift) b = false := by
      rw [show (c + 1) + shift = c + shift + 1 by omega]; exact hh.2
    exact ⟨lbb_of_hasBVarIn_false hb.1 hh.1, lbb_of_hasBVarIn_false hb2 hh2⟩
  | .forallE t b _, hb, hh => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    simp only [hasBVarIn, Bool.or_eq_false_iff] at hh
    have hb2 : b.looseBVarsBounded ((c + 1) + shift) = true := by
      rw [show (c + 1) + shift = c + shift + 1 by omega]; exact hb.2
    have hh2 : hasBVarIn (c + 1) ((c + 1) + shift) b = false := by
      rw [show (c + 1) + shift = c + shift + 1 by omega]; exact hh.2
    exact ⟨lbb_of_hasBVarIn_false hb.1 hh.1, lbb_of_hasBVarIn_false hb2 hh2⟩
  | .letE t v b _, hb, hh => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    simp only [hasBVarIn, Bool.or_eq_false_iff] at hh
    have hb2 : b.looseBVarsBounded ((c + 1) + shift) = true := by
      rw [show (c + 1) + shift = c + shift + 1 by omega]; exact hb.2
    have hh2 : hasBVarIn (c + 1) ((c + 1) + shift) b = false := by
      rw [show (c + 1) + shift = c + shift + 1 by omega]; exact hh.2
    exact ⟨⟨lbb_of_hasBVarIn_false hb.1.1 hh.1.1, lbb_of_hasBVarIn_false hb.1.2 hh.1.2⟩,
      lbb_of_hasBVarIn_false hb2 hh2⟩
  | .proj _ _ e, hb, hh => by
    simp only [Expr.looseBVarsBounded] at hb ⊢
    simp only [hasBVarIn] at hh
    exact lbb_of_hasBVarIn_false hb hh

private theorem hasBVarIn_instantiate1_fvar_above (d c shift : Nat) :
    ∀ {e : KExpr} (j : Nat), c + shift ≤ j →
      hasBVarIn c (c + shift) e = false →
      hasBVarIn c (c + shift) (e.instantiate1 (.fvar d (.sort .zero)) j) = false
  | .bvar i, j, hj, hh => by
    simp only [hasBVarIn, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hh
    simp only [Expr.instantiate1]
    split
    · rfl
    · split <;> simp only [hasBVarIn, Bool.and_eq_false_iff, decide_eq_false_iff_not] <;> omega
  | .fvar _ _, _, _, _ | .sort _, _, _, _ | .const _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .app f a, j, hj, hh => by
    simp only [hasBVarIn, Bool.or_eq_false_iff] at hh
    simp only [Expr.instantiate1, hasBVarIn, Bool.or_eq_false_iff]
    exact ⟨hasBVarIn_instantiate1_fvar_above d c shift j hj hh.1,
      hasBVarIn_instantiate1_fvar_above d c shift j hj hh.2⟩
  | .lam t b _, j, hj, hh => by
    simp only [hasBVarIn, Bool.or_eq_false_iff] at hh
    have hb := hasBVarIn_instantiate1_fvar_above d (c + 1) shift (j + 1) (by omega)
      (by rw [show c + 1 + shift = c + shift + 1 by omega]; exact hh.2)
    rw [show c + 1 + shift = c + shift + 1 by omega] at hb
    simp only [Expr.instantiate1, hasBVarIn, Bool.or_eq_false_iff]
    exact ⟨hasBVarIn_instantiate1_fvar_above d c shift j hj hh.1, hb⟩
  | .forallE t b _, j, hj, hh => by
    simp only [hasBVarIn, Bool.or_eq_false_iff] at hh
    have hb := hasBVarIn_instantiate1_fvar_above d (c + 1) shift (j + 1) (by omega)
      (by rw [show c + 1 + shift = c + shift + 1 by omega]; exact hh.2)
    rw [show c + 1 + shift = c + shift + 1 by omega] at hb
    simp only [Expr.instantiate1, hasBVarIn, Bool.or_eq_false_iff]
    exact ⟨hasBVarIn_instantiate1_fvar_above d c shift j hj hh.1, hb⟩
  | .letE t v b _, j, hj, hh => by
    simp only [hasBVarIn, Bool.or_eq_false_iff] at hh
    have hb := hasBVarIn_instantiate1_fvar_above d (c + 1) shift (j + 1) (by omega)
      (by rw [show c + 1 + shift = c + shift + 1 by omega]; exact hh.2)
    rw [show c + 1 + shift = c + shift + 1 by omega] at hb
    simp only [Expr.instantiate1, hasBVarIn, Bool.or_eq_false_iff]
    exact ⟨⟨hasBVarIn_instantiate1_fvar_above d c shift j hj hh.1.1,
      hasBVarIn_instantiate1_fvar_above d c shift j hj hh.1.2⟩, hb⟩
  | .proj _ _ e, j, hj, hh => by
    simp only [hasBVarIn] at hh
    simp only [Expr.instantiate1, hasBVarIn]
    exact hasBVarIn_instantiate1_fvar_above d c shift j hj hh

private theorem openDummies_of_bounded :
    ∀ (k d c : Nat) {e : KExpr}, e.looseBVarsBounded c = true → openDummies k d c e = e
  | 0, _, _, _, _ => rfl
  | k + 1, d, c, e, hb => by
    simp only [openDummies]
    rw [Expr.instantiate1_eq_self (SubstAux.lbb_mono (by omega) hb)]
    exact openDummies_of_bounded k (d + 1) c hb

private theorem lowerBVars_of_bounded (shift : Nat) :
    ∀ {e : KExpr} (c : Nat), e.looseBVarsBounded c = true → e.lowerBVars shift c = e
  | .bvar i, c, hb => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.lowerBVars, ite_eq_right (show ¬ c + shift ≤ i by omega)]
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, c, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.lowerBVars, lowerBVars_of_bounded shift c hb.1, lowerBVars_of_bounded shift c hb.2]
  | .lam t b _, c, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.lowerBVars, lowerBVars_of_bounded shift c hb.1,
      lowerBVars_of_bounded shift (c + 1) hb.2]
  | .forallE t b _, c, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.lowerBVars, lowerBVars_of_bounded shift c hb.1,
      lowerBVars_of_bounded shift (c + 1) hb.2]
  | .letE t v b _, c, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.lowerBVars, lowerBVars_of_bounded shift c hb.1.1,
      lowerBVars_of_bounded shift c hb.1.2, lowerBVars_of_bounded shift (c + 1) hb.2]
  | .proj _ _ e, c, hb => by
    simp only [Expr.looseBVarsBounded] at hb
    simpa [Expr.lowerBVars] using lowerBVars_of_bounded shift c hb

private theorem abstract1_lower_instantiate1_step (d shift : Nat) :
    ∀ {e : KExpr} (c m : Nat),
      fvarIdxLt d e = true → e.looseBVarsBounded (c + shift + m + 1) = true →
      hasBVarIn c (c + shift) e = false →
      ((e.instantiate1 (.fvar d (.sort .zero)) (c + shift + m)).lowerBVars shift c).abstract1 d
        (c + m) = e.lowerBVars shift c
  | .bvar i, c, m, _, hb, hh => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [hasBVarIn, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hh
    simp only [Expr.instantiate1]
    by_cases him : i = c + shift + m
    · subst him
      simp [Expr.lowerBVars, Expr.abstract1, show c + shift + m ≥ c + shift by omega]; omega
    · rw [ite_eq_right him, ite_eq_right (by omega)]
      by_cases hic : i ≥ c + shift
      · simp [Expr.lowerBVars, Expr.abstract1, hic]
      · simp [Expr.lowerBVars, Expr.abstract1, hic]
  | .fvar idx ty, c, m, hf, _, _ => by
    simp only [fvarIdxLt, decide_eq_true_eq] at hf
    simp [Expr.instantiate1, Expr.lowerBVars, Expr.abstract1, Nat.ne_of_lt hf]
  | .sort _, _, _, _, _, _ | .const _ _, _, _, _, _, _ | .lit _, _, _, _, _, _ => rfl
  | .app f a, c, m, hf, hb, hh => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp only [hasBVarIn, Bool.or_eq_false_iff] at hh
    simp [Expr.instantiate1, Expr.lowerBVars, Expr.abstract1,
      abstract1_lower_instantiate1_step d shift c m hf.1 hb.1 hh.1,
      abstract1_lower_instantiate1_step d shift c m hf.2 hb.2 hh.2]
  | .lam t b _, c, m, hf, hb, hh => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp only [hasBVarIn, Bool.or_eq_false_iff] at hh
    simp only [Expr.instantiate1, Expr.lowerBVars, Expr.abstract1]
    rw [abstract1_lower_instantiate1_step d shift c m hf.1 hb.1 hh.1]
    have hb' : b.looseBVarsBounded ((c + 1) + shift + m + 1) = true := by
      rw [show (c + 1) + shift + m + 1 = c + shift + m + 1 + 1 by omega]; exact hb.2
    have hh' : hasBVarIn (c + 1) ((c + 1) + shift) b = false := by
      rw [show (c + 1) + shift = c + shift + 1 by omega]; exact hh.2
    have step_b := abstract1_lower_instantiate1_step d shift (c + 1) m hf.2 hb' hh'
    rw [show c + 1 + shift + m = c + shift + m + 1 by omega,
      show c + 1 + m = c + m + 1 by omega] at step_b
    rw [step_b]
  | .forallE t b _, c, m, hf, hb, hh => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp only [hasBVarIn, Bool.or_eq_false_iff] at hh
    simp only [Expr.instantiate1, Expr.lowerBVars, Expr.abstract1]
    rw [abstract1_lower_instantiate1_step d shift c m hf.1 hb.1 hh.1]
    have hb' : b.looseBVarsBounded ((c + 1) + shift + m + 1) = true := by
      rw [show (c + 1) + shift + m + 1 = c + shift + m + 1 + 1 by omega]; exact hb.2
    have hh' : hasBVarIn (c + 1) ((c + 1) + shift) b = false := by
      rw [show (c + 1) + shift = c + shift + 1 by omega]; exact hh.2
    have step_b := abstract1_lower_instantiate1_step d shift (c + 1) m hf.2 hb' hh'
    rw [show c + 1 + shift + m = c + shift + m + 1 by omega,
      show c + 1 + m = c + m + 1 by omega] at step_b
    rw [step_b]
  | .letE t v b _, c, m, hf, hb, hh => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp only [hasBVarIn, Bool.or_eq_false_iff] at hh
    simp only [Expr.instantiate1, Expr.lowerBVars, Expr.abstract1]
    rw [abstract1_lower_instantiate1_step d shift c m hf.1.1 hb.1.1 hh.1.1,
      abstract1_lower_instantiate1_step d shift c m hf.1.2 hb.1.2 hh.1.2]
    have hb' : b.looseBVarsBounded ((c + 1) + shift + m + 1) = true := by
      rw [show (c + 1) + shift + m + 1 = c + shift + m + 1 + 1 by omega]; exact hb.2
    have hh' : hasBVarIn (c + 1) ((c + 1) + shift) b = false := by
      rw [show (c + 1) + shift = c + shift + 1 by omega]; exact hh.2
    have step_b := abstract1_lower_instantiate1_step d shift (c + 1) m hf.2 hb' hh'
    rw [show c + 1 + shift + m = c + shift + m + 1 by omega,
      show c + 1 + m = c + m + 1 by omega] at step_b
    rw [step_b]
  | .proj _ _ e, c, m, hf, hb, hh => by
    simp only [fvarIdxLt, Expr.looseBVarsBounded] at hf hb
    simp only [hasBVarIn] at hh
    simpa [Expr.instantiate1, Expr.lowerBVars, Expr.abstract1] using
      abstract1_lower_instantiate1_step d shift c m hf hb hh

private theorem closeDummies_lower_openDummies (shift : Nat) :
    ∀ (m d c : Nat) {e : KExpr},
      fvarIdxLt d e = true → e.looseBVarsBounded (c + shift + m) = true →
      hasBVarIn c (c + shift) e = false →
      closeDummies m d c (openDummies (shift + m) d c e) = e.lowerBVars shift c
  | 0, d, c, e, _, hb, hh => by
    simp only [Nat.add_zero, closeDummies] at hb ⊢
    have hbc := lbb_of_hasBVarIn_false hb hh
    rw [openDummies_of_bounded shift d c hbc, lowerBVars_of_bounded shift c hbc]
  | m + 1, d, c, e, hf, hb, hh => by
    have hadd : shift + (m + 1) = (shift + m) + 1 := by omega
    rw [hadd]
    simp only [openDummies, closeDummies]
    have h1 : c + (shift + m) = c + shift + m := by omega
    rw [h1]
    have hf' := fvarIdxLt_instantiate1_fvar (c + shift + m) hf
    have hb' := lbb_instantiate1_fvar d (.sort .zero) e (c + shift + m)
      (by rwa [show c + shift + m + 1 = c + shift + (m + 1) by omega])
    have hh' := hasBVarIn_instantiate1_fvar_above d c shift (c + shift + m) (by omega) hh
    rw [closeDummies_lower_openDummies shift m (d + 1) c hf' hb' hh']
    exact abstract1_lower_instantiate1_step d shift c m hf
      (by rwa [show c + shift + m + 1 = c + shift + (m + 1) by omega]) hh

/-- **`KernelSubst::expr_lower(pe, shift, cut)`** on `TmExact` at `d = 0` and local depth
`k ≥ cut + shift` with `NoIdx h cut (cut + shift) pe` produces `E.lowerBVars shift cut`. -/
theorem expr_lower_local_exact {κ : _root_.Address → KKey} {Γ₀ : Nat → KExpr}
    {k shift cut : Nat} {E : KExpr} {pe r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hcut_le : cut + shift ≤ k) (hshift_lt : shift < 4611686018427387904)
    (hcut_lt : cut < 4294967296) (hbnd : IxVM.Consistency.Bounded cs)
    (hE : TmExact κ 0 Γ₀ h k E pe) (hn : NoIdx h cut (cut + shift) pe)
    (ev : ObsFn Obs.W "KernelSubst::expr_lower" [pe, .field (shift : F), .field (cut : F)] h r h'
      cs) :
    TmExact κ 0 Γ₀ h' (k - shift) (E.lowerBVars shift cut) r := by
  let m := k - (cut + shift)
  have hk_eq : k = cut + (shift + m) := by omega
  have hE₀ : TmExact κ 0 (fun _ => .sort .zero) h (cut + (shift + m)) E pe := by
    rw [← hk_eq]; exact tmExact_congr_ghost (fun _ hj => by omega) hE
  have hop : TmExact κ (shift + m) (fun _ => .sort .zero) h cut
      (openDummies (shift + m) 0 cut E) pe := by
    simpa using tmExact_openDummies (shift + m) 0 cut hE₀
  have hval_s : ZMod.val (shift : F) = shift :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hshift_lt (by decide))
  have hval_c : ZMod.val (cut : F) = cut :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hcut_lt (by decide))
  have hlow := expr_lower_exact (d := shift + m) (Γ := fun _ => .sort .zero) hbnd
    (s₁ := 0) (s₂ := shift) (by rw [hval_s]; omega) (Nat.zero_le _) (by omega) ev
    (by rwa [hval_c]) (by rw [hval_c, Nat.sub_zero]; exact hn)
  rw [hval_c, Nat.sub_zero, show shift + m - shift = m by omega] at hlow
  have hcl : TmExact κ 0 (fun _ => .sort .zero) h' (cut + m)
      (closeDummies m 0 cut (openDummies (shift + m) 0 cut E)) r :=
    tmExact_closeDummies m 0 cut (by simpa using hlow)
  have hhb : hasBVarIn cut (cut + shift) E = false := by
    simpa using hasBVarIn_false_of_noIdx_tmExact (lo := cut) (hi := cut + shift) (m := 0) hE₀ hn
  rw [closeDummies_lower_openDummies shift m 0 cut (tmExact_fvarIdxLt hE₀)
      (by rw [show cut + shift + m = cut + (shift + m) by omega]; exact hE₀.toTm.looseBVarsBounded)
      hhb,
    show cut + m = k - shift by omega] at hcl
  exact tmExact_congr_ghost (fun _ hj => by omega) hcl

/-- **`KernelSubst::expr_lower(pe, shift, cut)`** on `TmOExact` with `NoIdx h cut (cut + shift) pe`
is `E.lowerBVars shift cut`. -/
theorem expr_lower_tmOExact {κ : _root_.Address → KKey} {E : KExpr} {pe r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} {shift cut : Nat}
    (hshift : shift < 4611686018427387904) (hcut : cut < 4294967296)
    (hbnd : IxVM.Consistency.Bounded cs) (hE : TmOExact κ h E pe)
    (hn : NoIdx h cut (cut + shift) pe)
    (ev : ObsFn Obs.W "KernelSubst::expr_lower" [pe, .field (shift : F), .field (cut : F)] h r h'
      cs) :
    TmOExact κ h' (E.lowerBVars shift cut) r := by
  obtain ⟨k, hk⟩ := hE
  exact ⟨_, expr_lower_local_exact (Nat.le_max_right k (cut + shift)) hshift hcut hbnd
    (tmExact_depth_le hk (max k (cut + shift)) (Nat.le_max_left _ _)) hn ev⟩

end IxVM.Refinement.Binding.FamilyRecon
