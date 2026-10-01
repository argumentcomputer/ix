module

public import ConLeche.Semantics.BasisType
public import ConLeche.Semantics.Interp

@[expose] public section

/-!
# `bval_mem_type` — every built-in inhabits its annotated type

*(Re-based to `ConLeche/SetBase/*` at THE SEPARATION's S2, task #161: the
module already imported nothing but base, and the graded lane needs it.
Path and module name changed; namespaces, statements and proofs
verbatim.)*


Step 2's second entry item, and the skeleton's `const` row's remaining
supplier: `ConLeche/Term/Semantics/ConstOk.lean`'s capstone ported onto
`piR`/`lamR` and `BConst.typeAV`.

## The port pattern

Each case is three moves, and the first two are mechanical:

1. `show` the value at its own tower (`bval` is a `match`, so this is
   definitional);
2. `simp only` with `BConst.typeAV`, the smart constructors it mentions,
   and the `interp` clause equations — this reduces
   `interp ρ (typeAV c us)` to the tower's *own space*, which is the
   whole point of having read the numeral convention off `Value.lean`
   rather than choosing one;
3. apply the tower's membership argument — `lamR_mem` down the
   binders, then the constant's own semantic fact.

Where v1 needed a universe side condition (`app_mem`'s codomain
premise, `pi_mem_univ`'s levels) the port needs none: `lamR_mem` has no
premise beyond the fibres and `app_mem_piR_pos` none at all.  Where v1
needed `pt_mem_piC_iff` because the collapse made a value `pt`, the
port often does not: `Empty.rec` is a *graph* here
(`emptyRecV = lamR v … (lamR v ∅ …)`), so its case is two `lamR_mem`s
over a vacuous domain rather than a proof-point argument.

## The `Nat.succ` wrinkle, inherited verbatim

`typeAV`'s step premise mentions `Nat.succ`'s *value*
(`natSuccAV (.bvar 1)` interprets to `app (natSuccV V) n`) while
`natStepSpace` is written with the operator `natsucc`.  They agree on
`ω`, which is what the outer product quantifies over — v1's
`natStepSpace_eq`, restated here as `natStepSpace_eq`.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.Term (BConst lv)

universe w

variable (V : Type w) [SetTheory V]

/-! ## `Nat` -/

theorem bval_mem_nat (us : List Nat) (ρ : Nat → V) :
    bval V .nat us ∈ˢ interp V ρ (BConst.typeAV .nat us) := by
  show (omega : V) ∈ˢ _
  simp only [BConst.typeAV, interp_sort]
  exact omega_mem_univ_succ 0

theorem bval_mem_natZero (us : List Nat) (ρ : Nat → V) :
    bval V .natZero us ∈ˢ interp V ρ (BConst.typeAV .natZero us) := by
  show natzero ∈ˢ _
  simp only [BConst.typeAV, natTyAV, interp_const, bval]
  exact natzero_mem

theorem bval_mem_natSucc (us : List Nat) (ρ : Nat → V) :
    bval V .natSucc us ∈ˢ interp V ρ (BConst.typeAV .natSucc us) := by
  show natSuccV V ∈ˢ _
  simp only [BConst.typeAV, arrowA, natTyAV, interp_pi, interp_const,
    AnnotTerm.liftN, bval]
  exact natSuccV_mem V

/-- The step space as `interp` produces it (with `Nat.succ`'s *value*
applied) is the one the tower is written with (`natsucc`): they agree
on `ω`.  v1's `natStepSpace_eq`. -/
theorem natStepSpace_eq {u : Nat} (M : V) :
    (piR u (omega : V) fun n =>
        piR u (app M n) fun _ => app M (app (natSuccV V) n))
      = natStepSpace V u M :=
  piR_congr fun n hn => by rw [natSuccV_app V hn]

/-- `Nat.rec`'s type, as `interp` produces it. -/
theorem interp_type_natRec (us : List Nat) (ρ : Nat → V) :
    interp V ρ (BConst.typeAV .natRec us) =
      piR (lv us 0) (natMotiveSpace V (lv us 0)) fun M =>
        piR (lv us 0) (app M natzero) fun _ =>
          piR (lv us 0) (natStepSpace V (lv us 0) M) fun _ =>
            piR (lv us 0) omega fun n => app M n := by
  simp only [BConst.typeAV, arrowA, natTyAV, natZeroAV, natSuccAV,
    interp_pi, interp_const, interp_app, interp_bvar, interp_sort,
    AnnotTerm.liftN, cons_zero, cons_succ, bval, natMotiveSpace]
  refine piR_congr fun M _ => piR_congr fun z _ => ?_
  rw [natStepSpace_eq]

theorem bval_mem_natRec (us : List Nat) (ρ : Nat → V) :
    bval V .natRec us ∈ˢ interp V ρ (BConst.typeAV .natRec us) := by
  rw [interp_type_natRec]
  show natRecV V (lv us 0) ∈ˢ _
  refine lamR_mem fun M hM => lamR_mem fun z hz =>
    lamR_mem fun s hs => ?_
  refine lamR_mem fun n hn => ?_
  exact natRecV_mem_fibre V hM hz hs hn

/-! ## `PUnit` -/

theorem bval_mem_punit (us : List Nat) (ρ : Nat → V) :
    bval V .punit us ∈ˢ interp V ρ (BConst.typeAV .punit us) := by
  show (unitSet : V) ∈ˢ _
  simp only [BConst.typeAV, interp_sort]
  exact unitSet_mem_univ _

theorem bval_mem_punitUnit (us : List Nat) (ρ : Nat → V) :
    bval V .punitUnit us
      ∈ˢ interp V ρ (BConst.typeAV .punitUnit us) := by
  show (pt : V) ∈ˢ _
  simp only [BConst.typeAV, punitAV, interp_const, bval]
  exact pt_mem_unitSet

theorem bval_mem_punitRec (us : List Nat) (ρ : Nat → V) :
    bval V .punitRec us
      ∈ˢ interp V ρ (BConst.typeAV .punitRec us) := by
  show punitRecV V (lv us 1) ∈ˢ _
  simp only [BConst.typeAV, arrowA, punitAV, punitUnitAV, interp_pi,
    interp_const, interp_app, interp_bvar, interp_sort,
    AnnotTerm.liftN, cons_zero, cons_succ, bval]
  refine lamR_mem fun M hM => lamR_mem fun m hm =>
    lamR_mem fun t ht => ?_
  rw [mem_unitSet ht]
  exact hm

/-! ## `Empty` -/

theorem bval_mem_empty (us : List Nat) (ρ : Nat → V) :
    bval V .empty us ∈ˢ interp V ρ (BConst.typeAV .empty us) := by
  show (empty : V) ∈ˢ _
  simp only [BConst.typeAV, interp_sort]
  exact empty_mem_univ _

theorem bval_mem_emptyRec (us : List Nat) (ρ : Nat → V) :
    bval V .emptyRec us
      ∈ˢ interp V ρ (BConst.typeAV .emptyRec us) := by
  show emptyRecV V (lv us 1) ∈ˢ _
  simp only [BConst.typeAV, arrowA, emptyAV, interp_pi, interp_const,
    interp_app, interp_bvar, interp_sort, AnnotTerm.liftN, cons_zero,
    cons_succ, bval]
  refine lamR_mem fun M _ => lamR_mem fun t ht => ?_
  exact absurd ht (not_mem_empty t)

/-! ## `PSigma'` -/

theorem bval_mem_psigma (us : List Nat) (ρ : Nat → V) :
    bval V .psigma us ∈ˢ interp V ρ (BConst.typeAV .psigma us) := by
  show psigmaV V (lv us 0) (lv us 1) ∈ˢ _
  simp only [BConst.typeAV, arrowA, interp_pi, interp_bvar,
    interp_sort, AnnotTerm.liftN, cons_zero, psigmaV,
    psigmaFibreSpace]
  exact lamR_mem fun A hA => lamR_mem fun B hB =>
    sigma_mem_univ hA fun x hx =>
      app_mem_piR_pos (Nat.succ_ne_zero _) hB hx

/-- **`PSigma'.mk`** — the case the port pattern does not reach.  v1's
four pointwise `lamC_mem`s work because `psigmaMkV`'s *body* carries an
explicit `if max u v = 0 then pt` tag; `psigmaMkV` dropped it (the
annotation squashes the tower instead), so the innermost pointwise
obligation would be `spair a b ∈ˢ sigmaSet 0 A B'` — **false**, since a
kind-`0` `sigmaSet` is a truth value and `spair a b ≠ pt`.  The kind-`0`
argument therefore moves from the leaf to the root: split first, then
exhibit the tower's *inhabitation* with `pt_mem_piR_zero`. -/
theorem bval_mem_psigmaMk (us : List Nat) (ρ : Nat → V) :
    bval V .psigmaMk us
      ∈ˢ interp V ρ (BConst.typeAV .psigmaMk us) := by
  show psigmaMkV V (lv us 0) (lv us 1) ∈ˢ _
  simp only [BConst.typeAV, arrowA, psigmaAV, interp_pi, interp_bvar,
    interp_sort, interp_app, interp_const, AnnotTerm.liftN,
    AnnotTerm.mkAppN, cons_zero, cons_succ, bval, lv,
    List.getD_cons_zero, List.getD_cons_succ]
  by_cases hw : Nat.max (us.getD 0 0) (us.getD 1 0) = 0
  · -- the whole tower is the canonical proof; exhibit inhabitation
    rw [psigmaMkV, hw, lamR_zero]
    refine pt_mem_piR_zero fun A hA => ⟨pt, pt_mem_piR_zero
      fun B hB => ⟨pt, pt_mem_piR_zero fun a ha => ⟨pt,
        pt_mem_piR_zero fun b hb => ⟨pt, ?_⟩⟩⟩⟩
    rw [psigmaV_app V hA hB, hw]
    exact pt_mem_sigma ha hb
  · refine lamR_mem fun A hA => lamR_mem fun B hB =>
      lamR_mem fun a ha => lamR_mem fun b hb => ?_
    rw [psigmaV_app V hA hB]
    exact spair_mem hw ha hb

/-! ## `Quot` -/

theorem bval_mem_quot (us : List Nat) (ρ : Nat → V) :
    bval V .quot us ∈ˢ interp V ρ (BConst.typeAV .quot us) := by
  show quotV V (lv us 0) ∈ˢ _
  simp only [BConst.typeAV, relAV, interp_pi, interp_bvar,
    interp_sort, AnnotTerm.liftN, cons_zero, quotV, relSpace]
  exact lamR_mem fun A hA => lamR_mem fun R _ => quotSet_mem_univ hA

theorem bval_mem_quotMk (us : List Nat) (ρ : Nat → V) :
    bval V .quotMk us ∈ˢ interp V ρ (BConst.typeAV .quotMk us) := by
  show quotMkV V (lv us 0) ∈ˢ _
  simp only [BConst.typeAV, relAV, quotAV, interp_pi, interp_bvar,
    interp_sort, interp_app, interp_const, AnnotTerm.liftN,
    AnnotTerm.mkAppN, cons_zero, cons_succ, quotMkV, relSpace, bval,
    lv, List.getD_cons_zero]
  refine lamR_mem fun A hA => lamR_mem fun R hR =>
    lamR_mem fun a ha => ?_
  rw [quotV_app V hA hR]
  exact quotClass_mem ha

/-- **`Quot.lift`** — six binders, five of them `lamR_mem`, and the
tail is `quotLiftR_mem`.  Its kind-`0` fibre premise comes from the
third binder (`B ∈ˢ univ v`, and `univ 0 = univZero`), so nothing new
is needed. -/
theorem bval_mem_quotLift (us : List Nat) (ρ : Nat → V) :
    bval V .quotLift us
      ∈ˢ interp V ρ (BConst.typeAV .quotLift us) := by
  show quotLiftV V (lv us 0) (lv us 1) ∈ˢ _
  simp only [BConst.typeAV, relAV, quotAV, interp_pi, interp_bvar,
    interp_sort, interp_app, interp_const, interp_eqE,
    AnnotTerm.liftN, AnnotTerm.mkAppN, cons_zero, cons_succ, quotLiftV,
    relSpace, quotInvSpace, bval, lv, List.getD_cons_zero]
  refine lamR_mem fun A hA => lamR_mem fun R hR =>
    lamR_mem fun B hB => lamR_mem fun f hf =>
      lamR_mem fun h hh => ?_
  rw [quotV_app V hA hR]
  exact quotLiftR_mem V hf fun h0 => by
    rw [← univ_zero]; exact h0 ▸ hB

/-! ## The `pt`-valued propositions

`Quot.ind`, `Quot.sound` and `propext` have `bval = pt`, so their
cases are *inhabitation* arguments rather than typings: every binder is
`piR 0`, and `pt_mem_piR_zero_of` replaces the collapse lane's
`pt_mem_piC_iff.mpr` line for line. -/

theorem bval_mem_quotInd (us : List Nat) (ρ : Nat → V) :
    bval V .quotInd us ∈ˢ interp V ρ (BConst.typeAV .quotInd us) := by
  show (pt : V) ∈ˢ _
  simp only [BConst.typeAV, relAV, quotAV, quotMkAV, interp_pi,
    interp_bvar, interp_sort, interp_app, interp_const,
    AnnotTerm.liftN, AnnotTerm.mkAppN, cons_zero, cons_succ,
    bval, lv, List.getD_cons_zero]
  refine pt_mem_piR_zero_of fun A hA => ?_
  refine pt_mem_piR_zero_of fun R hR => ?_
  refine pt_mem_piR_zero_of fun M hM => ?_
  refine pt_mem_piR_zero_of fun mi hmi => ?_
  refine pt_mem_piR_zero_of fun q hq => ?_
  have hMq : app M q ∈ˢ (univ 0 : V) :=
    app_mem_piR_pos Nat.one_ne_zero hM hq
  rw [quotV_app V hA hR] at hq
  obtain ⟨a, ha, rfl⟩ := quotClass_surj hq
  have h1 := app_mem_piR hmi ha fun _ x hx => by
      rw [quotMkV_app V hA hR hx, ← univ_zero]
      exact app_mem_piR_pos Nat.one_ne_zero hM
        (by rw [quotV_app V hA hR]; exact quotClass_mem hx)
  rw [quotMkV_app V hA hR ha] at h1
  exact mem_univ_zero hMq h1 ▸ h1

theorem bval_mem_quotSound (us : List Nat) (ρ : Nat → V) :
    bval V .quotSound us
      ∈ˢ interp V ρ (BConst.typeAV .quotSound us) := by
  show (pt : V) ∈ˢ _
  simp only [BConst.typeAV, relAV, quotMkAV, interp_pi,
    interp_bvar, interp_sort, interp_app, interp_const,
    interp_eqE, AnnotTerm.liftN, AnnotTerm.mkAppN, cons_zero, cons_succ,
    bval, lv, List.getD_cons_zero]
  refine pt_mem_piR_zero_of fun A hA => ?_
  refine pt_mem_piR_zero_of fun R hR => ?_
  refine pt_mem_piR_zero_of fun a ha => ?_
  refine pt_mem_piR_zero_of fun b hb => ?_
  refine pt_mem_piR_zero_of fun _wv hwv => ?_
  rw [quotMkV_app V hA hR ha, quotMkV_app V hA hR hb,
    SetTheory.quotSound ha hb hwv]
  exact pt_mem_eqv_self _

theorem bval_mem_propext (us : List Nat) (ρ : Nat → V) :
    bval V .propext us ∈ˢ interp V ρ (BConst.typeAV .propext us) := by
  show (pt : V) ∈ˢ _
  simp only [BConst.typeAV, interp_pi, interp_bvar, interp_sort,
    interp_eqE, cons_zero, cons_succ]
  refine pt_mem_piR_zero_of fun A hA => ?_
  refine pt_mem_piR_zero_of fun B hB => ?_
  refine pt_mem_piR_zero_of fun f hf => ?_
  refine pt_mem_piR_zero_of fun g hg => ?_
  have hAB : A = B := by
    refine prop_ext hA hB (fun hp => ?_) (fun hp => ?_)
    · have h1 : app f pt ∈ˢ B :=
        app_mem_piR hf hp fun _ _ _ => by rw [← univ_zero]; exact hB
      exact mem_univ_zero hB h1 ▸ h1
    · have h1 : app g pt ∈ˢ A :=
        app_mem_piR hg hp fun _ _ _ => by rw [← univ_zero]; exact hA
      exact mem_univ_zero hA h1 ▸ h1
  rw [hAB]
  exact pt_mem_eqv_self _

/-! ## `Classical.choice` -/

theorem bval_mem_choice (us : List Nat) (ρ : Nat → V) :
    bval V .choice us ∈ˢ interp V ρ (BConst.typeAV .choice us) := by
  show choiceV V (lv us 0) ∈ˢ _
  simp only [BConst.typeAV, negTyAV, arrowA, emptyAV, interp_pi,
    interp_bvar, interp_sort, interp_const, AnnotTerm.liftN, cons_zero,
    cons_succ, choiceV, dnegSpace, bval]
  refine lamR_mem fun A hA => lamR_mem fun h hh => ?_
  obtain ⟨x, hx⟩ := exists_mem_of_dneg V hh
  exact schoice_mem hx

/-! ## `lfpFam` (task #188) -/

theorem bval_mem_lfpFam (us : List Nat) (ρ : Nat → V) :
    bval V .lfpFam us ∈ˢ interp V ρ (BConst.typeAV .lfpFam us) := by
  show lfpFamV V (lv us 0) (lv us 1) ∈ˢ _
  simp only [BConst.typeAV, arrowA, interp_pi, interp_sort, interp_bvar, AnnotTerm.lift,
    AnnotTerm.liftN, cons_zero, cons_succ]
  exact lfpFamV_mem V (lv us 0) (lv us 1)

/-! ## The capstone

`ConstOk.lean`'s `bval_mem_type`, over `interp` and `BConst.typeAV`.
This is what the skeleton's `const` row waits on, and with it
deliverable (2) stands at ten formers of ten. -/

/-- **Every built-in constant inhabits its annotated type.** -/
theorem bval_mem_type (c : BConst) (us : List Nat) (ρ : Nat → V) :
    bval V c us ∈ˢ interp V ρ (BConst.typeAV c us) := by
  cases c with
  | nat => exact bval_mem_nat V us ρ
  | natZero => exact bval_mem_natZero V us ρ
  | natSucc => exact bval_mem_natSucc V us ρ
  | natRec => exact bval_mem_natRec V us ρ
  | punit => exact bval_mem_punit V us ρ
  | punitUnit => exact bval_mem_punitUnit V us ρ
  | punitRec => exact bval_mem_punitRec V us ρ
  | psigma => exact bval_mem_psigma V us ρ
  | psigmaMk => exact bval_mem_psigmaMk V us ρ
  | empty => exact bval_mem_empty V us ρ
  | emptyRec => exact bval_mem_emptyRec V us ρ
  | quot => exact bval_mem_quot V us ρ
  | quotMk => exact bval_mem_quotMk V us ρ
  | quotLift => exact bval_mem_quotLift V us ρ
  | quotInd => exact bval_mem_quotInd V us ρ
  | quotSound => exact bval_mem_quotSound V us ρ
  | propext => exact bval_mem_propext V us ρ
  | choice => exact bval_mem_choice V us ρ
  | lfpFam => exact bval_mem_lfpFam V us ρ

end ConLeche.Semantics
