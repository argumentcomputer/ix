module

public import ConLeche.Semantics.Tower.TowerLeaf

@[expose] public section

/-!
# The constructor tupler (task #175, stage 3b)

`mkTowerGo w Fs` spells the tier's `mkTower` — the right-nested
`.psigmaMk [w, w]` application tower with the `.punitUnit` terminator
— **at the constructor λ-frame**: the field values are the frame's own
bound variables (`.bvar m`, `m` = the count of later fields), and the
pair type arguments are the field domains lifted to that frame
(`liftN (m + 1)`, cutoff `0` for the first-component type, cutoff `1`
under the fibre λ).

The de Bruijn accounting, once: the input list is scoped as peeled —
domain `j` under the parameters plus `j` earlier fields — while every
application node sits under ALL `nF` field binders.  A suffix head
with `m` later fields therefore lifts by `m + 1` (its own binder plus
the `m` later ones); the recursive call's input is scoped one binder
deeper, and its lift amount is one smaller — the arithmetic is
self-consistent with no length parameter threaded.

`mkTowerGo_interp` is the one interpretation equation, two regimes in
one statement: at a fitting spine the tupler reads back as
`if w = 0 then pt else mkTower bs` — exactly `psigmaMkV_app`'s own
collapse, and exactly what the tier expects (`mkTower_mem` at the
graph regime, `pt_mem_tower` at squash).  The premises are
`FieldsBound` + `SpineFit`, nothing else.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The environment kit for the λ-frame -/

omit [SetTheory V] in
theorem shiftE_consList_add :
    ∀ (bs : List V) (j : Nat) (ρ : Nat → V),
      shiftE (bs.length + j) 0 (consList bs ρ) = shiftE j 0 ρ
  | [], j, ρ => by simp
  | b :: bs, j, ρ => by
    rw [consList_cons,
      show (b :: bs).length + j = bs.length + (j + 1) by
        simp [List.length_cons]; omega,
      shiftE_consList_add bs (j + 1) (cons b ρ), shiftE_succ_cons]

omit [SetTheory V] in
/-- Dropping a spine's worth of bindings lands back at the base
environment. -/
theorem shiftE_consList (bs : List V) (ρ : Nat → V) :
    shiftE bs.length 0 (consList bs ρ) = ρ := by
  have h := shiftE_consList_add bs 0 ρ
  rwa [shiftE_zero_zero] at h

omit [SetTheory V] in
theorem consList_apply_add :
    ∀ (bs : List V) (ρ : Nat → V) (i : Nat),
      consList bs ρ (i + bs.length) = ρ i
  | [], _, _ => rfl
  | b :: bs, ρ, i => by
    rw [consList_cons,
      show i + (b :: bs).length = (i + 1) + bs.length by
        simp [List.length_cons]; omega,
      consList_apply_add bs (cons b ρ) (i + 1), cons_succ]

/-! ## The tupler -/

/-- The constructor tupler at the λ-frame (see the module docstring
for the de Bruijn accounting). -/
def mkTowerGoPos (w : Nat) : List AnnotTerm → AnnotTerm
  | [] => .const .punitUnit []
  | F :: Fs =>
    .app (.app (.app (.app (.const .psigmaMk [w, w])
        (F.liftN (Fs.length + 1)))
        (.lam (w + 1) (F.liftN (Fs.length + 1))
          ((towerBodyAV w Fs).liftN (Fs.length + 1) 1)))
        (.bvar Fs.length))
      (mkTowerGoPos w Fs)

/-- The tupler, both regimes: at squash the constructor's value is the
proof point outright (`.punitUnit`, task #175 W4c/O4 — the pair
constructor's pinned valuation cannot take a data field there), the
pair tower above. -/
def mkTowerGo (w : Nat) (Fs : List AnnotTerm) : AnnotTerm :=
  if w = 0 then .const .punitUnit [] else mkTowerGoPos w Fs

theorem mkTowerGo_zero (Fs : List AnnotTerm) :
    mkTowerGo 0 Fs = .const .punitUnit [] := if_pos rfl

theorem mkTowerGo_pos {w : Nat} (hw : w ≠ 0) (Fs : List AnnotTerm) :
    mkTowerGo w Fs = mkTowerGoPos w Fs := if_neg hw

/-- **The tupler reads back as the tier's tupler**, two regimes in one
statement: at a fitting spine, `mkTower bs` in the graph regime and
`pt` at squash — `psigmaMkV_app`'s own collapse, matching the tier's
`mkTower_mem`/`pt_mem_tower` intro pair. -/
theorem mkTowerGoPos_interp {w : Nat} (hw : w ≠ 0) :
    ∀ {Fs : List AnnotTerm} {ρp : Nat → V} {bs : List V},
      FieldsBound w ρp Fs → SpineFit ρp Fs bs →
      interp V (consList bs ρp) (mkTowerGoPos w Fs)
        = if w = 0 then pt else mkTower bs
  | [], _, [], _, _ => by split <;> rfl
  | [], _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, [], _, hsp => hsp.elim
  | F :: Fs, ρp, b :: bs, hb, hsp => by
    have hlen : bs.length = Fs.length := hsp.2.length_eq
    -- the frame environment and its retraction to the base
    have hshift : shiftE (Fs.length + 1) 0 (consList bs (cons b ρp)) = ρp := by
      rw [← hlen,
        show bs.length + 1 = bs.length + (0 + 1) by rw [Nat.zero_add],
        shiftE_consList_add bs (0 + 1) (cons b ρp), Nat.zero_add,
        shiftE_succ_cons, shiftE_zero_zero]
    -- the pair-type argument's interpretation
    have hA : interp V (consList bs (cons b ρp)) (F.liftN (Fs.length + 1))
        = interp V ρp F := by
      rw [interp_liftN, hshift]
    -- the fibre λ's interpretation
    have hBfun : ∀ x : V,
        interp V (cons x (consList bs (cons b ρp)))
          ((towerBodyAV w Fs).liftN (Fs.length + 1) 1)
        = interp V (cons x ρp) (towerBodyAV w Fs) := fun x => by
      rw [interp_liftN, ← cons_shiftE, hshift]
    -- the field value's read-back
    have hval : consList bs (cons b ρp) (Fs.length) = b := by
      rw [← hlen, show bs.length = 0 + bs.length by rw [Nat.zero_add],
        consList_apply_add bs (cons b ρp) 0, cons_zero]
    -- the recursive read-back
    have hrec : interp V (consList bs (cons b ρp)) (mkTowerGoPos w Fs)
        = if w = 0 then pt else mkTower bs :=
      mkTowerGoPos_interp hw (hb.2 b hsp.1) hsp.2
    -- the psigmaMk application premises
    have hAm : interp V ρp F ∈ˢ (univ w : V) := hb.1
    have hBm : (lamR (w + 1) (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w Fs))
        ∈ˢ psigmaFibreSpace V w (interp V ρp F) :=
      lamR_mem fun x hx => by
        rw [towerBodyAV_interp (fun _ => hb.2 x hx)]
        exact towerSet_univ_teleOfFields (hb.2 x hx)
    have hfib : SetTheory.app (lamR (w + 1) (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w Fs)) b
        = towerSet w (teleOfFields (cons b ρp) Fs) := by
      rw [app_lamR_pos (Nat.succ_ne_zero w) hsp.1,
        towerBodyAV_interp (fun _ => hb.2 b hsp.1)]
    have hbm : (if w = 0 then pt else mkTower bs)
        ∈ˢ SetTheory.app (lamR (w + 1) (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w Fs)) b := by
      rw [hfib]
      split
      · next hz => exact hz ▸ pt_mem_tower_teleOfFields hsp.2
      · next hnz => exact mkTower_mem_teleOfFields hnz hsp.2
    -- assemble
    show SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (bval V .psigmaMk [w, w])
        (interp V (consList bs (cons b ρp)) (F.liftN (Fs.length + 1))))
        (lamR (w + 1)
          (interp V (consList bs (cons b ρp)) (F.liftN (Fs.length + 1)))
          fun x => interp V (cons x (consList bs (cons b ρp)))
            ((towerBodyAV w Fs).liftN (Fs.length + 1) 1)))
        (consList bs (cons b ρp) Fs.length))
        (interp V (consList bs (cons b ρp)) (mkTowerGoPos w Fs))
      = if w = 0 then pt else mkTower (b :: bs)
    have hbv : bval V .psigmaMk [w, w] = psigmaMkV V w w := rfl
    rw [hA, hval, hrec]
    have hBeq : (fun x => interp V (cons x (consList bs (cons b ρp)))
          ((towerBodyAV w Fs).liftN (Fs.length + 1) 1))
        = fun x => interp V (cons x ρp) (towerBodyAV w Fs) :=
      funext hBfun
    rw [hBeq, hbv, psigmaMkV_app V hAm hBm hsp.1 hbm,
      show Nat.max w w = w from Nat.max_self w]
    split <;> rfl

/-- **The tupler reads back as the tier's tupler**, both regimes. -/
theorem mkTowerGo_interp {w : Nat} {Fs : List AnnotTerm} {ρp : Nat → V}
    {bs : List V} (hb : w ≠ 0 → FieldsBound w ρp Fs)
    (hsp : SpineFit ρp Fs bs) :
    interp V (consList bs ρp) (mkTowerGo w Fs)
      = if w = 0 then pt else mkTower bs := by
  by_cases hw : w = 0
  · subst hw; rw [mkTowerGo_zero, if_pos rfl]; rfl
  · rw [mkTowerGo_pos hw]; exact mkTowerGoPos_interp hw (hb hw) hsp

/-! ## The tupler's grading -/

/-- The `[w, w]` instance of the pair constructor's product
membership, both regimes: in the graph regime the λ-tower folds onto
`spair` (`spair_mem` at the bottom); at squash the value IS `pt` and
every fibre is inhabited (`pt_mem_sigma`). -/
theorem psigmaMkV_ww_mem (w : Nat) :
    psigmaMkV V w w ∈ˢ piR w (univ w : V) (fun A =>
      piR w (psigmaFibreSpace V w A) (fun B =>
        piR w A (fun a =>
          piR w (SetTheory.app B a) (fun _ =>
            sigmaSet w A fun x => SetTheory.app B x)))) := by
  by_cases hw : w = 0
  · subst hw
    rw [psigmaMkV, show Nat.max 0 0 = 0 from Nat.max_self 0, lamR_zero]
    refine pt_mem_piR_zero fun A _ => ⟨pt, ?_⟩
    refine pt_mem_piR_zero fun B _ => ⟨pt, ?_⟩
    refine pt_mem_piR_zero fun a ha => ⟨pt, ?_⟩
    refine pt_mem_piR_zero fun b hb => ⟨pt, ?_⟩
    exact pt_mem_sigma ha hb
  · rw [psigmaMkV, show Nat.max w w = w from Nat.max_self w]
    refine lamR_mem fun A _ => ?_
    refine lamR_mem fun B _ => ?_
    refine lamR_mem fun a ha => ?_
    refine lamR_mem fun b hb => ?_
    exact spair_mem hw ha hb

/-- **The tupler is graded** (`WellDenoted`): the four application slots
are `psigmaMkV_ww_mem` chained down by `app_mem_piR`, the squash-side
fibre conditions all landing on `piR_zero_mem_univZero`/`sigmaSet`'s
truth value. -/
theorem mkTowerGoPos_wellDenoted {w : Nat} (hw : w ≠ 0) :
    ∀ {Fs : List AnnotTerm} {ρp : Nat → V} {bs : List V},
      FieldsOkB w ρp Fs → SpineFit ρp Fs bs →
      WellDenoted V (consList bs ρp) (mkTowerGoPos w Fs)
  | [], _, [], _, _ => by simp [mkTowerGoPos]
  | [], _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, [], _, hsp => hsp.elim
  | F :: Fs, ρp, b :: bs, hok, hsp => by
    have hb : FieldsBound w ρp (F :: Fs) := hok.toBound hw
    have hlen : bs.length = Fs.length := hsp.2.length_eq
    have hshift : shiftE (Fs.length + 1) 0 (consList bs (cons b ρp)) = ρp := by
      rw [← hlen,
        show bs.length + 1 = bs.length + (0 + 1) by rw [Nat.zero_add],
        shiftE_consList_add bs (0 + 1) (cons b ρp), Nat.zero_add,
        shiftE_succ_cons, shiftE_zero_zero]
    have hA : interp V (consList bs (cons b ρp)) (F.liftN (Fs.length + 1))
        = interp V ρp F := by
      rw [interp_liftN, hshift]
    have hBfun : ∀ x : V,
        interp V (cons x (consList bs (cons b ρp)))
          ((towerBodyAV w Fs).liftN (Fs.length + 1) 1)
        = interp V (cons x ρp) (towerBodyAV w Fs) := fun x => by
      rw [interp_liftN, ← cons_shiftE, hshift]
    have hval : consList bs (cons b ρp) (Fs.length) = b := by
      rw [← hlen, show bs.length = 0 + bs.length by rw [Nat.zero_add],
        consList_apply_add bs (cons b ρp) 0, cons_zero]
    have hrec : interp V (consList bs (cons b ρp)) (mkTowerGoPos w Fs)
        = if w = 0 then pt else mkTower bs :=
      mkTowerGoPos_interp hw (hb.2 b hsp.1) hsp.2
    have hAm : interp V ρp F ∈ˢ (univ w : V) := hb.1
    have hBv : interp V (consList bs (cons b ρp))
        (AnnotTerm.lam (w + 1) (F.liftN (Fs.length + 1))
          ((towerBodyAV w Fs).liftN (Fs.length + 1) 1))
        = lamR (w + 1) (interp V ρp F)
            (fun x => interp V (cons x ρp) (towerBodyAV w Fs)) := by
      rw [interp_lam, hA]
      exact congrArg _ (funext hBfun)
    have hBm : (lamR (w + 1) (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w Fs))
        ∈ˢ psigmaFibreSpace V w (interp V ρp F) :=
      lamR_mem fun x hx => by
        rw [towerBodyAV_interp (fun _ => hb.2 x hx)]
        exact towerSet_univ_teleOfFields (hb.2 x hx)
    -- the four squash-side fibre conditions
    have hz1 : w = 0 → ∀ A, A ∈ˢ (univ w : V) →
        piR w (psigmaFibreSpace V w A) (fun B => piR w A fun a =>
          piR w (SetTheory.app B a) fun _ => sigmaSet w A
            fun x => SetTheory.app B x) ∈ˢ (univZero : V) := by
      intro h0 A _; subst h0; exact piR_zero_mem_univZero
    have hz2 : w = 0 → ∀ B,
        B ∈ˢ psigmaFibreSpace V w (interp V ρp F) →
        piR w (interp V ρp F) (fun a => piR w (SetTheory.app B a)
          fun _ => sigmaSet w (interp V ρp F)
            fun x => SetTheory.app B x) ∈ˢ (univZero : V) := by
      intro h0 B _; subst h0; exact piR_zero_mem_univZero
    have hz3 : w = 0 → ∀ a, a ∈ˢ interp V ρp F →
        piR w (SetTheory.app (lamR (w + 1) (interp V ρp F)
            fun x => interp V (cons x ρp) (towerBodyAV w Fs)) a)
          (fun _ => sigmaSet w (interp V ρp F)
            fun x => SetTheory.app (lamR (w + 1) (interp V ρp F)
              fun y => interp V (cons y ρp) (towerBodyAV w Fs)) x)
          ∈ˢ (univZero : V) := by
      intro h0 _ _; subst h0; exact piR_zero_mem_univZero
    have hz4 : w = 0 → ∀ x,
        x ∈ˢ SetTheory.app (lamR (w + 1) (interp V ρp F)
          fun y => interp V (cons y ρp) (towerBodyAV w Fs)) b →
        sigmaSet w (interp V ρp F)
          (fun y => SetTheory.app (lamR (w + 1) (interp V ρp F)
            fun z => interp V (cons z ρp) (towerBodyAV w Fs)) y)
          ∈ˢ (univZero : V) := by
      intro h0 _ _; subst h0
      rw [sigmaSet_zero]
      exact truthVal_mem_univZero _
    -- the membership chain down the product tower
    have hm0 : psigmaMkV V w w ∈ˢ piR w (univ w : V) (fun A =>
        piR w (psigmaFibreSpace V w A) (fun B =>
          piR w A (fun a =>
            piR w (SetTheory.app B a) (fun _ =>
              sigmaSet w A fun x => SetTheory.app B x)))) :=
      psigmaMkV_ww_mem w
    have hm1 := app_mem_piR hm0 hAm hz1
    have hm2 := app_mem_piR hm1 hBm hz2
    have hm3 := app_mem_piR hm2 hsp.1 hz3
    have hfib : SetTheory.app (lamR (w + 1) (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w Fs)) b
        = towerSet w (teleOfFields (cons b ρp) Fs) := by
      rw [app_lamR_pos (Nat.succ_ne_zero w) hsp.1,
        towerBodyAV_interp (fun _ => hb.2 b hsp.1)]
    have hrm : interp V (consList bs (cons b ρp)) (mkTowerGoPos w Fs)
        ∈ˢ SetTheory.app (lamR (w + 1) (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w Fs)) b := by
      rw [hrec, hfib]
      split
      · next hz => exact hz ▸ pt_mem_tower_teleOfFields hsp.2
      · next hnz => exact mkTower_mem_teleOfFields hnz hsp.2
    -- assemble the clause tree
    show WellDenoted V (consList bs (cons b ρp))
      (.app (.app (.app (.app (.const .psigmaMk [w, w])
          (F.liftN (Fs.length + 1)))
          (.lam (w + 1) (F.liftN (Fs.length + 1))
            ((towerBodyAV w Fs).liftN (Fs.length + 1) 1)))
          (.bvar Fs.length))
        (mkTowerGoPos w Fs))
    rw [WellDenoted_app]
    refine ⟨?_, mkTowerGoPos_wellDenoted hw (hok.2.2 b hsp.1) hsp.2, ?_⟩
    · -- the triple-application head
      rw [WellDenoted_app]
      refine ⟨?_, trivial, ?_⟩
      · -- the double-application head
        rw [WellDenoted_app]
        refine ⟨?_, ?_, ?_⟩
        · -- `.psigmaMk [w,w] A`
          rw [WellDenoted_app]
          refine ⟨trivial, ?_, ?_⟩
          · rw [WellDenoted_liftN, hshift]
            exact hok.1
          · exact ⟨w, univ w, _, hm0, by rw [interp_liftN, hshift]; exact hAm,
              hz1⟩
        · -- the fibre λ
          rw [WellDenoted_lam]
          refine ⟨?_, ?_, ?_⟩
          · rw [WellDenoted_liftN, hshift]
            exact hok.1
          · intro x hx
            rw [hA] at hx
            rw [WellDenoted_liftN, ← cons_shiftE, hshift]
            exact towerBodyAV_wellDenoted (hok.2.2 x hx)
          · refine ⟨fun _ => (univ w : V), fun x hx => ?_,
              fun h0 => absurd h0 (Nat.succ_ne_zero w)⟩
            rw [hA] at hx
            rw [hBfun x, towerBodyAV_interp (fun _ => hb.2 x hx)]
            exact towerSet_univ_teleOfFields (hb.2 x hx)
        · -- the second application's kind slot
          refine ⟨w, psigmaFibreSpace V w (interp V ρp F), _, ?_, ?_, hz2⟩
          · show SetTheory.app (interp V (consList bs (cons b ρp))
                (.const .psigmaMk [w, w]))
              (interp V (consList bs (cons b ρp))
                (F.liftN (Fs.length + 1))) ∈ˢ _
            rw [hA]
            exact hm1
          · rw [hBv]
            exact hBm
      · -- the third application's kind slot
        refine ⟨w, interp V ρp F, _, ?_, ?_, hz3⟩
        · show SetTheory.app (SetTheory.app
              (interp V (consList bs (cons b ρp))
                (.const .psigmaMk [w, w]))
              (interp V (consList bs (cons b ρp))
                (F.liftN (Fs.length + 1))))
            (interp V (consList bs (cons b ρp))
              (.lam (w + 1) (F.liftN (Fs.length + 1))
                ((towerBodyAV w Fs).liftN (Fs.length + 1) 1))) ∈ˢ _
          rw [hA, hBv]
          exact hm2
        · show consList bs (cons b ρp) (Fs.length) ∈ˢ interp V ρp F
          rw [hval]
          exact hsp.1
    · -- the outer application's kind slot
      refine ⟨w, SetTheory.app (lamR (w + 1) (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w Fs)) b, _,
        ?_, hrm, hz4⟩
      show SetTheory.app (SetTheory.app (SetTheory.app
          (interp V (consList bs (cons b ρp))
            (.const .psigmaMk [w, w]))
          (interp V (consList bs (cons b ρp))
            (F.liftN (Fs.length + 1))))
          (interp V (consList bs (cons b ρp))
            (.lam (w + 1) (F.liftN (Fs.length + 1))
              ((towerBodyAV w Fs).liftN (Fs.length + 1) 1))))
        (interp V (consList bs (cons b ρp)) (.bvar Fs.length)) ∈ˢ _
      rw [hA, hBv, interp_bvar, hval]
      exact hm3

/-- **The tupler is graded** (`WellDenoted`), both regimes. -/
theorem mkTowerGo_wellDenoted {w : Nat} {Fs : List AnnotTerm} {ρp : Nat → V}
    {bs : List V} (hok : FieldsOkB w ρp Fs) (hsp : SpineFit ρp Fs bs) :
    WellDenoted V (consList bs ρp) (mkTowerGo w Fs) := by
  by_cases hw : w = 0
  · subst hw; rw [mkTowerGo_zero]; simp
  · rw [mkTowerGo_pos hw]; exact mkTowerGoPos_wellDenoted hw hok hsp

/-! ## The constructor leaf

`structMkAV w ds Fs = mkLamsC w ds (mkTowerGo w Fs)` — the
constant-bit λ-tower (bit `w`: the value's type is the structure
itself, of sort `w`, so the whole tower collapses of itself at a
squash instantiation) over the constructor type reading's binder data
`ds` (parameters ++ fields), with the tupler body.  `MkPre` is the
single hereditary premise the wiring discharges; `underTowerOk_fields`
threads the field phase with a spine accumulator (the tupler's body is
evaluated at the FULL frame, so the walk carries the prefix fit rather
than recursing on the field list). -/

/-- Walking a fitting prefix spine drops the graded chain to the
suffix. -/
theorem FieldsOkB.drop {w : Nat} :
    ∀ {Fs₁ : List AnnotTerm} {as : List V} {Fs₂ : List AnnotTerm}
      {ρ : Nat → V},
      FieldsOkB w ρ (Fs₁ ++ Fs₂) → SpineFit ρ Fs₁ as →
      FieldsOkB w (consList as ρ) Fs₂
  | [], [], _, _, h, _ => h
  | [], _ :: _, _, _, _, hsp => hsp.elim
  | _ :: _, [], _, _, _, hsp => hsp.elim
  | _ :: Fs₁, a :: as, Fs₂, ρ, h, hsp => by
    exact FieldsOkB.drop (Fs₁ := Fs₁) (as := as) (Fs₂ := Fs₂)
      (ρ := cons a ρ) (h.2.2 a hsp.1) hsp.2

/-- `MkPre`: the constructor leaf's ONE hereditary premise — each
parameter domain graded, and under every fitting parameter spine the
field chain is `FieldsOkB`-graded and the type reading's body reads
back as the instantiated carrier. -/
def MkPre (w : Nat) (ρ : Nat → V) (Fs : List AnnotTerm) (bodyC : AnnotTerm) :
    List (Nat × Nat × AnnotTerm) → Prop
  | [] => FieldsOkB w ρ Fs ∧ ∀ bs, SpineFit ρ Fs bs →
      interp V (consList bs ρ) bodyC = towerSet w (teleOfFields ρ Fs)
  | d :: pds => WellDenoted V ρ d.2.2 ∧
      ∀ a, a ∈ˢ interp V ρ d.2.2 → MkPre w (cons a ρ) Fs bodyC pds

/-- The field phase of the constructor leaf's premise: the walk
carries the prefix spine, because the tupler reads the FULL frame. -/
theorem underTowerOk_fields {w : Nat} {bodyC : AnnotTerm} {ρp : Nat → V}
    {Fs : List AnnotTerm} (hokF : FieldsOkB w ρp Fs)
    (hbody : ∀ bs : List V, SpineFit ρp Fs bs →
      interp V (consList bs ρp) bodyC
        = towerSet w (teleOfFields ρp Fs)) :
    ∀ {rest : List (Nat × Nat × AnnotTerm)} {pre : List AnnotTerm}
      {bs : List V},
      Fs = pre ++ rest.map (·.2.2) → SpineFit ρp pre bs →
      UnderTowerOk w (consList bs ρp) (mkTowerGo w Fs) bodyC rest
  | [], pre, bs, hsplit, hsp => by
    have hspF : SpineFit ρp Fs bs := by
      rw [hsplit, List.map_nil, List.append_nil]; exact hsp
    refine ⟨mkTowerGo_wellDenoted (hsplit ▸ hokF) hspF, ?_, ?_⟩
    · rw [hbody bs hspF, mkTowerGo_interp (fun hw => hokF.toBound hw) hspF]
      split
      · next hz => exact hz ▸ pt_mem_tower_teleOfFields hspF
      · next hnz => exact mkTower_mem_teleOfFields hnz hspF
    · intro h0
      rw [hbody bs hspF, h0]
      exact towerSet_zero_univZero_teleOfFields
  | d :: rest, pre, bs, hsplit, hsp => by
    have hd : FieldsOkB w (consList bs ρp) (d.2.2 :: rest.map (·.2.2)) :=
      FieldsOkB.drop (hsplit ▸ hokF) hsp
    refine ⟨hd.1, fun a ha => ?_⟩
    have hstep : UnderTowerOk w (consList (bs ++ [a]) ρp)
        (mkTowerGo w Fs) bodyC rest :=
      underTowerOk_fields hokF hbody
        (pre := pre ++ [d.2.2])
        (by rw [hsplit, List.map_cons, List.append_assoc,
          List.singleton_append])
        (hsp.append ⟨ha, trivial⟩)
    rwa [consList_append, consList_cons, consList_nil] at hstep

/-- The parameter phase: `MkPre` walks down to the field phase. -/
theorem underTowerOk_of_mkPre {w : Nat} {bodyC : AnnotTerm}
    {Fs : List AnnotTerm} {fds : List (Nat × Nat × AnnotTerm)} :
    ∀ {pds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      MkPre w ρ Fs bodyC pds → Fs = fds.map (·.2.2) →
      UnderTowerOk w ρ (mkTowerGo w Fs) bodyC (pds ++ fds)
  | [], ρ, h, hFs =>
    underTowerOk_fields h.1 h.2 (pre := []) (bs := [])
      (by simpa using hFs) trivial
  | d :: pds, ρ, h, hFs =>
    ⟨h.1, fun a ha => underTowerOk_of_mkPre (h.2 a ha) hFs⟩

/-- **The constructor leaf**: the constant-bit λ-tower (bit `w`) over
the constructor type reading's binder data, with the tupler body. -/
def structMkAV (w : Nat) (ds : List (Nat × Nat × AnnotTerm))
    (Fs : List AnnotTerm) : AnnotTerm :=
  mkLamsC w ds (mkTowerGo w Fs)

/-- **The constructor leaf inhabits its type's reading.** -/
theorem structMkAV_mem {w : Nat} {bodyC : AnnotTerm} {ρ : Nat → V}
    {pds fds : List (Nat × Nat × AnnotTerm)}
    (hz : ∀ d ∈ pds ++ fds, (w = 0 ↔ d.2.1 = 0))
    (hpre : MkPre w ρ (fds.map (·.2.2)) bodyC pds) :
    interp V ρ (structMkAV w (pds ++ fds) (fds.map (·.2.2)))
      ∈ˢ interp V ρ (mkPisAV (pds ++ fds) bodyC) :=
  mkLamsC_mem hz (underTowerOk_of_mkPre hpre rfl)

/-- **The constructor leaf's application fold** (graph regime): along
a fitting parameter + field spine, the leaf computes the tier's
tupler — the iota side's `⟦C p⃗ f⃗⟧ = mkTower f⃗`. -/
theorem structMkAV_fold {w : Nat} (hw : w ≠ 0)
    {pds fds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}
    {as bs : List V}
    (hsp₁ : SpineFit ρ (pds.map (·.2.2)) as)
    (hsp₂ : SpineFit (consList as ρ) (fds.map (·.2.2)) bs)
    (hokB : FieldsBound w (consList as ρ) (fds.map (·.2.2))) :
    (as ++ bs).foldl SetTheory.app
        (interp V ρ (structMkAV w (pds ++ fds) (fds.map (·.2.2))))
      = mkTower bs := by
  have hsp : SpineFit ρ
      (((pds ++ fds).map fun d => (w, d.2.2)).map (·.2)) (as ++ bs) := by
    have h2 : (((pds ++ fds).map fun d => (w, d.2.2)).map (·.2))
        = pds.map (·.2.2) ++ fds.map (·.2.2) := by
      simp [List.map_map, Function.comp_def]
    rw [h2]
    exact hsp₁.append hsp₂
  rw [structMkAV, mkLamsC,
    mkLamsAV_fold (fun d hd => by
      obtain ⟨d', -, rfl⟩ := List.mem_map.mp hd
      exact hw) hsp,
    consList_append, mkTowerGo_interp (fun _ => hokB) hsp₂, if_neg hw]

/-- **The constructor leaf at a squash instantiation is the proof
point** — the λ bits are `w`, so the collapse is the tower's own
(`lamR_zero`); a binder-free constructor's tupler is the `.punitUnit`
terminator, whose value is `pt` outright. -/
theorem structMkAV_zero {ds : List (Nat × Nat × AnnotTerm)}
    {Fs : List AnnotTerm} {ρ : Nat → V} :
    interp V ρ (structMkAV 0 ds Fs) = (pt : V) := by
  match ds with
  | [] =>
    show interp V ρ (mkTowerGo 0 Fs) = pt
    rw [mkTowerGo_zero]
    rfl
  | d :: ds => exact mkLamsAV_zero_head d.2.2 _ _ ρ

end ConLeche.Semantics
