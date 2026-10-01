module

public import ConLeche.Semantics.Tower.IdxEq

@[expose] public section

/-!
# The sum constructor leaf (task #175 sum-types, stage S3; indexed)

Constructor `j` of a direct sum is the constant-bit λ-tower (bit `w`)
over its type reading's binder data with the **injection** body: the
pinned pair constructor applied to the tag domain, the case-split
fibre, the numeral `j` and the constructor's own tupler.  Since task
#175 indexed every constructor tower carries one extra proof-field —
the index equation at the family's carrier, the trivially true
`idxEqAV []` at the constructor's own leaf — so the tupler is
`mkTowerGoU`: the tuple of the fields followed by the point.  It reads
to `inj j (mkTower (f⃗ ++ [pt]))` in the graph regime and to the point
at squash (`psigmaMkV`'s own collapse — `injW`), and its laws consume
`MkPreS`, the structure route's `MkPre` with the per-constructor chain
grading and the constructor's index at the base; the type reading's
body is only required to read to SOME tagged union whose `j`-th fibre
holds the tuple (at an indexed family that fibre is the restricted
tower at the constructor's own index tuple).
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The injection, spelled at a frame -/

/-- `PSigma'.mk Nat (λ k, case k) tag payload`, spelled `d` binders below
the parameter frame (the tower bodies are scoped there). -/
def sumInjAtAV (w : Nat) (Fss : List (List AnnotTerm)) (d : Nat) (tag payload : AnnotTerm) : AnnotTerm :=
  AnnotTerm.mkAppN (.const .psigmaMk [w, w])
    [natAV, .lam (w + 1) natAV (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0)),
      tag, payload]

/-- The semantic injection, both regimes: the point at squash. -/
noncomputable def injW (w i : Nat) (a : V) : V := if w = 0 then pt else inj i a

theorem injW_zero (i : Nat) (a : V) : injW 0 i a = pt := if_pos rfl
theorem injW_pos {w : Nat} (hw : w ≠ 0) (i : Nat) (a : V) : injW w i a = inj i a := if_neg hw

/-- The injection's value lands in the carrier. -/
theorem injW_mem {w : Nat} {f : Nat → V} {i : Nat} {a : V} (ha : a ∈ˢ f i) :
    injW w i a ∈ˢ sumSet w f := by
  by_cases hw : w = 0
  · subst hw; rw [injW_zero]; exact pt_mem_sumSet_zero ha
  · rw [injW_pos hw]; exact inj_mem hw ha

/-- The case-split fibre λ at a frame. -/
theorem sumFibreLam_facts {w : Nat} {ρp σ : Nat → V} {d : Nat} (hsh : shiftE d 0 σ = ρp)
    {Fss : List (List AnnotTerm)} (hok : SumFieldsOkB w ρp Fss) :
    interp V σ (.lam (w + 1) natAV (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0)))
        = lamR (w + 1) omega (natFibre (sumFibre w ρp Fss)) ∧
      lamR (w + 1) (omega : V) (natFibre (sumFibre w ρp Fss)) ∈ˢ psigmaFibreSpace V w omega ∧
      WellDenoted V σ (.lam (w + 1) natAV (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [interp_lam]
    exact lamR_congr fun k hk => (case_fibre_at hsh hok hk).1
  · refine lamR_mem fun k hk => ?_
    rw [← (case_fibre_at hsh hok hk).1]
    exact (case_fibre_at hsh hok hk).2.1
  · rw [WellDenoted_lam]
    exact ⟨trivial, fun k hk => (case_fibre_at hsh hok hk).2.2, fun _ => (univ w : V),
      fun k hk => (case_fibre_at hsh hok hk).2.1, fun h => absurd h (Nat.succ_ne_zero _)⟩

/-- **The injection reads to `injW`**: the pair at a numeral tag with
a fitting payload, the point at squash. -/
theorem sumInjAtAV_interp {w : Nat} {ρp σ : Nat → V} {d : Nat} (hsh : shiftE d 0 σ = ρp)
    {Fss : List (List AnnotTerm)} (hok : SumFieldsOkB w ρp Fss) {tag payload : AnnotTerm} {i : Nat}
    (htag : interp V σ tag = vnat i)
    (hpay : w ≠ 0 → interp V σ payload ∈ˢ sumFibre w ρp Fss i) :
    interp V σ (sumInjAtAV w Fss d tag payload) = injW w i (interp V σ payload) := by
  obtain ⟨hBv, hBm, -⟩ := sumFibreLam_facts hsh hok
  show SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app (bval V .psigmaMk [w, w])
    omega) (interp V σ (.lam (w + 1) natAV (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0)))))
    (interp V σ tag)) (interp V σ payload) = _
  rw [hBv, htag]
  by_cases hw : w = 0
  · subst hw
    show SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app (psigmaMkV V 0 0) _) _) _) _ = _
    rw [psigmaMkV, show Nat.max 0 0 = 0 from rfl, lamR_zero, app_pt, app_pt, app_pt, app_pt,
      injW_zero]
  · have hpay' : interp V σ payload
        ∈ˢ SetTheory.app (lamR (w + 1) omega (natFibre (sumFibre w ρp Fss))) (vnat i) := by
      rw [app_lamR_pos (Nat.succ_ne_zero w) (vnat_mem_omega i), natFibre_vnat]
      exact hpay hw
    show SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app (psigmaMkV V w w) _) _) _) _ = _
    rw [psigmaMkV_app V (omega_mem_univ_pos hw) hBm (vnat_mem_omega i) hpay',
      show Nat.max w w = w from Nat.max_self w, if_neg hw, injW_pos hw]
    rfl

/-- **The injection is graded**: in the graph regime the four slots
are the pair constructor's product chain, at squash the head is the
point and the slots are trivial. -/
theorem sumInjAtAV_wellDenoted {w : Nat} {ρp σ : Nat → V} {d : Nat} (hsh : shiftE d 0 σ = ρp)
    {Fss : List (List AnnotTerm)} (hok : SumFieldsOkB w ρp Fss) {tag payload : AnnotTerm} {i : Nat}
    (hoktag : WellDenoted V σ tag) (htag : interp V σ tag = vnat i)
    (hokpay : WellDenoted V σ payload)
    (hpay : w ≠ 0 → interp V σ payload ∈ˢ sumFibre w ρp Fss i) :
    WellDenoted V σ (sumInjAtAV w Fss d tag payload) := by
  obtain ⟨hBv, hBm, hBok⟩ := sumFibreLam_facts hsh hok
  by_cases hw : w = 0
  · subst hw
    refine (mkAppN_wellDenoted_of_pt_head (f := .const .psigmaMk [0, 0]) (σ := σ) trivial ?_ ?_).1
    · show psigmaMkV V 0 0 = pt
      rw [psigmaMkV, show Nat.max 0 0 = 0 from rfl, lamR_zero]
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · trivial
      · exact hBok
      · exact hoktag
      · exact hokpay
  · have hbv : interp V σ (.const .psigmaMk [w, w]) = psigmaMkV V w w := rfl
    have hA : (omega : V) ∈ˢ univ w := omega_mem_univ_pos hw
    have hz1 : w = 0 → ∀ A, A ∈ˢ (univ w : V) →
        piR w (psigmaFibreSpace V w A) (fun B => piR w A fun a =>
          piR w (SetTheory.app B a) fun _ => sigmaSet w A
            fun x => SetTheory.app B x) ∈ˢ (univZero : V) := fun h => absurd h hw
    have hz2 : w = 0 → ∀ B, B ∈ˢ psigmaFibreSpace V w omega →
        piR w omega (fun a => piR w (SetTheory.app B a)
          fun _ => sigmaSet w omega fun x => SetTheory.app B x) ∈ˢ (univZero : V) :=
      fun h => absurd h hw
    have hz3 : w = 0 → ∀ a, a ∈ˢ (omega : V) →
        piR w (SetTheory.app (lamR (w + 1) omega (natFibre (sumFibre w ρp Fss))) a)
          (fun _ => sigmaSet w omega
            fun x => SetTheory.app (lamR (w + 1) omega (natFibre (sumFibre w ρp Fss))) x)
          ∈ˢ (univZero : V) := fun h => absurd h hw
    have hz4 : w = 0 → ∀ x,
        x ∈ˢ SetTheory.app (lamR (w + 1) omega (natFibre (sumFibre w ρp Fss))) (vnat i) →
        sigmaSet w omega
          (fun y => SetTheory.app (lamR (w + 1) omega (natFibre (sumFibre w ρp Fss))) y)
          ∈ˢ (univZero : V) := fun h => absurd h hw
    have hm0 := psigmaMkV_ww_mem (V := V) w
    have hm1 := app_mem_piR hm0 hA hz1
    have hm2 := app_mem_piR hm1 hBm hz2
    have hm3 := app_mem_piR hm2 (vnat_mem_omega i) hz3
    have hpay' : interp V σ payload
        ∈ˢ SetTheory.app (lamR (w + 1) omega (natFibre (sumFibre w ρp Fss))) (vnat i) := by
      rw [app_lamR_pos (Nat.succ_ne_zero w) (vnat_mem_omega i), natFibre_vnat]
      exact hpay hw
    show WellDenoted V σ (.app (.app (.app (.app (.const .psigmaMk [w, w]) natAV)
      (.lam (w + 1) natAV (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0)))) tag) payload)
    rw [WellDenoted_app]
    refine ⟨?_, hokpay, w, _, _, ?_, hpay', hz4⟩
    · rw [WellDenoted_app]
      refine ⟨?_, hoktag, w, omega, _, ?_, by rw [htag]; exact vnat_mem_omega i, hz3⟩
      · rw [WellDenoted_app]
        refine ⟨?_, hBok, w, psigmaFibreSpace V w omega, _, ?_, by rw [hBv]; exact hBm, hz2⟩
        · rw [WellDenoted_app]
          exact ⟨trivial, trivial, w, univ w, _, hbv ▸ hm0, hA, hz1⟩
        · show SetTheory.app (interp V σ (.const .psigmaMk [w, w])) omega ∈ˢ _
          rw [hbv]; exact hm1
      · show SetTheory.app (SetTheory.app (interp V σ (.const .psigmaMk [w, w])) omega)
          (interp V σ (.lam (w + 1) natAV (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0))))
          ∈ˢ _
        rw [hbv, hBv]; exact hm2
    · show SetTheory.app (SetTheory.app (SetTheory.app (interp V σ (.const .psigmaMk [w, w])) omega)
        (interp V σ (.lam (w + 1) natAV (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0)))))
        (interp V σ tag) ∈ˢ _
      rw [hbv, hBv, htag]; exact hm3

/-! ## The tupler with the proof-field terminator

`mkTowerGoU w Fs E` spells `mkTower (f⃗ ++ [pt])` at the constructor
λ-frame: `mkTowerGoPos`'s tower over the chain `Fs ++ [E]`, whose last
component — the proof-field `E`, scoped at the full field frame — is
valued by `.prf` rather than by a binder.  Its facts are
`mkTowerGoPos`'s with one extra base case. -/

/-- The proof-field-terminated tupler, graph regime. -/
def mkTowerGoUPos (w : Nat) (E : AnnotTerm) : List AnnotTerm → AnnotTerm
  | [] =>
    .app (.app (.app (.app (.const .psigmaMk [w, w]) E)
        (.lam (w + 1) E (.const .punit [w + 1]))) .prf)
      (.const .punitUnit [])
  | F :: Fs =>
    .app (.app (.app (.app (.const .psigmaMk [w, w])
        (F.liftN (Fs.length + 1)))
        (.lam (w + 1) (F.liftN (Fs.length + 1))
          ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1)))
        (.bvar Fs.length))
      (mkTowerGoUPos w E Fs)

/-- The tupler, both regimes: the point at squash. -/
def mkTowerGoU (w : Nat) (Fs : List AnnotTerm) (E : AnnotTerm) : AnnotTerm :=
  if w = 0 then .const .punitUnit [] else mkTowerGoUPos w E Fs

theorem mkTowerGoU_zero (Fs : List AnnotTerm) (E : AnnotTerm) :
    mkTowerGoU 0 Fs E = .const .punitUnit [] := if_pos rfl

theorem mkTowerGoU_pos {w : Nat} (hw : w ≠ 0) (Fs : List AnnotTerm) (E : AnnotTerm) :
    mkTowerGoU w Fs E = mkTowerGoUPos w E Fs := if_neg hw

/-- The tupler at a fitting spine with the proof-field inhabited by the
point reads to the point-terminated tuple. -/
theorem mkTowerGoUPos_interp {w : Nat} (hw : w ≠ 0) {E : AnnotTerm} :
    ∀ {Fs : List AnnotTerm} {ρp : Nat → V} {bs : List V},
      FieldsBound w ρp (Fs ++ [E]) → SpineFit ρp Fs bs →
      (pt : V) ∈ˢ interp V (consList bs ρp) E →
      interp V (consList bs ρp) (mkTowerGoUPos w E Fs) = mkTower (bs ++ [pt])
  | [], ρp, [], hb, _, hpt => by
    have hA : interp V ρp E ∈ˢ (univ w : V) := hb.1
    have hB : (lamR (w + 1) (interp V ρp E) fun _ => (unitSet : V))
        ∈ˢ psigmaFibreSpace V w (interp V ρp E) :=
      lamR_mem fun _ _ => unitSet_mem_univ w
    have hpt' : (pt : V) ∈ˢ interp V ρp E := by simpa [consList] using hpt
    have hb' : (pt : V) ∈ˢ SetTheory.app (lamR (w + 1) (interp V ρp E) fun _ => (unitSet : V)) pt := by
      rw [app_lamR_pos (Nat.succ_ne_zero w) hpt']
      exact pt_mem_unitSet
    show SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app (bval V .psigmaMk [w, w])
        (interp V ρp E)) (lamR (w + 1) (interp V ρp E) fun _ => (unitSet : V))) pt) pt
      = mkTower [pt]
    have hbv : bval V .psigmaMk [w, w] = psigmaMkV V w w := rfl
    rw [hbv, psigmaMkV_app V hA hB hpt' hb', show Nat.max w w = w from Nat.max_self w, if_neg hw]
    rfl
  | [], _, _ :: _, _, hsp, _ => hsp.elim
  | _ :: _, _, [], _, hsp, _ => hsp.elim
  | F :: Fs, ρp, b :: bs, hb, hsp, hpt => by
    simp only [List.cons_append] at hb
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
          ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1)
        = interp V (cons x ρp) (towerBodyAV w (Fs ++ [E])) := fun x => by
      rw [interp_liftN, ← cons_shiftE, hshift]
    have hval : consList bs (cons b ρp) (Fs.length) = b := by
      rw [← hlen, show bs.length = 0 + bs.length by rw [Nat.zero_add],
        consList_apply_add bs (cons b ρp) 0, cons_zero]
    have hrec : interp V (consList bs (cons b ρp)) (mkTowerGoUPos w E Fs)
        = mkTower (bs ++ [pt]) :=
      mkTowerGoUPos_interp hw (hb.2 b hsp.1) hsp.2 hpt
    have hAm : interp V ρp F ∈ˢ (univ w : V) := hb.1
    have hBm : (lamR (w + 1) (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w (Fs ++ [E])))
        ∈ˢ psigmaFibreSpace V w (interp V ρp F) :=
      lamR_mem fun x hx => by
        rw [towerBodyAV_interp (fun _ => hb.2 x hx)]
        exact towerSet_univ_teleOfFields (hb.2 x hx)
    have hfib : SetTheory.app (lamR (w + 1) (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w (Fs ++ [E]))) b
        = towerSet w (teleOfFields (cons b ρp) (Fs ++ [E])) := by
      rw [app_lamR_pos (Nat.succ_ne_zero w) hsp.1,
        towerBodyAV_interp (fun _ => hb.2 b hsp.1)]
    have hbm : mkTower (bs ++ [pt])
        ∈ˢ SetTheory.app (lamR (w + 1) (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w (Fs ++ [E]))) b := by
      rw [hfib]
      refine mkTower_mem_teleOfFields hw (spineFit_append_split_mpr hsp.2 ?_)
      show SpineFit (consList bs (cons b ρp)) [E] [pt]
      exact ⟨hpt, trivial⟩
    show SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (bval V .psigmaMk [w, w])
        (interp V (consList bs (cons b ρp)) (F.liftN (Fs.length + 1))))
        (lamR (w + 1)
          (interp V (consList bs (cons b ρp)) (F.liftN (Fs.length + 1)))
          fun x => interp V (cons x (consList bs (cons b ρp)))
            ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1)))
        (consList bs (cons b ρp) Fs.length))
        (interp V (consList bs (cons b ρp)) (mkTowerGoUPos w E Fs))
      = mkTower (b :: bs ++ [pt])
    have hbv : bval V .psigmaMk [w, w] = psigmaMkV V w w := rfl
    rw [hA, hval, hrec]
    have hBeq : (fun x => interp V (cons x (consList bs (cons b ρp)))
          ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1))
        = fun x => interp V (cons x ρp) (towerBodyAV w (Fs ++ [E])) :=
      funext hBfun
    rw [hBeq, hbv, psigmaMkV_app V hAm hBm hsp.1 hbm,
      show Nat.max w w = w from Nat.max_self w, if_neg hw]
    rfl
where
  spineFit_append_split_mpr {ρ : Nat → V} {Fs Gs : List AnnotTerm} {as bs : List V}
      (h1 : SpineFit ρ Fs as) (h2 : SpineFit (consList as ρ) Gs bs) :
      SpineFit ρ (Fs ++ Gs) (as ++ bs) := h1.append h2

/-- **The tupler reads to the point-terminated tuple**, both regimes. -/
theorem mkTowerGoU_interp {w : Nat} {E : AnnotTerm} {Fs : List AnnotTerm} {ρp : Nat → V}
    {bs : List V} (hb : w ≠ 0 → FieldsBound w ρp (Fs ++ [E])) (hsp : SpineFit ρp Fs bs)
    (hpt : (pt : V) ∈ˢ interp V (consList bs ρp) E) :
    interp V (consList bs ρp) (mkTowerGoU w Fs E)
      = if w = 0 then pt else mkTower (bs ++ [pt]) := by
  by_cases hw : w = 0
  · subst hw; rw [mkTowerGoU_zero, if_pos rfl]; rfl
  · rw [mkTowerGoU_pos hw, if_neg hw]; exact mkTowerGoUPos_interp hw (hb hw) hsp hpt

/-- The tupler is graded (graph regime). -/
theorem mkTowerGoUPos_wellDenoted {w : Nat} (hw : w ≠ 0) {E : AnnotTerm} :
    ∀ {Fs : List AnnotTerm} {ρp : Nat → V} {bs : List V},
      FieldsOkB w ρp (Fs ++ [E]) → SpineFit ρp Fs bs →
      (pt : V) ∈ˢ interp V (consList bs ρp) E →
      WellDenoted V (consList bs ρp) (mkTowerGoUPos w E Fs)
  | [], ρp, [], hok, _, hpt => by
    have hokE : WellDenoted V ρp E := hok.1
    have hA : interp V ρp E ∈ˢ (univ w : V) := hok.2.1 hw
    have hpt' : (pt : V) ∈ˢ interp V ρp E := by simpa [consList] using hpt
    have hBm : (lamR (w + 1) (interp V ρp E) fun _ => (unitSet : V))
        ∈ˢ psigmaFibreSpace V w (interp V ρp E) :=
      lamR_mem fun _ _ => unitSet_mem_univ w
    have hbv : interp V ρp (.const .psigmaMk [w, w]) = psigmaMkV V w w := rfl
    have hz1 : w = 0 → ∀ A, A ∈ˢ (univ w : V) →
        piR w (psigmaFibreSpace V w A) (fun B => piR w A fun a =>
          piR w (SetTheory.app B a) fun _ => sigmaSet w A
            fun x => SetTheory.app B x) ∈ˢ (univZero : V) := fun h => absurd h hw
    have hz2 : w = 0 → ∀ B, B ∈ˢ psigmaFibreSpace V w (interp V ρp E) →
        piR w (interp V ρp E) (fun a => piR w (SetTheory.app B a)
          fun _ => sigmaSet w (interp V ρp E) fun x => SetTheory.app B x) ∈ˢ (univZero : V) :=
      fun h => absurd h hw
    have hz3 : w = 0 → ∀ a, a ∈ˢ interp V ρp E →
        piR w (SetTheory.app (lamR (w + 1) (interp V ρp E) fun _ => (unitSet : V)) a)
          (fun _ => sigmaSet w (interp V ρp E)
            fun x => SetTheory.app (lamR (w + 1) (interp V ρp E) fun _ => (unitSet : V)) x)
          ∈ˢ (univZero : V) := fun h => absurd h hw
    have hz4 : w = 0 → ∀ x,
        x ∈ˢ SetTheory.app (lamR (w + 1) (interp V ρp E) fun _ => (unitSet : V)) pt →
        sigmaSet w (interp V ρp E)
          (fun y => SetTheory.app (lamR (w + 1) (interp V ρp E) fun _ => (unitSet : V)) y)
          ∈ˢ (univZero : V) := fun h => absurd h hw
    have hm0 := psigmaMkV_ww_mem (V := V) w
    have hm1 := app_mem_piR hm0 hA hz1
    have hm2 := app_mem_piR hm1 hBm hz2
    have hm3 := app_mem_piR hm2 hpt' hz3
    have hlam : interp V ρp (.lam (w + 1) E (.const .punit [w + 1]))
        = lamR (w + 1) (interp V ρp E) fun _ => (unitSet : V) := rfl
    have hb' : (pt : V) ∈ˢ SetTheory.app (lamR (w + 1) (interp V ρp E) fun _ => (unitSet : V)) pt := by
      rw [app_lamR_pos (Nat.succ_ne_zero w) hpt']
      exact pt_mem_unitSet
    show WellDenoted V ρp (.app (.app (.app (.app (.const .psigmaMk [w, w]) E)
      (.lam (w + 1) E (.const .punit [w + 1]))) .prf) (.const .punitUnit []))
    rw [WellDenoted_app]
    refine ⟨?_, trivial, w, _, _, ?_, hb', hz4⟩
    · rw [WellDenoted_app]
      refine ⟨?_, trivial, w, interp V ρp E, _, ?_, hpt', hz3⟩
      · rw [WellDenoted_app]
        refine ⟨?_, ?_, w, psigmaFibreSpace V w (interp V ρp E), _, ?_, ?_, hz2⟩
        · rw [WellDenoted_app]
          exact ⟨trivial, hokE, w, univ w, _, hbv ▸ hm0, hA, hz1⟩
        · rw [WellDenoted_lam]
          exact ⟨hokE, fun _ _ => trivial, fun _ => (univ w : V),
            fun _ _ => unitSet_mem_univ w, fun h => absurd h (Nat.succ_ne_zero w)⟩
        · show SetTheory.app (interp V ρp (.const .psigmaMk [w, w])) (interp V ρp E) ∈ˢ _
          rw [hbv]; exact hm1
        · rw [hlam]; exact hBm
      · show SetTheory.app (SetTheory.app (interp V ρp (.const .psigmaMk [w, w])) (interp V ρp E))
          (interp V ρp (.lam (w + 1) E (.const .punit [w + 1]))) ∈ˢ _
        rw [hbv, hlam]; exact hm2
    · show SetTheory.app (SetTheory.app (SetTheory.app (interp V ρp (.const .psigmaMk [w, w]))
        (interp V ρp E)) (interp V ρp (.lam (w + 1) E (.const .punit [w + 1]))))
        (interp V ρp .prf) ∈ˢ _
      rw [hbv, hlam, interp_prf]; exact hm3
  | [], _, _ :: _, _, hsp, _ => hsp.elim
  | _ :: _, _, [], _, hsp, _ => hsp.elim
  | F :: Fs, ρp, b :: bs, hok, hsp, hpt => by
    simp only [List.cons_append] at hok
    have hb : FieldsBound w ρp (F :: (Fs ++ [E])) := hok.toBound hw
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
          ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1)
        = interp V (cons x ρp) (towerBodyAV w (Fs ++ [E])) := fun x => by
      rw [interp_liftN, ← cons_shiftE, hshift]
    have hval : consList bs (cons b ρp) (Fs.length) = b := by
      rw [← hlen, show bs.length = 0 + bs.length by rw [Nat.zero_add],
        consList_apply_add bs (cons b ρp) 0, cons_zero]
    have hrec : interp V (consList bs (cons b ρp)) (mkTowerGoUPos w E Fs)
        = mkTower (bs ++ [pt]) :=
      mkTowerGoUPos_interp hw (hb.2 b hsp.1) hsp.2 hpt
    have hAm : interp V ρp F ∈ˢ (univ w : V) := hb.1
    have hBv : interp V (consList bs (cons b ρp))
        (AnnotTerm.lam (w + 1) (F.liftN (Fs.length + 1))
          ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1))
        = lamR (w + 1) (interp V ρp F)
            (fun x => interp V (cons x ρp) (towerBodyAV w (Fs ++ [E]))) := by
      rw [interp_lam, hA]
      exact congrArg _ (funext hBfun)
    have hBm : (lamR (w + 1) (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w (Fs ++ [E])))
        ∈ˢ psigmaFibreSpace V w (interp V ρp F) :=
      lamR_mem fun x hx => by
        rw [towerBodyAV_interp (fun _ => hb.2 x hx)]
        exact towerSet_univ_teleOfFields (hb.2 x hx)
    have hz1 : w = 0 → ∀ A, A ∈ˢ (univ w : V) →
        piR w (psigmaFibreSpace V w A) (fun B => piR w A fun a =>
          piR w (SetTheory.app B a) fun _ => sigmaSet w A
            fun x => SetTheory.app B x) ∈ˢ (univZero : V) := fun h => absurd h hw
    have hz2 : w = 0 → ∀ B,
        B ∈ˢ psigmaFibreSpace V w (interp V ρp F) →
        piR w (interp V ρp F) (fun a => piR w (SetTheory.app B a)
          fun _ => sigmaSet w (interp V ρp F)
            fun x => SetTheory.app B x) ∈ˢ (univZero : V) := fun h => absurd h hw
    have hz3 : w = 0 → ∀ a, a ∈ˢ interp V ρp F →
        piR w (SetTheory.app (lamR (w + 1) (interp V ρp F)
            fun x => interp V (cons x ρp) (towerBodyAV w (Fs ++ [E]))) a)
          (fun _ => sigmaSet w (interp V ρp F)
            fun x => SetTheory.app (lamR (w + 1) (interp V ρp F)
              fun y => interp V (cons y ρp) (towerBodyAV w (Fs ++ [E]))) x)
          ∈ˢ (univZero : V) := fun h => absurd h hw
    have hz4 : w = 0 → ∀ x,
        x ∈ˢ SetTheory.app (lamR (w + 1) (interp V ρp F)
          fun y => interp V (cons y ρp) (towerBodyAV w (Fs ++ [E]))) b →
        sigmaSet w (interp V ρp F)
          (fun y => SetTheory.app (lamR (w + 1) (interp V ρp F)
            fun z => interp V (cons z ρp) (towerBodyAV w (Fs ++ [E]))) y)
          ∈ˢ (univZero : V) := fun h => absurd h hw
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
          fun x => interp V (cons x ρp) (towerBodyAV w (Fs ++ [E]))) b
        = towerSet w (teleOfFields (cons b ρp) (Fs ++ [E])) := by
      rw [app_lamR_pos (Nat.succ_ne_zero w) hsp.1,
        towerBodyAV_interp (fun _ => hb.2 b hsp.1)]
    have hrm : interp V (consList bs (cons b ρp)) (mkTowerGoUPos w E Fs)
        ∈ˢ SetTheory.app (lamR (w + 1) (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w (Fs ++ [E]))) b := by
      rw [hrec, hfib]
      exact mkTower_mem_teleOfFields hw (hsp.2.append ⟨hpt, trivial⟩)
    show WellDenoted V (consList bs (cons b ρp))
      (.app (.app (.app (.app (.const .psigmaMk [w, w])
          (F.liftN (Fs.length + 1)))
          (.lam (w + 1) (F.liftN (Fs.length + 1))
            ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1)))
          (.bvar Fs.length))
        (mkTowerGoUPos w E Fs))
    rw [WellDenoted_app]
    refine ⟨?_, mkTowerGoUPos_wellDenoted hw (hok.2.2 b hsp.1) hsp.2 hpt, ?_⟩
    · rw [WellDenoted_app]
      refine ⟨?_, trivial, ?_⟩
      · rw [WellDenoted_app]
        refine ⟨?_, ?_, ?_⟩
        · rw [WellDenoted_app]
          refine ⟨trivial, ?_, ?_⟩
          · rw [WellDenoted_liftN, hshift]
            exact hok.1
          · exact ⟨w, univ w, _, hm0, by rw [interp_liftN, hshift]; exact hAm, hz1⟩
        · rw [WellDenoted_lam]
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
        · refine ⟨w, psigmaFibreSpace V w (interp V ρp F), _, ?_, ?_, hz2⟩
          · show SetTheory.app (interp V (consList bs (cons b ρp))
                (.const .psigmaMk [w, w]))
              (interp V (consList bs (cons b ρp))
                (F.liftN (Fs.length + 1))) ∈ˢ _
            rw [hA]
            exact hm1
          · rw [hBv]
            exact hBm
      · refine ⟨w, interp V ρp F, _, ?_, ?_, hz3⟩
        · show SetTheory.app (SetTheory.app
              (interp V (consList bs (cons b ρp))
                (.const .psigmaMk [w, w]))
              (interp V (consList bs (cons b ρp))
                (F.liftN (Fs.length + 1))))
            (interp V (consList bs (cons b ρp))
              (.lam (w + 1) (F.liftN (Fs.length + 1))
                ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1))) ∈ˢ _
          rw [hA, hBv]
          exact hm2
        · show consList bs (cons b ρp) (Fs.length) ∈ˢ interp V ρp F
          rw [hval]
          exact hsp.1
    · refine ⟨w, SetTheory.app (lamR (w + 1) (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w (Fs ++ [E]))) b, _,
        ?_, hrm, hz4⟩
      show SetTheory.app (SetTheory.app (SetTheory.app
          (interp V (consList bs (cons b ρp))
            (.const .psigmaMk [w, w]))
          (interp V (consList bs (cons b ρp))
            (F.liftN (Fs.length + 1))))
          (interp V (consList bs (cons b ρp))
            (.lam (w + 1) (F.liftN (Fs.length + 1))
              ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1))))
        (interp V (consList bs (cons b ρp)) (.bvar Fs.length)) ∈ˢ _
      rw [hA, hBv, interp_bvar, hval]
      exact hm3

/-- **The tupler is graded**, both regimes. -/
theorem mkTowerGoU_wellDenoted {w : Nat} {E : AnnotTerm} {Fs : List AnnotTerm} {ρp : Nat → V}
    {bs : List V} (hok : FieldsOkB w ρp (Fs ++ [E])) (hsp : SpineFit ρp Fs bs)
    (hpt : (pt : V) ∈ˢ interp V (consList bs ρp) E) :
    WellDenoted V (consList bs ρp) (mkTowerGoU w Fs E) := by
  by_cases hw : w = 0
  · subst hw; rw [mkTowerGoU_zero]; simp
  · rw [mkTowerGoU_pos hw]; exact mkTowerGoUPos_wellDenoted hw hok hsp hpt

/-! ## The unit-restricted chains -/

/-- The constructor leaf's chains: every constructor's field chain
followed by the trivially true index equation (the extra proof-field
is the point). -/
def uChains (Fss : List (List AnnotTerm)) : List (List AnnotTerm) :=
  Fss.map fun Fs => Fs ++ [idxEqAV []]

theorem uChains_getElem? (Fss : List (List AnnotTerm)) (j : Nat) :
    (uChains Fss)[j]? = Fss[j]?.map fun Fs => Fs ++ [idxEqAV []] := by
  simp [uChains]

/-- The unit-restricted chains are graded when the chains are. -/
theorem SumFieldsOkB_uChains {w : Nat} {ρ : Nat → V} {Fss : List (List AnnotTerm)}
    (hok : SumFieldsOkB w ρ Fss) : SumFieldsOkB w ρ (uChains Fss) := by
  intro Fs' hFs'
  obtain ⟨Fs, hFs, rfl⟩ := List.mem_map.mp hFs'
  exact FieldsOkB_append_idxEq (hok Fs hFs) fun _ _ _ h => nomatch h

/-- The trivially true index equation holds. -/
theorem pt_mem_idxEqAV_nil (ρ : Nat → V) : (pt : V) ∈ˢ interp V ρ (idxEqAV []) :=
  pt_mem_idxEqAV.mpr (EqAll_nil ρ)

/-! ## The constructor leaf -/

/-- **Constructor `j`'s leaf**: the constant-bit λ-tower (bit `w`)
over the constructor type reading's binder data with the injection
of the point-terminated tupler at the numeral `j`. -/
def sumMkAV (w j : Nat) (ds : List (Nat × Nat × AnnotTerm)) (Fs : List AnnotTerm)
    (Fss : List (List AnnotTerm)) : AnnotTerm :=
  mkLamsC w ds (sumInjAtAV w Fss Fs.length (numeralAV j) (mkTowerGoU w Fs (idxEqAV [])))

/-- `MkPreS`: the constructor leaf's ONE hereditary premise — each
parameter domain graded, and under every fitting parameter spine every
constructor's chain is graded, this constructor's chain is the `j`-th,
and the type reading's body reads back as SOME tagged union whose
`j`-th fibre holds the point-terminated tuple. -/
def MkPreS (w j : Nat) (ρ : Nat → V) (Fs : List AnnotTerm) (Fss : List (List AnnotTerm))
    (bodyC : AnnotTerm) : List (Nat × Nat × AnnotTerm) → Prop
  | [] => SumFieldsOkB w ρ Fss ∧ Fss[j]? = some (Fs ++ [idxEqAV []]) ∧ ∀ bs, SpineFit ρ Fs bs →
      ∃ f : Nat → V, interp V (consList bs ρ) bodyC = sumSet w f ∧
        (if w = 0 then (pt : V) else mkTower (bs ++ [pt])) ∈ˢ f j
  | d :: pds => WellDenoted V ρ d.2.2 ∧
      ∀ a, a ∈ˢ interp V ρ d.2.2 → MkPreS w j (cons a ρ) Fs Fss bodyC pds

/-- The injection body at a fitting field frame: its value and its
grading. -/
theorem sumInj_at_fields {w j : Nat} {ρp : Nat → V} {Fs : List AnnotTerm}
    {Fss : List (List AnnotTerm)} {bs : List V}
    (hok : SumFieldsOkB w ρp Fss) (hj : Fss[j]? = some (Fs ++ [idxEqAV []]))
    (hsp : SpineFit ρp Fs bs) :
    interp V (consList bs ρp)
        (sumInjAtAV w Fss Fs.length (numeralAV j) (mkTowerGoU w Fs (idxEqAV [])))
        = injW w j (if w = 0 then pt else mkTower (bs ++ [pt])) ∧
      WellDenoted V (consList bs ρp)
        (sumInjAtAV w Fss Fs.length (numeralAV j) (mkTowerGoU w Fs (idxEqAV []))) := by
  have hokF : FieldsOkB w ρp (Fs ++ [idxEqAV []]) := hok _ (List.mem_of_getElem? hj)
  have hlen : bs.length = Fs.length := hsp.length_eq
  have hsh : shiftE Fs.length 0 (consList bs ρp) = ρp := by rw [← hlen]; exact shiftE_consList bs ρp
  have hpt : (pt : V) ∈ˢ interp V (consList bs ρp) (idxEqAV []) := pt_mem_idxEqAV_nil _
  have hmk := mkTowerGoU_interp (w := w) (fun hw => hokF.toBound hw) hsp hpt
  have hpay : w ≠ 0 → interp V (consList bs ρp) (mkTowerGoU w Fs (idxEqAV []))
      ∈ˢ sumFibre w ρp Fss j := by
    intro hw
    rw [hmk, if_neg hw, sumFibre_of_getElem? hj]
    exact mkTower_mem_teleOfFields hw (hsp.append ⟨hpt, trivial⟩)
  have hv := sumInjAtAV_interp hsh hok (interp_numeralAV j _) hpay
  rw [hmk] at hv
  exact ⟨hv, sumInjAtAV_wellDenoted hsh hok (numeralAV_wellDenoted j _) (interp_numeralAV j _)
    (mkTowerGoU_wellDenoted hokF hsp hpt) hpay⟩

/-- The field phase of the constructor leaf's premise (the walk
carries the prefix spine, as `underTowerOk_fields`). -/
theorem underTowerOkS_fields {w j : Nat} {bodyC : AnnotTerm} {ρp : Nat → V}
    {Fs : List AnnotTerm} {Fss : List (List AnnotTerm)}
    (hok : SumFieldsOkB w ρp Fss) (hj : Fss[j]? = some (Fs ++ [idxEqAV []]))
    (hbody : ∀ bs : List V, SpineFit ρp Fs bs →
      ∃ f : Nat → V, interp V (consList bs ρp) bodyC = sumSet w f ∧
        (if w = 0 then (pt : V) else mkTower (bs ++ [pt])) ∈ˢ f j) :
    ∀ {rest : List (Nat × Nat × AnnotTerm)} {pre : List AnnotTerm} {bs : List V},
      Fs = pre ++ rest.map (·.2.2) → SpineFit ρp pre bs →
      UnderTowerOk w (consList bs ρp)
        (sumInjAtAV w Fss Fs.length (numeralAV j) (mkTowerGoU w Fs (idxEqAV []))) bodyC rest
  | [], pre, bs, hsplit, hsp => by
    have hspF : SpineFit ρp Fs bs := by
      rw [hsplit, List.map_nil, List.append_nil]; exact hsp
    obtain ⟨hv, hok2⟩ := sumInj_at_fields hok hj hspF
    obtain ⟨f, hf, hmem⟩ := hbody bs hspF
    refine ⟨hok2, ?_, ?_⟩
    · rw [hf, hv]; exact injW_mem hmem
    · intro h0
      rw [hf, h0]
      exact sumSet_zero_mem_univZero _
  | d :: rest, pre, bs, hsplit, hsp => by
    have hokF : FieldsOkB w ρp (Fs ++ [idxEqAV []]) := hok _ (List.mem_of_getElem? hj)
    have hd : FieldsOkB w (consList bs ρp) (d.2.2 :: (rest.map (·.2.2) ++ [idxEqAV []])) := by
      have := FieldsOkB.drop (Fs₁ := pre) (Fs₂ := d.2.2 :: (rest.map (·.2.2) ++ [idxEqAV []]))
        (by rw [hsplit, List.append_assoc] at hokF; simpa using hokF) hsp
      exact this
    refine ⟨hd.1, fun a ha => ?_⟩
    have hstep : UnderTowerOk w (consList (bs ++ [a]) ρp)
        (sumInjAtAV w Fss Fs.length (numeralAV j) (mkTowerGoU w Fs (idxEqAV []))) bodyC rest :=
      underTowerOkS_fields hok hj hbody (pre := pre ++ [d.2.2])
        (by rw [hsplit, List.map_cons, List.append_assoc, List.singleton_append])
        (hsp.append ⟨ha, trivial⟩)
    rwa [consList_append, consList_cons, consList_nil] at hstep

/-- The parameter phase: `MkPreS` walks down to the field phase. -/
theorem underTowerOk_of_mkPreS {w j : Nat} {bodyC : AnnotTerm}
    {Fs : List AnnotTerm} {Fss : List (List AnnotTerm)} {fds : List (Nat × Nat × AnnotTerm)} :
    ∀ {pds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      MkPreS w j ρ Fs Fss bodyC pds → Fs = fds.map (·.2.2) →
      UnderTowerOk w ρ (sumInjAtAV w Fss Fs.length (numeralAV j) (mkTowerGoU w Fs (idxEqAV [])))
        bodyC (pds ++ fds)
  | [], ρ, h, hFs =>
    underTowerOkS_fields h.1 h.2.1 h.2.2 (pre := []) (bs := []) (by simpa using hFs) trivial
  | d :: pds, ρ, h, hFs =>
    ⟨h.1, fun a ha => underTowerOk_of_mkPreS (h.2 a ha) hFs⟩

/-- **The constructor leaf inhabits its type's reading.** -/
theorem sumMkAV_mem {w j : Nat} {bodyC : AnnotTerm} {ρ : Nat → V}
    {Fss : List (List AnnotTerm)} {pds fds : List (Nat × Nat × AnnotTerm)}
    (hz : ∀ d ∈ pds ++ fds, (w = 0 ↔ d.2.1 = 0))
    (hpre : MkPreS w j ρ (fds.map (·.2.2)) Fss bodyC pds) :
    interp V ρ (sumMkAV w j (pds ++ fds) (fds.map (·.2.2)) Fss)
      ∈ˢ interp V ρ (mkPisAV (pds ++ fds) bodyC) :=
  mkLamsC_mem hz (underTowerOk_of_mkPreS hpre rfl)

/-- **The constructor leaf is graded.** -/
theorem sumMkAV_wellDenoted {w j : Nat} {bodyC : AnnotTerm} {ρ : Nat → V}
    {Fss : List (List AnnotTerm)} {pds fds : List (Nat × Nat × AnnotTerm)}
    (hz : ∀ d ∈ pds ++ fds, (w = 0 ↔ d.2.1 = 0))
    (hpre : MkPreS w j ρ (fds.map (·.2.2)) Fss bodyC pds) :
    WellDenoted V ρ (sumMkAV w j (pds ++ fds) (fds.map (·.2.2)) Fss) :=
  mkLamsC_wellDenoted hz (underTowerOk_of_mkPreS hpre rfl)

/-- **The constructor leaf's application fold** (graph regime): along
a fitting parameter + field spine the leaf computes the injection of
the point-terminated tupler. -/
theorem sumMkAV_fold {w j : Nat} (hw : w ≠ 0)
    {pds fds : List (Nat × Nat × AnnotTerm)} {Fss : List (List AnnotTerm)} {ρ : Nat → V}
    {as bs : List V}
    (hsp₁ : SpineFit ρ (pds.map (·.2.2)) as)
    (hsp₂ : SpineFit (consList as ρ) (fds.map (·.2.2)) bs)
    (hok : SumFieldsOkB w (consList as ρ) Fss)
    (hj : Fss[j]? = some (fds.map (·.2.2) ++ [idxEqAV []])) :
    (as ++ bs).foldl SetTheory.app
        (interp V ρ (sumMkAV w j (pds ++ fds) (fds.map (·.2.2)) Fss))
      = inj j (mkTower (bs ++ [pt])) := by
  have hsp : SpineFit ρ
      (((pds ++ fds).map fun d => (w, d.2.2)).map (·.2)) (as ++ bs) := by
    have h2 : (((pds ++ fds).map fun d => (w, d.2.2)).map (·.2))
        = pds.map (·.2.2) ++ fds.map (·.2.2) := by
      simp [List.map_map, Function.comp_def]
    rw [h2]
    exact hsp₁.append hsp₂
  rw [sumMkAV, mkLamsC,
    mkLamsAV_fold (fun d hd => by
      obtain ⟨d', -, rfl⟩ := List.mem_map.mp hd
      exact hw) hsp,
    consList_append, (sumInj_at_fields hok hj hsp₂).1, if_neg hw, injW_pos hw]

/-- **The constructor leaf at a squash instantiation is the point.** -/
theorem sumMkAV_zero {j : Nat} {ds : List (Nat × Nat × AnnotTerm)} {Fs : List AnnotTerm}
    {Fss : List (List AnnotTerm)} {ρ : Nat → V} :
    interp V ρ (sumMkAV 0 j ds Fs Fss) = (pt : V) := by
  match ds with
  | [] =>
    show interp V ρ (sumInjAtAV 0 Fss Fs.length (numeralAV j) (mkTowerGoU 0 Fs (idxEqAV []))) = pt
    show SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app (psigmaMkV V 0 0) _) _) _) _ = _
    rw [psigmaMkV, show Nat.max 0 0 = 0 from rfl, lamR_zero, app_pt, app_pt, app_pt, app_pt]
  | d :: ds => exact mkLamsAV_zero_head d.2.2 _ _ ρ

end ConLeche.Semantics
