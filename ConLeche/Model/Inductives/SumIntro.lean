module

public import ConLeche.Model.Inductives.StructIntro
public import ConLeche.Semantics.Tower.SumWire

public section

/-!
# The sum leaves' bit validity and P packages (task #175 sum-types,
indexed)

`AnnotValid` for the three sum leaves at an indexed family.  The
case split and the injection carry no `.pi` node (hereditary
plumbing); the squash carrier's, the index equation's and the
recursor's motive `.pi` nodes carry the genuine clause — a zero
codomain bit over a truth value — discharged from
`piR_zero_mem_univZero` (the squash carrier, the equation chain) and
from the motive's own applications being truth values at a zero
elimination level (the recursor, `RecHypS.hM0`).  The restricted
chains (`rChain`) are bit-valid from the fields' validity at the
shifted frame and the index readings' validity at fitting field
frames (`rChain_validV`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## Kit -/

theorem AnnotValid.mkAppN_inv {ρ : Nat → V} :
    ∀ {args : List AnnotTerm} {f : AnnotTerm}, AnnotValid V ρ (AnnotTerm.mkAppN f args) →
      AnnotValid V ρ f ∧ ∀ a ∈ args, AnnotValid V ρ a
  | [], _, h => ⟨h, fun _ ha => nomatch ha⟩
  | a :: args, f, h => by
    rw [AnnotTerm.mkAppN_cons] at h
    obtain ⟨hfa, hall⟩ := AnnotValid.mkAppN_inv h
    rw [AnnotValid_app] at hfa
    exact ⟨hfa.1, fun a' ha' => by
      rcases List.mem_cons.mp ha' with rfl | ha'
      · exact hfa.2
      · exact hall a' ha'⟩

theorem numeralAV_validV (i : Nat) (σ : Nat → V) : AnnotValid V σ (numeralAV i) := by
  induction i with
  | zero => trivial
  | succ i ih =>
    show AnnotValid V σ (.app (.const .natSucc []) (numeralAV i))
    rw [AnnotValid_app]
    exact ⟨trivial, ih⟩

theorem succsAV_validV : ∀ (j : Nat) {kx : AnnotTerm} {σ : Nat → V},
    AnnotValid V σ kx → AnnotValid V σ (succsAV j kx)
  | 0, _, _, h => h
  | j + 1, kx, σ, h => by
    show AnnotValid V σ (.app (.const .natSucc []) (succsAV j kx))
    rw [AnnotValid_app]
    exact ⟨trivial, succsAV_validV j h⟩

theorem natRecAV_validV {u : Nat} {M z s kx : AnnotTerm} {σ : Nat → V}
    (hM : AnnotValid V σ M) (hz : AnnotValid V σ z) (hs : AnnotValid V σ s)
    (hk : AnnotValid V σ kx) : AnnotValid V σ (natRecAV u M z s kx) := by
  show AnnotValid V σ (.app (.app (.app (.app (.const .natRec [u]) M) z) s) kx)
  simp only [AnnotValid_app, AnnotValid_const]
  exact ⟨⟨⟨⟨trivial, hM⟩, hz⟩, hs⟩, hk⟩

theorem natSortMotiveAV_validV (w : Nat) (σ : Nat → V) :
    AnnotValid V σ (natSortMotiveAV w) := by
  show AnnotValid V σ (.lam (w + 1) natAV (.sort w))
  rw [AnnotValid_lam]
  exact ⟨trivial, fun _ _ => trivial⟩

/-- The selector is bit-valid from the spellings' validity at the
retracted environment (hereditary; no `.pi` node). -/
theorem caseAVAt_validV {w : Nat} :
    ∀ {Ts : List AnnotTerm} {d : Nat} {kx : AnnotTerm} {σ : Nat → V},
      (∀ T ∈ Ts, AnnotValid V (shiftE d 0 σ) T) → AnnotValid V σ kx →
      AnnotValid V σ (caseAVAt w Ts d kx)
  | [], _, _, _, _, _ => trivial
  | T :: Ts, d, kx, σ, hT, hk => by
    refine natRecAV_validV (natSortMotiveAV_validV w σ) ?_ ?_ hk
    · rw [AnnotValid_liftN]; exact hT T List.mem_cons_self
    · rw [AnnotValid_lam]
      refine ⟨trivial, fun b _ => ?_⟩
      rw [AnnotValid_lam]
      refine ⟨trivial, fun a _ => ?_⟩
      refine caseAVAt_validV (Ts := Ts) (d := d + 2) (kx := .bvar 1) (σ := cons a (cons b σ))
        ?_ trivial
      rw [shiftE_step]
      exact fun T' hT' => hT T' (List.mem_cons_of_mem _ hT')

/-! ## The index equation -/

/-- The equation chain is a truth value (every node is a
`Prop`-product). -/
theorem eqChainAV_mem_univZero : ∀ (eqs : List (AnnotTerm × AnnotTerm)) (ρ : Nat → V),
    interp V ρ (eqChainAV eqs) ∈ˢ (univZero : V)
  | [], _ => by
    show (empty : V) ∈ˢ univZero
    rw [← univ_zero]; exact empty_mem_univ 0
  | (_, _) :: _, _ => piR_zero_mem_univZero

theorem eqChainAV_validV :
    ∀ {eqs : List (AnnotTerm × AnnotTerm)} {ρ : Nat → V},
      (∀ e ∈ eqs, AnnotValid V ρ e.1 ∧ AnnotValid V ρ e.2) →
      AnnotValid V ρ (eqChainAV eqs)
  | [], _, _ => trivial
  | (a, b) :: r, ρ, h => by
    show AnnotValid V ρ (.pi 0 0 (.eqE a b) ((eqChainAV r).liftN 1 0))
    rw [AnnotValid_pi, AnnotValid_eqE]
    refine ⟨h (a, b) List.mem_cons_self, fun x _ => ?_, fun _ x _ => ?_⟩
    · rw [AnnotValid_liftN, show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
      exact eqChainAV_validV fun e he => h e (List.mem_cons_of_mem _ he)
    · rw [interp_liftN, show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
      exact eqChainAV_mem_univZero r ρ

/-- The index equation is bit-valid from its sides' validity. -/
theorem idxEqAV_validV {eqs : List (AnnotTerm × AnnotTerm)} {ρ : Nat → V}
    (h : ∀ e ∈ eqs, AnnotValid V ρ e.1 ∧ AnnotValid V ρ e.2) :
    AnnotValid V ρ (idxEqAV eqs) := by
  show AnnotValid V ρ (.pi 0 0 (eqChainAV eqs) (.const .empty [0]))
  rw [AnnotValid_pi]
  exact ⟨eqChainAV_validV h, fun _ _ => trivial,
    fun _ _ _ => by rw [← univ_zero]; exact empty_mem_univ 0⟩

theorem idxEqAV_nil_validV (ρ : Nat → V) : AnnotValid V ρ (idxEqAV []) :=
  idxEqAV_validV fun _ h => nomatch h

/-- A chain extended by one field valid at every fitting frame. -/
theorem FieldsValid_append_one {E : AnnotTerm} :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V}, FieldsValid ρ Fs →
      (∀ bs : List V, SpineFit ρ Fs bs → AnnotValid V (consList bs ρ) E) →
      FieldsValid ρ (Fs ++ [E])
  | [], ρ, _, hE => ⟨by simpa [consList] using hE [] trivial, fun _ _ => trivial⟩
  | F :: Fs, ρ, hv, hE => by
    refine ⟨hv.1, fun a ha => ?_⟩
    refine FieldsValid_append_one (hv.2 a ha) fun bs hsp => ?_
    have := hE (a :: bs) ⟨ha, hsp⟩
    rwa [consList_cons] at this

/-- The lifted chain's validity is the chain's at the shifted frame. -/
theorem FieldsValid_liftFields {n : Nat} :
    ∀ {Fs : List AnnotTerm} {k : Nat} {σ : Nat → V},
      FieldsValid σ (liftFields n k Fs) ↔ FieldsValid (shiftE n k σ) Fs
  | [], _, _ => Iff.rfl
  | F :: Fs, k, σ => by
    simp only [liftFields_cons, FieldsValid, AnnotValid_liftN, interp_liftN]
    refine and_congr Iff.rfl (forall_congr' fun a => imp_congr Iff.rfl ?_)
    rw [cons_shiftE]
    exact FieldsValid_liftFields

/-- **The restricted chain is bit-valid** from the fields' validity at
the shifted frame and the index readings' validity at fitting field
frames. -/
theorem rChain_validV {d nIdx : Nat} {Fs Es : List AnnotTerm} {σ : Nat → V}
    (hv : FieldsValid (shiftE d 0 σ) Fs)
    (hE : ∀ bs : List V, SpineFit (shiftE d 0 σ) Fs bs →
      ∀ E ∈ Es, AnnotValid V (consList bs (shiftE d 0 σ)) E) :
    FieldsValid σ (rChain d nIdx Fs Es) := by
  unfold rChain
  refine FieldsValid_append_one (FieldsValid_liftFields.mpr hv) fun bs hsp => ?_
  have hsp' : SpineFit (shiftE d 0 σ) Fs bs := (spineFit_liftFields d).mp hsp
  have hlen : bs.length = Fs.length := hsp'.length_eq
  refine idxEqAV_validV fun e he => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp he
  refine ⟨?_, trivial⟩
  show AnnotValid V (consList bs σ) ((Es.getD l default).liftN d Fs.length)
  rw [AnnotValid_liftN, ← hlen, shiftE_consList_len]
  by_cases hl : l < Es.length
  · exact hE bs hsp' _ (getD_mem_of_lt hl)
  · rw [getD_eq_default_of_le (by omega)]
    trivial

/-- Per-constructor hereditary validity. -/
@[expose] def SumFieldsValid (ρ : Nat → V) (Fss : List (List AnnotTerm)) : Prop :=
  ∀ Fs ∈ Fss, FieldsValid ρ Fs

/-- The restricted chains are bit-valid. -/
theorem rChains_validV {d nIdx : Nat} {Fss Ess : List (List AnnotTerm)} {σ : Nat → V}
    (hv : SumFieldsValid (shiftE d 0 σ) Fss)
    (hE : ∀ j, j < Fss.length → ∀ bs : List V, SpineFit (shiftE d 0 σ) (Fss.getD j []) bs →
      ∀ E ∈ Ess.getD j [], AnnotValid V (consList bs (shiftE d 0 σ)) E) :
    SumFieldsValid σ (rChains d nIdx Fss Ess) := by
  intro Fs' hFs'
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hFs'
  rw [rChains_getElem?] at hj
  cases hF : Fss[j]? with
  | none => rw [hF] at hj; exact nomatch hj
  | some Fs =>
    cases hEs : Ess[j]? with
    | none => rw [hF, hEs] at hj; exact nomatch hj
    | some Es =>
      rw [hF, hEs] at hj
      obtain rfl := Option.some.inj hj
      have hjn : j < Fss.length := (List.getElem?_eq_some_iff.mp hF).1
      refine rChain_validV (hv Fs (List.mem_of_getElem? hF)) fun bs hsp E hE' => ?_
      have hFs : Fss.getD j [] = Fs := by rw [List.getD_eq_getElem?_getD, hF]; rfl
      have hEsD : Ess.getD j [] = Es := by rw [List.getD_eq_getElem?_getD, hEs]; rfl
      exact hE j hjn bs (hFs ▸ hsp) E (hEsD ▸ hE')

/-- The unit-restricted chains are bit-valid. -/
theorem uChains_validV {ρ : Nat → V} {Fss : List (List AnnotTerm)} (hv : SumFieldsValid ρ Fss) :
    SumFieldsValid ρ (uChains Fss) := by
  intro Fs' hFs'
  obtain ⟨Fs, hFs, rfl⟩ := List.mem_map.mp hFs'
  exact FieldsValid_append_one (hv Fs hFs) fun _ _ => idxEqAV_nil_validV _

/-! ## The carrier -/

theorem towers_validV {w : Nat} {ρ : Nat → V} {Fss : List (List AnnotTerm)}
    (hv : SumFieldsValid ρ Fss) : ∀ T ∈ Fss.map (towerBodyAV w), AnnotValid V ρ T := by
  intro T hT
  obtain ⟨Fs, hFs, rfl⟩ := List.mem_map.mp hT
  exact towerBodyAV_validV (hv Fs hFs)

theorem case_validV_at {w : Nat} {ρp σ : Nat → V} {d : Nat} (hsh : shiftE d 0 σ = ρp)
    {Fss : List (List AnnotTerm)} (hv : SumFieldsValid ρp Fss) (k : V) :
    AnnotValid V (cons k σ) (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0)) := by
  refine caseAVAt_validV ?_ trivial
  rw [shiftE_succ_cons, hsh]
  exact towers_validV hv

theorem sumBodyAVPos_validV {w : Nat} {ρ : Nat → V} {Fss : List (List AnnotTerm)}
    (hv : SumFieldsValid ρ Fss) : AnnotValid V ρ (sumBodyAVPos w Fss) := by
  unfold sumBodyAVPos
  rw [AnnotValid_app, AnnotValid_app, AnnotValid_lam]
  exact ⟨⟨trivial, trivial⟩, trivial, fun k _ => case_validV_at (shiftE_zero_zero ρ) hv k⟩

theorem sqSumBodyAV_validV {ρ : Nat → V} {Fss : List (List AnnotTerm)}
    (hv : SumFieldsValid ρ Fss) : AnnotValid V ρ (sqSumBodyAV Fss) := by
  unfold sqSumBodyAV negAV
  rw [AnnotValid_pi]
  refine ⟨?_, fun _ _ => by simp, fun _ _ _ => by rw [← univ_zero]; exact empty_mem_univ 0⟩
  rw [AnnotValid_pi]
  refine ⟨trivial, fun k _ => ?_, fun _ k _ => piR_zero_mem_univZero⟩
  rw [AnnotValid_pi]
  exact ⟨case_validV_at (shiftE_zero_zero ρ) hv k, fun _ _ => by simp,
    fun _ _ _ => by rw [← univ_zero]; exact empty_mem_univ 0⟩

theorem sumBodyAV_validV {w : Nat} {ρ : Nat → V} {Fss : List (List AnnotTerm)}
    (hv : SumFieldsValid ρ Fss) : AnnotValid V ρ (sumBodyAV w Fss) := by
  by_cases hw : w = 0
  · subst hw; rw [sumBodyAV_zero]; exact sqSumBodyAV_validV hv
  · rw [sumBodyAV_pos hw]; exact sumBodyAVPos_validV hv

/-- The type-former leaf's P currency. -/
theorem sumTyAV_wellDenotedV {w : Nat} {Fss : List (List AnnotTerm)}
    {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}
    (hok : ParamsOkS w ρ Fss pps)
    (hval : UnderTowerValid ρ (sumBodyAV w Fss) pps) :
    WellDenotedV V ρ (sumTyAV w pps Fss) :=
  ⟨sumTyAV_wellDenoted hok, mkLamsC_validV hval⟩

/-! ## The constructor -/

theorem sumInjAtAV_validV {w : Nat} {ρp σ : Nat → V} {d : Nat} (hsh : shiftE d 0 σ = ρp)
    {Fss : List (List AnnotTerm)} (hv : SumFieldsValid ρp Fss) {tag payload : AnnotTerm}
    (ht : AnnotValid V σ tag) (hp : AnnotValid V σ payload) :
    AnnotValid V σ (sumInjAtAV w Fss d tag payload) := by
  show AnnotValid V σ (.app (.app (.app (.app (.const .psigmaMk [w, w]) natAV)
    (.lam (w + 1) natAV (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0)))) tag) payload)
  simp only [AnnotValid_app, AnnotValid_const, AnnotValid_lam]
  exact ⟨⟨⟨⟨trivial, trivial⟩, trivial, fun k _ => case_validV_at hsh hv k⟩, ht⟩, hp⟩

/-- The proof-field-terminated tupler is bit-valid at a fitting frame
(graph regime). -/
theorem mkTowerGoUPos_validV {w : Nat} {E : AnnotTerm} :
    ∀ {Fs : List AnnotTerm} {ρp : Nat → V} {bs : List V},
      FieldsValid ρp (Fs ++ [E]) → SpineFit ρp Fs bs →
      AnnotValid V (consList bs ρp) (mkTowerGoUPos w E Fs)
  | [], ρp, [], hv, _ => by
    show AnnotValid V ρp (.app (.app (.app (.app (.const .psigmaMk [w, w]) E)
        (.lam (w + 1) E (.const .punit [w + 1]))) .prf) (.const .punitUnit []))
    simp only [AnnotValid_app, AnnotValid_const, AnnotValid_lam, AnnotValid_prf]
    exact ⟨⟨⟨⟨trivial, hv.1⟩, hv.1, fun _ _ => trivial⟩, trivial⟩, trivial⟩
  | [], _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, [], _, hsp => hsp.elim
  | F :: Fs, ρp, b :: bs, hv, hsp => by
    have hlen : bs.length = Fs.length := hsp.2.length_eq
    have hshift : shiftE (Fs.length + 1) 0 (consList bs (cons b ρp)) = ρp := by
      rw [← hlen,
        show bs.length + 1 = bs.length + (0 + 1) by rw [Nat.zero_add],
        shiftE_consList_add bs (0 + 1) (cons b ρp), Nat.zero_add,
        shiftE_succ_cons, shiftE_zero_zero]
    have hA : interp V (consList bs (cons b ρp)) (F.liftN (Fs.length + 1))
        = interp V ρp F := by
      rw [interp_liftN, hshift]
    rw [List.cons_append] at hv
    show AnnotValid V (consList bs (cons b ρp))
      (.app (.app (.app (.app (.const .psigmaMk [w, w])
          (F.liftN (Fs.length + 1)))
          (.lam (w + 1) (F.liftN (Fs.length + 1))
            ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1)))
          (.bvar Fs.length))
        (mkTowerGoUPos w E Fs))
    rw [AnnotValid_app]
    refine ⟨?_, mkTowerGoUPos_validV (hv.2 b hsp.1) hsp.2⟩
    rw [AnnotValid_app]
    refine ⟨?_, by rw [AnnotValid_bvar]; trivial⟩
    rw [AnnotValid_app]
    refine ⟨?_, ?_⟩
    · rw [AnnotValid_app]
      refine ⟨by rw [AnnotValid_const]; trivial, ?_⟩
      rw [AnnotValid_liftN, hshift]
      exact hv.1
    · rw [AnnotValid_lam]
      refine ⟨by rw [AnnotValid_liftN, hshift]; exact hv.1, ?_⟩
      intro x hx
      rw [hA] at hx
      rw [AnnotValid_liftN, ← cons_shiftE, hshift]
      exact towerBodyAV_validV (hv.2 x hx)

/-- The tupler is bit-valid at a fitting frame, both regimes. -/
theorem mkTowerGoU_validV {w : Nat} {E : AnnotTerm} {Fs : List AnnotTerm} {ρp : Nat → V}
    {bs : List V} (hv : FieldsValid ρp (Fs ++ [E])) (hsp : SpineFit ρp Fs bs) :
    AnnotValid V (consList bs ρp) (mkTowerGoU w Fs E) := by
  by_cases hw : w = 0
  · subst hw; rw [mkTowerGoU_zero]; trivial
  · rw [mkTowerGoU_pos hw]; exact mkTowerGoUPos_validV hv hsp

/-- The constructor's body is bit-valid at a fitting field frame. -/
theorem sumInj_validV_at_fields {w j : Nat} {ρp : Nat → V} {Fs : List AnnotTerm}
    {Fss : List (List AnnotTerm)} {bs : List V}
    (hv : SumFieldsValid ρp Fss) (hvF : FieldsValid ρp Fs) (hsp : SpineFit ρp Fs bs) :
    AnnotValid V (consList bs ρp)
      (sumInjAtAV w Fss Fs.length (numeralAV j) (mkTowerGoU w Fs (idxEqAV []))) := by
  have hlen : bs.length = Fs.length := hsp.length_eq
  have hsh : shiftE Fs.length 0 (consList bs ρp) = ρp := by rw [← hlen]; exact shiftE_consList bs ρp
  exact sumInjAtAV_validV hsh hv (numeralAV_validV j _)
    (mkTowerGoU_validV (FieldsValid_append_one hvF fun _ _ => idxEqAV_nil_validV _) hsp)

/-- The constructor leaf's P currency. -/
theorem sumMkAV_wellDenotedV {w j : Nat} {bodyC : AnnotTerm} {ρ : Nat → V}
    {Fss : List (List AnnotTerm)} {pds fds : List (Nat × Nat × AnnotTerm)}
    (hz : ∀ d ∈ pds ++ fds, (w = 0 ↔ d.2.1 = 0))
    (hpre : MkPreS w j ρ (fds.map (·.2.2)) Fss bodyC pds)
    (hval : UnderTowerValid ρ
      (sumInjAtAV w Fss (fds.map (·.2.2)).length (numeralAV j)
        (mkTowerGoU w (fds.map (·.2.2)) (idxEqAV [])))
      (pds ++ fds)) :
    WellDenotedV V ρ (sumMkAV w j (pds ++ fds) (fds.map (·.2.2)) Fss) :=
  ⟨sumMkAV_wellDenoted hz hpre, mkLamsC_validV hval⟩

/-! ## The recursor -/

theorem major_fst_validV (σ : Nat → V) : AnnotValid V σ (.fst (.bvar 0)) := by
  rw [AnnotValid_fst]; trivial

theorem major_snd_validV (σ : Nat → V) : AnnotValid V σ (.snd (.bvar 0)) := by
  rw [AnnotValid_snd]; trivial

theorem motAppAV_validV (n nIdx D' : Nat) (σ : Nat → V) :
    AnnotValid V σ (motAppAV n nIdx D') :=
  mkAppN_validV trivial fun a ha => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha
    trivial

theorem srcAV_validV (nIdx D' : Nat) (s : Option Nat) (σ : Nat → V) :
    AnnotValid V σ (srcAV nIdx D' s) := by
  cases s <;> trivial

/-- The stage motive body is bit-valid at a tag in `ω`: its `.pi`
node's zero clause is the motive's application being a truth value. -/
theorem motiveBody_validV {ℓ w D : Nat} {ρ₀ σ : Nat → V} {Fss Ess : List (List AnnotTerm)}
    {Ids : List AnnotTerm} {famAt : List V → V}
    (hfr : RecFrameS D ρ₀ σ) (hyp : RecHypCore ℓ w ρ₀ Fss Ess Ids famAt)
    (hv : SumFieldsValid ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
    (j : Nat) (k : V) :
    AnnotValid V (cons k σ)
      (caseMotiveBodyAV ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
        Fss.length Ids.length D j) := by
  have hsh1 : shiftE (D + 1) 0 (cons k σ) = ρ₀ := by rw [shiftE_succ_cons]; exact hfr
  show AnnotValid V (cons k σ) (.pi w ℓ _ _)
  rw [AnnotValid_pi]
  refine ⟨?_, fun y _ => ?_, fun h0 y hy => ?_⟩
  · refine caseAVAt_validV ?_ trivial
    rw [hsh1]
    exact fun T hT => towers_validV hv T (List.mem_of_mem_drop hT)
  · rw [AnnotValid_app]
    refine ⟨motAppAV_validV _ _ _ _, sumInjAtAV_validV (by rw [shiftE_step]; exact hfr) hv
      (succsAV_validV j trivial) trivial⟩
  · -- the zero clause: the motive's application is a truth value
    show interp V (cons y (cons k σ))
      (.app (motAppAV Fss.length Ids.length (D + 2))
        (sumInjAtAV w _ (D + 2) (succsAV j (.bvar 1)) (.bvar 0)))
      ∈ˢ (univZero : V)
    rw [interp_app, (motApp_facts (hfr.step y k) hyp).1]
    exact hyp.hM0 h0 _

theorem motive_validV {ℓ w D : Nat} {ρ₀ σ : Nat → V} {Fss Ess : List (List AnnotTerm)}
    {Ids : List AnnotTerm} {famAt : List V → V}
    (hfr : RecFrameS D ρ₀ σ) (hyp : RecHypCore ℓ w ρ₀ Fss Ess Ids famAt)
    (hv : SumFieldsValid ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
    (j : Nat) :
    AnnotValid V σ
      (caseMotiveAV ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
        Fss.length Ids.length D j) := by
  show AnnotValid V σ (.lam (imaxN w ℓ + 1) natAV _)
  rw [AnnotValid_lam]
  exact ⟨trivial, fun k _ => motiveBody_validV hfr hyp hv j k⟩

end ConLeche.Model
