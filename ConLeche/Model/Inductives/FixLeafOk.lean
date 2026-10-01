module

public import ConLeche.Model.Inductives.FixRealChains
public import ConLeche.Semantics.Tower.FixWire
import ConLeche.Model.Inductives.SumIntro
public section

/-!
# The fixed-point leaf's P currency (task #188)

The former's leaf `nativeTyAVI` at the P carrier: closed
(`nativeTyAVI_below`), graded and inhabiting its type's reading
(`FixLeafI.lean`'s `nativeTyAVI_wellDenoted/_mem` at the hereditary premise
`ParamsOkXI`, walked from the former's data — `fixLeafWalks`), and
bit-valid (`AnnotValid`, the annotation's second currency): the
functor's λ's are valid over the X-chains, which are valid at every
family (`fixChainWalkValid`, the walk of `FixChainsP.lean` for the
validity predicate — the entries' validity carries off the recursive
slots exactly as their grading, `AnnotValid_congr_noBVar`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V]

/-! ## Validity ignores the variables a term does not mention -/

theorem AnnotValid_congr_noBVar :
    ∀ (e : AnnotTerm) {P : Nat → Prop} {σ σ' : Nat → V},
      NoBVar P e → AgreeOff P σ σ' → (AnnotValid V σ e ↔ AnnotValid V σ' e) := by
  intro e
  induction e with
  | bvar i => intros; simp
  | sort u => intros; simp
  | const c us => intros; simp
  | app f a ihf iha =>
    intro P σ σ' h hag
    rw [AnnotValid_app, AnnotValid_app, ihf h.1 hag, iha h.2 hag]
  | lam v A b ihA ihb =>
    intro P σ σ' h hag
    rw [AnnotValid_lam, AnnotValid_lam, ihA h.1 hag, interp_congr_noBVar A h.1 hag]
    exact and_congr Iff.rfl
      (forall_congr' fun x => imp_congr Iff.rfl (ihb h.2 (agreeOff_cons hag x)))
  | pi u v A B ihA ihB =>
    intro P σ σ' h hag
    rw [AnnotValid_pi, AnnotValid_pi, ihA h.1 hag, interp_congr_noBVar A h.1 hag]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl (ihB h.2 (agreeOff_cons hag x)))
      (imp_congr Iff.rfl (forall_congr' fun x => imp_congr Iff.rfl ?_)))
    rw [interp_congr_noBVar B h.2 (agreeOff_cons hag x)]
  | eqE a b iha ihb =>
    intro P σ σ' h hag
    rw [AnnotValid, AnnotValid, iha h.1 hag, ihb h.2 hag]
  | fst e ihe =>
    intro P σ σ' h hag
    rw [AnnotValid_fst, AnnotValid_fst, ihe h hag]
  | snd e ihe =>
    intro P σ σ' h hag
    rw [AnnotValid_snd, AnnotValid_snd, ihe h hag]
  | prf => intros; simp

/-! ## The X-chains, valid at every family -/

section Valid

variable {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {nP nF : Nat} {ks : List RecFieldKind}
  {tls : List (List (Nat × Nat × AnnotTerm))} {Fs : List AnnotTerm} {Eis : List (List AnnotTerm)}
  {Es : List AnnotTerm}

/-- A lifted entry is valid at the X-frame iff at the parameter frame
under the fields. -/
theorem AnnotValid_chainXI_ord (F : AnnotTerm) (as : List V) (t X : V) :
    AnnotValid V (consList as (cons t (cons X ρp))) (F.liftN 2 as.length)
      ↔ AnnotValid V (consList as ρp) F := by
  rw [AnnotValid_liftN, shiftE_consList_len, show (2 : Nat) = 1 + 1 from rfl,
    shiftE_succ_cons, shiftE_succ_cons, shiftE_zero_zero]

/-- A telescope valid at the parameter frame under the fields is
valid, lifted, at the X-frame. -/
theorem fieldsValid_liftTele2 (t X : V) :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (as : List V),
      FieldsValid (consList as ρp) (tl.map (·.2.2)) →
      FieldsValid (consList as (cons t (cons X ρp))) ((liftTele2 as.length tl).map (·.2.2))
  | [], _, _ => trivial
  | d :: tl, as, hF => by
    rw [liftTele2_cons, List.map_cons]
    rw [List.map_cons] at hF
    obtain ⟨hv, hrest⟩ := hF
    refine ⟨(AnnotValid_chainXI_ord _ as t X).mpr hv, fun a ha => ?_⟩
    rw [interp_chainXI_ord] at ha
    rw [consList_snoc']
    have := fieldsValid_liftTele2 t X tl (as ++ [a]) (by rw [← consList_snoc']; exact hrest a ha)
    rw [length_snoc'] at this
    exact this

/-- A valid telescope carried between frames agreeing off the slots
its domains do not mention. -/
theorem fieldsValid_congr_exclP {Q : Nat → Prop} :
    ∀ (Fs : List AnnotTerm) {d : Nat}, (∀ q, Q q → q < d) → ∀ {σ σ' : Nat → V},
      AgreeOff (exclP Q d) σ σ' →
      (∀ k F, Fs[k]? = some F → NoBVar (exclP Q (d + k)) F) →
      FieldsValid σ' Fs → FieldsValid σ Fs
  | [], _, _, _, _, _, _, _ => trivial
  | F :: Fs, d, hQ, σ, σ', hag, hnb, hF => by
    obtain ⟨hv, hrest⟩ := hF
    have hnb0 : NoBVar (exclP Q d) F := by simpa using hnb 0 F rfl
    have hval : interp V σ F = interp V σ' F := interp_congr_noBVar F hnb0 hag
    refine ⟨(AnnotValid_congr_noBVar F hnb0 hag).mpr hv, fun a ha => ?_⟩
    rw [hval] at ha
    refine fieldsValid_congr_exclP Fs (fun q hq => Nat.lt_succ_of_lt (hQ q hq))
      (agreeOff_exclP_cons hQ hag a) ?_ (hrest a ha)
    intro k F' hk
    have := hnb (k + 1) F' (by simpa using hk)
    rwa [show d + 1 + k = d + (k + 1) from by omega]

/-- A Π-tower over `Prop`-regime binders is a truth value. -/
theorem interp_mkPisAV_mem_univZero {R : AnnotTerm} :
    ∀ {gds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V}, (∀ d ∈ gds, d.2.1 = 0) →
      (gds = [] → interp V σ R ∈ˢ (univZero : V)) →
      interp V σ (mkPisAV gds R) ∈ˢ (univZero : V)
  | [], _, _, hR => by simpa [mkPisAV] using hR rfl
  | d :: gds, σ, hb, _ => by
    simp only [mkPisAV, interp_pi]
    rw [hb d List.mem_cons_self]
    exact piR_zero_mem_univZero

/-- **A Π-tower is valid** when its domains are along the telescope,
its body is at every fitting spine, and at the `Prop` regime the body
is a truth value there. -/
theorem AnnotValid_mkPisAV_of {w : Nat} {R : AnnotTerm} :
    ∀ {gds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      (∀ d ∈ gds, (d.2.1 = 0 ↔ w = 0)) →
      FieldsValid σ (gds.map (·.2.2)) →
      (∀ as, SpineFit σ (gds.map (·.2.2)) as → AnnotValid V (consList as σ) R) →
      (w = 0 → ∀ as, SpineFit σ (gds.map (·.2.2)) as →
        interp V (consList as σ) R ∈ˢ (univZero : V)) →
      AnnotValid V σ (mkPisAV gds R)
  | [], _, _, _, hR, _ => by simpa [mkPisAV, consList] using hR [] trivial
  | d :: gds, σ, hb, hF, hR, h0 => by
    rw [List.map_cons] at hF
    obtain ⟨hv, hrest⟩ := hF
    simp only [mkPisAV, AnnotValid_pi]
    refine ⟨hv, fun x hx => ?_, fun hd x hx => ?_⟩
    · refine AnnotValid_mkPisAV_of (fun d' hd' => hb d' (List.mem_cons_of_mem _ hd'))
        (hrest x hx) (fun as hsp => ?_) (fun hw as hsp => ?_)
      · have := hR (x :: as) ⟨hx, hsp⟩
        rwa [consList_cons] at this
      · have := h0 hw (x :: as) ⟨hx, hsp⟩
        rwa [consList_cons] at this
    · have hw : w = 0 := (hb d List.mem_cons_self).mp hd
      refine interp_mkPisAV_mem_univZero
        (fun d' hd' => (hb d' (List.mem_cons_of_mem _ hd')).mpr hw) fun hnil => ?_
      subst hnil
      have := h0 hw [x] ⟨hx, trivial⟩
      simpa [consList] using this

/-- **A valid Π-tower's pieces**: the domains are valid along the
telescope, and the body is valid at every fitting spine. -/
theorem AnnotValid_mkPisAV_inv {R : AnnotTerm} :
    ∀ {gds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      AnnotValid V σ (mkPisAV gds R) →
      FieldsValid σ (gds.map (·.2.2)) ∧
      ∀ as, SpineFit σ (gds.map (·.2.2)) as → AnnotValid V (consList as σ) R
  | [], σ, h => ⟨trivial, fun as hsp => by
      cases as with
      | nil => simpa [mkPisAV, consList] using h
      | cons a as => exact hsp.elim⟩
  | d :: gds, σ, h => by
    simp only [mkPisAV, AnnotValid_pi] at h
    obtain ⟨hv, hB, -⟩ := h
    refine ⟨⟨hv, fun x hx => (AnnotValid_mkPisAV_inv (hB x hx)).1⟩, fun as hsp => ?_⟩
    cases as with
    | nil => exact hsp.elim
    | cons a as =>
      obtain ⟨ha, hsp'⟩ := hsp
      rw [consList_cons]
      exact (AnnotValid_mkPisAV_inv (hB a ha)).2 as hsp'

/-- The validity facts beside `ChainFacts`: at a recursive field the
telescope is valid along the shadow spine and the index expressions
are valid under every fitting telescope spine (task #202). -/
structure ChainValidFacts (nP nF : Nat) (ρp : Nat → V) (ks : List RecFieldKind)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Fs : List AnnotTerm) (Eis : List (List AnnotTerm))
    (Es : List AnnotTerm) : Prop where
  grV : ∀ i, i < nF → ∀ as' : List V, SpineFit ρp ((shadowFs nP ks nF Fs).take i) as' →
    AnnotValid V (consList as' ρp) (Fs.getD i default) ∧
    (recAt nP ks (nP + i) →
      FieldsValid (consList as' ρp) ((tls.getD i []).map (·.2.2)) ∧
      ∀ bs : List V, SpineFit (consList as' ρp) ((tls.getD i []).map (·.2.2)) bs →
        ∀ E ∈ Eis.getD i [], AnnotValid V (consList (as' ++ bs) ρp) E)
  grEV : ∀ as' : List V, SpineFit ρp (shadowFs nP ks nF Fs) as' →
    ∀ E ∈ Es, AnnotValid V (consList as' ρp) E

/-- The λ-tower over valid fields ending in a body valid at every
fitting spine is valid under the fields. -/
theorem underTowerValid_of_fields {b : AnnotTerm} {u : Nat} :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V}, FieldsValid ρ Fs →
      (∀ bs : List V, SpineFit ρ Fs bs → AnnotValid V (consList bs ρ) b) →
      UnderTowerValid ρ b (Fs.map fun F => (u, u, F))
  | [], ρ, _, hb => hb [] trivial
  | F :: Fs, ρ, hv, hb => by
    refine ⟨hv.1, fun a ha => ?_⟩
    exact underTowerValid_of_fields (hv.2 a ha) fun bs hsp => by
      have := hb (a :: bs) ⟨ha, hsp⟩
      simpa [consList_cons] using this

/-- The tupler is valid at a frame whose index telescope is valid. -/
theorem tuplerAV_validV (hI : IdxOk u ρp Ids) (hV : FieldsValid ρp Ids) :
    AnnotValid V ρp (tuplerAV u Ids) := by
  unfold tuplerAV
  apply mkLamsC_validV
  exact underTowerValid_of_fields hV fun bs hsp => mkTowerGo_validV hV (fun _ => hI.2) hsp

/-- **The validity walk** along the X-chain, beside a shadow spine. -/
theorem fixChainWalkValid (hI : IdxOk u ρp Ids) (hIV : FieldsValid ρp Ids) {X : V}
    (hX : X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids)) {t : V}
    (hC : ChainFacts u w nP nF ρp Ids ks tls Fs Eis Es) (hCV : ChainValidFacts nP nF ρp ks tls Fs Eis Es) :
    ∀ (m : Nat) (as as' : List V), nF - as.length = m → as.length ≤ nF →
      ShadowRel nP ks as as' → SpineFit ρp ((shadowFs nP ks nF Fs).take as.length) as' →
      FieldsValid (consList as (cons t (cons X ρp)))
        (chainXIGo u Ids (rsOf ks) tls Eis (Fs.drop as.length) as.length ++
          [idxEqAV (eqsXI Ids.length nF Es)]) := by
  intro m
  induction m with
  | zero =>
    intro as as' hm hle hrel hsp
    have hlen : as.length = nF := by omega
    have hdrop : Fs.drop as.length = [] := by rw [List.drop_eq_nil_iff, hC.hFs]; omega
    rw [hdrop]
    simp only [chainXIGo, List.nil_append, FieldsValid]
    have hspF : SpineFit ρp (shadowFs nP ks nF Fs) as' := by
      rwa [hlen, List.take_of_length_le (by rw [shadowFs_length]; exact Nat.le_refl _)] at hsp
    have hag := agreeOff_shadow hrel ρp
    rw [hlen] at hag
    refine ⟨idxEqAV_validV fun e he => ?_, fun _ _ => trivial⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
    have hl' : l < Ids.length := List.mem_range.mp hl
    have hEmem : Es.getD l default ∈ Es := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hC.hEs]; exact hl')]
      exact List.getElem_mem _
    constructor
    · show AnnotValid V _ ((Es.getD l default).liftN 2 nF)
      rw [← hlen, AnnotValid_liftN, shiftE_consList_len, show (2 : Nat) = 1 + 1 from rfl,
        shiftE_succ_cons, shiftE_succ_cons, shiftE_zero_zero]
      exact (AnnotValid_congr_noBVar _ (hC.nbEs _ hEmem) hag).mpr (hCV.grEV as' hspF _ hEmem)
    · show AnnotValid V _ (projAV l (.bvar nF))
      exact projAV_validV (by simp)
  | succ m ih =>
    intro as as' hm hle hrel hsp
    have hi : as.length < nF := by omega
    have hdrop : Fs.drop as.length = Fs.getD as.length default :: Fs.drop (as.length + 1) := by
      rw [List.drop_eq_getElem_cons (by rw [hC.hFs]; exact hi), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hC.hFs]; exact hi)]
      rfl
    rw [hdrop, chainXIGo_cons, List.cons_append]
    have hag := agreeOff_shadow hrel ρp
    obtain ⟨hok', hbnd', hrec'⟩ := hC.gr as.length hi as' hsp
    obtain ⟨hv', hrecV'⟩ := hCV.grV as.length hi as' hsp
    have hFnb := hC.nb as.length hi
    have hvF : interp V (consList as ρp) (Fs.getD as.length default)
        = interp V (consList as' ρp) (Fs.getD as.length default) :=
      interp_congr_noBVar _ hFnb hag
    have hnext : ∀ (a a' : V), (¬ recAt nP ks (nP + as.length) → a' = a) →
        a' ∈ˢ interp V (consList as' ρp)
          (if recAt nP ks (nP + as.length) then AnnotTerm.sort 0 else Fs.getD as.length default) →
        FieldsValid (consList (as ++ [a]) (cons t (cons X ρp)))
          (chainXIGo u Ids (rsOf ks) tls Eis (Fs.drop (as.length + 1)) (as.length + 1) ++
            [idxEqAV (eqsXI Ids.length nF Es)]) := by
      intro a a' ha ha'
      have h := ih (as ++ [a]) (as' ++ [a']) (by simp; omega) (by simp; omega)
        (ShadowRel.snoc hrel ha) (by
          rw [List.length_append, List.length_singleton, shadowFs_take_succ hi]
          exact SpineFit.append hsp ⟨ha', trivial⟩)
      simpa only [List.length_append, List.length_singleton] using h
    by_cases hr : recAt nP ks (nP + as.length)
    · have hrs : (rsOf ks).getD as.length false = true := by
        have h2 := hr.2
        rw [Nat.add_sub_cancel_left] at h2
        exact (rsOf_getD_iff (by rw [hC.hks]; exact hi)).mpr h2
      have hQ : ∀ q, (recAt nP ks q ∧ q < nP + as.length) → q < nP + as.length := fun _ h => h.2
      have hfit : SlotFit u w ρp Ids (tls.getD as.length []) (Eis.getD as.length []) as :=
        slotFit_congr_shadow hrel (hC.nbT as.length hi hr) (hC.nbE as.length hi hr) (hrec' hr)
      obtain ⟨hTv', hEv'⟩ := hrecV' hr
      have hT' : ∀ k F, ((tls.getD as.length []).map (·.2.2))[k]? = some F →
          NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + as.length) (nP + as.length + k)) F := by
        intro k F hk
        rw [List.getElem?_map] at hk
        obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hk
        exact hC.nbT as.length hi hr k d hd
      have hTv : FieldsValid (consList as ρp) ((tls.getD as.length []).map (·.2.2)) :=
        fieldsValid_congr_exclP _ hQ hag hT' hTv'
      have hEv : ∀ bs : List V, SpineFit (consList as ρp) ((tls.getD as.length []).map (·.2.2)) bs →
          ∀ E ∈ Eis.getD as.length [], AnnotValid V (consList (as ++ bs) ρp) E := by
        intro bs hsp E hE
        have hsp' := (spineFit_congr_exclP _ bs hQ hag hT').mp hsp
        have hlen : bs.length = (tls.getD as.length []).length := by
          rw [hsp.length_eq, List.length_map]
        have hag' : AgreeOff (exclP (fun q => recAt nP ks q ∧ q < nP + as.length)
            (nP + as.length + (tls.getD as.length []).length))
            (consList (as ++ bs) ρp) (consList (as' ++ bs) ρp) := by
          rw [consList_append, consList_append, ← hlen]
          exact agreeOff_exclP_consList bs hQ hag
        exact (AnnotValid_congr_noBVar E (hC.nbE as.length hi hr E hE) hag').mpr
          (hEv' bs hsp' E hE)
      have hx : xEntry u Ids (rsOf ks) tls Eis (Fs.getD as.length default) as.length
          = slotXI u Ids (tls.getD as.length []) (Eis.getD as.length []) as.length := by
        unfold xEntry; rw [if_pos hrs]
      rw [hx]
      refine ⟨?_, fun a ha => ?_⟩
      · unfold slotXI
        refine AnnotValid_mkPisAV_of (w := w) (fun d hd => ?_)
          (fieldsValid_liftTele2 t X _ as hTv) (fun bs hsp => ?_) (fun hw bs hsp => ?_)
        · obtain ⟨d', hd', he⟩ := mem_liftTele2 hd
          rw [he]; exact hfit.2.1 d' hd'
        · have hsp' := (spineFit_liftTele2 t X _ as bs).mp hsp
          have hlen : bs.length = (tls.getD as.length []).length := by
            rw [hsp'.length_eq, List.length_map]
          rw [← consList_append,
            show as.length + 1 + (tls.getD as.length []).length = (as ++ bs).length + 1 from by
              rw [List.length_append, hlen]; omega,
            show as.length + 2 + (tls.getD as.length []).length = (as ++ bs).length + 2 from by
              rw [List.length_append, hlen]; omega,
            show as.length + (tls.getD as.length []).length = (as ++ bs).length from by
              rw [List.length_append, hlen]]
          rw [AnnotValid_app]
          refine ⟨by simp, mkAppN_validV ?_ ?_⟩
          · rw [AnnotValid_liftN, shiftE_Xframe]
            exact tuplerAV_validV hI hIV
          · intro E' hE'
            obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hE'
            rw [AnnotValid_chainXI_ord]
            exact hEv bs hsp' E hE
        · have hsp' := (spineFit_liftTele2 t X _ as bs).mp hsp
          have hlen : bs.length = (tls.getD as.length []).length := by
            rw [hsp'.length_eq, List.length_map]
          obtain ⟨hEok, hspE⟩ := hfit.2.2 bs hsp'
          have h := recSlot_facts hI hX (as ++ bs) t hEok hspE
          rw [← consList_append,
            show as.length + 1 + (tls.getD as.length []).length = (as ++ bs).length + 1 from by
              rw [List.length_append, hlen]; omega,
            show as.length + 2 + (tls.getD as.length []).length = (as ++ bs).length + 2 from by
              rw [List.length_append, hlen]; omega,
            show as.length + (tls.getD as.length []).length = (as ++ bs).length from by
              rw [List.length_append, hlen], h.1]
          rw [hw, univ_zero] at h
          exact h.2.2
      · rw [consList_snoc']
        exact hnext a shadowVal (fun h => absurd hr h) (by rw [if_pos hr]; exact shadowVal_mem)
    · have hrs : (rsOf ks).getD as.length false = false := by
        have := rsOf_getD_iff (ks := ks) (i := as.length) (by rw [hC.hks]; exact hi)
        cases h : (rsOf ks).getD as.length false with
        | false => rfl
        | true =>
          exfalso
          apply hr
          refine ⟨Nat.le_add_right _ _, ?_⟩
          rw [Nat.add_sub_cancel_left]
          exact this.mp h
      have hx : xEntry u Ids (rsOf ks) tls Eis (Fs.getD as.length default) as.length
          = (Fs.getD as.length default).liftN 2 as.length := by
        unfold xEntry; rw [if_neg (by rw [hrs]; exact Bool.false_ne_true)]
      rw [hx]
      refine ⟨?_, fun a ha => ?_⟩
      · rw [AnnotValid_liftN, shiftE_consList_len, show (2 : Nat) = 1 + 1 from rfl,
          shiftE_succ_cons, shiftE_succ_cons, shiftE_zero_zero]
        exact (AnnotValid_congr_noBVar _ hFnb hag).mpr hv'
      · rw [consList_snoc']
        rw [interp_chainXI_ord, hvF] at ha
        exact hnext a a (fun _ => rfl) (by rw [if_neg hr]; exact ha)

/-- **The X-chain, valid**, from the walk at the empty spine. -/
theorem fixChainValid_of (hI : IdxOk u ρp Ids) (hIV : FieldsValid ρp Ids) {X : V}
    (hX : X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids)) {t : V}
    (hC : ChainFacts u w nP nF ρp Ids ks tls Fs Eis Es) (hCV : ChainValidFacts nP nF ρp ks tls Fs Eis Es) :
    FieldsValid (cons t (cons X ρp)) (chainXI u Ids Ids.length (rsOf ks) tls Eis Fs Es) := by
  have h := fixChainWalkValid hI hIV hX (t := t) hC hCV nF [] [] (by simp) (by simp)
    (ShadowRel.nil nP ks) trivial
  simp only [List.length_nil, List.drop_zero, consList_nil] at h
  rw [chainXI, hC.hFs]
  exact h

end Valid

/-! ## Closedness -/

section Below

variable {u w nP nIdx nF : Nat} {Ids Fs Es : List AnnotTerm} {rs : List Bool}
  {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)}

omit [SetTheory V] in
theorem domsBelow_tuplerData {k : Nat} :
    ∀ {Ids : List AnnotTerm}, FieldsBelow k Ids → DomsBelow k (Ids.map fun F => (u, u, F))
  | [], _ => trivial
  | _ :: _, h => ⟨h.1, domsBelow_tuplerData h.2⟩

omit [SetTheory V] in
theorem tuplerAV_below (hIds : FieldsBelow nP Ids) :
    Term.bvarsBelow nP (tuplerAV u Ids).erase := by
  unfold tuplerAV
  refine mkLamsC_below (domsBelow_tuplerData hIds) ?_
  rw [List.length_map]
  exact mkTowerGo_below hIds

omit [SetTheory V] in
/-- A field's telescope, lifted to the X-frame, is below it. -/
theorem domsBelow_liftTele2 {nP : Nat} :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (i : Nat), DomsBelow (nP + i) tl →
      DomsBelow (nP + 2 + i) (liftTele2 i tl)
  | [], _, _ => trivial
  | d :: tl, i, h => by
    rw [liftTele2_cons]
    refine ⟨?_, ?_⟩
    · rw [AnnotTerm.erase_liftN]
      have := VExprAux.bvarsBelow_liftN 2 d.2.2.erase (nP + i) i h.1
      rwa [show nP + i + 2 = nP + 2 + i from by omega] at this
    · have := domsBelow_liftTele2 tl (i + 1)
        (by rw [show nP + (i + 1) = nP + i + 1 from by omega]; exact h.2)
      rwa [show nP + 2 + (i + 1) = nP + 2 + i + 1 from by omega] at this

omit [SetTheory V] in
/-- The X-chain's entries from position `i` on, below the X-frame. -/
theorem chainXIGo_below (hIds : FieldsBelow nP Ids)
    (hTls : ∀ i, DomsBelow (nP + i) (tls.getD i []))
    (hEis : ∀ i, ∀ E ∈ Eis.getD i [],
      Term.bvarsBelow (nP + i + (tls.getD i []).length) E.erase) :
    ∀ (Fs : List AnnotTerm) (i : Nat), FieldsBelow (nP + i) Fs →
      FieldsBelow (nP + 2 + i) (chainXIGo u Ids rs tls Eis Fs i)
  | [], _, _ => trivial
  | F :: Fs, i, hF => by
    rw [chainXIGo_cons]
    refine ⟨?_, ?_⟩
    · unfold xEntry
      split
      · unfold slotXI
        refine mkPisAV_below_of (domsBelow_liftTele2 _ i (hTls i)) ?_
        rw [liftTele2_length]
        simp only [AnnotTerm.erase_app, AnnotTerm.erase_bvar, Term.bvarsBelow]
        refine ⟨by omega, ?_⟩
        rw [AnnotTerm.erase_mkAppN]
        refine VExprAux.bvarsBelow_mkAppN ?_ ?_
        · rw [AnnotTerm.erase_liftN]
          have := VExprAux.bvarsBelow_liftN (i + 2 + (tls.getD i []).length) (tuplerAV u Ids).erase
            nP 0 (tuplerAV_below (u := u) hIds)
          rwa [show nP + (i + 2 + (tls.getD i []).length) = nP + 2 + i + (tls.getD i []).length
            from by omega] at this
        · intro a ha
          rw [List.map_map] at ha
          obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
          simp only [Function.comp, AnnotTerm.erase_liftN]
          have := VExprAux.bvarsBelow_liftN 2 E.erase (nP + i + (tls.getD i []).length)
            (i + (tls.getD i []).length) (hEis i E hE)
          rwa [show nP + i + (tls.getD i []).length + 2 = nP + 2 + i + (tls.getD i []).length
            from by omega] at this
      · rw [AnnotTerm.erase_liftN]
        have := VExprAux.bvarsBelow_liftN 2 F.erase (nP + i) i hF.1
        rwa [show nP + i + 2 = nP + 2 + i from by omega] at this
    · have := chainXIGo_below hIds hTls hEis Fs (i + 1)
        (by rw [show nP + (i + 1) = nP + i + 1 from by omega]; exact hF.2)
      rwa [show nP + 2 + (i + 1) = nP + 2 + i + 1 from by omega] at this

omit [SetTheory V] in
/-- A constructor's X-chain, below the X-frame. -/
theorem chainXI_below (hIds : FieldsBelow nP Ids)
    (hTls : ∀ i, DomsBelow (nP + i) (tls.getD i []))
    (hEis : ∀ i, ∀ E ∈ Eis.getD i [],
      Term.bvarsBelow (nP + i + (tls.getD i []).length) E.erase)
    (hFs : FieldsBelow nP Fs) (hEsLen : Es.length = nIdx)
    (hEs : ∀ E ∈ Es, Term.bvarsBelow (nP + Fs.length) E.erase) :
    FieldsBelow (nP + 2) (chainXI u Ids nIdx rs tls Eis Fs Es) := by
  unfold chainXI
  refine FieldsBelow_append_idxEq
    (by simpa using chainXIGo_below hIds hTls hEis Fs 0 (by simpa using hFs))
    ?_
  intro e he
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
  have hl' : l < nIdx := List.mem_range.mp hl
  rw [chainXIGo_length]
  have hmem : Es.getD l default ∈ Es := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hEsLen]; exact hl')]
    exact List.getElem_mem _
  constructor
  · show Term.bvarsBelow _ ((Es.getD l default).liftN 2 Fs.length).erase
    rw [AnnotTerm.erase_liftN]
    have := VExprAux.bvarsBelow_liftN 2 (Es.getD l default).erase (nP + Fs.length) Fs.length
      (hEs _ hmem)
    rwa [show nP + Fs.length + 2 = nP + 2 + Fs.length from by omega] at this
  · show Term.bvarsBelow _ (projAV l (.bvar Fs.length)).erase
    exact projAV_below (by simp [Term.bvarsBelow])

omit [SetTheory V] in
/-- The functor's λ, below the parameter frame. -/
theorem fixBodyAVI_below {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {Fss Ess : List (List AnnotTerm)} (hIds : FieldsBelow nP Ids)
    (hchains : ∀ chain ∈ chainsXI u Ids nIdx rss tlss Eiss Fss Ess, FieldsBelow (nP + 2) chain) :
    Term.bvarsBelow nP (fixBodyAVI u w Ids nIdx rss tlss Eiss Fss Ess).erase := by
  unfold fixBodyAVI
  rw [AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN (by simp [Term.bvarsBelow]) ?_
  intro a ha
  simp only [List.map_cons, List.map_nil, List.mem_cons] at ha
  rcases ha with rfl | rfl | h
  · exact towerBodyAV_below hIds
  · unfold fixFunAVI famTyAV
    simp only [AnnotTerm.erase_lam, AnnotTerm.erase_pi, AnnotTerm.erase_sort, Term.bvarsBelow]
    refine ⟨⟨towerBodyAV_below hIds, trivial⟩, ?_, ?_⟩
    · rw [AnnotTerm.erase_liftN]
      exact VExprAux.bvarsBelow_liftN 1 (towerBodyAV u Ids).erase nP 0 (towerBodyAV_below hIds)
    · exact sumBodyAV_below hchains
  · exact nomatch h

omit [SetTheory V] in
/-- **The former's leaf is closed.** -/
theorem nativeTyAVI_below {pps : List (Nat × Nat × AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {Fss Ess : List (List AnnotTerm)}
    (hp : DomsBelow 0 pps) (hlen : pps.length = nP + nIdx)
    (hIdsLen : (((pps.drop nP).map (·.2.2))).length = nIdx)
    (hchains : ∀ chain ∈ chainsXI u Ids nIdx rss tlss Eiss Fss Ess, FieldsBelow (nP + 2) chain)
    (hIds : Ids = (pps.drop nP).map (·.2.2)) :
    Term.bvarsBelow 0 (nativeTyAVI u w pps Ids rss tlss Eiss Fss Ess).erase := by
  have hIdsB : FieldsBelow nP Ids := by
    rw [hIds]
    have := (DomsBelow.drop nP hp).fields
    rwa [Nat.zero_add] at this
  have hIL : Ids.length = nIdx := by rw [hIds]; exact hIdsLen
  refine mkLamsAV_below hp.mapC ?_
  rw [List.length_map, hlen, Nat.zero_add]
  simp only [AnnotTerm.erase_app, Term.bvarsBelow]
  refine ⟨?_, ?_⟩
  · rw [AnnotTerm.erase_liftN]
    have := VExprAux.bvarsBelow_liftN Ids.length
      (fixBodyAVI u w Ids Ids.length rss tlss Eiss Fss Ess).erase nP 0
      (fixBodyAVI_below (w := w) (nIdx := Ids.length) hIdsB (by rw [hIL]; exact hchains))
    rw [hIL] at this ⊢
    exact this
  · have := mkTowerGo_below (w := u) hIdsB
    rwa [hIL] at this

end Below

/-! ## The leaf's currency -/

section Currency

variable {u w nP : Nat} {Ids : List AnnotTerm} {rss : List (List Bool)}
  {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {Fss Ess : List (List AnnotTerm)}

/-- The body's validity at the frame below the parameters and the
index variables. -/
theorem fixBody_validV {ρp : Nat → V} (hI : IdxOk u ρp Ids) (hIV : FieldsValid ρp Ids)
    (hchains : ∀ X, X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids) → ∀ t, t ∈ˢ idxSet u ρp Ids →
      SumFieldsValid (cons t (cons X ρp)) (chainsXI u Ids Ids.length rss tlss Eiss Fss Ess))
    {is : List V} (hsp : SpineFit ρp Ids is) :
    AnnotValid V (consList is ρp)
      (.app ((fixBodyAVI u w Ids Ids.length rss tlss Eiss Fss Ess).liftN Ids.length 0)
        (mkTowerGo u Ids)) := by
  have hsh : shiftE Ids.length 0 (consList is ρp) = ρp := by
    rw [← hsp.length_eq]; exact shiftE_consList is ρp
  rw [AnnotValid_app]
  refine ⟨?_, mkTowerGo_validV hIV (fun _ => hI.2) hsp⟩
  rw [AnnotValid_liftN, hsh]
  unfold fixBodyAVI
  refine mkAppN_validV (by simp) ?_
  intro a ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl | rfl | h
  · exact towerBodyAV_validV hIV
  · unfold fixFunAVI
    rw [AnnotValid_lam]
    refine ⟨?_, fun X hX => ?_⟩
    · unfold famTyAV
      rw [AnnotValid_pi]
      exact ⟨towerBodyAV_validV hIV, fun _ _ => trivial, fun h => absurd h (Nat.succ_ne_zero _)⟩
    · rw [(famTyAV_facts hI).1] at hX
      rw [AnnotValid_lam]
      have hsh1 : shiftE 1 0 (cons X ρp) = ρp := by
        rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
      refine ⟨?_, fun t ht => ?_⟩
      · rw [AnnotValid_liftN, hsh1]; exact towerBodyAV_validV hIV
      · rw [interp_liftN, hsh1, (idxTyAV_facts hI).1] at ht
        exact sumBodyAV_validV (hchains X hX t ht)
  · exact nomatch h

/-- **The former leaf's P currency**: graded at the hereditary premise,
valid under the tower. -/
theorem nativeTyAVI_wellDenotedV {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}
    (hok : ParamsOkXI u w ρ Ids rss tlss Eiss Fss Ess pps)
    (hval : UnderTowerValid ρ
      (.app ((fixBodyAVI u w Ids Ids.length rss tlss Eiss Fss Ess).liftN Ids.length 0)
        (mkTowerGo u Ids)) pps) :
    WellDenotedV V ρ (nativeTyAVI u w pps Ids rss tlss Eiss Fss Ess) :=
  ⟨nativeTyAVI_wellDenoted hok, mkLamsC_validV (m := w + 1) hval⟩

end Currency

end ConLeche.Model
