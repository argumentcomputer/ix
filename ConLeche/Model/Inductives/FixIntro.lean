module

public import ConLeche.Model.Inductives.SumIntro
public import ConLeche.Semantics.Tower.FixRecI

public section

/-!
# The recursive recursor leaf's bit validity (task #188)

The sum route's validity kit (`SumIntroP.lean`) extended by the
inductive-hypothesis arguments of the case split
(`caseRecAVI`, `ConLeche/Semantics/Tower/FixCaseI.lean`): an ih argument
applies the unfolded function to the block's variables, the field's
index expressions moved to the payload frame (`substProj`) and the
payload's projection; its validity is the index expressions' at the
projections — which fit the constructor's fields.  Then the recursor
body, the one-step unfolding, the fixed-point sigma and the selected
fixed point (`fixSelAVI`) are valid.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Substitution of the payload's projections -/

/-- `substProjAt` under binders preserves bit validity. -/
theorem AnnotValid_substProjAt (σ : Nat → V) (y : V) (bs : List V) :
    ∀ (i : Nat) (e : AnnotTerm),
      AnnotValid V (consList bs (cons y σ)) (substProjAt bs.length i e) ↔
        AnnotValid V (consList bs (consList (projList i y) (cons y σ))) e
  | 0, _ => Iff.rfl
  | i + 1, e => by
    show AnnotValid V (consList bs (cons y σ))
      (substProjAt bs.length i (e.inst (projAV i (.bvar i)) bs.length)) ↔ _
    have hp : AnnotValid V (shiftE bs.length 0 (consList bs (consList (projList i y) (cons y σ))))
        (projAV i (.bvar i)) := by
      rw [shiftE_consList]
      exact projAV_validV (by rw [AnnotValid_bvar]; trivial)
    rw [AnnotValid_substProjAt σ y bs i, AnnotValid_inst V _ _ _ _ hp, shiftE_consList, projAV_interp,
      interp_bvar]
    have hy : consList (projList i y) (cons y σ) i = y := by
      have := consList_apply_add (projList i y) (cons y σ) 0
      rwa [Nat.zero_add, projList_length] at this
    rw [hy, instE_consList', consList_snoc', ← projList_snoc]

/-- `UnderTowerValid` from the domains' validity and the leaf's at
every fitting spine. -/
theorem underTowerValid_of_fieldsValid {b : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      FieldsValid ρ (ds.map (·.2.2)) →
      (∀ as, SpineFit ρ (ds.map (·.2.2)) as → AnnotValid V (consList as ρ) b) →
      UnderTowerValid ρ b ds
  | [], ρ, _, hb => by
    show AnnotValid V ρ b
    simpa using hb [] trivial
  | d :: ds, ρ, hv, hb => by
    rw [List.map_cons] at hv
    refine ⟨hv.1, fun a ha => underTowerValid_of_fieldsValid (hv.2 a ha) fun as hsp => ?_⟩
    have := hb (a :: as) ⟨ha, hsp⟩
    rwa [consList_cons] at this

/-! ## The ih arguments -/

section IhValid

variable {ℓ w nP : Nat} {ρ₀ σ : Nat → V} {Fss Ess : List (List AnnotTerm)} {Ids : List AnnotTerm}
  {famAt : List V → V} {ihDoms : Nat → List V → List V} {rss : List (List Bool)}
  {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {D : Nat}

/-- The payload of constructor `j`'s fibre projects to a fitting field
spine at the parameter frame. -/
theorem fibre_projList_fit (hyp : RecHypI ℓ w ρ₀ Fss Ess Ids famAt ihDoms) (hw : w ≠ 0)
    {j : Nat} (hj : j < Fss.length) {y : V}
    (hy : y ∈ˢ sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess) j) :
    SpineFit (frP Fss.length Ids.length ρ₀) (Fss.getD j []) (projList (Fss.getD j []).length y) := by
  have hjF := hyp.rChain_getElem? hj
  rw [sumFibre_of_getElem? hjF] at hy
  have helim := restricted_member_elim hw
    (Fs := liftFields (Ids.length + Fss.length + 1) 0 (Fss.getD j []))
    (eqs := idxEqsAt (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []).length (Ess.getD j []))
    (ρ := ρ₀) (y := y) hy
  rw [liftFields_length] at helim
  exact (spineFit_liftFields (Ids.length + Fss.length + 1)).mp helim.1

/-- A field's index expression moved under telescope binders at the
payload frame is valid exactly when it is at the field's own frame. -/
theorem ihIdxM_validV (hfr : RecFrameS D ρ₀ σ) (y : V) (i : Nat) (bs : List V) (E : AnnotTerm) :
    AnnotValid V (consList bs (cons y σ))
        (substProjAt bs.length i (E.liftN (D + Ids.length + Fss.length + 2) (i + bs.length))) ↔
      AnnotValid V (consList bs (consList (projList i y) (frP Fss.length Ids.length ρ₀))) E := by
  rw [AnnotValid_substProjAt, AnnotValid_liftN, ← consList_append,
    show i + bs.length = (projList i y ++ bs).length from by rw [List.length_append, projList_length],
    shiftE_consList_len, shiftE_payload hfr, consList_append]

/-- The moved telescope's validity at the payload frame. -/
theorem fieldsValid_ihTeleAtGoP (hfr : RecFrameS D ρ₀ σ) (y : V) (i : Nat) :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (as : List V),
      FieldsValid (consList as (consList (projList i y) (frP Fss.length Ids.length ρ₀))) (tl.map (·.2.2)) →
      FieldsValid (consList as (cons y σ)) ((ihTeleAtGoP Ids.length Fss.length D i as.length tl).map (·.2.2))
  | [], _, _ => trivial
  | d :: tl, as, hF => by
    show FieldsValid _ (substProjAt as.length i (d.2.2.liftN (D + Ids.length + Fss.length + 2) (i + as.length)) ::
      (ihTeleAtGoP Ids.length Fss.length D i (as.length + 1) tl).map (·.2.2))
    rw [List.map_cons] at hF
    obtain ⟨hv, hrest⟩ := hF
    refine ⟨(ihIdxM_validV hfr y i as _).mpr hv, fun a ha => ?_⟩
    rw [ihIdxM_interp hfr y i as] at ha
    rw [consList_snoc']
    have := fieldsValid_ihTeleAtGoP hfr y i tl (as ++ [a]) (by rw [← consList_snoc']; exact hrest a ha)
    rw [length_snoc'] at this
    exact this

theorem fieldsValid_ihTeleAt (hfr : RecFrameS D ρ₀ σ) (y : V) (i : Nat) (tl : List (Nat × Nat × AnnotTerm))
    (h : FieldsValid (consList (projList i y) (frP Fss.length Ids.length ρ₀)) (tl.map (·.2.2))) :
    FieldsValid (cons y σ) ((ihTeleAt Ids.length Fss.length D i tl).map (·.2.2)) := by
  rw [ihTeleAt_eq_go]
  have := fieldsValid_ihTeleAtGoP hfr y i tl [] (by simpa using h)
  simpa using this

/-- **The ih arguments are bit-valid** at a payload of the
constructor's fibre: λ-towers over the moved telescopes (valid at the
fitting projections) whose leaves apply the function at the block, the
index expressions (valid under the telescope) and the field. -/
theorem ihArgsI_validV (hyp : RecHypI ℓ w ρ₀ Fss Ess Ids famAt ihDoms) (hw : w ≠ 0)
    (hfr : RecFrameS D ρ₀ σ) {j : Nat} (hj : j < Fss.length)
    (hEV : ∀ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length, ∀ fs : List V,
      SpineFit (frP Fss.length Ids.length ρ₀) (Fss.getD j []) fs →
      FieldsValid (consList (fs.take i) (frP Fss.length Ids.length ρ₀))
        (((tlss.getD j []).getD i []).map (·.2.2)) ∧
      ∀ bs : List V, SpineFit (consList (fs.take i) (frP Fss.length Ids.length ρ₀))
        (((tlss.getD j []).getD i []).map (·.2.2)) bs →
      ∀ E ∈ (Eiss.getD j []).getD i [],
        AnnotValid V (consList bs (consList (fs.take i) (frP Fss.length Ids.length ρ₀))) E)
    {y : V} (hy : y ∈ˢ sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess) j) :
    ∀ a ∈ ihArgsI ℓ nP Fss.length Ids.length rss tlss Eiss (fun j => (Fss.getD j []).length) D j,
      AnnotValid V (cons y σ) a := by
  have hspP := fibre_projList_fit hyp hw hj hy
  intro a ha
  unfold ihArgsI at ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hik, -⟩ := mem_recIdx.mp hi
  obtain ⟨hTV, hEV'⟩ := hEV i hi _ hspP
  rw [projList_take _ _ _ (Nat.le_of_lt hik)] at hTV hEV'
  rw [ihArgAV_eq]
  refine mkLamsC_validV (underTowerValid_of_fieldsValid (fieldsValid_ihTeleAt hfr y i _ hTV)
    fun bs hbs => ?_)
  have hbs' := (spineFit_ihTeleAt hfr y i _ bs).mp hbs
  have hlenbs : bs.length = ((tlss.getD j []).getD i []).length := by
    rw [hbs'.length_eq, List.length_map]
  unfold ihArgBody
  rw [← hlenbs]
  refine mkAppN_validV trivial fun a ha => ?_
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at ha
  rcases ha with (ha | ⟨E, hE, rfl⟩) | rfl
  · obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha
    trivial
  · exact (ihIdxM_validV hfr y i bs E).mpr (hEV' bs hbs' E hE)
  · refine mkAppN_validV (projAV_validV trivial) fun a ha => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
    trivial

/-- Constructor `j`'s branch with ih arguments is bit-valid. -/
theorem fixBase_validV (hyp : RecHypI ℓ w ρ₀ Fss Ess Ids famAt ihDoms) (hw : w ≠ 0)
    (hfr : RecFrameS D ρ₀ σ)
    (hv : SumFieldsValid ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
    (hEV : ∀ j, j < Fss.length → ∀ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length,
      ∀ fs : List V, SpineFit (frP Fss.length Ids.length ρ₀) (Fss.getD j []) fs →
      FieldsValid (consList (fs.take i) (frP Fss.length Ids.length ρ₀))
        (((tlss.getD j []).getD i []).map (·.2.2)) ∧
      ∀ bs : List V, SpineFit (consList (fs.take i) (frP Fss.length Ids.length ρ₀))
        (((tlss.getD j []).getD i []).map (·.2.2)) bs →
      ∀ E ∈ (Eiss.getD j []).getD i [],
        AnnotValid V (consList bs (consList (fs.take i) (frP Fss.length Ids.length ρ₀))) E)
    (j : Nat) :
    AnnotValid V σ
      (caseBaseAVI ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
        (fun j => (Fss.getD j []).length)
        (ihArgsI ℓ nP Fss.length Ids.length rss tlss Eiss (fun j => (Fss.getD j []).length))
        Fss.length Ids.length D j) := by
  show AnnotValid V σ (.lam ℓ _ _)
  rw [AnnotValid_lam]
  refine ⟨?_, fun y hy => ?_⟩
  · rw [AnnotValid_liftN, hfr]
    by_cases hj : j < (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess).length
    · have hjF : (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)[j]?
          = some ((rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess).getD j []) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
      exact towerBodyAV_validV (hv _ (List.mem_of_getElem? hjF))
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      exact towerBodyAV_validV trivial
  · refine mkAppN_validV trivial fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
      exact projAV_validV trivial
    · by_cases hj : j < Fss.length
      · -- the payload is in the fibre
        have hjF := hyp.rChain_getElem? hj
        have hokF : FieldsOkB w ρ₀
            (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j [])) :=
          hyp.hok _ (List.mem_of_getElem? hjF)
        have hy' : y ∈ˢ sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess) j := by
          rw [sumFibre_of_getElem? hjF]
          rw [interp_liftN, hfr, List.getD_eq_getElem?_getD, hjF, Option.getD_some,
            towerBodyAV_interp (hokF.toBound)] at hy
          exact hy
        exact ihArgsI_validV hyp hw hfr hj (hEV j hj) hy' a ha
      · -- no ih arguments at a stage past the constructors
        exfalso
        have h0 : (Fss.getD j []).length = 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
        unfold ihArgsI at ha
        simp only [h0, recIdx, List.range_zero, List.filter_nil, List.map_nil] at ha
        exact (List.not_mem_nil ha).elim

/-- **The case recursor with ih arguments is bit-valid.** -/
theorem fixCaseRec_validV (hyp : RecHypI ℓ w ρ₀ Fss Ess Ids famAt ihDoms) (hw : w ≠ 0)
    (hv : SumFieldsValid ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
    (hEV : ∀ j, j < Fss.length → ∀ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length,
      ∀ fs : List V, SpineFit (frP Fss.length Ids.length ρ₀) (Fss.getD j []) fs →
      FieldsValid (consList (fs.take i) (frP Fss.length Ids.length ρ₀))
        (((tlss.getD j []).getD i []).map (·.2.2)) ∧
      ∀ bs : List V, SpineFit (consList (fs.take i) (frP Fss.length Ids.length ρ₀))
        (((tlss.getD j []).getD i []).map (·.2.2)) bs →
      ∀ E ∈ (Eiss.getD j []).getD i [],
        AnnotValid V (consList bs (consList (fs.take i) (frP Fss.length Ids.length ρ₀))) E) :
    ∀ (r : Nat) {D j : Nat} {σ : Nat → V} {kx : AnnotTerm},
      RecFrameS D ρ₀ σ → AnnotValid V σ kx →
      AnnotValid V σ
        (caseRecAVI ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
          (fun j => (Fss.getD j []).length)
          (ihArgsI ℓ nP Fss.length Ids.length rss tlss Eiss (fun j => (Fss.getD j []).length))
          Fss.length Ids.length r D j kx)
  | 0, _, _, σ, _, _, _ => by
    show AnnotValid V σ (.lam ℓ (.const .empty [w]) .prf)
    rw [AnnotValid_lam]
    exact ⟨trivial, fun _ _ => trivial⟩
  | r + 1, D, j, σ, kx, hfr, hk => by
    refine natRecAV_validV (motive_validV hfr hyp.toRecHypCore hv j)
      (fixBase_validV hyp hw hfr hv hEV j) ?_ hk
    rw [AnnotValid_lam]
    refine ⟨trivial, fun b _ => ?_⟩
    rw [AnnotValid_lam]
    refine ⟨motiveBody_validV hfr hyp.toRecHypCore hv j b, fun a _ => ?_⟩
    exact fixCaseRec_validV hyp hw hv hEV r (hfr.step a b) trivial

/-- **The recursor body is bit-valid** at the frame under the K-frame,
all three regimes (the squash regime's body by `hsq`, task #202 A2). -/
theorem fixRecBody_validV (hfr : RecFrameS 1 ρ₀ σ) (hyp : RecHypI ℓ w ρ₀ Fss Ess Ids famAt ihDoms)
    (hv : SumFieldsValid ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
    (hEV : w ≠ 0 → ∀ j, j < Fss.length → ∀ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length,
      ∀ fs : List V, SpineFit (frP Fss.length Ids.length ρ₀) (Fss.getD j []) fs →
      FieldsValid (consList (fs.take i) (frP Fss.length Ids.length ρ₀))
        (((tlss.getD j []).getD i []).map (·.2.2)) ∧
      ∀ bs : List V, SpineFit (consList (fs.take i) (frP Fss.length Ids.length ρ₀))
        (((tlss.getD j []).getD i []).map (·.2.2)) bs →
      ∀ E ∈ (Eiss.getD j []).getD i [],
        AnnotValid V (consList bs (consList (fs.take i) (frP Fss.length Ids.length ρ₀))) E)
    (hsq : w = 0 → ℓ ≠ 0 → AnnotValid V σ
      (sqFixBodyAV ℓ nP Fss.length Ids.length (Fss.getD 0 []) (Ess.getD 0 []) (rss.getD 0 [])
        (tlss.getD 0 []) (Eiss.getD 0 []))) :
    AnnotValid V σ (fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss) := by
  by_cases hw : w = 0
  · subst hw
    by_cases hℓ : ℓ = 0
    · rw [fixRecBodyAVI_zero hℓ]
      trivial
    · rw [fixRecBodyAVI_sq hℓ]
      exact hsq rfl hℓ
  · rw [fixRecBodyAVI_pos hw, AnnotValid_app]
    exact ⟨fixCaseRec_validV hyp hw hv (hEV hw) Fss.length hfr (major_fst_validV σ),
      major_snd_validV σ⟩

/-! ## The ih-moved telescopes' validity (task #202) -/

theorem AnnotValid_ihIdxAtM {nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i ≤ nF) (as : List V) (E : AnnotTerm) :
    AnnotValid V (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
        (ihIdxAtM nF o i l as.length E) ↔
      AnnotValid V (consList as (consList (fs.take i) ρp)) E := by
  unfold ihIdxAtM
  rw [AnnotValid_liftN, show nF + l + as.length = as.length + (fs.length + ihs.length) from by omega,
    shiftE_consList_len', shiftE_fieldFrame hms, AnnotValid_liftN, shiftE_consList_len,
    ← consList_append]
  have hsplit : fs ++ ihs = fs.take i ++ (fs.drop i ++ ihs) := by
    rw [← List.append_assoc, List.take_append_drop]
  rw [hsplit, consList_append, show nF - i + l = (fs.drop i ++ ihs).length from by
    rw [List.length_append, List.length_drop]; omega, shiftE_consList]

/-- The telescope's validity moved to the ih frame. -/
theorem fieldsValid_ihTeleAtGo {nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i ≤ nF) :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (as : List V),
      FieldsValid (consList as (consList (fs.take i) ρp)) (tl.map (·.2.2)) →
      FieldsValid (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
        ((ihTeleAtGo nF o i l as.length tl).map (·.2.2))
  | [], _, _ => trivial
  | d :: tl, as, hF => by
    show FieldsValid _ (ihIdxAtM nF o i l as.length d.2.2 ::
      (ihTeleAtGo nF o i l (as.length + 1) tl).map (·.2.2))
    rw [List.map_cons] at hF
    obtain ⟨hv, hrest⟩ := hF
    refine ⟨(AnnotValid_ihIdxAtM hms hfs hihs hi as _).mpr hv, fun a ha => ?_⟩
    rw [interp_ihIdxAtM hms hfs hihs hi] at ha
    rw [consList_snoc']
    have := fieldsValid_ihTeleAtGo (M := M) (ρp := ρp) hms hfs hihs hi tl (as ++ [a])
      (by rw [← consList_snoc']; exact hrest a ha)
    rw [length_snoc'] at this
    exact this

/-- **The squash regime's body is bit-valid** at a K-frame (task #202
A2): the constructor's field telescope lifted under the frame, the
minor at the fields and the ih applications (their telescopes and
index expressions moved to the ih frame), the sources. -/
theorem sqFixBodyAV_validV {ℓ nP n nIdx : Nat} {Fs Es : List AnnotTerm} {rs : List Bool}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)}
    {ρp : Nat → V} {M t : V} {ms is : List V} (hlenM : ms.length = n) (hlenI : is.length = nIdx)
    (hFv : FieldsValid ρp Fs)
    (hTV : ∀ i ∈ recIdx rs Fs.length, ∀ fs : List V, SpineFit ρp Fs fs →
      FieldsValid (consList (fs.take i) ρp) ((tls.getD i []).map (·.2.2)))
    (hEV : ∀ i ∈ recIdx rs Fs.length, ∀ fs : List V, SpineFit ρp Fs fs →
      ∀ bs : List V, SpineFit (consList (fs.take i) ρp) ((tls.getD i []).map (·.2.2)) bs →
      ∀ E ∈ Eis.getD i [], AnnotValid V (consList bs (consList (fs.take i) ρp)) E) :
    AnnotValid V (cons t (consList is (consList ms (cons M ρp))))
      (sqFixBodyAV ℓ nP n nIdx Fs Es rs tls Eis) := by
  have hσ : cons t (consList is (consList ms (cons M ρp)))
      = consList (ms ++ is ++ [t]) (cons M ρp) := by
    rw [List.append_assoc, consList_append, consList_snoc']
  have hlen' : (ms ++ is ++ [t]).length + 1 = n + 1 + (nIdx + 1) := by
    simp [hlenM, hlenI]; omega
  have hsh : shiftE (nIdx + n + 2) 0 (consList (ms ++ is ++ [t]) (cons M ρp)) = ρp := by
    rw [show nIdx + n + 2 = (ms ++ is ++ [t]).length + 1 from by omega, shiftE_consList_add,
      shiftE_succ_cons, shiftE_zero_zero]
  rw [hσ]
  unfold sqFixBodyAV
  refine mkAppN_validV ?_ fun a ha => ?_
  · refine mkLamsC_validV ?_
    unfold fieldTeleAt
    refine underTowerValid_of_fieldsValid ?_ ?_
    · have hmap : ((liftFields (nIdx + n + 2) 0 Fs).map fun F => (0, 0, F)).map (·.2.2)
          = liftFields (nIdx + n + 2) 0 Fs := by
        rw [List.map_map]; exact List.map_id'' (fun _ => rfl) _
      rw [hmap, FieldsValid_liftFields, hsh]
      exact hFv
    · intro fs hfit
      rw [List.map_map, show ((fun x : Nat × Nat × AnnotTerm => x.2.2) ∘ fun F : AnnotTerm => (0, 0, F)) = id
        from rfl, List.map_id, spineFit_liftFields, hsh] at hfit
      have hlenF : fs.length = Fs.length := hfit.length_eq
      refine mkAppN_validV trivial fun a ha => ?_
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha
        trivial
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
        obtain ⟨hik, -⟩ := mem_recIdx.mp hi
        unfold ihAppAVb
        refine mkLamsC_validV (underTowerValid_of_fieldsValid ?_ ?_)
        · have := fieldsValid_ihTeleAtGo (o := n + 1 + (nIdx + 1)) (M := M) (ρp := ρp)
            (ms := ms ++ is ++ [t]) hlen' hlenF (ihs := []) rfl (Nat.le_of_lt hik) (tls.getD i []) []
            (hTV i hi fs hfit)
          simp only [consList_nil, List.length_nil] at this
          exact this
        · intro bs hbs
          have hbs' : SpineFit (consList (fs.take i) ρp) ((tls.getD i []).map (·.2.2)) bs := by
            have := (spineFit_ihTeleAtGo (o := n + 1 + (nIdx + 1)) (M := M) (ρp := ρp)
              (ms := ms ++ is ++ [t]) hlen' hlenF (ihs := []) rfl (Nat.le_of_lt hik) (tls.getD i [])
              [] bs).mp (by simp only [consList_nil, List.length_nil]; exact hbs)
            simpa using this
          have hlenbs : bs.length = (tls.getD i []).length := by
            rw [hbs.length_eq, List.length_map, ihTeleAtR_length]
          refine mkAppN_validV trivial fun a ha => ?_
          rcases List.mem_append.mp ha with ha | ha
          · rcases List.mem_append.mp ha with ha | ha
            · unfold prefixVarsAV at ha
              rcases List.mem_append.mp ha with ha | ha
              · rcases List.mem_append.mp ha with ha | ha
                · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; trivial
                · rw [List.mem_singleton] at ha; subst ha; trivial
              · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; trivial
            · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
              rw [← hlenbs]
              have := (AnnotValid_ihIdxAtM (o := n + 1 + (nIdx + 1)) (M := M) (ρp := ρp)
                (ms := ms ++ is ++ [t]) hlen' hlenF (ihs := []) rfl (Nat.le_of_lt hik) bs E).mpr
                (hEV i hi fs hfit bs hbs' E hE)
              simp only [consList_nil] at this
              exact this
          · rw [List.mem_singleton] at ha
            subst ha
            refine mkAppN_validV trivial fun a ha => ?_
            obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha
            trivial
  · obtain ⟨s', -, rfl⟩ := List.mem_map.mp ha
    exact srcAV_validV _ _ _ _

end IhValid

/-! ## The leaf -/

/-- **The recursor leaf is bit-valid**: from the type's validity and the
body's validity under the binder data over every function value. -/
theorem fixSelAVI_validV {ℓ w nP s : Nat} {Fss Ess : List (List AnnotTerm)} {Ids : List AnnotTerm}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {rds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}
    (hTy : AnnotValid V ρ (recTyAV Fss.length Ids.length rds))
    (hbody : ∀ r : V, r ∈ˢ interp V ρ (recTyAV Fss.length Ids.length rds) →
      UnderTowerValid (cons r ρ) (fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss) rds) :
    AnnotValid V ρ (fixSelAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s) := by
  have hstep : AnnotValid V ρ (fixStepAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s) := by
    show AnnotValid V ρ (.lam s (recTyAV Fss.length Ids.length rds) _)
    rw [AnnotValid_lam]
    exact ⟨hTy, fun r hr => mkLamsC_validV (hbody r hr)⟩
  have hsig : AnnotValid V ρ (fixSigAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s) := by
    show AnnotValid V ρ (.app (.app (.const .psigma [s, 0]) (recTyAV Fss.length Ids.length rds))
      (.lam 1 (recTyAV Fss.length Ids.length rds) _))
    simp only [AnnotValid_app, AnnotValid_const, AnnotValid_lam, AnnotValid_eqE,
      AnnotValid_bvar, and_true, true_and]
    refine ⟨hTy, hTy, fun r _ => ?_⟩
    rw [AnnotValid_liftN, shiftE_succ_cons, shiftE_zero_zero]
    exact hstep
  show AnnotValid V ρ (.fst (.app (.app (.const .choice [s]) _) .prf))
  simp only [AnnotValid_fst, AnnotValid_app, AnnotValid_const, AnnotValid_prf, and_true,
    true_and]
  exact hsig

end ConLeche.Model
