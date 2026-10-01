module

public import ConLeche.Semantics.Tower.FixRecCoreI
public import ConLeche.SetModel.RecGraph

@[expose] public section

/-!
# The recursive squash regime's large eliminator (task #202, Stage A2)

At `w = 0` the family's fibres are truth values and the sole proof is
the point; with a large eliminator (`ℓ ≠ 0`) the recursor cannot case
on the major.  The block has ONE constructor whose data fields are
index expressions (the subsingleton criterion), so at a tuple `t` the
constructor's spine is READ OFF THE INDICES (`sqSpine`: the sum route's
`srcVals`), and the recursor's value is determined by the recursion
equation `R t = m (spine t) (ih⃗ from R at the predecessors)`.  The
value is the unique element of the recursor's GRAPH (`sqGraph`, the
least fixed point of `recGraphStep`, `ConLeche/SetModel/RecGraph`) —
singleton at every tuple of the family, by lfp induction on the
family's functor (`sqGraph_singleton`).
-/

namespace ConLeche.Semantics
open ConLeche.SetModel ConLeche.SetTheory
open SetTheory ConLeche.SetTheory.Tower

universe w'

variable {V : Type w'} [SetTheory V]

/-! ## The ih frame, read -/

omit [SetTheory V] in
/-- The field frame over a K-frame: `l` ih values over the `nF`
fields over the `o - 1` minors and the motive over the parameter
frame.  The frame `o` below the fields is the parameter frame. -/
theorem shiftE_fieldFrame {o : Nat} {ρp : Nat → V} {M : V} {ms : List V} (hms : ms.length + 1 = o)
    (fs ihs : List V) :
    shiftE o (fs.length + ihs.length) (consList ihs (consList fs (consList ms (cons M ρp)))) = consList ihs (consList fs ρp) := by
  rw [← consList_append, ← List.length_append, shiftE_consList_len, ← hms,
    shiftE_consList_add, shiftE_succ_cons, shiftE_zero_zero, consList_append]

/-- `ihIdxAtM` under `as` telescope values reads the field's
expression at the field's own frame under those values. -/
theorem interp_ihIdxAtM {nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i ≤ nF) (as : List V) (E : AnnotTerm) :
    interp V (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
        (ihIdxAtM nF o i l as.length E)
      = interp V (consList as (consList (fs.take i) ρp)) E := by
  unfold ihIdxAtM
  rw [interp_liftN, show nF + l + as.length = as.length + (fs.length + ihs.length) from by omega,
    shiftE_consList_len', shiftE_fieldFrame hms, interp_liftN, shiftE_consList_len,
    ← consList_append]
  have hsplit : fs ++ ihs = fs.take i ++ (fs.drop i ++ ihs) := by
    rw [← List.append_assoc, List.take_append_drop]
  rw [hsplit, consList_append, show nF - i + l = (fs.drop i ++ ihs).length from by
    rw [List.length_append, List.length_drop]; omega, shiftE_consList]

/-- The nested product over the moved telescope at the ih frame is
the nested product over the telescope at the field's own frame. -/
theorem piTele_ihTeleAtGo {v : Nat} {B : List V → V} {nF o i l : Nat} {ρp : Nat → V} {M : V}
    {ms : List V} (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF)
    (hihs : ihs.length = l) (hi : i ≤ nF) :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (as acc : List V),
      piTele v (teleOfFields (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
          ((ihTeleAtGo nF o i l as.length tl).map (·.2.2))) B acc
        = piTele v (teleOfFields (consList as (consList (fs.take i) ρp)) (tl.map (·.2.2))) B acc
  | [], _, _ => rfl
  | d :: tl, as, acc => by
    show piTele v (teleOfFields _
      (((d.1, d.2.1, ihIdxAtM nF o i l as.length d.2.2) :: ihTeleAtGo nF o i l (as.length + 1) tl).map
        (·.2.2))) B acc = _
    rw [List.map_cons, List.map_cons]
    simp only [teleOfFields, piTele]
    rw [interp_ihIdxAtM hms hfs hihs hi]
    refine piR_congr fun a _ => ?_
    have := piTele_ihTeleAtGo (v := v) (B := B) (M := M) (ρp := ρp) hms hfs hihs hi tl (as ++ [a])
      (acc ++ [a])
    rw [length_snoc', ← consList_snoc', ← consList_snoc'] at this
    exact this


/-! ## Frame kit -/

theorem consList_getD_lt : ∀ (as : List V) (σ : Nat → V) (k : Nat), k < as.length →
    consList as σ k = as.getD (as.length - 1 - k) pt
  | [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | a :: as, σ, k, hk => by
    rw [consList_cons]
    rcases Nat.lt_or_ge k as.length with hlt | hge
    · rw [consList_getD_lt as (cons a σ) k hlt, List.length_cons,
        show as.length + 1 - 1 - k = (as.length - 1 - k) + 1 from by omega, List.getD_cons_succ]
    · have hk' : k = as.length := by simp at hk; omega
      subst hk'
      have := consList_apply_add as (cons a σ) 0
      rw [Nat.zero_add] at this
      rw [this, cons_zero, List.length_cons, Nat.add_sub_cancel, Nat.sub_self, List.getD_cons_zero]

theorem map_teleVarsAV_interp' {m : Nat} {bs : List V} (hm : bs.length = m) (ρ : Nat → V) :
    (teleVarsAV m).map (interp V (consList bs ρ)) = bs := by
  subst hm
  have h : (teleVarsAV bs.length).map (interp V (consList bs ρ))
      = frameIdx bs.length (consList bs ρ) := by
    unfold teleVarsAV frameIdx
    rw [List.map_map]
    apply List.map_congr_left
    intro l _
    simp only [Function.comp_def, interp_bvar]
  rw [h, frameIdx_consList']

theorem map_teleVarsAV_interp (bs : List V) (ρ : Nat → V) :
    (teleVarsAV bs.length).map (interp V (consList bs ρ)) = bs :=
  map_teleVarsAV_interp' rfl ρ

omit [SetTheory V] in
/-- The prefix variables depend only on the total depth below the
minors. -/
theorem prefixVarsAV_shift {nP n nF m nF' m' : Nat} (h : nF + m = nF' + m') :
    prefixVarsAV nP n nF m = prefixVarsAV nP n nF' m' := by
  unfold prefixVarsAV
  congr 1
  · congr 1
    · apply List.map_congr_left
      intro k _
      congr 1
      omega
    · congr 2
      omega
  · apply List.map_congr_left
    intro l hl
    have := List.mem_range.mp hl
    congr 1
    omega

/-- The prefix variables read to the block. -/
theorem map_prefixVarsAV_interp {nP n nF : Nat} {as₁ ms as₂ : List V} {M : V} {ρ : Nat → V}
    (hlenP : as₁.length = nP) (hlenM : ms.length = n) (hlenF : as₂.length = nF) (bs : List V) :
    (prefixVarsAV nP n nF bs.length).map
        (interp V (consList bs (consList as₂ (consList ms (cons M (consList as₁ ρ))))))
      = (as₁ ++ [M]) ++ ms := by
  unfold prefixVarsAV
  rw [List.map_append, List.map_append]
  congr 1
  congr 1
  · apply List.ext_getElem
    · simp [hlenP]
    · intro k h1 h2
      have hk : k < nP := by simpa using h1
      simp only [List.getElem_map, List.getElem_range, interp_bvar]
      rw [show nP + nF + n + 1 + bs.length - 1 - k = (((nP - 1 - k) + 1 + ms.length) + as₂.length) + bs.length
          from by omega,
        consList_apply_add, consList_apply_add, consList_apply_add, cons_succ,
        consList_getD_lt as₁ ρ (nP - 1 - k) (by omega), show as₁.length - 1 - (nP - 1 - k) = k from by omega,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
  · simp only [List.map_cons, List.map_nil, interp_bvar]
    rw [show nF + n + bs.length = ((0 + ms.length) + as₂.length) + bs.length from by omega,
      consList_apply_add, consList_apply_add, consList_apply_add, cons_zero]
  · apply List.ext_getElem
    · simp [hlenM]
    · intro l h1 h2
      have hl : l < n := by simpa using h1
      simp only [List.getElem_map, List.getElem_range, interp_bvar]
      rw [show nF + n - 1 - l + bs.length = ((n - 1 - l) + as₂.length) + bs.length from by omega,
        consList_apply_add, consList_apply_add, consList_getD_lt ms _ _ (by omega),
        show ms.length - 1 - (n - 1 - l) = l from by omega,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

/-- The λ-tower over the moved telescope at the ih frame is the λ-tower
over the telescope at the field's own frame (bodies agreeing at
corresponding leaves). -/
theorem lamTower_ihTeleAtGo {b nF o i : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs : List V} (hfs : fs.length = nF) (hi : i ≤ nF)
    {g₁ g₂ : (Nat → V) → V} :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (as : List V),
      (∀ bs : List V, bs.length = tl.length →
        g₁ (consList bs (consList as (consList fs (consList ms (cons M ρp)))))
          = g₂ (consList bs (consList as (consList (fs.take i) ρp)))) →
      lamTower b (consList as (consList fs (consList ms (cons M ρp)))) (ihTeleAtGo nF o i 0 as.length tl) g₁
        = lamTower b (consList as (consList (fs.take i) ρp)) tl g₂
  | [], as, hg => by
    have := hg [] rfl
    simpa [lamTower, ihTeleAtGo] using this
  | d :: tl, as, hg => by
    show lamR b (interp V _ (ihIdxAtM nF o i 0 as.length d.2.2))
        (fun a => lamTower b (cons a _) (ihTeleAtGo nF o i 0 (as.length + 1) tl) g₁)
      = lamR b (interp V _ d.2.2) (fun a => lamTower b (cons a _) tl g₂)
    have hd := interp_ihIdxAtM (ρp := ρp) (M := M) (l := 0) hms hfs (ihs := []) rfl hi as d.2.2
    rw [consList_nil] at hd
    rw [hd]
    refine lamR_congr fun a _ => ?_
    have ih := lamTower_ihTeleAtGo (b := b) hms hfs hi tl (as ++ [a]) (fun bs hbs => by
      have := hg (a :: bs) (by simp [hbs])
      rwa [consList_cons, consList_cons, consList_snoc', consList_snoc'] at this)
    rw [length_snoc', ← consList_snoc', ← consList_snoc'] at ih
    exact ih

theorem prefixVarsAV_wellDenoted {nP n nF m : Nat} {σ : Nat → V} {a : AnnotTerm}
    (ha : a ∈ prefixVarsAV nP n nF m) : WellDenoted V σ a := by
  unfold prefixVarsAV at ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha; trivial
    · rw [List.mem_singleton] at ha; subst ha; trivial
  · obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha; trivial

theorem teleVarsAV_wellDenoted {m : Nat} {σ : Nat → V} {a : AnnotTerm} (ha : a ∈ teleVarsAV m) :
    WellDenoted V σ a := by
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha; trivial

/-- The ih application's arguments read, under telescope values, to
the block, the field's index values and the field applied to the
values. -/
theorem ihAppAVb_args_interp {nP n nF e i : Nat} {as₁ ms ex fs bs : List V} {M : V} {ρ : Nat → V}
    (hlenP : as₁.length = nP) (hlenM : ms.length = n) (hlenE : ex.length = e) (hlenF : fs.length = nF)
    (hi : i < nF) (Eis : List AnnotTerm) :
    (prefixVarsAV nP n nF (bs.length + e) ++ Eis.map (ihIdxAtM nF (n + 1 + e) i 0 bs.length) ++
        [AnnotTerm.mkAppN (.bvar (nF - 1 - i + bs.length)) (teleVarsAV bs.length)]).map
      (interp V (consList bs (consList fs (consList ex (consList ms (cons M (consList as₁ ρ)))))))
      = (as₁ ++ [M]) ++ ms ++ Eis.map (interp V (consList bs (consList (fs.take i) (consList as₁ ρ)))) ++
        [(frameIdx bs.length (consList bs (consList (fs.take i) (consList as₁ ρ)))).foldl SetTheory.app
          (fs.getD i pt)] := by
  have hms : (ms ++ ex).length + 1 = n + 1 + e := by rw [List.length_append]; omega
  rw [List.map_append, List.map_append, List.map_map]
  have hσ : consList bs (consList fs (consList ex (consList ms (cons M (consList as₁ ρ)))))
      = consList bs (consList (ex ++ fs) (consList ms (cons M (consList as₁ ρ)))) := by
    rw [consList_append]
  have hσ' : consList bs (consList fs (consList ex (consList ms (cons M (consList as₁ ρ)))))
      = consList bs (consList [] (consList fs (consList (ms ++ ex) (cons M (consList as₁ ρ))))) := by
    rw [consList_nil, consList_append]
  have hpre : (prefixVarsAV nP n nF (bs.length + e)).map
      (interp V (consList bs (consList fs (consList ex (consList ms (cons M (consList as₁ ρ)))))))
      = (as₁ ++ [M]) ++ ms := by
    rw [hσ, prefixVarsAV_shift (nF' := e + nF) (m' := bs.length) (by omega)]
    exact map_prefixVarsAV_interp hlenP hlenM (by rw [List.length_append]; omega) bs
  have hEis : Eis.map (interp V (consList bs (consList fs (consList ex (consList ms (cons M (consList as₁ ρ))))))
      ∘ ihIdxAtM nF (n + 1 + e) i 0 bs.length)
      = Eis.map (interp V (consList bs (consList (fs.take i) (consList as₁ ρ)))) := by
    apply List.map_congr_left
    intro E _
    simp only [Function.comp_def]
    rw [hσ']
    exact interp_ihIdxAtM (ρp := consList as₁ ρ) (M := M) (l := 0) hms hlenF (ihs := []) rfl
      (Nat.le_of_lt hi) bs E
  have hfld : interp V (consList bs (consList fs (consList ex (consList ms (cons M (consList as₁ ρ))))))
      (AnnotTerm.mkAppN (.bvar (nF - 1 - i + bs.length)) (teleVarsAV bs.length))
      = (frameIdx bs.length (consList bs (consList (fs.take i) (consList as₁ ρ)))).foldl
          SetTheory.app (fs.getD i pt) := by
    rw [interp_mkAppN, ← List.foldl_map (f := interp V _) (g := SetTheory.app),
      map_teleVarsAV_interp, frameIdx_consList', interp_bvar, consList_apply_add,
      consList_getD_lt fs _ _ (by omega), show fs.length - 1 - (nF - 1 - i) = i from by omega]
  rw [hpre, hEis, List.map_cons, List.map_nil, hfld]

/-- **The ih application reads to the λ-tower** over the field's
telescope at the field's own frame of the function at the block, the
field's index values and the field applied to the telescope's values. -/
theorem interp_ihAppAVb {b nP n nF e i : Nat} {as₁ ms ex fs : List V} {M : V} {ρ : Nat → V}
    (hlenP : as₁.length = nP) (hlenM : ms.length = n) (hlenE : ex.length = e) (hlenF : fs.length = nF)
    (hi : i < nF) {Rm : Nat → AnnotTerm} {rV : V}
    (hR : ∀ bs : List V,
      interp V (consList bs (consList fs (consList ex (consList ms (cons M (consList as₁ ρ))))))
        (Rm bs.length) = rV)
    (tl : List (Nat × Nat × AnnotTerm)) (Eis : List AnnotTerm) :
    interp V (consList fs (consList ex (consList ms (cons M (consList as₁ ρ)))))
        (ihAppAVb b Rm nP n nF e i tl Eis)
      = lamTower b (consList (fs.take i) (consList as₁ ρ)) tl fun σ' =>
          ((as₁ ++ [M]) ++ ms ++ Eis.map (interp V σ') ++
            [(frameIdx tl.length σ').foldl SetTheory.app (fs.getD i pt)]).foldl SetTheory.app rV := by
  unfold ihAppAVb ihTeleAtR
  rw [interp_mkLamsC]
  have hms : (ms ++ ex).length + 1 = n + 1 + e := by rw [List.length_append]; omega
  have hfr : consList fs (consList ex (consList ms (cons M (consList as₁ ρ))))
      = consList [] (consList fs (consList (ms ++ ex) (cons M (consList as₁ ρ)))) := by
    rw [consList_nil, consList_append]
  rw [hfr]
  refine lamTower_ihTeleAtGo hms hlenF (Nat.le_of_lt hi) tl [] fun bs hbs => ?_
  simp only [consList_nil]
  rw [← hbs, interp_mkAppN, ← List.foldl_map (f := interp V _) (g := SetTheory.app), consList_append ms ex,
    ihAppAVb_args_interp hlenP hlenM hlenE hlenF hi, hR bs]

/-! ## Moved kit (from the P tier's `FixRuleKitP`; pure) -/

/-! ## The minor space's application chain -/

/-- A minor-space member applied along a fitting spine is a graded
application chain. -/
theorem minorSpI_appChainOk {ℓ : Nat} {c : List V → V}
    (hc0 : ℓ = 0 → ∀ acc, c acc ∈ˢ (univZero : V)) :
    ∀ {Fs : List AnnotTerm} {ρf : Nat → V} {acc : List V} {m : V} {as : List V},
      m ∈ˢ minorSpI ℓ c Fs ρf acc → SpineFit ρf Fs as → AppChainOk m as
  | [], _, _, _, [], _, _ => fun l hl => absurd hl (Nat.not_lt_zero _)
  | [], _, _, _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, _, _, [], _, hsp => hsp.elim
  | F :: Fs, ρf, acc, m, a :: as, hm, hsp => by
    have hB0 : ℓ = 0 → ∀ x, x ∈ˢ interp V ρf F →
        minorSpI ℓ c Fs (cons x ρf) (acc ++ [x]) ∈ˢ (univZero : V) :=
      fun h0 x _ => minorSpI_zero_univZero h0 (hc0 h0) Fs (cons x ρf) (acc ++ [x])
    have happ : SetTheory.app m a ∈ˢ minorSpI ℓ c Fs (cons a ρf) (acc ++ [a]) :=
      app_mem_piR hm hsp.1 hB0
    intro l hl
    cases l with
    | zero =>
      exact ⟨ℓ, interp V ρf F, fun x => minorSpI ℓ c Fs (cons x ρf) (acc ++ [x]), hm,
        by simpa using hsp.1, hB0⟩
    | succ l =>
      obtain ⟨v, A, B, h1, h2, h3⟩ := minorSpI_appChainOk hc0 (Fs := Fs) (as := as) happ hsp.2 l
        (by simpa using hl)
      refine ⟨v, A, B, ?_, ?_, h3⟩
      · simpa only [List.take_succ_cons, List.foldl_cons] using h1
      · simpa only [List.getD_cons_succ] using h2


theorem WellDenoted_ihIdxAtM {nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i ≤ nF) (as : List V) (E : AnnotTerm) :
    WellDenoted V (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
        (ihIdxAtM nF o i l as.length E) ↔
      WellDenoted V (consList as (consList (fs.take i) ρp)) E := by
  unfold ihIdxAtM
  rw [WellDenoted_liftN, show nF + l + as.length = as.length + (fs.length + ihs.length) from by omega,
    shiftE_consList_len', shiftE_fieldFrame hms, WellDenoted_liftN, shiftE_consList_len,
    ← consList_append]
  have hsplit : fs ++ ihs = fs.take i ++ (fs.drop i ++ ihs) := by
    rw [← List.append_assoc, List.take_append_drop]
  rw [hsplit, consList_append, show nF - i + l = (fs.drop i ++ ihs).length from by
    rw [List.length_append, List.length_drop]; omega, shiftE_consList]

/-- A spine fits the moved telescope at the ih frame iff it fits the
telescope at the field's own frame. -/
theorem spineFit_ihTeleAtGo {nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i ≤ nF) :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (as bs : List V),
      SpineFit (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
          ((ihTeleAtGo nF o i l as.length tl).map (·.2.2)) bs ↔
        SpineFit (consList as (consList (fs.take i) ρp)) (tl.map (·.2.2)) bs
  | [], _, [] => Iff.rfl
  | [], _, _ :: _ => Iff.rfl
  | _ :: _, _, [] => by simp [ihTeleAtGo, SpineFit]
  | d :: tl, as, b :: bs => by
    show b ∈ˢ interp V (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
        (ihIdxAtM nF o i l as.length d.2.2) ∧ SpineFit _ _ bs ↔
      b ∈ˢ interp V (consList as (consList (fs.take i) ρp)) d.2.2 ∧ SpineFit _ _ bs
    rw [interp_ihIdxAtM hms hfs hihs hi, consList_snoc', consList_snoc']
    have := spineFit_ihTeleAtGo (M := M) (ρp := ρp) hms hfs hihs hi tl (as ++ [b]) bs
    rw [length_snoc'] at this
    rw [this]

/-- The telescope's grading moved to the ih frame. -/
theorem fieldsOkB_ihTeleAtGo {w nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i ≤ nF) :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (as : List V),
      FieldsOkB w (consList as (consList (fs.take i) ρp)) (tl.map (·.2.2)) →
      FieldsOkB w (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
        ((ihTeleAtGo nF o i l as.length tl).map (·.2.2))
  | [], _, _ => trivial
  | d :: tl, as, hF => by
    show FieldsOkB w _ (ihIdxAtM nF o i l as.length d.2.2 ::
      (ihTeleAtGo nF o i l (as.length + 1) tl).map (·.2.2))
    rw [List.map_cons] at hF
    obtain ⟨hok, hbnd, hrest⟩ := hF
    refine ⟨(WellDenoted_ihIdxAtM hms hfs hihs hi as _).mpr hok,
      fun hw => by rw [interp_ihIdxAtM hms hfs hihs hi]; exact hbnd hw, fun a ha => ?_⟩
    rw [interp_ihIdxAtM hms hfs hihs hi] at ha
    rw [consList_snoc']
    have := fieldsOkB_ihTeleAtGo (M := M) (ρp := ρp) hms hfs hihs hi tl (as ++ [a])
      (by rw [← consList_snoc']; exact hrest a ha)
    rw [length_snoc'] at this
    exact this


/-- A graded telescope walks. -/
theorem domsWalk_of_fieldsOkB {w : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      FieldsOkB w ρ (ds.map (·.2.2)) → DomsWalk ρ ds
  | [], _, _ => trivial
  | _ :: ds, ρ, h => by
    rw [List.map_cons] at h
    exact ⟨h.1, fun a ha => domsWalk_of_fieldsOkB (h.2.2 a ha)⟩

/-! ## The slot's value along a telescope spine -/

/-- A family's applications are bounded by its universe (junk off the
index set). -/
theorem famApp_mem_univ {w : Nat} {I X : V} (hX : X ∈ˢ lfpFamSpace V w I) (t : V) :
    SetTheory.app X t ∈ˢ (univ w : V) := by
  by_cases ht : t ∈ˢ I
  · exact app_mem_piR_pos (Nat.succ_ne_zero w) hX ht
  · rw [(mem_piR_pos (Nat.succ_ne_zero w) hX).2.2.1 t ht]
    exact empty_mem_univ w

/-- **A field in a slot's value, applied along a fitting telescope
spine, lies in the family at the index values** (task #202). -/
theorem slotSet_fold_mem {w u : Nat} {ρ : Nat → V} {tl : List (Nat × Nat × AnnotTerm)}
    {Eis : List AnnotTerm} {X : V} (hX : ∀ t, SetTheory.app X t ∈ˢ (univ w : V)) {f : V}
    (hf : f ∈ˢ slotSet w u ρ tl Eis X) {bs : List V} (hsp : SpineFit ρ (tl.map (·.2.2)) bs) :
    bs.foldl SetTheory.app f
      ∈ˢ SetTheory.app X (tupW u (Eis.map (interp V (consList bs ρ)))) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · have hpt : f = pt := eq_pt_of_mem_slotSet_zero (fun t => by rw [← univ_zero]; exact hX t) hf
    unfold slotSet at hf
    obtain ⟨y, hy⟩ := mem_piTele_zero hf bs (fitsS_teleOfFields.mpr hsp)
    rw [List.nil_append] at hy
    have hz : SetTheory.app X (tupW u (Eis.map (interp V (consList bs ρ)))) ∈ˢ (univZero : V) := by
      rw [← univ_zero]; exact hX _
    rw [hpt, foldl_app_pt_sum, ← eq_pt_of_mem_univZero hz hy]
    exact hy
  · have hw' : w ≠ 0 := Nat.pos_iff_ne_zero.mp hw
    unfold slotSet at hf
    have := piTele_fold hw' hf (fitsS_teleOfFields.mpr hsp)
    rwa [List.nil_append] at this

/-- **A field in a slot's value has a graded application chain** along
a fitting telescope spine. -/
theorem slotSet_chainOk {w u : Nat} {ρ : Nat → V} {tl : List (Nat × Nat × AnnotTerm)}
    {Eis : List AnnotTerm} {X : V} (hX : ∀ t, SetTheory.app X t ∈ˢ (univ w : V)) {f : V}
    (hf : f ∈ˢ slotSet w u ρ tl Eis X) {bs : List V} (hsp : SpineFit ρ (tl.map (·.2.2)) bs) :
    AppChainOk f bs := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · -- the field is the point: every prefix application is the point, in
    -- a `Prop`-regime product over the next domain with inhabited fibres
    have hpt : f = pt := eq_pt_of_mem_slotSet_zero (fun t => by rw [← univ_zero]; exact hX t) hf
    subst hpt
    intro l hl
    have hlen : bs.length = tl.length := by rw [hsp.length_eq, List.length_map]
    refine ⟨0, interp V (consList (bs.take l) ρ) ((tl.map (·.2.2)).getD l default),
      fun _ => truthVal True, ?_, ?_, fun _ _ _ => truthVal_mem_univZero True⟩
    · rw [foldl_app_pt_sum, piR_zero]
      exact mem_truthVal.mpr ⟨fun _ _ => ⟨pt, mem_truthVal.mpr ⟨trivial, rfl⟩⟩, rfl⟩
    · exact FixKI.spineFit_getD_mem' hsp (by rw [List.length_map]; omega)
  · have hw' : w ≠ 0 := Nat.pos_iff_ne_zero.mp hw
    unfold slotSet at hf
    exact piTele_chainOk hw' hf (fitsS_teleOfFields.mpr hsp)

/-! ## λ-towers in nested products -/

/-- A λ-tower whose leaves lie in the bound lies in the nested product
over its telescope. -/
theorem lamTower_mem_piTele {m : Nat} {B : List V → V} {g : (Nat → V) → V} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {acc : List V},
      (∀ bs, SpineFit ρ (ds.map (·.2.2)) bs → g (consList bs ρ) ∈ˢ B (acc ++ bs)) →
      lamTower m ρ ds g ∈ˢ piTele m (teleOfFields ρ (ds.map (·.2.2))) B acc
  | [], ρ, acc, hg => by
    show g ρ ∈ˢ B acc
    simpa only [consList_nil, List.append_nil] using hg [] trivial
  | d :: ds, ρ, acc, hg => by
    show lamR m (interp V ρ d.2.2) (fun a => lamTower m (cons a ρ) ds g)
      ∈ˢ piR m (interp V ρ d.2.2)
        (fun a => piTele m (teleOfFields (cons a ρ) (ds.map (·.2.2))) B (acc ++ [a]))
    refine lamR_mem fun a ha => lamTower_mem_piTele fun bs hbs => ?_
    have := hg (a :: bs) ⟨ha, hbs⟩
    rwa [consList_cons, List.append_cons] at this

/-- A `Prop`-regime nested product over fibres in the truth values is a
truth value. -/
theorem piTele_zero_mem_univZero {B : List V → V} :
    ∀ {k : Nat} {T : TeleS V k} {acc : List V},
      (∀ as, FitsS T as → B (acc ++ as) ∈ˢ (univZero : V)) →
      piTele 0 T B acc ∈ˢ (univZero : V)
  | _, .nil, acc, h => by simpa [piTele] using h [] trivial
  | _, .cons _ _, _, _ => piR_zero_mem_univZero

/-- A member of a nested product (nonzero level) has a graded
application chain along a fitting spine. -/
theorem appChainOk_of_piTele {v : Nat} (hv : v ≠ 0) {B : List V → V} :
    ∀ {k : Nat} {T : TeleS V k} {acc : List V} {f : V} {as : List V},
      f ∈ˢ piTele v T B acc → FitsS T as → AppChainOk f as
  | _, .nil, _, _, [], _, _ => fun l hl => absurd hl (Nat.not_lt_zero _)
  | _, .nil, _, _, _ :: _, _, hf => hf.elim
  | _, .cons _ _, _, _, [], _, hf => hf.elim
  | _, .cons A T, acc, f, a :: as, hf, hfits => by
    have hfits' : a ∈ˢ A ∧ FitsS (T a) as := hfits
    obtain ⟨ha, hfit⟩ := hfits'
    have hf' : f ∈ˢ piR v A (fun a => piTele v (T a) B (acc ++ [a])) := hf
    intro l hl
    cases l with
    | zero => exact ⟨v, A, _, hf', ha, fun h0 => absurd h0 hv⟩
    | succ l =>
      have happ : SetTheory.app f a ∈ˢ piTele v (T a) B (acc ++ [a]) :=
        (mem_piR_pos hv hf').2.1 a ha
      obtain ⟨v', A', B', h1, h2, h3⟩ := appChainOk_of_piTele hv happ hfit l (by simpa using hl)
      exact ⟨v', A', B', by simpa only [List.take_succ_cons, List.foldl_cons] using h1,
        by simpa only [List.getD_cons_succ] using h2, h3⟩

/-- A member of a `Prop`-regime nested product (fibres truth values)
has a graded application chain along a fitting spine. -/
theorem appChainOk_piTele_zero {B : List V → V} :
    ∀ {k : Nat} {T : TeleS V k} {acc : List V} {x : V} {as : List V},
      x ∈ˢ piTele 0 T B acc → FitsS T as →
      (∀ as', FitsS T as' → B (acc ++ as') ∈ˢ (univZero : V)) → AppChainOk x as
  | _, .nil, _, _, [], _, _, _ => fun l hl => absurd hl (Nat.not_lt_zero _)
  | _, .nil, _, _, _ :: _, _, hf, _ => hf.elim
  | _, .cons _ _, _, _, [], _, hf, _ => hf.elim
  | _, .cons A T, acc, x, a :: as, hx, hfits, hB => by
    have hfits' : a ∈ˢ A ∧ FitsS (T a) as := hfits
    obtain ⟨ha, hfit⟩ := hfits'
    have hx' : x ∈ˢ piR 0 A (fun a => piTele 0 (T a) B (acc ++ [a])) := hx
    have hB' : ∀ a', a' ∈ˢ A → piTele 0 (T a') B (acc ++ [a']) ∈ˢ (univZero : V) := fun a' ha' =>
      piTele_zero_mem_univZero fun as' hf' => by
        have := hB (a' :: as') (show a' ∈ˢ A ∧ FitsS (T a') as' from ⟨ha', hf'⟩)
        rwa [List.append_cons] at this
    intro l hl
    cases l with
    | zero => exact ⟨0, A, _, hx', ha, fun _ => hB'⟩
    | succ l =>
      -- the application is the point, in the next product (inhabited)
      have hxpt : x = pt := eq_pt_of_mem_univZero piR_zero_mem_univZero hx'
      obtain ⟨y, hy⟩ := piTele_zero_inhab_of (B := B) (T := T a) (acc := acc ++ [a]) fun as' hf' => by
        have := mem_piTele_zero hx (a :: as') (show a ∈ˢ A ∧ FitsS (T a) as' from ⟨ha, hf'⟩)
        rwa [List.append_cons] at this
      have hypt : y = pt := eq_pt_of_mem_univZero (hB' a ha) hy
      subst hypt
      have happ : SetTheory.app x a ∈ˢ piTele 0 (T a) B (acc ++ [a]) := by
        rw [hxpt, app_pt]; exact hy
      obtain ⟨v', A', B', h1, h2, h3⟩ := appChainOk_piTele_zero happ hfit
        (fun as' hf' => by
          have := hB (a :: as') (show a ∈ˢ A ∧ FitsS (T a) as' from ⟨ha, hf'⟩)
          rwa [List.append_cons] at this) l (by simpa using hl)
      exact ⟨v', A', B', by simpa only [List.take_succ_cons, List.foldl_cons] using h1,
        by simpa only [List.getD_cons_succ] using h2, h3⟩

/-- A member of the ih tower has a graded application chain along ih
values in the domains. -/
theorem ihSpL_appChainOk {ℓ : Nat} {C : V} (hC0 : ℓ = 0 → C ∈ˢ (univZero : V)) :
    ∀ {As vs : List V} {x : V}, x ∈ˢ ihSpL ℓ C As → vs.length = As.length →
      (∀ l, l < As.length → vs.getD l pt ∈ˢ As.getD l pt) → AppChainOk x vs
  | [], [], _, _, _, _ => fun l hl => absurd hl (Nat.not_lt_zero _)
  | [], _ :: _, _, _, hlen, _ => nomatch hlen
  | _ :: _, [], _, _, hlen, _ => nomatch hlen
  | A :: As, v :: vs, x, hx, hlen, hmem => by
    have hx' : x ∈ˢ piR ℓ A (fun _ => ihSpL ℓ C As) := hx
    have hv : v ∈ˢ A := by simpa using hmem 0 (by simp)
    have hB0 : ℓ = 0 → ∀ y, y ∈ˢ A → ihSpL ℓ C As ∈ˢ (univZero : V) :=
      fun h0 _ _ => ihSpL_zero_univZero h0 (hC0 h0) As
    have happ : SetTheory.app x v ∈ˢ ihSpL ℓ C As := app_mem_piR hx' hv hB0
    intro l hl
    cases l with
    | zero => exact ⟨ℓ, A, _, hx', hv, hB0⟩
    | succ l =>
      obtain ⟨v', A', B', h1, h2, h3⟩ := ihSpL_appChainOk hC0 happ (by simpa using hlen)
        (fun l hl => by simpa using hmem (l + 1) (by simpa using hl)) l (by simpa using hl)
      exact ⟨v', A', B', by simpa only [List.take_succ_cons, List.foldl_cons] using h1,
        by simpa only [List.getD_cons_succ] using h2, h3⟩

/-- `UnderTowerOk` with a semantic bound at the leaves. -/
def UnderTowerOkB (m : Nat) (b : AnnotTerm) (B : List V → V) :
    (Nat → V) → List V → List (Nat × Nat × AnnotTerm) → Prop
  | ρ, acc, [] => WellDenoted V ρ b ∧ interp V ρ b ∈ˢ B acc ∧ (m = 0 → B acc ∈ˢ (univZero : V))
  | ρ, acc, d :: ds => WellDenoted V ρ d.2.2 ∧
      ∀ a, a ∈ˢ interp V ρ d.2.2 → UnderTowerOkB m b B (cons a ρ) (acc ++ [a]) ds

theorem underTowerOkB_of_leaves {m : Nat} {b : AnnotTerm} {B : List V → V} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {acc : List V},
      DomsWalk ρ ds →
      (∀ bs, SpineFit ρ (ds.map (·.2.2)) bs →
        WellDenoted V (consList bs ρ) b ∧ interp V (consList bs ρ) b ∈ˢ B (acc ++ bs) ∧
        (m = 0 → B (acc ++ bs) ∈ˢ (univZero : V))) →
      UnderTowerOkB m b B ρ acc ds
  | [], ρ, acc, _, hb => by
    show WellDenoted V ρ b ∧ interp V ρ b ∈ˢ B acc ∧ (m = 0 → B acc ∈ˢ (univZero : V))
    simpa only [consList_nil, List.append_nil] using hb [] trivial
  | d :: ds, ρ, acc, hok, hb => by
    refine ⟨hok.1, fun a ha => underTowerOkB_of_leaves (hok.2 a ha) fun bs hsp => ?_⟩
    have := hb (a :: bs) ⟨ha, hsp⟩
    rwa [consList_cons, List.append_cons] at this

/-- **A constant-bit λ-tower is graded and lies in the nested product**
over its telescope of the bound. -/
theorem mkLamsC_factsB {m : Nat} {b : AnnotTerm} {B : List V → V} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {acc : List V},
      UnderTowerOkB m b B ρ acc ds →
      WellDenoted V ρ (mkLamsC m ds b) ∧
        interp V ρ (mkLamsC m ds b) ∈ˢ piTele m (teleOfFields ρ (ds.map (·.2.2))) B acc
  | [], ρ, acc, h => ⟨h.1, h.2.1⟩
  | d :: ds, ρ, acc, h => by
    have hrest : ∀ a, a ∈ˢ interp V ρ d.2.2 →
        WellDenoted V (cons a ρ) (mkLamsC m ds b) ∧
        interp V (cons a ρ) (mkLamsC m ds b)
          ∈ˢ piTele m (teleOfFields (cons a ρ) (ds.map (·.2.2))) B (acc ++ [a]) :=
      fun a ha => mkLamsC_factsB (h.2 a ha)
    refine ⟨?_, ?_⟩
    · show WellDenoted V ρ (.lam m d.2.2 (mkLamsC m ds b))
      rw [WellDenoted_lam]
      refine ⟨h.1, fun a ha => (hrest a ha).1,
        fun a => piTele m (teleOfFields (cons a ρ) (ds.map (·.2.2))) B (acc ++ [a]),
        fun a ha => (hrest a ha).2, fun h0 a ha => ?_⟩
      subst h0
      refine piTele_zero_mem_univZero fun as' hf' => ?_
      exact underTowerOkB_zero (h.2 a ha) as' (fitsS_teleOfFields.mp hf')
    · show lamR m (interp V ρ d.2.2) (fun a => interp V (cons a ρ) (mkLamsC m ds b))
        ∈ˢ piR m (interp V ρ d.2.2)
          (fun a => piTele m (teleOfFields (cons a ρ) (ds.map (·.2.2))) B (acc ++ [a]))
      exact lamR_mem fun a ha => (hrest a ha).2
where
  /-- the bound is a truth value at level zero, at every fitting spine -/
  underTowerOkB_zero {b : AnnotTerm} {B : List V → V} :
      ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {acc : List V},
        UnderTowerOkB 0 b B ρ acc ds → ∀ bs, SpineFit ρ (ds.map (·.2.2)) bs →
        B (acc ++ bs) ∈ˢ (univZero : V)
    | [], _, _, h, [], _ => by simpa using h.2.2 rfl
    | [], _, _, _, _ :: _, hsp => hsp.elim
    | _ :: _, _, _, _, [], hsp => hsp.elim
    | d :: ds, ρ, acc, h, a :: bs, hsp => by
      have := underTowerOkB_zero (h.2 a hsp.1) bs hsp.2
      rwa [List.append_assoc] at this

/-! ## The sources -/

omit [SetTheory V] in
theorem srcList_length (Es : List AnnotTerm) (nF : Nat) : (srcList Es nF).length = nF := by
  simp [srcList]

omit [SetTheory V] in
theorem srcList_bound {Es : List AnnotTerm} {nF : Nat} :
    ∀ s ∈ srcList Es nF, ∀ l, s = some l → l < Es.length := by
  intro s hs l hl
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hs
  unfold srcOfEs at hl
  exact List.mem_range.mp (List.mem_of_find?_eq_some hl)

theorem srcVals_length (is : List V) (src : List (Option Nat)) : (srcVals is src).length = src.length := by
  simp [srcVals]

omit [SetTheory V] in
/-- A source position's expression is the field's variable. -/
theorem srcOfEs_some {Es : List AnnotTerm} {nF j l : Nat} (h : srcOfEs Es nF j = some l) :
    l < Es.length ∧ Es.getD l default = .bvar (nF - 1 - j) := by
  unfold srcOfEs at h
  refine ⟨List.mem_range.mp (List.mem_of_find?_eq_some h), ?_⟩
  have hp := List.find?_some h
  revert hp
  cases Es.getD l default <;> simp

omit [SetTheory V] in
/-- At an unsourced field no index expression is the field's variable. -/
theorem srcOfEs_none {Es : List AnnotTerm} {nF j l : Nat} (h : srcOfEs Es nF j = none)
    (hl : Es[l]? = some (.bvar (nF - 1 - j))) : False := by
  unfold srcOfEs at h
  have hlt : l < Es.length := (List.getElem?_eq_some_iff.mp hl).1
  have := List.find?_eq_none.mp h l (List.mem_range.mpr hlt)
  rw [List.getD_eq_getElem?_getD, hl, Option.getD_some] at this
  simp at this

/-- **The subsingleton criterion**: a spine fitting the fields whose
index values are the tuple is the source spine (an index-sourced field
is the index's value, the other fields are `Prop`s — points). -/
theorem srcVals_of_fit {ρp : Nat → V} {Fs Es : List AnnotTerm}
    (hprop : ∀ j, j < Fs.length → srcOfEs Es Fs.length j = none →
      ∀ fs : List V, SpineFit ρp (Fs.take j) fs →
        interp V (consList fs ρp) (Fs.getD j default) ∈ˢ (univZero : V))
    {fs is : List V} (hfit : SpineFit ρp Fs fs) (hidx : idxValsAt ρp Es fs = is) :
    fs = srcVals is (srcList Es Fs.length) := by
  have hlen : fs.length = Fs.length := hfit.length_eq
  apply List.ext_getElem
  · rw [srcVals_length, srcList_length, hlen]
  intro j h1 h2
  rw [srcVals_length, srcList_length] at h2
  have hfj : fs[j] = fs.getD j pt := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
  rw [hfj]
  cases hs : srcOfEs Es Fs.length j with
  | some l =>
    simp only [srcVals, srcList, List.getElem_map, List.getElem_range, hs]
    obtain ⟨hl, hE⟩ := srcOfEs_some hs
    subst hidx
    show fs.getD j pt = (Es.map (interp V (consList fs ρp))).getD l pt
    have hr : (Es.map (interp V (consList fs ρp))).getD l pt = interp V (consList fs ρp) Es[l] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl]; rfl
    have hEl : Es[l] = AnnotTerm.bvar (Fs.length - 1 - j) := by
      rw [← hE, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]; rfl
    rw [hr, hEl, interp_bvar, consList_getD_lt fs ρp _ (by omega),
      show fs.length - 1 - (Fs.length - 1 - j) = j from by omega]
  | none =>
    simp only [srcVals, srcList, List.getElem_map, List.getElem_range, hs]
    have hmem := FixKI.spineFit_getD_mem' hfit h2
    have hsp : SpineFit ρp (Fs.take j) (fs.take j) := by
      have := spineFit_prefix (as := fs.take j) (bs := fs.drop j) (by rw [List.take_append_drop]; exact hfit)
      rwa [List.length_take, hlen, Nat.min_eq_left (Nat.le_of_lt h2)] at this
    exact eq_pt_of_mem_univZero (hprop j h2 hs _ hsp) hmem

/-! ## The K-frame in list form -/

omit [SetTheory V] in
theorem consList_kframe (ps ms is : List V) (M : V) (ρ' : Nat → V) :
    consList (ps ++ [M] ++ ms ++ is) ρ' = consList is (consList ms (cons M (consList ps ρ'))) := by
  rw [consList_append, consList_append, consList_append, consList_cons, consList_nil]

/-! ## The squash data at a tuple -/

/-- The index spine of a tuple (at level `0` every index is a proof). -/
noncomputable def isOfW (u nIdx : Nat) (t : V) : List V :=
  if u = 0 then List.replicate nIdx pt else projList nIdx t

/-- A fitting spine over `Prop`-regime domains is the points. -/
theorem spineFit_zero_replicate :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V} {is : List V}, FieldsBound 0 ρ Fs → SpineFit ρ Fs is →
      is = List.replicate Fs.length pt
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, _, h => h.elim
  | _ :: _, _, [], _, h => h.elim
  | F :: Fs, ρ, a :: is, hb, hsp => by
    obtain ⟨ha, hsp'⟩ := hsp
    have hpt : a = pt := by
      have := hb.1
      rw [univ_zero] at this
      exact eq_pt_of_mem_univZero this ha
    subst hpt
    rw [List.length_cons, List.replicate_succ]
    exact congrArg _ (spineFit_zero_replicate (hb.2 pt ha) hsp')

theorem isOfW_tupW {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} (hI : IdxOk u ρp Ids)
    {is : List V} (hsp : SpineFit ρp Ids is) : isOfW u Ids.length (tupW u is) = is := by
  by_cases hu : u = 0
  · rw [isOfW, if_pos hu]
    subst hu
    exact (spineFit_zero_replicate hI.2 hsp).symm
  · rw [isOfW, tupW, if_neg hu, if_neg hu]
    exact projList_mkTower _ _ hsp.length_eq

/-- The source spine at a tuple: the constructor's fields read off the
indices (`srcVals`, the sum route's squash regime). -/
noncomputable def sqSpine (u nIdx : Nat) (src : List (Option Nat)) (t : V) : List V :=
  srcVals (isOfW u nIdx t) src

/-- The predecessors of a tuple: the index tuples of the recursive
fields' calls, along their telescopes at the source spine. -/
noncomputable def sqPred (u : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) (rs : List Bool)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eis : List (List AnnotTerm)) (nF : Nat)
    (src : List (Option Nat)) (t : V) : V :=
  sep (idxSet u ρp Ids) fun j => ∃ i ∈ recIdx rs nF, ∃ bs : List V,
    SpineFit (consList ((sqSpine u Ids.length src t).take i) ρp) ((tls.getD i []).map (·.2.2)) bs ∧
    j = tupW u ((Eis.getD i []).map
      (interp V (consList bs (consList ((sqSpine u Ids.length src t).take i) ρp))))

/-- The bound: the motive's fibre at the tuple's indices and the point. -/
noncomputable def sqB (u nIdx : Nat) (M : V) (t : V) : V :=
  SetTheory.app ((isOfW u nIdx t).foldl SetTheory.app M) pt

/-- The ih values from a choice `g` of the predecessors' values: for
each recursive field, the λ-tower over its telescope of `g` at the
call's index tuple. -/
noncomputable def sqIhs (ℓ u : Nat) (ρp : Nat → V) (rs : List Bool)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eis : List (List AnnotTerm)) (nF : Nat)
    (fs : List V) (g : V) : List V :=
  (recIdx rs nF).map fun i =>
    lamTower ℓ (consList (fs.take i) ρp) (tls.getD i []) fun σ' =>
      SetTheory.app g (tupW u ((Eis.getD i []).map (interp V σ')))

/-- The step: the (only) minor `m` at the source spine and the ih values. -/
noncomputable def sqSt (ℓ u : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) (rs : List Bool)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eis : List (List AnnotTerm)) (nF : Nat)
    (src : List (Option Nat)) (m : V) (t g : V) : V :=
  (sqSpine u Ids.length src t ++
    sqIhs ℓ u ρp rs tls Eis nF (sqSpine u Ids.length src t) g).foldl SetTheory.app m

/-- **The recursor's graph.** -/
noncomputable def sqGraph (ℓ u : Nat) (ρp : Nat → V) (M : V) (Ids : List AnnotTerm) (rs : List Bool)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eis : List (List AnnotTerm)) (nF : Nat)
    (src : List (Option Nat)) (m : V) : V :=
  recGraph ℓ (idxSet u ρp Ids) (sqPred u ρp Ids rs tls Eis nF src) (sqB u Ids.length M)
    (sqSt ℓ u ρp Ids rs tls Eis nF src m)

/-! ## The recursion theorem at the family -/

section Singleton

variable {ℓ u nF : Nat} {ρp : Nat → V} {M m : V} {Fss Ess Fss₀ : List (List AnnotTerm)}
  {Ids : List AnnotTerm} {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
  {Eiss : List (List (List AnnotTerm))} {src : List (Option Nat)}

/-- **The graph is a singleton at every tuple of the family**, by lfp
induction on the family's functor: a proof of `t` at a sub-family is a
spine fitting the X-chain there; its recursive slots lie in the
`Prop`-regime products, so every predecessor's fibre in the sub-family
is inhabited, hence a singleton of the graph; the spine is the source
spine (the subsingleton criterion, `hsrc`), so the predecessors are
`sqPred`'s and the local step applies. -/
theorem sqGraph_singleton (hX : XChainsOk u 0 ρp Ids rss tlss Eiss Fss₀ Ess)
    (hreal : ChainsRealI (fixFamI u 0 ρp Ids Ids.length rss tlss Eiss Fss₀ Ess) u 0 ρp Ids rss tlss
      Eiss Fss₀ Fss Ess)
    (hsingle : Fss.length = 1) (hlenF : (Fss.getD 0 []).length = nF)
    (hEs : (Ess.getD 0 []).length = Ids.length)
    (hsrc : ∀ (fs is : List V), SpineFit ρp (Fss.getD 0 []) fs → SpineFit ρp Ids is →
      idxValsAt ρp (Ess.getD 0 []) fs = is → fs = srcVals is src)
    (hB : ∀ t, t ∈ˢ idxSet u ρp Ids → sqB u Ids.length M t ∈ˢ (univ ℓ : V))
    (hst : ∀ (is : List V) (t : V), SpineFit ρp Ids is → t = tupW u is →
      SpineFit ρp (Fss.getD 0 []) (sqSpine u Ids.length src t) →
      idxValsAt ρp (Ess.getD 0 []) (sqSpine u Ids.length src t) = is → ∀ g,
      g ∈ˢ piSet (sqPred u ρp Ids (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 []) nF src t)
        (fun j => SetTheory.app
          (sqGraph ℓ u ρp M Ids (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 []) nF src m) j) →
      sqSt ℓ u ρp Ids (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 []) nF src m t g
        ∈ˢ sqB u Ids.length M t) :
    ∀ (is : List V) (t : V), SpineFit ρp Ids is →
      t ∈ˢ SetTheory.app (fixFamI u 0 ρp Ids Ids.length rss tlss Eiss Fss₀ Ess) (tupW u is) →
      (∃ v, v ∈ˢ SetTheory.app
        (sqGraph ℓ u ρp M Ids (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 []) nF src m)
        (tupW u is)) ∧
      ∀ v v', v ∈ˢ SetTheory.app
          (sqGraph ℓ u ρp M Ids (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 []) nF src m)
          (tupW u is) →
        v' ∈ˢ SetTheory.app
          (sqGraph ℓ u ρp M Ids (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 []) nF src m)
          (tupW u is) → v = v' := by
  have hI : IdxOk u ρp Ids := hX.hI
  obtain ⟨hl₀, hlE, hEs', hlenj, hc⟩ := hreal
  -- the property: the graph's fibre is a singleton
  let G := sqGraph ℓ u ρp M Ids (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 []) nF src m
  let P : V → V → Prop := fun i _ =>
    ∀ is, SpineFit ρp Ids is → i = tupW u is →
      (∃ v, v ∈ˢ SetTheory.app G i) ∧
      ∀ v v', v ∈ˢ SetTheory.app G i → v' ∈ˢ SetTheory.app G i → v = v'
  have hpred : ∀ t, t ∈ˢ idxSet u ρp Ids →
      sqPred u ρp Ids (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 []) nF src t ⊆ˢ idxSet u ρp Ids :=
    fun _ _ => sep_subset
  have hind := lfpFamSet_induction (w := 0) (I := idxSet u ρp Ids)
    (F := fixFunVI u 0 ρp Ids Ids.length rss tlss Eiss Fss₀ Ess) (fixFunVI_closed_exists hX)
    (fixFunVI_mono hX) P ?_
  · intro is t hsp ht
    exact hind (tupW u is) (tupW_mem hsp) t ht is hsp rfl
  intro i hi x hx is hsp hi'
  subst hi'
  -- the induction family
  let S := graph (fun i => sep (SetTheory.app (lfpFamSet 0 (idxSet u ρp Ids)
    (fixFunVI u 0 ρp Ids Ids.length rss tlss Eiss Fss₀ Ess)) i) (P i)) (idxSet u ρp Ids)
  have hμS : fixFamI u 0 ρp Ids Ids.length rss tlss Eiss Fss₀ Ess
      ∈ˢ lfpFamSpace V 0 (idxSet u ρp Ids) := fixFamI_mem u 0 ρp Ids rss tlss Eiss Fss₀ Ess
  have hfibre : ∀ t', SetTheory.app (fixFamI u 0 ρp Ids Ids.length rss tlss Eiss Fss₀ Ess) t'
      ∈ˢ (univZero : V) := by
    intro t'
    by_cases ht' : t' ∈ˢ idxSet u ρp Ids
    · rw [lfpFamSpace_eq] at hμS
      have := famSpace_app hμS ht'
      rwa [univ_zero] at this
    · rw [lfpFamSpace_eq] at hμS
      rw [app_off_dom_piR_pos (Nat.succ_ne_zero 0) hμS ht']
      exact mem_univZero.mpr (empty_subset _)
  have hSmem : S ∈ˢ lfpFamSpace V 0 (idxSet u ρp Ids) := by
    rw [lfpFamSpace_eq]
    refine graph_mem_famSpace fun i hi => ?_
    rw [univ_zero]
    exact mem_univZero.mpr fun z hz => mem_univZero.mp (hfibre i) z (mem_sep.mp hz).1
  have hSle : FamLe (idxSet u ρp Ids) S (fixFamI u 0 ρp Ids Ids.length rss tlss Eiss Fss₀ Ess) := by
    intro i hi y hy
    rw [app_graph hi] at hy
    exact (mem_sep.mp hy).1
  rw [fixFunVI_app hSmem, famFI_app (tupW_mem hsp)] at hx
  obtain ⟨rfl, j, fs, hj₀, hlen₀, hspX, hall⟩ := fixStepI_zero_elim hx
  have hj : j = 0 := by rw [hl₀, hsingle] at hj₀; omega
  subst hj
  -- the spine fits the real fields, its index values are the tuple's
  have hfit := hX.hfit S hSmem _ (tupW_mem hsp) 0 hj₀
  have hj' : 0 < Fss.length := by rw [hsingle]; exact Nat.zero_lt_one
  have hspR := spineFit_real_of_XI hI hSle (Fss₀.getD 0 []) (Fss.getD 0 []) 0 [] fs rfl (hc 0 hj')
    hfit hspX
  have hlen : fs.length = (Fss.getD 0 []).length := by rw [hlen₀]; exact hlenj 0 hj'
  have hidx : idxValsAt ρp (Ess.getD 0 []) fs = is := by
    rw [← hlen₀] at hall
    exact idxValsAt_of_eqsXI hI hsp hEs hall
  have hfs : fs = srcVals is src := hsrc fs is hspR hsp hidx
  -- the local step at the predecessors
  -- the source spine is the spine
  have hsq : sqSpine u Ids.length src (tupW u is) = fs := by
    unfold sqSpine
    rw [isOfW_tupW hI hsp, hfs]
  refine recGraph_singleton_of_preds hB hpred (tupW_mem hsp)
    (hst is _ hsp rfl (by rw [hsq]; exact hspR) (by rw [hsq]; exact hidx)) fun j hj => ?_
  obtain ⟨-, i', hi', bs, hbs, rfl⟩ := mem_sep.mp hj
  obtain ⟨hik, hri⟩ := mem_recIdx.mp hi'
  have hri' : (rss.getD 0 []).getD (0 + i') false = true := by rw [Nat.zero_add]; exact hri
  obtain ⟨hslot, hmem⟩ := fitsXI_slot_mem hI (Fss₀.getD 0 []) 0 [] fs rfl hfit hspX i'
    (by rw [hlen, hlenF]; exact hik) hri'
  rw [Nat.zero_add, List.nil_append] at hslot hmem
  rw [hsq] at hbs ⊢
  -- the slot at the induction family: the predecessor's fibre is inhabited there
  unfold slotSet at hmem
  obtain ⟨y, hy⟩ := mem_piTele_zero hmem bs (fitsS_teleOfFields.mpr hbs)
  rw [List.nil_append] at hy
  obtain ⟨-, hvsp⟩ := hslot.2.2 bs hbs
  rw [consList_append] at hvsp
  have hmemI := tupW_mem (u := u) hvsp
  rw [app_graph hmemI] at hy
  obtain ⟨-, hPj⟩ := mem_sep.mp hy
  exact hPj _ hvsp rfl

/-! ## The family's spine at a tuple -/

/-- With no constructor the family is empty (task #210 Part B: the
zero-constructor blocks on the fixpoint route). -/
theorem fam_empty_of_mem (hX : XChainsOk u 0 ρp Ids rss tlss Eiss Fss₀ Ess)
    (hreal : ChainsRealI (fixFamI u 0 ρp Ids Ids.length rss tlss Eiss Fss₀ Ess) u 0 ρp Ids rss tlss
      Eiss Fss₀ Fss Ess)
    (hnil : Fss.length = 0) {is : List V} (hsp : SpineFit ρp Ids is) {t : V}
    (ht : t ∈ˢ SetTheory.app (fixFamI u 0 ρp Ids Ids.length rss tlss Eiss Fss₀ Ess) (tupW u is)) :
    False := by
  obtain ⟨hl₀, -, -, -, -⟩ := hreal
  have hμ := fixFamI_mem u 0 ρp Ids rss tlss Eiss Fss₀ Ess
  have hfix := lfpFamSet_fixed (fixFunVI_closed_exists hX) (fixFunVI_mono hX) (fixFunVI_maps hX) _
    (tupW_mem hsp) t ht
  unfold fixFamI at hμ
  rw [fixFunVI_app hμ, famFI_app (tupW_mem hsp)] at hfix
  obtain ⟨-, j, -, hj₀, -⟩ := fixStepI_zero_elim hfix
  rw [hl₀, hnil] at hj₀
  exact Nat.not_lt_zero _ hj₀

/-- At most one constructor and a member: exactly one. -/
theorem fam_single_of_mem (hX : XChainsOk u 0 ρp Ids rss tlss Eiss Fss₀ Ess)
    (hreal : ChainsRealI (fixFamI u 0 ρp Ids Ids.length rss tlss Eiss Fss₀ Ess) u 0 ρp Ids rss tlss
      Eiss Fss₀ Fss Ess)
    (hle : Fss.length ≤ 1) {is : List V} (hsp : SpineFit ρp Ids is) {t : V}
    (ht : t ∈ˢ SetTheory.app (fixFamI u 0 ρp Ids Ids.length rss tlss Eiss Fss₀ Ess) (tupW u is)) :
    Fss.length = 1 := by
  rcases Nat.lt_or_eq_of_le hle with h0 | h1
  · exact (fam_empty_of_mem hX hreal (by omega) hsp ht).elim
  · exact h1

/-- A proof at a tuple of the family (squash regime) is the point, and
some spine fits the (only) constructor's fields with the tuple as its
index values. -/
theorem fam_spine_of_mem (hX : XChainsOk u 0 ρp Ids rss tlss Eiss Fss₀ Ess)
    (hreal : ChainsRealI (fixFamI u 0 ρp Ids Ids.length rss tlss Eiss Fss₀ Ess) u 0 ρp Ids rss tlss
      Eiss Fss₀ Fss Ess)
    (hsingle : Fss.length = 1) (hEs : (Ess.getD 0 []).length = Ids.length)
    {is : List V} (hsp : SpineFit ρp Ids is) {t : V}
    (ht : t ∈ˢ SetTheory.app (fixFamI u 0 ρp Ids Ids.length rss tlss Eiss Fss₀ Ess) (tupW u is)) :
    t = pt ∧ ∃ fs : List V, SpineFit ρp (Fss.getD 0 []) fs ∧ idxValsAt ρp (Ess.getD 0 []) fs = is := by
  have hI : IdxOk u ρp Ids := hX.hI
  obtain ⟨hl₀, hlE, hEs', hlenj, hc⟩ := hreal
  have hμ := fixFamI_mem u 0 ρp Ids rss tlss Eiss Fss₀ Ess
  have hfix := lfpFamSet_fixed (fixFunVI_closed_exists hX) (fixFunVI_mono hX) (fixFunVI_maps hX) _
    (tupW_mem hsp) t ht
  unfold fixFamI at hμ
  rw [fixFunVI_app hμ, famFI_app (tupW_mem hsp)] at hfix
  obtain ⟨rfl, j, fs, hj₀, hlen₀, hspX, hall⟩ := fixStepI_zero_elim hfix
  have hj : j = 0 := by rw [hl₀, hsingle] at hj₀; omega
  subst hj
  have hfit := hX.hfit _ hμ _ (tupW_mem hsp) 0 hj₀
  have hj' : 0 < Fss.length := by rw [hsingle]; exact Nat.zero_lt_one
  refine ⟨rfl, fs, spineFit_real_of_XI hI (FamLe.refl _ _) (Fss₀.getD 0 []) (Fss.getD 0 []) 0 [] fs rfl
    (hc 0 hj') hfit hspX, ?_⟩
  rw [← hlen₀] at hall
  exact idxValsAt_of_eqsXI hI hsp hEs hall

end Singleton

/-! ## The squash body at a K-frame -/

omit [SetTheory V] in
theorem getD_append_lt {as bs : List V} {l : Nat} (d : V) (h : l < as.length) :
    (as ++ bs).getD l d = as.getD l d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

omit [SetTheory V] in
theorem getD_append_ge {as bs : List V} {l : Nat} (d : V) (h : as.length ≤ l) :
    (as ++ bs).getD l d = bs.getD (l - as.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

omit [SetTheory V] in
theorem getD_map_lt {α : Type} {L : List α} {f : α → V} {l : Nat} (h : l < L.length) (d : V) :
    (L.map f).getD l d = f L[l] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h, Option.map_some,
    Option.getD_some]

/-- Application chains concatenate. -/
theorem appChainOk_append {m : V} {as bs : List V} (h1 : AppChainOk m as)
    (h2 : AppChainOk (as.foldl SetTheory.app m) bs) : AppChainOk m (as ++ bs) := by
  intro l hl
  rw [List.length_append] at hl
  by_cases h : l < as.length
  · obtain ⟨v, A, B, hm, ha, hz⟩ := h1 l h
    refine ⟨v, A, B, ?_, ?_, hz⟩
    · rwa [List.take_append_of_le_length (Nat.le_of_lt h)]
    · rwa [getD_append_lt _ h]
  · obtain ⟨v, A, B, hm, ha, hz⟩ := h2 (l - as.length) (by omega)
    refine ⟨v, A, B, ?_, ?_, hz⟩
    · rwa [List.take_append, List.take_of_length_le (by omega), List.foldl_append]
    · rwa [getD_append_ge _ (by omega)]

/-- The conclusion at a walk leaf: the motive at the frame's index
tuple, at the major (a pure reading). -/
theorem interp_recConcAV_leaf (n nIdx : Nat) (t : V) (K : Nat → V) :
    interp V (cons t K) (recConcAV n nIdx)
      = SetTheory.app ((frameIdx nIdx K).foldl SetTheory.app (frM n nIdx K)) t := by
  have hfr : RecFrameS 1 K (cons t K) := by
    unfold RecFrameS
    rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
  unfold recConcAV motAppAV
  rw [interp_app, interp_mkAppN, ← List.foldl_map (f := interp V _) (g := SetTheory.app),
    map_idxVarsAV_interp hfr, interp_bvar, interp_bvar, cons_zero]
  congr 2
  exact hfr.motive

/-- The ih values of the squash body at a field spine: for each
recursive field, the λ-tower over its telescope of the function at the
block, the field's index values and the field applied to the
telescope's values. -/
noncomputable def sqIhValsK (ℓ : Nat) (ρP : Nat → V) (ps ms : List V) (M r : V) (rs : List Bool)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eis : List (List AnnotTerm)) (nF : Nat) (fs : List V) :
    List V :=
  (recIdx rs nF).map fun i =>
    lamTower ℓ (consList (fs.take i) ρP) (tls.getD i []) fun σ' =>
      ((ps ++ [M]) ++ ms ++ (Eis.getD i []).map (interp V σ') ++
        [(frameIdx (tls.getD i []).length σ').foldl SetTheory.app (fs.getD i pt)]).foldl
        SetTheory.app r

section Body

variable {ℓ u nP : Nat} {Fss Ess Fss₀ : List (List AnnotTerm)} {Ids : List AnnotTerm}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
  {Eiss : List (List (List AnnotTerm))} {rds : List (Nat × Nat × AnnotTerm)}

set_option maxHeartbeats 3200000 in
/-- **The squash body's facts** at a K-frame (task #202 A2): under the
major (a proof at a tuple of the family), the body is graded, reads to
the (only) minor at the source spine and the ih values (`sqIhValsK`,
the function at the predecessors), and lies in the conclusion. -/
theorem sqFixBody_facts (hℓ : ℓ ≠ 0) {ps ms is : List V} {M r t : V} {ρb : Nat → V}
    (hlenP : ps.length = nP) (hlenM : ms.length = Fss.length) (hlenI : is.length = Ids.length)
    (h : FixKI ℓ 0 u nP (consList is (consList ms (cons M (consList ps (cons r ρb))))) Fss Ess Fss₀
      Ids rss tlss Eiss rds)
    (ht : t ∈ˢ SetTheory.app
      (fixFamI u 0 (consList ps (cons r ρb)) Ids Ids.length rss tlss Eiss Fss₀ Ess) (tupW u is)) :
    WellDenoted V (cons t (consList is (consList ms (cons M (consList ps (cons r ρb))))))
      (sqFixBodyAV ℓ nP Fss.length Ids.length (Fss.getD 0 []) (Ess.getD 0 []) (rss.getD 0 [])
        (tlss.getD 0 []) (Eiss.getD 0 [])) ∧
    interp V (cons t (consList is (consList ms (cons M (consList ps (cons r ρb))))))
      (sqFixBodyAV ℓ nP Fss.length Ids.length (Fss.getD 0 []) (Ess.getD 0 []) (rss.getD 0 [])
        (tlss.getD 0 []) (Eiss.getD 0 []))
      = (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) ++
          sqIhValsK ℓ (consList ps (cons r ρb)) ps ms M r (rss.getD 0 []) (tlss.getD 0 [])
            (Eiss.getD 0 []) (Fss.getD 0 []).length
            (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length))).foldl
          SetTheory.app (ms.getD 0 pt) ∧
    interp V (cons t (consList is (consList ms (cons M (consList ps (cons r ρb))))))
      (sqFixBodyAV ℓ nP Fss.length Ids.length (Fss.getD 0 []) (Ess.getD 0 []) (rss.getD 0 [])
        (tlss.getD 0 []) (Eiss.getD 0 []))
      ∈ˢ SetTheory.app (is.foldl SetTheory.app M) pt := by
  obtain ⟨hle, hFok, hprop⟩ := h.hsq rfl hℓ
  -- the frame's accessors
  have hK : consList is (consList ms (cons M (consList ps (cons r ρb))))
      = consList (ps ++ [M] ++ ms ++ is) (cons r ρb) := (consList_kframe ps ms is M (cons r ρb)).symm
  have hlen₀ : (ps ++ [M] ++ ms).length = nP + 1 + Fss.length := by
    simp only [List.length_append, List.length_singleton]; omega
  have hlenAs : (ps ++ [M] ++ ms ++ is).length = nP + 1 + Fss.length + Ids.length := by
    rw [List.length_append, hlen₀, hlenI]
  have hfrP : frP Fss.length Ids.length (consList is (consList ms (cons M (consList ps (cons r ρb)))))
      = consList ps (cons r ρb) := by
    rw [hK, frP_of Fss.length Ids.length hlenI, List.append_assoc, consList_append,
      show Fss.length + 1 = ([M] ++ ms).length from by simp [hlenM], shiftE_consList]
  have hfrIdx : frameIdx Ids.length (consList is (consList ms (cons M (consList ps (cons r ρb))))) = is := by
    rw [← hlenI, frameIdx_consList']
  -- a member of the family: the (one) constructor (task #210 Part B)
  have hsingle : Fss.length = 1 := by
    have hX := h.hX
    have hreal := h.hreal
    rw [hfrP] at hX hreal
    have hfitI := h.hyp.hfit
    rw [hfrP, hfrIdx] at hfitI
    exact fam_single_of_mem hX hreal hle hfitI ht
  have hfrM : frM Fss.length Ids.length (consList is (consList ms (cons M (consList ps (cons r ρb)))))
      = M := by
    unfold frM
    rw [show Ids.length + Fss.length = (0 + ms.length) + is.length from by omega, consList_apply_add,
      consList_apply_add, cons_zero]
  have hfrMs : frMs Fss.length Ids.length (consList is (consList ms (cons M (consList ps (cons r ρb))))) 0
      = ms.getD 0 pt := by
    unfold frMs
    rw [show Ids.length + Fss.length - 1 - 0 = (Fss.length - 1) + is.length from by omega,
      consList_apply_add, consList_getD_lt ms _ _ (by omega),
      show ms.length - 1 - (Fss.length - 1) = 0 from by omega]
  have hfrR : frR nP Fss.length Ids.length (consList is (consList ms (cons M (consList ps (cons r ρb))))) = r := by
    rw [hK, frR_of nP Fss.length Ids.length hlenAs]
  have hfrB : frBelow nP Fss.length Ids.length (consList is (consList ms (cons M (consList ps (cons r ρb))))) = ρb := by
    rw [hK, frBelow_of nP Fss.length Ids.length hlenAs]
  have hfrK : frKSpine nP Fss.length Ids.length (consList is (consList ms (cons M (consList ps (cons r ρb)))))
      = ps ++ [M] ++ ms := by
    rw [hK, frKSpine_of nP Fss.length Ids.length hlen₀ hlenI]
  -- the squash data
  rw [hfrP] at hFok hprop
  have hX := h.hX
  have hreal := h.hreal
  rw [hfrP] at hX hreal
  have hI : IdxOk u (consList ps (cons r ρb)) Ids := hX.hI
  have hfitI := h.hyp.hfit
  rw [hfrP, hfrIdx] at hfitI
  have hEs0 : (Ess.getD 0 []).length = Ids.length := h.hyp.hEs 0 (by omega)
  obtain ⟨rfl, fs, hfsfit, hfsidx⟩ := fam_spine_of_mem hX hreal hsingle hEs0 hfitI ht
  have hfs₀ : fs = srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) :=
    srcVals_of_fit hprop hfsfit hfsidx
  -- the family's fibres are truth values
  have hμ := fixFamI_mem u 0 (consList ps (cons r ρb)) Ids rss tlss Eiss Fss₀ Ess
  have hfam : ∀ t', SetTheory.app
      (fixFamI u 0 (consList ps (cons r ρb)) Ids Ids.length rss tlss Eiss Fss₀ Ess) t'
      ∈ˢ (univZero : V) := by
    intro t'
    have := famApp_mem_univ hμ t'
    rwa [univ_zero] at this
  -- the slots along a fitting spine
  obtain ⟨hl₀, -, -, -, hc⟩ := hreal
  have hslot : ∀ fs' : List V, SpineFit (consList ps (cons r ρb)) (Fss.getD 0 []) fs' →
      ∀ i ∈ recIdx (rss.getD 0 []) (Fss.getD 0 []).length,
        SlotFit u 0 (consList ps (cons r ρb)) Ids ((tlss.getD 0 []).getD i []) ((Eiss.getD 0 []).getD i [])
          (fs'.take i) ∧
        fs'.getD i pt ∈ˢ slotSet 0 u (consList (fs'.take i) (consList ps (cons r ρb)))
          ((tlss.getD 0 []).getD i []) ((Eiss.getD 0 []).getD i [])
          (fixFamI u 0 (consList ps (cons r ρb)) Ids Ids.length rss tlss Eiss Fss₀ Ess) := by
    intro fs' hfit' i hi
    obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
    have := chainRealI_at (Fss₀.getD 0 []) (Fss.getD 0 []) 0 [] fs' rfl (hc 0 (by omega)) hfit' i hik
      (by rw [Nat.zero_add]; exact hri)
    rw [Nat.zero_add, List.nil_append] at this
    refine ⟨this.1, ?_⟩
    rw [← this.2]
    exact FixKI.spineFit_getD_mem' hfit' hik
  -- the function's typing at the frame
  have hrV := h.hrV
  rw [hfrR, hfrB] at hrV
  have hspine := h.hspine
  rw [hfrR, hfrB, hfrK, hfrP] at hspine
  have hz := h.hz
  -- the minor's typing at the frame
  have hms := h.hyp.hms 0 (by omega)
  rw [hfrMs, hfrP, hfrM] at hms
  have hconc0 : ℓ = 0 → ∀ as', SpineFit (cons r ρb) (rds.map (·.2.2)) as' →
      interp V (consList as' (cons r ρb)) (recConcAV Fss.length Ids.length) ∈ˢ (univZero : V) :=
    fun h0 => absurd h0 hℓ
  have hfam' : ∀ t', SetTheory.app
      (fixFamI u 0 (consList ps (cons r ρb)) Ids Ids.length rss tlss Eiss Fss₀ Ess) t'
      ∈ˢ (univ 0 : V) := by
    intro t'; rw [univ_zero]; exact hfam t'
  -- the frame under the major, in the reading's shape
  have hσ : cons pt (consList is (consList ms (cons M (consList ps (cons r ρb)))))
      = consList (is ++ [pt]) (consList ms (cons M (consList ps (cons r ρb)))) := consList_snoc' _ _ _
  have hlenE : (is ++ [pt]).length = Ids.length + 1 := by rw [length_snoc', hlenI]
  have hR : ∀ (fs' bs : List V), fs'.length = (Fss.getD 0 []).length →
      interp V (consList bs (consList fs' (consList (is ++ [pt]) (consList ms (cons M (consList ps (cons r ρb)))))))
        (.bvar (bs.length + (Fss.getD 0 []).length + 1 + Ids.length + Fss.length + 1 + nP)) = r := by
    intro fs' bs hlenF'
    rw [interp_bvar,
      show bs.length + (Fss.getD 0 []).length + 1 + Ids.length + Fss.length + 1 + nP
        = (((((0 + ps.length) + 1) + ms.length) + (is ++ [pt]).length) + fs'.length) + bs.length from by
        rw [hlenE, hlenM, hlenP, hlenF']; omega,
      consList_apply_add, consList_apply_add, consList_apply_add, consList_apply_add, cons_succ,
      consList_apply_add, cons_zero]
  -- ## the ih arguments at a fitting field spine
  have hms' : (ms ++ (is ++ [pt])).length + 1 = Fss.length + 1 + (Ids.length + 1) := by
    rw [List.length_append, hlenM, hlenE]; omega
  have hfr2 : ∀ fs' : List V, consList fs' (consList (is ++ [pt]) (consList ms (cons M (consList ps (cons r ρb)))))
      = consList [] (consList [] (consList fs' (consList (ms ++ (is ++ [pt])) (cons M (consList ps (cons r ρb)))))) := by
    intro fs'
    rw [consList_nil, consList_nil, consList_append ms (is ++ [pt])]
  have hih : ∀ fs' : List V, SpineFit (consList ps (cons r ρb)) (Fss.getD 0 []) fs' →
      ∀ i ∈ recIdx (rss.getD 0 []) (Fss.getD 0 []).length,
        WellDenoted V (consList fs' (cons pt (consList is (consList ms (cons M (consList ps (cons r ρb)))))))
          (ihAppAVb ℓ (fun m => .bvar (m + (Fss.getD 0 []).length + 1 + Ids.length + Fss.length + 1 + nP))
            nP Fss.length (Fss.getD 0 []).length (Ids.length + 1) i ((tlss.getD 0 []).getD i [])
            ((Eiss.getD 0 []).getD i [])) ∧
        interp V (consList fs' (cons pt (consList is (consList ms (cons M (consList ps (cons r ρb)))))))
          (ihAppAVb ℓ (fun m => .bvar (m + (Fss.getD 0 []).length + 1 + Ids.length + Fss.length + 1 + nP))
            nP Fss.length (Fss.getD 0 []).length (Ids.length + 1) i ((tlss.getD 0 []).getD i [])
            ((Eiss.getD 0 []).getD i []))
          = lamTower ℓ (consList (fs'.take i) (consList ps (cons r ρb))) ((tlss.getD 0 []).getD i []) (fun σ' =>
              ((ps ++ [M]) ++ ms ++ ((Eiss.getD 0 []).getD i []).map (interp V σ') ++
                [(frameIdx ((tlss.getD 0 []).getD i []).length σ').foldl SetTheory.app (fs'.getD i pt)]).foldl
                SetTheory.app r) ∧
        lamTower ℓ (consList (fs'.take i) (consList ps (cons r ρb))) ((tlss.getD 0 []).getD i []) (fun σ' =>
              ((ps ++ [M]) ++ ms ++ ((Eiss.getD 0 []).getD i []).map (interp V σ') ++
                [(frameIdx ((tlss.getD 0 []).getD i []).length σ').foldl SetTheory.app (fs'.getD i pt)]).foldl
                SetTheory.app r)
          ∈ˢ piTele ℓ (teleOfFields (consList (fs'.take i) (consList ps (cons r ρb)))
              (((tlss.getD 0 []).getD i []).map (·.2.2)))
              (fun as => SetTheory.app
                ((((Eiss.getD 0 []).getD i []).map
                  (interp V (consList as (consList (fs'.take i) (consList ps (cons r ρb)))))).foldl
                  SetTheory.app M)
                (as.foldl SetTheory.app (fs'.getD i pt))) [] := by
    intro fs' hfit' i hi
    obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
    have hlenF' : fs'.length = (Fss.getD 0 []).length := hfit'.length_eq
    obtain ⟨hslotfit, hslotmem⟩ := hslot fs' hfit' i hi
    have hread := interp_ihAppAVb (b := ℓ) (as₁ := ps) (ms := ms) (ex := is ++ [pt]) (fs := fs') (M := M)
      (ρ := cons r ρb) hlenP hlenM hlenE hlenF' hik
      (Rm := fun m => .bvar (m + (Fss.getD 0 []).length + 1 + Ids.length + Fss.length + 1 + nP)) (rV := r)
      (fun bs => hR fs' bs hlenF') ((tlss.getD 0 []).getD i []) ((Eiss.getD 0 []).getD i [])
    -- the leaves of the ih tower
    have hleaf : ∀ bs : List V,
        SpineFit (consList fs' (consList (is ++ [pt]) (consList ms (cons M (consList ps (cons r ρb))))))
          ((ihTeleAtR (Fss.getD 0 []).length (Fss.length + 1 + (Ids.length + 1)) i 0
            ((tlss.getD 0 []).getD i [])).map (·.2.2)) bs →
        WellDenoted V (consList bs (consList fs' (consList (is ++ [pt]) (consList ms (cons M (consList ps (cons r ρb)))))))
          (AnnotTerm.mkAppN (.bvar (((tlss.getD 0 []).getD i []).length + (Fss.getD 0 []).length + 1 + Ids.length + Fss.length + 1 + nP))
            (prefixVarsAV nP Fss.length (Fss.getD 0 []).length (((tlss.getD 0 []).getD i []).length + (Ids.length + 1)) ++
              ((Eiss.getD 0 []).getD i []).map (ihIdxAtM (Fss.getD 0 []).length (Fss.length + 1 + (Ids.length + 1)) i 0 ((tlss.getD 0 []).getD i []).length) ++
              [AnnotTerm.mkAppN (.bvar ((Fss.getD 0 []).length - 1 - i + ((tlss.getD 0 []).getD i []).length))
                (teleVarsAV ((tlss.getD 0 []).getD i []).length)])) ∧
        interp V (consList bs (consList fs' (consList (is ++ [pt]) (consList ms (cons M (consList ps (cons r ρb)))))))
          (AnnotTerm.mkAppN (.bvar (((tlss.getD 0 []).getD i []).length + (Fss.getD 0 []).length + 1 + Ids.length + Fss.length + 1 + nP))
            (prefixVarsAV nP Fss.length (Fss.getD 0 []).length (((tlss.getD 0 []).getD i []).length + (Ids.length + 1)) ++
              ((Eiss.getD 0 []).getD i []).map (ihIdxAtM (Fss.getD 0 []).length (Fss.length + 1 + (Ids.length + 1)) i 0 ((tlss.getD 0 []).getD i []).length) ++
              [AnnotTerm.mkAppN (.bvar ((Fss.getD 0 []).length - 1 - i + ((tlss.getD 0 []).getD i []).length))
                (teleVarsAV ((tlss.getD 0 []).getD i []).length)]))
          ∈ˢ SetTheory.app
              ((((Eiss.getD 0 []).getD i []).map
                (interp V (consList bs (consList (fs'.take i) (consList ps (cons r ρb)))))).foldl
                SetTheory.app M)
              (bs.foldl SetTheory.app (fs'.getD i pt)) ∧
        (ℓ = 0 → SetTheory.app
              ((((Eiss.getD 0 []).getD i []).map
                (interp V (consList bs (consList (fs'.take i) (consList ps (cons r ρb)))))).foldl
                SetTheory.app M)
              (bs.foldl SetTheory.app (fs'.getD i pt)) ∈ˢ (univZero : V)) := by
      intro bs hbs
      rw [hfr2] at hbs
      have hbs' : SpineFit (consList (fs'.take i) (consList ps (cons r ρb)))
          (((tlss.getD 0 []).getD i []).map (·.2.2)) bs := by
        have := (spineFit_ihTeleAtGo (M := M) (ρp := consList ps (cons r ρb)) hms' hlenF' (ihs := []) rfl
          (Nat.le_of_lt hik) ((tlss.getD 0 []).getD i []) [] bs).mp hbs
        rwa [consList_nil] at this
      have hlenbs : bs.length = ((tlss.getD 0 []).getD i []).length := by
        rw [hbs'.length_eq, List.length_map]
      obtain ⟨hEok, hv⟩ := hslotfit.2.2 bs hbs'
      rw [consList_append] at hEok hv
      have hf := slotSet_fold_mem hfam' hslotmem hbs'
      have hsp' := hspine _ _ hv hf
      have hchainR := appChainOk_of_mkPisAV' hz hconc0 hrV hsp'
      have hval := mkPisAV_fold_mem hz hconc0 hrV hsp'
      rw [← consList_snoc', interp_recConcAV_leaf, frameIdx_of Ids.length hv.length_eq,
        frM_of Fss.length Ids.length hv.length_eq, List.append_assoc ps [M] ms, consList_append ps ([M] ++ ms),
        consList_append [M] ms, show Fss.length = 0 + ms.length from by omega, consList_apply_add,
        consList_cons, consList_nil, cons_zero] at hval
      rw [← hlenbs]
      have hargs := ihAppAVb_args_interp (bs := bs) (M := M) (ρ := cons r ρb) hlenP hlenM hlenE hlenF' hik
        ((Eiss.getD 0 []).getD i [])
      rw [frameIdx_consList'] at hargs
      rw [← List.append_assoc] at hval
      have hok : ∀ a ∈ prefixVarsAV nP Fss.length (Fss.getD 0 []).length (bs.length + (Ids.length + 1)) ++
          ((Eiss.getD 0 []).getD i []).map (ihIdxAtM (Fss.getD 0 []).length (Fss.length + 1 + (Ids.length + 1)) i 0 bs.length) ++
          [AnnotTerm.mkAppN (.bvar ((Fss.getD 0 []).length - 1 - i + bs.length)) (teleVarsAV bs.length)],
          WellDenoted V (consList bs (consList fs' (consList (is ++ [pt]) (consList ms (cons M (consList ps (cons r ρb))))))) a := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · rcases List.mem_append.mp ha with ha | ha
          · exact prefixVarsAV_wellDenoted ha
          · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
            rw [hfr2, consList_nil]
            have := (WellDenoted_ihIdxAtM (M := M) (ρp := consList ps (cons r ρb)) hms' hlenF' (ihs := []) rfl
              (Nat.le_of_lt hik) bs E).mpr (hEok E hE)
            rwa [consList_nil] at this
        · rw [List.mem_singleton] at ha
          subst ha
          have hchainF : AppChainOk (fs'.getD i pt) bs := slotSet_chainOk hfam' hslotmem hbs'
          refine (mkAppN_wellDenoted_of_chain
            (σ := consList bs (consList fs' (consList (is ++ [pt]) (consList ms (cons M (consList ps (cons r ρb)))))))
            (f := .bvar ((Fss.getD 0 []).length - 1 - i + bs.length)) (args := teleVarsAV bs.length) trivial
            (fun a ha => teleVarsAV_wellDenoted ha) ?_).1
          rw [map_teleVarsAV_interp, interp_bvar, consList_apply_add, consList_getD_lt fs' _ _ (by omega),
            show fs'.length - 1 - ((Fss.getD 0 []).length - 1 - i) = i from by omega]
          exact hchainF
      have hchain := mkAppN_wellDenoted_of_chain (σ := consList bs (consList fs' (consList (is ++ [pt]) (consList ms (cons M (consList ps (cons r ρb)))))))
        (f := .bvar (bs.length + (Fss.getD 0 []).length + 1 + Ids.length + Fss.length + 1 + nP)) trivial hok
        (by rw [hargs, hR fs' bs hlenF']; exact hchainR)
      refine ⟨hchain.1, ?_, fun h0 => absurd h0 hℓ⟩
      rw [hchain.2, hargs, hR fs' bs hlenF']
      exact hval
    -- the walk
    have hwalk : DomsWalk (consList fs' (consList (is ++ [pt]) (consList ms (cons M (consList ps (cons r ρb))))))
        (ihTeleAtR (Fss.getD 0 []).length (Fss.length + 1 + (Ids.length + 1)) i 0 ((tlss.getD 0 []).getD i [])) := by
      rw [hfr2]
      refine domsWalk_of_fieldsOkB (w := 0) ?_
      have := fieldsOkB_ihTeleAtGo (w := 0) (M := M) (ρp := consList ps (cons r ρb)) hms' hlenF' (ihs := []) rfl
        (Nat.le_of_lt hik) ((tlss.getD 0 []).getD i []) [] (by rw [consList_nil]; exact hslotfit.1)
      exact this
    have hfacts := mkLamsC_factsB (underTowerOkB_of_leaves
      (B := fun as => SetTheory.app
        ((((Eiss.getD 0 []).getD i []).map
          (interp V (consList as (consList (fs'.take i) (consList ps (cons r ρb)))))).foldl SetTheory.app M)
        (as.foldl SetTheory.app (fs'.getD i pt))) (acc := []) hwalk
      (fun bs hbs => by simpa only [List.nil_append] using hleaf bs hbs))
    rw [hσ]
    refine ⟨hfacts.1, hread, ?_⟩
    have hmem := hfacts.2
    have hread' := hread
    unfold ihAppAVb at hread'
    rw [hread'] at hmem
    unfold ihTeleAtR at hmem
    rw [hfr2] at hmem
    have hp := piTele_ihTeleAtGo (v := ℓ) (M := M) (ρp := consList ps (cons r ρb))
      (B := fun as => SetTheory.app
        ((((Eiss.getD 0 []).getD i []).map
          (interp V (consList as (consList (fs'.take i) (consList ps (cons r ρb)))))).foldl SetTheory.app M)
        (as.foldl SetTheory.app (fs'.getD i pt)))
      hms' hlenF' (ihs := []) rfl (Nat.le_of_lt hik) ((tlss.getD 0 []).getD i []) [] []
    simp only [List.length_nil] at hp
    rw [hp, consList_nil] at hmem
    exact hmem
  -- ## the inner body at a fitting field spine
  have hinner : ∀ fs' : List V, SpineFit (consList ps (cons r ρb)) (Fss.getD 0 []) fs' →
      WellDenoted V (consList fs' (cons pt (consList is (consList ms (cons M (consList ps (cons r ρb)))))))
        (AnnotTerm.mkAppN (.bvar ((Fss.getD 0 []).length + 1 + Ids.length + Fss.length - 1))
          (teleVarsAV (Fss.getD 0 []).length ++ (recIdx (rss.getD 0 []) (Fss.getD 0 []).length).map fun i =>
            ihAppAVb ℓ (fun m => .bvar (m + (Fss.getD 0 []).length + 1 + Ids.length + Fss.length + 1 + nP)) nP
              Fss.length (Fss.getD 0 []).length (Ids.length + 1) i ((tlss.getD 0 []).getD i [])
              ((Eiss.getD 0 []).getD i []))) ∧
      interp V (consList fs' (cons pt (consList is (consList ms (cons M (consList ps (cons r ρb)))))))
        (AnnotTerm.mkAppN (.bvar ((Fss.getD 0 []).length + 1 + Ids.length + Fss.length - 1))
          (teleVarsAV (Fss.getD 0 []).length ++ (recIdx (rss.getD 0 []) (Fss.getD 0 []).length).map fun i =>
            ihAppAVb ℓ (fun m => .bvar (m + (Fss.getD 0 []).length + 1 + Ids.length + Fss.length + 1 + nP)) nP
              Fss.length (Fss.getD 0 []).length (Ids.length + 1) i ((tlss.getD 0 []).getD i [])
              ((Eiss.getD 0 []).getD i [])))
        = (fs' ++ sqIhValsK ℓ (consList ps (cons r ρb)) ps ms M r (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 [])
            (Fss.getD 0 []).length fs').foldl SetTheory.app (ms.getD 0 pt) ∧
      interp V (consList fs' (cons pt (consList is (consList ms (cons M (consList ps (cons r ρb)))))))
        (AnnotTerm.mkAppN (.bvar ((Fss.getD 0 []).length + 1 + Ids.length + Fss.length - 1))
          (teleVarsAV (Fss.getD 0 []).length ++ (recIdx (rss.getD 0 []) (Fss.getD 0 []).length).map fun i =>
            ihAppAVb ℓ (fun m => .bvar (m + (Fss.getD 0 []).length + 1 + Ids.length + Fss.length + 1 + nP)) nP
              Fss.length (Fss.getD 0 []).length (Ids.length + 1) i ((tlss.getD 0 []).getD i [])
              ((Eiss.getD 0 []).getD i [])))
        ∈ˢ SetTheory.app ((idxValsAt (consList ps (cons r ρb)) (Ess.getD 0 []) fs').foldl SetTheory.app M) pt := by
    intro fs' hfit'
    have hlenF' : fs'.length = (Fss.getD 0 []).length := hfit'.length_eq
    have hminor : interp V (consList fs' (cons pt (consList is (consList ms (cons M (consList ps (cons r ρb)))))))
        (.bvar ((Fss.getD 0 []).length + 1 + Ids.length + Fss.length - 1)) = ms.getD 0 pt := by
      rw [interp_bvar,
        show (Fss.getD 0 []).length + 1 + Ids.length + Fss.length - 1
          = (((Fss.length - 1) + is.length) + 1) + fs'.length from by rw [hlenI, hlenF']; omega,
        consList_apply_add, cons_succ, consList_apply_add, consList_getD_lt ms _ _ (by omega),
        show ms.length - 1 - (Fss.length - 1) = 0 from by omega]
    have hargs : (teleVarsAV (Fss.getD 0 []).length ++ (recIdx (rss.getD 0 []) (Fss.getD 0 []).length).map fun i =>
          ihAppAVb ℓ (fun m => .bvar (m + (Fss.getD 0 []).length + 1 + Ids.length + Fss.length + 1 + nP)) nP
            Fss.length (Fss.getD 0 []).length (Ids.length + 1) i ((tlss.getD 0 []).getD i [])
            ((Eiss.getD 0 []).getD i [])).map
          (interp V (consList fs' (cons pt (consList is (consList ms (cons M (consList ps (cons r ρb))))))))
        = fs' ++ sqIhValsK ℓ (consList ps (cons r ρb)) ps ms M r (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 [])
            (Fss.getD 0 []).length fs' := by
      rw [List.map_append, map_teleVarsAV_interp' hlenF', List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      simp only [Function.comp_def]
      exact (hih fs' hfit' i hi).2.1
    have hfold := minorSpI_fold (fun h0 => absurd h0 hℓ) hms hfit'
    rw [List.nil_append] at hfold
    have hlenIh : (sqIhValsK ℓ (consList ps (cons r ρb)) ps ms M r (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 [])
        (Fss.getD 0 []).length fs').length
        = (ihDomsI ℓ (consList ps (cons r ρb)) M rss tlss Eiss (fun j => (Fss.getD j []).length) 0 fs').length := by
      simp [sqIhValsK, ihDomsI]
    have hmemIh : ∀ l, l < (ihDomsI ℓ (consList ps (cons r ρb)) M rss tlss Eiss (fun j => (Fss.getD j []).length) 0 fs').length →
        (sqIhValsK ℓ (consList ps (cons r ρb)) ps ms M r (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 [])
          (Fss.getD 0 []).length fs').getD l pt
        ∈ˢ (ihDomsI ℓ (consList ps (cons r ρb)) M rss tlss Eiss (fun j => (Fss.getD j []).length) 0 fs').getD l pt := by
      intro l hl
      have hl' : l < (recIdx (rss.getD 0 []) (Fss.getD 0 []).length).length := by
        simpa [ihDomsI] using hl
      have hi : (recIdx (rss.getD 0 []) (Fss.getD 0 []).length)[l] ∈ recIdx (rss.getD 0 []) (Fss.getD 0 []).length :=
        List.getElem_mem hl'
      unfold sqIhValsK ihDomsI
      show _ ∈ˢ (List.map _ (recIdx (rss.getD 0 []) (Fss.getD 0 []).length)).getD l pt
      rw [getD_map_lt hl', getD_map_lt hl']
      exact (hih fs' hfit' _ hi).2.2
    have hchain := mkAppN_wellDenoted_of_chain
      (σ := consList fs' (cons pt (consList is (consList ms (cons M (consList ps (cons r ρb)))))))
      (f := .bvar ((Fss.getD 0 []).length + 1 + Ids.length + Fss.length - 1))
      (args := teleVarsAV (Fss.getD 0 []).length ++ (recIdx (rss.getD 0 []) (Fss.getD 0 []).length).map fun i =>
        ihAppAVb ℓ (fun m => .bvar (m + (Fss.getD 0 []).length + 1 + Ids.length + Fss.length + 1 + nP)) nP
          Fss.length (Fss.getD 0 []).length (Ids.length + 1) i ((tlss.getD 0 []).getD i [])
          ((Eiss.getD 0 []).getD i [])) trivial
      (fun a ha => by
        rcases List.mem_append.mp ha with ha | ha
        · exact teleVarsAV_wellDenoted ha
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
          exact (hih fs' hfit' i hi).1)
      (by
        rw [hargs, hminor]
        exact appChainOk_append (minorSpI_appChainOk (fun h0 => absurd h0 hℓ) hms hfit')
          (ihSpL_appChainOk (fun h0 => absurd h0 hℓ) hfold hlenIh hmemIh))
    refine ⟨hchain.1, by rw [hchain.2, hargs, hminor], ?_⟩
    rw [hchain.2, hargs, hminor, List.foldl_append]
    have := ihSpL_fold (fun h0 => absurd h0 hℓ) hfold hlenIh hmemIh
    unfold concI ctorValI at this
    rw [if_pos rfl] at this
    exact this
  -- ## the outer tower and its application to the sources
  have hshift : shiftE (Ids.length + Fss.length + 2) 0 (cons pt (consList is (consList ms (cons M (consList ps (cons r ρb))))))
      = consList ps (cons r ρb) := by
    rw [hσ, show cons M (consList ps (cons r ρb)) = consList [M] (consList ps (cons r ρb)) from rfl,
      ← consList_append, ← consList_append,
      show Ids.length + Fss.length + 2 = ([M] ++ (ms ++ (is ++ [pt]))).length from by
        simp only [List.length_append, List.length_singleton, hlenM, hlenI]; omega,
      shiftE_consList]
  have hdoms : (fieldTeleAt (Ids.length + Fss.length + 2) (Fss.getD 0 [])).map (·.2.2)
      = liftFields (Ids.length + Fss.length + 2) 0 (Fss.getD 0 []) := by
    simp only [fieldTeleAt, List.map_map, Function.comp_def, List.map_id']
  have hwalkF : DomsWalk (cons pt (consList is (consList ms (cons M (consList ps (cons r ρb))))))
      (fieldTeleAt (Ids.length + Fss.length + 2) (Fss.getD 0 [])) := by
    refine domsWalk_of_fieldsOkB (w := 0) ?_
    rw [hdoms, FieldsOkB_liftFields, hshift]
    exact hFok
  have hleafF : ∀ bs : List V, SpineFit (cons pt (consList is (consList ms (cons M (consList ps (cons r ρb))))))
      ((fieldTeleAt (Ids.length + Fss.length + 2) (Fss.getD 0 [])).map (·.2.2)) bs →
      WellDenoted V (consList bs (cons pt (consList is (consList ms (cons M (consList ps (cons r ρb)))))))
        (AnnotTerm.mkAppN (.bvar ((Fss.getD 0 []).length + 1 + Ids.length + Fss.length - 1))
          (teleVarsAV (Fss.getD 0 []).length ++ (recIdx (rss.getD 0 []) (Fss.getD 0 []).length).map fun i =>
            ihAppAVb ℓ (fun m => .bvar (m + (Fss.getD 0 []).length + 1 + Ids.length + Fss.length + 1 + nP)) nP
              Fss.length (Fss.getD 0 []).length (Ids.length + 1) i ((tlss.getD 0 []).getD i [])
              ((Eiss.getD 0 []).getD i []))) ∧
      interp V (consList bs (cons pt (consList is (consList ms (cons M (consList ps (cons r ρb)))))))
        (AnnotTerm.mkAppN (.bvar ((Fss.getD 0 []).length + 1 + Ids.length + Fss.length - 1))
          (teleVarsAV (Fss.getD 0 []).length ++ (recIdx (rss.getD 0 []) (Fss.getD 0 []).length).map fun i =>
            ihAppAVb ℓ (fun m => .bvar (m + (Fss.getD 0 []).length + 1 + Ids.length + Fss.length + 1 + nP)) nP
              Fss.length (Fss.getD 0 []).length (Ids.length + 1) i ((tlss.getD 0 []).getD i [])
              ((Eiss.getD 0 []).getD i [])))
        ∈ˢ SetTheory.app ((idxValsAt (consList ps (cons r ρb)) (Ess.getD 0 []) ([] ++ bs)).foldl SetTheory.app M) pt ∧
      (ℓ = 0 → SetTheory.app ((idxValsAt (consList ps (cons r ρb)) (Ess.getD 0 []) ([] ++ bs)).foldl SetTheory.app M) pt
        ∈ˢ (univZero : V)) := by
    intro bs hbs
    rw [hdoms, spineFit_liftFields, hshift] at hbs
    rw [List.nil_append]
    exact ⟨(hinner bs hbs).1, (hinner bs hbs).2.2, fun h0 => absurd h0 hℓ⟩
  have hfactsF := mkLamsC_factsB (underTowerOkB_of_leaves
    (B := fun as => SetTheory.app ((idxValsAt (consList ps (cons r ρb)) (Ess.getD 0 []) as).foldl SetTheory.app M) pt)
    (acc := []) hwalkF hleafF)
  -- the sources read to the source spine
  have hfr1 : RecFrameS 1 (consList is (consList ms (cons M (consList ps (cons r ρb)))))
      (cons pt (consList is (consList ms (cons M (consList ps (cons r ρb)))))) := by
    unfold RecFrameS
    rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
  have hsrcv : ((srcList (Ess.getD 0 []) (Fss.getD 0 []).length).map (srcAV Ids.length 1)).map
      (interp V (cons pt (consList is (consList ms (cons M (consList ps (cons r ρb)))))))
      = srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) := by
    rw [map_srcAV_interp hfr1 _ (fun s hs l hl => by rw [← hEs0]; exact srcList_bound s hs l hl), hfrIdx]
  have hfitS : SpineFit (cons pt (consList is (consList ms (cons M (consList ps (cons r ρb))))))
      ((fieldTeleAt (Ids.length + Fss.length + 2) (Fss.getD 0 [])).map (·.2.2))
      (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)) := by
    rw [hdoms, spineFit_liftFields, hshift, ← hfs₀]
    exact hfsfit
  have hchainF : AppChainOk
      (interp V (cons pt (consList is (consList ms (cons M (consList ps (cons r ρb))))))
        (mkLamsC ℓ (fieldTeleAt (Ids.length + Fss.length + 2) (Fss.getD 0 []))
          (AnnotTerm.mkAppN (.bvar ((Fss.getD 0 []).length + 1 + Ids.length + Fss.length - 1))
            (teleVarsAV (Fss.getD 0 []).length ++ (recIdx (rss.getD 0 []) (Fss.getD 0 []).length).map fun i =>
              ihAppAVb ℓ (fun m => .bvar (m + (Fss.getD 0 []).length + 1 + Ids.length + Fss.length + 1 + nP)) nP
                Fss.length (Fss.getD 0 []).length (Ids.length + 1) i ((tlss.getD 0 []).getD i [])
                ((Eiss.getD 0 []).getD i [])))))
      (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)) :=
    appChainOk_of_piTele hℓ hfactsF.2 (fitsS_teleOfFields.mpr hfitS)
  have hβ : (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)).foldl SetTheory.app
      (interp V (cons pt (consList is (consList ms (cons M (consList ps (cons r ρb))))))
        (mkLamsC ℓ (fieldTeleAt (Ids.length + Fss.length + 2) (Fss.getD 0 []))
          (AnnotTerm.mkAppN (.bvar ((Fss.getD 0 []).length + 1 + Ids.length + Fss.length - 1))
            (teleVarsAV (Fss.getD 0 []).length ++ (recIdx (rss.getD 0 []) (Fss.getD 0 []).length).map fun i =>
              ihAppAVb ℓ (fun m => .bvar (m + (Fss.getD 0 []).length + 1 + Ids.length + Fss.length + 1 + nP)) nP
                Fss.length (Fss.getD 0 []).length (Ids.length + 1) i ((tlss.getD 0 []).getD i [])
                ((Eiss.getD 0 []).getD i [])))))
      = interp V (consList (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length))
          (cons pt (consList is (consList ms (cons M (consList ps (cons r ρb)))))))
          (AnnotTerm.mkAppN (.bvar ((Fss.getD 0 []).length + 1 + Ids.length + Fss.length - 1))
            (teleVarsAV (Fss.getD 0 []).length ++ (recIdx (rss.getD 0 []) (Fss.getD 0 []).length).map fun i =>
              ihAppAVb ℓ (fun m => .bvar (m + (Fss.getD 0 []).length + 1 + Ids.length + Fss.length + 1 + nP)) nP
                Fss.length (Fss.getD 0 []).length (Ids.length + 1) i ((tlss.getD 0 []).getD i [])
                ((Eiss.getD 0 []).getD i []))) := by
    unfold mkLamsC
    refine mkLamsAV_fold (fun d hd => ?_) ?_
    · obtain ⟨d', -, rfl⟩ := List.mem_map.mp hd
      exact hℓ
    · rw [List.map_map]
      exact hfitS
  have hall := mkAppN_wellDenoted_of_chain (σ := cons pt (consList is (consList ms (cons M (consList ps (cons r ρb))))))
    (args := (srcList (Ess.getD 0 []) (Fss.getD 0 []).length).map (srcAV Ids.length 1)) hfactsF.1
    (fun a ha => by obtain ⟨s, -, rfl⟩ := List.mem_map.mp ha; exact srcAV_wellDenoted _ _ _ _)
    (by rw [hsrcv]; exact hchainF)
  have hinner₀ := hinner _ hfsfit
  rw [hfs₀] at hinner₀ hfsidx
  unfold sqFixBodyAV
  refine ⟨hall.1, ?_, ?_⟩
  · rw [hall.2, hsrcv, hβ]
    exact hinner₀.2.1
  · rw [hall.2, hsrcv, hβ]
    have := hinner₀.2.2
    rw [hfsidx] at this
    exact this

/-! ## The recursor's value at a K-frame -/

/-- A tuple of the index set is the tuple of a fitting spine. -/
theorem mem_idxSet_elim {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {t : V}
    (ht : t ∈ˢ idxSet u ρp Ids) : ∃ is : List V, SpineFit ρp Ids is ∧ t = tupW u is := by
  by_cases hu : u = 0
  · subst hu
    obtain ⟨rfl, as, has⟩ := towerSet_zero_elim (teleOfFields ρp Ids) ht
    exact ⟨as, fitsS_teleOfFields.mp has, (tupW_zero as).symm⟩
  · obtain ⟨hsp, heq⟩ := towerSet_elim_teleOfFields hu ht
    exact ⟨_, hsp, by rw [tupW_pos hu]; exact heq⟩

/-- λ-towers at zeroness-agreeing bits agree. -/
theorem lamTower_bit_agree {m m' : Nat} (hz : m = 0 ↔ m' = 0) {g : (Nat → V) → V} :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (ρ : Nat → V), lamTower m ρ ds g = lamTower m' ρ ds g
  | [], _ => rfl
  | d :: ds, ρ => by
    show lamR m (interp V ρ d.2.2) (fun a => lamTower m (cons a ρ) ds g)
      = lamR m' (interp V ρ d.2.2) (fun a => lamTower m' (cons a ρ) ds g)
    exact lamR_zero_agree hz fun a _ => lamTower_bit_agree hz ds (cons a ρ)

/-- λ-towers with bodies agreeing at every fitting leaf agree. -/
theorem lamTower_congr_leaves {m : Nat} {g₁ g₂ : (Nat → V) → V} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      (∀ bs, SpineFit ρ (ds.map (·.2.2)) bs → g₁ (consList bs ρ) = g₂ (consList bs ρ)) →
      lamTower m ρ ds g₁ = lamTower m ρ ds g₂
  | [], ρ, hg => hg [] trivial
  | d :: ds, ρ, hg => by
    show lamR m (interp V ρ d.2.2) (fun a => lamTower m (cons a ρ) ds g₁)
      = lamR m (interp V ρ d.2.2) (fun a => lamTower m (cons a ρ) ds g₂)
    refine lamR_congr fun a ha => lamTower_congr_leaves fun bs hbs => hg (a :: bs) ⟨ha, hbs⟩

omit [SetTheory V] in
/-- The K-frame accessors in list form. -/
theorem kframe_frP' {n nIdx : Nat} {is ms : List V} {M : V} {ρP : Nat → V} (hlenI : is.length = nIdx)
    (hlenM : ms.length = n) : frP n nIdx (consList is (consList ms (cons M ρP))) = ρP := by
  unfold frP
  rw [show cons M ρP = consList [M] ρP from rfl, ← consList_append, ← consList_append,
    show nIdx + n + 1 = ([M] ++ (ms ++ is)).length from by
      simp only [List.length_append, List.length_singleton, hlenI, hlenM]; omega,
    shiftE_consList]

omit [SetTheory V] in
theorem kframe_frM' {n nIdx : Nat} {is ms : List V} {M : V} {ρP : Nat → V} (hlenI : is.length = nIdx)
    (hlenM : ms.length = n) : frM n nIdx (consList is (consList ms (cons M ρP))) = M := by
  unfold frM
  rw [show nIdx + n = (0 + ms.length) + is.length from by omega, consList_apply_add, consList_apply_add,
    cons_zero]

theorem kframe_frMs' {n nIdx : Nat} {is ms : List V} {M : V} {ρP : Nat → V} (hlenI : is.length = nIdx)
    (hlenM : ms.length = n) (hn : 0 < n) :
    frMs n nIdx (consList is (consList ms (cons M ρP))) 0 = ms.getD 0 pt := by
  unfold frMs
  rw [show nIdx + n - 1 - 0 = (n - 1) + is.length from by omega, consList_apply_add,
    consList_getD_lt ms _ _ (by omega), show ms.length - 1 - (n - 1) = 0 from by omega]

omit [SetTheory V] in
theorem kframe_frameIdx' {nIdx : Nat} {is : List V} (hlenI : is.length = nIdx) (ρ : Nat → V) :
    frameIdx nIdx (consList is ρ) = is := by
  rw [← hlenI, frameIdx_consList']

/-- A spine of the recursor's binder length splits into the parameters,
the motive, the minors and the indices. -/
theorem kframe_split3 {as : List V} {nP n nIdx : Nat} (h : as.length = nP + 1 + n + nIdx) :
    ∃ (ps ms is : List V) (M : V), as = ps ++ [M] ++ ms ++ is ∧ ps.length = nP ∧ ms.length = n ∧
      is.length = nIdx := by
  refine ⟨as.take nP, (as.drop (nP + 1)).take n, as.drop (nP + 1 + n), as.getD nP pt, ?_, ?_, ?_, ?_⟩
  · have h1 : as = as.take nP ++ as.drop nP := (List.take_append_drop _ _).symm
    have h2 : as.drop nP = as.getD nP pt :: as.drop (nP + 1) := by
      rw [List.drop_eq_getElem_cons (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)]
      rfl
    have h3 : as.drop (nP + 1) = (as.drop (nP + 1)).take n ++ as.drop (nP + 1 + n) := by
      have := (List.take_append_drop n (as.drop (nP + 1))).symm
      rwa [List.drop_drop] at this
    calc as = as.take nP ++ as.drop nP := h1
      _ = as.take nP ++ (as.getD nP pt :: as.drop (nP + 1)) := by rw [h2]
      _ = as.take nP ++ (as.getD nP pt :: ((as.drop (nP + 1)).take n ++ as.drop (nP + 1 + n))) := by
          rw [← h3]
      _ = as.take nP ++ [as.getD nP pt] ++ (as.drop (nP + 1)).take n ++ as.drop (nP + 1 + n) := by simp
  · rw [List.length_take]; omega
  · rw [List.length_take, List.length_drop]; omega
  · rw [List.length_drop]; omega

/-- The recursive slots along a fitting spine at a K-frame (squash
regime): the slot fits and the field lies in the slot's value. -/
theorem fixKI₀_slot {K ρP : Nat → V} (h : FixKI₀ ℓ 0 u K Fss Ess Fss₀ Ids rss tlss Eiss)
    (hfrP : frP Fss.length Ids.length K = ρP) (hsingle : Fss.length = 1) :
    ∀ fs' : List V, SpineFit ρP (Fss.getD 0 []) fs' →
      ∀ i ∈ recIdx (rss.getD 0 []) (Fss.getD 0 []).length,
        SlotFit u 0 ρP Ids ((tlss.getD 0 []).getD i []) ((Eiss.getD 0 []).getD i []) (fs'.take i) ∧
        fs'.getD i pt ∈ˢ slotSet 0 u (consList (fs'.take i) ρP) ((tlss.getD 0 []).getD i [])
          ((Eiss.getD 0 []).getD i []) (fixFamI u 0 ρP Ids Ids.length rss tlss Eiss Fss₀ Ess) := by
  obtain ⟨hl₀, -, -, -, hc⟩ := h.hreal
  rw [hfrP] at hc
  intro fs' hfit' i hi
  obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
  have := chainRealI_at (Fss₀.getD 0 []) (Fss.getD 0 []) 0 [] fs' rfl (hc 0 (by omega)) hfit' i hik
    (by rw [Nat.zero_add]; exact hri)
  rw [Nat.zero_add, List.nil_append] at this
  refine ⟨this.1, ?_⟩
  rw [← this.2]
  exact FixKI.spineFit_getD_mem' hfit' hik

/-- At a tuple of the family (squash regime) the major is the point,
and the source spine fits the fields with the tuple as its index
values. -/
theorem sqK_source (hℓ : ℓ ≠ 0) {K ρP : Nat → V} (h : FixKI₀ ℓ 0 u K Fss Ess Fss₀ Ids rss tlss Eiss)
    (hfrP : frP Fss.length Ids.length K = ρP) {is : List V} (hsp : SpineFit ρP Ids is) {t : V}
    (ht : t ∈ˢ SetTheory.app (fixFamI u 0 ρP Ids Ids.length rss tlss Eiss Fss₀ Ess) (tupW u is)) :
    t = pt ∧ SpineFit ρP (Fss.getD 0 []) (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)) ∧
      idxValsAt ρP (Ess.getD 0 []) (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)) = is := by
  obtain ⟨hle, -, hprop⟩ := h.hsq rfl hℓ
  rw [hfrP] at hprop
  have hX := h.hX
  have hreal := h.hreal
  rw [hfrP] at hX hreal
  have hsingle : Fss.length = 1 := fam_single_of_mem hX hreal hle hsp ht
  have hEs0 : (Ess.getD 0 []).length = Ids.length := h.hyp.hEs 0 (by omega)
  obtain ⟨rfl, fs, hfsfit, hfsidx⟩ := fam_spine_of_mem hX hreal hsingle hEs0 hsp ht
  have hfs₀ := srcVals_of_fit hprop hfsfit hfsidx
  rw [hfs₀] at hfsfit hfsidx
  exact ⟨rfl, hfsfit, hfsidx⟩

set_option maxHeartbeats 3200000 in
/-- **The recursor's value at a K-frame** (squash regime, task #202
A2): the graph's selector at every tuple of the family is in the
motive's fibre at the tuple, and satisfies the recursion equation —
the minor at the source spine and, for each recursive field, the
λ-tower over its telescope of the selector at the call's tuple. -/
theorem sqK_facts (hℓ : ℓ ≠ 0) {ρP : Nat → V} {M m : V} {K : Nat → V}
    (h : FixKI₀ ℓ 0 u K Fss Ess Fss₀ Ids rss tlss Eiss)
    (hfrP : frP Fss.length Ids.length K = ρP)
    (hfrM : frM Fss.length Ids.length K = M)
    (hfrMs : frMs Fss.length Ids.length K 0 = m) :
    ∀ (is : List V) (t : V), SpineFit (ρP) Ids is →
      t ∈ˢ SetTheory.app (fixFamI u 0 (ρP) Ids Ids.length rss tlss Eiss Fss₀ Ess)
        (tupW u is) →
      (∃ v, v ∈ˢ SetTheory.app
        (sqGraph ℓ u (ρP) M Ids (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 [])
          (Fss.getD 0 []).length (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) (m))
        (tupW u is)) ∧
      recSel (sqGraph ℓ u (ρP) M Ids (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 [])
          (Fss.getD 0 []).length (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) (m))
        (tupW u is)
        ∈ˢ SetTheory.app (is.foldl SetTheory.app M) pt ∧
      recSel (sqGraph ℓ u (ρP) M Ids (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 [])
          (Fss.getD 0 []).length (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) (m))
        (tupW u is)
        = (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) ++
            (recIdx (rss.getD 0 []) (Fss.getD 0 []).length).map fun i =>
              lamTower ℓ (consList ((srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)).take i)
                  (ρP)) ((tlss.getD 0 []).getD i []) fun σ' =>
                recSel (sqGraph ℓ u (ρP) M Ids (rss.getD 0 []) (tlss.getD 0 [])
                    (Eiss.getD 0 []) (Fss.getD 0 []).length
                    (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) (m))
                  (tupW u (((Eiss.getD 0 []).getD i []).map (interp V σ')))).foldl
            SetTheory.app (m) := by
  obtain ⟨hle, hFok, hprop⟩ := h.hsq rfl hℓ
  rw [hfrP] at hFok hprop
  have hX := h.hX
  have hreal := h.hreal
  rw [hfrP] at hX hreal
  rcases Nat.lt_or_eq_of_le hle with hz | hsingle
  · -- no constructor (task #210 Part B): the family is empty
    intro is t hsp ht
    exact (fam_empty_of_mem hX hreal (by omega) hsp ht).elim
  have hI : IdxOk u (ρP) Ids := hX.hI
  have hEs0 : (Ess.getD 0 []).length = Ids.length := h.hyp.hEs 0 (by omega)
  have hμ := fixFamI_mem u 0 (ρP) Ids rss tlss Eiss Fss₀ Ess
  have hfam : ∀ t', SetTheory.app
      (fixFamI u 0 (ρP) Ids Ids.length rss tlss Eiss Fss₀ Ess) t'
      ∈ˢ (univZero : V) := by
    intro t'
    have := famApp_mem_univ hμ t'
    rwa [univ_zero] at this
  obtain ⟨hl₀, -, -, -, hc⟩ := h.hreal
  rw [hfrP] at hc
  have hslot : ∀ fs' : List V, SpineFit (ρP) (Fss.getD 0 []) fs' →
      ∀ i ∈ recIdx (rss.getD 0 []) (Fss.getD 0 []).length,
        SlotFit u 0 (ρP) Ids ((tlss.getD 0 []).getD i []) ((Eiss.getD 0 []).getD i [])
          (fs'.take i) ∧
        fs'.getD i pt ∈ˢ slotSet 0 u (consList (fs'.take i) (ρP))
          ((tlss.getD 0 []).getD i []) ((Eiss.getD 0 []).getD i [])
          (fixFamI u 0 (ρP) Ids Ids.length rss tlss Eiss Fss₀ Ess) := by
    intro fs' hfit' i hi
    obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
    have := chainRealI_at (Fss₀.getD 0 []) (Fss.getD 0 []) 0 [] fs' rfl (hc 0 (by omega)) hfit' i hik
      (by rw [Nat.zero_add]; exact hri)
    rw [Nat.zero_add, List.nil_append] at this
    refine ⟨this.1, ?_⟩
    rw [← this.2]
    exact FixKI.spineFit_getD_mem' hfit' hik
  -- the motive's fibres are in the universe
  have hMtele := h.hyp.hMtele
  rw [hfrP, hfrM] at hMtele
  have hB : ∀ t', t' ∈ˢ idxSet u (ρP) Ids →
      sqB u Ids.length M t' ∈ˢ (univ ℓ : V) := by
    intro t' ht'
    obtain ⟨is', hsp', rfl⟩ := mem_idxSet_elim ht'
    unfold sqB
    rw [isOfW_tupW hI hsp']
    have hM' := piTele_fold (Nat.succ_ne_zero ℓ) hMtele (fitsS_teleOfFields.mpr hsp')
    rw [List.nil_append] at hM'
    by_cases hpt : (pt : V) ∈ˢ SetTheory.app
        (fixFamI u 0 (ρP) Ids Ids.length rss tlss Eiss Fss₀ Ess) (tupW u is')
    · exact app_mem_piR_pos (Nat.succ_ne_zero ℓ) hM' hpt
    · rw [app_off_dom_piR_pos (Nat.succ_ne_zero ℓ) hM' hpt]
      exact empty_mem_univ ℓ
  have hpred : ∀ t', t' ∈ˢ idxSet u (ρP) Ids →
      sqPred u (ρP) Ids (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 [])
        (Fss.getD 0 []).length (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) t'
        ⊆ˢ idxSet u (ρP) Ids := fun _ _ => sep_subset
  -- the minor's typing
  have hms := h.hyp.hms 0 (by omega)
  rw [hfrMs, hfrP, hfrM] at hms
  -- the step lands in the bound (at a tuple whose source spine fits)
  have hst : ∀ (is : List V) (t : V), SpineFit (ρP) Ids is → t = tupW u is →
      SpineFit (ρP) (Fss.getD 0 [])
        (sqSpine u Ids.length (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) t) →
      idxValsAt (ρP) (Ess.getD 0 [])
        (sqSpine u Ids.length (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) t) = is →
      ∀ g, g ∈ˢ piSet (sqPred u (ρP) Ids (rss.getD 0 []) (tlss.getD 0 [])
          (Eiss.getD 0 []) (Fss.getD 0 []).length (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) t)
          (fun j => SetTheory.app (sqGraph ℓ u (ρP) M Ids (rss.getD 0 []) (tlss.getD 0 [])
            (Eiss.getD 0 []) (Fss.getD 0 []).length (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)
            (m)) j) →
      sqSt ℓ u (ρP) Ids (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 [])
          (Fss.getD 0 []).length (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) (m) t g
        ∈ˢ sqB u Ids.length M t := by
    intro is t hsp ht hfit₀ hidx₀ g hg
    subst ht
    unfold sqSt sqB
    have hspine : sqSpine u Ids.length (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) (tupW u is)
        = srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) := by
      unfold sqSpine; rw [isOfW_tupW hI hsp]
    rw [hspine] at hfit₀ hidx₀ ⊢
    rw [isOfW_tupW hI hsp]
    have hfold := minorSpI_fold (fun h0 => absurd h0 hℓ) hms hfit₀
    rw [List.nil_append] at hfold
    have hlenIh : (sqIhs ℓ u (ρP) (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 [])
        (Fss.getD 0 []).length (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)) g).length
        = (ihDomsI ℓ (ρP) M rss tlss Eiss (fun j => (Fss.getD j []).length) 0
            (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length))).length := by
      simp [sqIhs, ihDomsI]
    have hmemIh : ∀ l, l < (ihDomsI ℓ (ρP) M rss tlss Eiss (fun j => (Fss.getD j []).length) 0
          (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length))).length →
        (sqIhs ℓ u (ρP) (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 [])
          (Fss.getD 0 []).length (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)) g).getD l pt
        ∈ˢ (ihDomsI ℓ (ρP) M rss tlss Eiss (fun j => (Fss.getD j []).length) 0
          (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length))).getD l pt := by
      intro l hl
      have hl' : l < (recIdx (rss.getD 0 []) (Fss.getD 0 []).length).length := by
        simpa [ihDomsI] using hl
      have hi : (recIdx (rss.getD 0 []) (Fss.getD 0 []).length)[l] ∈ recIdx (rss.getD 0 []) (Fss.getD 0 []).length :=
        List.getElem_mem hl'
      unfold sqIhs ihDomsI
      show _ ∈ˢ (List.map _ (recIdx (rss.getD 0 []) (Fss.getD 0 []).length)).getD l pt
      rw [getD_map_lt hl', getD_map_lt hl']
      obtain ⟨hslotfit, hslotmem⟩ := hslot _ hfit₀ _ hi
      have hfpt : (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)).getD
          (recIdx (rss.getD 0 []) (Fss.getD 0 []).length)[l] pt = pt :=
        eq_pt_of_mem_slotSet_zero hfam hslotmem
      refine lamTower_mem_piTele fun bs hbs => ?_
      rw [List.nil_append, hfpt, foldl_app_pt']
      obtain ⟨-, hv⟩ := hslotfit.2.2 bs hbs
      rw [consList_append] at hv
      -- the call's tuple is a predecessor
      have hj : tupW u (((Eiss.getD 0 []).getD (recIdx (rss.getD 0 []) (Fss.getD 0 []).length)[l] []).map
          (interp V (consList bs (consList ((srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)).take
            (recIdx (rss.getD 0 []) (Fss.getD 0 []).length)[l]) (ρP)))))
          ∈ˢ sqPred u (ρP) Ids (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 [])
            (Fss.getD 0 []).length (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) (tupW u is) := by
        unfold sqPred
        refine mem_sep.mpr ⟨tupW_mem hv, _, hi, bs, ?_, by rw [hspine]⟩
        rw [hspine]; exact hbs
      have hG := app_mem_of_mem_piSet hg hj
      unfold sqGraph at hG
      rw [app_recGraph_eq hB hpred (tupW_mem hv)] at hG
      have hBj := (mem_recGraphFibre.mp hG).1
      unfold sqB at hBj
      rwa [isOfW_tupW hI hv] at hBj
    have := ihSpL_fold (fun h0 => absurd h0 hℓ) hfold hlenIh hmemIh
    unfold concI ctorValI at this
    rw [if_pos rfl, hidx₀] at this
    rw [List.foldl_append]
    exact this
  have hsrc : ∀ (fs is : List V), SpineFit (ρP) (Fss.getD 0 []) fs →
      SpineFit (ρP) Ids is →
      idxValsAt (ρP) (Ess.getD 0 []) fs = is →
      fs = srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) :=
    fun fs is hf _ hi => srcVals_of_fit hprop hf hi
  have hsing := sqGraph_singleton (M := M) (m := m) hX hreal hsingle rfl hEs0 hsrc hB hst
  intro is t hsp ht
  obtain ⟨rfl, fs, hfsfit, hfsidx⟩ := fam_spine_of_mem hX hreal hsingle hEs0 hsp ht
  have hfs₀ := srcVals_of_fit hprop hfsfit hfsidx
  rw [hfs₀] at hfsfit hfsidx
  have hs := hsing is pt hsp ht
  refine ⟨hs.1, ?_, ?_⟩
  · have hv := recSel_mem hs.1
    unfold sqGraph at hv
    rw [app_recGraph_eq hB hpred (tupW_mem hsp)] at hv
    have hBt := (mem_recGraphFibre.mp hv).1
    unfold sqB at hBt
    rwa [isOfW_tupW hI hsp] at hBt
  · -- the recursion equation
    have hspine : sqSpine u Ids.length (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) (tupW u is)
        = srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) := by
      unfold sqSpine; rw [isOfW_tupW hI hsp]
    have hP : ∀ j, j ∈ˢ sqPred u (ρP) Ids (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 [])
          (Fss.getD 0 []).length (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) (tupW u is) →
        (∃ v, v ∈ˢ SetTheory.app (sqGraph ℓ u (ρP) M Ids (rss.getD 0 []) (tlss.getD 0 [])
          (Eiss.getD 0 []) (Fss.getD 0 []).length (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)
          (m)) j) ∧
        ∀ v v', v ∈ˢ SetTheory.app (sqGraph ℓ u (ρP) M Ids (rss.getD 0 []) (tlss.getD 0 [])
            (Eiss.getD 0 []) (Fss.getD 0 []).length (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)
            (m)) j →
          v' ∈ˢ SetTheory.app (sqGraph ℓ u (ρP) M Ids (rss.getD 0 []) (tlss.getD 0 [])
            (Eiss.getD 0 []) (Fss.getD 0 []).length (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)
            (m)) j → v = v' := by
      intro j hj
      obtain ⟨-, i, hi, bs, hbs, rfl⟩ := mem_sep.mp hj
      rw [hspine] at hbs
      obtain ⟨hslotfit, hslotmem⟩ := hslot _ hfsfit i hi
      obtain ⟨-, hv⟩ := hslotfit.2.2 bs hbs
      rw [consList_append] at hv
      unfold slotSet at hslotmem
      obtain ⟨y, hy⟩ := mem_piTele_zero hslotmem bs (fitsS_teleOfFields.mpr hbs)
      rw [List.nil_append] at hy
      rw [hspine]
      exact hsing _ y hv hy
    have heq := recSel_eq hB hpred (tupW_mem hsp) hs.1 hP
    unfold sqGraph at heq ⊢
    rw [heq]
    unfold sqSt sqIhs
    rw [hspine]
    congr 1
    congr 1
    apply List.map_congr_left
    intro i hi
    refine lamTower_congr_leaves fun bs hbs => ?_
    have hj : tupW u (((Eiss.getD 0 []).getD i []).map (interp V (consList bs
        (consList ((srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)).take i) (ρP)))))
        ∈ˢ sqPred u (ρP) Ids (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 [])
          (Fss.getD 0 []).length (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) (tupW u is) := by
      obtain ⟨hslotfit, -⟩ := hslot _ hfsfit i hi
      obtain ⟨-, hv⟩ := hslotfit.2.2 bs hbs
      rw [consList_append] at hv
      unfold sqPred
      refine mem_sep.mpr ⟨tupW_mem hv, i, hi, bs, ?_, by rw [hspine]⟩
      rw [hspine]; exact hbs
    rw [app_graph hj]

end Body

end ConLeche.Semantics
