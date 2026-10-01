module

public import ConLeche.Semantics.Tower.FixSquashI

@[expose] public section
/-!
# The ih arguments at a recursive field's telescope (task #202 Stage B)

The recursive route's body (`fixRecBodyAVI`, graph regime) spells the
ih argument of a recursive field as a λ-tower over the field's
telescope moved to the payload frame (`ihArgAV`, `ihTeleAt`): the
field variables are the payload's projections (`substProjAt`).  Stage
A proved the ih obligation at finitary fields only (empty telescopes,
`ihArgsOk_of` with `hfin`); this module reads the moved telescope and
the moved index expressions at any frame of the case split
(`interp_substProjAt`, `ihIdxM_interp`, `lamTower_ihTeleAt`,
`piTele_ihTeleAt`, `domsWalk_ihTeleAt`) and discharges the ih
obligation at every field (`FixKI.ihArgsOk_of`): the argument reads to
the ih value `ihValsI` (the λ-tower of the function at the block, the
call's index values and the field applied to the telescope's values),
is graded, and lies in the ih domain (the nested product of the motive
at the calls).
-/

namespace ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.SetTheory.Tower

universe uv
variable {V : Type uv} [SetTheory V]

/-! ## The payload's projections under binders -/

omit [SetTheory V] in
theorem instE_consList (v : V) :
    ∀ (bs : List V) (k : Nat) (ρ : Nat → V),
      instE (bs.length + k) v (consList bs ρ) = consList bs (instE k v ρ)
  | [], k, ρ => by rw [List.length_nil, Nat.zero_add]; rfl
  | b :: bs, k, ρ => by
    rw [consList_cons, consList_cons, List.length_cons,
      show bs.length + 1 + k = bs.length + (k + 1) from by omega, instE_consList v bs (k + 1) (cons b ρ),
      cons_instE]

omit [SetTheory V] in
theorem instE_consList' (v : V) (bs : List V) (ρ : Nat → V) :
    instE bs.length v (consList bs ρ) = consList bs (cons v ρ) := by
  have := instE_consList v bs 0 ρ
  rwa [Nat.add_zero, instE_zero] at this

/-- `substProjAt` under `m` binders reads at the payload's projections
below them. -/
theorem interp_substProjAt (σ : Nat → V) (y : V) (bs : List V) :
    ∀ (i : Nat) (e : AnnotTerm),
      interp V (consList bs (cons y σ)) (substProjAt bs.length i e)
        = interp V (consList bs (consList (projList i y) (cons y σ))) e
  | 0, _ => rfl
  | i + 1, e => by
    show interp V (consList bs (cons y σ)) (substProjAt bs.length i (e.inst (projAV i (.bvar i)) bs.length)) = _
    rw [interp_substProjAt σ y bs i, interp_inst, shiftE_consList, projAV_interp, interp_bvar]
    have hy : consList (projList i y) (cons y σ) i = y := by
      have := consList_apply_add (projList i y) (cons y σ) 0
      rwa [Nat.zero_add, projList_length] at this
    rw [hy, instE_consList', consList_snoc', ← projList_snoc]

theorem WellDenoted_substProjAt (σ : Nat → V) (y : V) (bs : List V) :
    ∀ (i : Nat) (e : AnnotTerm),
      (∀ m, m < i → WellDenoted V (consList (projList m y) (cons y σ)) (projAV m (.bvar m))) →
      (WellDenoted V (consList bs (cons y σ)) (substProjAt bs.length i e) ↔
        WellDenoted V (consList bs (consList (projList i y) (cons y σ))) e)
  | 0, _, _ => Iff.rfl
  | i + 1, e, hp => by
    show WellDenoted V (consList bs (cons y σ)) (substProjAt bs.length i (e.inst (projAV i (.bvar i)) bs.length)) ↔ _
    rw [WellDenoted_substProjAt σ y bs i _ (fun m hm => hp m (by omega)),
      WellDenoted_inst V _ _ _ _ (by rw [shiftE_consList]; exact hp i (by omega)), shiftE_consList,
      projAV_interp, interp_bvar]
    have hy : consList (projList i y) (cons y σ) i = y := by
      have := consList_apply_add (projList i y) (cons y σ) 0
      rwa [Nat.zero_add, projList_length] at this
    rw [hy, instE_consList', consList_snoc', ← projList_snoc]

/-- The ih argument's body under the moved telescope (`m` binders):
the function at the block, the moved index expressions and the field
applied to the telescope's variables. -/
def ihArgBody (nP n nIdx D i m : Nat) (Eis : List AnnotTerm) : AnnotTerm :=
  AnnotTerm.mkAppN (.bvar (D + 1 + nIdx + n + 1 + nP + m))
    (idxVarsAV (nP + 1 + n) (D + 1 + nIdx + m) ++
      Eis.map (fun E => substProjAt m i (E.liftN (D + nIdx + n + 2) (i + m))) ++
      [AnnotTerm.mkAppN (projAV i (.bvar m)) (teleVarsAV m)])

omit [SetTheory V] in
theorem ihArgAV_eq (ℓ nP n nIdx D i : Nat) (tl : List (Nat × Nat × AnnotTerm)) (Eis : List AnnotTerm) :
    ihArgAV ℓ nP n nIdx D i tl Eis = mkLamsC ℓ (ihTeleAt nIdx n D i tl) (ihArgBody nP n nIdx D i tl.length Eis) :=
  rfl

section IhFrame

variable {ℓ w u nP : Nat} {ρ₀ σ : Nat → V} {Fss Ess : List (List AnnotTerm)} {Ids : List AnnotTerm}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {D : Nat}

/-- A field's index expression, moved under `bs` telescope binders at
the payload frame, reads at the field's own frame under `bs`. -/
theorem ihIdxM_interp (hfr : RecFrameS D ρ₀ σ) (y : V) (i : Nat) (bs : List V) (E : AnnotTerm) :
    interp V (consList bs (cons y σ))
        (substProjAt bs.length i (E.liftN (D + Ids.length + Fss.length + 2) (i + bs.length)))
      = interp V (consList bs (consList (projList i y) (frP Fss.length Ids.length ρ₀))) E := by
  rw [interp_substProjAt, interp_liftN, ← consList_append,
    show i + bs.length = (projList i y ++ bs).length from by rw [List.length_append, projList_length],
    shiftE_consList_len, shiftE_payload hfr, consList_append]

theorem ihIdxM_wellDenoted (hfr : RecFrameS D ρ₀ σ) (y : V) (i : Nat) (bs : List V) (E : AnnotTerm)
    (hp : ∀ m, m < i → WellDenoted V (consList (projList m y) (cons y σ)) (projAV m (.bvar m)))
    (hE : WellDenoted V (consList bs (consList (projList i y) (frP Fss.length Ids.length ρ₀))) E) :
    WellDenoted V (consList bs (cons y σ))
      (substProjAt bs.length i (E.liftN (D + Ids.length + Fss.length + 2) (i + bs.length))) := by
  rw [WellDenoted_substProjAt σ y bs i _ hp, WellDenoted_liftN, ← consList_append,
    show i + bs.length = (projList i y ++ bs).length from by rw [List.length_append, projList_length],
    shiftE_consList_len, shiftE_payload hfr, consList_append]
  exact hE

/-! ## The moved telescope -/

/-- `ihTeleAt`, walked: binder `k` (under `k` earlier ones) of the
remaining telescope. -/
def ihTeleAtGoP (nIdx n D i : Nat) : Nat → List (Nat × Nat × AnnotTerm) → List (Nat × Nat × AnnotTerm)
  | _, [] => []
  | k, d :: tl => (d.1, d.2.1, substProjAt k i (d.2.2.liftN (D + nIdx + n + 2) (i + k))) ::
      ihTeleAtGoP nIdx n D i (k + 1) tl

omit [SetTheory V] in
theorem ihTeleAtGoP_eq (nIdx n D i : Nat) :
    ∀ (k : Nat) (tl : List (Nat × Nat × AnnotTerm)),
      ihTeleAtGoP nIdx n D i k tl = (List.range tl.length).map fun l =>
        let d := tl.getD l default
        (d.1, d.2.1, substProjAt (k + l) i (d.2.2.liftN (D + nIdx + n + 2) (i + (k + l))))
  | _, [] => rfl
  | k, d :: tl => by
    simp only [ihTeleAtGoP, ihTeleAtGoP_eq nIdx n D i (k + 1) tl, List.length_cons,
      List.range_succ_eq_map, List.map_cons, List.map_map, List.getD_cons_zero, List.getD_cons_succ,
      Nat.add_zero, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro l _
    rw [show k + 1 + l = k + (l + 1) from by omega]

omit [SetTheory V] in
theorem ihTeleAt_eq_go (nIdx n D i : Nat) (tl : List (Nat × Nat × AnnotTerm)) :
    ihTeleAt nIdx n D i tl = ihTeleAtGoP nIdx n D i 0 tl := by
  rw [ihTeleAtGoP_eq]
  unfold ihTeleAt
  apply List.map_congr_left
  intro l _
  simp only [Nat.zero_add]

/-- The λ-tower over the moved telescope at the payload frame is the
λ-tower over the telescope at the field's own frame. -/
theorem lamTower_ihTeleAtGoP (hfr : RecFrameS D ρ₀ σ) (y : V) (i : Nat) {g₁ g₂ : (Nat → V) → V} :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (as : List V),
      (∀ bs : List V, bs.length = tl.length →
        g₁ (consList bs (consList as (cons y σ)))
          = g₂ (consList bs (consList as (consList (projList i y) (frP Fss.length Ids.length ρ₀))))) →
      lamTower ℓ (consList as (cons y σ)) (ihTeleAtGoP Ids.length Fss.length D i as.length tl) g₁
        = lamTower ℓ (consList as (consList (projList i y) (frP Fss.length Ids.length ρ₀))) tl g₂
  | [], as, hg => by
    have := hg [] rfl
    simpa [lamTower, ihTeleAtGoP] using this
  | d :: tl, as, hg => by
    show lamR ℓ (interp V _ (substProjAt as.length i (d.2.2.liftN (D + Ids.length + Fss.length + 2) (i + as.length))))
        (fun a => lamTower ℓ (cons a _) (ihTeleAtGoP Ids.length Fss.length D i (as.length + 1) tl) g₁)
      = lamR ℓ (interp V _ d.2.2) (fun a => lamTower ℓ (cons a _) tl g₂)
    rw [ihIdxM_interp hfr y i as d.2.2]
    refine lamR_congr fun a _ => ?_
    have ih := lamTower_ihTeleAtGoP hfr y i tl (as ++ [a]) (fun bs hbs => by
      have := hg (a :: bs) (by simp [hbs])
      rwa [consList_cons, consList_cons, consList_snoc', consList_snoc'] at this)
    rw [length_snoc', ← consList_snoc', ← consList_snoc'] at ih
    exact ih

theorem lamTower_ihTeleAt (hfr : RecFrameS D ρ₀ σ) (y : V) (i : Nat) {g₁ g₂ : (Nat → V) → V}
    (tl : List (Nat × Nat × AnnotTerm))
    (hg : ∀ bs : List V, bs.length = tl.length →
      g₁ (consList bs (cons y σ))
        = g₂ (consList bs (consList (projList i y) (frP Fss.length Ids.length ρ₀)))) :
    lamTower ℓ (cons y σ) (ihTeleAt Ids.length Fss.length D i tl) g₁
      = lamTower ℓ (consList (projList i y) (frP Fss.length Ids.length ρ₀)) tl g₂ := by
  rw [ihTeleAt_eq_go]
  have := lamTower_ihTeleAtGoP (ℓ := ℓ) hfr y i tl [] (fun bs hbs => by simpa using hg bs hbs)
  simpa using this

/-- The nested product over the moved telescope at the payload frame is
the nested product over the telescope at the field's own frame. -/
theorem piTele_ihTeleAtGoP {v : Nat} {B : List V → V} (hfr : RecFrameS D ρ₀ σ) (y : V) (i : Nat) :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (as acc : List V),
      piTele v (teleOfFields (consList as (cons y σ))
          ((ihTeleAtGoP Ids.length Fss.length D i as.length tl).map (·.2.2))) B acc
        = piTele v (teleOfFields (consList as (consList (projList i y) (frP Fss.length Ids.length ρ₀)))
          (tl.map (·.2.2))) B acc
  | [], _, _ => rfl
  | d :: tl, as, acc => by
    show piTele v (teleOfFields _
      (((d.1, d.2.1, substProjAt as.length i (d.2.2.liftN (D + Ids.length + Fss.length + 2) (i + as.length))) ::
        ihTeleAtGoP Ids.length Fss.length D i (as.length + 1) tl).map (·.2.2))) B acc = _
    rw [List.map_cons, List.map_cons]
    simp only [teleOfFields, piTele]
    rw [ihIdxM_interp hfr y i as d.2.2]
    refine piR_congr fun a _ => ?_
    have := piTele_ihTeleAtGoP (v := v) (B := B) hfr y i tl (as ++ [a]) (acc ++ [a])
    rw [length_snoc', ← consList_snoc', ← consList_snoc'] at this
    exact this

theorem piTele_ihTeleAt {v : Nat} {B : List V → V} (hfr : RecFrameS D ρ₀ σ) (y : V) (i : Nat)
    (tl : List (Nat × Nat × AnnotTerm)) :
    piTele v (teleOfFields (cons y σ) ((ihTeleAt Ids.length Fss.length D i tl).map (·.2.2))) B []
      = piTele v (teleOfFields (consList (projList i y) (frP Fss.length Ids.length ρ₀)) (tl.map (·.2.2))) B [] := by
  rw [ihTeleAt_eq_go]
  have := piTele_ihTeleAtGoP (v := v) (B := B) (Ids := Ids) (Fss := Fss) hfr y i tl [] []
  simpa using this

/-- The moved telescope's domains walk at the payload frame when the
telescope's do at the field's frame. -/
theorem domsWalk_ihTeleAtGoP (hfr : RecFrameS D ρ₀ σ) (y : V) (i : Nat)
    (hp : ∀ m, m < i → WellDenoted V (consList (projList m y) (cons y σ)) (projAV m (.bvar m))) :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (as : List V),
      DomsWalk (consList as (consList (projList i y) (frP Fss.length Ids.length ρ₀))) tl →
      DomsWalk (consList as (cons y σ)) (ihTeleAtGoP Ids.length Fss.length D i as.length tl)
  | [], _, _ => trivial
  | d :: tl, as, h => by
    refine ⟨ihIdxM_wellDenoted hfr y i as d.2.2 hp h.1, fun a ha => ?_⟩
    rw [ihIdxM_interp hfr y i as d.2.2] at ha
    have := domsWalk_ihTeleAtGoP hfr y i hp tl (as ++ [a]) (by rw [← consList_snoc']; exact h.2 a ha)
    rw [length_snoc', ← consList_snoc'] at this
    exact this

theorem domsWalk_ihTeleAt (hfr : RecFrameS D ρ₀ σ) (y : V) (i : Nat)
    (hp : ∀ m, m < i → WellDenoted V (consList (projList m y) (cons y σ)) (projAV m (.bvar m)))
    (tl : List (Nat × Nat × AnnotTerm))
    (h : DomsWalk (consList (projList i y) (frP Fss.length Ids.length ρ₀)) tl) :
    DomsWalk (cons y σ) (ihTeleAt Ids.length Fss.length D i tl) := by
  rw [ihTeleAt_eq_go]
  have := domsWalk_ihTeleAtGoP hfr y i hp tl [] (by simpa using h)
  simpa using this

/-- A spine fitting the moved telescope at the payload frame fits the
telescope at the field's frame, and conversely. -/
theorem spineFit_ihTeleAtGoP (hfr : RecFrameS D ρ₀ σ) (y : V) (i : Nat) :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (as bs : List V),
      SpineFit (consList as (cons y σ)) ((ihTeleAtGoP Ids.length Fss.length D i as.length tl).map (·.2.2)) bs ↔
        SpineFit (consList as (consList (projList i y) (frP Fss.length Ids.length ρ₀))) (tl.map (·.2.2)) bs
  | [], _, [] => Iff.rfl
  | [], _, _ :: _ => Iff.rfl
  | _ :: _, _, [] => by simp [ihTeleAtGoP, SpineFit]
  | d :: tl, as, b :: bs => by
    show (b ∈ˢ interp V _ (substProjAt as.length i (d.2.2.liftN (D + Ids.length + Fss.length + 2) (i + as.length)))
        ∧ SpineFit (cons b _) ((ihTeleAtGoP Ids.length Fss.length D i (as.length + 1) tl).map (·.2.2)) bs)
      ↔ (b ∈ˢ interp V _ d.2.2 ∧ SpineFit (cons b _) (tl.map (·.2.2)) bs)
    rw [ihIdxM_interp hfr y i as d.2.2]
    have := spineFit_ihTeleAtGoP hfr y i tl (as ++ [b]) bs
    rw [length_snoc', ← consList_snoc', ← consList_snoc'] at this
    exact and_congr_right fun _ => this

theorem spineFit_ihTeleAt (hfr : RecFrameS D ρ₀ σ) (y : V) (i : Nat) (tl : List (Nat × Nat × AnnotTerm))
    (bs : List V) :
    SpineFit (cons y σ) ((ihTeleAt Ids.length Fss.length D i tl).map (·.2.2)) bs ↔
      SpineFit (consList (projList i y) (frP Fss.length Ids.length ρ₀)) (tl.map (·.2.2)) bs := by
  rw [ihTeleAt_eq_go]
  have := spineFit_ihTeleAtGoP (Ids := Ids) (Fss := Fss) hfr y i tl [] bs
  simpa using this

/-! ## The ih argument's leaf -/

omit [SetTheory V] in
/-- The block frame under `bs` telescope binders at the payload frame. -/
theorem recFrameS_tele (hfr : RecFrameS D ρ₀ σ) (y : V) (bs : List V) :
    RecFrameS (D + 1 + Ids.length + bs.length) (shiftE Ids.length 0 ρ₀) (consList bs (cons y σ)) := by
  unfold RecFrameS
  rw [Nat.add_comm _ bs.length, shiftE_add', shiftE_consList, shiftE_add', shiftE_succ_cons, hfr]

/-- The function's variable under `bs` telescope binders at the payload
frame. -/
theorem ihArg_head_interp (hfr : RecFrameS D ρ₀ σ) (y : V) (bs : List V) :
    interp V (consList bs (cons y σ)) (.bvar (D + 1 + Ids.length + Fss.length + 1 + nP + bs.length))
      = frR nP Fss.length Ids.length ρ₀ := by
  rw [interp_bvar, consList_apply_add bs (cons y σ)]
  have := rAt_interp (nP := nP) (Fss := Fss) (Ids := Ids) hfr y
  rwa [interp_bvar] at this

/-- **The ih argument's leaf arguments read** to the block, the field's
index values and the field applied to the telescope's values. -/
theorem ihArg_args_interp (hfr : RecFrameS D ρ₀ σ) (y : V) (i : Nat) (bs : List V) (Eis : List AnnotTerm) :
    (idxVarsAV (nP + 1 + Fss.length) (D + 1 + Ids.length + bs.length) ++
        Eis.map (fun E => substProjAt bs.length i (E.liftN (D + Ids.length + Fss.length + 2) (i + bs.length))) ++
        [AnnotTerm.mkAppN (projAV i (.bvar bs.length)) (teleVarsAV bs.length)]).map
      (interp V (consList bs (cons y σ)))
      = frKSpine nP Fss.length Ids.length ρ₀ ++
          Eis.map (interp V (consList bs (consList (projList i y) (frP Fss.length Ids.length ρ₀)))) ++
          [bs.foldl SetTheory.app (projS i y)] := by
  have hy : consList bs (cons y σ) bs.length = y := by
    have := consList_apply_add bs (cons y σ) 0
    rwa [Nat.zero_add] at this
  rw [List.map_append, List.map_append, map_idxVarsAV_interp (recFrameS_tele hfr y bs), List.map_map,
    List.map_cons, List.map_nil, interp_mkAppN, ← List.foldl_map (f := interp V _) (g := SetTheory.app),
    map_teleVarsAV_interp, projAV_interp, interp_bvar, hy]
  congr 2
  apply List.map_congr_left
  intro E _
  exact ihIdxM_interp hfr y i bs E

/-- **The ih argument's leaf reads** to the function at the block, the
field's index values and the field applied to the telescope's values. -/
theorem ihArg_leaf_interp (hfr : RecFrameS D ρ₀ σ) (y : V) (i : Nat) (bs : List V) (Eis : List AnnotTerm) :
    interp V (consList bs (cons y σ)) (ihArgBody nP Fss.length Ids.length D i bs.length Eis)
      = (frKSpine nP Fss.length Ids.length ρ₀ ++
          Eis.map (interp V (consList bs (consList (projList i y) (frP Fss.length Ids.length ρ₀)))) ++
          [bs.foldl SetTheory.app (projS i y)]).foldl SetTheory.app (frR nP Fss.length Ids.length ρ₀) := by
  unfold ihArgBody
  rw [interp_mkAppN, ← List.foldl_map (f := interp V _) (g := SetTheory.app), ihArg_args_interp hfr y i bs,
    ihArg_head_interp hfr y bs]

/-- **The ih argument reads to the ih value**: the λ-tower over the
field's telescope at the field's frame of the leaf. -/
theorem ihArgAV_interp (hfr : RecFrameS D ρ₀ σ) (y : V) (i : Nat) (tl : List (Nat × Nat × AnnotTerm))
    (Eis : List AnnotTerm) :
    interp V (cons y σ) (ihArgAV ℓ nP Fss.length Ids.length D i tl Eis)
      = lamTower ℓ (consList (projList i y) (frP Fss.length Ids.length ρ₀)) tl fun σ' =>
          (frKSpine nP Fss.length Ids.length ρ₀ ++ Eis.map (interp V σ') ++
            [(frameIdx tl.length σ').foldl SetTheory.app (projS i y)]).foldl SetTheory.app
            (frR nP Fss.length Ids.length ρ₀) := by
  rw [ihArgAV_eq, interp_mkLamsC]
  refine lamTower_ihTeleAt hfr y i tl fun bs hbs => ?_
  rw [← hbs, ihArg_leaf_interp hfr y i bs Eis, frameIdx_consList']

end IhFrame

/-! ## The ih values at a constructor payload -/

/-- The ih values at a constructor value are the λ-towers at the
fields' prefixes of the function at the block, the calls' index values
and the field applied to the telescope's values. -/
theorem ihValsI_mk {ℓ : Nat} {ρp : Nat → V} {rV : V} {kspine : List V} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {ar : Nat → Nat}
    {j : Nat} {fs : List V} (hlen : fs.length = ar j) :
    ihValsI ℓ ρp rV kspine rss tlss Eiss ar j (mkTower (fs ++ [pt]))
      = (recIdx (rss.getD j []) (ar j)).map fun i =>
          lamTower ℓ (consList (fs.take i) ρp) ((tlss.getD j []).getD i []) fun σ' =>
            (kspine ++ (((Eiss.getD j []).getD i []).map (interp V σ')) ++
              [(frameIdx ((tlss.getD j []).getD i []).length σ').foldl SetTheory.app (fs.getD i pt)]).foldl
              SetTheory.app rV := by
  unfold ihValsI
  apply List.map_congr_left
  intro i hi
  obtain ⟨hik, -⟩ := mem_recIdx.mp hi
  rw [projList_mkTower_take (by omega), projS_mkTower_getD (by omega)]

/-! ## The ih obligation at every field -/

namespace FixKI

variable {ℓ w u nP : Nat} {ρ₀ : Nat → V} {Fss Ess Fss₀ : List (List AnnotTerm)} {Ids : List AnnotTerm}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {rds : List (Nat × Nat × AnnotTerm)}

set_option maxHeartbeats 3200000 in
/-- **The ih obligation is discharged** at every frame of the case
split (graph regime), every field: the ih argument reads to the ih
value, is graded (a constant-bit λ-tower over the moved telescope whose
leaf is the function's graded application chain) and lies in the ih
domain (the nested product of the motive at the calls). -/
theorem ihArgsOk_tele (h : FixKI ℓ w u nP ρ₀ Fss Ess Fss₀ Ids rss tlss Eiss rds) (hw : w ≠ 0)
    {D : Nat} {σ : Nat → V} (hfr : RecFrameS D ρ₀ σ) {j : Nat} (hj : j < Fss.length) :
    IhArgsOk w ρ₀ σ Fss Ess Ids
      (ihDomsI ℓ (frP Fss.length Ids.length ρ₀) (frM Fss.length Ids.length ρ₀) rss tlss Eiss
        (fun j => (Fss.getD j []).length))
      (ihValsI ℓ (frP Fss.length Ids.length ρ₀) (frR nP Fss.length Ids.length ρ₀)
        (frKSpine nP Fss.length Ids.length ρ₀) rss tlss Eiss (fun j => (Fss.getD j []).length))
      (ihArgsI ℓ nP Fss.length Ids.length rss tlss Eiss (fun j => (Fss.getD j []).length)) D j := by
  intro y hy
  have hjF := h.hyp.rChain_getElem? hj
  rw [sumFibre_of_getElem? hjF] at hy
  have hokF : FieldsOkB w ρ₀
      (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j [])) :=
    h.hyp.hok _ (List.mem_of_getElem? hjF)
  have hbnd := hokF.toBound hw
  have hlenR : (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j [])).length
      = (Fss.getD j []).length + 1 := rChain_length _ _ _ _
  have hfam : ∀ t, SetTheory.app
      (fixFamI u w (frP Fss.length Ids.length ρ₀) Ids Ids.length rss tlss Eiss Fss₀ Ess) t ∈ˢ (univ w : V) :=
    fun t => famApp_mem_univ (fixFamI_mem u w (frP Fss.length Ids.length ρ₀) Ids rss tlss Eiss Fss₀ Ess) t
  -- the payload's projections fit the real chain at the parameter frame
  have helim := restricted_member_elim hw
    (Fs := liftFields (Ids.length + Fss.length + 1) 0 (Fss.getD j []))
    (eqs := idxEqsAt (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []).length (Ess.getD j []))
    (ρ := ρ₀) (y := y) hy
  rw [liftFields_length] at helim
  obtain ⟨hspL, -, -, -⟩ := helim
  have hspP : SpineFit (frP Fss.length Ids.length ρ₀) (Fss.getD j [])
      (projList (Fss.getD j []).length y) :=
    (spineFit_liftFields (Ids.length + Fss.length + 1)).mp hspL
  -- the projections are graded at their frames
  have hproj : ∀ m, m < (Fss.getD j []).length →
      ∀ (σ' : Nat → V) (k : Nat), interp V σ' (.bvar k) = y → WellDenoted V σ' (projAV m (.bvar k)) := by
    intro m hm σ' k hσ'
    refine projAV_wellDenoted_tower (w := w) (ρ := ρ₀) (by simp) ?_ hbnd (by omega)
    rw [hσ']; exact hy
  have hp : ∀ i, i ≤ (Fss.getD j []).length → ∀ m, m < i →
      WellDenoted V (consList (projList m y) (cons y σ)) (projAV m (.bvar m)) := by
    intro i hi m hm
    refine hproj m (by omega) _ m ?_
    rw [interp_bvar]
    have := consList_apply_add (projList m y) (cons y σ) 0
    rwa [Nat.zero_add, projList_length] at this
  -- per recursive position: the slot's fit and its value
  have hpos : ∀ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length,
      i < (Fss.getD j []).length ∧
      SlotFit u w (frP Fss.length Ids.length ρ₀) Ids ((tlss.getD j []).getD i []) ((Eiss.getD j []).getD i [])
        (projList i y) ∧
      projS i y ∈ˢ slotSet w u (consList (projList i y) (frP Fss.length Ids.length ρ₀))
        ((tlss.getD j []).getD i []) ((Eiss.getD j []).getD i [])
        (fixFamI u w (frP Fss.length Ids.length ρ₀) Ids Ids.length rss tlss Eiss Fss₀ Ess) := by
    intro i hi
    obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
    have hc := chainRealI_at (Fss₀.getD j []) (Fss.getD j []) 0 [] (projList (Fss.getD j []).length y)
      rfl (h.hreal.2.2.2.2 j hj) (by simpa using hspP) _ hik (by rw [Nat.zero_add]; exact hri)
    rw [Nat.zero_add, List.nil_append, projList_take _ _ _ (Nat.le_of_lt hik)] at hc
    obtain ⟨hf, heq⟩ := hc
    refine ⟨hik, hf, ?_⟩
    have := spineFit_getD_mem' hspP hik
    rw [projList_take _ _ _ (Nat.le_of_lt hik), heq] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [projList_length]; exact hik),
      Option.getD_some, projList_get _ _ _ hik] at this
    exact this
  -- the ih value of a recursive position, as the domain's bound sees it
  have hleaf : ∀ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length, ∀ bs : List V,
      SpineFit (consList (projList i y) (frP Fss.length Ids.length ρ₀))
        (((tlss.getD j []).getD i []).map (·.2.2)) bs →
      SpineFit (frP Fss.length Ids.length ρ₀) Ids
        (((Eiss.getD j []).getD i []).map (interp V (consList bs (consList (projList i y) (frP Fss.length Ids.length ρ₀))))) ∧
      (∀ E ∈ (Eiss.getD j []).getD i [],
        WellDenoted V (consList bs (consList (projList i y) (frP Fss.length Ids.length ρ₀))) E) ∧
      bs.foldl SetTheory.app (projS i y) ∈ˢ SetTheory.app
        (fixFamI u w (frP Fss.length Ids.length ρ₀) Ids Ids.length rss tlss Eiss Fss₀ Ess)
        (tupW u (((Eiss.getD j []).getD i []).map
          (interp V (consList bs (consList (projList i y) (frP Fss.length Ids.length ρ₀)))))) := by
    intro i hi bs hbs
    obtain ⟨-, hf, hmem⟩ := hpos i hi
    obtain ⟨hEok, hvsp⟩ := hf.2.2 bs hbs
    rw [consList_append] at hEok hvsp
    exact ⟨hvsp, hEok, slotSet_fold_mem hfam hmem hbs⟩
  refine ⟨?_, ?_, ?_⟩
  · -- the readings
    unfold ihArgsI ihValsI
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    show interp V (cons y σ) (ihArgAV ℓ nP Fss.length Ids.length D i _ _) = _
    exact ihArgAV_interp hfr y i _ _
  · -- the lengths
    unfold ihArgsI ihDomsI
    simp only [List.length_map]
  · -- the gradings and the memberships
    intro l hl
    unfold ihDomsI at hl ⊢
    rw [List.length_map] at hl
    have hi : (recIdx (rss.getD j []) (Fss.getD j []).length)[l]
        ∈ recIdx (rss.getD j []) (Fss.getD j []).length := List.getElem_mem hl
    obtain ⟨hik, hf, -⟩ := hpos _ hi
    have hgetA : (ihArgsI ℓ nP Fss.length Ids.length rss tlss Eiss (fun j => (Fss.getD j []).length) D j).getD l default
        = ihArgAV ℓ nP Fss.length Ids.length D ((recIdx (rss.getD j []) (Fss.getD j []).length)[l])
            ((tlss.getD j []).getD ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]) [])
            ((Eiss.getD j []).getD ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]) []) := by
      unfold ihArgsI
      rw [List.getD_eq_getElem?_getD (i := l), List.getElem?_map, List.getElem?_eq_getElem hl,
        Option.map_some, Option.getD_some]
    generalize hiL : (recIdx (rss.getD j []) (Fss.getD j []).length)[l] = i at hgetA hi hik hf
    have hgetD : (((recIdx (rss.getD j []) (Fss.getD j []).length)).map fun i =>
        piTele ℓ (teleOfFields (consList ((projList (Fss.getD j []).length y).take i) (frP Fss.length Ids.length ρ₀))
          (((tlss.getD j []).getD i []).map (·.2.2)))
          (fun as => SetTheory.app
            ((((Eiss.getD j []).getD i []).map
              (interp V (consList as (consList ((projList (Fss.getD j []).length y).take i)
                (frP Fss.length Ids.length ρ₀))))).foldl SetTheory.app (frM Fss.length Ids.length ρ₀))
            (as.foldl SetTheory.app ((projList (Fss.getD j []).length y).getD i pt))) []).getD l pt
        = piTele ℓ (teleOfFields (consList (projList i y) (frP Fss.length Ids.length ρ₀))
            (((tlss.getD j []).getD i []).map (·.2.2)))
            (fun as => SetTheory.app
              ((((Eiss.getD j []).getD i []).map
                (interp V (consList as (consList (projList i y) (frP Fss.length Ids.length ρ₀))))).foldl
                SetTheory.app (frM Fss.length Ids.length ρ₀))
              (as.foldl SetTheory.app (projS i y))) [] := by
      rw [List.getD_eq_getElem?_getD (i := l), List.getElem?_map, List.getElem?_eq_getElem hl,
        Option.map_some, Option.getD_some, hiL, projList_take _ _ _ (Nat.le_of_lt hik),
        List.getD_eq_getElem?_getD (l := projList (Fss.getD j []).length y),
        List.getElem?_eq_getElem (by rw [projList_length]; exact hik), Option.getD_some,
        projList_get _ _ _ hik]
    rw [hgetA, hgetD]
    -- the tower's facts
    have htower := mkLamsC_factsB (m := ℓ) (ρ := cons y σ) (acc := [])
      (b := ihArgBody nP Fss.length Ids.length D i ((tlss.getD j []).getD i []).length ((Eiss.getD j []).getD i []))
      (ds := ihTeleAt Ids.length Fss.length D i ((tlss.getD j []).getD i []))
      (B := fun as => SetTheory.app
        ((((Eiss.getD j []).getD i []).map
          (interp V (consList as (consList (projList i y) (frP Fss.length Ids.length ρ₀))))).foldl
          SetTheory.app (frM Fss.length Ids.length ρ₀))
        (as.foldl SetTheory.app (projS i y)))
      (underTowerOkB_of_leaves
        (domsWalk_ihTeleAt hfr y i (hp i (Nat.le_of_lt hik)) _ (domsWalk_of_fieldsOkB hf.1))
        fun bs hbs => ?_)
    · rw [ihArgAV_eq]
      rw [piTele_ihTeleAt hfr y i] at htower
      exact htower
    · rw [spineFit_ihTeleAt hfr y i] at hbs
      have hlenbs : bs.length = ((tlss.getD j []).getD i []).length := by
        rw [hbs.length_eq, List.length_map]
      obtain ⟨hvsp, hEok, hfmem⟩ := hleaf i hi bs hbs
      simp only [List.nil_append]
      rw [← hlenbs]
      unfold ihArgBody
      -- the leaf's arguments are graded, its chain is graded
      have hargs : ∀ a ∈ idxVarsAV (nP + 1 + Fss.length) (D + 1 + Ids.length + bs.length) ++
          ((Eiss.getD j []).getD i []).map
            (fun E => substProjAt bs.length i (E.liftN (D + Ids.length + Fss.length + 2) (i + bs.length))) ++
          [AnnotTerm.mkAppN (projAV i (.bvar bs.length)) (teleVarsAV bs.length)],
          WellDenoted V (consList bs (cons y σ)) a := by
        intro a ha
        simp only [List.mem_append, List.mem_map, List.mem_singleton] at ha
        rcases ha with (ha | ⟨E, hE, rfl⟩) | rfl
        · obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha
          simp
        · exact ihIdxM_wellDenoted hfr y i bs E (hp i (Nat.le_of_lt hik)) (hEok E hE)
        · -- the field applied to the telescope's variables
          have hy : interp V (consList bs (cons y σ)) (.bvar bs.length) = y := by
            rw [interp_bvar]
            have := consList_apply_add bs (cons y σ) 0
            rwa [Nat.zero_add] at this
          refine (mkAppN_wellDenoted_of_chain (hproj i hik _ _ hy) (fun a ha => teleVarsAV_wellDenoted ha) ?_).1
          rw [map_teleVarsAV_interp, projAV_interp, hy]
          exact slotSet_chainOk hfam (hpos i hi).2.2 hbs
      have hchain : AppChainOk
          (interp V (consList bs (cons y σ)) (.bvar (D + 1 + Ids.length + Fss.length + 1 + nP + bs.length)))
          ((idxVarsAV (nP + 1 + Fss.length) (D + 1 + Ids.length + bs.length) ++
            ((Eiss.getD j []).getD i []).map
              (fun E => substProjAt bs.length i (E.liftN (D + Ids.length + Fss.length + 2) (i + bs.length))) ++
            [AnnotTerm.mkAppN (projAV i (.bvar bs.length)) (teleVarsAV bs.length)]).map
              (interp V (consList bs (cons y σ)))) := by
        rw [ihArg_args_interp hfr y i bs, ihArg_head_interp hfr y bs]
        exact h.app_chain hvsp hfmem
      refine ⟨(mkAppN_wellDenoted_of_chain (by simp) hargs hchain).1, ?_, fun h0 => ?_⟩
      · have := ihArg_leaf_interp (nP := nP) (Fss := Fss) (Ids := Ids) hfr y i bs ((Eiss.getD j []).getD i [])
        unfold ihArgBody at this
        rw [this]
        exact h.app_mem hvsp hfmem
      · exact h.hyp.hMapp0 h0 hvsp.length_eq _

end FixKI

end ConLeche.Semantics
