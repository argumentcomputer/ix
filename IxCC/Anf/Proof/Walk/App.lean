import IxCC.Anf.Proof.Walk.BindBeta

/-! # The rewriting walk: applying related values

`Rel.AppSim` for the walk relation at bound `n`: applying related closures
to related arguments simulates. A closure of the same code enters the same
body (the fundamental lemma below `n`, `Rel.app_idc`); a walked closure
(`walkc`) enters the source body and its walk, one clock down, under the
environment the closure records (the walk's simulation below `n`); the
rest of the arguments are applied at `n` (induction on their number)
(M2.3). -/

set_option autoImplicit false

namespace IxCC.Anf.WalkProof

open IxCC.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open IxCC.Anf.Rel (Pw)
open Walk (Ent JEnt Fact Here Cfg Kont Fires)

variable {P Q : Program} {Valid : Cfg → List Val → List Val → List (Val × Val) → Prop} {Xc : Nat → List Val → Exp → Exp → Prop} {C : Cfg} {n : Nat}

/-- The parameters of a walked closure entered with arguments `vs`. -/
theorem walkc_params {σP : List Ent} {ρ' got got' : List Val} {nn m : Nat}
    {oOf : Nat → Opd} {wOf : Nat → Val} (hmn : m ≤ nn)
    (hng : nn - m ≤ got.length) (hgg : got'.length + (nn - m) = got.length)
    (hpre : ∀ p, p < nn - m → σP[nn - 1 - p]? = some (.opd (oOf p)) ∧ (oOf p).val ρ' = some (wOf p))
    (hpreg : ∀ p v, p < nn - m → got[p]? = some v → WV Q Valid Xc v (wOf p))
    (hown : ∀ p, nn - m ≤ p → p < nn → σP[nn - 1 - p]? = some (.opd (.lvl (ρ'.length + (p - (nn - m))))))
    (hownv : ∀ p v w, nn - m ≤ p → p < nn → got[p]? = some v → got'[p - (nn - m)]? = some w → WV Q Valid Xc v w)
    {vs ws : List Val} (hvs : WVs Q Valid Xc vs ws) (hsat : nn ≤ got.length + vs.length) :
    ∀ p, p < nn → ∃ o w v, σP[nn - 1 - p]? = some (.opd o) ∧
      o.val (((got' ++ ws).take m).reverse ++ ρ') = some w ∧ (got ++ vs)[p]? = some v ∧ WV Q Valid Xc v w := by
  intro p hp
  have hwl := hvs.length
  have hsuf : ρ' <:+ ((got' ++ ws).take m).reverse ++ ρ' := List.suffix_append _ _
  by_cases hpm : p < nn - m
  · obtain ⟨hσ, hval⟩ := hpre p hpm
    have hpg : p < got.length := by omega
    obtain ⟨v, hv⟩ : ∃ v, got[p]? = some v := ⟨got[p], List.getElem?_eq_getElem hpg⟩
    exact ⟨oOf p, wOf p, v, hσ, Opd.val_suffix hsuf hval, by rw [List.getElem?_append_left hpg, hv],
      hpreg p v hpm hv⟩
  · have hq : p - (nn - m) < m := by omega
    have hall : ((got' ++ ws).take m).length = m := by simp; omega
    have hval : (Opd.lvl (ρ'.length + (p - (nn - m)))).val (((got' ++ ws).take m).reverse ++ ρ') =
        (got' ++ ws)[p - (nn - m)]? := by
      rw [lvl_val_ext ρ' _ (by simp; omega), List.getElem?_reverse (by simp; omega)]
      simp only [List.length_reverse, hall, List.getElem?_take]
      rw [if_pos (by omega)]
      congr 1; omega
    by_cases hpg : p < got.length
    · have hqg : p - (nn - m) < got'.length := by omega
      obtain ⟨v, hv⟩ : ∃ v, got[p]? = some v := ⟨got[p], List.getElem?_eq_getElem hpg⟩
      obtain ⟨w, hw⟩ : ∃ w, got'[p - (nn - m)]? = some w :=
        ⟨got'[p - (nn - m)], List.getElem?_eq_getElem hqg⟩
      refine ⟨_, w, v, hown p (by omega) hp, by rw [hval, List.getElem?_append_left hqg, hw],
        by rw [List.getElem?_append_left hpg, hv], hownv p v w (by omega) hp hv hw⟩
    · have hidx : p - (nn - m) - got'.length = p - got.length := by omega
      rcases hvs.get (p - got.length) with ⟨h1, _⟩ | ⟨v, w, hv, hw, hvw⟩
      · rw [List.getElem?_eq_none_iff] at h1; omega
      · refine ⟨_, w, v, hown p (by omega) hp, ?_, by rw [List.getElem?_append_right (by omega), hv], hvw⟩
        rw [hval, List.getElem?_append_right (by omega), hidx, hw]

/-- Entering a walked closure with enough arguments: the source body and its
walk, one clock down. -/
theorem enter_walkc (hlow : ∀ m < n, ∀ fuel, WalkAt P Q Valid Xc m fuel)
    (hsuffix : ∀ C ρ ρ' prs ρ₂ ρ'₂, Valid C ρ ρ' prs → ρ <:+ ρ₂ → ρ' <:+ ρ'₂ → Valid C ρ₂ ρ'₂ prs)
    {C : Cfg} {fuel : Nat} {s s' : Fires} {σP σ0 : List Ent} {live : List Bool}
    {facts : Src.NatMap Fact} {ρ ρ' got got' : List Val} {nn m : Nat} {b b' : Exp}
    {oOf : Nat → Opd} {wOf : Nat → Val}
    (hV : VOk Q Valid Xc C ρ ρ')
    (hrun : (Walk.walk C fuel { σ := σP ++ σ0, jσ := [] } { d := ρ'.length + m, dj := 0, facts } b
      .ret).run s = .ok (b', s'))
    (henv : WEnv Q Valid Xc C live σ0 ρ ρ') (hf : FactsOk Q Valid facts ρ')
    (hnd : NoDead (List.replicate nn true ++ live) [] b) (hσP : σP.length = nn) (hmn : m ≤ nn)
    (hng : nn - m ≤ got.length) (hgg : got'.length + (nn - m) = got.length)
    (hpre : ∀ p, p < nn - m → σP[nn - 1 - p]? = some (.opd (oOf p)) ∧ (oOf p).val ρ' = some (wOf p))
    (hpreg : ∀ p v, p < nn - m → got[p]? = some v → WV Q Valid Xc v (wOf p))
    (hown : ∀ p, nn - m ≤ p → p < nn → σP[nn - 1 - p]? = some (.opd (.lvl (ρ'.length + (p - (nn - m))))))
    (hownv : ∀ p v w, nn - m ≤ p → p < nn → got[p]? = some v → got'[p - (nn - m)]? = some w → WV Q Valid Xc v w)
    {vs ws : List Val} (hvs : WVs Q Valid Xc vs ws) (hsat : nn ≤ got.length + vs.length) {i : Nat} (hi : i + 1 ≤ n) :
    SimUpTo (WV Q Valid Xc) i (fun k => eval P k (((got ++ vs).take nn).reverse ++ ρ) [] b)
      (fun k => eval Q k (((got' ++ ws).take m).reverse ++ ρ') [] b') := by
  have hwl := hvs.length
  have hall : ((got' ++ ws).take m).length = m := by simp; omega
  have hsuf : ρ' <:+ ((got' ++ ws).take m).reverse ++ ρ' := List.suffix_append _ _
  have hparams := walkc_params hmn hng hgg hpre hpreg hown hownv hvs hsat
  have hl1 : σP.length = (((got ++ vs).take nn).reverse).length := by simp; omega
  have henvb := WEnv.pushIdx (σP := σP) (V := ((got ++ vs).take nn).reverse) hl1 (fun i hi => by
    have hi' : i < nn := by omega
    obtain ⟨o, w, v, hσ, hw, hv, hvw⟩ := hparams (nn - 1 - i) (by omega)
    rw [show nn - 1 - (nn - 1 - i) = i by omega] at hσ
    refine ⟨o, w, ?_, hw, v, ?_, hvw⟩
    · rw [List.getElem?_eq_getElem hi] at hσ; exact Option.some.inj hσ
    · rw [List.getElem?_reverse (by simp; omega)]
      simp only [List.length_take, List.length_append, List.getElem?_take]
      rw [show min nn (got.length + vs.length) - 1 - i = nn - 1 - i by omega, if_pos (by omega)]
      exact hv) (henv.suffix hsuf)
  rw [hσP] at henvb
  have hk : KontW Q Valid Xc i .ret (fun v _ => .ok v) (((got' ++ ws).take m).reverse ++ ρ') [] :=
    ⟨_, rfl, fun x w hxw => SimUpTo.ok hxw⟩
  exact ((hlow i (by omega) fuel).walk hrun (((got ++ vs).take nn).reverse ++ ρ) [] _ [] _ [] _
    (VOk.suffix hsuffix hV (List.suffix_append _ _) hsuf) henvb .nil (by simp [hall]; omega) rfl (hf.suffix hsuf) hnd hk).congr
    (fun k => (Sem.Result.bind_pure _).symm) (fun _ => rfl)

theorem drop_got {α : Type} {got vs : List α} {nn : Nat} (h : got.length ≤ nn) :
    (got ++ vs).drop nn = vs.drop (nn - got.length) := by
  rw [List.drop_append, List.drop_eq_nil_of_le h, List.nil_append]

variable (P Q Valid Xc) in
/-- Entering a closure of another pass's code (`Xc`) with its arguments
simulates at bound `i`. -/
def XcEnter (i : Nat) : Prop :=
  ∀ ⦃n : Nat⦄ ⦃ρ ρ' : List Val⦄ ⦃b b' : Exp⦄ ⦃args args' : List Val⦄, WVs Q Valid Xc ρ ρ' →
    Xc n ρ b b' → WVs Q Valid Xc args args' → args.length = n →
    SimUpTo (WV Q Valid Xc) i (fun k => eval P k (args.reverse ++ ρ) [] b)
      (fun k => eval Q k (args'.reverse ++ ρ') [] b')

/-- `AppSim` for the walk relation at `n`, from the simulation, the
fundamental lemma and the interface below `n`. -/
theorem app_at (hlow : ∀ m < n, ∀ fuel, WalkAt P Q Valid Xc m fuel)
    (hfund : ∀ m < n, Rel.FundAt P Q (WV Q Valid Xc) m) (hxlow : ∀ m < n, XcEnter P Q Valid Xc m)
    (hsuffix : ∀ C ρ ρ' prs ρ₂ ρ'₂, Valid C ρ ρ' prs → ρ <:+ ρ₂ → ρ' <:+ ρ'₂ → Valid C ρ₂ ρ'₂ prs) :
    Rel.AppSim P Q (WV Q Valid Xc) n := by
  -- induction on the number of arguments
  suffices H : ∀ len, ∀ ⦃f g : Val⦄ ⦃vs ws : List Val⦄, vs.length ≤ len → WV Q Valid Xc f g →
      Pw (WV Q Valid Xc) vs ws → SimUpTo (WV Q Valid Xc) n (fun k => applyN P k f vs) (fun k => applyN Q k g ws) by
    intro f g vs ws hfg hvs; exact H _ (Nat.le_refl _) hfg hvs
  intro len
  induction len using Nat.strongRecOn with
  | _ len ih =>
  intro f g vs ws hlen hfg hvs
  have hrest : ∀ ⦃f g : Val⦄ ⦃us us' : List Val⦄, WV Q Valid Xc f g → Pw (WV Q Valid Xc) us us' →
      us.length < vs.length →
      SimUpTo (WV Q Valid Xc) n (fun k => applyN P k f us) (fun k => applyN Q k g us') :=
    fun f g us us' hfg hus hl => ih us.length (by omega) (Nat.le_refl _) hfg hus
  have hnil : ∀ ⦃f g : Val⦄, WV Q Valid Xc f g → vs = [] →
      SimUpTo (WV Q Valid Xc) n (fun k => applyN P k f vs) (fun k => applyN Q k g ws) := by
    intro f g hfg hv
    subst hv; cases hvs
    exact (SimUpTo.ok hfg).congr (fun k => applyN_nil' P k f) (fun k => applyN_nil' Q k g)
  have hnc : ∀ ⦃f g : Val⦄, (∀ ρ n b got, f ≠ .clos ρ n b got) → (∀ ρ n b got, g ≠ .clos ρ n b got) →
      WV Q Valid Xc f g → SimUpTo (WV Q Valid Xc) n (fun k => applyN P k f vs) (fun k => applyN Q k g ws) := by
    intro f g hf hg hfg
    cases vs with
    | nil => exact hnil hfg rfl
    | cons v vs' =>
      cases hvs with
      | cons _ _ =>
        exact (SimUpTo.stuck _).congr (fun k => applyN_not_clos P k f v vs' hf) (fun k => applyN_not_clos Q k g _ _ hg)
  cases hfg with
  | lit => exact hnc (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) .lit
  | box => exact hnc (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) .box
  | con h => exact hnc (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) (.con h)
  | idc hρ hg =>
    exact Rel.app_idc structural hfund (pw_of hρ) (pw_of hg) hvs hrest
  | xc hρ hgot hb =>
    rename_i ρ ρ' got got' m b b'
    have hρ' := pw_of hρ
    have hgot' := pw_of hgot
    have hgl := hgot'.length
    have hvl := hvs.length
    cases vs with
    | nil =>
      cases hvs
      exact (SimUpTo.ok (.xc hρ hgot hb)).congr (fun k => applyN_nil' P k _) (fun k => applyN_nil' Q k _)
    | cons v vs' =>
      obtain ⟨w, ws', rfl⟩ : ∃ w ws', ws = w :: ws' := by
        cases ws with
        | nil => cases hvs
        | cons w ws' => exact ⟨w, ws', rfl⟩
      by_cases hg : got.length < m
      · by_cases hu : got.length + (v :: vs').length < m
        · have hu' : got'.length + (w :: ws').length < m := by simp at hvl hu ⊢; omega
          refine (SimUpTo.later fun _ _ => SimUpTo.ok (WV.xc (n := m) hρ (of_pw (hgot'.append hvs)) hb)).congr
            (fun k => ?_) (fun k => ?_)
          · rw [applyN_clos]; simp only [hg, hu, if_true]
          · rw [applyN_clos]; simp only [show got'.length < m by omega, hu', if_true]
        · have hall := hgot'.append hvs
          refine (SimUpTo.bind (d := fun r k => applyN P k r ((got ++ v :: vs').drop m))
            (d' := fun r k => applyN Q k r ((got' ++ w :: ws').drop m))
            (ClockMono.later (eval_mono Q _ [] _)) (fun r => applyN_mono Q r _)
            (SimUpTo.later fun i hi => hxlow i (by omega) hρ hb (of_pw (hall.take m)) (by simp at hu hvl ⊢; omega))
            fun r r' hr => ?_).congr (fun k => ?_) (fun k => ?_)
          · by_cases hnil : ((got ++ v :: vs').drop m) = []
            · have : ((got' ++ w :: ws').drop m) = [] := by
                rw [List.drop_eq_nil_iff] at hnil ⊢; simp at hnil hvl ⊢; omega
              rw [hnil, this]
              exact (SimUpTo.ok hr).congr (fun k => applyN_nil' P k r) (fun k => applyN_nil' Q k r')
            · exact ih _ (by simp at hnil hlen ⊢; omega) (Nat.le_refl _) hr (hall.drop m)
          · rw [applyN_clos]
            simp only [hg, hu, if_true, if_false]
            cases k with
            | zero => rfl
            | succ k => simp only [later_succ, enter]
          · rw [applyN_clos]
            simp only [show got'.length < m by omega, if_true,
              show ¬ (got'.length + (w :: ws').length < m) by simp at hvl hu ⊢; omega, if_false]
            cases k with
            | zero => rfl
            | succ k => simp only [later_succ, enter]
      · refine (SimUpTo.later (c₁ := fun _ => (.stuck : Result Val)) (c₂ := fun _ => .stuck)
          fun _ _ => SimUpTo.stuck _).congr (fun k => ?_) (fun k => ?_)
        · rw [applyN_clos]; simp only [hg, if_false]
        · rw [applyN_clos]; simp only [show ¬ got'.length < m by omega, if_false]
  | walkc hV hrun henv hf hnd hσP hmn hng hgn hgg hpre hpreg hown hownv =>
    rename_i C fuel s s' σP σ0 live facts ρ ρ' got got' nn m b b' oOf wOf
    have hwl := hvs.length
    have hvs' := of_pw hvs
    cases vs with
    | nil => exact hnil (.walkc hV hrun henv hf hnd hσP hmn hng hgn hgg hpre hpreg hown hownv) rfl
    | cons v vs₀ =>
      obtain ⟨w, ws₀, rfl⟩ : ∃ w ws₀, ws = w :: ws₀ := by
        cases ws with
        | nil => cases hvs
        | cons w ws₀ => exact ⟨w, ws₀, rfl⟩
      have hgn' : got'.length < m := by omega
      by_cases hu : got.length + (v :: vs₀).length < nn
      · -- under-saturated: the closures with the arguments added
        have hu' : got'.length + (w :: ws₀).length < m := by simp at hu hwl ⊢; omega
        have hwv : WV Q Valid Xc (.clos ρ nn b (got ++ v :: vs₀)) (.clos ρ' m b' (got' ++ w :: ws₀)) := by
          refine .walkc hV hrun henv hf hnd hσP hmn (by simp; omega) (by simpa using hu)
            (by simp at hwl ⊢; omega) hpre (fun p u hp hu => ?_) hown (fun p u u' hp1 hp2 hu hu' => ?_)
          · rw [List.getElem?_append_left (by omega)] at hu; exact hpreg p u hp hu
          · by_cases hpg : p < got.length
            · rw [List.getElem?_append_left hpg] at hu
              rw [List.getElem?_append_left (by omega)] at hu'
              exact hownv p u u' hp1 hp2 hu hu'
            · rw [List.getElem?_append_right (by omega)] at hu
              rw [List.getElem?_append_right (by omega)] at hu'
              rw [show p - (nn - m) - got'.length = p - got.length by omega] at hu'
              rcases hvs'.get (p - got.length) with ⟨h1, _⟩ | ⟨v1, w1, hv1, hw1, hvw1⟩
              · rw [h1] at hu; cases hu
              · rw [hv1] at hu; rw [hw1] at hu'; cases hu; cases hu'; exact hvw1
        refine (SimUpTo.later (c₁ := fun _ => .ok _) (c₂ := fun _ => .ok _) fun _ _ => SimUpTo.ok hwv).congr
          (fun k => ?_) (fun k => ?_)
        · rw [applyN_clos]; simp only [hgn, if_true, hu]
        · rw [applyN_clos]; simp only [hgn', if_true, hu']
      · -- saturated: the body, then the rest
        have hu' : ¬ (got'.length + (w :: ws₀).length < m) := by simp at hu hwl ⊢; omega
        have hsat : nn ≤ got.length + (v :: vs₀).length := by omega
        refine (SimUpTo.bind (d := fun r k => applyN P k r ((got ++ v :: vs₀).drop nn))
          (d' := fun r k => applyN Q k r ((got' ++ w :: ws₀).drop m))
          (ClockMono.later (eval_mono Q _ [] b')) (fun r => applyN_mono Q r _)
          (SimUpTo.later fun i hi => enter_walkc hlow hsuffix hV hrun henv hf hnd hσP hmn hng hgg hpre hpreg
            hown hownv hvs' hsat hi)
          fun r r' hr => ?_).congr (fun k => ?_) (fun k => ?_)
        · rw [drop_got (by omega), drop_got (by omega)]
          rw [show m - got'.length = nn - got.length by omega]
          by_cases hnil' : (v :: vs₀).drop (nn - got.length) = []
          · have : (w :: ws₀).drop (nn - got.length) = [] := by
              rw [List.drop_eq_nil_iff] at hnil' ⊢; simp at hnil' hwl ⊢; omega
            rw [hnil', this]
            exact (SimUpTo.ok hr).congr (fun k => applyN_nil' P k r) (fun k => applyN_nil' Q k r')
          · exact hrest hr ((pw_of hvs').drop _) (by simp at hnil' ⊢; omega)
        · rw [applyN_clos]
          simp only [hgn, if_true, hu, if_false]
          cases k with
          | zero => rfl
          | succ k => simp only [later_succ, enter]
        · rw [applyN_clos]
          simp only [hgn', if_true, hu', if_false]
          cases k with
          | zero => rfl
          | succ k => simp only [later_succ, enter]

end IxCC.Anf.WalkProof
