module

public import ConLeche.Model.IotaRuleNested
import ConLeche.Verify.Denote.EnvExt
public section

/-!
# The group rule-list swap, P tier (task #161, IND TIER part 10)

`Install/SwapS.lean`'s twin one currency over: `EnvModelM.swapP`
transports the P invariant across the step that attaches a recursor
group's checked rule lists to its rule-less provisioned entries.

The workhorse is `denoteMeta_env_ext` — the `denoteMeta` mirror of
`denote_env_ext` (`Verify/Denote/EnvExt.lean`).  It is an **equation**
with no `ConstsBound` premise, unlike the extension crossing
(`denoteMeta_envExtend_mono`): a swap changes no stored name, so the
reading's three environment consultations — the `.const` clause's
`find?` (through the stored level parameters only), the two literal
guards, and the string spine's `levelParamsAt` — are all congruent.
That is why every field of the invariant crosses in *both* directions
and the contravariant readings need no determinism trick here.

The three environment-level facts about the *result* — `EnvWF`,
`RecCtorsStored`, `RecRules` — are hypotheses, exactly as in v1: they
are what the group install proves (the last through `iotaRules`), and
taking them here keeps the transport free of the per-rule content.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule IndCaps)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The reading across a level-preserving correspondence -/

/-- **`denoteMeta` reads the environment only through the stored level
parameters and the two literal guards** — `denote_env_ext`'s twin.  An
equation, so a law's `denoteMeta` *hypotheses* and *conclusions* both move
across it for free, which is what makes the fired-form fields
transportable at all. -/
theorem denoteMeta_env_ext {acval : Name → (Name → Nat) → AnnotTerm}
    {env₁ env₂ : Env} {φ : Name → Nat}
    (henvLev : ∀ n,
      (env₁.find? n).map (fun ci => ci.toConstantVal.levelParams) =
      (env₂.find? n).map (fun ci => ci.toConstantVal.levelParams))
    (hnat : ConLeche.natLitSupported env₁ = ConLeche.natLitSupported env₂)
    (hstr : ConLeche.strLitSupported env₁ = ConLeche.strLitSupported env₂)
    (hproj : ∀ (sn : Name) (i : Nat),
      env₁.findProj? sn i = env₂.findProj? sn i) :
    ∀ (d : Nat) (e : Expr),
      denoteMeta acval env₁ φ d e = denoteMeta acval env₂ φ d e := by
  intro d e
  induction d, e using denoteMeta.induct (env := env₁) with
  | case1 d u => rw [denoteMeta, denoteMeta]
  | case2 d idx ty => rw [denoteMeta, denoteMeta]
  | case3 d n us ci hf hlen =>
    have h := henvLev n
    rw [hf] at h
    cases hf₂ : env₂.find? n with
    | none => rw [hf₂] at h; exact nomatch h
    | some ci₂ =>
      rw [hf₂] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [denoteMeta, hf, denoteMeta, hf₂]
      dsimp only
      rw [if_pos hlen, if_pos (h ▸ hlen), h]
  | case4 d n us ci hf hlen =>
    have h := henvLev n
    rw [hf] at h
    cases hf₂ : env₂.find? n with
    | none => rw [hf₂] at h; exact nomatch h
    | some ci₂ =>
      rw [hf₂] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [denoteMeta, hf, denoteMeta, hf₂]
      dsimp only
      rw [if_neg hlen, if_neg (fun hh => hlen (h ▸ hh))]
  | case5 d n us hf =>
    have h := henvLev n
    rw [hf] at h
    cases hf₂ : env₂.find? n with
    | none => rw [denoteMeta, hf, denoteMeta, hf₂]
    | some ci₂ => rw [hf₂] at h; exact nomatch h
  | case6 d ty body m ihty ihbody =>
    rw [denoteMeta, denoteMeta, ihty, ihbody]
  | case7 d ty body m ihty ihbody =>
    rw [denoteMeta, denoteMeta, ihty, ihbody]
  | case8 d f a ihf iha => rw [denoteMeta, denoteMeta, ihf, iha]
  | case9 d ty val body =>
    rw [denoteMeta, denoteMeta]
  | case10 d sn i e ihe =>
    rw [denoteMeta, denoteMeta, ihe, hproj sn i]
  | case11 d n hsup =>
    rw [denoteMeta, if_pos hsup, denoteMeta, if_pos (hnat ▸ hsup)]
  | case12 d n hsup =>
    rw [denoteMeta, if_neg hsup, denoteMeta,
      if_neg (fun h => hsup (hnat.trans h))]
  | case13 d s hsup =>
    rw [denoteMeta, if_pos hsup, denoteMeta, if_pos (hstr ▸ hsup),
      levelParamsAt_ext (henvLev ConLeche.listNilName),
      levelParamsAt_ext (henvLev ConLeche.listConsName)]
  | case14 d s hsup =>
    rw [denoteMeta, if_neg hsup, denoteMeta,
      if_neg (fun h => hsup (hstr.trans h))]
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat' hstr' =>
    cases x with
    | bvar i => rw [denoteMeta.eq_def, denoteMeta.eq_def]
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b m => exact absurd rfl (hpi ty b m)
    | lam ty b m => exact absurd rfl (hlam ty b m)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat' n)
      | strVal s => exact absurd rfl (hstr' s)

/-- The reading crosses a swap congruence. -/
theorem denoteMeta_swap {acval : Name → (Name → Nat) → AnnotTerm}
    {env₀ env₃ : Env} (hcg : ConLeche.SwapCongr env₀ env₃)
    (φ : Name → Nat) (d : Nat) (e : Expr) :
    denoteMeta acval env₀ φ d e = denoteMeta acval env₃ φ d e :=
  denoteMeta_env_ext hcg.levelsEq hcg.natEq hcg.strEq hcg.projEq d e

/-! ## The fired modeled-iota contract across the swap -/

/-- **A fired law reads the environment only through `denoteMeta` and the
constructor's lookup, so it crosses the rule-list swap**
(`RecRuleLawV.swapS`'s twin).  Both carriers have the *same* `acval`;
the statement mentions the environment nowhere else. -/
theorem RecRuleLaw.swapP {env₀ env₃ : Env}
    (hcg : ConLeche.SwapCongr env₀ env₃)
    {m₀ : EnvModel V env₀} {m₃ : EnvModel V env₃}
    (hac : m₃.acval = m₀.acval)
    {φ : Name → Nat} {n : Name} {cv : ConstantVal} {mI rP : Nat}
    {rl : RecRule} (h : RecRuleLaw m₀ φ n cv mI rP rl) :
    RecRuleLaw m₃ φ n cv mI rP rl := by
  have hde : ∀ (d : Nat) (e : Expr),
      denoteMeta m₀.acval env₀ φ d e = denoteMeta m₀.acval env₃ φ d e :=
    fun d e => denoteMeta_swap hcg φ d e
  unfold RecRuleLaw at h ⊢
  rw [hac]
  obtain ⟨hle, h⟩ := h
  refine ⟨hle, ?_⟩
  intro us hus
  obtain ⟨Ra, hRa, hokRa, hpins, hlaw⟩ := h us hus
  refine ⟨Ra, ?_, hokRa, ?_, ?_⟩
  · rw [← hde]; exact hRa
  · -- the pins' carried readings and their guarded gradings
    intro lvls pins hfr i hi
    obtain ⟨vpa, hvpa, hgr⟩ := hpins lvls pins hfr i hi
    refine ⟨vpa, by rw [← hde]; exact hvpa, ?_⟩
    intro ρ zs TVa restR hzl hzok hTVa hfit
    rw [← hde] at hTVa
    exact hgr ρ zs TVa restR hzl hzok hTVa hfit
  · intro cvj cnP cnF hfc usj ρ xs ys TVa TVja restR restC hxl hyl hujl
      hlev hplain hnested hidx hTVa hTVja hfitR hfitC
    rw [← hde] at hTVa hTVja
    refine hlaw cvj cnP cnF
      (hcg.findDown _ _ hfc (fun _ _ _ _ hcon => nomatch hcon)) usj ρ
      xs ys TVa TVja restR restC hxl hyl hujl hlev hplain ?_ hidx hTVa
      hTVja hfitR hfitC
    intro lvls pins hfr i hi vpa hvpa
    refine hnested lvls pins hfr i hi vpa ?_
    rw [← hde]
    exact hvpa

/-! ## The P invariant across the swap -/

set_option maxHeartbeats 3200000 in
/-- **The group rule-list swap, P tier**: an invariant of the
provisional (rule-less) environment transports to the environment
carrying the checked rule lists, with the *same* annotated
valuation. -/
theorem EnvModelM.swapP {μ : CheckMode} {env₀ env₃ : Env}
    (mp : EnvModelM V μ env₀)
    (hsw : ConLeche.SwapShList env₀.consts env₃.consts)
    -- the four syntactic environment facts at the swapped
    -- environment (`swapEnvFacts`, `SetBase/IndRecsCoreR.lean`;
    -- task #161 S7, Wall C): taking them rather than rebuilding them
    -- keeps this file free of the rule facts, exactly as taking the
    -- v1 carrier used to
    (hwf₃ : EnvWF env₃) (hctors₃ : ConLeche.RecCtorsStored env₃)
    (hbp₃ : BasisPinnedTT env₃ mp.base2.cvalE)
    (hproj₃ : ProjOkT env₃)
    (hrecP : ∀ (m₃ : EnvModel V env₃), m₃.acval = mp.base2.acval →
      ∀ φ : Name → Nat, RecRules m₃ φ) :
    ∃ mp₃ : EnvModelM V μ env₃, mp₃.base2.acval = mp.base2.acval ∧
      mp₃.base2.cvalE = mp.base2.cvalE := by
  have hcg : ConLeche.SwapCongr env₀ env₃ := ConLeche.SwapShList.congr hsw
  have hcorr := ConLeche.swapSh_find?_corr hsw
  have hde : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr),
      denoteMeta mp.base2.acval env₀ ψ d e
        = denoteMeta mp.base2.acval env₃ ψ d e :=
    fun ψ d e => denoteMeta_swap hcg ψ d e
  -- an unchanged lookup, either way
  have hsame : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      (env₃.find? n = some ci ↔ env₀.find? n = some ci) :=
    fun n ci hnr =>
      ⟨fun h => hcg.findDown n ci h hnr, fun h => hcg.findUp n ci h hnr⟩
  -- the member correspondence, at the level of `toConstantVal`
  have hmemcorr : ∀ c₃ ∈ env₃.consts, ∃ c₀ ∈ env₀.consts,
      c₀.toConstantVal = c₃.toConstantVal ∧ c₀.name = c₃.name := by
    intro c₃ hc₃
    obtain ⟨c₀, hc₀, hpair⟩ := ConLeche.swapSh_mem_corr hsw c₃ hc₃
    rcases hpair with rfl | ⟨cv, mI, rP, rules, rfl, rfl⟩
    · exact ⟨c₀, hc₀, rfl, rfl⟩
    · exact ⟨_, hc₀, rfl, rfl⟩
  refine ⟨{ base2 :=
              { wf := hwf₃
                acval := mp.base2.acval
                cval_closedL := fun n ψ => mp.base2.cval_closedL n ψ
                basis_pinnedL := hbp₃
                proj_ok := hproj₃
                rec_ctors := hctors₃
                acval_closed := mp.base2.acval_closed
                acval_params := by
                  intro n ci hf ψ₁ ψ₂ hp
                  rcases hcorr n with heq |
                    ⟨cv, mI, rP, rules, h₀, h₃, -⟩
                  · exact mp.base2.acval_params n ci
                      (by rw [← heq]; exact hf) ψ₁ ψ₂ hp
                  · rw [h₃] at hf
                    obtain rfl := Option.some.inj hf
                    exact mp.base2.acval_params n _ h₀ ψ₁ ψ₂ hp
                acval_wellDenoted := mp.base2.acval_wellDenoted }
            acval_validV := mp.acval_validV
            type_reads := ?_
            type_wellDenotedV := ?_
            mem_type := ?_
            defn_reads := ?_
            nat_heads := ?_
            nat_ops := ?_
            div_mod := ?_
            eq_law := ?_
            caps_ok := ?_
            rec_rules := hrecP _ rfl
            reduce_ops := ?_
            tower_ok := ?_ },
          rfl, rfl⟩
  · -- `type_reads`
    intro c hc ψ
    obtain ⟨c₀, hc₀, hcv, -⟩ := hmemcorr c hc
    obtain ⟨ta, hta⟩ := mp.type_reads c₀ hc₀ ψ
    exact ⟨ta, by rw [← hde, ← hcv]; exact hta⟩
  · -- `type_wellDenotedV`
    intro c hc ψ ta hta ρ
    obtain ⟨c₀, hc₀, hcv, -⟩ := hmemcorr c hc
    rw [← hde, ← hcv] at hta
    exact mp.type_wellDenotedV c₀ hc₀ ψ ta hta ρ
  · -- `mem_type`: the swap touches recursors only, so the tower
    -- exclusion carries over
    intro c hc ψ ta hta ρ
    obtain ⟨c₀, hc₀, hpair⟩ := ConLeche.swapSh_mem_corr hsw c hc
    have hcv : c₀.toConstantVal = c.toConstantVal := by
      rcases hpair with rfl | ⟨cv, mI, rP, rules, rfl, rfl⟩ <;> rfl
    have hname : c₀.name = c.name := by
      rcases hpair with rfl | ⟨cv, mI, rP, rules, rfl, rfl⟩ <;> rfl
    rw [← hde, ← hcv] at hta
    have := mp.mem_type c₀ hc₀ ψ ta hta ρ
    rw [hname] at this
    exact this
  · -- `defn_reads`
    intro ψ cv value hmem
    have hmem₀ : ∃ hint : ConLeche.ReducibilityHint,
        ConstantInfo.defnInfo cv value hint ∈ env₀.consts := by
      obtain ⟨hint, hd⟩ := hmem
      obtain ⟨c₀, hc₀, hpair⟩ := ConLeche.swapSh_mem_corr hsw _ hd
      rcases hpair with rfl | ⟨cv2, mI, rP, rules, rfl, heq⟩
      · exact ⟨hint, hc₀⟩
      · exact nomatch heq
    rw [← hde]
    exact mp.defn_reads ψ cv value hmem₀
  · -- `nat_heads`
    intro φ hsup ρ
    exact mp.nat_heads φ (hcg.natEq ▸ hsup) ρ
  · -- `nat_ops`
    intro φ c hc cv value hint hf
    obtain ⟨hgu, hlaw⟩ := mp.nat_ops φ c hc cv value hint
      ((hsame _ _ (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
    refine ⟨by rw [← hcg.guardEq]; exact hgu, ?_⟩
    intro eq heq
    obtain ⟨L, R, hL, hR, hval⟩ := hlaw eq heq
    exact ⟨L, R, by rw [← hde]; exact hL,
      by rw [← hde]; exact hR, hval⟩
  · -- `div_mod`
    intro φ c hc cv value hint hf
    obtain ⟨hgu, hlaw⟩ := mp.div_mod φ c hc cv value hint
      ((hsame _ _ (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
    exact ⟨by rw [← hcg.guardEq]; exact hgu, hlaw⟩
  · -- `eq_law`: `Eq` is stored as an `indInfo`, so it is never swapped
    intro hf
    exact mp.eq_law
      ((hsame eqName eqA
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
  · -- `caps_ok`
    obtain ⟨he, hu⟩ := mp.caps_ok
    have hfam : ∀ (T : Name) (caps : IndCaps),
        ConLeche.EtaFamilyStored env₃ T caps →
        ConLeche.EtaFamilyStored env₀ T caps := by
      intro T caps hst
      obtain ⟨h1, ⟨cvC, cnP, cnF, hC⟩, h3⟩ := hst
      refine ⟨h1, ⟨cvC, cnP, cnF, (hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hC⟩, ?_⟩
      intro j hj
      obtain ⟨cv, mI, rP, rules, hfj⟩ := h3 j hj
      rcases hcorr (ConLeche.projFnName T j) with heq |
        ⟨cv2, mI2, rP2, rules2, h₀, h₃, -⟩
      · exact ⟨cv, mI, rP, rules, by rw [← heq]; exact hfj⟩
      · exact ⟨cv2, mI2, rP2, [], h₀⟩
    refine ⟨?_, ?_⟩
    · intro T cvT caps hf hcap hres hfamS φ' us hus
      obtain ⟨TVa, hTVa, hokT, hlaw⟩ :=
        he T cvT caps ((hsame _ _
          (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf) hcap
          hres (hfam T caps hfamS) φ' us hus
      exact ⟨TVa, by rw [← hde]; exact hTVa, hokT, hlaw⟩
    · intro T cvT caps hf hcap hres φ' us hus
      obtain ⟨TVa, hTVa, hokT, hlaw⟩ :=
        hu T cvT caps ((hsame _ _
          (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf) hcap
          hres φ' us hus
      exact ⟨TVa, by rw [← hde]; exact hTVa, hokT, hlaw⟩
  · -- `reduce_ops`
    intro c hc cv hf hpin
    obtain ⟨hs, hlaw⟩ := mp.reduce_ops c hc cv
      ((hsame _ _ (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
      hpin
    exact ⟨by rw [← hcg.isSomeEq]; exact hs, hlaw⟩
  · -- `tower_ok` (task #175 wiring W5): a table entry, a former and a
    -- constructor are never recursors, so every lookup the law reads
    -- is unchanged by the swap, and the readings are `hde`
    intro φ T i entry hf
    have hfP : env₀.findProj? T i = some entry := by
      obtain ⟨tbl, h3, hi, rfl⟩ := ConLeche.Env.findProj?_some hf
      have h0 := (hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp h3
      exact ConLeche.Env.findProj?_of_table h0 hi
    obtain ⟨hsn, hidx, hlt, ⟨cvT, capsT, hfT, hlpsT⟩, hO5, cvC, hfC, hlpsC,
      hlaw, hetaL⟩ := mp.tower_ok φ T i entry hfP
    refine ⟨hsn, hidx, hlt, ⟨cvT, capsT, (hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mpr hfT, hlpsT⟩,
      hO5, cvC, (hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mpr hfC, hlpsC,
      fun us hus => ?_, ?_⟩
    · obtain ⟨⟨Ta, hTa, hA⟩, ⟨TCa, hTCa, hB⟩⟩ := hlaw us hus
      exact ⟨⟨Ta, by rw [← hde]; exact hTa, hA⟩,
        ⟨TCa, by rw [← hde]; exact hTCa, hB⟩⟩
    · -- (C) the η law (task #175 W4c): the former's lookup is unchanged
      -- by the swap, and the reading is `hde`
      intro cvT' capsT' hfT' us hus
      obtain ⟨TVa, hTVa, hok, hlaw'⟩ := hetaL cvT' capsT' ((hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hfT') us hus
      exact ⟨TVa, by rw [← hde]; exact hTVa, hok, hlaw'⟩

end ConLeche.Model
