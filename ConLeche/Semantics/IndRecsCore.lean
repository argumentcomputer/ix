module

public import ConLeche.Semantics.EnvFactsCons
public import ConLeche.Verify.Denote.EnvExt

public import ConLeche.Verify.Denote.Levels

@[expose] public section

/-!
# The recursor group's **model-free core** (task #161 S7, Wall A)

S6 measured the last wall under `Bridge/DeclInd.lean`'s finding 8 and
found it one level below the residue: the projection walk starts at
`env₃`, the recursor group's output, and `env₃` is not a *cons* of
anything the bridge built — it is a **swap** of the provisional
environment (`EnvS.swap`, `SwapShList`).  An `EnvFacts env₃` therefore
needs, for every fired rule of every swapped recursor, the two facts
`rec_params_le` (`rP ≤ mI`) and `rec_rhs_denotes` (the right-hand
side's denotation at every level instantiation), and until S6 both
lived only inside `RecRuleLawV`, a model-carrying wrapper.

S6 built the storage half (`RuleFacts` / `iotaRulesFactsR` /
`indRecsFoldFacts`, `SetBase/IndBlockR.lean`).  This module is the
other half — the group's `EnvFacts` core, in three pieces:

* `provisionRecsRcore` — `provisionRecsS`'s `EnvFacts` twin, off the
  *relation*; its step is `memberInstallR` (S6);
* `EnvFacts.swap` — `EnvS.swap`'s `EnvFacts` shadow.  It is **strictly
  smaller** than the `EnvS` swap: no `RecCtorsStored`, no
  `SwapNResS`, no `RecRulesV` — an `EnvFacts` has no `rec_ctors`, no
  `basis_pinned` and no law field, so the transport is
  `denote_env_ext hcg.levelsEq hcg.natEq hcg.strEq hcg.projEq` plus the two rule
  facts, taken as hypotheses exactly as `EnvS.swap` takes its law;
* `indRecsCoreR` — `indRecsS`'s tail (`hwf₃`, the block invariant's
  survival, the three preservation facts), whose every ingredient is
  now `RuleFacts`.

**The one join that is not a copy.**  `RuleFacts`'s fired-rule
conjunct denotes the right-hand side *uninstantiated* (that is the
shape `IotaRuleR`'s H1 run exposure stores), while `rec_rhs_denotes`
asks for the *level-instantiated* one.  `denote_instLevels`
(`Verify/Denote/Levels.lean`) is the bridge, at the substituted
assignment `Level.substFn ψ cv.levelParams us`, and its `ValParams`
premise is `EnvFacts.val_params` verbatim.  Nothing semantic is involved.

Model-free by construction: no `V`, no `SetTheory`, no `EnvS`.
-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify

/-! ## The provisioning fold, at the `EnvFacts` level -/

/-! ## The group rule-list swap, at the `EnvFacts` level -/

/-- **The group rule-list swap, model-free**: an `EnvFacts` of the
provisional (rule-less) environment transports to the environment
carrying the checked rule lists, with the *same* valuation —
definitionally.

The two rule fields are hypotheses, exactly as `EnvS.swap` takes
`RecRulesV` as one: they are what the group install proves (there from
the iota bottoms, here from `RuleFacts`). -/

def EnvFacts.swap {env₀ env₃ : Env} (m₀ : EnvFacts env₀)
    (hsw : SwapShList env₀.consts env₃.consts)
    (hwf : EnvWF env₃)
    (hle : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
      (rules : List RecRule),
      env₃.find? n = some (.recInfo cv mI rP rules) →
      ∀ r ∈ rules, RecRule.fire r ≠ .inert → rP ≤ mI)
    (hrhs : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
      (rules : List RecRule),
      env₃.find? n = some (.recInfo cv mI rP rules) →
      ∀ r ∈ rules, RecRule.fire r ≠ .inert →
        ∀ (us : List Level) (ψ : Name → Nat),
          us.length = cv.levelParams.length →
          ∃ R, denoteClosed m₀.cval env₃ ψ
            (r.rhs.instantiateLevelParams cv.levelParams us) = some R) :
    EnvFacts env₃ := by
  have hcorr : ∀ n : Name,
      env₃.find? n = env₀.find? n ∨
      ∃ cv mI rP rules,
        env₀.find? n = some (.recInfo cv mI rP []) ∧
        env₃.find? n = some (.recInfo cv mI rP rules) ∧
        cv.name = n := swapSh_find?_corr hsw
  have hcg : SwapCongr env₀ env₃ := SwapShList.congr hsw
  have hde : ∀ (φ : Name → Nat) (d : Nat) (e : Expr),
      denote m₀.cval env₀ φ d e = denote m₀.cval env₃ φ d e :=
    fun _ => denote_env_ext hcg.levelsEq hcg.natEq hcg.strEq hcg.projEq
  have hdeC : ∀ (φ : Name → Nat) (e : Expr),
      denoteClosed m₀.cval env₀ φ e = denoteClosed m₀.cval env₃ φ e :=
    fun φ e => hde φ 0 e
  have hsame : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      (env₃.find? n = some ci ↔ env₀.find? n = some ci) :=
    fun n ci hnr =>
      ⟨fun h => hcg.findDown n ci h hnr, fun h => hcg.findUp n ci h hnr⟩
  refine
    { cval := m₀.cval
      cval_closed := m₀.cval_closed
      wf := hwf
      val_params := ?_
      ty_denotes := ?_
      defn_eq := ?_
      rec_rhs_denotes := hrhs
      rec_params_le := hle
      proj_ok := ?_
      nat_op_guard := ?_ }
  · -- val_params: the swap keeps every stored `ConstantVal`
    intro n ci hf φ₁ φ₂ hp
    rcases hcorr n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · exact m₀.val_params n ci (by rw [← heq]; exact hf) φ₁ φ₂ hp
    · rw [h₃] at hf
      obtain rfl := Option.some.inj hf
      exact m₀.val_params n _ h₀ φ₁ φ₂ hp
  · -- ty_denotes: the member correspondence plus the denote congruence
    intro c₃ hc₃ ψ
    obtain ⟨c₀, hc₀, hpair⟩ := swapSh_mem_corr hsw c₃ hc₃
    obtain ⟨t, ht⟩ := m₀.ty_denotes c₀ hc₀ ψ
    rcases hpair with rfl | ⟨cv, mI, rP, rules, rfl, rfl⟩
    · exact ⟨t, by rw [← hdeC]; exact ht⟩
    · exact ⟨t, by rw [← hdeC]; exact ht⟩
  · -- defn_eq: a definition is never a swap's right side
    intro cv value hint hmem ψ
    obtain ⟨c₀, hc₀, hpair⟩ := swapSh_mem_corr hsw _ hmem
    rcases hpair with rfl | ⟨cv2, mI, rP, rules, rfl, heq⟩
    · rw [← hdeC]
      exact m₀.defn_eq cv value hint hc₀ ψ
    · exact nomatch heq
  · -- proj_ok: projection tables and their blocks are untouched
    intro n tbl hf i hi
    exact TowerHead.mono (fun n ci hnr hf' => (hsame n ci hnr).mpr hf')
      (m₀.proj_ok n tbl ((hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf) i hi)
  · -- nat_op_guard: keyed on definitions, with the guard congruent
    intro c hmem hst
    obtain ⟨cv, v, hh, hf⟩ := natOpStored_inv hst
    have hf₀ : env₀.find? c = some (.defnInfo cv v hh) :=
      hcg.findDown c _ hf (fun _ _ _ _ hcon => ConstantInfo.noConfusion hcon)
    rw [← hcg.guardEq]
    exact m₀.nat_op_guard c hmem (by simp [natOpStored, hf₀])

/-! ## The swapped environment's four syntactic facts

`EnvFacts.swap` takes `EnvWF env₃` as a hypothesis and needs no
`RecCtorsStored`/`BasisPinnedTT`/`ProjOkT` of its own — but the *P*
lane's carrier (`EnvModel`) carries all four, and the [set] install
proves them inside `indRecsS`.  They are extracted here so that the
ind tier's two swaps (`indRecsCoreR` below and `EnvModelM.swapP`) share
one proof, off `RuleFacts` alone.
-/

/-- **The four syntactic environment facts survive the group swap.** -/

theorem swapEnvFacts {envSelf env₃ : Env} {cvalSelf : TConstVal}
    (hwfS : EnvWF envSelf) (hctorsS : RecCtorsStored envSelf)
    (hbpS : BasisPinnedTT envSelf cvalSelf) (hprojS : ProjOkT envSelf)
    (hswR : SwapShList envSelf.consts env₃.consts)
    (hnresR : SwapNResS envSelf env₃)
    (hentR : ∀ c ∈ env₃.consts, c ∈ envSelf.consts ∨
      ∃ (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
        c = .recInfo cv mI rP rules ∧
        ∀ rl ∈ rules, RuleFacts envSelf cvalSelf cv mI rP rl)
    (hentF : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
      (rules : List RecRule),
      env₃.find? n = some (.recInfo cv mI rP rules) →
      envSelf.find? n = some (.recInfo cv mI rP rules) ∨
      ∀ rl ∈ rules, RuleFacts envSelf cvalSelf cv mI rP rl) :
    EnvWF env₃ ∧ RecCtorsStored env₃ ∧
      BasisPinnedTT env₃ cvalSelf ∧ ProjOkT env₃ := by
  have hcg : SwapCongr envSelf env₃ := SwapShList.congr hswR
  have hcorr : ∀ n : Name,
      env₃.find? n = envSelf.find? n ∨
      ∃ cv mI rP rules,
        envSelf.find? n = some (.recInfo cv mI rP []) ∧
        env₃.find? n = some (.recInfo cv mI rP rules) ∧
        cv.name = n := swapSh_find?_corr hswR
  have hsame : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      (env₃.find? n = some ci ↔ envSelf.find? n = some ci) :=
    fun n ci hnr =>
      ⟨fun h => hcg.findDown n ci h hnr, fun h => hcg.findUp n ci h hnr⟩
  have hres₃ : ∀ e : Expr, e.constsResolve envSelf = true →
      e.constsResolve env₃ = true := by
    intro e he
    rw [← Expr.constsResolve_congr hcg.isSomeEq]
    exact he
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `EnvWF`
    intro c hc
    rcases hentR c hc with hcS | ⟨cv, mI, rP, rules, rfl, hfacts⟩
    · obtain ⟨hSw, hSlp, hSres, hSb, hSdef, hSrec, hStbl, hScaps⟩ := hwfS c hcS
      refine ⟨hSw, hSlp, hres₃ _ hSres, hSb, ?_, ?_, ?_, hScaps⟩
      · intro cv v hint heq
        obtain ⟨d1, d2, d3, d4⟩ := hSdef cv v hint heq
        exact ⟨d1, d2, hres₃ _ d3, d4⟩
      · intro cv mI rP rules heq r hr
        obtain ⟨r1, r2, r3, r4, r5⟩ := hSrec cv mI rP rules heq r hr
        refine ⟨r1, r2, hres₃ _ r3, r4, ?_⟩
        intro lvls pins hfr
        obtain ⟨n1, n2, n3, n4⟩ := r5 lvls pins hfr
        refine ⟨n1, n2, ?_, n4⟩
        intro pin hpin
        obtain ⟨p1, p2, p3, p4⟩ := n3 pin hpin
        exact ⟨p1, p2, hres₃ _ p3, p4⟩
      · intro tbl heq
        obtain ⟨g0, g⟩ := hStbl tbl heq
        refine ⟨g0, fun i b hb => ?_⟩
        obtain ⟨t1, t2, t3, t4⟩ := g i b hb
        exact ⟨t1, t2, hres₃ _ t3, t4⟩
    · obtain ⟨c₀, hc₀, hpair⟩ := swapSh_mem_corr hswR _ hc
      obtain ⟨hSw, hSlp, hSres, hSb, -, -, -, -⟩ := hwfS c₀ hc₀
      have hcvt : c₀.toConstantVal = cv := by
        rcases hpair with rfl | ⟨cv', mI', rP', rules', rfl, heq⟩
        · rfl
        · obtain ⟨rfl, -, -, -⟩ := ConstantInfo.recInfo.inj heq
          rfl
      rw [hcvt] at hSw hSlp hSres hSb
      refine ⟨hSw, hSlp, hres₃ _ hSres, hSb,
        fun _ _ _ hcon => ConstantInfo.noConfusion hcon, ?_,
        fun _ hcon => ConstantInfo.noConfusion hcon,
        fun _ _ hcon => ConstantInfo.noConfusion hcon⟩
      intro cv' mI' rP' rules' heq r hr
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj heq
      obtain ⟨w1, w2, w3, w4, w5, -, -⟩ := hfacts r hr
      refine ⟨w1, w2, hres₃ _ w3, w4, ?_⟩
      intro lvls pins hfr
      obtain ⟨n1, n2, n3, n4⟩ := w5 lvls pins hfr
      refine ⟨n1, n2, ?_, n4⟩
      intro pin hpin
      obtain ⟨p1, p2, p3, p4⟩ := n3 pin hpin
      exact ⟨p1, p2, hres₃ _ p3, p4⟩
  · -- `RecCtorsStored`
    intro n cv mI rP rules hf r hr
    have hkeep : ∀ (m : Name) (ci : ConstantInfo),
        (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
        envSelf.find? m = some ci → env₃.find? m = some ci :=
      fun m ci hnr hfc => hcg.findUp m ci hfc hnr
    rcases hentF n cv mI rP rules hf with hfS | hfacts
    · obtain ⟨⟨cvj, cnP, cnF, hfc⟩, hk, he⟩ :=
        hctorsS n cv mI rP rules hfS r hr
      exact ⟨⟨cvj, cnP, cnF, hkeep _ _
          (fun _ _ _ _ hcon => ConstantInfo.noConfusion hcon) hfc⟩,
        fun hb => recRuleKOf_mono hkeep (hk hb),
        fun hb => recRuleEtaOf_mono hkeep (he hb)⟩
    · obtain ⟨-, -, -, -, -, ⟨cvj, cnP, cnF, hfc⟩, -, hk, he⟩ := hfacts r hr
      -- the swapped recursor is stored under its own constant's name
      have hnR : cv.name = n := by
        rcases hcorr n with heq | ⟨cv', mI', rP', rules', h₀, h₃, hn'⟩
        · rw [heq] at hf
          obtain ⟨-, hfS⟩ : True ∧ envSelf.find? n = some (.recInfo cv mI rP rules) :=
            ⟨trivial, hf⟩
          exact (Env.find?_name hfS)
        · rw [h₃] at hf
          obtain ⟨rfl, -, -, -⟩ := ConstantInfo.recInfo.inj (Option.some.inj hf)
          exact hn'
      exact ⟨⟨cvj, cnP, cnF, hkeep _ _
          (fun _ _ _ _ hcon => ConstantInfo.noConfusion hcon) hfc⟩,
        fun hb => recRuleKOf_mono hkeep (hk hb),
        fun hb => recRuleEtaOf_mono hkeep (hnR ▸ he hb)⟩
  · -- `BasisPinnedTT`: a genuinely swapped entry is never reserved
    intro n ci hf hres
    have hf₀ : envSelf.find? n = some ci := by
      rcases hcorr n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
      · rw [← heq]; exact hf
      · rcases hnresR n cv mI rP rules h₀ h₃ with rfl | hnr
        · rw [h₃] at hf
          obtain rfl := Option.some.inj hf
          exact h₀
        · rw [hnr] at hres
          exact nomatch hres
    exact hbpS n ci hf₀ hres
  · -- `ProjOkT`: projection tables are untouched
    intro n tbl hf i hi
    exact TowerHead.mono (fun n ci hnr hf' => (hsame n ci hnr).mpr hf')
      (hprojS n tbl ((hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf) i hi)

/-! ## The group phase, at the `EnvFacts` level -/


end ConLeche.Semantics
