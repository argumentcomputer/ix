module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Annot.BitClosed

public section

/-!
# The soundness of the reduction rules (task #305, lanes S-red / S-iota)

One lemma per constructor of `Red`: the motives of its derivation
premises (the induction hypotheses) and its side conditions give the
motive of its conclusion.  The master induction (`Sound.lean`) is the
only place that mentions derivations; these lemmas are pure semantics,
mined from the `Model/Steps/*` rows each docstring names — the tier
they cite was deleted at the task #305 closing.

Lane S-red owns this file; `iota` and the three rescues are in
`IotaSound.lean` (lane S-iota).
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env}
  {φ : Name → Nat}

theorem Red.refl_sound {d : Nat} {e : Expr} : RedSem m φ d e e := by
  intro hf Δa ea _ hea hg
  exact ⟨hf, fun _ hl => hl, ea, hea, hg, fun _ _ => rfl⟩

theorem Red.trans_sound {d : Nat} {e₁ e₂ e₃ : Expr}
    (h₁ : RedSem m φ d e₁ e₂) (h₂ : RedSem m φ d e₂ e₃) :
    RedSem m φ d e₁ e₃ := by
  intro hf Δa ea hC hea hg
  obtain ⟨hf₂, hsub₂, ea₂, hea₂, hg₂, heq₂⟩ := h₁ hf hC hea hg
  obtain ⟨hf₃, hsub₃, ea₃, hea₃, hg₃, heq₃⟩ :=
    h₂ hf₂ (hC.of_subset hsub₂) hea₂ hg₂
  exact ⟨hf₃, fun l hl => hsub₂ l (hsub₃ l hl), ea₃, hea₃, hg₃,
    fun ρ hρ => (heq₂ ρ hρ).trans (heq₃ ρ hρ)⟩

/-- `whnfCore_app_claim`'s head-reduction half (`Steps/Whnf.lean:509`)
+ `frame_appFn` (`Stuck.lean:206`). -/
theorem Red.appFn_sound {d : Nat} {f f' a : Expr}
    (hf : RedSem m φ d f f') : RedSem m φ d (.app f a) (.app f' a) := by
  intro hf Δa ea hC hea hg
  obtain ⟨hws, hb, hLb⟩ := hf
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv hea
  have hokf : Graded V Δa fa := by
    intro ρ hρ
    have hx := hg ρ hρ
    exact ⟨by have h1 := hx.1; rw [WellDenoted_app] at h1; exact h1.1,
      by have h2 := hx.2; rw [AnnotValid_app] at h2; exact h2.1⟩
  have hoka : Graded V Δa aa := by
    intro ρ hρ
    have hx := hg ρ hρ
    exact ⟨by have h1 := hx.1; rw [WellDenoted_app] at h1; exact h1.2.1,
      by have h2 := hx.2; rw [AnnotValid_app] at h2; exact h2.2⟩
  obtain ⟨⟨hwf', hbf', hLf'⟩, hsubf, fa', hfa', hgf', heqf⟩ :=
    hf ⟨hws.1, hb.1, hLf⟩ hC.app_fn hfa hokf
  refine ⟨⟨by simp only [Expr.WScoped]; exact ⟨hwf', hws.2⟩, by
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hbf', hb.2⟩, fun l hl => ?_⟩, fun l hl => ?_,
    .app fa' aa, by rw [denoteMeta_app, hfa', haa]; rfl, ?_, ?_⟩
  · simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact hLf' l hl
    · exact hLa l hl
  · simp only [Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact Or.inl (hsubf l hl)
    · exact Or.inr hl
  · intro ρ hρ
    have hx := hg ρ hρ
    refine ⟨?_, ?_⟩
    · have hx1 := hx.1
      rw [WellDenoted_app] at hx1
      obtain ⟨-, hoka1, v', A, B, h1, h2, h3⟩ := hx1
      rw [WellDenoted_app]
      exact ⟨(hgf' ρ hρ).1, hoka1, v', A, B, (heqf ρ hρ) ▸ h1, h2, h3⟩
    · rw [AnnotValid_app]
      exact ⟨(hgf' ρ hρ).2, (hoka ρ hρ).2⟩
  · intro ρ hρ
    rw [interp_app, interp_app, heqf ρ hρ]


/-- The `.proj` clause's scrutinee reduction (`projStep_of_claims`'s
stuck branch, `Steps/ProjRows.lean:278`; `WellDenotedV_projAV_congr`). -/
theorem Red.projArg_sound {d : Nat} {sn : Name}
    {i : Nat} {e e' : Expr} (he : RedSem m φ d e e') :
    RedSem m φ d (.proj sn i e) (.proj sn i e') := by
  intro hf Δa ea hC hea hg
  obtain ⟨hws, hb, hLb⟩ := hf
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hsube : ∀ l ∈ e.fvarLeaves, l ∈ (Expr.proj sn i e).fvarLeaves :=
    fun l hl => by simpa [Expr.fvarLeaves] using hl
  have hLe : Expr.LeavesBounded e := fun l hl => hLb l (hsube l hl)
  have hCe : CtxOk m φ d Δa e := hC.of_subset hsube
  obtain ⟨vp, hvp, hrd⟩ := denoteMeta_proj_inv hea
  have hokVp : Graded V Δa vp := by
    intro σ hσ
    rcases hrd with ⟨_, -, rfl⟩ | ⟨-, hdec⟩
    · exact ProjAV.hoistV (hg σ hσ)
    · rcases AnnotTerm.projPair?_cases hdec with rfl | rfl
      · exact ⟨by have h1 := (hg σ hσ).1; rw [WellDenoted_fst] at h1; exact h1.1,
          by have h2 := (hg σ hσ).2; rwa [AnnotValid_fst] at h2⟩
      · exact ⟨by have h1 := (hg σ hσ).1; rw [WellDenoted_snd] at h1; exact h1.1,
          by have h2 := (hg σ hσ).2; rwa [AnnotValid_snd] at h2⟩
  obtain ⟨⟨hw', hb', hL'⟩, hsub, vp', hvp', hg', heq⟩ :=
    he ⟨hws, hb, hLe⟩ hCe hvp hokVp
  refine ⟨⟨by simp only [Expr.WScoped]; exact hw',
      by simp only [Expr.looseBVarsBounded]; exact hb',
      fun l hl => hL' l (by simpa [Expr.fvarLeaves] using hl)⟩,
    fun l hl => hsube l (hsub l (by simpa [Expr.fvarLeaves] using hl)), ?_⟩
  rcases hrd with ⟨entry, hfe, rfl⟩ | ⟨hnt, hdec⟩
  · refine ⟨projAV (i + entry.off) vp', ?_,
      fun σ hσ => ProjAV.congrV (heq σ hσ) (hg' σ hσ) (hg σ hσ),
      fun σ hσ => ProjAV.interp_congr (heq σ hσ)⟩
    rw [denoteMeta, hvp', hfe]; rfl
  · obtain ⟨x', hx'⟩ :=
      AnnotTerm.projPair?_exists_of_lt (AnnotTerm.lt_of_projPair? hdec) vp'
    have hred : denoteMeta m.acval env φ d (.proj sn i e') = some x' := by
      rw [denoteMeta, hvp', hnt]; exact hx'
    rcases AnnotTerm.projPair?_cases₂ hdec hx' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨.fst vp', hred, fun σ hσ => ?_,
        fun σ hσ => by rw [interp_fst, interp_fst, heq σ hσ]⟩
      refine ⟨?_, by rw [AnnotValid_fst]; exact (hg' σ hσ).2⟩
      have h1 := (hg σ hσ).1
      rw [WellDenoted_fst] at h1 ⊢
      obtain ⟨-, u, v, A, Bf, hsig, hA, hfib⟩ := h1
      exact ⟨(hg' σ hσ).1, u, v, A, Bf, (heq σ hσ) ▸ hsig, hA, hfib⟩
    · refine ⟨.snd vp', hred, fun σ hσ => ?_,
        fun σ hσ => by rw [interp_snd, interp_snd, heq σ hσ]⟩
      refine ⟨?_, by rw [AnnotValid_snd]; exact (hg' σ hσ).2⟩
      have h1 := (hg σ hσ).1
      rw [WellDenoted_snd] at h1 ⊢
      obtain ⟨-, u, v, A, Bf, hsig, hA, hfib⟩ := h1
      exact ⟨(hg' σ hσ).1, u, v, A, Bf, (heq σ hσ) ▸ hsig, hA, hfib⟩


/-- The β redex's syntactic side, shared by the gated and the certified
rule: the reduct's frame, its leaf inclusion and its reading. -/
theorem beta_syntax {d : Nat} {ty body a : Expr} {mb : ConLeche.BinderMeta}
    {ba aa : AnnotTerm}
    (hws : Expr.WScoped d (.app (.lam ty body mb) a))
    (hb : (Expr.app (.lam ty body mb) a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app (.lam ty body mb) a))
    (hbb : denoteMeta m.acval env φ (d + 1)
      (body.instantiate1 (.fvar d ty)) = some ba)
    (haa : denoteMeta m.acval env φ d a = some aa) :
    Frame d (body.instantiate1 a) ∧
      LeavesSub (body.instantiate1 a) (.app (.lam ty body mb) a) ∧
      denoteMeta m.acval env φ d (body.instantiate1 a) = some (ba.inst aa) := by
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hsubred : LeavesSub (body.instantiate1 a) (.app (.lam ty body mb) a) := by
    intro l hl
    rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · simp [Expr.fvarLeaves, h2]
    · simp [Expr.fvarLeaves, h2]
  refine ⟨⟨ConLeche.Expr.WScoped.instantiate1_gen hws.2 0 hws.1.2,
      ConLeche.Expr.looseBVarsBounded_instantiate1_gen hb.2 hb.1.2,
      fun l hl => hLb l (hsubred l hl)⟩, hsubred, ?_⟩
  rw [denoteMeta_beta m.acval_closed (acval_inst_self m)
    (ty := ty) hws.1.2.fvarsBelow hws.2 hb.2 haa 0, hbb]
  rfl

/-- `WellDenotedV_beta_gate` (`Steps/Gate.lean:80`) + `denoteMeta_beta`. -/
theorem Red.betaGate_sound {d : Nat}
    {ty body a : Expr} {mb : BinderMeta} (hnev : mb.pw.isNever = true) :
    RedSem m φ d (.app (.lam ty body mb) a) (body.instantiate1 a) := by
  intro hf Δa ea hC hea hg
  obtain ⟨hws, hb, hLb⟩ := hf
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv hea
  obtain ⟨tya, ba, htya, hbb, rfl⟩ := denoteMeta_lam_inv hfa
  obtain ⟨hfr, hsub, hred⟩ := beta_syntax hws hb hLb hbb haa
  have hstep : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ (.app (.lam (pwBit φ mb.pw) tya ba) aa)
          = interp V ρ (ba.inst aa) ∧
        WellDenotedV V ρ (ba.inst aa) := fun ρ hρ =>
    betaPosV (pwBit_ne_zero_of_isNever hnev φ) (hg ρ hρ)
  exact ⟨hfr, hsub, ba.inst aa, hred, fun ρ hρ => (hstep ρ hρ).2,
    fun ρ hρ => (hstep ρ hρ).1⟩

/-- `WellDenotedV_beta_pos` / `WellDenotedV_beta_zero` with the
certificate's membership (`betaCert_of_claims`, `Steps/Whnf.lean:424`). -/
theorem Red.beta_sound {d : Nat}
    {ty body a ta : Expr} {mb : BinderMeta}
    (hta : InferSemIO m φ d a ta) (hd : DefEqSem m φ d ta ty) :
    RedSem m φ d (.app (.lam ty body mb) a) (body.instantiate1 a) := by
  intro hf Δa ea hC hea hg
  obtain ⟨hws, hb, hLb⟩ := hf
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv hea
  obtain ⟨tya, ba, htya, hbb, rfl⟩ := denoteMeta_lam_inv hfa
  obtain ⟨hfr, hsub, hred⟩ := beta_syntax hws hb hLb hbb haa
  obtain ⟨hgf, hga⟩ := graded_app hg
  -- the two sides of the β certificate
  have hwsA := hws
  have hbA := hb
  simp only [Expr.WScoped] at hwsA
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbA
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  obtain ⟨hfta, hsubta, taA, htaA, hgtaA, hmemA⟩ :=
    hta ⟨hwsA.2, hbA.2, hLa⟩ hC.app_arg haa hga
  have hmem : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ aa ∈ˢ interp V ρ tya := by
    intro ρ hρ
    have h1 := hmemA ρ hρ
    rw [hd hfta ⟨hwsA.1.1, hbA.1.1, hLty⟩ (hC.app_arg.of_subset hsubta)
      hC.app_fn.lam_ty htaA htya hgtaA (fun σ hσ => lamDomV (hgf σ hσ))
      ρ hρ] at h1
    exact h1
  have hstep : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ (.app (.lam (pwBit φ mb.pw) tya ba) aa)
          = interp V ρ (ba.inst aa) ∧
        WellDenotedV V ρ (ba.inst aa) := by
    intro ρ hρ
    by_cases hz : pwBit φ mb.pw = 0
    · rw [hz] at hg ⊢
      exact betaZeroV (hg ρ hρ) (hmem ρ hρ)
    · exact betaPosV hz (hg ρ hρ)
  exact ⟨hfr, hsub, ba.inst aa, hred, fun ρ hρ => (hstep ρ hρ).2,
    fun ρ hρ => (hstep ρ hρ).1⟩

/-- The δ identity (`delta_of`, `Steps/Whnf.lean:329`: the same
annotation reads the unfolding) + `unfoldDefinition_WScoped`. -/
theorem Red.delta_sound (hin : RulesInputs V m φ) {d : Nat} {e e' : Expr}
    (h : ConLeche.unfoldDefinition env e = some e') : RedSem m φ d e e' := by
  intro hf Δa ea _ hea hg
  refine ⟨⟨ConLeche.unfoldDefinition_WScoped m.wf h hf.1,
      ConLeche.unfoldDefinition_looseBVars m.wf h hf.2.1,
      fun l hl => hf.2.2 l (ConLeche.unfoldDefinition_fvarLeaves m.wf h l hl)⟩,
    fun l hl => ConLeche.unfoldDefinition_fvarLeaves m.wf h l hl,
    ea, denoteMeta_unfoldDefinition hin.defn h hea, hg, fun _ _ => rfl⟩

/-- `denoteMeta_litToCtorIfNat` + `frame_litToCtorIfNat`
(`Steps/Major.lean:66`, `:92`). -/
theorem Red.natLit_sound {d n : Nat} (h : ConLeche.natLitSupported env = true) :
    RedSem m φ d (.lit (.natVal n)) (natLitToConstructor n) := by
  intro _ Δa ea _ hea hg
  refine ⟨⟨ConLeche.natLitToConstructor_WScoped n,
      ConLeche.natLitToConstructor_looseBVars n, ?_⟩, ?_, ea, ?_, hg,
    fun _ _ => rfl⟩
  · intro l hl
    rw [ConLeche.natLitToConstructor_fvarLeaves] at hl; exact nomatch hl
  · intro l hl
    rw [ConLeche.natLitToConstructor_fvarLeaves] at hl; exact nomatch hl
  · rw [denoteMeta_natLitToConstructor h]; exact hea

/-- `denotePStrLit_of_guard` (`Steps/Stuck.lean:540`). -/
theorem Red.strLit_sound {d : Nat} {s : String}
    (h : ConLeche.strLitSupported env = true) :
    RedSem m φ d (.lit (.strVal s)) (strLitToConstructor s) := by
  intro _ Δa ea _ hea hg
  refine ⟨⟨ConLeche.strLitToConstructor_WScoped s d,
      ConLeche.strLitToConstructor_looseBVars s 0, ?_⟩, ?_, ea, ?_, hg,
    fun _ _ => rfl⟩
  · intro l hl
    rw [ConLeche.strLitToConstructor_fvarLeaves] at hl; exact nomatch hl
  · intro l hl
    rw [ConLeche.strLitToConstructor_fvarLeaves] at hl; exact nomatch hl
  · rw [denoteMeta_strLitToConstructor h]; exact hea

/-- The successor row at the reduced argument (`NatSuccRow`). -/
theorem Red.natSucc_sound (hin : RulesInputs V m φ) {d : Nat} {a w : Expr}
    {n : Nat} (hsup : ConLeche.natLitSupported env = true)
    (hw : RedSem m φ d a w) (hn : ConLeche.rawNatLit? w = some n) :
    RedSem m φ d (.app (.const natSuccName []) a) (.lit (.natVal (n + 1))) := by
  intro hf Δa ea hC hea hg
  obtain ⟨hws, hb, hLb⟩ := hf
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv hea
  have hokf : Graded V Δa fa := fun σ hσ =>
    ⟨by have h1 := (hg σ hσ).1; rw [WellDenoted_app] at h1; exact h1.1,
      by have h2 := (hg σ hσ).2; rw [AnnotValid_app] at h2; exact h2.1⟩
  have hoka : Graded V Δa aa := fun σ hσ =>
    ⟨by have h1 := (hg σ hσ).1; rw [WellDenoted_app] at h1; exact h1.2.1,
      by have h2 := (hg σ hσ).2; rw [AnnotValid_app] at h2; exact h2.2⟩
  obtain ⟨-, -, wa, hwa, hgw, heqw⟩ :=
    hw ⟨hws.2, hb.2, hLa⟩ hC.app_arg haa hoka
  have hsw : denoteMeta m.acval env φ d (.app (.const ConLeche.natSuccName []) w)
      = some (.app fa wa) := by rw [denoteMeta_app, hfa, hwa]; rfl
  have hgsw : Graded V Δa (.app fa wa) := fun σ hσ =>
    appCongrV rfl (heqw σ hσ) (hokf σ hσ) (hgw σ hσ) (hg σ hσ)
  obtain ⟨ra, hra, hgra, heqra⟩ := hin.nat_succ hsup hn hsw hgsw
  obtain ⟨hfr, hsubr⟩ := frame_atom (d := d) (e := .lit (.natVal (n + 1)))
    (by simp [Expr.fvarLeaves]) (by simp [Expr.WScoped])
    (by simp [Expr.looseBVarsBounded])
  refine ⟨hfr, hsubr _, ra, hra, hgra, fun σ hσ => ?_⟩
  rw [interp_app, heqw σ hσ, ← interp_app]
  exact heqra σ hσ

/-- The binary row at the reduced arguments (`NatOpRow`). -/
theorem Red.natOp_sound (hin : RulesInputs V m φ) {d : Nat} {c : Name}
    {a wa b wb r : Expr} {n₁ n₂ : Nat}
    (hc : c ∈ natBinOpNames) (hst : ConLeche.natOpStored env c = true)
    (hwa : RedSem m φ d a wa) (hn₁ : ConLeche.rawNatLit? wa = some n₁)
    (hwb : RedSem m φ d b wb) (hn₂ : ConLeche.rawNatLit? wb = some n₂)
    (hr : ConLeche.natOpResult c n₁ n₂ = some r) :
    RedSem m φ d (.app (.app (.const c []) a) b) r := by
  intro hf Δa ea hC hea hg
  obtain ⟨hws, hb, hLb⟩ := hf
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbb : Expr.LeavesBounded b := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  obtain ⟨ga, ba, hga, hba, rfl⟩ := denoteMeta_app_inv hea
  obtain ⟨ca, aa, hca, haa, rfl⟩ := denoteMeta_app_inv hga
  obtain ⟨hgga, hgba⟩ := graded_app hg
  obtain ⟨hgca, hgaa⟩ := graded_app hgga
  obtain ⟨-, -, waA, hwaA, hgwaA, heqa⟩ :=
    hwa ⟨hws.1.2, hb.1.2, hLa⟩ hC.app_fn.app_arg haa hgaa
  obtain ⟨-, -, wbA, hwbA, hgwbA, heqb⟩ :=
    hwb ⟨hws.2, hb.2, hLbb⟩ hC.app_arg hba hgba
  have hsw : denoteMeta m.acval env φ d (.app (.app (.const c []) wa) wb)
      = some (.app (.app ca waA) wbA) := by
    rw [denoteMeta_app, denoteMeta_app, hca, hwaA, hwbA]; rfl
  have hgsw : Graded V Δa (.app (.app ca waA) wbA) := fun σ hσ =>
    appCongrV (by rw [interp_app, interp_app, heqa σ hσ]) (heqb σ hσ)
      (appCongrV rfl (heqa σ hσ) (hgca σ hσ) (hgwaA σ hσ) (hgga σ hσ))
      (hgwbA σ hσ) (hg σ hσ)
  obtain ⟨ra, hra, hgra, heqra⟩ := hin.nat_op hc hst hn₁ hn₂ hr hsw hgsw
  obtain ⟨hfr, hsubr⟩ : Frame d r ∧ ∀ (x : Expr), LeavesSub r x := by
    rcases ConLeche.natOpResult_shape hr with ⟨k, rfl⟩ | ⟨bn, rfl⟩
    · exact frame_atom (by simp [Expr.fvarLeaves]) (by simp [Expr.WScoped])
        (by simp [Expr.looseBVarsBounded])
    · exact frame_atom (by simp [Expr.fvarLeaves]) (by simp [Expr.WScoped])
        (by simp [Expr.looseBVarsBounded])
  refine ⟨hfr, hsubr _, ra, hra, hgra, fun σ hσ => ?_⟩
  rw [interp_app, interp_app, heqa σ hσ, heqb σ hσ, ← interp_app, ← interp_app]
  exact heqra σ hσ

/-- The tower law's iota clause at a certified spine (`projStep_of_claims`'s
firing branch, `Steps/ProjRows.lean:278`; `teleFit_of_teleFitPA`). -/
theorem Red.proj_sound (hin : RulesInputs V m φ) {d : Nat} {sn : Name} {i : Nat}
    {e : Expr} {entry : ProjEntry} {us : List Level} {cvC : ConstantVal}
    {nP nF : Nat}
    (hent : env.findProj? sn i = some entry)
    (hhead : e.getAppFn = .const entry.ctor us)
    (hi : i < entry.numFields)
    (hlen : e.getAppArgs.length = entry.numParams + entry.numFields)
    (hus : us.length = entry.levelParams.length)
    (hfire : entry.fireOk us = true)
    (hctor : env.find? entry.ctor = some (.ctorInfo cvC nP nF))
    (hcerts : CertsSem m φ d true
      (cvC.type.instantiateLevelParams cvC.levelParams us) e.getAppArgs) :
    RedSem m φ d (.proj sn i e)
      (e.getAppArgs.getD (entry.numParams + i) (.bvar 0)) := by
  intro hf Δa ea hC hea hg
  obtain ⟨hws, hb, hLb⟩ := hf
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hsube : ∀ l ∈ e.fvarLeaves, l ∈ (Expr.proj sn i e).fvarLeaves :=
    fun l hl => by simpa [Expr.fvarLeaves] using hl
  have hLe : Expr.LeavesBounded e := fun l hl => hLb l (hsube l hl)
  have hCe : CtxOk m φ d Δa e := hC.of_subset hsube
  obtain ⟨vp, hvp, rfl⟩ := denoteMeta_proj_inv_tower hent hea
  -- the tower entry's laws
  obtain ⟨-, -, -, -, hO5, cvC₀, hfC, hlpsC, hlaw, -⟩ := hin.tower_ok sn i entry hent
  obtain rfl : cvC₀ = cvC := by
    obtain ⟨rfl, -, -⟩ :=
      ConstantInfo.ctorInfo.inj (Option.some.inj (hfC.symm.trans hctor))
    rfl
  obtain ⟨-, ⟨TCa, hTCa, hB⟩⟩ := hlaw us hus
  -- the constructor spine, read at the constructor's leaf
  have he₃ : e = Expr.mkAppN (.const entry.ctor us) e.getAppArgs := by
    rw [← hhead]; exact (ConLeche.Expr.mkAppN_getApp e).symm
  have hvp' := hvp
  rw [he₃] at hvp'
  obtain ⟨vf, vs, hvf, hspa, hveq⟩ := denoteMeta_mkAppN_inv hvp'
  have hlenC : us.length = (ConstantInfo.ctorInfo cvC₀ entry.numParams
      entry.numFields).toConstantVal.levelParams.length := by
    show us.length = cvC₀.levelParams.length
    rw [hlpsC]; exact hus
  rw [denoteMeta_const hfC hlenC] at hvf
  obtain rfl : vf = m.acval entry.ctor (Level.substFn φ entry.levelParams us) := by
    rw [← hlpsC]; exact (Option.some.inj hvf).symm
  -- the selected argument's frame, reading and grading
  have hidx : entry.numParams + i < e.getAppArgs.length := by rw [hlen]; omega
  have hmemArg : e.getAppArgs.getD (entry.numParams + i) (.bvar 0)
      ∈ e.getAppArgs := ConLeche.getD_mem hidx
  obtain ⟨hfF, hCF⟩ := frame_spine ⟨hws, hb, hLe⟩ hCe _ hmemArg
  have hlenVs : vs.length = entry.numParams + entry.numFields := by
    rw [← hspa.length]; exact hlen
  have hfvd : denoteMeta m.acval env φ d
      (e.getAppArgs.getD (entry.numParams + i) (.bvar 0))
      = some (vs.getD (entry.numParams + i) default) := hspa.getD_read hidx
  have hgvp : Graded V Δa (AnnotTerm.mkAppN
      (m.acval entry.ctor (Level.substFn φ entry.levelParams us)) vs) := by
    rw [← hveq]
    exact fun σ hσ => ProjAV.hoistV (hg σ hσ)
  obtain ⟨-, hoA⟩ := hoist_spine vs hgvp
  have hokArg : Graded V Δa (vs.getD (entry.numParams + i) default) :=
    hoA _ (ConLeche.getD_mem (by rw [hlenVs]; omega))
  -- the constructor type's frame, reading and grading
  have hwfC := m.wf _ (ConLeche.Semantics.Env.find?_mem hfC)
  have hnfC : (cvC₀.type.instantiateLevelParams cvC₀.levelParams us).hasFvar
      = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hwfC.1
  have hbdC : (cvC₀.type.instantiateLevelParams cvC₀.levelParams
      us).looseBVarsBounded 0 = true := by
    rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]
    exact hwfC.2.2.2.1
  have hTCd : denoteMeta m.acval env φ d
      (cvC₀.type.instantiateLevelParams cvC₀.levelParams us) = some TCa :=
    denoteMeta_depth_of_closed m.acval_closed hnfC
      (fun k => denoteMeta_closed m.acval_erase m.cval_closed hnfC hbdC hTCa 1 k)
      hTCa d
  have hTC : CtxOk m φ d Δa
      (cvC₀.type.instantiateLevelParams cvC₀.levelParams us) :=
    ⟨hC.1, fun l hl => by
      rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfC] at hl
      exact nomatch hl⟩
  obtain ⟨TCa', hTCa', hokTCa, hmemC0⟩ := hin.const_ty 0 entry.ctor _ us hfC rfl
    (by show us.length = cvC₀.levelParams.length; rw [hlpsC]; exact hus)
  obtain rfl : TCa = TCa' := Option.some.inj (hTCa.symm.trans hTCa')
  have hmemC : ∀ σ : Nat → V, Sat V Δa σ →
      interp V σ (m.acval entry.ctor (Level.substFn φ entry.levelParams us))
        ∈ˢ interp V σ TCa := by
    intro σ _
    rw [← hlpsC]
    exact hmemC0 σ
  -- the ∀-chain, off the head data's arity pin
  obtain ⟨cvC'', hfC'', -, hstrip⟩ := (m.proj_ok.towerHead hent).2.2.2.2.2
  obtain ⟨rfl, -, -⟩ :=
    ConstantInfo.ctorInfo.inj (Option.some.inj (hfC.symm.trans hfC''))
  have hpc : PiChain e.getAppArgs.length TCa := by
    rw [hlen]
    exact piChain_of_stripPis (entry.numParams + entry.numFields)
      (ConLeche.Expr.stripPis_instantiateLevelParams_isSome cvC₀.levelParams us _
        hstrip) hTCd
  -- the licensed walk
  obtain ⟨resta, hfitA, -⟩ :=
    hcerts ⟨ConLeche.Expr.WScoped.of_not_hasFvar hnfC, hbdC,
        ConLeche.Expr.LeavesBounded.of_not_hasFvar hnfC⟩
      hTC hTCd (fun σ _ => hokTCa σ)
      (frame_spine ⟨hws, hb, hLe⟩ hCe) hspa hoA
      (fun _ => ⟨hgvp, hmemC⟩)
  refine ⟨hfF, fun l hl => hsube l (ConLeche.fvarLeaves_getAppArgs hmemArg l hl),
    vs.getD (entry.numParams + i) default, hfvd, hokArg, fun σ hσ => ?_⟩
  have hfit : TeleFit V σ TCa (vs.map (interp V σ)) (interp V σ resta) :=
    teleFit_of_teleFitPA (by rw [← hspa.length]; exact hpc) (hfitA σ hσ)
  rw [hveq, hB (towerGuardAt_of_fireOk hO5 hfire) σ vs _ hlenVs (hgvp σ hσ) hfit]

end ConLeche.Model.Rules
