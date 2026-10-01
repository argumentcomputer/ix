module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Semantics.LitParams
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.IOLicense
import ConLeche.Model.CtxOkKit
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Annot.ValidSpine
import ConLeche.Model.WellDenotedTransport
import ConLeche.Semantics.Frame
import ConLeche.Semantics.LitStep
import ConLeche.Semantics.Skeleton

public section

/-!
# The soundness of the inference rules (task #305, lane S-infer)

One lemma per constructor of `Infer`, at the constructor's grade
(`InferSem m φ g …` dispatches to the establishment motive at `.full`
and the consumption motive at `.io`).  The io lemmas mine
`Model/Steps/InferIO.lean` (the application clause's `appSkip` is
`infer_app_claimIO`'s gated arm: `io_domain_transfer` against the
subject's own hereditary app slot); the full ones `Model/Steps/Infer.lean`.

The λ rule's chain case needs the SHAPE of the body's inferred type
(a ∀ at the inner λ's own annotation, `infer_lam_meta_copy`'s twin
`Infer.lam_shape`), which the master induction reads off the premise
derivation and hands in as `hshape`.
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

/-! ## The grade kit

The establishment motive is the stronger one: it concludes the
subject's grading where the consumption motive takes it.  A leaf rule
(`sort`, `fvar`, `const`, `natLit`, `strLit`) establishes outright, so
its lemma is proved once at `InferSemFull` and dispatched. -/

/-- Establishment implies consumption: drop the concluded grading. -/
theorem InferSemFull.toIO {d : Nat} {e t : Expr}
    (h : InferSemFull m φ d e t) : InferSemIO m φ d e t := by
  intro hf Δa ea hC hea _
  obtain ⟨hft, hsub, ta, hta, -, hgt, hmem⟩ := h hf hC hea
  exact ⟨hft, hsub, ta, hta, hgt, hmem⟩

/-- A rule that establishes is sound at either grade. -/
theorem InferSemFull.toSem {g : Grade} {d : Nat} {e t : Expr}
    (h : InferSemFull m φ d e t) : InferSem m φ g d e t := by
  cases g with
  | full => exact h
  | io => exact h.toIO

/-- **The uniform view of the inference motive.**  Both grades
conclude the type's frame, its reading, its grading and the
membership; they differ only in where the SUBJECT's grading sits — a
premise at `.io`, a conclusion at `.full`.  Reading a premise
derivation's motive through this lemma, and building the conclusion's
through `InferSem.of_uniform`, is what lets one argument serve both
grades. -/
theorem InferSem.apply {g : Grade} {d : Nat} {e t : Expr}
    (h : InferSem m φ g d e t) (hfe : Frame d e) {Δa : List AnnotTerm}
    {ea : AnnotTerm} (hC : CtxOk m φ d Δa e)
    (hea : denoteMeta m.acval env φ d e = some ea)
    (hgr : g = .io → Graded V Δa ea) :
    Frame d t ∧ LeavesSub t e ∧ Graded V Δa ea ∧
      ∃ ta, denoteMeta m.acval env φ d t = some ta ∧ Graded V Δa ta ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea ∈ˢ interp V ρ ta := by
  cases g with
  | full =>
    obtain ⟨hft, hsub, ta, hta, hge, hgt, hmem⟩ := h hfe hC hea
    exact ⟨hft, hsub, hge, ta, hta, hgt, hmem⟩
  | io =>
    obtain ⟨hft, hsub, ta, hta, hgt, hmem⟩ := h hfe hC hea (hgr rfl)
    exact ⟨hft, hsub, hgr rfl, ta, hta, hgt, hmem⟩

/-- `InferSem.apply`'s converse: the uniform statement builds the
motive at either grade. -/
theorem InferSem.of_uniform {g : Grade} {d : Nat} {e t : Expr}
    (h : ∀ {Δa : List AnnotTerm} {ea : AnnotTerm}, Frame d e →
      CtxOk m φ d Δa e → denoteMeta m.acval env φ d e = some ea →
      (g = .io → Graded V Δa ea) →
      Frame d t ∧ LeavesSub t e ∧ Graded V Δa ea ∧
        ∃ ta, denoteMeta m.acval env φ d t = some ta ∧ Graded V Δa ta ∧
          ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea ∈ˢ interp V ρ ta) :
    InferSem m φ g d e t := by
  cases g with
  | full =>
    intro hfe Δa ea hC hea
    obtain ⟨hft, hsub, hge, ta, hta, hgt, hmem⟩ :=
      h hfe hC hea (fun hg => by simp at hg)
    exact ⟨hft, hsub, ta, hta, hge, hgt, hmem⟩
  | io =>
    intro hfe Δa ea hC hea hge
    obtain ⟨hft, hsub, -, ta, hta, hgt, hmem⟩ := h hfe hC hea (fun _ => hge)
    exact ⟨hft, hsub, ta, hta, hgt, hmem⟩

/-- **The sort fact at a grade** (`sortSemAt_of_claims`,
`Steps/Infer.lean:798`, at the motives): a subject whose inferred type
reduces to `.sort u` reads into the universe — and is graded, which at
the io grade is the premise and at the full grade the first motive's
conclusion.  The totality factor the run version routes
(`InferReads`) is the existence form of `InferSem`. -/
theorem sortSem_of {g : Grade} {d : Nat} {e s : Expr} {u : Level}
    (hs : InferSem m φ g d e s) (hu : RedSem m φ d s (.sort u))
    (hfe : Frame d e) {Δa : List AnnotTerm} {ea : AnnotTerm}
    (hC : CtxOk m φ d Δa e)
    (hea : denoteMeta m.acval env φ d e = some ea)
    (hgr : g = .io → Graded V Δa ea) :
    ∀ ρ : Nat → V, Sat V Δa ρ →
      WellDenotedV V ρ ea ∧ interp V ρ ea ∈ˢ (univ (u.eval φ) : V) := by
  obtain ⟨hfs, hsub, hge, sa, hsa, hgs, hmem⟩ := hs.apply hfe hC hea hgr
  obtain ⟨-, -, ua, hua, -, heq⟩ := hu hfs (hC.of_subset hsub) hsa hgs
  rw [denoteMeta] at hua
  obtain rfl : ua = .sort (u.eval φ) := (Option.some.inj hua).symm
  intro ρ hρ
  refine ⟨hge ρ hρ, ?_⟩
  have hm := hmem ρ hρ
  rw [heq ρ hρ, interp_sort] at hm
  exact hm

/-- `infer_sort_claim` / `infer_sort_claimIO`. -/
theorem Infer.sort_sound {g : Grade} {d : Nat} {u : Level} :
    InferSem m φ g d (.sort u) (.sort (.succ u)) := by
  refine InferSemFull.toSem ?_
  intro hf Δa ea hC hea
  rw [denoteMeta] at hea
  obtain rfl : ea = .sort (u.eval φ) := (Option.some.inj hea).symm
  have hty : denoteMeta m.acval env φ d (.sort (.succ u))
      = some (.sort (Level.eval φ (.succ u))) := by rw [denoteMeta]
  refine ⟨⟨by simp [Expr.WScoped], by simp [Expr.looseBVarsBounded],
      fun l hl => by simp [Expr.fvarLeaves] at hl⟩,
    fun l hl => by simp [Expr.fvarLeaves] at hl,
    _, hty, fun _ _ => ⟨by simp, by simp⟩, fun _ _ => ⟨by simp, by simp⟩, ?_⟩
  intro ρ _
  exact (sound_sort V ρ (u.eval φ)).2

/-- `infer_fvar_claim(IO)`: `CtxOk`'s leaf package. -/
theorem Infer.fvar_sound {g : Grade} {d idx : Nat} {ty : Expr} (h : idx < d) :
    InferSem m φ g d (.fvar idx ty) ty := by
  refine InferSemFull.toSem ?_
  intro hf Δa ea hC hea
  obtain ⟨hws, hb, hLb⟩ := hf
  obtain ⟨-, -, tya, Aa, hden, hi, hlink, hokP⟩ := CtxOk.fvar_leaf hC
  rw [denoteMeta] at hea
  obtain rfl : ea = .bvar (d - 1 - idx) := (Option.some.inj hea).symm
  simp only [Expr.WScoped] at hws
  have hmem : ∀ l ∈ ty.fvarLeaves, l ∈ (Expr.fvar idx ty).fvarLeaves := by
    intro l hl
    rw [Expr.fvarLeaves]
    exact List.mem_cons_of_mem _ hl
  refine ⟨⟨hws.2.mono (by omega), hLb (idx, ty) (by simp [Expr.fvarLeaves]),
      fun l hl => hLb l (hmem l hl)⟩,
    hmem, tya, hden, fun _ _ => ⟨by simp, by simp⟩, hokP, ?_⟩
  intro ρ hρ
  rw [interp_bvar, hlink ρ hρ]
  exact hρ (d - 1 - idx) Aa hi

/-- `infer_const_claim(IO)`: `ConstType` + `AcvalValid`. -/
theorem Infer.const_sound (hin : RulesInputs V m φ) {g : Grade} {d : Nat}
    {n : Name} {us : List Level} {ci : ConLeche.ConstantInfo}
    (hf : env.find? n = some ci) (htower : ci.isTowerEntry = false)
    (hus : us.length = ci.toConstantVal.levelParams.length) :
    InferSem m φ g d (.const n us)
      (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) := by
  refine InferSemFull.toSem ?_
  intro _ Δa ea hC hea
  rw [denoteMeta, hf] at hea
  dsimp only at hea
  rw [if_pos hus] at hea
  obtain rfl : ea = m.acval n
      (Level.substFn φ ci.toConstantVal.levelParams us) :=
    (Option.some.inj hea).symm
  obtain ⟨ta, hta, hok, hmem⟩ := hin.const_ty d n ci us hf htower hus
  obtain ⟨htc, -, -, htb, -⟩ := m.wf _ (Env.find?_mem hf)
  have hnf : (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact htc
  exact ⟨⟨Expr.WScoped.of_not_hasFvar hnf,
      by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact htb,
      Expr.LeavesBounded.of_not_hasFvar hnf⟩,
    (fun l hl => by
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf] at hl; cases hl),
    ta, hta, fun ρ _ => ⟨m.acval_wellDenoted n _ ρ, hin.leaf_valid n _ ρ⟩,
    fun ρ _ => hok ρ, fun ρ _ => hmem ρ⟩

/-- `infer_natLit_claim(IO)`: `NatHeads` + `AcvalValid`. -/
theorem Infer.natLit_sound (hin : RulesInputs V m φ) {g : Grade} {d n : Nat}
    (h : ConLeche.natLitSupported env = true) :
    InferSem m φ g d (.lit (.natVal n)) (.const natName []) := by
  refine InferSemFull.toSem ?_
  intro _ Δa ea _ hea
  rw [denoteMeta, if_pos h] at hea
  obtain rfl : ea = natLitAV
      (m.acval natZeroName (Level.substFn φ [] []))
      (m.acval natSuccName (Level.substFn φ [] [])) n :=
    (Option.some.inj hea).symm
  cases hf : env.find? natName with
  | none =>
    simp only [ConLeche.natLitSupported, Bool.and_eq_true] at h
    obtain ⟨⟨h1, -⟩, -⟩ := h
    rw [hf] at h1
    exact nomatch h1
  | some ci =>
    have hlp : ci.toConstantVal.levelParams = [] :=
      natName_levelParams_nil h hf
    have hta : denoteMeta m.acval env φ d (.const natName [])
        = some (m.acval natName (Level.substFn φ [] [])) := by
      rw [denoteMeta, hf]
      dsimp only
      rw [if_pos (by simp [hlp]), hlp]
    have hrow : ∀ ρ : Nat → V,
        WellDenoted V ρ (natLitAV
            (m.acval natZeroName (Level.substFn φ [] []))
            (m.acval natSuccName (Level.substFn φ [] [])) n) ∧
          interp V ρ (natLitAV
              (m.acval natZeroName (Level.substFn φ [] []))
              (m.acval natSuccName (Level.substFn φ [] [])) n)
            ∈ˢ interp V ρ (m.acval natName (Level.substFn φ [] [])) :=
      fun ρ => natLit_factsAV (m.acval_wellDenoted _ _ ρ)
        (m.acval_wellDenoted _ _ ρ) (hin.nat_heads h ρ).1
        (hin.nat_heads h ρ).2 n
    exact ⟨⟨by simp [Expr.WScoped], by simp [Expr.looseBVarsBounded],
        fun l hl => by simp [Expr.fvarLeaves] at hl⟩,
      (fun l hl => by simp [Expr.fvarLeaves] at hl),
      _, hta,
      fun ρ _ => ⟨(hrow ρ).1, AnnotValid_natLitAV (hin.leaf_valid _ _ ρ)
        (hin.leaf_valid _ _ ρ) n⟩,
      fun ρ _ => ⟨m.acval_wellDenoted _ _ ρ, hin.leaf_valid _ _ ρ⟩,
      fun ρ _ => (hrow ρ).2⟩

/-- `inferStrLitStep_of_claims` (`Steps/StrLit.lean:451`). -/
theorem Infer.strLit_sound (hin : RulesInputs V m φ) {g : Grade} {d : Nat}
    {s : String} (h : ConLeche.strLitSupported env = true) :
    InferSem m φ g d (.lit (.strVal s)) (.const stringName []) := by
  refine InferSemFull.toSem ?_
  intro _ Δa ea _ hea
  obtain ⟨-, ciS, -, -, -, -, -, -, -, -, -, hfS, -,
    -, -, -, -, -, hlpS, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    ConLeche.strLitSupported_inv h
  have hta : denoteMeta m.acval env φ d (.const stringName [])
      = some (m.acval ConLeche.stringName (Level.substFn φ [] [])) := by
    have hc := denoteMeta_const (acval := m.acval) (φ := φ) (d := d)
      (us := []) hfS (by simp [hlpS])
    rwa [hlpS] at hc
  exact ⟨⟨by simp [Expr.WScoped], by simp [Expr.looseBVarsBounded],
      fun l hl => by simp [Expr.fvarLeaves] at hl⟩,
    (fun l hl => by simp [Expr.fvarLeaves] at hl),
    _, hta,
    fun ρ _ => (strLitFacts hin.const_ty hin.leaf_valid hin.nat_heads h hea ρ).1,
    fun ρ _ => ⟨m.acval_wellDenoted _ _ ρ, hin.leaf_valid _ _ ρ⟩,
    fun ρ _ => (strLitFacts hin.const_ty hin.leaf_valid hin.nat_heads h hea ρ).2⟩

/-- `infer_forallE_claim(IO)` (`Steps/Infer.lean:254`, `InferIO.lean:339`):
the two sort facts (`sortSemAt_of_claims`'s content) and the bit law. -/
theorem Infer.forallE_sound {g : Grade} {d : Nat}
    {ty body s bs : Expr} {u v : Level} {mb : BinderMeta}
    (hs : InferSem m φ g d ty s) (hu : RedSem m φ d s (.sort u))
    (hbs : InferSem m φ g (d + 1) (body.instantiate1 (.fvar d ty)) bs)
    (hv : RedSem m φ (d + 1) bs (.sort v))
    (hz : Level.zeronessOf v = mb.pw) :
    InferSem m φ g d (.forallE ty body mb) (.sort (.imax u v)) := by
  have main : ∀ {Δa : List AnnotTerm} {ea : AnnotTerm},
      Frame d (.forallE ty body mb) →
      CtxOk m φ d Δa (.forallE ty body mb) →
      denoteMeta m.acval env φ d (.forallE ty body mb) = some ea →
      (g = .io → Graded V Δa ea) →
      Frame d (.sort (.imax u v)) ∧
        LeavesSub (.sort (.imax u v)) (.forallE ty body mb) ∧
        ∃ ta, denoteMeta m.acval env φ d (.sort (.imax u v)) = some ta ∧
          Graded V Δa ea ∧ Graded V Δa ta ∧
          ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea ∈ˢ interp V ρ ta := by
    intro Δa ea hfr hC hea hgr
    obtain ⟨hws, hb, hLb⟩ := hfr
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hLty : Expr.LeavesBounded ty := fun l hl =>
      hLb l (by simp [Expr.fvarLeaves, hl])
    have hLbody : Expr.LeavesBounded body := fun l hl =>
      hLb l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hwopen, hbopen, hLopen⟩ :=
      frame_open2 hws.1 hb.1 hws.2 hb.2 hLty hLbody
    obtain ⟨tyA, baA, htyA, hbaA, rfl⟩ := denoteMeta_forallE_inv hea
    -- the io grade's premise, split hereditarily
    have hoist : g = .io →
        Graded V Δa tyA ∧ Graded V (tyA :: Δa) baA := fun hg =>
      WellDenotedV.hoist_pi (V := V) (hgr hg)
    have hdomU := sortSem_of hs hu ⟨hws.1, hb.1, hLty⟩ hC.forallE_ty htyA
      (fun hg => (hoist hg).1)
    have hCop : CtxOk m φ (d + 1) (tyA :: Δa)
        (body.instantiate1 (.fvar d ty)) :=
      CtxOk.openS hC.forallE_ty hC.forallE_body htyA
        (fun ρ hρ => (hdomU ρ hρ).1)
    have hcodU := sortSem_of hbs hv ⟨hwopen, hbopen, hLopen⟩ hCop hbaA
      (fun hg => (hoist hg).2)
    have hgea : Graded V Δa (.pi 0 (pwBit φ mb.pw) tyA baA) := by
      intro ρ hρ
      have hdom := hdomU ρ hρ
      have hcod : ∀ x, x ∈ˢ interp V ρ tyA →
          WellDenotedV V (cons x ρ) baA ∧
            interp V (cons x ρ) baA ∈ˢ (univ (v.eval φ) : V) :=
        fun x hx => hcodU (cons x ρ) (Sat_cons V hρ hx)
      refine ⟨?_, ?_⟩
      · rw [WellDenoted_pi]
        exact ⟨hdom.1.1, fun x hx => (hcod x hx).1.1⟩
      · rw [AnnotValid_pi]
        refine ⟨hdom.1.2, fun x hx => (hcod x hx).1.2, ?_⟩
        intro hbit x hx
        exact pwBit_zero_mem_univZero hz hbit (hcod x hx).2
    refine ⟨⟨by simp [Expr.WScoped], by simp [Expr.looseBVarsBounded],
        fun l hl => by simp [Expr.fvarLeaves] at hl⟩,
      (fun l hl => by simp [Expr.fvarLeaves] at hl),
      _, by rw [denoteMeta], hgea, fun _ _ => ⟨by simp, by simp⟩, ?_⟩
    intro ρ hρ
    have hdom := hdomU ρ hρ
    have hcod : ∀ x, x ∈ˢ interp V ρ tyA →
        WellDenoted V (cons x ρ) baA ∧
          interp V (cons x ρ) baA ∈ˢ (univ (v.eval φ) : V) :=
      fun x hx =>
        ⟨(hcodU (cons x ρ) (Sat_cons V hρ hx)).1.1,
          (hcodU (cons x ρ) (Sat_cons V hρ hx)).2⟩
    have hrow := sound_pi V (u := u.eval φ) (v := v.eval φ)
      hdom.1.1 (fun x hx => (hcod x hx).1) hdom.2
      (fun x hx => (hcod x hx).2)
    have hzag : pwBit φ mb.pw = 0 ↔ v.eval φ = 0 := by
      rw [← hz]; exact pwBit_zeronessOf φ v
    have hbridge :
        interp V ρ (.pi 0 (pwBit φ mb.pw) tyA baA)
          = interp V ρ (.pi (u.eval φ) (v.eval φ) tyA baA) := by
      rw [interp_pi, interp_pi]
      exact piR_zero_agree hzag fun x _ => rfl
    rw [hbridge]
    exact hrow.2
  cases g with
  | full =>
    intro hfr Δa ea hC hea
    exact main hfr hC hea (fun hg => by simp at hg)
  | io =>
    intro hfr Δa ea hC hea hge
    obtain ⟨hft, hsub, ta, hta, -, hgt, hmem⟩ := main hfr hC hea (fun _ => hge)
    exact ⟨hft, hsub, ta, hta, hgt, hmem⟩

/-- `infer_lam_claim(IO)` (`Steps/Infer.lean:358`, `InferIO.lean:456`):
the fibre regime fact from the leaf sort run or, at a chain node, from
the copied annotation (`piR_zero_mem_univZero`). -/
theorem Infer.lam_sound {g : Grade} {d : Nat}
    {ty body s bt btt : Expr} {u v : Level} {mb : BinderMeta}
    (hs : g = .full → InferSemFull m φ d ty s)
    (hu : g = .full → RedSem m φ d s (.sort u))
    (hbt : InferSem m φ g (d + 1) (body.instantiate1 (.fvar d ty)) bt)
    (hshape : ∀ tyI bI mbI, body = .lam tyI bI mbI →
      ∃ btI, bt = .forallE (tyI.instantiate1 (.fvar d ty)) btI mbI)
    (hchain : ∀ pwI, body.lamPw = some pwI → mb.pw = pwI)
    (hbtt : body.lamPw = none → InferSemIO m φ (d + 1) bt btt)
    (hv : body.lamPw = none → RedSem m φ (d + 1) btt (.sort v))
    (hz : body.lamPw = none → Level.zeronessOf v = mb.pw) :
    InferSem m φ g d (.lam ty body mb) (.forallE ty (bt.abstract1 d) mb) := by
  refine InferSem.of_uniform ?_
  intro Δa ea hfr hC hea hgr
  obtain ⟨hws, hb, hLb⟩ := hfr
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded body := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  -- the subject's reading
  rw [denoteMeta] at hea
  rcases htyA : denoteMeta m.acval env φ d ty with _ | tyA
  · rw [htyA] at hea; exact nomatch hea
  rw [htyA] at hea
  rcases hba : denoteMeta m.acval env φ (d + 1)
      (body.instantiate1 (.fvar d ty)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  rw [hba] at hea
  obtain rfl : ea = .lam (pwBit φ mb.pw) tyA ba :=
    (Option.some.inj hea).symm
  obtain ⟨hwopen, hbopen, hLopen⟩ :=
    frame_open2 hws.1 hb.1 hws.2 hb.2 hLty hLbody
  -- the domain's grading: established at the full grade by its own
  -- sort run, consumed at the io grade off the subject (`hoist_lam`)
  have hoist : g = .io →
      Graded V Δa tyA ∧ Graded V (tyA :: Δa) ba := fun hg =>
    WellDenotedV.hoist_lam (V := V) (hgr hg)
  have hokty : Graded V Δa tyA := by
    cases g with
    | full =>
      exact fun ρ hρ =>
        (sortSem_of (g := .full) (hs rfl) (hu rfl) ⟨hws.1, hb.1, hLty⟩
          hC.lam_ty htyA (fun hg => by simp at hg) ρ hρ).1
    | io => exact (hoist rfl).1
  have hCop : CtxOk m φ (d + 1) (tyA :: Δa)
      (body.instantiate1 (.fvar d ty)) :=
    CtxOk.openS hC.lam_ty hC.lam_body htyA hokty
  -- the opened body's inferred type
  obtain ⟨hbtf, hbtsub, hrowE, btA, hbtA, hrowT, hrowM⟩ :=
    hbt.apply ⟨hwopen, hbopen, hLopen⟩ hCop hba (fun hg => (hoist hg).2)
  obtain ⟨hwbt, hbtb, hLbt⟩ := hbtf
  -- the abstraction round trip, for the ∀-type's reading
  have hleaf : Expr.LeafCond d ty (body.instantiate1 (.fvar d ty)) := by
    intro l hl hd
    rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · exact absurd hd (by
        have := Expr.fvarLeaves_lt_of_wscoped hws.2 l h2
        omega)
    · rw [Expr.fvarLeaves] at h2
      rcases List.mem_cons.mp h2 with rfl | h3
      · exact rfl
      · exact absurd hd (by
          have := Expr.fvarLeaves_lt_of_wscoped hws.1 l h3
          omega)
  have hcons : Expr.fvarConsistent d ty bt :=
    Expr.fvarConsistent_of_leafCond bt (fun l hl => hleaf l (hbtsub l hl))
  have hround : (bt.abstract1 d).instantiate1 (.fvar d ty) = bt :=
    ConLeche.abstract1_instantiate1 bt 0 hcons hbtb
  have hta : denoteMeta m.acval env φ d (.forallE ty (bt.abstract1 d) mb)
      = some (.pi 0 (pwBit φ mb.pw) tyA btA) := by
    rw [denoteMeta, htyA, hround, hbtA]
    rfl
  have hCbt : CtxOk m φ (d + 1) (tyA :: Δa) bt := hCop.of_subset hbtsub
  -- the fibre regime fact, one `have`, both uses (the meta copy)
  have hzfib : pwBit φ mb.pw = 0 →
      ∀ (ρ' : Nat → V), Sat V (tyA :: Δa) ρ' →
        interp V ρ' btA ∈ˢ (univZero : V) := by
    intro hb0 ρ' hρ'
    cases hpw : body.lamPw with
    | some pwI =>
      -- chain: no run — impredicativity at the copied meta
      obtain ⟨tyI, bI, mbI, rfl⟩ : ∃ tyI bI mbI, body = .lam tyI bI mbI := by
        cases body <;> simp [Expr.lamPw] at hpw
        exact ⟨_, _, _, rfl⟩
      have hpwEq : mb.pw = mbI.pw := by
        have := hchain pwI hpw
        simp only [Expr.lamPw, Option.some.injEq] at hpw
        rw [this, hpw]
      obtain ⟨btI, rfl⟩ := hshape tyI bI mbI rfl
      obtain ⟨tyIA, btIA, -, -, rfl⟩ := denoteMeta_forallE_inv hbtA
      rw [interp_pi]
      have hinner : pwBit φ mbI.pw = 0 := by rw [← hpwEq]; exact hb0
      rw [hinner]
      exact piR_zero_mem_univZero
    | none =>
      -- leaf: the io sort walk on the body type + the bit law
      exact pwBit_zero_mem_univZero (hz hpw) hb0
        (sortSem_of (g := .io)
          (show InferSem m φ .io (d + 1) bt btt from hbtt hpw) (hv hpw)
          ⟨hwbt, hbtb, hLbt⟩ hCbt hbtA (fun _ => hrowT) ρ' hρ').2
  -- the conclusion's frame and leaves
  have hsubT : ∀ l ∈ (Expr.forallE ty (bt.abstract1 d) mb).fvarLeaves,
      l ∈ (Expr.lam ty body mb).fvarLeaves := by
    intro l hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with h2 | h2
    · exact Or.inl h2
    · obtain ⟨hlbt, hlne⟩ := ConLeche.Expr.fvarLeaves_abstract1_ne bt 0 hwbt l h2
      rcases Expr.fvarLeaves_instantiate1 body 0 (hbtsub l hlbt) with h3 | h3
      · exact Or.inr h3
      · rw [Expr.fvarLeaves] at h3
        rcases List.mem_cons.mp h3 with rfl | h4
        · exact absurd rfl hlne
        · exact Or.inl h4
  have hwT : Expr.WScoped d (.forallE ty (bt.abstract1 d) mb) := by
    simp only [Expr.WScoped]
    exact ⟨hws.1, ConLeche.WScoped.abstract1 0 hwbt⟩
  have hbT : (Expr.forallE ty (bt.abstract1 d) mb).looseBVarsBounded 0
      = true := by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨hb.1, ConLeche.looseBVarsBounded_abstract1 bt 0 hbtb⟩
  refine ⟨⟨hwT, hbT, fun l hl => hLb l (hsubT l hl)⟩,
    hsubT, ?_, _, hta, ?_, ?_⟩
  · -- the λ's own grading
    intro ρ hρ
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_lam]
      exact ⟨(hokty ρ hρ).1,
        fun x hx => (hrowE (cons x ρ) (Sat_cons V hρ hx)).1,
        fun x => interp V (cons x ρ) btA,
        fun x hx => hrowM (cons x ρ) (Sat_cons V hρ hx),
        fun h0 x hx => hzfib h0 (cons x ρ) (Sat_cons V hρ hx)⟩
    · rw [AnnotValid_lam]
      exact ⟨(hokty ρ hρ).2,
        fun x hx => (hrowE (cons x ρ) (Sat_cons V hρ hx)).2⟩
  · -- the copied ∀-type's grading
    intro ρ hρ
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_pi]
      exact ⟨(hokty ρ hρ).1,
        fun x hx => (hrowT (cons x ρ) (Sat_cons V hρ hx)).1⟩
    · rw [AnnotValid_pi]
      exact ⟨(hokty ρ hρ).2,
        fun x hx => (hrowT (cons x ρ) (Sat_cons V hρ hx)).2,
        fun h0 x hx => hzfib h0 (cons x ρ) (Sat_cons V hρ hx)⟩
  · -- the membership row
    intro ρ hρ
    exact (sound_lam V (hokty ρ hρ).1
      (fun x hx => (hrowE (cons x ρ) (Sat_cons V hρ hx)).1)
      (fun x hx => hrowM (cons x ρ) (Sat_cons V hρ hx))
      (fun h0 x hx => hzfib h0 (cons x ρ) (Sat_cons V hρ hx))).2

/-- `infer_app_claim` / `infer_app_claimIO`'s kept arm
(`Steps/Infer.lean:842`, `InferIO.lean:609`). -/
theorem Infer.app_sound {g : Grade} {d : Nat}
    {f a tf ty body ta : Expr} {mt : BinderMeta}
    (htf : InferSem m φ g d f tf) (hw : RedSem m φ d tf (.forallE ty body mt))
    (hta : InferSem m φ g d a ta) (hd : DefEqSem m φ d ta ty) :
    InferSem m φ g d (.app f a) (body.instantiate1 a) := by
  refine InferSem.of_uniform ?_
  intro Δa ea hfr hC hea hgr
  obtain ⟨hws, hb, hLb⟩ := hfr
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  -- the subject's reading splits
  rw [denoteMeta] at hea
  rcases hfa : denoteMeta m.acval env φ d f with _ | fa
  · rw [hfa] at hea; exact nomatch hea
  rw [hfa] at hea
  rcases haa : denoteMeta m.acval env φ d a with _ | aa
  · rw [haa] at hea; exact nomatch hea
  rw [haa] at hea
  obtain rfl : ea = .app fa aa := (Option.some.inj hea).symm
  have hoist : g = .io → Graded V Δa fa ∧ Graded V Δa aa := fun hg =>
    ⟨(WellDenotedV.hoist_app (V := V) (hgr hg)).1,
      (WellDenotedV.hoist_app (V := V) (hgr hg)).2.1⟩
  -- the head, its type, and the ∀ it reduces to
  obtain ⟨htff, htfsub, hgfa, tfa, htfa, hgtfa, hrowfM⟩ :=
    htf.apply ⟨hws.1, hb.1, hLf⟩ hC.app_fn hfa (fun hg => (hoist hg).1)
  obtain ⟨hpif, hpisub, pa, hpa, hokpa, hredf⟩ :=
    hw htff (hC.app_fn.of_subset htfsub) htfa hgtfa
  obtain ⟨hwfe, hbfe, hLfe⟩ := hpif
  simp only [Expr.WScoped] at hwfe
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbfe
  have hLty' : Expr.LeavesBounded ty := fun l hl =>
    hLfe l (by simp [Expr.fvarLeaves, hl])
  have hCpi : CtxOk m φ d Δa (.forallE ty body mt) :=
    (hC.app_fn.of_subset htfsub).of_subset hpisub
  obtain ⟨Aa, Ba, hAa, hBa, rfl⟩ := denoteMeta_forallE_inv hpa
  -- the ∀'s reading, split
  have hokAa : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ Aa := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := hokpa ρ hρ
    rw [WellDenoted_pi] at h1
    rw [AnnotValid_pi] at h2
    exact ⟨h1.1, h2.1⟩
  have hokBa : ∀ (ρ : Nat → V), Sat V Δa ρ →
      ∀ x, x ∈ˢ interp V ρ Aa → WellDenotedV V (cons x ρ) Ba := by
    intro ρ hρ x hx
    obtain ⟨h1, h2⟩ := hokpa ρ hρ
    rw [WellDenoted_pi] at h1
    rw [AnnotValid_pi] at h2
    exact ⟨h1.2 x hx, h2.2.1 x hx⟩
  have hcod0 : ∀ (ρ : Nat → V), Sat V Δa ρ → pwBit φ mt.pw = 0 →
      ∀ x, x ∈ˢ interp V ρ Aa →
        interp V (cons x ρ) Ba ∈ˢ (univZero : V) := by
    intro ρ hρ h0 x hx
    obtain ⟨-, h2⟩ := hokpa ρ hρ
    rw [AnnotValid_pi] at h2
    exact h2.2.2 h0 x hx
  -- the argument, and the domain agreement
  obtain ⟨htaf, htasub, hgaa, tyaA, htyaA, hgtyaA, hrowaM⟩ :=
    hta.apply ⟨hws.2, hb.2, hLa⟩ hC.app_arg haa (fun hg => (hoist hg).2)
  have hdom : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ tyaA = interp V ρ Aa :=
    hd htaf ⟨hwfe.1, hbfe.1, hLty'⟩ (hC.app_arg.of_subset htasub)
      hCpi.forallE_ty htyaA hAa hgtyaA hokAa
  have ha2 : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ aa ∈ˢ interp V ρ Aa := by
    intro ρ hρ
    rw [← hdom ρ hρ]
    exact hrowaM ρ hρ
  have hf2 : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ fa ∈ˢ interp V ρ (.pi 0 (pwBit φ mt.pw) Aa Ba) := by
    intro ρ hρ
    rw [← hredf ρ hρ]
    exact hrowfM ρ hρ
  -- the returned type's reading, `denoteMeta_beta` backwards
  have hcross : denoteMeta m.acval env φ d (body.instantiate1 a)
      = some (Ba.inst aa) := by
    rw [denoteMeta_beta (ty := ty) m.acval_closed
      (acval_inst_self m) hwfe.2.fvarsBelow hws.2 hb.2 haa 0, hBa]
    rfl
  refine ⟨⟨Expr.WScoped.instantiate1_gen hws.2 0 hwfe.2,
      Expr.looseBVarsBounded_instantiate1_gen hb.2 hbfe.2,
      fun l hl => ?_⟩, fun l hl => ?_, ?_, _, hcross, ?_, ?_⟩
  · rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · exact hLfe l (by simp [Expr.fvarLeaves, h2])
    · exact hLa l h2
  · rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · rw [Expr.fvarLeaves]
      exact List.mem_append_left _ (htfsub l (hpisub l
        (by simp [Expr.fvarLeaves, h2])))
    · rw [Expr.fvarLeaves]
      exact List.mem_append_right _ h2
  · intro ρ hρ
    refine ⟨(sound_app V (hgfa ρ hρ).1 (hgaa ρ hρ).1 (hf2 ρ hρ)
      (ha2 ρ hρ) (hcod0 ρ hρ)).1, ?_⟩
    rw [AnnotValid_app]
    exact ⟨(hgfa ρ hρ).2, (hgaa ρ hρ).2⟩
  · intro ρ hρ
    exact (WellDenotedV_inst0 (hgaa ρ hρ)).mpr (hokBa ρ hρ _ (ha2 ρ hρ))
  · intro ρ hρ
    exact (sound_app V (hgfa ρ hρ).1 (hgaa ρ hρ).1 (hf2 ρ hρ)
      (ha2 ρ hρ) (hcod0 ρ hρ)).2

/-- **The io licence** (`infer_app_claimIO`'s gated arm): the skipped
membership from the subject's own hereditary app slot,
`io_domain_transfer` + `piR_dom_unique` at a bit pinned positive by
`pwBit_ne_zero_of_isNever`. -/
theorem Infer.appSkip_sound {d : Nat}
    {f a tf ty body : Expr} {mt : BinderMeta}
    (htf : InferSemIO m φ d f tf) (hw : RedSem m φ d tf (.forallE ty body mt))
    (hnev : mt.pw.isNever = true) :
    InferSemIO m φ d (.app f a) (body.instantiate1 a) := by
  intro hfr Δa ea hC hea hge
  obtain ⟨hws, hb, hLb⟩ := hfr
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  -- the subject's reading splits
  rw [denoteMeta] at hea
  rcases hfa : denoteMeta m.acval env φ d f with _ | fa
  · rw [hfa] at hea; exact nomatch hea
  rw [hfa] at hea
  rcases haa : denoteMeta m.acval env φ d a with _ | aa
  · rw [haa] at hea; exact nomatch hea
  rw [haa] at hea
  obtain rfl : ea = .app fa aa := (Option.some.inj hea).symm
  -- **the premise, spent**: the parts' grading and the hereditary slot
  obtain ⟨hokf, hoka, hslot⟩ := WellDenotedV.hoist_app (V := V) hge
  obtain ⟨htff, htfsub, tfa, htfa, hgtfa, hrowfM⟩ :=
    htf ⟨hws.1, hb.1, hLf⟩ hC.app_fn hfa hokf
  obtain ⟨hpif, hpisub, pa, hpa, hokpa, hredf⟩ :=
    hw htff (hC.app_fn.of_subset htfsub) htfa hgtfa
  obtain ⟨hwfe, hbfe, hLfe⟩ := hpif
  simp only [Expr.WScoped] at hwfe
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbfe
  obtain ⟨Aa, Ba, hAa, hBa, rfl⟩ := denoteMeta_forallE_inv hpa
  have hokBa : ∀ (ρ : Nat → V), Sat V Δa ρ →
      ∀ x, x ∈ˢ interp V ρ Aa → WellDenotedV V (cons x ρ) Ba := by
    intro ρ hρ x hx
    obtain ⟨h1, h2⟩ := hokpa ρ hρ
    rw [WellDenoted_pi] at h1
    rw [AnnotValid_pi] at h2
    exact ⟨h1.2 x hx, h2.2.1 x hx⟩
  have hcod0 : ∀ (ρ : Nat → V), Sat V Δa ρ → pwBit φ mt.pw = 0 →
      ∀ x, x ∈ˢ interp V ρ Aa →
        interp V (cons x ρ) Ba ∈ˢ (univZero : V) := by
    intro ρ hρ h0 x hx
    obtain ⟨-, h2⟩ := hokpa ρ hρ
    rw [AnnotValid_pi] at h2
    exact h2.2.2 h0 x hx
  have hf2 : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ fa ∈ˢ interp V ρ (.pi 0 (pwBit φ mt.pw) Aa Ba) := by
    intro ρ hρ
    rw [← hredf ρ hρ]
    exact hrowfM ρ hρ
  -- **THE LICENCE**: the skipped membership, from the subject's own
  -- hereditary app slot at a bit pinned positive by the datum
  have ha2 : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ aa ∈ˢ interp V ρ Aa := by
    have hw0 : pwBit φ mt.pw ≠ 0 := pwBit_ne_zero_of_isNever hnev φ
    intro ρ hρ
    obtain ⟨v, A, B, hfslot, haslot, -⟩ := hslot ρ hρ
    have hf' := hf2 ρ hρ
    rw [interp_pi] at hf'
    exact io_domain_transfer hw0 hfslot haslot hf'
  have hcross : denoteMeta m.acval env φ d (body.instantiate1 a)
      = some (Ba.inst aa) := by
    rw [denoteMeta_beta (ty := ty) m.acval_closed
      (acval_inst_self m) hwfe.2.fvarsBelow hws.2 hb.2 haa 0, hBa]
    rfl
  refine ⟨⟨Expr.WScoped.instantiate1_gen hws.2 0 hwfe.2,
      Expr.looseBVarsBounded_instantiate1_gen hb.2 hbfe.2,
      fun l hl => ?_⟩, fun l hl => ?_, _, hcross, ?_, ?_⟩
  · rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · exact hLfe l (by simp [Expr.fvarLeaves, h2])
    · exact hLa l h2
  · rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · rw [Expr.fvarLeaves]
      exact List.mem_append_left _ (htfsub l (hpisub l
        (by simp [Expr.fvarLeaves, h2])))
    · rw [Expr.fvarLeaves]
      exact List.mem_append_right _ h2
  · intro ρ hρ
    exact (WellDenotedV_inst0 (hoka ρ hρ)).mpr (hokBa ρ hρ _ (ha2 ρ hρ))
  · intro ρ hρ
    exact (sound_app V (hokf ρ hρ).1 (hoka ρ hρ).1 (hf2 ρ hρ)
      (ha2 ρ hρ) (hcod0 ρ hρ)).2

/-- `inferProjStep_of_claims` / `inferProjStepIO_of_claims`
(`Steps/ProjRows.lean:71`, `:160`): the tower law's typing clause. -/
theorem Infer.proj_sound (hin : RulesInputs V m φ) {g : Grade} {d : Nat}
    {sn : Name} {i : Nat} {pe tpe te : Expr} {us : List Level}
    {entry : ProjEntry}
    (htpe : InferSem m φ g d pe tpe) (hte : RedSem m φ d tpe te)
    (hhead : te.getAppFn = .const sn us)
    (hent : env.findProj? sn i = some entry)
    (hlen : te.getAppArgs.length = entry.numParams)
    (hus : us.length = entry.levelParams.length)
    (hprop : Level.isEquiv entry.structSort .zero = some true →
      Level.isEquiv (Level.subst entry.levelParams us entry.fieldSort) .zero
        = some true) :
    InferSem m φ g d (.proj sn i pe) (entry.typeAt us te.getAppArgs pe) := by
  refine InferSem.of_uniform ?_
  intro Δa ea hfr hC hea hgr
  obtain ⟨hws, hb, hLb⟩ := hfr
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hLpe : Expr.LeavesBounded pe := fun l hl =>
    hLb l (by simpa [Expr.fvarLeaves] using hl)
  have hCpe : CtxOk m φ d Δa pe :=
    hC.of_subset (fun l hl => by simpa [Expr.fvarLeaves] using hl)
  obtain ⟨vp, hvp, rfl⟩ := denoteMeta_proj_inv_tower hent hea
  -- the io grade's premise, hoisted through the projection spelling
  have hoist : g = .io → Graded V Δa vp := fun hg ρ hρ =>
    WellDenotedV_projAV_hoist ((hgr hg) ρ hρ)
  -- the scrutinee's inferred type, and its reduct
  obtain ⟨htpef, htpesub, hokPe, tpea, htpea, hokTpe, hmemPe⟩ :=
    htpe.apply ⟨hws, hb, hLpe⟩ hCpe hvp hoist
  obtain ⟨htef, htesub, tea, htea, hokTe, heqTe⟩ :=
    hte htpef (hCpe.of_subset htpesub) htpea hokTpe
  obtain ⟨hwte', hbte, hLte⟩ := htef
  -- the tower law's typing clause
  obtain ⟨-, -, -, ⟨cvT, capsT, hfT, hlpsT, -⟩, hO5, _, -, -, hlaw, -⟩ :=
    hin.tower_ok sn i entry hent
  obtain ⟨⟨Ta, hTa, hA⟩, -⟩ := hlaw us hus
  -- the reduced type's spine, at the former's leaf
  rw [show te = Expr.mkAppN te.getAppFn te.getAppArgs from
    (Expr.mkAppN_getApp te).symm, hhead] at htea
  obtain ⟨vT, vs, hvT, hspt, hteq⟩ := denoteMeta_mkAppN_inv htea
  have hlenT : us.length
      = (ConstantInfo.indInfo cvT capsT).toConstantVal.levelParams.length := by
    show us.length = cvT.levelParams.length
    rw [hlpsT]; exact hus
  rw [denoteMeta_const hfT hlenT] at hvT
  have hvT' : vT = m.acval sn (Level.substFn φ entry.levelParams us) := by
    rw [← hlpsT]; exact (Option.some.inj hvT).symm
  subst hvT'
  subst hteq
  -- the residual: the entry type's peel, read
  have hframes : ∀ x ∈ te.getAppArgs ++ [pe],
      Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact ⟨hwte'.getAppArgs x hx',
        ConLeche.looseBVarsBounded_getAppArgs hbte x hx'⟩
    · rcases List.mem_singleton.mp hx' with rfl
      exact ⟨hws, hb⟩
  obtain ⟨restA, hrest, hpeel⟩ :=
    denoteMeta_typeAt_peel hent hTa hlen hframes (hspt.snoc hvp)
  have hlenVs : vs.length = entry.numParams := by
    rw [← hspt.length]; exact hlen
  have hlaw' : ∀ σ : Nat → V, Sat V Δa σ →
      WellDenotedV V σ (projAV (i + entry.off) vp) ∧
        WellDenotedV V σ restA ∧
        interp V σ (projAV (i + entry.off) vp) ∈ˢ interp V σ restA :=
    fun σ hσ =>
      hA (towerGuardAt_of hO5 (fun hp => by
        simp only [beq_iff_eq] at hp ⊢
        exact hprop hp)) σ vs vp restA hlenVs (hokTe σ hσ)
        (hokPe σ hσ) ((heqTe σ hσ) ▸ hmemPe σ hσ) hpeel
  -- the returned type's leaves: the spine's or the subject's
  have hleaves : ∀ l ∈ (entry.typeAt us te.getAppArgs pe).fvarLeaves,
      (∃ x ∈ te.getAppArgs, l ∈ x.fvarLeaves) ∨ l ∈ pe.fvarLeaves := by
    intro l hl
    rw [ProjEntry.typeAt_eq_instSpine entry us hlen pe] at hl
    rcases fvarLeaves_instSpine _ hl with hty | ⟨a, ha, hla⟩
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar
        (ConLeche.projEntry_body_hasFvar m.wf hent us)] at hty
      exact nomatch hty
    · rcases List.mem_append.mp ha with ha | ha
      · exact Or.inl ⟨a, ha, hla⟩
      · rcases List.mem_singleton.mp ha with rfl
        exact Or.inr hla
  refine ⟨⟨ConLeche.projEntry_typeAt_WScoped m.wf hent us hlen
      (fun a ha => hwte'.getAppArgs a ha) hws,
    ConLeche.projEntry_typeAt_looseBVars m.wf hent us hlen
      (fun a ha => ConLeche.looseBVarsBounded_getAppArgs hbte a ha) hb,
    fun l hl => ?_⟩, fun l hl => ?_, ?_, restA, hrest, ?_, ?_⟩
  · rcases hleaves l hl with ⟨x, hx, hlx⟩ | hlx
    · exact hLte l (ConLeche.fvarLeaves_getAppArgs hx l hlx)
    · exact hLpe l hlx
  · rcases hleaves l hl with ⟨x, hx, hlx⟩ | hlx
    · rw [Expr.fvarLeaves]
      exact htpesub l (htesub l (ConLeche.fvarLeaves_getAppArgs hx l hlx))
    · rw [Expr.fvarLeaves]
      exact hlx
  · exact fun σ hσ => (hlaw' σ hσ).1
  · exact fun σ hσ => (hlaw' σ hσ).2.1
  · exact fun σ hσ => (hlaw' σ hσ).2.2

end ConLeche.Model.Rules
