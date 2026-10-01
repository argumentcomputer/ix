module

import ConLeche.Model.Capstone
import ConLeche.Model.NatEqs
public import ConLeche.Model.DivModCert
import ConLeche.Model.Caps
import ConLeche.Model.RecRulesCons
public import ConLeche.Model.ReduceOps
import ConLeche.Semantics.DeclRun
import ConLeche.Model.Annot.BitLevels

public section

/-!
# The harvest, value kinds (task #161, P4 — the fold's species)

The `defn` species below, and then its `thm` mirror (batch H2, T1).
The `opaque` mirror is **not** here: see the SKIP record at the end of
this module for the one missing link and the upstream strengthening it
names.

`harvestDefn`: from a checked `def`'s harvest relation (`DeclDefnR`,
the H1-exposed runs included) and the P machinery at the prefix
environment, the P invariant extends — `declStep_preserves_of_cons`'s premises
assembled end to end:

* the v1 base and its agreement come **constructively** from
  `declDefnS` (`∃ m'`, not a `Nonempty`);
* the new leaf `A ψ` is the value's own `denoteMeta` reading (the
  `accepted_reads` totality leaf at the H1-exposed infer run); its
  laws are `denoteMeta_closed` / `denoteMeta_params_ext` / the claims'
  `WellDenotedV` conclusions at `Sat_nil`;
* the leaf erases to the v1 leaf (`hAerase`) through `denoteMeta_erase`,
  `denote_install` (at `LitAgree.of_fresh` — freshness alone), and the
  new base's own `defn_eq` field;
* the membership (`hmemNew`) is the claims' membership at the value
  run carried across the H1-exposed defeq run by the defeq claim;
* `nat_heads` at the extension derives from guard reflection
  (`natLitSupported_cons_back`) + freshness — no bespoke premise.

No routed semantic premise any more: the subject-side totality leaf
is `acceptedReads_of` (`Steps/Accepted.lean`, task #161 ENDGAME A),
so the harvests take the environment invariant and the install-tier
pins alone.
`LitGuardsAgree` is GONE from every harvest: the guard equality is
refutable at a support-completing install, and the monotone crossing
(`denoteMeta_cons_fresh_mono`) plus guard reflection replace every use —
the harvests carry no literal-tier premise at all.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics ConLeche.SetModel
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint inferTypeCore isDefEqCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {F : Nat}

/-- **The `Nat` guard reflects across a value-kind cons**: the three
components need `indInfo`/`ctorInfo` shapes, which no `defn`/`thm`/
`axiom` cons can supply — so a guard true at the extension was true
at the prefix.  (This kills the routed guard-equality premise: the
nat half is free, and the str half is never consulted backward.) -/
theorem natLitSupported_cons_back {env : Env} {c₀ : ConstantInfo}
    (hknd : (∀ cv mI, c₀ ≠ .indInfo cv mI) ∧
      ∀ cv a b, c₀ ≠ .ctorInfo cv a b)
    (hg : ConLeche.natLitSupported ⟨c₀ :: env.consts⟩ = true) :
    ConLeche.natLitSupported env = true := by
  have hfind : ∀ p : Name,
      (⟨c₀ :: env.consts⟩ : Env).find? p
        = if c₀.name = p then some c₀ else env.find? p := by
    intro p
    show List.find? _ (c₀ :: env.consts) = _
    by_cases hp : c₀.name = p
    · rw [List.find?_cons_of_pos (by simpa using hp), if_pos hp]
    · rw [List.find?_cons_of_neg (by simpa using hp), if_neg hp]
      rfl
  simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hg ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := hg
  rw [hfind] at h1 h2 h3
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · revert h1
    split
    · cases c₀ with
      | indInfo cv mI => exact absurd rfl (hknd.1 cv mI)
      | _ => intro h; simp [natIndOk] at h
    · exact id
  · revert h2
    split
    · cases c₀ with
      | ctorInfo cv a b => exact absurd rfl (hknd.2 cv a b)
      | _ => intro h; simp [natZeroOk] at h
    · exact id
  · revert h3
    split
    · cases c₀ with
      | ctorInfo cv a b => exact absurd rfl (hknd.2 cv a b)
      | _ => intro h; simp [natSuccOk] at h
    · exact id

/-- **`nat_heads` at a fresh cons, from the routed guard agreement.**
The three literal heads are *stored* wherever the guard holds, so
freshness makes each of them distinct from the new name and the fresh
leaf is invisible to all three — `mp.nat_heads` transports unchanged.
No bespoke premise: this is the lemma `InstallP.lean`'s docstring
calls `declStepPM_natHeads_fresh`, landed here because the harvest is
its only consumer and `InstallP.lean` is not this batch's to edit.

The species below predates it and still carries the block inline (its
statement is sealed; the proof adopts this when the seal next opens);
`harvestThm` and `harvestAxiom` call it. -/
theorem natHeads_cons_fresh (mp : EnvModelM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none)
    (hknd : (∀ cv mI, c₀ ≠ .indInfo cv mI) ∧
      ∀ cv a b, c₀ ≠ .ctorInfo cv a b)
    (m2 : EnvModel V ⟨c₀ :: env.consts⟩)
    (hacval : m2.acval = acvalWith mp.base2.acval c₀.name A)
    (φ : Name → Nat) : NatHeads m2 φ := by
  intro hg ρ
  rw [hacval]
  have hgold : ConLeche.natLitSupported env = true :=
    natLitSupported_cons_back hknd hg
  have hstored : ∀ n0, (env.find? n0).isSome = true → n0 ≠ c₀.name := by
    intro n0 hs hh
    rw [hh, hfresh] at hs
    exact nomatch hs
  have hz : (env.find? natZeroName).isSome = true := by
    have hgg := hgold
    simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hgg
    obtain ⟨⟨-, hz0⟩, -⟩ := hgg
    revert hz0; cases env.find? natZeroName <;> simp [natZeroOk]
  have hsc : (env.find? natSuccName).isSome = true := by
    have hgg := hgold
    simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hgg
    obtain ⟨-, hs0⟩ := hgg
    revert hs0; cases env.find? natSuccName <;> simp [natSuccOk]
  have hn : (env.find? natName).isSome = true := by
    have hgg := hgold
    simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hgg
    obtain ⟨⟨hn0, -⟩, -⟩ := hgg
    revert hn0; cases env.find? natName <;> simp [natIndOk]
  have e1 : acvalWith mp.base2.acval c₀.name A natZeroName
      = mp.base2.acval natZeroName :=
    acvalWith_ne (hstored _ hz)
  have e2 : acvalWith mp.base2.acval c₀.name A natSuccName
      = mp.base2.acval natSuccName :=
    acvalWith_ne (hstored _ hsc)
  have e3 : acvalWith mp.base2.acval c₀.name A natName
      = mp.base2.acval natName :=
    acvalWith_ne (hstored _ hn)
  have := mp.nat_heads φ hgold ρ
  simpa only [e1, e2, e3] using this

/-- **The `defn` harvest** (see the module docstring). -/
theorem harvestDefn (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ env)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    {env₂ : Env}
    (hR : DeclDefnRun μ F env cv value hint env₂) :
    Nonempty (EnvModelM V μ env₂) := by
  obtain ⟨type', value', hcv, hvfr, rfl, hnatc, hdmc⟩ := hR
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr,
    hrunT⟩ := hcv
  obtain ⟨hvlb, hvhf, hannv, hvp, hvr, ⟨vtype, hvrun, hvde⟩⟩ := hvfr
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  obtain ⟨hvf', hbv'⟩ := annotate_syntax hannv hvhf hvlb
  have hfresh : env.find? cv.name = none :=
    Option.isNone_iff_eq_none.mp hfind
  -- the scoping packages of the primed forms
  have hwv : Expr.WScoped 0 value' := Expr.WScoped.of_not_hasFvar hvf'
  have hLv : Expr.LeavesBounded value' := fun l hl => by
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hvf'] at hl
    exact absurd hl (List.not_mem_nil)
  have hnlv : value'.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar hvf'
  have hwt : Expr.WScoped 0 type' := Expr.WScoped.of_not_hasFvar htf'
  have hLt : Expr.LeavesBounded type' := fun l hl => by
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'] at hl
    exact absurd hl (List.not_mem_nil)
  have hnlt : type'.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'
  have hCv : CtxOk mp.base2 (fun _ => 0) 0 ([] : List AnnotTerm) value' :=
    CtxOk.nil hnlv
  -- the leaf: the value's reading, per assignment
  have hAex : ∀ ψ : Name → Nat,
      ∃ va, denoteMeta mp.base2.acval env ψ 0 value' = some va := by
    intro ψ
    exact acceptedReads_of mp.base2 ψ hvrun hwv hbv' hLv
  let A : (Name → Nat) → AnnotTerm :=
    fun ψ => (denoteMeta mp.base2.acval env ψ 0 value').getD default
  have hA : ∀ ψ : Name → Nat,
      denoteMeta mp.base2.acval env ψ 0 value' = some (A ψ) := by
    intro ψ
    obtain ⟨va, hva⟩ := hAex ψ
    show _ = some ((denoteMeta mp.base2.acval env ψ 0 value').getD default)
    simp [hva]
  -- the type's reading, per assignment
  obtain ⟨stype, u, hst, hens⟩ := hrunT
  have hTex : ∀ ψ : Name → Nat,
      ∃ ta, denoteMeta mp.base2.acval env ψ 0 type' = some ta := by
    intro ψ
    exact acceptedReads_of mp.base2 ψ hst hwt hbt' hLt
  let Ta : (Name → Nat) → AnnotTerm :=
    fun ψ => (denoteMeta mp.base2.acval env ψ 0 type').getD default
  have hTa : ∀ ψ : Name → Nat,
      denoteMeta mp.base2.acval env ψ 0 type' = some (Ta ψ) := by
    intro ψ
    obtain ⟨ta, hta⟩ := hTex ψ
    show _ = some ((denoteMeta mp.base2.acval env ψ 0 type').getD default)
    simp [hta]
  -- the claims and the reads, per assignment
  have hclaims := fun ψ =>
    checkSoundAt (V := V) hμ (Rules.RulesInputs.ofSem mp ψ) F
  have hreads : ∀ ψ, InferReads mp.base2 μ ψ F :=
    fun ψ => inferReads_of hμ (Rules.RulesInputs.ofSem mp ψ)
  -- the value's rows: gradings and the membership at its own type
  have hrowsV : ∀ ψ : Name → Nat, ∃ vta,
      denoteMeta mp.base2.acval env ψ 0 vtype = some vta ∧
      ((∀ ρ : Nat → V, Sat V [] ρ → WellDenotedV V ρ (A ψ)) ∧
        (∀ ρ : Nat → V, Sat V [] ρ → WellDenotedV V ρ vta) ∧
        ∀ ρ : Nat → V, Sat V [] ρ →
          interp V ρ (A ψ) ∈ˢ interp V ρ vta) := by
    intro ψ
    obtain ⟨-, -, -, ihi⟩ := hclaims ψ
    obtain ⟨vta, hvta⟩ :=
      hreads ψ hvrun hwv hbv' hLv (CtxOk.nil hnlv)
        (hA ψ)
    exact ⟨vta, hvta, ihi hvrun hwv hbv' hLv (CtxOk.nil hnlv)
      (hA ψ) hvta⟩
  -- the type's rows: its own grading as a subject
  have hrowsT : ∀ ψ : Name → Nat, ∃ sta,
      denoteMeta mp.base2.acval env ψ 0 stype = some sta ∧
      ((∀ ρ : Nat → V, Sat V [] ρ → WellDenotedV V ρ (Ta ψ)) ∧
        (∀ ρ : Nat → V, Sat V [] ρ → WellDenotedV V ρ sta) ∧
        ∀ ρ : Nat → V, Sat V [] ρ →
          interp V ρ (Ta ψ) ∈ˢ interp V ρ sta) := by
    intro ψ
    obtain ⟨-, -, -, ihi⟩ := hclaims ψ
    obtain ⟨sta, hsta⟩ :=
      hreads ψ hst hwt hbt' hLt (CtxOk.nil hnlt)
        (hTa ψ)
    exact ⟨sta, hsta, ihi hst hwt hbt' hLt (CtxOk.nil hnlt)
      (hTa ψ) hsta⟩
  -- the leaf laws
  have hAclosed : ∀ (ψ : Name → Nat) (k : Nat),
      (A ψ).liftN 1 k = A ψ := fun ψ k =>
    denoteMeta_closed mp.base2.acval_erase mp.base2.cval_closed
      hvf' hbv' (hA ψ) 1 k
  have hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ cv.levelParams, ψ₁ p = ψ₂ p) → A ψ₁ = A ψ₂ := by
    intro ψ₁ ψ₂ hψ
    have := denoteMeta_params_ext mp.base2 hψ 0 value' hvp
    rw [hA ψ₁, hA ψ₂] at this
    exact Option.some.inj this
  have hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      WellDenoted V ρ (A ψ) := by
    intro ψ ρ
    obtain ⟨vta, hvta, hrE, -, -⟩ := hrowsV ψ
    exact (hrE ρ (Sat_nil V ρ)).1
  have hAvalid : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotValid V ρ (A ψ) := by
    intro ψ ρ
    obtain ⟨vta, hvta, hrE, -, -⟩ := hrowsV ψ
    exact (hrE ρ (Sat_nil V ρ)).2
  -- the membership at the declared type, across the defeq run
  have hmemA : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (A ψ) ∈ˢ interp V ρ (Ta ψ) := by
    intro ψ ρ
    obtain ⟨-, -, ihd, ihi⟩ := hclaims ψ
    obtain ⟨vta, hvta, hrE, hrT, hrM⟩ := hrowsV ψ
    obtain ⟨sta, hsta, htE, -, -⟩ := hrowsT ψ
    -- vtype's scoping package
    have hwvt : Expr.WScoped 0 vtype :=
      inferTypeCore_WScoped mp.base2.wf F hvrun hwv
    have hbvt : vtype.looseBVarsBounded 0 = true :=
      inferTypeCore_looseBVars mp.base2.wf F hvrun hwv hbv' hLv
    have hnlvt : vtype.fvarLeaves = [] := by
      have hsub := inferTypeCore_fvarLeaves mp.base2.wf F hvrun hwv
      cases hh : vtype.fvarLeaves with
      | nil => rfl
      | cons l ls =>
        have := hsub l (by rw [hh]; exact List.mem_cons_self ..)
        rw [hnlv] at this
        exact absurd this (List.not_mem_nil)
    have hLvt : Expr.LeavesBounded vtype := fun l hl => by
      rw [hnlvt] at hl
      exact absurd hl (List.not_mem_nil)
    have heq := ihd hvde hwvt hbvt hLvt hwt hbt' hLt
      (CtxOk.nil hnlvt) (CtxOk.nil hnlt) hvta (hTa ψ)
      hrT htE ρ (Sat_nil V ρ)
    rw [← heq]
    exact hrM ρ (Sat_nil V ρ)
  -- the transfer to the extension
  have hcbT : ConstsBound env type' := constsBound_of_constsResolve _ htr
  have hcbV : ConstsBound env value' := constsBound_of_constsResolve _ hvr
  have hcomp : ∀ (ψ : Name → Nat) (e : Expr), ConstsBound env e →
      ∀ {ea : AnnotTerm}, denoteMeta mp.base2.acval env ψ 0 e = some ea →
      denoteMeta (acvalWith mp.base2.acval cv.name A)
          ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
            env.consts⟩ ψ 0 e = some ea :=
    fun ψ e hcb {ea} h =>
      denoteMeta_cons_fresh_mono
        (acval := mp.base2.acval)
        (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
        (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
        ψ 0 e hcb h
  -- assemble
  refine ⟨(declStep_preserves_of_cons mp
    (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
    (A := A) hfresh
    (ConsHead.ofFresh
      (EnvWF.cons mp.base2.wf ⟨htf', htp,
        Expr.constsResolve_mono htr, hbt',
        (fun _ _ _ heq => by
          obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.defnInfo.inj heq
          exact ⟨hvf', hvp, Expr.constsResolve_mono hvr, hbv'⟩),
        (fun _ _ _ _ heq => nomatch heq),
        (fun _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩)
      (fun ψ => denote_closed mp.base2.cval_closed hvf' hbv'
        (denoteMeta_erase mp.base2.acval_erase 0 value' (hA ψ)))
      hnres (fun _ heq => nomatch heq)
      (fun _ _ _ _ heq => nomatch heq)) hAclosed
    hAparams hAok hAvalid ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).choose⟩
  · -- `htyReads`
    intro ψ
    show ∃ ta, denoteMeta (acvalWith mp.base2.acval cv.name A)
      ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
        env.consts⟩ ψ 0 type' = some ta
    exact ⟨Ta ψ, hcomp ψ type' hcbT (hTa ψ)⟩
  · -- `htyOk`
    intro ψ ta hta ρ
    replace hta : denoteMeta (acvalWith mp.base2.acval cv.name A)
        ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
          env.consts⟩ ψ 0 type' = some ta := hta
    obtain rfl : ta = Ta ψ :=
      (Option.some.inj
        ((hcomp ψ type' hcbT (hTa ψ)).symm.trans hta)).symm
    obtain ⟨sta, hsta, htE, -, -⟩ := hrowsT ψ
    exact htE ρ (Sat_nil V ρ)
  · -- `hmemNew`
    intro ψ ta hta ρ
    replace hta : denoteMeta (acvalWith mp.base2.acval cv.name A)
        ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
          env.consts⟩ ψ 0 type' = some ta := hta
    obtain rfl : ta = Ta ψ :=
      (Option.some.inj
        ((hcomp ψ type' hcbT (hTa ψ)).symm.trans hta)).symm
    exact hmemA ψ ρ
  · -- `hvalReads`
    intro ψ cv2 value2 hmem
    obtain ⟨hint2, hdt⟩ := hmem
    injection hdt with h1 h2 h3
    show denoteMeta (acvalWith mp.base2.acval cv.name A)
        ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
          env.consts⟩ ψ 0 value2
      = some (A ψ)
    rw [h2]
    exact hcomp ψ value' hcbV (hA ψ)
  · -- `nat_heads` at the extension, from the guard agreement
    intro φ hg ρ
    show interp V ρ (acvalWith mp.base2.acval cv.name A natZeroName
          (Level.substFn φ [] []))
        ∈ˢ interp V ρ (acvalWith mp.base2.acval cv.name A natName
          (Level.substFn φ [] [])) ∧
      interp V ρ (acvalWith mp.base2.acval cv.name A natSuccName
          (Level.substFn φ [] []))
        ∈ˢ piR 1 (interp V ρ (acvalWith mp.base2.acval cv.name A
            natName (Level.substFn φ [] [])))
          (fun _ => interp V ρ (acvalWith mp.base2.acval cv.name A
            natName (Level.substFn φ [] [])))
    have hgold : ConLeche.natLitSupported env = true :=
      natLitSupported_cons_back
        ⟨(fun _ _ h => ConstantInfo.noConfusion h),
          (fun _ _ _ h => ConstantInfo.noConfusion h)⟩ hg
    have hstored : ∀ n0, (env.find? n0).isSome = true →
        n0 ≠ cv.name := by
      intro n0 hs hh
      rw [hh, hfresh] at hs
      exact nomatch hs
    have hz : (env.find? natZeroName).isSome = true := by
      have hgg := hgold
      simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hgg
      obtain ⟨⟨-, hz0⟩, -⟩ := hgg
      revert hz0; cases env.find? natZeroName <;> simp [natZeroOk]
    have hsc : (env.find? natSuccName).isSome = true := by
      have hgg := hgold
      simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hgg
      obtain ⟨-, hs0⟩ := hgg
      revert hs0; cases env.find? natSuccName <;> simp [natSuccOk]
    have hn : (env.find? natName).isSome = true := by
      have hgg := hgold
      simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hgg
      obtain ⟨⟨hn0, -⟩, -⟩ := hgg
      revert hn0; cases env.find? natName <;> simp [natIndOk]
    have e1 : acvalWith mp.base2.acval cv.name A natZeroName
        = mp.base2.acval natZeroName :=
      acvalWith_ne (hstored _ hz)
    have e2 : acvalWith mp.base2.acval cv.name A natSuccName
        = mp.base2.acval natSuccName :=
      acvalWith_ne (hstored _ hsc)
    have e3 : acvalWith mp.base2.acval cv.name A natName
        = mp.base2.acval natName :=
      acvalWith_ne (hstored _ hn)
    have := mp.nat_heads φ hgold ρ
    simpa only [e1, e2, e3] using this
  · -- `nat_ops` at the extension: the operation's own install goes
    -- through the run-certificate conversion; any other definition
    -- preserves the stored entries
    intro φ
    by_cases hno : ConLeche.natOpNames.contains cv.name = true
    · -- the install
      obtain ⟨hg2, hdeps₂, hruns⟩ := hnatc hno
      have hcmem : cv.name ∈ ConLeche.natOpNames :=
        List.contains_iff_mem.mp hno
      -- the self entry of the dependency check: level-mono + pinned
      have hself : cv.name ∈ ConLeche.natOpDeps cv.name := by
        have h7 := hcmem
        simp only [ConLeche.natOpNames, List.mem_cons,
          List.not_mem_nil, or_false] at h7
        rcases h7 with h | h | h | h | h | h | h <;> rw [h] <;> decide
      have hd := List.all_eq_true.mp hdeps₂ cv.name (by simpa using hself)
      unfold ConLeche.natOpStoredOk at hd
      rw [show (⟨ConstantInfo.defnInfo ⟨cv.name, cv.levelParams, type'⟩
            value' hint :: env.consts⟩ : Env).find? cv.name
          = some (.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value'
            hint) from by
        rw [ConLeche.Env.find?_cons]; exact if_pos rfl] at hd
      simp only [Bool.and_eq_true] at hd
      have hlpcv : cv.levelParams = [] := by
        simpa [List.isEmpty_iff] using hd.1
      have hpin : ConLeche.natOpTyPinned
          (⟨ConstantInfo.defnInfo ⟨cv.name, cv.levelParams, type'⟩
            value' hint :: env.consts⟩ : Env) cv.name type' = true :=
        hd.2
      have hsE : ConLeche.natLitSupported env = true :=
        natLitSupported_cons_back
          ⟨(fun _ _ h => ConstantInfo.noConfusion h),
            (fun _ _ _ h => ConstantInfo.noConfusion h)⟩
          (ConLeche.natOpGuard_deps hg2).1
      have hTok : ∀ (ψ : Name → Nat) (ρ : Nat → V),
          WellDenotedV V ρ (Ta ψ) := fun ψ ρ => by
        obtain ⟨sta, hsta, hT1, -, -⟩ := hrowsT ψ
        exact hT1 ρ (Sat_nil V ρ)
      have hA2 : ∀ ψ, denoteMeta mp.base2.acval env ψ 2 value'
          = some (A ψ) := fun ψ =>
        denoteMeta_depth_of_closed mp.base2.acval_closed hvf'
          (hAclosed ψ) (hA ψ) 2
      obtain ⟨hSelfBin, hSelfUn⟩ := natSelfHead_install (φ := φ) mp
        hcmem hfresh hpin hsE hTa hTok hA2
        (fun ψ ρ => ⟨hAok ψ ρ, hAvalid ψ ρ⟩) hmemA
      exact natOps_install mp ((hclaims φ).2.2.1) (mp.nat_ops φ)
        hcmem hfresh hlpcv hsE hg2 hdeps₂ hruns hA hAclosed hvf' hbv'
        hSelfBin hSelfUn _ rfl
    · exact natOps_cons_fresh mp (mp.nat_ops φ)
        (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
        (A := A) hfresh (hntc := fun _ h => ConstantInfo.noConfusion h)
        (Or.inr (fun hm => hno (List.contains_iff_mem.mpr hm))) _ rfl
  · -- `div_mod` at the extension: a WF operation's own install goes
    -- through the certificate conversion; any other definition
    -- preserves the stored entries
    intro φ
    by_cases hno : ConLeche.natDivModNames.contains cv.name = true
    · obtain ⟨hgenv, _, -, -, _, -, hcerts⟩ := hdmc hno
      exact divMod_install mp (mp.div_mod φ) mp.eq_law
        (fun {d} {e} {t} hrun hw hb hL =>
          acceptedReads_of mp.base2 φ hrun hw hb hL)
        (hreads φ) ((hclaims φ).2.2.2) ((hclaims φ).2.2.1)
        (List.contains_iff_mem.mp hno) hfresh hgenv hcerts
        hA hAclosed hvf' hbv'
        hTa (fun ψ ρ => by
          obtain ⟨sta, hsta, hT1, -, -⟩ := hrowsT ψ
          exact hT1 ρ (Sat_nil V ρ))
        (fun ψ ρ => ⟨hAok ψ ρ, hAvalid ψ ρ⟩) hmemA _ rfl
    · exact divMod_cons_fresh (mp.div_mod φ)
        (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
        (A := A) hfresh
        (Or.inr (fun hm => hno (List.contains_iff_mem.mpr hm))) _ rfl
  · -- `eq_law` at the extension: a definition is not an inductive
    exact eqLaw_cons_valueKind mp.eq_law
      (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
      (A := A) (fun _ _ h => ConstantInfo.noConfusion h) _ rfl
  · -- `caps_ok` at the extension: a value-kind cons is neither a
    -- former, nor a capability constructor, nor a projection function,
    -- so no stored family can be completed here
    exact capsOk_cons_fresh mp mp.caps_ok
      (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ _ h => ConstantInfo.noConfusion h) _ rfl
  · -- `rec_rules` at the extension: a value-kind cons is neither a
    -- recursor nor a constructor, so no stored rule moves
    exact fun φ => recRules_cons_fresh mp
      (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ _ h => ConstantInfo.noConfusion h) _ rfl φ
  · -- `reduce_ops` at the extension: a definition is not an
    -- `axiomInfo`, so no reduce operation can be this cons
    exact reduceOps_cons_fresh mp.reduce_ops
      (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
      (A := A) hfresh
      (Or.inl (fun _ h => ConstantInfo.noConfusion h)) _ rfl
  · -- `tower_ok` (task #175 wiring W5): a value-kind cons is never a
    -- tower entry
    exact fun φ => towerOk_cons_fresh mp
      (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ h => ConstantInfo.noConfusion h) _ rfl φ

/-! ## The `thm` mirror (batch H2, T1)

`harvestThm` is `harvestDefn` at `DeclThmR`/`declThmS`, and the
mirror is exact: the same two front doors (`ConstantValR`,
`ValueFrontR`) with the same H1-exposed runs, the same leaf (the
value's `denoteMeta` reading), the same claims, the same crossing.  The
three deltas are all shape:

* the stored kind is `.thmInfo cvA value'` — no `hint`, and the v1
  step is `declThmS`, which takes **no** `DivModPinS` (a theorem has
  neither the structural-`Nat` nor the div/mod pin clause, so the
  harvest sheds `hdm` too);
* there is no erasure link to read: a theorem is opaque to reduction
  (`unfoldDefinition` has no `thmInfo` arm — anticipating
  https://github.com/leanprover/lean4/pull/14896), so the invariant
  keeps no equation between the value and the leaf, and `hvalReads`
  is vacuous (its one arm is a `defnInfo`).  The value is still read
  once, here: the leaf `A` is its reading, and `hmemA` is what makes
  the constant an inhabitant of its statement.

`DeclThmR`'s two extra conjuncts (H1's prop-check run triple and the
semantic `.sort 0` front) are **not spent**: the type's P reading and
its grading come from `ConstantValR`'s own run, exactly as in the
species, and the P invariant stores no is-a-proposition field.  They
are destructured away with `-`. -/
theorem harvestThm (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ env)
    {cv : ConstantVal} {value : Expr} {env₂ : Env}
    (hR : DeclThmRun μ F env cv value env₂) :
    Nonempty (EnvModelM V μ env₂) := by
  obtain ⟨type', value', hcv, -, hvfr, rfl⟩ := hR
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr,
    hrunT⟩ := hcv
  obtain ⟨hvlb, hvhf, hannv, hvp, hvr, ⟨vtype, hvrun, hvde⟩⟩ := hvfr
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  obtain ⟨hvf', hbv'⟩ := annotate_syntax hannv hvhf hvlb
  have hfresh : env.find? cv.name = none :=
    Option.isNone_iff_eq_none.mp hfind
  -- the scoping packages of the primed forms
  have hwv : Expr.WScoped 0 value' := Expr.WScoped.of_not_hasFvar hvf'
  have hLv : Expr.LeavesBounded value' := fun l hl => by
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hvf'] at hl
    exact absurd hl (List.not_mem_nil)
  have hnlv : value'.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar hvf'
  have hwt : Expr.WScoped 0 type' := Expr.WScoped.of_not_hasFvar htf'
  have hLt : Expr.LeavesBounded type' := fun l hl => by
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'] at hl
    exact absurd hl (List.not_mem_nil)
  have hnlt : type'.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'
  -- the leaf: the value's reading, per assignment
  have hAex : ∀ ψ : Name → Nat,
      ∃ va, denoteMeta mp.base2.acval env ψ 0 value' = some va := by
    intro ψ
    exact acceptedReads_of mp.base2 ψ hvrun hwv hbv' hLv
  let A : (Name → Nat) → AnnotTerm :=
    fun ψ => (denoteMeta mp.base2.acval env ψ 0 value').getD default
  have hA : ∀ ψ : Name → Nat,
      denoteMeta mp.base2.acval env ψ 0 value' = some (A ψ) := by
    intro ψ
    obtain ⟨va, hva⟩ := hAex ψ
    show _ = some ((denoteMeta mp.base2.acval env ψ 0 value').getD default)
    simp [hva]
  -- the type's reading, per assignment
  obtain ⟨stype, u, hst, hens⟩ := hrunT
  have hTex : ∀ ψ : Name → Nat,
      ∃ ta, denoteMeta mp.base2.acval env ψ 0 type' = some ta := by
    intro ψ
    exact acceptedReads_of mp.base2 ψ hst hwt hbt' hLt
  let Ta : (Name → Nat) → AnnotTerm :=
    fun ψ => (denoteMeta mp.base2.acval env ψ 0 type').getD default
  have hTa : ∀ ψ : Name → Nat,
      denoteMeta mp.base2.acval env ψ 0 type' = some (Ta ψ) := by
    intro ψ
    obtain ⟨ta, hta⟩ := hTex ψ
    show _ = some ((denoteMeta mp.base2.acval env ψ 0 type').getD default)
    simp [hta]
  -- the claims and the reads, per assignment
  have hclaims := fun ψ =>
    checkSoundAt (V := V) hμ (Rules.RulesInputs.ofSem mp ψ) F
  have hreads : ∀ ψ, InferReads mp.base2 μ ψ F :=
    fun ψ => inferReads_of hμ (Rules.RulesInputs.ofSem mp ψ)
  -- the value's rows: gradings and the membership at its own type
  have hrowsV : ∀ ψ : Name → Nat, ∃ vta,
      denoteMeta mp.base2.acval env ψ 0 vtype = some vta ∧
      ((∀ ρ : Nat → V, Sat V [] ρ → WellDenotedV V ρ (A ψ)) ∧
        (∀ ρ : Nat → V, Sat V [] ρ → WellDenotedV V ρ vta) ∧
        ∀ ρ : Nat → V, Sat V [] ρ →
          interp V ρ (A ψ) ∈ˢ interp V ρ vta) := by
    intro ψ
    obtain ⟨-, -, -, ihi⟩ := hclaims ψ
    obtain ⟨vta, hvta⟩ :=
      hreads ψ hvrun hwv hbv' hLv (CtxOk.nil hnlv)
        (hA ψ)
    exact ⟨vta, hvta, ihi hvrun hwv hbv' hLv (CtxOk.nil hnlv)
      (hA ψ) hvta⟩
  -- the type's rows: its own grading as a subject
  have hrowsT : ∀ ψ : Name → Nat, ∃ sta,
      denoteMeta mp.base2.acval env ψ 0 stype = some sta ∧
      ((∀ ρ : Nat → V, Sat V [] ρ → WellDenotedV V ρ (Ta ψ)) ∧
        (∀ ρ : Nat → V, Sat V [] ρ → WellDenotedV V ρ sta) ∧
        ∀ ρ : Nat → V, Sat V [] ρ →
          interp V ρ (Ta ψ) ∈ˢ interp V ρ sta) := by
    intro ψ
    obtain ⟨-, -, -, ihi⟩ := hclaims ψ
    obtain ⟨sta, hsta⟩ :=
      hreads ψ hst hwt hbt' hLt (CtxOk.nil hnlt)
        (hTa ψ)
    exact ⟨sta, hsta, ihi hst hwt hbt' hLt (CtxOk.nil hnlt)
      (hTa ψ) hsta⟩
  -- the leaf laws
  have hAclosed : ∀ (ψ : Name → Nat) (k : Nat),
      (A ψ).liftN 1 k = A ψ := fun ψ k =>
    denoteMeta_closed mp.base2.acval_erase mp.base2.cval_closed
      hvf' hbv' (hA ψ) 1 k
  have hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ cv.levelParams, ψ₁ p = ψ₂ p) → A ψ₁ = A ψ₂ := by
    intro ψ₁ ψ₂ hψ
    have := denoteMeta_params_ext mp.base2 hψ 0 value' hvp
    rw [hA ψ₁, hA ψ₂] at this
    exact Option.some.inj this
  have hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      WellDenoted V ρ (A ψ) := by
    intro ψ ρ
    obtain ⟨vta, hvta, hrE, -, -⟩ := hrowsV ψ
    exact (hrE ρ (Sat_nil V ρ)).1
  have hAvalid : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotValid V ρ (A ψ) := by
    intro ψ ρ
    obtain ⟨vta, hvta, hrE, -, -⟩ := hrowsV ψ
    exact (hrE ρ (Sat_nil V ρ)).2
  -- the membership at the declared type, across the defeq run
  have hmemA : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (A ψ) ∈ˢ interp V ρ (Ta ψ) := by
    intro ψ ρ
    obtain ⟨-, -, ihd, ihi⟩ := hclaims ψ
    obtain ⟨vta, hvta, hrE, hrT, hrM⟩ := hrowsV ψ
    obtain ⟨sta, hsta, htE, -, -⟩ := hrowsT ψ
    -- vtype's scoping package
    have hwvt : Expr.WScoped 0 vtype :=
      inferTypeCore_WScoped mp.base2.wf F hvrun hwv
    have hbvt : vtype.looseBVarsBounded 0 = true :=
      inferTypeCore_looseBVars mp.base2.wf F hvrun hwv hbv' hLv
    have hnlvt : vtype.fvarLeaves = [] := by
      have hsub := inferTypeCore_fvarLeaves mp.base2.wf F hvrun hwv
      cases hh : vtype.fvarLeaves with
      | nil => rfl
      | cons l ls =>
        have := hsub l (by rw [hh]; exact List.mem_cons_self ..)
        rw [hnlv] at this
        exact absurd this (List.not_mem_nil)
    have hLvt : Expr.LeavesBounded vtype := fun l hl => by
      rw [hnlvt] at hl
      exact absurd hl (List.not_mem_nil)
    have heq := ihd hvde hwvt hbvt hLvt hwt hbt' hLt
      (CtxOk.nil hnlvt) (CtxOk.nil hnlt) hvta (hTa ψ)
      hrT htE ρ (Sat_nil V ρ)
    rw [← heq]
    exact hrM ρ (Sat_nil V ρ)
  -- the transfer to the extension
  have hcbT : ConstsBound env type' := constsBound_of_constsResolve _ htr
  have hcbV : ConstsBound env value' := constsBound_of_constsResolve _ hvr
  have hcomp : ∀ (ψ : Name → Nat) (e : Expr), ConstsBound env e →
      ∀ {ea : AnnotTerm}, denoteMeta mp.base2.acval env ψ 0 e = some ea →
      denoteMeta (acvalWith mp.base2.acval cv.name A)
          ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩ value ::
            env.consts⟩ ψ 0 e = some ea :=
    fun ψ e hcb {ea} h =>
      denoteMeta_cons_fresh_mono
        (acval := mp.base2.acval)
        (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ value)
        (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
        ψ 0 e hcb h
  -- assemble
  refine ⟨(declStep_preserves_of_cons mp
    (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ value)
    (A := A) hfresh
    (ConsHead.ofFresh
      (EnvWF.cons mp.base2.wf ⟨htf', htp,
        Expr.constsResolve_mono htr, hbt',
        (fun _ _ _ heq => nomatch heq),
        (fun _ _ _ _ heq => nomatch heq),
        (fun _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩)
      (fun ψ => denote_closed mp.base2.cval_closed hvf' hbv'
        (denoteMeta_erase mp.base2.acval_erase 0 value' (hA ψ)))
      hnres (fun _ heq => nomatch heq)
      (fun _ _ _ _ heq => nomatch heq)) hAclosed
    hAparams hAok hAvalid ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).choose⟩
  · -- `htyReads`
    intro ψ
    show ∃ ta, denoteMeta (acvalWith mp.base2.acval cv.name A)
      ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩ value ::
        env.consts⟩ ψ 0 type' = some ta
    exact ⟨Ta ψ, hcomp ψ type' hcbT (hTa ψ)⟩
  · -- `htyOk`
    intro ψ ta hta ρ
    replace hta : denoteMeta (acvalWith mp.base2.acval cv.name A)
        ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩ value ::
          env.consts⟩ ψ 0 type' = some ta := hta
    obtain rfl : ta = Ta ψ :=
      (Option.some.inj
        ((hcomp ψ type' hcbT (hTa ψ)).symm.trans hta)).symm
    obtain ⟨sta, hsta, htE, -, -⟩ := hrowsT ψ
    exact htE ρ (Sat_nil V ρ)
  · -- `hmemNew`
    intro ψ ta hta ρ
    replace hta : denoteMeta (acvalWith mp.base2.acval cv.name A)
        ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩ value ::
          env.consts⟩ ψ 0 type' = some ta := hta
    obtain rfl : ta = Ta ψ :=
      (Option.some.inj
        ((hcomp ψ type' hcbT (hTa ψ)).symm.trans hta)).symm
    exact hmemA ψ ρ
  · -- `hvalReads`: vacuous — a theorem is opaque to reduction, so the
    -- invariant asks for no reading of its value at its leaf
    intro ψ cv2 value2 hmem
    obtain ⟨_, hdt⟩ := hmem
    exact nomatch hdt
  · -- `nat_heads` at the extension, from the guard agreement
    exact fun φ => natHeads_cons_fresh mp
      (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ value) (A := A)
      hfresh ⟨(fun _ _ h => ConstantInfo.noConfusion h),
          (fun _ _ _ h => ConstantInfo.noConfusion h)⟩
      _ rfl φ
  · -- `nat_ops` at the extension: a theorem is not a definition
    exact fun φ => natOps_cons_fresh mp (mp.nat_ops φ)
      (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ value) (A := A)
      hfresh (hntc := fun _ h => ConstantInfo.noConfusion h)
      (Or.inl (fun _ _ _ h => ConstantInfo.noConfusion h)) _ rfl
  · -- `div_mod`/`eq_law` at the extension: a theorem is neither a
    -- definition nor an inductive
    exact fun φ => divMod_cons_fresh (mp.div_mod φ)
      (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ value)
      (A := A) hfresh
      (Or.inl (fun _ _ _ h => ConstantInfo.noConfusion h)) _ rfl
  · exact eqLaw_cons_valueKind mp.eq_law
      (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ value)
      (A := A) (fun _ _ h => ConstantInfo.noConfusion h) _ rfl
  · -- `caps_ok` at the extension: a value-kind cons is neither a
    -- former, nor a capability constructor, nor a projection function,
    -- so no stored family can be completed here
    exact capsOk_cons_fresh mp mp.caps_ok
      (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ value)
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ _ h => ConstantInfo.noConfusion h) _ rfl
  · -- `rec_rules` at the extension: a value-kind cons is neither a
    -- recursor nor a constructor, so no stored rule moves
    exact fun φ => recRules_cons_fresh mp
      (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ value)
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ _ h => ConstantInfo.noConfusion h) _ rfl φ
  · -- `reduce_ops` at the extension: a theorem is not an `axiomInfo`
    exact reduceOps_cons_fresh mp.reduce_ops
      (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ value)
      (A := A) hfresh
      (Or.inl (fun _ h => ConstantInfo.noConfusion h)) _ rfl
  · -- `tower_ok` (task #175 wiring W5): a value-kind cons is never a
    -- tower entry
    exact fun φ => towerOk_cons_fresh mp
      (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ value)
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ h => ConstantInfo.noConfusion h) _ rfl φ

/-! ## The `opaque` kind: the H2 SKIP, since unlocked

(The record below is batch H2's original finding, kept for the trail;
the named strengthening has been LANDED — `extendValueS` now exposes
the leaf equation, `declOpaqueS` carries it with the annotate link —
and `harvestOpaque` at the end of this file is the species on it.)

There is **no `harvestOpaque` here**, and the wall is one equation.

Everything the species does transfers: `DeclOpaqueR` carries the same
two front doors, so the leaf `A` (the value's `denoteMeta` reading), its
laws, the type's reading and grading, the membership across the defeq
run, the crossing and `nat_heads` are all available verbatim, and
`hvalReads`'s two arms are *both* `nomatch` (an `opaque` is stored as
`.axiomInfo ⟨cv.name, cv.levelParams, type'⟩` — `Decl.lean`'s
`DeclOpaqueR`, third conjunct — so it is neither a `defnInfo` nor a
`thmInfo`).  What is missing is `declStep_preserves_of_cons`'s `hAerase`:

    ∀ ψ, (A ψ).erase = m'.cval cv.name ψ

At a `def` this is the new base's `defn_eq` field (`harvestDefn`
above; a theorem, opaque to reduction, has no such field).  At an
`opaque` **neither field speaks**: v1 stores an axiom and keeps no
equation between the discarded body and the leaf.  The equation is
*true* — `extendValueS` values the constant by `cvalAt m.cval env
cv.name value'`, i.e. by the value's own denotation — but
`declOpaqueS`'s conclusion is `∃ m' : EnvS V env₂, ∀ n, n ≠ cv.name →
m.cval n = m'.cval n`, and the agreement says nothing *at* `cv.name`.
The witness that knows the leaf is thrown away at the `∃`-boundary.

This is the same wall the U tier already named: `declStep2_of_value`'s
`hleaf` premise, whose docstring (`Step2Cons.lean`, `leafEq_defn` /
`leafEq_thm`) records "a residue only at the `opaque` kind".  The P
tier hits it in the same place, for the same reason.

**The bill (upstream, `ConLeche/SetR/Install/ValueKinds.lean` — not this
file's to edit).**  `declOpaqueS` should expose its leaf, the way
`extendValueS` already exposes its agreement:

    theorem declOpaqueS (hrp : ReducePinS V) … :
      ∃ m' : EnvS V env₂,
        (∀ n, n ≠ cv.name → m.cval n = m'.cval n) ∧
        ∀ value', annotateCore μ env F 0 value = .ok value' →
          ∀ ψ, denoteClosed m.cval env ψ value' = some (m'.cval cv.name ψ)

(the second conjunct quantified over the *annotate output*, which is
determined, since `value'` is bound inside `DeclOpaqueR`'s `∃`; the
proof is `cvalAt_self` at the `hkey` reading `extendValueS` already
has in hand, one `have` inside the existing call).  With that conjunct
`harvestOpaque` is the species with `defn_eq` replaced by it and both
`hvalReads` arms `nomatch` — no new semantic content, no new premise.
Landing it here instead as a premise would be a conditional form with
**no supplier at all** (unlike `harvestAxiom` below, whose premises
the pin tier really does discharge), so it is not landed. -/

/-! ## The `axiom` kind (batch H2, T3)

`harvestAxiom` is not a mirror of the species but of
`declStep2M_of_axiom` (`Step2Cons.lean`) at the P fields: **an axiom
has no value**, so the leaf is not a reading of anything the harvest
can see, and the constructive v1 step (`declAxiomExtS` /
`declAxiomLeafExtS`, `Install/Axiom.lean`) produces its leaf from the
pinned families' bespoke keys (`StdAxiomKeyS`, `trustCompilerKeyS`,
`ofReduceKeyS`).  So the leaf and its facts arrive as **premises** —
that is the pin tier's bill, and it is a real bill, not a conditional
form: `declAxiomLeafExtS` already yields `hbase`, `hag`, an `A`,
`hAerase` and `hAok` constructively; what P adds to that list is
`hAclosed`, `hAparams`, `hAvalid` and the interp membership `hmemA`.

What the harvest still does for free, and why the wrapper is worth
having: the *type* side is harvested exactly as in the species — the
type's P reading and its grading come from `ConstantValR`'s own
`inferType` run through `accepted_reads` and `checkSoundAt` — the
crossing to the extension is `denoteMeta_cons_fresh`, `hvalReads`'s two
arms are both `nomatch` (an axiom is neither a `def` nor a `thm`), and
`nat_heads` comes from the routed guard agreement plus freshness.
`hmemA` is stated at the **prefix** reading, which is where the pin
tier works; the wrapper crosses it.

`DeclAxiomR`'s fourth branch — the tolerated skip — needs none of
this: it stores nothing (`env₂ = env`), so its P invariant is `mp`
itself. -/
theorem harvestAxiom (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ env)
    {cv : ConstantVal} {type' : Expr} {A : (Name → Nat) → AnnotTerm}
    (hcv : ConstantValRun μ F env cv type')
    (hAvclosed : ∀ ψ : Name → Nat, Term.Closed ((A ψ).erase))
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ cv.levelParams, ψ₁ p = ψ₂ p) → A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (A ψ))
    (hAvalid : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotValid V ρ (A ψ))
    (hmemA : ∀ (ψ : Name → Nat) (ta : AnnotTerm),
      denoteMeta mp.base2.acval env ψ 0 type' = some ta →
      ∀ ρ : Nat → V, interp V ρ (A ψ) ∈ˢ interp V ρ ta)
    -- an axiom cons *is* an `axiomInfo`, so `reduce_ops`' preservation
    -- cannot go through the kind; it goes through the name.  Every
    -- `DeclAxiomR` branch pins `cv.name` (`matchesPin` compares it on
    -- the nose), and none of the pinned names is a reduce operation —
    -- the operations are installed as `opaque`s, never as axioms.
    (hnotreduce : cv.name ∉ ConLeche.reduceOpNames) :
    Nonempty (EnvModelM V μ
      ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩) := by
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr,
    hrunT⟩ := hcv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  have hfresh : env.find? cv.name = none :=
    Option.isNone_iff_eq_none.mp hfind
  -- the type's scoping package
  have hwt : Expr.WScoped 0 type' := Expr.WScoped.of_not_hasFvar htf'
  have hLt : Expr.LeavesBounded type' := fun l hl => by
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'] at hl
    exact absurd hl (List.not_mem_nil)
  have hnlt : type'.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'
  -- the type's reading, per assignment
  obtain ⟨stype, u, hst, hens⟩ := hrunT
  have hTex : ∀ ψ : Name → Nat,
      ∃ ta, denoteMeta mp.base2.acval env ψ 0 type' = some ta := by
    intro ψ
    exact acceptedReads_of mp.base2 ψ hst hwt hbt' hLt
  let Ta : (Name → Nat) → AnnotTerm :=
    fun ψ => (denoteMeta mp.base2.acval env ψ 0 type').getD default
  have hTa : ∀ ψ : Name → Nat,
      denoteMeta mp.base2.acval env ψ 0 type' = some (Ta ψ) := by
    intro ψ
    obtain ⟨ta, hta⟩ := hTex ψ
    show _ = some ((denoteMeta mp.base2.acval env ψ 0 type').getD default)
    simp [hta]
  -- the claims and the reads, per assignment
  have hclaims := fun ψ =>
    checkSoundAt (V := V) hμ (Rules.RulesInputs.ofSem mp ψ) F
  have hreads : ∀ ψ, InferReads mp.base2 μ ψ F :=
    fun ψ => inferReads_of hμ (Rules.RulesInputs.ofSem mp ψ)
  -- the type's rows: its own grading as a subject
  have hrowsT : ∀ ψ : Name → Nat, ∃ sta,
      denoteMeta mp.base2.acval env ψ 0 stype = some sta ∧
      ((∀ ρ : Nat → V, Sat V [] ρ → WellDenotedV V ρ (Ta ψ)) ∧
        (∀ ρ : Nat → V, Sat V [] ρ → WellDenotedV V ρ sta) ∧
        ∀ ρ : Nat → V, Sat V [] ρ →
          interp V ρ (Ta ψ) ∈ˢ interp V ρ sta) := by
    intro ψ
    obtain ⟨-, -, -, ihi⟩ := hclaims ψ
    obtain ⟨sta, hsta⟩ :=
      hreads ψ hst hwt hbt' hLt (CtxOk.nil hnlt)
        (hTa ψ)
    exact ⟨sta, hsta, ihi hst hwt hbt' hLt (CtxOk.nil hnlt)
      (hTa ψ) hsta⟩
  -- the transfer to the extension
  have hcbT : ConstsBound env type' := constsBound_of_constsResolve _ htr
  have hcomp : ∀ (ψ : Name → Nat) (e : Expr), ConstsBound env e →
      ∀ {ea : AnnotTerm}, denoteMeta mp.base2.acval env ψ 0 e = some ea →
      denoteMeta (acvalWith mp.base2.acval cv.name A)
          ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
            env.consts⟩ ψ 0 e = some ea :=
    fun ψ e hcb {ea} h =>
      denoteMeta_cons_fresh_mono
        (acval := mp.base2.acval)
        (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
        (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
        ψ 0 e hcb h
  -- assemble
  refine ⟨(declStep_preserves_of_cons mp
    (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
    (A := A) hfresh
    (ConsHead.ofFresh
      (EnvWF.cons mp.base2.wf ⟨htf', htp,
        Expr.constsResolve_mono htr, hbt',
        (fun _ _ _ heq => nomatch heq),
        (fun _ _ _ _ heq => nomatch heq),
        (fun _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩)
      hAvclosed hnres (fun _ heq => nomatch heq)
      (fun _ _ _ _ heq => nomatch heq))
    hAclosed
    hAparams hAok hAvalid ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).choose⟩
  · -- `htyReads`
    intro ψ
    show ∃ ta, denoteMeta (acvalWith mp.base2.acval cv.name A)
      ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
        env.consts⟩ ψ 0 type' = some ta
    exact ⟨Ta ψ, hcomp ψ type' hcbT (hTa ψ)⟩
  · -- `htyOk`
    intro ψ ta hta ρ
    replace hta : denoteMeta (acvalWith mp.base2.acval cv.name A)
        ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
          env.consts⟩ ψ 0 type' = some ta := hta
    obtain rfl : ta = Ta ψ :=
      (Option.some.inj
        ((hcomp ψ type' hcbT (hTa ψ)).symm.trans hta)).symm
    obtain ⟨sta, hsta, htE, -, -⟩ := hrowsT ψ
    exact htE ρ (Sat_nil V ρ)
  · -- `hmemNew`: the pin tier's membership, crossed
    intro ψ ta hta ρ
    replace hta : denoteMeta (acvalWith mp.base2.acval cv.name A)
        ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
          env.consts⟩ ψ 0 type' = some ta := hta
    obtain rfl : ta = Ta ψ :=
      (Option.some.inj
        ((hcomp ψ type' hcbT (hTa ψ)).symm.trans hta)).symm
    exact hmemA ψ (Ta ψ) (hTa ψ) ρ
  · -- `hvalReads`: an axiom is neither a `def` nor a `thm`
    intro ψ cv2 value2 hmem
    obtain ⟨_, hdt⟩ := hmem
    exact nomatch hdt
  · -- `nat_heads` at the extension, from the guard agreement
    exact fun φ => natHeads_cons_fresh mp
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩) (A := A)
      hfresh ⟨(fun _ _ h => ConstantInfo.noConfusion h),
          (fun _ _ _ h => ConstantInfo.noConfusion h)⟩
      _ rfl φ
  · -- `nat_ops` at the extension: an axiom is not a definition
    exact fun φ => natOps_cons_fresh mp (mp.nat_ops φ)
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩) (A := A)
      hfresh (hntc := fun _ h => ConstantInfo.noConfusion h)
      (Or.inl (fun _ _ _ h => ConstantInfo.noConfusion h)) _ rfl
  · -- `div_mod`/`eq_law` at the extension: an axiom is neither
    exact fun φ => divMod_cons_fresh (mp.div_mod φ)
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) hfresh
      (Or.inl (fun _ _ _ h => ConstantInfo.noConfusion h)) _ rfl
  · exact eqLaw_cons_valueKind mp.eq_law
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) (fun _ _ h => ConstantInfo.noConfusion h) _ rfl
  · -- `caps_ok` at the extension: a value-kind cons is neither a
    -- former, nor a capability constructor, nor a projection function,
    -- so no stored family can be completed here
    exact capsOk_cons_fresh mp mp.caps_ok
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ _ h => ConstantInfo.noConfusion h) _ rfl
  · -- `rec_rules` at the extension: a value-kind cons is neither a
    -- recursor nor a constructor, so no stored rule moves
    exact fun φ => recRules_cons_fresh mp
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ _ h => ConstantInfo.noConfusion h) _ rfl φ
  · -- `reduce_ops` at the extension: the cons *is* an `axiomInfo`, so
    -- the preservation goes through the pinned name (the branch's
    -- hypothesis), not the kind
    exact reduceOps_cons_fresh mp.reduce_ops
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) hfresh (Or.inr hnotreduce) _ rfl
  · -- `tower_ok` (task #175 wiring W5): a value-kind cons is never a
    -- tower entry
    exact fun φ => towerOk_cons_fresh mp
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ h => ConstantInfo.noConfusion h) _ rfl φ


/-! ## The `opaque` kind, unlocked (the exposed leaf equation)

The H2 SKIP record above named the one missing premise: the leaf
equation invisible at `declOpaqueS`'s `∃`-boundary.  `extendValueS`
now exposes it (an additive conjunct; `declOpaqueS` carries it with
the annotate link), and the harvest is the species with the erasure
link read **directly** off the exposed equation — no `denote_install`,
no `defn_eq`/`thm_ok` detour. -/

theorem harvestOpaque (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ env)
    {cv : ConstantVal} {value : Expr} {env₂ : Env}
    (hR : DeclOpaqueRun μ F env cv value env₂) :
    Nonempty (EnvModelM V μ env₂) := by
  obtain ⟨type', value', hcv, hvfr, rfl, hred⟩ := hR
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr,
    hrunT⟩ := hcv
  obtain ⟨hvlb, hvhf, hannv, hvp, hvr, ⟨vtype, hvrun, hvde⟩⟩ := hvfr
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  obtain ⟨hvf', hbv'⟩ := annotate_syntax hannv hvhf hvlb
  have hfresh : env.find? cv.name = none :=
    Option.isNone_iff_eq_none.mp hfind
  -- the scoping packages of the primed forms
  have hwv : Expr.WScoped 0 value' := Expr.WScoped.of_not_hasFvar hvf'
  have hLv : Expr.LeavesBounded value' := fun l hl => by
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hvf'] at hl
    exact absurd hl (List.not_mem_nil)
  have hnlv : value'.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar hvf'
  have hwt : Expr.WScoped 0 type' := Expr.WScoped.of_not_hasFvar htf'
  have hLt : Expr.LeavesBounded type' := fun l hl => by
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'] at hl
    exact absurd hl (List.not_mem_nil)
  have hnlt : type'.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'
  -- the leaf: the value's reading, per assignment
  have hAex : ∀ ψ : Name → Nat,
      ∃ va, denoteMeta mp.base2.acval env ψ 0 value' = some va := by
    intro ψ
    exact acceptedReads_of mp.base2 ψ hvrun hwv hbv' hLv
  let A : (Name → Nat) → AnnotTerm :=
    fun ψ => (denoteMeta mp.base2.acval env ψ 0 value').getD default
  have hA : ∀ ψ : Name → Nat,
      denoteMeta mp.base2.acval env ψ 0 value' = some (A ψ) := by
    intro ψ
    obtain ⟨va, hva⟩ := hAex ψ
    show _ = some ((denoteMeta mp.base2.acval env ψ 0 value').getD default)
    simp [hva]
  -- the type's reading, per assignment
  obtain ⟨stype, u, hst, hens⟩ := hrunT
  have hTex : ∀ ψ : Name → Nat,
      ∃ ta, denoteMeta mp.base2.acval env ψ 0 type' = some ta := by
    intro ψ
    exact acceptedReads_of mp.base2 ψ hst hwt hbt' hLt
  let Ta : (Name → Nat) → AnnotTerm :=
    fun ψ => (denoteMeta mp.base2.acval env ψ 0 type').getD default
  have hTa : ∀ ψ : Name → Nat,
      denoteMeta mp.base2.acval env ψ 0 type' = some (Ta ψ) := by
    intro ψ
    obtain ⟨ta, hta⟩ := hTex ψ
    show _ = some ((denoteMeta mp.base2.acval env ψ 0 type').getD default)
    simp [hta]
  -- the claims and the reads, per assignment
  have hclaims := fun ψ =>
    checkSoundAt (V := V) hμ (Rules.RulesInputs.ofSem mp ψ) F
  have hreads : ∀ ψ, InferReads mp.base2 μ ψ F :=
    fun ψ => inferReads_of hμ (Rules.RulesInputs.ofSem mp ψ)
  -- the value's rows: gradings and the membership at its own type
  have hrowsV : ∀ ψ : Name → Nat, ∃ vta,
      denoteMeta mp.base2.acval env ψ 0 vtype = some vta ∧
      ((∀ ρ : Nat → V, Sat V [] ρ → WellDenotedV V ρ (A ψ)) ∧
        (∀ ρ : Nat → V, Sat V [] ρ → WellDenotedV V ρ vta) ∧
        ∀ ρ : Nat → V, Sat V [] ρ →
          interp V ρ (A ψ) ∈ˢ interp V ρ vta) := by
    intro ψ
    obtain ⟨-, -, -, ihi⟩ := hclaims ψ
    obtain ⟨vta, hvta⟩ :=
      hreads ψ hvrun hwv hbv' hLv (CtxOk.nil hnlv)
        (hA ψ)
    exact ⟨vta, hvta, ihi hvrun hwv hbv' hLv (CtxOk.nil hnlv)
      (hA ψ) hvta⟩
  -- the type's rows: its own grading as a subject
  have hrowsT : ∀ ψ : Name → Nat, ∃ sta,
      denoteMeta mp.base2.acval env ψ 0 stype = some sta ∧
      ((∀ ρ : Nat → V, Sat V [] ρ → WellDenotedV V ρ (Ta ψ)) ∧
        (∀ ρ : Nat → V, Sat V [] ρ → WellDenotedV V ρ sta) ∧
        ∀ ρ : Nat → V, Sat V [] ρ →
          interp V ρ (Ta ψ) ∈ˢ interp V ρ sta) := by
    intro ψ
    obtain ⟨-, -, -, ihi⟩ := hclaims ψ
    obtain ⟨sta, hsta⟩ :=
      hreads ψ hst hwt hbt' hLt (CtxOk.nil hnlt)
        (hTa ψ)
    exact ⟨sta, hsta, ihi hst hwt hbt' hLt (CtxOk.nil hnlt)
      (hTa ψ) hsta⟩
  -- the leaf laws
  have hAclosed : ∀ (ψ : Name → Nat) (k : Nat),
      (A ψ).liftN 1 k = A ψ := fun ψ k =>
    denoteMeta_closed mp.base2.acval_erase mp.base2.cval_closed
      hvf' hbv' (hA ψ) 1 k
  have hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ cv.levelParams, ψ₁ p = ψ₂ p) → A ψ₁ = A ψ₂ := by
    intro ψ₁ ψ₂ hψ
    have := denoteMeta_params_ext mp.base2 hψ 0 value' hvp
    rw [hA ψ₁, hA ψ₂] at this
    exact Option.some.inj this
  have hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      WellDenoted V ρ (A ψ) := by
    intro ψ ρ
    obtain ⟨vta, hvta, hrE, -, -⟩ := hrowsV ψ
    exact (hrE ρ (Sat_nil V ρ)).1
  have hAvalid : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotValid V ρ (A ψ) := by
    intro ψ ρ
    obtain ⟨vta, hvta, hrE, -, -⟩ := hrowsV ψ
    exact (hrE ρ (Sat_nil V ρ)).2
  -- the membership at the declared type, across the defeq run
  have hmemA : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (A ψ) ∈ˢ interp V ρ (Ta ψ) := by
    intro ψ ρ
    obtain ⟨-, -, ihd, ihi⟩ := hclaims ψ
    obtain ⟨vta, hvta, hrE, hrT, hrM⟩ := hrowsV ψ
    obtain ⟨sta, hsta, htE, -, -⟩ := hrowsT ψ
    -- vtype's scoping package
    have hwvt : Expr.WScoped 0 vtype :=
      inferTypeCore_WScoped mp.base2.wf F hvrun hwv
    have hbvt : vtype.looseBVarsBounded 0 = true :=
      inferTypeCore_looseBVars mp.base2.wf F hvrun hwv hbv' hLv
    have hnlvt : vtype.fvarLeaves = [] := by
      have hsub := inferTypeCore_fvarLeaves mp.base2.wf F hvrun hwv
      cases hh : vtype.fvarLeaves with
      | nil => rfl
      | cons l ls =>
        have := hsub l (by rw [hh]; exact List.mem_cons_self ..)
        rw [hnlv] at this
        exact absurd this (List.not_mem_nil)
    have hLvt : Expr.LeavesBounded vtype := fun l hl => by
      rw [hnlvt] at hl
      exact absurd hl (List.not_mem_nil)
    have heq := ihd hvde hwvt hbvt hLvt hwt hbt' hLt
      (CtxOk.nil hnlvt) (CtxOk.nil hnlt) hvta (hTa ψ)
      hrT htE ρ (Sat_nil V ρ)
    rw [← heq]
    exact hrM ρ (Sat_nil V ρ)
  -- the transfer to the extension
  have hcbT : ConstsBound env type' := constsBound_of_constsResolve _ htr
  have hcbV : ConstsBound env value' := constsBound_of_constsResolve _ hvr
  have hcomp : ∀ (ψ : Name → Nat) (e : Expr), ConstsBound env e →
      ∀ {ea : AnnotTerm}, denoteMeta mp.base2.acval env ψ 0 e = some ea →
      denoteMeta (acvalWith mp.base2.acval cv.name A)
          ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
            env.consts⟩ ψ 0 e = some ea :=
    fun ψ e hcb {ea} h =>
      denoteMeta_cons_fresh_mono
        (acval := mp.base2.acval)
        (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
        (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
        ψ 0 e hcb h
  -- assemble
  refine ⟨(declStep_preserves_of_cons mp
    (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
    (A := A) hfresh
    (ConsHead.ofFresh
      (EnvWF.cons mp.base2.wf ⟨htf', htp,
        Expr.constsResolve_mono htr, hbt',
        (fun _ _ _ heq => nomatch heq),
        (fun _ _ _ _ heq => nomatch heq),
        (fun _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩)
      (fun ψ => denote_closed mp.base2.cval_closed hvf' hbv'
        (denoteMeta_erase mp.base2.acval_erase 0 value' (hA ψ)))
      hnres (fun _ heq => nomatch heq)
      (fun _ _ _ _ heq => nomatch heq))
    hAclosed
    hAparams hAok hAvalid ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).choose⟩
  · -- `htyReads`
    intro ψ
    show ∃ ta, denoteMeta (acvalWith mp.base2.acval cv.name A)
      ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
        env.consts⟩ ψ 0 type' = some ta
    exact ⟨Ta ψ, hcomp ψ type' hcbT (hTa ψ)⟩
  · -- `htyOk`
    intro ψ ta hta ρ
    replace hta : denoteMeta (acvalWith mp.base2.acval cv.name A)
        ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
          env.consts⟩ ψ 0 type' = some ta := hta
    obtain rfl : ta = Ta ψ :=
      (Option.some.inj
        ((hcomp ψ type' hcbT (hTa ψ)).symm.trans hta)).symm
    obtain ⟨sta, hsta, htE, -, -⟩ := hrowsT ψ
    exact htE ρ (Sat_nil V ρ)
  · -- `hmemNew`
    intro ψ ta hta ρ
    replace hta : denoteMeta (acvalWith mp.base2.acval cv.name A)
        ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
          env.consts⟩ ψ 0 type' = some ta := hta
    obtain rfl : ta = Ta ψ :=
      (Option.some.inj
        ((hcomp ψ type' hcbT (hTa ψ)).symm.trans hta)).symm
    exact hmemA ψ ρ
  · -- `hvalReads`: an opaque stores an axiom — both arms impossible
    intro ψ cv2 value2 hmem
    obtain ⟨_, hdt⟩ := hmem
    exact nomatch hdt
  · -- `nat_heads` at the extension, from the guard agreement
    exact fun φ => natHeads_cons_fresh mp
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩) (A := A)
      hfresh ⟨(fun _ _ h => ConstantInfo.noConfusion h),
          (fun _ _ _ h => ConstantInfo.noConfusion h)⟩
      _ rfl φ
  · -- `nat_ops` at the extension: an opaque stores an axiom entry
    exact fun φ => natOps_cons_fresh mp (mp.nat_ops φ)
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩) (A := A)
      hfresh (hntc := fun _ h => ConstantInfo.noConfusion h)
      (Or.inl (fun _ _ _ h => ConstantInfo.noConfusion h)) _ rfl
  · -- `div_mod`/`eq_law` at the extension: an opaque stores an axiom
    -- entry, which is neither a definition nor an inductive
    exact fun φ => divMod_cons_fresh (mp.div_mod φ)
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) hfresh
      (Or.inl (fun _ _ _ h => ConstantInfo.noConfusion h)) _ rfl
  · exact eqLaw_cons_valueKind mp.eq_law
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) (fun _ _ h => ConstantInfo.noConfusion h) _ rfl
  · -- `caps_ok` at the extension: a value-kind cons is neither a
    -- former, nor a capability constructor, nor a projection function,
    -- so no stored family can be completed here
    exact capsOk_cons_fresh mp mp.caps_ok
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ _ h => ConstantInfo.noConfusion h) _ rfl
  · -- `rec_rules` at the extension: a value-kind cons is neither a
    -- recursor nor a constructor, so no stored rule moves
    exact fun φ => recRules_cons_fresh mp
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ _ h => ConstantInfo.noConfusion h) _ rfl φ
  · -- `reduce_ops` at the extension: **this is the establishment**.
    -- An `opaque` cons is the only place a compiler-trust operation is
    -- ever stored, and `ReducePinR`'s recorded identity-certificate run
    -- is what makes the law true of it (`Interp/ReduceOps.lean`);
    -- every *other* stored operation crosses by the transport inside.
    exact reduceOps_install hμ mp hfresh hvf' hbv' hannv hA hAclosed
      hAok hAvalid hTa
      (fun ψ ρ => by
        obtain ⟨sta, hsta, htE, -, -⟩ := hrowsT ψ
        exact htE ρ (Sat_nil V ρ))
      hmemA hred _ rfl
  · -- `tower_ok` (task #175 wiring W5): a value-kind cons is never a
    -- tower entry
    exact fun φ => towerOk_cons_fresh mp
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ h => ConstantInfo.noConfusion h) _ rfl φ

end ConLeche.Model
