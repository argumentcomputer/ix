module

public import ConLeche.Model.Inductives.TowerCons

public section

/-!
# `CapsOk` across the direct block's member conses (task #175 W4c, P3 module 5, part 1)

The block's three non-entry conses — the former, the constructor and
the recursor — are exactly the head kinds `capsOk_cons_fresh`
refutes, because a head of those kinds can *complete* a stored family
(`EtaFamilyStored`).  Here the only family a block cons can complete
is the block's own (`T`): every other stored family's capability
constructor is stored already (the fold's `EtaFamiliesClosed` at the
pre-block environment), and its projection-function slots are
projection-shaped names a block constant never carries.  So the
prefix families' laws cross as at any fresh cons, and the block's
own family's laws are the install's premise.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps
  projFnName)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

theorem projFnName_isProjFnShape (T : Name) (j : Nat) :
    (projFnName T j).isProjFnShape = true := rfl

/-- **The block's own capability laws at a carrier** (task #210 Part
A): what `capsOk_cons_native` asks of the family being installed at
each of its conses — the η law where the family claims η and is
stored complete, the unit law where it claims unit-likeness.  A stage
takes it as a hypothesis about the carrier it builds; the assembly
discharges it from the leaves (or vacuously: `capsLawsAt_of_none`,
`capsLawsAt_vacuous`). -/
@[expose] def CapsLawsAt {env : Env} (m : EnvModel V env) (T : Name) (cvT : ConstantVal)
    (caps : IndCaps) : Prop :=
  (caps.eta = true → ConLeche.EtaFamilyStored env T caps →
    ∀ φ' : Name → Nat, EtaLaw m φ' T cvT caps) ∧
  (caps.unitlike = true → ∀ φ' : Name → Nat, UnitLaw m φ' T cvT caps)

/-- A record claiming η at a family with a field and no unit-likeness
owes nothing while its projection-function family is free: the η
half's premise `EtaFamilyStored` stores a projection function at every
field, and the first slot is fresh. -/
theorem capsLawsAt_vacuous {env : Env} (m : EnvModel V env) {T : Name} {cvT : ConstantVal}
    {caps : IndCaps} (hU : caps.unitlike = false)
    (hE : caps.eta = true → 0 < caps.etaFields ∧ env.find? (projFnName T 0) = none) :
    CapsLawsAt m T cvT caps := by
  refine ⟨fun he hfam => ?_, fun hu => absurd (hU.symm.trans hu) Bool.false_ne_true⟩
  exfalso
  obtain ⟨hpos, hfresh⟩ := hE he
  obtain ⟨-, -, hslots⟩ := hfam
  obtain ⟨cv, mI, rP, rules, hf⟩ := hslots 0 hpos
  rw [hfresh] at hf
  exact nomatch hf

/-- **`CapsOk` at a block-member cons.**  The head is fresh, not
projection-shaped, and either the block's former itself or not an
inductive at all; every other stored family's capability constructor
is stored in the prefix (`hother`); the block's own family's laws at
the extension are supplied (`hTlaws`). -/
theorem capsOk_cons_native (mp : EnvModelM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm} {T : Name}
    (hfresh : env.find? c₀.name = none)
    (hcross : ConsCrossEnv env c₀)
    (hpshape : c₀.name.isProjFnShape = false)
    (hkind : (∃ cvT caps, c₀ = .indInfo cvT caps ∧ c₀.name = T) ∨
      ∀ cv caps, c₀ ≠ .indInfo cv caps)
    (hother : ∀ (T' : Name) (cvT' : ConstantVal) (caps' : IndCaps),
      env.find? T' = some (.indInfo cvT' caps') → T' ≠ T →
      ConLeche.reservedBasisNames.contains T' = false →
      caps'.eta = true →
      ∃ cvC', env.find? caps'.etaCtor
        = some (.ctorInfo cvC' caps'.etaParams caps'.etaFields))
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A)
    (hTlaws : ∀ (cvT : ConstantVal) (caps : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      ConLeche.reservedBasisNames.contains T = false →
      (caps.eta = true → ConLeche.EtaFamilyStored ⟨c₀ :: env.consts⟩ T caps →
        ∀ φ' : Name → Nat, EtaLaw m₂ φ' T cvT caps) ∧
      (caps.unitlike = true → ∀ φ' : Name → Nat, UnitLaw m₂ φ' T cvT caps)) :
    CapsOk m₂ := by
  -- a stored family other than the block's is a prefix lookup
  have hdown : ∀ n : Name, n ≠ c₀.name →
      (⟨c₀ :: env.consts⟩ : Env).find? n = env.find? n := by
    intro n hn
    rw [ConLeche.Env.find?_cons, if_neg (fun hh => hn hh.symm)]
  have hneT : ∀ (T' : Name) (cvT' : ConstantVal) (caps' : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T' = some (.indInfo cvT' caps') →
      T' ≠ T → T' ≠ c₀.name := by
    intro T' cvT' caps' hf hne hh
    rcases hkind with ⟨cvT₀, caps₀, rfl, hname⟩ | hnotind
    · exact hne (hh.trans hname)
    · rw [hh, ConLeche.Env.find?_cons_self] at hf
      exact hnotind cvT' caps' (Option.some.inj hf)
  constructor
  · -- the η half
    intro T' cvT' caps' hf hcape hres hfam φ' us hlen
    by_cases hTT : T' = T
    · subst hTT
      exact (hTlaws cvT' caps' hf hres).1 hcape hfam φ' us hlen
    have hnT' : T' ≠ c₀.name := hneT T' cvT' caps' hf hTT
    have hfE : env.find? T' = some (.indInfo cvT' caps') := by
      rwa [hdown _ hnT'] at hf
    -- the family's names are all prefix lookups
    obtain ⟨cvC', hfC'⟩ := hother T' cvT' caps' hfE hTT hres hcape
    have hnC : caps'.etaCtor ≠ c₀.name := by
      intro hh
      rw [hh, hfresh] at hfC'
      exact nomatch hfC'
    have hnP : ∀ j, j < caps'.etaFields → projFnName T' j ≠ c₀.name := by
      intro j _ hh
      have := projFnName_isProjFnShape T' j
      rw [hh, hpshape] at this
      exact nomatch this
    have hfam₀ : ConLeche.EtaFamilyStored env T' caps' := by
      obtain ⟨hCres, ⟨cvC'', hfC''⟩, hfP⟩ := hfam
      refine ⟨hCres, ⟨cvC'', by rwa [hdown _ hnC] at hfC''⟩, ?_⟩
      intro j hj
      obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfP j hj
      exact ⟨cv2, mI2, rP2, rules2, by rwa [hdown _ (hnP j hj)] at hf2⟩
    obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ :=
      mp.caps_ok.1 T' cvT' caps' hfE hcape hres hfam₀ φ' us hlen
    refine ⟨TVa, ?_, hokTVa, ?_⟩
    · rw [hac]
      exact denoteMeta_cons_mono hfresh
        ((hcross.typeOf hfE).instantiateLevelParams _ _) _ 0
        (constsBound_instType mp.base2.wf
          (ConLeche.Semantics.Env.find?_mem hfE) us) hTVa
    · intro ρ ts rest x hlents hfit hmem
      rw [hac, acvalWith_ne hnT'] at hmem
      have hfab : etaFabArgsV
            (fun n => interp V ρ
              (m₂.acval n (Level.substFn φ' cvT'.levelParams us)))
            T' ts x caps'.etaFields
          = etaFabArgsV
            (fun n => interp V ρ
              (mp.base2.acval n (Level.substFn φ' cvT'.levelParams us)))
            T' ts x caps'.etaFields := by
        unfold etaFabArgsV projSpines
        refine congrArg _ (List.map_congr_left fun j hj => ?_)
        dsimp only
        rw [hac, acvalWith_ne (hnP j (List.mem_range.mp hj))]
      rw [hfab, hac, acvalWith_ne hnC]
      exact hlaw ρ ts rest x hlents hfit hmem
  · -- the unit-like half
    intro T' cvT' caps' hf hcapu hres φ' us hlen
    by_cases hTT : T' = T
    · subst hTT
      exact (hTlaws cvT' caps' hf hres).2 hcapu φ' us hlen
    have hnT' : T' ≠ c₀.name := hneT T' cvT' caps' hf hTT
    have hfE : env.find? T' = some (.indInfo cvT' caps') := by
      rwa [hdown _ hnT'] at hf
    obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ :=
      mp.caps_ok.2 T' cvT' caps' hfE hcapu hres φ' us hlen
    refine ⟨TVa, ?_, hokTVa, ?_⟩
    · rw [hac]
      exact denoteMeta_cons_mono hfresh
        ((hcross.typeOf hfE).instantiateLevelParams _ _) _ 0
        (constsBound_instType mp.base2.wf
          (ConLeche.Semantics.Env.find?_mem hfE) us) hTVa
    · intro ρ ts rest x y hlents hfit hmx hmy
      rw [hac, acvalWith_ne hnT'] at hmx hmy
      exact hlaw ρ ts rest x y hlents hfit hmx hmy

end ConLeche.Model
