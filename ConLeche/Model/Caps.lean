module

public import ConLeche.Model.Install

public section

/-!
# The structure-capability laws across a fresh cons (task #161, caps
tier)

The statements (`TeleFit`, `projSpines`/`etaFabArgsV`, `EtaLaw`,
`UnitLaw`, `CapsOk`) live in `Annot/EnvModelM.lean` beside `NatOps`,
`DivMod` and `EqLaw` — the `EnvModelM` field `caps_ok` must mention
them, and `EnvModelM` is upstream of everything in `Interp/`.  This file
is the *preservation* half: `capsOk_cons_fresh`, the obligation every
value-kind harvest discharges.

The shape is `CapsOkV.cons`'s non-head case (`Install/Cons.lean:204`)
at the P currency, with one addition the value currency does not have:
the law **carries the instantiated former type's reading**, so the
crossing must move that reading forward too
(`denoteMeta_cons_fresh_mono`, on `ConstsBound` of the instantiated type
— `constsBound_instType`).  Everything else is `acvalWith_ne` at the
three families of leaves the law mentions (the former, the capability
constructor, the documented projection functions), each `≠` the fresh
name because `EtaFamilyStored` *stores* them at kinds the four
value-kind harvests never cons.

The head case is therefore not a case at all: a `defnInfo`/`thmInfo`/
`axiomInfo` cons can be neither the former (an `indInfo` lookup), nor
the capability constructor (a `ctorInfo` lookup), nor a projection
function (a `recInfo` lookup), so all three disequalities are
`ConstantInfo.noConfusion`.  This is *simpler* than
`natOps_cons_fresh`, whose head case needs a disjunctive premise.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  IndCaps projFnName)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-! ## The instantiated former type is prefix-bound

`CapsOkV.cons` needs the same fact one currency over and gets it from
`Expr.constsResolve_instantiateLevelParams`; the P side needs it as a
`ConstsBound`, which is that lemma composed with
`constsBound_of_constsResolve`. -/

/-- **A stored constant's level-instantiated type is prefix-bound.**
Level instantiation does not move constants, so this is the stored
type's own `constsResolve` read through `ConstsBound`. -/
theorem constsBound_instType {env : Env} (hwf : ConLeche.EnvWF env)
    {c : ConstantInfo} (hc : c ∈ env.consts) (us : List Level) :
    ConstsBound env
      (c.toConstantVal.type.instantiateLevelParams
        c.toConstantVal.levelParams us) := by
  obtain ⟨-, -, hty, -⟩ := hwf c hc
  refine constsBound_of_constsResolve _ ?_
  rw [ConLeche.Expr.constsResolve_instantiateLevelParams]
  exact hty

/-! ## The family descent

An extended-environment family whose three stored members are all of
kinds the cons is not descends verbatim to the prefix, and its three
name families miss the fresh name. -/

/-- **The stored family descends past a value-kind cons**, together
with the three disequalities the law's leaf transport needs. -/
theorem etaFamilyStored_descend {c₀ : ConstantInfo} {T : Name}
    {cvT : ConstantVal} {caps : IndCaps}
    (hnotind : ∀ cv caps, c₀ ≠ .indInfo cv caps)
    (hnotctor : ∀ cv np nf, c₀ ≠ .ctorInfo cv np nf)
    (hnotrec : ∀ cv mI rP rules, c₀ ≠ .recInfo cv mI rP rules)
    (hf : (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps))
    (hfam : ConLeche.EtaFamilyStored ⟨c₀ :: env.consts⟩ T caps) :
    env.find? T = some (.indInfo cvT caps) ∧
      ConLeche.EtaFamilyStored env T caps ∧
      T ≠ c₀.name ∧ caps.etaCtor ≠ c₀.name ∧
      ∀ j, j < caps.etaFields → projFnName T j ≠ c₀.name := by
  obtain ⟨hCres, ⟨cvC, cnP, cnF, hfC⟩, hfP⟩ := hfam
  -- the former is not the cons: the cons is not an `indInfo`
  have hnT : T ≠ c₀.name := by
    rintro rfl
    rw [ConLeche.Env.find?_cons, if_pos rfl] at hf
    exact hnotind cvT caps (Option.some.inj hf)
  -- the capability constructor is not the cons: it is a `ctorInfo`
  have hnC : caps.etaCtor ≠ c₀.name := by
    intro heq
    rw [heq, ConLeche.Env.find?_cons, if_pos rfl] at hfC
    exact hnotctor cvC cnP cnF (Option.some.inj hfC)
  -- no projection function is the cons: they are `recInfo`s
  have hnP : ∀ j, j < caps.etaFields → projFnName T j ≠ c₀.name := by
    intro j hj heq
    obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfP j hj
    rw [heq, ConLeche.Env.find?_cons, if_pos rfl] at hf2
    exact hnotrec cv2 mI2 rP2 rules2 (Option.some.inj hf2)
  have hdown : ∀ n : Name, n ≠ c₀.name →
      (⟨c₀ :: env.consts⟩ : Env).find? n = env.find? n := by
    intro n hn
    rw [ConLeche.Env.find?_cons, if_neg (fun hh => hn hh.symm)]
  refine ⟨by rwa [hdown _ hnT] at hf, ⟨hCres, ⟨cvC, cnP, cnF, ?_⟩, ?_⟩,
    hnT, hnC, hnP⟩
  · rwa [hdown _ hnC] at hfC
  · intro j hj
    obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfP j hj
    rw [hdown _ (hnP j hj)] at hf2
    exact ⟨cv2, mI2, rP2, rules2, hf2⟩

/-! ## THE CAPS TIER'S NAMED WALL: the unit half's `EtaFamilyStored`
premise is not consumable

`CapsOk`'s docstring says the field is "keyed identically" to
`CapsOkV` (`Sound/Motives.lean:305`).  It is not: the **unit half**
gained a fourth premise, `EtaFamilyStored env T caps`, that the v1
field does not have — and neither does `DefEq.structUnit`
(`Rel.lean:759`) nor the install-side obligation `MemberUnitS`
(`Install/IndMembersS.lean:67`), both of which key the unit law on
exactly `find? = indInfo`, `unitlike`, `¬reserved`.

The premise makes the field **unusable by its own consumer**.
`StructUnitIrrel`'s only evidence is `structUnitCertFueled`'s verdict, and
`structUnitCert_inv` (`Verify/InferLemmas.lean:2305`) yields nine
facts, *none* of which mentions `caps.etaCtor` or `projFnName T j`:
the certificate never looks at a constructor or a projection.  Nor is
the premise derivable from the environment: `EtaFamilyStored` is a
statement about what is *stored* under two name families that an
`indInfo` entry's `caps` record merely *names*, and `EnvWF` relates
the two not at all.  `indBlockCaps` (`Inductives/Modeled.lean:713`)
computes `eta` and `unitlike` by two independent checks, so a
`unitlike`-but-not-`eta` family — whose projection indices install as
elimination *templates* (`projInfo`), not projection functions
(`recInfo`) — is exactly the shape the premise excludes and the
certificate accepts.

`etaFamilyStored_not_derivable` below is that gap, mechanized.

**The wall statement.**  `StructUnitIrrel` is not a consequence of
the frozen `CapsOk` plus the claims.  The fix is one deletion — drop
`ConLeche.EtaFamilyStored env T caps →` from `CapsOk`'s second
conjunct, restoring `CapsOkV`'s keying — which *strengthens* the
field (fewer premises = more obligations) and so cannot weaken any
downstream statement; establishment is unaffected, since `MemberUnitS`
already discharges the unpremised form.  Per the batch protocol the
statement is frozen, so the deletion is NOT taken here: the row stays
in the census, named, for the lane lead. -/

/-- The witnessing capability record: `unitlike` without `eta`, naming
a constructor that is stored nowhere. -/
def unitNoFamilyCaps : IndCaps where
  eta := false
  etaCtor := Name.anonymous.str "ConLecheCapsWall.mk"
  etaParams := 0
  etaFields := 0
  unitlike := true
  unitParams := 0
  ruleK := false

/-- The witnessing environment: one non-reserved `unitlike` former
carrying `unitNoFamilyCaps`. -/
def unitNoFamilyEnv : Env :=
  ⟨[.indInfo ⟨Name.anonymous.str "ConLecheCapsWall.T", [], .sort .zero⟩
      unitNoFamilyCaps]⟩

/-- **The wall, mechanized**: a well-formed environment storing a
non-reserved `unitlike` family for which `EtaFamilyStored` is FALSE.
Everything `structUnitCert`'s inversion can ever hand a consumer holds
here, and the frozen `CapsOk`'s unit half is vacuous. -/
theorem etaFamilyStored_not_derivable :
    ∃ (env : Env) (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      ConLeche.EnvWF env ∧
      env.find? T = some (.indInfo cvT caps) ∧
      caps.unitlike = true ∧
      ConLeche.reservedBasisNames.contains T = false ∧
      ¬ ConLeche.EtaFamilyStored env T caps := by
  refine ⟨unitNoFamilyEnv, Name.anonymous.str "ConLecheCapsWall.T",
    ⟨Name.anonymous.str "ConLecheCapsWall.T", [], .sort .zero⟩,
    unitNoFamilyCaps, ?_, rfl, rfl, by decide, ?_⟩
  · intro c hc
    rcases List.mem_singleton.mp hc with rfl
    exact ⟨rfl, rfl, rfl, rfl, by rintro _ _ _ ⟨⟩,
      by rintro _ _ _ _ ⟨⟩, by rintro _ ⟨⟩,
      ConLeche.IndCapsWF.of_caps (fun _ => rfl) (fun h => nomatch h)⟩
  · rintro ⟨-, ⟨cvC, _, _, hfC⟩, -⟩
    exact nomatch hfC

/-! ## The crossing -/

/-- **`CapsOk` at a fresh value-kind cons** — every `defnInfo`,
`thmInfo` and `axiomInfo` harvest discharges its `caps_ok` obligation
here.  (An `indInfo`/`ctorInfo`/`recInfo` cons may *complete* a family
and so genuinely owes the law; those installs supply it bespoke —
`IndStepPB`'s bill.) -/
theorem capsOk_cons_fresh (mp : EnvModelM V μ env)
    (hprev : CapsOk mp.base2)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none)
    (hntc : ConsCrossEnv env c₀)
    (hnotind : ∀ cv caps, c₀ ≠ .indInfo cv caps)
    (hnotctor : ∀ cv np nf, c₀ ≠ .ctorInfo cv np nf)
    (hnotrec : ∀ cv mI rP rules, c₀ ≠ .recInfo cv mI rP rules)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A) :
    CapsOk m₂ := by
  constructor
  · -- the η half
    intro T cvT caps hf hcape hres hfam φ' us hlen
    obtain ⟨hfE, hfam₀, hnT, hnC, hnP⟩ :=
      etaFamilyStored_descend hnotind hnotctor hnotrec hf hfam
    obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ :=
      hprev.1 T cvT caps hfE hcape hres hfam₀ φ' us hlen
    refine ⟨TVa, ?_, hokTVa, ?_⟩
    · rw [hac]
      exact denoteMeta_cons_mono hfresh
        ((hntc.typeOf hfE).instantiateLevelParams _ _) _ 0
        (constsBound_instType mp.base2.wf
          (ConLeche.Semantics.Env.find?_mem hfE) us) hTVa
    · intro ρ ts rest x hlents hfit hmem
      rw [hac, acvalWith_ne hnT] at hmem
      have hfab : etaFabArgsV
            (fun n => interp V ρ
              (m₂.acval n (Level.substFn φ' cvT.levelParams us)))
            T ts x caps.etaFields
          = etaFabArgsV
            (fun n => interp V ρ
              (mp.base2.acval n (Level.substFn φ' cvT.levelParams us)))
            T ts x caps.etaFields := by
        unfold etaFabArgsV projSpines
        refine congrArg _ (List.map_congr_left fun j hj => ?_)
        dsimp only
        rw [hac, acvalWith_ne (hnP j (List.mem_range.mp hj))]
      rw [hfab, hac, acvalWith_ne hnC]
      exact hlaw ρ ts rest x hlents hfit hmem
  · -- the unit-like half: no fabricated spine, one leaf to move
    -- (and, post-repair, no family premise: the former's freshness
    -- disequality comes from the cons head's non-inductive kind)
    intro T cvT caps hf hcapu hres φ' us hlen
    have hnT : T ≠ c₀.name := by
      intro hh
      subst hh
      have h0 := (ConLeche.Env.find?_cons_self c₀ env).symm.trans hf
      exact hnotind cvT caps (Option.some.inj h0)
    have hfE : env.find? T = some (.indInfo cvT caps) := by
      rw [ConLeche.Env.find?_cons, if_neg (fun hh => hnT hh.symm)] at hf
      exact hf
    obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ :=
      hprev.2 T cvT caps hfE hcapu hres φ' us hlen
    refine ⟨TVa, ?_, hokTVa, ?_⟩
    · rw [hac]
      exact denoteMeta_cons_mono hfresh
        ((hntc.typeOf hfE).instantiateLevelParams _ _) _ 0
        (constsBound_instType mp.base2.wf
          (ConLeche.Semantics.Env.find?_mem hfE) us) hTVa
    · intro ρ ts rest x y hlents hfit hmx hmy
      rw [hac, acvalWith_ne hnT] at hmx hmy
      exact hlaw ρ ts rest x y hlents hfit hmx hmy

end ConLeche.Model
