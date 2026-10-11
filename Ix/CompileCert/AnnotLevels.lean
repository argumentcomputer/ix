import Ix.CompileCert.AnnotLiterals
import IxC.Kernel.Model.Levels

/-! Reading parameter locality without a source EnvModel. The proof follows
Kernel.Model.denoteMeta_params_ext, using the already proved bare
AcvalParamsAt literal lemmas instead of assuming the source carrier that this
certification layer must construct. No Kernel export or axiom is added. -/
namespace Ix.CompileCert
open Kernel Kernel.Model Kernel.Semantics Kernel.Verify

theorem denoteMeta_params_at {env : Kernel.Env}
    {acval : Kernel.Name → (Kernel.Name → Nat) → AnnotTerm}
    (hp : AcvalParamsAt env acval)
    {ps : List Kernel.Name} {φ₁ φ₂ : Kernel.Name → Nat}
    (hφ : ∀ p ∈ ps, φ₁ p = φ₂ p) :
    ∀ (d : Nat) (e : Kernel.Expr), e.allLevelParamsDefined ps = true →
      denoteMeta acval env φ₁ d e = denoteMeta acval env φ₂ d e := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u =>
    intro hd
    rw [denoteMeta, denoteMeta,
      Kernel.Level.eval_ext (by simpa [Kernel.Expr.allLevelParamsDefined] using hd) hφ]
  | case2 d idx ty => intro _; rw [denoteMeta, denoteMeta]
  | case3 d n us ci h1 h2 =>
    intro hd
    rw [denoteMeta, denoteMeta, h1]
    dsimp only
    rw [ite_eq_left h2, ite_eq_left h2]
    refine congrArg _ (hp n ci h1 _ _ fun p hpm => ?_)
    refine Kernel.Level.substFn_ext hφ ?_ h2 p hpm
    intro u hu
    simp only [Kernel.Expr.allLevelParamsDefined, List.all_eq_true] at hd
    exact hd u hu
  | case4 d n us ci h1 h2 =>
    intro _
    rw [denoteMeta, denoteMeta, h1]
    dsimp only
    rw [ite_eq_right h2, ite_eq_right h2]
  | case5 d n us h1 => intro _; rw [denoteMeta, denoteMeta, h1]
  | case6 d ty body mb ihty ihbody =>
    intro hd
    simp only [Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    have hpw : pwBit φ₁ mb.pw = pwBit φ₂ mb.pw := by
      unfold pwBit
      rw [Ix.Kernel.PropWhen.holds_ext hd.2 hφ]
    rw [denoteMeta, denoteMeta, ← ihty hd.1.1,
      ← ihbody (Ix.Kernel.Expr.allLevelParamsDefined_instantiate1 hd.1.1 0
        hd.1.2)]
    simp only [hpw]
  | case7 d ty body mb ihty ihbody =>
    intro hd
    simp only [Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    have hpw : pwBit φ₁ mb.pw = pwBit φ₂ mb.pw := by
      unfold pwBit
      rw [Ix.Kernel.PropWhen.holds_ext hd.2 hφ]
    rw [denoteMeta, denoteMeta, ← ihty hd.1.1,
      ← ihbody (Ix.Kernel.Expr.allLevelParamsDefined_instantiate1 hd.1.1 0
        hd.1.2)]
    simp only [hpw]
  | case8 d fe a ihf iha =>
    intro hd
    simp only [Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    rw [denoteMeta, denoteMeta, ← ihf hd.1, ← iha hd.2]
  | case9 d ty val body =>
    intro _
    rw [denoteMeta, denoteMeta]
  | case10 d sn i e ihe =>
    intro hd
    rw [denoteMeta, denoteMeta,
      ← ihe (by simpa [Kernel.Expr.allLevelParamsDefined] using hd)]
  | case11 d k hsup =>
    intro _
    rw [denoteMeta, denoteMeta, ite_eq_left hsup, ite_eq_left hsup]
    obtain ⟨ez, es⟩ := acvalAt_natPair hp hsup
      (Kernel.Level.substFn φ₁ [] []) (Kernel.Level.substFn φ₂ [] [])
    rw [ez, es]
  | case12 d k hsup =>
    intro _
    rw [denoteMeta, denoteMeta, ite_eq_right hsup, ite_eq_right hsup]
  | case13 d s hsup =>
    intro _
    rw [denoteMeta, denoteMeta, ite_eq_left hsup, ite_eq_left hsup]
    have hg := hsup
    simp only [Ix.Kernel.strLitSupported, Bool.and_eq_true] at hg
    obtain ⟨⟨⟨⟨⟨⟨⟨h0, -⟩, h2⟩, -⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hg
    obtain ⟨ez, es⟩ := acvalAt_natPair hp h0
      (Kernel.Level.substFn φ₁ [] []) (Kernel.Level.substFn φ₂ [] [])
    have esol := acvalAt_scalar hp stringOfListName stringOfListTyOk h2 rfl
      (by intro ci hh
          simp only [stringOfListTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Kernel.Level.substFn φ₁ [] []) (Kernel.Level.substFn φ₂ [] [])
    have echar := acvalAt_scalar hp charName charTyOk h6 rfl
      (by intro ci hh
          simp only [charTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Kernel.Level.substFn φ₁ [] []) (Kernel.Level.substFn φ₂ [] [])
    have eofn := acvalAt_scalar hp charOfNatName charOfNatTyOk h7 rfl
      (by intro ci hh
          simp only [charOfNatTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Kernel.Level.substFn φ₁ [] []) (Kernel.Level.substFn φ₂ [] [])
    have enil := acvalAt_one hp listNilName listNilTyOk h4 rfl
      (by intro ci hh
          simp only [listNilTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      φ₁ φ₂
    have econs := acvalAt_one hp listConsName listConsTyOk h5 rfl
      (by intro ci hh
          simp only [listConsTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      φ₁ φ₂
    rw [ez, es, esol, echar, eofn, enil, econs]
  | case14 d s hsup =>
    intro _
    rw [denoteMeta, denoteMeta, ite_eq_right hsup, ite_eq_right hsup]
  | case15 d x hxs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _
    cases x with
    | bvar i => rw [denoteMeta.eq_def, denoteMeta.eq_def]
    | sort u => exact absurd rfl (hxs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n vs => exact absurd rfl (hc n vs)
    | forallE ty b mb => exact absurd rfl (hpi ty b mb)
    | lam ty b mb => exact absurd rfl (hlam ty b mb)
    | app fe a => exact absurd rfl (happ fe a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal k => exact absurd rfl (hnat k)
      | strVal s => exact absurd rfl (hstr s)

/-- Member-level checks produce equal annotation readings at the original
source assignment. Only the actual member telescope is recovered; unrelated
ambient parameters need not agree. This uses no source EnvModel. -/
theorem checkInstalledMemberExpr_annotated_reading {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (targetModel : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (support : checkLiteralSupport sourceEnv targetEnv = true)
    {name : Kernel.Name} {sourceEntry : Kernel.ConstantInfo}
    (lookup : sourceEnv.find? name = some sourceEntry)
    {source target : Kernel.Expr}
    (checked : checkInstalledMemberExpr sourceEnv targetEnv names name source target = some true)
    (sourceLevels : Kernel.Name → Nat) (depth : Nat) :
    denoteMeta ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations targetModel.internal.base2.acval)
      sourceEnv sourceLevels depth source =
    denoteMeta targetModel.internal.base2.acval targetEnv
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels name sourceLevels) depth target := by
  obtain ⟨targetEntry, targetLookup, sourceUnique, targetUnique, sameArity⟩ :=
    association name sourceEntry lookup
  simp only [checkInstalledMemberExpr, lookup, targetLookup] at checked
  split at checked
  next bounded =>
    have image := checkInstalledExpr_annotated targetModel association _
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels name sourceLevels) support checked depth
    refine (denoteMeta_params_at ?_ ?_ depth source bounded).trans image.reading
    · intro constant info present first second agree
      exact PullbackMap.annotations_params targetModel association present first second agree
    · intro parameter present
      simp only [PullbackMap.fromEnvs, lookup, targetLookup]
      exact (UniverseImage.telescope_recovery sourceLevels sourceUnique targetUnique sameArity parameter present).symm
  next => contradiction

open Kernel.SetTheory in
/-- The actual all-row type check establishes the three strong-model type
fields under target-derived annotations, at every original source valuation.
There is no per-member annotation-image or source-model premise. -/
theorem checkInstalledTypes_annotated {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (support : checkLiteralSupport sourceEnv targetEnv = true)
    (checked : checkInstalledTypes sourceEnv targetEnv names = true)
    (sourceEntry : Kernel.ConstantInfo) (present : sourceEntry ∈ sourceEnv.consts)
    (levels : Kernel.Name → Nat) :
    ∃ annotation,
      denoteMeta ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval)
        sourceEnv levels 0 sourceEntry.toConstantVal.type = some annotation ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ annotation) ∧
      (∀ ρ : Nat → V, interp V ρ
        ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval
          sourceEntry.name levels) ∈ˢ interp V ρ annotation) := by
  obtain ⟨sourceLookup, targetEntry, targetLookup, comparison⟩ := checkInstalledTypes_member checked present
  have member := Kernel.Semantics.Env.find?_mem targetLookup
  obtain ⟨annotation, reading⟩ := target.internal.type_reads targetEntry member
    ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels sourceEntry.name levels)
  have transferred := checkInstalledMemberExpr_annotated_reading target association support
    sourceLookup comparison levels 0
  refine ⟨annotation, transferred.trans reading,
    target.internal.type_wellDenotedV targetEntry member _ annotation reading, ?_⟩
  intro ρ
  have membership := target.internal.mem_type targetEntry member _ annotation reading ρ
  have targetName := Kernel.Semantics.Env.find?_name targetLookup
  simpa only [PullbackMap.annotations, PullbackMap.fromEnvs, targetName] using membership

/-- The checked actual definition-body association supplies the source
`AcvalDefnInst` equation under the same pulled annotation carrier. This is
only for installed definitions; opaque/theorem checking bodies do not become
transparent value equations. -/
theorem checkInstalledDefinitions_annotated {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (support : checkLiteralSupport sourceEnv targetEnv = true)
    (checked : checkInstalledDefinitions sourceEnv targetEnv names = true)
    (levels : Kernel.Name → Nat) (header : Kernel.ConstantVal) (value : Kernel.Expr)
    (present : ∃ hint : Kernel.ReducibilityHint,
      Kernel.ConstantInfo.defnInfo header value hint ∈ sourceEnv.consts) :
    denoteMeta ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval)
      sourceEnv levels 0 value =
    some ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval
      header.name levels) := by
  obtain ⟨hint, member⟩ := present
  obtain ⟨sourceLookup, targetHeader, targetValue, targetHint, targetLookup, comparison⟩ :=
    checkInstalledDefinitions_member checked member
  have reading := target.internal.defn_reads
    ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels header.name levels)
    targetHeader targetValue ⟨targetHint, Kernel.Semantics.Env.find?_mem targetLookup⟩
  have transferred := checkInstalledMemberExpr_annotated_reading target association support
    sourceLookup comparison levels 0
  have targetName := Kernel.Semantics.Env.find?_name targetLookup
  simpa only [Kernel.ConstantInfo.name, PullbackMap.annotations, PullbackMap.fromEnvs] using
    transferred.trans (reading.trans (congrArg some (congrArg
      (fun name => target.internal.base2.acval name
        ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels header.name levels)) targetName)))

end Ix.CompileCert
