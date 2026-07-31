import Ix.Tc.Verify.Whnf.Delta.UniverseMonotonicity

/-!
# Exact trusted delta-body semantics

`UnfoldingState` closes the operational state and support behavior of delta unfolding,
but its two remaining semantic inputs are intentionally too broad for final
K1 closure: one can certify an unfold-cache write for an arbitrary supported
head/result pair, and the other can reflect any observed successful delta
run.

This module replaces that shape with a declaration-specific certificate.  A
certificate is tied to one exact immutable catalog entry, its trusted id, the
assigned Theory name and lookup, the concrete body, its typed structural
translation, and the semantic reason that the body may be unfolded:

* an ordinary definition carries its registered Theory equation;
* a theorem carries evidence that its type is a proposition, so unfolding is
  justified by proof irrelevance;
* opaque definitions have no constructor.

The universe-instantiation theorem covers both production paths.  Nonempty
universe arrays use the verified walker quotient; the empty fast path uses
UniverseMonotonicity's universe-count monotonicity because production returns the admitted
body unchanged.  ClosedTranslation then weakens the closed body translation into the
caller's arbitrary mixed context.
-/

namespace Ix.Tc

open Lean4Lean (VDefVal VEnv VExpr VLevel)

/-- The exact definition-shaped catalog fields relevant to delta unfolding.
Keeping this as an indexed proposition lets a certificate retain the complete
catalog entry without storing proof-irrelevant data inside `Prop`. -/
inductive DeltaBodyShape (kind : Ix.DefKind) (lvls : UInt64)
    (body : KExpr .anon) : KConst .anon → Prop where
  | defn
      {name : Mode.anon.F Name}
      {levelParams : Mode.anon.F (Array Name)}
      {safety : Ix.DefinitionSafety}
      {hints : Lean.ReducibilityHints}
      {type : KExpr .anon}
      {leanAll : Mode.anon.F (Array (KId .anon))}
      {block : KId .anon} :
    DeltaBodyShape kind lvls body
      (.defn name levelParams kind safety hints lvls type body leanAll block)

/-- The Theory fact that permits production to unfold one definition-shaped
catalog entry.  There is deliberately no opaque case. -/
inductive DeltaBodyEquation (env : VEnv) (ci : VDefVal) :
    Ix.DefKind → Prop where
  | defn :
    env.defeqs ci.toDefEq →
    DeltaBodyEquation env ci .defn
  | thm :
    env.HasType ci.uvars [] ci.type (.sort .zero) →
    DeltaBodyEquation env ci .thm

namespace DeltaBodyEquation

/-- A delta equation remains available when the trusted Theory environment
grows. -/
theorem mono {before after : VEnv} (hle : before ≤ after)
    {ci : VDefVal} {kind : Ix.DefKind}
    (h : DeltaBodyEquation before ci kind) :
    DeltaBodyEquation after ci kind := by
  cases h with
  | defn hregistered =>
      exact .defn (hle.defeqs hregistered)
  | thm hprop =>
      exact .thm (hprop.mono hle)

end DeltaBodyEquation

/-- Admission-owned semantic certificate for one exact reducible catalog
entry.

The Theory name is `ci.name` throughout.  This is stronger than separately
recording an arbitrary lookup name: the registered equation's left-hand side
is headed by `ci.name`, so allowing a different source name would be
unsound. -/
structure TrustedDeltaBody (trProj : RawProjRel) (world : VerifyWorld)
    (id : KId .anon) (concrete : KConst .anon) (ci : VDefVal)
    (kind : Ix.DefKind) (lvls : UInt64) (body : KExpr .anon) : Prop where
  shape : DeltaBodyShape kind lvls body concrete
  catalog : world.catalog id = some concrete
  trusted : world.trusted id
  nameEq : world.nameOf id.addr = some ci.name
  lookup : world.venv.constants ci.name = some ci.toVConstant
  uvars : lvls.toNat = ci.uvars
  bodyStructural :
    TrKExprS world.venv ci.uvars world.nameOf trProj [] body ci.value
  wf : ci.WF world.venv
  equation : DeltaBodyEquation world.venv ci kind

namespace TrustedDeltaBody

/-- The same exact catalog/body certificate survives trusted-world
extension.  Catalog and address-name assignments are immutable under
`VerifyWorld.LE`; only trusted membership and Theory facts grow. -/
theorem mono {trProj : RawProjRel} {before after : VerifyWorld}
    (hle : before ≤ after)
    {id : KId .anon} {concrete : KConst .anon} {ci : VDefVal}
    {kind : Ix.DefKind} {lvls : UInt64} {body : KExpr .anon}
    (h : TrustedDeltaBody trProj before id concrete ci kind lvls body) :
    TrustedDeltaBody trProj after id concrete ci kind lvls body := by
  refine ⟨h.shape, ?_, hle.trusted h.trusted, ?_,
    hle.venv.constants h.lookup, h.uvars, ?_,
    h.wf.mono hle.venv, h.equation.mono hle.venv⟩
  · rw [← hle.catalog]
    exact h.catalog
  · rw [← hle.nameOf]
    exact h.nameEq
  · simpa only [← hle.nameOf] using h.bodyStructural.mono hle.venv

/-- The list of Theory levels selected by one concrete universe array. -/
private def instantiatedLevels (us : Array (KUniv .anon)) : List VLevel :=
  us.toList.map KUniv.toVLevel

/-- Universe-instantiating a certified closed body yields a quotient
translation to the instantiated Theory body in every caller context.

For the nonempty path this is `TrKExprS.instL` followed by right weakening.
For the empty production fast path, arity forces the admitted body to have
zero universe parameters; UniverseMonotonicity raises that structural derivation to the
caller's universe count before ClosedTranslation weakens it into `Delta`. -/
theorem instantiatedBody
    {trProj : RawProjRel} {world : VerifyWorld}
    {id : KId .anon} {concrete : KConst .anon} {ci : VDefVal}
    {kind : Ix.DefKind} {lvls : UInt64} {body : KExpr .anon}
    (h : TrustedDeltaBody trProj world id concrete ci kind lvls body)
    {uvars : Nat} (theory : WhnfTheory trProj world uvars)
    {us : Array (KUniv .anon)} {result : KExpr .anon}
    (hus : ∀ level ∈ us, (KUniv.toVLevel level).WF uvars)
    (harity : us.size = ci.uvars)
    (hspec : KExpr.instantiateUnivParamsSpec body us = .ok result)
    (hfaithful : ∀ left right,
      KExpr.LevelReach us body left →
      KExpr.LevelReach us body right → left.AddrFaithful right)
    (hsize : ∀ level, KExpr.LevelReach us body level →
      level.size < UInt64.size)
    {Delta : KVLCtx} (hDelta : KVLCtx.WF world.venv uvars Delta) :
    TrKExpr world.venv uvars world.nameOf trProj Delta result
      (ci.value.instL (instantiatedLevels us)) := by
  by_cases hempty : us.isEmpty
  · have husEmpty : us = #[] := Array.empty_of_isEmpty hempty
    subst us
    have hresult : result = body := by
      simpa [KExpr.instantiateUnivParamsSpec] using hspec.symm
    subst result
    have hzero : ci.uvars = 0 := by
      simpa using harity.symm
    have hbody0 :
        TrKExprS world.venv 0 world.nameOf trProj [] body ci.value := by
      simpa only [hzero] using h.bodyStructural
    have hbodyU :
        TrKExprS world.venv uvars world.nameOf trProj [] body ci.value :=
      hbody0.monoU (Nat.zero_le uvars) (by trivial)
    have hbodyDelta :
        TrKExprS world.venv uvars world.nameOf trProj Delta body ci.value := by
      simpa only [KVLCtx.appendOuter] using
        hbodyU.weakRight world.venvWF.ordered theory.literalWF
          theory.projections (by trivial) Delta
    have hwf := h.wf
    change world.venv.HasType ci.uvars [] ci.value ci.type at hwf
    have hwf0 : world.venv.HasType 0 [] ci.value ci.type := by
      simpa only [hzero] using hwf
    have hvalueLevels : ci.value.LevelWF 0 :=
      (hwf0.levelWF (by trivial)).1
    have hinst : ci.value.instL [] = ci.value := by
      simpa [VLevel.params] using hvalueLevels.instL_id
    simpa [instantiatedLevels, hinst] using
      hbodyDelta.trKExpr world.venvWF.ordered theory.literalWF
        theory.projections.wf hDelta
  · have hspec' : KExpr.instUnivSpec body us = .ok result := by
      simpa [KExpr.instantiateUnivParamsSpec, hempty] using hspec
    have hresult :=
      TrKExprS.instL world.venvWF theory.literalWF theory.projections
        hus harity.symm h.bodyStructural (by trivial) hspec'
          hfaithful hsize
    simpa only [KVLCtx.instL, KVLCtx.appendOuter, instantiatedLevels] using
      hresult.weakRight world.venvWF.ordered theory.literalWF
        theory.projections (by trivial) Delta

/-- The concrete constant head has the exact structural Theory translation
selected by a trusted delta-body certificate. -/
private theorem sourceStructural
    {trProj : RawProjRel} {world : VerifyWorld}
    {id : KId .anon} {concrete : KConst .anon} {ci : VDefVal}
    {kind : Ix.DefKind} {lvls : UInt64} {body : KExpr .anon}
    (h : TrustedDeltaBody trProj world id concrete ci kind lvls body)
    {uvars : Nat} {us : Array (KUniv .anon)} {info : ExprInfo .anon}
    (hus : ∀ level ∈ us, (KUniv.toVLevel level).WF uvars)
    (harity : us.size = ci.uvars)
    {Delta : KVLCtx} :
    TrKExprS world.venv uvars world.nameOf trProj Delta
      (.const id us info) (.const ci.name (instantiatedLevels us)) :=
  .const h.nameEq h.lookup hus harity

/-- Exact K1 semantics of unfolding one trusted definition or theorem body.

Ordinary definitions use their registered equation.  Theorem constants are
not registered as reducible Theory equations, so the proof uses the
certificate's proposition-typing fact and Theory proof irrelevance. -/
theorem meaning
    {trProj : RawProjRel} {world : VerifyWorld}
    {id : KId .anon} {concrete : KConst .anon} {ci : VDefVal}
    {kind : Ix.DefKind} {lvls : UInt64} {body : KExpr .anon}
    (h : TrustedDeltaBody trProj world id concrete ci kind lvls body)
    {uvars : Nat} (theory : WhnfTheory trProj world uvars)
    {us : Array (KUniv .anon)} {info : ExprInfo .anon}
    {result : KExpr .anon}
    (hus : ∀ level ∈ us, (KUniv.toVLevel level).WF uvars)
    (harity : us.size = ci.uvars)
    (hspec : KExpr.instantiateUnivParamsSpec body us = .ok result)
    (hfaithful : ∀ left right,
      KExpr.LevelReach us body left →
      KExpr.LevelReach us body right → left.AddrFaithful right)
    (hsize : ∀ level, KExpr.LevelReach us body level →
      level.size < UInt64.size)
    {Delta : KVLCtx} (hDelta : KVLCtx.WF world.venv uvars Delta) :
    WhnfMeaning trProj world uvars Delta (.const id us info) result := by
  let levels := instantiatedLevels us
  have hlevels : ∀ level ∈ levels, level.WF uvars := by
    intro level hlevel
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.1 hlevel
    exact hus source (by simpa [levels, instantiatedLevels] using hsource)
  have hlength : levels.length = ci.uvars := by
    simpa [levels, instantiatedLevels] using harity
  have hsource :
      TrKExprS world.venv uvars world.nameOf trProj Delta
        (.const id us info) (.const ci.name levels) := by
    simpa only [levels] using h.sourceStructural hus harity
  have hresult :
      TrKExpr world.venv uvars world.nameOf trProj Delta result
        (ci.value.instL levels) := by
    simpa only [levels] using
      h.instantiatedBody theory hus harity hspec hfaithful hsize hDelta
  cases h.equation with
  | defn hregistered =>
      have hstep :
          world.venv.IsDefEq uvars Delta.toCtx
            (.const ci.name levels) (ci.value.instL levels)
            (ci.type.instL levels) := by
        simpa [VDefVal.toDefEq, VExpr.instL,
          VLevel.inst_map_id hlength] using
            (VEnv.IsDefEq.extra (Γ := Delta.toCtx)
              hregistered hlevels hlength)
      have hsourceQ :
          TrKExpr world.venv uvars world.nameOf trProj Delta
            (.const id us info) (ci.value.instL levels) :=
        ⟨_, hsource, ⟨_, hstep⟩⟩
      exact WhnfMeaning.ofQuot hDelta hsourceQ hresult
  | thm hprop =>
      obtain ⟨resultV, hresultS, hresultEq⟩ := hresult
      have hsourceType :
          world.venv.HasType uvars Delta.toCtx
            (.const ci.name levels) (ci.type.instL levels) :=
        VEnv.HasType.const h.lookup hlevels hlength
      have hbodyType0 :
          world.venv.HasType uvars []
            (ci.value.instL levels) (ci.type.instL levels) := by
        simpa using h.wf.instL hlevels
      have hbodyType :
          world.venv.HasType uvars Delta.toCtx
            (ci.value.instL levels) (ci.type.instL levels) :=
        hbodyType0.weak0 world.venvWF.ordered
      have hresultType :
          world.venv.HasType uvars Delta.toCtx resultV
            (ci.type.instL levels) :=
        (hresultEq.of_r world.venvWF hDelta.toCtx hbodyType).hasType.1
      have hprop0 :
          world.venv.HasType uvars []
            (ci.type.instL levels) (.sort .zero) := by
        simpa [VExpr.instL, VLevel.inst] using hprop.instL hlevels
      have hpropDelta :
          world.venv.HasType uvars Delta.toCtx
            (ci.type.instL levels) (.sort .zero) :=
        hprop0.weak0 world.venvWF.ordered
      exact ⟨_, _, hsource, hresultS,
        ⟨_, .proofIrrel hpropDelta hsourceType hresultType⟩⟩

end TrustedDeltaBody

end Ix.Tc
