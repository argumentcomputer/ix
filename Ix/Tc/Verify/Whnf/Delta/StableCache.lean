import Ix.Tc.Verify.Whnf.Delta.TrustedBody

/-!
# Stable trusted delta-cache provenance

TrustedBody proves that one exact trusted definition or theorem body has the Theory
meaning required by delta unfolding.  An unfold-cache entry has a stronger
lifetime, however: it is stored under stable-world authority and may be read
after the trusted Theory environment grows.  This module makes that
persistence obligation explicit and turns the declaration certificate into
the exact `CacheProvenance` consumed by the production cache invariant.

Two facts are intentionally not inferred from the generic instantiation
request:

* `WalkerRequest.Bounds (.instUniv _ _)` is vacuous, so address faithfulness
  and `UInt64` level-size bounds must be supplied by the run's exact delta
  census;
* `WhnfTheory` is not automatically monotone, because a later world may add
  literal and projection obligations.  A stable theory family supplies those
  obligations at every permitted extension.
-/

namespace Ix.Tc

/-- Theory closure at one universe count for every extension of the world in
which a stable cache entry may be interpreted. -/
def StableWhnfTheory (trProj : RawProjRel) (world : VerifyWorld)
    (uvars : Nat) : Prop :=
  ∀ ⦃later : VerifyWorld⦄, world ≤ later →
    WhnfTheory trProj later uvars

namespace StableWhnfTheory

/-- Project the current-world theory from its stable family. -/
theorem current {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    (h : StableWhnfTheory trProj world uvars) :
    WhnfTheory trProj world uvars :=
  h VerifyWorld.LE.rfl

/-- A stable theory family remains stable after advancing its lower world
bound. -/
theorem mono {trProj : RawProjRel} {before after : VerifyWorld} {uvars : Nat}
    (h : StableWhnfTheory trProj before uvars) (hle : before ≤ after) :
    StableWhnfTheory trProj after uvars := by
  intro later hlater
  exact h (VerifyWorld.LE.trans hle hlater)

end StableWhnfTheory

/-- The two non-vacuous resource obligations used by the universe
instantiation proof for one exact body and universe array. -/
structure DeltaInstantiationResources (us : Array (KUniv .anon))
    (body : KExpr .anon) : Prop where
  addrFaithful : ∀ left right,
    KExpr.LevelReach us body left →
    KExpr.LevelReach us body right →
    left.AddrFaithful right
  levelSize : ∀ level,
    KExpr.LevelReach us body level →
    level.size < UInt64.size

namespace TrustedDeltaBody

/-- Invert the structural translation of the concrete constant selected by a
trusted delta certificate.

The translation's name and `VConstant` are not accepted independently:
determinism of `nameOf` and the Theory constant map identifies them with the
certificate's exact `VDefVal`.  Consequently the returned universe arity is
the arity of the registered definition, not merely that of an unrelated
constant found at the same source node. -/
theorem sourceInputs
    {trProj : RawProjRel} {world : VerifyWorld}
    {id : KId .anon} {concrete : KConst .anon}
    {ci : Lean4Lean.VDefVal} {kind : Ix.DefKind}
    {lvls : UInt64} {body : KExpr .anon}
    (h : TrustedDeltaBody trProj world id concrete ci kind lvls body)
    {uvars : Nat} {us : Array (KUniv .anon)} {info : ExprInfo .anon}
    {Delta : KVLCtx} {sourceV : Lean4Lean.VExpr}
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.const id us info) sourceV) :
    sourceV =
        .const ci.name (us.toList.map KUniv.toVLevel) ∧
      (∀ level ∈ us, (KUniv.toVLevel level).WF uvars) ∧
      us.size = ci.uvars := by
  cases hsource with
  | const hname hlookup hus harity =>
      have hnameEq := Option.some.inj (hname.symm.trans h.nameEq)
      subst hnameEq
      have hconstantEq := Option.some.inj (hlookup.symm.trans h.lookup)
      subst hconstantEq
      exact ⟨rfl, hus, harity⟩

/-- The exact body meaning remains available in every future world accepted
by the stable cache authority. -/
theorem futureMeaning
    {trProj : RawProjRel} {world : VerifyWorld}
    {id : KId .anon} {concrete : KConst .anon}
    {ci : Lean4Lean.VDefVal} {kind : Ix.DefKind}
    {lvls : UInt64} {body : KExpr .anon}
    (h : TrustedDeltaBody trProj world id concrete ci kind lvls body)
    {uvars : Nat} (theory : StableWhnfTheory trProj world uvars)
    {us : Array (KUniv .anon)} {info : ExprInfo .anon}
    {result : KExpr .anon}
    (hus : ∀ level ∈ us, (KUniv.toVLevel level).WF uvars)
    (harity : us.size = ci.uvars)
    (hspec : KExpr.instantiateUnivParamsSpec body us = .ok result)
    (resources : DeltaInstantiationResources us body)
    {later : VerifyWorld} (hle : world ≤ later)
    {Delta : KVLCtx} (hDelta : KVLCtx.WF later.venv uvars Delta) :
    WhnfMeaning trProj later uvars Delta (.const id us info) result :=
  (h.mono hle).meaning (theory hle) hus harity hspec
    resources.addrFaithful resources.levelSize hDelta

/-- Construct the collision-robust, stable-world provenance installed by a
cold `unfoldConstValue` run.  This is the declaration-specific replacement
for `UnfoldCacheWriteOracle.write`. -/
theorem unfoldCacheProvenance
    {trProj : RawProjRel} {world : VerifyWorld}
    {id : KId .anon} {concrete : KConst .anon}
    {ci : Lean4Lean.VDefVal} {kind : Ix.DefKind}
    {lvls : UInt64} {body : KExpr .anon}
    (h : TrustedDeltaBody trProj world id concrete ci kind lvls body)
    {uvars : Nat} {fallback : CacheSemantics}
    (theory : StableWhnfTheory trProj world uvars)
    {support : RunSupport}
    (hcollision : support.CollisionFree)
    (hreferences : RecM.TrustedReferences world support)
    {us : Array (KUniv .anon)} {info : ExprInfo .anon}
    {result : KExpr .anon}
    (hhead : support (.const id us info))
    (hresult : support result)
    (hus : ∀ level ∈ us, (KUniv.toVLevel level).WF uvars)
    (harity : us.size = ci.uvars)
    (hspec : KExpr.instantiateUnivParamsSpec body us = .ok result)
    (resources : DeltaInstantiationResources us body) :
    CacheProvenance (unfoldCacheSemantics uvars trProj fallback)
      (CacheAuthority.stable world) support
      (.unfold (.const id us info : KExpr .anon).addr result) := by
  apply CacheProvenance.unfoldOfMeaning hcollision hreferences hhead hresult
  intro later hle Delta hDelta
  exact h.futureMeaning theory hus harity hspec resources hle hDelta

end TrustedDeltaBody

end Ix.Tc
