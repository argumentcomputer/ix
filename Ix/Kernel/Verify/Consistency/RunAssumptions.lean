/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Driver
import Ix.Kernel.Verify.Support
import Ix.Kernel.Verify.Consistency.ConversionRecipe
import Ix.Kernel.Verify.Consistency.SourceOwnershipCheck
import Ix.Kernel.Verify.Consistency.SourceAgreement

/-!
# Run-level assumptions

One record collects the hypotheses that the refinement lemmas currently take
one at a time: the finite source ownership check, hash verification, and
collision freedom and arithmetic bounds over the finite syntax inventory of a
run. The inventory is an explicit parameter; the final theorem instantiates it
with the actual expressions and universes reached by `checkEnvAnon`. Every
consumer needs only membership in that inventory, so no injectivity of content
addresses beyond the inventory is assumed. Context-digest collision freedom has
no consumer in this library yet and is deliberately not recorded here.
-/

namespace Ix.Kernel.Consistency

/-- The finite syntax inventory of one run: every expression and universe term
the walkers key, intern, compare, or construct, and the additive walker budget
(binder depth plus simultaneous-argument count) of any walker call. -/
structure RunDomain where
  expressions : List (KExpr .anon)
  universes : List (KUniv .anon)
  slack : Nat

/-- Run-level hypotheses. Each field names the lemma family consuming it. -/
structure RunAssumptions (source : Ixon.Env) (cfg : CheckCfg) (domain : RunDomain) : Prop where
  /-- Finite source ownership: `SourceOwnership.ofCheck`, `OwnedLazySupport.ofCheckedSource`,
  `InferenceStateInvariant.ofCheckedSource`, `SourceCacheInvariant.ofCheckedSource`. -/
  checked : sourceOwnershipCheck source = true
  /-- Hash verification on: identifies the driver's initial state with
  `TcState.newLazyAnon source`, whose loader is the one named by
  `InferenceStateInvariant.installed` and `VerifiedLazySupport.installed`. -/
  verify : cfg.verifyHashes = true
  /-- Expression collision freedom over the inventory: every `faithful` field
  (`BinderOpeningData`, `BinderOpeningSupport`, `ApplicationSubstitutionData`,
  `LambdaClosingData`, `ConstantInstantiationData`, `ConversionData`), the cache
  key data (`InferenceCacheHistory.KeyData`, `BetaCacheHistory.KeyData`,
  `SourceCacheKeyData`), `RunSupport.CollisionFree.expr`, and pairwise
  `KExpr.AddrFaithful` at hash comparisons. -/
  expressions : KExpr.CollisionFree (· ∈ domain.expressions)
  /-- Universe collision freedom: `ConversionData.universes`,
  `RunSupport.CollisionFree.univ`, and pairwise `KUniv.AddrFaithful`. -/
  universes : KUniv.CollisionFree (· ∈ domain.universes)
  /-- Walker size bounds: `BinderOpeningData.bound`, `ApplicationSubstitutionData`
  bounds, `LambdaClosingData.bound`, and the lifting/substitution specifications
  (`instantiateRev_spec`, `subst_spec`, simultaneous substitution). -/
  sizes : ∀ term ∈ domain.expressions, term.size + domain.slack < UInt64.size
  /-- Universe size bounds: universe construction and instantiation walkers
  (`InstUniv`, `Level`, and the level bounds of `SynthesisSupport`). -/
  levels : ∀ level ∈ domain.universes, level.size < UInt64.size

namespace RunAssumptions

variable {source : Ixon.Env} {cfg : CheckCfg} {domain : RunDomain}
  (assumptions : RunAssumptions source cfg domain)
include assumptions

theorem ownership : SourceOwnership source := .ofCheck assumptions.checked

/-- The driver's initial checker is the verified lazy state. -/
theorem initialState : TcState.newLazyAnon source cfg.verifyHashes = TcState.newLazyAnon source := by
  rw [assumptions.verify]

theorem initialLoopState :
    (initialAnonCheckLoopState source cfg).checker = TcState.newLazyAnon source :=
  assumptions.initialState

/-- Any support drawn from the inventory is collision free. -/
theorem collisionFree {support : KExpr .anon → Prop}
    (covered : ∀ term, support term → term ∈ domain.expressions) : KExpr.CollisionFree support :=
  assumptions.expressions.mono covered

theorem keyCollisionFree {support : KExpr .anon → Prop}
    (covered : ∀ term, support term → term ∈ domain.expressions) : KExpr.KeyCollisionFree support :=
  KExpr.keyCollisionFree_anon.mpr (assumptions.collisionFree covered)

theorem addrFaithful {left right : KExpr .anon} (leftMember : left ∈ domain.expressions)
    (rightMember : right ∈ domain.expressions) : left.AddrFaithful right :=
  assumptions.expressions.addrFaithful leftMember rightMember

theorem universeCollisionFree {support : KUniv .anon → Prop}
    (covered : ∀ level, support level → level ∈ domain.universes) : KUniv.CollisionFree support :=
  assumptions.universes.mono covered

theorem universeAddrFaithful {left right : KUniv .anon} (leftMember : left ∈ domain.universes)
    (rightMember : right ∈ domain.universes) : left.AddrFaithful right :=
  assumptions.universes.addrFaithful leftMember rightMember

/-- The validation run support of `Production.lean` is covered by the inventory. -/
theorem supportCollisionFree (support : RunSupport)
    (exprs : ∀ term, support term → term ∈ domain.expressions)
    (univs : ∀ level, support.univ level → level ∈ domain.universes) : support.CollisionFree :=
  ⟨assumptions.collisionFree exprs, assumptions.universeCollisionFree univs⟩

/-- Source conversion data at a table whose support and candidates are in the inventory. -/
theorem conversionData {α : Type} (recipe : ConversionRecipe α) (table : InternTable .anon)
    (exprs : ∀ term, table.ExprSupport term → term ∈ domain.expressions)
    (recipeExprs : ∀ term ∈ recipe.exprs, term ∈ domain.expressions)
    (univs : ∀ level, table.UnivSupport level → level ∈ domain.universes)
    (recipeUnivs : ∀ level ∈ recipe.univs, level ∈ domain.universes) :
    ConversionData recipe table :=
  ⟨assumptions.collisionFree fun _ h => h.elim (exprs _) (recipeExprs _),
    assumptions.universeCollisionFree fun _ h => h.elim (univs _) (recipeUnivs _)⟩

/-- Lookup data for every standalone whose predicted conversion candidates are in the inventory. -/
theorem standaloneConversionData (addr : Address) (env : AnonEnv)
    (exprs : ∀ term, env.intern.ExprSupport term → term ∈ domain.expressions)
    (univs : ∀ level, env.intern.UnivSupport level → level ∈ domain.universes)
    (recipeExprs : ∀ constant, getConstVerified source addr true = .ok (some constant) →
      ∀ term ∈ (ConversionRecipe.standalone source addr constant).exprs, term ∈ domain.expressions)
    (recipeUnivs : ∀ constant, getConstVerified source addr true = .ok (some constant) →
      ∀ level ∈ (ConversionRecipe.standalone source addr constant).univs, level ∈ domain.universes) :
    StandaloneConversionData source addr env := by
  intro constant verified _
  exact assumptions.conversionData _ _ exprs (recipeExprs constant verified) univs
    (recipeUnivs constant verified)

/-- A walker bound whose additive budget is within the run's slack. -/
theorem bound {term : KExpr .anon} (member : term ∈ domain.expressions) {extra : Nat}
    (budget : extra ≤ domain.slack) : term.size + extra < UInt64.size :=
  Nat.lt_of_le_of_lt (Nat.add_le_add_left budget _) (assumptions.sizes term member)

end RunAssumptions

end Ix.Kernel.Consistency
