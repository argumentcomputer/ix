import Ix.Tc.Verify.Decl
import Ix.Tc.Verify.Trans
import Lean4Lean.Verify.Typing.Lemmas

/-!
# Concrete Lean4Lean projection adapter

Ix keeps projection translation abstract so the checker proofs do not depend
on one implementation of structure projections.  This module closes that
boundary with Lean4Lean's registered, recursor-encoded `TrProj` relation.

The field mapping is direct:

* `weakN` uses Lean4Lean's general-depth weakening theorem;
* `instN`, `wf`, `uniq`, and `defeqDFC` consume the corresponding fields of
  `TrProj.structuralLaws`;
* `instL` uses the named universe-instantiation theorem, whose statement is
  slightly more general than the bundled compatibility field; and
* `monoU` instantiates with the identity parameter spine and discharges the
  resulting identities from the source context and projection typing data.

Consequently the adapter inherits Lean4Lean's named
`VEnv.WF.registeredStructureHeadInversion` debt through projection uniqueness
and the existing `VEnv.IsDefEqU.forallE_inv_stratified` /
`VEnv.IsDefEqU.sort_inv` debts through context-defeq/unique typing; it
introduces no Ix axiom or pending assumption.
-/

namespace Ix.Tc

open Lean4Lean (OnCtx VEnv VExpr VLevel)

namespace RawProjRel

/-- Lean4Lean's concrete, environment-indexed projection semantics in Ix's
universe-indexed projection slot. -/
abbrev lean4Lean (env : VEnv) :=
  fun uvars ctx structName field major result =>
    Lean4Lean.TrProj env uvars ctx structName field major result

private theorem vlevelWF_mono {before after : Nat}
    (hle : before ≤ after) :
    ∀ {level : VLevel}, level.WF before → level.WF after := by
  intro level hlevel
  induction level with
  | zero => trivial
  | succ level ih => exact ih hlevel
  | max left right ihLeft ihRight =>
      exact ⟨ihLeft hlevel.1, ihRight hlevel.2⟩
  | imax left right ihLeft ihRight =>
      exact ⟨ihLeft hlevel.1, ihRight hlevel.2⟩
  | param index => exact Nat.lt_of_lt_of_le hlevel hle

private theorem context_levelWF {env : VEnv} {uvars : Nat} :
    ∀ {ctx : List VExpr},
      OnCtx ctx (env.IsType uvars) →
        OnCtx ctx (fun _ type => type.LevelWF uvars)
  | [], _ => trivial
  | _ :: _, ⟨hctx, _level, htype⟩ =>
      ⟨context_levelWF hctx,
        (htype.levelWF (context_levelWF hctx)).1⟩

private theorem context_instParams_eq {uvars : Nat} :
    ∀ {ctx : List VExpr},
      OnCtx ctx (fun _ type => type.LevelWF uvars) →
        ctx.map (VExpr.instL (VLevel.params uvars)) = ctx
  | [], _ => rfl
  | type :: ctx, ⟨hctx, htype⟩ => by
      simp only [List.map_cons, context_instParams_eq hctx, htype.instL_id]

/-- A concrete projection remains the same projection when only the available
universe-parameter budget grows.  Lean4Lean supplies universe instantiation;
its typing data proves that instantiating with the original parameter spine is
the identity on the context, major, and computed result. -/
private theorem lean4Lean_monoU
    {env : VEnv} {before after : Nat} {ctx : List VExpr}
    {structName : Lean.Name} {field : Nat} {major result : VExpr}
    (hle : before ≤ after) (hctx : OnCtx ctx (env.IsType before))
    (hproj : Lean4Lean.TrProj env before ctx structName field major result) :
    Lean4Lean.TrProj env after ctx structName field major result := by
  have hctxLevels := context_levelWF hctx
  have hlevels : ∀ level ∈ VLevel.params before, level.WF after := by
    intro level hlevel
    exact vlevelWF_mono hle (VLevel.params_wf hlevel)
  obtain ⟨view, levels, params, hname, htheory⟩ := hproj
  have hmajorWF : VExpr.WF env before ctx major :=
    ⟨_, htheory.majorType⟩
  have hresultWF : VExpr.WF env before ctx result :=
    (show Lean4Lean.TrProj env before ctx structName field major result from
      ⟨view, levels, params, hname, htheory⟩).wf hmajorWF
  have hmajorLevels : major.LevelWF before :=
    (htheory.majorType.levelWF hctxLevels).1
  obtain ⟨resultType, hresultType⟩ := hresultWF
  have hresultLevels : result.LevelWF before :=
    (hresultType.levelWF hctxLevels).1
  have hinst :=
    (show Lean4Lean.TrProj env before ctx structName field major result from
      ⟨view, levels, params, hname, htheory⟩).instL hlevels
  rw [context_instParams_eq hctxLevels, hmajorLevels.instL_id,
    hresultLevels.instL_id] at hinst
  exact hinst

/-- Lean4Lean's concrete projection relation satisfies every Ix projection
capability.  The `uvars` index selects the laws used by ordinary checker
proofs; universe instantiation and monotonicity remain polymorphic because
declaration translation crosses universe counts. -/
theorem lean4Lean_ok (henv : VEnv.WF env) (uvars : Nat) :
    TrProjOK env uvars (lean4Lean env) := by
  let laws := Lean4Lean.TrProj.structuralLaws henv
  refine {
    weakN := ?_
    instN := ?_
    wf := ?_
    uniq := ?_
    defeqDFC := ?_
    instL := ?_
    monoU := ?_ }
  · intro Γ Γ' n k s i e e' hlift hproj
    exact Lean4Lean.TrProj.weakN henv.ordered hlift hproj
  · intro Γ₀ e₀ A₀ k Γ₁ Γ s i e e' htype hinst hproj
    exact laws.termSubstitution htype hinst hproj
  · intro Γ s i e e' hproj hwf
    exact laws.wellFormed hproj hwf
  · intro Γ₁ Γ₂ s i e₁ e₂ e₁' e₂' hctx hproj₁ hproj₂ hdefeq
    exact laws.unique hctx hproj₁ hproj₂ hdefeq
  · intro Γ₁ Γ₂ s i e₁ e₂ e' hctx hdefeq hproj
    exact laws.contextDefEq hctx hdefeq hproj
  · intro U U' levels Γ s i e e' hlevels hproj
    exact hproj.instL hlevels
  · intro U U' Γ s i e e' hle hctx hproj
    exact lean4Lean_monoU hle hctx hproj

end RawProjRel
end Ix.Tc
