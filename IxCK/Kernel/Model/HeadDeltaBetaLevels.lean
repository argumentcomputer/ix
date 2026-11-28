module

public import IxCK.Kernel.Model.HeadDeltaBeta
public import IxCK.Kernel.Model.LevelRenKit

@[expose] public section

/-!
# Head traces under an instantiation of level parameters

A head step of `HeadDeltaBeta` is kept by `Expr.instantiateLevelParams`: a definition unfolded at
levels `us` unfolds at the instantiated levels to the instantiated value, a beta step
instantiates its body and its argument, and a step of an application's function is a step of
the instantiated function. So a trace from `e` to `r` gives a trace from the instance of `e` to
the instance of `r`, for every instantiation, not only for a renaming of parameters.

The one hypothesis is that every stored definition's value mentions only the level parameters
of its own constant (`DefnLevelsClosed`). It is the definition clause of `LvStore`, and of
`EnvWF`. Level instantiation here is `Level.subst`, which rebuilds no `max` or `imax`: the
statement is an equality of terms, with no level equivalence involved.
-/

namespace Ix.Kernel.HeadDeltaBeta

open Ix.Kernel.LevelRen (inst_instantiate1 inst_comp inst_getAppFn_const)

/-- Every stored definition's value mentions only its own constant's level parameters. -/
def DefnLevelsClosed (env : Env md) : Prop :=
  ∀ (n : Key md) (cv : ConstantVal md) (value : Expr md) (hint : ReducibilityHint),
    env.find? n = some (.defnInfo cv value hint) →
      value.allLevelParamsDefined cv.levelParams = true

/-- The store's level clause gives the definition clause. -/
theorem DefnLevelsClosed.of_lvStore {env : Env md} (h : LvStore env) : DefnLevelsClosed env :=
  fun _ _ _ _ hf => h.defn hf

/-- Syntactic well-formedness of the environment gives the definition clause. -/
theorem DefnLevelsClosed.of_envWF {env : Env md} (h : EnvWF env) : DefnLevelsClosed env := by
  intro n cv value hint hf
  have hmem : ConstantInfo.defnInfo cv value hint ∈ env.consts := by
    unfold Env.find? at hf
    exact List.mem_of_find?_eq_some hf
  exact ((h _ hmem).2.2.2.2.1 cv value hint rfl).2.1

/-- Unfolding a definition commutes with level instantiation. -/
theorem unfoldDefinition_instantiateLevelParams {env : Env md} (hdef : DefnLevelsClosed env)
    (ks : List LevelParam) (ws : List Level) {e e' : Expr md}
    (hu : unfoldDefinition env e = some e') :
    unfoldDefinition env (e.instantiateLevelParams ks ws) =
      some (e'.instantiateLevelParams ks ws) := by
  unfold unfoldDefinition at hu ⊢
  split at hu
  · rename_i n us hfn
    cases hf : env.find? n with
    | none => rw [hf] at hu; exact nomatch hu
    | some c =>
      rw [hf] at hu
      cases c with
      | defnInfo cv value hint =>
        dsimp only at hu
        split at hu
        · next hlen =>
          obtain rfl := Option.some.inj hu
          rw [inst_getAppFn_const ks ws hfn]
          dsimp only
          rw [hf]
          dsimp only
          have hlen' : (us.map (Level.subst ks ws)).length = cv.levelParams.length := by
            rw [List.length_map]; exact hlen
          rw [if_pos hlen', instantiateLevelParams_mkAppN,
            inst_comp hlen (hdef n cv value hint hf), Expr.getAppArgs_instantiateLevelParams]
        · exact nomatch hu
      | _ => exact nomatch hu
  · exact nomatch hu

/-- A head step is kept by level instantiation. -/
theorem Step.instantiateLevelParams {env : Env md} (hdef : DefnLevelsClosed env)
    (ks : List LevelParam) (ws : List Level) {e r : Expr md} (h : Step env e r) :
    Step env (e.instantiateLevelParams ks ws) (r.instantiateLevelParams ks ws) := by
  induction h with
  | @delta n us _ hd =>
    have hd' := unfoldDefinition_instantiateLevelParams hdef ks ws hd
    exact Step.delta (n := n) (us := us.map (Level.subst ks ws)) hd'
  | @beta ty body a mb =>
    rw [inst_instantiate1 ks ws a body 0]
    exact Step.beta (ty := ty.instantiateLevelParams ks ws)
      (body := body.instantiateLevelParams ks ws) (a := a.instantiateLevelParams ks ws)
      (mb := { mb with pw := Level.substPW ks ws mb.pw })
  | @appFn _ _ a _ ih =>
    exact Step.appFn (a := a.instantiateLevelParams ks ws) ih

/-- A head trace is kept by level instantiation. -/
theorem Trace.instantiateLevelParams {env : Env md} (hdef : DefnLevelsClosed env)
    (ks : List LevelParam) (ws : List Level) {e r : Expr md} (h : Trace env e r) :
    Trace env (e.instantiateLevelParams ks ws) (r.instantiateLevelParams ks ws) := by
  induction h with
  | refl => exact Trace.refl
  | cons hs _ ih => exact Trace.cons (Step.instantiateLevelParams hdef ks ws hs) ih

/-- A head trace can run beneath a fixed application argument. -/
theorem Trace.appFn {env : Env md} {e r : Expr md} (h : Trace env e r) (a : Expr md) :
    Trace env (.app e a) (.app r a) := by
  induction h with
  | refl => exact Trace.refl
  | cons hs _ ih => exact Trace.cons (Step.appFn hs) ih

end Ix.Kernel.HeadDeltaBeta
