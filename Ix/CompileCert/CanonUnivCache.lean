import Ix.CompileCert.CanonUnivEmit
import Ix.CompileCert.RawRun
import Std.Data.HashMap.Lemmas

/-! # The compiler's canonical-universe memo

`Ix.CompileM.canonUnivCached` memoizes `Ixon.canonUniv` per block in
`BlockState.canonUnivCache`, keyed by the positional universe itself
(structural equality). A hit returns exactly the canonicalizer's output, not
merely an equivalent universe (`CanonCacheExact`); an empty memo establishes
that, and every run keeps it. So the memo computes `canonUniv`
(`canonUnivCached_correct`), changes nothing but itself, and preserves the
value of the universe under every valuation (`canonUnivCached_eval`, from
`CanonUnivEmit.canonUniv_eval`).

`compileUniv_frame`: the raw universe compiler changes only its own memo
`univCache`, failing runs included, so it keeps the canonical memo and every
table. Its value theorems need a cache whose hits are confirmed structurally
(CQ2.8); they are not stated here. -/

namespace Ix.CompileCert.CanonUnivCache

open Ix.CompileM

/-- A canonical-memo hit is the exact producer output. -/
def CanonCacheExact (state : BlockState) : Prop :=
  ∀ source value, state.canonUnivCache.get? source = some value → value = Ixon.canonUniv source

theorem canonCache_empty (state : BlockState) : CanonCacheExact { state with canonUnivCache := {} } := by
  intro source value impossible
  simp at impossible

theorem canonCache_insert {state : BlockState} (prior : CanonCacheExact state) (source : Ixon.Univ) :
    CanonCacheExact { state with canonUnivCache := state.canonUnivCache.insert source (Ixon.canonUniv source) } := by
  intro query value found
  change (state.canonUnivCache.insert source (Ixon.canonUniv source))[query]? = some value at found
  rw [Std.HashMap.getElem?_insert] at found
  split at found
  · rename_i same
    have same : source = query := beq_iff_eq.mp same
    subst query
    exact (Option.some.inj found).symm
  · exact prior query value found

def withoutCanonCache (state : BlockState) : BlockState := { state with canonUnivCache := {} }

theorem canonUnivCached_run (source : Ixon.Univ) (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun (canonUnivCached source) context state =
      match state.canonUnivCache.get? source with
      | some value => (.ok value, state)
      | none => (.ok (Ixon.canonUniv source),
          { state with canonUnivCache := state.canonUnivCache.insert source (Ixon.canonUniv source) }) := by
  unfold canonUnivCached
  simp only [rawRun_bind, rawRun_get]
  cases state.canonUnivCache.get? source <;> simp only [rawRun_bind, rawRun_modify, rawRun_pure]

/-- The memoized canonicalizer returns `canonUniv`, keeps the memo exact,
and changes nothing else. -/
theorem canonUnivCached_correct (source : Ixon.Univ) (context : CompileEnv × BlockEnv)
    (before : BlockState) (valid : CanonCacheExact before) :
    ∃ after, rawRun (canonUnivCached source) context before = (.ok (Ixon.canonUniv source), after) ∧
      CanonCacheExact after ∧ withoutCanonCache after = withoutCanonCache before := by
  rw [canonUnivCached_run]
  cases found : before.canonUnivCache.get? source with
  | none => exact ⟨_, rfl, canonCache_insert valid source, rfl⟩
  | some value =>
    rw [valid source value found]
    exact ⟨before, rfl, valid, rfl⟩

/-- The memoized canonicalizer preserves the value of the universe under
every valuation. -/
theorem canonUnivCached_eval (source : Ixon.Univ) (context : CompileEnv × BlockEnv)
    (before : BlockState) (valid : CanonCacheExact before) (ρ : UInt64 → Nat) :
    ∃ value after, rawRun (canonUnivCached source) context before = (.ok value, after) ∧
      CanonCacheExact after ∧ univEval ρ value = univEval ρ source := by
  obtain ⟨after, ran, sound, _⟩ := canonUnivCached_correct source context before valid
  exact ⟨Ixon.canonUniv source, after, ran, sound, CanonUnivEmit.canonUniv_eval ρ source⟩

def withoutUnivCache (state : BlockState) : BlockState := { state with univCache := {} }

/-- Raw universe compilation can change only its memo, including on errors.
In particular it preserves the canonical memo and every table. -/
theorem compileUniv_frame (source : Ix.Level) : Preserves withoutUnivCache (compileUniv source) := by
  induction source <;> rw [compileUniv]
  all_goals
    with_reducible repeat' first
      | assumption
      | exact Preserves.pure withoutUnivCache _
      | exact Preserves.throw withoutUnivCache _
      | exact Preserves.get withoutUnivCache
      | exact Preserves.read withoutUnivCache
      | refine Preserves.bind ?_ (fun _ => ?_)
      | apply Preserves.modify; intro before; simp only [withoutUnivCache, BlockState.cacheUniv]
      | dsimp only
      | split

end Ix.CompileCert.CanonUnivCache
