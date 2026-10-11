import Ix.CompileCert.Pj.MotiveChoice
import Ix.CompileCert.Pj.RecTeleSyntax

/-! Selection of the complete motive family in the recursor's actual telescope. -/

namespace Ix.CompileCert.Pj

open Kernel.SetTheory Kernel.SetModel
open Ix.CompileCert (pushArguments)

theorem RecRd.motive_at_split (R : RecRd)
    {before after : List (Kernel.Expr × Kernel.BinderMeta)}
    {t : Kernel.Expr} {bm : Kernel.BinderMeta}
    (split : R.motiveBinders = before ++ (t, bm) :: after) :
    R.motives.getD before.length default ∈ R.motives ∧
      t = ((R.motives.getD before.length default).type R.np).liftLooseBVars
        before.length 0 := by
  have bound : before.length < R.motives.length := by
    have lengths := congrArg List.length split
    simp only [RecRd.motiveBinders, List.length_mapIdx, List.length_append,
      List.length_cons] at lengths
    omega
  have selected : R.motives.getD before.length default = R.motives[before.length] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound,
      Option.getD_some]
  have entry : R.motiveBinders[before.length]? = some (t, bm) := by
    rw [split, List.getElem?_append_right (Nat.le_refl _)]
    simp
  have actual : R.motiveBinders[before.length]? =
      some (((R.motives[before.length]).type R.np).liftLooseBVars before.length 0,
        (R.motives[before.length]).binderMeta) := by
    simp only [RecRd.motiveBinders, List.getElem?_mapIdx,
      List.getElem?_eq_getElem bound, Option.map_some]
  refine ⟨?_, ?_⟩
  · rw [selected]
    exact List.getElem_mem bound
  · rw [selected]
    exact (congrArg Prod.fst (Option.some.inj (actual.symm.trans entry))).symm

universe u

variable {V : Type u} [Kernel.SetTheory V]
  {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat}

/-- Choose every motive in its dependent binder domain at the original universe
assignment. Each chosen motive denotes its requested predicate on all typed
index/major tuples; no replacement universe or zero-sort premise is used. -/
theorem RecRd.choose_motives {r : Kernel.Name} {R : RecRd}
    (checked : R.Check env r) (ρ : Nat → V) {b : Kernel.Expr} {T : V}
    (typeRead : Kernel.Denotes cval env φ ρ (piJoin R.motiveBinders b) T)
    (predicate : Nat → List V → Prop) :
    ∃ motives, TeleTyped cval env φ ρ (R.motiveBinders.map Prod.fst) motives ∧
      motives.length = R.nm ∧
      ∀ j (bound : j < motives.length) arguments,
        TeleTyped cval env φ ρ
          (((R.motives.getD j default).tele R.np).map Prod.fst) arguments →
        arguments.foldl app motives[j] = truthVal (predicate j arguments) := by
  let Q (selected : List V) (M : V) : Prop := ∀ arguments,
    TeleTyped cval env φ ρ
      (((R.motives.getD selected.length default).tele R.np).map Prod.fst) arguments →
    arguments.foldl app M = truthVal (predicate selected.length arguments)
  have choose : ∀ before after t bm,
      R.motiveBinders = before ++ (t, bm) :: after →
      ∀ xs, TeleTyped cval env φ ρ (before.map Prod.fst) xs →
      ∀ A, Kernel.Denotes cval env φ (pushArguments ρ xs) t A →
      ∃ M, M ∈ˢ A ∧ Q xs M := by
    intro before after t bm split xs typed A domain
    obtain ⟨member, binder⟩ := R.motive_at_split split
    have length : xs.length = before.length := by
      simpa only [List.length_map] using typed.length
    have lifted : Kernel.Denotes cval env φ (pushArguments ρ xs)
        (((R.motives.getD before.length default).type R.np).liftLooseBVars
          xs.length 0) A := by
      simpa only [binder, length] using domain
    have picked := motive_value_choice R.np (R.motives.getD before.length default)
      (RecRd.motive_graph checked member) ρ xs lifted (predicate xs.length)
    simpa only [Q, length] using picked
  obtain ⟨motives, typed, properties⟩ := tele_pick R.motiveBinders typeRead Q choose
  refine ⟨motives, typed, ?_, ?_⟩
  · simpa only [List.length_map, motiveBinders_length] using typed.length
  · intro j bound
    simpa only [Q, List.length_take_of_le (Nat.le_of_lt bound)] using properties j bound

end Ix.CompileCert.Pj
