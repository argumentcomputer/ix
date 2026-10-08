import Ix.CompileCert.Pj.RecConclusion

/-! Internal assembly of the recursor membership argument. The remaining
constructor-step proof must discharge minor inhabitation; this module does not
replace that obligation with a premise of the promised induction theorem. -/

namespace Ix.CompileCert.Pj

open Kernel.SetTheory Kernel.SetModel
open Ix.CompileCert (pushArguments)

theorem RecRd.minor_at_split (R : RecRd)
    {before after : List (Kernel.Expr × Kernel.BinderMeta)}
    {t : Kernel.Expr} {bm : Kernel.BinderMeta}
    (split : R.minorBinders = before ++ (t, bm) :: after) :
    R.minors.getD before.length default ∈ R.minors ∧
      t = ((R.minors.getD before.length default).type R.np R.nm R.motives).liftLooseBVars
        before.length 0 := by
  have bound : before.length < R.minors.length := by
    have lengths := congrArg List.length split
    simp only [RecRd.minorBinders, List.length_mapIdx, List.length_append,
      List.length_cons] at lengths
    omega
  have selected : R.minors.getD before.length default = R.minors[before.length] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound,
      Option.getD_some]
  have entry : R.minorBinders[before.length]? = some (t, bm) := by
    rw [split, List.getElem?_append_right (Nat.le_refl _)]
    simp
  have actual : R.minorBinders[before.length]? =
      some (((R.minors[before.length]).type R.np R.nm R.motives).liftLooseBVars
        before.length 0, (R.minors[before.length]).binderMeta) := by
    simp only [RecRd.minorBinders, List.getElem?_mapIdx,
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

/-- The actual dependent minor-binder telescope can be filled once each
unlifted minor domain is shown inhabited. Earlier selected minors are removed
using the valuation lift relation, rather than an independence assumption. -/
theorem RecRd.choose_minors (R : RecRd) (ρ : Nat → V) {b : Kernel.Expr} {T : V}
    (typeRead : Kernel.Denotes cval env φ ρ (piJoin R.minorBinders b) T)
    (inhabited : ∀ n ∈ R.minors, ∀ A,
      Kernel.Denotes cval env φ ρ (n.type R.np R.nm R.motives) A →
      ∃ x, x ∈ˢ A) :
    ∃ minors, TeleTyped cval env φ ρ (R.minorBinders.map Prod.fst) minors ∧
      minors.length = R.nmin := by
  have choose : ∀ before after t bm,
      R.minorBinders = before ++ (t, bm) :: after →
      ∀ xs, TeleTyped cval env φ ρ (before.map Prod.fst) xs →
      ∀ A, Kernel.Denotes cval env φ (pushArguments ρ xs) t A →
      ∃ x, x ∈ˢ A ∧ True := by
    intro before after t bm split xs typed A domain
    obtain ⟨member, binder⟩ := R.minor_at_split split
    have length : xs.length = before.length := by
      simpa only [List.length_map] using typed.length
    have lifted : Kernel.Denotes cval env φ (pushArguments ρ xs)
        (((R.minors.getD before.length default).type R.np R.nm R.motives).liftLooseBVars
          xs.length 0) A := by
      simpa only [binder, length] using domain
    have original := denotes_unlift xs.length _ (valuationLift_prefix ρ xs) lifted
    obtain ⟨x, hx⟩ := inhabited _ member A original
    exact ⟨x, hx, trivial⟩
  obtain ⟨minors, typed, _⟩ := tele_pick R.minorBinders typeRead (fun _ _ => True) choose
  refine ⟨minors, typed, ?_⟩
  simpa only [List.length_map, minorBinders_length] using typed.length

/-- A checked reader identifies a stored constant whose model membership
inhabits precisely the rebuilt recursor type, at the original assignment. -/
theorem RecRd.type_inhabited {r : Kernel.Name} {R : RecRd}
    (checked : R.RecOk env r) (model : Kernel.Model V env)
    (φ : Kernel.Name → Nat) (ρ : Nat → V) :
    ∃ T, Kernel.Denotes model.cval env φ ρ R.type T ∧ ∃ f, f ∈ˢ T := by
  have entry : ∃ ci, env.find? r = some ci ∧ ci.toConstantVal.type = R.type := by
    cases lookup : env.find? r with
    | none => simp [RecRd.RecOk, lookup] at checked
    | some ci =>
      cases ci <;> simp only [RecRd.RecOk, lookup] at checked
      case recInfo hdr np nm rules => exact ⟨_, rfl, checked⟩
  obtain ⟨ci, lookup, typeEq⟩ := entry
  obtain ⟨T, typeRead, member⟩ := model.mem ci (Kernel.Semantics.Env.find?_mem lookup) φ ρ
  exact ⟨T, typeEq ▸ typeRead, _, member⟩

/-- Internal recursor-membership assembly. The quantified `minorInhabited`
argument is discharged by the constructor-step/IH proof in the induction
theorem; it is kept explicit here to isolate that still-open proof. -/
theorem RecRd.predicate_of_minor_inhabitation {r : Kernel.Name} {R : RecRd}
    (checked : R.Check env r) (model : Kernel.Model V env)
    (φ : Kernel.Name → Nat) (ρ : Nat → V) (params : List V)
    (paramsTyped : TeleTyped model.cval env φ ρ (R.params.map Prod.fst) params)
    (predicate : Nat → List V → Prop)
    (minorInhabited : ∀ motives,
      TeleTyped model.cval env φ (pushArguments ρ params)
        (R.motiveBinders.map Prod.fst) motives →
      (∀ j (bound : j < motives.length) arguments,
        TeleTyped model.cval env φ (pushArguments ρ params)
          (((R.motives.getD j default).tele R.np).map Prod.fst) arguments →
        arguments.foldl app motives[j] = truthVal (predicate j arguments)) →
      ∀ n ∈ R.minors, ∀ A,
        Kernel.Denotes model.cval env φ (pushArguments (pushArguments ρ params) motives)
          (n.type R.np R.nm R.motives) A → ∃ x, x ∈ˢ A)
    (arguments : List V)
    (typed : TeleTyped model.cval env φ (pushArguments ρ params)
      ((R.majorMotive.tele R.np).map Prod.fst) arguments) :
    predicate R.major arguments := by
  obtain ⟨T, typeRead, f, member⟩ := RecRd.type_inhabited checked.1 model φ ρ
  obtain ⟨T₁, motivesRead, afterParams⟩ := teleTyped_apply
    (bs := R.params) (by simpa only [RecRd.type] using typeRead) member paramsTyped
  obtain ⟨motives, motivesTyped, motiveLength, chosen⟩ :=
    RecRd.choose_motives checked (pushArguments ρ params) motivesRead predicate
  obtain ⟨T₂, minorsRead, afterMotives⟩ := teleTyped_apply motivesRead afterParams motivesTyped
  obtain ⟨minors, minorsTyped, minorLength⟩ := R.choose_minors
    (pushArguments (pushArguments ρ params) motives) minorsRead
    (minorInhabited motives motivesTyped chosen)
  obtain ⟨T₃, finalRead, afterMinors⟩ := teleTyped_apply minorsRead afterMotives minorsTyped
  exact RecRd.predicate_of_final_application checked (pushArguments ρ params)
    motives minors motiveLength minorLength predicate chosen
    (by simpa only [Ix.CompileCert.pushArguments_append] using finalRead)
    afterMinors arguments typed

end Ix.CompileCert.Pj
