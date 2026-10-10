import Ix.CompileCert.Pj.MinorFamily
import Ix.CompileCert.Pj.GradedTelescope
import Ix.CompileCert.Pj.Graded

/-! Internal recursor assembly with the grading facts derived from the same
strong installed model. Constructor-step minor inhabitation remains open. -/

namespace Ix.CompileCert.Pj

open Kernel.SetTheory Kernel.SetModel
open Ix.CompileCert (pushArguments)

universe u

variable {V : Type u} [Kernel.SetTheory V]
  {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat}

theorem RecRd.type_graded {r : Kernel.Name} {R : RecRd}
    (checked : R.RecOk env r) (strong : Ix.CompileCert.StrongInstalledModel V env)
    (φ : Kernel.Name → Nat) (ρ : Nat → V) :
    Bridge.Graded strong.public.cval env φ ρ R.type := by
  have entry : ∃ ci, env.find? r = some ci ∧ ci.toConstantVal.type = R.type := by
    cases lookup : env.find? r with
    | none => simp [RecRd.RecOk, lookup] at checked
    | some ci =>
      cases ci <;> simp only [RecRd.RecOk, lookup] at checked
      case recInfo hdr np nm rules => exact ⟨_, rfl, checked⟩
  obtain ⟨ci, lookup, typeEq⟩ := entry
  rw [← typeEq]
  exact installed_type_graded strong (Kernel.Semantics.Env.find?_mem lookup) φ ρ

/-- At each selected prefix, grading supplies the actual next minor domain.
Removing the earlier-minor insertion transports both grading and denotation. -/
theorem RecRd.choose_minors_graded (R : RecRd) (ρ : Nat → V)
    {b : Kernel.Expr} {T : V}
    (graded : Bridge.Graded cval env φ ρ (piJoin R.minorBinders b))
    (typeRead : Kernel.Denotes cval env φ ρ (piJoin R.minorBinders b) T)
    (inhabited : ∀ n ∈ R.minors,
      Bridge.Graded cval env φ ρ (n.type R.np R.nm R.motives) → ∀ A,
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
    have domainGraded := graded_piJoin_domain_at_split split graded typed
    have liftedGraded : Bridge.Graded cval env φ (pushArguments ρ xs)
        (((R.minors.getD before.length default).type R.np R.nm R.motives).liftLooseBVars
          xs.length 0) := by
      simpa only [binder, length] using domainGraded
    have original := denotes_unlift xs.length _ (valuationLift_prefix ρ xs) lifted
    have originalGraded := graded_unlift xs.length _ (valuationLift_prefix ρ xs) liftedGraded
    obtain ⟨x, hx⟩ := inhabited _ member originalGraded A original
    exact ⟨x, hx, trivial⟩
  obtain ⟨minors, typed, _⟩ := tele_pick R.minorBinders typeRead (fun _ _ => True) choose
  refine ⟨minors, typed, ?_⟩
  simpa only [List.length_map, minorBinders_length] using typed.length

/-- The original strong model supplies all grading used by the remaining
constructor-step obligation. No grading premise is added to its caller. -/
theorem RecRd.predicate_of_graded_minor_inhabitation {r : Kernel.Name} {R : RecRd}
    (checked : R.Check env r) (strong : Ix.CompileCert.StrongInstalledModel V env)
    (φ : Kernel.Name → Nat) (ρ : Nat → V) (params : List V)
    (paramsTyped : TeleTyped strong.public.cval env φ ρ (R.params.map Prod.fst) params)
    (predicate : Nat → List V → Prop)
    (minorInhabited : ∀ motives,
      TeleTyped strong.public.cval env φ (pushArguments ρ params)
        (R.motiveBinders.map Prod.fst) motives →
      (∀ j (bound : j < motives.length) arguments,
        TeleTyped strong.public.cval env φ (pushArguments ρ params)
          (((R.motives.getD j default).tele R.np).map Prod.fst) arguments →
        arguments.foldl app motives[j] = truthVal (predicate j arguments)) →
      ∀ n ∈ R.minors,
        Bridge.Graded strong.public.cval env φ
          (pushArguments (pushArguments ρ params) motives)
          (n.type R.np R.nm R.motives) → ∀ A,
        Kernel.Denotes strong.public.cval env φ
          (pushArguments (pushArguments ρ params) motives)
          (n.type R.np R.nm R.motives) A → ∃ x, x ∈ˢ A)
    (arguments : List V)
    (typed : TeleTyped strong.public.cval env φ (pushArguments ρ params)
      ((R.majorMotive.tele R.np).map Prod.fst) arguments) :
    predicate R.major arguments := by
  have wholeGraded := RecRd.type_graded checked.1 strong φ ρ
  obtain ⟨T, typeRead, f, member⟩ := RecRd.type_inhabited checked.1 strong.public φ ρ
  obtain ⟨T₁, motivesRead, afterParams⟩ := teleTyped_apply
    (bs := R.params) (by simpa only [RecRd.type] using typeRead) member paramsTyped
  have motivesGraded := graded_piJoin (bs := R.params)
    (by simpa only [RecRd.type] using wholeGraded) paramsTyped
  obtain ⟨motives, motivesTyped, motiveLength, chosen⟩ :=
    RecRd.choose_motives checked (pushArguments ρ params) motivesRead predicate
  obtain ⟨T₂, minorsRead, afterMotives⟩ := teleTyped_apply motivesRead afterParams motivesTyped
  have minorsGraded := graded_piJoin motivesGraded motivesTyped
  obtain ⟨minors, minorsTyped, minorLength⟩ := R.choose_minors_graded
    (pushArguments (pushArguments ρ params) motives) minorsGraded minorsRead
    (minorInhabited motives motivesTyped chosen)
  obtain ⟨T₃, finalRead, afterMinors⟩ := teleTyped_apply minorsRead afterMotives minorsTyped
  exact RecRd.predicate_of_final_application checked (pushArguments ρ params)
    motives minors motiveLength minorLength predicate chosen
    (by simpa only [Ix.CompileCert.pushArguments_append] using finalRead)
    afterMinors arguments typed

end Ix.CompileCert.Pj
