import Ix.CompileCert.Pj.MotiveFamily
import Ix.CompileCert.Pj.RecValuation

namespace Ix.CompileCert.Pj

open Kernel.SetTheory Kernel.SetModel
open Ix.CompileCert (pushArguments DenotesSpine)

universe u

variable {V : Type u} [Kernel.SetTheory V]
  {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat}

/-- The conclusion reads the selected motive at the actual argument values,
with both the minor and final argument segments accounted for. -/
theorem RecRd.concl_denotes (R : RecRd) (ρ : Nat → V)
    (motives minors arguments : List V)
    (motiveLength : motives.length = R.nm)
    (minorLength : minors.length = R.nmin)
    (argumentLength : arguments.length = (R.majorMotive.tele R.np).length)
    (majorBound : R.major < motives.length) :
    Kernel.Denotes cval env φ
      (pushArguments ρ (motives ++ minors ++ arguments)) R.concl
      (arguments.foldl app motives[R.major]) := by
  have position : (R.majorMotive.tele R.np).length + R.nmin +
      (R.nm - 1 - R.major) =
      (minors ++ arguments).length + (motives.length - 1 - R.major) := by
    simp only [List.length_append, motiveLength, minorLength, argumentLength]
    omega
  have value : pushArguments ρ (motives ++ minors ++ arguments)
      ((R.majorMotive.tele R.np).length + R.nmin + (R.nm - 1 - R.major)) =
      motives[R.major] := by
    rw [List.append_assoc, Ix.CompileCert.pushArguments_append, position,
      Ix.CompileCert.pushArguments_above,
      Ix.CompileCert.pushArguments_get motives ρ R.major majorBound]
  have head : Kernel.Denotes cval env φ
      (pushArguments ρ (motives ++ minors ++ arguments))
      (.bvar ((R.majorMotive.tele R.np).length + R.nmin + (R.nm - 1 - R.major)))
      motives[R.major] := by
    rw [← value]
    exact .bvar
  have argumentsRead : DenotesSpine cval env φ
      (pushArguments ρ (motives ++ minors ++ arguments))
      (bvarsAt (R.majorMotive.tele R.np).length 0) arguments := by
    simpa only [List.append_nil, List.length_nil,
      Ix.CompileCert.pushArguments_append, argumentLength] using
      (denotesSpine_bvarsAt (cval := cval) (env := env) (φ := φ)
        (pushArguments ρ (motives ++ minors)) arguments [])
  exact Ix.CompileCert.denotes_mkAppN head argumentsRead

/-- Once the recursor has its motives and minor inhabitants, its membership
law forces the selected predicate for every typed index/major tuple. Minor
inhabitation remains a separate obligation of the induction construction. -/
theorem RecRd.predicate_of_final_application {r : Kernel.Name} {R : RecRd}
    (checked : R.Check env r) (ρ : Nat → V)
    (motives minors : List V)
    (motiveLength : motives.length = R.nm)
    (minorLength : minors.length = R.nmin)
    (predicate : Nat → List V → Prop)
    (chosen : ∀ j (bound : j < motives.length) arguments,
      TeleTyped cval env φ ρ
        (((R.motives.getD j default).tele R.np).map Prod.fst) arguments →
      arguments.foldl app motives[j] = truthVal (predicate j arguments))
    {T f : V}
    (typeRead : Kernel.Denotes cval env φ (pushArguments ρ (motives ++ minors))
      (piJoin R.finalBinders R.concl) T)
    (member : f ∈ˢ T)
    (arguments : List V)
    (typed : TeleTyped cval env φ ρ
      ((R.majorMotive.tele R.np).map Prod.fst) arguments) :
    predicate R.major arguments := by
  have majorBound : R.major < motives.length := by
    rw [motiveLength]
    exact checked.2.1
  have argumentLength : arguments.length = (R.majorMotive.tele R.np).length := by
    simpa only [List.length_map] using typed.length
  have finalTyped : TeleTyped cval env φ (pushArguments ρ (motives ++ minors))
      (R.finalBinders.map Prod.fst) arguments := by
    rw [finalBinders_types checked]
    have lifted := typed.lift (valuationLift_prefix ρ (motives ++ minors))
    simpa only [List.length_append, motiveLength, minorLength] using lifted
  obtain ⟨B, bodyRead, bodyMember⟩ := teleTyped_apply typeRead member finalTyped
  have conclusionRead := R.concl_denotes (cval := cval) (env := env) (φ := φ)
    ρ motives minors arguments motiveLength minorLength argumentLength majorBound
  have Bvalue : B = arguments.foldl app motives[R.major] :=
    Kernel.Denotes_functional bodyRead
      (by simpa only [Ix.CompileCert.pushArguments_append] using conclusionRead)
  have truth := chosen R.major majorBound arguments typed
  rw [Bvalue, truth] at bodyMember
  exact of_mem_truthVal bodyMember

end Ix.CompileCert.Pj
