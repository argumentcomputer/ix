import Ix.CompileCert.Pj.ConstructorApplication

namespace Ix.CompileCert.Pj

open Kernel.SetTheory Kernel.SetModel
open Ix.CompileCert (pushArguments DenotesSpine)

universe u

variable {V : Type u} [Kernel.SetTheory V]
  {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat}

/-- The actual recursive-field IH telescope inserts motives below earlier
fields, then the remaining fields and earlier IHs above those fields. Removing
both insertions recovers the original dependent function-argument typing. -/
theorem MinorRd.ih_arguments_unlift (n : MinorRd) (nm : Nat)
    (ys : List (Kernel.Expr × Kernel.BinderMeta)) (ρ : Nat → V)
    (params motives before after hypotheses arguments : List V)
    (motiveLength : motives.length = nm)
    (fieldLength : (before ++ after).length = n.fields.length)
    (typed : TeleTyped cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ after ++ hypotheses))
      ((liftTele (n.fields.length - before.length + hypotheses.length) 0
        (liftTele nm before.length ys)).map Prod.fst) arguments) :
    TeleTyped cval env φ (pushArguments ρ (params ++ before))
      (ys.map Prod.fst) arguments := by
  have shift : n.fields.length - before.length + hypotheses.length =
      (after ++ hypotheses).length := by
    simp only [List.length_append] at fieldLength ⊢
    omega
  have lifted : TeleTyped cval env φ
      (pushArguments (pushArguments ρ (params ++ motives ++ before)) (after ++ hypotheses))
      (liftTypes (after ++ hypotheses).length 0
        (liftTypes motives.length before.length (ys.map Prod.fst))) arguments := by
    simpa only [liftTele_types, shift, motiveLength,
      Ix.CompileCert.pushArguments_append] using typed
  have withoutLater := TeleTyped.unlift
    (valuationLift_prefix (pushArguments ρ (params ++ motives ++ before))
      (after ++ hypotheses)) lifted
  exact TeleTyped.unlift (valuationLift_middle ρ params motives before) withoutLater

/-- The two insertions used by the actual IH preserve the original recursive
result-index readings after applying its dependent argument telescope. -/
theorem MinorRd.ih_indices_lift (n : MinorRd) (nm ky : Nat)
    (idx : List Kernel.Expr) (ρ : Nat → V)
    (params motives before after hypotheses arguments indices : List V)
    (motiveLength : motives.length = nm)
    (fieldLength : (before ++ after).length = n.fields.length)
    (argumentLength : arguments.length = ky)
    (reading : DenotesSpine cval env φ
      (pushArguments ρ (params ++ before ++ arguments)) idx indices) :
    DenotesSpine cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ after ++ hypotheses ++ arguments))
      (idx.map (fun e => (e.liftLooseBVars nm (before.length + ky)).liftLooseBVars
        (n.fields.length - before.length + hypotheses.length) ky)) indices := by
  have shift : n.fields.length - before.length + hypotheses.length =
      (after ++ hypotheses).length := by
    simp only [List.length_append] at fieldLength ⊢
    omega
  have first := denotesSpine_lift reading
    (by simpa only [List.append_assoc] using
      valuationLift_middle ρ params motives (before ++ arguments))
  have firstRead : DenotesSpine cval env φ
      (pushArguments ρ ((params ++ motives ++ before) ++ arguments))
      (idx.map (fun e => e.liftLooseBVars motives.length
        (before.length + arguments.length))) indices := by
    simpa only [List.append_assoc, List.length_append] using first
  have second := denotesSpine_lift firstRead
    (valuationLift_middle ρ (params ++ motives ++ before) (after ++ hypotheses) arguments)
  simpa only [List.append_assoc, List.map_map, Function.comp_def,
    motiveLength, argumentLength, shift] using second

end Ix.CompileCert.Pj
