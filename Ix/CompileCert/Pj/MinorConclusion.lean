import Ix.CompileCert.Pj.RecConclusion

namespace Ix.CompileCert.Pj

open Kernel.SetTheory Kernel.SetModel
open Ix.CompileCert (pushArguments DenotesSpine ValuationLift)

universe u

variable {V : Type u} [Kernel.SetTheory V]
  {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat}

/-- The same insertion transports every expression of an application spine. -/
theorem denotesSpine_lift {ρ target : Nat → V} {es : List Kernel.Expr}
    {xs : List V} {amount cutoff : Nat}
    (reading : DenotesSpine cval env φ ρ es xs)
    (related : ValuationLift amount cutoff ρ target) :
    DenotesSpine cval env φ target
      (es.map (fun e => e.liftLooseBVars amount cutoff)) xs := by
  induction reading with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons (Ix.CompileCert.denotes_lift head related) ih

/-- The rebuilt minor conclusion reads the selected motive at the constructor's
actual result indices and its parameter/field application. The motive and IH
insertions preserve the original constructor-context index readings. -/
theorem MinorRd.concl_denotes (n : MinorRd) (np nm : Nat) (ρ : Nat → V)
    (params motives fields hypotheses indices : List V) (constructor : V)
    (paramLength : params.length = np)
    (motiveLength : motives.length = nm)
    (fieldLength : fields.length = n.fields.length)
    (hypothesisLength : hypotheses.length = n.recFields.length)
    (motiveBound : n.motive < motives.length)
    (indexRead : DenotesSpine cval env φ (pushArguments ρ (params ++ fields))
      n.resIdx indices)
    (constructorRead : Kernel.Denotes cval env φ
      (pushArguments ρ (params ++ motives ++ fields ++ hypotheses))
      (.const n.ctor n.ctorUs) constructor) :
    Kernel.Denotes cval env φ
      (pushArguments ρ (params ++ motives ++ fields ++ hypotheses))
      (n.concl np nm)
      ((indices ++ [(params ++ fields).foldl app constructor]).foldl app
        motives[n.motive]) := by
  have position : n.recFields.length + n.fields.length + (nm - 1 - n.motive) =
      (fields ++ hypotheses).length + (motives.length - 1 - n.motive) := by
    simp only [List.length_append, motiveLength, fieldLength, hypothesisLength]
    omega
  have value : pushArguments ρ (params ++ motives ++ fields ++ hypotheses)
      (n.recFields.length + n.fields.length + (nm - 1 - n.motive)) =
      motives[n.motive] := by
    have segments : params ++ motives ++ fields ++ hypotheses =
        params ++ (motives ++ (fields ++ hypotheses)) := by
      simp only [List.append_assoc]
    rw [segments, Ix.CompileCert.pushArguments_append, position,
      Ix.CompileCert.pushArguments_append, Ix.CompileCert.pushArguments_above,
      Ix.CompileCert.pushArguments_get motives (pushArguments ρ params)
        n.motive motiveBound]
  have headRead : Kernel.Denotes cval env φ
      (pushArguments ρ (params ++ motives ++ fields ++ hypotheses))
      (.bvar (n.recFields.length + n.fields.length + (nm - 1 - n.motive)))
      motives[n.motive] := by
    rw [← value]
    exact .bvar
  have lifted := denotesSpine_lift
    (denotesSpine_lift indexRead (valuationLift_middle ρ params motives fields))
    (valuationLift_prefix (pushArguments ρ (params ++ motives ++ fields)) hypotheses)
  have indicesRead : DenotesSpine cval env φ
      (pushArguments ρ (params ++ motives ++ fields ++ hypotheses))
      (n.resIdx.map (fun e =>
        (e.liftLooseBVars nm n.fields.length).liftLooseBVars n.recFields.length 0))
      indices := by
    simpa only [List.map_map, Function.comp_def, motiveLength, fieldLength,
      hypothesisLength, Ix.CompileCert.pushArguments_append] using lifted
  have paramsRead : DenotesSpine cval env φ
      (pushArguments ρ (params ++ motives ++ fields ++ hypotheses))
      (bvarsAt np (n.recFields.length + n.fields.length + nm)) params := by
    have offset : n.recFields.length + n.fields.length + nm =
        (motives ++ fields ++ hypotheses).length := by
      simp only [List.length_append, motiveLength, fieldLength, hypothesisLength]
      omega
    rw [offset, ← paramLength]
    simpa only [List.append_assoc] using
      (denotesSpine_bvarsAt (cval := cval) (env := env) (φ := φ)
        ρ params (motives ++ fields ++ hypotheses))
  have fieldsRead : DenotesSpine cval env φ
      (pushArguments ρ (params ++ motives ++ fields ++ hypotheses))
      (bvarsAt n.fields.length n.recFields.length) fields := by
    simpa only [fieldLength, hypothesisLength] using
      (denotesSpine_bvarsAt_middle (cval := cval) (env := env) (φ := φ)
        ρ (params ++ motives) fields hypotheses)
  have constructorApp := Ix.CompileCert.denotes_mkAppN constructorRead
    (paramsRead.append fieldsRead)
  simpa only [MinorRd.concl] using
    (Ix.CompileCert.denotes_mkAppN headRead
      (indicesRead.append (.cons constructorApp .nil)))

end Ix.CompileCert.Pj
