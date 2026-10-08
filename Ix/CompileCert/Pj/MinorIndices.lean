import Ix.CompileCert.Pj.ConstructorApplication

namespace Ix.CompileCert.Pj

open Kernel.SetTheory Kernel.SetModel
open Ix.CompileCert (pushArguments DenotesSpine ValuationLift)

universe u

variable {V : Type u} [Kernel.SetTheory V]
  {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat}

/-- Grading supplies the readings of every actual application argument. -/
theorem graded_spine_arguments (args : List Kernel.Expr)
    {f : Kernel.Expr} {ρ : Nat → V}
    (graded : Bridge.Graded cval env φ ρ (Kernel.Expr.mkAppN f args)) :
    ∃ xs, DenotesSpine cval env φ ρ args xs := by
  induction args generalizing f with
  | nil => exact ⟨[], .nil⟩
  | cons a args ih =>
    have rest : Bridge.Graded cval env φ ρ
        (Kernel.Expr.mkAppN (.app f a) args) := by
      simpa only [Kernel.Expr.mkAppN, List.foldl_cons] using graded
    have first := graded_spine_head args rest
    obtain ⟨x, read⟩ := Bridge.Graded.denotes first.2.1
    obtain ⟨xs, reads⟩ := ih rest
    exact ⟨x :: xs, .cons read reads⟩

/-- Removing a valuation insertion transports the entire lifted spine. -/
theorem denotesSpine_unlift {ρ target : Nat → V} {es : List Kernel.Expr}
    {xs : List V} {amount cutoff : Nat}
    (related : ValuationLift amount cutoff ρ target)
    (reading : DenotesSpine cval env φ target
      (es.map (fun e => e.liftLooseBVars amount cutoff)) xs) :
    DenotesSpine cval env φ ρ es xs := by
  induction es generalizing xs with
  | nil => cases reading; exact .nil
  | cons e es ih =>
    cases reading with
    | cons head tail => exact .cons (denotes_unlift amount e related head) (ih tail)

/-- The actual graded minor conclusion supplies its original constructor-context
result-index readings. Neither these readings nor a closed-input restriction
need to be postulated by the enclosing induction proof. -/
theorem MinorRd.indices_read (n : MinorRd) (np nm : Nat) (ρ : Nat → V)
    (params motives fields hypotheses : List V)
    (motiveLength : motives.length = nm)
    (fieldLength : fields.length = n.fields.length)
    (hypothesisLength : hypotheses.length = n.recFields.length)
    (graded : Bridge.Graded cval env φ
      (pushArguments ρ (params ++ motives ++ fields ++ hypotheses)) (n.concl np nm)) :
    ∃ indices, DenotesSpine cval env φ (pushArguments ρ (params ++ fields))
      n.resIdx indices := by
  obtain ⟨arguments, spine⟩ := graded_spine_arguments
    (n.resIdx.map (fun e =>
      (e.liftLooseBVars nm n.fields.length).liftLooseBVars n.recFields.length 0) ++
      [Kernel.Expr.mkAppN (.const n.ctor n.ctorUs)
        (bvarsAt np (n.recFields.length + n.fields.length + nm) ++
          bvarsAt n.fields.length n.recFields.length)])
    (f := .bvar (n.recFields.length + n.fields.length + (nm - 1 - n.motive)))
    graded
  have frontRead := spine.take n.resIdx.length
  have allIndices :
      (n.resIdx.map (fun e =>
        (e.liftLooseBVars nm n.fields.length).liftLooseBVars n.recFields.length 0)).take
        n.resIdx.length = n.resIdx.map (fun e =>
          (e.liftLooseBVars nm n.fields.length).liftLooseBVars n.recFields.length 0) := by
    have full (es : List Kernel.Expr) : es.take es.length = es := List.take_length
    simpa only [List.length_map] using full
      (n.resIdx.map (fun e =>
        (e.liftLooseBVars nm n.fields.length).liftLooseBVars n.recFields.length 0))
  have lifted : DenotesSpine cval env φ
      (pushArguments (pushArguments ρ (params ++ motives ++ fields)) hypotheses)
      ((n.resIdx.map (fun e => e.liftLooseBVars motives.length fields.length)).map
        (fun e => e.liftLooseBVars hypotheses.length 0))
      (arguments.take n.resIdx.length) := by
    simpa only [List.map_map, Function.comp_def, motiveLength, fieldLength,
      hypothesisLength, Ix.CompileCert.pushArguments_append,
      List.take_append, List.length_map, Nat.sub_self, List.take_zero,
      List.append_nil, allIndices] using frontRead
  have withoutHypotheses := denotesSpine_unlift
    (valuationLift_prefix (pushArguments ρ (params ++ motives ++ fields)) hypotheses) lifted
  exact ⟨_, denotesSpine_unlift (valuationLift_middle ρ params motives fields)
    withoutHypotheses⟩

/-- Both semantic inputs to the minor-conclusion reading now come from the
checked constructor and the actual graded conclusion in the same strong model. -/
theorem MinorRd.concl_read_of_graded (n : MinorRd) (np nm : Nat)
    (sourceMotives : List MotiveRd) (paramBinders : List (Kernel.Expr × Kernel.BinderMeta))
    (checked : n.CtorOk env np sourceMotives paramBinders)
    (strong : Ix.CompileCert.StrongInstalledModel V env)
    (φ : Kernel.Name → Nat) (ρ : Nat → V)
    (params motives fields hypotheses : List V)
    (paramLength : params.length = np)
    (motiveLength : motives.length = nm)
    (fieldLength : fields.length = n.fields.length)
    (hypothesisLength : hypotheses.length = n.recFields.length)
    (motiveBound : n.motive < motives.length)
    (graded : Bridge.Graded strong.public.cval env φ
      (pushArguments ρ (params ++ motives ++ fields ++ hypotheses)) (n.concl np nm)) :
    ∃ constructor indices,
      (∀ valuation, Kernel.Denotes strong.public.cval env φ valuation
        (.const n.ctor n.ctorUs) constructor) ∧
      DenotesSpine strong.public.cval env φ (pushArguments ρ (params ++ fields))
        n.resIdx indices ∧
      Kernel.Denotes strong.public.cval env φ
        (pushArguments ρ (params ++ motives ++ fields ++ hypotheses)) (n.concl np nm)
        ((indices ++ [(params ++ fields).foldl app constructor]).foldl app motives[n.motive]) := by
  obtain ⟨constructor, _, constructorRead, _, _⟩ :=
    n.constructor_typed np sourceMotives paramBinders checked strong φ ρ
  obtain ⟨indices, indexRead⟩ := n.indices_read np nm ρ params motives fields hypotheses
    motiveLength fieldLength hypothesisLength graded
  exact ⟨constructor, indices, constructorRead, indexRead,
    n.concl_denotes np nm ρ params motives fields hypotheses indices constructor
      paramLength motiveLength fieldLength hypothesisLength motiveBound indexRead
      (constructorRead _)⟩

end Ix.CompileCert.Pj
