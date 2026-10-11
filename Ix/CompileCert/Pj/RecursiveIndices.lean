import Ix.CompileCert.Pj.RecursiveHypothesis
import Ix.CompileCert.Pj.MinorIndices

namespace Ix.CompileCert.Pj

open Kernel.SetTheory Kernel.SetModel
open Ix.CompileCert (pushArguments DenotesSpine)

universe u

variable {V : Type u} [Kernel.SetTheory V]
  {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat}

/-- Reading an application supplies a reading of each actual argument. -/
theorem denotes_spine_arguments (args : List Kernel.Expr)
    {f : Kernel.Expr} {ρ : Nat → V} {value : V}
    (reading : Kernel.Denotes cval env φ ρ (Kernel.Expr.mkAppN f args) value) :
    ∃ xs, DenotesSpine cval env φ ρ args xs := by
  induction args generalizing f value with
  | nil => exact ⟨[], .nil⟩
  | cons a args ih =>
    have rest : Kernel.Denotes cval env φ ρ
        (Kernel.Expr.mkAppN (.app f a) args) value := reading
    obtain ⟨_, first⟩ := Ix.CompileCert.denotes_mkAppN_head args rest
    cases first with
    | app _ argument =>
      obtain ⟨xs, reads⟩ := ih rest
      exact ⟨_ :: xs, .cons argument reads⟩

/-- Removing both actual IH-context insertions recovers the original recursive
result-index readings, with the recursive arguments still in scope. -/
theorem MinorRd.ih_indices_unlift (n : MinorRd) (nm ky : Nat)
    (idx : List Kernel.Expr) (ρ : Nat → V)
    (params motives before after hypotheses arguments indices : List V)
    (motiveLength : motives.length = nm)
    (fieldLength : (before ++ after).length = n.fields.length)
    (argumentLength : arguments.length = ky)
    (reading : DenotesSpine cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ after ++ hypotheses ++ arguments))
      (idx.map (fun e => (e.liftLooseBVars nm (before.length + ky)).liftLooseBVars
        (n.fields.length - before.length + hypotheses.length) ky)) indices) :
    DenotesSpine cval env φ
      (pushArguments ρ (params ++ before ++ arguments)) idx indices := by
  have shift : n.fields.length - before.length + hypotheses.length =
      (after ++ hypotheses).length := by
    simp only [List.length_append] at fieldLength ⊢
    omega
  have lifted : DenotesSpine cval env φ
      (pushArguments ρ ((params ++ motives ++ before) ++
        (after ++ hypotheses) ++ arguments))
      ((idx.map (fun e => e.liftLooseBVars motives.length
        (before.length + arguments.length))).map
          (fun e => e.liftLooseBVars (after ++ hypotheses).length arguments.length))
      indices := by
    simpa only [List.append_assoc, List.map_map, Function.comp_def,
      motiveLength, argumentLength, shift] using reading
  have withoutLater := denotesSpine_unlift
    (valuationLift_middle ρ (params ++ motives ++ before) (after ++ hypotheses) arguments)
    lifted
  have firstRead : DenotesSpine cval env φ
      (pushArguments ρ (params ++ motives ++ (before ++ arguments)))
      (idx.map (fun e => e.liftLooseBVars motives.length
        (before ++ arguments).length)) indices := by
    simpa only [List.append_assoc, List.length_append] using withoutLater
  have original := denotesSpine_unlift
    (valuationLift_middle ρ params motives (before ++ arguments)) firstRead
  simpa only [List.append_assoc] using original

/-- The inhabited actual IH type supplies the original index readings at every
typed argument tuple. No separate index-denotation premise is required. -/
theorem MinorRd.ih_indices_read (n : MinorRd) (nm j : Nat)
    (ys : List (Kernel.Expr × Kernel.BinderMeta)) (idx : List Kernel.Expr)
    (ρ : Nat → V) (params motives before after hypotheses arguments : List V)
    (field : V)
    (motiveLength : motives.length = nm)
    (fieldLength : (before ++ [field] ++ after).length = n.fields.length)
    {T f : V}
    (typeRead : Kernel.Denotes cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses))
      (n.ihTy nm hypotheses.length before.length j ys idx) T)
    (member : f ∈ˢ T)
    (typed : TeleTyped cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses))
      ((liftTele (n.fields.length - before.length + hypotheses.length) 0
        (liftTele nm before.length ys)).map Prod.fst) arguments) :
    ∃ indices, DenotesSpine cval env φ
      (pushArguments ρ (params ++ before ++ arguments)) idx indices := by
  have argumentLength : arguments.length = ys.length := by
    simpa only [List.length_map, liftTele_length] using typed.length
  obtain ⟨B, bodyRead, _⟩ := teleTyped_apply
    (bs := liftTele (n.fields.length - before.length + hypotheses.length) 0
      (liftTele nm before.length ys))
    (by simpa only [MinorRd.ihTy] using typeRead) member typed
  obtain ⟨values, spine⟩ := denotes_spine_arguments
    (idx.map (fun e => (e.liftLooseBVars nm (before.length + ys.length)).liftLooseBVars
      (n.fields.length - before.length + hypotheses.length) ys.length) ++
      [Kernel.Expr.mkAppN
        (.bvar (ys.length + hypotheses.length + (n.fields.length - 1 - before.length)))
        (bvarsAt ys.length 0)]) bodyRead
  have frontRead := spine.take idx.length
  have allIndices :
      (idx.map (fun e => (e.liftLooseBVars nm (before.length + ys.length)).liftLooseBVars
        (n.fields.length - before.length + hypotheses.length) ys.length)).take idx.length =
      idx.map (fun e => (e.liftLooseBVars nm (before.length + ys.length)).liftLooseBVars
        (n.fields.length - before.length + hypotheses.length) ys.length) := by
    have full (es : List Kernel.Expr) : es.take es.length = es := List.take_length
    simpa only [List.length_map] using full
      (idx.map (fun e => (e.liftLooseBVars nm (before.length + ys.length)).liftLooseBVars
        (n.fields.length - before.length + hypotheses.length) ys.length))
  have lifted : DenotesSpine cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses ++ arguments))
      (idx.map (fun e => (e.liftLooseBVars nm (before.length + ys.length)).liftLooseBVars
        (n.fields.length - before.length + hypotheses.length) ys.length))
      (values.take idx.length) := by
    simpa only [Ix.CompileCert.pushArguments_append, List.take_append,
      List.length_map, Nat.sub_self, List.take_zero, List.append_nil, allIndices] using frontRead
  exact ⟨_, n.ih_indices_unlift nm ys.length idx ρ params motives before
    ([field] ++ after) hypotheses arguments _ motiveLength
    (by simpa only [List.append_assoc] using fieldLength) argumentLength
    (by simpa only [List.append_assoc] using lifted)⟩

/-- An actual IH inhabitant gives both the original index readings and the
selected motive membership. The enclosing induction need not postulate either. -/
theorem MinorRd.ih_applied_exists (n : MinorRd) (nm j : Nat)
    (ys : List (Kernel.Expr × Kernel.BinderMeta)) (idx : List Kernel.Expr)
    (ρ : Nat → V) (params motives before after hypotheses arguments : List V)
    (field : V)
    (motiveLength : motives.length = nm)
    (fieldLength : (before ++ [field] ++ after).length = n.fields.length)
    (motiveBound : j < motives.length)
    {T f : V}
    (typeRead : Kernel.Denotes cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses))
      (n.ihTy nm hypotheses.length before.length j ys idx) T)
    (member : f ∈ˢ T)
    (typed : TeleTyped cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses))
      ((liftTele (n.fields.length - before.length + hypotheses.length) 0
        (liftTele nm before.length ys)).map Prod.fst) arguments) :
    ∃ indices, DenotesSpine cval env φ
      (pushArguments ρ (params ++ before ++ arguments)) idx indices ∧
      arguments.foldl app f ∈ˢ
        (indices ++ [arguments.foldl app field]).foldl app motives[j] := by
  obtain ⟨indices, indexRead⟩ := n.ih_indices_read nm j ys idx ρ params motives before
    after hypotheses arguments field motiveLength fieldLength typeRead member typed
  exact ⟨indices, indexRead, n.ih_applied nm j ys idx ρ params motives before after
    hypotheses arguments indices field motiveLength fieldLength motiveBound indexRead
    typeRead member typed⟩


end Ix.CompileCert.Pj
