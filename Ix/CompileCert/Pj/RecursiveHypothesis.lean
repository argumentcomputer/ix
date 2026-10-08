import Ix.CompileCert.Pj.RecursiveTransport

namespace Ix.CompileCert.Pj

open Kernel.SetTheory Kernel.SetModel
open Ix.CompileCert (pushArguments DenotesSpine)

universe u

variable {V : Type u} [Kernel.SetTheory V]
  {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat}

/-- A selected variable retains its value across explicit earlier and later
argument segments, in the reader's outermost-first argument order. -/
theorem denotes_bvar_segment (ρ : Nat → V) (earlier values later : List V)
    (index : Nat) (bound : index < values.length) :
    Kernel.Denotes cval env φ (pushArguments ρ (earlier ++ values ++ later))
      (.bvar (later.length + (values.length - 1 - index))) values[index] := by
  have value : pushArguments ρ (earlier ++ values ++ later)
      (later.length + (values.length - 1 - index)) = values[index] := by
    rw [Ix.CompileCert.pushArguments_append, Ix.CompileCert.pushArguments_above,
      Ix.CompileCert.pushArguments_append,
      Ix.CompileCert.pushArguments_get values (pushArguments ρ earlier) index bound]
  rw [← value]
  exact .bvar

/-- The body of the actual recursive-field IH reads its selected motive at
the original recursive indices and the recursive field applied to its arguments.
All parameter, motive, field and earlier-IH segments remain in scope. -/
theorem MinorRd.ih_body_denotes (n : MinorRd) (nm j : Nat)
    (ys : List (Kernel.Expr × Kernel.BinderMeta)) (idx : List Kernel.Expr)
    (ρ : Nat → V) (params motives before after hypotheses arguments indices : List V)
    (field : V)
    (motiveLength : motives.length = nm)
    (fieldLength : (before ++ [field] ++ after).length = n.fields.length)
    (argumentLength : arguments.length = ys.length)
    (motiveBound : j < motives.length)
    (indexRead : DenotesSpine cval env φ
      (pushArguments ρ (params ++ before ++ arguments)) idx indices) :
    Kernel.Denotes cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses ++ arguments))
      (Kernel.Expr.mkAppN
        (.bvar (ys.length + hypotheses.length + n.fields.length + (nm - 1 - j)))
        (idx.map (fun e => (e.liftLooseBVars nm (before.length + ys.length)).liftLooseBVars
          (n.fields.length - before.length + hypotheses.length) ys.length) ++
          [Kernel.Expr.mkAppN
            (.bvar (ys.length + hypotheses.length + (n.fields.length - 1 - before.length)))
            (bvarsAt ys.length 0)]))
      ((indices ++ [arguments.foldl app field]).foldl app motives[j]) := by
  have motivePosition :
      (before ++ [field] ++ after ++ hypotheses ++ arguments).length +
        (motives.length - 1 - j) =
      ys.length + hypotheses.length + n.fields.length + (nm - 1 - j) := by
    simp only [List.length_append, List.length_cons, List.length_nil] at fieldLength ⊢
    omega
  have headRead : Kernel.Denotes cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses ++ arguments))
      (.bvar (ys.length + hypotheses.length + n.fields.length + (nm - 1 - j)))
      motives[j] := by
    have reading := denotes_bvar_segment (cval := cval) (env := env) (φ := φ)
      ρ params motives (before ++ [field] ++ after ++ hypotheses ++ arguments) j motiveBound
    rw [motivePosition] at reading
    simpa only [List.append_assoc] using reading
  have fieldPosition :
      (after ++ hypotheses ++ arguments).length + ([field].length - 1 - 0) =
      ys.length + hypotheses.length + (n.fields.length - 1 - before.length) := by
    simp only [List.length_append, List.length_cons, List.length_nil] at fieldLength ⊢
    omega
  have fieldRead : Kernel.Denotes cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses ++ arguments))
      (.bvar (ys.length + hypotheses.length + (n.fields.length - 1 - before.length)))
      field := by
    have reading := denotes_bvar_segment (cval := cval) (env := env) (φ := φ)
      ρ (params ++ motives ++ before) [field] (after ++ hypotheses ++ arguments) 0 (by simp)
    rw [fieldPosition] at reading
    simpa only [List.append_assoc, List.getElem_cons_zero] using reading
  have argumentsRead : DenotesSpine cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses ++ arguments))
      (bvarsAt ys.length 0) arguments := by
    simpa only [List.append_nil, List.length_nil, argumentLength] using
      (denotesSpine_bvarsAt_middle (cval := cval) (env := env) (φ := φ)
        ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses) arguments [])
  have indicesRead := n.ih_indices_lift nm ys.length idx ρ params motives before
    ([field] ++ after) hypotheses arguments indices motiveLength
    (by simpa only [List.append_assoc] using fieldLength) argumentLength indexRead
  have liftedIndices : DenotesSpine cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses ++ arguments))
      (idx.map (fun e => (e.liftLooseBVars nm (before.length + ys.length)).liftLooseBVars
        (n.fields.length - before.length + hypotheses.length) ys.length)) indices := by
    simpa only [List.append_assoc] using indicesRead
  exact Ix.CompileCert.denotes_mkAppN headRead
    (liftedIndices.append (.cons
      (Ix.CompileCert.denotes_mkAppN fieldRead argumentsRead) .nil))

/-- An inhabitant of the reader's actual IH type supplies the selected motive
at every typed recursive-field argument tuple. This is the IH application used
by the minor constructor step; it does not assume the induction conclusion. -/
theorem MinorRd.ih_applied (n : MinorRd) (nm j : Nat)
    (ys : List (Kernel.Expr × Kernel.BinderMeta)) (idx : List Kernel.Expr)
    (ρ : Nat → V) (params motives before after hypotheses arguments indices : List V)
    (field : V)
    (motiveLength : motives.length = nm)
    (fieldLength : (before ++ [field] ++ after).length = n.fields.length)
    (motiveBound : j < motives.length)
    (indexRead : DenotesSpine cval env φ
      (pushArguments ρ (params ++ before ++ arguments)) idx indices)
    {T f : V}
    (typeRead : Kernel.Denotes cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses))
      (n.ihTy nm hypotheses.length before.length j ys idx) T)
    (member : f ∈ˢ T)
    (typed : TeleTyped cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses))
      ((liftTele (n.fields.length - before.length + hypotheses.length) 0
        (liftTele nm before.length ys)).map Prod.fst) arguments) :
    arguments.foldl app f ∈ˢ
      (indices ++ [arguments.foldl app field]).foldl app motives[j] := by
  have argumentLength : arguments.length = ys.length := by
    simpa only [List.length_map, liftTele_length] using typed.length
  obtain ⟨B, bodyRead, applied⟩ := teleTyped_apply
    (bs := liftTele (n.fields.length - before.length + hypotheses.length) 0
      (liftTele nm before.length ys))
    (by simpa only [MinorRd.ihTy] using typeRead) member typed
  have reading := n.ih_body_denotes nm j ys idx ρ params motives before after
    hypotheses arguments indices field motiveLength fieldLength argumentLength motiveBound indexRead
  have value : B = (indices ++ [arguments.foldl app field]).foldl app motives[j] :=
    Kernel.Denotes_functional bodyRead
      (by simpa only [Ix.CompileCert.pushArguments_append] using reading)
  simpa only [value] using applied

end Ix.CompileCert.Pj
