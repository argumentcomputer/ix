import Aiur.Memory.Encoding
import Aiur.Memory.Representation
import Mathlib.Data.Fintype.EquivFin

namespace Aiur

variable {F : Type} {rom : ROM F} {encode : Nat → F}

theorem HeapCells.of_prefix {before after : Heap F} (cells : HeapCells rom encode after)
    (grows : before <+: after) : HeapCells rom encode before :=
  fun i value found => cells i value (heap_get_of_prefix grows found)

/-- A source execution can be interpreted against any table containing its encoded heap. -/
theorem EvalExpr.toROM [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F Nat} {expr : Expr F} {before after : Heap F} {value : SourceValue F}
    (evaluated : EvalExpr program locals expr before value after) :
    HeapCells rom encode after →
      ROMEvalExpr rom program (encodeEnv encode locals) expr (value.mapAddress encode) := by
  induction evaluated using EvalExpr.rec
    (motive_2 := fun locals exprs before values after _ => HeapCells rom encode after →
      ROMEvalArgs rom program (encodeEnv encode locals) exprs (values.map (Value.mapAddress encode)))
    (motive_3 := fun name args before value after _ => HeapCells rom encode after →
      ROMEvalCall rom program name (args.map (Value.mapAddress encode)) (value.mapAddress encode)) with
  | literal => intro _; simpa only [Value.mapAddress] using ROMEvalExpr.literal
  | var found =>
      intro _
      apply ROMEvalExpr.var
      simp [encodeEnv, List.find?_map, Function.comp_def, found]
  | tuple _ ih =>
      intro cells
      simpa only [Value.mapAddress] using ROMEvalExpr.tuple (ih cells)
  | construct _ ih =>
      intro cells
      simpa only [Value.mapAddress] using ROMEvalExpr.construct (ih cells)
  | project _ projected ih =>
      intro cells
      refine .project (ih cells) ?_
      rw [projectValue_mapAddress, projected]
      rfl
  | letValue _ matched body valueIH bodyIH =>
      intro cells
      have mapped := congrArg (Option.map (encodeEnv encode)) matched
      rw [← Pattern.bindings_mapAddress] at mapped
      simp only [Option.map_some] at mapped
      refine .letValue (valueIH (cells.of_prefix body.grows)) mapped ?_
      simpa only [encodeEnv_append] using bodyIH cells
  | @store locals expr before input middle value ih =>
      intro cells
      have grow : middle <+: middle ++ [input] := ⟨[input], rfl⟩
      have cell := cells middle.length input (by simp)
      simpa only [Value.mapAddress, Value.type_mapAddress] using
        ROMEvalExpr.store (ih (cells.of_prefix grow)) cell
  | @load locals expr before input after result pointer loaded ih =>
      intro cells
      cases input with
      | field | tuple | construct => cases loaded
      | ptr target address =>
          cases found : after[address]? with
          | none => simp [loadValue, found] at loaded
          | some stored =>
              by_cases typed : stored.type = target
              · simp [loadValue, found, typed, pure, Except.pure, bind, Except.bind] at loaded
                subst result
                exact .load (by simpa only [Value.mapAddress] using ih cells)
                  (cells address stored found) (by simpa only [Value.type_mapAddress] using typed)
              · simp [loadValue, found, typed] at loaded
  | neg _ operation ih =>
      intro cells
      refine .neg (ih cells) ?_
      rw [evalNeg_mapAddress, operation]; rfl
  | hint _ typed ih =>
      intro cells
      simpa only [Constant.toValue_mapAddress] using ROMEvalExpr.hint (ih cells) typed
  | assertEq _ right operation leftIH rightIH =>
      intro cells
      refine .assertEq (leftIH (cells.of_prefix right.grows)) (rightIH cells) ?_
      exact evalAssertEq_mapAddress operation encode
  | binary _ right operation leftIH rightIH =>
      intro cells
      refine .binary (leftIH (cells.of_prefix right.grows)) (rightIH cells) ?_
      rw [evalBinOp_mapAddress, operation]; rfl
  | call _ callee argsIH callIH =>
      intro cells
      exact .call (argsIH (cells.of_prefix callee.grows)) (callIH cells)
  | matchValue _ selected branch valueIH bodyIH =>
      intro cells
      have mapped := congrArg (Option.map (fun (locals, expr) => (encodeEnv encode locals, expr))) selected
      rw [← selectArm_mapAddress] at mapped
      simp only [Option.map_some] at mapped
      refine .matchValue (valueIH (cells.of_prefix branch.grows)) mapped ?_
      simpa only [encodeEnv_append] using bodyIH cells
  | nil => exact .nil
  | cons _ tail headIH tailIH =>
      rename_i cells
      exact .cons (headIH (cells.of_prefix tail.grows)) (tailIH cells)
  | intro prepared _ bodyIH =>
      rename_i cells
      exact .intro (prepareCall_mapAddress prepared encode) (bodyIH cells)

theorem EvalFn.toROM [Field F] [DecidableEq F] {program : Program F}
    {name : String} {args : List (SourceValue F)} {before after : Heap F} {value : SourceValue F}
    (evaluated : EvalFn program name args before value after) (cells : HeapCells rom encode after) :
    ROMEvalCall rom program name (args.map (Value.mapAddress encode)) (value.mapAddress encode) := by
  cases evaluated with
  | intro prepared body => exact .intro (prepareCall_mapAddress prepared encode) (body.toROM cells)

/-- A finite field has enough address space whenever the allocation count fits its cardinality. -/
theorem heap_address_embedding [Field F] [Fintype F] (heap : Heap F)
    (capacity : heap.length ≤ Fintype.card F) :
    ∃ encode : Nat → F,
      ∀ i j, i < heap.length → j < heap.length → encode i = encode j → i = j := by
  classical
  have capacity' : Fintype.card (Fin heap.length) ≤ Fintype.card F := by simpa using capacity
  obtain ⟨embedding⟩ := Function.Embedding.nonempty_of_card_le capacity'
  let encode : Nat → F := fun i => if h : i < heap.length then embedding ⟨i, h⟩ else 0
  refine ⟨encode, ?_⟩
  intro i j hi hj same
  have equal : (⟨i, hi⟩ : Fin heap.length) = ⟨j, hj⟩ := embedding.injective (by simpa [encode, hi, hj] using same)
  exact congrArg Fin.val equal

end Aiur
