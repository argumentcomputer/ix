import Aiur.Semantics
import Aiur.Tables
import Mathlib.Data.List.FinRange

namespace Aiur

theorem Value.mapAddress_free (value : Value F A) (free : value.pointerFree = true)
    (left right : A → B) : value.mapAddress left = value.mapAddress right := by
  cases value with
  | field => simp [Value.mapAddress]
  | ptr => simp [Value.pointerFree, Value.type, Ty.pointerFree] at free
  | tuple items | construct _ _ items =>
      simp only [Value.mapAddress, Value.tuple.injEq, Value.construct.injEq, true_and]
      have itemsFree : ∀ item ∈ items, item.pointerFree = true := by
        simpa [Value.pointerFree, Value.type, Ty.pointerFree] using free
      exact List.map_congr_left (fun item member => Value.mapAddress_free item (itemsFree item member) left right)
termination_by sizeOf value

def encodeEnv (encode : A → B) (locals : Environment F A) : Environment F B :=
  locals.map (fun (name, value) => (name, value.mapAddress encode))

@[simp] theorem encodeEnv_append (encode : A → B) (left right : Environment F A) :
    encodeEnv encode (left ++ right) = encodeEnv encode left ++ encodeEnv encode right := List.map_append

mutual
  theorem Pattern.bindings_mapAddress [DecidableEq F] (pattern : Pattern F) (value : Value F A)
      (encode : A → B) :
      pattern.bindings (value.mapAddress encode) = (pattern.bindings value).map (encodeEnv encode) := by
    cases pattern with
    | wildcard => simp [Pattern.bindings, encodeEnv]
    | bind => simp [Pattern.bindings, encodeEnv]
    | literal =>
        cases value with
        | tuple | ptr | construct => simp [Value.mapAddress, Pattern.bindings]
        | field => simp only [Value.mapAddress, Pattern.bindings]; split <;> rfl
    | tuple patterns =>
        cases value with
        | field | ptr | construct => simp [Value.mapAddress, Pattern.bindings]
        | tuple values =>
            simpa only [Value.mapAddress, Pattern.bindings] using
              Pattern.bindingsList_mapAddress patterns values encode
    | construct name ctor patterns =>
        cases value with
        | field | ptr | tuple => simp [Value.mapAddress, Pattern.bindings]
        | construct actual actualCtor values =>
            simp only [Value.mapAddress, Pattern.bindings]
            split
            · exact Pattern.bindingsList_mapAddress patterns values encode
            · rfl
  termination_by sizeOf pattern

  theorem Pattern.bindingsList_mapAddress [DecidableEq F] (patterns : List (Pattern F))
      (values : List (Value F A)) (encode : A → B) :
      Pattern.bindingsList patterns (values.map (Value.mapAddress encode)) =
        (Pattern.bindingsList patterns values).map (encodeEnv encode) := by
    cases patterns with
    | nil => cases values <;> simp [Pattern.bindingsList, encodeEnv]
    | cons pattern patterns =>
        cases values with
        | nil => simp [Pattern.bindingsList]
        | cons value values =>
            simp only [List.map_cons, Pattern.bindingsList,
              Pattern.bindings_mapAddress pattern value encode, Pattern.bindingsList_mapAddress patterns values encode]
            cases pattern.bindings value <;> cases Pattern.bindingsList patterns values <;>
              simp [encodeEnv_append]
  termination_by sizeOf patterns
end

theorem selectArm_mapAddress [DecidableEq F] (value : Value F A)
    (arms : List (Pattern F × Expr F)) (encode : A → B) :
    selectArm (value.mapAddress encode) arms =
      (selectArm value arms).map (fun (locals, expr) => (encodeEnv encode locals, expr)) := by
  induction arms with
  | nil => rfl
  | cons arm arms ih =>
      rcases arm with ⟨pattern, body⟩
      simp only [selectArm, Pattern.bindings_mapAddress]
      cases pattern.bindings value <;> simp [ih]

theorem projectValue_mapAddress (value : Value F A) (index : Nat) (encode : A → B) :
    projectValue (value.mapAddress encode) index = (projectValue value index).map (Value.mapAddress encode) := by
  cases value with
  | field | ptr | construct => simp [Value.mapAddress, projectValue, Except.map]
  | tuple items =>
      cases found : items[index]? <;> simp [Value.mapAddress, projectValue, List.getElem?_map, found, Except.map,
        pure, Except.pure]

theorem evalNeg_mapAddress [Field F] (value : Value F A) (encode : A → B) :
    evalNeg (value.mapAddress encode) = (evalNeg value).map (Value.mapAddress encode) := by
  cases value <;> simp [Value.mapAddress, evalNeg, Except.map]

theorem evalBinOp_mapAddress [Field F] [DecidableEq F]
    (op : BinOp) (left right : Value F A) (encode : A → B) :
    evalBinOp op (left.mapAddress encode) (right.mapAddress encode) =
      (evalBinOp op left right).map (Value.mapAddress encode) := by
  cases left <;> cases right <;> simp [Value.mapAddress, evalBinOp, Except.map]
  cases op <;> simp [Value.mapAddress]
  split <;> simp [Value.mapAddress]

theorem prepareCall_mapAddress [DecidableEq F] {program : Program F} {name : String} {args : List (Value F A)}
    {locals : Environment F A} {body : Expr F}
    (prepared : prepareCall program name args = .ok (locals, body)) (encode : A → B) :
    prepareCall program name (args.map (Value.mapAddress encode)) = .ok (encodeEnv encode locals, body) := by
  rcases prepareCall_spec prepared with function | table
  · obtain ⟨fn, found, types, formed, rfl, rfl⟩ := function
    have shape : fn.params.map Prod.snd = (args.map (Value.mapAddress encode)).map Value.type := by
      simpa only [List.map_map, Function.comp_def, Value.type_mapAddress] using types
    have prepared := prepareCall_of_types found shape (by
      intro value member
      obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
      simpa using formed source sourceMember)
    have localsMap : encodeEnv encode ((fn.params.map Prod.fst).zip args) =
        (fn.params.map Prod.fst).zip (args.map (Value.mapAddress encode)) := by
      simp only [encodeEnv, List.zip_map_right]
      exact List.map_congr_left (fun pair _ => by cases pair; rfl)
    simpa only [localsMap] using prepared
  · obtain ⟨value, absent, looked, rfl, rfl⟩ := table
    simpa only [encodeEnv, List.map_nil] using
      prepareCall_map absent ((lookupMap_mapAddress program name args encode).trans looked)

theorem EvalExpr.grows [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F Nat} {expr : Expr F} {before after : Heap F} {value : SourceValue F}
    (evaluated : EvalExpr program locals expr before value after) : before <+: after := by
  induction evaluated using EvalExpr.rec
    (motive_2 := fun _ _ before _ after _ => before <+: after)
    (motive_3 := fun _ _ before _ after _ => before <+: after) with
  | literal | var | nil => exact List.prefix_refl _
  | tuple _ ih | construct _ ih | project _ _ ih | neg _ _ ih | load _ _ ih | hint _ _ ih | intro _ _ ih => exact ih
  | letValue _ _ _ a b | binary _ _ _ a b | assertEq _ _ _ a b | call _ _ a b | matchValue _ _ _ a b | cons _ _ a b => exact a.trans b
  | store _ ih => exact ih.trans ⟨_, rfl⟩

theorem EvalFn.grows [Field F] [DecidableEq F] {program : Program F}
    {name : String} {args : List (SourceValue F)} {before after : Heap F} {value : SourceValue F}
    (evaluated : EvalFn program name args before value after) : before <+: after := by
  cases evaluated with
  | intro _ body => exact body.grows

theorem EvalArgs.grows [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F Nat} {exprs : List (Expr F)} {before after : Heap F} {values : List (SourceValue F)}
    (evaluated : EvalArgs program locals exprs before values after) : before <+: after := by
  exact (EvalExpr.tuple evaluated).grows

/-- Encode all allocated cells into one heterogeneous finite ROM. -/
def ROM.ofHeap (heap : Heap F) (encode : Nat → F) : ROM F :=
  ⟨List.ofFn (fun i : Fin heap.length => (encode i, heap[i].mapAddress encode))⟩

def HeapCells (rom : ROM F) (encode : Nat → F) (heap : Heap F) : Prop :=
  ∀ i value, heap[i]? = some value → (encode i, value.mapAddress encode) ∈ rom.entries

theorem ROM.ofHeap_cells (heap : Heap F) (encode : Nat → F) : HeapCells (ROM.ofHeap heap encode) encode heap := by
  intro i value found
  obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp found
  exact List.mem_ofFn.mpr ⟨⟨i, bound⟩, by simp [same]⟩

theorem ROM.ofHeap_valid (heap : Heap F) (encode : Nat → F)
    (injective : ∀ i j, i < heap.length → j < heap.length → encode i = encode j → i = j) :
    (ROM.ofHeap heap encode).Valid := by
  intro a ha b hb address _
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
  have same : i = j := Fin.ext (injective i j i.isLt j.isLt address)
  subst j
  rfl

end Aiur
