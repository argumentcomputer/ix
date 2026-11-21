import Aiur.Memory.Encoding
import Aiur.Memory.Representation
import Mathlib.Data.Fintype.EquivFin

namespace Aiur

variable {F : Type} {rom : ROM F} {encode : Nat → F}

theorem HeapCells.of_prefix {before after : Heap F} (cells : HeapCells rom encode after)
    (grows : before <+: after) : HeapCells rom encode before :=
  fun i value found => cells i value (heap_get_of_prefix grows found)

private theorem distinct_of_prefix {before after : Heap F} {encode : Nat → F}
    (distinct : ∀ i j, i < after.length → j < after.length → encode i = encode j → i = j)
    (grows : before <+: after) :
    ∀ i j, i < before.length → j < before.length → encode i = encode j → i = j := by
  intro i j hi hj heq
  obtain ⟨suffix, rfl⟩ := grows
  exact distinct i j (by simp only [List.length_append]; omega)
    (by simp only [List.length_append]; omega) heq

/-- An exact-address source execution can be interpreted against any
table containing its encoded heap under an injective address map. -/
theorem ExactEvalExpr.toROM [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F Nat} {expr : Expr F} {before after : Heap F} {value : SourceValue F}
    (evaluated : ExactEvalExpr program locals expr before value after) :
    HeapCells rom encode after →
    (∀ i j, i < after.length → j < after.length → encode i = encode j → i = j) →
      ROMEvalExpr rom program (encodeEnv encode locals) expr (value.mapAddress encode) := by
  induction evaluated using ExactEvalExpr.rec
    (motive_2 := fun locals exprs before values after _ =>
      HeapCells rom encode after →
      (∀ i j, i < after.length → j < after.length → encode i = encode j → i = j) →
      ROMEvalArgs rom program (encodeEnv encode locals) exprs (values.map (Value.mapAddress encode)))
    (motive_3 := fun name args before value after _ =>
      HeapCells rom encode after →
      (∀ i j, i < after.length → j < after.length → encode i = encode j → i = j) →
      ROMEvalCall rom program name (args.map (Value.mapAddress encode)) (value.mapAddress encode)) with
  | literal => intro _ _; simpa only [Value.mapAddress] using ROMEvalExpr.literal
  | var found =>
      intro _ _
      apply ROMEvalExpr.var
      simp [encodeEnv, List.find?_map, Function.comp_def, found]
  | tuple _ ih =>
      intro cells distinct
      simpa only [Value.mapAddress] using ROMEvalExpr.tuple (ih cells distinct)
  | construct _ ih =>
      intro cells distinct
      simpa only [Value.mapAddress] using ROMEvalExpr.construct (ih cells distinct)
  | project _ projected ih =>
      intro cells distinct
      refine .project (ih cells distinct) ?_
      rw [projectValue_mapAddress, projected]
      rfl
  | letValue _ matched body valueIH bodyIH =>
      intro cells distinct
      have mapped := congrArg (Option.map (encodeEnv encode)) matched
      rw [← Pattern.bindings_mapAddress] at mapped
      simp only [Option.map_some] at mapped
      have hg := body.toEvalExpr.grows
      refine .letValue (valueIH (cells.of_prefix hg) (distinct_of_prefix distinct hg)) mapped ?_
      simpa only [encodeEnv_append] using bodyIH cells distinct
  | @store locals expr before input middle value ih =>
      intro cells distinct
      have grow : middle <+: middle ++ [input] := ⟨[input], rfl⟩
      have cell := cells middle.length input (by simp)
      simpa only [Value.mapAddress, Value.type_mapAddress] using
        ROMEvalExpr.store (ih (cells.of_prefix grow) (distinct_of_prefix distinct grow)) cell
  | @load locals expr before input after result pointer loaded ih =>
      intro cells distinct
      cases input with
      | field | tuple | construct => cases loaded
      | ptr target address =>
          cases found : after[address]? with
          | none => simp [loadValue, found] at loaded
          | some stored =>
              by_cases typed : stored.type = target
              · simp [loadValue, found, typed, pure, Except.pure, bind, Except.bind] at loaded
                subst result
                exact .load (by simpa only [Value.mapAddress] using ih cells distinct)
                  (cells address stored found) (by simpa only [Value.type_mapAddress] using typed)
              · simp [loadValue, found, typed] at loaded
  | neg _ operation ih =>
      intro cells distinct
      refine .neg (ih cells distinct) ?_
      rw [evalNeg_mapAddress, operation]; rfl
  | hint _ typed ih =>
      intro cells distinct
      simpa only [Constant.toValue_mapAddress] using ROMEvalExpr.hint (ih cells distinct) typed
  | assertEq _ right operation leftIH rightIH =>
      intro cells distinct
      have hg := right.toEvalExpr.grows
      refine .assertEq (leftIH (cells.of_prefix hg) (distinct_of_prefix distinct hg))
        (rightIH cells distinct) ?_
      exact evalAssertEq_mapAddress operation encode
  | @ptrEq locals lhs before middle rhs after target a₁ a₂ left right h1 h2 leftIH rightIH =>
      intro cells distinct
      have hg := right.toEvalExpr.grows
      have hLeft := leftIH (cells.of_prefix hg) (distinct_of_prefix distinct hg)
      have hRight := rightIH cells distinct
      simp only [Value.mapAddress] at hLeft hRight ⊢
      have hiff : encode a₁ = encode a₂ ↔ a₁ = a₂ :=
        ⟨fun h => distinct a₁ a₂ h1 h2 h, fun h => congrArg encode h⟩
      have hres : (if a₁ = a₂ then (1 : F) else 0) = (if encode a₁ = encode a₂ then 1 else 0) := by
        by_cases h : a₁ = a₂
        · simp [h, hiff.mpr h]
        · have hne : encode a₁ ≠ encode a₂ := fun heq => h (hiff.mp heq)
          simp [h, hne]
      rw [hres]
      exact ROMEvalExpr.ptrEq hLeft hRight
  | binary _ right operation leftIH rightIH =>
      intro cells distinct
      have hg := right.toEvalExpr.grows
      refine .binary (leftIH (cells.of_prefix hg) (distinct_of_prefix distinct hg))
        (rightIH cells distinct) ?_
      rw [evalBinOp_mapAddress, operation]; rfl
  | call _ callee argsIH callIH =>
      intro cells distinct
      have hg := callee.toEvalFn.grows
      exact .call (argsIH (cells.of_prefix hg) (distinct_of_prefix distinct hg))
        (callIH cells distinct)
  | matchValue _ selected branch valueIH bodyIH =>
      intro cells distinct
      have mapped := congrArg (Option.map (fun (locals, expr) => (encodeEnv encode locals, expr))) selected
      rw [← selectArm_mapAddress] at mapped
      simp only [Option.map_some] at mapped
      have hg := branch.toEvalExpr.grows
      refine .matchValue (valueIH (cells.of_prefix hg) (distinct_of_prefix distinct hg)) mapped ?_
      simpa only [encodeEnv_append] using bodyIH cells distinct
  | nil => exact .nil
  | cons _ tail headIH tailIH =>
      rename_i cells distinct
      have hg := (ExactEvalExpr.toEvalExpr (ExactEvalExpr.tuple tail)).grows
      exact .cons (headIH (cells.of_prefix hg) (distinct_of_prefix distinct hg))
        (tailIH cells distinct)
  | intro prepared _ bodyIH =>
      rename_i cells distinct
      exact .intro (prepareCall_mapAddress prepared encode) (bodyIH cells distinct)

theorem ExactEvalFn.toROM [Field F] [DecidableEq F] {program : Program F}
    {name : String} {args : List (SourceValue F)} {before after : Heap F} {value : SourceValue F}
    (evaluated : ExactEvalFn program name args before value after)
    (cells : HeapCells rom encode after)
    (distinct : ∀ i j, i < after.length → j < after.length → encode i = encode j → i = j) :
    ROMEvalCall rom program name (args.map (Value.mapAddress encode)) (value.mapAddress encode) := by
  cases evaluated with
  | intro prepared body => exact .intro (prepareCall_mapAddress prepared encode) (body.toROM cells distinct)

@[simp] theorem Constant.toExpr_ptrEqFree (value : Constant F) : value.toExpr.ptrEqFree = true := by
  cases value with
  | field => simp [Constant.toExpr, Expr.ptrEqFree]
  | ptr _ address => exact Empty.elim address
  | tuple values | construct _ _ values =>
      simp only [Constant.toExpr, Expr.ptrEqFree, List.map_map, List.all_map, List.all_eq_true]
      exact fun value _ => Constant.toExpr_ptrEqFree value
termination_by sizeOf value

theorem prepareCall_ptrEqFree [DecidableEq F] {program : Program F}
    (free : program.ptrEqFree = true) {name : String} {args : List (Value F A)}
    {locals : Environment F A} {body : Expr F}
    (prepared : prepareCall program name args = .ok (locals, body)) : body.ptrEqFree = true := by
  rcases prepareCall_spec prepared with function | table
  · obtain ⟨function, found, _, _, _, rfl⟩ := function
    exact (by simpa [Program.ptrEqFree] using free : ∀ f ∈ program.functions, f.body.ptrEqFree = true)
      function (List.mem_of_find?_eq_some found)
  · obtain ⟨value, _, _, _, rfl⟩ := table
    exact value.toExpr_ptrEqFree

theorem selectArm_ptrEqFree [DecidableEq F] {value : Value F A}
    {arms : List (Pattern F × Expr F)} {bindings : Environment F A} {body : Expr F}
    (free : ∀ arm ∈ arms, arm.2.ptrEqFree = true)
    (selected : selectArm value arms = some (bindings, body)) : body.ptrEqFree = true := by
  induction arms with
  | nil => cases selected
  | cons arm arms ih =>
      simp only [selectArm] at selected
      split at selected
      · cases selected; exact free arm (by simp)
      · exact ih (fun a h => free a (by simp [h])) selected

/-- Every evaluation of a `ptr_eq`-free program lifts directly to an exact-address derivation. -/
theorem EvalExpr.toExact_of_ptrEqFree [Field F] [DecidableEq F] {program : Program F}
    (progFree : program.ptrEqFree = true)
    {locals : Environment F Nat} {expr : Expr F} {before after : Heap F} {value : SourceValue F}
    (evaluated : EvalExpr program locals expr before value after) :
    expr.ptrEqFree = true → ExactEvalExpr program locals expr before value after := by
  induction evaluated using EvalExpr.rec
    (motive_2 := fun l exprs b vs a _ =>
      (∀ e ∈ exprs, e.ptrEqFree = true) → ExactEvalArgs program l exprs b vs a)
    (motive_3 := fun n as b v a _ => ExactEvalFn program n as b v a) with
  | literal => intro _; exact .literal
  | var found => intro _; exact .var found
  | tuple _ ih => intro h; exact .tuple (ih (by simpa [Expr.ptrEqFree] using h))
  | construct _ ih => intro h; exact .construct (ih (by simpa [Expr.ptrEqFree] using h))
  | project _ p ih => intro h; exact .project (ih (by simpa [Expr.ptrEqFree] using h)) p
  | store _ ih => intro h; exact .store (ih (by simpa [Expr.ptrEqFree] using h))
  | load _ l ih => intro h; exact .load (ih (by simpa [Expr.ptrEqFree] using h)) l
  | hint _ t ih => intro h; exact .hint (ih (by simpa [Expr.ptrEqFree] using h)) t
  | neg _ n ih => intro h; exact .neg (ih (by simpa [Expr.ptrEqFree] using h)) n
  | letValue _ m _ vIH bIH =>
      intro h
      simp only [Expr.ptrEqFree, Bool.and_eq_true] at h
      exact .letValue (vIH h.1) m (bIH h.2)
  | assertEq _ _ eq vIH bIH =>
      intro h
      simp only [Expr.ptrEqFree, Bool.and_eq_true] at h
      exact .assertEq (vIH h.1) (bIH h.2) eq
  | binary _ _ op vIH bIH =>
      intro h
      simp only [Expr.ptrEqFree, Bool.and_eq_true] at h
      exact .binary (vIH h.1) (bIH h.2) op
  | ptrEq => intro h; simp [Expr.ptrEqFree] at h
  | call _ _ aIH cIH =>
      intro h
      exact .call (aIH (by simpa [Expr.ptrEqFree] using h)) cIH
  | matchValue _ selected _ vIH bIH =>
      intro h
      simp only [Expr.ptrEqFree, Bool.and_eq_true, List.all_eq_true, List.mem_map] at h
      exact .matchValue (vIH h.1) selected (bIH (selectArm_ptrEqFree (fun arm hm => h.2 _ ⟨arm, hm, rfl⟩) selected))
  | nil => exact .nil
  | cons _ _ hIH tIH =>
      rename_i hall
      exact .cons (hIH (hall _ (by simp))) (tIH (fun e he => hall e (by simp [he])))
  | intro prepared _ bIH =>
      exact .intro prepared (bIH (prepareCall_ptrEqFree progFree prepared))

theorem EvalFn.toExact_of_ptrEqFree [Field F] [DecidableEq F] {program : Program F}
    (progFree : program.ptrEqFree = true)
    {name : String} {args : List (SourceValue F)} {before after : Heap F} {value : SourceValue F}
    (evaluated : EvalFn program name args before value after) :
    ExactEvalFn program name args before value after := by
  cases evaluated with
  | intro prepared body =>
      exact .intro prepared (body.toExact_of_ptrEqFree progFree (prepareCall_ptrEqFree progFree prepared))

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
