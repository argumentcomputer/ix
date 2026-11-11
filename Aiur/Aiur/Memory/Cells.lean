import Aiur.Memory.Soundness

/-!
# Realized heaps live in the ROM

`ROMEvalExpr.realize` turns a ROM-level evaluation into a source evaluation by
fresh allocations. Every allocation stores a value that a ROM cell represents.
`HeapInROM rom heap` records this for a whole heap: cell `i` is represented by a
ROM cell relative to the heap up to and including cell `i`, so every prefix of
the heap that contains the cell can represent a pointer to it.

`ROMEvalCall.realizeCells` is `ROMEvalCall.realize` with that fact added.
-/

namespace Aiur

variable {F : Type} {rom : ROM F}

/-- Every cell of `heap` from `start` on is a ROM cell, represented relative to
the heap up to it. -/
def CellsInROM (rom : ROM F) (start : Nat) (heap : Heap F) : Prop :=
  ∀ i stored, start ≤ i → heap[i]? = some stored →
    ∃ address encoded, (address, encoded) ∈ rom.entries ∧
      Represents rom (heap.take (i + 1)) stored encoded

/-- Every cell of `heap` is a ROM cell, represented relative to the heap up to it. -/
abbrev HeapInROM (rom : ROM F) (heap : Heap F) : Prop := CellsInROM rom 0 heap

theorem CellsInROM.empty (heap : Heap F) : CellsInROM rom heap.length heap := by
  intro i stored inside found
  have := (List.getElem?_eq_some_iff.mp found).1
  omega

theorem CellsInROM.trans {start : Nat} {middle after : Heap F} (first : CellsInROM rom start middle)
    (second : CellsInROM rom middle.length after) (grows : middle <+: after) :
    CellsInROM rom start after := by
  intro i stored inside found
  by_cases early : i < middle.length
  · obtain ⟨rest, rfl⟩ := grows
    have same : middle[i]? = some stored := by rwa [List.getElem?_append_left early] at found
    obtain ⟨address, encoded, cell, related⟩ := first i stored inside same
    refine ⟨address, encoded, cell, ?_⟩
    rwa [List.take_append_of_le_length (by omega)]
  · exact second i stored (by omega) found

theorem CellsInROM.snoc {start : Nat} {heap : Heap F} {stored : SourceValue F} {address : F}
    {encoded : Value F} (cells : CellsInROM rom start heap) (cell : (address, encoded) ∈ rom.entries)
    (related : Represents rom (heap ++ [stored]) stored encoded) :
    CellsInROM rom start (heap ++ [stored]) := by
  apply cells.trans _ ⟨[stored], rfl⟩
  intro i value inside found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  simp only [List.length_append, List.length_singleton] at bound
  obtain rfl : i = heap.length := by omega
  simp only [List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero,
    Option.some.injEq] at found
  subst found
  refine ⟨address, encoded, cell, ?_⟩
  rw [List.take_of_length_le (by simp)]
  exact related

private theorem option_related_some {R : α → β → Prop} {source : Option α} {target : β}
    (related : Option.Rel R source (some target)) : ∃ value, source = some value ∧ R value target := by
  cases related with
  | some relation => exact ⟨_, rfl, relation⟩

/-- `ROMEvalExpr.realize`, also recording that every new cell is a ROM cell. -/
theorem ROMEvalExpr.realizeCells [Field F] [DecidableEq F] (valid : rom.Valid)
    {program : Program F} {locals : Environment F} {expr : Expr F} {target : Value F}
    (evaluated : ROMEvalExpr rom program locals expr target) :
    ∀ heap sourceLocals, RepresentsEnv rom heap sourceLocals locals →
      ∃ source after, EvalExpr program sourceLocals expr heap source after ∧ heap <+: after ∧
        Represents rom after source target ∧ CellsInROM rom heap.length after := by
  induction evaluated using ROMEvalExpr.rec
    (motive_2 := fun locals exprs targets _ => ∀ heap sourceLocals,
      RepresentsEnv rom heap sourceLocals locals →
      ∃ sources after, EvalArgs program sourceLocals exprs heap sources after ∧ heap <+: after ∧
        RepresentsArgs rom after sources targets ∧ CellsInROM rom heap.length after)
    (motive_3 := fun name targets result _ => ∀ heap sources,
      RepresentsArgs rom heap sources targets →
      ∃ source after, EvalFn program name sources heap source after ∧ heap <+: after ∧
        Represents rom after source result ∧ CellsInROM rom heap.length after) with
  | literal =>
      intro heap locals _
      exact ⟨_, heap, .literal, List.prefix_refl _, .field, CellsInROM.empty heap⟩
  | var found =>
      intro heap locals related
      obtain ⟨source, lookup, related⟩ := related.lookup found
      exact ⟨source, heap, .var lookup, List.prefix_refl _, related, CellsInROM.empty heap⟩
  | tuple _ ih =>
      intro heap locals related
      obtain ⟨sources, after, evaluated, grows, results, cells⟩ := ih heap locals related
      exact ⟨.tuple sources, after, .tuple evaluated, grows, .tuple results, cells⟩
  | construct _ ih =>
      intro heap locals related
      obtain ⟨sources, after, evaluated, grows, results, cells⟩ := ih heap locals related
      exact ⟨_, after, .construct evaluated, grows, .construct results, cells⟩
  | project _ projected ih =>
      intro heap locals related
      obtain ⟨source, after, evaluated, grows, result, cells⟩ := ih heap locals related
      obtain ⟨value, projected, result⟩ := result.project projected
      exact ⟨value, after, .project evaluated projected, grows, result, cells⟩
  | letValue _ matched _ valueIH bodyIH =>
      intro heap locals related
      obtain ⟨source, middle, valueEval, first, input, cells₁⟩ := valueIH heap locals related
      obtain ⟨bindings, matchSource, bindingRep⟩ := option_related_some
        (by rw [← matched]; exact Pattern.represents _ input)
      obtain ⟨result, after, bodyEval, second, output, cells₂⟩ :=
        bodyIH middle (bindings ++ locals) (List.rel_append bindingRep (related.mono first))
      exact ⟨result, after, .letValue valueEval matchSource bodyEval, first.trans second, output,
        cells₁.trans cells₂ second⟩
  | store _ cell ih =>
      intro heap locals related
      obtain ⟨source, middle, evaluated, grows, result, cells⟩ := ih heap locals related
      have appends : middle <+: middle ++ [source] := ⟨[source], rfl⟩
      exact ⟨.ptr source.type middle.length, middle ++ [source], .store evaluated,
        grows.trans appends, .ptr (by simp) cell (result.mono appends),
        cells.snoc cell (result.mono appends)⟩
  | load _ cell shape ih =>
      intro heap locals related
      obtain ⟨pointer, after, evaluated, grows, pointerRep, cells⟩ := ih heap locals related
      cases pointerRep with
      | ptr source stored content =>
          have same := ROM.functional valid stored cell shape.symm
          subst_vars
          exact ⟨_, after, .load evaluated (by simp [loadValue, source, pure, Except.pure, bind,
            Except.bind]), grows, content, cells⟩
  | neg _ operation ih =>
      intro heap locals related
      obtain ⟨source, after, evaluated, grows, result, cells⟩ := ih heap locals related
      obtain ⟨value, operation, result⟩ := result.neg operation
      exact ⟨value, after, .neg evaluated operation, grows, result, cells⟩
  | @hint locals expr input type channel _ constant typed ih =>
      intro heap sourceLocals related
      obtain ⟨key, after, keyEval, grows, _, cells⟩ := ih heap sourceLocals related
      refine ⟨constant.toValue, after, .hint keyEval typed, grows, ?_, cells⟩
      simpa only [Constant.toValue_mapAddress] using
        (Represents.of_pointerFree (rom := rom) (heap := after) constant.toValue
          (Constant.toValue_pointerFree constant) (fun _ => (0 : F)))
  | assertEq _ _ operation leftIH rightIH =>
      intro heap locals related
      obtain ⟨left, middle, leftEval, first, leftRep, cells₁⟩ := leftIH heap locals related
      obtain ⟨right, after, rightEval, second, rightRep, cells₂⟩ :=
        rightIH middle locals (related.mono first)
      obtain ⟨value, operation, result⟩ := (leftRep.mono second).assertEq rightRep operation
      exact ⟨value, after, .assertEq leftEval rightEval operation, first.trans second, result,
        cells₁.trans cells₂ second⟩
  | binary _ _ operation leftIH rightIH =>
      intro heap locals related
      obtain ⟨left, middle, leftEval, first, leftRep, cells₁⟩ := leftIH heap locals related
      obtain ⟨right, after, rightEval, second, rightRep, cells₂⟩ :=
        rightIH middle locals (related.mono first)
      obtain ⟨value, operation, result⟩ := (leftRep.mono second).binary rightRep operation
      exact ⟨value, after, .binary leftEval rightEval operation, first.trans second, result,
        cells₁.trans cells₂ second⟩
  | call _ _ argsIH callIH =>
      intro heap locals related
      obtain ⟨args, middle, argsEval, first, argsRep, cells₁⟩ := argsIH heap locals related
      obtain ⟨value, after, callEval, second, result, cells₂⟩ := callIH middle args argsRep
      exact ⟨value, after, .call argsEval callEval, first.trans second, result,
        cells₁.trans cells₂ second⟩
  | matchValue _ selected _ valueIH bodyIH =>
      intro heap locals related
      obtain ⟨source, middle, valueEval, first, input, cells₁⟩ := valueIH heap locals related
      obtain ⟨⟨bindings, body⟩, selectedSource, bindingRep, same⟩ := option_related_some
        (by rw [← selected]; exact selectArm_represents input _)
      dsimp at same
      subst body
      obtain ⟨result, after, bodyEval, second, output, cells₂⟩ :=
        bodyIH middle (bindings ++ locals) (List.rel_append bindingRep (related.mono first))
      exact ⟨result, after, .matchValue valueEval selectedSource bodyEval, first.trans second, output,
        cells₁.trans cells₂ second⟩
  | nil =>
      rename_i heap locals related
      exact ⟨[], heap, .nil, List.prefix_refl _, .nil, CellsInROM.empty heap⟩
  | cons _ _ headIH tailIH =>
      rename_i heap locals related
      obtain ⟨head, middle, headEval, first, headRep, cells₁⟩ := headIH heap locals related
      obtain ⟨tail, after, tailEval, second, tailRep, cells₂⟩ := tailIH middle locals (related.mono first)
      exact ⟨head :: tail, after, .cons headEval tailEval, first.trans second,
        .cons (headRep.mono second) tailRep, cells₁.trans cells₂ second⟩
  | intro prepared _ bodyIH =>
      rename_i heap sources related
      obtain ⟨locals, preparedSource, environment⟩ := prepareCall_represents related prepared
      obtain ⟨value, after, evaluated, grows, result, cells⟩ := bodyIH heap locals environment
      exact ⟨value, after, .intro preparedSource evaluated, grows, result, cells⟩

/-- `ROMEvalCall.realize`, also recording that every new cell is a ROM cell. -/
theorem ROMEvalCall.realizeCells [Field F] [DecidableEq F] (valid : rom.Valid)
    {program : Program F} {name : String} {args : List (Value F)} {result : Value F}
    (evaluated : ROMEvalCall rom program name args result)
    {heap : Heap F} {sources : List (SourceValue F)} (related : RepresentsArgs rom heap sources args) :
    ∃ source after, EvalFn program name sources heap source after ∧ heap <+: after ∧
      Represents rom after source result ∧ CellsInROM rom heap.length after := by
  cases evaluated with
  | intro prepared body =>
      obtain ⟨locals, prepareSource, environment⟩ := prepareCall_represents related prepared
      obtain ⟨source, after, evaluated, grows, output, cells⟩ :=
        body.realizeCells valid heap locals environment
      exact ⟨source, after, .intro prepareSource evaluated, grows, output, cells⟩

end Aiur
