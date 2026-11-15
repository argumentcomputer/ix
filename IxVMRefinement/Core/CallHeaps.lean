import IxVMRefinement.Core.Obs

/-! # Heap bounds for observed subcalls

Every recorded call starts between the caller's initial and final heaps. This lets record
representations move to a selected subcall without rebuilding the whole allocation chain.
-/

namespace Aiur.Generic.SourceSemantics

variable {F : Type}

private def HeapTrace (before after : Heap F) (calls : List (Call F)) : Prop :=
  Heap.Extends before after ∧
    ∀ cl ∈ calls, Heap.Extends before cl.heap ∧ Heap.Extends cl.heap after

private theorem HeapTrace.refl (heap : Heap F) : HeapTrace heap heap [] :=
  ⟨Heap.Extends.refl _, fun _ h => nomatch h⟩

private theorem HeapTrace.seq {before middle after : Heap F} {left right : List (Call F)}
    (hleft : HeapTrace before middle left) (hright : HeapTrace middle after right) :
    HeapTrace before after (left ++ right) := by
  refine ⟨hleft.1.trans hright.1, ?_⟩
  intro cl hcl
  rcases List.mem_append.mp hcl with hcl | hcl
  · obtain ⟨hin, hout⟩ := hleft.2 cl hcl
    exact ⟨hin, hout.trans hright.1⟩
  · obtain ⟨hin, hout⟩ := hright.2 cl hcl
    exact ⟨hleft.1.trans hin, hout⟩

private theorem HeapTrace.extend {before middle after : Heap F} {calls : List (Call F)}
    (h : HeapTrace before middle calls) (hext : Heap.Extends middle after) :
    HeapTrace before after calls :=
  ⟨h.1.trans hext, fun cl hm => ⟨(h.2 cl hm).1, (h.2 cl hm).2.trans hext⟩⟩

variable [Field F] [DecidableEq F]

private theorem ObsFn.heap_trace {world : World F} {name : String}
    {args : List (SourceValue F)} {before after : Heap F}
    {result : SourceValue F} {calls : List (Call F)}
    (evaluated : ObsFn world name args before result after calls) :
    HeapTrace before after calls := by
  induction evaluated using ObsFn.rec
    (motive_1 := fun _ _ _ before _ after calls _ => HeapTrace before after calls)
    (motive_2 := fun _ _ _ before _ after calls _ => HeapTrace before after calls)
    (motive_4 := fun _ _ _ before _ _ after calls _ => HeapTrace before after calls)
    (motive_5 := fun _ _ _ before _ _ after calls _ => HeapTrace before after calls) with
  | literal | var | nil => exact HeapTrace.refl _
  | block _ ih
  | blockExit _ ih
  | global _ _ _ ih
  | tuple _ ih
  | array _ ih
  | «repeat» _ ih
  | index _ _ ih
  | slice _ _ ih
  | builtin _ _ ih
  | update _ _ ih
  | record _ ih
  | member _ _ ih
  | construct _ ih
  | constructAs _ ih
  | project _ _ ih
  | load _ _ ih
  | hint _ _ ih
  | neg _ _ ih
  | intro _ _ ih
  | returned _ _ ih
  | exit _ ih
  | exitPayload _ ih
  | fromBlock _ _ ih
  | fromGlobal _ _ _ ih
  | fromTuple _ ih
  | fromArray _ ih
  | fromRepeat _ ih
  | fromIndex _ ih
  | fromSlice _ ih
  | fromBuiltin _ ih
  | fromUpdate _ ih
  | fromRecord _ ih
  | fromMember _ ih
  | fromConstruct _ ih
  | fromConstructAs _ ih
  | fromProject _ ih
  | fromLetValue _ ih
  | fromStore _ ih
  | fromLoad _ ih
  | fromHint _ ih
  | fromNeg _ ih
  | binaryLeft _ ih
  | fromCall _ ih
  | fromMatchValue _ ih
  | head _ ih => exact ih
  | letValue _ _ _ ih₁ ih₂
  | binary _ _ _ ih₁ ih₂
  | matchValue _ _ _ ih₁ ih₂
  | cons _ _ ih₁ ih₂
  | letBody _ _ _ ih₁ ih₂
  | binaryRight _ _ ih₁ ih₂
  | matchBody _ _ _ ih₁ ih₂
  | tail _ _ ih₁ ih₂ => exact ih₁.seq ih₂
  | store _ ih => exact ih.extend (Heap.Extends.snoc _ _)
  | call _ _ ih₁ ih₂ =>
    refine ⟨ih₁.1.trans ih₂.1, ?_⟩
    intro cl hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨hin, hout⟩ := ih₁.2 cl hm
      exact ⟨hin, hout.trans ih₂.1⟩
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨ih₁.1, ih₂.1⟩
      · obtain ⟨hin, hout⟩ := ih₂.2 cl hm
        exact ⟨ih₁.1.trans hin, hout⟩

/-- A recorded subcall's input heap extends the caller's input heap and is extended by
the caller's output heap. No semantic environment or load invariant is needed. -/
theorem ObsFn.call_heap_bounds {world : World F} {name : String}
    {args : List (SourceValue F)} {before after : Heap F} {result : SourceValue F}
    {calls : List (Call F)} (evaluated : ObsFn world name args before result after calls)
    {cl : Call F} (hmem : cl ∈ calls) :
    Heap.Extends before cl.heap ∧ Heap.Extends cl.heap after :=
  evaluated.heap_trace.2 cl hmem

end Aiur.Generic.SourceSemantics
