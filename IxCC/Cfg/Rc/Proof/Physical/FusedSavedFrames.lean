import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedWords
import IxCC.Cfg.Semantics

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc.Procs IxCC.Cfg.Rc.Proof.Physical.Bridge

/-- A saved activation records the entire source environment bound, its
physical register relation, and an independently supplied syntax/layout
witness for the exact return destination and target frame. `resume` is kept
opaque so the eventual raw lowering cursor can supply its own layout facts.
This relation contains no execution or desired post-state premise. -/
inductive FusedSavedFramesWords (addresses : AddressMap) (heapSize : Nat)
    (omitted : Cfg.Frame → Nat → Prop)
    (resume : Cfg.Frame → Fir.Var → Lir.Frame → Nat → Prop) :
    List (Cfg.Frame × Fir.Var) → List Lir.Frame → Prop
  | nil : FusedSavedFramesWords addresses heapSize omitted resume [] []
  | cons {source : Cfg.Frame} {destination : Fir.Var} {target : Lir.Frame} {bound : Nat}
      {sources : List (Cfg.Frame × Fir.Var)} {targets : List Lir.Frame}
      (bounded : Own.Plain.EnvBounded heapSize source.env)
      (registers : FusedWords addresses (omitted source) bound source.env target.env)
      (layout : resume source destination target bound)
      (rest : FusedSavedFramesWords addresses heapSize omitted resume sources targets) :
      FusedSavedFramesWords addresses heapSize omitted resume ((source, destination) :: sources) (target :: targets)

/-- Every entry in a suspended source frame, including stale bindings outside
its live roots, is below the old heap size. -/
theorem FusedSavedFramesWords.envBounded
    {addresses : AddressMap} {heapSize : Nat}
    {omitted : Cfg.Frame → Nat → Prop}
    {resume : Cfg.Frame → Fir.Var → Lir.Frame → Nat → Prop}
    {sources : List (Cfg.Frame × Fir.Var)} {targets : List Lir.Frame}
    (before : FusedSavedFramesWords addresses heapSize omitted resume sources targets)
    {source : Cfg.Frame} {destination : Fir.Var} (member : (source, destination) ∈ sources) :
    Own.Plain.EnvBounded heapSize source.env := by
  induction before with
  | nil => simp at member
  | @cons head dst target bound sources targets bounded registers layout rest ih =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      exact bounded
    · exact ih member

/-- All physical frames stay literally identical across publication. In
particular fn/label/pos/dsts and the opaque return layout witness are retained;
only the interpretation map and source-location bound grow. -/
theorem FusedSavedFramesWords.placeFresh
    {addresses : AddressMap} {oldSize newSize : Nat}
    {omitted : Cfg.Frame → Nat → Prop}
    {resume : Cfg.Frame → Fir.Var → Lir.Frame → Nat → Prop}
    {sources : List (Cfg.Frame × Fir.Var)} {targets : List Lir.Frame}
    (before : FusedSavedFramesWords addresses oldSize omitted resume sources targets)
    (grown : oldSize ≤ newSize) (address : Lir.Word) :
    FusedSavedFramesWords (IxCC.Cfg.Rc.Native.placeFresh addresses oldSize address)
      newSize omitted resume sources targets := by
  induction before with
  | nil => exact .nil
  | cons bounded registers layout rest ih =>
    exact .cons (bounded.mono grown) (registers.placeFresh bounded address) layout ih

/-- The actual logical allocation result establishes the fresh location and
new bound. Its extended map preserves every saved source/target frame and
resume witness, and every old value's pointer/immediate representation. -/
theorem fused_allocation_saved_frames
    {H : Own.Heap} {body : Own.Body} {allocated : Own.RVal × Own.Heap}
    (result : H.alloc .rc body = allocated)
    {addresses : AddressMap}
    {omitted : Cfg.Frame → Nat → Prop}
    {resume : Cfg.Frame → Fir.Var → Lir.Frame → Nat → Prop}
    {sources : List (Cfg.Frame × Fir.Var)} {targets : List Lir.Frame}
    (before : FusedSavedFramesWords addresses H.size omitted resume sources targets)
    (address : Lir.Word) :
    allocated.1 = .loc H.size ∧ allocated.2.size = H.size + 1 ∧
      valueWord (placeFresh addresses H.size address) allocated.1 = some address ∧
      FusedSavedFramesWords (placeFresh addresses H.size address) allocated.2.size omitted resume sources targets ∧
      (∀ value, Own.Plain.Bounded H.size value →
        valueWord (placeFresh addresses H.size address) value = valueWord addresses value) ∧
      (∀ source destination, (source, destination) ∈ sources →
        ∀ x value, source.env.get? x = some value →
          valueWord (placeFresh addresses H.size address) value = valueWord addresses value) := by
  subst allocated
  have size : (H.alloc .rc body).2.size = H.size + 1 := by simp [Own.Heap.alloc, Own.Heap.size]
  refine ⟨rfl, size, placeFresh_new addresses H.size address,
    before.placeFresh (by omega) address, ?_, ?_⟩
  · intro value bounded
    exact placeFresh_old bounded
  · intro source destination member x value lookup
    exact placeFresh_old (before.envBounded member x value lookup)




end IxCC.Cfg.Rc.Native
