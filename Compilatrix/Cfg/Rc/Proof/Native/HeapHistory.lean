import Compilatrix.Cfg.Rc.Proof.Native.FrameState

/-! The history needed at a non-tail return. Physical slots may be recycled,
while old logical location mappings remain available for stale registers.
This relation composes across arbitrarily many allocations in a callee. -/
set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec
open Compilatrix.Cfg.Rc.Proof.Physical.Bridge Compilatrix.Rt.Rc.Procs

structure HeapHistory (oldSize : Nat) (oldAddresses : AddressMap)
    (newSize : Nat) (newAddresses : AddressMap) : Prop where
  growth : oldSize ≤ newSize
  retained : ∀ location, location < oldSize → newAddresses location = oldAddresses location

theorem HeapHistory.refl (size : Nat) (addresses : AddressMap) :
    HeapHistory size addresses size addresses := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem HeapHistory.trans {size₀ size₁ size₂ : Nat} {addresses₀ addresses₁ addresses₂ : AddressMap}
    (first : HeapHistory size₀ addresses₀ size₁ addresses₁)
    (second : HeapHistory size₁ addresses₁ size₂ addresses₂) :
    HeapHistory size₀ addresses₀ size₂ addresses₂ := by
  refine ⟨Nat.le_trans first.growth second.growth, ?_⟩
  intro location before
  exact (second.retained location (Nat.lt_of_lt_of_le before first.growth)).trans
    (first.retained location before)

theorem HeapHistory.allocate (H : Own.Heap) (body : Own.Body)
    (addresses : AddressMap) (address : Lir.Word) :
    HeapHistory H.size addresses (H.alloc .rc body).2.size
      (Native.placeFresh addresses H.size address) := by
  refine ⟨?_, ?_⟩
  · simp [Own.Heap.alloc, Own.Heap.size]
  · intro location before
    simp [Native.placeFresh, Nat.ne_of_lt before]

theorem HeapHistory.value {oldSize newSize : Nat} {oldAddresses newAddresses : AddressMap}
    (history : HeapHistory oldSize oldAddresses newSize newAddresses)
    {value : Own.RVal} (bounded : Own.Plain.Bounded oldSize value) :
    valueWord newAddresses value = valueWord oldAddresses value := by
  cases value with
  | loc location => exact history.retained location bounded
  | lit literal => cases literal <;> rfl
  | ctor0 ctor => rfl
  | erased => rfl

theorem HeapHistory.words {oldSize newSize bound : Nat} {oldAddresses newAddresses : AddressMap}
    (history : HeapHistory oldSize oldAddresses newSize newAddresses)
    {D : Nat → Prop} {source : Own.Env} {target : Lir.Env}
    (registers : FusedWords oldAddresses D bound source target)
    (bounded : Own.Plain.EnvBounded oldSize source) :
    FusedWords newAddresses D bound source target := by
  refine ⟨registers.dom, ?_⟩
  intro x value lookup live
  obtain ⟨word, represented, physical⟩ := registers.word lookup live
  exact ⟨word, (history.value (bounded x value lookup)).trans represented, physical⟩

theorem HeapHistory.frame {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    {oldSize newSize bound : Nat} {oldAddresses newAddresses : AddressMap}
    (history : HeapHistory oldSize oldAddresses newSize newAddresses)
    {function : Cfg.Fun} {source : Cfg.Frame} {target : Lir.Frame}
    (before : FrameState P pairs lp oldAddresses oldSize bound function source target) :
    FrameState P pairs lp newAddresses newSize bound function source target :=
  ⟨before.lookup, before.cursor, history.words before.words before.bounded,
    before.bounded.mono history.growth, before.compatible⟩

/-- The actual return instruction restores a saved caller after any composed
heap history. The target frame itself was never rewritten during the callee. -/
theorem HeapHistory.resume {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    {oldSize newSize bound : Nat} {oldAddresses newAddresses : AddressMap}
    (history : HeapHistory oldSize oldAddresses newSize newAddresses)
    {function : Cfg.Fun} {source : Cfg.Frame} {caller returning : Lir.Frame}
    (before : FrameState P pairs lp oldAddresses oldSize bound function source caller)
    {x : Nat} (destination : caller.dsts = [x]) (real : x < bound)
    {value : Own.RVal} {word : Lir.Word} (represented : valueWord newAddresses value = some word)
    (bounded : Own.Plain.Bounded newSize value) (compatible : ValueCtorOk (tablesOf P pairs) value)
    (returned : Rt.Proof.RetAt lp returning word)
    (memory : X86.Memory) (context : Lir.Word) (callers : List Lir.Frame) :
    let resumed := {caller with env := caller.env.insert x word, dsts := []}
    Lir.step lp {mem := memory, ctx := context, stack := returning :: caller :: callers} =
      .next {mem := memory, ctx := context, stack := resumed :: callers} false ∧
    FrameState P pairs lp newAddresses newSize bound function
      {source with env := source.env.insert x value} resumed :=
  (history.frame before).resume destination real represented bounded compatible returned memory context callers








end Compilatrix.Cfg.Rc.Native.Spec
