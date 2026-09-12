import Compilatrix.X86.HeapPrimitives

namespace Compilatrix.X86.HeapPrimitives
open WordRegion PhysicalHeap HeapArena HeapMacros

structure Environment (layout : HeapArena.Layout) (frame : Scalar.Frame layout.region)
    (state : State) (holes : Stream.Holes) (returns : List ReturnFrame) (rootTop : Nat) : Prop where
  framed : Scalar.Framed frame state
  based : Based layout state
  safe : Scalar.HolesIn layout.region rootTop holes
  frames : Scalar.FramesAbove layout.region frame.top returns
  access : Access layout holes returns
  separate : heapWords ≤ frame.stackIndex
  below : frame.top ≤ rootTop

theorem Environment.advance {layout frame before after holes returns rootTop}
    (environment : Environment layout frame before holes returns rootTop) (stable : Scalar.Stable before after) :
    Environment layout frame after holes returns rootTop :=
  ⟨stable.framed environment.framed, environment.based.stable stable, environment.safe, environment.frames,
    environment.access, environment.separate, environment.below⟩

theorem Environment.save {layout frame state holes returns rootTop destination}
    (environment : Environment layout frame state holes returns rootTop) (bound : destination < Scalar.maxLocals) :
    SafeTrace layout.region returns [.spill (Scalar.slot destination) .rax] state holes (save frame state destination) holes :=
  save_trace environment.framed environment.safe environment.frames bound

theorem Environment.tag {layout frame state holes returns rootTop index}
    (environment : Environment layout frame state holes returns rootTop) (allocated : index < capacity)
    (pointer : state.registers .rax = layout.pointer index) (word : Word) :
    SafeTrace layout.region returns (HeapTarget.setTag word) state holes (tag state index word) holes :=
  tag_trace environment.access allocated pointer word

theorem Environment.writeCell {layout frame state holes returns rootTop index}
    (environment : Environment layout frame state holes returns rootTop) (allocated : index < capacity)
    (pointer : state.registers .rax = layout.pointer index) (ctor : Constructor) :
    SafeTrace layout.region returns (HeapTarget.writeCell ctor) state holes (writeCell state index ctor) holes :=
  writeCell_trace environment.access allocated pointer ctor

/-- The operation relation states only finite slot effects and the address
facts needed by the primitive. It does not contain an x86 execution premise. -/
inductive Executes (layout : HeapArena.Layout) (frame : Scalar.Frame layout.region) : Primitive → State → State → Prop where
  | nop (state) : Executes layout frame .nop state state
  | move (state destination source) : Executes layout frame (.move destination source) state
      (save frame (load frame state source) destination)
  | alloc (state index world ctor arguments destination)
      (allocated : index < capacity) (cursor : state.words 0 = UInt64.ofNat (32 * index)) :
      Executes layout frame (.alloc world ctor arguments destination) state
        (allocate layout frame state index ctor arguments destination)
  | fetch (state index source field destination) (allocated : index < capacity)
      (pointer : HeapCopies.atomValue frame state source = layout.pointer index) :
      Executes layout frame (.fetch source field destination) state (fetch frame state index source field destination)
  | reserve (state index world ctor source destination credit) (allocated : index < capacity)
      (pointer : HeapCopies.atomValue frame state source = layout.pointer index) :
      Executes layout frame (.reserve world ctor source destination credit) state
        (reserve frame state index world ctor source destination credit)
  | reuse (state index world ctor credit arguments destination) (allocated : index < capacity)
      (pointer : state.words (frame.localIndex (creditBase + credit)) = layout.pointer index) :
      Executes layout frame (.reuse world ctor credit arguments destination) state
        (reuse frame state index ctor credit arguments destination)
  | release (state index world source) (allocated : index < capacity)
      (pointer : HeapCopies.atomValue frame state source = layout.pointer index) :
      Executes layout frame (.release world source) state (release frame state index world source)
  | discard (state index credit) (allocated : index < capacity)
      (pointer : state.words (frame.localIndex (creditBase + credit)) = layout.pointer index) :
      Executes layout frame (.discard credit) state (discard frame state index credit)

theorem Executes.stable {layout frame operation before after} (executed : Executes layout frame operation before after) :
    Scalar.Stable before after := by
  cases executed with
  | nop => exact .refl _
  | move => exact (load_stable _ _ _).trans (save_stable _ _ _)
  | alloc => exact allocate_stable _ _ _ _ _ _ _
  | fetch => exact fetch_stable _ _ _ _ _ _
  | reserve => exact reserve_stable _ _ _ _ _ _ _ _
  | reuse => exact reuse_stable _ _ _ _ _ _ _
  | release => exact release_stable _ _ _ _ _
  | discard => exact discard_stable _ _ _ _

theorem Executes.trace {layout frame operation before after holes returns rootTop}
    (executed : Executes layout frame operation before after)
    (environment : Environment layout frame before holes returns rootTop)
    (valid : HeapTarget.primitiveValid operation = true) :
    SafeTrace layout.region returns (HeapTarget.primitive operation) before holes after holes := by
  cases executed with
  | nop => exact .nil _ _
  | move state destination source =>
      simp only [HeapTarget.primitiveValid, Bool.and_eq_true, decide_eq_true_eq] at valid
      have loaded := load_trace (returns := returns) environment.framed environment.safe valid.2
      have saved := (environment.advance (load_stable frame before source)).save
        (by simp only [maxValues, Scalar.maxLocals] at *; omega : destination < Scalar.maxLocals)
      simpa only [HeapTarget.primitive, List.singleton_append] using loaded.append saved
  | alloc state index world ctor arguments destination allocated cursor =>
      simp only [HeapTarget.primitiveValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at valid
      have loaded := fields_trace (returns := returns) environment.framed environment.safe valid.1.2
      have first := environment.advance (fields_stable frame before arguments)
      have pointed := cursor_trace first.based first.access (by exact cursor)
      have second := first.advance (Scalar.Stable.setReg _ .rax (layout.pointer index) (by simp))
      have written := second.writeCell allocated (by simp) ctor
      have third := second.advance (writeCell_stable _ index ctor)
      have cursorCount := increment_trace third.based third.access (by decide : 0 < headerWords) (by decide : 32 < 2147483648)
      have fourth := third.advance (counter_stable _ 0 (· + 32))
      have allocCount := increment_trace fourth.based fourth.access (by decide : 2 < headerWords) (by decide : 1 < 2147483648)
      have fifth := fourth.advance (counter_stable _ 2 (· + 1))
      have saved := fifth.save (by simp only [maxValues, Scalar.maxLocals] at *; omega : destination < Scalar.maxLocals)
      simpa only [HeapTarget.primitive, allocate, List.append_assoc, List.cons_append, List.nil_append] using
        ((((loaded.append pointed).append written).append cursorCount).append allocCount).append saved
  | fetch state index source field destination allocated pointer =>
      simp only [HeapTarget.primitiveValid, Bool.and_eq_true, decide_eq_true_eq] at valid
      have loaded := load_trace (returns := returns) environment.framed environment.safe valid.1.1
      have first := environment.advance (load_stable frame before source)
      have fetched := load_field (state := load frame before source) first.access .rax allocated
        (by simp only [cellWords]; omega : field + 1 < cellWords) (by simpa [load] using pointer)
      have second := first.advance (Scalar.Stable.setReg _ .rax ((load frame before source).words (cellSlot index (field + 1))) (by simp))
      have saved := second.save (by simp only [maxValues, Scalar.maxLocals] at *; omega : destination < Scalar.maxLocals)
      simpa only [HeapTarget.primitive, HeapPrimitives.fetch, List.cons_append, List.nil_append] using (loaded.append fetched).append saved
  | reserve state index world ctor source destination credit allocated pointer =>
      simp only [HeapTarget.primitiveValid, Bool.and_eq_true, decide_eq_true_eq] at valid
      have ctorBound : ctor.schema.fields.size ≤ 2 := by
        have accepted := valid.1.1.1
        simp only [HeapTarget.constructorValid, Bool.and_eq_true, decide_eq_true_eq] at accepted
        exact accepted.1.1
      have loaded := load_trace (returns := returns) environment.framed environment.safe valid.1.1.2
      have first := environment.advance (load_stable frame before source)
      have captured := captureFields_trace first.framed first.safe first.frames first.access allocated ctorBound
        (by simp only [maxValues, Scalar.maxLocals] at *; omega : destination + ctor.schema.fields.size ≤ Scalar.maxLocals)
        (by simpa [load] using pointer)
      have second := first.advance (captureFields_stable frame _ index ctor.schema.fields.size destination)
      have tagged := second.tag allocated (by simpa [load] using pointer) 1
      have third := second.advance (tag_stable _ index 1)
      have reserved := increment_trace third.based third.access (by decide : 9 < headerWords) (by decide : 1 < 2147483648)
      have fourth := third.advance (counter_stable _ 9 (· + 1))
      have shared := sharedReset_trace fourth.based fourth.access world
      have fifth := fourth.advance (sharedReset_stable world _)
      have saved := fifth.save (by simp only [creditBase, maxCredits, Scalar.maxLocals] at *; omega : creditBase + credit < Scalar.maxLocals)
      simpa only [HeapTarget.primitive, HeapPrimitives.reserve, List.append_assoc] using
        ((((loaded.append captured).append tagged).append reserved).append shared).append saved
  | reuse state index world ctor credit arguments destination allocated pointer =>
      simp only [HeapTarget.primitiveValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at valid
      have ctorBound : ctor.schema.fields.size ≤ 2 := by
        have accepted := valid.1.1.1.1
        simp only [HeapTarget.constructorValid, Bool.and_eq_true, decide_eq_true_eq] at accepted
        exact accepted.1.1
      have loaded := fields_trace (returns := returns) environment.framed environment.safe valid.1.2
      have first := environment.advance (fields_stable frame before arguments)
      have creditLoaded := credit_trace (returns := returns) first.framed first.safe valid.1.1.1.2
      have second := first.advance (credit_stable frame _ credit)
      have written := second.writeCell allocated (by simpa [creditState, fields] using pointer) ctor
      have third := second.advance (writeCell_stable _ index ctor)
      have reused := increment_trace third.based third.access (by decide : 4 < headerWords) (by decide : 1 < 2147483648)
      have fourth := third.advance (counter_stable _ 4 (· + 1))
      have payload := increment_trace fourth.based fourth.access (by decide : 8 < headerWords)
        (by omega : ctor.schema.fields.size < 2147483648)
      have fifth := fourth.advance (counter_stable _ 8 (· + UInt64.ofNat ctor.schema.fields.size))
      have reservation := decrement_trace fifth.based fifth.access (by decide : 9 < headerWords)
      have sixth := fifth.advance (counter_stable _ 9 (· - 1))
      have saved := sixth.save (by simp only [maxValues, Scalar.maxLocals] at *; omega : destination < Scalar.maxLocals)
      simpa only [HeapTarget.primitive, HeapPrimitives.reuse, List.append_assoc] using
        (((((loaded.append creditLoaded).append written).append reused).append payload).append reservation).append saved
  | release state index world source allocated pointer =>
      have loaded := load_trace (returns := returns) environment.framed environment.safe valid
      have first := environment.advance (load_stable frame before source)
      have tagged := first.tag allocated (by simpa [load] using pointer) 0
      have second := first.advance (tag_stable _ index 0)
      have freed := increment_trace second.based second.access (by decide : 3 < headerWords) (by decide : 1 < 2147483648)
      have third := second.advance (counter_stable _ 3 (· + 1))
      have shared := sharedRelease_trace third.based third.access world
      simpa only [HeapTarget.primitive, HeapPrimitives.release, List.append_assoc] using ((loaded.append tagged).append freed).append shared
  | discard state index credit allocated pointer =>
      have loaded := credit_trace (returns := returns) environment.framed environment.safe (of_decide_eq_true valid)
      have first := environment.advance (credit_stable frame before credit)
      have tagged := first.tag allocated (by simpa [creditState] using pointer) 0
      have second := first.advance (tag_stable _ index 0)
      have freed := increment_trace second.based second.access (by decide : 3 < headerWords) (by decide : 1 < 2147483648)
      have third := second.advance (counter_stable _ 3 (· + 1))
      have reservation := decrement_trace third.based third.access (by decide : 9 < headerWords)
      simpa only [HeapTarget.primitive, HeapPrimitives.discard, List.append_assoc] using ((loaded.append tagged).append freed).append reservation

end Compilatrix.X86.HeapPrimitives
