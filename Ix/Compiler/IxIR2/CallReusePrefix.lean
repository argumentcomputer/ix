import Ix.Compiler.IxIR2.CallReusePrefixHeap

/-! Actual target reset and move steps synchronize with the extracted baseline prefix. -/

namespace Ix.Compiler.IxIR2.CallReuse.Sim

open Eval
open Ix.Compiler.IxIR1.Sim (RValIso RValsIso)

theorem move_prefix_control (shape : Shape) {context : Context} {frame : Frame}
    {parameters fields : Array RVal} {store : Store} {heapFuel : Nat} {stack : List Continuation}
    (blockAt : frame.definition.blocks[frame.block]? = some shape.target)
    (parameterCount : parameters.size = shape.valueParams.size) (fieldCount : fields.size = shape.fieldCount) :
    Eval.Steps context .physical shape.fieldCount
      { store, heapFuel, control := .running { frame with pc := 1, values := parameters ++ fields } stack }
      { store, heapFuel, control := .running
          { frame with pc := shape.fieldCount + 1, values := parameters ++ fields ++ fields } stack } := by
  have loop : ∀ count, count ≤ shape.fieldCount → Eval.Steps context .physical count
      { store, heapFuel, control := .running { frame with pc := 1, values := parameters ++ fields } stack }
      { store, heapFuel, control := .running
          { frame with pc := 1 + count, values := prefixValues (parameters ++ fields) fields count } stack } := by
    intro count within
    induction count with
    | zero =>
        simpa [prefixValues] using (Eval.Steps.refl
          ({ store, heapFuel, control := .running { frame with pc := 1, values := parameters ++ fields } stack } : Machine))
    | succ count ih =>
        have before := ih (by omega)
        have bound : count < fields.size := by omega
        have atInstruction := shape.move_at (field := count) (by omega)
        obtain ⟨pc, instruction⟩ := Array.getElem?_eq_some_iff.mp atInstruction
        have resolved : resolveAtom (prefixValues (parameters ++ fields) fields count)
            (.reg (shape.valueParams.size + count)) = .ok fields[count] := by
          simp only [prefixValues, resolveAtom, Array.getElem?_append, Array.size_append,
            ← parameterCount, Nat.add_lt_add_iff_left, bound, ↓reduceIte,
            show ¬parameters.size + count < parameters.size by omega, Nat.add_sub_cancel_left,
            Array.getElem?_eq_getElem bound]
        have one := (InstructionTransferCase.move (context := context)
          (interpretation := .physical) (store := store) (heapFuel := heapFuel)
          (frame := { frame with pc := 1 + count, values := prefixValues (parameters ++ fields) fields count })
          (stack := stack) resolved).step blockAt pc instruction
        have advanced := before.trans (one.toSteps rfl)
        simpa only [prefixValues_succ bound, Nat.add_assoc] using advanced
  have allFields : (fields.toList.take shape.fieldCount).toArray = fields := by
    rw [← fieldCount]
    have size : fields.size = fields.toList.length := Array.length_toList.symm
    rw [size, List.take_length]
  simpa only [prefixValues, allFields, Nat.add_comm 1] using loop shape.fieldCount (Nat.le_refl _)

theorem FrameRel.afterPrefix {limits : Validate.Limits} {validation : Validate.Context}
    {mapping : Array Nat} {block : Block} {left right : Frame}
    (frames : FrameRel limits validation mapping block left right)
    {site : Site limits validation block} (produced : inspect limits validation block = some site)
    {leftFields rightFields : Array RVal} (fields : RValsIso (MapRel mapping) leftFields.toList rightFields.toList)
    {credit : Credit} (layout : credit.layout = site.representation.layout) (physical : PhysicalCredit credit) :
    FrameRel limits validation mapping block
      { left with pc := 2 * site.shape.fieldCount + 1, values := left.values ++ leftFields ++ leftFields }
      { right with
        pc := site.shape.fieldCount + 1
        values := right.values ++ rightFields ++ rightFields
        credits := #[some credit] } := by
  exact { frames with
    values := by simpa only [Array.toList_append] using (frames.values.append fields).append fields
    position := by simpa only [Nat.add_zero] using Position.body site produced 0 (Nat.zero_le _) credit layout physical
    entryCount := by intro zero; simp only at zero; omega }

theorem reset_prefix_related {limits : Validate.Limits} {validation : Validate.Context}
    {leftContext rightContext : Context} {mapping : Array Nat}
    {leftStore rightStore retained released : Store} {leftFuel rightFuel remaining : Nat}
    {block : Block} {leftFrame rightFrame : Frame} {leftStack rightStack : List Continuation}
    {site : Site limits validation block} {location rc : Nat} {fields : Array RVal}
    (contexts : ContextRel limits validation leftContext rightContext)
    (schemas : leftContext.schemas = validation.schemas)
    (machines : MachineRel limits validation leftContext mapping
      { store := leftStore, heapFuel := leftFuel, control := .running leftFrame leftStack }
      { store := rightStore, heapFuel := rightFuel, control := .running rightFrame rightStack })
    (frames : FrameRel limits validation mapping block leftFrame rightFrame)
    (stack : StackRel limits validation mapping leftStack rightStack)
    (produced : inspect limits validation block = some site)
    (leftPC : leftFrame.pc = 0) (rightPC : rightFrame.pc = 0) (credits : rightFrame.credits = #[])
    (resolved : resolveAtom leftFrame.values (.reg site.shape.source) = .ok (.loc location))
    (found : leftStore.get? location = some ⟨.shared, rc, .ctorN site.shape.sourceConstructor fields⟩)
    (fieldCount : fields.size = site.shape.fieldCount)
    (retains : RetainSharedMany leftStore fields retained)
    (releases : releaseShared leftFuel retained (.loc location) = .ok (released, remaining)) :
    ∃ rightAfter,
      Policy.Steps .suspendedCallsV1 rightContext .physical (site.shape.fieldCount + 1)
        { store := rightStore, heapFuel := rightFuel, control := .running rightFrame rightStack } rightAfter ∧
      TransferRel limits validation leftContext mapping mapping leftStore rightStore
        { store := released, heapFuel := remaining
          control := .running
            { leftFrame with
              pc := 2 * site.shape.fieldCount + 1
              values := leftFrame.values ++ fields ++ fields } leftStack } rightAfter := by
  obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
  cases valueRel with
  | @loc _ targetLocation mapped =>
      obtain ⟨targetBox, targetFields, targetView, boxes, fieldsRel⟩ :=
        machines.heap.constructorView mapped (ConstructorView.of_box found rfl rfl)
      have targetBoxEq : targetBox = ⟨.shared, rc, .ctorN site.shape.sourceConstructor targetFields⟩ := by
        have world := boxes.world
        have count := boxes.rc
        have node := targetView.parts.2.2
        cases targetBox
        simp_all
      have targetAt := targetView.parts.1
      rw [targetBoxEq] at targetAt
      have targetConstructor := ConstructorView.of_box targetAt rfl rfl
      have targetFieldCount : targetFields.size = site.shape.fieldCount := (values_size fieldsRel).symm.trans fieldCount
      have parameterCount : rightFrame.values.size = site.shape.valueParams.size := by
        have count := frames.entryCount leftPC
        have sourceCount : block.valueParams.size = site.shape.valueParams.size := by
          simp only [site.exact, Shape.baseline]
        exact (values_size frames.values).symm.trans (count.trans sourceCount)
      obtain ⟨sourceSchema, _, sourceAt, _, _, _, sourceLayout, _⟩ := site.schemas
      have targetSchema : rightContext.schemas .shared site.shape.sourceConstructor = some sourceSchema := by
        rw [← contexts.schemas, schemas]
        exact sourceAt
      have targetBlockAt : rightFrame.definition.blocks[rightFrame.block]? = some site.shape.target := by
        simpa only [rewriteBlock_accepted produced] using frames.targetAt
      have resetAt : site.shape.target.instructions[rightFrame.pc]? =
          some (.resetShared (.reg site.shape.source) site.shape.sourceConstructor) := by
        rw [rightPC]
        exact site.shape.reset_at
      obtain ⟨resetPC, resetInstruction⟩ := Array.getElem?_eq_some_iff.mp resetAt
      have finish : ∀ (targetStore : Store) (credit : Credit),
          credit.layout = site.representation.layout → PhysicalCredit credit →
          Eval.Step rightContext .physical
            { store := rightStore, heapFuel := rightFuel, control := .running rightFrame rightStack }
            { store := targetStore, heapFuel := rightFuel
              control := .running
                { rightFrame with
                  pc := 1
                  values := rightFrame.values ++ targetFields
                  credits := #[some credit] } rightStack } →
          HeapTransition leftContext mapping mapping leftStore released rightStore targetStore →
          ∃ rightAfter,
            Policy.Steps .suspendedCallsV1 rightContext .physical (site.shape.fieldCount + 1)
              { store := rightStore, heapFuel := rightFuel, control := .running rightFrame rightStack } rightAfter ∧
            TransferRel limits validation leftContext mapping mapping leftStore rightStore
              { store := released, heapFuel := remaining
                control := .running
                  { leftFrame with
                    pc := 2 * site.shape.fieldCount + 1
                    values := leftFrame.values ++ fields ++ fields } leftStack } rightAfter := by
        intro targetStore credit layout physical reset transition
        have moves := move_prefix_control site.shape (context := rightContext)
          (frame := { rightFrame with credits := #[some credit] })
          (store := targetStore) (heapFuel := rightFuel) (stack := rightStack)
          targetBlockAt parameterCount targetFieldCount
        have actual := (reset.toSteps rfl).trans moves
        let target : Machine :=
          { store := targetStore, heapFuel := rightFuel
            control := .running
              { rightFrame with
                pc := site.shape.fieldCount + 1
                values := rightFrame.values ++ targetFields ++ targetFields
                credits := #[some credit] } rightStack }
        refine ⟨target, ?_, ⟨transition, ?_, .running (frames.afterPrefix produced fieldsRel layout physical) stack⟩⟩
        · simpa only [Nat.add_comm 1] using Policy.of_originalSteps actual
        · exact Nat.le_trans (ReuseSim.releaseShared_remaining_le releases) machines.fuel
      by_cases unit : rc = 1
      · subst rc
        have transition := machines.heapState.hotPrefix mapped found retains releases
        apply finish _ { layout := sourceSchema.layout, presence := .present (some targetLocation) }
          sourceLayout.symm (.inr ⟨targetLocation, rfl⟩) _ transition
        have reset := (InstructionTransferCase.resetSharedPhysicalHot
          (context := rightContext) (heapFuel := rightFuel) (stack := rightStack)
          rfl targetSchema targetResolved targetConstructor rfl).step targetBlockAt resetPC resetInstruction
        simpa only [rightPC, credits, Nat.zero_add, Array.push_empty, ReuseSim.physicalHotResetStore] using reset
      · have many : 1 < rc := by
          have positive : 0 < rc := machines.ordered.rc_pos found
          omega
        obtain ⟨targetStore, targetRetains, transition⟩ :=
          machines.heapState.coldPrefix mapped targetAt many fieldsRel retains releases
        apply finish targetStore { layout := sourceSchema.layout, presence := .absent }
          sourceLayout.symm (.inl rfl) _ transition
        have reset := (InstructionTransferCase.resetSharedCold
          (context := rightContext) (interpretation := .physical) (heapFuel := rightFuel) (stack := rightStack)
          targetSchema targetResolved targetConstructor many targetRetains).step targetBlockAt resetPC resetInstruction
        simpa only [rightPC, credits, Nat.zero_add, Array.push_empty] using reset

end Ix.Compiler.IxIR2.CallReuse.Sim
