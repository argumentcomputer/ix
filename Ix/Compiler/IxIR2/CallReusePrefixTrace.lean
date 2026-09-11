import Ix.Compiler.IxIR2.CallReuseBody

/-! The successful baseline execution supplies every fact needed by a reset prefix. -/

namespace Ix.Compiler.IxIR2.CallReuse.Sim

open Eval

theorem step_instruction {context : Context} {interpretation : Interpretation}
    {store : Store} {heapFuel : Nat} {frame : Frame} {stack : List Continuation}
    {block : Block} {instruction : Instr} {target : Machine}
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size) (instructionAt : block.instructions[frame.pc] = instruction)
    (stepped : Eval.Step context interpretation { store, heapFuel, control := .running frame stack } target) :
    InstructionTransferCase context interpretation store heapFuel frame stack instruction target := by
  cases stepped.classify with
  | instruction found _ atInstruction classified =>
      have blocks := Option.some.inj (found.symm.trans blockAt)
      cases blocks
      have instructions := atInstruction.symm.trans instructionAt
      cases instructions
      exact classified
  | terminator found atEnd _ _ =>
      have blocks := Option.some.inj (found.symm.trans blockAt)
      cases blocks
      omega

theorem instruction_head {context : Context} {interpretation : Interpretation}
    {store : Store} {heapFuel count : Nat} {frame : Frame} {stack : List Continuation}
    {block : Block} {instruction : Instr} {final : Machine}
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (found : block.instructions[frame.pc]? = some instruction)
    (halted : ∃ value, final.control = .halted value)
    (steps : Eval.Steps context interpretation count
      { store, heapFuel, control := .running frame stack } final) :
    ∃ remaining next, count = remaining + 1 ∧
      InstructionTransferCase context interpretation store heapFuel frame stack instruction next ∧
      Eval.Steps context interpretation remaining next final := by
  cases steps with
  | refl => obtain ⟨value, impossible⟩ := halted; cases impossible
  | cons _ head tail =>
      obtain ⟨pc, instructionAt⟩ := Array.getElem?_eq_some_iff.mp found
      exact ⟨_, _, rfl, step_instruction blockAt pc instructionAt head, tail⟩

def prefixValues (parameters fields : Array RVal) (count : Nat) : Array RVal :=
  parameters ++ (fields.toList.take count).toArray

theorem prefixValues_succ {parameters fields : Array RVal} {count : Nat}
    (bound : count < fields.size) :
    (prefixValues parameters fields count).push fields[count] = prefixValues parameters fields (count + 1) := by
  apply Array.toList_inj.mp
  simp only [prefixValues, Array.toList_push, Array.toList_append]
  rw [← List.take_append_getElem (l := fields.toList) (i := count) (by simpa using bound)]
  simp [List.append_assoc]

theorem resolve_parameter_append {parameters suffix : Array RVal} {source : Nat} {value : RVal}
    (bound : source < parameters.size) (resolved : resolveAtom parameters (.reg source) = .ok value) :
    resolveAtom (parameters ++ suffix) (.reg source) = .ok value := by
  simpa only [resolveAtom, Array.getElem?_append_left bound] using resolved

theorem fetch_prefix_inverse {limits : Validate.Limits} {validation : Validate.Context} {block : Block}
    (site : Site limits validation block) {context : Context} {definition : Function} {blockId : Nat}
    {parameters fields : Array RVal} {store : Store} {heapFuel total : Nat} {stack : List Continuation}
    {location : Nat} {box : NodeBox} {final : Machine}
    (blockAt : definition.blocks[blockId]? = some block)
    (parameterCount : parameters.size = site.shape.valueParams.size)
    (resolved : resolveAtom parameters (.reg site.shape.source) = .ok (.loc location))
    (boxAt : store.get? location = some box) (node : box.node = .ctorN site.shape.sourceConstructor fields)
    (halted : ∃ value, final.control = .halted value)
    (steps : Eval.Steps context .physical total
      { store, heapFuel, control := .running { definition, block := blockId, values := parameters } stack } final)
    (count : Nat) (within : count ≤ site.shape.fieldCount) :
    ∃ remaining, total = count + remaining ∧ count ≤ fields.size ∧
      Eval.Steps context .physical remaining
        { store, heapFuel
          control := .running
            { definition, block := blockId, pc := count, values := prefixValues parameters fields count } stack } final := by
  induction count with
  | zero => exact ⟨total, by omega, by omega, by simpa [prefixValues] using steps⟩
  | succ count ih =>
      obtain ⟨remaining, totalCount, fieldBound, rest⟩ := ih (by omega)
      have instructionAt : block.instructions[count]? =
          some (.fetch (.reg site.shape.source) site.shape.sourceConstructor count) := by
        simpa only [site.exact] using site.shape.fetch_at (field := count) (by omega)
      obtain ⟨afterCount, next, remainingCount, head, tail⟩ :=
        instruction_head blockAt instructionAt halted rest
      cases head with
      | @fetch _ _ _ otherLocation otherBox otherFields value sourceResolved foundBox foundNode fieldAt =>
          have root := resolve_parameter_append
            (suffix := (fields.toList.take count).toArray)
            (by rw [parameterCount]; exact site.sourceBound) resolved
          have locations := Except.ok.inj (sourceResolved.symm.trans root)
          cases locations
          have boxes := Option.some.inj (foundBox.symm.trans boxAt)
          cases boxes
          have payloads := IxIR1.Node.ctorN.inj (foundNode.symm.trans node)
          cases payloads.2
          obtain ⟨currentBound, valueAt⟩ := Array.getElem?_eq_some_iff.mp fieldAt
          subst value
          refine ⟨afterCount, by omega, by omega, ?_⟩
          simpa only [prefixValues_succ currentBound] using tail

theorem retain_suffix_inverse {limits : Validate.Limits} {validation : Validate.Context} {block : Block}
    (site : Site limits validation block) {context : Context} {definition : Function} {blockId : Nat}
    {parameters fields : Array RVal} {store : Store} {heapFuel total : Nat} {stack : List Continuation}
    {final : Machine} (blockAt : definition.blocks[blockId]? = some block)
    (parameterCount : parameters.size = site.shape.valueParams.size)
    (fieldCount : fields.size = site.shape.fieldCount)
    (halted : ∃ value, final.control = .halted value) (remaining : List RVal) :
    ∀ (processed : List RVal), fields.toList = processed ++ remaining →
      Eval.Steps context .physical total
        { store, heapFuel
          control := .running
            { definition, block := blockId, pc := site.shape.fieldCount + processed.length,
              values := parameters ++ fields ++ processed.toArray } stack } final →
      ∃ afterCount retained, total = remaining.length + afterCount ∧
        RetainSharedMany store remaining.toArray retained ∧
        Eval.Steps context .physical afterCount
          { store := retained, heapFuel
            control := .running
              { definition, block := blockId, pc := 2 * site.shape.fieldCount,
                values := parameters ++ fields ++ fields } stack } final := by
  induction remaining generalizing total store with
  | nil =>
      intro processed split steps
      have processedEq : processed.toArray = fields := by
        simpa using congrArg List.toArray split.symm
      have processedSize : processed.length = site.shape.fieldCount := by
        simpa only [List.size_toArray, fieldCount] using congrArg Array.size processedEq
      exact ⟨total, store, by simp, RetainSharedMany.empty store,
        by simpa only [processedEq, processedSize, Nat.two_mul] using steps⟩
  | cons value remaining ih =>
      intro processed split steps
      have within : processed.length < site.shape.fieldCount := by
        have sizes := congrArg List.length split
        simp only [Array.length_toList, List.length_append, List.length_cons, fieldCount] at sizes
        omega
      have instructionAt : block.instructions[site.shape.fieldCount + processed.length]? =
          some (.retainShared (.reg (site.shape.valueParams.size + processed.length))) := by
        simpa only [site.exact] using site.shape.retain_at within
      obtain ⟨nextCount, next, totalCount, head, tail⟩ := instruction_head blockAt instructionAt halted steps
      cases head with
      | @retainShared _ otherValue output resolved retained =>
          have fieldAt : fields[processed.length]? = some value := by
            have atList : fields.toList[processed.length]? = some value := by rw [split]; simp
            simpa using atList
          have resolveValue : resolveAtom (parameters ++ fields ++ processed.toArray)
              (.reg (site.shape.valueParams.size + processed.length)) = .ok value := by
            simp only [resolveAtom, Array.getElem?_append, Array.size_append, Nat.add_lt_add_iff_left, ← parameterCount,
              show ¬parameters.size + processed.length < parameters.size by omega,
              show processed.length < fields.size by omega, fieldAt,
              ↓reduceIte, Nat.add_sub_cancel_left]
          have same := Except.ok.inj (resolved.symm.trans resolveValue)
          subst otherValue
          have advancedValues : (parameters ++ fields ++ processed.toArray).push value =
              parameters ++ fields ++ (processed ++ [value]).toArray := by
            apply Array.toList_inj.mp
            simp
          have nextSteps : Eval.Steps context .physical nextCount
              { store := output, heapFuel
                control := .running
                  { definition, block := blockId, pc := site.shape.fieldCount + (processed ++ [value]).length,
                    values := parameters ++ fields ++ (processed ++ [value]).toArray } stack } final := by
            simpa [advancedValues, List.length_append, Nat.add_assoc] using tail
          obtain ⟨afterCount, output, restCount, retainedRest, rest⟩ :=
            ih (processed ++ [value]) (by simpa [List.append_assoc] using split) nextSteps
          exact ⟨afterCount, output, by simp only [List.length_cons]; omega,
            RetainSharedMany.cons retained retainedRest, rest⟩

theorem baseline_prefix_trace {limits : Validate.Limits} {validation : Validate.Context} {block : Block}
    (site : Site limits validation block) {context : Context} {definition : Function} {blockId : Nat}
    {parameters : Array RVal} {store : Store} {heapFuel total : Nat} {stack : List Continuation}
    {final : Machine} (blockAt : definition.blocks[blockId]? = some block)
    (parameterCount : parameters.size = site.shape.valueParams.size)
    (schemas : context.schemas = validation.schemas) (ordered : Ordered store) (shaped : Shaped context store)
    (halted : ∃ value, final.control = .halted value)
    (steps : Eval.Steps context .physical total
      { store, heapFuel, control := .running { definition, block := blockId, values := parameters } stack } final) :
    ∃ location box fields retained released remainingFuel remainingCount,
      resolveAtom parameters (.reg site.shape.source) = .ok (.loc location) ∧
      store.get? location = some box ∧ box.world = .shared ∧
      box.node = .ctorN site.shape.sourceConstructor fields ∧ fields.size = site.shape.fieldCount ∧
      RetainSharedMany store fields retained ∧
      releaseShared heapFuel retained (.loc location) = .ok (released, remainingFuel) ∧
      total = 2 * site.shape.fieldCount + 1 + remainingCount ∧
      Eval.Steps context .physical remainingCount
        { store := released, heapFuel := remainingFuel
          control := .running
            { definition, block := blockId, pc := 2 * site.shape.fieldCount + 1,
              values := parameters ++ fields ++ fields } stack } final := by
  have firstAt : block.instructions[0]? =
      some (.fetch (.reg site.shape.source) site.shape.sourceConstructor 0) := by
    simpa only [site.exact] using site.shape.fetch_at site.fieldsPositive
  obtain ⟨_, _, _, first, _⟩ := instruction_head blockAt firstAt halted steps
  cases first with
  | @fetch _ _ _ location box fields firstValue resolved boxAt node _ =>
      obtain ⟨afterFetchCount, fetchCount, fieldBound, afterFetch⟩ :=
        fetch_prefix_inverse site blockAt parameterCount resolved boxAt node halted steps
          site.shape.fieldCount (Nat.le_refl _)
      let opened := (fields.toList.take site.shape.fieldCount).toArray
      have openedSize : opened.size = site.shape.fieldCount := by
        simp only [opened, List.size_toArray, List.length_take, Array.length_toList,
          Nat.min_eq_left fieldBound]
      obtain ⟨afterRetainCount, retained, retainCount, retains, afterRetain⟩ :=
        retain_suffix_inverse site (fields := opened) blockAt parameterCount openedSize halted
          opened.toList [] (by simp) (by simpa [prefixValues, opened] using afterFetch)
      have retainedFields : RetainSharedMany store opened retained := by simpa using retains
      have releaseAt : block.instructions[2 * site.shape.fieldCount]? =
          some (.releaseShared (.reg site.shape.source)) := by
        simpa only [site.exact] using site.shape.release_at
      obtain ⟨remainingCount, _, releaseCount, head, tail⟩ :=
        instruction_head blockAt releaseAt halted afterRetain
      cases head with
      | @releaseShared _ releasedValue released remainingFuel sourceResolved releases =>
          have root : resolveAtom (parameters ++ opened ++ opened) (.reg site.shape.source) =
              .ok (.loc location) := by
            simpa only [Array.append_assoc] using resolve_parameter_append
              (suffix := opened ++ opened) (by rw [parameterCount]; exact site.sourceBound) resolved
          have same := Except.ok.inj (sourceResolved.symm.trans root)
          subst releasedValue
          have avoids : ∀ value ∈ opened.toList, value ≠ .loc location := by
            intro value member same
            subst value
            have original : .loc location ∈ fields.toList := by
              exact List.mem_of_mem_take (by simpa only [opened, List.toList_toArray] using member)
            have older := ordered.child_lt boxAt (by simpa only [node, IxIR1.Sim.nodeChildren] using original)
            omega
          have retainedAt := ReuseSim.RetainSharedMany.preserves_box boxAt avoids retains
          have shared : box.world = .shared := by
            cases heapFuel with
            | zero => simp [releaseShared, releaseSharedWork] at releases
            | succ fuel =>
                by_cases same : box.world = .shared
                · exact same
                · simp [releaseShared, releaseSharedWork, retainedAt, same] at releases
          obtain ⟨sourceSchema, _, sourceAt, _, schemaFields, _, _, _⟩ := site.schemas
          have fieldCount : fields.size = site.shape.fieldCount := by
            have arity := shaped.fields (ConstructorView.of_box boxAt shared node)
              (by rw [schemas]; exact sourceAt)
            simpa only [schemaFields, Array.size_replicate] using arity
          have openedEq : opened = fields := by
            simp only [opened, ← fieldCount]
            have size : fields.size = fields.toList.length := Array.length_toList.symm
            rw [size, List.take_length]
          refine ⟨location, box, fields, retained, released, remainingFuel, remainingCount,
            resolved, boxAt, shared, node, fieldCount, ?_, releases, ?_, ?_⟩
          · simpa only [openedEq] using retainedFields
          · simp only [Array.length_toList, openedSize] at retainCount
            omega
          · simpa only [openedEq] using tail

end Ix.Compiler.IxIR2.CallReuse.Sim
