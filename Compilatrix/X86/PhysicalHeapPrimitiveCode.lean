import Compilatrix.X86.PhysicalHeap

namespace Compilatrix.X86.PhysicalHeap

/-- Static evidence for one selected instruction. The witnesses concern
syntax, schemas, kinds, and slot placement; they contain no runtime input. -/
inductive PrimitiveCode (schemas : Schemas) (constructors : Array IxIR2.CtorId) (scope : Scope) :
    IxIR2.Instr → Primitive → Scope → Prop where
  | move {source kind operand consumed next}
      (taken : scope.take source = .ok (kind, operand, consumed))
      (pushed : consumed.pushValue kind = .ok next) :
      PrimitiveCode schemas constructors scope (.move source) (.move scope.values.size operand) next
  | retain {source kind operand next}
      (peeked : scope.peek source = .ok (kind, operand)) (scalar : kind ≠ .node)
      (pushed : scope.pushValue kind = .ok next) :
      PrimitiveCode schemas constructors scope (.retainShared source) (.move scope.values.size operand) next
  | release {source kind operand next}
      (taken : scope.take source = .ok (kind, operand, next)) :
      PrimitiveCode schemas constructors scope (.releaseShared source)
        (if kind == .node then .release .shared operand else .nop) next
  | drop {source kind operand next}
      (taken : scope.take source = .ok (kind, operand, next)) :
      PrimitiveCode schemas constructors scope (.dropUnique source)
        (if kind == .node then .release .unique operand else .nop) next
  | alloc {world cid arguments ctor operands next}
      (constructorAt : constructor schemas constructors world cid = .ok ctor)
      (arity : arguments.size = ctor.schema.fields.size)
      (fields : arguments.mapM scope.scalar = .ok operands)
      (pushed : scope.pushValue .node = .ok next) :
      PrimitiveCode schemas constructors scope (.alloc world cid arguments)
        (.alloc world ctor operands scope.values.size) next
  | reuse {credit world cid arguments ctor operands consumed next}
      (constructorAt : constructor schemas constructors world cid = .ok ctor)
      (arity : arguments.size = ctor.schema.fields.size)
      (fields : arguments.mapM scope.scalar = .ok operands)
      (taken : scope.takeCredit credit = .ok (ctor.schema.layout, consumed))
      (pushed : consumed.pushValue .node = .ok next) :
      PrimitiveCode schemas constructors scope (.allocWith credit world cid arguments)
        (.reuse world ctor credit operands scope.values.size) next
  | takeUnique {source cid ctor operand consumed fieldScope next}
      (constructorAt : constructor schemas constructors .unique cid = .ok ctor)
      (taken : scope.take source = .ok (.node, operand, consumed))
      (fields : consumed.pushFields ctor.schema.fields.size = .ok fieldScope)
      (credit : fieldScope.pushCredit ctor.schema.layout = .ok next) :
      PrimitiveCode schemas constructors scope (.takeUnique source cid)
        (.reserve .unique ctor operand scope.values.size scope.credits.size) next
  | resetShared {source cid ctor operand consumed fieldScope next}
      (constructorAt : constructor schemas constructors .shared cid = .ok ctor)
      (taken : scope.take source = .ok (.node, operand, consumed))
      (fields : consumed.pushFields ctor.schema.fields.size = .ok fieldScope)
      (credit : fieldScope.pushCredit ctor.schema.layout = .ok next) :
      PrimitiveCode schemas constructors scope (.resetShared source cid)
        (.reserve .shared ctor operand scope.values.size scope.credits.size) next
  | discard {credit id next} (taken : scope.takeCredit credit = .ok (id, next)) :
      PrimitiveCode schemas constructors scope (.discardCredit credit) (.discard credit) next
  | free {source cid ctor operand next}
      (constructorAt : constructor schemas constructors .unique cid = .ok ctor)
      (taken : scope.take source = .ok (.node, operand, next)) :
      PrimitiveCode schemas constructors scope (.freeUnique source cid) (.release .unique operand) next
  | fetch {source cid field operand next}
      (peeked : scope.node source = .ok operand) (small : field < 2)
      (pushed : scope.pushValue .scalar = .ok next) :
      PrimitiveCode schemas constructors scope (.fetch source cid field) (.fetch operand field scope.values.size) next

structure PrimitiveRow (schemas : Schemas) (constructors : Array IxIR2.CtorId) (scope : Scope) (instruction : IxIR2.Instr) where
  operation : Primitive
  next : Scope
  bounded : scope.bounded = true
  code : PrimitiveCode schemas constructors scope instruction operation next

def checkedExcept {α : Type} (action : Except String α) : Except String { output // action = .ok output } :=
  match equal : action with
  | .error error => .error error
  | .ok output => .ok ⟨output, rfl⟩

def selectPrimitiveChecked (schemas : Schemas) (constructors : Array IxIR2.CtorId)
    (scope : Scope) (instruction : IxIR2.Instr) : Except String (PrimitiveRow schemas constructors scope instruction) := do
  if bounded : scope.bounded = true then
    match atInstr : instruction with
    | .move source =>
        let taken ← checkedExcept (scope.take source)
        let pushed ← checkedExcept (taken.val.2.2.pushValue taken.val.1)
        return ⟨.move scope.values.size taken.val.2.1, pushed.val, bounded, by simpa only [atInstr] using PrimitiveCode.move taken.property pushed.property⟩
    | .retainShared source =>
        let peeked ← checkedExcept (scope.peek source)
        if scalar : peeked.val.1 ≠ .node then
          let pushed ← checkedExcept (scope.pushValue peeked.val.1)
          return ⟨.move scope.values.size peeked.val.2, pushed.val, bounded, by simpa only [atInstr] using PrimitiveCode.retain peeked.property scalar pushed.property⟩
        else throw "heap CFG retaining a constructor would introduce sharing"
    | .releaseShared source =>
        let taken ← checkedExcept (scope.take source)
        return ⟨if taken.val.1 == .node then .release .shared taken.val.2.1 else .nop,
          taken.val.2.2, bounded, by simpa only [atInstr] using PrimitiveCode.release taken.property⟩
    | .dropUnique source =>
        let taken ← checkedExcept (scope.take source)
        return ⟨if taken.val.1 == .node then .release .unique taken.val.2.1 else .nop,
          taken.val.2.2, bounded, by simpa only [atInstr] using PrimitiveCode.drop taken.property⟩
    | .alloc world cid arguments =>
        let ctor ← checkedExcept (constructor schemas constructors world cid)
        if arity : arguments.size = ctor.val.schema.fields.size then
          let fields ← checkedExcept (arguments.mapM scope.scalar)
          let pushed ← checkedExcept (scope.pushValue .node)
          return ⟨.alloc world ctor.val fields.val scope.values.size, pushed.val, bounded,
            by simpa only [atInstr] using PrimitiveCode.alloc ctor.property arity fields.property pushed.property⟩
        else throw "heap CFG allocation field arity mismatch"
    | .allocWith credit world cid arguments =>
        let ctor ← checkedExcept (constructor schemas constructors world cid)
        if arity : arguments.size = ctor.val.schema.fields.size then
          let fields ← checkedExcept (arguments.mapM scope.scalar)
          let taken ← checkedExcept (scope.takeCredit credit)
          if layout : taken.val.1 = ctor.val.schema.layout then
            let pushed ← checkedExcept (taken.val.2.pushValue .node)
            return ⟨.reuse world ctor.val credit fields.val scope.values.size, pushed.val, bounded,
              by simpa only [atInstr] using PrimitiveCode.reuse (credit := credit) ctor.property arity fields.property (by simpa only [← layout] using taken.property) pushed.property⟩
          else throw "heap CFG reuse layout mismatch"
        else throw "heap CFG reuse field arity mismatch"
    | .takeUnique source cid =>
        let ctor ← checkedExcept (constructor schemas constructors .unique cid)
        let taken ← checkedExcept (scope.take source)
        if node : taken.val.1 = .node then
          let fields ← checkedExcept (taken.val.2.2.pushFields ctor.val.schema.fields.size)
          let credit ← checkedExcept (fields.val.pushCredit ctor.val.schema.layout)
          return ⟨.reserve .unique ctor.val taken.val.2.1 scope.values.size scope.credits.size, credit.val, bounded,
            by simpa only [atInstr] using PrimitiveCode.takeUnique (source := source) (operand := taken.val.2.1) ctor.property (by simpa only [← node] using taken.property) fields.property credit.property⟩
        else throw "heap CFG reset requires a constructor"
    | .resetShared source cid =>
        let ctor ← checkedExcept (constructor schemas constructors .shared cid)
        let taken ← checkedExcept (scope.take source)
        if node : taken.val.1 = .node then
          let fields ← checkedExcept (taken.val.2.2.pushFields ctor.val.schema.fields.size)
          let credit ← checkedExcept (fields.val.pushCredit ctor.val.schema.layout)
          return ⟨.reserve .shared ctor.val taken.val.2.1 scope.values.size scope.credits.size, credit.val, bounded,
            by simpa only [atInstr] using PrimitiveCode.resetShared (source := source) (operand := taken.val.2.1) ctor.property (by simpa only [← node] using taken.property) fields.property credit.property⟩
        else throw "heap CFG reset requires a constructor"
    | .discardCredit credit =>
        let taken ← checkedExcept (scope.takeCredit credit)
        return ⟨.discard credit, taken.val.2, bounded, by simpa only [atInstr] using PrimitiveCode.discard taken.property⟩
    | .freeUnique source cid =>
        let ctor ← checkedExcept (constructor schemas constructors .unique cid)
        let taken ← checkedExcept (scope.take source)
        if node : taken.val.1 = .node then
          return ⟨.release .unique taken.val.2.1, taken.val.2.2, bounded,
            by simpa only [atInstr] using PrimitiveCode.free (source := source) (operand := taken.val.2.1) ctor.property (by simpa only [← node] using taken.property)⟩
        else throw "heap CFG free requires a constructor"
    | .fetch source cid field =>
        let peeked ← checkedExcept (scope.node source)
        if small : field < 2 then
          let pushed ← checkedExcept (scope.pushValue .scalar)
          return ⟨.fetch peeked.val field scope.values.size, pushed.val, bounded, by simpa only [atInstr] using PrimitiveCode.fetch (cid := cid) peeked.property small pushed.property⟩
        else throw "heap CFG fetch exceeds the leaf cell"
    | _ => throw "heap CFG instruction is outside the leaf fragment"
  else throw "heap CFG input scope exceeds its frame"

end Compilatrix.X86.PhysicalHeap
