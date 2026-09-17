import Compilatrix.Ixby.Inline.Relation

namespace Compilatrix.Ixby.Inline

open Ix.Ixby

structure FunctionLayout where
  arity : Nat
  entry : BlockId
  locals : Array Nat
  deriving DecidableEq

def functionLayout (function : Function) : FunctionLayout :=
  ⟨function.arity, function.entry, function.blocks.map Block.locals⟩

structure SameLayout (source target : Program) : Prop where
  entry : source.entry = target.entry
  constructors : source.constructors = target.constructors
  functions : source.functions.map functionLayout = target.functions.map functionLayout

theorem FunctionRelated.layout {limits source left right}
    (related : FunctionRelated limits source left right) : functionLayout left = functionLayout right := by
  have blocks := related.blocks.map_eq Block.locals Block.locals (fun _ _ h => h.locals)
  have arrays : left.blocks.map Block.locals = right.blocks.map Block.locals := by
    apply Array.toList_inj.mp
    simpa using blocks
  simp [functionLayout, related.arity, related.entry, arrays]

theorem ProgramRelated.layout {limits source target}
    (related : ProgramRelated limits source target) : SameLayout source target := by
  refine ⟨related.entry, related.constructors, ?_⟩
  apply Array.toList_inj.mp
  simpa using related.functions.map_eq functionLayout functionLayout (fun _ _ h => h.layout)

theorem SameLayout.symm {source target} (same : SameLayout source target) : SameLayout target source :=
  ⟨same.entry.symm, same.constructors.symm, same.functions.symm⟩

theorem SameLayout.getFunction {source target} (same : SameLayout source target) (id : FunctionId) :
    (source.getFunction id).map functionLayout = (target.getFunction id).map functionLayout := by
  have found := congrArg (fun functions => functions[id]?) same.functions
  simp only [Array.getElem?_map] at found
  cases left : source.functions[id]? <;> cases right : target.functions[id]? <;>
    simp_all [Program.getFunction, Except.map]

theorem SameLayout.getConstructor {source target} (same : SameLayout source target) (id : Constructor) :
    source.getConstructor id = target.getConstructor id := by
  simp [Program.getConstructor, same.constructors]

theorem SameLayout.check {source target} (same : SameLayout source target) (limits : Limits) (frame : Frame) :
    (frame.check limits source).map Block.locals = (frame.check limits target).map Block.locals := by
  have functions := same.getFunction frame.function
  cases left : source.getFunction frame.function with
  | error error =>
    cases right : target.getFunction frame.function <;>
      simp_all [Frame.check, Except.map, bind, Except.bind]
  | ok first =>
    cases right : target.getFunction frame.function with
    | error error => simp [left, right, Except.map] at functions
    | ok second =>
      have layouts : functionLayout first = functionLayout second := by
        simpa [left, right, Except.map] using functions
      have blocks := congrArg (fun layout => layout.locals[frame.block]?) layouts
      simp only [functionLayout, Array.getElem?_map] at blocks
      cases firstBlock : first.blocks[frame.block]? with
      | none =>
        cases secondBlock : second.blocks[frame.block]? <;>
          simp_all [Frame.check, Except.map, bind, Except.bind]
      | some before =>
        cases secondBlock : second.blocks[frame.block]? with
        | none => simp [firstBlock, secondBlock] at blocks
        | some after =>
          have locals : before.locals = after.locals := by simpa [firstBlock, secondBlock] using blocks
          by_cases capacity : limits.locals < frame.locals.size <;>
            by_cases size : frame.locals.size = after.locals <;>
            simp [Frame.check, left, right, firstBlock, secondBlock, locals, capacity, size,
              Except.map, bind, Except.bind, pure, Except.pure] <;>
            (by_cases normalized : limits.locals < after.locals <;> simp [normalized, locals])

theorem SameLayout.transfer {source target} (same : SameLayout source target) (limits : Limits)
    (frame : Frame) (next : BlockId) (extra : Array Value) :
    frame.transfer limits source next extra = frame.transfer limits target next extra := by
  let resumed : Frame := { frame with block := next, locals := frame.locals ++ extra }
  have checked := same.check limits resumed
  cases left : resumed.check limits source <;> cases right : resumed.check limits target <;>
    simp_all [Frame.transfer, resumed, Except.map, bind, Except.bind, pure, Except.pure]

theorem SameLayout.enter {source target} (same : SameLayout source target) (limits : Limits)
    (callee : FunctionId) (args : Array Value) :
    enter limits source callee args = enter limits target callee args := by
  have functions := same.getFunction callee
  cases left : source.getFunction callee with
  | error error =>
    cases right : target.getFunction callee <;>
      simp_all [Ix.Ixby.enter, Except.map, bind, Except.bind]
  | ok first =>
    cases right : target.getFunction callee with
    | error error => simp [left, right, Except.map] at functions
    | ok second =>
      have layouts : functionLayout first = functionLayout second := by
        simpa [left, right, Except.map] using functions
      have arity := congrArg FunctionLayout.arity layouts
      have entry := congrArg FunctionLayout.entry layouts
      change first.arity = second.arity at arity
      change first.entry = second.entry at entry
      let frame : Frame := { function := callee, block := second.entry, locals := args }
      have checked := same.check limits frame
      cases firstCheck : frame.check limits source <;> cases secondCheck : frame.check limits target <;>
        simp_all [Ix.Ixby.enter, frame, Except.map, bind, Except.bind, pure, Except.pure]

theorem SameLayout.evalOp {source target} (same : SameLayout source target) (limits : Limits)
    (frame : Frame) (operation : Op) :
    evalOp limits source frame operation = evalOp limits target frame operation := by
  cases operation with
  | construct ctor args => simp only [Ix.Ixby.evalOp, same.getConstructor]
  | closure callee args =>
    have functions := same.getFunction callee
    cases left : source.getFunction callee with
    | error error =>
      cases right : target.getFunction callee <;>
        simp_all [Ix.Ixby.evalOp, Except.map, bind, Except.bind]
    | ok first =>
      cases right : target.getFunction callee with
      | error error => simp [left, right, Except.map] at functions
      | ok second =>
        have layouts : functionLayout first = functionLayout second := by
          simpa [left, right, Except.map] using functions
        have arity := congrArg FunctionLayout.arity layouts
        change first.arity = second.arity at arity
        simp [Ix.Ixby.evalOp, left, right, arity, bind, Except.bind]
  | _ => rfl

theorem SameLayout.selectCase {source target} (same : SameLayout source target)
    (id : CtorId) (alternatives : List Alternative) :
    selectCase source id alternatives = selectCase target id alternatives := by
  induction alternatives with
  | nil => rfl
  | cons alternative alternatives ih => simp only [Ix.Ixby.selectCase, same.getConstructor, ih]

theorem SameLayout.stepApply {source target} (same : SameLayout source target) (limits : Limits)
    (state : State) (value : Value) (args : Array Value) :
    stepApply limits source state value args = stepApply limits target state value args := by
  cases value with
  | pap callee captured =>
    have functions := same.getFunction callee
    cases left : source.getFunction callee with
    | error error =>
      cases right : target.getFunction callee <;>
        simp_all [Ix.Ixby.stepApply, Except.map, bind, Except.bind]
    | ok first =>
      cases right : target.getFunction callee with
      | error error => simp [left, right, Except.map] at functions
      | ok second =>
        have layouts : functionLayout first = functionLayout second := by
          simpa [left, right, Except.map] using functions
        have arity := congrArg FunctionLayout.arity layouts
        change first.arity = second.arity at arity
        simp [Ix.Ixby.stepApply, left, right, arity, same.enter, bind, Except.bind]
  | _ => rfl

end Compilatrix.Ixby.Inline
