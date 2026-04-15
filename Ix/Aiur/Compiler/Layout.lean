module
public import Ix.Aiur.Stages.Concrete
public import Ix.Aiur.Stages.Bytecode
public import Lean.Data.RBTree

/-!
Circuit layout computation for Aiur bytecode.

Consumes `Concrete.Term`, so `typSize` has no `.mvar` or parametric `.app` arms
to reject — the failure modes `Ix/Aiur/Compiler/Layout.lean` has (at `:41, :93`
per the `unreachable!` audit) cannot happen.

The `gadget` arm of the previous `Layout` is dropped.
-/

public section
@[expose] section

namespace Aiur

namespace Concrete

/-! ## Flat size computation — total via `visited` set + depth bound.

Mirrors the pattern used in `Ix/Aiur/Semantics/Flatten.lean` to keep the
three mutual functions total: every `DataType.size` call inserts a fresh
name into `visited`, and we carry a `bound` parameter that upper-bounds
the remaining recursion depth. The outer interfaces use `decls.size + 1`
as bound — the monotonic visited set makes this bound unreachable on
well-formed inputs. -/

mutual

/-- See `Typ.size` for the outer interface. -/
def Typ.sizeBound (decls : Decls) : Nat → Std.HashSet Global → Typ →
    Except String Nat
  | 0, _, _ => pure 0
  | _+1, _, .unit => pure 0
  | _+1, _, .field => pure 1
  | _+1, _, .pointer _ => pure 1
  | _+1, _, .function _ _ => pure 1
  | bound+1, visited, .tuple ts =>
      ts.attach.foldlM (init := 0) fun acc ⟨t, _⟩ => do
        let s ← Typ.sizeBound decls bound visited t
        pure (acc + s)
  | bound+1, visited, .array t n => do
      let s ← Typ.sizeBound decls bound visited t
      pure (n * s)
  | bound+1, visited, .ref g => match decls.getByKey g with
    | some (.dataType dt) => DataType.sizeBound decls bound visited dt
    | _ => throw s!"Datatype not found: `{g}`"

/-- See `Constructor.size` for the outer interface. -/
def Constructor.sizeBound (decls : Decls) (bound : Nat) (visited : Std.HashSet Global)
    (c : Constructor) : Except String Nat :=
  c.argTypes.foldlM (init := 0) fun acc t => do
    let s ← Typ.sizeBound decls bound visited t
    pure (acc + s)

/-- See `DataType.size` for the outer interface. -/
def DataType.sizeBound (decls : Decls) : Nat → Std.HashSet Global → DataType →
    Except String Nat
  | 0, _, _ => pure 1
  | bound+1, visited, dt =>
    if visited.contains dt.name then
      throw s!"Cycle detected at datatype `{dt.name}`"
    else do
      let visited := visited.insert dt.name
      let ctorSizes ← dt.constructors.mapM
        (Concrete.Constructor.sizeBound decls bound visited)
      let maxFields := ctorSizes.foldl max 0
      pure (maxFields + 1)
end

/-- Outer interface: the recursion bound is `decls.size + 1`, which the
monotonic growth of `visited` (capped at `decls.size`) guarantees cannot
be exhausted on well-formed inputs. -/
def Typ.size (decls : Decls) (visited : Std.HashSet Global := {}) (t : Typ) :
    Except String Nat :=
  Typ.sizeBound decls (decls.size + 1) visited t

def Constructor.size (decls : Decls) (visited : Std.HashSet Global := {})
    (c : Constructor) : Except String Nat :=
  Constructor.sizeBound decls (decls.size + 1) visited c

def DataType.size (dt : DataType) (decls : Decls)
    (visited : Std.HashSet Global := {}) : Except String Nat :=
  DataType.sizeBound decls (decls.size + 1) visited dt

namespace Bytecode

structure SharedData where
  auxiliaries : Nat
  lookups : Nat

def SharedData.maximals (a b : SharedData) : SharedData := {
  auxiliaries := a.auxiliaries.max b.auxiliaries
  lookups := a.lookups.max b.lookups
}

abbrev MemSizes := Lean.RBTree Nat compare

structure LayoutMState where
  functionLayout : Aiur.Bytecode.FunctionLayout
  memSizes : MemSizes
  degrees : Array Nat

@[inline] def LayoutMState.new (inputSize : Nat) : LayoutMState :=
  ⟨{ inputSize, selectors := 0, auxiliaries := 1, lookups := 0 }, .empty, Array.replicate inputSize 1⟩

abbrev LayoutM := StateM LayoutMState

@[inline] def bumpSelectors (n : Nat := 1) : LayoutM Unit :=
  modify fun stt => { stt with
    functionLayout := { stt.functionLayout with selectors := stt.functionLayout.selectors + n } }

@[inline] def bumpLookups (n : Nat := 1) : LayoutM Unit :=
  modify fun stt => { stt with
    functionLayout := { stt.functionLayout with lookups := stt.functionLayout.lookups + n } }

@[inline] def bumpAuxiliaries (n : Nat := 1) : LayoutM Unit :=
  modify fun stt => { stt with
    functionLayout := { stt.functionLayout with auxiliaries := stt.functionLayout.auxiliaries + n } }

@[inline] def addMemSize (size : Nat) : LayoutM Unit :=
  modify fun stt => { stt with memSizes := stt.memSizes.insert size }

@[inline] def pushDegree (degree : Nat) : LayoutM Unit :=
  modify fun stt => { stt with degrees := stt.degrees.push degree }

@[inline] def pushDegrees (degrees : Array Nat) : LayoutM Unit :=
  modify fun stt => { stt with degrees := stt.degrees ++ degrees }

@[inline] def getDegrees : LayoutM $ Array Nat :=
  get >>= (pure ·.degrees)

@[inline] def getDegree (v : Aiur.Bytecode.ValIdx) : LayoutM Nat :=
  get >>= fun stt => pure (stt.degrees[v]?.getD 0)

@[inline] def setDegrees (degrees : Array Nat) : LayoutM Unit :=
  modify fun stt => { stt with degrees }

def getSharedData : LayoutM SharedData :=
  get >>= fun stt =>
    pure {
      auxiliaries := stt.functionLayout.auxiliaries
      lookups := stt.functionLayout.lookups
    }

def setSharedData (sharedData : SharedData) : LayoutM Unit :=
  modify fun stt => { stt with functionLayout := { stt.functionLayout with
    auxiliaries := sharedData.auxiliaries
    lookups := sharedData.lookups } }

def opLayout : Bytecode.Op → LayoutM Unit
  | .const _ => pushDegree 0
  | .add a b | .sub a b => do
    let aDegree ← getDegree a
    let bDegree ← getDegree b
    pushDegree (aDegree.max bDegree)
  | .mul a b => do
    let aDegree ← getDegree a
    let bDegree ← getDegree b
    let degree := aDegree + bDegree
    if degree < 2 then pushDegree degree
    else do pushDegree 1; bumpAuxiliaries
  | .eqZero a => do
    let degree ← getDegree a
    if degree = 0 then pushDegree 0
    else do pushDegree 1; bumpAuxiliaries 2
  | .call _ _ outputSize unconstrained => do
    pushDegrees $ .replicate outputSize 1
    bumpAuxiliaries outputSize
    if !unconstrained then bumpLookups
  | .store values => do
    pushDegree 1; bumpAuxiliaries; bumpLookups; addMemSize values.size
  | .load size _ => do
    pushDegrees $ .replicate size 1
    bumpAuxiliaries size; bumpLookups; addMemSize size
  | .assertEq .. => pure ()
  | .ioGetInfo _ => do pushDegrees #[1, 1]; bumpAuxiliaries 2
  | .ioSetInfo .. => pure ()
  | .ioRead _ len => do pushDegrees $ .replicate len 1; bumpAuxiliaries len
  | .ioWrite .. => pure ()
  | .u8BitDecomposition _ => do pushDegrees $ .replicate 8 1; bumpAuxiliaries 8; bumpLookups
  | .u8ShiftLeft _ | .u8ShiftRight _ | .u8Xor .. | .u8And .. | .u8Or .. => do
    pushDegree 1; bumpAuxiliaries; bumpLookups
  | .u8Add .. | .u8Sub .. => do pushDegrees #[1, 1]; bumpAuxiliaries 2; bumpLookups
  | .u8LessThan .. => do pushDegree 1; bumpAuxiliaries; bumpLookups
  | .u32LessThan .. => do pushDegree 1; bumpAuxiliaries 12; bumpLookups 6
  | .debug .. => pure ()

/-- Termination helper for blockLayout's Block/Ctrl traversal. -/
private theorem Bytecode.Block.sizeOf_ctrl_lt_layout (b : Bytecode.Block) :
    sizeOf b.ctrl < sizeOf b := by
  rcases b with ⟨ops, ctrl⟩
  show sizeOf ctrl < 1 + sizeOf ops + sizeOf ctrl
  omega

mutual

def ctrlLayout (c : Bytecode.Ctrl) : LayoutM Unit := match c with
  | .match _ branches defaultBranch => do
    let initSharedData ← getSharedData
    let degrees ← getDegrees
    -- Fold over branches, tracking the running maximum shared data.
    let maximalSharedData ← branches.attach.foldlM (init := initSharedData)
      fun currMax ⟨(_, block), _⟩ => do
        setSharedData initSharedData
        blockLayout block
        let blockSharedData ← getSharedData
        setDegrees degrees
        pure (currMax.maximals blockSharedData)
    -- Apply default branch if present.
    let finalMax ← match defaultBranch with
      | none => pure maximalSharedData
      | some defaultBlock => do
        setSharedData initSharedData
        bumpAuxiliaries branches.size
        blockLayout defaultBlock
        let defaultBlockSharedData ← getSharedData
        setDegrees degrees
        pure (maximalSharedData.maximals defaultBlockSharedData)
    setSharedData finalMax
  | .return .. => bumpSelectors
  | .yield .. => bumpSelectors
  | .matchContinue _ branches defaultBranch outputSize _sharedAux _sharedLookups continuation => do
    let initSharedData ← getSharedData
    let degrees ← getDegrees
    let maximalSharedData ← branches.attach.foldlM (init := initSharedData)
      fun currMax ⟨(_, block), _⟩ => do
        setSharedData initSharedData
        blockLayout block
        let blockSharedData ← getSharedData
        setDegrees degrees
        pure (currMax.maximals blockSharedData)
    let finalMax ← match defaultBranch with
      | none => pure maximalSharedData
      | some defaultBlock => do
        setSharedData initSharedData
        bumpAuxiliaries branches.size
        blockLayout defaultBlock
        let defaultBlockSharedData ← getSharedData
        setDegrees degrees
        pure (maximalSharedData.maximals defaultBlockSharedData)
    setSharedData finalMax
    bumpAuxiliaries outputSize
    pushDegrees (.replicate outputSize 1)
    blockLayout continuation
termination_by (sizeOf c, 0)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | grind

def blockLayout (block : Bytecode.Block) : LayoutM Unit := do
  block.ops.forM opLayout
  ctrlLayout block.ctrl
termination_by (sizeOf block, 1)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (apply Prod.Lex.left; exact Bytecode.Block.sizeOf_ctrl_lt_layout _)

end

end Bytecode

end Concrete

end Aiur

end -- @[expose] section
end
