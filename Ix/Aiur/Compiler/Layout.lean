module
public import Std.Data.HashSet.Basic
public import Ix.Aiur.Term
public import Ix.Aiur.Bytecode
public import Lean.Data.RBTree

/-!
Circuit layout computation for Aiur bytecode.

Walks a compiled `Block` to determine how many selectors, auxiliaries, and lookups
each function's circuit requires. The result (`FunctionLayout`) is used by the Rust
backend to allocate columns in the constraint system.
-/

public section

namespace Aiur

mutual

open Std (HashSet)

partial def Typ.size (decls : TypedDecls) (visited : HashSet Global := {}) :
    Typ → Except String Nat
  | .unit => pure 0
  | .field .. => pure 1
  | .pointer .. => pure 1
  | .function .. => pure 1
  | .tuple ts => ts.foldlM (init := 0) fun acc t => do
    let tSize ← t.size decls visited
    pure $ acc + tSize
  | .array t n => do
    let tSize ← t.size decls visited
    pure $ n * tSize
  | .ref g => match decls.getByKey g with
    | some (.dataType data) => data.size decls visited
    | _ => throw s!"Datatype not found: `{g}`"

partial def Constructor.size (decls : TypedDecls) (visited : HashSet Global := {})
    (c : Constructor) : Except String Nat :=
  c.argTypes.foldlM (init := 0) fun acc t => do
    let tSize ← t.size decls visited
    pure $ acc + tSize

partial def DataType.size (dt : DataType) (decls : TypedDecls)
    (visited : HashSet Global := {}) : Except String Nat :=
  if visited.contains dt.name then
    throw s!"Cycle detected at datatype `{dt.name}`"
  else do
    let visited := visited.insert dt.name
    let ctorSizes ← dt.constructors.mapM (Constructor.size decls visited)
    let maxFields := ctorSizes.foldl max 0
    pure $ maxFields + 1
end

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
  functionLayout : FunctionLayout
  memSizes : MemSizes
  degrees : Array Nat

/-- A new `LayoutMState` starts with one auxiliar for the multiplicity. -/
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

@[inline] def getDegree (v : ValIdx) : LayoutM Nat :=
  get >>= fun stt => pure stt.degrees[v]!

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
    pushDegree $ aDegree.max bDegree
  | .mul a b => do
    let aDegree ← getDegree a
    let bDegree ← getDegree b
    let degree := aDegree + bDegree
    if degree < 2 then
      pushDegree degree
    else
      pushDegree 1
      bumpAuxiliaries
  | .eqZero a => do
    let degree ← getDegree a
    if degree = 0 then pushDegree 0
    else
      pushDegree 1
      bumpAuxiliaries 2
  | .call _ _ outputSize unconstrained => do
    pushDegrees $ .replicate outputSize 1
    bumpAuxiliaries outputSize
    if !unconstrained then bumpLookups
  | .store values => do
    pushDegree 1
    bumpAuxiliaries
    bumpLookups
    addMemSize values.size
  | .load size _ => do
    pushDegrees $ .replicate size 1
    bumpAuxiliaries size
    bumpLookups
    addMemSize size
  | .assertEq .. => pure ()
  | .ioGetInfo _ => do
    pushDegrees #[1, 1]
    bumpAuxiliaries 2
  | .ioSetInfo .. => pure ()
  | .ioRead _ len => do
    pushDegrees $ .replicate len 1
    bumpAuxiliaries len
  | .ioWrite .. => pure ()
  | .u8BitDecomposition _ => do
    pushDegrees $ .replicate 8 1
    bumpAuxiliaries 8
    bumpLookups
  | .u8ShiftLeft _ | .u8ShiftRight _ | .u8Xor .. | .u8And .. | .u8Or .. => do
    pushDegree 1
    bumpAuxiliaries
    bumpLookups
  | .u8Add .. | .u8Sub .. => do
    pushDegrees #[1, 1]
    bumpAuxiliaries 2
    bumpLookups
  | .u8LessThan .. => do
    pushDegree 1
    bumpAuxiliaries
    bumpLookups
  | .u32LessThan .. => do
    pushDegree 1
    bumpAuxiliaries 12
    bumpLookups 6
  | .debug .. => pure ()

partial def blockLayout (block : Bytecode.Block) : LayoutM Unit := do
  block.ops.forM opLayout
  match block.ctrl with
  | .match _ branches defaultBranch =>
    let initSharedData ← getSharedData
    let mut maximalSharedData := initSharedData
    let mut degrees ← getDegrees
    for (_, block) in branches do
      setSharedData initSharedData
      blockLayout block
      let blockSharedData ← getSharedData
      maximalSharedData := maximalSharedData.maximals blockSharedData
      setDegrees degrees
    if let some defaultBlock := defaultBranch then
      setSharedData initSharedData
      -- An auxiliary per case for proving inequality
      bumpAuxiliaries branches.size
      blockLayout defaultBlock
      let defaultBlockSharedData ← getSharedData
      maximalSharedData := maximalSharedData.maximals defaultBlockSharedData
      setDegrees degrees
    setSharedData maximalSharedData
  | .return .. =>
    bumpSelectors
    bumpLookups

end Bytecode

end Aiur

end
