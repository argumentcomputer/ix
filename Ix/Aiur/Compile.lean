module
public import Std.Data.HashMap
public import Lean.Data.RBTree
public import Ix.Aiur.Term
public import Ix.Aiur.Bytecode

public section

namespace Aiur

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

abbrev LayoutM := ReaderT TypedDecls $ StateM LayoutMState

@[inline] def bumpSelectors : LayoutM Unit :=
  modify fun stt => { stt with
    functionLayout := { stt.functionLayout with selectors := stt.functionLayout.selectors + 1 } }

@[inline] def bumpLookups : LayoutM Unit :=
  modify fun stt => { stt with
    functionLayout := { stt.functionLayout with lookups := stt.functionLayout.lookups + 1 } }

@[inline] def bumpAuxiliaries (n : Nat) : LayoutM Unit :=
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
      bumpAuxiliaries 1
  | .eqZero a => do
    let degree ← getDegree a
    if degree = 0 then pushDegree 0
    else
      pushDegrees #[1, 1]
      bumpAuxiliaries 2
  | .call funIdx _ outputSize => do
    pushDegrees $ .replicate outputSize 1
    bumpAuxiliaries outputSize
    let decls ← read
    if !decls.isUnconstrainedFunction funIdx then bumpLookups
  | .store values => do
    pushDegree 1
    bumpAuxiliaries 1
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
    bumpAuxiliaries 1
    bumpLookups
  | .u8Add .. | .u8Sub .. => do
    pushDegrees #[1, 1]
    bumpAuxiliaries 2
    bumpLookups
  | .u8LessThan .. => do
    pushDegree 1
    bumpAuxiliaries 1
    bumpLookups
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

structure DataTypeLayout where
  size: Nat
  deriving Inhabited

structure FunctionLayout where
  index: Nat
  inputSize : Nat
  outputSize : Nat
  offsets: Array Nat
  deriving Inhabited

structure ConstructorLayout where
  index: Nat
  size: Nat
  offsets: Array Nat
  deriving Inhabited

structure GadgetLayout where
  index : Nat
  outputSize : Nat
  deriving Inhabited

inductive Layout
  | dataType : DataTypeLayout → Layout
  | function : FunctionLayout → Layout
  | constructor : ConstructorLayout → Layout
  | gadget : GadgetLayout → Layout
  deriving Inhabited

abbrev LayoutMap := Std.HashMap Global Layout

def TypedDecls.layoutMap (decls : TypedDecls) : Except String LayoutMap := do
  let pass := fun (layoutMap, funcIdx, gadgetIdx) (_, v) => do match v with
    | .dataType dataType =>
      let dataTypeSize ← dataType.size decls
      let layoutMap := layoutMap.insert dataType.name (.dataType { size := dataTypeSize })
      let pass := fun (acc, index) constructor => do
        let offsets ← constructor.argTypes.foldlM (init := #[0]) fun offsets typ => do
          let typSyze ← typ.size decls
          pure $ offsets.push (offsets[offsets.size - 1]! + typSyze)
        let decl := .constructor { size := dataTypeSize, offsets, index }
        let name := dataType.name.pushNamespace constructor.nameHead
        pure (acc.insert name decl, index + 1)
      let (layoutMap, _) ← dataType.constructors.foldlM pass (layoutMap, 0)
      pure (layoutMap, funcIdx, gadgetIdx)
    | .function function =>
      let inputSize ← function.inputs.foldlM (init := 0) fun acc (_, typ) => do
        let typSize ← typ.size decls
        pure $ acc + typSize
      let outputSize ← function.output.size decls
      let offsets ← function.inputs.foldlM (init := #[0]) fun offsets (_, typ) => do
        let typSyze ← typ.size decls
        pure $ offsets.push (offsets[offsets.size - 1]! + typSyze)
      let layoutMap := layoutMap.insert function.name $
        .function { index := funcIdx, inputSize, outputSize, offsets }
      pure (layoutMap, funcIdx + 1, gadgetIdx)
    | .constructor .. => pure (layoutMap, funcIdx, gadgetIdx)
  let (layoutMap, _) ← decls.foldlM pass ({}, 0, 0)
  pure layoutMap

def typSize (layoutMap : LayoutMap) : Typ → Except String Nat
| .unit => pure 0
| .field .. => pure 1
| .pointer .. => pure 1
| .function .. => pure 1
| .tuple ts => ts.foldlM (init := 0) fun acc t => do
  let tSize ← typSize layoutMap t
  pure $ acc + tSize
| .array typ n => do
  let size ← typSize layoutMap typ
  pure $ n * size
| .dataType g => match layoutMap[g]? with
  | some (.dataType layout) => pure layout.size
  | _ => throw "Impossible case"

structure CompilerState where
  valIdx : Bytecode.ValIdx
  ops : Array Bytecode.Op
  selIdx : Bytecode.SelIdx
  deriving Inhabited

abbrev CompileM := EStateM String CompilerState

def pushOp (op : Bytecode.Op) (size : Nat := 1) : CompileM (Array Bytecode.ValIdx) :=
  modifyGet (fun s =>
    let valIdx := s.valIdx
    let ops := s.ops
    (Array.range' valIdx size, { s with valIdx := valIdx + size, ops := ops.push op}))

def extractOps : CompileM (Array Bytecode.Op) :=
  modifyGet fun s => (s.ops, {s with ops := #[]})

partial def toIndex
 (layoutMap : LayoutMap)
 (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
 (term : TypedTerm) : CompileM (Array Bytecode.ValIdx) :=
  match term.inner with
  -- | .unsafeCast inner castTyp =>
  --   if typSize layoutMap castTyp != typSize layoutMap term.typ then
  --     throw "Impossible cast"
  --   else
  --     toIndex layoutMap bindings (.mk term.typ inner)
  | .unit => pure #[]
  | .ret .. => throw "Should not happen after typechecking"
  | .match .. => throw "Non-tail `match` not yet implemented"
  | .var name => pure bindings[name]!
  | .ref name => match layoutMap[name]! with
    | .function layout => do
      pushOp (.const (.ofNat layout.index))
    | .constructor layout => do
      let size := layout.size
      let paddingOp := .const (.ofNat layout.index)
      let index ← pushOp paddingOp
      if index.size < size then
        let padding := (← pushOp paddingOp)[0]!
        pure $ index ++ Array.replicate (size - index.size) padding
      else
        pure index
    | _ => throw "Should not happen after typechecking"
  | .data (.field g) => pushOp (Bytecode.Op.const g)
  | .data (.tuple terms) | .data (.array terms) =>
      terms.foldlM (init := #[]) fun acc arg => do
        pure $ acc ++ (← toIndex layoutMap bindings arg)
  | .let (.var var) val bod => do
    let val ← toIndex layoutMap bindings val
    toIndex layoutMap (bindings.insert var val) bod
  | .let .. => throw "Should not happen after simplifying"
  | .add a b => do
    let a ← expectIdx a
    let b ← expectIdx b
    pushOp (.add a b)
  | .sub a b => do
    let a ← expectIdx a
    let b ← expectIdx b
    pushOp (.sub a b)
  | .mul a b => do
    let a ← expectIdx a
    let b ← expectIdx b
    pushOp (.mul a b)
  | .eqZero a => do
    let a ← expectIdx a
    pushOp (.eqZero a)
  | .app name@(⟨.str .anonymous unqualifiedName⟩) args =>
    match bindings.get? (.str unqualifiedName) with
    | some _ => throw "Dynamic calls not yet implemented"
    | none => match layoutMap[name]! with
      | .function layout => do
        let args ← buildArgs args
        pushOp (Bytecode.Op.call layout.index args layout.outputSize) layout.outputSize
      | .constructor layout => do
        let size := layout.size
        let index ← pushOp (.const (.ofNat layout.index))
        let index ← buildArgs args index
        if index.size < size then
          let padding := (← pushOp (.const (.ofNat 0)))[0]!
          pure $ index ++ Array.replicate (size - index.size) padding
        else
          pure index
      | _ => throw "Should not happen after typechecking"
  | .app name args => match layoutMap[name]! with
    | .function layout => do
      let args ← buildArgs args
      pushOp (Bytecode.Op.call layout.index args layout.outputSize) layout.outputSize
    | .constructor layout => do
      let size := layout.size
      let index ← pushOp (.const (.ofNat layout.index))
      let index ← buildArgs args index
      if index.size < size then
        let padding := (← pushOp (.const (.ofNat 0)))[0]!
        pure $ index ++ Array.replicate (size - index.size) padding
      else
        pure index
    | _ => throw "Should not happen after typechecking"
  -- | .preimg name@(⟨.str .anonymous unqualifiedName⟩) out =>
  --   match bindings.get? (.str unqualifiedName) with
  --   | some _ => throw "dynamic preimage not yet implemented"
  --   | none => match layoutMap.get' name with
  --     | .function layout => do
  --       let out ← toIndex layoutMap bindings out
  --       pushOp (Bytecode.Op.preimg layout.index out layout.inputSize) layout.inputSize
  --     | _ => throw "should not happen after typechecking"
  -- | .preimg name out => match layoutMap.get' name with
  --   | .function layout => do
  --     let out ← toIndex layoutMap bindings out
  --     pushOp (Bytecode.Op.preimg layout.index out layout.inputSize) layout.inputSize
  --   | _ => throw "should not happen after typechecking"
  | .proj arg i => do
    let typs ← match (arg.typ, arg.escapes) with
      | (.tuple typs, false) => pure typs
      | _ => throw "Should not happen after typechecking"
    let offset ← (typs.extract 0 i).foldlM (init := 0) fun acc typ => do
      let typLen ← match typSize layoutMap typ with
        | .error e => throw e
        | .ok len => pure len
      pure $ typLen + acc
    let arg ← toIndex layoutMap bindings arg
    let iLen ← match typSize layoutMap typs[i]! with
      | .error e => throw e
      | .ok len => pure len
    pure $ arg.extract offset (offset + iLen)
  | .get arr i => do
    let eltTyp ← match (arr.typ, arr.escapes) with
      | (.array typ _, false) => pure typ
      | _ => throw "Should not happen after typechecking"
    let eltSize ← match typSize layoutMap eltTyp with
      | .error e => throw e
      | .ok len => pure len
    let offset := i * eltSize
    let arr ← toIndex layoutMap bindings arr
    pure $ arr.extract offset (offset + eltSize)
  | .slice arr i j => do
    let eltTyp ← match (arr.typ, arr.escapes) with
      | (.array typ _, false) => pure typ
      | _ => throw "Should not happen after typechecking"
    let eltSize ← match typSize layoutMap eltTyp with
      | .error e => throw e
      | .ok len => pure len
    let arr ← toIndex layoutMap bindings arr
    pure $ arr.extract (i * eltSize) (j * eltSize)
  | .set arr i val => do
    let eltTyp ← match (arr.typ, arr.escapes) with
      | (.array typ _, false) => pure typ
      | _ => throw "Should not happen after typechecking"
    let eltSize ← match typSize layoutMap eltTyp with
      | .error e => throw e
      | .ok len => pure len
    let arr ← toIndex layoutMap bindings arr
    let left := arr.extract 0 (i * eltSize)
    let val ← toIndex layoutMap bindings val
    let right := arr.extract ((i + 1) * eltSize)
    pure $ left ++ val ++ right
  | .store arg => do
    let args ← toIndex layoutMap bindings arg
    pushOp (.store args)
  | .load ptr => do
    let size ← match (ptr.typ, ptr.escapes) with
    | (.pointer typ, false) => match typSize layoutMap typ with
      | .error e => throw e
      | .ok len => pure len
    | _ => throw "Impossible case"
    let ptr ← expectIdx ptr
    pushOp (.load size ptr) size
  | .ptrVal ptr => toIndex layoutMap bindings ptr
  -- | .trace str expr => do
  --   let arr ← toIndex layoutMap bindings expr
  --   let op := .trace str arr
  --   modify (fun state => { state with ops := state.ops.push op})
  --   pure arr
  | .assertEq a b ret => do
    let a ← toIndex layoutMap bindings a
    let b ← toIndex layoutMap bindings b
    modify fun stt => { stt with ops := stt.ops.push (.assertEq a b) }
    toIndex layoutMap bindings ret
  | .ioGetInfo key => do
    let key ← toIndex layoutMap bindings key
    pushOp (.ioGetInfo key) 2
  | .ioSetInfo key idx len ret => do
    let key ← toIndex layoutMap bindings key
    let idx ← expectIdx idx
    let len ← expectIdx len
    modify fun stt => { stt with ops := stt.ops.push (.ioSetInfo key idx len) }
    toIndex layoutMap bindings ret
  | .ioRead idx len => do
    let idx ← expectIdx idx
    pushOp (.ioRead idx len) len
  | .ioWrite data ret => do
    let data ← toIndex layoutMap bindings data
    modify fun stt => { stt with ops := stt.ops.push (.ioWrite data) }
    toIndex layoutMap bindings ret
  | .u8BitDecomposition byte => do
    let byte ← expectIdx byte
    pushOp (.u8BitDecomposition byte) 8
  | .u8ShiftLeft byte => do
    let byte ← expectIdx byte
    pushOp (.u8ShiftLeft byte)
  | .u8ShiftRight byte => do
    let byte ← expectIdx byte
    pushOp (.u8ShiftRight byte)
  | .u8Xor i j => do
    let i ← expectIdx i
    let j ← expectIdx j
    pushOp (.u8Xor i j)
  | .u8Add i j => do
    let i ← expectIdx i
    let j ← expectIdx j
    pushOp (.u8Add i j) 2
  | .u8Sub i j => do
    let i ← expectIdx i
    let j ← expectIdx j
    pushOp (.u8Sub i j) 2
  | .u8And i j => do
    let i ← expectIdx i
    let j ← expectIdx j
    pushOp (.u8And i j)
  | .u8Or i j => do
    let i ← expectIdx i
    let j ← expectIdx j
    pushOp (.u8Or i j)
  | .u8LessThan i j => do
    let i ← expectIdx i
    let j ← expectIdx j
    pushOp (.u8LessThan i j)
  | .debug label term ret => do
    let term ← term.mapM (toIndex layoutMap bindings)
    modify fun stt => { stt with ops := stt.ops.push (.debug label term) }
    toIndex layoutMap bindings ret
  where
    buildArgs (args : List TypedTerm) (init := #[]) :=
      let append acc arg := do
        pure (acc.append (← toIndex layoutMap bindings arg))
      args.foldlM (init := init) append
    expectIdx term := do
      let idxs ← toIndex layoutMap bindings term
      if h : idxs.size = 1 then
        have : 0 < idxs.size := by simp only [h, Nat.lt_add_one]
        pure idxs[0]
      else throw "Term is not of size 1"

mutual

partial def TypedTerm.compile
 (term : TypedTerm)
 (returnTyp : Typ)
 (layoutMap : LayoutMap)
 (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
: CompileM Bytecode.Block := match term.inner with
  | .let (.var var) val bod => do
    let val ← toIndex layoutMap bindings val
    bod.compile returnTyp layoutMap (bindings.insert var val)
  | .let .. => throw "Should not happen after simplifying"
  | .debug label term ret => do
    let term ← term.mapM (toIndex layoutMap bindings)
    modify fun stt => { stt with ops := stt.ops.push (.debug label term) }
    ret.compile returnTyp layoutMap bindings
  | .match term cases =>
    match term.typ with
    -- Also do this for tuple-like and array-like (one constructor only) datatypes
    | .tuple typs => match cases with
      | [(.tuple vars, branch)] => do
        let bindArgs bindings pats typs idxs := do
          let (bindings, _) ← (pats.zip typs).foldlM (init := (bindings, 0))
            fun (bindings, offset) (pat, typ) => match pat with
              | .var var => do
                let len ← match typSize layoutMap typ with
                  | .error e => throw e
                  | .ok len => pure len
                let newOffset := offset + len
                pure (bindings.insert var (idxs.extract offset newOffset), newOffset)
              | _ => throw "Should not happen after simplification"
          pure bindings
        let idxs ← toIndex layoutMap bindings term
        let bindings ← bindArgs bindings vars typs idxs
        branch.compile returnTyp layoutMap bindings
      | _ => throw "Impossible case"
    | .array typ _ => match cases with
      | [(.array vars, branch)] => do
        let bindArgs bindings pats idxs := do
          let len ← match typSize layoutMap typ with
            | .error e => throw e
            | .ok len => pure len
          let (bindings, _) ← pats.foldlM (init := (bindings, 0))
            fun (bindings, offset) pat => match pat with
              | .var var =>
                let newOffset := offset + len
                pure (bindings.insert var (idxs.extract offset newOffset), newOffset)
              | _ => throw "Should not happen after simplification"
          pure bindings
        let idxs ← toIndex layoutMap bindings term
        let bindings ← bindArgs bindings vars idxs
        branch.compile returnTyp layoutMap bindings
      | _ => throw "Impossible case"
    | _ => do
      let idxs ← toIndex layoutMap bindings term
      let ops ← extractOps
      let minSelIncluded := (← get).selIdx
      let (cases, default) ← cases.foldlM (init := default)
        (addCase layoutMap bindings returnTyp idxs)
      let maxSelExcluded := (← get).selIdx
      let ctrl := .match idxs[0]! cases default
      pure { ops, ctrl, minSelIncluded, maxSelExcluded }
  | .ret term => do
    let idxs ← toIndex layoutMap bindings term
    let state ← get
    let state := { state with selIdx := state.selIdx + 1 }
    set state
    let ops := state.ops
    let id := state.selIdx
    pure { ops, ctrl := .return (id - 1) idxs, minSelIncluded := id - 1, maxSelExcluded := id }
  | _ => do
    let idxs ← toIndex layoutMap bindings term
    let state ← get
    let state := { state with selIdx := state.selIdx + 1 }
    set state
    let ops := state.ops
    let id := state.selIdx
    pure { ops, ctrl := .return (id - 1) idxs, minSelIncluded := id - 1, maxSelExcluded := id }

partial def addCase
  (layoutMap : LayoutMap)
  (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
  (returnTyp : Typ)
  (idxs : Array Bytecode.ValIdx)
: (Array (G × Bytecode.Block) × Option Bytecode.Block) →
  (Pattern × TypedTerm) →
  CompileM (Array (G × Bytecode.Block) × Option Bytecode.Block) := fun (cases, default) (pat, term) =>
  -- If simplified, only one default will exist, and it will appear at the end of the match
  assert! default.isNone
  match pat with
  | .field g => do
    let initState ← get
    let term ← term.compile returnTyp layoutMap bindings
    set { initState with selIdx := (← get).selIdx }
    let cases' := cases.push (g, term)
    pure (cases', default)
  | .ref global pats => do
    let layout := layoutMap[global]!
    let (index, offsets) ← match layout with
    | .function layout => pure (layout.index, layout.offsets)
    | .constructor layout => pure (layout.index, layout.offsets)
    | .dataType _
    | .gadget _ => throw "Impossible after typechecking"
    let bindArgs bindings pats offsets idxs := do
      let n := pats.length
      let bindings ← (List.range n).foldlM (init := bindings) fun bindings i =>
        let pat := pats[i]!
        -- the `+ 1` is to account for the tag
        let offset := offsets[i]! + 1
        let next_offset := offsets[(i + 1)]! + 1
        match pat with
        | .var var =>
          pure $ bindings.insert var (idxs.extract offset next_offset)
        | _ => throw "Should not happen after simplification"
      pure bindings
    let bindings ← bindArgs bindings pats offsets idxs
    let initState ← get
    let term ← term.compile returnTyp layoutMap bindings
    set { initState with selIdx := (← get).selIdx }
    let cases' := cases.push (.ofNat index, term)
    pure (cases', default)
  | .wildcard => do
    let initState ← get
    let term ← term.compile returnTyp layoutMap bindings
    set { initState with selIdx := (← get).selIdx }
    pure (cases, .some term)
  | _ => throw "Impossible case"

end

def TypedFunction.compile (decls : TypedDecls) (layoutMap : LayoutMap) (f : TypedFunction) :
    Except String (Bytecode.Block × Bytecode.LayoutMState) := do
  let (inputSize, _outputSize) ← match layoutMap[f.name]? with
    | some (.function layout) => pure (layout.inputSize, layout.outputSize)
    | _ => throw s!"`{f.name}` should be a function"
  let (valIdx, bindings) ← f.inputs.foldlM (init := (0, default))
    fun (valIdx, bindings) (arg, typ) => do
      let len ← match typSize layoutMap typ with
        | .error e => throw e
        | .ok len => pure len
      let indices := Array.range' valIdx len
      pure (valIdx + len, bindings.insert arg indices)
  let state := { valIdx, selIdx := 0, ops := #[] }
  match f.body.compile f.output layoutMap bindings |>.run state with
  | .error e _ => throw e
  | .ok body _ =>
    let (_, layoutMState) := Bytecode.blockLayout body |>.run decls (.new inputSize)
    pure (body, layoutMState)

def TypedDecls.compile (decls : TypedDecls) : Except String Bytecode.Toplevel := do
  let layout ← decls.layoutMap
  let initMemSizes : Bytecode.MemSizes := .empty
  let (functions, memSizes) ← decls.foldlM (init := (#[], initMemSizes))
    fun acc@(functions, memSizes) (_, decl) => match decl with
      | .function function => do
        let (body, layoutMState) ← function.compile decls layout
        let function := ⟨body, layoutMState.functionLayout, function.unconstrained⟩
        let memSizes := layoutMState.memSizes.fold (·.insert ·) memSizes
        pure (functions.push function, memSizes)
      | _ => pure acc
  pure ⟨functions, memSizes.toArray⟩

end Aiur

end
