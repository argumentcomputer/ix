import Std.Data.HashMap
import Lean.Data.RBTree
import Ix.Aiur.Term
import Ix.Aiur.Bytecode

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

abbrev LayoutM := StateM LayoutMState

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
  | .call _ _ outputSize => do
    pushDegrees $ .replicate outputSize 1
    bumpAuxiliaries outputSize
    bumpLookups
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
  | .u8ShiftLeft _ | .u8ShiftRight _ | .u8Xor .. => do
    pushDegree 1
    bumpAuxiliaries 1
    bumpLookups
  | .u8Add .. => do
    pushDegrees #[1, 1]
    bumpAuxiliaries 2
    bumpLookups

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

def TypedDecls.layoutMap (decls : TypedDecls) : LayoutMap :=
  let pass := fun (layoutMap, funcIdx, gadgetIdx) (_, v) => match v with
    | .dataType dataType =>
      let dataTypeSize := dataType.size decls
      let layoutMap := layoutMap.insert dataType.name (.dataType { size := dataTypeSize })
      let pass := fun (acc, index) constructor =>
        let offsets := constructor.argTypes.foldl (init := #[0])
          fun offsets typ => offsets.push (offsets[offsets.size - 1]! + typ.size decls)
        let decl := .constructor { size := dataTypeSize, offsets, index }
        let name := dataType.name.pushNamespace constructor.nameHead
        (acc.insert name decl, index + 1)
      let (layoutMap, _) := dataType.constructors.foldl (init := (layoutMap, 0)) pass
      (layoutMap, funcIdx, gadgetIdx)
    | .function function =>
      let inputSize := function.inputs.foldl (init := 0) fun acc (_, typ) => acc + typ.size decls
      let outputSize := function.output.size decls
      let offsets := function.inputs.foldl (init := #[0])
        fun offsets (_, typ) => offsets.push (offsets[offsets.size - 1]! + typ.size decls)
      let layoutMap := layoutMap.insert function.name $
        .function { index := funcIdx, inputSize, outputSize, offsets }
      (layoutMap, funcIdx + 1, gadgetIdx)
    | .constructor .. => (layoutMap, funcIdx, gadgetIdx)
  let (layoutMap, _) := decls.foldl pass ({}, 0, 0)
  layoutMap

def typSize (layoutMap : LayoutMap) : Typ → Nat
| .unit => 0
| .field .. => 1
| .pointer .. => 1
| .function .. => 1
| .tuple ts => ts.foldl (fun acc t => acc + typSize layoutMap t) 0
| .array typ n => n * typSize layoutMap typ
| .dataType g => match layoutMap[g]? with
  | some (.dataType layout) => layout.size
  | _ => unreachable!

structure CompilerState where
  valIdx : Bytecode.ValIdx
  ops : Array Bytecode.Op
  selIdx : Bytecode.SelIdx
  deriving Inhabited

def pushOp (op : Bytecode.Op) (size : Nat := 1) : StateM CompilerState (Array Bytecode.ValIdx) :=
  modifyGet (fun s =>
    let valIdx := s.valIdx
    let ops := s.ops
    (Array.range' valIdx size, { s with valIdx := valIdx + size, ops := ops.push op}))

def extractOps : StateM CompilerState (Array Bytecode.Op) :=
  modifyGet fun s => (s.ops, {s with ops := #[]})

partial def toIndex
 (layoutMap : LayoutMap)
 (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
 (term : TypedTerm) : StateM CompilerState (Array Bytecode.ValIdx) :=
  match term.inner with
  | .unit => pure #[]
  | .ret .. => panic! "Should not happen after typechecking"
  | .match .. => panic! "Non-tail `match` not yet implemented"
  | .var name => do
    pure (bindings[name]!)
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
    | _ => panic! "Should not happen after typechecking"
  | .data (.field g) => pushOp (Bytecode.Op.const g)
  | .data (.tuple terms) | .data (.array terms) =>
      terms.foldlM (init := #[]) fun acc arg => do
        pure $ acc ++ (← toIndex layoutMap bindings arg)
  | .let (.var var) val bod => do
    let val ← toIndex layoutMap bindings val
    toIndex layoutMap (bindings.insert var val) bod
  | .let .. => panic! "Should not happen after simplifying"
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
    | some _ => panic! "Dynamic calls not yet implemented"
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
      | _ => panic! "Should not happen after typechecking"
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
    | _ => panic! "Should not happen after typechecking"
  -- | .preimg name@(⟨.str .anonymous unqualifiedName⟩) out =>
  --   match bindings.get? (.str unqualifiedName) with
  --   | some _ => panic! "dynamic preimage not yet implemented"
  --   | none => match layoutMap.get' name with
  --     | .function layout => do
  --       let out ← toIndex layoutMap bindings out
  --       pushOp (Bytecode.Op.preimg layout.index out layout.inputSize) layout.inputSize
  --     | _ => panic! "should not happen after typechecking"
  -- | .preimg name out => match layoutMap.get' name with
  --   | .function layout => do
  --     let out ← toIndex layoutMap bindings out
  --     pushOp (Bytecode.Op.preimg layout.index out layout.inputSize) layout.inputSize
  --   | _ => panic! "should not happen after typechecking"
  | .proj arg i => do
    let typs := match arg.typ with
      | .evaluates (.tuple typs) => typs
      | _ => panic! "Should not happen after typechecking"
    let offset := (typs.extract 0 i).foldl (init := 0)
      fun acc typ => typSize layoutMap typ + acc
    let arg ← toIndex layoutMap bindings arg
    let length := typSize layoutMap typs[i]!
    pure $ arg.extract offset (offset + length)
  | .get arr i => do
    let eltTyp := match arr.typ with
      | .evaluates (.array typ _) => typ
      | _ => panic! "Should not happen after typechecking"
    let eltSize := typSize layoutMap eltTyp
    let offset := i * eltSize
    let arr ← toIndex layoutMap bindings arr
    pure $ arr.extract offset (offset + eltSize)
  | .slice arr i j => do
    let eltTyp := match arr.typ with
      | .evaluates (.array typ _) => typ
      | _ => panic! "Should not happen after typechecking"
    let eltSize := typSize layoutMap eltTyp
    let arr ← toIndex layoutMap bindings arr
    pure $ arr.extract (i * eltSize) (j * eltSize)
  | .set arr i val => do
    let eltTyp := match arr.typ with
      | .evaluates (.array typ _) => typ
      | _ => panic! "Should not happen after typechecking"
    let eltSize := typSize layoutMap eltTyp
    let arr ← toIndex layoutMap bindings arr
    let left := arr.extract 0 (i * eltSize)
    let val ← toIndex layoutMap bindings val
    let right := arr.extract ((i + 1) * eltSize)
    pure $ left ++ val ++ right
  | .store arg => do
    let args ← toIndex layoutMap bindings arg
    pushOp (.store args)
  | .load ptr => do
    let size := match ptr.typ.unwrap with
    | .pointer typ => typSize layoutMap typ
    | _ => unreachable!
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
      else panic! "Term is not of size 1"

mutual

partial def TypedTerm.compile
 (term : TypedTerm)
 (returnTyp : Typ)
 (layoutMap : LayoutMap)
 (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
: StateM CompilerState Bytecode.Block := match term.inner with
  | .let (.var var) val bod => do
    let val ← toIndex layoutMap bindings val
    bod.compile returnTyp layoutMap (bindings.insert var val)
  | .let .. => panic! "Should not happen after simplifying"
  | .match term cases =>
    match term.typ.unwrapOr returnTyp with
    -- Also do this for tuple-like and array-like (one constructor only) datatypes
    | .tuple typs => match cases with
      | [(.tuple vars, branch)] => do
        let bindArgs bindings pats typs idxs :=
          let (bindings, _) := (pats.zip typs).foldl (init := (bindings, 0))
            fun (bindings, offset) (pat, typ) => match pat with
              | .var var =>
                let len := typSize layoutMap typ
                let newOffset := offset + len
                (bindings.insert var (idxs.extract offset newOffset), newOffset)
              | _ => panic! "Should not happen after simplification"
          bindings
        let idxs ← toIndex layoutMap bindings term
        let bindings := bindArgs bindings vars typs idxs
        branch.compile returnTyp layoutMap bindings
      | _ => unreachable!
    | .array typ _ => match cases with
      | [(.array vars, branch)] => do
        let bindArgs bindings pats idxs :=
          let len := typSize layoutMap typ
          let (bindings, _) := pats.foldl (init := (bindings, 0))
            fun (bindings, offset) pat => match pat with
              | .var var =>
                let newOffset := offset + len
                (bindings.insert var (idxs.extract offset newOffset), newOffset)
              | _ => panic! "Should not happen after simplification"
          bindings
        let idxs ← toIndex layoutMap bindings term
        let bindings := bindArgs bindings vars idxs
        branch.compile returnTyp layoutMap bindings
      | _ => unreachable!
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
  StateM CompilerState (Array (G × Bytecode.Block) × Option Bytecode.Block) := fun (cases, default) (pat, term) =>
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
    let (index, offsets) := match layout with
    | .function layout => (layout.index, layout.offsets)
    | .constructor layout => (layout.index, layout.offsets)
    | .dataType _
    | .gadget _ => panic! "Impossible after typechecking"
    let bindArgs bindings pats offsets idxs :=
      let n := pats.length
      let bindings := (List.range n).foldl (init := bindings) fun bindings i =>
        let pat := pats[i]!
        -- the `+ 1` is to account for the tag
        let offset := offsets[i]! + 1
        let next_offset := offsets[(i + 1)]! + 1
        match pat with
        | .var var =>
          bindings.insert var (idxs.extract offset next_offset)
        | _ => panic! "Should not happen after simplification"
      bindings
    let bindings := bindArgs bindings pats offsets idxs
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
  | _ => unreachable!

end

def TypedFunction.compile (layoutMap : LayoutMap) (f : TypedFunction) :
    Bytecode.Block × Bytecode.LayoutMState :=
  let (inputSize, _outputSize) := match layoutMap[f.name]? with
    | some (.function layout) => (layout.inputSize, layout.outputSize)
    | _ => panic! s!"`{f.name}` should be a function"
  let (valIdx, bindings) := f.inputs.foldl (init := (0, default))
    fun (valIdx, bindings) (arg, typ) =>
      let len := typSize layoutMap typ
      let indices := Array.range' valIdx len
      (valIdx + len, bindings.insert arg indices)
  let state := { valIdx, selIdx := 0, ops := #[] }
  let body := f.body.compile f.output layoutMap bindings |>.run' state
  let (_, layoutMState) := Bytecode.blockLayout body |>.run $ .new inputSize
  (body, layoutMState)

def TypedDecls.compile (decls : TypedDecls) : Bytecode.Toplevel :=
  let layout := decls.layoutMap
  let initMemSizes : Bytecode.MemSizes := .empty
  let (functions, memSizes) := decls.foldl (init := (#[], initMemSizes))
    fun acc@(functions, memSizes) (_, decl) => match decl with
      | .function function =>
        let (body, layoutMState) := function.compile layout
        let function := ⟨body, layoutMState.functionLayout⟩
        let memSizes := layoutMState.memSizes.fold (·.insert ·) memSizes
        (functions.push function, memSizes)
      | _ => acc
  ⟨functions, memSizes.toArray⟩

end Aiur
