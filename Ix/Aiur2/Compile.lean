import Std.Data.HashMap
import Lean.Data.RBTree
import Ix.Aiur2.Term
import Ix.Aiur2.Bytecode

namespace Aiur

namespace Bytecode

structure SharedData where
  auxiliaries : Nat
  lookups : Nat

def SharedData.maximals (a b : SharedData) : SharedData := {
  auxiliaries := a.auxiliaries.max b.auxiliaries
  lookups := a.lookups.max b.lookups
}

abbrev MemWidths := Lean.RBTree Nat compare

structure LayoutMState where
  functionLayout : FunctionLayout
  memWidths : MemWidths
  degrees : Array Nat

/-- A new `LayoutMState` starts with one auxiliar for the multiplicity. -/
@[inline] def LayoutMState.new (inputSize outputSize : Nat) : LayoutMState :=
  ⟨{ inputSize, outputSize, selectors := 0, auxiliaries := 1, lookups := 0 }, .empty, #[]⟩

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

@[inline] def addMemWidth (memWidth : Nat) : LayoutM Unit :=
  modify fun stt => { stt with memWidths := stt.memWidths.insert memWidth }

@[inline] def pushDegree (degree : Nat) : LayoutM Unit :=
  modify fun stt => { stt with degrees := stt.degrees.push degree }

@[inline] def pushDegrees (degrees : Array Nat) : LayoutM Unit :=
  modify fun stt => { stt with degrees := stt.degrees ++ degrees }

@[inline] def getDegree (v : ValIdx) : LayoutM Nat :=
  get >>= fun stt => pure stt.degrees[v]!

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
  | .call _ _ outputSize => do
    pushDegrees $ .mkArray outputSize 1
    bumpAuxiliaries outputSize
    bumpLookups
  | .store values => do
    pushDegree 1
    bumpAuxiliaries 1
    bumpLookups
    addMemWidth values.size
  | .load width _ => do
    pushDegrees $ .mkArray width 1
    bumpAuxiliaries width
    bumpLookups
    addMemWidth width

partial def blockLayout (block : Bytecode.Block) : LayoutM Unit := do
  block.ops.forM opLayout
  match block.ctrl with
  | .match _ branches defaultBranch =>
    let initSharedData ← getSharedData
    let mut maximalSharedData := initSharedData
    for (_, block) in branches do
      setSharedData initSharedData
      -- An auxiliary for proving inequality
      bumpAuxiliaries 1
      blockLayout block
      let blockSharedData ← getSharedData
      maximalSharedData := maximalSharedData.maximals blockSharedData
    if let some defaultBlock := defaultBranch then
      setSharedData initSharedData
      blockLayout defaultBlock
      let defaultBlockSharedData ← getSharedData
      maximalSharedData := maximalSharedData.maximals defaultBlockSharedData
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
| Typ.field .. => 1
| Typ.pointer .. => 1
| Typ.function .. => 1
| Typ.tuple ts => ts.foldl (init := 0) (fun acc t => acc + typSize layoutMap t)
| Typ.dataType g => match layoutMap[g]? with
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
  let typ := term.typ.unwrap
  match term.inner with
  | .ret .. => panic! "should not happen after typechecking"
  | .match .. => panic! "non-tail `match` not yet implemented"
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
        pure $ index ++ Array.mkArray (size - index.size) padding
      else
        pure index
    | _ => panic! "should not happen after typechecking"
  | .data (.field g) => pushOp (Bytecode.Op.const g)
  | .data (.tuple args) =>
      -- TODO use `buildArgs`
      let append arg acc := do
        pure (acc.append (← toIndex layoutMap bindings arg))
      args.foldrM (init := #[]) append
  | .let (.var var) val bod => do
    let val ← toIndex layoutMap bindings val
    toIndex layoutMap (bindings.insert var val) bod
  | .let .. => panic! "should not happen after simplifying"
  | .add a b => do
    let a ← toIndex layoutMap bindings a
    assert! (a.size == 1)
    let b ← toIndex layoutMap bindings b
    assert! (b.size == 1)
    pushOp (.add (a[0]!) (b[0]!))
  | .sub a b => do
    let a ← toIndex layoutMap bindings a
    assert! (a.size == 1)
    let b ← toIndex layoutMap bindings b
    assert! (b.size == 1)
    pushOp (.sub (a[0]!) (b[0]!))
  | .mul a b => do
    let a ← toIndex layoutMap bindings a
    assert! (a.size == 1)
    let b ← toIndex layoutMap bindings b
    assert! (b.size == 1)
    pushOp (.mul (a[0]!) (b[0]!))
  | .app name@(⟨.str .anonymous unqualifiedName⟩) args =>
    match bindings.get? (.str unqualifiedName) with
    | some _ => panic! "dynamic calls not yet implemented"
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
          pure $ index ++ Array.mkArray (size - index.size) padding
        else
          pure index
      | _ => panic! "should not happen after typechecking"
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
        pure $ index ++ Array.mkArray (size - index.size) padding
      else
        pure index
    | _ => panic! "should not happen after typechecking"
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
  -- | .ffi name args => match layoutMap.get' name with
  --   | .gadget layout => do
  --     let args ← buildArgs args
  --     pushOp (Bytecode.Op.ffi layout.index args layout.outputSize) layout.outputSize
  --   | _ => panic! "should not happen after typechecking"
  | .get arg i => do
    let typs := (match arg.typ with
      | .evaluates (.tuple typs) => typs
      | _ => panic! "should not happen after typechecking")
    let offset := (typs.extract 0 i).foldl (init := 0)
      fun acc typ => typSize layoutMap typ + acc
    let arg ← toIndex layoutMap bindings arg
    let length := typSize layoutMap typ
    pure $ arg.extract offset (offset + length)
  | .slice arg i j => do
    let typs := (match arg.typ with
      | .evaluates (.tuple typs) => typs
      | _ => panic! "should not happen after typechecking")
    let offset := (typs.extract 0 i).foldl (init := 0)
      fun acc typ => typSize layoutMap typ + acc
    let length := (typs.extract i j).foldl (init := 0)
      fun acc typ => typSize layoutMap typ + acc
    let arg ← toIndex layoutMap bindings arg
    pure $ arg.extract offset (offset + length)
  | .store arg => do
    let args ← toIndex layoutMap bindings arg
    pushOp (Bytecode.Op.store args)
  | .load ptr => do
    let size := match ptr.typ.unwrap with
    | .pointer typ => typSize layoutMap typ
    | _ => unreachable!
    let ptr ← toIndex layoutMap bindings ptr
    assert! (ptr.size == 1)
    pushOp (Bytecode.Op.load size ptr[0]!) size
  | .ptrVal ptr => toIndex layoutMap bindings ptr
  -- | .trace str expr => do
  --   let arr ← toIndex layoutMap bindings expr
  --   let op := .trace str arr
  --   modify (fun state => { state with ops := state.ops.push op})
  --   pure arr
  where
    buildArgs (args : List TypedTerm) (init := #[]) :=
      let append acc arg := do
        pure (acc.append (← toIndex layoutMap bindings arg))
      args.foldlM (init := init) append

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
  | .let .. => panic! "should not happen after simplifying"
  | .match term cases =>
    match term.typ.unwrapOr returnTyp with
    -- Also do this for tuple-like (one constructor only) datatypes
    | .tuple typs => match cases with
      | [(.tuple vars, branch)] => do
        let bindArgs bindings pats typs idxs :=
          let n := pats.size
          let init := (bindings, 0)
          let (bindings, _) := (List.range n).foldl (init := init) fun (bindings, offset) i =>
            match pats[i]! with
            | .var var =>
              let len := typSize layoutMap typs[i]!
              let new_offset := offset + len
              (bindings.insert var (idxs.extract offset new_offset), new_offset)
            | _ => panic! "should not happen after simplification"
          bindings
        let idxs ← toIndex layoutMap bindings term
        let bindings := bindArgs bindings vars typs idxs
        branch.compile returnTyp layoutMap bindings
      | _ => unreachable!
    | _ => do
      let idxs ← toIndex layoutMap bindings term
      let ops ← extractOps
      let minSelIncluded := (← get).selIdx
      let (cases, default) ← cases.foldlM (init := default)
        (addCase layoutMap bindings returnTyp idxs)
      let maxSelExcluded := (← get).selIdx
      let ctrl := .match (idxs[0]!) cases default
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
    | .gadget _ => panic! "impossible after typechecking"
    let bindArgs bindings pats offsets idxs :=
      let n := pats.length
      let bindings := (List.range n).foldl (init := bindings) fun bindings i =>
        let pat := (pats[i]!)
        -- the `+ 1` is to account for the tag
        let offset := (offsets[i]!) + 1
        let next_offset := (offsets[(i + 1)]!) + 1
        match pat with
        | .var var =>
          bindings.insert var (idxs.extract offset next_offset)
        | _ => panic! "should not happen after simplification"
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
  let (inputSize, outputSize) := match layoutMap[f.name]? with
    | some (.function layout) => (layout.inputSize, layout.outputSize)
    | _ => panic! s!"`{f.name}` should be a function"
  let (valIdx, bindings) := f.inputs.foldl (init := (0, default))
    fun (valIdx, bindings) (arg, typ) =>
      let len := typSize layoutMap typ
      let indices := Array.range' valIdx len
      (valIdx + len, bindings.insert arg indices)
  let state := { valIdx, selIdx := 0, ops := #[] }
  let body := f.body.compile f.output layoutMap bindings |>.run' state
  let (_, layoutMState) := Bytecode.blockLayout body |>.run $ .new inputSize outputSize
  (body, layoutMState)

def TypedDecls.compile (decls : TypedDecls) : Bytecode.Toplevel :=
  let layout := decls.layoutMap
  let initMemWidths : Bytecode.MemWidths := .empty
  let (functions, memWidths) := decls.foldl (init := (#[], initMemWidths))
    fun acc@(functions, memWidths) (_, decl) => match decl with
      | .function function =>
        let (body, layoutMState) := function.compile layout
        let function := ⟨body, layoutMState.functionLayout⟩
        let memWidths := layoutMState.memWidths.fold (·.insert ·) memWidths
        (functions.push function, memWidths)
      | _ => acc
  ⟨functions, memWidths.toArray⟩

end Aiur
