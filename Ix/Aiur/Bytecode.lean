import Std.Data.HashMap
import Ix.Aiur.Term
import Ix.Aiur.Gadget

open Std

abbrev Name := Aiur.Global
abbrev ValIdx := Nat
abbrev SelIdx := Nat
abbrev FuncIdx := Nat
abbrev MemIdx := Nat
abbrev GadgetIdx := Nat

def Std.HashMap.get' [Inhabited β] [BEq α] [Hashable α] [Repr α] (m : HashMap α β) (a : α) : β :=
  match m.get? a with
  | .some b => b
  | .none => panic! s!"could not find key `{(repr a).pretty}`"

def List.get' [Inhabited A] (as : List A) (n : Nat) : A :=
  match as[n]? with
  | .some a => a
  | .none => panic! s!"index {n} out of bounds {as.length}"

def Array.get' [Inhabited A] (as : Array A) (n : Nat) : A :=
  match as[n]? with
  | .some a => a
  | .none => panic! s!"index {n} out of bounds {as.size}"

namespace Aiur.Bytecode

inductive Op where
  | prim : Primitive → Op
  | add : ValIdx → ValIdx → Op
  | sub : ValIdx → ValIdx → Op
  | mul : ValIdx → ValIdx → Op
  | xor : ValIdx → ValIdx → Op
  | and : ValIdx → ValIdx → Op
  | lt: ValIdx → ValIdx → Op
  | store : Array ValIdx → Op
  | load : MemIdx → ValIdx → Op
  | call : FuncIdx → Array ValIdx → Nat → Op
  | dynCall : ValIdx → Array ValIdx → ValIdx → Op
  | preimg : FuncIdx → Array ValIdx → ValIdx → Op
  | dynPreimg : ValIdx → Array ValIdx → ValIdx → Op
  | ffi : GadgetIdx → Array ValIdx → Nat → Op
  | trace : String → Array ValIdx → Op
  deriving Repr, Inhabited

mutual
  inductive Ctrl where
    | if : ValIdx → Block → Block → Ctrl
    | match : ValIdx → List (UInt64 × Block) -> Option Block → Ctrl
    | ret : SelIdx → Array ValIdx → Ctrl
    deriving Repr, Inhabited

  structure Block where
    ops : Array Op
    ctrl : Ctrl
    returnIdents : SelIdx × SelIdx
    deriving Repr, Inhabited
end

structure Function where
  name : Name
  inputSize : Nat
  outputSize : Nat
  body : Block
  deriving Repr, Inhabited

end Bytecode

namespace Circuit

/--
The circuit layout of a function.

`selectors` are bit values that identify which path the computation
took. Exactly one selector must be set.

`u*Auxiliaries` represent registers that hold temporary values
and can be shared by different circuit paths, since they never
overlap.

`sharedConstraints` are constraint slots that can be shared in
different paths of the circuit.
-/
structure Layout where
  inputs : Nat
  outputs : Nat
  selectors : Nat
  u1Auxiliaries : Nat
  u8Auxiliaries : Nat
  u64Auxiliaries : Nat
  sharedConstraints : Nat
  deriving Repr, Inhabited

structure SharedData where
  u1Auxiliaries : Nat
  u8Auxiliaries : Nat
  u64Auxiliaries : Nat
  constraints : Nat

def SharedData.maximals (a b : SharedData) : SharedData := {
  u1Auxiliaries := a.u1Auxiliaries.max b.u1Auxiliaries
  u8Auxiliaries := a.u8Auxiliaries.max b.u8Auxiliaries
  u64Auxiliaries := a.u64Auxiliaries.max b.u64Auxiliaries
  constraints := a.constraints.max b.constraints
}

@[inline] def Layout.init (inputs outputs : Nat) : Layout :=
  ⟨inputs, outputs, 0, 0, 0, 0, 0⟩

structure LayoutMState where
  layout : Layout
  memWidths : Array Nat

abbrev LayoutM := StateM LayoutMState

@[inline] def bumpSelectors : LayoutM Unit :=
  modify fun stt => { stt with
    layout := { stt.layout with selectors := stt.layout.selectors + 1 } }

@[inline] def bumpSharedConstraints (n : Nat) : LayoutM Unit :=
  modify fun stt => { stt with
    layout := { stt.layout with sharedConstraints := stt.layout.sharedConstraints + n } }

@[inline] def bumpU1Auxiliaries : LayoutM Unit :=
  modify fun stt => { stt with
    layout := { stt.layout with u1Auxiliaries := stt.layout.u1Auxiliaries + 1 } }

@[inline] def bumpU64Auxiliaries (n : Nat) : LayoutM Unit :=
  modify fun stt => { stt with
    layout := { stt.layout with u64Auxiliaries := stt.layout.u64Auxiliaries + n } }

@[inline] def addMemWidth (memWidth : Nat) : LayoutM Unit :=
  modify fun stt =>
    let memWidths := if stt.memWidths.contains memWidth
      then stt.memWidths
      else stt.memWidths.push memWidth
    { stt with memWidths }

def getSharedData : LayoutM SharedData := do
  let stt ← get
  pure {
    u1Auxiliaries := stt.layout.u1Auxiliaries
    u8Auxiliaries := stt.layout.u8Auxiliaries
    u64Auxiliaries := stt.layout.u64Auxiliaries
    constraints := stt.layout.sharedConstraints
  }

def setSharedData (sharedData : SharedData) : LayoutM Unit :=
  modify fun stt => { stt with layout := { stt.layout with
    u1Auxiliaries := sharedData.u1Auxiliaries
    u8Auxiliaries := sharedData.u8Auxiliaries
    u64Auxiliaries := sharedData.u64Auxiliaries
    sharedConstraints := sharedData.constraints } }

def opLayout : Bytecode.Op → LayoutM Unit
  | .prim _ | .xor .. => pure ()
  | .and .. => do
    -- `and` is achieved by multiplication. Since we do not want
    -- expressions of order greater than 1, we create a new auxiliary
    -- and constrain it to be equal to the product of the two expressions
    bumpSharedConstraints 1
    bumpU1Auxiliaries
  | .add .. | .lt .. | .sub .. => do
    -- Uses the addition gadget which outputs 8 bytes of sum
    -- plus 1 byte of carry
    bumpU64Auxiliaries 1
    bumpU1Auxiliaries
  | .mul .. => do
    -- Uses the multiplication gadget which outputs 8 bytes
    bumpU64Auxiliaries 1
  | .store values => do
    addMemWidth values.size
    -- Outputs a pointer and a require hint
    bumpU64Auxiliaries 2
  | .load len _ => do
    addMemWidth len
    -- Outputs the loaded values and a require hint
    bumpU64Auxiliaries (len + 1)
  | .call _ _ outSize =>
    -- Outputs the call values and a require hint
    bumpU64Auxiliaries (outSize + 1)
  | .ffi _ _ outSize =>
    -- Outputs the ffi values and a require hint
    bumpU64Auxiliaries (outSize + 1)
  | _ => panic! "TODO"

partial def blockLayout (block : Bytecode.Block) : LayoutM Unit := do
  block.ops.forM opLayout
  match block.ctrl with
  | .if _ tt ff =>
    let initSharedData ← getSharedData
    -- This auxiliary is for proving inequality
    bumpU64Auxiliaries 1
    blockLayout tt
    let ttSharedData ← getSharedData
    setSharedData initSharedData
    blockLayout ff
    let ffSharedData ← getSharedData
    setSharedData $ ttSharedData.maximals ffSharedData
  | .match _ branches defaultBranch =>
    let initSharedData ← getSharedData
    let mut maximalSharedData := initSharedData
    for (_, block) in branches do
      setSharedData initSharedData
      -- This auxiliary is for proving inequality
      bumpU64Auxiliaries 1
      blockLayout block
      let blockSharedData ← getSharedData
      maximalSharedData := maximalSharedData.maximals blockSharedData
    if let some defaultBlock := defaultBranch then
      setSharedData initSharedData
      blockLayout defaultBlock
      let defaultBlockSharedData ← getSharedData
      maximalSharedData := maximalSharedData.maximals defaultBlockSharedData
    setSharedData maximalSharedData
  | .ret _ out =>
    -- One selector per return
    bumpSelectors
    -- Each output must equal its respective return variable,
    -- thus one constraint per return variable
    bumpSharedConstraints out.size

def functionLayout (function : Bytecode.Function) : LayoutMState :=
  let initLayout :=  (Layout.init function.inputSize function.outputSize)
  let (_, stt) := blockLayout function.body |>.run ⟨initLayout, #[]⟩
  stt

end Circuit

namespace Bytecode

structure DataTypeLayout where
  size: Nat
  deriving Repr, Inhabited

structure FunctionLayout where
  index: Nat
  inputSize : Nat
  outputSize : Nat
  offsets: Array Nat
  deriving Repr, Inhabited

structure ConstructorLayout where
  index: Nat
  size: Nat
  offsets: Array Nat
  deriving Repr, Inhabited

structure GadgetLayout where
  index : Nat
  outputSize : Nat
  deriving Repr, Inhabited

inductive Layout
  | dataType : DataTypeLayout → Layout
  | function : FunctionLayout → Layout
  | constructor : ConstructorLayout → Layout
  | gadget : GadgetLayout → Layout
  deriving Repr, Inhabited

abbrev LayoutMap := HashMap Global Layout

structure Toplevel where
  functions : Array Function
  memWidths : Array Nat
  layouts : Array Circuit.Layout
  gadgets : Array Gadget
  deriving Repr, Inhabited

end Aiur.Bytecode

namespace Aiur

structure CompilerState where
  index : ValIdx
  ops : Array Bytecode.Op
  returnIdent : SelIdx
  deriving Repr, Inhabited

def pushOp (op : Bytecode.Op) (size : Nat := 1) : StateM CompilerState (Array ValIdx) :=
  modifyGet (fun s =>
    let index := s.index
    let ops := s.ops
    (Array.range' index size, { s with index := index + size, ops := ops.push op}))

def extractOps : StateM CompilerState (Array Bytecode.Op) :=
  modifyGet (fun s => (s.ops, {s with ops := #[]}))

def typSize (layoutMap : Bytecode.LayoutMap) : Typ → Nat
| Typ.primitive .. => 1
| Typ.pointer .. => 1
| Typ.function .. => 1
| Typ.tuple ts => ts.foldl (init := 0) (fun acc t => acc + typSize layoutMap t)
| Typ.dataType g => match layoutMap.get' g with
  | .dataType layout => layout.size
  | _ => unreachable!

partial def toIndex
 (layoutMap : Bytecode.LayoutMap)
 (bindings : HashMap Local (Array ValIdx))
 (term : TypedTerm) : StateM CompilerState (Array ValIdx) :=
  let typ := term.typ.unwrap
  match term.inner with
  | .ret .. => panic! "should not happen after typechecking"
  | .match .. => panic! "non-tail `match` not yet implemented"
  | .if .. => panic! "non-tail `if` not yet implemented"
  | .var name => do
    pure (bindings.get' name)
  | .ref name => match layoutMap.get' name with
    | .function layout => do
      pushOp (Bytecode.Op.prim (Primitive.u64 layout.index.toUInt64))
    | .constructor layout => do
      let size := layout.size
      let index ← pushOp (Bytecode.Op.prim (Primitive.u64 layout.index.toUInt64))
      if index.size < size then
        let padding := (← pushOp (Bytecode.Op.prim (Primitive.u64 0)))[0]!
        pure $ index ++ Array.mkArray (size - index.size) padding
      else
        pure index
    | _ => panic! "should not happen after typechecking"
  | .data (.primitive p) => do
    pushOp (Bytecode.Op.prim p)
  | .data (.tuple args) =>
      -- TODO use `buildArgs`
      let append arg acc := do
        pure (acc.append (← toIndex layoutMap bindings arg))
      args.foldrM (init := #[]) append
  | .let (.var var) val bod => do
    let val ← toIndex layoutMap bindings val
    toIndex layoutMap (bindings.insert var val) bod
  | .let .. => panic! "should not happen after simplifying"
  | .xor a b => do
    let a ← toIndex layoutMap bindings a
    assert! (a.size == 1)
    let b ← toIndex layoutMap bindings b
    assert! (b.size == 1)
    pushOp (.xor (a.get' 0) (b.get' 0))
  | .addU64 a b => do
    let a ← toIndex layoutMap bindings a
    assert! (a.size == 1)
    let b ← toIndex layoutMap bindings b
    assert! (b.size == 1)
    pushOp (.add (a.get' 0) (b.get' 0))
  | .subU64 a b => do
    let a ← toIndex layoutMap bindings a
    assert! (a.size == 1)
    let b ← toIndex layoutMap bindings b
    assert! (b.size == 1)
    pushOp (.sub (a.get' 0) (b.get' 0))
  | .mulU64 a b => do
    let a ← toIndex layoutMap bindings a
    assert! (a.size == 1)
    let b ← toIndex layoutMap bindings b
    assert! (b.size == 1)
    pushOp (.mul (a.get' 0) (b.get' 0))
  | .and a b => do
    let a ← toIndex layoutMap bindings a
    assert! (a.size == 1)
    let b ← toIndex layoutMap bindings b
    assert! (b.size == 1)
    pushOp (.and (a.get' 0) (b.get' 0))
  | .app name@(⟨.str .anonymous unqualifiedName⟩) args =>
    match bindings.get? (.str unqualifiedName) with
    | some _ => panic! "dynamic calls not yet implemented"
    | none => match layoutMap.get' name with
      | .function layout => do
        let args ← buildArgs args
        pushOp (Bytecode.Op.call layout.index args layout.outputSize) layout.outputSize
      | .constructor layout => do
        let size := layout.size
        let index ← pushOp (Bytecode.Op.prim (Primitive.u64 layout.index.toUInt64))
        let index ← buildArgs args index
        if index.size < size then
          let padding := (← pushOp (Bytecode.Op.prim (Primitive.u64 0)))[0]!
          pure $ index ++ Array.mkArray (size - index.size) padding
        else
          pure index
      | _ => panic! "should not happen after typechecking"
  | .app name args => match layoutMap.get' name with
    | .function layout => do
      let args ← buildArgs args
      pushOp (Bytecode.Op.call layout.index args layout.outputSize) layout.outputSize
    | .constructor layout => do
      let size := layout.size
      let index ← pushOp (Bytecode.Op.prim (Primitive.u64 layout.index.toUInt64))
      let index ← buildArgs args index
      if index.size < size then
        let padding := (← pushOp (Bytecode.Op.prim (Primitive.u64 0)))[0]!
        pure $ index ++ Array.mkArray (size - index.size) padding
      else
        pure index
    | _ => panic! "should not happen after typechecking"
  | .preimg name@(⟨.str .anonymous unqualifiedName⟩) out =>
    match bindings.get? (.str unqualifiedName) with
    | some _ => panic! "dynamic preimage not yet implemented"
    | none => match layoutMap.get' name with
      | .function layout => do
        let out ← toIndex layoutMap bindings out
        pushOp (Bytecode.Op.preimg layout.index out layout.inputSize) layout.inputSize
      | _ => panic! "should not happen after typechecking"
  | .preimg name out => match layoutMap.get' name with
    | .function layout => do
      let out ← toIndex layoutMap bindings out
      pushOp (Bytecode.Op.preimg layout.index out layout.inputSize) layout.inputSize
    | _ => panic! "should not happen after typechecking"
  | .ffi name args => match layoutMap.get' name with
    | .gadget layout => do
      let args ← buildArgs args
      pushOp (Bytecode.Op.ffi layout.index args layout.outputSize) layout.outputSize
    | _ => panic! "should not happen after typechecking"
  | .get arg i =>
    let typs := (match arg.typ with
      | .evaluates (.tuple typs) => typs
      | _ => panic! "should not happen after typechecking")
    let offset := (typs.extract 0 i).foldl (init := 0)
      fun acc typ => typSize layoutMap typ + acc
    pure $ Array.range' offset (typSize layoutMap typ)
  | .slice arg i j =>
    let typs := (match arg.typ with
      | .evaluates (.tuple typs) => typs
      | _ => panic! "should not happen after typechecking")
    let offset := (typs.extract 0 i).foldl (init := 0)
      fun acc typ => typSize layoutMap typ + acc
    let length := (typs.extract i j).foldl (init := 0)
      fun acc typ => typSize layoutMap typ + acc
    pure $ Array.range' offset length
  | .store arg => do
    let arg ← toIndex layoutMap bindings arg
    pushOp (Bytecode.Op.store arg)
  | .load ptr => do
    let size := match ptr.typ.unwrap with
    | .pointer typ => typSize layoutMap typ
    | _ => unreachable!
    let ptr ← toIndex layoutMap bindings ptr
    assert! (ptr.size == 1)
    pushOp (Bytecode.Op.load size (ptr.get' 0)) size
  | .pointerAsU64 ptr => toIndex layoutMap bindings ptr
  | .trace str expr => do
    let arr ← toIndex layoutMap bindings expr
    let op := .trace str arr
    modify (fun state => { state with ops := state.ops.push op})
    pure arr
  where
    buildArgs (args : List TypedTerm) (init : Array ValIdx := #[]) : StateM CompilerState (Array ValIdx) :=
      let append acc arg := do
        pure (acc.append (← toIndex layoutMap bindings arg))
      args.foldlM (init := init) append

mutual

partial def TypedTerm.compile
 (term : TypedTerm)
 (returnTyp : Typ)
 (layoutMap : Bytecode.LayoutMap)
 (bindings : HashMap Local (Array ValIdx))
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
            let pat := (pats.get' i)
            let typ := (typs.get' i)
            match pat with
            | .var var =>
              let len := typSize layoutMap typ
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
      let initIdent := (← get).returnIdent
      let (cases, default) ← cases.foldlM (init := ([], .none)) (addCase layoutMap bindings returnTyp idxs)
      let lastIdent := (← get).returnIdent
      let ctrl := .match (idxs.get' 0) cases.reverse default
      pure { ops, ctrl, returnIdents := (initIdent, lastIdent) }
  | .if b t f => do
    let b ← toIndex layoutMap bindings b
    assert! (b.size == 1)
    let ops ← extractOps
    let initState ← get
    let initIdent := initState.returnIdent
    let t ← t.compile returnTyp layoutMap bindings
    set { initState with returnIdent := (← get).returnIdent }
    let f ← f.compile returnTyp layoutMap bindings
    let lastIdent := (← get).returnIdent
    pure { ops, ctrl := .if (b.get' 0) t f, returnIdents := (initIdent, lastIdent) }
  | .ret term => do
    let idxs ← toIndex layoutMap bindings term
    let state ← get
    let state := { state with returnIdent := state.returnIdent + 1 }
    set state
    let ops := state.ops
    let id := state.returnIdent
    pure { ops, ctrl := .ret (id - 1) idxs, returnIdents := (id - 1, id) }
  | _ => do
    let idxs ← toIndex layoutMap bindings term
    let state ← get
    let state := { state with returnIdent := state.returnIdent + 1 }
    set state
    let ops := state.ops
    let id := state.returnIdent
    pure { ops, ctrl := .ret (id - 1) idxs, returnIdents := (id - 1, id) }

partial def addCase
  (layoutMap : Bytecode.LayoutMap)
  (bindings : HashMap Local (Array ValIdx))
  (returnTyp : Typ)
  (idxs : Array ValIdx)
: (List (UInt64 × Bytecode.Block) × Option Bytecode.Block) →
  (Pattern × TypedTerm) →
  StateM CompilerState (List (UInt64 × Bytecode.Block) × Option Bytecode.Block) := fun (cases, default) (pat, term) =>
  -- If simplified, only one default will exist, and it will appear at the end of the match
  assert! default.isNone
  match pat with
  | .primitive prim => do
    let initState ← get
    let term ← term.compile returnTyp layoutMap bindings
    set { initState with returnIdent := (← get).returnIdent }
    let cases' := cases.cons (prim.toU64, term)
    pure (cases', default)
  | .ref global pats => do
    let layout := layoutMap.get' global
    let (index, offsets) := match layout with
    | .function layout => (layout.index, layout.offsets)
    | .constructor layout => (layout.index, layout.offsets)
    | .dataType _
    | .gadget _ => panic! "impossible after typechecking"
    let bindArgs bindings pats offsets idxs :=
      let n := pats.length
      let bindings := (List.range n).foldl (init := bindings) fun bindings i =>
        let pat := (pats.get' i)
        -- the `+ 1` is to account for the tag
        let offset := (offsets.get' i) + 1
        let next_offset := (offsets.get' (i + 1)) + 1
        match pat with
        | .var var =>
          bindings.insert var (idxs.extract offset next_offset)
        | _ => panic! "should not happen after simplification"
      bindings
    let bindings := bindArgs bindings pats offsets idxs
    let initState ← get
    let term ← term.compile returnTyp layoutMap bindings
    set { initState with returnIdent := (← get).returnIdent }
    let cases' := cases.cons (index.toUInt64, term)
    pure (cases', default)
  | .wildcard => do
    let initState ← get
    let term ← term.compile returnTyp layoutMap bindings
    set { initState with returnIdent := (← get).returnIdent }
    pure (cases, .some term)
  | _ => unreachable!

end

def TypedFunction.compile (layoutMap : Bytecode.LayoutMap) (f : TypedFunction) : Bytecode.Function :=
  let (inputSize, outputSize) := match layoutMap.get' f.name with
  | .function layout => (layout.inputSize, layout.outputSize)
  | _ => panic! s!"`{f.name}` should be a function"
  let (index, bindings) := f.inputs.foldl (init := (0, default))
    (fun (index, bindings) (arg, typ) =>
      let len := typSize layoutMap typ
      let indices := Array.range' index len
      (index + len, bindings.insert arg indices))
  let state := { index, returnIdent := 0, ops := #[] }
  let body :=  (f.body.compile f.output layoutMap bindings).run' state
  { name := f.name, inputSize, outputSize, body }

def TypedDecls.dataTypeLayouts (decls : TypedDecls) : Bytecode.LayoutMap :=
  let pass := fun (layoutMap, funcIdx, gadgetIdx) (_, v) => match v with
    | .dataType dataType =>
      let dataTypeSize := dataType.size decls
      let layoutMap := layoutMap.insert dataType.name (.dataType { size := dataTypeSize })
      let pass := fun (acc, index) constructor =>
        let offsets :=
          constructor.argTypes.foldl (init := #[0])
            (fun offsets typ => offsets.push (offsets[offsets.size - 1]! + typ.size decls))
        let decl := .constructor {
          size := dataTypeSize,
          offsets,
          index,
        }
        let name := dataType.name.pushNamespace constructor.nameHead
        (acc.insert name decl, index + 1)
      let (layoutMap, _) := dataType.constructors.foldl (init := (layoutMap, 0)) pass
      (layoutMap, funcIdx, gadgetIdx)
    | .function function =>
      let inputSize := function.inputs.foldl (init := 0) (fun acc (_, typ) => acc + typ.size decls)
      let outputSize := function.output.size decls
      let offsets :=
        function.inputs.foldl (init := #[0])
          (fun offsets (_, typ) => offsets.push (offsets[offsets.size - 1]! + typ.size decls))
      let layoutMap := layoutMap.insert function.name (.function { index := funcIdx, inputSize, outputSize, offsets })
      (layoutMap, funcIdx + 1, gadgetIdx)
    | .constructor .. => (layoutMap, funcIdx, gadgetIdx)
    | .gadget g =>
      let layoutMap := layoutMap.insert ⟨g.name⟩ (.gadget ⟨gadgetIdx, g.outputSize⟩)
      (layoutMap, funcIdx, gadgetIdx + 1)
  let (layoutMap, _) := decls.foldl pass ({}, 0, 0)
  layoutMap

def TypedDecls.compile (decls : TypedDecls) : Bytecode.Toplevel :=
  let layout := decls.dataTypeLayouts
  let (functions, memWidths, layouts, gadgets) := decls.foldl (init := (#[], #[], #[], #[]))
    fun acc@(functions, memWidths, layouts, gadgets) (_, decl) => match decl with
      | .function function =>
        let compiledFunction := function.compile layout
        let layoutMState := Circuit.functionLayout compiledFunction
        let memWidths := layoutMState.memWidths.foldl (init := memWidths) fun memWidths memWidth =>
          if memWidths.contains memWidth then memWidths else memWidths.push memWidth
        (functions.push compiledFunction, memWidths, layouts.push layoutMState.layout, gadgets)
      | .gadget gadget => (functions, memWidths, layouts, gadgets.push gadget)
      | _ => acc
  ⟨functions, memWidths.qsort, layouts, gadgets⟩

end Aiur
