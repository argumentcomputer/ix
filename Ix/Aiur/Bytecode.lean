import Std.Data.HashMap
import Ix.Aiur.Term

open Std

abbrev Name := Aiur.Global
abbrev ValIdx := Nat
abbrev SelIdx := Nat
abbrev FuncIdx := UInt64
abbrev MemIdx := Nat

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
    returnIdents : List SelIdx
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
  deriving Repr

structure LayoutBranchState where
  u1AuxiliariesInit : Nat
  u1AuxiliariesMax  : Nat
  u8AuxiliariesInit : Nat
  u8AuxiliariesMax  : Nat
  u64AuxiliariesInit : Nat
  u64AuxiliariesMax  : Nat
  sharedConstraintsInit : Nat
  sharedConstraintsMax  : Nat

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

namespace LayoutBranchState

def save : LayoutM LayoutBranchState := do
  let stt ← get
  pure {
    u1AuxiliariesInit := stt.layout.u1Auxiliaries
    u1AuxiliariesMax := stt.layout.u1Auxiliaries
    u8AuxiliariesInit := stt.layout.u8Auxiliaries
    u8AuxiliariesMax := stt.layout.u8Auxiliaries
    u64AuxiliariesInit := stt.layout.u64Auxiliaries
    u64AuxiliariesMax := stt.layout.u64Auxiliaries
    sharedConstraintsInit := stt.layout.sharedConstraints
    sharedConstraintsMax := stt.layout.sharedConstraints }

def merge (lbs : LayoutBranchState) : LayoutM LayoutBranchState := do
  let stt ← get
  let lbs' := { lbs with
    u1AuxiliariesMax := lbs.u1AuxiliariesMax.max stt.layout.u1Auxiliaries
    u8AuxiliariesMax := lbs.u8AuxiliariesMax.max stt.layout.u8Auxiliaries
    u64AuxiliariesMax := lbs.u64AuxiliariesMax.max stt.layout.u64Auxiliaries
    sharedConstraintsMax := lbs.sharedConstraintsMax.max stt.layout.sharedConstraints }
  let layout := { stt.layout with
    u1Auxiliaries := lbs.u1AuxiliariesInit
    u8Auxiliaries := lbs.u8AuxiliariesInit
    u64Auxiliaries := lbs.u64AuxiliariesInit
    sharedConstraints := lbs.sharedConstraintsInit }
  set { stt with layout }
  pure lbs'

def finish (lbs : LayoutBranchState) : LayoutM Unit := do
  modify fun stt => { stt with layout := { stt.layout with
    u1Auxiliaries := lbs.u1AuxiliariesMax.max stt.layout.u1Auxiliaries
    u8Auxiliaries := lbs.u8AuxiliariesMax.max stt.layout.u8Auxiliaries
    u64Auxiliaries := lbs.u64AuxiliariesMax.max stt.layout.u64Auxiliaries
    sharedConstraints := lbs.sharedConstraintsMax.max stt.layout.sharedConstraints } }

end LayoutBranchState

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
  | _ => panic! "TODO"

partial def blockLayout (block : Bytecode.Block) : LayoutM Unit := do
  block.ops.forM opLayout
  match block.ctrl with
  | .if _ tt ff =>
    let lbs ← LayoutBranchState.save
    -- This auxiliary is for proving inequality
    bumpU64Auxiliaries 1
    blockLayout tt
    let lbs ← lbs.merge
    blockLayout ff
    lbs.finish
  | .match _ branches defaultBranch =>
    let lbs ← branches.foldlM (init := ← LayoutBranchState.save) fun lbs (_, block) => do
      blockLayout block
      lbs.merge
    if let some defaultBlock := defaultBranch then
      blockLayout defaultBlock
    lbs.finish
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
  index: UInt64
  inputSize : Nat
  outputSize : Nat
  offsets: Array Nat
  deriving Repr, Inhabited

structure ConstructorLayout where
  index: UInt64
  size: Nat
  offsets: Array Nat
  deriving Repr, Inhabited

inductive Layout
  | dataType : DataTypeLayout → Layout
  | function : FunctionLayout → Layout
  | constructor : ConstructorLayout → Layout
  deriving Repr, Inhabited

abbrev LayoutMap := HashMap Global Layout

structure Toplevel where
  functions : Array Function
  memWidths : Array Nat
  layouts : Array Circuit.Layout
  deriving Repr, Inhabited

end Aiur.Bytecode

namespace Aiur

structure CompilerState where
  index : ValIdx
  ops : Array Bytecode.Op
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
      pushOp (Bytecode.Op.prim (Primitive.u64 layout.index))
    | .constructor layout => do
      let size := layout.size
      let index ← pushOp (Bytecode.Op.prim (Primitive.u64 layout.index))
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
        let index ← pushOp (Bytecode.Op.prim (Primitive.u64 layout.index))
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
      let index ← pushOp (Bytecode.Op.prim (Primitive.u64 layout.index))
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
  | .get arg i => do
    let typs := (match arg.typ with
      | .evaluates (.tuple typs) => typs
      | _ => panic! "should not happen after typechecking")
    let offset := (typs.extract 0 i).foldl (init := 0) (fun acc typ => typSize layoutMap typ + acc)
    pure $ Array.range' offset (typSize layoutMap typ)
  | .slice arg i j => do
    let typs := (match arg.typ with
      | .evaluates (.tuple typs) => typs
      | _ => panic! "should not happen after typechecking")
    let offset := (typs.extract 0 i).foldl (init := 0) (fun acc typ => typSize layoutMap typ + acc)
    let length := (typs.extract i j).foldl (init := 0) (fun acc typ => typSize layoutMap typ + acc)
    pure $ Array.range' offset length
  | .store arg => do
    let arg ← toIndex layoutMap bindings arg
    pushOp (Bytecode.Op.store arg)
  | .load ptr => do
    let size := match ptr.typ.unwrap with
    | .pointer typ => typSize layoutMap typ
    | _ => panic! "unreachable"
    dbg_trace s!"size {size}"
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
      let append arg acc := do
        pure (acc.append (← toIndex layoutMap bindings arg))
      args.foldrM (init := init) append

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
      let (cases, default) ← cases.foldlM (init := ([], .none)) (addCase layoutMap bindings returnTyp idxs)
      let ctrl := .match (idxs.get' 0) cases default
      -- TODO Fix the selector indices
      pure { ops, ctrl, returnIdents := [] }
  | .if b t f => do
    let b ← toIndex layoutMap bindings b
    assert! (b.size == 1)
    let ops ← extractOps
    let initState ← get
    let t ← t.compile returnTyp layoutMap bindings
    set initState
    let f ← f.compile returnTyp layoutMap bindings
    -- TODO Fix the selector indices
    pure { ops, ctrl := .if (b.get' 0) t f, returnIdents := [] }
  | .ret term => do
    let idxs ← toIndex layoutMap bindings term
    let state ← get
    -- TODO Fix the selector indices
    pure { ops := state.ops, ctrl := .ret 0 idxs, returnIdents := [] }
  | _ => do
    let idxs ← toIndex layoutMap bindings term
    let state ← get
    -- TODO Fix the selector indices
    pure { ops := state.ops, ctrl := .ret 0 idxs, returnIdents := [] }

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
    set initState
    let cases' := cases.cons (prim.toU64, term)
    pure (cases', default)
  | .ref global pats => do
    let layout := layoutMap.get' global
    let (index, offsets) := match layout with
    | .function layout => (layout.index, layout.offsets)
    | .constructor layout => (layout.index, layout.offsets)
    | .dataType _ => panic! "impossible after typechecking"
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
    set initState
    let cases' := cases.cons (index, term)
    pure (cases', default)
  | .wildcard => do
    let initState ← get
    let term ← term.compile returnTyp layoutMap bindings
    set initState
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
  let state := { index, ops := #[] }
  let body :=  (f.body.compile f.output layoutMap bindings).run' state
  { name := f.name, inputSize, outputSize, body }

def TypedDecls.dataTypeLayouts (decls : TypedDecls) : Bytecode.LayoutMap :=
  let pass := fun (acc, funcIndex) (_, v) => match v with
  | .dataType dataType =>
    let dataTypeSize := dataType.size decls
    let acc := acc.insert dataType.name (.dataType { size := dataTypeSize })
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
    let (layout, _) := dataType.constructors.foldl (init := (acc, 0)) pass
    (layout, funcIndex)
  | .function function =>
    let inputSize := function.inputs.foldl (init := 0) (fun acc (_, typ) => acc + typ.size decls)
    let outputSize := function.output.size decls
    let offsets :=
      function.inputs.foldl (init := #[0])
        (fun offsets (_, typ) => offsets.push (offsets[offsets.size - 1]! + typ.size decls))
    let layout := acc.insert function.name (.function { index := funcIndex, inputSize, outputSize, offsets })
    (layout, funcIndex + 1)
  | .constructor .. => (acc, funcIndex)
  let (layout, _) := decls.foldl (init := ({}, 0)) pass
  layout

def TypedDecls.compile (decls : TypedDecls) : Bytecode.Toplevel :=
  let layout := decls.dataTypeLayouts
  let (functions, memWidths, layouts) := decls.foldl (init := (#[], #[], #[]))
    fun acc@(functions, memWidths, layouts) (_, decl) => match decl with
      | .function function =>
        let compiledFunction := function.compile layout
        let layoutMState := Circuit.functionLayout compiledFunction
        let memWidths := layoutMState.memWidths.foldl (init := memWidths) fun memWidths memWidth =>
          if memWidths.contains memWidth then memWidths else memWidths.push memWidth
        (functions.push compiledFunction, memWidths, layouts.push layoutMState.layout)
      | _ => acc
  ⟨functions, memWidths.qsort, layouts⟩

end Aiur
