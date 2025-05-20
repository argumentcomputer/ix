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
  deriving Repr, Inhabited

end Aiur.Bytecode

namespace Aiur

structure CompilerState where
  index : ValIdx
  ops : Array Bytecode.Op
  deriving Repr, Inhabited

def pushOp (op : Bytecode.Op) : StateM CompilerState ValIdx :=
  modifyGet (fun s =>
    let index := s.index
    let ops := s.ops
    (index, { s with index := index + 1, ops := ops.push op}))

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
      let index ← pushOp (Bytecode.Op.prim (Primitive.u64 layout.index))
      pure #[index]
    | .constructor layout => do
      let index ← pushOp (Bytecode.Op.prim (Primitive.u64 layout.index))
      pure #[index]
    | _ => panic! "should not happen after typechecking"
  | .data (.primitive p) => do
    let index ← pushOp (Bytecode.Op.prim p)
    pure #[index]
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
    let index ← pushOp (.xor (a.get' 0) (b.get' 0))
    pure #[index]
  | .and a b => do
    let a ← toIndex layoutMap bindings a
    assert! (a.size == 1)
    let b ← toIndex layoutMap bindings b
    assert! (b.size == 1)
    let index ← pushOp (.and (a.get' 0) (b.get' 0))
    pure #[index]
  | .app name@(⟨.str .anonymous unqualifiedName⟩) args =>
    match bindings.get? (.str unqualifiedName) with
    | some _ => panic! "dynamic calls not yet implemented"
    | none => match layoutMap.get' name with
      | .function layout => do
        let args ← buildArgs args
        let index ← pushOp (Bytecode.Op.call layout.index args layout.outputSize)
        pure $ Array.range' index layout.outputSize
      | .constructor layout => do
        let index ← pushOp (Bytecode.Op.prim (Primitive.u64 layout.index))
        buildArgs args #[index]
      | _ => panic! "should not happen after typechecking"
  | .app name args => match layoutMap.get' name with
    | .function layout => do
      let args ← buildArgs args
      let index ← pushOp (Bytecode.Op.call layout.index args layout.outputSize)
      pure $ Array.range' index layout.outputSize
    | .constructor layout => do
      let index ← pushOp (Bytecode.Op.prim (Primitive.u64 layout.index))
      buildArgs args #[index]
    | _ => panic! "should not happen after typechecking"
  | .preimg name@(⟨.str .anonymous unqualifiedName⟩) out =>
    match bindings.get? (.str unqualifiedName) with
    | some _ => panic! "dynamic preimage not yet implemented"
    | none => match layoutMap.get' name with
      | .function layout => do
        let out ← toIndex layoutMap bindings out
        let index ← pushOp (Bytecode.Op.preimg layout.index out layout.inputSize)
        pure $ Array.range' index layout.inputSize
      | _ => panic! "should not happen after typechecking"
  | .preimg name out => match layoutMap.get' name with
    | .function layout => do
      let out ← toIndex layoutMap bindings out
      let index ← pushOp (Bytecode.Op.preimg layout.index out layout.inputSize)
      pure $ Array.range' index layout.inputSize
    | _ => panic! "should not happen after typechecking"
  | .get arg i => do
    let typs := (match arg.typ with
      | .evaluates (.tuple typs) => typs
      | _ => panic! "should not happen after typechecking")
    let offset := (typs.extract 0 i).foldl (init := 0) (fun acc typ => typSize layoutMap typ + acc)
    pure $ Array.range' offset (offset + typSize layoutMap typ)
  | .slice arg i j => do
    let typs := (match arg.typ with
      | .evaluates (.tuple typs) => typs
      | _ => panic! "should not happen after typechecking")
    let offset := (typs.extract 0 i).foldl (init := 0) (fun acc typ => typSize layoutMap typ + acc)
    let length := (typs.extract i j).foldl (init := 0) (fun acc typ => typSize layoutMap typ + acc)
    pure $ Array.range' offset (offset + length)
  | .store arg => do
    let arg ← toIndex layoutMap bindings arg
    let index ← pushOp (Bytecode.Op.store arg)
    pure #[index]
  | .load ptr => do
    let size := typSize layoutMap ptr.typ.unwrap
    let ptr ← toIndex layoutMap bindings ptr
    assert! (ptr.size == 1)
    let index ← pushOp (Bytecode.Op.load size (ptr.get' 0))
    pure #[index]
  | .pointerAsU64 ptr => toIndex layoutMap bindings ptr
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
        let offset := (offsets.get' i)
        let next_offset := (offsets.get' (i + 1))
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
      let indices := Array.range' index (index + len)
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
          (fun offsets typ => offsets.push (typ.size decls))
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
        (fun offsets (_, typ) => offsets.push (typ.size decls))
    let layout := acc.insert function.name (.function { index := funcIndex, inputSize, outputSize, offsets })
    (layout, funcIndex + 1)
  | .constructor .. => (acc, funcIndex)
  let (layout, _) := decls.pairs.foldl (init := ({}, 0)) pass
  layout

partial def accMemWidths (block : Bytecode.Block) (memWidths : Array Nat) : Array Nat :=
  let memWidths := block.ops.foldl (init := memWidths) fun acc op =>
    match op with
    | .store values =>
      let width := values.size
      if acc.contains width then acc else acc.push width
    | _ => acc
  match block.ctrl with
  | .match _ branches defaultBranch =>
    let memWidths := branches.foldl (init := memWidths) fun acc (_, block) =>
      accMemWidths block acc
    match defaultBranch with
    | some block => accMemWidths block memWidths
    | none => memWidths
  | .if _ tt ff => accMemWidths tt (accMemWidths ff memWidths)
  | .ret .. => memWidths

def TypedDecls.compile (decls : TypedDecls) : Bytecode.Toplevel :=
  let layout := decls.dataTypeLayouts
  let (functions, memWidths) := decls.pairs.foldl (init := (#[], #[]))
    fun acc@(functions, memWidths) (_, decl) => match decl with
      | .function function =>
        let compiledFunction := function.compile layout
        (functions.push compiledFunction, accMemWidths compiledFunction.body memWidths)
      | _ => acc
  ⟨functions, memWidths.qsort⟩

end Aiur
