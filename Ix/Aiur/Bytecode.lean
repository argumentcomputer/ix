import Std.Data.HashMap
import Ix.Aiur.Term

open Std

abbrev Name := Aiur.Global
abbrev ValIdx := Nat
abbrev SelIdx := Nat
abbrev FuncIdx := UInt64
abbrev MemIdx := Nat

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
  offsets: List Nat
  deriving Repr, Inhabited

structure ConstructorLayout where
  index: UInt64
  size: Nat
  offsets: List Nat
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
    pure (bindings.get! name)
  | .ref name => match layoutMap.get! name with
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
    let index ← pushOp (.xor a[0]! b[0]!)
    pure #[index]
  | .and a b => do
    let a ← toIndex layoutMap bindings a
    assert! (a.size == 1)
    let b ← toIndex layoutMap bindings b
    assert! (b.size == 1)
    let index ← pushOp (.and a[0]! b[0]!)
    pure #[index]
  | .app name@(⟨.str .anonymous unqualifiedName⟩) args =>
    match bindings.get? (.str unqualifiedName) with
    | some _ => panic! "dynamic calls not yet implemented"
    | none => match layoutMap.get! name with
      | .function layout => do
        let args ← buildArgs args
        let index ← pushOp (Bytecode.Op.call layout.index args layout.outputSize)
        pure $ Array.range' index layout.outputSize
      | .constructor layout => do
        let index ← pushOp (Bytecode.Op.prim (Primitive.u64 layout.index))
        buildArgs args #[index]
      | _ => panic! "should not happen after typechecking"
  | .app name args => match layoutMap.get! name with
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
    | none => match layoutMap.get! name with
      | .function layout => do
        let out ← toIndex layoutMap bindings out
        let index ← pushOp (Bytecode.Op.preimg layout.index out layout.inputSize)
        pure $ Array.range' index layout.inputSize
      | _ => panic! "should not happen after typechecking"
  | .preimg name out => match layoutMap.get! name with
    | .function layout => do
      let out ← toIndex layoutMap bindings out
      let index ← pushOp (Bytecode.Op.preimg layout.index out layout.inputSize)
      pure $ Array.range' index layout.inputSize
    | _ => panic! "should not happen after typechecking"
  | .get arg i => do
    let typs := (match arg.typ with
      | .evaluates (.tuple typs) => typs
      | _ => panic! "should not happen after typechecking")
    let offset := (typs.extract 0 i).foldl (init := 0) (fun acc typ => typSize typ + acc)
    pure $ Array.range' offset (offset + typSize typ)
  | .slice arg i j => do
    let typs := (match arg.typ with
      | .evaluates (.tuple typs) => typs
      | _ => panic! "should not happen after typechecking")
    let offset := (typs.extract 0 i).foldl (init := 0) (fun acc typ => typSize typ + acc)
    let length := (typs.extract i j).foldl (init := 0) (fun acc typ => typSize typ + acc)
    pure $ Array.range' offset (offset + length)
  | .store arg => do
    let arg ← toIndex layoutMap bindings arg
    let index ← pushOp (Bytecode.Op.store arg)
    pure #[index]
  | .load ptr => do
    let size := typSize ptr.typ.unwrap
    let ptr ← toIndex layoutMap bindings ptr
    assert! (ptr.size == 1)
    let index ← pushOp (Bytecode.Op.load size ptr[0]!)
    pure #[index]
  | .pointerAsU64 ptr => toIndex layoutMap bindings ptr
  where
    typSize : Typ → Nat
    | Typ.primitive .. => 1
    | Typ.pointer .. => 1
    | Typ.function .. => 1
    | Typ.tuple ts => ts.foldl (init := 0) (fun acc t => acc + typSize t)
    | Typ.dataType g => match layoutMap.get! g with
      | .dataType layout => layout.size
      | _ => unreachable!
    buildArgs (args : List TypedTerm) (init : Array ValIdx := #[]) : StateM CompilerState (Array ValIdx) :=
      let append arg acc := do
        pure (acc.append (← toIndex layoutMap bindings arg))
      args.foldrM (init := init) append

mutual

partial def TypedTerm.compile
 (term : TypedTerm)
 (returnTyp : Typ)
 (layoutMap : Bytecode.LayoutMap)
 (bindings : HashMap Local (Array ValIdx) := {})
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
            let pat := pats[i]!
            let typ := typs[i]!
            match pat with
            | .var var =>
              let len := typSize typ
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
      let ctrl := .match idxs[0]! cases default
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
    pure { ops, ctrl := .if b[0]! t f, returnIdents := [] }
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
  where
    typSize : Typ → Nat
    | Typ.primitive .. => 1
    | Typ.pointer .. => 1
    | Typ.function .. => 1
    | Typ.tuple ts => ts.foldl (init := 0) (fun acc t => acc + typSize t)
    | Typ.dataType g => match layoutMap.get! g with
      | .dataType layout => layout.size
      | _ => unreachable!

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
    let layout := layoutMap.get! global
    let (index, offsets) := match layout with
    | .function layout => (layout.index, layout.offsets)
    | .constructor layout => (layout.index, layout.offsets)
    | .dataType _ => panic! "impossible after typechecking"
    let bindArgs bindings pats offsets idxs :=
      let n := pats.length
      let init := (bindings, 0)
      let (bindings, _) := (List.range n).foldl (init := init) fun (bindings, offset) i =>
        let pat := pats[i]!
        let len := offsets[i]!
        match pat with
        | .var var =>
          let new_offset := offset + len
          (bindings.insert var (idxs.extract offset new_offset), new_offset)
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
  let (inputSize, outputSize) := match layoutMap.get! f.name with
  | .function layout => (layout.inputSize, layout.outputSize)
  | _ => panic! s!"`{f.name}` should be a function"
  let body :=  (f.body.compile f.output layoutMap).run' default
  { name := f.name, inputSize, outputSize, body }

def TypedDecls.dataTypeLayouts (decls : TypedDecls) : Bytecode.LayoutMap :=
  let pass acc _ v := match v with
  | .dataType dataType =>
    let dataTypeSize := dataType.size decls
    let acc := acc.insert dataType.name (.dataType { size := dataTypeSize })
    let pass := fun (acc, index) constructor =>
      let (_, offsets) :=
        constructor.argTypes.foldr (init := (none, []))
         (fun typ (prev_offset, offsets) => match prev_offset with
          | .none => (some (typ.size decls), offsets)
          | .some prev_offset => (some (typ.size decls), offsets.cons prev_offset))
      let decl := .constructor {
        size := dataTypeSize,
        offsets,
        index,
      }
      let name := dataType.name.pushNamespace constructor.nameHead
      (acc.insert name decl, index + 1)
    (dataType.constructors.foldl (init := (acc, 0)) pass).fst
  | .function function =>
    let inputSize := function.inputs.foldl (init := 0) (fun acc (_, typ) => acc + typ.size decls)
    let outputSize := function.output.size decls
    let (_, offsets) :=
      function.inputs.foldr (init := (none, []))
       (fun (_, typ) (prev_offset, offsets) => match prev_offset with
        | .none => (some (typ.size decls), offsets)
        | .some prev_offset => (some (typ.size decls), offsets.cons prev_offset))
    acc.insert function.name (.function { index := 0, inputSize, outputSize, offsets })
  | .constructor .. => acc
  decls.fold (init := {}) pass

def TypedDecls.compile (decls : TypedDecls) : Bytecode.Toplevel :=
  let layout := decls.dataTypeLayouts
  let functions := decls.fold (init := #[]) fun functions _ decl => match decl with
    | .function function => functions.push (function.compile layout)
    | _ => functions
  -- TODO
  let memWidths := #[]
  { functions, memWidths }

end Aiur
