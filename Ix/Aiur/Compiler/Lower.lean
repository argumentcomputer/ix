module
public import Std.Data.HashMap
public import Ix.Aiur.Stages.Concrete
public import Ix.Aiur.Compiler.Layout

/-!
Bytecode lowering: `Concrete.Decls` → `Bytecode.Toplevel`.

Consumes `Concrete.Term` (no mvars, no parametric apps), so `typSize` has no
failure modes — the `Impossible case` / `unreachable!` sites in
`Ix/Aiur/Compiler/Lower.lean` cannot be reached. The `gadget` arm has been
dropped.

Non-tail match in let-RHS positions is compiled to `Bytecode.Ctrl.matchContinue`
via `findNonTailMatch` + `compileMatchContinue`.
-/

public section
@[expose] section

namespace Aiur

structure FunctionLayout where
  index : Nat
  inputSize : Nat
  outputSize : Nat
  offsets : Array Nat
  deriving Inhabited

structure ConstructorLayout where
  index : Nat
  size : Nat
  offsets : Array Nat
  deriving Inhabited

inductive Layout
  | dataType : (size : Nat) → Layout
  | function : FunctionLayout → Layout
  | constructor : ConstructorLayout → Layout
  deriving Inhabited

abbrev LayoutMap := Std.HashMap Global Layout

open Concrete in
def Concrete.Decls.layoutMap (decls : Decls) : Except String LayoutMap := do
  let pass := fun (layoutMap, funcIdx) (_, v) => do match v with
    | .dataType dataType => do
      let dataTypeSize ← dataType.size decls
      let layoutMap := layoutMap.insert dataType.name (.dataType dataTypeSize)
      let pass := fun (acc, index) constructor => do
        let offsets ← constructor.argTypes.foldlM (init := #[0]) fun offsets typ => do
          let typSyze ← typ.size decls
          pure $ offsets.push ((offsets[offsets.size - 1]?.getD 0) + typSyze)
        let decl := .constructor { size := dataTypeSize, offsets, index }
        let name := dataType.name.pushNamespace constructor.nameHead
        pure (acc.insert name decl, index + 1)
      let (layoutMap, _) ← dataType.constructors.foldlM pass (layoutMap, 0)
      pure (layoutMap, funcIdx)
    | .function function => do
      let inputSize ← function.inputs.foldlM (init := 0) fun acc (_, typ) => do
        let typSize ← typ.size decls
        pure $ acc + typSize
      let outputSize ← function.output.size decls
      let offsets ← function.inputs.foldlM (init := #[0]) fun offsets (_, typ) => do
        let typSyze ← typ.size decls
        pure $ offsets.push ((offsets[offsets.size - 1]?.getD 0) + typSyze)
      let layoutMap := layoutMap.insert function.name $
        .function { index := funcIdx, inputSize, outputSize, offsets }
      pure (layoutMap, funcIdx + 1)
    | .constructor .. => pure (layoutMap, funcIdx)
  let (layoutMap, _) ← decls.foldlM pass ({}, 0)
  pure layoutMap

open Concrete in
def typSize (layoutMap : LayoutMap) : Concrete.Typ → Except String Nat
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
| .ref g => match layoutMap[g]? with
  | some (.dataType size) => pure size
  /- The other arms are ruled out by the `Concrete.Decls.layoutMap` invariant:
     every `.ref` in a well-typed concrete program points at a datatype layout. -/
  | _ => throw s!"Layout missing for `{g}`"

structure CompilerState where
  valIdx : Bytecode.ValIdx
  ops : Array Bytecode.Op
  selIdx : Bytecode.SelIdx
  degrees : Array Nat
  deriving Inhabited

abbrev CompileM := EStateM String CompilerState

def pushOpDegree (degrees : Array Nat) (op : Bytecode.Op) (size : Nat) : Array Nat :=
  if size > 1 then
    (Array.replicate size 1).foldl (init := degrees) (·.push ·)
  else match op with
  | .const _ => degrees.push 0
  | .add a b | .sub a b =>
    degrees.push ((degrees[a]?.getD 0).max (degrees[b]?.getD 0))
  | .mul a b =>
    let d := (degrees[a]?.getD 0) + (degrees[b]?.getD 0)
    degrees.push (if d < 2 then d else 1)
  | .eqZero a => degrees.push (if (degrees[a]?.getD 0) == 0 then 0 else 1)
  | _ => degrees.push 1

def pushOp (op : Bytecode.Op) (size : Nat := 1) : CompileM (Array Bytecode.ValIdx) :=
  modifyGet (fun s =>
    let valIdx := s.valIdx
    (Array.range' valIdx size, { s with
      valIdx := valIdx + size,
      ops := s.ops.push op,
      degrees := pushOpDegree s.degrees op size }))

def extractOps : CompileM (Array Bytecode.Op) :=
  modifyGet fun s => (s.ops, {s with ops := #[]})

open Concrete in
mutual

/-- Lower a `Concrete.Term` to a flat array of `ValIdx`s, appending ops to the
state as needed. Tail-position constructors (`.ret`, `.match`) are handled by
`TypedTerm.compile` at the block level, so this function is for straight-line
code. -/
def toIndex
    (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (term : Term) : CompileM (Array Bytecode.ValIdx) :=
  match term with
  | .unit _ _ => pure #[]
  | .ret .. => throw "ret in value position (should not happen after typechecking)"
  | .match .. => throw "Non-tail match in arbitrary position (not supported)"
  | .letLoad _ _ dst dstTyp src bod => do
    let size ← match typSize layoutMap dstTyp with
      | .error e => throw e
      | .ok n => pure n
    let ptrIdxs := bindings[src]?.getD #[0]
    let loaded ← pushOp (.load size ptrIdxs[0]!) size
    toIndex layoutMap (bindings.insert dst loaded) bod
  | .var _ _ name => pure (bindings[name]?.getD #[])
  | .ref _ _ name => match layoutMap[name]? with
    | some (.function layout) => do
      pushOp (.const (.ofNat layout.index))
    | some (.constructor layout) => do
      let size := layout.size
      let paddingOp := Bytecode.Op.const (.ofNat layout.index)
      let index ← pushOp paddingOp
      if index.size < size then
        let padding := (← pushOp paddingOp)[0]!
        pure $ index ++ Array.replicate (size - index.size) padding
      else
        pure index
    | _ => throw s!"ref: layout missing for `{name}`"
  | .field _ _ g => pushOp (Bytecode.Op.const g)
  | .tuple _ _ terms | .array _ _ terms =>
      terms.foldlM (init := #[]) fun acc arg => do
        pure $ acc ++ (← toIndex layoutMap bindings arg)
  | .letVar _ _ var val bod => do
    let val ← toIndex layoutMap bindings val
    toIndex layoutMap (bindings.insert var val) bod
  | .letWild _ _ val bod => do
    let _ ← toIndex layoutMap bindings val
    toIndex layoutMap bindings bod
  | .add _ _ a b => do
    let a ← expectIdx layoutMap bindings a; let b ← expectIdx layoutMap bindings b
    pushOp (.add a b)
  | .sub _ _ a b => do
    let a ← expectIdx layoutMap bindings a; let b ← expectIdx layoutMap bindings b
    pushOp (.sub a b)
  | .mul _ _ a b => do
    let a ← expectIdx layoutMap bindings a; let b ← expectIdx layoutMap bindings b
    pushOp (.mul a b)
  | .eqZero _ _ a => do
    let a ← expectIdx layoutMap bindings a
    pushOp (.eqZero a)
  | .app _ _ name args unconstrained => match layoutMap[name]? with
    | some (.function layout) => do
      let args ← buildArgs layoutMap bindings args
      pushOp (.call layout.index args layout.outputSize unconstrained) layout.outputSize
    | some (.constructor layout) => do
      let size := layout.size
      let index ← pushOp (.const (.ofNat layout.index))
      let index ← buildArgs layoutMap bindings args index
      if index.size < size then
        let padding := (← pushOp (.const (.ofNat 0)))[0]!
        pure $ index ++ Array.replicate (size - index.size) padding
      else
        pure index
    | _ => throw s!"app: layout missing for `{name}`"
  | .proj _ _ arg i => do
    let typs ← match arg.typ with
      | .tuple typs => pure typs
      | _ => throw "proj on non-tuple"
    let offset ← (typs.extract 0 i).foldlM (init := 0) fun acc typ => do
      let typLen ← match typSize layoutMap typ with
        | .error e => throw e
        | .ok len => pure len
      pure $ typLen + acc
    let arg ← toIndex layoutMap bindings arg
    let iLen ← match typSize layoutMap (typs[i]?.getD .unit) with
      | .error e => throw e
      | .ok len => pure len
    pure $ arg.extract offset (offset + iLen)
  | .get _ _ arr i => do
    let eltTyp ← match arr.typ with
      | .array typ _ => pure typ
      | _ => throw "get on non-array"
    let eltSize ← match typSize layoutMap eltTyp with
      | .error e => throw e
      | .ok len => pure len
    let offset := i * eltSize
    let arr ← toIndex layoutMap bindings arr
    pure $ arr.extract offset (offset + eltSize)
  | .slice _ _ arr i j => do
    let eltTyp ← match arr.typ with
      | .array typ _ => pure typ
      | _ => throw "slice on non-array"
    let eltSize ← match typSize layoutMap eltTyp with
      | .error e => throw e
      | .ok len => pure len
    let arr ← toIndex layoutMap bindings arr
    pure $ arr.extract (i * eltSize) (j * eltSize)
  | .set _ _ arr i val => do
    let eltTyp ← match arr.typ with
      | .array typ _ => pure typ
      | _ => throw "set on non-array"
    let eltSize ← match typSize layoutMap eltTyp with
      | .error e => throw e
      | .ok len => pure len
    let arr ← toIndex layoutMap bindings arr
    let left := arr.extract 0 (i * eltSize)
    let val ← toIndex layoutMap bindings val
    let right := arr.extract ((i + 1) * eltSize)
    pure $ left ++ val ++ right
  | .store _ _ arg => do
    let args ← toIndex layoutMap bindings arg
    pushOp (.store args)
  | .load _ _ ptr => do
    let size ← match ptr.typ with
      | .pointer typ => match typSize layoutMap typ with
        | .error e => throw e
        | .ok len => pure len
      | _ => throw "load on non-pointer"
    let ptr ← expectIdx layoutMap bindings ptr
    pushOp (.load size ptr) size
  | .ptrVal _ _ ptr => toIndex layoutMap bindings ptr
  | .assertEq _ _ a b ret => do
    let a ← toIndex layoutMap bindings a
    let b ← toIndex layoutMap bindings b
    modify fun stt => { stt with ops := stt.ops.push (.assertEq a b) }
    toIndex layoutMap bindings ret
  | .ioGetInfo _ _ key => do
    let key ← toIndex layoutMap bindings key
    pushOp (.ioGetInfo key) 2
  | .ioSetInfo _ _ key idx len ret => do
    let key ← toIndex layoutMap bindings key
    let idx ← expectIdx layoutMap bindings idx
    let len ← expectIdx layoutMap bindings len
    modify fun stt => { stt with ops := stt.ops.push (.ioSetInfo key idx len) }
    toIndex layoutMap bindings ret
  | .ioRead _ _ idx len => do
    let idx ← expectIdx layoutMap bindings idx
    pushOp (.ioRead idx len) len
  | .ioWrite _ _ data ret => do
    let data ← toIndex layoutMap bindings data
    modify fun stt => { stt with ops := stt.ops.push (.ioWrite data) }
    toIndex layoutMap bindings ret
  | .u8BitDecomposition _ _ byte => do
    let byte ← expectIdx layoutMap bindings byte
    pushOp (.u8BitDecomposition byte) 8
  | .u8ShiftLeft _ _ byte => do let byte ← expectIdx layoutMap bindings byte; pushOp (.u8ShiftLeft byte)
  | .u8ShiftRight _ _ byte => do let byte ← expectIdx layoutMap bindings byte; pushOp (.u8ShiftRight byte)
  | .u8Xor _ _ i j => do
    let i ← expectIdx layoutMap bindings i; let j ← expectIdx layoutMap bindings j
    pushOp (.u8Xor i j)
  | .u8Add _ _ i j => do
    let i ← expectIdx layoutMap bindings i; let j ← expectIdx layoutMap bindings j
    pushOp (.u8Add i j) 2
  | .u8Sub _ _ i j => do
    let i ← expectIdx layoutMap bindings i; let j ← expectIdx layoutMap bindings j
    pushOp (.u8Sub i j) 2
  | .u8And _ _ i j => do let i ← expectIdx layoutMap bindings i; let j ← expectIdx layoutMap bindings j; pushOp (.u8And i j)
  | .u8Or _ _ i j => do let i ← expectIdx layoutMap bindings i; let j ← expectIdx layoutMap bindings j; pushOp (.u8Or i j)
  | .u8LessThan _ _ i j => do let i ← expectIdx layoutMap bindings i; let j ← expectIdx layoutMap bindings j; pushOp (.u8LessThan i j)
  | .u32LessThan _ _ i j => do let i ← expectIdx layoutMap bindings i; let j ← expectIdx layoutMap bindings j; pushOp (.u32LessThan i j)
  | .debug _ _ label term ret => do
    let term ← match term with
      | none => pure none
      | some sub => do pure (some (← toIndex layoutMap bindings sub))
    modify fun stt => { stt with ops := stt.ops.push (.debug label term) }
    toIndex layoutMap bindings ret
termination_by (sizeOf term, 0)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

/-- Lower a list of args, appending each lowered ValIdx to `init`. -/
def buildArgs
    (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (args : List Term) (init : Array Bytecode.ValIdx := #[]) :
    CompileM (Array Bytecode.ValIdx) :=
  args.attach.foldlM (init := init) fun acc ⟨arg, _⟩ => do
    pure (acc.append (← toIndex layoutMap bindings arg))
termination_by (sizeOf args, 1)

/-- Lower a term, asserting it produces exactly one ValIdx. -/
def expectIdx
    (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (term : Term) : CompileM Bytecode.ValIdx := do
  let idxs ← toIndex layoutMap bindings term
  if h : idxs.size = 1 then
    have : 0 < idxs.size := by simp only [h, Nat.lt_add_one]
    pure idxs[0]
  else throw "Term is not of size 1"
termination_by (sizeOf term, 1)

end

/-- Compute the max aux/lookup usage across match-continue branches (for layout
pre-reservation). Uses `Bytecode.blockLayout` with the current degree array. -/
def Concrete.computeSharedLayout
    (matchCases : Array (G × Bytecode.Block))
    (defaultBlock : Option Bytecode.Block) : CompileM (Nat × Nat) := do
  let degrees := (← get).degrees
  let initLS : Bytecode.LayoutMState :=
    ⟨{ inputSize := 0, selectors := 0, auxiliaries := 0, lookups := 0 },
     .empty, degrees⟩
  let (sharedAux, sharedLookups) := matchCases.foldl (init := (0, 0))
    fun (maxA, maxL) (_, block) =>
      let (_, ls) := Bytecode.blockLayout block |>.run initLS
      (maxA.max ls.functionLayout.auxiliaries, maxL.max ls.functionLayout.lookups)
  pure $ match defaultBlock with
    | some block =>
      let (_, ls) := Bytecode.blockLayout block |>.run initLS
      (sharedAux.max (ls.functionLayout.auxiliaries + matchCases.size),
       sharedLookups.max ls.functionLayout.lookups)
    | none => (sharedAux, sharedLookups)

mutual

/-- Lower a `Concrete.Term` body to a `Bytecode.Block`. -/
def Concrete.Term.compile
    (term : Concrete.Term) (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool := false) : CompileM Bytecode.Block :=
  match term with
  -- Non-tail match: `let var = match scrut {...}; body` → `matchContinue` ctrl.
  | .letVar _ _ var (.match matchTyp valEscapes scrut cases defaultOpt) bod => do
    if valEscapes then
      -- All branches escape; match is effectively tail, body is dead.
      (Concrete.Term.match matchTyp valEscapes scrut cases defaultOpt).compile
        returnTyp layoutMap bindings yieldCtrl
    else
      let idxs := bindings[scrut]?.getD #[0]
      let ops ← extractOps
      let (matchCases, defaultBlock) ← cases.foldlM (init := (#[], .none))
        (Concrete.addCase layoutMap bindings returnTyp idxs (yieldCtrl := true))
      let defaultBlock ← match defaultOpt with
        | some t => do
          let blk ← t.compile returnTyp layoutMap bindings (yieldCtrl := true)
          pure (some blk)
        | none => pure defaultBlock
      let outputSize ← match typSize layoutMap matchTyp with
        | .error e => throw e
        | .ok n => pure n
      let (sharedAux, sharedLookups) ← Concrete.computeSharedLayout matchCases defaultBlock
      let mergedStart := (← get).valIdx
      modify fun s => { s with
        valIdx := s.valIdx + outputSize,
        degrees := (Array.replicate outputSize 1).foldl (init := s.degrees) (·.push ·) }
      let mergedIdxs := Array.range' mergedStart outputSize
      let continuation ← bod.compile returnTyp layoutMap
        (bindings.insert var mergedIdxs) yieldCtrl
      let ctrl : Bytecode.Ctrl :=
        .matchContinue idxs[0]! matchCases defaultBlock outputSize
          sharedAux sharedLookups continuation
      pure ({ ops, ctrl } : Bytecode.Block)
  | .letWild _ _ (.match matchTyp valEscapes scrut cases defaultOpt) bod => do
    if valEscapes then
      (Concrete.Term.match matchTyp valEscapes scrut cases defaultOpt).compile
        returnTyp layoutMap bindings yieldCtrl
    else
      let idxs := bindings[scrut]?.getD #[0]
      let ops ← extractOps
      let (matchCases, defaultBlock) ← cases.foldlM (init := (#[], .none))
        (Concrete.addCase layoutMap bindings returnTyp idxs (yieldCtrl := true))
      let defaultBlock ← match defaultOpt with
        | some t => do
          let blk ← t.compile returnTyp layoutMap bindings (yieldCtrl := true)
          pure (some blk)
        | none => pure defaultBlock
      let outputSize ← match typSize layoutMap matchTyp with
        | .error e => throw e
        | .ok n => pure n
      let (sharedAux, sharedLookups) ← Concrete.computeSharedLayout matchCases defaultBlock
      modify fun s => { s with
        valIdx := s.valIdx + outputSize,
        degrees := (Array.replicate outputSize 1).foldl (init := s.degrees) (·.push ·) }
      let continuation ← bod.compile returnTyp layoutMap bindings yieldCtrl
      let ctrl : Bytecode.Ctrl :=
        .matchContinue idxs[0]! matchCases defaultBlock outputSize
          sharedAux sharedLookups continuation
      pure ({ ops, ctrl } : Bytecode.Block)
  | .letVar _ _ var val bod => do
    let val ← toIndex layoutMap bindings val
    bod.compile returnTyp layoutMap (bindings.insert var val) yieldCtrl
  | .letWild _ _ val bod => do
    let _ ← toIndex layoutMap bindings val
    bod.compile returnTyp layoutMap bindings yieldCtrl
  | .letLoad _ _ dst dstTyp src bod => do
    let size ← match typSize layoutMap dstTyp with
      | .error e => throw e
      | .ok n => pure n
    let ptrIdxs := bindings[src]?.getD #[0]
    let loaded ← pushOp (.load size ptrIdxs[0]!) size
    bod.compile returnTyp layoutMap (bindings.insert dst loaded) yieldCtrl
  | .debug _ _ label term ret => do
    let term ← term.mapM (toIndex layoutMap bindings)
    modify fun stt => { stt with ops := stt.ops.push (.debug label term) }
    ret.compile returnTyp layoutMap bindings yieldCtrl
  | .assertEq _ _ a b ret => do
    let a ← toIndex layoutMap bindings a
    let b ← toIndex layoutMap bindings b
    modify fun stt => { stt with ops := stt.ops.push (.assertEq a b) }
    ret.compile returnTyp layoutMap bindings yieldCtrl
  | .ioSetInfo _ _ key idx len ret => do
    let key ← toIndex layoutMap bindings key
    let idx ← toIndex layoutMap bindings idx
    let len ← toIndex layoutMap bindings len
    modify fun stt => { stt with ops := stt.ops.push (.ioSetInfo key idx[0]! len[0]!) }
    ret.compile returnTyp layoutMap bindings yieldCtrl
  | .ioWrite _ _ data ret => do
    let data ← toIndex layoutMap bindings data
    modify fun stt => { stt with ops := stt.ops.push (.ioWrite data) }
    ret.compile returnTyp layoutMap bindings yieldCtrl
  | .match _ _ scrut cases defaultOpt => do
    let idxs := bindings[scrut]?.getD #[0]
    let ops ← extractOps
    let (bcCases, defaultBlock) ← cases.foldlM (init := (#[], .none))
      (Concrete.addCase layoutMap bindings returnTyp idxs yieldCtrl)
    let defaultBlock ← match defaultOpt with
      | some t => do
        let blk ← t.compile returnTyp layoutMap bindings yieldCtrl
        pure (some blk)
      | none => pure defaultBlock
    let ctrl : Bytecode.Ctrl := .match idxs[0]! bcCases defaultBlock
    pure ({ ops, ctrl } : Bytecode.Block)
  | .ret _ _ term => do
    let idxs ← toIndex layoutMap bindings term
    let state ← get
    let state := { state with selIdx := state.selIdx + 1 }
    set state
    let ops := state.ops
    let id := state.selIdx
    pure ({ ops, ctrl := .return (id - 1) idxs } : Bytecode.Block)
  | _ => do
    let idxs ← toIndex layoutMap bindings term
    let state ← get
    let state := { state with selIdx := state.selIdx + 1 }
    set state
    let ops := state.ops
    let id := state.selIdx
    let ctrl : Bytecode.Ctrl :=
      if yieldCtrl && !term.escapes then .yield (id - 1) idxs else .return (id - 1) idxs
    pure ({ ops, ctrl } : Bytecode.Block)
termination_by (sizeOf term, 0)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | grind

def Concrete.addCase
    (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (returnTyp : Concrete.Typ)
    (idxs : Array Bytecode.ValIdx)
    (yieldCtrl : Bool := false) :
    (Array (G × Bytecode.Block) × Option Bytecode.Block) →
    (Concrete.Pattern × Concrete.Term) →
    CompileM (Array (G × Bytecode.Block) × Option Bytecode.Block) :=
  fun (cases, defaultBlock) (pat, term) =>
    match pat with
    | .field g => do
      let initState ← get
      let term ← term.compile returnTyp layoutMap bindings yieldCtrl
      set { initState with selIdx := (← get).selIdx }
      pure (cases.push (g, term), defaultBlock)
    | .ref global pats => do
      let (index, offsets) ← match layoutMap[global]? with
        | some (.function layout) => pure (layout.index, layout.offsets)
        | some (.constructor layout) => pure (layout.index, layout.offsets)
        | _ => throw s!"addCase: layout missing for `{global}`"
      -- Bind each sub-pattern `Local` to the corresponding slice of `idxs`.
      -- `idxs[0]` is the tag; argument `i` occupies `idxs[1 + offsets[i] ..
      -- 1 + offsets[i+1]]`.
      let ptrBindings : Std.HashMap Local (Array Bytecode.ValIdx) :=
        (Array.range pats.size).foldl (init := bindings) fun acc i =>
          let startOff := 1 + (offsets[i]?.getD 0)
          let endOff := 1 + (offsets[i+1]?.getD startOff)
          let slice := idxs.extract startOff endOff
          let patLocal := pats[i]?.getD (.idx 0)
          acc.insert patLocal slice
      let initState ← get
      let term ← term.compile returnTyp layoutMap ptrBindings yieldCtrl
      set { initState with selIdx := (← get).selIdx }
      pure (cases.push (.ofNat index, term), defaultBlock)
    | .wildcard => do
      let initState ← get
      let term ← term.compile returnTyp layoutMap bindings yieldCtrl
      set { initState with selIdx := (← get).selIdx }
      pure (cases, .some term)
    | _ => throw "addCase: unsupported pattern in concrete lower"
termination_by _ pair => (sizeOf pair.snd, 1)
decreasing_by all_goals first | decreasing_tactic | grind

end

/-- Lower a full concrete function to bytecode. -/
def Concrete.Function.compile (layoutMap : LayoutMap) (f : Concrete.Function) :
    Except String (Bytecode.Block × Bytecode.LayoutMState) := do
  let (_inputSize, _outputSize) ← match layoutMap[f.name]? with
    | some (.function layout) => pure (layout.inputSize, layout.outputSize)
    | _ => throw s!"`{f.name}` should be a function"
  let (valIdx, bindings) ← f.inputs.foldlM (init := (0, default))
    fun (valIdx, bindings) (arg, typ) => do
      let len ← match typSize layoutMap typ with
        | .error e => throw e
        | .ok len => pure len
      let indices := Array.range' valIdx len
      pure (valIdx + len, bindings.insert arg indices)
  let state := { valIdx, selIdx := 0, ops := #[], degrees := Array.replicate valIdx 1 }
  match f.body.compile f.output layoutMap bindings |>.run state with
  | .error e _ => throw e
  | .ok body _ =>
    let (_, layoutMState) := Bytecode.blockLayout body |>.run (.new valIdx)
    let layoutMState := { layoutMState with functionLayout :=
      { layoutMState.functionLayout with
        lookups := layoutMState.functionLayout.lookups + 1 } }
    pure (body, layoutMState)

def Concrete.Decls.toBytecode (decls : Concrete.Decls) :
    Except String (Bytecode.Toplevel × Std.HashMap Global Bytecode.FunIdx) := do
  let layout ← decls.layoutMap
  let initMemSizes : Bytecode.MemSizes := .empty
  let (functions, memSizes, nameMap) ← decls.foldlM (init := (#[], initMemSizes, {}))
    fun acc@(functions, memSizes, nameMap) (_, decl) => match decl with
      | .function function => do
        let (body, layoutMState) ← function.compile layout
        let nameMap := nameMap.insert function.name functions.size
        let function := ⟨body, layoutMState.functionLayout, function.entry, false⟩
        let memSizes := layoutMState.memSizes.fold (·.insert ·) memSizes
        pure (functions.push function, memSizes, nameMap)
      | _ => pure acc
  pure (⟨functions, memSizes.toArray⟩, nameMap)

end Aiur

end -- @[expose] section
end
