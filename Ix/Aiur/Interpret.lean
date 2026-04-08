module
public import Ix.Aiur.Term
public import Ix.Aiur.Protocol

public section

namespace Aiur

/-- Runtime values produced by the Aiur interpreter. -/
inductive Value : Type where
  | unit    : Value
  | field   : G → Value
  | tuple   : Array Value → Value
  | array   : Array Value → Value
  /-- Constructor application: constructor name + argument values. -/
  | ctor    : Global → Array Value → Value
  /-- Function pointer: a reference to a named function -/
  | fn      : Global → Value
  /-- Heap pointer: index into the interpreter heap. -/
  | pointer : Nat → Value
  deriving Repr, BEq, Inhabited

abbrev Bindings := List (Local × Value)
abbrev Heap     := Array Value

-- ---------------------------------------------------------------------------
-- Pretty printing
-- ---------------------------------------------------------------------------

private def hexDigit (d : Nat) : Char :=
  if d < 10 then Char.ofNat ('0'.toNat + d)
  else Char.ofNat ('a'.toNat + d - 10)

private partial def natToHexGo (n : Nat) (acc : String) : String :=
  if n == 0 then acc
  else natToHexGo (n / 16) (String.singleton (hexDigit (n % 16)) ++ acc)

private def natToHex (n : Nat) : String :=
  if n == 0 then "0" else natToHexGo n ""

partial def ppValue : Value → String
  | .unit      => "()"
  | .field g   => toString g.val.toNat
  | .tuple vs  => "(" ++ String.intercalate ", " (vs.toList.map ppValue) ++ ")"
  | .array vs  => "[" ++ String.intercalate ", " (vs.toList.map ppValue) ++ "]"
  | .ctor g args =>
      let name := g.toName.toString
      if args.isEmpty then name
      else name ++ "(" ++ String.intercalate ", " (args.toList.map ppValue) ++ ")"
  | .fn g      => "fn(" ++ g.toName.toString ++ ")"
  | .pointer n => "&0x" ++ natToHex n

instance : ToString Value := ⟨ppValue⟩

-- ---------------------------------------------------------------------------
-- Field arithmetic helpers
-- ---------------------------------------------------------------------------

private def gPrime : Nat := gSize.toNat

/-- Reduce a natural number modulo the Goldilocks prime and wrap in G. -/
private def mkG (n : Nat) : G := G.ofNat (n % gPrime)

private def addG (a b : G) : G := mkG (a.val.toNat + b.val.toNat)
private def subG (a b : G) : G := mkG (a.val.toNat + gPrime - b.val.toNat)
private def mulG (a b : G) : G := mkG (a.val.toNat * b.val.toNat)

-- ---------------------------------------------------------------------------
-- Pattern matching (pure, reads heap for pointer dereference)
-- ---------------------------------------------------------------------------

mutual

/-- Try to match a pattern against a value.
    Returns the new bindings introduced by the match, or `none` on failure. -/
private def matchPattern (heap : Heap) : Pattern → Value → Option Bindings
  | .wildcard,    _           => some []
  | .var l,       v           => some [(l, v)]
  | .field g,     .field g'   => if g == g' then some [] else none
  | .tuple pats,  .tuple vs   => matchPatsArr heap pats vs
  | .array pats,  .array vs   => matchPatsArr heap pats vs
  | .ref g pats,  .ctor g' vs =>
      if g != g' then none else matchPatsList heap pats vs.toList
  | .or p1 p2,    v           =>
      matchPattern heap p1 v <|> matchPattern heap p2 v
  | .pointer p,   .pointer n  =>
      if h : n < heap.size then matchPattern heap p heap[n]
      else none
  | _,            _           => none

/-- Match a list of patterns against a list of values element-wise. -/
private def matchPatsList (heap : Heap) : List Pattern → List Value → Option Bindings
  | [],      []      => some []
  | p :: ps, v :: vs => do
      let b1 ← matchPattern heap p v
      let b2 ← matchPatsList heap ps vs
      return b1 ++ b2
  | _,       _       => none

/-- Match an array of patterns against an array of values element-wise. -/
private def matchPatsArr (heap : Heap) (pats : Array Pattern) (vs : Array Value) :
    Option Bindings :=
  matchPatsList heap pats.toList vs.toList

end

-- ---------------------------------------------------------------------------
-- Interrupt: early return or runtime error with call-stack trace
-- ---------------------------------------------------------------------------

/-- An `Interrupt` terminates a computation early.
    Errors carry a message and a call-stack trace (function + arguments at each
    call site); the trace starts empty and is extended at every `applyGlobal`
    call site as the interrupt unwinds. -/
inductive Interrupt where
  | error : String → List (Global × List Value) → Interrupt
  | ret   : Value → Interrupt

instance : ToString Interrupt where
  toString
    | .ret v           => s!"unexpected return: {v}"
    | .error msg []    => msg
    | .error msg stack =>
        let frames := stack.map fun (g, args) =>
          let argStr := String.intercalate ", " (args.map toString)
          s!"  in {g}({argStr})"
        msg ++ "\nCall stack:\n" ++ String.intercalate "\n" frames

-- ---------------------------------------------------------------------------
-- Interpreter monad
-- ---------------------------------------------------------------------------

/-- Interpreter state: heap + IO buffer. -/
structure InterpState where
  heap : Heap
  ioBuffer : IOBuffer

/-- Interpreter monad: heap + IO buffer state, structured interrupts (errors and returns). -/
abbrev InterpM := StateT InterpState (Except Interrupt)

/-- Throw a runtime error (call stack starts empty here). -/
private def throwErr (msg : String) : InterpM α :=
  throw (.error msg [])

private def getHeap : InterpM Heap := return (← get).heap
private def getIOBuffer : InterpM IOBuffer := return (← get).ioBuffer
private def modifyHeap (f : Heap → Heap) : InterpM Unit :=
  modify fun s => { s with heap := f s.heap }
private def modifyIOBuffer (f : IOBuffer → IOBuffer) : InterpM Unit :=
  modify fun s => { s with ioBuffer := f s.ioBuffer }

private def expectField : Value → InterpM G
  | .field g => pure g
  | v        => throwErr s!"expected field value, got {v}"

private def expectFieldArray : Value → InterpM (Array G)
  | .array vs => vs.mapM expectField
  | v         => throwErr s!"expected array of field values, got {v}"

private def lookupVar (bindings : Bindings) (l : Local) : InterpM Value :=
  match bindings.find? (·.1 == l) with
  | some (_, v) => pure v
  | none => throwErr s!"Unbound variable: {repr l}"

/-- Try to resolve a Global as a local binding.
    Only simple (unqualified) names can match a `Local.str` binding. -/
private def tryLocalLookup (g : Global) (bindings : Bindings) : Option Value :=
  match g.toName with
  | .str .anonymous name => bindings.find? (·.1 == Local.str name) |>.map (·.2)
  | _                    => none

-- ---------------------------------------------------------------------------
-- Main interpreter (mutual with application helpers)
-- ---------------------------------------------------------------------------

/-- Wrap a function body: captures `.ret v` as the return value, and annotates
    `.error` interrupts with the call site `(g, args)`. -/
private def callSite (g : Global) (args : List Value) (m : InterpM Value) : InterpM Value :=
  tryCatch m fun i => match i with
    | .ret v           => pure v
    | .error msg stack => throw (.error msg ((g, args) :: stack))

mutual

/-- Apply a globally-named function or constructor to already-evaluated argument values. -/
private partial def applyGlobal (decls : Decls) (g : Global) (args : List Value) :
    InterpM Value :=
  callSite g args do
    match decls.getByKey g with
    | some (.function f) =>
        if args.length != f.inputs.length then
          throwErr s!"arity mismatch calling '{f.name}': \
                     expected {f.inputs.length}, got {args.length}"
        interp decls (f.inputs.map (·.1) |>.zip args) f.body
    | some (.constructor _ _) => return .ctor g args.toArray
    | none                    => throwErr s!"apply: '{g}' is not known"
    | some (.dataType _)      => throwErr s!"apply: '{g}' is a type, not callable"

/-- Apply a locally-bound value (dynamic dispatch) to already-evaluated argument values.
    The value must be a `Value.fn` function pointer. -/
private partial def applyLocal (decls : Decls) (v : Value) (args : List Value) :
    InterpM Value :=
  match v with
  | .fn g => applyGlobal decls g args
  | _     => throwErr s!"apply: expected a function pointer, got {v}"

/-- Interpret a `Term` under the given bindings.
    Heap allocations accumulate in the `InterpM` state. -/
partial def interp (decls : Decls) (bindings : Bindings) : Term → InterpM Value
  | .unit => return .unit

  | .var l => lookupVar bindings l

  -- A reference is a function pointer or a zero-argument constructor.
  -- References to constructors with arguments, or unknown names, are errors.
  | .ref g =>
      match decls.getByKey g with
      | some (.function _)          => return .fn g
      | some (.constructor _ ctor)  =>
          if ctor.argTypes.isEmpty then return .ctor g #[]
          else throwErr s!"ref: constructor '{g}' requires {ctor.argTypes.length} argument(s)"
      | some (.dataType _)          => throwErr s!"ref: '{g}' is a type, not a value"
      | none                        => throwErr s!"ref: '{g}' is not known"

  | .data (.field g)  => return .field g
  | .data (.tuple ts) => return .tuple (← ts.mapM (interp decls bindings))
  | .data (.array ts) => return .array (← ts.mapM (interp decls bindings))

  | .ret t   => do let v ← interp decls bindings t; throw (.ret v)
  | .ann _ t => interp decls bindings t

  -- let: evaluate scrutinee, match pattern, extend bindings
  | .let p t1 t2 => do
      let v    ← interp decls bindings t1
      let heap ← getHeap
      match matchPattern heap p v with
      | some bs => interp decls (bs ++ bindings) t2
      | none    => throwErr "let: pattern match failed"

  -- match: try each case in order
  | .match t cases => do
      let v    ← interp decls bindings t
      let heap ← getHeap
      match cases.findSome? fun (p, body) =>
        matchPattern heap p v |>.map (·, body) with
      | some (bs, body) => interp decls (bs ++ bindings) body
      | none            => throwErr "match: non-exhaustive patterns"

  -- application: check local bindings first (dynamic), then global lookup (static)
  | .app g args _ => do
      let vs ← args.mapM (interp decls bindings)
      match tryLocalLookup g bindings with
      | some v => applyLocal decls v vs
      | none   => applyGlobal decls g vs

  -- field arithmetic
  | .add t1 t2 => do
      let v1 ← interp decls bindings t1
      let v2 ← interp decls bindings t2
      match v1, v2 with
      | .field a, .field b => return .field (addG a b)
      | _, _ => throwErr "add: expected field values"

  | .sub t1 t2 => do
      let v1 ← interp decls bindings t1
      let v2 ← interp decls bindings t2
      match v1, v2 with
      | .field a, .field b => return .field (subG a b)
      | _, _ => throwErr "sub: expected field values"

  | .mul t1 t2 => do
      let v1 ← interp decls bindings t1
      let v2 ← interp decls bindings t2
      match v1, v2 with
      | .field a, .field b => return .field (mulG a b)
      | _, _ => throwErr "mul: expected field values"

  -- eqZero: returns 1 if the value is zero, 0 otherwise
  | .eqZero t => do
      let v ← interp decls bindings t
      match v with
      | .field g => return .field (if g.val == 0 then 1 else 0)
      | _        => throwErr "eqZero: expected field value"

  -- tuple projection
  | .proj t n => do
      let v ← interp decls bindings t
      match v with
      | .tuple vs =>
          if h : n < vs.size then return vs[n]
          else throwErr s!"proj: index {n} out of bounds (size {vs.size})"
      | _ => throwErr "proj: expected tuple"

  -- array indexing
  | .get t n => do
      let v ← interp decls bindings t
      match v with
      | .array vs =>
          if h : n < vs.size then return vs[n]
          else throwErr s!"get: index {n} out of bounds (size {vs.size})"
      | _ => throwErr "get: expected array"

  -- array slice
  | .slice t i j => do
      let v ← interp decls bindings t
      match v with
      | .array vs => return .array (vs.extract i j)
      | _         => throwErr "slice: expected array"

  -- array update
  | .set t n vTerm => do
      let val ← interp decls bindings vTerm
      let arr ← interp decls bindings t
      match arr with
      | .array vs =>
          if n < vs.size then return .array (vs.set! n val)
          else throwErr s!"set: index {n} out of bounds (size {vs.size})"
      | _ => throwErr "set: expected array"

  -- heap store: allocate a new cell
  | .store t => do
      let v ← interp decls bindings t
      let heap ← getHeap
      let idx := heap.size
      modifyHeap (·.push v)
      return .pointer idx

  -- heap load: dereference a pointer
  | .load t => do
      let v ← interp decls bindings t
      match v with
      | .pointer n =>
          let heap ← getHeap
          if h : n < heap.size then return heap[n]
          else throwErr s!"load: invalid pointer {n}"
      | _ => throwErr "load: expected pointer"

  -- pointer address as a field element
  | .ptrVal t => do
      let v ← interp decls bindings t
      match v with
      | .pointer n => return .field (mkG n)
      | _          => throwErr "ptrVal: expected pointer"

  -- assertion
  | .assertEq t1 t2 ret => do
      let v1 ← interp decls bindings t1
      let v2 ← interp decls bindings t2
      if v1 != v2 then throwErr s!"assertEq: {v1} ≠ {v2}"
      interp decls bindings ret

  -- U8 operations (inputs are field elements encoding bytes 0–255)

  | .u8BitDecomposition t => do
      let v ← interp decls bindings t
      match v with
      | .field g =>
          let byte := g.val.toUInt8
          return .array (Array.ofFn fun (i : Fin 8) =>
            .field (G.ofUInt8 ((byte >>> i.val.toUInt8) &&& 1)))
      | _ => throwErr "u8BitDecomposition: expected field value"

  | .u8ShiftLeft t => do
      let v ← interp decls bindings t
      match v with
      | .field g => return .field (G.ofUInt8 (g.val.toUInt8 <<< 1))
      | _        => throwErr "u8ShiftLeft: expected field value"

  | .u8ShiftRight t => do
      let v ← interp decls bindings t
      match v with
      | .field g => return .field (G.ofUInt8 (g.val.toUInt8 >>> 1))
      | _        => throwErr "u8ShiftRight: expected field value"

  | .u8Xor t1 t2 => do
      let v1 ← interp decls bindings t1
      let v2 ← interp decls bindings t2
      match v1, v2 with
      | .field a, .field b => return .field (G.ofUInt8 (a.val.toUInt8 ^^^ b.val.toUInt8))
      | _, _ => throwErr "u8Xor: expected field values"

  -- u8Add returns a tuple (sum mod 256, overflow bit)
  | .u8Add t1 t2 => do
      let v1 ← interp decls bindings t1
      let v2 ← interp decls bindings t2
      match v1, v2 with
      | .field a, .field b =>
          let x        := a.val.toUInt8.toNat + b.val.toUInt8.toNat
          let sum      : Value := .field (G.ofUInt8 x.toUInt8)
          let overflow : Value := .field (if x >= 256 then 1 else 0)
          return .tuple #[sum, overflow]
      | _, _ => throwErr "u8Add: expected field values"

  | .u8Sub t1 t2 => do
      let v1 ← interp decls bindings t1
      let v2 ← interp decls bindings t2
      match v1, v2 with
      | .field a, .field b =>
          let i := a.val.toUInt8
          let j := b.val.toUInt8
          return .tuple #[.field (G.ofUInt8 (i - j)), .field (if j > i then 1 else 0)]
      | _, _ => throwErr "u8Sub: expected field values"

  | .u8And t1 t2 => do
      let v1 ← interp decls bindings t1
      let v2 ← interp decls bindings t2
      match v1, v2 with
      | .field a, .field b => return .field (G.ofUInt8 (a.val.toUInt8 &&& b.val.toUInt8))
      | _, _ => throwErr "u8And: expected field values"

  | .u8Or t1 t2 => do
      let v1 ← interp decls bindings t1
      let v2 ← interp decls bindings t2
      match v1, v2 with
      | .field a, .field b => return .field (G.ofUInt8 (a.val.toUInt8 ||| b.val.toUInt8))
      | _, _ => throwErr "u8Or: expected field values"

  | .u8LessThan t1 t2 => do
      let v1 ← interp decls bindings t1
      let v2 ← interp decls bindings t2
      match v1, v2 with
      | .field a, .field b =>
          return .field (if a.val.toUInt8 < b.val.toUInt8 then 1 else 0)
      | _, _ => throwErr "u8LessThan: expected field values"

  | .u32LessThan t1 t2 => do
      let v1 ← interp decls bindings t1
      let v2 ← interp decls bindings t2
      match v1, v2 with
      | .field a, .field b =>
          return .field (if a.val.toUInt32 < b.val.toUInt32 then 1 else 0)
      | _, _ => throwErr "u32LessThan: expected field values"

  -- debug: print label and optional value, then continue
  | .debug label optT cont => do
      match optT with
      | none   => dbg_trace s!"{label}"
      | some t =>
        let v ← interp decls bindings t
        dbg_trace s!"{label}: {v}"
      interp decls bindings cont

  -- IO operations
  | .ioGetInfo key => do
      let keyGs ← expectFieldArray (← interp decls bindings key)
      let io ← getIOBuffer
      match io.map[keyGs]? with
      | some info =>
        return .tuple #[.field (.ofNat info.idx), .field (.ofNat info.len)]
      | none => throwErr s!"ioGetInfo: key not found"

  | .ioSetInfo key idx len ret => do
      let keyGs ← expectFieldArray (← interp decls bindings key)
      let idxVal ← expectField (← interp decls bindings idx)
      let lenVal ← expectField (← interp decls bindings len)
      let info : IOKeyInfo := ⟨idxVal.val.toNat, lenVal.val.toNat⟩
      modifyIOBuffer fun io => { io with map := io.map.insert keyGs info }
      interp decls bindings ret

  | .ioRead idx len => do
      let idxVal ← expectField (← interp decls bindings idx)
      let io ← getIOBuffer
      let start := idxVal.val.toNat
      return .array (io.data.extract start (start + len) |>.map .field)

  | .ioWrite data ret => do
      let dataGs ← expectFieldArray (← interp decls bindings data)
      modifyIOBuffer fun io => { io with data := io.data ++ dataGs }
      interp decls bindings ret

end -- mutual

-- ---------------------------------------------------------------------------
-- Flattening values to field elements (matching bytecode layout)
-- ---------------------------------------------------------------------------

mutual

private partial def typFlatSize (decls : Decls) : Typ → Nat
  | .unit         => 0
  | .field        => 1
  | .pointer _    => 1
  | .function _ _ => 1
  | .tuple ts     => ts.foldl (init := 0) fun acc t => acc + typFlatSize decls t
  | .array t n    => n * typFlatSize decls t
  | .ref g | .app g _ =>
      match decls.getByKey g with
      | some (.dataType dt) => dataTypeFlatSize decls dt
      | _                   => 0
  | .mvar _       => 0

private partial def dataTypeFlatSize (decls : Decls) (dt : DataType) : Nat :=
  let ctorSizes := dt.constructors.map fun ctor =>
    ctor.argTypes.foldl (init := 0) fun acc t => acc + typFlatSize decls t
  ctorSizes.foldl max 0 + 1

end

/-- Flatten a `Value` to an `Array G`, matching the bytecode flat layout.
    `funcIdx` maps function globals to their compiled indices. -/
partial def flattenValue (decls : Decls) (funcIdx : Global → Option Nat) :
    Value → Array G
  | .unit      => #[]
  | .field g   => #[g]
  | .pointer n => #[.ofNat n]
  | .fn g      => #[.ofNat (funcIdx g |>.getD 0)]
  | .tuple vs  => vs.flatMap (flattenValue decls funcIdx)
  | .array vs  => vs.flatMap (flattenValue decls funcIdx)
  | .ctor g args =>
      match decls.getByKey g with
      | some (.constructor dt ctor) =>
          let ctorIndex := dt.constructors.findIdx? (· == ctor) |>.getD 0
          let dtSize := dataTypeFlatSize decls dt
          let flat := #[.ofNat ctorIndex] ++ args.flatMap (flattenValue decls funcIdx)
          let padding := dtSize - flat.size
          flat ++ Array.replicate padding 0
      | _ => args.flatMap (flattenValue decls funcIdx)

-- ---------------------------------------------------------------------------
-- Unflattening field elements to structured values (inverse of flattenValue)
-- ---------------------------------------------------------------------------

/-- Read a structured `Value` from a flat `Array G` starting at `offset`,
    guided by the `Typ`. Returns the value and the number of elements consumed. -/
partial def unflattenValue (decls : Decls) (gs : Array G) (offset : Nat) :
    Typ → Value × Nat
  | .unit         => (.unit, 0)
  | .field        => (.field (gs.getD offset 0), 1)
  | .pointer _    => (.pointer (gs.getD offset 0).val.toNat, 1)
  | .function _ _ => (.fn ⟨.anonymous⟩, 1)  -- best effort; index → name not available
  | .tuple ts     =>
      let (vs, consumed) := ts.foldl (init := (#[], 0)) fun (acc, off) t =>
        let (v, n) := unflattenValue decls gs (offset + off) t
        (acc.push v, off + n)
      (.tuple vs, consumed)
  | .array t n    =>
      let eltSize := typFlatSize decls t
      let vs := Array.ofFn fun (i : Fin n) =>
        (unflattenValue decls gs (offset + i.val * eltSize) t).1
      (.array vs, n * eltSize)
  | .ref g | .app g _ =>
      match decls.getByKey g with
      | some (.dataType dt) =>
          let dtSize := dataTypeFlatSize decls dt
          let tag := (gs.getD offset 0).val.toNat
          let ctors := dt.constructors.toArray
          if h : tag < ctors.size then
            let ctor := ctors[tag]
            let ctorName := dt.name.pushNamespace ctor.nameHead
            let (args, _) := ctor.argTypes.foldl (init := (#[], 1)) fun (acc, off) t =>
              let (v, n) := unflattenValue decls gs (offset + off) t
              (acc.push v, off + n)
            (.ctor ctorName args, dtSize)
          else (.field (gs.getD offset 0), dtSize)
      | _ => (.field (gs.getD offset 0), 1)
  | .mvar _ => (.unit, 0)

/-- Reconstruct structured input `Value`s from a flat `Array G` according to
    the function's input types. -/
def unflattenInputs (decls : Decls) (gs : Array G) (inputTypes : List Typ) :
    List Value :=
  let (vals, _) := inputTypes.foldl (init := (#[], 0)) fun (acc, off) t =>
    let (v, n) := unflattenValue decls gs off t
    (acc.push v, off + n)
  vals.toList

-- ---------------------------------------------------------------------------
-- Top-level entry point
-- ---------------------------------------------------------------------------

/-- Run a named function with the given input values.
    Returns `(output, final_state)` or an `Interrupt`. -/
def runFunction (decls : Decls) (funcName : Global) (inputs : List Value)
    (ioBuffer : IOBuffer := default) :
    Except Interrupt (Value × InterpState) := do
  let f ← match decls.getByKey funcName with
    | some (.function f) => pure f
    | _                  => throw (.error s!"Function not found: {funcName}" [])
  if inputs.length != f.inputs.length then
    throw (.error s!"runFunction: arity mismatch for {funcName}: \
                    expected {f.inputs.length}, got {inputs.length}" [])
  let bindings := f.inputs.map (·.1) |>.zip inputs
  StateT.run (interp decls bindings f.body) ⟨#[], ioBuffer⟩

end Aiur

end
