module
public import Ix.Aiur.Term

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
  /-- Heap pointer: index into the interpreter heap. -/
  | pointer : Nat → Value
  deriving Repr, BEq, Inhabited

abbrev Bindings := List (Local × Value)
abbrev Heap     := Array Value

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
-- Interpreter monad
-- ---------------------------------------------------------------------------

/-- Interpreter monad: heap state + error reporting. -/
abbrev InterpM := StateT Heap (Except String)

private def lookupVar (bindings : Bindings) (l : Local) : InterpM Value :=
  match bindings.find? (·.1 == l) with
  | some (_, v) => pure v
  | none => throw s!"Unbound variable: {repr l}"

private def findFunc (toplevel : Toplevel) (g : Global) : Option Function :=
  toplevel.functions.find? (·.name == g)

-- ---------------------------------------------------------------------------
-- Main interpreter
-- ---------------------------------------------------------------------------

/-- Interpret a `Term` under the given bindings.
    Heap allocations accumulate in the `InterpM` state. -/
partial def interp (toplevel : Toplevel) (bindings : Bindings) : Term → InterpM Value
  | .unit => return .unit

  | .var l => lookupVar bindings l

  | .ref g =>
      -- A bare global is a zero-argument constructor unless it names a
      -- zero-input function, in which case we call it.
      match findFunc toplevel g with
      | some f =>
          if f.inputs.isEmpty then interp toplevel [] f.body
          else return .ctor g #[]
      | none => return .ctor g #[]

  | .data (.field g)  => return .field g
  | .data (.tuple ts) => return .tuple (← ts.mapM (interp toplevel bindings))
  | .data (.array ts) => return .array (← ts.mapM (interp toplevel bindings))

  | .ret t   => interp toplevel bindings t
  | .ann _ t => interp toplevel bindings t

  -- let: evaluate scrutinee, match pattern, extend bindings
  | .let p t1 t2 => do
      let v    ← interp toplevel bindings t1
      let heap ← get
      match matchPattern heap p v with
      | some bs => interp toplevel (bs ++ bindings) t2
      | none    => throw "let: pattern match failed"

  -- match: try each case in order
  | .match t cases => do
      let v    ← interp toplevel bindings t
      let heap ← get
      match cases.findSome? fun (p, body) =>
        matchPattern heap p v |>.map (·, body) with
      | some (bs, body) => interp toplevel (bs ++ bindings) body
      | none            => throw "match: non-exhaustive patterns"

  -- function / constructor application
  | .app g args _ => do
      let vs ← args.mapM (interp toplevel bindings)
      match findFunc toplevel g with
      | some f =>
          if vs.length != f.inputs.length then
            throw s!"app: arity mismatch for {g}: \
                     expected {f.inputs.length}, got {vs.length}"
          let inputBindings := f.inputs.map (·.1) |>.zip vs
          interp toplevel inputBindings f.body
      | none => return .ctor g vs.toArray

  -- field arithmetic
  | .add t1 t2 => do
      let v1 ← interp toplevel bindings t1
      let v2 ← interp toplevel bindings t2
      match v1, v2 with
      | .field a, .field b => return .field (addG a b)
      | _, _ => throw "add: expected field values"

  | .sub t1 t2 => do
      let v1 ← interp toplevel bindings t1
      let v2 ← interp toplevel bindings t2
      match v1, v2 with
      | .field a, .field b => return .field (subG a b)
      | _, _ => throw "sub: expected field values"

  | .mul t1 t2 => do
      let v1 ← interp toplevel bindings t1
      let v2 ← interp toplevel bindings t2
      match v1, v2 with
      | .field a, .field b => return .field (mulG a b)
      | _, _ => throw "mul: expected field values"

  -- eqZero: returns 1 if the value is zero, 0 otherwise
  | .eqZero t => do
      let v ← interp toplevel bindings t
      match v with
      | .field g => return .field (if g.val == 0 then 1 else 0)
      | _        => throw "eqZero: expected field value"

  -- tuple projection
  | .proj t n => do
      let v ← interp toplevel bindings t
      match v with
      | .tuple vs =>
          if h : n < vs.size then return vs[n]
          else throw s!"proj: index {n} out of bounds (size {vs.size})"
      | _ => throw "proj: expected tuple"

  -- array indexing
  | .get t n => do
      let v ← interp toplevel bindings t
      match v with
      | .array vs =>
          if h : n < vs.size then return vs[n]
          else throw s!"get: index {n} out of bounds (size {vs.size})"
      | _ => throw "get: expected array"

  -- array slice
  | .slice t i j => do
      let v ← interp toplevel bindings t
      match v with
      | .array vs => return .array (vs.extract i j)
      | _         => throw "slice: expected array"

  -- array update
  | .set t n vTerm => do
      let val ← interp toplevel bindings vTerm
      let arr ← interp toplevel bindings t
      match arr with
      | .array vs =>
          if n < vs.size then return .array (vs.set! n val)
          else throw s!"set: index {n} out of bounds (size {vs.size})"
      | _ => throw "set: expected array"

  -- heap store: allocate a new cell
  | .store t => do
      let v   ← interp toplevel bindings t
      let idx ← modifyGet fun heap => (heap.size, heap.push v)
      return .pointer idx

  -- heap load: dereference a pointer
  | .load t => do
      let v ← interp toplevel bindings t
      match v with
      | .pointer n =>
          let heap ← get
          if h : n < heap.size then return heap[n]
          else throw s!"load: invalid pointer {n}"
      | _ => throw "load: expected pointer"

  -- pointer address as a field element
  | .ptrVal t => do
      let v ← interp toplevel bindings t
      match v with
      | .pointer n => return .field (mkG n)
      | _          => throw "ptrVal: expected pointer"

  -- assertion
  | .assertEq t1 t2 ret => do
      let v1 ← interp toplevel bindings t1
      let v2 ← interp toplevel bindings t2
      if v1 != v2 then throw "assertEq: values are not equal"
      interp toplevel bindings ret

  -- U8 operations (inputs are field elements encoding bytes 0–255)

  | .u8BitDecomposition t => do
      let v ← interp toplevel bindings t
      match v with
      | .field g =>
          let byte := g.val.toUInt8
          let mut bits : Array Value := Array.mkEmpty 8
          for i in List.range 8 do
            bits := bits.push (.field (G.ofUInt8 ((byte >>> i.toUInt8) &&& 1)))
          return .array bits
      | _ => throw "u8BitDecomposition: expected field value"

  | .u8ShiftLeft t => do
      let v ← interp toplevel bindings t
      match v with
      | .field g => return .field (G.ofUInt8 (g.val.toUInt8 <<< 1))
      | _        => throw "u8ShiftLeft: expected field value"

  | .u8ShiftRight t => do
      let v ← interp toplevel bindings t
      match v with
      | .field g => return .field (G.ofUInt8 (g.val.toUInt8 >>> 1))
      | _        => throw "u8ShiftRight: expected field value"

  | .u8Xor t1 t2 => do
      let v1 ← interp toplevel bindings t1
      let v2 ← interp toplevel bindings t2
      match v1, v2 with
      | .field a, .field b => return .field (G.ofUInt8 (a.val.toUInt8 ^^^ b.val.toUInt8))
      | _, _ => throw "u8Xor: expected field values"

  -- u8Add returns a tuple (sum mod 256, overflow bit)
  | .u8Add t1 t2 => do
      let v1 ← interp toplevel bindings t1
      let v2 ← interp toplevel bindings t2
      match v1, v2 with
      | .field a, .field b =>
          let x        := a.val.toUInt8.toNat + b.val.toUInt8.toNat
          let sum      : Value := .field (G.ofUInt8 x.toUInt8)
          let overflow : Value := .field (if x >= 256 then 1 else 0)
          return .tuple #[sum, overflow]
      | _, _ => throw "u8Add: expected field values"

  | .u8Sub t1 t2 => do
      let v1 ← interp toplevel bindings t1
      let v2 ← interp toplevel bindings t2
      match v1, v2 with
      | .field a, .field b => return .field (G.ofUInt8 (a.val.toUInt8 - b.val.toUInt8))
      | _, _ => throw "u8Sub: expected field values"

  | .u8And t1 t2 => do
      let v1 ← interp toplevel bindings t1
      let v2 ← interp toplevel bindings t2
      match v1, v2 with
      | .field a, .field b => return .field (G.ofUInt8 (a.val.toUInt8 &&& b.val.toUInt8))
      | _, _ => throw "u8And: expected field values"

  | .u8Or t1 t2 => do
      let v1 ← interp toplevel bindings t1
      let v2 ← interp toplevel bindings t2
      match v1, v2 with
      | .field a, .field b => return .field (G.ofUInt8 (a.val.toUInt8 ||| b.val.toUInt8))
      | _, _ => throw "u8Or: expected field values"

  | .u8LessThan t1 t2 => do
      let v1 ← interp toplevel bindings t1
      let v2 ← interp toplevel bindings t2
      match v1, v2 with
      | .field a, .field b =>
          return .field (if a.val.toUInt8 < b.val.toUInt8 then 1 else 0)
      | _, _ => throw "u8LessThan: expected field values"

  | .u32LessThan t1 t2 => do
      let v1 ← interp toplevel bindings t1
      let v2 ← interp toplevel bindings t2
      match v1, v2 with
      | .field a, .field b =>
          return .field (if a.val.toUInt32 < b.val.toUInt32 then 1 else 0)
      | _, _ => throw "u32LessThan: expected field values"

  -- debug: evaluate and discard the optional value, then continue
  | .debug _ optT cont => do
      if let some t := optT then
        let _ ← interp toplevel bindings t
      interp toplevel bindings cont

  -- IO operations (not fully supported)
  | .ioGetInfo key => do
      let _ ← interp toplevel bindings key
      throw "ioGetInfo: IO not supported in interpreter"

  | .ioSetInfo key idx len ret => do
      let _ ← interp toplevel bindings key
      let _ ← interp toplevel bindings idx
      let _ ← interp toplevel bindings len
      interp toplevel bindings ret

  | .ioRead idx _ => do
      let _ ← interp toplevel bindings idx
      throw "ioRead: IO not supported in interpreter"

  | .ioWrite data ret => do
      let _ ← interp toplevel bindings data
      interp toplevel bindings ret

-- ---------------------------------------------------------------------------
-- Top-level entry point
-- ---------------------------------------------------------------------------

/-- Run a named function with the given input values.
    Returns `(output, final_heap)` or an error string. -/
def runFunction (toplevel : Toplevel) (funcName : Global) (inputs : List Value) :
    Except String (Value × Heap) := do
  let f ← match findFunc toplevel funcName with
    | some f => pure f
    | none   => throw s!"Function not found: {funcName}"
  if inputs.length != f.inputs.length then
    throw s!"runFunction: arity mismatch for {funcName}: \
             expected {f.inputs.length}, got {inputs.length}"
  let bindings := f.inputs.map (·.1) |>.zip inputs
  StateT.run (interp toplevel bindings f.body) #[]

end Aiur

end
