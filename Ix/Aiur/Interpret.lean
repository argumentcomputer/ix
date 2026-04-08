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
-- Interpreter monad
-- ---------------------------------------------------------------------------

/-- Interpreter monad: heap state + error reporting. -/
abbrev InterpM := StateT Heap (Except String)

private def lookupVar (bindings : Bindings) (l : Local) : InterpM Value :=
  match bindings.find? (·.1 == l) with
  | some (_, v) => pure v
  | none => throw s!"Unbound variable: {repr l}"

/-- Try to resolve a Global as a local binding.
    Only simple (unqualified) names can match a `Local.str` binding. -/
private def tryLocalLookup (g : Global) (bindings : Bindings) : Option Value :=
  match g.toName with
  | .str .anonymous name => bindings.find? (·.1 == Local.str name) |>.map (·.2)
  | _                    => none

-- ---------------------------------------------------------------------------
-- Main interpreter (mutual with application helpers)
-- ---------------------------------------------------------------------------

mutual

/-- Apply a globally-named function or constructor to already-evaluated argument values. -/
private partial def applyGlobal (decls : Decls) (g : Global) (args : List Value) :
    InterpM Value := do
  match decls.getByKey g with
  | some (.function f) =>
      if args.length != f.inputs.length then
        throw s!"arity mismatch calling '{f.name}': \
                 expected {f.inputs.length}, got {args.length}"
      interp decls (f.inputs.map (·.1) |>.zip args) f.body
  | some (.constructor _ _) => return .ctor g args.toArray
  | none => throw s!"apply: '{g}' is not known"
  | some (.dataType _) => throw s!"apply: '{g}' is a type, not callable"

/-- Apply a locally-bound value (dynamic dispatch) to already-evaluated argument values.
    The value must be a `Value.fn` function pointer. -/
private partial def applyLocal (decls : Decls) (v : Value) (args : List Value) :
    InterpM Value :=
  match v with
  | .fn g => applyGlobal decls g args
  | _     => throw s!"apply: expected a function pointer, got {v}"

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
          else throw s!"ref: constructor '{g}' requires {ctor.argTypes.length} argument(s)"
      | some (.dataType _)          => throw s!"ref: '{g}' is a type, not a value"
      | none                        => throw s!"ref: '{g}' is not known"

  | .data (.field g)  => return .field g
  | .data (.tuple ts) => return .tuple (← ts.mapM (interp decls bindings))
  | .data (.array ts) => return .array (← ts.mapM (interp decls bindings))

  | .ret t   => interp decls bindings t
  | .ann _ t => interp decls bindings t

  -- let: evaluate scrutinee, match pattern, extend bindings
  | .let p t1 t2 => do
      let v    ← interp decls bindings t1
      let heap ← get
      match matchPattern heap p v with
      | some bs => interp decls (bs ++ bindings) t2
      | none    => throw "let: pattern match failed"

  -- match: try each case in order
  | .match t cases => do
      let v    ← interp decls bindings t
      let heap ← get
      match cases.findSome? fun (p, body) =>
        matchPattern heap p v |>.map (·, body) with
      | some (bs, body) => interp decls (bs ++ bindings) body
      | none            => throw "match: non-exhaustive patterns"

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
      | _, _ => throw "add: expected field values"

  | .sub t1 t2 => do
      let v1 ← interp decls bindings t1
      let v2 ← interp decls bindings t2
      match v1, v2 with
      | .field a, .field b => return .field (subG a b)
      | _, _ => throw "sub: expected field values"

  | .mul t1 t2 => do
      let v1 ← interp decls bindings t1
      let v2 ← interp decls bindings t2
      match v1, v2 with
      | .field a, .field b => return .field (mulG a b)
      | _, _ => throw "mul: expected field values"

  -- eqZero: returns 1 if the value is zero, 0 otherwise
  | .eqZero t => do
      let v ← interp decls bindings t
      match v with
      | .field g => return .field (if g.val == 0 then 1 else 0)
      | _        => throw "eqZero: expected field value"

  -- tuple projection
  | .proj t n => do
      let v ← interp decls bindings t
      match v with
      | .tuple vs =>
          if h : n < vs.size then return vs[n]
          else throw s!"proj: index {n} out of bounds (size {vs.size})"
      | _ => throw "proj: expected tuple"

  -- array indexing
  | .get t n => do
      let v ← interp decls bindings t
      match v with
      | .array vs =>
          if h : n < vs.size then return vs[n]
          else throw s!"get: index {n} out of bounds (size {vs.size})"
      | _ => throw "get: expected array"

  -- array slice
  | .slice t i j => do
      let v ← interp decls bindings t
      match v with
      | .array vs => return .array (vs.extract i j)
      | _         => throw "slice: expected array"

  -- array update
  | .set t n vTerm => do
      let val ← interp decls bindings vTerm
      let arr ← interp decls bindings t
      match arr with
      | .array vs =>
          if n < vs.size then return .array (vs.set! n val)
          else throw s!"set: index {n} out of bounds (size {vs.size})"
      | _ => throw "set: expected array"

  -- heap store: allocate a new cell
  | .store t => do
      let v   ← interp decls bindings t
      let idx ← modifyGet fun heap => (heap.size, heap.push v)
      return .pointer idx

  -- heap load: dereference a pointer
  | .load t => do
      let v ← interp decls bindings t
      match v with
      | .pointer n =>
          let heap ← get
          if h : n < heap.size then return heap[n]
          else throw s!"load: invalid pointer {n}"
      | _ => throw "load: expected pointer"

  -- pointer address as a field element
  | .ptrVal t => do
      let v ← interp decls bindings t
      match v with
      | .pointer n => return .field (mkG n)
      | _          => throw "ptrVal: expected pointer"

  -- assertion
  | .assertEq t1 t2 ret => do
      let v1 ← interp decls bindings t1
      let v2 ← interp decls bindings t2
      match v1, v2 with
      | .field a, .field b =>
          if a != b then throw s!"assertEq: {a.val} ≠ {b.val}"
          interp decls bindings ret
      | _, _ => throw "assertEq: expected field values"

  -- U8 operations (inputs are field elements encoding bytes 0–255)

  | .u8BitDecomposition t => do
      let v ← interp decls bindings t
      match v with
      | .field g =>
          let byte := g.val.toUInt8
          let mut bits : Array Value := Array.mkEmpty 8
          for i in List.range 8 do
            bits := bits.push (.field (G.ofUInt8 ((byte >>> i.toUInt8) &&& 1)))
          return .array bits
      | _ => throw "u8BitDecomposition: expected field value"

  | .u8ShiftLeft t => do
      let v ← interp decls bindings t
      match v with
      | .field g => return .field (G.ofUInt8 (g.val.toUInt8 <<< 1))
      | _        => throw "u8ShiftLeft: expected field value"

  | .u8ShiftRight t => do
      let v ← interp decls bindings t
      match v with
      | .field g => return .field (G.ofUInt8 (g.val.toUInt8 >>> 1))
      | _        => throw "u8ShiftRight: expected field value"

  | .u8Xor t1 t2 => do
      let v1 ← interp decls bindings t1
      let v2 ← interp decls bindings t2
      match v1, v2 with
      | .field a, .field b => return .field (G.ofUInt8 (a.val.toUInt8 ^^^ b.val.toUInt8))
      | _, _ => throw "u8Xor: expected field values"

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
      | _, _ => throw "u8Add: expected field values"

  | .u8Sub t1 t2 => do
      let v1 ← interp decls bindings t1
      let v2 ← interp decls bindings t2
      match v1, v2 with
      | .field a, .field b => return .field (G.ofUInt8 (a.val.toUInt8 - b.val.toUInt8))
      | _, _ => throw "u8Sub: expected field values"

  | .u8And t1 t2 => do
      let v1 ← interp decls bindings t1
      let v2 ← interp decls bindings t2
      match v1, v2 with
      | .field a, .field b => return .field (G.ofUInt8 (a.val.toUInt8 &&& b.val.toUInt8))
      | _, _ => throw "u8And: expected field values"

  | .u8Or t1 t2 => do
      let v1 ← interp decls bindings t1
      let v2 ← interp decls bindings t2
      match v1, v2 with
      | .field a, .field b => return .field (G.ofUInt8 (a.val.toUInt8 ||| b.val.toUInt8))
      | _, _ => throw "u8Or: expected field values"

  | .u8LessThan t1 t2 => do
      let v1 ← interp decls bindings t1
      let v2 ← interp decls bindings t2
      match v1, v2 with
      | .field a, .field b =>
          return .field (if a.val.toUInt8 < b.val.toUInt8 then 1 else 0)
      | _, _ => throw "u8LessThan: expected field values"

  | .u32LessThan t1 t2 => do
      let v1 ← interp decls bindings t1
      let v2 ← interp decls bindings t2
      match v1, v2 with
      | .field a, .field b =>
          return .field (if a.val.toUInt32 < b.val.toUInt32 then 1 else 0)
      | _, _ => throw "u32LessThan: expected field values"

  -- debug: evaluate and discard the optional value, then continue
  | .debug _ optT cont => do
      if let some t := optT then
        let _ ← interp decls bindings t
      interp decls bindings cont

  -- IO operations (not fully supported)
  | .ioGetInfo key => do
      let _ ← interp decls bindings key
      throw "ioGetInfo: IO not supported in interpreter"

  | .ioSetInfo key idx len ret => do
      let _ ← interp decls bindings key
      let _ ← interp decls bindings idx
      let _ ← interp decls bindings len
      interp decls bindings ret

  | .ioRead idx _ => do
      let _ ← interp decls bindings idx
      throw "ioRead: IO not supported in interpreter"

  | .ioWrite data ret => do
      let _ ← interp decls bindings data
      interp decls bindings ret

end -- mutual

-- ---------------------------------------------------------------------------
-- Top-level entry point
-- ---------------------------------------------------------------------------

/-- Run a named function with the given input values.
    Returns `(output, final_heap)` or an error string. -/
def runFunction (decls : Decls) (funcName : Global) (inputs : List Value) :
    Except String (Value × Heap) := do
  let f ← match decls.getByKey funcName with
    | some (.function f) => pure f
    | _                  => throw s!"Function not found: {funcName}"
  if inputs.length != f.inputs.length then
    throw s!"runFunction: arity mismatch for {funcName}: \
             expected {f.inputs.length}, got {inputs.length}"
  let bindings := f.inputs.map (·.1) |>.zip inputs
  StateT.run (interp decls bindings f.body) #[]

end Aiur

end
