module
public import Ix.Aiur.Stages.Source
public import Ix.Aiur.Flatten
public import Ix.Aiur.Protocol

/-!
Debug interpreter — fast interactive execution with `callCache` and call-stack
traces. Still `partial` by design: loops on non-terminating programs.
-/

public section

namespace Aiur

open Source

abbrev Bindings := List (Local × Value)
abbrev Store    := IndexMap (Array Value) Unit

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
  | .fn g        => "fn(" ++ g.toName.toString ++ ")"
  | .pointer _ n => "&0x" ++ natToHex n

instance : ToString Value := ⟨ppValue⟩

-- ---------------------------------------------------------------------------
-- Pattern matching
-- ---------------------------------------------------------------------------

mutual

private def matchPattern (store : Store) :
    Pattern → Value → Option Bindings
  | .wildcard,    _           => some []
  | .var l,       v           => some [(l, v)]
  | .field g,     .field g'   => if g == g' then some [] else none
  | .tuple pats,  .tuple vs   => matchPatsArr store pats vs
  | .array pats,  .array vs   => matchPatsArr store pats vs
  | .ref g pats,  .ctor g' vs =>
      if g != g' then none else matchPatsList store pats vs.toList
  | .or p1 p2,    v           =>
      matchPattern store p1 v <|> matchPattern store p2 v
  | .pointer p,   .pointer _ n =>
      match store.getByIdx n with
      | some (vs, _) => vs[0]?.bind (matchPattern store p ·)
      | none         => none
  | _,            _           => none

private def matchPatsList (store : Store) :
    List Pattern → List Value → Option Bindings
  | [],      []      => some []
  | p :: ps, v :: vs => do
      let b1 ← matchPattern store p v
      let b2 ← matchPatsList store ps vs
      return b1 ++ b2
  | _,       _       => none

private def matchPatsArr (store : Store)
    (pats : Array Pattern) (vs : Array Value) : Option Bindings :=
  matchPatsList store pats.toList vs.toList

end

-- ---------------------------------------------------------------------------
-- Interrupt
-- ---------------------------------------------------------------------------

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

structure InterpState where
  store      : Store := default
  ioBuffer   : IOBuffer
  callCache  : Std.HashMap (Global × List Value) Value := {}

abbrev InterpM := StateT InterpState (Except Interrupt)

private def throwErr (msg : String) : InterpM α :=
  throw (.error msg [])

private def getStore : InterpM Store := return (← get).store
private def getIOBuffer : InterpM IOBuffer := return (← get).ioBuffer
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

private def tryLocalLookup (g : Global) (bindings : Bindings) : Option Value :=
  match g.toName with
  | .str .anonymous name => bindings.find? (·.1 == Local.str name) |>.map (·.2)
  | _                    => none

-- ---------------------------------------------------------------------------
-- Main interpreter
-- ---------------------------------------------------------------------------

private def callSite (g : Global) (args : List Value) (m : InterpM Value) : InterpM Value :=
  tryCatch m fun i => match i with
    | .ret v           => pure v
    | .error msg stack => throw (.error msg ((g, args) :: stack))

mutual

private partial def applyGlobal (decls : Decls) (g : Global) (args : List Value) :
    InterpM Value :=
  callSite g args do
    match decls.getByKey g with
    | some (.function f) =>
        if args.length != f.inputs.length then
          throwErr s!"arity mismatch calling '{f.name}': \
                     expected {f.inputs.length}, got {args.length}"
        if let some v := (← get).callCache[(g, args)]? then
          return v
        let v ← interp decls (f.inputs.map (·.1) |>.zip args) f.body
        modify fun s => { s with callCache := s.callCache.insert (g, args) v }
        return v
    | some (.constructor _ _) => return .ctor g args.toArray
    | none                    => throwErr s!"apply: '{g}' is not known"
    | some (.dataType _)      => throwErr s!"apply: '{g}' is a type, not callable"

private partial def applyLocal (decls : Decls) (v : Value) (args : List Value) :
    InterpM Value :=
  match v with
  | .fn g => applyGlobal decls g args
  | _     => throwErr s!"apply: expected a function pointer, got {v}"

partial def interp (decls : Decls) (bindings : Bindings) : Term → InterpM Value
  | .unit => return .unit
  | .var l => lookupVar bindings l
  | .ref g =>
      match decls.getByKey g with
      | some (.function _)          => return .fn g
      | some (.constructor _ ctor)  =>
          if ctor.argTypes.isEmpty then return .ctor g #[]
          else throwErr s!"ref: constructor '{g}' requires {ctor.argTypes.length} argument(s)"
      | some (.dataType _)          => throwErr s!"ref: '{g}' is a type, not a value"
      | none                        => throwErr s!"ref: '{g}' is not known"
  | .field g  => return .field g
  | .tuple ts => return .tuple (← ts.mapM (interp decls bindings))
  | .array ts => return .array (← ts.mapM (interp decls bindings))
  | .ret t   => do let v ← interp decls bindings t; throw (.ret v)
  | .ann _ t => interp decls bindings t
  | .let p t1 t2 => do
      let v     ← interp decls bindings t1
      let store ← getStore
      match matchPattern store p v with
      | some bs => interp decls (bs ++ bindings) t2
      | none    => throwErr "let: pattern match failed"
  | .match t cases => do
      let v     ← interp decls bindings t
      let store ← getStore
      match cases.findSome? fun (p, body) =>
        matchPattern store p v |>.map (·, body) with
      | some (bs, body) => interp decls (bs ++ bindings) body
      | none            => throwErr "match: non-exhaustive patterns"
  | .app g args _ => do
      let vs ← args.mapM (interp decls bindings)
      match tryLocalLookup g bindings with
      | some v => applyLocal decls v vs
      | none   => applyGlobal decls g vs
  | .add t1 t2 => do
      match (← interp decls bindings t1), (← interp decls bindings t2) with
      | .field a, .field b => return .field (a + b)
      | _, _ => throwErr "add: expected field values"
  | .sub t1 t2 => do
      match (← interp decls bindings t1), (← interp decls bindings t2) with
      | .field a, .field b => return .field (a - b)
      | _, _ => throwErr "sub: expected field values"
  | .mul t1 t2 => do
      match (← interp decls bindings t1), (← interp decls bindings t2) with
      | .field a, .field b => return .field (a * b)
      | _, _ => throwErr "mul: expected field values"
  | .eqZero t => do
      match ← interp decls bindings t with
      | .field g => return .field (if g.val == 0 then 1 else 0)
      | _        => throwErr "eqZero: expected field value"
  | .proj t n => do
      match ← interp decls bindings t with
      | .tuple vs =>
          if h : n < vs.size then return vs[n]
          else throwErr s!"proj: index {n} out of bounds (size {vs.size})"
      | _ => throwErr "proj: expected tuple"
  | .get t n => do
      match ← interp decls bindings t with
      | .array vs =>
          if h : n < vs.size then return vs[n]
          else throwErr s!"get: index {n} out of bounds (size {vs.size})"
      | _ => throwErr "get: expected array"
  | .slice t i j => do
      match ← interp decls bindings t with
      | .array vs => return .array (vs.extract i j)
      | _         => throwErr "slice: expected array"
  | .set t n vTerm => do
      let val ← interp decls bindings vTerm
      match ← interp decls bindings t with
      | .array vs =>
          if n < vs.size then return .array (vs.set! n val)
          else throwErr s!"set: index {n} out of bounds (size {vs.size})"
      | _ => throwErr "set: expected array"
  | .store t => do
      let v ← interp decls bindings t
      let store ← getStore
      if let some idx := store.getIdxOf #[v] then
        return .pointer 0 idx
      let idx := store.size
      modify fun s => { s with store := s.store.insert #[v] () }
      return .pointer 0 idx
  | .load t => do
      match ← interp decls bindings t with
      | .pointer _ n =>
          let store ← getStore
          match store.getByIdx n with
          | some (vs, _) => return vs[0]!
          | none         => throwErr s!"load: invalid pointer {n}"
      | _ => throwErr "load: expected pointer"
  | .ptrVal t => do
      match ← interp decls bindings t with
      | .pointer _ n => return .field (G.ofNat n)
      | _            => throwErr "ptrVal: expected pointer"
  | .assertEq t1 t2 ret => do
      let v1 ← interp decls bindings t1
      let v2 ← interp decls bindings t2
      if v1 != v2 then throwErr s!"assertEq: {v1} ≠ {v2}"
      interp decls bindings ret
  | .u8BitDecomposition t => do
      match ← interp decls bindings t with
      | .field g =>
          let byte := g.val.toUInt8
          return .array (Array.ofFn fun (i : Fin 8) =>
            .field (G.ofUInt8 ((byte >>> i.val.toUInt8) &&& 1)))
      | _ => throwErr "u8BitDecomposition: expected field value"
  | .u8ShiftLeft t => do
      match ← interp decls bindings t with
      | .field g => return .field (G.ofUInt8 (g.val.toUInt8 <<< 1))
      | _        => throwErr "u8ShiftLeft: expected field value"
  | .u8ShiftRight t => do
      match ← interp decls bindings t with
      | .field g => return .field (G.ofUInt8 (g.val.toUInt8 >>> 1))
      | _        => throwErr "u8ShiftRight: expected field value"
  | .u8Xor t1 t2 => do
      match (← interp decls bindings t1), (← interp decls bindings t2) with
      | .field a, .field b => return .field (G.ofUInt8 (a.val.toUInt8 ^^^ b.val.toUInt8))
      | _, _ => throwErr "u8Xor: expected field values"
  | .u8Add t1 t2 => do
      match (← interp decls bindings t1), (← interp decls bindings t2) with
      | .field a, .field b =>
          let x        := a.val.toUInt8.toNat + b.val.toUInt8.toNat
          let sum      : Value := .field (G.ofUInt8 x.toUInt8)
          let overflow : Value := .field (if x >= 256 then 1 else 0)
          return .tuple #[sum, overflow]
      | _, _ => throwErr "u8Add: expected field values"
  | .u8Sub t1 t2 => do
      match (← interp decls bindings t1), (← interp decls bindings t2) with
      | .field a, .field b =>
          let i := a.val.toUInt8
          let j := b.val.toUInt8
          return .tuple #[.field (G.ofUInt8 (i - j)), .field (if j > i then 1 else 0)]
      | _, _ => throwErr "u8Sub: expected field values"
  | .u8And t1 t2 => do
      match (← interp decls bindings t1), (← interp decls bindings t2) with
      | .field a, .field b => return .field (G.ofUInt8 (a.val.toUInt8 &&& b.val.toUInt8))
      | _, _ => throwErr "u8And: expected field values"
  | .u8Or t1 t2 => do
      match (← interp decls bindings t1), (← interp decls bindings t2) with
      | .field a, .field b => return .field (G.ofUInt8 (a.val.toUInt8 ||| b.val.toUInt8))
      | _, _ => throwErr "u8Or: expected field values"
  | .u8LessThan t1 t2 => do
      match (← interp decls bindings t1), (← interp decls bindings t2) with
      | .field a, .field b => return .field (if a.val.toUInt8 < b.val.toUInt8 then 1 else 0)
      | _, _ => throwErr "u8LessThan: expected field values"
  | .u32LessThan t1 t2 => do
      match (← interp decls bindings t1), (← interp decls bindings t2) with
      | .field a, .field b =>
          return .field (if a.val.toUInt32 < b.val.toUInt32 then 1 else 0)
      | _, _ => throwErr "u32LessThan: expected field values"
  | .debug label optT cont => do
      match optT with
      | none   => dbg_trace s!"{label}"
      | some t =>
        let v ← interp decls bindings t
        dbg_trace s!"{label}: {v}"
      interp decls bindings cont
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
      let io ← getIOBuffer
      if io.map.contains keyGs then
        throwErr s!"ioSetInfo: key already set"
      let info : IOKeyInfo := ⟨idxVal.val.toNat, lenVal.val.toNat⟩
      modifyIOBuffer fun io => { io with map := io.map.insert keyGs info }
      interp decls bindings ret
  | .ioRead idx len => do
      let idxVal ← expectField (← interp decls bindings idx)
      let io ← getIOBuffer
      let start := idxVal.val.toNat
      if start + len > io.data.size then
        throwErr s!"ioRead: out-of-bounds read at {start} for length {len} \
                   (buffer size {io.data.size})"
      return .array (io.data.extract start (start + len) |>.map .field)
  | .ioWrite data ret => do
      let dataGs ← expectFieldArray (← interp decls bindings data)
      modifyIOBuffer fun io => { io with data := io.data ++ dataGs }
      interp decls bindings ret

end

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
  StateT.run (interp decls bindings f.body) { ioBuffer }

end Aiur

end
