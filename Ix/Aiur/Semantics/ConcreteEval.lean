module
public import Ix.Aiur.Stages.Concrete
public import Ix.Aiur.Semantics.Flatten
public import Ix.Aiur.Semantics.BytecodeFfi
public import Ix.Aiur.Semantics.SourceEval

/-!
Concrete-form reference evaluator — proof-bearing semantics on `Concrete.Term`.

Supersedes `Source.Eval` in the proof chain:
1. `Value.pointer (w, i)` carries width + index.
2. `Store : IndexMap Nat (IndexMap (Array G) Unit)` — per-width memory buckets
   matching Rust's `memory_queries`.
3. `.store t` computes the flat width of `t.typ` via `typFlatSize`, flattens
   `t`'s value, inserts into the right bucket.
4. `.load ptr` reads the width from the typed `.load` node, dispatches to the
   right bucket, unflattens via the element type.
5. Pointer numeric values on source and bytecode now agree.

`Concrete.Eval` and `Bytecode.Eval` produce identical `IOBuffer`s and
identical flat results on every program.
-/

public section
@[expose] section

namespace Aiur

namespace Concrete.Eval

/-- Reuse `Source.Eval.SourceError` since the error taxonomy is identical. -/
abbrev ConcreteError := Aiur.Source.Eval.SourceError

abbrev Bindings := List (Local × Value)

/-- Per-width memory bucket, matching Rust's `memory_queries`. -/
abbrev Store := IndexMap Nat (IndexMap (Array G) Unit)

structure EvalState where
  store    : Store := default
  ioBuffer : IOBuffer
  deriving Inhabited

abbrev EvalResult := Except ConcreteError (Value × EvalState)

/-! ## `Concrete.Typ` → outer `Typ` lift, for reusing `unflattenValue`. -/

def concreteTypToSource : Concrete.Typ → Aiur.Typ
  | .unit => .unit
  | .field => .field
  | .tuple ts => .tuple (ts.attach.map fun ⟨t, _⟩ => concreteTypToSource t)
  | .array t n => .array (concreteTypToSource t) n
  | .pointer t => .pointer (concreteTypToSource t)
  | .ref g => .ref g
  | .function ins out =>
      .function (ins.attach.map fun ⟨t, _⟩ => concreteTypToSource t) (concreteTypToSource out)
termination_by t => sizeOf t

/-! ## Bucket-based memory ops -/

/-- Flatten a `Value` to `Array G` using the same flattening function used in
the relation, but specialized to concrete types (no `.mvar`). -/
def flattenForStore (v : Value) : Array G :=
  Aiur.flattenValue (default : Source.Decls) (fun _ => none) v

/-- Insert a flattened `Array G` into the right width bucket, returning index. -/
def storeInsert (st : EvalState) (gs : Array G) : EvalState × Nat :=
  let width := gs.size
  let bucket := st.store.getByKey width |>.getD default
  match bucket.getIdxOf gs with
  | some idx => (st, idx)
  | none =>
    let idx := bucket.size
    let newBucket := bucket.insert gs ()
    ({ st with store := st.store.insert width newBucket }, idx)

/-- Look up a width-`w` pointer at index `i`, returning the flat array. -/
def storeLookup (st : EvalState) (w i : Nat) : Option (Array G) := do
  let bucket ← st.store.getByKey w
  (← bucket.getByIdx i).1

/-! ## Pattern matching (with `letLoad` handling moved to the term level) -/

def matchPattern : Pattern → Value → Option Bindings
  | .wildcard,     _                 => some []
  | .field g,      .field g'         => if g == g' then some [] else none
  | .ref g vars,   .ctor g' vs       =>
      if g != g' then none
      else if vars.size != vs.size then none
      else
        let binds := vars.zip vs
        some binds.toList
  | .tuple vars,   .tuple vs         =>
      if vars.size != vs.size then none
      else some (vars.zip vs).toList
  | .array vars,   .array vs         =>
      if vars.size != vs.size then none
      else some (vars.zip vs).toList
  | _,             _                 => none

/-! ## Helpers -/

def tryLocalLookup (g : Global) (bindings : Bindings) : Option Value :=
  match g.toName with
  | .str .anonymous name => bindings.find? (·.1 == Local.str name) |>.map (·.2)
  | _                    => none

def expectFieldArray (vs : Array Value) : Option (Array G) :=
  vs.foldlM (init := #[]) fun acc v =>
    match v with
    | .field g => some (acc.push g)
    | _        => none

/-- `sizeOf ts.toList < 1 + sizeOf ts`. Helper for evaluator termination. -/
theorem sizeOf_toList_lt {α : Type} [SizeOf α] (a : Array α) :
    sizeOf a.toList < 1 + sizeOf a := by
  rcases a with ⟨l⟩
  show sizeOf l < 1 + (1 + sizeOf l)
  omega

/-! ## Evaluator (total) -/

mutual

def applyGlobal (decls : Decls) (fuel : Nat) (g : Global) (args : List Value)
    (st : EvalState) : EvalResult :=
  match fuel with
  | 0 => .error .outOfFuel
  | fuel+1 =>
    match decls.getByKey g with
    | some (.function f) =>
      if args.length != f.inputs.length then .error (.arityMismatch g)
      else
        let bindings := f.inputs.map (·.1) |>.zip args
        interp decls fuel bindings f.body st
    | some (.constructor _ _) => .ok (.ctor g args.toArray, st)
    | none                    => .error (.unboundGlobal g)
    | some (.dataType _)      => .error (.notCallable g)
termination_by (fuel, 0, 0, 0)

def applyLocal (decls : Decls) (fuel : Nat) (v : Value) (args : List Value)
    (st : EvalState) : EvalResult :=
  match v with
  | .fn g => applyGlobal decls fuel g args st
  | _     => .error .notAFunctionValue
termination_by (fuel, 1, 0, 0)

def interp (decls : Decls) (fuel : Nat) (bindings : Bindings)
    (t : Term) (st : EvalState) : EvalResult :=
  match t with
  | .unit _ _ => .ok (.unit, st)
  | .var _ _ l =>
    match bindings.find? (·.1 == l) with
    | some (_, v) => .ok (v, st)
    | none        => .error (.unboundVar l)
  | .ref _ _ g =>
    match decls.getByKey g with
    | some (.function _)          => .ok (.fn g, st)
    | some (.constructor _ ctor)  =>
        if ctor.argTypes.isEmpty then .ok (.ctor g #[], st)
        else .error (.notCallable g)
    | some (.dataType _)          => .error (.notCallable g)
    | none                        => .error (.unboundGlobal g)
  | .field _ _ g => .ok (.field g, st)
  | .tuple _ _ ts =>
    match evalList decls fuel bindings ts.toList st with
    | .error e => .error e
    | .ok (vs, st') => .ok (.tuple vs, st')
  | .array _ _ ts =>
    match evalList decls fuel bindings ts.toList st with
    | .error e => .error e
    | .ok (vs, st') => .ok (.array vs, st')
  | .ret _ _ sub => interp decls fuel bindings sub st
  | .letVar _ _ l v b =>
    match interp decls fuel bindings v st with
    | .error e => .error e
    | .ok (val, st') => interp decls fuel ((l, val) :: bindings) b st'
  | .letWild _ _ v b =>
    match interp decls fuel bindings v st with
    | .error e => .error e
    | .ok (_, st') => interp decls fuel bindings b st'
  | .letLoad _ _ dst dstTyp src b =>
    match bindings.find? (·.1 == src) with
    | none => .error (.unboundVar src)
    | some (_, .pointer w i) =>
      match storeLookup st w i with
      | some gs =>
        let srcTyp := concreteTypToSource dstTyp
        let (stored, _) := unflattenValue (default : Source.Decls) gs 0 srcTyp
        interp decls fuel ((dst, stored) :: bindings) b st
      | none => .error (.invalidPointer i)
    | some _ => .error (.typeMismatch "letLoad src is not a pointer")
  | .match _ _ scrutIdx cases defaultOpt =>
    match bindings.find? (·.1 == scrutIdx) with
    | none => .error (.unboundVar scrutIdx)
    | some (_, scrut) =>
      evalMatchCases decls fuel bindings st scrut cases defaultOpt
  | .app _ _ g args _ =>
    match evalList decls fuel bindings args st with
    | .error e => .error e
    | .ok (vs, st') =>
      match tryLocalLookup g bindings with
      | some v => applyLocal decls fuel v vs.toList st'
      | none   => applyGlobal decls fuel g vs.toList st'
  | .add _ _ a b => evalBinField decls fuel bindings a b st fun x y => .field (x + y)
  | .sub _ _ a b => evalBinField decls fuel bindings a b st fun x y => .field (x - y)
  | .mul _ _ a b => evalBinField decls fuel bindings a b st fun x y => .field (x * y)
  | .eqZero _ _ a =>
    match interp decls fuel bindings a st with
    | .error e => .error e
    | .ok (.field g, st') => .ok (.field (if g.val == 0 then 1 else 0), st')
    | .ok _ => .error (.typeMismatch "eqZero")
  | .proj _ _ t n =>
    match interp decls fuel bindings t st with
    | .error e => .error e
    | .ok (.tuple vs, st') =>
      if h : n < vs.size then .ok (vs[n], st')
      else .error (.indexOoB n)
    | .ok _ => .error (.typeMismatch "proj")
  | .get _ _ t n =>
    match interp decls fuel bindings t st with
    | .error e => .error e
    | .ok (.array vs, st') =>
      if h : n < vs.size then .ok (vs[n], st')
      else .error (.indexOoB n)
    | .ok _ => .error (.typeMismatch "get")
  | .slice _ _ t i j =>
    match interp decls fuel bindings t st with
    | .error e => .error e
    | .ok (.array vs, st') => .ok (.array (vs.extract i j), st')
    | .ok _ => .error (.typeMismatch "slice")
  | .set _ _ t n vT =>
    match interp decls fuel bindings vT st with
    | .error e => .error e
    | .ok (val, st1) =>
      match interp decls fuel bindings t st1 with
      | .error e => .error e
      | .ok (.array vs, st2) =>
        if n < vs.size then .ok (.array (vs.set! n val), st2)
        else .error (.indexOoB n)
      | .ok _ => .error (.typeMismatch "set")
  | .store _ _ t =>
    match interp decls fuel bindings t st with
    | .error e => .error e
    | .ok (v, st') =>
      let gs := flattenForStore v
      let w := gs.size
      let (st'', idx) := storeInsert st' gs
      .ok (.pointer w idx, st'')
  | .load _ _ t =>
    match interp decls fuel bindings t st with
    | .error e => .error e
    | .ok (.pointer w i, st') =>
      match storeLookup st' w i with
      | some gs =>
        let srcTyp : Aiur.Typ := concreteTypToSource t.typ
        let eltTyp : Aiur.Typ := match srcTyp with
          | Aiur.Typ.pointer inner => inner
          | t' => t'
        let (v, _) := unflattenValue (default : Source.Decls) gs 0 eltTyp
        .ok (v, st')
      | none => .error (.invalidPointer i)
    | .ok _ => .error (.typeMismatch "load")
  | .ptrVal _ _ t =>
    match interp decls fuel bindings t st with
    | .error e => .error e
    | .ok (.pointer _ i, st') => .ok (.field (G.ofNat i), st')
    | .ok _ => .error (.typeMismatch "ptrVal")
  | .assertEq _ _ a b r =>
    match interp decls fuel bindings a st with
    | .error e => .error e
    | .ok (v1, st1) =>
      match interp decls fuel bindings b st1 with
      | .error e => .error e
      | .ok (v2, st2) =>
        if v1 != v2 then .error (.typeMismatch "assertEq")
        else interp decls fuel bindings r st2
  | .u8BitDecomposition _ _ t =>
    match interp decls fuel bindings t st with
    | .error e => .error e
    | .ok (.field g, st') =>
      let byte := g.val.toUInt8
      .ok (.array (Array.ofFn fun (i : Fin 8) =>
        .field (G.ofUInt8 ((byte >>> i.val.toUInt8) &&& 1))), st')
    | .ok _ => .error (.typeMismatch "u8BitDecomposition")
  | .u8ShiftLeft _ _ t =>
    match interp decls fuel bindings t st with
    | .error e => .error e
    | .ok (.field g, st') => .ok (.field (G.ofUInt8 (g.val.toUInt8 <<< 1)), st')
    | .ok _ => .error (.typeMismatch "u8ShiftLeft")
  | .u8ShiftRight _ _ t =>
    match interp decls fuel bindings t st with
    | .error e => .error e
    | .ok (.field g, st') => .ok (.field (G.ofUInt8 (g.val.toUInt8 >>> 1)), st')
    | .ok _ => .error (.typeMismatch "u8ShiftRight")
  | .u8Xor _ _ a b =>
    evalBinField decls fuel bindings a b st fun x y =>
      .field (G.ofUInt8 (x.val.toUInt8 ^^^ y.val.toUInt8))
  | .u8Add _ _ a b =>
    evalBinField decls fuel bindings a b st fun x y =>
      let sum := x.val.toUInt8.toNat + y.val.toUInt8.toNat
      .tuple #[.field (G.ofUInt8 sum.toUInt8),
               .field (if sum ≥ 256 then 1 else 0)]
  | .u8Sub _ _ a b =>
    evalBinField decls fuel bindings a b st fun x y =>
      let i := x.val.toUInt8; let j := y.val.toUInt8
      .tuple #[.field (G.ofUInt8 (i - j)), .field (if j > i then 1 else 0)]
  | .u8And _ _ a b =>
    evalBinField decls fuel bindings a b st fun x y =>
      .field (G.ofUInt8 (x.val.toUInt8 &&& y.val.toUInt8))
  | .u8Or _ _ a b =>
    evalBinField decls fuel bindings a b st fun x y =>
      .field (G.ofUInt8 (x.val.toUInt8 ||| y.val.toUInt8))
  | .u8LessThan _ _ a b =>
    evalBinField decls fuel bindings a b st fun x y =>
      .field (if x.val.toUInt8 < y.val.toUInt8 then 1 else 0)
  | .u32LessThan _ _ a b =>
    evalBinField decls fuel bindings a b st fun x y =>
      .field (if x.val.toUInt32 < y.val.toUInt32 then 1 else 0)
  | .debug _ _ _ _ r => interp decls fuel bindings r st
  | .ioGetInfo _ _ key =>
    match interp decls fuel bindings key st with
    | .error e => .error e
    | .ok (.array vs, st') =>
      match expectFieldArray vs with
      | none       => .error (.typeMismatch "ioGetInfo key")
      | some keyGs =>
        match st'.ioBuffer.map[keyGs]? with
        | some info =>
          .ok (.tuple #[.field (.ofNat info.idx), .field (.ofNat info.len)], st')
        | none => .error .ioKeyNotFound
    | .ok _ => .error (.typeMismatch "ioGetInfo")
  | .ioSetInfo _ _ key idx len ret =>
    -- Eval all three args left-to-right, THEN pattern-match. Matches Source
    -- and Typed eval order; prevents side-effect short-circuit divergence.
    match interp decls fuel bindings key st with
    | .error e => .error e
    | .ok (vk, stk) =>
    match interp decls fuel bindings idx stk with
    | .error e => .error e
    | .ok (vi, sti) =>
    match interp decls fuel bindings len sti with
    | .error e => .error e
    | .ok (vl, stl) =>
      match vk, vi, vl with
      | .array vs, .field iG, .field lG =>
        match expectFieldArray vs with
        | none       => .error (.typeMismatch "ioSetInfo key")
        | some keyGs =>
          if stl.ioBuffer.map.contains keyGs then .error .ioKeyAlreadySet
          else
            let info : IOKeyInfo := ⟨iG.val.toNat, lG.val.toNat⟩
            let st' := { stl with ioBuffer :=
              { stl.ioBuffer with map := stl.ioBuffer.map.insert keyGs info } }
            interp decls fuel bindings ret st'
      | _, _, _ => .error (.typeMismatch "ioSetInfo")
  | .ioRead _ _ idx len =>
    match interp decls fuel bindings idx st with
    | .error e => .error e
    | .ok (.field g, st') =>
      let start := g.val.toNat
      if start + len > st'.ioBuffer.data.size then .error .ioReadOoB
      else .ok (.array (st'.ioBuffer.data.extract start (start + len) |>.map .field), st')
    | .ok _ => .error (.typeMismatch "ioRead")
  | .ioWrite _ _ data ret =>
    match interp decls fuel bindings data st with
    | .error e => .error e
    | .ok (.array vs, st') =>
      match expectFieldArray vs with
      | none       => .error (.typeMismatch "ioWrite")
      | some dataGs =>
        let st'' := { st' with ioBuffer :=
          { st'.ioBuffer with data := st'.ioBuffer.data ++ dataGs } }
        interp decls fuel bindings ret st''
    | .ok _ => .error (.typeMismatch "ioWrite")
termination_by (fuel, 2, sizeOf t, 0)
decreasing_by all_goals first | decreasing_tactic | grind [sizeOf_toList_lt]

/-- Structurally-recursive match-arm dispatcher. Index-based traversal makes
the per-step decreasing measure `cases.size - i` and the `Array.sizeOf_get`
lemma fire automatically when we recurse into `interp` on a case body. -/
def evalMatchCases (decls : Decls) (fuel : Nat) (bindings : Bindings)
    (st : EvalState) (scrut : Value)
    (cases : Array (Pattern × Term)) (defaultOpt : Option Term) (i : Nat := 0) :
    EvalResult :=
  if h : i < cases.size then
    match matchPattern cases[i].fst scrut with
    | some bs => interp decls fuel (bs ++ bindings) cases[i].snd st
    | none    => evalMatchCases decls fuel bindings st scrut cases defaultOpt (i + 1)
  else
    match defaultOpt with
    | some body => interp decls fuel bindings body st
    | none      => .error .nonExhaustiveMatch
termination_by (fuel, 2, sizeOf cases + sizeOf defaultOpt, cases.size - i)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have h := Array.sizeOf_get cases i ‹_›
       grind)

def evalList (decls : Decls) (fuel : Nat) (bindings : Bindings)
    : List Term → EvalState → Except ConcreteError (Array Value × EvalState)
  | [], st => .ok (#[], st)
  | t :: ts, st =>
    match interp decls fuel bindings t st with
    | .error e => .error e
    | .ok (v, st') =>
      match evalList decls fuel bindings ts st' with
      | .error e => .error e
      | .ok (vs, st'') => .ok (#[v] ++ vs, st'')
termination_by ts _ => (fuel, 2, sizeOf ts, 0)
decreasing_by all_goals decreasing_tactic

def evalBinField (decls : Decls) (fuel : Nat) (bindings : Bindings)
    (t1 t2 : Term) (st : EvalState) (k : G → G → Value) : EvalResult :=
  match interp decls fuel bindings t1 st with
  | .error e => .error e
  | .ok (v1, st1) =>
    match interp decls fuel bindings t2 st1 with
    | .error e => .error e
    | .ok (v2, st2) =>
      match v1, v2 with
      | .field a, .field b => .ok (k a b, st2)
      | _, _ => .error (.typeMismatch "bin field")
termination_by (fuel, 2, sizeOf t1 + sizeOf t2 + 1, 0)
decreasing_by all_goals first | decreasing_tactic | grind

end

/-! ## Top-level entry -/

def runFunction (decls : Decls) (funcName : Global) (inputs : List Value)
    (ioBuffer : IOBuffer := default) (fuel : Nat) :
    Except ConcreteError (Value × IOBuffer) :=
  let st : EvalState := { ioBuffer }
  match applyGlobal decls fuel funcName inputs st with
  | .error e => .error e
  | .ok (v, st') => .ok (v, st'.ioBuffer)

end Concrete.Eval

end Aiur

end -- @[expose] section
end
