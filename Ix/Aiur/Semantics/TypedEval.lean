module
public import Ix.Aiur.Stages.Typed
public import Ix.Aiur.Semantics.SourceEval

/-!
Typed-form reference evaluator — proof-bearing semantics on `Typed.Term`.

Mirrors `Ix/Aiur/Source/Eval.lean` structurally. Values are type-erased: we
reuse `Source.Value` directly (types don't affect value-level dynamics), so a
Typed eval outputs `Source.Value`. The `typ`/`escapes` fields on every
`Typed.Term` constructor are ignored here, as are `tArgs` (on `.ref`/`.app`)
and the `unconstrained` flag on `.app` — all purely type-level metadata.

Pattern-matching helpers (`matchPattern`, `matchPatsList`, `matchPatsArr`) are
reused verbatim from `Source.Eval` since `Typed.Term` still carries
`Source.Pattern`. Likewise the `SourceError`, `Bindings`, `Store`, `EvalState`,
and `EvalResult` scaffolding is imported directly from `Source.Eval`.
-/

public section
@[expose] section

namespace Aiur

namespace Typed.Eval

open Source.Eval (SourceError Bindings Store EvalState EvalResult matchPattern)

/-- Typed-level value flat width — mirrors `Source.flattenValue`'s output size
on `Typed.Decls`. Used by `.store` for width-bucketing (matches Rust
`src/aiur/execute.rs` semantics). -/
def valueFlatWidth (decls : Typed.Decls) : Value → Nat
  | .unit => 0
  | .field _ => 1
  | .pointer _ _ => 1
  | .fn _ => 1
  | .tuple vs => vs.attach.foldl (fun acc ⟨v, _⟩ => acc + valueFlatWidth decls v) 0
  | .array vs => vs.attach.foldl (fun acc ⟨v, _⟩ => acc + valueFlatWidth decls v) 0
  | .ctor g args =>
    match decls.getByKey g with
    | some (.constructor dt _) =>
      let ctorSizes := dt.constructors.map fun c =>
        c.argTypes.foldl (fun acc _ => acc + 1) 0  -- placeholder: per-ctor arg count
      1 + ctorSizes.foldl max 0
    | _ => args.attach.foldl (fun acc ⟨v, _⟩ => acc + valueFlatWidth decls v) 0
termination_by v => sizeOf v

def expectFieldArray (vs : Array Value) : Option (Array G) :=
  vs.foldlM (init := #[]) fun acc v =>
    match v with
    | .field g => some (acc.push g)
    | _        => none

/-! ## Evaluator -/

def tryLocalLookup (g : Global) (bindings : Bindings) : Option Value :=
  match g.toName with
  | .str .anonymous name => bindings.find? (·.1 == Local.str name) |>.map (·.2)
  | _                    => none

@[inline] def combineFieldsResult
    (k : G → G → Value)
    (r1 : EvalResult) (r2 : EvalState → EvalResult) : EvalResult :=
  match r1 with
  | .error e => .error e
  | .ok (v1, st1) =>
    match r2 st1 with
    | .error e => .error e
    | .ok (v2, st2) =>
      match v1, v2 with
      | .field a, .field b => .ok (k a b, st2)
      | _, _ => .error (.typeMismatch "bin field")

mutual

/-- Apply a globally-named function or constructor. Decrements `fuel`. -/
partial def applyGlobal (decls : Typed.Decls) (fuel : Nat) (g : Global)
    (args : List Value) (st : EvalState) : EvalResult :=
  match fuel with
  | 0 => .error .outOfFuel
  | fuel+1 =>
    match decls.getByKey g with
    | some (.function f) =>
        if args.length != f.inputs.length then .error (.arityMismatch g)
        else
          let bindings := f.inputs.map (·.1) |>.zip args
          match interp decls fuel bindings f.body st with
          | .error e => .error e
          | .ok (v, st') => .ok (v, st')
    | some (.constructor _ _) => .ok (.ctor g args.toArray, st)
    | none                    => .error (.unboundGlobal g)
    | some (.dataType _)      => .error (.notCallable g)

partial def applyLocal (decls : Typed.Decls) (fuel : Nat) (v : Value)
    (args : List Value) (st : EvalState) : EvalResult :=
  match v with
  | .fn g => applyGlobal decls fuel g args st
  | _     => .error .notAFunctionValue

/-- Big-step evaluator on `Typed.Term`. Ignores `typ`, `escapes`, `tArgs`, and
the `unconstrained` flag — these are type-level metadata with no value-level
effect. -/
partial def interp (decls : Typed.Decls) (fuel : Nat) (bindings : Bindings)
    (t : Typed.Term) (st : EvalState) : EvalResult :=
  match t with
  | .unit _ _ => .ok (.unit, st)
  | .var _ _ l =>
    match bindings.find? (·.1 == l) with
    | some (_, v) => .ok (v, st)
    | none        => .error (.unboundVar l)
  | .ref _ _ g _ =>
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
  | .ret _ _ sub =>
      interp decls fuel bindings sub st
  | .let _ _ p t1 t2 =>
      match interp decls fuel bindings t1 st with
      | .error e => .error e
      | .ok (v, st') =>
        match matchPattern st'.store p v with
        | some bs => interp decls fuel (bs ++ bindings) t2 st'
        | none    => .error .patternFail
  | .match _ _ t cases =>
      match interp decls fuel bindings t st with
      | .error e => .error e
      | .ok (v, st') =>
        evalMatchCases decls fuel bindings st' v cases
  | .app _ _ g _ args _ =>
      match evalList decls fuel bindings args st with
      | .error e => .error e
      | .ok (vs, st') =>
        match tryLocalLookup g bindings with
        | some v => applyLocal decls fuel v vs.toList st'
        | none   => applyGlobal decls fuel g vs.toList st'
  | .add _ _ t1 t2 =>
      match interp decls fuel bindings t1 st with
      | .error e => .error e
      | .ok (v1, st1) =>
        match interp decls fuel bindings t2 st1 with
        | .error e => .error e
        | .ok (v2, st2) =>
          match v1, v2 with
          | .field a, .field b => .ok (.field (a + b), st2)
          | _, _ => .error (.typeMismatch "add")
  | .sub _ _ t1 t2 =>
      match interp decls fuel bindings t1 st with
      | .error e => .error e
      | .ok (v1, st1) =>
        match interp decls fuel bindings t2 st1 with
        | .error e => .error e
        | .ok (v2, st2) =>
          match v1, v2 with
          | .field a, .field b => .ok (.field (a - b), st2)
          | _, _ => .error (.typeMismatch "sub")
  | .mul _ _ t1 t2 =>
      match interp decls fuel bindings t1 st with
      | .error e => .error e
      | .ok (v1, st1) =>
        match interp decls fuel bindings t2 st1 with
        | .error e => .error e
        | .ok (v2, st2) =>
          match v1, v2 with
          | .field a, .field b => .ok (.field (a * b), st2)
          | _, _ => .error (.typeMismatch "mul")
  | .eqZero _ _ t =>
      match interp decls fuel bindings t st with
      | .error e => .error e
      | .ok (v, st') =>
        match v with
        | .field g => .ok (.field (if g.val == 0 then 1 else 0), st')
        | _        => .error (.typeMismatch "eqZero")
  | .proj _ _ t n =>
      match interp decls fuel bindings t st with
      | .error e => .error e
      | .ok (v, st') =>
        match v with
        | .tuple vs =>
          if h : n < vs.size then .ok (vs[n], st')
          else .error (.indexOoB n)
        | _ => .error (.typeMismatch "proj")
  | .get _ _ t n =>
      match interp decls fuel bindings t st with
      | .error e => .error e
      | .ok (v, st') =>
        match v with
        | .array vs =>
          if h : n < vs.size then .ok (vs[n], st')
          else .error (.indexOoB n)
        | _ => .error (.typeMismatch "get")
  | .slice _ _ t i j =>
      match interp decls fuel bindings t st with
      | .error e => .error e
      | .ok (v, st') =>
        match v with
        | .array vs => .ok (.array (vs.extract i j), st')
        | _         => .error (.typeMismatch "slice")
  | .set _ _ t n vT =>
      match interp decls fuel bindings vT st with
      | .error e => .error e
      | .ok (val, st1) =>
        match interp decls fuel bindings t st1 with
        | .error e => .error e
        | .ok (arr, st2) =>
          match arr with
          | .array vs =>
            if n < vs.size then .ok (.array (vs.set! n val), st2)
            else .error (.indexOoB n)
          | _ => .error (.typeMismatch "set")
  | .store _ _ t =>
      match interp decls fuel bindings t st with
      | .error e => .error e
      | .ok (v, st') =>
        -- Typed.Eval uses Typed.Decls (no `flattenValue` variant defined for it
        -- yet). Compute width structurally via a value-shape helper matching
        -- Source.Eval's Rust-aligned width-bucketed semantics.
        let w := valueFlatWidth decls v
        let inner := st'.store[w]?.getD (default : IndexMap (Array Value) Unit)
        if let some idx := inner.getIdxOf #[v] then
          .ok (.pointer w idx, st')
        else
          let idx := inner.size
          let inner' := inner.insert #[v] ()
          let st'' := { st' with store := st'.store.insert w inner' }
          .ok (.pointer w idx, st'')
  | .load _ _ t =>
      match interp decls fuel bindings t st with
      | .error e => .error e
      | .ok (v, st') =>
        match v with
        | .pointer w n =>
          match st'.store[w]? with
          | some inner =>
            match inner.getByIdx n with
            | some (vs, _) => .ok (vs[0]!, st')
            | none         => .error (.invalidPointer n)
          | none => .error (.invalidPointer n)
        | _ => .error (.typeMismatch "load")
  | .ptrVal _ _ t =>
      match interp decls fuel bindings t st with
      | .error e => .error e
      | .ok (v, st') =>
        match v with
        | .pointer _ n => .ok (.field (G.ofNat n), st')
        | _            => .error (.typeMismatch "ptrVal")
  | .assertEq _ _ t1 t2 ret =>
      match interp decls fuel bindings t1 st with
      | .error e => .error e
      | .ok (v1, st1) =>
        match interp decls fuel bindings t2 st1 with
        | .error e => .error e
        | .ok (v2, st2) =>
          if v1 != v2 then .error (.typeMismatch "assertEq")
          else interp decls fuel bindings ret st2
  | .u8BitDecomposition _ _ t =>
      match interp decls fuel bindings t st with
      | .error e => .error e
      | .ok (v, st') =>
        match v with
        | .field g =>
          let byte := g.val.toUInt8
          .ok (.array (Array.ofFn fun (i : Fin 8) =>
            .field (G.ofUInt8 ((byte >>> i.val.toUInt8) &&& 1))), st')
        | _ => .error (.typeMismatch "u8BitDecomposition")
  | .u8ShiftLeft _ _ t =>
      match interp decls fuel bindings t st with
      | .error e => .error e
      | .ok (v, st') =>
        match v with
        | .field g => .ok (.field (G.ofUInt8 (g.val.toUInt8 <<< 1)), st')
        | _        => .error (.typeMismatch "u8ShiftLeft")
  | .u8ShiftRight _ _ t =>
      match interp decls fuel bindings t st with
      | .error e => .error e
      | .ok (v, st') =>
        match v with
        | .field g => .ok (.field (G.ofUInt8 (g.val.toUInt8 >>> 1)), st')
        | _        => .error (.typeMismatch "u8ShiftRight")
  | .u8Xor _ _ t1 t2 =>
      combineFieldsResult (fun a b => .field (G.ofUInt8 (a.val.toUInt8 ^^^ b.val.toUInt8)))
        (interp decls fuel bindings t1 st)
        (fun st1 => interp decls fuel bindings t2 st1)
  | .u8Add _ _ t1 t2 =>
      combineFieldsResult
        (fun a b =>
          let x := a.val.toUInt8.toNat + b.val.toUInt8.toNat
          .tuple #[.field (G.ofUInt8 x.toUInt8),
                   .field (if x >= 256 then 1 else 0)])
        (interp decls fuel bindings t1 st)
        (fun st1 => interp decls fuel bindings t2 st1)
  | .u8Sub _ _ t1 t2 =>
      combineFieldsResult
        (fun a b =>
          let i := a.val.toUInt8; let j := b.val.toUInt8
          .tuple #[.field (G.ofUInt8 (i - j)), .field (if j > i then 1 else 0)])
        (interp decls fuel bindings t1 st)
        (fun st1 => interp decls fuel bindings t2 st1)
  | .u8And _ _ t1 t2 =>
      combineFieldsResult (fun a b => .field (G.ofUInt8 (a.val.toUInt8 &&& b.val.toUInt8)))
        (interp decls fuel bindings t1 st)
        (fun st1 => interp decls fuel bindings t2 st1)
  | .u8Or _ _ t1 t2 =>
      combineFieldsResult (fun a b => .field (G.ofUInt8 (a.val.toUInt8 ||| b.val.toUInt8)))
        (interp decls fuel bindings t1 st)
        (fun st1 => interp decls fuel bindings t2 st1)
  | .u8LessThan _ _ t1 t2 =>
      combineFieldsResult (fun a b => .field (if a.val.toUInt8 < b.val.toUInt8 then 1 else 0))
        (interp decls fuel bindings t1 st)
        (fun st1 => interp decls fuel bindings t2 st1)
  | .u32LessThan _ _ t1 t2 =>
      combineFieldsResult (fun a b => .field (if a.val.toUInt32 < b.val.toUInt32 then 1 else 0))
        (interp decls fuel bindings t1 st)
        (fun st1 => interp decls fuel bindings t2 st1)
  | .debug _ _ _ _ ret => interp decls fuel bindings ret st
  | .ioGetInfo _ _ key =>
      match interp decls fuel bindings key st with
      | .error e => .error e
      | .ok (v, st') =>
        match v with
        | .array vs =>
          match expectFieldArray vs with
          | none      => .error (.typeMismatch "ioGetInfo key")
          | some keyGs =>
            match st'.ioBuffer.map[keyGs]? with
            | some info =>
              .ok (.tuple #[.field (.ofNat info.idx), .field (.ofNat info.len)], st')
            | none => .error .ioKeyNotFound
        | _ => .error (.typeMismatch "ioGetInfo")
  | .ioSetInfo _ _ key idx len ret =>
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
            if stl.ioBuffer.map.contains keyGs then
              .error .ioKeyAlreadySet
            else
              let info : IOKeyInfo := ⟨iG.val.toNat, lG.val.toNat⟩
              let st' := { stl with ioBuffer :=
                { stl.ioBuffer with map := stl.ioBuffer.map.insert keyGs info } }
              interp decls fuel bindings ret st'
        | _, _, _ => .error (.typeMismatch "ioSetInfo")
  | .ioRead _ _ idx len =>
      match interp decls fuel bindings idx st with
      | .error e => .error e
      | .ok (v, st') =>
        match v with
        | .field g =>
          let start := g.val.toNat
          if start + len > st'.ioBuffer.data.size then .error .ioReadOoB
          else .ok (.array (st'.ioBuffer.data.extract start (start + len) |>.map .field), st')
        | _ => .error (.typeMismatch "ioRead")
  | .ioWrite _ _ data ret =>
      match interp decls fuel bindings data st with
      | .error e => .error e
      | .ok (v, st') =>
        match v with
        | .array vs =>
          match expectFieldArray vs with
          | none       => .error (.typeMismatch "ioWrite")
          | some dataGs =>
            let st'' := { st' with ioBuffer :=
              { st'.ioBuffer with data := st'.ioBuffer.data ++ dataGs } }
            interp decls fuel bindings ret st''
        | _ => .error (.typeMismatch "ioWrite")

/-- Structurally-recursive `match` arm dispatcher. -/
partial def evalMatchCases (decls : Typed.Decls) (fuel : Nat) (bindings : Bindings)
    (st : EvalState) (v : Value) :
    List (Pattern × Typed.Term) → EvalResult
  | [] => .error .nonExhaustiveMatch
  | (p, body) :: rest =>
    match matchPattern st.store p v with
    | some bs => interp decls fuel (bs ++ bindings) body st
    | none    => evalMatchCases decls fuel bindings st v rest

partial def evalList (decls : Typed.Decls) (fuel : Nat) (bindings : Bindings)
    : List Typed.Term → EvalState → Except SourceError (Array Value × EvalState)
  | [], st => .ok (#[], st)
  | t :: ts, st =>
    match interp decls fuel bindings t st with
    | .error e => .error e
    | .ok (v, st') =>
      match evalList decls fuel bindings ts st' with
      | .error e => .error e
      | .ok (vs, st'') => .ok (#[v] ++ vs, st'')

end

/-! ## Top-level entry -/

/-- Run a named function with the given input values, under fuel. -/
def runFunction (decls : Typed.Decls) (funcName : Global) (inputs : List Value)
    (ioBuffer : IOBuffer := default) (fuel : Nat) :
    Except SourceError (Value × IOBuffer) :=
  let st : EvalState := { ioBuffer }
  match applyGlobal decls fuel funcName inputs st with
  | .error e => .error e
  | .ok (v, st') => .ok (v, st'.ioBuffer)

end Typed.Eval

end Aiur

end -- @[expose] section
end
