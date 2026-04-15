module
public import Ix.Aiur.Stages.Source
public import Ix.Aiur.Semantics.Flatten
public import Ix.Aiur.Protocol

/-!
Source-form reference evaluator — proof-bearing semantics on `Source.Term`.

Design:
- **No cache.** The cache is a debug-interpreter optimization (`Ix/Aiur/Interpret.lean`)
  and a Rust trace-multiplicity device, not part of the semantic model.
- **No stack trace.** Errors are tagged; debugging is the debug interpreter's job.
- **Fuel-indexed, call-only accounting.** `fuel : Nat` decrements only at `applyGlobal`.
  Intra-body recursion is structural.
- **Errors return, never panic.** `ioSetInfo` on existing key, `ioRead` OOB, pattern
  failure, type mismatch, etc. all produce `Except.error`.

This source-level evaluator does not yet distinguish pointer widths — source
pointers are a single global store. The width-bucketed `Concrete.Eval`
evaluator fixes that divergence with Rust.
-/

public section
@[expose] section

namespace Aiur

namespace Source.Eval

open Source

/-- Tagged errors — small enum, no messages, for use in proof statements. -/
inductive SourceError
  | outOfFuel
  | unboundVar (l : Local)
  | unboundGlobal (g : Global)
  | typeMismatch (ctx : String)
  | arityMismatch (g : Global)
  | indexOoB (n : Nat)
  | rangeOoB (i j : Nat)
  | patternFail
  | nonExhaustiveMatch
  | ioKeyAlreadySet
  | ioKeyNotFound
  | ioReadOoB
  | invalidPointer (n : Nat)
  | notCallable (g : Global)
  | notAFunctionValue
  deriving Repr, Inhabited

abbrev Bindings := List (Local × Value)
/-- Memory store, width-bucketed to match Rust `src/aiur/execute.rs`
`memory_queries: HashMap<size, IndexMap<Vec<G>, QueryResult>>`. Each width
has its own `IndexMap`; `ptrVal` returns the local index within its width's
bucket. Distinct-width pointers may share the same local index. -/
abbrev Store    := Std.HashMap Nat (IndexMap (Array Value) Unit)

structure EvalState where
  store    : Store := {}
  ioBuffer : IOBuffer
  deriving Inhabited

/-- Result of evaluation: either a successful value+state pair, or an error. -/
abbrev EvalResult := Except SourceError (Value × EvalState)

/-! ## Pattern matching (pure, reads store for pointer dereference) -/

mutual

def matchPattern (store : Store) :
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
  | .pointer p,   .pointer w n =>
      match store[w]? with
      | some inner =>
        match inner.getByIdx n with
        | some (vs, _) => vs[0]?.bind (matchPattern store p ·)
        | none         => none
      | none => none
  | _,            _           => none

def matchPatsList (store : Store) :
    List Pattern → List Value → Option Bindings
  | [],      []      => some []
  | p :: ps, v :: vs => do
      let b1 ← matchPattern store p v
      let b2 ← matchPatsList store ps vs
      return b1 ++ b2
  | _,       _       => none

def matchPatsArr (store : Store)
    (pats : Array Pattern) (vs : Array Value) : Option Bindings :=
  matchPatsList store pats.toList vs.toList

end

def expectFieldArray (vs : Array Value) : Option (Array G) :=
  vs.foldlM (init := #[]) fun acc v =>
    match v with
    | .field g => some (acc.push g)
    | _        => none

/-! ## Evaluator

`fuel : Nat` decrements only on `applyGlobal`. Intra-body recursion is structural.
-/

def tryLocalLookup (g : Global) (bindings : Bindings) : Option Value :=
  match g.toName with
  | .str .anonymous name => bindings.find? (·.1 == Local.str name) |>.map (·.2)
  | _                    => none

/-- Array's `sizeOf` strictly exceeds its `toList`'s `sizeOf`. Used in
termination proofs that go from `interp .tuple ts` to `evalList ts.toList`. -/
private theorem sizeOf_toList_lt {α : Type} [SizeOf α] (a : Array α) :
    sizeOf a.toList < 1 + sizeOf a := by
  rcases a with ⟨l⟩
  show sizeOf l < 1 + (1 + sizeOf l)
  omega

/-- Combine two pre-computed `interp` results into a binary field-arithmetic
op. Defined outside the mutual block so it bears no termination obligation —
the `interp` calls have already happened by the time this runs, supplied as
`r1 : EvalResult` and `r2 : EvalState → EvalResult` arguments. This replaces
a former `evalBinField` mutual member that introduced cross-function
termination headaches. -/
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

/-- Apply a globally-named function or constructor. Decrements `fuel`; returns
`.outOfFuel` when exhausted. -/
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
          match interp decls fuel bindings f.body st with
          | .error e => .error e
          | .ok (v, st') => .ok (v, st')
    | some (.constructor _ _) => .ok (.ctor g args.toArray, st)
    | none                    => .error (.unboundGlobal g)
    | some (.dataType _)      => .error (.notCallable g)
termination_by (fuel, 0, 0)

def applyLocal (decls : Decls) (fuel : Nat) (v : Value) (args : List Value)
    (st : EvalState) : EvalResult :=
  match v with
  | .fn g => applyGlobal decls fuel g args st
  | _     => .error .notAFunctionValue
termination_by (fuel, 1, 0)

/-- Big-step evaluator on `Source.Term`. `fuel` is only consumed at function-call
boundaries; the intra-body recursion here is structural. On a `.ret`, the return
value escapes via a bespoke path that the caller unwraps — implemented here as
a sentinel pattern in the `Except` result. -/
def interp (decls : Decls) (fuel : Nat) (bindings : Bindings)
    (t : Term) (st : EvalState) : EvalResult :=
  match t with
  | .unit => .ok (.unit, st)
  | .var l =>
    match bindings.find? (·.1 == l) with
    | some (_, v) => .ok (v, st)
    | none        => .error (.unboundVar l)
  | .ref g =>
      match decls.getByKey g with
      | some (.function _)          => .ok (.fn g, st)
      | some (.constructor _ ctor)  =>
          if ctor.argTypes.isEmpty then .ok (.ctor g #[], st)
          else .error (.notCallable g)
      | some (.dataType _)          => .error (.notCallable g)
      | none                        => .error (.unboundGlobal g)
  | .field g  => .ok (.field g, st)
  | .tuple ts =>
      match evalList decls fuel bindings ts.toList st with
      | .error e => .error e
      | .ok (vs, st') => .ok (.tuple vs, st')
  | .array ts =>
      match evalList decls fuel bindings ts.toList st with
      | .error e => .error e
      | .ok (vs, st') => .ok (.array vs, st')
  | .ann _ t => interp decls fuel bindings t st
  | .ret sub =>
      -- Explicit returns only appear inside function bodies; the body recursion
      -- here returns normally (the surrounding caller treats the full body value
      -- as the return value).
      interp decls fuel bindings sub st
  | .let p t1 t2 =>
      match interp decls fuel bindings t1 st with
      | .error e => .error e
      | .ok (v, st') =>
        match matchPattern st'.store p v with
        | some bs => interp decls fuel (bs ++ bindings) t2 st'
        | none    => .error .patternFail
  | .match t cases =>
      match interp decls fuel bindings t st with
      | .error e => .error e
      | .ok (v, st') =>
        evalMatchCases decls fuel bindings st' v cases
  | .app g args _ =>
      match evalList decls fuel bindings args st with
      | .error e => .error e
      | .ok (vs, st') =>
        match tryLocalLookup g bindings with
        | some v => applyLocal decls fuel v vs.toList st'
        | none   => applyGlobal decls fuel g vs.toList st'
  | .add t1 t2 =>
      match interp decls fuel bindings t1 st with
      | .error e => .error e
      | .ok (v1, st1) =>
        match interp decls fuel bindings t2 st1 with
        | .error e => .error e
        | .ok (v2, st2) =>
          match v1, v2 with
          | .field a, .field b => .ok (.field (a + b), st2)
          | _, _ => .error (.typeMismatch "add")
  | .sub t1 t2 =>
      match interp decls fuel bindings t1 st with
      | .error e => .error e
      | .ok (v1, st1) =>
        match interp decls fuel bindings t2 st1 with
        | .error e => .error e
        | .ok (v2, st2) =>
          match v1, v2 with
          | .field a, .field b => .ok (.field (a - b), st2)
          | _, _ => .error (.typeMismatch "sub")
  | .mul t1 t2 =>
      match interp decls fuel bindings t1 st with
      | .error e => .error e
      | .ok (v1, st1) =>
        match interp decls fuel bindings t2 st1 with
        | .error e => .error e
        | .ok (v2, st2) =>
          match v1, v2 with
          | .field a, .field b => .ok (.field (a * b), st2)
          | _, _ => .error (.typeMismatch "mul")
  | .eqZero t =>
      match interp decls fuel bindings t st with
      | .error e => .error e
      | .ok (v, st') =>
        match v with
        | .field g => .ok (.field (if g.val == 0 then 1 else 0), st')
        | _        => .error (.typeMismatch "eqZero")
  | .proj t n =>
      match interp decls fuel bindings t st with
      | .error e => .error e
      | .ok (v, st') =>
        match v with
        | .tuple vs =>
          if h : n < vs.size then .ok (vs[n], st')
          else .error (.indexOoB n)
        | _ => .error (.typeMismatch "proj")
  | .get t n =>
      match interp decls fuel bindings t st with
      | .error e => .error e
      | .ok (v, st') =>
        match v with
        | .array vs =>
          if h : n < vs.size then .ok (vs[n], st')
          else .error (.indexOoB n)
        | _ => .error (.typeMismatch "get")
  | .slice t i j =>
      match interp decls fuel bindings t st with
      | .error e => .error e
      | .ok (v, st') =>
        match v with
        | .array vs => .ok (.array (vs.extract i j), st')
        | _         => .error (.typeMismatch "slice")
  | .set t n vT =>
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
  | .store t =>
      match interp decls fuel bindings t st with
      | .error e => .error e
      | .ok (v, st') =>
        -- Width-bucketed store (matches Rust `src/aiur/execute.rs:173-191`).
        -- Width = flat size of the stored value (funcIdx-irrelevant for length).
        let w := (flattenValue decls (fun _ => none) v).size
        let inner := st'.store[w]?.getD (default : IndexMap (Array Value) Unit)
        if let some idx := inner.getIdxOf #[v] then
          .ok (.pointer w idx, st')
        else
          let idx := inner.size
          let inner' := inner.insert #[v] ()
          let st'' := { st' with store := st'.store.insert w inner' }
          .ok (.pointer w idx, st'')
  | .load t =>
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
  | .ptrVal t =>
      match interp decls fuel bindings t st with
      | .error e => .error e
      | .ok (v, st') =>
        match v with
        | .pointer _ n => .ok (.field (G.ofNat n), st')
        | _            => .error (.typeMismatch "ptrVal")
  | .assertEq t1 t2 ret =>
      match interp decls fuel bindings t1 st with
      | .error e => .error e
      | .ok (v1, st1) =>
        match interp decls fuel bindings t2 st1 with
        | .error e => .error e
        | .ok (v2, st2) =>
          if v1 != v2 then .error (.typeMismatch "assertEq")
          else interp decls fuel bindings ret st2
  | .u8BitDecomposition t =>
      match interp decls fuel bindings t st with
      | .error e => .error e
      | .ok (v, st') =>
        match v with
        | .field g =>
          let byte := g.val.toUInt8
          .ok (.array (Array.ofFn fun (i : Fin 8) =>
            .field (G.ofUInt8 ((byte >>> i.val.toUInt8) &&& 1))), st')
        | _ => .error (.typeMismatch "u8BitDecomposition")
  | .u8ShiftLeft t =>
      match interp decls fuel bindings t st with
      | .error e => .error e
      | .ok (v, st') =>
        match v with
        | .field g => .ok (.field (G.ofUInt8 (g.val.toUInt8 <<< 1)), st')
        | _        => .error (.typeMismatch "u8ShiftLeft")
  | .u8ShiftRight t =>
      match interp decls fuel bindings t st with
      | .error e => .error e
      | .ok (v, st') =>
        match v with
        | .field g => .ok (.field (G.ofUInt8 (g.val.toUInt8 >>> 1)), st')
        | _        => .error (.typeMismatch "u8ShiftRight")
  | .u8Xor t1 t2 =>
      combineFieldsResult (fun a b => .field (G.ofUInt8 (a.val.toUInt8 ^^^ b.val.toUInt8)))
        (interp decls fuel bindings t1 st)
        (fun st1 => interp decls fuel bindings t2 st1)
  | .u8Add t1 t2 =>
      combineFieldsResult
        (fun a b =>
          let x := a.val.toUInt8.toNat + b.val.toUInt8.toNat
          .tuple #[.field (G.ofUInt8 x.toUInt8),
                   .field (if x >= 256 then 1 else 0)])
        (interp decls fuel bindings t1 st)
        (fun st1 => interp decls fuel bindings t2 st1)
  | .u8Sub t1 t2 =>
      combineFieldsResult
        (fun a b =>
          let i := a.val.toUInt8; let j := b.val.toUInt8
          .tuple #[.field (G.ofUInt8 (i - j)), .field (if j > i then 1 else 0)])
        (interp decls fuel bindings t1 st)
        (fun st1 => interp decls fuel bindings t2 st1)
  | .u8And t1 t2 =>
      combineFieldsResult (fun a b => .field (G.ofUInt8 (a.val.toUInt8 &&& b.val.toUInt8)))
        (interp decls fuel bindings t1 st)
        (fun st1 => interp decls fuel bindings t2 st1)
  | .u8Or t1 t2 =>
      combineFieldsResult (fun a b => .field (G.ofUInt8 (a.val.toUInt8 ||| b.val.toUInt8)))
        (interp decls fuel bindings t1 st)
        (fun st1 => interp decls fuel bindings t2 st1)
  | .u8LessThan t1 t2 =>
      combineFieldsResult (fun a b => .field (if a.val.toUInt8 < b.val.toUInt8 then 1 else 0))
        (interp decls fuel bindings t1 st)
        (fun st1 => interp decls fuel bindings t2 st1)
  | .u32LessThan t1 t2 =>
      combineFieldsResult (fun a b => .field (if a.val.toUInt32 < b.val.toUInt32 then 1 else 0))
        (interp decls fuel bindings t1 st)
        (fun st1 => interp decls fuel bindings t2 st1)
  | .debug _ _ ret => interp decls fuel bindings ret st
  | .ioGetInfo key =>
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
  | .ioSetInfo key idx len ret =>
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
  | .ioRead idx len =>
      match interp decls fuel bindings idx st with
      | .error e => .error e
      | .ok (v, st') =>
        match v with
        | .field g =>
          let start := g.val.toNat
          if start + len > st'.ioBuffer.data.size then .error .ioReadOoB
          else .ok (.array (st'.ioBuffer.data.extract start (start + len) |>.map .field), st')
        | _ => .error (.typeMismatch "ioRead")
  | .ioWrite data ret =>
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
termination_by (fuel, 2, sizeOf t)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (apply Prod.Lex.right; apply Prod.Lex.right
       show sizeOf (Array.toList _) < _
       have h := sizeOf_toList_lt (α := Term)
       simp only [Term.tuple.sizeOf_spec, Term.array.sizeOf_spec]
       exact h _)

/-- Structurally-recursive `match` arm dispatcher. Walks `cases` and returns the
first arm that matches, evaluating its body. Splits out from `interp`'s `.match`
arm so termination is provable: each recursive `interp` call uses a `body`
that's structurally smaller than `cases` (via `List.sizeOf_lt_of_mem`). -/
def evalMatchCases (decls : Decls) (fuel : Nat) (bindings : Bindings)
    (st : EvalState) (v : Value) :
    List (Pattern × Term) → EvalResult
  | [] => .error .nonExhaustiveMatch
  | (p, body) :: rest =>
    match matchPattern st.store p v with
    | some bs => interp decls fuel (bs ++ bindings) body st
    | none    => evalMatchCases decls fuel bindings st v rest
termination_by cases => (fuel, 2, sizeOf cases)

def evalList (decls : Decls) (fuel : Nat) (bindings : Bindings)
    : List Term → EvalState → Except SourceError (Array Value × EvalState)
  | [], st => .ok (#[], st)
  | t :: ts, st =>
    match interp decls fuel bindings t st with
    | .error e => .error e
    | .ok (v, st') =>
      match evalList decls fuel bindings ts st' with
      | .error e => .error e
      | .ok (vs, st'') => .ok (#[v] ++ vs, st'')
termination_by ts _ => (fuel, 2, sizeOf ts)

end

/-! ## Top-level entry -/

/-- Run a named function with the given input values, under fuel. -/
def runFunction (decls : Decls) (funcName : Global) (inputs : List Value)
    (ioBuffer : IOBuffer := default) (fuel : Nat) :
    Except SourceError (Value × IOBuffer) :=
  let st : EvalState := { ioBuffer }
  match applyGlobal decls fuel funcName inputs st with
  | .error e => .error e
  | .ok (v, st') => .ok (v, st'.ioBuffer)

end Source.Eval

end Aiur

end -- @[expose] section
end
