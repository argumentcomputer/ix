/-
  Aiur bytecode → Rust source codegen.

  Next stage after `Bytecode`. Walks a `Bytecode.Toplevel` and emits one
  Rust fn per Aiur function:

  ```rust
  fn aiur_fn_N(
    inp: [G; INPUT_SIZE],
    record: &mut QueryRecord,
    io_buffer: &mut IOBuffer,
    unconstrained: bool,
  ) -> [G; OUTPUT_SIZE]
  ```

  `INPUT_SIZE = Function.layout.inputSize`. `OUTPUT_SIZE` derived from
  the function's `Ctrl.return` arms (Aiur fn layouts are fixed; all
  Returns within a fn agree).

  Architecture: build a structured Rust IR (`RustExpr` / `RustStmt` /
  `RustItem`) by walking the Bytecode, then format the IR to a single
  Rust source `String` at the end. No string interpolation during
  codegen — collect IR, dispatch to string late.

  # Correctness invariant

  Generated code MUST produce a `QueryRecord` indistinguishable from
  `crates/aiur/src/execute.rs`'s interpreter:

  - `function_queries[idx].insert(args, output, mult)` MUST happen on
    `Ctrl::Return` of the callee, AFTER the callee's body's inserts.
  - Cache-hit `multiplicity += G::ONE` MUST trigger iff
    `!unconstrained && !op_unconstrained` for `Op::Call`, and
    `!unconstrained` for `Op::Store` / `Op::Load`.
  - `memory_queries[size]` insertion order: each unique store gets a
    pointer = `memory_queries.len()` at that moment.
  - `bytes1_queries` / `bytes2_queries` updates from `U8*` ops in
    constrained mode, suppressed when `unconstrained == true`.
  - `io_buffer` ops preserve order.

  # `unconstrained` propagation

  `unconstrained: bool` is the fn-local flag. Once `true`, stays `true`.
  Each `Op::Call(callee, args, _, op_unconstrained)` invokes the callee
  with `unconstrained || op_unconstrained`.

  # Status

  Skeleton: Rust IR + formatter. A few Op variants (`Const`, `Add` /
  `Sub` / `Mul`, `EqZero`) emit faithful IR. `Ctrl::Return` + `Ctrl::Match`
  emit faithful IR.

  Remaining (mechanical fill-in following the same IR shape):
  - `Op::Call` cache-check via `ifLetSome` (needs IR extension)
  - `Op::Store` / `Op::Load` / `Op::AssertEq`
  - IO ops: `IOGetInfo`, `IOSetInfo`, `IORead`, `IOWrite`
  - Byte ops: all `U8*` + `U32LessThan` (gated on `unconstrained`)
  - `UnconstrainedBigUintDivMod`, `Debug`
  - `Ctrl::MatchContinue` + `Ctrl::Yield` (needs `BlockResult` enum)

  Parity test BEFORE wiring into the build: generate code for one small
  Aiur fn, run both backends on the same input, diff the resulting
  `QueryRecord` byte-for-byte. Diverging records ⇒ invalid witnesses
  ⇒ proving fails hard.
-/
module
public import Ix.Aiur.Stages.Bytecode

public section

namespace Aiur.Codegen

open Bytecode

/-! ## Rust IR -/

mutual

inductive RustExpr where
  /-- A bare identifier (e.g. `record`, `__args`). -/
  | var (name : String)
  /-- A literal emitted verbatim (numbers, strings, `true`, `false`). -/
  | lit (text : String)
  /-- Path: `G::ZERO`, `ExecError::MatchNoCase`, etc. -/
  | path (segments : Array String)
  /-- Function or method call: `callee(args)`. -/
  | call (callee : RustExpr) (args : Array RustExpr)
  /-- Indexed access: `arr[idx]`. -/
  | index (arr : RustExpr) (idx : RustExpr)
  /-- Field access: `e.field`. -/
  | field (e : RustExpr) (name : String)
  /-- Binary operator: `a op b`. The formatter parenthesises. -/
  | binop (op : String) (a b : RustExpr)
  /-- `*e`. -/
  | deref (e : RustExpr)
  /-- `&e`. -/
  | ref (e : RustExpr)
  /-- `vec![...]`, `[...]`, etc. — `macro!(args)`. -/
  | macroCall (name : String) (args : Array RustExpr)
  /-- A Rust array literal: `[a, b, c]`. -/
  | arrayLit (elems : Array RustExpr)
  /-- A labeled block expression: `'label: { stmts }`. Used by
      MatchContinue: case bodies `break 'label vec![...]` to bubble
      yielded values, the labeled block as a whole evaluates to the
      yielded `Vec<G>`. -/
  | labeledBlock (label : String) (stmts : Array RustStmt)
  deriving Inhabited

inductive RustStmt where
  /-- `let [mut] name [: ty] = expr;` -/
  | letStmt (isMut : Bool) (name : String) (ty : Option String) (val : RustExpr)
  /-- `*target += val;` (used for multiplicity bumps). -/
  | addAssign (target : RustExpr) (val : RustExpr)
  /-- `expr;` -/
  | exprStmt (e : RustExpr)
  /-- `return expr;` -/
  | returnStmt (e : RustExpr)
  /-- `if cond { thenStmts } else { elseStmts? }` -/
  | ifStmt (cond : RustExpr) (thenStmts : Array RustStmt) (elseStmts : Option (Array RustStmt))
  /-- `if let Some(binding) = scrut { thenStmts } else { elseStmts }` —
      the shape used for Aiur's memoization cache checks. -/
  | ifLetSome (binding : String) (scrut : RustExpr)
      (thenStmts : Array RustStmt) (elseStmts : Array RustStmt)
  /-- `match scrut { pats... }` -/
  | matchStmt (scrut : RustExpr) (arms : Array MatchArm)
  /-- A nested block `{ stmts }` for scoping. -/
  | block (stmts : Array RustStmt)
  /-- `break 'label expr;` — yield a value out of an enclosing
      labeledBlock. -/
  | breakWith (label : String) (e : RustExpr)
  deriving Inhabited

inductive MatchPat where
  | litU64 (n : Nat)
  | wildcard
  deriving Inhabited

structure MatchArm where
  pat : MatchPat
  body : Array RustStmt
  deriving Inhabited

end

/-- A generated top-level item. -/
inductive RustItem where
  /-- A constant: `const NAME: usize = value;` -/
  | constUsize (name : String) (value : Nat)
  /-- A function. -/
  | function (name : String) (params : Array (String × String))
      (returnTy : String) (body : Array RustStmt)
  /-- Raw text (prelude, enum decls, etc.). -/
  | raw (text : String)
  deriving Inhabited

/-! ## Pretty printer

    Indentation: 2 spaces per nesting level. Expressions render on one
    line; statements get their own line. Match arms are one block each.
-/

@[inline] def indent (n : Nat) : String :=
  String.ofList (List.replicate (n * 2) ' ')

def MatchPat.toStr : MatchPat → String
  | .litU64 n => s!"{n}u64"
  | .wildcard => "_"

mutual

partial def RustExpr.toStr : RustExpr → String
  | .var n => n
  | .lit t => t
  | .path segs => "::".intercalate segs.toList
  | .call c args =>
    let argList := ", ".intercalate (args.toList.map RustExpr.toStr)
    s!"{c.toStr}({argList})"
  | .index a i => s!"{a.toStr}[{i.toStr}]"
  | .field e n => s!"{e.toStr}.{n}"
  | .binop op a b => s!"({a.toStr} {op} {b.toStr})"
  | .deref e => s!"*{e.toStr}"
  | .ref e => s!"&{e.toStr}"
  | .macroCall n args =>
    let argList := ", ".intercalate (args.toList.map RustExpr.toStr)
    s!"{n}!({argList})"
  | .arrayLit elems =>
    let lb := "["
    let rb := "]"
    let elemList := ", ".intercalate (elems.toList.map RustExpr.toStr)
    s!"{lb}{elemList}{rb}"
  | .labeledBlock label stmts =>
    -- One-line approximation. Aiur case bodies are short enough.
    let body := stmts.toList.map (RustStmt.toStr 0) |>.foldl (· ++ ·) ""
    let lbrace := "{"
    let rbrace := "}"
    s!"'{label}: {lbrace} {body} {rbrace}"

partial def RustStmt.toStr (d : Nat) : RustStmt → String
  | .letStmt isMut name ty val =>
    let mutStr := if isMut then "mut " else ""
    let tyStr := match ty with | some t => s!": {t}" | none => ""
    s!"{indent d}let {mutStr}{name}{tyStr} = {val.toStr};\n"
  | .addAssign target val =>
    s!"{indent d}{target.toStr} += {val.toStr};\n"
  | .exprStmt e => s!"{indent d}{e.toStr};\n"
  | .returnStmt e => s!"{indent d}return {e.toStr};\n"
  | .ifLetSome binding scrut thenStmts elseStmts => Id.run do
    let lbrace := "{"
    let rbrace := "}"
    let mut o := s!"{indent d}if let Some({binding}) = {scrut.toStr} {lbrace}\n"
    o := o ++ stmtsToStr (d+1) thenStmts
    o := o ++ s!"{indent d}{rbrace} else {lbrace}\n"
    o := o ++ stmtsToStr (d+1) elseStmts
    o := o ++ s!"{indent d}{rbrace}\n"
    return o
  | .ifStmt cond thenStmts elseStmts? => Id.run do
    let lbrace := "{"
    let rbrace := "}"
    let mut o := s!"{indent d}if {cond.toStr} {lbrace}\n"
    o := o ++ stmtsToStr (d+1) thenStmts
    match elseStmts? with
    | some elseStmts =>
      o := o ++ s!"{indent d}{rbrace} else {lbrace}\n"
      o := o ++ stmtsToStr (d+1) elseStmts
      o := o ++ s!"{indent d}{rbrace}\n"
    | none =>
      o := o ++ s!"{indent d}{rbrace}\n"
    return o
  | .matchStmt scrut arms => Id.run do
    let lbrace := "{"
    let rbrace := "}"
    let mut o := s!"{indent d}match {scrut.toStr} {lbrace}\n"
    for arm in arms do
      o := o ++ s!"{indent (d+1)}{arm.pat.toStr} => {lbrace}\n"
      o := o ++ stmtsToStr (d+2) arm.body
      o := o ++ s!"{indent (d+1)}{rbrace},\n"
    o := o ++ s!"{indent d}{rbrace}\n"
    return o
  | .block stmts => Id.run do
    let lbrace := "{"
    let rbrace := "}"
    let mut o := s!"{indent d}{lbrace}\n"
    o := o ++ stmtsToStr (d+1) stmts
    o := o ++ s!"{indent d}{rbrace}\n"
    return o
  | .breakWith label e =>
    s!"{indent d}break '{label} {e.toStr};\n"

partial def stmtsToStr (d : Nat) (stmts : Array RustStmt) : String := Id.run do
  let mut o := ""
  for s in stmts do
    o := o ++ s.toStr d
  o

end

def RustItem.toStr : RustItem → String
  | .constUsize n v => s!"const {n}: usize = {v};\n"
  | .raw text => text
  | .function name params returnTy body => Id.run do
    let lbrace := "{"
    let rbrace := "}"
    let paramList := ",\n  ".intercalate
      (params.toList.map (fun (n, t) => s!"{n}: {t}"))
    let mut o := s!"fn {name}(\n  {paramList},\n) -> {returnTy} {lbrace}\n"
    o := o ++ stmtsToStr 1 body
    o := o ++ s!"{rbrace}\n\n"
    return o

/-! ## IR helper constructors -/

def gZero : RustExpr := .path #["G", "ZERO"]
def gOne : RustExpr := .path #["G", "ONE"]
def gFromU64 (n : Nat) : RustExpr := .call (.path #["G", "from_u64"]) #[.lit (toString n)]
def gFromBool (cond : RustExpr) : RustExpr := .call (.path #["G", "from_bool"]) #[cond]
def gFromUsize (n : RustExpr) : RustExpr := .call (.path #["G", "from_usize"]) #[n]

/-- Local variable for Aiur ValIdx `i` — `__v_{i}`. Replaces the
    interpreter's `map[i]` Vec lookup. -/
def valVar (i : Nat) : RustExpr := .var s!"__v_{i}"

/-- Emit a single-G let-binding for the next ValIdx slot. -/
def declVal (idx : Nat) (rhs : RustExpr) : RustStmt :=
  .letStmt false s!"__v_{idx}" (some "G") rhs

/-- The `[G; n]` array literal of `valVar` for `is`. -/
def argsAsArray (is : Array ValIdx) : RustExpr :=
  .arrayLit (is.map valVar)

/-- `record.function_queries[idx]` access. -/
def funQueriesAt (idx : Nat) : RustExpr :=
  .index (.field (.var "record") "function_queries") (.lit (toString idx))

/-- `record.memory_queries.get_mut(&SIZE)?` chain — used by Store/Load. -/
def memQueriesGetMut (size : Nat) : RustExpr :=
  .call (.field (.field (.var "record") "memory_queries") "get_mut")
    #[.ref (.lit (toString size))]

/-- `cond` Rust expression for `!unconstrained && !op_unconstrained` /
    `!unconstrained` etc. We emit as `lit` to avoid building elaborate
    AST for unary `!`. -/
def litBool (b : Bool) : RustExpr := .lit (if b then "true" else "false")

/-- `!unconstrained`. -/
def notUnconstrained : RustExpr := .lit "!unconstrained"

/-- `!unconstrained && !op_unconstrained` (or just `!unconstrained` when
    `op_unconstrained == false`). -/
def constrainedCond (opUn : Bool) : RustExpr :=
  if opUn then .lit "false" else notUnconstrained

/-- `unconstrained || op_unconstrained` for callee propagation. -/
def calleeUnconstrained (opUn : Bool) : RustExpr :=
  if opUn then .lit "true" else .var "unconstrained"

/-! ## Op emission

    Each emitted Op mirrors `crates/aiur/src/execute.rs`'s matching arm. The
    interpreter's `map: Vec<G>` is gone: every Aiur ValIdx becomes a
    real Rust local `__v_{i}: G`. Per-op output counts decide how many
    new locals each op allocates; the counter is threaded via
    `EmitM`.

    Multi-output ops emit consecutive let-bindings; helpers that need
    a Vec-shaped scratch (byte ops via `bytes{1,2}_execute`) build a
    small local Vec inside a sub-block and read outputs back out as
    G values.
-/

/-- How many ValIdx slots an Op consumes (i.e. how much it grows
    Aiur's value-stack). MUST match `execute.rs`'s `map.push` /
    `map.extend` totals exactly per arm — else local-variable names
    drift from the bytecode's expected ValIdx layout and subsequent
    ops index the wrong values. -/
def Op.outputCount : Op → Nat
  | .const _ => 1
  | .add _ _ | .sub _ _ | .mul _ _ | .eqZero _ => 1
  | .call _ _ outSize _ => outSize
  | .store _ => 1
  | .load size _ => size
  | .assertEq _ _ => 0
  | .ioGetInfo _ _ => 2
  | .ioSetInfo _ _ _ _ => 0
  | .ioRead _ _ len => len
  | .ioWrite _ _ => 0
  | .u8BitDecomposition _ => 8
  | .u8ShiftLeft _ | .u8ShiftRight _ => 1
  | .u8Xor _ _ | .u8And _ _ | .u8Or _ _ | .u8LessThan _ _ => 1
  | .u8Mul _ _ => 2
  | .u8Add _ _ | .u8Sub _ _ => 2
  | .u8ChainRotr7 _ _ | .u8ChainRotr4 _ _ => 3
  | .u32LessThan _ _ => 1
  | .u8RangeCheck _ _ => 0
  | .unconstrainedBigUintDivMod _ _ => 2
  | .debug _ _ => 0

private def emitConst (out : Nat) (c : Aiur.G) : Array RustStmt :=
  #[declVal out (gFromU64 c.n)]

private def emitBinop (out : Nat) (op : String) (a b : ValIdx) : Array RustStmt :=
  #[declVal out (.binop op (valVar a) (valVar b))]

private def emitEqZero (out : Nat) (a : ValIdx) : Array RustStmt :=
  #[declVal out (gFromBool (.binop "==" (valVar a) gZero))]

/-- `Op::Call`: mirror execute.rs lines 284-305 (caller) + 625-633
    (callee's Return inserts into `function_queries[fun_idx]`). On
    cache hit: bump multiplicity if both sides constrained, extend map
    with cached output. On miss: direct Rust call to the generated
    callee. -/
private def emitCall (out : Nat) (callee : FunIdx) (args : Array ValIdx)
    (outSize : Nat) (opUn : Bool) : Array RustStmt := Id.run do
  -- Build the inner cache-check as a Rust block expression (raw lit).
  -- Structured IR for if-let-as-expression would need a `blockExpr`
  -- node; deferred until after parity testing validates the shape.
  let argsStr : String := (argsAsArray args).toStr
  -- Constant-fold the `unconstrained || OP_UN` / `!unconstrained && !OP_UN`
  -- patterns based on the static `opUn` flag. When opUn = true the
  -- callee always runs unconstrained AND the multiplicity bump is
  -- always skipped; when opUn = false both expressions collapse to
  -- just `unconstrained`.
  let cuExpr : String := if opUn then "true" else "unconstrained"
  let bumpCond : String := if opUn then "false" else "!unconstrained"
  let bumpStmt : String :=
    if opUn then ""
    else s!" if {bumpCond} \{ *result.multiplicity += G::ONE; }"
  -- Skip `try_into().unwrap()` on the cache hit: we statically know
  -- the cached output has exactly `OUT_{callee}` elements (only we
  -- ever insert into this slot via the matching aiur_fn_{callee}
  -- `Ctrl::Return`). An unchecked array copy is sound.
  let retExpr : String :=
    s!" let __ret: [G; OUT_{callee}] = unsafe \{ *(result.output.as_ptr() as *const [G; OUT_{callee}]) }; __ret"
  let blockExpr : String :=
    s!"\{ let __args: [G; IN_{callee}] = {argsStr};" ++
    s!" let __cu = {cuExpr};" ++
    s!" if let Some(result) = record.function_queries[{callee}].get_mut(&__args[..]) \{" ++
    bumpStmt ++
    retExpr ++
    s!" } else \{ aiur_fn_{callee}(__args, record, io_buffer, __cu)? } }"
  let mut stmts : Array RustStmt := #[
    .letStmt false "__r_arr" (some s!"[G; OUT_{callee}]") (.lit blockExpr)
  ]
  for k in [0 : outSize] do
    stmts := stmts.push (declVal (out + k) (.index (.var "__r_arr") (.lit (toString k))))
  return stmts

/-- `Op::Store`: mirror execute.rs lines 306-326. Insert hit/miss into
    `record.memory_queries[size]`; output is the allocated/cached ptr. -/
private def emitStore (out : Nat) (values : Array ValIdx) : Array RustStmt :=
  let size := values.size
  let valsStr : String := (argsAsArray values).toStr
  let blockExpr : String :=
    s!"\{ let __values: [G; {size}] = {valsStr};" ++
    s!" let __mq = record.memory_queries.get_mut(&{size}).ok_or(ExecError::InvalidMemorySize({size}))?;" ++
    s!" if let Some(result) = __mq.get_mut(&__values[..]) \{" ++
    s!" if !unconstrained \{ *result.multiplicity += G::ONE; }" ++
    s!" result.output[0]" ++
    s!" } else \{" ++
    s!" let __ptr = G::from_usize(__mq.len());" ++
    s!" __mq.insert(&__values[..], &[__ptr], G::from_bool(!unconstrained)); __ptr } }"
  #[.letStmt false s!"__v_{out}" (some "G") (.lit blockExpr)]

/-- `Op::Load`: mirror execute.rs lines 328-345. Look up by pointer
    index, bump multiplicity if constrained, splat `size` outputs. -/
private def emitLoad (out : Nat) (size : Nat) (ptr : ValIdx) : Array RustStmt := Id.run do
  let blockExpr : String :=
    s!"\{ let __mq = record.memory_queries.get_mut(&{size}).ok_or(ExecError::InvalidMemorySize({size}))?;" ++
    s!" let __ptr_u64 = __v_{ptr}.as_canonical_u64();" ++
    s!" let __ptr_usize = usize::try_from(__ptr_u64).ok().ok_or(ExecError::PointerTooLarge(__ptr_u64))?;" ++
    s!" let (__args, __mult) = __mq.get_index_mut(__ptr_usize).ok_or(ExecError::UnboundPointer \{ ptr: __ptr_u64, size: {size} })?;" ++
    s!" if !unconstrained \{ *__mult += G::ONE; }" ++
    s!" let __arr: [G; {size}] = __args[..{size}].try_into().unwrap(); __arr }"
  let mut stmts : Array RustStmt := #[
    .letStmt false "__loaded" (some s!"[G; {size}]") (.lit blockExpr)
  ]
  for k in [0 : size] do
    stmts := stmts.push (declVal (out + k) (.index (.var "__loaded") (.lit (toString k))))
  return stmts

/-- `Op::AssertEq`: mirror execute.rs lines 346-363. -/
private def emitAssertEq (xs ys : Array ValIdx) : Array RustStmt :=
  if xs.size != ys.size then
    #[.exprStmt (.lit s!"return Err(ExecError::AssertEqLengthMismatch \{ lhs: {xs.size}, rhs: {ys.size} })")]
  else Id.run do
    let mut stmts : Array RustStmt := #[]
    for (x, y) in xs.zip ys do
      stmts := stmts.push (.ifStmt
        (.binop "!=" (valVar x) (valVar y))
        #[.exprStmt (.lit s!"return Err(ExecError::AssertEqMismatch \{ lhs: __v_{x}.as_canonical_u64(), rhs: __v_{y}.as_canonical_u64() })")]
        none)
    return stmts

/-! ### IO ops -/

/-- `Op::IOGetInfo`: pushes 2 outputs (idx, len). -/
private def emitIOGetInfo (out : Nat) (channel : ValIdx) (key : Array ValIdx) :
    Array RustStmt :=
  let keyStr := (argsAsArray key).toStr
  let blockIdxLen : String :=
    s!"\{ let __key: [G; {key.size}] = {keyStr};" ++
    s!" let __info = io_buffer.get_info(__v_{channel}, &__key[..])?;" ++
    s!" (G::from_usize(__info.idx), G::from_usize(__info.len)) }"
  #[
    .letStmt false "__io_pair" (some "(G, G)") (.lit blockIdxLen),
    declVal out (.field (.var "__io_pair") "0"),
    declVal (out + 1) (.field (.var "__io_pair") "1")
  ]

/-- `Op::IOSetInfo`: 0 outputs; side-effects io_buffer. -/
private def emitIOSetInfo (channel : ValIdx) (key : Array ValIdx)
    (idx len : ValIdx) : Array RustStmt :=
  let keyStr := (argsAsArray key).toStr
  let stmt : String :=
    s!"\{ let __key: [G; {key.size}] = {keyStr};" ++
    s!" let __idx = usize::try_from(__v_{idx}.as_canonical_u64()).ok().ok_or(ExecError::IndexTooLarge(__v_{idx}.as_canonical_u64()))?;" ++
    s!" let __len = usize::try_from(__v_{len}.as_canonical_u64()).ok().ok_or(ExecError::IndexTooLarge(__v_{len}.as_canonical_u64()))?;" ++
    s!" io_buffer.set_info(__v_{channel}, __key.to_vec(), __idx, __len)?; }"
  #[.exprStmt (.lit stmt)]

/-- `Op::IORead`: pushes `len` outputs (one G per byte). -/
private def emitIORead (out : Nat) (channel : ValIdx) (idx : ValIdx) (len : Nat) :
    Array RustStmt := Id.run do
  let blockExpr : String :=
    s!"\{ let __idx_u64 = __v_{idx}.as_canonical_u64();" ++
    s!" let __idx = usize::try_from(__idx_u64).ok().ok_or(ExecError::IndexTooLarge(__idx_u64))?;" ++
    s!" let __data = io_buffer.read(__v_{channel}, __idx, {len})?;" ++
    s!" let __arr: [G; {len}] = __data[..{len}].try_into().unwrap(); __arr }"
  let mut stmts : Array RustStmt := #[
    .letStmt false "__io_read" (some s!"[G; {len}]") (.lit blockExpr)
  ]
  for k in [0 : len] do
    stmts := stmts.push (declVal (out + k) (.index (.var "__io_read") (.lit (toString k))))
  return stmts

/-- `Op::IOWrite`: 0 outputs; side-effects io_buffer. -/
private def emitIOWrite (channel : ValIdx) (data : Array ValIdx) : Array RustStmt :=
  let dataIter : RustExpr :=
    .call (.field (.arrayLit (data.map valVar)) "into_iter") #[]
  #[.exprStmt
    (.call (.field (.var "io_buffer") "write")
      #[valVar channel, dataIter])]

/-! ### Byte ops

    All `U8*` ops are gated on `unconstrained`: in constrained mode
    they go through `bytes{1,2}_execute` helpers (which update
    `record.bytes{1,2}_queries`); in unconstrained mode they take a
    pure arithmetic shortcut and skip the byte-chip queries.

    For codegen simplicity, the constrained path is emitted as a raw
    helper call; the unconstrained shortcut is the pure variant of
    the same op. The execute.rs interpreter does the same dispatch.
-/

/-- Bytes1 op. No scratch Vec — the constrained branch calls
    `bytes1_*_value` (defined in `aiur::execute`) which
    bumps the byte-chip queries and returns the gadget output by
    value; the unconstrained branch calls the pure `Bytes1::*`
    helper directly. -/
private def emitU8Bytes1 (out : Nat) (valueHelper : String)
    (unconShortcut : String) (byte : ValIdx) (outCount : Nat) :
    Array RustStmt := Id.run do
  if outCount == 1 then
    let blockExpr : String :=
      s!"if unconstrained \{ {unconShortcut}(&__v_{byte}) }" ++
      s!" else \{ {valueHelper}(__v_{byte}, record) }"
    return #[.letStmt false s!"__v_{out}" (some "G") (.lit blockExpr)]
  else
    -- BitDecomposition returns [G; 8]; the unconstrained shortcut
    -- is the pure `Bytes1::bit_decompose` which returns Vec<G>.
    -- Coerce its result into [G; outCount] for unified handling.
    let blockExpr : String :=
      s!"if unconstrained \{ let __v: Vec<G> = {unconShortcut}(&__v_{byte}); let __a: [G; {outCount}] = __v.try_into().unwrap(); __a }" ++
      s!" else \{ {valueHelper}(__v_{byte}, record) }"
    let mut stmts : Array RustStmt := #[
      .letStmt false "__b1_out" (some s!"[G; {outCount}]") (.lit blockExpr)
    ]
    for k in [0 : outCount] do
      stmts := stmts.push (declVal (out + k) (.index (.var "__b1_out") (.lit (toString k))))
    return stmts

/-- Bytes2 op. Same pattern as `emitU8Bytes1` — no scratch Vec. -/
private def emitU8Bytes2 (out : Nat) (valueHelper : String)
    (unconShortcut : String) (i j : ValIdx) (outCount : Nat) :
    Array RustStmt := Id.run do
  if outCount == 1 then
    let blockExpr : String :=
      s!"if unconstrained \{ Bytes2::{unconShortcut}(&__v_{i}, &__v_{j}) }" ++
      s!" else \{ {valueHelper}(__v_{i}, __v_{j}, record) }"
    return #[.letStmt false s!"__v_{out}" (some "G") (.lit blockExpr)]
  else
    -- 2-tuple outputs (Mul) or 3-tuple (ChainRotr7/4).
    let blockExpr : String :=
      s!"if unconstrained \{ Bytes2::{unconShortcut}(&__v_{i}, &__v_{j}) }" ++
      s!" else \{ {valueHelper}(__v_{i}, __v_{j}, record) }"
    let tupTy : String :=
      "(" ++ (String.intercalate ", " (List.replicate outCount "G")) ++ ")"
    let mut stmts : Array RustStmt := #[
      .letStmt false "__b2_out" (some tupTy) (.lit blockExpr)
    ]
    for k in [0 : outCount] do
      stmts := stmts.push (declVal (out + k) (.field (.var "__b2_out") (toString k)))
    return stmts

/-- `Op::U8Add`: gadget bumps `bytes2_queries.add` and returns
    `(low, carry)`. Codegen now calls `bytes2_add_value` ONCE in
    the constrained branch (vs the interpreter's two `Bytes2::add`
    calls). -/
private def emitU8Add (out : Nat) (i j : ValIdx) : Array RustStmt :=
  let blockExpr : String :=
    s!"if unconstrained \{ Bytes2::add(&__v_{i}, &__v_{j}) }" ++
    s!" else \{ bytes2_add_value(__v_{i}, __v_{j}, record) }"
  #[
    .letStmt false "__b2_add" (some "(G, G)") (.lit blockExpr),
    declVal out (.field (.var "__b2_add") "0"),
    declVal (out + 1) (.field (.var "__b2_add") "1")
  ]

/-- `Op::U8Sub`: symmetric to U8Add. -/
private def emitU8Sub (out : Nat) (i j : ValIdx) : Array RustStmt :=
  let blockExpr : String :=
    s!"if unconstrained \{ Bytes2::sub(&__v_{i}, &__v_{j}) }" ++
    s!" else \{ bytes2_sub_value(__v_{i}, __v_{j}, record) }"
  #[
    .letStmt false "__b2_sub" (some "(G, G)") (.lit blockExpr),
    declVal out (.field (.var "__b2_sub") "0"),
    declVal (out + 1) (.field (.var "__b2_sub") "1")
  ]

/-- `Op::U32LessThan`: mirror execute.rs lines 477-505. Pure
    compare + 6-byte-pair range-check via
    `bytes2_queries.bump_range_check` (constrained mode only). -/
private def emitU32LessThan (out : Nat) (x y : ValIdx) : Array RustStmt :=
  let blockExpr : String :=
    s!"\{ let __a_val = __v_{x}.as_canonical_u64();" ++
    s!" let __b_val = __v_{y}.as_canonical_u64();" ++
    s!" let __a_u32 = u32::try_from(__a_val).ok().ok_or(ExecError::U32OutOfRange(__a_val))?;" ++
    s!" let __b_u32 = u32::try_from(__b_val).ok().ok_or(ExecError::U32OutOfRange(__b_val))?;" ++
    s!" let __result = G::from_bool(__a_u32 < __b_u32);" ++
    s!" if !unconstrained \{" ++
    s!" let __x_bytes = __a_u32.to_le_bytes();" ++
    s!" let __z_bytes = __b_u32.to_le_bytes();" ++
    s!" let __c_u32 = __b_u32.wrapping_sub(__a_u32).wrapping_sub(1);" ++
    s!" let __y_bytes = __c_u32.to_le_bytes();" ++
    s!" record.bytes2_queries.bump_range_check(&G::from_u8(__x_bytes[0]), &G::from_u8(__x_bytes[1]));" ++
    s!" record.bytes2_queries.bump_range_check(&G::from_u8(__x_bytes[2]), &G::from_u8(__x_bytes[3]));" ++
    s!" record.bytes2_queries.bump_range_check(&G::from_u8(__y_bytes[0]), &G::from_u8(__y_bytes[1]));" ++
    s!" record.bytes2_queries.bump_range_check(&G::from_u8(__y_bytes[2]), &G::from_u8(__y_bytes[3]));" ++
    s!" record.bytes2_queries.bump_range_check(&G::from_u8(__z_bytes[0]), &G::from_u8(__z_bytes[1]));" ++
    s!" record.bytes2_queries.bump_range_check(&G::from_u8(__z_bytes[2]), &G::from_u8(__z_bytes[3]));" ++
    s!" } __result }"
  #[.letStmt false s!"__v_{out}" (some "G") (.lit blockExpr)]

/-- `Op::U8RangeCheck`: 0 outputs; pure range-check side effect. -/
private def emitU8RangeCheck (i j : ValIdx) : Array RustStmt :=
  let stmt : String :=
    s!"if !unconstrained \{" ++
    s!" let __vi = __v_{i}; let __vj = __v_{j};" ++
    s!" let __bi = __vi.as_canonical_u64(); let __bj = __vj.as_canonical_u64();" ++
    s!" if __bi >= 256 \{ return Err(ExecError::U8RangeCheckFailed(__bi)); }" ++
    s!" if __bj >= 256 \{ return Err(ExecError::U8RangeCheckFailed(__bj)); }" ++
    s!" record.bytes2_queries.bump_range_check(&__vi, &__vj);" ++
    s!" }"
  #[.exprStmt (.lit stmt)]

/-- `Op::UnconstrainedBigUintDivMod`: BigUint hint, 2 outputs
    (q_ptr, r_ptr). Calls the extracted `unconstrained_big_uint_div_mod_helper`
    which returns `(G, G)` directly. -/
private def emitUncBigUintDivMod (out : Nat) (a b : ValIdx) : Array RustStmt :=
  let blockExpr : String :=
    s!"unconstrained_big_uint_div_mod_helper(__v_{a}, __v_{b}, record)?"
  #[
    .letStmt false "__bu_qr" (some "(G, G)") (.lit blockExpr),
    declVal out (.field (.var "__bu_qr") "0"),
    declVal (out + 1) (.field (.var "__bu_qr") "1")
  ]

/-- `Op::Debug`: 0 outputs; println side effect. Skipped for now. -/
private def emitDebug : Array RustStmt := #[]

/-- Top-level op dispatch. `out` = the first ValIdx for outputs;
    callers must advance their counter by `Op.outputCount`. -/
def emitOp (out : Nat) (op : Op) : Array RustStmt :=
  match op with
  | .const c => emitConst out c
  | .add a b => emitBinop out "+" a b
  | .sub a b => emitBinop out "-" a b
  | .mul a b => emitBinop out "*" a b
  | .eqZero a => emitEqZero out a
  | .call callee args outSz opUn => emitCall out callee args outSz opUn
  | .store vs => emitStore out vs
  | .load size ptr => emitLoad out size ptr
  | .assertEq xs ys => emitAssertEq xs ys
  | .ioGetInfo ch key => emitIOGetInfo out ch key
  | .ioSetInfo ch key idx len => emitIOSetInfo ch key idx len
  | .ioRead ch idx len => emitIORead out ch idx len
  | .ioWrite ch data => emitIOWrite ch data
  | .u8BitDecomposition b => emitU8Bytes1 out "bytes1_bit_decompose_value" "Bytes1::bit_decompose" b 8
  | .u8ShiftLeft b => emitU8Bytes1 out "bytes1_shift_left_value" "Bytes1::shift_left" b 1
  | .u8ShiftRight b => emitU8Bytes1 out "bytes1_shift_right_value" "Bytes1::shift_right" b 1
  | .u8Xor i j => emitU8Bytes2 out "bytes2_xor_value" "xor" i j 1
  | .u8Mul i j => emitU8Bytes2 out "bytes2_mul_value" "mul" i j 2
  | .u8And i j => emitU8Bytes2 out "bytes2_and_value" "and" i j 1
  | .u8Or i j => emitU8Bytes2 out "bytes2_or_value" "or" i j 1
  | .u8LessThan i j => emitU8Bytes2 out "bytes2_less_than_value" "less_than" i j 1
  | .u8ChainRotr7 i j => emitU8Bytes2 out "bytes2_chain_rotr7_value" "chain_rotr7" i j 3
  | .u8ChainRotr4 i j => emitU8Bytes2 out "bytes2_chain_rotr4_value" "chain_rotr4" i j 3
  | .u8Add i j => emitU8Add out i j
  | .u8Sub i j => emitU8Sub out i j
  | .u32LessThan a b => emitU32LessThan out a b
  | .u8RangeCheck i j => emitU8RangeCheck i j
  | .unconstrainedBigUintDivMod a b => emitUncBigUintDivMod out a b
  | .debug _ _ => emitDebug

/-! ## Ctrl emission -/

/-- Scan a Block for the first `Ctrl.return`'s arity. Aiur fn layouts
    are fixed, so all Returns in a fn agree; we only need one. -/
partial def findReturnArity (b : Block) : Option Nat :=
  ctrlArity b.ctrl
where
  ctrlArity : Ctrl → Option Nat
    | .return _ vals => some vals.size
    | .yield _ _ => none
    | .match _ cases dflt? =>
      let viaCases := cases.findSome? (fun ⟨_, blk⟩ => findReturnArity blk)
      match viaCases with
      | some n => some n
      | none => dflt?.bind findReturnArity
    | .matchContinue _ cases dflt? _ _ _ cont =>
      let viaCases := cases.findSome? (fun ⟨_, blk⟩ => findReturnArity blk)
      let viaDflt := dflt?.bind findReturnArity
      let viaCont := findReturnArity cont
      viaCases <|> viaDflt <|> viaCont

/-- Codegen state: `nextVal` is the next ValIdx slot to allocate for
    op outputs (must match Aiur's value-stack growth exactly);
    `nextLabel` is a fresh counter for unique `'__mc_N` labels in
    nested `MatchContinue`s. -/
structure EmitState where
  nextVal : Nat
  nextLabel : Nat
  deriving Inhabited

abbrev EmitM (α : Type) := StateM EmitState α

@[inline] def freshLabel : EmitM String := do
  let s ← get
  set { s with nextLabel := s.nextLabel + 1 }
  return s!"__mc_{s.nextLabel}"

/-- Allocate `count` consecutive ValIdx slots and return the base. -/
@[inline] def allocVals (count : Nat) : EmitM Nat := do
  let s ← get
  set { s with nextVal := s.nextVal + count }
  return s.nextVal

/-- Run `m` with the current `nextVal` snapshotted; on exit restore
    `nextVal` to its value at entry. Used for `Match` / `MatchContinue`
    case bodies, which logically execute from the SAME value-stack
    snapshot that existed before the match dispatch. -/
@[inline] def withSavedNextVal (m : EmitM α) : EmitM α := do
  let saved := (← get).nextVal
  let a ← m
  modify ({ · with nextVal := saved })
  return a

mutual

/-- Emit a Block's stmts. `mcLabel?` is the label of the enclosing
    `MatchContinue` (used by `Ctrl.yield` to `break` with values).
    A Block whose Ctrl is `Return` does NOT bubble — it always emits
    the outer fn's `return`. -/
partial def emitBlock (funIdx : FunIdx) (mcLabel? : Option String)
    (b : Block) : EmitM (Array RustStmt) := do
  let mut stmts : Array RustStmt := #[]
  for op in b.ops do
    let outBase ← allocVals (Op.outputCount op)
    stmts := stmts ++ emitOp outBase op
  let ctrlStmts ← emitCtrl funIdx mcLabel? b.ctrl
  return stmts ++ ctrlStmts

partial def emitCtrl (funIdx : FunIdx) (mcLabel? : Option String)
    (ctrl : Ctrl) : EmitM (Array RustStmt) := do
  match ctrl with
  | .return _ outs =>
    -- Mirror execute.rs Ctrl::Return: build the output array, insert
    -- into function_queries (binding to the per-fn `inp` slice for
    -- args), then Rust-return the array. Ignores `mcLabel?` because
    -- Return exits the whole fn.
    let outArr : RustStmt :=
      .letStmt false "__ret" (some s!"[G; OUT_{funIdx}]")
        (.arrayLit (outs.map valVar))
    let insertCall : RustStmt :=
      .exprStmt (.call
        (.field
          (.index (.field (.var "record") "function_queries")
            (.lit (toString funIdx)))
          "insert")
        #[.ref (.index (.var "inp") (.lit "..")),
          .ref (.index (.var "__ret") (.lit "..")),
          gFromBool (.lit "!unconstrained")])
    -- Wrap in Ok(...) since fn now returns Result<[G; OUT_N], ExecError>.
    return #[outArr, insertCall,
      .returnStmt (.call (.var "Ok") #[.var "__ret"])]
  | .match valIdx cases dflt? => do
    -- Each arm body executes from the SAME value-stack snapshot as
    -- match entry. Snapshot nextVal per arm so per-arm allocations
    -- don't leak to siblings.
    let mut arms : Array MatchArm := #[]
    for ⟨key, blk⟩ in cases do
      let armBody ← withSavedNextVal (emitBlock funIdx mcLabel? blk)
      arms := arms.push { pat := .litU64 key.n, body := armBody }
    let dfltBody ← (match dflt? with
      | some d => withSavedNextVal (emitBlock funIdx mcLabel? d)
      | none => pure #[
          .returnStmt
            (.call (.var "Err")
              #[.call (.path #["ExecError", "MatchNoCase"])
                #[.call (.field (valVar valIdx) "as_canonical_u64") #[]]])])
    arms := arms.push { pat := .wildcard, body := dfltBody }
    return #[.matchStmt
      (.call (.field (valVar valIdx) "as_canonical_u64") #[])
      arms]
  | .matchContinue valIdx cases dflt? outputSize _shAux _shLk continuation => do
    -- Snapshot the value-stack base for the case bodies; they all
    -- run from this same snapshot.
    --
    -- Generated shape (no `map`, only locals):
    --   let __mc_out_N: [G; OUT_SIZE] = '__mc_N: {
    --     match __v_{valIdx}.as_canonical_u64() {
    --       K1 => { ... break '__mc_N [__v_a, __v_b, ...]; },
    --       ...
    --       _  => { ... },
    --     }
    --   };
    --   let __v_{base}:   G = __mc_out_N[0];
    --   let __v_{base+1}: G = __mc_out_N[1];
    --   ...   // outputSize values rebound at outer scope
    --   /* continuation emitted with nextVal = base + outputSize */
    let label ← freshLabel
    let mut arms : Array MatchArm := #[]
    for ⟨key, blk⟩ in cases do
      let armBody ← withSavedNextVal (emitBlock funIdx (some label) blk)
      arms := arms.push { pat := .litU64 key.n, body := armBody }
    let dfltBody ← (match dflt? with
      | some d => withSavedNextVal (emitBlock funIdx (some label) d)
      | none => pure #[
          .returnStmt
            (.call (.var "Err")
              #[.call (.path #["ExecError", "MatchNoCase"])
                #[.call (.field (valVar valIdx) "as_canonical_u64") #[]]])])
    arms := arms.push { pat := .wildcard, body := dfltBody }
    let matchStmt : RustStmt :=
      .matchStmt (.call (.field (valVar valIdx) "as_canonical_u64") #[]) arms
    -- Reserve `outputSize` slots at outer scope for the yielded values.
    let outBase ← allocVals outputSize
    let yieldedLet : RustStmt :=
      .letStmt false s!"__mc_out_{label}" (some s!"[G; {outputSize}]")
        (.labeledBlock label #[matchStmt])
    let mut splat : Array RustStmt := #[]
    for k in [0 : outputSize] do
      splat := splat.push
        (declVal (outBase + k)
          (.index (.var s!"__mc_out_{label}") (.lit (toString k))))
    let contStmts ← emitBlock funIdx mcLabel? continuation
    return #[yieldedLet] ++ splat ++ contStmts
  | .yield _ outs =>
    -- Yield: bubble values to the enclosing `MatchContinue`'s labeled
    -- block via `break '__mc_N vec![...];`. Only valid inside a
    -- MatchContinue case body, so `mcLabel?` MUST be set; if it isn't,
    -- emit a panic so the failure is obvious during testing.
    match mcLabel? with
    | some label =>
      return #[.breakWith label (.arrayLit (outs.map valVar))]
    | none =>
      return #[.exprStmt
        (.lit "unreachable!(\"Ctrl::Yield outside of MatchContinue context\")")]

end

/-! ## Function & toplevel emission -/

def emitFunction (funIdx : FunIdx) (f : Function) : Array RustItem := Id.run do
  let inSize := f.layout.inputSize
  let outSize := (findReturnArity f.body).getD 0
  let inputSizeConst := RustItem.constUsize s!"INPUT_SIZE_{funIdx}" inSize
  let inConst := RustItem.constUsize s!"IN_{funIdx}" inSize
  let outConst := RustItem.constUsize s!"OUT_{funIdx}" outSize
  -- Bind inputs as `__v_0..__v_{inSize-1}` so subsequent op outputs
  -- can reference them by ValIdx.
  let mut bindInputs : Array RustStmt := #[]
  for i in [0 : inSize] do
    bindInputs := bindInputs.push
      (.letStmt false s!"__v_{i}" (some "G") (.index (.var "inp") (.lit (toString i))))
  -- nextVal starts at inSize (the next free ValIdx after the inputs).
  let initState : EmitState := { nextVal := inSize, nextLabel := 0 }
  let (bodyStmts, _) := (emitBlock funIdx none f.body).run initState
  let body := bindInputs ++ bodyStmts
  -- Wrap the whole body in `stacker::maybe_grow` so deep Aiur
  -- recursion grows the stack on demand instead of overflowing.
  -- Red zone 64KB / new stack 4MB — when the current thread has
  -- <64KB of stack left, stacker allocates a fresh 4MB segment
  -- and runs the closure there. Repeats as deep as the recursion
  -- goes.
  let lbrace := "{"
  let rbrace := "}"
  let bodyText : String := stmtsToStr 2 body
  let fnText : String :=
    s!"fn aiur_fn_{funIdx}(\n" ++
    s!"  inp: [G; IN_{funIdx}],\n" ++
    s!"  record: &mut QueryRecord,\n" ++
    s!"  io_buffer: &mut IOBuffer,\n" ++
    s!"  unconstrained: bool,\n" ++
    s!") -> Result<[G; OUT_{funIdx}], ExecError> {lbrace}\n" ++
    s!"  stacker::maybe_grow(64 * 1024, 4 * 1024 * 1024, || {lbrace}\n" ++
    bodyText ++
    s!"  {rbrace})\n" ++
    s!"{rbrace}\n\n"
  #[inputSizeConst, inConst, outConst, .raw fnText]

/-- Header that's always emitted (file comments, lint allows, and the
    fixed `use` items every generated body references). Per-op
    helpers (`bytes2_xor_value`, etc.) are added only when the body
    actually mentions them — see `emitConditionalImports`. -/
def emitPreludeHeader : String :=
  "// Auto-generated by Aiur codegen. Do not edit.\n\
   //\n\
   // Mirrors `crates/aiur/src/execute.rs`'s QueryRecord side effects exactly.\n\
   //\n\
   // Skip rustfmt — this file is huge and the codegen lays it out\n\
   // for the compiler, not for humans.\n\
   #![cfg_attr(rustfmt, rustfmt::skip)]\n\
   #![allow(\n\
   \x20\x20unused_variables, unused_assignments, unused_mut, dead_code,\n\
   \x20\x20unused_parens, non_snake_case, clippy::all,\n\
   \x20\x20clippy::ptr_as_ptr, clippy::match_same_arms,\n\
   \x20\x20clippy::large_types_passed_by_value,\n\
   )]\n\
   \n\
   use multi_stark::p3_field::{PrimeCharacteristicRing, PrimeField64};\n\
   use aiur::G;\n"

/-- The set of optional `aiur::execute` items the codegen
    might emit references to. Each pair is `(rust_path, search_token)`
    — if `search_token` appears anywhere in the body string, the item
    is included in the generated `use` block. The token is the exact
    identifier that appears at every call site; substring match is
    safe because all of these names are unique within the generated
    file (no other crate-level item has the same identifier). -/
def optionalExecuteUses : Array (String × String) := #[
  ("bytes1_bit_decompose_value", "bytes1_bit_decompose_value"),
  ("bytes1_shift_left_value", "bytes1_shift_left_value"),
  ("bytes1_shift_right_value", "bytes1_shift_right_value"),
  ("bytes2_xor_value", "bytes2_xor_value"),
  ("bytes2_and_value", "bytes2_and_value"),
  ("bytes2_or_value", "bytes2_or_value"),
  ("bytes2_less_than_value", "bytes2_less_than_value"),
  ("bytes2_mul_value", "bytes2_mul_value"),
  ("bytes2_add_value", "bytes2_add_value"),
  ("bytes2_sub_value", "bytes2_sub_value"),
  ("bytes2_chain_rotr7_value", "bytes2_chain_rotr7_value"),
  ("bytes2_chain_rotr4_value", "bytes2_chain_rotr4_value"),
  ("unconstrained_big_uint_div_mod_helper", "unconstrained_big_uint_div_mod_helper"),
  ("CodegenBytes1 as Bytes1", "Bytes1::"),
  ("CodegenBytes2 as Bytes2", "Bytes2::")
]

/-- Build the `use aiur::execute::{...};` block, including only
    items whose search token appears in `body`. -/
def emitConditionalImports (body : String) : String := Id.run do
  let always : Array String := #["ExecError", "IOBuffer", "QueryRecord"]
  let mut items : Array String := always
  for (path, token) in optionalExecuteUses do
    if (body.splitOn token).length > 1 then
      items := items.push path
  let joined : String := items.toList.foldl
    (fun acc s => if acc.isEmpty then s else acc ++ ", " ++ s) ""
  s!"use aiur::execute::\{ {joined} };\n\n"

/-- Build the dispatch entry point `pub fn execute_generated(...)`
    that maps a `fun_idx` to the right `aiur_fn_N` invocation. Mirrors
    the interpreter's `execute::execute` signature so callers (kernel
    runner, tests) can swap it in. -/
def emitDispatch (tl : Toplevel) : RustItem := Id.run do
  let mut arms : Array MatchArm := #[]
  for funIdx in [0 : tl.functions.size] do
    let armBody : Array RustStmt := #[
      .letStmt false "__inp" (some s!"[G; IN_{funIdx}]")
        (.lit "args.try_into().expect(\"input size mismatch\")"),
      .letStmt false "__out" none
        (.lit s!"aiur_fn_{funIdx}(__inp, record, io_buffer, false)?"),
      .returnStmt (.call (.var "Ok")
        #[.call (.field (.var "__out") "to_vec") #[]])
    ]
    arms := arms.push { pat := .litU64 funIdx, body := armBody }
  arms := arms.push {
    pat := .wildcard,
    body := #[.returnStmt
      (.call (.var "Err")
        #[.call (.path #["ExecError", "InvalidFunIdx"]) #[.var "fun_idx"]])]
  }
  -- Emit raw text for the dispatch fn so we can prefix `pub(crate)`
  -- without extending RustItem. The body is built via stmtsToStr at
  -- the right indentation.
  let body : Array RustStmt := #[.matchStmt (.lit "fun_idx as u64") arms]
  let lbrace := "{"
  let rbrace := "}"
  .raw (s!"pub(crate) fn execute_generated(\n" ++
        s!"  fun_idx: usize,\n" ++
        s!"  args: &[G],\n" ++
        s!"  record: &mut QueryRecord,\n" ++
        s!"  io_buffer: &mut IOBuffer,\n" ++
        s!") -> Result<Vec<G>, ExecError> {lbrace}\n" ++
        stmtsToStr 1 body ++
        s!"{rbrace}\n")

/-- Emit Rust source for the whole `Bytecode.Toplevel`. Builds the
    body first, then emits a prelude whose `use` block lists only
    the helpers the body actually mentions. -/
def emit (tl : Toplevel) : String := Id.run do
  let mut items : Array RustItem := #[]
  for funIdx in [0 : tl.functions.size] do
    items := items ++ emitFunction funIdx tl.functions[funIdx]!
  items := items.push (emitDispatch tl)
  let mut bodyStr := ""
  for it in items do
    bodyStr := bodyStr ++ it.toStr
  emitPreludeHeader ++ emitConditionalImports bodyStr ++ bodyStr

end Aiur.Codegen

end
