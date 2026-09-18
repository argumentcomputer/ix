/-
  Aiur bytecode → structured Rust syntax → Rust source.

  Emits one const-generic Rust function per Aiur function. Ordinary calls
  inherit UNCONSTRAINED, hint calls select true, and entry dispatch selects
  false. Real Rust locals replace the interpreter's value stack.

  Correctness invariant: native execution preserves the interpreter's
  QueryRecord, including insertion order, multiplicities, hint promotion,
  byte-chip queries, and IO order. Return registration happens AFTER the
  callee body and rechecks the complete input key, reusing the caller's hash.

  Syntax and formatting live in Codegen.Rust. This module only constructs
  syntax trees; strings here are identifiers, diagnostic text, or the fixed
  module header, never executable Rust fragments.
-/
module
public import Ix.Aiur.Stages.Bytecode
public import Ix.Aiur.Codegen.Rust

public section
namespace Aiur.Codegen
open Bytecode

/-! ## Shared syntax constructors -/

private def gTy : RustType := .named "G"
private def gArray (n : Nat) : RustType := .array gTy (.value n)
private def inputTy (idx : Nat) : RustType := .array gTy (.named s!"IN_{idx}")
private def outputTy (idx : Nat) : RustType := .array gTy (.named s!"OUT_{idx}")
private def resultTy (ty : RustType) : RustType := .app "Result" #[ty, .named "ExecError"]
private def method (e : RustExpr) (name : String) (args : Array RustExpr := #[]) : RustExpr :=
  .methodCall e name args
private def staticCall (ty name : String) (args : Array RustExpr) : RustExpr :=
  .call (.path #[ty, name]) args
private def runtimeCall (name : String) (args : Array RustExpr) : RustExpr :=
  .call (.path #["aiur", "execute", name]) args
private def errorValue (name : String) (args : Array RustExpr) : RustExpr :=
  staticCall "ExecError" name args
private def returnError (e : RustExpr) : RustStmt := .returnStmt (.call (.var "Err") #[e])
private def tailBlock (e : RustExpr) : RustBlock := { tail := some e }
private def blockValue (ss : Array RustStmt) (e : RustExpr) : RustExpr :=
  .block { stmts := ss, tail := some e }
private def sliceRef (e : RustExpr) : RustExpr := .ref (.index e (.range none none))
private def canonical (e : RustExpr) : RustExpr := method e "as_canonical_u64"
private def expect (e : RustExpr) (msg : String) : RustExpr :=
  method e "expect" #[.string msg]
private def checkedCast (ty : String) (e : RustExpr) (error : String) : RustExpr :=
  .tryExpr (method (method (staticCall ty "try_from" #[e]) "ok") "ok_or"
    #[errorValue error #[e]])
private def fixedArray (e : RustExpr) (size : Nat) : RustExpr :=
  method (method (.index e (.range none (some (.nat size)))) "try_into") "unwrap"

def gZero : RustExpr := .path #["G", "ZERO"]
def gFromU64 (n : Nat) : RustExpr := staticCall "G" "from_u64" #[.nat n]
def gFromBool (e : RustExpr) : RustExpr := staticCall "G" "from_bool" #[e]
def gFromUsize (e : RustExpr) : RustExpr := staticCall "G" "from_usize" #[e]
def valVar (i : Nat) : RustExpr := .var s!"__v_{i}"
def declVal (i : Nat) (e : RustExpr) : RustStmt :=
  .letStmt false s!"__v_{i}" (some gTy) e
def argsAsArray (is : Array ValIdx) : RustExpr := .arrayLit (is.map valVar)
def funQueriesAt (idx : Nat) : RustExpr :=
  .index (.field (.var "record") "function_queries") (.nat idx)
def notUnconstrained : RustExpr := .not (.var "unconstrained")
private def whenConstrained (ss : Array RustStmt) : RustStmt :=
  .ifStmt notUnconstrained ss none
private def bumpMultiplicity (table idx : RustExpr) : RustStmt :=
  .exprStmt (method table "bump_multiplicity" #[idx])
private def lookupKey (table key : RustExpr) : RustStmt :=
  .letPattern (.tuple #[.binding "__hash", .binding "__hit"]) none
    (method table "lookup" #[sliceRef key])
private def splatArray (out count : Nat) (name : String) : Array RustStmt :=
  (Array.range count).map fun k => declVal (out + k) (.index (.var name) (.nat k))
private def splatTuple (out count : Nat) (name : String) : Array RustStmt :=
  (Array.range count).map fun k => declVal (out + k) (.field (.var name) (toString k))
private def nativeCall (idx : Nat) (mode : RustExpr) (input hash : RustExpr) : RustExpr :=
  .tryExpr (.call (.constGeneric (.var s!"aiur_fn_{idx}") #[mode])
    #[input, hash, .var "record", .var "io_buffer"])

/-! ## Operation emission -/

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
  | .assertEq _ _ _ => 0
  | .ioGetInfo _ _ => 2
  | .ioSetInfo _ _ _ _ => 0
  | .ioRead _ _ len => len
  | .ioWrite _ _ => 0
  | .u8BitDecomposition _ => 8
  | .u8ShiftLeft _ | .u8ShiftRight _ => 1
  | .u8Xor _ _ | .u8And _ _ | .u8Or _ _ | .u8LessThan _ _ => 1
  | .u8Mul _ _ => 2
  | .u8Add _ _ | .u8Sub _ _ => 2
  | .u8XorSplit7 _ _ | .u8XorSplit4 _ _ => 2
  | .u32LessThan _ _ => 1
  | .u8RangeCheck _ _ => 0
  | .unconstrainedBigUintDivMod _ _ => 2
  | .unconstrainedGToBytes _ => 8
  | .unconstrainedGInverse _ => 1
  | .unconstrainedU32Add _ _ | .unconstrainedU32Add3 _ _ _ => 5
  | .u32ToField _ => 1
  | .debug _ _ => 0


private def emitConst (out : Nat) (c : Aiur.G) : Array RustStmt :=
  #[declVal out (gFromU64 c.n)]

private def emitBinop (out : Nat) (op : RustBinOp) (a b : ValIdx) : Array RustStmt :=
  #[declVal out (.binop op (valVar a) (valVar b))]

private def emitEqZero (out : Nat) (a : ValIdx) : Array RustStmt :=
  #[declVal out (gFromBool (.binop .eq (valVar a) gZero))]

/-- Cached hints must be replayed in constrained mode to promote their whole
    dependency tree, not just the cached row. A hit may only skip the body
    when already constrained or when the caller also requests a hint. -/
private def emitCall (out : Nat) (callee : FunIdx) (args : Array ValIdx)
    (outSize : Nat) (opUn : Bool) : Array RustStmt :=
  let queries := funQueriesAt callee
  let mode : RustExpr := if opUn then .bool true else .var "UNCONSTRAINED"
  let guard : RustExpr := if opUn then .bool true else
    .binop .or (.var "__cu") (.binop .ne (method queries "mult_at" #[.var "__i"]) gZero)
  let bump := if opUn then #[] else
    #[whenConstrained #[bumpMultiplicity queries (.var "__i")]]
  -- Every row in this function's table has exactly OUT_N outputs. Preserve
  -- the existing unchecked array copy, explicitly scoped as an unsafe block.
  let cached := .unsafeBlock (tailBlock (.deref
    (.cast (method (method queries "output_at" #[.var "__i"]) "as_ptr")
      (.ptr false (outputTy callee)))))
  let hit : MatchArm := {
    pat := .constructor #["Some"] #[.binding "__i"], guard := some guard
    body := { stmts := bump ++ #[.letStmt false "__ret" (some (outputTy callee)) cached]
              tail := some (.var "__ret") }
  }
  let miss : MatchArm := {
    pat := .wildcard
    body := tailBlock (nativeCall callee mode (.var "__args") (.var "__hash"))
  }
  let rhs := blockValue #[
    .letStmt false "__args" (some (inputTy callee)) (argsAsArray args),
    .letStmt false "__cu" none (if opUn then .bool true else .var "unconstrained"),
    lookupKey queries (.var "__args")
  ] (.matchExpr (.var "__hit") #[hit, miss])
  #[.letStmt false "__r_arr" (some (outputTy callee)) rhs] ++
    splatArray out outSize "__r_arr"

/-- Fixed table slots are validated once by entry dispatch. Standalone op
    emission, which has no toplevel layout, uses the width-keyed fallback. -/
private def memoryQuery (memorySizes : Array Nat) (size : Nat) : RustExpr :=
  let tables : RustExpr := .field (.var "record") "memory_queries"
  let query := match memorySizes.findIdx? (· == size) with
    | some slot => method (method tables "get_index_mut" #[.nat slot]) "map"
        #[.closure #[.tuple #[.wildcard, .binding "q"]] (.var "q")]
    | none => method tables "get_mut" #[.ref (.nat size)]
  .tryExpr (method query "ok_or" #[errorValue "InvalidMemorySize" #[.nat size]])

private def emitStore (out : Nat) (values : Array ValIdx)
    (memorySizes : Array Nat) : Array RustStmt :=
  let table : RustExpr := .var "__mq"
  let hit : MatchArm := {
    pat := .constructor #["Some"] #[.binding "__i"]
    body := {
      stmts := #[whenConstrained #[bumpMultiplicity table (.var "__i")]]
      tail := some (.index (method table "output_at" #[.var "__i"]) (.nat 0))
    }
  }
  let miss : MatchArm := {
    pat := .wildcard
    body := {
      stmts := #[
        .letStmt false "__ptr" none (gFromUsize (method table "len")),
        .exprStmt (method table "insert_hashed" #[
          sliceRef (.var "__values"), .ref (.arrayLit #[.var "__ptr"]),
          gFromBool notUnconstrained, .var "__hash"])
      ]
      tail := some (.var "__ptr")
    }
  }
  #[declVal out (blockValue #[
    .letStmt false "__values" (some (gArray values.size)) (argsAsArray values),
    .letStmt false "__mq" none (memoryQuery memorySizes values.size),
    lookupKey table (.var "__values")
  ] (.matchExpr (.var "__hit") #[hit, miss]))]

private def emitLoad (out size : Nat) (ptr : ValIdx)
    (memorySizes : Array Nat) : Array RustStmt :=
  let table : RustExpr := .var "__mq"
  let rhs := blockValue #[
    .letStmt false "__mq" none (memoryQuery memorySizes size),
    .letStmt false "__ptr_u64" none (canonical (valVar ptr)),
    .letStmt false "__ptr_usize" none (checkedCast "usize" (.var "__ptr_u64") "PointerTooLarge"),
    .ifStmt (.binop .ge (.var "__ptr_usize") (method table "len"))
      #[returnError (.structLit #["ExecError", "UnboundPointer"]
        #[("ptr", .var "__ptr_u64"), ("size", .nat size)])] none,
    whenConstrained #[bumpMultiplicity table (.var "__ptr_usize")],
    .letPattern (.tuple #[.binding "__args", .wildcard]) none
      (expect (method table "get_index" #[.var "__ptr_usize"]) "bounds checked above"),
    .letStmt false "__arr" (some (gArray size)) (fixedArray (.var "__args") size)
  ] (.var "__arr")
  #[.letStmt false "__loaded" (some (gArray size)) rhs] ++ splatArray out size "__loaded"

private def emitAssertEq (xs ys : Array ValIdx) (msg : Option String) : Array RustStmt :=
  let message : RustExpr := match msg with
    | some m => .call (.var "Some") #[method (.string m) "to_string"]
    | none => .var "None"
  if xs.size != ys.size then
    #[returnError (.structLit #["ExecError", "AssertEqLengthMismatch"]
      #[("lhs", .nat xs.size), ("rhs", .nat ys.size)])]
  else (xs.zip ys).map fun (x, y) =>
    .ifStmt (.binop .ne (valVar x) (valVar y))
      #[returnError (.structLit #["ExecError", "AssertEqMismatch"]
        #[("lhs", canonical (valVar x)), ("rhs", canonical (valVar y)), ("msg", message)])] none

/-! ### IO -/

private def emitIOGetInfo (out channel : Nat) (key : Array ValIdx) : Array RustStmt :=
  #[.letStmt false "__io_pair" (some (.tuple #[gTy, gTy])) (blockValue #[
    .letStmt false "__key" (some (gArray key.size)) (argsAsArray key),
    .letStmt false "__info" none
      (.tryExpr (method (.var "io_buffer") "get_info" #[valVar channel, sliceRef (.var "__key")]))
  ] (.tuple #[gFromUsize (.field (.var "__info") "idx"),
              gFromUsize (.field (.var "__info") "len")]))] ++ splatTuple out 2 "__io_pair"

private def emitIOSetInfo (channel : ValIdx) (key : Array ValIdx)
    (idx len : ValIdx) : Array RustStmt :=
  #[.block #[
    .letStmt false "__key" (some (gArray key.size)) (argsAsArray key),
    .letStmt false "__idx" none (checkedCast "usize" (canonical (valVar idx)) "IndexTooLarge"),
    .letStmt false "__len" none (checkedCast "usize" (canonical (valVar len)) "IndexTooLarge"),
    .exprStmt (.tryExpr (method (.var "io_buffer") "set_info"
      #[valVar channel, method (.var "__key") "to_vec", .var "__idx", .var "__len"]))
  ]]

private def emitIORead (out channel idx len : Nat) : Array RustStmt :=
  #[.letStmt false "__io_read" (some (gArray len)) (blockValue #[
    .letStmt false "__idx_u64" none (canonical (valVar idx)),
    .letStmt false "__idx" none (checkedCast "usize" (.var "__idx_u64") "IndexTooLarge"),
    .letStmt false "__data" none
      (.tryExpr (method (.var "io_buffer") "read" #[valVar channel, .var "__idx", .nat len])),
    .letStmt false "__arr" (some (gArray len)) (fixedArray (.var "__data") len)
  ] (.var "__arr"))] ++ splatArray out len "__io_read"

private def emitIOWrite (channel : ValIdx) (data : Array ValIdx) : Array RustStmt :=
  #[.exprStmt (method (.var "io_buffer") "write"
    #[valVar channel, method (argsAsArray data) "into_iter"])]

/-! ### Byte operations and hints -/

/-- Helper paths are explicit in the tree, not inferred by searching source.
    The constrained helper records queries; the hint computes only values. -/
private def byteResult (chip shortcut helper : String) (args : Array ValIdx) : RustExpr :=
  .ifExpr (.var "unconstrained")
    (tailBlock (.call (.path #["aiur", "execute", chip, shortcut])
      (args.map fun i => .ref (valVar i))))
    (tailBlock (runtimeCall helper ((args.map valVar).push (.var "record"))))

private def emitU8Bytes1 (out : Nat) (helper shortcut : String)
    (byte : ValIdx) (outCount : Nat) : Array RustStmt :=
  if outCount == 1 then
    #[declVal out (byteResult "CodegenBytes1" shortcut helper #[byte])]
  else
    -- The hint returns Vec<G>, while the constrained helper returns [G; 8].
    let hint : RustBlock := {
      stmts := #[
        .letStmt false "__v" (some (.app "Vec" #[gTy]))
          (.call (.path #["aiur", "execute", "CodegenBytes1", shortcut]) #[.ref (valVar byte)]),
        .letStmt false "__a" (some (gArray outCount))
          (method (method (.var "__v") "try_into") "unwrap")
      ]
      tail := some (.var "__a")
    }
    #[.letStmt false "__b1_out" (some (gArray outCount))
      (.ifExpr (.var "unconstrained") hint
        (tailBlock (runtimeCall helper #[valVar byte, .var "record"])))] ++
      splatArray out outCount "__b1_out"

private def emitU8Bytes2 (out : Nat) (helper shortcut : String)
    (i j : ValIdx) (outCount : Nat) : Array RustStmt :=
  let rhs := byteResult "CodegenBytes2" shortcut helper #[i, j]
  if outCount == 1 then #[declVal out rhs]
  else
    #[.letStmt false "__b2_out" (some (.tuple (Array.replicate outCount gTy))) rhs] ++
      splatTuple out outCount "__b2_out"

private def emitU32LessThan (out x y : Nat) : Array RustStmt :=
  let bump (e : RustExpr) : RustStmt :=
    .exprStmt (method (.field (.var "record") "bytes2_queries") "bump_u16_range_check"
      #[.cast e (.named "u16")])
  #[declVal out (blockValue #[
    .letStmt false "__a_val" none (canonical (valVar x)),
    .letStmt false "__b_val" none (canonical (valVar y)),
    .letStmt false "__a_u32" none (checkedCast "u32" (.var "__a_val") "U32OutOfRange"),
    .letStmt false "__b_u32" none (checkedCast "u32" (.var "__b_val") "U32OutOfRange"),
    .letStmt false "__result" none (gFromBool (.binop .lt (.var "__a_u32") (.var "__b_u32"))),
    whenConstrained #[
      .letStmt false "__c_u32" none (method (.var "__a_u32") "wrapping_sub" #[.var "__b_u32"]),
      .forStmt (.binding "__word") (.arrayLit #[.var "__a_u32", .var "__c_u32", .var "__b_u32"])
        #[bump (.binop .bitAnd (.var "__word") (.nat 65535)),
          bump (.binop .shr (.var "__word") (.nat 16))]
    ]
  ] (.var "__result"))]

private def u32PackExpr (xs : Array ValIdx) : RustExpr :=
  let terms := xs.mapIdx fun i idx => .binop .shl (canonical (valVar idx)) (.nat (8 * i))
  -- Valid bytecode supplies four limbs. Zero also gives a well-formed empty fold.
  match terms.toList with
  | [] => .nat 0
  | first :: rest => rest.foldl (.binop .bitOr) first

private def emitUnconstrainedU32Add (out : Nat) (inputs : List (Array ValIdx)) : Array RustStmt :=
  let terms := inputs.map fun xs => staticCall "u128" "from" #[u32PackExpr xs]
  let sum := match terms with
    | [] => .nat 0
    | first :: rest => rest.foldl (.binop .add) first
  #[
    .letStmt false "__u32_sum" (some (.named "u128")) sum,
    .letStmt false "__u32_bytes" none (method
      (expect (staticCall "u32" "try_from" #[.binop .bitAnd (.var "__u32_sum") (.nat 4294967295)])
        "masked") "to_le_bytes")
  ] ++ (Array.range 4).map (fun i =>
    declVal (out + i) (staticCall "G" "from_u8" #[.index (.var "__u32_bytes") (.nat i)])) ++
  #[declVal (out + 4) (staticCall "G" "from_u64" #[
    expect (staticCall "u64" "try_from" #[.binop .shr (.var "__u32_sum") (.nat 32)])
      "u32 sum overflow fits u64"])]

private def emitU32ToField (out : Nat) (bytes : Array ValIdx) : Array RustStmt :=
  #[declVal out (staticCall "G" "from_u64" #[u32PackExpr bytes])]

private def emitU8RangeCheck (i j : ValIdx) : Array RustStmt :=
  #[whenConstrained #[
    .letStmt false "__vi" none (valVar i),
    .letStmt false "__vj" none (valVar j),
    .letStmt false "__bi" none (canonical (.var "__vi")),
    .letStmt false "__bj" none (canonical (.var "__vj")),
    .ifStmt (.binop .ge (.var "__bi") (.nat 256))
      #[returnError (errorValue "U8RangeCheckFailed" #[.var "__bi"])] none,
    .ifStmt (.binop .ge (.var "__bj") (.nat 256))
      #[returnError (errorValue "U8RangeCheckFailed" #[.var "__bj"])] none,
    .exprStmt (method (.field (.var "record") "bytes2_queries") "bump_range_check"
      #[.ref (.var "__vi"), .ref (.var "__vj")])
  ]]

private def emitUncBigUintDivMod (out a b : Nat) : Array RustStmt :=
  #[.letStmt false "__bu_qr" (some (.tuple #[gTy, gTy]))
    (.tryExpr (runtimeCall "unconstrained_big_uint_div_mod_helper"
      #[valVar a, valVar b, .var "record"]))] ++ splatTuple out 2 "__bu_qr"

private def emitUncGToBytes (out a : Nat) : Array RustStmt :=
  #[.letStmt false "__gb" (some (.array (.named "u8") (.value 8)))
    (method (canonical (valVar a)) "to_le_bytes")] ++
    (Array.range 8).map fun i =>
      declVal (out + i) (staticCall "G" "from_u8" #[.index (.var "__gb") (.nat i)])

private def emitUncGInverse (out a : Nat) : Array RustStmt :=
  #[declVal out (runtimeCall "g_inverse_value" #[valVar a])]

private def emitDebug (label : String) (args : Option (Array ValIdx)) : Array RustStmt :=
  -- Format-string braces and Rust string escaping are separate concerns.
  let label := label.replace "{" "{{" |>.replace "}" "}}"
  let (format, values) := match args with
    | none => (label, #[])
    | some idxs =>
      (label ++ ": " ++ ", ".intercalate (idxs.toList.map fun _ => "{}"), idxs.map valVar)
  #[.exprStmt (.macroCall "println" (#[.string format] ++ values))]

/-- Top-level op dispatch. `out` = the first ValIdx for outputs;
    callers must advance their counter by `Op.outputCount`. -/
def emitOp (out : Nat) (op : Op) (memorySizes : Array Nat := #[]) : Array RustStmt :=
  match op with
  | .const c => emitConst out c
  | .add a b => emitBinop out .add a b
  | .sub a b => emitBinop out .sub a b
  | .mul a b => emitBinop out .mul a b
  | .eqZero a => emitEqZero out a
  | .call callee args outSz opUn => emitCall out callee args outSz opUn
  | .store vs => emitStore out vs memorySizes
  | .load size ptr => emitLoad out size ptr memorySizes
  | .assertEq xs ys msg => emitAssertEq xs ys msg
  | .ioGetInfo ch key => emitIOGetInfo out ch key
  | .ioSetInfo ch key idx len => emitIOSetInfo ch key idx len
  | .ioRead ch idx len => emitIORead out ch idx len
  | .ioWrite ch data => emitIOWrite ch data
  | .u8BitDecomposition b => emitU8Bytes1 out "bytes1_bit_decompose_value" "bit_decompose" b 8
  | .u8ShiftLeft b => emitU8Bytes1 out "bytes1_shift_left_value" "shift_left" b 1
  | .u8ShiftRight b => emitU8Bytes1 out "bytes1_shift_right_value" "shift_right" b 1
  | .u8Xor i j => emitU8Bytes2 out "bytes2_xor_value" "xor" i j 1
  | .u8Mul i j => emitU8Bytes2 out "bytes2_mul_value" "mul" i j 2
  | .u8And i j => emitU8Bytes2 out "bytes2_and_value" "and" i j 1
  | .u8Or i j => emitU8Bytes2 out "bytes2_or_value" "or" i j 1
  | .u8LessThan i j => emitU8Bytes2 out "bytes2_less_than_value" "less_than" i j 1
  | .u8XorSplit7 i j => emitU8Bytes2 out "bytes2_xor_split7_value" "xor_split7" i j 2
  | .u8XorSplit4 i j => emitU8Bytes2 out "bytes2_xor_split4_value" "xor_split4" i j 2
  | .u8Add i j => emitU8Bytes2 out "bytes2_add_value" "add" i j 2
  | .u8Sub i j => emitU8Bytes2 out "bytes2_sub_value" "sub" i j 2
  | .u32LessThan a b => emitU32LessThan out a b
  | .u8RangeCheck i j => emitU8RangeCheck i j
  | .unconstrainedBigUintDivMod a b => emitUncBigUintDivMod out a b
  | .unconstrainedGToBytes a => emitUncGToBytes out a
  | .unconstrainedGInverse a => emitUncGInverse out a
  | .unconstrainedU32Add a b => emitUnconstrainedU32Add out [a, b]
  | .unconstrainedU32Add3 a b c => emitUnconstrainedU32Add out [a, b, c]
  | .u32ToField a => emitU32ToField out a
  | .debug label args => emitDebug label args

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
  memorySizes : Array Nat := #[]
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
    stmts := stmts ++ emitOp outBase op (← get).memorySizes
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
      .letStmt false "__ret" (some (outputTy funIdx))
        (.arrayLit (outs.map valVar))
    let insertCall : RustStmt := .exprStmt (method (funQueriesAt funIdx) "finish_hashed"
      #[sliceRef (.var "inp"), sliceRef (.var "__ret"), notUnconstrained, .var "input_hash"])
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
      arms := arms.push { pat := .litU64 key.n, body := { stmts := armBody } }
    let dfltBody ← (match dflt? with
      | some d => withSavedNextVal (emitBlock funIdx mcLabel? d)
      | none => pure #[
          .returnStmt
            (.call (.var "Err")
              #[.call (.path #["ExecError", "MatchNoCase"])
                #[canonical (valVar valIdx)]])])
    arms := arms.push { pat := .wildcard, body := { stmts := dfltBody } }
    return #[.matchStmt
      (canonical (valVar valIdx))
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
      arms := arms.push { pat := .litU64 key.n, body := { stmts := armBody } }
    let dfltBody ← (match dflt? with
      | some d => withSavedNextVal (emitBlock funIdx (some label) d)
      | none => pure #[
          .returnStmt
            (.call (.var "Err")
              #[.call (.path #["ExecError", "MatchNoCase"])
                #[canonical (valVar valIdx)]])])
    arms := arms.push { pat := .wildcard, body := { stmts := dfltBody } }
    let matchStmt : RustStmt :=
      .matchStmt (canonical (valVar valIdx)) arms
    -- Reserve `outputSize` slots at outer scope for the yielded values.
    let outBase ← allocVals outputSize
    let yieldedLet : RustStmt :=
      .letStmt false s!"__mc_out_{label}" (some (gArray outputSize))
        (.labeledBlock label { stmts := #[matchStmt] })
    let mut splat : Array RustStmt := #[]
    for k in [0 : outputSize] do
      splat := splat.push
        (declVal (outBase + k)
          (.index (.var s!"__mc_out_{label}") (.nat k)))
    let contStmts ← emitBlock funIdx mcLabel? continuation
    return #[yieldedLet] ++ splat ++ contStmts
  | .yield _ outs =>
    -- Yield: bubble values to the enclosing `MatchContinue`'s labeled
    -- block via `break '__mc_N [...];`. Only valid inside a
    -- MatchContinue case body, so `mcLabel?` MUST be set; if it isn't,
    -- emit a panic so the failure is obvious during testing.
    match mcLabel? with
    | some label =>
      return #[.breakWith label (.arrayLit (outs.map valVar))]
    | none =>
      return #[.exprStmt
        (.macroCall "unreachable" #[.string "Ctrl::Yield outside of MatchContinue context"])]

end


/-! ## Functions and module emission -/

def emitFunction (funIdx : FunIdx) (f : Function)
    (memorySizes : Array Nat := #[]) : Array RustItem :=
  let inSize := f.layout.inputSize
  let outSize := (findReturnArity f.body).getD 0
  let bindInputs := (Array.range inSize).map fun i =>
    declVal i (.index (.var "inp") (.nat i))
  let initState : EmitState := { nextVal := inSize, nextLabel := 0, memorySizes }
  let (stmts, _) := (emitBlock funIdx none f.body).run initState
  let body : RustBlock := {
    stmts := #[.letStmt false "unconstrained" none (.var "UNCONSTRAINED")] ++ bindInputs ++ stmts
  }
  -- Preserve stack growth at every function entry: 64 KiB red zone, 4 MiB segment.
  let guarded := .call (.path #["stacker", "maybe_grow"]) #[
    .binop .mul (.nat 64) (.nat 1024),
    .binop .mul (.binop .mul (.nat 4) (.nat 1024)) (.nat 1024),
    .closure #[] (.block body)]
  #[
    .constUsize s!"INPUT_SIZE_{funIdx}" inSize,
    .constUsize s!"IN_{funIdx}" inSize,
    .constUsize s!"OUT_{funIdx}" outSize,
    .function {
      name := s!"aiur_fn_{funIdx}"
      constParams := #[("UNCONSTRAINED", .named "bool")]
      params := #[
        ("inp", inputTy funIdx), ("input_hash", .named "u64"),
        ("record", .ref true (.named "QueryRecord")),
        ("io_buffer", .ref true (.named "IOBuffer"))]
      returnTy := resultTy (outputTy funIdx)
      body := tailBlock guarded
    }
  ]

/-- Entry dispatch validates the fixed memory-table layout before any mutation.
    Generated functions and runtime helpers only insert rows, never tables. -/
def emitDispatch (tl : Toplevel) : RustItem := Id.run do
  let mut arms : Array MatchArm := #[]
  for funIdx in [0 : tl.functions.size] do
    arms := arms.push {
      pat := .litU64 funIdx
      body := { stmts := #[
        .letStmt false "__inp" (some (inputTy funIdx))
          (expect (method (.var "args") "try_into") "input size mismatch"),
        .letStmt false "__out" none
          (nativeCall funIdx (.bool false) (.var "__inp") (.var "__input_hash")),
        .returnStmt (.call (.var "Ok") #[method (.var "__out") "to_vec"])
      ] }
    }
  arms := arms.push {
    pat := .wildcard
    body := { stmts := #[returnError (errorValue "InvalidFunIdx" #[.var "fun_idx"])] }
  }
  let mut body : Array RustStmt := #[]
  for slot in [0 : tl.memorySizes.size] do
    let size := tl.memorySizes[slot]!
    let actual := method
      (method (.field (.var "record") "memory_queries") "get_index" #[.nat slot])
      "map" #[.closure #[.tuple #[.binding "size", .wildcard]] (.deref (.var "size"))]
    body := body.push (.ifStmt
      (.binop .ne actual (.call (.var "Some") #[.nat size]))
      #[returnError (errorValue "InvalidMemorySize" #[.nat size])] none)
  body := body.push (.letStmt false "__input_hash" none
    (.call (.path #["aiur", "querymap", "hash_g_slice"]) #[.var "args"]))
  body := body.push (.matchStmt (.cast (.var "fun_idx") (.named "u64")) arms)
  return .function {
    name := "execute_generated"
    visibility := .crate
    params := #[
      ("fun_idx", .named "usize"), ("args", .ref false (.slice gTy)),
      ("record", .ref true (.named "QueryRecord")),
      ("io_buffer", .ref true (.named "IOBuffer"))]
    returnTy := resultTy (.app "Vec" #[gTy])
    body := { stmts := body }
  }

/-- Fixed module-level boilerplate only. Runtime helper paths are carried
    explicitly by expressions, so no rendered-source scanning is needed. -/
def emitPreludeHeader : String :=
  "// Auto-generated by Aiur codegen. Do not edit.\n\
   // Mirrors crates/aiur/src/execute.rs QueryRecord side effects.\n\
   #![cfg_attr(rustfmt, rustfmt::skip)]\n\
   #![allow(unused_variables, unused_assignments, unused_mut, dead_code,\n\
   unused_parens, non_snake_case, clippy::all,\n\
   clippy::ptr_as_ptr, clippy::match_same_arms,\n\
   clippy::large_types_passed_by_value)]\n\
   use multi_stark::p3_field::{PrimeCharacteristicRing, PrimeField64};\n\
   use aiur::G;\n\
   use aiur::execute::{ExecError, IOBuffer, QueryRecord};\n\n"

/-- Build syntax for the complete module before rendering any source. -/
def emitItems (tl : Toplevel) : Array RustItem := Id.run do
  let mut items := #[]
  for funIdx in [0 : tl.functions.size] do
    items := items ++ emitFunction funIdx tl.functions[funIdx]! tl.memorySizes
  return items.push (emitDispatch tl)

def emit (tl : Toplevel) : String :=
  emitPreludeHeader ++
    (String.join ((emitItems tl).toList.map RustItem.toStr)).trimAsciiEnd.toString ++ "\n"

end Aiur.Codegen
end
