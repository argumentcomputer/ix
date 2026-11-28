import IxCCAiur.TypedLower
import IxCCAiur.World
import Aiur.Library.U32.Correctness
import Aiur.Library.U8Facts

/-! # World Verification for Typed / Demand-Linked Programs (`IxCCAiur.TypedWorld`)

Checks the prepared Formal Aiur source for a typed `LoweredProgram` according
to its linked `TableTier`:
* `.none` — only `World.checkFunctions` (zero tables!);
* `.byte256` — `checkU8ByteTable` (256-row `U8Byte::check` map + tables) and
  `World.checkFunctions`;
* `.u32` — `World.checkTables`, `checkU32Functions`, and `World.checkFunctions`;
* `.u64` — `World.checkTables`, `checkU32Functions`, `Gadgets.checkU64Functions`,
  and `World.checkFunctions`.

Also proves:
* `u8ByteSpec_of_check`: exact operational contract of `U8Byte::check` from the
  256-row table check;
* `u32LibraryWorld_of_check`: soundness of `checkU32Functions` for `U32LibraryWorld`;
* `u32Contracts_of_check`: full operational `EvalFn` contracts (`U32LibraryContracts`)
  for the `UInt8` and `UInt32` library operations from `World.checkTables` and
  `checkU32Functions` over any `Aiur.Library.U32.Compatible F` field.

Zero `sorry`, zero `admit`, zero `axiom`, zero `native_decide`, zero `bv_decide`. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.TypedWorld

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxCC.AiurBackend.Lower IxCC.AiurBackend.Gadgets IxCC.AiurBackend.World
open IxCC.AiurBackend.TypedRep IxCC.AiurBackend.TypedLower

variable {F : Type} [Field F] [DecidableEq F]

/-! ## Slim 256-Row `U8Byte::check` Table Specification & Check -/

/-- Exact map specification for `U8Byte::check(x : Field) -> ()`. -/
def U8ByteSpec (world : World F) : Prop :=
  ∀ v h r h',
    EvalFn world "U8Byte::check" [v] h r h' →
    r = .tuple [] ∧ h' = h ∧ ∃ b : Nat, b < 256 ∧ v = .field (b : F)

/-- Executable check that `U8Byte::check` is a static map over the exact 256-row
`byte_inputs` / `byte_units` tables. -/
def checkU8ByteTable (s : Generic.Source F) : Bool :=
  checkNoFunction s "U8Byte::check" &&
  checkMap s "U8Byte::check" "U8Byte::byte_inputs" "U8Byte::byte_units" &&
  checkTable s "U8Byte::byte_inputs"
    ((List.range 256).map fun (x : Nat) => .tuple [.field (x : F)]) &&
  checkTable s "U8Byte::byte_units"
    ((List.range 256).map fun (_ : Nat) => .tuple [])

/-! ## `UInt32` Library Body Definitions, Check, and Contracts -/

/-- Checked 32-bit word value: 4 little-endian byte fields `< 256` packing to `n`.
Definitionally identical to `TypedGadgets.isU32Val`. -/
def isU32Word (n : Nat) (v : SourceValue F) : Prop :=
  ∃ b0 b1 b2 b3 : Nat,
    b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 ∧
    n = U32.pack b0 b1 b2 b3 ∧
    v = .tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)]

private abbrev u8f (e : Aiur.Generic.Expr F) : Aiur.Generic.Expr F :=
  .call "UInt8::to_field" (some []) [e]

/-- Expected elaborated body of `UInt8::to_field(byte)`. -/
def u8ToFieldExpr : Aiur.Generic.Expr F := .var "byte"

/-- Expected elaborated body of `UInt8::from_fields(a, b)`. -/
def u8FromFieldsExpr : Aiur.Generic.Expr F :=
  .letValue .wildcard (.call "UInt8::range_pair" (some []) [.var "a", .var "b"])
    (.tuple [.var "a", .var "b"])

/-- Expected elaborated body of `UInt8::raw_and(a, b)`. -/
def u8RawAndExpr : Aiur.Generic.Expr F :=
  .letValue (.bind "x") (.call "UInt8::raw_xor" (some []) [.var "a", .var "b"])
    (.binary .div (.binary .sub (.binary .add (.var "a") (.var "b")) (.var "x")) (.literal (2 : F)))

/-- Expected elaborated body of `UInt8::raw_or(a, b)`. -/
def u8RawOrExpr : Aiur.Generic.Expr F :=
  .letValue (.bind "x") (.call "UInt8::raw_xor" (some []) [.var "a", .var "b"])
    (.binary .div (.binary .add (.binary .add (.var "a") (.var "b")) (.var "x")) (.literal (2 : F)))

/-- Expected elaborated body of `UInt8::and(a, b)`. -/
def u8AndExpr : Aiur.Generic.Expr F :=
  .call "UInt8::raw_and" (some []) [.var "a", .var "b"]

/-- Expected elaborated body of `UInt8::or(a, b)`. -/
def u8OrExpr : Aiur.Generic.Expr F :=
  .call "UInt8::raw_or" (some []) [.var "a", .var "b"]

/-- Expected elaborated body of `UInt8::xor(a, b)`. -/
def u8XorExpr : Aiur.Generic.Expr F :=
  .call "UInt8::raw_xor" (some []) [.var "a", .var "b"]

/-- Expected elaborated body of `UInt8::xor_split4(a, b)`. -/
def u8XorSplit4Body : Aiur.Generic.Expr F :=
  .call "UInt8::raw_xor_split4" (some []) [.var "a", .var "b"]

/-- Expected elaborated body of `UInt8::xor_split7(a, b)`. -/
def u8XorSplit7Body : Aiur.Generic.Expr F :=
  .call "UInt8::raw_xor_split7" (some []) [.var "a", .var "b"]

/-- Expected elaborated body of `UInt8::join4(high, low)` and `UInt8::join7(high, low)`. -/
def u8JoinBody : Aiur.Generic.Expr F :=
  .binary .add (.project (.var "high") 0) (.project (.var "low") 1)

/-- Expected elaborated body of `UInt32::from_bytes(bytes)`. -/
def u32FromBytesBody : Aiur.Generic.Expr F := .var "bytes"

/-- Expected elaborated body of `UInt32::to_bytes(word)`. -/
def u32ToBytesBody : Aiur.Generic.Expr F := .var "word"

/-- Expected elaborated body of `UInt32::compact_field(word)`. -/
def u32CompactFieldBody : Aiur.Generic.Expr F := .var "word"

/-- Expected elaborated body of `UInt32::compact(word)`. -/
def u32CompactBody : Aiur.Generic.Expr F :=
  .binary .add
    (.binary .add
      (.binary .add (u8f (.index (.var "word") 0))
        (.binary .mul (.literal (256 : F)) (u8f (.index (.var "word") 1))))
      (.binary .mul (.literal (65536 : F)) (u8f (.index (.var "word") 2))))
    (.binary .mul (.literal (16777216 : F)) (u8f (.index (.var "word") 3)))

/-- Expected elaborated body of `UInt32::from_fields(raw)`. -/
def u32FromFieldsBody : Aiur.Generic.Expr F :=
  .letValue (.tuple [.bind "b0", .bind "b1"])
    (.call "UInt8::from_fields" (some []) [.index (.var "raw") 0, .index (.var "raw") 1]) <|
  .letValue (.tuple [.bind "b2", .bind "b3"])
    (.call "UInt8::from_fields" (some []) [.index (.var "raw") 2, .index (.var "raw") 3]) <|
  .array [.var "b0", .var "b1", .var "b2", .var "b3"]

/-- Expected elaborated body of `UInt32::from_field(value)`. -/
def u32FromFieldBody : Aiur.Generic.Expr F :=
  .letValue (.bind "raw") (.hint (.array .field 4) (.var "value") "u32.bytes") <|
  .letValue (.bind "word") (.call "UInt32::from_fields" (some []) [.var "raw"]) <|
  .letValue .wildcard
    (.builtin (.assertEq { message := some "u32 decomposition", runtimeCheck := false })
      [.call "UInt32::compact" (some []) [.var "word"], .var "value"]) <|
  .var "word"

private def u32WordFieldsExpr (v : String) : Aiur.Generic.Expr F :=
  .array [u8f (.index (.var v) 0), u8f (.index (.var v) 1),
          u8f (.index (.var v) 2), u8f (.index (.var v) 3)]

/-- Expected elaborated body of `UInt32::add(a, b)`. -/
def u32AddBody : Aiur.Generic.Expr F :=
  .letValue (.bind "raw")
    (.hint (.array .field 4) (.tuple [u32WordFieldsExpr "a", u32WordFieldsExpr "b"]) "u32.add") <|
  .letValue (.bind "result") (.call "UInt32::from_fields" (some []) [.var "raw"]) <|
  .letValue (.bind "carry")
    (.binary .div
      (.binary .sub
        (.binary .add (.call "UInt32::compact" (some []) [.var "a"])
                      (.call "UInt32::compact" (some []) [.var "b"]))
        (.call "UInt32::compact" (some []) [.var "result"]))
      (.literal (4294967296 : F))) <|
  .letValue .wildcard
    (.builtin (.assertEq { message := some "u32 add carry", runtimeCheck := false })
      [.binary .mul (.var "carry") (.binary .sub (.var "carry") (.literal (1 : F))),
       .literal (0 : F)]) <|
  .var "result"

/-- Expected elaborated body of `UInt32::add3(a, b, c)`. -/
def u32Add3Body : Aiur.Generic.Expr F :=
  .letValue (.bind "raw")
    (.hint (.array .field 4)
      (.tuple [u32WordFieldsExpr "a", u32WordFieldsExpr "b", u32WordFieldsExpr "c"]) "u32.add3") <|
  .letValue (.bind "result") (.call "UInt32::from_fields" (some []) [.var "raw"]) <|
  .letValue (.bind "carry")
    (.binary .div
      (.binary .sub
        (.binary .add
          (.binary .add (.call "UInt32::compact" (some []) [.var "a"])
                        (.call "UInt32::compact" (some []) [.var "b"]))
          (.call "UInt32::compact" (some []) [.var "c"]))
        (.call "UInt32::compact" (some []) [.var "result"]))
      (.literal (4294967296 : F))) <|
  .letValue .wildcard
    (.builtin (.assertEq { message := some "u32 add3 carry", runtimeCheck := false })
      [.binary .mul
         (.binary .mul (.var "carry") (.binary .sub (.var "carry") (.literal (1 : F))))
         (.binary .sub (.var "carry") (.literal (2 : F))),
       .literal (0 : F)]) <|
  .var "result"

/-- Expected elaborated body of `UInt32::sub_borrow(a, b)`. -/
def u32SubBorrowBody : Aiur.Generic.Expr F :=
  .letValue (.bind "raw")
    (.hint (.array .field 4)
      (.tuple [.call "UInt32::compact_field" (some []) [.var "a"],
               .call "UInt32::compact_field" (some []) [.var "b"]]) "u32.sub") <|
  .letValue (.bind "result") (.call "UInt32::from_fields" (some []) [.var "raw"]) <|
  .letValue (.bind "borrow")
    (.binary .div
      (.binary .sub
        (.binary .add (.call "UInt32::compact" (some []) [.var "result"]) (.var "b"))
        (.var "a"))
      (.literal (4294967296 : F))) <|
  .letValue .wildcard
    (.builtin (.assertEq { message := some "u32 subtraction borrow", runtimeCheck := false })
      [.binary .mul (.var "borrow") (.binary .sub (.var "borrow") (.literal (1 : F))),
       .literal (0 : F)]) <|
  .tuple [.var "result", .var "borrow"]

/-- Expected elaborated body of `UInt32::sub(a, b)`. -/
def u32SubBody : Aiur.Generic.Expr F :=
  .project (.call "UInt32::sub_borrow" (some [])
    [.call "UInt32::compact" (some []) [.var "a"],
     .call "UInt32::compact" (some []) [.var "b"]]) 0

/-- Expected elaborated body of `UInt32::compact_less_than(a, b)`. -/
def u32CompactLessThanBody : Aiur.Generic.Expr F :=
  .project (.call "UInt32::sub_borrow" (some []) [.var "a", .var "b"]) 1

/-- Expected elaborated body of `UInt32::less_than(a, b)`. -/
def u32LessThanBody : Aiur.Generic.Expr F :=
  .call "UInt32::compact_less_than" (some [])
    [.call "UInt32::compact" (some []) [.var "a"],
     .call "UInt32::compact" (some []) [.var "b"]]

/-- Expected elaborated body of `UInt32::{xor,and,or}(a, b)`. -/
def u32BitwiseBody (op : String) : Aiur.Generic.Expr F :=
  .array
    [.call op (some []) [.index (.var "a") 0, .index (.var "b") 0],
     .call op (some []) [.index (.var "a") 1, .index (.var "b") 1],
     .call op (some []) [.index (.var "a") 2, .index (.var "b") 2],
     .call op (some []) [.index (.var "a") 3, .index (.var "b") 3]]

/-- Expected elaborated body of `UInt32::rotr8(a)`. -/
def u32Rotr8Body : Aiur.Generic.Expr F :=
  .array [.index (.var "a") 1, .index (.var "a") 2, .index (.var "a") 3, .index (.var "a") 0]

/-- Expected elaborated body of `UInt32::rotr16(a)`. -/
def u32Rotr16Body : Aiur.Generic.Expr F :=
  .array [.index (.var "a") 2, .index (.var "a") 3, .index (.var "a") 0, .index (.var "a") 1]

/-- Expected elaborated body of `UInt32::xor_rotr7(a, b)`. -/
def u32XorRotr7Body : Aiur.Generic.Expr F :=
  .letValue (.bind "p0") (.call "UInt8::xor_split7" (some []) [.index (.var "a") 0, .index (.var "b") 0]) <|
  .letValue (.bind "p1") (.call "UInt8::xor_split7" (some []) [.index (.var "a") 1, .index (.var "b") 1]) <|
  .letValue (.bind "p2") (.call "UInt8::xor_split7" (some []) [.index (.var "a") 2, .index (.var "b") 2]) <|
  .letValue (.bind "p3") (.call "UInt8::xor_split7" (some []) [.index (.var "a") 3, .index (.var "b") 3]) <|
  .array
    [.call "UInt8::join7" (some []) [.var "p0", .var "p1"],
     .call "UInt8::join7" (some []) [.var "p1", .var "p2"],
     .call "UInt8::join7" (some []) [.var "p2", .var "p3"],
     .call "UInt8::join7" (some []) [.var "p3", .var "p0"]]

/-- Expected elaborated body of `UInt32::xor_rotr12(a, b)`. -/
def u32XorRotr12Body : Aiur.Generic.Expr F :=
  .letValue (.bind "p0") (.call "UInt8::xor_split4" (some []) [.index (.var "a") 0, .index (.var "b") 0]) <|
  .letValue (.bind "p1") (.call "UInt8::xor_split4" (some []) [.index (.var "a") 1, .index (.var "b") 1]) <|
  .letValue (.bind "p2") (.call "UInt8::xor_split4" (some []) [.index (.var "a") 2, .index (.var "b") 2]) <|
  .letValue (.bind "p3") (.call "UInt8::xor_split4" (some []) [.index (.var "a") 3, .index (.var "b") 3]) <|
  .array
    [.call "UInt8::join4" (some []) [.var "p1", .var "p2"],
     .call "UInt8::join4" (some []) [.var "p2", .var "p3"],
     .call "UInt8::join4" (some []) [.var "p3", .var "p0"],
     .call "UInt8::join4" (some []) [.var "p0", .var "p1"]]

/-- World hypothesis for the linked `Aiur.Library.U32.source` library. -/
structure U32LibraryWorld (world : World F) : Prop where
  maps : U8MapSpec world
  u8_to_field : WorldHasFn world "UInt8::to_field" ["byte"] u8ToFieldExpr
  u8_from_fields : WorldHasFn world "UInt8::from_fields" ["a", "b"] u8FromFieldsExpr
  u8_raw_and : WorldHasFn world "UInt8::raw_and" ["a", "b"] u8RawAndExpr
  u8_raw_or : WorldHasFn world "UInt8::raw_or" ["a", "b"] u8RawOrExpr
  u8_and : WorldHasFn world "UInt8::and" ["a", "b"] u8AndExpr
  u8_or : WorldHasFn world "UInt8::or" ["a", "b"] u8OrExpr
  u8_xor : WorldHasFn world "UInt8::xor" ["a", "b"] u8XorExpr
  u8_xor_split4 : WorldHasFn world "UInt8::xor_split4" ["a", "b"] u8XorSplit4Body
  u8_xor_split7 : WorldHasFn world "UInt8::xor_split7" ["a", "b"] u8XorSplit7Body
  u8_join4 : WorldHasFn world "UInt8::join4" ["high", "low"] u8JoinBody
  u8_join7 : WorldHasFn world "UInt8::join7" ["high", "low"] u8JoinBody
  u32_from_bytes : WorldHasFn world "UInt32::from_bytes" ["bytes"] u32FromBytesBody
  u32_to_bytes : WorldHasFn world "UInt32::to_bytes" ["word"] u32ToBytesBody
  u32_compact_field : WorldHasFn world "UInt32::compact_field" ["word"] u32CompactFieldBody
  u32_compact : WorldHasFn world "UInt32::compact" ["word"] u32CompactBody
  u32_from_fields : WorldHasFn world "UInt32::from_fields" ["raw"] u32FromFieldsBody
  u32_from_field : WorldHasFn world "UInt32::from_field" ["value"] u32FromFieldBody
  u32_add : WorldHasFn world "UInt32::add" ["a", "b"] u32AddBody
  u32_add3 : WorldHasFn world "UInt32::add3" ["a", "b", "c"] u32Add3Body
  u32_sub_borrow : WorldHasFn world "UInt32::sub_borrow" ["a", "b"] u32SubBorrowBody
  u32_sub : WorldHasFn world "UInt32::sub" ["a", "b"] u32SubBody
  u32_compact_less_than : WorldHasFn world "UInt32::compact_less_than" ["a", "b"] u32CompactLessThanBody
  u32_less_than : WorldHasFn world "UInt32::less_than" ["a", "b"] u32LessThanBody
  u32_xor : WorldHasFn world "UInt32::xor" ["a", "b"] (u32BitwiseBody "UInt8::xor")
  u32_and : WorldHasFn world "UInt32::and" ["a", "b"] (u32BitwiseBody "UInt8::and")
  u32_or : WorldHasFn world "UInt32::or" ["a", "b"] (u32BitwiseBody "UInt8::or")
  u32_rotr8 : WorldHasFn world "UInt32::rotr8" ["a"] u32Rotr8Body
  u32_rotr16 : WorldHasFn world "UInt32::rotr16" ["a"] u32Rotr16Body
  u32_xor_rotr7 : WorldHasFn world "UInt32::xor_rotr7" ["a", "b"] u32XorRotr7Body
  u32_xor_rotr12 : WorldHasFn world "UInt32::xor_rotr12" ["a", "b"] u32XorRotr12Body

/-- Computable checker verifying that a prepared `Generic.Source` contains all 30
exact `UInt8`/`UInt32` library functions used by the `.u32` and `.u64` tiers. -/
def checkU32Functions (s : Generic.Source F) : Bool :=
  let checkFn (nm : String) (ps : List String) (body : Aiur.Generic.Expr F) : Bool :=
    match s.program.findFunction? nm with
    | some f => f.typeParams.isEmpty && (f.params.map Prod.fst == ps) && (f.body == body)
    | none => false
  checkFn "UInt8::to_field" ["byte"] u8ToFieldExpr &&
  checkFn "UInt8::from_fields" ["a", "b"] u8FromFieldsExpr &&
  checkFn "UInt8::raw_and" ["a", "b"] u8RawAndExpr &&
  checkFn "UInt8::raw_or" ["a", "b"] u8RawOrExpr &&
  checkFn "UInt8::and" ["a", "b"] u8AndExpr &&
  checkFn "UInt8::or" ["a", "b"] u8OrExpr &&
  checkFn "UInt8::xor" ["a", "b"] u8XorExpr &&
  checkFn "UInt8::xor_split4" ["a", "b"] u8XorSplit4Body &&
  checkFn "UInt8::xor_split7" ["a", "b"] u8XorSplit7Body &&
  checkFn "UInt8::join4" ["high", "low"] u8JoinBody &&
  checkFn "UInt8::join7" ["high", "low"] u8JoinBody &&
  checkFn "UInt32::from_bytes" ["bytes"] u32FromBytesBody &&
  checkFn "UInt32::to_bytes" ["word"] u32ToBytesBody &&
  checkFn "UInt32::compact_field" ["word"] u32CompactFieldBody &&
  checkFn "UInt32::compact" ["word"] u32CompactBody &&
  checkFn "UInt32::from_fields" ["raw"] u32FromFieldsBody &&
  checkFn "UInt32::from_field" ["value"] u32FromFieldBody &&
  checkFn "UInt32::add" ["a", "b"] u32AddBody &&
  checkFn "UInt32::add3" ["a", "b", "c"] u32Add3Body &&
  checkFn "UInt32::sub_borrow" ["a", "b"] u32SubBorrowBody &&
  checkFn "UInt32::sub" ["a", "b"] u32SubBody &&
  checkFn "UInt32::compact_less_than" ["a", "b"] u32CompactLessThanBody &&
  checkFn "UInt32::less_than" ["a", "b"] u32LessThanBody &&
  checkFn "UInt32::xor" ["a", "b"] (u32BitwiseBody "UInt8::xor") &&
  checkFn "UInt32::and" ["a", "b"] (u32BitwiseBody "UInt8::and") &&
  checkFn "UInt32::or" ["a", "b"] (u32BitwiseBody "UInt8::or") &&
  checkFn "UInt32::rotr8" ["a"] u32Rotr8Body &&
  checkFn "UInt32::rotr16" ["a"] u32Rotr16Body &&
  checkFn "UInt32::xor_rotr7" ["a", "b"] u32XorRotr7Body &&
  checkFn "UInt32::xor_rotr12" ["a", "b"] u32XorRotr12Body

/-- Operational `EvalFn` contracts for the `UInt8`/`UInt32` library operations,
discharged from `World.checkTables` and `checkU32Functions` (`u32Contracts_of_check`). -/
structure U32LibraryContracts (world : World F) : Prop where
  u8_to_field : ∀ v h r h',
    EvalFn world "UInt8::to_field" [v] h r h' → r = v ∧ h' = h
  u8_from_fields : ∀ v1 v2 h r h',
    EvalFn world "UInt8::from_fields" [v1, v2] h r h' →
    r = .tuple [v1, v2] ∧ h' = h ∧
    ∃ a b : Nat, a < 256 ∧ b < 256 ∧ v1 = .field (a : F) ∧ v2 = .field (b : F)
  u8_xor : ∀ (a b : Nat) h r h', a < 256 → b < 256 →
    EvalFn world "UInt8::xor" [.field (a : F), .field (b : F)] h r h' →
    r = .field ((Nat.xor a b : Nat) : F) ∧ h' = h
  u8_and : ∀ (a b : Nat) h r h', a < 256 → b < 256 →
    EvalFn world "UInt8::and" [.field (a : F), .field (b : F)] h r h' →
    r = .field ((Nat.land a b : Nat) : F) ∧ h' = h
  u8_or : ∀ (a b : Nat) h r h', a < 256 → b < 256 →
    EvalFn world "UInt8::or" [.field (a : F), .field (b : F)] h r h' →
    r = .field ((Nat.lor a b : Nat) : F) ∧ h' = h
  from_bytes : ∀ n w h r h', isU32Word n w →
    EvalFn world "UInt32::from_bytes" [w] h r h' → r = w ∧ h' = h
  to_bytes : ∀ n w h r h', isU32Word n w →
    EvalFn world "UInt32::to_bytes" [w] h r h' → r = w ∧ h' = h
  compact : ∀ n w h r h', isU32Word n w →
    EvalFn world "UInt32::compact" [w] h r h' → r = .field (n : F) ∧ h' = h
  compact_field : ∀ v h r h',
    EvalFn world "UInt32::compact_field" [v] h r h' → r = v ∧ h' = h
  from_fields : ∀ v0 v1 v2 v3 h r h',
    EvalFn world "UInt32::from_fields" [.tuple [v0, v1, v2, v3]] h r h' →
    ∃ b0 b1 b2 b3 : Nat,
      b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 ∧
      v0 = .field (b0 : F) ∧ v1 = .field (b1 : F) ∧
      v2 = .field (b2 : F) ∧ v3 = .field (b3 : F) ∧
      isU32Word (U32.pack b0 b1 b2 b3) r ∧ h' = h
  from_field : ∀ v h r h',
    EvalFn world "UInt32::from_field" [v] h r h' →
    ∃ n, n < U32.base ∧ v = .field (n : F) ∧ isU32Word n r ∧ h' = h
  add : ∀ a b wa wb h r h', isU32Word a wa → isU32Word b wb →
    EvalFn world "UInt32::add" [wa, wb] h r h' →
    isU32Word ((a + b) % U32.base) r ∧ h' = h
  add3 : ∀ a b c wa wb wc h r h', isU32Word a wa → isU32Word b wb → isU32Word c wc →
    EvalFn world "UInt32::add3" [wa, wb, wc] h r h' →
    isU32Word ((a + b + c) % U32.base) r ∧ h' = h
  sub_borrow : ∀ a b h r h', a < U32.base → b < U32.base →
    EvalFn world "UInt32::sub_borrow" [.field (a : F), .field (b : F)] h r h' →
    ∃ wd, isU32Word ((a + U32.base - b) % U32.base) wd ∧
      r = .tuple [wd, .field (if a < b then 1 else 0)] ∧ h' = h
  sub : ∀ a b wa wb h r h', isU32Word a wa → isU32Word b wb →
    EvalFn world "UInt32::sub" [wa, wb] h r h' →
    isU32Word ((a + U32.base - b) % U32.base) r ∧ h' = h
  compact_less_than : ∀ a b h r h', a < U32.base → b < U32.base →
    EvalFn world "UInt32::compact_less_than" [.field (a : F), .field (b : F)] h r h' →
    r = .field (if a < b then 1 else 0) ∧ h' = h
  less_than : ∀ a b wa wb h r h', isU32Word a wa → isU32Word b wb →
    EvalFn world "UInt32::less_than" [wa, wb] h r h' →
    r = .field (if a < b then 1 else 0) ∧ h' = h
  xor : ∀ a b wa wb h r h', isU32Word a wa → isU32Word b wb →
    EvalFn world "UInt32::xor" [wa, wb] h r h' →
    isU32Word (Nat.xor a b) r ∧ h' = h
  and : ∀ a b wa wb h r h', isU32Word a wa → isU32Word b wb →
    EvalFn world "UInt32::and" [wa, wb] h r h' →
    isU32Word (a &&& b) r ∧ h' = h
  or : ∀ a b wa wb h r h', isU32Word a wa → isU32Word b wb →
    EvalFn world "UInt32::or" [wa, wb] h r h' →
    isU32Word (a ||| b) r ∧ h' = h
  rotr8 : ∀ a wa h r h', isU32Word a wa →
    EvalFn world "UInt32::rotr8" [wa] h r h' →
    isU32Word ((a / 256) + (a % 256) * 16777216) r ∧ h' = h
  rotr16 : ∀ a wa h r h', isU32Word a wa →
    EvalFn world "UInt32::rotr16" [wa] h r h' →
    isU32Word ((a / 65536) + (a % 65536) * 65536) r ∧ h' = h

/-- Executable tier-aware world check for a typed `LoweredProgram`. -/
def checkTypedWorld (s : Generic.Source F) (lp : LoweredProgram) : Bool :=
  let tablesOk := match lp.tier with
    | .none => true
    | .byte256 => checkU8ByteTable s
    | .u32 => checkTables s && checkU32Functions s
    | .u64 => checkTables s && checkU32Functions s && checkU64Functions s
  tablesOk && checkFunctions s lp.program

/-! ## Soundness of `checkU8ByteTable` -/

omit [Field F] [DecidableEq F] in
private theorem isPlainExpr_constantExpr :
    ∀ (c : Constant F), isPlainExpr (Generic.constantExpr c) = true
  | .field _ => by simp [Generic.constantExpr, isPlainExpr]
  | .tuple xs => by
    simp only [Generic.constantExpr, isPlainExpr, Lower.isPlainList_iff, List.mem_map]
    rintro _ ⟨y, hy, rfl⟩
    have : sizeOf y < sizeOf (Value.tuple xs) := by
      have := List.sizeOf_lt_of_mem hy
      simp [Value.tuple.sizeOf_spec]; omega
    exact isPlainExpr_constantExpr y
  | .construct n ctor xs => by
    simp only [Generic.constantExpr, isPlainExpr, Lower.isPlainList_iff, List.mem_map]
    rintro _ ⟨y, hy, rfl⟩
    have : sizeOf y < sizeOf (Value.construct n ctor xs) := by
      have := List.sizeOf_lt_of_mem hy
      simp [Value.construct.sizeOf_spec]; omega
    exact isPlainExpr_constantExpr y
  | .ptr _ a => Empty.elim a
termination_by c => sizeOf c

private theorem mem_zip_map_iff {α β γ : Type*} {xs : List α} {f : α → β} {g : α → γ}
    {p : β × γ} : p ∈ (xs.map f).zip (xs.map g) ↔ ∃ x ∈ xs, f x = p.1 ∧ g x = p.2 := by
  induction xs with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨x, hx, h1, h2⟩)
      · exact ⟨a, Or.inl rfl, rfl, rfl⟩
      · exact ⟨x, Or.inr hx, h1, h2⟩
    · rintro ⟨x, rfl | hx, h1, h2⟩
      · left; cases p; simp_all
      · exact Or.inr ⟨x, hx, h1, h2⟩

/-- Soundness of `checkU8ByteTable`: every evaluation of `U8Byte::check` proves
its argument is a field element `(b : F)` with `b < 256` and leaves the heap
unchanged. -/
theorem u8ByteSpec_of_check {s : Generic.Source F} (h : checkU8ByteTable s = true) :
    U8ByteSpec s.world := by
  simp only [checkU8ByteTable, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hNoFn, hMap, hIn, hOut⟩ := h
  have hNoFn' := checkNoFunction_sound hNoFn
  obtain ⟨m, hm, hmIn, hmOut⟩ := checkMap_sound hMap
  obtain ⟨tIn, htIn, htInRows⟩ := checkTable_sound hIn
  obtain ⟨tOut, htOut, htOutRows⟩ := checkTable_sound hOut
  intro v heap r heap' ev
  cases ev with
  | intro prep body =>
    simp only [Generic.Source.world, sourceWorld, hNoFn', bind, Except.bind, pure, Except.pure] at prep
    cases hlook : lookupMap s.tables "U8Byte::check" [v] with
    | error e => simp [hlook] at prep
    | ok row =>
      simp only [hlook, Except.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨rfl, rfl, rfl⟩ := prep
      obtain ⟨map, key, hfm, _, _, hkey, hmem, _⟩ := Aiur.lookupMap_spec hlook
      rw [hm, Option.some.injEq] at hfm; subst hfm
      simp only [Aiur.Program.mapRows, hmIn, hmOut, htIn, htOut, htInRows, htOutRows] at hmem
      obtain ⟨b, hb, hkeq, hreq⟩ := mem_zip_map_iff.mp hmem
      have hbLt : b < 256 := List.mem_range.mp hb
      subst hkeq hreq
      simp only [Generic.constantExpr, List.map_nil] at body
      cases body with
      | tuple hargs =>
        cases hargs
        have hv := Aiur.Value.toConstant_spec hkey
        simp only [Constant.toValue, Value.mapAddress, List.map, Value.tuple.injEq,
          List.cons.injEq, and_true] at hv
        exact ⟨rfl, rfl, b, hbLt, hv.symm⟩
  | returned prep body =>
    simp only [Generic.Source.world, sourceWorld, hNoFn', bind, Except.bind, pure, Except.pure] at prep
    cases hlook : lookupMap s.tables "U8Byte::check" [v] with
    | error e => simp [hlook] at prep
    | ok row =>
      simp only [hlook, Except.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨rfl, rfl, rfl⟩ := prep
      exact False.elim (no_evalExit_of_plain (isPlainExpr_constantExpr row) body)

/-! ## Soundness of `checkU32Functions` (`U32LibraryWorld` & `U32LibraryContracts`) -/

local macro "u32_lib_name" : tactic => `(tactic| first | decide | simp)

/-- Soundness of `checkU32Functions`: a source with the `UInt8` tables that passes
`checkU32Functions` satisfies `U32LibraryWorld s.world`. -/
theorem u32LibraryWorld_of_check (s : Generic.Source F) (tables : U8TablesMatch s)
    (h : checkU32Functions s = true) : U32LibraryWorld s.world := by
  simp only [checkU32Functions, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23,
    h24, h25, h26, h27, h28, h29, h30⟩ := h
  exact
    { maps := u8MapSpec_of_source s tables
      u8_to_field := worldHasFn_of_check s (by u32_lib_name) h1
      u8_from_fields := worldHasFn_of_check s (by u32_lib_name) h2
      u8_raw_and := worldHasFn_of_check s (by u32_lib_name) h3
      u8_raw_or := worldHasFn_of_check s (by u32_lib_name) h4
      u8_and := worldHasFn_of_check s (by u32_lib_name) h5
      u8_or := worldHasFn_of_check s (by u32_lib_name) h6
      u8_xor := worldHasFn_of_check s (by u32_lib_name) h7
      u8_xor_split4 := worldHasFn_of_check s (by u32_lib_name) h8
      u8_xor_split7 := worldHasFn_of_check s (by u32_lib_name) h9
      u8_join4 := worldHasFn_of_check s (by u32_lib_name) h10
      u8_join7 := worldHasFn_of_check s (by u32_lib_name) h11
      u32_from_bytes := worldHasFn_of_check s (by u32_lib_name) h12
      u32_to_bytes := worldHasFn_of_check s (by u32_lib_name) h13
      u32_compact_field := worldHasFn_of_check s (by u32_lib_name) h14
      u32_compact := worldHasFn_of_check s (by u32_lib_name) h15
      u32_from_fields := worldHasFn_of_check s (by u32_lib_name) h16
      u32_from_field := worldHasFn_of_check s (by u32_lib_name) h17
      u32_add := worldHasFn_of_check s (by u32_lib_name) h18
      u32_add3 := worldHasFn_of_check s (by u32_lib_name) h19
      u32_sub_borrow := worldHasFn_of_check s (by u32_lib_name) h20
      u32_sub := worldHasFn_of_check s (by u32_lib_name) h21
      u32_compact_less_than := worldHasFn_of_check s (by u32_lib_name) h22
      u32_less_than := worldHasFn_of_check s (by u32_lib_name) h23
      u32_xor := worldHasFn_of_check s (by u32_lib_name) h24
      u32_and := worldHasFn_of_check s (by u32_lib_name) h25
      u32_or := worldHasFn_of_check s (by u32_lib_name) h26
      u32_rotr8 := worldHasFn_of_check s (by u32_lib_name) h27
      u32_rotr16 := worldHasFn_of_check s (by u32_lib_name) h28
      u32_xor_rotr7 := worldHasFn_of_check s (by u32_lib_name) h29
      u32_xor_rotr12 := worldHasFn_of_check s (by u32_lib_name) h30 }

section U32Proofs

private theorem evalExpr_var_eq {world : World F} {locals : Environment F Nat}
    {nm : String} {v r : SourceValue F} {h h' : Heap F}
    (hlook : locals.find? (·.1 == nm) = some (nm, v))
    (ev : EvalExpr world [] locals (.var nm) h r h') :
    r = v ∧ h' = h := by
  obtain ⟨hl, rfl⟩ := evalExpr_var_inv ev
  rw [hlook, Option.some.injEq, Prod.mk.injEq] at hl
  exact ⟨hl.2.symm, rfl⟩

private theorem evalExpr_array4_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {e0 e1 e2 e3 : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.array [e0, e1, e2, e3]) h r h') :
    ∃ v0 v1 v2 v3 h1 h2 h3,
      EvalExpr world types locals e0 h v0 h1 ∧
      EvalExpr world types locals e1 h1 v1 h2 ∧
      EvalExpr world types locals e2 h2 v2 h3 ∧
      EvalExpr world types locals e3 h3 v3 h' ∧
      r = .tuple [v0, v1, v2, v3] := by
  cases ev with
  | array hargs =>
    cases hargs with | cons h0 t0 =>
    cases t0 with | cons h1 t1 =>
    cases t1 with | cons h2 t2 =>
    cases t2 with | cons h3 t3 =>
    cases t3
    exact ⟨_, _, _, _, _, _, _, h0, h1, h2, h3, rfl⟩

private theorem evalExpr_project_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {e : Aiur.Generic.Expr F} {idx : Nat} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.project e idx) h r h') :
    ∃ v, EvalExpr world types locals e h v h' ∧ projectValue v idx = .ok r := by
  cases ev with
  | project hv hp => exact ⟨_, hv, hp⟩

private theorem evalExpr_tuple3_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {e0 e1 e2 : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.tuple [e0, e1, e2]) h r h') :
    ∃ v0 v1 v2 h1 h2,
      EvalExpr world types locals e0 h v0 h1 ∧
      EvalExpr world types locals e1 h1 v1 h2 ∧
      EvalExpr world types locals e2 h2 v2 h' ∧
      r = .tuple [v0, v1, v2] := by
  cases ev with
  | tuple hargs =>
    cases hargs with | cons h0 t0 =>
    cases t0 with | cons h1 t1 =>
    cases t1 with | cons h2 t2 =>
    cases t2
    exact ⟨_, _, _, _, _, h0, h1, h2, rfl⟩

omit [DecidableEq F] in
private theorem u32Compat_two_ne_zero (hc : U32.Compatible F) : (2 : F) ≠ 0 := by
  intro h
  have h20 : (2 : Nat) = 0 :=
    hc (show 2 < 3 * U32.base by unfold U32.base; omega)
       (show 0 < 3 * U32.base by unfold U32.base; omega) (by simpa using h)
  omega

omit [DecidableEq F] in
private theorem u32Compat_byte_inj (hc : U32.Compatible F) {a b : Nat}
    (ha : a < 256) (hb : b < 256) (heq : (a : F) = (b : F)) : a = b :=
  hc (show a < 3 * U32.base by unfold U32.base; omega)
     (show b < 3 * U32.base by unfold U32.base; omega) heq

private theorem testBit_pack {b0 b1 b2 b3 : Nat}
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256) (k : Nat) :
    (U32.pack b0 b1 b2 b3).testBit k =
      if k < 8 then b0.testBit k
      else if k < 16 then b1.testBit (k - 8)
      else if k < 24 then b2.testBit (k - 16)
      else if k < 32 then b3.testBit (k - 24)
      else false := by
  have heq : U32.pack b0 b1 b2 b3 =
      2 ^ 8 * (2 ^ 8 * (2 ^ 8 * b3 + b2) + b1) + b0 := by
    unfold U32.pack; omega
  rw [heq, Nat.testBit_two_pow_mul_add _ (by omega : b0 < 2 ^ 8)]
  by_cases hk0 : k < 8
  · simp [hk0]
  · simp only [hk0, ↓reduceIte]
    rw [Nat.testBit_two_pow_mul_add _ (by omega : b1 < 2 ^ 8)]
    by_cases hk1 : k < 16
    · have : k - 8 < 8 := by omega
      simp [hk1, this]
    · have hn1 : ¬ (k - 8 < 8) := by omega
      simp only [hk1, hn1, ↓reduceIte]
      rw [Nat.testBit_two_pow_mul_add _ (by omega : b2 < 2 ^ 8)]
      by_cases hk2 : k < 24
      · have hsub : k - 8 - 8 = k - 16 := by omega
        have hlt : k - 16 < 8 := by omega
        simp [hk2, hsub, hlt]
      · have hn2 : ¬ (k - 8 - 8 < 8) := by omega
        simp only [hk2, hn2, ↓reduceIte]
        have hsub : k - 8 - 8 - 8 = k - 24 := by omega
        rw [hsub]
        by_cases hk3 : k < 32
        · simp [hk3]
        · simp only [hk3, ↓reduceIte]
          apply Nat.testBit_lt_two_pow
          calc b3 < 2 ^ 8 := h3
            _ ≤ 2 ^ (k - 24) := Nat.pow_le_pow_right (by omega) (by omega)

private theorem pack_bitwise (f : Bool → Bool → Bool) (hf : f false false = false)
    {a0 a1 a2 a3 b0 b1 b2 b3 : Nat}
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hc0 : Nat.bitwise f a0 b0 < 256) (hc1 : Nat.bitwise f a1 b1 < 256)
    (hc2 : Nat.bitwise f a2 b2 < 256) (hc3 : Nat.bitwise f a3 b3 < 256) :
    U32.pack (Nat.bitwise f a0 b0) (Nat.bitwise f a1 b1)
      (Nat.bitwise f a2 b2) (Nat.bitwise f a3 b3) =
    Nat.bitwise f (U32.pack a0 a1 a2 a3) (U32.pack b0 b1 b2 b3) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_pack hc0 hc1 hc2 hc3]
  rw [Nat.testBit_bitwise (x := U32.pack a0 a1 a2 a3) hf]
  rw [testBit_pack ha0 ha1 ha2 ha3, testBit_pack hb0 hb1 hb2 hb3]
  by_cases hk0 : k < 8
  · simp [hk0, Nat.testBit_bitwise hf]
  · by_cases hk1 : k < 16
    · simp [hk0, hk1, Nat.testBit_bitwise hf]
    · by_cases hk2 : k < 24
      · simp [hk0, hk1, hk2, Nat.testBit_bitwise hf]
      · by_cases hk3 : k < 32
        · simp [hk0, hk1, hk2, hk3, Nat.testBit_bitwise hf]
        · simp [hk0, hk1, hk2, hk3, hf]

private theorem land_lt_256 {a b : Nat} (ha : a < 256) (hb : b < 256) : Nat.land a b < 256 := by
  have h : Nat.land a b = (BitVec.ofNat 8 a &&& BitVec.ofNat 8 b).toNat := by
    simp [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rw [h]
  exact (BitVec.ofNat 8 a &&& BitVec.ofNat 8 b).isLt

private theorem lor_lt_256 {a b : Nat} (ha : a < 256) (hb : b < 256) : Nat.lor a b < 256 := by
  have h : Nat.lor a b = (BitVec.ofNat 8 a ||| BitVec.ofNat 8 b).toNat := by
    simp [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rw [h]
  exact (BitVec.ofNat 8 a ||| BitVec.ofNat 8 b).isLt

variable {world : World F}

private theorem u32lib_u8_to_field (lib : U32LibraryWorld world) {v r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt8::to_field" [v] h r h') : r = v ∧ h' = h := by
  obtain ⟨_, b⟩ := evalFn_plain_inv lib.u8_to_field rfl ev
  exact evalExpr_var_eq (by simp) b

private theorem u32lib_u8_from_fields (lib : U32LibraryWorld world) {v1 v2 r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt8::from_fields" [v1, v2] h r h') :
    r = .tuple [v1, v2] ∧ h' = h ∧
    ∃ a b : Nat, a < 256 ∧ b < 256 ∧ v1 = .field (a : F) ∧ v2 = .field (b : F) := by
  obtain ⟨_, b⟩ := evalFn_plain_inv lib.u8_from_fields rfl ev
  obtain ⟨_, _, hcall, hret⟩ := evalExpr_let_wildcard_inv b
  obtain ⟨va, vb, _, _, eva, evb, hcal⟩ := evalExpr_call2_inv hcall
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb
  obtain ⟨_, rfl, a, b', ha, hb, rfl, rfl⟩ := lib.maps.range_pair _ _ _ _ _ hcal
  obtain ⟨va', vb', _, eva', evb', rfl⟩ := evalExpr_tuple2_inv hret
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva'
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb'
  exact ⟨rfl, rfl, a, b', ha, hb, rfl, rfl⟩

private theorem u32lib_u8_xor (hc : U32.Compatible F) (lib : U32LibraryWorld world)
    {a b : Nat} (ha : a < 256) (hb : b < 256)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt8::xor" [.field (a : F), .field (b : F)] h r h') :
    r = .field ((Nat.xor a b : Nat) : F) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u8_xor rfl ev
  obtain ⟨va, vb, _, _, eva, evb, hcal⟩ := evalExpr_call2_inv body
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb
  obtain ⟨rfl, a', b', ha', hb', haEq, hbEq, rfl⟩ := lib.maps.raw_xor _ _ _ _ _ hcal
  have := u32Compat_byte_inj hc ha ha' (Value.field.inj haEq)
  have := u32Compat_byte_inj hc hb hb' (Value.field.inj hbEq)
  subst_vars
  exact ⟨rfl, rfl⟩

private theorem u32lib_u8_and (hc : U32.Compatible F) (lib : U32LibraryWorld world)
    {a b : Nat} (ha : a < 256) (hb : b < 256)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt8::and" [.field (a : F), .field (b : F)] h r h') :
    r = .field ((Nat.land a b : Nat) : F) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u8_and rfl ev
  obtain ⟨va, vb, _, _, eva, evb, hcal⟩ := evalExpr_call2_inv body
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb
  obtain ⟨_, body2⟩ := evalFn_plain_inv lib.u8_raw_and rfl hcal
  obtain ⟨vx, _, hcallx, hret⟩ := evalExpr_let_bind_inv body2
  obtain ⟨va', vb', _, _, eva', evb', hxor⟩ := evalExpr_call2_inv hcallx
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva'
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb'
  obtain ⟨rfl, a', b', ha', hb', haEq, hbEq, rfl⟩ := lib.maps.raw_xor _ _ _ _ _ hxor
  have ha1 : a' = a := u32Compat_byte_inj hc ha' ha (Value.field.inj haEq).symm
  have hb1 : b' = b := u32Compat_byte_inj hc hb' hb (Value.field.inj hbEq).symm
  subst a' b'
  obtain ⟨xn, yn, _, evnum, ev2, hdiv⟩ := evalExpr_binary_inv hret
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev2
  obtain ⟨xs, ys, _, evadd, evx, hsub⟩ := evalExpr_binary_inv evnum
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evx
  obtain ⟨xa, xb, _, eva2, evb2, hadd⟩ := evalExpr_binary_inv evadd
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb2
  simp only [evalBinOp, Except.ok.injEq] at hadd; subst hadd
  simp only [evalBinOp, Except.ok.injEq] at hsub; subst hsub
  have h2ne : (2 : F) ≠ 0 := u32Compat_two_ne_zero hc
  simp only [evalBinOp, h2ne, ↓reduceIte, Except.ok.injEq] at hdiv; subst hdiv
  have hId := congrArg (fun n : Nat => (n : F)) (U8Facts.xor_and_identity a b)
  push_cast at hId
  have hDivEq : ((a : F) + (b : F) - ((Nat.xor a b : Nat) : F)) / (2 : F) =
      ((Nat.land a b : Nat) : F) := by
    apply (div_eq_iff h2ne).mpr
    linear_combination hId
  exact ⟨congrArg Value.field hDivEq, rfl⟩

private theorem u32lib_u8_or (hc : U32.Compatible F) (lib : U32LibraryWorld world)
    {a b : Nat} (ha : a < 256) (hb : b < 256)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt8::or" [.field (a : F), .field (b : F)] h r h') :
    r = .field ((Nat.lor a b : Nat) : F) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u8_or rfl ev
  obtain ⟨va, vb, _, _, eva, evb, hcal⟩ := evalExpr_call2_inv body
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb
  obtain ⟨_, body2⟩ := evalFn_plain_inv lib.u8_raw_or rfl hcal
  obtain ⟨vx, _, hcallx, hret⟩ := evalExpr_let_bind_inv body2
  obtain ⟨va', vb', _, _, eva', evb', hxor⟩ := evalExpr_call2_inv hcallx
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva'
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb'
  obtain ⟨rfl, a', b', ha', hb', haEq, hbEq, rfl⟩ := lib.maps.raw_xor _ _ _ _ _ hxor
  have ha1 : a' = a := u32Compat_byte_inj hc ha' ha (Value.field.inj haEq).symm
  have hb1 : b' = b := u32Compat_byte_inj hc hb' hb (Value.field.inj hbEq).symm
  subst a' b'
  obtain ⟨xn, yn, _, evnum, ev2, hdiv⟩ := evalExpr_binary_inv hret
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev2
  obtain ⟨xs, ys, _, evadd, evx, hadd2⟩ := evalExpr_binary_inv evnum
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evx
  obtain ⟨xa, xb, _, eva2, evb2, hadd⟩ := evalExpr_binary_inv evadd
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb2
  simp only [evalBinOp, Except.ok.injEq] at hadd; subst hadd
  simp only [evalBinOp, Except.ok.injEq] at hadd2; subst hadd2
  have h2ne : (2 : F) ≠ 0 := u32Compat_two_ne_zero hc
  simp only [evalBinOp, h2ne, ↓reduceIte, Except.ok.injEq] at hdiv; subst hdiv
  have hId := congrArg (fun n : Nat => (n : F)) (U8Facts.xor_or_identity a b)
  push_cast at hId
  have hDivEq : ((a : F) + (b : F) + ((Nat.xor a b : Nat) : F)) / (2 : F) =
      ((Nat.lor a b : Nat) : F) := by
    apply (div_eq_iff h2ne).mpr
    linear_combination -hId
  exact ⟨congrArg Value.field hDivEq, rfl⟩

private theorem u32lib_from_bytes (lib : U32LibraryWorld world) {x r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::from_bytes" [x] h r h') : r = x ∧ h' = h := by
  obtain ⟨_, b⟩ := evalFn_plain_inv lib.u32_from_bytes rfl ev
  exact evalExpr_var_eq (by simp) b

private theorem u32lib_to_bytes (lib : U32LibraryWorld world) {x r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::to_bytes" [x] h r h') : r = x ∧ h' = h := by
  obtain ⟨_, b⟩ := evalFn_plain_inv lib.u32_to_bytes rfl ev
  exact evalExpr_var_eq (by simp) b

private theorem u32lib_compact_field (lib : U32LibraryWorld world) {x r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::compact_field" [x] h r h') : r = x ∧ h' = h := by
  obtain ⟨_, b⟩ := evalFn_plain_inv lib.u32_compact_field rfl ev
  exact evalExpr_var_eq (by simp) b

private theorem u32lib_compact (lib : U32LibraryWorld world) {n : Nat} {w r : SourceValue F} {h h' : Heap F}
    (hw : isU32Word n w)
    (ev : EvalFn world "UInt32::compact" [w] h r h') :
    r = .field (n : F) ∧ h' = h := by
  obtain ⟨b0, b1, b2, b3, _, _, _, _, rfl, rfl⟩ := hw
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u32_compact rfl ev
  have hbyte : ∀ (i bi : Nat) (h1 h2 : Heap F) (rv : SourceValue F),
      projectValue (.tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)] : SourceValue F) i =
        .ok (.field (bi : F)) →
      EvalExpr world []
        [("word", .tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)])]
        (u8f (.index (.var "word") i)) h1 rv h2 →
      rv = .field (bi : F) ∧ h2 = h1 := by
    intro i bi h1 h2 rv hpr e
    obtain ⟨vi, _, evi, cal⟩ := evalExpr_call1_inv e
    obtain ⟨vt, evt, pr⟩ := evalExpr_index_inv evi
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evt
    obtain rfl := Except.ok.inj (hpr.symm.trans pr)
    exact u32lib_u8_to_field lib cal
  obtain ⟨va3, vb3, _, eva3, evb3, opAdd3⟩ := evalExpr_binary_inv body
  obtain ⟨va2, vb2, _, eva2, evb2, opAdd2⟩ := evalExpr_binary_inv eva3
  obtain ⟨va1, vb1, _, eva1, evb1, opAdd1⟩ := evalExpr_binary_inv eva2
  obtain ⟨rfl, rfl⟩ := hbyte 0 b0 _ _ _ rfl eva1
  obtain ⟨vc1, vd1, _, evc1, evd1, opMul1⟩ := evalExpr_binary_inv evb1
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evc1
  obtain ⟨rfl, rfl⟩ := hbyte 1 b1 _ _ _ rfl evd1
  simp only [evalBinOp, Except.ok.injEq] at opMul1; subst opMul1
  simp only [evalBinOp, Except.ok.injEq] at opAdd1; subst opAdd1
  obtain ⟨vc2, vd2, _, evc2, evd2, opMul2⟩ := evalExpr_binary_inv evb2
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evc2
  obtain ⟨rfl, rfl⟩ := hbyte 2 b2 _ _ _ rfl evd2
  simp only [evalBinOp, Except.ok.injEq] at opMul2; subst opMul2
  simp only [evalBinOp, Except.ok.injEq] at opAdd2; subst opAdd2
  obtain ⟨vc3, vd3, _, evc3, evd3, opMul3⟩ := evalExpr_binary_inv evb3
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evc3
  obtain ⟨rfl, rfl⟩ := hbyte 3 b3 _ _ _ rfl evd3
  simp only [evalBinOp, Except.ok.injEq] at opMul3; subst opMul3
  simp only [evalBinOp, Except.ok.injEq] at opAdd3; subst opAdd3
  refine ⟨?_, rfl⟩
  congr 1
  simp only [U32.pack]
  push_cast
  ring

private theorem u32lib_from_fields_any (lib : U32LibraryWorld world) {x r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::from_fields" [x] h r h') :
    ∃ n, n < U32.base ∧ isU32Word n r ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u32_from_fields rfl ev
  obtain ⟨vb0, vb1, _, ev1, k1⟩ := evalExpr_let_tuple2_inv body
  obtain ⟨vr0, vr1, _, _, evr0, evr1, cal1⟩ := evalExpr_call2_inv ev1
  obtain ⟨_, evx0, _⟩ := evalExpr_index_inv evr0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evx0
  obtain ⟨_, evx1, _⟩ := evalExpr_index_inv evr1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evx1
  obtain ⟨heq1, rfl, b0, b1, hb0, hb1, rfl, rfl⟩ := u32lib_u8_from_fields lib cal1
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1
  obtain ⟨rfl, rfl⟩ := heq1
  obtain ⟨vb2, vb3, _, ev2, k2⟩ := evalExpr_let_tuple2_inv k1
  obtain ⟨vr2, vr3, _, _, evr2, evr3, cal2⟩ := evalExpr_call2_inv ev2
  obtain ⟨_, evx2, _⟩ := evalExpr_index_inv evr2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evx2
  obtain ⟨_, evx3, _⟩ := evalExpr_index_inv evr3
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evx3
  obtain ⟨heq2, rfl, b2, b3, hb2, hb3, rfl, rfl⟩ := u32lib_u8_from_fields lib cal2
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2
  obtain ⟨rfl, rfl⟩ := heq2
  obtain ⟨u0, u1, u2, u3, _, _, _, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv k2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e3
  exact ⟨U32.pack b0 b1 b2 b3, U32.pack_lt hb0 hb1 hb2 hb3,
    ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, rfl⟩, rfl⟩

private theorem u32lib_from_fields (lib : U32LibraryWorld world) {v0 v1 v2 v3 r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::from_fields" [.tuple [v0, v1, v2, v3]] h r h') :
    ∃ b0 b1 b2 b3 : Nat,
      b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 ∧
      v0 = .field (b0 : F) ∧ v1 = .field (b1 : F) ∧
      v2 = .field (b2 : F) ∧ v3 = .field (b3 : F) ∧
      isU32Word (U32.pack b0 b1 b2 b3) r ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u32_from_fields rfl ev
  obtain ⟨vb0, vb1, _, ev1, k1⟩ := evalExpr_let_tuple2_inv body
  obtain ⟨vr0, vr1, _, _, evr0, evr1, cal1⟩ := evalExpr_call2_inv ev1
  obtain ⟨_, evx0, pr0⟩ := evalExpr_index_inv evr0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evx0
  simp only [projectValue, List.getElem?_cons_zero, pure, Except.pure, Except.ok.injEq] at pr0; subst pr0
  obtain ⟨_, evx1, pr1⟩ := evalExpr_index_inv evr1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evx1
  simp only [projectValue, List.getElem?_cons_succ, List.getElem?_cons_zero, pure, Except.pure,
    Except.ok.injEq] at pr1; subst pr1
  obtain ⟨heq1, rfl, b0, b1, hb0, hb1, rfl, rfl⟩ := u32lib_u8_from_fields lib cal1
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1
  obtain ⟨rfl, rfl⟩ := heq1
  obtain ⟨vb2, vb3, _, ev2, k2⟩ := evalExpr_let_tuple2_inv k1
  obtain ⟨vr2, vr3, _, _, evr2, evr3, cal2⟩ := evalExpr_call2_inv ev2
  obtain ⟨_, evx2, pr2⟩ := evalExpr_index_inv evr2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evx2
  simp only [projectValue, List.getElem?_cons_succ, List.getElem?_cons_zero, pure, Except.pure,
    Except.ok.injEq] at pr2; subst pr2
  obtain ⟨_, evx3, pr3⟩ := evalExpr_index_inv evr3
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evx3
  simp only [projectValue, List.getElem?_cons_succ, List.getElem?_cons_zero, pure, Except.pure,
    Except.ok.injEq] at pr3; subst pr3
  obtain ⟨heq2, rfl, b2, b3, hb2, hb3, rfl, rfl⟩ := u32lib_u8_from_fields lib cal2
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2
  obtain ⟨rfl, rfl⟩ := heq2
  obtain ⟨u0, u1, u2, u3, _, _, _, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv k2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e3
  exact ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, rfl, rfl, rfl,
    ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, rfl⟩, rfl⟩

private theorem u32lib_from_field (lib : U32LibraryWorld world) {v r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::from_field" [v] h r h') :
    ∃ n, n < U32.base ∧ v = .field (n : F) ∧ isU32Word n r ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u32_from_field rfl ev
  obtain ⟨vraw, _, evHint, k1⟩ := evalExpr_let_bind_inv body
  obtain ⟨_, evKey⟩ := evalExpr_hint_inv evHint
  obtain ⟨_, rfl⟩ := evalExpr_var_inv evKey
  obtain ⟨vword, _, evWord, k2⟩ := evalExpr_let_bind_inv k1
  obtain ⟨vraw', _, evRaw', calFF⟩ := evalExpr_call1_inv evWord
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evRaw'
  obtain ⟨n, hn, hwn, rfl⟩ := u32lib_from_fields_any lib calFF
  obtain ⟨_, _, evAss, k3⟩ := evalExpr_let_wildcard_inv k2
  obtain ⟨vl, vr, _, evl, evr, heq, _⟩ := evalExpr_assertEq_inv evAss
  obtain ⟨vw', _, evw', calC⟩ := evalExpr_call1_inv evl
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evw'
  obtain ⟨rfl, rfl⟩ := u32lib_compact lib hwn calC
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) k3
  exact ⟨n, hn, heq.symm, hwn, rfl⟩

private theorem eval_u32WordFields_heap (lib : U32LibraryWorld world) {locals : Environment F Nat}
    {v : String} {val : SourceValue F} {h h' : Heap F} {r : SourceValue F}
    (hl : locals.find? (·.1 == v) = some (v, val))
    (ev : EvalExpr world [] locals (u32WordFieldsExpr v) h r h') : h' = h := by
  have hslot : ∀ (k : Nat) (h1 h2 : Heap F) (rv : SourceValue F),
      EvalExpr world [] locals (u8f (.index (.var v) k)) h1 rv h2 → h2 = h1 := by
    intro k h1 h2 rv e
    obtain ⟨vi, _, evi, cal⟩ := evalExpr_call1_inv e
    obtain ⟨vt, evt, _⟩ := evalExpr_index_inv evi
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hl evt
    exact (u32lib_u8_to_field lib cal).2
  obtain ⟨_, _, _, _, _, _, _, e0, e1, e2, e3, _⟩ := evalExpr_array4_inv ev
  obtain rfl := hslot 0 _ _ _ e0
  obtain rfl := hslot 1 _ _ _ e1
  obtain rfl := hslot 2 _ _ _ e2
  exact hslot 3 _ _ _ e3

private theorem u32lib_add (hc : U32.Compatible F) (lib : U32LibraryWorld world)
    {a b : Nat} {wa wb r : SourceValue F} {h h' : Heap F}
    (ha : isU32Word a wa) (hb : isU32Word b wb)
    (ev : EvalFn world "UInt32::add" [wa, wb] h r h') :
    isU32Word ((a + b) % U32.base) r ∧ h' = h := by
  have haLt : a < U32.base := by
    obtain ⟨b0, b1, b2, b3, h0, h1, h2, h3, rfl, _⟩ := ha; exact U32.pack_lt h0 h1 h2 h3
  have hbLt : b < U32.base := by
    obtain ⟨b0, b1, b2, b3, h0, h1, h2, h3, rfl, _⟩ := hb; exact U32.pack_lt h0 h1 h2 h3
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u32_add rfl ev
  obtain ⟨vraw, _, evHint, k1⟩ := evalExpr_let_bind_inv body
  obtain ⟨_, evKey⟩ := evalExpr_hint_inv evHint
  obtain ⟨_, _, _, evKa, evKb, _⟩ := evalExpr_tuple2_inv evKey
  obtain rfl := eval_u32WordFields_heap lib (by simp; rfl) evKa
  obtain rfl := eval_u32WordFields_heap lib (by simp; rfl) evKb
  obtain ⟨vres, _, evRes, k2⟩ := evalExpr_let_bind_inv k1
  obtain ⟨vraw', _, evRaw', calFF⟩ := evalExpr_call1_inv evRes
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evRaw'
  obtain ⟨res, hresLt, hresW, rfl⟩ := u32lib_from_fields_any lib calFF
  obtain ⟨vcarry, _, evCarry, k3⟩ := evalExpr_let_bind_inv k2
  obtain ⟨vnum, vden, _, evNum, evDen, opDiv⟩ := evalExpr_binary_inv evCarry
  obtain ⟨vsum, vcres, _, evSum, evCres, opSub⟩ := evalExpr_binary_inv evNum
  obtain ⟨vca, vcb, _, evCa, evCb, opAdd⟩ := evalExpr_binary_inv evSum
  obtain ⟨va', _, eva', calCa⟩ := evalExpr_call1_inv evCa
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva'
  obtain ⟨rfl, rfl⟩ := u32lib_compact lib ha calCa
  obtain ⟨vb', _, evb', calCb⟩ := evalExpr_call1_inv evCb
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb'
  obtain ⟨rfl, rfl⟩ := u32lib_compact lib hb calCb
  simp only [evalBinOp, Except.ok.injEq] at opAdd; subst opAdd
  obtain ⟨vr', _, evr', calCr⟩ := evalExpr_call1_inv evCres
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr'
  obtain ⟨rfl, rfl⟩ := u32lib_compact lib hresW calCr
  simp only [evalBinOp, Except.ok.injEq] at opSub; subst opSub
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evDen
  have hbase : (4294967296 : F) ≠ 0 := by simpa [U32.base] using U32.base_ne_zero hc
  simp only [evalBinOp, hbase, ↓reduceIte, Except.ok.injEq] at opDiv; subst opDiv
  obtain ⟨_, _, evAss, k4⟩ := evalExpr_let_wildcard_inv k3
  obtain ⟨vl, vr, _, evl, evr, heq, _⟩ := evalExpr_assertEq_inv evAss
  obtain ⟨vc1, vcm1, _, evc1, evcm1, opMul⟩ := evalExpr_binary_inv evl
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc1
  obtain ⟨vc2, v1, _, evc2, ev1, opSub1⟩ := evalExpr_binary_inv evcm1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc2
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev1
  simp only [evalBinOp, Except.ok.injEq] at opSub1; subst opSub1
  simp only [evalBinOp, Except.ok.injEq] at opMul; subst opMul
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evr
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) k4
  have hvalid :
      let carry := ((a : F) + (b : F) - (res : F)) / (U32.base : F)
      carry * (carry - 1) = 0 := by
    simpa [U32.base] using Value.field.inj heq
  have hEq : res = (a + b) % U32.base :=
    (U32.add_words_check_iff hc haLt hbLt hresLt).1 hvalid
  rw [← hEq]
  exact ⟨hresW, rfl⟩

private theorem u32lib_add3 (hc : U32.Compatible F) (lib : U32LibraryWorld world)
    {a b c : Nat} {wa wb wc r : SourceValue F} {h h' : Heap F}
    (ha : isU32Word a wa) (hb : isU32Word b wb) (hcw : isU32Word c wc)
    (ev : EvalFn world "UInt32::add3" [wa, wb, wc] h r h') :
    isU32Word ((a + b + c) % U32.base) r ∧ h' = h := by
  have haLt : a < U32.base := by
    obtain ⟨b0, b1, b2, b3, h0, h1, h2, h3, rfl, _⟩ := ha; exact U32.pack_lt h0 h1 h2 h3
  have hbLt : b < U32.base := by
    obtain ⟨b0, b1, b2, b3, h0, h1, h2, h3, rfl, _⟩ := hb; exact U32.pack_lt h0 h1 h2 h3
  have hcLt : c < U32.base := by
    obtain ⟨b0, b1, b2, b3, h0, h1, h2, h3, rfl, _⟩ := hcw; exact U32.pack_lt h0 h1 h2 h3
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u32_add3 rfl ev
  obtain ⟨vraw, _, evHint, k1⟩ := evalExpr_let_bind_inv body
  obtain ⟨_, evKey⟩ := evalExpr_hint_inv evHint
  obtain ⟨_, _, _, _, _, evKa, evKb, evKc, _⟩ := evalExpr_tuple3_inv evKey
  obtain rfl := eval_u32WordFields_heap lib (by simp; rfl) evKa
  obtain rfl := eval_u32WordFields_heap lib (by simp; rfl) evKb
  obtain rfl := eval_u32WordFields_heap lib (by simp; rfl) evKc
  obtain ⟨vres, _, evRes, k2⟩ := evalExpr_let_bind_inv k1
  obtain ⟨vraw', _, evRaw', calFF⟩ := evalExpr_call1_inv evRes
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evRaw'
  obtain ⟨res, hresLt, hresW, rfl⟩ := u32lib_from_fields_any lib calFF
  obtain ⟨vcarry, _, evCarry, k3⟩ := evalExpr_let_bind_inv k2
  obtain ⟨vnum, vden, _, evNum, evDen, opDiv⟩ := evalExpr_binary_inv evCarry
  obtain ⟨vsum3, vcres, _, evSum3, evCres, opSub⟩ := evalExpr_binary_inv evNum
  obtain ⟨vsum2, vcc, _, evSum2, evCc, opAdd2⟩ := evalExpr_binary_inv evSum3
  obtain ⟨vca, vcb, _, evCa, evCb, opAdd1⟩ := evalExpr_binary_inv evSum2
  obtain ⟨va', _, eva', calCa⟩ := evalExpr_call1_inv evCa
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva'
  obtain ⟨rfl, rfl⟩ := u32lib_compact lib ha calCa
  obtain ⟨vb', _, evb', calCb⟩ := evalExpr_call1_inv evCb
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb'
  obtain ⟨rfl, rfl⟩ := u32lib_compact lib hb calCb
  simp only [evalBinOp, Except.ok.injEq] at opAdd1; subst opAdd1
  obtain ⟨vc', _, evc', calCc⟩ := evalExpr_call1_inv evCc
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc'
  obtain ⟨rfl, rfl⟩ := u32lib_compact lib hcw calCc
  simp only [evalBinOp, Except.ok.injEq] at opAdd2; subst opAdd2
  obtain ⟨vr', _, evr', calCr⟩ := evalExpr_call1_inv evCres
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr'
  obtain ⟨rfl, rfl⟩ := u32lib_compact lib hresW calCr
  simp only [evalBinOp, Except.ok.injEq] at opSub; subst opSub
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evDen
  have hbase : (4294967296 : F) ≠ 0 := by simpa [U32.base] using U32.base_ne_zero hc
  simp only [evalBinOp, hbase, ↓reduceIte, Except.ok.injEq] at opDiv; subst opDiv
  obtain ⟨_, _, evAss, k4⟩ := evalExpr_let_wildcard_inv k3
  obtain ⟨vl, vr, _, evl, evr, heq, _⟩ := evalExpr_assertEq_inv evAss
  obtain ⟨vp, vcm2, _, evp, evcm2, opMul2⟩ := evalExpr_binary_inv evl
  obtain ⟨vc1, vcm1, _, evc1, evcm1, opMul1⟩ := evalExpr_binary_inv evp
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc1
  obtain ⟨vc2, v1, _, evc2, ev1, opSub1⟩ := evalExpr_binary_inv evcm1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc2
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev1
  simp only [evalBinOp, Except.ok.injEq] at opSub1; subst opSub1
  simp only [evalBinOp, Except.ok.injEq] at opMul1; subst opMul1
  obtain ⟨vc3, v2, _, evc3, ev2, opSub2⟩ := evalExpr_binary_inv evcm2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc3
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev2
  simp only [evalBinOp, Except.ok.injEq] at opSub2; subst opSub2
  simp only [evalBinOp, Except.ok.injEq] at opMul2; subst opMul2
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evr
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) k4
  have hvalid :
      let carry := ((a : F) + (b : F) + (c : F) - (res : F)) / (U32.base : F)
      carry * (carry - 1) * (carry - 2) = 0 := by
    simpa [U32.base] using Value.field.inj heq
  have hEq : res = (a + b + c) % U32.base :=
    (U32.add3_words_check_iff hc haLt hbLt hcLt hresLt).1 hvalid
  rw [← hEq]
  exact ⟨hresW, rfl⟩

private theorem u32lib_sub_borrow (hc : U32.Compatible F) (lib : U32LibraryWorld world)
    {a b : Nat} (ha : a < U32.base) (hb : b < U32.base)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::sub_borrow" [.field (a : F), .field (b : F)] h r h') :
    ∃ wd, isU32Word ((a + U32.base - b) % U32.base) wd ∧
      r = .tuple [wd, .field (if a < b then 1 else 0)] ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u32_sub_borrow rfl ev
  obtain ⟨vraw, _, evHint, k1⟩ := evalExpr_let_bind_inv body
  obtain ⟨_, evKey⟩ := evalExpr_hint_inv evHint
  obtain ⟨_, _, _, evKa, evKb, _⟩ := evalExpr_tuple2_inv evKey
  obtain ⟨_, _, eva0, calCa0⟩ := evalExpr_call1_inv evKa
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva0
  obtain ⟨_, rfl⟩ := u32lib_compact_field lib calCa0
  obtain ⟨_, _, evb0, calCb0⟩ := evalExpr_call1_inv evKb
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb0
  obtain ⟨_, rfl⟩ := u32lib_compact_field lib calCb0
  obtain ⟨vres, _, evRes, k2⟩ := evalExpr_let_bind_inv k1
  obtain ⟨vraw', _, evRaw', calFF⟩ := evalExpr_call1_inv evRes
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evRaw'
  obtain ⟨res, hresLt, hresW, rfl⟩ := u32lib_from_fields_any lib calFF
  obtain ⟨vbor, _, evBor, k3⟩ := evalExpr_let_bind_inv k2
  obtain ⟨vnum, vden, _, evNum, evDen, opDiv⟩ := evalExpr_binary_inv evBor
  obtain ⟨vsum, va', _, evSum, eva', opSub⟩ := evalExpr_binary_inv evNum
  obtain ⟨vcres, vb', _, evCres, evb', opAdd⟩ := evalExpr_binary_inv evSum
  obtain ⟨vr', _, evr', calCr⟩ := evalExpr_call1_inv evCres
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr'
  obtain ⟨rfl, rfl⟩ := u32lib_compact lib hresW calCr
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb'
  simp only [evalBinOp, Except.ok.injEq] at opAdd; subst opAdd
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva'
  simp only [evalBinOp, Except.ok.injEq] at opSub; subst opSub
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evDen
  have hbase : (4294967296 : F) ≠ 0 := by simpa [U32.base] using U32.base_ne_zero hc
  simp only [evalBinOp, hbase, ↓reduceIte, Except.ok.injEq] at opDiv; subst opDiv
  obtain ⟨_, _, evAss, k4⟩ := evalExpr_let_wildcard_inv k3
  obtain ⟨vl, vr, _, evl, evr, heq, _⟩ := evalExpr_assertEq_inv evAss
  obtain ⟨vc1, vcm1, _, evc1, evcm1, opMul⟩ := evalExpr_binary_inv evl
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc1
  obtain ⟨vc2, v1, _, evc2, ev1, opSub1⟩ := evalExpr_binary_inv evcm1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc2
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev1
  simp only [evalBinOp, Except.ok.injEq] at opSub1; subst opSub1
  simp only [evalBinOp, Except.ok.injEq] at opMul; subst opMul
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evr
  obtain ⟨vret0, vret1, _, evret0, evret1, rfl⟩ := evalExpr_tuple2_inv k4
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evret0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evret1
  have hvalid :
      let borrow := ((res : F) + (b : F) - (a : F)) / (U32.base : F)
      borrow * (borrow - 1) = 0 := by
    simpa [U32.base] using Value.field.inj heq
  obtain ⟨hResEq, hBorEq⟩ := U32.sub_sound hc ha hb hresLt hvalid
  refine ⟨_, hResEq ▸ hresW, ?_, rfl⟩
  congr 1
  simp only [List.cons.injEq, and_true, Value.field.injEq]
  simpa [U32.base] using hBorEq

private theorem u32lib_sub (hc : U32.Compatible F) (lib : U32LibraryWorld world)
    {a b : Nat} {wa wb r : SourceValue F} {h h' : Heap F}
    (ha : isU32Word a wa) (hb : isU32Word b wb)
    (ev : EvalFn world "UInt32::sub" [wa, wb] h r h') :
    isU32Word ((a + U32.base - b) % U32.base) r ∧ h' = h := by
  have haLt : a < U32.base := by
    obtain ⟨b0, b1, b2, b3, h0, h1, h2, h3, rfl, _⟩ := ha; exact U32.pack_lt h0 h1 h2 h3
  have hbLt : b < U32.base := by
    obtain ⟨b0, b1, b2, b3, h0, h1, h2, h3, rfl, _⟩ := hb; exact U32.pack_lt h0 h1 h2 h3
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u32_sub rfl ev
  obtain ⟨vt, evt, hproj⟩ := evalExpr_project_inv body
  obtain ⟨vca, vcb, _, _, evca, evcb, calSB⟩ := evalExpr_call2_inv evt
  obtain ⟨va', _, eva', calCa⟩ := evalExpr_call1_inv evca
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva'
  obtain ⟨rfl, rfl⟩ := u32lib_compact lib ha calCa
  obtain ⟨vb', _, evb', calCb⟩ := evalExpr_call1_inv evcb
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb'
  obtain ⟨rfl, rfl⟩ := u32lib_compact lib hb calCb
  obtain ⟨wd, hwd, rfl, rfl⟩ := u32lib_sub_borrow hc lib haLt hbLt calSB
  simp only [projectValue, List.getElem?_cons_zero, pure, Except.pure, Except.ok.injEq] at hproj
  subst hproj
  exact ⟨hwd, rfl⟩

private theorem u32lib_compact_less_than (hc : U32.Compatible F) (lib : U32LibraryWorld world)
    {a b : Nat} (ha : a < U32.base) (hb : b < U32.base)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::compact_less_than" [.field (a : F), .field (b : F)] h r h') :
    r = .field (if a < b then 1 else 0) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u32_compact_less_than rfl ev
  obtain ⟨vt, evt, hproj⟩ := evalExpr_project_inv body
  obtain ⟨va', vb', _, _, eva', evb', calSB⟩ := evalExpr_call2_inv evt
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva'
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb'
  obtain ⟨wd, _, rfl, rfl⟩ := u32lib_sub_borrow hc lib ha hb calSB
  simp only [projectValue, List.getElem?_cons_succ, List.getElem?_cons_zero, pure, Except.pure,
    Except.ok.injEq] at hproj
  subst hproj
  exact ⟨rfl, rfl⟩

private theorem u32lib_less_than (hc : U32.Compatible F) (lib : U32LibraryWorld world)
    {a b : Nat} {wa wb r : SourceValue F} {h h' : Heap F}
    (ha : isU32Word a wa) (hb : isU32Word b wb)
    (ev : EvalFn world "UInt32::less_than" [wa, wb] h r h') :
    r = .field (if a < b then 1 else 0) ∧ h' = h := by
  have haLt : a < U32.base := by
    obtain ⟨b0, b1, b2, b3, h0, h1, h2, h3, rfl, _⟩ := ha; exact U32.pack_lt h0 h1 h2 h3
  have hbLt : b < U32.base := by
    obtain ⟨b0, b1, b2, b3, h0, h1, h2, h3, rfl, _⟩ := hb; exact U32.pack_lt h0 h1 h2 h3
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u32_less_than rfl ev
  obtain ⟨vca, vcb, _, _, evca, evcb, calCLT⟩ := evalExpr_call2_inv body
  obtain ⟨va', _, eva', calCa⟩ := evalExpr_call1_inv evca
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva'
  obtain ⟨rfl, rfl⟩ := u32lib_compact lib ha calCa
  obtain ⟨vb', _, evb', calCb⟩ := evalExpr_call1_inv evcb
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb'
  obtain ⟨rfl, rfl⟩ := u32lib_compact lib hb calCb
  exact u32lib_compact_less_than hc lib haLt hbLt calCLT

private theorem u32lib_bitwise {fnName opName : String} {f : Bool → Bool → Bool}
    (hf : f false false = false)
    (hfn : WorldHasFn world fnName ["a", "b"] (u32BitwiseBody opName))
    (hlt : ∀ x y, x < 256 → y < 256 → Nat.bitwise f x y < 256)
    (hop : ∀ (x y : Nat) h r h', x < 256 → y < 256 →
      EvalFn world opName [.field (x : F), .field (y : F)] h r h' →
      r = .field ((Nat.bitwise f x y : Nat) : F) ∧ h' = h)
    {a b : Nat} {wa wb r : SourceValue F} {h h' : Heap F}
    (ha : isU32Word a wa) (hb : isU32Word b wb)
    (ev : EvalFn world fnName [wa, wb] h r h') :
    isU32Word (Nat.bitwise f a b) r ∧ h' = h := by
  obtain ⟨a0, a1, a2, a3, ha0, ha1, ha2, ha3, rfl, rfl⟩ := ha
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, rfl⟩ := hb
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn rfl ev
  obtain ⟨v0, v1, v2, v3, _, _, _, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv body
  have hstep : ∀ (i ai bi : Nat) (h1 h2 : Heap F) (rv : SourceValue F),
      ai < 256 → bi < 256 →
      projectValue (.tuple [.field (a0 : F), .field (a1 : F), .field (a2 : F), .field (a3 : F)] : SourceValue F) i =
        .ok (.field (ai : F)) →
      projectValue (.tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)] : SourceValue F) i =
        .ok (.field (bi : F)) →
      EvalExpr world []
        [("a", .tuple [.field (a0 : F), .field (a1 : F), .field (a2 : F), .field (a3 : F)]),
         ("b", .tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)])]
        (.call opName (some []) [.index (.var "a") i, .index (.var "b") i]) h1 rv h2 →
      rv = .field ((Nat.bitwise f ai bi : Nat) : F) ∧ h2 = h1 := by
    intro i ai bi h1 h2 rv hai hbi hpa hpb e
    obtain ⟨vai, vbi, _, _, evai, evbi, cal⟩ := evalExpr_call2_inv e
    obtain ⟨_, eva, pa⟩ := evalExpr_index_inv evai
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva
    obtain rfl := Except.ok.inj (hpa.symm.trans pa)
    obtain ⟨_, evb, pb⟩ := evalExpr_index_inv evbi
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb
    obtain rfl := Except.ok.inj (hpb.symm.trans pb)
    exact hop ai bi _ _ _ hai hbi cal
  obtain ⟨rfl, rfl⟩ := hstep 0 a0 b0 _ _ _ ha0 hb0 rfl rfl e0
  obtain ⟨rfl, rfl⟩ := hstep 1 a1 b1 _ _ _ ha1 hb1 rfl rfl e1
  obtain ⟨rfl, rfl⟩ := hstep 2 a2 b2 _ _ _ ha2 hb2 rfl rfl e2
  obtain ⟨rfl, rfl⟩ := hstep 3 a3 b3 _ _ _ ha3 hb3 rfl rfl e3
  have hc0 := hlt a0 b0 ha0 hb0
  have hc1 := hlt a1 b1 ha1 hb1
  have hc2 := hlt a2 b2 ha2 hb2
  have hc3 := hlt a3 b3 ha3 hb3
  rw [← pack_bitwise f hf ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hc0 hc1 hc2 hc3]
  exact ⟨⟨_, _, _, _, hc0, hc1, hc2, hc3, rfl, rfl⟩, rfl⟩

private theorem u32lib_rotr8 (lib : U32LibraryWorld world) {a : Nat} {wa r : SourceValue F} {h h' : Heap F}
    (ha : isU32Word a wa)
    (ev : EvalFn world "UInt32::rotr8" [wa] h r h') :
    isU32Word ((a / 256) + (a % 256) * 16777216) r ∧ h' = h := by
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, rfl⟩ := ha
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u32_rotr8 rfl ev
  obtain ⟨v0, v1, v2, v3, _, _, _, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv body
  obtain ⟨_, eu0, hp0⟩ := evalExpr_index_inv e0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eu0; simp [projectValue] at hp0; subst hp0
  obtain ⟨_, eu1, hp1⟩ := evalExpr_index_inv e1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eu1; simp [projectValue] at hp1; subst hp1
  obtain ⟨_, eu2, hp2⟩ := evalExpr_index_inv e2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eu2; simp [projectValue] at hp2; subst hp2
  obtain ⟨_, eu3, hp3⟩ := evalExpr_index_inv e3
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eu3; simp [projectValue] at hp3; subst hp3
  have hrot : U32.pack b0 b1 b2 b3 / 256 + U32.pack b0 b1 b2 b3 % 256 * 16777216 =
      U32.pack b1 b2 b3 b0 := by
    unfold U32.pack; omega
  rw [hrot]
  exact ⟨⟨b1, b2, b3, b0, hb1, hb2, hb3, hb0, rfl, rfl⟩, rfl⟩

private theorem u32lib_rotr16 (lib : U32LibraryWorld world) {a : Nat} {wa r : SourceValue F} {h h' : Heap F}
    (ha : isU32Word a wa)
    (ev : EvalFn world "UInt32::rotr16" [wa] h r h') :
    isU32Word ((a / 65536) + (a % 65536) * 65536) r ∧ h' = h := by
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, rfl⟩ := ha
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u32_rotr16 rfl ev
  obtain ⟨v0, v1, v2, v3, _, _, _, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv body
  obtain ⟨_, eu0, hp0⟩ := evalExpr_index_inv e0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eu0; simp [projectValue] at hp0; subst hp0
  obtain ⟨_, eu1, hp1⟩ := evalExpr_index_inv e1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eu1; simp [projectValue] at hp1; subst hp1
  obtain ⟨_, eu2, hp2⟩ := evalExpr_index_inv e2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eu2; simp [projectValue] at hp2; subst hp2
  obtain ⟨_, eu3, hp3⟩ := evalExpr_index_inv e3
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eu3; simp [projectValue] at hp3; subst hp3
  have hrot : U32.pack b0 b1 b2 b3 / 65536 + U32.pack b0 b1 b2 b3 % 65536 * 65536 =
      U32.pack b2 b3 b0 b1 := by
    unfold U32.pack; omega
  rw [hrot]
  exact ⟨⟨b2, b3, b0, b1, hb2, hb3, hb0, hb1, rfl, rfl⟩, rfl⟩

/-- Construct `U32LibraryContracts world` from `U32LibraryWorld world` and `U32.Compatible F`. -/
theorem U32LibraryContracts.ofLibraryWorld (lib : U32LibraryWorld world) (hc : U32.Compatible F) :
    U32LibraryContracts world where
  u8_to_field := fun _ _ _ _ ev => u32lib_u8_to_field lib ev
  u8_from_fields := fun _ _ _ _ _ ev => u32lib_u8_from_fields lib ev
  u8_xor := fun _ _ _ _ _ ha hb ev => u32lib_u8_xor hc lib ha hb ev
  u8_and := fun _ _ _ _ _ ha hb ev => u32lib_u8_and hc lib ha hb ev
  u8_or := fun _ _ _ _ _ ha hb ev => u32lib_u8_or hc lib ha hb ev
  from_bytes := fun _ _ _ _ _ _ ev => u32lib_from_bytes lib ev
  to_bytes := fun _ _ _ _ _ _ ev => u32lib_to_bytes lib ev
  compact := fun _ _ _ _ _ hw ev => u32lib_compact lib hw ev
  compact_field := fun _ _ _ _ ev => u32lib_compact_field lib ev
  from_fields := fun _ _ _ _ _ _ _ ev => u32lib_from_fields lib ev
  from_field := fun _ _ _ _ ev => u32lib_from_field lib ev
  add := fun _ _ _ _ _ _ _ ha hb ev => u32lib_add hc lib ha hb ev
  add3 := fun _ _ _ _ _ _ _ _ _ ha hb hcw ev => u32lib_add3 hc lib ha hb hcw ev
  sub_borrow := fun _ _ _ _ _ ha hb ev => u32lib_sub_borrow hc lib ha hb ev
  sub := fun _ _ _ _ _ _ _ ha hb ev => u32lib_sub hc lib ha hb ev
  compact_less_than := fun _ _ _ _ _ ha hb ev => u32lib_compact_less_than hc lib ha hb ev
  less_than := fun _ _ _ _ _ _ _ ha hb ev => u32lib_less_than hc lib ha hb ev
  xor := fun _ _ _ _ _ _ _ ha hb ev =>
    u32lib_bitwise (f := bne) rfl lib.u32_xor
      (fun _ _ hx hy => U8Facts.xor_lt_256 hx hy)
      (fun _ _ _ _ _ hx hy e => u32lib_u8_xor hc lib hx hy e) ha hb ev
  and := fun _ _ _ _ _ _ _ ha hb ev =>
    u32lib_bitwise (f := Bool.and) rfl lib.u32_and
      (fun _ _ hx hy => land_lt_256 hx hy)
      (fun _ _ _ _ _ hx hy e => u32lib_u8_and hc lib hx hy e) ha hb ev
  or := fun _ _ _ _ _ _ _ ha hb ev =>
    u32lib_bitwise (f := Bool.or) rfl lib.u32_or
      (fun _ _ hx hy => lor_lt_256 hx hy)
      (fun _ _ _ _ _ hx hy e => u32lib_u8_or hc lib hx hy e) ha hb ev
  rotr8 := fun _ _ _ _ _ ha ev => u32lib_rotr8 lib ha ev
  rotr16 := fun _ _ _ _ _ ha ev => u32lib_rotr16 lib ha ev

end U32Proofs

/-- **End-to-end soundness of `checkU32Functions`**: any prepared `Generic.Source F`
over a `U32.Compatible F` field passing `World.checkTables` and `checkU32Functions`
satisfies all operational `U32LibraryContracts` over `EvalFn`. -/
theorem u32Contracts_of_check {s : Generic.Source F}
    (hc : U32.Compatible F) (ht : checkTables s = true) (h : checkU32Functions s = true) :
    U32LibraryContracts s.world :=
  U32LibraryContracts.ofLibraryWorld (u32LibraryWorld_of_check s (u8TablesMatch_of_check ht) h) hc

end IxCC.AiurBackend.TypedWorld
