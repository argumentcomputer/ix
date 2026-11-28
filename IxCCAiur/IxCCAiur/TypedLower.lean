import IxCCAiur.TypedRep
import IxCCAiur.Peephole
import Aiur.Library.U32

/-! # Typed / Unboxed `Fir → Formal Aiur` Lowering (`IxCCAiur.TypedLower`)

Lowers `(Fir.Program, Fir.Shape.ShapeCert, CircuitSchedule)` to a compact,
unboxed Formal Aiur module (`Prog`) with demand-driven library linking:

* **Unboxed scalars & enums**: `irr → ()` (0 cols), `nat` / `natLt b` → raw
  `Field` (1 col), `word .w8/.w16` → raw `Field` (1 col), `word .w32` →
  `UInt32::U32` (`[U8; 4]`), `word .w64` → `UInt64::U64` (`[U8; 8]`),
  `enum ind` → dedicated 1-col enum `E<ind>`, `data d` → dedicated enum `D<d>`
  with inline unboxed non-recursive fields, and fallback `Obj` only at `.any`
  / `.fn`.
* **Interval-tracked lazy range checks**: when `ShapeCert` bounds `a + b ≤ 2^56`
  or `a * b ≤ 2^56`, raw field `+`/`*` is emitted with zero range checks.
* **Countdown structural recursion**: `natPred`, `proj x natSucc 0`, and
  `natSub x (lit k)` (`k ∈ 1..4`) emit direct `.binary .sub`, enabling Formal
  Aiur's `Depth.Structural` pass to drop the 24-bit depth column and its
  65,536-row `range16` table completely!
* **Slim 256-row `U8Byte` table tier**: programs without bitwise/U32/U64 ops
  link only a 256-row `U8Byte::check` table (256× smaller than `U8.source`'s
  65,536-row pair tables).
* **Exact free-variable join-point capture filtering** and **sharing-aware
  `Function.isInline`** per `CircuitSchedule`.
* **All 16 `Nat` primitives** (including `natPow`, `natGcd`, `natShl`, `natShr`)
  and **all fixed-width `Lam.Prim.word` (`U8`/`U16`/`U32`/`U64`) operations**.

Every emitted expression is plain (`Lower.isPlainExpr = true`). Zero `sorry`,
zero `native_decide`, zero `bv_decide`. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.TypedLower

open IxCC.Fir (Program Fun FunId Var JoinId Arg Rhs Code Alt CtorInfo)
open IxCC.Key
open IxCC.Lam (Lit Prim)
open IxCC.Shape (Shape)
open IxCC.Fir.Shape (ShapeCert FunShapes)
open IxCC.AiurBackend.Lower
  (Ty Expr Pat Fn natLimit moduleName objName bytesName objQName bytesQName objTy bytesTy
   ptrObjTy ptrBytesTy funName entryName jpFunName localName entryParamName ctorNameOf
   allDistinct objCtorNames mk natE erasedE bytesE strE pN pC callE vE litE letE seqE matchE
   addE subE assertion trapE wordE qualifyName qualifyExprF isPlainExpr)
open IxCC.AiurBackend.Schedule (CircuitSchedule RangeCheckMode)
open IxCC.AiurBackend.TypedRep

/-! ## Slim 256-Row `U8Byte` Module (`TableTier.byte256`) -/

/-- Minimal 256-row byte range-check module: `U8Byte::check(x : Field) -> ()`
succeeds iff `x ∈ {0, …, 255}`. Avoids linking the 65,536-row pair tables of
`Aiur.Library.U8.source` on pure `Nat` arithmetic programs. -/
def u8ByteProgram : Aiur.Generic.Program Nat :=
  { functions := []
    tables := [
      { name := "byte_inputs"
        rowType := .tuple [.field]
        rows := (List.range 256).map fun x => .tuple [.literal x] },
      { name := "byte_units"
        rowType := .tuple []
        rows := List.replicate 256 (.tuple []) }
    ]
    maps := [
      { name := "check"
        params := [("x", .field)]
        result := .tuple []
        input := "byte_inputs"
        output := "byte_units" }
    ] }

def u8ByteModule : Aiur.Modules.Program Nat :=
  { modules := [{ name := "U8Byte", body := .definitions { program := u8ByteProgram } }] }

/-! ## Small-Table (`256`-Row) Arithmetic Helpers over Raw `Field` -/

def mulE (a b : Expr) : Expr := .binary .mul a b

private def byteTerm (prefixName : String) (i : Nat) : Expr :=
  if i == 0 then vE s!"{prefixName}0"
  else mulE (litE (256 ^ i)) (vE s!"{prefixName}{i}")

private def recomposeBytes (prefixName : String) : List Nat → Expr
  | [] => litE 0
  | [i] => byteTerm prefixName i
  | i :: rest => addE (byteTerm prefixName i) (recomposeBytes prefixName rest)

private def bytePat8 (prefixName : String) : Pat :=
  .array ((List.range 8).map fun i => .bind s!"{prefixName}{i}")

private def byteCheckSeq (usePair : Bool) (prefixName : String) (count : Nat) (body : Expr) : Expr :=
  if usePair then
    -- Check pairs via `UInt8::from_fields` when `UInt8` pair tables are already linked.
    let rec go (idx : Nat) : Nat → Expr
      | 0 => body
      | 1 => seqE (callE "UInt8::from_fields" [vE s!"{prefixName}{idx}", litE 0]) body
      | k + 2 =>
        seqE (callE "UInt8::from_fields" [vE s!"{prefixName}{idx}", vE s!"{prefixName}{idx + 1}"])
          (go (idx + 2) k)
    go 0 count
  else
    (List.range count).foldr
      (fun i acc => seqE (callE "U8Byte::check" [vE s!"{prefixName}{i}"]) acc) body

private def assertZeroSeq (prefixName : String) (fromIdx toIdx : Nat) (msg : String) (body : Expr) : Expr :=
  (List.range (toIdx - fromIdx)).foldr
    (fun k acc =>
      seqE (.builtin (.assertEq (assertion msg)) [vE s!"{prefixName}{fromIdx + k}", litE 0]) acc)
    body

/-- `check_u8(x : Field) -> ()`: verifies `x < 256`. -/
def checkU8Fn (usePair : Bool) : Fn :=
  { name := "check_u8", params := [("x", .field)], result := .tuple []
    isInline := true
    body :=
      if usePair then seqE (callE "UInt8::from_fields" [vE "x", litE 0]) (.tuple [])
      else callE "U8Byte::check" [vE "x"] }

/-- `check_u56(x : Field) -> ()`: verifies `x < 2^56` using `bytes_le` + 7 byte lookups. -/
def checkU56Fn (usePair : Bool) : Fn :=
  { name := "check_u56", params := [("x", .field)], result := .tuple []
    isInline := false
    body :=
      .letValue (bytePat8 "b") (.hint (.array .field 8) (vE "x") "bytes_le") <|
      byteCheckSeq usePair "b" 7 <|
      seqE (.builtin (.assertEq (assertion "u56: top byte must be zero")) [vE "b7", litE 0]) <|
      seqE (.builtin (.assertEq (assertion "u56: bytes do not recompose"))
        [recomposeBytes "b" (List.range 7), vE "x"]) (.tuple []) }

/-- `check_u16(x : Field) -> ()`: verifies `x < 2^16`. -/
def checkU16Fn (usePair : Bool) : Fn :=
  { name := "check_u16", params := [("x", .field)], result := .tuple []
    isInline := false
    body :=
      .letValue (bytePat8 "b") (.hint (.array .field 8) (vE "x") "bytes_le") <|
      byteCheckSeq usePair "b" 2 <|
      assertZeroSeq "b" 2 8 "u16: high bytes must be zero" <|
      seqE (.builtin (.assertEq (assertion "u16: bytes do not recompose"))
        [recomposeBytes "b" [0, 1], vE "x"]) (.tuple []) }

/-- `check_u24(x : Field) -> ()`: verifies `x < 2^24`. -/
def checkU24Fn (usePair : Bool) : Fn :=
  { name := "check_u24", params := [("x", .field)], result := .tuple []
    isInline := false
    body :=
      .letValue (bytePat8 "b") (.hint (.array .field 8) (vE "x") "bytes_le") <|
      byteCheckSeq usePair "b" 3 <|
      assertZeroSeq "b" 3 8 "u24: high bytes must be zero" <|
      seqE (.builtin (.assertEq (assertion "u24: bytes do not recompose"))
        [recomposeBytes "b" [0, 1, 2], vE "x"]) (.tuple []) }

/-- `sub_borrow_56(x y : Field) -> (Field, Field)`: for `x, y < 2^56`, returns
`(x - y, 1)` when `x ≥ y`, and `(0, 0)` when `x < y`.
Uses `z = x - y + 2^56 ∈ [1, 2^57 - 1]`, decomposing `z = lo + 2^56 * b7` with
`lo < 2^56` and `b7 ∈ {0, 1}` via existing `bytes_le` + 7 byte lookups! -/
def subBorrow56Fn (usePair : Bool) : Fn :=
  { name := "sub_borrow_56", params := [("x", .field), ("y", .field)],
    result := .tuple [.field, .field], isInline := false
    body :=
      letE "z" (addE (subE (vE "x") (vE "y")) (litE natLimit)) <|
      .letValue (bytePat8 "b") (.hint (.array .field 8) (vE "z") "bytes_le") <|
      byteCheckSeq usePair "b" 7 <|
      seqE (.builtin (.assertEq (assertion "sub_borrow_56: b7 not boolean"))
        [mulE (vE "b7") (subE (vE "b7") (litE 1)), litE 0]) <|
      letE "lo" (recomposeBytes "b" (List.range 7)) <|
      seqE (.builtin (.assertEq (assertion "sub_borrow_56: recomposition failed"))
        [addE (vE "lo") (mulE (litE natLimit) (vE "b7")), vE "z"]) <|
      .tuple [mulE (vE "b7") (vE "lo"), vE "b7"] }

/-- `split_32_24(x : Field) -> (Field, Field)`: decomposes `x < 2^56` into
`(lo < 2^32, hi < 2^24)` such that `x = lo + 2^32 * hi`. -/
def split32_24Fn (usePair : Bool) : Fn :=
  { name := "split_32_24", params := [("x", .field)],
    result := .tuple [.field, .field], isInline := true
    body :=
      .letValue (bytePat8 "b") (.hint (.array .field 8) (vE "x") "bytes_le") <|
      byteCheckSeq usePair "b" 7 <|
      seqE (.builtin (.assertEq (assertion "split_32_24: top byte must be zero"))
        [vE "b7", litE 0]) <|
      letE "lo" (recomposeBytes "b" [0, 1, 2, 3]) <|
      letE "hi" (addE (vE "b4") (addE (mulE (litE 256) (vE "b5")) (mulE (litE 65536) (vE "b6")))) <|
      seqE (.builtin (.assertEq (assertion "split_32_24: recomposition failed"))
        [addE (vE "lo") (mulE (litE (2 ^ 32)) (vE "hi")), vE "x"]) <|
      .tuple [vE "lo", vE "hi"] }

/-- `mul_56(x y : Field) -> Field`: for `x, y < 2^56` over Goldilocks (`p > (2^32 - 1)^2`),
verifies `x * y < 2^56` in `ℕ` without wraparound and returns `x * y`. -/
def mul56Fn : Fn :=
  { name := "mul_56", params := [("x", .field), ("y", .field)], result := .field
    isInline := false
    body :=
      .letValue (.tuple [.bind "xlo", .bind "xhi"]) (callE "split_32_24" [vE "x"]) <|
      .letValue (.tuple [.bind "ylo", .bind "yhi"]) (callE "split_32_24" [vE "y"]) <|
      seqE (.builtin (.assertEq (assertion "mul_56: high product overflow"))
        [mulE (vE "xhi") (vE "yhi"), litE 0]) <|
      letE "mid" (addE (mulE (vE "xlo") (vE "yhi")) (mulE (vE "xhi") (vE "ylo"))) <|
      seqE (callE "check_u24" [vE "mid"]) <|
      letE "lo" (mulE (vE "xlo") (vE "ylo")) <|
      seqE (callE "check_u56" [vE "lo"]) <|
      letE "prod" (addE (vE "lo") (mulE (litE (2 ^ 32)) (vE "mid"))) <|
      seqE (callE "check_u56" [vE "prod"]) (vE "prod") }

/-- `divmod_56(x y : Field) -> (Field, Field)`: for `x, y < 2^56` and `y ≠ 0`,
returns `(x / y, x % y)` verified via `ixcc.divmod`, `mul_56`, `check_u56`, and
`sub_borrow_56`. Uses only the 256-row `U8Byte::check` table in `byte256` mode! -/
def divmod56Fn : Fn :=
  { name := "divmod_56", params := [("x", .field), ("y", .field)],
    result := .tuple [.field, .field], isInline := false
    body :=
      .letValue (.tuple [.bind "q", .bind "r"])
        (.hint (.tuple [.field, .field]) (.tuple [vE "x", vE "y"]) "ixcc.divmod") <|
      letE "p" (callE "mul_56" [vE "q", vE "y"]) <|
      seqE (callE "check_u56" [vE "r"]) <|
      seqE (.builtin (.assertEq (assertion "divmod_56: q*y + r = x"))
        [addE (vE "p") (vE "r"), vE "x"]) <|
      .letValue (.tuple [.wildcard, .bind "ge"]) (callE "sub_borrow_56" [vE "r", vE "y"]) <|
      seqE (.builtin (.assertEq (assertion "divmod_56: r < y")) [vE "ge", litE 0]) <|
      .tuple [vE "q", vE "r"] }

/-- `pow_56_loop(base exp acc : Field) -> Field`: binary exponentiation `acc * base^exp < 2^56`. -/
def pow56LoopFn : Fn :=
  { name := "pow_56_loop", params := [("base", .field), ("exp", .field), ("acc", .field)],
    result := .field, isInline := false
    body :=
      matchE (vE "exp")
        [(.literal 0, vE "acc"),
         (.wildcard,
          .letValue (.tuple [.bind "half", .bind "bit"])
            (callE "divmod_56" [vE "exp", litE 2]) <|
          letE "acc2"
            (matchE (vE "bit")
              [(.literal 0, vE "acc"),
               (.wildcard, callE "mul_56" [vE "acc", vE "base"])]) <|
          matchE (vE "half")
            [(.literal 0, vE "acc2"),
             (.wildcard,
              letE "b2" (callE "mul_56" [vE "base", vE "base"]) <|
              callE "pow_56_loop" [vE "b2", vE "half", vE "acc2"])])] }

def pow56Fn : Fn :=
  { name := "pow_56", params := [("base", .field), ("exp", .field)], result := .field
    isInline := true
    body := callE "pow_56_loop" [vE "base", vE "exp", litE 1] }

/-- `gcd_56(a b : Field) -> Field`: Euclidean `Nat.gcd` on `< 2^56` naturals. -/
def gcd56Fn : Fn :=
  { name := "gcd_56", params := [("a", .field), ("b", .field)], result := .field
    isInline := false
    body :=
      matchE (vE "b")
        [(.literal 0, vE "a"),
         (.wildcard,
          .letValue (.tuple [.wildcard, .bind "r"]) (callE "divmod_56" [vE "a", vE "b"]) <|
          callE "gcd_56" [vE "b", vE "r"])] }

/-- `shl_56(x k : Field) -> Field`: `x * 2^k < 2^56`. -/
def shl56Fn : Fn :=
  { name := "shl_56", params := [("x", .field), ("k", .field)], result := .field
    isInline := true
    body :=
      matchE (vE "x")
        [(.literal 0, litE 0),
         (.wildcard, callE "mul_56" [vE "x", callE "pow_56" [litE 2, vE "k"]])] }

/-- `shr_56(x k : Field) -> Field`: `x / 2^k` (returns `0` when `k ≥ 56`). -/
def shr56Fn : Fn :=
  { name := "shr_56", params := [("x", .field), ("k", .field)], result := .field
    isInline := false
    body :=
      .letValue (.tuple [.wildcard, .bind "ge"]) (callE "sub_borrow_56" [vE "k", litE 56]) <|
      matchE (vE "ge")
        [(.literal 1, litE 0),
         (.wildcard,
          .letValue (.tuple [.bind "q", .wildcard])
            (callE "divmod_56" [vE "x", callE "pow_56" [litE 2, vE "k"]]) <|
          vE "q")] }

/-! ## `UInt32` / `UInt64` Helper Functions (Only Emitted on Demand) -/

/-- Extract the raw `Field` value of a `UInt32::U32` via `UInt32::compact_field(UInt32::compact(e))`. -/
private def u32ToFieldE (e : Expr) : Expr :=
  callE "UInt32::compact_field" [callE "UInt32::compact" [e]]

/-- `u32_mul(a b : U32) -> U32`: wraps `a * b mod 2^32` using the fact that
`(2^32 - 1)^2 = 1 + 2^32 * (2^32 - 2) < Goldilocks.modulus`. Asserting `hi ≠ 2^32 - 1`
bounds `lo + 2^32 * hi ≤ 2^64 - 2^32 - 1 < p_G`, preventing Goldilocks wraparound
forgery (`lo = 1, hi = 2^32 - 1` for `a = b = 0`) with zero extra lookups or hints! -/
def u32MulFn : Fn :=
  { name := "u32_mul", params := [("a", u32Ty), ("b", u32Ty)], result := u32Ty
    isInline := false
    body :=
      letE "p" (mulE (u32ToFieldE (vE "a")) (u32ToFieldE (vE "b"))) <|
      .letValue (bytePat8 "h") (.hint (.array .field 8) (vE "p") "bytes_le") <|
      letE "lo" (callE "UInt32::from_fields" [.array [vE "h0", vE "h1", vE "h2", vE "h3"]]) <|
      letE "hi" (callE "UInt32::from_fields" [.array [vE "h4", vE "h5", vE "h6", vE "h7"]]) <|
      letE "hif" (u32ToFieldE (vE "hi")) <|
      seqE (.builtin (.assertEq (assertion "u32_mul: recomposition failed"))
        [addE (u32ToFieldE (vE "lo"))
          (mulE (litE (2 ^ 32)) (vE "hif")), vE "p"]) <|
      matchE (vE "hif")
        [(.literal (2 ^ 32 - 1),
          seqE (.builtin (.assertEq (assertion "u32_mul: hi = 2^32 - 1 overflow"))
            [litE 0, litE 1]) (vE "lo")),
         (.wildcard, vE "lo")] }

def u32ComplementFn : Fn :=
  { name := "u32_complement", params := [("a", u32Ty)], result := u32Ty
    isInline := true
    body :=
      letE "bs" (callE "UInt32::to_bytes" [vE "a"]) <|
      callE "UInt32::from_fields"
        [.array [subE (litE 255) (callE "UInt8::to_field" [.index (vE "bs") 0]),
                 subE (litE 255) (callE "UInt8::to_field" [.index (vE "bs") 1]),
                 subE (litE 255) (callE "UInt8::to_field" [.index (vE "bs") 2]),
                 subE (litE 255) (callE "UInt8::to_field" [.index (vE "bs") 3])]] }

def u32DivFn : Fn :=
  { name := "u32_div", params := [("a", u32Ty), ("b", u32Ty)], result := u32Ty
    isInline := false
    body :=
      letE "bf" (u32ToFieldE (vE "b")) <|
      matchE (vE "bf")
        [(.literal 0, callE "UInt32::from_field" [litE 0]),
         (.wildcard,
          .letValue (.tuple [.bind "q", .wildcard])
            (callE "divmod_56" [u32ToFieldE (vE "a"), vE "bf"]) <|
          callE "UInt32::from_field" [vE "q"])] }

def u32ModFn : Fn :=
  { name := "u32_mod", params := [("a", u32Ty), ("b", u32Ty)], result := u32Ty
    isInline := false
    body :=
      letE "bf" (u32ToFieldE (vE "b")) <|
      matchE (vE "bf")
        [(.literal 0, vE "a"),
         (.wildcard,
          .letValue (.tuple [.wildcard, .bind "r"])
            (callE "divmod_56" [u32ToFieldE (vE "a"), vE "bf"]) <|
          callE "UInt32::from_field" [vE "r"])] }

/-- `u32_shl(a b : U32) -> U32`: shift left by `b % 32`, reducing mod `2^32`. -/
def u32ShlFn : Fn :=
  { name := "u32_shl", params := [("a", u32Ty), ("b", u32Ty)], result := u32Ty
    isInline := false
    body :=
      letE "s" (callE "UInt8::to_field" [.index (callE "UInt32::to_bytes" [vE "b"]) 0]) <|
      .letValue (.tuple [.wildcard, .bind "k"]) (callE "divmod_56" [vE "s", litE 32]) <|
      letE "p" (callE "pow_56" [litE 2, vE "k"]) <|
      callE "u32_mul" [vE "a", callE "UInt32::from_field" [vE "p"]] }

/-- `u32_shr(a b : U32) -> U32`: logical shift right by `b % 32`. -/
def u32ShrFn : Fn :=
  { name := "u32_shr", params := [("a", u32Ty), ("b", u32Ty)], result := u32Ty
    isInline := false
    body :=
      letE "s" (callE "UInt8::to_field" [.index (callE "UInt32::to_bytes" [vE "b"]) 0]) <|
      .letValue (.tuple [.wildcard, .bind "k"]) (callE "divmod_56" [vE "s", litE 32]) <|
      letE "p" (callE "pow_56" [litE 2, vE "k"]) <|
      .letValue (.tuple [.bind "q", .wildcard])
        (callE "divmod_56" [u32ToFieldE (vE "a"), vE "p"]) <|
      callE "UInt32::from_field" [vE "q"] }

/-- `u32_of_field(x : Field) -> U32`: reduces `x < 2^56` modulo `2^32` into `UInt32::U32`. -/
def u32OfFieldFn : Fn :=
  { name := "u32_of_field", params := [("x", .field)], result := u32Ty
    isInline := true
    body :=
      .letValue (bytePat8 "h") (.hint (.array .field 8) (vE "x") "bytes_le") <|
      letE "lo" (callE "UInt32::from_fields" [.array [vE "h0", vE "h1", vE "h2", vE "h3"]]) <|
      letE "hi" (callE "UInt32::from_fields" [.array [vE "h4", vE "h5", vE "h6", vE "h7"]]) <|
      seqE (.builtin (.assertEq (assertion "u32_of_field: top byte zero")) [vE "h7", litE 0]) <|
      seqE (.builtin (.assertEq (assertion "u32_of_field: recomposition"))
        [addE (u32ToFieldE (vE "lo"))
          (mulE (litE (2 ^ 32)) (u32ToFieldE (vE "hi"))), vE "x"]) <|
      vE "lo" }

/-- `u64_shr(a b : U64) -> U64`: exact logical shift right by `b % 64` via 32+32 split. -/
def u64ShrFn : Fn :=
  { name := "u64_shr", params := [("a", u64Ty), ("b", u64Ty)], result := u64Ty
    isInline := false
    body :=
      letE "s" (callE "UInt8::to_field" [.index (vE "b") 0]) <|
      .letValue (.tuple [.wildcard, .bind "k"]) (callE "divmod_56" [vE "s", litE 64]) <|
      matchE (vE "k")
        [(.literal 0, vE "a"),
         (.wildcard,
          letE "alo" (callE "UInt32::from_bytes"
            [.array [.index (vE "a") 0, .index (vE "a") 1, .index (vE "a") 2, .index (vE "a") 3]]) <|
          letE "ahi" (callE "UInt32::from_bytes"
            [.array [.index (vE "a") 4, .index (vE "a") 5, .index (vE "a") 6, .index (vE "a") 7]]) <|
          letE "lo" (u32ToFieldE (vE "alo")) <|
          letE "hi" (u32ToFieldE (vE "ahi")) <|
          .letValue (.tuple [.bind "ksub", .bind "ge32"])
            (callE "sub_borrow_56" [vE "k", litE 32]) <|
          matchE (vE "ge32")
            [(.literal 1,
              letE "p" (callE "pow_56" [litE 2, vE "ksub"]) <|
              .letValue (.tuple [.bind "q", .wildcard]) (callE "divmod_56" [vE "hi", vE "p"]) <|
              letE "bl" (callE "UInt32::to_bytes" [callE "UInt32::from_field" [vE "q"]]) <|
              .letValue (.tuple [.bind "z0", .wildcard])
                (callE "UInt8::from_fields" [litE 0, litE 0]) <|
              .array [.index (vE "bl") 0, .index (vE "bl") 1, .index (vE "bl") 2, .index (vE "bl") 3,
                      vE "z0", vE "z0", vE "z0", vE "z0"]),
             (.wildcard,
              letE "p" (callE "pow_56" [litE 2, vE "k"]) <|
              letE "pcomp" (callE "pow_56" [litE 2, subE (litE 32) (vE "k")]) <|
              .letValue (.tuple [.bind "qlo", .wildcard]) (callE "divmod_56" [vE "lo", vE "p"]) <|
              .letValue (.tuple [.bind "qhi", .bind "rhi"]) (callE "divmod_56" [vE "hi", vE "p"]) <|
              letE "reslo" (addE (vE "qlo") (callE "mul_56" [vE "rhi", vE "pcomp"])) <|
              letE "bl" (callE "UInt32::to_bytes" [callE "UInt32::from_field" [vE "reslo"]]) <|
              letE "bh" (callE "UInt32::to_bytes" [callE "UInt32::from_field" [vE "qhi"]]) <|
              .array [.index (vE "bl") 0, .index (vE "bl") 1, .index (vE "bl") 2, .index (vE "bl") 3,
                      .index (vE "bh") 0, .index (vE "bh") 1, .index (vE "bh") 2, .index (vE "bh") 3])])] }

/-- `u64_shl(a b : U64) -> U64`: exact logical shift left by `b % 64` via 32+32 split. -/
def u64ShlFn : Fn :=
  { name := "u64_shl", params := [("a", u64Ty), ("b", u64Ty)], result := u64Ty
    isInline := false
    body :=
      letE "s" (callE "UInt8::to_field" [.index (vE "b") 0]) <|
      .letValue (.tuple [.wildcard, .bind "k"]) (callE "divmod_56" [vE "s", litE 64]) <|
      matchE (vE "k")
        [(.literal 0, vE "a"),
         (.wildcard,
          letE "alo" (callE "UInt32::from_bytes"
            [.array [.index (vE "a") 0, .index (vE "a") 1, .index (vE "a") 2, .index (vE "a") 3]]) <|
          letE "ahi" (callE "UInt32::from_bytes"
            [.array [.index (vE "a") 4, .index (vE "a") 5, .index (vE "a") 6, .index (vE "a") 7]]) <|
          letE "lo" (u32ToFieldE (vE "alo")) <|
          .letValue (.tuple [.bind "ksub", .bind "ge32"])
            (callE "sub_borrow_56" [vE "k", litE 32]) <|
          matchE (vE "ge32")
            [(.literal 1,
              letE "p" (callE "pow_56" [litE 2, vE "ksub"]) <|
              letE "bh" (callE "UInt32::to_bytes"
                [callE "u32_mul" [vE "alo", callE "UInt32::from_field" [vE "p"]]]) <|
              .letValue (.tuple [.bind "z0", .wildcard])
                (callE "UInt8::from_fields" [litE 0, litE 0]) <|
              .array [vE "z0", vE "z0", vE "z0", vE "z0",
                      .index (vE "bh") 0, .index (vE "bh") 1, .index (vE "bh") 2, .index (vE "bh") 3]),
             (.wildcard,
              letE "p" (callE "pow_56" [litE 2, vE "k"]) <|
              letE "pcomp" (callE "pow_56" [litE 2, subE (litE 32) (vE "k")]) <|
              .letValue (.tuple [.bind "carry", .wildcard])
                (callE "divmod_56" [vE "lo", vE "pcomp"]) <|
              letE "pu" (callE "UInt32::from_field" [vE "p"]) <|
              letE "reslo" (callE "u32_mul" [vE "alo", vE "pu"]) <|
              letE "reshi" (callE "UInt32::add"
                [callE "u32_mul" [vE "ahi", vE "pu"], callE "UInt32::from_field" [vE "carry"]]) <|
              letE "bl" (callE "UInt32::to_bytes" [vE "reslo"]) <|
              letE "bh" (callE "UInt32::to_bytes" [vE "reshi"]) <|
              .array [.index (vE "bl") 0, .index (vE "bl") 1, .index (vE "bl") 2, .index (vE "bl") 3,
                      .index (vE "bh") 0, .index (vE "bh") 1, .index (vE "bh") 2, .index (vE "bh") 3])])] }

/-! ## Lowering Context, Typed Variable Map & Demand State -/

structure TCx where
  P : Program
  cert : ShapeCert
  feat : Features
  sched : CircuitSchedule

def TCx.rep (cx : TCx) (s : Shape) : Rep := repOf cx.P cx.cert cx.feat s

def TCx.funShapes (cx : TCx) (f : FunId) : FunShapes := cx.cert.fn f

def TCx.ctorEntry? (cx : TCx) (k : CtorKey) : Option (Nat × Lam.CtorInfo) :=
  Lower.ctorEntry? cx.P k

/-- Dedicated `Bool` enum in `cert`, if both pinned `Bool` ctors are in a valid enum. -/
def TCx.boolEnum? (cx : TCx) : Option (Src.CId × String × String) := do
  let tt ← cx.P.known.boolTrue
  let ff ← cx.P.known.boolFalse
  let (it, et) ← cx.ctorEntry? tt
  let (if_, ef) ← cx.ctorEntry? ff
  unless et.arity == 0 && ef.arity == 0 do none
  let (ind, _) ← cx.cert.enums.find? fun e =>
    validEnum cx.P cx.cert e.1 && e.2.contains tt && e.2.contains ff
  return (ind, ctorNameOf it et.key, ctorNameOf if_ ef.key)

/-- Static typed variable map: `(Fir.Var, Aiur local name, Rep)`. -/
abbrev TVarMap := List (Var × String × Rep)

/-- Static descriptor of a lifted typed join point. -/
structure TJEntry where
  id : JoinId
  fnName : String
  capVars : List (String × Rep)
  paramReps : List Rep
  retRep : Rep
  deriving DecidableEq, Repr, Inhabited

/-- Demand flags recorded while lowering all functions & entries, so only
actually-used helpers, enums, and table tiers are emitted! -/
structure Demand where
  needObj : Bool := false
  needBytes : Bool := false
  needCheckU56 : Bool := false
  needCheckU16 : Bool := false
  needCheckU24 : Bool := false
  needSubBorrow56 : Bool := false
  needMul56 : Bool := false
  needDivMod56 : Bool := false
  needPow56 : Bool := false
  needGcd56 : Bool := false
  needShl56 : Bool := false
  needShr56 : Bool := false
  needU32Mul : Bool := false
  needU32Comp : Bool := false
  needU32Div : Bool := false
  needU32Mod : Bool := false
  needU32Shl : Bool := false
  needU32Shr : Bool := false
  needU32OfField : Bool := false
  needU64Bitwise : Bool := false
  needU64Shl : Bool := false
  needU64Shr : Bool := false
  deriving Repr, Inhabited

structure TState where
  nextLocal : Nat := 0
  nextJp : Nat := 0
  lifted : List Fn := []
  demand : Demand := {}

abbrev TLowerM := StateT TState (Except String)

private def tLift {α : Type} (r : Except String α) : TLowerM α := fun st =>
  match r with
  | .ok a => .ok (a, st)
  | .error e => .error e

private def tFreshLocal : TLowerM String := fun st =>
  .ok (localName st.nextLocal, { st with nextLocal := st.nextLocal + 1 })

private def tFreshLocals : Nat → TLowerM (List String)
  | 0 => pure []
  | n + 1 => do
    let h ← tFreshLocal
    let t ← tFreshLocals n
    return h :: t

private def tFreshJp : TLowerM Nat := fun st =>
  .ok (st.nextJp, { st with nextJp := st.nextJp + 1 })

private def tEmitLifted (f : Fn) : TLowerM Unit := fun st =>
  .ok ((), { st with lifted := st.lifted ++ [f] })

private def tMark (upd : Demand → Demand) : TLowerM Unit := fun st =>
  .ok ((), { st with demand := upd st.demand })

private def tBindVm (vm : TVarMap) : List Var → List (String × Rep) → TVarMap
  | x :: xs, nr :: nrs => tBindVm ((x, nr) :: vm) xs nrs
  | _, _ => vm

/-! ## Representation Coercions (`coerceE`) -/

/-- Coerce an Aiur expression `e` of representation `fromR` to representation `toR`.
Same-representation and widening-bound field coercions emit ZERO instructions! -/
def coerceEAux (fuel : Nat) (cx : TCx) (fromR toR : Rep) (e : Expr) : TLowerM Expr := do
  if fromR == toR then return e
  match fromR, toR with
  | .nat a, .nat b =>
    if a ≤ b then return e
    else return e -- Both are `< natLimit` raw `Field`s; `ShapeCert` guarantees `a ≤ b` on checked flows.
  | .w8, .nat _ | .w8, .w16 => return e
  | .w16, .nat _ => return e
  | .nat a, .w8 =>
    if a ≤ 256 then return e
    else
      tMark fun d => { d with needCheckU56 := true }
      let tmp ← tFreshLocal
      return letE tmp e (seqE (callE "check_u8" [vE tmp]) (vE tmp))
  | .nat a, .w16 =>
    if a ≤ 65536 then return e
    else
      tMark fun d => { d with needCheckU16 := true }
      let tmp ← tFreshLocal
      return letE tmp e (seqE (callE "check_u16" [vE tmp]) (vE tmp))
  | .nat _, .w32 | .w8, .w32 | .w16, .w32 =>
    tMark fun d => { d with needU32OfField := true }
    return callE "u32_of_field" [e]
  | .w32, .nat _ | .w32, .w8 | .w32, .w16 =>
    return u32ToFieldE e
  | .nat _, .w64 | .w8, .w64 | .w16, .w64 =>
    tMark fun d => { d with needU64Bitwise := true }
    return callE "UInt64::from_field" [e]
  | .w64, .nat _ | .w64, .w8 | .w64, .w16 =>
    tMark fun d => { d with needU64Bitwise := true }
    return callE "UInt64::to_field" [e]
  | .w32, .w64 =>
    tMark fun d => { d with needU64Bitwise := true }
    return callE "UInt64::from_field" [u32ToFieldE e]
  | .w64, .w32 =>
    tMark fun d => { d with needU64Bitwise := true }
    let tmp ← tFreshLocal
    return letE tmp e <|
      callE "UInt32::from_bytes"
        [.array [.index (vE tmp) 0, .index (vE tmp) 1, .index (vE tmp) 2, .index (vE tmp) 3]]
  | .irr, .obj =>
    tMark fun d => { d with needObj := true }
    return seqE e erasedE
  | .nat _, .obj | .w8, .obj | .w16, .obj =>
    tMark fun d => { d with needObj := true }
    return natE e
  | .w32, .obj =>
    tMark fun d => { d with needObj := true }
    return natE (u32ToFieldE e)
  | .w64, .obj =>
    tMark fun d => { d with needObj := true, needU64Bitwise := true }
    return natE (callE "UInt64::to_field" [e])
  | .enum ind, .obj =>
    tMark fun d => { d with needObj := true }
    let some ks := cx.cert.enum? ind | tLift (throw s!"coerce: unknown enum {ind}")
    let arms ← ks.mapM fun k => do
      let some (idx, entry) := cx.ctorEntry? k | tLift (throw "coerce enum: missing ctor")
      let nm := ctorNameOf idx entry.key
      return (.construct (.named (enumName ind) []) nm [], mk nm [])
    return matchE e arms
  | .data d, .obj =>
    match fuel with
    | 0 => tLift (throw s!"coerce: recursive data {d} → Obj exceeded depth")
    | fuel' + 1 =>
      tMark fun d0 => { d0 with needObj := true }
      let some D := cx.cert.data? d | tLift (throw s!"coerce: unknown data {d}")
      let arms ← D.ctors.mapM fun (k, fl) => do
        let some (idx, entry) := cx.ctorEntry? k | tLift (throw "coerce data: missing ctor")
        let nm := ctorNameOf idx entry.key
        let fvars ← tFreshLocals fl.length
        let fieldExprs ← (fl.zip fvars).mapM fun (sh, fv) => do
          let fr := cx.rep sh
          let raw := if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then .load (vE fv) else vE fv
          let asObj ← coerceEAux fuel' cx fr .obj raw
          return .store asObj
        return (.construct (.named (dataName d) []) nm (fvars.map .bind), mk nm fieldExprs)
      return matchE e arms
  | .obj, .irr =>
    tMark fun d => { d with needObj := true }
    return matchE e [(pC "E" [], .tuple [])]
  | .obj, .nat _ | .obj, .w8 | .obj, .w16 =>
    tMark fun d => { d with needObj := true }
    let tmp ← tFreshLocal
    return matchE e [(pN (.bind tmp), vE tmp)]
  | .obj, .w32 =>
    tMark fun d => { d with needObj := true, needU32OfField := true }
    let tmp ← tFreshLocal
    return matchE e [(pN (.bind tmp), callE "u32_of_field" [vE tmp])]
  | .obj, .w64 =>
    tMark fun d => { d with needObj := true, needU64Bitwise := true }
    let tmp ← tFreshLocal
    return matchE e [(pN (.bind tmp), callE "UInt64::from_field" [vE tmp])]
  | .obj, .enum ind =>
    tMark fun d => { d with needObj := true }
    let some ks := cx.cert.enum? ind | tLift (throw s!"coerce: unknown enum {ind}")
    let arms ← ks.mapM fun k => do
      let some (idx, entry) := cx.ctorEntry? k | tLift (throw "coerce obj→enum: missing ctor")
      let nm := ctorNameOf idx entry.key
      return (pC nm [], .construct (enumName ind) (some []) nm [])
    return matchE e arms
  | .obj, .data d =>
    match fuel with
    | 0 => tLift (throw s!"coerce: recursive Obj → data {d} exceeded depth")
    | fuel' + 1 =>
      tMark fun d0 => { d0 with needObj := true }
      let some D := cx.cert.data? d | tLift (throw s!"coerce: unknown data {d}")
      let arms ← D.ctors.mapM fun (k, fl) => do
        let some (idx, entry) := cx.ctorEntry? k | tLift (throw "coerce obj→data: missing ctor")
        let nm := ctorNameOf idx entry.key
        let fvars ← tFreshLocals fl.length
        let fieldExprs ← (fl.zip fvars).mapM fun (sh, fv) => do
          let fr := cx.rep sh
          let typed ← coerceEAux fuel' cx .obj fr (.load (vE fv))
          return if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then .store typed else typed
        return (pC nm (fvars.map .bind), .construct (dataName d) (some []) nm fieldExprs)
      return matchE e arms
  | _, _ =>
    tLift (throw s!"unsupported coercion from {reprStr fromR} to {reprStr toR}")

def coerceE (cx : TCx) (fromR toR : Rep) (e : Expr) : TLowerM Expr :=
  coerceEAux (cx.cert.datas.length + 2) cx fromR toR e

/-! ## Lowering Operands (`tArgE`) -/

/-- Lower an operand `a` to `(expr, actualRep)`. -/
def tArgRaw (_cx : TCx) (vm : TVarMap) : Arg → TLowerM (Expr × Rep)
  | .var x =>
    match vm.lookup x with
    | some (nx, r) => return (vE nx, r)
    | none => tLift (throw s!"unbound variable {x}")
  | .lit (.nat n) =>
    if n < natLimit then return (litE n, .nat (n + 1))
    else tLift (throw s!"literal {n} ≥ 2^56")
  | .lit (.str s) => do
    tMark fun d => { d with needObj := true, needBytes := true }
    return (strE s, .obj)
  | .erased => return (.tuple [], .irr)

/-- Lower an operand `a` and coerce it to target representation `target`. -/
def tArgE (cx : TCx) (vm : TVarMap) (a : Arg) (target : Rep) : TLowerM Expr := do
  let (e, r) ← tArgRaw cx vm a
  coerceE cx r target e

/-! ## Lowering Typed Primitives (`tPrimE`) -/

/-- Build a constant-subtraction match `x - k` for small `k ∈ 1..4` using direct
`.binary .sub` so `Depth.Structural` recognizes countdown recursion with zero
depth column and zero table lookups! -/
private def constSubMatch (xExpr : Expr) (k : Nat) : Expr :=
  let zeroArms := (List.range k).map fun i => (.literal i, litE 0)
  matchE xExpr (zeroArms ++ [(.wildcard, subE xExpr (litE k))])

/-- Wrap a `Field` boolean (`0` or `1`) into `target` (`enum Bool` or `Obj`). -/
private def wrapBool (cx : TCx) (condExpr : Expr) (target : Rep) : TLowerM Expr := do
  match target with
  | .enum ind =>
    match cx.boolEnum? with
    | some (bind, tt, ff) =>
      if bind == ind then
        return matchE condExpr
          [(.literal 0, .construct (enumName ind) (some []) ff []),
           (.wildcard, .construct (enumName ind) (some []) tt [])]
      else tLift (throw "wrapBool: enum mismatch")
    | none => tLift (throw "wrapBool: Bool enum missing")
  | .obj =>
    tMark fun d => { d with needObj := true }
    let some (tt, ff) := (Lower.Cx.mk cx.P).boolNames
      | tLift (throw "wrapBool: Bool pins missing")
    return matchE condExpr [(.literal 0, mk ff []), (.wildcard, mk tt [])]
  | _ => tLift (throw s!"wrapBool: unexpected target rep {reprStr target}")

/-- Lower a `Nat` or fixed-width `Word` primitive into target representation `target`. -/
def tPrimE (cx : TCx) (vm : TVarMap) (op : Prim) (as : List Arg) (target : Rep) : TLowerM Expr := do
  match op with
  | .natPred =>
    let [a] := as | tLift (throw "natPred: arity mismatch")
    let (ea, ra) ← tArgRaw cx vm a
    let xf ← coerceE cx ra (.nat natLimit) ea
    let tmp ← tFreshLocal
    let res := letE tmp xf (matchE (vE tmp) [(.literal 0, litE 0), (.wildcard, subE (vE tmp) (litE 1))])
    coerceE cx (.nat ra.fieldBound) target res
  | .natAdd =>
    let [a, b] := as | tLift (throw "natAdd: arity mismatch")
    let (ea, ra) ← tArgRaw cx vm a
    let (eb, rb) ← tArgRaw cx vm b
    let xa ← coerceE cx ra (.nat natLimit) ea
    let xb ← coerceE cx rb (.nat natLimit) eb
    -- Interval-tracked lazy range check: ZERO check when `ra + rb ≤ 2^56`!
    if ra.isFieldNat && rb.isFieldNat && ra.fieldBound + rb.fieldBound ≤ natLimit then
      coerceE cx (.nat (ra.fieldBound + rb.fieldBound)) target (addE xa xb)
    else
      tMark fun d => { d with needCheckU56 := true }
      let tmp ← tFreshLocal
      let res := letE tmp (addE xa xb) (seqE (callE "check_u56" [vE tmp]) (vE tmp))
      coerceE cx (.nat natLimit) target res
  | .natSub =>
    let [a, b] := as | tLift (throw "natSub: arity mismatch")
    let (ea, ra) ← tArgRaw cx vm a
    let xa ← coerceE cx ra (.nat natLimit) ea
    -- Fast countdown path for literal subtraction `x - k` (`k ∈ 1..4`): ZERO table lookups
    -- and directly recognized by `Depth.Structural`!
    match b with
    | .lit (.nat 0) => coerceE cx (.nat ra.fieldBound) target xa
    | .lit (.nat k) =>
      if k ≤ 4 then
        let tmp ← tFreshLocal
        let res := letE tmp xa (constSubMatch (vE tmp) k)
        coerceE cx (.nat ra.fieldBound) target res
      else
        let (eb, rb) ← tArgRaw cx vm b
        let xb ← coerceE cx rb (.nat natLimit) eb
        tMark fun d => { d with needSubBorrow56 := true }
        let res := .project (callE "sub_borrow_56" [xa, xb]) 0
        coerceE cx (.nat ra.fieldBound) target res
    | _ =>
      let (eb, rb) ← tArgRaw cx vm b
      let xb ← coerceE cx rb (.nat natLimit) eb
      tMark fun d => { d with needSubBorrow56 := true }
      let res := .project (callE "sub_borrow_56" [xa, xb]) 0
      coerceE cx (.nat ra.fieldBound) target res
  | .natMul =>
    let [a, b] := as | tLift (throw "natMul: arity mismatch")
    let (ea, ra) ← tArgRaw cx vm a
    let (eb, rb) ← tArgRaw cx vm b
    let xa ← coerceE cx ra (.nat natLimit) ea
    let xb ← coerceE cx rb (.nat natLimit) eb
    if ra.isFieldNat && rb.isFieldNat && ra.fieldBound * rb.fieldBound ≤ natLimit then
      coerceE cx (.nat (ra.fieldBound * rb.fieldBound)) target (mulE xa xb)
    else
      tMark fun d => { d with needMul56 := true, needCheckU56 := true, needCheckU24 := true }
      coerceE cx (.nat natLimit) target (callE "mul_56" [xa, xb])
  | .natDiv =>
    let [a, b] := as | tLift (throw "natDiv: arity mismatch")
    let xa ← tArgE cx vm a (.nat natLimit)
    let xb ← tArgE cx vm b (.nat natLimit)
    tMark fun d => { d with needDivMod56 := true, needMul56 := true, needCheckU56 := true,
                            needCheckU24 := true, needSubBorrow56 := true }
    let tx ← tFreshLocal
    let ty ← tFreshLocal
    let res := letE tx xa <| letE ty xb <|
      matchE (vE ty)
        [(.literal 0, litE 0),
         (.wildcard, .project (callE "divmod_56" [vE tx, vE ty]) 0)]
    coerceE cx (.nat natLimit) target res
  | .natMod =>
    let [a, b] := as | tLift (throw "natMod: arity mismatch")
    let xa ← tArgE cx vm a (.nat natLimit)
    let xb ← tArgE cx vm b (.nat natLimit)
    tMark fun d => { d with needDivMod56 := true, needMul56 := true, needCheckU56 := true,
                            needCheckU24 := true, needSubBorrow56 := true }
    let tx ← tFreshLocal
    let ty ← tFreshLocal
    let res := letE tx xa <| letE ty xb <|
      matchE (vE ty)
        [(.literal 0, vE tx),
         (.wildcard, .project (callE "divmod_56" [vE tx, vE ty]) 1)]
    coerceE cx (.nat natLimit) target res
  | .natPow =>
    let [a, b] := as | tLift (throw "natPow: arity mismatch")
    let xa ← tArgE cx vm a (.nat natLimit)
    let xb ← tArgE cx vm b (.nat natLimit)
    tMark fun d => { d with needPow56 := true, needDivMod56 := true, needMul56 := true,
                            needCheckU56 := true, needCheckU24 := true, needSubBorrow56 := true }
    coerceE cx (.nat natLimit) target (callE "pow_56" [xa, xb])
  | .natGcd =>
    let [a, b] := as | tLift (throw "natGcd: arity mismatch")
    let xa ← tArgE cx vm a (.nat natLimit)
    let xb ← tArgE cx vm b (.nat natLimit)
    tMark fun d => { d with needGcd56 := true, needDivMod56 := true, needMul56 := true,
                            needCheckU56 := true, needCheckU24 := true, needSubBorrow56 := true }
    coerceE cx (.nat natLimit) target (callE "gcd_56" [xa, xb])
  | .natShl =>
    let [a, b] := as | tLift (throw "natShl: arity mismatch")
    let xa ← tArgE cx vm a (.nat natLimit)
    let xb ← tArgE cx vm b (.nat natLimit)
    tMark fun d => { d with needShl56 := true, needPow56 := true, needDivMod56 := true,
                            needMul56 := true, needCheckU56 := true, needCheckU24 := true,
                            needSubBorrow56 := true }
    coerceE cx (.nat natLimit) target (callE "shl_56" [xa, xb])
  | .natShr =>
    let [a, b] := as | tLift (throw "natShr: arity mismatch")
    let xa ← tArgE cx vm a (.nat natLimit)
    let xb ← tArgE cx vm b (.nat natLimit)
    tMark fun d => { d with needShr56 := true, needPow56 := true, needDivMod56 := true,
                            needMul56 := true, needCheckU56 := true, needCheckU24 := true,
                            needSubBorrow56 := true }
    coerceE cx (.nat natLimit) target (callE "shr_56" [xa, xb])
  | .natBeq =>
    let [a, b] := as | tLift (throw "natBeq: arity mismatch")
    let xa ← tArgE cx vm a (.nat natLimit)
    let xb ← tArgE cx vm b (.nat natLimit)
    let isEq := matchE (subE xa xb) [(.literal 0, litE 1), (.wildcard, litE 0)]
    wrapBool cx isEq target
  | .natBle =>
    let [a, b] := as | tLift (throw "natBle: arity mismatch")
    let xa ← tArgE cx vm a (.nat natLimit)
    let xb ← tArgE cx vm b (.nat natLimit)
    tMark fun d => { d with needSubBorrow56 := true }
    let ge := .project (callE "sub_borrow_56" [xb, xa]) 1
    wrapBool cx ge target
  | .natBlt =>
    let [a, b] := as | tLift (throw "natBlt: arity mismatch")
    let xa ← tArgE cx vm a (.nat natLimit)
    let xb ← tArgE cx vm b (.nat natLimit)
    tMark fun d => { d with needSubBorrow56 := true }
    let ge := .project (callE "sub_borrow_56" [xa, xb]) 1
    wrapBool cx (subE (litE 1) ge) target
  | .natLand | .natLor | .natXor =>
    let [a, b] := as | tLift (throw s!"{op.name}: arity mismatch")
    let xa ← tArgE cx vm a (.nat natLimit)
    let xb ← tArgE cx vm b (.nat natLimit)
    tMark fun d => { d with needU64Bitwise := true }
    let u64Op := match op with
      | .natLand => "UInt64::and" | .natLor => "UInt64::or" | _ => "UInt64::xor"
    let res := callE "UInt64::to_field" [callE u64Op [wordE xa, wordE xb]]
    coerceE cx (.nat natLimit) target res
  | .word .w32 wop =>
    match wop, as with
    | .add, [a, b] =>
      let xa ← tArgE cx vm a .w32
      let xb ← tArgE cx vm b .w32
      coerceE cx .w32 target (callE "UInt32::add" [xa, xb])
    | .sub, [a, b] =>
      let xa ← tArgE cx vm a .w32
      let xb ← tArgE cx vm b .w32
      coerceE cx .w32 target (callE "UInt32::sub" [xa, xb])
    | .mul, [a, b] =>
      let xa ← tArgE cx vm a .w32
      let xb ← tArgE cx vm b .w32
      tMark fun d => { d with needU32Mul := true }
      coerceE cx .w32 target (callE "u32_mul" [xa, xb])
    | .div, [a, b] =>
      let xa ← tArgE cx vm a .w32
      let xb ← tArgE cx vm b .w32
      tMark fun d => { d with needU32Div := true, needDivMod56 := true, needMul56 := true,
                              needCheckU56 := true, needCheckU24 := true, needSubBorrow56 := true }
      coerceE cx .w32 target (callE "u32_div" [xa, xb])
    | .mod, [a, b] =>
      let xa ← tArgE cx vm a .w32
      let xb ← tArgE cx vm b .w32
      tMark fun d => { d with needU32Mod := true, needDivMod56 := true, needMul56 := true,
                              needCheckU56 := true, needCheckU24 := true, needSubBorrow56 := true }
      coerceE cx .w32 target (callE "u32_mod" [xa, xb])
    | .land, [a, b] =>
      let xa ← tArgE cx vm a .w32
      let xb ← tArgE cx vm b .w32
      coerceE cx .w32 target (callE "UInt32::and" [xa, xb])
    | .lor, [a, b] =>
      let xa ← tArgE cx vm a .w32
      let xb ← tArgE cx vm b .w32
      coerceE cx .w32 target (callE "UInt32::or" [xa, xb])
    | .xor, [a, b] =>
      let xa ← tArgE cx vm a .w32
      let xb ← tArgE cx vm b .w32
      coerceE cx .w32 target (callE "UInt32::xor" [xa, xb])
    | .shiftLeft, [a, b] =>
      let xa ← tArgE cx vm a .w32
      let xb ← tArgE cx vm b .w32
      tMark fun d => { d with needU32Shl := true, needU32Mul := true, needPow56 := true,
                              needDivMod56 := true, needMul56 := true, needCheckU56 := true,
                              needCheckU24 := true, needSubBorrow56 := true }
      coerceE cx .w32 target (callE "u32_shl" [xa, xb])
    | .shiftRight, [a, b] =>
      let xa ← tArgE cx vm a .w32
      let xb ← tArgE cx vm b .w32
      tMark fun d => { d with needU32Shr := true, needPow56 := true, needDivMod56 := true,
                              needMul56 := true, needCheckU56 := true, needCheckU24 := true,
                              needSubBorrow56 := true }
      coerceE cx .w32 target (callE "u32_shr" [xa, xb])
    | .complement, [a] =>
      let xa ← tArgE cx vm a .w32
      tMark fun d => { d with needU32Comp := true }
      coerceE cx .w32 target (callE "u32_complement" [xa])
    | .neg, [a] =>
      let xa ← tArgE cx vm a .w32
      coerceE cx .w32 target (callE "UInt32::sub" [callE "UInt32::from_field" [litE 0], xa])
    | .ofNat, [a] =>
      let xa ← tArgE cx vm a (.nat natLimit)
      tMark fun d => { d with needU32OfField := true }
      coerceE cx .w32 target (callE "u32_of_field" [xa])
    | .toNat, [a] =>
      let xa ← tArgE cx vm a .w32
      coerceE cx (.nat (2 ^ 32)) target (u32ToFieldE xa)
    | .convert w', [a] =>
      let xa ← tArgE cx vm a .w32
      match w' with
      | .w8 => coerceE cx .w8 target (callE "UInt8::to_field" [.index (callE "UInt32::to_bytes" [xa]) 0])
      | .w16 =>
        let tmp ← tFreshLocal
        let res := letE tmp (callE "UInt32::to_bytes" [xa]) <|
          addE (callE "UInt8::to_field" [.index (vE tmp) 0])
            (mulE (litE 256) (callE "UInt8::to_field" [.index (vE tmp) 1]))
        coerceE cx .w16 target res
      | .w32 => coerceE cx .w32 target xa
      | .w64 => coerceE cx .w32 .w64 xa >>= coerceE cx .w64 target
    | _, _ => tLift (throw s!"UInt32 primitive {wop.leanName .w32}: unsupported")
  | .word .w64 wop =>
    tMark fun d => { d with needU64Bitwise := true }
    match wop, as with
    | .add, [a, b] =>
      let xa ← tArgE cx vm a .w64
      let xb ← tArgE cx vm b .w64
      coerceE cx .w64 target (.project (callE "UInt64::add" [xa, xb]) 0)
    | .sub, [a, b] =>
      let xa ← tArgE cx vm a .w64
      let xb ← tArgE cx vm b .w64
      coerceE cx .w64 target (.project (callE "UInt64::sub_with_borrow" [xa, xb]) 0)
    | .mul, [a, b] =>
      let xa ← tArgE cx vm a .w64
      let xb ← tArgE cx vm b .w64
      coerceE cx .w64 target (.project (callE "UInt64::mul" [xa, xb]) 0)
    | .land, [a, b] =>
      let xa ← tArgE cx vm a .w64
      let xb ← tArgE cx vm b .w64
      coerceE cx .w64 target (callE "UInt64::and" [xa, xb])
    | .lor, [a, b] =>
      let xa ← tArgE cx vm a .w64
      let xb ← tArgE cx vm b .w64
      coerceE cx .w64 target (callE "UInt64::or" [xa, xb])
    | .xor, [a, b] =>
      let xa ← tArgE cx vm a .w64
      let xb ← tArgE cx vm b .w64
      coerceE cx .w64 target (callE "UInt64::xor" [xa, xb])
    | .shiftRight, [a, b] =>
      let xa ← tArgE cx vm a .w64
      match b with
      | .lit (.nat 32) =>
        let tmp ← tFreshLocal
        let z0 ← tFreshLocal
        let res :=
          letE tmp xa <|
          .letValue (.tuple [.bind z0, .wildcard]) (callE "UInt8::from_fields" [litE 0, litE 0]) <|
          .array [.index (vE tmp) 4, .index (vE tmp) 5, .index (vE tmp) 6, .index (vE tmp) 7,
                  vE z0, vE z0, vE z0, vE z0]
        coerceE cx .w64 target res
      | _ =>
        let xb ← tArgE cx vm b .w64
        tMark fun d => { d with needU64Shr := true, needDivMod56 := true, needPow56 := true,
                                needMul56 := true, needCheckU56 := true, needCheckU24 := true,
                                needSubBorrow56 := true }
        coerceE cx .w64 target (callE "u64_shr" [xa, xb])
    | .shiftLeft, [a, b] =>
      let xa ← tArgE cx vm a .w64
      let xb ← tArgE cx vm b .w64
      tMark fun d => { d with needU64Shl := true, needU32Mul := true, needDivMod56 := true,
                              needPow56 := true, needMul56 := true, needCheckU56 := true,
                              needCheckU24 := true, needSubBorrow56 := true }
      coerceE cx .w64 target (callE "u64_shl" [xa, xb])
    | .complement, [a] =>
      let xa ← tArgE cx vm a .w64
      let tmp ← tFreshLocal
      let res := letE tmp xa <|
        callE "UInt64::from_fields"
          [.array [subE (litE 255) (callE "UInt8::to_field" [.index (vE tmp) 0]),
                   subE (litE 255) (callE "UInt8::to_field" [.index (vE tmp) 1]),
                   subE (litE 255) (callE "UInt8::to_field" [.index (vE tmp) 2]),
                   subE (litE 255) (callE "UInt8::to_field" [.index (vE tmp) 3]),
                   subE (litE 255) (callE "UInt8::to_field" [.index (vE tmp) 4]),
                   subE (litE 255) (callE "UInt8::to_field" [.index (vE tmp) 5]),
                   subE (litE 255) (callE "UInt8::to_field" [.index (vE tmp) 6]),
                   subE (litE 255) (callE "UInt8::to_field" [.index (vE tmp) 7])]]
      coerceE cx .w64 target res
    | .neg, [a] =>
      let xa ← tArgE cx vm a .w64
      coerceE cx .w64 target
        (.project (callE "UInt64::sub_with_borrow" [callE "UInt64::from_field" [litE 0], xa]) 0)
    | .ofNat, [a] =>
      let xa ← tArgE cx vm a (.nat natLimit)
      coerceE cx .w64 target (callE "UInt64::from_field" [xa])
    | .toNat, [a] =>
      let xa ← tArgE cx vm a .w64
      coerceE cx (.nat natLimit) target (callE "UInt64::to_field" [xa])
    | .mulWideLo, [a, b] =>
      let xa ← tArgE cx vm a .w64
      let xb ← tArgE cx vm b .w64
      coerceE cx .w64 target (.project (callE "UInt64::mul" [xa, xb]) 0)
    | .mulWideHi, [a, b] =>
      let xa ← tArgE cx vm a .w64
      let xb ← tArgE cx vm b .w64
      coerceE cx .w64 target (.project (callE "UInt64::mul" [xa, xb]) 1)
    | .convert w', [a] =>
      let xa ← tArgE cx vm a .w64
      match w' with
      | .w8 => coerceE cx .w8 target (callE "UInt8::to_field" [.index xa 0])
      | .w16 =>
        let tmp ← tFreshLocal
        let res := letE tmp xa <|
          addE (callE "UInt8::to_field" [.index (vE tmp) 0])
            (mulE (litE 256) (callE "UInt8::to_field" [.index (vE tmp) 1]))
        coerceE cx .w16 target res
      | .w32 => coerceE cx .w64 .w32 xa >>= coerceE cx .w32 target
      | .w64 => coerceE cx .w64 target xa
    | _, _ => tLift (throw s!"UInt64 primitive {wop.leanName .w64}: unsupported")
  | .word .w8 wop =>
    match wop, as with
    | .ofNat, [a] =>
      let xa ← tArgE cx vm a (.nat natLimit)
      tMark fun d => { d with needDivMod56 := true, needMul56 := true, needCheckU56 := true,
                              needCheckU24 := true, needSubBorrow56 := true }
      coerceE cx .w8 target (.project (callE "divmod_56" [xa, litE 256]) 1)
    | .toNat, [a] => tArgE cx vm a .w8 >>= coerceE cx .w8 target
    | .add, [a, b] =>
      let xa ← tArgE cx vm a .w8
      let xb ← tArgE cx vm b .w8
      tMark fun d => { d with needDivMod56 := true, needMul56 := true, needCheckU56 := true,
                              needCheckU24 := true, needSubBorrow56 := true }
      coerceE cx .w8 target (.project (callE "divmod_56" [addE xa xb, litE 256]) 1)
    | .sub, [a, b] =>
      let xa ← tArgE cx vm a .w8
      let xb ← tArgE cx vm b .w8
      tMark fun d => { d with needDivMod56 := true, needMul56 := true, needCheckU56 := true,
                              needCheckU24 := true, needSubBorrow56 := true }
      coerceE cx .w8 target (.project (callE "divmod_56" [addE (subE (addE xa (litE 256)) xb) (litE 0), litE 256]) 1)
    | .mul, [a, b] =>
      let xa ← tArgE cx vm a .w8
      let xb ← tArgE cx vm b .w8
      tMark fun d => { d with needDivMod56 := true, needMul56 := true, needCheckU56 := true,
                              needCheckU24 := true, needSubBorrow56 := true }
      coerceE cx .w8 target (.project (callE "divmod_56" [mulE xa xb, litE 256]) 1)
    | .convert w', [a] =>
      let xa ← tArgE cx vm a .w8
      match w' with
      | .w8 => coerceE cx .w8 target xa
      | .w16 => coerceE cx .w16 target xa
      | .w32 => coerceE cx .w8 .w32 xa >>= coerceE cx .w32 target
      | .w64 => coerceE cx .w8 .w64 xa >>= coerceE cx .w64 target
    | _, _ => tLift (throw s!"UInt8 primitive {wop.leanName .w8}: unsupported")
  | .word .w16 wop =>
    match wop, as with
    | .ofNat, [a] =>
      let xa ← tArgE cx vm a (.nat natLimit)
      tMark fun d => { d with needDivMod56 := true, needMul56 := true, needCheckU56 := true,
                              needCheckU24 := true, needSubBorrow56 := true }
      coerceE cx .w16 target (.project (callE "divmod_56" [xa, litE 65536]) 1)
    | .toNat, [a] => tArgE cx vm a .w16 >>= coerceE cx .w16 target
    | .add, [a, b] =>
      let xa ← tArgE cx vm a .w16
      let xb ← tArgE cx vm b .w16
      tMark fun d => { d with needDivMod56 := true, needMul56 := true, needCheckU56 := true,
                              needCheckU24 := true, needSubBorrow56 := true }
      coerceE cx .w16 target (.project (callE "divmod_56" [addE xa xb, litE 65536]) 1)
    | .convert w', [a] =>
      let xa ← tArgE cx vm a .w16
      match w' with
      | .w8 =>
        tMark fun d => { d with needDivMod56 := true, needMul56 := true, needCheckU56 := true,
                                needCheckU24 := true, needSubBorrow56 := true }
        coerceE cx .w8 target (.project (callE "divmod_56" [xa, litE 256]) 1)
      | .w16 => coerceE cx .w16 target xa
      | .w32 => coerceE cx .w16 .w32 xa >>= coerceE cx .w32 target
      | .w64 => coerceE cx .w16 .w64 xa >>= coerceE cx .w64 target
    | _, _ => tLift (throw s!"UInt16 primitive {wop.leanName .w16}: unsupported")
  | .arr aop => tLift (throw s!"array primitive {(Prim.arr aop).name}: unsupported")

/-! ## Lowering Typed RHS, Case, and Code -/

/-- A typed dummy value of representation `r` (used solely after unsatisfiable `0 = 1` traps). -/
private def dummyOfRepAux (fuel : Nat) (cx : TCx) : Rep → TLowerM Expr
  | .irr => pure (.tuple [])
  | .nat _ | .w8 | .w16 => pure (litE 0)
  | .w32 => pure (callE "UInt32::from_field" [litE 0])
  | .w64 => do
    tMark fun d => { d with needU64Bitwise := true }
    pure (callE "UInt64::from_field" [litE 0])
  | .enum ind => do
    let some (k :: _) := cx.cert.enum? ind | tLift (throw s!"dummy: empty enum {ind}")
    let some (idx, e) := cx.ctorEntry? k | tLift (throw "dummy: missing enum ctor")
    return .construct (enumName ind) (some []) (ctorNameOf idx e.key) []
  | .data d =>
    match fuel with
    | 0 => tLift (throw s!"dummy: data {d} exceeded depth")
    | fuel' + 1 => do
      let some D := cx.cert.data? d | tLift (throw s!"dummy: missing data {d}")
      -- Pick a non-self-recursive ctor if available, else fail closed.
      let some (k, fl) := D.ctors.find? (fun (_, fl) => fl.all fun s => cx.rep s != .data d)
        | tLift (throw s!"dummy: data {d} has no base constructor")
      let some (idx, e) := cx.ctorEntry? k | tLift (throw "dummy: missing data ctor")
      let args ← fl.mapM fun s => do
        let fr := cx.rep s
        let dv ← dummyOfRepAux fuel' cx fr
        return if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then .store dv else dv
      return .construct (dataName d) (some []) (ctorNameOf idx e.key) args
  | .obj => do
    tMark fun d => { d with needObj := true }
    pure erasedE

private def dummyOfRep (cx : TCx) (r : Rep) : TLowerM Expr :=
  dummyOfRepAux (cx.cert.datas.length + 2) cx r

private def tTrapE (cx : TCx) (r : Rep) (msg : String) : TLowerM Expr := do
  let dv ← dummyOfRep cx r
  return seqE (.builtin (.assertEq (assertion msg)) [litE 0, litE 1]) dv

private def markRep : Rep → TLowerM Unit
  | .obj => tMark fun d => { d with needObj := true }
  | .w64 => tMark fun d => { d with needU64Bitwise := true }
  | _ => pure ()

/-- Track countdown offsets `x = baseNm - d` (guaranteed `baseNm ≥ d` because every
increment came from a `nz`-checked predecessor) so nested `Nat.succ` peeling and
`n + 1` reconstruction (e.g. `fib (n + 2) → fib n + fib (n + 1)`) emit direct
`baseNm - k` expressions that trigger `Aiur.Optimized.Depth.Structural` and drop
the 65,536-row `range16` depth table! -/
abbrev OffMap := List (Var × (String × Nat))

private def stepDownNat (cx : TCx) (offs : OffMap) (x : Var) (nx : String) (rx target : Rep) :
    TLowerM (Expr × Option (String × Nat)) := do
  match offs.lookup x with
  | some (baseNm, d) =>
    if d < 256 then
      let e ← coerceE cx (.nat rx.fieldBound) target (subE (vE baseNm) (litE (d + 1)))
      let off? := match target with | .nat _ => some (baseNm, d + 1) | _ => none
      return (e, off?)
    else
      let e ← coerceE cx (.nat rx.fieldBound) target (subE (vE nx) (litE 1))
      let off? := match target with | .nat _ => some (nx, 1) | _ => none
      return (e, off?)
  | none =>
    let e ← coerceE cx (.nat rx.fieldBound) target (subE (vE nx) (litE 1))
    let off? := match target with | .nat _ => some (nx, 1) | _ => none
    return (e, off?)

def tRhsE (cx : TCx) (vm : TVarMap) (nz : List Var) (offs : OffMap) (r : Rhs) (target : Rep) :
    TLowerM (Expr × Option (String × Nat)) := do
  match r with
  | .arg a =>
    let e ← tArgE cx vm a target
    let off? := match a, target with
      | .var x, .nat _ => offs.lookup x
      | _, _ => none
    return (e, off?)
  | .ctor c as =>
    let some (idx, entry) := cx.ctorEntry? c.key
      | tLift (throw "constructor is not in the constructor table")
    unless as.length == entry.arity && c.arity == entry.arity do
      tLift (throw s!"constructor {ctorNameOf idx entry.key}: arity mismatch")
    let nm := ctorNameOf idx entry.key
    let e : Expr ← match target with
      | .enum ind =>
        pure (.construct (enumName ind) (some []) nm [])
      | .data d => do
        let some D := cx.cert.data? d | tLift (throw s!"ctor: unknown data {d}")
        let some (_, fl) := D.ctors.find? (·.1 == c.key)
          | tLift (throw s!"ctor {nm}: not in data {d}")
        let fieldExprs ← (as.zip fl).mapM fun (a, sh) => do
          let fr := cx.rep sh
          let ae ← tArgE cx vm a fr
          pure (if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then .store ae else ae)
        pure (.construct (dataName d) (some []) nm fieldExprs)
      | _ => do
        tMark fun d => { d with needObj := true }
        let argEs ← as.mapM fun a => do pure (.store (← tArgE cx vm a .obj))
        coerceE cx .obj target (mk nm argEs)
    return (e, none)
  | .proj x c i =>
    let some (nx, rx) := vm.lookup x | tLift (throw s!"unbound variable {x}")
    match rx with
    | .nat _ | .w8 | .w16 =>
      if cx.P.known.natSucc == some c && i == 0 then
        -- Inside a `natSucc` branch (`x ∈ nz`), `x ≠ 0` is already proved by the enclosing
        -- `match x { 0 => ..., _ => ... }`: emit direct `base - (d + 1)` so `Depth.Structural`
        -- sees countdown recursion directly with zero extra columns and zero `range16` table!
        if nz.contains x then
          stepDownNat cx offs x nx rx target
        else
          let tr ← tTrapE cx (.nat rx.fieldBound) "Nat.zero has no field"
          let res := matchE (vE nx) [(.literal 0, tr), (.wildcard, subE (vE nx) (litE 1))]
          return (← coerceE cx (.nat rx.fieldBound) target res, none)
      else return (← tTrapE cx target "projection of non-Nat.succ on Nat", none)
    | .data d =>
      let some D := cx.cert.data? d | tLift (throw s!"proj: unknown data {d}")
      match D.ctors.find? (·.1 == c) with
      | some (_, fl) =>
        match cx.ctorEntry? c, fl[i]? with
        | some (idx, entry), some sh =>
          let nm := ctorNameOf idx entry.key
          let fr := cx.rep sh
          let q ← tFreshLocal
          let body0 := if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then .load (vE q) else vE q
          let body ← coerceE cx fr target body0
          let pats := (List.range entry.arity).map fun j => if j = i then .bind q else .wildcard
          return (matchE (vE nx) [(.construct (.named (dataName d) []) nm pats, body)], none)
        | _, _ => return (← tTrapE cx target "projection of missing data field", none)
      | none => return (← tTrapE cx target "projection of missing data ctor", none)
    | .obj =>
      tMark fun d => { d with needObj := true }
      let raw := Lower.projE ⟨cx.P⟩ nx c i
      return (← coerceE cx .obj target raw, none)
    | _ => return (← tTrapE cx target "projection on non-constructor value", none)
  | .prim op as =>
    -- Countdown offset fast paths for `natPred`, `natSub _ 1`, and `natAdd (base - d) k` (`k ≤ d`):
    -- eliminates redundant range checks AND preserves `Depth.Structural` `.down` relations!
    match op, as, target with
    | .natPred, [.var x], .nat _ =>
      if nz.contains x then
        match vm.lookup x with
        | some (nx, rx) =>
          if rx.isFieldNat then stepDownNat cx offs x nx rx target
          else return (← tPrimE cx vm op as target, none)
        | none => return (← tPrimE cx vm op as target, none)
      else return (← tPrimE cx vm op as target, none)
    | .natSub, [.var x, .lit (.nat 1)], .nat _ =>
      if nz.contains x then
        match vm.lookup x with
        | some (nx, rx) =>
          if rx.isFieldNat then stepDownNat cx offs x nx rx target
          else return (← tPrimE cx vm op as target, none)
        | none => return (← tPrimE cx vm op as target, none)
      else return (← tPrimE cx vm op as target, none)
    | .natAdd, [.var x, .lit (.nat k)], .nat _
    | .natAdd, [.lit (.nat k), .var x], .nat _ =>
      match offs.lookup x with
      | some (baseNm, d) =>
        if k ≤ d then
          if k == d then return (vE baseNm, some (baseNm, 0))
          else return (subE (vE baseNm) (litE (d - k)), some (baseNm, d - k))
        else return (← tPrimE cx vm op as target, none)
      | none => return (← tPrimE cx vm op as target, none)
    | _, _, _ => return (← tPrimE cx vm op as target, none)
  | .call f as =>
    let some fd := cx.P.fun? f | tLift (throw s!"unknown function {f}")
    unless f < cx.P.size do tLift (throw s!"function {f} outside program size")
    unless as.length == fd.params.length do tLift (throw s!"function {f}: arity mismatch")
    let fsh := cx.funShapes f
    let paramReps := (fd.params.map (·.1)).map fun p => cx.rep (fsh.var p)
    let retRep := cx.rep fsh.ret
    let argEs ← (as.zip paramReps).mapM fun (a, pr) => tArgE cx vm a pr
    return (← coerceE cx retRep target (callE (funName f) argEs), none)

/-- Lower `case x alts d` specialized to the scrutinee's `Rep`!
* On `.nat _`/`.w8`/`.w16`: direct 2-arm `match x { 0 => z, _ => s }` (ZERO `Obj` arms!).
* On `.enum ind`: direct match over `E<ind>` tags (ZERO `Obj` / `Bytes` arms!).
* On `.data d`: direct match over `D<d>` constructors (ZERO `Obj` / `Bytes` arms!).
* On `.obj`: existing full `Lower.caseE` semantics. -/
def tCaseE (cx : TCx) (nx : String) (rx : Rep) (retR : Rep)
    (alts : List (CtorKey × Expr)) (d : Option Expr) : TLowerM Expr := do
  let firsts := Lower.firstPerKey [] alts
  let fb ← match d with
    | some e => pure e
    | none => tTrapE cx retR "no alternative"
  let pick (ok : Option CtorKey) : TLowerM Expr := do
    match ok with
    | some k => return ((firsts.find? (·.1 == k)).map (·.2)).getD fb
    | none => tTrapE cx retR "unpinned Nat literal under case"
  match rx with
  | .nat _ | .w8 | .w16 =>
    let zBody ← pick cx.P.known.natZero
    let sBody ← pick cx.P.known.natSucc
    return matchE (vE nx) [(.literal 0, zBody), (.wildcard, sBody)]
  | .enum ind =>
    let some ks := cx.cert.enum? ind | tLift (throw s!"case: unknown enum {ind}")
    let arms ← firsts.filterMapM fun (k, body) => do
      if ks.contains k then
        match cx.ctorEntry? k with
        | some (idx, entry) =>
          return some (.construct (.named (enumName ind) []) (ctorNameOf idx entry.key) [], body)
        | none => return none
      else return none
    let dfltArm := match d with | some e => [(.wildcard, e)] | none => []
    return matchE (vE nx) (arms ++ dfltArm)
  | .data did =>
    let some D := cx.cert.data? did | tLift (throw s!"case: unknown data {did}")
    let arms ← firsts.filterMapM fun (k, body) => do
      if D.ctors.any (·.1 == k) then
        match cx.ctorEntry? k with
        | some (idx, entry) =>
          return some (.construct (.named (dataName did) []) (ctorNameOf idx entry.key)
            (List.replicate entry.arity .wildcard), body)
        | none => return none
      else return none
    let dfltArm := match d with | some e => [(.wildcard, e)] | none => []
    return matchE (vE nx) (arms ++ dfltArm)
  | .obj =>
    tMark fun dm => { dm with needObj := true }
    let arms := Lower.ctorArms ⟨cx.P⟩ firsts
    let q ← tFreshLocal
    let zBody ← pick cx.P.known.natZero
    let sBody ← pick cx.P.known.natSucc
    let natArm : Pat × Expr := (pN (.bind q), matchE (vE q) [(.literal 0, zBody), (.wildcard, sBody)])
    let erasedArm : Pat × Expr := (pC "E" [], ← tTrapE cx retR "case on an erased value")
    let strArm : Pat × Expr := (pC "S" [.wildcard], ← tTrapE cx retR "case on a string literal")
    let dfltArm := match d with | some e => [(.wildcard, e)] | none => []
    return matchE (vE nx) (arms ++ [natArm, erasedArm, strArm] ++ dfltArm)
  | .irr => tTrapE cx retR "case on erased value"
  | _ => tLift (throw s!"case on unsupported rep {reprStr rx}")

private def freeArgNames (vm : TVarMap) (bound : List Var) : Arg → List String
  | .var x =>
    if bound.contains x then []
    else match vm.lookup x with | some (nm, _) => [nm] | none => []
  | _ => []

private def freeArgsNames (vm : TVarMap) (bound : List Var) (as : List Arg) : List String :=
  as.flatMap (freeArgNames vm bound)

private def freeRhsNames (vm : TVarMap) (bound : List Var) : Rhs → List String
  | .arg a => freeArgNames vm bound a
  | .ctor _ as | .prim _ as | .call _ as => freeArgsNames vm bound as
  | .proj x _ _ => freeArgNames vm bound (.var x)

mutual

private def freeCodeNames (vm : TVarMap) (bound : List Var)
    (jmap : List (JoinId × List String)) : Code → List String
  | .bind x r k => freeRhsNames vm bound r ++ freeCodeNames vm (x :: bound) jmap k
  | .jp j' ps' isRec' b' k' =>
    let bf := freeCodeNames vm (ps' ++ bound) (if isRec' then (j', []) :: jmap else jmap) b'
    bf ++ freeCodeNames vm bound ((j', bf) :: jmap) k'
  | .jmp j' as => (jmap.lookup j').getD [] ++ freeArgsNames vm bound as
  | .case x alts d =>
    freeArgNames vm bound (.var x) ++ freeAltsNames vm bound jmap alts ++ freeOptNames vm bound jmap d
  | .ret a => freeArgNames vm bound a
  | .tcall _ as => freeArgsNames vm bound as
  | .trap => []

private def freeAltsNames (vm : TVarMap) (bound : List Var)
    (jmap : List (JoinId × List String)) : List Alt → List String
  | [] => []
  | .mk _ b :: rest => freeCodeNames vm bound jmap b ++ freeAltsNames vm bound jmap rest

private def freeOptNames (vm : TVarMap) (bound : List Var)
    (jmap : List (JoinId × List String)) : Option Code → List String
  | none => []
  | some c => freeCodeNames vm bound jmap c

end

/-- Collect all `(AiurName, Rep)` pairs captured by `jenv` and free in `body`,
preserving exact shadowed Aiur local names (never conflating outer/inner bindings
of the same `Fir.Var`). -/
private def collectJpCaptures (vm : TVarMap) (jenv : List TJEntry) (ps : List Var)
    (j : JoinId) (isRec : Bool) (body : Code) (filterCaps : Bool) : List (String × Rep) :=
  let allScope : List (String × Rep) :=
    let fromVm := vm.map fun (_, nm, r) => (nm, r)
    let fromJ := jenv.flatMap fun je => je.capVars
    (fromVm ++ fromJ).foldl (init := []) fun acc p =>
      if acc.any (·.1 == p.1) then acc else acc ++ [p]
  if !filterCaps then allScope
  else
    let initJmap :=
      let base := jenv.map fun je => (je.id, je.capVars.map (·.1))
      if isRec then (j, []) :: base else base
    let needed := freeCodeNames vm ps initJmap body
    allScope.filter fun p => needed.contains p.1

mutual

def tCodeE (cx : TCx) (fid : FunId) (fsh : FunShapes) (retR : Rep)
    (vm : TVarMap) (jenv : List TJEntry) (nz : List Var) (offs : OffMap) : Code → TLowerM Expr
  | .bind x r k => do
    let rx := cx.rep (fsh.var x)
    markRep rx
    let (re, xOff?) ← tRhsE cx vm nz offs r rx
    let nx ← tFreshLocal
    let nz' := nz.filter (· != x)
    let offs' := match xOff? with
      | some off => (x, off) :: offs.filter (·.1 != x)
      | none => offs.filter (·.1 != x)
    let ke ← tCodeE cx fid fsh retR ((x, nx, rx) :: vm) jenv nz' offs' k
    return letE nx re ke
  | .jp j ps isRec body k => do
    let capVars := collectJpCaptures vm jenv ps j isRec body cx.sched.filterJpCaptures
    let uid ← tFreshJp
    let jpName := jpFunName fid uid
    let paramReps := ps.map fun p => cx.rep (fsh.var p)
    for (_, cr) in capVars do markRep cr
    for pr in paramReps do markRep pr
    markRep retR
    let paramNames ← tFreshLocals ps.length
    let ji : TJEntry := ⟨j, jpName, capVars, paramReps, retR⟩
    let bodyVm := tBindVm vm ps (paramNames.zip paramReps)
    let bodyJenv := if isRec then ji :: jenv else jenv
    let bodyNz := nz.filter fun v => !ps.contains v
    let bodyOffs : OffMap :=
      (ps.zip (paramNames.zip paramReps)).filterMap fun (p, nm, r) =>
        match r with | .nat _ => some (p, (nm, 0)) | _ => none
    let bodyExpr ← tCodeE cx fid fsh retR bodyVm bodyJenv bodyNz bodyOffs body
    let inlineFlag := shouldInlineJp cx.sched j isRec body k
    tEmitLifted {
      name := jpName
      params := capVars.map (fun (nm, r) => (nm, r.aiurTy)) ++
        (paramNames.zip paramReps).map (fun (nm, r) => (nm, r.aiurTy))
      result := retR.aiurTy
      body := bodyExpr
      isInline := inlineFlag
    }
    tCodeE cx fid fsh retR vm (ji :: jenv) nz offs k
  | .jmp j as => do
    let some ji := jenv.find? (·.id == j) | tLift (throw s!"unbound join point {j}")
    unless as.length == ji.paramReps.length do
      tLift (throw s!"join point {j}: arity mismatch")
    let argExprs ← (as.zip ji.paramReps).mapM fun (a, pr) => tArgE cx vm a pr
    let capExprs := ji.capVars.map fun (nm, _) => vE nm
    return callE ji.fnName (capExprs ++ argExprs)
  | .case x alts d => do
    let some (nx, rx) := vm.lookup x | tLift (throw s!"unbound variable {x}")
    let altExprs ← tAltsE cx fid fsh retR vm jenv nz offs x rx alts
    let dExpr ← tOptE cx fid fsh retR vm jenv nz offs d
    tCaseE cx nx rx retR altExprs dExpr
  | .ret a => tArgE cx vm a retR
  | .tcall f as => do
    let some fd := cx.P.fun? f | tLift (throw s!"unknown function {f}")
    unless f < cx.P.size do tLift (throw s!"function {f} outside program size")
    unless as.length == fd.params.length do tLift (throw s!"function {f}: arity mismatch")
    let gsh := cx.funShapes f
    let paramReps := (fd.params.map (·.1)).map fun p => cx.rep (gsh.var p)
    let gRet := cx.rep gsh.ret
    let argExprs ← (as.zip paramReps).mapM fun (a, pr) => tArgE cx vm a pr
    coerceE cx gRet retR (callE (funName f) argExprs)
  | .trap => tTrapE cx retR "trap"

def tAltsE (cx : TCx) (fid : FunId) (fsh : FunShapes) (retR : Rep)
    (vm : TVarMap) (jenv : List TJEntry) (nz : List Var) (offs : OffMap) (scrut : Var) (scrutR : Rep) :
    List Alt → TLowerM (List (CtorKey × Expr))
  | [] => pure []
  | .mk k b :: rest => do
    -- Inside the `natSucc` branch of a `Field`-represented `Nat`, `scrut ≠ 0` is guaranteed!
    let nz' :=
      if scrutR.isFieldNat && cx.P.known.natSucc == some k then
        if nz.contains scrut then nz else scrut :: nz
      else nz
    let be ← tCodeE cx fid fsh retR vm jenv nz' offs b
    let re ← tAltsE cx fid fsh retR vm jenv nz offs scrut scrutR rest
    return (k, be) :: re

def tOptE (cx : TCx) (fid : FunId) (fsh : FunShapes) (retR : Rep)
    (vm : TVarMap) (jenv : List TJEntry) (nz : List Var) (offs : OffMap) :
    Option Code → TLowerM (Option Expr)
  | none => pure none
  | some c => do return some (← tCodeE cx fid fsh retR vm jenv nz offs c)

end

/-! ## Lowering Functions, Entries, Dedicated Enums, and Demand-Linked Module -/

def tFunE (cx : TCx) (fid : FunId) (fd : Fun) : TLowerM (List Fn) := do
  let fsh := cx.funShapes fid
  let paramReps := (fd.params.map (·.1)).map fun p => cx.rep (fsh.var p)
  let retR := cx.rep fsh.ret
  for pr in paramReps do markRep pr
  markRep retR
  let paramNames ← tFreshLocals fd.params.length
  let vm := tBindVm [] (fd.params.map Prod.fst) (paramNames.zip paramReps)
  let initOffs : OffMap :=
    ((fd.params.map Prod.fst).zip (paramNames.zip paramReps)).filterMap fun (p, nm, r) =>
      match r with | .nat _ => some (p, (nm, 0)) | _ => none
  let prevLifted := (← get).lifted
  modify fun st => { st with lifted := [] }
  let body ← tCodeE cx fid fsh retR vm [] [] initOffs fd.body
  let liftedHere := (← get).lifted
  modify fun st => { st with lifted := prevLifted }
  let mainFn : Fn := {
    name := funName fid
    params := (paramNames.zip paramReps).map fun (nm, r) => (nm, r.aiurTy)
    result := retR.aiurTy
    body
    isInline := shouldInlineFun cx.P cx.sched fid fd
  }
  return mainFn :: liftedHere

/-- Entry wrapper `main<i>(x0 … : Field) -> <unboxed retTy>`: range-checks each
`Field` input once to `< 2^56` (via `check_u56`) and invokes `f<f>` directly
with unboxed arguments, returning `f<f>`'s unboxed result! -/
def tEntryE (cx : TCx) (i : Nat) (f : FunId) : TLowerM (Fn × Rep) := do
  let some fd := cx.P.fun? f | tLift (throw s!"export {i}: function {f} is missing")
  unless f < cx.P.size do tLift (throw s!"export {i}: function {f} outside program size")
  let fsh := cx.funShapes f
  let paramReps := (fd.params.map (·.1)).map fun p => cx.rep (fsh.var p)
  let retR := cx.rep fsh.ret
  let n := fd.params.length
  if n > 0 then
    tMark fun d => { d with needCheckU56 := true }
  let argExprs ← ((List.range n).zip paramReps).mapM fun (j, pr) => do
    let pName := entryParamName j
    let checked := seqE (callE "check_u56" [vE pName]) (vE pName)
    coerceE cx (.nat natLimit) pr checked
  return ({
    name := entryName i
    params := (List.range n).map fun j => (entryParamName j, (.field : Ty))
    result := retR.aiurTy
    body := callE (funName f) argExprs
    isInline := false
  }, retR)

/-- Dedicated Aiur enum declarations for all valid `ShapeCert` enumerations. -/
def enumDecls (cx : TCx) : List Aiur.Generic.EnumDecl :=
  cx.cert.enums.filterMap fun (ind, ks) =>
    if validEnum cx.P cx.cert ind then
      let cs := ks.filterMap fun k =>
        (cx.ctorEntry? k).map fun (idx, e) =>
          ({ name := ctorNameOf idx e.key, fields := [] } : Aiur.Generic.ConstructorDecl)
      some { name := enumName ind, constructors := cs }
    else none

/-- Dedicated Aiur enum declarations for all valid `ShapeCert` data entries
(inline unboxed non-recursive fields; `&D<d>` pointers only on cyclic fields). -/
def dataDecls (cx : TCx) : List Aiur.Generic.EnumDecl :=
  cx.cert.datas.zipIdx.filterMap fun (D, d) =>
    if validData cx.P cx.cert d then
      let cs := D.ctors.filterMap fun (k, fl) =>
        (cx.ctorEntry? k).map fun (idx, e) =>
          let fieldTys := fl.map fun sh =>
            let fr := cx.rep sh
            if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then .ptr fr.aiurTy else fr.aiurTy
          ({ name := ctorNameOf idx e.key, fields := fieldTys } : Aiur.Generic.ConstructorDecl)
      some { name := dataName d, constructors := cs }
    else none

/-- Emit ONLY the helper functions actually demanded by the lowered program! -/
def demandedHelpers (d : Demand) (usePair : Bool) : List Fn :=
  let needSplit := d.needMul56
  let needU24 := d.needCheckU24 || d.needMul56
  let needU56 := d.needCheckU56 || d.needMul56 || d.needDivMod56
  (if needU56 then [checkU8Fn usePair, checkU56Fn usePair] else []) ++
  (if d.needCheckU16 then [checkU16Fn usePair] else []) ++
  (if needU24 then [checkU24Fn usePair] else []) ++
  (if d.needSubBorrow56 then [subBorrow56Fn usePair] else []) ++
  (if needSplit then [split32_24Fn usePair] else []) ++
  (if d.needMul56 then [mul56Fn] else []) ++
  (if d.needDivMod56 then [divmod56Fn] else []) ++
  (if d.needPow56 then [pow56LoopFn, pow56Fn] else []) ++
  (if d.needGcd56 then [gcd56Fn] else []) ++
  (if d.needShl56 then [shl56Fn] else []) ++
  (if d.needShr56 then [shr56Fn] else []) ++
  (if d.needU32Mul then [u32MulFn] else []) ++
  (if d.needU32Comp then [u32ComplementFn] else []) ++
  (if d.needU32Div then [u32DivFn] else []) ++
  (if d.needU32Mod then [u32ModFn] else []) ++
  (if d.needU32Shl then [u32ShlFn] else []) ++
  (if d.needU32Shr then [u32ShrFn] else []) ++
  (if d.needU32OfField then [u32OfFieldFn] else []) ++
  (if d.needU64Shl then [u64ShlFn] else []) ++
  (if d.needU64Shr then [u64ShrFn] else [])

/-- Result of typed lowering: the `Prog` generic program, the selected `TableTier`,
the result `Rep` of each export, and the recorded `Demand`. -/
structure LoweredProgram where
  program : Aiur.Generic.Program Nat
  tier : TableTier
  exportReps : List Rep
  demand : Demand
  cert : ShapeCert

/-- Lower `(P, cert, sched)` to a typed/unboxed `LoweredProgram` with demand-driven
helper and table selection. -/
def lowerProgram (P : Program) (cert : ShapeCert) (sched : CircuitSchedule := {}) :
    Except String LoweredProgram := do
  unless allDistinct (P.ctors.map (·.key)) do
    throw "duplicate constructor key in constructor table"
  unless allDistinct (objCtorNames P) do
    throw "duplicate constructor name in constructor table"
  let feat := scanFeatures P
  let cx : TCx := { P, cert, feat, sched }
  let ((fns, entriesWithReps), st) ← (do
    for entry in cx.cert.datas.zipIdx do
      let D : IxCC.Shape.DataDecl CtorKey := entry.1
      let d : Nat := entry.2
      if validData cx.P cx.cert d then
        for (_, fl) in D.ctors do
          for sh in fl do
            markRep (cx.rep sh)
    let fnGroups ← P.funList.mapM fun (f, fd) => tFunE cx f fd
    let entries ← ((List.range P.exports.length).zip P.exports).mapM fun (i, f) => tEntryE cx i f
    pure (fnGroups.flatten, entries) : TLowerM _).run {}
  let d := st.demand
  let usesRangeCheck :=
    d.needCheckU56 || d.needCheckU16 || d.needCheckU24 || d.needSubBorrow56 ||
    d.needMul56 || d.needDivMod56
  let tier :=
    if !sched.demandLink then .u64
    else if d.needU64Bitwise then .u64
    else tableTier feat sched usesRangeCheck
  let usePair := tier == .u32 || tier == .u64
  let helpers := demandedHelpers d usePair
  let enums :=
    enumDecls cx ++
    dataDecls cx ++
    (if d.needBytes || d.needObj then [Lower.bytesEnumDecl] else []) ++
    (if d.needObj then [Lower.objEnumDecl P] else [])
  let fns := fns.map IxCC.AiurBackend.Peephole.rewriteFn
  return {
    program := { functions := entriesWithReps.map Prod.fst ++ fns ++ helpers, enums }
    tier
    exportReps := entriesWithReps.map Prod.snd
    demand := d
    cert
  }

/-- Link a typed `LoweredProgram` with ONLY the Formal Aiur library modules
required by its `TableTier`!
* `.none` → zero library tables (0 table rows!)
* `.byte256` → slim 256-row `U8Byte` table ONLY (256 table rows!)
* `.u32` → `Aiur.Library.U32.source`
* `.u64` → `Aiur.Library.U32.source` + `Aiur.Library.U64.declarations`. -/
def linkedProgram (F : Type) [NatCast F] (lp : LoweredProgram) : Aiur.Modules.Program F :=
  let progMod : Aiur.Modules.Program Nat :=
    { modules := [{ name := moduleName, body := .definitions { program := lp.program } }] }
  let combined : Aiur.Modules.Program Nat := match lp.tier with
    | .none => progMod
    | .byte256 => u8ByteModule.append progMod
    | .u32 => Aiur.Library.U32.source.append progMod
    | .u64 => (Aiur.Library.U32.source.append Aiur.Library.U64.declarations).append progMod
  combined.toField F

end IxCC.AiurBackend.TypedLower
