import IxCCAiur.FieldLower
import IxCCAiur.FieldLowerProof
import IxCCAiur.WitnessIO
import IxCCAiur.Blake3Spec
import Aiur.Library.Field.Goldilocks
import Aiur.Library.Field.Goldilocks.Emulated
import Aiur.Library.Blake3
import Aiur.Library.Blake3.Goldilocks
import Aiur.Library.Blake3.BN254

/-! # Certified Compression Intrinsic Lowering, Multi-Field Linking & Custom Entry Aliasing

Extends `IxCCAiur`'s `@[circuit_intrinsic "..."]` lowering pipeline (building on
`FieldLower`, `Blake3Spec`, and `WitnessIO`) for production recursive compression
verifiers (`CompressWrap`, `CompressGL`, `CompressNarrowFixed`, `CompressFinalNarrow`):

1. **Compression intrinsic taxonomy (`CompressionOp`)**:
   - Ambient field ops `field.{add,sub,mul,neg,inv,div,is_zero,eq}` (delegated to
     `FieldLower`),
   - Native / Emulated Goldilocks field ops
     `goldilocks.{add,sub,mul,neg,inv,is_zero,eq,ext_add,ext_sub,ext_mul,ext_inv}`
     lowering to `Goldilocks::*` (linking `Aiur.Library.Field.Goldilocks` natively on
     Goldilocks, or `Aiur.Library.Field.Goldilocks.Emulated` on BN254 / BLS12-381
     when `--emulate-goldilocks` is enabled),
   - BLAKE3 block / stream ops `blake3.{compress_init,hash,pack_digest}` linking
     `Aiur.Library.Blake3` (certified by `IxCCAiur.Blake3Spec`),
   - Witness-stream channel ops `stark.io.{read_channel,read_byte_stream}` and
     `kzg.io.{read_channel,sized_channel}` lowering to `WitnessIO`'s checked
     `StarkIO::*` and `KzgIO::*` readers.
2. **Multi-field Goldilocks emulation bounds (`bls12381_emulated_product_bound`,
   `bls12381_emulated_reduction_bound`)**:
   Proves that `Aiur.Library.Field.Goldilocks.Emulated` never wraps in `BLS12-381 Fr`
   (complementing `Aiur.Library.Field.Goldilocks.Emulated.product_bound` /
   `reduction_bound` for `BN254 Fr`).
3. **Plainness preservation (`compressionOp_plain`, `lowerCompressionOps_plain`)**:
   Proves every lowered intrinsic expression and transformed function body preserves
   `Lower.isPlainExpr = true`.
4. **Custom entry-point aliasing (`aliasEntry`, `--entry-name`, `--assert-ok`) &
   certified backward soundness (`aliasEntry_sound`, `aliasEntry_sound_of_check`)**:
   Exports any lowered `Prog::main<i>` under a custom qualified name (e.g.
   `CompressWrap::verify_root`, `CompressGL::verify_root`,
   `CompressNarrowFixed::step_v1`, `CompressFinalNarrow::verify_accumulator_v1`)
   with an optional `assert_eq!(result, 1)` unit-returning ABI adapter, keeping
   `Prog::main<i>` intact and proving exact backward equivalence.
5. **Deduplicated multi-field linker (`linkedProgramWith`)**:
   Demand-links `U8Byte`, `UInt8`, `UInt32`, `UInt64`, `Lists`, `Fields`, `Bytes`,
   `Blake3`, `Goldilocks` (native or emulated), `StarkIO`, `KzgIO`, `Prog`, and any
   custom entry module without duplicate module or signature declarations over
   Goldilocks, BN254 `Fr`, or BLS12-381 `Fr`.

Pure Lean 4, strictly total (zero `partial`), zero `sorry`, zero `native_decide`,
zero `bv_decide`. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.CompressionIntrinsics

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxCC.AiurBackend.Lower
  (Expr Pat Fn moduleName qualified funName entryName
   vE litE letE callE hasDoubleColon allDistinct allDistinct_iff_nodup
   isPlainExpr isPlainList isPlainArms isPlainExpr_map)
open IxCC.AiurBackend.TypedRep (TableTier)
open IxCC.AiurBackend.TypedLower (LoweredProgram)
open IxCC.AiurBackend.InlineFuse (pruneUnreachable)
open IxCC.AiurBackend.FieldLower
  (FieldOp fieldOpExpr fieldOpBody allFieldParams usesFieldsLibrary checkFieldsIsZero
   isPlainExpr_fieldOpExpr isPlainExpr_fieldOpBody)
open IxCC.AiurBackend.Gadgets
  (WorldHasFn evalFn_plain_inv evalExpr_var_inv evalExpr_literal_inv)

/-! ## Section 1: Compression Intrinsic Taxonomy (`CompressionOp`) -/

/-- Native or emulated Goldilocks base and cubic-extension field operations. -/
inductive GoldilocksOp where
  | add
  | sub
  | mul
  | neg
  | inv
  | isZero
  | eq
  | extAdd
  | extSub
  | extMul
  | extInv
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Parse `@[circuit_intrinsic "goldilocks.*"]` into a `GoldilocksOp`. -/
def GoldilocksOp.ofIntrinsicName? : String → Option GoldilocksOp
  | "goldilocks.add" => some .add
  | "goldilocks.sub" => some .sub
  | "goldilocks.mul" => some .mul
  | "goldilocks.neg" => some .neg
  | "goldilocks.inv" => some .inv
  | "goldilocks.is_zero" => some .isZero
  | "goldilocks.eq" => some .eq
  | "goldilocks.ext_add" => some .extAdd
  | "goldilocks.ext_sub" => some .extSub
  | "goldilocks.ext_mul" => some .extMul
  | "goldilocks.ext_inv" => some .extInv
  | _ => none

/-- Canonical `@[circuit_intrinsic "..."]` name of a `GoldilocksOp`. -/
def GoldilocksOp.intrinsicName : GoldilocksOp → String
  | .add => "goldilocks.add"
  | .sub => "goldilocks.sub"
  | .mul => "goldilocks.mul"
  | .neg => "goldilocks.neg"
  | .inv => "goldilocks.inv"
  | .isZero => "goldilocks.is_zero"
  | .eq => "goldilocks.eq"
  | .extAdd => "goldilocks.ext_add"
  | .extSub => "goldilocks.ext_sub"
  | .extMul => "goldilocks.ext_mul"
  | .extInv => "goldilocks.ext_inv"

/-- Target qualified function name in `Goldilocks` (shared by both
`Aiur.Library.Field.Goldilocks` and `Aiur.Library.Field.Goldilocks.Emulated`). -/
def GoldilocksOp.qualifiedCall : GoldilocksOp → String
  | .add => "Goldilocks::gl_add"
  | .sub => "Goldilocks::gl_sub"
  | .mul => "Goldilocks::gl_mul"
  | .neg => "Goldilocks::gl_neg"
  | .inv => "Goldilocks::gl_inverse"
  | .isZero => "Goldilocks::gl_is_zero"
  | .eq => "Goldilocks::gl_eq"
  | .extAdd => "Goldilocks::eg_add"
  | .extSub => "Goldilocks::eg_sub"
  | .extMul => "Goldilocks::eg_mul"
  | .extInv => "Goldilocks::eg_inverse"

/-- Operand arity of a `GoldilocksOp` (counting each `ExtGoldilocks = [Field; 3]` as 1). -/
def GoldilocksOp.arity : GoldilocksOp → Nat
  | .add | .sub | .mul | .eq | .extAdd | .extSub | .extMul => 2
  | .neg | .inv | .isZero | .extInv => 1

/-- True iff `op` operates on cubic extension elements `ExtGoldilocks = [Field; 3]`. -/
def GoldilocksOp.isExt : GoldilocksOp → Bool
  | .extAdd | .extSub | .extMul | .extInv => true
  | _ => false

/-- BLAKE3 block and stream operations backed by `Aiur.Library.Blake3` + `Blake3Spec`. -/
inductive Blake3Op where
  | compressInit
  | hash
  | packDigest
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Parse `@[circuit_intrinsic "blake3.*"]` into a `Blake3Op`. -/
def Blake3Op.ofIntrinsicName? : String → Option Blake3Op
  | "blake3.compress_init" => some .compressInit
  | "blake3.hash" => some .hash
  | "blake3.pack_digest" => some .packDigest
  | _ => none

/-- Canonical `@[circuit_intrinsic "..."]` name of a `Blake3Op`. -/
def Blake3Op.intrinsicName : Blake3Op → String
  | .compressInit => "blake3.compress_init"
  | .hash => "blake3.hash"
  | .packDigest => "blake3.pack_digest"

/-- Target qualified function name in `Aiur.Library.Blake3`. -/
def Blake3Op.qualifiedCall : Blake3Op → String
  | .compressInit => "Blake3::compress_init"
  | .hash => "Blake3::hash"
  | .packDigest => "Blake3::pack_digest"

/-- Operand arity of a `Blake3Op`. -/
def Blake3Op.arity : Blake3Op → Nat
  | .compressInit => 5
  | .hash | .packDigest => 1

/-- Checked witness-stream channel operations backed by `IxCCAiur.WitnessIO`. -/
inductive WitnessOp where
  | starkReadChannel
  | starkReadByteStream
  | kzgReadChannel
  | kzgSizedChannel
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Parse `@[circuit_intrinsic "stark.io.*"]` / `"kzg.io.*"` into a `WitnessOp`. -/
def WitnessOp.ofIntrinsicName? : String → Option WitnessOp
  | "stark.io.read_channel" => some .starkReadChannel
  | "stark.io.read_byte_stream" => some .starkReadByteStream
  | "kzg.io.read_channel" => some .kzgReadChannel
  | "kzg.io.sized_channel" => some .kzgSizedChannel
  | _ => none

/-- Canonical `@[circuit_intrinsic "..."]` name of a `WitnessOp`. -/
def WitnessOp.intrinsicName : WitnessOp → String
  | .starkReadChannel => "stark.io.read_channel"
  | .starkReadByteStream => "stark.io.read_byte_stream"
  | .kzgReadChannel => "kzg.io.read_channel"
  | .kzgSizedChannel => "kzg.io.sized_channel"

/-- Target qualified function name in `StarkIO` / `KzgIO` (`WitnessIO`). -/
def WitnessOp.qualifiedCall : WitnessOp → String
  | .starkReadChannel => "StarkIO::read_channel"
  | .starkReadByteStream => "StarkIO::read_byte_stream"
  | .kzgReadChannel => "KzgIO::read_stream"
  | .kzgSizedChannel => "KzgIO::sized_channel"

/-- Operand arity of a `WitnessOp`. -/
def WitnessOp.arity : WitnessOp → Nat
  | .starkReadChannel | .kzgReadChannel | .kzgSizedChannel => 1
  | .starkReadByteStream => 3

/-- Unified compression-verifier intrinsic taxonomy covering ambient prime-field
ops, native/emulated Goldilocks base & cubic-extension ops, BLAKE3 compression &
hashing ops, and checked STARK/KZG witness-stream channel readers. -/
inductive CompressionOp where
  | field (op : FieldOp)
  | goldilocks (op : GoldilocksOp)
  | blake3 (op : Blake3Op)
  | witness (op : WitnessOp)
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Parse any `@[circuit_intrinsic "..."]` name into a `CompressionOp`. -/
def CompressionOp.ofIntrinsicName? (name : String) : Option CompressionOp :=
  match FieldOp.ofIntrinsicName? name with
  | some op => some (.field op)
  | none =>
    match GoldilocksOp.ofIntrinsicName? name with
    | some op => some (.goldilocks op)
    | none =>
      match Blake3Op.ofIntrinsicName? name with
      | some op => some (.blake3 op)
      | none =>
        (WitnessOp.ofIntrinsicName? name).map .witness

/-- Canonical `@[circuit_intrinsic "..."]` name of a `CompressionOp`. -/
def CompressionOp.intrinsicName : CompressionOp → String
  | .field op => op.intrinsicName
  | .goldilocks op => op.intrinsicName
  | .blake3 op => op.intrinsicName
  | .witness op => op.intrinsicName

/-- Primary operand arity of a `CompressionOp`. -/
def CompressionOp.arity : CompressionOp → Nat
  | .field op => op.arity
  | .goldilocks op => op.arity
  | .blake3 op => op.arity
  | .witness op => op.arity

theorem CompressionOp.ofIntrinsicName_intrinsicName (op : CompressionOp) :
    CompressionOp.ofIntrinsicName? op.intrinsicName = some op := by
  cases op with
  | field fop => cases fop <;> rfl
  | goldilocks gop => cases gop <;> rfl
  | blake3 bop => cases bop <;> rfl
  | witness wop => cases wop <;> rfl

/-! ## Section 2: Emulated Goldilocks No-Wrap Bounds for BN254 `Fr` & BLS12-381 `Fr` -/

/-- No-wrap product bound for emulated Goldilocks multiplication in `BN254 Fr`. -/
theorem bn254_emulated_product_bound :
    (Aiur.Library.Field.Goldilocks.Emulated.modulus - 1) ^ 2 <
      Aiur.Library.Field.BN254.modulus :=
  Aiur.Library.Field.Goldilocks.Emulated.product_bound

/-- No-wrap Euclidean reduction bound for emulated Goldilocks in `BN254 Fr`. -/
theorem bn254_emulated_reduction_bound :
    (2 ^ 64 - 1) * Aiur.Library.Field.Goldilocks.Emulated.modulus +
      (Aiur.Library.Field.Goldilocks.Emulated.modulus - 1) <
      Aiur.Library.Field.BN254.modulus :=
  Aiur.Library.Field.Goldilocks.Emulated.reduction_bound

/-- No-wrap product bound for emulated Goldilocks multiplication in `BLS12-381 Fr`:
`(p_G - 1)^2 < r_{BLS12-381}` so `a * b` never wraps modulo `r_{BLS12-381}`. -/
theorem bls12381_emulated_product_bound :
    (Aiur.Library.Field.Goldilocks.Emulated.modulus - 1) ^ 2 <
      Aiur.Library.Field.BLS12381.modulus := by
  decide

/-- No-wrap Euclidean reduction bound for emulated Goldilocks in `BLS12-381 Fr`:
`(2^64 - 1) * p_G + (p_G - 1) < r_{BLS12-381}` so `q * p_G + r` never wraps. -/
theorem bls12381_emulated_reduction_bound :
    (2 ^ 64 - 1) * Aiur.Library.Field.Goldilocks.Emulated.modulus +
      (Aiur.Library.Field.Goldilocks.Emulated.modulus - 1) <
      Aiur.Library.Field.BLS12381.modulus := by
  decide

/-- Generic no-wrap addition/subtraction bound for canonical Goldilocks residues in
any ambient prime modulus `m > 2 * p_G`. -/
theorem goldilocks_emulated_add_bound (m : Nat)
    (hm : 2 * Aiur.Library.Field.Goldilocks.Emulated.modulus < m)
    {a b : Nat}
    (ha : a < Aiur.Library.Field.Goldilocks.Emulated.modulus)
    (hb : b < Aiur.Library.Field.Goldilocks.Emulated.modulus) :
    a + b < m := by
  omega

/-- Emulated Goldilocks addition/subtraction never wraps in `BN254 Fr`. -/
theorem bn254_emulated_add_bound {a b : Nat}
    (ha : a < Aiur.Library.Field.Goldilocks.Emulated.modulus)
    (hb : b < Aiur.Library.Field.Goldilocks.Emulated.modulus) :
    a + b < Aiur.Library.Field.BN254.modulus :=
  goldilocks_emulated_add_bound Aiur.Library.Field.BN254.modulus (by decide) ha hb

/-- Emulated Goldilocks addition/subtraction never wraps in `BLS12-381 Fr`. -/
theorem bls12381_emulated_add_bound {a b : Nat}
    (ha : a < Aiur.Library.Field.Goldilocks.Emulated.modulus)
    (hb : b < Aiur.Library.Field.Goldilocks.Emulated.modulus) :
    a + b < Aiur.Library.Field.BLS12381.modulus :=
  goldilocks_emulated_add_bound Aiur.Library.Field.BLS12381.modulus (by decide) ha hb

/-! ## Section 3: Compression Intrinsic Lowering Pass (`lowerCompressionOps`) -/

/-- Binding of a lowered `Prog` function `fnName` to a `CompressionOp`.
When `dropFirstParam = true` (used for parametric-modulus `field.*` helpers),
parameter 0 is the ambient prime modulus. -/
structure CompressionBinding where
  fnName : String
  op : CompressionOp
  dropFirstParam : Bool := false
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Configuration for `lowerCompressionOps` and `lowerCompressionProgram`. -/
structure CompressionConfig where
  /-- Explicit intrinsic bindings resolved from `CircuitSchedule`. -/
  bindings : List CompressionBinding := []
  /-- Enable lowering `field.*` bindings (usually handled by `FieldLower`). -/
  enableField : Bool := false
  /-- Enable lowering `goldilocks.*` bindings to `Goldilocks::*`. -/
  enableGoldilocks : Bool := true
  /-- Enable lowering `blake3.*` bindings to `Blake3::*`. -/
  enableBlake3 : Bool := true
  /-- Enable lowering `stark.io.*` / `kzg.io.*` bindings to `StarkIO::*` / `KzgIO::*`. -/
  enableWitnessIO : Bool := true
  /-- Inline direct call sites whose argument count matches `compressionOpExpr`. -/
  inlineOps : Bool := true
  /-- Optional roots for dead-helper pruning via `InlineFuse.pruneUnreachable`. -/
  pruneRoots : Option (List String) := none
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Whether `op` is enabled under `cfg`. -/
def compressionOpEnabled (cfg : CompressionConfig) : CompressionOp → Bool
  | .field _ => cfg.enableField
  | .goldilocks _ => cfg.enableGoldilocks
  | .blake3 _ => cfg.enableBlake3
  | .witness _ => cfg.enableWitnessIO

private def extArrayTy : Lower.Ty := .array .field 3
private def extTupleTy : Lower.Ty := .tuple [.field, .field, .field]

/-- Inline Formal Aiur expression for a `CompressionOp` given operand expressions.
Delegates `.field` to `FieldLower.fieldOpExpr`, and lowers `.goldilocks`, `.blake3`,
and `.witness` to their corresponding certified library calls. -/
def compressionOpExpr : CompressionOp → List Expr → Option Expr
  | .field fop, xs => fieldOpExpr fop xs
  | .goldilocks gop, xs =>
    if xs.length == gop.arity then
      some (callE gop.qualifiedCall xs)
    else
      match gop, xs with
      | .extAdd, [a0, a1, a2, b0, b1, b2]
      | .extSub, [a0, a1, a2, b0, b1, b2]
      | .extMul, [a0, a1, a2, b0, b1, b2] =>
        some (callE gop.qualifiedCall [.array [a0, a1, a2], .array [b0, b1, b2]])
      | .extInv, [a0, a1, a2] =>
        some (callE gop.qualifiedCall [.array [a0, a1, a2]])
      | _, _ => none
  | .blake3 bop, xs =>
    if xs.length == bop.arity then some (callE bop.qualifiedCall xs) else none
  | .witness wop, xs =>
    if xs.length == wop.arity then some (callE wop.qualifiedCall xs) else none

/-- Function-body lowering for a `CompressionOp` given typed parameter declarations
and return type. Supports both native `[Field; 3]` arrays and unpacked 3-tuples /
flat scalar parameters for cubic extension `goldilocks.ext_*` intrinsics. -/
def compressionOpBody (op : CompressionOp) (params : List (String × Lower.Ty))
    (resultTy : Lower.Ty) : Option Expr :=
  match op with
  | .field fop =>
    if resultTy == .field && params.all (fun p => p.2 == .field) then
      fieldOpBody fop (params.map Prod.fst)
    else none
  | .goldilocks gop =>
    if !gop.isExt then
      if params.length == gop.arity && resultTy == .field && params.all (fun p => p.2 == .field) then
        some (callE gop.qualifiedCall (params.map fun p => vE p.1))
      else none
    else
      let callArr := fun (args : List Expr) =>
        let raw := callE gop.qualifiedCall args
        if resultTy == extArrayTy then some raw
        else if resultTy == extTupleTy then
          some (letE "_cg_ext" raw
            (.tuple [.index (vE "_cg_ext") 0, .index (vE "_cg_ext") 1, .index (vE "_cg_ext") 2]))
        else none
      match gop.arity, params with
      | 2, [(a, ta), (b, tb)] =>
        if ta == extArrayTy && tb == extArrayTy then
          callArr [vE a, vE b]
        else if ta == extTupleTy && tb == extTupleTy then
          callArr [
            .array [.project (vE a) 0, .project (vE a) 1, .project (vE a) 2],
            .array [.project (vE b) 0, .project (vE b) 1, .project (vE b) 2]]
        else none
      | 1, [(a, ta)] =>
        if ta == extArrayTy then
          callArr [vE a]
        else if ta == extTupleTy then
          callArr [.array [.project (vE a) 0, .project (vE a) 1, .project (vE a) 2]]
        else none
      | 2, [(a0, .field), (a1, .field), (a2, .field), (b0, .field), (b1, .field), (b2, .field)] =>
        callArr [.array [vE a0, vE a1, vE a2], .array [vE b0, vE b1, vE b2]]
      | 1, [(a0, .field), (a1, .field), (a2, .field)] =>
        callArr [.array [vE a0, vE a1, vE a2]]
      | _, _ => none
  | .blake3 bop =>
    if params.length == bop.arity then
      some (callE bop.qualifiedCall (params.map fun p => vE p.1))
    else none
  | .witness wop =>
    if params.length == wop.arity then
      some (callE wop.qualifiedCall (params.map fun p => vE p.1))
    else none

/-- Local call-site rewriter for bound compression intrinsics.
Only inlines non-ext ops (and direct-arity `[Field; 3]` ext ops) directly at call sites;
tuple-adapting ext wrappers keep their body rewritten and marked `isInline := true` so
Formal Aiur's inliner expands them type-safely. -/
def lowerCompressionCall (bindings : List CompressionBinding) (inlineOps : Bool)
    (nm : String) (targs : Option (List Lower.Ty)) (xs xs' : List Expr) : Expr :=
  if inlineOps && targs == some [] then
    match bindings.find? (·.fnName == nm) with
    | some b =>
      match b.op with
      | .goldilocks gop =>
        if gop.isExt then .call nm targs xs'
        else (compressionOpExpr b.op xs').getD (.call nm targs xs')
      | .field _ =>
        if !b.dropFirstParam then
          (compressionOpExpr b.op xs').getD (.call nm targs xs')
        else
          match xs, xs' with
          | .literal _ :: _, _ :: rest' =>
            (compressionOpExpr b.op rest').getD (.call nm targs xs')
          | _, _ => .call nm targs xs'
      | _ => (compressionOpExpr b.op xs').getD (.call nm targs xs')
    | none => .call nm targs xs'
  else .call nm targs xs'

mutual

/-- Strictly structural bottom-up compression-intrinsic expression rewriter. -/
def lowerCompressionExpr (bindings : List CompressionBinding) (inlineOps : Bool) : Expr → Expr
  | .call nm targs xs =>
    let xs' := lowerCompressionExprList bindings inlineOps xs
    lowerCompressionCall bindings inlineOps nm targs xs xs'
  | .tuple xs => .tuple (lowerCompressionExprList bindings inlineOps xs)
  | .array xs => .array (lowerCompressionExprList bindings inlineOps xs)
  | .construct ty targs nm xs =>
    .construct ty targs nm (lowerCompressionExprList bindings inlineOps xs)
  | .constructAs ty targs nm xs =>
    .constructAs ty targs nm (lowerCompressionExprList bindings inlineOps xs)
  | .record ty fs => .record ty (lowerCompressionExprList bindings inlineOps fs)
  | .update ty fs => .update ty (lowerCompressionExprList bindings inlineOps fs)
  | .builtin op xs => .builtin op (lowerCompressionExprList bindings inlineOps xs)
  | .repeat x n => .repeat (lowerCompressionExpr bindings inlineOps x) n
  | .index x i => .index (lowerCompressionExpr bindings inlineOps x) i
  | .slice x a b => .slice (lowerCompressionExpr bindings inlineOps x) a b
  | .member x f => .member (lowerCompressionExpr bindings inlineOps x) f
  | .project x i => .project (lowerCompressionExpr bindings inlineOps x) i
  | .store x => .store (lowerCompressionExpr bindings inlineOps x)
  | .load x => .load (lowerCompressionExpr bindings inlineOps x)
  | .hint ty x ch => .hint ty (lowerCompressionExpr bindings inlineOps x) ch
  | .neg x => .neg (lowerCompressionExpr bindings inlineOps x)
  | .binary op x y =>
    .binary op (lowerCompressionExpr bindings inlineOps x)
      (lowerCompressionExpr bindings inlineOps y)
  | .letValue p x b =>
    .letValue p (lowerCompressionExpr bindings inlineOps x)
      (lowerCompressionExpr bindings inlineOps b)
  | .matchValue s arms =>
    .matchValue (lowerCompressionExpr bindings inlineOps s)
      (lowerCompressionArms bindings inlineOps arms)
  | .literal n => .literal n
  | .var x => .var x
  | .global nm targs => .global nm targs
  | .control c e => .control c e

def lowerCompressionExprList (bindings : List CompressionBinding) (inlineOps : Bool) :
    List Expr → List Expr
  | [] => []
  | x :: xs =>
    lowerCompressionExpr bindings inlineOps x :: lowerCompressionExprList bindings inlineOps xs

def lowerCompressionArms (bindings : List CompressionBinding) (inlineOps : Bool) :
    List (Pat × Expr) → List (Pat × Expr)
  | [] => []
  | (p, b) :: rest =>
    (p, lowerCompressionExpr bindings inlineOps b) :: lowerCompressionArms bindings inlineOps rest

end

/-- Lower a single `Lower.Fn`: if `f` is bound to an enabled `CompressionOp` with a
matching typed signature, replace its body with the library intrinsic call (marking
`isInline := true`); otherwise rewrite its body via `lowerCompressionExpr`. -/
def lowerCompressionFn (bindings : List CompressionBinding) (inlineOps : Bool) (f : Fn) : Fn :=
  match bindings.find? (·.fnName == f.name) with
  | some b =>
    if f.typeParams.isEmpty then
      let opParams := if b.dropFirstParam then f.params.drop 1 else f.params
      match compressionOpBody b.op opParams f.result with
      | some body' => { f with body := body', isInline := true }
      | none => { f with body := lowerCompressionExpr bindings inlineOps f.body }
    else
      { f with body := lowerCompressionExpr bindings inlineOps f.body }
  | none =>
    { f with body := lowerCompressionExpr bindings inlineOps f.body }

/-- Core compression-intrinsic lowering pass on a list of `Lower.Fn`s (before pruning). -/
def lowerCompressionOpsCore (cfg : CompressionConfig) (fns : List Fn) : List Fn :=
  let active := cfg.bindings.filter (fun b => compressionOpEnabled cfg b.op)
  if active.isEmpty then fns
  else fns.map (lowerCompressionFn active cfg.inlineOps)

/-- Full compression-intrinsic lowering pass (with optional `pruneUnreachable`). -/
def lowerCompressionOps (cfg : CompressionConfig) (fns : List Fn) : List Fn :=
  let lowered := lowerCompressionOpsCore cfg fns
  match cfg.pruneRoots with
  | some roots => pruneUnreachable roots lowered
  | none => lowered

/-- Apply `lowerCompressionOps` to a `TypedLower.LoweredProgram` and recompute its
minimal `TableTier`. -/
def lowerCompressionProgram (cfg : CompressionConfig) (lp : LoweredProgram) : LoweredProgram :=
  let fns' := lowerCompressionOps cfg lp.program.functions
  let tier' := FieldLower.computeTier fns'
  { lp with
    program := { lp.program with functions := fns' }
    tier := tier' }

private def gkeySourceCId? : IxCC.Key.GKey → Option IxCC.Src.CId
  | .const c _ | .byName c _ => some c
  | .spec g _ | .worker g _ | .entry g _ => gkeySourceCId? g
  | .recStar _ _ | .wrapper _ _ | .lam _ _ | .dispatch _ => none

private def funAddress? (src : IxCC.Src.Program) (fd : IxCC.Fir.Fun) :
    Option IxCC.Ixon.Address :=
  (gkeySourceCId? fd.key).bind fun cid => (src.entry? cid).map (·.addr)

/-- Resolve all `@[circuit_intrinsic "..."]` directives from a resolved
`Schedule.CircuitSchedule` (`byFun` / `byAddress`) into concrete `CompressionBinding`s
against the lowered `Prog` functions `fns`. -/
def resolveCompressionBindings (src : IxCC.Src.Program) (P : IxCC.Fir.Program)
    (resolvedSched : Schedule.CircuitSchedule) (fns : List Fn) : List CompressionBinding :=
  P.funList.filterMap fun (fid, fd) => do
    let fs := resolvedSched.forFun fid (funAddress? src fd)
    let intrName ← fs.intrinsic
    let op ← CompressionOp.ofIntrinsicName? intrName
    let nm := funName fid
    let fnDef ← fns.find? (·.name == nm)
    if !fnDef.typeParams.isEmpty then none
    else
      match op with
      | .field fop =>
        if !allFieldParams fnDef then none
        else if fnDef.params.length == fop.arity then
          some { fnName := nm, op, dropFirstParam := false }
        else if fnDef.params.length == fop.arity + 1 then
          some { fnName := nm, op, dropFirstParam := true }
        else none
      | _ =>
        if (compressionOpBody op fnDef.params fnDef.result).isSome then
          some { fnName := nm, op, dropFirstParam := false }
        else none

/-! ## Section 4: Plainness Preservation Theorems (`Lower.isPlainExpr = true`, Zero `sorry`) -/

private theorem isPlainList_vars (ns : List String) :
    isPlainList (ns.map vE) = true := by
  induction ns with
  | nil => rfl
  | cons _ rest ih => simp only [List.map, isPlainList, Bool.and_eq_true]; exact ⟨rfl, ih⟩

private theorem isPlainList_paramVars (ps : List (String × Lower.Ty)) :
    isPlainList (ps.map fun p => vE p.1) = true := by
  induction ps with
  | nil => rfl
  | cons _ rest ih => simp only [List.map, isPlainList, Bool.and_eq_true]; exact ⟨rfl, ih⟩

/-- Every expression produced by `compressionOpExpr` is plain (`isPlainExpr = true`)
whenever its operand expressions are plain. -/
theorem compressionOp_plain {op : CompressionOp} {xs : List Expr} {e : Expr}
    (h : compressionOpExpr op xs = some e) (hxs : isPlainList xs = true) :
    isPlainExpr e = true := by
  cases op with
  | field fop =>
    exact isPlainExpr_fieldOpExpr h hxs
  | goldilocks gop =>
    simp only [compressionOpExpr] at h
    split at h
    · injection h with h; subst h
      simp [callE, isPlainExpr, hxs]
    · cases gop <;>
        rcases xs with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | _⟩⟩⟩⟩⟩⟩ <;>
        simp only [Option.some.injEq, reduceCtorEq] at h
      all_goals subst h
      all_goals simp only [isPlainList, Bool.and_true, Bool.and_eq_true] at hxs
      all_goals simp [callE, isPlainExpr, isPlainList, hxs]
  | blake3 bop =>
    simp only [compressionOpExpr] at h
    split at h
    · injection h with h; subst h
      simp [callE, isPlainExpr, hxs]
    · cases h
  | witness wop =>
    simp only [compressionOpExpr] at h
    split at h
    · injection h with h; subst h
      simp [callE, isPlainExpr, hxs]
    · cases h

private theorem isPlainExpr_extCallWrap (qname : String) (resultTy : Lower.Ty)
    {args : List Expr} (hargs : isPlainList args = true) {e : Expr}
    (h : (if resultTy == extArrayTy then some (callE qname args)
          else if resultTy == extTupleTy then
            some (letE "_cg_ext" (callE qname args)
              (.tuple [.index (vE "_cg_ext") 0, .index (vE "_cg_ext") 1, .index (vE "_cg_ext") 2]))
          else none) = some e) :
    isPlainExpr e = true := by
  split at h
  · injection h with h; subst h
    simp [callE, isPlainExpr, hargs]
  · split at h
    · injection h with h; subst h
      simp [letE, callE, vE, isPlainExpr, isPlainList, hargs]
    · cases h

/-- Every function body produced by `compressionOpBody` is plain (`isPlainExpr = true`). -/
theorem compressionOpBody_plain {op : CompressionOp} {params : List (String × Lower.Ty)}
    {resultTy : Lower.Ty} {e : Expr}
    (h : compressionOpBody op params resultTy = some e) :
    isPlainExpr e = true := by
  cases op with
  | field fop =>
    simp only [compressionOpBody] at h
    split at h
    · exact isPlainExpr_fieldOpBody h
    · cases h
  | goldilocks gop =>
    simp only [compressionOpBody] at h
    split at h
    · split at h
      · injection h with h; subst h
        simp [callE, isPlainExpr, isPlainList_paramVars]
      · cases h
    · split at h
      · split at h
        · exact isPlainExpr_extCallWrap _ _ (by simp [isPlainList, vE, isPlainExpr]) h
        · split at h
          · exact isPlainExpr_extCallWrap _ _ (by simp [isPlainList, vE, isPlainExpr]) h
          · cases h
      · split at h
        · exact isPlainExpr_extCallWrap _ _ (by simp [isPlainList, vE, isPlainExpr]) h
        · split at h
          · exact isPlainExpr_extCallWrap _ _ (by simp [isPlainList, vE, isPlainExpr]) h
          · cases h
      · exact isPlainExpr_extCallWrap _ _ (by simp [isPlainList, vE, isPlainExpr]) h
      · exact isPlainExpr_extCallWrap _ _ (by simp [isPlainList, vE, isPlainExpr]) h
      · cases h
  | blake3 bop =>
    simp only [compressionOpBody] at h
    split at h
    · injection h with h; subst h
      simp [callE, isPlainExpr, isPlainList_paramVars]
    · cases h
  | witness wop =>
    simp only [compressionOpBody] at h
    split at h
    · injection h with h; subst h
      simp [callE, isPlainExpr, isPlainList_paramVars]
    · cases h

theorem isPlainExpr_lowerCompressionCall (bindings : List CompressionBinding) (inlineOps : Bool)
    (nm : String) (targs : Option (List Lower.Ty)) (xs : List Expr) {xs' : List Expr}
    (hxs : isPlainList xs' = true) :
    isPlainExpr (lowerCompressionCall bindings inlineOps nm targs xs xs') = true := by
  unfold lowerCompressionCall
  split
  · split
    · next b _ =>
      cases hop : b.op with
      | goldilocks gop =>
        dsimp only
        split
        · simp [isPlainExpr, hxs]
        · cases he : compressionOpExpr (.goldilocks gop) xs' with
          | none => simp [Option.getD, isPlainExpr, hxs]
          | some e => exact compressionOp_plain he hxs
      | field fop =>
        dsimp only
        split
        · cases he : compressionOpExpr (.field fop) xs' with
          | none => simp [Option.getD, isPlainExpr, hxs]
          | some e => exact compressionOp_plain he hxs
        · split
          · next _ _ hd' rest' =>
            simp only [isPlainList, Bool.and_eq_true] at hxs
            cases he : compressionOpExpr (.field fop) rest' with
            | none => simp [Option.getD, isPlainExpr, isPlainList, hxs.1, hxs.2]
            | some e => exact compressionOp_plain he hxs.2
          · simp [isPlainExpr, hxs]
      | blake3 bop =>
        dsimp only
        cases he : compressionOpExpr (.blake3 bop) xs' with
        | none => simp [Option.getD, isPlainExpr, hxs]
        | some e => exact compressionOp_plain he hxs
      | witness wop =>
        dsimp only
        cases he : compressionOpExpr (.witness wop) xs' with
        | none => simp [Option.getD, isPlainExpr, hxs]
        | some e => exact compressionOp_plain he hxs
    · simp [isPlainExpr, hxs]
  · simp [isPlainExpr, hxs]

mutual

/-- `lowerCompressionExpr` preserves `Lower.isPlainExpr = true` on every expression. -/
theorem lowerCompressionExpr_plain (bindings : List CompressionBinding) (inlineOps : Bool) :
    ∀ (e : Expr), isPlainExpr e = true →
      isPlainExpr (lowerCompressionExpr bindings inlineOps e) = true
  | .call nm targs xs, h =>
    isPlainExpr_lowerCompressionCall bindings inlineOps nm targs xs
      (lowerCompressionExprList_plain bindings inlineOps xs h)
  | .tuple xs, h | .array xs, h | .construct _ _ _ xs, h | .constructAs _ _ _ xs, h
  | .record _ xs, h | .update _ xs, h | .builtin _ xs, h =>
    lowerCompressionExprList_plain bindings inlineOps xs h
  | .repeat x _, h | .index x _, h | .slice x _ _, h | .member x _, h
  | .project x _, h | .store x, h | .load x, h | .hint _ x _, h | .neg x, h =>
    lowerCompressionExpr_plain bindings inlineOps x h
  | .binary _ x y, h | .letValue _ x y, h => by
    simp only [isPlainExpr, Bool.and_eq_true] at h
    simp only [lowerCompressionExpr, isPlainExpr,
      lowerCompressionExpr_plain bindings inlineOps x h.1,
      lowerCompressionExpr_plain bindings inlineOps y h.2,
      Bool.and_self]
  | .matchValue s arms, h => by
    simp only [isPlainExpr, Bool.and_eq_true] at h
    simp only [lowerCompressionExpr, isPlainExpr,
      lowerCompressionExpr_plain bindings inlineOps s h.1,
      lowerCompressionArms_plain bindings inlineOps arms h.2,
      Bool.and_self]
  | .literal _, _ | .var _, _ => rfl
  | .global _ _, h | .control _ _, h => by simp [isPlainExpr] at h

theorem lowerCompressionExprList_plain (bindings : List CompressionBinding) (inlineOps : Bool) :
    ∀ (xs : List Expr), isPlainList xs = true →
      isPlainList (lowerCompressionExprList bindings inlineOps xs) = true
  | [], _ => rfl
  | x :: xs, h => by
    simp only [isPlainList, Bool.and_eq_true] at h
    simp only [lowerCompressionExprList, isPlainList,
      lowerCompressionExpr_plain bindings inlineOps x h.1,
      lowerCompressionExprList_plain bindings inlineOps xs h.2,
      Bool.and_self]

theorem lowerCompressionArms_plain (bindings : List CompressionBinding) (inlineOps : Bool) :
    ∀ (arms : List (Pat × Expr)), isPlainArms arms = true →
      isPlainArms (lowerCompressionArms bindings inlineOps arms) = true
  | [], _ => rfl
  | (_, b) :: rest, h => by
    simp only [isPlainArms, Bool.and_eq_true] at h
    simp only [lowerCompressionArms, isPlainArms,
      lowerCompressionExpr_plain bindings inlineOps b h.1,
      lowerCompressionArms_plain bindings inlineOps rest h.2,
      Bool.and_self]

end

/-- `lowerCompressionFn` preserves `Lower.isPlainExpr = true`. -/
theorem lowerCompressionFn_plain (bindings : List CompressionBinding) (inlineOps : Bool) {f : Fn}
    (hf : isPlainExpr f.body = true) :
    isPlainExpr (lowerCompressionFn bindings inlineOps f).body = true := by
  unfold lowerCompressionFn
  cases bindings.find? (·.fnName == f.name) with
  | none => exact lowerCompressionExpr_plain bindings inlineOps f.body hf
  | some b =>
    dsimp only
    by_cases htp : f.typeParams.isEmpty = true
    · simp only [htp, ↓reduceIte]
      cases hbody : compressionOpBody b.op (if b.dropFirstParam then f.params.drop 1 else f.params) f.result with
      | some body' => exact compressionOpBody_plain hbody
      | none => exact lowerCompressionExpr_plain bindings inlineOps f.body hf
    · simp only [htp]
      exact lowerCompressionExpr_plain bindings inlineOps f.body hf

/-- `lowerCompressionOps` (including optional `pruneUnreachable`) preserves
`Lower.isPlainExpr = true` on every surviving function body. -/
theorem lowerCompressionOps_plain (cfg : CompressionConfig) {fns : List Fn}
    (hfns : ∀ f ∈ fns, isPlainExpr f.body = true) :
    ∀ f ∈ lowerCompressionOps cfg fns, isPlainExpr f.body = true := by
  have hcore : ∀ f ∈ lowerCompressionOpsCore cfg fns, isPlainExpr f.body = true := by
    intro f hf
    unfold lowerCompressionOpsCore at hf
    dsimp only at hf
    split at hf
    · exact hfns f hf
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      exact lowerCompressionFn_plain _ _ (hfns g hg)
  unfold lowerCompressionOps
  split
  · intro f hf
    unfold pruneUnreachable at hf
    exact hcore f (List.mem_filter.mp hf).1
  · exact hcore

/-! ## Section 5: Custom Entry-Point Aliasing (`aliasEntry`, `--entry-name`, `--assert-ok`) -/

/-- Reserved module and signature names owned by the linked Formal Aiur standard
and compression libraries. Custom `--entry-name` modules may not collide with these. -/
def reservedLibraryNames : List String :=
  ["UInt8", "U8Signature", "UInt32", "U32Signature", "UInt64",
   "Lists", "Fields", "Bytes", "Blake3",
   "Goldilocks", "GoldilocksSignature", "U8Byte",
   "StarkIO", "KzgIO"]

/-- Parsed qualified entry-point name `modName::fnName`. -/
structure ParsedEntryName where
  modName : String
  fnName : String
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Qualified string `modName::fnName`. -/
def ParsedEntryName.qualified (p : ParsedEntryName) : String :=
  p.modName ++ "::" ++ p.fnName

/-- Parse and validate a custom `--entry-name "Module::fn_name"` (e.g.
`"CompressWrap::verify_root"`, `"CompressGL::verify_root"`,
`"CompressNarrowFixed::step_v1"`, `"CompressFinalNarrow::verify_accumulator_v1"`). -/
def parseEntryName (raw : String) : Except String ParsedEntryName := do
  match raw.splitOn "::" with
  | [modName, fnName] =>
    unless Aiur.Modules.simpleIdentifier modName do
      throw s!"invalid --entry-name module '{modName}' in '{raw}' (must be a valid Aiur identifier)"
    unless Aiur.Modules.simpleIdentifier fnName do
      throw s!"invalid --entry-name function '{fnName}' in '{raw}' (must be a valid Aiur identifier)"
    if reservedLibraryNames.contains modName then
      throw s!"--entry-name module '{modName}' collides with a reserved Aiur library module/signature"
    return { modName, fnName }
  | _ =>
    throw s!"invalid --entry-name '{raw}' (expected 'Module::fn_name')"

mutual

/-- Qualify unqualified local `Prog` nominal types (`Obj`, `D<id>`, `E<id>`) with
`"Prog::"` so they are valid in an external alias module (e.g. `CompressWrap`). -/
def qualifyProgTy : Lower.Ty → Lower.Ty
  | .named nm args =>
    let nm' := if hasDoubleColon nm.toList then nm else qualified nm
    .named nm' (qualifyProgTyList args)
  | .tuple ts => .tuple (qualifyProgTyList ts)
  | .array t n => .array (qualifyProgTy t) n
  | .ptr t => .ptr (qualifyProgTy t)
  | t => t

def qualifyProgTyList : List Lower.Ty → List Lower.Ty
  | [] => []
  | t :: ts => qualifyProgTy t :: qualifyProgTyList ts

end

/-- Standard assertion descriptor used by `--assert-ok` entry wrappers. -/
def assertOkAssertion : Aiur.Assertion :=
  { message := some "verifier returned non-1" }

/-- Body of an aliased entry function calling `targetQName` with `paramNames`:
* `assertOk = false`: direct passthrough `targetQName(p0, ..., pk)`
* `assertOk = true`: unit-returning assertion `assert_eq!(targetQName(p0, ..., pk), 1)` -/
def aliasEntryBody (targetQName : String) (paramNames : List String) (assertOk : Bool) : Expr :=
  let callTarget := callE targetQName (paramNames.map vE)
  if assertOk then
    .builtin (.assertEq assertOkAssertion) [callTarget, litE 1]
  else
    callTarget

/-- `aliasEntryBody` is always plain (`isPlainExpr = true`). -/
theorem isPlainExpr_aliasEntryBody (targetQName : String) (paramNames : List String)
    (assertOk : Bool) :
    isPlainExpr (aliasEntryBody targetQName paramNames assertOk) = true := by
  unfold aliasEntryBody
  cases assertOk <;> simp [callE, litE, isPlainExpr, isPlainList, isPlainList_vars]

/-- Complete specification of a custom entry-point alias emitted by `aliasEntry`. -/
structure AliasSpec where
  /-- Final exported entry name (e.g. `"CompressWrap::verify_root"` or `"Prog::main0"`). -/
  entry : String
  /-- Module owning `entry`. -/
  modName : String
  /-- Unqualified function name inside `modName`. -/
  fnName : String
  /-- Underlying lowered `Prog` entry (always `"Prog::main<i>"`). -/
  targetEntry : String
  /-- Parameter names of the aliased entry (distinct, matching `Prog::main<i>`). -/
  paramNames : List String
  /-- Whether `--assert-ok` wraps the return value with `assert_eq!(res, 1) -> ()`. -/
  assertOk : Bool
  /-- Whether an alias wrapper function was actually emitted (false for identity `Prog::main<i>`). -/
  hasWrapper : Bool
  /-- Possibly updated `Prog` module (unchanged whenever `modName ≠ "Prog"`). -/
  prog : Aiur.Generic.Program Nat
  /-- External wrapper module (e.g. `module CompressWrap { fn verify_root ... }`), if `modName ≠ "Prog"`. -/
  extraModule? : Option (Aiur.Modules.Module Nat)
  deriving Repr

/-- Emit a thin wrapper module/entry exporting `Prog::main<entryIdx>` under an optional
custom qualified name `--entry-name "Module::fn_name"` and optional `--assert-ok`
(`assert_eq!(result, 1) -> ()`) unit-returning ABI adapter.
* Keeps `Prog::main<entryIdx>` completely intact so `World.checkFunctions` and
  `aliasEntry_sound` hold without modifying any existing proof obligation.
* When `entryName? = none` and `assertOk = false`, returns the identity spec for
  `Prog::main<entryIdx>` with `extraModule? = none`.
* When `entryName? = none` and `assertOk = true`, emits a wrapper in module `"Verify"`
  (`"Verify::main<entryIdx>"`). -/
def aliasEntry (prog : Aiur.Generic.Program Nat) (entryIdx : Nat := 0)
    (entryName? : Option String := none) (assertOk : Bool := false) :
    Except String AliasSpec := do
  let targetLocal := entryName entryIdx
  let targetQ := qualified targetLocal
  let some origFn := prog.functions.find? (·.name == targetLocal)
    | throw s!"aliasEntry: missing entry function '{targetQ}'"
  unless origFn.typeParams.isEmpty do
    throw s!"aliasEntry: entry '{targetQ}' must be monomorphic"
  let paramNames := origFn.params.map Prod.fst
  unless allDistinct paramNames do
    throw s!"aliasEntry: entry '{targetQ}' has duplicate parameter names"
  if assertOk && origFn.result != .field then
    throw s!"aliasEntry: --assert-ok requires '{targetQ}' to return Field (e.g. unboxed Nat 1/0), got {reprStr origFn.result}"
  match entryName?, assertOk with
  | none, false =>
    return {
      entry := targetQ
      modName := moduleName
      fnName := targetLocal
      targetEntry := targetQ
      paramNames
      assertOk := false
      hasWrapper := false
      prog
      extraModule? := none
    }
  | _, _ =>
    let parsed : ParsedEntryName ← match entryName? with
      | some raw => parseEntryName raw
      | none => pure { modName := "Verify", fnName := targetLocal }
    if parsed.modName == moduleName then
      if parsed.fnName == targetLocal then
        if assertOk then
          throw s!"aliasEntry: --assert-ok cannot overwrite '{targetQ}' in place; pass a distinct --entry-name (e.g. CompressWrap::verify_root)"
        else
          return {
            entry := targetQ
            modName := moduleName
            fnName := targetLocal
            targetEntry := targetQ
            paramNames
            assertOk := false
            hasWrapper := false
            prog
            extraModule? := none
          }
      else
        if (Aiur.Modules.memberNames prog).contains parsed.fnName then
          throw s!"aliasEntry: '{parsed.qualified}' collides with an existing member of '{moduleName}'"
        let wrapperFn : Fn := {
          name := parsed.fnName
          typeParams := []
          params := origFn.params
          result := if assertOk then .tuple [] else origFn.result
          body := aliasEntryBody targetLocal paramNames assertOk
          isInline := false
        }
        let prog' : Aiur.Generic.Program Nat :=
          { prog with functions := prog.functions ++ [wrapperFn] }
        return {
          entry := parsed.qualified
          modName := parsed.modName
          fnName := parsed.fnName
          targetEntry := targetQ
          paramNames
          assertOk
          hasWrapper := true
          prog := prog'
          extraModule? := none
        }
    else
      let qualifiedParams := origFn.params.map fun (n, t) => (n, qualifyProgTy t)
      let qualifiedResult := if assertOk then .tuple [] else qualifyProgTy origFn.result
      let wrapperFn : Fn := {
        name := parsed.fnName
        typeParams := []
        params := qualifiedParams
        result := qualifiedResult
        body := aliasEntryBody targetQ paramNames assertOk
        isInline := false
      }
      let wrapperMod : Aiur.Modules.Module Nat := {
        name := parsed.modName
        body := .definitions { program := { functions := [wrapperFn] } }
      }
      return {
        entry := parsed.qualified
        modName := parsed.modName
        fnName := parsed.fnName
        targetEntry := targetQ
        paramNames
        assertOk
        hasWrapper := true
        prog
        extraModule? := some wrapperMod
      }

/-- Executable check verifying that the elaborated `Generic.Source F` contains the
aliased entry function matching `spec` (non-instantiated symbol, no type params,
matching distinct parameter names, and exact `aliasEntryBody` calling `spec.targetEntry`). -/
def checkAliasEntry {F : Type} [Field F] [DecidableEq F]
    (s : Aiur.Generic.Source F) (spec : AliasSpec) : Bool :=
  if !spec.hasWrapper then true
  else
    decide (spec.entry.toList.head? ≠ some '$') &&
    allDistinct spec.paramNames &&
    match s.program.findFunction? spec.entry with
    | some f =>
      f.typeParams.isEmpty &&
      (f.params.map Prod.fst == spec.paramNames) &&
      (f.body == (aliasEntryBody spec.targetEntry spec.paramNames spec.assertOk).map (Nat.cast : Nat → F))
    | none => false

/-! ### Certified Backward & Forward Soundness of `aliasEntry` (Zero `sorry`) -/

section AliasSoundness

variable {F : Type} [Field F] [DecidableEq F]

private theorem find_zip_of_nodup {α β : Type} [DecidableEq α]
    {ks : List α} {vs : List β} (hnodup : ks.Nodup) (hlen : ks.length = vs.length)
    {k : α} {v : β} (hmem : (k, v) ∈ ks.zip vs) :
    (ks.zip vs).find? (·.1 == k) = some (k, v) := by
  induction ks generalizing vs with
  | nil => simp at hmem
  | cons a ks ih =>
    cases vs with
    | nil => simp at hlen
    | cons b vs =>
      simp only [List.nodup_cons] at hnodup
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [List.zip_cons_cons, List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · injection hhead with hka hvb
        subst hka; subst hvb
        simp
      · have hkMem : k ∈ ks := (List.of_mem_zip htail).1
        have hne : a ≠ k := fun heq => hnodup.1 (heq ▸ hkMem)
        have hbeq : (a == k) = false := beq_false_of_ne hne
        simp only [List.zip_cons_cons, List.find?_cons, hbeq]
        exact ih hnodup.2 hlen htail

private theorem evalArgs_vars_of_zip_suffix
    {world : World F} {locals : Environment F Nat}
    {ks : List String} {vs : List (SourceValue F)}
    (hlookup : ∀ k v, (k, v) ∈ ks.zip vs → locals.find? (·.1 == k) = some (k, v))
    (hlen : ks.length = vs.length) {h : Heap F} :
    ∀ {vals : List (SourceValue F)} {h' : Heap F},
      EvalArgs world [] locals (ks.map fun n => (Expr.var n : Aiur.Generic.Expr F)) h vals h' →
      vals = vs ∧ h' = h := by
  induction ks generalizing vs h with
  | nil =>
    cases vs with
    | nil =>
      intro vals h' ev
      cases ev
      exact ⟨rfl, rfl⟩
    | cons _ _ => simp at hlen
  | cons k ks ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      intro vals h' ev
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      cases ev with
      | cons evHead evTail =>
        obtain ⟨hlk, rfl⟩ := evalExpr_var_inv evHead
        have hkv : locals.find? (·.1 == k) = some (k, v) :=
          hlookup k v (by simp [List.zip_cons_cons])
        rw [hkv] at hlk
        injection hlk with hpair
        injection hpair with _ hvEq
        subst hvEq
        have hlookupTail : ∀ k' v', (k', v') ∈ ks.zip vs → locals.find? (·.1 == k') = some (k', v') :=
          fun k' v' hmem => hlookup k' v' (by simp [List.zip_cons_cons, hmem])
        obtain ⟨rfl, rfl⟩ := ih hlookupTail hlen evTail
        exact ⟨rfl, rfl⟩

private theorem evalArgs_vars_of_zip_fwd
    {world : World F} {locals : Environment F Nat}
    {ks : List String} {vs : List (SourceValue F)}
    (hlookup : ∀ k v, (k, v) ∈ ks.zip vs → locals.find? (·.1 == k) = some (k, v))
    (hlen : ks.length = vs.length) (h : Heap F) :
    EvalArgs world [] locals (ks.map fun n => (Expr.var n : Aiur.Generic.Expr F)) h vs h := by
  induction ks generalizing vs with
  | nil =>
    cases vs with
    | nil => exact .nil
    | cons _ _ => simp at hlen
  | cons k ks ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      have hkv : locals.find? (·.1 == k) = some (k, v) :=
        hlookup k v (by simp [List.zip_cons_cons])
      have hlookupTail : ∀ k' v', (k', v') ∈ ks.zip vs → locals.find? (·.1 == k') = some (k', v') :=
        fun k' v' hmem => hlookup k' v' (by simp [List.zip_cons_cons, hmem])
      exact .cons (.var hkv) (ih hlookupTail hlen)

omit [DecidableEq F] in
private theorem map_vE_cast (paramNames : List String) :
    (paramNames.map vE).map (Aiur.Generic.Expr.map (Nat.cast : Nat → F)) =
      paramNames.map (fun n => (Aiur.Generic.Expr.var n : Aiur.Generic.Expr F)) := by
  induction paramNames with
  | nil => rfl
  | cons _ rest ih => simp [vE, Aiur.Generic.Expr.map, ih]

/-- **Backward soundness of passthrough `aliasEntry` (`assertOk = false`)**:
when `paramNames.Nodup`, any derivation of the aliased entry on `vs` gives a derivation
of `Prog::main<i>` on the exact same `vs`, with `vs.length = paramNames.length`. -/
theorem aliasEntry_passthrough_sound
    {world : World F} {aliasQName targetQName : String}
    {paramNames : List String}
    (hDistinct : paramNames.Nodup)
    (hFn : WorldHasFn world aliasQName paramNames
      ((aliasEntryBody targetQName paramNames false).map (Nat.cast : Nat → F)))
    {vs : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (evAlias : EvalFn world aliasQName vs h r h') :
    vs.length = paramNames.length ∧ EvalFn world targetQName vs h r h' := by
  have hPlain : isPlainExpr ((aliasEntryBody targetQName paramNames false).map (Nat.cast : Nat → F)) = true := by
    rw [isPlainExpr_map]; exact isPlainExpr_aliasEntryBody targetQName paramNames false
  obtain ⟨hlen, evBody⟩ := evalFn_plain_inv hFn hPlain evAlias
  simp only [aliasEntryBody, Bool.false_eq_true, ↓reduceIte, callE, Aiur.Generic.Expr.map] at evBody
  cases evBody with
  | call evArgs evCallee =>
    rw [map_vE_cast] at evArgs
    have hlookup : ∀ k v, (k, v) ∈ paramNames.zip vs → (paramNames.zip vs).find? (·.1 == k) = some (k, v) :=
      fun _ _ hmem => find_zip_of_nodup hDistinct hlen.symm hmem
    obtain ⟨rfl, rfl⟩ := evalArgs_vars_of_zip_suffix hlookup hlen.symm evArgs
    have hInst : instanceName [] targetQName (some []) = targetQName := by
      simp [instanceName, Instance.symbol]
    rw [hInst] at evCallee
    exact ⟨hlen, evCallee⟩

/-- **Forward completeness of passthrough `aliasEntry` (`assertOk = false`)**. -/
theorem aliasEntry_passthrough_complete
    {world : World F} {aliasQName targetQName : String}
    {paramNames : List String} {vs : List (SourceValue F)}
    (hDistinct : paramNames.Nodup)
    (hlen : vs.length = paramNames.length)
    (hPrep : world.prepare aliasQName vs = .ok ([], paramNames.zip vs,
      ((aliasEntryBody targetQName paramNames false).map (Nat.cast : Nat → F))))
    {h h' : Heap F} {r : SourceValue F}
    (evTarget : EvalFn world targetQName vs h r h') :
    EvalFn world aliasQName vs h r h' := by
  have hlookup : ∀ k v, (k, v) ∈ paramNames.zip vs → (paramNames.zip vs).find? (·.1 == k) = some (k, v) :=
    fun _ _ hmem => find_zip_of_nodup hDistinct hlen.symm hmem
  have evArgs : EvalArgs world [] (paramNames.zip vs)
      ((paramNames.map vE).map (Aiur.Generic.Expr.map (Nat.cast : Nat → F))) h vs h := by
    rw [map_vE_cast]
    exact evalArgs_vars_of_zip_fwd hlookup hlen.symm h
  have hInst : instanceName [] targetQName (some []) = targetQName := by
    simp [instanceName, Instance.symbol]
  have evBody : EvalExpr world [] (paramNames.zip vs)
      ((aliasEntryBody targetQName paramNames false).map (Nat.cast : Nat → F)) h r h' := by
    simp only [aliasEntryBody, Bool.false_eq_true, ↓reduceIte, callE, Aiur.Generic.Expr.map]
    exact .call evArgs (by rwa [hInst])
  exact .intro hPrep evBody

/-- **Backward soundness of `--assert-ok` `aliasEntry` (`assertOk = true`)**:
any derivation of the asserting wrapper entry on `vs` produces `r = .tuple []` (unit)
and implies a derivation of `Prog::main<i>` returning `.field 1` with final heap `h'`. -/
theorem aliasEntry_assertOk_sound
    {world : World F} {aliasQName targetQName : String}
    {paramNames : List String}
    (hDistinct : paramNames.Nodup)
    (hFn : WorldHasFn world aliasQName paramNames
      ((aliasEntryBody targetQName paramNames true).map (Nat.cast : Nat → F)))
    {vs : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (evAlias : EvalFn world aliasQName vs h r h') :
    vs.length = paramNames.length ∧ r = .tuple [] ∧ EvalFn world targetQName vs h (.field 1) h' := by
  have hPlain : isPlainExpr ((aliasEntryBody targetQName paramNames true).map (Nat.cast : Nat → F)) = true := by
    rw [isPlainExpr_map]; exact isPlainExpr_aliasEntryBody targetQName paramNames true
  obtain ⟨hlen, evBody⟩ := evalFn_plain_inv hFn hPlain evAlias
  simp only [aliasEntryBody, ↓reduceIte, callE, litE, Aiur.Generic.Expr.map, List.map, Nat.cast_one] at evBody
  cases evBody with
  | builtin evItems hApp =>
    cases evItems with
    | cons evCall evRest =>
      cases evRest with
      | cons evOne evNil =>
        cases evNil
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evOne
        simp only [Builtin.apply] at hApp
        obtain ⟨_, rfl, rfl⟩ := evalAssertEq_ok.mp hApp
        cases evCall with
        | call evArgs evCallee =>
          rw [map_vE_cast] at evArgs
          have hlookup : ∀ k v, (k, v) ∈ paramNames.zip vs → (paramNames.zip vs).find? (·.1 == k) = some (k, v) :=
            fun _ _ hmem => find_zip_of_nodup hDistinct hlen.symm hmem
          obtain ⟨rfl, rfl⟩ := evalArgs_vars_of_zip_suffix hlookup hlen.symm evArgs
          have hInst : instanceName [] targetQName (some []) = targetQName := by
            simp [instanceName, Instance.symbol]
          rw [hInst] at evCallee
          exact ⟨hlen, rfl, evCallee⟩

/-- **Forward completeness of `--assert-ok` `aliasEntry` (`assertOk = true`)**. -/
theorem aliasEntry_assertOk_complete
    {world : World F} {aliasQName targetQName : String}
    {paramNames : List String} {vs : List (SourceValue F)}
    (hDistinct : paramNames.Nodup)
    (hlen : vs.length = paramNames.length)
    (hPrep : world.prepare aliasQName vs = .ok ([], paramNames.zip vs,
      ((aliasEntryBody targetQName paramNames true).map (Nat.cast : Nat → F))))
    {h h' : Heap F}
    (evTarget : EvalFn world targetQName vs h (.field 1) h') :
    EvalFn world aliasQName vs h (.tuple []) h' := by
  have hlookup : ∀ k v, (k, v) ∈ paramNames.zip vs → (paramNames.zip vs).find? (·.1 == k) = some (k, v) :=
    fun _ _ hmem => find_zip_of_nodup hDistinct hlen.symm hmem
  have evArgs : EvalArgs world [] (paramNames.zip vs)
      ((paramNames.map vE).map (Aiur.Generic.Expr.map (Nat.cast : Nat → F))) h vs h := by
    rw [map_vE_cast]
    exact evalArgs_vars_of_zip_fwd hlookup hlen.symm h
  have hInst : instanceName [] targetQName (some []) = targetQName := by
    simp [instanceName, Instance.symbol]
  have evCall : EvalExpr world [] (paramNames.zip vs)
      (.call targetQName (some []) ((paramNames.map vE).map (Aiur.Generic.Expr.map (Nat.cast : Nat → F))))
      h (.field 1) h' :=
    .call evArgs (by rwa [hInst])
  have evOne : EvalExpr world [] (paramNames.zip vs) (.literal (1 : F)) h' (.field (1 : F)) h' :=
    .literal
  have hApp : (Builtin.assertEq assertOkAssertion).apply [(.field (1 : F)), (.field (1 : F))] =
      .ok (.tuple []) := by
    simp [Builtin.apply, evalAssertEq, Value.pointerFree]
  have evBody : EvalExpr world [] (paramNames.zip vs)
      ((aliasEntryBody targetQName paramNames true).map (Nat.cast : Nat → F)) h (.tuple []) h' := by
    simp only [aliasEntryBody, ↓reduceIte, callE, litE, Aiur.Generic.Expr.map, List.map, Nat.cast_one]
    exact .builtin (.cons evCall (.cons evOne .nil)) hApp
  exact .intro hPrep evBody

/-- **Certified backward soundness of custom entry-point aliasing (`aliasEntry_sound`)**:
for any aliased entry (passthrough or `--assert-ok`), any successful derivation of
the custom entry implies a matching derivation of `Prog::main<i>` on the exact same
arguments (and with result `.field 1` and unit return `.tuple []` when `assertOk = true`). -/
theorem aliasEntry_sound
    {world : World F} {aliasQName targetQName : String}
    {paramNames : List String} {assertOk : Bool}
    (hDistinct : paramNames.Nodup)
    (hFn : WorldHasFn world aliasQName paramNames
      ((aliasEntryBody targetQName paramNames assertOk).map (Nat.cast : Nat → F)))
    {vs : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalFn world aliasQName vs h r h') :
    if assertOk then
      r = .tuple [] ∧ EvalFn world targetQName vs h (.field 1) h'
    else
      EvalFn world targetQName vs h r h' := by
  cases assertOk
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact (aliasEntry_passthrough_sound hDistinct hFn ev).2
  · simp only [↓reduceIte]
    exact (aliasEntry_assertOk_sound hDistinct hFn ev).2

/-- Executable-check bridge: if `checkAliasEntry s spec = true` on a prepared
`Generic.Source F` (for a wrapped `spec`), then `aliasEntry_sound` holds directly
on `s.world`. -/
theorem aliasEntry_sound_of_check
    {s : Aiur.Generic.Source F} {spec : AliasSpec}
    (hWrap : spec.hasWrapper = true)
    (hChk : checkAliasEntry s spec = true)
    {vs : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalFn s.world spec.entry vs h r h') :
    if spec.assertOk then
      r = .tuple [] ∧ EvalFn s.world spec.targetEntry vs h (.field 1) h'
    else
      EvalFn s.world spec.targetEntry vs h r h' := by
  unfold checkAliasEntry at hChk
  simp only [hWrap, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
    decide_eq_true_eq] at hChk
  obtain ⟨⟨hNoDollar, hDistB⟩, hFind⟩ := hChk
  have hDistinct : spec.paramNames.Nodup := (allDistinct_iff_nodup spec.paramNames).mp hDistB
  have hFn : WorldHasFn s.world spec.entry spec.paramNames
      ((aliasEntryBody spec.targetEntry spec.paramNames spec.assertOk).map (Nat.cast : Nat → F)) :=
    World.worldHasFn_of_check s hNoDollar hFind
  exact aliasEntry_sound hDistinct hFn ev

end AliasSoundness

/-! ## Section 6: Library Usage Scans & Deduplicated Multi-Field Linker (`linkedProgramWith`) -/

mutual

private def exprHasPrefix (pfx : String) : Expr → Bool
  | .call nm _ xs => nm.startsWith pfx || exprListHasPrefix pfx xs
  | .global nm _ => nm.startsWith pfx
  | .literal _ | .var _ | .control _ _ => false
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs => exprListHasPrefix pfx xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x => exprHasPrefix pfx x
  | .letValue _ x b | .binary _ x b => exprHasPrefix pfx x || exprHasPrefix pfx b
  | .matchValue x arms => exprHasPrefix pfx x || armsHasPrefix pfx arms

private def exprListHasPrefix (pfx : String) : List Expr → Bool
  | [] => false
  | x :: xs => exprHasPrefix pfx x || exprListHasPrefix pfx xs

private def armsHasPrefix (pfx : String) : List (Pat × Expr) → Bool
  | [] => false
  | (_, b) :: rest => exprHasPrefix pfx b || armsHasPrefix pfx rest

end

mutual

private def tyHasPrefix (pfx : String) : Lower.Ty → Bool
  | .named nm args => nm.startsWith pfx || tyListHasPrefix pfx args
  | .tuple ts => tyListHasPrefix pfx ts
  | .array t _ | .ptr t => tyHasPrefix pfx t
  | _ => false

private def tyListHasPrefix (pfx : String) : List Lower.Ty → Bool
  | [] => false
  | t :: ts => tyHasPrefix pfx t || tyListHasPrefix pfx ts

end

private def fnHasPrefix (pfx : String) (f : Fn) : Bool :=
  exprHasPrefix pfx f.body ||
  tyHasPrefix pfx f.result ||
  f.params.any (fun p => tyHasPrefix pfx p.2)

/-- True iff any function in `fns` references `Goldilocks::*`. -/
def usesGoldilocksLibrary (fns : List Fn) : Bool :=
  fns.any (fnHasPrefix "Goldilocks::")

/-- True iff any function in `fns` references `Blake3::*`. -/
def usesBlake3Library (fns : List Fn) : Bool :=
  fns.any (fnHasPrefix "Blake3::")

/-- True iff any function in `fns` references `StarkIO::*`. -/
def usesStarkIOLibrary (fns : List Fn) : Bool :=
  fns.any (fnHasPrefix "StarkIO::")

/-- True iff any function in `fns` references `KzgIO::*`. -/
def usesKzgIOLibrary (fns : List Fn) : Bool :=
  fns.any (fnHasPrefix "KzgIO::")

/-- Multi-field library linking configuration for `linkedProgramWith`. -/
structure LinkConfig where
  /-- Link `Aiur.Library.Field.Goldilocks.Emulated` instead of native
  `Aiur.Library.Field.Goldilocks` (required over BN254 / BLS12-381). -/
  emulateGoldilocks : Bool := false
  /-- Link `Aiur.Library.Blake3` (and its U32/U64/List/Field/Bytes dependencies). -/
  linkBlake3 : Bool := false
  /-- Link `WitnessIO.starkIOModule` and `WitnessIO.kzgIOModule` for witness channels. -/
  witnessIO : Bool := false
  /-- Optional custom entry-point alias specification from `aliasEntry`. -/
  aliasSpec? : Option AliasSpec := none
  deriving Repr

/-- Deduplicated `Modules.Program Nat` composition for a `TypedLower.LoweredProgram`
under `LinkConfig`. Each Aiur library module and signature is appended at most once
in dependency order, guaranteeing `Aiur.Modules.validate` never encounters duplicate
modules or signatures for any combination of flags over Goldilocks, BN254, or BLS12-381. -/
def linkedProgramNat (cfg : LinkConfig) (lp : LoweredProgram) : Aiur.Modules.Program Nat :=
  let prog := match cfg.aliasSpec? with
    | some spec => spec.prog
    | none => lp.program
  let fns := prog.functions
  let needBlake3 := cfg.linkBlake3 || usesBlake3Library fns
  let needGoldilocks := cfg.emulateGoldilocks || usesGoldilocksLibrary fns
  let needStarkIO := cfg.witnessIO || usesStarkIOLibrary fns
  let needKzgIO := cfg.witnessIO || usesKzgIOLibrary fns
  let needBytes := needBlake3 || needStarkIO || needKzgIO || fns.any (fnHasPrefix "Bytes::")
  let needLists := needBytes || needBlake3 || needStarkIO || needKzgIO || fns.any (fnHasPrefix "Lists::")
  let needU64 := lp.tier == .u64 || needBlake3
  let needU32 := lp.tier == .u32 || needU64 || needKzgIO
  let needU8 := needU32 || needGoldilocks || needBytes || needStarkIO
  let needU8Byte := lp.tier == .byte256
  let needFields := usesFieldsLibrary fns || needBlake3 || needGoldilocks
  let acc : Aiur.Modules.Program Nat := {}
  let acc := if needU8Byte then acc.append TypedLower.u8ByteModule else acc
  let acc := if needU8 then acc.append Aiur.Library.U8.source else acc
  let acc := if needU32 then acc.append Aiur.Library.U32.declarations else acc
  let acc := if needU64 then acc.append Aiur.Library.U64.declarations else acc
  let acc := if needLists then acc.append Aiur.Library.List.declarations else acc
  let acc := if needFields then acc.append Aiur.Library.Field.declarations else acc
  let acc := if needBytes then acc.append Aiur.Library.Bytes.declarations else acc
  let acc := if needBlake3 then acc.append Aiur.Library.Blake3.declarations else acc
  let acc := if needGoldilocks then
    acc.append (if cfg.emulateGoldilocks then Aiur.Library.Field.Goldilocks.Emulated.declarations
                else Aiur.Library.Field.Goldilocks.declarations)
    else acc
  let acc := if needStarkIO then acc.append WitnessIO.starkIOModule else acc
  let acc := if needKzgIO then acc.append WitnessIO.kzgIOModule else acc
  let progMod : Aiur.Modules.Program Nat :=
    { modules := [{ name := moduleName, body := .definitions { program := prog } }] }
  let acc := acc.append progMod
  match cfg.aliasSpec?.bind (·.extraModule?) with
  | some extraMod => acc.append { modules := [extraMod] }
  | none => acc

/-- Specialize `linkedProgramNat` over any prime field `F` (`Goldilocks`, `BN254 Fr`,
`BLS12-381 Fr`, or arbitrary `ZMod p`). -/
def linkedProgramWith (F : Type) [NatCast F] (cfg : LinkConfig) (lp : LoweredProgram) :
    Aiur.Modules.Program F :=
  (linkedProgramNat cfg lp).toField F

/-- Executable world check for compression-linked programs: checks any custom
`AliasSpec` wrapper and checks `Blake3` / `StarkIO` / `KzgIO` library worlds
whenever they are referenced by `lp`. -/
def checkCompressionWorld {F : Type} [Field F] [DecidableEq F]
    (s : Aiur.Generic.Source F) (lp : LoweredProgram)
    (aliasSpec? : Option AliasSpec := none) : Bool :=
  let aliasOk := match aliasSpec? with
    | some spec => checkAliasEntry s spec
    | none => true
  let fns := lp.program.functions
  let blake3Ok := !usesBlake3Library fns || Blake3Spec.checkBlake3World s
  let starkIoOk := !usesStarkIOLibrary fns || WitnessIO.checkStarkIOFunctions s
  let kzgIoOk := !usesKzgIOLibrary fns || WitnessIO.checkKzgIOFunctions s
  aliasOk && blake3Ok && starkIoOk && kzgIoOk

end IxCC.AiurBackend.CompressionIntrinsics
