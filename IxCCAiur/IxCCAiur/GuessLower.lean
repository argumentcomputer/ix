import IxCCAiur.TypedLower
import IxCCAiur.TypedGadgets
import IxCC.Src.Table.Guess
import IxCC.Fir.Semantics

/-! # Phase 2.2d Tier-2 `guess f c θ [θc]` Lowering (`IxCCAiur.GuessLower`)

Rewrites validated Tier-2 `guess` subjects `f` (`Src.Program.table.guess`) in a
`TypedLower.LoweredProgram` into isolated, non-inlined verify-a-hint wrappers:

```aiur
fn f<fid>(p0: T0, ..., pk-1: Tk-1) -> R {
  let g_y: R = hint("ixcc.guess.f<fid>", (p0, ..., pk-1));
  let _ = <shapeCheck g_y>;           // U4: canonical bounds on raw advice!
  let g_ok = f<cid>(p0, ..., pk-1, g_y);
  assert_eq!(g_ok, <boolTrue>);
  g_y
}
```

Key invariants:
* **Aiur cost law**: Every rewritten guess wrapper is forced `isInline := false`
  so it stays isolated in its own dedicated small chip and is never inlined into
  wide callers.
* **U4 canonicality protection**: `isShapeCheckableRep` fails closed on `.obj`
  and pointer-bearing/cyclic `.data` representations; every accepted return
  representation receives an exact range/constructor check (`check_u56`,
  `check_u8`, `check_u16`, `check_u24`, `sub_borrow_56`, `UInt32::from_fields`,
  `UInt64::from_fields`, or exhaustive enum/data match) before the checker is
  invoked.
* **Certified `Fir.Code` oversized-literal comparison pre-pass**
  (`foldOversizedNatCmp`): folds `<`/`≤`/`==` comparisons between `< 2^56`-typed
  `Nat` operands and constants `M ≥ 2^56` (such as `maxFieldModulus = 2^384` in
  `fqInvMod.check`) directly to `Bool.true`/`Bool.false`, proved sound in
  `IxCCAiur.GuessLowerProof`.
* **Universal advice preparation** (`prepareAdviceProgram`): preserves the
  unmodified pre-guess lowered program with every resolved guess subject exposed
  as a non-inline entrypoint (`Prog::<adviceEntry>`), so both the Lean evaluator
  (`Hints.dispatcherWithAdvice`) and the Rust prover (`ixcc::register_advice_program`)
  generate exact honest advice with zero per-function hardcoding.
* **Plainness preservation**: every emitted expression is proved `Lower.isPlainExpr = true`.

Strictly total (zero `partial`), zero `sorry`, zero `native_decide`, zero `bv_decide`. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.GuessLower

open IxCC.Fir (Program Fun FunId Var Arg Rhs Code Alt CtorInfo)
open IxCC.Key
open IxCC.Lam (Lit Prim)
open IxCC.Shape (Shape DataDecl)
open IxCC.Fir.Shape (ShapeCert FunShapes)
open IxCC.AiurBackend.Lower
  (Ty Expr Pat Fn natLimit moduleName qualified funName entryName ctorNameOf
   pC callE vE litE letE seqE matchE assertion trapE isPlainExpr isPlainList isPlainArms)
open IxCC.AiurBackend.TypedRep
open IxCC.AiurBackend.TypedLower

/-! ## Channel & Advice Naming -/

/-- Prefix shared by Lean (`Hints.dispatcherWithAdvice`) and Rust (`ixcc::register_advice_program`). -/
def guessChannelPrefix : String := "ixcc.guess."

/-- Hint channel name for a lowered guess subject function `fName`. -/
def guessChannel (fName : String) : String := guessChannelPrefix ++ fName

/-- Entrypoint name (unqualified inside `Prog`) exposed in the companion advice program. -/
def adviceEntryName (fName : String) (usesOpaque : Bool) : String :=
  if usesOpaque then fName ++ "_advice" else fName

/-! ## Certified `Fir.Code` Oversized-Literal Comparison Pre-Pass -/

/-- Whether a `Fir.Shape` denotes a `< natLimit` (`< 2^56`) natural under `TypedRep`. -/
def isSmallNatShape : Shape → Bool
  | .nat => true
  | .natLt b => b ≤ natLimit
  | .word .w8 => true
  | .word .w16 => true
  | _ => false

/-- Whether a `Fir.Arg` is guaranteed `< natLimit` under `fsh`. -/
def isSmallNatArg (fsh : FunShapes) : Arg → Bool
  | .lit (.nat n) => n < natLimit
  | .var x => isSmallNatShape (fsh.var x)
  | _ => false

/-- Nullary `CtorInfo` for pinned `Bool.true` / `Bool.false`, if present with arity 0. -/
def boolCtorInfo? (P : Program) (b : Bool) : Option CtorInfo := do
  let k ← if b then P.known.boolTrue else P.known.boolFalse
  let info ← P.ctorInfo? k
  if info.arity == 0 then some info else none

/-- Fold a comparison between a `< natLimit` `Nat` operand and a literal `M ≥ natLimit`
directly into the pinned `Bool` constructor. Leaves all other `Rhs` unchanged. -/
def foldOversizedNatCmpRhs (P : Program) (fsh : FunShapes) (r : Rhs) : Rhs :=
  match r with
  | .prim op [a, b] =>
    let foldResult? : Option Bool :=
      match op, a, b with
      | .natBlt, x, .lit (.nat m) =>
        if natLimit ≤ m && isSmallNatArg fsh x then some true else none
      | .natBle, x, .lit (.nat m) =>
        if natLimit ≤ m && isSmallNatArg fsh x then some true else none
      | .natBlt, .lit (.nat m), x =>
        if natLimit ≤ m && isSmallNatArg fsh x then some false else none
      | .natBle, .lit (.nat m), x =>
        if natLimit ≤ m && isSmallNatArg fsh x then some false else none
      | .natBeq, x, .lit (.nat m) =>
        if natLimit ≤ m && isSmallNatArg fsh x then some false else none
      | .natBeq, .lit (.nat m), x =>
        if natLimit ≤ m && isSmallNatArg fsh x then some false else none
      | _, _, _ => none
    match foldResult?.bind (boolCtorInfo? P) with
    | some cInfo => .ctor cInfo []
    | none => r
  | _ => r

/-- Fuel budget for evaluating closed literal-argument helper calls (e.g. `pow2 384`) during
`foldOversizedNatCmpCode`. -/
def closedCallFuel : Nat := 1024

/-- Extract constant `Nat` literal values from an argument list when every argument is `.lit (.nat _)`. -/
def litNatArgs? : List Arg → Option (List IxCC.Fir.Val)
  | [] => some []
  | .lit (.nat n) :: rest => (litNatArgs? rest).map (.lit (.nat n) :: ·)
  | _ :: _ => none

/-- Conservative syntactic check: whether variable `x` is read anywhere inside `a`. -/
def argReadsVar (x : Var) : Arg → Bool
  | .var v => v == x
  | _ => false

/-- Conservative syntactic check: whether variable `x` is read anywhere inside `r`. -/
def rhsReadsVar (x : Var) : Rhs → Bool
  | .arg a => argReadsVar x a
  | .ctor _ as | .prim _ as | .call _ as => as.any (argReadsVar x)
  | .proj v _ _ => v == x

mutual

/-- Conservative syntactic check: whether variable `x` is read anywhere inside `c`
(including inside any nested join point bodies). When `false`, updating `ρ` at `x`
cannot change the evaluation of `c`. -/
def codeReadsVar (x : Var) : Code → Bool
  | .bind _ r k => rhsReadsVar x r || codeReadsVar x k
  | .jp _ _ _ b k => codeReadsVar x b || codeReadsVar x k
  | .jmp _ as | .tcall _ as => as.any (argReadsVar x)
  | .case v alts d => (v == x) || altsReadsVar x alts || optReadsVar x d
  | .ret a => argReadsVar x a
  | .trap => false

def altsReadsVar (x : Var) : List Alt → Bool
  | [] => false
  | .mk _ b :: rest => codeReadsVar x b || altsReadsVar x rest

def optReadsVar (x : Var) : Option Code → Bool
  | none => false
  | some c => codeReadsVar x c

end

/-- Check whether `.bind x (.call g as) (.bind y (.prim op [a, b]) k')` evaluates a closed
`Nat` constant `m ≥ natLimit` whose only use is an oversized comparison against a `< natLimit`
operand; if so, returns the pinned `Bool` constructor `CtorInfo` to replace the pair. -/
def foldOversizedCallStep? (P : Program) (fsh : FunShapes)
    (x : Var) (g : FunId) (as : List Arg)
    (y : Var) (op : Prim) (a b : Arg) (k' : Code) : Option CtorInfo := do
  guard (x != y && !codeReadsVar x k')
  let vs ← litNatArgs? as
  match IxCC.Fir.evalCall P closedCallFuel g vs with
  | .ok (.lit (.nat m)) =>
    guard (natLimit ≤ m)
    let substX := fun (arg : Arg) => if arg == .var x then Arg.lit (.nat m) else arg
    match foldOversizedNatCmpRhs P fsh (.prim op [substX a, substX b]) with
    | .ctor cInfo [] => some cInfo
    | _ => none
  | _ => none

mutual

def foldOversizedNatCmpCode (P : Program) (fsh : FunShapes) : Code → Code
  | .bind x (.call g as) (.bind y (.prim op [a, b]) k') =>
    match foldOversizedCallStep? P fsh x g as y op a b k' with
    | some cInfo => .bind y (.ctor cInfo []) (foldOversizedNatCmpCode P fsh k')
    | none =>
      .bind x (.call g as)
        (.bind y (foldOversizedNatCmpRhs P fsh (.prim op [a, b]))
          (foldOversizedNatCmpCode P fsh k'))
  | .bind x r k =>
    .bind x (foldOversizedNatCmpRhs P fsh r) (foldOversizedNatCmpCode P fsh k)
  | .jp j ps isRec b k =>
    .jp j ps isRec (foldOversizedNatCmpCode P fsh b) (foldOversizedNatCmpCode P fsh k)
  | .case x alts d =>
    .case x (foldOversizedNatCmpAlts P fsh alts) (foldOversizedNatCmpOpt P fsh d)
  | c => c

def foldOversizedNatCmpAlts (P : Program) (fsh : FunShapes) : List Alt → List Alt
  | [] => []
  | .mk k b :: rest =>
    .mk k (foldOversizedNatCmpCode P fsh b) :: foldOversizedNatCmpAlts P fsh rest

def foldOversizedNatCmpOpt (P : Program) (fsh : FunShapes) : Option Code → Option Code
  | none => none
  | some c => some (foldOversizedNatCmpCode P fsh c)

end

/-- Rewrite all function bodies in `P` with `foldOversizedNatCmpCode` using `cert`.
Preserves `size`, `exports`, `ctors`, `known`, function keys, and parameter lists. -/
def foldOversizedNatCmp (P : Program) (cert : ShapeCert) : Program :=
  let funs' := P.funList.foldl (init := P.funs) fun acc (fid, fd) =>
    acc.insert fid { fd with body := foldOversizedNatCmpCode P (cert.fn fid) fd.body }
  { P with funs := funs' }

/-! ## Guess-Aware `ShapeCert` Inference -/

/-- Extract source `CId` from a direct/specialized `GKey`. -/
def gkeySourceCId? : GKey → Option IxCC.Src.CId
  | .const c _ | .byName c _ => some c
  | .spec g _ | .worker g _ | .entry g _ => gkeySourceCId? g
  | .recStar _ _ | .wrapper _ _ | .lam _ _ | .dispatch _ => none

/-- Locate a `Fir.FunId` corresponding to source constant `cid` with expected arity `arity`.
Prefers exact `.const cid []` over wrapper/specialized keys. -/
def findFirFunForCId (P : Program) (cid : IxCC.Src.CId) (arity : Nat) : Option (FunId × Fun) :=
  match P.funList.find? fun (_, fd) => fd.key == .const cid [] && fd.params.length == arity with
  | some p => some p
  | none => P.funList.find? fun (_, fd) =>
      gkeySourceCId? fd.key == some cid && fd.params.length == arity

/-- Collect `(fFunId, cFunId)` pairs for every validated `guess` entry present in `P`. -/
def guessFunPairs (src : IxCC.Src.Program) (P : Program) : List (FunId × FunId) :=
  src.table.guess.toList.filterMap fun (fCId, g) => do
    let (fFid, _) ← findFirFunForCId P fCId g.arity
    let (cFid, _) ← findFirFunForCId P g.checker (g.arity + 1)
    return (fFid, cFid)

mutual

private def seedCode (cFid : FunId) (fParams : List Arg) (fresh : Var) : Code → Code
  | .bind x r k => .bind x r (seedCode cFid fParams fresh k)
  | .jp j ps isRec b k =>
    .jp j ps isRec (seedCode cFid fParams fresh b) (seedCode cFid fParams fresh k)
  | .case x alts d =>
    .case x (seedAlts cFid fParams fresh alts) (seedOpt cFid fParams fresh d)
  | .ret a =>
    .bind (fresh + 1) (.call cFid (fParams ++ [a])) (.ret a)
  | .tcall g as =>
    .bind fresh (.call g as)
      (.bind (fresh + 1) (.call cFid (fParams ++ [.var fresh])) (.ret (.var fresh)))
  | c => c

private def seedAlts (cFid : FunId) (fParams : List Arg) (fresh : Var) : List Alt → List Alt
  | [] => []
  | .mk k b :: rest => .mk k (seedCode cFid fParams fresh b) :: seedAlts cFid fParams fresh rest

private def seedOpt (cFid : FunId) (fParams : List Arg) (fresh : Var) : Option Code → Option Code
  | none => none
  | some c => some (seedCode cFid fParams fresh c)

end

/-- Infer a `ShapeCert` on a guess-seeded copy of `P` (where each subject `f` synthetically
calls its checker `c` on `(fParams, ret)` so `c`'s parameter shapes match `f`'s exact
inferred parameter/return shapes, including monomorphic structs like `QuotRem`), then
independently verify `Fir.Shape.check P cert` on the real `P`! Falls back cleanly to
`TypedRep.inferCheckedShapes src P` if verification fails. -/
def seedGuessShapes (src : IxCC.Src.Program) (P : Program) : ShapeCert × Bool :=
  let pairs := guessFunPairs src P
  if pairs.isEmpty then
    TypedRep.inferCheckedShapes src P
  else
    let seededFuns := pairs.foldl (init := P.funs) fun acc (fFid, cFid) =>
      match acc.get? fFid with
      | none => acc
      | some fd =>
        let fParams := fd.params.map fun (v, _) => Arg.var v
        let fresh := fd.vars + 1
        acc.insert fFid { fd with body := seedCode cFid fParams fresh fd.body, vars := fresh + 2 }
    let PSeed : Program := { P with funs := seededFuns }
    let cert := IxCC.Fir.ShapeInfer.infer PSeed (shapeInferConfig src)
    if IxCC.Fir.Shape.check P cert then
      (cert, true)
    else
      TypedRep.inferCheckedShapes src P

/-! ## Representation Safety, Raw Hint Types & `U4` Shape Checks -/

/-- Whether `r` contains no heap pointers (required by Formal Aiur for hint keys/results). -/
def isPointerFreeRep (P : Program) (cert : ShapeCert) (feat : Features) : Nat → Rep → Bool
  | _, .irr | _, .nat _ | _, .w8 | _, .w16 | _, .w32 | _, .w64 => true
  | _, .enum ind => validEnum P cert ind
  | 0, .data _ => false
  | fuel + 1, .data d =>
    validData P cert d &&
    match cert.data? d with
    | none => false
    | some D =>
      D.ctors.all fun (_, fl) =>
        fl.all fun sh =>
          let fr := repOf P cert feat sh
          !dataFieldNeedsPtr P cert feat d fr && isPointerFreeRep P cert feat fuel fr
  | _, .obj => false

/-- Whether `r` contains neither heap pointers nor opaque library types (`UInt8::U8`,
`UInt32::U32`, `UInt64::U64`), so it may appear directly in a Formal Aiur `hint` type
or an entry signature. -/
def isNonOpaqueRep (P : Program) (cert : ShapeCert) (feat : Features) : Nat → Rep → Bool
  | _, .irr | _, .nat _ | _, .w8 | _, .w16 => true
  | _, .w32 | _, .w64 => false
  | _, .enum ind => validEnum P cert ind
  | 0, .data _ => false
  | fuel + 1, .data d =>
    validData P cert d &&
    match cert.data? d with
    | none => false
    | some D =>
      D.ctors.all fun (_, fl) =>
        fl.all fun sh =>
          let fr := repOf P cert feat sh
          !dataFieldNeedsPtr P cert feat d fr && isNonOpaqueRep P cert feat fuel fr
  | _, .obj => false

/-- Whether `r` is eligible as a guess return representation with a complete, certified `U4`
canonical bounds check. Fails closed on `.obj`, empty `.nat 0`, and cyclic/pointer-bearing
or opaque-containing `.data` structs. -/
def isShapeCheckableRep (P : Program) (cert : ShapeCert) (feat : Features) : Nat → Rep → Bool
  | _, .irr => true
  | _, .nat b => 0 < min b natLimit
  | _, .w8 | _, .w16 | _, .w32 | _, .w64 => true
  | _, .enum ind => validEnum P cert ind
  | 0, .data _ => false
  | fuel + 1, .data d =>
    validData P cert d &&
    match cert.data? d with
    | none => false
    | some D =>
      D.ctors.all fun (_, fl) =>
        fl.all fun sh =>
          let fr := repOf P cert feat sh
          !dataFieldNeedsPtr P cert feat d fr &&
          isNonOpaqueRep P cert feat fuel fr &&
          isShapeCheckableRep P cert feat fuel fr
  | _, .obj => false

/-- Whether a parameter `Rep` can be marshalled through the host hint key channel. -/
def isHintKeyParamRep (P : Program) (cert : ShapeCert) (feat : Features) (fuel : Nat) :
    Rep → Bool
  | .w32 | .w64 => true
  | r => isNonOpaqueRep P cert feat fuel r

/-- Whether `r` uses an opaque library word type (`.w32` or `.w64`) requiring raw `[Field; N]`
hint marshalling. -/
def repUsesOpaque : Rep → Bool
  | .w32 | .w64 => true
  | _ => false

/-- Non-opaque Formal Aiur type transmitted over a hint channel for `r`. -/
def rawHintTy : Rep → Ty
  | .w32 => .array .field 4
  | .w64 => .array .field 8
  | r => r.aiurTy

/-- Convert a value expression `e` of type `r.aiurTy` into its non-opaque raw hint value of
type `rawHintTy r`. -/
def toRawExpr (r : Rep) (e : Expr) : Expr :=
  match r with
  | .w32 =>
    letE "g_bs" (callE "UInt32::to_bytes" [e])
      (.array [
        callE "UInt8::to_field" [.index (vE "g_bs") 0],
        callE "UInt8::to_field" [.index (vE "g_bs") 1],
        callE "UInt8::to_field" [.index (vE "g_bs") 2],
        callE "UInt8::to_field" [.index (vE "g_bs") 3]
      ])
  | .w64 =>
    letE "g_bs" e
      (.array [
        callE "UInt8::to_field" [.index (vE "g_bs") 0],
        callE "UInt8::to_field" [.index (vE "g_bs") 1],
        callE "UInt8::to_field" [.index (vE "g_bs") 2],
        callE "UInt8::to_field" [.index (vE "g_bs") 3],
        callE "UInt8::to_field" [.index (vE "g_bs") 4],
        callE "UInt8::to_field" [.index (vE "g_bs") 5],
        callE "UInt8::to_field" [.index (vE "g_bs") 6],
        callE "UInt8::to_field" [.index (vE "g_bs") 7]
      ])
  | _ => e

/-- Convert a raw hint value `e` of type `rawHintTy r` into a checked value of type `r.aiurTy`.
For `.w32` and `.w64`, `UInt32::from_fields` / `UInt64::from_fields` also performs the complete
`U4` per-byte canonicality check (`< 256` per byte). -/
def fromRawExpr (r : Rep) (e : Expr) : Expr :=
  match r with
  | .w32 => callE "UInt32::from_fields" [e]
  | .w64 => callE "UInt64::from_fields" [e]
  | _ => e

/-- Component-wise logical OR of two `TypedLower.Demand` records. -/
def mergeDemand (a b : Demand) : Demand :=
  { needObj := a.needObj || b.needObj
    needBytes := a.needBytes || b.needBytes
    needCheckU56 := a.needCheckU56 || b.needCheckU56
    needCheckU16 := a.needCheckU16 || b.needCheckU16
    needCheckU24 := a.needCheckU24 || b.needCheckU24
    needSubBorrow56 := a.needSubBorrow56 || b.needSubBorrow56
    needMul56 := a.needMul56 || b.needMul56
    needDivMod56 := a.needDivMod56 || b.needDivMod56
    needPow56 := a.needPow56 || b.needPow56
    needGcd56 := a.needGcd56 || b.needGcd56
    needShl56 := a.needShl56 || b.needShl56
    needShr56 := a.needShr56 || b.needShr56
    needU32Mul := a.needU32Mul || b.needU32Mul
    needU32Comp := a.needU32Comp || b.needU32Comp
    needU32Div := a.needU32Div || b.needU32Div
    needU32Mod := a.needU32Mod || b.needU32Mod
    needU32Shl := a.needU32Shl || b.needU32Shl
    needU32Shr := a.needU32Shr || b.needU32Shr
    needU32OfField := a.needU32OfField || b.needU32OfField
    needU64Bitwise := a.needU64Bitwise || b.needU64Bitwise
    needU64Shl := a.needU64Shl || b.needU64Shl
    needU64Shr := a.needU64Shr || b.needU64Shr }

/-- Sequence a list of unit-returning expressions followed by `()`. -/
def seqUnitList : List Expr → Expr
  | [] => .tuple []
  | [e] => e
  | e :: es => seqE e (seqUnitList es)

/-- Emit the exact `U4` canonical shape-check expression (returning `()`) for variable `yNm`
of representation `r`, together with any helper `Demand` flags it requires.

Every accepted case guarantees `TVR P cert feat h r v yVal` upon successful evaluation:
* `.irr` → unpacks `let () = yNm; ()`;
* `.nat b` → `check_u56` / `check_u8` / `check_u16` / `check_u24`, or `check_u56` +
  `sub_borrow_56(yNm, min b natLimit).1 == 0` for arbitrary `0 < bound < natLimit`;
* `.w8` / `.w16` → `check_u8` / `check_u16`;
* `.w32` / `.w64` → `()` (canonical byte checks already enforced by `fromRawExpr`);
* `.enum ind` → exhaustive constructor match over `E<ind>`;
* `.data d` → exhaustive constructor match over `D<d>`, recursively checking every field. -/
def shapeCheckExpr (P : Program) (cert : ShapeCert) (feat : Features) :
    Nat → String → Rep → String → Expr × Demand
  | _, _, .irr, yNm =>
    (.letValue (.tuple []) (vE yNm) (.tuple []), {})
  | _, _, .nat b, yNm =>
    let bound := min b natLimit
    if bound == natLimit then
      (callE "check_u56" [vE yNm], { needCheckU56 := true })
    else if bound == 256 then
      (callE "check_u8" [vE yNm], { needCheckU56 := true })
    else if bound == 65536 then
      (callE "check_u16" [vE yNm], { needCheckU16 := true })
    else if bound == 16777216 then
      (callE "check_u24" [vE yNm], { needCheckU24 := true })
    else
      (seqE (callE "check_u56" [vE yNm])
        (.letValue (.tuple [.wildcard, .bind "g_ge"])
          (callE "sub_borrow_56" [vE yNm, litE bound])
          (.builtin (.assertEq (assertion "guess: nat exceeds shape bound"))
            [vE "g_ge", litE 0])),
       { needCheckU56 := true, needSubBorrow56 := true })
  | _, _, .w8, yNm =>
    (callE "check_u8" [vE yNm], { needCheckU56 := true })
  | _, _, .w16, yNm =>
    (callE "check_u16" [vE yNm], { needCheckU16 := true })
  | _, _, .w32, _ =>
    (.tuple [], {})
  | _, _, .w64, _ =>
    (.tuple [], {})
  | _, _, .enum ind, yNm =>
    match cert.enum? ind with
    | none => (trapE "guess: unknown enum", {})
    | some ks =>
      let arms : List (Pat × Expr) := ks.filterMap fun k =>
        (Lower.ctorEntry? P k).map fun (idx, e) =>
          (.construct (.named (enumName ind) []) (ctorNameOf idx e.key) [], .tuple [])
      if arms.isEmpty then (trapE "guess: empty enum", {})
      else (matchE (vE yNm) arms, {})
  | 0, _, .data _, _ =>
    (trapE "guess: data depth exceeded", {})
  | fuel + 1, pfx, .data d, yNm =>
    match cert.data? d with
    | none => (trapE "guess: unknown data", {})
    | some D =>
      let armPairs : List ((Pat × Expr) × Demand) := D.ctors.filterMap fun (k, fl) =>
        (Lower.ctorEntry? P k).map fun (idx, e) =>
          let fieldChecks : List (String × Expr × Demand) :=
            fl.zipIdx.map fun (sh, fi) =>
              let fnm := pfx ++ "_" ++ String.ofList (Lower.natDigits fi)
              let fr := repOf P cert feat sh
              let (fe, fd) := shapeCheckExpr P cert feat fuel fnm fr fnm
              (fnm, fe, fd)
          let pat : Pat := .construct (.named (dataName d) []) (ctorNameOf idx e.key)
            (fieldChecks.map fun (fnm, _, _) => .bind fnm)
          let body := seqUnitList (fieldChecks.map fun (_, fe, _) => fe)
          let dem := fieldChecks.foldl (init := ({} : Demand)) fun acc (_, _, fd) => mergeDemand acc fd
          ((pat, body), dem)
      if armPairs.isEmpty then (trapE "guess: empty data", {})
      else
        let arms := armPairs.map Prod.fst
        let dem := armPairs.foldl (init := ({} : Demand)) fun acc (_, d1) => mergeDemand acc d1
        (matchE (vE yNm) arms, dem)
  | _, _, .obj, _ =>
    (trapE "guess: unsupported obj shape", {})

/-! ## Checking the Checker's `Bool.true` Result -/

/-- How the guess wrapper verifies that `c(args, y)` returned `Bool.true`. -/
inductive BoolCheckKind where
  /-- Dedicated `E<ind>` enumeration (`assert_eq!(g_ok, E<ind>::<trueCtor>)`). -/
  | enumTrue (ind : IxCC.Src.CId) (trueCtorName : String)
  /-- Fallback boxed `Obj` (`match g_ok { Obj::<trueCtor> => g_y, _ => assert_eq!(0, 1); g_y }`). -/
  | objTrue (trueCtorName : String)
  deriving DecidableEq, Repr, Inhabited

/-- Resolve how `c`'s return value of representation `cRetRep` encodes `Bool.true`. -/
def boolCheckKind? (P : Program) (cert : ShapeCert) (cRetRep : Rep) : Option BoolCheckKind := do
  let tt ← P.known.boolTrue
  let (idx, entry) ← Lower.ctorEntry? P tt
  unless entry.arity == 0 do none
  let ctorNm := ctorNameOf idx entry.key
  match cRetRep with
  | .enum ind =>
    let ks ← cert.enum? ind
    if validEnum P cert ind && ks.contains tt then
      some (.enumTrue ind ctorNm)
    else none
  | .obj => some (.objTrue ctorNm)
  | _ => none

/-! ## Guess Resolution, Wrapper Construction & Advice Manifest -/

/-- A fully validated and shape-checked Tier-2 `guess` rewrite target. -/
structure ResolvedGuess where
  fCId : IxCC.Src.CId
  cCId : IxCC.Src.CId
  thmCId : IxCC.Src.CId
  compCId? : Option IxCC.Src.CId
  fFunId : FunId
  cFunId : FunId
  fName : String
  cName : String
  channel : String
  adviceEntry : String
  paramNames : List String
  paramReps : List Rep
  retRep : Rep
  boolCheck : BoolCheckKind
  usesOpaque : Bool
  deriving Repr

/-- Metadata for one advice channel, serialized/inspected by host advice drivers. -/
structure AdviceChannelInfo where
  channel : String
  fName : String
  adviceEntry : String
  paramCount : Nat
  usesOpaque : Bool
  deriving Repr, DecidableEq

/-- Advice manifest listing all `"ixcc.guess.*"` channels emitted by `applyGuesses`. -/
structure AdviceManifest where
  channels : List AdviceChannelInfo := []
  deriving Repr, DecidableEq

/-- Result of applying `GuessLower` to a `TypedLower.LoweredProgram`. -/
structure GuessLowerResult where
  lowered : LoweredProgram
  resolved : List ResolvedGuess
  skipped : List (IxCC.Src.CId × String)
  manifest : AdviceManifest

/-- Resolve all validated `src.table.guess` entries against `(P, lp)`.
Fails closed (recording a diagnostic in `skipped`) whenever:
* subject or checker is absent from `P` or `lp.program`,
* parameter count or parameter/return `Rep`s do not align between `f` and `c`,
* any parameter is not pointer-free / hint-key-safe,
* `retRep` is not shape-checkable (`U4`, e.g., `.obj` or cyclic `.data`),
* checker return rep cannot represent `Bool.true`, or
* any parameter name collides with the reserved `"g_"` wrapper prefix. -/
def resolveGuesses (src : IxCC.Src.Program) (P : Program) (lp : LoweredProgram) :
    List ResolvedGuess × List (IxCC.Src.CId × String) :=
  let cert := lp.cert
  let feat := scanFeatures P
  let fuel := cert.datas.length + 2
  src.table.guess.toList.foldl (init := ([], [])) fun (okAcc, skipAcc) (fCId, g) =>
    let skip (reason : String) := (okAcc, skipAcc ++ [(fCId, reason)])
    match findFirFunForCId P fCId g.arity, findFirFunForCId P g.checker (g.arity + 1) with
    | none, _ => skip "subject function not present in FIR with matching arity"
    | _, none => skip "checker function not present in FIR with matching arity"
    | some (fFid, fFd), some (cFid, cFd) =>
      let fName := funName fFid
      let cName := funName cFid
      match lp.program.functions.find? (·.name == fName),
            lp.program.functions.find? (·.name == cName) with
      | none, _ => skip s!"lowered subject {fName} missing"
      | _, none => skip s!"lowered checker {cName} missing"
      | some fFn, some cFn =>
        let fsh := cert.fn fFid
        let csh := cert.fn cFid
        let fParamReps := (fFd.params.map Prod.fst).map fun v => repOf P cert feat (fsh.var v)
        let fRetRep := repOf P cert feat fsh.ret
        let cParamReps := (cFd.params.map Prod.fst).map fun v => repOf P cert feat (csh.var v)
        let cRetRep := repOf P cert feat csh.ret
        let pNames := fFn.params.map Prod.fst
        if fFn.params.length != g.arity || cFn.params.length != g.arity + 1 then
          skip "lowered parameter arity mismatch"
        else if cParamReps != fParamReps ++ [fRetRep] then
          skip s!"checker param reps {reprStr cParamReps} != {reprStr (fParamReps ++ [fRetRep])}"
        else if !Lower.allDistinct pNames then
          skip "duplicate parameter names in lowered subject"
        else if pNames.any (·.startsWith "g_") then
          skip "parameter name collides with guess wrapper prefix g_"
        else if !fParamReps.all (isHintKeyParamRep P cert feat fuel) then
          skip s!"non-hintable parameter rep in {reprStr fParamReps}"
        else if !isShapeCheckableRep P cert feat fuel fRetRep then
          skip s!"non-shape-checkable return rep {reprStr fRetRep} (U4 fail-closed)"
        else
          match boolCheckKind? P cert cRetRep with
          | none => skip s!"checker return rep {reprStr cRetRep} is not Bool"
          | some boolCheck =>
            let usesOpaque := fParamReps.any repUsesOpaque || repUsesOpaque fRetRep
            let rg : ResolvedGuess := {
              fCId, cCId := g.checker, thmCId := g.thm, compCId? := g.comp?
              fFunId := fFid, cFunId := cFid
              fName, cName
              channel := guessChannel fName
              adviceEntry := adviceEntryName fName usesOpaque
              paramNames := pNames
              paramReps := fParamReps
              retRep := fRetRep
              boolCheck
              usesOpaque
            }
            (okAcc ++ [rg], skipAcc)

/-- Emit the verified-hint body for `g` together with the extra helper `Demand` required
by its `U4` shape check. -/
def guessWrapperBody (P : Program) (cert : ShapeCert) (feat : Features) (g : ResolvedGuess) :
    Expr × Demand :=
  let keyExpr : Expr :=
    .tuple ((g.paramNames.zip g.paramReps).map fun (nm, r) => toRawExpr r (vE nm))
  let callChk : Expr := callE g.cName (g.paramNames.map vE ++ [vE "g_y"])
  let checkTail : Expr :=
    letE "g_ok" callChk <|
      match g.boolCheck with
      | .enumTrue ind ctorNm =>
        seqE (.builtin (.assertEq (assertion "guess: checker returned false"))
               [vE "g_ok", .construct (enumName ind) (some []) ctorNm []])
          (vE "g_y")
      | .objTrue ctorNm =>
        matchE (vE "g_ok")
          [(pC ctorNm [], vE "g_y"),
           (.wildcard, seqE (.builtin (.assertEq (assertion "guess: checker returned false"))
             [litE 0, litE 1]) (vE "g_y"))]
  match g.retRep with
  | .w32 =>
    let body :=
      letE "g_raw" (.hint (rawHintTy .w32) keyExpr g.channel) <|
      letE "g_y" (fromRawExpr .w32 (vE "g_raw")) checkTail
    (body, {})
  | .w64 =>
    let body :=
      letE "g_raw" (.hint (rawHintTy .w64) keyExpr g.channel) <|
      letE "g_y" (fromRawExpr .w64 (vE "g_raw")) checkTail
    (body, { needU64Bitwise := true })
  | _ =>
    let (chkExpr, chkDem) :=
      shapeCheckExpr P cert feat (cert.datas.length + 2) "g_f" g.retRep "g_y"
    let body :=
      letE "g_y" (.hint (rawHintTy g.retRep) keyExpr g.channel) <|
      seqE chkExpr checkTail
    (body, chkDem)

/-- Ensure the `LoweredProgram` includes any newly demanded range-check helpers and
upgrades `TableTier.none` → `TableTier.byte256` (or to `.u64` if `needU64Bitwise` was added). -/
def linkDemandedHelpers (lp : LoweredProgram) (extraDemand : Demand) : LoweredProgram :=
  let d := mergeDemand lp.demand extraDemand
  let needsRangeCheck :=
    d.needCheckU56 || d.needCheckU16 || d.needCheckU24 || d.needSubBorrow56 ||
    d.needMul56 || d.needDivMod56
  let tier :=
    if d.needU64Bitwise then .u64
    else if lp.tier == .none && needsRangeCheck then .byte256
    else lp.tier
  let usePair := tier == .u32 || tier == .u64
  let helpers := demandedHelpers d usePair
  let existingNames := lp.program.functions.map (·.name)
  let missing := helpers.filter fun h => !existingNames.contains h.name
  { lp with
    program := { lp.program with functions := lp.program.functions ++ missing }
    tier
    demand := d }

/-- Rewrite all resolved Tier-2 `guess` subjects in `lp` to isolated (`isInline := false`)
verify-a-hint wrappers, linking any newly required `U4` range-check helpers. -/
def applyGuesses (src : IxCC.Src.Program) (P : Program) (lp : LoweredProgram) :
    GuessLowerResult :=
  let (resolved, skipped) := resolveGuesses src P lp
  if resolved.isEmpty then
    { lowered := lp, resolved := [], skipped, manifest := {} }
  else
    let feat := scanFeatures P
    let wrappers : List (String × Expr × Demand) :=
      resolved.map fun g =>
        let (body, dem) := guessWrapperBody P lp.cert feat g
        (g.fName, body, dem)
    let extraDemand :=
      wrappers.foldl (init := ({} : Demand)) fun acc (_, _, dem) => mergeDemand acc dem
    let fns' := lp.program.functions.map fun f =>
      match wrappers.find? (·.1 == f.name) with
      | some (_, body, _) => { f with body, isInline := false }
      | none => f
    let lp1 : LoweredProgram :=
      { lp with program := { lp.program with functions := fns' } }
    let lp2 := linkDemandedHelpers lp1 extraDemand
    let manifest : AdviceManifest := {
      channels := resolved.map fun g => {
        channel := g.channel
        fName := g.fName
        adviceEntry := g.adviceEntry
        paramCount := g.paramNames.length
        usesOpaque := g.usesOpaque
      }
    }
    { lowered := lp2, resolved, skipped, manifest }

/-- Prepare the companion unmodified pre-guess `LoweredProgram` for host advice execution:
* forces `isInline := false` on every resolved guess subject so `Aiur.Modules.prepare`
  accepts `Prog::<fName>` as a callable entrypoint;
* appends a non-opaque raw-field adapter `<fName>_advice` whenever `g.usesOpaque = true`;
* returns `(adviceProgram, adviceEntryQualifiedNames)`. -/
def prepareAdviceProgram (lp : LoweredProgram) (resolved : List ResolvedGuess) :
    LoweredProgram × List String :=
  let subjectNames := resolved.map (·.fName)
  let fns0 := lp.program.functions.map fun f =>
    if subjectNames.contains f.name then { f with isInline := false } else f
  let adapters : List Fn := resolved.filterMap fun g =>
    if !g.usesOpaque then none
    else
      let rawParams : List (String × Ty) :=
        (g.paramNames.zip g.paramReps).map fun (nm, r) => (nm, rawHintTy r)
      let callArgs : List Expr :=
        (g.paramNames.zip g.paramReps).map fun (nm, r) => fromRawExpr r (vE nm)
      let body : Expr := toRawExpr g.retRep (callE g.fName callArgs)
      some {
        name := g.adviceEntry
        params := rawParams
        result := rawHintTy g.retRep
        body
        isInline := false
      }
  let lp' : LoweredProgram :=
    { lp with program := { lp.program with functions := fns0 ++ adapters } }
  let entries := resolved.map fun g => qualified g.adviceEntry
  (lp', entries)

/-! ## Plainness Preservation Proofs (Zero `sorry`) -/

section Plainness

theorem isPlainExpr_toRawExpr (r : Rep) (e : Expr) (he : isPlainExpr e = true) :
    isPlainExpr (toRawExpr r e) = true := by
  cases r <;> simp [toRawExpr, letE, callE, vE, isPlainExpr, isPlainList, he]

theorem isPlainExpr_fromRawExpr (r : Rep) (e : Expr) (he : isPlainExpr e = true) :
    isPlainExpr (fromRawExpr r e) = true := by
  cases r <;> simp [fromRawExpr, callE, isPlainExpr, isPlainList, he]

theorem isPlainExpr_seqUnitList :
    ∀ es : List Expr, (∀ e ∈ es, isPlainExpr e = true) → isPlainExpr (seqUnitList es) = true
  | [], _ => rfl
  | [e], h => h e List.mem_cons_self
  | e1 :: e2 :: rest, h => by
    simp only [seqUnitList, seqE, isPlainExpr, Bool.and_eq_true]
    exact ⟨h e1 List.mem_cons_self,
      isPlainExpr_seqUnitList (e2 :: rest) fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

private theorem isPlainList_map_true {α : Type*} (f : α → Expr) (xs : List α)
    (h : ∀ x ∈ xs, isPlainExpr (f x) = true) :
    isPlainList (xs.map f) = true := by
  induction xs with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.map_cons, isPlainList, Bool.and_eq_true]
    exact ⟨h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

private theorem isPlainArms_of_all (arms : List (Pat × Expr))
    (h : ∀ arm ∈ arms, isPlainExpr arm.2 = true) :
    isPlainArms arms = true := by
  induction arms with
  | nil => rfl
  | cons a tl ih =>
    rcases a with ⟨p, b⟩
    simp only [isPlainArms, Bool.and_eq_true]
    exact ⟨h (p, b) List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

theorem isPlainExpr_shapeCheckExpr (P : Program) (cert : ShapeCert) (feat : Features) :
    ∀ (fuel : Nat) (pfx : String) (r : Rep) (yNm : String),
      isPlainExpr (shapeCheckExpr P cert feat fuel pfx r yNm).1 = true
  | fuel, pfx, .irr, yNm => by
    simp [shapeCheckExpr, vE, isPlainExpr, isPlainList]
  | fuel, pfx, .nat b, yNm => by
    unfold shapeCheckExpr
    dsimp only
    split_ifs <;> simp [callE, vE, litE, seqE, isPlainExpr, isPlainList]
  | fuel, pfx, .w8, yNm => by
    simp [shapeCheckExpr, callE, vE, isPlainExpr, isPlainList]
  | fuel, pfx, .w16, yNm => by
    simp [shapeCheckExpr, callE, vE, isPlainExpr, isPlainList]
  | fuel, pfx, .w32, yNm => by
    simp [shapeCheckExpr, isPlainExpr, isPlainList]
  | fuel, pfx, .w64, yNm => by
    simp [shapeCheckExpr, isPlainExpr, isPlainList]
  | fuel, pfx, .enum ind, yNm => by
    unfold shapeCheckExpr
    cases h : cert.enum? ind with
    | none => simp [trapE, seqE, litE, Lower.erasedE, Lower.mk, isPlainExpr, isPlainList]
    | some ks =>
      dsimp only
      split
      · simp [trapE, seqE, litE, Lower.erasedE, Lower.mk, isPlainExpr, isPlainList]
      · simp only [matchE, vE, isPlainExpr, Bool.true_and]
        apply isPlainArms_of_all
        intro arm harm
        simp only [List.mem_filterMap, Option.map_eq_some_iff] at harm
        obtain ⟨_, _, _, _, rfl⟩ := harm
        rfl
  | 0, pfx, .data d, yNm => by
    simp [shapeCheckExpr, trapE, seqE, litE, Lower.erasedE, Lower.mk, isPlainExpr, isPlainList]
  | fuel + 1, pfx, .data d, yNm => by
    unfold shapeCheckExpr
    cases h : cert.data? d with
    | none => simp [trapE, seqE, litE, Lower.erasedE, Lower.mk, isPlainExpr, isPlainList]
    | some D =>
      dsimp only
      split
      · simp [trapE, seqE, litE, Lower.erasedE, Lower.mk, isPlainExpr, isPlainList]
      · simp only [matchE, vE, isPlainExpr, Bool.true_and]
        apply isPlainArms_of_all
        intro arm harm
        simp only [List.mem_map] at harm
        obtain ⟨⟨arm', _⟩, harm', rfl⟩ := harm
        simp only [List.mem_filterMap] at harm'
        obtain ⟨⟨k, fl⟩, _, hMap⟩ := harm'
        cases hce : Lower.ctorEntry? P k with
        | none => simp [hce] at hMap
        | some ce =>
          rcases ce with ⟨idx, e⟩
          simp only [hce, Option.map_some, Option.some.injEq] at hMap
          have hBodyEq : arm'.2 = seqUnitList ((fl.zipIdx.map fun (sh, fi) =>
              let fnm := pfx ++ "_" ++ String.ofList (Lower.natDigits fi)
              let fr := repOf P cert feat sh
              let (fe, fd) := shapeCheckExpr P cert feat fuel fnm fr fnm
              (fnm, fe, fd)).map fun (_, fe, _) => fe) := by
            have := congrArg (fun p => p.1.2) hMap
            simpa using this.symm
          rw [hBodyEq]
          apply isPlainExpr_seqUnitList
          intro fe hfe
          rw [List.mem_map] at hfe
          obtain ⟨⟨fnm, fe', fd'⟩, hmem, rfl⟩ := hfe
          rw [List.mem_map] at hmem
          obtain ⟨⟨sh, fi⟩, _, hEq2⟩ := hmem
          have hfeEq : fe' = (shapeCheckExpr P cert feat fuel
              (pfx ++ "_" ++ String.ofList (Lower.natDigits fi))
              (repOf P cert feat sh)
              (pfx ++ "_" ++ String.ofList (Lower.natDigits fi))).1 := by
            have := congrArg (fun p => p.2.1) hEq2
            simpa using this.symm
          rw [hfeEq]
          exact isPlainExpr_shapeCheckExpr P cert feat fuel _ _ _
  | fuel, pfx, .obj, yNm => by
    simp [shapeCheckExpr, trapE, seqE, litE, Lower.erasedE, Lower.mk, isPlainExpr, isPlainList]

theorem isPlainExpr_guessWrapperBody (P : Program) (cert : ShapeCert) (feat : Features)
    (g : ResolvedGuess) :
    isPlainExpr (guessWrapperBody P cert feat g).1 = true := by
  have hKey : isPlainExpr
      (Aiur.Generic.Expr.tuple ((g.paramNames.zip g.paramReps).map fun (nm, r) => toRawExpr r (vE nm))) = true := by
    simp only [isPlainExpr]
    exact isPlainList_map_true _ _ fun (nm, r) _ => isPlainExpr_toRawExpr r (vE nm) rfl
  have hCall : isPlainExpr (callE g.cName (g.paramNames.map vE ++ [vE "g_y"])) = true := by
    simp only [callE, isPlainExpr]
    have hmap : isPlainList (g.paramNames.map vE) = true :=
      isPlainList_map_true vE g.paramNames fun _ _ => rfl
    have happ : ∀ (xs ys : List Expr), isPlainList xs = true → isPlainList ys = true →
        isPlainList (xs ++ ys) = true := by
      intro xs ys hxs hys
      induction xs with
      | nil => exact hys
      | cons a tl ih =>
        simp only [List.cons_append, isPlainList, Bool.and_eq_true] at hxs ⊢
        exact ⟨hxs.1, ih hxs.2⟩
    exact happ _ _ hmap (by simp [vE, isPlainList, isPlainExpr])
  have hTail : isPlainExpr
      (match g.boolCheck with
       | .enumTrue ind ctorNm =>
         seqE (.builtin (.assertEq (assertion "guess: checker returned false"))
                [vE "g_ok", .construct (enumName ind) (some []) ctorNm []])
           (vE "g_y")
       | .objTrue ctorNm =>
         matchE (vE "g_ok")
           [(pC ctorNm [], vE "g_y"),
            (.wildcard, seqE (.builtin (.assertEq (assertion "guess: checker returned false"))
              [litE 0, litE 1]) (vE "g_y"))]) = true := by
    cases g.boolCheck with
    | enumTrue ind ctorNm =>
      simp [seqE, vE, isPlainExpr, isPlainList]
    | objTrue ctorNm =>
      simp [matchE, seqE, vE, litE, isPlainExpr, isPlainList, isPlainArms]
  unfold guessWrapperBody
  cases hret : g.retRep with
  | w32 =>
    dsimp only
    rw [letE, isPlainExpr, Bool.and_eq_true]
    refine ⟨hKey, ?_⟩
    rw [letE, isPlainExpr, Bool.and_eq_true]
    refine ⟨isPlainExpr_fromRawExpr .w32 (vE "g_raw") rfl, ?_⟩
    rw [letE, isPlainExpr, Bool.and_eq_true]
    exact ⟨hCall, hTail⟩
  | w64 =>
    dsimp only
    rw [letE, isPlainExpr, Bool.and_eq_true]
    refine ⟨hKey, ?_⟩
    rw [letE, isPlainExpr, Bool.and_eq_true]
    refine ⟨isPlainExpr_fromRawExpr .w64 (vE "g_raw") rfl, ?_⟩
    rw [letE, isPlainExpr, Bool.and_eq_true]
    exact ⟨hCall, hTail⟩
  | irr | nat _ | w8 | w16 | «enum» _ | data _ | obj =>
    dsimp only
    rw [letE, isPlainExpr, Bool.and_eq_true]
    refine ⟨hKey, ?_⟩
    rw [seqE, isPlainExpr, Bool.and_eq_true]
    refine ⟨isPlainExpr_shapeCheckExpr P cert feat (cert.datas.length + 2) "g_f" _ "g_y", ?_⟩
    rw [letE, isPlainExpr, Bool.and_eq_true]
    exact ⟨hCall, hTail⟩

theorem isPlainExpr_applyGuesses (src : IxCC.Src.Program) (P : Program) (lp : LoweredProgram)
    (hPlain : ∀ f ∈ lp.program.functions, isPlainExpr f.body = true) :
    ∀ f ∈ (applyGuesses src P lp).lowered.program.functions, isPlainExpr f.body = true := by
  unfold applyGuesses
  dsimp only
  split
  · exact hPlain
  · intro f hf
    unfold linkDemandedHelpers at hf
    simp only [List.mem_append, List.mem_map, List.mem_filter] at hf
    rcases hf with ⟨g0, hg0, rfl⟩ | ⟨hmem, _⟩
    · split
      · rename_i nm body dem hw
        have hmemW := List.mem_of_find?_eq_some hw
        simp only [List.mem_map] at hmemW
        obtain ⟨rg, _, hEq⟩ := hmemW
        have hBodyEq : body = (guessWrapperBody P lp.cert (scanFeatures P) rg).1 := by
          have := congrArg (fun p => p.2.1) hEq
          simpa using this.symm
        simpa [hBodyEq] using isPlainExpr_guessWrapperBody P lp.cert (scanFeatures P) rg
      · exact hPlain g0 hg0
    · exact IxCC.AiurBackend.TypedGadgets.isPlainExpr_demandedHelpers _ _ f hmem

end Plainness

end IxCC.AiurBackend.GuessLower
