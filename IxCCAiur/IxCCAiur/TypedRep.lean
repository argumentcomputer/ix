import IxCCAiur.Lower
import IxCCAiur.Schedule
import IxCC.Fir.Shape
import IxCC.Fir.ShapeInfer

/-! # Typed Representations, Free-Variable Analysis & Demand Linking (`IxCCAiur.TypedRep`)

Maps a checked `IxCC.Fir.Shape.ShapeCert` to compact, unboxed Formal Aiur
representations (`Rep`), computes exact transitive free variables for join
points, classifies which library tiers (`none`, `byte256`, `u32`, `u64`) and
auxiliary enums (`Obj`, `Bytes`) a `Fir.Program` actually requires, and
decides sharing-aware `Function.isInline` flags from `CircuitSchedule`.

Nothing in this file is trusted: `TypedBackward` proves backward simulation for
every lowered program regardless of how `ShapeCert` or `CircuitSchedule` was
produced. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.TypedRep

open IxCC.Fir
open IxCC.Key
open IxCC.Shape (Shape DataDecl)
open IxCC.Fir.Shape (ShapeCert FunShapes)
open IxCC.AiurBackend.Lower (Ty natLimit natDigits ctorNameOf objName bytesName objTy bytesTy)
open IxCC.AiurBackend.Schedule (CircuitSchedule InlinePolicy RangeCheckMode)

/-! ## Concrete Aiur Representation per `Shape` -/

/-- The lowered Aiur representation of a `Fir` value. -/
inductive Rep where
  /-- Erased / irrelevant value: lowered to `()` (0 field columns). -/
  | irr
  /-- Small natural `< bound` (with `bound ≤ natLimit`): lowered to raw `Field` (1 column). -/
  | nat (bound : Nat)
  /-- 8-bit word `< 256`: lowered to raw `Field` (1 column). -/
  | w8
  /-- 16-bit word `< 65536`: lowered to raw `Field` (1 column). -/
  | w16
  /-- 32-bit word `< 2^32`: lowered to `UInt32::U32` (`[UInt8::U8; 4]`, 4 checked bytes). -/
  | w32
  /-- 64-bit word `< 2^64`: lowered to `UInt64::U64` (`[UInt8::U8; 8]`, 8 checked bytes). -/
  | w64
  /-- Dedicated nullary enumeration `E<ind>` (1 column tag, 0 payload). -/
  | enum (ind : Src.CId)
  /-- Dedicated per-inductive enum `D<d>` (unboxed non-recursive fields, `&D<d>` on cycles). -/
  | data (d : Nat)
  /-- Universal fallback `Obj` (for `.any`, closures `.fn`, strings, heterogeneous values). -/
  | obj
  deriving DecidableEq, Repr, Inhabited

/-- Dedicated Aiur enum name for a `ShapeCert` enumeration `ind`. -/
def enumName (ind : Src.CId) : String := String.ofList ('E' :: natDigits ind)

/-- Dedicated Aiur enum name for a `ShapeCert` data entry `d`. -/
def dataName (d : Nat) : String := String.ofList ('D' :: natDigits d)

def enumQName (ind : Src.CId) : String := Lower.qualified (enumName ind)
def dataQName (d : Nat) : String := Lower.qualified (dataName d)

def u8Ty : Ty := .named "UInt8::U8" []
def u32Ty : Ty := .named "UInt32::U32" []
def u64Ty : Ty := .named "UInt64::U64" []

/-- The Formal Aiur type of a `Rep`. -/
def Rep.aiurTy : Rep → Ty
  | .irr => .tuple []
  | .nat _ => .field
  | .w8 => .field
  | .w16 => .field
  | .w32 => u32Ty
  | .w64 => u64Ty
  | .enum ind => .named (enumName ind) []
  | .data d => .named (dataName d) []
  | .obj => objTy

/-- Whether `r` is stored as a single raw `Field` holding a `< natLimit` natural. -/
def Rep.isFieldNat : Rep → Bool
  | .nat _ | .w8 | .w16 => true
  | _ => false

/-- Upper bound `b ≤ natLimit` guaranteed for a field-natural `Rep`. -/
def Rep.fieldBound : Rep → Nat
  | .nat b => min b natLimit
  | .w8 => 256
  | .w16 => 65536
  | _ => natLimit

/-- Whether a `ShapeCert` enumeration `ind` is usable as a dedicated Aiur enum:
present, non-empty, and every listed key is in `P.ctors` with arity 0. -/
def validEnum (P : Program) (cert : ShapeCert) (ind : Src.CId) : Bool :=
  match cert.enum? ind with
  | some ks =>
    !ks.isEmpty && ks.all fun k =>
      match Lower.ctorEntry? P k with
      | some (_, e) => e.arity == 0
      | none => false
  | none => false

/-- Whether a `ShapeCert` data entry `d` is usable as a dedicated Aiur enum:
present, non-empty, and every listed constructor matches `P.ctors` in arity. -/
def validData (P : Program) (cert : ShapeCert) (d : Nat) : Bool :=
  match cert.data? d with
  | some D =>
    !D.ctors.isEmpty && D.ctors.all fun (k, fl) =>
      match Lower.ctorEntry? P k with
      | some (_, e) => e.arity == fl.length
      | none => false
  | none => false

/-- Program-level feature scan over a `Fir.Program` to drive demand-based library
linking, `UInt32` representation choice, and `Obj`/`Bytes` pruning. -/
structure Features where
  usesPrim : List Lam.Prim := []
  usesStr : Bool := false
  usesW8 : Bool := false
  usesW16 : Bool := false
  usesW32 : Bool := false
  usesW64 : Bool := false
  usesBitwiseNat : Bool := false
  usesDivMod : Bool := false
  usesMul : Bool := false
  usesSubCmp : Bool := false
  usesAdd : Bool := false
  deriving Repr, Inhabited

private def recordArg (a : Arg) (f : Features) : Features :=
  match a with
  | .lit (.str _) => { f with usesStr := true }
  | _ => f

private def recordArgs (as : List Arg) (f : Features) : Features :=
  as.foldl (fun acc a => recordArg a acc) f

private def recordPrim (op : Lam.Prim) (f : Features) : Features :=
  let f := if f.usesPrim.contains op then f else { f with usesPrim := op :: f.usesPrim }
  match op with
  | .natAdd => { f with usesAdd := true }
  | .natSub | .natBle | .natBlt => { f with usesSubCmp := true }
  | .natMul | .natPow => { f with usesMul := true }
  | .natDiv | .natMod | .natGcd | .natShl | .natShr => { f with usesDivMod := true }
  | .natLand | .natLor | .natXor => { f with usesBitwiseNat := true }
  | .word w _ =>
    match w with
    | .w8 => { f with usesW8 := true }
    | .w16 => { f with usesW16 := true }
    | .w32 => { f with usesW32 := true }
    | .w64 => { f with usesW64 := true }
  | _ => f

mutual

private def scanCode (f : Features) : Code → Features
  | .bind _ r k =>
    let f1 := match r with
      | .arg a => recordArg a f
      | .ctor _ as => recordArgs as f
      | .proj .. => f
      | .prim op as => recordPrim op (recordArgs as f)
      | .call _ as => recordArgs as f
    scanCode f1 k
  | .jp _ _ _ b k => scanCode (scanCode f b) k
  | .jmp _ as | .tcall _ as => recordArgs as f
  | .case _ alts d => scanOpt (scanAlts f alts) d
  | .ret a => recordArg a f
  | .trap => f

private def scanAlts (f : Features) : List Alt → Features
  | [] => f
  | .mk _ b :: rest => scanAlts (scanCode f b) rest

private def scanOpt (f : Features) : Option Code → Features
  | none => f
  | some c => scanCode f c

end

/-- Scan a complete `Fir.Program` for used primitives and literals. -/
def scanFeatures (P : Program) : Features :=
  P.funList.foldl (fun acc (_, fd) => scanCode acc fd.body) {}

/-- Choose the `Rep` for a `Shape` under `(P, cert, feat)`.
* `.irr` → `.irr` (`()`, 0 columns)
* `.word .w8/.w16/.w32/.w64` → `.w8/.w16/.w32/.w64`
* `.natLt b`:
  - `b == 2^32` when `feat.usesW32` → `.w32` (`UInt32::U32`, native BLAKE3 layout)
  - `b ≤ natLimit` → `.nat b` (1-column raw `Field`, interval-tracked!)
  - `b ≤ 2^64` → `.w64` (`UInt64::U64`, full 64-bit range!)
  - otherwise → `.nat natLimit`
* `.nat` → `.nat natLimit`
* `.enum ind` (valid) → `.enum ind` (1-column tag)
* `.data d` (valid) → `.data d` (unboxed non-recursive fields)
* everything else → `.obj`. -/
def repOf (P : Program) (cert : ShapeCert) (feat : Features) : Shape → Rep
  | .irr => .irr
  | .word .w8 => .w8
  | .word .w16 => .w16
  | .word .w32 => .w32
  | .word .w64 => .w64
  | .natLt b =>
    if feat.usesW32 && b == 2 ^ 32 then .w32
    else if feat.usesW64 && b == 2 ^ 64 then .w64
    else if b ≤ natLimit then .nat b
    else .nat natLimit
  | .nat => .nat natLimit
  | .enum ind => if validEnum P cert ind then .enum ind else .obj
  | .data d => if validData P cert d then .data d else .obj
  | _ => .obj

/-- Whether data entry `d`'s field of representation `r` must be stored behind a
ROM pointer (`&D<d>`). Only cyclic data references (fields whose `Rep` is
`.data d'` with `d' ≥ d` or reachable back to `d`) need pointer indirection;
all scalar, enum, word, and strictly acyclic fields live inline unboxed! -/
def dataFieldNeedsPtr (P : Program) (cert : ShapeCert) (feat : Features)
    (owner : Nat) (r : Rep) : Bool :=
  match r with
  | .data d' =>
    -- Conservative cycle break: box whenever `d'` can reach `owner` in `cert.datas`.
    canReach cert P feat cert.datas.length d' owner
  | _ => false
where
  canReach (cert : ShapeCert) (P : Program) (feat : Features) :
      Nat → Nat → Nat → Bool
    | 0, _, _ => true
    | fuel + 1, cur, target =>
      if cur == target then true
      else
        match cert.data? cur with
        | none => false
        | some D =>
          D.ctors.any fun (_, fl) =>
            fl.any fun s =>
              match repOf P cert feat s with
              | .data next => canReach cert P feat fuel next target
              | _ => false

/-! ## Library Linking Tiers -/

/-- Minimum Formal Aiur library tier required by a lowered program. -/
inductive TableTier where
  /-- Zero byte tables linked (only raw field ops, `natPred`, `natBeq`, enums, structs). -/
  | none
  /-- Slim 256-row `UInt8::byte_inputs` table only (`check_u56`, `sub_borrow_56`,
  `mul_56`, `divmod_56`, `UInt8`/`UInt16` range checks): 256× smaller than `U8.source`! -/
  | byte256
  /-- Full `UInt8` + `UInt32` library (needed when `UInt32` ops are used without `UInt64`). -/
  | u32
  /-- Full `UInt8` + `UInt32` + `UInt64` library (needed when `UInt64` or bitwise `Nat` ops are used). -/
  | u64
  deriving DecidableEq, Repr, Inhabited

/-- Determine the minimal `TableTier` for `(feat, sched, usesRangeCheck)`. -/
def tableTier (feat : Features) (sched : CircuitSchedule) (usesRangeCheck : Bool) : TableTier :=
  if feat.usesW64 || feat.usesBitwiseNat then .u64
  else if feat.usesW32 then .u32
  else if feat.usesW8 || feat.usesW16 || usesRangeCheck then
    match sched.rangeCheck with
    | .pairTable => .u64
    | .smallTable | .auto => .byte256
  else .none

/-! ## Exact Transitive Free-Variable Analysis for Join Points -/

private def insertVar (x : Var) (xs : List Var) : List Var :=
  if xs.contains x then xs else x :: xs

private def unionVars (a b : List Var) : List Var :=
  a.foldl (fun acc x => insertVar x acc) b

private def removeVars (bound xs : List Var) : List Var :=
  xs.filter fun x => !bound.contains x

private def argVars : Arg → List Var
  | .var x => [x]
  | _ => []

private def argsVars (as : List Arg) : List Var :=
  as.foldl (fun acc a => unionVars (argVars a) acc) []

private def rhsVars : Rhs → List Var
  | .arg a => argVars a
  | .ctor _ as | .prim _ as | .call _ as => argsVars as
  | .proj x _ _ => [x]

mutual

/-- Compute the exact free `Fir.Var`s of `c`, given a map `jcaps` from in-scope
`JoinId`s to their captured free variables. Used so lifted join points capture
ONLY the variables they (or join points they jump to) actually read! -/
def freeVarsCode (jcaps : List (JoinId × List Var)) : Code → List Var
  | .bind x r k =>
    unionVars (rhsVars r) (removeVars [x] (freeVarsCode jcaps k))
  | .jp j ps isRec body k =>
    let bodyFree := removeVars ps (freeVarsCode (if isRec then (j, []) :: jcaps else jcaps) body)
    unionVars bodyFree (freeVarsCode ((j, bodyFree) :: jcaps) k)
  | .jmp j as =>
    let cap := (jcaps.lookup j).getD []
    unionVars cap (argsVars as)
  | .case x alts d =>
    insertVar x (unionVars (freeVarsAlts jcaps alts) (freeVarsOpt jcaps d))
  | .ret a => argVars a
  | .tcall _ as => argsVars as
  | .trap => []

def freeVarsAlts (jcaps : List (JoinId × List Var)) : List Alt → List Var
  | [] => []
  | .mk _ b :: rest => unionVars (freeVarsCode jcaps b) (freeVarsAlts jcaps rest)

def freeVarsOpt (jcaps : List (JoinId × List Var)) : Option Code → List Var
  | none => []
  | some c => freeVarsCode jcaps c

end

/-! ## Sharing-Aware Inlining & Call-Graph Analysis -/

mutual

/-- Approximate AST size of a `Fir.Code` (for auto-inlining heuristics). -/
def codeSize : Code → Nat
  | .bind _ _ k => 1 + codeSize k
  | .jp _ _ _ b k => 1 + codeSize b + codeSize k
  | .case _ alts d => 1 + altsSize alts + optSize d
  | .jmp .. | .ret _ | .tcall .. | .trap => 1

def altsSize : List Alt → Nat
  | [] => 0
  | .mk _ b :: rest => codeSize b + altsSize rest

def optSize : Option Code → Nat
  | none => 0
  | some c => codeSize c

end

mutual

/-- Direct `Fir.FunId` callees of a `Fir.Code`. -/
def directCallees : Code → List FunId
  | .bind _ r k =>
    match r with
    | .call g _ => g :: directCallees k
    | _ => directCallees k
  | .jp _ _ _ b k => directCallees b ++ directCallees k
  | .case _ alts d => directCalleesAlts alts ++ directCalleesOpt d
  | .tcall g _ => [g]
  | .jmp .. | .ret _ | .trap => []

def directCalleesAlts : List Alt → List FunId
  | [] => []
  | .mk _ b :: rest => directCallees b ++ directCalleesAlts rest

def directCalleesOpt : Option Code → List FunId
  | none => []
  | some c => directCallees c

end

/-- Whether `f` can reach `target` in the call graph of `P` (within `fuel` steps). -/
def canCall (P : Program) : Nat → FunId → FunId → Bool
  | 0, _, _ => true
  | fuel + 1, cur, target =>
    match P.fun? cur with
    | none => false
    | some fd =>
      let cs := directCallees fd.body
      cs.contains target || cs.any fun g => canCall P fuel g target

/-- Whether `f` is recursive (directly or mutually) in `P`. -/
def isRecursiveFun (P : Program) (f : FunId) : Bool :=
  canCall P (P.size + 1) f f

mutual

/-- Count static jumps to join point `j` inside `c` (respecting shadowing). -/
def countJumps (j : JoinId) : Code → Nat
  | .bind _ _ k => countJumps j k
  | .jp j' _ isRec b k =>
    (if j' == j && isRec then 0 else countJumps j b) +
    (if j' == j then 0 else countJumps j k)
  | .jmp j' _ => if j' == j then 1 else 0
  | .case _ alts d => countJumpsAlts j alts + countJumpsOpt j d
  | .ret _ | .tcall .. | .trap => 0

def countJumpsAlts (j : JoinId) : List Alt → Nat
  | [] => 0
  | .mk _ b :: rest => countJumps j b + countJumpsAlts j rest

def countJumpsOpt (j : JoinId) : Option Code → Nat
  | none => 0
  | some c => countJumps j c

end

/-- Decide `isInline` for a top-level `Fir` function `f` under `sched`.
Never inlines recursive functions or entry exports. -/
def shouldInlineFun (P : Program) (sched : CircuitSchedule) (f : FunId) (fd : Fun) : Bool :=
  if isRecursiveFun P f then false
  else
    match (sched.forFun f).inline with
    | .always => true
    | .never => false
    | .auto => sched.autoInline && codeSize fd.body ≤ sched.inlineMaxNodes

/-- Decide `isInline` for a lifted join point `(j, isRec, body, k)` under `sched`. -/
def shouldInlineJp (sched : CircuitSchedule) (j : JoinId) (isRec : Bool) (body k : Code) : Bool :=
  if isRec || !sched.autoInline then false
  else countJumps j k ≤ 1 || codeSize body ≤ 16

/-! ## `ShapeInfer` Helper for `IxCCAiur` -/

/-- Build `ShapeInfer.Config` from a `Src.Program`, assuming export parameters
are `< natLimit` (enforced by `main<i>`). -/
def shapeInferConfig (src : Src.Program) : Fir.ShapeInfer.Config :=
  { indOf := fun c =>
      match src.decl? c with
      | some (.ctor _ _ ind _ _ _ _) => some ind
      | _ => none
    rootParam := .natLt natLimit }

/-- Infer and verify a `ShapeCert` for `(src, P)`. Returns `(cert, accepted)`;
falls back cleanly to `ShapeInfer.trivial P` if the checker refuses. -/
def inferCheckedShapes (src : Src.Program) (P : Program) : ShapeCert × Bool :=
  Fir.ShapeInfer.run P (shapeInferConfig src)

end IxCC.AiurBackend.TypedRep
