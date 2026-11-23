import IxCC.Fir.Semantics
import IxCC.Lam.WordSem
import IxCC.Lam.Erase.Limb
import IxCC.Lam.Erase.Array

/-! # DR2 Stage W2: Checked Word Representations, Scalar Fields, and `box` / `unbox` in Fir

Activates `Fir.Rep.word` (unboxed 64-bit unsigned integer `< 2^64`), `Fir.Rep.obj` (uniform
polymorphic value where a `UInt64` is boxed in a 1-scalar-word cell `⟨nobj = 0, nscalar = 1,
tag = 0⟩`), `Fir.Rep.tobj` (Phase 1 tagged/pointer value), and `CtorInfo.nscalar > 0` scalar
tails via a kernel-evaluable representation certificate (`Fir.Rep.Cert`, D17):

* `Cert.check`: linear structural validator verifying that every `.word` variable, parameter,
  join-point parameter, function return, and scalar-tail constructor field is guaranteed to
  evaluate in `Fir.eval` to `.lit (.nat n)` with `n < 2^64`, and that no `.obj` value (which may
  hold a boxed 1-scalar-word cell) reaches a tagged-`Nat` primitive or `Nat` switch without
  unboxing (`Fir.Proof.Rep.check_sound`).
* `RepRhs` / `RepCode` / `RepProgram`: Stage W2 explicit-representation Fir with `Rhs.box` and
  `Rhs.unbox` and scalar-tail `CtorInfo` (`nscalar > 0`) populated by `elaborate`.
* `infer`: kernel-evaluable bounded-fixpoint producer of `Cert` for a `Fir.Program`. -/

set_option autoImplicit false

namespace IxCC.Fir.Rep

open IxCC.Fir (Var FunId JoinId Arg CtorInfo Fun Program Code Alt Val Env)
open IxCC.Src (Width WordOp)

/-- Canonical 1-scalar-word boxed `UInt64` cell layout (`nobj = 0, nscalar = 1, tag = 0`):
class 2 (16 bytes), `scan = 0` (no object fields for RC to scan), raw 64-bit word at `+8`. -/
def wordBoxCtor (key : Key.CtorKey) : CtorInfo :=
  { key, tag := 0, nobj := 0, nscalar := 1, fieldKinds := [] }

/-- Apply an explicit `(nobj, nscalar)` split to a constructor info (`fieldKinds` has length `nobj`). -/
def CtorInfo.withScalars (c : CtorInfo) (nobj nscalar : Nat) : CtorInfo :=
  { c with nobj, nscalar, fieldKinds := List.replicate nobj .shared }

/-- Allowed representations in a Stage W2 certificate (`.tobj`, `.obj`, `.word`). -/
def isValidRep : Fir.Rep → Bool
  | .tobj | .obj | .word => true
  | .erased => false

/-- Constructor scalar-tail layout override: `nobj` object fields (of representation `objRep`,
either `.tobj` or `.obj`), followed by `nscalar` raw 64-bit `.word` fields. -/
structure CtorRep where
  key : Key.CtorKey
  nobj : Nat
  nscalar : Nat
  objRep : Fir.Rep := .tobj
  deriving DecidableEq, Repr, Inhabited

def CtorRep.arity (cr : CtorRep) : Nat := cr.nobj + cr.nscalar

def CtorRep.fieldRep (cr : CtorRep) (i : Nat) : Fir.Rep :=
  if i < cr.nobj then cr.objRep else .word

/-- Per-function checked representation annotation. -/
structure FunCert where
  params : List Fir.Rep := []
  ret : Fir.Rep := .tobj
  vars : Src.NatMap Fir.Rep := .leaf
  joins : Src.NatMap (List Fir.Rep) := .leaf
  deriving Inhabited

def FunCert.varRep (fc : FunCert) (x : Var) : Fir.Rep := fc.vars.getD x .tobj

def FunCert.joinReps (fc : FunCert) (j : JoinId) : List Fir.Rep := fc.joins.getD j []

/-- Native contiguous array/bytearray primitive operation bound to a `Fir.FunId` (DR3). -/
inductive ArrayPrimOp where
  | emptyCap
  | size
  | get
  | getBang
  | set
  | push
  | pop
  | extract
  | copySlice
  | swap
  deriving DecidableEq, Repr, Inhabited

/-- Whether an array primitive may mutate its receiver in place when unique (`rc == 0`). -/
def ArrayPrimOp.isMutating : ArrayPrimOp → Bool
  | .set | .push | .pop | .copySlice | .swap => true
  | .emptyCap | .size | .get | .getBang | .extract => false

/-- Binding of one `Fir.FunId` to a native DR3 array/bytearray runtime proc.
`argIdx` gives the surviving `Fir.Fun` parameter positions (after any `DeadParam`
stripping) corresponding to the runtime proc's value arguments:
* `emptyCap`: `[]` (capacity 0) or `[capIdx]`
* `size`: `[arrIdx]`
* `get`: `[arrIdx, idxIdx]`
* `set`: `[arrIdx, idxIdx, valIdx]`
* `push`: `[arrIdx, valIdx]`
* `pop`: `[arrIdx]`
* `extract`: `[arrIdx, startIdx, stopIdx]`
* `copySlice`: `[srcIdx, srcOffIdx, destIdx, destOffIdx, lenIdx]`
* `swap`: `[arrIdx, iIdx, jIdx]` -/
structure ArrayPrimSpec where
  op : ArrayPrimOp
  kind : Src.ArrayRepKind
  argIdx : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- Program-wide Stage W2 + DR3 representation certificate. -/
structure Cert where
  funs : Src.NatMap FunCert := .leaf
  ctors : List CtorRep := []
  /-- DR3 native array/bytearray primitive bindings by `Fir.FunId`. -/
  arrayPrims : Src.NatMap ArrayPrimSpec := .leaf
  /-- Constructor key of `Array.mk` when `Array` is lowered to native contiguous cells. -/
  arrayMkKey : Option Key.CtorKey := none
  /-- Representation kind for `Array.mk` / `Array.toList` (`.boxed` or `.limbs`). -/
  arrayMkKind : Src.ArrayRepKind := .boxed
  /-- Constructor key of `ByteArray.mk` when `ByteArray` is lowered to packed byte cells. -/
  byteArrayMkKey : Option Key.CtorKey := none
  /-- Tag of `List.nil` (for `arrToList*` bridges). -/
  listNilTag : Nat := 0
  /-- Tag of `List.cons` (for `arrToList*` bridges). -/
  listConsTag : Nat := 1
  deriving Inhabited

def Cert.hasArrays (cert : Cert) : Bool :=
  !cert.arrayPrims.toList.isEmpty || cert.arrayMkKey.isSome || cert.byteArrayMkKey.isSome

def Cert.empty : Cert := {}

def Cert.funCert (cert : Cert) (f : FunId) : FunCert := cert.funs.getD f {}

def Cert.ctorRep? (cert : Cert) (k : Key.CtorKey) : Option CtorRep :=
  cert.ctors.find? (·.key == k)

/-- Constructor info with `nobj`/`nscalar` from `cert` wired in when present. -/
def Cert.ctorInfo (cert : Cert) (table : List Lam.CtorInfo) (k : Key.CtorKey) : Option CtorInfo :=
  (CtorInfo.ofKey table k).map fun c =>
    match cert.ctorRep? k with
    | some cr =>
      if cr.nobj + cr.nscalar == c.arity then CtorInfo.withScalars c cr.nobj cr.nscalar else c
    | none => c

/-- Representation of field `i` of constructor `k` under `cert`. -/
def Cert.fieldRep (cert : Cert) (k : Key.CtorKey) (i : Nat) : Fir.Rep :=
  match cert.ctorRep? k with
  | some cr => cr.fieldRep i
  | none => .tobj

/-! ## Checking a Representation Certificate (kernel-evaluable, D17) -/

/-- Whether a `Lam.Prim` is an unsigned comparison (`natBeq`, `natBle`, `natBlt`), which can
operate directly on two raw 64-bit `.word` operands as well as two tagged `.tobj` operands. -/
def isCmpPrim : Lam.Prim → Bool
  | .natBeq | .natBle | .natBlt => true
  | _ => false

/-- Whether `a` can supply a value of expected representation `expected` (with `box64` inserted
automatically when `.word` flows into `.obj`, and `.tobj → .obj` a zero-cost subtyping step). -/
def argCompat (fc : FunCert) (a : Arg) (expected : Fir.Rep) : Bool :=
  match expected with
  | .word =>
    match a with
    | .var y => fc.varRep y == .word
    | .lit (.nat n) => decide (n < 2 ^ 64)
    | _ => false
  | .obj =>
    match a with
    | .var y => isValidRep (fc.varRep y)
    | .lit (.nat _) | .lit (.str _) | .erased => true
  | .tobj =>
    match a with
    | .var y => fc.varRep y == .tobj
    | .lit _ | .erased => true
  | .erased => false

def argsCompat (fc : FunCert) : List Arg → List Fir.Rep → Bool
  | [], [] => true
  | a :: as, r :: rs => argCompat fc a r && argsCompat fc as rs
  | _, _ => false

/-- Whether an operand is valid as input to a word primitive (`Lam.Prim.word w op`): `.word`,
`.obj` (unboxed by `unbox64`), or `.tobj` (untagged by `>>> 1`), or any literal. -/
def wordPrimArgOk (fc : FunCert) : Arg → Bool
  | .var y => isValidRep (fc.varRep y)
  | .lit (.nat _) => true
  | _ => false

/-- Check a single constructor's `CtorRep` override against the program's table and pinned keys. -/
def checkCtorRep (P : Program) (cr : CtorRep) : Bool :=
  (cr.objRep == .tobj || cr.objRep == .obj) &&
  P.known.natZero != some cr.key && P.known.natSucc != some cr.key &&
  P.known.boolFalse != some cr.key && P.known.boolTrue != some cr.key &&
  match P.ctorInfo? cr.key with
  | some c => cr.nobj + cr.nscalar == c.arity
  | none => false

/-- Check the representation of a right-hand side binding variable `x`. -/
def checkRhs (P : Program) (cert : Cert) (fc : FunCert) (x : Var) (rhs : Fir.Rhs) : Bool :=
  let rx := fc.varRep x
  isValidRep rx &&
  match rhs with
  | .arg a => argCompat fc a rx
  | .ctor c as =>
    (rx == .tobj || rx == .obj) &&
    match cert.ctorRep? c.key with
    | some cr =>
      as.length == cr.arity &&
      argsCompat fc as (List.replicate cr.nobj cr.objRep ++ List.replicate cr.nscalar .word)
    | none =>
      as.all (argCompat fc · .tobj)
  | .proj y c i =>
    let ry := fc.varRep y
    if P.known.natSucc == some c then
      ry == .tobj && (rx == .tobj || rx == .obj)
    else if P.known.natZero == some c then
      false
    else
      (ry == .tobj || ry == .obj) &&
      let fr := cert.fieldRep c i
      match fr, rx with
      | .word, .word => true
      | .word, .obj => true
      | .tobj, .tobj => true
      | .tobj, .obj => true
      | .obj, .obj => true
      | _, _ => false
  | .prim (.word _ _) as =>
    as.all (wordPrimArgOk fc)
  | .prim op as =>
    (rx == .tobj || rx == .obj) &&
    if isCmpPrim op then
      match as with
      | [a, b] =>
        (wordPrimArgOk fc a && wordPrimArgOk fc b) ||
        (argCompat fc a .tobj && argCompat fc b .tobj)
      | _ => false
    else
      as.all (argCompat fc · .tobj)
  | .call g as =>
    decide (g < P.size) &&
    let gc := cert.funCert g
    argsCompat fc as gc.params &&
    match gc.ret, rx with
    | .word, .word => true
    | .word, .obj => true
    | .tobj, .tobj => true
    | .tobj, .obj => true
    | .obj, .obj => true
    | _, _ => false

/-- Check every join-point parameter matches its declared representation in `fc.vars`. -/
def checkParams (fc : FunCert) : List Var → List Fir.Rep → Bool
  | [], [] => true
  | x :: xs, r :: rs => isValidRep r && fc.varRep x == r && checkParams fc xs rs
  | _, _ => false

mutual

def checkCode (P : Program) (cert : Cert) (fc : FunCert) : Code → Bool
  | .bind x rhs k => checkRhs P cert fc x rhs && checkCode P cert fc k
  | .jp j ps _ body k =>
    let jrs := fc.joinReps j
    checkParams fc ps jrs && checkCode P cert fc body && checkCode P cert fc k
  | .jmp j as => argsCompat fc as (fc.joinReps j)
  | .case x alts d =>
    let rx := fc.varRep x
    let isNat := alts.any fun a => P.known.natZero == some a.key || P.known.natSucc == some a.key
    let scrOk := if isNat then rx == .tobj else (rx == .tobj || rx == .obj)
    scrOk && checkAlts P cert fc alts && checkOpt P cert fc d
  | .ret a => argCompat fc a fc.ret
  | .tcall g as =>
    decide (g < P.size) &&
    let gc := cert.funCert g
    argsCompat fc as gc.params && gc.ret == fc.ret
  | .trap => true

def checkAlts (P : Program) (cert : Cert) (fc : FunCert) : List Alt → Bool
  | [] => true
  | .mk _ b :: rest => checkCode P cert fc b && checkAlts P cert fc rest

def checkOpt (P : Program) (cert : Cert) (fc : FunCert) : Option Code → Bool
  | none => true
  | some c => checkCode P cert fc c

end

def checkFun (P : Program) (cert : Cert) (f : FunId) (fd : Fun) : Bool :=
  let fc := cert.funCert f
  isValidRep fc.ret &&
  checkParams fc (fd.params.map (·.1)) fc.params &&
  checkCode P cert fc fd.body

/-- **Kernel-evaluable certificate checker** for Stage W2 representations on `Fir.Program`. -/
def check (P : Program) (cert : Cert) : Bool :=
  cert.ctors.all (checkCtorRep P) &&
  (List.range P.size).all fun f =>
    match P.fun? f with
    | some fd => checkFun P cert f fd
    | none => true

/-! ## Explicit Stage W2 Representation IR (`Rhs.box` / `Rhs.unbox` + `nscalar > 0`) -/

/-- Stage W2 Fir right-hand side with explicit `box` (raw `.word` → 1-scalar-word `.obj` cell),
`unbox` (`.obj`/`.tobj` → raw `.word`), and scalar-tail `CtorInfo` (`nscalar > 0`). -/
inductive RepRhs where
  | arg (a : Arg)
  | box (a : Arg)
  | unbox (a : Arg)
  | ctor (c : CtorInfo) (args : List Arg)
  | proj (x : Var) (c : Key.CtorKey) (i : Nat)
  | prim (op : Lam.Prim) (args : List Arg)
  | call (f : FunId) (args : List Arg)
  deriving DecidableEq, Repr, Inhabited

mutual

inductive RepCode where
  | bind (x : Var) (rhs : RepRhs) (k : RepCode)
  | jp (j : JoinId) (params : List (Var × Fir.Rep)) (rec : Bool) (body k : RepCode)
  | jmp (j : JoinId) (args : List Arg)
  | case (x : Var) (alts : List RepAlt) (dflt : Option RepCode)
  | ret (a : Arg)
  | tcall (f : FunId) (args : List Arg)
  | trap

inductive RepAlt where
  | mk (key : Key.CtorKey) (body : RepCode)

end

deriving instance Repr for RepCode, RepAlt

instance : Inhabited RepCode := ⟨.trap⟩

structure RepFun where
  key : Key.GKey
  params : List (Var × Fir.Rep)
  retRep : Fir.Rep := .tobj
  body : RepCode
  result : Ixon.V3.ResultMode := .shared
  vars : Nat := 0
  joins : Nat := 0
  deriving Inhabited

structure RepProgram where
  funs : Src.NatMap RepFun
  size : Nat
  exports : List FunId
  ctors : List Lam.CtorInfo
  known : Lam.Known
  cert : Cert
  deriving Inhabited

/-- Semantics of `RepRhs`: `box` and `unbox` witness 64-bit word bounds (`n < 2^64`) and are
otherwise the identity on `Fir.Val`. -/
def evalRepRhs (P : Program) (ρ : Env) : RepRhs → Sem.Result Val
  | .arg a => Sem.Result.ofOption (a.eval ρ)
  | .box a =>
    match a.eval ρ with
    | some (.lit (.nat n)) => if n < 2 ^ 64 then .ok (.lit (.nat n)) else .stuck
    | _ => .stuck
  | .unbox a =>
    match a.eval ρ with
    | some (.lit (.nat n)) => if n < 2 ^ 64 then .ok (.lit (.nat n)) else .stuck
    | _ => .stuck
  | .ctor c as =>
    match Fir.evalArgs ρ as with
    | some vs => if vs.length = c.arity then .ok (.ctor c vs) else .stuck
    | none => .stuck
  | .proj x c i =>
    match ρ.get? x with
    | some v =>
      match v.asCtor P.known with
      | some (c', fs) => if c' = c then Sem.Result.ofOption fs[i]? else .stuck
      | none => .stuck
    | none => .stuck
  | .prim op as =>
    match Fir.evalArgs ρ as with
    | some vs => Fir.primResult P op vs
    | none => .stuck
  | .call .. => .stuck

/-! ## Elaboration (`Fir.Program` + `Cert` → `RepProgram` with explicit `box`/`unbox`) -/

/-- State for fresh temporary variables introduced by explicit `box`/`unbox` coercions. -/
structure ElabSt where
  nextVar : Var
  deriving Inhabited

/-- Coerce operand `a` from its representation under `fc` to `expected`, wrapping `k` in a
`.box` or `.unbox` binding when crossing the `.word` ↔ `.obj` boundary. -/
def coerceArg (fc : FunCert) (a : Arg) (expected : Fir.Rep) (next : Var) :
    Arg × Option (Var × RepRhs) × Var :=
  match a, expected with
  | .var y, .obj =>
    if fc.varRep y == .word then (.var next, some (next, .box (.var y)), next + 1)
    else (a, none, next)
  | .var y, .word =>
    if fc.varRep y == .obj || fc.varRep y == .tobj then
      (.var next, some (next, .unbox (.var y)), next + 1)
    else (a, none, next)
  | _, _ => (a, none, next)

def coerceArgs (fc : FunCert) : List Arg → List Fir.Rep → Var →
    List Arg × List (Var × RepRhs) × Var
  | [], _, next => ([], [], next)
  | a :: as, [], next =>
    let (as', bs, next') := coerceArgs fc as [] next
    (a :: as', bs, next')
  | a :: as, r :: rs, next =>
    let (a', b?, next1) := coerceArg fc a r next
    let (as', bs, next2) := coerceArgs fc as rs next1
    let bs' := match b? with | some b => b :: bs | none => bs
    (a' :: as', bs', next2)

def wrapBinds (bs : List (Var × RepRhs)) (k : RepCode) : RepCode :=
  bs.foldr (fun (x, r) acc => .bind x r acc) k

mutual

def elabCode (P : Program) (cert : Cert) (fc : FunCert) (next : Var) : Code → RepCode × Var
  | .bind x rhs k =>
    let rx := fc.varRep x
    let (preBinds, r', postBox, next1) : List (Var × RepRhs) × RepRhs × Bool × Var :=
      match rhs with
      | .arg a =>
        match a, rx with
        | .var y, .obj =>
          if fc.varRep y == .word then ([], .box (.var y), false, next)
          else ([], .arg a, false, next)
        | _, _ => ([], .arg a, false, next)
      | .ctor c as =>
        let c' := (cert.ctorInfo P.ctors c.key).getD c
        let reps := match cert.ctorRep? c.key with
          | some cr => List.replicate cr.nobj cr.objRep ++ List.replicate cr.nscalar .word
          | none => List.replicate as.length .tobj
        let (as', bs, n1) := coerceArgs fc as reps next
        (bs, .ctor c' as', false, n1)
      | .proj y c i =>
        let fr := cert.fieldRep c i
        if fr == .word && rx == .obj then ([], .proj y c i, true, next)
        else ([], .proj y c i, false, next)
      | .prim (.word w op) as =>
        -- Unbox any `.obj`/`.tobj` operands for raw word execution; box output if destination is `.obj`.
        let (as', bs, n1) := coerceArgs fc as (List.replicate as.length .word) next
        (bs, .prim (.word w op) as', rx == .obj, n1)
      | .prim op as =>
        ([], .prim op as, false, next)
      | .call g as =>
        let gc := cert.funCert g
        let (as', bs, n1) := coerceArgs fc as gc.params next
        (bs, .call g as', gc.ret == .word && rx == .obj, n1)
    let (k', next2) := elabCode P cert fc (if postBox then next1 + 1 else next1) k
    if postBox then
      (wrapBinds preBinds (.bind next1 r' (.bind x (.box (.var next1)) k')), next2)
    else
      (wrapBinds preBinds (.bind x r' k'), next2)
  | .jp j ps isRec body k =>
    let jrs := fc.joinReps j
    let psRep := ps.zipIdx.map fun (p, i) => (p, jrs.getD i .tobj)
    let (body', next1) := elabCode P cert fc next body
    let (k', next2) := elabCode P cert fc next1 k
    (.jp j psRep isRec body' k', next2)
  | .jmp j as =>
    let (as', bs, next1) := coerceArgs fc as (fc.joinReps j) next
    (wrapBinds bs (.jmp j as'), next1)
  | .case x alts d =>
    let (alts', next1) := elabAlts P cert fc next alts
    let (d', next2) := elabOpt P cert fc next1 d
    (.case x alts' d', next2)
  | .ret a =>
    let (a', b?, next1) := coerceArg fc a fc.ret next
    let bs := match b? with | some b => [b] | none => []
    (wrapBinds bs (.ret a'), next1)
  | .tcall g as =>
    let gc := cert.funCert g
    let (as', bs, next1) := coerceArgs fc as gc.params next
    (wrapBinds bs (.tcall g as'), next1)
  | .trap => (.trap, next)

def elabAlts (P : Program) (cert : Cert) (fc : FunCert) (next : Var) :
    List Alt → List RepAlt × Var
  | [] => ([], next)
  | .mk k b :: rest =>
    let (b', next1) := elabCode P cert fc next b
    let (rest', next2) := elabAlts P cert fc next1 rest
    (.mk k b' :: rest', next2)

def elabOpt (P : Program) (cert : Cert) (fc : FunCert) (next : Var) :
    Option Code → Option RepCode × Var
  | none => (none, next)
  | some c =>
    let (c', next1) := elabCode P cert fc next c
    (some c', next1)

end

/-- Elaborate a checked `Fir.Program` with `cert` into a `RepProgram` carrying explicit `Rhs.box`
/ `Rhs.unbox` and `CtorInfo.nscalar > 0`. -/
def elaborate (P : Program) (cert : Cert) : RepProgram :=
  let funs := (List.range P.size).foldl (init := Src.NatMap.leaf) fun m f =>
    match P.fun? f with
    | some fd =>
      let fc := cert.funCert f
      let params := fd.params.zipIdx.map fun ((x, _), i) => (x, fc.params.getD i .tobj)
      let (body', vars') := elabCode P cert fc fd.vars fd.body
      m.insert f {
        key := fd.key, params, retRep := fc.ret, body := body',
        result := fd.result, vars := vars', joins := fd.joins
      }
    | none => m
  { funs, size := P.size, exports := P.exports, ctors := P.ctors, known := P.known, cert }

/-- Update `Fun.params` in a `Fir.Program` with the representations from `cert`. -/
def applyParams (P : Program) (cert : Cert) : Program :=
  let funs := (List.range P.size).foldl (init := P.funs) fun m f =>
    match m.get? f with
    | some fd =>
      let fc := cert.funCert f
      let params := fd.params.zipIdx.map fun ((x, _), i) => (x, fc.params.getD i .tobj)
      m.insert f { fd with params }
    | none => m
  { P with funs }

/-! ## Local Representation Inference (kernel-evaluable, D17)

Infers `.word` for variables defined by 64-bit word & limb primitives and propagates `.word`
through pure copies and literals `< 2^64` within each function. The inferred `Cert` is always
validated independently by `check`. -/

/-- Whether a primitive always produces a 64-bit word (`.word` representation candidate). -/
def isWord64Prim : Lam.Prim → Bool
  | .word .w64 op => !op.isDecision && op != .toNat && op.resultWidth .w64 == .w64
  | .word _ (.convert .w64) => true
  | _ => false

mutual

def inferVarsCode (vars : Src.NatMap Fir.Rep) : Code → Src.NatMap Fir.Rep
  | .bind x rhs k =>
    let vars' := match rhs with
      | .prim op _ => if isWord64Prim op then vars.insert x .word else vars
      | .arg (.var y) => if vars.getD y .tobj == .word then vars.insert x .word else vars
      | _ => vars
    inferVarsCode vars' k
  | .jp _ _ _ b k => inferVarsCode (inferVarsCode vars b) k
  | .case _ alts d => inferVarsOpt (inferVarsAlts vars alts) d
  | .jmp .. | .ret _ | .tcall .. | .trap => vars

def inferVarsAlts (vars : Src.NatMap Fir.Rep) : List Alt → Src.NatMap Fir.Rep
  | [] => vars
  | .mk _ b :: rest => inferVarsAlts (inferVarsCode vars b) rest

def inferVarsOpt (vars : Src.NatMap Fir.Rep) : Option Code → Src.NatMap Fir.Rep
  | none => vars
  | some c => inferVarsCode vars c

end

/-- Infer a basic per-function `.word` certificate for `P` (validated with `check`). -/
def infer (P : Program) : Cert :=
  let funs := (List.range P.size).foldl (init := Src.NatMap.leaf) fun m f =>
    match P.fun? f with
    | some fd =>
      let vars0 := inferVarsCode .leaf fd.body
      -- Re-check: drop `.word` on any variable used where `.tobj` is required (conservative fallback
      -- to `.tobj` ensures `checkFun` succeeds; callers can supply richer certs directly).
      let fc : FunCert := {
        params := List.replicate fd.params.length .tobj
        ret := .tobj
        vars := vars0
      }
      if checkFun P { funs := m.insert f fc } f fd then m.insert f fc
      else m.insert f { params := List.replicate fd.params.length .tobj, ret := .tobj }
    | none => m
  { funs, ctors := [] }

/-! ## DR3 Array & ByteArray Certificate Validation and Inference -/

/-- Validate one `ArrayPrimSpec` binding against function `fd` and its `FunCert`. -/
def checkArrayPrimSpec (fd : Fun) (fc : FunCert) (spec : ArrayPrimSpec) : Bool :=
  let arity := fd.params.length
  let inBounds := spec.argIdx.all (· < arity)
  let arityOk :=
    match spec.op with
    | .emptyCap => spec.argIdx.length ≤ 1
    | .size | .pop => spec.argIdx.length == 1
    | .get | .getBang | .push => spec.argIdx.length == 2
    | .set | .extract | .swap => spec.argIdx.length == 3
    | .copySlice => spec.argIdx.length == 5
  let retOk :=
    match spec.op, spec.kind with
    | .get, .limbs => fc.ret == .word || fc.ret == .obj
    | _, _ => fc.ret == .tobj || fc.ret == .obj
  inBounds && arityOk && isValidRep fc.ret && retOk &&
  checkParams fc (fd.params.map (·.1)) fc.params

/-- **DR3 + Stage W2 certificate checker**: validates all constructor scalar-tail overrides,
validates every pinned array/bytearray primitive binding via `checkArrayPrimSpec`, and runs
`checkFun` on every user function outside `cert.arrayPrims`. -/
def checkWithArrays (P : Program) (cert : Cert) : Bool :=
  cert.ctors.all (checkCtorRep P) &&
  (List.range P.size).all fun f =>
    match P.fun? f with
    | some fd =>
      match cert.arrayPrims.get? f with
      | some spec => checkArrayPrimSpec fd (cert.funCert f) spec
      | none => checkFun P cert f fd
    | none => true

/-- Recover the originating `Src.CId` and surviving original parameter positions from a
`Key.GKey`, unwrapping any `Anf.DeadParam` `.worker` masks. -/
def originConstAndPositions (arity : Nat) : Key.GKey → Option (Src.CId × List Nat)
  | .const c _ => some (c, List.range arity)
  | .worker inner keep =>
    match originConstAndPositions keep.length inner with
    | some (c, pos) =>
      let kept := (pos.zip keep).filterMap fun (p, b) => if b then some p else none
      some (c, kept)
    | none => none
  | _ => none

/-- Find the surviving parameter index in `positions` corresponding to original position `orig`. -/
private def findPos? (positions : List Nat) (orig : Nat) : Option Nat :=
  (positions.zipIdx.find? (·.1 == orig)).map (·.2)

/-- Map a pinned Lean 4.34.1 `Array`/`ByteArray` operation and surviving parameter positions
to its `ArrayPrimSpec`. -/
def mkArrayPrimSpec (arrKind : Src.ArrayRepKind) (op : Lam.Erase.Array.PinnedOp)
    (positions : List Nat) : Option ArrayPrimSpec :=
  let get1 (o0 : Nat) := (findPos? positions o0).map fun i0 => [i0]
  let get2 (o0 o1 : Nat) := do
    let i0 ← findPos? positions o0
    let i1 ← findPos? positions o1
    pure [i0, i1]
  let get3 (o0 o1 o2 : Nat) := do
    let i0 ← findPos? positions o0
    let i1 ← findPos? positions o1
    let i2 ← findPos? positions o2
    pure [i0, i1, i2]
  let get5 (o0 o1 o2 o3 o4 : Nat) := do
    let i0 ← findPos? positions o0
    let i1 ← findPos? positions o1
    let i2 ← findPos? positions o2
    let i3 ← findPos? positions o3
    let i4 ← findPos? positions o4
    pure [i0, i1, i2, i3, i4]
  match op with
  -- Array ops (orig param 0 is erased type α)
  | .arr .emptyWithCapacity =>
    some { op := .emptyCap, kind := arrKind, argIdx := (findPos? positions 1).toList }
  | .arr .size => (get1 1).map fun ps => { op := .size, kind := arrKind, argIdx := ps }
  | .arr .getInternal | .arrUget =>
    (get2 1 2).map fun ps => { op := .get, kind := arrKind, argIdx := ps }
  | .arr .set | .arrUset | .arrSetBang | .arr .setIfInBounds =>
    (get3 1 2 3).map fun ps => { op := .set, kind := arrKind, argIdx := ps }
  | .arr .push => (get2 1 2).map fun ps => { op := .push, kind := arrKind, argIdx := ps }
  | .arr .pop => (get1 1).map fun ps => { op := .pop, kind := arrKind, argIdx := ps }
  | .arr .extract => (get3 1 2 3).map fun ps => { op := .extract, kind := arrKind, argIdx := ps }
  | .arr .copySlice =>
    (get5 1 2 3 4 5).map fun ps => { op := .copySlice, kind := arrKind, argIdx := ps }
  | .arr .swap | .arrSwapIfInBounds =>
    (get3 1 2 3).map fun ps => { op := .swap, kind := arrKind, argIdx := ps }
  -- ByteArray ops (monomorphic, no α param)
  | .ba .emptyWithCapacity =>
    some { op := .emptyCap, kind := .bytes, argIdx := (findPos? positions 0).toList }
  | .baEmpty =>
    some { op := .emptyCap, kind := .bytes, argIdx := [] }
  | .ba .size => (get1 0).map fun ps => { op := .size, kind := .bytes, argIdx := ps }
  | .ba .get | .baUget => (get2 0 1).map fun ps => { op := .get, kind := .bytes, argIdx := ps }
  | .baGetBang => (get2 0 1).map fun ps => { op := .getBang, kind := .bytes, argIdx := ps }
  | .ba .set | .baUset | .baSetBang => (get3 0 1 2).map fun ps => { op := .set, kind := .bytes, argIdx := ps }
  | .ba .push => (get2 0 1).map fun ps => { op := .push, kind := .bytes, argIdx := ps }
  | .ba .extract => (get3 0 1 2).map fun ps => { op := .extract, kind := .bytes, argIdx := ps }
  | .ba .copySlice =>
    (get5 0 1 2 3 4).map fun ps => { op := .copySlice, kind := .bytes, argIdx := ps }

/-- Lattice join on `Option Fir.Rep` (`none` = polymorphic bottom `⊥`, e.g., `< 2^63` literals):
`.tobj < .obj` and `.word < .obj`, while `.tobj` and `.word` join to `.obj`. -/
private def repJoinOpt : Option Fir.Rep → Option Fir.Rep → Option Fir.Rep
  | none, r => r
  | r, none => r
  | some r1, some r2 =>
    if r1 == r2 then some r1 else some .obj

private def argRepOpt (vars : Src.NatMap (Option Fir.Rep)) : Arg → Option Fir.Rep
  | .var y => vars.getD y none
  | .lit (.nat n) => if n < 2 ^ 63 then none else some .word
  | .lit (.str _) | .erased => some .tobj

private def isSpecialKey (P : Program) (k : Key.CtorKey) : Bool :=
  P.known.natZero == some k || P.known.natSucc == some k ||
  P.known.boolFalse == some k || P.known.boolTrue == some k

/-- Forward-propagation state for `inferWithArrays` (height-2 monotone lattice). -/
private structure InferState where
  vars : Src.NatMap (Src.NatMap (Option Fir.Rep)) := .leaf
  funParams : Src.NatMap (List (Option Fir.Rep)) := .leaf
  funRet : Src.NatMap (Option Fir.Rep) := .leaf
  objCtors : List Key.CtorKey := []

private def InferState.joinVar (st : InferState) (f : FunId) (x : Var) (r : Option Fir.Rep) : InferState :=
  let vm := st.vars.getD f .leaf
  let cur := vm.getD x none
  let next := repJoinOpt cur r
  if next == cur then st else { st with vars := st.vars.insert f (vm.insert x next) }

private def InferState.joinRet (st : InferState) (f : FunId) (r : Option Fir.Rep) : InferState :=
  let cur := st.funRet.getD f none
  let next := repJoinOpt cur r
  if next == cur then st else { st with funRet := st.funRet.insert f next }

private def InferState.joinParams (st : InferState) (g : FunId) (rs : List (Option Fir.Rep)) : InferState :=
  let cur := st.funParams.getD g (List.replicate rs.length none)
  let next := (cur.zip rs).map fun (a, b) => repJoinOpt a b
  if next == cur then st else { st with funParams := st.funParams.insert g next }

private def InferState.markObjCtor (st : InferState) (P : Program) (k : Key.CtorKey) : InferState :=
  if isSpecialKey P k || st.objCtors.contains k then st
  else { st with objCtors := k :: st.objCtors }

mutual

/-- Collect join-point parameter lists in `c`. -/
private def collectJpParams (jm : Src.NatMap (List Var)) : Code → Src.NatMap (List Var)
  | .bind _ _ k => collectJpParams jm k
  | .jp j ps _ b k => collectJpParams (collectJpParams (jm.insert j ps) b) k
  | .case _ alts d => collectJpParamsOpt (collectJpParamsAlts jm alts) d
  | .jmp .. | .ret _ | .tcall .. | .trap => jm

private def collectJpParamsAlts (jm : Src.NatMap (List Var)) : List Alt → Src.NatMap (List Var)
  | [] => jm
  | .mk _ b :: rest => collectJpParamsAlts (collectJpParams jm b) rest

private def collectJpParamsOpt (jm : Src.NatMap (List Var)) : Option Code → Src.NatMap (List Var)
  | none => jm
  | some c => collectJpParams jm c

end

mutual

/-- One monotone forward-propagation step over `c` inside function `f`. -/
private def propForwardCode (P : Program) (arrayPrims : Src.NatMap ArrayPrimSpec)
    (f : FunId) (jpParams : Src.NatMap (List Var)) (st : InferState) : Code → InferState
  | .bind x rhs k =>
    let vm := st.vars.getD f .leaf
    let st1 := match rhs with
      | .prim op _ =>
        if isWord64Prim op then st.joinVar f x (some .word)
        else st.joinVar f x (some .tobj)
      | .arg a =>
        st.joinVar f x (argRepOpt vm a)
      | .ctor c as =>
        let st' := st.joinVar f x (some .tobj)
        let needsObj := as.any fun a =>
          match argRepOpt vm a with
          | some .word | some .obj => true
          | _ => false
        if needsObj then st'.markObjCtor P c.key else st'
      | .proj _ c _ =>
        if P.known.natSucc == some c then st.joinVar f x (some .tobj)
        else if st.objCtors.contains c then st.joinVar f x (some .obj)
        else st.joinVar f x (some .tobj)
      | .call g as =>
        let argReps := as.map (argRepOpt vm)
        let st' := if (arrayPrims.get? g).isSome then st else st.joinParams g argReps
        let gr := st'.funRet.getD g none
        st'.joinVar f x gr
    propForwardCode P arrayPrims f jpParams st1 k
  | .jp _ _ _ b k =>
    let st1 := propForwardCode P arrayPrims f jpParams st b
    propForwardCode P arrayPrims f jpParams st1 k
  | .jmp j as =>
    let vm := st.vars.getD f .leaf
    let ps := jpParams.getD j []
    (as.zip ps).foldl (init := st) fun acc (a, p) =>
      acc.joinVar f p (argRepOpt vm a)
  | .case _ alts d =>
    let st1 := propForwardAlts P arrayPrims f jpParams st alts
    propForwardOpt P arrayPrims f jpParams st1 d
  | .ret a =>
    let vm := st.vars.getD f .leaf
    st.joinRet f (argRepOpt vm a)
  | .tcall g as =>
    let vm := st.vars.getD f .leaf
    let argReps := as.map (argRepOpt vm)
    let st1 := if (arrayPrims.get? g).isSome then st else st.joinParams g argReps
    let rf := st1.funRet.getD f none
    let rg := st1.funRet.getD g none
    let rBoth := repJoinOpt rf rg
    (st1.joinRet f rBoth).joinRet g rBoth
  | .trap => st

private def propForwardAlts (P : Program) (arrayPrims : Src.NatMap ArrayPrimSpec)
    (f : FunId) (jpParams : Src.NatMap (List Var)) (st : InferState) : List Alt → InferState
  | [] => st
  | .mk _ b :: rest =>
    propForwardAlts P arrayPrims f jpParams (propForwardCode P arrayPrims f jpParams st b) rest

private def propForwardOpt (P : Program) (arrayPrims : Src.NatMap ArrayPrimSpec)
    (f : FunId) (jpParams : Src.NatMap (List Var)) (st : InferState) : Option Code → InferState
  | none => st
  | some c => propForwardCode P arrayPrims f jpParams st c

end

mutual

/-- Build join-point representation map from final resolved `vars` (defaulting `none` → `.tobj`). -/
private def buildJoinsCode (vars : Src.NatMap Fir.Rep) (jm : Src.NatMap (List Fir.Rep)) :
    Code → Src.NatMap (List Fir.Rep)
  | .bind _ _ k => buildJoinsCode vars jm k
  | .jp j ps _ b k =>
    let rs := ps.map fun v => vars.getD v .tobj
    buildJoinsCode vars (buildJoinsCode vars (jm.insert j rs) b) k
  | .case _ alts d => buildJoinsOpt vars (buildJoinsAlts vars jm alts) d
  | .jmp .. | .ret _ | .tcall .. | .trap => jm

private def buildJoinsAlts (vars : Src.NatMap Fir.Rep) (jm : Src.NatMap (List Fir.Rep)) :
    List Alt → Src.NatMap (List Fir.Rep)
  | [] => jm
  | .mk _ b :: rest => buildJoinsAlts vars (buildJoinsCode vars jm b) rest

private def buildJoinsOpt (vars : Src.NatMap Fir.Rep) (jm : Src.NatMap (List Fir.Rep)) :
    Option Code → Src.NatMap (List Fir.Rep)
  | none => jm
  | some c => buildJoinsCode vars jm c

end

/-- Infer a checked DR3 + Stage W2 `Cert` for `P` from `Lam.Erase.Array.ArrayEraseInfo`:
* binds every surviving pinned `Array`/`ByteArray` global (including `.worker`s from
  `Anf.DeadParam`) to its native `ArrayPrimSpec`;
* records `arrayMkKey`, `byteArrayMkKey`, `listNilTag`, `listConsTag`;
* for `Array UInt64` (`.limbs`), runs a forward monotone fixed-point over `{⊥ < .tobj, .word < .obj}`
  so 64-bit limbs stay raw `.word` (unboxed in registers and `LimbArray`), containers holding limbs
  receive `objRep := .obj`, and `Nat` arithmetic/indices stay `.tobj` without spurious boxing;
* always produces a certificate validated by `checkWithArrays`. -/
def inferWithArrays (P : Program) (info : Lam.Erase.Array.ArrayEraseInfo) : Cert :=
  -- 1. Identify all pinned array/bytearray primitives in P.
  let arrayPrims : Src.NatMap ArrayPrimSpec :=
    (List.range P.size).foldl (init := .leaf) fun m f =>
      match P.fun? f with
      | some fd =>
        match originConstAndPositions fd.params.length fd.key with
        | some (c, positions) =>
          match Lam.Erase.Array.pinnedOpOf info.ops c with
          | some pinOp =>
            match mkArrayPrimSpec info.arrayKind pinOp positions with
            | some spec => m.insert f spec
            | none => m
          | none => m
        | none => m
      | none => m
  -- 2. Resolve List.nil / List.cons tags for List <-> Array bridges.
  let listNilTag := (info.listNilKey.bind (CtorInfo.ofKey P.ctors)).map (·.tag) |>.getD 0
  let listConsTag := (info.listConsKey.bind (CtorInfo.ofKey P.ctors)).map (·.tag) |>.getD 1
  let hasArrMk := info.arrayMkKey.any fun k => (CtorInfo.ofKey P.ctors k).isSome
  let hasBaMk := info.byteArrayMkKey.any fun k => (CtorInfo.ofKey P.ctors k).isSome
  let useObj := info.arrayKind == .limbs
  if !useObj then
    -- Fast path for boxed `Array α` / `ByteArray` closures: all `.tobj`.
    let funs := (List.range P.size).foldl (init := Src.NatMap.leaf) fun m f =>
      match P.fun? f with
      | some fd =>
        let joins := buildJoinsCode .leaf .leaf fd.body
        m.insert f { params := List.replicate fd.params.length .tobj, ret := .tobj, joins }
      | none => m
    { funs
      ctors := []
      arrayPrims
      arrayMkKey := if hasArrMk then info.arrayMkKey else none
      arrayMkKind := info.arrayKind
      byteArrayMkKey := if hasBaMk then info.byteArrayMkKey else none
      listNilTag
      listConsTag }
  else
    -- 3. Collect join-point param lists per function and seed `InferState`.
    let jpMap : Src.NatMap (Src.NatMap (List Var)) :=
      (List.range P.size).foldl (init := .leaf) fun m f =>
        match P.fun? f with
        | some fd => m.insert f (collectJpParams .leaf fd.body)
        | none => m
    let st0 : InferState :=
      (List.range P.size).foldl (init := {}) fun st f =>
        match P.fun? f with
        | some fd =>
          match arrayPrims.get? f with
          | some spec =>
            let pReps : List (Option Fir.Rep) := List.replicate fd.params.length (some .obj)
            let rRep : Option Fir.Rep :=
              if spec.op == .get && spec.kind == .limbs then some .word else some .tobj
            let vm := (fd.params.zip pReps).foldl (init := Src.NatMap.leaf) fun acc ((v, _), r) =>
              acc.insert v r
            { st with
              vars := st.vars.insert f vm
              funParams := st.funParams.insert f pReps
              funRet := st.funRet.insert f rRep }
          | none =>
            let pReps : List (Option Fir.Rep) := List.replicate fd.params.length none
            { st with
              funParams := st.funParams.insert f pReps
              funRet := st.funRet.insert f none }
        | none => st
    -- 4. Run monotone forward fixed-point (16 rounds).
    let stepOnce (st : InferState) : InferState :=
      (List.range P.size).foldl (init := st) fun acc f =>
        match P.fun? f with
        | some fd =>
          if (arrayPrims.get? f).isSome then acc
          else
            -- Sync function parameter vars from `funParams[f]`.
            let ps := acc.funParams.getD f (List.replicate fd.params.length none)
            let acc1 := (fd.params.zip ps).foldl (init := acc) fun s ((v, _), r) =>
              s.joinVar f v r
            propForwardCode P arrayPrims f (jpMap.getD f .leaf) acc1 fd.body
        | none => acc
    let stFinal := (List.range 16).foldl (fun s _ => stepOnce s) st0
    -- 5. Materialize final `CtorRep`s and `FunCert`s (defaulting `none` → `.tobj`).
    let ctors : List CtorRep :=
      P.ctors.filterMap fun ci =>
        if stFinal.objCtors.contains ci.key && !isSpecialKey P ci.key then
          some { key := ci.key, nobj := ci.arity, nscalar := 0, objRep := .obj }
        else none
    let funs : Src.NatMap FunCert :=
      (List.range P.size).foldl (init := .leaf) fun m f =>
        match P.fun? f with
        | some fd =>
          let vmOpt := stFinal.vars.getD f .leaf
          let vm : Src.NatMap Fir.Rep :=
            vmOpt.toList.foldl (init := .leaf) fun acc (v, rOpt) =>
              acc.insert v (rOpt.getD .tobj)
          let pReps : List Fir.Rep :=
            match arrayPrims.get? f with
            | some _ => List.replicate fd.params.length .obj
            | none => (stFinal.funParams.getD f (List.replicate fd.params.length none)).map (·.getD .tobj)
          let vmWithParams : Src.NatMap Fir.Rep :=
            (fd.params.zip pReps).foldl (init := vm) fun acc ((v, _), r) => acc.insert v r
          let retRep : Fir.Rep := (stFinal.funRet.getD f none).getD .tobj
          let joins := buildJoinsCode vmWithParams .leaf fd.body
          m.insert f { params := pReps, ret := retRep, vars := vmWithParams, joins }
        | none => m
    { funs
      ctors
      arrayPrims
      arrayMkKey := if hasArrMk then info.arrayMkKey else none
      arrayMkKind := info.arrayKind
      byteArrayMkKey := if hasBaMk then info.byteArrayMkKey else none
      listNilTag
      listConsTag }

end IxCC.Fir.Rep
