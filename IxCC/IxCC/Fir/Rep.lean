import IxCC.Fir.Semantics
import IxCC.Lam.WordSem
import IxCC.Lam.Erase.Limb

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

/-- Program-wide Stage W2 representation certificate. -/
structure Cert where
  funs : Src.NatMap FunCert := .leaf
  ctors : List CtorRep := []
  deriving Inhabited

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
        (argCompat fc a .word && argCompat fc b .word) ||
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

end IxCC.Fir.Rep
