import IxCCAiur.InlineFuse
import IxCCAiur.TypedLower
import IxCCAiur.TypedWorld
import IxCCAiur.CompiledCert
import IxCCAiur.Hints
import IxCCAiur.ScheduleJson
import Aiur.Library.Field
import Aiur.Library.U32.Goldilocks
import Aiur.Library.Field.BN254
import Aiur.Library.Field.BLS12381.Prime
import Aiur.Trace.Export
import Aiur.Artifact

/-! # Phase 3.4 Certified Ambient-Field Lowering (`IxCCAiur.FieldLower`)

Lowers ambient prime-field operations in `TypedLower` (`Prog`) programs directly
to native Formal Aiur `Field` arithmetic over any prime modulus `p` (`Goldilocks`,
`BN254` `Fr`, `BLS12-381` `Fr`, or arbitrary `[Fact (Nat.Prime p)]`):

1. **Intrinsic binding & canonical mod-`p` helper recognition (`lowerFieldOps`)**:
   - Honors explicit `@[circuit_intrinsic "field.{add,sub,mul,neg,inv,div,is_zero,eq}"]`
     directives exported in `"ixcc/circuit-schedule/1"` JSON sidecars.
   - Automatically recognizes canonical modular arithmetic helpers whose lowered
     `Lower.Fn` bodies implement `(a + b) % p`, `(a + p - b) % p`, `(a * b) % p`,
     `(p - a) % p`, `if a == 0 then 0 else p - a`, `a == 0`, or `a == b`.
   - Replaces each ambient-field operation with zero-lookup native Formal Aiur
     arithmetic (`a + b`, `a - b`, `a * b`, `0 - a`, total
     `match Fields::is_zero(a) { 1 => 0, _ => 1 / a }` matching Lean's `0⁻¹ = 0`,
     `Fields::is_zero(a)`, `Fields::is_zero(a - b)`).
2. **Range-check elimination, constant-helper folding, dead-helper pruning &
   `TableTier.none` downgrade**:
   - Eliminates redundant `check_u56` wrappers inside pure ambient-field
     expressions and entrypoints.
   - Constant-folds literal `check_u56`, `sub_borrow_56`, `mul_56`, and
     `divmod_56` calls.
   - Prunes dead arithmetic helpers via `InlineFuse.pruneUnreachable` and
     downgrades `TableTier` to `.none` (**0 fixed table rows!**) whenever no
     byte/word operations remain.
3. **3-field linker & packager (`linkedProgramFor`, `compileForField`)**:
   - Prepares, optimizes, exports trace plans, and packages `.ixa` artifacts over
     **Goldilocks (`p_G`)**, **BN254 (`Fr`)**, or **BLS12-381 (`Fr`)**, linking
     `Aiur.Library.Field.declarations` (`Fields::is_zero`, 0 tables) on demand.
4. **Plainness preservation**: proves `Lower.isPlainExpr = true` is preserved by
   every lowered field expression and program transformation.

Strictly total (zero `partial`), zero `sorry`, zero `native_decide`, zero `bv_decide`. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.FieldLower

open IxCC.AiurBackend.Lower
  (Ty Expr Pat Fn natLimit moduleName qualified funName entryName
   vE litE letE matchE callE isPlainExpr isPlainList isPlainArms)
open IxCC.AiurBackend.TypedRep (TableTier)
open IxCC.AiurBackend.TypedLower (LoweredProgram)
open IxCC.AiurBackend.InlineFuse (callsAny pruneUnreachable)

/-! ## Target Prime Moduli -/

/-- Goldilocks 64-bit prime `2^64 - 2^32 + 1`. -/
abbrev goldilocksModulus : Nat := Aiur.Library.U32.Goldilocks.modulus

/-- BN254 scalar field prime `Fr`. -/
abbrev bn254Modulus : Nat := Aiur.Library.Field.BN254.modulus

/-- BLS12-381 scalar field prime `Fr`. -/
abbrev bls12381Modulus : Nat := Aiur.Library.Field.BLS12381.modulus

/-! ## Native Ambient-Field Operations & Bindings -/

/-- Native ambient prime-field operations lowered to Formal Aiur `Field` ops. -/
inductive FieldOp where
  | add
  | sub
  | mul
  | neg
  | inv
  | div
  | isZero
  | eq
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Parse an `@[circuit_intrinsic "..."]` name into a native `FieldOp`. -/
def FieldOp.ofIntrinsicName? : String → Option FieldOp
  | "field.add" => some .add
  | "field.sub" => some .sub
  | "field.mul" => some .mul
  | "field.neg" => some .neg
  | "field.inv" => some .inv
  | "field.div" => some .div
  | "field.is_zero" => some .isZero
  | "field.eq" => some .eq
  | _ => none

/-- Canonical `@[circuit_intrinsic "..."]` name of a `FieldOp`. -/
def FieldOp.intrinsicName : FieldOp → String
  | .add => "field.add"
  | .sub => "field.sub"
  | .mul => "field.mul"
  | .neg => "field.neg"
  | .inv => "field.inv"
  | .div => "field.div"
  | .isZero => "field.is_zero"
  | .eq => "field.eq"

/-- Operand arity of a `FieldOp` (excluding an optional leading modulus parameter). -/
def FieldOp.arity : FieldOp → Nat
  | .add | .sub | .mul | .div | .eq => 2
  | .neg | .inv | .isZero => 1

/-- Semantic denotation of a `FieldOp` in an arbitrary field `F` (with Lean's
total inverse convention `0⁻¹ = 0` and `a / 0 = 0`). -/
def FieldOp.eval {F : Type} [Field F] [DecidableEq F] : FieldOp → List F → Option F
  | .add, [a, b] => some (a + b)
  | .sub, [a, b] => some (a - b)
  | .mul, [a, b] => some (a * b)
  | .neg, [a] => some (0 - a)
  | .inv, [a] => some a⁻¹
  | .div, [a, b] => some (a / b)
  | .isZero, [a] => some (if a = 0 then 1 else 0)
  | .eq, [a, b] => some (if a = b then 1 else 0)
  | _, _ => none

/-- Binding of a lowered `Prog` function `fnName` to a native `FieldOp`.
When `dropFirstParam = true`, parameter 0 is the prime modulus `p` (as in
`addMod (p a b : Nat)`); when `false`, all parameters are field operands. -/
structure FieldBinding where
  fnName : String
  op : FieldOp
  dropFirstParam : Bool := false
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Expected total parameter count of `b` (operands + optional leading modulus). -/
def FieldBinding.paramCount (b : FieldBinding) : Nat :=
  if b.dropFirstParam then b.op.arity + 1 else b.op.arity

/-! ## Native Formal Aiur `Field` Expression Builders -/

/-- Native field addition `a + b` (0 lookups, degree 1). -/
def fieldAddE (a b : Expr) : Expr := .binary .add a b

/-- Native field subtraction `a - b` (0 lookups, degree 1). -/
def fieldSubE (a b : Expr) : Expr := .binary .sub a b

/-- Native field multiplication `a * b` (0 lookups, degree 2). -/
def fieldMulE (a b : Expr) : Expr := .binary .mul a b

/-- Native field negation `0 - a` (0 lookups, degree 1). -/
def fieldNegE (a : Expr) : Expr := .binary .sub (litE 0) a

/-- Native zero-test `Fields::is_zero(a)` (returns `1` iff `a = 0`, else `0`). -/
def fieldIsZeroE (a : Expr) : Expr := callE "Fields::is_zero" [a]

/-- Native field equality indicator `Fields::is_zero(a - b)` (`1` iff `a = b`, else `0`). -/
def fieldEqE (a b : Expr) : Expr := callE "Fields::is_zero" [.binary .sub a b]

/-- Total native field inverse on bound variable `v`: `match Fields::is_zero(v) { 1 => 0, _ => 1 / v }`.
Matches Lean's total `0⁻¹ = 0` convention using a single `inv` constraint and 0 loops. -/
def fieldInvVarE (v : String) : Expr :=
  matchE (fieldIsZeroE (vE v))
    [(.literal 1, litE 0),
     (.wildcard, .binary .div (litE 1) (vE v))]

/-- Total native field inverse on an arbitrary expression `a`, evaluating `a` once. -/
def fieldInvE (a : Expr) : Expr :=
  letE "_fi_x" a (fieldInvVarE "_fi_x")

/-- Total native field division on bound variables `a, b`:
`match Fields::is_zero(b) { 1 => 0 * a, _ => a / b }`.
Evaluating `0 * a` on the zero-divisor arm ensures `a` is a `.field` value
with zero lookup cost and returns `0 = a / 0`. -/
def fieldDivVarsE (a b : String) : Expr :=
  matchE (fieldIsZeroE (vE b))
    [(.literal 1, fieldMulE (litE 0) (vE a)),
     (.wildcard, .binary .div (vE a) (vE b))]

/-- Total native field division on arbitrary expressions `a, b`, evaluating both
in the outer lexical scope (capture-free) before binding. -/
def fieldDivE (a b : Expr) : Expr :=
  .letValue (.tuple [.bind "_fi_a", .bind "_fi_b"]) (.tuple [a, b])
    (fieldDivVarsE "_fi_a" "_fi_b")

/-- Native function body for `op` given the operand parameter names. -/
def fieldOpBody : FieldOp → List String → Option Expr
  | .add, [a, b] => some (fieldAddE (vE a) (vE b))
  | .sub, [a, b] => some (fieldSubE (vE a) (vE b))
  | .mul, [a, b] => some (fieldMulE (vE a) (vE b))
  | .neg, [a] => some (fieldNegE (vE a))
  | .inv, [a] => some (fieldInvVarE a)
  | .div, [a, b] => some (fieldDivVarsE a b)
  | .isZero, [a] => some (fieldIsZeroE (vE a))
  | .eq, [a, b] => some (fieldEqE (vE a) (vE b))
  | _, _ => none

/-- Native inline expression for `op` given operand expressions. -/
def fieldOpExpr : FieldOp → List Expr → Option Expr
  | .add, [a, b] => some (fieldAddE a b)
  | .sub, [a, b] => some (fieldSubE a b)
  | .mul, [a, b] => some (fieldMulE a b)
  | .neg, [a] => some (fieldNegE a)
  | .inv, [a] => some (fieldInvE a)
  | .div, [a, b] => some (fieldDivE a b)
  | .isZero, [a] => some (fieldIsZeroE a)
  | .eq, [a, b] => some (fieldEqE a b)
  | _, _ => none

/-! ## Canonical Mod-`p` Helper Recognition (`recognizeFieldOpFn`) -/

/-- Lightweight symbolic view of straight-line `TypedLower` arithmetic bodies,
used strictly for read-only recognition of canonical mod-`p` helpers. -/
private inductive SymExpr where
  | var (name : String)
  | lit (n : Nat)
  | add (a b : SymExpr)
  | sub (a b : SymExpr)
  | mul (a b : SymExpr)
  | mod (a m : SymExpr)
  | eqZero (a : SymExpr)
  | eqNat (a b : SymExpr)
  | ite (c t e : SymExpr)
  | ctor (name : String)
  | other
  deriving BEq, DecidableEq, Repr

private def toSymExpr (env : List (String × SymExpr)) : Expr → SymExpr
  | .var x => (env.lookup x).getD (.var x)
  | .literal n => .lit n
  | .construct _ _ nm [] => .ctor nm
  | .binary .add a b => .add (toSymExpr env a) (toSymExpr env b)
  | .binary .sub a b => .sub (toSymExpr env a) (toSymExpr env b)
  | .binary .mul a b => .mul (toSymExpr env a) (toSymExpr env b)
  | .call "mul_56" (some []) [a, b] => .mul (toSymExpr env a) (toSymExpr env b)
  | .project (.call "sub_borrow_56" (some []) [a, b]) 0 =>
    .sub (toSymExpr env a) (toSymExpr env b)
  | .project (.call "divmod_56" (some []) [a, m]) 1 =>
    .mod (toSymExpr env a) (toSymExpr env m)
  | .letValue .wildcard (.call "check_u56" (some []) [_]) b =>
    toSymExpr env b
  | .letValue (.bind v) rhs b =>
    toSymExpr ((v, toSymExpr env rhs) :: env) b
  | .matchValue scrut [(.literal 0, e0), (.wildcard, e1)] =>
    let s := toSymExpr env scrut
    let t := toSymExpr env e0
    let f := toSymExpr env e1
    match f with
    | .mod a m =>
      if s == m && t == a then .mod a m
      else .ite (.eqZero s) t f
    | _ =>
      match s with
      | .sub a (.lit 0) => .ite (.eqZero a) t f
      | .sub a b => .ite (.eqNat a b) t f
      | _ => .ite (.eqZero s) t f
  | .matchValue scrut [(.construct _ c1 [], e1), (.construct _ c2 [], e2)] =>
    match toSymExpr env scrut with
    | .ite cond (.ctor ct) (.ctor cf) =>
      if c1 == ct && c2 == cf then .ite cond (toSymExpr env e1) (toSymExpr env e2)
      else if c1 == cf && c2 == ct then .ite cond (toSymExpr env e2) (toSymExpr env e1)
      else .other
    | _ => .other
  | _ => .other

private def matchAddSym (a b : SymExpr) : SymExpr → Bool
  | .add x y => (x == a && y == b) || (x == b && y == a)
  | _ => false

private def matchMulSym (a b : SymExpr) : SymExpr → Bool
  | .mul x y => (x == a && y == b) || (x == b && y == a)
  | _ => false

private def matchEqZeroSym (a : SymExpr) : SymExpr → Bool
  | .eqZero x => x == a
  | .eqNat x (.lit 0) | .eqNat (.lit 0) x => x == a
  | _ => false

private def matchEqNatSym (a b : SymExpr) : SymExpr → Bool
  | .eqNat x y => (x == a && y == b) || (x == b && y == a)
  | _ => false

private def classifyMod2 (m a b : SymExpr) (s : SymExpr) : Option FieldOp :=
  match s with
  | .mod inner m' =>
    if m' != m then none
    else if matchAddSym a b inner then some .add
    else if matchMulSym a b inner then some .mul
    else match inner with
      | .sub lhs b' =>
        if b' == b && matchAddSym a m lhs then some .sub else none
      | _ => none
  | _ => none

private def classifyMod1 (m a : SymExpr) (s : SymExpr) : Option FieldOp :=
  match s with
  | .mod (.sub m1 a1) m2 =>
    if m1 == m && m2 == m && a1 == a then some .neg else none
  | .ite cond (.lit 0) (.sub m1 a1) =>
    if matchEqZeroSym a cond && m1 == m && a1 == a then some .neg else none
  | _ => none

/-- True iff `f` is monomorphic with all `.field` parameters and `.field` result. -/
def allFieldParams (f : Fn) : Bool :=
  f.typeParams.isEmpty && f.result == .field && f.params.all (fun p => p.2 == .field)

/-- Inspect a lowered `Lower.Fn` body and recognize canonical modular field
operations:
* When `recognizeConstMod = true`: recognizes 1- and 2-argument helpers whose
  modulus literal equals `ambientModulus` (`(a + b) % p`, `(a + p - b) % p`,
  `(a * b) % p`, `(p - a) % p`, `if a == 0 then 0 else p - a`, `a == 0`, `a == b`).
* When `recognizeParamMod = true`: also recognizes parametric-modulus helpers
  `(p, a, b) ↦ (a + b) % p`, `(a + p - b) % p`, `(a * b) % p`, and
  `(p, a) ↦ (p - a) % p` / `if a == 0 then 0 else p - a`. -/
def recognizeFieldOpFn (ambientModulus : Nat) (recognizeConstMod recognizeParamMod : Bool)
    (f : Fn) : Option FieldBinding :=
  if !allFieldParams f then none
  else
    let sym := toSymExpr [] f.body
    match f.params.map Prod.fst with
    | [a] =>
      if !recognizeConstMod then none
      else
        match classifyMod1 (.lit ambientModulus) (.var a) sym with
        | some op => some { fnName := f.name, op, dropFirstParam := false }
        | none =>
          match sym with
          | .ite cond (.lit 1) (.lit 0) =>
            if matchEqZeroSym (.var a) cond then
              some { fnName := f.name, op := .isZero, dropFirstParam := false }
            else none
          | _ => none
    | [a, b] =>
      let constHit :=
        if !recognizeConstMod then none
        else
          match classifyMod2 (.lit ambientModulus) (.var a) (.var b) sym with
          | some op => some { fnName := f.name, op, dropFirstParam := false }
          | none =>
            match sym with
            | .ite cond (.lit 1) (.lit 0) =>
              if matchEqNatSym (.var a) (.var b) cond then
                some { fnName := f.name, op := .eq, dropFirstParam := false }
              else none
            | _ => none
      match constHit with
      | some hit => some hit
      | none =>
        if !recognizeParamMod then none
        else
          match classifyMod1 (.var a) (.var b) sym with
          | some op => some { fnName := f.name, op, dropFirstParam := true }
          | none => none
    | [p, a, b] =>
      if !recognizeParamMod then none
      else
        match classifyMod2 (.var p) (.var a) (.var b) sym with
        | some op => some { fnName := f.name, op, dropFirstParam := true }
        | none => none
    | _ => none

/-! ## Ambient-Field Lowering Configuration & Pass (`lowerFieldOps`) -/

/-- Configuration for `FieldLower.lowerFieldOps` and `FieldLower.lowerProgram`. -/
structure Config where
  /-- Ambient prime modulus `p` (e.g. Goldilocks, BN254 `Fr`, BLS12-381 `Fr`). -/
  ambientModulus : Nat := goldilocksModulus
  /-- Explicit function bindings (e.g. resolved from `@[circuit_intrinsic "field.*"]`). -/
  bindings : List FieldBinding := []
  /-- Automatically recognize constant-modulus `(a op b) % ambientModulus` helpers. -/
  recognizeConstMod : Bool := true
  /-- Automatically recognize parametric-modulus `(p, a, b) ↦ (a op b) % p` helpers. -/
  recognizeParamMod : Bool := false
  /-- Inline bound field-op calls directly into callers (`a + b`, `a * b`, …). -/
  inlineFieldOps : Bool := true
  /-- Strip redundant `check_u56` wrappers inside pure ambient-field expressions. -/
  stripCheckU56 : Bool := true
  /-- Constant-fold literal `check_u56` / `sub_borrow_56` / `mul_56` / `divmod_56` calls. -/
  foldConstHelpers : Bool := true
  /-- Optional list of root function names for dead-helper pruning via `pruneUnreachable`. -/
  pruneRoots : Option (List String) := none
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Collect effective `FieldBinding`s for `fns`: explicit `cfg.bindings` followed
by automatically recognized modular field helpers. -/
def effectiveBindings (cfg : Config) (fns : List Fn) : List FieldBinding :=
  let auto := fns.filterMap fun f =>
    if cfg.bindings.any (·.fnName == f.name) then none
    else recognizeFieldOpFn cfg.ambientModulus cfg.recognizeConstMod cfg.recognizeParamMod f
  cfg.bindings ++ auto

/-! ### Factored Local Rewrite Steps (Clean Non-Overlapping Dispatch) -/

/-- Constant-fold literal calls to 56-bit arithmetic helpers (`check_u56`,
`sub_borrow_56`, `mul_56`, `divmod_56`). -/
def foldConstCall (foldConst : Bool) (nm : String) (targs : Option (List Ty))
    (xs : List Expr) : Option Expr :=
  if foldConst && targs == some [] then
    match nm, xs with
    | "check_u56", [.literal n] =>
      if n < natLimit then some (.tuple []) else none
    | "sub_borrow_56", [.literal a, .literal b] =>
      if a < natLimit && b < natLimit then
        some (.tuple [.literal (a - b), .literal (if a ≥ b then 1 else 0)])
      else none
    | "mul_56", [.literal a, .literal b] =>
      if a < natLimit && b < natLimit && a * b < natLimit then
        some (.literal (a * b))
      else none
    | "divmod_56", [.literal a, .literal b] =>
      if a < natLimit && b < natLimit && 0 < b then
        some (.tuple [.literal (a / b), .literal (a % b)])
      else none
    | _, _ => none
  else none

/-- Local call-site rewriter: constant-folds literal 56-bit helpers (matching original
literal arguments for direct backward simulation) and inlines bound native `FieldOp` calls. -/
def lowerCall (bindings : List FieldBinding) (inlineFieldOps foldConst : Bool)
    (nm : String) (targs : Option (List Ty)) (xs xs' : List Expr) : Expr :=
  match foldConstCall foldConst nm targs xs with
  | some e => e
  | none =>
    if inlineFieldOps && targs == some [] then
      match bindings.find? (·.fnName == nm) with
      | some b =>
        if !b.dropFirstParam then
          (fieldOpExpr b.op xs').getD (.call nm targs xs')
        else
          match xs, xs' with
          | .literal _ :: _, _ :: rest' => (fieldOpExpr b.op rest').getD (.call nm targs xs')
          | _, _ => .call nm targs xs'
      | none => .call nm targs xs'
    else .call nm targs xs'

/-- Local projection rewriter: collapses projections of constant 56-bit helper calls
(`sub_borrow_56(lit a, lit b).0/1`, `divmod_56(lit a, lit b).0/1`) and literal pairs. -/
def lowerProject (foldConst : Bool) (x x' : Expr) (i : Nat) : Expr :=
  if foldConst then
    match x, i with
    | .call "sub_borrow_56" (some []) [.literal a, .literal b], 0 =>
      if a < natLimit && b < natLimit then .literal (a - b) else .project x' i
    | .call "sub_borrow_56" (some []) [.literal a, .literal b], 1 =>
      if a < natLimit && b < natLimit then .literal (if a ≥ b then 1 else 0) else .project x' i
    | .call "divmod_56" (some []) [.literal a, .literal b], 0 =>
      if a < natLimit && b < natLimit && 0 < b then .literal (a / b) else .project x' i
    | .call "divmod_56" (some []) [.literal a, .literal b], 1 =>
      if a < natLimit && b < natLimit && 0 < b then .literal (a % b) else .project x' i
    | .tuple [.literal a, .literal _], 0 => .literal a
    | .tuple [.literal _, .literal b], 1 => .literal b
    | _, _ => .project x' i
  else .project x' i

/-- Local `letValue` rewriter: strips redundant `check_u56` wrappers and eta-reduces
trivial `let v := rhs'; v` bindings. -/
def lowerLetValue (stripCheckU56 foldConst : Bool) (p : Pat) (x x' b' : Expr) : Expr :=
  match p, x, x', b' with
  | .wildcard, .call "check_u56" (some []) [.var v], _, .var v' =>
    if stripCheckU56 && v == v' then .var v
    else .letValue p x' b'
  | .wildcard, .call "check_u56" (some []) [.literal n], _, body =>
    if (stripCheckU56 || foldConst) && n < natLimit then body
    else .letValue p x' b'
  | .wildcard, .tuple [], _, body =>
    if stripCheckU56 || foldConst then body
    else .letValue p x' b'
  | .bind v, _, rhs, .letValue .wildcard (.call "check_u56" (some []) [.var v']) body =>
    if stripCheckU56 && v == v' then
      match body with
      | .var w => if w == v then rhs else .letValue (.bind v) rhs body
      | _ => .letValue (.bind v) rhs body
    else .letValue p x' b'
  | .bind v, _, rhs, .var w =>
    if stripCheckU56 && v == w then rhs
    else .letValue p x' b'
  | _, _, _, _ => .letValue p x' b'

/-- Local `matchValue` rewriter: constant-folds literal-discriminant
`match (lit n) { 0 => e0, _ => e1 }` whenever `n < ambientModulus`. -/
def lowerMatchValue (ambientModulus : Nat) (foldConst : Bool)
    (s s' : Expr) (arms' : List (Pat × Expr)) : Expr :=
  if foldConst then
    match s, arms' with
    | .literal n, [(.literal 0, e0), (.wildcard, e1)] =>
      if n == 0 then e0
      else if n < ambientModulus then e1
      else .matchValue s' arms'
    | _, _ => .matchValue s' arms'
  else .matchValue s' arms'

mutual

/-- Strictly structural bottom-up ambient-field expression rewriter (exactly one
equation per `Expr` constructor). -/
def lowerFieldExpr (ambientModulus : Nat) (bindings : List FieldBinding)
    (inlineFieldOps stripCheckU56 foldConst : Bool) : Expr → Expr
  | .call nm targs xs =>
    let xs' := lowerFieldExprList ambientModulus bindings inlineFieldOps stripCheckU56 foldConst xs
    lowerCall bindings inlineFieldOps foldConst nm targs xs xs'
  | .project x i =>
    let x' := lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst x
    lowerProject foldConst x x' i
  | .letValue p x b =>
    let x' := lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst x
    let b' := lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst b
    lowerLetValue stripCheckU56 foldConst p x x' b'
  | .matchValue s arms =>
    let s' := lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst s
    let arms' := lowerFieldArms ambientModulus bindings inlineFieldOps stripCheckU56 foldConst arms
    lowerMatchValue ambientModulus foldConst s s' arms'
  | .tuple xs =>
    .tuple (lowerFieldExprList ambientModulus bindings inlineFieldOps stripCheckU56 foldConst xs)
  | .array xs =>
    .array (lowerFieldExprList ambientModulus bindings inlineFieldOps stripCheckU56 foldConst xs)
  | .construct ty targs nm xs =>
    .construct ty targs nm
      (lowerFieldExprList ambientModulus bindings inlineFieldOps stripCheckU56 foldConst xs)
  | .constructAs ty targs nm xs =>
    .constructAs ty targs nm
      (lowerFieldExprList ambientModulus bindings inlineFieldOps stripCheckU56 foldConst xs)
  | .record ty fs =>
    .record ty
      (lowerFieldExprList ambientModulus bindings inlineFieldOps stripCheckU56 foldConst fs)
  | .update ty fs =>
    .update ty
      (lowerFieldExprList ambientModulus bindings inlineFieldOps stripCheckU56 foldConst fs)
  | .builtin op xs =>
    .builtin op
      (lowerFieldExprList ambientModulus bindings inlineFieldOps stripCheckU56 foldConst xs)
  | .repeat x n =>
    .repeat (lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst x) n
  | .index x i =>
    .index (lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst x) i
  | .slice x a b =>
    .slice (lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst x) a b
  | .member x f =>
    .member (lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst x) f
  | .store x =>
    .store (lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst x)
  | .load x =>
    .load (lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst x)
  | .hint ty x ch =>
    .hint ty (lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst x) ch
  | .neg x =>
    .neg (lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst x)
  | .binary op x y =>
    .binary op
      (lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst x)
      (lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst y)
  | .literal n => .literal n
  | .var x => .var x
  | .global nm targs => .global nm targs
  | .control c e => .control c e

def lowerFieldExprList (ambientModulus : Nat) (bindings : List FieldBinding)
    (inlineFieldOps stripCheckU56 foldConst : Bool) : List Expr → List Expr
  | [] => []
  | x :: xs =>
    lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst x ::
      lowerFieldExprList ambientModulus bindings inlineFieldOps stripCheckU56 foldConst xs

def lowerFieldArms (ambientModulus : Nat) (bindings : List FieldBinding)
    (inlineFieldOps stripCheckU56 foldConst : Bool) : List (Pat × Expr) → List (Pat × Expr)
  | [] => []
  | (p, b) :: rest =>
    (p, lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst b) ::
      lowerFieldArms ambientModulus bindings inlineFieldOps stripCheckU56 foldConst rest

end

/-- Lower a single `Lower.Fn`: if `f` is bound to a native `FieldOp` with
matching signature (all `.field` params and `.field` result), replace its body
with the native `FieldOp` body and mark `isInline := true`; otherwise lower its
body via `lowerFieldExpr`. -/
def lowerFieldFn (ambientModulus : Nat) (bindings : List FieldBinding)
    (inlineFieldOps stripCheckU56 foldConst : Bool) (f : Fn) : Fn :=
  match bindings.find? (·.fnName == f.name) with
  | some b =>
    if allFieldParams f && f.params.length == b.paramCount then
      let pNames := f.params.map Prod.fst
      let opParams := if b.dropFirstParam then pNames.drop 1 else pNames
      match fieldOpBody b.op opParams with
      | some nativeBody => { f with body := nativeBody, isInline := true }
      | none =>
        { f with body := lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst f.body }
    else
      { f with body := lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst f.body }
  | none =>
    { f with body := lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst f.body }

/-- Core ambient-field lowering pass on a list of `Lower.Fn`s (before pruning). -/
def lowerFieldOpsCore (cfg : Config) (fns : List Fn) : List Fn :=
  let bs := effectiveBindings cfg fns
  fns.map (lowerFieldFn cfg.ambientModulus bs cfg.inlineFieldOps cfg.stripCheckU56 cfg.foldConstHelpers)

/-- Full ambient-field lowering pass on `Lower.Fn`s: lowers all bound/recognized
ambient-field ops to native Formal Aiur `Field` arithmetic, eliminates redundant
`check_u56` / constant helpers, and prunes dead helpers via `pruneUnreachable`
when `cfg.pruneRoots` is set. -/
def lowerFieldOps (cfg : Config) (fns : List Fn) : List Fn :=
  let lowered := lowerFieldOpsCore cfg fns
  match cfg.pruneRoots with
  | some roots => pruneUnreachable roots lowered
  | none => lowered

/-! ## Exact Minimal `TableTier` Recomputation (`TableTier.none` Downgrade) -/

mutual

private def exprCallsPrefix (pfx : String) : Expr → Bool
  | .call nm _ xs => nm.startsWith pfx || exprListCallsPrefix pfx xs
  | .literal _ | .var _ | .global _ _ | .control _ _ => false
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs => exprListCallsPrefix pfx xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x => exprCallsPrefix pfx x
  | .letValue _ x b | .binary _ x b => exprCallsPrefix pfx x || exprCallsPrefix pfx b
  | .matchValue x arms => exprCallsPrefix pfx x || armsCallsPrefix pfx arms

private def exprListCallsPrefix (pfx : String) : List Expr → Bool
  | [] => false
  | x :: xs => exprCallsPrefix pfx x || exprListCallsPrefix pfx xs

private def armsCallsPrefix (pfx : String) : List (Pat × Expr) → Bool
  | [] => false
  | (_, b) :: rest => exprCallsPrefix pfx b || armsCallsPrefix pfx rest

end

mutual

private def tyUsesPrefix (pfx : String) : Ty → Bool
  | .named nm args => nm.startsWith pfx || tyListUsesPrefix pfx args
  | .tuple ts => tyListUsesPrefix pfx ts
  | .array t _ | .ptr t => tyUsesPrefix pfx t
  | _ => false

private def tyListUsesPrefix (pfx : String) : List Ty → Bool
  | [] => false
  | t :: ts => tyUsesPrefix pfx t || tyListUsesPrefix pfx ts

end

private def fnUsesPrefix (pfx : String) (f : Fn) : Bool :=
  exprCallsPrefix pfx f.body ||
  tyUsesPrefix pfx f.result ||
  f.params.any (fun p => tyUsesPrefix pfx p.2)

/-- Recompute the minimal `TableTier` required by `fns`.
Downgrades to `.none` (**0 fixed table rows!**) when no surviving function
references `UInt64::*`, `UInt32::*`, `UInt8::*`, or `U8Byte::*`. -/
def computeTier (fns : List Fn) : TableTier :=
  if fns.any (fnUsesPrefix "UInt64::") then .u64
  else if fns.any (fun f => fnUsesPrefix "UInt32::" f || fnUsesPrefix "UInt8::" f) then .u32
  else if fns.any (fnUsesPrefix "U8Byte::") then .byte256
  else .none

/-- True iff any function in `fns` calls `Fields::is_zero`. -/
def usesFieldsLibrary (fns : List Fn) : Bool :=
  fns.any fun f => callsAny ["Fields::is_zero"] f.body

/-- Apply `lowerFieldOps` to a `TypedLower.LoweredProgram` and downgrade its
`TableTier` to the exact minimum needed by the surviving functions. -/
def lowerProgram (cfg : Config) (lp : LoweredProgram) : LoweredProgram :=
  let fns' := lowerFieldOps cfg lp.program.functions
  let tier' := computeTier fns'
  { lp with
    program := { lp.program with functions := fns' }
    tier := tier' }

/-! ## Extended Schedule JSON Reader (`@[circuit_intrinsic]` & Extended Directives) -/

/-- Extended per-address directives emitted by `Ix.Compile.CircuitContract.Emit`
as optional fields inside `"ixcc/circuit-schedule/1"`. -/
structure ExtendedFnDirectives where
  isStatic : Bool := false
  reprJson : Option String := none
  intrinsic : Option String := none
  splitFastpath : Bool := false
  deriving BEq, DecidableEq, Repr, Inhabited

private def lookupEntry? (entries : List (String × Lean.Json)) (k : String) : Option Lean.Json :=
  (entries.find? (·.1 == k)).map (·.2)

/-- Parse an extended `"ixcc/circuit-schedule/1"` JSON string (which may carry
optional `"static"`, `"repr"`, `"intrinsic"`, `"splitFastpath"` keys under
`"byAddress"`), returning BOTH the base `CircuitSchedule` and the resolved
address-keyed `ExtendedFnDirectives`. -/
def parseExtendedScheduleJson (text : String) :
    Except String (Schedule.CircuitSchedule × List (IxCC.Ixon.Address × ExtendedFnDirectives)) := do
  IxCC.Src.Hints.checkJsonText text
  let j ← Lean.Json.parse text
  let topEntries ← match j.getObj? with
    | .ok m => pure m.toList
    | .error _ => throw "field-lower: expected JSON object for circuit schedule"
  let mut extList : List (IxCC.Ixon.Address × ExtendedFnDirectives) := []
  let mut strippedByAddr : List (String × Lean.Json) := []
  if let some byAddrJson := lookupEntry? topEntries "byAddress" then
    let addrEntries ← match byAddrJson.getObj? with
      | .ok m => pure m.toList
      | .error _ => throw "field-lower: expected JSON object for byAddress"
    for (hex, v) in addrEntries do
      let addr ← ScheduleJson.addressFromHex hex
      let fsEntries ← match v.getObj? with
        | .ok m => pure m.toList
        | .error _ => throw s!"field-lower: expected JSON object for byAddress.{hex}"
      let isStatic := match lookupEntry? fsEntries "static" with
        | some (.bool b) => b
        | _ => false
      let reprJson := (lookupEntry? fsEntries "repr").map Lean.Json.compress
      let intrinsic := match lookupEntry? fsEntries "intrinsic" with
        | some (.str s) => some s
        | _ => none
      let splitFastpath := match lookupEntry? fsEntries "splitFastpath" with
        | some (.bool b) => b
        | _ => false
      if isStatic || reprJson.isSome || intrinsic.isSome || splitFastpath then
        let dir : ExtendedFnDirectives :=
          { isStatic := isStatic, reprJson := reprJson,
            intrinsic := intrinsic, splitFastpath := splitFastpath }
        extList := extList ++ [(addr, dir)]
      let legacyOnly := fsEntries.filter fun (k, _) =>
        k == "inline" || k == "group" || k == "unroll" || k == "lanes"
      strippedByAddr := strippedByAddr ++ [(hex, Lean.Json.mkObj legacyOnly)]
  let strippedTop := topEntries.map fun (k, v) =>
    if k == "byAddress" then (k, Lean.Json.mkObj strippedByAddr) else (k, v)
  let baseSched ← ScheduleJson.fromJson (Lean.Json.mkObj strippedTop)
  return (baseSched, extList)

private def gkeySourceCId? : IxCC.Key.GKey → Option IxCC.Src.CId
  | .const c _ | .byName c _ => some c
  | .spec g _ | .worker g _ | .entry g _ => gkeySourceCId? g
  | .recStar _ _ | .wrapper _ _ | .lam _ _ | .dispatch _ => none

private def funAddress? (src : IxCC.Src.Program) (fd : IxCC.Fir.Fun) : Option IxCC.Ixon.Address :=
  (gkeySourceCId? fd.key).bind fun cid => (src.entry? cid).map (·.addr)

/-- Resolve `@[circuit_intrinsic "field.*"]` address-keyed directives against
`(src, P, fns)` into concrete `FieldBinding`s for `FieldLower.Config`. -/
def resolveIntrinsicBindings (src : IxCC.Src.Program) (P : IxCC.Fir.Program) (fns : List Fn)
    (ext : List (IxCC.Ixon.Address × ExtendedFnDirectives)) : List FieldBinding :=
  P.funList.filterMap fun (fid, fd) => do
    let addr ← funAddress? src fd
    let (_, dir) ← ext.find? (·.1 == addr)
    let intrName ← dir.intrinsic
    let op ← FieldOp.ofIntrinsicName? intrName
    let nm := funName fid
    let fnDef ← fns.find? (·.name == nm)
    if !allFieldParams fnDef then none
    else if fnDef.params.length == op.arity then
      some { fnName := nm, op, dropFirstParam := false }
    else if fnDef.params.length == op.arity + 1 then
      some { fnName := nm, op, dropFirstParam := true }
    else none

/-! ## 3-Field Linker, World Check, Evaluator & Packager (`Goldilocks` | `BN254` | `BLS12-381`) -/

/-- Executable check that `Fields::is_zero` is present in `s` with its exact
signature `(x : Field)` and body `match x { 0 => 1, _ => 0 }`. -/
def checkFieldsIsZero {F : Type} [Field F] [DecidableEq F] (s : Aiur.Generic.Source F) : Bool :=
  match s.program.findFunction? "Fields::is_zero" with
  | some f =>
    f.typeParams.isEmpty &&
    (f.params == [("x", .field)]) &&
    (f.body == Aiur.Generic.Expr.matchValue (.var "x")
      [(.literal (0 : F), .literal (1 : F)), (.wildcard, .literal (0 : F))])
  | none => false

/-- Executable world check for a `FieldLower`-lowered program over any prime field `F`:
verifies `TypedWorld.checkTypedWorld` and, whenever `Fields::is_zero` is referenced,
verifies `checkFieldsIsZero`. -/
def checkFieldWorld {F : Type} [Field F] [DecidableEq F] (s : Aiur.Generic.Source F)
    (lp : LoweredProgram) : Bool :=
  TypedWorld.checkTypedWorld s lp &&
  (!usesFieldsLibrary lp.program.functions || checkFieldsIsZero s)

/-- Link a `LoweredProgram` over **any** prime field `F` (`Goldilocks`, `BN254`,
`BLS12-381`, or arbitrary `ZMod p`):
* links `Aiur.Library.Field.declarations` (`Fields::is_zero`, 0 tables!) on demand;
* links ONLY the table modules required by `lp.tier` (`.none` → **0 table rows!**). -/
def linkedProgramFor (F : Type) [NatCast F] (lp : LoweredProgram) : Aiur.Modules.Program F :=
  let progMod : Aiur.Modules.Program Nat :=
    { modules := [{ name := moduleName, body := .definitions { program := lp.program } }] }
  let withFields : Aiur.Modules.Program Nat :=
    if usesFieldsLibrary lp.program.functions then
      Aiur.Library.Field.declarations.append progMod
    else progMod
  let combined : Aiur.Modules.Program Nat := match lp.tier with
    | .none => withFields
    | .byte256 => TypedLower.u8ByteModule.append withFields
    | .u32 => Aiur.Library.U32.source.append withFields
    | .u64 => (Aiur.Library.U32.source.append Aiur.Library.U64.declarations).append withFields
  combined.toField F

/-- Compiled & packaged artifact for an ambient prime field `ZMod p`. -/
structure FieldCompiled where
  modulus : Nat
  entry : String
  tier : TableTier
  usesFieldsLib : Bool
  worldOk : Bool
  chips : List (String × Nat × Nat × Nat)
  bytes : ByteArray
  digest : IxCC.Ixon.Address

/-- Prepare, check world, optimize (`compileOptimized`), export trace plan
(`Trace.exportPlanPar`), and package (`Aiur.Artifact.package` or
`Aiur.Artifact.execution`) a `FieldLower`-lowered program over **any** prime
field `ZMod p` (`[Fact (Nat.Prime p)]`) — ready for `ixcc_prove`,
`tiling_export2 --goldilocks | --bn254 | --bls12-381`, `wide_export`, and
`plonk_export --bn254 | --bls12-381`! -/
def compileForField (p : Nat) [Fact (Nat.Prime p)]
    (lp : LoweredProgram)
    (entryIdx : Nat := 0)
    (kind : CompiledCert.ArtifactKind := .program)
    (args : List Nat := [])
    (aiurConfig : Aiur.Optimized.Config := {})
    (groups : List (String × List String) := []) : Except String FieldCompiled := do
  let prog := linkedProgramFor (ZMod p) lp
  let entry := qualified (entryName entryIdx)
  let prepared ← Aiur.Modules.prepare prog [entry]
  let worldOk := checkFieldWorld prepared.environment.source lp
  unless worldOk do
    throw s!"field-lower: world check failed for entry {entry} over prime modulus {p}"
  let execution ← prepared.exportExecution
  let compiled ← prepared.compileOptimized aiurConfig
  let chips := compiled.circuit.artifact.system.chips.map fun c =>
    (c.name, c.numVars, c.sends.length, c.memory.length)
  let isWide := p ≥ 2 ^ 64
  let (execution, trace) ←
    if isWide then
      Aiur.Trace.exportPlanWide p ZMod.val
        compiled.circuit.inlined.program compiled.circuit.artifact execution groups
    else
      Aiur.Trace.exportPlanPar p ZMod.val
        compiled.circuit.inlined.program compiled.circuit.artifact execution groups
  let bytes ← match kind with
    | .program =>
      if isWide then
        Aiur.Artifact.packageWide execution p ZMod.val (some trace)
      else
        Aiur.Artifact.package execution p ZMod.val (some trace)
    | .execution =>
      if isWide then
        throw s!"field-lower: execution packages require a 64-bit prime; use .program (wide v3) for modulus {p}"
      else
        Aiur.Artifact.execution execution p ZMod.val (some trace) args [] #[]
  return {
    modulus := p
    entry
    tier := lp.tier
    usesFieldsLib := usesFieldsLibrary lp.program.functions
    worldOk
    chips
    bytes
    digest := IxCC.Ixon.Address.blake3Pure bytes
  }

/-- Evaluate a `FieldLower`-lowered program over any prime field `ZMod p` via
Formal Aiur's fuelled evaluator (`Aiur.Modules.Prepared.run`). -/
def runForField (p : Nat) [Fact (Nat.Prime p)]
    (lp : LoweredProgram) (args : List Nat)
    (entryIdx : Nat := 0) (fuel : Nat := 100000000) :
    Except String (Aiur.SourceValue (ZMod p)) := do
  let prog := linkedProgramFor (ZMod p) lp
  let entry := qualified (entryName entryIdx)
  let prepared ← Aiur.Modules.prepare prog [entry]
  let hints := prepared.environment.source.checkedHints
    (Hints.dispatcher (fun (x : ZMod p) => x.val))
  let (value, _) ← prepared.run entry (args.map fun n => .field (n : ZMod p)) fuel hints
  return value

/-- Compile and package a `FieldLower`-lowered program over Goldilocks (`p_G`). -/
def compileGoldilocks (lp : LoweredProgram) (entryIdx : Nat := 0)
    (kind : CompiledCert.ArtifactKind := .program) (args : List Nat := [])
    (aiurConfig : Aiur.Optimized.Config := {})
    (groups : List (String × List String) := []) : Except String FieldCompiled :=
  compileForField goldilocksModulus lp entryIdx kind args aiurConfig groups

/-- Compile and package a `FieldLower`-lowered program over BN254 `Fr`. -/
def compileBN254 (lp : LoweredProgram) (entryIdx : Nat := 0)
    (kind : CompiledCert.ArtifactKind := .program) (args : List Nat := [])
    (aiurConfig : Aiur.Optimized.Config := {})
    (groups : List (String × List String) := []) : Except String FieldCompiled :=
  compileForField bn254Modulus lp entryIdx kind args aiurConfig groups

/-- Compile and package a `FieldLower`-lowered program over BLS12-381 `Fr`. -/
def compileBLS12381 (lp : LoweredProgram) (entryIdx : Nat := 0)
    (kind : CompiledCert.ArtifactKind := .program) (args : List Nat := [])
    (aiurConfig : Aiur.Optimized.Config := {})
    (groups : List (String × List String) := []) : Except String FieldCompiled :=
  compileForField bls12381Modulus lp entryIdx kind args aiurConfig groups

/-! ## Plainness Preservation Proofs (`Lower.isPlainExpr = true`, Zero `sorry`) -/

theorem isPlainExpr_fieldOpBody {op : FieldOp} {params : List String} {e : Expr}
    (h : fieldOpBody op params = some e) : isPlainExpr e = true := by
  cases op <;> rcases params with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;>
    simp only [fieldOpBody, Option.some.injEq, reduceCtorEq] at h
  all_goals subst h; rfl

theorem isPlainExpr_fieldOpExpr {op : FieldOp} {xs : List Expr} {e : Expr}
    (h : fieldOpExpr op xs = some e) (hxs : isPlainList xs = true) :
    isPlainExpr e = true := by
  cases op <;> rcases xs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;>
    simp only [fieldOpExpr, Option.some.injEq, reduceCtorEq] at h
  all_goals subst h
  all_goals simp only [isPlainList, Bool.and_true, Bool.and_eq_true] at hxs
  all_goals simp [fieldAddE, fieldSubE, fieldMulE, fieldNegE, fieldIsZeroE, fieldEqE,
    fieldInvE, fieldInvVarE, fieldDivE, fieldDivVarsE, callE, vE, litE, letE, matchE,
    isPlainExpr, isPlainList, isPlainArms, hxs]

theorem isPlainExpr_foldConstCall {foldConst : Bool} {nm : String} {targs : Option (List Ty)}
    {xs : List Expr} {e : Expr} (h : foldConstCall foldConst nm targs xs = some e) :
    isPlainExpr e = true := by
  unfold foldConstCall at h
  split at h
  · split at h
    · split at h <;> cases h; rfl
    · split at h <;> cases h; rfl
    · split at h <;> cases h; rfl
    · split at h <;> cases h; rfl
    · cases h
  · cases h

theorem isPlainExpr_lowerCall (bindings : List FieldBinding) (inlineFieldOps foldConst : Bool)
    (nm : String) (targs : Option (List Ty)) (xs : List Expr) {xs' : List Expr}
    (hxs : isPlainList xs' = true) :
    isPlainExpr (lowerCall bindings inlineFieldOps foldConst nm targs xs xs') = true := by
  unfold lowerCall
  cases hfold : foldConstCall foldConst nm targs xs with
  | some e => exact isPlainExpr_foldConstCall hfold
  | none =>
    dsimp only
    split
    · split
      · next b _ =>
        split
        · cases hop : fieldOpExpr b.op xs' with
          | none => simp [Option.getD, isPlainExpr, hxs]
          | some e => exact isPlainExpr_fieldOpExpr hop hxs
        · split
          · next _ _ hd' rest' =>
            simp only [isPlainList, Bool.and_eq_true] at hxs
            cases hop : fieldOpExpr b.op rest' with
            | none => simp [Option.getD, isPlainExpr, isPlainList, hxs.1, hxs.2]
            | some e => exact isPlainExpr_fieldOpExpr hop hxs.2
          · simp [isPlainExpr, hxs]
      · simp [isPlainExpr, hxs]
    · simp [isPlainExpr, hxs]

theorem isPlainExpr_lowerProject (foldConst : Bool) (x : Expr) {x' : Expr}
    (hx : isPlainExpr x' = true) (i : Nat) :
    isPlainExpr (lowerProject foldConst x x' i) = true := by
  unfold lowerProject
  split
  · split
    · split <;> first | rfl | exact hx
    · split <;> first | rfl | exact hx
    · split <;> first | rfl | exact hx
    · split <;> first | rfl | exact hx
    · rfl
    · rfl
    · exact hx
  · exact hx

theorem isPlainExpr_lowerLetValue (stripCheckU56 foldConst : Bool) (p : Pat) (x : Expr)
    {x' b' : Expr} (hx : isPlainExpr x' = true) (hb : isPlainExpr b' = true) :
    isPlainExpr (lowerLetValue stripCheckU56 foldConst p x x' b') = true := by
  unfold lowerLetValue
  split
  · split
    · rfl
    · simp [isPlainExpr, hx]
  · split
    · exact hb
    · simp [isPlainExpr, hx, hb]
  · split
    · exact hb
    · simp [isPlainExpr, hx, hb]
  · simp only [isPlainExpr, isPlainList, Bool.and_true, Bool.true_and] at hb
    split
    · split
      · split
        · exact hx
        · simp [isPlainExpr, hx]
      · simp [isPlainExpr, hx, hb]
    · simp [isPlainExpr, isPlainList, hx, hb]
  · split
    · exact hx
    · simp [isPlainExpr, hx]
  · simp [isPlainExpr, hx, hb]

theorem isPlainExpr_lowerMatchValue (ambientModulus : Nat) (foldConst : Bool)
    (s : Expr) {s' : Expr} {arms' : List (Pat × Expr)}
    (hs : isPlainExpr s' = true) (ha : isPlainArms arms' = true) :
    isPlainExpr (lowerMatchValue ambientModulus foldConst s s' arms') = true := by
  unfold lowerMatchValue
  split
  · split
    · simp only [isPlainArms, Bool.and_true, Bool.and_eq_true] at ha
      split
      · exact ha.1
      · split
        · exact ha.2
        · simp [isPlainExpr, isPlainArms, hs, ha.1, ha.2]
    · simp [isPlainExpr, hs, ha]
  · simp [isPlainExpr, hs, ha]

mutual

/-- `lowerFieldExpr` preserves `Lower.isPlainExpr = true` on every expression. -/
theorem isPlainExpr_lowerFieldExpr (ambientModulus : Nat) (bindings : List FieldBinding)
    (inlineFieldOps stripCheckU56 foldConst : Bool) :
    ∀ (e : Expr), isPlainExpr e = true →
      isPlainExpr (lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst e) = true
  | .call nm targs xs, h =>
    isPlainExpr_lowerCall bindings inlineFieldOps foldConst nm targs xs
      (isPlainList_lowerFieldExprList ambientModulus bindings inlineFieldOps stripCheckU56 foldConst xs h)
  | .project x i, h =>
    isPlainExpr_lowerProject foldConst x
      (isPlainExpr_lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst x h) i
  | .letValue p x b, h => by
    simp only [isPlainExpr, Bool.and_eq_true] at h
    exact isPlainExpr_lowerLetValue stripCheckU56 foldConst p x
      (isPlainExpr_lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst x h.1)
      (isPlainExpr_lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst b h.2)
  | .matchValue s arms, h => by
    simp only [isPlainExpr, Bool.and_eq_true] at h
    exact isPlainExpr_lowerMatchValue ambientModulus foldConst s
      (isPlainExpr_lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst s h.1)
      (isPlainArms_lowerFieldArms ambientModulus bindings inlineFieldOps stripCheckU56 foldConst arms h.2)
  | .tuple xs, h | .array xs, h | .construct _ _ _ xs, h | .constructAs _ _ _ xs, h
  | .record _ xs, h | .update _ xs, h | .builtin _ xs, h =>
    isPlainList_lowerFieldExprList ambientModulus bindings inlineFieldOps stripCheckU56 foldConst xs h
  | .repeat x _, h | .index x _, h | .slice x _ _, h | .member x _, h
  | .store x, h | .load x, h | .hint _ x _, h | .neg x, h =>
    isPlainExpr_lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst x h
  | .binary _ x y, h => by
    simp only [isPlainExpr, Bool.and_eq_true] at h
    simp only [lowerFieldExpr, isPlainExpr,
      isPlainExpr_lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst x h.1,
      isPlainExpr_lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst y h.2,
      Bool.and_self]
  | .literal _, _ | .var _, _ => rfl
  | .global _ _, h | .control _ _, h => by simp [isPlainExpr] at h

theorem isPlainList_lowerFieldExprList (ambientModulus : Nat) (bindings : List FieldBinding)
    (inlineFieldOps stripCheckU56 foldConst : Bool) :
    ∀ (xs : List Expr), isPlainList xs = true →
      isPlainList (lowerFieldExprList ambientModulus bindings inlineFieldOps stripCheckU56 foldConst xs) = true
  | [], _ => rfl
  | x :: xs, h => by
    simp only [isPlainList, Bool.and_eq_true] at h
    simp only [lowerFieldExprList, isPlainList,
      isPlainExpr_lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst x h.1,
      isPlainList_lowerFieldExprList ambientModulus bindings inlineFieldOps stripCheckU56 foldConst xs h.2,
      Bool.and_self]

theorem isPlainArms_lowerFieldArms (ambientModulus : Nat) (bindings : List FieldBinding)
    (inlineFieldOps stripCheckU56 foldConst : Bool) :
    ∀ (arms : List (Pat × Expr)), isPlainArms arms = true →
      isPlainArms (lowerFieldArms ambientModulus bindings inlineFieldOps stripCheckU56 foldConst arms) = true
  | [], _ => rfl
  | (_, b) :: rest, h => by
    simp only [isPlainArms, Bool.and_eq_true] at h
    simp only [lowerFieldArms, isPlainArms,
      isPlainExpr_lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst b h.1,
      isPlainArms_lowerFieldArms ambientModulus bindings inlineFieldOps stripCheckU56 foldConst rest h.2,
      Bool.and_self]

end

/-- `lowerFieldFn` preserves `Lower.isPlainExpr = true`. -/
theorem isPlainExpr_lowerFieldFn (ambientModulus : Nat) (bindings : List FieldBinding)
    (inlineFieldOps stripCheckU56 foldConst : Bool) {f : Fn}
    (hf : isPlainExpr f.body = true) :
    isPlainExpr (lowerFieldFn ambientModulus bindings inlineFieldOps stripCheckU56 foldConst f).body = true := by
  unfold lowerFieldFn
  cases bindings.find? (·.fnName == f.name) with
  | none =>
    exact isPlainExpr_lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst f.body hf
  | some b =>
    dsimp only
    by_cases hsig : (allFieldParams f && (f.params.length == b.paramCount)) = true
    · simp only [hsig, ↓reduceIte]
      cases hbody : fieldOpBody b.op (if b.dropFirstParam then (f.params.map Prod.fst).drop 1 else f.params.map Prod.fst) with
      | some nativeBody => exact isPlainExpr_fieldOpBody hbody
      | none => exact isPlainExpr_lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst f.body hf
    · simp only [hsig]
      exact isPlainExpr_lowerFieldExpr ambientModulus bindings inlineFieldOps stripCheckU56 foldConst f.body hf

/-- `lowerFieldOps` (including optional `pruneUnreachable`) preserves `Lower.isPlainExpr = true`
on every surviving function body. -/
theorem isPlainExpr_lowerFieldOps (cfg : Config) {fns : List Fn}
    (hfns : ∀ f ∈ fns, isPlainExpr f.body = true) :
    ∀ f ∈ lowerFieldOps cfg fns, isPlainExpr f.body = true := by
  have hcore : ∀ f ∈ lowerFieldOpsCore cfg fns, isPlainExpr f.body = true := by
    intro f hf
    unfold lowerFieldOpsCore at hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    exact isPlainExpr_lowerFieldFn _ _ _ _ _ (hfns g hg)
  unfold lowerFieldOps
  split
  · intro f hf
    unfold pruneUnreachable at hf
    exact hcore f (List.mem_filter.mp hf).1
  · exact hcore

end IxCC.AiurBackend.FieldLower
