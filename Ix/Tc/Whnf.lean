module

public import Ix.Tc.Monad

/-!
Mirror: crates/kernel/src/whnf.rs (plus `str_lit_to_constructor` from
def_eq.rs and `computed_is_rec` from inductive.rs, which whnf's
struct-likeness check needs).

WHNF layering (each with its own fuel-bounded loop):
- `whnf`: whnf-no-delta → native → nat → decidable → string → delta, looping
  with cycle detection. Full caching keyed `(exprAddr, ctxAddrForLbr)`.
- `whnfNoDeltaImpl`: whnf-core → proj-app → bitvec → nat → native → string →
  projection-definition rewriting (FULL only) → quot.
- `whnfCoreWithFlags(Uncached)`: beta / iota / zeta / proj — structural only.

Load-bearing cache semantics (from env.rs / whnf.rs, do not "simplify"):
- FULL vs DEF_EQ_CORE (cheap-proj) results go to **separate caches**;
  `cheapRecursionDepth` bumps around the def-eq entry points route writes.
- `NatSuccMode.stuck` bypasses all whnf caches (`useCache = false`).
- Transient Nat-literal recursor work is never cached (RSS would grow linear
  in the literal); `natSuccStuck` memoizes stuck succ-chain peels instead.
- Nothing is cached while `inNativeReduce` is set.

Errors inside K-synthesis, struct-eta, and decidable probes are swallowed
(state mutations survive — EStateM parity with Rust `&mut`).

v1 scope (per plan): Nat literal arithmetic + succ-collapse + linear-rec,
String machinery, platform bits, reduceBool/reduceNat markers, Nat
decidables, Int decidable literal normalization, and BitVec natives
(`BitVec.toNat/ult/decide-lt` — load-bearing for UInt-heavy grind proofs,
which otherwise descend into Nat.rec towers and trip maxDefEqDepth).
-/

public section
@[expose] section

namespace Ix.Tc

open Std (HashMap HashSet)

/-- Local fuel cap for whnf on *open* arguments of the Nat reducer. -/
def natReducerOpenArgRecFuel : UInt64 := 4096

/-- Recursor info snapshot for iota reduction (tc.rs `IotaInfo`). -/
structure IotaInfo (m : Mode) where
  k : Bool
  params : Nat
  motives : Nat
  minors : Nat
  indices : Nat
  majorIdx : Nat
  rules : Array (RecRule m)
  lvls : UInt64

structure NatRecLiteralParts (m : Mode) where
  spine : Array (KExpr m)
  major : Nat
  baseIdx : Nat
  stepIdx : Nat
  majorIdx : Nat

/-! ### Pure helpers -/

/-- Decode exactly the recursor fields consumed by ordinary iota.  Keeping
this pure snapshot separate from `tryIotaWithFlags` gives verification an
exact relation between the loaded `KConst` and the rule array later indexed
by constructor position. -/
def KConst.iotaInfo? : KConst m → Option (IotaInfo m)
  | .recr (k := k) (lvls := lvls) (params := params)
      (indices := indices) (motives := motives) (minors := minors)
      (rules := rules) .. =>
    let majorIdx := (params + motives + minors + indices).toNat
    some {
      k
      params := params.toNat
      motives := motives.toNat
      minors := minors.toNat
      indices := indices.toNat
      majorIdx
      rules
      lvls }
  | _ => none

/-- Decode the constructor index and field count used by ordinary iota.
All other loaded constant kinds are constructor misses. -/
def KConst.iotaCtorInfo? : KConst m → Option (Nat × Nat)
  | .ctor (cidx := cidx) (fields := fields) .. =>
    some (cidx.toNat, fields.toNat)
  | _ => none

/-- Nat value from a literal or the `Nat.zero` constructor (C++
    `is_nat_lit_ext` / lean4lean `rawNatLitExt?`). -/
def extractNatLit (e : KExpr m) (prims : Primitives m) : Option Nat :=
  match e with
  | .nat val _ _ => some val
  | .const id _ _ => if id.addr == prims.natZero.addr then some 0 else none
  | _ => none

/-- Nat value from literal form or a constructor numeral
    (`Nat.succ (Nat.succ …(lit)…)`). Exactly one application is accepted at
    each successor layer, matching the former `collectSpine`/size check. -/
def extractNatValue (e : KExpr m) (prims : Primitives m) : Option Nat :=
  match extractNatLit e prims with
  | some n => some n
  | none =>
    match e with
    | .app (.const id _ _) arg _ =>
      if id.addr == prims.natSucc.addr then
        (extractNatValue arg prims).map (· + 1)
      else none
    | _ => none
termination_by structural e

/-- Binary Nat op evaluation. `none` when uncomputable (pow exponent above
    the kernel cap, shift beyond u64) — caller leaves the term unreduced. -/
def computeNatBin (addr : Address) (p : PrimAddrs) (a b : Nat) : Option Nat :=
  if addr == p.natAdd then some (a + b)
  else if addr == p.natSub then some (a - b)
  else if addr == p.natMul then some (a * b)
  else if addr == p.natDiv then some (if b == 0 then 0 else a / b)
  else if addr == p.natMod then some (if b == 0 then a else a % b)
  else if addr == p.natPow then
    -- Matches C++ `ReducePowMaxExp` / lean4lean `reducePowMaxExp`.
    if b ≤ 16777216 then some (a ^ b) else none
  else if addr == p.natGcd then some (Nat.gcd a b)
  else if addr == p.natLand then some (a &&& b)
  else if addr == p.natLor then some (a ||| b)
  else if addr == p.natXor then some (a ^^^ b)
  else if addr == p.natShiftLeft then
    if b < 2 ^ 64 then some (a <<< b) else none
  else if addr == p.natShiftRight then
    if b < 2 ^ 64 then some (a >>> b) else none
  else none

/-- Int literal (canonical ctor form `Int.ofNat n` / `Int.negSucc n`) as a
    mathematical integer. -/
def extractIntLit (e : KExpr m) (prims : Primitives m) : Option _root_.Int :=
  let (head, args) := e.collectSpine
  match head with
  | .const id _ _ =>
    if args.size != 1 then none
    else match extractNatValue args[0]! prims with
      | none => none
      | some n =>
        if id.addr == prims.intOfNat.addr then some (_root_.Int.ofNat n)
        else if id.addr == prims.intNegSucc.addr then some (-(_root_.Int.ofNat n + 1))
        else none
  | _ => none

/-- Arity/field info when a definition body is a projection wrapper
    `λ…λ. Prj(S, f, Var k)` (whnf.rs `projection_definition_info`). -/
def projectionDefinitionInfo (val : KExpr m) :
    Option (Nat × KId m × UInt64 × Nat) :=
  go val 0
where
  go (cur : KExpr m) (arity : Nat) : Option (Nat × KId m × UInt64 × Nat) :=
    match cur with
    | .lam _ _ _ body _ => go body (arity + 1)
    | .prj structId field projected _ =>
      match projected with
      | .var idx _ _ =>
        if idx.toNat ≥ arity then none
        else some (arity, structId, field, arity - 1 - idx.toNat)
      | _ => none
    | _ => none
  termination_by structural cur

namespace RecM

/-- Swallow any `TcError`, yielding `none` (Rust `Err(_) => return Ok(None)`
    with state mutations surviving). -/
@[inline] def try? (x : RecM m α) : RecM m (Option α) := do
  try
    return some (← x)
  catch _ =>
    return none

@[inline] def prims : RecM m (Primitives m) := do
  return (← get).prims

/-- Anon-metadata name/binder-info for freshly built nodes. -/
@[inline] def anonN : {m : Mode} → m.F Name :=
  Mode.fieldWith fun _ => .mkAnon
@[inline] def anonBi : {m : Mode} → m.F Lean.BinderInfo :=
  Mode.fieldWith fun _ => .default

def natExprFromValue (n : Nat) : KExpr m :=
  KExpr.mkNat n (KExpr.natBlob n)

def natLiteral (n : Nat) : KExpr m := natExprFromValue n

/-- `Nat.succ pred` (NOT interned — mirrors `mk_nat_succ`). -/
def mkNatSucc (pred : KExpr m) : RecM m (KExpr m) := do
  return KExpr.mkApp (.mkConst (← prims).natSucc #[]) pred

/-- `Nat.add a b` (NOT interned). -/
def mkNatAdd (a b : KExpr m) : RecM m (KExpr m) := do
  return KExpr.mkApp (KExpr.mkApp (.mkConst (← prims).natAdd #[]) a) b

/-- `0 → Nat.zero`, `n+1 → Nat.succ (lit (n-1))` (one layer; NOT interned). -/
def natToConstructor (val : Nat) : RecM m (KExpr m) := do
  let p ← prims
  if val == 0 then
    return .mkConst p.natZero #[]
  else
    return KExpr.mkApp (.mkConst p.natSucc #[]) (natExprFromValue (val - 1))

def isNatBinArithAddr (addr : Address) : RecM m Bool := do
  let p ← prims
  return addr == p.natAdd.addr || addr == p.natSub.addr
    || addr == p.natMul.addr || addr == p.natDiv.addr
    || addr == p.natMod.addr || addr == p.natPow.addr
    || addr == p.natGcd.addr || addr == p.natLand.addr
    || addr == p.natLor.addr || addr == p.natXor.addr
    || addr == p.natShiftLeft.addr || addr == p.natShiftRight.addr

def isNatBinPredAddr (addr : Address) : RecM m Bool := do
  let p ← prims
  return addr == p.natBeq.addr || addr == p.natBle.addr

/-- Intern the character-list fold used by String-literal expansion.  The
input is already reversed, so each step prepends the current character and
the final list retains source order.  Keeping this recursion explicit gives
verification a structural induction point without changing production's
left-to-right intern sequence. -/
def strLitListToConstructor (charOfNat cons : KExpr m) :
    List Char → KExpr m → RecM m (KExpr m)
  | [], list => pure list
  | c :: chars, list => do
    let natLit ← TcM.intern (natExprFromValue c.toNat : KExpr m)
    let charVal ← TcM.intern (KExpr.mkApp charOfNat natLit)
    let partialApp ← TcM.intern (KExpr.mkApp cons charVal)
    let list ← TcM.intern (KExpr.mkApp partialApp list)
    strLitListToConstructor charOfNat cons chars list

/-- `"abc" → String.ofList (List.cons (Char.ofNat 97) … List.nil)` — the
    kernel's string-literal constructor expansion (def_eq.rs
    `str_lit_to_constructor`; `Char.ofNat` + `String.ofList`, matching
    lean4lean / C++). -/
def strLitToConstructor (s : String) : RecM m (KExpr m) := do
  let p ← prims
  let charConst ← TcM.intern (.mkConst p.charType #[])
  let charOfNat ← TcM.intern (.mkConst p.charOfNat #[])
  let stringMk ← TcM.intern (.mkConst p.stringOfList #[])
  let listNilZ ← TcM.intern (.mkConst p.listNil #[.mkZero])
  let nil ← TcM.intern (KExpr.mkApp listNilZ charConst)
  let listConsZ ← TcM.intern (.mkConst p.listCons #[.mkZero])
  let cons ← TcM.intern (KExpr.mkApp listConsZ charConst)
  let list ← strLitListToConstructor charOfNat cons s.toList.reverse nil
  TcM.intern (KExpr.mkApp stringMk list)

/-- `Int.ofNat n` / `Int.negSucc (|v|-1)` canonical literal. -/
def internIntLit (v : _root_.Int) : RecM m (KExpr m) := do
  let p ← prims
  let (ctorId, natVal) :=
    if v < 0 then (p.intNegSucc, ((-v).toNat - 1))
    else (p.intOfNat, v.toNat)
  let natExpr ← TcM.intern (natExprFromValue natVal : KExpr m)
  let ctor ← TcM.intern (.mkConst ctorId #[])
  TcM.intern (KExpr.mkApp ctor natExpr)

def boolLitValue (e : KExpr m) : RecM m (Option Bool) := do
  let p ← prims
  match e with
  | .const id _ _ =>
    if id.addr == p.boolTrue.addr then return some true
    else if id.addr == p.boolFalse.addr then return some false
    else return none
  | _ => return none

def finishAppResult (result₀ : KExpr m) (args : Array (KExpr m))
    (consumed : Nat) : RecM m (KExpr m) := do
  let mut result := result₀
  for arg in args.extract consumed args.size do
    result ← TcM.intern (KExpr.mkApp result arg)
  return result

/-! ### Bounded Nat-offset parsing (Tier B)

The public API carries the historical `depth`; the total workers carry the
equivalent remaining budget `256 - depth` so every recursive call is visibly
decreasing and the old cutoff result is unchanged.
-/

mutual

def natOffsetFuel : Nat → KExpr m → RecM m (Option (KExpr m × Nat))
  | 0, _ => pure none
  | fuel + 1, e => do
    let (head, args) := e.collectSpine
    let .const id _ _ := head | return none
    let p ← prims
    if id.addr == p.natSucc.addr && args.size == 1 then
      let arg := args[0]!
      let (base, offset) := (← natOffsetFuel fuel arg).getD (arg, 0)
      return some (base, offset + 1)
    if id.addr == p.natAdd.addr && args.size == 2 then
      let some rhs ← evalNatOffsetLiteralFuel fuel args[1]! | return none
      let arg := args[0]!
      let (base, offset) := (← natOffsetFuel fuel arg).getD (arg, 0)
      return some (base, offset + rhs)
    return none

/-- Syntactic, no-delta evaluator for Nat offset constants (weaker than
    WHNF by design), indexed by its remaining historical depth budget. -/
def evalNatOffsetLiteralFuel : Nat → KExpr m → RecM m (Option Nat)
  | 0, _ => pure none
  | fuel + 1, e => do
    let p ← prims
    if let some n := extractNatValue e p then
      return some n
    let (head, args) := e.collectSpine
    let .const id _ _ := head | return none
    if id.addr == p.natPred.addr && args.size == 1 then
      let some n ← evalNatOffsetLiteralFuel fuel args[0]! | return none
      return some (n - 1)
    if (← isNatBinArithAddr id.addr) && args.size == 2 then
      let some a ← evalNatOffsetLiteralFuel fuel args[0]! | return none
      let some b ← evalNatOffsetLiteralFuel fuel args[1]! | return none
      return computeNatBin id.addr PrimAddrs.canonical a b
    return none

end

def natOffset (e : KExpr m) (depth : Nat) :
    RecM m (Option (KExpr m × Nat)) :=
  natOffsetFuel (256 - depth) e

def natOffsetOrZero (e : KExpr m) (depth : Nat) :
    RecM m (KExpr m × Nat) := do
  return (← natOffset e depth).getD (e, 0)

def evalNatOffsetLiteral (e : KExpr m) (depth : Nat) :
    RecM m (Option Nat) :=
  evalNatOffsetLiteralFuel (256 - depth) e

/-- Decompose a (whnf'd) Nat term into `(base, offset)` for offset-aware
    def-eq: `Lit n` → `(none, n)`; `succ^j(Nat.add core (Lit m))` →
    `(some core, j + m)` read in O(1) per layer via `natOffset` instead of
    peeled one def-eq recursion level at a time. `base = none` means the
    core is literal zero (the term IS a numeral). The outer `none` means
    "not offset-shaped". Mirrors whnf.rs `nat_offset_decompose`. -/
def natOffsetDecompose (e : KExpr m) :
    RecM m (Option (Option (KExpr m) × Nat)) := do
  if let some v := extractNatValue e (← prims) then
    return some (none, v)
  match (← natOffset e 0) with
  | some (base, offset) =>
    if offset == 0 then
      return none
    if let some bv := extractNatValue base (← prims) then
      return some (none, bv + offset)
    return some (some base, offset)
  | none => return none

/-- Rebuild `base + r` in the compact offset form left stuck by
    `tryNatOffsetStuck` (NOT interned — mirrors `nat_offset_rebuild`). -/
def natOffsetRebuild (base : Option (KExpr m)) (r : Nat) :
    RecM m (KExpr m) := do
  match base with
  | none => return natExprFromValue r
  | some b =>
    if r == 0 then
      return b
    mkNatAdd b (natExprFromValue r)

/-- Allocation-free head probe for `tryNatOffsetStuck`: the probe runs once
    per delta-unfold loop iteration, so the spine head must be one of the
    three Nat primitives before a spine is collected. -/
def natOffsetStuckHead (p : Primitives m) : KExpr m → Bool
  | .app f _ _ => natOffsetStuckHead p f
  | .const id _ _ =>
    id.addr == p.natAdd.addr || id.addr == p.natDiv.addr
      || id.addr == p.natMod.addr
  | _ => false

/-! ### Non-recursive WHNF helpers

These helpers used to live in the large recursive WHNF mutual block even
though none of them takes a recursive edge.  Keeping them outside that block
makes their equations transparent to the K0 proofs without adding runtime
fuel or changing their operational behavior.
-/

/-- Universe-instantiated body of an unfolded head, cached by the head
    `const` expression's content hash (lean4 C++ `m_unfold` cache). -/
def unfoldConstValue (headExpr : KExpr m) (val : KExpr m)
    (us : Array (KUniv m)) : RecM m (KExpr m) := do
  let key := headExpr.addr
  if let some cached := (← get).env.unfoldCache[key]? then
    return cached
  let result ← TcM.instantiateUnivParams val us
  modify fun s => { s with env := { s.env with
    unfoldCache := s.env.unfoldCache.insert key result } }
  return result

def tryDeltaUnfold (e : KExpr m) : RecM m (Option (KExpr m)) := do
  let (head, args) := e.collectSpine
  let .const id us _ := head | return none
  let val ← match (← TcM.tryGetConst id) with
    | some (.defn (kind := kind) (val := val) ..) =>
      match kind with
      | .defn | .thm => pure val
      | .opaq => return none
    | _ => return none
  let val ← unfoldConstValue head val us
  let mut result := val
  for arg in args do
    result ← TcM.intern (KExpr.mkApp result arg)
  return some result

/-- Delta: unfold one defined constant (head-applied or bare). -/
def deltaUnfoldOne (e : KExpr m) : RecM m (Option (KExpr m)) := do
  if let some unfolded ← tryDeltaUnfold e then
    return some unfolded
  if let .const id us _ := e then
    match (← TcM.tryGetConst id) with
    | some (.defn (kind := kind) (val := val) ..) =>
      match kind with
      | .defn | .thm => return some (← unfoldConstValue e val us)
      | .opaq => return none
    | _ => return none
  return none

/-- Transient-mode iota application: beta-reduce as we go without interning
    (Nat-literal recursor chains would otherwise pin every predecessor). -/
def applyIotaArg (result : KExpr m) (arg : KExpr m)
    (transient : Bool) : RecM m (KExpr m) := do
  if transient then
    if let .lam _ _ _ body _ := result then
      return substNoIntern body arg 0
    return KExpr.mkApp result arg
  else
    TcM.intern (KExpr.mkApp result arg)

/-- Apply an iota rule's arguments from left to right.  Keeping this loop in
    one helper makes the three argument segments in `tryIotaWithFlags`
    observationally identical while preserving the transient Nat-literal
    policy. -/
def applyIotaArgs (result : KExpr m) (args : Array (KExpr m))
    (transient : Bool) : RecM m (KExpr m) := do
  let mut result := result
  for arg in args do
    result ← applyIotaArg result arg transient
  return result

/-- Parameters, motives, and minors passed to an ordinary iota rule.  The
`min` is production's defensive truncation when a malformed recursor reports
more prefix arguments than the source spine contains. -/
def iotaPrefixArgs (recr : IotaInfo m) (spine : Array (KExpr m)) :
    Array (KExpr m) :=
  let pmmEnd := recr.params + recr.motives + recr.minors
  spine.extract 0 (min pmmEnd spine.size)

/-- Constructor fields passed to an ordinary iota rule.  Production has
already checked `ctorFields ≤ ctorArgs.size` before selecting this slice. -/
def iotaFieldArgs (ctorArgs : Array (KExpr m)) (ctorFields : Nat) :
    Array (KExpr m) :=
  ctorArgs.extract (ctorArgs.size - ctorFields) ctorArgs.size

/-- Arguments after the recursor major are retained as an over-application
suffix of the reduced rule. -/
def iotaTrailingArgs (recr : IotaInfo m) (spine : Array (KExpr m)) :
    Array (KExpr m) :=
  spine.extract (recr.majorIdx + 1) spine.size

/-- Instantiate one selected iota rule and apply exactly the three argument
segments used by `tryIotaWithFlags`.  Isolating this successful constructor
branch gives verification one production term whose indices cannot drift
from the reducer's slice arithmetic. -/
def applyIotaRule (rule : RecRule m) (recUs : Array (KUniv m))
    (recr : IotaInfo m) (spine ctorArgs : Array (KExpr m))
    (ctorFields : Nat) (transient : Bool) : RecM m (KExpr m) := do
  let rhs ← TcM.instantiateUnivParams rule.rhs recUs
  let result ← applyIotaArgs rhs (iotaPrefixArgs recr spine) transient
  let result ← applyIotaArgs result
    (iotaFieldArgs ctorArgs ctorFields) transient
  applyIotaArgs result (iotaTrailingArgs recr spine) transient

/-- Select and execute the constructor-indexed ordinary iota rule.  The
three guards are kept in production order: rule existence, universe arity,
then constructor-field availability. -/
def tryApplyIotaCtor (recr : IotaInfo m) (recUs : Array (KUniv m))
    (spine ctorArgs : Array (KExpr m)) (cidx ctorFields : Nat)
    (transient : Bool) : RecM m (Option (KExpr m)) := do
  let some rule := recr.rules[cidx]? | return none
  -- H6: level arity; H5: fields ≤ ctor args (lean4lean Reduce.lean:75-76).
  if recUs.size.toUInt64 != recr.lvls then
    return none
  if ctorFields > ctorArgs.size then
    return none
  return some (← applyIotaRule rule recUs recr spine ctorArgs ctorFields
    transient)

def isNatLiteralRecursorApp (e : KExpr m) : RecM m Bool := do
  let (head, spine) := e.collectSpine
  let .const id _ _ := head | return false
  let p ← prims
  if id.addr != p.natRec.addr && id.addr != p.natCasesOn.addr then
    return false
  let some (.recr (params := params) (motives := motives) (minors := minors)
      (indices := indices) ..) ← TcM.tryGetConst id
    | return false
  let majorIdx := (params + motives + minors + indices).toNat
  match spine[majorIdx]? with
  | some (.nat ..) => return true
  | _ => return false

/-- Nat-literal recursor work is only useful while the current WHNF runs;
    caching it would make RSS linear in the literal. -/
def isTransientNatLiteralWork (e : KExpr m) : RecM m Bool := do
  if (← isNatLiteralRecursorApp e) then
    return true
  let (head, args) := e.collectSpine
  let .const id _ _ := head | return false
  if id.addr == (← prims).natSucc.addr && args.size == 1 then
    isNatLiteralRecursorApp args[0]!
  else
    return false

/-- Lean's `cleanupNatOffsetMajor`: expose one ctor layer of a definitional
    offset `base + k` (k > 0) as `Nat.succ (base + (k-1))`, keeping closed
    arithmetic for the primitive reducer. -/
def cleanupNatOffsetMajor (e : KExpr m) :
    RecM m (Option (KExpr m)) := do
  if (← evalNatOffsetLiteral e 0).isSome then
    return none
  let some (base, offset) ← natOffset e 0 | return none
  if offset == 0 then
    return none
  let predOffset := offset - 1
  let pred ← if predOffset == 0 then pure base
    else do mkNatAdd base (natExprFromValue predOffset)
  return some (← mkNatSucc pred)

def projectDecidableFinValMinor (id : KId m) (field : UInt64)
    (minor : KExpr m) : RecM m (Option (KExpr m)) := do
  let .lam name bi dom body _ := minor | return none
  let proj ← TcM.intern (KExpr.mkPrj id field body)
  return some (← TcM.intern (KExpr.mkLam name bi dom proj))

/-- `(Decidable.rec … : Fin n).val` → push the projection into both minors
    (whnf.rs `try_reduce_fin_val_decidable_rec`). -/
def tryReduceFinValDecidableRec (id : KId m) (field : UInt64)
    (head : KExpr m) (args : Array (KExpr m)) :
    RecM m (Option (KExpr m)) := do
  if (← get).noAccel then return none
  let p ← prims
  if id.addr != p.fin.addr || field != 0 then
    return none
  let .const recId recUs _ := head | return none
  if recId.addr != p.decidableRec.addr || args.size < 5 then
    return none
  let .lam motiveName motiveBi motiveDom _ _ := args[1]! | return none
  let some falseMinor ← projectDecidableFinValMinor id field args[2]!
    | return none
  let some trueMinor ← projectDecidableFinValMinor id field args[3]!
    | return none
  let natTy ← TcM.intern (.mkConst p.nat #[])
  let motive ← TcM.intern (KExpr.mkLam motiveName motiveBi motiveDom natTy)
  let mut result ← TcM.intern (KExpr.mkConst recId recUs)
  result ← TcM.intern (KExpr.mkApp result args[0]!)
  result ← TcM.intern (KExpr.mkApp result motive)
  result ← TcM.intern (KExpr.mkApp result falseMinor)
  result ← TcM.intern (KExpr.mkApp result trueMinor)
  result ← TcM.intern (KExpr.mkApp result args[4]!)
  for arg in args.extract 5 args.size do
    result ← TcM.intern (KExpr.mkApp result arg)
  return some result

/-- Rewrite an applied projection-wrapper definition to a `prj` node. -/
def tryReduceProjectionDefinition (e : KExpr m) :
    RecM m (Option (KExpr m)) := do
  let (head, args) := e.collectSpine
  let .const id _ _ := head | return none
  let val ← match (← TcM.tryGetConst id) with
    | some (.defn (kind := .defn) (val := val) ..) => pure val
    | _ => return none
  let some (arity, structId, field, structArgIdx) :=
    projectionDefinitionInfo val | return none
  if args.size < arity then
    return none
  let mut result ← TcM.intern (KExpr.mkPrj structId field args[structArgIdx]!)
  for arg in args.extract arity args.size do
    result ← TcM.intern (KExpr.mkApp result arg)
  return some result

def natRecLiteralParts (e : KExpr m) :
    RecM m (Option (NatRecLiteralParts m)) := do
  let (head, spine) := e.collectSpine
  let .const id _ _ := head | return none
  if id.addr != (← prims).natRec.addr then
    return none
  let some (.recr (params := params) (motives := motives) (minors := minors)
      (indices := indices) ..) ← TcM.tryGetConst id
    | return none
  if minors.toNat < 2 then
    return none
  let baseIdx := params.toNat + motives.toNat
  let stepIdx := baseIdx + 1
  let majorIdx := params.toNat + motives.toNat + minors.toNat + indices.toNat
  let some (.nat major _ _) := spine[majorIdx]? | return none
  return some { spine, major, baseIdx, stepIdx, majorIdx }

/-- Heads that leave a Nat-predicate argument stuck. -/
def isNatStuckRecursorAddr (addr : Address) : RecM m Bool := do
  let p ← prims
  return addr == p.natRec.addr || addr == p.natCasesOn.addr
    || addr == p.bitVecToNat.addr

def isStuckNatPredicateProbe (e : KExpr m) : RecM m Bool := do
  let (head, _) := e.collectSpine
  match head with
  | .const id _ _ =>
    return (← isNatBinPredAddr id.addr) || (← isNatStuckRecursorAddr id.addr)
  | .prj id _ val _ =>
    if id.addr == (← prims).fin.addr then
      return true
    let (valHead, _) := val.collectSpine
    match valHead with
    | .const valId _ _ => isNatStuckRecursorAddr valId.addr
    | _ => return false
  | _ => return false

/-- `(width, n)` from `BitVec.ofNat width n` or
    `OfNat.ofNat (BitVec width) n inst…`. -/
def bitvecOfNatArgs (e : KExpr m) :
    RecM m (Option (KExpr m × KExpr m)) := do
  let p ← prims
  let (head, args) := e.collectSpine
  let .const id _ _ := head | return none
  if id.addr == p.bitVecOfNat.addr && args.size == 2 then
    return some (args[0]!, args[1]!)
  if id.addr != p.ofNatOfNat.addr || args.size < 2 then
    return none
  let (typeHead, typeArgs) := args[0]!.collectSpine
  let .const typeId _ _ := typeHead | return none
  if typeId.addr == p.bitVec.addr && typeArgs.size == 1 then
    return some (typeArgs[0]!, args[1]!)
  return none

def charOfNatExpr (n : Nat) : RecM m (Option (KExpr m)) := do
  let charOfNat ← TcM.intern (.mkConst (← prims).charOfNat #[])
  let natLit ← TcM.intern (natExprFromValue n : KExpr m)
  return some (← TcM.intern (KExpr.mkApp charOfNat natLit))

/-- Reduce an already recognized String literal under a constant head.  This
named seam keeps the literal cases independently verifiable while preserving
the original primitive tests and intern order. -/
def tryReduceStringLiteral (p : Primitives m) (id : KId m)
    (s : String) : RecM m (Option (KExpr m)) := do
  let isUtf8ByteSize := id.addr == p.stringUtf8ByteSize.addr
  let isToByteArray := id.addr == p.stringToByteArray.addr
  if isUtf8ByteSize then
    return some (← TcM.intern (natExprFromValue s.utf8ByteSize : KExpr m))
  if isToByteArray then
    if s.isEmpty then
      return some (← TcM.intern (.mkConst p.byteArrayEmpty #[]))
    return none
  let codepoint := (s.toList.getLast?.map (·.toNat)).getD 65
  charOfNatExpr codepoint

/-- String literal primitives: `String.back` / legacy back /
    `utf8ByteSize` / `toByteArray ""`. -/
def tryReduceString (e : KExpr m) : RecM m (Option (KExpr m)) := do
  let (head, args) := e.collectSpine
  if args.size != 1 then
    return none
  let .const id _ _ := head | return none
  let p ← prims
  let isBack := id.addr == p.stringBack.addr
    || id.addr == p.stringLegacyBack.addr
  let isUtf8ByteSize := id.addr == p.stringUtf8ByteSize.addr
  let isToByteArray := id.addr == p.stringToByteArray.addr
  if !isBack && !isUtf8ByteSize && !isToByteArray then
    return none
  let .str s _ _ := args[0]! | return none
  tryReduceStringLiteral p id s

def discoverBlockInductives (blockId : KId m) :
    RecM m (Array (KId m)) := do
  let some members ← TcM.tryGetBlock blockId | return #[]
  let mut inds : Array (KId m) := #[]
  for id in members do
    if let some (.indc ..) ← TcM.tryGetConst id then
      inds := inds.push id
  return inds

/-- Peel as many leading lambdas as there are application arguments. The
    explicit bound is the original argument count, so the old inner `repeat`
    cannot outlive its spine. -/
def consumeBetaLamsFuel : Nat → KExpr m → Array (KExpr m) →
    Array (KExpr m) → KExpr m × Array (KExpr m)
  | 0, body, _, consumed => (body, consumed)
  | fuel + 1, body, args, consumed =>
    if consumed.size ≥ args.size then
      (body, consumed)
    else
      match body with
      | .lam _ _ _ inner _ =>
        consumeBetaLamsFuel fuel inner args
          (consumed.push args[consumed.size]!)
      | _ => (body, consumed)

def consumeBetaLams (body : KExpr m) (args : Array (KExpr m)) :
    KExpr m × Array (KExpr m) :=
  consumeBetaLamsFuel args.size body args (Array.mkEmpty args.size)

/-- Internal WHNF back-edges. Each crosses to the predecessor `methodsN`
    table without changing the runtime state; the policy-sensitive entries
    preserve cheap-projection and stuck-succ behavior exactly. -/
@[inline] def whnfRec (e : KExpr m) : RecM m (KExpr m) := do
  (← read).whnf e

@[inline] def whnfModeRec (e : KExpr m) (mode : NatSuccMode) :
    RecM m (KExpr m) := do
  (← read).whnfMode e mode

@[inline] def whnfCoreFlagsRec (e : KExpr m) (flags : WhnfFlags) :
    RecM m (KExpr m) := do
  (← read).whnfCoreFlags e flags

/-- Inference back-edge under the validation policy used by K synthesis and
other WHNF probes.  Naming this seam exposes the caught callback as one
operation while preserving the original method-table read and state scope. -/
@[inline] def inferOnlyRec (e : KExpr m) : RecM m (KExpr m) := do
  let methods ← read
  TcM.withInferOnly (methods.infer e)

/-- Catch a WHNF probe error as absence while retaining its error-side state,
matching Rust's `&mut` catch-and-continue behavior. -/
@[inline] def tryOptional (x : RecM m α) : RecM m (Option α) :=
  try? x

/-- The result of the pure front-end classifier for native reduction.  A
completed plan returns immediately; a marker plan still has to pass the
stateful re-entrancy guard before its argument can be reduced. -/
inductive NativeReductionPlan (m : Mode) where
  | done (result : Option (KExpr m))
  | marker (isReduceBool : Bool) (arg : KExpr m)

mutual

/-- Full WHNF: loop of whnf-no-delta → native/nat/decidable/string → delta. -/
def whnf (e : KExpr m) : RecM m (KExpr m) :=
  whnfWithNatSuccMode e .collapse

def whnfWithNatSuccMode (e : KExpr m) (natSuccMode : NatSuccMode) :
    RecM m (KExpr m) := do
  -- Quick exit for non-reducing forms.
  match e with
  | .sort .. | .all .. | .lam .. | .nat .. | .str .. => return e
  | .var i _ _ =>
    if !(← TcM.isLetVar (m := m) i) then return e
  | _ => pure ()
  whnfWithNatSuccModeNonLeaf e natSuccMode

/-- One full-WHNF loop iteration.  The named seam exposes the exact order of
    no-delta normalization, cycle detection, accelerators, literal reducers,
    and one delta step without changing the bounded driver. -/
def whnfWithNatSuccModeStep (natSuccMode : NatSuccMode)
    (state : KExpr m × HashSet Address) :
    RecM m (BoundedStep (KExpr m × HashSet Address) (KExpr m)) := do
  let (cur, seen) := state
  let cur ← whnfNoDeltaImpl cur .FULL natSuccMode
  if seen.contains cur.addr then
    return .done cur
  let seen := seen.insert cur.addr
  -- Native reduction runs before nat reduction (lean4lean order).
  if let some reduced ← tryReduceNative cur then
    return .next (reduced, seen)
  if let some reduced ← tryReduceBitvec cur then
    return .next (reduced, seen)
  -- Nat primitives BEFORE delta (short-circuit Nat.sub/pow/… bodies).
  if let some reduced ← tryReduceNatWithSuccMode cur natSuccMode then
    return .next (reduced, seen)
  -- Nat decidables BEFORE delta.
  if let some reduced ← tryReduceDecidable cur then
    return .next (reduced, seen)
  if let some reduced ← tryReduceString cur then
    return .next (reduced, seen)
  -- Keep `Nat.add base (Lit n)` (symbolic base, n > 0) and
  -- `Nat.div/mod base (Lit k)` (k ≥ 2) STUCK as a compact offset instead
  -- of delta-unfolding: `Nat.add` would materialize succ^n(base) — O(n)
  -- substitution per layer — and `Nat.div/mod` would expand the division
  -- algorithm, even though both are irreducible for a symbolic base.
  -- Iota over such a major still works via `cleanupNatOffsetMajor`;
  -- def-eq decides offset pairs in `tryDefEqOffset`.
  if let some stuck ← tryNatOffsetStuck cur then
    return .done stuck
  if let some unfolded ← deltaUnfoldOne cur then
    return .next (unfolded, seen)
  return .done cur

/-- Full-WHNF bounded loop without the outer instrumentation/cache policy. -/
def whnfWithNatSuccModeUncached (e : KExpr m)
    (natSuccMode : NatSuccMode) : RecM m (KExpr m) :=
  runBounded (whnfWithNatSuccModeStep natSuccMode) maxWhnfFuel.toNat (e, {})

/-- Trace/statistics prefix executed by full WHNF after syntactic fast paths
    and before key computation. -/
def whnfWithNatSuccModePrefix (e : KExpr m) : RecM m Unit := do
  TcM.stepTrace (m := m) "whnf+" fun _ => TcM.addr8 e.addr
  TcM.bumpStats (m := m) fun s => { s with whnfCalls := s.whnfCalls + 1 }

/-- Work charged only after a full-WHNF cache miss. -/
def whnfWithNatSuccModeMissCharge : RecM m Unit := do
  TcM.bumpStats (m := m) fun s => { s with whnfMisses := s.whnfMisses + 1 }
  TcM.tick (m := m)

/-- Instrumented/keyed full-WHNF body reached after the public syntactic fast
    paths.  Naming it makes the cache and fuel boundary equation-visible. -/
def whnfWithNatSuccModeNonLeaf (e : KExpr m)
    (natSuccMode : NatSuccMode) : RecM m (KExpr m) := do
  whnfWithNatSuccModePrefix e
  let key ← TcM.whnfKey e
  let useCache := natSuccMode == .collapse
  let transientNatWork ← isTransientNatLiteralWork e
  if useCache && !transientNatWork then
    if let some cached := (← get).env.whnfCache[key]? then
      return cached
  -- Tick AFTER fast paths and cache: only consume fuel for actual work.
  whnfWithNatSuccModeMissCharge
  let cur ← whnfWithNatSuccModeUncached e natSuccMode
  if !(← get).inNativeReduce && useCache && !transientNatWork then
    modify fun s => { s with env := { s.env with
      whnfCache := s.env.whnfCache.insert key cur } }
  return cur

/-- Structural WHNF (beta/iota/zeta/proj), NO delta, FULL flags. -/
def whnfCore (e : KExpr m) : RecM m (KExpr m) :=
  whnfCoreWithFlags e .FULL

/-- Run one cheap recursive reduction scope.  Cheap-mode cache routing is
visible only while the body executes; the caller's depth is restored on both
success and error. -/
def withCheapRecursionDepth (x : RecM m α) : RecM m α := do
  modify fun s => { s with cheapRecursionDepth := s.cheapRecursionDepth + 1 }
  try
    x
  finally
    modify fun s => { s with cheapRecursionDepth := s.cheapRecursionDepth - 1 }

/-- Structural WHNF for def-eq's cheap-projection scaffold
    (`whnfCore (cheapProj := true)`). Bumps `cheapRecursionDepth` so cheap
    false negatives stay out of the full def-eq cache. -/
def whnfCoreForDefEq (e : KExpr m) : RecM m (KExpr m) :=
  withCheapRecursionDepth (whnfCoreWithFlags e .DEF_EQ_CORE)

/-- Key/cache/uncached body reached after structural-WHNF's syntactic fast
paths.  Naming this seam leaves runtime behavior unchanged while allowing the
outer cache policy to be verified independently of leaf/variable dispatch. -/
def whnfCoreWithFlagsNonLeaf (e : KExpr m) (flags : WhnfFlags) :
    RecM m (KExpr m) := do
  let key ← TcM.whnfKey e
  let transientNatWork ← isTransientNatLiteralWork e
  if flags.isFull then
    if !transientNatWork then
      if let some cached := (← get).env.whnfCoreCache[key]? then
        return cached
    let result ← whnfCoreWithFlagsUncached e flags
    if !transientNatWork then
      modify fun s => { s with env := { s.env with
        whnfCoreCache := s.env.whnfCoreCache.insert key result } }
    return result
  else
    if !transientNatWork then
      if let some cached := (← get).env.whnfCoreCheapCache[key]? then
        return cached
    let result ← whnfCoreWithFlagsUncached e flags
    if !transientNatWork then
      modify fun s => { s with env := { s.env with
        whnfCoreCheapCache := s.env.whnfCoreCheapCache.insert key result } }
    return result

def whnfCoreWithFlags (e : KExpr m) (flags : WhnfFlags) :
    RecM m (KExpr m) := do
  -- Leaves whnf_core never reduces (incl. `const` — no delta here); `var`
  -- only when no let frame can zeta it.
  match e with
  | .sort .. | .all .. | .lam .. | .nat .. | .str .. | .const .. => return e
  | .var i _ _ =>
    if !(← TcM.isLetVar (m := m) i) then return e
  | _ => pure ()
  whnfCoreWithFlagsNonLeaf e flags

/-- One structural-WHNF loop iteration.  Naming the step keeps the bounded
driver unchanged while exposing a stable verification seam for individual
reduction branches. -/
def whnfCoreWithFlagsStep (cur : KExpr m) (flags : WhnfFlags) :
    RecM m (BoundedStep (KExpr m) (KExpr m)) := do
    match cur with
    | .var i _ _ =>
      -- Legacy let-bound variable zeta-reduction.
      match (← TcM.lookupLetVal (m := m) i) with
      | some val => return .next val
      | none => return .done cur
    | .fvar id _ _ =>
      -- Let-bound fvar zeta-reduction (lean4lean `whnfFVar`).
      match (← get).lctx.find? id with
      | some (.ldecl _ _ val) => return .next val
      | _ => return .done cur
    | .sort .. | .all .. | .lam .. | .nat .. | .str .. | .const .. =>
      return .done cur
    | .prj id field val _ =>
      -- FULL: full whnf on the struct value (delta may expose a ctor).
      -- CHEAP: structural only; stuck projections stay stuck.
      let wval ← if flags.cheapProj then whnfCoreFlagsRec val flags
        else whnfRec val
      match (← tryProjReduce id field wval) with
      | some result => return .next result
      | none => return .done cur
    | .letE _ _ val body _ _ =>
      return .next (← TcM.runIntern (subst body val 0))
    | .app .. => pure ()
    -- App: collect spine, whnf-core the head, beta / iota.
    let (f0, args) := cur.collectSpine
    let f ← whnfCoreFlagsRec f0 flags
    if let .lam .. := f then
      -- Multi-arg beta.
      let (body₀, consumedArgs) := consumeBetaLams f args
      let mut body := body₀
      let remainingStart := consumedArgs.size
      if !consumedArgs.isEmpty then
        body ← TcM.runIntern (simulSubst body consumedArgs.reverse 0)
      body ← finishAppResult body args remainingStart
      return .next body
    if f != f0 then
      -- Head reduced: rebuild, try iota once, else done.
      let rebuilt ← finishAppResult f args 0
      match (← tryIotaWithFlags rebuilt flags) with
      | some reduced => return .next reduced
      | none => return .done rebuilt
    match (← tryIotaWithFlags cur flags) with
    | some reduced => return .next reduced
    | none => return .done cur

def whnfCoreWithFlagsUncached (e : KExpr m) (flags : WhnfFlags) :
    RecM m (KExpr m) :=
  runBounded (fun cur => whnfCoreWithFlagsStep cur flags)
    maxWhnfFuel.toNat e

/-- WHNF without delta: whnf-core → proj-app → nat/native/string → quot. -/
def whnfNoDelta (e : KExpr m) : RecM m (KExpr m) :=
  whnfNoDeltaImpl e .FULL .collapse

/-- Def-eq no-delta WHNF (cheap projection policy). -/
def whnfNoDeltaForDefEq (e : KExpr m) : RecM m (KExpr m) :=
  withCheapRecursionDepth
    (whnfNoDeltaImpl e .DEF_EQ_CORE .collapse)

/-- Ordered reducer tail of one no-delta iteration, after structural WHNF has
    completed.  Naming this seam makes the helper precedence and partial
    error states independently verifiable without changing the bounded loop. -/
def whnfNoDeltaReducersStep (flags : WhnfFlags)
    (natSuccMode : NatSuccMode) (cur : KExpr m) :
    RecM m (BoundedStep (KExpr m) (KExpr m)) := do
  -- App-of-Prj: whnf_core resolves the outermost Prj only; give the
  -- head one more attempt under the same projection policy.
  if let some result ← tryProjAppReduceFinished cur flags then
    return .next result
  if let some reduced ← tryReduceBitvec cur then
    return .next reduced
  if let some reduced ← tryReduceNatWithSuccMode cur natSuccMode then
    return .next reduced
  -- Native/string before projection-definition rewriting (wrappers like
  -- Subtype.val are projection definitions; once rewritten to Prj the
  -- recognizers no longer see the head).
  if let some reduced ← tryReduceNative cur then
    return .next reduced
  if let some reduced ← tryReduceString cur then
    return .next reduced
  if flags.isFull then
    if let some reduced ← tryReduceProjectionDefinition cur then
      return .next reduced
  if let some reduced ← tryQuotReduce cur then
    return .next reduced
  return .done cur

/-- One no-delta WHNF loop iteration, in the precise production reducer
    order.  Successful syntax-directed helpers remain visible as `.next`;
    a fully stuck structural result terminates the loop. -/
def whnfNoDeltaImplStep (flags : WhnfFlags) (natSuccMode : NatSuccMode)
    (cur : KExpr m) : RecM m (BoundedStep (KExpr m) (KExpr m)) := do
  let cur ← whnfCoreWithFlags cur flags
  whnfNoDeltaReducersStep flags natSuccMode cur

/-- No-delta bounded loop without its outer cache policy. -/
def whnfNoDeltaImplUncached (e : KExpr m) (flags : WhnfFlags)
    (natSuccMode : NatSuccMode) : RecM m (KExpr m) :=
  runBounded (whnfNoDeltaImplStep flags natSuccMode) maxWhnfFuel.toNat e

/-- Key/cache/uncached no-delta body reached after syntactic fast paths. -/
def whnfNoDeltaImplNonLeaf (e : KExpr m) (flags : WhnfFlags)
    (natSuccMode : NatSuccMode) : RecM m (KExpr m) := do
  let key ← TcM.whnfKey e
  let useCache := natSuccMode == .collapse
  let transientNatWork ← isTransientNatLiteralWork e
  if useCache && !transientNatWork then
    if flags.isFull then
      if let some cached := (← get).env.whnfNoDeltaCache[key]? then
        return cached
    else
      if let some cached := (← get).env.whnfNoDeltaCheapCache[key]? then
        return cached
  let cur ← whnfNoDeltaImplUncached e flags natSuccMode
  if !(← get).inNativeReduce && useCache && !transientNatWork then
    if flags.isFull then
      modify fun s => { s with env := { s.env with
        whnfNoDeltaCache := s.env.whnfNoDeltaCache.insert key cur } }
    else
      modify fun s => { s with env := { s.env with
        whnfNoDeltaCheapCache := s.env.whnfNoDeltaCheapCache.insert key cur } }
  return cur

def whnfNoDeltaImpl (e : KExpr m) (flags : WhnfFlags)
    (natSuccMode : NatSuccMode) : RecM m (KExpr m) := do
  match e with
  | .sort .. | .all .. | .lam .. | .nat .. | .str .. => return e
  | .var i _ _ =>
    if !(← TcM.isLetVar (m := m) i) then return e
  | _ => pure ()
  whnfNoDeltaImplNonLeaf e flags natSuccMode

/-- Dispatch an already normalized, non-String major either to an ordinary
constructor rule or to struct eta.  Literal conversion and cleanup live in
`tryIotaAfterMajorWhnf`, so this seam owns only constructor lookup and the
final fallback. -/
def tryIotaCtorOrStructEta (recId : KId m) (recr : IotaInfo m)
    (recUs : Array (KUniv m)) (spine : Array (KExpr m))
    (majorWhnf : KExpr m) (transient : Bool) :
    RecM m (Option (KExpr m)) := do
  let (ctorHead, ctorArgs) := majorWhnf.collectSpine
  let ctorInfo? ← match ctorHead with
    | .const cid _ _ =>
      match (← TcM.tryGetConst cid) with
      | some ctor => pure ctor.iotaCtorInfo?
      | _ => pure none
    | _ => pure none
  if let some (cidx, ctorFields) := ctorInfo? then
    return ← tryApplyIotaCtor recr recUs spine ctorArgs cidx ctorFields
      transient
  tryStructEtaIota recId recr recUs spine

/-- Dispatch after Nat-offset cleanup.  String literals require constructor
expansion plus one policy-selected recursive WHNF callback; every other
shape proceeds directly to constructor/struct-eta selection. -/
def tryIotaAfterCleanup (flags : WhnfFlags) (recId : KId m)
    (recr : IotaInfo m) (recUs : Array (KUniv m))
    (spine : Array (KExpr m)) (majorWhnf : KExpr m)
    (majorWasNatLit : Bool) : RecM m (Option (KExpr m)) := do
  let mut majorWhnf := majorWhnf
  match majorWhnf with
  | .str val _ _ =>
    let strCtor ← strLitToConstructor val
    majorWhnf ← if flags.cheapRec then whnfCoreFlagsRec strCtor flags
      else whnfRec strCtor
  | _ => pure ()
  tryIotaCtorOrStructEta recId recr recUs spine majorWhnf majorWasNatLit

/-- Finish iota preprocessing after the major callback.  This seam owns Nat
literal expansion, the second offset cleanup, String expansion, and then the
constructor/struct-eta dispatch above. -/
def tryIotaAfterMajorWhnf (flags : WhnfFlags) (recId : KId m)
    (recr : IotaInfo m) (recUs : Array (KUniv m))
    (spine : Array (KExpr m)) (majorWhnf0 : KExpr m) :
    RecM m (Option (KExpr m)) := do
  -- Nat literal → constructor form (one layer).
  let mut majorWhnf := majorWhnf0
  let mut majorWasNatLit := false
  match majorWhnf with
  | .nat val _ _ =>
    majorWasNatLit := true
    majorWhnf ← natToConstructor val
  | _ => pure ()
  if let some cleaned ← cleanupNatOffsetMajor majorWhnf then
    majorWhnf := cleaned
  -- String literal → constructor form, then WHNF (same flag policy).
  tryIotaAfterCleanup flags recId recr recUs spine majorWhnf majorWasNatLit

/-- Iota: recursor applied to a constructor (or K-synthesized / struct-eta
    fallback). `cheapRec` reduces the major structurally only. -/
def tryIotaWithFlags (e : KExpr m) (flags : WhnfFlags) :
    RecM m (Option (KExpr m)) := do
  let (head, spine) := e.collectSpine
  let .const recId recUs _ := head | return none
  let some recursor ← TcM.tryGetConst recId | return none
  let some recr := recursor.iotaInfo? | return none
  if spine.size ≤ recr.majorIdx then
    return none
  -- K-like: synthesize a nullary ctor from the major's type before WHNF.
  let major := spine[recr.majorIdx]!
  let major ← if recr.k then
      pure ((← synthCtorWhenK major recId recr recUs).getD major)
    else pure major
  let major := (← cleanupNatOffsetMajor major).getD major
  -- WHNF the major (cheap mode skips delta on the major itself).
  let majorWhnf0 ← if flags.cheapRec then whnfCoreFlagsRec major flags
    else whnfRec major
  tryIotaAfterMajorWhnf flags recId recr recUs spine majorWhnf0

def isStructLike (id : KId m) : RecM m Bool := do
  match (← TcM.tryGetConst id) with
  | some (.indc (indices := indices) (ctors := ctors) ..) =>
    if indices != 0 || ctors.size != 1 then
      return false
  | _ => return false
  return !(← computedIsRec id)

/-- Intern the projection/application pairs for a contiguous struct field
range.  The explicit remaining-field index makes totality and left-to-right
state threading visible while retaining the old loop's exact request order. -/
def finishStructEtaFields (indId : KId m) (major : KExpr m) :
    Nat → Nat → KExpr m → RecM m (KExpr m)
  | 0, _, result => pure result
  | fuel + 1, field, result => do
      let proj ← TcM.intern (KExpr.mkPrj indId field.toUInt64 major)
      let result ← TcM.intern (KExpr.mkApp result proj)
      finishStructEtaFields indId major fuel (field + 1) result

/-- Rebuild the struct-eta recursor result after all semantic guards have
passed.  The three named left-to-right segments preserve the generated
expression and intern order of the former imperative loops. -/
def finishStructEtaResult (indId : KId m) (major rhs : KExpr m)
    (fields : UInt64) (prefixArgs trailingArgs : Array (KExpr m)) :
    RecM m (KExpr m) := do
  let result ← finishAppResult rhs prefixArgs 0
  let result ← finishStructEtaFields indId major fields.toNat 0 result
  finishAppResult result trailingArgs 0

/-- The H3 post-probe guard rejects exactly `Prop`-valued majors.  Keeping
this test pure makes the semantic boundary independently inspectable without
moving any checker effects across it. -/
def structEtaSortRejected : KExpr m → Bool
  | .sort u _ => u.isZero
  | _ => false

/-- Apply the H3 Prop guard and, for an admissible major sort, instantiate
and rebuild the selected struct-eta rule. -/
def finishStructEtaAfterSort (recUs : Array (KUniv m))
    (spine : Array (KExpr m)) (recr : IotaInfo m) (rule : RecRule m)
    (indId : KId m) (major majorSortW : KExpr m) :
    RecM m (Option (KExpr m)) := do
  if structEtaSortRejected majorSortW then
    return none
  let rhs ← TcM.instantiateUnivParams rule.rhs recUs
  let pmmEnd := recr.params + recr.motives + recr.minors
  let result ← finishStructEtaResult indId major rhs rule.fields
    (spine.extract 0 (min pmmEnd spine.size))
    (spine.extract (recr.majorIdx + 1) spine.size)
  return some result

/-- Complete struct-eta after the recursor type scan has selected the major
inductive.  Optional inference/WHNF probes retain their error-side state;
universe instantiation and rebuilding errors remain ordinary propagated
errors. -/
def tryStructEtaAfterInductive (recUs : Array (KUniv m))
    (spine : Array (KExpr m)) (recr : IotaInfo m) (rule : RecRule m)
    (indId : KId m) : RecM m (Option (KExpr m)) := do
  if !(← isStructLike indId) then
    return none
  -- H3: Prop guard.
  let major := spine[recr.majorIdx]!
  let some majorTy ← tryOptional (inferOnlyRec major) | return none
  let some majorSort ← tryOptional (inferOnlyRec majorTy) | return none
  let some majorSortW ← tryOptional (whnfRec majorSort) | return none
  finishStructEtaAfterSort recUs spine recr rule indId major majorSortW

/-- Struct-eta iota: single-rule recursor over a non-recursive one-ctor
    zero-index inductive; rebuild the rule with projections of the major.
    Prop-typed majors are excluded (lean4lean `toCtorWhenStruct`). -/
def tryStructEtaIota (recId : KId m) (recr : IotaInfo m)
    (recUs : Array (KUniv m)) (spine : Array (KExpr m)) :
    RecM m (Option (KExpr m)) := do
  if recr.rules.size != 1 then
    return none
  if recUs.size.toUInt64 != recr.lvls then
    return none
  let rule := recr.rules[0]!
  let recTy ← match (← TcM.tryGetConst recId) with
    | some c => pure c.ty
    | none => return none
  let skip := (recr.params + recr.motives + recr.minors + recr.indices).toUInt64
  let some indId ← tryOptional (do
    -- The stored declaration type is polymorphic in the recursor's own
    -- universe parameters.  Scan the instance named by this application,
    -- not that raw declaration under the caller's unrelated universe scope.
    let recTy ← TcM.instantiateUnivParams recTy recUs
    getMajorInductiveId recTy skip) | return none
  tryStructEtaAfterInductive recUs spine recr rule indId

/-- Build one K-synthesis constructor candidate and validate that its inferred
type is definitionally equal to the normalized major type.  Catalog selection
stays in `synthCtorWhenK`; this seam owns all intern, stats, and final DefEq
effects, including the counted silent rejection. -/
def verifyKSynthCandidate (majorTyW : KExpr m) (ctorId : KId m)
    (tyUs : Array (KUniv m)) (tyArgs : Array (KExpr m)) (params : Nat) :
    RecM m (Option (KExpr m)) := do
  let ctorApp ← TcM.intern (KExpr.mkConst ctorId tyUs)
  let ctorApp ← finishAppResult ctorApp
    (tyArgs.extract 0 (min params tyArgs.size)) 0
  let some ctorTy ← tryOptional (inferOnlyRec ctorApp)
    | return none
  TcM.bumpStats (m := m) fun s =>
    { s with kSynthAttempts := s.kSynthAttempts + 1 }
  if !(← callIsDefEq majorTyW ctorTy) then
    -- Silent fallback (the caller keeps the stuck major — `.getD major`;
    -- Rust parity: `.unwrap_or_else`). Counted so reject totals can be
    -- compared cross-kernel (IX_TC_STATS ↔ Rust IX_KSYNTH_LOG).
    TcM.bumpStats (m := m) fun s =>
      { s with kSynthRejects := s.kSynthRejects + 1 }
    return none
  return some ctorApp

/-- Finish K-synthesis after the recursor scan has selected its major
inductive.  Naming this defensive catalog transaction exposes the address
check, repeated inductive lookup, empty-constructor fallback, and candidate
result without changing their order or state scope. -/
def selectKSynthCandidate (majorTyW : KExpr m) (tyHeadId : KId m)
    (tyUs : Array (KUniv m)) (tyArgs : Array (KExpr m))
    (indId : KId m) (params : Nat) : RecM m (Option (KExpr m)) := do
  if tyHeadId.addr != indId.addr then
    return none
  let ctorId ← match (← TcM.tryGetConst indId) with
    | some (.indc (ctors := ctors) ..) =>
      match ctors[0]? with
      | some c => pure c
      | none => return none
    | _ => return none
  verifyKSynthCandidate majorTyW ctorId tyUs tyArgs params

/-- K-like recursors: when the major isn't a ctor but its type matches the
    target inductive, build `ctor₀ params…` and def-eq-verify its type. -/
def synthCtorWhenK (major : KExpr m) (recId : KId m)
    (recr : IotaInfo m) (recUs : Array (KUniv m)) :
    RecM m (Option (KExpr m)) := do
  if recUs.size.toUInt64 != recr.lvls then
    return none
  let some majorTy ← tryOptional (inferOnlyRec major)
    | return none
  let some majorTyW ← tryOptional (whnfRec majorTy) | return none
  let (tyHead, tyArgs) := majorTyW.collectSpine
  let .const tyHeadId tyUs _ := tyHead | return none
  let recTy ← match (← TcM.tryGetConst recId) with
    | some c => pure c.ty
    | none => return none
  let skip := (recr.params + recr.motives + recr.minors + recr.indices).toUInt64
  let some indId ← tryOptional (do
    let recTy ← TcM.instantiateUnivParams recTy recUs
    getMajorInductiveId recTy skip) | return none
  selectKSynthCandidate majorTyW tyHeadId tyUs tyArgs indId recr.params

/- Projection reduction is split at the String-literal preprocessing
boundary.  Besides giving verification an induction-free seam, this keeps
the accelerated `Fin.val` probe and lazy constructor lookup in one tail whose
evaluation order is shared by literal and non-literal inputs. -/

/-- Projection tail after any String-literal expansion and recursive WHNF. -/
def tryProjReduceTail (id : KId m) (field : UInt64) (wval : KExpr m) :
    RecM m (Option (KExpr m)) := do
  let (head, args) := wval.collectSpine
  if let some result ← tryReduceFinValDecidableRec id field head args then
    return some result
  let .const ctorId _ _ := head | return none
  let ctorParams ← match (← TcM.tryGetConst ctorId) with
    | some (.ctor (params := params) ..) => pure params.toNat
      | _ => return none
  return args[ctorParams + field.toNat]?

/-- Normalize only the String-literal input form used by projection. -/
def tryProjPrepare (wval : KExpr m) : RecM m (KExpr m) :=
  match wval with
  | .str s _ _ => do
      let expanded ← strLitToConstructor s
      whnfRec expanded
  | _ => pure wval

/-- Projection of a ctor application (with string-literal expansion first,
    and the `Fin.val`-through-`Decidable.rec` special case). -/
def tryProjReduce (id : KId m) (field : UInt64) (wval : KExpr m) :
    RecM m (Option (KExpr m)) := do
  let wval ← tryProjPrepare wval
  tryProjReduceTail id field wval

/-- `App(Prj(S, i, v), args…)`: one more projection attempt on the head. -/
def tryProjAppReduce (e : KExpr m) (flags : WhnfFlags) :
    RecM m (Option (KExpr m × Array (KExpr m))) := do
  let (head, args) := e.collectSpine
  if args.isEmpty then
    return none
  let .prj id field val _ := head | return none
  let wval ← if flags.cheapProj then whnfCoreFlagsRec val flags
    else whnfRec val
  match (← tryProjReduce id field wval) with
  | some result => return some (result, args)
  | none => return none

/-- Complete the app-of-projection reduction by rebuilding the full trailing
    spine through the shared, left-to-right application helper. -/
def tryProjAppReduceFinished (e : KExpr m) (flags : WhnfFlags) :
    RecM m (Option (KExpr m)) := do
  match (← tryProjAppReduce e flags) with
  | some (projResult, args) =>
    return some (← finishAppResult projResult args 0)
  | none => return none

/-- Peel the fixed recursor prefix before searching for the major premise. -/
def peelMajorForalls : Nat → KExpr m → RecM m (KExpr m)
  | 0, ty => pure ty
  | fuel + 1, ty => do
    let w ← whnfRec ty
    match w with
    | .all _ _ dom body _ =>
      -- The body is open.  Retain the binder in the legacy context so a
      -- recursive WHNF cannot resolve one of its variables through an
      -- unrelated caller frame.
      TcM.pushLocal dom
      peelMajorForalls fuel body
    | _ => throw (.other "get_major_inductive_id: not enough foralls")

/-- One successful-WHNF step of the bounded major-inductive scan.  Naming the
step keeps the callback boundary and the binder-scoped continuation visible to
verification without changing lookup or error order. -/
def scanMajorInductiveStep
    (next : KExpr m → RecM m (KId m)) (w : KExpr m) : RecM m (KId m) := do
  match w with
  | .all _ _ dom body _ =>
    let (head, _) := dom.collectSpine
    if let .const id _ _ := head then
      if let some (.indc ..) ← TcM.tryGetConst id then
        return id
    -- Continue underneath the forall in the context in which its body is
    -- scoped.  `getMajorInductiveId` restores the caller depth on every
    -- outcome.
    TcM.pushLocal dom
    next body
  | _ => throw (.other "get_major_inductive_id: expected forall at major")

/-- Bounded search for the first forall whose domain head is a loaded
inductive.  The recursive presentation preserves the former loop's exact
left-to-right lookup and error order. -/
def scanMajorInductive : Nat → KExpr m → RecM m (KId m)
  | 0, _ => throw (.other
      "get_major_inductive_id: no inductive-headed forall within scan bound")
  | fuel + 1, ty => do
    let w ← whnfRec ty
    scanMajorInductiveStep (scanMajorInductive fuel) w

/-- Major-premise inductive of a recursor type: peel `skip` foralls, then
    scan (bounded) for the first forall whose domain head is an inductive. -/
def getMajorInductiveId (recTy : KExpr m) (skip : UInt64) :
    RecM m (KId m) := do
  let saved ← liftM (TcM.saveDepth (m := m))
  try
    let ty ← peelMajorForalls skip.toNat recTy
    scanMajorInductive 9 ty
  finally
    liftM (TcM.restoreDepth (m := m) saved)

/-- Nat primitives: succ-collapse, binary arithmetic, boolean predicates. -/
def tryReduceNat (e : KExpr m) : RecM m (Option (KExpr m)) :=
  tryReduceNatWithSuccMode e .collapse

def tryReduceNatWithSuccMode (e : KExpr m)
    (natSuccMode : NatSuccMode) : RecM m (Option (KExpr m)) := do
  let (head, args) := e.collectSpine
  let .const id _ _ := head | return none
  let addr := id.addr
  let p ← prims
  if addr == p.natSucc.addr && args.size == 1 then
    if natSuccMode == .stuck then
      return none
    return (← tryReduceNatSuccIter args[0]!)
  if args.size < 2 then
    return none
  let isBinArith ← isNatBinArithAddr addr
  let isBinPred ← isNatBinPredAddr addr
  if !isBinArith && !isBinPred then
    return none
  if isBinPred then
    return (← tryReduceNatPredicate addr args)
  let some wa ← whnfNatReducerArg args[0]! | return none
  let some wb ← whnfNatReducerArg args[1]! | return none
  let some aVal := extractNatLit wa p | return none
  let some bVal := extractNatLit wb p | return none
  let resultExpr ← if isBinArith then
      match computeNatBin addr PrimAddrs.canonical aVal bVal with
      | some r => pure (natExprFromValue r)
      | none => return none
    else
      let b := if addr == p.natBeq.addr then aVal == bVal else aVal.ble bVal
      TcM.intern (.mkConst (if b then p.boolTrue else p.boolFalse) #[])
  finishAppResult resultExpr args 2

/-- Recognize exactly one `Nat.succ` application after recursive WHNF.  The
    helper retains the production's second primitive-table read while making
    its Boolean branch independently equation-visible. -/
def isNatSuccSpine (w : KExpr m) : RecM m Bool := do
  let (head, args) := w.collectSpine
  match head with
  | .const id _ _ =>
    pure (id.addr == (← prims).natSucc.addr && args.size == 1)
  | _ => pure false

/-- Commit the finite set of successor arguments proved stuck by one loop
    execution.  Both stuck exits share this exact state mutation. -/
def recordNatSuccStuck (visited : Array (Address × Address)) : RecM m Unit :=
  modify fun s => { s with env := { s.env with
    natSuccStuck := visited.foldl (·.insert ·) s.env.natSuccStuck } }

/-- Extend the successor-loop trace after the peeled argument is known not to
    have a stuck memo entry. -/
def tryReduceNatSuccPeelMiss (w cur : KExpr m) (offset : Nat)
    (visited : Array (Address × Address)) (curKey : Address × Address) :
    RecM m (BoundedStep
      (KExpr m × Nat × Array (Address × Address)) (Option (KExpr m))) := do
  let visited := visited.push curKey
  -- succ(cur) can surface later as a succ-iter argument too.
  let visited := visited.push (← TcM.whnfKey w)
  return .next (cur, offset + 1, visited)

/-- Decide a resolved peeled argument key: either propagate a known-stuck
    suffix to the whole visited prefix, or continue with the second key. -/
def tryReduceNatSuccPeelAfterKey (w cur : KExpr m) (offset : Nat)
    (visited : Array (Address × Address)) (curKey : Address × Address) :
    RecM m (BoundedStep
      (KExpr m × Nat × Array (Address × Address)) (Option (KExpr m))) := do
  if (← get).env.natSuccStuck.contains curKey then
    -- Known-stuck suffix ⇒ the whole chain above is stuck too.
    recordNatSuccStuck visited
    return .done none
  tryReduceNatSuccPeelMiss w cur offset visited curKey

/-- Peel one recognized successor layer, either stopping at a previously
    memoized suffix or extending the visited-key trace for the next step. -/
def tryReduceNatSuccPeel (w cur : KExpr m) (offset : Nat)
    (visited : Array (Address × Address)) :
    RecM m (BoundedStep
      (KExpr m × Nat × Array (Address × Address)) (Option (KExpr m))) := do
  let curKey ← TcM.whnfKey cur
  tryReduceNatSuccPeelAfterKey w cur offset visited curKey

/-- Classify the recursively normalized successor argument.  This second
    successor-loop seam isolates literal success, successor peeling, and both
    stuck-memo writes from the two recursive callbacks that precede it. -/
def tryReduceNatSuccAfterWhnf (w : KExpr m) (offset : Nat)
    (visited : Array (Address × Address)) :
    RecM m (BoundedStep
      (KExpr m × Nat × Array (Address × Address)) (Option (KExpr m))) := do
  let p ← prims
  if let some n := extractNatLit w p then
    return .done (some (natExprFromValue (n + offset)))
  let (_, args) := w.collectSpine
  let isSucc ← isNatSuccSpine w
  if isSucc then
    let cur := args[0]!
    return (← tryReduceNatSuccPeel w cur offset visited)
  recordNatSuccStuck visited
  return .done none

/-- One bounded successor-collapse iteration.  Naming this seam exposes the
    linear-recognizer, recursive WHNF, literal, successor-peel, and stuck-memo
    branches to verification without changing their production order. -/
def tryReduceNatSuccIterStep
    (state : KExpr m × Nat × Array (Address × Address)) :
    RecM m (BoundedStep
      (KExpr m × Nat × Array (Address × Address)) (Option (KExpr m))) := do
  let (cur, offset, visited) := state
  if let some result ← tryReduceNatSuccLinearRec cur offset then
    return .done (some result)
  let w ← whnfModeRec cur .stuck
  tryReduceNatSuccAfterWhnf w offset visited

/-- Collapse a `Nat.succ` chain onto a literal (with stuck-chain memo: the
    inner WHNF runs in `stuck` mode which bypasses caches, so without the
    memo a stuck `succ^k(x)` re-peels from every depth — O(k²)). -/
def tryReduceNatSuccIter (arg : KExpr m) :
    RecM m (Option (KExpr m)) := do
  let entryKey ← TcM.whnfKey arg
  if (← get).env.natSuccStuck.contains entryKey then
    return none
  runBounded tryReduceNatSuccIterStep maxWhnfFuel.toNat
    (arg, 1, #[entryKey])

/-- `Nat.rec base step (lit n)` where step = `fun _ ih => Nat.succ ih`:
    compute `base + n + offset` directly (literal base), or collapse to the
    compact offset `Nat.add base (Lit (n + offset))` (symbolic base). -/
def tryReduceNatSuccLinearRec (arg : KExpr m) (offset : Nat) :
    RecM m (Option (KExpr m)) := do
  let some parts ← natRecLiteralParts arg | return none
  let some base := parts.spine[parts.baseIdx]? | return none
  let some step := parts.spine[parts.stepIdx]? | return none
  if !(← isNatSuccIhStep step) then
    return none
  let baseWhnf ← whnfRec base
  match extractNatValue baseWhnf (← prims) with
  | some baseVal =>
    return some (natExprFromValue (baseVal + parts.major + offset))
  | none =>
    -- Symbolic base: collapse `succ^offset(Nat.rec base succ-step (Lit n))`
    -- to the compact offset `Nat.add base (Lit (n + offset))` rather than
    -- declining into n iota steps that materialize succ^n(base). Keeps the
    -- value in the same `base + k` form a literal already has, so def-eq
    -- converges instead of descending n unary succ layers. Conservative:
    -- only when the recursor application carries no post-major arguments.
    -- Mirrors whnf.rs `try_reduce_nat_succ_linear_rec`.
    if parts.spine.size != parts.majorIdx + 1 then
      return none
    return some (← mkNatAdd baseWhnf (natExprFromValue (parts.major + offset)))

def isNatSuccIhStep (step : KExpr m) : RecM m Bool := do
  let step ← whnfRec step
  let .lam _ _ _ body _ := step | return false
  let .lam _ _ _ body _ := body | return false
  let (head, args) := body.collectSpine
  let .const id _ _ := head | return false
  if id.addr != (← prims).natSucc.addr || args.size != 1 then
    return false
  match args[0]! with
  | .var 0 _ _ => return true
  | _ => return false

/-- WHNF a Nat-reducer argument. Open arguments get a bounded local fuel so
    a stuck symbolic argument can't burn the shared budget; fuel exhaustion
    yields `none` (leave unreduced). -/
def whnfNatReducerArg (arg : KExpr m) :
    RecM m (Option (KExpr m)) := do
  if !arg.hasFVars || (← get).eagerReduce then
    return some (← whnfRec arg)
  let savedFuel := (← get).recFuel
  let localFuel := min savedFuel natReducerOpenArgRecFuel
  modify fun s => { s with recFuel := localFuel }
  let result : Except (TcError m) (KExpr m) ←
    try
      let w ← whnfRec arg
      pure (Except.ok w)
    catch e =>
      pure (Except.error e)
  let consumed := localFuel - (← get).recFuel
  modify fun s => { s with recFuel := savedFuel - min savedFuel consumed }
  match result with
  | .ok w => return some w
  | .error .maxRecDepth | .error .maxRecFuel => return none
  | .error e => throw e

def tryReduceNatPredicate (addr : Address) (args : Array (KExpr m)) :
    RecM m (Option (KExpr m)) := do
  let some wa ← whnfNatReducerArg args[0]! | return none
  let p ← prims
  let some aVal := extractNatLit wa p | return none
  let some wb ← whnfNatReducerArg args[1]! | return none
  let some bVal := extractNatLit wb p | return none
  let decision := if addr == p.natBeq.addr then aVal == bVal else aVal.ble bVal
  let boolId := if decision then p.boolTrue else p.boolFalse
  let result ← TcM.intern (.mkConst boolId #[])
  return some (← finishAppResult result args 2)

/-- If `e` is `Nat.add base (Lit n)` (n > 0) or `Nat.div/mod base (Lit k)`
    (k ≥ 2) with a non-literal base, return the same operation in canonical
    compact form so the WHNF loop can leave it stuck instead of
    delta-unfolding. Thresholds keep `x + 0`, `x / 1`, `x / 0` (and mod)
    reducing through the normal path. `none` means "not this shape —
    proceed normally". Mirrors whnf.rs `try_nat_offset_stuck`. -/
def tryNatOffsetStuck (e : KExpr m) : RecM m (Option (KExpr m)) := do
  let p ← prims
  if !natOffsetStuckHead p e then
    return none
  let (head, args) := e.collectSpine
  let .const id _ _ := head | return none
  let isAdd := id.addr == p.natAdd.addr
  let isDivmod := id.addr == p.natDiv.addr || id.addr == p.natMod.addr
  if (!isAdd && !isDivmod) || args.size != 2 then
    return none
  let some wb ← whnfNatReducerArg args[1]! | return none
  let some n := extractNatValue wb p | return none
  if n == 0 then
    return none
  if isDivmod && n == 1 then
    return none
  let some wa ← whnfNatReducerArg args[0]! | return none
  if (extractNatValue wa p).isSome then
    -- Both sides literal: closed arithmetic for the Nat reducer, not a
    -- stuck offset.
    return none
  let inner ← TcM.intern (KExpr.mkApp head wa)
  return some (← TcM.intern (KExpr.mkApp inner (natExprFromValue n)))

/-- Build the canonical `Decidable.isTrue` proof term for a successful
native Nat decision.  This seam records the exact left-to-right intern order
without mixing construction with the surrounding reducer classifier. -/
def buildNatDecidableTrue (p : Primitives m) (prop : KExpr m)
    (args : Array (KExpr m)) (proofTrueFn : KId m) (u1 : KUniv m) :
    RecM m (KExpr m) := do
  let eqRefl ← TcM.intern (.mkConst p.eqRefl #[u1])
  let boolTy ← TcM.intern (.mkConst p.boolType #[])
  let boolTrue ← TcM.intern (.mkConst p.boolTrue #[])
  let reflProof ← TcM.intern (KExpr.mkApp eqRefl boolTy)
  let reflProof ← TcM.intern (KExpr.mkApp reflProof boolTrue)
  let proofConst ← TcM.intern (.mkConst proofTrueFn #[])
  let proof ← TcM.intern (KExpr.mkApp proofConst args[0]!)
  let proof ← TcM.intern (KExpr.mkApp proof args[1]!)
  let proof ← TcM.intern (KExpr.mkApp proof reflProof)
  let isTrue ← TcM.intern (.mkConst p.decidableIsTrue #[])
  let result ← TcM.intern (KExpr.mkApp isTrue prop)
  TcM.intern (KExpr.mkApp result proof)

/-- Build the canonical `Decidable.isFalse` proof term for a failed native
Nat equality decision.  As above, the helper preserves the production intern
sequence exactly. -/
def buildNatDecidableFalse (p : Primitives m) (prop : KExpr m)
    (args : Array (KExpr m)) (proofFalseFn : KId m) (u1 : KUniv m) :
    RecM m (KExpr m) := do
  let eqRefl ← TcM.intern (.mkConst p.eqRefl #[u1])
  let boolTy ← TcM.intern (.mkConst p.boolType #[])
  let boolFalse ← TcM.intern (.mkConst p.boolFalse #[])
  let reflProof ← TcM.intern (KExpr.mkApp eqRefl boolTy)
  let reflProof ← TcM.intern (KExpr.mkApp reflProof boolFalse)
  let proofConst ← TcM.intern (.mkConst proofFalseFn #[])
  let proof ← TcM.intern (KExpr.mkApp proofConst args[0]!)
  let proof ← TcM.intern (KExpr.mkApp proof args[1]!)
  let proof ← TcM.intern (KExpr.mkApp proof reflProof)
  let isFalse ← TcM.intern (.mkConst p.decidableIsFalse #[])
  let result ← TcM.intern (KExpr.mkApp isFalse prop)
  TcM.intern (KExpr.mkApp result proof)

/-- Recover the proposition carried by a `Decidable` expression.  Inference
runs under the validation-only policy and is caught as an accelerator miss;
normalizing the inferred type remains a recursive WHNF edge. -/
def inferDecidableProp (e : KExpr m) : RecM m (Option (KExpr m)) := do
  let some eTy ← try? (TcM.withInferOnly ((← read).infer e))
    | return none
  let eTyWhnf ← whnfRec eTy
  return eTyWhnf.collectSpine.2[0]?

/-- Native Nat.decLe/decEq/decLt on literals → `Decidable.isTrue/isFalse`
    with the canonical kernel proof terms; `decLt n m → decLe (n+1) m`;
    Int decidables get literal *normalization* only. `decLe false` falls to
    delta (needs the `False` primitive). -/
def tryReduceDecidable (e : KExpr m) : RecM m (Option (KExpr m)) := do
  if (← get).noAccel then return none
  let (head, args) := e.collectSpine
  let .const id _ _ := head | return none
  let addr := id.addr
  let p ← prims
  let isDecLe := addr == p.natDecLe.addr
  let isDecEq := addr == p.natDecEq.addr
  let isDecLt := addr == p.natDecLt.addr
  if addr == p.intDecLe.addr || addr == p.intDecEq.addr
      || addr == p.intDecLt.addr then
    return (← tryNormalizeIntDecidable addr args)
  if !isDecLe && !isDecEq && !isDecLt then
    return none
  if args.size < 2 then
    return none
  let wa ← whnfRec args[0]!
  let wb ← whnfRec args[1]!
  let some aVal := extractNatValue wa p | return none
  let some bVal := extractNatValue wb p | return none
  -- S5: @Eq.refl.{1} for Bool : Type = Sort 1.
  let u1 : KUniv m := .mkSucc .mkZero
  if isDecLt then
    -- decLt n m → decLe (n+1) m (recursively reduced by the caller loop).
    let succAExpr ← TcM.intern (natExprFromValue (aVal + 1) : KExpr m)
    let decLeConst ← TcM.intern (.mkConst p.natDecLe #[])
    let mut result ← TcM.intern (KExpr.mkApp decLeConst succAExpr)
    result ← TcM.intern (KExpr.mkApp result args[1]!)
    return some (← finishAppResult result args 2)
  -- The proposition from `e : Decidable prop`.
  let some prop ← inferDecidableProp e | return none
  let (bResult, proofTrueFn, proofFalseFn) :=
    if isDecLe then
      (aVal.ble bVal, p.natLeOfBleEqTrue, p.natNotLeOfNotBleEqTrue)
    else
      (aVal == bVal, p.natEqOfBeqEqTrue, p.natNeOfBeqEqFalse)
  let resultExpr ← if bResult then
      buildNatDecidableTrue p prop args proofTrueFn u1
    else if isDecEq then
      buildNatDecidableFalse p prop args proofFalseFn u1
    else
      -- decLe false: fall through to delta.
      return none
  return some (← finishAppResult resultExpr args 2)

/-- Normalize Int decidable arguments to canonical ctor-form literals (the
    delta+iota chain then reduces them; no native Int evaluation). -/
def tryNormalizeIntDecidable (addr : Address)
    (args : Array (KExpr m)) : RecM m (Option (KExpr m)) := do
  if args.size < 2 then
    return none
  let wa ← whnfRec args[0]!
  let wb ← whnfRec args[1]!
  let p ← prims
  let some aVal := extractIntLit wa p | return none
  let some bVal := extractIntLit wb p | return none
  let a ← internIntLit aVal
  let b ← internIntLit bVal
  if a.addr == args[0]!.addr && b.addr == args[1]!.addr then
    return none
  let headId := if addr == p.intDecEq.addr then p.intDecEq
    else if addr == p.intDecLe.addr then p.intDecLe
    else p.intDecLt
  let head ← TcM.intern (.mkConst headId #[])
  let mut result ← TcM.intern (KExpr.mkApp head a)
  result ← TcM.intern (KExpr.mkApp result b)
  return some (← finishAppResult result args 2)

/-- Quotient reduction (`Quot.lift` arity 6 / major 5; `Quot.ind` arity 5 /
    major 4), gated on the resolved primitive addresses. -/
def tryQuotReduce (e : KExpr m) : RecM m (Option (KExpr m)) := do
  let (head, args) := e.collectSpine
  let .const id _ _ := head | return none
  let p ← prims
  let (fIdx, majorIdx) ←
    if id.addr == p.quotLift.addr then
      if args.size < 6 then return none
      pure (3, 5)
    else if id.addr == p.quotInd.addr then
      if args.size < 5 then return none
      pure (3, 4)
    else
      return none
  let majorWhnf ← whnfRec args[majorIdx]!
  let (mkHead, mkArgs) := majorWhnf.collectSpine
  let .const mkId _ _ := mkHead | return none
  if mkId.addr != p.quotCtor.addr then
    return none
  -- Quot.mk has exactly 3 args (α, r, a); the value is last.
  if mkArgs.size != 3 then
    return none
  let mut result ← TcM.intern (KExpr.mkApp args[fIdx]! mkArgs[2]!)
  for arg in args.extract (majorIdx + 1) args.size do
    result ← TcM.intern (KExpr.mkApp result arg)
  return some result

-- ### BitVec native reduction (whnf.rs try_reduce_bitvec)

/-- Bounded literal evaluator for widths/predicate args: literal
    extraction, succ/pred/binary-arith folding, stuck-probe early-out,
    whnf fallback. Mirrors whnf.rs `try_eval_nat_value_for_pred`. -/
def tryEvalNatValueForPred (e : KExpr m) (depth : Nat := 0) :
    RecM m (Option Nat) :=
  tryEvalNatValueForPredFuel (64 - depth) e

def tryEvalNatValueForPredFuel : Nat → KExpr m → RecM m (Option Nat)
  | 0, _ => return none
  | fuel + 1, e => do
  let p ← prims
  if let some n := extractNatLit e p then
    return some n
  if ← isStuckNatPredicateProbe e then
    return none
  let (head, args) := e.collectSpine
  match head with
  | .const id _ _ =>
    if id.addr == p.natSucc.addr && args.size == 1 then
      let some pred ← tryEvalNatValueForPredFuel fuel args[0]!
        | return none
      return some (pred + 1)
    if id.addr == p.natPred.addr && args.size == 1 then
      let some n ← tryEvalNatValueForPredFuel fuel args[0]!
        | return none
      return some (n - 1)
    if (← isNatBinArithAddr id.addr) && args.size == 2 then
      let some a ← tryEvalNatValueForPredFuel fuel args[0]!
        | return none
      let some b ← tryEvalNatValueForPredFuel fuel args[1]!
        | return none
      return computeNatBin id.addr PrimAddrs.canonical a b
  | .var .. | .fvar .. | .sort .. | .lam .. | .all .. | .str .. | .nat .. =>
    return none
  | _ => pure ()
  let w ← whnfRec e
  if let some n := extractNatValue w p then
    return some n
  if w.addr == e.addr then
    return none
  tryEvalNatValueForPredFuel fuel w

/-- `BitVec.toNat (BitVec.ofNat w n) ⇒ n % 2^w` (width ≤ 2^24). -/
def tryReduceBitvecToNat (value : KExpr m) :
    RecM m (Option (KExpr m)) := do
  let some (width, nExpr) ← bitvecOfNatArgs value | return none
  let nWhnf ← whnfRec nExpr
  let some n := extractNatValue nWhnf (← prims) | return none
  if n == 0 then
    return some (natLiteral 0)
  let some widthVal ← tryEvalNatValueForPred width | return none
  if widthVal > (1 <<< 24) then
    return none
  return some (natExprFromValue (n % (1 <<< widthVal)))

/-- `value.toNat` — collapsed when possible, else the symbolic
    `BitVec.toNat width value` application. -/
def bitvecToNatExpr (width value : KExpr m) : RecM m (KExpr m) := do
  if let some result ← tryReduceBitvecToNat value then
    return result
  let head ← TcM.intern (.mkConst (← prims).bitVecToNat #[])
  let withWidth ← TcM.intern (.mkApp head width)
  TcM.intern (.mkApp withWidth value)

/-- `BitVec.ult w x y`: rhs 0 ⇒ false; both literal ⇒ compare; else the
    definitional `Nat.ble (succ x.toNat) y.toNat` route when it collapses
    to a Bool literal. -/
def tryReduceBitvecUlt (width lhs rhs : KExpr m) :
    RecM m (Option (KExpr m)) := do
  let p ← prims
  let lhsNat ← bitvecToNatExpr width lhs
  let rhsNat ← bitvecToNatExpr width rhs
  let rhsNatWhnf ← whnfRec rhsNat
  if let some rhsVal := extractNatValue rhsNatWhnf p then
    if rhsVal == 0 then
      return some (← TcM.intern (.mkConst p.boolFalse #[]))
    let lhsNatWhnf ← whnfRec lhsNat
    if let some lhsVal := extractNatValue lhsNatWhnf p then
      let resultId := if lhsVal < rhsVal then p.boolTrue else p.boolFalse
      return some (← TcM.intern (.mkConst resultId #[]))
  let lhsSucc ← mkNatSucc lhsNat
  let ble ← TcM.intern (.mkConst p.natBle #[])
  let cmpLhs ← TcM.intern (.mkApp ble lhsSucc)
  let cmp ← TcM.intern (.mkApp cmpLhs rhsNat)
  let result ← whnfRec cmp
  if (← boolLitValue result).isSome then
    return some result
  return none

/-- `LT.lt (BitVec w) inst x y ⇒ ult w x y`. -/
def tryReduceBitvecLtProp (prop : KExpr m) :
    RecM m (Option (KExpr m)) := do
  let p ← prims
  let (head, args) := prop.collectSpine
  let .const id _ _ := head | return none
  if id.addr != p.ltLt.addr || args.size != 4 then
    return none
  let (typeHead, typeArgs) := args[0]!.collectSpine
  let .const typeId _ _ := typeHead | return none
  if typeId.addr != p.bitVec.addr || typeArgs.size != 1 then
    return none
  tryReduceBitvecUlt typeArgs[0]! args[2]! args[3]!

/-- BitVec native reduction: `BitVec.toNat`, `BitVec.ult`, and
    `Decidable.decide (LT.lt (BitVec w) …)`. -/
def tryReduceBitvec (e : KExpr m) : RecM m (Option (KExpr m)) := do
  if (← get).noAccel then return none
  let p ← prims
  let (head, args) := e.collectSpine
  let .const id _ _ := head | return none
  if id.addr == p.bitVecToNat.addr && args.size ≥ 2 then
    if let some result ← tryReduceBitvecToNat args[1]! then
      return some (← finishAppResult result args 2)
    return none
  if id.addr == p.bitVecUlt.addr && args.size ≥ 3 then
    if let some result ← tryReduceBitvecUlt args[0]! args[1]! args[2]! then
      return some (← finishAppResult result args 3)
    return none
  if id.addr == p.decidableDecide.addr && args.size ≥ 2 then
    if let some result ← tryReduceBitvecLtProp args[0]! then
      return some (← finishAppResult result args 2)
  return none

/-- Execute an already recognized `Lean.reduceBool`/`Lean.reduceNat` marker.
This seam owns the lazy declaration lookup, universe instantiation,
re-entrancy guard, recursive callback, guard restoration, and final result
classifier. -/
def tryReduceNativeMarker (p : Primitives m) (isReduceBool : Bool)
    (argId : KId m) (argUs : Array (KUniv m)) :
    RecM m (Option (KExpr m)) := do
  let body ← match (← TcM.tryGetConst argId) with
    | some (.defn (val := val) ..) => pure val
    | _ => return none
  let body ← TcM.instantiateUnivParams body argUs
  modify fun s => { s with inNativeReduce := true }
  let result : Except (TcError m) (KExpr m) ←
    try
      let r ← whnfRec body
      pure (Except.ok r)
    catch err =>
      pure (Except.error err)
  modify fun s => { s with inNativeReduce := false }
  let result ← match result with
    | .ok r => pure r
    | .error err => throw err
  if isReduceBool then
    match result with
    | .const rid _ _ =>
      if rid.addr == p.boolTrue.addr || rid.addr == p.boolFalse.addr then
        return some result
      return none
    | _ => return none
  else
    match result with
    | .nat .. => return some result
    | _ => return none

/-- Classify the syntax-only native reductions after the primitive table and
constant-headed spine have been obtained.  Keeping this decision tree pure
separates it from the re-entrancy guard and recursive callback. -/
def planNativeReduction (p : Primitives m) (e : KExpr m)
    (headAddr : Address) (args : Array (KExpr m)) :
    NativeReductionPlan m := Id.run do
  let isUnitSizeofImpl := headAddr == p.punitSizeOf1.addr && args.size == 1
  if e.lbr > 0 then
    if isUnitSizeofImpl then
      return .done (some (natLiteral 1))
    return .done none
  -- `System.Platform.numBits` via the subtype projection of getNumBits ().
  if headAddr == p.subtypeVal.addr && args.size == 3 then
    let (valueHead, valueArgs) := args[2]!.collectSpine
    if valueArgs.size == 1 then
      if let .const valueId _ _ := valueHead then
        if valueId.addr == p.systemPlatformGetNumBits.addr then
          return .done (some (natLiteral 64))
  -- PUnit/Unit SizeOf instance is extensionally the constant 1.
  if headAddr == p.sizeOfSizeOf.addr && args.size == 3 then
    let (tyHead, _) := args[0]!.collectSpine
    if let .const tyId _ _ := tyHead then
      if tyId.addr == p.unit.addr || tyId.addr == p.punit.addr then
        return .done (some (natLiteral 1))
  if isUnitSizeofImpl then
    return .done (some (natLiteral 1))
  if headAddr == p.systemPlatformNumBits.addr && args.isEmpty then
    return .done (some (natLiteral 64))
  let isReduceBool := headAddr == p.reduceBool.addr
  let isReduceNat := headAddr == p.reduceNat.addr
  if !isReduceBool && !isReduceNat then
    return .done none
  if args.size != 1 then
    return .done none
  return .marker isReduceBool args[0]!

/-- Native reduction: `Lean.reduceBool/reduceNat` markers,
    `System.Platform.numBits ⇒ 64` (also the `Subtype.val (getNumBits ())`
    form), and the PUnit/Unit SizeOf singletons. -/
def tryReduceNative (e : KExpr m) : RecM m (Option (KExpr m)) := do
  if (← get).noAccel then return none
  let (head, args) := e.collectSpine
  let .const id _ _ := head | return none
  let p ← prims
  let headAddr := id.addr
  match planNativeReduction p e headAddr args with
  | .done result => pure result
  | .marker isReduceBool arg =>
    -- Re-entrancy guard: whnf → native → whnf → native.
    if (← get).inNativeReduce then
      return none
    let .const argId argUs _ := arg | return none
    tryReduceNativeMarker p isReduceBool argId argUs

-- ### `is_rec` verification (inductive.rs `computed_is_rec` — hosted here
-- because struct-likeness needs it; `Ix.Tc.Inductive` reuses it)

/-- Finish one constructor-parameter peel after the recursive WHNF callback.
Naming the post-callback seam keeps the binder mutation equation stable for
verification without changing the production control flow. -/
def computeIsRecParamStepAfterWhnf (ty w : KExpr m) :
    RecM m (ForInStep (KExpr m)) := do
  match w with
  | .all _ _ dom body _ =>
    TcM.pushLocal dom
    return .yield body
  | _ => return .done ty

/-- Peel one constructor parameter when its normalized type remains a forall.
The pushed domain scopes the returned body for every later scan step. -/
def computeIsRecParamStep (ty : KExpr m) :
    RecM m (ForInStep (KExpr m)) := do
  let w ← whnfRec ty
  computeIsRecParamStepAfterWhnf ty w

/-- Finish one constructor-field scan after the recursive WHNF callback. -/
def computeIsRecFieldStepAfterWhnf (blockAddrs : Array Address)
    (w : KExpr m) : RecM m (BoundedStep (KExpr m) Bool) := do
  match w with
  | .all _ _ dom body _ =>
    if exprMentionsAnyAddr dom blockAddrs then
      return .done true
    TcM.pushLocal dom
    return .next body
  | _ => return .done false

/-- Inspect one constructor field and either find a recursive occurrence,
continue under its binder, or finish at the end of the telescope. -/
def computeIsRecFieldStep (blockAddrs : Array Address) (ty : KExpr m) :
    RecM m (BoundedStep (KExpr m) Bool) := do
  let w ← whnfRec ty
  computeIsRecFieldStepAfterWhnf blockAddrs w

/-- Classify one constructor telescope while restoring the caller's legacy
context depth on every result and partial error. -/
def computeIsRecCtor (ctorTy : KExpr m) (nParams : Nat)
    (blockAddrs : Array Address) : RecM m Bool := do
  let saved ← liftM (TcM.saveDepth (m := m))
  try
    let ty ← forIn [0:nParams] ctorTy fun _ ty =>
      computeIsRecParamStep ty
    runBounded (computeIsRecFieldStep blockAddrs) maxWhnfFuel.toNat ty
  finally
    liftM (TcM.restoreDepth (m := m) saved)

def computeIsRec (ctors : Array (KId m)) (nParams : Nat)
    (blockAddrs : Array Address) : RecM m Bool := do
  for ctorId in ctors do
    let ctorTy ← match (← TcM.tryGetConst ctorId) with
      | some (.ctor (ty := ty) ..) => pure ty
      | _ => continue
    let found ← computeIsRecCtor ctorTy nParams blockAddrs
    if found then
      return true
  return false

/-- The single physical write used for both the provisional re-entrancy
marker and the final recursion result.  Naming the seam keeps the semantic
cache certificate separate from the classifier's control flow. -/
def cacheIsRec (ind : KId m) (value : Bool) : RecM m Unit :=
  modify fun s => { s with env := { s.env with
    isRecCache := s.env.isRecCache.insert ind.addr value } }

/-- Cleanup performed only when the constructor-field classifier throws.
Errors from declaration or mutual-block discovery occur before this scope and
therefore deliberately retain the provisional marker. -/
def eraseCachedIsRec (ind : KId m) : RecM m Unit :=
  modify fun s => { s with env := { s.env with
    isRecCache := s.env.isRecCache.erase ind.addr } }

/-- Classify one already-discovered mutual block and commit its exact result.
The non-backtracking handler erases the provisional entry from the partial
error state before rethrowing. -/
def computedIsRecClassify (ind : KId m) (ctors : Array (KId m))
    (nParams : Nat) (blockAddrs : Array Address) : RecM m Bool :=
  tryCatch
    (do
      let value ← computeIsRec ctors nParams blockAddrs
      cacheIsRec ind value
      return value)
    (fun err => do
      eraseCachedIsRec ind
      throw err)

/-- Cache-miss transaction after the inductive metadata has been selected.
The provisional marker precedes mutual-block discovery, matching the original
Rust/Lean state-on-error behavior. -/
def computedIsRecMiss (ind : KId m) (params : UInt64)
    (ctors : Array (KId m)) (block : KId m) : RecM m Bool := do
  cacheIsRec ind true
  let blockInds ← discoverBlockInductives block
  computedIsRecClassify ind ctors params.toNat (blockInds.map (·.addr))

/-- Constructive `is_rec`: any constructor field (after params) mentioning
    any inductive of the mutual block. Provisional-true cache entry guards
    re-entrancy through whnf → struct-eta → isStructLike. -/
def computedIsRec (ind : KId m) : RecM m Bool := do
  if let some value := (← get).env.isRecCache[ind.addr]? then
    return value
  match (← TcM.getConst ind) with
  | .indc (params := params) (ctors := ctors) (block := block) .. =>
      computedIsRecMiss ind params ctors block
  | _ => throw (.other "computed_is_rec: not an inductive")

end

/-- Equation theorem exposing only the projection prelude/tail split.  Keeping
this outside the large recursive method block prevents downstream proofs from
unfolding unrelated WHNF definitions merely to inspect `tryProjReduce`. -/
theorem tryProjPrepare_eq (wval : KExpr m) :
    tryProjPrepare wval =
      match wval with
      | .str value _ _ => do
          let expanded ← strLitToConstructor value
          whnfRec expanded
      | _ => pure wval := by
  cases wval <;> rfl

theorem tryProjReduce_eq (id : KId m) (field : UInt64) (wval : KExpr m) :
    tryProjReduce id field wval = (do
      let prepared ← tryProjPrepare wval
      tryProjReduceTail id field prepared) := by
  rfl

attribute [irreducible] tryProjPrepare tryProjReduce

end RecM

end Ix.Tc

end
end
