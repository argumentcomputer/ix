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
decidables, Int decidable literal normalization. **BitVec native reduction
is deferred** — `tryReduceBitvec` is a stub returning `none` (Rust reduces
`BitVec.toNat/ult/decide-lt` natively; those fall to delta/iota here).
-/

public section
@[expose] section

namespace Ix.Tc

open Std (HashMap HashSet)

/-- Local fuel cap for whnf on *open* arguments of the Nat reducer. -/
def natReducerOpenArgRecFuel : UInt64 := 4096

/-- Reduction-policy flags (whnf.rs `WhnfFlags`). -/
structure WhnfFlags where
  cheapRec : Bool
  cheapProj : Bool
  deriving BEq, Repr, Inhabited

namespace WhnfFlags

def FULL : WhnfFlags := ⟨false, false⟩
def DEF_EQ_CORE : WhnfFlags := ⟨false, true⟩

@[inline] def isFull (f : WhnfFlags) : Bool := !f.cheapRec && !f.cheapProj

end WhnfFlags

/-- Nat succ-collapse policy: `stuck` bypasses whnf caches and disables the
    succ-chain collapse (used inside the succ-peeling loop itself). -/
inductive NatSuccMode where
  | collapse
  | stuck
  deriving BEq, Repr, Inhabited

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

/-! ### Pure helpers -/

/-- Nat value from a literal or the `Nat.zero` constructor (C++
    `is_nat_lit_ext` / lean4lean `rawNatLitExt?`). -/
def extractNatLit (e : KExpr m) (prims : Primitives m) : Option Nat :=
  match e with
  | .nat val _ _ => some val
  | .const id _ _ => if id.addr == prims.natZero.addr then some 0 else none
  | _ => none

/-- Nat value from literal form or a constructor numeral
    (`Nat.succ (Nat.succ …(lit)…)`). -/
partial def extractNatValue (e : KExpr m) (prims : Primitives m) : Option Nat :=
  match extractNatLit e prims with
  | some n => some n
  | none =>
    let (head, args) := e.collectSpine
    match head with
    | .const id _ _ =>
      if id.addr == prims.natSucc.addr && args.size == 1 then
        (extractNatValue args[0]! prims).map (· + 1)
      else none
    | _ => none

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
partial def projectionDefinitionInfo (val : KExpr m) :
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
  let mut list := nil
  for c in s.toList.reverse do
    let natLit ← TcM.intern (natExprFromValue c.toNat : KExpr m)
    let charVal ← TcM.intern (KExpr.mkApp charOfNat natLit)
    let partialApp ← TcM.intern (KExpr.mkApp cons charVal)
    list ← TcM.intern (KExpr.mkApp partialApp list)
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

mutual

/-- Full WHNF: loop of whnf-no-delta → native/nat/decidable/string → delta. -/
partial def whnf (e : KExpr m) : RecM m (KExpr m) :=
  whnfWithNatSuccMode e .collapse

partial def whnfWithNatSuccMode (e : KExpr m) (natSuccMode : NatSuccMode) :
    RecM m (KExpr m) := do
  -- Quick exit for non-reducing forms.
  match e with
  | .sort .. | .all .. | .lam .. | .nat .. | .str .. => return e
  | .var i _ _ =>
    if !(← TcM.isLetVar (m := m) i) then return e
  | _ => pure ()
  let key ← TcM.whnfKey e
  let useCache := natSuccMode == .collapse
  let transientNatWork ← isTransientNatLiteralWork e
  if useCache && !transientNatWork then
    if let some cached := (← get).env.whnfCache[key]? then
      return cached
  -- Tick AFTER fast paths and cache: only consume fuel for actual work.
  TcM.tick (m := m)
  let mut cur := e
  let mut fuel := maxWhnfFuel
  let mut seen : HashSet Address := {}
  repeat
    if fuel == 0 then
      throw .maxRecDepth
    fuel := fuel - 1
    cur ← whnfNoDeltaImpl cur .FULL natSuccMode
    if seen.contains cur.addr then
      break
    seen := seen.insert cur.addr
    -- Native reduction runs before nat reduction (lean4lean order).
    if let some reduced ← tryReduceNative cur then
      cur := reduced
      continue
    if let some reduced ← tryReduceBitvec cur then
      cur := reduced
      continue
    -- Nat primitives BEFORE delta (short-circuit Nat.sub/pow/… bodies).
    if let some reduced ← tryReduceNatWithSuccMode cur natSuccMode then
      cur := reduced
      continue
    -- Nat decidables BEFORE delta.
    if let some reduced ← tryReduceDecidable cur then
      cur := reduced
      continue
    if let some reduced ← tryReduceString cur then
      cur := reduced
      continue
    if let some unfolded ← deltaUnfoldOne cur then
      cur := unfolded
      continue
    break
  if !(← get).inNativeReduce && useCache && !transientNatWork then
    modify fun s => { s with env := { s.env with
      whnfCache := s.env.whnfCache.insert key cur } }
  return cur

/-- Structural WHNF (beta/iota/zeta/proj), NO delta, FULL flags. -/
partial def whnfCore (e : KExpr m) : RecM m (KExpr m) :=
  whnfCoreWithFlags e .FULL

/-- Structural WHNF for def-eq's cheap-projection scaffold
    (`whnfCore (cheapProj := true)`). Bumps `cheapRecursionDepth` so cheap
    false negatives stay out of the full def-eq cache. -/
partial def whnfCoreForDefEq (e : KExpr m) : RecM m (KExpr m) := do
  modify fun s => { s with cheapRecursionDepth := s.cheapRecursionDepth + 1 }
  try
    whnfCoreWithFlags e .DEF_EQ_CORE
  finally
    modify fun s => { s with cheapRecursionDepth := s.cheapRecursionDepth - 1 }

partial def whnfCoreWithFlags (e : KExpr m) (flags : WhnfFlags) :
    RecM m (KExpr m) := do
  -- Leaves whnf_core never reduces (incl. `const` — no delta here); `var`
  -- only when no let frame can zeta it.
  match e with
  | .sort .. | .all .. | .lam .. | .nat .. | .str .. | .const .. => return e
  | .var i _ _ =>
    if !(← TcM.isLetVar (m := m) i) then return e
  | _ => pure ()
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

partial def whnfCoreWithFlagsUncached (e : KExpr m) (flags : WhnfFlags) :
    RecM m (KExpr m) := do
  let mut cur := e
  let mut fuel := maxWhnfFuel
  repeat
    if fuel == 0 then
      throw .maxRecDepth
    fuel := fuel - 1
    match cur with
    | .var i _ _ =>
      -- Legacy let-bound variable zeta-reduction.
      match (← TcM.lookupLetVal (m := m) i) with
      | some val =>
        cur := val
        continue
      | none => return cur
    | .fvar id _ _ =>
      -- Let-bound fvar zeta-reduction (lean4lean `whnfFVar`).
      match (← get).lctx.find? id with
      | some (.ldecl _ _ val) =>
        cur := val
        continue
      | _ => return cur
    | .sort .. | .all .. | .lam .. | .nat .. | .str .. | .const .. =>
      return cur
    | .prj id field val _ =>
      -- FULL: full whnf on the struct value (delta may expose a ctor).
      -- CHEAP: structural only; stuck projections stay stuck.
      let wval ← if flags.cheapProj then whnfCoreWithFlags val flags
        else whnf val
      match (← tryProjReduce id field wval) with
      | some result =>
        cur := result
        continue
      | none => return cur
    | .letE _ _ val body _ _ =>
      cur ← TcM.runIntern (subst body val 0)
      continue
    | .app .. => pure ()
    -- App: collect spine, whnf-core the head, beta / iota.
    let (f0, args) := cur.collectSpine
    let f ← whnfCoreWithFlags f0 flags
    if let .lam .. := f then
      -- Multi-arg beta.
      let mut body := f
      let mut consumedArgs : Array (KExpr m) := Array.mkEmpty args.size
      repeat
        if consumedArgs.size ≥ args.size then break
        match body with
        | .lam _ _ _ inner _ =>
          consumedArgs := consumedArgs.push args[consumedArgs.size]!
          body := inner
        | _ => break
      let remainingStart := consumedArgs.size
      if !consumedArgs.isEmpty then
        body ← TcM.runIntern (simulSubst body consumedArgs.reverse 0)
      for arg in args.extract remainingStart args.size do
        body ← TcM.intern (KExpr.mkApp body arg)
      cur := body
      continue
    if f != f0 then
      -- Head reduced: rebuild, try iota once, else done.
      let mut rebuilt := f
      for arg in args do
        rebuilt ← TcM.intern (KExpr.mkApp rebuilt arg)
      match (← tryIotaWithFlags rebuilt flags) with
      | some reduced =>
        cur := reduced
        continue
      | none => return rebuilt
    match (← tryIotaWithFlags cur flags) with
    | some reduced =>
      cur := reduced
      continue
    | none => return cur
  throw .maxRecDepth

/-- WHNF without delta: whnf-core → proj-app → nat/native/string → quot. -/
partial def whnfNoDelta (e : KExpr m) : RecM m (KExpr m) :=
  whnfNoDeltaImpl e .FULL .collapse

/-- Def-eq no-delta WHNF (cheap projection policy). -/
partial def whnfNoDeltaForDefEq (e : KExpr m) : RecM m (KExpr m) := do
  modify fun s => { s with cheapRecursionDepth := s.cheapRecursionDepth + 1 }
  try
    whnfNoDeltaImpl e .DEF_EQ_CORE .collapse
  finally
    modify fun s => { s with cheapRecursionDepth := s.cheapRecursionDepth - 1 }

partial def whnfNoDeltaImpl (e : KExpr m) (flags : WhnfFlags)
    (natSuccMode : NatSuccMode) : RecM m (KExpr m) := do
  match e with
  | .sort .. | .all .. | .lam .. | .nat .. | .str .. => return e
  | .var i _ _ =>
    if !(← TcM.isLetVar (m := m) i) then return e
  | _ => pure ()
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
  let mut cur := e
  let mut fuel := maxWhnfFuel
  repeat
    if fuel == 0 then
      throw .maxRecDepth
    fuel := fuel - 1
    cur ← whnfCoreWithFlags cur flags
    -- App-of-Prj: whnf_core resolves the outermost Prj only; give the
    -- head one more attempt under the same projection policy.
    match (← tryProjAppReduce cur flags) with
    | some (projResult, args) =>
      let mut result := projResult
      for arg in args do
        result ← TcM.intern (KExpr.mkApp result arg)
      cur := result
      continue
    | none => pure ()
    if let some reduced ← tryReduceBitvec cur then
      cur := reduced
      continue
    if let some reduced ← tryReduceNatWithSuccMode cur natSuccMode then
      cur := reduced
      continue
    -- Native/string before projection-definition rewriting (wrappers like
    -- Subtype.val are projection definitions; once rewritten to Prj the
    -- recognizers no longer see the head).
    if let some reduced ← tryReduceNative cur then
      cur := reduced
      continue
    if let some reduced ← tryReduceString cur then
      cur := reduced
      continue
    if flags.isFull then
      if let some reduced ← tryReduceProjectionDefinition cur then
        cur := reduced
        continue
    if let some reduced ← tryQuotReduce cur then
      cur := reduced
      continue
    break
  if !(← get).inNativeReduce && useCache && !transientNatWork then
    if flags.isFull then
      modify fun s => { s with env := { s.env with
        whnfNoDeltaCache := s.env.whnfNoDeltaCache.insert key cur } }
    else
      modify fun s => { s with env := { s.env with
        whnfNoDeltaCheapCache := s.env.whnfNoDeltaCheapCache.insert key cur } }
  return cur

/-- Delta: unfold one defined constant (head-applied or bare). -/
partial def deltaUnfoldOne (e : KExpr m) : RecM m (Option (KExpr m)) := do
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

partial def tryDeltaUnfold (e : KExpr m) : RecM m (Option (KExpr m)) := do
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

/-- Universe-instantiated body of an unfolded head, cached by the head
    `const` expression's content hash (lean4 C++ `m_unfold` cache). -/
partial def unfoldConstValue (headExpr : KExpr m) (val : KExpr m)
    (us : Array (KUniv m)) : RecM m (KExpr m) := do
  let key := headExpr.addr
  if let some cached := (← get).env.unfoldCache[key]? then
    return cached
  let result ← TcM.instantiateUnivParams val us
  modify fun s => { s with env := { s.env with
    unfoldCache := s.env.unfoldCache.insert key result } }
  return result

/-- Iota: recursor applied to a constructor (or K-synthesized / struct-eta
    fallback). `cheapRec` reduces the major structurally only. -/
partial def tryIotaWithFlags (e : KExpr m) (flags : WhnfFlags) :
    RecM m (Option (KExpr m)) := do
  let (head, spine) := e.collectSpine
  let .const recId recUs _ := head | return none
  let recr ← match (← TcM.tryGetConst recId) with
    | some (.recr (k := k) (lvls := lvls) (params := params)
        (indices := indices) (motives := motives) (minors := minors)
        (rules := rules) ..) =>
      let majorIdx := (params + motives + minors + indices).toNat
      if spine.size ≤ majorIdx then
        return none
      pure { k, params := params.toNat, motives := motives.toNat,
             minors := minors.toNat, indices := indices.toNat,
             majorIdx, rules, lvls : IotaInfo m }
    | _ => return none
  -- K-like: synthesize a nullary ctor from the major's type before WHNF.
  let major := spine[recr.majorIdx]!
  let major ← if recr.k then
      pure ((← synthCtorWhenK major recId recr).getD major)
    else pure major
  let major := (← cleanupNatOffsetMajor major).getD major
  -- WHNF the major (cheap mode skips delta on the major itself).
  let majorWhnf0 ← if flags.cheapRec then whnfCoreWithFlags major flags
    else whnf major
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
  match majorWhnf with
  | .str val _ _ =>
    let strCtor ← strLitToConstructor val
    majorWhnf ← if flags.cheapRec then whnfCoreWithFlags strCtor flags
      else whnf strCtor
  | _ => pure ()
  -- Constructor application?
  let (ctorHead, ctorArgs) := majorWhnf.collectSpine
  let ctorInfo? ← match ctorHead with
    | .const cid _ _ =>
      match (← TcM.tryGetConst cid) with
      | some (.ctor (cidx := cidx) (fields := fields) ..) =>
        pure (some (cidx.toNat, fields.toNat))
      | _ => pure none
    | _ => pure none
  if let some (cidx, ctorFields) := ctorInfo? then
    if h : cidx < recr.rules.size then
      let rule := recr.rules[cidx]
      -- H6: level arity; H5: fields ≤ ctor args (lean4lean Reduce.lean:75-76).
      if recUs.size.toUInt64 != recr.lvls then
        return none
      if ctorFields > ctorArgs.size then
        return none
      let rhs ← TcM.instantiateUnivParams rule.rhs recUs
      let pmmEnd := recr.params + recr.motives + recr.minors
      let fieldStart := ctorArgs.size - ctorFields
      let mut result := rhs
      for arg in spine.extract 0 (min pmmEnd spine.size) do
        result ← applyIotaArg result arg majorWasNatLit
      for arg in ctorArgs.extract fieldStart ctorArgs.size do
        result ← applyIotaArg result arg majorWasNatLit
      for arg in spine.extract (recr.majorIdx + 1) spine.size do
        result ← applyIotaArg result arg majorWasNatLit
      return some result
    else
      return none
  -- Struct eta iota fallback.
  tryStructEtaIota recId recr recUs spine

partial def isStructLike (id : KId m) : RecM m Bool := do
  match (← TcM.tryGetConst id) with
  | some (.indc (indices := indices) (ctors := ctors) ..) =>
    if indices != 0 || ctors.size != 1 then
      return false
  | _ => return false
  return !(← computedIsRec id)

/-- Transient-mode iota application: beta-reduce as we go without interning
    (Nat-literal recursor chains would otherwise pin every predecessor). -/
partial def applyIotaArg (result : KExpr m) (arg : KExpr m)
    (transient : Bool) : RecM m (KExpr m) := do
  if transient then
    if let .lam _ _ _ body _ := result then
      return substNoIntern body arg 0
    return KExpr.mkApp result arg
  else
    TcM.intern (KExpr.mkApp result arg)

/-- Nat-literal recursor work is only useful while the current WHNF runs;
    caching it would make RSS linear in the literal. -/
partial def isTransientNatLiteralWork (e : KExpr m) : RecM m Bool := do
  if (← isNatLiteralRecursorApp e) then
    return true
  let (head, args) := e.collectSpine
  let .const id _ _ := head | return false
  if id.addr == (← prims).natSucc.addr && args.size == 1 then
    isNatLiteralRecursorApp args[0]!
  else
    return false

partial def isNatLiteralRecursorApp (e : KExpr m) : RecM m Bool := do
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

/-- Lean's `cleanupNatOffsetMajor`: expose one ctor layer of a definitional
    offset `base + k` (k > 0) as `Nat.succ (base + (k-1))`, keeping closed
    arithmetic for the primitive reducer. -/
partial def cleanupNatOffsetMajor (e : KExpr m) :
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

partial def natOffset (e : KExpr m) (depth : Nat) :
    RecM m (Option (KExpr m × Nat)) := do
  if depth ≥ 256 then
    return none
  let (head, args) := e.collectSpine
  let .const id _ _ := head | return none
  let p ← prims
  if id.addr == p.natSucc.addr && args.size == 1 then
    let (base, offset) ← natOffsetOrZero args[0]! (depth + 1)
    return some (base, offset + 1)
  if id.addr == p.natAdd.addr && args.size == 2 then
    let some rhs ← evalNatOffsetLiteral args[1]! (depth + 1) | return none
    let (base, offset) ← natOffsetOrZero args[0]! (depth + 1)
    return some (base, offset + rhs)
  return none

partial def natOffsetOrZero (e : KExpr m) (depth : Nat) :
    RecM m (KExpr m × Nat) := do
  return (← natOffset e depth).getD (e, 0)

/-- Syntactic, no-delta evaluator for Nat offset constants (weaker than
    WHNF by design). -/
partial def evalNatOffsetLiteral (e : KExpr m) (depth : Nat) :
    RecM m (Option Nat) := do
  if depth ≥ 256 then
    return none
  let p ← prims
  if let some n := extractNatValue e p then
    return some n
  let (head, args) := e.collectSpine
  let .const id _ _ := head | return none
  if id.addr == p.natPred.addr && args.size == 1 then
    let some n ← evalNatOffsetLiteral args[0]! (depth + 1) | return none
    return some (n - 1)
  if (← isNatBinArithAddr id.addr) && args.size == 2 then
    let some a ← evalNatOffsetLiteral args[0]! (depth + 1) | return none
    let some b ← evalNatOffsetLiteral args[1]! (depth + 1) | return none
    return computeNatBin id.addr PrimAddrs.canonical a b
  return none

/-- Struct-eta iota: single-rule recursor over a non-recursive one-ctor
    zero-index inductive; rebuild the rule with projections of the major.
    Prop-typed majors are excluded (lean4lean `toCtorWhenStruct`). -/
partial def tryStructEtaIota (recId : KId m) (recr : IotaInfo m)
    (recUs : Array (KUniv m)) (spine : Array (KExpr m)) :
    RecM m (Option (KExpr m)) := do
  if recr.rules.size != 1 then
    return none
  let rule := recr.rules[0]!
  let recTy ← match (← TcM.tryGetConst recId) with
    | some c => pure c.ty
    | none => return none
  let skip := (recr.params + recr.motives + recr.minors + recr.indices).toUInt64
  let some indId ← try? (getMajorInductiveId recTy skip) | return none
  if !(← isStructLike indId) then
    return none
  -- H3: Prop guard.
  let major := spine[recr.majorIdx]!
  let some majorTy ← try? (TcM.withInferOnly ((← read).infer major))
    | return none
  let some majorSort ← try? (TcM.withInferOnly ((← read).infer majorTy))
    | return none
  let some majorSortW ← try? (whnf majorSort) | return none
  if let .sort u _ := majorSortW then
    if u.isZero then
      return none
  let rhs ← TcM.instantiateUnivParams rule.rhs recUs
  let pmmEnd := recr.params + recr.motives + recr.minors
  let mut result := rhs
  for arg in spine.extract 0 (min pmmEnd spine.size) do
    result ← TcM.intern (KExpr.mkApp result arg)
  for i in [0:rule.fields.toNat] do
    let proj ← TcM.intern (KExpr.mkPrj indId i.toUInt64 major)
    result ← TcM.intern (KExpr.mkApp result proj)
  for arg in spine.extract (recr.majorIdx + 1) spine.size do
    result ← TcM.intern (KExpr.mkApp result arg)
  return some result

/-- K-like recursors: when the major isn't a ctor but its type matches the
    target inductive, build `ctor₀ params…` and def-eq-verify its type. -/
partial def synthCtorWhenK (major : KExpr m) (recId : KId m)
    (recr : IotaInfo m) : RecM m (Option (KExpr m)) := do
  let some majorTy ← try? (TcM.withInferOnly ((← read).infer major))
    | return none
  let some majorTyW ← try? (whnf majorTy) | return none
  let (tyHead, tyArgs) := majorTyW.collectSpine
  let .const tyHeadId tyUs _ := tyHead | return none
  let recTy ← match (← TcM.tryGetConst recId) with
    | some c => pure c.ty
    | none => return none
  let skip := (recr.params + recr.motives + recr.minors + recr.indices).toUInt64
  let some indId ← try? (getMajorInductiveId recTy skip) | return none
  if tyHeadId.addr != indId.addr then
    return none
  let ctorId ← match (← TcM.tryGetConst indId) with
    | some (.indc (ctors := ctors) ..) =>
      match ctors[0]? with
      | some c => pure c
      | none => return none
    | _ => return none
  let mut ctorApp ← TcM.intern (KExpr.mkConst ctorId tyUs)
  for arg in tyArgs.extract 0 (min recr.params tyArgs.size) do
    ctorApp ← TcM.intern (KExpr.mkApp ctorApp arg)
  let some ctorTy ← try? (TcM.withInferOnly ((← read).infer ctorApp))
    | return none
  if !(← callIsDefEq majorTyW ctorTy) then
    return none
  return some ctorApp

/-- Projection of a ctor application (with string-literal expansion first,
    and the `Fin.val`-through-`Decidable.rec` special case). -/
partial def tryProjReduce (id : KId m) (field : UInt64) (wval : KExpr m) :
    RecM m (Option (KExpr m)) := do
  let wval ← match wval with
    | .str s _ _ => do
      let expanded ← strLitToConstructor s
      whnf expanded
    | _ => pure wval
  let (head, args) := wval.collectSpine
  if let some result ← tryReduceFinValDecidableRec id field head args then
    return some result
  let .const ctorId _ _ := head | return none
  let ctorParams ← match (← TcM.tryGetConst ctorId) with
    | some (.ctor (params := params) ..) => pure params.toNat
    | _ => return none
  return args[ctorParams + field.toNat]?

/-- `(Decidable.rec … : Fin n).val` → push the projection into both minors
    (whnf.rs `try_reduce_fin_val_decidable_rec`). -/
partial def tryReduceFinValDecidableRec (id : KId m) (field : UInt64)
    (head : KExpr m) (args : Array (KExpr m)) :
    RecM m (Option (KExpr m)) := do
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

partial def projectDecidableFinValMinor (id : KId m) (field : UInt64)
    (minor : KExpr m) : RecM m (Option (KExpr m)) := do
  let .lam name bi dom body _ := minor | return none
  let proj ← TcM.intern (KExpr.mkPrj id field body)
  return some (← TcM.intern (KExpr.mkLam name bi dom proj))

/-- `App(Prj(S, i, v), args…)`: one more projection attempt on the head. -/
partial def tryProjAppReduce (e : KExpr m) (flags : WhnfFlags) :
    RecM m (Option (KExpr m × Array (KExpr m))) := do
  let (head, args) := e.collectSpine
  if args.isEmpty then
    return none
  let .prj id field val _ := head | return none
  let wval ← if flags.cheapProj then whnfCoreWithFlags val flags
    else whnf val
  match (← tryProjReduce id field wval) with
  | some result => return some (result, args)
  | none => return none

/-- Rewrite an applied projection-wrapper definition to a `prj` node. -/
partial def tryReduceProjectionDefinition (e : KExpr m) :
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

/-- Major-premise inductive of a recursor type: peel `skip` foralls, then
    scan (bounded) for the first forall whose domain head is an inductive. -/
partial def getMajorInductiveId (recTy : KExpr m) (skip : UInt64) :
    RecM m (KId m) := do
  let mut ty := recTy
  for _ in [0:skip.toNat] do
    let w ← whnf ty
    match w with
    | .all _ _ _ body _ => ty := body
    | _ => throw (.other "get_major_inductive_id: not enough foralls")
  for _ in [0:9] do
    let w ← whnf ty
    match w with
    | .all _ _ dom body _ =>
      let (head, _) := dom.collectSpine
      if let .const id _ _ := head then
        if let some (.indc ..) ← TcM.tryGetConst id then
          return id
      ty := body
    | _ => throw (.other "get_major_inductive_id: expected forall at major")
  throw (.other
    "get_major_inductive_id: no inductive-headed forall within scan bound")

/-- Nat primitives: succ-collapse, binary arithmetic, boolean predicates. -/
partial def tryReduceNat (e : KExpr m) : RecM m (Option (KExpr m)) :=
  tryReduceNatWithSuccMode e .collapse

partial def tryReduceNatWithSuccMode (e : KExpr m)
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

/-- Collapse a `Nat.succ` chain onto a literal (with stuck-chain memo: the
    inner WHNF runs in `stuck` mode which bypasses caches, so without the
    memo a stuck `succ^k(x)` re-peels from every depth — O(k²)). -/
partial def tryReduceNatSuccIter (arg : KExpr m) :
    RecM m (Option (KExpr m)) := do
  let entryKey ← TcM.whnfKey arg
  if (← get).env.natSuccStuck.contains entryKey then
    return none
  let mut visited : Array (Address × Address) := #[entryKey]
  let mut offset : Nat := 1
  let mut cur := arg
  repeat
    if let some result ← tryReduceNatSuccLinearRec cur offset then
      return some result
    let w ← whnfWithNatSuccMode cur .stuck
    if let some n := extractNatLit w (← prims) then
      return some (natExprFromValue (n + offset))
    let (head, args) := w.collectSpine
    let isSucc ← match head with
      | .const id _ _ =>
        pure (id.addr == (← prims).natSucc.addr && args.size == 1)
      | _ => pure false
    if isSucc then
      offset := offset + 1
      cur := args[0]!
      let curKey ← TcM.whnfKey cur
      if (← get).env.natSuccStuck.contains curKey then
        -- Known-stuck suffix ⇒ the whole chain above is stuck too.
        let vs := visited
        modify fun s => { s with env := { s.env with
          natSuccStuck := vs.foldl (·.insert ·) s.env.natSuccStuck } }
        return none
      visited := visited.push curKey
      -- succ(cur) can surface later as a succ-iter argument too.
      visited := visited.push (← TcM.whnfKey w)
      continue
    let vs := visited
    modify fun s => { s with env := { s.env with
      natSuccStuck := vs.foldl (·.insert ·) s.env.natSuccStuck } }
    return none
  return none

/-- `Nat.rec base step (lit n)` where step = `fun _ ih => Nat.succ ih`:
    compute `base + n + offset` directly. -/
partial def tryReduceNatSuccLinearRec (arg : KExpr m) (offset : Nat) :
    RecM m (Option (KExpr m)) := do
  let some parts ← natRecLiteralParts arg | return none
  let some base := parts.spine[parts.baseIdx]? | return none
  let some step := parts.spine[parts.stepIdx]? | return none
  if !(← isNatSuccIhStep step) then
    return none
  let baseWhnf ← whnf base
  let some baseVal := extractNatValue baseWhnf (← prims) | return none
  return some (natExprFromValue (baseVal + parts.major + offset))

partial def natRecLiteralParts (e : KExpr m) :
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
  return some { spine, major, baseIdx, stepIdx }

partial def isNatSuccIhStep (step : KExpr m) : RecM m Bool := do
  let step ← whnf step
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
partial def whnfNatReducerArg (arg : KExpr m) :
    RecM m (Option (KExpr m)) := do
  if !arg.hasFVars || (← get).eagerReduce then
    return some (← whnf arg)
  let savedFuel := (← get).recFuel
  let localFuel := min savedFuel natReducerOpenArgRecFuel
  modify fun s => { s with recFuel := localFuel }
  let result : Except (TcError m) (KExpr m) ←
    try
      let w ← whnf arg
      pure (Except.ok w)
    catch e =>
      pure (Except.error e)
  let consumed := localFuel - (← get).recFuel
  modify fun s => { s with recFuel := savedFuel - min savedFuel consumed }
  match result with
  | .ok w => return some w
  | .error .maxRecDepth | .error .maxRecFuel => return none
  | .error e => throw e

partial def tryReduceNatPredicate (addr : Address) (args : Array (KExpr m)) :
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

/-- Native Nat.decLe/decEq/decLt on literals → `Decidable.isTrue/isFalse`
    with the canonical kernel proof terms; `decLt n m → decLe (n+1) m`;
    Int decidables get literal *normalization* only. `decLe false` falls to
    delta (needs the `False` primitive). -/
partial def tryReduceDecidable (e : KExpr m) : RecM m (Option (KExpr m)) := do
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
  let wa ← whnf args[0]!
  let wb ← whnf args[1]!
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
  let some prop ← (do
    let some eTy ← try? (TcM.withInferOnly ((← read).infer e))
      | return none
    let eTyWhnf ← whnf eTy
    let (_, typeArgs) := eTyWhnf.collectSpine
    return typeArgs[0]?) | return none
  let (bResult, proofTrueFn, proofFalseFn) :=
    if isDecLe then
      (aVal.ble bVal, p.natLeOfBleEqTrue, p.natNotLeOfNotBleEqTrue)
    else
      (aVal == bVal, p.natEqOfBeqEqTrue, p.natNeOfBeqEqFalse)
  let resultExpr ← if bResult then do
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
      let r ← TcM.intern (KExpr.mkApp isTrue prop)
      TcM.intern (KExpr.mkApp r proof)
    else if isDecEq then do
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
      let r ← TcM.intern (KExpr.mkApp isFalse prop)
      TcM.intern (KExpr.mkApp r proof)
    else
      -- decLe false: fall through to delta.
      return none
  return some (← finishAppResult resultExpr args 2)

/-- Normalize Int decidable arguments to canonical ctor-form literals (the
    delta+iota chain then reduces them; no native Int evaluation). -/
partial def tryNormalizeIntDecidable (addr : Address)
    (args : Array (KExpr m)) : RecM m (Option (KExpr m)) := do
  if args.size < 2 then
    return none
  let wa ← whnf args[0]!
  let wb ← whnf args[1]!
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
partial def tryQuotReduce (e : KExpr m) : RecM m (Option (KExpr m)) := do
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
  let majorWhnf ← whnf args[majorIdx]!
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

/-- BitVec native reduction (BitVec.toNat/ofNat/ult, decide-lt) —
    **deferred** for v1 (falls back to delta/iota). TODO(post-v1): port
    whnf.rs `try_reduce_bitvec` + `try_eval_nat_value_for_pred`. -/
partial def tryReduceBitvec (_e : KExpr m) : RecM m (Option (KExpr m)) :=
  return none

/-- Native reduction: `Lean.reduceBool/reduceNat` markers,
    `System.Platform.numBits ⇒ 64` (also the `Subtype.val (getNumBits ())`
    form), and the PUnit/Unit SizeOf singletons. -/
partial def tryReduceNative (e : KExpr m) : RecM m (Option (KExpr m)) := do
  let (head, args) := e.collectSpine
  let .const id _ _ := head | return none
  let p ← prims
  let headAddr := id.addr
  let isUnitSizeofImpl := headAddr == p.punitSizeOf1.addr && args.size == 1
  if e.lbr > 0 then
    if isUnitSizeofImpl then
      return some (natLiteral 1)
    return none
  -- `System.Platform.numBits` via the subtype projection of getNumBits ().
  if headAddr == p.subtypeVal.addr && args.size == 3 then
    let (valueHead, valueArgs) := args[2]!.collectSpine
    if valueArgs.size == 1 then
      if let .const valueId _ _ := valueHead then
        if valueId.addr == p.systemPlatformGetNumBits.addr then
          return some (natLiteral 64)
  -- PUnit/Unit SizeOf instance is extensionally the constant 1.
  if headAddr == p.sizeOfSizeOf.addr && args.size == 3 then
    let (tyHead, _) := args[0]!.collectSpine
    if let .const tyId _ _ := tyHead then
      if tyId.addr == p.unit.addr || tyId.addr == p.punit.addr then
        return some (natLiteral 1)
  if isUnitSizeofImpl then
    return some (natLiteral 1)
  if headAddr == p.systemPlatformNumBits.addr && args.isEmpty then
    return some (natLiteral 64)
  let isReduceBool := headAddr == p.reduceBool.addr
  let isReduceNat := headAddr == p.reduceNat.addr
  if !isReduceBool && !isReduceNat then
    return none
  if args.size != 1 then
    return none
  -- Re-entrancy guard: whnf → native → whnf → native.
  if (← get).inNativeReduce then
    return none
  let .const argId argUs _ := args[0]! | return none
  let body ← match (← TcM.tryGetConst argId) with
    | some (.defn (val := val) ..) => pure val
    | _ => return none
  let body ← TcM.instantiateUnivParams body argUs
  modify fun s => { s with inNativeReduce := true }
  let result : Except (TcError m) (KExpr m) ←
    try
      let r ← whnf body
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

/-- String literal primitives: `String.back` / legacy back /
    `utf8ByteSize` / `toByteArray ""`. -/
partial def tryReduceString (e : KExpr m) : RecM m (Option (KExpr m)) := do
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
  if isUtf8ByteSize then
    return some (← TcM.intern (natExprFromValue s.utf8ByteSize : KExpr m))
  if isToByteArray then
    if s.isEmpty then
      return some (← TcM.intern (.mkConst p.byteArrayEmpty #[]))
    return none
  let codepoint := (s.toList.getLast?.map (·.toNat)).getD 65
  charOfNatExpr codepoint

partial def charOfNatExpr (n : Nat) : RecM m (Option (KExpr m)) := do
  let charOfNat ← TcM.intern (.mkConst (← prims).charOfNat #[])
  let natLit ← TcM.intern (natExprFromValue n : KExpr m)
  return some (← TcM.intern (KExpr.mkApp charOfNat natLit))

-- ### `is_rec` verification (inductive.rs `computed_is_rec` — hosted here
-- because struct-likeness needs it; `Ix.Tc.Inductive` reuses it)

partial def discoverBlockInductives (blockId : KId m) :
    RecM m (Array (KId m)) := do
  let some members ← TcM.tryGetBlock blockId | return #[]
  let mut inds : Array (KId m) := #[]
  for id in members do
    if let some (.indc ..) ← TcM.tryGetConst id then
      inds := inds.push id
  return inds

/-- Constructive `is_rec`: any constructor field (after params) mentioning
    any inductive of the mutual block. Provisional-true cache entry guards
    re-entrancy through whnf → struct-eta → isStructLike. -/
partial def computedIsRec (ind : KId m) : RecM m Bool := do
  if let some v := (← get).env.isRecCache[ind.addr]? then
    return v
  let (params, ctors, block) ← match (← TcM.getConst ind) with
    | .indc (params := params) (ctors := ctors) (block := block) .. =>
      pure (params, ctors, block)
    | _ => throw (.other "computed_is_rec: not an inductive")
  modify fun s => { s with env := { s.env with
    isRecCache := s.env.isRecCache.insert ind.addr true } }
  let blockInds ← discoverBlockInductives block
  let blockAddrs := blockInds.map (·.addr)
  try
    let v ← computeIsRec ctors params.toNat blockAddrs
    modify fun s => { s with env := { s.env with
      isRecCache := s.env.isRecCache.insert ind.addr v } }
    return v
  catch e =>
    modify fun s => { s with env := { s.env with
      isRecCache := s.env.isRecCache.erase ind.addr } }
    throw e

partial def computeIsRec (ctors : Array (KId m)) (nParams : Nat)
    (blockAddrs : Array Address) : RecM m Bool := do
  for ctorId in ctors do
    let ctorTy ← match (← TcM.tryGetConst ctorId) with
      | some (.ctor (ty := ty) ..) => pure ty
      | _ => continue
    let mut ty := ctorTy
    for _ in [0:nParams] do
      let w ← whnf ty
      match w with
      | .all _ _ _ body _ => ty := body
      | _ => break
    repeat
      let w ← whnf ty
      match w with
      | .all _ _ dom body _ =>
        if exprMentionsAnyAddr dom blockAddrs then
          return true
        ty := body
      | _ => break
  return false

end

end RecM

end Ix.Tc

end
end
