/-
  Ix.AuxGen.Kernel: the aux_gen ↔ kernel bridge.

  Port of the kernel-facing half of
  `crates/compile/src/compile/aux_gen/expr_utils.rs` (:1726-3232) plus the
  compile-side entry points of `crates/kernel/src/ingress.rs` (:2097-2270).
  aux_gen needs exactly four kernel operations — `whnf`, `infer` +
  `ensureSort`, `isDefEq`, `isLargeEliminator` — over Meta-mode `KExpr`;
  the pure-Lean kernel `Ix.Tc` exposes all four (Knot.lean), so this file
  only supplies the VALUE bridge:

  - `Ix.Expr → KExpr .meta` (`toKexprStatic` for open terms in an FVar
    context, `leanExprToKexprCached` for closed constants with the
    ingress cache), and back (`kexprToLean`);
  - kenv population (`ensurePreludeInKenvOf` hardcoded PUnit/PProd,
    `ensureInKenvOf` family) under PROVISIONAL addresses
    (`resolveLeanNameAddr`: compiled address if known, else the name
    hash — mirrors KernelCtx's "addresses may shift" model);
  - `TcScope`: a scoped view running `Ix.Tc.TcM` actions against the
    bridge state, with the fault-in retry loop and WHNF source-name
    restoration.

  State model: Rust's `KernelCtx { kenv }` + `KEnv.ingress_cache` become
  `AuxKernelCtx { tcState, ingressCache }` — the cache lives HERE, not in
  `Ix.Tc.KEnv` (`Ix/Tc` is consumed, never modified). Rust's fresh
  `TypeChecker::new(&mut kenv)` per scope = fresh `TcState.new` carrying
  over the persistent `KEnv` (whose whnf/infer caches live inside it,
  matching the Rust split of TC-transient vs kenv-persistent state).
-/
module
public import Ix.Common
public import Ix.Address
public import Ix.Environment
public import Ix.CompileM
public import Ix.Tc
public import Ix.AuxGen.Types
public import Ix.AuxGen.ExprUtils
public import Ix.AuxGen.Levels
public import Ix.AuxGen.Nested
public section

namespace Ix.AuxGen

open Ix.CompileM (CompileM CompileError)

abbrev MKExpr := Ix.Tc.KExpr .meta
abbrev MKUniv := Ix.Tc.KUniv .meta
abbrev MKId := Ix.Tc.KId .meta
abbrev MKConst := Ix.Tc.KConst .meta

/-- Inverse of `Ix.Tc.EgressLean.safetyToLean`. -/
def safetyOfLean : Lean.DefinitionSafety → Ix.DefinitionSafety
  | .unsafe => .unsaf | .safe => .safe | .partial => .part

/-- Inverse of `Ix.Tc.EgressLean.quotKindToLean`. -/
def quotKindOfLean : Lean.QuotKind → Ix.QuotKind
  | .type => .type | .ctor => .ctor | .lift => .lift | .ind => .ind

/-! ## Address resolution (provisional) -/

/-- Name→address view for the bridge. Mirrors Rust
    `resolve_lean_name_addr` (kernel ingress.rs:2133): compiled address
    (`name_to_addr`), then aux table, then the NAME HASH as a provisional
    stand-in. Provisional addresses are internally consistent within one
    bridge kenv — that is all the kernel needs. -/
structure AddrMaps where
  nameToAddr : Name → Option Address
  auxNameToAddr : Name → Option Address := fun _ => none

def AddrMaps.resolve (maps : AddrMaps) (name : Name) : Address :=
  match maps.nameToAddr name with
  | some a => a
  | none =>
    match maps.auxNameToAddr name with
    | some a => a
    | none => name.getHash

/-- The compile-env view (production callers thread `auxNameToAddr` from
    block state once orchestration lands; mirrors `stt.resolve_addr`,
    compile.rs:261-274). -/
def AddrMaps.ofCompileEnv (cenv : Ix.CompileM.CompileEnv)
    (aux : Std.HashMap Name Address := {}) : AddrMaps where
  nameToAddr := fun n => (cenv.nameToNamed.get? n).map (·.addr)
  auxNameToAddr := fun n => aux.get? n

/-! ## Level conversions -/

/-- `Ix.Level → KUniv .meta` with positional params. Mirrors Rust
    `lean_level_to_kuniv` (kernel ingress.rs:2097) — including the panic
    on unknown params (a construction bug, not a user error). Note the
    SMART `mkMax`/`mkIMax` (Rust `KUniv::max/imax` normalize). -/
partial def leanLevelToKuniv (lvl : Level) (paramNames : Array Name) : MKUniv :=
  match lvl with
  | .zero _ => Ix.Tc.KUniv.mkZero
  | .succ l _ => Ix.Tc.KUniv.mkSucc (leanLevelToKuniv l paramNames)
  | .max a b _ =>
    Ix.Tc.KUniv.mkMax (leanLevelToKuniv a paramNames)
      (leanLevelToKuniv b paramNames)
  | .imax a b _ =>
    Ix.Tc.KUniv.mkIMax (leanLevelToKuniv a paramNames)
      (leanLevelToKuniv b paramNames)
  | .param name _ =>
    match paramNames.findIdx? (· == name) with
    | some idx => Ix.Tc.KUniv.mkParam idx.toUInt64 name
    | none =>
      panic! s!"unknown level param `{name.pretty}` not found in param_names \
{paramNames.toList.map (·.pretty)}"
  | .mvar _ _ => panic! "leanLevelToKuniv: level metavariable"

/-- `KUniv .meta → Ix.Level` via positional param names, RAW max/imax
    constructors (no smart simplification). Mirrors Rust `kuniv_to_level`
    (aux_gen/below.rs:1689) including the `u_{idx}` fallback. -/
partial def kunivToLevel (u : MKUniv) (paramNames : Array Name) : Level :=
  match u with
  | .zero _ => Level.mkZero
  | .succ inner _ => Level.mkSucc (kunivToLevel inner paramNames)
  | .max a b _ =>
    Level.mkMax (kunivToLevel a paramNames) (kunivToLevel b paramNames)
  | .imax a b _ =>
    Level.mkIMax (kunivToLevel a paramNames) (kunivToLevel b paramNames)
  | .param idx _ _ =>
    match paramNames[idx.toNat]? with
    | some name => Level.mkParam name
    | none => Level.mkParam (Name.mkStr .mkAnon s!"u_{idx.toNat}")

/-! ## Bridge state -/

/-- Rust `KernelCtx` + `KEnv.ingress_cache`. The cache key is
    `(expr contentHash, paramNamesHash)` — Rust ingress.rs:2216. -/
structure AuxKernelCtx where
  tcState : Ix.Tc.TcState .meta
  ingressCache : Std.HashMap (Address × Address) MKExpr := {}

/-- Fresh bridge context: empty Meta kenv, canonical prim addresses with
    no resolver (prim KIds get synthetic display names; the accelerations
    simply never match the provisional-address constants — same shape as
    the Rust bridge, whose static prim addresses don't match either). -/
def AuxKernelCtx.new : AuxKernelCtx :=
  { tcState := Ix.Tc.TcState.new {}
      (Ix.Tc.Primitives.ofResolve .canonical fun _ => none) }

/-- Bridge monad: aux kernel state over CompileM. -/
abbrev KBridgeM := StateT AuxKernelCtx CompileM

/-- Run an `Ix.Tc.TcM` action against the bridge's kernel state,
    threading the state back in BOTH outcomes (Rust's `&mut` semantics —
    caches warmed by a failing call stay warm). -/
def runTc (act : Ix.Tc.TcM .meta α) : KBridgeM (Except (Ix.Tc.TcError .meta) α) := do
  let kctx ← get
  match act kctx.tcState with
  | .ok a st' =>
    set { kctx with tcState := st' }
    return .ok a
  | .error e st' =>
    set { kctx with tcState := st' }
    return .error e

/-- Insert a constant into the bridge kenv. -/
def kenvInsert (id : MKId) (kc : MKConst) : KBridgeM Unit :=
  modify fun kctx => { kctx with tcState := { kctx.tcState with
    env := { kctx.tcState.env with
      consts := kctx.tcState.env.consts.insert id kc } } }

def kenvGet? (id : MKId) : KBridgeM (Option MKConst) := do
  return (← get).tcState.env.consts.get? id

/-- Intern a KExpr through the kenv's intern table (Rust
    `kenv.intern.intern_expr`). -/
def internK (e : MKExpr) : KBridgeM MKExpr := do
  let kctx ← get
  let (e', it') := kctx.tcState.env.intern.internExpr e
  set { kctx with tcState := { kctx.tcState with
    env := { kctx.tcState.env with intern := it' } } }
  return e'

/-! ## Closed-term ingress (Ix.Expr → KExpr, cached) -/

/-- Blake3 over `len(u64 LE) ++ each name hash`. Mirrors Rust
    `param_names_hash` (kernel ingress.rs:2159). -/
def paramNamesHash (paramNames : Array Name) : Address := Id.run do
  let mut buf := ByteArray.empty
  buf := buf ++ (UInt64.ofNat paramNames.size).toLEBytes
  for n in paramNames do
    buf := buf ++ n.getHash.hash
  return Address.blake3 buf

/-- Closed-term `Ix.Expr → KExpr .meta`, cached by
    `(expr hash, paramNames hash)` and interned. Mirrors Rust
    `lean_expr_to_zexpr_cached`/`_raw` (kernel ingress.rs:2232/:2273):
    consecutive `mdata` wrappers accumulate onto the innermost node;
    `binderNames` is the de-Bruijn display-name stack (cache staleness on
    Var names is benign — the kernel never consults them). -/
partial def leanExprToKexprCached (e : Expr) (paramNames : Array Name)
    (binderNames : Array Name) (pnHash : Address) (maps : AddrMaps)
    : KBridgeM MKExpr := do
  let key := (e.getHash, pnHash)
  if let some hit := (← get).ingressCache.get? key then
    return hit

  -- Accumulate consecutive mdata wrappers.
  let mut mdataLayers : Array Ix.Tc.MData := #[]
  let mut cur := e
  let mut go := true
  while go do
    match cur with
    | .mdata kv inner _ =>
      mdataLayers := mdataLayers.push kv
      cur := inner
    | _ => go := false

  let raw ← match cur with
    | .bvar idx _ =>
      let name := Id.run do
        if idx < binderNames.size then
          return binderNames[binderNames.size - 1 - idx]!
        return Name.mkAnon
      pure (Ix.Tc.KExpr.mkVar (UInt64.ofNat idx) name mdataLayers)
    | .sort lvl _ =>
      pure (Ix.Tc.KExpr.mkSort (leanLevelToKuniv lvl paramNames) mdataLayers)
    | .const name us _ =>
      let zid : MKId := ⟨maps.resolve name, name⟩
      let zus := us.map (leanLevelToKuniv · paramNames)
      pure (Ix.Tc.KExpr.mkConst zid zus mdataLayers)
    | .app f a _ =>
      let fk ← leanExprToKexprCached f paramNames binderNames pnHash maps
      let ak ← leanExprToKexprCached a paramNames binderNames pnHash maps
      pure (Ix.Tc.KExpr.mkApp fk ak mdataLayers)
    | .forallE binderName dom body bi _ =>
      let dk ← leanExprToKexprCached dom paramNames binderNames pnHash maps
      let bk ← leanExprToKexprCached body paramNames
        (binderNames.push binderName) pnHash maps
      pure (Ix.Tc.KExpr.mkAll binderName bi dk bk mdataLayers)
    | .lam binderName dom body bi _ =>
      let dk ← leanExprToKexprCached dom paramNames binderNames pnHash maps
      let bk ← leanExprToKexprCached body paramNames
        (binderNames.push binderName) pnHash maps
      pure (Ix.Tc.KExpr.mkLam binderName bi dk bk mdataLayers)
    | .letE binderName ty val body nd _ =>
      let tk ← leanExprToKexprCached ty paramNames binderNames pnHash maps
      let vk ← leanExprToKexprCached val paramNames binderNames pnHash maps
      let bk ← leanExprToKexprCached body paramNames
        (binderNames.push binderName) pnHash maps
      pure (Ix.Tc.KExpr.mkLet binderName tk vk bk nd mdataLayers)
    | .proj pname idx s _ =>
      let zid : MKId := ⟨maps.resolve pname, pname⟩
      let sk ← leanExprToKexprCached s paramNames binderNames pnHash maps
      pure (Ix.Tc.KExpr.mkPrj zid (UInt64.ofNat idx) sk mdataLayers)
    | .lit (.natVal n) _ =>
      -- Compile-side blob convention: 8-byte u64 LE (Rust to_kexpr_static
      -- / ingress use `nat_to_u64(n).to_le_bytes()`), NOT the kernel's
      -- trimmed `natBlob`.
      pure (Ix.Tc.KExpr.mkNat n (Address.blake3 (UInt64.ofNat n).toLEBytes) mdataLayers)
    | .lit (.strVal s) _ =>
      pure (Ix.Tc.KExpr.mkStr s (Address.blake3 s.toUTF8) mdataLayers)
    | .fvar _ _ =>
      -- Closed-term converter: fvars have no meaning here (Rust `_raw`
      -- has no Fvar arm reachable from ensure-in-kenv callers).
      pure (Ix.Tc.KExpr.mkSort Ix.Tc.KUniv.mkZero)
    | .mvar _ _ =>
      pure (Ix.Tc.KExpr.mkSort Ix.Tc.KUniv.mkZero)
    | .mdata .. => unreachable!

  let result ← internK raw
  modify fun kctx =>
    { kctx with ingressCache := kctx.ingressCache.insert key result }
  return result

/-- Entry point mirroring Rust `lean_expr_to_zexpr_with_kenv`
    (kernel ingress.rs:2193). -/
def leanExprToKexpr (e : Expr) (paramNames : Array Name) (maps : AddrMaps)
    : KBridgeM MKExpr :=
  leanExprToKexprCached e paramNames #[] (paramNamesHash paramNames) maps

/-! ## Kenv population -/

/-- Hardcoded authoritative PUnit/PProd `KConst`s, inserted before any
    ingress (aux `.below` uses PUnit/PProd; `ingress_field_deps` may have
    stubbed them as axioms with wrong types — overwrite is intended).
    Mirrors Rust `ensure_prelude_in_kenv_of` (expr_utils.rs:1726). -/
def ensurePreludeInKenvOf (maps : AddrMaps) : KBridgeM Unit := do
  let punitName := Name.mkStr .mkAnon "PUnit"
  let punitId : MKId := ⟨maps.resolve punitName, punitName⟩

  -- Fast path: PUnit already a real Indc ⇒ assume PProd is too.
  if let some (.indc ..) ← kenvGet? punitId then
    return

  let uName := Name.mkStr .mkAnon "u"
  -- PUnit.{u} : Sort u ; PUnit.unit : PUnit.{u}
  let u0 : MKUniv := Ix.Tc.KUniv.mkParam 0 uName
  let punitTy := Ix.Tc.KExpr.mkSort u0
  let unitName := Name.mkStr punitName "unit"
  let unitId : MKId := ⟨maps.resolve unitName, unitName⟩
  let unitTy := Ix.Tc.KExpr.mkConst punitId #[Ix.Tc.KUniv.mkParam 0 uName]
  kenvInsert unitId (.ctor unitName #[uName] false 1 punitId 0 0 0 unitTy)
  kenvInsert punitId
    (.indc punitName #[uName] 1 0 0 false punitId 0 punitTy #[unitId] #[])

  -- PProd.{u,v} (α : Sort u) (β : Sort v) : Sort (max 1 u v)
  let pprodName := Name.mkStr .mkAnon "PProd"
  let pprodId : MKId := ⟨maps.resolve pprodName, pprodName⟩
  let vName := Name.mkStr .mkAnon "v"
  let alphaName := Name.mkStr .mkAnon "α"
  let betaName := Name.mkStr .mkAnon "β"
  let fstName := Name.mkStr .mkAnon "fst"
  let sndName := Name.mkStr .mkAnon "snd"
  let u0' : MKUniv := Ix.Tc.KUniv.mkParam 0 uName
  let u1 : MKUniv := Ix.Tc.KUniv.mkParam 1 vName
  let sortU := Ix.Tc.KExpr.mkSort u0'
  let sortV := Ix.Tc.KExpr.mkSort u1
  -- Lean stores `max 1 u v` LEFT-associated: max(max(1,u),v). Essential:
  -- after substitution the normalizing max collapses differently for the
  -- right-associated form (expr_utils.rs:1813-1821).
  let max1uv := Ix.Tc.KUniv.mkMax
    (Ix.Tc.KUniv.mkMax (Ix.Tc.KUniv.mkSucc Ix.Tc.KUniv.mkZero) u0') u1
  let pprodTy := Ix.Tc.KExpr.mkAll alphaName Lean.BinderInfo.default sortU
    (Ix.Tc.KExpr.mkAll betaName Lean.BinderInfo.default sortV (Ix.Tc.KExpr.mkSort max1uv))
  -- PProd.mk : {α : Sort u} → {β : Sort v} → α → β → PProd.{u,v} α β
  let mkName := Name.mkStr pprodName "mk"
  let mkId : MKId := ⟨maps.resolve mkName, mkName⟩
  let pprodApp := Ix.Tc.KExpr.mkApp
    (Ix.Tc.KExpr.mkApp (Ix.Tc.KExpr.mkConst pprodId #[u0', u1])
      (Ix.Tc.KExpr.mkVar 3 Name.mkAnon))
    (Ix.Tc.KExpr.mkVar 2 Name.mkAnon)
  let mkTy := Ix.Tc.KExpr.mkAll alphaName Lean.BinderInfo.implicit sortU
    (Ix.Tc.KExpr.mkAll betaName Lean.BinderInfo.implicit sortV
      (Ix.Tc.KExpr.mkAll fstName Lean.BinderInfo.default (Ix.Tc.KExpr.mkVar 1 Name.mkAnon)
        (Ix.Tc.KExpr.mkAll sndName Lean.BinderInfo.default (Ix.Tc.KExpr.mkVar 1 Name.mkAnon)
          pprodApp)))
  kenvInsert mkId (.ctor mkName #[uName, vName] false 2 pprodId 0 2 2 mkTy)
  kenvInsert pprodId
    (.indc pprodName #[uName, vName] 2 2 0 false pprodId 0 pprodTy #[mkId] #[])

/-- Ingress ONE Lean constant into the bridge kenv (non-transitive; see
    the Rust contract note — callers own the dependency closure, missing
    deps surface as `unknownConst` at TC time and are faulted in).
    Mirrors Rust `ensure_in_kenv_of_inner_env` (expr_utils.rs:1944). -/
partial def ensureInKenvOfInner (name : Name) (maps : AddrMaps)
    (replaceAxioStub : Bool) : KBridgeM Unit := do
  let addr := maps.resolve name
  let zid : MKId := ⟨addr, name⟩

  if let some existing ← kenvGet? zid then
    -- Only axiom stubs may be upgraded; never overwrite real entries.
    match existing with
    | .axio .. => if !replaceAxioStub then return
    | _ => return

  let some ci ← lookupConst? name | return

  match ci with
  | .inductInfo ind =>
    let lp := ind.cnst.levelParams
    let nLvls := UInt64.ofNat lp.size
    let tyZ ← leanExprToKexpr ind.cnst.type lp maps
    let mut ctorZids : Array MKId := #[]
    for ctorName in ind.ctors do
      if let some (.ctorInfo ctor) ← lookupConst? ctorName then
        let ctorZid : MKId := ⟨maps.resolve ctorName, ctorName⟩
        let ty ← leanExprToKexpr ctor.cnst.type lp maps
        kenvInsert ctorZid (.ctor ctorName lp ctor.isUnsafe nLvls zid
          (UInt64.ofNat ctorZids.size) (UInt64.ofNat ctor.numParams)
          (UInt64.ofNat ctor.numFields) ty)
        ctorZids := ctorZids.push ctorZid
    kenvInsert zid (.indc name lp nLvls (UInt64.ofNat ind.numParams)
      (UInt64.ofNat ind.numIndices) ind.isUnsafe zid 0 tyZ ctorZids #[])
  | .defnInfo d =>
    let lp := d.cnst.levelParams
    let ty ← leanExprToKexpr d.cnst.type lp maps
    let val ← leanExprToKexpr d.value lp maps
    kenvInsert zid (.defn name lp .defn (safetyOfLean d.safety) d.hints
      (UInt64.ofNat lp.size) ty val #[] zid)
  | .thmInfo d =>
    let lp := d.cnst.levelParams
    let ty ← leanExprToKexpr d.cnst.type lp maps
    let val ← leanExprToKexpr d.value lp maps
    kenvInsert zid (.defn name lp .thm .safe .opaque
      (UInt64.ofNat lp.size) ty val #[] zid)
  | .opaqueInfo d =>
    let lp := d.cnst.levelParams
    let ty ← leanExprToKexpr d.cnst.type lp maps
    let val ← leanExprToKexpr d.value lp maps
    kenvInsert zid (.defn name lp .opaq .safe .opaque
      (UInt64.ofNat lp.size) ty val #[] zid)
  | .axiomInfo a =>
    let lp := a.cnst.levelParams
    let ty ← leanExprToKexpr a.cnst.type lp maps
    kenvInsert zid (.axio name lp a.isUnsafe (UInt64.ofNat lp.size) ty)
  | .quotInfo q =>
    let lp := q.cnst.levelParams
    let ty ← leanExprToKexpr q.cnst.type lp maps
    kenvInsert zid (.quot name lp (quotKindOfLean q.kind) (UInt64.ofNat lp.size) ty)
  | .ctorInfo ctor =>
    -- Constructors ingress via their parent (the one downstream walk).
    ensureInKenvOfInner ctor.induct maps replaceAxioStub
  | .recInfo _ =>
    -- Recursors are kernel-generated, never ingressed from Lean.
    pure ()

/-- Mirrors Rust `ensure_in_kenv_of` (expr_utils.rs:2162). -/
def ensureInKenvOf (name : Name) (maps : AddrMaps) : KBridgeM Unit :=
  ensureInKenvOfInner name maps false

/-- Stub-upgrading variant (Rust `ensure_full_in_kenv_of`,
    expr_utils.rs:2174). -/
def ensureFullInKenvOf (name : Name) (maps : AddrMaps) : KBridgeM Unit :=
  ensureInKenvOfInner name maps true

/-! ## Open-term conversion (FVar context) -/

/-- `Ix.Expr → KExpr .meta` for open terms in an FVar context: FVars
    become `Var(ctxDepth - level - 1)`, unknown FVars degrade to `Sort 0`,
    mdata is STRIPPED (unlike the closed-term ingress). Pure construction
    — no interning, no cache. Mirrors Rust `to_kexpr_static`
    (expr_utils.rs:3153). -/
partial def toKexprStatic (e : Expr) (fvarLevels : Std.HashMap Name Nat)
    (ctxDepth : Nat) (paramNames : Array Name) (maps : AddrMaps) : MKExpr :=
  match e with
  | .fvar fname _ =>
    match fvarLevels.get? fname with
    | some level => Ix.Tc.KExpr.mkVar (UInt64.ofNat (ctxDepth - level - 1)) .mkAnon
    | none => Ix.Tc.KExpr.mkSort Ix.Tc.KUniv.mkZero
  | .bvar idx _ => Ix.Tc.KExpr.mkVar (UInt64.ofNat idx) .mkAnon
  | .sort lvl _ => Ix.Tc.KExpr.mkSort (leanLevelToKuniv lvl paramNames)
  | .const cname us _ =>
    let zid : MKId := ⟨maps.resolve cname, cname⟩
    Ix.Tc.KExpr.mkConst zid (us.map (leanLevelToKuniv · paramNames))
  | .app f a _ =>
    Ix.Tc.KExpr.mkApp (toKexprStatic f fvarLevels ctxDepth paramNames maps)
      (toKexprStatic a fvarLevels ctxDepth paramNames maps)
  | .forallE binderName dom body bi _ =>
    Ix.Tc.KExpr.mkAll binderName bi
      (toKexprStatic dom fvarLevels ctxDepth paramNames maps)
      (toKexprStatic body fvarLevels (ctxDepth + 1) paramNames maps)
  | .lam binderName dom body bi _ =>
    Ix.Tc.KExpr.mkLam binderName bi
      (toKexprStatic dom fvarLevels ctxDepth paramNames maps)
      (toKexprStatic body fvarLevels (ctxDepth + 1) paramNames maps)
  | .letE binderName ty val body nd _ =>
    Ix.Tc.KExpr.mkLet binderName
      (toKexprStatic ty fvarLevels ctxDepth paramNames maps)
      (toKexprStatic val fvarLevels ctxDepth paramNames maps)
      (toKexprStatic body fvarLevels (ctxDepth + 1) paramNames maps) nd
  | .proj pname idx s _ =>
    let zid : MKId := ⟨maps.resolve pname, pname⟩
    Ix.Tc.KExpr.mkPrj zid (UInt64.ofNat idx)
      (toKexprStatic s fvarLevels ctxDepth paramNames maps)
  | .lit (.natVal n) _ =>
    -- 8-byte u64 LE blob convention (see leanExprToKexprCached).
    Ix.Tc.KExpr.mkNat n (Address.blake3 (UInt64.ofNat n).toLEBytes)
  | .lit (.strVal s) _ =>
    Ix.Tc.KExpr.mkStr s (Address.blake3 s.toUTF8)
  | .mdata _ inner _ =>
    toKexprStatic inner fvarLevels ctxDepth paramNames maps
  | .mvar _ _ => Ix.Tc.KExpr.mkSort Ix.Tc.KUniv.mkZero

/-- `KExpr .meta → Ix.Expr` reconstructing FVars from de-Bruijn `Var`s:
    indices below `localDepth` stay BVars; above, level =
    `outerDepth - (i - localDepth) - 1` looks up `fvarLevels` (reverse
    linear scan — contexts are small). Kernel mdata layers re-wrap
    outermost-first. Mirrors Rust `kexpr_to_lean` (expr_utils.rs:2671). -/
partial def kexprToLean (e : MKExpr) (outerDepth : Nat)
    (fvarLevels : Std.HashMap Name Nat) (localDepth : Nat)
    (paramNames : Array Name) : Expr := Id.run do
  let lookupFvar (level : Nat) : Option Name :=
    fvarLevels.toList.findSome? fun (name, lvl) =>
      if lvl == level then some name else none

  let inner := match e with
    | .var i _ _ =>
      let i := i.toNat
      if i < localDepth then
        Expr.mkBVar i
      else
        let fvarIdxFromTop := i - localDepth
        if fvarIdxFromTop + 1 > outerDepth then
          panic! "kexprToLean: Var index out of range of outer context"
        else
          let level := outerDepth - fvarIdxFromTop - 1
          let name := (lookupFvar level).getD
            (Name.mkStr .mkAnon s!"_dangling_fvar_{level}")
          Expr.mkFVar name
    | .fvar id _ _ =>
      -- Kernel-side FVar nodes should never appear here (leaked open
      -- expression); surface as a synthetic free variable.
      Expr.mkFVar (Name.mkStr .mkAnon s!"_kernel_fvar_{id.id.toNat}")
    | .sort u _ => Expr.mkSort (kunivToLevel u paramNames)
    | .const kid us _ =>
      Expr.mkConst kid.name (us.map (kunivToLevel · paramNames))
    | .app f a _ =>
      Expr.mkApp (kexprToLean f outerDepth fvarLevels localDepth paramNames)
        (kexprToLean a outerDepth fvarLevels localDepth paramNames)
    | .all name bi d b _ =>
      Expr.mkForallE name
        (kexprToLean d outerDepth fvarLevels localDepth paramNames)
        (kexprToLean b outerDepth fvarLevels (localDepth + 1) paramNames) bi
    | .lam name bi d b _ =>
      Expr.mkLam name
        (kexprToLean d outerDepth fvarLevels localDepth paramNames)
        (kexprToLean b outerDepth fvarLevels (localDepth + 1) paramNames) bi
    | .letE name ty val body nd _ =>
      Expr.mkLetE name
        (kexprToLean ty outerDepth fvarLevels localDepth paramNames)
        (kexprToLean val outerDepth fvarLevels localDepth paramNames)
        (kexprToLean body outerDepth fvarLevels (localDepth + 1) paramNames) nd
    | .prj kid field val _ =>
      Expr.mkProj kid.name field.toNat
        (kexprToLean val outerDepth fvarLevels localDepth paramNames)
    | .nat n _ _ => Expr.mkLit (.natVal n)
    | .str s _ _ => Expr.mkLit (.strVal s)

  -- Re-wrap mdata layers, outermost first (matching egress order).
  return e.mdata.foldr (init := inner) fun kvs acc => Expr.mkMData kvs acc

/-! ## WHNF source-name restoration -/

/-- Same name, or both resolve to one address (alias pair). Mirrors Rust
    `same_resolved_name_addr` (expr_utils.rs:3134). -/
def sameResolvedNameAddr (a b : Name) (maps : AddrMaps) : Bool :=
  a == b || maps.resolve a == maps.resolve b

/-- Collect source-shaped subterms (`App`/`Proj`, BVar-free) keyed by
    kernel content hash, so WHNF-copied arguments can retain the caller's
    spelling. Mirrors Rust `collect_lean_source_name_hints`
    (expr_utils.rs:2791). -/
partial def collectLeanSourceNameHints (source : Expr)
    (fvarLevels : Std.HashMap Name Nat) (depth : Nat)
    (paramNames : Array Name) (maps : AddrMaps)
    (out : Std.HashMap Address Expr) : Std.HashMap Address Expr := Id.run do
  let mut out := out
  if sourceNameHintCandidate source && !exprHasBVar source then
    let key := (toKexprStatic source fvarLevels depth paramNames maps).addr
    if !out.contains key then
      out := out.insert key source
  match source with
  | .mdata _ inner _ =>
    return collectLeanSourceNameHints inner fvarLevels depth paramNames maps out
  | .app f a _ =>
    out := collectLeanSourceNameHints f fvarLevels depth paramNames maps out
    return collectLeanSourceNameHints a fvarLevels depth paramNames maps out
  | .forallE _ d b _ _ | .lam _ d b _ _ =>
    out := collectLeanSourceNameHints d fvarLevels depth paramNames maps out
    return collectLeanSourceNameHints b fvarLevels depth paramNames maps out
  | .letE _ t v b _ _ =>
    out := collectLeanSourceNameHints t fvarLevels depth paramNames maps out
    out := collectLeanSourceNameHints v fvarLevels depth paramNames maps out
    return collectLeanSourceNameHints b fvarLevels depth paramNames maps out
  | .proj _ _ v _ =>
    return collectLeanSourceNameHints v fvarLevels depth paramNames maps out
  | _ => return out

/-- Restore source spellings for copied subterms after a real reduction.
    Mirrors Rust `restore_lean_source_name_hints` (expr_utils.rs:2895). -/
partial def restoreLeanSourceNameHints (generated : Expr)
    (fvarLevels : Std.HashMap Name Nat) (depth : Nat)
    (paramNames : Array Name) (maps : AddrMaps)
    (hints : Std.HashMap Address Expr) : Expr := Id.run do
  if sourceNameHintCandidate generated && !exprHasBVar generated then
    let key := (toKexprStatic generated fvarLevels depth paramNames maps).addr
    if let some source := hints.get? key then
      return source
  match generated with
  | .app f a _ =>
    return Expr.mkApp
      (restoreLeanSourceNameHints f fvarLevels depth paramNames maps hints)
      (restoreLeanSourceNameHints a fvarLevels depth paramNames maps hints)
  | .forallE n d b bi _ =>
    return Expr.mkForallE n
      (restoreLeanSourceNameHints d fvarLevels depth paramNames maps hints)
      (restoreLeanSourceNameHints b fvarLevels depth paramNames maps hints) bi
  | .lam n d b bi _ =>
    return Expr.mkLam n
      (restoreLeanSourceNameHints d fvarLevels depth paramNames maps hints)
      (restoreLeanSourceNameHints b fvarLevels depth paramNames maps hints) bi
  | .letE n t v b nd _ =>
    return Expr.mkLetE n
      (restoreLeanSourceNameHints t fvarLevels depth paramNames maps hints)
      (restoreLeanSourceNameHints v fvarLevels depth paramNames maps hints)
      (restoreLeanSourceNameHints b fvarLevels depth paramNames maps hints) nd
  | .proj n i v _ =>
    return Expr.mkProj n i
      (restoreLeanSourceNameHints v fvarLevels depth paramNames maps hints)
  | .mdata kvs v _ =>
    return Expr.mkMData kvs
      (restoreLeanSourceNameHints v fvarLevels depth paramNames maps hints)
  | _ => return generated

/-- Restore source display names after a content-preserving WHNF
    roundtrip (kernel caches ignore display names, so a cache hit may
    return an alias's spelling). Structure-parallel walk keeping the
    GENERATED levels/binder-infos with the SOURCE names. Mirrors Rust
    `restore_source_names_same_content` (expr_utils.rs:3049). -/
partial def restoreSourceNamesSameContent (generated source : Expr)
    (maps : AddrMaps) : Expr :=
  let source := stripMdataRef source
  match generated with
  | .mdata kvs inner _ =>
    Expr.mkMData kvs (restoreSourceNamesSameContent inner source maps)
  | _ =>
    match generated, source with
    | .const genName genLvls _, .const sourceName _ _ =>
      if sameResolvedNameAddr genName sourceName maps then
        Expr.mkConst sourceName genLvls
      else generated
    | .app genF genA _, .app sourceF sourceA _ =>
      Expr.mkApp (restoreSourceNamesSameContent genF sourceF maps)
        (restoreSourceNamesSameContent genA sourceA maps)
    | .forallE _ genDom genBody genBi _, .forallE sourceName sourceDom sourceBody _ _ =>
      Expr.mkForallE sourceName
        (restoreSourceNamesSameContent genDom sourceDom maps)
        (restoreSourceNamesSameContent genBody sourceBody maps) genBi
    | .lam _ genDom genBody genBi _, .lam sourceName sourceDom sourceBody _ _ =>
      Expr.mkLam sourceName
        (restoreSourceNamesSameContent genDom sourceDom maps)
        (restoreSourceNamesSameContent genBody sourceBody maps) genBi
    | .letE _ genTy genVal genBody genNd _, .letE sourceName sourceTy sourceVal sourceBody _ _ =>
      Expr.mkLetE sourceName
        (restoreSourceNamesSameContent genTy sourceTy maps)
        (restoreSourceNamesSameContent genVal sourceVal maps)
        (restoreSourceNamesSameContent genBody sourceBody maps) genNd
    | .proj genName genField genVal _, .proj sourceName sourceField sourceVal _ =>
      if genField == sourceField
          && sameResolvedNameAddr genName sourceName maps then
        Expr.mkProj sourceName genField
          (restoreSourceNamesSameContent genVal sourceVal maps)
      else generated
    | _, _ => generated

/-! ## TcScope -/

/-- Scoped FVar-context view over the bridge kernel. Rust `TcScope`
    (expr_utils.rs:2211): a FRESH type-checker per scope (fresh
    `TcState.new` carrying the persistent kenv, `inferOnly := true`),
    with the outer FVar context pushed as kernel locals. Threaded
    explicitly through KBridgeM actions. -/
structure TcScopeSt where
  fvarLevels : Std.HashMap Name Nat
  baseDepth : Nat
  extraLocals : Nat := 0
  paramNames : Array Name
  maps : AddrMaps

namespace TcScopeSt

def depth (scope : TcScopeSt) : Nat := scope.baseDepth + scope.extraLocals

/-- Open a scope: fresh TC state over the persistent kenv, push the
    outer FVar types as kernel locals (Rust `TcScope::new`). -/
def new (outerFvarCtx : Array LocalDecl) (paramNames : Array Name)
    (maps : AddrMaps) : KBridgeM TcScopeSt := do
  -- Fresh TC portions, persistent env (caches live in KEnv).
  modify fun kctx => { kctx with tcState :=
    { Ix.Tc.TcState.new kctx.tcState.env kctx.tcState.prims with
      inferOnly := true } }
  let mut fvarLevels : Std.HashMap Name Nat := {}
  for (decl, i) in outerFvarCtx.zipIdx do
    fvarLevels := fvarLevels.insert decl.fvarName i
  let scope : TcScopeSt :=
    { fvarLevels, baseDepth := outerFvarCtx.size, paramNames, maps }
  for (decl, i) in outerFvarCtx.zipIdx do
    let kty := toKexprStatic decl.domain fvarLevels i paramNames maps
    discard <| runTc (Ix.Tc.TcM.pushLocal kty)
  return scope

/-- Push additional locals (e.g. minor-premise binders); balance with
    `popLocals`. Mirrors Rust `push_locals` (expr_utils.rs:2257). -/
def pushLocals (scope : TcScopeSt) (decls : Array LocalDecl)
    : KBridgeM TcScopeSt := do
  let mut scope := scope
  let depth0 := scope.depth
  for (decl, i) in decls.zipIdx do
    scope := { scope with
      fvarLevels := scope.fvarLevels.insert decl.fvarName (depth0 + i) }
    let kty := toKexprStatic decl.domain scope.fvarLevels (depth0 + i)
      scope.paramNames scope.maps
    discard <| runTc (Ix.Tc.TcM.pushLocal kty)
  return { scope with extraLocals := scope.extraLocals + decls.size }

/-- Mirrors Rust `pop_locals` (expr_utils.rs:2274). -/
def popLocals (scope : TcScopeSt) (decls : Array LocalDecl)
    : KBridgeM TcScopeSt := do
  let mut scope := scope
  for decl in decls.reverse do
    discard <| runTc Ix.Tc.TcM.popLocal
    scope := { scope with fvarLevels := scope.fvarLevels.erase decl.fvarName }
  return { scope with extraLocals := scope.extraLocals - decls.size }

/-- Fault one name into the TC env (full ingress, stub-upgrading);
    reports whether its resolved address is now present. Mirrors Rust
    `fault_in_name` (expr_utils.rs:2290). -/
def faultInName (scope : TcScopeSt) (name : Name) : KBridgeM Bool := do
  ensureFullInKenvOf name scope.maps
  let addr := scope.maps.resolve name
  return (← get).tcState.env.consts.toList.any fun (id, _) => id.addr == addr

/-- Reverse address lookup (linear over the compile-env views + name
    hashes; mirrors Rust `name_for_addr`, expr_utils.rs:2317). -/
def nameForAddr (addr : Address) : KBridgeM (Option Name) := do
  let cenv ← Ix.CompileM.getCompileEnv
  for (name, named) in cenv.nameToNamed do
    if named.addr == addr then
      return some name
  for (name, _) in cenv.env.consts do
    if name.getHash == addr then
      return some name
  return none

/-- Fault in the constant behind an address discovered mid-inference.
    Mirrors Rust `fault_in_addr` (expr_utils.rs:2303). -/
def faultInAddr (scope : TcScopeSt) (addr : Address) : KBridgeM Bool := do
  if (← get).tcState.env.consts.toList.any (fun (id, _) => id.addr == addr) then
    return true
  let some name ← nameForAddr addr | return false
  if !(← scope.faultInName name) then
    return false
  return (← get).tcState.env.consts.toList.any fun (id, _) => id.addr == addr

/-- Pre-fault every constant directly referenced by `e` (Rust
    `fault_in_direct_expr_consts`, expr_utils.rs:2282). -/
def faultInDirectExprConsts (scope : TcScopeSt) (e : Expr) : KBridgeM Unit := do
  let refs := collectLeanConstRefs e {}
  for name in refs do
    discard <| scope.faultInName name

/-- Non-zero level check (Rust `is_not_zero_level`, expr_utils.rs:2453). -/
partial def isNotZeroLevel : Level → Bool
  | .succ _ _ => true
  | .max a b _ => isNotZeroLevel a || isNotZeroLevel b
  | .imax _ b _ => isNotZeroLevel b
  | _ => false

/-- `KUniv → Level` substituting param indices with a Const's concrete
    level args, simplifying with `levelMax`/Lean's `mk_imax` rules.
    Mirrors Rust `kuniv_to_level_with_const_levels` (expr_utils.rs:2524). -/
partial def kunivToLevelWithConstLevels (scope : TcScopeSt) (u : MKUniv)
    (constLevels : Array Level) : Level :=
  match u with
  | .zero _ => Level.mkZero
  | .succ inner _ =>
    Level.mkSucc (kunivToLevelWithConstLevels scope inner constLevels)
  | .max a b _ =>
    levelMax (kunivToLevelWithConstLevels scope a constLevels)
      (kunivToLevelWithConstLevels scope b constLevels)
  | .imax a b _ =>
    let la := kunivToLevelWithConstLevels scope a constLevels
    let lb := kunivToLevelWithConstLevels scope b constLevels
    if isNotZeroLevel lb then
      levelMax la lb
    else if lb matches .zero _ then lb
    else if la matches .zero _ then lb
    else if (la matches .succ (.zero _) _) then lb
    else if la == lb then la
    else Level.mkIMax la lb
  | .param idx _ _ =>
    match constLevels[idx.toNat]? with
    | some l => l
    | none =>
      match scope.paramNames[idx.toNat]? with
      | some name => Level.mkParam name
      | none => Level.mkParam (Name.mkStr .mkAnon s!"u_{idx.toNat}")

/-- Fast path for `getLevel`: fully-applied constant whose stored kernel
    type telescopes to `Sort l` — read `l` directly with level-param
    substitution (Lean's `inferAppType` optimization). Mirrors Rust
    `try_infer_app_sort_level` (expr_utils.rs:2474). -/
def tryInferAppSortLevel (scope : TcScopeSt) (ty : Expr)
    : KBridgeM (Option Level) := do
  let (head, args) := decomposeApps ty
  let .const name levels _ := head | return none
  let addr := scope.maps.resolve name
  let kid : MKId := ⟨addr, name⟩
  let some kconst ← kenvGet? kid | return none
  let mut cur := kconst.ty
  for _ in [0:args.size] do
    match cur with
    | .all _ _ _ body _ => cur := body
    | _ => return none
  let .sort ku _ := cur | return none
  return some (scope.kunivToLevelWithConstLevels ku levels)

/-- Infer the sort level of a type in the current context, with the
    fault-in retry loop and forall-level normalization. Mirrors Rust
    `TcScope::get_level` (expr_utils.rs:2400). -/
partial def getLevel (scope : TcScopeSt) (ty : Expr) : KBridgeM Level := do
  if let some lvl ← scope.tryInferAppSortLevel ty then
    return lvl

  let kexpr := toKexprStatic ty scope.fvarLevels scope.depth
    scope.paramNames scope.maps

  scope.faultInDirectExprConsts ty
  let mut faultedAddrs : Std.HashSet Address := {}
  let mut inferred? : Option MKExpr := none
  while inferred?.isNone do
    match ← runTc (Ix.Tc.TcM.infer kexpr) with
    | .ok e => inferred? := some e
    | .error (.unknownConst addr) =>
      if !faultedAddrs.contains addr then
        faultedAddrs := faultedAddrs.insert addr
        if !(← scope.faultInAddr addr) then
          throw (.unsupportedExpr
            s!"TcScope::get_level: tc.infer failed: unknown constant \
{(toString addr).take 12}")
      else
        throw (.unsupportedExpr
          s!"TcScope::get_level: tc.infer failed: unknown constant \
{(toString addr).take 12}")
    | .error e =>
      throw (.unsupportedExpr
        s!"TcScope::get_level: tc.infer failed: {e}")
  let inferred := inferred?.get!

  let ku ← match ← runTc (Ix.Tc.TcM.ensureSort inferred) with
    | .ok u => pure u
    | .error e =>
      throw (.unsupportedExpr s!"TcScope::get_level: ensure_sort failed: {e}")
  let raw := kunivToLevel ku scope.paramNames
  -- Mirror Lean's `inferForallType`: normalize forall-typed levels only.
  if ty matches .forallE .. then
    return levelNormalize raw
  return raw

/-- WHNF a `LeanExpr` in the current context, restoring source display
    names (kernel caches alias same-content names). Falls back to the
    input on kernel errors. Mirrors Rust `TcScope::whnf_lean`
    (expr_utils.rs:2589). -/
def whnfLean (scope : TcScopeSt) (ty : Expr) : KBridgeM Expr := do
  let depth := scope.depth
  let kexpr := toKexprStatic ty scope.fvarLevels depth
    scope.paramNames scope.maps
  let whnfed ← match ← runTc (Ix.Tc.TcM.whnf kexpr) with
    | .ok k => pure k
    | .error _ => return ty
  let out := kexprToLean whnfed depth scope.fvarLevels 0 scope.paramNames
  if whnfed.addr == kexpr.addr then
    return restoreSourceNamesSameContent out ty scope.maps
  else
    let hints := collectLeanSourceNameHints ty scope.fvarLevels depth
      scope.paramNames scope.maps {}
    return restoreLeanSourceNameHints out scope.fvarLevels depth
      scope.paramNames scope.maps hints

/-- Definitional equality in the current context; `false` on kernel
    errors. Mirrors Rust `TcScope::is_def_eq` (expr_utils.rs:2636). -/
def isDefEq (scope : TcScopeSt) (a b : Expr) : KBridgeM Bool := do
  let depth := scope.depth
  let ka := toKexprStatic a scope.fvarLevels depth scope.paramNames scope.maps
  let kb := toKexprStatic b scope.fvarLevels depth scope.paramNames scope.maps
  match ← runTc (Ix.Tc.TcM.isDefEq ka kb) with
  | .ok r => return r
  | .error _ => return false

end TcScopeSt

end Ix.AuxGen
