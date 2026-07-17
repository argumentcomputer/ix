module

public import Ix.Tc.Monad
public import Ix.Ixon

/-!
Mirror: crates/kernel/src/ingress.rs (the Ixon → kernel, anonymous-mode half)

Anon ingress uses only `Ixon.Constant` data — never `ConstantMeta`,
`Env.named`, or `Env.names`. Projection addresses are reconstructed
deterministically from `(block, idx, [cidx])` via `serConstant` commitment,
which agrees with the addresses the compiler stores in `env.consts`.

Expression conversion is an explicit stack machine (Init-scale terms overflow
default runtime stacks under structural recursion; Rust runs the recursive
meta-mode converter on 2 GB stacks — the anon machine here is iterative).
`share` nodes expand transparently against the constant's sharing table, with
a share-index-keyed conversion cache (Lean has no stable pointers; a
deserialized subterm is only re-entered via `share`, so this captures exactly
the hits Rust's pointer-keyed cache sees). Universe conversion caches by
universe-table index for the same reason. Every constructed node is interned.

Integrity: `getConstVerified` checks `blake3(rawBytes) == addr` at
materialization. Rust's `Env::get` does this on its main path; the
`rs_de_env_lazy`-style loaders and pure-Lean `getEnv` do not, and Ix.Tc is
the soundness-critical consumer — so it verifies here (`verify := true` by
default; the driver's `CheckCfg` can disable it for benchmarking).

The reserved-marker guard (Rust panics inside `KEnv::insert`) is enforced
here in `insertEntries`, the only path feeding untrusted constants into the
kernel env.

Meta-mode ingress (arena parallel walk, name resolution, mdata layers)
lives in `Ix.Tc.IngressMeta`.
-/

public section
@[expose] section

namespace Ix.Tc

open Std (HashMap)

/-- Ingress errors are diagnostic strings (mirrors Rust's `Result<_, String>`). -/
abbrev IngressErr := String

/-- Anon kernel environment shorthand. -/
abbrev AnonEnv := KEnv .anon

/-- Ingress monad: state-threads the anon `KEnv` being populated. -/
abbrev IngressM := EStateM IngressErr AnonEnv

namespace IngressM

@[inline] def internE (e : KExpr .anon) : IngressM (KExpr .anon) := fun env =>
  let (e, it) := env.intern.internExpr e
  .ok e { env with intern := it }

@[inline] def internU (u : KUniv .anon) : IngressM (KUniv .anon) := fun env =>
  let (u, it) := env.intern.internUniv u
  .ok u { env with intern := it }

@[inline] def liftExcept : Except IngressErr α → IngressM α
  | .ok a => pure a
  | .error e => throw e

end IngressM

/-! ### Deterministic projection addresses

`blake3(serConstant ⟨.xPrj …, #[], #[], #[]⟩)` — the same commitment the
compiler uses when storing projection constants (`Ix.CompileM`), so the
kernel-side lookup key and the compile-side storage key stay in lock-step. -/

def defnProjAddr (block : Address) (idx : UInt64) : Address :=
  Address.blake3 (Ixon.serConstant ⟨.dPrj ⟨idx, block⟩, #[], #[], #[]⟩)

def indcProjAddr (block : Address) (idx : UInt64) : Address :=
  Address.blake3 (Ixon.serConstant ⟨.iPrj ⟨idx, block⟩, #[], #[], #[]⟩)

def recrProjAddr (block : Address) (idx : UInt64) : Address :=
  Address.blake3 (Ixon.serConstant ⟨.rPrj ⟨idx, block⟩, #[], #[], #[]⟩)

def ctorProjAddr (block : Address) (idx cidx : UInt64) : Address :=
  Address.blake3 (Ixon.serConstant ⟨.cPrj ⟨idx, cidx, block⟩, #[], #[], #[]⟩)

/-- Ctor projection addresses for every constructor of the inductive at
    member position `indcIdx` of `blockAddr`. -/
def anonCtorAddrs (blockAddr : Address) (indcIdx : UInt64)
    (ind : Ixon.Inductive) : Array Address :=
  (Array.range ind.ctors.size).map fun cidx =>
    ctorProjAddr blockAddr indcIdx cidx.toUInt64

/-! ### Verified constant materialization -/

/-- Materialize `addr` from the Ixon env, verifying (when `verify`) that the
    stored bytes hash back to `addr`. `none` when absent. -/
def getConstVerified (ixonEnv : Ixon.Env) (addr : Address)
    (verify : Bool := true) : Except IngressErr (Option Ixon.Constant) := do
  match ixonEnv.consts[addr]? with
  | none => return none
  | some lc =>
    if verify then
      let raw := lc.rawBytes
      let computed := Address.blake3 raw
      if computed != addr then
        throw s!"ingress: constant at {addr} fails integrity check (bytes hash to {computed})"
    match lc.get with
    | .ok c => return some c
    | .error e => throw s!"ingress: constant at {addr} failed to parse: {e}"

/-! ### Expression conversion (explicit stack machine) -/

/-- Read-only context for converting a single Ixon constant's expressions. -/
structure IngressCtx where
  sharing : Array Ixon.Expr
  refs : Array Address
  univs : Array Ixon.Univ
  /-- KIds of mutual block members, for resolving `Expr.recur`. -/
  mutCtx : Array (KId .anon)

/-- Per-constant conversion caches. -/
structure ConvState where
  /-- Converted `share` expansions, keyed by share-table index. -/
  exprCache : HashMap UInt64 (KExpr .anon) := {}
  /-- Converted universe-table roots, keyed by table index. -/
  univCache : HashMap UInt64 (KUniv .anon) := {}

/-- Conversion monad: per-constant caches over the env-threading ingress. -/
abbrev ConvM := StateT ConvState IngressM

inductive UFrame where
  | process (u : Ixon.Univ)
  | succ
  | max
  | imax
  deriving Inhabited

/-- Convert one universe tree (iterative). Uses the *simplifying*
    `mkMax`/`mkIMax` smart constructors — reduced-node addresses must match
    the Rust kernel node-for-node — and interns every node. -/
def ingressUnivTree (root : Ixon.Univ) : IngressM (KUniv .anon) := do
  let mut stack : Array UFrame := #[.process root]
  let mut values : Array (KUniv .anon) := #[]
  while !stack.isEmpty do
    let frame := stack.back!
    stack := stack.pop
    match frame with
    | .process u =>
      match u with
      | .zero =>
        values := values.push (← IngressM.internU .mkZero)
      | .succ inner =>
        stack := stack.push .succ |>.push (.process inner)
      | .max a b =>
        stack := stack.push .max |>.push (.process b) |>.push (.process a)
      | .imax a b =>
        stack := stack.push .imax |>.push (.process b) |>.push (.process a)
      | .var idx =>
        values := values.push (← IngressM.internU (.mkParam idx ()))
    | .succ =>
      let inner := values.back!
      values := values.pop
      values := values.push (← IngressM.internU (.mkSucc inner))
    | .max =>
      let b := values.back!; values := values.pop
      let a := values.back!; values := values.pop
      values := values.push (← IngressM.internU (.mkMax a b))
    | .imax =>
      let b := values.back!; values := values.pop
      let a := values.back!; values := values.pop
      values := values.push (← IngressM.internU (.mkIMax a b))
  match values.back? with
  | some v => return v
  | none => throw "ingressUnivTree: empty result stack"

/-- Convert the universe at table index `idx`, cached per constant. -/
def ingressUnivIdx (ctx : IngressCtx) (idx : UInt64) :
    ConvM (KUniv .anon) := do
  if let some cached := (← get).univCache[idx]? then
    return cached
  let some u := ctx.univs[idx.toNat]?
    | throw s!"invalid universe index {idx} (len {ctx.univs.size})"
  let ku ← liftM (ingressUnivTree u)
  modify fun s => { s with univCache := s.univCache.insert idx ku }
  return ku

/-- Convert an array of universe-table indices. -/
def ingressUnivArgs (ctx : IngressCtx) (idxs : Array UInt64) :
    ConvM (Array (KUniv .anon)) := do
  let mut out : Array (KUniv .anon) := Array.mkEmpty idxs.size
  for i in idxs do
    out := out.push (← ingressUnivIdx ctx i)
  return out

inductive EFrame where
  | process (e : Ixon.Expr)
  | appDone
  | lamDone
  | allDone
  | letDone (nd : Bool)
  | prjDone (id : KId .anon) (field : UInt64)
  | cacheShare (idx : UInt64)
  deriving Inhabited

/-- Convert one Ixon expression (explicit stack machine).

    Resolution: `sort i → univs[i]`; `ref i us → refs[i]` KId + univ args;
    `recur i us → mutCtx[i]` (the sibling *projection* KId); `nat/str i →
    refs[i]` names a blob, decoded from the env (the blob address is the hash
    payload; the value itself is never hashed); `share i` expands
    transparently against the sharing table (cached by index). -/
def ingressExpr (ixonEnv : Ixon.Env) (ctx : IngressCtx) (root : Ixon.Expr) :
    ConvM (KExpr .anon) := do
  let mut stack : Array EFrame := #[.process root]
  let mut values : Array (KExpr .anon) := #[]
  while !stack.isEmpty do
    let frame := stack.back!
    stack := stack.pop
    match frame with
    | .process e =>
      match e with
      | .share idx =>
        if let some cached := (← get).exprCache[idx]? then
          values := values.push cached
        else
          let some expansion := ctx.sharing[idx.toNat]?
            | throw s!"invalid Share index {idx}"
          stack := stack.push (.cacheShare idx) |>.push (.process expansion)
      | .var idx =>
        values := values.push (← liftM (IngressM.internE (.mkVar idx ())))
      | .sort uidx =>
        let u ← ingressUnivIdx ctx uidx
        values := values.push (← liftM (IngressM.internE (.mkSort u)))
      | .ref refIdx univIdxs =>
        let some addr := ctx.refs[refIdx.toNat]?
          | throw s!"invalid Ref index {refIdx}"
        let univs ← ingressUnivArgs ctx univIdxs
        values := values.push
          (← liftM (IngressM.internE (.mkConst ⟨addr, ()⟩ univs)))
      | .recur recIdx univIdxs =>
        let some mid := ctx.mutCtx[recIdx.toNat]?
          | throw s!"invalid Rec index {recIdx}"
        let univs ← ingressUnivArgs ctx univIdxs
        values := values.push
          (← liftM (IngressM.internE (.mkConst mid univs)))
      | .nat blobIdx =>
        let some blobAddr := ctx.refs[blobIdx.toNat]?
          | throw s!"invalid Nat blob ref index {blobIdx}"
        let some bytes := ixonEnv.getBlob? blobAddr
          | throw s!"missing Nat blob {blobAddr}"
        let val := Nat.fromBytesLE bytes.data
        values := values.push
          (← liftM (IngressM.internE (.mkNat val blobAddr)))
      | .str blobIdx =>
        let some blobAddr := ctx.refs[blobIdx.toNat]?
          | throw s!"invalid Str blob ref index {blobIdx}"
        let some bytes := ixonEnv.getBlob? blobAddr
          | throw s!"missing Str blob {blobAddr}"
        let some val := String.fromUTF8? bytes
          | throw s!"Str blob {blobAddr} is not valid UTF-8"
        values := values.push
          (← liftM (IngressM.internE (.mkStr val blobAddr)))
      | .app f a =>
        stack := stack.push .appDone |>.push (.process a) |>.push (.process f)
      | .lam ty body =>
        stack := stack.push .lamDone |>.push (.process body)
          |>.push (.process ty)
      | .all ty body =>
        stack := stack.push .allDone |>.push (.process body)
          |>.push (.process ty)
      | .letE nd ty val body =>
        stack := stack.push (.letDone nd) |>.push (.process body)
          |>.push (.process val) |>.push (.process ty)
      | .prj typeRefIdx field val =>
        let some typeAddr := ctx.refs[typeRefIdx.toNat]?
          | throw s!"invalid Prj type ref index {typeRefIdx}"
        stack := stack.push (.prjDone ⟨typeAddr, ()⟩ field)
          |>.push (.process val)
    | .appDone =>
      let a := values.back!; values := values.pop
      let f := values.back!; values := values.pop
      values := values.push (← liftM (IngressM.internE (.mkApp f a)))
    | .lamDone =>
      let body := values.back!; values := values.pop
      let ty := values.back!; values := values.pop
      values := values.push
        (← liftM (IngressM.internE (.mkLam () () ty body)))
    | .allDone =>
      let body := values.back!; values := values.pop
      let ty := values.back!; values := values.pop
      values := values.push
        (← liftM (IngressM.internE (.mkAll () () ty body)))
    | .letDone nd =>
      let body := values.back!; values := values.pop
      let val := values.back!; values := values.pop
      let ty := values.back!; values := values.pop
      values := values.push
        (← liftM (IngressM.internE (.mkLet () ty val body nd)))
    | .prjDone id field =>
      let val := values.back!; values := values.pop
      values := values.push
        (← liftM (IngressM.internE (.mkPrj id field val)))
    | .cacheShare idx =>
      let v := values.back!
      modify fun s => { s with exprCache := s.exprCache.insert idx v }
  match values.back? with
  | some v =>
    if values.size != 1 then
      throw s!"ingressExpr: unbalanced value stack ({values.size} values)"
    return v
  | none => throw "ingressExpr: empty result stack"

/-! ### Constant conversion (anon) -/

/-- One converted `(KId, KConst)` entry. -/
abbrev Entry := KId .anon × KConst .anon

/-- Insert converted entries into the kernel env, enforcing the
    reserved-marker guard (Rust panics in `KEnv::insert`; ingress is the only
    untrusted-input path, so the check lives here). -/
def guardReserved (entries : Array Entry) : IngressM Unit := do
  for (id, _) in entries do
    if let some marker := reservedMarkerName id.addr then
      throw s!"attempted to insert constant at reserved kernel marker address {marker} ({id.addr})"

/-- Standalone registration: each entry is its own single-member block. -/
def insertStandaloneEntries (entries : Array Entry) : IngressM Unit := do
  guardReserved entries
  modifyGet fun env => ((), entries.foldl (init := env) fun env (id, c) =>
    (env.insert id c).insertBlock id #[id])

/-- Muts registration: `blocks[blockId] = [m0, m0.ctors…, m1, …]` (flat, in
    generation order), block id read from the first entry's `block` field. -/
def insertMutsEntries (entries : Array Entry) : IngressM Unit := do
  guardReserved entries
  let blockId? := entries[0]?.bind fun (_, c) => match c with
    | .defn (block := b) .. => some b
    | .recr (block := b) .. => some b
    | .indc (block := b) .. => some b
    | _ => none
  modifyGet fun env => Id.run do
    let mut env := env
    if let some bid := blockId? then
      env := env.insertBlock bid (entries.map (·.1))
    for (id, c) in entries do
      env := env.insert id c
    return ((), env)

/-- Convert a `Definition`. `mutCtx` resolves `Expr.recur`; standalone
    callers pass `#[selfId]` (self-recursive standalones encode their
    self-reference as `recur 0`). Hints come from the env's `anonHints`
    channel with the Rust `Regular 0` fall-through. -/
def ingressDefnAnon (ixonEnv : Ixon.Env) (defn : Ixon.Definition)
    (selfId : KId .anon) (constant : Ixon.Constant) (block : KId .anon)
    (mutCtx : Array (KId .anon)) (hintsOverride : Option Lean.ReducibilityHints) :
    IngressM (Array Entry) := do
  let ctx : IngressCtx :=
    { sharing := constant.sharing, refs := constant.refs
      univs := constant.univs, mutCtx }
  let (ty, st) ← (ingressExpr ixonEnv ctx defn.typ).run {}
  let (val, _) ← (ingressExpr ixonEnv ctx defn.value).run st
  let hints := hintsOverride.getD (.regular 0)
  return #[(selfId,
    .defn () () defn.kind defn.safety hints defn.lvls ty val () block)]

/-- Convert a `Recursor`. `memberIdx` stays 0 on the anon path (Rust parity:
    "filled in by caller for muts blocks" — the anon caller never does). -/
def ingressRecursorAnon (ixonEnv : Ixon.Env) (rec : Ixon.Recursor)
    (selfId : KId .anon) (constant : Ixon.Constant) (block : KId .anon)
    (mutCtx : Array (KId .anon)) : IngressM (Array Entry) := do
  let ctx : IngressCtx :=
    { sharing := constant.sharing, refs := constant.refs
      univs := constant.univs, mutCtx }
  let (ty, st) ← (ingressExpr ixonEnv ctx rec.typ).run {}
  let mut st := st
  let mut rules : Array (RecRule .anon) := Array.mkEmpty rec.rules.size
  for rule in rec.rules do
    let (rhs, st') ← (ingressExpr ixonEnv ctx rule.rhs).run st
    st := st'
    rules := rules.push { ctor := (), fields := rule.fields, rhs }
  return #[(selfId,
    .recr () () rec.k rec.isUnsafe rec.lvls rec.params rec.indices
      rec.motives rec.minors block 0 ty rules ())]

/-- Convert an `Inductive` block member plus all of its constructors.
    `ctorAddrs` are the caller-computed CPrj addresses. -/
def ingressAnonInductive (ixonEnv : Ixon.Env) (ind : Ixon.Inductive)
    (selfId : KId .anon) (blockConstant : Ixon.Constant) (blockId : KId .anon)
    (memberIdx : UInt64) (ctorAddrs : Array Address)
    (mutCtx : Array (KId .anon)) : IngressM (Array Entry) := do
  if ctorAddrs.size != ind.ctors.size then
    throw s!"ingressAnonInductive: ctorAddrs.size={ctorAddrs.size} but ind.ctors.size={ind.ctors.size}"
  let ctx : IngressCtx :=
    { sharing := blockConstant.sharing, refs := blockConstant.refs
      univs := blockConstant.univs, mutCtx }
  let (ty, st) ← (ingressExpr ixonEnv ctx ind.typ).run {}
  let ctorIds : Array (KId .anon) := ctorAddrs.map (⟨·, ()⟩)
  let mut results : Array Entry := #[(selfId,
    .indc () () ind.lvls ind.params ind.indices ind.isUnsafe blockId
      memberIdx ty ctorIds ())]
  let mut st := st
  for h : cidx in [0:ind.ctors.size] do
    let ctor := ind.ctors[cidx]
    let (ctorTy, st') ← (ingressExpr ixonEnv ctx ctor.typ).run st
    st := st'
    results := results.push (ctorIds[cidx]!,
      .ctor () () ctor.isUnsafe ctor.lvls selfId ctor.cidx ctor.params
        ctor.fields ctorTy)
  return results

/-- Anon ingress for a single standalone (non-mutual) constant.
    `Defn`/`Recr` get `mutCtx = #[selfId]` for `recur 0` self-references;
    `Axio`/`Quot` cannot contain `recur`. Projections/`Muts` are not valid
    standalone entries. -/
def ingressAnonStandalone (ixonEnv : Ixon.Env) (addr : Address)
    (constant : Ixon.Constant) : IngressM (KId .anon) := do
  let selfId : KId .anon := ⟨addr, ()⟩
  let hintsOverride := ixonEnv.anonHints[addr]?
  let entries ← match constant.info with
    | .defn d =>
      ingressDefnAnon ixonEnv d selfId constant selfId #[selfId] hintsOverride
    | .recr r =>
      ingressRecursorAnon ixonEnv r selfId constant selfId #[selfId]
    | .axio a => do
      let ctx : IngressCtx :=
        { sharing := constant.sharing, refs := constant.refs
          univs := constant.univs, mutCtx := #[] }
      let (ty, _) ← (ingressExpr ixonEnv ctx a.typ).run {}
      pure #[(selfId, .axio () () a.isUnsafe a.lvls ty)]
    | .quot q => do
      let ctx : IngressCtx :=
        { sharing := constant.sharing, refs := constant.refs
          univs := constant.univs, mutCtx := #[] }
      let (ty, _) ← (ingressExpr ixonEnv ctx q.typ).run {}
      pure #[(selfId, .quot () () q.kind q.lvls ty)]
    | _ =>
      throw s!"ingressAnonStandalone: {addr} is a projection or Muts block, not a standalone"
  insertStandaloneEntries entries
  return selfId

/-- Anon ingress for an entire Muts block: every member (and every ctor of
    every inductive member) lands under its deterministic projection address.
    Verifies each computed address exists in `ixonEnv.consts` (missing ⇒
    corrupted env). Returns the member KIds in order; the first is the
    block's "primary". -/
def ingressAnonBlock (ixonEnv : Ixon.Env) (blockConstant : Ixon.Constant)
    (blockAddr : Address) : IngressM (Array (KId .anon)) := do
  let .muts members := blockConstant.info
    | throw s!"ingressAnonBlock: {blockAddr} is not a Muts block"
  let blockId : KId .anon := ⟨blockAddr, ()⟩
  -- One KId per member, addressed by its projection variant; threaded
  -- through every member's conversion so `recur i` resolves to a sibling.
  let mutCtx : Array (KId .anon) := Id.run do
    let mut out : Array (KId .anon) := Array.mkEmpty members.size
    for h : i in [0:members.size] do
      let addr := match members[i] with
        | .defn _ => defnProjAddr blockAddr i.toUInt64
        | .indc _ => indcProjAddr blockAddr i.toUInt64
        | .recr _ => recrProjAddr blockAddr i.toUInt64
      out := out.push ⟨addr, ()⟩
    return out
  let verifyProj (kind : String) (projAddr : Address) (idx : UInt64)
      (cidx : Option UInt64) : IngressM Unit := do
    if !ixonEnv.consts.contains projAddr then
      let tail := match cidx with
        | none => s!"(block {blockAddr} idx {idx})"
        | some c => s!"(block {blockAddr} idx {idx} cidx {c})"
      throw s!"ingressAnonBlock: computed {kind} address {projAddr} not present in env {tail}"
  let mut allEntries : Array Entry := #[]
  let mut memberKids : Array (KId .anon) := Array.mkEmpty members.size
  for h : i in [0:members.size] do
    let idx := i.toUInt64
    match members[i] with
    | .defn d =>
      let projAddr := defnProjAddr blockAddr idx
      verifyProj "DPrj" projAddr idx none
      let selfId : KId .anon := ⟨projAddr, ()⟩
      memberKids := memberKids.push selfId
      let hintsOverride := ixonEnv.anonHints[projAddr]?
      let entries ← ingressDefnAnon ixonEnv d selfId blockConstant blockId
        mutCtx hintsOverride
      allEntries := allEntries ++ entries
    | .recr r =>
      let projAddr := recrProjAddr blockAddr idx
      verifyProj "RPrj" projAddr idx none
      let selfId : KId .anon := ⟨projAddr, ()⟩
      memberKids := memberKids.push selfId
      let entries ← ingressRecursorAnon ixonEnv r selfId blockConstant
        blockId mutCtx
      allEntries := allEntries ++ entries
    | .indc ind =>
      let projAddr := indcProjAddr blockAddr idx
      verifyProj "IPrj" projAddr idx none
      let selfId : KId .anon := ⟨projAddr, ()⟩
      memberKids := memberKids.push selfId
      let ctorAddrs := anonCtorAddrs blockAddr idx ind
      for h : cidx in [0:ctorAddrs.size] do
        verifyProj "CPrj" ctorAddrs[cidx] idx (some cidx.toUInt64)
      let entries ← ingressAnonInductive ixonEnv ind selfId blockConstant
        blockId idx ctorAddrs mutCtx
      allEntries := allEntries ++ entries
  insertMutsEntries allEntries
  return memberKids

/-- Anon shallow ingress for a single address — the lazy fault path. For a
    projection, fetches the parent block and ingresses the whole block (with
    block-level dedup via `kenv.blocks`); for a standalone, ingresses
    directly. `false` when the address is absent from the env. -/
def ingressAnonAddrShallow (ixonEnv : Ixon.Env) (addr : Address)
    (verify : Bool := true) : IngressM Bool := do
  let some constant ← IngressM.liftExcept (getConstVerified ixonEnv addr verify)
    | return false
  let blockAddr? : Option Address := match constant.info with
    | .dPrj p => some p.block
    | .iPrj p => some p.block
    | .rPrj p => some p.block
    | .cPrj p => some p.block
    | .muts _ => some addr
    | _ => none
  match blockAddr? with
  | some blockAddr =>
    -- Block dedup: a prior fault on any projection of this block already
    -- populated every member.
    let blockKid : KId .anon := ⟨blockAddr, ()⟩
    if (← get).blocks.contains blockKid then
      return true
    let some blockConst ← IngressM.liftExcept
        (getConstVerified ixonEnv blockAddr verify)
      | throw s!"ingressAnonAddrShallow: block {blockAddr} (parent of {addr}) absent"
    let _ ← ingressAnonBlock ixonEnv blockConst blockAddr
    return true
  | none =>
    let _ ← ingressAnonStandalone ixonEnv addr constant
    return true

end Ix.Tc

end
end
