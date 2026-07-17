module

public import Ix.Tc.Ingress
public import Ix.Tc.CanonicalCheck

/-!
Mirror: crates/kernel/src/ingress.rs (the Ixon → kernel, meta-mode half)

Meta ingress converts the same `Ixon.Constant` structure as the anon path
(`Ix.Tc.Ingress`) but additionally threads the per-constant metadata
(`Ixon.ConstantMeta`) — binder names/infos, mdata layers, level-param
names, constant names — into the kernel types' `Mode.F` fields. Semantic
Blake3 addresses never include metadata, so every KExpr/KUniv/KConst
produced here carries the same address as its anon twin (the
`tc-meta-addr` property pins this).

Structure mirrors the anon file: explicit stack machines (Init-scale
terms overflow default runtime stacks; Rust runs its recursive converter
on 2 GB stacks). Key differences, all from `ingress.rs`:

- Frames carry `(Ixon.Expr, arenaIdx)` — the metadata arena mirrors the
  UNSHARED logical tree, so `share` expansion keeps the same arena index.
  The conversion cache keys `(shareIdx, arenaIdx)` (Lean has no stable
  pointers; a deserialized subterm is only re-entered via `share`).
- Each `process` step first walks the arena's `mdata` chain, resolving
  KVMaps against the env (`Ixon.resolveKVMap`), then reads the node.
- `var` names resolve from a de-Bruijn binder-name stack (BinderPush/Pop
  frames). `var` results are never cached (their name depends on the
  enclosing binder context).
- `ref`/`prj` arena mismatch is a HARD error (no other name source);
  `lam`/`all`/`letE` mismatch soft-falls-back to a synthetic name and the
  frozen arena index; `app` mismatch propagates the frozen index.
- A `callSite` arena node at an `app` re-flattens the canonical App
  telescope and distributes `canonMeta[i]` as per-arg arena roots; the
  head (`ref`/`recur`) is built inline from the call-site's `name`.
- Constant names, level params, `leanAll`, rule ctor names, and ctor ids
  resolve through `ConstantMetaInfo` name-hash addresses. `all`/`ctx`/
  `ctors` round-trip name-hash → Lean name → `named[name].addr` (the
  projection address a `KConst` is actually stored under) — missing Named
  entries are hard errors (ghost-KId prevention, see `resolve_all`).
- Work items come from `env.named` (one per entry: `Muts` for muts metas,
  `standalone` for non-projection constants; projections are materialized
  by their block). Aliases (same addr, different name) become separate
  KIds — meta `KId` equality includes the name.
- All-inductive Muts blocks run `validateCanonicalBlockSinglePass`
  (kernel-side canonicity gate, matching Rust `ingress_muts_block`).

The extension tables (`ConstantMeta.metaSharing`/`metaRefs`/`metaUnivs`)
are decompile-only surgery state — the kernel never reads them (parity
with Rust ingress, which ignores them entirely).
-/

public section
@[expose] section

namespace Ix.Tc

open Std (HashMap)

/-- Meta kernel environment shorthand. -/
abbrev MetaEnv := KEnv .«meta»

/-- Meta ingress monad: state-threads the meta `KEnv` being populated. -/
abbrev IngressMetaM := EStateM IngressErr MetaEnv

namespace IngressMetaM

@[inline] def internE (e : KExpr .«meta») : IngressMetaM (KExpr .«meta») :=
  fun env =>
    let (e, it) := env.intern.internExpr e
    .ok e { env with intern := it }

@[inline] def internU (u : KUniv .«meta») : IngressMetaM (KUniv .«meta») :=
  fun env =>
    let (u, it) := env.intern.internUniv u
    .ok u { env with intern := it }

@[inline] def liftExcept : Except IngressErr α → IngressMetaM α
  | .ok a => pure a
  | .error e => throw e

end IngressMetaM

/-! ### Name resolution -/

/-- Resolve a name-component address against the env's names table;
    anonymous when absent (Rust `resolve_name`). -/
def resolveName (ixonEnv : Ixon.Env) (addr : Address) : Name :=
  (ixonEnv.names[addr]?).getD Ix.Name.mkAnon

/-- Resolve level-param name addresses (Rust `resolve_level_params`). -/
def resolveLevelParams (ixonEnv : Ixon.Env) (lvlAddrs : Array Address) :
    Array Name :=
  lvlAddrs.map (resolveName ixonEnv)

/-- Resolve **name-hash** addresses to `KId .meta` whose `addr` is the
    **projection-content address** the corresponding KConst is stored
    under: name-hash → Lean name → `named[name].addr`. Hard error on a
    missing Named entry (Rust `resolve_all` — the fallback alternative
    produced ghost KIds). -/
def resolveAllMeta (ixonEnv : Ixon.Env) (addrs : Array Address) :
    Except IngressErr (Array (KId .«meta»)) :=
  addrs.mapM fun nameAddr => do
    let name := resolveName ixonEnv nameAddr
    match ixonEnv.getNamed? name with
    | some named => .ok ⟨named.addr, name⟩
    | none => .error s!"resolve_all: Named entry for '{name}' missing in \
                        ixon_env.named (expected projection or block address \
                        for the compiled constant)"

/-- The `ctx` name-hash addresses of a metadata payload (Rust
    `get_ctx_addrs`). -/
def ctxAddrsOf (cm : Ixon.ConstantMeta) : Array Address :=
  match cm.info with
  | .defn _ _ _ ctx .. => ctx
  | .indc _ _ _ _ ctx .. => ctx
  | .recr _ _ _ _ ctx .. => ctx
  | _ => #[]

/-- Mutual-recursion context from metadata `ctx` addresses (Rust
    `build_mut_ctx`). -/
def buildMutCtx (ixonEnv : Ixon.Env) (cm : Ixon.ConstantMeta) :
    Except IngressErr (Array (KId .«meta»)) :=
  resolveAllMeta ixonEnv (ctxAddrsOf cm)

/-! ### Expression conversion (explicit stack machine) -/

/-- Read-only context for converting a single Ixon constant's expressions
    in meta mode. -/
structure IngressMetaCtx where
  sharing : Array Ixon.Expr
  refs : Array Address
  univs : Array Ixon.Univ
  /-- KIds of mutual block members, for resolving `Expr.recur`. -/
  mutCtx : Array (KId .«meta»)
  /-- Metadata arena for this constant (mirrors the UNSHARED tree). -/
  arena : Ixon.ExprMetaArena
  /-- Resolved level-param names (positional). -/
  lvls : Array Name

/-- Per-constant conversion caches + the synthetic-name counter. -/
structure MetaConvState where
  /-- Converted `share` expansions, keyed by `(shareIdx, arenaIdx)`. -/
  exprCache : HashMap (UInt64 × UInt64) (KExpr .«meta») := {}
  /-- Converted universe-table roots, keyed by table index. -/
  univCache : HashMap UInt64 (KUniv .«meta») := {}
  /-- Counter for `_s{n}` synthetic binder names (Rust `synth_counter`). -/
  synthCounter : UInt64 := 0

/-- Conversion monad: per-constant caches over the env-threading ingress. -/
abbrev MetaConvM := StateT MetaConvState IngressMetaM

/-- Next synthetic name `_s{n}` (Rust `Ctx::synth_name`). -/
def synthName : MetaConvM Name := do
  let n := (← get).synthCounter
  modify fun s => { s with synthCounter := s.synthCounter + 1 }
  return Ix.Name.mkStr Ix.Name.mkAnon s!"_s{n}"

/-- Convert one universe tree (iterative), resolving `var` names from the
    level-param context. Same simplifying `mkMax`/`mkIMax` smart
    constructors as the anon path. -/
def ingressUnivTreeMeta (ctx : IngressMetaCtx) (root : Ixon.Univ) :
    IngressMetaM (KUniv .«meta») := do
  let mut stack : Array UFrame := #[.process root]
  let mut values : Array (KUniv .«meta») := #[]
  while !stack.isEmpty do
    let frame := stack.back!
    stack := stack.pop
    match frame with
    | .process u =>
      match u with
      | .zero =>
        values := values.push (← IngressMetaM.internU .mkZero)
      | .succ inner =>
        stack := stack.push .succ |>.push (.process inner)
      | .max a b =>
        stack := stack.push .max |>.push (.process b) |>.push (.process a)
      | .imax a b =>
        stack := stack.push .imax |>.push (.process b) |>.push (.process a)
      | .var idx =>
        let name := (ctx.lvls[idx.toNat]?).getD Ix.Name.mkAnon
        values := values.push (← IngressMetaM.internU (.mkParam idx name))
    | .succ =>
      let inner := values.back!
      values := values.pop
      values := values.push (← IngressMetaM.internU (.mkSucc inner))
    | .max =>
      let b := values.back!; values := values.pop
      let a := values.back!; values := values.pop
      values := values.push (← IngressMetaM.internU (.mkMax a b))
    | .imax =>
      let b := values.back!; values := values.pop
      let a := values.back!; values := values.pop
      values := values.push (← IngressMetaM.internU (.mkIMax a b))
  match values.back? with
  | some v => return v
  | none => throw "ingressUnivTreeMeta: empty result stack"

/-- Convert the universe at table index `idx`, cached per constant. -/
def ingressUnivIdxMeta (ctx : IngressMetaCtx) (idx : UInt64) :
    MetaConvM (KUniv .«meta») := do
  if let some cached := (← get).univCache[idx]? then
    return cached
  let some u := ctx.univs[idx.toNat]?
    | throw s!"invalid universe index {idx} (len {ctx.univs.size})"
  let ku ← liftM (ingressUnivTreeMeta ctx u)
  modify fun s => { s with univCache := s.univCache.insert idx ku }
  return ku

/-- Convert an array of universe-table indices. -/
def ingressUnivArgsMeta (ctx : IngressMetaCtx) (idxs : Array UInt64) :
    MetaConvM (Array (KUniv .«meta»)) := do
  let mut out : Array (KUniv .«meta») := Array.mkEmpty idxs.size
  for i in idxs do
    out := out.push (← ingressUnivIdxMeta ctx i)
  return out

/-- Meta expression frames. Binder pushes/pops maintain the de-Bruijn
    name stack for `var` resolution. -/
inductive MFrame where
  | process (e : Ixon.Expr) (arenaIdx : UInt64)
  | appDone (mdata : Array MData)
  | lamDone (name : Name) (bi : Lean.BinderInfo) (mdata : Array MData)
  | allDone (name : Name) (bi : Lean.BinderInfo) (mdata : Array MData)
  | letDone (name : Name) (nd : Bool) (mdata : Array MData)
  | prjDone (id : KId .«meta») (field : UInt64) (mdata : Array MData)
  | cacheAt (key : UInt64 × UInt64)
  | binderPush (name : Name)
  | binderPop
  deriving Inhabited

/-- Expand `share` chains, returning the expanded expression and the LAST
    share index traversed (the conversion-cache key component), if any. -/
def expandShares (ctx : IngressMetaCtx) (e : Ixon.Expr) :
    Except IngressErr (Ixon.Expr × Option UInt64) := do
  let mut cur := e
  let mut lastIdx : Option UInt64 := none
  let mut fuel := ctx.sharing.size + 1
  while true do
    match cur with
    | .share idx =>
      if fuel == 0 then throw s!"share expansion cycle at index {idx}"
      fuel := fuel - 1
      let some expansion := ctx.sharing[idx.toNat]?
        | throw s!"invalid Share index {idx}"
      lastIdx := some idx
      cur := expansion
    | _ => break
  return (cur, lastIdx)

/-- Convert one Ixon expression in meta mode (explicit stack machine).
    See the module doc for the arena-walk / cache / binder-stack rules. -/
def ingressExprMeta (ixonEnv : Ixon.Env) (ctx : IngressMetaCtx)
    (root : Ixon.Expr) (rootArena : UInt64) : MetaConvM (KExpr .«meta») := do
  let mut stack : Array MFrame := #[.process root rootArena]
  let mut values : Array (KExpr .«meta») := #[]
  let mut binderNames : Array Name := #[]
  while !stack.isEmpty do
    let frame := stack.back!
    stack := stack.pop
    match frame with
    | .process e0 arenaIdx =>
      -- Share is transparent and keeps the same arena root.
      let (e, shareIdx?) ← liftM (IngressMetaM.liftExcept (expandShares ctx e0))
      -- Cache check (share-reached, non-var nodes only; `var` names
      -- depend on the binder stack).
      let isVar := match e with | .var _ => true | _ => false
      let cacheKey? : Option (UInt64 × UInt64) :=
        if isVar then none else shareIdx?.map (fun i => (i, arenaIdx))
      if let some key := cacheKey? then
        if let some cached := (← get).exprCache[key]? then
          values := values.push cached
          continue
      -- Walk the arena's mdata chain.
      let mut currentIdx := arenaIdx
      let mut mdataLayers : Array MData := #[]
      let mut walking := true
      while walking do
        match ctx.arena.nodes[currentIdx.toNat]? with
        | some (.mdata kvmaps child) =>
          for kvm in kvmaps do
            mdataLayers := mdataLayers.push (Ixon.resolveKVMap ixonEnv kvm)
          currentIdx := child
        | _ => walking := false
      let node := (ctx.arena.nodes[currentIdx.toNat]?).getD .leaf
      -- BVar early return (never cached).
      if let .var idx := e then
        let name :=
          if binderNames.size ≥ 1 + idx.toNat then
            binderNames[binderNames.size - 1 - idx.toNat]!
          else Ix.Name.mkAnon
        values := values.push
          (← liftM (IngressMetaM.internE (.mkVar idx name (Mode.field mdataLayers))))
        continue
      if let some key := cacheKey? then
        stack := stack.push (.cacheAt key)
      let mdata := mdataLayers
      match e with
      | .share _ | .var _ => throw "unreachable: share/var handled above"
      | .sort uidx =>
        let u ← ingressUnivIdxMeta ctx uidx
        values := values.push
          (← liftM (IngressMetaM.internE (.mkSort u (Mode.field mdata))))
      | .ref refIdx univIdxs =>
        let some addr := ctx.refs[refIdx.toNat]?
          | throw s!"invalid Ref index {refIdx}"
        -- Hard error: without an arena Ref node there is no name source.
        let name ← match node with
          | .ref nameAddr => pure (resolveName ixonEnv nameAddr)
          | _ => throw s!"Ref at index {refIdx} (addr {addr}) has no \
                          metadata name (node={reprStr node})"
        let univs ← ingressUnivArgsMeta ctx univIdxs
        values := values.push (← liftM (IngressMetaM.internE
          (.mkConst ⟨addr, name⟩ univs (Mode.field mdata))))
      | .recur recIdx univIdxs =>
        let some mid := ctx.mutCtx[recIdx.toNat]?
          | throw s!"invalid Rec index {recIdx}"
        let univs ← ingressUnivArgsMeta ctx univIdxs
        values := values.push (← liftM (IngressMetaM.internE
          (.mkConst mid univs (Mode.field mdata))))
      | .nat blobIdx =>
        let some blobAddr := ctx.refs[blobIdx.toNat]?
          | throw s!"invalid Nat blob ref index {blobIdx}"
        let some bytes := ixonEnv.getBlob? blobAddr
          | throw s!"missing Nat blob {blobAddr}"
        let val := Nat.fromBytesLE bytes.data
        values := values.push (← liftM (IngressMetaM.internE
          (.mkNat val blobAddr (Mode.field mdata))))
      | .str blobIdx =>
        let some blobAddr := ctx.refs[blobIdx.toNat]?
          | throw s!"invalid Str blob ref index {blobIdx}"
        let some bytes := ixonEnv.getBlob? blobAddr
          | throw s!"missing Str blob {blobAddr}"
        let some val := String.fromUTF8? bytes
          | throw s!"Str blob {blobAddr} is not valid UTF-8"
        values := values.push (← liftM (IngressMetaM.internE
          (.mkStr val blobAddr (Mode.field mdata))))
      | .app f a =>
        match node with
        | .callSite csName entries canonMeta origHead =>
          -- Surgered call site: re-flatten the canonical App telescope
          -- and distribute canonMeta[i] as per-arg arena roots. The
          -- source-order `entries` and `origHead` are decompile-only.
          let _ := entries
          let _ := origHead
          let mut canonicalArgs : Array Ixon.Expr := #[]
          let mut cur := e
          let mut looping := true
          while looping do
            match cur with
            | .app f2 a2 =>
              canonicalArgs := canonicalArgs.push a2
              let (f2', _) ←
                liftM (IngressMetaM.liftExcept (expandShares ctx f2))
              cur := f2'
            | _ => looping := false
          canonicalArgs := canonicalArgs.reverse
          let headIxon := cur
          let nArgs := canonicalArgs.size
          if canonMeta.size != nArgs then
            let headName := resolveName ixonEnv csName
            throw s!"CallSite for '{headName}' has {canonMeta.size} \
                     canonical metadata entries but canonical telescope \
                     has {nArgs} args"
          -- Build the head KExpr inline from the call-site name.
          let headK : KExpr .«meta» ← match headIxon with
            | .ref refIdx univIdxs => do
              let some addr := ctx.refs[refIdx.toNat]?
                | throw s!"CallSite head: invalid Ref index {refIdx}"
              let name := resolveName ixonEnv csName
              let univs ← ingressUnivArgsMeta ctx univIdxs
              liftM (IngressMetaM.internE
                (.mkConst ⟨addr, name⟩ univs (Mode.field #[])))
            | .recur recIdx univIdxs => do
              let some mid := ctx.mutCtx[recIdx.toNat]?
                | throw s!"CallSite head: invalid Rec index {recIdx}"
              let univs ← ingressUnivArgsMeta ctx univIdxs
              liftM (IngressMetaM.internE
                (.mkConst mid univs (Mode.field #[])))
            | _ =>
              throw s!"CallSite head is not Ref/Rec: {reprStr headIxon}"
          if nArgs == 0 then
            values := values.push headK
          else
            -- LIFO: outermost AppDone carries the mdata; inner AppDones
            -- are bare (the Ixon Mdata wrapper sits outside the spine).
            stack := stack.push (.appDone mdata)
            stack := stack.push
              (.process canonicalArgs[nArgs - 1]! canonMeta[nArgs - 1]!)
            for i in [0:nArgs - 1] do
              let j := nArgs - 2 - i
              stack := stack.push (.appDone #[])
              stack := stack.push (.process canonicalArgs[j]! canonMeta[j]!)
            values := values.push headK
        | .app fArena aArena =>
          stack := stack.push (.appDone mdata)
            |>.push (.process a aArena) |>.push (.process f fArena)
        | _ =>
          stack := stack.push (.appDone mdata)
            |>.push (.process a currentIdx) |>.push (.process f currentIdx)
      | .lam ty body =>
        let (name, bi, tyArena, bodyArena) ← match node with
          | .binder nameAddr info tyChild bodyChild =>
            pure (resolveName ixonEnv nameAddr, info, tyChild, bodyChild)
          | _ => do
            let n ← synthName
            pure (n, Lean.BinderInfo.default, currentIdx, currentIdx)
        stack := stack.push (.lamDone name bi mdata)
          |>.push .binderPop
          |>.push (.process body bodyArena)
          |>.push (.binderPush name)
          |>.push (.process ty tyArena)
      | .all ty body =>
        let (name, bi, tyArena, bodyArena) ← match node with
          | .binder nameAddr info tyChild bodyChild =>
            pure (resolveName ixonEnv nameAddr, info, tyChild, bodyChild)
          | _ => do
            let n ← synthName
            pure (n, Lean.BinderInfo.default, currentIdx, currentIdx)
        stack := stack.push (.allDone name bi mdata)
          |>.push .binderPop
          |>.push (.process body bodyArena)
          |>.push (.binderPush name)
          |>.push (.process ty tyArena)
      | .letE nd ty val body =>
        let (name, tyArena, valArena, bodyArena) ← match node with
          | .letBinder nameAddr tyChild valChild bodyChild =>
            pure (resolveName ixonEnv nameAddr, tyChild, valChild, bodyChild)
          | _ => do
            let n ← synthName
            pure (n, currentIdx, currentIdx, currentIdx)
        stack := stack.push (.letDone name nd mdata)
          |>.push .binderPop
          |>.push (.process body bodyArena)
          |>.push (.binderPush name)
          |>.push (.process val valArena)
          |>.push (.process ty tyArena)
      | .prj typeRefIdx field val =>
        let some typeAddr := ctx.refs[typeRefIdx.toNat]?
          | throw s!"invalid Prj type ref index {typeRefIdx}"
        -- Hard error: the arena holds both the struct name and the child
        -- arena pointer.
        let (structName, childArena) ← match node with
          | .prj nameAddr child =>
            pure (resolveName ixonEnv nameAddr, child)
          | _ => throw s!"Prj at ref index {typeRefIdx} (addr {typeAddr}) \
                          has no metadata name (node={reprStr node})"
        stack := stack.push (.prjDone ⟨typeAddr, structName⟩ field mdata)
          |>.push (.process val childArena)
    | .appDone mdata =>
      let a := values.back!; values := values.pop
      let f := values.back!; values := values.pop
      values := values.push (← liftM (IngressMetaM.internE
        (.mkApp f a (Mode.field mdata))))
    | .lamDone name bi mdata =>
      let body := values.back!; values := values.pop
      let ty := values.back!; values := values.pop
      values := values.push (← liftM (IngressMetaM.internE
        (.mkLam name bi ty body (Mode.field mdata))))
    | .allDone name bi mdata =>
      let body := values.back!; values := values.pop
      let ty := values.back!; values := values.pop
      values := values.push (← liftM (IngressMetaM.internE
        (.mkAll name bi ty body (Mode.field mdata))))
    | .letDone name nd mdata =>
      let body := values.back!; values := values.pop
      let val := values.back!; values := values.pop
      let ty := values.back!; values := values.pop
      values := values.push (← liftM (IngressMetaM.internE
        (.mkLet name ty val body nd (Mode.field mdata))))
    | .prjDone id field mdata =>
      let val := values.back!; values := values.pop
      values := values.push (← liftM (IngressMetaM.internE
        (.mkPrj id field val (Mode.field mdata))))
    | .cacheAt key =>
      let v := values.back!
      modify fun s => { s with exprCache := s.exprCache.insert key v }
    | .binderPush name =>
      binderNames := binderNames.push name
    | .binderPop =>
      binderNames := binderNames.pop
  match values.back? with
  | some v =>
    if values.size != 1 then
      throw s!"ingressExprMeta: unbalanced value stack ({values.size} values)"
    return v
  | none => throw "ingressExprMeta: empty result stack"

/-! ### Constant conversion (meta) -/

/-- One converted meta `(KId, KConst)` entry. -/
abbrev MetaEntry := KId .«meta» × KConst .«meta»

/-- Reserved-marker guard (same rule as the anon path). -/
def guardReservedMeta (entries : Array MetaEntry) : IngressMetaM Unit := do
  for (id, _) in entries do
    if let some marker := reservedMarkerName id.addr then
      throw s!"attempted to insert constant at reserved kernel marker \
               address {marker} ({id.addr})"

/-- Standalone registration: each entry is its own single-member block. -/
def insertStandaloneEntriesMeta (entries : Array MetaEntry) :
    IngressMetaM Unit := do
  guardReservedMeta entries
  modifyGet fun env => ((), entries.foldl (init := env) fun env (id, c) =>
    (env.insert id c).insertBlock id #[id])

/-- Muts registration (block id from the first entry's `block` field). -/
def insertMutsEntriesMeta (entries : Array MetaEntry) : IngressMetaM Unit := do
  guardReservedMeta entries
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

/-- The empty-arena fallback metadata destructure (Rust `DEFAULT_ARENA`
    arms): unknown metadata kinds degrade to no names, empty arena. -/
def emptyArena : Ixon.ExprMetaArena := {}

/-- Convert a `Definition` with metadata (Rust `ingress_defn`, meta half). -/
def ingressDefnMeta (ixonEnv : Ixon.Env) (defn : Ixon.Definition)
    (selfId : KId .«meta») (cm : Ixon.ConstantMeta)
    (sharing : Array Ixon.Expr) (refs : Array Address)
    (univs : Array Ixon.Univ) (block : KId .«meta»)
    (mutCtxOverride : Option (Array (KId .«meta») ) := none) :
    IngressMetaM (Array MetaEntry) := do
  let hints := (ixonEnv.anonHints[selfId.addr]?).getD (.regular 0)
  let (levelParams, arena, typeRoot, valueRoot, allAddrs) := match cm.info with
    | .defn _ lvls all _ arena typeRoot valueRoot =>
      (resolveLevelParams ixonEnv lvls, arena, typeRoot, valueRoot, all)
    | _ => (#[], emptyArena, 0, 0, #[])
  let mutCtx ← match mutCtxOverride with
    | some m => pure m
    | none => IngressMetaM.liftExcept (buildMutCtx ixonEnv cm)
  let ctx : IngressMetaCtx :=
    { sharing, refs, univs, mutCtx, arena, lvls := levelParams }
  let (ty, st) ← (ingressExprMeta ixonEnv ctx defn.typ typeRoot).run {}
  let (val, _) ← (ingressExprMeta ixonEnv ctx defn.value valueRoot).run st
  let leanAll ← IngressMetaM.liftExcept (resolveAllMeta ixonEnv allAddrs)
  let name := match cm.info with
    | .defn nameAddr .. => resolveName ixonEnv nameAddr
    | _ => resolveName ixonEnv selfId.addr
  return #[(selfId,
    .defn name levelParams defn.kind defn.safety hints defn.lvls ty val
      leanAll block)]

/-- Convert a `Recursor` with metadata (Rust `ingress_recursor`, meta
    half). `memberIdx` stays 0 (Rust parity: caller-filled for muts). -/
def ingressRecursorMeta (ixonEnv : Ixon.Env) (rec : Ixon.Recursor)
    (selfId : KId .«meta») (cm : Ixon.ConstantMeta)
    (sharing : Array Ixon.Expr) (refs : Array Address)
    (univs : Array Ixon.Univ) (block : KId .«meta»)
    (mutCtxOverride : Option (Array (KId .«meta»)) := none) :
    IngressMetaM (Array MetaEntry) := do
  let (levelParams, arena, typeRoot, ruleRoots, ruleCtorAddrs, allAddrs) :=
    match cm.info with
    | .recr _ lvls rules all _ arena typeRoot ruleRoots =>
      (resolveLevelParams ixonEnv lvls, arena, typeRoot, ruleRoots, rules, all)
    | _ => (#[], emptyArena, 0, #[], #[], #[])
  let mutCtx ← match mutCtxOverride with
    | some m => pure m
    | none => IngressMetaM.liftExcept (buildMutCtx ixonEnv cm)
  let ctx : IngressMetaCtx :=
    { sharing, refs, univs, mutCtx, arena, lvls := levelParams }
  let (ty, st) ← (ingressExprMeta ixonEnv ctx rec.typ typeRoot).run {}
  let mut st := st
  let mut rules : Array (RecRule .«meta») := Array.mkEmpty rec.rules.size
  for h : i in [0:rec.rules.size] do
    let rule := rec.rules[i]
    -- Empty `ruleRoots` (no meta) degrades to root 0 over the empty
    -- arena, where every index misses to `.leaf`.
    let rhsRoot := (ruleRoots[i]?).getD 0
    let (rhs, st') ← (ingressExprMeta ixonEnv ctx rule.rhs rhsRoot).run st
    st := st'
    let ctorName := match ruleCtorAddrs[i]? with
      | some a => resolveName ixonEnv a
      | none => Ix.Name.mkAnon
    rules := rules.push { ctor := ctorName, fields := rule.fields, rhs }
  let leanAll ← IngressMetaM.liftExcept (resolveAllMeta ixonEnv allAddrs)
  let name := match cm.info with
    | .recr nameAddr .. => resolveName ixonEnv nameAddr
    | _ => resolveName ixonEnv selfId.addr
  return #[(selfId,
    .recr name levelParams rec.k rec.isUnsafe rec.lvls rec.params rec.indices
      rec.motives rec.minors block 0 ty rules leanAll)]

/-- Meta ingress for a single standalone (non-mutual) constant. Returns
    `#[]` for projections/Muts (handled by the block path — Rust parity). -/
def ingressMetaStandalone (ixonEnv : Ixon.Env) (constName : Name)
    (addr : Address) (constant : Ixon.Constant) (cm : Ixon.ConstantMeta) :
    IngressMetaM (Array MetaEntry) := do
  let selfId : KId .«meta» := ⟨addr, constName⟩
  match constant.info with
  | .defn d =>
    ingressDefnMeta ixonEnv d selfId cm constant.sharing constant.refs
      constant.univs selfId
  | .recr r =>
    ingressRecursorMeta ixonEnv r selfId cm constant.sharing constant.refs
      constant.univs selfId
  | .axio a => do
    let (levelParams, arena, typeRoot) := match cm.info with
      | .axio _ lvls arena typeRoot =>
        (resolveLevelParams ixonEnv lvls, arena, typeRoot)
      | _ => (#[], emptyArena, 0)
    let ctx : IngressMetaCtx :=
      { sharing := constant.sharing, refs := constant.refs
        univs := constant.univs, mutCtx := #[], arena, lvls := levelParams }
    let (ty, _) ← (ingressExprMeta ixonEnv ctx a.typ typeRoot).run {}
    let name := match cm.info with
      | .axio nameAddr .. => resolveName ixonEnv nameAddr
      | _ => resolveName ixonEnv addr
    pure #[(selfId, .axio name levelParams a.isUnsafe a.lvls ty)]
  | .quot q => do
    let (levelParams, arena, typeRoot) := match cm.info with
      | .quot _ lvls arena typeRoot =>
        (resolveLevelParams ixonEnv lvls, arena, typeRoot)
      | _ => (#[], emptyArena, 0)
    let ctx : IngressMetaCtx :=
      { sharing := constant.sharing, refs := constant.refs
        univs := constant.univs, mutCtx := #[], arena, lvls := levelParams }
    let (ty, _) ← (ingressExprMeta ixonEnv ctx q.typ typeRoot).run {}
    let name := match cm.info with
      | .quot nameAddr .. => resolveName ixonEnv nameAddr
      | _ => resolveName ixonEnv addr
    pure #[(selfId, .quot name levelParams q.kind q.lvls ty)]
  | .iPrj _ | .cPrj _ | .rPrj _ | .dPrj _ | .muts _ => pure #[]

/-- Convert an `Inductive` block member plus all of its constructors
    (Rust `ingress_muts_inductive`). Ctor ids and per-ctor metadata come
    from the ctor Named entries (hard errors when missing). -/
def ingressMutsInductiveMeta (ixonEnv : Ixon.Env) (ind : Ixon.Inductive)
    (selfId : KId .«meta») (cm : Ixon.ConstantMeta)
    (blockConstant : Ixon.Constant) (blockId : KId .«meta»)
    (memberIdx : UInt64) : IngressMetaM (Array MetaEntry) := do
  let (levelParams, arena, typeRoot, allAddrs, ctorAddrs) := match cm.info with
    | .indc _ lvls ctors all _ arena typeRoot =>
      (resolveLevelParams ixonEnv lvls, arena, typeRoot, all, ctors)
    | _ => (#[], emptyArena, 0, #[], #[])
  let mutCtx ← IngressMetaM.liftExcept (buildMutCtx ixonEnv cm)
  let ctx : IngressMetaCtx :=
    { sharing := blockConstant.sharing, refs := blockConstant.refs
      univs := blockConstant.univs, mutCtx, arena, lvls := levelParams }
  let (ty, _) ← (ingressExprMeta ixonEnv ctx ind.typ typeRoot).run {}
  let leanAll ← IngressMetaM.liftExcept (resolveAllMeta ixonEnv allAddrs)
  let ctorIds ← IngressMetaM.liftExcept (resolveAllMeta ixonEnv ctorAddrs)
  let name := match cm.info with
    | .indc nameAddr .. => resolveName ixonEnv nameAddr
    | _ => resolveName ixonEnv selfId.addr
  let mut results : Array MetaEntry := #[(selfId,
    .indc name levelParams ind.lvls ind.params ind.indices ind.isUnsafe
      blockId memberIdx ty ctorIds leanAll)]
  for h : cidx in [0:ind.ctors.size] do
    let ctor := ind.ctors[cidx]
    let some ctorId := ctorIds[cidx]?
      | throw s!"missing ctor_id for constructor index {cidx}"
    let some ctorNameAddr := ctorAddrs[cidx]?
      | throw s!"missing ctor_addrs entry for constructor index {cidx}"
    let ctorName := resolveName ixonEnv ctorNameAddr
    -- Per-ctor metadata from its own Named entry (hard error: the parent
    -- inductive's meta doesn't carry ctor expression metadata inline).
    let some ctorNamed := ixonEnv.getNamed? ctorName
      | throw s!"missing Named entry for ctor '{ctorName}' (cidx={cidx}) — \
                 per-ctor metadata (arena, type_root, lvls) must be \
                 registered for every constructor of this inductive block"
    let (ctorLvlParams, ctorArena, ctorTypeRoot) ←
      match ctorNamed.constMeta.info with
      | .ctor _ lvls _ arena typeRoot =>
        pure (resolveLevelParams ixonEnv lvls, arena, typeRoot)
      | other =>
        throw s!"ctor '{ctorName}' has unexpected meta kind \
                 '{other.kindName}' (expected Ctor)"
    let ctorCtx : IngressMetaCtx :=
      { sharing := blockConstant.sharing, refs := blockConstant.refs
        univs := blockConstant.univs, mutCtx, arena := ctorArena
        lvls := ctorLvlParams }
    -- Fresh caches per ctor: the arena (hence cache-key space) changes.
    let (ctorTy, _) ←
      (ingressExprMeta ixonEnv ctorCtx ctor.typ ctorTypeRoot).run {}
    results := results.push (ctorId,
      .ctor ctorName ctorLvlParams ctor.isUnsafe ctor.lvls selfId ctor.cidx
        ctor.params ctor.fields ctorTy)
  return results

/-- Meta ingress for an entire Muts block from its Muts Named entry (Rust
    `ingress_muts_block`): member self-KIds come from each member's
    canonical Named entry (`all[i][0]` name-hash → name → projection
    address); all-inductive blocks additionally pass the kernel-side
    canonicity gate. -/
def ingressMetaMutsBlock (ixonEnv : Ixon.Env) (entryName : Name)
    (entryAddr : Address) (all : Array (Array Address))
    (verify : Bool := true) : IngressMetaM (Array MetaEntry) := do
  let blockId : KId .«meta» := ⟨entryAddr, entryName⟩
  let some blockConstant ← IngressMetaM.liftExcept
      (getConstVerified ixonEnv entryAddr verify)
    | throw s!"missing Muts block constant {entryAddr}"
  let .muts members := blockConstant.info
    | throw s!"constant at {entryAddr} is not Muts"
  let mut results : Array MetaEntry := #[]
  for h : i in [0:members.size] do
    let member := members[i]
    let some primaryNameAddr := (all[i]?).bind (·[0]?)
      | throw s!"Muts block member {i} has no name in all"
    let memberName := resolveName ixonEnv primaryNameAddr
    let some memberNamed := ixonEnv.getNamed? memberName
      | throw s!"Muts member '{memberName}' not found in named entries"
    let selfId : KId .«meta» := ⟨memberNamed.addr, memberName⟩
    match member with
    | .indc ind =>
      results := results ++ (← ingressMutsInductiveMeta ixonEnv ind selfId
        memberNamed.constMeta blockConstant blockId i.toUInt64)
    | .recr rec =>
      results := results ++ (← ingressRecursorMeta ixonEnv rec selfId
        memberNamed.constMeta blockConstant.sharing blockConstant.refs
        blockConstant.univs blockId)
    | .defn d =>
      results := results ++ (← ingressDefnMeta ixonEnv d selfId
        memberNamed.constMeta blockConstant.sharing blockConstant.refs
        blockConstant.univs blockId)
  -- Canonicity gate for all-inductive blocks (Rust parity).
  let allIndc := members.all fun m => match m with
    | .indc _ => true | _ => false
  if allIndc && !members.isEmpty then
    let indcs := results.filter fun (_, c) => match c with
      | .indc .. => true | _ => false
    let resolveCtor : ResolveCtor .«meta» := fun cid =>
      (results.find? fun (rid, _) => rid == cid).map (·.2)
    match validateCanonicalBlockSinglePass entryAddr resolveCtor indcs with
    | .ok () => pure ()
    | .error e => throw s!"{entryName}: {e}"
  return results

/-! ### Work enumeration -/

/-- One meta work item (Rust `IngressWorkItem`): a Named-entry name. -/
inductive MetaWorkItem where
  | standalone (name : Name)
  | muts (name : Name)
  deriving Inhabited, BEq, Repr

namespace MetaWorkItem

def name : MetaWorkItem → Name
  | .standalone n => n
  | .muts n => n

end MetaWorkItem

/-- Partition `env.named` into meta work items (Rust `ixon_ingress_inner`
    work loop): `muts` for Muts metas; `standalone` for entries whose
    constant is not a projection (projections are materialized by their
    block; entries with missing constants are skipped). Sorted by name for
    deterministic order (Rust iterates a DashMap; items are independent). -/
def buildMetaWork (ixonEnv : Ixon.Env) : Array MetaWorkItem := Id.run do
  let mut items : Array (Name × MetaWorkItem) := #[]
  for (name, named) in ixonEnv.named do
    match named.constMeta.info with
    | .muts .. => items := items.push (name, .muts name)
    | .indc .. | .ctor .. | .recr .. | .defn .. =>
      match ixonEnv.consts[named.addr]? with
      | none => pure ()
      | some lc =>
        match lc.peekTag with
        | .ok tag =>
          match tag with
          | .iPrj | .cPrj | .rPrj | .dPrj => pure ()
          | _ => items := items.push (name, .standalone name)
        | .error _ => items := items.push (name, .standalone name)
    | _ => items := items.push (name, .standalone name)
  let sorted := items.qsort fun a b =>
    (a.1.getHash.cmpBytes b.1.getHash).isLT
  return sorted.map (·.2)

/-- Ingress one meta work item into the kernel env. Missing constants are
    skipped silently (Rust parity: `continue` on missing const). -/
def ingressMetaWorkItem (ixonEnv : Ixon.Env) (item : MetaWorkItem)
    (verify : Bool := true) : IngressMetaM Unit := do
  match item with
  | .standalone name =>
    let some named := ixonEnv.getNamed? name
      | throw s!"{name}: missing Named entry"
    let some constant ← IngressMetaM.liftExcept
        (getConstVerified ixonEnv named.addr verify)
      | return ()
    let entries ←
      try
        ingressMetaStandalone ixonEnv name named.addr constant named.constMeta
      catch e => throw s!"{name}: {e}"
    insertStandaloneEntriesMeta entries
  | .muts name =>
    let some named := ixonEnv.getNamed? name
      | throw s!"{name}: missing Named entry"
    let .muts all _ := named.constMeta.info
      | return ()
    let entries ←
      try
        ingressMetaMutsBlock ixonEnv name named.addr all verify
      catch e => throw s!"{name}: {e}"
    insertMutsEntriesMeta entries

end Ix.Tc

end
end
