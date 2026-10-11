/-
  `ix pack` against its Lean oracle (owner, 2026-10-07; M6R slice 6).

  A bundle is the root's transitive reference closure, including the
  compiler-introduced constants it references, never its compilation unit
  (`Ix.Cli.PackCmd`). `ix pack` computes it in Rust by address
  (`Ixon.rsPackEnv`: `Env::prune_to_closure`, or `prune_to_closure_anon`).
  `packOracle` is Lean's implementation of the same closure over the same
  source, written from the Rust definition's three edges and metadata
  fixpoint (`crates/ixon/src/env.rs`: `closure_edges`, `prune_value_pass`,
  `carry_named_entry`, `enqueue_named_refs`, `carry_name`;
  `crates/ixon/src/metadata.rs`: `collect_deps`, `named_refs`):

  - the value closure from `main`: a constant's `refs`, a projection's block,
    a block's member and constructor projections; a reached blob is carried,
    a reached declared cut point is recorded in `assumptions` and not
    followed (an unreached one is skipped), anything else reached is an
    error; per-constant hints travel with their constants;
  - unless anonymous, to a fixpoint: every `Named` entry whose constant is
    carried, its name and every name and blob its metadata references
    (each name with its parent chain and string-component blobs), its
    `metaRefs` and its stored `original` as further roots, and the
    constants of the names meta ingress resolves (`all`, `ctx`, `ctors`).

  `run` compares, for each root, Rust's bundle file with `Ixon.serEnv` of the
  oracle's bundle, byte for byte, with metadata, and the first root also
  anonymously. A difference, or a failure on one side only, is a defect.

  Until M6R slice 6 this module compared Rust's whole-unit pack (slice 5's
  `rsPackEnvUnits`) with Lean's (`packWholeUnits`, M1-h); both, and the unit
  view of a compiled environment they read, were removed when the owner
  decided that a bundle never carries the compilation unit.
-/
import Ix.Cli.PackCmd
import Ix.Tc.Ingress

namespace Tests.Ix.Compile.PackParity

open Ix.Cli.PackCmd (ixToLeanName readIxe)

def say (s : String) : IO Unit := do
  IO.println s!"[pack-parity] {s}"
  (← IO.getStdout).flush

/-- Does `n` have a Pass 3 reserved component? -/
def hasReserved (n : Lean.Name) : Bool :=
  n.components.any fun c => match c with
    | .str .anonymous s => Lean.unitReservedComponent s
    | _ => false

/-! ## The oracle -/

/-- A constant's closure edges (`Env::closure_edges`): its `refs`, a
    projection's block, and a block's member and constructor projections. -/
def closureEdges (addr : Address) (c : Ixon.Constant) : Array Address := Id.run do
  let mut out := c.refs
  match c.info with
  | .iPrj p => out := out.push p.block
  | .cPrj p => out := out.push p.block
  | .rPrj p => out := out.push p.block
  | .dPrj p => out := out.push p.block
  | .muts ms =>
    for i in [0:ms.size] do
      let iu := i.toUInt64
      match ms[i]! with
      | .defn _ => out := out.push (Ix.Tc.defnProjAddr addr iu)
      | .recr _ => out := out.push (Ix.Tc.recrProjAddr addr iu)
      | .indc ind =>
        out := out.push (Ix.Tc.indcProjAddr addr iu)
        for j in [0:ind.ctors.size] do
          out := out.push (Ix.Tc.ctorProjAddr addr iu j.toUInt64)
  | _ => pure ()
  return out

/-- The names, blobs and constant edges a constant's metadata references
    (`ConstantMeta::collect_deps`). -/
def metaDeps (cm : Ixon.ConstantMeta) : Array Address × Array Address × Array Address := Id.run do
  let mut names : Array Address := #[]
  let mut blobs : Array Address := #[]
  let mut arena? : Option Ixon.ExprMetaArena := none
  match cm.info with
  | .empty => pure ()
  | .defn name lvls all ctx arena _ _ =>
    names := #[name] ++ lvls ++ all ++ ctx
    arena? := some arena
  | .axio name lvls arena _ | .quot name lvls arena _ =>
    names := #[name] ++ lvls
    arena? := some arena
  | .indc name lvls ctors all ctx arena _ =>
    names := #[name] ++ lvls ++ ctors ++ all ++ ctx
    arena? := some arena
  | .ctor name lvls induct arena _ =>
    names := #[name] ++ lvls ++ #[induct]
    arena? := some arena
  | .recr name lvls rules all ctx arena _ _ =>
    names := #[name] ++ lvls ++ rules ++ all ++ ctx
    arena? := some arena
  | .muts all _ => for cls in all do names := names ++ cls
  if let some a := arena? then
    for node in a.nodes do
      match node with
      | .leaf | .app .. => pure ()
      | .binder n .. | .letBinder n .. | .ref n | .callSite n .. | .etaCallSite _ n .. =>
        names := names.push n
      | .prj s _ => names := names.push s
      | .mdata kvs _ =>
        for kv in kvs do
          for (k, v) in kv do
            names := names.push k
            match v with
            | .ofName x => names := names.push x
            | .ofString x | .ofNat x | .ofInt x | .ofSyntax x => blobs := blobs.push x
            | .ofBool _ => pure ()
  return (names, blobs, cm.metaRefs)

/-- The names meta ingress resolves to constants through `named`
    (`ConstantMeta::named_refs`). -/
def namedRefs (cm : Ixon.ConstantMeta) : Array Address :=
  match cm.info with
  | .defn _ _ all ctx .. | .recr _ _ _ all ctx .. => all ++ ctx
  | .indc _ _ ctors all ctx .. => ctors ++ all ++ ctx
  | _ => #[]

/-- The number of components of `n` (a bound for walking its parent chain). -/
def depth : Ix.Name → Nat
  | .anonymous _ => 0
  | .str p _ _ => depth p + 1
  | .num p _ _ => depth p + 1

/-- `n` and its parent chain into `out.names`, each string component's bytes
    as a blob (`Env::carry_name`). -/
def carryName (out : Ixon.Env) (n : Ix.Name) : Ixon.Env := Id.run do
  let mut out := out
  let mut cur := n
  for _ in [0:depth n + 1] do
    let a := cur.getHash
    if out.names.contains a then return out
    out := { out with names := out.names.insert a cur }
    match cur with
    | .anonymous _ => return out
    | .str p s _ =>
      out := (out.storeBlob s.toUTF8).1
      cur := p
    | .num p _ _ => cur := p
  return out

/-- The bundle of `main` in `src`, cut at `assumed`: the reference closure,
    with display metadata unless `anon` (Lean's implementation of
    `Env::prune_to_closure` / `prune_to_closure_anon`, the oracle of
    `ix pack`). -/
def packOracle (src : Ixon.Env) (main : Address) (assumed : Std.HashSet Address)
    (anon : Bool) : Except String Ixon.Env := do
  if assumed.contains main then throw "prune_to_closure: main cannot be assumed"
  let named := src.named.toArray
  let mut out : Ixon.Env := { main := some main }
  let mut visited : Std.HashSet Address := ({} : Std.HashSet Address).insert main
  let mut pending : Array Address := #[main]
  let mut done : Std.HashSet Ix.Name := {}
  -- every address is queued at most once (`visited`), and every round but the
  -- last queues one, so these bounds are never reached
  let bound := src.consts.size + src.blobs.size + assumed.size + 2
  for _ in [0:bound] do
    -- the value pass
    for _ in [0:bound] do
      let some a := pending.back? | break
      pending := pending.pop
      if assumed.contains a then
        out := { out with assumptions := out.assumptions.insert a }
        continue
      match src.consts.get? a with
      | some lc =>
        out := { out with consts := out.consts.insert a lc }
        if let some h := src.anonHints.get? a then
          out := { out with anonHints := out.anonHints.insert a h }
        let c ← match lc.get with
          | .ok c => pure c
          | .error e => throw s!"prune_to_closure: constant {a} unparseable: {e}"
        for e in closureEdges a c do
          unless visited.contains e do
            visited := visited.insert e
            pending := pending.push e
      | none => match src.blobs.get? a with
        | some b => out := { out with blobs := out.blobs.insert a b }
        | none => throw s!"prune_to_closure: {a} reachable from main but not in consts/blobs \
            and not assumed"
    unless pending.isEmpty do throw "packOracle: the value pass did not finish"
    if anon then return out
    -- the named pass
    let mut refNames : Array Ix.Name := #[]
    for (name, nd) in named do
      unless out.consts.contains nd.addr do continue
      if done.contains name then continue
      done := done.insert name
      out := carryName { out with named := out.named.insert name nd } name
      for na in namedRefs nd.constMeta do
        if let some n := src.names.get? na then refNames := refNames.push n
      let (ns, bs, dag) := metaDeps nd.constMeta
      let mut ns := ns
      let mut bs := bs
      let mut dag := dag
      if let some (oa, om) := nd.original then
        if assumed.contains oa || src.consts.contains oa || src.blobs.contains oa then
          dag := dag.push oa
        let (ns', bs', dag') := metaDeps om
        ns := ns ++ ns'
        bs := bs ++ bs'
        dag := dag ++ dag'
      for na in ns do
        match src.names.get? na with
        | some n => out := carryName out n
        | none => throw s!"prune_to_closure: metadata references name {na} absent from names"
      for ba in bs do
        match src.blobs.get? ba with
        | some b => out := { out with blobs := out.blobs.insert ba b }
        | none => throw s!"prune_to_closure: metadata references blob {ba} absent from blobs"
      for da in dag do
        unless visited.contains da do
          visited := visited.insert da
          pending := pending.push da
    for n in refNames do
      if let some nd := src.named.get? n then
        unless visited.contains nd.addr do
          visited := visited.insert nd.addr
          pending := pending.push nd.addr
    if pending.isEmpty then return out
  throw "packOracle: no fixpoint"

/-! ## The comparison -/

/-- How many elements of `a` are not in `b`. -/
def countOnly {α : Type} [BEq α] [Hashable α] (a b : Array α) : Nat :=
  let s : Std.HashSet α := b.foldl (·.insert ·) {}
  (a.filter (!s.contains ·)).size

/-- The keys of an address-keyed map. -/
def keys {β : Type} (m : Std.HashMap Address β) : Array Address := m.toArray.map (·.1)

/-- What two bundles differ by (constants, Named entries, names, blobs). -/
def describe (lean rust : Ixon.Env) : String :=
  let ln := lean.named.toArray.map (·.1)
  let rn := rust.named.toArray.map (·.1)
  s!"constants Lean-only {countOnly (keys lean.consts) (keys rust.consts)} / Rust-only \
    {countOnly (keys rust.consts) (keys lean.consts)}; Named Lean-only {countOnly ln rn} / \
    Rust-only {countOnly rn ln}; names Lean-only {countOnly (keys lean.names) (keys rust.names)} / \
    Rust-only {countOnly (keys rust.names) (keys lean.names)}; blobs Lean-only \
    {countOnly (keys lean.blobs) (keys rust.blobs)} / Rust-only \
    {countOnly (keys rust.blobs) (keys lean.blobs)}; main {lean.main == rust.main}; \
    assumptions {lean.assumptions.size} / {rust.assumptions.size}"

/-- The shape of a reserved name: its first reserved component with the
    component after it, digits dropped (`x._ix.rec_2` ↦ `_ix.rec_`), or the
    reserved component alone when it is last (`c._ix` ↦ `_ix`). -/
def shapeOf (n : Lean.Name) : String := Id.run do
  let cs : Array String := n.components.toArray.map fun c => match c with
    | .str .anonymous s => s
    | .num .anonymous i => toString i
    | _ => ""
  let some i := cs.findIdx? Lean.unitReservedComponent | return ""
  let strip (s : String) := String.ofList (s.toList.reverse.dropWhile Char.isDigit).reverse
  match cs[i + 1]? with
  | some nxt => return s!"{cs[i]!}.{strip nxt}"
  | none => return cs[i]!

/-- The roots compared on `src`: `extra` (always), then, up to `max` roots in
    all, one name with a Pass 3 reserved component per shape (the least by
    its string), then the remaining reserved names in string order. If those
    do not fill the budget, ordinary names fill it: a unit without introduced
    constants still exercises the pack oracle. -/
def defaultRoots (src : Ixon.Env) (extra : Array Lean.Name) (max : Nat) : Array Lean.Name :=
  Id.run do
  let reserved := ((src.named.toArray.map (ixToLeanName ·.1)).filter hasReserved).qsort
    (·.toString < ·.toString)
  let mut out := extra
  let mut shapes : Std.HashSet String := {}
  for n in reserved do
    if out.size ≥ max then break
    let sh := shapeOf n
    if shapes.contains sh || out.contains n then continue
    shapes := shapes.insert sh
    out := out.push n
  for n in reserved do
    if out.size ≥ max then break
    unless out.contains n do out := out.push n
  let ordinary := ((src.named.toArray.map (ixToLeanName ·.1)).filter (!hasReserved ·)).qsort
    (·.toString < ·.toString)
  for n in ordinary do
    if out.size ≥ max then break
    unless out.contains n do out := out.push n
  return out

/-- Pack each root of `roots` from the env at `srcPath` with `ix pack`'s Rust
    path and with `packOracle`, with metadata (and the first root also
    anonymously when `anon`), and compare the bundles byte for byte. Returns
    the differences as messages. -/
def run (label srcPath : String) (roots : Array Lean.Name) (anon : Bool := true) :
    IO (Array String) := do
  let src ← readIxe srcPath
  let addrOf : Std.HashMap Lean.Name Address :=
    src.named.fold (fun m n nd => m.insert (ixToLeanName n) nd.addr) {}
  let dir ← IO.FS.createTempDir
  let mut errors : Array String := #[]
  let mut compared := 0
  let mut constants := 0
  let t0 ← IO.monoMsNow
  let runs : Array (Lean.Name × Bool) :=
    roots.map (·, false) ++ (if anon then (roots[0]?.map fun r => #[(r, true)]).getD #[] else #[])
  for (r, an) in runs do
    let tag := s!"{r}{if an then " [anon]" else ""}"
    let some main := addrOf.get? r
      | errors := errors.push s!"{label}: root {r} not in the source"
        continue
    let out := dir / "rust.ixe"
    let rust ← (Ixon.rsPackEnv srcPath (r.toString (escape := false)) #[] out.toString an
      false).toBaseIO
    match rust, packOracle src main {} an with
    | .error e, .error e' =>
      errors := errors.push s!"{label} {tag}: both fail (Rust: {e}; Lean: {e'})"
    | .error e, .ok _ => errors := errors.push s!"{label} {tag}: Rust fails ({e}), the oracle packs"
    | .ok _, .error e => errors := errors.push s!"{label} {tag}: the oracle fails ({e}), Rust packs"
    | .ok _, .ok lean =>
      match Ixon.serEnv lean with
      | .error e => errors := errors.push s!"{label} {tag}: the oracle's bundle does not serialize: {e}"
      | .ok lb =>
        compared := compared + 1
        constants := constants + lean.consts.size
        let leanOut := dir / "lean.ixe"
        IO.FS.writeBinFile leanOut lb
        unless (← Ixon.rsIxeFilesEqual leanOut.toString out.toString) do
          let rb ← IO.FS.readBinFile out
          let detail := match Ixon.rsDeEnv rb with
            | .ok rustEnv => describe lean rustEnv
            | .error e => s!"Rust bundle unreadable: {e}"
          errors := errors.push s!"{label} {tag}: bundles differ ({lb.size} / {rb.size} bytes; {detail})"
  IO.FS.removeDirAll dir
  let t1 ← IO.monoMsNow
  say s!"{label}: {compared} bundle(s) compared with the Lean oracle ({roots.size} root(s)\
    {if anon then ", the first also anonymously" else ""}; {constants} constants in all), \
    {errors.size} difference(s), {(t1 - t0) / 1000} s"
  return errors

end Tests.Ix.Compile.PackParity
