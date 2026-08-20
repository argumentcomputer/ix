/-
  C5: qualification is metadata-only THROUGH aux-gen — the strongest
  regression binding the aux-disposition fix to the catalog machinery.

  The `Tests.Ix.Compile.Mutual` corpus (alpha-collapse, over-merge,
  nested aux ordering, and the `AuxOwnership.*` cross-SCC shapes that
  produced the TruthMines alias collision) is compiled twice: once
  unqualified, once with every fixture constant relocated under a
  `C5Qual.` prefix (compile-layer rename via
  `Ix.Catalog.relocateConstantInfo`, no kernel replay). The anon
  layers must agree exactly:

  - the sets of anon constant addresses are equal, and
  - for every fixture constant `N`, `addr(N) = addr(C5Qual.N)`.

  Both compiles run over the fixtures' reference closure only (BFS
  into the base env), so the gate stays default-suite fast.
-/
module

public import LSpec
public import Ix.Catalog
public import Ix.CompileM
public import Ix.Meta

public section

open LSpec

namespace Tests.Ix.CatalogQualified

private def fixtureModule : Lean.Name := `Tests.Ix.Compile.Mutual
private def qualPrefix : Lean.Name := `C5Qual

/-- Reference closure of `roots` over `env`, as a name→info list. -/
private def closureOf (env : Lean.Environment)
    (roots : Array Lean.Name) :
    Except String (Array (Lean.Name × Lean.ConstantInfo)) := do
  let mut seen : Lean.NameSet := {}
  let mut work := roots
  let mut out : Array (Lean.Name × Lean.ConstantInfo) := #[]
  while !work.isEmpty do
    let n := work.back!
    work := work.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n
      | throw s!"closure: unknown constant {n}"
    out := out.push (n, ci)
    for r in Ix.Catalog.constantInfoReferences ci do
      unless seen.contains r do
        work := work.push r
  return out

private def qualifiedAnonTest : IO (Bool × Nat × Nat × Option String) := do
  initLeanSearchPath
  let env ← Lean.importModules #[{ module := fixtureModule }] {}
  -- Fixture-owned constants by MODULE identity, not name prefix: the
  -- corpus is a module-mode file, so private-mangled spellings
  -- (`_private.Tests.Ix.Compile.Mutual.0.…`) circulate alongside the
  -- plain names — a prefix filter splits one constant set into
  -- renamed and unrenamed halves with dangling cross-references
  -- (observed as an ungrounded cascade). Ownership is
  -- `getModuleIdxFor?`; the rename map then covers EVERY owned
  -- spelling that appears as a key or reference, each qualified
  -- atomically.
  let some fixtureIdx := env.getModuleIdx? fixtureModule
    | return (false, 0, 0, some "fixture module not in environment")
  let ownedKey := fun (n : Lean.Name) =>
    env.getModuleIdxFor? n == some fixtureIdx
  let owned := env.constants.fold (init := (#[] : Array Lean.Name))
    fun acc n _ => if ownedKey n then acc.push n else acc
  if owned.isEmpty then
    return (false, 0, 0, some "no fixture constants found")
  let closure ← match closureOf env owned with
    | .ok c => pure c
    | .error e => return (false, 0, 0, some e)
  -- Rename map over every owned spelling in play (keys and refs).
  let mut renameMap : Lean.NameMap Lean.Name := {}
  for (n, ci) in closure do
    if ownedKey n then
      renameMap := renameMap.insert n (qualPrefix ++ n)
    for r in Ix.Catalog.constantInfoReferences ci do
      if ownedKey r then
        renameMap := renameMap.insert r (qualPrefix ++ r)
  let renameMapFrozen := renameMap
  let renamed := closure.map fun (n, ci) =>
    if renameMapFrozen.contains n then
      (Ix.Catalog.rename renameMapFrozen n,
       Ix.Catalog.relocateConstantInfo renameMapFrozen ci)
    else
      (n, ci)
  let env1 ← Ix.CompileM.rsCompileEnvOf closure.toList
  let env2 ← Ix.CompileM.rsCompileEnvOf renamed.toList
  -- Per-constant address preservation first — a concrete divergent
  -- name beats a set-size delta for diagnosis.
  let mut checked := 0
  let mut diverged : Array String := #[]
  for n in owned do
    let (ixSrc, _) := (Ix.CanonM.canonName n).run {}
    let (ixTgt, _) := (Ix.CanonM.canonName (qualPrefix ++ n)).run {}
    match env1.named.get? ixSrc, env2.named.get? ixTgt with
    | some a, some b =>
      checked := checked + 1
      if a.addr != b.addr then
        diverged := diverged.push s!"addr({n}) ≠ addr({qualPrefix ++ n})"
    | none, _ => diverged := diverged.push s!"unqualified missing {n}"
    | _, none =>
      diverged := diverged.push s!"qualified missing {qualPrefix ++ n}"
  unless diverged.isEmpty do
    -- Diagnostic: what the qualified env holds for the first affected
    -- block family.
    -- Diagnostic: recompile the renamed list through the
    -- status-returning FFI, which names every ungrounded constant with
    -- a reason.
    let dir ← IO.FS.createTempDir
    let status ← Ix.CompileM.rsCompileEnvBytesFFI renamed.toList
      (dir / "diag.ixe").toString true
    IO.FS.removeDirAll dir
    let reasons := status.ungrounded.toList.take 1 |>.map
      fun (n, r) => s!"{n}: {r.take 900}"
    return (false, 0, 0, some s!"{diverged.size} divergent \
({checked} checked; named sizes {env1.named.size} vs \
{env2.named.size}; ungrounded {status.ungrounded.size}): \
{String.intercalate " || " reasons}")
  -- Whole anon layers agree.
  if env1.consts.size != env2.consts.size then
    return (false, 0, 0, some s!"anon layer size drift: \
{env1.consts.size} unqualified vs {env2.consts.size} qualified")
  for (addr, _) in env1.consts do
    unless env2.consts.contains addr do
      return (false, 0, 0,
        some s!"anon address {addr} missing from the qualified compile")
  return (true, checked, env1.consts.size, none)

def suite : List TestSeq := [
  .individualIO
    "qualified and unqualified Mutual-corpus compiles share one anon layer (C5)"
    none qualifiedAnonTest .done ]

end Tests.Ix.CatalogQualified
