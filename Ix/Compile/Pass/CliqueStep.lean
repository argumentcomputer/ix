/-
  Ix.Compile.Pass.CliqueStep: the changed-clique hook in a block's compile
  (CQ5.2 (b)), the step `Ix.CompileDriver.runBlockWithAux` takes first, as
  one bind before hook 2 (`prepareBlock`).

  `cliqueStep` reads the clique tables the driver set before the first wave
  (`CompileEnv.p3Cliques`, `p3CliqueRoots`: `Clique.scheduleCliques`) and the
  plan table (`p3CliquePlans`), asks the hook (`Clique.prepareCliques`) what
  the block needs, and gives the block:
  * its compile environment: the input with the overlay of the block's
    transported members and carried lemmas (Lean's constant, Lean's name,
    type and constructors, the transported value under the decompile record
    `_ix.inline`), and those records' sources (`CompileEnv.p3Sources`,
    placeholder indices from `Clique.cliqueRecordBase`);
  * the block state it starts from: the canonical constants the members
    reach, compiled as auxiliary constants (`auxConsts`, `auxNamed`,
    `auxNameToAddr`, under their reserved `_ix` names) in the hook's order,
    and the plans the block computed for the plan table;
  * what the canonical constants' rewrites publish (their views).

  **The inert test first** (`cliqueInert`): a block with no member in the
  clique table and no reference to a clique's encoding constant gets the
  compile environment as it is, the empty block state and nothing published,
  which is what `runBlockWithAux` used before the step
  (`Ix.Cert.PassHooks.cliqueStep_inert`).

  **Well-founded cliques only** (decision (ii), 2026-10-21): the hook runs
  with `HookEnv.wfOnly`, so a structural or `partial_fixpoint` clique keeps
  Lean's form (its outcome is `baseline enc .shape`, with the reason), and
  its callers compile as today.

  **The memo caveat.** The canonical constants' call-site rewrite is the one
  the block's members get (`prepareBlock`: the definitional passes,
  `passConfig`, with `passExpansionLookup`), which records nothing (no
  decline, no proof-justified form, not in place) and reads the image memo
  for a recursor's image only. So the step neither reads nor writes clique
  data in the rewrite state, and the image memo is untouched.

  Rust: `pass3::driver::compile_block`'s clique step (`clique_step`), the
  same order and the same tests.
-/
module
public import Ix.Compile.Pass.Driver
public import Ix.Compile.Pass.Clique.Hook
public section

namespace Ix.Compile.Pass

open Ix (Name Expr ConstantInfo)
open Ix.CompileM

/-- The clique step has nothing to do with the block `all` (key `lo`): the
input has no clique, or no member of the block is in the clique table and
none of the block's references (the condensation's, `p3BlockRefs`) is one of
Lean's encoding constants of a clique (`Clique.encodingOwner?`). The hook
would then give the empty preparation (`Clique.prepareCliques`); the test
decides it without the hook. -/
def cliqueInert (cenv : CompileEnv) (all : Set Name) (lo : Name) : Bool :=
  cenv.p3Cliques.isEmpty ||
    (!all.toList.any cenv.p3Cliques.contains &&
      !(cenv.p3BlockRefs.getD lo {}).toList.any fun r =>
        (Clique.encodingOwner? cenv.p3CliqueRoots r).isSome)

/-- The hook's read of the compile state (`Clique.HookEnv`), well-founded
cliques only. -/
def cliqueHookEnv (cenv : CompileEnv) : Clique.HookEnv :=
  { env := cenv.env, addr? := resolveAddr cenv, table := cenv.p3Cliques
    roots := cenv.p3CliqueRoots, plans := cenv.p3CliquePlans
    checkPlans := cenv.p3CheckPlans, wfOnly := true }

/-- The call-site rewrite of a canonical constant `c` of a clique: the
rewrite a block's members get (`prepareBlock`: the views of the changed
blocks it references, the definitional passes), so a transported clique
over a changed block references its images as any constant does. The
rewritten constant (itself when nothing changed), its decompile sources
(placeholder `i` for entry `i`) and the views the rewrite built. A rewrite
that records Pass 3 data (a decline, a pass's canonical constant, a
proof-justified form) is an error: the memo caveat, checked. -/
def rewriteCliqueCanon (cenv : CompileEnv) (c : Name) (ci : ConstantInfo) :
    Except CompileError (ConstantInfo × Std.HashMap Nat Expr × Published) := do
  if cenv.p3Heads.isEmpty then return (ci, {}, {})
  let used := headsIn cenv.p3Heads ci
  if used.isEmpty then return (ci, {}, {})
  let fail := pass3Failure cenv (used.filterMap fun h => cenv.p3Heads.get? h)
  let views ← (viewsOf cenv used).mapError fail
  let rwr ← (rewriteBlock (passExpansionLookup cenv views) #[(c, ci)]
    (passConfig cenv views)).mapError fail
  -- the memo caveat, checked: the rewrite records nothing (no decline, no
  -- canonical constant of a pass, no proof-justified form), so the step reads
  -- the image memo as any block does and writes no clique data into it (Rust
  -- `rewrite_block` returns no records at all)
  unless rwr.declines.isEmpty && rwr.canon.isEmpty && rwr.pjForms.isEmpty do
    throw (.invalidMutualBlock
      s!"Pass 3 cliques: the rewrite of the canonical constant {c.pretty} recorded Pass 3 data")
  let ci' := ((rwr.overlay[0]?).map (·.2)).getD ci
  let sources : Std.HashMap Nat Expr :=
    rwr.sources.zipIdx.foldl (fun m (e, i) => m.insert i e) {}
  return (ci', sources, { views := newMemoViews cenv views })

/-- The error of a canonical constant that does not compile. -/
def cliqueCanonError (c : Name) (e : CompileError) : CompileError :=
  .invalidMutualBlock s!"Pass 3 cliques: canonical constant {c.pretty}: {e}"

/-- Compile the canonical constants `canon` (in the hook's order: each after
the canonical constants it references) into the block state `st`, each as a
lone constant from its own rewrite, as an auxiliary constant under its
reserved name (`auxConsts`, `auxNamed`, `auxNameToAddr`, its blobs, names
and hints): the block's members then resolve them through the block's
auxiliary names (`lookupConstAddr`), and the driver merges them like the aux
tail's constants (`mergeCompiledBlock`; reserved names are insert-once,
`checkBlockClaims`). Each constant resolves the earlier ones through the
same map. -/
def compileCliqueCanon (cenv : CompileEnv) (canon : Array (Name × ConstantInfo))
    (st : BlockState) : Except CompileError (BlockState × Published) := do
  let mut st := st
  let mut published : Published := {}
  for (c, ci) in canon do
    let (ci', sources, pub) ← (rewriteCliqueCanon cenv c ci).mapError (cliqueCanonError c)
    published := published ++ pub
    let blockEnv : BlockEnv :=
      { all := ({} : Set Name).insert c, current := c, mutCtx := default, univCtx := [] }
    let (r, bs) ← (CompileM.run { cenv with p3Sources := sources } blockEnv
      { auxNameToAddr := st.auxNameToAddr } (compileConstantInfo ci')).mapError (cliqueCanonError c)
    let r := withMetaRefs bs.p3MetaRefs c r
    st := { st with
      auxConsts := st.auxConsts.push (r.blockAddr, r.block)
      auxNamed := st.auxNamed.push (c, { addr := r.blockAddr, constMeta := r.blockMeta })
      auxNameToAddr := st.auxNameToAddr.insert c r.blockAddr
      blockBlobs := bs.blockBlobs.fold (fun m k v => m.insert k v) st.blockBlobs
      blockNames := bs.blockNames.fold (fun m k v => m.insert k v) st.blockNames
      defHints := bs.defHints.fold (fun m k v => m.insert k v) st.defHints }
  return (st, published)

/-- **The clique step**, before hook 2 (`prepareBlock`): the block's compile
environment, the block state it starts from, and what it publishes (see the
module note). Identity (the compile environment as it is, the empty block
state, nothing published) when the block has nothing to do with a clique
(`cliqueInert`). A caller that unfolds a transported clique's encoding, a
plan-table difference under `p3CheckPlans`, and a canonical constant that
does not compile are the block's errors.

The compile environment changes only by the overlay: each overlay entry is
Lean's constant of that name with another value (`Clique.withValue`), so
every name, type and constructor reads as in the input; and by the overlay
records' sources (`p3Sources`), which hook 2 merges with its own. -/
def cliqueStep (cenv : CompileEnv) (all : Set Name) (lo : Name) :
    Except CompileError (CompileEnv × BlockState × Published) := do
  if cliqueInert cenv all lo then return (cenv, {}, {})
  let prep ← (Clique.prepareCliques (cliqueHookEnv cenv) all (cenv.p3BlockRefs.getD lo {})).mapError
    .invalidMutualBlock
  let init : BlockState := { p3CliquePlans := prep.fresh, p3PlanReused := prep.reused }
  if prep.overlay.isEmpty then return (cenv, init, {})
  let (init, published) ← compileCliqueCanon cenv prep.canon init
  let overlay : Std.HashMap Name ConstantInfo :=
    prep.overlay.foldl (fun m (n, ci) => m.insert n ci) {}
  let sources : Std.HashMap Nat Expr :=
    prep.sources.foldl (fun m (i, e) => m.insert i e) cenv.p3Sources
  -- the transported members over the input, read through `fallback?` (as
  -- hook 2's overlay: the input's materialized constants count as
  -- unmaterialized in this view)
  let base := cenv.env
  let env : Ix.Environment :=
    { consts := {}, fallback? := some fun n => (overlay.get? n).orElse fun _ => base.get? n }
  return ({ cenv with env, unmaterialized := cenv.unmaterialized + base.consts.size
                      p3Sources := sources }, init, published)

end Ix.Compile.Pass

end
