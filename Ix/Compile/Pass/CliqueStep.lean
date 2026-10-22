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
open Ix.Compile.ExactKey (ExactName)

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
that records a decline returns it in Published (CQ5.3a), so no effect is
lost. A pass-created canonical constant or proof-justified form is still an
error: those records are not carried by this path. -/
def rewriteCliqueCanon (cenv : CompileEnv) (sourceAll : Set Name) (c : Name) (ci : ConstantInfo) :
    Except CompileError (ConstantInfo × Std.HashMap Nat Expr × Published) := do
  if cenv.p3Heads.isEmpty then return (ci, {}, {})
  let used := headsIn cenv.p3Heads ci
  if used.isEmpty then return (ci, {}, {})
  let fail := pass3Failure cenv (used.filterMap fun h => cenv.p3Heads.get? h)
  let views ← (viewsOf cenv used).mapError fail
  let rwr ← (rewriteBlock (passExpansionLookup cenv views) #[(c, ci)]
    (passConfig cenv views sourceAll)).mapError fail
  -- Declines travel with this result and are published on block success.
  -- The default image memo still records nothing; passExpansionLookup does
  -- not reuse a definitional head rewritten under another configuration.
  unless rwr.canon.isEmpty && rwr.pjForms.isEmpty do
    throw (.invalidMutualBlock
      s!"Pass 3 cliques: the rewrite of the canonical constant {c.pretty} recorded Pass 3 data")
  let ci' := ((rwr.overlay[0]?).map (·.2)).getD ci
  let sources : Std.HashMap Nat Expr :=
    rwr.sources.zipIdx.foldl (fun m (e, i) => m.insert i e) {}
  return (ci', sources, { views := newMemoViews cenv views, declines := rwr.declines })

/-- A lone constant `c` compiled for the clique step or its rows (`r`, with
the block state `bs` of its compile), added to the block state `st` as an
auxiliary constant under its reserved name: its record (`auxConsts`), its
`Named` entry (`auxNamed`), its address (`auxNameToAddr`, where later
constants and the block's members resolve it), its blobs, names and hints. -/
def addAuxConst (st : BlockState) (c : Name) (r : BlockResult) (bs : BlockState) : BlockState :=
  { st with
    auxConsts := st.auxConsts.push (r.blockAddr, r.block)
    auxNamed := st.auxNamed.push (c, { addr := r.blockAddr, constMeta := r.blockMeta })
    auxNameToAddr := st.auxNameToAddr.insert c r.blockAddr
    blockBlobs := bs.blockBlobs.fold (fun m k v => m.insert k v) st.blockBlobs
    blockNames := bs.blockNames.fold (fun m k v => m.insert k v) st.blockNames
    defHints := bs.defHints.fold (fun m k v => m.insert k v) st.defHints }

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
def compileCliqueCanon (cenv : CompileEnv) (sourceAll : Set Name) (canon : Array (Name × ConstantInfo))
    (st : BlockState) : Except CompileError (BlockState × Published) := do
  let mut st := st
  let mut published : Published := {}
  for (c, ci) in canon do
    let (ci', sources, pub) ← (rewriteCliqueCanon cenv sourceAll c ci).mapError (cliqueCanonError c)
    published := published ++ pub
    let blockEnv : BlockEnv :=
      { all := ({} : Set Name).insert c, current := c, mutCtx := default, univCtx := [] }
    let (r, bs) ← (CompileM.run { cenv with p3Sources := sources } blockEnv
      { auxNameToAddr := st.auxNameToAddr } (compileConstantInfo ci')).mapError (cliqueCanonError c)
    st := addAuxConst st c (withMetaRefs bs.p3MetaRefs c r) bs
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
  let init : BlockState :=
    { p3CliquePlans := prep.fresh, p3CliqueRows := prep.rows, p3PlanReused := prep.reused }
  if prep.overlay.isEmpty then return (cenv, init, {})
  let (init, published) ← compileCliqueCanon cenv all prep.canon init
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

/-! ## The rows, after the fold -/

/-- Compile a row or an `_ix.src` copy `ci` as a lone constant (no decompile
record), resolving the rows' earlier constants through `known` (the rows'
block state's auxiliary names). A reserved name already claimed at another
address is an error (`checkBlockClaims`, Rust `publish_image`). -/
def compileRowConst (cenv : CompileEnv) (known : Std.HashMap ExactName Address)
    (ci : ConstantInfo) : Except CompileError (BlockResult × BlockState) := do
  let c := ci.getCnst.name
  let blockEnv : BlockEnv :=
    { all := ({} : Set Name).insert c, current := c, mutCtx := default, univCtx := [] }
  let (r, bs) ← CompileM.run { cenv with p3Sources := {} } blockEnv
    { auxNameToAddr := known } (compileConstantInfo ci)
  if let some a := cenv.auxNameToAddr.get? c then
    if a != r.blockAddr then
      throw (.invalidMutualBlock s!"Pass 3 cliques: {c.pretty} is already claimed at another address")
  return (r, bs)

/-- Compile the rows' constants `cs` against the block state `st`, each on a
task of its own (`Task.spawn`), and add them to `st` in their order
(`addAuxConst`). The value does not depend on the tasks: `(Task.spawn f).get
= f ()`, and the merge is in order. -/
def compileRowsParallel (cenv : CompileEnv) (st : BlockState) (cs : Array ConstantInfo) :
    Except String BlockState := do
  let known := st.auxNameToAddr
  let tasks := cs.map fun ci => Task.spawn fun _ => (ci.getCnst.name, compileRowConst cenv known ci)
  let mut st := st
  for t in tasks do
    match t.get with
    | (c, .ok (r, bs)) => st := addAuxConst st c r bs
    | (c, .error e) => throw s!"Pass 3 cliques: row {c.pretty}: {e}"
  return st

/-- **The clique rows** (CQ5.2), compiled after the fold from its final
compile environment: for every transported plan of the plan table
(`CompileEnv.p3CliquePlans`, by clique key in pretty-name order) whose
members and rows' prerequisites (`Clique.rowPrereqs`) all compiled, its
`_ix.src` copies, then its rows (`Clique.rowsOf`), each as a lone constant
under its reserved name. Nothing references a row or a copy but a row, so they
come last; the bytes do not depend on their order (content addressing,
name-keyed tables).

The plans' rows come from the rows table (`CompileEnv.p3CliqueRows`, a memo
of `rowsOf` filled when each plan was made: `CliqueOutcome.wfOnlyRows`),
through `memoLookup`: a missing entry is computed, and with `p3CheckPlans`
every entry is recomputed and a difference is an error prefixed by
`Clique.planCheckPrefix`. The table changes no byte.

In parallel, in rounds: the plans' rows are read (or computed) on a task
each; the copies (which reference each other: `all₀._mutual._ix.src` its
proofs' copies) compile level by level, each round taking every pending copy
whose copy references (`Clique.canonRefs`) are compiled, at most one round
per copy plus one (a bounded `for`; a round that takes nothing is the cyclic
error); then every row in one round (`compileRowsParallel`). A copy or a
row that does not compile, and a plan whose rows no longer apply (`rowsOf`
accepted it when the plan was made, `CliqueOutcome.wfOnly`), are the
compile's errors. A plan with a member that did not compile has no rows: its
members are not published. -/
def cliqueRows (cenv : CompileEnv) : Except String BlockState := do
  let plans := (cenv.p3CliquePlans.toArray.qsort fun a b => a.1.pretty < b.1.pretty).filterMap
    fun (key, outcome) => match outcome with
      | .transported plan =>
        if (plan.all ++ Clique.rowPrereqs).all fun n => (resolveAddr cenv n).isSome then
          some (key, plan)
        else none
      | _ => none
  let rowTasks := plans.map fun (key, plan) => Task.spawn fun _ =>
    memoLookup cenv.p3CliqueRows cenv.p3CheckPlans
      s!"{Clique.planCheckPrefix} the rows of the clique {key.pretty}" key
      fun _ => Clique.rowsOf cenv.env.get? plan
  let mut copies : Array ConstantInfo := #[]
  let mut rows : Array ConstantInfo := #[]
  for t in rowTasks do
    let (cs, rs) ← t.get
    copies := copies ++ cs
    rows := rows ++ rs
  let byName : Std.HashMap Name ConstantInfo :=
    copies.foldl (fun m ci => m.insert ci.getCnst.name ci) {}
  let mut st : BlockState := {}
  let mut pending := copies
  for _ in [0:copies.size + 1] do
    if pending.isEmpty then break
    let done := st.auxNameToAddr
    let ready := pending.filter fun ci =>
      (Clique.canonRefs byName ci.getCnst.name ci).all fun r => done.contains r
    if ready.isEmpty then
      throw s!"Pass 3 cliques: row copies with cyclic references: {pending.map (·.getCnst.name.pretty)}"
    st ← compileRowsParallel cenv st ready
    let now := st.auxNameToAddr
    pending := pending.filter fun ci => !now.contains ci.getCnst.name
  unless pending.isEmpty do
    throw s!"Pass 3 cliques: row copies left: {pending.map (·.getCnst.name.pretty)}"
  compileRowsParallel cenv st rows

end Ix.Compile.Pass

end
