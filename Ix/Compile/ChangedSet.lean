/- # The changed set of a compile (H1)

## Contract
Input: the compiler's input environment `env` (`Ix.CanonM`'s output, the
statements' `env`), the compile's condensation `condensed` (its declaration
groups and their references: the statements' `Ix.Cert.compileBlocks env`, or
the IO pipeline's `LeanPipelineOut.blocks`) and the artifact `ixe` it
compiled to (`Ix.Cert.compileReport env = .ok (ixe, failures)`, or the IO
pipeline's `LeanPipelineOut.env`). Output (`ofCompile`): the input constants whose
compiled form the compiler made something other than a renaming of their
source, each with a typed cause (`Cause`), and the changed components with
theirs (`BlockCause`). Everything outside the set compiles as a pure renaming
of its source, up to the alias fibers that span Source's groups (the proposed
statement is `ChangedSetSound`, below), so the set and its cones are what
`CompileCorrect`'s validation hypotheses name (`ROUTE-A.md` §4.3, H1) and the
only part CQ5.4 validates.

What it reads, and nothing else:
* the `Muts` records of `ixe` (`Ixon.ConstantMetaInfo.muts`): each stored
  component's classes (name hashes, canonical order) and nested layout, as the
  aux tail registered them (`compileMutualAuxTail`, Rust `compile_mutual`);
* the metadata context of `ixe`'s definitions (`ConstantMetaInfo.defn`'s
  `ctx`: the members of the component it was compiled in), for a definition
  component stored as one constant (one class, no `Muts` record);
* Lean's blocks (`InductiveVal.all`) and constants of `env`;
* the condensation `condensed`, with the clique table and the encoding roots
  that Pass 3's driver computes from it and the input before the first wave
  (`cliqueTables`, the driver's own `scheduleCliques`);
* `Named.original` of `ixe`'s entries: the address of the compile of Lean's
  own form of a regenerated auxiliary (the promotion route);
* the aux table `table` (`Ix.AuxGen.AuxTable`): the driver's verdict, on
  bytes, whether a regenerated auxiliary's record is the compile of Lean's own
  form (`identical`).

The causes:
* `member`: a member of a changed component, with the component's
  `BlockCause`s:
  - an inductive component (and its constructors) for which the plan
    predicate (`isChanged`, `Ix.Compile.ChangedSet.Block`) holds against
    Lean's block: split, collapsed, permuted, a nested auxiliary moved or
    evaporated. Lean-generated blocks count as Lean's blocks: an
    `IndPredBelow` family whose regenerated order is not Lean's (A3V-IPB) is a
    changed component, which the plan registration never saw;
  - a definition component two of whose members share a class (`collapsed`):
    a block-internal alias fiber (`ALPHA-COLLAPSE.md` §8.4, the `perm` kind,
    K1). Source groups definitions by component, and quotient Source collapses
    only fibers that span groups, so the compiled component is not a renaming
    of its Source group even up to fibers. The plan predicate is false on it
    (the aux tail sees no `all`), and Pass 3's hooks never run on it: the set's
    predicate is `componentChanged` = `isChanged || collapsesInside`;
* `imageHead`: an image-kind auxiliary (`Ix.Compile.Pass.imageKinds`) of a
  Lean block with a changed inductive component: its recursors, `casesOn`,
  `recOn`, `below`, `brecOn` (with `.go`, `.eq`) and the nested `_N` forms.
  Before Pass 3 these names denote Pass 2's regenerated forms; after it,
  images. All of them, not only the ones CQ4.1's recognizers authenticate
  (which Pass 3 publishes): a custom wrapper that keeps its own form is then in
  the set without need, and the set stays clear of AuxGen's generators, which
  the recognizers run and which are `partial`;
* `caller`: every member of a condensation block whose references
  (`condensed.blockRefs`) hold an image head, and that is not one itself
  (`callerStage`): its block is rewritten by Pass 3's `Translate` (hook 2
  tests exactly these references); and every member of a condensation
  block that references one of Lean's encoding constants of a clique
  (`cliqueStage`): the clique step refuses it when the clique is transported;
* `clique`: a member of an input clique, or an equation lemma carried with
  one (the clique table, `cliqueStage`): the clique step may transport its
  value;
* `regenerated`: a regenerated auxiliary (an input name with a
  `Named.original`) whose published record is not the compile of Lean's own
  form, as the driver decided on bytes (the aux table `table`,
  `Ix.AuxGen.AuxTable.identical`; a name without a row counts as not
  identical), whatever its block
  (ROUTE-A's `aux` kind, B9). It makes the set sound on every input without a
  proof that Pass 2 regenerates Lean's form on unchanged blocks (measured, not
  proved: Init+Std has none).

Not causes: an alias fiber whose names lie in different Source groups is a
renaming up to fibers, handled on the Source side (quotient Source); a
definition component's class order (Source's group order is Lean's name order,
which the renaming's order independence covers, K0). A constant whose own form
is a renaming but whose closure meets the set (the cascade) is not in the set:
it is in the cone of an entry, which `Avoids` excludes for a whole closure.
(Before Pass 3 one kind of rewritten constant is only in a cone: a caller of
a regenerated `IndPredBelow` family's inductives, whose call sites the surgery
permutes; Pass 3 keeps those names, so the caller becomes a renaming.)

The function is the same before and after Pass 3 is wired: it reads the
canonical blocks from the artifact and the heads and callers from the input,
never a Pass 3 table of the fold (the clique tables are the driver's function
of the input and its condensation, computed again here).

## Shape (for the statements)
Pure and total: folds over the artifact's and the input's maps; no name is
parsed (names are built and compared, never read as strings); no `partial`.
Every definition is exposed. Its order is a function of its input (entries
sorted by name hash).
-/
module
public import Ix.Ixon
public import Ix.Compile.Canon.Graph
public import Ix.Compile.Pass.Names
public import Ix.Compile.ChangedSet.Block
public import Ix.Compile.Pass.Clique.Table
public import Ix.AuxGen.Report
@[expose] public section

namespace Ix.Compile.ChangedSet

open Ix (Name ConstantInfo)

/-- Why an input constant is in the changed set. -/
inductive Cause where
  /-- An inductive or constructor of a changed component (`Block.causes`). -/
  | member
  /-- An image-kind auxiliary of a Lean block with a changed component. -/
  | imageHead
  /-- References an image head, and is not one: its call sites are rewritten. -/
  | caller
  /-- A regenerated auxiliary whose published record is not the compile of
  Lean's own form (the aux table's verdict, `AuxTable.identical`). -/
  | regenerated
  /-- A member of an input clique, or an equation lemma carried with one
  (Pass 3's clique table, `cliqueStage`): its value may be transported. -/
  | clique
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

def Cause.tag : Cause → String
  | .member => "member"
  | .imageHead => "image-head"
  | .caller => "caller"
  | .regenerated => "regenerated"
  | .clique => "clique"

def Cause.index : Cause → Nat
  | .member => 0
  | .imageHead => 1
  | .caller => 2
  | .regenerated => 3
  | .clique => 4

/-- The kind of a component. Source groups an inductive block by Lean's `all`
(with its constructors and recursors) and definitions by component. -/
inductive ComponentKind where
  | inductiveBlock
  | definitions
  deriving BEq, DecidableEq, Repr, Inhabited

/-- A changed component, as the artifact stores it. -/
structure Block where
  kind : ComponentKind
  /-- Lean's block (`InductiveVal.all`) of an inductive component; empty for a
  definition component, whose Source group is the component itself (as the
  aux tail sees it: no `all`). -/
  all : Array Name
  /-- The component's classes, canonical order, representative first. -/
  classes : Array (Array Name)
  /-- The component's nested layout. -/
  layout? : Option Ixon.AuxLayout
  /-- Why it is changed (nonempty, `componentCauses_isEmpty`). -/
  causes : Array BlockCause
  deriving Inhabited

/-- The name a component is reported under: Lean's first member of an
inductive block, the first representative of a definition component. -/
def Block.first (b : Block) : Option Name :=
  match b.kind with
  | .inductiveBlock => b.all[0]?
  | .definitions => (b.classes[0]?).bind (·[0]?)

/-- One input constant of the set, with its cause. -/
structure Entry where
  name : Name
  cause : Cause
  /-- `member`: the component's `Block.first`; `imageHead`: the first member of
  the Lean block; `caller`: the least image head its block's references hold (by
  name hash),
  or, for a member of a block that references a clique's encoding
  (`cliqueStage`), the clique's first member; `clique`: the clique's first
  member; `regenerated`: none. -/
  ref : Option Name := none
  deriving Inhabited

def Entry.beq (a b : Entry) : Bool := a.name == b.name && a.cause == b.cause && a.ref == b.ref

/-- The changed set of a compile. -/
structure ChangedSet where
  /-- The changed components, by the hash of `Block.first`, then of the first
  representative. -/
  blocks : Array Block := #[]
  /-- The entries, by name hash, then cause, then reference. A name has one
  entry per cause and reference (a `caller` can have two: an image head's and
  a clique's). -/
  entries : Array Entry := #[]
  /-- The names of `entries`. -/
  names : Std.HashSet Name := {}
  deriving Inhabited

/-- `n` is in the set. -/
def ChangedSet.contains (cs : ChangedSet) (n : Name) : Bool := cs.names.contains n

/-! ## Reading the artifact -/

/-- The `Muts` records of an artifact: each stored component's classes (name
hashes, canonical order) and nested layout. -/
def mutsRecords (ixe : Ixon.Env) : Array (Array (Array Address) × Option Ixon.AuxLayout) :=
  ixe.named.fold (init := #[]) fun acc _ named =>
    match named.constMeta.info with
    | .muts all layout? => acc.push (all, layout?)
    | _ => acc

/-- Lean's block of each input inductive, by the inductive's name hash. -/
def leanBlocks (env : Ix.Environment) : Std.HashMap Address (Array Name) :=
  env.consts.fold (init := {}) fun m n ci =>
    match ci with
    | .inductInfo v => m.insert n.getHash v.all
    | _ => m

/-- The component a `Muts` record stores, read against Lean's block of its
first member: its classes as names, when every stored member is a member of
that block (otherwise the record is no component of an input inductive block:
a definition block, or a regenerated family under other names). -/
def componentOf (lean : Std.HashMap Address (Array Name))
    (record : Array (Array Address) × Option Ixon.AuxLayout) :
    Option (Array Name × Array (Array Name) × Option Ixon.AuxLayout) := do
  let (hashes, layout?) := record
  let h0 ← (hashes[0]?).bind (·[0]?)
  let all ← lean.get? h0
  let byHash : Std.HashMap Address Name := all.foldl (init := {}) fun m n => m.insert n.getHash n
  let classes ← hashes.mapM fun cls => cls.mapM byHash.get?
  pure (all, classes, layout?)

/-- The published names of an artifact, by name hash. -/
def publishedByHash (ixe : Ixon.Env) : Std.HashMap Address Name :=
  ixe.named.fold (init := {}) fun m n _ => m.insert n.getHash n

/-- A member of a Source definition group: an input definition, theorem or
opaque that no aux tail compiled (its entry has no original form). -/
def sourceDefinition (env : Ix.Environment) (ixe : Ixon.Env) (n : Name) : Bool :=
  (match env.get? n with
    | some (.defnInfo _) | some (.thmInfo _) | some (.opaqueInfo _) => true
    | _ => false) &&
  ((ixe.named.get? n).bind (·.original)).isNone

/-- A definition's metadata context (`ConstantMetaInfo.defn`'s `ctx`): its
component's members, by class, then by name. -/
def definitionContext (cm : Ixon.ConstantMeta) : Array Address :=
  match cm.info with
  | .defn _ _ _ ctx .. => ctx
  | _ => #[]

/-- The definition components of the artifact that collapse inside, by their
classes:
* a `Muts` record with a class of two or more members, all of them source
  definitions (several classes);
* a definition published at the address of every member of its metadata
  context, when that context has two or more members, all source definitions
  (one class: the compiler stores the component as a lone constant, with no
  `Muts` record). -/
def collapsedDefinitionComponents (env : Ix.Environment) (ixe : Ixon.Env) :
    Array (Array (Array Name)) := Id.run do
  let byHash := publishedByHash ixe
  let lean := leanBlocks env
  let mut out : Array (Array (Array Name)) := #[]
  for r in mutsRecords ixe do
    if !r.1.any (1 < ·.size) || (componentOf lean r).isSome then continue
    if let some classes := r.1.mapM (·.mapM byHash.get?) then
      if classes.all (·.all (sourceDefinition env ixe)) then out := out.push classes
  let mut seen : Std.HashSet Address := {}
  for (_, named) in ixe.named do
    let ctx := definitionContext named.constMeta
    if ctx.size < 2 || seen.contains named.addr then continue
    let some members := ctx.mapM byHash.get? | continue
    if members.all fun m => ((ixe.named.get? m).map (·.addr)) == some named.addr then
      seen := seen.insert named.addr
      if members.all (sourceDefinition env ixe) then out := out.push #[members]
  return out

/-- The changed components of the artifact: inductive components for which
`componentChanged` holds against Lean's block, and definition components
that collapse inside. -/
def changedBlocks (env : Ix.Environment) (ixe : Ixon.Env) : Array Block :=
  let lean := leanBlocks env
  let inductives := (mutsRecords ixe).filterMap fun r => do
    let (all, classes, layout?) ← componentOf lean r
    if componentChanged all classes layout? then
      some { kind := .inductiveBlock, all, classes, layout?
             causes := componentCauses all classes layout? : Block }
    else none
  let definitions := (collapsedDefinitionComponents env ixe).map fun classes =>
    { kind := .definitions, all := #[], classes, layout? := none
      causes := componentCauses #[] classes none : Block }
  let key (b : Block) : Address × Address :=
    ((b.first.map (·.getHash)).getD default,
      (((b.classes[0]?).bind (·[0]?)).map (·.getHash)).getD default)
  (inductives ++ definitions).qsort fun a b => compare (key a) (key b) == .lt

/-! ## The set -/

/-- The least name of a set, by name hash. -/
def leastName (s : Std.HashSet Name) (keep : Name → Bool) : Option Name :=
  s.fold (init := none) fun best n =>
    if !keep n then best
    else match best with
      | some b => if Ix.nameCompare n b == .lt then some n else some b
      | none => some n

/-- Sort entries by name hash, then cause, then reference; drop repeats. -/
def sortEntries (es : Array Entry) : Array Entry :=
  let key (e : Entry) : Address × Nat × Address :=
    (e.name.getHash, e.cause.index, (e.ref.map (·.getHash)).getD default)
  let sorted := es.qsort fun a b => compare (key a) (key b) == .lt
  sorted.foldl (init := #[]) fun acc e =>
    match acc.back? with
    | some p => if p.beq e then acc else acc.push e
    | none => acc.push e

/-! ## The clique stage (CQ5.2) -/

/-- The clique table and the encoding roots of the input, exactly as the
driver computes them before the first wave from the compile's condensation
`condensed` (`Ix.Compile.Pass.Clique.scheduleCliques` over the input's
lookups): the driver installs them as `CompileEnv.p3Cliques` and
`p3CliqueRoots`, and nothing changes them during the fold. -/
def cliqueTables (env : Ix.Environment) (condensed : Ix.CondensedBlocks) :
    Std.HashMap Name (Array Name × Array Name) × Std.HashMap Name (Array Name) :=
  let view : Ix.Environment := { consts := {}, fallback? := some env.get? }
  (Ix.Compile.Pass.Clique.scheduleCliques view condensed).2

/-- **The clique stage**: the entries of Pass 3's clique step, from the
compile's condensation `condensed` and the clique tables the driver installs
(`cliqueTables`), appended to `entries`:
* `clique`: every name of the clique table (each member of an input clique
  and each equation lemma carried with one), with the clique's first member;
* `caller`: every member of a condensation block whose references
  (`condensed.blockRefs`, the map the driver installs as
  `CompileEnv.p3BlockRefs`) hold one of Lean's encoding constants of a clique
  (`Ix.Compile.Pass.Clique.encodingOwner?` over the encoding roots), with that
  clique's first member. The referencing block's members are entered, not the
  encoding constant, so the block is covered whatever that constant is.

So a block none of whose members is in the set has no member in the clique
table and no reference to a clique's encoding: the clique step is the
identity on it (`Ix.Compile.Pass.cliqueInert`). The stage reads the input
and its condensation only, never a plan: every clique of the table is
entered, with its members, carried lemmas and callers, whatever its outcome.
So the stage over-approximates the clique step, soundly: a clique that keeps
Lean's form (structural or `partial_fixpoint`, decision (ii); a plan that
keeps it; a well-founded plan whose rows do not apply) still has its
`clique` and `caller` entries. Being in the clique table does not mean being
transported. -/
def cliqueStage (env : Ix.Environment) (condensed : Ix.CondensedBlocks)
    (entries : Array Entry) : Array Entry := Id.run do
  let tables := cliqueTables env condensed
  let mut entries := entries
  for (n, cl) in tables.1 do
    entries := entries.push { name := n, cause := .clique, ref := cl.1[0]? }
  for (lo, mems) in condensed.blocks do
    for r in condensed.blockRefs.getD lo {} do
      if let some all := Ix.Compile.Pass.Clique.encodingOwner? tables.2 r then
        for m in mems do
          entries := entries.push { name := m, cause := .caller, ref := all[0]? }
  return entries

/-- **The callers' stage**: every member of a condensation block whose
references (`condensed.blockRefs`, the map the driver installs as
`CompileEnv.p3BlockRefs`, which hook 2 tests) hold an image head, and that is
not one itself, with the least such head by name hash; appended to
`entries`. A caller's call sites are rewritten (Pass 3's `Translate`); a
sibling of a caller in its block compiles in the rewritten block, so it is in
the set too (a sound over-approximation of the constants that reference a
head). Reads the condensation and the heads only: no lookup, no term walk. -/
def callerStage (condensed : Ix.CondensedBlocks) (heads : Std.HashSet Name)
    (entries : Array Entry) : Array Entry := Id.run do
  let mut entries := entries
  if heads.isEmpty then return entries
  for (rep, mems) in condensed.blocks do
    if let some h := leastName (condensed.blockRefs.getD rep {}) heads.contains then
      for m in mems do
        if !heads.contains m then
          entries := entries.push { name := m, cause := .caller, ref := some h }
  return entries

/-- **The changed set** of the compile of `env` to `ixe`, whose condensation
(the compile's declaration groups and their references) is `condensed` and
whose aux table (the driver's byte verdicts on the regenerated auxiliaries,
`Ix.AuxGen.AuxTable`) is `table` (see the module docstring). -/
def ofCompile (env : Ix.Environment) (condensed : Ix.CondensedBlocks) (table : Ix.AuxGen.AuxTable)
    (ixe : Ixon.Env) : ChangedSet := Id.run do
  let blocks := changedBlocks env ixe
  let mut entries : Array Entry := #[]
  -- members of the changed components (with an inductive component's
  -- constructors), every component, whether or not it has a `first`
  for b in blocks do
    for cls in b.classes do
      for m in cls do
        entries := entries.push { name := m, cause := .member, ref := b.first }
        if b.kind == .inductiveBlock then
          if let some (.inductInfo v) := env.get? m then
            for c in v.ctors do
              entries := entries.push { name := c, cause := .member, ref := b.first }
  -- the image heads of each changed inductive component's Lean block, read
  -- off the component itself (two components of one Lean block push the same
  -- entries, which the sort drops), not through a map keyed by first name
  let mut heads : Std.HashSet Name := {}
  for b in blocks do
    if b.kind == .inductiveBlock then
      for h in Ix.Compile.Pass.imageKinds env.get? b.all do
        heads := heads.insert h
        entries := entries.push { name := h, cause := .imageHead, ref := b.first }
  -- the clique step's members, carried lemmas and callers (`cliqueStage`)
  entries := cliqueStage env condensed entries
  -- the callers of the heads, by block (`callerStage`)
  entries := callerStage condensed heads entries
  -- regenerated auxiliaries, over the published names
  for (n, named) in ixe.named do
    if named.original.isSome && (env.get? n).isSome && !table.identical n then
      entries := entries.push { name := n, cause := .regenerated }
  let sorted := sortEntries entries
  let names : Std.HashSet Name := sorted.foldl (init := {}) fun s e => s.insert e.name
  return { blocks, entries := sorted, names }

/-! ## Counts -/

/-- The set's size by cause. -/
structure Counts where
  /-- Changed inductive components, and the Lean blocks they belong to. -/
  components : Nat := 0
  leanBlocks : Nat := 0
  /-- Inductive components with each block cause. -/
  split : Nat := 0
  collapsed : Nat := 0
  permuted : Nat := 0
  nestedMoved : Nat := 0
  nestedEvaporated : Nat := 0
  /-- Definition components that collapse inside (each `collapsed`). -/
  definitions : Nat := 0
  /-- Names, and names with each cause. -/
  names : Nat := 0
  member : Nat := 0
  imageHead : Nat := 0
  caller : Nat := 0
  regenerated : Nat := 0
  clique : Nat := 0
  deriving Inhabited, Repr, BEq

def ChangedSet.counts (cs : ChangedSet) : Counts := Id.run do
  let has (b : Block) (p : BlockCause → Bool) : Nat := if b.causes.any p then 1 else 0
  let mut c : Counts := { names := cs.names.size }
  let mut alls : Std.HashSet Name := {}
  for b in cs.blocks do
    if b.kind == .definitions then
      c := { c with definitions := c.definitions + 1 }
      continue
    if let some a := b.all[0]? then alls := alls.insert a
    c := { c with
      components := c.components + 1
      split := c.split + has b (· == .split)
      collapsed := c.collapsed + has b (· == .collapsed)
      permuted := c.permuted + has b (· == .permuted)
      nestedMoved := c.nestedMoved + has b BlockCause.isNestedMoved
      nestedEvaporated := c.nestedEvaporated + has b BlockCause.isNestedEvaporated }
  c := { c with leanBlocks := alls.size }
  for e in cs.entries do
    c := match e.cause with
      | .member => { c with member := c.member + 1 }
      | .imageHead => { c with imageHead := c.imageHead + 1 }
      | .caller => { c with caller := c.caller + 1 }
      | .regenerated => { c with regenerated := c.regenerated + 1 }
      | .clique => { c with clique := c.clique + 1 }
  return c

/-- One line: the counts by cause. -/
def Counts.summary (c : Counts) : String :=
  s!"{c.components} changed inductive components in {c.leanBlocks} Lean blocks \
(split {c.split}, collapsed {c.collapsed}, permuted {c.permuted}, \
nested moved {c.nestedMoved}, nested evaporated {c.nestedEvaporated}); \
{c.definitions} definition components collapsed inside; \
{c.names} names (member {c.member}, image head {c.imageHead}, caller {c.caller}, \
regenerated {c.regenerated}, clique {c.clique})"

/-! ## The statement (H1)

`Avoids` says that the closure `sub` meets no constant of the set. It selects
the unchanged-closure case inside the proof of `Ix.Cert.CompileCorrect`, whose
statement takes no such hypothesis (the changed records are validated instead,
`Ix.Cert.KindAccepted`). Then the compiled closure is a renaming of
its source up to the alias fibers that span Source's groups. Block-internal
fibers (two names of one fiber in one Source group: an inductive block, or a
definition component) are classified, not renamed: they are the `perm` kind
(K1, `ALPHA-COLLAPSE.md` §8.4), whose members are `member` entries of a
changed component (an inductive block that collapses is a plan change, a
definition component that collapses inside is `componentChanged`), so a
closure that `Avoids` the set meets none. Only cross-group fibers are handled
up to σ, by quotient Source. The proposed statement, for the statements lane
(`Ix.Cert` imports this module, not the reverse; names as in
`Ix.Cert.Statement` and `ROUTE-A.md` §4.4):

```
/-- σ: a source id to the address `ixe` publishes for it (`Ixon.Env.named`).
Every member of an alias fiber goes to the fiber's address, so σ is injective
exactly up to fibers; `collapse` keeps one declaration per fiber (its members
rename to one declaration, `FiberHyp`, ROUTE-A §4.4). Under `Avoids` every
fiber the closure meets spans Source's groups. -/
def fiberAddr (ixe : Ixon.Env) : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon := …

/-- **ChangedSet soundness**: a closure outside the changed set compiles as a
renaming of its source up to the alias fibers that span Source's groups. The
reader's declarations of the compiled closure (in a closure order, B4) are the
Source declarations of `sub` (one per group), renamed by
`Key.map (fiberAddr ixe)`, one per cross-group fiber, up to that order. -/
def ChangedSetSound : Prop :=
  ∀ (env : Ix.Environment) (roots : List Ix.Name) (sub : Ix.Environment) (ixe : Ixon.Env)
    (failures : Failures) (preS : Ix.Kernel.Reader.Prelude .source) (dsS : Array (CDecl .source)),
    IsClosure env roots sub → compileReport env = .ok (ixe, failures) → NoFailure failures sub →
    (Ix.Compile.ChangedSet.ofCompile env (compileBlocks env) (compileTable env) ixe).Avoids sub →
    Ix.LeanIngress.prepareSource preS sub (blocksOf sub) = .ok dsS →
    ∃ binding preA limits order evA dsA,
      Ix.Kernel.Admission.defaultBinding = .ok binding ∧
      ClosureOrder ixe (Seed ixe sub) order ∧
      Ix.Kernel.Admission.prepareWith Address.blake3Pure binding preA limits
        (recordsOf ixe order) (blobsOf ixe order) (hintsOf ixe) = .ok (evA, dsA) ∧
      dsA.toList.Perm
        (collapse (dsS.map (Rename.declaration (Ix.Kernel.Key.map (fiberAddr ixe))))).toList
```

The evidence (B6), hints (B7), universes (B8) and roles (B5) are the bridge
items ROUTE-A §3.2 lists beside it; `collapse` and `FiberHyp` are ROUTE-A
§4.4's drafts (no file defines them yet). The per-constant core, which the
statement reduces to with the reading chain (N-READS): for `n` published and
not in the set, the record at `n`'s address is the compile of `n`'s Lean
declaration in Lean's own form, in a component that does not collapse inside
(no member of a changed component, no image head, no rewritten call site, and
a regenerated auxiliary only at the address of its original form). -/

/-- No constant of `sub` is in the set: the case of `Ix.Cert.CompileCorrect`'s proof in
which the compiled closure is a renaming of its source. -/
def ChangedSet.Avoids (cs : ChangedSet) (sub : Ix.Environment) : Prop :=
  ∀ n ci, sub.consts.get? n = some ci → cs.contains n = false

/-- `Avoids`, decided over `sub`'s keys. (The equivalence needs
`EquivBEq Ix.Name`, which `Ix.Cert.Statement` provides; see `noFailure_iff`.) -/
def ChangedSet.avoids (cs : ChangedSet) (sub : Ix.Environment) : Bool :=
  sub.consts.keys.all fun n => !cs.contains n

end Ix.Compile.ChangedSet

end
