/- # The changed set of a compile (H1)

## Contract
Input: the compiler's input environment `env` (`Ix.CanonM`'s output, the
statements' `env`) and the artifact `ixe` it compiled to
(`Ix.Cert.compileReport env = .ok (ixe, failures)`, or the IO pipeline's
`LeanPipelineOut.env`). Output (`ofCompile`): the input constants whose
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
* `Named.original` of `ixe`'s entries: the address of the compile of Lean's
  own form of a regenerated auxiliary (the promotion route).

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
* `caller`: an input constant that references an image head and is not one:
  its call sites are rewritten (by Pass 3's `Translate`; before it, by the
  call-site surgery of the planned heads);
* `regenerated`: a regenerated auxiliary whose address is not the address of
  the compile of Lean's own form (`Named.original ≠ addr`), whatever its block
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
never a Pass 3 table.

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
  /-- A regenerated auxiliary whose address is not the compile of Lean's own
  form (`Named.original ≠ addr`). -/
  | regenerated
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

def Cause.tag : Cause → String
  | .member => "member"
  | .imageHead => "image-head"
  | .caller => "caller"
  | .regenerated => "regenerated"

def Cause.index : Cause → Nat
  | .member => 0
  | .imageHead => 1
  | .caller => 2
  | .regenerated => 3

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
  the Lean block; `caller`: the least image head it references (by name hash);
  `regenerated`: none. -/
  ref : Option Name := none
  deriving Inhabited

def Entry.beq (a b : Entry) : Bool := a.name == b.name && a.cause == b.cause && a.ref == b.ref

/-- The changed set of a compile. -/
structure ChangedSet where
  /-- The changed components, by the hash of `Block.first`, then of the first
  representative. -/
  blocks : Array Block := #[]
  /-- The entries, by name hash, then cause. A name has one entry per cause. -/
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

/-- **The changed set** of the compile of `env` to `ixe` (see the module
docstring). -/
def ofCompile (env : Ix.Environment) (ixe : Ixon.Env) : ChangedSet := Id.run do
  let blocks := changedBlocks env ixe
  let mut entries : Array Entry := #[]
  -- members of the changed components, and the Lean blocks of the inductive ones
  let mut leanAll : Std.HashMap Name (Array Name) := {}
  for b in blocks do
    let some first := b.first | continue
    if b.kind == .inductiveBlock then leanAll := leanAll.insert first b.all
    for cls in b.classes do
      for m in cls do
        entries := entries.push { name := m, cause := .member, ref := some first }
        if b.kind == .inductiveBlock then
          if let some (.inductInfo v) := env.get? m then
            for c in v.ctors do
              entries := entries.push { name := c, cause := .member, ref := some first }
  -- the image heads of those Lean blocks
  let mut heads : Std.HashSet Name := {}
  for (all0, all) in leanAll do
    for h in Ix.Compile.Pass.imageKinds env.get? all do
      heads := heads.insert h
      entries := entries.push { name := h, cause := .imageHead, ref := some all0 }
  -- callers and regenerated auxiliaries, over the published names
  for (n, named) in ixe.named do
    if !heads.isEmpty && !heads.contains n then
      if let some ci := env.get? n then
        if let some h := leastName (Ix.Compile.Canon.refsConst ci) heads.contains then
          entries := entries.push { name := n, cause := .caller, ref := some h }
    if let some (orig, _) := named.original then
      if orig != named.addr && (env.get? n).isSome then
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
  return c

/-- One line: the counts by cause. -/
def Counts.summary (c : Counts) : String :=
  s!"{c.components} changed inductive components in {c.leanBlocks} Lean blocks \
(split {c.split}, collapsed {c.collapsed}, permuted {c.permuted}, \
nested moved {c.nestedMoved}, nested evaporated {c.nestedEvaporated}); \
{c.definitions} definition components collapsed inside; \
{c.names} names (member {c.member}, image head {c.imageHead}, caller {c.caller}, \
regenerated {c.regenerated})"

/-! ## The statement (H1)

`Avoids` is the hypothesis shape `CompileCorrect` takes under H1: the closure
`sub` meets no constant of the set. Then the compiled closure is a renaming of
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
    (Ix.Compile.ChangedSet.ofCompile env ixe).Avoids sub →
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

/-- No constant of `sub` is in the set: the hypothesis of the static part of
`CompileCorrect` (H1). -/
def ChangedSet.Avoids (cs : ChangedSet) (sub : Ix.Environment) : Prop :=
  ∀ n ci, sub.consts.get? n = some ci → cs.contains n = false

/-- `Avoids`, decided over `sub`'s keys. (The equivalence needs
`EquivBEq Ix.Name`, which `Ix.Cert.Statement` provides; see `noFailure_iff`.) -/
def ChangedSet.avoids (cs : ChangedSet) (sub : Ix.Environment) : Bool :=
  sub.consts.keys.all fun n => !cs.contains n

end Ix.Compile.ChangedSet

end
