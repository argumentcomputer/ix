module
public import Ix.LeanIngress
public import Ix.AuxGen.SourceEnv
public import Ix.AuxGen.ExprUtils
public import Ix.AuxGen.FastPaths
public section

/-! # The Source service environment (AuxGen on IxC, M1; AUXGEN-IXC §3.2)

The environment IxC answers AuxGen's kernel questions in: the compiler's own
input in Source mode (`Ix.LeanIngress`), checked by the verified fold one
declaration group at a time, **on demand**, and extended by the canonical
flat blocks of the blocks whose canonical layout is not Lean's
(`Ix.AuxGen.Flat`), read through their class map σ. Its checked half (the
fold, the evidence, σ, terms in, installs) is `Ix.AuxGen.Source.SourceEnv`;
this file builds it from the compiler's input, and carries it through the
compile drivers (`RunAhead`, below).

## Shape

* **The input** (`Input`) is read through lookups only (`Ix.Environment.get?`)
  and the condensation. The service never enumerates the environment, so the
  compile drivers can hand it their lookup view (theorem and opaque bodies
  canonicalized on demand), and a materialized environment with the same
  lookups gives the same service.
* **Groups are met when a name they claim is asked for or referenced**
  (`discover`): an inductive family member in its block's group
  (`inductiveGroup`, with the recursors `T.rec` and `T₀.rec_j` the block
  names), any other constant in its condensation component's group
  (`componentGroup`), a constant neither claims in a group of its own that
  fails with the reader's reason (`unplaced`): `groupsOf`'s placement, one
  group at a time.
* **Lowering** (`lowerClosure`): a group is converted and lowered through the
  reader's back half after every group it references (the condensation's
  `blockRefs`, and the groups of the constants its literals reference), by a
  depth-first postorder whose successors are taken in Lean's name order
  (`orderOf`'s rule), against the reader's state threaded group by group. A
  group whose references do not all come before it (a cycle) or cannot be
  placed is refused, as `scheduleOf` refuses it.
* **Folding** (`ensure`): a group is folded after every group it depends on
  (hard and literal edges, and the ground of the `Nat` operations it
  declares, `natOpDeps`, the edges `preparePrelude`'s hoist serves), by the
  verified fold's two phases per declaration. A group is folded once; a group
  a failed group precedes is blocked, not folded; a group whose declaration
  the fold refuses leaves the fold as it was before the group. A group's
  terms are dropped once it is lowered and its reading once it is folded:
  the fold holds what it accepted.
* **Up front** (`start`), only the prelude's front: the input's own copy of
  each prelude declaration (its group, with its dependencies), else the
  prelude's, folded first, as `Frontend.preparePrelude` puts them first.
  The evidence is given (`Ix.RoleEvidence.bundleEvidence` in the drivers).

So the cost scales with what is asked, not with the library
(`auxgen-flat-initstd`: every inductive block of Init+Std, and what its
groups depend on, is about 7 % of Init+Std's groups).

* **Flat blocks** (`Service.installFlat`): the canonical flat block of a
  block, lowered as the Source ingress lowers an inductive group
  (`inductiveGroup`, `convert`, `lower`) against the reader's state, after
  the groups it references, and installed with its σ (`SourceEnv.install`).
  A refused flat block leaves σ as it was: queries about that block keep
  Lean's names and fail closed there.
* **Generated definitions** (`Service.admitDefinition`): the groups they
  reference folded, then `SourceEnv.admitDefinition`.

## In the compile drivers (AuxGen M2b)

The wave fold (`Ix.CompileM.compileEnvFoldWithSource`) runs the service
**ahead of the waves** (`RunAhead`): from the start, on a dedicated thread,
it asks level by level of the fold's schedule for the blocks with a
Type-level `.below` (`Asks.below`, `holdsTypeBelow`: the blocks whose tails
ask IxC), and publishes the run after each level. Each such block's aux tail
asks `.below`'s level questions of IxC over its level's snapshot
(`Ix.AuxGen.Oracle`, `Ix.AuxGen.Ixc`); the fold joins the run-ahead at its
end and reports what Source mode accepted (`Report`). (AuxGen M1 asked for
every block that holds an inductive, on a task chain driven by the waves,
and no tail read it.)

## What it is not

Not a verdict: `Ix.LeanIngress.checkSource` is. The groups the ingress
declines for their safety (`partial` and unsafe definitions, unsafe opaques
and axioms, unsafe inductives) are installed by the typing tier
(`SourceEnv.installTierDecl`, `installTierInd`, at the views of Lean's
lattice), to answer an unsafe block's questions (M7 Q1). Their status is
`tier`, never `accepted`; a logical group that depends on one is blocked, as
it was behind the decline. Nothing here is trusted: every declaration it
installs went through the verified fold or the tier's checks, and an answer
it cannot give is a refusal. -/

namespace Ix.AuxGen.Source

open Ix.LeanIngress
open Ix.Kernel.Reader (State Read CDecl CName ReadError Prelude)
open Ix.Kernel.Tier (TierDecl TierInd)
open Ix.AuxGen.Flat (NameKey ClassMap FlatBlock FlatError)

def renderRead : ReadError → String
  | .malformed m => s!"ingress: malformed: {m}"
  | .declined m => s!"ingress: declined: {m}"

/-- A declaration group's state in the service. -/
inductive Status where
  /-- met, not folded yet -/
  | pending
  | accepted
  /-- the ingress or the fold refused it -/
  | refused (reason : String)
  /-- a group it depends on is refused (`root`, by group index) -/
  | blocked (root : Nat)
  /-- installed by the typing tier (M7 Q1), with its safety: no verdict -/
  | tier (safety : String)
  deriving Inhabited, BEq

def Status.isAccepted : Status → Bool
  | .accepted => true
  | _ => false

def Status.isTier : Status → Bool
  | .tier _ => true
  | _ => false

def Status.isPending : Status → Bool
  | .pending => true
  | _ => false

/-- An installed (or refused) flat block. -/
structure FlatRecord where
  /-- the block's first member, fresh -/
  name : Name
  status : Status

/-! ## The input -/

/-- What the service reads of the compiler's input: constants by name and the
condensation. -/
structure Input where
  get? : Ix.Name → Option Ix.ConstantInfo
  blocks : Ix.CondensedBlocks

instance : Inhabited Input := ⟨{ get? := fun _ => none, blocks := default }⟩

namespace Input

/-- The constants of `names` the input has, as an environment (the grouping
functions read `env.consts`). -/
def envOf (inp : Input) (names : Array Ix.Name) : Ix.Environment :=
  { consts := names.foldl (init := {}) fun m n =>
      match inp.get? n with
      | some ci => m.insert n ci
      | none => m }

/-- The recursors naming the inductive block whose first member is `first`,
as `groupsOf` collects them for `blockRecursors`: those of `T.rec` (each
member `T`) and `first.rec_j` (`j = 1 … numNested`) that the input has as
recursors of this block. -/
def recursorsOf (inp : Input) (first : Ix.InductiveVal) : Array Ix.RecursorVal :=
  let names := first.all.map (Ix.Name.mkStr · "rec") ++
    (Array.range first.numNested).map fun j => Ix.Name.mkStr first.cnst.name s!"rec_{j + 1}"
  names.filterMap fun n => match inp.get? n with
    | some (.recInfo rv) =>
      if (rv.all[0]?.map (·.beqRaw first.cnst.name)).getD false then some rv else none
    | _ => none

/-- The group of the inductive block whose first member is `first`
(`inductiveGroup` over the block's members and their constructors). -/
def inductiveGroupOf (inp : Input) (first : Ix.InductiveVal) : Group :=
  let ctors := first.all.flatMap fun n => match inp.get? n with
    | some (.inductInfo v) => v.ctors
    | _ => #[]
  inductiveGroup (inp.envOf (first.all ++ ctors)) first (inp.recursorsOf first)

/-- The group of the inductive block `ind` belongs to: `groupsOf` makes one
for each inductive that heads its own `all`. -/
def blockGroupOf? (inp : Input) (ind : Ix.Name) : Option Group :=
  match inp.get? ind with
  | some (.inductInfo v) =>
    match v.all[0]? with
    | some first =>
      match inp.get? first with
      | some (.inductInfo fv) =>
        if (fv.all[0]?.map (·.beqRaw first)).getD false then some (inp.inductiveGroupOf fv)
        else none
      | _ => none
    | none => none
  | _ => none

/-- **The group claiming `n`** (whose constant is `ci`), as `groupsOf` places
it: an inductive family member in its block's group, any other constant in
its condensation component's group, and a constant neither claims in a group
of its own that fails with the reader's reason (`unplaced`). -/
def groupFor (inp : Input) (n : Ix.Name) (ci : Ix.ConstantInfo) : Group :=
  let claiming (g : Option Group) : Group :=
    match g with
    | some g => if g.names.any (·.beqRaw n) then g else unplaced n ci
    | none => unplaced n ci
  match ci with
  | .inductInfo _ => claiming (inp.blockGroupOf? n)
  | .ctorInfo cv => claiming (inp.blockGroupOf? cv.induct)
  | .recInfo rv => claiming (rv.all[0]?.bind inp.blockGroupOf?)
  | _ =>
    match (inp.blocks.lowLinks.get? n).bind inp.blocks.blocks.get? with
    | some members =>
      -- `n`'s constant is `ci`: not looked up again (under a lookup view a
      -- theorem's body would be canonicalized again)
      let others := inp.envOf (members.toArray.filter (!·.beqRaw n))
      claiming (componentGroup { others with consts := others.consts.insert n ci } members)
    | none => unplaced n ci

end Input

/-- A checker name as the environment spells it (`ingressName`'s inverse). -/
def ixName : Ix.Kernel.Name → Ix.Name
  | .anonymous => Ix.Name.mkAnon
  | .str p s => Ix.Name.mkStr (ixName p) s
  | .num p i => Ix.Name.mkNat (ixName p) i

/-- The Lean name a Source key spells: an input key's own, a role key's
role's (Source mode binds role `r` to the constant named `r.leanName`); a
derived key spells none. -/
def nameOfKey : CName .source → Option Ix.Name
  | .id i => some (ixName i)
  | .role r => some (ixName r.leanName)
  | .aux .. => none

/-! ## The service -/

/-- **A tier group's conversion** (M7 Q1): a tier declaration with its
members' hints (`convertTier`), or an unsafe inductive block
(`convertTierInductive`). -/
inductive TierItem where
  | decl (d : TierDecl .source) (hints : List Ix.Kernel.ReducibilityHint)
  | ind (b : TierInd .source)

/-- The terms of a tier group, for its literal edges. -/
def TierItem.exprs : TierItem → List (Ix.Kernel.Expr .source)
  | .decl (.defs _ ms) _ => ms.flatMap fun (cv, v) => [cv.type, v]
  | .decl (.unsafeOpaque cv v) _ => [cv.type, v]
  | .decl (.unsafeAxiom cv) _ => [cv.type]
  | .ind b => b.types.map (·.1.type) ++ b.ctors.map (·.1.type) ++
      b.recs.flatMap fun (cv, _, rules) => cv.type :: rules.map (·.rhs)

/-- A group's conversion: the Source ingress's, or the tier's. -/
inductive Conv where
  | logical (c : Converted)
  | tier (t : TierItem)

/-- **A group's conversion in the service**: a tier group (`isTierGroup`,
`isTierInductive`) by the tier's conversion, any other by the ingress's. -/
def convertGroup (g : Group) : Except ReadError Conv :=
  if isTierGroup g then do
    let hints := match g with
      | .definitions ms => ms.toList.map fun ci => ((definitionShape ci).map (·.2.2)).getD (.regular 0)
      | _ => []
    return .tier (.decl (← convertTier g) hints)
  else match g with
    | .inductive ts cs rs =>
      if isTierInductive g then return .tier (.ind (← convertTierInductive ts cs rs))
      else .logical <$> convert g
    | _ => .logical <$> convert g

/-- Whether a conversion's terms contain a `Nat` and a `String` literal
(`literalKinds`, each tier term on its own). -/
def Conv.literalKinds : Conv → Bool × Bool
  | .logical c => Ix.LeanIngress.literalKinds c
  | .tier t => t.exprs.foldl (init := (false, false)) fun (n, s) e =>
    let (n', s') := Ix.LeanIngress.literalKinds (.axiom ⟨.id .anonymous, [], e⟩)
    (n || n', s || s')

/-- A group's reading: lowered once the groups it references are, dropped
once folded; a tier group's is its conversion. -/
inductive Reading where
  | pending
  | lowered (r : Read .source)
  | tier (t : TierItem)
  | refused (e : ReadError)
  | folded

def Reading.isPending : Reading → Bool
  | .pending => true
  | _ => false

/-- What the order needs of a group, computed when the group is first
visited (`graphOf`'s, for one group): the groups its constants reference
(`hard`, from the condensation's `blockRefs`), the groups of the constants
its literals reference (`literal`), and a reference it cannot place. -/
structure Edges where
  hard : Array Nat
  literal : Array Nat
  unplaced : Option ReadError

/-- A declaration group the service has met. -/
structure Entry where
  /-- the constants it declares (`Group.names`) -/
  names : Array Ix.Name
  /-- the group, until it is converted -/
  group : Option Group
  /-- its conversion, until it is lowered -/
  converted : Option (Except ReadError Conv) := none
  edges : Option Edges := none
  reading : Reading := .pending
  /-- the groups the `Nat` operations it declares stand on (`natOpDeps`) -/
  ground : Array Nat := #[]
  status : Status := .pending

instance : Inhabited Entry := ⟨{ names := #[], group := none }⟩

/-- The name a group is reported under: its first constant's
(`Group.name`). -/
def Entry.name (e : Entry) : CName .source :=
  match e.names[0]? with
  | some n => ingressKey n
  | none => .id .anonymous

/-- **The Source service environment.** -/
structure Service where
  input : Input
  /-- the groups met so far, in the order met -/
  entries : Array Entry := #[]
  /-- the group claiming each Lean name met so far -/
  groupOf : Std.HashMap NameKey Nat := {}
  /-- the groups of the constants a `Nat` literal references -/
  natTargets : Array Nat := #[]
  /-- the groups of the constants a `String` literal references -/
  strTargets : Array Nat := #[]
  /-- the reader's state after every lowered group and installed flat block -/
  reader : State .source
  /-- the checked half: the fold, the evidence, σ -/
  env : SourceEnv
  flats : Array FlatRecord := #[]
  /-- the prelude declarations no group of the input declares, folded from
  the prelude itself -/
  synthesised : Nat := 0

instance : Inhabited Service := ⟨{ input := default, reader := {}, env := {} }⟩

namespace Service

/-! The functions below that change a large field take the service apart
first (`let { … } := s`), so that the field they change is not shared with
the service they were given and is changed in place (README §6 item 22). -/

/-- σ of everything installed. -/
def sigma (s : Service) : ClassMap := s.env.sigma

/-- `groups.map convert`, on `workers` tasks. -/
def convertAll (groups : Array Group) (workers : Nat) : Array (Except ReadError Converted) :=
  if workers ≤ 1 then groups.map convert else
  let size := max ((groups.size + workers - 1) / workers) 1
  let chunks := (Array.range ((groups.size + size - 1) / size)).map fun k =>
    groups.extract (k * size) ((k + 1) * size)
  let tasks := chunks.map fun chunk => Task.spawn fun _ => chunk.map convert
  tasks.flatMap Task.get

/-- Entry `i` changed in place. -/
@[inline] def modifyEntry (s : Service) (i : Nat) (f : Entry → Entry) : Service :=
  let ⟨input, entries, groupOf, natTargets, strTargets, reader, env, flats, synthesised⟩ := s
  ⟨input, entries.modify i f, groupOf, natTargets, strTargets, reader, env, flats, synthesised⟩

/-- The reader's state after a reading. -/
def commit (s : Service) (r : Read .source) : Service :=
  let ⟨input, entries, groupOf, natTargets, strTargets, reader, env, flats, synthesised⟩ := s
  ⟨input, entries, groupOf, natTargets, strTargets, reader.commit r, env, flats, synthesised⟩

/-- **Meet the group claiming `n`**: its index, or none if the input has no
constant `n`. -/
def discover (s : Service) (n : Ix.Name) : Option Nat × Service :=
  match s.groupOf.get? ⟨n⟩ with
  | some i => (some i, s)
  | none =>
    match s.input.get? n with
    | none => (none, s)
    | some ci =>
      let g := s.input.groupFor n ci
      let ⟨input, entries, groupOf, natTargets, strTargets, reader, env, flats, synthesised⟩ := s
      let i := entries.size
      let names := g.names
      let groupOf := names.foldl (init := groupOf) fun m k =>
        if m.contains ⟨k⟩ then m else m.insert ⟨k⟩ i
      let entry : Entry := { names := names, group := some g }
      (some i, ⟨input, entries.push entry, groupOf, natTargets, strTargets, reader, env, flats,
        synthesised⟩)

/-- The group of the constant a key spells, met now if it was not. -/
def discoverKey (s : Service) (k : CName .source) : Option Nat × Service :=
  match nameOfKey k with
  | some n => s.discover n
  | none => (none, s)

/-- The groups of the constants `keys` spell, in order, each once. -/
def discoverKeys (s : Service) (keys : List (CName .source)) : Array Nat × Service :=
  keys.foldl (init := (#[], s)) fun (out, s) k =>
    match s.discoverKey k with
    | (some j, s) => (if out.contains j then out else out.push j, s)
    | (none, s) => (out, s)

def isPendingReading (s : Service) (i : Nat) : Bool :=
  (s.entries[i]?.map (·.reading.isPending)).getD false

def isPendingStatus (s : Service) (i : Nat) : Bool :=
  (s.entries[i]?.map (·.status.isPending)).getD false

/-- `is` in descending Lean name order of their groups (`namesLt`), so that a
stack pops them in ascending order. -/
def byNameDesc (s : Service) (is : Array Nat) : Array Nat :=
  let names (i : Nat) : Array Ix.Name := (s.entries[i]?.map (·.names)).getD #[]
  is.qsort fun a b => namesLt (names b) (names a)

/-- Group `i`'s conversion and edges, computed (and the groups they reach
met) if they were not; the group itself is dropped. -/
def prepare (s : Service) (i : Nat) : Service := Id.run do
  let some e := s.entries[i]? | return s
  if e.edges.isSome then return s
  let converted := match e.group with
    | some g => convertGroup g
    | none => .error (.malformed "group dropped before its conversion")
  let mut s := s
  let mut seenLo : Ix.Set Ix.Name := {}
  let mut hard : Std.HashSet Nat := {}
  let mut bad : Option ReadError := none
  for n in e.names do
    match s.input.blocks.lowLinks.get? n with
    | none =>
      if bad.isNone then
        bad := some (.malformed s!"constant {ingressName n} is not in the condensation")
    | some lo =>
      if seenLo.contains lo then continue
      seenLo := seenLo.insert lo
      for r in (s.input.blocks.blockRefs.get? lo).getD {} do
        let (j?, s') := s.discover r
        s := s'
        match j? with
        | some j => if j != i then hard := hard.insert j
        | none =>
          if bad.isNone then
            bad := some (.malformed s!"references {ingressName r}, which is not in the environment")
  let literal := match converted with
    | .ok c =>
      let (nat, str) := c.literalKinds
      (if str then s.strTargets else if nat then s.natTargets else #[]).filter (· != i)
    | .error _ => #[]
  let edges : Edges := { hard := hard.toArray.qsort (· < ·), literal, unplaced := bad }
  return s.modifyEntry i fun e =>
    { e with group := none, converted := some converted, edges := edges }

/-- The groups group `i` must be lowered after: hard and literal edges. -/
def lowerDeps (s : Service) (i : Nat) : Array Nat :=
  match s.entries[i]?.bind (·.edges) with
  | some ed => ed.hard ++ ed.literal
  | none => #[]

/-- The groups group `i` must be folded after: hard and literal edges and
the ground of the `Nat` operations it declares. -/
def deps (s : Service) (i : Nat) : Array Nat :=
  match s.entries[i]? with
  | some e => ((s.lowerDeps i) ++ e.ground).filter (· != i)
  | none => #[]

/-- Lower group `i`, prepared, whose references are lowered (one still being
visited is a cycle), against the reader's state, and commit what it taught;
then meet the ground of the `Nat` operations it declares. A tier group is
not lowered: its reading is its conversion, behind the same placement
checks. -/
def lowerOne (s : Service) (i : Nat) : Service := Id.run do
  let some e := s.entries[i]? | return s
  unless e.reading.isPending do return s
  let some ed := e.edges | return s
  let result : Except ReadError (Read .source ⊕ TierItem) := do
    let c ← e.converted.getD (.error (.malformed "group not converted"))
    if let some err := ed.unplaced then throw err
    unless ed.hard.all (!s.isPendingReading ·) do
      throw (.malformed "a reference cycle through another declaration group")
    match c with
    | .logical c => .inl <$> lower s.reader c
    | .tier t => pure (.inr t)
  match result with
  | .error err =>
    return s.modifyEntry i fun e => { e with converted := none, reading := .refused err }
  | .ok (.inr t) => return s.modifyEntry i fun e => { e with converted := none, reading := .tier t }
  | .ok (.inl r) =>
    let mut s := s.commit r
    let mut ground : Array Nat := #[]
    for d in r.decls do
      if let some c := Ix.Kernel.Frontend.isNatOpRecord d then
        for k in Ix.Kernel.natOpDeps c do
          let (j?, s') := s.discoverKey k
          s := s'
          if let some j := j? then
            if j != i && !ground.contains j then ground := ground.push j
    return s.modifyEntry i fun e =>
      { e with converted := none, reading := .lowered r, ground := ground }

/-- **Lower group `root`** after every group it references, depth first in
postorder, successors in Lean's name order. -/
def lowerClosure (s : Service) (root : Nat) : Service := Id.run do
  let mut s := s
  let mut active : Std.HashSet Nat := {}
  let mut stack : Array (Nat × Bool) := #[(root, false)]
  while h : stack.size > 0 do
    let (node, expanded) := stack[stack.size - 1]
    stack := stack.pop
    if expanded then
      active := active.erase node
      s := s.lowerOne node
    else if s.isPendingReading node && !active.contains node then
      active := active.insert node
      s := s.prepare node
      stack := stack.push (node, true)
      -- pushed last-first, so that they are visited first-first
      for d in s.byNameDesc (s.lowerDeps node) do
        if s.isPendingReading d && !active.contains d then stack := stack.push (d, false)
  return s

/-- Fold group `i`, whose dependencies are folded: blocked if one failed,
refused if the ingress refused it or the fold refuses one of its
declarations (the fold then stays as before the group), accepted
otherwise. A tier group is installed by the tier (`tier`, or refused), and
may depend on tier groups; a logical group behind a tier group is blocked.
A group already folded is left as it is; its reading is dropped either way. -/
def foldGroup (s : Service) (i : Nat) : Service :=
  match s.entries[i]? with
  | none => s
  | some e =>
    if !e.status.isPending then s else
    let tierOk := e.reading matches .tier _
    let failed := (s.deps i).find? fun j =>
      !((s.entries[j]?.map fun d => d.status.isAccepted || (tierOk && d.status.isTier)).getD false)
    match failed with
    | some j =>
      let root := match s.entries[j]?.map (·.status) with
        | some (.blocked r) => r
        | _ => j
      s.modifyEntry i fun e => { e with status := .blocked root, reading := .folded }
    | none =>
      match e.reading with
      | .lowered r =>
        let ⟨input, entries, groupOf, natTargets, strTargets, reader, env, flats, synthesised⟩ := s
        let ⟨fold, ev, sigma, tier⟩ := env
        let (fold, err) := fold.stepsOwned ev r.decls
        let status : Status := match err with
          | none => .accepted
          | some e => .refused (renderCheck e)
        let entries := entries.modify i fun e => { e with status := status, reading := .folded }
        ⟨input, entries, groupOf, natTargets, strTargets, reader, ⟨fold, ev, sigma, tier⟩, flats,
          synthesised⟩
      | .tier t =>
        let installed := match t with
          | .decl d hints => (s.env.installTierDecl d hints).map (·, d.safety.word)
          | .ind b => (s.env.installTierInd b).map (·, "unsafe")
        match installed with
        | .ok (env, word) =>
          let s := s.modifyEntry i fun e => { e with status := .tier word, reading := .folded }
          { s with env }
        | .error why => s.modifyEntry i fun e => { e with status := .refused why, reading := .folded }
      | .refused err =>
        s.modifyEntry i fun e => { e with status := .refused (renderRead err), reading := .folded }
      | _ => s

/-- **Fold group `root` and everything it depends on**, depth first, in
postorder, successors in Lean's name order; each group is lowered (with what
it references) when it is first visited. -/
def ensure (s : Service) (root : Nat) : Service := Id.run do
  let mut s := s
  let mut active : Std.HashSet Nat := {}
  let mut stack : Array (Nat × Bool) := #[(root, false)]
  while h : stack.size > 0 do
    let (node, expanded) := stack[stack.size - 1]
    stack := stack.pop
    if expanded then
      active := active.erase node
      s := s.foldGroup node
    else if s.isPendingStatus node && !active.contains node then
      active := active.insert node
      s := s.lowerClosure node
      stack := stack.push (node, true)
      -- pushed last-first, so that they are visited first-first
      for d in s.byNameDesc (s.deps node) do
        if s.isPendingStatus d && !active.contains d then stack := stack.push (d, false)
  return s

/-- The group claiming a Lean name, if it has been met. -/
def groupOfName? (s : Service) (n : Name) : Option Nat := s.groupOf.get? ⟨n⟩

/-- **Fold the groups claiming `names`**, with their dependencies. -/
def ensureNames (s : Service) (names : Array Name) : Service :=
  names.foldl (init := s) fun s n =>
    match s.discover n with
    | (some i, s) => s.ensure i
    | (none, s) => s

/-- The state of the group claiming a Lean name, if it has been met. -/
def statusOf? (s : Service) (n : Name) : Option Status := do
  (← s.entries[← s.groupOfName? n]?).status

/-- The first of `names` whose group Source mode did not accept. -/
def firstUnaccepted? (s : Service) (names : Array Name) : Option Name :=
  names.find? fun n => !((s.statusOf? n).map (·.isAccepted)).getD true

/-- The first of `names` whose group is neither accepted nor tier-installed:
what a tier install may not reference. -/
def firstUnusable? (s : Service) (names : Array Name) : Option Name :=
  names.find? fun n => !((s.statusOf? n).map fun st => st.isAccepted || st.isTier).getD true

/-- **Whether a block is tier-installed** (M7 Q1): every one of its members'
groups is. -/
def tierBlock (s : Service) (members : Array Name) : Bool :=
  !members.isEmpty && members.all fun n => (s.statusOf? n).any (·.isTier)

/-- Whether group `i`'s reading declares the key `k`. -/
def declares (s : Service) (i : Nat) (k : CName .source) : Bool :=
  match s.entries[i]? with
  | some e =>
    match e.reading with
    | .lowered r => r.decls.any (·.names.contains k)
    | _ => false
  | none => false

/-- **The service over an input**, behind the prelude `pre`, at the evidence
`ev`: the groups of the constants literals reference met, and the prelude's
front folded: the input's own copy of each prelude declaration (its group,
with its dependencies, if its reading declares it), else the prelude's.
Nothing else is met or folded yet. -/
def start (pre : Prelude .source) (input : Input) (ev : Ix.Kernel.Evidences .source) :
    Service := Id.run do
  let s : Service := { input := input, reader := pre.state, env := { ev := ev } }
  let (natTargets, s) := s.discoverKeys Ix.Kernel.Reader.natLitSupportNames
  let (strTargets, s) := s.discoverKeys Ix.Kernel.Reader.strLitSupportNames
  let mut s := { s with natTargets, strTargets }
  for p in pre.ix.decls do
    let mut own : Option Nat := none
    if let some k := Ix.Kernel.Frontend.preludeKey p then
      let (i?, s') := s.discoverKey k
      s := s'
      if let some i := i? then
        s := s.lowerClosure i
        if s.declares i k then own := some i
    match own with
    | some i => s := s.ensure i
    | none =>
      let ⟨input, entries, groupOf, natTargets, strTargets, reader, env, flats, synthesised⟩ := s
      let ⟨fold, ev, sigma, tier⟩ := env
      let (fold, err) := fold.stepsOwned ev #[p]
      let synthesised := if err.isNone then synthesised + 1 else synthesised
      s := ⟨input, entries, groupOf, natTargets, strTargets, reader, ⟨fold, ev, sigma, tier⟩, flats,
        synthesised⟩
  return s

/-- Source mode's evidence from the input itself, as `checkSource` takes it:
`sourceEvidence` over the whole ingress of `env` (every group lowered in the
Source order, conversions on `workers` tasks). It reads `env.consts`: for
tests over a materialized input; the drivers give the committed bundle's. -/
def inputEvidence (pre : Prelude .source) (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (workers : Nat) : Ix.Kernel.Evidences .source := Id.run do
  let groups := groupsOf env blocks
  let g := graphOf blocks groups (convertAll groups workers)
  let mut st := pre.state
  let mut lowered : Array Decl := #[]
  for (_, c) in scheduleOf g do
    match c >>= lower st with
    | .ok r =>
      st := st.commit r
      lowered := lowered ++ r.decls
    | .error _ => pure ()
  return sourceEvidence (Ix.Kernel.Frontend.preparePrelude pre.ix lowered)

/-- **The service over a materialized input** (`env` under its condensation
`blocks`) behind the prelude `pre`, at the evidence `evidence`, else the
input's own (`inputEvidence`, conversions on `workers` tasks). -/
def create (pre : Prelude .source) (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (workers : Nat := 1) (evidence : Option (Ix.Kernel.Evidences .source) := none) : Service :=
  let ev := match evidence with
    | some ev => ev
    | none => inputEvidence pre env blocks workers
  start pre { get? := env.get?, blocks := blocks } ev

/-! ## Flat blocks -/

/-- The Lean names a flat block references outside itself, in Lean's name
order. -/
def flatRefs (b : FlatBlock) : Array Name := Id.run do
  let mut out : Std.HashSet Name := {}
  for v in b.types do out := collectLeanConstRefs v.cnst.type out
  for cs in b.ctors do
    for c in cs do out := collectLeanConstRefs c.cnst.type out
  for r in b.recs do
    out := collectLeanConstRefs r.cnst.type out
    for rule in r.rules do out := collectLeanConstRefs rule.rhs out
  return (out.toArray.filter (!Flat.isFresh ·)).qsort (nameCmp · · == .lt)

/-- **Install a canonical flat block**: the groups it references folded
first, then the block lowered as the Source ingress lowers an inductive
group, against the reader's state, and installed with its σ
(`SourceEnv.install`). The outcome is recorded (`flats`); a refusal leaves
the environment and σ as they were. With `tier` (an unsafe block's, M7 Q1)
the block is installed typing only (`SourceEnv.installTierInd`), its
references accepted or tier-installed, and recorded `tier`. -/
def installFlat (s : Service) (b : FlatBlock) (tier : Bool := false) : Service := Id.run do
  let some first := b.types[0]? | return s
  let record (st : Status) (s : Service) : Service :=
    { s with flats := s.flats.push ⟨first.cnst.name, st⟩ }
  let refs := flatRefs b
  let s := s.ensureNames refs
  if let some n := if tier then s.firstUnusable? refs else s.firstUnaccepted? refs then
    return record (.refused s!"references {n.pretty}, which Source mode did not accept") s
  let env : Ix.Environment := { consts := b.consts.foldl (fun m (n, c) => m.insert n c) {} }
  if tier then
    let installed := match inductiveGroup env first b.recs with
      | .inductive ts cs rs => (convertTierInductive ts cs rs).mapError renderRead >>=
          (s.env.installTierInd · b.sigma)
      | _ => .error "tier: the flat block is not an inductive group"
    return match installed with
      | .ok env' => record (.tier "unsafe") { s with env := env' }
      | .error why => record (.refused why) s
  match convert (inductiveGroup env first b.recs) >>= lower s.reader with
  | .error e => return record (.refused (renderRead e)) s
  | .ok r =>
    match s.env.install r.decls b.sigma with
    | .ok env' => return record .accepted { s with env := env', reader := s.reader.commit r }
    | .error why => return record (.refused why) s

/-- The state of the flat block installed under a fresh first member. -/
def flatStatus? (s : Service) (first : Name) : Option Status :=
  (s.flats.find? fun r => Ix.Compile.ExactKey.nameEq r.name first).map (·.status)

/-! ## Generated definitions -/

/-- **Admit a generated definition** (or theorem, `thm`): the groups it
references (outside σ) folded first, then `SourceEnv.admitDefinition`. The
service after it, and the verdict. With `tier` (an unsafe block's, M7 Q1),
by the tier (`SourceEnv.admitTierDefinition`), its references accepted or
tier-installed, and the verdict `tier`. -/
def admitDefinition (s : Service) (name : Name) (lps : Array Name) (type value : Expr)
    (thm : Bool) (hint : Ix.Kernel.ReducibilityHint := .abbrev) (tier : Bool := false) :
    Service × Status :=
  let refs := ((collectLeanConstRefs value (collectLeanConstRefs type {})).toArray.filter
    fun n => (s.sigma.find? n).isNone && !Flat.isFresh n).qsort (nameCmp · · == .lt)
  let s := s.ensureNames refs
  match if tier then s.firstUnusable? refs else s.firstUnaccepted? refs with
  | some n => (s, .refused s!"references {n.pretty}, which Source mode did not accept")
  | none =>
    let admitted := if tier then s.env.admitTierDefinition name lps type value thm hint
      else s.env.admitDefinition name lps type value thm hint
    match admitted with
    | .ok env' => ({ s with env := env' }, if tier then .tier "unsafe" else .accepted)
    | .error why => (s, .refused why)

/-! ## Counts and views -/

/-- The groups met, by state: pending, accepted, refused, blocked (a
tier-installed group is in none: `tierCount`). -/
def counts (s : Service) : Nat × Nat × Nat × Nat :=
  s.entries.foldl (init := (0, 0, 0, 0)) fun (p, a, r, b) e => match e.status with
    | .pending => (p + 1, a, r, b)
    | .accepted => (p, a + 1, r, b)
    | .refused _ => (p, a, r + 1, b)
    | .blocked _ => (p, a, r, b + 1)
    | .tier _ => (p, a, r, b)

/-- The groups met that the tier installed (M7 Q1). -/
def tierCount (s : Service) : Nat := s.entries.foldl (init := 0) fun n e =>
  if e.status.isTier then n + 1 else n

/-- Each met group's state, by index. -/
def status (s : Service) : Array Status := s.entries.map (·.status)

/-- The groups met, by index (`graph.groups[i]!.name` names one). -/
structure Met where
  groups : Array Entry

def graph (s : Service) : Met := ⟨s.entries⟩

end Service

/-! ## The drivers' service (AuxGen M1)

What the compile drivers carry: the service over their input at the committed
bundle's evidence, asked for every block that holds an inductive, and a
report of Source mode's answers. -/

/-- Whether a condensation block holds an inductive, told without reading its
members: some member `T` has a recursor `T.rec` of its own block in the input.
Lean declares one with every inductive; a block whose inductives have none
is not a Source-mode inductive group either (`blockRecursors`). Reading a
member could canonicalize a theorem body under the drivers' lookup view;
`T.rec` is a recursor, materialized there, or absent. -/
def holdsInductive (get? : Ix.Name → Option Ix.ConstantInfo) (members : Array Ix.Name) : Bool :=
  members.any fun n => match get? (Ix.Name.mkStr n "rec") with
    | some (.recInfo rv) => rv.all.any (·.beqRaw n)
    | _ => false

/-- What Source mode said of the drivers' asks. -/
structure Report where
  /-- why there is no service (the committed prelude does not load) -/
  error : Option String := none
  /-- the blocks asked for (those that hold an inductive) -/
  blocks : Nat := 0
  /-- of those, the blocks whose own groups Source mode accepted -/
  accepted : Nat := 0
  /-- the groups met, and by state -/
  met : Nat := 0
  groupsAccepted : Nat := 0
  groupsRefused : Nat := 0
  groupsBlocked : Nat := 0
  /-- the groups the tier installed (M7 Q1: never accepted) -/
  groupsTier : Nat := 0
  /-- prelude declarations folded from the prelude itself -/
  synthesised : Nat := 0
  /-- the blocks not accepted, by canonical key, with the reason: the first
  `Report.cap` in Lean's name order -/
  notAccepted : Array (Ix.Name × String) := #[]
  /-- the groups refused, by name, with the reason: the first `Report.cap`
  by name -/
  refused : Array (String × String) := #[]
  deriving Inhabited, BEq

/-- How many blocks and groups a report names. -/
def Report.cap : Nat := 64

/-- One line (the tier's count only when the tier installed a group). -/
def Report.summary (r : Report) : String :=
  match r.error with
  | some e => s!"unavailable: {e}"
  | none =>
    let tier := if r.groupsTier == 0 then "" else s!", {r.groupsTier} tier-installed"
    s!"{r.accepted} of {r.blocks} inductive blocks accepted; groups met {r.met}: \
      {r.groupsAccepted} accepted, {r.groupsRefused} refused, {r.groupsBlocked} blocked{tier}; \
      prelude declarations synthesised {r.synthesised}"

/-- The drivers' service and what they asked. -/
structure Run where
  service : Except String Service
  /-- the blocks asked for -/
  blocks : Nat := 0
  accepted : Nat := 0
  /-- the blocks not accepted, by canonical key, with the reason -/
  notAccepted : Array (Ix.Name × String) := #[]

instance : Inhabited Run := ⟨{ service := .error "uninitialized" }⟩

namespace Run

/-- The service over the drivers' input, at the committed bundle's evidence
(`Ix.RoleEvidence.bundleEvidence`: the input need not carry the certificate
theorems). -/
def start (input : Input) : Run :=
  match Ix.Kernel.Reader.builtinPrelude (md := .source) with
  | .error e => { service := .error s!"the committed prelude does not load: {e}" }
  | .ok pre => { service := .ok (Service.start pre input (Ix.RoleEvidence.bundleEvidence ())) }

/-- Why a block's own groups are not accepted, if they are not. -/
def blockReason? (svc : Service) (members : Array Ix.Name) : Option String :=
  members.findSome? fun n => match svc.statusOf? n with
    | some (.refused why) => some why
    | some (.blocked root) =>
      some s!"blocked behind {(svc.entries[root]?.map (·.name)).getD (.id .anonymous)}"
    | some .pending => some "not folded"
    | some (.tier safety) => some s!"tier-installed ({safety})"
    | _ => none

/-- **Ask for blocks**, in order (key, representative, members): each block
that holds an inductive has its groups folded, with everything they depend
on. -/
def ask (r : Run) (ready : Array (Ix.Name × Ix.Name × Ix.Set Ix.Name)) : Run := Id.run do
  let ⟨service, blocks, accepted, notAccepted⟩ := r
  let .ok svc := service | return ⟨service, blocks, accepted, notAccepted⟩
  let mut svc := svc
  let mut blocks := blocks
  let mut accepted := accepted
  let mut notAccepted := notAccepted
  for (key, _, all) in ready do
    let members := all.toArray.qsort (nameCmp · · == .lt)
    unless holdsInductive svc.input.get? members do continue
    svc := svc.ensureNames members
    blocks := blocks + 1
    match blockReason? svc members with
    | none => accepted := accepted + 1
    | some why => notAccepted := notAccepted.push (key, why)
  return ⟨.ok svc, blocks, accepted, notAccepted⟩

/-- The report. -/
def report (r : Run) : Report :=
  match r.service with
  | .error e => { error := some e }
  | .ok svc =>
    let (_, a, f, b) := svc.counts
    let notAccepted := (r.notAccepted.qsort fun x y => nameCmp x.1 y.1 == .lt).extract 0 Report.cap
    let refused := (svc.entries.filterMap fun e => match e.status with
      | .refused why => some (toString e.name, why)
      | _ => none).qsort (·.1 < ·.1) |>.extract 0 Report.cap
    { blocks := r.blocks, accepted := r.accepted, met := svc.entries.size, groupsAccepted := a,
      groupsRefused := f, groupsBlocked := b, groupsTier := svc.tierCount, synthesised := svc.synthesised,
      notAccepted := notAccepted, refused := refused }

end Run

/-! ## The run-ahead (AuxGen M2a; the drivers' since M2b)

M2's aux tails read the service, so its asks cannot wait for the waves: a
wave's tails would wait for that wave's asks, and the waves would run at the
service's pace plus the tails' (auxgen-m2.md §2). The asks depend only on the
input and the condensation, so the run-ahead makes them from the start, one
level of the fold's schedule at a time (`levels`: the blocks whose
source-owned dependencies are in earlier levels, in key order), on a
dedicated thread, and publishes the run after each level. A block's tail
reads the run of its level, which holds its groups and everything they
depend on: a function of the input and the condensation, not of timing or
of the waves' width. One snapshot per level, not per block: each snapshot
handed out costs the next ask one copy of the fold's index (a task's value is
shared, and `Std.HashMap.insert` copies a shared map). -/

/-- Which blocks the run-ahead asks for. -/
inductive Asks where
  /-- every block that holds an inductive (M1's asks) -/
  | inductive
  /-- the blocks with a Type-level `.below` family, the ones M2's IxC arm asks
  about (lever P2) -/
  | below
  /-- AuxGen M4: the blocks with a Type-level `.below`, and those the recursor
  generator or the elimination decision can ask past the fast paths
  (`Ix.AuxGen.Ixc.recursorsMayAsk`) -/
  | recursors
  deriving BEq, Inhabited, Repr

/-- Whether a block has a Type-level `.below` family in the input: a member
`T` whose `T.below` is a definition, or whose `T.below_1` is (a nested
auxiliary's, hung off Lean's first member). -/
def holdsTypeBelow (get? : Ix.Name → Option Ix.ConstantInfo) (members : Array Ix.Name) : Bool :=
  let isDefn (n : Ix.Name) : Bool := match get? n with
    | some (.defnInfo _) => true
    | _ => false
  members.any fun n => isDefn (Ix.Name.mkStr n "below") || isDefn (Ix.Name.mkStr n "below_1")

/-- **Whether `asks` selects a block** (`members` sorted by name), beyond holding
an inductive. -/
def Asks.selects (asks : Asks) (get? : Ix.Name → Option Ix.ConstantInfo)
    (members : Array Ix.Name) : Bool :=
  match asks with
  | .inductive => true
  | .below => holdsTypeBelow get? members
  | .recursors => holdsTypeBelow get? members || Ixc.recursorsMayAsk get? members

namespace Run

/-- `ask`, asking only for the blocks `asks` selects. -/
def askWhere (asks : Asks) (r : Run) (ready : Array (Ix.Name × Ix.Name × Ix.Set Ix.Name)) : Run :=
  match asks, r.service with
  | .inductive, _ => r.ask ready
  | _, .ok svc =>
    r.ask (ready.filter fun (_, _, all) =>
      asks.selects svc.input.get? (all.toArray.qsort (nameCmp · · == .lt)))
  | _, .error _ => r

end Run

/-- The constants AuxGen's `.below` names besides a block's own: `PUnit` and
`PProd`, which `Ix.Tc`'s bridge admits by hand (`ensurePreludeInKenvOf`). The
run-ahead folds their groups first, so every snapshot holds them. -/
def auxPreludeNames : Array Ix.Name :=
  #[Ix.Name.mkStr .mkAnon "PUnit", Ix.Name.mkStr .mkAnon "PProd"]

/-- The run with the groups claiming `names` folded, with their dependencies. -/
def Run.ensureNames (r : Run) (names : Array Ix.Name) : Run :=
  { r with service := r.service.map (·.ensureNames names) }

/-- **The service run ahead of the waves**: the run before any ask, then the
run after each level's asks. -/
structure RunAhead where
  /-- `levels[0]` before any ask; `levels[i + 1]` after level `i`'s -/
  levels : Array (Task Run)
  /-- each block's level and members, by canonical key -/
  levelOf : Std.HashMap NameKey (Nat × Ix.Set Ix.Name)

instance : Inhabited RunAhead := ⟨{ levels := #[], levelOf := {} }⟩

namespace RunAhead

/-- Start the service over the input (`get?`, the condensation), fold
`auxPreludeNames`, and ask, on a dedicated thread, level by level
(`(canonical key, representative, members)`, key order within a level), the
blocks `asks` selects. -/
def start (get? : Ix.Name → Option Ix.ConstantInfo) (blocks : Ix.CondensedBlocks)
    (levels : Array (Array (Ix.Name × Ix.Name × Ix.Set Ix.Name))) (asks : Asks) : RunAhead :=
  Id.run do
    let t₀ : Task Run :=
      Task.spawn (prio := .dedicated) fun _ =>
        (Run.start { get? := get?, blocks := blocks }).ensureNames auxPreludeNames
    let mut tasks : Array (Task Run) := #[t₀]
    let mut levelOf : Std.HashMap NameKey (Nat × Ix.Set Ix.Name) := {}
    let mut t := t₀
    for (level, i) in levels.zipIdx do
      t := t.map (prio := .dedicated) (·.askWhere asks level)
      tasks := tasks.push t
      for (key, _, all) in level do
        levelOf := levelOf.insert ⟨key⟩ (i, all)
    return { levels := tasks, levelOf }

/-- The run a block's tail reads: the run after its level's asks, by the
block's canonical key; `none` for a block the schedule does not place. -/
def runFor (ra : RunAhead) (key : Ix.Name) : Option (Task Run) := do
  let (i, _) ← ra.levelOf.get? ⟨key⟩
  ra.levels[i + 1]?

/-- A block's members (sorted by name), by its canonical key. -/
def membersFor (ra : RunAhead) (key : Ix.Name) : Array Ix.Name :=
  match ra.levelOf.get? ⟨key⟩ with
  | some (_, all) => all.toArray.qsort (nameCmp · · == .lt)
  | none => #[]

/-- Wait for every ask; the report. -/
def report (ra : RunAhead) : Report :=
  match ra.levels.back? with
  | some t => t.get.report
  | none => {}

end RunAhead

/-! ## The service measured (AuxGen M2a: levers P1 and P2)

`measure` times the run-ahead's work on the calling thread, in three ways:
* **as it runs**: every level's asks, each group lowered when first met and
  folded after what it depends on (`ensure`): the service's sequential time;
* **lowering, then folding**: the same groups lowered first, all of them
  (`lowerOnly`), then folded (`ensure`, whose lowering is then done): the
  lowering's share, which bounds what a two-stage pipeline (P1) can save;
* **the `.below` asks only** (P2), as it runs.
-/

namespace Service

/-- **Lower group `root` and everything `ensure root` would fold, folding
nothing**, in `ensure`'s first-visit order; `seen` carries the groups
visited by earlier calls. -/
def lowerOnly (s : Service) (seen : Std.HashSet Nat) (root : Nat) :
    Service × Std.HashSet Nat := Id.run do
  let mut s := s
  let mut seen := seen
  let mut stack : Array Nat := #[root]
  while h : stack.size > 0 do
    let node := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains node || !s.isPendingStatus node then continue
    seen := seen.insert node
    s := s.lowerClosure node
    -- pushed last-first, so that they are visited first-first
    for d in s.byNameDesc (s.deps node) do
      if !seen.contains d && s.isPendingStatus d then stack := stack.push d
  return (s, seen)

/-- `lowerOnly` for the groups claiming `names`. -/
def lowerNames (s : Service) (seen : Std.HashSet Nat) (names : Array Ix.Name) :
    Service × Std.HashSet Nat :=
  names.foldl (init := (s, seen)) fun (s, seen) n =>
    match s.discover n with
    | (some i, s) => s.lowerOnly seen i
    | (none, s) => (s, seen)

end Service

/-- The members of the blocks of `levels` that `asks` selects, in ask order. -/
def askedMembers (get? : Ix.Name → Option Ix.ConstantInfo) (asks : Asks)
    (levels : Array (Array (Ix.Name × Ix.Name × Ix.Set Ix.Name))) : Array (Array Ix.Name) :=
  levels.foldl (init := #[]) fun out level =>
    level.foldl (init := out) fun out (_, _, all) =>
      let members := all.toArray.qsort (nameCmp · · == .lt)
      let take := holdsInductive get? members && asks.selects get? members
      if take then out.push members else out

/-- **The service's work timed** on this thread (AuxGen M2a; P1, P2): one
line per measurement. -/
def measure (get? : Ix.Name → Option Ix.ConstantInfo) (blocks : Ix.CondensedBlocks)
    (levels : Array (Array (Ix.Name × Ix.Name × Ix.Set Ix.Name))) : IO (Array String) := do
  let .ok pre := Ix.Kernel.Reader.builtinPrelude (md := .source)
    | return #["[auxgen-ixc] measure: the committed prelude does not load"]
  let input : Input := { get? := get?, blocks := blocks }
  let fresh : IO Service := IO.lazyPure fun _ =>
    Service.start pre input (Ix.RoleEvidence.bundleEvidence ())
  let summary (s : Service) : String :=
    let (p, a, r, b) := s.counts
    s!"groups met {s.entries.size}: {a} accepted, {r} refused, {b} blocked, {p} pending"
  let mut out : Array String := #[]
  -- as it runs, every inductive block
  let all := askedMembers get? .inductive levels
  let s₀ ← fresh
  let t₀ ← IO.monoMsNow
  let s ← IO.lazyPure fun _ => all.foldl (init := s₀) fun s ms => s.ensureNames ms
  let t₁ ← IO.monoMsNow
  out := out.push s!"[auxgen-ixc] measure: as it runs, {all.size} inductive blocks: {t₁ - t₀} ms; \
    {summary s}"
  -- lowering, then folding
  let s₀ ← fresh
  let t₀ ← IO.monoMsNow
  let (s, _) ← IO.lazyPure fun _ =>
    all.foldl (init := (s₀, ({} : Std.HashSet Nat))) fun (s, seen) ms => s.lowerNames seen ms
  let t₁ ← IO.monoMsNow
  let s ← IO.lazyPure fun _ => all.foldl (init := s) fun s ms => s.ensureNames ms
  let t₂ ← IO.monoMsNow
  out := out.push s!"[auxgen-ixc] measure: lowering {t₁ - t₀} ms, then folding {t₂ - t₁} ms; \
    {summary s}"
  -- the `.below` asks only
  let below := askedMembers get? .below levels
  let s₀ ← fresh
  let t₀ ← IO.monoMsNow
  let s ← IO.lazyPure fun _ => below.foldl (init := s₀) fun s ms => s.ensureNames ms
  let t₁ ← IO.monoMsNow
  out := out.push s!"[auxgen-ixc] measure: as it runs, the {below.size} blocks with a \
    Type-level .below: {t₁ - t₀} ms; {summary s}"
  -- AuxGen M4: the recursors' asks
  let recs := askedMembers get? .recursors levels
  let s₀ ← fresh
  let t₀ ← IO.monoMsNow
  let s ← IO.lazyPure fun _ => recs.foldl (init := s₀) fun s ms => s.ensureNames ms
  let t₁ ← IO.monoMsNow
  out := out.push s!"[auxgen-ixc] measure: as it runs, the {recs.size} blocks of the \
    recursors' asks (M4): {t₁ - t₀} ms; {summary s}"
  return out

end Ix.AuxGen.Source

end
