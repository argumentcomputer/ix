import Ix.LeanIngress
import Ix.AuxGen.SourceEnv
import Ix.AuxGen.ExprUtils

/-! # The Source service environment (AuxGen on IxC, M1; AUXGEN-IXC §3.2)

The environment IxC answers AuxGen's kernel questions in: the compiler's own
input in Source mode (`Ix.LeanIngress`), checked by the verified fold one
declaration group at a time, **on demand**, and extended by the canonical
flat blocks of the blocks whose canonical layout is not Lean's
(`Ix.AuxGen.Flat`), read through their class map σ. Its checked half (the
fold, the evidence, σ, terms in, installs) is `Ix.AuxGen.Source.SourceEnv`,
a module; this file builds it from a Lean environment.

## Shape

* **Up front** (`Service.create`), what is cheap: the declaration groups,
  their conversions (on tasks) and the reference graph
  (`Ix.LeanIngress.graphOf`), every group lowered through the reader's back
  half in the Source order from the prelude's reader state, exactly as
  `leanIngress` lowers them, Source mode's evidence (`sourceEvidence`) over
  the prepared stream, and the prelude's front: the input's own copy of
  each prelude declaration (its group), else the prelude's, folded first,
  as `Frontend.preparePrelude` puts them first.
* **On demand** (`Service.ensure`), what is expensive: a group is folded
  after every group it depends on, by a depth-first postorder over the
  graph's hard and literal edges and the `Nat` operations' ground
  (`natOpDeps`, the edges `preparePrelude`'s hoist serves), successors in
  Lean's name order (`orderOf`'s rule). A group is folded once; a group a
  failed group precedes is blocked, not folded; a group whose declaration
  the fold refuses leaves the fold as it was before the group. So a driver
  that asks for a block's groups before its aux tail (AUXGEN-IXC §3.2,
  "incrementally in the driver") gets an environment holding exactly the
  closure it asked for: the cost scales with what AuxGen asks about, not
  with the library (`auxgen-flat-initstd`: 7,753 of Init+Std's 114,921
  groups for all its inductive blocks).
* **Flat blocks** (`Service.installFlat`): the canonical flat block of a
  block, lowered as the Source ingress lowers an inductive group
  (`inductiveGroup`, `convert`, `lower`) against the reader state of the
  whole input, after the groups it references, and installed with its σ
  (`SourceEnv.install`). A refused flat block leaves σ as it was: queries
  about that block keep Lean's names and fail closed there.
* **Generated definitions** (`Service.admitDefinition`): the groups they
  reference folded, then `SourceEnv.admitDefinition`.

## What it is not

Not a verdict: `Ix.LeanIngress.checkSource` is. Unsafe groups decline in
the ingress and stay declined here (AUXGEN-IXC §7 Q4: no unchecked install).
Nothing here is trusted: every declaration it installs went through the
verified fold, and an answer it cannot give is a refusal.

## Why this file is not a `module`

The grouping, order and lowering of `Ix.LeanIngress` and the Ixon reader's
back half it lowers through (`IxC/Kernel/Ixon/Reader.lean`, with the role
table, the prelude and `Ix.RoleEvidence`) are not modules, and a module
cannot import them, so the compile drivers (modules) cannot construct this
service yet. The library and its tests run outside the drivers; once those
are modules (an IxC-lane change) this file becomes one by its header. -/

namespace Ix.AuxGen.Source

open Ix.LeanIngress
open Ix.Kernel.Reader (State Read CDecl CName ReadError Prelude)
open Ix.AuxGen.Flat (NameKey ClassMap FlatBlock FlatError)

def renderRead : ReadError → String
  | .malformed m => s!"ingress: malformed: {m}"
  | .declined m => s!"ingress: declined: {m}"

/-! ## The service -/

/-- A declaration group's state in the service. -/
inductive Status where
  /-- lowered, not folded yet -/
  | pending
  | accepted
  /-- the ingress or the fold refused it -/
  | refused (reason : String)
  /-- a group it depends on is refused (`root`, by group index) -/
  | blocked (root : Nat)
  deriving Inhabited, BEq

def Status.isAccepted : Status → Bool
  | .accepted => true
  | _ => false

/-- An installed (or refused) flat block. -/
structure FlatRecord where
  /-- the block's first member, fresh -/
  name : Name
  status : Status

/-- **The Source service environment.** -/
structure Service where
  /-- the input's groups, conversions and edges -/
  graph : Graph
  /-- each group's reading, lowered in the Source order -/
  reads : Array (Except ReadError (Read .source))
  /-- each group's implicit edges to the ground of the `Nat` operations it
  declares -/
  ground : Array (Array Nat)
  /-- each group's rank in Lean's name order (`orderOf`'s) -/
  rank : Array Nat
  /-- the group claiming a Lean name -/
  groupOf : Std.HashMap NameKey Nat
  /-- the reader's state after every group and every installed flat block -/
  reader : State .source
  status : Array Status
  /-- the checked half: the fold, the evidence, σ -/
  env : SourceEnv
  flats : Array FlatRecord := #[]
  /-- the prelude declarations no group of the input declares, folded from
  the prelude itself -/
  synthesised : Nat := 0

instance : Inhabited Service :=
  ⟨{ graph := ⟨#[], #[], #[], #[], #[]⟩, reads := #[], ground := #[], rank := #[], groupOf := {},
     reader := {}, status := #[], env := {} }⟩

namespace Service

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

/-- The group's edges: hard, literal and `Nat` ground, without itself. -/
def deps (s : Service) (i : Nat) : Array Nat :=
  ((s.graph.hard[i]?.getD #[]) ++ (s.graph.literal[i]?.getD #[]) ++ (s.ground[i]?.getD #[])).filter
    (· != i)

/-- Fold group `i`, whose dependencies are folded: blocked if one failed,
refused if the ingress refused it or the fold refuses one of its
declarations (the fold then stays as before the group), accepted
otherwise. A group already folded is left as it is. -/
def foldGroup (s : Service) (i : Nat) : Service :=
  if !(s.status[i]? == some .pending) then s else
  let failed := (s.deps i).find? fun j => (s.status[j]?.map (!·.isAccepted)).getD true
  match failed with
  | some j =>
    let root := match s.status[j]? with
      | some (.blocked r) => r
      | _ => j
    { s with status := s.status.set! i (.blocked root) }
  | none =>
    match s.reads[i]? with
    | some (.ok r) =>
      match s.env.fold.steps s.env.ev r.decls with
      | .ok f => { s with env := { s.env with fold := f }, status := s.status.set! i .accepted }
      | .error e => { s with status := s.status.set! i (.refused (renderCheck e)) }
    | some (.error e) => { s with status := s.status.set! i (.refused (renderRead e)) }
    | none => s

/-- **Fold group `root` and everything it depends on**, depth first, in
postorder, successors in Lean's name order. -/
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
    else if s.status[node]? == some .pending && !active.contains node then
      active := active.insert node
      stack := stack.push (node, true)
      -- pushed last-first, so that they are visited first-first
      let succs := (s.deps node).qsort fun a b => (s.rank[a]?.getD 0) > (s.rank[b]?.getD 0)
      for d in succs do
        if s.status[d]? == some .pending && !active.contains d then
          stack := stack.push (d, false)
  return s

/-- The group claiming a Lean name, if the input has it. -/
def groupOfName? (s : Service) (n : Name) : Option Nat := s.groupOf.get? ⟨n⟩

/-- **Fold the groups claiming `names`**, with their dependencies. -/
def ensureNames (s : Service) (names : Array Name) : Service :=
  names.foldl (fun s n => match s.groupOfName? n with
    | some i => s.ensure i
    | none => s) s

/-- The state of the group claiming a Lean name. -/
def statusOf? (s : Service) (n : Name) : Option Status := do
  s.status[← s.groupOfName? n]?

/-- The first of `names` whose group Source mode did not accept. -/
def firstUnaccepted? (s : Service) (names : Array Name) : Option Name :=
  names.find? fun n => !((s.statusOf? n).map (·.isAccepted)).getD true

/-- **The service over an input** (`env` under its condensation `blocks`)
behind the prelude `pre`: groups, conversions (on `workers` tasks) and
edges; every group lowered in the Source order; Source mode's evidence
(unless `evidence` is given); the prelude's front folded. Nothing else is
folded yet. -/
def create (pre : Prelude .source) (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (workers : Nat := 1) (evidence : Option (Ix.Kernel.Evidences .source) := none) : Service :=
  Id.run do
  let groups := groupsOf env blocks
  let g := graphOf blocks groups (convertAll groups workers)
  let n := groups.size
  -- every group lowered in the Source order from the prelude's state
  let mut st := pre.state
  let mut reads : Array (Except ReadError (Read .source)) :=
    Array.replicate n (.error (.malformed "not scheduled"))
  let mut lowered : Array Decl := #[]
  for (gi, c) in scheduleOf g do
    match c >>= lower st with
    | .ok r =>
      st := st.commit r
      reads := reads.set! gi (.ok r)
      lowered := lowered ++ r.decls
    | .error e => reads := reads.set! gi (.error e)
  let ev := evidence.getD (sourceEvidence (Ix.Kernel.Frontend.preparePrelude pre.ix lowered))
  -- the group declaring each key, and the ground of each group's `Nat` operations
  let mut keyGroup : Std.HashMap (CName .source) Nat := {}
  for (r, i) in reads.zipIdx do
    if let .ok r := r then
      for d in r.decls do
        for k in d.names do keyGroup := keyGroup.insert k i
  let mut ground : Array (Array Nat) := Array.replicate n #[]
  for (r, i) in reads.zipIdx do
    if let .ok r := r then
      for d in r.decls do
        if let some c := Ix.Kernel.Frontend.isNatOpRecord d then
          for k in Ix.Kernel.natOpDeps c do
            if let some j := keyGroup[k]? then
              if j != i && !ground[i]!.contains j then ground := ground.modify i (·.push j)
  -- ranks in Lean's name order
  let byName := (Array.range n).qsort fun i j => namesLt groups[i]!.names groups[j]!.names
  let mut rank : Array Nat := Array.replicate n 0
  for (i, r) in byName.zipIdx do rank := rank.set! i r
  let mut groupOf : Std.HashMap NameKey Nat := {}
  for (grp, i) in groups.zipIdx do
    for m in grp.names do groupOf := groupOf.insert ⟨m⟩ i
  let mut s : Service :=
    { graph := g, reads, ground, rank, groupOf, reader := st,
      status := Array.replicate n .pending, env := { ev } }
  -- the prelude's front: the input's own copy of a prelude declaration
  -- (its group, with its dependencies), else the prelude's
  for p in pre.ix.decls do
    match (Ix.Kernel.Frontend.preludeKey p).bind (keyGroup[·]?) with
    | some i => s := s.ensure i
    | none =>
      match s.env.fold.step s.env.ev p with
      | .ok f => s := { s with env := { s.env with fold := f }, synthesised := s.synthesised + 1 }
      | .error _ => pure ()
  return s

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
group, against the reader state of the whole input, and installed with its
σ (`SourceEnv.install`). The outcome is recorded (`flats`); a refusal leaves
the environment and σ as they were. -/
def installFlat (s : Service) (b : FlatBlock) : Service := Id.run do
  let some first := b.types[0]? | return s
  let record (st : Status) (s : Service) : Service :=
    { s with flats := s.flats.push ⟨first.cnst.name, st⟩ }
  let refs := flatRefs b
  let s := s.ensureNames refs
  if let some n := s.firstUnaccepted? refs then
    return record (.refused s!"references {n.pretty}, which Source mode did not accept") s
  let env : Ix.Environment := { consts := b.consts.foldl (fun m (n, c) => m.insert n c) {} }
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
service after it, and the verdict. -/
def admitDefinition (s : Service) (name : Name) (lps : Array Name) (type value : Expr)
    (thm : Bool) (hint : Ix.Kernel.ReducibilityHint := .abbrev) : Service × Status :=
  let refs := ((collectLeanConstRefs value (collectLeanConstRefs type {})).toArray.filter
    fun n => (s.sigma.find? n).isNone && !Flat.isFresh n).qsort (nameCmp · · == .lt)
  let s := s.ensureNames refs
  match s.firstUnaccepted? refs with
  | some n => (s, .refused s!"references {n.pretty}, which Source mode did not accept")
  | none =>
    match s.env.admitDefinition name lps type value thm hint with
    | .ok env' => ({ s with env := env' }, .accepted)
    | .error why => (s, .refused why)

/-! ## Counts -/

/-- Groups by state: pending, accepted, refused, blocked. -/
def counts (s : Service) : Nat × Nat × Nat × Nat :=
  s.status.foldl (init := (0, 0, 0, 0)) fun (p, a, r, b) st => match st with
    | .pending => (p + 1, a, r, b)
    | .accepted => (p, a + 1, r, b)
    | .refused _ => (p, a, r + 1, b)
    | .blocked _ => (p, a, r, b + 1)

end Service

end Ix.AuxGen.Source
