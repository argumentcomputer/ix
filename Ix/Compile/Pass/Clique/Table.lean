/-
  Ix.Compile.Pass.Clique.Table: the definition cliques of the input, the
  changed-clique table and the scheduling edges, and the reserved names of a
  clique's canonical constants.

  **The clique of a member.** Lean's `all` of a safe definition or a theorem,
  when it has two or more members, each in its own block, and some block
  references an encoding marker (`_mutual`, `mutual`, `_f`, or the `brecOn`
  of an inductive predicate whose `below` is an inductive). A kernel mutual
  block is one block, so it is not an encoded clique; neither is a `partial`
  or `unsafe` clique.

  **The table.** Every member of an input clique, and every carried
  equation lemma, ↦ (Lean's `all`, the carried lemmas) (`scheduleCliques`).
  The form of a clique is decided from the clique, its own logical unit and
  its dependencies only: no caller is read.

  **The edges** only order blocks (each member block can plan the clique
  alone, and the first member's block plans it first); they change no byte.

  Total: `for` loops over finite collections, structural recursion, and two
  bounds of `Bounds` (`eqLemmaBound`, `encodingOwnerDepth`).
-/
module
public import Ix.Environment
public import Ix.CondenseM
public import Ix.Compile.Pass.Names
public import Ix.Compile.Pass.Clique.Basic
@[expose] public section

namespace Ix.Compile.Pass.Clique

open Ix (Name ConstantInfo)

/-! ## Names -/

/-- The side-car record key on a canonical functional: `_ix.clique`. -/
def cliqueKey : Name := Name.mkStr (Name.mkStr Name.mkAnon ixComponent) "clique"

/-- The decompile records of transported members use placeholder indices
from here (the call-site rewrite's indices start at `0` in every block). -/
def cliqueRecordBase : Nat := 1 <<< 40

/-- `x ++ s` for a string component. -/
def nameStr (x : Name) (s : String) : Name := Name.mkStr x s

/-- The last string component. -/
def lastStr : Name → String
  | .str _ s _ => s
  | _ => ""

/-- The display name of a Lean encoding constant `x.rest` (`x` a member, the
first in `all` that is a proper prefix): `x._ix.rest`. -/
def cliqueIxName (all : Array Name) (a : Name) : Option Name := do
  let (x, rest) ← all.findSome? fun x =>
    match stripPrefix? x a with
    | some rest => if rest.isEmpty then none else some (x, rest)
    | none => none
  return appendComps (nameStr x ixComponent) rest

/-! ## Terms

The constants of a term satisfying a predicate are `constOccurrences`
(`Basic`): distinct names, in first-occurrence pre-order. -/

/-- Rename a declaration's name and the constants of its type and value
(`renameConsts`). -/
def renameDecl (m : Std.HashMap Name Name) (d : Decl) : Decl :=
  if m.isEmpty then d else
  { d with
    name := (m.get? d.name).getD d.name
    type := renameConsts m.get? d.type
    value := renameConsts m.get? d.value }

/-! ## The clique of a member -/

/-- Lean's `all`. -/
def allOf : ConstantInfo → Array Name
  | .defnInfo v => v.all
  | .thmInfo v => v.all
  | _ => #[]

/-- A safe definition or a theorem, as the transport's declaration. -/
def cliqueDecl? (ci : ConstantInfo) : Option Decl :=
  match ci with
  | .defnInfo v => if v.safety == .safe then Decl.ofConstantInfo? ci else none
  | .thmInfo _ => Decl.ofConstantInfo? ci
  | _ => none

/-- A name that marks a clique encoding in a reference set: `_mutual`
(well-founded), `mutual` (`partial_fixpoint`), `_f` (structural), or the
`brecOn` of an inductive predicate whose `below` is an inductive (the
inductive-predicate route). -/
def isEncodingMarker (const? : Name → Option ConstantInfo) (n : Name) : Bool :=
  match n with
  | .str p s _ =>
    s == "_mutual" || s == "mutual" || s == "_f" ||
      (s == "brecOn" && (match const? (nameStr p "below") with
        | some (.inductInfo _) => true
        | _ => false))
  | _ => false

/-! ## The clique table and the scheduling edges -/

/-- The cliques of the input whose members are separate blocks, by Lean's
`all`. Only blocks that reference an encoding marker are read. -/
def inputCliques (env : Ix.Environment) (blocks : Ix.CondensedBlocks) : Array (Array Name) := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut out : Array (Array Name) := #[]
  -- the blocks that reference an encoding marker, and their members, in
  -- pretty-name order (not the hash maps' order), as the Rust twin reads them
  let marked := blocks.blocks.toArray.filter fun (lo, _) =>
    (blocks.blockRefs.getD lo {}).toList.any (isEncodingMarker env.get?)
  for (_, mems) in marked.qsort (fun a b => a.1.pretty < b.1.pretty) do
    for m in mems.toArray.qsort (fun a b => a.pretty < b.pretty) do
      if seen.contains m then continue
      let some ci := env.get? m | continue
      let all := allOf ci
      if all.size < 2 || (cliqueDecl? ci).isNone then continue
      for a in all do seen := seen.insert a
      -- every member present, each in its own block
      let los := all.filterMap blocks.lowLinks.get?
      if los.size != all.size then continue
      let loSet : Std.HashSet Name := los.foldl (·.insert ·) {}
      if loSet.size != all.size then continue
      out := out.push all
  return out

/-- A Lean encoding constant of a clique, by name: `all₀._mutual` and
`all₀.mutual` with everything under them (proofs, equation lemmas), `m._f`. -/
def isEncodingName (all : Array Name) (n : Name) : Bool :=
  match all[0]? with
  | none => false
  | some all0 =>
    (stripPrefix? (nameStr all0 "_mutual") n).isSome || (stripPrefix? (nameStr all0 "mutual") n).isSome ||
      (match n with
        | .str p "_f" _ => all.contains p
        | _ => false)

/-- The library constants the transport may introduce (the composition
fallback of `partial_fixpoint`, the case split of a regenerated equation
lemma): every clique block waits for them too, when the input has them. -/
def transportPrereqs : Array Name :=
  #[``Lean.Order.monotone_compose, ``PSigma.casesOn, ``PSigma.mk, ``PSum.casesOn, ``PSum.inl,
    ``PSum.inr, ``Eq, ``Eq.trans, ``id].map Ix.Name.fromLeanName

/-- `_private.<module>.0.<n>` ↦ `n` (Lean's `privateToUserName?`): the
module system realises an on-demand lemma of a public definition under a
private name when a private declaration asks for it. The marker is the
number `0` (Lean) or, in names that went through a string form, the
component `"0"`: the first one after `_private`. -/
def privateUserName? (n : Name) : Option Name :=
  match comps n with
  | .s "_private" :: rest => do
    let i ← rest.findIdx? fun c => c == .n 0 || c == .s "0"
    some (ofComps (rest.drop (i + 1)))
  | _ => none

/-- An equation lemma's last component: `eq_def`, `eq_unfold`, `eq_<k>`. -/
def isEqSuffix (s : String) : Bool :=
  s == "eq_def" || s == "eq_unfold" ||
    (s.startsWith "eq_" && (s.drop 3).all Char.isDigit && !(s.drop 3).isEmpty)

/-- The equation lemmas the input has under a private name, by their user
name (`privateUserName?`). An index of names only: a clique reads the
entries of its own members' lemma names. -/
def privateEqLemmas (blocks : Ix.CondensedBlocks) : Std.HashMap Name (Array Name) := Id.run do
  let mut out : Std.HashMap Name (Array Name) := {}
  for (_, mems) in blocks.blocks do
    for n in mems do
      let some u := privateUserName? n | continue
      let .str _ s _ := u | continue
      if isEqSuffix s then out := out.insert u ((out.getD u #[]).push n)
  return out

/-- The equation lemmas of a member that the input has, by name: `m.eq_def`,
`m.eq_unfold` and `m.eq_1`, `m.eq_2`, … (numbered from 1 without gaps, as
Lean realises them, below `eqLemmaBound`), under that name or under a private
name whose user name it is (`priv`, `privateEqLemmas`). They are on-demand
auxiliaries of the clique's own unit: reading them is reading the unit. -/
def memberEqLemmas (const? : Name → Option ConstantInfo) (priv : Std.HashMap Name (Array Name))
    (m : Name) : Array Name := Id.run do
  let mut out : Array Name := #[]
  let present (n : Name) : Array Name :=
    (if (const? n).isSome then #[n] else #[]) ++
      ((priv.getD n #[]).qsort fun a b => a.pretty < b.pretty)
  for s in ["eq_def", "eq_unfold"] do
    out := out ++ present (nameStr m s)
  for k in [1:eqLemmaBound] do
    let found := present (nameStr m s!"eq_{k}")
    if found.isEmpty then break
    out := out ++ found
  return out

/-- The clique whose Lean encoding constant `n` is (`isEncodingName`), from a
map of the encoding roots (`all₀._mutual`, `all₀.mutual`, `m._f`) to the
cliques: `n` or one of its prefixes is a root. The first `encodingOwnerDepth`
names (`n`, its parent, …) are looked up, nearest first. -/
def encodingOwner? (roots : Std.HashMap Name (Array Name)) (n : Name) : Option (Array Name) :=
  go encodingOwnerDepth n
where
  /-- Look up `cur` and, with `fuel` lookups left, its prefixes. -/
  go : Nat → Name → Option (Array Name)
    | 0, _ => none
    | fuel + 1, cur =>
      match (roots.get? cur).filter (isEncodingName · n), cur with
      | some all, _ => some all
      | none, .str p _ _ | none, .num p _ _ => go fuel p
      | none, .anonymous _ => none

/-- The changed-clique table and the scheduling edges (called once per
compile, before the schedule). The form of a clique is decided from the
clique, its own logical unit and its dependencies only: no caller is read.
Returns the blocks with the added edges, the table and the encoding roots.

* **The table.** Every member of an input clique (`inputCliques`) ↦ (Lean's
  `all`, the carried lemmas). The **carried lemmas** are the members' own
  equation lemmas (`memberEqLemmas`, read by name: the clique's unit) whose
  block references a member and one of Lean's encoding constants of the
  clique (`isEncodingName`): their proofs unfold the members to Lean's
  encoding, so they are transported with the clique (each carried lemma is
  in the table too), or the clique stays in Lean's form when one cannot be
  carried.
* **The encoding roots.** `all₀._mutual`, `all₀.mutual` and every `m._f` ↦
  the clique, so that a block can tell that it references a clique's
  encoding (`encodingOwner?`). A block outside the unit that references a
  member and an encoding constant of a transported clique is refused when it
  compiles; the clique is never changed for it.
* **The edges.** Every member block, and every carried lemma's block, also
  waits for everything any member's block references (the encoding
  constants, the other members' matchers and proofs, the constants their
  statements mention) and for the input's `transportPrereqs`, so that each
  such block can plan the clique alone: the specifications' external
  references and the canonical constants' dependencies are compiled before
  it. The clique's other blocks also wait for the block of its first member
  (`all₀`), which plans the clique first: they take its plan from the plan
  table. These edges only order blocks; they change no byte. The carried
  lemmas and the union are read from the input's references, the edges
  accumulate over the cliques. -/
def scheduleCliques (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    Ix.CondensedBlocks × Std.HashMap Name (Array Name × Array Name) × Std.HashMap Name (Array Name) :=
    Id.run do
  let cliques := inputCliques env blocks
  let priv := if cliques.isEmpty then {} else privateEqLemmas blocks
  let mut roots : Std.HashMap Name (Array Name) := {}
  let mut table : Std.HashMap Name (Array Name × Array Name) := {}
  let mut blockRefs := blocks.blockRefs
  for all in cliques do
    if let some all0 := all[0]? then
      roots := roots.insert (nameStr all0 "_mutual") all |>.insert (nameStr all0 "mutual") all
    for m in all do roots := roots.insert (nameStr m "_f") all
    -- the carried lemmas: the members' equation lemmas over Lean's encoding
    let mut found : Array Name := #[]
    for m in all do
      for c in memberEqLemmas env.get? priv m do
        let some lo := blocks.lowLinks.get? c | continue
        let refs := blocks.blockRefs.getD lo {}
        if refs.toList.any (isEncodingName all ·) && refs.toList.any all.contains then
          found := found.push c
    let carried := found.qsort fun a b => a.pretty < b.pretty
    for m in all do table := table.insert m (all, carried)
    for c in carried do table := table.insert c (all, carried)
    -- the edges
    let members : Std.HashSet Name := all.foldl (·.insert ·) {}
    let los := all.filterMap blocks.lowLinks.get?
    let mut union : Ix.Set Name := {}
    for p in transportPrereqs do
      if blocks.lowLinks.contains p then union := union.insert p
    for lo in los do
      for r in blocks.blockRefs.getD lo {} do
        if !members.contains r then union := union.insert r
    -- one block plans the clique first (the block of `all₀`); the clique's
    -- other blocks also wait for it, so that they take the plan from the
    -- plan table instead of planning it again in its wave
    let all0? := all[0]?
    let plannerLo? := all0?.bind blocks.lowLinks.get?
    for lo in los ++ carried.filterMap blocks.lowLinks.get? do
      let own := blocks.blocks.getD lo {}
      let mut rs := blockRefs.getD lo {}
      for r in union do
        if !own.contains r then rs := rs.insert r
      if let some all0 := all0? then
        if plannerLo? != some lo && !own.contains all0 then rs := rs.insert all0
      blockRefs := blockRefs.insert lo rs
  return ({ blocks with blockRefs }, table, roots)

end Ix.Compile.Pass.Clique

end
