/-
  Ix.AuxGen.FlatBlock: the canonical flat block of an inductive block under
  fresh names, with the class map σ (AuxGen on IxC, M1; AUXGEN-IXC §4.4 and
  §7 Q1, README §6 finding 7).

  ## Why

  The compiler collapses α-equivalent members of an inductive block into one
  class, orders the classes canonically, and generates the block's
  auxiliaries (`rec`, `casesOn`, `below`, `brecOn`, …) over the
  representatives. Those auxiliaries are well typed in the α-quotient of the
  source, not in the source by name: a canonical recursor applies one
  class's motive to terms of an α-equivalent member's type. `Ix.Tc` accepts
  this because its environment keys both members by one provisional
  address; IxC's Source mode keys them by name, and refuses (the spike's 20
  fixture refusals, AUXGEN-IXC §4.4 item 1). The fix is to make the quotient
  an object: the canonical flat block, installed beside the source under
  fresh names, and the class map σ that sends each member to its
  representative's fresh name. Queries and generated terms are read through
  σ. That is `Ix.Tc`'s provisional-address trick, checked instead of
  assumed, and the alias-collapse step the statements' bridge needs before
  the renaming lemma applies (IXC-PLAN §12, SP3 H2).

  ## What

  For the canonical classes of a block (`sortedClasses` as the compiler
  computes them, representative first, restricted to Lean's `all`) and the
  block's canonical recursors (`AuxPatchesOutput.canonicalRecs`):
  * one inductive per class, the representative's declaration under its
    fresh name, its constructors the representative's constructors under
    theirs;
  * the canonical recursors, the class recursors first and then one per
    canonical nested auxiliary, named as the Source ingress expects a block's
    recursors (`F.rec` for each member `F`, `F₀.rec_j` for the first member
    `F₀`, `j = 1 … numNested`, where `numNested` is the canonical auxiliary
    count);
  * every term renamed by σ, which also renames projections' structure names.

  σ maps each member of a class to the fresh name of the class's
  representative, each member's constructor `j` to the fresh name of the
  representative's constructor `j` (α-equivalent members have the same
  constructor count, checked), and each canonical recursor's name (the name
  AuxGen gives it: `<rep>.rec`, `<all0>.rec_N` source-indexed) to its fresh
  name. Every other name is fixed.

  ## Fresh names, and why they are input keys

  A fresh name is the original name under the reserved root component
  `_ixflat` (`fresh`), checked absent from the environment (`FlatError.taken`).
  In Source mode a name is an input key (`Key.id`), so σ on Source keys is
  `Key.map` of the same name map, and the flat block's keys rename into the
  Ixon reading of the compiled block (whose members are `.id` keys at their
  projection addresses) by `Key.map f`: σ fits the renaming lemma's shape
  (IXC-PLAN §12; SP3 §9 H1: `Key.map` sends `.id` to `.id`). Keys of the
  checker's derived shape (`Key.aux`) would not: `Key.map f (.aux b d) = .aux
  (Key.map f b) d`, which no Ixon reading produces, and IxC's `Derived` has
  no shape for them. σ is not injective, by design: an α-collapsed class's
  members share one fresh name. The renaming lemma applies after it, to the
  flat block and its dependencies, on which `f` is injective.

  `ClassMap.misfit` finds a breach of the one side condition the Source
  side needs: σ moves no name its role binding fixes, and maps nothing onto
  such a name (`Key.map` fixes `.role` keys). A block with a role-bound member keeps
  Lean's layout (the basis blocks are single and uncollapsed), so σ is never
  asked to move one; `SourceEnv.install` refuses it if it were.

  ## When it is needed

  `needed` holds when the canonical layout is not Lean's: a class with
  several members, a class order other than Lean's `all`, or nested
  auxiliaries in another order or number. Otherwise the canonical
  recursors are named as Lean's own and σ is the identity.

  Nothing here reads a hash for identity: names compare structurally
  (`Ix.Compile.ExactKey.nameEq`), the renaming's memo is keyed by `ExprKey`.
  Nothing here depends on IxC: the Source side (installing the block,
  reading queries through σ) is `Ix.AuxGen.SourceEnv`'s, and building
  the environment from Lean's is `Ix.AuxGen.SourceService`'s.
-/
module
public import Ix.Environment
public import Ix.Compile.ExactKey
public import Ix.AuxGen.Types
public section

namespace Ix.AuxGen.Flat

open Ix.Compile.ExactKey (nameEq nameEq_iff exprEq ExprKey)

/-! ## Exact name keys -/

/-- A name as an exact map key: the stored hash selects a bucket, structural
equality (`nameEq`) decides, so two names whose hashes collide are two
keys. -/
structure NameKey where
  name : Name

instance : BEq NameKey := ⟨fun a b => nameEq a.name b.name⟩
instance : Hashable NameKey := ⟨fun k => hash k.name⟩

instance : LawfulBEq NameKey where
  eq_of_beq {a b} h := by
    cases a with
    | mk a =>
      cases b with
      | mk b =>
        have : nameEq a b = true := h
        rw [nameEq_iff] at this
        rw [this]
  rfl {a} := by
    show nameEq a.name a.name = true
    rw [nameEq_iff]

/-! ## Fresh names -/

/-- The reserved first component of every fresh name. -/
def freshRoot : String := "_ixflat"

/-- **The fresh name of `n`**: `n`'s components under the reserved root
`_ixflat`. Injective, and it commutes with extending a name
(`fresh (n.str s) = (fresh n).str s`), so a block member's recursor `T.rec`
has the fresh name `(fresh T).rec`. -/
def fresh : Name → Name
  | .anonymous _ => Name.mkStr .mkAnon freshRoot
  | .str p s _ => Name.mkStr (fresh p) s
  | .num p i _ => Name.mkNat (fresh p) i

/-- Whether `n` is a fresh name: its first component is the reserved root. -/
def isFresh : Name → Bool
  | .str (.anonymous _) s _ => s == freshRoot
  | .str p _ _ | .num p _ _ => isFresh p
  | .anonymous _ => false

/-! ## The class map σ -/

/-- Why a flat block cannot be built (or σ extended). -/
inductive FlatError where
  /-- the canonical classes are empty, or class `index` is -/
  | emptyClass (index : Nat)
  /-- a class member that is not an inductive of the environment -/
  | notInductive (name : Name)
  /-- a constructor the environment lacks -/
  | missingCtor (name : Name)
  /-- an α-collapsed member whose constructor count differs from its
  representative's -/
  | ctorCount (member rep : Name) (memberCount repCount : Nat)
  /-- fewer canonical recursors than classes -/
  | recCount (classes recs : Nat)
  /-- a class recursor that is not `<rep>.rec` -/
  | recName (expected got : Name)
  /-- a fresh name the environment already declares -/
  | taken (freshName : Name)
  /-- a name σ would send to two different fresh names -/
  | conflict (name first second : Name)
  /-- a name σ would move or produce that its role binding fixes -/
  | roleBound (name : Name)
  deriving Inhabited

def FlatError.render : FlatError → String
  | .emptyClass i => s!"canonical flat block: class {i} is empty"
  | .notInductive n => s!"canonical flat block: {n.pretty} is not an inductive of the environment"
  | .missingCtor n => s!"canonical flat block: constructor {n.pretty} is missing"
  | .ctorCount m r a b =>
    s!"canonical flat block: {m.pretty} has {a} constructors, its representative {r.pretty} {b}"
  | .recCount c r => s!"canonical flat block: {r} canonical recursors for {c} classes"
  | .recName e g => s!"canonical flat block: class recursor {g.pretty}, expected {e.pretty}"
  | .taken f => s!"canonical flat block: the fresh name {f.pretty} is declared in the environment"
  | .conflict n a b =>
    s!"canonical flat block: σ would send {n.pretty} to {a.pretty} and to {b.pretty}"
  | .roleBound n => s!"canonical flat block: σ would move the role-bound name {n.pretty}"

instance : ToString FlatError := ⟨FlatError.render⟩

/-- **The class map σ** on Lean names: the non-identity entries, in the order
they were made, and their index. Every name it has no entry for is fixed. -/
structure ClassMap where
  entries : Array (Name × Name) := #[]
  map : Std.HashMap NameKey Name := {}
  deriving Inhabited

namespace ClassMap

/-- σ's entry for `n`, if it moves `n`. -/
def find? (σ : ClassMap) (n : Name) : Option Name := σ.map.get? ⟨n⟩

/-- σ applied to a name. -/
def apply (σ : ClassMap) (n : Name) : Name := (σ.find? n).getD n

/-- σ with `n ↦ m`. An entry `n ↦ m` already there is kept; a different
target for `n` is a conflict. -/
def insert (σ : ClassMap) (n m : Name) : Except FlatError ClassMap :=
  match σ.find? n with
  | some m' => if nameEq m m' then .ok σ else .error (.conflict n m' m)
  | none => .ok { entries := σ.entries.push (n, m), map := σ.map.insert ⟨n⟩ m }

/-- σ extended by every entry of `τ` (the conflicts of `insert`). -/
def union (σ τ : ClassMap) : Except FlatError ClassMap :=
  τ.entries.foldlM (fun σ (n, m) => σ.insert n m) σ

/-- **σ fits the renaming lemma's `Key.map`** (IXC-PLAN §12), given which
names Source mode's role binding fixes (`roleBound`): σ moves no role-bound
name and sends nothing onto one. Then a σ-renamed term's Source keys are
its keys renamed by `Key.map`, since a moved name and its image are both
input keys. The first offending name, if any. -/
def misfit (σ : ClassMap) (roleBound : Name → Bool) : Option Name :=
  σ.entries.findSome? fun (n, m) =>
    if roleBound n then some n else if roleBound m then some m else none

end ClassMap

/-! ## σ on terms -/

/-- The renaming's memo, keyed exactly (`ExprKey`): a hit is the same term. -/
abbrev RenameCache := Std.HashMap ExprKey Expr

/-- **σ on a term**: every constant and every projection's structure name
renamed by σ, everything else kept. Computed on the DAG (one memo across
the terms of a block); a node none of whose children moved is returned as
it is. -/
def renameExpr (σ : ClassMap) (e : Expr) : StateM RenameCache Expr := do
  if let some r := (← get).get? ⟨e⟩ then return r
  let r ← match e with
    | .const n us _ =>
      pure (match σ.find? n with
        | some n' => Expr.mkConst n' us
        | none => e)
    | .app f a _ => do
      let f' ← renameExpr σ f
      let a' ← renameExpr σ a
      pure (if exprEq f' f && exprEq a' a then e else Expr.mkApp f' a')
    | .lam n t b bi _ => do
      let t' ← renameExpr σ t
      let b' ← renameExpr σ b
      pure (if exprEq t' t && exprEq b' b then e else Expr.mkLam n t' b' bi)
    | .forallE n t b bi _ => do
      let t' ← renameExpr σ t
      let b' ← renameExpr σ b
      pure (if exprEq t' t && exprEq b' b then e else Expr.mkForallE n t' b' bi)
    | .letE n t v b nd _ => do
      let t' ← renameExpr σ t
      let v' ← renameExpr σ v
      let b' ← renameExpr σ b
      pure (if exprEq t' t && exprEq v' v && exprEq b' b then e else Expr.mkLetE n t' v' b' nd)
    | .mdata d b _ => do
      let b' ← renameExpr σ b
      pure (if exprEq b' b then e else Expr.mkMData d b')
    | .proj n i b _ => do
      let b' ← renameExpr σ b
      match σ.find? n with
      | some n' => pure (Expr.mkProj n' i b')
      | none => pure (if exprEq b' b then e else Expr.mkProj n i b')
    | .bvar .. | .fvar .. | .mvar .. | .sort .. | .lit .. => pure e
  modify (·.insert ⟨e⟩ r)
  return r

/-- σ on one term, with a fresh memo. -/
def rename (σ : ClassMap) (e : Expr) : Expr := (renameExpr σ e).run' {}

/-! ## The canonical flat block -/

/-- **The canonical flat block** of an inductive block: its canonical
classes, the class representatives' declarations under fresh names, the
canonical recursors under fresh names, and σ. -/
structure FlatBlock where
  /-- The canonical classes, representative first, in canonical order. -/
  classes : Array (Array Name)
  /-- One inductive per class, in class order. -/
  types : Array InductiveVal
  /-- Each type's constructors, in order. -/
  ctors : Array (Array ConstructorVal)
  /-- The class recursors in class order, then the nested auxiliaries'
  recursors in canonical order. -/
  recs : Array RecursorVal
  /-- The class map. -/
  sigma : ClassMap
  deriving Inhabited

namespace FlatBlock

/-- The flat block's constants under their fresh names: the types, each
type's constructors, the recursors. -/
def consts (b : FlatBlock) : Array (Name × ConstantInfo) :=
  b.types.map (fun v => (v.cnst.name, .inductInfo v)) ++
    b.ctors.flatMap (·.map fun c => (c.cnst.name, .ctorInfo c)) ++
    b.recs.map (fun r => (r.cnst.name, .recInfo r))

/-- The number of canonical nested auxiliaries. -/
def numNested (b : FlatBlock) : Nat := b.recs.size - b.types.size

/-- The flat block's first member, under its fresh name: the name the block
is installed and reported under. -/
def firstName (b : FlatBlock) : Option Name := b.types[0]?.map (·.cnst.name)

end FlatBlock

/-- **The canonical layout is not Lean's**: a class with several members, a
class order other than Lean's `all` (`originalAll`), or canonical nested
auxiliaries that are not Lean's `all0.rec_1 … all0.rec_n` in order
(`auxRecNames`, the canonical recursors past the classes; `leanNumNested`,
Lean's count). When it is Lean's, the canonical recursors carry Lean's
recursors' names and σ is the identity, so no flat block is installed. -/
def needed (classes : Array (Array Name)) (originalAll : Array Name)
    (auxRecNames : Array Name) (leanNumNested : Nat) : Bool := Id.run do
  if classes.any (·.size != 1) then return true
  if classes.size != originalAll.size then return true
  for (cls, n) in classes.zip originalAll do
    match cls[0]? with
    | some r => if !nameEq r n then return true
    | none => return true
  if auxRecNames.size != leanNumNested then return true
  let some all0 := originalAll[0]? | return !auxRecNames.isEmpty
  for (n, j) in auxRecNames.zipIdx do
    if !nameEq n (Name.mkStr all0 s!"rec_{j + 1}") then return true
  return false

/-- **Build the canonical flat block** of a block from its canonical classes
(representative first, canonical order, restricted to Lean's `all`) and its
canonical recursors (`AuxPatchesOutput.canonicalRecs`: the class recursors
in class order, then the canonical nested auxiliaries'), over the
environment `lookup`. Fails closed (`FlatError`): a class member or
constructor the environment lacks, a collapsed member whose constructor
count differs from its representative's, a class recursor not named
`<rep>.rec`, a fresh name the environment declares, a conflict in σ.

`base` is the class map of the flat blocks installed before this one: the
block's terms are renamed by `base` and the block's own σ together, so a
block that references a collapsed block reads it through its σ (the
compiler identifies the collapsed members there too). The result's
`sigma` is the block's own entries; `base` is not repeated in it. -/
def build (lookup : Name → Option ConstantInfo) (classes : Array (Array Name))
    (canonicalRecs : Array (Name × RecursorVal)) (base : ClassMap := {}) :
    Except FlatError FlatBlock := do
  if classes.isEmpty then throw (.emptyClass 0)
  -- the representatives and their constructors
  let mut reps : Array (InductiveVal × Array ConstructorVal) := #[]
  for (cls, i) in classes.zipIdx do
    let some rep := cls[0]? | throw (.emptyClass i)
    let some (.inductInfo v) := lookup rep | throw (.notInductive rep)
    let cs ← v.ctors.mapM fun c => match lookup c with
      | some (.ctorInfo cv) => pure cv
      | _ => throw (.missingCtor c)
    reps := reps.push (v, cs)
  let nClasses := classes.size
  unless canonicalRecs.size ≥ nClasses do throw (.recCount nClasses canonicalRecs.size)
  -- σ on the members and their constructors
  let mut own : ClassMap := {}
  for (cls, (v, _)) in classes.zip reps do
    let rep := v.cnst.name
    for m in cls do
      own ← own.insert m (fresh rep)
      if nameEq m rep then
        for c in v.ctors do own ← own.insert c (fresh c)
      else
        let some (.inductInfo vm) := lookup m | throw (.notInductive m)
        unless vm.ctors.size == v.ctors.size do
          throw (.ctorCount m rep vm.ctors.size v.ctors.size)
        for (c, c') in vm.ctors.zip v.ctors do own ← own.insert c (fresh c')
  -- σ on the canonical recursors' names
  let freshReps : Array Name := reps.map fun (v, _) => fresh v.cnst.name
  let some first := freshReps[0]? | throw (.emptyClass 0)
  let mut recNames : Array Name := #[]
  for ((n, _), k) in canonicalRecs.zipIdx do
    let target ← if h : k < reps.size then do
        let want := Name.mkStr reps[k].1.cnst.name "rec"
        unless nameEq n want do throw (.recName want n)
        pure (fresh want)
      else pure (Name.mkStr first s!"rec_{k - nClasses + 1}")
    own ← own.insert n target
    recNames := recNames.push target
  -- every fresh name is fresh
  for (_, f) in own.entries do
    if (lookup f).isSome then throw (.taken f)
  -- the terms, renamed by `base` and the block's own σ, on one memo
  let σ ← base.union own
  let numNested := canonicalRecs.size - nClasses
  let go : StateM RenameCache FlatBlock := do
    let mut types : Array InductiveVal := #[]
    let mut ctors : Array (Array ConstructorVal) := #[]
    for ((v, cs), f) in reps.zip freshReps do
      let ty ← renameExpr σ v.cnst.type
      types := types.push { v with
        cnst := { v.cnst with name := f, type := ty }
        all := freshReps
        ctors := v.ctors.map fresh
        numNested }
      let mut out : Array ConstructorVal := #[]
      for c in cs do
        let cty ← renameExpr σ c.cnst.type
        out := out.push { c with
          cnst := { c.cnst with name := fresh c.cnst.name, type := cty }
          induct := f }
      ctors := ctors.push out
    let mut recs : Array RecursorVal := #[]
    for ((_, rv), name) in canonicalRecs.zip recNames do
      let mut rules : Array RecursorRule := #[]
      for r in rv.rules do
        let rhs ← renameExpr σ r.rhs
        rules := rules.push { r with ctor := σ.apply r.ctor, rhs }
      let rty ← renameExpr σ rv.cnst.type
      recs := recs.push { rv with
        cnst := { rv.cnst with name, type := rty }
        all := freshReps
        rules }
    return { classes, types, ctors, recs, sigma := own }
  return go.run' {}

end Ix.AuxGen.Flat

end
