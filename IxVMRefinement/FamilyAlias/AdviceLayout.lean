import IxVMRefinement.FamilyAlias.Check

/-! # From IxC's modeled install to the advice layout

IxC's own fold installs a mutual or nested block with its in-process model at the derived keys:
the model of member `X` is a definition at `auxKey X .model` with `X`'s own level parameters, and
the theorem of rule `j` of recursor `R` is stored at `auxKey (auxKey R .model) (.iota j)` with
`R`'s level parameters.

The circuit sees the same model as advice records at keys of their own, each definition and
theorem read with its level parameters at positions. This module states the passage as
functions of the environment IxC's fold stores (`ModeledFamily`):

* `advicePrefix`: the prefix in the advice layout. Every stored constant that is not a member of
  the block is kept; a constant of the model moves to its advice key (`adviceKey`), its constants
  renamed, and a definition's or theorem's level parameters renamed to positions.
* `familyAliases`: the alias group. The alias of a member keeps the model's declared type (the
  member's annotated type renamed to the model keys) and its level parameters, and its value is
  the advice constant at those parameters.
* **The rule copy** (`ruleCopy`): the alias at an `iota` key keeps the stored statement, with the
  binder domains of its telescope renamed to the advice keys. Its head (the recursor's model key),
  the head of its major premise and a nested rule's pins stay over the model keys, as the record's
  literal conjuncts read them; the binder domains are over the advice keys, so that the alias
  renaming fixes the leaf annotations of the opened statement.
* `familyTable`, `annotatedTypes`, `annotatedRules`: the alias table and the annotated data the
  record search takes.

The advice keys here are placeholders (`adviceKey`: an address made of the model constant's
position), since a model constant's own address is a hash of its record.
-/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal BinderMeta RecRule IndCaps
  LevelParam ReducibilityHint Derived auxKey)

set_option linter.unusedVariables false

/-- **A block as IxC's fold installs it with its in-process model.** -/
structure ModeledFamily where
  /-- the block, as read: types, constructors, recursors -/
  block : List (ConstantInfo .anon)
  /-- the environment after the block, newest first: the block's members, the model at the
  derived keys, the prefix -/
  stored : List (ConstantInfo .anon)

namespace ModeledFamily

/-- The block's names. -/
def names (m : ModeledFamily) : List KKey := m.block.map (·.name)

/-- A derived key rooted at a member of the block: a key of the block's model. -/
def isModelKey (m : ModeledFamily) (k : KKey) : Bool :=
  match k with
  | .aux _ _ => m.names.contains k.base
  | _ => false

/-- The model's keys, oldest first. -/
def modelKeys (m : ModeledFamily) : List KKey :=
  ((m.stored.map (·.name)).reverse).filter m.isModelKey

/-- The placeholder address of the model constant at position `i`. -/
def adviceAddress (i : Nat) : _root_.Address :=
  ⟨⟨#[0xAD, UInt8.ofNat (i / 256), UInt8.ofNat (i % 256)]⟩⟩

/-- The pairs (model key, advice key), oldest first. -/
def adviceKeys (m : ModeledFamily) : List (KKey × KKey) :=
  m.modelKeys.zipIdx.map fun p => (p.1, Key.id (adviceAddress p.2))

/-- **The renaming to the advice keys**: a model key goes to its advice key. -/
def adviceRen (m : ModeledFamily) : KKey → KKey := aliasMap m.adviceKeys

end ModeledFamily

/-- A rule with its constants renamed. -/
def renameRule (g : KKey → KKey) (r : RecRule .anon) : RecRule .anon :=
  { r with ctor := g r.ctor, rhs := r.rhs.renameConsts g,
           fire := match r.fire with
             | .nested lvls pins => .nested lvls (pins.map (·.renameConsts g))
             | .plain => .plain
             | .inert => .inert }

/-- **A model constant in the advice layout**: at its advice key, its constants renamed; a
definition, theorem or axiom with its level parameters at positions. A projection table has no
advice form. -/
def adviceConst (g : KKey → KKey) : ConstantInfo .anon → Option (ConstantInfo .anon)
  | .axiomInfo cv =>
    some (.axiomInfo ⟨g cv.name, List.range cv.levelParams.length,
      posOf cv.levelParams (cv.type.renameConsts g)⟩)
  | .defnInfo cv v hint =>
    some (.defnInfo ⟨g cv.name, List.range cv.levelParams.length,
      posOf cv.levelParams (cv.type.renameConsts g)⟩
      (posOf cv.levelParams (v.renameConsts g)) hint)
  | .thmInfo cv v =>
    some (.thmInfo ⟨g cv.name, List.range cv.levelParams.length,
      posOf cv.levelParams (cv.type.renameConsts g)⟩
      (posOf cv.levelParams (v.renameConsts g)))
  | .indInfo cv caps =>
    some (.indInfo ⟨g cv.name, cv.levelParams, cv.type.renameConsts g⟩
      { caps with etaCtor := caps.etaCtor.map g })
  | .ctorInfo cv nP nF =>
    some (.ctorInfo ⟨g cv.name, cv.levelParams, cv.type.renameConsts g⟩ nP nF)
  | .recInfo cv mI rP rules =>
    some (.recInfo ⟨g cv.name, cv.levelParams, cv.type.renameConsts g⟩ mI rP
      (rules.map (renameRule g)))
  | .projInfo _ => none

/-- **The prefix in the advice layout**, newest first. -/
def advicePrefix (m : ModeledFamily) : List (ConstantInfo .anon) :=
  m.stored.filterMap fun c =>
    if m.names.contains c.name then none
    else if m.isModelKey c.name then adviceConst m.adviceRen c
    else some c

/-- The binder domains of a statement's telescope, renamed. -/
def renameDomains (g : KKey → KKey) : KExpr → KExpr
  | .forallE ty body mb => .forallE (ty.renameConsts g) (renameDomains g body) mb
  | e => e

/-- The alias at a model key: a definition by the advice constant at the alias's own level
parameters. -/
def aliasAt (g : KKey → KKey) (k : KKey) (lps : List LevelParam) (ty : KExpr) :
    ConstantInfo .anon :=
  .defnInfo ⟨k, lps, ty⟩ (.const (g k) (lps.map .param)) .abbrev

/-- The stored constant at a key. -/
def storedAt (m : ModeledFamily) (k : KKey) : Option (ConstantInfo .anon) :=
  m.stored.find? (·.name == k)

/-- **A member's alias**: the model's declared type and level parameters, as IxC stores them. -/
def memberAlias (m : ModeledFamily) (x : KKey) : Option (ConstantInfo .anon) :=
  (storedAt m (auxKey x .model)).map fun c =>
    aliasAt m.adviceRen (auxKey x .model) c.toConstantVal.levelParams c.toConstantVal.type

/-- **The rule copy**: the stored statement of rule `j` of recursor `x`, its telescope's binder
domains renamed to the advice keys. -/
def ruleCopy (m : ModeledFamily) (x : KKey) (j : Nat) : Option (ConstantInfo .anon) :=
  (storedAt m (auxKey (auxKey x .model) (.iota j))).map fun c =>
    aliasAt m.adviceRen (auxKey (auxKey x .model) (.iota j)) c.toConstantVal.levelParams
      (renameDomains m.adviceRen c.toConstantVal.type)

/-- The rule copies of a member: none unless it is a recursor. -/
def ruleCopies (m : ModeledFamily) : ConstantInfo .anon → List (ConstantInfo .anon)
  | .recInfo cv _ _ rules => (List.range rules.length).filterMap (ruleCopy m cv.name)
  | _ => []

/-- **The alias group of the family**, newest first: the rule copies, then the members' aliases
in the reverse of the block's order. -/
def familyAliases (m : ModeledFamily) : List (ConstantInfo .anon) :=
  (m.block.flatMap (ruleCopies m)).reverse ++
    (m.block.filterMap fun c => memberAlias m c.name).reverse

/-- **The alias table of the family**: each alias key with its advice key. -/
def familyTable (m : ModeledFamily) : List (KKey × KKey) :=
  (familyAliases m).map fun a => (a.name, m.adviceRen a.name)

/-- The annotated types of the listed members, as IxC stores them. -/
def annotatedTypes (m : ModeledFamily) (ms : List (ConstantInfo .anon)) : List KExpr :=
  ms.filterMap fun c => (storedAt m c.name).map (·.toConstantVal.type)

/-- The annotated right-hand sides of the listed recursors' rules, as IxC stores them. -/
def annotatedRules (m : ModeledFamily) (rs : List (ConstantInfo .anon)) : List (List KExpr) :=
  rs.map fun c =>
    match storedAt m c.name with
    | some (.recInfo _ _ _ rules) => rules.map (·.rhs)
    | _ => []

end IxVM.Refinement.Decl.FamilyAlias
