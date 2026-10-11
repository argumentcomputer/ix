/-
  Ix.Compile.Canon.NameMap: the map `N` from every Lean name of a block or
  clique to its canonical position (Phase A §3.1, "Output of Pass 1").

  * a member `T` of `all`: its component and its class;
  * a constructor `T.c` (index `k`): its member's position and `k`;
  * a recursor `T.rec` (and `T.recOn`, `T.casesOn`, `T.below`,
    `T.brecOn`, which hang off the member in Lean's naming): the member's
    position;
  * Lean's nested auxiliaries `all₀.rec_j`, `all₀.below_j`,
    `all₀.brecOn_j` (`j = 1, …`): the component that discovers source
    position `j - 1` and its canonical auxiliary position (`perm`), or
    `evaporated` / `outside` when it has none;
  * a clique member: its class in the clique's canonical order.

  Names of auxiliaries Lean did not export are not in the map; the map is
  built from the canonical data only, never from the environment's names.
-/
module
public import Ix.Environment
public import Ix.Compile.Canon.Expr
public import Ix.Compile.Canon.Block
public import Ix.Compile.Canon.Clique
public section

namespace Ix.Compile.Canon

open Ix (Name ConstantInfo)

inductive CanonPos where
  /-- Component `comp`, class `cls` (members and their recursors). -/
  | member (comp cls : Nat)
  /-- Constructor `ctor` of the member at `(comp, cls)`. -/
  | ctor (comp cls ctor : Nat)
  /-- Canonical nested auxiliary `aux` of component `comp`. -/
  | aux (comp aux : Nat)
  /-- A source nested position no component discovers, aliased to the
  external recursor. -/
  | evaporated
  /-- A source nested position owned by another component's expansion and
  absent from every canonical one (not evaporated). -/
  | outside
  /-- Class `cls` of a clique. -/
  | clique (cls : Nat)
  deriving BEq, Repr, Inhabited, Hashable

/-- The suffixes that hang off a member under Lean's naming. -/
def memberSuffixes : List String := ["rec", "recOn", "casesOn", "below", "brecOn"]

/-- The name map of one block. `const?` supplies constructor lists. -/
def blockNameMap (const? : Name → Option ConstantInfo) (b : BlockCanon) :
    Std.HashMap Name CanonPos := Id.run do
  let mut m : Std.HashMap Name CanonPos := {}
  for (c, ci) in b.components.zipIdx do
    for (cls, k) in c.classes.zipIdx do
      for n in cls do
        m := m.insert n (.member ci k)
        for s in memberSuffixes do
          m := m.insert (Name.mkStr n s) (.member ci k)
        if let some (.inductInfo v) := const? n then
          for (cn, j) in v.ctors.zipIdx do
            m := m.insert cn (.ctor ci k j)
  if let some all0 := b.all[0]? then
    for (c, ci) in b.components.zipIdx do
      if let some n := c.nested then
        for (p, j) in n.perm.zipIdx do
          let pos : Option CanonPos := match p with
            | some a => some (.aux ci a)
            | none => if n.evaporated[j]?.getD false then some .evaporated else none
          match pos with
          | some pos =>
            for s in ["rec", "below", "brecOn"] do
              m := m.insert (Name.mkStr all0 s!"{s}_{j + 1}") pos
          | none =>
            for s in ["rec", "below", "brecOn"] do
              let nm := Name.mkStr all0 s!"{s}_{j + 1}"
              if !m.contains nm then m := m.insert nm .outside
  return m

/-- The name map of one clique given its classes. -/
def cliqueNameMap (classes : Array (Array Name)) : Std.HashMap Name CanonPos :=
  classes.zipIdx.foldl (init := {}) fun m (cls, k) =>
    cls.foldl (init := m) fun m n => m.insert n (.clique k)

end Ix.Compile.Canon

end
