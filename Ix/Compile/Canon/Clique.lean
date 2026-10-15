/-
  Ix.Compile.Canon.Clique: definition cliques, their recursive
  specifications, and their classes and canonical order.

  **Clique.** The pre-definitions Lean compiled together. The caller reads
  them from the Lean environment (this module imports no Lean elaborator
  state):
  * structural, well-founded and `partial_fixpoint` recursion:
    `EqnInfo.declNames` of `Lean.Elab.Structural.eqnInfoExt`,
    `Lean.Elab.WF.eqnInfoExt` and `Lean.Elab.PartialFixpoint.eqnInfoExt`
    (Lean 4.34.1, `src/lean/Lean/Elab/PreDefinition/{Structural,WF,
    PartialFixpoint}/Eqns.lean`), in Lean's clique order;
  * `partial`: the opaques' `all` (`addAndCompilePartial`), with the
    `f._unsafe_rec` witnesses as their specifications;
  * `unsafe`: the definitions' `all` (one kernel mutual block);
  * theorems and Prop-valued definitions: Lean records no `EqnInfo` and no
    `_unsafe_rec` for them (`registerEqnsInfo` is skipped), so they have no
    specification (`CliqueKind.noSpec`); their clique is their `all`.

  **Specification.** Per member: universe parameters, type, and value
  (`EqnInfo.value`, Lean's pre-definition body after nested-proof
  abstraction; the `_unsafe_rec` body with witnesses renamed back to their
  members; the definition's value for `unsafe`), plus the pinned choice:
  the recursive-argument position `recArgPos` for structural recursion.
  Lean's well-founded measure is not recorded in `EqnInfo` (only the
  argument packer), so it is not part of the specification here; it lives
  only inside the `_mutual` definition's `WellFounded.fix` relation.

  **Classes and order.** `Classes.sortClasses` over the specifications as
  definitions, with clique members as the in-block names, so recursive
  calls compare by class index. The recursion method is the same for every
  member of a clique; the pinned choice compares **last**: the value
  compared is `value (recArgPos)`, the body applied to the literal, so the
  position is compared after the type and the whole value, and a pinned
  choice that differs between presentations changes the order only when
  everything else ties.

  Not called by the compiler yet (clique transport comes with Pass 3);
  `canon-clique` tests the order.
-/
module
public import Ix.Environment
public import Ix.Mutual
public import Ix.Compile.Canon.Expr
public import Ix.Compile.Canon.Order
public import Ix.Compile.Canon.Classes
@[expose] public section

namespace Ix.Compile.Canon

open Ix (Name Level Expr MutConst)

inductive CliqueKind where
  | structural
  | wellFounded
  | partialFixpoint
  /-- Theorems and Prop-valued definitions: no specification. -/
  | noSpec
  | «partial»
  | «unsafe»
  deriving BEq, Repr, Inhabited, Hashable

def CliqueKind.name : CliqueKind → String
  | .structural => "structural"
  | .wellFounded => "well-founded"
  | .partialFixpoint => "partial_fixpoint"
  | .noSpec => "theorem / Prop (no specification)"
  | .partial => "partial"
  | .unsafe => "unsafe"

/-- One member's recursive specification. -/
structure CliqueMember where
  name : Name
  levelParams : Array Name
  type : Expr
  value : Expr
  recArgPos : Option Nat := none
  deriving Inhabited

/-- A clique in Lean's order. -/
structure Clique where
  kind : CliqueKind
  members : Array CliqueMember
  deriving Inhabited

def Clique.names (c : Clique) : Array Name := c.members.map (·.name)

/-- The specification as the definition the comparator sorts: the value
applied to the pinned choice, which the comparator reaches after the value
(pinned choices compare last). -/
def CliqueMember.toMutConst (m : CliqueMember) : MutConst :=
  let value := match m.recArgPos with
    | some p => Expr.mkApp m.value (Expr.mkLit (.natVal p))
    | none => m.value
  .defn { name := m.name, levelParams := m.levelParams, type := m.type, kind := .defn,
          value, hints := .opaque, safety := .safe, all := #[] }

/-- Classes and canonical order of a clique. -/
def cliqueClasses (rules : Rules) (addr? : Name → Option Address) (c : Clique) :
    Except String (Array (Array Name) × SortStats) := do
  let (cls, st) ← (sortClasses rules addr? (c.members.toList.map (·.toMutConst))).mapError toString
  return (classNames cls, st)

end Ix.Compile.Canon

end
