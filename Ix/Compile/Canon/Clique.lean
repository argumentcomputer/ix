/-
  Ix.Compile.Canon.Clique: definition cliques, their recursive
  specifications, and their classes and canonical order (old plan M.1-M.3,
  `plans/review/auxgen-certify/PLAN.md:910-998`).

  **M.1 Clique.** The pre-definitions Lean compiled together. The caller
  reads them from the Lean environment (this module imports no Lean
  elaborator state; `Benchmarks/Canon/Census.lean` does the reading):
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

  **M.2 Specification.** Per member: universe parameters, type, and value
  (`EqnInfo.value`, Lean's pre-definition body after nested-proof
  abstraction; the `_unsafe_rec` body with witnesses renamed back to their
  members; the definition's value for `unsafe`), plus the pinned choice:
  the recursive-argument position `recArgPos` for structural recursion.
  Lean's well-founded measure is not recorded in `EqnInfo` (only the
  argument packer), so it is not part of the specification here; it lives
  only inside the `_mutual` definition's `WellFounded.fix` relation.

  **M.3 Classes and order.** `Classes.sortClasses` over the specifications
  as definitions, with clique members as the in-block names, so recursive
  calls compare by class index. The recursion method is the same for every
  member of a clique; the pinned position enters as a header key: the value
  compared is `(recArgPos) value`, a literal applied to the body, so the
  position is compared first and strongly.
-/
module
public import Ix.Environment
public import Ix.Mutual
public import Ix.Compile.Canon.Expr
public import Ix.Compile.Canon.Order
public import Ix.Compile.Canon.Classes
public section

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

/-- The specification as the definition the comparator sorts. -/
def CliqueMember.toMutConst (m : CliqueMember) : MutConst :=
  let value := match m.recArgPos with
    | some p => Expr.mkApp (Expr.mkLit (.natVal p)) m.value
    | none => m.value
  .defn { name := m.name, levelParams := m.levelParams, type := m.type, kind := .defn,
          value, hints := .opaque, safety := .safe, all := #[] }

/-- Classes and canonical order of a clique (M.3). -/
def cliqueClasses (rules : Rules) (addr? : Name → Option Address) (c : Clique) :
    Except String (Array (Array Name) × SortStats) := do
  let (cls, st) ← sortClasses rules addr? (c.members.toList.map (·.toMutConst))
  return (classNames cls, st)

/-- The clique changes under the canonical order (M.6, without the
dependence on changed blocks): classes merge, or the representatives are
not in Lean's order. -/
def cliqueChanged (c : Clique) (classes : Array (Array Name)) : Bool :=
  classes.size != c.members.size ||
    classes.filterMap (·[0]?) != c.names

/-- The type former of a structural member's recursive argument: the head
constant of the `recArgPos`-th binder's domain. -/
def recArgTypeFormer (m : CliqueMember) : Option Name := do
  let p ← m.recArgPos
  let (bs, _) := peelForalls (p + 1) m.type #[]
  let (_, dom, _) ← bs[p]?
  match getAppFnArgs (stripMdata dom) with
  | (.const n _ _, _) => some n
  | _ => none

/-- Some type former carries two or more of the clique's functions. -/
def severalPerTypeFormer (c : Clique) : Bool :=
  let formers := c.members.filterMap recArgTypeFormer
  formers.zipIdx.any fun (f, i) => (formers.extract (i + 1) formers.size).contains f

/-- Rename `_unsafe_rec` witnesses back to their members in a value. -/
def unsafeRecToMembers (members : Array Name) (e : Expr) : Expr :=
  let m : Std.HashMap Name Name := members.foldl (init := {}) fun m n =>
    m.insert (Name.mkStr n "_unsafe_rec") n
  replaceConstNames m e

end Ix.Compile.Canon

end
