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
  member of a clique; the pinned choice compares **last** (owner, Q8,
  2026-10-03; design document §2.7): the value compared is `value
  (recArgPos)`, the body applied to the literal, so the position is compared
  after the type and the whole value, and a pinned choice that differs between
  presentations changes the order only when everything else ties. (Before
  2026-10-07 the literal was the function, `(recArgPos) value`, so the
  position was compared before the value, against Q8. Only the census sets
  `recArgPos`; the compiler's clique order, `Clique.cliqueOrder`, builds its
  members with `recArgPos := none`, so no compiled byte depended on it.)
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

/-- The specification as the definition the comparator sorts: the value
applied to the pinned choice, which the comparator reaches after the value
(Q8, pinned choices compare last). -/
def CliqueMember.toMutConst (m : CliqueMember) : MutConst :=
  let value := match m.recArgPos with
    | some p => Expr.mkApp m.value (Expr.mkLit (.natVal p))
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

/-- Q6 (owner, 2026-10-03), first source: the canonical order of a theorem
clique (no specification, `CliqueKind.noSpec`) by its statements. The
statements are classified and ordered as Pass 1 orders specifications (each
statement compared as its own value); `σ[i]` is the canonical position of
Lean's member `i`. `none` when two statements tie: the statements do not
determine the order, and the clique keeps Lean's form (cause `NOSPEC`) unless
Q6's second source, the recovered specification, separates them (not built
here). -/
def statementOrder (rules : Rules) (addr? : Name → Option Address) (members : Array CliqueMember) :
    Except String (Option (Array Nat)) := do
  let c : Clique := { kind := .noSpec
                      members := members.map fun m => { m with value := m.type, recArgPos := none } }
  let (cls, _) ← cliqueClasses rules addr? c
  if cls.any (·.size ≥ 2) then return none
  return some (c.members.map fun m => (cls.findIdx? (·.contains m.name)).getD 0)

/-- Rename `_unsafe_rec` witnesses back to their members in a value. -/
def unsafeRecToMembers (members : Array Name) (e : Expr) : Expr :=
  let m : Std.HashMap Name Name := members.foldl (init := {}) fun m n =>
    m.insert (Name.mkStr n "_unsafe_rec") n
  replaceConstNames m e

end Ix.Compile.Canon

end
