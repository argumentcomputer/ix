/-
  Ix.Compile.Pass.Clique.Order: the canonical order of a theorem clique by
  its statements.

  A clique without a specification (theorems and Prop-valued definitions,
  `CliqueKind.noSpec`) has its statements as its only presentation-invariant
  data. `statementOrder` classifies and orders them as Pass 1 orders
  specifications (`Ix.Compile.Canon.cliqueClasses`, each statement compared as
  its own value). When two statements tie, the statements do not determine the
  order (`none`); the recovery's specifications (`Recover.cliqueOrder`) may
  still separate them, and otherwise the clique keeps Lean's form (cause
  `NOSPEC`).

  The Rust twin is `pass3::clique::order` (`statement_order`).
-/
module
public import Ix.Compile.Canon.Clique
@[expose] public section

namespace Ix.Compile.Pass.Clique

open Ix (Name)
open Ix.Compile.Canon (Rules Clique CliqueMember cliqueClasses)

/-- The canonical order of a theorem clique by its statements: `σ[i]` is the
canonical position of Lean's member `i`, or `none` when two statements tie
(a class of two or more). An error is the comparator's, or a member the
classes do not contain. -/
def statementOrder (rules : Rules) (addr? : Name → Option Address) (members : Array CliqueMember) :
    Except String (Option (Array Nat)) := do
  let c : Clique := { kind := .noSpec
                      members := members.map fun m => { m with value := m.type, recArgPos := none } }
  let (cls, _) ← cliqueClasses rules addr? c
  if cls.any (·.size ≥ 2) then return none
  let some σ := c.members.mapM fun m => cls.findIdx? (·.contains m.name)
    | throw "statementOrder: a member is in no class"
  return some σ

end Ix.Compile.Pass.Clique

end
