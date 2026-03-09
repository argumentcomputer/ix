/-
  Kernel2 Quote: Read-back helpers for Val → Expr conversion.

  The full `quote` function lives in the mutual block in Infer.lean (because
  quoting under binders requires eval, and quoting spine requires forceThunk).
  This file provides non-monadic helpers used by quote.
-/
import Ix.Kernel2.Value

namespace Ix.Kernel2

open Ix.Kernel (MetaMode MetaField)

/-! ## Non-monadic quote helpers -/

/-- Convert a de Bruijn level to a de Bruijn index at the given quoting depth. -/
def levelToIndex (depth : Nat) (level : Nat) : Nat :=
  depth - 1 - level

/-- Quote a Head to an Expr at the given depth.
    `names` maps de Bruijn levels to binder names (populated by `quote`). -/
def quoteHead (h : Head m) (d : Nat) (names : Array (KMetaField m Ix.Name) := #[]) : KExpr m :=
  match h with
  | .fvar level _ =>
    let idx := levelToIndex d level
    .bvar idx (names[level]?.getD default)
  | .const addr levels name => .const addr levels name

end Ix.Kernel2
