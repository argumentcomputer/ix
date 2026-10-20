module

public import IxC.Kernel.Ixon.Prelude

@[expose] public section

/-!
# The prelude's shape (S1, fact (ii))

`preludeFor` ends with `checkPreludeShape`: the prelude it returns names the
pinned prelude roles (`Ix.Kernel.preludeShape`), declaration by declaration,
in order. So under every table it returns a prelude for, at every mode, the
prelude's declarations name the same role keys in the same order
(`preludeFor_shape`), and there are `preludeSize` of them
(`preludeFor_size`). The union of S1 takes the two lists' fronts from it: the
Source side's prelude (`builtinPrelude`, the default table at Source mode)
and the certificate's (`preludeFor t`) list the same twelve declarations' role
keys in the same order.
-/

namespace Ix.Kernel.Reader

open Ix.Kernel

variable {md : Mode}

theorem checkPreludeShape_ok {pre : Prelude md} (h : checkPreludeShape pre = .ok ()) :
    pre.ix.decls.toList.map (·.names) = preludeShape.map (·.map Key.role) := by
  unfold checkPreludeShape at h
  dsimp only at h
  split at h
  · rename_i heq
    exact beq_iff_eq.mp heq
  · exact nomatch h

/-- **Fact (ii)**: a prelude `preludeFor` returns names the pinned prelude
roles, declaration by declaration, in order. -/
theorem preludeFor_shape {t : RoleTable} {pre : Prelude md} (h : preludeFor t = .ok pre) :
    pre.ix.decls.toList.map (·.names) = preludeShape.map (·.map Key.role) := by
  unfold preludeFor at h
  cases hr : (preludeRead t : Except String (Prelude md)) with
  | error e => rw [hr] at h; exact nomatch h
  | ok pre' =>
    rw [hr] at h
    change (checkPreludeShape pre' >>= fun _ => pure pre') = .ok pre at h
    cases hc : checkPreludeShape pre' with
    | error e => rw [hc] at h; exact nomatch h
    | ok u =>
      rw [hc] at h
      obtain rfl : pre' = pre := Except.ok.inj h
      exact checkPreludeShape_ok hc

/-- A prelude `preludeFor` returns has `preludeSize` declarations. -/
theorem preludeFor_size {t : RoleTable} {pre : Prelude md} (h : preludeFor t = .ok pre) :
    pre.ix.decls.size = preludeSize := by
  have := congrArg List.length (preludeFor_shape h)
  simpa [preludeSize] using this

/-- **Fact (ii), the default table's prelude** (`builtinPrelude`, Source
mode's). -/
theorem builtinPrelude_shape {pre : Prelude md} (h : builtinPrelude = .ok pre) :
    pre.ix.decls.toList.map (·.names) = preludeShape.map (·.map Key.role) := by
  unfold builtinPrelude at h
  cases ht : defaultTable with
  | error e => rw [ht] at h; exact nomatch h
  | ok t =>
    rw [ht] at h
    exact preludeFor_shape h

end Ix.Kernel.Reader
