module

import ConLeche.Kernel.Inductives.StructParts
public import ConLeche.Verify.FastOps

public section

/-!
# The incremental projection residual agrees with the generator (task #175 W4c)

The cached drivers thread `structProjResidP` — the constructor
telescope peeled one earlier-projection substitute at a time — and read
each slot's type off it (`structProjTyR`); the pure checker computes
`structProjTyP` from scratch.  The two agree: the incremental residual
is the whole-spine `instPisAtLift`.
-/

namespace ConLeche

theorem structProjResidP_eq (T : Name) (nP : Nat) (cty : Expr) :
    ∀ i, structProjResidP T nP cty i
      = Expr.instPisAtLift
          (structProjPs nP ++ (List.range i).map (structProjArgP T)) cty
  | 0 => by simp [structProjResidP, List.range_zero, List.map_nil, List.append_nil]
  | i + 1 => by
    rw [structProjResidP, structProjResidP_eq T nP cty i, List.range_succ,
      List.map_append, List.map_singleton, ← List.append_assoc,
      instPisAtLift_append (structProjPs nP ++ (List.range i).map (structProjArgP T))
        [structProjArgP T i]]

end ConLeche
