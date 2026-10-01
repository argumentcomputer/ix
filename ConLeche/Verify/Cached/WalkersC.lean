module

public import ConLeche.Verify.Cached.GuardsC

public section

/-!
# The cached driver's walkers are the plain ones (task #214)

`structWalkersC` — the memoised constant-resolution gate and the
memoised projection-body builder the cached driver hands the direct
installers (`StructWalkers`, `ConLeche/Kernel/Inductives/StructInstallF.lean`) —
is equal to the specification record `StructWalkers.plain`: the gate by
`constsResolveFC_spec` (task #171), the builder by
`instantiate1LiftC_spec` (`OpsC.lean`) through the two loops.  Every
bridge lemma about the driver rewrites by `structWalkersC_eq_plain`
once and then reads the plain installer.
-/

namespace ConLeche.Cached

open ConLeche

theorem instPisAtLiftC_eq : ∀ (as : List Expr) (e : Expr),
    instPisAtLiftC as e = Expr.instPisAtLift as e
  | [], _ => rfl
  | _ :: _, .bvar _ => rfl
  | _ :: _, .fvar .. => rfl
  | _ :: _, .sort _ => rfl
  | _ :: _, .const .. => rfl
  | _ :: _, .app .. => rfl
  | _ :: _, .lam .. => rfl
  | _ :: _, .letE .. => rfl
  | _ :: _, .lit _ => rfl
  | _ :: _, .proj .. => rfl
  | a :: as, .forallE _ body _ => by
    simp only [instPisAtLiftC, Expr.instPisAtLift, Expr.instantiate1LiftC_spec]
    exact instPisAtLiftC_eq as _

theorem structProjBodiesGoC_eq (T : Name) : ∀ (k i : Nat) (r : Expr),
    structProjBodiesGoC T k i r = structProjBodiesGo T k i r
  | 0, _, _ => rfl
  | _ + 1, _, .bvar _ => rfl
  | _ + 1, _, .fvar .. => rfl
  | _ + 1, _, .sort _ => rfl
  | _ + 1, _, .const .. => rfl
  | _ + 1, _, .app .. => rfl
  | _ + 1, _, .lam .. => rfl
  | _ + 1, _, .letE .. => rfl
  | _ + 1, _, .lit _ => rfl
  | _ + 1, _, .proj .. => rfl
  | k + 1, i, .forallE fdom body _ => by
    simp only [structProjBodiesGoC, structProjBodiesGo, Expr.instantiate1LiftC_spec]
    rw [structProjBodiesGoC_eq T k (i + 1)]

theorem structProjBodiesC_eq (T : Name) (nP nF : Nat) (cty : Expr) :
    structProjBodiesC T nP nF cty = structProjBodies T nP nF cty := by
  unfold structProjBodiesC structProjBodies
  rw [instPisAtLiftC_eq]
  cases Expr.instPisAtLift (structProjPs nP) cty with
  | none => rfl
  | some r => simp only [structProjBodiesGoC_eq]

/-- **The driver's walkers are the plain ones.** -/
theorem structWalkersC_eq_plain : structWalkersC = StructWalkers.plain := by
  unfold structWalkersC StructWalkers.plain
  congr 1
  · funext fe e; exact constsResolveFC_spec
  · funext T nP nF cty; exact structProjBodiesC_eq T nP nF cty

end ConLeche.Cached
