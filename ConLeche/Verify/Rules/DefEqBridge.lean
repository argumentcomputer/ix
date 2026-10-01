module

public import ConLeche.Verify.Rules.Defs
import ConLeche.Verify.Rules.DefEqStepInv
import ConLeche.Verify.Rules.Certs
import ConLeche.Verify.Rules.RedBridge
import ConLeche.Rules.Derived

public section

/-!
# The definitional-equality bridge (task #305, lane B3)

`isDefEqCore` at `fuel + 1` from the five bridges at `fuel`: one
`defeqStep` under a bridged continuation is a derivation, the loop
follows by induction on its budget, the body is the loop at
`defeqLoopFuel`.

The inversion is `Verify/Rules/DefEqStepInv.lean`'s `defeqStep_inv`
(the lane's by-product: the model tier's `defeqStep_claim`,
`Model/Steps/DefEq.lean:514`, inverts the step inline against its
continuation contract `DefEqCont`, and nothing in `Verify/` did).  It
hands back the prefix's three exits, the two `whnfCore` reducts, and
under them the nine ways the step ends — the last being
`DefeqStuckExit`, the stuck tree's seventeen.  Each lands on one rule:

| exit (`Core.lean`) | rule |
|---|---|
| `a == b` (`:1463`) | `DefEq.refl` |
| the `Bool.true` shortcut (`:1468-1471`) | `boolTrueShortcut_bridge` |
| `whnfCore` both, `a' == b'` (`:1466-1472`) | `DefEq.redBoth` + `refl` |
| `propIrrel` (`:1498-1500`) | `redBoth` + `propIrrel_bridge` |
| `reduceNat` left / right (`:1517-1529`) | `redBoth` + `redL (reduceNat_bridge)` / `redR` + continuation |
| lazy δ, one side / both (`:1537-1577`) | `redBoth` + `deltaL` / `deltaR` / `deltaBoth` + continuation |
| same-head short-circuit (`:1568-1571`) | `redBoth` + `defeqSpine_bridge` |
| sorts / literals / fvars / consts (`:1581-1626`) | `sort` / `lit` / `fvar` / `const`, else `stuckIrrel_bridge` |
| `lit` vs `Nat.zero` / `Nat.succ` (`:1586-1603`) | `natZero`(`R`) / `natSucc`(`R`) with the continuation |
| string literal vs `String.ofList` (`:1610-1617`) | `strLitL` / `strLitR` with the continuation |
| ∀ / λ congruence (`:1627-1651`) | `forallE` / `lam` |
| stuck applications (`:1652-1678`) | `spine` (head + `defEqList_bridge`), else `stuckIrrel_bridge` |
| stuck projections (`:1679-1689`) | `proj`, else `stuckIrrel_bridge` |
| one-sided λ (`:1690-1696`) | `etaCert_bridge` / `etaR`, else `stuckIrrel_bridge` |
| distinct heads (`:1700`) | `stuckIrrel_bridge` |

all under the `redBoth` of the two `whnfCore` reducts.
-/

namespace ConLeche.Rules

variable {env : Env} {fuel : Nat}

/-- One `defeqStep` under a bridged continuation. -/
theorem defeqStep_bridge (hwc : WhnfCoreBridge env fuel) (hw : WhnfBridge env fuel)
    (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} {k : Bool → Expr → Expr → CheckM Bool}
    (hk : ∀ {pi : Bool} {a b : Expr}, k pi a b = .ok true → DefEq env d a b)
    {pi : Bool} {a b : Expr}
    (h : defeqStep .verified (pureFns .verified env fuel) env d k pi a b = .ok true) :
    DefEq env d a b := by
  rcases defeqStep_inv h with rfl | ⟨rfl, hsc⟩ | ⟨a', b', hwa, hwb, hrest⟩
  · exact .refl
  · exact boolTrueShortcut_bridge hw hsc
  refine DefEq.redBoth (hwc hwa) (hwc hwb) ?_
  rcases hrest with rfl | hpi | ⟨a₂, hn, hk₂⟩ | ⟨b₂, hn, hk₂⟩ | ⟨a₂, hu, hk₂⟩ |
    ⟨b₂, hu, hk₂⟩ | ⟨a₂, b₂, hua, hub, hk₂⟩ | hsp | hstuck
  · exact .refl
  · exact propIrrel_bridge hw hio hpi
  · exact .redL (reduceNat_bridge hw hn) (hk hk₂)
  · exact .redR (reduceNat_bridge hw hn) (hk hk₂)
  · exact .deltaL hu (hk hk₂)
  · exact .deltaR hu (hk hk₂)
  · exact .deltaBoth hua hub (hk hk₂)
  · exact defeqSpine_bridge hd hsp
  -- the stuck tree: one rule per exit
  cases hstuck with
  | fallback hs => exact stuckIrrel_bridge hw hd hio hs
  | sort hle => exact .sort hle
  | lit => exact .refl
  | natZeroL => exact .natZero
  | natZeroR => exact .natZeroR
  | natSuccL hde => exact .natSucc (hd hde)
  | natSuccR hde => exact .natSuccR (hd hde)
  | strLitL hg hde => exact .strLitL hg (hd hde)
  | strLitR hg hde => exact .strLitR hg (hd hde)
  | fvar => exact .fvar
  | const hle => exact .const hle
  | forallE hdt hbd hpw => exact .forallE (hd hdt) (hd hbd) hpw
  | lam hdt hbd hpw => exact .lam (hd hdt) (hd hbd) hpw
  | spine hhd hls => exact .spine (hd hhd) (defEqList_bridge hd hls)
  | proj hde => exact .proj (hd hde)
  | etaL he => exact etaCert_bridge hw hd hio he
  | etaR he => exact (etaCert_bridge hw hd hio he).symm

/-- The loop at every budget. -/
theorem defeqLoop_bridge (hwc : WhnfCoreBridge env fuel) (hw : WhnfBridge env fuel)
    (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} : ∀ (n : Nat) {pi : Bool} {a b : Expr},
      defeqLoop .verified (pureFns .verified env fuel) env d n pi a b = .ok true →
      DefEq env d a b
  | 0, _, _, _, h => by
    simp [defeqLoop, throw, throwThe, MonadExceptOf.throw] at h
  | n + 1, _, _, _, h =>
    defeqStep_bridge hwc hw hd hio (defeqLoop_bridge hwc hw hd hio n) h

/-- **`isDefEqCore` at `fuel + 1`**: the loop at its budget. -/
theorem defeq_bridge_succ (hwc : WhnfCoreBridge env fuel) (hw : WhnfBridge env fuel)
    (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel) :
    DefEqBridge env (fuel + 1) := by
  intro d a b h
  rw [isDefEqCore_succ] at h
  exact defeqLoop_bridge hwc hw hd hio _ h

end ConLeche.Rules
