/-
  Ix.Theory.Quotient: Well-formed quotient type declarations and reduction rules.

  Formalizes the four quotient constants (Quot, Quot.mk, Quot.lift, Quot.ind)
  and their two computation rules as `SDefEq` entries:

  1. **Quot.lift**: `Quot.lift.{u,v} α r β f h (Quot.mk.{u} α r a) ≡ f a : β`
  2. **Quot.ind**:  `Quot.ind.{u} α r β h (Quot.mk.{u} α r a) ≡ h a : β (Quot.mk α r a)`

  All reduction rules are encoded for the `extra` rule in the typing judgment.
  Arguments are universally quantified over closed expressions to ensure
  compatibility with `WFClosed`.

  Reference: docs/theory/kernel.md Phase 8.
-/
import Ix.Theory.Inductive

namespace Ix.Theory

open SExpr

/-! ## Quot.lift rule construction

    Quot.lift has 6 spine arguments: [α, r, β, f, h, q].
    When q = Quot.mk α r a, the reduction is:
    ```
    Quot.lift.{u,v} α r β f h (Quot.mk.{u} α r a) ≡ f a : β
    ``` -/

/-- Assemble the Quot.lift reduction SDefEq. -/
def mkQuotLiftRule (liftId ctorId : Nat)
    (ls_lift ls_ctor : List SLevel)
    (α r β f h a : TExpr) : SDefEq :=
  { uvars := 0,
    lhs := mkApps (.const liftId ls_lift)
      [α, r, β, f, h, mkApps (.const ctorId ls_ctor) [α, r, a]],
    rhs := .app f a,
    type := β }

theorem mkQuotLiftRule_closed {liftId ctorId : Nat}
    {ls_lift ls_ctor : List SLevel}
    {α r β f h a : TExpr}
    (hα : α.Closed) (hr : r.Closed) (hβ : β.Closed)
    (hf : f.Closed) (hh : h.Closed) (ha : a.Closed) :
    let rl := mkQuotLiftRule liftId ctorId ls_lift ls_ctor α r β f h a
    rl.lhs.Closed ∧ rl.rhs.Closed ∧ rl.type.Closed := by
  refine ⟨?_, ⟨hf, ha⟩, hβ⟩
  unfold mkQuotLiftRule
  -- LHS: mkApps (const liftId ls_lift) [α, r, β, f, h, mkApps (const ctorId ls_ctor) [α, r, a]]
  apply mkApps_closed (const_closed _ _)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hα
  · exact hr
  · exact hβ
  · exact hf
  · exact hh
  · exact mkApps_closed (const_closed _ _)
      (fun x hx => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hα
        · exact hr
        · exact ha)

/-! ## Quot.ind rule construction

    Quot.ind has 5 spine arguments: [α, r, β, h, q].
    When q = Quot.mk α r a, the reduction is:
    ```
    Quot.ind.{u} α r β h (Quot.mk.{u} α r a) ≡ h a : β (Quot.mk.{u} α r a)
    ``` -/

/-- Assemble the Quot.ind reduction SDefEq. -/
def mkQuotIndRule (indId ctorId : Nat)
    (ls_ind ls_ctor : List SLevel)
    (α r β h a : TExpr) : SDefEq :=
  { uvars := 0,
    lhs := mkApps (.const indId ls_ind)
      [α, r, β, h, mkApps (.const ctorId ls_ctor) [α, r, a]],
    rhs := .app h a,
    type := .app β (mkApps (.const ctorId ls_ctor) [α, r, a]) }

theorem mkQuotIndRule_closed {indId ctorId : Nat}
    {ls_ind ls_ctor : List SLevel}
    {α r β h a : TExpr}
    (hα : α.Closed) (hr : r.Closed) (hβ : β.Closed)
    (hh : h.Closed) (ha : a.Closed) :
    let rl := mkQuotIndRule indId ctorId ls_ind ls_ctor α r β h a
    rl.lhs.Closed ∧ rl.rhs.Closed ∧ rl.type.Closed := by
  have hmk : (mkApps (.const ctorId ls_ctor) [α, r, a] : TExpr).Closed :=
    mkApps_closed (const_closed _ _)
      (fun x hx => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hα
        · exact hr
        · exact ha)
  refine ⟨?_, ⟨hh, ha⟩, ⟨hβ, hmk⟩⟩
  unfold mkQuotIndRule
  apply mkApps_closed (const_closed _ _)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact hα
  · exact hr
  · exact hβ
  · exact hh
  · exact hmk

/-! ## WFQuot: well-formed quotient type declaration

    Asserts that the environment contains all four quotient constants
    (Quot, Quot.mk, Quot.lift, Quot.ind) and the two computation rules.

    Universe parameter counts are hardcoded:
    - Quot, Quot.mk, Quot.ind: 1 universe param (u)
    - Quot.lift: 2 universe params (u, v) -/

/-- Well-formed quotient type declaration in the specification environment. -/
structure WFQuot (env : SEnv) where
  -- Constant IDs
  typeId : Nat
  ctorId : Nat
  liftId : Nat
  indId  : Nat
  -- Types
  typeType : TExpr
  ctorType : TExpr
  liftType : TExpr
  indType  : TExpr
  -- Closedness
  typeType_closed : typeType.Closed
  ctorType_closed : ctorType.Closed
  liftType_closed : liftType.Closed
  indType_closed  : indType.Closed
  -- Constants exist in the environment
  hasType : env.constants typeId = some (.quot 1 typeType .type)
  hasCtor : env.constants ctorId = some (.quot 1 ctorType .ctor)
  hasLift : env.constants liftId = some (.quot 2 liftType .lift)
  hasInd  : env.constants indId  = some (.quot 1 indType  .ind)
  -- Quot.lift reduction: for all closed arguments
  hasLiftRule : ∀ (u v : SLevel) (α r β f h a : TExpr),
    α.Closed → r.Closed → β.Closed → f.Closed → h.Closed → a.Closed →
    env.defeqs (mkQuotLiftRule liftId ctorId [u, v] [u] α r β f h a)
  -- Quot.ind reduction: for all closed arguments
  hasIndRule : ∀ (u : SLevel) (α r β h a : TExpr),
    α.Closed → r.Closed → β.Closed → h.Closed → a.Closed →
    env.defeqs (mkQuotIndRule indId ctorId [u] [u] α r β h a)

/-! ### WFClosed compatibility -/

/-- Every Quot.lift defeq from a `WFQuot` has closed lhs/rhs/type. -/
theorem WFQuot.lift_defeq_closed (_wfq : WFQuot env)
    {u v : SLevel} {α r β f h a : TExpr}
    (hα : α.Closed) (hr : r.Closed) (hβ : β.Closed)
    (hf : f.Closed) (hh : h.Closed) (ha : a.Closed) :
    let rl := mkQuotLiftRule _wfq.liftId _wfq.ctorId [u, v] [u] α r β f h a
    rl.lhs.Closed ∧ rl.rhs.Closed ∧ rl.type.Closed :=
  mkQuotLiftRule_closed hα hr hβ hf hh ha

/-- Every Quot.ind defeq from a `WFQuot` has closed lhs/rhs/type. -/
theorem WFQuot.ind_defeq_closed (_wfq : WFQuot env)
    {u : SLevel} {α r β h a : TExpr}
    (hα : α.Closed) (hr : r.Closed) (hβ : β.Closed)
    (hh : h.Closed) (ha : a.Closed) :
    let rl := mkQuotIndRule _wfq.indId _wfq.ctorId [u] [u] α r β h a
    rl.lhs.Closed ∧ rl.rhs.Closed ∧ rl.type.Closed :=
  mkQuotIndRule_closed hα hr hβ hh ha

/-! ## Sanity checks -/

private abbrev u₀ : SLevel := .zero
private abbrev u₁ : SLevel := .succ .zero

-- Quot.lift rule: RHS = f a
#guard (mkQuotLiftRule 3 1 [u₀, u₁] [u₀]
    (.const 10 []) (.const 11 []) (.const 12 [])
    (.const 13 []) (.const 14 []) (.const 15 []) : SDefEq).rhs ==
  .app (.const 13 []) (.const 15 [])

-- Quot.lift rule: LHS has the expected structure
#guard (mkQuotLiftRule 3 1 ([u₀, u₁] : List SLevel) [u₀]
    (.const 10 []) (.const 11 []) (.const 12 [])
    (.const 13 []) (.const 14 []) (.const 15 []) : SDefEq).lhs ==
  mkApps (.const 3 [u₀, u₁])
    [.const 10 [], .const 11 [], .const 12 [], .const 13 [], .const 14 [],
     mkApps (.const 1 [u₀]) [.const 10 [], .const 11 [], .const 15 []]]

-- Quot.lift rule: type = β
#guard (mkQuotLiftRule 3 1 ([u₀, u₁] : List SLevel) [u₀]
    (.const 10 []) (.const 11 []) (.const 12 [])
    (.const 13 []) (.const 14 []) (.const 15 []) : SDefEq).type ==
  .const 12 []

-- Quot.ind rule: RHS = h a
#guard (mkQuotIndRule 4 1 ([u₀] : List SLevel) [u₀]
    (.const 10 []) (.const 11 []) (.const 12 [])
    (.const 13 []) (.const 14 []) : SDefEq).rhs ==
  .app (.const 13 []) (.const 14 [])

-- Quot.ind rule: type = β (Quot.mk α r a)
#guard (mkQuotIndRule 4 1 ([u₀] : List SLevel) [u₀]
    (.const 10 []) (.const 11 []) (.const 12 [])
    (.const 13 []) (.const 14 []) : SDefEq).type ==
  .app (.const 12 [])
    (mkApps (.const 1 [u₀]) [.const 10 [], .const 11 [], .const 14 []])

end Ix.Theory
