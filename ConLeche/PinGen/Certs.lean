module

import all Init.Data.Nat.Gcd
import all Init.Data.Nat.Bitwise.Basic
@[expose] public section

/-!
# Certificate theorems for the pin-certified Nat operations (elab-time)

The characterization certificates of the pin-certified WF-recursive
`Nat` operations, elaborated against the ambient *toolchain* prelude,
where `Nat.div`/`Nat.mod`/… are the real operations.  The *statements*
fix the pinned spellings: guards via the already-certified `Nat.ble`
(never the `Nat.le`/`Nat.lt` `Prop` inductives), numerals via
`Nat.succ`/`Nat.zero` (never `OfNat`), so the model-side consumption
rides the existing `NatOpsOk` literal semantics.

The proofs are written with *controlled* dependencies: no `simp`, no
`decide` — the core lemmas (`Nat.mod_eq` …) are proved with simp steps
whose terms mention `eq_true`/`and_self` and hence `Iff`/`propext`,
which do not exist in the export stream before `Nat.mod`.  Everything
below reduces to `Eq`-rewriting, `Nat`/`Decidable` case analysis, and
prefix-present arithmetic lemmas.  (Constants that are *definitions*
outside the stream prefix are inlined by the generator; a non-prefix
*inductive* aborts the build.)

This module is part of the elab-time pin generator
(`ConLeche/PinGen.lean`); nothing in it is used by the checker at
runtime.  It is deliberately *not* a `module`: the proofs unfold core
definition bodies (`eq_def`, `rfl`-iota) that the module system hides,
and the early stream positions of `Nat.land`/`Nat.lor`/`Nat.xor` (in
the `Init.Prelude` region, before `HAnd`/`AndOp`/`testBit` even exist)
rule out the public bitwise lemma API.  It is built ahead of
`ConLeche/Kernel/NatOpPins.lean` as its own Lake target
(`ConLechePinCerts`, wired via `extraDepTargets`), and the generator
loads it by name into its full-view environment.
-/

namespace ConLeche.PinGen

/-! ## Support lemmas for `Nat.div`/`Nat.mod` -/

/-- One-step unfolding of the fuel-recursive worker (the auto-generated
`eq_def`, coerced through the definitional match reduction at `succ`). -/
private theorem divGoStep (y : Nat) (hy : 0 < y) (f x : Nat)
    (h : x < Nat.succ f) :
    Nat.div.go y hy (Nat.succ f) x h =
      dite (y ≤ x)
        (fun hle => Nat.succ (Nat.div.go y hy f (x - y)
          (Nat.div_rec_fuel_lemma hy hle h)))
        (fun _ => 0) :=
  Nat.div.go.eq_def y hy (Nat.succ f) x h

private theorem modGoStep (y : Nat) (hy : 0 < y) (f x : Nat)
    (h : x < Nat.succ f) :
    Nat.modCore.go y hy (Nat.succ f) x h =
      dite (y ≤ x)
        (fun hle => Nat.modCore.go y hy f (x - y)
          (Nat.div_rec_fuel_lemma hy hle h))
        (fun _ => x) :=
  Nat.modCore.go.eq_def y hy (Nat.succ f) x h

private theorem divGoFuelCongr (y : Nat) (hy : 0 < y) :
    ∀ (f1 x : Nat) (h1 : x < f1) (f2 : Nat) (h2 : x < f2),
      Nat.div.go y hy f1 x h1 = Nat.div.go y hy f2 x h2 := by
  intro f1
  induction f1 with
  | zero => intro x h1 f2 h2; exact absurd h1 (Nat.not_succ_le_zero x)
  | succ f1 ih =>
    intro x h1 f2 h2
    cases f2 with
    | zero => exact absurd h2 (Nat.not_succ_le_zero x)
    | succ f2 =>
      rw [divGoStep, divGoStep]
      match Nat.decLe y x with
      | .isTrue hle =>
        rw [dif_pos hle, dif_pos hle]
        exact congrArg Nat.succ (ih _ _ _ _)
      | .isFalse hnle => rw [dif_neg hnle, dif_neg hnle]

private theorem modGoFuelCongr (y : Nat) (hy : 0 < y) :
    ∀ (f1 x : Nat) (h1 : x < f1) (f2 : Nat) (h2 : x < f2),
      Nat.modCore.go y hy f1 x h1 = Nat.modCore.go y hy f2 x h2 := by
  intro f1
  induction f1 with
  | zero => intro x h1 f2 h2; exact absurd h1 (Nat.not_succ_le_zero x)
  | succ f1 ih =>
    intro x h1 f2 h2
    cases f2 with
    | zero => exact absurd h2 (Nat.not_succ_le_zero x)
    | succ f2 =>
      rw [modGoStep, modGoStep]
      match Nat.decLe y x with
      | .isTrue hle =>
        rw [dif_pos hle, dif_pos hle]
        exact ih _ _ _ _
      | .isFalse hnle => rw [dif_neg hnle, dif_neg hnle]

/-- The dispatcher, unfolded (the auto-generated `eq_def`). -/
private theorem divUnfold (x y : Nat) :
    Nat.div x y =
      dite (0 < y)
        (fun hy => Nat.div.go y hy (Nat.succ x) x (Nat.lt_succ_self x))
        (fun _ => Nat.zero) :=
  Nat.div.eq_def x y

private theorem modCoreUnfold (x y : Nat) :
    Nat.modCore x y =
      dite (0 < y)
        (fun hy => Nat.modCore.go y hy (Nat.succ x) x (Nat.lt_succ_self x))
        (fun _ => x) :=
  Nat.modCore.eq_def x y

/-- `Nat.mod` agrees with `Nat.modCore` (the dispatcher's `x`-match and
`≤`-test collapse against `modCore`'s own tests). -/
private theorem modEqModCore (x y : Nat) (hy : 0 < y) :
    Nat.mod x y = Nat.modCore x y := by
  cases x with
  | zero =>
    show Nat.zero = Nat.modCore Nat.zero y
    rw [modCoreUnfold, dif_pos hy, modGoStep,
      dif_neg (fun hle => absurd (Nat.lt_of_lt_of_le hy hle) (Nat.lt_irrefl Nat.zero))]
  | succ n =>
    show ite (y ≤ Nat.succ n) (Nat.modCore (Nat.succ n) y) (Nat.succ n) = _
    match Nat.decLe y (Nat.succ n) with
    | .isTrue hle => rw [if_pos hle]
    | .isFalse hnle =>
      rw [if_neg hnle, modCoreUnfold, dif_pos hy, modGoStep, dif_neg hnle]

/-! ## The `Nat.div`/`Nat.mod` certificate theorems -/

theorem modRecCert : ∀ (x y : Nat), Nat.ble y x = Bool.true →
    Nat.ble (Nat.succ Nat.zero) y = Bool.true →
    Nat.mod x y = Nat.mod (Nat.sub x y) y := by
  intro x y hyx h1y
  have hy : 0 < y := Nat.le_of_ble_eq_true h1y
  have hxy : y ≤ x := Nat.le_of_ble_eq_true hyx
  rw [modEqModCore x y hy, modEqModCore (Nat.sub x y) y hy,
    modCoreUnfold, modCoreUnfold, dif_pos hy, dif_pos hy,
    modGoStep, dif_pos hxy]
  exact modGoFuelCongr y hy _ _ _ _ _

theorem modBaseGtCert : ∀ (x y : Nat), Nat.ble y x = Bool.false →
    Nat.mod x y = x := by
  intro x y hf
  have hnle : ¬ (y ≤ x) := fun h =>
    Bool.noConfusion ((Nat.ble_eq_true_of_le h).symm.trans hf)
  cases x with
  | zero => rfl
  | succ n =>
    show ite (y ≤ Nat.succ n) (Nat.modCore (Nat.succ n) y) (Nat.succ n) = _
    rw [if_neg hnle]

theorem modBaseZeroCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) y = Bool.false →
    Nat.mod x y = x := by
  intro x y hf
  have hny : ¬ (0 < y) := fun h =>
    Bool.noConfusion ((Nat.ble_eq_true_of_le h).symm.trans hf)
  cases x with
  | zero => rfl
  | succ n =>
    show ite (y ≤ Nat.succ n) (Nat.modCore (Nat.succ n) y) (Nat.succ n) = _
    match Nat.decLe y (Nat.succ n) with
    | .isTrue hle => rw [if_pos hle, modCoreUnfold, dif_neg hny]
    | .isFalse hnle => rw [if_neg hnle]

theorem divRecCert : ∀ (x y : Nat), Nat.ble y x = Bool.true →
    Nat.ble (Nat.succ Nat.zero) y = Bool.true →
    Nat.div x y = Nat.succ (Nat.div (Nat.sub x y) y) := by
  intro x y hyx h1y
  have hy : 0 < y := Nat.le_of_ble_eq_true h1y
  have hxy : y ≤ x := Nat.le_of_ble_eq_true hyx
  rw [divUnfold, divUnfold, dif_pos hy, dif_pos hy, divGoStep, dif_pos hxy]
  exact congrArg Nat.succ (divGoFuelCongr y hy _ _ _ _ _)

theorem divBaseGtCert : ∀ (x y : Nat), Nat.ble y x = Bool.false →
    Nat.div x y = Nat.zero := by
  intro x y hf
  have hnle : ¬ (y ≤ x) := fun h =>
    Bool.noConfusion ((Nat.ble_eq_true_of_le h).symm.trans hf)
  rw [divUnfold]
  match Nat.decLt 0 y with
  | .isTrue hy => rw [dif_pos hy, divGoStep, dif_neg hnle]
  | .isFalse hny => rw [dif_neg hny]

theorem divBaseZeroCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) y = Bool.false →
    Nat.div x y = Nat.zero := by
  intro x y hf
  have hny : ¬ (0 < y) := fun h =>
    Bool.noConfusion ((Nat.ble_eq_true_of_le h).symm.trans hf)
  rw [divUnfold, dif_neg hny]

/-! ## `funext`-free unfolding of `WellFounded.Nat.fix`

The WF-recursive operations (`gcd`, the bit operations) compile to
`WellFounded.Nat.fix`, a *fuel*-structural recursor (`fix.go` recurses
on `Nat` fuel and calls `F x (fun y hy => go f y …)`).  The stock
unfolding `WellFounded.Nat.fix_eq` equates `F x g₁ = F x g₂` for an
*opaque* `F` and therefore needs `funext` — whose proof drags in the
`Quot` primitives, which a dependency-sliced stream need not declare
before the operation (task #113: cert residuals must lie in the
operation's own dependency cone).  For each *concrete* body the
recursive occurrences are first-order applications, so a pointwise
congruence hypothesis (`hF`) replaces `funext`: the per-op `hF` proofs
go through the `Decidable` case split of the body's `dite`s
(`dcongr`), never through function extensionality. -/

private theorem dcongr {c : Prop} [inst : Decidable c] {γ : Sort u}
    {t1 t2 : c → γ} {e1 e2 : ¬c → γ}
    (ht : ∀ h, t1 h = t2 h) (he : ∀ h, e1 h = e2 h) :
    dite c t1 e1 = dite c t2 e2 := by
  cases inst with
  | isTrue h => exact ht h
  | isFalse h => exact he h

private theorem natFixGoCongr {α : Sort u} {motive : α → Sort v}
    (h : α → Nat)
    (F : (x : α) → ((y : α) → InvImage Nat.lt h y x → motive y) → motive x)
    (hF : ∀ (x : α) (g1 g2 : (y : α) → InvImage Nat.lt h y x → motive y),
      (∀ y p, g1 y p = g2 y p) → F x g1 = F x g2) :
    ∀ (f1 : Nat) (x : α) (h1 : h x < f1) (f2 : Nat) (h2 : h x < f2),
      WellFounded.Nat.fix.go h F f1 x h1 =
        WellFounded.Nat.fix.go h F f2 x h2 := by
  intro f1
  induction f1 with
  | zero => intro x h1 f2 h2; exact absurd h1 (Nat.not_succ_le_zero (h x))
  | succ f1 ih =>
    intro x h1 f2 h2
    cases f2 with
    | zero => exact absurd h2 (Nat.not_succ_le_zero (h x))
    | succ f2 => exact hF x _ _ (fun y p => ih y _ f2 _)

private theorem natFixUnfold {α : Sort u} {motive : α → Sort v}
    (h : α → Nat)
    (F : (x : α) → ((y : α) → InvImage Nat.lt h y x → motive y) → motive x)
    (hF : ∀ (x : α) (g1 g2 : (y : α) → InvImage Nat.lt h y x → motive y),
      (∀ y p, g1 y p = g2 y p) → F x g1 = F x g2) (x : α) :
    WellFounded.Nat.fix h F x = F x (fun y _ => WellFounded.Nat.fix h F y) := by
  show WellFounded.Nat.fix.go h F (WellFounded.Nat.eager (h x + 1)) x _ = _
  refine Eq.trans
    (natFixGoCongr h F hF _ x _ (Nat.succ (h x)) (Nat.lt_succ_self _)) ?_
  exact hF x _ _ (fun y p => natFixGoCongr h F hF (h x) y _ _ _)

private theorem bleOneFalse {x : Nat}
    (h : Nat.ble (Nat.succ Nat.zero) x = Bool.false) : x = 0 := by
  cases x with
  | zero => rfl
  | succ n => exact Bool.noConfusion h

private theorem bleOneTrue {x : Nat}
    (h : Nat.ble (Nat.succ Nat.zero) x = Bool.true) : x ≠ 0 :=
  fun hz => by rw [hz] at h; exact Bool.noConfusion h

/-! ## The `Nat.gcd` certificate theorems

`Nat.gcd` compiles to `WellFounded.Nat.fix` over the packed `PSigma`
argument; its one-step unfolding comes from `natFixUnfold` (the stock
`Nat.gcd_succ`/`Nat.gcd_zero_left` go through the auto-generated
`gcd.eq_def`, whose proof mentions `funext`). -/

private theorem gcdUnfold (x y : Nat) :
    Nat.gcd x y = if x = 0 then y else Nat.gcd (Nat.mod y x) x := by
  delta Nat.gcd Nat.gcd._unary
  refine Eq.trans (natFixUnfold _ _ ?hF (PSigma.mk (β := fun _ : Nat => Nat) x y)) ?_
  case hF =>
    intro z g1 g2 hg
    cases z with
    | mk n m => exact dcongr (fun _ => rfl) (fun _ => by rw [hg])
  exact rfl

theorem gcdRecCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) x = Bool.true →
    Nat.gcd x y = Nat.gcd (Nat.mod y x) x := by
  intro x y h1x
  rw [gcdUnfold, if_neg (bleOneTrue h1x)]

theorem gcdBaseCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) x = Bool.false →
    Nat.gcd x y = y := by
  intro x y h1x
  rw [gcdUnfold, if_pos (bleOneFalse h1x)]

/-! ## The `Nat.shiftLeft`/`Nat.shiftRight` certificate theorems

Both are structurally recursive on the second argument; the guarded
recurrences reduce to the defining iota equations. -/

theorem shiftLeftRecCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) y = Bool.true →
    Nat.shiftLeft x y =
      Nat.shiftLeft (Nat.mul (Nat.succ (Nat.succ Nat.zero)) x)
        (Nat.sub y (Nat.succ Nat.zero)) := by
  intro x y h1y
  cases y with
  | zero => exact Bool.noConfusion h1y
  | succ m => rfl

theorem shiftLeftBaseCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) y = Bool.false →
    Nat.shiftLeft x y = x := by
  intro x y h1y
  cases y with
  | zero => rfl
  | succ m => exact Bool.noConfusion h1y

theorem shiftRightRecCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) y = Bool.true →
    Nat.shiftRight x y =
      Nat.div (Nat.shiftRight x (Nat.sub y (Nat.succ Nat.zero)))
        (Nat.succ (Nat.succ Nat.zero)) := by
  intro x y h1y
  cases y with
  | zero => exact Bool.noConfusion h1y
  | succ m => rfl

theorem shiftRightBaseCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) y = Bool.false →
    Nat.shiftRight x y = x := by
  intro x y h1y
  cases y with
  | zero => rfl
  | succ m => exact Bool.noConfusion h1y

/-! ## The `Nat.land`/`Nat.lor`/`Nat.xor` certificate theorems

The three bit operations are `Nat.bitwise` at `and`/`or`/`bne`.  The
pinned recurrences characterize the operation *arithmetically* — the
combined bit is `(x%2)*(y%2)` for `and`, `x%2 + y%2 - (x%2)*(y%2)` for
`or`, `(x%2 + y%2) % 2` for `bne` — so the statements mention only
already-certified ground (`add`/`sub`/`mul`/`div`/`mod`), never `Bool`
combinators or `ite`.  The recurrences hold for *all* `x`; the
statements keep the `ble` guard for uniformity with the rest of the
family (the guard is what drives the model-side strong induction).

These operations sit in the `Init.Prelude` region of the stream —
before `HAnd`/`AndOp`, `testBit`, `Trans`, `Lean.RArray` (hence before
everything `omega`/`calc`/the public bitwise API would drag in) — so
the proofs work from `Nat.bitwise.eq_def` and elementary `Nat`
arithmetic only. -/

/-- The one-step unfolding of `Nat.bitwise`, via the `funext`-free
`natFixUnfold` (the auto-generated `Nat.bitwise.eq_def`'s proof
mentions `Subsingleton`, which does not exist in the stream at the bit
operations' `Init.Prelude`-region install points, and
`WellFounded.Nat.fix_eq` mentions `funext`, which a dependency-sliced
stream need not declare; `delta` bypasses the equation compiler). -/
private theorem bitwiseUnfold (f : Bool → Bool → Bool) (x y : Nat) :
    Nat.bitwise f x y =
      if x = 0 then (if f false true = true then y else 0)
      else if y = 0 then (if f true false = true then x else 0)
      else
        if f (decide (x % 2 = 1)) (decide (y % 2 = 1)) = true
        then Nat.bitwise f (x / 2) (y / 2) + Nat.bitwise f (x / 2) (y / 2) + 1
        else Nat.bitwise f (x / 2) (y / 2) + Nat.bitwise f (x / 2) (y / 2) := by
  delta Nat.bitwise Nat.bitwise._unary
  refine Eq.trans (natFixUnfold _ _ ?hF (PSigma.mk (β := fun _ : Nat => Nat) x y)) ?_
  case hF =>
    intro z g1 g2 hg
    cases z with
    | mk n m =>
      refine dcongr (fun _ => rfl) (fun _ => ?_)
      refine dcongr (fun _ => rfl) (fun _ => ?_)
      exact congrArg
        (fun r => if f (decide (n % 2 = 1)) (decide (m % 2 = 1)) = true
          then r + r + 1 else r + r)
        (hg ⟨n / 2, m / 2⟩ _)
  exact rfl

private theorem bitwiseStep (f : Bool → Bool → Bool) (x y : Nat)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    Nat.bitwise f x y =
      (if f (decide (x % 2 = 1)) (decide (y % 2 = 1)) = true
       then Nat.bitwise f (x / 2) (y / 2) + Nat.bitwise f (x / 2) (y / 2) + 1
       else Nat.bitwise f (x / 2) (y / 2) + Nat.bitwise f (x / 2) (y / 2)) := by
  rw [bitwiseUnfold f x y, if_neg hx, if_neg hy]

private theorem bitwiseZeroLeft (f : Bool → Bool → Bool) (y : Nat) :
    Nat.bitwise f 0 y = if f false true = true then y else 0 := by
  rw [bitwiseUnfold, if_pos rfl]

private theorem bitwiseZeroRight (f : Bool → Bool → Bool) (x : Nat)
    (hx : x ≠ 0) :
    Nat.bitwise f x 0 = if f true false = true then x else 0 := by
  rw [bitwiseUnfold, if_neg hx, if_pos rfl]

/-- `v + v = 2 * v` at prefix level. -/
private theorem twoMul (v : Nat) : v + v = 2 * v :=
  (Nat.two_mul v).symm

/-- `2 * (v / 2) + v % 2 = v` at prefix level. -/
private theorem divAddMod (v : Nat) : 2 * (v / 2) + v % 2 = v :=
  Nat.div_add_mod v 2

theorem landRecCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) x = Bool.true →
    Nat.land x y =
      Nat.add
        (Nat.mul (Nat.succ (Nat.succ Nat.zero))
          (Nat.land (Nat.div x (Nat.succ (Nat.succ Nat.zero)))
            (Nat.div y (Nat.succ (Nat.succ Nat.zero)))))
        (Nat.mul (Nat.mod x (Nat.succ (Nat.succ Nat.zero)))
          (Nat.mod y (Nat.succ (Nat.succ Nat.zero)))) := by
  intro x y h1x
  have hx := bleOneTrue h1x
  show Nat.bitwise and x y =
    2 * Nat.bitwise and (x / 2) (y / 2) + (x % 2) * (y % 2)
  by_cases hy : y = 0
  · subst hy
    rw [bitwiseZeroRight and x hx, Nat.zero_div]
    have hres : Nat.bitwise and (x / 2) 0 = 0 := by
      by_cases hz : x / 2 = 0
      · rw [hz, bitwiseZeroLeft]
        exact rfl
      · rw [bitwiseZeroRight and _ hz]
        exact rfl
    rw [hres]
    exact rfl
  · rw [bitwiseStep and x y hx hy]
    rcases Nat.mod_two_eq_zero_or_one x with hx2 | hx2 <;>
      rcases Nat.mod_two_eq_zero_or_one y with hy2 | hy2 <;>
      rw [hx2, hy2, twoMul] <;> exact rfl

theorem landBaseCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) x = Bool.false →
    Nat.land x y = Nat.zero := by
  intro x y h1x
  have hx := bleOneFalse h1x
  subst hx
  show Nat.bitwise and 0 y = 0
  rw [bitwiseZeroLeft]
  exact rfl

theorem lorRecCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) x = Bool.true →
    Nat.lor x y =
      Nat.add
        (Nat.mul (Nat.succ (Nat.succ Nat.zero))
          (Nat.lor (Nat.div x (Nat.succ (Nat.succ Nat.zero)))
            (Nat.div y (Nat.succ (Nat.succ Nat.zero)))))
        (Nat.sub
          (Nat.add (Nat.mod x (Nat.succ (Nat.succ Nat.zero)))
            (Nat.mod y (Nat.succ (Nat.succ Nat.zero))))
          (Nat.mul (Nat.mod x (Nat.succ (Nat.succ Nat.zero)))
            (Nat.mod y (Nat.succ (Nat.succ Nat.zero))))) := by
  intro x y h1x
  have hx := bleOneTrue h1x
  show Nat.bitwise or x y =
    2 * Nat.bitwise or (x / 2) (y / 2) + (x % 2 + y % 2 - (x % 2) * (y % 2))
  by_cases hy : y = 0
  · subst hy
    rw [bitwiseZeroRight or x hx, Nat.zero_div]
    have hres : Nat.bitwise or (x / 2) 0 = x / 2 := by
      by_cases hz : x / 2 = 0
      · rw [hz, bitwiseZeroLeft]
        exact rfl
      · rw [bitwiseZeroRight or _ hz]
        exact rfl
    rw [hres]
    show x = 2 * (x / 2) + x % 2
    exact (divAddMod x).symm
  · rw [bitwiseStep or x y hx hy]
    rcases Nat.mod_two_eq_zero_or_one x with hx2 | hx2 <;>
      rcases Nat.mod_two_eq_zero_or_one y with hy2 | hy2 <;>
      rw [hx2, hy2, twoMul] <;> exact rfl

theorem lorBaseCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) x = Bool.false →
    Nat.lor x y = y := by
  intro x y h1x
  have hx := bleOneFalse h1x
  subst hx
  show Nat.bitwise or 0 y = y
  rw [bitwiseZeroLeft]
  exact rfl

theorem xorRecCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) x = Bool.true →
    Nat.xor x y =
      Nat.add
        (Nat.mul (Nat.succ (Nat.succ Nat.zero))
          (Nat.xor (Nat.div x (Nat.succ (Nat.succ Nat.zero)))
            (Nat.div y (Nat.succ (Nat.succ Nat.zero)))))
        (Nat.mod
          (Nat.add (Nat.mod x (Nat.succ (Nat.succ Nat.zero)))
            (Nat.mod y (Nat.succ (Nat.succ Nat.zero))))
          (Nat.succ (Nat.succ Nat.zero))) := by
  intro x y h1x
  have hx := bleOneTrue h1x
  show Nat.bitwise bne x y =
    2 * Nat.bitwise bne (x / 2) (y / 2) + (x % 2 + y % 2) % 2
  by_cases hy : y = 0
  · subst hy
    rw [bitwiseZeroRight bne x hx, Nat.zero_div]
    have hres : Nat.bitwise bne (x / 2) 0 = x / 2 := by
      by_cases hz : x / 2 = 0
      · rw [hz, bitwiseZeroLeft]
        exact rfl
      · rw [bitwiseZeroRight bne _ hz]
        exact rfl
    rw [hres]
    have hmm : (x % 2) % 2 = x % 2 := by
      rcases Nat.mod_two_eq_zero_or_one x with hx2 | hx2 <;> rw [hx2]
    show x = 2 * (x / 2) + (x % 2 + 0) % 2
    rw [Nat.add_zero, hmm]
    exact (divAddMod x).symm
  · rw [bitwiseStep bne x y hx hy]
    rcases Nat.mod_two_eq_zero_or_one x with hx2 | hx2 <;>
      rcases Nat.mod_two_eq_zero_or_one y with hy2 | hy2 <;>
      rw [hx2, hy2, twoMul] <;> exact rfl

theorem xorBaseCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) x = Bool.false →
    Nat.xor x y = y := by
  intro x y h1x
  have hx := bleOneFalse h1x
  subst hx
  show Nat.bitwise bne 0 y = y
  rw [bitwiseZeroLeft]
  exact rfl

end ConLeche.PinGen
