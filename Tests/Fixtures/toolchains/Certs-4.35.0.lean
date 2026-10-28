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

**The proofs are written for the size of their closed form.** The
generator (`Ix.RoleEvidence.closeProof`) inlines every constant outside
the operation's dependency closure, with beta reduction, so a lemma
outside the closure costs its whole proof once per instantiation, and
every checker of the default table (IxC, IxVM in-circuit) checks the
result. So the proofs here:

- unfold the operations definitionally (`with_unfolding_all`), never
  through the auto-generated `eq_def` lemmas, whose proofs are large;
- decide `dite`/`ite` by case analysis on the `Decidable` instance
  (`dpos`, `dneg`, `dcongr`), never through `dif_pos`, `if_pos` or `rw`;
- discharge the cases where the measure is a numeral (`x = 0`, and `y = 0`
  in the bit operations) by evaluation;
- use only lemmas in the operations' dependency closures, and small local
  facts (`modTwoCases`, `modAddDivTwo`, `twoMul`) in place of the general
  library lemmas (`Nat.mod_two_eq_zero_or_one`, `Nat.div_add_mod`,
  `Nat.two_mul`).

There is no `simp` and no `decide`. The proofs reach no axiom outside the
operations' dependency closures: the bit operations' proofs reach `propext`,
which their definitions already use.

This module is part of the elab-time pin generator; nothing in it is used
by the checker at runtime. The proofs unfold core definition bodies that
the module system hides, hence `import all`. It is its own Lake target;
the role-table generator (`kernel-pin-gen`) loads it by name into its
full-view environment and egresses its theorems as the default table's
evidence records, the compiler's role binding
(`Ix.RoleBinding.Compile.finalize`) compiles and closes them the same way,
and Source mode reads them from the checked environment
(`Ix.LeanIngress.sourceEvidence`). The model reuses the bit operations'
statements (`IxC/Kernel/Model/NatWf.lean`), so the theorems' names and
statements are fixed.
-/

namespace Ix.Kernel.PinGen

/-! ## `Decidable` case analysis -/

/-- Case analysis on a `Decidable` instance, false case first: the argument
order of `Decidable.casesOn` when `Decidable` was an inductive with the two
constructors `isFalse` and `isTrue`. It cases on the instance's fields, as
`dite` does, so that a closed proof reaches `Decidable` only through its
projections and constructor (structure eta), never through its recursor, which
is outside the operations' dependency closures. -/
private abbrev decCases {c : Prop} {motive : Decidable c → Sort u} (d : Decidable c)
    (isFalse : ∀ h, motive (Decidable.isFalse h)) (isTrue : ∀ h, motive (Decidable.isTrue h)) :
    motive d :=
  Bool.casesOn (motive := fun b => ∀ r : b.Reflects c, motive ⟨b, r⟩) d.decide isFalse isTrue
    d.reflects_decide

/-- `dite` at a true condition. -/
private theorem dpos {c : Prop} {d : Decidable c} {α : Sort u} {t : c → α} {e : ¬c → α}
    (hc : c) : @dite α c d t e = t hc :=
  decCases (motive := fun d => @dite α c d t e = t hc) d
    (fun hn => absurd hc hn) (fun _ => rfl)

/-- `dite` at a false condition. -/
private theorem dneg {c : Prop} {d : Decidable c} {α : Sort u} {t : c → α} {e : ¬c → α}
    (hn : ¬c) : @dite α c d t e = e hn :=
  decCases (motive := fun d => @dite α c d t e = e hn) d
    (fun _ => rfl) (fun hc => absurd hc hn)

/-- `dite` is a congruence in its branches. -/
private theorem dcongr {c : Prop} {d : Decidable c} {α : Sort u} {t1 t2 : c → α}
    {e1 e2 : ¬c → α} (ht : ∀ h, t1 h = t2 h) (he : ∀ h, e1 h = e2 h) :
    @dite α c d t1 e1 = @dite α c d t2 e2 :=
  decCases (motive := fun d => @dite α c d t1 e1 = @dite α c d t2 e2) d he ht

/-! ## The `Nat.div`/`Nat.mod` certificate theorems

`Nat.div x y` and `Nat.modCore x y` are a `dite` on `0 < y` around a
fuel-recursive worker (`go`, fuel `x + 1`). One step of the worker is its
definition at a `succ` fuel; the recurrence then needs the worker's
independence of the fuel (`divGoCongr`, `modGoCongr`), since `x / y` and
`(x - y) / y` start from different fuels. -/

private theorem divGoCongr (y : Nat) (hy : 0 < y) :
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
      with_unfolding_all exact dcongr (fun h => congrArg Nat.succ (ih _ _ f2 _)) (fun _ => rfl)

private theorem modGoCongr (y : Nat) (hy : 0 < y) :
    ∀ (f1 x : Nat) (h1 : x < f1) (f2 : Nat) (h2 : x < f2),
      Nat.modCore.go y hy f1 x h1 = Nat.modCore.go y hy f2 x h2 := by
  intro f1
  induction f1 with
  | zero => intro x h1 f2 h2; exact absurd h1 (Nat.not_succ_le_zero x)
  | succ f1 ih =>
    intro x h1 f2 h2
    cases f2 with
    | zero => exact absurd h2 (Nat.not_succ_le_zero x)
    | succ f2 => with_unfolding_all exact dcongr (fun h => ih _ _ f2 _) (fun _ => rfl)

/-- `Nat.mod` agrees with `Nat.modCore` for `0 < y` (the dispatcher's
`x`-match and `≤`-test collapse against `modCore`'s own). -/
private theorem modEqModCore (x y : Nat) (hy : 0 < y) : Nat.mod x y = Nat.modCore x y := by
  cases x with
  | zero =>
    have hn : ¬ (y ≤ 0) := fun hle =>
      absurd (Nat.lt_of_lt_of_le hy hle) (Nat.lt_irrefl 0)
    have e : Nat.modCore 0 y = 0 := by with_unfolding_all exact (dpos hy).trans (dneg hn)
    exact e.symm
  | succ n =>
    show @ite Nat (y ≤ n + 1) (Nat.decLe y (n + 1)) (Nat.modCore (n + 1) y) (n + 1) = _
    exact decCases (motive := fun d =>
        @ite Nat (y ≤ n + 1) d (Nat.modCore (n + 1) y) (n + 1) = Nat.modCore (n + 1) y)
      (Nat.decLe y (n + 1))
      (fun hnle => by with_unfolding_all exact ((dpos hy).trans (dneg hnle)).symm)
      (fun _ => rfl)

theorem modRecCert : ∀ (x y : Nat), Nat.ble y x = Bool.true →
    Nat.ble (Nat.succ Nat.zero) y = Bool.true →
    Nat.mod x y = Nat.mod (Nat.sub x y) y := by
  intro x y hyx h1y
  have hy : 0 < y := Nat.le_of_ble_eq_true h1y
  have hxy : y ≤ x := Nat.le_of_ble_eq_true hyx
  have e1 : Nat.modCore x y = Nat.modCore.go y hy (Nat.succ x) x (Nat.lt_succ_self x) := by
    with_unfolding_all exact dpos hy
  have e2 : Nat.modCore.go y hy (Nat.succ x) x (Nat.lt_succ_self x) =
      Nat.modCore.go y hy x (x - y) (Nat.div_rec_fuel_lemma hy hxy (Nat.lt_succ_self x)) := by
    with_unfolding_all exact dpos hxy
  have e3 : Nat.modCore (Nat.sub x y) y =
      Nat.modCore.go y hy (Nat.succ (x - y)) (x - y) (Nat.lt_succ_self _) := by
    with_unfolding_all exact dpos hy
  exact (modEqModCore x y hy).trans (e1.trans (e2.trans ((modGoCongr y hy _ _ _ _ _).trans
    (e3.symm.trans (modEqModCore (Nat.sub x y) y hy).symm))))

theorem modBaseGtCert : ∀ (x y : Nat), Nat.ble y x = Bool.false →
    Nat.mod x y = x := by
  intro x y hf
  have hnle : ¬ (y ≤ x) := fun h =>
    Bool.noConfusion ((Nat.ble_eq_true_of_le h).symm.trans hf)
  cases x with
  | zero => rfl
  | succ n =>
    show @ite Nat (y ≤ n + 1) (Nat.decLe y (n + 1)) (Nat.modCore (n + 1) y) (n + 1) = _
    exact decCases (motive := fun d =>
        @ite Nat (y ≤ n + 1) d (Nat.modCore (n + 1) y) (n + 1) = n + 1)
      (Nat.decLe y (n + 1)) (fun _ => rfl) (fun h => absurd h hnle)

theorem modBaseZeroCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) y = Bool.false →
    Nat.mod x y = x := by
  intro x y hf
  have hny : ¬ (0 < y) := fun h =>
    Bool.noConfusion ((Nat.ble_eq_true_of_le h).symm.trans hf)
  cases x with
  | zero => rfl
  | succ n =>
    show @ite Nat (y ≤ n + 1) (Nat.decLe y (n + 1)) (Nat.modCore (n + 1) y) (n + 1) = _
    exact decCases (motive := fun d =>
        @ite Nat (y ≤ n + 1) d (Nat.modCore (n + 1) y) (n + 1) = n + 1)
      (Nat.decLe y (n + 1)) (fun _ => rfl)
      (fun _ => by with_unfolding_all exact dneg hny)

theorem divRecCert : ∀ (x y : Nat), Nat.ble y x = Bool.true →
    Nat.ble (Nat.succ Nat.zero) y = Bool.true →
    Nat.div x y = Nat.succ (Nat.div (Nat.sub x y) y) := by
  intro x y hyx h1y
  have hy : 0 < y := Nat.le_of_ble_eq_true h1y
  have hxy : y ≤ x := Nat.le_of_ble_eq_true hyx
  have e1 : Nat.div x y = Nat.div.go y hy (Nat.succ x) x (Nat.lt_succ_self x) := by
    with_unfolding_all exact dpos hy
  have e2 : Nat.div.go y hy (Nat.succ x) x (Nat.lt_succ_self x) =
      Nat.succ (Nat.div.go y hy x (x - y)
        (Nat.div_rec_fuel_lemma hy hxy (Nat.lt_succ_self x))) := by
    with_unfolding_all exact dpos hxy
  have e3 : Nat.div (Nat.sub x y) y =
      Nat.div.go y hy (Nat.succ (x - y)) (x - y) (Nat.lt_succ_self _) := by
    with_unfolding_all exact dpos hy
  exact e1.trans (e2.trans (congrArg Nat.succ ((divGoCongr y hy _ _ _ _ _).trans e3.symm)))

theorem divBaseGtCert : ∀ (x y : Nat), Nat.ble y x = Bool.false →
    Nat.div x y = Nat.zero := by
  intro x y hf
  have hnle : ¬ (y ≤ x) := fun h =>
    Bool.noConfusion ((Nat.ble_eq_true_of_le h).symm.trans hf)
  with_unfolding_all
    exact decCases (motive := fun d => @dite Nat (0 < y) d
        (fun hy => Nat.div.go y hy (Nat.succ x) x (Nat.lt_succ_self x)) (fun _ => 0) = 0)
      (Nat.decLt 0 y) (fun _ => rfl) (fun _ => dneg hnle)

theorem divBaseZeroCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) y = Bool.false →
    Nat.div x y = Nat.zero := by
  intro x y hf
  have hny : ¬ (0 < y) := fun h =>
    Bool.noConfusion ((Nat.ble_eq_true_of_le h).symm.trans hf)
  with_unfolding_all exact dneg hny

/-! ## `WellFounded.Nat.fix`, one step at a time

`Nat.gcd` and the bit operations compile to `WellFounded.Nat.fix`, a
fuel-structural recursor: `fix h F x` is `fix.go h F (eager (h x + 1)) x _`,
and `fix.go` at a `succ` fuel is `F x (fun y _ => fix.go …)`. Both measures
(`gcd`'s and `bitwise`'s first argument) make the fuel a numeral when that
argument is `0`, so those cases evaluate. Otherwise `natFixEager` rewrites
the fuel `eager (h x + 1)` to `h x + 1` (`WellFounded.Nat.eager_eq`, in the
closure), and the one recursive call then meets the call's own `fix` through
the worker's independence of the fuel (`natFixGoCongr`). Its pointwise
congruence hypothesis `hF` replaces `funext` (`WellFounded.Nat.fix_eq`'s
route), which the operations' closures do not contain: each operation proves
it through the `Decidable` case split of its body (`dcongr`). -/

private theorem natFixEager {α : Sort u} {motive : α → Sort v} (h : α → Nat)
    (F : (x : α) → ((y : α) → InvImage Nat.lt h y x → motive y) → motive x) (x : α) :
    WellFounded.Nat.fix h F x = F x (fun y hy => WellFounded.Nat.fix.go h F (h x) y hy) := by
  have e : ∀ (n : Nat) (p : h x < n), n = h x + 1 →
      WellFounded.Nat.fix.go h F n x p =
        F x (fun y hy => WellFounded.Nat.fix.go h F (h x) y hy) := by
    intro n p hn
    subst hn
    rfl
  exact e _ _ (WellFounded.Nat.eager_eq _)

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

/-- One step of `WellFounded.Nat.fix`, the recursive calls met with `fix`
itself. -/
private theorem natFixUnfold {α : Sort u} {motive : α → Sort v}
    (h : α → Nat)
    (F : (x : α) → ((y : α) → InvImage Nat.lt h y x → motive y) → motive x)
    (hF : ∀ (x : α) (g1 g2 : (y : α) → InvImage Nat.lt h y x → motive y),
      (∀ y p, g1 y p = g2 y p) → F x g1 = F x g2) (x : α) :
    WellFounded.Nat.fix h F x = F x (fun y _ => WellFounded.Nat.fix h F y) :=
  (natFixEager h F x).trans (hF x _ _ (fun y p => natFixGoCongr h F hF (h x) y p _ _))

/-! ## The `Nat.gcd` certificate theorems -/

theorem gcdRecCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) x = Bool.true →
    Nat.gcd x y = Nat.gcd (Nat.mod y x) x := by
  intro x y h1x
  cases x with
  | zero => exact Bool.noConfusion h1x
  | succ n =>
    delta Nat.gcd Nat.gcd._unary
    refine (natFixUnfold _ _ ?_ (PSigma.mk (β := fun _ : Nat => Nat) (n + 1) y)).trans ?_
    · intro z g1 g2 hg
      cases z
      exact dcongr (fun _ => rfl) (fun _ => hg _ _)
    · with_unfolding_all rfl

theorem gcdBaseCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) x = Bool.false →
    Nat.gcd x y = y := by
  intro x y h1x
  cases x with
  | zero => with_unfolding_all rfl
  | succ n => exact Bool.noConfusion h1x

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

The bit operations' closures hold `Nat.succ_add`, `Nat.sub_add_cancel` and
`WellFounded.Nat.eager_eq`, and nothing about parity, so the parity facts
are proved here from `Nat.modCore.go` and `Nat.div.go` at `2`. -/

/-- `2 * r = r + r`. -/
private theorem twoMul (r : Nat) : 2 * r = r + r :=
  Nat.rec (motive := fun r => 2 * r = r + r) rfl
    (fun r ih => (congrArg (fun t => t + 2) ih).trans
      (congrArg Nat.succ (Nat.succ_add r r).symm)) r

/-- Below `2`, a number is `0` or `1`. -/
private theorem belowTwo (v : Nat) (hn : ¬ (2 ≤ v)) : v = 0 ∨ v = 1 := by
  cases v with
  | zero => exact Or.inl rfl
  | succ v =>
    cases v with
    | zero => exact Or.inr rfl
    | succ k => exact absurd (Nat.le_of_ble_eq_true rfl) hn

/-- The remainder worker at `2` returns `0` or `1`, and with the quotient
worker it rebuilds its argument. -/
private theorem goTwo (hy : 0 < 2) : ∀ (f v : Nat) (h : v < f),
    (Nat.modCore.go 2 hy f v h = 0 ∨ Nat.modCore.go 2 hy f v h = 1) ∧
      Nat.modCore.go 2 hy f v h + 2 * Nat.div.go 2 hy f v h = v := by
  intro f
  induction f with
  | zero => intro v h; exact absurd h (Nat.not_succ_le_zero v)
  | succ f ih =>
    intro v h
    with_unfolding_all
      exact decCases (motive := fun d =>
          (@dite Nat (2 ≤ v) d (fun hle => Nat.modCore.go 2 hy f (v - 2)
              (Nat.div_rec_fuel_lemma hy hle h)) (fun _ => v) = 0 ∨
            @dite Nat (2 ≤ v) d (fun hle => Nat.modCore.go 2 hy f (v - 2)
              (Nat.div_rec_fuel_lemma hy hle h)) (fun _ => v) = 1) ∧
          @dite Nat (2 ≤ v) d (fun hle => Nat.modCore.go 2 hy f (v - 2)
              (Nat.div_rec_fuel_lemma hy hle h)) (fun _ => v) +
            2 * @dite Nat (2 ≤ v) d (fun hle => Nat.div.go 2 hy f (v - 2)
              (Nat.div_rec_fuel_lemma hy hle h) + 1) (fun _ => 0) = v)
        (Nat.decLe 2 v)
        (fun hn => And.intro (belowTwo v hn) rfl)
        (fun hle => And.intro (ih _ _).1
          ((congrArg (fun t => t + 2) (ih _ _).2).trans (Nat.sub_add_cancel hle)))

/-- `v % 2` through the remainder worker at fuel `v + 1`. -/
private theorem modTwoGo (v : Nat) :
    v % 2 = Nat.modCore.go 2 (Nat.le_of_ble_eq_true rfl) (v + 1) v (Nat.lt_succ_self v) := by
  cases v with
  | zero => rfl
  | succ n =>
    show @ite Nat (2 ≤ n + 1) (Nat.decLe 2 (n + 1)) (Nat.modCore (n + 1) 2) (n + 1) = _
    with_unfolding_all
      exact decCases (motive := fun d =>
          @ite Nat (2 ≤ n + 1) d (Nat.modCore (n + 1) 2) (n + 1) =
            Nat.modCore.go 2 (Nat.le_of_ble_eq_true rfl) (n + 1 + 1) (n + 1)
              (Nat.lt_succ_self _))
        (Nat.decLe 2 (n + 1)) (fun hn => (dneg (e := fun _ => n + 1) hn).symm) (fun _ => rfl)

/-- `v % 2` is `0` or `1`. -/
private theorem modTwoCases (v : Nat) : v % 2 = 0 ∨ v % 2 = 1 :=
  (modTwoGo v).symm ▸ (goTwo _ (v + 1) v (Nat.lt_succ_self v)).1

/-- `v % 2 + 2 * (v / 2) = v`. -/
private theorem modAddDivTwo (v : Nat) : v % 2 + 2 * (v / 2) = v := by
  have e := (goTwo (Nat.le_of_ble_eq_true rfl) (v + 1) v (Nat.lt_succ_self v)).2
  with_unfolding_all exact (congrArg (fun t => t + 2 * (v / 2)) (modTwoGo v)).trans e

/-- One step of `Nat.bitwise f` at a positive first argument, the
recursive call met with `Nat.bitwise f` itself. -/
private theorem bitwiseSucc (f : Bool → Bool → Bool) (n y : Nat) :
    Nat.bitwise f (n + 1) y =
      if y = 0 then (if f true false = true then n + 1 else 0)
      else if f (decide ((n + 1) % 2 = 1)) (decide (y % 2 = 1)) = true
        then Nat.bitwise f ((n + 1) / 2) (y / 2) + Nat.bitwise f ((n + 1) / 2) (y / 2) + 1
        else Nat.bitwise f ((n + 1) / 2) (y / 2) + Nat.bitwise f ((n + 1) / 2) (y / 2) := by
  delta Nat.bitwise Nat.bitwise._unary
  refine (natFixUnfold _ _ ?_ (PSigma.mk (β := fun _ : Nat => Nat) (n + 1) y)).trans ?_
  · intro z g1 g2 hg
    cases z with
    | mk a b =>
      exact dcongr (fun _ => rfl) (fun _ => dcongr (fun _ => rfl) (fun _ =>
        congrArg (fun r => if f (decide (a % 2 = 1)) (decide (b % 2 = 1)) = true
            then r + r + 1 else r + r) (hg _ _)))
  · with_unfolding_all rfl

/-- `Nat.bitwise f z 0`, by the case split of its first test. -/
private theorem bitwiseZeroRight (f : Bool → Bool → Bool) (z : Nat) :
    Nat.bitwise f z 0 =
      if z = 0 then (if f false true = true then 0 else 0)
      else (if f true false = true then z else 0) := by
  delta Nat.bitwise Nat.bitwise._unary
  refine (natFixEager _ _ (PSigma.mk (β := fun _ : Nat => Nat) z 0)).trans ?_
  with_unfolding_all exact dcongr (fun _ => rfl) (fun _ => rfl)

/-- `Nat.bitwise f z 0 = z` when `f false true` and `f true false` are `true`
(`or`, `bne`): both branches of the first test give `z`. -/
private theorem bitwiseZeroRightId (f : Bool → Bool → Bool) (z : Nat)
    (h1 : f false true = true) (h2 : f true false = true) : Nat.bitwise f z 0 = z := by
  refine (bitwiseZeroRight f z).trans ?_
  rw [h1, h2]
  exact decCases (motive := fun d =>
      @ite Nat (z = 0) d (if true = true then 0 else 0) (if true = true then z else 0) = z)
    (instDecidableEqNat z 0) (fun _ => rfl) (fun h => h.symm)

/-- The `and` step: the combined bit is `a * b`. -/
private theorem landBit (R a b : Nat) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    (if (decide (a = 1) && decide (b = 1)) = true then R + R + 1 else R + R) =
      2 * R + a * b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (twoMul R).symm
  · exact (twoMul R).symm
  · exact (twoMul R).symm
  · exact congrArg Nat.succ (twoMul R).symm

/-- The `or` step: the combined bit is `a + b - a * b`. -/
private theorem lorBit (R a b : Nat) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    (if (decide (a = 1) || decide (b = 1)) = true then R + R + 1 else R + R) =
      2 * R + (a + b - a * b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (twoMul R).symm
  · exact congrArg Nat.succ (twoMul R).symm
  · exact congrArg Nat.succ (twoMul R).symm
  · exact congrArg Nat.succ (twoMul R).symm

/-- The `bne` step: the combined bit is `(a + b) % 2`. -/
private theorem xorBit (R a b : Nat) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    (if (decide (a = 1) != decide (b = 1)) = true then R + R + 1 else R + R) =
      2 * R + (a + b) % 2 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (twoMul R).symm
  · exact congrArg Nat.succ (twoMul R).symm
  · exact congrArg Nat.succ (twoMul R).symm
  · exact (twoMul R).symm

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
  cases x with
  | zero => exact Bool.noConfusion h1x
  | succ n =>
    refine (bitwiseSucc and n y).trans ?_
    cases y with
    | zero =>
      have h0 : Nat.bitwise and ((n + 1) / 2) 0 = 0 := by
        refine (bitwiseZeroRight and ((n + 1) / 2)).trans ?_
        with_unfolding_all
          exact decCases (motive := fun d =>
              @dite Nat ((n + 1) / 2 = 0) d (fun _ => 0) (fun _ => 0) = 0)
            (instDecidableEqNat ((n + 1) / 2) 0) (fun _ => rfl) (fun _ => rfl)
      with_unfolding_all exact (congrArg (fun t => 2 * t) h0).symm
    | succ m =>
      with_unfolding_all
        exact landBit _ _ _ (modTwoCases (n + 1)) (modTwoCases (m + 1))

theorem landBaseCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) x = Bool.false →
    Nat.land x y = Nat.zero := by
  intro x y h1x
  cases x with
  | zero => with_unfolding_all rfl
  | succ n => exact Bool.noConfusion h1x

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
  cases x with
  | zero => exact Bool.noConfusion h1x
  | succ n =>
    refine (bitwiseSucc or n y).trans ?_
    cases y with
    | zero =>
      have hz := bitwiseZeroRightId or ((n + 1) / 2) rfl rfl
      with_unfolding_all
        exact ((congrArg (fun t => 2 * t + (n + 1) % 2) hz).trans
          ((Nat.add_comm _ _).trans (modAddDivTwo (n + 1)))).symm
    | succ m =>
      with_unfolding_all
        exact lorBit _ _ _ (modTwoCases (n + 1)) (modTwoCases (m + 1))

theorem lorBaseCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) x = Bool.false →
    Nat.lor x y = y := by
  intro x y h1x
  cases x with
  | zero => with_unfolding_all rfl
  | succ n => exact Bool.noConfusion h1x

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
  cases x with
  | zero => exact Bool.noConfusion h1x
  | succ n =>
    refine (bitwiseSucc bne n y).trans ?_
    cases y with
    | zero =>
      have hz := bitwiseZeroRightId bne ((n + 1) / 2) rfl rfl
      have ha : (n + 1) % 2 % 2 = (n + 1) % 2 := by
        rcases modTwoCases (n + 1) with h | h <;> rw [h]
      with_unfolding_all
        exact ((congrArg (fun t => 2 * t + (n + 1) % 2 % 2) hz).trans
          ((congrArg (fun t => 2 * ((n + 1) / 2) + t) ha).trans
            ((Nat.add_comm _ _).trans (modAddDivTwo (n + 1))))).symm
    | succ m =>
      with_unfolding_all
        exact xorBit _ _ _ (modTwoCases (n + 1)) (modTwoCases (m + 1))

theorem xorBaseCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) x = Bool.false →
    Nat.xor x y = y := by
  intro x y h1x
  cases x with
  | zero => with_unfolding_all rfl
  | succ n => exact Bool.noConfusion h1x

end Ix.Kernel.PinGen
