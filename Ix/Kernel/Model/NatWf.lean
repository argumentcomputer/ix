module

public import Ix.Kernel.Model.DivMod
import Ix.Kernel.PinGen.Certs
public section

/-!
# The WF-recursive `Nat` operations' literal values at `interp`
(task #161, literal tier — the divmod leg, part 2)

`Sound/NatOpsWf.lean`'s meta-level strong inductions, re-proved at the
validated-annotation currency: the `ble`-guarded value clauses of
`DivMod` drive the recursion, the guards are computed by
`natOpV_ble`, the steps by the structural operations' closed forms
(`NatSemP.lean`), and the metatheory-side bit-operation recurrences
are the pin generator's own certificate theorems (`PinGen.*Cert`) —
pure `Nat` facts, reused verbatim.

The one presentational improvement over v1: each operation's clause
dispatch is unpacked by a named lemma stated at the interpretation
valuation (`divModClauses_gcd` …), instead of a page-wide type
ascription inline in the induction.
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint natOpGuard natLitSupported)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}

/-! ## The small numerals, unfolded -/

/-- The literal `1` (definitional, packaged for rewriting). -/
theorem natLit_one (m : EnvModel V env) (ρ : Nat → V) :
    interp V ρ (natLit m φ 1)
      = SetTheory.app (interp V ρ (m.acval Ix.Kernel.natSuccName φ))
          (interp V ρ (m.acval Ix.Kernel.natZeroName φ)) := by rfl

/-- The literal `2` (definitional). -/
theorem natLit_two (m : EnvModel V env) (ρ : Nat → V) :
    interp V ρ (natLit m φ 2)
      = SetTheory.app (interp V ρ (m.acval Ix.Kernel.natSuccName φ))
          (SetTheory.app (interp V ρ (m.acval Ix.Kernel.natSuccName φ))
            (interp V ρ (m.acval Ix.Kernel.natZeroName φ))) := by rfl

/-! ## The clause dispatch, unpacked per operation

Each lemma below is `DivModClausesV`'s branch for one operation, read
at the interpretation valuation.  `divModClausesV_divmod`
(`Sound/NatOpsWf.lean`) is already valuation-generic and is reused for
`Nat.div`/`Nat.mod`. -/

section Unpack

variable (m : EnvModel V env) (ρ : Nat → V)

/-- `Nat.gcd`'s two clauses. -/
theorem divModClauses_gcd {x y : V}
    (h : DivModClausesV V (fun n => interp V ρ (m.acval n φ))
      Ix.Kernel.natGcdName x y) :
    (SetTheory.app (SetTheory.app
        (interp V ρ (m.acval Ix.Kernel.natBleName φ))
        (interp V ρ (natLit m φ 1))) x
      = interp V ρ (m.acval Ix.Kernel.boolTrueName φ) →
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natGcdName φ)) x) y
        = SetTheory.app (SetTheory.app
            (interp V ρ (m.acval Ix.Kernel.natGcdName φ))
            (SetTheory.app (SetTheory.app
              (interp V ρ (m.acval Ix.Kernel.natModName φ)) y) x)) x) ∧
    (SetTheory.app (SetTheory.app
        (interp V ρ (m.acval Ix.Kernel.natBleName φ))
        (interp V ρ (natLit m φ 1))) x
      = interp V ρ (m.acval Ix.Kernel.boolFalseName φ) →
      SetTheory.app (SetTheory.app
        (interp V ρ (m.acval Ix.Kernel.natGcdName φ)) x) y = y) := by
  rw [natLit_one]
  simpa +decide only [DivModClausesV, if_false, if_true] using h

/-- `Nat.shiftLeft`'s two clauses. -/
theorem divModClauses_shiftLeft {x y : V}
    (h : DivModClausesV V (fun n => interp V ρ (m.acval n φ))
      Ix.Kernel.natShiftLeftName x y) :
    (SetTheory.app (SetTheory.app
        (interp V ρ (m.acval Ix.Kernel.natBleName φ))
        (interp V ρ (natLit m φ 1))) y
      = interp V ρ (m.acval Ix.Kernel.boolTrueName φ) →
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natShiftLeftName φ)) x) y
        = SetTheory.app (SetTheory.app
            (interp V ρ (m.acval Ix.Kernel.natShiftLeftName φ))
            (SetTheory.app (SetTheory.app
              (interp V ρ (m.acval Ix.Kernel.natMulName φ))
              (interp V ρ (natLit m φ 2))) x))
            (SetTheory.app (SetTheory.app
              (interp V ρ (m.acval Ix.Kernel.natSubName φ)) y)
              (interp V ρ (natLit m φ 1)))) ∧
    (SetTheory.app (SetTheory.app
        (interp V ρ (m.acval Ix.Kernel.natBleName φ))
        (interp V ρ (natLit m φ 1))) y
      = interp V ρ (m.acval Ix.Kernel.boolFalseName φ) →
      SetTheory.app (SetTheory.app
        (interp V ρ (m.acval Ix.Kernel.natShiftLeftName φ)) x) y = x) := by
  rw [natLit_one, natLit_two]
  simpa +decide only [DivModClausesV, if_false, if_true] using h

/-- `Nat.shiftRight`'s two clauses. -/
theorem divModClauses_shiftRight {x y : V}
    (h : DivModClausesV V (fun n => interp V ρ (m.acval n φ))
      Ix.Kernel.natShiftRightName x y) :
    (SetTheory.app (SetTheory.app
        (interp V ρ (m.acval Ix.Kernel.natBleName φ))
        (interp V ρ (natLit m φ 1))) y
      = interp V ρ (m.acval Ix.Kernel.boolTrueName φ) →
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natShiftRightName φ)) x) y
        = SetTheory.app (SetTheory.app
            (interp V ρ (m.acval Ix.Kernel.natDivName φ))
            (SetTheory.app (SetTheory.app
              (interp V ρ (m.acval Ix.Kernel.natShiftRightName φ)) x)
              (SetTheory.app (SetTheory.app
                (interp V ρ (m.acval Ix.Kernel.natSubName φ)) y)
                (interp V ρ (natLit m φ 1)))))
            (interp V ρ (natLit m φ 2))) ∧
    (SetTheory.app (SetTheory.app
        (interp V ρ (m.acval Ix.Kernel.natBleName φ))
        (interp V ρ (natLit m φ 1))) y
      = interp V ρ (m.acval Ix.Kernel.boolFalseName φ) →
      SetTheory.app (SetTheory.app
        (interp V ρ (m.acval Ix.Kernel.natShiftRightName φ)) x) y
        = x) := by
  rw [natLit_one, natLit_two]
  simpa +decide only [DivModClausesV, if_false, if_true] using h

/-- `Nat.land`'s two clauses. -/
theorem divModClauses_land {x y : V}
    (h : DivModClausesV V (fun n => interp V ρ (m.acval n φ))
      Ix.Kernel.natLandName x y) :
    (SetTheory.app (SetTheory.app
        (interp V ρ (m.acval Ix.Kernel.natBleName φ))
        (interp V ρ (natLit m φ 1))) x
      = interp V ρ (m.acval Ix.Kernel.boolTrueName φ) →
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natLandName φ)) x) y
        = SetTheory.app (SetTheory.app
            (interp V ρ (m.acval Ix.Kernel.natAddName φ))
            (SetTheory.app (SetTheory.app
              (interp V ρ (m.acval Ix.Kernel.natMulName φ))
              (interp V ρ (natLit m φ 2)))
              (SetTheory.app (SetTheory.app
                (interp V ρ (m.acval Ix.Kernel.natLandName φ))
                (SetTheory.app (SetTheory.app
                  (interp V ρ (m.acval Ix.Kernel.natDivName φ)) x)
                  (interp V ρ (natLit m φ 2))))
                (SetTheory.app (SetTheory.app
                  (interp V ρ (m.acval Ix.Kernel.natDivName φ)) y)
                  (interp V ρ (natLit m φ 2))))))
            (SetTheory.app (SetTheory.app
              (interp V ρ (m.acval Ix.Kernel.natMulName φ))
              (SetTheory.app (SetTheory.app
                (interp V ρ (m.acval Ix.Kernel.natModName φ)) x)
                (interp V ρ (natLit m φ 2))))
              (SetTheory.app (SetTheory.app
                (interp V ρ (m.acval Ix.Kernel.natModName φ)) y)
                (interp V ρ (natLit m φ 2))))) ∧
    (SetTheory.app (SetTheory.app
        (interp V ρ (m.acval Ix.Kernel.natBleName φ))
        (interp V ρ (natLit m φ 1))) x
      = interp V ρ (m.acval Ix.Kernel.boolFalseName φ) →
      SetTheory.app (SetTheory.app
        (interp V ρ (m.acval Ix.Kernel.natLandName φ)) x) y
        = interp V ρ (m.acval Ix.Kernel.natZeroName φ)) := by
  rw [natLit_one, natLit_two]
  simpa +decide only [DivModClausesV, if_false, if_true] using h

/-- `Nat.lor`'s two clauses. -/
theorem divModClauses_lor {x y : V}
    (h : DivModClausesV V (fun n => interp V ρ (m.acval n φ))
      Ix.Kernel.natLorName x y) :
    (SetTheory.app (SetTheory.app
        (interp V ρ (m.acval Ix.Kernel.natBleName φ))
        (interp V ρ (natLit m φ 1))) x
      = interp V ρ (m.acval Ix.Kernel.boolTrueName φ) →
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natLorName φ)) x) y
        = SetTheory.app (SetTheory.app
            (interp V ρ (m.acval Ix.Kernel.natAddName φ))
            (SetTheory.app (SetTheory.app
              (interp V ρ (m.acval Ix.Kernel.natMulName φ))
              (interp V ρ (natLit m φ 2)))
              (SetTheory.app (SetTheory.app
                (interp V ρ (m.acval Ix.Kernel.natLorName φ))
                (SetTheory.app (SetTheory.app
                  (interp V ρ (m.acval Ix.Kernel.natDivName φ)) x)
                  (interp V ρ (natLit m φ 2))))
                (SetTheory.app (SetTheory.app
                  (interp V ρ (m.acval Ix.Kernel.natDivName φ)) y)
                  (interp V ρ (natLit m φ 2))))))
            (SetTheory.app (SetTheory.app
              (interp V ρ (m.acval Ix.Kernel.natSubName φ))
              (SetTheory.app (SetTheory.app
                (interp V ρ (m.acval Ix.Kernel.natAddName φ))
                (SetTheory.app (SetTheory.app
                  (interp V ρ (m.acval Ix.Kernel.natModName φ)) x)
                  (interp V ρ (natLit m φ 2))))
                (SetTheory.app (SetTheory.app
                  (interp V ρ (m.acval Ix.Kernel.natModName φ)) y)
                  (interp V ρ (natLit m φ 2)))))
              (SetTheory.app (SetTheory.app
                (interp V ρ (m.acval Ix.Kernel.natMulName φ))
                (SetTheory.app (SetTheory.app
                  (interp V ρ (m.acval Ix.Kernel.natModName φ)) x)
                  (interp V ρ (natLit m φ 2))))
                (SetTheory.app (SetTheory.app
                  (interp V ρ (m.acval Ix.Kernel.natModName φ)) y)
                  (interp V ρ (natLit m φ 2)))))) ∧
    (SetTheory.app (SetTheory.app
        (interp V ρ (m.acval Ix.Kernel.natBleName φ))
        (interp V ρ (natLit m φ 1))) x
      = interp V ρ (m.acval Ix.Kernel.boolFalseName φ) →
      SetTheory.app (SetTheory.app
        (interp V ρ (m.acval Ix.Kernel.natLorName φ)) x) y = y) := by
  rw [natLit_one, natLit_two]
  simpa +decide only [DivModClausesV, if_false, if_true] using h

/-- `Nat.xor`'s two clauses. -/
theorem divModClauses_xor {x y : V}
    (h : DivModClausesV V (fun n => interp V ρ (m.acval n φ))
      Ix.Kernel.natXorName x y) :
    (SetTheory.app (SetTheory.app
        (interp V ρ (m.acval Ix.Kernel.natBleName φ))
        (interp V ρ (natLit m φ 1))) x
      = interp V ρ (m.acval Ix.Kernel.boolTrueName φ) →
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natXorName φ)) x) y
        = SetTheory.app (SetTheory.app
            (interp V ρ (m.acval Ix.Kernel.natAddName φ))
            (SetTheory.app (SetTheory.app
              (interp V ρ (m.acval Ix.Kernel.natMulName φ))
              (interp V ρ (natLit m φ 2)))
              (SetTheory.app (SetTheory.app
                (interp V ρ (m.acval Ix.Kernel.natXorName φ))
                (SetTheory.app (SetTheory.app
                  (interp V ρ (m.acval Ix.Kernel.natDivName φ)) x)
                  (interp V ρ (natLit m φ 2))))
                (SetTheory.app (SetTheory.app
                  (interp V ρ (m.acval Ix.Kernel.natDivName φ)) y)
                  (interp V ρ (natLit m φ 2))))))
            (SetTheory.app (SetTheory.app
              (interp V ρ (m.acval Ix.Kernel.natModName φ))
              (SetTheory.app (SetTheory.app
                (interp V ρ (m.acval Ix.Kernel.natAddName φ))
                (SetTheory.app (SetTheory.app
                  (interp V ρ (m.acval Ix.Kernel.natModName φ)) x)
                  (interp V ρ (natLit m φ 2))))
                (SetTheory.app (SetTheory.app
                  (interp V ρ (m.acval Ix.Kernel.natModName φ)) y)
                  (interp V ρ (natLit m φ 2)))))
              (interp V ρ (natLit m φ 2)))) ∧
    (SetTheory.app (SetTheory.app
        (interp V ρ (m.acval Ix.Kernel.natBleName φ))
        (interp V ρ (natLit m φ 1))) x
      = interp V ρ (m.acval Ix.Kernel.boolFalseName φ) →
      SetTheory.app (SetTheory.app
        (interp V ρ (m.acval Ix.Kernel.natXorName φ)) x) y = y) := by
  rw [natLit_one, natLit_two]
  simpa +decide only [DivModClausesV, if_false, if_true] using h

end Unpack

/-! ## The per-operation strong inductions -/

variable {m : EnvModel V env}

/-- The common induction for `Nat.div` and `Nat.mod` (they share their
guards and their step argument) — `natOpV_divmod`'s mirror. -/
theorem natOpV_divmod (hops : NatOps m φ) (hnh : NatHeads m φ)
    (hval : AcvalValid m) (hdm : DivMod m φ) {c : Name}
    (hc : c = Ix.Kernel.natDivName ∨ c = Ix.Kernel.natModName)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? c = some (.defnInfo cv v hint)) (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app (interp V ρ (m.acval c φ))
          (interp V ρ (natLit m φ a)))
        (interp V ρ (natLit m φ b))
      = interp V ρ (natLit m φ
          (if c = Ix.Kernel.natDivName then a / b else a % b)) := by
  have hcmem : c ∈ Ix.Kernel.natDivModNames := by
    rcases hc with rfl | rfl <;> decide
  obtain ⟨hg, hclauses⟩ := hdm c hcmem cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := Ix.Kernel.natOpGuard_inv hg
  have hdepmem : Ix.Kernel.natSubName ∈ Ix.Kernel.natOpDeps c ∧
      Ix.Kernel.natBleName ∈ Ix.Kernel.natOpDeps c := by
    rcases hc with rfl | rfl <;> exact ⟨by decide, by decide⟩
  obtain ⟨cvsu, vsu, hsu, hfsu, -⟩ := hdeps Ix.Kernel.natSubName hdepmem.1
  obtain ⟨cvbl, vbl, hbl, hfbl, -⟩ := hdeps Ix.Kernel.natBleName hdepmem.2
  intro a b
  induction a using Nat.strongRecOn with
  | ind a ih =>
    have hamem := natLit_mem m hnh hval hs ρ a
    have hbmem := natLit_mem m hnh hval hs ρ b
    obtain ⟨hrec, hgt, hzero⟩ :=
      divModClausesV_divmod hc (hclauses ρ _ _ hamem hbmem)
    by_cases hb0 : b = 0
    · subst hb0
      -- `ble 1 0` is `false`: the second base clause fires
      have h1 : SetTheory.app (SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natBleName φ))
          (SetTheory.app (interp V ρ (m.acval Ix.Kernel.natSuccName φ))
            (interp V ρ (m.acval Ix.Kernel.natZeroName φ))))
          (interp V ρ (natLit m φ 0))
          = interp V ρ (m.acval Ix.Kernel.boolFalseName φ) := by
        have h := natOpV_ble m hops hnh hval hfbl ρ 1 0
        rw [natLit_one] at h
        rw [h, if_neg (by omega)]
      rw [hzero h1]
      rcases hc with rfl | rfl
      · rw [if_pos rfl, if_pos rfl, Nat.div_zero]
        rfl
      · rw [if_neg (by decide), if_neg (by decide), Nat.mod_zero]
    · by_cases hba : b ≤ a
      · have h1 : SetTheory.app (SetTheory.app
            (interp V ρ (m.acval Ix.Kernel.natBleName φ))
            (interp V ρ (natLit m φ b)))
            (interp V ρ (natLit m φ a))
            = interp V ρ (m.acval Ix.Kernel.boolTrueName φ) := by
          rw [natOpV_ble m hops hnh hval hfbl ρ b a, if_pos hba]
        have h2 : SetTheory.app (SetTheory.app
            (interp V ρ (m.acval Ix.Kernel.natBleName φ))
            (SetTheory.app (interp V ρ (m.acval Ix.Kernel.natSuccName φ))
              (interp V ρ (m.acval Ix.Kernel.natZeroName φ))))
            (interp V ρ (natLit m φ b))
            = interp V ρ (m.acval Ix.Kernel.boolTrueName φ) := by
          have h := natOpV_ble m hops hnh hval hfbl ρ 1 b
          rw [natLit_one] at h
          rw [h, if_pos (by omega)]
        have hsub : SetTheory.app (SetTheory.app
            (interp V ρ (m.acval Ix.Kernel.natSubName φ))
            (interp V ρ (natLit m φ a)))
            (interp V ρ (natLit m φ b))
            = interp V ρ (natLit m φ (a - b)) :=
          natOpV_sub m hops hnh hval hfsu ρ a b
        have hlt : a - b < a := Nat.sub_lt (by omega) (by omega)
        have hih := ih (a - b) hlt
        rw [hrec h1 h2, hsub, hih]
        by_cases hcd : c = Ix.Kernel.natDivName
        · subst hcd
          rw [if_pos rfl, if_pos rfl, if_pos rfl]
          have hd : a / b = (a - b) / b + 1 := by
            rw [Nat.div_eq a b, if_pos ⟨by omega, hba⟩]
          rw [hd]
          rfl
        · rw [if_neg hcd, if_neg hcd, if_neg hcd]
          have hmo : a % b = (a - b) % b := Nat.mod_eq_sub_mod hba
          rw [hmo]
      · have h1 : SetTheory.app (SetTheory.app
            (interp V ρ (m.acval Ix.Kernel.natBleName φ))
            (interp V ρ (natLit m φ b)))
            (interp V ρ (natLit m φ a))
            = interp V ρ (m.acval Ix.Kernel.boolFalseName φ) := by
          rw [natOpV_ble m hops hnh hval hfbl ρ b a, if_neg hba]
        rw [hgt h1]
        have hab : a < b := by omega
        by_cases hcd : c = Ix.Kernel.natDivName
        · subst hcd
          rw [if_pos rfl, if_pos rfl, Nat.div_eq_of_lt hab]
          rfl
        · rw [if_neg hcd, if_neg hcd, Nat.mod_eq_of_lt hab]

/-- `Nat.div` on literal values. -/
theorem natOpV_div (hops : NatOps m φ) (hnh : NatHeads m φ)
    (hval : AcvalValid m) (hdm : DivMod m φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Ix.Kernel.natDivName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natDivName φ))
          (interp V ρ (natLit m φ a)))
        (interp V ρ (natLit m φ b))
      = interp V ρ (natLit m φ (a / b)) := by
  intro a b
  have h := natOpV_divmod hops hnh hval hdm (Or.inl rfl) hf ρ a b
  rwa [if_pos rfl] at h

/-- `Nat.mod` on literal values. -/
theorem natOpV_mod (hops : NatOps m φ) (hnh : NatHeads m φ)
    (hval : AcvalValid m) (hdm : DivMod m φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Ix.Kernel.natModName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natModName φ))
          (interp V ρ (natLit m φ a)))
        (interp V ρ (natLit m φ b))
      = interp V ρ (natLit m φ (a % b)) := by
  intro a b
  have h := natOpV_divmod hops hnh hval hdm (Or.inr rfl) hf ρ a b
  rwa [if_neg (by decide)] at h

/-- `Nat.gcd` on literal values. -/
theorem natOpV_gcd (hops : NatOps m φ) (hnh : NatHeads m φ)
    (hval : AcvalValid m) (hdm : DivMod m φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Ix.Kernel.natGcdName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natGcdName φ))
          (interp V ρ (natLit m φ a)))
        (interp V ρ (natLit m φ b))
      = interp V ρ (natLit m φ (Nat.gcd a b)) := by
  obtain ⟨hg, hclauses⟩ := hdm Ix.Kernel.natGcdName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := Ix.Kernel.natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps Ix.Kernel.natBleName (by decide)
  obtain ⟨cvmo, vmo, himo, hfmo, -⟩ := hdeps Ix.Kernel.natModName (by decide)
  intro a b
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    obtain ⟨hrec, hbase⟩ := divModClauses_gcd m ρ
      (hclauses ρ _ _ (natLit_mem m hnh hval hs ρ a)
        (natLit_mem m hnh hval hs ρ b))
    by_cases ha0 : a = 0
    · subst ha0
      have h1 := natOpV_ble m hops hnh hval hfbl ρ 1 0
      rw [if_neg (by omega)] at h1
      rw [hbase h1, Nat.gcd_zero_left]
    · have h1 := natOpV_ble m hops hnh hval hfbl ρ 1 a
      rw [hrec (by rw [h1, if_pos (by omega)]),
        natOpV_mod hops hnh hval hdm hfmo ρ b a,
        ih (b % a) (Nat.mod_lt _ (by omega)) a, Nat.gcd_rec a b]

/-- `Nat.shiftLeft` on literal values. -/
theorem natOpV_shiftLeft (hops : NatOps m φ) (hnh : NatHeads m φ)
    (hval : AcvalValid m) (hdm : DivMod m φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Ix.Kernel.natShiftLeftName
      = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natShiftLeftName φ))
          (interp V ρ (natLit m φ a)))
        (interp V ρ (natLit m φ b))
      = interp V ρ (natLit m φ (Nat.shiftLeft a b)) := by
  obtain ⟨hg, hclauses⟩ :=
    hdm Ix.Kernel.natShiftLeftName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := Ix.Kernel.natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps Ix.Kernel.natBleName (by decide)
  obtain ⟨cvsu, vsu, hisu, hfsu, -⟩ := hdeps Ix.Kernel.natSubName (by decide)
  obtain ⟨cvmu, vmu, himu, hfmu, -⟩ := hdeps Ix.Kernel.natMulName (by decide)
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    obtain ⟨hrec, hbase⟩ := divModClauses_shiftLeft m ρ
      (hclauses ρ _ _ (natLit_mem m hnh hval hs ρ a)
        (natLit_mem m hnh hval hs ρ b))
    by_cases hb0 : b = 0
    · subst hb0
      have h1 := natOpV_ble m hops hnh hval hfbl ρ 1 0
      rw [if_neg (by omega)] at h1
      rw [hbase h1]
      exact rfl
    · have h1 := natOpV_ble m hops hnh hval hfbl ρ 1 b
      rw [if_pos (by omega)] at h1
      rw [hrec h1, natOpV_mul m hops hnh hval hfmu ρ 2 a,
        natOpV_sub m hops hnh hval hfsu ρ b 1,
        ih (b - 1) (by omega) (2 * a)]
      obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rfl

/-- `Nat.shiftRight` on literal values. -/
theorem natOpV_shiftRight (hops : NatOps m φ) (hnh : NatHeads m φ)
    (hval : AcvalValid m) (hdm : DivMod m φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Ix.Kernel.natShiftRightName
      = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natShiftRightName φ))
          (interp V ρ (natLit m φ a)))
        (interp V ρ (natLit m φ b))
      = interp V ρ (natLit m φ (Nat.shiftRight a b)) := by
  obtain ⟨hg, hclauses⟩ :=
    hdm Ix.Kernel.natShiftRightName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := Ix.Kernel.natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps Ix.Kernel.natBleName (by decide)
  obtain ⟨cvsu, vsu, hisu, hfsu, -⟩ := hdeps Ix.Kernel.natSubName (by decide)
  obtain ⟨cvdi, vdi, hidi, hfdi, -⟩ := hdeps Ix.Kernel.natDivName (by decide)
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    obtain ⟨hrec, hbase⟩ := divModClauses_shiftRight m ρ
      (hclauses ρ _ _ (natLit_mem m hnh hval hs ρ a)
        (natLit_mem m hnh hval hs ρ b))
    by_cases hb0 : b = 0
    · subst hb0
      have h1 := natOpV_ble m hops hnh hval hfbl ρ 1 0
      rw [if_neg (by omega)] at h1
      rw [hbase h1]
      exact rfl
    · have h1 := natOpV_ble m hops hnh hval hfbl ρ 1 b
      rw [if_pos (by omega)] at h1
      rw [hrec h1, natOpV_sub m hops hnh hval hfsu ρ b 1,
        ih (b - 1) (by omega) a,
        natOpV_div hops hnh hval hdm hfdi ρ (Nat.shiftRight a (b - 1)) 2]
      obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rfl

/-- `Nat.land` on literal values. -/
theorem natOpV_land (hops : NatOps m φ) (hnh : NatHeads m φ)
    (hval : AcvalValid m) (hdm : DivMod m φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Ix.Kernel.natLandName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natLandName φ))
          (interp V ρ (natLit m φ a)))
        (interp V ρ (natLit m φ b))
      = interp V ρ (natLit m φ (Nat.land a b)) := by
  obtain ⟨hg, hclauses⟩ :=
    hdm Ix.Kernel.natLandName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := Ix.Kernel.natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps Ix.Kernel.natBleName (by decide)
  obtain ⟨cvad, vad, hiad, hfad, -⟩ := hdeps Ix.Kernel.natAddName (by decide)
  obtain ⟨cvmu, vmu, himu, hfmu, -⟩ := hdeps Ix.Kernel.natMulName (by decide)
  obtain ⟨cvdi, vdi, hidi, hfdi, -⟩ := hdeps Ix.Kernel.natDivName (by decide)
  obtain ⟨cvmo, vmo, himo, hfmo, -⟩ := hdeps Ix.Kernel.natModName (by decide)
  intro a b
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    obtain ⟨hrec, hbase⟩ := divModClauses_land m ρ
      (hclauses ρ _ _ (natLit_mem m hnh hval hs ρ a)
        (natLit_mem m hnh hval hs ρ b))
    by_cases ha0 : a = 0
    · subst ha0
      have h1 := natOpV_ble m hops hnh hval hfbl ρ 1 0
      rw [if_neg (by omega)] at h1
      rw [hbase h1, show Nat.land 0 b = 0 from PinGen.landBaseCert 0 b rfl]
      exact rfl
    · have h1 := natOpV_ble m hops hnh hval hfbl ρ 1 a
      rw [if_pos (by omega)] at h1
      rw [hrec h1, natOpV_div hops hnh hval hdm hfdi ρ a 2,
        natOpV_div hops hnh hval hdm hfdi ρ b 2,
        ih (a / 2) (Nat.div_lt_self (by omega) (by omega)) (b / 2),
        natOpV_mul m hops hnh hval hfmu ρ 2 (Nat.land (a / 2) (b / 2)),
        natOpV_mod hops hnh hval hdm hfmo ρ a 2,
        natOpV_mod hops hnh hval hdm hfmo ρ b 2,
        natOpV_mul m hops hnh hval hfmu ρ (a % 2) (b % 2),
        natOpV_add m hops hnh hval hfad ρ
          (2 * Nat.land (a / 2) (b / 2)) _,
        show Nat.land a b = 2 * Nat.land (a / 2) (b / 2) + _ from
          PinGen.landRecCert a b
            (Nat.ble_eq_true_of_le (by omega : 1 ≤ a))]
      exact rfl

/-- `Nat.lor` on literal values. -/
theorem natOpV_lor (hops : NatOps m φ) (hnh : NatHeads m φ)
    (hval : AcvalValid m) (hdm : DivMod m φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Ix.Kernel.natLorName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natLorName φ))
          (interp V ρ (natLit m φ a)))
        (interp V ρ (natLit m φ b))
      = interp V ρ (natLit m φ (Nat.lor a b)) := by
  obtain ⟨hg, hclauses⟩ :=
    hdm Ix.Kernel.natLorName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := Ix.Kernel.natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps Ix.Kernel.natBleName (by decide)
  obtain ⟨cvad, vad, hiad, hfad, -⟩ := hdeps Ix.Kernel.natAddName (by decide)
  obtain ⟨cvmu, vmu, himu, hfmu, -⟩ := hdeps Ix.Kernel.natMulName (by decide)
  obtain ⟨cvdi, vdi, hidi, hfdi, -⟩ := hdeps Ix.Kernel.natDivName (by decide)
  obtain ⟨cvmo, vmo, himo, hfmo, -⟩ := hdeps Ix.Kernel.natModName (by decide)
  obtain ⟨cvsu, vsu, hisu, hfsu, -⟩ := hdeps Ix.Kernel.natSubName (by decide)
  intro a b
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    obtain ⟨hrec, hbase⟩ := divModClauses_lor m ρ
      (hclauses ρ _ _ (natLit_mem m hnh hval hs ρ a)
        (natLit_mem m hnh hval hs ρ b))
    by_cases ha0 : a = 0
    · subst ha0
      have h1 := natOpV_ble m hops hnh hval hfbl ρ 1 0
      rw [if_neg (by omega)] at h1
      rw [hbase h1, show Nat.lor 0 b = b from PinGen.lorBaseCert 0 b rfl]
    · have h1 := natOpV_ble m hops hnh hval hfbl ρ 1 a
      rw [if_pos (by omega)] at h1
      rw [hrec h1, natOpV_div hops hnh hval hdm hfdi ρ a 2,
        natOpV_div hops hnh hval hdm hfdi ρ b 2,
        ih (a / 2) (Nat.div_lt_self (by omega) (by omega)) (b / 2),
        natOpV_mul m hops hnh hval hfmu ρ 2 (Nat.lor (a / 2) (b / 2)),
        natOpV_mod hops hnh hval hdm hfmo ρ a 2,
        natOpV_mod hops hnh hval hdm hfmo ρ b 2,
        natOpV_add m hops hnh hval hfad ρ (a % 2) (b % 2),
        natOpV_mul m hops hnh hval hfmu ρ (a % 2) (b % 2),
        natOpV_sub m hops hnh hval hfsu ρ (a % 2 + b % 2)
          (a % 2 * (b % 2)),
        natOpV_add m hops hnh hval hfad ρ
          (2 * Nat.lor (a / 2) (b / 2)) _,
        show Nat.lor a b = 2 * Nat.lor (a / 2) (b / 2) + _ from
          PinGen.lorRecCert a b
            (Nat.ble_eq_true_of_le (by omega : 1 ≤ a))]
      exact rfl

/-- `Nat.xor` on literal values. -/
theorem natOpV_xor (hops : NatOps m φ) (hnh : NatHeads m φ)
    (hval : AcvalValid m) (hdm : DivMod m φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Ix.Kernel.natXorName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natXorName φ))
          (interp V ρ (natLit m φ a)))
        (interp V ρ (natLit m φ b))
      = interp V ρ (natLit m φ (Nat.xor a b)) := by
  obtain ⟨hg, hclauses⟩ :=
    hdm Ix.Kernel.natXorName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := Ix.Kernel.natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps Ix.Kernel.natBleName (by decide)
  obtain ⟨cvad, vad, hiad, hfad, -⟩ := hdeps Ix.Kernel.natAddName (by decide)
  obtain ⟨cvmu, vmu, himu, hfmu, -⟩ := hdeps Ix.Kernel.natMulName (by decide)
  obtain ⟨cvdi, vdi, hidi, hfdi, -⟩ := hdeps Ix.Kernel.natDivName (by decide)
  obtain ⟨cvmo, vmo, himo, hfmo, -⟩ := hdeps Ix.Kernel.natModName (by decide)
  intro a b
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    obtain ⟨hrec, hbase⟩ := divModClauses_xor m ρ
      (hclauses ρ _ _ (natLit_mem m hnh hval hs ρ a)
        (natLit_mem m hnh hval hs ρ b))
    by_cases ha0 : a = 0
    · subst ha0
      have h1 := natOpV_ble m hops hnh hval hfbl ρ 1 0
      rw [if_neg (by omega)] at h1
      rw [hbase h1, show Nat.xor 0 b = b from PinGen.xorBaseCert 0 b rfl]
    · have h1 := natOpV_ble m hops hnh hval hfbl ρ 1 a
      rw [if_pos (by omega)] at h1
      rw [hrec h1, natOpV_div hops hnh hval hdm hfdi ρ a 2,
        natOpV_div hops hnh hval hdm hfdi ρ b 2,
        ih (a / 2) (Nat.div_lt_self (by omega) (by omega)) (b / 2),
        natOpV_mul m hops hnh hval hfmu ρ 2 (Nat.xor (a / 2) (b / 2)),
        natOpV_mod hops hnh hval hdm hfmo ρ a 2,
        natOpV_mod hops hnh hval hdm hfmo ρ b 2,
        natOpV_add m hops hnh hval hfad ρ (a % 2) (b % 2),
        natOpV_mod hops hnh hval hdm hfmo ρ (a % 2 + b % 2) 2,
        natOpV_add m hops hnh hval hfad ρ
          (2 * Nat.xor (a / 2) (b / 2)) _,
        show Nat.xor a b = 2 * Nat.xor (a / 2) (b / 2) + _ from
          PinGen.xorRecCert a b
            (Nat.ble_eq_true_of_le (by omega : 1 ≤ a))]
      exact rfl

end Ix.Kernel.Model
