module

public import IxC.Kernel.Model.Annot.Laws
public import IxC.Kernel.Model.Annot.BitLemmas
import IxC.Kernel.Semantics.Kit

public section

/-!
# `Nat.add`'s recurrences at values

The stored structural operations' defining equations (`NatOps`, established at
each operation's install) read at value slots (`natEq_value`), and for `Nat.add`
the two clauses `add x 0 = x` and `add x (succ y) = succ (add x y)` for `x`, `y` in
the stored `Nat` (`natAdd_clauses`). In a module of their own, below the rules
tier's soundness, so that both the literal transports (`Model/NatSem.lean`) and
the `Nat` offset rules (`Model/Rules/NatOffsetSound.lean`) read them.
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (Env Expr Key ConstantInfo ConstantVal ReducibilityHint)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env md} {φ : LevelParam → Nat}

/-- A leaf's interpretation does not read the valuation. -/
theorem leaf_interp_closed (m : EnvModel V env) (n : Key md) (ψ : LevelParam → Nat)
    (ρ ρ' : Nat → V) : interp V ρ (m.acval n ψ) = interp V ρ' (m.acval n ψ) :=
  interp_closed V (by rw [m.acval_erase]; exact m.cval_closed n ψ) ρ ρ'

/-- A stored constant without level parameters reads to its leaf at the plain
assignment. -/
theorem denoteMeta_leaf {acval : Key md → (LevelParam → Nat) → AnnotTerm} {d : Nat}
    {n : Key md} {ci : ConstantInfo md} (hf : env.find? n = some ci)
    (hlp : ci.toConstantVal.levelParams = []) :
    denoteMeta acval env φ d (.const n []) = some (acval n φ) := by
  rw [denoteMeta_const hf (by simp [hlp]), hlp,
    show Level.substFn φ [] [] = φ from funext fun _ => rfl]

/-- One certified recurrence equation, read at value slots
(`natEq_value`'s mirror over `NatOps`). -/
theorem natEq_value (m : EnvModel V env) (hops : NatOps m φ)
    {c : Key md} (hc : c ∈ Ix.Kernel.natOpNames) {cv : ConstantVal md}
    {v : Expr md} {hint : ReducibilityHint}
    (hf : env.find? c = some (.defnInfo cv v hint))
    {eq : Expr md × Expr md} (heq : eq ∈ Ix.Kernel.natOpEquations 0 c)
    {L R : AnnotTerm}
    (hdL : denoteMeta m.acval env φ 2 eq.1 = some L)
    (hdR : denoteMeta m.acval env φ 2 eq.2 = some R)
    {ρ : Nat → V} {x y : V}
    (hx : x ∈ˢ interp V ρ (m.acval Ix.Kernel.natName φ))
    (hy : y ∈ˢ interp V ρ (m.acval Ix.Kernel.natName φ)) :
    interp V (cons y (cons x ρ)) L
      = interp V (cons y (cons x ρ)) R := by
  obtain ⟨L', R', hdL', hdR', hval⟩ :=
    (hops c hc cv v hint hf).2 eq heq
  obtain rfl : L' = L := Option.some.inj (hdL'.symm.trans hdL)
  obtain rfl : R' = R := Option.some.inj (hdR'.symm.trans hdR)
  exact hval ρ x y hx hy

/-- **`Nat.add`'s two recurrences, at values**: `add x 0 = x` and
`add x (succ y) = succ (add x y)` for `x`, `y` in the stored `Nat`. -/
theorem natAdd_clauses (m : EnvModel V env) (hops : NatOps m φ)
    (hnh : NatHeads m φ)
    {cv : ConstantVal md} {v : Expr md} {hint : ReducibilityHint}
    (hf : env.find? Ix.Kernel.natAddName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    (∀ x : V,
      x ∈ˢ interp V ρ (m.acval Ix.Kernel.natName φ) →
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natAddName φ)) x)
        (interp V ρ (m.acval Ix.Kernel.natZeroName φ))
      = x) ∧
    (∀ x y : V,
      x ∈ˢ interp V ρ (m.acval Ix.Kernel.natName φ) →
      y ∈ˢ interp V ρ (m.acval Ix.Kernel.natName φ) →
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natAddName φ)) x)
        (SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natSuccName φ)) y)
      = SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natSuccName φ))
          (SetTheory.app (SetTheory.app
            (interp V ρ (m.acval Ix.Kernel.natAddName φ)) x) y)) := by
  obtain ⟨hg, -⟩ := hops Ix.Kernel.natAddName (by (cases md <;> decide)) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := Ix.Kernel.natOpGuard_inv hg
  obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps Ix.Kernel.natAddName
    (by (cases md <;> decide))
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := Ix.Kernel.natLitSupported_inv hs
  have hKc : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const Ix.Kernel.natAddName [])
      = some (m.acval Ix.Kernel.natAddName φ) :=
    fun d => denoteMeta_leaf hfc
      (show (ConstantInfo.defnInfo cvc vc hcnt).toConstantVal.levelParams
        = [] from hlpc)
  have hKz : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const Ix.Kernel.natZeroName [])
      = some (m.acval Ix.Kernel.natZeroName φ) :=
    fun d => denoteMeta_leaf hfZ
      (show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
        = [] from hlpZ)
  have hKs : ∀ d : Nat, denoteMeta m.acval env φ d
      (.const Ix.Kernel.natSuccName [])
      = some (m.acval Ix.Kernel.natSuccName φ) :=
    fun d => denoteMeta_leaf hfS
      (show (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
        = [] from hlpS)
  have hzm : interp V ρ (m.acval Ix.Kernel.natZeroName φ)
      ∈ˢ interp V ρ (m.acval Ix.Kernel.natName φ) := by
    have h := (hnh hs ρ).1
    rw [show Level.substFn φ [] [] = φ from funext fun _ => rfl] at h
    exact h
  -- base clause, read at values
  have h0 : ∀ x : V,
      x ∈ˢ interp V ρ (m.acval Ix.Kernel.natName φ) →
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natAddName φ)) x)
        (interp V ρ (m.acval Ix.Kernel.natZeroName φ))
      = x := by
    intro x hx
    have h := natEq_value m hops (by (cases md <;> decide)) hf
      (eq := (.app (.app (.const Ix.Kernel.natAddName [])
          (.fvar 0
            (.const Ix.Kernel.natName [])))
        (.const Ix.Kernel.natZeroName []),
        .fvar 0 (.const Ix.Kernel.natName [])))
      (by (cases md <;> decide))
      (L := .app (.app (m.acval Ix.Kernel.natAddName φ) (.bvar 1))
        (m.acval Ix.Kernel.natZeroName φ))
      (R := .bvar 1)
      (by rw [denoteMeta_app, denoteMeta_app, hKc 2, denoteMeta_fvar, hKz 2]
          rfl)
      (by rw [denoteMeta_fvar])
      hx hzm
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      leaf_interp_closed m Ix.Kernel.natAddName φ _ ρ,
      leaf_interp_closed m Ix.Kernel.natZeroName φ _ ρ] at h
    exact h
  -- successor clause, read at values
  have hS : ∀ x y : V,
      x ∈ˢ interp V ρ (m.acval Ix.Kernel.natName φ) →
      y ∈ˢ interp V ρ (m.acval Ix.Kernel.natName φ) →
      SetTheory.app (SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natAddName φ)) x)
        (SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natSuccName φ)) y)
      = SetTheory.app
          (interp V ρ (m.acval Ix.Kernel.natSuccName φ))
          (SetTheory.app (SetTheory.app
            (interp V ρ (m.acval Ix.Kernel.natAddName φ)) x) y) := by
    intro x y hx hy
    have h := natEq_value m hops (by (cases md <;> decide)) hf
      (eq := (.app (.app (.const Ix.Kernel.natAddName [])
          (.fvar 0
            (.const Ix.Kernel.natName [])))
        (.app (.const Ix.Kernel.natSuccName [])
          (.fvar 1
            (.const Ix.Kernel.natName []))),
        .app (.const Ix.Kernel.natSuccName [])
          (.app (.app (.const Ix.Kernel.natAddName [])
            (.fvar 0
              (.const Ix.Kernel.natName [])))
            (.fvar 1
              (.const Ix.Kernel.natName [])))))
      (by (cases md <;> decide))
      (L := .app (.app (m.acval Ix.Kernel.natAddName φ) (.bvar 1))
        (.app (m.acval Ix.Kernel.natSuccName φ) (.bvar 0)))
      (R := .app (m.acval Ix.Kernel.natSuccName φ)
        (.app (.app (m.acval Ix.Kernel.natAddName φ) (.bvar 1))
          (.bvar 0)))
      (by rw [denoteMeta_app, denoteMeta_app, hKc 2, denoteMeta_fvar,
            denoteMeta_app, hKs 2, denoteMeta_fvar]
          rfl)
      (by rw [denoteMeta_app, hKs 2, denoteMeta_app, denoteMeta_app, hKc 2,
            denoteMeta_fvar, denoteMeta_fvar]
          rfl)
      hx hy
    simp only [interp_app, interp_bvar, cons_succ, cons_zero,
      leaf_interp_closed m Ix.Kernel.natAddName φ _ ρ,
      leaf_interp_closed m Ix.Kernel.natSuccName φ _ ρ] at h
    exact h
  exact ⟨h0, hS⟩


end Ix.Kernel.Model
