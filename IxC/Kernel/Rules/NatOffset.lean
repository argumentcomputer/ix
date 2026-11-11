module

public import IxC.Kernel.Rules.Rel
public import IxC.Kernel.Rules.TransportKit

@[expose] public section

/-!
# The `Nat` offset helpers, inverted

What the offset rules' soundness, transport and renaming read of `natAddTyOk`,
`natAddLit` and `natOffsetOf` (`Rules/Rel.lean`):

* the pinned shape of a stored `Nat.add` (`natAddTyOk_inv`);
* the three shapes that have an offset, with their one-step reading
  (`natOffsetOf_some`, `natOffsetStep_eq`);
* a recursion principle along the steps (`natOffsetOf_rec`): to prove a fact of a
  term, assume it of the term `x` under `Nat.succ x` or `Nat.add x (lit n)`;
* the commutation of `natAddLit` and `natOffsetOf` with free-variable renaming.
-/

namespace Ix.Kernel.Rules

open Ix.Kernel.Expr (renFV)

/-- **`natAddTyOk`, inverted**: the stored `Nat.add` has no level parameters, the
type `Nat → Nat → Nat`, and a `never` datum at its outer binder. -/
theorem natAddTyOk_inv {o : Option (ConstantInfo md)} (h : natAddTyOk o = true) :
    ∃ (n : Key md) (v : Expr md) (hint : ReducibilityHint) (mb₁ mb₂ : BinderMeta),
      o = some (.defnInfo ⟨n, [], .forallE (.const natName [])
        (.forallE (.const natName []) (.const natName []) mb₂) mb₁⟩ v hint) ∧
      mb₁.pw.isNever = true := by
  cases o with
  | none => exact nomatch h
  | some ci =>
    cases ci with
    | defnInfo cv v hint =>
      obtain ⟨n, lps, ty⟩ := cv
      simp only [natAddTyOk, Bool.and_eq_true, List.isEmpty_iff] at h
      obtain ⟨rfl, hty⟩ := h
      split at hty
      · simp only [Bool.and_eq_true, beq_iff_eq] at hty
        obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, hnev⟩ := hty
        subst_vars
        exact ⟨n, v, hint, _, _, rfl, hnev⟩
      · exact nomatch hty
    | _ => exact nomatch h

theorem natAddLit_zero (b : Expr md) : natAddLit b 0 = b := by
  unfold natAddLit
  exact ite_eq_left rfl

theorem natAddLit_succ (b : Expr md) (k : Nat) :
    natAddLit b (k + 1) = .app (.app (.const natAddName []) b) (.lit (.natVal (k + 1))) := by
  unfold natAddLit
  exact ite_eq_right (Nat.succ_ne_zero k)

/-- `natOffsetOf` at a literal. -/
theorem natOffsetOf_lit (n : Nat) :
    natOffsetOf (.lit (.natVal n) : Expr md) = some (.lit (.natVal 0), n) := rfl

/-- `natOffsetOf` at a constant applied once. -/
theorem natOffsetOf_succ (c : Key md) (us : List Level) (x : Expr md) :
    natOffsetOf (.app (.const c us) x) =
      if c = natSuccName then some (natOffsetStep x (natOffsetOf x) 1) else none := rfl

/-- `natOffsetOf` at a constant applied to a term and a literal. -/
theorem natOffsetOf_add (c : Key md) (us : List Level) (x : Expr md) (m : Nat) :
    natOffsetOf (.app (.app (.const c us) x) (.lit (.natVal m))) =
      if c = natAddName then some (natOffsetStep x (natOffsetOf x) m) else none := rfl

/-- `natOffsetStep`, inverted. -/
theorem natOffsetStep_eq {x b : Expr md} {o : Option (Expr md × Nat)} {n k : Nat}
    (h : natOffsetStep x o n = (b, k)) :
    (∃ k', o = some (b, k') ∧ k = k' + n) ∨ (o = none ∧ b = x ∧ k = n) := by
  cases o with
  | none =>
    simp only [natOffsetStep, Prod.mk.injEq] at h
    exact Or.inr ⟨rfl, h.1.symm, h.2.symm⟩
  | some p =>
    obtain ⟨b', k'⟩ := p
    simp only [natOffsetStep, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨k', rfl, rfl⟩

/-- **`natOffsetOf`, inverted**: a term with an offset is a literal, a `Nat.succ`
application or a `Nat.add` application to a literal, and its offset is that shape's
step. -/
theorem natOffsetOf_some {e b : Expr md} {k : Nat} (h : natOffsetOf e = some (b, k)) :
    (e = .lit (.natVal k) ∧ b = .lit (.natVal 0)) ∨
    (∃ us x, e = .app (.const natSuccName us) x ∧
      natOffsetStep x (natOffsetOf x) 1 = (b, k)) ∨
    (∃ us x n, e = .app (.app (.const natAddName us) x) (.lit (.natVal n)) ∧
      natOffsetStep x (natOffsetOf x) n = (b, k)) := by
  cases e with
  | lit l =>
    cases l with
    | natVal n =>
      rw [natOffsetOf_lit] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨rfl, rfl⟩
    | strVal _ => exact nomatch h
  | app f x =>
    cases f with
    | const c us =>
      rw [natOffsetOf_succ] at h
      by_cases hc : c = natSuccName
      · subst hc
        rw [ite_eq_left rfl] at h
        exact Or.inr (Or.inl ⟨us, x, rfl, Option.some.inj h⟩)
      · rw [ite_eq_right hc] at h
        exact nomatch h
    | app g y =>
      cases g with
      | const c us =>
        cases x with
        | lit l =>
          cases l with
          | natVal n =>
            rw [natOffsetOf_add] at h
            by_cases hc : c = natAddName
            · subst hc
              rw [ite_eq_left rfl] at h
              exact Or.inr (Or.inr ⟨us, y, n, rfl, Option.some.inj h⟩)
            · rw [ite_eq_right hc] at h
              exact nomatch h
          | strVal _ => exact nomatch h
        | _ => exact nomatch h
      | _ => exact nomatch h
    | _ => exact nomatch h
  | _ => exact nomatch h

/-- **Recursion along `natOffsetOf`**: to prove `Q e`, assume `Q x` for the term `x`
an offset step reads under `e` (`Nat.succ x`, or `Nat.add x (lit n)`). -/
theorem natOffsetOf_rec {Q : Expr md → Prop}
    (step : ∀ e, (∀ x, ((∃ us, e = .app (.const natSuccName us) x) ∨
      (∃ us n, e = .app (.app (.const natAddName us) x) (.lit (.natVal n)))) → Q x) → Q e) :
    ∀ e, Q e := by
  suffices h : ∀ e : Expr md, Q e ∧ ∀ g y, e = .app g y → Q y from fun e => (h e).1
  intro e
  induction e with
  | app f a ihf iha =>
    refine ⟨step _ fun x hx => ?_, fun g y he => ?_⟩
    · rcases hx with ⟨us, he⟩ | ⟨us, n, he⟩
      · injection he with _ h₂
        subst h₂
        exact iha.1
      · injection he with h₁ _
        exact ihf.2 _ _ h₁
    · injection he with _ h₂
      subst h₂
      exact iha.1
  | _ =>
    refine ⟨step _ fun x hx => ?_, fun g y he => nomatch he⟩
    rcases hx with ⟨_, he⟩ | ⟨_, _, he⟩ <;> exact nomatch he

/-! ## Free-variable renaming -/

theorem natAddLit_renFV (ρ : Nat → Nat) (b : Expr md) (k : Nat) :
    (natAddLit b k).renFV ρ = natAddLit (b.renFV ρ) k := by
  unfold natAddLit
  by_cases hk : k = 0
  · rw [ite_eq_left hk, ite_eq_left hk]
  · rw [ite_eq_right hk, ite_eq_right hk]
    rfl

/-- **`natOffsetOf` commutes with renaming free variables.** -/
theorem natOffsetOf_renFV (ρ : Nat → Nat) : ∀ e : Expr md,
    natOffsetOf (e.renFV ρ) = (natOffsetOf e).map (fun p => (p.1.renFV ρ, p.2)) := by
  refine natOffsetOf_rec (fun e ih => ?_)
  cases e with
  | lit l => cases l <;> rfl
  | app f x =>
    cases f with
    | const c us =>
      show natOffsetOf (.app (.const c us) (x.renFV ρ)) = _
      rw [natOffsetOf_succ, natOffsetOf_succ]
      by_cases hc : c = natSuccName
      · subst hc
        rw [ite_eq_left rfl, ite_eq_left rfl, ih x (Or.inl ⟨us, rfl⟩)]
        cases natOffsetOf x with
        | none => rfl
        | some p => obtain ⟨b, k⟩ := p; rfl
      · rw [ite_eq_right hc, ite_eq_right hc]
        rfl
    | app g y =>
      cases g with
      | const c us =>
        cases x with
        | lit l =>
          cases l with
          | natVal m =>
            show natOffsetOf (.app (.app (.const c us) (y.renFV ρ)) (.lit (.natVal m))) = _
            rw [natOffsetOf_add, natOffsetOf_add]
            by_cases hc : c = natAddName
            · subst hc
              rw [ite_eq_left rfl, ite_eq_left rfl, ih y (Or.inr ⟨us, m, rfl⟩)]
              cases natOffsetOf y with
              | none => rfl
              | some p => obtain ⟨b, k⟩ := p; rfl
            · rw [ite_eq_right hc, ite_eq_right hc]
              rfl
          | strVal _ => rfl
        | _ => rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

end Ix.Kernel.Rules
