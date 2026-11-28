module

public import IxCK.Kernel.Inductives.WrapCheck
public import IxCK.Kernel.Verify.Level

@[expose] public section

/-!
# Equal up to consumed type-annotation wrappers

Lean's kernel builds a recursor's type and its rules' right-hand sides from locals whose types
have their type-annotation wrappers (`outParam`, `semiOutParam`, `optParam`, `autoParam`) removed at
the head (`consumeTypeAnnotations`, at every local the inductive module creates: parameters,
indices, constructor fields, the binders of a reflexive field's hypothesis). The native route's
generator (`structRecTyR`, `checkNativeRules`) keeps them. The two forms are the same term up to
those wrappers.

`WrapRel find? g d` relates a generated term `g` to a declared one `d`:

* **Positions.** At the domain of every `∀` and every `λ` binder, at every depth (the recursor's own
  telescope, the binders inside a motive's and a minor premise's types, a rule's λ-prefix and the
  binders inside its body), the generated domain may have wrappers at its head that the declared
  domain does not: zero or more, removed one at a time, so a nest of wrappers may be removed in
  part or in full (`WrapDom.consume`). Consumption is never forced: a domain may also keep its
  wrapper (`WrapDom.keep`). Nowhere else: not inside an application's arguments, not in a body.
* **Wrappers, by shape.** A wrapper is a constant stored as a definition whose value is
  `λ x₁ … xₖ, x₁` with every λ's zero-ness datum `never` (`wrapperArity`), applied to exactly `k`
  arguments; consuming it leaves its first argument (`consumeWrapper`). No name is read. The datum
  makes each λ a function in the model, so its application to an argument in its domain reduces.
* **Levels and binder data.** Sort and constant levels agree under every valuation; every
  binder's zero-ness datum (`pw`, which the model reads) is equal. The rest of the binder and
  `let` metadata is free, and a `let` of the declared term is
  expanded (`WrapRel.zeta`), as the statement's `Annotates` expands it.

`wrapRelOk` is a sound incomplete recognizer: it requires syntactic level equality
(`wrapRelOk_sound`).
-/

namespace Ix.Kernel.Semantics

open Ix.Kernel (Key Expr Level LevelParam ConstantInfo Literal)

/-- Two lists related position by position. -/
inductive Forall₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall₂ R [] []
  | cons {a : α} {b : β} {l₁ : List α} {l₂ : List β} :
      R a b → Forall₂ R l₁ l₂ → Forall₂ R (a :: l₁) (b :: l₂)

theorem Forall₂.refl {α : Type} {R : α → α → Prop} (hR : ∀ x, R x x) :
    ∀ xs : List α, Forall₂ R xs xs
  | [] => .nil
  | x :: xs => .cons (hR x) (Forall₂.refl hR xs)


mutual

/-- **`g` and `d` have equivalent levels and wrappers consumed at binder domains.** -/
inductive WrapRel (find? : Key md → Option (ConstantInfo md)) : Expr md → Expr md → Prop
  | bvar (i : Nat) : WrapRel find? (.bvar i) (.bvar i)
  | fvar {i : Nat} {t t' : Expr md} : WrapRel find? t t' → WrapRel find? (.fvar i t) (.fvar i t')
  | sort {u v : Level} :
      (∀ φ : LevelParam → Nat, u.eval φ = v.eval φ) → WrapRel find? (.sort u) (.sort v)
  | const {n : Key md} {us vs : List Level} :
      Forall₂ (fun u v => ∀ φ : LevelParam → Nat, u.eval φ = v.eval φ) us vs →
      WrapRel find? (.const n us) (.const n vs)
  | lit (l : Literal) : WrapRel find? (.lit l) (.lit l)
  | app {f a f' a' : Expr md} :
      WrapRel find? f f' → WrapRel find? a a' → WrapRel find? (.app f a) (.app f' a')
  | lam {t b t' b' : Expr md} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → WrapDom find? t t' → WrapRel find? b b' →
      WrapRel find? (.lam t b m) (.lam t' b' m')
  | forallE {t b t' b' : Expr md} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → WrapDom find? t t' → WrapRel find? b b' →
      WrapRel find? (.forallE t b m) (.forallE t' b' m')
  | letE {t v b t' v' b' : Expr md} {l l' : Ix.Kernel.LetMeta} :
      WrapRel find? t t' → WrapRel find? v v' → WrapRel find? b b' →
      WrapRel find? (.letE t v b l) (.letE t' v' b' l')
  | proj {s : Key md} {i : Nat} {e e' : Expr md} :
      WrapRel find? e e' → WrapRel find? (.proj s i e) (.proj s i e')
  /-- a `let` of the declared term, expanded, as the statement's `Annotates` expands it -/
  | zeta {g t v b : Expr md} {l : Ix.Kernel.LetMeta} :
      WrapRel find? g (b.instantiate1Lift v) → WrapRel find? g (.letE t v b l)

/-- **A binder domain**: equal, or a wrapper application whose first argument is related. -/
inductive WrapDom (find? : Key md → Option (ConstantInfo md)) : Expr md → Expr md → Prop
  | keep {t t' : Expr md} : WrapRel find? t t' → WrapDom find? t t'
  | consume {t a t' : Expr md} :
      consumeWrapper find? t = some a → WrapDom find? a t' → WrapDom find? t t'

end

/-- Every term is related to itself. -/
theorem WrapRel.refl (find? : Key md → Option (ConstantInfo md)) :
    ∀ e : Expr md, WrapRel find? e e
  | .bvar i => .bvar i
  | .fvar _ t => .fvar (WrapRel.refl find? t)
  | .sort _ => .sort (fun _ => rfl)
  | .const _ us => .const (Forall₂.refl (fun _ _ => rfl) us)
  | .lit l => .lit l
  | .app f a => .app (WrapRel.refl find? f) (WrapRel.refl find? a)
  | .lam t b _ => .lam rfl (.keep (WrapRel.refl find? t)) (WrapRel.refl find? b)
  | .forallE t b _ => .forallE rfl (.keep (WrapRel.refl find? t)) (WrapRel.refl find? b)
  | .letE t v b _ => .letE (WrapRel.refl find? t) (WrapRel.refl find? v) (WrapRel.refl find? b)
  | .proj _ _ e => .proj (WrapRel.refl find? e)

theorem WrapDom.refl (find? : Key md → Option (ConstantInfo md)) (e : Expr md) :
    WrapDom find? e e :=
  .keep (WrapRel.refl find? e)

/-! ## Soundness of the executable wrapper checks -/
mutual

theorem wrapRelB_sound (find? : Key md → Option (ConstantInfo md)) :
    ∀ (fuel : Nat) (g d : Expr md), wrapRelB find? fuel g d = true → WrapRel find? g d
  | 0, _, _, h => by simp [wrapRelB] at h
  | fuel + 1, g, d, h => by
    cases g <;> cases d <;>
      simp only [wrapRelB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true] at h
    all_goals first
      | exact .zeta (wrapRelB_sound find? fuel _ _ h)
      | (rcases h with ⟨⟨h1, h2⟩, h3⟩ | h
         · exact .letE (wrapRelB_sound find? fuel _ _ h1) (wrapRelB_sound find? fuel _ _ h2)
             (wrapRelB_sound find? fuel _ _ h3)
         · exact .zeta (wrapRelB_sound find? fuel _ _ h))
      | (subst h; exact .bvar _)
      | (subst h; exact .sort (fun _ => rfl))
      | (subst h; exact .lit _)
      | (obtain ⟨rfl, h⟩ := h; exact .fvar (wrapRelB_sound find? fuel _ _ h))
      | (obtain ⟨rfl, rfl⟩ := h; exact .const (Forall₂.refl (fun _ _ => rfl) _))
      | exact .app (wrapRelB_sound find? fuel _ _ h.1) (wrapRelB_sound find? fuel _ _ h.2)
      | exact .lam h.1.1 (wrapDomB_sound find? fuel _ _ h.1.2) (wrapRelB_sound find? fuel _ _ h.2)
      | exact .forallE h.1.1 (wrapDomB_sound find? fuel _ _ h.1.2)
          (wrapRelB_sound find? fuel _ _ h.2)
      | (obtain ⟨⟨rfl, rfl⟩, h⟩ := h; exact .proj (wrapRelB_sound find? fuel _ _ h))

theorem wrapDomB_sound (find? : Key md → Option (ConstantInfo md)) :
    ∀ (fuel : Nat) (t t' : Expr md), wrapDomB find? fuel t t' = true → WrapDom find? t t'
  | 0, _, _, h => by simp [wrapDomB] at h
  | fuel + 1, t, t', h => by
    simp only [wrapDomB, Bool.or_eq_true] at h
    rcases h with h | h
    · exact .keep (wrapRelB_sound find? fuel t t' h)
    · cases hc : consumeWrapper find? t with
      | none => rw [hc] at h; exact absurd h (by simp)
      | some a =>
        rw [hc] at h
        exact .consume hc (wrapDomB_sound find? fuel a t' h)

end

/-- **The recognizer is sound.** -/
theorem wrapRelOk_sound {find? : Key md → Option (ConstantInfo md)} {g d : Expr md}
    (h : wrapRelOk find? g d = true) : WrapRel find? g d :=
  wrapRelB_sound find? _ g d h

end Ix.Kernel.Semantics
