module

public import IxC.Kernel.Env
public import IxC.Kernel.ExprOps

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
* **Everything else is equal**: every binder's zero-ness datum (`pw`, which the model reads) is
  equal; the rest of the binder and `let` metadata is free, and a `let` of the declared term is
  expanded (`WrapRel.zeta`), as the statement's `Annotates` expands it.

`wrapRelOk` decides it, with a budget no derivation needs to exceed (`wrapRelOk_sound`).
-/

namespace Ix.Kernel.Semantics

open Ix.Kernel (Key Expr Level ConstantInfo Literal)

/-- The arity of a value `λ x₁ … xₖ, x₁` (`k ≥ 1`) whose binders' zero-ness data are all `never`
(the λs are functions, never proofs), after `n` binders already passed. -/
def lamFirstArity : Expr md → Nat → Option Nat
  | .lam _ b m, n => if m.pw.isNever then lamFirstArity b (n + 1) else none
  | .bvar i, n => if 0 < n && i == n - 1 then some n else none
  | _, _ => none

/-- **A wrapper**: a constant stored as a definition whose value is `λ x₁ … xₖ, x₁`; its arity. -/
def wrapperArity (find? : Key md → Option (ConstantInfo md)) (w : Key md) : Option Nat :=
  match find? w with
  | some (.defnInfo _ v _) => lamFirstArity v 0
  | _ => none

/-- **One consumption**: a wrapper applied to exactly its arity leaves its first argument. -/
def consumeWrapper (find? : Key md → Option (ConstantInfo md)) (t : Expr md) : Option (Expr md) :=
  match t.getAppFn, t.getAppArgs with
  | .const w _, a :: rest => if wrapperArity find? w == some (rest.length + 1) then some a else none
  | _, _ => none

mutual

/-- **`g` is `d` with wrappers consumed at binder domains.** -/
inductive WrapRel (find? : Key md → Option (ConstantInfo md)) : Expr md → Expr md → Prop
  | bvar (i : Nat) : WrapRel find? (.bvar i) (.bvar i)
  | fvar {i : Nat} {t t' : Expr md} : WrapRel find? t t' → WrapRel find? (.fvar i t) (.fvar i t')
  | sort (u : Level) : WrapRel find? (.sort u) (.sort u)
  | const (n : Key md) (us : List Level) : WrapRel find? (.const n us) (.const n us)
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
  | .sort u => .sort u
  | .const n us => .const n us
  | .lit l => .lit l
  | .app f a => .app (WrapRel.refl find? f) (WrapRel.refl find? a)
  | .lam t b _ => .lam rfl (.keep (WrapRel.refl find? t)) (WrapRel.refl find? b)
  | .forallE t b _ => .forallE rfl (.keep (WrapRel.refl find? t)) (WrapRel.refl find? b)
  | .letE t v b _ => .letE (WrapRel.refl find? t) (WrapRel.refl find? v) (WrapRel.refl find? b)
  | .proj _ _ e => .proj (WrapRel.refl find? e)

theorem WrapDom.refl (find? : Key md → Option (ConstantInfo md)) (e : Expr md) :
    WrapDom find? e e :=
  .keep (WrapRel.refl find? e)

/-! ## The decision -/

/-- The number of nodes of a term. -/
def exprSize : Expr md → Nat
  | .fvar _ t => exprSize t + 1
  | .app f a => exprSize f + exprSize a + 1
  | .lam t b _ => exprSize t + exprSize b + 1
  | .forallE t b _ => exprSize t + exprSize b + 1
  | .letE t v b _ => exprSize t + exprSize v + exprSize b + 1
  | .proj _ _ e => exprSize e + 1
  | _ => 1

mutual

/-- `WrapRel`, at a budget of recursive steps. -/
def wrapRelB (find? : Key md → Option (ConstantInfo md)) : Nat → Expr md → Expr md → Bool
  | 0, _, _ => false
  | fuel + 1, g, d =>
    match g, d with
    | .letE t v b l, .letE t' v' b' _ =>
      (wrapRelB find? fuel t t' && wrapRelB find? fuel v v' && wrapRelB find? fuel b b') ||
        wrapRelB find? fuel (.letE t v b l) (b'.instantiate1Lift v')
    | g, .letE _ v' b' _ => wrapRelB find? fuel g (b'.instantiate1Lift v')
    | .bvar i, .bvar j => i == j
    | .fvar i t, .fvar j t' => i == j && wrapRelB find? fuel t t'
    | .sort u, .sort v => u == v
    | .const n us, .const n' us' => n == n' && us == us'
    | .lit l, .lit l' => l == l'
    | .app f a, .app f' a' => wrapRelB find? fuel f f' && wrapRelB find? fuel a a'
    | .lam t b m, .lam t' b' m' =>
      m.pw == m'.pw && wrapDomB find? fuel t t' && wrapRelB find? fuel b b'
    | .forallE t b m, .forallE t' b' m' =>
      m.pw == m'.pw && wrapDomB find? fuel t t' && wrapRelB find? fuel b b'
    | .proj s i e, .proj s' i' e' => s == s' && i == i' && wrapRelB find? fuel e e'
    | _, _ => false

/-- `WrapDom`, at a budget of recursive steps. -/
def wrapDomB (find? : Key md → Option (ConstantInfo md)) : Nat → Expr md → Expr md → Bool
  | 0, _, _ => false
  | fuel + 1, t, t' =>
    wrapRelB find? fuel t t' ||
      match consumeWrapper find? t with
      | some a => wrapDomB find? fuel a t'
      | none => false

end

/-- **The decision**: `WrapRel` at a budget of twice the generated term's size, enough for every
step of the walk and every consumption (each consumption leaves a strict subterm). -/
def wrapRelOk (find? : Key md → Option (ConstantInfo md)) (g d : Expr md) : Bool :=
  wrapRelB find? (2 * (exprSize g + exprSize d) + 2) g d

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
      | (subst h; exact .sort _)
      | (subst h; exact .lit _)
      | (obtain ⟨rfl, h⟩ := h; exact .fvar (wrapRelB_sound find? fuel _ _ h))
      | (obtain ⟨rfl, rfl⟩ := h; exact .const _ _)
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

/-- **The decision is sound.** -/
theorem wrapRelOk_sound {find? : Key md → Option (ConstantInfo md)} {g d : Expr md}
    (h : wrapRelOk find? g d = true) : WrapRel find? g d :=
  wrapRelB_sound find? _ g d h

end Ix.Kernel.Semantics
