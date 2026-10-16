module

public import Ix.LeanIngress.Expr

/-! # Lean's binder names on the Source terms (IxC step 6b, display only)

The Source ingress converts a Lean term (`ingressExpr`) without its binder
names. A failure prints terms with Lean's names, reduced terms included, so the
names must travel inside the terms the checker holds, as in Lean. This module
writes them: `nameExprs es ks` is the conversions `ks` of the Lean terms `es`
with each binder annotated with Lean's name and binder info, and each `let`
with Lean's name (`BinderMeta.display`, `LetMeta.display`).

The annotations are subsingletons (`Squash`), so the annotated terms **are**
the conversions (`nameExprs_eq`): every statement about the Source ingress, the
checker and the `CanonM` correspondence holds of them unchanged, and the
checker's verdicts are the same. Only a renderer outside the kernel can read a
name (`Ix.Kernel.Display`).

The walk follows the Lean term and its conversion together: a binder of the
term is a binder of the conversion (`mdata` is skipped, as `ingressExpr` skips
it; a contract frame changes the binder's contracts, not its kind). A node
whose conversion is not of the same kind is left as it is. The terms are DAGs,
so the walk is memoized by the Lean node's content hash, and a hit is used
only for the conversion it was recorded at (`==`, a pointer test at run
time). -/

public section

namespace Ix.LeanIngress

/-- Lean's binder annotation as the checker's display one. -/
@[expose] def ingressBinderInfo : Lean.BinderInfo → Ix.Kernel.BinderInfo
  | .default => .default
  | .implicit => .implicit
  | .strictImplicit => .strictImplicit
  | .instImplicit => .instImplicit

/-- A binder's metadata with a Lean name: the same binder (the annotation is a
subsingleton). -/
theorem binderMeta_named (m : Ix.Kernel.BinderMeta) (d : Squash Ix.Kernel.BinderDisplay) :
    { m with display := d } = m := by
  obtain ⟨p, c, r, d0⟩ := m
  show Ix.Kernel.BinderMeta.mk p c r d = Ix.Kernel.BinderMeta.mk p c r d0
  rw [Subsingleton.elim d d0]

/-- A let's metadata with a Lean name: the same let. -/
theorem letMeta_named (l : Ix.Kernel.LetMeta) (d : Squash Ix.Kernel.Name) :
    { l with display := d } = l := by
  obtain ⟨c, d0⟩ := l
  show Ix.Kernel.LetMeta.mk c d = Ix.Kernel.LetMeta.mk c d0
  rw [Subsingleton.elim d d0]

/-- A memo entry: the conversion a node was annotated at, and the result. -/
structure NameEntry where
  k : KExpr
  v : KExpr
  eq : v = k

/-- The walk's memo, under the Lean node's content hash. -/
abbrev NameMemo := Std.HashMap Address NameEntry

/-- **The names of `e` on its conversion `k`**, with the memo. -/
def nameGo (e : Ix.Expr) (k : KExpr) : StateM NameMemo { v : KExpr // v = k } :=
  match e, k with
  | .lam n t b bi h, .lam kt kb m => memo h do
    let t' ← nameGo t kt
    let b' ← nameGo b kb
    pure ⟨.lam t'.1 b'.1 { m with display := Squash.mk ⟨ingressName n, ingressBinderInfo bi⟩ },
      by rw [t'.2, b'.2, binderMeta_named]⟩
  | .forallE n t b bi h, .forallE kt kb m => memo h do
    let t' ← nameGo t kt
    let b' ← nameGo b kb
    pure ⟨.forallE t'.1 b'.1
        { m with display := Squash.mk ⟨ingressName n, ingressBinderInfo bi⟩ },
      by rw [t'.2, b'.2, binderMeta_named]⟩
  | .letE n t v b _ h, .letE kt kv kb l => memo h do
    let t' ← nameGo t kt
    let v' ← nameGo v kv
    let b' ← nameGo b kb
    pure ⟨.letE t'.1 v'.1 b'.1 { l with display := Squash.mk (ingressName n) },
      by rw [t'.2, v'.2, b'.2, letMeta_named]⟩
  | .app f a h, .app kf ka => memo h do
    let f' ← nameGo f kf
    let a' ← nameGo a ka
    pure ⟨.app f'.1 a'.1, by rw [f'.2, a'.2]⟩
  | .proj _ _ b h, .proj s i kb => memo h do
    let b' ← nameGo b kb
    pure ⟨.proj s i b'.1, by rw [b'.2]⟩
  | .mdata _ b _, k => nameGo b k
  | _, k => pure ⟨k, rfl⟩
where
  /-- The memoized step at the node of hash `h`: a hit recorded at the same
  conversion, or the step, recorded. -/
  memo {k : KExpr} (h : Address) (step : StateM NameMemo { v : KExpr // v = k }) :
      StateM NameMemo { v : KExpr // v = k } := do
    if let some en := (← get)[h]? then
      if hk : en.k == k then
        return ⟨en.v, en.eq.trans (eq_of_beq hk)⟩
    let r ← step
    modify (·.insert h ⟨k, r.1, r.2⟩)
    return r

/-- Several terms' names, with one memo. -/
def nameGoList : (es : List Ix.Expr) → (ks : List KExpr) →
    StateM NameMemo { vs : List KExpr // vs = ks }
  | e :: es, k :: ks => do
    let v ← nameGo e k
    let vs ← nameGoList es ks
    pure ⟨v.1 :: vs.1, by rw [v.2, vs.2]⟩
  | _, ks => pure ⟨ks, rfl⟩

/-- **Lean's binder names on the conversions `ks` of the terms `es`** (display
only). -/
def nameExprs (es : List Ix.Expr) (ks : List KExpr) : List KExpr :=
  ((nameGoList es ks).run' {}).1

/-- The annotated conversions are the conversions. -/
theorem nameExprs_eq (es : List Ix.Expr) (ks : List KExpr) : nameExprs es ks = ks :=
  ((nameGoList es ks).run' {}).2

end Ix.LeanIngress
