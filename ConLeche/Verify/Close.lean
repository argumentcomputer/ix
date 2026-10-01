module

public import ConLeche.Verify.Shift

public section

/-!
# Closing free variables as de Bruijn indices

The checker opens a binder with a fresh `fvar d` and reads the body at
depth `d + 1` (`denoteMeta`, `denote`); the statement's relation
`Denotes` (`ConLeche/Denotes.lean`) reads the body under its binder
with `bvar 0` for the bound variable.  `closeN d e k` translates: every
`fvar idx` with `idx < d` becomes the de Bruijn index `k + (d - 1 - idx)`
at cursor `k` (bumped under binders) — the index the open reading
already assigns it (`.bvar (d - 1 - idx)` at the leaf, plus the
binders crossed).  The two lemmas are the whole use: closing commutes
with opening one more binder (`closeN_instantiate1`), and a term with
no free variable is its own closure (`closeN_of_hasFvar`).
-/

namespace ConLeche.Expr

/-- Close the free variables below `d` as de Bruijn indices; `k` is the
number of binders crossed. -/
@[expose] def closeN (d : Nat) : Expr → (k : Nat := 0) → Expr
  | .fvar idx _, k => .bvar (k + (d - 1 - idx))
  | .bvar i, _ => .bvar i
  | .sort u, _ => .sort u
  | .const n us, _ => .const n us
  | .app f a, k => .app (closeN d f k) (closeN d a k)
  | .lam ty body m, k => .lam (closeN d ty k) (closeN d body (k + 1)) m
  | .forallE ty body m, k => .forallE (closeN d ty k) (closeN d body (k + 1)) m
  | .letE ty v b, k => .letE (closeN d ty k) (closeN d v k) (closeN d b (k + 1))
  | .lit l, _ => .lit l
  | .proj s i e, k => .proj s i (closeN d e k)

/-- A term without free variables is its own closure. -/
theorem closeN_of_hasFvar : ∀ (e : Expr) (d k : Nat), e.hasFvar = false →
    closeN d e k = e := by
  intro e
  induction e <;> intro d k h <;> simp_all [closeN, hasFvar]

/-- Closing commutes with opening: opening the outermost binder with
`fvar d` and closing at depth `d + 1` is closing the body at depth `d`
one binder in.  The body must be locally closed at its binder
(`looseBVarsBounded (k + 1)`) and scoped below `d`. -/
theorem closeN_instantiate1 {d : Nat} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded (k + 1) = true →
      fvarsBelow d e →
      closeN (d + 1) (e.instantiate1 (.fvar d ty) k) k = closeN d e (k + 1) := by
  intro e
  induction e <;> intro k hb hf <;>
    simp_all [closeN, instantiate1, looseBVarsBounded, fvarsBelow]
  case bvar i =>
    by_cases hik : i = k
    · subst hik; simp [closeN]
    · have : ¬ i > k := by omega
      simp [closeN, hik, this]
  case fvar idx ty' =>
    omega

end ConLeche.Expr
