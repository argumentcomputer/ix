import Aiur.Scalar.Circuit.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
Sparse multivariate polynomials with an executable normal form, used to
validate tiled templates. Only soundness is proved: `norm` preserves the
denotation, so equal normal forms denote equal functions. A non-canonical
result can only make the template checker reject.
-/

namespace Aiur.Tiling

open Aiur.Scalar.Circuit (ArithExpr)

/-- A monomial: the multiset of its variables, kept sorted. -/
abbrev Mono := List Nat

/-- A sum of coefficient-weighted monomials. -/
abbrev Poly (F : Type) := List (Mono × F)

namespace Mono

def eval [CommRing F] (a : Nat → F) (m : Mono) : F := (m.map a).prod

def insert (v : Nat) : Mono → Mono
  | [] => [v]
  | w :: m => if v ≤ w then v :: w :: m else w :: insert v m

def mul (m n : Mono) : Mono := n.foldr insert m

/-- Strict lexicographic order on monomials. -/
def lt : Mono → Mono → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | v :: m, w :: n => v < w || (v == w && lt m n)

variable {F : Type} [CommRing F]

@[simp] theorem eval_nil (a : Nat → F) : eval a [] = 1 := rfl

@[simp] theorem eval_cons (a : Nat → F) (v : Nat) (m : Mono) :
    eval a (v :: m) = a v * eval a m := by simp [eval]

theorem eval_insert (a : Nat → F) (v : Nat) (m : Mono) :
    eval a (insert v m) = a v * eval a m := by
  induction m with
  | nil => simp [insert]
  | cons w m ih =>
      unfold insert
      split
      · simp
      · simp only [eval_cons, ih]; ring

theorem eval_mul (a : Nat → F) (m n : Mono) : eval a (mul m n) = eval a m * eval a n := by
  induction n with
  | nil => simp [mul]
  | cons v n ih =>
      simp only [mul, List.foldr_cons] at ih ⊢
      rw [eval_insert, ih, eval_cons]; ring

end Mono

namespace Poly

variable {F : Type}

def denote [CommRing F] (a : Nat → F) (p : Poly F) : F :=
  (p.map fun t => t.2 * Mono.eval a t.1).sum

def const (c : F) : Poly F := [([], c)]
def var [One F] (v : Nat) : Poly F := [([v], 1)]
def add (p q : Poly F) : Poly F := p ++ q
def scale [Mul F] (c : F) (p : Poly F) : Poly F := p.map fun t => (t.1, c * t.2)
def neg [Neg F] (p : Poly F) : Poly F := p.map fun t => (t.1, -t.2)
def sub [Neg F] (p q : Poly F) : Poly F := p ++ q.neg
def mul [Mul F] (p q : Poly F) : Poly F :=
  p.flatMap fun t => q.map fun u => (Mono.mul t.1 u.1, t.2 * u.2)

/-- Replace every variable `v` by the polynomial `σ v`. -/
def substMono [CommRing F] (σ : Nat → Poly F) (m : Mono) : Poly F :=
  m.foldr (fun v acc => mul (σ v) acc) (const 1)

def subst [CommRing F] (σ : Nat → Poly F) (p : Poly F) : Poly F :=
  p.flatMap fun t => scale t.2 (substMono σ t.1)

def ofExpr [CommRing F] : ArithExpr F → Poly F
  | .const c => const c
  | .var v => var v
  | .add x y => add (ofExpr x) (ofExpr y)
  | .sub x y => sub (ofExpr x) (ofExpr y)
  | .mul x y => mul (ofExpr x) (ofExpr y)

/-- Insert one term into a sorted, merged polynomial, dropping zero terms. -/
def insertTerm [Add F] [Zero F] [DecidableEq F] (t : Mono × F) : Poly F → Poly F
  | [] => if t.2 = 0 then [] else [t]
  | u :: p =>
      if t.1 = u.1 then
        if t.2 + u.2 = 0 then p else (u.1, t.2 + u.2) :: p
      else if Mono.lt t.1 u.1 then
        if t.2 = 0 then u :: p else t :: u :: p
      else u :: insertTerm t p

def norm [Add F] [Zero F] [DecidableEq F] (p : Poly F) : Poly F := p.foldr insertTerm []

/-- Executable identity test; see `Identical.denote`. -/
def Identical [Add F] [Zero F] [DecidableEq F] (p q : Poly F) : Bool := norm p == norm q

section Semantics

variable [CommRing F] (a : Nat → F)

@[simp] theorem denote_nil : denote a ([] : Poly F) = 0 := rfl

@[simp] theorem denote_cons (t : Mono × F) (p : Poly F) :
    denote a (t :: p) = t.2 * Mono.eval a t.1 + denote a p := by simp [denote]

@[simp] theorem denote_append (p q : Poly F) : denote a (p ++ q) = denote a p + denote a q := by
  simp [denote]

@[simp] theorem denote_const (c : F) : denote a (const c) = c := by simp [const]

@[simp] theorem denote_var (v : Nat) : denote a (var v : Poly F) = a v := by simp [var]

@[simp] theorem denote_add (p q : Poly F) : denote a (add p q) = denote a p + denote a q :=
  denote_append a p q

@[simp] theorem denote_scale (c : F) (p : Poly F) : denote a (scale c p) = c * denote a p := by
  induction p with
  | nil => simp [scale]
  | cons t p ih =>
      simp only [scale, List.map_cons, denote_cons] at ih ⊢
      rw [ih]; ring

@[simp] theorem denote_neg (p : Poly F) : denote a (neg p) = -denote a p := by
  induction p with
  | nil => simp [neg]
  | cons t p ih =>
      simp only [neg, List.map_cons, denote_cons] at ih ⊢
      rw [ih]; ring

@[simp] theorem denote_sub (p q : Poly F) : denote a (sub p q) = denote a p - denote a q := by
  simp [sub, sub_eq_add_neg]

theorem denote_mulTerm (t : Mono × F) (q : Poly F) :
    denote a (q.map fun u => (Mono.mul t.1 u.1, t.2 * u.2)) = t.2 * Mono.eval a t.1 * denote a q := by
  induction q with
  | nil => simp
  | cons u q ih =>
      simp only [List.map_cons, denote_cons, Mono.eval_mul, ih]; ring

@[simp] theorem denote_mul (p q : Poly F) : denote a (mul p q) = denote a p * denote a q := by
  induction p with
  | nil => simp [mul]
  | cons t p ih =>
      simp only [mul, List.flatMap_cons, denote_append, denote_cons] at ih ⊢
      rw [denote_mulTerm, ih]; ring

theorem denote_substMono (σ : Nat → Poly F) (m : Mono) :
    denote a (substMono σ m) = Mono.eval (fun v => denote a (σ v)) m := by
  induction m with
  | nil => simp [substMono]
  | cons v m ih => simp only [substMono, List.foldr_cons] at ih ⊢; rw [denote_mul, ih]; simp

theorem denote_subst (σ : Nat → Poly F) (p : Poly F) :
    denote a (subst σ p) = denote (fun v => denote a (σ v)) p := by
  induction p with
  | nil => simp [subst]
  | cons t p ih =>
      simp only [subst, List.flatMap_cons, denote_append, denote_cons] at ih ⊢
      rw [ih, denote_scale, denote_substMono]

variable [DecidableEq F]

theorem denote_insertTerm (t : Mono × F) (p : Poly F) :
    denote a (insertTerm t p) = t.2 * Mono.eval a t.1 + denote a p := by
  induction p with
  | nil =>
      unfold insertTerm
      split
      · simp [*]
      · simp
  | cons u p ih =>
      unfold insertTerm
      by_cases same : t.1 = u.1
      · simp only [same, ↓reduceIte]
        split
        · rename_i zero
          simp only [denote_cons]
          have : t.2 * Mono.eval a u.1 + u.2 * Mono.eval a u.1 = 0 := by
            rw [← add_mul, zero]; simp
          linear_combination -this
        · simp only [denote_cons]; ring
      · simp only [same, ↓reduceIte]
        split
        · split
          · rename_i _ zero
            simp [zero]
          · simp
        · simp only [denote_cons, ih]; ring

theorem denote_norm (p : Poly F) : denote a (norm p) = denote a p := by
  induction p with
  | nil => rfl
  | cons t p ih => simp only [norm, List.foldr_cons] at ih ⊢; rw [denote_insertTerm, ih, denote_cons]

theorem Identical.denote {p q : Poly F} (same : Identical p q = true) :
    Poly.denote a p = Poly.denote a q := by
  have equal : norm p = norm q := by simpa [Identical] using same
  rw [← denote_norm a p, ← denote_norm a q, equal]

end Semantics

theorem denote_ofExpr [Field F] (a : Nat → F) (e : ArithExpr F) :
    denote a (ofExpr e) = e.denote a := by
  induction e with
  | const c => simp [ofExpr, ArithExpr.denote]
  | var v => simp [ofExpr, ArithExpr.denote]
  | add x y hx hy => simp [ofExpr, ArithExpr.denote, hx, hy]
  | sub x y hx hy => simp [ofExpr, ArithExpr.denote, hx, hy]
  | mul x y hx hy => simp [ofExpr, ArithExpr.denote, hx, hy]

end Poly

end Aiur.Tiling
