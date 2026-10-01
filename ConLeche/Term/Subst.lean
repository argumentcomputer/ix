module

public import ConLeche.Term.Syntax

@[expose] public section

/-!
# Lifting and instantiation

The two de Bruijn operations every reading of a stored term needs:
`liftN` (weakening) and `inst` (single substitution).

**This module is deliberately tiny.**  lean4lean's corresponding file
is ~800 lines and 123 theorems of substitution boilerplate, roughly a
third of its declarative layer, because its metatheory (Church–Rosser,
unique typing, weakening, inversion) is *syntactic* and every step has
to commute lifts and substitutions past each other.  Here the only
metatheorem is soundness, which goes straight to the model, so the
substitution facts that are actually needed are *semantic* ones
(`ConLeche/Semantics/*`).  Everything below is definitions plus their
constructor-wise `rfl` equations; what syntactic commutation the
bridge does need is filed with the bridge, in
`ConLeche/Verify/Denote/SubstAlgebra.lean` until task #221 deleted it
unread; the live algebra is `ConLeche/Model/IndSubst.lean`'s, at
`AnnotTerm`.
-/

namespace ConLeche.Term
namespace Term

/-- Weakening: insert `n` fresh binders at depth `k`. -/
def liftN (n : Nat) : Term → (k : Nat := 0) → Term
  | .bvar i, k => .bvar (if i < k then i else i + n)
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app f a, k => .app (liftN n f k) (liftN n a k)
  | .lam A b, k => .lam (liftN n A k) (liftN n b (k + 1))
  | .pi A B, k => .pi (liftN n A k) (liftN n B (k + 1))
  | .eqE a b, k => .eqE (liftN n a k) (liftN n b k)
  | .fst e, k => .fst (liftN n e k)
  | .snd e, k => .snd (liftN n e k)
  | .prf, _ => .prf

/-- Weakening by one. -/
abbrev lift (e : Term) : Term := liftN 1 e

/-- Single substitution: replace the variable at depth `k` by `a`,
decrementing the variables above it. -/
def inst : Term → Term → (k : Nat := 0) → Term
  | .bvar i, a, k =>
    if i < k then .bvar i else if i = k then liftN k a else .bvar (i - 1)
  | .sort u, _, _ => .sort u
  | .const c us, _, _ => .const c us
  | .app f b, a, k => .app (inst f a k) (inst b a k)
  | .lam A b, a, k => .lam (inst A a k) (inst b a (k + 1))
  | .pi A B, a, k => .pi (inst A a k) (inst B a (k + 1))
  | .eqE b c, a, k => .eqE (inst b a k) (inst c a k)
  | .fst e, a, k => .fst (inst e a k)
  | .snd e, a, k => .snd (inst e a k)
  | .prf, _, _ => .prf

@[simp] theorem liftN_bvar (n k i : Nat) :
    liftN n (.bvar i) k = .bvar (if i < k then i else i + n) := rfl
@[simp] theorem liftN_sort (n k : Nat) (u : Nat) :
    liftN n (.sort u) k = .sort u := rfl
@[simp] theorem liftN_const (n k : Nat) (c : BConst) (us : List Nat) :
    liftN n (.const c us) k = .const c us := rfl
@[simp] theorem liftN_app (n k : Nat) (f a : Term) :
    liftN n (.app f a) k = .app (liftN n f k) (liftN n a k) := rfl
@[simp] theorem liftN_lam (n k : Nat) (A b : Term) :
    liftN n (.lam A b) k = .lam (liftN n A k) (liftN n b (k + 1)) := rfl
@[simp] theorem liftN_pi (n k : Nat) (A B : Term) :
    liftN n (.pi A B) k = .pi (liftN n A k) (liftN n B (k + 1)) := rfl
@[simp] theorem liftN_eqE (n k : Nat) (a b : Term) :
    liftN n (.eqE a b) k = .eqE (liftN n a k) (liftN n b k) := rfl
@[simp] theorem liftN_fst (n k : Nat) (e : Term) :
    liftN n (.fst e) k = .fst (liftN n e k) := rfl
@[simp] theorem liftN_snd (n k : Nat) (e : Term) :
    liftN n (.snd e) k = .snd (liftN n e k) := rfl
@[simp] theorem liftN_prf (n k : Nat) : liftN n .prf k = .prf := rfl

@[simp] theorem inst_bvar (a : Term) (k i : Nat) :
    inst (.bvar i) a k =
      (if i < k then .bvar i else if i = k then liftN k a else .bvar (i - 1)) := by
  rfl
@[simp] theorem inst_sort (a : Term) (k : Nat) (u : Nat) :
    inst (.sort u) a k = .sort u := rfl
@[simp] theorem inst_const (a : Term) (k : Nat) (c : BConst) (us : List Nat) :
    inst (.const c us) a k = .const c us := rfl
@[simp] theorem inst_app (a : Term) (k : Nat) (f b : Term) :
    inst (.app f b) a k = .app (inst f a k) (inst b a k) := rfl
@[simp] theorem inst_lam (a : Term) (k : Nat) (A b : Term) :
    inst (.lam A b) a k = .lam (inst A a k) (inst b a (k + 1)) := rfl
@[simp] theorem inst_pi (a : Term) (k : Nat) (A B : Term) :
    inst (.pi A B) a k = .pi (inst A a k) (inst B a (k + 1)) := rfl
@[simp] theorem inst_eqE (a : Term) (k : Nat) (b c : Term) :
    inst (.eqE b c) a k = .eqE (inst b a k) (inst c a k) := rfl
@[simp] theorem inst_fst (a : Term) (k : Nat) (e : Term) :
    inst (.fst e) a k = .fst (inst e a k) := rfl
@[simp] theorem inst_snd (a : Term) (k : Nat) (e : Term) :
    inst (.snd e) a k = .snd (inst e a k) := rfl
@[simp] theorem inst_prf (a : Term) (k : Nat) : inst .prf a k = .prf := rfl

end Term

/-- Non-dependent function space.  (Outside the `Term` namespace so it
can be used without `open Term`, which would collide with
`SetTheory.app`.) -/
def arrow (A B : Term) : Term := .pi A B.lift

end ConLeche.Term
