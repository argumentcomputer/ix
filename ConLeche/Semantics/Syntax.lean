module

public import ConLeche.Term.Subst

@[expose] public section

/-!
# `AnnotTerm`: the sort-annotated variant of `Term` (task #151, tier A)

`Term` (`ConLeche/Term/Syntax.lean`) carries **no** universe information at
its binders: `pi A B` and `lam A b` are the bare formers.  Without a
sort at the binder an interpretation cannot tell a predicate space
with its one proof point from a dependent function space — the
universe-cohabitation wall: no *typing* separates a proposition's
inhabitant from the proof point.

`AnnotTerm` is the same syntax with the binder formers carrying **ground
numeral sorts**:

| `Term` | `AnnotTerm` | annotation |
|---|---|---|
| `pi A B` | `pi u v A B` | the domain's sort `u` and the body's sort `v` |
| `lam A b` | `lam u A b` | the sort `u` of the body's **type** (the codomain), which `interp` dispatches on |
| everything else | the same node | none |

**Design rulings this file implements** (task #151's own):

* **Ground numerals, not `Level`s.**  `Term` already evaluates every
  level expression at its use site (`ConLeche/Term/Syntax.lean`'s "universe
  levels are concrete `Nat`s"), so an annotation is a `Nat`.  There is
  no level substitution to commute with, which is what makes the whole
  substitution metatheory below *inert*.
* **Annotations are cached premises.**  A slot exists exactly where the
  checker's own inference establishes the fact and a consumer reads
  it: the rules tier's `Infer.forallE` carries the sort premises of
  both binder positions and `Infer.lam` the codomain's
  (`ConLeche/Rules/Rel.lean`).  Hence:
* **There is no `letE` former at all** (task #241) — the slot question
  is moot: no stored expression carries a `let`, so the denotation's
  `letE` clause is `none` and the node never reaches this syntax.  See
  `ConLeche/Term/Syntax.lean` and `ConLeche/Verify/Denote.lean`.
* **`eqE` gets no annotation**, and since task #237 carries no type
  slot either — exactly as `Term` does; see
  `ConLeche/Term/Syntax.lean` on why the type was never constrained.

## The structural kit

`erase` forgets the annotations; `liftN`/`inst` are the de Bruijn
operations, defined *clause for clause* against
`ConLeche/Term/Subst.lean`'s.  Their whole content is the pair of
commutations `erase_liftN` / `erase_inst`: **annotations are inert data
under substitution** — instantiation rewrites subterms and never
touches a numeral — so the annotated operations project onto the plain
ones on the nose.  That is what lets tier B and tier C move an
annotated term through a β/ζ/telescope step without re-deriving any
sort fact.
-/

namespace ConLeche.Semantics

open ConLeche.Term

/-- `Term` with ground numeral sorts at the binder formers.  Node for
node the same syntax; see the module docstring for the annotation
table. -/
inductive AnnotTerm where
  /-- de Bruijn index -/
  | bvar (i : Nat)
  /-- `Sort u` at a concrete level -/
  | sort (u : Nat)
  /-- a built-in constant at a concrete level instantiation -/
  | const (c : BConst) (us : List Nat)
  /-- application -/
  | app (f a : AnnotTerm)
  /-- `fun (_ : ty) => body`, where `body`'s **type** has sort `u` —
  the codomain numeral `interp` dispatches on (tier B's F4; the
  #152 resolution made it derivable, and `Annotates.lam` caches it) -/
  | lam (u : Nat) (ty body : AnnotTerm)
  /-- `(_ : ty) → body`, with `ty`'s sort `u` and `body`'s sort `v` -/
  | pi (u v : Nat) (ty body : AnnotTerm)
  /-- `@Eq _ lhs rhs`; no annotation, and no type slot either, as in
  `Term` (task #237) -/
  | eqE (lhs rhs : AnnotTerm)
  /-- first field of a pair -/
  | fst (e : AnnotTerm)
  /-- second field of a pair -/
  | snd (e : AnnotTerm)
  /-- the canonical (irrelevant) proof of a derivable equation -/
  | prf
  deriving Repr, Inhabited

namespace AnnotTerm

/-- Forget the annotations. -/
def erase : AnnotTerm → Term
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c us => .const c us
  | .app f a => .app (erase f) (erase a)
  | .lam _ A b => .lam (erase A) (erase b)
  | .pi _ _ A B => .pi (erase A) (erase B)
  | .eqE a b => .eqE (erase a) (erase b)
  | .fst e => .fst (erase e)
  | .snd e => .snd (erase e)
  | .prf => .prf

@[simp] theorem erase_bvar (i : Nat) : erase (.bvar i) = .bvar i := rfl
@[simp] theorem erase_sort (u : Nat) : erase (.sort u) = .sort u := rfl
@[simp] theorem erase_const (c : BConst) (us : List Nat) :
    erase (.const c us) = .const c us := rfl
@[simp] theorem erase_app (f a : AnnotTerm) :
    erase (.app f a) = .app (erase f) (erase a) := rfl
@[simp] theorem erase_lam (u : Nat) (A b : AnnotTerm) :
    erase (.lam u A b) = .lam (erase A) (erase b) := rfl
@[simp] theorem erase_pi (u v : Nat) (A B : AnnotTerm) :
    erase (.pi u v A B) = .pi (erase A) (erase B) := rfl
@[simp] theorem erase_eqE (a b : AnnotTerm) :
    erase (.eqE a b) = .eqE (erase a) (erase b) := rfl
@[simp] theorem erase_fst (e : AnnotTerm) :
    erase (.fst e) = .fst (erase e) := rfl
@[simp] theorem erase_snd (e : AnnotTerm) :
    erase (.snd e) = .snd (erase e) := rfl
@[simp] theorem erase_prf : erase .prf = .prf := rfl

/-- Weakening: insert `n` fresh binders at depth `k`.  Clause for
clause `Term.liftN`; the numerals ride along untouched. -/
def liftN (n : Nat) : AnnotTerm → (k : Nat := 0) → AnnotTerm
  | .bvar i, k => .bvar (if i < k then i else i + n)
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app f a, k => .app (liftN n f k) (liftN n a k)
  | .lam u A b, k => .lam u (liftN n A k) (liftN n b (k + 1))
  | .pi u v A B, k => .pi u v (liftN n A k) (liftN n B (k + 1))
  | .eqE a b, k => .eqE (liftN n a k) (liftN n b k)
  | .fst e, k => .fst (liftN n e k)
  | .snd e, k => .snd (liftN n e k)
  | .prf, _ => .prf

/-- Weakening by one. -/
abbrev lift (e : AnnotTerm) : AnnotTerm := liftN 1 e

/-- Single substitution at depth `k`.  Clause for clause
`Term.inst`. -/
def inst : AnnotTerm → AnnotTerm → (k : Nat := 0) → AnnotTerm
  | .bvar i, a, k =>
    if i < k then .bvar i else if i = k then liftN k a else .bvar (i - 1)
  | .sort u, _, _ => .sort u
  | .const c us, _, _ => .const c us
  | .app f b, a, k => .app (inst f a k) (inst b a k)
  | .lam u A b, a, k => .lam u (inst A a k) (inst b a (k + 1))
  | .pi u v A B, a, k => .pi u v (inst A a k) (inst B a (k + 1))
  | .eqE b c, a, k => .eqE (inst b a k) (inst c a k)
  | .fst e, a, k => .fst (inst e a k)
  | .snd e, a, k => .snd (inst e a k)
  | .prf, _, _ => .prf

/-- Iterated application (`Term.mkAppN`'s transpose). -/
def mkAppN (f : AnnotTerm) : List AnnotTerm → AnnotTerm
  | [] => f
  | a :: as => mkAppN (.app f a) as

@[simp] theorem mkAppN_nil (f : AnnotTerm) : mkAppN f [] = f := rfl
@[simp] theorem mkAppN_cons (f a : AnnotTerm) (as : List AnnotTerm) :
    mkAppN f (a :: as) = mkAppN (.app f a) as := rfl

/-- `Term.projPair?`'s transpose: decode the checker's projection index
for the pinned pair (task #225).  The bound `i < 2` that the single
`proj i e` former carried as a side condition is this function's
`none` branch. -/
def projPair? : Nat → AnnotTerm → Option AnnotTerm
  | 0, e => some (.fst e)
  | 1, e => some (.snd e)
  | _ + 2, _ => none

/-- The decoder is defined exactly at the two field indices, so a
decoded projection still witnesses the old side condition. -/
theorem lt_of_projPair? {i : Nat} {e x : AnnotTerm} (h : projPair? i e = some x) :
    i < 2 := by
  rcases i with _ | _ | i
  · omega
  · omega
  · exact nomatch h

/-- …and conversely: below the bound the decoder always fires, on any
subject.  Definedness depends on the index alone. -/
theorem projPair?_exists_of_lt {i : Nat} (h : i < 2) (e : AnnotTerm) :
    ∃ x, projPair? i e = some x := by
  rcases i with _ | _ | i
  · exact ⟨.fst e, rfl⟩
  · exact ⟨.snd e, rfl⟩
  · omega

/-- A decoded projection is one of the two formers on the same
subject — the case split consumers of the decoder want. -/
theorem projPair?_cases {i : Nat} {e x : AnnotTerm} (h : projPair? i e = some x) :
    x = .fst e ∨ x = .snd e := by
  rcases i with _ | _ | i
  · exact Or.inl (Option.some.inj h).symm
  · exact Or.inr (Option.some.inj h).symm
  · exact nomatch h

/-- The same split for two decodings **at one index**: a congruence
site sees the same former on both sides. -/
theorem projPair?_cases₂ {i : Nat} {e x e' x' : AnnotTerm}
    (h : projPair? i e = some x) (h' : projPair? i e' = some x') :
    (x = .fst e ∧ x' = .fst e') ∨ (x = .snd e ∧ x' = .snd e') := by
  rcases i with _ | _ | i
  · exact Or.inl ⟨(Option.some.inj h).symm, (Option.some.inj h').symm⟩
  · exact Or.inr ⟨(Option.some.inj h).symm, (Option.some.inj h').symm⟩
  · exact nomatch h

/-! ### Clause equations for the substitution operations -/

@[simp] theorem liftN_bvar (n k i : Nat) :
    liftN n (.bvar i) k = .bvar (if i < k then i else i + n) := rfl
@[simp] theorem liftN_sort (n k u : Nat) : liftN n (.sort u) k = .sort u := rfl
@[simp] theorem liftN_const (n k : Nat) (c : BConst) (us : List Nat) :
    liftN n (.const c us) k = .const c us := rfl
@[simp] theorem liftN_app (n k : Nat) (f a : AnnotTerm) :
    liftN n (.app f a) k = .app (liftN n f k) (liftN n a k) := rfl
@[simp] theorem liftN_lam (n k u : Nat) (A b : AnnotTerm) :
    liftN n (.lam u A b) k = .lam u (liftN n A k) (liftN n b (k + 1)) := rfl
@[simp] theorem liftN_pi (n k u v : Nat) (A B : AnnotTerm) :
    liftN n (.pi u v A B) k = .pi u v (liftN n A k) (liftN n B (k + 1)) := rfl
@[simp] theorem liftN_eqE (n k : Nat) (a b : AnnotTerm) :
    liftN n (.eqE a b) k = .eqE (liftN n a k) (liftN n b k) := rfl
@[simp] theorem liftN_fst (n k : Nat) (e : AnnotTerm) :
    liftN n (.fst e) k = .fst (liftN n e k) := rfl
@[simp] theorem liftN_snd (n k : Nat) (e : AnnotTerm) :
    liftN n (.snd e) k = .snd (liftN n e k) := rfl
@[simp] theorem liftN_prf (n k : Nat) : liftN n .prf k = .prf := rfl

@[simp] theorem inst_bvar (a : AnnotTerm) (k i : Nat) :
    inst (.bvar i) a k =
      (if i < k then .bvar i else if i = k then liftN k a else .bvar (i - 1)) := by
  rfl
@[simp] theorem inst_sort (a : AnnotTerm) (k u : Nat) :
    inst (.sort u) a k = .sort u := rfl
@[simp] theorem inst_const (a : AnnotTerm) (k : Nat) (c : BConst) (us : List Nat) :
    inst (.const c us) a k = .const c us := rfl
@[simp] theorem inst_app (a : AnnotTerm) (k : Nat) (f b : AnnotTerm) :
    inst (.app f b) a k = .app (inst f a k) (inst b a k) := rfl
@[simp] theorem inst_lam (a : AnnotTerm) (k u : Nat) (A b : AnnotTerm) :
    inst (.lam u A b) a k = .lam u (inst A a k) (inst b a (k + 1)) := rfl
@[simp] theorem inst_pi (a : AnnotTerm) (k u v : Nat) (A B : AnnotTerm) :
    inst (.pi u v A B) a k = .pi u v (inst A a k) (inst B a (k + 1)) := rfl
@[simp] theorem inst_eqE (a : AnnotTerm) (k : Nat) (b c : AnnotTerm) :
    inst (.eqE b c) a k = .eqE (inst b a k) (inst c a k) := rfl
@[simp] theorem inst_fst (a : AnnotTerm) (k : Nat) (e : AnnotTerm) :
    inst (.fst e) a k = .fst (inst e a k) := rfl
@[simp] theorem inst_snd (a : AnnotTerm) (k : Nat) (e : AnnotTerm) :
    inst (.snd e) a k = .snd (inst e a k) := rfl
@[simp] theorem inst_prf (a : AnnotTerm) (k : Nat) : inst .prf a k = .prf := rfl

/-! ### The erase-commutations

**Annotations are inert data under substitution.**  Both operations
project onto `Term`'s on the nose: nothing in `liftN`/`inst` reads or
writes a numeral slot, so `erase` is a homomorphism for them.  These
two equations are the whole point of the structural kit — tier B and
tier C move annotated terms through β, ζ and telescope steps by
rewriting with them, never by re-deriving a sort fact. -/

/-- `erase` commutes with lifting. -/
@[simp] theorem erase_liftN : ∀ (e : AnnotTerm) (n k : Nat),
    erase (liftN n e k) = Term.liftN n (erase e) k := by
  intro e
  induction e with
  | bvar i => intros; rfl
  | sort u => intros; rfl
  | const c us => intros; rfl
  | app f a ihf iha => intro n k; simp only [liftN_app, erase_app, ihf, iha,
      Term.liftN_app]
  | lam u A b ihA ihb => intro n k; simp only [liftN_lam, erase_lam, ihA, ihb,
      Term.liftN_lam]
  | pi u v A B ihA ihB => intro n k; simp only [liftN_pi, erase_pi, ihA, ihB,
      Term.liftN_pi]
  | eqE a b iha ihb => intro n k; simp only [liftN_eqE, erase_eqE,
      iha, ihb, Term.liftN_eqE]
  | fst e ih => intro n k; simp only [liftN_fst, erase_fst, ih,
      Term.liftN_fst]
  | snd e ih => intro n k; simp only [liftN_snd, erase_snd, ih,
      Term.liftN_snd]
  | prf => intros; rfl

/-- `erase` commutes with instantiation. -/
@[simp] theorem erase_inst : ∀ (e a : AnnotTerm) (k : Nat),
    erase (inst e a k) = Term.inst (erase e) (erase a) k := by
  intro e
  induction e with
  | bvar i =>
    intro a k
    simp only [inst_bvar, Term.inst_bvar, erase_bvar]
    split
    · rfl
    · split
      · exact erase_liftN a k 0
      · rfl
  | sort u => intros; rfl
  | const c us => intros; rfl
  | app f b ihf ihb => intro a k; simp only [inst_app, erase_app, ihf, ihb,
      Term.inst_app]
  | lam u A b ihA ihb => intro a k; simp only [inst_lam, erase_lam, ihA, ihb,
      Term.inst_lam]
  | pi u v A B ihA ihB => intro a k; simp only [inst_pi, erase_pi, ihA, ihB,
      Term.inst_pi]
  | eqE b c ihb ihc => intro a k; simp only [inst_eqE, erase_eqE,
      ihb, ihc, Term.inst_eqE]
  | fst e ih => intro a k; simp only [inst_fst, erase_fst, ih,
      Term.inst_fst]
  | snd e ih => intro a k; simp only [inst_snd, erase_snd, ih,
      Term.inst_snd]
  | prf => intros; rfl

/-- `erase` commutes with application spines. -/
theorem erase_mkAppN : ∀ (as : List AnnotTerm) (f : AnnotTerm),
    erase (mkAppN f as) = Term.mkAppN (erase f) (as.map erase) := by
  intro as
  induction as with
  | nil => intro f; rfl
  | cons a as ih => intro f; simpa using ih (.app f a)

end AnnotTerm


/-! ## `erase` at the constant clause -/

open ConLeche.Term (BConst)

/-- **`erase` is injective at the constant clause.**  Every other
`AnnotTerm` constructor erases to a different `Term` constructor, so a
constant erasure has a constant source — with the *same* name and the
*same* level numerals, since the constant clause carries no
annotation to forget. -/
theorem erase_eq_const {ea : AnnotTerm} {c : BConst} {us : List Nat}
    (h : ea.erase = .const c us) : ea = .const c us := by
  cases ea with
  | bvar i => rw [AnnotTerm.erase_bvar] at h; exact nomatch h
  | sort u => rw [AnnotTerm.erase_sort] at h; exact nomatch h
  | const c' us' =>
    rw [AnnotTerm.erase_const] at h
    injection h with h1 h2
    rw [h1, h2]
  | app f a => rw [AnnotTerm.erase_app] at h; exact nomatch h
  | lam u ty b => rw [AnnotTerm.erase_lam] at h; exact nomatch h
  | pi u v ty b => rw [AnnotTerm.erase_pi] at h; exact nomatch h
  | eqE l r => rw [AnnotTerm.erase_eqE] at h; exact nomatch h
  | fst e => rw [AnnotTerm.erase_fst] at h; exact nomatch h
  | snd e => rw [AnnotTerm.erase_snd] at h; exact nomatch h
  | prf => rw [AnnotTerm.erase_prf] at h; exact nomatch h


end ConLeche.Semantics
