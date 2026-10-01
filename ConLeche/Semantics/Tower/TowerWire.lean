module

public import ConLeche.Semantics.Tower.TowerRec
public import ConLeche.Semantics.DenoteClosed

@[expose] public section

/-!
# The direct-structure leaves' syntactic battery (task #175 wiring, W4)

The wiring checklist's item 1: the `hAclosed` row of an install-step
leaf is `AnnotTerm.liftN 1 (leaf) k = leaf`, and by
`AnnotTerm.liftN_eq_self` (`SetBase/DenoteClosed.lean`) that is exactly
boundedness of the leaf's **erasure** — annotations are inert, only
bvars move.  So this module is a bvar-bound walk per leaf
constructor, plus the peel lemma that produces the binder-data bounds
from the (closed) type reading the wiring strips
(`stripPisAV_below`).

Everything is a structural induction over the leaf formers of
`SetBase/Tower{Leaf,Mk,Rec}.lean`; no semantics, no `V`.

The `hAparams` row needs nothing from here: every leaf is a *plain
function* of its computed numerals and binder data
(`structTyAV`/`structMkAV`/`structRecAV`), so level-parameter
congruence at the install site is congruence of the inputs — the
readings' own `denoteMeta` congruence, discharged where the readings are
made.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term

/-! ## Bound-variable bounds, at the erasure -/

/-- The domains of a λ-frame, each bounded at its own depth
(`(u, dom)` pairs — `mkLamsAV`'s data). -/
def LamDomsBelow (k : Nat) : List (Nat × AnnotTerm) → Prop
  | [] => True
  | d :: ds => Term.bvarsBelow k d.2.erase ∧ LamDomsBelow (k + 1) ds

/-- The binder triples of a Π-frame, each domain bounded at its own
depth (`(u, v, dom)` triples — `mkPisAV`/`mkLamsC`'s data). -/
def DomsBelow (k : Nat) : List (Nat × Nat × AnnotTerm) → Prop
  | [] => True
  | d :: ds => Term.bvarsBelow k d.2.2.erase ∧ DomsBelow (k + 1) ds

/-- A field-domain chain, each domain bounded at its own depth. -/
def FieldsBelow (k : Nat) : List AnnotTerm → Prop
  | [] => True
  | F :: Fs => Term.bvarsBelow k F.erase ∧ FieldsBelow (k + 1) Fs

/-- The domains' closedness, entry by entry. -/
theorem DomsBelow.getD_below {K : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)}, DomsBelow K ds → ∀ k, k < ds.length →
      Term.bvarsBelow (K + k) (ds.getD k default).2.2.erase
  | [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | d :: ds, h, 0, _ => by simpa using h.1
  | d :: ds, h, k + 1, hk => by
    simp only [List.getD_cons_succ]
    have := DomsBelow.getD_below (K := K + 1) (ds := ds) h.2 k (by simpa using hk)
    rwa [show K + 1 + k = K + (k + 1) from by omega] at this

theorem domsBelow_of_getD {K : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)},
      (∀ k, k < ds.length → Term.bvarsBelow (K + k) (ds.getD k default).2.2.erase) → DomsBelow K ds
  | [], _ => trivial
  | d :: ds, h => by
    refine ⟨by simpa using h 0 (by simp), domsBelow_of_getD (K := K + 1) (ds := ds) fun k hk => ?_⟩
    have := h (k + 1) (by simpa using hk)
    simpa [show K + (k + 1) = K + 1 + k from by omega] using this

theorem DomsBelow.map {k : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)}, DomsBelow k ds →
      LamDomsBelow k (ds.map fun d => (d.1, d.2.2))
  | [], _ => trivial
  | _ :: _, h => ⟨h.1, DomsBelow.map h.2⟩

theorem DomsBelow.mapC {m k : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)}, DomsBelow k ds →
      LamDomsBelow k (ds.map fun d => (m, d.2.2))
  | [], _ => trivial
  | _ :: _, h => ⟨h.1, DomsBelow.mapC h.2⟩

theorem DomsBelow.fields {k : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)}, DomsBelow k ds →
      FieldsBelow k (ds.map (·.2.2))
  | [], _ => trivial
  | _ :: _, h => ⟨h.1, DomsBelow.fields h.2⟩

/-! ## The `Term`-side helpers -/

namespace VExprAux

open ConLeche.Term.Term

/-- Lifting raises a bound by exactly the inserted count, at any
cut. -/
theorem bvarsBelow_liftN (n : Nat) :
    ∀ (v : Term) (m k : Nat), Term.bvarsBelow m v →
      Term.bvarsBelow (m + n) (Term.liftN n v k) := by
  intro v
  induction v with
  | bvar i =>
    intro m k h
    show Term.bvarsBelow (m + n) (.bvar (if i < k then i else i + n))
    by_cases hik : i < k
    · rw [if_pos hik]
      exact Nat.lt_of_lt_of_le (show i < m from h) (Nat.le_add_right m n)
    · rw [if_neg hik]
      exact Nat.add_lt_add_right (show i < m from h) n
  | sort u => intro _ _ _; trivial
  | const c us => intro _ _ _; trivial
  | prf => intro _ _ _; trivial
  | app f a ihf iha =>
    intro m k h
    exact ⟨ihf m k h.1, iha m k h.2⟩
  | lam A b ihA ihb =>
    intro m k h
    refine ⟨ihA m k h.1, ?_⟩
    have := ihb (m + 1) (k + 1) h.2
    rw [show m + 1 + n = m + n + 1 by omega] at this
    exact this
  | pi A B ihA ihB =>
    intro m k h
    refine ⟨ihA m k h.1, ?_⟩
    have := ihB (m + 1) (k + 1) h.2
    rw [show m + 1 + n = m + n + 1 by omega] at this
    exact this
  | eqE a b iha ihb =>
    intro m k h
    exact ⟨iha m k h.1, ihb m k h.2⟩
  | fst e ihe =>
    intro m k h
    exact ihe m k h
  | snd e ihe =>
    intro m k h
    exact ihe m k h

/-- Application spines preserve a bound. -/
theorem bvarsBelow_mkAppN :
    ∀ {as : List Term} {f : Term} {k : Nat}, Term.bvarsBelow k f →
      (∀ a ∈ as, Term.bvarsBelow k a) →
      Term.bvarsBelow k (Term.mkAppN f as)
  | [], _, _, hf, _ => hf
  | a :: as, f, k, hf, has => by
    rw [Term.mkAppN_cons]
    exact bvarsBelow_mkAppN ⟨hf, has a (.head _)⟩
      fun a' ha' => has a' (.tail _ ha')

end VExprAux

/-! ## The leaf constructors' bounds -/

/-- The carrier body (graph regime): bounded from the field chain's
own bounds. -/
theorem towerBodyAVPos_below {w : Nat} :
    ∀ {Fs : List AnnotTerm} {k : Nat}, FieldsBelow k Fs →
      Term.bvarsBelow k (towerBodyAVPos w Fs).erase
  | [], _, _ => trivial
  | _ :: _, _, h =>
    ⟨⟨trivial, h.1⟩, h.1, towerBodyAVPos_below h.2⟩

/-- The carrier body (squash regime): bounded from the field chain's
own bounds. -/
theorem sqBodyAV_below :
    ∀ {Fs : List AnnotTerm} {k : Nat}, FieldsBelow k Fs →
      Term.bvarsBelow k (sqBodyAV Fs).erase
  | [], _, _ => trivial
  | _ :: _, _, h =>
    ⟨⟨h.1, sqBodyAV_below h.2, trivial⟩, trivial⟩

/-- The carrier body, both regimes. -/
theorem towerBodyAV_below {w : Nat} {Fs : List AnnotTerm} {k : Nat}
    (h : FieldsBelow k Fs) :
    Term.bvarsBelow k (towerBodyAV w Fs).erase := by
  by_cases hw : w = 0
  · subst hw; rw [towerBodyAV_zero]; exact sqBodyAV_below h
  · rw [towerBodyAV_pos hw]; exact towerBodyAVPos_below h

/-- The uniform projection spelling adds no variables. -/
theorem projAV_below :
    ∀ {i : Nat} {e : AnnotTerm} {k : Nat}, Term.bvarsBelow k e.erase →
      Term.bvarsBelow k (projAV i e).erase
  | 0, _, _, h => h
  | i + 1, e, _, h => projAV_below (i := i) (e := .snd e) h

/-- The recursor body mentions only the minor (`.bvar 1`) and the
major (`.bvar 0`). -/
theorem recBodyAV_below {nF k : Nat} (h2 : 2 ≤ k) :
    Term.bvarsBelow k (recBodyAV nF).erase := by
  rw [recBodyAV, AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN (show 1 < k by omega) ?_
  intro a ha
  obtain ⟨ea, hea, rfl⟩ := List.mem_map.mp ha
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hea
  exact projAV_below (show (0 : Nat) < k by omega)

/-- The tupler (graph regime): bounded at the full field frame. -/
theorem mkTowerGoPos_below {w : Nat} :
    ∀ {Fs : List AnnotTerm} {k : Nat}, FieldsBelow k Fs →
      Term.bvarsBelow (k + Fs.length) (mkTowerGoPos w Fs).erase
  | [], _, _ => trivial
  | F :: Fs, k, h => by
    have hF : Term.bvarsBelow (k + (Fs.length + 1))
        (F.liftN (Fs.length + 1)).erase := by
      rw [AnnotTerm.erase_liftN]
      have := VExprAux.bvarsBelow_liftN (Fs.length + 1) F.erase k 0 h.1
      exact this
    have hbody : Term.bvarsBelow (k + (Fs.length + 1) + 1)
        ((towerBodyAV w Fs).liftN (Fs.length + 1) 1).erase := by
      rw [AnnotTerm.erase_liftN]
      have := VExprAux.bvarsBelow_liftN (Fs.length + 1)
        (towerBodyAV w Fs).erase (k + 1) 1 (towerBodyAV_below h.2)
      rw [show k + 1 + (Fs.length + 1) = k + (Fs.length + 1) + 1
        by omega] at this
      exact this
    have hrec : Term.bvarsBelow (k + (Fs.length + 1))
        (mkTowerGoPos w Fs).erase := by
      have := mkTowerGoPos_below (w := w) (Fs := Fs) (k := k + 1) h.2
      rw [show k + 1 + Fs.length = k + (Fs.length + 1) by omega] at this
      exact this
    exact ⟨⟨⟨⟨trivial, hF⟩, hF, hbody⟩,
      show Fs.length < k + (Fs.length + 1) by omega⟩, hrec⟩

/-- The tupler, both regimes. -/
theorem mkTowerGo_below {w : Nat} {Fs : List AnnotTerm} {k : Nat}
    (h : FieldsBelow k Fs) :
    Term.bvarsBelow (k + Fs.length) (mkTowerGo w Fs).erase := by
  by_cases hw : w = 0
  · subst hw; rw [mkTowerGo_zero]; trivial
  · rw [mkTowerGo_pos hw]; exact mkTowerGoPos_below h

/-- The λ-tower former: bounded from the frame's own bounds and the
body's at the full depth. -/
theorem mkLamsAV_below :
    ∀ {ds : List (Nat × AnnotTerm)} {b : AnnotTerm} {k : Nat},
      LamDomsBelow k ds →
      Term.bvarsBelow (k + ds.length) b.erase →
      Term.bvarsBelow k (mkLamsAV ds b).erase
  | [], _, _, _, hb => hb
  | d :: ds, b, k, h, hb =>
    ⟨h.1, mkLamsAV_below h.2 (by
      rw [show k + 1 + ds.length = k + (ds.length + 1) by omega]
      exact hb)⟩

/-- The constant-bit tower, over Π-frame data. -/
theorem mkLamsC_below {m : Nat} {ds : List (Nat × Nat × AnnotTerm)}
    {b : AnnotTerm} {k : Nat} (h : DomsBelow k ds)
    (hb : Term.bvarsBelow (k + ds.length) b.erase) :
    Term.bvarsBelow k (mkLamsC m ds b).erase :=
  mkLamsAV_below h.mapC (by
    rw [List.length_map]; exact hb)

/-! ## The peel: bounds off a bounded reading -/

/-- A successful `stripPisAV` of a bounded reading bounds every binder
domain at its own depth and the residual at the full depth. -/
theorem stripPisAV_below :
    ∀ {n : Nat} {e : AnnotTerm} {ps : List (Nat × Nat × AnnotTerm)}
      {b : AnnotTerm} {k : Nat},
      stripPisAV n e = some (ps, b) →
      Term.bvarsBelow k e.erase →
      DomsBelow k ps ∧ Term.bvarsBelow (k + n) b.erase
  | 0, e, ps, b, k, h, he => by
    obtain ⟨rfl, rfl⟩ : ps = [] ∧ b = e := by
      simpa [stripPisAV] using h.symm
    exact ⟨trivial, he⟩
  | n + 1, .pi u v A B, ps, b, k, h, he => by
    simp only [stripPisAV, Option.map_eq_some_iff] at h
    obtain ⟨⟨ps', b'⟩, hstrip, heq⟩ := h
    obtain ⟨rfl, rfl⟩ : (u, v, A) :: ps' = ps ∧ b' = b := by
      simpa using heq
    obtain ⟨hds, hb⟩ := stripPisAV_below hstrip he.2
    exact ⟨⟨he.1, hds⟩, by
      rw [show k + (n + 1) = k + 1 + n by omega]
      exact hb⟩

/-! ## The three leaves -/

/-- **The recursor leaf is bounded**: the body reads only the minor
and the major, which sit inside any frame of length ≥ 2. -/
theorem structRecAV_below {ℓ : Nat} {ds : List (Nat × Nat × AnnotTerm)}
    {nF : Nat} {k : Nat} (hd : DomsBelow k ds)
    (h2 : 2 ≤ ds.length) :
    Term.bvarsBelow k (structRecAV ℓ ds nF).erase :=
  mkLamsC_below hd (recBodyAV_below (by omega))

/-! ## The `hAclosed` packages

The install rows want `AnnotTerm.liftN 1 (leaf) k = leaf` for every cut
`k`; a leaf bounded at `0` is bounded at every cut
(`Term.bvarsBelow.mono`), and a lift below the bound is the identity
(`AnnotTerm.liftN_eq_self`). -/

/-- A closed leaf is `liftN`-invariant at every cut. -/
theorem liftN_eq_self_of_closed {e : AnnotTerm}
    (h : Term.bvarsBelow 0 e.erase) (k n : Nat) :
    AnnotTerm.liftN n e k = e :=
  AnnotTerm.liftN_eq_self e (Term.bvarsBelow.mono (Nat.zero_le k) h) n

end ConLeche.Semantics
