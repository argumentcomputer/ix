module

public import ConLeche.Model.Annot.Valid

public section

/-!
# `BitAgree`: two readings of the same term (task #161, ENDGAME E)

The basis tier's type readings need a bridge that does not exist yet,
and the ENDGAME D resume-here's item 2 understated it.  Its claim was

> `denoteMeta acval env ψ 0 (basis decl type) = some (BConst.typeAV c us)`

and that equation is **false as stated**, for two independent reasons,
neither of which is a defect:

* `denoteMeta`'s `forallE` clause emits `.pi 0 (pwBit φ m.pw) ta ba` — the
  domain slot is always the literal `0`, because the reading has no
  sort run to take a domain sort from.  `BConst.typeAV` carries the
  *exact* domain sort at every binder, because its consumers
  (`WellDenoted`'s binder clauses, `Skeleton.sound_pi`) read it;
* `denoteMeta`'s codomain slot is a `pwBit`, canonically in `{0, 1}`.
  `BConst.typeAV` carries the tower's result sort, which can be any
  numeral.

Both slots therefore differ as *numerals* while agreeing on everything
that is read.  `interp` dispatches on the codomain slot only through
`v = 0` (`piR`/`lamR` are `if v = 0`), and on the domain slot **not at
all**; `WellDenoted` and `AnnotValid` do the same.  So the right bridge is
not an equation between readings but a congruence:

**`BitAgree e e'` — same tree, same leaves, binder numerals agreeing on
zero-ness, domain numerals unconstrained.**

It carries everything the P tier reads: the interpretation on the nose
(`interp_eq`), and both grading predicates as iffs (`wellDenoted`, `validV`),
hence `WellDenotedV` (`okP`).  With it, a basis type reading is discharged
by *computing* `denoteMeta` and exhibiting a `BitAgree` to `BConst.typeAV`,
after which `bval_mem_type` and `WellDenotedV_bconst_type` apply
unchanged — which is what the resume-here meant.

The relation is deliberately **not** an equivalence-by-erasure: it
demands the two trees be structurally identical, so it cannot silently
identify a `.lam` with a `.pi` or move a leaf.  `erase_eq` records that
it refines erasure-equality, and it is strictly finer.
-/

-- `AnnotTerm.BitAgree` extends `ConLeche.Semantics.AnnotTerm` (dot notation on
-- readings), so this module stays in the semantic tier's namespace.
namespace ConLeche.Semantics
open ConLeche.SetModel ConLeche.Model

open ConLeche.Semantics SetTheory ConLeche.SetModel

universe w

/-- **Two readings of the same term, differing only in binder
numerals' non-zero values.**  Structurally identical trees; at each
binder the codomain numerals agree on zero-ness and the domain numerals
are unconstrained (nothing reads them). -/
inductive AnnotTerm.BitAgree : AnnotTerm → AnnotTerm → Prop where
  | bvar (i : Nat) : BitAgree (.bvar i) (.bvar i)
  | sort (u : Nat) : BitAgree (.sort u) (.sort u)
  | const (c : ConLeche.Term.BConst) (us : List Nat) :
      BitAgree (.const c us) (.const c us)
  | prf : BitAgree .prf .prf
  | app {f f' a a' : AnnotTerm} :
      BitAgree f f' → BitAgree a a' → BitAgree (.app f a) (.app f' a')
  | lam {v v' : Nat} {A A' b b' : AnnotTerm} :
      (v = 0 ↔ v' = 0) → BitAgree A A' → BitAgree b b' →
      BitAgree (.lam v A b) (.lam v' A' b')
  | pi {u u' v v' : Nat} {A A' B B' : AnnotTerm} :
      (v = 0 ↔ v' = 0) → BitAgree A A' → BitAgree B B' →
      BitAgree (.pi u v A B) (.pi u' v' A' B')
  | eqE {a a' b b' : AnnotTerm} :
      BitAgree a a' → BitAgree b b' →
      BitAgree (.eqE a b) (.eqE a' b')
  | fst {e e' : AnnotTerm} :
      BitAgree e e' → BitAgree (.fst e) (.fst e')
  | snd {e e' : AnnotTerm} :
      BitAgree e e' → BitAgree (.snd e) (.snd e')

namespace AnnotTerm.BitAgree

/-- Reflexivity — every reading agrees with itself. -/
theorem refl : ∀ e : AnnotTerm, BitAgree e e
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c us => .const c us
  | .prf => .prf
  | .app f a => .app (refl f) (refl a)
  | .lam _ A b => .lam Iff.rfl (refl A) (refl b)
  | .pi _ _ A B => .pi Iff.rfl (refl A) (refl B)
  | .eqE a b => .eqE (refl a) (refl b)
  | .fst e => .fst (refl e)
  | .snd e => .snd (refl e)

/-- Symmetry. -/
theorem symm : ∀ {e e' : AnnotTerm}, BitAgree e e' → BitAgree e' e := by
  intro e e' h
  induction h with
  | bvar i => exact .bvar i
  | sort u => exact .sort u
  | const c us => exact .const c us
  | prf => exact .prf
  | app _ _ ihf iha => exact .app ihf iha
  | lam hz _ _ ihA ihb => exact .lam hz.symm ihA ihb
  | pi hz _ _ ihA ihB => exact .pi hz.symm ihA ihB
  | eqE _ _ iha ihb => exact .eqE iha ihb
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih

/-- **The relation refines erasure-equality** — and strictly: erasure
also forgets the *structure* of the numerals' binders, while `BitAgree`
demands the trees be identical. -/
theorem erase_eq : ∀ {e e' : AnnotTerm}, BitAgree e e' →
    e.erase = e'.erase := by
  intro e e' h
  induction h with
  | bvar i => rfl
  | sort u => rfl
  | const c us => rfl
  | prf => rfl
  | app _ _ ihf iha => simp [AnnotTerm.erase, ihf, iha]
  | lam _ _ _ ihA ihb => simp [AnnotTerm.erase, ihA, ihb]
  | pi _ _ _ ihA ihB => simp [AnnotTerm.erase, ihA, ihB]
  | eqE _ _ iha ihb => simp [AnnotTerm.erase, iha, ihb]
  | fst _ ih => simp [AnnotTerm.erase, ih]
  | snd _ ih => simp [AnnotTerm.erase, ih]

variable (V : Type w) [SetTheory V]

/-- **The interpretation is invariant** — `interp` reads a codomain
numeral only through `v = 0` (`piR_zero_agree`/`lamR_zero_agree`) and a
domain numeral not at all. -/
theorem interp_eq : ∀ {e e' : AnnotTerm}, BitAgree e e' →
    ∀ ρ : Nat → V, interp V ρ e = interp V ρ e' := by
  intro e e' h
  induction h with
  | bvar i => intro ρ; rfl
  | sort u => intro ρ; rfl
  | const c us => intro ρ; rfl
  | prf => intro ρ; rfl
  | app _ _ ihf iha => intro ρ; simp only [interp_app, ihf, iha]
  | lam hz _ _ ihA ihb =>
    intro ρ
    simp only [interp_lam, ihA ρ]
    exact lamR_zero_agree hz fun x _ => ihb (cons x ρ)
  | pi hz _ _ ihA ihB =>
    intro ρ
    simp only [interp_pi, ihA ρ]
    exact piR_zero_agree hz fun x _ => ihB (cons x ρ)
  | eqE _ _ iha ihb =>
    intro ρ; simp only [interp_eqE, iha, ihb]
  | fst _ ih => intro ρ; simp only [interp_fst, ih]
  | snd _ ih => intro ρ; simp only [interp_snd, ih]

/-- **Truthfulness is invariant.**  The `lam`/`app` clauses' fibre
obligations are `v = 0 → …`, so zero-agreement transfers them; every
other clause is structural. -/
theorem wellDenoted : ∀ {e e' : AnnotTerm}, BitAgree e e' →
    ∀ ρ : Nat → V, (WellDenoted V ρ e ↔ WellDenoted V ρ e') := by
  intro e e' h
  induction h with
  | bvar i => intro ρ; simp
  | sort u => intro ρ; simp
  | const c us => intro ρ; simp
  | prf => intro ρ; simp
  | app hf ha ihf iha =>
    intro ρ
    rw [WellDenoted_app, WellDenoted_app, ihf ρ, iha ρ,
      interp_eq V hf ρ, interp_eq V ha ρ]
  | lam hz hA hb ihA ihb =>
    intro ρ
    rw [WellDenoted_lam, WellDenoted_lam, ihA ρ, interp_eq V hA ρ]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl (ihb (cons x ρ)))
      (exists_congr fun B => and_congr
        (forall_congr' fun x => imp_congr Iff.rfl ?_)
        ⟨fun hh h0 => hh (hz.mpr h0), fun hh h0 => hh (hz.mp h0)⟩))
    rw [interp_eq V hb (cons x ρ)]
  | pi _ hA hB ihA ihB =>
    intro ρ
    rw [WellDenoted_pi, WellDenoted_pi, ihA ρ, interp_eq V hA ρ]
    exact and_congr Iff.rfl
      (forall_congr' fun x => imp_congr Iff.rfl (ihB (cons x ρ)))
  | eqE _ _ iha ihb =>
    intro ρ; rw [WellDenoted_eqE, WellDenoted_eqE, iha ρ, ihb ρ]
  | fst he ih =>
    intro ρ
    rw [WellDenoted_fst, WellDenoted_fst, ih ρ, interp_eq V he ρ]
  | snd he ih =>
    intro ρ
    rw [WellDenoted_snd, WellDenoted_snd, ih ρ, interp_eq V he ρ]

/-- **Bit validity is invariant.**  The one clause that reads a numeral
is `pi`'s `v = 0 → …`, and zero-agreement is exactly what it needs. -/
theorem validV : ∀ {e e' : AnnotTerm}, BitAgree e e' →
    ∀ ρ : Nat → V, (AnnotValid V ρ e ↔ AnnotValid V ρ e') := by
  intro e e' h
  induction h with
  | bvar i => intro ρ; simp
  | sort u => intro ρ; simp
  | const c us => intro ρ; simp
  | prf => intro ρ; simp
  | app _ _ ihf iha =>
    intro ρ; rw [AnnotValid_app, AnnotValid_app, ihf ρ, iha ρ]
  | lam _ hA hb ihA ihb =>
    intro ρ
    rw [AnnotValid_lam, AnnotValid_lam, ihA ρ, interp_eq V hA ρ]
    exact and_congr Iff.rfl
      (forall_congr' fun x => imp_congr Iff.rfl (ihb (cons x ρ)))
  | pi hz hA hB ihA ihB =>
    intro ρ
    rw [AnnotValid_pi, AnnotValid_pi, ihA ρ, interp_eq V hA ρ]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl (ihB (cons x ρ)))
      ⟨fun hh h0 x hx => ?_, fun hh h0 x hx => ?_⟩)
    · rw [← interp_eq V hB (cons x ρ)]; exact hh (hz.mpr h0) x hx
    · rw [interp_eq V hB (cons x ρ)]; exact hh (hz.mp h0) x hx
  | eqE _ _ iha ihb =>
    intro ρ; rw [AnnotValid_eqE, AnnotValid_eqE, iha ρ, ihb ρ]
  | fst _ ih => intro ρ; rw [AnnotValid_fst, AnnotValid_fst, ih ρ]
  | snd _ ih => intro ρ; rw [AnnotValid_snd, AnnotValid_snd, ih ρ]

end AnnotTerm.BitAgree

end ConLeche.Semantics
