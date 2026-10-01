module

public import ConLeche.Model.Annot.Bit
public section

/-!
# `AnnotValid` — bit validity, on the bit (task #161, P3.2)

The regime numerals of a `denoteMeta` image are *claims* — the input's
own validated annotations, read at a ground valuation.  `interp`
dispatches on them (`piR`/`lamR`), so the soundness ladder needs, at
exactly one place per binder former, that the claimed bit is
semantically right.  `AnnotValid` is that predicate, and nothing
else:

* **the `pi` clause carries the bit component** — `v = 0 → the
  codomain fibres are truth values` — the fact `WellDenoted` does *not*
  carry at `pi` (its app clause carries the kind package, its λ clause
  the fibre package, but a bare product's regime has no home there);
* **the λ clause carries nothing** — the λ-side regime facts live in
  `WellDenoted`'s λ clause already (`∃ B, fibres + (v = 0 → truth
  values)`), and the chain rule's semantic content is the model's own
  impredicativity (`piR_zero_mem_univZero`): an inner λ's ∀-type at
  bit `0` is a truth value *because it is a `piR 0`*, no run needed;
* every other clause is hereditary plumbing, clause-for-clause the
  `WellDenoted` environment discipline (so the substitution metatheory
  rides the identical rewrites).

**Establishment is from run inversions, never a validity
metatheorem.**  `ValidInfer` — "every inferred type has a sort" — is
*refuted* at the application clause (`Annot/Validity.lean`, the
`DefEq`-crossing wall), so `AnnotValid` is never established by
recursion on derivations.  It is established at the checker's own
visit sites, where the P2 validation conjunct
(`zeronessOf v = m.pw`, `inferTypeCore_forallE_inv`) meets the
run lemma's semantic sort fact; `pwBit_zero_mem_univZero` below is
that establishment step, isolated.  Preservation is the substitution
pair (`AnnotValid_liftN`/`AnnotValid_inst`) + the level-crossing
laws (`denotePInstLevels` upstream of any `interp` fact).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Name Level PropWhen)

universe w

variable (V : Type w) [SetTheory V]

/-- Bit validity of the binder annotations under a variable
environment (see the module docstring): the one new fact is the `pi`
clause's `v = 0` component; everything else is the hereditary
environment discipline of `WellDenoted`. -/
@[expose] def AnnotValid : (Nat → V) → AnnotTerm → Prop
  | ρ, .pi _u v A B =>
    AnnotValid ρ A ∧
    (∀ x, x ∈ˢ interp V ρ A → AnnotValid (cons x ρ) B) ∧
    (v = 0 → ∀ x, x ∈ˢ interp V ρ A →
      interp V (cons x ρ) B ∈ˢ (univZero : V))
  | ρ, .lam _v A b =>
    AnnotValid ρ A ∧
    ∀ x, x ∈ˢ interp V ρ A → AnnotValid (cons x ρ) b
  | ρ, .app f a => AnnotValid ρ f ∧ AnnotValid ρ a
  | ρ, .eqE a b => AnnotValid ρ a ∧ AnnotValid ρ b
  | ρ, .fst e => AnnotValid ρ e
  | ρ, .snd e => AnnotValid ρ e
  | _, .bvar _ => True
  | _, .sort _ => True
  | _, .const _ _ => True
  | _, .prf => True

/-! ### Clause equations -/

@[simp] theorem AnnotValid_bvar (ρ : Nat → V) (i : Nat) :
    AnnotValid V ρ (.bvar i) = True := by rw [AnnotValid]
@[simp] theorem AnnotValid_sort (ρ : Nat → V) (u : Nat) :
    AnnotValid V ρ (.sort u) = True := by rw [AnnotValid]
@[simp] theorem AnnotValid_const (ρ : Nat → V) (c : ConLeche.Term.BConst)
    (us : List Nat) : AnnotValid V ρ (.const c us) = True := by
  rw [AnnotValid]
@[simp] theorem AnnotValid_prf (ρ : Nat → V) :
    AnnotValid V ρ .prf = True := by rw [AnnotValid]
theorem AnnotValid_pi (ρ : Nat → V) (u v : Nat) (A B : AnnotTerm) :
    AnnotValid V ρ (.pi u v A B) =
      (AnnotValid V ρ A ∧
        (∀ x, x ∈ˢ interp V ρ A → AnnotValid V (cons x ρ) B) ∧
        (v = 0 → ∀ x, x ∈ˢ interp V ρ A →
          interp V (cons x ρ) B ∈ˢ (univZero : V))) := by
  rw [AnnotValid]
theorem AnnotValid_lam (ρ : Nat → V) (v : Nat) (A b : AnnotTerm) :
    AnnotValid V ρ (.lam v A b) =
      (AnnotValid V ρ A ∧
        ∀ x, x ∈ˢ interp V ρ A → AnnotValid V (cons x ρ) b) := by
  rw [AnnotValid]
theorem AnnotValid_app (ρ : Nat → V) (f a : AnnotTerm) :
    AnnotValid V ρ (.app f a) =
      (AnnotValid V ρ f ∧ AnnotValid V ρ a) := by rw [AnnotValid]
theorem AnnotValid_eqE (ρ : Nat → V) (a b : AnnotTerm) :
    AnnotValid V ρ (.eqE a b) =
      (AnnotValid V ρ a ∧ AnnotValid V ρ b) := by rw [AnnotValid]
theorem AnnotValid_fst (ρ : Nat → V) (e : AnnotTerm) :
    AnnotValid V ρ (.fst e) = AnnotValid V ρ e := by
  rw [AnnotValid]
theorem AnnotValid_snd (ρ : Nat → V) (e : AnnotTerm) :
    AnnotValid V ρ (.snd e) = AnnotValid V ρ e := by
  rw [AnnotValid]

/-! ## The establishment step, isolated

The `pi` component at a checker-visited node: the P2 run inversion
supplies `zeronessOf v = pw` (the site passed), the run lemma
supplies the codomain's semantic sort membership, and the bit laws
turn the claimed bit into the sort's true zero — impredicativity is
not consulted, the sort fact is enough. -/

variable {V}

/-- A validated zero bit puts the sort's inhabitants in `univZero`:
the pointwise establishment step for `AnnotValid`'s `pi` component
(and for `WellDenoted`'s λ-clause `v = 0` component at the leaf case). -/
theorem pwBit_zero_mem_univZero {v : Level} {pw : PropWhen}
    {φ : Name → Nat}
    (hz : Level.zeronessOf v = pw)
    (hb : pwBit φ pw = 0) {x : V}
    (hx : x ∈ˢ (univ (Level.eval φ v) : V)) :
    x ∈ˢ (univZero : V) := by
  have h0 : Level.eval φ v = 0 := by
    subst hz
    exact (pwBit_zeronessOf φ v).mp hb
  rw [h0, univ_zero] at hx
  exact hx

/-! ## Preservation: the substitution pair

Clause for clause `WellDenoted_liftN`/`WellDenoted_inst` — the `pi` bit
component mentions only `interp` of the clause's own subterms, so it
rides `interp_liftN`/`cons_shiftE` exactly as the λ clause's fibre
package does there. -/

variable (V)

/-- Bit validity through lifting. -/
theorem AnnotValid_liftN (n : Nat) :
    ∀ (e : AnnotTerm) (k : Nat) (ρ : Nat → V),
      AnnotValid V ρ (e.liftN n k) ↔ AnnotValid V (shiftE n k ρ) e := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ
    simp only [AnnotTerm.liftN_bvar]
    split <;> simp
  | sort u => intro k ρ; simp
  | const c us => intro k ρ; simp
  | app f a ihf iha =>
    intro k ρ
    rw [AnnotTerm.liftN_app, AnnotValid_app, AnnotValid_app, ihf, iha]
  | lam v A b ihA ihb =>
    intro k ρ
    rw [AnnotTerm.liftN_lam, AnnotValid_lam, AnnotValid_lam, ihA,
      interp_liftN]
    refine and_congr Iff.rfl
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
    rw [ihb, cons_shiftE]
  | pi u v A B ihA ihB =>
    intro k ρ
    rw [AnnotTerm.liftN_pi, AnnotValid_pi, AnnotValid_pi, ihA,
      interp_liftN]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (imp_congr Iff.rfl (forall_congr' fun x =>
        imp_congr Iff.rfl ?_)))
    · rw [ihB, cons_shiftE]
    · rw [interp_liftN, cons_shiftE]
  | eqE a b iha ihb =>
    intro k ρ
    rw [AnnotTerm.liftN_eqE, AnnotValid_eqE, AnnotValid_eqE, iha, ihb]
  | fst e ihe =>
    intro k ρ
    rw [AnnotTerm.liftN_fst, AnnotValid_fst, AnnotValid_fst, ihe]
  | snd e ihe =>
    intro k ρ
    rw [AnnotTerm.liftN_snd, AnnotValid_snd, AnnotValid_snd, ihe]
  | prf => intro k ρ; simp

/-! ### Instantiation — and the one premise that had to change

`WellDenoted_inst` takes `WellDenoted V (shiftE k 0 ρ) a`, and the P3 brief
proposed the same premise here.  **It does not work, for a structural
reason worth recording.**  The `bvar` clause at `i = k` reduces the
goal to `AnnotValid V ρ (a.liftN k)`, which `AnnotValid_liftN`
turns into `AnnotValid V (shiftE k 0 ρ) a` — *bit validity of the
substituted term itself*.  `WellDenoted` does not imply it (the two
predicates are independent: `WellDenoted`'s `pi` clause carries no bit
component at all, which is exactly why `AnnotValid` exists).

So the premise below is the **matching** one, `AnnotValid` of `a`,
not the conjunction: no other clause reads anything about `a` beyond
what its own induction hypothesis supplies, so asking for `WellDenotedV`
would over-charge the lemma.  The conjunction form is available as
`WellDenotedV_inst0` (`Interp/WellDenotedTransport.lean`), where it is assembled
from this lemma and `WellDenoted_inst` — each half paying only its own
premise. -/

/-- Bit validity through instantiation. -/
theorem AnnotValid_inst :
    ∀ (e a : AnnotTerm) (k : Nat) (ρ : Nat → V),
      AnnotValid V (shiftE k 0 ρ) a →
      (AnnotValid V ρ (e.inst a k) ↔
        AnnotValid V (instE k (interp V (shiftE k 0 ρ) a) ρ) e) := by
  intro e
  induction e with
  | bvar i =>
    intro a k ρ ha
    show AnnotValid V ρ
        (if i < k then .bvar i
         else if i = k then AnnotTerm.liftN k a else .bvar (i - 1)) ↔ _
    by_cases h : i < k
    · simp [if_pos h]
    · by_cases h2 : i = k
      · simp only [if_neg h, if_pos h2, AnnotValid_bvar, iff_true]
        exact (AnnotValid_liftN V k a 0 ρ).mpr ha
      · simp [if_neg h, if_neg h2]
  | sort u => intro a k ρ _; simp [AnnotTerm.inst]
  | const c us => intro a k ρ _; simp [AnnotTerm.inst]
  | app f b ihf ihb =>
    intro a k ρ ha
    rw [AnnotTerm.inst_app, AnnotValid_app, AnnotValid_app, ihf a k ρ ha,
      ihb a k ρ ha]
  | lam v A b ihA ihb =>
    intro a k ρ ha
    rw [AnnotTerm.inst_lam, AnnotValid_lam, AnnotValid_lam, ihA a k ρ ha,
      interp_inst]
    refine and_congr Iff.rfl (forall_congr' fun x => imp_congr Iff.rfl ?_)
    have ha' : AnnotValid V (shiftE (k + 1) 0 (cons x ρ)) a := by
      rw [shiftE_succ_cons]; exact ha
    rw [ihb a (k + 1) (cons x ρ) ha', shiftE_succ_cons, cons_instE]
  | pi u v A B ihA ihB =>
    intro a k ρ ha
    rw [AnnotTerm.inst_pi, AnnotValid_pi, AnnotValid_pi, ihA a k ρ ha,
      interp_inst]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (imp_congr Iff.rfl (forall_congr' fun x =>
        imp_congr Iff.rfl ?_)))
    · have ha' : AnnotValid V (shiftE (k + 1) 0 (cons x ρ)) a := by
        rw [shiftE_succ_cons]; exact ha
      rw [ihB a (k + 1) (cons x ρ) ha', shiftE_succ_cons, cons_instE]
    · rw [interp_inst, shiftE_succ_cons, cons_instE]
  | eqE x y ihx ihy =>
    intro a k ρ ha
    rw [AnnotTerm.inst_eqE, AnnotValid_eqE, AnnotValid_eqE, ihx a k ρ ha,
      ihy a k ρ ha]
  | fst e ihe =>
    intro a k ρ ha
    rw [AnnotTerm.inst_fst, AnnotValid_fst, AnnotValid_fst, ihe a k ρ ha]
  | snd e ihe =>
    intro a k ρ ha
    rw [AnnotTerm.inst_snd, AnnotValid_snd, AnnotValid_snd, ihe a k ρ ha]
  | prf => intro a k ρ _; simp [AnnotTerm.inst]

/-- Substitution at the outermost binder — the β/ζ transport form,
`WellDenoted_inst0`'s mirror. -/
theorem AnnotValid_inst0 {e a : AnnotTerm} {ρ : Nat → V}
    (ha : AnnotValid V ρ a) :
    AnnotValid V ρ (e.inst a) ↔
      AnnotValid V (cons (interp V ρ a) ρ) e := by
  have h := AnnotValid_inst V e a 0 ρ (by rwa [shiftE_zero_zero])
  rwa [shiftE_zero_zero, instE_zero] at h

end ConLeche.Model
