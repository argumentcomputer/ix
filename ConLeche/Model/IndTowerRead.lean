module

public import ConLeche.Model.IndPoint
import ConLeche.Model.Annot.BitRename
public section

/-!
# The two opened towers, read (task #161, IND TIER part 5)

The pair part 2's seal named as owed and part 3's survey did not
reach: the reading's `openPisAtFvars_denoteTele` and
`instLamsAt_denoteTele`.  Both are `stripPis_denotePTele`'s move for
move (`IndTeleP.lean`), and both are near-verbatim for the reason that
seal predicted — **the reading is blind to an opener**
(`denoteMeta_erasedEq`'s `fvar` clause compares indices only), so an
`openPisAtFvars`/`instLamsAt` run at any same-index opener spine
produces the same tower.

Two deltas from v1, both bookkeeping:

* the λ tower is a `LamTele` relation rather than an equation against
  a `lamCtx` constructor.  `AnnotTerm`'s `.lam` carries a *bit*, so there
  is no bit-free `lamCtx` to equate against; `LamTele` quantifies the
  bits existentially exactly as `PiTeleAV` does, and the consumers read
  neither;
* `openPisAtFvars_denotePTele` needs no `stripPis` side lemma: v1
  reaches for `openPisAtFvars_stripPis` only to bound an index into
  the tail context, and `PiTeleAV.length` gives that directly.

**Who consumes them.**  `openPisAtFvars_denotePTele` reads the checked
`iota_j` statement's own telescope (the frame `Γs` every stage runs
on) and the constructor's field openers `xFvsP`; `instLamsAt_denotePTele`
reads the rule's λ-tower, which is the truthfulness transport's whole
subject.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name BinderMeta)

universe w

variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-! ## The opened `∀` telescope -/

/-- **The opening walk, read** (`openPisAtFvars_denoteTele`): opening a
telescope whose reading succeeds yields the `.pi` tower's context, the
opened body's reading, and each opener's annotation read *at its own
depth* to its tower entry. -/
theorem openPisAtFvars_denotePTele :
    ∀ (k : Nat) {e : Expr} {j : Nat} {fvs : List Expr} {body : Expr}
      {T : AnnotTerm},
      openPisAtFvars k e j = some (fvs, body) →
      denoteMeta acval env φ j e = some T →
      ∃ (Γ : List AnnotTerm) (R : AnnotTerm),
        PiTeleAV k T Γ R ∧
        denoteMeta acval env φ (j + k) body = some R ∧
        ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
          denoteMeta acval env φ (j + i) (Expr.fvarTypeD x)
            = some (Γ.getD (k - 1 - i) default) := by
  intro k
  induction k with
  | zero =>
    intro e j fvs body T h hT
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], T, .nil, hT, fun i x hx => nomatch hx⟩
  | succ k ih =>
    intro e j fvs body T h hT
    match e, h with
    | .forallE dom bodyE mb, h =>
      simp only [openPisAtFvars] at h
      cases hop : openPisAtFvars k (bodyE.instantiate1 (.fvar j dom))
          (j + 1) with
      | none => rw [hop] at h; exact nomatch h
      | some p =>
        rw [hop] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [denoteMeta_forallE] at hT
        cases hA : denoteMeta acval env φ j dom with
        | none => rw [hA] at hT; exact nomatch hT
        | some A => ?_
        rw [hA] at hT
        cases hB : denoteMeta acval env φ (j + 1)
            (bodyE.instantiate1 (.fvar j dom)) with
        | none => rw [hB] at hT; exact nomatch hT
        | some B => ?_
        rw [hB] at hT
        obtain rfl : T = .pi 0 (pwBit φ mb.pw) A B := by
          simpa using hT.symm
        obtain ⟨Γ', R, htele, hbody, hdoms⟩ := ih hop hB
        have hΓlen : Γ'.length = k := htele.length
        refine ⟨Γ' ++ [A], R, .cons htele, ?_, ?_⟩
        · rw [show j + (k + 1) = j + 1 + k from by omega]
          exact hbody
        · intro i x hx
          cases i with
          | zero =>
            obtain rfl : Expr.fvar j dom = x := by simpa using hx
            show denoteMeta acval env φ (j + 0) dom = _
            rw [show (Γ' ++ [A]).getD (k + 1 - 1 - 0) default = A from by
              simp only [Nat.sub_zero, Nat.add_sub_cancel, List.getD]
              rw [List.getElem?_append_right (by omega), hΓlen,
                Nat.sub_self]
              rfl]
            exact hA
          | succ i =>
            rw [List.getElem?_cons_succ] at hx
            have h1 := hdoms i x hx
            have hik : i < k := by
              rcases Nat.lt_or_ge i k with h' | h'
              · exact h'
              · exfalso
                rw [List.getElem?_eq_none
                  (by rw [openPisAtFvars_length _ hop]; omega)] at hx
                exact nomatch hx
            rw [show (Γ' ++ [A]).getD (k + 1 - 1 - (i + 1)) default
                = Γ'.getD (k - 1 - i) default from by
              simp only [List.getD]
              rw [show k + 1 - 1 - (i + 1) = k - 1 - i from by omega,
                List.getElem?_append_left (by omega)]]
            rw [show j + (i + 1) = j + 1 + i from by omega]
            exact h1

/-! ## The λ telescope -/

/-- **`PiTeleAV`'s λ twin.**  The bit is existential for the same reason
`PiTeleAV`'s two are: a `fun` reads to `.lam (pwBit φ mb.pw)` and no
consumer reads the component. -/
inductive LamTele : Nat → AnnotTerm → List AnnotTerm → AnnotTerm → Prop
  | nil {T : AnnotTerm} : LamTele 0 T [] T
  | cons {k v : Nat} {A B R : AnnotTerm} {Γ : List AnnotTerm} :
      LamTele k B Γ R → LamTele (k + 1) (.lam v A B) (Γ ++ [A]) R

theorem LamTele.length : ∀ {k : Nat} {T : AnnotTerm} {Γ : List AnnotTerm}
    {R : AnnotTerm}, LamTele k T Γ R → Γ.length = k := by
  intro k T Γ R h
  induction h with
  | nil => rfl
  | cons _ ih => simp [ih]

/-- A λ telescope of positive length exposes its head `.lam`. -/
theorem LamTele.succ_inv {k : Nat} {T : AnnotTerm} {Γ : List AnnotTerm}
    {R : AnnotTerm} (h : LamTele (k + 1) T Γ R) :
    ∃ (v : Nat) (A B : AnnotTerm) (Γ' : List AnnotTerm),
      T = .lam v A B ∧ Γ = Γ' ++ [A] ∧ LamTele k B Γ' R := by
  cases h with
  | cons h' => exact ⟨_, _, _, _, rfl, rfl, h'⟩

set_option maxHeartbeats 1600000 in
/-- **The λ-telescope's reading, through an `instLamsAt` run at shaped
openers** (`instLamsAt_denoteTele`): the reading is a `LamTele` tower
whose layers are the run's progressively-instantiated domains, read at
their own depths, and whose core is the residual's reading.  The
reading consults neither an opener's name nor its annotation, so any
same-index opener spine produces the same tower. -/
theorem instLamsAt_denotePTele :
    ∀ (sp : List Expr) {e : Expr} {j : Nat} {ds : List Expr}
      {rest : Expr} {Va : AnnotTerm},
      Expr.instLamsAt sp e = some (ds, rest) →
      (∀ (i : Nat) (x : Expr), sp[i]? = some x →
        ∃ ty, x = Expr.fvar (j + i) ty) →
      denoteMeta acval env φ j e = some Va →
      ∃ (Γ : List AnnotTerm) (C : AnnotTerm),
        LamTele sp.length Va Γ C ∧ Γ.length = sp.length ∧
        denoteMeta acval env φ (j + sp.length) rest = some C ∧
        ∀ (i0 : Nat) (x : Expr), ds[i0]? = some x →
          denoteMeta acval env φ (j + i0) x
            = some (Γ.getD (sp.length - 1 - i0) default) := by
  intro sp
  induction sp with
  | nil =>
    intro e j ds rest Va h _ hV
    simp only [Expr.instLamsAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], Va, .nil, rfl, hV, fun i0 x hx => nomatch hx⟩
  | cons a sp ih =>
    intro e j ds rest Va h hshape hV
    match e, h with
    | .lam dom bodyE mb, h =>
      simp only [Expr.instLamsAt] at h
      cases h1 : Expr.instLamsAt sp (bodyE.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p => ?_
      rw [h1] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [denoteMeta_lam] at hV
      cases hA : denoteMeta acval env φ j dom with
      | none => rw [hA] at hV; exact nomatch hV
      | some A => ?_
      rw [hA] at hV
      cases hB : denoteMeta acval env φ (j + 1)
          (bodyE.instantiate1 (.fvar j dom)) with
      | none => rw [hB] at hV; exact nomatch hV
      | some Bv => ?_
      rw [hB] at hV
      obtain rfl : Va = .lam (pwBit φ mb.pw) A Bv := by simpa using hV.symm
      obtain ⟨tyA, rfl⟩ := hshape 0 a rfl
      -- re-open at the run's opener (the reading is blind to it)
      have hB' : denoteMeta acval env φ (j + 1)
          (bodyE.instantiate1 (.fvar (j + 0) tyA)) = some Bv := by
        rw [denoteMeta_erasedEq (ConLeche.Expr.ErasedEq.instantiate1
          (ConLeche.Expr.ErasedEq.rfl bodyE)
          (show ConLeche.Expr.ErasedEq (.fvar (j + 0) tyA)
            (.fvar j dom) from by constructor)) (j + 1)]
        exact hB
      have hshape' : ∀ (i : Nat) (x : Expr), sp[i]? = some x →
          ∃ ty', x = Expr.fvar (j + 1 + i) ty' := by
        intro i x hx
        obtain ⟨ty', hx'⟩ := hshape (i + 1) x (by simpa using hx)
        exact ⟨ty', by rw [hx']; congr 1; omega⟩
      obtain ⟨Γ', C, htele, hΓlen, hrest, hdoms⟩ := ih h1 hshape' hB'
      refine ⟨Γ' ++ [A], C, .cons htele, ?_, ?_, ?_⟩
      · simp [hΓlen]
      · simp only [List.length_cons]
        rw [show j + (sp.length + 1) = j + 1 + sp.length from by omega]
        exact hrest
      · intro i0 x hx
        simp only [List.length_cons]
        cases i0 with
        | zero =>
          obtain rfl : dom = x := Option.some.inj hx
          rw [Nat.add_zero, hA]
          congr 1
          rw [show sp.length + 1 - 1 - 0 = Γ'.length from by
            rw [hΓlen]; omega]
          rw [List.getD, List.getElem?_append_right (Nat.le_refl _),
            Nat.sub_self]
          rfl
        | succ i =>
          have hx' : p.1[i]? = some x := by simpa using hx
          have hi : i < sp.length := by
            have hh := (List.getElem?_eq_some_iff.mp hx').1
            rw [instLamsAt_length sp h1] at hh
            exact hh
          have h2 := hdoms i x hx'
          rw [show j + (i + 1) = j + 1 + i from by omega, h2]
          congr 1
          rw [show sp.length + 1 - 1 - (i + 1) = sp.length - 1 - i from by
            omega, List.getD, List.getD,
            List.getElem?_append_left (by rw [hΓlen]; omega)]

end ConLeche.Model
