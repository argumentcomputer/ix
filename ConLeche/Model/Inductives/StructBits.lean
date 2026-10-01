module

public import ConLeche.Model.Annot.BitLemmas
import ConLeche.Semantics.Tower.TowerLeaf
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.InstLevels
public import ConLeche.Verify.BinderLoop
import ConLeche.Verify.Mono
import ConLeche.Verify.Subst
import ConLeche.Kernel.Inductives.StructParts
public section

/-!
# The direct structure's annotated Π-bits are exact (task #175 W4c, P3 module 1)

The tower leaves' folds need the annotated Π-types' codomain bits
*exactly*: the type former's parameter binders carry a nonzero bit
(their codomains end in `Sort w`, of sort `succ w`), the constructor's
and recursor's binders carry a bit that is zero exactly when the
result sort (resp. the elimination sort) evaluates to zero.  Validity
(`AnnotValid`) is one-directional — a zero bit at an empty-domain
codomain is valid — so the content is *syntactic*: in verified mode
`inferTypeCore`'s `.forallE` clause validates `zeronessOf v ==
mb.pw` against the opened body's inferred sort `v`
(`inferTypeCore_forall_inv`), and `checkConstantVal` runs that
inference on the annotated type.  This module walks the Π-prefix
(`piBits_of_infer`), pins the innermost sort per block constant, and
reads the bits off the `denoteMeta` reading (`stripPisAV_bits`) — the
three walks (`checkConstantVal`, `openPisAtFvars`, `denoteMeta`) open
the binders with the same `fvar`s, so one predicate over the opening
(`PiBitsOpen`) serves all three.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  BinderMeta inferTypeCore ensureSortCore whnf openPisAtFvars)

variable {mode : CheckMode}

/-! ## Leaf clauses of the inference, inverted -/

theorem whnf_sort_eq {env : Env} {F d : Nat} {u : Level} {e' : Expr}
    (h : whnf mode env F d (.sort u) = .ok e') : e' = .sort u := by
  have h1 := ConLeche.whnf_mono (Nat.le_add_right F 2) h
  rw [ConLeche.whnf_sort] at h1
  exact (Except.ok.inj h1).symm

theorem ensureSortCore_sort_eq {env : Env} {F d : Nat} {u v : Level}
    (h : ensureSortCore mode env F d (.sort u) = .ok v) : v = u :=
  Expr.sort.inj (whnf_sort_eq (ConLeche.ensureSortCore_inv h))

theorem inferTypeCore_sort_inv {env : Env} {F d : Nat} {u : Level} {t : Expr}
    (h : inferTypeCore mode env F d (.sort u) = .ok t) :
    t = .sort (.succ u) := by
  match F, h with
  | 0, h => rw [ConLeche.inferTypeCore_zero] at h; exact nomatch h
  | F + 1, h =>
    rw [ConLeche.inferTypeCore_succ] at h
    simp only [ConLeche.inferBody, pure, Except.pure] at h
    exact (Except.ok.inj h).symm

/-- A run on an application spine carries a run on its head. -/
theorem inferTypeCore_mkAppN_fn_inv {env : Env} {F d : Nat} :
    ∀ (as : List Expr) {f t : Expr},
      inferTypeCore mode env F d (Expr.mkAppN f as) = .ok t →
      ∃ tf, inferTypeCore mode env F d f = .ok tf
  | [], _, t, h => ⟨t, h⟩
  | a :: as, f, t, h => by
    obtain ⟨tfa, hfa⟩ := inferTypeCore_mkAppN_fn_inv as (f := .app f a) h
    obtain ⟨tf, _, _, _, hf, -⟩ := ConLeche.inferTypeCore_app_inv' hfa
    exact ⟨tf, hf⟩

/-- **A spine into a sort**: applying a head whose type is a
Π-telescope of the spine's length ending in `Sort s` types at
`Sort s` — the sort carries no bound variables, so the per-argument
instantiations leave it alone. -/
theorem inferTypeCore_mkAppN_sort {env : Env} {F d : Nat} :
    ∀ (as : List Expr) {f ty : Expr} {bs : List (Expr × BinderMeta)}
      {s : Level} {t : Expr},
      inferTypeCore mode env F d f = .ok ty →
      ty.stripPis as.length = some (bs, .sort s) →
      inferTypeCore mode env F d (Expr.mkAppN f as) = .ok t →
      t = .sort s
  | [], f, ty, bs, s, t, hf, hst, h => by
    obtain rfl : ty = t := Except.ok.inj (hf.symm.trans h)
    simp only [List.length_nil, Expr.stripPis, Option.some.injEq,
      Prod.mk.injEq] at hst
    exact hst.2
  | a :: as, f, ty, bs, s, t, hf, hst, h => by
    obtain ⟨dom, body, mb, rfl⟩ :
        ∃ dom body mb, ty = .forallE dom body mb := by
      cases ty <;> first
        | exact ⟨_, _, _, rfl⟩
        | simp [Expr.stripPis] at hst
    obtain ⟨tfa, hfa⟩ := inferTypeCore_mkAppN_fn_inv as (f := .app f a) h
    obtain ⟨tf, ty', body', m', hf', hw, rfl, -⟩ :=
      ConLeche.inferTypeCore_app_inv' hfa
    obtain rfl : tf = .forallE dom body mb :=
      Except.ok.inj (hf'.symm.trans hf)
    obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (ConLeche.whnf_forallE_eq hw)
    simp only [List.length_cons, Expr.stripPis, Option.map_eq_some_iff] at hst
    obtain ⟨⟨bs', body₀⟩, hst', heq⟩ := hst
    simp only [Prod.mk.injEq] at heq
    obtain ⟨-, rfl⟩ := heq
    have hsome := Expr.stripPis_instantiate1_isSome (v := a) as.length
      (e := body') 0 (by rw [hst']; rfl)
    obtain ⟨⟨bs'', body''⟩, hst''⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨hb, -⟩ := Expr.stripPis_instantiate1_eq (v := a) as.length 0
      hst' hst''
    rw [Expr.instantiate1_sort] at hb
    subst hb
    exact inferTypeCore_mkAppN_sort as hfa hst'' h

/-! ## The opening walk -/

/-- The first `n` binders of `e`, opened from depth `d` with the
inference's own `fvar`s, each codomain bit zero exactly when `z`. -/
def PiBitsOpen (φ : Name → Nat) (z : Prop) : Nat → Nat → Expr → Prop
  | 0, _, _ => True
  | n + 1, d, .forallE dom body mb =>
    (pwBit φ mb.pw = 0 ↔ z) ∧
      PiBitsOpen φ z n (d + 1) (body.instantiate1 (.fvar d dom))
  | _ + 1, _, _ => False

theorem eval_imax_eq_zero_iff (φ : Name → Nat) (l r : Level) :
    Level.eval φ (.imax l r) = 0 ↔ Level.eval φ r = 0 := by
  simp only [Level.eval]
  split
  · next h => exact ⟨fun _ => h, fun _ => rfl⟩
  · next h => exact ⟨fun h' => absurd (Nat.max_eq_zero_iff.mp h').2 h, fun h' => absurd h' h⟩

/-- **The Π-prefix walk**: in verified mode, the first `n` binders'
bits of an inferred type are exact against the innermost opened
body's inferred sort, and the whole type's sort is zero exactly when
that one is (`imax`'s zero-ness is its right argument's). -/
theorem piBits_of_infer {env : Env} (hver : mode.verifiedChecks = true) :
    ∀ (n : Nat) {F d : Nat} {e t : Expr} {v₀ : Level} {fvs : List Expr}
      {opened : Expr},
      openPisAtFvars n e d = some (fvs, opened) →
      inferTypeCore mode env F d e = .ok t →
      ensureSortCore mode env F d t = .ok v₀ →
      ∃ (F' : Nat) (tb : Expr) (vb : Level),
        inferTypeCore mode env F' (d + n) opened = .ok tb ∧
        ensureSortCore mode env F' (d + n) tb = .ok vb ∧
        (∀ φ, Level.eval φ v₀ = 0 ↔ Level.eval φ vb = 0) ∧
        ∀ φ, PiBitsOpen φ (Level.eval φ vb = 0) n d e
  | 0, F, d, e, t, v₀, fvs, opened, hop, h, hens => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨-, rfl⟩ := hop
    exact ⟨F, t, v₀, h, hens, fun _ => Iff.rfl, fun _ => trivial⟩
  | n + 1, F, d, e, t, v₀, fvs, opened, hop, h, hens => by
    match e, hop, h with
    | .forallE dom body mb, hop, h =>
      match F, h with
      | 0, h => rw [ConLeche.inferTypeCore_zero] at h; exact nomatch h
      | F + 1, h =>
        obtain ⟨tty, u, bt, v, -, -, hbt, hensb, hz, rfl⟩ :=
          ConLeche.inferTypeCore_forall_inv h
        simp only [openPisAtFvars] at hop
        split at hop
        · next fvs' e' hop' =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hop
          obtain ⟨-, rfl⟩ := hop
          obtain ⟨F', tb, vb, hrun, hensb', hv, hbits⟩ :=
            piBits_of_infer hver n hop' hbt hensb
          refine ⟨F', tb, vb, ?_, ?_, ?_, ?_⟩
          · rw [show d + (n + 1) = d + 1 + n from by omega]; exact hrun
          · rw [show d + (n + 1) = d + 1 + n from by omega]; exact hensb'
          · intro φ
            rw [ensureSortCore_sort_eq hens, eval_imax_eq_zero_iff]
            exact hv φ
          · intro φ
            refine ⟨?_, hbits φ⟩
            rw [← hz hver]
            exact (pwBit_zeronessOf φ _).trans (hv φ)
        · exact nomatch hop
    | .bvar _, hop, _ | .fvar _ _, hop, _ | .sort _, hop, _
    | .const _ _, hop, _ | .app _ _, hop, _ | .lam _ _ _, hop, _
    | .letE _ _ _, hop, _ | .lit _, hop, _ | .proj _ _ _, hop, _ =>
      simp [openPisAtFvars] at hop

/-! ## The bits, read -/

/-- The reading's Π-peel carries the syntactic bits: `denoteMeta` opens
with the same `fvar`s. -/
theorem stripPisAV_bits {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {z : Prop} :
    ∀ (n : Nat) {d : Nat} {e : Expr} {ea : AnnotTerm}
      {pps : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm},
      PiBitsOpen φ z n d e → denoteMeta acval env φ d e = some ea →
      stripPisAV n ea = some (pps, b) →
      ∀ p ∈ pps, (p.2.1 = 0 ↔ z)
  | 0, d, e, ea, pps, b, _, _, hst => by
    simp only [stripPisAV, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, -⟩ := hst
    intro p hp
    exact absurd hp (by simp)
  | n + 1, d, e, ea, pps, b, hbits, hden, hst => by
    match e, hbits with
    | .forallE dom body mb, ⟨hhead, htail⟩ =>
      obtain ⟨ta, ba, -, hba, rfl⟩ := denoteMeta_forallE_inv hden
      simp only [stripPisAV, Option.map_eq_some_iff] at hst
      obtain ⟨⟨pps', b'⟩, hst', heq⟩ := hst
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hhead
      · exact stripPisAV_bits n htail hba hst' p hp
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      exact h.elim

/-! ## `openPisAtFvars` bookkeeping -/

theorem openPisAtFvars_length :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr},
      openPisAtFvars n e d = some (fvs, o) → fvs.length = n
  | 0, e, d, fvs, o, h => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | n + 1, e, d, fvs, o, h => by
    match e, h with
    | .forallE dom body mb, h =>
      simp only [openPisAtFvars] at h
      split at h
      · next fvs' e' h' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1, List.length_cons, openPisAtFvars_length n h']
      · exact nomatch h
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [openPisAtFvars] at h

/-- Two consecutive openings are one. -/
theorem openPisAtFvars_add :
    ∀ (n : Nat) {m : Nat} {e : Expr} {d : Nat} {fvs fvs' : List Expr}
      {o o' : Expr},
      openPisAtFvars n e d = some (fvs, o) →
      openPisAtFvars m o (d + n) = some (fvs', o') →
      openPisAtFvars (n + m) e d = some (fvs ++ fvs', o')
  | 0, m, e, d, fvs, fvs', o, o', h, h' => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using h'
  | n + 1, m, e, d, fvs, fvs', o, o', h, h' => by
    match e, h with
    | .forallE dom body mb, h =>
      simp only [openPisAtFvars] at h
      split at h
      · next fvs₁ e₁ h₁ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have h'' := openPisAtFvars_add n h₁
          (by rw [show d + 1 + n = d + (n + 1) from by omega]; exact h')
        rw [show n + 1 + m = n + m + 1 from by omega]
        simp only [openPisAtFvars]
        rw [h'']
        rfl
      · exact nomatch h
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [openPisAtFvars] at h

/-- Opening a telescope whose stripped body is a sort reaches that
sort (sorts carry no bound variables). -/
theorem openPisAtFvars_of_stripPis_sort :
    ∀ (n : Nat) {e : Expr} (d : Nat) {bs : List (Expr × BinderMeta)}
      {s : Level},
      e.stripPis n = some (bs, .sort s) →
      ∃ fvs, openPisAtFvars n e d = some (fvs, .sort s)
  | 0, e, d, bs, s, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨[], by rw [h.2]; rfl⟩
  | n + 1, e, d, bs, s, h => by
    match e, h with
    | .forallE dom body mb, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body₀⟩, hst', heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      have hsome := Expr.stripPis_instantiate1_isSome
        (v := .fvar d dom) n (e := body) 0 (by rw [hst']; rfl)
      obtain ⟨⟨bs'', body''⟩, hst''⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨hb, -⟩ := Expr.stripPis_instantiate1_eq
        (v := .fvar d dom) n 0 hst' hst''
      rw [Expr.instantiate1_sort] at hb
      subst hb
      obtain ⟨fvs, hop⟩ := openPisAtFvars_of_stripPis_sort n (d + 1) hst''
      refine ⟨Expr.fvar d dom :: fvs, ?_⟩
      show (match openPisAtFvars n (body.instantiate1 (.fvar d dom)) (d + 1)
          with
        | some (fvs, e) => some (Expr.fvar d dom :: fvs, e)
        | none => none) = _
      rw [hop]
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.stripPis] at h

end ConLeche.Model
