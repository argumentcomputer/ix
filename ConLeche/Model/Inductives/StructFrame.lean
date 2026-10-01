module

public import ConLeche.Model.Inductives.StructRead
public import ConLeche.Model.IndTowerRead
import ConLeche.Model.IndFrame
import ConLeche.Model.IndDomGrade
import ConLeche.Verify.Leaves
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Denote.IndFrame
public section

/-!
# The direct structure's opened frames (task #175 W4c, P3 module 3)

The direct install's stage checks run **at opened frames**: each
binder-domain comparison (`checkStructDomsAt`), each field's sort
inference (`checkStructFieldSorts`) and the recursor's pins run at the
depth of the binder they concern, over the variables `openPisAtFvars`
created for the earlier binders.  The claims interface
(`Model/Claims.lean`) answers such a run at a context `Δa` that
correlates with the run's subject (`CtxOk`) and is satisfied by the
valuations the conclusion is drawn at (`Sat`).  This module builds
those contexts from a type's reading:

* the **telescope grading** (`piTeleAV_graded`): the reading's own
  grading descends the `.pi` tower — each domain is graded at every
  valuation satisfying the earlier domains, in `Sat`-of-`drop` form;
* the **opened context** (`ctxOk_opened`): any well-scoped term over
  the opening's variables correlates with the reading's context at its
  depth;
* the **context transfer** (`CtxOk.transfer`, `Sat2_of_entries_eq`):
  two contexts whose entries interpret alike under the earlier entries
  are interchangeable — how the type former's and the constructor's
  parameter frames, opened at their own variables and pinned
  definitionally binder by binder, are identified.

The tower leaves' premises (`ParamsOkT`, `MkPre`, `RecPre`) walk the
same frames in `cons` form; `Sat_cons`/`Sat_cons_inv` are the
bridge, one binder at a time.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche ConLeche.Semantics ConLeche.Verify SetTheory ConLeche.SetModel
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-! ## `Sat` bookkeeping -/

omit [SetTheory V] in
theorem cons_eta (ρ : Nat → V) : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
  funext i
  cases i <;> rfl

theorem Sat_cons_inv {Δ : List AnnotTerm} {A : AnnotTerm} {ρ : Nat → V}
    (h : Sat V (A :: Δ) ρ) :
    ρ 0 ∈ˢ interp V (fun j => ρ (j + 1)) A ∧
      Sat V Δ (fun j => ρ (j + 1)) :=
  ⟨by have := h 0 A rfl; simpa using this, Sat_tail h⟩

/-- Dropping entries shifts the valuation. -/
theorem Sat_drop {Δ : List AnnotTerm} {ρ : Nat → V} (h : Sat V Δ ρ)
    (m : Nat) : Sat V (Δ.drop m) (fun j => ρ (j + m)) := by
  intro i Aa hi
  rw [List.getElem?_drop] at hi
  have h1 := h (m + i) Aa hi
  show ρ (i + m) ∈ˢ interp V (fun j => ρ (j + i + 1 + m)) Aa
  have e : (fun j => ρ (j + i + 1 + m)) = fun j => ρ (j + (m + i) + 1) := by
    funext j; congr 1; omega
  rw [e, Nat.add_comm i m]
  exact h1

/-- **Context transfer**: a correspondence survives replacing the
context by one with the same satisfying valuations whose entries
interpret alike under them. -/
theorem CtxOk.transfer {env : Env} {m : EnvModel V env} {φ : Name → Nat}
    {d : Nat} {Δ₁ Δ₂ : List AnnotTerm} {b : Expr}
    (h : CtxOk m φ d Δ₁ b) (hlen : Δ₂.length = d)
    (hsat : ∀ ρ : Nat → V, Sat V Δ₂ ρ → Sat V Δ₁ ρ)
    (hent : ∀ (p : Nat) (A₁ A₂ : AnnotTerm), Δ₁[p]? = some A₁ →
      Δ₂[p]? = some A₂ → ∀ ρ : Nat → V, Sat V Δ₂ ρ →
        interp V (fun j => ρ (j + p + 1)) A₁
          = interp V (fun j => ρ (j + p + 1)) A₂) :
    CtxOk m φ d Δ₂ b := by
  obtain ⟨hlen₁, hleaf⟩ := h
  refine ⟨hlen, ?_⟩
  intro l hl
  obtain ⟨hlt, hfb, tya, A₁, hty, hA₁, heq, hok⟩ := hleaf l hl
  have hpl : d - 1 - l.1 < Δ₂.length := by omega
  obtain ⟨A₂, hA₂⟩ : ∃ A₂, Δ₂[d - 1 - l.1]? = some A₂ :=
    ⟨Δ₂[d - 1 - l.1]'hpl, List.getElem?_eq_getElem hpl⟩
  refine ⟨hlt, hfb, tya, A₂, hty, hA₂, ?_, fun ρ hρ => hok ρ (hsat ρ hρ)⟩
  intro ρ hρ
  rw [heq ρ (hsat ρ hρ), hent _ A₁ A₂ hA₁ hA₂ ρ hρ]

/-! ## The telescope grading -/

/-- **The reading's grading descends its `.pi` tower**: domain `i`
(outermost first) is graded at every valuation satisfying the earlier
domains, and the core at every valuation satisfying them all. -/
theorem piTeleAV_graded :
    ∀ {k : Nat} {T : AnnotTerm} {Γ : List AnnotTerm} {R : AnnotTerm},
      PiTeleAV k T Γ R →
      ∀ {Δ₀ : List AnnotTerm},
        (∀ ρ : Nat → V, Sat V Δ₀ ρ → WellDenotedV V ρ T) →
        (∀ i, i < k → ∀ ρ : Nat → V, Sat V (Γ.drop (k - i) ++ Δ₀) ρ →
          WellDenotedV V ρ (Γ.getD (k - 1 - i) default)) ∧
        (∀ ρ : Nat → V, Sat V (Γ ++ Δ₀) ρ → WellDenotedV V ρ R) := by
  intro k T Γ R h
  induction h with
  | nil =>
    intro Δ₀ hT
    exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun ρ hρ => hT ρ hρ⟩
  | @cons k u v A B R Γ' h ih =>
    intro Δ₀ hT
    have hlen : Γ'.length = k := h.length
    have hB : ∀ ρ : Nat → V, Sat V (A :: Δ₀) ρ → WellDenotedV V ρ B := by
      intro ρ hρ
      obtain ⟨h0, htl⟩ := Sat_cons_inv hρ
      have := WellDenotedV_pi_body (hT _ htl) h0
      rwa [cons_eta] at this
    obtain ⟨ih1, ih2⟩ := ih hB
    refine ⟨?_, ?_⟩
    · intro i hi ρ hρ
      cases i with
      | zero =>
        rw [Nat.sub_zero, show k + 1 = (Γ' ++ [A]).length from by
          simp [hlen], List.drop_length, List.nil_append] at hρ
        rw [show (Γ' ++ [A]).getD (k + 1 - 1 - 0) default = A from by
          simp only [Nat.sub_zero, Nat.add_sub_cancel, List.getD]
          rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]
          rfl]
        exact WellDenotedV_pi_dom (hT ρ hρ)
      | succ i =>
        rw [show k + 1 - (i + 1) = k - i from by omega,
          List.drop_append_of_le_length (by omega), List.append_assoc,
          List.singleton_append] at hρ
        rw [show (Γ' ++ [A]).getD (k + 1 - 1 - (i + 1)) default
            = Γ'.getD (k - 1 - i) default from by
          simp only [List.getD]
          rw [show k + 1 - 1 - (i + 1) = k - 1 - i from by omega,
            List.getElem?_append_left (by omega)]]
        exact ih1 i (by omega) ρ hρ
    · intro ρ hρ
      rw [List.append_assoc, List.singleton_append] at hρ
      exact ih2 ρ hρ

/-! ## The opened context -/

/-- **`CtxOk` at an opening's frame**: a term well-scoped at depth
`i ≤ k` over the opening's variables correlates with the reading's
context at that depth (`Γ.drop (k - i)` — the earlier domains,
innermost first). -/
theorem ctxOk_opened {env : Env} {m : EnvModel V env} {φ : Name → Nat}
    {k : Nat} {e : Expr} {fvs : List Expr} {o : Expr}
    (hop : openPisAtFvars k e 0 = some (fvs, o)) (hcl : e.hasFvar = false)
    {Γ : List AnnotTerm} (hΓ : Γ.length = k)
    (hdoms : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denoteMeta m.acval env φ i (Expr.fvarTypeD x)
        = some (Γ.getD (k - 1 - i) default))
    (hokΓ : ∀ i, i < k → ∀ ρ : Nat → V, Sat V (Γ.drop (k - i)) ρ →
      WellDenotedV V ρ (Γ.getD (k - 1 - i) default))
    {i : Nat} (hik : i ≤ k) {x : Expr} (hwx : Expr.WScoped i x)
    (hleaf : ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs) :
    CtxOk m φ i (Γ.drop (k - i)) x := by
  have hidx := openPisAtFvars_index k e 0 hop
  have hlenF : fvs.length = k := openPisAtFvars_length k hop
  have hws := (openPisAtFvars_WScoped k e 0 hop
    (Expr.WScoped.of_not_hasFvar hcl)).1
  -- the positions of the variables a leaf can be
  have hpos : ∀ l ∈ x.fvarLeaves, fvs[l.1]? = some (Expr.fvar l.1 l.2) := by
    intro l hl
    obtain ⟨p, hp⟩ := List.getElem?_of_mem (hleaf l hl)
    obtain ⟨ty, hx⟩ := hidx p _ hp
    rw [Nat.zero_add] at hx
    obtain ⟨rfl, -⟩ : l.1 = p ∧ l.2 = ty := by
      injection hx with a b
      exact ⟨a, b⟩
    exact hp
  refine ctxOk_of_openers m.acval_closed (fvs := fvs.take i)
    (Aa := fun j => Γ.getD (k - 1 - j) default) (Δa := Γ.drop (k - i))
    (by rw [List.length_drop]; omega) ?_ ?_ ?_ (e := x) (n := i) ?_
    (Expr.fvarLeaves_lt_of_wscoped hwx) ?_ ?_
  · intro j y hy
    have hj : j < i := by
      have := (List.getElem?_eq_some_iff.mp hy).1
      rw [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt hj] at hy
    obtain ⟨ty, hx⟩ := hidx j y hy
    exact ⟨ty, by rw [hx, Nat.zero_add]⟩
  · intro y hy
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hy
    have hji : j < i := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      rw [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt hji] at hj
    obtain ⟨ty, rfl⟩ := hidx j y hj
    have hw := hws _ (List.mem_of_getElem? hj)
    rw [Nat.zero_add] at hw ⊢
    simp only [Expr.WScoped, Nat.zero_add] at hw ⊢
    exact ⟨hji, hw.2⟩
  · intro j y hy
    have hj : j < i := by
      have := (List.getElem?_eq_some_iff.mp hy).1
      rw [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt hj] at hy
    exact hdoms j y hy
  · intro l hl
    have hlt := Expr.fvarLeaves_lt_of_wscoped hwx l hl
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hlt]; exact hpos l hl)
  · intro j hj
    rw [List.getElem?_drop, show k - i + (i - 1 - j) = k - 1 - j from by omega]
    have hjl : k - 1 - j < Γ.length := by omega
    rw [List.getD, List.getElem?_eq_getElem hjl]
    rfl
  · intro j hj ρ hρ
    have hd := Sat_drop hρ (i - j)
    rw [List.drop_drop, show k - i + (i - j) = k - j from by omega] at hd
    have e : (fun l => ρ (l + (i - 1 - j) + 1)) = fun l => ρ (l + (i - j)) := by
      funext l; congr 1; omega
    rw [e]
    exact hokΓ j (by omega) _ hd

end ConLeche.Model
