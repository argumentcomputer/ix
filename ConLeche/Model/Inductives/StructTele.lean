module

public import ConLeche.Model.Inductives.StructRows
import ConLeche.Semantics.Tower.TowerRec
public section

/-!
# The direct structure's telescope walks (task #175 W4c, P3 module 3, part 3)

The tower leaves' hereditary premises (`ParamsOkT`, `MkPre`, `RecPre`,
`FieldsOkB`) walk a binder list in `cons` form; the opened-type record
(`Opened`) hands out gradings in `Sat`-of-`drop` form.  This module
bridges the two:

* `PiTeleAV.unique`/`piTeleAV_of_stripPisAV`: the `.pi` context of a
  reading is its `stripPisAV` peel reversed — the leaves are spelled
  over the peel, the frames over the context;
* `hereditaryWalk`: any predicate that descends one binder at a time
  (graded domain, then the tail under every member) holds along the
  peel from the reading's gradings and its base case at the full
  context;
* `fieldsOkB_of_frame`: the field chain's `FieldsOkB` from the
  gradings and the per-field bounds;
* `sat_of_spineFit`: a fitting spine satisfies the entries it fits.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche ConLeche.Semantics ConLeche.Verify SetTheory ConLeche.SetModel
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The peel and the context -/

theorem PiTeleAV.unique :
    ∀ {k : Nat} {T : AnnotTerm} {Γ Γ' : List AnnotTerm} {R R' : AnnotTerm},
      PiTeleAV k T Γ R → PiTeleAV k T Γ' R' → Γ = Γ' ∧ R = R' := by
  intro k T Γ Γ' R R' h
  induction h generalizing Γ' R' with
  | nil => intro h'; cases h'; exact ⟨rfl, rfl⟩
  | @cons k u v A B R Γ₁ h ih =>
    intro h'
    obtain ⟨u', v', A', B', Γ₂, hT, hΓ, h₂⟩ := h'.succ_inv
    obtain ⟨rfl, rfl, rfl, rfl⟩ : u = u' ∧ v = v' ∧ A = A' ∧ B = B' := by
      injection hT with a b c d
      exact ⟨a, b, c, d⟩
    obtain ⟨rfl, rfl⟩ := ih h₂
    exact ⟨hΓ.symm, rfl⟩

/-- A successful peel is a `.pi` context: the peel's domains reversed. -/
theorem piTeleAV_of_stripPisAV :
    ∀ {k : Nat} {T : AnnotTerm} {pps : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm},
      stripPisAV k T = some (pps, b) →
      PiTeleAV k T (pps.map (·.2.2)).reverse b
  | 0, T, pps, b, h => by
    simp only [stripPisAV, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .nil
  | k + 1, .pi u v A B, pps, b, h => by
    simp only [stripPisAV, Option.map_eq_some_iff] at h
    obtain ⟨⟨pps', b'⟩, hst, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have := piTeleAV_of_stripPisAV hst
    simpa [List.reverse_cons] using PiTeleAV.cons (A := A) (u := u) (v := v) this
  | k + 1, .bvar _, _, _, h | k + 1, .sort _, _, _, h | k + 1, .const _ _, _, _, h
  | k + 1, .app _ _, _, _, h | k + 1, .lam _ _ _, _, _, h
  | k + 1, .eqE _ _, _, _, h
  | k + 1, .fst _, _, _, h | k + 1, .snd _, _, _, h
  | k + 1, .prf, _, _, h => by
    simp [stripPisAV] at h

/-- The peel's entries, read off the reversed context. -/
theorem getD_reverse_of_peel {pps : List (Nat × Nat × AnnotTerm)} {k : Nat}
    (hlen : pps.length = k) {i : Nat} (hi : i < k) {p : Nat × Nat × AnnotTerm}
    (hp : pps[i]? = some p) :
    ((pps.map (·.2.2)).reverse).getD (k - 1 - i) default = p.2.2 := by
  rw [List.getD, List.getElem?_reverse (by simp; omega)]
  simp only [List.length_map, hlen]
  rw [show k - 1 - (k - 1 - i) = i from by omega, List.getElem?_map, hp]
  rfl

/-! ## The hereditary walk -/

/-- **The hereditary walk**: a binder-descending predicate holds along
a peel whose entries are graded under the earlier ones, from its base
case at the full context. -/
theorem hereditaryWalk {Q : (Nat → V) → List (Nat × Nat × AnnotTerm) → Prop}
    {n : Nat} {Γ : List AnnotTerm} {pps : List (Nat × Nat × AnnotTerm)}
    (hΓ : Γ.length = n) (hlen : pps.length = n)
    (hent : ∀ i, i < n → ∃ p, pps[i]? = some p ∧
      p.2.2 = Γ.getD (n - 1 - i) default)
    (okΓ : ∀ i, i < n → ∀ ρ : Nat → V, Sat V (Γ.drop (n - i)) ρ →
      WellDenotedV V ρ (Γ.getD (n - 1 - i) default))
    (hnil : ∀ ρ : Nat → V, Sat V Γ ρ → Q ρ [])
    (hcons : ∀ (ρ : Nat → V) (d : Nat × Nat × AnnotTerm)
      (ds : List (Nat × Nat × AnnotTerm)), d ∈ pps →
      WellDenotedV V ρ d.2.2 →
      (∀ a, a ∈ˢ interp V ρ d.2.2 → Q (cons a ρ) ds) → Q ρ (d :: ds)) :
    ∀ (i : Nat), i ≤ n → ∀ ρ : Nat → V, Sat V (Γ.drop (n - i)) ρ →
      Q ρ (pps.drop i) := by
  -- descend on the remaining length
  suffices ∀ (m i : Nat), n - i = m → i ≤ n → ∀ ρ : Nat → V,
      Sat V (Γ.drop (n - i)) ρ → Q ρ (pps.drop i) from
    fun i => this (n - i) i rfl
  intro m
  induction m with
  | zero =>
    intro i hm hi ρ hρ
    have hin : i = n := by omega
    rw [hin, Nat.sub_self, List.drop_zero] at hρ
    rw [hin, ← hlen, List.drop_length]
    exact hnil ρ hρ
  | succ m ih =>
  intro i hm hi ρ hρ
  by_cases hin : i = n
  · rw [hin, Nat.sub_self, List.drop_zero] at hρ
    rw [hin, ← hlen, List.drop_length]
    exact hnil ρ hρ
  · have hlt : i < n := by omega
    obtain ⟨p, hp, hpe⟩ := hent i hlt
    have hdrop : pps.drop i = p :: pps.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by omega)]
      congr 1
      rw [List.getElem?_eq_getElem (by omega)] at hp
      exact Option.some.inj hp
    rw [hdrop]
    refine hcons ρ p _ (List.mem_of_getElem? hp) ?_ fun a ha => ?_
    · rw [hpe]; exact okΓ i hlt ρ hρ
    · refine ih (i + 1) (by omega) (by omega) (cons a ρ) ?_
      rw [show n - (i + 1) = n - i - 1 from by omega,
        List.drop_eq_getElem_cons (l := Γ) (i := n - i - 1) (by omega)]
      have hG : Γ[n - i - 1] = Γ.getD (n - 1 - i) default := by
        rw [List.getD, List.getElem?_eq_getElem (by omega)]
        simp only [Option.getD_some]
        congr 1; omega
      rw [hG, show n - i - 1 + 1 = n - i from by omega]
      rw [hpe] at ha
      exact Sat_cons V hρ ha

/-! ## The field chain -/

/-- The field entries of a context, in binder order, from position
`j`: entry `nP + j + t` of an opening of length `k`. -/
@[expose] def fieldsFrom (Γ : List AnnotTerm) (k nP nF j : Nat) : List AnnotTerm :=
  (List.range (nF - j)).map fun t => Γ.getD (k - 1 - (nP + j + t)) default

theorem fieldsFrom_succ {Γ : List AnnotTerm} {k nP nF j : Nat} (hj : j < nF) :
    fieldsFrom Γ k nP nF j
      = Γ.getD (k - 1 - (nP + j)) default :: fieldsFrom Γ k nP nF (j + 1) := by
  unfold fieldsFrom
  rw [show nF - j = (nF - (j + 1)) + 1 from by omega, List.range_succ_eq_map,
    List.map_cons, List.map_map]
  rw [Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro t _
  show Γ.getD (k - 1 - (nP + j + (t + 1))) default
    = Γ.getD (k - 1 - (nP + (j + 1) + t)) default
  congr 2
  omega

/-- **The field chain is `FieldsOkB`-graded** from the gradings and
the per-field bounds, at every valuation satisfying the parameters and
the earlier fields. -/
theorem fieldsOkB_of_frame {w : Nat} {Γ : List AnnotTerm} {k nP nF : Nat}
    (hk : k = nP + nF) (hΓ : Γ.length = k)
    (okΓ : ∀ i, i < k → ∀ ρ : Nat → V, Sat V (Γ.drop (k - i)) ρ →
      WellDenotedV V ρ (Γ.getD (k - 1 - i) default))
    (hbnd : ∀ j, j < nF → ∀ ρ : Nat → V, Sat V (Γ.drop (k - (nP + j))) ρ →
      w ≠ 0 → interp V ρ (Γ.getD (k - 1 - (nP + j)) default) ∈ˢ (univ w : V)) :
    ∀ (j : Nat), j ≤ nF → ∀ ρ : Nat → V, Sat V (Γ.drop (k - (nP + j))) ρ →
      FieldsOkB w ρ (fieldsFrom Γ k nP nF j) := by
  suffices ∀ (m j : Nat), nF - j = m → j ≤ nF → ∀ ρ : Nat → V,
      Sat V (Γ.drop (k - (nP + j))) ρ →
      FieldsOkB w ρ (fieldsFrom Γ k nP nF j) from
    fun j => this (nF - j) j rfl
  intro m
  induction m with
  | zero =>
    intro j hm hj ρ hρ
    have hjn : j = nF := by omega
    subst hjn
    simp only [fieldsFrom, Nat.sub_self, List.range_zero, List.map_nil]
    trivial
  | succ m ih =>
    intro j hm hj ρ hρ
    have hlt : j < nF := by omega
    rw [fieldsFrom_succ hlt]
    refine ⟨(okΓ (nP + j) (by omega) ρ hρ).1, hbnd j hlt ρ hρ, fun a ha => ?_⟩
    refine ih (j + 1) (by omega) (by omega) (cons a ρ) ?_
    rw [show k - (nP + (j + 1)) = k - (nP + j) - 1 from by omega,
      List.drop_eq_getElem_cons (l := Γ) (i := k - (nP + j) - 1) (by omega)]
    have hG : Γ[k - (nP + j) - 1] = Γ.getD (k - 1 - (nP + j)) default := by
      rw [List.getD, List.getElem?_eq_getElem (by omega)]
      simp only [Option.getD_some]
      congr 1; omega
    rw [hG, show k - (nP + j) - 1 + 1 = k - (nP + j) from by omega]
    exact Sat_cons V hρ ha

/-! ## Spines and satisfaction -/

/-- A fitting spine satisfies the entries it fits, pushed onto the
ambient context (the entries in binder order become the context's
innermost-first prefix). -/
theorem sat_of_spineFit :
    ∀ {Ds : List AnnotTerm} {as : List V} {Δ₀ : List AnnotTerm} {ρ : Nat → V},
      Sat V Δ₀ ρ → SpineFit ρ Ds as →
      Sat V (Ds.reverse ++ Δ₀) (consList as ρ)
  | [], [], _, _, h, _ => by simpa using h
  | [], _ :: _, _, _, _, hsp => hsp.elim
  | _ :: _, [], _, _, _, hsp => hsp.elim
  | D :: Ds, a :: as, Δ₀, ρ, h, hsp => by
    rw [consList_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    exact sat_of_spineFit (Sat_cons V h hsp.1) hsp.2

/-- `SpineFit` along the peel's domains from `Sat` of the peeled
context (the converse, at the context's own valuation). -/
theorem spineFit_of_sat :
    ∀ {Ds : List AnnotTerm} {Δ₀ : List AnnotTerm} {ρ : Nat → V},
      Sat V (Ds.reverse ++ Δ₀) ρ →
      SpineFit (fun j => ρ (j + Ds.length)) Ds
        ((List.range Ds.length).reverse.map ρ) := by
  intro Ds
  induction Ds with
  | nil => intro Δ₀ ρ _; simp [SpineFit]
  | cons D Ds ih =>
    intro Δ₀ ρ h
    rw [List.reverse_cons, List.append_assoc, List.singleton_append] at h
    have hd := Sat_drop h Ds.length
    rw [List.drop_append_of_le_length (by simp),
      List.drop_eq_nil_of_le (by simp), List.nil_append] at hd
    obtain ⟨h0, -⟩ := Sat_cons_inv hd
    rw [List.length_cons, List.range_succ, List.reverse_append,
      List.reverse_singleton, List.singleton_append, List.map_cons]
    refine ⟨?_, ?_⟩
    · have e : (fun j => ρ (j + (Ds.length + 1))) = fun j => ρ (j + 1 + Ds.length) := by
        funext j; congr 1; omega
      rw [e]
      simpa using h0
    · have := ih (Δ₀ := D :: Δ₀) (ρ := ρ) h
      have e : cons (ρ Ds.length) (fun j => ρ (j + (Ds.length + 1)))
          = fun j => ρ (j + Ds.length) := by
        funext j
        cases j with
        | zero => show ρ Ds.length = ρ (0 + Ds.length); rw [Nat.zero_add]
        | succ j => show ρ (j + (Ds.length + 1)) = ρ (j + 1 + Ds.length); congr 1; omega
      rw [e]
      exact this

end ConLeche.Model
