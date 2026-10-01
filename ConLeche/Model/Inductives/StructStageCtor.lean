module

public import ConLeche.Model.Inductives.StructCtorFrames
public section

/-!
# The constructor's cons (task #175 W4c, P3 module 6, part 5)

`stageCtor`: the P step at the constructor's cons.  The leaf is
`structMkAV (resSort.eval ψ) (ds ψ) (Fs ψ)` over the constructor
type's peel; its two hereditary premises (`MkPre`, `UnderTowerValid`)
walk the parameter frame and the full frame from the constructor's
data and frames; the family application at the bottom folds the
former's real leaf along the parameters (`formerFold`), the frames
identified.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps StructParts)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Kit -/

omit [SetTheory V] in
theorem consN_eq_consList : ∀ (ts : List V) (ρ : Nat → V), consN ts ρ = consList ts ρ
  | [], _ => rfl
  | t :: ts, ρ => consN_eq_consList ts (cons t ρ)

omit [SetTheory V] in
/-- The reversed range under a consed spine recovers the spine. -/
theorem range_reverse_map_consList :
    ∀ (as : List V) (ρ : Nat → V),
      (List.range as.length).reverse.map (consList as ρ) = as
  | [], _ => rfl
  | a :: as, ρ => by
    rw [List.length_cons, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, consList_cons]
    have h0 : consList as (cons a ρ) as.length = a := by
      have := consList_apply_add as (cons a ρ) 0
      rw [Nat.zero_add] at this
      rw [this]; rfl
    rw [h0, range_reverse_map_consList as (cons a ρ)]

/-- Two domain lists whose reversed contexts have the same satisfying
valuations fit the same spines. -/
theorem spineFit_iff_of_sat_iff {Ds₁ Ds₂ : List AnnotTerm}
    (hlen : Ds₁.length = Ds₂.length)
    (hiff : ∀ ρ : Nat → V, Sat V Ds₁.reverse ρ ↔ Sat V Ds₂.reverse ρ)
    (ρ : Nat → V) (as : List V) (hl : as.length = Ds₁.length) :
    SpineFit ρ Ds₁ as ↔ SpineFit ρ Ds₂ as := by
  have key : ∀ (Ds₁ Ds₂ : List AnnotTerm), Ds₁.length = Ds₂.length →
      (∀ ρ : Nat → V, Sat V Ds₁.reverse ρ → Sat V Ds₂.reverse ρ) →
      ∀ (ρ : Nat → V) (as : List V), as.length = Ds₁.length →
      SpineFit ρ Ds₁ as → SpineFit ρ Ds₂ as := by
    intro Ds₁ Ds₂ hlen hsat ρ as hl h
    have h1 := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) h
    rw [List.append_nil] at h1
    have h2 := spineFit_of_sat (Δ₀ := []) (Ds := Ds₂)
      (by rw [List.append_nil]; exact hsat _ h1)
    have e1 : (fun j => consList as ρ (j + Ds₂.length)) = ρ := by
      funext j; rw [← hlen, ← hl, consList_apply_add]
    have e2 : ((List.range Ds₂.length).reverse.map (consList as ρ)) = as := by
      rw [← hlen, ← hl]; exact range_reverse_map_consList as ρ
    rw [e1, e2] at h2
    exact h2
  exact ⟨key Ds₁ Ds₂ hlen (fun ρ => (hiff ρ).mp) ρ as hl,
    key Ds₂ Ds₁ hlen.symm (fun ρ => (hiff ρ).mpr) ρ as (by rw [hl, hlen])⟩

/-- The reversed constructor context's parameter entries are the
reversed parameter context's. -/
theorem getD_reverse_take {ds : List (Nat × Nat × AnnotTerm)} {nP nF : Nat}
    (hlen : ds.length = nP + nF) {i : Nat} (hi : i < nP) :
    ((ds.map (·.2.2)).reverse).getD (nP + nF - 1 - i) default
      = (((ds.take nP).map (·.2.2)).reverse).getD (nP - 1 - i) default := by
  have hil : i < ds.length := by omega
  rw [getD_reverse_of_peel hlen (by omega) (List.getElem?_eq_getElem hil),
    getD_reverse_of_peel (List.length_take_of_le (by omega)) hi
      (by rw [List.getElem?_take_of_lt hi]; exact List.getElem?_eq_getElem hil)]

/-! ## The constructor leaf's premises -/

/-! ## The cons -/

end ConLeche.Model
