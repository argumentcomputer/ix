module

public import ConLeche.Model.Inductives.StructCtorData
public import ConLeche.Model.Inductives.StructIntro
public section

/-!
# The constructor's frames (task #175 W4c, P3 module 6, part 4)

`ctorFrames`: from the former's and the constructor's data at the
environment holding the former, the binder-domain pins identify the
two parameter frames (`paramFrames`), and the field-sort runs grade
the field chain at the constructor's parameter frame — `FieldsOkB`
(bounded by the result sort in the graph regime, O5), `FieldsValid`,
and `FieldsBound 0` at a propositional structure with the large
eliminator.  These are the premises the former's real leaf and the
constructor's leaf consume.
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

/-- An opened type whose reading is a known peel: the opened record
at the peel's reversed domains. -/
theorem opened_of_peel {m : EnvModel V env} {k : Nat} {e : Expr}
    {fvs : List Expr} {o : Expr} {pps : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm}
    (hop : openPisAtFvars k e 0 = some (fvs, o)) (hcl : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true)
    (hread : denoteMeta m.acval env φ 0 e = some (mkPisAV pps b))
    (hlen : pps.length = k)
    (hok : ∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV pps b)) :
    Opened m φ k e fvs o ((pps.map (·.2.2)).reverse) b := by
  obtain ⟨Γ, R, htele, hO⟩ := opened_of hop hcl hb hread hok
  have hst := stripPisAV_mkPisAV pps b
  rw [hlen] at hst
  obtain ⟨rfl, rfl⟩ := PiTeleAV.unique htele (piTeleAV_of_stripPisAV hst)
  exact hO

/-- The field entries of the reversed constructor context are the
peel's field domains. -/
theorem fieldsFrom_eq_drop {ds : List (Nat × Nat × AnnotTerm)} {nP nF : Nat}
    (hlen : ds.length = nP + nF) :
    fieldsFrom ((ds.map (·.2.2)).reverse) (nP + nF) nP nF 0
      = (ds.drop nP).map (·.2.2) := by
  apply List.ext_getElem
  · simp [fieldsFrom, hlen]
  · intro t h1 h2
    simp only [fieldsFrom, List.getElem_map, List.getElem_range, List.getElem_drop]
    have ht : t < nF := by simpa [fieldsFrom] using h1
    rw [Nat.add_zero, getD_reverse_of_peel hlen (by omega)
      (List.getElem?_eq_getElem (by omega))]

/-- The reversed constructor context above the fields is the reversed
parameter context. -/
theorem drop_fields_eq {ds : List (Nat × Nat × AnnotTerm)} {nP nF : Nat}
    (hlen : ds.length = nP + nF) (i : Nat) (hi : i ≤ nP) :
    ((ds.map (·.2.2)).reverse).drop (nP + nF - i)
      = (((ds.take nP).map (·.2.2)).reverse).drop (nP - i) := by
  rw [reverse_map_take_drop ds nP, List.drop_append]
  have hl : (((ds.drop nP).map (·.2.2)).reverse).length = nF := by
    simp [hlen]
  rw [List.drop_eq_nil_of_le (by rw [hl]; omega), List.nil_append, hl,
    show nP + nF - i - nF = nP - i from by omega]

/-- The field chain's validity, walked like its grading. -/
theorem fieldsValid_of_frame {Γ : List AnnotTerm} {k nP nF : Nat}
    (hk : k = nP + nF) (hΓ : Γ.length = k)
    (okΓ : ∀ i, i < k → ∀ ρ : Nat → V, Sat V (Γ.drop (k - i)) ρ →
      WellDenotedV V ρ (Γ.getD (k - 1 - i) default)) :
    ∀ (j : Nat), j ≤ nF → ∀ ρ : Nat → V, Sat V (Γ.drop (k - (nP + j))) ρ →
      FieldsValid ρ (fieldsFrom Γ k nP nF j) := by
  suffices ∀ (m j : Nat), nF - j = m → j ≤ nF → ∀ ρ : Nat → V,
      Sat V (Γ.drop (k - (nP + j))) ρ →
      FieldsValid ρ (fieldsFrom Γ k nP nF j) from
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
    refine ⟨(okΓ (nP + j) (by omega) ρ hρ).2, fun a ha => ?_⟩
    refine ih (j + 1) (by omega) (by omega) (cons a ρ) ?_
    rw [show k - (nP + (j + 1)) = k - (nP + j) - 1 from by omega,
      List.drop_eq_getElem_cons (l := Γ) (i := k - (nP + j) - 1) (by omega)]
    have hG : Γ[k - (nP + j) - 1]'(by omega) = Γ.getD (k - 1 - (nP + j)) default := by
      rw [List.getD, List.getElem?_eq_getElem (by omega)]
      simp only [Option.getD_some]
      congr 1; omega
    rw [hG, show k - (nP + j) - 1 + 1 = k - (nP + j) from by omega]
    exact Sat_cons V hρ ha

/-- The field chain's universe bound, walked like its grading. -/
theorem fieldsBound_of_frame {Γ : List AnnotTerm} {k nP nF w : Nat}
    (hk : k = nP + nF) (hΓ : Γ.length = k)
    (hbnd : ∀ j, j < nF → ∀ ρ : Nat → V, Sat V (Γ.drop (k - (nP + j))) ρ →
      interp V ρ (Γ.getD (k - 1 - (nP + j)) default) ∈ˢ (univ w : V)) :
    ∀ (j : Nat), j ≤ nF → ∀ ρ : Nat → V, Sat V (Γ.drop (k - (nP + j))) ρ →
      FieldsBound w ρ (fieldsFrom Γ k nP nF j) := by
  suffices ∀ (m j : Nat), nF - j = m → j ≤ nF → ∀ ρ : Nat → V,
      Sat V (Γ.drop (k - (nP + j))) ρ →
      FieldsBound w ρ (fieldsFrom Γ k nP nF j) from
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
    refine ⟨hbnd j hlt ρ hρ, fun a ha => ?_⟩
    refine ih (j + 1) (by omega) (by omega) (cons a ρ) ?_
    rw [show k - (nP + (j + 1)) = k - (nP + j) - 1 from by omega,
      List.drop_eq_getElem_cons (l := Γ) (i := k - (nP + j) - 1) (by omega)]
    have hG : Γ[k - (nP + j) - 1]'(by omega) = Γ.getD (k - 1 - (nP + j)) default := by
      rw [List.getD, List.getElem?_eq_getElem (by omega)]
      simp only [Option.getD_some]
      congr 1; omega
    rw [hG, show k - (nP + j) - 1 + 1 = k - (nP + j) from by omega]
    exact Sat_cons V hρ ha

/-! ## The frames -/

end ConLeche.Model
