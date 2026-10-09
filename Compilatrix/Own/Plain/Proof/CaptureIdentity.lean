import Compilatrix.Own.Plain.Proof.Captures

/-! Lexical identities, separately from aliased heap values. Captures are an
ordered sublist of the active unique variable names. Fresh bindings cannot
overwrite their saved lookups, including parameter rebinding after a jump. -/

set_option autoImplicit false

namespace Compilatrix.Own.Plain

theorem fresh_nodup_append {live params : List Fir.Var}
    (hl : live.Nodup) (hf : fresh live params = true) : (live ++ params).Nodup := by
  induction params generalizing live with
  | nil => simpa using hl
  | cons x xs ih =>
    have hp : (!live.contains x) = true ∧ fresh (live ++ [x]) xs = true := by
      simpa only [fresh, Bool.and_eq_true] using hf
    have hx : x ∉ live := by simpa using hp.1
    have hn : (live ++ [x]).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨hl, by simp, ?_⟩
      intro y hy z hz he
      have hz' : z = x := by simpa using hz
      subst z
      subst y
      exact hx hy
    simpa [List.append_assoc] using ih hn hp.2

theorem fresh_avoids {live params : List Fir.Var} (hf : fresh live params = true)
    {x : Fir.Var} (hx : x ∈ live) : x ∉ params := by
  induction params generalizing live with
  | nil => simp
  | cons y ys ih =>
    have hp : (!live.contains y) = true ∧ fresh (live ++ [y]) ys = true := by
      simpa only [fresh, Bool.and_eq_true] using hf
    have hy : y ∉ live := by simpa using hp.1
    intro hm
    rcases List.mem_cons.mp hm with he | hm
    · subst x
      exact hy hx
    · exact ih hp.2 (List.mem_append_left _ hx) hm

theorem get_bindAll_untouched (ρ : Own.Env) (params : List Fir.Var) (values : List RVal)
    (x : Fir.Var) (hx : x ∉ params) : (Own.bindAll ρ params values).get? x = ρ.get? x := by
  induction params generalizing ρ values with
  | nil => rfl
  | cons p ps ih =>
    cases values with
    | nil => rfl
    | cons v vs =>
      have hp : x ≠ p := by intro he; subst x; exact hx (by simp)
      have ht : x ∉ ps := fun hm => hx (List.mem_cons_of_mem _ hm)
      rw [Own.bindAll, ih _ _ ht, Src.NatMap.get?_insert_ne _ _ hp]

structure CaptureView (saved current : Own.Env) (captured live : List Fir.Var) : Prop where
  order : captured.Sublist live
  distinct : live.Nodup
  agree : ∀ x, x ∈ captured → saved.get? x = current.get? x

theorem CaptureView.declare (ρ : Own.Env) (live : List Fir.Var) (hl : live.Nodup) :
    CaptureView ρ ρ live live := ⟨List.Sublist.refl _, hl, fun _ _ => rfl⟩

theorem CaptureView.captured_nodup {saved current : Own.Env} {captured live : List Fir.Var}
    (h : CaptureView saved current captured live) : captured.Nodup := h.order.nodup h.distinct

theorem CaptureView.bind {saved current : Own.Env} {captured live : List Fir.Var}
    (h : CaptureView saved current captured live) (x : Fir.Var) (v : RVal) (hx : x ∉ live) :
    CaptureView saved (current.insert x v) captured (live ++ [x]) := by
  refine ⟨List.sublist_append_of_sublist_left h.order, ?_, ?_⟩
  · exact fresh_nodup_append h.distinct (by simp [fresh, hx])
  · intro y hy
    have he : y ≠ x := by intro he; subst y; exact hx (h.order.subset hy)
    rw [Src.NatMap.get?_insert_ne _ _ he]
    exact h.agree y hy

theorem CaptureView.rebind {saved current : Own.Env} {captured live : List Fir.Var}
    (h : CaptureView saved current captured live) (params : List Fir.Var) (values : List RVal)
    (hf : fresh live params = true) :
    CaptureView saved (Own.bindAll current params values) captured (live ++ params) := by
  refine ⟨List.sublist_append_of_sublist_left h.order, fresh_nodup_append h.distinct hf, ?_⟩
  intro x hx
  rw [get_bindAll_untouched current params values x (fresh_avoids hf (h.order.subset hx))]
  exact h.agree x hx


end Compilatrix.Own.Plain
