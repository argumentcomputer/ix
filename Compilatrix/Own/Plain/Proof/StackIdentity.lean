import Compilatrix.Own.Plain.Proof.CaptureIdentity

/-! Nested saved environments agree by variable identity. The relation is
rebuilt at a declaration and maintained through fresh bindings and charged
join re-entry; value aliases never replace these lexical requirements. -/

set_option autoImplicit false

namespace Compilatrix.Own.Plain

theorem CaptureView.trans {ρ₀ ρ₁ ρ₂ : Own.Env} {xs ys zs : List Fir.Var}
    (h₀ : CaptureView ρ₀ ρ₁ xs ys) (h₁ : CaptureView ρ₁ ρ₂ ys zs) : CaptureView ρ₀ ρ₂ xs zs :=
  ⟨h₀.order.trans h₁.order, h₁.distinct,
    fun x hx => (h₀.agree x hx).trans (h₁.agree x (h₀.order.subset hx))⟩

inductive StackViews : Own.Env → List Fir.Var → Joins → List JEntry → Prop
  | nil (ρ : Own.Env) (live : List Fir.Var) : StackViews ρ live [] []
  | cons {ρ : Own.Env} {live captured : List Fir.Var} {older : Joins}
      {e : JEntry} {rest : List JEntry}
      (view : CaptureView e.env ρ captured live)
      (tail : StackViews e.env captured older rest) :
      StackViews ρ live ((e.id, captured) :: older) (e :: rest)

theorem StackViews.bind {ρ : Own.Env} {live : List Fir.Var} {joins : Joins} {J : List JEntry}
    (h : StackViews ρ live joins J) (x : Fir.Var) (v : RVal) (hx : x ∉ live) :
    StackViews (ρ.insert x v) (live ++ [x]) joins J := by
  cases h with
  | nil => exact .nil _ _
  | cons hv ht => exact .cons (hv.bind x v hx) ht

theorem StackViews.rebind {ρ : Own.Env} {live : List Fir.Var} {joins : Joins} {J : List JEntry}
    (h : StackViews ρ live joins J) (params : List Fir.Var) (values : List RVal)
    (hf : fresh live params = true) :
    StackViews (Own.bindAll ρ params values) (live ++ params) joins J := by
  cases h with
  | nil => exact .nil _ _
  | cons hv ht => exact .cons (hv.rebind params values hf) ht

theorem StackViews.lookup {ρ : Own.Env} {live : List Fir.Var} {joins : Joins} {J : List JEntry}
    (h : StackViews ρ live joins J) {j : Fir.JoinId} {e : JEntry} {rest : List JEntry}
    (hl : lookupJ j J = some (e, rest)) :
    ∃ captured older, joins.lookup j = some captured ∧ CaptureView e.env ρ captured live ∧
      StackViews e.env captured older rest := by
  induction h with
  | nil => simp [lookupJ] at hl
  | @cons ρ live captured older e₀ rest₀ hv ht ih =>
    by_cases he : e₀.id = j
    · have hh : e₀ = e ∧ rest₀ = rest := by simpa [lookupJ, he] using hl
      rcases hh with ⟨rfl, rfl⟩
      exact ⟨captured, older, by simp [List.lookup, he], hv, ht⟩
    · have hl' : lookupJ j rest₀ = some (e, rest) := by simpa [lookupJ, he] using hl
      obtain ⟨captured', older', hm, hv', ht'⟩ := ih hl'
      have hb : (j == e₀.id) = false := beq_eq_false_iff_ne.mpr (Ne.symm he)
      exact ⟨captured', older', by simpa only [List.lookup, hb] using hm, hv'.trans hv, ht'⟩

theorem StackViews.after {captured : List Fir.Var} {older : Joins}
    {e : JEntry} {rest : List JEntry} (ht : StackViews e.env captured older rest)
    (hn : captured.Nodup) (hf : fresh captured e.params = true) (values : List RVal) :
    StackViews (Own.bindAll e.env e.params values) (captured ++ e.params)
      (if e.isRec then (e.id, captured) :: older else older) (e.after rest) := by
  cases hr : e.isRec with
  | false => simpa [JEntry.after, hr] using ht.rebind e.params values hf
  | true =>
    have hv := (CaptureView.declare e.env captured hn).rebind e.params values hf
    have hs : StackViews (Own.bindAll e.env e.params values) (captured ++ e.params)
        ((e.id, captured) :: older) ({ e with charged := true } :: rest) :=
      .cons (e := { e with charged := true }) hv ht
    simpa [JEntry.after, hr] using hs


end Compilatrix.Own.Plain
