import Compilatrix.Cfg.Rc.Markers
import Compilatrix.Src.Proof.NatMap

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc


theorem decode_marker (limit slot : Nat) (a : Action) : decode limit (marker limit slot a) = some (slot, a) := by
  cases a <;> simp [decode, marker]

theorem reserved_marker (limit slot : Nat) (a : Action) : reserved limit (marker limit slot a) = true := by
  cases a <;> simp [reserved, marker]

theorem tableEq_iff (a b : ActionTable) : tableEq a b = true ↔ a = b := by
  induction a generalizing b with
  | leaf => cases b <;> simp [tableEq]
  | node v z o iz io => cases b <;> simp [tableEq, iz, io, and_assoc]

theorem checkMarkers_iff (limit first : Nat) (code : List Instr) (table : ActionTable) :
    checkMarkers limit first code table = true ↔ collect limit first code = some table := by
  unfold checkMarkers
  cases h : collect limit first code with
  | none => simp
  | some expected => simp [tableEq_iff]

theorem collect_reserved {limit first : Nat} {i : Instr} {rest : List Instr} {table : ActionTable}
    (hc : collect limit first (i :: rest) = some table) (hr : reserved limit i = true) :
    ∃ slot a tail, decode limit i = some (slot, a) ∧ first ≤ slot ∧
      collect limit first rest = some tail ∧ tail.contains slot = false ∧ table = tail.insert slot a := by
  cases ht : collect limit first rest with
  | none => simp [collect, ht] at hc
  | some tail =>
    cases hd : decode limit i with
    | none => simp [collect, ht, hr, hd] at hc
    | some pair =>
      obtain ⟨slot, a⟩ := pair
      simp only [collect, ht, hr, hd, bind, Option.bind, ↓reduceIte] at hc
      split at hc
      · cases hc
      · next hn =>
        have hs : first ≤ slot ∧ tail.contains slot = false := by
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hn
          exact ⟨by omega, by cases h : tail.contains slot <;> simp_all⟩
        cases hc
        exact ⟨slot, a, tail, rfl, hs.1, rfl, hs.2, rfl⟩

theorem checked_head_intercepts {limit first : Nat} {i : Instr} {rest : List Instr} {table : ActionTable}
    (hc : checkMarkers limit first (i :: rest) table = true) (hr : reserved limit i = true) :
    ∃ slot a, decode limit i = some (slot, a) ∧ first ≤ slot ∧ table.get? slot = some a := by
  obtain ⟨slot, a, tail, hd, hs, _, _, ht⟩ := collect_reserved ((checkMarkers_iff ..).mp hc) hr
  exact ⟨slot, a, hd, hs, by rw [ht, Src.NatMap.get?_insert_self]⟩

end Compilatrix.Cfg.Rc
