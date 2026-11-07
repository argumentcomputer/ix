import IxCC.Cfg.Rc.Proof.Step

set_option autoImplicit false
namespace IxCC.Cfg.Rc

/-- Collection preserves every action in the instruction suffix. -/
theorem collect_tail {limit first : Nat} {i : Instr} {rest : List Instr} {table : ActionTable}
    (hc : collect limit first (i :: rest) = some table) :
    ∃ tail, collect limit first rest = some tail ∧
      ∀ slot a, tail.get? slot = some a → table.get? slot = some a := by
  cases hr : reserved limit i with
  | true =>
    obtain ⟨slot, a, tail, _, _, ht, absent, eq⟩ := collect_reserved hc hr
    refine ⟨tail, ht, ?_⟩
    intro s b hb
    have ne : s ≠ slot := by
      intro h
      subst s
      simp [Src.NatMap.contains, hb] at absent
    rw [eq, Src.NatMap.get?_insert_ne _ _ ne]
    exact hb
  | false =>
    cases ht : collect limit first rest with
    | none => simp [collect, ht] at hc
    | some tail =>
      have eq : tail = table := by
        cases i with
        | bind x rhs =>
          cases rhs with
          | fir r =>
            cases r <;> simp [collect, ht, hr] at hc <;> exact hc.2
          | alloc c args kind =>
            simp [collect, ht, hr] at hc
            exact hc.2
          | proj x key index =>
            simp [collect, ht, hr] at hc
            exact hc.2
      exact ⟨tail, rfl, by intro s a h; simpa [← eq] using h⟩

theorem collect_member {limit first : Nat} {code : List Instr} {table : ActionTable} {i : Instr}
    (hc : collect limit first code = some table) (hi : i ∈ code)
    (hr : reserved limit i = true) :
    ∃ slot a, decode limit i = some (slot, a) ∧ first ≤ slot ∧ table.get? slot = some a := by
  induction code generalizing table with
  | nil => simp at hi
  | cons head rest ih =>
    cases hi with
    | head => exact checked_head_intercepts ((checkMarkers_iff ..).mpr hc) hr
    | tail _ hi =>
      obtain ⟨tail, ht, preserve⟩ := collect_tail hc
      obtain ⟨slot, a, hd, hs, ha⟩ := ih ht hi
      exact ⟨slot, a, hd, hs, preserve slot a ha⟩

/-- The complete function table covers a marker reached in any block/suffix,
not merely the first instruction in the flattened function inventory. -/
theorem step_checked_member {P : Program} {fr : Frame} {stk : List (Frame × Fir.Var)}
    {H : Own.Heap} {i : Instr} {rest code : List Instr} {table : ActionTable} {first : Nat}
    (hrest : fr.rest = i :: rest) (ht : P.actions.get? fr.fn = some table)
    (hc : checkMarkers P.base.size first code table = true) (hi : i ∈ code)
    (hr : reserved P.base.size i = true) :
    ∃ slot a, decode P.base.size i = some (slot, a) ∧ first ≤ slot ∧
      step P (.run fr stk H) = actionStep fr stk H rest a := by
  obtain ⟨slot, a, hd, hs, ha⟩ := collect_member ((checkMarkers_iff ..).mp hc) hi hr
  refine ⟨slot, a, hd, hs, ?_⟩
  simp [step, hrest, hr, hd, ht, ha]


end IxCC.Cfg.Rc
