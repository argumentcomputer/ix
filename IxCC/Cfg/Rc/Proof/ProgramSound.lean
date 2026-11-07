import IxCC.Cfg.Rc.Proof.Maps

set_option autoImplicit false
namespace IxCC.Cfg.Rc

def EntryOk (F : Fir.Program) (bodies : Src.NatMap Own.Plain.Code)
    (f : Nat) (fd : Cfg.Fun) (table : ActionTable) : Prop :=
  ∃ source body, F.fun? f = some source ∧ bodies.get? f = some body ∧
    fd = lowerFunction F.size f source body ∧ functionBounds F.size source.vars fd = true ∧
    collect F.size source.vars (instructions fd) = some table

theorem entries_ok {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {ids : List Nat} {es : List (Nat × Cfg.Fun × ActionTable)}
    (h : entries F bodies ids = some es) : ∀ e ∈ es, EntryOk F bodies e.1 e.2.1 e.2.2 := by
  induction ids generalizing es with
  | nil => simp [entries] at h; subst es; simp
  | cons f ids ih =>
    rw [entries] at h
    cases hf : F.fun? f with
    | none => simp [hf] at h
    | some source =>
      simp only [hf, bind, Option.bind] at h
      cases hb : bodies.get? f with
      | none => simp [hb] at h
      | some body =>
        simp only [hb, bind, Option.bind] at h
        split at h
        · cases h
        · next hbound =>
          have bound : functionBounds F.size source.vars (lowerFunction F.size f source body) = true := by
            simpa using hbound
          cases ht : collect F.size source.vars (instructions (lowerFunction F.size f source body)) with
          | none => simp [ht] at h
          | some table =>
            simp only [ht, bind, Option.bind] at h
            cases he : entries F bodies ids with
            | none => simp [he] at h
            | some tail =>
              simp only [he, bind, Option.bind, Option.some.injEq] at h
              subst es
              intro e member
              rcases List.mem_cons.mp member with rfl | member
              · exact ⟨source, body, hf, hb, rfl, bound, ht⟩
              · exact ih he e member

/-- A numbered entry has both its actual lowered function and actual complete
table in the generated maps, together with the source and layout witnesses. -/
theorem generate_entry {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (h : generate F bodies = some P) {f : Nat} (hf : f < F.size) :
    ∃ fd table, P.base.fun? f = some fd ∧ P.actions.get? f = some table ∧ EntryOk F bodies f fd table := by
  unfold generate at h
  cases he : entries F bodies (List.range F.size) with
  | none => simp [he] at h
  | some es =>
    simp only [he, bind, Option.bind, Option.some.injEq] at h
    subst P
    have keys := entries_keys he
    have hn : (es.map (·.1)).Nodup := by rw [keys]; exact List.nodup_range
    have member : f ∈ es.map (·.1) := by rw [keys]; exact List.mem_range.mpr hf
    obtain ⟨e, mem, eq⟩ := List.mem_map.mp member
    rcases e with ⟨index, fd, table⟩
    simp only at eq
    subst index
    refine ⟨fd, table, ?_, ?_, entries_ok he _ mem⟩
    · exact Src.NatMap.get?_ofList
        (by simpa only [List.map_map, Function.comp_def] using hn)
        (List.mem_map.mpr ⟨(f, fd, table), mem, rfl⟩)
    · exact Src.NatMap.get?_ofList
        (by simpa only [List.map_map, Function.comp_def] using hn)
        (List.mem_map.mpr ⟨(f, fd, table), mem, rfl⟩)

theorem checked_entry {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (h : checkProgram F bodies P = true) {f : Nat} (hf : f < F.size) :
    ∃ fd table, P.base.fun? f = some fd ∧ P.actions.get? f = some table ∧ EntryOk F bodies f fd table :=
  generate_entry (checkProgram_parts h).2 hf


end IxCC.Cfg.Rc
