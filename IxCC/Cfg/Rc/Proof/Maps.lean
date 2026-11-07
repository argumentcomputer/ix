import IxCC.Cfg.Rc.Proof.Check

set_option autoImplicit false
namespace IxCC.Cfg.Rc

theorem entries_keys {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {ids : List Nat} {es : List (Nat × Cfg.Fun × ActionTable)}
    (h : entries F bodies ids = some es) : es.map (·.1) = ids := by
  induction ids generalizing es with
  | nil => simp [entries] at h; subst es; rfl
  | cons f ids ih =>
    rw [entries] at h
    cases hf : F.fun? f with
    | none => simp [hf] at h
    | some fd =>
      simp only [hf, bind, Option.bind] at h
      cases hb : bodies.get? f with
      | none => simp [hb] at h
      | some body =>
        simp only [hb, bind, Option.bind] at h
        split at h
        · cases h
        · cases ht : collect F.size fd.vars (instructions (lowerFunction F.size f fd body)) with
          | none => simp [ht] at h
          | some table =>
            simp only [ht, bind, Option.bind] at h
            cases he : entries F bodies ids with
            | none => simp [he] at h
            | some tail =>
              simp only [he, bind, Option.bind, Option.some.injEq] at h
              subst es
              simp only [List.map_cons, ih he]

theorem get_ofList_absent {α : Type} (xs : List (Nat × α))
    (hn : (xs.map (·.1)).Nodup) {k : Nat} (hk : k ∉ xs.map (·.1)) :
    (Src.NatMap.ofList xs).get? k = none :=
  (Src.NatMap.get?_foldl_insert (fun _ _ => rfl) xs .leaf hn).1 k hk

/-- Sparse trie extras cannot hide behind the program size: both maps are
constructed only from the exact successful numbered entry list. -/
theorem generate_reserved_absent {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (h : generate F bodies = some P) {f : Nat} (hf : F.size ≤ f) :
    P.base.fun? f = none ∧ P.actions.get? f = none := by
  unfold generate at h
  cases he : entries F bodies (List.range F.size) with
  | none => simp [he] at h
  | some es =>
    simp only [he, bind, Option.bind, Option.some.injEq] at h
    subst P
    have keys := entries_keys he
    have hn : (es.map (·.1)).Nodup := by rw [keys]; exact List.nodup_range
    have absent : f ∉ es.map (·.1) := by rw [keys]; simp; omega
    constructor
    · exact get_ofList_absent (es.map fun e => (e.1, e.2.1))
        (by simpa only [List.map_map, Function.comp_def] using hn)
        (by simpa only [List.map_map, Function.comp_def] using absent)
    · exact get_ofList_absent (es.map fun e => (e.1, e.2.2))
        (by simpa only [List.map_map, Function.comp_def] using hn)
        (by simpa only [List.map_map, Function.comp_def] using absent)

theorem checked_reserved_absent {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (h : checkProgram F bodies P = true) {f : Nat} (hf : F.size ≤ f) :
    P.base.fun? f = none ∧ P.actions.get? f = none :=
  generate_reserved_absent (checkProgram_parts h).2 hf

theorem generate_size {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (h : generate F bodies = some P) : P.base.size = F.size := by
  unfold generate at h
  cases he : entries F bodies (List.range F.size) with
  | none => simp [he] at h
  | some es =>
    simp only [he, bind, Option.bind, Option.some.injEq] at h
    subst P
    rfl

/-- Legacy execution cannot accidentally call a candidate-supplied function
at either marker ID after complete-map admission. -/
theorem checked_reserved_call_stuck {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (h : checkProgram F bodies P = true) (offset : Nat)
    (args : List Own.RVal) (stk : List (Frame × Fir.Var)) (H : Own.Heap) :
    Cfg.step .rc P.base (.call (P.base.size + offset) args stk H) = .stuck := by
  have size := generate_size (checkProgram_parts h).2
  have absent := (checked_reserved_absent h (f := P.base.size + offset) (by omega)).1
  simp only [Cfg.step, absent]



end IxCC.Cfg.Rc
