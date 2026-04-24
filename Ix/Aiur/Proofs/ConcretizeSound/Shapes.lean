module
public import Ix.Aiur.Proofs.ConcretizeSound
public import Ix.Aiur.Proofs.ConcretizeSound.Layout

/-!
Shared shape invariants: `StrongNewNameShape` + `NewFnInputsLabelShape`
preservation through `concretizeDrain`, `IndexMap` key-uniqueness in pairs,
and `step4Lower` key-level helpers. Extracted from `ConcretizeSound.lean`
2026-04-29.
-/

public section

namespace Aiur

open Source

/-! ### Helpers shared by `RefClosedBody` and `DirectDagBody`.

These were previously private to `DirectDagBody` (ported from
`MonoDataTypeTraceScratch.lean` on 2026-04-23 and duplicating
`CompilerProgress` content that cannot be imported here due to cycles).
Relocated on 2026-04-23 so `RefClosedBody.L2_*` can use them too. Proof
text is identical to the originals. -/

/-! #### `StrongNewNameShape` preservation through `concretizeDrain`. -/

theorem concretizeDrainEntry_preserves_StrongNewNameShape
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.StrongNewNameShape decls) (entry : Global × Array Typ)
    (hstep : concretizeDrainEntry decls state entry = .ok state') :
    state'.StrongNewNameShape decls := by
  unfold concretizeDrainEntry at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hseen : state.seen.contains (entry.1, entry.2)
  · simp [hseen] at hstep
    rw [← hstep]; exact hinv
  · simp [hseen] at hstep
    split at hstep
    · rename_i f hf_get
      by_cases hsz : f.params.length = entry.2.size
      · simp [hsz] at hstep
        rw [← hstep]
        refine ⟨?_, ?_⟩
        · intro f' hf'mem
          rcases Array.mem_push.mp hf'mem with hin | heq
          · exact hinv.1 f' hin
          · subst heq
            exact ⟨entry.1, entry.2, f, rfl, hf_get, hsz.symm⟩
        · intro dt hdt
          exact hinv.2 dt hdt
      · simp [hsz] at hstep
    · rename_i dt hdt_get
      by_cases hsz : dt.params.length = entry.2.size
      · simp [hsz] at hstep
        rw [← hstep]
        refine ⟨?_, ?_⟩
        · intro f hf
          exact hinv.1 f hf
        · intro dt' hdt'mem
          rcases Array.mem_push.mp hdt'mem with hin | heq
          · exact hinv.2 dt' hin
          · subst heq
            refine ⟨entry.1, entry.2, dt, rfl, hdt_get, hsz.symm, ?_⟩
            rw [List.map_map]
            apply List.map_congr_left
            intro c _
            rfl
      · simp [hsz] at hstep
    · exact absurd hstep (by intro h; cases h)

theorem concretizeDrainEntry_list_foldlM_preserves_StrongNewNameShape
    {decls : Typed.Decls}
    (L : List (Global × Array Typ))
    (state0 state' : DrainState)
    (hinv0 : state0.StrongNewNameShape decls)
    (hstep : L.foldlM (concretizeDrainEntry decls) state0 = .ok state') :
    state'.StrongNewNameShape decls := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]; exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hinv1 : s''.StrongNewNameShape decls :=
        concretizeDrainEntry_preserves_StrongNewNameShape hinv0 hd hs''
      exact ih s'' hinv1 hstep

theorem concretizeDrainIter_preserves_StrongNewNameShape
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.StrongNewNameShape decls)
    (hstep : concretizeDrainIter decls state = .ok state') :
    state'.StrongNewNameShape decls := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : state0.StrongNewNameShape decls := hinv
  exact concretizeDrainEntry_list_foldlM_preserves_StrongNewNameShape
    state.pending.toArray.toList state0 state' hinv0 hstep

theorem concretize_drain_preserves_StrongNewNameShape
    {decls : Typed.Decls} (fuel : Nat) (init : DrainState)
    (hinv : init.StrongNewNameShape decls)
    {drained : DrainState}
    (hdrain : concretizeDrain decls fuel init = .ok drained) :
    drained.StrongNewNameShape decls := by
  induction fuel generalizing init with
  | zero =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp [hpen] at hdrain
  | succ n ih =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp only [hpen, if_false, Bool.false_eq_true] at hdrain
      simp only [bind, Except.bind] at hdrain
      split at hdrain
      · cases hdrain
      · rename_i state' hstate'
        have hinv' : state'.StrongNewNameShape decls :=
          concretizeDrainIter_preserves_StrongNewNameShape hinv hstate'
        exact ih state' hinv' hdrain

/-! #### `NewFnInputsLabelShape` preservation through `concretizeDrain`. -/

theorem concretizeDrainEntry_preserves_NewFnInputsLabelShape
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.NewFnInputsLabelShape decls) (entry : Global × Array Typ)
    (hstep : concretizeDrainEntry decls state entry = .ok state') :
    state'.NewFnInputsLabelShape decls := by
  unfold concretizeDrainEntry at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hseen : state.seen.contains (entry.1, entry.2)
  · simp [hseen] at hstep
    rw [← hstep]; exact hinv
  · simp [hseen] at hstep
    split at hstep
    · rename_i f hf_get
      by_cases hsz : f.params.length = entry.2.size
      · simp [hsz] at hstep
        rw [← hstep]
        intro f' hf'mem
        rcases Array.mem_push.mp hf'mem with hin | heq
        · exact hinv f' hin
        · subst heq
          refine ⟨entry.1, entry.2, f, rfl, hf_get, ?_⟩
          -- Goal: newInputs.map (·.1) = f.inputs.map (·.1) where
          -- newInputs := f.inputs.map (l, t) ↦ (l, Typ.instantiate subst t).
          rw [List.map_map]
          apply List.map_congr_left
          intro lt _
          rfl
      · simp [hsz] at hstep
    · rename_i dt hdt_get
      by_cases hsz : dt.params.length = entry.2.size
      · simp [hsz] at hstep
        rw [← hstep]
        intro f hf
        exact hinv f hf
      · simp [hsz] at hstep
    · exact absurd hstep (by intro h; cases h)

theorem concretizeDrainEntry_list_foldlM_preserves_NewFnInputsLabelShape
    {decls : Typed.Decls}
    (L : List (Global × Array Typ))
    (state0 state' : DrainState)
    (hinv0 : state0.NewFnInputsLabelShape decls)
    (hstep : L.foldlM (concretizeDrainEntry decls) state0 = .ok state') :
    state'.NewFnInputsLabelShape decls := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]; exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hinv1 : s''.NewFnInputsLabelShape decls :=
        concretizeDrainEntry_preserves_NewFnInputsLabelShape hinv0 hd hs''
      exact ih s'' hinv1 hstep

theorem concretizeDrainIter_preserves_NewFnInputsLabelShape
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.NewFnInputsLabelShape decls)
    (hstep : concretizeDrainIter decls state = .ok state') :
    state'.NewFnInputsLabelShape decls := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : state0.NewFnInputsLabelShape decls := hinv
  exact concretizeDrainEntry_list_foldlM_preserves_NewFnInputsLabelShape
    state.pending.toArray.toList state0 state' hinv0 hstep

theorem concretize_drain_preserves_NewFnInputsLabelShape
    {decls : Typed.Decls} (fuel : Nat) (init : DrainState)
    (hinv : init.NewFnInputsLabelShape decls)
    {drained : DrainState}
    (hdrain : concretizeDrain decls fuel init = .ok drained) :
    drained.NewFnInputsLabelShape decls := by
  induction fuel generalizing init with
  | zero =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp [hpen] at hdrain
  | succ n ih =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp only [hpen, if_false, Bool.false_eq_true] at hdrain
      simp only [bind, Except.bind] at hdrain
      split at hdrain
      · cases hdrain
      · rename_i state' hstate'
        have hinv' : state'.NewFnInputsLabelShape decls :=
          concretizeDrainIter_preserves_NewFnInputsLabelShape hinv hstate'
        exact ih state' hinv' hdrain

/-! #### `IndexMap` key-uniqueness in pairs. -/

/-- If two pairs in `m.pairs.toList` share a key, they are equal. -/
theorem indexMap_pairs_key_unique
    {α : Type _} {β : Type _} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α]
    (m : IndexMap α β) {p₁ p₂ : α × β}
    (h₁ : p₁ ∈ m.pairs.toList) (h₂ : p₂ ∈ m.pairs.toList)
    (hkey : p₁.1 == p₂.1) : p₁ = p₂ := by
  obtain ⟨i, hi, hi_eq⟩ := List.getElem_of_mem h₁
  obtain ⟨j, hj, hj_eq⟩ := List.getElem_of_mem h₂
  rw [Array.length_toList] at hi hj
  have hgi : m.pairs[i]'hi = p₁ := by rw [← hi_eq, Array.getElem_toList]
  have hgj : m.pairs[j]'hj = p₂ := by rw [← hj_eq, Array.getElem_toList]
  have hpii := m.pairsIndexed i hi
  have hpij := m.pairsIndexed j hj
  rw [hgi] at hpii
  rw [hgj] at hpij
  have hcong : m.indices[p₁.1]? = m.indices[p₂.1]? :=
    Std.HashMap.getElem?_congr hkey
  rw [hpii, hpij] at hcong
  simp only [Option.some.injEq] at hcong
  subst hcong
  rw [hgi] at hgj; exact hgj

/-- At most one list index has a given key. -/
theorem indexMap_pairs_index_unique_of_key
    {α : Type _} {β : Type _} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α]
    (m : IndexMap α β) {i j : Nat} (hi : i < m.pairs.toList.length)
    (hj : j < m.pairs.toList.length)
    (hkey : ((m.pairs.toList[i]'hi).1 == (m.pairs.toList[j]'hj).1) = true) :
    i = j := by
  rw [Array.length_toList] at hi hj
  rw [Array.getElem_toList, Array.getElem_toList] at hkey
  have hpii := m.pairsIndexed i hi
  have hpij := m.pairsIndexed j hj
  have hcong : m.indices[(m.pairs[i]'hi).1]? = m.indices[(m.pairs[j]'hj).1]? :=
    Std.HashMap.getElem?_congr hkey
  rw [hpii, hpij] at hcong
  exact Option.some.inj hcong

/-- DataType-key bridge for the `step4Lower` fold. Uses
`indexMap_pairs_key_unique` (above) to discharge the post-fold preservation
case where another pair has the same key as the dt-pair: by uniqueness within
`monoDecls.pairs.toList`, that pair must be `(g, .dataType dt)`. -/
theorem step4Lower_fold_dataType_bridge_inline
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {dt : DataType}
    (hmd_get : monoDecls.getByKey g = some (.dataType dt))
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∃ cdt, concDecls.getByKey g = some (.dataType cdt) := by
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  have hmem_ml : (g, Typed.Declaration.dataType dt) ∈ monoDecls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hmd_get
  -- Inner induction with strengthened "preserve .dataType-at-g" invariant,
  -- threading membership in `monoDecls.pairs.toList` to invoke
  -- `indexMap_pairs_key_unique` when another pair shares key g.
  have aux : ∀ (xs : List (Global × Typed.Declaration)) (init result : Concrete.Decls)
      (_hsub : ∀ p, p ∈ xs → p ∈ monoDecls.pairs.toList)
      (_hmem : (g, Typed.Declaration.dataType dt) ∈ xs)
      (_hP : init.getByKey g = none ∨ ∃ cdt, init.getByKey g = some (.dataType cdt)),
      xs.foldlM step4Lower init = .ok result →
      ∃ cdt, result.getByKey g = some (.dataType cdt) := by
    intro xs
    induction xs with
    | nil => intro _ _ _ hmem; cases hmem
    | cons hd tl ih =>
      intro init result hsub hmem hP hf
      simp only [List.foldlM_cons, bind, Except.bind] at hf
      cases hstep_h : step4Lower init hd with
      | error _ => rw [hstep_h] at hf; cases hf
      | ok acc' =>
        rw [hstep_h] at hf
        rcases List.mem_cons.mp hmem with hmem_hd | hmem_tl
        · -- hd = (g, .dataType dt). step4Lower inserts .dataType at g.
          subst hmem_hd
          have hP' : ∃ cdt, acc'.getByKey g = some (.dataType cdt) := by
            unfold step4Lower at hstep_h
            simp only [bind, Except.bind, pure, Except.pure] at hstep_h
            split at hstep_h
            · cases hstep_h
            rename_i ctors _hctors
            simp only [Except.ok.injEq] at hstep_h
            subst hstep_h
            exact ⟨_, IndexMap.getByKey_insert_self _ _ _⟩
          have hsub_tl : ∀ p, p ∈ tl → p ∈ monoDecls.pairs.toList :=
            fun p hp => hsub p (List.mem_cons.mpr (Or.inr hp))
          -- Strengthened tail induction: preserve .dataType-at-g.
          have aux2 : ∀ (ys : List (Global × Typed.Declaration)) (s s' : Concrete.Decls)
              (_hsub' : ∀ p, p ∈ ys → p ∈ monoDecls.pairs.toList),
              (∃ cdt, s.getByKey g = some (.dataType cdt)) →
              ys.foldlM step4Lower s = .ok s' →
              ∃ cdt, s'.getByKey g = some (.dataType cdt) := by
            intro ys
            induction ys with
            | nil => intro s s' _ hP hf
                     simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hf
                     subst hf; exact hP
            | cons hd' tl' ih' =>
              intro s s' hsub' hP hf
              simp only [List.foldlM_cons, bind, Except.bind] at hf
              cases hstep_h' : step4Lower s hd' with
              | error _ => rw [hstep_h'] at hf; cases hf
              | ok s'' =>
                rw [hstep_h'] at hf
                obtain ⟨name', d'⟩ := hd'
                have hsub_tl' : ∀ p, p ∈ tl' → p ∈ monoDecls.pairs.toList :=
                  fun p hp => hsub' p (List.mem_cons.mpr (Or.inr hp))
                by_cases hkn : (name' == g) = true
                · -- By IndexMap key-uniqueness, (name', d') = (g, .dataType dt).
                  have h_hd_in : (name', d') ∈ monoDecls.pairs.toList :=
                    hsub' (name', d') (List.mem_cons.mpr (Or.inl rfl))
                  have h_eq : (name', d') = (g, Typed.Declaration.dataType dt) :=
                    indexMap_pairs_key_unique _ h_hd_in hmem_ml hkn
                  rw [h_eq] at hstep_h'
                  unfold step4Lower at hstep_h'
                  simp only [bind, Except.bind, pure, Except.pure] at hstep_h'
                  split at hstep_h'
                  · cases hstep_h'
                  simp only [Except.ok.injEq] at hstep_h'
                  subst hstep_h'
                  exact ih' _ _ hsub_tl'
                    ⟨_, IndexMap.getByKey_insert_self _ _ _⟩ hf
                · have hne : (name' == g) = false := Bool.not_eq_true _ |>.mp hkn
                  cases d' with
                  | function fn =>
                    unfold step4Lower at hstep_h'
                    simp only [bind, Except.bind, pure, Except.pure] at hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    simp only [Except.ok.injEq] at hstep_h'
                    subst hstep_h'
                    obtain ⟨cdt, hcdt⟩ := hP
                    exact ih' _ _ hsub_tl'
                      ⟨cdt, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcdt⟩
                      hf
                  | dataType dt' =>
                    unfold step4Lower at hstep_h'
                    simp only [bind, Except.bind, pure, Except.pure] at hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    simp only [Except.ok.injEq] at hstep_h'
                    subst hstep_h'
                    obtain ⟨cdt, hcdt⟩ := hP
                    exact ih' _ _ hsub_tl'
                      ⟨cdt, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcdt⟩
                      hf
                  | constructor dt' c' =>
                    unfold step4Lower at hstep_h'
                    simp only [bind, Except.bind, pure, Except.pure] at hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    simp only [Except.ok.injEq] at hstep_h'
                    subst hstep_h'
                    obtain ⟨cdt, hcdt⟩ := hP
                    exact ih' _ _ hsub_tl'
                      ⟨cdt, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcdt⟩
                      hf
          exact aux2 tl acc' result hsub_tl hP' hf
        · -- hd is in tl-context. Either hd has key g (then hd = (g, .dataType dt)
          -- by uniqueness, proceed via dataType insertion) or hd's key ≠ g.
          obtain ⟨name_h, d_h⟩ := hd
          have hsub_tl : ∀ p, p ∈ tl → p ∈ monoDecls.pairs.toList :=
            fun p hp => hsub p (List.mem_cons.mpr (Or.inr hp))
          by_cases hkn : (name_h == g) = true
          · -- By uniqueness, hd = (g, .dataType dt).
            have h_hd_in : (name_h, d_h) ∈ monoDecls.pairs.toList :=
              hsub (name_h, d_h) (List.mem_cons.mpr (Or.inl rfl))
            have h_eq : (name_h, d_h) = (g, Typed.Declaration.dataType dt) :=
              indexMap_pairs_key_unique _ h_hd_in hmem_ml hkn
            rw [h_eq] at hstep_h
            have hP' : ∃ cdt, acc'.getByKey g = some (.dataType cdt) := by
              unfold step4Lower at hstep_h
              simp only [bind, Except.bind, pure, Except.pure] at hstep_h
              split at hstep_h
              · cases hstep_h
              simp only [Except.ok.injEq] at hstep_h
              subst hstep_h
              exact ⟨_, IndexMap.getByKey_insert_self _ _ _⟩
            exact ih acc' result hsub_tl hmem_tl (Or.inr hP') hf
          · have hne : (name_h == g) = false := Bool.not_eq_true _ |>.mp hkn
            have hP' : acc'.getByKey g = none ∨
                ∃ cdt, acc'.getByKey g = some (.dataType cdt) := by
              cases d_h with
              | function fn =>
                unfold step4Lower at hstep_h
                simp only [bind, Except.bind, pure, Except.pure] at hstep_h
                split at hstep_h
                · cases hstep_h
                split at hstep_h
                · cases hstep_h
                split at hstep_h
                · cases hstep_h
                simp only [Except.ok.injEq] at hstep_h
                subst hstep_h
                rcases hP with hp | ⟨cdt, hcdt⟩
                · exact Or.inl (by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hp)
                · exact Or.inr ⟨cdt, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcdt⟩
              | dataType dt_h =>
                unfold step4Lower at hstep_h
                simp only [bind, Except.bind, pure, Except.pure] at hstep_h
                split at hstep_h
                · cases hstep_h
                simp only [Except.ok.injEq] at hstep_h
                subst hstep_h
                rcases hP with hp | ⟨cdt, hcdt⟩
                · exact Or.inl (by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hp)
                · exact Or.inr ⟨cdt, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcdt⟩
              | constructor dt_h c_h =>
                unfold step4Lower at hstep_h
                simp only [bind, Except.bind, pure, Except.pure] at hstep_h
                split at hstep_h
                · cases hstep_h
                split at hstep_h
                · cases hstep_h
                simp only [Except.ok.injEq] at hstep_h
                subst hstep_h
                rcases hP with hp | ⟨cdt, hcdt⟩
                · exact Or.inl (by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hp)
                · exact Or.inr ⟨cdt, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcdt⟩
            exact ih acc' result hsub_tl hmem_tl hP' hf
  apply aux _ _ _ (fun _ hp => hp) hmem_ml _ hfold
  · -- default has none at g
    left
    unfold IndexMap.getByKey
    show ((default : Concrete.Decls).indices[g]?).bind _ = none
    have : (default : Concrete.Decls).indices[g]? = none := by
      show ((default : Std.HashMap Global Nat))[g]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl

/-- Constructor-key bridge for the `step4Lower` fold. Mirror of
`step4Lower_fold_dataType_bridge_inline` over `.constructor`. -/
theorem step4Lower_fold_ctor_bridge_inline
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {dt : DataType} {c : Constructor}
    (hmd_get : monoDecls.getByKey g = some (.constructor dt c))
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∃ cdt cc, concDecls.getByKey g = some (.constructor cdt cc) := by
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  have hmem_ml : (g, Typed.Declaration.constructor dt c) ∈ monoDecls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hmd_get
  have aux : ∀ (xs : List (Global × Typed.Declaration)) (init result : Concrete.Decls)
      (_hsub : ∀ p, p ∈ xs → p ∈ monoDecls.pairs.toList)
      (_hmem : (g, Typed.Declaration.constructor dt c) ∈ xs)
      (_hP : init.getByKey g = none ∨
        ∃ cdt cc, init.getByKey g = some (.constructor cdt cc)),
      xs.foldlM step4Lower init = .ok result →
      ∃ cdt cc, result.getByKey g = some (.constructor cdt cc) := by
    intro xs
    induction xs with
    | nil => intro _ _ _ hmem; cases hmem
    | cons hd tl ih =>
      intro init result hsub hmem hP hf
      simp only [List.foldlM_cons, bind, Except.bind] at hf
      cases hstep_h : step4Lower init hd with
      | error _ => rw [hstep_h] at hf; cases hf
      | ok acc' =>
        rw [hstep_h] at hf
        rcases List.mem_cons.mp hmem with hmem_hd | hmem_tl
        · subst hmem_hd
          have hP' : ∃ cdt cc, acc'.getByKey g = some (.constructor cdt cc) := by
            unfold step4Lower at hstep_h
            simp only [bind, Except.bind, pure, Except.pure] at hstep_h
            split at hstep_h
            · cases hstep_h
            split at hstep_h
            · cases hstep_h
            simp only [Except.ok.injEq] at hstep_h
            subst hstep_h
            exact ⟨_, _, IndexMap.getByKey_insert_self _ _ _⟩
          have hsub_tl : ∀ p, p ∈ tl → p ∈ monoDecls.pairs.toList :=
            fun p hp => hsub p (List.mem_cons.mpr (Or.inr hp))
          have aux2 : ∀ (ys : List (Global × Typed.Declaration)) (s s' : Concrete.Decls)
              (_hsub' : ∀ p, p ∈ ys → p ∈ monoDecls.pairs.toList),
              (∃ cdt cc, s.getByKey g = some (.constructor cdt cc)) →
              ys.foldlM step4Lower s = .ok s' →
              ∃ cdt cc, s'.getByKey g = some (.constructor cdt cc) := by
            intro ys
            induction ys with
            | nil => intro s s' _ hP hf
                     simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hf
                     subst hf; exact hP
            | cons hd' tl' ih' =>
              intro s s' hsub' hP hf
              simp only [List.foldlM_cons, bind, Except.bind] at hf
              cases hstep_h' : step4Lower s hd' with
              | error _ => rw [hstep_h'] at hf; cases hf
              | ok s'' =>
                rw [hstep_h'] at hf
                obtain ⟨name', d'⟩ := hd'
                have hsub_tl' : ∀ p, p ∈ tl' → p ∈ monoDecls.pairs.toList :=
                  fun p hp => hsub' p (List.mem_cons.mpr (Or.inr hp))
                by_cases hkn : (name' == g) = true
                · have h_hd_in : (name', d') ∈ monoDecls.pairs.toList :=
                    hsub' (name', d') (List.mem_cons.mpr (Or.inl rfl))
                  have h_eq : (name', d') = (g, Typed.Declaration.constructor dt c) :=
                    indexMap_pairs_key_unique _ h_hd_in hmem_ml hkn
                  rw [h_eq] at hstep_h'
                  unfold step4Lower at hstep_h'
                  simp only [bind, Except.bind, pure, Except.pure] at hstep_h'
                  split at hstep_h'
                  · cases hstep_h'
                  split at hstep_h'
                  · cases hstep_h'
                  simp only [Except.ok.injEq] at hstep_h'
                  subst hstep_h'
                  exact ih' _ _ hsub_tl'
                    ⟨_, _, IndexMap.getByKey_insert_self _ _ _⟩ hf
                · have hne : (name' == g) = false := Bool.not_eq_true _ |>.mp hkn
                  cases d' with
                  | function fn =>
                    unfold step4Lower at hstep_h'
                    simp only [bind, Except.bind, pure, Except.pure] at hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    simp only [Except.ok.injEq] at hstep_h'
                    subst hstep_h'
                    obtain ⟨cdt, cc, hcc⟩ := hP
                    exact ih' _ _ hsub_tl' ⟨cdt, cc, by
                      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcc⟩ hf
                  | dataType dt' =>
                    unfold step4Lower at hstep_h'
                    simp only [bind, Except.bind, pure, Except.pure] at hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    simp only [Except.ok.injEq] at hstep_h'
                    subst hstep_h'
                    obtain ⟨cdt, cc, hcc⟩ := hP
                    exact ih' _ _ hsub_tl' ⟨cdt, cc, by
                      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcc⟩ hf
                  | constructor dt' c' =>
                    unfold step4Lower at hstep_h'
                    simp only [bind, Except.bind, pure, Except.pure] at hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    simp only [Except.ok.injEq] at hstep_h'
                    subst hstep_h'
                    obtain ⟨cdt, cc, hcc⟩ := hP
                    exact ih' _ _ hsub_tl' ⟨cdt, cc, by
                      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcc⟩ hf
          exact aux2 tl acc' result hsub_tl hP' hf
        · obtain ⟨name_h, d_h⟩ := hd
          have hsub_tl : ∀ p, p ∈ tl → p ∈ monoDecls.pairs.toList :=
            fun p hp => hsub p (List.mem_cons.mpr (Or.inr hp))
          by_cases hkn : (name_h == g) = true
          · have h_hd_in : (name_h, d_h) ∈ monoDecls.pairs.toList :=
              hsub (name_h, d_h) (List.mem_cons.mpr (Or.inl rfl))
            have h_eq : (name_h, d_h) = (g, Typed.Declaration.constructor dt c) :=
              indexMap_pairs_key_unique _ h_hd_in hmem_ml hkn
            rw [h_eq] at hstep_h
            have hP' : ∃ cdt cc, acc'.getByKey g = some (.constructor cdt cc) := by
              unfold step4Lower at hstep_h
              simp only [bind, Except.bind, pure, Except.pure] at hstep_h
              split at hstep_h
              · cases hstep_h
              split at hstep_h
              · cases hstep_h
              simp only [Except.ok.injEq] at hstep_h
              subst hstep_h
              exact ⟨_, _, IndexMap.getByKey_insert_self _ _ _⟩
            exact ih acc' result hsub_tl hmem_tl (Or.inr hP') hf
          · have hne : (name_h == g) = false := Bool.not_eq_true _ |>.mp hkn
            have hP' : acc'.getByKey g = none ∨
                ∃ cdt cc, acc'.getByKey g = some (.constructor cdt cc) := by
              cases d_h with
              | function fn =>
                unfold step4Lower at hstep_h
                simp only [bind, Except.bind, pure, Except.pure] at hstep_h
                split at hstep_h
                · cases hstep_h
                split at hstep_h
                · cases hstep_h
                split at hstep_h
                · cases hstep_h
                simp only [Except.ok.injEq] at hstep_h
                subst hstep_h
                rcases hP with hp | ⟨cdt, cc, hcc⟩
                · exact Or.inl (by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hp)
                · exact Or.inr ⟨cdt, cc, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcc⟩
              | dataType dt_h =>
                unfold step4Lower at hstep_h
                simp only [bind, Except.bind, pure, Except.pure] at hstep_h
                split at hstep_h
                · cases hstep_h
                simp only [Except.ok.injEq] at hstep_h
                subst hstep_h
                rcases hP with hp | ⟨cdt, cc, hcc⟩
                · exact Or.inl (by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hp)
                · exact Or.inr ⟨cdt, cc, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcc⟩
              | constructor dt_h c_h =>
                unfold step4Lower at hstep_h
                simp only [bind, Except.bind, pure, Except.pure] at hstep_h
                split at hstep_h
                · cases hstep_h
                split at hstep_h
                · cases hstep_h
                simp only [Except.ok.injEq] at hstep_h
                subst hstep_h
                rcases hP with hp | ⟨cdt, cc, hcc⟩
                · exact Or.inl (by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hp)
                · exact Or.inr ⟨cdt, cc, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcc⟩
            exact ih acc' result hsub_tl hmem_tl hP' hf
  apply aux _ _ _ (fun _ hp => hp) hmem_ml _ hfold
  · left
    unfold IndexMap.getByKey
    show ((default : Concrete.Decls).indices[g]?).bind _ = none
    have : (default : Concrete.Decls).indices[g]? = none := by
      show ((default : Std.HashMap Global Nat))[g]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl

-- `step4Lower_fold_preserves_TermRefsDt` and `concretize_preserves_TermRefsDt`
-- relocated to `ConcretizeSound/TermRefsDtBridge.lean` 2026-05-04
-- (downstream of `Phase4` so they can use CtorKind/Phase4 infra to discharge
-- the `concretizeBuild_preserves_TermRefsDt` bridge premise).

-- `TypesNotFunction` bridge moved to `ConcretizeSoundTypesNotFunction.lean`.

/-! #### `step4Lower` key-level helpers. -/

/-- `step4Lower` on a `.dataType` input inserts a `.dataType` at the input key. -/
theorem step4Lower_dataType_shape
    {acc : Concrete.Decls} {name : Global} {dt : DataType}
    {r : Concrete.Decls}
    (hstep : step4Lower acc (name, .dataType dt) = .ok r) :
    ∃ cdt : Concrete.DataType,
      r.getByKey name = some (.dataType cdt) := by
  unfold step4Lower at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · cases hstep
  rename_i ctors _hctors
  simp only [Except.ok.injEq] at hstep
  subst hstep
  exact ⟨_, IndexMap.getByKey_insert_self _ _ _⟩

/-- `step4Lower` on a `.function` input inserts a `.function` at the input key. -/
theorem step4Lower_function_shape
    {acc : Concrete.Decls} {name : Global} {f : Typed.Function}
    {r : Concrete.Decls}
    (hstep : step4Lower acc (name, .function f) = .ok r) :
    ∃ cf : Concrete.Function,
      r.getByKey name = some (.function cf) := by
  unfold step4Lower at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · cases hstep
  split at hstep
  · cases hstep
  split at hstep
  · cases hstep
  simp only [Except.ok.injEq] at hstep
  subst hstep
  exact ⟨_, IndexMap.getByKey_insert_self _ _ _⟩

/-- `step4Lower` on a `.constructor` input inserts a `.constructor` at the input key. -/
theorem step4Lower_constructor_shape
    {acc : Concrete.Decls} {name : Global} {dt : DataType} {c : Constructor}
    {r : Concrete.Decls}
    (hstep : step4Lower acc (name, .constructor dt c) = .ok r) :
    ∃ (cdt : Concrete.DataType) (cc : Concrete.Constructor),
      r.getByKey name = some (.constructor cdt cc) := by
  unfold step4Lower at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · cases hstep
  split at hstep
  · cases hstep
  simp only [Except.ok.injEq] at hstep
  subst hstep
  exact ⟨_, _, IndexMap.getByKey_insert_self _ _ _⟩

/-- Length-preservation for `List.mapM` in the `Except` monad. -/
theorem List.mapM_except_ok_length {α β ε : Type}
    {f : α → Except ε β} : ∀ {l : List α} {ls : List β},
    l.mapM f = .ok ls → ls.length = l.length
  | [], ls, h => by
    simp only [_root_.List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | x :: xs, ls, h => by
    simp only [_root_.List.mapM_cons, bind, Except.bind] at h
    split at h
    · cases h
    rename_i fx _
    split at h
    · cases h
    rename_i fxs hfxs
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have ih := List.mapM_except_ok_length (f := f) (l := xs) (ls := fxs) hfxs
    simp [_root_.List.length_cons, ih]

/-- Per-position correspondence for `List.mapM` in the `Except` monad. -/
theorem List.mapM_except_ok_getElem {α β ε : Type}
    {f : α → Except ε β} : ∀ {l : List α} {ls : List β}
    (h : l.mapM f = .ok ls)
    (i : Nat) (hi : i < l.length),
    f (l[i]'hi) = .ok (ls[i]'(by
      rw [List.mapM_except_ok_length h]; exact hi))
  | [], _, _, _, hi => by cases hi
  | x :: xs, ls, h, i, hi => by
    simp only [_root_.List.mapM_cons, bind, Except.bind] at h
    split at h
    · cases h
    rename_i fx hfx
    split at h
    · cases h
    rename_i fxs hfxs
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    cases i with
    | zero => simpa using hfx
    | succ j =>
      have hj : j < xs.length := by
        simp only [_root_.List.length_cons] at hi; omega
      have ih := List.mapM_except_ok_getElem (f := f) hfxs j hj
      simpa using ih

/-- Explicit-structure version of `step4Lower_constructor_shape`: when
`step4Lower` processes `(name, .constructor dt c)`, the resulting decls at
`name` is `.constructor cdt cc` where `cdt.constructors.length =
dt.constructors.length`, `cc.nameHead = c.nameHead`, and the inner
constructor `nameHead`s correspond positionally. -/
theorem step4Lower_constructor_step_explicit
    {acc : Concrete.Decls} {name : Global} {dt : DataType} {c : Constructor}
    {r : Concrete.Decls}
    (hstep : step4Lower acc (name, .constructor dt c) = .ok r) :
    ∃ cdt cc,
      r.getByKey name = some (.constructor cdt cc) ∧
      cdt.name = dt.name ∧
      cdt.constructors.length = dt.constructors.length ∧
      cc.nameHead = c.nameHead ∧
      (∀ i (hi : i < dt.constructors.length) (hi' : i < cdt.constructors.length),
        (cdt.constructors[i]'hi').nameHead = (dt.constructors[i]'hi).nameHead) ∧
      -- At any position i where dt.constructors[i] = c, the i-th cdt
      -- constructor equals cc.
      (∀ i (hi : i < dt.constructors.length) (hi' : i < cdt.constructors.length),
        (dt.constructors[i]'hi) = c → (cdt.constructors[i]'hi') = cc) ∧
      -- Exact ctors-list witness: cdt.constructors equals
      -- `dt.constructors.mapM (fun c' => …) = .ok …` for the deterministic
      -- step4Lower per-element function.
      (dt.constructors.mapM (fun c' => do
          let argTypes ← c'.argTypes.mapM
            (typToConcrete (∅ : Std.HashMap (Global × Array Typ) Global))
          pure ({ nameHead := c'.nameHead, argTypes } : Concrete.Constructor)))
        = .ok cdt.constructors ∧
      -- Exact argTypes-mapM witness: cc.argTypes = c.argTypes.mapM (typToConcrete ∅).ok.
      (c.argTypes.mapM
          (typToConcrete (∅ : Std.HashMap (Global × Array Typ) Global)))
        = .ok cc.argTypes := by
  unfold step4Lower at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · cases hstep
  rename_i ctors hctors
  split at hstep
  · cases hstep
  rename_i argTypes hargTypes
  simp only [Except.ok.injEq] at hstep
  subst hstep
  refine ⟨{ name := dt.name, constructors := ctors },
          { nameHead := c.nameHead, argTypes },
          IndexMap.getByKey_insert_self _ _ _,
          rfl, ?_, rfl, ?_, ?_, hctors, hargTypes⟩
  · exact List.mapM_except_ok_length hctors
  · intro i hi _hi'
    have hget := List.mapM_except_ok_getElem hctors i hi
    simp only [bind, Except.bind, pure, Except.pure] at hget
    split at hget
    · cases hget
    rename_i argTypes_i _
    simp only [Except.ok.injEq] at hget
    rw [← hget]
  · intro i hi _hi' hci
    have hget := List.mapM_except_ok_getElem hctors i hi
    simp only [bind, Except.bind, pure, Except.pure] at hget
    split at hget
    · cases hget
    rename_i argTypes_i hargTypes_i
    simp only [Except.ok.injEq] at hget
    rw [hci] at hargTypes_i
    rw [hargTypes] at hargTypes_i
    cases hargTypes_i
    rw [← hget, hci]

/-- `step4Lower` preserves `getByKey g` across an insertion at `name ≠ g`. -/
theorem step4Lower_preserves_other_key
    {acc : Concrete.Decls} {name : Global} {d : Typed.Declaration}
    {r : Concrete.Decls} {g : Global}
    (hstep : step4Lower acc (name, d) = .ok r) (hne_beq : (name == g) = false) :
    r.getByKey g = acc.getByKey g := by
  unfold step4Lower at hstep
  cases d with
  | function f =>
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · cases hstep
    split at hstep
    · cases hstep
    split at hstep
    · cases hstep
    simp only [Except.ok.injEq] at hstep
    subst hstep
    exact IndexMap.getByKey_insert_of_beq_false _ _ hne_beq
  | dataType dt =>
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · cases hstep
    simp only [Except.ok.injEq] at hstep
    subst hstep
    exact IndexMap.getByKey_insert_of_beq_false _ _ hne_beq
  | constructor dt c =>
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · cases hstep
    split at hstep
    · cases hstep
    simp only [Except.ok.injEq] at hstep
    subst hstep
    exact IndexMap.getByKey_insert_of_beq_false _ _ hne_beq

/-- If no element of `xs` has key `g`, then `foldlM step4Lower` preserves
`getByKey g`. -/
theorem step4Lower_foldlM_no_key_preserves
    {g : Global} :
    ∀ (xs : List (Global × Typed.Declaration))
      (_hne : ∀ p ∈ xs, (p.1 == g) = false)
      (init : Concrete.Decls) (result : Concrete.Decls),
      _root_.List.foldlM step4Lower init xs = .ok result →
      result.getByKey g = init.getByKey g
  | [], _, _, _, hfold => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
    subst hfold; rfl
  | hd :: tl, hne, init, result, hfold => by
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    cases hstep : step4Lower init hd with
    | error e => rw [hstep] at hfold; cases hfold
    | ok acc' =>
      rw [hstep] at hfold
      have hhd_ne : (hd.1 == g) = false := hne hd List.mem_cons_self
      have hacc' : acc'.getByKey g = init.getByKey g := by
        obtain ⟨name, d⟩ := hd
        exact step4Lower_preserves_other_key hstep hhd_ne
      have ih := step4Lower_foldlM_no_key_preserves tl
        (fun p hp => hne p (List.mem_cons_of_mem _ hp)) acc' result hfold
      rw [ih, hacc']

/-- Shape trace: if `monoDecls.getByKey g = some d_mono`, then `cd.getByKey g`
matches the kind of `d_mono`. -/
theorem step4Lower_fold_kind_at_key
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {d_mono : Typed.Declaration}
    (hget_mono : monoDecls.getByKey g = some d_mono)
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    (match d_mono with
     | .function _ => ∃ cf, concDecls.getByKey g = some (.function cf)
     | .dataType _ => ∃ cdt, concDecls.getByKey g = some (.dataType cdt)
     | .constructor _ _ => ∃ cdt c, concDecls.getByKey g = some (.constructor cdt c)) := by
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  have hmem : (g, d_mono) ∈ monoDecls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hget_mono
  -- Key uniqueness: every pair with key g equals (g, d_mono).
  have hunique : ∀ p ∈ monoDecls.pairs.toList,
      (p.1 == g) = true → p = (g, d_mono) := by
    intro p hp hpkey
    exact indexMap_pairs_key_unique _ hp hmem hpkey
  -- Split list at the first occurrence of (g, d_mono).
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  have huni' : ∀ p ∈ pre ++ (g, d_mono) :: post,
      (p.1 == g) = true → p = (g, d_mono) := by
    rw [← hsplit]; exact hunique
  have hpre_no_g : ∀ p ∈ pre, (p.1 == g) = false := by
    intro p hp
    rcases hpkey : (p.1 == g) with _ | _
    · rfl
    exfalso
    have hpkey_eq : (p.1 == g) = true := hpkey
    have hp_in_full : p ∈ pre ++ (g, d_mono) :: post := by
      rw [List.mem_append]; exact Or.inl hp
    have hp_eq_gdmono : p = (g, d_mono) := huni' p hp_in_full hpkey_eq
    have hgdm_in_pre : (g, d_mono) ∈ pre := hp_eq_gdmono ▸ hp
    obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hgdm_in_pre
    have hi_lt_full : i < monoDecls.pairs.toList.length := by
      rw [hsplit, List.length_append]
      exact Nat.lt_add_right _ hi_lt
    have hmid_lt_full : pre.length < monoDecls.pairs.toList.length := by
      rw [hsplit, List.length_append]
      exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
    have hlist_i_eq : monoDecls.pairs.toList[i]'hi_lt_full = (g, d_mono) := by
      rw [show monoDecls.pairs.toList[i]'hi_lt_full = (pre ++ (g, d_mono) :: post)[i]'(by
          rw [List.length_append]; exact Nat.lt_add_right _ hi_lt) from by
        congr 1 <;> exact hsplit]
      rw [List.getElem_append_left hi_lt]; exact hi_eq
    have hlist_mid_eq :
        monoDecls.pairs.toList[pre.length]'hmid_lt_full = (g, d_mono) := by
      rw [show monoDecls.pairs.toList[pre.length]'hmid_lt_full =
          (pre ++ (g, d_mono) :: post)[pre.length]'(by
            rw [List.length_append]
            exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
        congr 1 <;> exact hsplit]
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp
    have hkey_eq : ((monoDecls.pairs.toList[i]'hi_lt_full).1 ==
        (monoDecls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
      rw [hlist_i_eq, hlist_mid_eq]; simp
    have hij := indexMap_pairs_index_unique_of_key monoDecls hi_lt_full hmid_lt_full hkey_eq
    omega
  have hpost_no_g : ∀ p ∈ post, (p.1 == g) = false := by
    intro p hp
    rcases hpkey : (p.1 == g) with _ | _
    · rfl
    exfalso
    have hpkey_eq : (p.1 == g) = true := hpkey
    have hp_in_full : p ∈ pre ++ (g, d_mono) :: post := by
      rw [List.mem_append]
      exact Or.inr (List.mem_cons_of_mem _ hp)
    have hp_eq_gdmono : p = (g, d_mono) := huni' p hp_in_full hpkey_eq
    have hgdm_in_post : (g, d_mono) ∈ post := hp_eq_gdmono ▸ hp
    obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hgdm_in_post
    have hipost_lt_full : pre.length + (i + 1) < monoDecls.pairs.toList.length := by
      rw [hsplit, List.length_append]
      simp [List.length_cons]
      omega
    have hmid_lt_full : pre.length < monoDecls.pairs.toList.length := by
      rw [hsplit, List.length_append]
      exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
    have hlist_ipost :
        monoDecls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full = (g, d_mono) := by
      rw [show monoDecls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (pre ++ (g, d_mono) :: post)[pre.length + (i + 1)]'(by
            rw [List.length_append]; simp [List.length_cons]; omega) from by
        congr 1 <;> exact hsplit]
      rw [List.getElem_append_right (by omega : pre.length ≤ pre.length + (i + 1))]
      simp
      exact hi_eq
    have hlist_mid :
        monoDecls.pairs.toList[pre.length]'hmid_lt_full = (g, d_mono) := by
      rw [show monoDecls.pairs.toList[pre.length]'hmid_lt_full =
          (pre ++ (g, d_mono) :: post)[pre.length]'(by
            rw [List.length_append]
            exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
        congr 1 <;> exact hsplit]
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp
    have hkey_eq : ((monoDecls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full).1 ==
        (monoDecls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
      rw [hlist_ipost, hlist_mid]; simp
    have hij := indexMap_pairs_index_unique_of_key monoDecls hipost_lt_full hmid_lt_full hkey_eq
    omega
  -- Split the foldlM via hsplit.
  rw [hsplit] at hfold
  rw [List.foldlM_append] at hfold
  simp only [bind, Except.bind] at hfold
  cases hpre_res : _root_.List.foldlM step4Lower (default : Concrete.Decls) pre with
  | error e => rw [hpre_res] at hfold; cases hfold
  | ok acc_pre =>
    rw [hpre_res] at hfold
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    cases hstep_g : step4Lower acc_pre (g, d_mono) with
    | error e => rw [hstep_g] at hfold; cases hfold
    | ok acc_g =>
      rw [hstep_g] at hfold
      have hpost_preserve :=
        step4Lower_foldlM_no_key_preserves post hpost_no_g acc_g concDecls hfold
      rw [hpost_preserve]
      cases d_mono with
      | function f =>
        obtain ⟨cf, hcf⟩ := step4Lower_function_shape hstep_g
        exact ⟨cf, hcf⟩
      | dataType dt =>
        obtain ⟨cdt, hcdt⟩ := step4Lower_dataType_shape hstep_g
        exact ⟨cdt, hcdt⟩
      | constructor dt c =>
        obtain ⟨cdt, cc, hcc⟩ := step4Lower_constructor_shape hstep_g
        exact ⟨cdt, cc, hcc⟩

/-- Explicit-structure version of `step4Lower_constructor_shape` lifted to the
full `foldlM`: when `monoDecls.getByKey g = some (.constructor md_dt md_c)`
and the fold succeeds, the resulting `concDecls` at `g` is
`.constructor cd_dt cd_c` where `cd_dt.constructors.length =
md_dt.constructors.length`, `cd_c.nameHead = md_c.nameHead`, and inner
constructor `nameHead`s correspond positionally. -/
theorem step4Lower_constructor_explicit
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {md_dt : DataType} {md_c : Constructor}
    (hget : monoDecls.getByKey g = some (.constructor md_dt md_c))
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∃ cd_dt cd_c,
      concDecls.getByKey g = some (.constructor cd_dt cd_c) ∧
      cd_dt.name = md_dt.name ∧
      cd_dt.constructors.length = md_dt.constructors.length ∧
      cd_c.nameHead = md_c.nameHead ∧
      (∀ i (hi : i < md_dt.constructors.length)
          (hi' : i < cd_dt.constructors.length),
        (cd_dt.constructors[i]'hi').nameHead =
          (md_dt.constructors[i]'hi).nameHead) ∧
      -- At any position i where md_dt.constructors[i] = md_c, cd_dt.constructors[i] = cd_c.
      (∀ i (hi : i < md_dt.constructors.length)
          (hi' : i < cd_dt.constructors.length),
        (md_dt.constructors[i]'hi) = md_c → (cd_dt.constructors[i]'hi') = cd_c) ∧
      -- Exact ctors-list witness for cross-arm comparison (D4 closure).
      (md_dt.constructors.mapM (fun c' => do
          let argTypes ← c'.argTypes.mapM
            (typToConcrete (∅ : Std.HashMap (Global × Array Typ) Global))
          pure ({ nameHead := c'.nameHead, argTypes } : Concrete.Constructor)))
        = .ok cd_dt.constructors ∧
      -- Exact argTypes mapM witness for the .ctor entry.
      (md_c.argTypes.mapM
          (typToConcrete (∅ : Std.HashMap (Global × Array Typ) Global)))
        = .ok cd_c.argTypes := by
  -- Replay `step4Lower_fold_kind_at_key`'s splitting strategy to find the
  -- intermediate accumulator `acc_g` from which the (g, .constructor md_dt md_c)
  -- step is taken, then apply `step4Lower_constructor_step_explicit`.
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  have hmem : (g, Typed.Declaration.constructor md_dt md_c) ∈ monoDecls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hget
  have hunique : ∀ p ∈ monoDecls.pairs.toList,
      (p.1 == g) = true → p = (g, .constructor md_dt md_c) := by
    intro p hp hpkey
    exact indexMap_pairs_key_unique _ hp hmem hpkey
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  have huni' : ∀ p ∈ pre ++ (g, .constructor md_dt md_c) :: post,
      (p.1 == g) = true → p = (g, .constructor md_dt md_c) := by
    rw [← hsplit]; exact hunique
  have hpost_no_g : ∀ p ∈ post, (p.1 == g) = false := by
    intro p hp
    rcases hpkey : (p.1 == g) with _ | _
    · rfl
    exfalso
    have hpkey_eq : (p.1 == g) = true := hpkey
    have hp_in_full : p ∈ pre ++ (g, .constructor md_dt md_c) :: post := by
      rw [List.mem_append]
      exact Or.inr (List.mem_cons_of_mem _ hp)
    have hp_eq := huni' p hp_in_full hpkey_eq
    have hgdm_in_post : (g, Typed.Declaration.constructor md_dt md_c) ∈ post :=
      hp_eq ▸ hp
    obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hgdm_in_post
    have hipost_lt_full : pre.length + (i + 1) < monoDecls.pairs.toList.length := by
      rw [hsplit, List.length_append]; simp [List.length_cons]; omega
    have hmid_lt_full : pre.length < monoDecls.pairs.toList.length := by
      rw [hsplit, List.length_append]
      exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
    have hlist_ipost :
        monoDecls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (g, .constructor md_dt md_c) := by
      rw [show monoDecls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (pre ++ (g, .constructor md_dt md_c) :: post)[pre.length + (i + 1)]'(by
            rw [List.length_append]; simp [List.length_cons]; omega) from by
        congr 1 <;> exact hsplit]
      rw [List.getElem_append_right (by omega : pre.length ≤ pre.length + (i + 1))]
      simp; exact hi_eq
    have hlist_mid :
        monoDecls.pairs.toList[pre.length]'hmid_lt_full =
          (g, .constructor md_dt md_c) := by
      rw [show monoDecls.pairs.toList[pre.length]'hmid_lt_full =
          (pre ++ (g, .constructor md_dt md_c) :: post)[pre.length]'(by
            rw [List.length_append]
            exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
        congr 1 <;> exact hsplit]
      rw [List.getElem_append_right (Nat.le_refl _)]; simp
    have hkey_eq : ((monoDecls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full).1 ==
        (monoDecls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
      rw [hlist_ipost, hlist_mid]; simp
    have hij := indexMap_pairs_index_unique_of_key monoDecls hipost_lt_full hmid_lt_full hkey_eq
    omega
  rw [hsplit] at hfold
  rw [List.foldlM_append] at hfold
  simp only [bind, Except.bind] at hfold
  cases hpre_res : _root_.List.foldlM step4Lower (default : Concrete.Decls) pre with
  | error _ => rw [hpre_res] at hfold; cases hfold
  | ok acc_pre =>
    rw [hpre_res] at hfold
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    cases hstep_g : step4Lower acc_pre (g, .constructor md_dt md_c) with
    | error _ => rw [hstep_g] at hfold; cases hfold
    | ok acc_g =>
      rw [hstep_g] at hfold
      have hpost_preserve :=
        step4Lower_foldlM_no_key_preserves post hpost_no_g acc_g concDecls hfold
      obtain ⟨cdt, cc, hg_acc, hname, hlen, hch, hperpos, hpos_eq, hctors, hargTypes⟩ :=
        step4Lower_constructor_step_explicit hstep_g
      refine ⟨cdt, cc, ?_, hname, hlen, hch, hperpos, hpos_eq, hctors, hargTypes⟩
      rw [hpost_preserve]; exact hg_acc

/-- Explicit-structure version of `step4Lower_dataType_shape`: when
`step4Lower` processes `(name, .dataType dt)`, the resulting decls at `name`
is `.dataType cdt` where `cdt.constructors.length = dt.constructors.length`
and inner constructor `nameHead`s correspond positionally. -/
theorem step4Lower_dataType_step_explicit
    {acc : Concrete.Decls} {name : Global} {dt : DataType}
    {r : Concrete.Decls}
    (hstep : step4Lower acc (name, .dataType dt) = .ok r) :
    ∃ cdt,
      r.getByKey name = some (.dataType cdt) ∧
      cdt.name = dt.name ∧
      cdt.constructors.length = dt.constructors.length ∧
      (∀ i (hi : i < dt.constructors.length) (hi' : i < cdt.constructors.length),
        (cdt.constructors[i]'hi').nameHead = (dt.constructors[i]'hi).nameHead) ∧
      -- Exact ctors-list witness for cross-arm comparison (D4 closure).
      (dt.constructors.mapM (fun c => do
          let argTypes ← c.argTypes.mapM
            (typToConcrete (∅ : Std.HashMap (Global × Array Typ) Global))
          pure ({ nameHead := c.nameHead, argTypes } : Concrete.Constructor)))
        = .ok cdt.constructors := by
  unfold step4Lower at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · cases hstep
  rename_i ctors hctors
  simp only [Except.ok.injEq] at hstep
  subst hstep
  refine ⟨{ name := dt.name, constructors := ctors },
          IndexMap.getByKey_insert_self _ _ _,
          rfl,
          ?_, ?_, hctors⟩
  · exact List.mapM_except_ok_length hctors
  · intro i hi _hi'
    have hget := List.mapM_except_ok_getElem hctors i hi
    simp only [bind, Except.bind, pure, Except.pure] at hget
    split at hget
    · cases hget
    rename_i argTypes_i _
    simp only [Except.ok.injEq] at hget
    rw [← hget]

/-- Explicit-structure version of `step4Lower_dataType_shape` lifted to the
full `foldlM`: when `monoDecls.getByKey g = some (.dataType md_dt)` and the
fold succeeds, the resulting `concDecls` at `g` is `.dataType cdt` with
length and per-position nameHead correspondence to `md_dt`. -/
theorem step4Lower_dataType_explicit
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {md_dt : DataType}
    (hget : monoDecls.getByKey g = some (.dataType md_dt))
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∃ cdt,
      concDecls.getByKey g = some (.dataType cdt) ∧
      cdt.name = md_dt.name ∧
      cdt.constructors.length = md_dt.constructors.length ∧
      (∀ i (hi : i < md_dt.constructors.length)
          (hi' : i < cdt.constructors.length),
        (cdt.constructors[i]'hi').nameHead =
          (md_dt.constructors[i]'hi).nameHead) ∧
      -- Exact ctors-list witness for cross-arm comparison (D4 closure).
      (md_dt.constructors.mapM (fun c => do
          let argTypes ← c.argTypes.mapM
            (typToConcrete (∅ : Std.HashMap (Global × Array Typ) Global))
          pure ({ nameHead := c.nameHead, argTypes } : Concrete.Constructor)))
        = .ok cdt.constructors := by
  -- Replay `step4Lower_constructor_explicit`'s splitting strategy to find the
  -- intermediate accumulator `acc_g` from which the (g, .dataType md_dt) step
  -- is taken, then apply `step4Lower_dataType_step_explicit`.
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  have hmem : (g, Typed.Declaration.dataType md_dt) ∈ monoDecls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hget
  have hunique : ∀ p ∈ monoDecls.pairs.toList,
      (p.1 == g) = true → p = (g, .dataType md_dt) := by
    intro p hp hpkey
    exact indexMap_pairs_key_unique _ hp hmem hpkey
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  have huni' : ∀ p ∈ pre ++ (g, .dataType md_dt) :: post,
      (p.1 == g) = true → p = (g, .dataType md_dt) := by
    rw [← hsplit]; exact hunique
  have hpost_no_g : ∀ p ∈ post, (p.1 == g) = false := by
    intro p hp
    rcases hpkey : (p.1 == g) with _ | _
    · rfl
    exfalso
    have hpkey_eq : (p.1 == g) = true := hpkey
    have hp_in_full : p ∈ pre ++ (g, .dataType md_dt) :: post := by
      rw [List.mem_append]
      exact Or.inr (List.mem_cons_of_mem _ hp)
    have hp_eq := huni' p hp_in_full hpkey_eq
    have hgdm_in_post : (g, Typed.Declaration.dataType md_dt) ∈ post :=
      hp_eq ▸ hp
    obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hgdm_in_post
    have hipost_lt_full : pre.length + (i + 1) < monoDecls.pairs.toList.length := by
      rw [hsplit, List.length_append]; simp [List.length_cons]; omega
    have hmid_lt_full : pre.length < monoDecls.pairs.toList.length := by
      rw [hsplit, List.length_append]
      exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
    have hlist_ipost :
        monoDecls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (g, .dataType md_dt) := by
      rw [show monoDecls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (pre ++ (g, .dataType md_dt) :: post)[pre.length + (i + 1)]'(by
            rw [List.length_append]; simp [List.length_cons]; omega) from by
        congr 1 <;> exact hsplit]
      rw [List.getElem_append_right (by omega : pre.length ≤ pre.length + (i + 1))]
      simp; exact hi_eq
    have hlist_mid :
        monoDecls.pairs.toList[pre.length]'hmid_lt_full =
          (g, .dataType md_dt) := by
      rw [show monoDecls.pairs.toList[pre.length]'hmid_lt_full =
          (pre ++ (g, .dataType md_dt) :: post)[pre.length]'(by
            rw [List.length_append]
            exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
        congr 1 <;> exact hsplit]
      rw [List.getElem_append_right (Nat.le_refl _)]; simp
    have hkey_eq : ((monoDecls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full).1 ==
        (monoDecls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
      rw [hlist_ipost, hlist_mid]; simp
    have hij := indexMap_pairs_index_unique_of_key monoDecls hipost_lt_full hmid_lt_full hkey_eq
    omega
  rw [hsplit] at hfold
  rw [List.foldlM_append] at hfold
  simp only [bind, Except.bind] at hfold
  cases hpre_res : _root_.List.foldlM step4Lower (default : Concrete.Decls) pre with
  | error _ => rw [hpre_res] at hfold; cases hfold
  | ok acc_pre =>
    rw [hpre_res] at hfold
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    cases hstep_g : step4Lower acc_pre (g, .dataType md_dt) with
    | error _ => rw [hstep_g] at hfold; cases hfold
    | ok acc_g =>
      rw [hstep_g] at hfold
      have hpost_preserve :=
        step4Lower_foldlM_no_key_preserves post hpost_no_g acc_g concDecls hfold
      obtain ⟨cdt, hg_acc, hname, hlen, hperpos, hctors⟩ :=
        step4Lower_dataType_step_explicit hstep_g
      refine ⟨cdt, ?_, hname, hlen, hperpos, hctors⟩
      rw [hpost_preserve]; exact hg_acc

/-- Explicit-structure version of `step4Lower_function_shape`: when
`step4Lower` processes `(name, .function md_f)`, the resulting decls at
`name` is `.function cf` where `cf.inputs`/`cf.output` are derivable from
`md_f.inputs`/`md_f.output` via `typToConcrete` with empty mono. -/
theorem step4Lower_function_step_explicit
    {acc : Concrete.Decls} {name : Global} {md_f : Typed.Function}
    {r : Concrete.Decls}
    (hstep : step4Lower acc (name, .function md_f) = .ok r) :
    ∃ cf,
      r.getByKey name = some (.function cf) ∧
      cf.name = md_f.name ∧
      (md_f.inputs.mapM (fun (p : Local × Typ) => do
          let t' ← typToConcrete (∅ : Std.HashMap (Global × Array Typ) Global) p.2
          pure (p.1, t'))) = .ok cf.inputs ∧
      typToConcrete (∅ : Std.HashMap (Global × Array Typ) Global) md_f.output
        = .ok cf.output := by
  unfold step4Lower at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · cases hstep
  rename_i inputs hinputs
  split at hstep
  · cases hstep
  rename_i output houtput
  split at hstep
  · cases hstep
  rename_i body _
  simp only [Except.ok.injEq] at hstep
  subst hstep
  refine ⟨{ name := md_f.name, inputs, output, body, entry := md_f.entry },
          IndexMap.getByKey_insert_self _ _ _, rfl, ?_, houtput⟩
  exact hinputs

/-- Lifted to the full `foldlM`: when `monoDecls.getByKey g = some (.function md_f)`
and the fold succeeds, the resulting `concDecls` at `g` is `.function cf` with
the typToConcrete witnesses for inputs/output. -/
theorem step4Lower_function_explicit
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {md_f : Typed.Function}
    (hget : monoDecls.getByKey g = some (.function md_f))
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∃ cf,
      concDecls.getByKey g = some (.function cf) ∧
      cf.name = md_f.name ∧
      (md_f.inputs.mapM (fun (p : Local × Typ) => do
          let t' ← typToConcrete (∅ : Std.HashMap (Global × Array Typ) Global) p.2
          pure (p.1, t'))) = .ok cf.inputs ∧
      typToConcrete (∅ : Std.HashMap (Global × Array Typ) Global) md_f.output
        = .ok cf.output := by
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  have hmem : (g, Typed.Declaration.function md_f) ∈ monoDecls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hget
  have hunique : ∀ p ∈ monoDecls.pairs.toList,
      (p.1 == g) = true → p = (g, .function md_f) := by
    intro p hp hpkey
    exact indexMap_pairs_key_unique _ hp hmem hpkey
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  have huni' : ∀ p ∈ pre ++ (g, .function md_f) :: post,
      (p.1 == g) = true → p = (g, .function md_f) := by
    rw [← hsplit]; exact hunique
  have hpost_no_g : ∀ p ∈ post, (p.1 == g) = false := by
    intro p hp
    rcases hpkey : (p.1 == g) with _ | _
    · rfl
    exfalso
    have hpkey_eq : (p.1 == g) = true := hpkey
    have hp_in_full : p ∈ pre ++ (g, .function md_f) :: post := by
      rw [List.mem_append]
      exact Or.inr (List.mem_cons_of_mem _ hp)
    have hp_eq := huni' p hp_in_full hpkey_eq
    have hgdm_in_post : (g, Typed.Declaration.function md_f) ∈ post :=
      hp_eq ▸ hp
    obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hgdm_in_post
    have hipost_lt_full : pre.length + (i + 1) < monoDecls.pairs.toList.length := by
      rw [hsplit, List.length_append]; simp [List.length_cons]; omega
    have hmid_lt_full : pre.length < monoDecls.pairs.toList.length := by
      rw [hsplit, List.length_append]
      exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
    have hlist_ipost :
        monoDecls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (g, .function md_f) := by
      rw [show monoDecls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (pre ++ (g, .function md_f) :: post)[pre.length + (i + 1)]'(by
            rw [List.length_append]; simp [List.length_cons]; omega) from by
        congr 1 <;> exact hsplit]
      rw [List.getElem_append_right (by omega : pre.length ≤ pre.length + (i + 1))]
      simp; exact hi_eq
    have hlist_mid :
        monoDecls.pairs.toList[pre.length]'hmid_lt_full =
          (g, .function md_f) := by
      rw [show monoDecls.pairs.toList[pre.length]'hmid_lt_full =
          (pre ++ (g, .function md_f) :: post)[pre.length]'(by
            rw [List.length_append]
            exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
        congr 1 <;> exact hsplit]
      rw [List.getElem_append_right (Nat.le_refl _)]; simp
    have hkey_eq : ((monoDecls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full).1 ==
        (monoDecls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
      rw [hlist_ipost, hlist_mid]; simp
    have hij := indexMap_pairs_index_unique_of_key monoDecls hipost_lt_full hmid_lt_full hkey_eq
    omega
  rw [hsplit] at hfold
  rw [List.foldlM_append] at hfold
  simp only [bind, Except.bind] at hfold
  cases hpre_res : _root_.List.foldlM step4Lower (default : Concrete.Decls) pre with
  | error _ => rw [hpre_res] at hfold; cases hfold
  | ok acc_pre =>
    rw [hpre_res] at hfold
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    cases hstep_g : step4Lower acc_pre (g, .function md_f) with
    | error _ => rw [hstep_g] at hfold; cases hfold
    | ok acc_g =>
      rw [hstep_g] at hfold
      have hpost_preserve :=
        step4Lower_foldlM_no_key_preserves post hpost_no_g acc_g concDecls hfold
      obtain ⟨cf, hg_acc, hname, hinputs, houtput⟩ :=
        step4Lower_function_step_explicit hstep_g
      refine ⟨cf, ?_, hname, hinputs, houtput⟩
      rw [hpost_preserve]; exact hg_acc


end Aiur

end -- public section
