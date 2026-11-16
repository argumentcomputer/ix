import IxVMRefinement.Assembly.AdmittedBare

/-! # Prepared bare role declarations are covered by the checked full preparation -/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader Ix.Kernel.Frontend

private theorem pickSpec_input_member {md : Mode} (key : Option (Key md)) :
    ∀ {input : List (Declaration md)} {decl : Declaration md}, decl ∈ input →
      (pickSpec key input).1 = some decl ∨ decl ∈ (pickSpec key input).2
  | [], _, member => by cases member
  | first :: rest, decl, member => by
    simp only [pickSpec]
    split
    · rcases List.mem_cons.mp member with rfl | later
      · exact Or.inl rfl
      · exact Or.inr later
    · rcases List.mem_cons.mp member with rfl | later
      · exact Or.inr List.mem_cons_self
      · rcases pickSpec_input_member key later with selected | retained
        · exact Or.inl selected
        · exact Or.inr (List.mem_cons_of_mem _ retained)

private theorem frontSpec_input_member {md : Mode} :
    ∀ (prelude input : List (Declaration md)) {decl : Declaration md}, decl ∈ input →
      decl ∈ (frontSpec prelude input).1 ++ (frontSpec prelude input).2
  | [], _, _, member => member
  | first :: rest, input, decl, member => by
    rcases pickSpec_input_member (preludeKey first) member with selected | retained
    · simp [frontSpec, selected]
    · exact List.mem_cons_of_mem _ (frontSpec_input_member rest _ retained)

private theorem pickSpec_filter (keep : Declaration md → Bool) (key : Option (Key md))
    (hkeep : ∀ d, declares key d = true → keep d = true) :
    ∀ ds : List (Declaration md),
      pickSpec key (ds.filter keep) = ((pickSpec key ds).1, (pickSpec key ds).2.filter keep)
  | [] => rfl
  | d :: ds => by
    by_cases hdeclares : declares key d = true
    · simp [pickSpec, hdeclares, hkeep d hdeclares]
    · have hdeclares' := Bool.eq_false_iff.mpr hdeclares
      cases hk : keep d <;>
        simp [pickSpec, hdeclares', hk, pickSpec_filter keep key hkeep ds]

private theorem frontSpec_filter (keep : Declaration md → Bool) :
    ∀ (ps ds : List (Declaration md)),
      (∀ p ∈ ps, ∀ d, declares (preludeKey p) d = true → keep d = true) →
      frontSpec ps (ds.filter keep) = ((frontSpec ps ds).1, (frontSpec ps ds).2.filter keep)
  | [], _, _ => rfl
  | p :: ps, ds, hkeep => by
    have hpick := pickSpec_filter keep (preludeKey p) (hkeep p List.mem_cons_self) ds
    have hrest := frontSpec_filter keep ps (pickSpec (preludeKey p) ds).2
      (fun p' hp' => hkeep p' (List.mem_cons_of_mem p hp'))
    simp only [frontSpec, hpick, hrest]

private theorem declared_prelude_notGenerated {p d : Declaration md}
    (hnames : ∀ k ∈ p.names, NonAuxKey k) (hd : declares (preludeKey p) d = true) :
    (!d.isGenerated) = true := by
  cases hp : preludeKey p with
  | none => simp [declares, hp] at hd
  | some k =>
    have hk : k ∈ p.names := List.mem_of_head? hp
    have hmember : k ∈ d.names := by
      simpa only [declares, hp, Option.any_some, List.contains_iff_mem] using hd
    cases hg : d.isGenerated with
    | false => rfl
    | true =>
      have hkAux : k.isAux = true := by
        simp only [Declaration.isGenerated, Bool.and_eq_true] at hg
        exact List.all_eq_true.mp hg.2 k hmember
      rw [isAux_eq_false_iff.mpr (hnames k hk)] at hkAux
      cases hkAux

private theorem preparePrelude_mem_spec (pre : PreludeIx md) (ds : Array (Declaration md))
    (d : Declaration md) :
    d ∈ (preparePrelude pre ds).toList ↔
      d ∈ (frontSpec pre.decls.toList ds.toList).1 ++ (frontSpec pre.decls.toList ds.toList).2 := by
  have hperm : (preparePrelude pre ds).toList.Perm
      ((frontSpec pre.decls.toList ds.toList).1 ++ (frontSpec pre.decls.toList ds.toList).2) := by
    rw [preparePrelude_front, Array.toList_append]
    have hh := List.Perm.append_left (frontOf #[] pre.decls.toList ds).1.toList
      (hoistNatOpGround_perm (frontOf #[] pre.decls.toList ds).2)
    obtain ⟨hfront, hrest⟩ := frontOf_toList pre.decls.toList #[] ds
    rw [hfront, hrest] at hh
    simpa [hfront] using hh
  exact hperm.mem_iff

/-- Prelude preparation selects the input's own declarations where present and only
permutes the remaining input. Every input declaration is retained in the prepared stream. -/
theorem preparePrelude_input_subset (pre : PreludeIx md) (input : Array (Declaration md)) :
    ∀ decl ∈ input.toList, decl ∈ (preparePrelude pre input).toList := by
  intro decl member
  exact (preparePrelude_mem_spec pre input decl).mpr
    (frontSpec_input_member pre.decls.toList input.toList member)

/-- Filtering generated declarations leaves the prelude's selected copies unchanged;
the later hoist only permutes declarations. Thus the full preparation covers the bare one. -/
theorem preparePrelude_filter_subset {pre : PreludeIx md} {full bare : Array (Declaration md)}
    (hpre : ∀ p ∈ pre.decls.toList, ∀ k ∈ p.names, NonAuxKey k)
    (hfilter : full.toList.filter (fun d => !d.isGenerated) = bare.toList) :
    ∀ d ∈ (preparePrelude pre bare).toList, d ∈ (preparePrelude pre full).toList := by
  have hfront := frontSpec_filter (fun d => !d.isGenerated) pre.decls.toList full.toList
    (fun p hp d hd => declared_prelude_notGenerated (hpre p hp) hd)
  intro d hd
  apply (preparePrelude_mem_spec pre full d).mpr
  have hmem := (preparePrelude_mem_spec pre bare d).mp hd
  rw [← hfilter, hfront] at hmem
  simp only [List.mem_append] at hmem ⊢
  exact hmem.imp_right fun hm => (List.mem_filter.mp hm).1

/-- The original full role preparation accepted by the public witness covers each
declaration of its concrete bare preparation. -/
theorem admitted_prepared_bare_covered
    {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : IxVM.Consistency.ReaderAdmissionWitness V b) {bare : Array (Declaration .anon)}
    (hfilter : w.fullDecls.toList.filter (fun d => !d.isGenerated) = bare.toList) :
    ∀ d ∈ (preparePrelude w.prelude.ix bare).toList,
      d ∈ (preparePrelude w.prelude.ix w.fullDecls).toList := by
  apply preparePrelude_filter_subset _ hfilter
  intro p hp k hk
  obtain ⟨role, _, hrole⟩ := (preludeFor_decls_roles w.preludeRead).2 p hp k hk
  rw [hrole]
  intro _ _ heq
  cases heq

/-- Removing generated declarations preserves any established uniqueness of the keys
contributed by the full prepared declarations. This also accounts for hoisting order. -/
theorem preparePrelude_filter_nodup {α : Type} (keys : Declaration md → List α)
    {pre : PreludeIx md} {full bare : Array (Declaration md)}
    (hpre : ∀ p ∈ pre.decls.toList, ∀ k ∈ p.names, NonAuxKey k)
    (hfilter : full.toList.filter (fun d => !d.isGenerated) = bare.toList)
    (hfull : ((preparePrelude pre full).toList.flatMap keys).Nodup) :
    ((preparePrelude pre bare).toList.flatMap keys).Nodup := by
  have perm (ds : Array (Declaration md)) : (preparePrelude pre ds).toList.Perm
      ((frontSpec pre.decls.toList ds.toList).1 ++ (frontSpec pre.decls.toList ds.toList).2) := by
    rw [preparePrelude_front, Array.toList_append]
    have hh := List.Perm.append_left (frontOf #[] pre.decls.toList ds).1.toList
      (hoistNatOpGround_perm (frontOf #[] pre.decls.toList ds).2)
    obtain ⟨hfront, hrest⟩ := frontOf_toList pre.decls.toList #[] ds
    rw [hfront, hrest] at hh
    simpa [hfront] using hh
  have hfront := frontSpec_filter (fun d => !d.isGenerated) pre.decls.toList full.toList
    (fun p hp d hd => declared_prelude_notGenerated (hpre p hp) hd)
  have hsub :
      ((frontSpec pre.decls.toList bare.toList).1 ++
        (frontSpec pre.decls.toList bare.toList).2).Sublist
      ((frontSpec pre.decls.toList full.toList).1 ++
        (frontSpec pre.decls.toList full.toList).2) := by
    rw [← hfilter, hfront]
    exact (List.Sublist.refl _).append List.filter_sublist
  apply (List.Perm.flatMap_right keys (perm bare)).nodup_iff.mpr
  exact ((List.Perm.flatMap_right keys (perm full)).nodup_iff.mp hfull).sublist (hsub.flatMap keys)

end IxVM.Refinement.Assembly
