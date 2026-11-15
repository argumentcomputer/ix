import IxVMRefinement.Assembly.AdmittedBare

/-! # Prepared bare role declarations are covered by the checked full preparation -/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader Ix.Kernel.Frontend

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
    simpa using hh
  exact hperm.mem_iff

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

end IxVM.Refinement.Assembly
