import IxVMRefinement.Assembly.GroupedInstall

/-! # Installing reader declarations from selected final constants

The order used to establish a model need not be the reader's order. Once the final constants
are known, their stored representations and distinct names suffice to construct the public
syntactic installation relation in the reader's order.
-/

namespace IxVM.Refinement.Assembly

/-- A declaration's selected final constants, including any auxiliary constants assigned to it. -/
def InstallChunk (d : Ix.Kernel.Declaration .anon)
    (chunk : List (Ix.Kernel.ConstantInfo .anon)) : Prop :=
  (∀ ci₀ ∈ IxVM.Consistency.installs d,
    ∃ ci ∈ chunk, IxVM.Consistency.StoredAs ci ci₀) ∧
  (∀ ci ∈ chunk,
    (∃ ci₀ ∈ IxVM.Consistency.installs d, ci₀.name = ci.name) ∨
      ∃ k auxTag, ci.name = .aux k auxTag)

/-- Append selected chunks to an existing installation. Freshness is required only against
the starting environment; distinctness of all selected names supplies freshness thereafter. -/
theorem installs_append_chunks
    {ds : List (Ix.Kernel.Declaration .anon)}
    {chunks : List (List (Ix.Kernel.ConstantInfo .anon))}
    (hchunks : List.Forall₂ InstallChunk ds chunks) :
    ∀ {before : List (Ix.Kernel.Declaration .anon)} {env : Ix.Kernel.Env .anon},
      IxVM.Consistency.Installs before env →
      (chunks.flatten.map (·.name)).Nodup →
      (∀ ci ∈ chunks.flatten, env.find? ci.name = none) →
      IxVM.Consistency.Installs (before ++ ds) ⟨chunks.reverse.flatten ++ env.consts⟩ := by
  induction hchunks with
  | nil =>
    intro before env hinst _ _
    simpa using hinst
  | @cons d chunk ds chunks hchunk hchunks ih =>
    intro before env hinst hnd hfresh
    simp only [List.flatten_cons, List.map_append, List.nodup_append] at hnd
    let env₁ : Ix.Kernel.Env .anon := ⟨chunk ++ env.consts⟩
    have hstep : IxVM.Consistency.InstallStep env d env₁ :=
      ⟨chunk, rfl, hnd.1,
        fun ci hci => hfresh ci (List.mem_append_left _ hci), hchunk.1, hchunk.2⟩
    have htail_fresh : ∀ ci ∈ chunks.flatten, env₁.find? ci.name = none := by
      intro ci hci
      have hnone : chunk.find? (·.name == ci.name) = none := by
        apply List.find?_eq_none.mpr
        intro head hhead hmatch
        exact hnd.2.2 head.name
          (List.mem_map.mpr ⟨head, hhead, rfl⟩) ci.name
          (List.mem_map.mpr ⟨ci, hci, rfl⟩) (eq_of_beq hmatch)
      change (chunk ++ env.consts).find? (·.name == ci.name) = none
      rw [List.find?_append, hnone]
      exact hfresh ci (List.mem_append_right _ hci)
    have hrest := ih (IxVM.Consistency.Installs.snoc hinst hstep) hnd.2.1 htail_fresh
    simpa [env₁, List.reverse_cons, List.flatten_append, List.append_assoc] using hrest

/-- A complete syntactic installation in the chosen declaration order, obtained from
matching chunks of final constants with distinct names. -/
theorem installs_of_chunks
    {ds : List (Ix.Kernel.Declaration .anon)}
    {chunks : List (List (Ix.Kernel.ConstantInfo .anon))}
    (hchunks : List.Forall₂ InstallChunk ds chunks)
    (hnd : (chunks.flatten.map (·.name)).Nodup) :
    IxVM.Consistency.Installs ds ⟨chunks.reverse.flatten⟩ := by
  have h := installs_append_chunks hchunks IxVM.Consistency.Installs.nil hnd
    (fun _ _ => rfl)
  simpa using h

end IxVM.Refinement.Assembly
