  rintro ⟨k, hgw | ⟨v, hv, hview⟩⟩
  · exact ⟨k, .inl hgw⟩
  · refine ⟨k, .inr ⟨v, hv, ?_, hview⟩⟩
    obtain ⟨hfr, -, -⟩ := runLir_spec (run_parts h).1
    obtain ⟨installed, hchk, hcan, hsrc⟩ := front_accepted hfr
    have hf : Facts a.src c.relevance a.checked := by
      have := facts_modeEq hchk hcan (Src.Lazify.run_modeEq installed a.checked.keys)
      rw [show a.src = a.front.src from rfl, hsrc]
      exact this
    change Lam.Erase.Proof.srcRun ⟨a.src, a.checked⟩ i k = .ok v at hv
    unfold Lam.Erase.Proof.srcRun at hv
    split at hv
    · rename_i x root hr
      obtain ⟨w, hw, hwv⟩ := bind_ok_inv hv
      cases hwv
      exact run_live hf (shapeOk_of_run h) ⟨x, List.mem_of_getElem? hr⟩
        (hsa k root (by simp [Artifact.front, hr])) hw
    · cases hv
