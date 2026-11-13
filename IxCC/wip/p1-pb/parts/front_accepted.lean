  unfold front at h
  simp only [bind, Except.bind, Except.mapError] at h
  cases hm : checkMidCert c.mid with
  | error e => simp [hm] at h
  | ok u =>
    simp only [hm] at h
    cases htab : Src.Table.ofCert cfg.table P c.table with
    | error e => simp [htab] at h
    | ok table =>
      simp only [htab] at h
      have hkeys : checkRelevanceKeys P c.relevance = .ok () := by
        cases hk : checkRelevanceKeys P c.relevance with
        | error e => simp [hk] at h
        | ok u => cases u; rfl
      simp only [hkeys] at h
      cases hann : Src.Recheck.annotation { P with table } c.relevance with
      | error err =>
        rw [hann] at h
        cases err <;> cases h
      | ok res =>
        rw [hann] at h
        cases h
        unfold Src.Recheck.annotation at hann
        cases hinst : Src.Relevance.install { P with table } c.relevance with
        | error e => simp [hinst] at hann
        | ok installed =>
          simp only [hinst] at hann
          cases hchk : Src.Relevance.check installed c.relevance with
          | error errs =>
            rw [hchk] at hann
            cases hann
          | ok chk =>
            rw [hchk] at hann
            dsimp only at hann
            split at hann
            · cases hann
            · rename_i hne
              cases hann
              refine ⟨installed, hchk, ?_, rfl⟩
              simpa using hne
