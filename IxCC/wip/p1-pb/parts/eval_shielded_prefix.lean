  have hmk := mkApps_spineL t
  rw [hsp] at hmk
  rw [← hmk, eval_mkApps, eval_var_of p k ls ρ hs] at he
  obtain ⟨v0, hv0, he⟩ := bind_ok_inv he
  subst hlen
  exact applySpine_ignoresSlot hig hv0 he
