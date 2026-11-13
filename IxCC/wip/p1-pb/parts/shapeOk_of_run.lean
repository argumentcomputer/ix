  obtain ⟨-, ⟨st, he⟩, -⟩ := runLir_spec (run_parts h).1
  have hwf := Lam.Erase.Proof.erase_progWF he
  refine ⟨fun c c' sf sf' lv lv' ind j np np' nf nf' ty ty' hc hc' => ?_⟩
  have h1 := hwf.ctorIn (c := c) (sf := sf) (lv := lv) (ind := ind) (cidx := j) (np := np) (nf := nf)
    (ty := ty) hc
  have h2 := hwf.ctorIn (c := c') (sf := sf') (lv := lv') (ind := ind) (cidx := j) (np := np')
    (nf := nf') (ty := ty') hc'
  exact Option.some.inj (h1.symm.trans h2)
