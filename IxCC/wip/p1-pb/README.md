# P1, engineer PB's proofs (work in progress; not built, not landed)

Durable copy of PB's proofs against the P1 statements (`plans/resource-cert/P1-Statements.lean`
in the lead's tree, 643 lines, md5 `eba738083749687cb6df5ba6946722a0`). Remove this directory when the
proofs land as modules on `IxCC/Src/Relevance/Proof/P1/Defs.lean`.

- `P1-Statements-with-PB-proofs.lean`: the statements file with PB's parts substituted for their
  `sorry` (`assemble.sh`). Elaborated on the box (job PB-el3, checkout fix-s at `a2c060d0c`, the
  eleventh route's head): no error; six `sorry`s left (`facts_modeEq`, `live_not_irr`, `preserve`,
  `pre_step`, `reads_live`, `run_live`); `#print axioms`: `front_accepted`, `shapeOk_of_run`
  `[propext, Classical.choice, Quot.sound]`; `eval_shielded_prefix` `[propext, Quot.sound]`;
  `eval_erased_prefix` `[propext, Classical.choice, Quot.sound]`. `goesWrong_live` and `sound_live`
  are proved there from `run_live` and `facts_modeEq`.
- `parts/`: the proof texts (`prefix.lean` holds the helper lemmas inserted before
  `eval_shielded_prefix`).
- `Prefix.lean.draft`: the module the prefix lemmas become (imports `P1.Defs`, not yet existing).
