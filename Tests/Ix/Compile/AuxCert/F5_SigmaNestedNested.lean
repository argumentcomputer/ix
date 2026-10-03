/-! F5 (class B: kernels disagree; class D: decompile roundtrip). A nested occurrence inside the
*function* argument of a nested container: `Sigma Nat (fun _ => List T)`.
`ix compile F5_SigmaNestedNested.lean --no-build --consts T.rec,T.rec_1,T.rec_2,T.brecOn,Sigma.rec,List.rec,PProd.rec,PUnit.rec,Nat.rec --out c.ixe`
`ix check-rs c.ixe`  -> T.rec, T.rec_1, T.rec_2: check_recursor: could not resolve inductive block
`ix check-rs --anon` -> same; `ix check-lean` -> T.rec_2: could not resolve inductive block (29/32)
kernel-check-ixe (certified): 30/30 accept.
`ix validate F5_SigmaNestedNested.lean --no-build --ns T` -> 30 failures: Phase 6 aux congruence 15,
Phase 7b fidelity 15 ("roundtrip recompile hash mismatch for T.rec / casesOn / recOn / below").
Passes: `Nat × List T`, `(_ : Nat) × T`, `PSigma (fun _ => T)`, `Option (Vec T 2)`.
Fails too: `(n : Nat) × Vec T n` (user indexed Vec). -/
inductive T : Type where
  | leaf : T
  | node : (n : Nat) × List T → T
