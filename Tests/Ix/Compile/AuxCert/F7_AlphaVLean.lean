/-! F7 (class D, validator: Ix.Tc meta roundtrip). Every alpha-collapsing mutual block fails
`ix validate-lean` Phase 4 (kernel meta roundtrip), although `ix validate` (Rust) passes and
both kernels accept:
`ix validate-lean F7_AlphaVLean.lean --ns A,B` ->
  ✗ B.s: type mismatch: .ty: const 'A' vs 'B'
  ✗ A: constant absent from kernel env after ingress  (also A.s, A.z)
Seen on M2_{T,P,U}_alpha, M2_*_alphaidx, M3_*_alpha3, NP_mutual_alpha, every F1 shape. -/
mutual
inductive A where
  | z
  | s : B → A
inductive B where
  | z
  | s : A → B
end
