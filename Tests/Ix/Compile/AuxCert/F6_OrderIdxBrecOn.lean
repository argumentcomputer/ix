/-! F6 (class A, and C: the outcome depends on source order). Mutual block whose members have
different index counts, declared indexed-member FIRST, plus mutual structural recursion.
`ix compile F6_OrderIdxBrecOn.lean --no-build` -> exit 1:
  block FAILED A.w (1 members): invalid mutual block: eta call-site adapter for 'A.brecOn'
  found no residual Pi binders after 5 args
  (then B.w._sunfold: missing constant: A.w)
Same declarations with `A` declared before `B`: compiles (whichever order the two defs are in).
Lean accepts both orders. -/
mutual
inductive B : Nat → Type where
  | z : B 0
  | s : {n : Nat} → A → B n → B (n + 1)
inductive A : Type where
  | nil
  | mk : {n : Nat} → B n → A
end
mutual
def A.w : A → Nat
  | .nil => 0
  | .mk b => b.w + 1
  termination_by structural x => x
def B.w : {n : Nat} → B n → Nat
  | _, .z => 0
  | _, .s a b => a.w + b.w
  termination_by structural _ x => x
end

/-! Neighbours (round 2, `corpus/R2/F6_*`): the B-first order also fails for index counts 1/2,
for a block parameter, and for the Prop version (theorems). With a third member
`C : Nat → Nat → Type | z : C 0 0 | s : {n m} → A → C n m`:
  order A, C, B: compiles, but `B.w` is ill-typed: check-rs AppTypeMismatch AND kernel-check-ixe
  reject "application type mismatch" (class B);
  orders with B before A: block FAILED A.w (eta call-site adapter … after 7 args). -/
