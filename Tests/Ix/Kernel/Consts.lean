/-
  Shared constant name arrays for kernel tests.
  Both Lean and Rust kernel tests iterate over these lists.
-/

namespace Tests.Ix.Kernel.Consts

/-- Regression constants: the unified set of constants tested by both Lean and Rust kernels. -/
def regressionConsts : Array String := #[
  -- Basic inductives
  "Nat", "Nat.zero", "Nat.succ", "Nat.rec",
  "Bool", "Bool.true", "Bool.false", "Bool.rec",
  "Eq", "Eq.refl",
  "List", "List.nil", "List.cons",
  "Nat.below",
  -- Quotient types
  "Quot", "Quot.mk", "Quot.lift", "Quot.ind",
  -- K-reduction exercisers
  "Eq.rec", "Eq.subst", "Eq.symm", "Eq.trans",
  -- Proof irrelevance
  "And.intro", "Or.inl", "Or.inr",
  -- K-like reduction with congr
  "congr", "congrArg", "congrFun",
  -- Structure projections + eta
  "Prod.fst", "Prod.snd", "Prod.mk", "Sigma.mk", "Subtype.mk",
  -- Nat primitives
  "Nat.add", "Nat.sub", "Nat.mul", "Nat.div", "Nat.mod",
  "Nat.gcd", "Nat.beq", "Nat.ble",
  "Nat.land", "Nat.lor", "Nat.xor",
  "Nat.shiftLeft", "Nat.shiftRight", "Nat.pow",
  "Nat.pred", "Nat.bitwise",
  -- String/Char primitives
  "Char.ofNat", "String.ofList",
  -- Recursors
  "List.rec",
  -- Delta unfolding
  "id", "Function.comp",
  -- Various inductives
  "Empty", "PUnit", "Fin", "Sigma", "Prod",
  -- Proofs / proof irrelevance
  "True", "False", "And", "Or",
  -- Mutual/nested inductives
  "List.map", "List.foldl", "List.append",
  -- Universe polymorphism
  "ULift", "PLift",
  -- More complex
  "Option", "Option.some", "Option.none",
  "String", "String.mk", "Char",
  -- Partial definitions
  "WellFounded.fix",
  -- Well-founded recursion scaffolding
  "Nat.brecOn",
  -- PProd (used by Nat.below)
  "PProd", "PProd.mk", "PProd.fst", "PProd.snd",
  "PUnit.unit",
  -- noConfusion
  "Lean.Meta.Grind.Origin.noConfusionType",
  "Lean.Meta.Grind.Origin.noConfusion",
  "Lean.Meta.Grind.Origin.stx.noConfusion",
  "String.length_empty",
  "_private.Init.Grind.Ring.Basic.«0».Lean.Grind.IsCharP.mk'_aux._proof_1_5",
  -- BVDecide regression test (fuel-sensitive)
  "Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.instLawfulVecOperatorShiftConcatInputBlastShiftConcat",
  -- Theorem with sub-term type mismatch (requires inferOnly)
  "Std.Do.Spec.tryCatch_ExceptT",
  -- Nested inductive positivity check (requires whnf)
  "Lean.Elab.Term.Do.Code.action",
  -- UInt64/BitVec isDefEq regression
  "UInt64.decLt",
  -- Dependencies of _sunfold
  "Std.Time.FormatPart",
  "Std.Time.FormatConfig",
  "Std.Time.FormatString",
  "Std.Time.FormatType",
  "Std.Time.FormatType.match_1",
  "Std.Time.TypeFormat",
  "Std.Time.Modifier",
  "List.below",
  "List.brecOn",
  "Std.Internal.Parsec.String.Parser",
  "Std.Internal.Parsec.instMonad",
  "Std.Internal.Parsec.instAlternative",
  "Std.Internal.Parsec.String.skipString",
  "Std.Internal.Parsec.eof",
  "Std.Internal.Parsec.fail",
  "Bind.bind",
  "Monad.toBind",
  "SeqRight.seqRight",
  "Applicative.toSeqRight",
  "Applicative.toPure",
  "Alternative.toApplicative",
  "Pure.pure",
  "_private.Std.Time.Format.Basic.«0».Std.Time.parseWith",
  "_private.Std.Time.Format.Basic.«0».Std.Time.GenericFormat.builderParser.go.match_3",
  "_private.Std.Time.Format.Basic.«0».Std.Time.GenericFormat.builderParser.go.match_1",
  "_private.Std.Time.Format.Basic.«0».Std.Time.GenericFormat.builderParser.go",
  -- Deeply nested let chain (stack overflow regression)
  "_private.Std.Time.Format.Basic.«0».Std.Time.GenericFormat.builderParser.go._sunfold",
  -- Let-bound bvar zeta-reduction regression
  "Std.Sat.AIG.mkGate",
  -- Proof irrelevance regression
  "Fin.dfoldrM.loop._sunfold",
  -- K-reduction: extra args after major premise
  "UInt8.toUInt64_toUSize",
  -- DHashMap: rfl theorem requiring projection reduction + eta-struct
  "Std.DHashMap.Internal.Raw₀.contains_eq_containsₘ",
  -- K-reduction: toCtorWhenK must check isDefEq before reducing
  "instDecidableEqVector.decEq",
  -- Recursor-only Ixon block regression
  "Lean.Elab.Tactic.RCases.RCasesPatt.rec_1",
  -- check-env hang regression
  "Std.Time.Modifier.ctorElim",
  -- rfl theorem
  "Std.Tactic.BVDecide.BVExpr.eval.eq_10",
  -- check-env hang: complex recursor
  "Std.DHashMap.Raw.WF.rec",
  -- Stack overflow regression
  "Nat.Linear.Poly.of_denote_eq_cancel",
  -- Nat.Linear isValid reduction (eagerReduce + polynomial constraint validity)
  "Nat.Linear.PolyCnstr.eq_true_of_isValid",
  "Nat.Linear.ExprCnstr.eq_true_of_isValid",
  "_private.Init.Data.Range.Polymorphic.SInt.«0».Int64.instRxiHasSize_eq",
  -- Proof irrelevance edge cases
  "Decidable.decide",
  -- K-reduction
  "Eq.mpr", "Eq.ndrec",
  -- Structure eta / projections
  "Sigma.fst", "Sigma.snd", "Subtype.val",
  -- String handling
  "String.data", "String.length",
  -- Complex recursion
  "Fin.mk",
  -- Nested inductives
  "Array.toList",
  -- Well-founded recursion
  "WellFounded.fixF",
  -- Nat prim fvar-blocking + Ctor(Nat.succ) extraction regression
  "Batteries.BinaryHeap.heapifyDown._unsafe_rec"
]

/-- Lean kernel problematic constants: slow or hanging, isolated for profiling. -/
def problematicConsts : Array String := #[
  "Batteries.BinaryHeap.heapifyDown._unsafe_rec",
]

/-- Rust kernel problematic constants. -/
def rustProblematicConsts : Array String := #[
]

end Tests.Ix.Kernel.Consts
