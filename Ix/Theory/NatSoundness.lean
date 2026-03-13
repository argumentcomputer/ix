/-
  Ix.Theory.NatSoundness: Soundness properties of nat reduction.

  Connects the nat-reducing evaluator to the environment's `extra` defeqs.
  The key results:
  - `natPrimRule_sound`: each primitive reduction is a valid SDefEq
  - `natIota_complete`: both zero and succ iota rules are valid SDefEqs
  - `natPrim_agrees`: BigUint computation equals recursor-based computation

  Note: Full connection to the typing judgment (`IsDefEq`) is deferred to
  when the typing judgment is defined (Phase 3 of the formalization roadmap).
  The theorems here are stated in terms of `SEnv.defeqs` and `WFNatEnv`,
  which the `extra` rule of `IsDefEq` consumes.
-/
import Ix.Theory.NatEval

namespace Ix.Theory

/-! ## Soundness summary

    This section collects the key soundness results into a single namespace
    for easy reference. All proofs are in `Nat.lean` and `NatEval.lean`;
    this file re-exports them with documentation. -/

/-- **Primitive computation soundness**: For every nat binary operation,
    the kernel's direct computation (BigUint) agrees with the recursor-based
    structural recursion. This means the fast-path reduction is correct.

    Example: `Nat.add 3 5` computes to `8` via BigUint, and the recursor
    definition `add m 0 = m, add m (n+1) = succ(add m n)` also gives `8`.

    Proof: by structural induction on the second argument for each op.
    See `Ix.Theory.natPrim_agrees`. -/
theorem primCompute_eq_recCompute (op : NatPrimOp) (m n : Nat) :
    natPrimCompute op m n = natRecCompute op m n :=
  natPrim_agrees op m n

/-- **Primitive rule soundness**: In any well-formed Nat environment,
    each primitive reduction rule is a valid `SDefEq` entry.
    The `extra` rule of `IsDefEq` can use these to justify
    `op(lit m, lit n) ≡ lit(result) : Nat`.

    See `Ix.Theory.natPrimRule_sound`. -/
theorem primRule_defeq (h : WFNatEnv env cfg) (op : NatPrimOp) (m n : Nat) :
    env.defeqs {
      uvars := 0,
      lhs := mkNatPrimApp cfg op (.lit m) (.lit n),
      rhs := .lit (natPrimCompute op m n),
      type := natTypeExpr cfg } :=
  natPrimRule_sound h op m n

/-- **Lit↔ctor soundness**: In any well-formed Nat environment,
    the conversion `lit n ≡ succ^n(zero)` is a valid `SDefEq`.
    This justifies comparing nat literals against constructor chains.

    The kernel's current bug: `nat_lit_to_ctor_val` only converts `0`,
    but this theorem holds for ALL `n`. Any correct implementation
    must handle the general case.

    See `Ix.Theory.natLitCtor_sound`. -/
theorem litCtor_defeq (h : WFNatEnv env cfg) (n : Nat) :
    env.defeqs {
      uvars := 0,
      lhs := .lit n,
      rhs := natLitToCtorExpr cfg n,
      type := natTypeExpr cfg } :=
  natLitCtor_sound h n

/-- **Iota completeness**: In any well-formed Nat environment,
    `Nat.rec` applied to any nat literal (not just `0`) reduces correctly.

    - `Nat.rec motive z s (lit 0) ≡ z`
    - `Nat.rec motive z s (lit (n+1)) ≡ s (lit n) (Nat.rec motive z s (lit n))`

    The kernel's current bug: only `lit 0` is converted before iota,
    so `Nat.rec` on `lit 5` gets stuck. This theorem specifies the
    correct behavior for all literals.

    See `Ix.Theory.natIota_complete`. -/
theorem iota_complete_defeq (h : WFNatEnv env cfg) :
    (∀ motive z s, env.defeqs {
      uvars := 0,
      lhs := .app (.app (.app (.app (.const cfg.recId [.zero]) motive) z) s) (.lit 0),
      rhs := z,
      type := .app motive (.lit 0) })
    ∧
    (∀ motive z s n, env.defeqs {
      uvars := 0,
      lhs := .app (.app (.app (.app (.const cfg.recId [.zero]) motive) z) s) (.lit (n + 1)),
      rhs := .app (.app s (.lit n))
        (.app (.app (.app (.app (.const cfg.recId [.zero]) motive) z) s) (.lit n)),
      type := .app motive (.lit (n + 1)) }) :=
  natIota_complete h

/-! ## Nat reduction oracle correctness -/

/-- The nat reduction oracle preserves well-formedness. -/
theorem natReduce_wf [BEq L] (cfg : SNatConfig)
    (hv : tryNatReduce cfg v = some v') : ValWF (L := L) v' d :=
  tryNatReduce_preserves_wf cfg hv

/-- The nat reduction oracle never fires on fvar-headed terms,
    which means it doesn't interfere with NbE on normal forms. -/
theorem natReduce_fvar_noop [BEq L] (cfg : SNatConfig)
    (level : Nat) (spine : List (SVal L)) :
    reduceNat cfg (.neutral (.fvar level) spine) =
    SVal.neutral (.fvar level) spine :=
  reduceNat_fvar level spine cfg

/-! ## Key implementation invariants

    These are not theorems per se, but documented invariants that the
    kernel implementation must satisfy for soundness. The formalization
    above proves them at the specification level.

    1. **Complete lit↔ctor conversion**: When comparing `lit n` against
       a constructor chain, the kernel must convert for ALL `n`, not
       just `n = 0`. (`litCtor_defeq` proves this is sound.)

    2. **Complete literal iota**: When `Nat.rec` is applied to `lit n`
       for any `n`, the kernel must either:
       (a) Convert `lit n` to the full constructor chain and apply
           standard iota, OR
       (b) Directly compute `Nat.rec motive z s (lit n)` using
           the recurrence `s (lit (n-1)) (Nat.rec ... (lit (n-1)))`.
       (`iota_complete_defeq` proves both approaches are sound.)

    3. **Primitive reduction agrees with recursor**: For each nat
       binary operation, the direct BigUint computation produces the
       same result as the recursor-based definition.
       (`primCompute_eq_recCompute` proves this for all 14 ops.)
-/

end Ix.Theory
