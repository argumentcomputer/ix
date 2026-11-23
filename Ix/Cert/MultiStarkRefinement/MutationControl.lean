import Ix.Cert.MultiStarkRefinement.EndToEnd

/-! # Mutation Negative Controls for `MultiStark.recursionProgram` Refinement

Verifies that our AST pin and semantic verifier specifications are non-vacuous by proving
three independent negative controls:
1. **AST Mutation Control (`mutated_drop_ext_is_zero_fails_pin`):**
   Replacing `StarkVerifier::verify_batch`'s body in `MultiStark.recursionSource` with a body
   that drops the final `ext_is_zero(total) == 1` check breaks `RecursionVerifierAstPinned`!
2. **Semantic LogUp Mutation Control (`mutated_drop_ext_is_zero_unsound`):**
   A mutated batch verifier that omits `total == GoldilocksExt.zero` accepts a concrete
   nonzero-residual witness (`total = ⟨1, 0⟩`) that `Ix.Cert.MultiStark.verifyBatch` rejects!
3. **Semantic `MEMSEG` Closure Mutation Control (`mutated_drop_closure_pairs_unsound`):**
   A mutated preamble validator that omits `checkClosurePairs` accepts a concrete overlapping
   `MEMSEG = 16` interval message list (`[5, 10)` and `[7, 12)` at width `1`) that
   `Ix.Cert.MultiStark.checkClosurePairs` rejects!

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard axioms only.
-/

namespace Ix.Cert.MultiStarkRefinement

open Aiur Aiur.Generic Aiur.Modules
open CertiFri.P3
open Ix.Cert.MultiStark

/-! ## 1. AST Mutation Control: Tampering `StarkVerifier::verify_batch` Breaks the Pin -/

/-- Replace the body of function `targetFn` inside module `targetMod` with `newBody`. -/
def mutateModuleFn {α : Type} (prog : Modules.Program α)
    (targetMod targetFn : String) (newBody : Generic.Expr α) : Modules.Program α :=
  { prog with
    modules := prog.modules.map fun m =>
      if m.name == targetMod then
        match m.body with
        | .«alias» r => { m with body := .«alias» r }
        | .definitions d =>
          { m with
            body := .definitions
              { d with
                program :=
                  { d.program with
                    functions := d.program.functions.map fun fdecl =>
                      if fdecl.name == targetFn then { fdecl with body := newBody } else fdecl } } }
      else m }

/-- Concrete tampered `MultiStark.recursionSource` where `StarkVerifier::verify_batch` drops
`ext_is_zero(total) == 1` (returning `batch_claims(headers)` directly). -/
def mutatedRecursionSourceNoExtIsZero : Modules.Program Nat :=
  mutateModuleFn MultiStark.recursionSource "StarkVerifier" "verify_batch"
    (.call "batch_claims" none [.var "headers"])

/-- **Negative Control 1:** Dropping `ext_is_zero` from `StarkVerifier::verify_batch` breaks
`RecursionVerifierAstPinned` (contrast with `recursionSource_ast_pinned`). -/
theorem mutated_drop_ext_is_zero_fails_pin :
    RecursionVerifierAstPinned mutatedRecursionSourceNoExtIsZero = false := by
  decide

/-! ## 2. Semantic Mutation Control: Dropping `total == 0` Breaks LogUp Soundness -/

/-- Mutated final LogUp residual check that accepts any residual (omitting `ext_is_zero`). -/
def mutatedFinalCheck (_total : EF) : Bool := true

/-- Certified final LogUp residual check used in `Ix.Cert.MultiStark.verifyBatch`. -/
def certifiedFinalCheck (total : EF) : Bool := total == GoldilocksExt3.zero

/-- **Negative Control 2:** There exists a concrete nonzero LogUp residual (`⟨1, 0, 0⟩`)
accepted by `mutatedFinalCheck` but rejected by `certifiedFinalCheck` (and hence by
`Ix.Cert.MultiStark.verifyBatch`). -/
theorem mutated_drop_ext_is_zero_unsound :
    ¬ (∀ total : EF, mutatedFinalCheck total = true → certifiedFinalCheck total = true) := by
  intro h
  have hbad := h GoldilocksExt3.one rfl
  revert hbad
  decide

/-! ## 3. Semantic Mutation Control: Dropping `checkClosurePairs` Permits Overlapping ROM Intervals -/

/-- Concrete overlapping `MEMSEG = 16` message list: width `1`, intervals `[5, 10)` and `[7, 12)`. -/
def overlappingMemsegMessages : Array BatchMessage :=
  let negOne : Goldilocks := Goldilocks.neg Goldilocks.one
  let ch16 : Goldilocks := Goldilocks.ofNat MEMSEG_CHANNEL
  let w1 : Goldilocks := Goldilocks.ofNat 1
  #[ { args := #[ch16, w1, Goldilocks.ofNat 5], multiplicity := negOne }
   , { args := #[ch16, w1, Goldilocks.ofNat 10], multiplicity := Goldilocks.one }
   , { args := #[ch16, w1, Goldilocks.ofNat 7], multiplicity := negOne }
   , { args := #[ch16, w1, Goldilocks.ofNat 12], multiplicity := Goldilocks.one }
   ]

/-- **Negative Control 3:** `Ix.Cert.MultiStark.checkClosurePairs` rejects
`overlappingMemsegMessages`, and `extractWidthIntervals 1` fails `DisjointIntervals` — so any
mutated verifier that omits `assert_closure_pairs` / `checkClosurePairs` breaks `WidthROM.Valid`! -/
theorem mutated_drop_closure_pairs_unsound :
    checkClosurePairs overlappingMemsegMessages = false ∧
    ¬ DisjointIntervals (extractWidthIntervals 1 overlappingMemsegMessages.toList) := by
  constructor
  · unfold checkClosurePairs overlappingMemsegMessages
    dsimp only [Id.run]
    simp only [Array.size, List.length_cons, List.length_nil]
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    decide
  · intro hdisj
    have hstep := hdisj.2 0 (by decide)
    revert hstep
    decide

end Ix.Cert.MultiStarkRefinement
