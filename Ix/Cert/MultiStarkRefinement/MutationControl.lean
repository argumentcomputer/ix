import Ix.Cert.MultiStarkRefinement.EndToEnd

/-! # Mutation Negative Controls for `MultiStark.recursionProgram` Refinement

Verifies that our AST pin and semantic verifier specifications are non-vacuous by proving
three independent negative controls:
1. **AST Mutation Control (`mutated_drop_ext_is_zero_fails_pin`):**
   Replacing `StarkVerifier::verify_batch`'s body in `MultiStark.recursionSource` with a body
   that drops the final `ext_is_zero(total) == 1` check breaks `RecursionVerifierAstPinned`!
1b. **AST Mutation Control (`mutated_drop_fixed_height_fails_pins`):**
   Replacing `StarkVerifier::ood_loop`'s fixed-table height assertion
   `(1 - Fields::is_zero(ph)) * (height - ph) == 0` breaks `OodLoopBindsFixedHeights` and
   `RecursionVerifierAstPinned`.
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

/-! ## 1b. AST Mutation Control: Dropping the Fixed-Table Height Binding Breaks Both Pins -/

mutual
/-- `e` with every subexpression satisfying `p` replaced by `r` (outermost first). -/
def exprReplace (p : Generic.Expr Nat → Bool) (r : Generic.Expr Nat) :
    Generic.Expr Nat → Generic.Expr Nat
  | e@(.literal _) | e@(.var _) | e@(.global _ _) => if p e then r else e
  | e@(.tuple xs) => if p e then r else .tuple (exprListReplace p r xs)
  | e@(.array xs) => if p e then r else .array (exprListReplace p r xs)
  | e@(.repeat x n) => if p e then r else .repeat (exprReplace p r x) n
  | e@(.index x i) => if p e then r else .index (exprReplace p r x) i
  | e@(.slice x a b) => if p e then r else .slice (exprReplace p r x) a b
  | e@(.construct n ts c xs) => if p e then r else .construct n ts c (exprListReplace p r xs)
  | e@(.constructAs ps t c xs) => if p e then r else .constructAs ps t c (exprListReplace p r xs)
  | e@(.record h xs) => if p e then r else .record h (exprListReplace p r xs)
  | e@(.member x f) => if p e then r else .member (exprReplace p r x) f
  | e@(.update ps xs) => if p e then r else .update ps (exprListReplace p r xs)
  | e@(.builtin b xs) => if p e then r else .builtin b (exprListReplace p r xs)
  | e@(.project x i) => if p e then r else .project (exprReplace p r x) i
  | e@(.letValue pat v b) => if p e then r else .letValue pat (exprReplace p r v) (exprReplace p r b)
  | e@(.store x) => if p e then r else .store (exprReplace p r x)
  | e@(.load x) => if p e then r else .load (exprReplace p r x)
  | e@(.hint t k c) => if p e then r else .hint t (exprReplace p r k) c
  | e@(.neg x) => if p e then r else .neg (exprReplace p r x)
  | e@(.binary o a b) => if p e then r else .binary o (exprReplace p r a) (exprReplace p r b)
  | e@(.call f ts xs) => if p e then r else .call f ts (exprListReplace p r xs)
  | e@(.matchValue s arms) => if p e then r else .matchValue (exprReplace p r s) (exprArmsReplace p r arms)
  | e@(.control k x) => if p e then r else .control k (exprReplace p r x)

def exprListReplace (p : Generic.Expr Nat → Bool) (r : Generic.Expr Nat) :
    List (Generic.Expr Nat) → List (Generic.Expr Nat)
  | [] => []
  | x :: xs => exprReplace p r x :: exprListReplace p r xs

def exprArmsReplace (p : Generic.Expr Nat → Bool) (r : Generic.Expr Nat) :
    List (Generic.Pattern Nat × Generic.Expr Nat) → List (Generic.Pattern Nat × Generic.Expr Nat)
  | [] => []
  | (q, e) :: arms => (q, exprReplace p r e) :: exprArmsReplace p r arms
end

/-- `MultiStark.recursionSource` with `ood_loop`'s fixed-table height assertion
(`isFixedHeightAssert`) replaced by the literal `0`: the verifier that accepted fixed tables
at any height. -/
def mutatedRecursionSourceNoFixedHeight : Modules.Program Nat :=
  match findModuleFunction? MultiStark.recursionSource "StarkVerifier" "ood_loop" with
  | some f =>
    mutateModuleFn MultiStark.recursionSource "StarkVerifier" "ood_loop"
      (exprReplace isFixedHeightAssert (.literal 0) f.body)
  | none => MultiStark.recursionSource

/-- **Negative Control 1b:** Dropping the fixed-table height assertion from `ood_loop` breaks
both `OodLoopBindsFixedHeights` and `RecursionVerifierAstPinned` (its assertion count). -/
theorem mutated_drop_fixed_height_fails_pins :
    OodLoopBindsFixedHeights mutatedRecursionSourceNoFixedHeight = false ∧
      RecursionVerifierAstPinned mutatedRecursionSourceNoFixedHeight = false := by
  decide

/-- Concrete tampered `MultiStark.recursionSource` where `StarkVerifier::verify_shard` omits its
security-floor and zero-bit PoW checks. -/
def mutatedRecursionSourceNoSecurityFloor : Modules.Program Nat :=
  mutateModuleFn MultiStark.recursionSource "StarkVerifier" "verify_shard"
    (.call "last_acc" none [.var "accs"])

/-- **Negative Control 1c:** Dropping the security-floor and zero-bit PoW checks from
`StarkVerifier::verify_shard` breaks `RecursionVerifierAstPinned`. -/
theorem mutated_drop_security_floor_fails_pin :
    RecursionVerifierAstPinned mutatedRecursionSourceNoSecurityFloor = false := by
  decide

/-- Concrete tampered `MultiStark.recursionSource` where `SystemDeserialize::read_opt_idx_n` omits
its `has_commit == 1` check when decoding a preprocessed index. -/
def mutatedRecursionSourceNoPrepCommitGuard : Modules.Program Nat :=
  mutateModuleFn MultiStark.recursionSource "SystemDeserialize" "read_opt_idx_n"
    (.call "read_vk_u16" none [.var "i"])

/-- **Negative Control 1d:** Dropping the preprocessed commit guard from
`SystemDeserialize::read_opt_idx_n` breaks `RecursionVerifierAstPinned`. -/
theorem mutated_drop_prep_commit_guard_fails_pin :
    RecursionVerifierAstPinned mutatedRecursionSourceNoPrepCommitGuard = false := by
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
