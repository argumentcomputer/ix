import MultiStark.Program
import Ix.Cert.MultiStark.Types
import Ix.Cert.MultiStark.FieldModel
import Aiur.Library.Bytes.Correctness
import Aiur.Optimized.Observed
import Ix.Address.Pure

/-! # MultiStark Recursive Verifier Program Pinning & Representation Seams (`ProgramPin`)

Pins the deployed `MultiStark.recursionSource` and `MultiStark.recursionProgram` ASTs by
kernel-checked proofs (`decide` / `rfl`) and defines the value representations and
BLAKE3 collision escape connecting observed `MultiStark::verify_multi_stark_proof`
executions to `Ix.Cert.MultiStark`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard axioms only.
-/

namespace Ix.Cert.MultiStarkRefinement

open Aiur Aiur.Generic Aiur.Modules
open Ix.Cert.MultiStark

/-! ## 1. Structural AST Inspection Predicates (Kernel-Reducible Mutual Recursion) -/

mutual
/-- Collect all callee names appearing anywhere inside an Aiur `Generic.Expr`. -/
def exprCalls {α : Type} : Generic.Expr α → List String
  | .literal _ | .var _ | .global _ _ => []
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs =>
      exprListCalls xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _
  | .project x _ | .store x | .load x | .hint _ x _ | .neg x | .control _ x =>
      exprCalls x
  | .letValue _ v b | .binary _ v b =>
      exprCalls v ++ exprCalls b
  | .call name _ args =>
      name :: exprListCalls args
  | .matchValue s arms =>
      exprCalls s ++ exprArmsCalls arms

def exprListCalls {α : Type} : List (Generic.Expr α) → List String
  | [] => []
  | x :: xs => exprCalls x ++ exprListCalls xs

def exprArmsCalls {α : Type} : List (Generic.Pattern α × Generic.Expr α) → List String
  | [] => []
  | (_, e) :: arms => exprCalls e ++ exprArmsCalls arms
end

mutual
/-- Count how many `assert_eq!` builtins appear inside an Aiur `Generic.Expr`. -/
def exprAssertCount {α : Type} : Generic.Expr α → Nat
  | .literal _ | .var _ | .global _ _ => 0
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs =>
      exprListAssertCount xs
  | .builtin (.assertEq _) xs =>
      1 + exprListAssertCount xs
  | .builtin _ xs =>
      exprListAssertCount xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _
  | .project x _ | .store x | .load x | .hint _ x _ | .neg x | .control _ x =>
      exprAssertCount x
  | .letValue _ v b | .binary _ v b =>
      exprAssertCount v + exprAssertCount b
  | .call _ _ args =>
      exprListAssertCount args
  | .matchValue s arms =>
      exprAssertCount s + exprArmsAssertCount arms

def exprListAssertCount {α : Type} : List (Generic.Expr α) → Nat
  | [] => 0
  | x :: xs => exprAssertCount x + exprListAssertCount xs

def exprArmsAssertCount {α : Type} : List (Generic.Pattern α × Generic.Expr α) → Nat
  | [] => 0
  | (_, e) :: arms => exprAssertCount e + exprArmsAssertCount arms
end

/-- Extract all literal match-arm patterns of the top-level (or nested) `matchValue` on `expr`. -/
def exprMatchLitArms : Generic.Expr Nat → List Nat
  | .matchValue _ arms =>
      arms.filterMap fun
        | (.literal n, _) => some n
        | _ => none
  | .letValue _ _ body => exprMatchLitArms body
  | .control _ body => exprMatchLitArms body
  | _ => []

/-- Look up a function by module name and function name inside a `Modules.Program`. -/
def findModuleFunction? {α : Type} (prog : Modules.Program α)
    (modName fnName : String) : Option (Generic.Function α) := do
  let m ← prog.findModule? modName
  match m.body with
  | .definitions defs => defs.program.findFunction? fnName
  | Modules.Body.alias _ => none

/-- Check whether `prog` contains module `modName` defining function `fnName`. -/
def hasModuleFunction {α : Type} (prog : Modules.Program α) (modName fnName : String) : Bool :=
  (findModuleFunction? prog modName fnName).isSome

/-- Check whether function `modName::fnName` in `prog` contains calls to every name in `callees`
and at least `minAsserts` `assert_eq!` constraints. -/
def fnHasCallsAndAsserts {α : Type} (prog : Modules.Program α)
    (modName fnName : String) (callees : List String) (minAsserts : Nat) : Bool :=
  match findModuleFunction? prog modName fnName with
  | none => false
  | some fdecl =>
      let calls := exprCalls fdecl.body
      callees.all (fun c => calls.contains c) && decide (minAsserts ≤ exprAssertCount fdecl.body)

/-! ## 2. `Program.map` Preservation Lemmas (lifting `Nat` pins to `_root_.MultiStark.F`) -/

mutual
theorem exprCalls_map {α β : Type} (f : α → β) :
    ∀ (e : Generic.Expr α), exprCalls (e.map f) = exprCalls e
  | .literal _ => by simp [Generic.Expr.map, exprCalls]
  | .var _ => by simp [Generic.Expr.map, exprCalls]
  | .global _ _ => by simp [Generic.Expr.map, exprCalls]
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs => by
      simp only [Generic.Expr.map, exprCalls]
      exact exprListCalls_map f xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _
  | .project x _ | .store x | .load x | .hint _ x _ | .neg x | .control _ x => by
      simp only [Generic.Expr.map, exprCalls]
      exact exprCalls_map f x
  | .letValue _ v b | .binary _ v b => by
      simp only [Generic.Expr.map, exprCalls, exprCalls_map f v, exprCalls_map f b]
  | .call _ _ args => by
      simp only [Generic.Expr.map, exprCalls, exprListCalls_map f args]
  | .matchValue s arms => by
      simp only [Generic.Expr.map, exprCalls, exprCalls_map f s, exprArmsCalls_map f arms]

theorem exprListCalls_map {α β : Type} (f : α → β) :
    ∀ (xs : List (Generic.Expr α)), exprListCalls (xs.map (Generic.Expr.map f)) = exprListCalls xs
  | [] => rfl
  | x :: xs => by
      simp only [List.map_cons, exprListCalls, exprCalls_map f x, exprListCalls_map f xs]

theorem exprArmsCalls_map {α β : Type} (f : α → β) :
    ∀ (arms : List (Generic.Pattern α × Generic.Expr α)),
      exprArmsCalls (arms.map fun arm => (arm.1.map f, arm.2.map f)) = exprArmsCalls arms
  | [] => rfl
  | (_, e) :: arms => by
      simp only [List.map_cons, exprArmsCalls, exprCalls_map f e, exprArmsCalls_map f arms]
end

mutual
theorem exprAssertCount_map {α β : Type} (f : α → β) :
    ∀ (e : Generic.Expr α), exprAssertCount (e.map f) = exprAssertCount e
  | .literal _ => by simp [Generic.Expr.map, exprAssertCount]
  | .var _ => by simp [Generic.Expr.map, exprAssertCount]
  | .global _ _ => by simp [Generic.Expr.map, exprAssertCount]
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs => by
      simp only [Generic.Expr.map, exprAssertCount]
      exact exprListAssertCount_map f xs
  | .builtin op xs => by
      cases op <;> simp only [Generic.Expr.map, exprAssertCount, exprListAssertCount_map f xs]
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _
  | .project x _ | .store x | .load x | .hint _ x _ | .neg x | .control _ x => by
      simp only [Generic.Expr.map, exprAssertCount]
      exact exprAssertCount_map f x
  | .letValue _ v b | .binary _ v b => by
      simp only [Generic.Expr.map, exprAssertCount, exprAssertCount_map f v, exprAssertCount_map f b]
  | .call _ _ args => by
      simp only [Generic.Expr.map, exprAssertCount]
      exact exprListAssertCount_map f args
  | .matchValue s arms => by
      simp only [Generic.Expr.map, exprAssertCount, exprAssertCount_map f s, exprArmsAssertCount_map f arms]

theorem exprListAssertCount_map {α β : Type} (f : α → β) :
    ∀ (xs : List (Generic.Expr α)),
      exprListAssertCount (xs.map (Generic.Expr.map f)) = exprListAssertCount xs
  | [] => rfl
  | x :: xs => by
      simp only [List.map_cons, exprListAssertCount, exprAssertCount_map f x,
        exprListAssertCount_map f xs]

theorem exprArmsAssertCount_map {α β : Type} (f : α → β) :
    ∀ (arms : List (Generic.Pattern α × Generic.Expr α)),
      exprArmsAssertCount (arms.map fun arm => (arm.1.map f, arm.2.map f)) =
        exprArmsAssertCount arms
  | [] => rfl
  | (_, e) :: arms => by
      simp only [List.map_cons, exprArmsAssertCount, exprAssertCount_map f e,
        exprArmsAssertCount_map f arms]
end

private theorem list_find?_map_pred {α β : Type} (g : α → β) (p : β → Bool) (q : α → Bool)
    (hpq : ∀ a, p (g a) = q a) (xs : List α) :
    (xs.map g).find? p = (xs.find? q).map g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.find?_cons, hpq]
    cases q x <;> simp [ih]

theorem findModuleFunction?_map {α β : Type} (f : α → β) (prog : Modules.Program α)
    (modName fnName : String) :
    findModuleFunction? (prog.map f) modName fnName =
      (findModuleFunction? prog modName fnName).map (fun fd => { fd with body := fd.body.map f }) := by
  unfold findModuleFunction? Modules.Program.findModule? Modules.Program.map
  rw [list_find?_map_pred _ _ (fun m => m.name == modName) (fun _ => rfl)]
  cases h : prog.modules.find? (fun m => m.name == modName) with
  | none => rfl
  | some m =>
    simp only [Option.map_some, bind, Option.bind]
    cases hm : m.body with
    | definitions d =>
      simp only [Modules.Definitions.map, Generic.Program.findFunction?, Generic.Program.map]
      exact list_find?_map_pred
        (fun (fd : Generic.Function α) => { fd with body := fd.body.map f })
        (fun (fd : Generic.Function β) => fd.name == fnName)
        (fun (fd : Generic.Function α) => fd.name == fnName)
        (fun _ => rfl) d.program.functions
    | «alias» _ => rfl

theorem fnHasCallsAndAsserts_map {α β : Type} (f : α → β) (prog : Modules.Program α)
    (modName fnName : String) (callees : List String) (minAsserts : Nat) :
    fnHasCallsAndAsserts (prog.map f) modName fnName callees minAsserts =
      fnHasCallsAndAsserts prog modName fnName callees minAsserts := by
  unfold fnHasCallsAndAsserts
  rw [findModuleFunction?_map]
  cases findModuleFunction? prog modName fnName with
  | none => rfl
  | some fdecl =>
    simp only [Option.map_some, exprCalls_map, exprAssertCount_map]

theorem findModule?_map_none {α β : Type} (f : α → β) (prog : Modules.Program α) (modName : String)
    (h : prog.findModule? modName = none) :
    (prog.map f).findModule? modName = none := by
  unfold Modules.Program.findModule? Modules.Program.map at *
  rw [list_find?_map_pred _ _ (fun m => m.name == modName) (fun _ => rfl), h]
  rfl

theorem findModule?_append_none {α : Type} (p q : Modules.Program α) (modName : String)
    (hp : p.findModule? modName = none) (hq : q.findModule? modName = none) :
    (p.append q).findModule? modName = none := by
  unfold Modules.Program.findModule? Modules.Program.append at *
  rw [List.find?_append, hp, hq]
  rfl

theorem findModuleFunction?_append_right {α : Type} (p q : Modules.Program α)
    (modName fnName : String) (hNotInP : p.findModule? modName = none) :
    findModuleFunction? (p.append q) modName fnName = findModuleFunction? q modName fnName := by
  unfold findModuleFunction? Modules.Program.findModule? Modules.Program.append at *
  rw [List.find?_append, hNotInP]
  rfl

/-! ## 3. Kernel-Checked Pinning of `MultiStark.recursionSource` and `MultiStark.recursionProgram` -/

/-- All nine MultiStark verifier modules present in `MultiStark.recursionSource`. -/
def recursionModuleNames : List String :=
  ["ProofDeserialize", "SystemDeserialize", "Pcs", "StarkIO",
   "StarkHash", "Mmcs", "StarkVerifier", "Transcript", "MultiStark"]

/-- Required core functions of the recursive Multi-STARK verifier. -/
def recursionCoreFunctions : List (String × String) :=
  [ ("MultiStark", "verify_multi_stark_proof")
  , ("StarkIO", "read_byte_stream")
  , ("SystemDeserialize", "read_system")
  , ("SystemDeserialize", "lookup_groups_count")
  , ("ProofDeserialize", "read_batch")
  , ("ProofDeserialize", "read_proof")
  , ("Transcript", "ch_sample8")
  , ("Transcript", "ch_sample_field")
  , ("Transcript", "ch_sample_ext")
  , ("Transcript", "ch_sample_bits")
  , ("Transcript", "batch_fiat_shamir")
  , ("Transcript", "shard_fiat_shamir")
  , ("StarkHash", "b3_rows")
  , ("StarkHash", "b3_to_digest")
  , ("Mmcs", "mmcs_verify_multi")
  , ("Pcs", "pcs_fri_verify")
  , ("StarkVerifier", "ext_is_zero")
  , ("StarkVerifier", "two_adic_gen")
  , ("StarkVerifier", "quotient_degree_of")
  , ("StarkVerifier", "eval_at")
  , ("StarkVerifier", "ood_composition")
  , ("StarkVerifier", "ood_loop")
  , ("StarkVerifier", "claims_acc")
  , ("StarkVerifier", "messages_acc")
  , ("StarkVerifier", "assert_shard_count_ok")
  , ("StarkVerifier", "at_most_row_bound")
  , ("StarkVerifier", "batch_rows")
  , ("StarkVerifier", "lookups_ok")
  , ("StarkVerifier", "assert_batch_bounds")
  , ("StarkVerifier", "bytes8_le")
  , ("StarkVerifier", "assert_closure_pairs")
  , ("StarkVerifier", "verify_shard")
  , ("StarkVerifier", "verify_shards")
  , ("StarkVerifier", "verify_batch")
  , ("StarkVerifier", "verify_batch_at")
  , ("StarkVerifier", "read_claims")
  ]

/-- Kernel-checked pin: every required MultiStark module and verifier function exists in
`MultiStark.recursionSource`. -/
theorem recursionSource_core_functions_present :
    recursionModuleNames.all (fun m => (MultiStark.recursionSource.findModule? m).isSome) = true ∧
    recursionCoreFunctions.all (fun p => hasModuleFunction MultiStark.recursionSource p.1 p.2) = true := by
  decide

/-- Required calls inside `MultiStark::verify_multi_stark_proof`. -/
def entryRequiredCalls : List String :=
  ["StarkIO::read_byte_stream", "Blake3::hash", "Blake3::pack_digest",
   "SystemDeserialize::read_system", "StarkVerifier::read_claims", "StarkVerifier::verify_batch_at"]

/-- Required calls inside `StarkVerifier::verify_batch`. -/
def verifyBatchRequiredCalls : List String :=
  ["assert_shard_count_ok", "assert_batch_bounds", "assert_closure_pairs",
   "Transcript::batch_fiat_shamir", "messages_acc", "verify_shards", "ext_is_zero", "batch_claims"]

/-- Required calls inside `StarkVerifier::verify_shard`. -/
def verifyShardRequiredCalls : List String :=
  ["Transcript::shard_fiat_shamir", "claims_acc", "ood_loop", "Pcs::pcs_fri_verify", "last_acc"]

/-- AST-level pin predicate on any MultiStark verifier program: checks entry point, `verify_batch`,
and `verify_shard` retain all mandatory subcalls and `assert_eq!` constraints. -/
def RecursionVerifierAstPinned {α : Type} (prog : Modules.Program α) : Bool :=
  fnHasCallsAndAsserts prog "MultiStark" "verify_multi_stark_proof" entryRequiredCalls 3 &&
  fnHasCallsAndAsserts prog "StarkVerifier" "verify_batch" verifyBatchRequiredCalls 5 &&
  fnHasCallsAndAsserts prog "StarkVerifier" "verify_shard" verifyShardRequiredCalls 15

/-- Kernel-checked AST pin of the deployed `MultiStark.recursionSource`. -/
theorem recursionSource_ast_pinned :
    RecursionVerifierAstPinned MultiStark.recursionSource = true := by
  decide

/-- None of the MultiStark-owned modules appear in the library prefix of `withLibraries`. -/
theorem libraries_disjoint_multistark :
    let libPrefix : Modules.Program Fp :=
      (Aiur.Library.Blake3.Goldilocks.program.append
        (Aiur.Library.Option.declarations.toField Fp)).append
        Aiur.Library.Field.Goldilocks.program
    libPrefix.findModule? "MultiStark" = none ∧
    libPrefix.findModule? "StarkVerifier" = none := by
  have hb1 : Aiur.Library.Blake3.Goldilocks.program.findModule? "MultiStark" = none := rfl
  have hb2 : Aiur.Library.Blake3.Goldilocks.program.findModule? "StarkVerifier" = none := rfl
  have ho : Aiur.Library.Option.declarations.findModule? "MultiStark" = none ∧
      Aiur.Library.Option.declarations.findModule? "StarkVerifier" = none := by
    decide
  have hf : Aiur.Library.Field.Goldilocks.declarations.findModule? "MultiStark" = none ∧
      Aiur.Library.Field.Goldilocks.declarations.findModule? "StarkVerifier" = none := by
    decide
  refine ⟨?_, ?_⟩
  · apply findModule?_append_none
    · exact findModule?_append_none _ _ _ hb1 (findModule?_map_none _ _ _ ho.1)
    · exact findModule?_map_none _ _ _ hf.1
  · apply findModule?_append_none
    · exact findModule?_append_none _ _ _ hb2 (findModule?_map_none _ _ _ ho.2)
    · exact findModule?_map_none _ _ _ hf.2

/-- Kernel-checked AST pin lifted to the actual Goldilocks `MultiStark.recursionProgram`. -/
theorem recursionProgram_ast_pinned :
    RecursionVerifierAstPinned MultiStark.recursionProgram = true := by
  have hdisj := libraries_disjoint_multistark
  unfold MultiStark.recursionProgram MultiStark.withLibraries RecursionVerifierAstPinned
  unfold fnHasCallsAndAsserts
  rw [findModuleFunction?_append_right _ _ "MultiStark" _ hdisj.1]
  rw [findModuleFunction?_append_right _ _ "StarkVerifier" _ hdisj.2]
  rw [findModuleFunction?_append_right _ _ "StarkVerifier" _ hdisj.2]
  have hsrc := recursionSource_ast_pinned
  unfold RecursionVerifierAstPinned fnHasCallsAndAsserts at hsrc
  have h1 := fnHasCallsAndAsserts_map (Nat.cast : Nat → Fp) MultiStark.recursionSource
    "MultiStark" "verify_multi_stark_proof" entryRequiredCalls 3
  have h2 := fnHasCallsAndAsserts_map (Nat.cast : Nat → Fp) MultiStark.recursionSource
    "StarkVerifier" "verify_batch" verifyBatchRequiredCalls 5
  have h3 := fnHasCallsAndAsserts_map (Nat.cast : Nat → Fp) MultiStark.recursionSource
    "StarkVerifier" "verify_shard" verifyShardRequiredCalls 15
  unfold fnHasCallsAndAsserts at h1 h2 h3
  unfold Modules.Program.toField
  rw [h1, h2, h3]
  exact hsrc

/-! ## 4. Public Digest Packing, Value Representations, and BLAKE3 Escape -/

/-- Entry point name of the recursive verifier program. -/
def verifyMultiStarkEntry : String := "MultiStark::verify_multi_stark_proof"

/-- Entry point name of the BLAKE3 hash function in `MultiStark.recursionProgram`. -/
def blake3HashEntry : String := "Blake3::hash"

/-- Canonical `Lists::Node<UInt8::U8>` byte-stream enum instance symbol. -/
def byteStreamEnumSymbol : String := "${\"name\":\"Lists::Node\",\"types\":[\"field\"]}"

/-- Eight-word little-endian packing of a 32-byte `Address` into Goldilocks field elements
(`Blake3::pack_digest`). -/
def packDigest8 (a : Address) : Fin 8 → Fp := fun i =>
  let b (k : Nat) : Nat := (a.hash.data.getD k 0).toNat
  ((b (4 * i.val) + 256 * b (4 * i.val + 1) + 65536 * b (4 * i.val + 2) +
    16777216 * b (4 * i.val + 3) : Nat) : Fp)

/-- The `Aiur.SourceValue Fp` representation of a `[Field; 8]` public digest argument. -/
def digest8SourceValue (d : Fin 8 → Fp) : Aiur.SourceValue Fp :=
  .tuple (List.ofFn fun i => .field (d i))

/-- Every `Address.blake3Pure` digest has exact byte length `32`. -/
theorem address_blake3Pure_size (x : ByteArray) : (Address.blake3Pure x).hash.size = 32 :=
  (Blake3.Pure.hash x).property

/-- Packing a 32-byte `Address` into 8 Goldilocks field elements is injective: each 32-bit
word is strictly below `2^32 < p = 2^64 - 2^32 + 1`. -/
theorem packDigest8_inj {a b : Address}
    (ha32 : a.hash.size = 32) (hb32 : b.hash.size = 32)
    (h : packDigest8 a = packDigest8 b) : a = b := by
  have hdata : a.hash.data = b.hash.data := by
    apply Array.ext
    · change a.hash.size = b.hash.size; rw [ha32, hb32]
    · intro k hk1 hk2
      have hk32 : k < 32 := by change k < a.hash.size at hk1; omega
      set wi : Fin 8 := ⟨k / 4, by omega⟩
      have hwi := congrFun h wi
      unfold packDigest8 at hwi
      have hba : ∀ j < 32, (a.hash.data.getD j 0).toNat < 256 := fun j _ => UInt8.toNat_lt _
      have hbb : ∀ j < 32, (b.hash.data.getD j 0).toNat < 256 := fun j _ => UInt8.toNat_lt _
      have hwi_val : wi.val = k / 4 := rfl
      have h0a := hba (4 * wi.val) (by omega)
      have h1a := hba (4 * wi.val + 1) (by omega)
      have h2a := hba (4 * wi.val + 2) (by omega)
      have h3a := hba (4 * wi.val + 3) (by omega)
      have h0b := hbb (4 * wi.val) (by omega)
      have h1b := hbb (4 * wi.val + 1) (by omega)
      have h2b := hbb (4 * wi.val + 2) (by omega)
      have h3b := hbb (4 * wi.val + 3) (by omega)
      have hltA : (a.hash.data.getD (4 * wi.val) 0).toNat +
          256 * (a.hash.data.getD (4 * wi.val + 1) 0).toNat +
          65536 * (a.hash.data.getD (4 * wi.val + 2) 0).toNat +
          16777216 * (a.hash.data.getD (4 * wi.val + 3) 0).toNat <
          Aiur.Library.U32.Goldilocks.modulus := by
        unfold Aiur.Library.U32.Goldilocks.modulus; omega
      have hltB : (b.hash.data.getD (4 * wi.val) 0).toNat +
          256 * (b.hash.data.getD (4 * wi.val + 1) 0).toNat +
          65536 * (b.hash.data.getD (4 * wi.val + 2) 0).toNat +
          16777216 * (b.hash.data.getD (4 * wi.val + 3) 0).toNat <
          Aiur.Library.U32.Goldilocks.modulus := by
        unfold Aiur.Library.U32.Goldilocks.modulus; omega
      have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hwi
      rw [Nat.mod_eq_of_lt hltA, Nat.mod_eq_of_lt hltB] at hmod
      have hbyte : (a.hash.data.getD k 0).toNat = (b.hash.data.getD k 0).toNat := by
        have hrem : k = 4 * wi.val ∨ k = 4 * wi.val + 1 ∨
            k = 4 * wi.val + 2 ∨ k = 4 * wi.val + 3 := by omega
        rcases hrem with h0 | h1 | h2 | h3
        · rw [h0]; omega
        · rw [h1]; omega
        · rw [h2]; omega
        · rw [h3]; omega
      have hgetA : a.hash.data.getD k 0 = a.hash.data[k] := by
        unfold Array.getD; simp only [hk1, ↓reduceDIte]; rfl
      have hgetB : b.hash.data.getD k 0 = b.hash.data[k] := by
        unfold Array.getD; simp only [hk2, ↓reduceDIte]; rfl
      rw [hgetA, hgetB] at hbyte
      exact UInt8.toNat_inj.mp hbyte
  cases a with | mk ha =>
  cases b with | mk hb =>
  cases ha; cases hb
  simp only at hdata
  subst hdata
  rfl

/-- Representation of a base Goldilocks field element in `SourceValue Fp`. -/
def RepFp (x : CertiFri.P3.Goldilocks) (v : Aiur.SourceValue Fp) : Prop :=
  v = .field (baseToFp x)

/-- Representation of a quadratic extension element `[Field; 2]` in `SourceValue Fp`. -/
def RepExt (e : CertiFri.P3.GoldilocksExt) (v : Aiur.SourceValue Fp) : Prop :=
  v = .tuple [.field (baseToFp e.c0), .field (baseToFp e.c1)]

/-- Representation of an 8-byte little-endian `UInt64::U64` (`[UInt8::U8; 8]`). -/
def RepU64 (x : UInt64) (v : Aiur.SourceValue Fp) : Prop :=
  v = .tuple (List.ofFn fun i : Fin 8 => .field ((((x.toNat / 2 ^ (8 * i.val)) % 256) : Nat) : Fp))

/-- Representation of a 32-byte `CertiFri.P3.Digest` (`[UInt8::U8; 32]` / 4×8 bytes). -/
def RepDigest (d : CertiFri.P3.Digest) (v : Aiur.SourceValue Fp) : Prop :=
  v = .tuple (List.ofFn fun i : Fin 32 => .field ((d.toBytes.data.getD i.val 0).toNat : Fp))

/-- A byte string hashed by an observed `MultiStark` execution (`Blake3::hash`). -/
def HashedInMultiStark (calls : List (Aiur.Generic.SourceSemantics.Call Fp))
    (bytes : ByteArray) : Prop :=
  ∃ c ∈ calls, c.name = blake3HashEntry ∧ ∃ input : Aiur.SourceValue Fp,
    c.args = [input] ∧
    Aiur.Library.Bytes.RepByteStream byteStreamEnumSymbol c.heap bytes.data.toList input

/-- A concrete BLAKE3 collision exhibited by an observed `MultiStark` execution against
any byte string in `anchors` (e.g. `[vkBytes, claimsBytes]`) or against another byte string
the run itself hashed. -/
def MultiStarkCollision (anchors : List ByteArray)
    (calls : List (Aiur.Generic.SourceSemantics.Call Fp)) : Prop :=
  ∃ (b₁ b₂ : ByteArray),
    (b₁ ∈ anchors ∨ HashedInMultiStark calls b₁) ∧
    HashedInMultiStark calls b₂ ∧
    b₁ ≠ b₂ ∧
    Address.blake3Pure b₁ = Address.blake3Pure b₂

/-- If an observed run hashes `b` whose packed BLAKE3 digest equals `packDigest8 (blake3Pure a)`
for an anchor `a ∈ anchors`, then either `b = a` or a concrete BLAKE3 collision occurred. -/
theorem hashed_eq_or_collision {anchors : List ByteArray}
    {calls : List (Aiur.Generic.SourceSemantics.Call Fp)} {a b : ByteArray}
    (ha : a ∈ anchors) (hb : HashedInMultiStark calls b)
    (hdig : packDigest8 (Address.blake3Pure b) = packDigest8 (Address.blake3Pure a)) :
    b = a ∨ MultiStarkCollision anchors calls := by
  by_cases hEq : b = a
  · exact Or.inl hEq
  · refine Or.inr ⟨a, b, Or.inl ha, hb, Ne.symm hEq,
      (packDigest8_inj (address_blake3Pure_size b) (address_blake3Pure_size a) hdig).symm⟩

end Ix.Cert.MultiStarkRefinement
