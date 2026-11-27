import MultiStark.Program
import MultiStark.CompressGL
import MultiStark.BN.KzgPackedTerminal
import MultiStark.CompressFinal
import Ix.Cert.MultiStarkRefinement.ProgramPin
import Ix.Cert.Aggr.Shapes

/-! # Kernel-Checked AST & Source-Identity Pins for the Lean-Compiled Aiur Compression Pipeline

Mechanically pins (by Lean kernel reduction `decide` and pure structural proofs — zero `sorry`,
zero custom `axiom`, zero `native_decide`, zero `bv_decide`, strictly
`[propext, Classical.choice, Quot.sound]`) every pure deployed Lean Aiur compression program
and shared packed-SHPLONK verifier module in the L3 / BLS12-381 Aiur compression chain:

1. **Stage 0 (`MultiStark.aggregateProgram` / `MultiStark::ix_aggr`):**
   Re-exports `Ix.Cert.Aggr.aggregateProgram_ast_pinned` and `aggregateDigest_eq`.
2. **Stage 1 (`MultiStark.compressWrapProgram` / `CompressWrap::verify_root`):**
   Pins `CompressWrap::verify_root` (reserved-zero assertion, BLAKE3 digest binding of key
   and claims, call to `MultiStark::verify_multi_stark_proof`), `CompressWrap::statement_bytes`
   (exact 20-byte domain tag `"ix/compress-wrap/v1\0"`), and the shared `StarkVerifier` core,
   lifted from `Nat` to Goldilocks `Fp`.
3. **Stage 2 (`MultiStark.CompressGL.program` / `CompressGL::verify_root`):**
   Pins `CompressGL = CompressWrap` alias over `BN254.F` with emulated Goldilocks arithmetic.
4. **Stage 3 & 4 Shared Packed-SHPLONK Verifier & Fold Modules
   (`MultiStark.Source.{compressBN, compressBNPacked, kzgPackedDeserialize, kzgPackedTerminal}`):**
   - `CompressBN::previous`: CALL tag `1`, match arm `[1]` (`gl_entry` + `[0;8]` + statement) vs
     `bn_entry` + `policy_digest` + `stage - 1` + statement + unpacked accumulator (`≥ 7` asserts).
   - `CompressBNPacked::{fold_domain, fold_weight, fold}`: exact 31-byte fold domain separator
     `"ix/aiur/kzg/fold-transcript/v1\0"`, nonzero fold-weight assertion, MSM + G1 addition.
   - `KzgPackedDeserialize::{chain_policy, key, proof}`: exact `"IXAUKG01"`, `"IXAUSK02"`,
     `"IXAUSP01"` magics and 128-byte pairing anchor checks.
   - `KzgPackedTerminal::{key, verify_key, verify}`: embedded fixed-table packed-SHPLONK
     key reconstruction and verification shared verbatim by `CompressNarrowFixed` and
     `CompressFinalNarrow` (including nonzero `zeta` assertion and `KzgPcsPacked::reduce`).
5. **Terminal Relation & Narrow-Terminal Configuration Validation (`MultiStark.Final.source`
   & `validateFinalNarrowConfig`):**
   - For any `cfg` accepted by pure `MultiStark.Final.source cfg`, proves exact configuration
     validity (`FinalConfigValid cfg`) and kernel-checked AST pins of
     `CompressFinal::{verify_v1, verify_accumulator_v1, statement, anchor_stream}`.
   - Formalizes `FinalNarrowConfigValid` and pure `validateFinalNarrowConfig` (mirroring
     `MultiStark/MultiStark/CompressFinalNarrow.lean:137-148`) and proves constructive rejection
     of stage `< 2` and header word sums `≠ 21`.

**Axiom-hygiene note on `Blake3.Rust.hash`:** The three key-embedding wrapper functions
`MultiStark.{CompressGLFixed,NarrowFixed,FinalNarrow}.source` call `@[extern]`
`Blake3.Rust.hash` (whose Lean definition pulls in `Blake3.HasherOps.hash._native.native_decide.ax_1✝`),
so theorem statements in this certified audit layer deliberately avoid naming those three
`Blake3.Rust`-dependent wrappers and instead pin the pure shared verifier/fold/terminal ASTs
(`compressWrapProgram`, `CompressGL.program`, `kzgPackedTerminal`, `compressBNPacked`,
`kzgPackedDeserialize`, `Final.source`) plus typed `NarrowFixedAstPinned` / `FinalNarrowAstPinned`
predicates — keeping every audited theorem strictly within `[propext, Classical.choice, Quot.sound]`.
-/

namespace Ix.Cert.AiurCompression

open Aiur Aiur.Generic Aiur.Modules
open Ix.Cert.MultiStarkRefinement
open Ix.Cert.Aggr

/-! ## 1. Additional Kernel-Reducible AST Helpers (Globals & Module Aliases) -/

mutual
/-- Collect all global constant references (`mod::CONST`) appearing in a `Generic.Expr`. -/
def exprGlobals {α : Type} : Generic.Expr α → List String
  | .literal _ | .var _ => []
  | .global name _ => [name]
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs => exprListGlobals xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _
  | .project x _ | .store x | .load x | .hint _ x _ | .neg x | .control _ x =>
      exprGlobals x
  | .letValue _ v b | .binary _ v b => exprGlobals v ++ exprGlobals b
  | .call _ _ args => exprListGlobals args
  | .matchValue s arms => exprGlobals s ++ exprArmsGlobals arms

def exprListGlobals {α : Type} : List (Generic.Expr α) → List String
  | [] => []
  | x :: xs => exprGlobals x ++ exprListGlobals xs

def exprArmsGlobals {α : Type} : List (Generic.Pattern α × Generic.Expr α) → List String
  | [] => []
  | (_, e) :: arms => exprGlobals e ++ exprArmsGlobals arms
end

mutual
theorem exprGlobals_map {α β : Type} (f : α → β) :
    ∀ (e : Generic.Expr α), exprGlobals (e.map f) = exprGlobals e
  | .literal _ => by simp [Generic.Expr.map, exprGlobals]
  | .var _ => by simp [Generic.Expr.map, exprGlobals]
  | .global _ _ => by simp [Generic.Expr.map, exprGlobals]
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs => by
      simp only [Generic.Expr.map, exprGlobals]
      exact exprListGlobals_map f xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _
  | .project x _ | .store x | .load x | .hint _ x _ | .neg x | .control _ x => by
      simp only [Generic.Expr.map, exprGlobals]
      exact exprGlobals_map f x
  | .letValue _ v b | .binary _ v b => by
      simp only [Generic.Expr.map, exprGlobals, exprGlobals_map f v, exprGlobals_map f b]
  | .call _ _ args => by
      simp only [Generic.Expr.map, exprGlobals, exprListGlobals_map f args]
  | .matchValue s arms => by
      simp only [Generic.Expr.map, exprGlobals, exprGlobals_map f s, exprArmsGlobals_map f arms]

theorem exprListGlobals_map {α β : Type} (f : α → β) :
    ∀ (xs : List (Generic.Expr α)), exprListGlobals (xs.map (Generic.Expr.map f)) = exprListGlobals xs
  | [] => rfl
  | x :: xs => by
      simp only [List.map_cons, exprListGlobals, exprGlobals_map f x, exprListGlobals_map f xs]

theorem exprArmsGlobals_map {α β : Type} (f : α → β) :
    ∀ (arms : List (Generic.Pattern α × Generic.Expr α)),
      exprArmsGlobals (arms.map fun arm => (arm.1.map f, arm.2.map f)) = exprArmsGlobals arms
  | [] => rfl
  | (_, e) :: arms => by
      simp only [List.map_cons, exprArmsGlobals, exprGlobals_map f e, exprArmsGlobals_map f arms]
end

/-- Check whether module `modName` is an alias of module `targetName` (with zero type args). -/
def hasModuleAlias {α : Type} (prog : Modules.Program α) (modName targetName : String) : Bool :=
  match prog.findModule? modName with
  | some m =>
      match m.body with
      | .alias (.mk t []) => t == targetName
      | _ => false
  | none => false

private theorem list_find?_map_eq {α β : Type} (g : α → β) (p : β → Bool) (q : α → Bool)
    (hpq : ∀ a, p (g a) = q a) (xs : List α) :
    (xs.map g).find? p = (xs.find? q).map g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.find?_cons, hpq]
    cases q x <;> simp [ih]

theorem hasModuleAlias_map {α β : Type} (f : α → β) (prog : Modules.Program α)
    (modName targetName : String) :
    hasModuleAlias (prog.map f) modName targetName = hasModuleAlias prog modName targetName := by
  unfold hasModuleAlias Modules.Program.findModule? Modules.Program.map
  rw [list_find?_map_eq _ _ (fun m => m.name == modName) (fun _ => rfl)]
  cases h : prog.modules.find? (fun m => m.name == modName) with
  | none => rfl
  | some m =>
    simp only [Option.map_some]
    cases m.body with
    | definitions _ => rfl
    | «alias» t =>
      cases t with
      | mk name args => cases args <;> rfl

theorem hasModuleAlias_append_right {α : Type} (p q : Modules.Program α)
    (modName targetName : String) (hNotInP : p.findModule? modName = none) :
    hasModuleAlias (p.append q) modName targetName = hasModuleAlias q modName targetName := by
  unfold hasModuleAlias Modules.Program.findModule? Modules.Program.append at *
  rw [List.find?_append, hNotInP]
  rfl

theorem fnHasCallsAndAsserts_append_right {α : Type} (p q : Modules.Program α)
    (modName fnName : String) (callees : List String) (minAsserts : Nat)
    (hNotInP : p.findModule? modName = none) :
    fnHasCallsAndAsserts (p.append q) modName fnName callees minAsserts =
      fnHasCallsAndAsserts q modName fnName callees minAsserts := by
  unfold fnHasCallsAndAsserts
  rw [findModuleFunction?_append_right p q modName fnName hNotInP]

/-- Check whether `modName::fnName` in `prog` references the exact global list `expectedGlobals`
in order (used to pin inline ASCII domain separator byte sequences). -/
def fnGlobalsEq {α : Type} (prog : Modules.Program α)
    (modName fnName : String) (expectedGlobals : List String) : Bool :=
  match findModuleFunction? prog modName fnName with
  | none => false
  | some fdecl => exprGlobals fdecl.body == expectedGlobals

theorem fnGlobalsEq_map {α β : Type} (f : α → β) (prog : Modules.Program α)
    (modName fnName : String) (expectedGlobals : List String) :
    fnGlobalsEq (prog.map f) modName fnName expectedGlobals =
      fnGlobalsEq prog modName fnName expectedGlobals := by
  unfold fnGlobalsEq
  rw [findModuleFunction?_map]
  cases findModuleFunction? prog modName fnName with
  | none => rfl
  | some fdecl => simp only [Option.map_some, exprGlobals_map]

theorem fnGlobalsEq_append_right {α : Type} (p q : Modules.Program α)
    (modName fnName : String) (expectedGlobals : List String)
    (hNotInP : p.findModule? modName = none) :
    fnGlobalsEq (p.append q) modName fnName expectedGlobals =
      fnGlobalsEq q modName fnName expectedGlobals := by
  unfold fnGlobalsEq
  rw [findModuleFunction?_append_right p q modName fnName hNotInP]

/-- Check whether `modName::fnName` in a `Nat` program contains every required numeric literal. -/
def fnHasLiterals (prog : Modules.Program Nat) (modName fnName : String)
    (required : List Nat) : Bool :=
  match findModuleFunction? prog modName fnName with
  | none => false
  | some fdecl =>
      let lits := exprLiterals fdecl.body
      required.all (fun n => lits.contains n)

private theorem findModuleFunction?_map_modules {α : Type} (prog : Modules.Program α)
    (f : Modules.Module α → Modules.Module α)
    (hname : ∀ m, (f m).name = m.name)
    (hfns : ∀ m,
      (match (f m).body with | .definitions d => some d.program.functions | .alias _ => none) =
      (match m.body with | .definitions d => some d.program.functions | .alias _ => none))
    (modName fnName : String) :
    findModuleFunction? { prog with modules := prog.modules.map f } modName fnName =
      findModuleFunction? prog modName fnName := by
  unfold findModuleFunction? Modules.Program.findModule?
  rw [list_find?_map_eq f (fun m => m.name == modName) (fun m => m.name == modName)
    (fun m => by rw [hname m])]
  cases prog.modules.find? (fun m => m.name == modName) with
  | none => rfl
  | some m =>
    simp only [Option.map_some, bind, Option.bind]
    have hf := hfns m
    cases h1 : (f m).body <;> cases h2 : m.body <;> simp [h1, h2] at hf ⊢
    simp only [Generic.Program.findFunction?, hf]

private theorem fnHasCallsAndAsserts_map_modules {α : Type} (prog : Modules.Program α)
    (f : Modules.Module α → Modules.Module α)
    (hname : ∀ m, (f m).name = m.name)
    (hfns : ∀ m,
      (match (f m).body with | .definitions d => some d.program.functions | .alias _ => none) =
      (match m.body with | .definitions d => some d.program.functions | .alias _ => none))
    (modName fnName : String) (callees : List String) (minAsserts : Nat) :
    fnHasCallsAndAsserts { prog with modules := prog.modules.map f } modName fnName callees minAsserts =
      fnHasCallsAndAsserts prog modName fnName callees minAsserts := by
  unfold fnHasCallsAndAsserts
  rw [findModuleFunction?_map_modules prog f hname hfns modName fnName]

private theorem except_guard_ok {α : Type} {c : Bool} {msg : String} {jp : Unit → Except String α} {x : α}
    (h : (if c = true then jp () else (throw msg : Except String Unit) >>= jp) = .ok x) :
    c = true ∧ jp () = .ok x := by
  cases c
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · simp at h
    exact ⟨rfl, h⟩

/-! ## 2. Stage 1 Pin: `MultiStark.compressWrapSource` & `MultiStark.compressWrapProgram` -/

/-- Entry point of the Goldilocks compression wrapper stage. -/
def compressWrapEntry : String := "CompressWrap::verify_root"

/-- Entry point of the fixed-key narrow stage (`MultiStark/MultiStark/CompressNarrowFixed.lean:60`). -/
def compressNarrowFixedEntry : String := "CompressNarrowFixed::step_v1"

/-- Entry point of the narrow terminal stage (`MultiStark/MultiStark/CompressFinalNarrow.lean:125`). -/
def compressFinalNarrowEntry : String := "CompressFinalNarrow::verify_accumulator_v1"

/-- Exact 20 `UInt8::BYTE_*` global constants encoding `"ix/compress-wrap/v1\0"` inside
`CompressWrap::statement_bytes`. -/
def compressWrapDomainGlobals : List String :=
  [ "UInt8::BYTE_105", "UInt8::BYTE_120", "UInt8::BYTE_47",  "UInt8::BYTE_99"
  , "UInt8::BYTE_111", "UInt8::BYTE_109", "UInt8::BYTE_112", "UInt8::BYTE_114"
  , "UInt8::BYTE_101", "UInt8::BYTE_115", "UInt8::BYTE_115", "UInt8::BYTE_45"
  , "UInt8::BYTE_119", "UInt8::BYTE_114", "UInt8::BYTE_97",  "UInt8::BYTE_112"
  , "UInt8::BYTE_47",  "UInt8::BYTE_118", "UInt8::BYTE_49",  "UInt8::BYTE_0" ]

/-- Required callees in `CompressWrap::verify_root`. -/
def compressWrapVerifyRootCalls : List String :=
  [ "StarkIO::read_byte_stream"
  , "Blake3::hash"
  , "statement_bytes"
  , "Blake3::pack_digest"
  , "MultiStark::verify_multi_stark_proof" ]

/-- AST pin predicate for `CompressWrap` (shared by Goldilocks `compressWrapProgram` and
BN254 `CompressGL.program`). -/
def CompressWrapAstPinned {α : Type} (prog : Modules.Program α) : Bool :=
  fnHasCallsAndAsserts prog "CompressWrap" "verify_root" compressWrapVerifyRootCalls 2 &&
  fnHasCallsAndAsserts prog "CompressWrap" "statement_bytes"
    ["StarkHash::b3_flatten_onto", "StarkVerifier::b8_onto",
     "StarkHash::b3_w4_onto", "UInt32::from_bytes"] 0 &&
  fnGlobalsEq prog "CompressWrap" "statement_bytes" compressWrapDomainGlobals &&
  RecursionVerifierAstPinned prog

theorem compressWrapSource_ast_pinned :
    CompressWrapAstPinned MultiStark.compressWrapSource = true := by
  decide

private theorem goldilocks_libs_disjoint_compressWrap :
    let libPrefix : Modules.Program _root_.MultiStark.F :=
      (Aiur.Library.Blake3.Goldilocks.program.append
        (Aiur.Library.Option.declarations.toField _root_.MultiStark.F)).append
        Aiur.Library.Field.Goldilocks.program
    ["CompressWrap", "MultiStark", "SystemDeserialize", "StarkVerifier", "Pcs"].all
      (fun name => (libPrefix.findModule? name).isNone) = true := by
  decide

private theorem findModule?_none_of_mem {α : Type} {prog : Modules.Program α}
    {names : List String} (h : names.all (fun n => (prog.findModule? n).isNone) = true)
    {name : String} (hmem : name ∈ names) : prog.findModule? name = none := by
  have hall := List.all_eq_true.mp h name hmem
  exact Option.isNone_iff_eq_none.mp hall

/-- Kernel-checked AST pin of the deployed Goldilocks `MultiStark.compressWrapProgram`. -/
theorem compressWrapProgram_ast_pinned :
    CompressWrapAstPinned MultiStark.compressWrapProgram = true := by
  unfold MultiStark.compressWrapProgram MultiStark.withLibraries CompressWrapAstPinned
    RecursionVerifierAstPinned
  have hd := goldilocks_libs_disjoint_compressWrap
  dsimp only at hd
  have hCW := findModule?_none_of_mem hd (by decide : "CompressWrap" ∈ _)
  have hMS := findModule?_none_of_mem hd (by decide : "MultiStark" ∈ _)
  have hSD := findModule?_none_of_mem hd (by decide : "SystemDeserialize" ∈ _)
  have hSV := findModule?_none_of_mem hd (by decide : "StarkVerifier" ∈ _)
  have hPcs := findModule?_none_of_mem hd (by decide : "Pcs" ∈ _)
  simp only [fnHasCallsAndAsserts_append_right _ _ _ _ _ _ hCW,
    fnHasCallsAndAsserts_append_right _ _ _ _ _ _ hMS,
    fnHasCallsAndAsserts_append_right _ _ _ _ _ _ hSD,
    fnHasCallsAndAsserts_append_right _ _ _ _ _ _ hSV,
    fnHasCallsAndAsserts_append_right _ _ _ _ _ _ hPcs,
    fnGlobalsEq_append_right _ _ _ _ _ hCW]
  simp only [Modules.Program.toField, fnHasCallsAndAsserts_map, fnGlobalsEq_map]
  exact compressWrapSource_ast_pinned

/-! ## 3. Stage 2 Pin: `MultiStark.CompressGL.program` -/

/-- AST pin predicate for `MultiStark.CompressGL.program`: verifies both the
`module CompressGL = CompressWrap` alias AND the full `CompressWrapAstPinned` core. -/
def CompressGLAstPinned {α : Type} (prog : Modules.Program α) : Bool :=
  hasModuleAlias prog "CompressGL" "CompressWrap" &&
  CompressWrapAstPinned prog

theorem compressGLSource_ast_pinned :
    CompressGLAstPinned MultiStark.CompressGL.source = true := by
  decide

private theorem bn254_gl_libs_disjoint_compressGL :
    let libPrefix : Modules.Program MultiStark.CompressGL.F :=
      (Aiur.Library.Blake3.BN254.program.append
        (Aiur.Library.Option.declarations.toField MultiStark.CompressGL.F)).append
        Aiur.Library.Field.Goldilocks.Emulated.program
    ["CompressGL", "CompressWrap", "MultiStark", "SystemDeserialize", "StarkVerifier", "Pcs"].all
      (fun name => (libPrefix.findModule? name).isNone) = true := by
  decide

/-- Kernel-checked AST pin of the deployed BN254 `MultiStark.CompressGL.program`. -/
theorem compressGLProgram_ast_pinned :
    CompressGLAstPinned MultiStark.CompressGL.program = true := by
  unfold MultiStark.CompressGL.program CompressGLAstPinned CompressWrapAstPinned
    RecursionVerifierAstPinned
  have hd := bn254_gl_libs_disjoint_compressGL
  dsimp only at hd
  have hGL := findModule?_none_of_mem hd (by decide : "CompressGL" ∈ _)
  have hCW := findModule?_none_of_mem hd (by decide : "CompressWrap" ∈ _)
  have hMS := findModule?_none_of_mem hd (by decide : "MultiStark" ∈ _)
  have hSD := findModule?_none_of_mem hd (by decide : "SystemDeserialize" ∈ _)
  have hSV := findModule?_none_of_mem hd (by decide : "StarkVerifier" ∈ _)
  have hPcs := findModule?_none_of_mem hd (by decide : "Pcs" ∈ _)
  simp only [hasModuleAlias_append_right _ _ _ _ hGL,
    fnHasCallsAndAsserts_append_right _ _ _ _ _ _ hCW,
    fnHasCallsAndAsserts_append_right _ _ _ _ _ _ hMS,
    fnHasCallsAndAsserts_append_right _ _ _ _ _ _ hSD,
    fnHasCallsAndAsserts_append_right _ _ _ _ _ _ hSV,
    fnHasCallsAndAsserts_append_right _ _ _ _ _ _ hPcs,
    fnGlobalsEq_append_right _ _ _ _ _ hCW]
  simp only [Modules.Program.toField, hasModuleAlias_map, fnHasCallsAndAsserts_map, fnGlobalsEq_map]
  exact compressGLSource_ast_pinned

/-! ## 4. Stage 3 & 4 Shared Packed-SHPLONK Verifier, Policy & Fold AST Pins -/

/-- Exact 31 `UInt8::BYTE_*` global constants in `CompressBNPacked::fold_domain`
(prepended in reverse order to form `"ix/aiur/kzg/fold-transcript/v1\0"`). -/
def foldDomainGlobalsRev : List String :=
  [ "UInt8::BYTE_0",   "UInt8::BYTE_49",  "UInt8::BYTE_118", "UInt8::BYTE_47"
  , "UInt8::BYTE_116", "UInt8::BYTE_112", "UInt8::BYTE_105", "UInt8::BYTE_114"
  , "UInt8::BYTE_99",  "UInt8::BYTE_115", "UInt8::BYTE_110", "UInt8::BYTE_97"
  , "UInt8::BYTE_114", "UInt8::BYTE_116", "UInt8::BYTE_45",  "UInt8::BYTE_100"
  , "UInt8::BYTE_108", "UInt8::BYTE_111", "UInt8::BYTE_102", "UInt8::BYTE_47"
  , "UInt8::BYTE_103", "UInt8::BYTE_122", "UInt8::BYTE_107", "UInt8::BYTE_47"
  , "UInt8::BYTE_114", "UInt8::BYTE_117", "UInt8::BYTE_105", "UInt8::BYTE_97"
  , "UInt8::BYTE_47",  "UInt8::BYTE_120", "UInt8::BYTE_105" ]

/-- Required callees in `CompressNarrowFixed::step_v1`. -/
def narrowFixedStepCalls : List String :=
  [ "CompressBN::digest_onto"
  , "KzgIO::digest_word"
  , "KzgIO::sized_channel"
  , "Blake3::pack_digest"
  , "KzgBlake3::hash_input"
  , "KzgPackedDeserialize::chain_policy"
  , "key_digest"
  , "KzgPackedTerminal::key"
  , "KzgIO::equal_bytes"
  , "KzgDeserialize::claims"
  , "KzgIO::channel"
  , "CompressBN::previous"
  , "KzgPackedTerminal::verify_key"
  , "KzgPackedDeserialize::proof"
  , "CompressBNPacked::fold"
  , "KzgAccumulator::pack" ]

/-- AST pin predicate for `CompressNarrowFixed::step_v1`. -/
def NarrowFixedAstPinned {α : Type} (prog : Modules.Program α) : Bool :=
  fnHasCallsAndAsserts prog "CompressNarrowFixed" "step_v1" narrowFixedStepCalls 3

/-- Required callees of `KzgPackedTerminal::verify_key` (the embedded-key packed-SHPLONK
verifier shared by both `CompressNarrowFixed` and `CompressFinalNarrow`). -/
def kzgPackedTerminalVerifyKeyCalls : List String :=
  [ "KzgPackedShape::frames"
  , "KzgPackedVerifier::observe_key"
  , "KzgTranscript::observe_input"
  , "KzgPcsPacked::commitment_bytes"
  , "KzgTranscript::observe_fields"
  , "KzgTranscript::observe_claims"
  , "KzgTranscript::sample"
  , "KzgTranscript::observe_field"
  , "KzgAlgebra::claims_accumulator"
  , "Fields::is_zero"
  , "verify_frames"
  , "KzgPcsPacked::rounds"
  , "KzgPcsPacked::reduce" ]

/-- AST pin predicate for `KzgPackedTerminal` (`key`, `verify_key`, `verify`). -/
def KzgPackedTerminalAstPinned {α : Type} (prog : Modules.Program α) : Bool :=
  fnHasCallsAndAsserts prog "KzgPackedTerminal" "key"
    ["key_words", "KzgIO::magic", "KzgIO::blob", "KzgIO::u32",
     "UInt32::less_than_fields", "KzgDeserialize::supported_power",
     "KzgIO::point", "KzgIO::read_bytes", "circuits", "KzgPackedDeserialize::fixed"] 2 &&
  fnHasCallsAndAsserts prog "KzgPackedTerminal" "verify_key" kzgPackedTerminalVerifyKeyCalls 1 &&
  fnHasCallsAndAsserts prog "KzgPackedTerminal" "verify"
    ["KzgIO::digest_bytes", "KzgIO::sized_channel", "KzgIO::channel",
     "Blake3::pack_digest", "KzgBlake3::hash_input", "verify_key", "key",
     "KzgPackedDeserialize::proof", "KzgDeserialize::claims", "KzgAccumulator::pack"] 1

/-- Kernel-checked AST pin of the deployed pure `MultiStark.Source.kzgPackedTerminal`
(shared verbatim by both `CompressNarrowFixed` and `CompressFinalNarrow`). -/
theorem kzgPackedTerminal_ast_pinned :
    KzgPackedTerminalAstPinned MultiStark.Source.kzgPackedTerminal = true := by
  decide

/-- Kernel-checked AST pin of `MultiStark.Source.compressBN` (`CompressBN::previous` checks
CALL namespace `1`, GL entry + `[0;8]` reserved + statement at stage `1`, and BN entry +
policy + `stage - 1` + statement + unpacked accumulator at later stages). -/
theorem compressBN_previous_ast_pinned :
    fnHasCallsAndAsserts MultiStark.Source.compressBN "CompressBN" "previous"
      ["take8", "KzgAccumulator::unpack"] 7 = true ∧
    (match findModuleFunction? MultiStark.Source.compressBN "CompressBN" "previous" with
     | some fdecl => exprMatchLitArms fdecl.body
     | none => []) = [1] := by
  decide

/-- Kernel-checked AST pin of `MultiStark.Source.compressBNPacked` (`fold_domain` pins exact
`"ix/aiur/kzg/fold-transcript/v1\0"`, `fold_weight` asserts nonzero weight, `fold` calls
`fold_weight`, `KzgMsm::msm`, `BN254G1::add`). -/
theorem compressBNPacked_fold_ast_pinned :
    fnGlobalsEq MultiStark.Source.compressBNPacked "CompressBNPacked" "fold_domain"
      foldDomainGlobalsRev = true ∧
    fnHasCallsAndAsserts MultiStark.Source.compressBNPacked "CompressBNPacked" "fold_weight"
      ["KzgIO::fields_to_bytes", "BN254G1::point_list_bytes", "CompressBN::digest_onto",
       "KzgIO::prepend4", "UInt32::to_bytes", "KzgIO::digest_word",
       "KzgTranscript::sample", "KzgTranscript::observe_bytes", "fold_domain",
       "Fields::is_zero"] 1 = true ∧
    fnHasCallsAndAsserts MultiStark.Source.compressBNPacked "CompressBNPacked" "fold"
      ["fold_weight", "KzgMsm::msm", "BN254G1::add"] 0 = true := by
  decide

/-- Kernel-checked AST pin of `MultiStark.Source.kzgPackedDeserialize`:
- `chain_policy` enforces `"IXAUKG01"` (`[73, 88, 65, 85, 75, 71, 48, 49]`) + 128-byte anchors;
- `key` enforces `"IXAUSK02"` (`[73, 88, 65, 85, 83, 75, 48, 50]`) + domain `< 29` + 128-byte anchors;
- `proof` enforces `"IXAUSP01"` (`[73, 88, 65, 85, 83, 80, 48, 49]`). -/
theorem kzgPackedDeserialize_formats_ast_pinned :
    fnHasLiterals MultiStark.Source.kzgPackedDeserialize "KzgPackedDeserialize" "chain_policy"
      [73, 88, 65, 85, 75, 71, 48, 49, 128] = true ∧
    fnHasLiterals MultiStark.Source.kzgPackedDeserialize "KzgPackedDeserialize" "key"
      [73, 88, 65, 85, 83, 75, 48, 50, 29, 0, 1, 28, 128] = true ∧
    fnHasLiterals MultiStark.Source.kzgPackedDeserialize "KzgPackedDeserialize" "proof"
      [73, 88, 65, 85, 83, 80, 48, 49] = true := by
  decide

/-! ## 5. Stage 4 Pins: `MultiStark.Final.source` & Narrow-Terminal Configuration Validation -/

/-- AST pin predicate for the pure `CompressFinal` module (`MultiStark.Final.source`). -/
def CompressFinalAstPinned {α : Type} (prog : Modules.Program α) : Bool :=
  fnHasCallsAndAsserts prog "CompressFinal" "verify_accumulator_v1"
    ["statement", "configuration", "KzgIO::digest_word", "UInt32::less_than_fields",
     "CompressBN::step_v1", "KzgIO::equal_bytes", "anchor_stream",
     "BN254G1Encoding::from_chunks", "BN254G1::to_raw"] 2 &&
  fnHasCallsAndAsserts prog "CompressFinal" "verify_v1"
    ["statement", "configuration", "KzgIO::digest_word", "UInt32::less_than_fields",
     "CompressBN::step_v1", "KzgIO::equal_bytes", "anchor_stream",
     "BN254Pairing::check_chunks"] 2 &&
  fnHasCallsAndAsserts prog "CompressFinal" "statement"
    ["BN254G1Encoding::chunk_bytes", "word"] 0 &&
  fnHasCallsAndAsserts prog "CompressFinal" "anchor_stream"
    ["KzgIO::prepend_words32", "Blake3::address_from_fields"] 0

private theorem compressFinalAstPinned_map_modules {α : Type} (prog : Modules.Program α)
    (f : Modules.Module α → Modules.Module α)
    (hname : ∀ m, (f m).name = m.name)
    (hfns : ∀ m,
      (match (f m).body with | .definitions d => some d.program.functions | .alias _ => none) =
      (match m.body with | .definitions d => some d.program.functions | .alias _ => none)) :
    CompressFinalAstPinned { prog with modules := prog.modules.map f } =
      CompressFinalAstPinned prog := by
  unfold CompressFinalAstPinned
  simp only [fnHasCallsAndAsserts_map_modules prog f hname hfns]

/-- Validated configuration invariants enforced by `MultiStark.Final.Configuration.validate`. -/
structure FinalConfigValid (cfg : MultiStark.Final.Configuration) : Prop where
  policyDigest_len : cfg.policyDigest.length = 8
  policyDigest_u32 : ∀ w ∈ cfg.policyDigest, w < 2 ^ 32
  anchors_len : cfg.anchors.length = 128
  anchors_u8 : ∀ b ∈ cfg.anchors, b < 256
  minStage_one_or_two : cfg.minStage = 1 ∨ cfg.minStage = 2
  stage_ordered : cfg.minStage ≤ cfg.maxStage
  maxStage_u32 : cfg.maxStage < 2 ^ 32

/-- Pure export-time soundness + AST pin for `MultiStark.Final.source`:
whenever `MultiStark.Final.source cfg = .ok prog`, BOTH `FinalConfigValid cfg` AND
`CompressFinalAstPinned prog = true` hold (strictly `[propext, Classical.choice, Quot.sound]`)! -/
theorem finalSource_ok_spec {cfg : MultiStark.Final.Configuration} {prog : Modules.Program Nat}
    (hok : MultiStark.Final.source cfg = .ok prog) :
    FinalConfigValid cfg ∧ CompressFinalAstPinned prog = true := by
  unfold MultiStark.Final.source at hok
  cases hval : cfg.validate with
  | error e =>
    simp [bind, Except.bind, hval] at hok
  | ok u =>
    have hval' := hval
    unfold MultiStark.Final.Configuration.validate at hval'
    obtain ⟨hpolT, hval'⟩ := except_guard_ok hval'
    obtain ⟨hancT, hval'⟩ := except_guard_ok hval'
    obtain ⟨hstgT, _⟩ := except_guard_ok hval'
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
      List.all_eq_true] at hpolT hancT hstgT
    have hValid : FinalConfigValid cfg :=
      ⟨hpolT.1, hpolT.2, hancT.1, hancT.2, hstgT.1.1, hstgT.1.2, hstgT.2⟩
    refine ⟨hValid, ?_⟩
    simp only [bind, Except.bind, hval, pure, Except.pure] at hok
    injection hok with hok
    subst hok
    refine (compressFinalAstPinned_map_modules _ _ ?_ ?_).trans ?_
    · intro _; rfl
    · intro m; cases m.body <;> rfl
    · decide

/-- Pure mirror of `MultiStark.FinalNarrow.Header` (`tag`, `key`, `values`). -/
structure NarrowClaimHeader where
  tag : Nat
  key : Nat
  values : Nat
  deriving DecidableEq, Repr

/-- Required callees of `CompressFinalNarrow::verify_accumulator_v1`. -/
def finalNarrowVerifyCalls : List String :=
  [ "statement"
  , "configuration"
  , "KzgIO::sized_channel"
  , "Blake3::pack_digest"
  , "KzgBlake3::hash_input"
  , "KzgPackedDeserialize::chain_policy"
  , "key_digest"
  , "KzgPackedTerminal::key"
  , "KzgIO::equal_bytes"
  , "anchor_stream"
  , "KzgDeserialize::claims"
  , "KzgIO::channel"
  , "previous"
  , "values"
  , "KzgPackedTerminal::verify_key"
  , "KzgPackedDeserialize::proof"
  , "CompressBNPacked::fold"
  , "BN254G1Encoding::from_chunks"
  , "KzgAccumulator::pack"
  , "BN254G1::to_raw" ]

/-- AST pin predicate for `CompressFinalNarrow` (covering all 5 core functions). -/
def FinalNarrowAstPinned {α : Type} (prog : Modules.Program α) : Bool :=
  fnHasCallsAndAsserts prog "CompressFinalNarrow" "verify_accumulator_v1" finalNarrowVerifyCalls 1 &&
  fnHasCallsAndAsserts prog "CompressFinalNarrow" "values"
    ["header", "Lists::length", "Lists::concat", "values"] 4 &&
  fnHasCallsAndAsserts prog "CompressFinalNarrow" "previous"
    ["CompressBN::take8", "KzgAccumulator::unpack"] 3 &&
  fnHasCallsAndAsserts prog "CompressFinalNarrow" "statement"
    ["BN254G1Encoding::chunk_bytes", "word"] 0 &&
  fnHasCallsAndAsserts prog "CompressFinalNarrow" "anchor_stream"
    ["KzgIO::prepend_words32", "Blake3::address_from_fields"] 0

/-- Pure configuration & keyed-claim-header validator mirroring lines 137–148 of
`MultiStark/MultiStark/CompressFinalNarrow.lean` (zero FFI, pure Lean). -/
def validateFinalNarrowConfig (cfg : MultiStark.Final.Configuration)
    (headers : List NarrowClaimHeader) : Except String Unit := do
  unless cfg.policyDigest.length == 8 && cfg.policyDigest.all (· < 2 ^ 32) do
    throw "final policy digest requires eight u32 words"
  unless cfg.anchors.length == 128 && cfg.anchors.all (· < 256) do
    throw "final pairing anchors require 128 canonical bytes"
  unless 2 ≤ cfg.minStage && cfg.minStage == cfg.maxStage && cfg.maxStage < 2 ^ 32 do
    throw "the narrow terminal follows one fixed BN stage"
  unless headers.length != 0 && headers.all (fun h => h.tag < MultiStark.BN.modulus &&
      h.key < MultiStark.BN.modulus && h.values != 0) do
    throw "invalid narrow claim headers"
  unless (headers.map (·.values)).sum == 21 do
    throw "narrow claim headers must cover the step_v1 call"
  return ()

/-- Validated export-time configuration invariants for `CompressFinalNarrow`. -/
structure FinalNarrowConfigValid (cfg : MultiStark.Final.Configuration)
    (headers : List NarrowClaimHeader) : Prop where
  policyDigest_len : cfg.policyDigest.length = 8
  policyDigest_u32 : ∀ w ∈ cfg.policyDigest, w < 2 ^ 32
  anchors_len : cfg.anchors.length = 128
  anchors_u8 : ∀ b ∈ cfg.anchors, b < 256
  minStage_ge_two : 2 ≤ cfg.minStage
  single_stage : cfg.minStage = cfg.maxStage
  maxStage_u32 : cfg.maxStage < 2 ^ 32
  headers_nonempty : headers.length ≠ 0
  headers_bounds : ∀ h ∈ headers,
    h.tag < MultiStark.BN.modulus ∧ h.key < MultiStark.BN.modulus ∧ h.values ≠ 0
  headers_cover_step_v1 : (headers.map (·.values)).sum = 21

/-- Soundness of `validateFinalNarrowConfig`: acceptance yields every configuration and
21-word `step_v1` header invariant (`[propext, Classical.choice, Quot.sound]` only). -/
theorem validateFinalNarrowConfig_ok_spec {cfg : MultiStark.Final.Configuration}
    {headers : List NarrowClaimHeader}
    (hok : validateFinalNarrowConfig cfg headers = .ok ()) :
    FinalNarrowConfigValid cfg headers := by
  unfold validateFinalNarrowConfig at hok
  obtain ⟨hpolT, hok⟩ := except_guard_ok hok
  obtain ⟨hancT, hok⟩ := except_guard_ok hok
  obtain ⟨hstgT, hok⟩ := except_guard_ok hok
  obtain ⟨hhdrT, hok⟩ := except_guard_ok hok
  obtain ⟨hsumT, _⟩ := except_guard_ok hok
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    bne_iff_ne] at hpolT hancT hstgT hhdrT hsumT
  exact ⟨hpolT.1, hpolT.2, hancT.1, hancT.2, hstgT.1.1, hstgT.1.2, hstgT.2,
    hhdrT.1, fun h hh => ⟨(hhdrT.2 h hh).1.1, (hhdrT.2 h hh).1.2, (hhdrT.2 h hh).2⟩, hsumT⟩

/-- Constructive rejection: `validateFinalNarrowConfig` rejects any stage `< 2`
(preventing bypass of the narrow fixed-key stage). -/
theorem validateFinalNarrowConfig_rejects_stage_one
    (cfg : MultiStark.Final.Configuration) (headers : List NarrowClaimHeader)
    (hstage : cfg.minStage < 2) :
    validateFinalNarrowConfig cfg headers ≠ .ok () := by
  intro hok
  have hge := (validateFinalNarrowConfig_ok_spec hok).minStage_ge_two
  omega

/-- Constructive rejection: `validateFinalNarrowConfig` rejects any header set whose
total word width is not `21` (preventing truncated or padded `step_v1` claims). -/
theorem validateFinalNarrowConfig_rejects_wrong_header_width
    (cfg : MultiStark.Final.Configuration) (headers : List NarrowClaimHeader)
    (hwidth : (headers.map (·.values)).sum ≠ 21) :
    validateFinalNarrowConfig cfg headers ≠ .ok () := by
  intro hok
  exact hwidth (validateFinalNarrowConfig_ok_spec hok).headers_cover_step_v1

end Ix.Cert.AiurCompression
