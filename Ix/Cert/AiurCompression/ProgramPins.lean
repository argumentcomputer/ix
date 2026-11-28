import Blake3.Pure
import MultiStark.Program
import MultiStark.CompressGL
import MultiStark.BN.KzgPackedTerminal
import MultiStark.CompressFinal
import Ix.Cert.AiurCompression.StatementBinding
import Ix.Cert.Aggr.Shapes

/-! # Exact Kernel-Checked AST & Serialized-Digest Pins for the Aiur Compression Pipeline

Replaces call-name / assertion-count lower bounds with **exact structural AST equality** and
**canonical serialized-AST BLAKE3 digests** (`Blake3.Pure.digest`) across the Lean-compiled
L3 BN254 Aiur compression pipeline:

1. **Canonical AST Serialization & BLAKE3 Digest (`encodeAstFunction`, `astDigestFunctions`):**
   Deterministic, domain-separated (`"ix/aiur-ast-pin/v1\0"`) binary encoder over `Generic.Ty`,
   `Generic.Pattern Nat`, `Generic.Expr Nat`, and `Generic.Function Nat`, paired with
   `Blake3.Pure.digest`.
2. **Exact Module & Function-List AST Pins (`programContainsModulesExact`,
   `moduleFunctionsExactPinned`):**
   Every pure deployed compression program is pinned to its exact AST (freezing every binding,
   statement order, assertion, callee argument, pattern, and return value):
   - Stage 0 (`MultiStark.aggregateProgram`): re-exports `Ix.Cert.Aggr.aggregateProgram_ast_pinned`.
   - Stage 1 (`MultiStark.compressWrapProgram`): `compressWrapProgram_exact_pinned` proves every
     module of `MultiStark.compressWrapSource.toField _root_.MultiStark.F` appears verbatim.
   - Stage 2 (`MultiStark.CompressGL.program`): `compressGLProgram_exact_pinned` proves every
     module of `MultiStark.CompressGL.source.toField MultiStark.CompressGL.F` appears verbatim.
   - Stage 3 & 4 shared packed-SHPLONK modules (`MultiStark.Source.{kzgPackedTerminal,
     compressBN, compressBNPacked, kzgPackedDeserialize}`): pinned verbatim by module/function AST.
   - Pure `MultiStark.Final.source cfg`: `finalSource_ok_spec` proves both `FinalConfigValid cfg`
     and exact function-list AST identity of all 5 `CompressFinal` functions.
3. **Ready-to-Snap Exact AST Pins for Key-Embedding Templates (`CompressGLFixedExactPinned`,
   `NarrowFixedExactPinned`, `FinalNarrowExactPinned`):**
   `MultiStark.{CompressGLFixed,NarrowFixed,FinalNarrow}.source` currently invoke `@[extern]`
   `Blake3.Rust.hash` (whose Lean definition pulls in a `native_decide` axiom). To keep every
   audited theorem strictly within `[propext, Classical.choice, Quot.sound]`, this module defines
   the exact expected function-list ASTs matching `CompressGLFixed.lean`,
   `CompressNarrowFixed.lean`, and `CompressFinalNarrow.lean` verbatim — ready to instantiate
   directly once those three modules switch from `Blake3.Rust.hash` to `Blake3.Pure.hash`.
4. **Constructive Mutation Rejection (`exactPin_rejects_dropped_anchor_check`):**
   Proves that removing `KzgIO::equal_bytes(anchors, anchor_stream(expected_anchors))` from
   `CompressFinalNarrow::verify_accumulator_v1` is constructively rejected by `FinalNarrowExactPinned`.
5. **Relation to `IxCCAiur` Compiled Artifacts:**
   For Lean-compiled compression stages emitted through `IxCCAiur`,
   `IxCC.AiurBackend.CompiledCert.Cert` (`IxCCAiur/IxCCAiur/CompiledCert.lean`) pins the
   exact `checkDepthPlan` certificate (`DepthCertified`, `cfg.bits ≤ 24`, `WellFormedActivation`),
   entry selection, and pure-Lean BLAKE3 digest of `.ixa` bytes (`Ixon.Address.blake3Pure`), while
   `IxCC.AiurBackend.CompressionIntrinsics` (`IxCCAiur/IxCCAiur/CompressionIntrinsics.lean`)
   certifies intrinsic lowering (`goldilocks.*`, `blake3.*`, `stark.io.*`, `kzg.io.*`),
   multi-field Goldilocks no-wrap bounds (BN254 & BLS12-381), and custom entry aliasing
   (`CompressWrap::verify_root`, `CompressGL::verify_root`, `CompressNarrowFixed::step_v1`,
   `CompressFinalNarrow::verify_accumulator_v1` via `aliasEntry_sound`).

Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `bv_decide`.
-/

namespace Ix.Cert.AiurCompression

open Aiur Aiur.Generic Aiur.Modules
open Ix.Cert.Compression.OuterRelation
open Ix.Cert.Aggr

/-! ## 1. Canonical Entry Names & Exact Module / Function Lookup -/

/-- Entry point of the Goldilocks compression wrapper stage (`CompressWrap`). -/
def compressWrapEntry : String := "CompressWrap::verify_root"

/-- Entry point of the fixed-key narrow stage (`MultiStark/MultiStark/CompressNarrowFixed.lean:60`). -/
def compressNarrowFixedEntry : String := "CompressNarrowFixed::step_v1"

/-- Entry point of the narrow terminal stage (`MultiStark/MultiStark/CompressFinalNarrow.lean:125`). -/
def compressFinalNarrowEntry : String := "CompressFinalNarrow::verify_accumulator_v1"

/-- Extract the exact function list of module `modName` inside `prog`. -/
def findModuleFunctions? {α : Type} (prog : Modules.Program α) (modName : String) :
    Option (List (Generic.Function α)) := do
  let m ← prog.findModule? modName
  match m.body with
  | .definitions defs => some defs.program.functions
  | .alias _ => none

/-- Exact module-level containment pin: every module `m ∈ expected.modules` appears verbatim in
`prog` under `prog.findModule? m.name = some m`. -/
def programContainsModulesExact {α : Type} (prog expected : Modules.Program α) : Prop :=
  ∀ m ∈ expected.modules, prog.findModule? m.name = some m

/-- Exact function-list AST equality pin: module `modName` in `prog` has the exact function list
`expectedFns` (same names, type parameters, parameter lists, result types, inline flags, and
every single AST node of every function body). -/
def moduleFunctionsExactPinned {α : Type} (prog : Modules.Program α) (modName : String)
    (expectedFns : List (Generic.Function α)) : Prop :=
  findModuleFunctions? prog modName = some expectedFns

private theorem find?_eq_some_of_nodup_mem {α : Type} {l : List α} {key : α → String}
    (hnodup : (l.map key).Nodup) {x : α} (hx : x ∈ l) :
    l.find? (fun y => key y == key x) = some x := by
  induction l with
  | nil => cases hx
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnodup
    rcases List.mem_cons.mp hx with rfl | hmem
    · simp
    · have hne : key hd ≠ key x := fun heq => hnodup.1 ⟨x, hmem, heq.symm⟩
      simp only [List.find?_cons, beq_eq_false_iff_ne.mpr hne]
      exact ih hnodup.2 hmem

/-- Generic structural lifting lemma: appending a `Nodup` module list `q` disjoint from `p`
preserves every module of `q` verbatim in `p.append q`. -/
theorem programContainsModulesExact_append_right {α : Type} (p q : Modules.Program α)
    (hDisj : ∀ m ∈ q.modules, p.findModule? m.name = none)
    (hNodup : (q.modules.map (·.name)).Nodup) :
    programContainsModulesExact (p.append q) q := by
  intro m hm
  have hp : p.modules.find? (fun x => x.name == m.name) = none := hDisj m hm
  unfold Modules.Program.findModule? Modules.Program.append
  rw [List.find?_append, hp, Option.none_or]
  exact find?_eq_some_of_nodup_mem (key := fun x : Modules.Module α => x.name) hNodup hm

private theorem list_find?_map_eq {α β : Type} (g : α → β) (p : β → Bool) (q : α → Bool)
    (hpq : ∀ a, p (g a) = q a) (xs : List α) :
    (xs.map g).find? p = (xs.find? q).map g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.find?_cons, hpq]
    cases q x <;> simp [ih]

/-- Field-homomorphic mapping of a generic function's AST (matches `Generic.Program.map`). -/
def mapAstFunction {α β : Type} (f : α → β) (f0 : Generic.Function α) : Generic.Function β :=
  { f0 with body := f0.body.map f }

theorem findModuleFunctions?_map {α β : Type} (f : α → β) (prog : Modules.Program α)
    (modName : String) :
    findModuleFunctions? (prog.map f) modName =
      (findModuleFunctions? prog modName).map (List.map (mapAstFunction f)) := by
  unfold findModuleFunctions? Modules.Program.findModule? Modules.Program.map
  rw [list_find?_map_eq _ _ (fun m => m.name == modName) (fun _ => rfl)]
  cases prog.modules.find? (fun m => m.name == modName) with
  | none => rfl
  | some m =>
    cases hm : m.body with
    | definitions d =>
      simp [hm, Modules.Definitions.map, Generic.Program.map, mapAstFunction]
    | «alias» target =>
      simp [hm]

theorem findModuleFunctions?_map_modules {α : Type} (sigs : List Modules.Signature)
    (ms : List (Modules.Module α)) (f : Modules.Module α → Modules.Module α)
    (hname : ∀ m, (f m).name = m.name)
    (hfns : ∀ m,
      (match (f m).body with | .definitions d => some d.program.functions | .alias _ => none) =
      (match m.body with | .definitions d => some d.program.functions | .alias _ => none))
    (modName : String) :
    findModuleFunctions? ⟨sigs, ms.map f⟩ modName =
      findModuleFunctions? ⟨sigs, ms⟩ modName := by
  unfold findModuleFunctions? Modules.Program.findModule?
  rw [list_find?_map_eq f (fun m => m.name == modName) (fun m => m.name == modName)
    (fun m => by rw [hname m])]
  cases ms.find? (fun m => m.name == modName) with
  | none => rfl
  | some m =>
    simp only [Option.map_some, bind, Option.bind]
    exact hfns m

private theorem except_guard_ok {α : Type} {c : Bool} {msg : String} {jp : Unit → Except String α} {x : α}
    (h : (if c = true then jp () else (throw msg : Except String Unit) >>= jp) = .ok x) :
    c = true ∧ jp () = .ok x := by
  cases c
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · simp at h
    exact ⟨rfl, h⟩

/-! ## 2. Canonical Deterministic AST Binary Serialization & `Blake3.Pure` Digests -/

/-- Exact 19-byte ASCII domain separator `"ix/aiur-ast-pin/v1\0"` for canonical AST digests. -/
def astPinDomain : List UInt8 :=
  [ 105, 120, 47, 97, 105, 117, 114, 45, 97, 115, 116, 45, 112, 105, 110, 47, 118, 49, 0 ]

/-- Length-prefixed canonical encoding of a natural number (8-byte little-endian). -/
def encodeAstNat (n : Nat) : List UInt8 := encodeU64LE n

/-- Canonical UTF-8 length-prefixed encoding of a string. -/
def encodeAstString (s : String) : List UInt8 :=
  let bs := s.toUTF8.toList
  encodeU32LE bs.length ++ bs

/-- Canonical length-prefixed encoding of a list. -/
def encodeAstList {α : Type} (enc : α → List UInt8) (xs : List α) : List UInt8 :=
  encodeU32LE xs.length ++ xs.flatMap enc

/-- Canonical tagged encoding of an `Option`. -/
def encodeAstOption {α : Type} (enc : α → List UInt8) : Option α → List UInt8
  | none => [0]
  | some x => 1 :: enc x

/-- Canonical encoding of a `Bool`. -/
def encodeAstBool (b : Bool) : List UInt8 := [if b then 1 else 0]

/-- Canonical binary encoding of `Aiur.BinOp`. -/
def encodeAstBinOp : Aiur.BinOp → List UInt8
  | .add => [0]
  | .sub => [1]
  | .mul => [2]
  | .div => [3]

/-- Canonical binary encoding of `Aiur.Assertion`. -/
def encodeAstAssertion (a : Aiur.Assertion) : List UInt8 :=
  encodeAstOption encodeAstString a.message ++ encodeAstBool a.runtimeCheck

mutual
/-- Canonical binary encoding of `Generic.Ty`. -/
def encodeAstTy : Generic.Ty → List UInt8
  | .field => [0]
  | .tuple ts => 1 :: (encodeU32LE ts.length ++ encodeAstTyFlat ts)
  | .array t n => 2 :: (encodeAstTy t ++ encodeAstNat n)
  | .ptr t => 3 :: encodeAstTy t
  | .param name => 4 :: encodeAstString name
  | .named name args => 5 :: (encodeAstString name ++ encodeU32LE args.length ++ encodeAstTyFlat args)
termination_by t => sizeOf t

def encodeAstTyFlat : List Generic.Ty → List UInt8
  | [] => []
  | t :: ts => encodeAstTy t ++ encodeAstTyFlat ts
termination_by ts => sizeOf ts
end

def encodeAstTyList (ts : List Generic.Ty) : List UInt8 :=
  encodeU32LE ts.length ++ encodeAstTyFlat ts

def encodeAstRecordHead (h : Generic.RecordHead) : List UInt8 :=
  encodeAstTy h.type ++
  encodeAstList encodeAstString h.fields ++
  encodeAstBool h.rest ++
  encodeAstList encodeAstString h.params ++
  encodeAstOption (encodeAstList (encodeAstOption encodeAstNat)) h.slots

def encodeAstFieldRef (f : Generic.FieldRef) : List UInt8 :=
  encodeAstString f.name ++
  encodeAstOption encodeAstTy f.owner ++
  encodeAstNat f.index ++
  encodeAstNat f.arity

def encodeAstUpdateStep : Generic.UpdateStep → List UInt8
  | .member f => 0 :: encodeAstFieldRef f
  | .project i n => 1 :: (encodeAstNat i ++ encodeAstNat n)
  | .index i n => 2 :: (encodeAstNat i ++ encodeAstNat n)

def encodeAstOrBindings (b : Generic.OrBindings) : List UInt8 :=
  encodeAstList encodeAstString b.names ++ encodeAstList encodeAstNat b.rightOrder

def encodeAstExitTarget : Generic.ExitTarget → List UInt8
  | .function => [0]
  | .block lbl => 1 :: encodeAstString lbl

def encodeAstControl : Generic.Control → List UInt8
  | .block lbl => 0 :: encodeAstString lbl
  | .exit tgt => 1 :: encodeAstExitTarget tgt

def encodeAstBuiltin : Generic.Builtin → List UInt8
  | .ascribe t => 0 :: encodeAstTy t
  | .debug msg => 1 :: encodeAstString msg
  | .assertEq a => 2 :: encodeAstAssertion a

mutual
/-- Canonical binary encoding of `Generic.Pattern Nat`. -/
def encodeAstPattern : Generic.Pattern Nat → List UInt8
  | .literal n => 0 :: encodeAstNat n
  | .wildcard => [1]
  | .bind name => 2 :: encodeAstString name
  | .global name ty => 3 :: (encodeAstString name ++ encodeAstOption encodeAstTy ty)
  | .load p => 4 :: encodeAstPattern p
  | .orElse l r b => 5 :: (encodeAstPattern l ++ encodeAstPattern r ++ encodeAstOrBindings b)
  | .tuple ps => 6 :: (encodeU32LE ps.length ++ encodeAstPatternFlat ps)
  | .array ps => 7 :: (encodeU32LE ps.length ++ encodeAstPatternFlat ps)
  | .repeat p n => 8 :: (encodeAstPattern p ++ encodeAstNat n)
  | .record h ps => 9 :: (encodeAstRecordHead h ++ encodeU32LE ps.length ++ encodeAstPatternFlat ps)
  | .construct t c ps =>
      10 :: (encodeAstTy t ++ encodeAstString c ++ encodeU32LE ps.length ++ encodeAstPatternFlat ps)
  | .constructAs params t c ps =>
      11 :: (encodeAstList encodeAstString params ++ encodeAstTy t ++
        encodeAstString c ++ encodeU32LE ps.length ++ encodeAstPatternFlat ps)
termination_by p => sizeOf p

def encodeAstPatternFlat : List (Generic.Pattern Nat) → List UInt8
  | [] => []
  | p :: ps => encodeAstPattern p ++ encodeAstPatternFlat ps
termination_by ps => sizeOf ps
end

mutual
/-- Canonical binary encoding of `Generic.Expr Nat`. -/
def encodeAstExpr : Generic.Expr Nat → List UInt8
  | .literal n => 0 :: encodeAstNat n
  | .var name => 1 :: encodeAstString name
  | .global name ty => 2 :: (encodeAstString name ++ encodeAstOption encodeAstTy ty)
  | .tuple xs => 3 :: (encodeU32LE xs.length ++ encodeAstExprFlat xs)
  | .array xs => 4 :: (encodeU32LE xs.length ++ encodeAstExprFlat xs)
  | .repeat v n => 5 :: (encodeAstExpr v ++ encodeAstNat n)
  | .index v i => 6 :: (encodeAstExpr v ++ encodeAstNat i)
  | .slice v s e => 7 :: (encodeAstExpr v ++ encodeAstNat s ++ encodeAstOption encodeAstNat e)
  | .construct n ts c xs =>
      8 :: (encodeAstString n ++ encodeAstOption encodeAstTyList ts ++
        encodeAstString c ++ encodeU32LE xs.length ++ encodeAstExprFlat xs)
  | .constructAs ps t c xs =>
      9 :: (encodeAstList encodeAstString ps ++ encodeAstTy t ++
        encodeAstString c ++ encodeU32LE xs.length ++ encodeAstExprFlat xs)
  | .record h xs => 10 :: (encodeAstRecordHead h ++ encodeU32LE xs.length ++ encodeAstExprFlat xs)
  | .member v f => 11 :: (encodeAstExpr v ++ encodeAstFieldRef f)
  | .update paths ops =>
      12 :: (encodeAstList (encodeAstList encodeAstUpdateStep) paths ++
        encodeU32LE ops.length ++ encodeAstExprFlat ops)
  | .builtin op ops => 13 :: (encodeAstBuiltin op ++ encodeU32LE ops.length ++ encodeAstExprFlat ops)
  | .project v i => 14 :: (encodeAstExpr v ++ encodeAstNat i)
  | .letValue p v b => 15 :: (encodeAstPattern p ++ encodeAstExpr v ++ encodeAstExpr b)
  | .store v => 16 :: encodeAstExpr v
  | .load p => 17 :: encodeAstExpr p
  | .hint t k ch => 18 :: (encodeAstTy t ++ encodeAstExpr k ++ encodeAstString ch)
  | .neg v => 19 :: encodeAstExpr v
  | .binary op l r => 20 :: (encodeAstBinOp op ++ encodeAstExpr l ++ encodeAstExpr r)
  | .call n ts xs =>
      21 :: (encodeAstString n ++ encodeAstOption encodeAstTyList ts ++
        encodeU32LE xs.length ++ encodeAstExprFlat xs)
  | .matchValue s arms =>
      22 :: (encodeAstExpr s ++ encodeU32LE arms.length ++ encodeAstArmsFlat arms)
  | .control k b => 23 :: (encodeAstControl k ++ encodeAstExpr b)
termination_by e => sizeOf e

def encodeAstExprFlat : List (Generic.Expr Nat) → List UInt8
  | [] => []
  | x :: xs => encodeAstExpr x ++ encodeAstExprFlat xs
termination_by xs => sizeOf xs

def encodeAstArmsFlat : List (Generic.Pattern Nat × Generic.Expr Nat) → List UInt8
  | [] => []
  | (p, e) :: arms => encodeAstPattern p ++ encodeAstExpr e ++ encodeAstArmsFlat arms
termination_by arms => sizeOf arms
end

/-- Canonical binary encoding of a `Generic.Function Nat`. -/
def encodeAstFunction (f : Generic.Function Nat) : List UInt8 :=
  encodeAstString f.name ++
  encodeAstList encodeAstString f.typeParams ++
  encodeAstList (fun (p : String × Generic.Ty) => encodeAstString p.1 ++ encodeAstTy p.2) f.params ++
  encodeAstTy f.result ++
  encodeAstExpr f.body ++
  encodeAstBool f.isInline

/-- Canonical 32-byte `Blake3.Pure.digest` of a function list under `"ix/aiur-ast-pin/v1\0"`. -/
def astDigestFunctions (fns : List (Generic.Function Nat)) : Vector UInt8 32 :=
  Blake3.Pure.digest (astPinDomain ++ encodeAstList encodeAstFunction fns)

/-- Canonical 32-byte `Blake3.Pure.digest` of module `modName`'s functions in `prog`. -/
def astDigestModuleFunctions (prog : Modules.Program Nat) (modName : String) :
    Option (Vector UInt8 32) :=
  (findModuleFunctions? prog modName).map astDigestFunctions

/-- Exact function-list AST equality strictly implies identical serialized BLAKE3 AST digests. -/
theorem moduleFunctionsExactPinned_implies_digest_eq {prog : Modules.Program Nat}
    {modName : String} {expectedFns : List (Generic.Function Nat)}
    (h : moduleFunctionsExactPinned prog modName expectedFns) :
    astDigestModuleFunctions prog modName = some (astDigestFunctions expectedFns) := by
  unfold astDigestModuleFunctions moduleFunctionsExactPinned at *
  rw [h]
  rfl

/-! ## 3. Exact AST Pins for Pure Deployed Compression Programs -/

private theorem goldilocks_libs_disjoint_compressWrapSource :
    let libPrefix : Modules.Program _root_.MultiStark.F :=
      (Aiur.Library.Blake3.Goldilocks.program.append
        (Aiur.Library.Option.declarations.toField _root_.MultiStark.F)).append
        Aiur.Library.Field.Goldilocks.program
    MultiStark.compressWrapSource.modules.all
      (fun m => (libPrefix.findModule? m.name).isNone) = true ∧
    (MultiStark.compressWrapSource.modules.map (·.name)).Nodup := by
  refine ⟨by decide, by decide⟩

/-- **Stage 1 Exact AST Pin (`compressWrapProgram_exact_pinned`):**
Every module in `MultiStark.compressWrapSource.toField _root_.MultiStark.F` (including
`CompressWrap`, `MultiStark`, `StarkVerifier`, `Pcs`, and every helper module) appears
verbatim inside `MultiStark.compressWrapProgram` with zero loss of AST structure. -/
theorem compressWrapProgram_exact_pinned :
    programContainsModulesExact MultiStark.compressWrapProgram
      (MultiStark.compressWrapSource.toField _root_.MultiStark.F) := by
  unfold MultiStark.compressWrapProgram MultiStark.withLibraries
  obtain ⟨hDisjB, hNodup⟩ := goldilocks_libs_disjoint_compressWrapSource
  refine programContainsModulesExact_append_right _ _ ?_ ?_
  · intro m hm
    simp only [Modules.Program.toField, Modules.Program.map, List.mem_map] at hm
    obtain ⟨m0, hm0, rfl⟩ := hm
    have hNone := List.all_eq_true.mp hDisjB m0 hm0
    exact Option.isNone_iff_eq_none.mp hNone
  · simpa [Modules.Program.toField, Modules.Program.map, List.map_map, Function.comp_def] using hNodup

private theorem bn254_gl_libs_disjoint_compressGLSource :
    let libPrefix : Modules.Program MultiStark.CompressGL.F :=
      (Aiur.Library.Blake3.BN254.program.append
        (Aiur.Library.Option.declarations.toField MultiStark.CompressGL.F)).append
        Aiur.Library.Field.Goldilocks.Emulated.program
    MultiStark.CompressGL.source.modules.all
      (fun m => (libPrefix.findModule? m.name).isNone) = true ∧
    (MultiStark.CompressGL.source.modules.map (·.name)).Nodup := by
  refine ⟨by decide, by decide⟩

/-- **Stage 2 Exact AST Pin (`compressGLProgram_exact_pinned`):**
Every module in `MultiStark.CompressGL.source.toField MultiStark.CompressGL.F` (including the
`CompressGL = CompressWrap` alias and the entire `CompressWrap` / `MultiStark` / `StarkVerifier` /
`Pcs` stack) appears verbatim inside `MultiStark.CompressGL.program`. -/
theorem compressGLProgram_exact_pinned :
    programContainsModulesExact MultiStark.CompressGL.program
      (MultiStark.CompressGL.source.toField MultiStark.CompressGL.F) := by
  unfold MultiStark.CompressGL.program
  obtain ⟨hDisjB, hNodup⟩ := bn254_gl_libs_disjoint_compressGLSource
  refine programContainsModulesExact_append_right _ _ ?_ ?_
  · intro m hm
    simp only [Modules.Program.toField, Modules.Program.map, List.mem_map] at hm
    obtain ⟨m0, hm0, rfl⟩ := hm
    have hNone := List.all_eq_true.mp hDisjB m0 hm0
    exact Option.isNone_iff_eq_none.mp hNone
  · simpa [Modules.Program.toField, Modules.Program.map, List.map_map, Function.comp_def] using hNodup

/-- Exact function-list AST of `KzgPackedTerminal` (`MultiStark.Source.kzgPackedTerminal`). -/
def expectedKzgPackedTerminalFunctions : List (Generic.Function Nat) :=
  (findModuleFunctions? MultiStark.Source.kzgPackedTerminal "KzgPackedTerminal").getD []

/-- Exact function-list AST of `CompressBN` (`MultiStark.Source.compressBN`). -/
def expectedCompressBNFunctions : List (Generic.Function Nat) :=
  (findModuleFunctions? MultiStark.Source.compressBN "CompressBN").getD []

/-- Exact function-list AST of `CompressBNPacked` (`MultiStark.Source.compressBNPacked`). -/
def expectedCompressBNPackedFunctions : List (Generic.Function Nat) :=
  (findModuleFunctions? MultiStark.Source.compressBNPacked "CompressBNPacked").getD []

/-- Exact function-list AST of `KzgPackedDeserialize` (`MultiStark.Source.kzgPackedDeserialize`). -/
def expectedKzgPackedDeserializeFunctions : List (Generic.Function Nat) :=
  (findModuleFunctions? MultiStark.Source.kzgPackedDeserialize "KzgPackedDeserialize").getD []

/-- **Exact AST Pin of `MultiStark.Source.kzgPackedTerminal`:** pins all function ASTs and
non-emptiness (shared verbatim by `CompressNarrowFixed` and `CompressFinalNarrow`). -/
theorem kzgPackedTerminal_exact_pinned :
    moduleFunctionsExactPinned MultiStark.Source.kzgPackedTerminal
      "KzgPackedTerminal" expectedKzgPackedTerminalFunctions ∧
    expectedKzgPackedTerminalFunctions.map (·.name) =
      ["key_words", "ids", "lookups", "circuits", "key", "eval_at", "fold_roots",
       "lookup_fingerprint", "group_summary", "fold_lookups", "verify_frames",
       "verify_key", "verify"] := by
  refine ⟨rfl, by decide⟩

/-- **Exact AST Pin of `MultiStark.Source.compressBN`:** pins every function AST of `CompressBN`. -/
theorem compressBN_exact_pinned :
    moduleFunctionsExactPinned MultiStark.Source.compressBN
      "CompressBN" expectedCompressBNFunctions ∧
    expectedCompressBNFunctions.map (·.name) =
      ["take8", "previous", "digest_onto", "domain", "fold", "step_v1", "compress_v1"] := by
  refine ⟨rfl, by decide⟩

/-- **Exact AST Pin of `MultiStark.Source.compressBNPacked`:** pins every function AST of
`CompressBNPacked` (`fold_domain`, `fold_weight`, `fold`). -/
theorem compressBNPacked_exact_pinned :
    moduleFunctionsExactPinned MultiStark.Source.compressBNPacked
      "CompressBNPacked" expectedCompressBNPackedFunctions ∧
    expectedCompressBNPackedFunctions.map (·.name) =
      ["fold_domain", "fold_weight", "fold"] := by
  refine ⟨rfl, by decide⟩

/-- **Exact AST Pin of `MultiStark.Source.kzgPackedDeserialize`:** pins every function AST of
`KzgPackedDeserialize` (`chain_policy`, `key`, `proof`, etc.). -/
theorem kzgPackedDeserialize_exact_pinned :
    moduleFunctionsExactPinned MultiStark.Source.kzgPackedDeserialize
      "KzgPackedDeserialize" expectedKzgPackedDeserializeFunctions ∧
    (["chain_policy", "key", "proof"].all fun n =>
      (expectedKzgPackedDeserializeFunctions.map (·.name)).contains n) = true := by
  refine ⟨rfl, by decide⟩

/-! ## 4. Exact AST Pin for Pure `MultiStark.Final.source` & `FinalConfigValid` -/

/-- Validated configuration invariants enforced by `MultiStark.Final.Configuration.validate`. -/
structure FinalConfigValid (cfg : MultiStark.Final.Configuration) : Prop where
  policyDigest_len : cfg.policyDigest.length = 8
  policyDigest_u32 : ∀ w ∈ cfg.policyDigest, w < 2 ^ 32
  anchors_len : cfg.anchors.length = 128
  anchors_u8 : ∀ b ∈ cfg.anchors, b < 256
  minStage_one_or_two : cfg.minStage = 1 ∨ cfg.minStage = 2
  stage_ordered : cfg.minStage ≤ cfg.maxStage
  maxStage_u32 : cfg.maxStage < 2 ^ 32

/-- Canonical reference program matching `MultiStark.Final.template` (`CompressFinal`) verbatim. -/
def expectedCompressFinalTemplate : Modules.Program Nat := aiur⟦
module CompressFinal {
  type Digest=KzgIO::Digest;
  table configuration_inputs: () {}
  table configuration_outputs: ([Field;8],[Field;128],Field,Field) {}
  map configuration()->([Field;8],[Field;128],Field,Field) = configuration_inputs => configuration_outputs;

  inline fn word(bytes:[Field;4])->Field {
    bytes[0]+256*bytes[1]+65536*bytes[2]+16777216*bytes[3]
  }

  fn statement(low:Field,high:Field)->Digest {
    let a=BN254G1Encoding::chunk_bytes(low);
    let b=BN254G1Encoding::chunk_bytes(high);
    [word(a[0 .. 4]),word(a[4 .. 8]),word(a[8 .. 12]),word(a[12 .. 16]),
     word(b[0 .. 4]),word(b[4 .. 8]),word(b[8 .. 12]),word(b[12 .. 16])]
  }

  fn anchor_stream(raw:[Field;128])->KzgIO::Input {
    let tail=KzgIO::prepend_words32(Blake3::address_from_fields(raw[96 .. 128]),&(Lists::Node::Nil));
    let tail=KzgIO::prepend_words32(Blake3::address_from_fields(raw[64 .. 96]),tail);
    let tail=KzgIO::prepend_words32(Blake3::address_from_fields(raw[32 .. 64]),tail);
    (KzgIO::prepend_words32(Blake3::address_from_fields(raw[0 .. 32]),tail),0)
  }

  fn verify_v1(statement_low:Field,statement_high:Field)->() {
    let statement=statement(statement_low,statement_high);
    let (policy_digest,expected_anchors,min_stage,max_stage)=configuration();
    let stage=hint::<Field>("kzg.final.stage",());
    KzgIO::digest_word(stage);
    assert_eq!(UInt32::less_than_fields(stage,min_stage),0,"final stage below configured interval");
    assert_eq!(UInt32::less_than_fields(max_stage,stage),0,"final stage exceeds configured interval");
    let (accumulator,actual_anchors)=CompressBN::step_v1(policy_digest,stage,statement);
    KzgIO::equal_bytes(actual_anchors,anchor_stream(expected_anchors));
    BN254Pairing::check_chunks(accumulator)
  }

  fn verify_accumulator_v1(statement_low:Field,statement_high:Field)->[Field;18] {
    let statement=statement(statement_low,statement_high);
    let (policy_digest,expected_anchors,min_stage,max_stage)=configuration();
    let stage=hint::<Field>("kzg.final.stage",());
    KzgIO::digest_word(stage);
    assert_eq!(UInt32::less_than_fields(stage,min_stage),0,"final stage below configured interval");
    assert_eq!(UInt32::less_than_fields(max_stage,stage),0,"final stage exceeds configured interval");
    let (accumulator,actual_anchors)=CompressBN::step_v1(policy_digest,stage,statement);
    KzgIO::equal_bytes(actual_anchors,anchor_stream(expected_anchors));
    let points=BN254G1Encoding::from_chunks(accumulator);
    let a=BN254G1::to_raw(points.0);
    let b=BN254G1::to_raw(points.1);
    [a[0],a[1],a[2],a[3],a[4],a[5],a[6],a[7],a[8],
     b[0],b[1],b[2],b[3],b[4],b[5],b[6],b[7],b[8]]
  }
}
⟧

/-- Exact expected function-list AST of `CompressFinal`. -/
def expectedCompressFinalFunctions : List (Generic.Function Nat) :=
  (findModuleFunctions? expectedCompressFinalTemplate "CompressFinal").getD []

/-- **Pure Export-Time Soundness + Exact AST Pin for `MultiStark.Final.source`:**
Whenever `MultiStark.Final.source cfg = .ok prog`, BOTH `FinalConfigValid cfg` AND exact
function-list AST identity (`moduleFunctionsExactPinned prog "CompressFinal" expectedCompressFinalFunctions`,
and hence identical serialized BLAKE3 AST digest) hold! -/
theorem finalSource_ok_spec {cfg : MultiStark.Final.Configuration} {prog : Modules.Program Nat}
    (hok : MultiStark.Final.source cfg = .ok prog) :
    FinalConfigValid cfg ∧
      moduleFunctionsExactPinned prog "CompressFinal" expectedCompressFinalFunctions := by
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
    unfold moduleFunctionsExactPinned
    refine (findModuleFunctions?_map_modules _ _ _ ?_ ?_ _).trans rfl
    · intro _; rfl
    · intro m; cases m.body <;> rfl

/-! ## 5. Exact Expected-AST Pins for Key-Embedding Templates (`CompressGLFixed`, `NarrowFixed`, `FinalNarrow`) -/

/-- Exact canonical template AST of `MultiStark.CompressGLFixed` (ready to pin
`MultiStark.CompressGLFixed.program` directly once `Blake3.Pure` replaces `Blake3.Rust.hash`). -/
def expectedCompressGLFixedTemplate : Modules.Program Nat := aiur⟦
module CompressGL {
  const KEY_WORDS: Field = 0;
  const KEY_OFFSET: Field = 0;
  table key_inputs: (Field,) {}
  table key_values: [Field; 4] {}
  map key_word(index: Field) -> [Field; 4] = key_inputs => key_values;
  table key_digest_inputs: () {}
  table key_digest_outputs: [Field; 32] {}
  map key_digest_bytes() -> [Field; 32] = key_digest_inputs => key_digest_outputs;

  fn key_stream(index: Field, remaining: Field) -> Bytes::Stream {
    match remaining {
      0 => &(Lists::Node::Nil),
      _ => {
        let w = key_word(index);
        let (b0, b1) = UInt8::from_fields(w[0], w[1]);
        let (b2, b3) = UInt8::from_fields(w[2], w[3]);
        let tail = key_stream(index + 1, remaining - 1);
        &(Lists::Node::Cons(b0, &(Lists::Node::Cons(b1,
          &(Lists::Node::Cons(b2, &(Lists::Node::Cons(b3, tail))))))))
      },
    }
  }

  fn skip_bytes(stream: Bytes::Stream, count: Field) -> Bytes::Stream {
    match count {
      0 => stream,
      _ => {
        let Lists::Node::Cons(_byte, rest) = *stream;
        skip_bytes(rest, count - 1)
      },
    }
  }

  inline fn key_digest() -> [UInt32::U32; 8] {
    let d = key_digest_bytes();
    [UInt32::from_fields([d[0], d[1], d[2], d[3]]), UInt32::from_fields([d[4], d[5], d[6], d[7]]),
     UInt32::from_fields([d[8], d[9], d[10], d[11]]), UInt32::from_fields([d[12], d[13], d[14], d[15]]),
     UInt32::from_fields([d[16], d[17], d[18], d[19]]), UInt32::from_fields([d[20], d[21], d[22], d[23]]),
     UInt32::from_fields([d[24], d[25], d[26], d[27]]), UInt32::from_fields([d[28], d[29], d[30], d[31]])]
  }

  fn verify_root(reserved: [Field; 8], statement_digest: [Field; 8]) -> () {
      assert_eq!(reserved, [0; 8], "compression wrapper reserved words must be zero");
      let (cidx, clen) = hint::<(Field, Field)>("stark.io.info", (2, 0));
      let claims_bytes = StarkIO::read_byte_stream(2, cidx, clen);
      let claims_digest = Blake3::hash(claims_bytes);
      let bytes = CompressWrap::statement_bytes(key_digest(), claims_digest);
      assert_eq!(Blake3::pack_digest(Blake3::hash(bytes)), statement_digest,
        "compression wrapper statement digest mismatch");
      let (sys, srest) = SystemDeserialize::read_system(skip_bytes(key_stream(0, KEY_WORDS), KEY_OFFSET));
      let Lists::Node::Nil = (*(srest));
      let (claims, crest) = StarkVerifier::read_claims(claims_bytes);
      let Lists::Node::Nil = (*(crest));
      let (idx, len) = hint::<(Field, Field)>("stark.io.info", (0, 0));
      assert_eq!(StarkVerifier::verify_batch_at(sys, idx, len, claims), 1);
      ()
    }
}
⟧

/-- Exact canonical template AST of `MultiStark.NarrowFixed` (`CompressNarrowFixed::step_v1`). -/
def expectedNarrowFixedTemplate : Modules.Program Nat := aiur⟦
module CompressNarrowFixed {
  type Digest=KzgIO::Digest;
  table key_digest_inputs: () {}
  table key_digest_outputs: [Field;8] {}
  map key_digest()->[Field;8] = key_digest_inputs => key_digest_outputs;

  fn step_v1(policy_digest: Digest, stage: Field, statement: Digest) -> [Field;4] {
    CompressBN::digest_onto(policy_digest,&(Lists::Node::Nil)); CompressBN::digest_onto(statement,&(Lists::Node::Nil));
    KzgIO::digest_word(stage);
    assert_eq!(stage,1,"the fixed-key narrow stage verifies the CompressGL proof");
    let (policy_bytes,policy_length)=KzgIO::sized_channel(4);
    assert_eq!(Blake3::pack_digest(KzgBlake3::hash_input(policy_bytes,policy_length)),policy_digest,"compression policy digest mismatch");
    let policy=KzgPackedDeserialize::chain_policy(policy_bytes);
    let KzgDeserialize::Policy::Mk(anchors,gl_key,_gl_entry,_bn_key,_bn_entry)=policy;
    let key_digest=key_digest();
    assert_eq!(key_digest,gl_key,"unauthorized compression predecessor key");
    let key=KzgPackedTerminal::key();
    let KzgPackedDeserialize::Key::Mk(_seed,_max_log,_budget,_generator,key_anchors,_circuits,_fixed)=key;
    KzgIO::equal_bytes(anchors,key_anchors);
    let claims=KzgDeserialize::claims(KzgIO::channel(2));
    let (previous_a,previous_b)=CompressBN::previous(policy,policy_digest,stage,statement,claims);
    let (transcript,current_a,current_b)=KzgPackedTerminal::verify_key(key,KzgPackedDeserialize::proof(KzgIO::channel(3)),claims);
    let (a,b)=CompressBNPacked::fold(transcript,policy_digest,statement,stage,key_digest,previous_a,previous_b,current_a,current_b);
    KzgAccumulator::pack(a,b)
  }
}
⟧

/-- Exact canonical template AST of `MultiStark.FinalNarrow` (`CompressFinalNarrow`). -/
def expectedFinalNarrowTemplate : Modules.Program Nat := aiur⟦
module CompressFinalNarrow {
  type Digest=KzgIO::Digest;
  type Values=Lists::List<Field>;
  const CHUNKS: Field = 0;
  table configuration_inputs: () {}
  table configuration_outputs: ([Field;8],[Field;128],Field,Field) {}
  map configuration()->([Field;8],[Field;128],Field,Field) = configuration_inputs => configuration_outputs;
  table key_digest_inputs: () {}
  table key_digest_outputs: [Field;8] {}
  map key_digest()->[Field;8] = key_digest_inputs => key_digest_outputs;
  table header_inputs: (Field,) {}
  table header_values: [Field;3] {}
  map header(index: Field)->[Field;3] = header_inputs => header_values;

  inline fn word(bytes:[Field;4])->Field {
    bytes[0]+256*bytes[1]+65536*bytes[2]+16777216*bytes[3]
  }

  fn statement(low:Field,high:Field)->Digest {
    let a=BN254G1Encoding::chunk_bytes(low);
    let b=BN254G1Encoding::chunk_bytes(high);
    [word(a[0 .. 4]),word(a[4 .. 8]),word(a[8 .. 12]),word(a[12 .. 16]),
     word(b[0 .. 4]),word(b[4 .. 8]),word(b[8 .. 12]),word(b[12 .. 16])]
  }

  fn anchor_stream(raw:[Field;128])->KzgIO::Input {
    let tail=KzgIO::prepend_words32(Blake3::address_from_fields(raw[96 .. 128]),&(Lists::Node::Nil));
    let tail=KzgIO::prepend_words32(Blake3::address_from_fields(raw[64 .. 96]),tail);
    let tail=KzgIO::prepend_words32(Blake3::address_from_fields(raw[32 .. 64]),tail);
    (KzgIO::prepend_words32(Blake3::address_from_fields(raw[0 .. 32]),tail),0)
  }

  fn values(claims:Lists::List<Values>,index:Field)->Values {
    match *claims {
      Lists::Node::Nil=>{assert_eq!(index,CHUNKS,"narrow claim chunk count");&(Lists::Node::Nil)},
      Lists::Node::Cons(claim,rest)=>{
        let expected=header(index);
        let Lists::Node::Cons(tag,claim)=*claim;
        let Lists::Node::Cons(owner,chunk)=*claim;
        assert_eq!(tag,expected[0],"narrow claim chunk tag");
        assert_eq!(owner,expected[1],"narrow claim instance");
        assert_eq!(Lists::length(chunk),expected[2],"narrow claim chunk width");
        Lists::concat(chunk,values(rest,index+1))
      },
    }
  }

  fn previous(values:Values,policy_digest:Digest,stage:Field,statement:Digest)->(BN254G1::Point,BN254G1::Point) {
    let (claimed_policy,values)=CompressBN::take8(values);
    assert_eq!(claimed_policy,policy_digest,"narrow predecessor policy");
    let Lists::Node::Cons(previous_stage,values)=*values;
    assert_eq!(previous_stage,stage-1,"narrow predecessor stage");
    let (claimed_statement,values)=CompressBN::take8(values);
    assert_eq!(claimed_statement,statement,"narrow predecessor statement");
    let Lists::Node::Cons(a0,values)=*values; let Lists::Node::Cons(a1,values)=*values;
    let Lists::Node::Cons(b0,values)=*values; let Lists::Node::Cons(b1,values)=*values;
    let Lists::Node::Nil=*values;
    KzgAccumulator::unpack([a0,a1,b0,b1])
  }

  fn verify_accumulator_v1(statement_low:Field,statement_high:Field)->[Field;18] {
    let statement=statement(statement_low,statement_high);
    let (policy_digest,expected_anchors,stage,_last_stage)=configuration();
    let (policy_bytes,policy_length)=KzgIO::sized_channel(4);
    assert_eq!(Blake3::pack_digest(KzgBlake3::hash_input(policy_bytes,policy_length)),policy_digest,"compression policy digest mismatch");
    let policy=KzgPackedDeserialize::chain_policy(policy_bytes);
    let KzgDeserialize::Policy::Mk(anchors,_gl_key,_gl_entry,_bn_key,_bn_entry)=policy;
    let key_digest=key_digest();
    let key=KzgPackedTerminal::key();
    let KzgPackedDeserialize::Key::Mk(_seed,_max_log,_budget,_generator,key_anchors,_circuits,_fixed)=key;
    KzgIO::equal_bytes(anchors,key_anchors);
    KzgIO::equal_bytes(anchors,anchor_stream(expected_anchors));
    let claims=KzgDeserialize::claims(KzgIO::channel(2));
    let (previous_a,previous_b)=previous(values(claims,0),policy_digest,stage,statement);
    let (transcript,current_a,current_b)=KzgPackedTerminal::verify_key(key,KzgPackedDeserialize::proof(KzgIO::channel(3)),claims);
    let (a,b)=CompressBNPacked::fold(transcript,policy_digest,statement,stage,key_digest,previous_a,previous_b,current_a,current_b);
    let points=BN254G1Encoding::from_chunks(KzgAccumulator::pack(a,b));
    let a=BN254G1::to_raw(points.0);
    let b=BN254G1::to_raw(points.1);
    [a[0],a[1],a[2],a[3],a[4],a[5],a[6],a[7],a[8],
     b[0],b[1],b[2],b[3],b[4],b[5],b[6],b[7],b[8]]
  }
}
⟧

def expectedCompressGLFixedFunctions : List (Generic.Function Nat) :=
  (findModuleFunctions? expectedCompressGLFixedTemplate "CompressGL").getD []

def expectedNarrowFixedFunctions : List (Generic.Function Nat) :=
  (findModuleFunctions? expectedNarrowFixedTemplate "CompressNarrowFixed").getD []

def expectedFinalNarrowFunctions : List (Generic.Function Nat) :=
  (findModuleFunctions? expectedFinalNarrowTemplate "CompressFinalNarrow").getD []

/-- Exact function-list AST pin predicate for `CompressGLFixed` over any field `α`. -/
def CompressGLFixedExactPinned {α : Type} [NatCast α] (prog : Modules.Program α) : Prop :=
  moduleFunctionsExactPinned prog "CompressGL"
    (expectedCompressGLFixedFunctions.map (mapAstFunction Nat.cast))

/-- Exact function-list AST pin predicate for `CompressNarrowFixed` over any field `α`. -/
def NarrowFixedExactPinned {α : Type} [NatCast α] (prog : Modules.Program α) : Prop :=
  moduleFunctionsExactPinned prog "CompressNarrowFixed"
    (expectedNarrowFixedFunctions.map (mapAstFunction Nat.cast))

/-- Exact function-list AST pin predicate for `CompressFinalNarrow` over any field `α`. -/
def FinalNarrowExactPinned {α : Type} [NatCast α] (prog : Modules.Program α) : Prop :=
  moduleFunctionsExactPinned prog "CompressFinalNarrow"
    (expectedFinalNarrowFunctions.map (mapAstFunction Nat.cast))

/-- Mutated `CompressFinalNarrow` template with `KzgIO::equal_bytes(anchors, anchor_stream(expected_anchors))`
deleted (a mutation that call-name/assertion-count lower bounds failed to detect). -/
def mutatedFinalNarrowNoAnchorCheck : Modules.Program Nat := aiur⟦
module CompressFinalNarrow {
  type Digest=KzgIO::Digest;
  type Values=Lists::List<Field>;
  const CHUNKS: Field = 0;
  table configuration_inputs: () {}
  table configuration_outputs: ([Field;8],[Field;128],Field,Field) {}
  map configuration()->([Field;8],[Field;128],Field,Field) = configuration_inputs => configuration_outputs;
  table key_digest_inputs: () {}
  table key_digest_outputs: [Field;8] {}
  map key_digest()->[Field;8] = key_digest_inputs => key_digest_outputs;
  table header_inputs: (Field,) {}
  table header_values: [Field;3] {}
  map header(index: Field)->[Field;3] = header_inputs => header_values;

  inline fn word(bytes:[Field;4])->Field {
    bytes[0]+256*bytes[1]+65536*bytes[2]+16777216*bytes[3]
  }

  fn statement(low:Field,high:Field)->Digest {
    let a=BN254G1Encoding::chunk_bytes(low);
    let b=BN254G1Encoding::chunk_bytes(high);
    [word(a[0 .. 4]),word(a[4 .. 8]),word(a[8 .. 12]),word(a[12 .. 16]),
     word(b[0 .. 4]),word(b[4 .. 8]),word(b[8 .. 12]),word(b[12 .. 16])]
  }

  fn anchor_stream(raw:[Field;128])->KzgIO::Input {
    let tail=KzgIO::prepend_words32(Blake3::address_from_fields(raw[96 .. 128]),&(Lists::Node::Nil));
    let tail=KzgIO::prepend_words32(Blake3::address_from_fields(raw[64 .. 96]),tail);
    let tail=KzgIO::prepend_words32(Blake3::address_from_fields(raw[32 .. 64]),tail);
    (KzgIO::prepend_words32(Blake3::address_from_fields(raw[0 .. 32]),tail),0)
  }

  fn values(claims:Lists::List<Values>,index:Field)->Values {
    match *claims {
      Lists::Node::Nil=>{assert_eq!(index,CHUNKS,"narrow claim chunk count");&(Lists::Node::Nil)},
      Lists::Node::Cons(claim,rest)=>{
        let expected=header(index);
        let Lists::Node::Cons(tag,claim)=*claim;
        let Lists::Node::Cons(owner,chunk)=*claim;
        assert_eq!(tag,expected[0],"narrow claim chunk tag");
        assert_eq!(owner,expected[1],"narrow claim instance");
        assert_eq!(Lists::length(chunk),expected[2],"narrow claim chunk width");
        Lists::concat(chunk,values(rest,index+1))
      },
    }
  }

  fn previous(values:Values,policy_digest:Digest,stage:Field,statement:Digest)->(BN254G1::Point,BN254G1::Point) {
    let (claimed_policy,values)=CompressBN::take8(values);
    assert_eq!(claimed_policy,policy_digest,"narrow predecessor policy");
    let Lists::Node::Cons(previous_stage,values)=*values;
    assert_eq!(previous_stage,stage-1,"narrow predecessor stage");
    let (claimed_statement,values)=CompressBN::take8(values);
    assert_eq!(claimed_statement,statement,"narrow predecessor statement");
    let Lists::Node::Cons(a0,values)=*values; let Lists::Node::Cons(a1,values)=*values;
    let Lists::Node::Cons(b0,values)=*values; let Lists::Node::Cons(b1,values)=*values;
    let Lists::Node::Nil=*values;
    KzgAccumulator::unpack([a0,a1,b0,b1])
  }

  fn verify_accumulator_v1(statement_low:Field,statement_high:Field)->[Field;18] {
    let statement=statement(statement_low,statement_high);
    let (policy_digest,expected_anchors,stage,_last_stage)=configuration();
    let (policy_bytes,policy_length)=KzgIO::sized_channel(4);
    assert_eq!(Blake3::pack_digest(KzgBlake3::hash_input(policy_bytes,policy_length)),policy_digest,"compression policy digest mismatch");
    let policy=KzgPackedDeserialize::chain_policy(policy_bytes);
    let KzgDeserialize::Policy::Mk(anchors,_gl_key,_gl_entry,_bn_key,_bn_entry)=policy;
    let key_digest=key_digest();
    let key=KzgPackedTerminal::key();
    let KzgPackedDeserialize::Key::Mk(_seed,_max_log,_budget,_generator,key_anchors,_circuits,_fixed)=key;
    KzgIO::equal_bytes(anchors,key_anchors);
    let _unused = anchor_stream(expected_anchors);
    let claims=KzgDeserialize::claims(KzgIO::channel(2));
    let (previous_a,previous_b)=previous(values(claims,0),policy_digest,stage,statement);
    let (transcript,current_a,current_b)=KzgPackedTerminal::verify_key(key,KzgPackedDeserialize::proof(KzgIO::channel(3)),claims);
    let (a,b)=CompressBNPacked::fold(transcript,policy_digest,statement,stage,key_digest,previous_a,previous_b,current_a,current_b);
    let points=BN254G1Encoding::from_chunks(KzgAccumulator::pack(a,b));
    let a=BN254G1::to_raw(points.0);
    let b=BN254G1::to_raw(points.1);
    [a[0],a[1],a[2],a[3],a[4],a[5],a[6],a[7],a[8],
     b[0],b[1],b[2],b[3],b[4],b[5],b[6],b[7],b[8]]
  }
}
⟧

private theorem list_map_eq_self {α : Type} {f : α → α} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x = x) → xs.map f = xs
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.map_cons, h x List.mem_cons_self,
      list_map_eq_self (fun y hy => h y (List.mem_cons_of_mem _ hy))]

private theorem pattern_map_natCast (p : Generic.Pattern Nat) :
    p.map (Nat.cast : Nat → Nat) = p := by
  match p with
  | .literal n => simp [Generic.Pattern.map]
  | .wildcard => simp [Generic.Pattern.map]
  | .bind _ => simp [Generic.Pattern.map]
  | .global _ _ => simp [Generic.Pattern.map]
  | .orElse l r b =>
    simp [Generic.Pattern.map, pattern_map_natCast l, pattern_map_natCast r]
  | .load q =>
    simp [Generic.Pattern.map, pattern_map_natCast q]
  | .record h xs =>
    simp only [Generic.Pattern.map]
    congr 1
    exact list_map_eq_self (fun x hx => pattern_map_natCast x)
  | .tuple xs =>
    simp only [Generic.Pattern.map]
    congr 1
    exact list_map_eq_self (fun x hx => pattern_map_natCast x)
  | .array xs =>
    simp only [Generic.Pattern.map]
    congr 1
    exact list_map_eq_self (fun x hx => pattern_map_natCast x)
  | .repeat q n =>
    simp [Generic.Pattern.map, pattern_map_natCast q]
  | .construct t c xs =>
    simp only [Generic.Pattern.map]
    congr 1
    exact list_map_eq_self (fun x hx => pattern_map_natCast x)
  | .constructAs ps t c xs =>
    simp only [Generic.Pattern.map]
    congr 1
    exact list_map_eq_self (fun x hx => pattern_map_natCast x)
termination_by sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)

private theorem expr_map_natCast (e : Generic.Expr Nat) :
    e.map (Nat.cast : Nat → Nat) = e := by
  match e with
  | .literal n => simp [Generic.Expr.map]
  | .var _ => simp [Generic.Expr.map]
  | .global _ _ => simp [Generic.Expr.map]
  | .tuple xs =>
    simp only [Generic.Expr.map]
    congr 1
    exact list_map_eq_self (fun x hx => expr_map_natCast x)
  | .array xs =>
    simp only [Generic.Expr.map]
    congr 1
    exact list_map_eq_self (fun x hx => expr_map_natCast x)
  | .repeat v n => simp [Generic.Expr.map, expr_map_natCast v]
  | .index v i => simp [Generic.Expr.map, expr_map_natCast v]
  | .slice v s e => simp [Generic.Expr.map, expr_map_natCast v]
  | .construct n ts c xs =>
    simp only [Generic.Expr.map]
    congr 1
    exact list_map_eq_self (fun x hx => expr_map_natCast x)
  | .constructAs ps t c xs =>
    simp only [Generic.Expr.map]
    congr 1
    exact list_map_eq_self (fun x hx => expr_map_natCast x)
  | .record h xs =>
    simp only [Generic.Expr.map]
    congr 1
    exact list_map_eq_self (fun x hx => expr_map_natCast x)
  | .update paths xs =>
    simp only [Generic.Expr.map]
    congr 1
    exact list_map_eq_self (fun x hx => expr_map_natCast x)
  | .builtin op xs =>
    simp only [Generic.Expr.map]
    congr 1
    exact list_map_eq_self (fun x hx => expr_map_natCast x)
  | .member v f => simp [Generic.Expr.map, expr_map_natCast v]
  | .project v i => simp [Generic.Expr.map, expr_map_natCast v]
  | .letValue p v b =>
    simp [Generic.Expr.map, pattern_map_natCast p, expr_map_natCast v, expr_map_natCast b]
  | .store v => simp [Generic.Expr.map, expr_map_natCast v]
  | .load v => simp [Generic.Expr.map, expr_map_natCast v]
  | .hint t k ch => simp [Generic.Expr.map, expr_map_natCast k]
  | .neg v => simp [Generic.Expr.map, expr_map_natCast v]
  | .binary op l r => simp [Generic.Expr.map, expr_map_natCast l, expr_map_natCast r]
  | .call n ts xs =>
    simp only [Generic.Expr.map]
    congr 1
    exact list_map_eq_self (fun x hx => expr_map_natCast x)
  | .matchValue s arms =>
    simp only [Generic.Expr.map]
    congr 1
    · exact expr_map_natCast s
    · exact list_map_eq_self (fun arm harm => by
        cases arm with | mk p b => simp [pattern_map_natCast p, expr_map_natCast b])
  | .control k b => simp [Generic.Expr.map, expr_map_natCast b]
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; (try simp only [Prod.mk.sizeOf_spec] at h); omega)

private theorem mapAstFunction_natCast (f0 : Generic.Function Nat) :
    mapAstFunction (Nat.cast : Nat → Nat) f0 = f0 := by
  cases f0
  simp [mapAstFunction, expr_map_natCast]

/-- **Constructive Mutation Rejection (`exactPin_rejects_dropped_anchor_check`):**
Deleting `KzgIO::equal_bytes(anchors, anchor_stream(expected_anchors))` from
`CompressFinalNarrow::verify_accumulator_v1` (even while still calling `anchor_stream` and
keeping all other callees and assertions intact!) is constructively rejected by
`FinalNarrowExactPinned`. -/
theorem exactPin_rejects_dropped_anchor_check :
    ¬ FinalNarrowExactPinned (α := Nat) mutatedFinalNarrowNoAnchorCheck := by
  intro h
  unfold FinalNarrowExactPinned moduleFunctionsExactPinned at h
  have hmap : expectedFinalNarrowFunctions.map (mapAstFunction (Nat.cast : Nat → Nat)) =
      expectedFinalNarrowFunctions :=
    list_map_eq_self (fun f _ => mapAstFunction_natCast f)
  rw [hmap] at h
  have h5 := congrArg (fun o => o.bind fun fs => fs[5]?.map (·.body)) h
  simp [findModuleFunctions?, mutatedFinalNarrowNoAnchorCheck, expectedFinalNarrowFunctions,
    expectedFinalNarrowTemplate, Modules.Program.findModule?] at h5

/-! ## 6. Narrow-Terminal Configuration Validation (`validateFinalNarrowConfig`) -/

/-- Pure mirror of `MultiStark.FinalNarrow.Header` (`tag`, `key`, `values`). -/
structure NarrowClaimHeader where
  tag : Nat
  key : Nat
  values : Nat
  deriving DecidableEq, Repr

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
