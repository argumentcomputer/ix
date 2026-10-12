import Ix.CompileCert.ExpressionLeaves
import Ix.CompileCert.BlobWrites
import Ix.CompileCert.ExpressionIndices

/-! State and source/reader contracts for ordinary expression compilation.
The source relation is independent of compiler success. It preserves source
structure, positional universe meaning and the declaration prefix's logical
name correspondence; hashes and presentation metadata do not enter it. -/

namespace Ix.CompileCert.ExpressionState

open Ix.CompileM Ix.CompileCert.HeadWriterFrame
open Ix.CompileCert.ExpressionCacheRun (Meaning Valid)

open private Nat.toBytesLE.go from Ix.Common

def CorrectResult (invariant : BlockState → Prop) (meaning : Meaning) (source : Ix.Expr)
    (result : Except CompileError (Ixon.Expr × UInt64) × BlockState) : Prop :=
  invariant result.2 ∧ ExpressionCacheRun.CorrectResult meaning source result

/-- Inserting into the expression memo cannot change the independent table
and reader-state invariant. Content validity of that memo is handled separately. -/
def CacheBlind (invariant : BlockState → Prop) : Prop :=
  ∀ state cache, invariant { state with exprCache := cache } = invariant state

theorem cached_correct (invariant : BlockState → Prop) (stateBlind : CacheBlind invariant)
    (meaning : Meaning) (meaningBlind : ExpressionCacheRun.CacheBlind meaning)
    (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (source : Ix.Expr)
    (context : CompileEnv × BlockEnv) (before : BlockState) (stateValid : invariant before)
    (cacheValid : Valid meaning before)
    (step : before.exprCache.get? source = none →
      CorrectResult invariant meaning source (rawRun (compile source) context before)) :
    CorrectResult invariant meaning source (rawRun (ExpressionRuntime.cached compile source) context before) := by
  refine ⟨?_, ExpressionCacheRun.cached_run_correct meaning meaningBlind compile source context before cacheValid
    (fun missing => (step missing).2)⟩
  simp only [ExpressionRuntime.cached, rawRun_bind, rawRun_get]
  cases found : before.exprCache.get? source with
  | some value => exact stateValid
  | none =>
    have invariantAfter := (step found).1
    simp only [rawRun_bind]
    cases ran : rawRun (compile source) context before with
    | mk outcome after =>
      rw [ran] at invariantAfter
      cases outcome with
      | error error => exact invariantAfter
      | ok value =>
        cases value with
        | mk expr root =>
          simp only [rawRun_modify, rawRun_pure]
          exact (stateBlind after (after.exprCache.insert source (expr, root))).mpr invariantAfter

theorem universe_cacheBlind : CacheBlind UniversePipeline.Sound := by
  intro state cache
  apply propext
  constructor
  · intro valid
    exact ⟨valid.rawCache, valid.canonCache, valid.tables⟩
  · exact ExpressionLeaves.sound_exprCache state cache

/-- A source/reader relation independent of compilation success. Universe
meaning is positional; constant names are related by the dependency-prefix
correspondence. Source hashes, binder names and presentation metadata are not
part of the resulting kernel syntax. -/
inductive Related (names : Ix.Name → Kernel.Name → Prop)
    (sourceParams : List Ix.Name) (params : List Kernel.Name) : Ix.Expr → Kernel.Expr → Prop where
  | bvar (index : Nat) (hash : Address) : Related names sourceParams params (.bvar index hash) (.bvar index)
  | sort {source level} (hash : Address) (meaning : ExpressionLeaves.LevelMeaning sourceParams params source level) :
      Related names sourceParams params (.sort source hash) (.sort level)
  | const {name target} (hash : Address) (levels : Array Ix.Level) (targetLevels : List Kernel.Level)
      (mapped : names name target)
      (universes : List.Forall₂ (ExpressionLeaves.LevelMeaning sourceParams params) levels.toList targetLevels) :
      Related names sourceParams params (.const name levels hash) (.const target targetLevels)
  | app {fn arg targetFn targetArg} (hash : Address)
      (fnRel : Related names sourceParams params fn targetFn) (argRel : Related names sourceParams params arg targetArg) :
      Related names sourceParams params (.app fn arg hash) (.app targetFn targetArg)
  | lam {type body targetType targetBody} (name : Ix.Name) (info : Lean.BinderInfo) (hash : Address)
      (typeRel : Related names sourceParams params type targetType) (bodyRel : Related names sourceParams params body targetBody) :
      Related names sourceParams params (.lam name type body info hash) (.lam targetType targetBody ⟨.never⟩)
  | all {type body targetType targetBody} (name : Ix.Name) (info : Lean.BinderInfo) (hash : Address)
      (typeRel : Related names sourceParams params type targetType) (bodyRel : Related names sourceParams params body targetBody) :
      Related names sourceParams params (.forallE name type body info hash) (.forallE targetType targetBody ⟨.never⟩)
  | letE {type value body targetType targetValue targetBody} (name : Ix.Name) (nonDep : Bool) (hash : Address)
      (typeRel : Related names sourceParams params type targetType)
      (valueRel : Related names sourceParams params value targetValue) (bodyRel : Related names sourceParams params body targetBody) :
      Related names sourceParams params (.letE name type value body nonDep hash) (.letE targetType targetValue targetBody)
  | nat (value : Nat) (hash : Address) : Related names sourceParams params (.lit (.natVal value) hash) (.lit (.natVal value))
  | str (value : String) (hash : Address) : Related names sourceParams params (.lit (.strVal value) hash) (.lit (.strVal value))
  | proj {name target value targetValue} (field : Nat) (hash : Address) (mapped : names name target)
      (valueRel : Related names sourceParams params value targetValue) :
      Related names sourceParams params (.proj name field value hash) (.proj target field targetValue)
  | mdata {source target} (data : Array (Ix.Name × Ix.DataValue)) (hash : Address)
      (bodyRel : Related names sourceParams params source target) :
      Related names sourceParams params (.mdata data source hash) target

theorem extends_refl (reader : Kernel.Reader.ECx) : ExpressionRead.Extends reader reader :=
  ⟨fun _ _ success => success, fun _ _ success => success, fun _ _ success => success,
    fun _ _ found => found, fun _ => rfl⟩

theorem extends_trans {first middle last : Kernel.Reader.ECx}
    (head : ExpressionRead.Extends first middle) (tail : ExpressionRead.Extends middle last) :
    ExpressionRead.Extends first last :=
  ⟨fun index value found => tail.level index value (head.level index value found),
    fun index value found => tail.ref index value (head.ref index value found),
    fun index value found => tail.blob index value (head.blob index value found),
    fun index value found => tail.self index value (head.self index value found),
    fun ref => (tail.name ref).trans (head.name ref)⟩

abbrev Bindings := Std.HashMap Ix.Name Address × Std.HashMap Ix.Name Address

def bindingView (state : BlockState) : Bindings := (state.blockNameToAddr, state.auxNameToAddr)

/-- The production precedence among local, published and auxiliary bindings.
This view is independent of expression tables and memos. -/
def lookupBinding (env : CompileEnv) (bindings : Bindings) (name : Ix.Name) : Option Address :=
  (bindings.1.get? name).orElse fun _ => (env.nameToAddr.get? name).orElse fun _ =>
    (bindings.2.get? name).orElse fun _ => env.auxNameToAddr.get? name

theorem lookupConstAddr_run (name : Ix.Name) (context : CompileEnv × BlockEnv) (before : BlockState) :
    rawRun (lookupConstAddr name) context before =
      ((match lookupBinding context.1 (bindingView before) name with
        | some address => .ok address
        | none => .error (.missingConstant s!"{name}")), before) := by
  simp only [lookupConstAddr, rawRun_bind, rawRun_read, rawRun_get, lookupBinding, bindingView]
  cases before.blockNameToAddr.get? name with
  | some address => rfl
  | none =>
    cases context.1.nameToAddr.get? name with
    | some address => rfl
    | none =>
      cases before.auxNameToAddr.get? name with
      | some address => rfl
      | none => cases context.1.auxNameToAddr.get? name <;> rfl

/-- The declaration-prefix obligation for external references: successful
source lookup resolves to an anonymous reference with the related logical
kernel identity. It assumes no theorem about expression compilation. -/
def BindingsCorrect (env : CompileEnv) (bindings : Bindings) (reader : Kernel.Reader.Ctx)
    (names : Ix.Name → Kernel.Name → Prop) : Prop :=
  ∀ name address, lookupBinding env bindings name = some address →
    ∃ ref, Kernel.Reader.resolve reader.store address = some ref ∧ names name (reader.nameOf ref)

theorem lookupConstAddr_correct (name : Ix.Name) (context : CompileEnv × BlockEnv) (before : BlockState)
    (bindings : Bindings) (fixed : bindingView before = bindings) (reader : Kernel.Reader.Ctx)
    (names : Ix.Name → Kernel.Name → Prop) (valid : BindingsCorrect context.1 bindings reader names)
    {address : Address} (success : (rawRun (lookupConstAddr name) context before).1 = .ok address) :
    ∃ ref, Kernel.Reader.resolve reader.store address = some ref ∧ names name (reader.nameOf ref) := by
  rw [lookupConstAddr_run, fixed] at success
  cases found : lookupBinding context.1 bindings name with
  | none => rw [found] at success; cases success
  | some actual =>
    rw [found] at success
    cases Except.ok.inj success
    exact valid name address found

theorem lookupConstAddr_state (name : Ix.Name) (context : CompileEnv × BlockEnv) (before : BlockState) :
    (rawRun (lookupConstAddr name) context before).2 = before := by
  rw [lookupConstAddr_run]

def SelfCorrect (block : BlockEnv) (self : Nat → Option Kernel.Name) (names : Ix.Name → Kernel.Name → Prop) : Prop :=
  ∀ name index, block.mutCtx.get? name = some index →
    ∃ target, self index = some target ∧ names name target

/-- Mutable table indices stay sound, and expression compilation retains the
source-name/address bindings supplied by the declaration-unit prefix. -/
def StateSound (bindings : Bindings) (state : BlockState) : Prop :=
  UniversePipeline.Sound state ∧ Interning.RefIndexSound state ∧ Interning.MetaRefIndexSound state ∧
    bindingView state = bindings

def withoutRefTables (state : BlockState) : BlockState :=
  { state with refs := #[], refsIndex := {}, p3MetaRefs := #[], p3MetaRefsIndex := {} }

open Interning in
theorem internRef_frame (address : Address) : UniversePipeline.Preserves withoutRefTables (internRef address) := by
  intro context before
  cases mode : before.p3MetaMode with
  | false =>
    cases found : before.refsIndex.get? address with
    | some index => rw [internRef_primary_hit address context before mode found]
    | none =>
      rw [internRef_primary_miss address context before mode found]
      split
      · rfl
      · rw [checkedTableIndex_state]
  | true =>
    rw [internRef_meta_run address context before mode]
    cases primary : before.refsIndex.get? address with
    | some index => rw [internRefMeta_primary_hit address context before primary]
    | none =>
      cases metadata : before.p3MetaRefsIndex.get? address with
      | some slot => rw [internRefMeta_extension_hit address context before primary metadata, checkedTableIndex_state]
      | none => rw [internRefMeta_miss address context before primary metadata]; split <;> rfl

open Interning in
theorem internRef_primary_metadata (address : Address) (context : CompileEnv × BlockEnv) (before : BlockState)
    (mode : before.p3MetaMode = false) :
    (rawRun (internRef address) context before).2.p3MetaRefs = before.p3MetaRefs ∧
      (rawRun (internRef address) context before).2.p3MetaRefsIndex = before.p3MetaRefsIndex := by
  cases found : before.refsIndex.get? address with
  | some index => rw [internRef_primary_hit address context before mode found]; exact ⟨rfl, rfl⟩
  | none =>
    rw [internRef_primary_miss address context before mode found]
    split
    · exact ⟨rfl, rfl⟩
    · rw [checkedTableIndex_state]; exact ⟨rfl, rfl⟩

open Interning in
theorem internRef_indices (address : Address) (context : CompileEnv × BlockEnv) (before : BlockState)
    (primary : RefIndexSound before) (metadata : MetaRefIndexSound before) :
    let result := rawRun (internRef address) context before
    RefIndexSound result.2 ∧ MetaRefIndexSound result.2 ∧
      ∀ index, result.1 = .ok index → (refTable result.2)[index.toNat]? = some address := by
  have afterMode := congrArg BlockState.p3MetaMode (internRef_frame address context before)
  change (rawRun (internRef address) context before).2.p3MetaMode = before.p3MetaMode at afterMode
  cases mode : before.p3MetaMode with
  | false =>
    have correct := internRef_primary_correct address context before mode primary
    have same := internRef_primary_metadata address context before mode
    refine ⟨correct.1, ?_, ?_⟩
    · intro query index found
      rw [same.2] at found
      rw [same.1]
      exact metadata query index found
    · intro index success
      simpa only [refTable, afterMode, mode, Bool.false_eq_true, ↓reduceIte] using correct.2.2 index success
  | true =>
    rw [internRef_meta_run address context before mode] at afterMode ⊢
    have correct := internRefMeta_correct address context before primary metadata
    refine ⟨correct.1, correct.2.1, ?_⟩
    intro index success
    simpa only [refTable, afterMode, mode, ↓reduceIte] using correct.2.2.2 index success

theorem state_cacheBlind (bindings : Bindings) : CacheBlind (StateSound bindings) := by
  intro state cache
  change (UniversePipeline.Sound { state with exprCache := cache } ∧
    Interning.RefIndexSound state ∧ Interning.MetaRefIndexSound state ∧ bindingView state = bindings) = StateSound bindings state
  rw [universe_cacheBlind state cache]
  rfl

theorem natural_go (fuel value : Nat) (bounded : value ≤ fuel) :
    (Nat.toBytesLE.go fuel value).foldr (fun byte rest => byte.toNat + 256 * rest) 0 = value := by
  induction fuel generalizing value with
  | zero =>
    have zero : value = 0 := by omega
    subst value
    rfl
  | succ fuel ih =>
    cases value with
    | zero => rfl
    | succ value =>
      rw [Nat.toBytesLE.go]
      simp only [List.foldr_cons]
      have smaller : (value + 1) / 256 ≤ fuel := by
        have less := Nat.div_lt_self (by omega : 0 < value + 1) (by decide : 1 < 256)
        omega
      rw [ih _ smaller]
      exact Nat.mod_add_div _ _
      all_goals omega

theorem natural_toBytes (value : Nat) : Kernel.Reader.natural (ByteArray.mk (Nat.toBytesLE value)) = value := by
  unfold Kernel.Reader.natural Nat.toBytesLE
  by_cases zero : value = 0
  · subst value; rfl
  · simp only [beq_iff_eq, zero, ↓reduceIte]
    rw [← Array.foldr_toList]
    simpa only [List.toList_toArray] using natural_go value value (Nat.le_refl _)

theorem string_toBytes (value : String) : String.fromUTF8? value.toUTF8 = some value := by
  simp [String.fromUTF8?, String.toUTF8, String.fromUTF8, value.isValidUTF8]


end Ix.CompileCert.ExpressionState
