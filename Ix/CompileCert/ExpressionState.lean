import Ix.CompileCert.UniversePipeline
import Ix.CompileCert.BlobWrites
import Ix.CompileCert.Serializers
import Batteries.Data.List.Basic

/-! # The ordinary expression compiler: state, source relation, effects

The state and source/reader contracts of `Ix.CompileM.compileExpr`
(CT-13's expression core, re-derived for this tree):

* **The source relation** `Related names levels`: an `Ix.Expr` and the
  checker term the certified reader reads, independent of compiler
  success. It is Source mode's own reading (`Ix.LeanIngress.ingressExpr`)
  case for case, with two parameters for what the compiled side reads
  through tables: constant keys (`names`, the declaration prefix's
  correspondence) and levels (`levels`, by value: `LevelMeaning`). Hashes,
  binder names and plain metadata do not enter it; a contract frame puts
  its contract on the binder it wraps (`withContract`), as the ingress and
  the compiler's `Contract.lower` do.
* **The state invariant** `Good`: the universe invariants
  (`UniversePipeline.Sound`), the reference index, the fixed binding view
  of the declaration prefix, and the expression memo's meaning
  (`CacheSound` over `ExpressionRead.KeyReading`, at exact cache keys).
* **`Checked`**: a run keeps `Good`, extends the in-flight reader, and a
  successful one returns a value that reads as a related term.
* Each effect the compiler's steps perform keeps `Good` and extends the
  reader: metadata allocation (`good_metadata`), reference interning
  (`internRef_good`), blob and name writes (`storeBlob_good`,
  `compileName_good`), the metadata serializer (`compileKVMap_good`) and
  universe compilation (`compileLevel_good`, `compileLevels_good`). -/

namespace Ix.CompileCert.ExpressionState

open Ix.CompileM Ix.CompileCert Ix.CompileCert.UniversePipeline
open Ix.Kernel (Mode LevelParam)
open Ix.Kernel.Reader (Ctx CName CExpr ReadM)

/-! ## The source relation -/

/-- The checker side of a contract frame: the binder's metadata takes the
contract, exactly as `Ix.LeanIngress.withContract` puts it, on a binder of
the frame's kind. -/
def withContract {md : Mode} (c : Ix.SemanticContract.Contract) (source : Ix.Expr)
    (target : CExpr md) : Option (CExpr md) :=
  match c.kind, source, target with
  | .lam, .lam .., .lam t b m => some (.lam t b { m with contract := c.binder })
  | .all, .forallE .., .forallE t b m =>
    some (.forallE t b { m with contract := c.binder, result := c.result })
  | .letE, .letE .., .letE t v b l =>
    some (.letE t v b { contract := { l.contract with binder := c.binder, kind := c.letKind } })
  | _, _, _ => none

/-- A source expression and the checker term the certified reader reads,
independently of compiler success. Each case is the ingress's
(`Ix.LeanIngress.ingressExpr`): constants are related through `names`, and
levels through `levels`. -/
inductive Related {md : Mode} (names : Ix.Name → CName md → Prop)
    (levels : Ix.Level → Kernel.Level → Prop) : Ix.Expr → CExpr md → Prop where
  | bvar (index : Nat) (hash : Address) :
      Related names levels (.bvar index hash) (Ix.Kernel.Expr.mkBvar index)
  | sort {source : Ix.Level} {level : Kernel.Level} (hash : Address) (meaning : levels source level) :
      Related names levels (.sort source hash) (.sort level)
  | const {name : Ix.Name} {key : CName md} (hash : Address) (sources : Array Ix.Level)
      (targets : List Kernel.Level) (mapped : names name key)
      (universes : List.Forall₂ levels sources.toList targets) :
      Related names levels (.const name sources hash) (.const key targets)
  | app {fn arg : Ix.Expr} {targetFn targetArg : CExpr md} (hash : Address)
      (fnRel : Related names levels fn targetFn) (argRel : Related names levels arg targetArg) :
      Related names levels (.app fn arg hash) (.app targetFn targetArg)
  | lam {type body : Ix.Expr} {targetType targetBody : CExpr md} (name : Ix.Name)
      (info : Lean.BinderInfo) (hash : Address)
      (typeRel : Related names levels type targetType) (bodyRel : Related names levels body targetBody) :
      Related names levels (.lam name type body info hash) (.lam targetType targetBody { pw := .never })
  | all {type body : Ix.Expr} {targetType targetBody : CExpr md} (name : Ix.Name)
      (info : Lean.BinderInfo) (hash : Address)
      (typeRel : Related names levels type targetType) (bodyRel : Related names levels body targetBody) :
      Related names levels (.forallE name type body info hash)
        (.forallE targetType targetBody { pw := .never })
  | letE {type value body : Ix.Expr} {targetType targetValue targetBody : CExpr md} (name : Ix.Name)
      (nonDep : Bool) (hash : Address)
      (typeRel : Related names levels type targetType)
      (valueRel : Related names levels value targetValue)
      (bodyRel : Related names levels body targetBody) :
      Related names levels (.letE name type value body nonDep hash)
        (.letE targetType targetValue targetBody { contract := .lean nonDep })
  | nat (value : Nat) (hash : Address) :
      Related names levels (.lit (.natVal value) hash) (.lit (.natVal value))
  | str (value : String) (hash : Address) :
      Related names levels (.lit (.strVal value) hash) (.lit (.strVal value))
  | proj {name : Ix.Name} {key : CName md} {value : Ix.Expr} {targetValue : CExpr md} (field : Nat)
      (hash : Address) (mapped : names name key) (valueRel : Related names levels value targetValue) :
      Related names levels (.proj name field value hash) (.proj key field targetValue)
  | mdata {source : Ix.Expr} {target : CExpr md} (data : Array (Ix.Name × Ix.DataValue))
      (hash : Address) (plain : Ix.SemanticContract.hasMetadata data = false)
      (bodyRel : Related names levels source target) :
      Related names levels (.mdata data source hash) target
  | contract {source : Ix.Expr} {target result : CExpr md} (data : Array (Ix.Name × Ix.DataValue))
      (hash : Address) (c : Ix.SemanticContract.Contract)
      (frame : Ix.SemanticContract.hasMetadata data = true)
      (read : Ix.SemanticContract.read data = .ok c)
      (bodyRel : Related names levels source target) (lowered : withContract c source target = some result) :
      Related names levels (.mdata data source hash) result

/-! ## External references -/

abbrev Bindings :=
  Std.HashMap Ix.Compile.ExactKey.ExactName Address

/-- The block's own binding map (its primary registrations), which expression
compilation never writes. -/
def bindingView (state : BlockState) : Bindings := state.blockNameToAddr

/-- The production precedence between local and published bindings
(`Ix.CompileM.lookupConstAddr`). -/
def lookupBinding (env : CompileEnv) (bindings : Bindings) (name : Ix.Name) : Option Address :=
  (bindings.get? name).orElse fun _ => env.nameToAddr.get? name

theorem lookupConstAddr_run (name : Ix.Name) (context : CompileEnv × BlockEnv) (before : BlockState) :
    rawRun (lookupConstAddr name) context before =
      ((match lookupBinding context.1 (bindingView before) name with
        | some address => .ok address
        | none => .error (.missingConstant s!"{name}")), before) := by
  simp only [lookupConstAddr, rawRun_bind, rawRun_read, rawRun_get, lookupBinding, bindingView]
  cases before.blockNameToAddr.get? name with
  | some address => rfl
  | none => cases context.1.nameToAddr.get? name <;> rfl

theorem lookupConstAddr_state (name : Ix.Name) (context : CompileEnv × BlockEnv) (before : BlockState) :
    (rawRun (lookupConstAddr name) context before).2 = before := by
  rw [lookupConstAddr_run]

/-- The declaration-prefix obligation for external references: a name the
compiler resolves reads, at its address, as a key `names` relates to it. -/
def BindingsCorrect {md : Mode} (env : CompileEnv) (bindings : Bindings) (cx : Ctx md)
    (names : Ix.Name → CName md → Prop) : Prop :=
  ∀ name address, lookupBinding env bindings name = some address →
    ∃ key, cx.keyAt address = .ok key ∧ names name key

theorem lookupConstAddr_correct {md : Mode} (name : Ix.Name) (context : CompileEnv × BlockEnv)
    (before : BlockState) (bindings : Bindings) (fixed : bindingView before = bindings) (cx : Ctx md)
    (names : Ix.Name → CName md → Prop) (valid : BindingsCorrect context.1 bindings cx names)
    {address : Address} (success : (rawRun (lookupConstAddr name) context before).1 = .ok address) :
    ∃ key, cx.keyAt address = .ok key ∧ names name key := by
  rw [lookupConstAddr_run, fixed] at success
  cases found : lookupBinding context.1 bindings name with
  | none => rw [found] at success; cases success
  | some actual =>
    rw [found] at success
    cases Except.ok.inj success
    exact valid name address found

/-- The block's own members: a member slot reads as a key `names` relates to
the member's name. -/
def SelfCorrect {md : Mode} (block : BlockEnv) (self : Nat → Option (ReadM (CName md)))
    (names : Ix.Name → CName md → Prop) : Prop :=
  ∀ name index, block.mutCtx.get? name = some index →
    ∃ key, self index = some (.ok key) ∧ names name key

/-- A member slot of the block, if `name` has one, reads as a key `names`
relates to `name`. -/
def SelfName {md : Mode} (block : BlockEnv) (self : Nat → Option (ReadM (CName md)))
    (names : Ix.Name → CName md → Prop) (name : Ix.Name) : Prop :=
  ∀ index, block.mutCtx.get? name = some index → ∃ key, self index = some (.ok key) ∧ names name key

/-- Every constant occurrence of `e` satisfies `P` (a projection's structure
name is resolved as an external reference, so it is not an occurrence). -/
def ConstsSatisfy (P : Ix.Name → Prop) : Ix.Expr → Prop
  | .const name _ _ => P name
  | .app f a _ => ConstsSatisfy P f ∧ ConstsSatisfy P a
  | .lam _ t b _ _ | .forallE _ t b _ _ => ConstsSatisfy P t ∧ ConstsSatisfy P b
  | .letE _ t v b _ _ => ConstsSatisfy P t ∧ ConstsSatisfy P v ∧ ConstsSatisfy P b
  | .proj _ _ e _ => ConstsSatisfy P e
  | .mdata _ e _ => ConstsSatisfy P e
  | _ => True

theorem constsSatisfy_of_forall {P : Ix.Name → Prop} (all : ∀ name, P name) :
    ∀ e, ConstsSatisfy P e := by
  intro e
  induction e <;> simp_all [ConstsSatisfy]

theorem constsSatisfy_mono {P Q : Ix.Name → Prop} (implies : ∀ name, P name → Q name) :
    ∀ e, ConstsSatisfy P e → ConstsSatisfy Q e := by
  intro e
  induction e <;> simp_all [ConstsSatisfy]

/-! ## The state invariant -/

/-- The universe invariants, the reference index, and the binding view of
the declaration prefix. -/
def StateSound (bindings : Bindings) (state : BlockState) : Prop :=
  Sound state ∧ Interning.RefIndexSound state ∧ bindingView state = bindings

/-- Arena metadata and spelling patches: not inputs of the certified
reader. -/
def withoutExprMetadata (state : BlockState) : BlockState :=
  { state with arena := {}, univPatches := #[] }

/-- The reference interner changes only the reference table and its index. -/
def withoutRefTables (state : BlockState) : BlockState :=
  { state with refs := #[], refsIndex := {} }

theorem internRef_frame (address : Address) : Preserves withoutRefTables (internRef address) := by
  intro context before
  by_cases wide : address.hash.size = 32
  case neg =>
    obtain ⟨e, h⟩ := Interning.internRef_narrow address context before wide
    rw [h]
  cases found : before.refsIndex.get? address with
  | some index => rw [Interning.internRef_hit address context before wide found]
  | none =>
    rw [Interning.internRef_miss address context before wide found]
    split
    · rfl
    · rw [Interning.checkedTableCount_state]

open private Nat.toBytesLE.go from Ix.Common

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

/-- A natural-number literal's blob reads back as the literal. -/
theorem natural_toBytes (value : Nat) :
    Kernel.Reader.natural (ByteArray.mk (Nat.toBytesLE value)) = value := by
  unfold Kernel.Reader.natural Nat.toBytesLE
  by_cases zero : value = 0
  · subst value; rfl
  · simp only [beq_iff_eq, zero, ↓reduceIte]
    rw [← Array.foldr_toList]
    simpa only [List.toList_toArray] using natural_go value value (Nat.le_refl _)

/-- A string literal's blob reads back as the literal. -/
theorem string_toBytes (value : String) : String.fromUTF8? value.toUTF8 = some value := by
  simp [String.fromUTF8?, String.toUTF8, String.fromUTF8, value.isValidUTF8]

theorem extends_trans {md : Mode} {first middle last : Kernel.Reader.ECx md}
    (head : ExpressionRead.Extends first middle) (tail : ExpressionRead.Extends middle last) :
    ExpressionRead.Extends first last :=
  ⟨fun index value found => tail.level index value (head.level index value found),
    fun index value found => tail.key index value (head.key index value found),
    fun index value found => tail.blob index value (head.blob index value found),
    fun index member found => tail.self index member (head.self index member found)⟩

section Effects

variable {md : Mode} (cx : Ctx md) (param : Nat → LevelParam)
  (self : Nat → Option (ReadM (CName md))) (related : Ix.Expr → CExpr md → Prop)
  (bindings : Bindings)

local notation "reader" => ExpressionRead.blockReader cx param self
local notation "meaning" => ExpressionRead.Reading related reader

/-- The state invariant of the expression compiler. -/
def Good (state : BlockState) : Prop :=
  StateSound bindings state ∧ CacheSound (ExpressionRead.KeyReading related reader state) state.exprCache

/-- A run keeps `Good`, extends the in-flight reader, and a successful one
returns a value that reads as a term related to `source`. -/
def Checked (source : Ix.Expr) (before : BlockState)
    (result : Except CompileError (Ixon.Expr × UInt64) × BlockState) : Prop :=
  Good cx param self related bindings result.2 ∧
    ExpressionRead.Extends (reader before).ecx (reader result.2).ecx ∧
    ∀ value, result.1 = .ok value → meaning result.2 source value

/-- A failing run that keeps `Good` and extends the reader is `Checked`. -/
theorem checked_error {source : Ix.Expr} {before after : BlockState} (error : CompileError)
    (good : Good cx param self related bindings after)
    (growth : ExpressionRead.Extends (reader before).ecx (reader after).ecx) :
    Checked cx param self related bindings source before (.error error, after) :=
  ⟨good, growth, by intro value bad; cases bad⟩

/-- A reading survives every extension of the in-flight reader. -/
theorem meaning_grows {before after : BlockState}
    (growth : ExpressionRead.Extends (reader before).ecx (reader after).ecx)
    {source : Ix.Expr} {value : Ixon.Expr × UInt64} (prior : meaning before source value) :
    meaning after source value := by
  apply ExpressionRead.Reading.of_growth growth ?_ prior
  intro index value found
  rw [ExpressionRead.blockReader_tbl] at found
  simp at found

theorem read_grows {before after : BlockState}
    (growth : ExpressionRead.Extends (reader before).ecx (reader after).ecx)
    {value : Ixon.Expr} {target : CExpr md} (prior : (reader before).read value = .ok target) :
    (reader after).read value = .ok target := by
  apply ExpressionRead.convExpr_preserves growth ?_ value target prior
  intro index value found
  rw [ExpressionRead.blockReader_tbl] at found
  simp at found

theorem withoutExprMetadata_reader {before after : BlockState}
    (frame : withoutExprMetadata after = withoutExprMetadata before) :
    ExpressionRead.blockReader cx param self after = ExpressionRead.blockReader cx param self before := by
  have same := congrArg (ExpressionRead.blockReader cx param self) frame
  exact same

/-- Metadata allocation keeps `Good`. -/
theorem good_metadata {before after : BlockState}
    (frame : withoutExprMetadata after = withoutExprMetadata before)
    (good : Good cx param self related bindings before) : Good cx param self related bindings after := by
  have sameReader := withoutExprMetadata_reader cx param self frame
  have sameCache : after.exprCache = before.exprCache := by
    have same := congrArg BlockState.exprCache frame; exact same
  refine ⟨⟨Sound.of_view (by have same := congrArg univView frame; exact same) good.1.1, ?_, ?_⟩, ?_⟩
  · have same := congrArg Interning.RefIndexSound frame
    exact same.mpr good.1.2.1
  · have same := congrArg bindingView frame
    exact same.trans good.1.2.2
  · intro key value found
    rw [sameCache] at found
    obtain ⟨target, rel, read⟩ := good.2 key value found
    exact ⟨target, rel, by rw [sameReader]; exact read⟩

/-- A metadata-only step returning a value that already reads as a related
term is `Checked`. -/
theorem checked_metadata {source : Ix.Expr} {before after : BlockState}
    (frame : withoutExprMetadata after = withoutExprMetadata before)
    (good : Good cx param self related bindings before) {value : Ixon.Expr × UInt64}
    (prior : meaning before source value) :
    Checked cx param self related bindings source before (.ok value, after) := by
  have same := withoutExprMetadata_reader cx param self frame
  refine ⟨good_metadata cx param self related bindings frame good, ?_, ?_⟩
  · rw [same]; exact ExpressionRead.Extends.refl _
  · intro result success
    cases Except.ok.inj success
    obtain ⟨target, rel, read⟩ := prior
    exact ⟨target, rel, by rw [same]; exact read⟩

theorem internRef_good (address : Address) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx param self related bindings before) :
    let result := rawRun (internRef address) context before
    Good cx param self related bindings result.2 ∧
      ExpressionRead.Extends (reader before).ecx (reader result.2).ecx ∧
      ∀ index, result.1 = .ok index → result.2.refs[index.toNat]? = some address := by
  have frame := internRef_frame address context before
  have correct := Interning.internRef_correct address context before good.1.2.1
  refine ⟨⟨⟨Sound.of_view (by have same := congrArg univView frame; exact same) good.1.1, correct.1, ?_⟩,
    Interning.internRef_cache_sound address context before cx param self related good.2⟩,
    Interning.internRef_reading address context before cx param self, correct.2.2⟩
  have same := congrArg bindingView frame
  exact same.trans good.1.2.2

/-- A names-and-blobs step keeps `Good` and extends the reader. -/
theorem good_namesBlobs (context : CompileEnv × BlockEnv) {before after : BlockState}
    (frame : BlobWrites.withoutNamesBlobs after = BlobWrites.withoutNamesBlobs before)
    (grows : BlobWrites.Extends context.1.blobs before after)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (good : Good cx param self related bindings before) :
    Good cx param self related bindings after ∧
      ExpressionRead.Extends (reader before).ecx (reader after).ecx := by
  refine ⟨⟨⟨Sound.of_view (by have same := congrArg univView frame; exact same) good.1.1, ?_, ?_⟩,
    BlobWrites.cache_preserved context.1.blobs before after frame grows cx param self aligned related good.2⟩,
    BlobWrites.reader_extends context.1.blobs before after frame grows cx param self aligned⟩
  · have same := congrArg Interning.RefIndexSound frame
    exact same.mpr good.1.2.1
  · have same := congrArg bindingView frame
    exact same.trans good.1.2.2

theorem storeBlob_good (bytes : ByteArray) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx param self related bindings before)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address) :
    let result := rawRun (storeBlob bytes) context before
    Good cx param self related bindings result.2 ∧
      ExpressionRead.Extends (reader before).ecx (reader result.2).ecx ∧
      ∀ address, result.1 = .ok address → result.2.blockBlobs.get? address = some bytes := by
  have preserved := BlobWrites.storeBlob_preserves bytes context before
  have kept := good_namesBlobs cx param self related bindings context preserved.1 preserved.2.1 aligned good
  exact ⟨kept.1, kept.2, preserved.2.2⟩

theorem compileName_good (name : Ix.Name) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx param self related bindings before)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address) :
    let after := (rawRun (compileName name) context before).2
    Good cx param self related bindings after ∧
      ExpressionRead.Extends (reader before).ecx (reader after).ecx := by
  have preserved := BlobWrites.compileName_preserves name context before
  exact good_namesBlobs cx param self related bindings context preserved.1 preserved.2 aligned good

theorem compileKVMap_good (data : Array (Ix.Name × Ix.DataValue)) (context : CompileEnv × BlockEnv)
    (before : BlockState) (good : Good cx param self related bindings before)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address) :
    let after := (rawRun (compileKVMap data) context before).2
    Good cx param self related bindings after ∧
      ExpressionRead.Extends (reader before).ecx (reader after).ecx := by
  have preserved := Serializers.NamesBlobs.compileKVMap data context before
  exact good_namesBlobs cx param self related bindings context preserved.1 preserved.2 aligned good

/-- The literal slot `index` of the in-flight reader reads the blob at its
reference. -/
theorem blockReader_blob (state : BlockState) {index : UInt64} {address : Address} {bytes : ByteArray}
    (found : state.refs[index.toNat]? = some address)
    (stored : state.blockBlobs.get? address = some bytes) :
    (reader state).ecx.blobAt index = .ok bytes := by
  unfold Kernel.Reader.ECx.blobAt
  change (do
    let some key := state.refs[index.toNat]? | Kernel.Reader.malformed "literal reference index is out of bounds"
    let some value := (state.blockBlobs.get? key).orElse (fun _ => cx.blob key)
      | Kernel.Reader.malformed s!"literal blob {key} is missing"
    pure value) = _
  rw [found]
  dsimp only
  rw [stored]
  rfl

/-- The reference slot `index` of the in-flight reader reads the key at its
address. -/
theorem blockReader_key (state : BlockState) {index : UInt64} {address : Address} {key : CName md}
    (found : state.refs[index.toNat]? = some address) (read : cx.keyAt address = .ok key) :
    (reader state).ecx.keyAt index = .ok key := by
  unfold Kernel.Reader.ECx.keyAt
  change (do
    let some a := state.refs[index.toNat]? | Kernel.Reader.malformed "reference index is out of bounds"
    (ExpressionRead.withBlockBlobs cx state).keyAt a) = _
  rw [found]
  exact read

/-- Universe compilation keeps `Good`, extends the reader, and a successful
run's slot reads as a level that means the source level. -/
theorem compileLevel_good (source : Ix.Level) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx param self related bindings before) (σ : Ix.Name → LevelParam) :
    let result := rawRun (compileAndInternUnivCanon source) context before
    Good cx param self related bindings result.2 ∧
      ExpressionRead.Extends (reader before).ecx (reader result.2).ecx ∧
      ∀ value, result.1 = .ok value → ∃ level,
        (reader result.2).ecx.level value.1 = .ok level ∧
        LevelMeaning context.2.univCtx σ param source level := by
  have correct := compileAndInternUnivCanon_correct source context before good.1.1
  have frame := compileAndInternUnivCanon_frame source context before
  refine ⟨⟨⟨correct.1, ?_, ?_⟩,
    compileAndInternUnivCanon_cache_sound source context before good.1.1 cx param self related good.2⟩,
    compileAndInternUnivCanon_reading source context before good.1.1 cx param self, ?_⟩
  · have same := congrArg Interning.RefIndexSound frame
    exact same.mpr good.1.2.1
  · have same := congrArg bindingView frame
    exact same.trans good.1.2.2
  · intro value success
    have ran : rawRun (compileAndInternUnivCanon source) context before =
        (.ok value, (rawRun (compileAndInternUnivCanon source) context before).2) :=
      Prod.ext success rfl
    exact (compileAndInternUnivCanon_read source context before good.1.1 ran cx param self σ).2

/-- Compiled universe arguments keep their source order and meaning. -/
def LevelsRead (params : List Ix.Name) (σ : Ix.Name → LevelParam) (sources : List Ix.Level)
    (values : List (UInt64 × Option UInt64)) (state : BlockState) : Prop :=
  ∃ targets, List.Forall₂ (LevelMeaning params σ param) sources targets ∧
    (values.map Prod.fst).mapM (reader state).ecx.level = .ok targets

theorem compileLevels_list_good (sources : List Ix.Level) (context : CompileEnv × BlockEnv)
    (σ : Ix.Name → LevelParam) :
    ∀ before, Good cx param self related bindings before →
      let result := rawRun (sources.mapM compileAndInternUnivCanon) context before
      Good cx param self related bindings result.2 ∧
        ExpressionRead.Extends (reader before).ecx (reader result.2).ecx ∧
        ∀ values, result.1 = .ok values →
          LevelsRead cx param self context.2.univCtx σ sources values result.2 := by
  induction sources with
  | nil =>
    intro before good
    refine ⟨good, ExpressionRead.Extends.refl _, ?_⟩
    intro values success
    cases Except.ok.inj success
    exact ⟨[], .nil, rfl⟩
  | cons source rest ih =>
    intro before good
    rw [List.mapM_cons, rawRun_bind]
    have head := compileLevel_good cx param self related bindings source context before good σ
    cases ran : rawRun (compileAndInternUnivCanon source) context before with
    | mk outcome middle =>
      rw [ran] at head
      cases outcome with
      | error error => exact ⟨head.1, head.2.1, by intro values bad; cases bad⟩
      | ok value =>
        dsimp only
        rw [rawRun_bind]
        have tail := ih middle head.1
        cases tailRun : rawRun (rest.mapM compileAndInternUnivCanon) context middle with
        | mk outcome after =>
          rw [tailRun] at tail
          cases outcome with
          | error error => exact ⟨tail.1, extends_trans head.2.1 tail.2.1, by intro values bad; cases bad⟩
          | ok values =>
            refine ⟨tail.1, extends_trans head.2.1 tail.2.1, ?_⟩
            intro output success
            cases Except.ok.inj success
            obtain ⟨level, readLevel, levelMeaning⟩ := head.2.2 value rfl
            obtain ⟨levels, relatedLevels, readLevels⟩ := tail.2.2 values rfl
            refine ⟨level :: levels, .cons levelMeaning relatedLevels, ?_⟩
            have retained := tail.2.1.level value.1 level readLevel
            change ((value.1 :: values.map Prod.fst).mapM (reader after).ecx.level) = .ok (level :: levels)
            simp only [List.mapM_cons, retained, readLevels]
            rfl

theorem compileLevels_good (sources : Array Ix.Level) (context : CompileEnv × BlockEnv)
    (before : BlockState) (good : Good cx param self related bindings before) (σ : Ix.Name → LevelParam) :
    let result := rawRun (sources.mapM compileAndInternUnivCanon) context before
    Good cx param self related bindings result.2 ∧
      ExpressionRead.Extends (reader before).ecx (reader result.2).ecx ∧
      ∀ values, result.1 = .ok values → ∃ levels,
        List.Forall₂ (LevelMeaning context.2.univCtx σ param) sources.toList levels ∧
        (reader result.2).ecx.levels (values.map Prod.fst) = .ok levels := by
  rw [Array.mapM_eq_mapM_toList]
  have correct := compileLevels_list_good cx param self related bindings sources.toList context σ before good
  simp only [map_eq_pure_bind, rawRun_bind]
  cases ran : rawRun (sources.toList.mapM compileAndInternUnivCanon) context before with
  | mk outcome after =>
    rw [ran] at correct
    cases outcome with
    | error error => exact ⟨correct.1, correct.2.1, by intro values bad; cases bad⟩
    | ok values =>
      simp only [rawRun_pure]
      refine ⟨correct.1, correct.2.1, ?_⟩
      intro output success
      cases Except.ok.inj success
      obtain ⟨levels, rel, read⟩ := correct.2.2 values rfl
      exact ⟨levels, rel, by
        simpa only [Kernel.Reader.ECx.levels, Array.toList_map, List.toList_toArray] using read⟩

end Effects

end Ix.CompileCert.ExpressionState
