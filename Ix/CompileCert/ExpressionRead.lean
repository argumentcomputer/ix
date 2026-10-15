import IxC.Kernel.Ixon.Reader
import Ix.CompileM
import Ix.CompileCert.CacheSound

/-! # The certified reader on the compiler's in-flight tables

The certified reader's expression interpretation (`Ix.Kernel.Reader.convExpr`)
survives table growth: a reading that succeeds against the compiler's block
state before a step succeeds, with the same result, after it, as long as
every successful leaf lookup the reader makes is preserved
(`convExpr_preserves`). This is the meaning-transport side of the compiler
cache proofs (`cache_sound_of_growth`). Production writers must still
establish table growth, and constructor steps must establish the source
relation of the values they add. These facts concern unshared expressions
before a record's sharing is built.

The reader is the one Ixon mode reads with, at any mode `md`: references
read as keys (`Ix.Kernel.Reader.ECx.keyAt`, which can decline), level
parameters are positions (`Nat → LevelParam`), and `recur i` reads the
reader's own `self i`. `blockReader` reads an in-flight expression against
the block state's primary tables, with the block's blobs overlaid on the
context's: the key of a reference does not depend on the blobs, so the
overlay never changes a key. -/

namespace Ix.CompileCert.ExpressionRead

open Ix.Kernel (Mode LevelParam)
open Ix.Kernel.Reader

/-- Successful readings survive extension; new entries may make a formerly
missing reference readable, so equality of errors is not required. -/
def Preserves (before after : ReadM α) : Prop :=
  ∀ value, before = .ok value → after = .ok value

theorem Preserves.refl (value : ReadM α) : Preserves value value := fun _ same => same

theorem Preserves.bind {before after : ReadM α} {first second : α → ReadM β}
    (head : Preserves before after) (tail : ∀ value, Preserves (first value) (second value)) :
    Preserves (before >>= first) (after >>= second) := by
  intro result success
  cases found : before with
  | error error => rw [found] at success; cases success
  | ok value =>
    have next := head value found
    rw [found] at success
    rw [next]
    exact tail value result success

/-- The leaves `convExpr` reads: universe slots, reference keys, blobs and
the block's own members. Nothing else of the context is read. -/
structure Extends {md : Mode} (before after : ECx md) : Prop where
  level : ∀ index, Preserves (before.level index) (after.level index)
  key : ∀ index, Preserves (before.keyAt index) (after.keyAt index)
  blob : ∀ index, Preserves (before.blobAt index) (after.blobAt index)
  self : ∀ index member, before.self index = some member → after.self index = some member

theorem Extends.refl {md : Mode} (context : ECx md) : Extends context context :=
  ⟨fun _ => .refl _, fun _ => .refl _, fun _ => .refl _, fun _ _ found => found⟩

theorem Extends.levels {md : Mode} {before after : ECx md} (growth : Extends before after)
    (indices : Array UInt64) : Preserves (before.levels indices) (after.levels indices) := by
  unfold ECx.levels
  suffices ∀ indices : List UInt64,
      Preserves (indices.mapM before.level) (indices.mapM after.level) from this _
  intro indices
  induction indices with
  | nil => exact .refl _
  | cons index rest ih =>
    rw [List.mapM_cons, List.mapM_cons]
    exact (growth.level index).bind fun _ => ih.bind fun _ => .refl _

/-- Reading an arbitrary Ixon expression gives the same result after its
successful leaf lookups and already-read sharing entries are preserved. -/
theorem convExpr_preserves {md : Mode} {before after : ECx md} (growth : Extends before after)
    {table nextTable : Array (ReadM (CExpr md))}
    (sharing : ∀ (index : Nat) (value : CExpr md), table[index]? = some (.ok value) →
      nextTable[index]? = some (.ok value)) (expr : Ixon.Expr) :
    Preserves (convExpr before table expr) (convExpr after nextTable expr) := by
  induction expr with
  | var index => exact .refl _
  | sort index => exact (growth.level index).bind fun _ => .refl _
  | ref index levels =>
    exact (growth.key index).bind fun _ => (growth.levels levels).bind fun _ => .refl _
  | recur index levels =>
    unfold convExpr
    cases found : before.self index.toNat with
    | none => intro value success; cases success
    | some member =>
      rw [growth.self _ _ found]
      exact (Preserves.refl member).bind fun _ => (growth.levels levels).bind fun _ => .refl _
  | prj index field value ih =>
    exact (growth.key index).bind fun _ => ih.bind fun _ => .refl _
  | str index => exact (growth.blob index).bind fun _ => .refl _
  | nat index => exact (growth.blob index).bind fun _ => .refl _
  | app fn arg ihf iha => exact ihf.bind fun _ => iha.bind fun _ => .refl _
  | lam _ ty body iht ihb => exact iht.bind fun _ => ihb.bind fun _ => .refl _
  | all _ _ ty body iht ihb => exact iht.bind fun _ => ihb.bind fun _ => .refl _
  | letE _ ty value body iht ihv ihb =>
    exact iht.bind fun _ => ihv.bind fun _ => ihb.bind fun _ => .refl _
  | share index =>
    intro value success
    unfold convExpr at *
    cases found : table[index.toNat]? with
    | none => simp [found, malformed] at success
    | some result =>
      have same : result = .ok value := by simpa [found] using success
      rw [sharing _ value (by simpa [same] using found)]

/-- A concrete table-growth discharger: the old reference and universe
slots, successful key readings and blob reads, and the block's members are
retained. The remaining fields of the record do not affect expression
reading. -/
theorem Extends.of_tables {md : Mode} (before after : ECx md)
    (self : after.self = before.self)
    (keys : ∀ address, Preserves (before.cx.keyAt address) (after.cx.keyAt address))
    (blobs : ∀ address bytes, before.cx.blob address = some bytes →
      after.cx.blob address = some bytes)
    (refs : ∀ (index : Nat) (address : Address), before.src.refs[index]? = some address →
      after.src.refs[index]? = some address)
    (levels : ∀ (index : Nat) (level : CLevel), before.univs[index]? = some level →
      after.univs[index]? = some level) : Extends before after := by
  constructor
  · intro index value success
    unfold ECx.level at *
    cases found : before.univs[index.toNat]? with
    | none => simp [found, malformed] at success
    | some level =>
      simpa [found, levels _ _ found] using success
  · intro index value success
    unfold ECx.keyAt at *
    cases found : before.src.refs[index.toNat]? with
    | none => simp [found, malformed] at success
    | some address =>
      have read : before.cx.keyAt address = .ok value := by simpa [found] using success
      simpa [refs _ _ found] using keys address value read
  · intro index value success
    unfold ECx.blobAt at *
    cases found : before.src.refs[index.toNat]? with
    | none => simp [found, malformed] at success
    | some address =>
      cases fetched : before.cx.blob address with
      | none => simp [found, fetched, malformed] at success
      | some bytes =>
        simpa [found, fetched, refs _ _ found, blobs _ _ fetched] using success
  · intro index member found
    simpa [self] using found

/-- The record an in-flight expression is read against: the block state's
primary tables, and no sharing table. `convExpr` reads no other field. -/
def tablesRecord (state : Ix.CompileM.BlockState) : Ixon.Constant :=
  { (default : Ixon.Constant) with refs := state.refs, univs := state.univs, sharing := #[] }

/-- The block's blobs overlaid on the context's. -/
def withBlockBlobs {md : Mode} (context : Ctx md) (state : Ix.CompileM.BlockState) : Ctx md :=
  { context with blob := fun address => (state.blockBlobs.get? address).orElse (fun _ => context.blob address) }

/-- **The reader of in-flight expressions**: the actual certified reader
(`MemberReader.mk'`) over the block state's primary tables, with the block's
blobs overlaid. Arena roots, name metadata and the expression cache never
enter it. -/
def blockReader {md : Mode} (context : Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (state : Ix.CompileM.BlockState) : MemberReader md :=
  MemberReader.mk' (withBlockBlobs context state) (tablesRecord state) param self

/-- The blob overlay does not change a key. -/
theorem withBlockBlobs_keyAt {md : Mode} (context : Ctx md) (state : Ix.CompileM.BlockState)
    (address : Address) : (withBlockBlobs context state).keyAt address = context.keyAt address := rfl

/-- The in-flight reader has no sharing entries. -/
theorem blockReader_tbl {md : Mode} (context : Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (state : Ix.CompileM.BlockState) :
    (blockReader context param self state).tbl = #[] := rfl

/-- The universe slot `index` of the in-flight reader is the reading of the
block's universe table entry. -/
theorem blockReader_level {md : Mode} (context : Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (state : Ix.CompileM.BlockState)
    {index : UInt64} {univ : Ixon.Univ} (found : state.univs[index.toNat]? = some univ) :
    (blockReader context param self state).ecx.level index = .ok (convUniv param univ) := by
  change (match (state.univs.map (convUniv param))[index.toNat]? with
    | some level => pure level
    | none => malformed "universe table index is out of bounds") = _
  rw [Array.getElem?_map, found]
  rfl

/-- **Growth of the block state's tables extends the in-flight reader**: if
the old reference and universe slots and every blob the overlay reads are
retained, every successful leaf lookup is. -/
theorem blockReader_growth {md : Mode} (context : Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (before after : Ix.CompileM.BlockState)
    (refs : ∀ (index : Nat) (address : Address), before.refs[index]? = some address →
      after.refs[index]? = some address)
    (univs : ∀ (index : Nat) (univ : Ixon.Univ), before.univs[index]? = some univ →
      after.univs[index]? = some univ)
    (blobs : ∀ address bytes, (withBlockBlobs context before).blob address = some bytes →
      (withBlockBlobs context after).blob address = some bytes) :
    Extends (blockReader context param self before).ecx (blockReader context param self after).ecx := by
  apply Extends.of_tables
  · rfl
  · intro address; exact .refl _
  · exact blobs
  · exact refs
  · intro index level found
    change (before.univs.map (convUniv param))[index]? = some level at found
    change (after.univs.map (convUniv param))[index]? = some level
    rw [Array.getElem?_map] at found ⊢
    cases prior : before.univs[index]? with
    | none => simp [prior] at found
    | some univ => simpa [prior, univs _ _ prior] using found

/-- `blockReader_growth` for a step that leaves the block's blobs alone. -/
theorem blockReader_growth_tables {md : Mode} (context : Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (before after : Ix.CompileM.BlockState)
    (refs : ∀ (index : Nat) (address : Address), before.refs[index]? = some address →
      after.refs[index]? = some address)
    (univs : ∀ (index : Nat) (univ : Ixon.Univ), before.univs[index]? = some univ →
      after.univs[index]? = some univ)
    (blobs : after.blockBlobs = before.blockBlobs) :
    Extends (blockReader context param self before).ecx (blockReader context param self after).ecx :=
  blockReader_growth context param self before after refs univs fun address bytes found => by
    change (after.blockBlobs.get? address).orElse (fun _ => context.blob address) = some bytes
    rw [blobs]
    exact found

/-- The compiler cache's semantic boundary: its value reads as a term related
to the source expression. The source relation is supplied by the caller;
this definition does not assume it holds. -/
def Reading {md : Mode} (source : Ix.Expr → CExpr md → Prop)
    (reader : Ix.CompileM.BlockState → MemberReader md) (state : Ix.CompileM.BlockState)
    (expr : Ix.Expr) (value : Ixon.Expr × UInt64) : Prop :=
  ∃ target, source expr target ∧ (reader state).read value.1 = .ok target

theorem blockReader_cache_blind {md : Mode} (context : Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (state : Ix.CompileM.BlockState) (cache) :
    blockReader context param self { state with exprCache := cache } =
      blockReader context param self state := rfl

theorem reading_cache_blind {md : Mode} (source : Ix.Expr → CExpr md → Prop)
    (context : Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (state : Ix.CompileM.BlockState) (cache) :
    Reading source (blockReader context param self) { state with exprCache := cache } =
      Reading source (blockReader context param self) state := rfl

theorem Reading.of_growth {md : Mode} {source : Ix.Expr → CExpr md → Prop}
    {reader : Ix.CompileM.BlockState → MemberReader md} {before after : Ix.CompileM.BlockState}
    (growth : Extends (reader before).ecx (reader after).ecx)
    (sharing : ∀ (index : Nat) (value : CExpr md), (reader before).tbl[index]? = some (.ok value) →
      (reader after).tbl[index]? = some (.ok value))
    {expr : Ix.Expr} {value : Ixon.Expr × UInt64} (prior : Reading source reader before expr value) :
    Reading source reader after expr value := by
  obtain ⟨target, related, read⟩ := prior
  exact ⟨target, related, convExpr_preserves growth sharing value.1 target read⟩

/-- **Transport every cached value** after the reader's lookups grow.
Insertion correctness remains the separate constructor-step obligation. -/
theorem cache_sound_of_growth {md : Mode} {source : Ix.Expr → CExpr md → Prop}
    {reader : Ix.CompileM.BlockState → MemberReader md} {before after : Ix.CompileM.BlockState}
    (growth : Extends (reader before).ecx (reader after).ecx)
    (sharing : ∀ (index : Nat) (value : CExpr md), (reader before).tbl[index]? = some (.ok value) →
      (reader after).tbl[index]? = some (.ok value))
    (cache : after.exprCache = before.exprCache)
    (prior : CacheSound (Reading source reader before) before.exprCache) :
    CacheSound (Reading source reader after) after.exprCache := by
  rw [cache]
  exact prior.mono fun _ _ related => related.of_growth growth sharing

/-- `cache_sound_of_growth` for the in-flight reader, whose sharing table is
empty. -/
theorem blockReader_cache_sound {md : Mode} {source : Ix.Expr → CExpr md → Prop}
    {context : Ctx md} {param : Nat → LevelParam} {self : Nat → Option (ReadM (CName md))}
    {before after : Ix.CompileM.BlockState}
    (growth : Extends (blockReader context param self before).ecx (blockReader context param self after).ecx)
    (cache : after.exprCache = before.exprCache)
    (prior : CacheSound (Reading source (blockReader context param self) before) before.exprCache) :
    CacheSound (Reading source (blockReader context param self) after) after.exprCache := by
  apply cache_sound_of_growth growth ?_ cache prior
  intro index value found
  rw [blockReader_tbl] at found
  simp at found

end Ix.CompileCert.ExpressionRead
