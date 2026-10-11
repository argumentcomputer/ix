import IxC.Kernel.Ixon.Reader
import Ix.CompileM
import Ix.CompileCert.ExpressionCache

/-! The certified reader's expression interpretation survives preserved table
lookups. This supplies the meaning-transport and memo-blindness side of the
compiler cache proof. Production writers must still establish table growth,
and constructor transitions must establish the source relation for new values.
These theorems concern unshared expressions before final record emission. -/

namespace Ix.CompileCert.ExpressionRead

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

/-- The actual leaves read by `convExpr`. This contract mentions no external
name metadata or arena state. The self/name maps are logical reader bindings. -/
structure Extends (before after : ECx) : Prop where
  level : ∀ index, Preserves (before.level index) (after.level index)
  ref : ∀ index, Preserves (before.refAt index) (after.refAt index)
  blob : ∀ index, Preserves (before.blobAt index) (after.blobAt index)
  self : ∀ index name, before.self index = some name → after.self index = some name
  name : ∀ ref, after.cx.nameOf ref = before.cx.nameOf ref

theorem Extends.levels {before after : ECx} (growth : Extends before after)
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

/-- Reading an arbitrary Ixon expression remains the same after its successful
leaf lookups and already-read sharing entries have been preserved. -/
theorem convExpr_preserves {before after : ECx} (growth : Extends before after)
    {table nextTable : Array (ReadM CExpr)}
    (sharing : ∀ (index : Nat) (value : CExpr), table[index]? = some (.ok value) →
      nextTable[index]? = some (.ok value)) (expr : Ixon.Expr) :
    Preserves (convExpr before table expr) (convExpr after nextTable expr) := by
  induction expr with
  | var index => exact .refl _
  | sort index => exact (growth.level index).bind fun _ => .refl _
  | ref index levels =>
    apply (growth.ref index).bind
    intro ref
    apply (growth.levels levels).bind
    intro levels
    rw [growth.name ref]
    exact .refl _
  | recur index levels =>
    unfold convExpr
    cases found : before.self index.toNat with
    | none => intro value success; cases success
    | some name =>
      rw [growth.self _ _ found]
      exact (growth.levels levels).bind fun _ => .refl _
  | prj index field value ih =>
    apply (growth.ref index).bind
    intro ref
    apply ih.bind
    intro value
    rw [growth.name ref]
    exact .refl _
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

/-- A concrete table-growth discharger: retain old reference/universe slots,
successful store resolution and blob reads, and logical name bindings. The
remaining fields of the containing constant do not affect expression reading. -/
theorem Extends.of_tables (before after : ECx)
    (self : after.self = before.self)
    (names : ∀ ref, after.cx.nameOf ref = before.cx.nameOf ref)
    (resolution : ∀ address ref, resolve before.cx.store address = some ref →
      resolve after.cx.store address = some ref)
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
    unfold ECx.refAt at *
    cases found : before.src.refs[index.toNat]? with
    | none => simp [found, malformed] at success
    | some address =>
      cases resolved : resolve before.cx.store address with
      | none => simp [found, resolved, malformed] at success
      | some ref =>
        simpa [found, resolved, refs _ _ found, resolution _ _ resolved] using success
  · intro index value success
    unfold ECx.blobAt at *
    cases found : before.src.refs[index.toNat]? with
    | none => simp [found, malformed] at success
    | some address =>
      cases fetched : before.cx.blob address with
      | none => simp [found, fetched, malformed] at success
      | some bytes =>
        simpa [found, fetched, refs _ _ found, blobs _ _ fetched] using success
  · intro index name found
    simpa [self] using found
  · exact names

/-- Read an in-flight, unshared compiler expression using the actual certified
reader. Metadata-mode source records use the virtual extension tables; ordinary
output expressions use only the primary tables. Arena roots and name metadata
never enter this interpretation. `base` supplies the containing record's other
fields, which `convExpr` does not inspect. -/
def blockReader (context : Ctx) (base : Ixon.Constant) (param : Nat → CName)
    (self : Nat → Option CName) (state : Ix.CompileM.BlockState) : MemberReader :=
  let refs := if state.p3MetaMode then state.refs ++ state.p3MetaRefs else state.refs
  let univs := if state.p3MetaMode then state.univs ++ state.metaUnivs else state.univs
  let context := { context with blob := fun address =>
    (state.blockBlobs.get? address).orElse (fun _ => context.blob address) }
  MemberReader.mk' context { base with refs, univs, sharing := #[] } param self

/-- The compiler cache's semantic boundary: its value reads as a term related
to the source expression. The source relation is supplied by the bridge; this
definition does not assume that relation holds or mention the metadata root. -/
def Reading (source : Ix.Expr → CExpr → Prop)
    (reader : Ix.CompileM.BlockState → MemberReader) (state : Ix.CompileM.BlockState)
    (expr : Ix.Expr) (value : Ixon.Expr × UInt64) : Prop :=
  ∃ target, source expr target ∧ (reader state).read value.1 = .ok target

theorem blockReader_cache_blind (context : Ctx) (base : Ixon.Constant)
    (param : Nat → CName) (self : Nat → Option CName)
    (state : Ix.CompileM.BlockState) (cache) :
    blockReader context base param self { state with exprCache := cache } =
      blockReader context base param self state := rfl

theorem reading_cache_blind (source : Ix.Expr → CExpr → Prop)
    (context : Ctx) (base : Ixon.Constant) (param : Nat → CName)
    (self : Nat → Option CName) (state : Ix.CompileM.BlockState) (cache) :
    Reading source (blockReader context base param self) { state with exprCache := cache } =
      Reading source (blockReader context base param self) state := rfl

theorem Reading.of_growth {source : Ix.Expr → CExpr → Prop}
    {reader : Ix.CompileM.BlockState → MemberReader} {before after : Ix.CompileM.BlockState}
    (growth : Extends (reader before).ecx (reader after).ecx)
    (sharing : ∀ (index : Nat) (value : CExpr), (reader before).tbl[index]? = some (.ok value) →
      (reader after).tbl[index]? = some (.ok value))
    {expr : Ix.Expr} {value : Ixon.Expr × UInt64} (prior : Reading source reader before expr value) :
    Reading source reader after expr value := by
  obtain ⟨target, related, read⟩ := prior
  exact ⟨target, related, convExpr_preserves growth sharing value.1 target read⟩

/-- Transport every cached value after the actual reader lookups grow. Cache
insertion correctness remains the separate constructor-transition obligation. -/
theorem cache_sound_of_growth {source : Ix.Expr → CExpr → Prop}
    {reader : Ix.CompileM.BlockState → MemberReader} {before after : Ix.CompileM.BlockState}
    (growth : Extends (reader before).ecx (reader after).ecx)
    (sharing : ∀ (index : Nat) (value : CExpr), (reader before).tbl[index]? = some (.ok value) →
      (reader after).tbl[index]? = some (.ok value))
    (cache : after.exprCache = before.exprCache)
    (prior : ExpressionCache.Sound (Reading source reader before) before.exprCache) :
    ExpressionCache.Sound (Reading source reader after) after.exprCache := by
  rw [cache]
  exact prior.mono fun _ _ related => related.of_growth growth sharing

end Ix.CompileCert.ExpressionRead
