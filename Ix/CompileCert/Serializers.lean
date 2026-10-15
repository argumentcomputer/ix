import Ix.CompileCert.BlobWrites

/-! # The metadata serializers' footprint

The compiler's metadata serializers (`storeBlob`, `storeString`,
`compileName`, `compileNames`, `serializeIxSubstring`,
`serializeIxSourceInfo`, `serializeIxSyntaxPreresolved`, `serializeIxSyntax`,
`compileDataValue`, `compileKVMap`) write only the block's names and blobs,
and every blob the block could read before one of them runs it reads after,
failing runs included (`NamesBlobs`). That one footprint fact gives every
frame property of the serializers by projection: the in-flight reader's
readings survive them (`NamesBlobs.reading`), and so do the expression
cache's meanings (`NamesBlobs.cache_sound`), when the reader's blobs are the
published prefix. -/

namespace Ix.CompileCert.Serializers

open Ix.CompileM Ix.CompileCert
open Ix.CompileCert.BlobWrites (withoutNamesBlobs)
open Ix.Kernel (Mode LevelParam)

/-- **The footprint**: the action changes only the block's names and blobs,
and keeps every blob the block reads, on every run. -/
def NamesBlobs (action : CompileM α) : Prop :=
  ∀ context before, withoutNamesBlobs (rawRun action context before).2 = withoutNamesBlobs before ∧
    BlobWrites.Extends context.1.blobs before (rawRun action context before).2

theorem NamesBlobs.pure (value : α) : NamesBlobs (pure value : CompileM α) :=
  fun _ _ => ⟨rfl, .refl _ _⟩

theorem NamesBlobs.throw (error : CompileError) : NamesBlobs (throw error : CompileM α) :=
  fun _ _ => ⟨rfl, .refl _ _⟩

theorem NamesBlobs.get : NamesBlobs getBlockState := fun _ _ => ⟨rfl, .refl _ _⟩

theorem NamesBlobs.read : NamesBlobs getCompileEnv := fun _ _ => ⟨rfl, .refl _ _⟩

theorem NamesBlobs.bind {action : CompileM α} {next : α → CompileM β}
    (first : NamesBlobs action) (later : ∀ value, NamesBlobs (next value)) :
    NamesBlobs (action >>= next) := by
  intro context before
  have head := first context before
  rw [rawRun_bind]
  cases ran : rawRun action context before with
  | mk outcome middle =>
    rw [ran] at head
    cases outcome with
    | error error => exact head
    | ok value =>
      have tail := later value context middle
      exact ⟨tail.1.trans head.1, BlobWrites.Extends.trans head.2 tail.2⟩

theorem NamesBlobs.map {action : CompileM α} (framed : NamesBlobs action) (f : α → β) :
    NamesBlobs (f <$> action) :=
  NamesBlobs.bind framed (fun _ => NamesBlobs.pure _)

theorem NamesBlobs.mapM_list (items : List α) (action : α → CompileM β)
    (each : ∀ item ∈ items, NamesBlobs (action item)) : NamesBlobs (items.mapM action) := by
  induction items with
  | nil => exact NamesBlobs.pure _
  | cons item rest ih =>
    rw [List.mapM_cons]
    refine NamesBlobs.bind (each item (by simp)) (fun _ => ?_)
    refine NamesBlobs.bind (ih (fun item member => each item (by simp [member]))) (fun _ => ?_)
    exact NamesBlobs.pure _

theorem NamesBlobs.mapM_array (items : Array α) (action : α → CompileM β)
    (each : ∀ item ∈ items, NamesBlobs (action item)) : NamesBlobs (items.mapM action) := by
  rw [Array.mapM_eq_mapM_toList]
  exact (NamesBlobs.mapM_list _ action (fun item member => each item (by simpa using member))).map _

theorem NamesBlobs.storeBlob (bytes : ByteArray) : NamesBlobs (storeBlob bytes) := by
  intro context before
  have preserved := BlobWrites.storeBlob_preserves bytes context before
  exact ⟨preserved.1, preserved.2.1⟩

theorem NamesBlobs.storeString (value : String) : NamesBlobs (storeString value) :=
  NamesBlobs.storeBlob _

theorem NamesBlobs.compileName (name : Ix.Name) : NamesBlobs (compileName name) :=
  fun context before => BlobWrites.compileName_preserves name context before

theorem NamesBlobs.compileNames (names : Array Ix.Name) : NamesBlobs (compileNames names) :=
  fun context before => BlobWrites.compileNames_preserves names context before

theorem NamesBlobs.serializeIxSubstring (value : Ix.Substring) :
    NamesBlobs (serializeIxSubstring value) :=
  NamesBlobs.bind (NamesBlobs.storeString _) (fun _ => NamesBlobs.pure _)

theorem NamesBlobs.serializeIxSourceInfo (value : Ix.SourceInfo) :
    NamesBlobs (serializeIxSourceInfo value) := by
  cases value <;> unfold Ix.CompileM.serializeIxSourceInfo
  · exact NamesBlobs.bind (NamesBlobs.serializeIxSubstring _) fun _ =>
      NamesBlobs.bind (NamesBlobs.serializeIxSubstring _) fun _ => NamesBlobs.pure _
  all_goals exact NamesBlobs.pure _

theorem NamesBlobs.serializeIxSyntaxPreresolved (value : Ix.SyntaxPreresolved) :
    NamesBlobs (serializeIxSyntaxPreresolved value) := by
  cases value <;> unfold Ix.CompileM.serializeIxSyntaxPreresolved
  · exact NamesBlobs.bind (NamesBlobs.compileName _) fun _ => NamesBlobs.pure _
  · exact NamesBlobs.bind (NamesBlobs.compileName _) fun _ =>
      NamesBlobs.bind (NamesBlobs.mapM_array _ _ (fun _ _ => NamesBlobs.storeString _)) fun _ =>
        NamesBlobs.pure _

theorem NamesBlobs.serializeIxSyntax (value : Ix.Syntax) : NamesBlobs (serializeIxSyntax value) := by
  induction value using Ix.CompileM.serializeIxSyntax.induct with
  | case1 => rw [Ix.CompileM.serializeIxSyntax]; exact NamesBlobs.pure _
  | case2 info kind args ih =>
    rw [Ix.CompileM.serializeIxSyntax]
    refine NamesBlobs.bind (NamesBlobs.compileName _) (fun _ => ?_)
    refine NamesBlobs.bind (NamesBlobs.serializeIxSourceInfo _) (fun _ => ?_)
    refine NamesBlobs.bind (NamesBlobs.mapM_array _ _ (fun arg _ => ih arg)) (fun _ => ?_)
    exact NamesBlobs.pure _
  | case3 info value =>
    rw [Ix.CompileM.serializeIxSyntax]
    exact NamesBlobs.bind (NamesBlobs.serializeIxSourceInfo _) fun _ =>
      NamesBlobs.bind (NamesBlobs.storeString _) fun _ => NamesBlobs.pure _
  | case4 info raw value resolved =>
    rw [Ix.CompileM.serializeIxSyntax]
    exact NamesBlobs.bind (NamesBlobs.compileName _) fun _ =>
      NamesBlobs.bind (NamesBlobs.serializeIxSourceInfo _) fun _ =>
        NamesBlobs.bind (NamesBlobs.serializeIxSubstring _) fun _ =>
          NamesBlobs.bind (NamesBlobs.mapM_array _ _ (fun _ _ => NamesBlobs.serializeIxSyntaxPreresolved _))
            fun _ => NamesBlobs.pure _

theorem NamesBlobs.compileDataValue (value : Ix.DataValue) : NamesBlobs (compileDataValue value) := by
  cases value <;> unfold Ix.CompileM.compileDataValue
  all_goals with_reducible repeat' first
    | exact NamesBlobs.pure _
    | exact NamesBlobs.compileName _
    | exact NamesBlobs.serializeIxSyntax _
    | exact NamesBlobs.storeBlob _
    | refine NamesBlobs.bind ?_ (fun _ => ?_)

theorem NamesBlobs.compileKVMap (values : Array (Ix.Name × Ix.DataValue)) :
    NamesBlobs (compileKVMap values) := by
  unfold Ix.CompileM.compileKVMap
  refine NamesBlobs.mapM_array _ _ (fun entry _ => ?_)
  rcases entry with ⟨key, value⟩
  exact NamesBlobs.bind (NamesBlobs.compileName _) fun _ =>
    NamesBlobs.bind (NamesBlobs.compileDataValue _) fun _ => NamesBlobs.pure _

/-- **The in-flight reader survives a serializer**, failing runs included,
when its blobs are the published prefix. -/
theorem NamesBlobs.reading {md : Mode} {action : CompileM α} (framed : NamesBlobs action)
    (context : CompileEnv × BlockEnv) (before : BlockState) (reader : Kernel.Reader.Ctx md)
    (param : Nat → LevelParam) (self : Nat → Option (Kernel.Reader.ReadM (Kernel.Reader.CName md)))
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address) :
    ExpressionRead.Extends (ExpressionRead.blockReader reader param self before).ecx
      (ExpressionRead.blockReader reader param self (rawRun action context before).2).ecx :=
  BlobWrites.reader_extends context.1.blobs before _ (framed context before).1 (framed context before).2
    reader param self aligned

/-- **The expression cache's meanings survive a serializer.** -/
theorem NamesBlobs.cache_sound {md : Mode} {action : CompileM α} (framed : NamesBlobs action)
    (context : CompileEnv × BlockEnv) (before : BlockState) (reader : Kernel.Reader.Ctx md)
    (param : Nat → LevelParam) (self : Nat → Option (Kernel.Reader.ReadM (Kernel.Reader.CName md)))
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (related : Ix.Expr → Kernel.Reader.CExpr md → Prop)
    (valid : CacheSound (ExpressionRead.Reading related (ExpressionRead.blockReader reader param self) before)
      before.exprCache) :
    let after := (rawRun action context before).2
    CacheSound (ExpressionRead.Reading related (ExpressionRead.blockReader reader param self) after)
      after.exprCache :=
  BlobWrites.cache_preserved context.1.blobs before _ (framed context before).1 (framed context before).2
    reader param self aligned related valid

/-- The serializers keep every projection that forgets names and blobs. -/
theorem NamesBlobs.preserves {action : CompileM α} (framed : NamesBlobs action)
    (projection : BlockState → β) (factors : ∀ state, projection state = projection (withoutNamesBlobs state)) :
    Preserves projection action := by
  intro context before
  rw [factors, (framed context before).1, ← factors]

end Ix.CompileCert.Serializers
