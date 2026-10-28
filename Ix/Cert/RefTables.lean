import Ix.Cert.BlockLayout
import Ix.Cert.GraphWalk
import Ix.CompileCert.EmissionWire

/-! # What a compiled block's reference table holds

Every entry of a block's reference table is the binding of a name the block's terms mention
(`GraphWalk.Refs`), or a stored blob (`Allowed`). The table grows only through `internRef`, which
the compiler calls on the binding of a name at a `const` or `proj` node it compiles, or on a blob
it has just stored; the preseed interns what its collector gathered from the same terms.

`Triple I P action Q` is a Hoare triple on successful runs with a frame invariant `I` of the
compile environment and block state; `Holds I action post` is the triple without a precondition.
The combinators (`bind`, `seq`, `mapM`, `forIn`, the context changes) hold for any invariant, so
other table facts can share them. `RefsOK M B` is the invariant here: the block's binding view is
`B`, and every entry is `Allowed` for the names `M` admits; a term is compiled under it when `M`
admits every name it mentions (`Covers`). -/

namespace Ix.Cert.RefTables

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState
open Ix.Cert.GraphWalk (Refs)

/-! ## Runs under an invariant -/

/-- **A successful run from a state with `I` and `P` ends in a state with `I`**, its value and
final state satisfying `Q`. -/
def Triple (I P : CompileEnv → BlockState → Prop) {α : Type} (action : CompileM α)
    (Q : CompileEnv → BlockState → α → Prop) : Prop :=
  ∀ context before value after, I context.1 before → P context.1 before →
    rawRun action context before = (.ok value, after) → I context.1 after ∧ Q context.1 after value

/-- **Every successful run from a state with `I` ends in one with `I`**, with `post`. -/
abbrev Holds (I : CompileEnv → BlockState → Prop) {α : Type} (action : CompileM α)
    (post : CompileEnv → BlockState → α → Prop := fun _ _ _ => True) : Prop :=
  Triple I (fun _ _ => True) action post

section Combinators

variable {I P : CompileEnv → BlockState → Prop} {α β : Type}

theorem Triple.returns {value : α} {Q : CompileEnv → BlockState → α → Prop}
    (h : ∀ env s, I env s → P env s → Q env s value) : Triple I P (pure value : CompileM α) Q := by
  intro context before v after hI hP ran
  cases ran
  exact ⟨hI, h _ _ hI hP⟩

theorem Holds.pure (value : α) : Holds I (Pure.pure value : CompileM α) :=
  Triple.returns fun _ _ _ _ => trivial

theorem Triple.throw (error : CompileError) {Q : CompileEnv → BlockState → α → Prop} :
    Triple I P (throw error : CompileM α) Q := by
  intro context before value after _ _ ran
  cases ran

theorem Triple.bind {action : CompileM α} {next : α → CompileM β} {Q : CompileEnv → BlockState → α → Prop}
    {R : CompileEnv → BlockState → β → Prop} (head : Triple I P action Q)
    (tail : ∀ value, Triple I (fun env s => Q env s value) (next value) R) : Triple I P (action >>= next) R := by
  intro context before output after hI hP ran
  obtain ⟨middle, state, firstRan, lastRan⟩ := bind_ok ran
  obtain ⟨hI', hQ⟩ := head context before middle state hI hP firstRan
  exact tail middle context state output after hI' hQ lastRan

theorem Triple.pre {action : CompileM α} {P' : CompileEnv → BlockState → Prop}
    {Q : CompileEnv → BlockState → α → Prop} (h : Triple I P action Q)
    (imp : ∀ env s, I env s → P' env s → P env s) : Triple I P' action Q :=
  fun c b v a hI hP ran => h c b v a hI (imp _ _ hI hP) ran

theorem Triple.post {action : CompileM α} {Q Q' : CompileEnv → BlockState → α → Prop}
    (h : Triple I P action Q) (imp : ∀ env s v, I env s → Q env s v → Q' env s v) : Triple I P action Q' :=
  fun c b v a hI hP ran => let r := h c b v a hI hP ran; ⟨r.1, imp _ _ _ r.1 r.2⟩

theorem Holds.seq {action : CompileM α} {next : α → CompileM β} {last : CompileEnv → BlockState → β → Prop}
    (head : Holds I action) (tail : ∀ value, Holds I (next value) last) : Holds I (action >>= next) last :=
  Triple.bind head fun value => Triple.pre (tail value) fun _ _ _ _ => trivial

theorem Triple.throwBind (error : CompileError) (next : α → CompileM β) {Q : CompileEnv → BlockState → β → Prop} :
    Triple I P (MonadExceptOf.throw error >>= next) Q := by
  intro context before value after _ _ ran
  obtain ⟨_, _, bad, _⟩ := bind_ok ran
  cases bad

theorem Holds.forget {action : CompileM α} {post : CompileEnv → BlockState → α → Prop}
    (h : Holds I action post) : Holds I action :=
  Triple.post h fun _ _ _ _ _ => trivial

theorem Holds.map {action : CompileM α} {post : CompileEnv → BlockState → α → Prop} (h : Holds I action post)
    (f : α → β) : Holds I (f <$> action) := by
  rw [map_eq_pure_bind]
  exact Holds.seq (Holds.forget h) (fun _ => Holds.pure _)

theorem Triple.withBlockEnv (update : BlockEnv → BlockEnv) {action : CompileM α}
    {Q : CompileEnv → BlockState → α → Prop} (h : Triple I P action Q) :
    Triple I P (withBlockEnv update action) Q := by
  intro context before value after hI hP ran
  rw [rawRun_withBlockEnv] at ran
  exact h (context.1, update context.2) before value after hI hP ran

theorem Triple.withCurrent (name : Ix.Name) {action : CompileM α} {Q : CompileEnv → BlockState → α → Prop}
    (h : Triple I P action Q) : Triple I P (withCurrent name action) Q := Triple.withBlockEnv _ h

theorem Triple.withMutCtx (mutCtx : MutCtx) {action : CompileM α} {Q : CompileEnv → BlockState → α → Prop}
    (h : Triple I P action Q) : Triple I P (withMutCtx mutCtx action) Q := Triple.withBlockEnv _ h

/-- An invariant read through a view the action keeps. -/
theorem Holds.preserves {σ : Type} {view : BlockState → σ} {action : CompileM α} (frame : Preserves view action)
    (factors : ∀ env s s', view s' = view s → I env s → I env s') : Holds I action := by
  intro context before value after hI _ ran
  have same := frame context before
  rw [ran] at same
  exact ⟨factors _ _ _ same hI, trivial⟩

theorem Holds.mapM_list (items : List α) (action : α → CompileM β)
    (each : ∀ item ∈ items, Holds I (action item)) : Holds I (items.mapM action) := by
  induction items with
  | nil => exact Holds.pure _
  | cons item rest ih =>
    rw [List.mapM_cons]
    exact Holds.seq (each item (by simp)) fun _ =>
      Holds.seq (ih (fun item member => each item (List.mem_cons_of_mem _ member))) fun _ => Holds.pure _

theorem Holds.mapM_array (items : Array α) (action : α → CompileM β)
    (each : ∀ item ∈ items, Holds I (action item)) : Holds I (items.mapM action) := by
  rw [Array.mapM_eq_mapM_toList]
  exact Holds.map (Holds.mapM_list _ action (fun item member => each item (by simpa using member))) _

theorem Holds.forIn_list (items : List α) (initial : β) (body : α → β → CompileM (ForInStep β))
    (each : ∀ item ∈ items, ∀ acc, Holds I (body item acc)) : Holds I (forIn items initial body) := by
  induction items generalizing initial with
  | nil => exact Holds.pure _
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply Holds.seq (each item (by simp) initial)
    intro step
    cases step with
    | done value => exact Holds.pure value
    | yield value => exact ih value (fun item member acc => each item (List.mem_cons_of_mem _ member) acc)

theorem Holds.forIn_array (items : Array α) (initial : β) (body : α → β → CompileM (ForInStep β))
    (each : ∀ item ∈ items, ∀ acc, Holds I (body item acc)) : Holds I (forIn items initial body) := by
  rw [← Array.forIn_toList]
  exact Holds.forIn_list _ initial body (fun item member acc => each item (by simpa using member) acc)

end Combinators

/-! ## The invariant -/

/-- **An entry the block may hold**: the binding at `B` of a name `M` admits, or a blob the
block or the environment stores. -/
def Allowed (M : CompileEnv → Ix.Name → Prop) (B : Bindings) (env : CompileEnv) (state : BlockState)
    (a : Address) : Prop :=
  (∃ m, M env m ∧ lookupBinding env B m = some a) ∨ (BlobWrites.readBlob env.blobs state a).isSome = true

/-- **The reference invariant**: the binding view is `B`, and every entry is `Allowed`. -/
def RefsOK (M : CompileEnv → Ix.Name → Prop) (B : Bindings) (env : CompileEnv) (state : BlockState) : Prop :=
  bindingView state = B ∧ ∀ a ∈ state.refs, Allowed M B env state a

/-- Every address of `refs` is `Allowed`. -/
def AllAllowed (M : CompileEnv → Ix.Name → Prop) (B : Bindings) (refs : Array Address) (env : CompileEnv)
    (state : BlockState) : Prop :=
  ∀ a ∈ refs, Allowed M B env state a

/-- `M` admits every name the term mentions, in every environment. -/
def Covers (M : CompileEnv → Ix.Name → Prop) (e : Ix.Expr) : Prop := ∀ env m, Refs m e → M env m

variable {M : CompileEnv → Ix.Name → Prop} {B : Bindings} {α : Type}

theorem name_beq_self (n : Ix.Name) : (n == n) = true := Address.beq_iff_eq.mpr rfl

theorem Allowed.mono {env : CompileEnv} {s s' : BlockState} {a : Address} (h : Allowed M B env s a)
    (ext : BlobWrites.Extends env.blobs s s') : Allowed M B env s' a := by
  rcases h with named | blob
  · exact .inl named
  · refine .inr ?_
    obtain ⟨bytes, hb⟩ := Option.isSome_iff_exists.mp blob
    rw [ext a bytes hb]
    rfl

theorem Extends.of_blobs {ambient : BlobWrites.Store} {s s' : BlockState} (h : s'.blockBlobs = s.blockBlobs) :
    BlobWrites.Extends ambient s s' := by
  intro a b hb
  unfold BlobWrites.readBlob at hb ⊢
  rw [h]
  exact hb

theorem AllAllowed.push {refs : Array Address} {env : CompileEnv} {s : BlockState} {a : Address}
    (h : AllAllowed M B refs env s) (ha : Allowed M B env s a) : AllAllowed M B (refs.push a) env s := by
  intro x hx
  rcases Array.mem_push.mp hx with old | rfl
  · exact h x old
  · exact ha

/-- An action that keeps the reference table and the binding view and only adds blobs, on every
run. -/
def Frame (action : CompileM α) : Prop :=
  ∀ context before, (rawRun action context before).2.refs = before.refs ∧
    bindingView (rawRun action context before).2 = bindingView before ∧
    BlobWrites.Extends context.1.blobs before (rawRun action context before).2

theorem Frame.pure (value : α) : Frame (Pure.pure value : CompileM α) :=
  fun _ _ => ⟨rfl, rfl, BlobWrites.Extends.refl _ _⟩

theorem Frame.throw (error : CompileError) : Frame (throw error : CompileM α) :=
  fun _ _ => ⟨rfl, rfl, BlobWrites.Extends.refl _ _⟩

theorem Frame.bind {β : Type} {action : CompileM α} {next : α → CompileM β} (head : Frame action)
    (tail : ∀ value, Frame (next value)) : Frame (action >>= next) := by
  intro context before
  obtain ⟨r₁, v₁, e₁⟩ := head context before
  rw [rawRun_bind]
  cases ran : rawRun action context before with
  | mk outcome mid =>
    rw [ran] at r₁ v₁ e₁
    cases outcome with
    | error e => exact ⟨r₁, v₁, e₁⟩
    | ok value =>
      obtain ⟨r₂, v₂, e₂⟩ := tail value context mid
      exact ⟨r₂.trans r₁, v₂.trans v₁, e₁.trans e₂⟩

theorem Frame.of_same {action : CompileM α}
    (same : ∀ context before, (rawRun action context before).2.refs = before.refs ∧
      (rawRun action context before).2.blockNameToAddr = before.blockNameToAddr ∧
      (rawRun action context before).2.blockBlobs = before.blockBlobs) : Frame action := by
  intro context before
  obtain ⟨h₁, h₂, h₄⟩ := same context before
  exact ⟨h₁, by simp only [bindingView, h₂], Extends.of_blobs h₄⟩

theorem Frame.namesBlobs {action : CompileM α} (framed : Serializers.NamesBlobs action) : Frame action := by
  intro context before
  obtain ⟨same, ext⟩ := framed context before
  have h₁ := congrArg BlockState.refs same
  have h₂ := congrArg BlockState.blockNameToAddr same
  exact ⟨h₁, by simp only [bindingView]; exact h₂, ext⟩

theorem Frame.preserves {σ : Type} {action : CompileM α} {projection : BlockState → σ}
    (frame : Preserves projection action)
    (factors : ∀ s s', projection s' = projection s → s'.refs = s.refs ∧ s'.blockNameToAddr = s.blockNameToAddr ∧
      s'.blockBlobs = s.blockBlobs) : Frame action :=
  Frame.of_same fun context before => factors _ _ (frame context before)

/-- The fields `Frame` reads. -/
def refView (s : BlockState) := (s.refs, s.blockNameToAddr, s.blockBlobs)

theorem Frame.view {action : CompileM α} (frame : Preserves refView action) : Frame action :=
  Frame.preserves frame fun _ _ same => by
    simp only [refView, Prod.mk.injEq] at same
    exact same

/-- A frame action carries `AllAllowed` of any addresses. -/
theorem Frame.triple {refs : Array Address} {action : CompileM α} (frame : Frame action) :
    Triple (RefsOK M B) (AllAllowed M B refs) action (fun env s _ => AllAllowed M B refs env s) := by
  intro context before value after hI hP ran
  obtain ⟨hrefs, hview, hext⟩ := frame context before
  rw [ran] at hrefs hview hext
  refine ⟨⟨hview.trans hI.1, fun a ha => ?_⟩, fun a ha => (hP a ha).mono hext⟩
  rw [hrefs] at ha
  exact (hI.2 a ha).mono hext

theorem Holds.framed {action : CompileM α} (frame : Frame action) : Holds (RefsOK M B) action :=
  Triple.post (Triple.pre (Frame.triple (refs := #[]) frame) fun _ _ _ _ a ha => by simp at ha)
    fun _ _ _ _ _ => trivial

/-! ## The leaves -/

theorem Holds.get : Holds (RefsOK M B) getBlockState := Holds.framed (Frame.view (Preserves.get _))
theorem Holds.readBlock : Holds (RefsOK M B) getBlockEnv := Holds.framed (Frame.view (Preserves.read _))
theorem Holds.readCompile : Holds (RefsOK M B) getCompileEnv :=
  Holds.framed (Frame.view (Preserves.readCompile _))

theorem Holds.modify (update : BlockState → BlockState) (same : ∀ s, refView (update s) = refView s) :
    Holds (RefsOK M B) (modifyBlockState update) := Holds.framed (Frame.view (Preserves.modify _ _ same))

theorem Holds.modifyGet {β : Type} (update : BlockState → β × BlockState)
    (same : ∀ s, refView (update s).2 = refView s) : Holds (RefsOK M B) (modifyGetBlockState update) :=
  Holds.framed (Frame.view (Preserves.modifyGet _ _ same))

theorem Frame.checkedIndex (table : String) (index : Nat) : Frame (checkedTableIndex table index) :=
  Frame.of_same fun context before => by
    rw [Interning.checkedTableIndex_state]; exact ⟨rfl, rfl, rfl⟩

theorem Frame.checkedCount (table : String) (count : Nat) : Frame (checkedTableCount table count) :=
  Frame.of_same fun context before => by
    rw [Interning.checkedTableCount_state]; exact ⟨rfl, rfl, rfl⟩

theorem Holds.checkedIndex (table : String) (index : Nat) : Holds (RefsOK M B) (checkedTableIndex table index) :=
  Holds.framed (Frame.checkedIndex table index)

theorem Holds.checkedCount (table : String) (count : Nat) : Holds (RefsOK M B) (checkedTableCount table count) :=
  Holds.framed (Frame.checkedCount table count)

theorem Holds.compileLevel (source : Ix.Level) : Holds (RefsOK M B) (compileAndInternUnivCanon source) :=
  Holds.framed (Frame.preserves (UniversePipeline.compileAndInternUnivCanon_frame source)
    (fun _ _ same => by
      have h₁ := congrArg BlockState.refs same
      have h₂ := congrArg BlockState.blockNameToAddr same
      have h₄ := congrArg BlockState.blockBlobs same
      exact ⟨h₁, h₂, h₄⟩))

theorem Holds.compileName (name : Ix.Name) : Holds (RefsOK M B) (compileName name) :=
  Holds.framed (Frame.namesBlobs (Serializers.NamesBlobs.compileName name))

theorem Holds.compileNames (names : Array Ix.Name) : Holds (RefsOK M B) (compileNames names) :=
  Holds.framed (Frame.namesBlobs (Serializers.NamesBlobs.compileNames names))

theorem Holds.kvmap (data : Array (Ix.Name × Ix.DataValue)) : Holds (RefsOK M B) (compileKVMap data) :=
  Holds.framed (Frame.namesBlobs (Serializers.NamesBlobs.compileKVMap data))

theorem Holds.alloc (node : Ixon.ExprMetaData) : Holds (RefsOK M B) (allocArenaNode node) := by
  unfold allocArenaNode; exact Holds.modifyGet _ (fun _ => rfl)

theorem Holds.patch (root : UInt64) (indices : Array UInt64) : Holds (RefsOK M B) (pushUnivPatch root indices) := by
  unfold pushUnivPatch; exact Holds.modify _ (fun _ => rfl)

theorem Triple.withUnivCtx (params : List Ix.Name) {P : CompileEnv → BlockState → Prop} {action : CompileM α}
    {Q : CompileEnv → BlockState → α → Prop} (keep : ∀ env s, P env s → P env { s with univCache := {} })
    (h : Triple (RefsOK M B) P action Q) : Triple (RefsOK M B) P (withUnivCtx params action) Q := by
  unfold Ix.CompileM.withUnivCtx
  refine Triple.bind (Q := fun env s _ => P env s) ?_ fun _ => Triple.withBlockEnv _ h
  intro context before value after hI hP ran
  rw [rawRun_modify] at ran
  cases ran
  exact ⟨⟨hI.1, fun a ha => (hI.2 a ha).mono (Extends.of_blobs rfl)⟩, keep _ _ hP⟩

theorem Holds.withUnivCtx (params : List Ix.Name) {action : CompileM α} {post : CompileEnv → BlockState → α → Prop}
    (h : Holds (RefsOK M B) action post) : Holds (RefsOK M B) (withUnivCtx params action) post :=
  Triple.withUnivCtx params (fun _ _ _ => trivial) h

/-- A name's lookup keeps the state, and returns its binding at the invariant's view. -/
theorem Triple.lookup (name : Ix.Name) {refs : Array Address} :
    Triple (RefsOK M B) (AllAllowed M B refs) (lookupConstAddr name)
      (fun env s a => AllAllowed M B refs env s ∧ lookupBinding env B name = some a) := by
  intro context before value after hI hP ran
  rw [ExpressionState.lookupConstAddr_run] at ran
  cases hb : lookupBinding context.1 (bindingView before) name with
  | none => rw [hb] at ran; cases ran
  | some a =>
    rw [hb] at ran
    cases ran
    exact ⟨hI, hP, by rw [← hI.1]; exact hb⟩

/-- Storing a blob carries `AllAllowed`, and the returned address reads as a blob. -/
theorem Triple.blob (bytes : ByteArray) {refs : Array Address} :
    Triple (RefsOK M B) (AllAllowed M B refs) (storeBlob bytes)
      (fun env s a => AllAllowed M B refs env s ∧ (BlobWrites.readBlob env.blobs s a).isSome = true) := by
  intro context before a after hI hP ran
  obtain ⟨_, _, stored⟩ := BlobWrites.storeBlob_preserves bytes context before
  rw [ran] at stored
  have h := (Frame.triple (M := M) (B := B) (refs := refs)
    (Frame.namesBlobs (Serializers.NamesBlobs.storeBlob bytes))) context before a after hI hP ran
  refine ⟨h.1, h.2, ?_⟩
  unfold BlobWrites.readBlob
  rw [stored a rfl]
  rfl

/-- What a successful `internRef` changes: at most one entry appended, the address. -/
theorem internRef_ok {address : Address} {context : CompileEnv × BlockEnv} {before after : BlockState}
    {index : UInt64} (ran : rawRun (internRef address) context before = (.ok index, after)) :
    (after.refs = before.refs ∨ after.refs = before.refs.push address) ∧
      after.blockBlobs = before.blockBlobs ∧ bindingView after = bindingView before := by
  have frame := ExpressionState.internRef_frame address context before
  rw [ran] at frame
  have h₂ := congrArg BlockState.blockBlobs frame
  have h₃ := congrArg BlockState.blockNameToAddr frame
  refine ⟨?_, h₂, by simp only [bindingView]; exact h₃⟩
  by_cases wide : address.hash.size = 32
  case neg =>
    obtain ⟨e, h⟩ := Interning.internRef_narrow address context before wide
    rw [h] at ran
    cases ran
  cases found : before.refsIndex.get? address with
  | some i =>
    rw [Interning.internRef_hit address context before wide found] at ran
    cases ran
    exact .inl rfl
  | none =>
    rw [Interning.internRef_miss address context before wide found] at ran
    split at ran
    · cases ran
      exact .inr rfl
    · have same := Interning.checkedTableCount_state "reference" (before.refs.size + 1) context before
      rw [ran] at same
      exact .inl (by rw [show after = before from same])

/-- **Interning an allowed entry keeps the invariant**, and carries any condition that reads the
state only through its blobs. -/
theorem Triple.internRefWith {address : Address} {C : CompileEnv → BlockState → Prop}
    (keep : ∀ env s s', s'.blockBlobs = s.blockBlobs → C env s → C env s') :
    Triple (RefsOK M B) (fun env s => C env s ∧ Allowed M B env s address) (internRef address)
      (fun env s _ => C env s) := by
  intro context before value after hI hP ran
  obtain ⟨hrefs, hblobs, hview⟩ := internRef_ok ran
  have ext : BlobWrites.Extends context.1.blobs before after := Extends.of_blobs hblobs
  refine ⟨⟨hview.trans hI.1, fun a ha => ?_⟩, keep _ _ _ hblobs hP.1⟩
  rcases hrefs with same | pushed
  · rw [same] at ha
    exact (hI.2 a ha).mono ext
  · rw [pushed] at ha
    rcases Array.mem_push.mp ha with old | rfl
    · exact (hI.2 a old).mono ext
    · exact hP.2.mono ext

/-- **Interning an allowed entry keeps the invariant**, and carries `AllAllowed`. -/
theorem Triple.internRef {address : Address} {refs : Array Address} :
    Triple (RefsOK M B) (fun env s => AllAllowed M B refs env s ∧ Allowed M B env s address) (internRef address)
      (fun env s _ => AllAllowed M B refs env s) := by
  intro context before value after hI hP ran
  obtain ⟨hrefs, hblobs, hview⟩ := internRef_ok ran
  have ext : BlobWrites.Extends context.1.blobs before after := Extends.of_blobs hblobs
  refine ⟨⟨hview.trans hI.1, fun a ha => ?_⟩, fun a ha => (hP.1 a ha).mono ext⟩
  rcases hrefs with same | pushed
  · rw [same] at ha
    exact (hI.2 a ha).mono ext
  · rw [pushed] at ha
    rcases Array.mem_push.mp ha with old | rfl
    · exact (hI.2 a old).mono ext
    · exact hP.2.mono ext

/-- **A name's binding, interned**, for a name `M` admits. -/
theorem Holds.lookupIntern {β : Type} (name : Ix.Name) (mentioned : ∀ env, M env name)
    (next : Address → UInt64 → CompileM β) {post : CompileEnv → BlockState → β → Prop}
    (rest : ∀ a i, Holds (RefsOK M B) (next a i) post) :
    Holds (RefsOK M B) (lookupConstAddr name >>= fun a => internRef a >>= fun i => next a i) post :=
  Triple.bind (Triple.pre (Triple.lookup (refs := #[]) name) fun _ _ _ _ a ha => by simp at ha) fun a =>
    Triple.bind (Triple.pre (Triple.internRef (refs := #[])) fun env _ _ h => ⟨h.1, .inl ⟨name, mentioned env, h.2⟩⟩)
      fun i => Triple.pre (rest a i) fun _ _ _ _ => trivial

/-- **A blob, stored then interned.** -/
theorem Holds.blobIntern {β : Type} (bytes : ByteArray) (next : Address → UInt64 → CompileM β)
    {post : CompileEnv → BlockState → β → Prop} (rest : ∀ a i, Holds (RefsOK M B) (next a i) post) :
    Holds (RefsOK M B) (storeBlob bytes >>= fun a => internRef a >>= fun i => next a i) post :=
  Triple.bind (Triple.pre (Triple.blob (refs := #[]) bytes) fun _ _ _ _ a ha => by simp at ha) fun a =>
    Triple.bind (Triple.pre (Triple.internRef (refs := #[])) fun _ _ _ h => ⟨h.1, .inr h.2⟩)
      fun i => Triple.pre (rest a i) fun _ _ _ _ => trivial

theorem Holds.finishReference (name : Ix.Name) (levels : Array (UInt64 × Option UInt64)) (value : Ixon.Expr) :
    Holds (RefsOK M B) (ExpressionState.finishReference name levels value) := by
  unfold ExpressionState.finishReference
  refine Holds.seq (Holds.alloc _) fun _ => ?_
  split
  · exact Holds.seq (Holds.patch _ _) fun _ => Holds.pure _
  · exact Holds.pure _

/-! ## The expression compiler -/

/-- The head and arguments of an application spine mention only what the spine mentions. -/
theorem decompose_covers : ∀ (expr : Ix.Expr) (args : Array Ix.Expr), Covers M expr → (∀ x ∈ args, Covers M x) →
    Covers M (Ix.CompileM.decomposeApps.go expr args).1 ∧ ∀ x ∈ (Ix.CompileM.decomposeApps.go expr args).2, Covers M x := by
  intro expr
  induction expr
  case app f a h ihf iha =>
    intro args c hargs
    refine ihf (args.push a) (fun env m r => c env m (.appF r)) (fun x hx => ?_)
    rcases Array.mem_push.mp hx with hx | rfl
    · exact hargs x hx
    · exact fun env m r => c env m (.appA r)
  all_goals
    intro args c hargs
    exact ⟨c, fun x hx => hargs x (Array.mem_reverse.mp hx)⟩

/-- **One step keeps the invariant** on success, given the same of the recursive compile on
every strict subterm the invariant covers. -/
theorem Holds.step (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (source : Ix.Expr) (cov : Covers M source)
    (each : ∀ child, sizeOf child < sizeOf source → Covers M child → Holds (RefsOK M B) (compile child)) :
    Holds (RefsOK M B) (ExpressionState.step compile source) := by
  cases source with
  | bvar index hash =>
    rw [ExpressionState.bvar_step_eq]
    exact Holds.seq (Holds.checkedIndex _ _) fun _ => Holds.seq (Holds.alloc _) fun _ => Holds.pure _
  | sort level hash =>
    rw [ExpressionState.sort_step_eq]
    refine Holds.seq (Holds.compileLevel _) fun result => ?_
    obtain ⟨index, patch⟩ := result
    dsimp only
    unfold ExpressionState.finishSort
    refine Holds.seq (Holds.alloc _) fun _ => ?_
    split
    · exact Holds.seq (Holds.patch _ _) fun _ => Holds.pure _
    · exact Holds.pure _
  | const name levels hash =>
    rw [ExpressionState.const_step_eq, ExpressionState.compileConstExprRaw_eq]
    refine Holds.seq Holds.readBlock fun block => ?_
    dsimp only
    refine Holds.seq (Holds.mapM_array _ _ fun _ _ => Holds.compileLevel _) fun compiled =>
      Holds.seq (Holds.compileName _) fun _ => ?_
    unfold ExpressionState.constBody
    split
    · exact Holds.seq (Holds.checkedIndex _ _) fun _ => Holds.finishReference _ _ _
    · exact Holds.lookupIntern name (fun env => cov env name (.const (name_beq_self name))) _
        fun _ _ => Holds.finishReference _ _ _
  | app fn arg hash =>
    rw [ExpressionState.app_step_eq]
    have parts := decompose_covers (.app fn arg hash) #[] cov (fun x hx => by simp at hx)
    refine Holds.seq (each _ (Ix.CompileM.decomposeApps_app_head_lt fn arg hash) parts.1) (fun head => ?_)
    rw [forIn'_eq_forIn _ _ _ (fun x acc => ExpressionState.appBody compile acc x) (fun _ _ _ => rfl)]
    refine Holds.seq (Holds.forIn_array _ _ _ (fun x member acc => ?_)) (fun _ => Holds.pure _)
    unfold ExpressionState.appBody
    exact Holds.seq (each x (Ix.CompileM.decomposeApps_app_mem_lt fn arg hash member) (parts.2 x member)) fun _ =>
      Holds.seq (Holds.alloc _) fun _ => Holds.pure _
  | lam name type body info hash =>
    rw [show ExpressionState.step compile (.lam name type body info hash) = _ from
      ExpressionState.binder_step_eq false compile name type body info hash]
    unfold ExpressionState.finishBinder
    exact Holds.seq (Holds.compileName _) fun _ =>
      Holds.seq (each type (by simp; omega) fun env m r => cov env m (.lamT r)) fun _ =>
      Holds.seq (each body (by simp; omega) fun env m r => cov env m (.lamB r)) fun _ =>
      Holds.seq (Holds.alloc _) fun _ => Holds.pure _
  | forallE name type body info hash =>
    rw [show ExpressionState.step compile (.forallE name type body info hash) = _ from
      ExpressionState.binder_step_eq true compile name type body info hash]
    unfold ExpressionState.finishBinder
    exact Holds.seq (Holds.compileName _) fun _ =>
      Holds.seq (each type (by simp; omega) fun env m r => cov env m (.allT r)) fun _ =>
      Holds.seq (each body (by simp; omega) fun env m r => cov env m (.allB r)) fun _ =>
      Holds.seq (Holds.alloc _) fun _ => Holds.pure _
  | letE name type value body nonDep hash =>
    rw [ExpressionState.let_step_eq]
    unfold ExpressionState.finishLet
    exact Holds.seq (Holds.compileName _) fun _ =>
      Holds.seq (each type (by simp; omega) fun env m r => cov env m (.letT r)) fun _ =>
      Holds.seq (each value (by simp; omega) fun env m r => cov env m (.letV r)) fun _ =>
      Holds.seq (each body (by simp; omega) fun env m r => cov env m (.letB r)) fun _ =>
      Holds.seq (Holds.alloc _) fun _ => Holds.pure _
  | lit literal hash =>
    cases literal
    · rw [ExpressionState.nat_step_eq]
      unfold ExpressionState.compileLiteral ExpressionState.finishLiteral
      exact Holds.blobIntern _ _ fun _ _ => Holds.seq (Holds.alloc _) fun _ => Holds.pure _
    · rw [ExpressionState.string_step_eq]
      unfold ExpressionState.compileLiteral ExpressionState.finishLiteral
      exact Holds.blobIntern _ _ fun _ _ => Holds.seq (Holds.alloc _) fun _ => Holds.pure _
  | proj name field value hash =>
    rw [ExpressionState.projection_step_eq]
    unfold ExpressionState.finishProjection
    exact Holds.seq (Holds.checkedIndex _ _) fun _ => Holds.seq (Holds.compileName _) fun _ =>
      Holds.lookupIntern name (fun env => cov env name (.projName (name_beq_self name))) _ fun _ _ =>
        Holds.seq (each value (by simp; omega) fun env m r => cov env m (.projStruct r)) fun _ =>
          Holds.seq (Holds.alloc _) fun _ => Holds.pure _
  | mdata data value hash =>
    unfold ExpressionState.step compileExprStep
    dsimp only
    have child := each value (by simp; omega) fun env m r => cov env m (.mdata r)
    split
    · split
      · refine Holds.seq (Holds.pure _) fun _ => Holds.seq child fun _ => ?_
        split
        · exact Holds.pure _
        · exact Triple.throwBind _ _
      · exact Triple.throwBind _ _
    · exact Holds.seq (Holds.kvmap _) fun _ => Holds.seq child fun _ => Holds.seq (Holds.alloc _) fun _ =>
        Holds.pure _
  | fvar name hash =>
    unfold ExpressionState.step compileExprStep
    exact Triple.throw _
  | mvar name hash =>
    unfold ExpressionState.step compileExprStep
    exact Triple.throw _

/-- **The expression compiler keeps the invariant** on success, for a term it covers. -/
theorem Holds.expression (source : Ix.Expr) (cov : Covers M source) :
    Holds (RefsOK M B) (compileExpr source) := by
  induction source using (measure (fun e : Ix.Expr => sizeOf e)).wf.induction with
  | h source ih =>
    rw [compileExpr]
    refine Holds.seq Holds.get (fun state => ?_)
    split
    · exact Holds.pure _
    · rw [show (compileExprStep source fun x _h => compileExpr x) =
        ExpressionState.step compileExpr source from rfl]
      refine Holds.seq (Holds.step compileExpr source cov (fun child smaller c => ih child smaller c))
        (fun value => ?_)
      exact Holds.seq (Holds.modify _ (fun _ => rfl)) (fun _ => Holds.pure _)

/-! ## The drains and the payloads -/

theorem Holds.takeArena : Holds (RefsOK M B) takeArena := by
  unfold Ix.CompileM.takeArena; exact Holds.modifyGet _ (fun _ => rfl)

theorem Holds.takeUnivPatches : Holds (RefsOK M B) takeUnivPatches := by
  unfold Ix.CompileM.takeUnivPatches; exact Holds.modifyGet _ (fun _ => rfl)

theorem Holds.clearExprCache : Holds (RefsOK M B) clearExprCache := by
  unfold Ix.CompileM.clearExprCache; exact Holds.modify _ (fun _ => rfl)

theorem Holds.resetArena : Holds (RefsOK M B) resetArena := by
  unfold Ix.CompileM.resetArena; exact Holds.modify _ (fun _ => rfl)

theorem Holds.recordDefHints (name : Ix.Name) (hints : Lean.ReducibilityHints) :
    Holds (RefsOK M B) (recordDefHints name hints) := by
  unfold Ix.CompileM.recordDefHints; exact Holds.modify _ (fun _ => rfl)

theorem Holds.mutCtxAddrs : Holds (RefsOK M B) getMutCtxAddrs := by
  unfold getMutCtxAddrs
  exact Holds.seq Holds.readBlock (fun _ => Holds.pure _)

/-- The finishers' metadata steps. -/
local macro "holds_finish" : tactic => `(tactic|
  with_reducible repeat' first
    | exact Holds.pure _
    | exact Holds.takeArena
    | exact Holds.takeUnivPatches
    | exact Holds.clearExprCache
    | exact Holds.checkedCount _ _
    | exact Holds.checkedIndex _ _
    | exact Holds.compileName _
    | exact Holds.compileNames _
    | exact Holds.recordDefHints _ _
    | exact Holds.mutCtxAddrs
    | exact Holds.readBlock
    | refine Holds.seq ?_ (fun _ => ?_)
    | dsimp only)

theorem Holds.finishDefinitionData (source : Ix.Def) (type : Ixon.Expr) (typeRoot : UInt64)
    (value : Ixon.Expr) (valueRoot : UInt64) :
    Holds (RefsOK M B) (finishDefinitionDataCompilation source type typeRoot value valueRoot) := by
  unfold finishDefinitionDataCompilation
  holds_finish

theorem Holds.definitionData (source : Ix.Def) (ct : Covers M source.type) (cv : Covers M source.value) :
    Holds (RefsOK M B) (compileDefinitionData source) := by
  unfold compileDefinitionData
  refine Triple.withCurrent _ (Holds.withUnivCtx _ ?_)
  exact Holds.seq Holds.resetArena fun _ => Holds.seq (Holds.expression _ ct) fun type =>
    Holds.seq (Holds.expression _ cv) fun value =>
      Holds.finishDefinitionData source type.1 type.2 value.1 value.2

theorem Holds.finishAxiom (source : AxiomVal) (type : Ixon.Expr) (root : UInt64) :
    Holds (RefsOK M B) (finishAxiomCompilation source type root) := by
  unfold finishAxiomCompilation
  holds_finish

theorem Holds.axiomPayload (source : AxiomVal) (ct : Covers M source.cnst.type) :
    Holds (RefsOK M B) (compileAxiom source) := by
  unfold compileAxiom
  refine Triple.withCurrent _ (Holds.withUnivCtx _ ?_)
  exact Holds.seq Holds.resetArena fun _ => Holds.seq (Holds.expression _ ct) fun type =>
    Holds.finishAxiom source type.1 type.2

theorem Holds.finishQuotient (source : QuotVal) (type : Ixon.Expr) (root : UInt64) :
    Holds (RefsOK M B) (finishQuotientCompilation source type root) := by
  unfold finishQuotientCompilation
  holds_finish

theorem Holds.quotientPayload (source : QuotVal) (ct : Covers M source.cnst.type) :
    Holds (RefsOK M B) (compileQuotient source) := by
  unfold compileQuotient
  refine Triple.withCurrent _ (Holds.withUnivCtx _ ?_)
  exact Holds.seq Holds.resetArena fun _ => Holds.seq (Holds.expression _ ct) fun type =>
    Holds.finishQuotient source type.1 type.2

theorem Holds.rules (sources : List RecursorRule) (initial : RecursorRuleCompileState)
    (covers : ∀ rule ∈ sources, Covers M rule.rhs) : Holds (RefsOK M B) (compileRecursorRules sources initial) := by
  induction sources generalizing initial with
  | nil => exact Holds.pure _
  | cons source rest ih =>
    rw [compileRecursorRules]
    refine Holds.seq ?_ (fun _ => ih _ (fun rule member => covers rule (List.mem_cons_of_mem _ member)))
    unfold compileRecursorRule
    exact Holds.seq (Holds.expression _ (covers source (by simp))) fun _ =>
      Holds.seq (Holds.checkedCount _ _) fun _ => Holds.pure _

theorem Holds.finishRecursor (source : RecursorVal) (type : Ixon.Expr) (root : UInt64)
    (rules : RecursorRuleCompileState) : Holds (RefsOK M B) (finishRecursorCompilation source type root rules) := by
  unfold finishRecursorCompilation
  holds_finish

theorem Holds.recursorPayload (source : RecursorVal) (ct : Covers M source.cnst.type)
    (cr : ∀ rule ∈ source.rules.toList, Covers M rule.rhs) : Holds (RefsOK M B) (compileRecursor source) := by
  unfold compileRecursor
  refine Triple.withCurrent _ (Holds.withUnivCtx _ ?_)
  exact Holds.seq Holds.resetArena fun _ => Holds.seq (Holds.expression _ ct) fun type =>
    Holds.seq (Holds.rules _ _ cr) fun rules => Holds.finishRecursor source type.1 type.2 rules

theorem Holds.finishConstructor (source : ConstructorVal) (type : Ixon.Expr) (root : UInt64) :
    Holds (RefsOK M B) (finishConstructorCompilation source type root) := by
  unfold finishConstructorCompilation
  holds_finish

theorem Holds.constructors (sources : List ConstructorVal) (initial : InductiveConstructorCompileState)
    (covers : ∀ c ∈ sources, Covers M c.cnst.type) :
    Holds (RefsOK M B) (compileInductiveConstructors sources initial) := by
  induction sources generalizing initial with
  | nil => exact Holds.pure _
  | cons source rest ih =>
    rw [compileInductiveConstructors]
    refine Holds.seq ?_ (fun _ => ih _ (fun c member => covers c (List.mem_cons_of_mem _ member)))
    unfold compileConstructor
    refine Triple.withCurrent _ ?_
    exact Holds.seq Holds.resetArena fun _ => Holds.seq (Holds.expression _ (covers source (by simp))) fun type =>
      Holds.finishConstructor source type.1 type.2

theorem Holds.inductiveMetadata : Holds (RefsOK M B) takeInductiveTypeCompileMeta := by
  unfold takeInductiveTypeCompileMeta
  holds_finish

theorem Holds.finishInductive (source : InductiveVal) (type : Ixon.Expr) (root : UInt64)
    (metadata : InductiveTypeCompileMeta) (constructors : InductiveConstructorCompileState) :
    Holds (RefsOK M B) (finishInductiveCompilation source type root metadata constructors) := by
  unfold finishInductiveCompilation
  holds_finish

theorem Holds.inductivePayload (source : InductiveVal) (constructors : Array ConstructorVal)
    (ct : Covers M source.cnst.type) (cc : ∀ c ∈ constructors.toList, Covers M c.cnst.type) :
    Holds (RefsOK M B) (compileInductive source constructors) := by
  unfold compileInductive
  refine Triple.withCurrent _ (Holds.withUnivCtx _ ?_)
  exact Holds.seq Holds.resetArena fun _ => Holds.seq (Holds.expression _ ct) fun type =>
    Holds.seq Holds.inductiveMetadata fun metadata => Holds.seq (Holds.constructors _ _ cc) fun built =>
      Holds.finishInductive source type.1 type.2 metadata built

theorem Holds.finishInductiveData (source : Ix.Ind) (type : Ixon.Expr) (root : UInt64)
    (metadata : InductiveTypeCompileMeta) (constructors : InductiveConstructorCompileState) :
    Holds (RefsOK M B) (finishInductiveDataCompilation source type root metadata constructors) := by
  unfold finishInductiveDataCompilation
  holds_finish

theorem Holds.inductiveData (source : Ix.Ind) (ct : Covers M source.type)
    (cc : ∀ c ∈ source.ctors.toList, Covers M c.cnst.type) : Holds (RefsOK M B) (compileInductiveData source) := by
  unfold compileInductiveData
  refine Triple.withCurrent _ (Holds.withUnivCtx _ ?_)
  exact Holds.seq Holds.resetArena fun _ => Holds.seq (Holds.expression _ ct) fun type =>
    Holds.seq Holds.inductiveMetadata fun metadata => Holds.seq (Holds.constructors _ _ cc) fun built =>
      Holds.finishInductiveData source type.1 type.2 metadata built

/-- `M` admits every name a mutual member's terms mention. -/
def MutCovers (M : CompileEnv → Ix.Name → Prop) : MutConst → Prop
  | .defn d => Covers M d.type ∧ Covers M d.value
  | .indc i => Covers M i.type ∧ ∀ c ∈ i.ctors.toList, Covers M c.cnst.type
  | .recr r => Covers M r.cnst.type ∧ ∀ rule ∈ r.rules.toList, Covers M rule.rhs

theorem Holds.member (source : MutConst) (cov : MutCovers M source) :
    Holds (RefsOK M B) (compileMutConstMember source) := by
  cases source <;> unfold compileMutConstMember
  · exact Holds.seq (Triple.withCurrent _ (Holds.definitionData _ cov.1 cov.2)) fun _ => Holds.pure _
  · exact Holds.seq (Triple.withCurrent _ (Holds.inductiveData _ cov.1 cov.2)) fun _ => Holds.pure _
  · exact Holds.seq (Triple.withCurrent _ (Holds.recursorPayload _ cov.1 cov.2)) fun _ => Holds.pure _

theorem Holds.members (sources : List MutConst) (initial : MutConstCompileState)
    (cov : ∀ c ∈ sources, MutCovers M c) :
    Holds (RefsOK M B) (compileMutConstMembers sources initial) := by
  induction sources generalizing initial with
  | nil => exact Holds.pure _
  | cons source rest ih =>
    rw [compileMutConstMembers]
    exact Holds.seq (Holds.member source (cov source (by simp)))
      (fun _ => ih _ (fun c member => cov c (List.mem_cons_of_mem _ member)))

theorem Holds.mutConsts (sources : List MutConst) (cov : ∀ c ∈ sources, MutCovers M c) :
    Holds (RefsOK M B) (compileMutConsts sources) := by
  unfold compileMutConsts
  exact Holds.seq (Holds.members sources {} cov) (fun _ => Holds.pure _)

/-! ## The block finishers: the block's table is the state's -/

theorem build_refs {limits : Ix.Sharing.Exact.Limits} {info : Ixon.ConstantInfo} {refs : Array Address}
    {univs : Array Ixon.Univ} {c : Ixon.Constant} (h : buildConstantWithSharing limits info refs univs = .ok c) :
    c.refs = refs :=
  (SharingRoots.build_roots (md := .anon) limits info refs univs c h).2.1

theorem buildBlockConstant_preserves (info : Ixon.ConstantInfo) (refs : Array Address) (univs : Array Ixon.Univ) :
    Preserves id (buildBlockConstant info refs univs) := by
  unfold buildBlockConstant
  refine Preserves.bind (fun _ _ => rfl) fun context => ?_
  unfold liftSharing
  split
  · exact Preserves.pure _ _
  · exact Preserves.throw _ _

theorem Holds.finishConstant (info : Ixon.ConstantInfo) (blockMeta : Ixon.ConstantMeta) :
    Holds (RefsOK M B) (finishConstantInfoWithSharing info blockMeta) (fun _ s r => r.block.refs = s.refs) := by
  intro context before value after hI _ ran
  unfold finishConstantInfoWithSharing finishConstantWithSharing at ran
  obtain ⟨cache, mid, hc, ran⟩ := bind_ok ran
  have hc : (Except.ok before, before) = (Except.ok cache, mid) := hc
  cases hc
  obtain ⟨block, mid', hb, done⟩ := bind_ok ran
  have same : mid' = before := by
    have := buildBlockConstant_preserves info before.refs before.univs context before
    rw [hb] at this
    exact this
  subst same
  rw [rawRun_pure] at done
  cases done
  exact ⟨hI, build_refs (BlockLayout.buildBlockConstant_ok hb)⟩

theorem Holds.finishInductiveFamily (source : InductiveVal) (ind : Ixon.Inductive) (indMeta : Ixon.ConstantMeta)
    (pairs : Array (Ix.Name × Ixon.ConstantMeta)) :
    Holds (RefsOK M B) (finishInductiveFamilyBlock source ind indMeta pairs) (fun _ s r => r.block.refs = s.refs) := by
  unfold finishInductiveFamilyBlock
  refine Holds.seq (Holds.checkedCount _ _) fun _ => Holds.seq (Holds.checkedCount _ _) fun _ => ?_
  intro context before value after hI _ ran
  obtain ⟨cache, mid, hc, ran⟩ := bind_ok ran
  have hc : (Except.ok before, before) = (Except.ok cache, mid) := hc
  cases hc
  obtain ⟨block, mid', hb, done⟩ := bind_ok ran
  have same : mid' = before := by
    have := buildBlockConstant_preserves (.muts #[.indc ind]) before.refs before.univs context before
    rw [hb] at this
    exact this
  subst same
  rw [rawRun_pure] at done
  cases done
  exact ⟨hI, build_refs (BlockLayout.buildBlockConstant_ok hb)⟩

theorem mutual_refs {limits : Ix.Sharing.Exact.Limits} {classes : List MutConst}
    {payloads : Array Ixon.MutConst} {metas : Array (Ix.Name × Ixon.ConstantMeta)} {cache : BlockState}
    {out : BlockResult} (ran : buildCompiledMutualBlock limits classes payloads metas cache = .ok out) :
    out.block.refs = cache.refs := by
  unfold buildCompiledMutualBlock at ran
  cases hs : standaloneMutConstInfo? payloads with
  | some info =>
    rw [hs] at ran
    obtain ⟨block, hb, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases Except.ok.inj returned
    exact build_refs hb
  | none =>
    rw [hs] at ran
    obtain ⟨block, hb, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases Except.ok.inj returned
    exact build_refs hb

theorem Holds.finishMutual (classes : List MutConst) (payloads : Array Ixon.MutConst)
    (metas : Array (Ix.Name × Ixon.ConstantMeta)) :
    Holds (RefsOK M B) (finishMutualCompilation classes payloads metas) (fun _ s r => r.block.refs = s.refs) := by
  intro context before value after hI _ ran
  obtain ⟨same, _, built⟩ := ProjectionLayout.finish_mutual_ok context classes payloads metas ran
  subst same
  exact ⟨hI, mutual_refs built⟩

theorem Holds.mutualPayload (classes : List MutConst) (cov : ∀ c ∈ classes, MutCovers M c) :
    Holds (RefsOK M B) (compileMutualPayload classes) (fun _ s r => r.block.refs = s.refs) := by
  unfold compileMutualPayload
  refine Holds.seq (Holds.mutConsts classes cov) fun compiled => ?_
  obtain ⟨payloads, roots, metas⟩ := compiled
  exact Holds.finishMutual classes payloads metas

/-! ## The preseed -/

theorem Frame.compileUniv (source : Ix.Level) : Frame (compileUniv source) :=
  Frame.preserves (CanonUnivCache.compileUniv_frame source) fun _ _ same => by
    have h₁ := congrArg BlockState.refs same
    have h₂ := congrArg BlockState.blockNameToAddr same
    have h₄ := congrArg BlockState.blockBlobs same
    exact ⟨h₁, h₂, h₄⟩

theorem Frame.univs (levels : List Ix.Level) (initial : Array Ixon.Univ) :
    Frame (collectExprTableUnivs levels initial) := by
  induction levels generalizing initial with
  | nil => exact Frame.pure _
  | cons level rest ih =>
    rw [collectExprTableUnivs]
    exact Frame.bind (Frame.compileUniv level) (fun value => ih (initial.push value))

/-- **The collector gathers allowed addresses**: a reference it collects is the binding of a
name the term mentions, or a blob it stored. -/
theorem Triple.collect (ctxKey : Address) (mutCtx : MutCtx) (params : List Ix.Name) :
    ∀ (e : Ix.Expr) (acc : ExprTableCollection), Covers M e →
      Triple (RefsOK M B) (AllAllowed M B acc.1) (collectExprTablesStructural ctxKey mutCtx params e acc)
        (fun env s out => AllAllowed M B out.1 env s) := by
  intro e
  induction e with
  | bvar index hash =>
    rintro ⟨refs, univs, seen⟩ _
    rw [collectExprTablesStructural]
    split
    · exact Triple.returns fun _ _ _ h => h
    · exact Triple.returns fun _ _ _ h => h
  | fvar name hash =>
    rintro ⟨refs, univs, seen⟩ _
    rw [collectExprTablesStructural]
    split
    · exact Triple.returns fun _ _ _ h => h
    · exact Triple.throw _
  | mvar name hash =>
    rintro ⟨refs, univs, seen⟩ _
    rw [collectExprTablesStructural]
    split
    · exact Triple.returns fun _ _ _ h => h
    · exact Triple.throw _
  | sort level hash =>
    rintro ⟨refs, univs, seen⟩ _
    rw [collectExprTablesStructural]
    split
    · exact Triple.returns fun _ _ _ h => h
    · exact Triple.bind (Frame.triple (Frame.compileUniv level)) fun _ => Triple.returns fun _ _ _ h => h
  | const name levels hash =>
    rintro ⟨refs, univs, seen⟩ cov
    rw [collectExprTablesStructural]
    split
    · exact Triple.returns fun _ _ _ h => h
    · refine Triple.bind (Frame.triple (Frame.univs levels.toList univs)) fun _ => ?_
      split
      · exact Triple.bind (Triple.lookup name) fun a => Triple.returns fun env _ _ h =>
          h.1.push (.inl ⟨name, cov env name (.const (name_beq_self name)), h.2⟩)
      · exact Triple.returns fun _ _ _ h => h
  | app fn arg hash ihf iha =>
    rintro ⟨refs, univs, seen⟩ cov
    rw [collectExprTablesStructural]
    split
    · exact Triple.returns fun _ _ _ h => h
    · exact Triple.bind (Triple.pre (ihf _ fun env m r => cov env m (.appF r)) fun _ _ _ h => h) fun acc =>
        iha acc fun env m r => cov env m (.appA r)
  | lam name type body info hash iht ihb =>
    rintro ⟨refs, univs, seen⟩ cov
    rw [collectExprTablesStructural]
    split
    · exact Triple.returns fun _ _ _ h => h
    · exact Triple.bind (Triple.pre (iht _ fun env m r => cov env m (.lamT r)) fun _ _ _ h => h) fun acc =>
        ihb acc fun env m r => cov env m (.lamB r)
  | forallE name type body info hash iht ihb =>
    rintro ⟨refs, univs, seen⟩ cov
    rw [collectExprTablesStructural]
    split
    · exact Triple.returns fun _ _ _ h => h
    · exact Triple.bind (Triple.pre (iht _ fun env m r => cov env m (.allT r)) fun _ _ _ h => h) fun acc =>
        ihb acc fun env m r => cov env m (.allB r)
  | letE name type value body nonDep hash iht ihv ihb =>
    rintro ⟨refs, univs, seen⟩ cov
    rw [collectExprTablesStructural]
    split
    · exact Triple.returns fun _ _ _ h => h
    · exact Triple.bind (Triple.pre (iht _ fun env m r => cov env m (.letT r)) fun _ _ _ h => h) fun acc =>
        Triple.bind (ihv acc fun env m r => cov env m (.letV r)) fun acc' =>
          ihb acc' fun env m r => cov env m (.letB r)
  | lit literal hash =>
    rintro ⟨refs, univs, seen⟩ _
    rw [collectExprTablesStructural]
    split
    · exact Triple.returns fun _ _ _ h => h
    · cases literal
      · exact Triple.bind (Triple.blob _) fun _ => Triple.returns fun _ _ _ h => h.1.push (.inr h.2)
      · exact Triple.bind (Triple.blob _) fun _ => Triple.returns fun _ _ _ h => h.1.push (.inr h.2)
  | mdata data inner hash ih =>
    rintro ⟨refs, univs, seen⟩ cov
    rw [collectExprTablesStructural]
    split
    · exact Triple.returns fun _ _ _ h => h
    · exact Triple.pre (ih _ fun env m r => cov env m (.mdata r)) fun _ _ _ h => h
  | proj name field struct hash ih =>
    rintro ⟨refs, univs, seen⟩ cov
    rw [collectExprTablesStructural]
    split
    · exact Triple.returns fun _ _ _ h => h
    · exact Triple.bind (Triple.lookup name) fun a => Triple.pre (ih _ fun env m r => cov env m (.projStruct r))
        fun env _ _ h => h.1.push (.inl ⟨name, cov env name (.projName (name_beq_self name)), h.2⟩)

theorem Triple.collectRoots (roots : List (Ix.Expr × List Ix.Name)) (acc : ExprTableCollection)
    (cov : ∀ root ∈ roots, Covers M root.1) :
    Triple (RefsOK M B) (AllAllowed M B acc.1) (collectPreseedExprs roots acc)
      (fun env s out => AllAllowed M B out.1 env s) := by
  induction roots generalizing acc with
  | nil => exact Triple.returns fun _ _ _ h => h
  | cons root rest ih =>
    obtain ⟨e, params⟩ := root
    rw [collectPreseedExprs]
    refine Triple.bind ?_ fun acc' => ih acc' (fun r hr => cov r (List.mem_cons_of_mem _ hr))
    refine Triple.withUnivCtx params (fun _ _ h a ha => h a ha |>.mono (Extends.of_blobs rfl)) ?_
    unfold collectExprTables
    exact Triple.bind (Frame.triple (Frame.view (Preserves.read _))) fun block =>
      Triple.collect _ _ _ e acc (cov (e, params) (by simp))

theorem Triple.internRefs (refs : List Address) (previous : Option Address) :
    Triple (RefsOK M B) (fun env s => ∀ a ∈ refs, Allowed M B env s a) (internPreseedRefs refs previous)
      (fun _ _ _ => True) := by
  induction refs generalizing previous with
  | nil => exact Triple.returns fun _ _ _ _ => trivial
  | cons address rest ih =>
    unfold internPreseedRefs
    split
    · refine Triple.bind (Q := fun env s _ => ∀ a ∈ rest, Allowed M B env s a) ?_ fun _ => ih _
      unfold Functor.discard
      exact Triple.bind (Triple.pre (Triple.internRefWith (C := fun env s => ∀ a ∈ rest, Allowed M B env s a)
          (fun _ _ _ e h a ha => (h a ha).mono (Extends.of_blobs e)))
          fun _ _ _ h => ⟨fun a ha => h a (List.mem_cons_of_mem _ ha), h address (by simp)⟩)
        fun _ => Triple.returns fun _ _ _ h => h
    · exact Triple.pre (ih _) fun _ _ _ h a ha => h a (List.mem_cons_of_mem _ ha)

theorem Frame.internUniv (univ : Ixon.Univ) : Frame (internUniv univ) := by
  refine Frame.of_same fun context before => ?_
  cases found : before.univsIndex.get? univ with
  | some index => rw [Interning.internUniv_hit univ context before found]; exact ⟨rfl, rfl, rfl⟩
  | none =>
    rw [Interning.internUniv_miss univ context before found]
    split
    · exact ⟨rfl, rfl, rfl⟩
    · rw [Interning.checkedTableCount_state]; exact ⟨rfl, rfl, rfl⟩

theorem Frame.discard {action : CompileM α} (inner : Frame action) : Frame (Functor.discard action) := by
  unfold Functor.discard
  exact Frame.bind inner (fun _ => Frame.pure ())

theorem Frame.internUnivs (entries : List (ByteArray × Ixon.Univ)) (previous : Option ByteArray) :
    Frame (internPreseedUnivs entries previous) := by
  induction entries generalizing previous with
  | nil => exact Frame.pure ()
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    unfold internPreseedUnivs
    split
    · exact Frame.bind (Frame.discard (Frame.internUniv value)) (fun _ => ih _)
    · exact ih _

theorem Frame.canonUnivs (values : List Ixon.Univ) (initial : Array Ixon.Univ) :
    Frame (canonPreseedUnivs values initial) := by
  induction values generalizing initial with
  | nil => exact Frame.pure initial
  | cons value rest ih =>
    unfold canonPreseedUnivs
    refine Frame.bind ?_ (fun canonical => ih (initial.push canonical))
    refine Frame.of_same fun context before => ?_
    rw [CanonUnivCache.canonUnivCached_run]
    cases before.canonUnivCache.get? value
    all_goals exact ⟨rfl, rfl, rfl⟩

theorem Frame.checkUnivs (univs : Array Ixon.Univ) : Frame (checkPreseedUnivs univs) := by
  unfold checkPreseedUnivs
  split
  · exact Frame.pure ()
  · exact Frame.throw _

/-- **The preseed keeps the invariant**, for roots it covers. -/
theorem Holds.preseed (roots : Array (Ix.Expr × List Ix.Name)) (cov : ∀ root ∈ roots.toList, Covers M root.1) :
    Holds (RefsOK M B) (preseedExprTables roots) := by
  unfold preseedExprTables
  refine Triple.bind (Triple.pre (Triple.collectRoots roots.toList (#[], #[], {}) cov)
    fun _ _ _ _ a ha => by simp at ha) fun collection => ?_
  obtain ⟨refs, univs, seen⟩ := collection
  refine Triple.bind (Triple.pre (Triple.internRefs _ none) fun _ _ _ h a ha => h a ?_) fun _ => ?_
  · rw [Array.mem_toList_iff, Canon.mem_qsort] at ha
    exact ha
  · exact Holds.framed (Frame.bind (Frame.canonUnivs _ _) fun _ => Frame.bind (Frame.checkUnivs _) fun _ =>
      Frame.bind (Frame.internUnivs _ _) fun _ => Frame.view (Preserves.modify _ _ fun _ => rfl))

/-! ## A block compile's reference table -/

/-- A term a block compile reads under the name `x`: one of the constant's terms, or the type of
a constructor an inductive lists. -/
def TermOf (E : Ix.Environment) (x : Ix.Name) (e : Ix.Expr) : Prop :=
  ∃ ci, E.get? x = some ci ∧ (e ∈ termsOf ci ∨
    ∃ iv c cv, ci = .inductInfo iv ∧ c ∈ iv.ctors ∧ E.get? c = some (.ctorInfo cv) ∧ e = cv.cnst.type)

/-- **A name a block's terms mention**: one a term read under a name `N` admits mentions. -/
def Mentioned (E : Ix.Environment) (N : Ix.Name → Prop) (n : Ix.Name) : Prop :=
  ∃ x e, N x ∧ TermOf E x e ∧ Refs n e

theorem covers_of {E : Ix.Environment} {N : Ix.Name → Prop} {x : Ix.Name} {e : Ix.Expr} (hN : N x)
    (ht : TermOf E x e) : Covers (fun _ => Mentioned E N) e :=
  fun _ _ r => ⟨x, e, hN, ht, r⟩

theorem refsOK_empty : RefsOK M (bindingView {}) env ({} : BlockState) :=
  ⟨rfl, fun a ha => by simp at ha⟩

theorem Holds.definitionDataInfo (d : Ix.Def) (ct : Covers M d.type) (cv : Covers M d.value) :
    Holds (RefsOK M B) (compileDefinitionDataInfo d) (fun _ s r => r.block.refs = s.refs) := by
  unfold compileDefinitionDataInfo compileDefinitionDataBlock
  refine Holds.seq (Holds.preseed _ ?_) fun _ => Holds.seq (Holds.definitionData d ct cv) fun out => ?_
  · intro root hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ct
    · exact cv
  · obtain ⟨defn, md, _, _⟩ := out
    exact Holds.finishConstant _ _

/-- **A lone constant's compile keeps the invariant**, for the terms read under its name, and
returns a block whose table is the final state's. -/
theorem Holds.constantInfo {E : Ix.Environment} {N : Ix.Name → Prop} {x : Ix.Name} {const : ConstantInfo}
    (found : E.get? x = some const) (hN : N x) (hi : ∀ v, const = .inductInfo v → False)
    (hc : ∀ v, const = .ctorInfo v → False) :
    Holds (RefsOK (fun _ => Mentioned E N) B) (compileConstantInfo const) (fun _ s r => r.block.refs = s.refs) := by
  have cov : ∀ e ∈ termsOf const, Covers (fun _ => Mentioned E N) e :=
    fun e he => covers_of hN ⟨const, found, .inl he⟩
  cases const with
  | defnInfo v =>
    show Holds _ (compileDefinitionConstantInfo v) _
    unfold compileDefinitionConstantInfo
    rw [EmissionDispatch.compileDefinitionInfo_eq]
    exact Triple.withMutCtx _ (Holds.definitionDataInfo _ (cov _ (by simp [termsOf, definitionValData]))
      (cov _ (by simp [termsOf, definitionValData])))
  | thmInfo v =>
    show Holds _ (compileTheoremConstantInfo v) _
    unfold compileTheoremConstantInfo compileTheoremInfo
    exact Triple.withMutCtx _ (Holds.definitionDataInfo _ (cov _ (by simp [termsOf, theoremValData]))
      (cov _ (by simp [termsOf, theoremValData])))
  | opaqueInfo v =>
    show Holds _ (compileOpaqueConstantInfo v) _
    unfold compileOpaqueConstantInfo compileOpaqueInfo
    exact Triple.withMutCtx _ (Holds.definitionDataInfo _ (cov _ (by simp [termsOf, opaqueValData]))
      (cov _ (by simp [termsOf, opaqueValData])))
  | axiomInfo v =>
    show Holds _ (compileConstantInfoCore (.axiomInfo v)) _
    unfold compileConstantInfoCore
    refine Triple.withMutCtx _ ?_
    show Holds _ (compileAxiomInfo v) _
    have ct := cov v.cnst.type (by simp [termsOf, ConstantInfo.getCnst])
    unfold compileAxiomInfo compileAxiomBlock
    refine Holds.seq (Holds.preseed _ fun root hr => ?_) fun _ =>
      Holds.seq (Holds.axiomPayload v ct) fun out => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [hr]
      exact ct
    · obtain ⟨_, _, _⟩ := out
      exact Holds.finishConstant _ _
  | quotInfo v =>
    show Holds _ (compileQuotientConstantInfo v) _
    unfold compileQuotientConstantInfo
    refine Triple.withMutCtx _ ?_
    have ct := cov v.cnst.type (by simp [termsOf, ConstantInfo.getCnst])
    unfold compileQuotientInfo compileQuotientBlock
    refine Holds.seq (Holds.preseed _ fun root hr => ?_) fun _ =>
      Holds.seq (Holds.quotientPayload v ct) fun out => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [hr]
      exact ct
    · obtain ⟨_, _, _⟩ := out
      exact Holds.finishConstant _ _
  | recInfo v =>
    show Holds _ (compileRecursorConstantInfo v) _
    unfold compileRecursorConstantInfo
    refine Triple.withMutCtx _ ?_
    unfold compileRecursorInfo compileRecursorBlock
    refine Holds.seq (Holds.preseed _ fun root hr => ?_) fun _ =>
      Holds.seq (Holds.recursorPayload v (cov _ (by simp [termsOf]))
        fun rule hr => cov _ (by simp only [termsOf]; exact List.mem_cons_of_mem _ (List.mem_map_of_mem hr)))
        fun out => ?_
    · unfold recursorPreseedExprs at hr
      simp only [List.mem_map] at hr
      obtain ⟨e, he, rfl⟩ := hr
      exact cov e he
    · obtain ⟨_, _, _⟩ := out
      exact Holds.finishConstant _ _
  | inductInfo v => exact (hi v rfl).elim
  | ctorInfo v => exact (hc v rfl).elim

/-- The preseed roots of a member are its terms. -/
theorem memberInputs_covers {c : MutConst} (cov : MutCovers M c) :
    ∀ root ∈ mutConstPreseedInputs c, Covers M root.1 := by
  intro root hr
  cases c with
  | defn d =>
    simp only [mutConstPreseedInputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cov.1
    · exact cov.2
  | indc i =>
    simp only [mutConstPreseedInputs, List.mem_cons, List.mem_map] at hr
    rcases hr with rfl | ⟨ctor, hctor, rfl⟩
    · exact cov.1
    · exact cov.2 ctor hctor
  | recr r =>
    simp only [mutConstPreseedInputs, recursorSourceExprs, List.mem_map, List.mem_cons] at hr
    obtain ⟨e, he, rfl⟩ := hr
    rcases he with rfl | ⟨rule, hrule, rfl⟩
    · exact cov.1
    · exact cov.2 rule hrule

theorem mutualInputs_covers : ∀ (members : List MutConst), (∀ c ∈ members, MutCovers M c) →
    ∀ root ∈ mutualPreseedInputs members, Covers M root.1
  | [], _, root, hr => by simp [mutualPreseedInputs] at hr
  | source :: rest, cov, root, hr => by
    rw [mutualPreseedInputs, List.mem_append] at hr
    rcases hr with hr | hr
    · exact memberInputs_covers (cov source (by simp)) root hr
    · exact mutualInputs_covers rest (fun c h => cov c (List.mem_cons_of_mem _ h)) root hr

/-- **A mutual block compile keeps the invariant**, for its members' terms, and returns a block
whose table is the final state's. -/
theorem Holds.mutualBlock (classes : List MutConst) (cov : ∀ c ∈ classes, MutCovers M c) :
    Holds (RefsOK M B) (compileMutualBlock classes) (fun _ s r => r.block.refs = s.refs) := by
  unfold compileMutualBlock
  dsimp only
  refine Triple.withMutCtx _ ?_
  refine Holds.seq (Holds.preseed _ fun root hr => ?_) fun _ => Holds.mutualPayload classes cov
  unfold mutualPreseedExprs at hr
  rw [List.toList_toArray] at hr
  exact mutualInputs_covers classes cov root hr

/-- **The members the block compile reads cover their terms.** -/
theorem members_covers (ctx : CompileEnv × BlockEnv) (all : Ix.Set Ix.Name) {N : Ix.Name → Prop}
    (hN : ∀ x, all.contains x = true → N x) :
    Claims.RunPost ctx (fun cs : Array MutConst => ∀ m ∈ cs, MutCovers (fun _ => Mentioned ctx.1.env N) m)
      (forIn all #[] fun n (acc : Array Ix.MutConst) => do
        match ← findConst n with
        | .inductInfo val => pure (ForInStep.yield (acc.push (← MutConst.mkIndc val)))
        | .defnInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromDefinitionVal val)))
        | .opaqueInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromOpaqueVal val)))
        | .thmInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromTheoremVal val)))
        | .recInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.recr val)))
        | _ => pure (ForInStep.yield acc)) := by
  rw [Std.HashSet.forIn_eq_forIn_toList]
  refine Claims.RunPost.forIn ctx _ _ all.toList (fun n hn acc hacc => ?_) #[] (by simp)
  have hin : N n := hN n (Std.HashSet.mem_iff_contains.1 (Std.HashSet.mem_of_mem_toList hn))
  have push : ∀ m, MutCovers (fun _ => Mentioned ctx.1.env N) m →
      ∀ m' ∈ acc.push m, MutCovers (fun _ => Mentioned ctx.1.env N) m' := by
    intro m hm m' hm'
    rcases Array.mem_push.1 hm' with hm' | rfl
    · exact hacc m' hm'
    · exact hm
  refine Claims.RunPost.bind (Claims.RunPost.findConst ctx n) fun ci hci => ?_
  have cov : ∀ e ∈ termsOf ci, Covers (fun _ => Mentioned ctx.1.env N) e :=
    fun e he => covers_of hin ⟨ci, hci, .inl he⟩
  split
  · rename_i val
    refine Claims.RunPost.bind (q := fun m => MutCovers (fun _ => Mentioned ctx.1.env N) m) ?_
      fun m hm => Claims.RunPost.pure (push m hm)
    unfold MutConst.mkIndc
    refine Claims.RunPost.bind (Claims.collectCtors_post ctx val.ctors.toList _ #[] (by simp) fun _ h => h)
      fun ctors h => Claims.RunPost.pure ⟨cov _ (by simp [termsOf, ConstantInfo.getCnst]), fun ctor hctor => ?_⟩
    obtain ⟨c, hc, hcs⟩ := h ctor (by simpa using hctor)
    exact covers_of hin ⟨_, hci, .inr ⟨val, c, ctor, rfl, Array.mem_toList_iff.1 hc, hcs, rfl⟩⟩
  · exact Claims.RunPost.pure (push _ ⟨cov _ (by simp [termsOf]),
      cov _ (by simp [termsOf])⟩)
  · exact Claims.RunPost.pure (push _ ⟨cov _ (by simp [termsOf]),
      cov _ (by simp [termsOf])⟩)
  · exact Claims.RunPost.pure (push _ ⟨cov _ (by simp [termsOf]),
      cov _ (by simp [termsOf])⟩)
  · exact Claims.RunPost.pure (push _ ⟨cov _ (by simp [termsOf]),
      fun rule hr => cov _ (by simp only [termsOf]; exact List.mem_cons_of_mem _ (List.mem_map_of_mem hr))⟩)
  · exact Claims.RunPost.pure hacc

/-- **Every entry of a compiled block's reference table is allowed**: the binding, at the
empty block's view, of a name the block's members' terms mention, or a blob of the block
compile's final state or of the environment. -/
theorem compileBlock_refs {ctx : CompileEnv × BlockEnv} {lo : Ix.Name} {all : Ix.Set Ix.Name}
    {r : BlockResult} {s' : BlockState}
    (h : rawRun (compileBlock lo all) ctx {} = (.ok r, s')) :
    ∃ s : BlockState, ∀ a ∈ r.block.refs,
      Allowed (fun _ => Mentioned ctx.1.env (fun x => all.contains x = true ∨ x = lo)) (bindingView {}) ctx.1 s a := by
  unfold compileBlock at h
  obtain ⟨const, s₁, hc, h⟩ := bind_ok h
  have found := BlockRecords.findConst_ok hc
  have h₁ : s₁ = {} := by
    have := BlockRecords.findConst_preserves lo ctx {}
    rw [hc] at this
    exact this
  subst h₁
  dsimp only at h
  split at h <;> split at h
  all_goals first
    | (rename_i hcond; simp at hcond; done)
    | (obtain ⟨cs, s₂, hcs, h⟩ := bind_ok h
       obtain ⟨out, s₄, hout, h⟩ := bind_ok h
       have same : BlockRecords.recordsOf r = BlockRecords.recordsOf out := by
         revert h
         refine BlockRecords.Returns.elim
           (P := fun (x : BlockResult) =>
             BlockRecords.recordsOf x = BlockRecords.recordsOf out) ?_
         repeat returns_step
       have block : r.block = out.block := (Prod.mk.inj same).1
       have members := members_covers ctx all (N := fun x => all.contains x = true ∨ x = lo)
         (fun x hx => .inl hx) {} cs s₂ hcs
       have h₂ : s₂ = {} := BlockRecords.forIn_set_state hcs fun n acc => by
         refine Preserves.bind (BlockRecords.findConst_preserves n) fun c => ?_
         split
         · exact Preserves.bind (BlockRecords.mkIndc_preserves _) fun _ => Preserves.pure id _
         all_goals exact Preserves.pure id _
       subst h₂
       obtain ⟨hI, refs⟩ := Holds.mutualBlock (B := bindingView {}) (sourceMembers cs)
         (fun c hc => members c (Claims.mem_sourceMembers hc)) ctx {} out s₄ refsOK_empty trivial hout
       exact ⟨s₄, fun a ha => hI.2 a (by rw [← refs, ← block]; exact ha)⟩)
    | (obtain ⟨hI, same⟩ := Holds.constantInfo (B := bindingView {})
         (N := fun x => all.contains x = true ∨ x = lo) found (Or.inr rfl)
         (by assumption) (by assumption) ctx {} r s' refsOK_empty trivial h
       refine ⟨s', fun a ha => hI.2 a ?_⟩
       rw [← same]
       exact ha)

/-- **Every entry of a compiled block's reference table is allowed**, for `runBlock`. -/
theorem runBlock_refs {cenv : CompileEnv} {all : Ix.Set Ix.Name} {lo : Ix.Name} {r : BlockResult}
    {c : BlockState} (h : runBlock cenv all lo = .ok (r, c)) :
    ∃ s : BlockState, ∀ a ∈ r.block.refs,
      Allowed (fun _ => Mentioned cenv.env (fun x => all.contains x = true ∨ x = lo)) (bindingView {}) cenv s a :=
  compileBlock_refs (Ix.CompileCert.run_success (BlockRecords.runBlock_compiles h))

/--
info: 'Ix.Cert.RefTables.Holds.expression' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Holds.expression

/--
info: 'Ix.Cert.RefTables.Holds.preseed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Holds.preseed

/--
info: 'Ix.Cert.RefTables.runBlock_refs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms runBlock_refs

end Ix.Cert.RefTables
