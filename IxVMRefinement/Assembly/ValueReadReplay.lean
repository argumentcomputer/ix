import IxVMRefinement.Assembly.AdmittedExpr
import IxVMRefinement.Assembly.BareState

/-! # Value declaration replay with the reader's actual hint

Pruning may change the height-derived reducibility hint. It does not change the parsed
header or value of a retained singleton whose original read performed no projection
rewrite. The final model's hint restoration can use the new reader's concrete hint.
-/

namespace IxVM.Refinement.Assembly.ReaderStoreTransfer

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok)
open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

inductive ValueDeclAgree {md : Mode} : CDecl md → CDecl md → Prop
  | defn (cv : CVal md) (value : CExpr md) (oldHint newHint : ReducibilityHint) :
      ValueDeclAgree (.defnDecl cv value oldHint) (.defnDecl cv value newHint)
  | thm (cv : CVal md) (value : CExpr md) :
      ValueDeclAgree (.thmDecl cv value) (.thmDecl cv value)
  | opaqueVal (cv : CVal md) (value : CExpr md) :
      ValueDeclAgree (.opaqueDecl cv value) (.opaqueDecl cv value)

theorem ValueDeclAgree.names {md : Mode} {old new : CDecl md}
    (h : ValueDeclAgree old new) : new.names = old.names := by
  cases h <;> rfl

private def valueDecl {md : Mode} (cv : CVal md) (value : CExpr md)
    (hint : Option ReducibilityHint) (heights : CName md → Nat) : Ix.DefKind → CDecl md
  | .defn => .defnDecl cv value (hint.getD (Frontend.InModel.hintFor heights value))
  | .thm => .thmDecl cv value
  | .opaq => .opaqueDecl cv value

/-- Empty projection levels replay the raw value at any actual target heights and hint. -/
theorem lowerDefinition_replay_values {md : Mode}
    {oldHint newHint : Option ReducibilityHint} {source target : State md}
    {oldHeights newHeights : CName md → Nat} {cv : CVal md} {value : CExpr md}
    {kind : Ix.DefKind} {safety : Ix.DefinitionSafety} {old : CDecl md}
    (read : lowerDefinition oldHint source oldHeights cv value kind safety = .ok (old, false))
    (empty : ∀ k : CName md, target.projLevels[k]? = none) :
    ∃ new, lowerDefinition newHint target newHeights cv value kind safety = .ok (new, false) ∧
      ValueDeclAgree old new := by
  unfold lowerDefinition at read
  cases safe : safetyDeclineOf kind safety with
  | some reason => simp [safe, declined, throw, throwThe, MonadExceptOf.throw] at read
  | none =>
    simp only [safe, pure, Except.pure] at read
    have declared := congrArg Prod.fst (Except.ok.inj read)
    have flag := congrArg Prod.snd (Except.ok.inj read)
    dsimp only at declared flag
    let result := valueDecl cv value newHint newHeights kind
    have output : lowerDefinition newHint target newHeights cv value kind safety = .ok (result, false) := by
      unfold lowerDefinition
      rw [projRewrite_eq_none empty cv value]
      simp only [safe]
      cases kind <;> rfl
    refine ⟨result, output, ?_⟩
    rw [← declared]
    clear read declared
    cases kind <;> cases rewritten : projRewrite source cv value <;> simp_all [result, valueDecl]
    all_goals first
      | constructor
      | have impossible : (true : Bool) = false := flag
        cases impossible

/-- The new definition read preserves the actual parsed header/value and exposes only a
possible hint change. Its member key, type reading and value reading are all constructed. -/
theorem admitted_readDefinition {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: b.bytes :: readerImages V) calls)
    {seeds : _root_.Address → Prop}
    (closure : UsedClosureOrderAt w.table (admittedOverlay w trace keepTrace) seeds order)
    {owner : _root_.Address} {record : Ixon.Constant} {definition : Ixon.Definition}
    (selected : owner ∈ w.order) (original : Ix.Cert.recordAt w.env owner = some record)
    (info : record.info = .defn definition) (retained : owner ∈ order)
    {source target : State .anon} {oldHeights newHeights : CName .anon → Nat}
    (empty : ∀ k : CName .anon, target.projLevels[k]? = none) {old : CDecl .anon}
    (read : readDefinition (readerContext w.table w.prelude w.env w.order) source oldHeights
      (.member owner 0) (List.range definition.lvls.toNat)
      (MemberReader.mk' (readerContext w.table w.prelude w.env w.order) record id
        (singletonSelf (readerContext w.table w.prelude w.env w.order) owner)) definition =
      .ok (old, false)) :
    ∃ new, readDefinition
        (readerContext w.table w.prelude (admittedOverlay w trace keepTrace) order) target newHeights
        (.member owner 0) (List.range definition.lvls.toNat)
        (MemberReader.mk' (readerContext w.table w.prelude (admittedOverlay w trace keepTrace) order)
          record id (singletonSelf
            (readerContext w.table w.prelude (admittedOverlay w trace keepTrace) order) owner)) definition =
        .ok (new, false) ∧ ValueDeclAgree old new := by
  have single : (match record.info with | .defn _ | .recr _ | .axio _ | .quot _ => True | _ => False) := by
    simp [info]
  have targetRecord := ReaderStoreTransfer.selected (table := w.table) (prelude := w.prelude) retained
    (admittedOverlay_recordAt w keepTrace loaded decoded noCollision selected original)
  have targetKey := streamContext_memberKey_singleton
    (admittedReaderStore_authentic w keepTrace order loaded decoded)
    (check_of_admitBinding w.admitted) targetRecord single
  unfold readDefinition at read ⊢
  obtain ⟨name, nameRead, read⟩ := except_bind_ok.mp read
  obtain ⟨type, typeRead, read⟩ := except_bind_ok.mp read
  obtain ⟨value, valueRead, lowered⟩ := except_bind_ok.mp read
  have originalRecord := ReaderStoreTransfer.selected (table := w.table) (prelude := w.prelude) selected original
  have originalKey := streamContext_memberKey_singleton (admitted_streamStore_authentic w)
    (check_of_admitBinding w.admitted) originalRecord single
  have nameEq := Except.ok.inj (nameRead.symm.trans originalKey)
  have typeRead' := admitted_singleton_read w keepTrace claimBytes loaded decoded noCollision closure
    selected original retained single id
    (fun i used => by simp [usedRefIdxs, info, used]) typeRead
  have valueRead' := admitted_singleton_read w keepTrace claimBytes loaded decoded noCollision closure
    selected original retained single id
    (fun i used => by simp [usedRefIdxs, info, used]) valueRead
  obtain ⟨new, newRead, same⟩ := lowerDefinition_replay_values
    (newHint := (readerContext w.table w.prelude (admittedOverlay w trace keepTrace) order).hint (.member owner 0))
    (newHeights := newHeights) lowered empty
  refine ⟨new, ?_, same⟩
  rw [targetKey, ← nameEq]
  dsimp only [bind, Except.bind]
  rw [typeRead', valueRead']
  exact newRead

/-- Each record of a full stream with zero rewrites was itself read without rewriting. -/
theorem streamRead_member_no_rewrite {md : Mode} {cx : Ctx md} {source final : State md}
    {records : List (_root_.Address × Ixon.Constant)} {decls : Array (CDecl md)}
    (stream : StreamRead cx source records final decls) (zero : final.projRewrites = 0)
    {owner : _root_.Address} {record : Ixon.Constant} (member : (owner, record) ∈ records) :
    ∃ state full, readRecord cx state owner record = .ok full ∧ full.projRewrites = 0 ∧
      ∀ decl ∈ full.decls, decl ∈ decls := by
  induction stream with
  | nil => cases member
  | @cons state _ address constant full rest tail read later ih =>
    rcases List.mem_cons.mp member with same | member
    · cases same
      have counter := streamRead_projRewrites_le later
      rw [commit_projRewrites, zero] at counter
      exact ⟨state, full, read, by omega, fun decl present => Array.mem_append_left _ present⟩
    · obtain ⟨state', full', read', noRewrite, declared⟩ := ih zero member
      exact ⟨state', full', read', noRewrite,
        fun decl present => Array.mem_append_right _ (declared decl present)⟩

theorem admitted_defn_replay {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: b.bytes :: readerImages V) calls)
    {seeds : _root_.Address → Prop}
    (closure : UsedClosureOrderAt w.table (admittedOverlay w trace keepTrace) seeds order)
    {owner : _root_.Address} {record : Ixon.Constant} {definition : Ixon.Definition}
    (selected : owner ∈ w.order) (original : Ix.Cert.recordAt w.env owner = some record)
    (info : record.info = .defn definition) (retained : owner ∈ order)
    {source target : State .anon} (empty : ∀ k : CName .anon, target.projLevels[k]? = none)
    {full : Read .anon}
    (read : readRecord (readerContext w.table w.prelude w.env w.order) source owner record = .ok full)
    (zero : full.projRewrites = 0) :
    ∃ bare old new,
      readRecordBare (readerContext w.table w.prelude (admittedOverlay w trace keepTrace) order)
        target owner record = .ok bare ∧
      full.decls = #[old] ∧ bare.decls = #[new] ∧ ValueDeclAgree old new ∧
      bare.generated = 0 ∧ bare.projRewrites = 0 := by
  simp only [readRecord, info] at read
  obtain ⟨⟨old, rewrote⟩, definitionRead, returned⟩ := except_bind_ok.mp read
  simp only [pure, Except.pure, Except.ok.injEq] at returned
  subst full
  cases rewrote with
  | true => simp at zero
  | false =>
    obtain ⟨new, replay, same⟩ := admitted_readDefinition w keepTrace claimBytes loaded decoded
      noCollision closure selected original info retained
      (newHeights := fun key => target.heights.getD key 0) empty definitionRead
    refine ⟨{ decls := #[new] }, old, new, ?_, rfl, rfl, same, rfl, rfl⟩
    simp only [readRecordBare, info, readRecord]
    simp only [singletonSelf] at replay
    rw [replay]
    rfl

/-- Every retained admitted singleton definition has an actual bare reading at the new
state. The old declaration and its membership in the original full output are recovered
from the admitted run, rather than supplied by the caller. -/
theorem admitted_defn_record {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: b.bytes :: readerImages V) calls)
    {seeds : _root_.Address → Prop}
    (closure : UsedClosureOrderAt w.table (admittedOverlay w trace keepTrace) seeds order)
    {owner : _root_.Address} {record : Ixon.Constant} {definition : Ixon.Definition}
    (selected : owner ∈ w.order) (original : Ix.Cert.recordAt w.env owner = some record)
    (info : record.info = .defn definition) (retained : owner ∈ order)
    (target : State .anon) (empty : ∀ k : CName .anon, target.projLevels[k]? = none) :
    ∃ bare old new,
      readRecordBare (readerContext w.table w.prelude (admittedOverlay w trace keepTrace) order)
        target owner record = .ok bare ∧
      old ∈ w.fullDecls ∧ bare.decls = #[new] ∧ ValueDeclAgree old new ∧
      bare.generated = 0 ∧ bare.projRewrites = 0 := by
  have present := Ix.Cert.RecursorIndex.mem_decoded.mpr ⟨selected, original⟩
  obtain ⟨source, full, read, zero, declared⟩ := streamRead_member_no_rewrite
    (readRecords_spec w.read) w.noProjRewrites (Array.mem_toList_iff.mpr present)
  obtain ⟨bare, old, new, replay, oldDecl, newDecl, same, generated, noRewrite⟩ :=
    admitted_defn_replay w keepTrace claimBytes loaded decoded noCollision closure
      selected original info retained empty read zero
  exact ⟨bare, old, new, replay, declared old (by rw [oldDecl]; simp),
    newDecl, same, generated, noRewrite⟩

end IxVM.Refinement.Assembly.ReaderStoreTransfer
