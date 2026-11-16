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

end IxVM.Refinement.Assembly.ReaderStoreTransfer
