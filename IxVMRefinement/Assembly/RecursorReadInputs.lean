import IxVMRefinement.Assembly.ReadBare
import Ix.Cert.CtxAgree
import Ix.CompileCert.Loop
import Ix.CompileCert.ReaderIndex

/-! # Inputs retained by an actual recursor reading

A successful recursor read determines its raw payload, chosen member key, level-parameter
mapping, type conversion and each rule conversion. The certificate keeps the actual major
carrier and constructor slots; it does not identify local motive positions with a globally
chosen block order or assume that reader member keys equal a role table's keys.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok forIn_inv_array forall₂_append)
open Ix.Cert.ReaderUnits (fail_bind throw_ok)

def recursorReaderSelf {md : Mode} (cx : Ctx md) (record : Ixon.Constant)
    (owner : _root_.Address) (key : CName md) : Nat → Option (ReadM (CName md)) :=
  fun i => match record.info with
    | .muts members => if i < members.size then some (cx.memberKey (.member owner i)) else none
    | _ => if i == 0 then some (pure key) else none

def RecursorRuleReadFrame {md : Mode} (cx : Ctx md) (reader : MemberReader md)
    (majorOwner : _root_.Address) (majorSlot : Nat)
    (source : Ixon.RecursorRule × Nat) (rule : RecRule md) : Prop :=
  cx.memberKey (.ctor majorOwner majorSlot source.2) = .ok rule.ctor ∧
  reader.read source.1.rhs = .ok rule.rhs ∧
  rule = RecRule.mk rule.ctor source.1.fields.toNat 0 .inert rule.rhs false false false

/-- All fields come from the successful reader run. In particular the rule correspondence
is positional and keeps the raw field counts, without assuming semantic rule validity. -/
structure RecursorReadInputs {md : Mode} (cx : Ctx md) (blockLps : List LevelParam)
    (ref : ConstRef _root_.Address) (entry : RecEntry)
    (row : CVal md × RecCounts × List (RecRule md)) where
  owner : _root_.Address
  slot : Nat
  record : Ixon.Constant
  recursor : Ixon.Recursor
  majorOwner : _root_.Address
  majorSlot : Nat
  major : Ixon.Inductive
  reference : ref = .member owner slot
  stored : cx.store owner = some record
  selected : (recursorMembers record).find? (·.1 == slot) = some (slot, recursor)
  safe : recursor.isUnsafe = false
  named : cx.memberKey ref = .ok row.1.name
  levels : row.1.levelParams = recLps entry.large blockLps
  typeRead : (MemberReader.mk' cx record (recParam (recLps entry.large blockLps))
    (recursorReaderSelf cx record owner row.1.name)).read recursor.typ = .ok row.1.type
  majorReference : entry.major = .member majorOwner majorSlot
  majorStored : inductiveAt cx.store entry.major = some major
  ruleCount : major.ctors.size = recursor.rules.size
  counts : row.2.1 = ⟨recursor.params.toNat, recursor.motives.toNat, recursor.minors.toNat,
    recursor.indices.toNat, recursor.k, some entry.motive⟩
  rules : List.Forall₂ (RecursorRuleReadFrame cx
    (MemberReader.mk' cx record (recParam (recLps entry.large blockLps))
      (recursorReaderSelf cx record owner row.1.name)) majorOwner majorSlot)
    recursor.rules.zipIdx.toList row.2.2

theorem readRecursor_inputs {md : Mode} {cx : Ctx md} {blockLps : List LevelParam}
    {ref : ConstRef _root_.Address} {entry : RecEntry}
    {row : CVal md × RecCounts × List (RecRule md)}
    (read : readRecursor cx blockLps ref entry = .ok row) :
    Nonempty (RecursorReadInputs cx blockLps ref entry row) := by
  cases ref with
  | ctor owner member slot =>
    exact (throw_ok read).elim
  | member owner slot =>
    unfold readRecursor at read
    dsimp only at read
    cases stored : cx.store owner with
    | none =>
      rw [stored] at read
      exact (throw_ok read).elim
    | some record =>
      rw [stored] at read
      dsimp only at read
      cases selected : (recursorMembers record).find? (·.1 == slot) with
      | none =>
        rw [selected] at read
        exact (throw_ok read).elim
      | some found =>
        rcases found with ⟨selectedSlot, recursor⟩
        have slotEq : selectedSlot = slot := by
          simpa using Array.find?_some (p := fun pair : Nat × Ixon.Recursor => pair.1 == slot) selected
        subst selectedSlot
        rw [selected] at read
        dsimp only at read
        rcases Ix.Cert.CtxAgree.ite_ok' read with ⟨_, failed⟩ | ⟨safe, read⟩
        · exact (fail_bind failed).elim
        · obtain ⟨key, named, read⟩ := except_bind_ok.mp read
          obtain ⟨type, typeRead, read⟩ := except_bind_ok.mp read
          cases majorStored : inductiveAt cx.store entry.major with
          | none =>
            rw [majorStored] at read
            exact (throw_ok read).elim
          | some major =>
            rw [majorStored] at read
            dsimp only at read
            rcases Ix.Cert.CtxAgree.ite_ok' read with ⟨ruleCount, read⟩ | ⟨_, failed⟩
            · cases majorReference : entry.major with
              | ctor majorOwner majorSlot ctorSlot =>
                rw [majorReference] at read
                exact (throw_ok read).elim
              | member majorOwner majorSlot =>
                rw [majorReference] at read
                dsimp only at read
                obtain ⟨rules, rulesRead, returned⟩ := except_bind_ok.mp read
                simp only [pure, Except.pure, Except.ok.injEq] at returned
                subst row
                let reader := MemberReader.mk' cx record (recParam (recLps entry.large blockLps))
                  (recursorReaderSelf cx record owner key)
                have frames : List.Forall₂ (RecursorRuleReadFrame cx reader majorOwner majorSlot)
                    recursor.rules.zipIdx.toList rules := by
                  apply forIn_inv_array
                    (fun processed current =>
                      List.Forall₂ (RecursorRuleReadFrame cx reader majorOwner majorSlot) processed current)
                    _ recursor.rules.zipIdx ?_ (.nil) rulesRead
                  intro processed source suffix current out _ held ran
                  rcases source with ⟨raw, position⟩
                  obtain ⟨ctor, ctorRead, ran⟩ := except_bind_ok.mp ran
                  obtain ⟨rhs, rhsRead, ran⟩ := except_bind_ok.mp ran
                  simp only [pure, Except.pure, Except.ok.injEq] at ran
                  subst out
                  refine ⟨_, rfl, ?_⟩
                  exact forall₂_append held (.cons ⟨ctorRead, rhsRead, rfl⟩ .nil)
                exact ⟨{
                  owner, slot, record, recursor, majorOwner, majorSlot, major
                  reference := rfl
                  stored, selected
                  safe := by simpa using safe
                  named
                  levels := rfl
                  typeRead
                  majorReference, majorStored
                  ruleCount := by simpa using ruleCount
                  counts := rfl
                  rules := frames }⟩
            · exact (fail_bind failed).elim

theorem RecursorReadInputs.payload {md : Mode} {cx : Ctx md} {blockLps : List LevelParam}
    {ref : ConstRef _root_.Address} {entry : RecEntry}
    {row : CVal md × RecCounts × List (RecRule md)}
    (inputs : RecursorReadInputs cx blockLps ref entry row) :
    (inputs.slot, inputs.recursor) ∈ recursorMembers inputs.record :=
  Array.mem_of_find?_eq_some inputs.selected

/-- The retained payload is the given stored member, not an independently chosen raw
record or recursor with a coincidentally matching output. -/
theorem RecursorReadInputs.same_payload {md : Mode} {cx : Ctx md} {blockLps : List LevelParam}
    {owner : _root_.Address} {slot : Nat} {entry : RecEntry}
    {row : CVal md × RecCounts × List (RecRule md)}
    (inputs : RecursorReadInputs cx blockLps (.member owner slot) entry row)
    {source : Ixon.Constant} {recursor : Ixon.Recursor}
    (stored : cx.store owner = some source) (member : (slot, recursor) ∈ recursorMembers source) :
    inputs.record = source ∧ inputs.recursor = recursor := by
  have positions := ConstRef.member.inj inputs.reference
  have actualStored := inputs.stored
  rw [← positions.1] at actualStored
  have sameRecord : inputs.record = source := Option.some.inj (actualStored.symm.trans stored)
  have actualMember := inputs.payload
  rw [← positions.2, sameRecord] at actualMember
  exact ⟨sameRecord, Ix.CompileCert.ReaderIndex.member_unique source slot inputs.recursor recursor
    actualMember member⟩

end IxVM.Refinement.Assembly
