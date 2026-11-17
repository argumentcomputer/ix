import IxVMRefinement.Assembly.GuardRawReadback
import IxVMRefinement.Assembly.GuardRawLoads

/-! # Actual raw constant payloads supply their selected dictionary roots

The root relation retains the exact physical pointer and actual serialized conversion, rather
than only existence of a reader answer. It includes self-reference and literal-store agreement.
-/

namespace IxVM.Refinement.GuardRaw

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Consistency
open IxVM (F)

/-- Actual conversion of one selected dictionary root, at its physical payload pointer. -/
def RootConverted (blob : Blobs) (root : Root) (h : Heap F) (p : SourceValue F) : Prop :=
  ∃ (recurAddrs : List _root_.Address) (blobs : List (_root_.Address × ByteArray)),
    L1.RawConvExpr root.source.refs.toList recurAddrs root.source.univs.toList
      root.source.sharing.toList blobs h 4294967295 root.expression p ∧
    (∀ i a, recurAddrs[i]? = some a → ∃ m key, root.self i = some m ∧ m = .ok key) ∧
    (∀ i a m key, recurAddrs[i]? = some a → root.self i = some m → m = .ok key →
      key = Core.keyOf addressTable a) ∧
    (∀ a bytes, (a, bytes) ∈ blobs → blob a = some bytes)

theorem RootConverted.read {blob : Blobs} {root : Root} {h : Heap F} {p : SourceValue F}
    (converted : RootConverted blob root h p) : ∃ e, readRoot blob root = some e := by
  obtain ⟨_, _, raw, selfComplete, _, blobs⟩ := converted
  exact readRoot_of_rawConv raw selfComplete blobs

theorem RootConverted.exact {blob : Blobs} {root : Root} {h : Heap F} {p : SourceValue F}
    {Γ : Nat → Core.KExpr} {k : Nat} {R E : Core.KExpr}
    (converted : RootConverted blob root h p)
    (physical : Decl.RawTmExact (Core.keyOf addressTable) 0 Γ h k R E p) :
    readRoot blob root = some R.eraseMeta := by
  obtain ⟨e, read⟩ := converted.read
  obtain ⟨_, _, raw, _, keyed, blobs⟩ := converted
  have same := readRoot_exact raw keyed blobs physical read
  rwa [same] at read

private theorem solo_self_complete (a : _root_.Address) (d : Ixon.Definition) :
    ∀ i x, (L1.defnRecurAddrs d a)[i]? = some x →
      ∃ m key, soloSelf addressTable a i = some m ∧ m = .ok key := by
  unfold L1.defnRecurAddrs
  split
  · exact LoadedReads.soloSelf_ok addressTable a
  · intro i x impossible; simp at impossible

private theorem solo_self_keyed (a : _root_.Address) (d : Ixon.Definition) :
    ∀ i x m key, (L1.defnRecurAddrs d a)[i]? = some x → soloSelf addressTable a i = some m →
      m = .ok key → key = Core.keyOf addressTable x := by
  unfold L1.defnRecurAddrs
  split
  · exact LoadedReads.soloSelf_key addressTable a
  · intro i x m key impossible; simp at impossible

private theorem member_self_complete (B : _root_.Address) (ms : Array Ixon.MutConst)
    (d : Ixon.Definition) :
    ∀ i x, (L1.defnMemberRecurAddrs d B ms.toList)[i]? = some x →
      ∃ m key, blockSelf addressTable B ms i = some m ∧ m = .ok key := by
  unfold L1.defnMemberRecurAddrs
  split
  · exact LoadedReads.blockSelf_ok addressTable B ms
  · intro i x impossible; simp at impossible

private theorem member_self_keyed (B : _root_.Address) (ms : Array Ixon.MutConst)
    (d : Ixon.Definition) :
    ∀ i x m key, (L1.defnMemberRecurAddrs d B ms.toList)[i]? = some x →
      blockSelf addressTable B ms i = some m → m = .ok key → key = Core.keyOf addressTable x := by
  unfold L1.defnMemberRecurAddrs
  split
  · exact LoadedReads.blockSelf_key addressTable B ms
  · intro i x m key impossible; simp at impossible

/-- A standalone actual Defn payload supplies the exact selected value root and count. -/
theorem valueRoot_converted_defn {E : Ixon.Env} {h : Heap F} {a : _root_.Address}
    {c : Ixon.Constant} {d : Ixon.Definition} {v nl ty value flag hint : SourceValue F}
    (record : recordOf E a = some c) (info : c.info = .defn d)
    (shape : v = .construct Core.kciEnum "Defn" [nl, ty, value, flag, hint])
    (raw : L1.RawCIRep E h a c v) :
    L1.EnvInternalCollision E ∨ ∃ root,
      valueRoot (recordOf E) a = some root ∧ root.levels < 4294967296 ∧
      nl = .field (root.levels : F) ∧ RootConverted (fun x => E.blobs.get? x) root h value := by
  rw [L1.RawCIRep, info] at raw
  obtain ⟨blobs, stored, bound, tp, vp, hint', observedShape, _, converted⟩ := raw
  have kind := definition_kind_of_shape (observedShape.symm.trans shape)
  have same := observedShape.symm.trans shape
  simp only [L1.defnValShape, kind, Value.construct.injEq, List.cons.injEq, and_true, true_and] at same
  obtain ⟨count, _, valueEq, _, _⟩ := same
  cases valueEq
  rcases stored with stored | collision
  · let root : Root := ⟨c, soloSelf addressTable a, 1, d.lvls.toNat, d.value⟩
    refine Or.inr ⟨root, ?_, bound, count.symm, ?_⟩
    · simp [valueRoot, record, info, kind, root]
    · exact ⟨_, blobs, converted, solo_self_complete a d, solo_self_keyed a d,
        fun x bytes member => (stored x bytes member).1⟩
  · exact Or.inl collision

/-- A definition-block member actually loaded as Defn supplies its physical value root,
including the owner record and its serialized member offset. -/
theorem valueRoot_converted_dprj {E : Ixon.Env} {h : Heap F} {a : _root_.Address}
    {c : Ixon.Constant} {p : Ixon.DefinitionProj} {v nl ty value flag hint : SourceValue F}
    (record : recordOf E a = some c) (info : c.info = .dPrj p)
    (shape : v = .construct Core.kciEnum "Defn" [nl, ty, value, flag, hint])
    (raw : L1.RawCIRep E h a c v) :
    L1.EnvInternalCollision E ∨ ∃ root,
      valueRoot (recordOf E) a = some root ∧ root.levels < 4294967296 ∧
      nl = .field (root.levels : F) ∧ RootConverted (fun x => E.blobs.get? x) root h value := by
  rw [L1.RawCIRep, info] at raw
  obtain ⟨_, lc, cb, ms, d, blobs, getOwner, _, _, decoded, _, members, member, stored,
    bound, tp, vp, hint', observedShape, _, converted⟩ := raw
  have kind := definition_kind_of_shape (observedShape.symm.trans shape)
  have same := observedShape.symm.trans shape
  simp only [L1.defnValShape, kind, Value.construct.injEq, List.cons.injEq, and_true, true_and] at same
  obtain ⟨count, _, valueEq, _, _⟩ := same
  cases valueEq
  have owner := Typing.recordOf_of_get getOwner decoded
  have member' : ms[p.idx.toNat]? = some (.defn d) := by simpa only [Array.getElem?_toList] using member
  rcases stored with stored | collision
  · let root : Root := ⟨cb, blockSelf addressTable p.block ms,
        L1.mutsRootOffset ms.toList p.idx.toNat + 1, d.lvls.toNat, d.value⟩
    refine Or.inr ⟨root, ?_, bound, count.symm, ?_⟩
    · simp [valueRoot, record, info, memberRoot, owner, members, member', definitionValue, kind, root]
    · exact ⟨_, blobs, converted, member_self_complete p.block ms d, member_self_keyed p.block ms d,
        fun x bytes belongs => (stored x bytes belongs).1⟩
  · exact Or.inl collision

end IxVM.Refinement.GuardRaw
