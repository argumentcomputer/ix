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
    Ingress.RawConvExpr root.source.refs.toList recurAddrs root.source.univs.toList
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
    ∀ i x, (Ingress.defnRecurAddrs d a)[i]? = some x →
      ∃ m key, soloSelf addressTable a i = some m ∧ m = .ok key := by
  unfold Ingress.defnRecurAddrs
  split
  · exact LoadedReads.soloSelf_ok addressTable a
  · intro i x impossible; simp at impossible

private theorem solo_self_keyed (a : _root_.Address) (d : Ixon.Definition) :
    ∀ i x m key, (Ingress.defnRecurAddrs d a)[i]? = some x → soloSelf addressTable a i = some m →
      m = .ok key → key = Core.keyOf addressTable x := by
  unfold Ingress.defnRecurAddrs
  split
  · exact LoadedReads.soloSelf_key addressTable a
  · intro i x m key impossible; simp at impossible

private theorem member_self_complete (B : _root_.Address) (ms : Array Ixon.MutConst)
    (d : Ixon.Definition) :
    ∀ i x, (Ingress.defnMemberRecurAddrs d B ms.toList)[i]? = some x →
      ∃ m key, blockSelf addressTable B ms i = some m ∧ m = .ok key := by
  unfold Ingress.defnMemberRecurAddrs
  split
  · exact LoadedReads.blockSelf_ok addressTable B ms
  · intro i x impossible; simp at impossible

private theorem member_self_keyed (B : _root_.Address) (ms : Array Ixon.MutConst)
    (d : Ixon.Definition) :
    ∀ i x m key, (Ingress.defnMemberRecurAddrs d B ms.toList)[i]? = some x →
      blockSelf addressTable B ms i = some m → m = .ok key → key = Core.keyOf addressTable x := by
  unfold Ingress.defnMemberRecurAddrs
  split
  · exact LoadedReads.blockSelf_key addressTable B ms
  · intro i x m key impossible; simp at impossible

/-- A standalone actual Defn payload supplies the exact selected value root and count. -/
theorem valueRoot_converted_defn {E : Ixon.Env} {h : Heap F} {a : _root_.Address}
    {c : Ixon.Constant} {d : Ixon.Definition} {v nl ty value flag hint : SourceValue F}
    (record : recordOf E a = some c) (info : c.info = .defn d)
    (shape : v = .construct Core.kciEnum "Defn" [nl, ty, value, flag, hint])
    (raw : Ingress.RawCIRep E h a c v) :
    Ingress.EnvInternalCollision E ∨ ∃ root,
      valueRoot (recordOf E) a = some root ∧ root.levels < 4294967296 ∧
      nl = .field (root.levels : F) ∧ RootConverted (fun x => E.blobs.get? x) root h value := by
  rw [Ingress.RawCIRep, info] at raw
  obtain ⟨blobs, stored, bound, tp, vp, hint', observedShape, _, converted⟩ := raw
  have kind := definition_kind_of_shape (observedShape.symm.trans shape)
  have same := observedShape.symm.trans shape
  simp only [Ingress.defnValShape, kind, Value.construct.injEq, List.cons.injEq, and_true, true_and] at same
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
    (raw : Ingress.RawCIRep E h a c v) :
    Ingress.EnvInternalCollision E ∨ ∃ root,
      valueRoot (recordOf E) a = some root ∧ root.levels < 4294967296 ∧
      nl = .field (root.levels : F) ∧ RootConverted (fun x => E.blobs.get? x) root h value := by
  rw [Ingress.RawCIRep, info] at raw
  obtain ⟨_, lc, cb, ms, d, blobs, getOwner, _, _, decoded, _, members, member, stored,
    bound, tp, vp, hint', observedShape, _, converted⟩ := raw
  have kind := definition_kind_of_shape (observedShape.symm.trans shape)
  have same := observedShape.symm.trans shape
  simp only [Ingress.defnValShape, kind, Value.construct.injEq, List.cons.injEq, and_true, true_and] at same
  obtain ⟨count, _, valueEq, _, _⟩ := same
  cases valueEq
  have owner := Typing.recordOf_of_get getOwner decoded
  have member' : ms[p.idx.toNat]? = some (.defn d) := by simpa only [Array.getElem?_toList] using member
  rcases stored with stored | collision
  · let root : Root := ⟨cb, blockSelf addressTable p.block ms,
        Ingress.mutsRootOffset ms.toList p.idx.toNat + 1, d.lvls.toNat, d.value⟩
    refine Or.inr ⟨root, ?_, bound, count.symm, ?_⟩
    · simp [valueRoot, record, info, memberRoot, owner, members, member', definitionValue, kind, root]
    · exact ⟨_, blobs, converted, member_self_complete p.block ms d, member_self_keyed p.block ms d,
        fun x bytes belongs => (stored x bytes belongs).1⟩
  · exact Or.inl collision

/-- The actual Defn runtime tag rules out every non-definition record kind, so the selected
value root producer covers every raw constant load accepted by the classifier's delta branch. -/
theorem valueRoot_converted {E : Ixon.Env} {h : Heap F} {a : _root_.Address}
    {c : Ixon.Constant} {v nl ty value flag hint : SourceValue F}
    (record : recordOf E a = some c)
    (shape : v = .construct Core.kciEnum "Defn" [nl, ty, value, flag, hint])
    (raw : Ingress.RawCIRep E h a c v) :
    Ingress.EnvInternalCollision E ∨ ∃ root,
      valueRoot (recordOf E) a = some root ∧ root.levels < 4294967296 ∧
      nl = .field (root.levels : F) ∧ RootConverted (fun x => E.blobs.get? x) root h value := by
  cases info : c.info with
  | defn d => exact valueRoot_converted_defn record info shape raw
  | dPrj p => exact valueRoot_converted_dprj record info shape raw
  | axio ax =>
    rw [Ingress.RawCIRep, info] at raw
    obtain ⟨_, _, _, _, observedShape, _⟩ := raw
    simp [shape] at observedShape
  | quot q =>
    rw [Ingress.RawCIRep, info] at raw
    obtain ⟨_, _, _, _, observedShape, _⟩ := raw
    simp [shape] at observedShape
  | recr rc =>
    rw [Ingress.RawCIRep, info] at raw
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, observedShape, _, _⟩ := raw
    simp [shape] at observedShape
  | iPrj p =>
    rw [Ingress.RawCIRep, info] at raw
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, observedShape, _⟩ := raw
    simp [shape] at observedShape
  | cPrj p =>
    rw [Ingress.RawCIRep, info] at raw
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, observedShape, _⟩ := raw
    simp [shape] at observedShape
  | rPrj p =>
    rw [Ingress.RawCIRep, info] at raw
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, observedShape, _, _⟩ := raw
    simp [shape] at observedShape
  | muts ms =>
    rw [Ingress.RawCIRep, info] at raw
    exact raw.elim

/-- Actual raw payload agreement and the actual universe count identify a delta lookup answer. -/
theorem value_lookup_exact {E : Ixon.Env} {h : Heap F} {a : _root_.Address}
    {c : Ixon.Constant} {v nl ty value flag hint : SourceValue F}
    {Γ : Nat → Core.KExpr} {k : Nat} {R semantic : Core.KExpr} {ps : List Core.KLevel}
    (record : recordOf E a = some c)
    (shape : v = .construct Core.kciEnum "Defn" [nl, ty, value, flag, hint])
    (raw : Ingress.RawCIRep E h a c v)
    (physical : Decl.RawTmExact (Core.keyOf addressTable) 0 Γ h k R semantic value)
    (arity : nl = .field (ps.length : F)) (small : ps.length < 549755813888) :
    Ingress.EnvInternalCollision E ∨
      (ofStore E).valueOf (.id a) ps =
        some (R.instantiateLevelParams (List.range ps.length) ps).eraseMeta := by
  rcases valueRoot_converted record shape raw with collision | ⟨root, selected, bound, count, converted⟩
  · exact Or.inl collision
  · have countEq := congrArg ZMod.val (Value.field.inj (arity.symm.trans count))
    rw [ZMod.val_natCast_of_lt (by change _ < 18446744069414584321; omega),
      ZMod.val_natCast_of_lt (by change _ < 18446744069414584321; omega)] at countEq
    refine Or.inr ?_
    change answer (fun x => E.blobs.get? x) (valueRoot (recordOf E) a) ps = _
    rw [selected]
    exact answer_exact (converted.exact physical) countEq

/-- The two raw payload fields used by declared-type classification. -/
def typeFields : SourceValue F → Option (SourceValue F × SourceValue F)
  | .construct _ _ (count :: type :: _) => some (count, type)
  | _ => none

/-- Every actual raw constant kind supplies its selected type root, exact physical type pointer
and universe count. The recursor type uses its actual empty recur table. -/
theorem typeRoot_converted {E : Ixon.Env} {h : Heap F} {a : _root_.Address}
    {c : Ixon.Constant} {v : SourceValue F}
    (record : recordOf E a = some c) (raw : Ingress.RawCIRep E h a c v) :
    Ingress.EnvInternalCollision E ∨ ∃ root p,
      typeRoot (recordOf E) a = some root ∧ root.levels < 4294967296 ∧
      typeFields v = some (.field (root.levels : F), p) ∧
      RootConverted (fun x => E.blobs.get? x) root h p := by
  cases info : c.info with
  | defn d =>
    rw [Ingress.RawCIRep, info] at raw
    obtain ⟨blobs, stored, bound, tp, vp, hint, shape, converted, _⟩ := raw
    rcases stored with stored | collision
    · let root : Root := ⟨c, soloSelf addressTable a, 0, d.lvls.toNat, d.typ⟩
      refine Or.inr ⟨root, tp, by simp [typeRoot, record, info, root], bound, ?_, ?_⟩
      · cases kind : d.kind <;> simp [typeFields, shape, Ingress.defnValShape, kind, root]
      · exact ⟨_, blobs, converted, solo_self_complete a d, solo_self_keyed a d,
          fun x bytes member => (stored x bytes member).1⟩
    · exact Or.inl collision
  | axio ax =>
    rw [Ingress.RawCIRep, info] at raw
    obtain ⟨blobs, stored, bound, tp, shape, converted⟩ := raw
    rcases stored with stored | collision
    · let root : Root := ⟨c, fun _ => none, 0, ax.lvls.toNat, ax.typ⟩
      refine Or.inr ⟨root, tp, by simp [typeRoot, record, info, root], bound,
        by rw [shape]; rfl, ?_⟩
      exact ⟨[], blobs, converted, (fun i x impossible => by simp at impossible),
        (fun i x m key impossible => by simp at impossible), fun x bytes member => (stored x bytes member).1⟩
    · exact Or.inl collision
  | quot q =>
    rw [Ingress.RawCIRep, info] at raw
    obtain ⟨blobs, stored, bound, tp, shape, converted⟩ := raw
    rcases stored with stored | collision
    · let root : Root := ⟨c, fun _ => none, 0, q.lvls.toNat, q.typ⟩
      refine Or.inr ⟨root, tp, by simp [typeRoot, record, info, root], bound,
        by rw [shape]; rfl, ?_⟩
      exact ⟨[], blobs, converted, (fun i x impossible => by simp at impossible),
        (fun i x m key impossible => by simp at impossible), fun x bytes member => (stored x bytes member).1⟩
    · exact Or.inl collision
  | recr rc =>
    rw [Ingress.RawCIRep, info] at raw
    obtain ⟨blobs, stored, bound, _, _, _, _, _, tp, _, _, _, _, _, shape, converted, _⟩ := raw
    rcases stored with stored | collision
    · let root : Root := ⟨c, soloSelf addressTable a, 0, rc.lvls.toNat, rc.typ⟩
      refine Or.inr ⟨root, tp, by simp [typeRoot, record, info, root], bound,
        by rw [shape]; rfl, ?_⟩
      exact ⟨[], blobs, converted, (fun i x impossible => by simp at impossible),
        (fun i x m key impossible => by simp at impossible), fun x bytes member => (stored x bytes member).1⟩
    · exact Or.inl collision
  | dPrj p =>
    rw [Ingress.RawCIRep, info] at raw
    obtain ⟨_, lc, cb, ms, d, blobs, getOwner, _, _, decoded, _, members, member, stored,
      bound, tp, vp, hint, shape, converted, _⟩ := raw
    have owner := Typing.recordOf_of_get getOwner decoded
    have member' : ms[p.idx.toNat]? = some (.defn d) := by simpa only [Array.getElem?_toList] using member
    rcases stored with stored | collision
    · let root : Root := ⟨cb, blockSelf addressTable p.block ms,
          Ingress.mutsRootOffset ms.toList p.idx.toNat, d.lvls.toNat, d.typ⟩
      refine Or.inr ⟨root, tp, ?_, bound, ?_, ?_⟩
      · simp [typeRoot, record, info, memberRoot, owner, members, member', definitionType, root]
      · cases kind : d.kind <;> simp [typeFields, shape, Ingress.defnValShape, kind, root]
      · exact ⟨_, blobs, converted, member_self_complete p.block ms d, member_self_keyed p.block ms d,
          fun x bytes belongs => (stored x bytes belongs).1⟩
    · exact Or.inl collision
  | iPrj p =>
    rw [Ingress.RawCIRep, info] at raw
    obtain ⟨_, lc, cb, ms, ind, blobs, getOwner, _, _, decoded, _, members, member, stored,
      bound, _, _, _, _, tp, _, _, _, _, shape, converted⟩ := raw
    have owner := Typing.recordOf_of_get getOwner decoded
    have member' : ms[p.idx.toNat]? = some (.indc ind) := by simpa only [Array.getElem?_toList] using member
    rcases stored with stored | collision
    · let root : Root := ⟨cb, blockSelf addressTable p.block ms,
          Ingress.mutsRootOffset ms.toList p.idx.toNat, ind.lvls.toNat, ind.typ⟩
      refine Or.inr ⟨root, tp, ?_, bound, by rw [shape]; rfl, ?_⟩
      · simp [typeRoot, record, info, memberRoot, owner, members, member', inductiveType, root]
      · exact ⟨_, blobs, converted, LoadedReads.blockSelf_ok addressTable p.block ms,
          LoadedReads.blockSelf_key addressTable p.block ms, fun x bytes belongs => (stored x bytes belongs).1⟩
    · exact Or.inl collision
  | cPrj p =>
    rw [Ingress.RawCIRep, info] at raw
    obtain ⟨_, _, lc, cb, ms, ind, ct, blobs, getOwner, _, _, decoded, _, members, member, ctor, stored,
      bound, _, _, _, _, tp, _, _, _, _, shape, converted⟩ := raw
    have owner := Typing.recordOf_of_get getOwner decoded
    have member' : ms[p.idx.toNat]? = some (.indc ind) := by simpa only [Array.getElem?_toList] using member
    have ctor' : ind.ctors[p.cidx.toNat]? = some ct := by simpa only [Array.getElem?_toList] using ctor
    rcases stored with stored | collision
    · let root : Root := ⟨cb, blockSelf addressTable p.block ms,
          Ingress.mutsRootOffset ms.toList p.idx.toNat + (1 + p.cidx.toNat), ct.lvls.toNat, ct.typ⟩
      refine Or.inr ⟨root, tp, ?_, bound, by rw [shape]; rfl, ?_⟩
      · simp [typeRoot, record, info, memberRoot, owner, members, member', constructorType, ctor', root]
      · exact ⟨_, blobs, converted, LoadedReads.blockSelf_ok addressTable p.block ms,
          LoadedReads.blockSelf_key addressTable p.block ms, fun x bytes belongs => (stored x bytes belongs).1⟩
    · exact Or.inl collision
  | rPrj p =>
    rw [Ingress.RawCIRep, info] at raw
    obtain ⟨_, lc, cb, ms, rc, blobs, getOwner, _, _, decoded, _, members, member, stored,
      bound, _, _, _, _, _, tp, _, _, _, _, _, shape, converted, _⟩ := raw
    have owner := Typing.recordOf_of_get getOwner decoded
    have member' : ms[p.idx.toNat]? = some (.recr rc) := by simpa only [Array.getElem?_toList] using member
    rcases stored with stored | collision
    · let root : Root := ⟨cb, blockSelf addressTable p.block ms,
          Ingress.mutsRootOffset ms.toList p.idx.toNat, rc.lvls.toNat, rc.typ⟩
      refine Or.inr ⟨root, tp, ?_, bound, by rw [shape]; rfl, ?_⟩
      · simp [typeRoot, record, info, memberRoot, owner, members, member', recursorType, root]
      · exact ⟨[], blobs, converted, (fun i x impossible => by simp at impossible),
          (fun i x m key impossible => by simp at impossible), fun x bytes belongs => (stored x bytes belongs).1⟩
    · exact Or.inl collision
  | muts ms =>
    rw [Ingress.RawCIRep, info] at raw
    exact raw.elim

/-- Actual count and type-pointer agreement identify every declared-type dictionary answer. -/
theorem type_lookup_exact {E : Ixon.Env} {h : Heap F} {a : _root_.Address}
    {c : Ixon.Constant} {v typePtr : SourceValue F}
    {Γ : Nat → Core.KExpr} {k : Nat} {R semantic : Core.KExpr} {ps : List Core.KLevel}
    (record : recordOf E a = some c) (raw : Ingress.RawCIRep E h a c v)
    (physical : Decl.RawTmExact (Core.keyOf addressTable) 0 Γ h k R semantic typePtr)
    (fields : typeFields v = some (.field (ps.length : F), typePtr))
    (small : ps.length < 549755813888) :
    Ingress.EnvInternalCollision E ∨
      (ofStore E).typeOf (.id a) ps =
        some (R.instantiateLevelParams (List.range ps.length) ps).eraseMeta := by
  rcases typeRoot_converted record raw with collision | ⟨root, p, selected, bound, rootFields, converted⟩
  · exact Or.inl collision
  · obtain ⟨count, samePointer⟩ := Prod.mk.inj (Option.some.inj (fields.symm.trans rootFields))
    cases samePointer
    have countEq := congrArg ZMod.val (Value.field.inj count)
    rw [ZMod.val_natCast_of_lt (by change _ < 18446744069414584321; omega),
      ZMod.val_natCast_of_lt (by change _ < 18446744069414584321; omega)] at countEq
    refine Or.inr ?_
    change answer (fun x => E.blobs.get? x) (typeRoot (recordOf E) a) ps = _
    rw [selected]
    exact answer_exact (converted.exact physical) countEq

/-- The actual helper returns the raw payload's second field and changes no heap. -/
theorem const_type_fields {v r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (observed : ObsFn Core.W "KernelInfer::const_type_of" [v] h r h' calls) :
    ∃ count, typeFields v = some (count, r) ∧ h' = h := by
  match Obs.«KernelInfer::const_type_of».obs observed with
  | .Axiom (hv15 := value) (he35 := result) (he36 := heap) ..
  | .Defn (hv43 := value) (he75 := result) (he76 := heap) ..
  | .Thm (hv83 := value) (he103 := result) (he104 := heap) ..
  | .Opaque (hv111 := value) (he137 := result) (he138 := heap) ..
  | .Quot (hv145 := value) (he165 := result) (he166 := heap) ..
  | .Induct (hv173 := value) (he223 := result) (he224 := heap) ..
  | .Ctor (hv231 := value) (he281 := result) (he282 := heap) ..
  | .Rec (hv289 := value) (he357 := result) (he358 := heap) .. =>
    subst value result heap
    exact ⟨_, rfl, rfl⟩

/-- The actual count helper returns the payload's first field and changes no heap. -/
theorem const_count_fields {v r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (observed : ObsFn Core.W "KernelInfer::const_num_lvls" [v] h r h' calls) :
    ∃ typePtr, typeFields v = some (r, typePtr) ∧ h' = h := by
  match Obs.«KernelInfer::const_num_lvls».obs observed with
  | .Axiom (hv15 := value) (he35 := result) (he36 := heap) ..
  | .Defn (hv43 := value) (he75 := result) (he76 := heap) ..
  | .Thm (hv83 := value) (he103 := result) (he104 := heap) ..
  | .Opaque (hv111 := value) (he137 := result) (he138 := heap) ..
  | .Quot (hv145 := value) (he165 := result) (he166 := heap) ..
  | .Induct (hv173 := value) (he223 := result) (he224 := heap) ..
  | .Ctor (hv231 := value) (he281 := result) (he282 := heap) ..
  | .Rec (hv289 := value) (he357 := result) (he358 := heap) .. =>
    subst value result heap
    exact ⟨_, rfl, rfl⟩

end IxVM.Refinement.GuardRaw
