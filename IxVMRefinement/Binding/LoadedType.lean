import IxVMRefinement.StatementRel.LoadedReads

/-! # The type field of a loaded constant, against the reading of its record

A role validation loads the bound record (`Ingress::get_ci`) and reads the loaded constant's
level count and type (`const_num_lvls`, `const_type_of`). For every kind of record, the loaded
value's first two fields are the record's level count and a converted heap term of the record's
type expression, and the reading of the record (`ReadsRecord`) reads the same expression. This
file states that correspondence once for all record kinds, so that a user can turn the
circuit's well-scoping check of the type into the reading's well-scopedness
(`Assembly.validate_expr_well_scoped_spec`) and then the heap term into an exact representation
of an annotation of the reading (`Ingress.rawConvExpr_to_valRepExact`).

* `LoadedTypeReads t E h v a ci₀`: the loaded value `v` has the level count `n` and the type
  pointer `tyPtr` as its first fields; `tyPtr` is the raw conversion of an expression `e` of a
  record `src`, under a recursion table whose keys are the table's, with the conversion's blobs
  in `E`; `e` reads as `ty₀` with level parameters by position; and the reading `ci₀` declares
  `⟨keyOf t a, List.range n, ty₀⟩`, or is a recursor whose type `ty₀` heads a family
  (`familyKey`), or is a pinned quotient constant.
* `loadedTypeReads`: every load of a record a run store holds, with its reading over the store.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.LoadedReads

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency

/-- **The type field of a loaded constant, against the reading of its record** (module
docstring). -/
def LoadedTypeReads (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (h : Heap F) (v : SourceValue F)
    (a : _root_.Address) (ci₀ : Ix.Kernel.ConstantInfo .anon) : Prop :=
  ∃ (tag : String) (n : Nat) (tyPtr : SourceValue F) (rest : List (SourceValue F))
    (src : Ixon.Constant) (recurAddrs : List _root_.Address)
    (blobs : List (_root_.Address × ByteArray))
    (self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))) (e : Ixon.Expr)
    (ty₀ : Ix.Kernel.Expr .anon),
    v = .construct Core.kciEnum tag (.field (n : F) :: tyPtr :: rest) ∧ n < 4294967296 ∧
    Ingress.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs h
      4294967295 e tyPtr ∧
    (∀ x bs, (x, bs) ∈ blobs → E.blobs.get? x = some bs) ∧
    (∀ i x m k, recurAddrs[i]? = some x → self i = some m → m = .ok k → k = Core.keyOf t x) ∧
    (exprReader t (fun x => E.blobs.get? x) src id self).read e = .ok ty₀ ∧
    (ci₀.toConstantVal = ⟨keyOf t a, List.range n, ty₀⟩ ∨
      (∃ (rc : Ixon.Recursor) (kF : Ix.Kernel.Key .anon), familyKey rc ty₀ = some kF) ∨
      ci₀ ∈ (Ix.Kernel.BasisKind.quotK.declsA : List (Ix.Kernel.ConstantInfo .anon)))

private theorem defnValShape_fields (d : Ixon.Definition) (tyPtr valPtr hint : SourceValue F) :
    ∃ (tag : String) (rest : List (SourceValue F)), Ingress.defnValShape d tyPtr valPtr hint =
      .construct Core.kciEnum tag (.field (d.lvls.toNat : F) :: tyPtr :: rest) := by
  unfold Ingress.defnValShape
  cases d.kind <;> exact ⟨_, _, rfl⟩

private theorem defnShape_cv {kind : Ix.DefKind} {cv : Ix.Kernel.ConstantVal .anon}
    {value : Ix.Kernel.Expr .anon} {ci₀ : Ix.Kernel.ConstantInfo .anon}
    (h : DefnShape kind cv value ci₀) : ci₀.toConstantVal = cv := by
  cases kind with
  | defn =>
    obtain ⟨hint, rfl⟩ := h
    rfl
  | thm =>
    have h' : ci₀ = .thmInfo cv value := h
    subst h'
    rfl
  | opaq =>
    have h' : ci₀ = .axiomInfo cv := h
    subst h'
    rfl

section Loads

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E : Ixon.Env}

/-- A block a load decoded is the block the run's store holds there. -/
private theorem block_eq (hS : RunStore calls E) {cs_ld : List (Call F)} {E_ld : Ixon.Env}
    (hload : LoadedBy cs_ld E_ld) (hsub : ∀ cl ∈ cs_ld, cl ∈ calls) {B : _root_.Address}
    {lcB : Ixon.LazyConstant} {cb' cb : Ixon.Constant}
    (hgetB : E_ld.consts.get? B = some lcB) (hexB : Ixon.deConstantExact lcB.rawBytes = .ok cb')
    (hB : recordOf E B = some cb) : cb' = cb := by
  obtain ⟨hhB, haB⟩ := hload.1 B lcB hgetB
  have hrecB : Ix.Cert.recordAt E B = some cb := by
    rw [← hS.recordOf_eq_recordAt]
    exact hB
  exact hS.record_eq hrecB (Core.hashed_mono hsub hhB) haB hexB

private theorem safe_of_member {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {i : Nat}
    {d : Ixon.Definition} (hlogic : InLogic cb) (hmuts : cb.info = .muts ms)
    (hm : ms[i]? = some (.defn d)) : Ix.Kernel.Reader.safetyDecline d = none := by
  have hmem : Ixon.MutConst.defn d ∈ ms.toList :=
    List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hm)
  have hl := hlogic
  unfold InLogic at hl
  rw [hmuts] at hl
  exact hl (.defn d) hmem

/-- **Every load of a record the run's store holds, against the record's reading** (module
docstring). The load's evidence is the record layer's (`Ingress.RawCIRep` over the load's own store,
`Ingress.get_ci_loadedRecords_spec`); the reading is over the run's store. -/
theorem loadedTypeReads (hS : RunStore calls E) {cs_ld : List (Call F)} {E_ld : Ixon.Env}
    {h : Heap F} {a : _root_.Address} {c : Ixon.Constant} {v : SourceValue F}
    {ci₀ : Ix.Kernel.ConstantInfo .anon}
    (hload : LoadedBy cs_ld E_ld) (hsub : ∀ cl ∈ cs_ld, cl ∈ calls)
    (hraw : Ingress.RawCIRep E_ld h a c v)
    (hrd : ReadsRecord t (recordOf E) (fun x => E.blobs.get? x) a c ci₀ c.info) :
    LoadedTypeReads t E h v a ci₀ := by
  unfold Ingress.RawCIRep at hraw
  have hlog : c.info = c.info → InLogic c → InLogic c := fun _ h => h
  generalize hinfo : c.info = info at hraw hrd
  cases info with
  | defn d =>
    obtain ⟨blobs, hb, hlvls, tyPtr, valPtr, hint, rfl, hty_raw, -⟩ := hraw
    obtain ⟨hlogic, ty, value, hty, -, hshape⟩ := hrd
    have hsafe : Ix.Kernel.Reader.safetyDecline d = none := by
      have hl := hlogic
      unfold InLogic at hl
      rw [hinfo] at hl
      exact hl
    have hrecur : Ingress.defnRecurAddrs d a = [] := by
      have hf := (Ingress.defnIsUnsafeCI_eq_false_iff d).mpr hsafe
      simp [Ingress.defnRecurAddrs, hf]
    rw [hrecur] at hty_raw
    obtain ⟨tag, rest, hv⟩ := defnValShape_fields d tyPtr valPtr hint
    exact ⟨tag, d.lvls.toNat, tyPtr, rest, c, [], blobs, soloSelf t a, d.typ, ty, hv, hlvls,
      hty_raw, hS.blob_of_table hload hsub hb, fun _ _ _ _ hx => by simp at hx, hty,
      Or.inl (defnShape_cv hshape)⟩
  | axio ax =>
    obtain ⟨blobs, hb, hlvls, tyPtr, rfl, hty_raw⟩ := hraw
    obtain ⟨-, -, ty, hty, rfl⟩ := hrd
    exact ⟨_, ax.lvls.toNat, tyPtr, _, c, [], blobs, fun _ => none, ax.typ, ty, rfl, hlvls,
      hty_raw, hS.blob_of_table hload hsub hb, fun _ _ _ _ hx => by simp at hx, hty,
      Or.inl rfl⟩
  | quot q =>
    obtain ⟨blobs, hb, hlvls, tyPtr, rfl, hty_raw⟩ := hraw
    obtain ⟨ty, hty, -, hslot⟩ := hrd
    exact ⟨_, q.lvls.toNat, tyPtr, _, c, [], blobs, fun _ => none, q.typ, ty, rfl, hlvls,
      hty_raw, hS.blob_of_table hload hsub hb, fun _ _ _ _ hx => by simp at hx, hty,
      Or.inr (Or.inr (List.mem_of_getElem? hslot))⟩
  | recr rc =>
    obtain ⟨blobs, hb, hlvls, -, -, -, -, -, tyPtr, rulesPtr, blkPtr, b, -, -, rfl, hty_raw, -⟩ :=
      hraw
    obtain ⟨-, tyP, ty, kF, -, -, -, -, -, -, -, -, -, hP, hfam, -⟩ := hrd
    exact ⟨_, rc.lvls.toNat, tyPtr, _, c, [], blobs, soloSelf t a, rc.typ, tyP, rfl, hlvls,
      hty_raw, hS.blob_of_table hload hsub hb, fun _ _ _ _ hx => by simp at hx, hP,
      Or.inr (Or.inl ⟨rc, kF, hfam⟩)⟩
  | dPrj p =>
    obtain ⟨-, lcB, cb', ms', d', blobs, hgetB, -, -, hexB, -, hcb', hms', hb, raw⟩ := hraw
    obtain ⟨cb, ms, d, ⟨hB, hmuts, hm, -, -, hlogic⟩, ty, value, hty, -, hshape⟩ := hrd
    obtain rfl := block_eq hS hload hsub hgetB hexB hB
    obtain rfl : ms' = ms := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hmuts)
    have hm' : ms'[p.idx.toNat]? = some (.defn d') := by
      rw [← Array.getElem?_toList]
      exact hms'
    obtain rfl : d' = d := Ixon.MutConst.defn.inj (Option.some.inj (hm'.symm.trans hm))
    obtain ⟨hlvls, tyPtr, valPtr, hint, rfl, hty_raw, -⟩ := raw
    have hrecur : Ingress.defnMemberRecurAddrs d' p.block ms'.toList = [] := by
      have hf := (Ingress.defnIsUnsafeCI_eq_false_iff d').mpr (safe_of_member hlogic hmuts hm)
      simp [Ingress.defnMemberRecurAddrs, hf]
    rw [hrecur] at hty_raw
    obtain ⟨tag, rest, hv⟩ := defnValShape_fields d' tyPtr valPtr hint
    exact ⟨tag, d'.lvls.toNat, tyPtr, rest, cb', [], blobs, blockSelf t p.block ms', d'.typ, ty,
      hv, hlvls, hty_raw, hS.blob_of_table hload hsub hb, fun _ _ _ _ hx => by simp at hx, hty,
      Or.inl (defnShape_cv hshape)⟩
  | iPrj p =>
    obtain ⟨-, lcB, cb', ms', ind', blobs, hgetB, -, -, hexB, -, hcb', hms', hb, raw⟩ := hraw
    obtain ⟨cb, ms, ind, ⟨hB, hmuts, hm, -, -, -⟩, ty, caps, hty, rfl⟩ := hrd
    obtain rfl := block_eq hS hload hsub hgetB hexB hB
    obtain rfl : ms' = ms := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hmuts)
    have hm' : ms'[p.idx.toNat]? = some (.indc ind') := by
      rw [← Array.getElem?_toList]
      exact hms'
    obtain rfl : ind' = ind := Ixon.MutConst.indc.inj (Option.some.inj (hm'.symm.trans hm))
    obtain ⟨hlvls, -, -, -, -, tyPtr, blkPtr, b, -, -, rfl, hty_raw⟩ := raw
    exact ⟨_, ind'.lvls.toNat, tyPtr, _, cb', Ingress.blockRecurAddrs p.block ms'.toList, blobs,
      blockSelf t p.block ms', ind'.typ, ty, rfl, hlvls, hty_raw,
      hS.blob_of_table hload hsub hb, blockSelf_key t p.block ms', hty, Or.inl rfl⟩
  | cPrj p =>
    obtain ⟨-, -, lcB, cb', ms', ind', ct', blobs, hgetB, -, -, hexB, -, hcb', hms', hct', hb,
      raw⟩ := hraw
    obtain ⟨cb, ms, ind, ct, hB, hmuts, hm, hct, -, -, -, -, ty, hty, rfl⟩ := hrd
    obtain rfl := block_eq hS hload hsub hgetB hexB hB
    obtain rfl : ms' = ms := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hmuts)
    have hm' : ms'[p.idx.toNat]? = some (.indc ind') := by
      rw [← Array.getElem?_toList]
      exact hms'
    obtain rfl : ind' = ind := Ixon.MutConst.indc.inj (Option.some.inj (hm'.symm.trans hm))
    have hct'' : ind'.ctors[p.cidx.toNat]? = some ct' := by
      rw [← Array.getElem?_toList]
      exact hct'
    obtain rfl : ct' = ct := Option.some.inj (hct''.symm.trans hct)
    obtain ⟨hlvls, -, -, -, -, tyPtr, blkPtr, b, -, -, rfl, hty_raw⟩ := raw
    exact ⟨_, ct'.lvls.toNat, tyPtr, _, cb', Ingress.blockRecurAddrs p.block ms'.toList, blobs,
      blockSelf t p.block ms', ct'.typ, ty, rfl, hlvls, hty_raw,
      hS.blob_of_table hload hsub hb, blockSelf_key t p.block ms', hty, Or.inl rfl⟩
  | rPrj p =>
    obtain ⟨-, lcB, cb', ms', rc', blobs, hgetB, -, -, hexB, -, hcb', hms', hb, raw⟩ := hraw
    obtain ⟨cb, ms, rc, ⟨hB, hmuts, hm, -, -, -⟩, tyP, ty, kF, -, -, -, -, -, -, -, -, -, hP,
      hfam, -⟩ := hrd
    obtain rfl := block_eq hS hload hsub hgetB hexB hB
    obtain rfl : ms' = ms := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hmuts)
    have hm' : ms'[p.idx.toNat]? = some (.recr rc') := by
      rw [← Array.getElem?_toList]
      exact hms'
    obtain rfl : rc' = rc := Ixon.MutConst.recr.inj (Option.some.inj (hm'.symm.trans hm))
    obtain ⟨hlvls, -, -, -, -, -, tyPtr, rulesPtr, blkPtr, b, -, -, rfl, hty_raw, -⟩ := raw
    exact ⟨_, rc'.lvls.toNat, tyPtr, _, cb', [], blobs, blockSelf t p.block ms', rc'.typ, tyP,
      rfl, hlvls, hty_raw, hS.blob_of_table hload hsub hb, fun _ _ _ _ hx => by simp at hx, hP,
      Or.inr (Or.inl ⟨rc', kF, hfam⟩)⟩
  | muts ms => exact hraw.elim

end Loads

end IxVM.Refinement.LoadedReads
