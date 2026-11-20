import IxVMRefinement.StatementRel.LoadedReads

/-! # A later load of a definition record represents an annotation of the same reading

A record's reading (`ReadsIn`) is fixed by the record, the role table and the store's blobs:
it is established once, with its well-scopedness, when the record is checked. This module
shows what any other `get_ci` on the record's address returns, for calls that hash no
collision with the store (the calls need not be among those the store was built from): the
pointer holds a definition whose type and value are annotations of that one reading, under
every reducibility hint.

What it does not show is that the annotations are the same from one load to the next: the
annotated terms are given per load. With that (determinism of the circuit's annotation of a
record), a later load represents the very constant a step stored.
-/

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.LoadedReads

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency

/-- **Literal bytes a load hashed agree with the store's blobs**, where the calls hash no
collision with the store: at an address the store holds a blob, the load hashed those bytes. -/
theorem blobReadAgreement_of_noCollision {E : Ixon.Env} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs)
    {blobs : List (_root_.Address × ByteArray)} (hhp : Ingress.HashedPairs cs blobs)
    (t : Ix.Kernel.RoleTable) :
    Ingress.BlobReadAgreement (readCtx t (fun x => E.blobs.get? x)).blob blobs := by
  intro x observed hmem declared hfound
  obtain ⟨hhx, hxa⟩ := hhp (x, observed) hmem
  apply Classical.byContradiction
  intro hne
  exact hnc (.inl ⟨x, declared, observed, .inl (.inr (.inl hfound)), hhx, hne, hxa⟩)

/-- **Any load of a standalone definition, theorem or opaque record represents annotations
of the record's reading.** The store `E` holds the record `c` at the address, with its exact
decoding as cache, in Lean's logic; `ty₀`, `val₀` are the readings of its type and value in
the reading context over `E`'s blobs, well scoped (all of which the record's own check
gives: `checkedAtFull_defn`). Then for a `get_ci` at the address in calls that hash no
collision with `E`, there are annotations `ty'`, `val'` of `ty₀`, `val₀` such that the
returned pointer represents the constant with type `ty'` and value `val'`, under every
hint. -/
theorem get_ci_defn_rep {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ()) {E : Ixon.Env}
    (hdec : Ingress.EnvDecoded E) {cs : List (Call F)} (hbound : Bounded cs)
    (hnc : ¬ View.HashedCollision { env := E } [] cs) {a : Aiur.Library.Bytes.Address}
    {addr ptr : SourceValue F} {h h' : Heap F}
    (ha : Aiur.Library.Bytes.RepAddressRef Core.addrTy h a addr)
    (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs) {c : Ixon.Constant}
    {d : Ixon.Definition} (hrec : Ix.Cert.recordAt E (Core.ixAddr a) = some c)
    (hinfo : c.info = .defn d) (hlogic : InLogic c) {ty₀ val₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) c id
      (soloSelf t (Core.ixAddr a))).read d.typ = .ok ty₀)
    (hval : (exprReader t (fun x => E.blobs.get? x) c id
      (soloSelf t (Core.ixAddr a))).read d.value = .ok val₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true)
    (hval_lbb : val₀.looseBVarsBounded 0 = true)
    (hval_def : val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true) :
    ∃ ty' val' : Ix.Kernel.Expr .anon, Annotates ty' ty₀ ∧ Annotates val' val₀ ∧
      ∀ hn : Ix.Kernel.ReducibilityHint,
        Core.CIPtrRep (Core.keyOf t) h' ptr
          (defnConst d.kind ⟨keyOf t (Core.ixAddr a), List.range d.lvls.toNat, ty'⟩ val' hn) := by
  obtain ⟨-, rawBytes, c', blobs, hh, haddr, hex, -, -, hhp, hres⟩ := Ingress.get_ci_spec hbound ha ev
  have hc : c' = c := by
    unfold Ix.Cert.recordAt at hrec
    cases hget : E.consts.get? (Core.ixAddr a) with
    | none =>
      rw [hget] at hrec
      cases hrec
    | some lc =>
      rw [hget] at hrec
      obtain ⟨c₀, hc₀, hce₀⟩ := hdec _ lc hget
      have hb : rawBytes = lc.rawBytes := Core.load_escape hget hnc rawBytes hh haddr
      rw [hb, hce₀] at hex
      have h1 : c₀ = c' := Except.ok.inj hex
      have h2 : lc.get? = some c := hrec
      rw [hc₀] at h2
      rw [← h1]
      exact Option.some.inj h2
  subst hc
  unfold Ingress.GetCIRawResult at hres
  rw [hinfo] at hres
  obtain ⟨v, hld, raw⟩ := hres
  have hsafe : Ix.Kernel.Reader.safetyDecline d = none := by
    have hl := hlogic
    unfold InLogic at hl
    rw [hinfo] at hl
    exact hl
  have hrecur : Ingress.defnRecurAddrs d (Core.ixAddr a) = [] := by
    have hf := (Ingress.defnIsUnsafeCI_eq_false_iff d).mpr hsafe
    simp [Ingress.defnRecurAddrs, hf]
  rw [hrecur] at raw
  obtain ⟨hnlvls, tyPtr, valPtr, hint, rfl, rty, rval⟩ := raw
  have hagree := blobReadAgreement_of_noCollision hnc hhp t
  have hkeyAt := readCtx_keyAt_inv ht (fun x => E.blobs.get? x)
  have hty' : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t (fun x => E.blobs.get? x)) c'
      (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat))
      (soloSelf t (Core.ixAddr a))).read d.typ = .ok ty₀ := by
    rw [Assembly.recParam_range]
    exact hty
  have hval' : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t (fun x => E.blobs.get? x)) c'
      (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat))
      (soloSelf t (Core.ixAddr a))).read d.value = .ok val₀ := by
    rw [Assembly.recParam_range]
    exact hval
  obtain ⟨ty', hty_ann, hty_tm⟩ :=
    rty.toTmCExact_of_blobAgreement (recurAddrs := []) (κ := Core.keyOf t)
      (ps := List.range d.lvls.toNat) (by simp) (by simpa using hnlvls) hkeyAt
      (fun _ _ _ _ hx => by simp at hx) hagree hty' hty_lbb hty_def
  obtain ⟨val', hval_ann, hval_tm⟩ :=
    rval.toTmCExact_of_blobAgreement (recurAddrs := []) (κ := Core.keyOf t)
      (ps := List.range d.lvls.toNat) (by simp) (by simpa using hnlvls) hkeyAt
      (fun _ _ _ _ hx => by simp at hx) hagree hval' hval_lbb hval_def
  refine ⟨ty', val', hty_ann, hval_ann, fun hn => ⟨_, hld, ?_⟩⟩
  have hlen : d.lvls.toNat = (List.range d.lvls.toNat).length := by simp
  have hvr : Core.ValRep (Core.keyOf t) h' (.field (d.lvls.toNat : F)) tyPtr
      ⟨keyOf t (Core.ixAddr a), List.range d.lvls.toNat, ty'⟩ :=
    ⟨congrArg (fun n : Nat => Value.field (n : F)) hlen,
      by simpa using hnlvls, by simp, hty_tm.toTmC⟩
  cases hk : d.kind with
  | defn =>
    simp only [Ingress.defnValShape, hk]
    exact .defn hvr hval_tm.toTmC
  | thm =>
    simp only [Ingress.defnValShape, hk]
    exact .thm hvr hval_tm.toTmC
  | opaq =>
    simp only [Ingress.defnValShape, hk]
    exact .opaq hvr

end IxVM.Refinement.LoadedReads
