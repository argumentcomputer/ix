import IxVMRefinement.StatementRel.LoadedReadsCanon

/-! # The reload of a quotient record

The analogue of the axiom case (`get_ci_axio_canon`, `reloadsAs_axio`) for a quotient record
(`Ixon.ConstantInfo.quot`): the circuit converts its type at root `0` with no `recur` address
(`Convert::convert_quotient`, traced by `L1.convert_quotient_trace_spec`), and the loaded value
is `Quot [nl, ty, kind]`. A kernel constant `ci` is represented by it when its constant value is
the record's level count and the canonical annotation of the reading, and its kind matches the
record's (`Core.QuotKindRep`: the type former is an inductive, `Quot.mk` a constructor,
`Quot.lift` and `Quot.ind` recursors).

* `quotKindOk`, `quotKindRep_of_ok`: the kind match, decided.
* `get_ci_quot_canon`: every load of a held quotient record represents every such constant,
  under the table's keying and under the keying of a prefix that stores the references the
  record uses.
* `reloadsAs_quot`: `Decl.ReloadsAs` for such a constant.
-/

namespace IxVM.Refinement.LoadedReads

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency

/-- The kind of a quotient record matches a kernel constant's shape. -/
def quotKindOk : Ix.QuotKind → Ix.Kernel.ConstantInfo .anon → Bool
  | .type, .indInfo _ _ => true
  | .ctor, .ctorInfo _ _ _ => true
  | .lift, .recInfo _ _ _ _ => true
  | .ind, .recInfo _ _ _ _ => true
  | _, _ => false

theorem quotKindRep_of_ok {k : Ix.QuotKind} {ci : Ix.Kernel.ConstantInfo .anon}
    (h : quotKindOk k ci = true) : Core.QuotKindRep (L1.repQuotKindVal k) ci := by
  cases k <;> cases ci <;> simp [quotKindOk] at h <;> simp [Core.QuotKindRep, L1.repQuotKindVal]

section Quot

variable {t : Ix.Kernel.RoleTable}

/-- **Every load of a held quotient record represents the constants of its kind with the
canonical annotation of its read type.** The store `E` holds the record `c` at the address
(exact decoding); `ty₀` is the reading of its type over `E`'s blobs, well scoped. Then for a
`get_ci` at the address in calls that hash no collision with `E`, the canonical annotation of
the reading (at root `0`) is defined, and the returned pointer represents every constant whose
value is the record's level count and that annotation and whose kind is the record's: under
the table's keying, and under the keying of any prefix that stores the references the record
uses. -/
theorem get_ci_quot_canon (ht : t.check = .ok ()) {E : Ixon.Env} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) {a : Aiur.Library.Bytes.Address}
    {addr ptr : SourceValue F} {h h' : Heap F}
    (ha : Aiur.Library.Bytes.RepAddressRef Core.addrTy h a addr)
    (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs) {c : Ixon.Constant}
    {q : Ixon.Quotient} (hrec : recordOf E (Core.ixAddr a) = some c)
    (hinfo : c.info = .quot q) {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) c id (fun _ => none)).read q.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range q.lvls.toNat) = true) :
    ∃ ty' : Ix.Kernel.Expr .anon,
      canonAnn c (List.range q.lvls.toNat) 0 q.typ ty₀ = some ty' ∧ Annotates ty' ty₀ ∧
      ∀ ci : Ix.Kernel.ConstantInfo .anon,
        ci.toConstantVal = ⟨keyOf t (Core.ixAddr a), List.range q.lvls.toNat, ty'⟩ →
        Core.QuotKindRep (L1.repQuotKindVal q.kind) ci →
        Core.CIPtrRep (Core.keyOf t) h' ptr ci ∧
        ∀ (env : Ix.Kernel.Env .anon) (lim : Option Nat), Decl.UsedRefsStored t env c →
          Core.CIPtrRep (Core.Ctx.stored ⟨E, env, t, lim⟩).κ h' ptr ci := by
  obtain ⟨rawBytes, c', hh, haddr, hex, hres⟩ := L1.get_ci_trace_spec ha ev
  obtain ⟨lc, hget, hdec⟩ := recordOf_inv hrec
  have hb : rawBytes = lc.rawBytes := Core.load_escape hget hnc rawBytes hh haddr
  have hc : c = c' := by
    rw [hb, hdec] at hex
    exact Except.ok.inj hex
  subst hc
  unfold L1.GetCITraceResult at hres
  rw [hinfo] at hres
  obtain ⟨blobs, tree, v, hhp, built, hld, htr⟩ := hres
  obtain ⟨hnlvls, tyPtr, plan, hv, rty, hp, hl⟩ := htr
  subst hv
  have hagree := blobReadAgreement_of_noCollision hnc hhp t
  obtain ⟨ty', hcT, hannT, htmT⟩ :=
    annotation_canon ht hnlvls hagree rty built hp hl hty hty_lbb hty_def
  have heT : ∀ i, i ∈ exprRefIdxs q.typ → i ∈ usedRefIdxs c := by
    intro i hi
    unfold usedRefIdxs
    rw [hinfo]
    exact List.mem_append_right _ hi
  refine ⟨ty', hcT, hannT, fun ci hcv hk => ⟨⟨_, hld, .quot ?_ hk⟩,
    fun env lim hstored => ⟨_, hld, .quot ?_ hk⟩⟩⟩
  · rw [hcv]
    exact valRep_range hnlvls htmT
  · rw [hcv]
    exact valRep_range hnlvls
      (Decl.tmC_stored_of_usedRefs (E₀ := E) (lim := lim) rty heT hstored htmT)

/-- **A quotient constant with the canonical annotation of the record's read type reloads** at
every store `E'` that holds the record `c` at `a` (exact decoding) and over whose blobs the
record's type reads as `ty₀`, under the keying of any prefix `env` that stores the references
the record uses, when the constant's kind is the record's. -/
theorem reloadsAs_quot (ht : t.check = .ok ()) {E' : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {a : _root_.Address} {c : Ixon.Constant} {q : Ixon.Quotient}
    (hrec : recordOf E' a = some c) (hinfo : c.info = .quot q)
    {ty₀ ty' : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E'.blobs.get? x) c id (fun _ => none)).read q.typ =
      .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range q.lvls.toNat) = true)
    (hstored : Decl.UsedRefsStored t env c)
    (hcn : canonAnn c (List.range q.lvls.toNat) 0 q.typ ty₀ = some ty')
    {ci : Ix.Kernel.ConstantInfo .anon}
    (hcv : ci.toConstantVal = ⟨keyOf t a, List.range q.lvls.toNat, ty'⟩)
    (hk : quotKindOk q.kind ci = true) :
    Decl.ReloadsAs E' t env ci := by
  intro addr ptr h h' cs a' ev hgood ha hkey
  have hk' : Core.keyOf t (Core.ixAddr a') = Core.keyOf t a := by
    rw [hkey]
    exact congrArg Ix.Kernel.ConstantVal.name hcv
  have haddr : Core.ixAddr a' = a := Assembly.keyOf_injective ht hk'
  subst haddr
  obtain ⟨ty'', hcT', -, hrep⟩ :=
    get_ci_quot_canon ht hgood.1 ha ev hrec hinfo hty hty_lbb hty_def
  have e1 : ty'' = ty' := Option.some.inj (hcT'.symm.trans hcn)
  subst e1
  exact (hrep ci hcv (quotKindRep_of_ok hk)).2 env none hstored

end Quot

end IxVM.Refinement.LoadedReads
