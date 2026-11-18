import IxVMRefinement.Guard.Certificate

/-! # The firing of a projection guard at a use, from the certificates and the use reading

The projection step of the registry (`Core.infer_proj_common`) owes, at a projection out of a
propositional structure, the rules tier's firing condition `Ix.Kernel.Rules.FireSem` of the
table entry at the use's levels.

* `Core.ProjGuardFires c` states that debt at one context, in the vocabulary of the registry:
  under the registry's induction hypothesis at the context, a run of `KernelInfer::proj_guard`
  for a stored member whose table the environment stores, whose returned level is zero at the
  use's levels, fires the entry. It mentions no witness store, no raw dictionary and no
  certificate, so it can be stated below them. Its hypotheses are what the projection step has
  in hand: the member's stored inductive, the member's projection record as the step's own load
  of the structure read it, the stored constructor and table, and the zero premise.
* `Guard.projGuardFires_of_certs` produces it at every context, whatever its limit and call
  scope, from the carried certificates (`Guard.GuardCerts`), the use reading
  (`Core.ProjGuardUseReading`, a statement) and a store with no blob and record of different
  bytes at one address. The three premises `Guard.GuardCerts.fireSem` asks beside the
  observation are discharged here from the hypotheses above: the table's well-formedness from
  the context's facts, the projection record from the step's own load, and the index from its
  being read off a field element.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel)

/-- **The projection guards fire at the context `c`**: for every run of
`KernelInfer::proj_guard` shorter than the calls the registry's induction hypothesis covers, at
member `i` of the block `b` whose inductive, first constructor and projection table the
environment stores and whose projection record the store holds, a returned level that is zero at
the use's levels gives the rules tier's firing condition of the table's entry at those levels.

This is what the registry's projection step consumes. It is relative to the context (its
environment, keying, limit and call scope) through the induction hypothesis, so it is produced
at each context from facts that mention none of them (`Guard.projGuardFires_of_certs`). -/
def ProjGuardFires (c : ScopedCtx) : Prop :=
  ∀ {calls0 : List (Call F)} (ih : IH c calls0)
    {x_rc x_block r : SourceValue F} {h h' : Heap F} {calls : List (Call F)} {i f : F}
    (hlt0 : calls.length < calls0.length) (good : CoreGood c calls)
    (ev : ObsFn W "KernelInfer::proj_guard" [x_rc, x_block, .field i, .field f] h r h' calls)
    {b : Bytes.Address} (hrc : c.rc h x_rc)
    (hb : Bytes.RepAddressRef addrTy h b x_block)
    {cvT : Ix.Kernel.ConstantVal .anon} {caps : Ix.Kernel.IndCaps .anon}
    (hind : c.env.find? (c.κ (iprjAddr (ixAddr b) (ZMod.val i))) = some (.indInfo cvT caps))
    {cm : Ixon.Constant}
    (hrec : Ix.Cert.recordAt c.E (iprjAddr (ixAddr b) (ZMod.val i)) = some cm)
    (hinfo : cm.info = .iPrj ⟨(ZMod.val i).toUInt64, ixAddr b⟩)
    {cvC : Ix.Kernel.ConstantVal .anon} {nP nF : Nat} {tbl : Ix.Kernel.ProjTable .anon}
    (hctor : c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) =
      some (.ctorInfo cvC nP nF))
    (htbl : c.env.find? (Ix.Kernel.projTableName (c.κ (iprjAddr (ixAddr b) (ZMod.val i)))) =
      some (.projInfo tbl))
    (hnF : tbl.numFields = nF) (hf : ZMod.val f < nF) {g : KLevel} (hg : RepKLevel h' g r)
    {us : List KLevel} (hus : us.length = tbl.levelParams.length)
    (hzero : ∀ φ : Ix.Kernel.LevelParam → Nat,
      Ix.Kernel.Level.eval φ (Ix.Kernel.Level.subst (List.range us.length) us g) = 0),
    Ix.Kernel.Rules.FireSem (tbl.entry (ZMod.val f)) us

end IxVM.Refinement.Core

namespace IxVM.Refinement.Guard

open IxVM.Consistency

/-- In a store whose records decode exactly, the exact decoding of the stored bytes is the
decoded cache. -/
private theorem recordOf_eq_recordAt_decoded {E : Ixon.Env} (hd : L1.EnvDecoded E)
    (a : _root_.Address) : recordOf E a = Ix.Cert.recordAt E a := by
  unfold recordOf Ix.Cert.recordAt
  cases hget : E.consts.get? a with
  | none => rfl
  | some lc =>
    obtain ⟨c, hc, hdec⟩ := hd a lc hget
    change (Ixon.deConstantExact lc.rawBytes).toOption = lc.get?
    rw [hdec, hc]
    rfl

/-- **The projection guards fire at every context over a record store for the witness store of
the certificates**, given the use reading. The context's limit, call scope and keying are
arbitrary; the store is constrained by `Typing.RecordsFor` and by holding no blob and record of
different bytes at one address (the alternative the use reading leaves).

The reading turns the run into a use observation over the context's store; the certificate of
the table and that observation give the firing condition (`GuardCerts.fireSem`). The member the
run names is the member the certificate holds because the store's record at the member's
projection address is that member's projection, as the projection step's own load read it. -/
theorem projGuardFires_of_certs (hread : Core.ProjGuardUseReading) {c : Core.ScopedCtx}
    (hc : Core.ScopedCoreFacts c) {R : Ixon.Env} (hRE : Typing.RecordsFor R c.E)
    (hcerts : GuardCerts c.t R c.env) (hnocol : ¬ L1.EnvInternalCollision c.E) :
    Core.ProjGuardFires c := by
  intro calls0 ih x_rc x_block r h h' calls i f hlt0 good ev b hrc hb cvT caps hind cm hrec hinfo
    cvC nP nF tbl hctor htbl hnF hf g hg us hus hzero
  intro hprop
  have hprop' : Ix.Kernel.Level.isEquiv tbl.structSort .zero = some true := hprop
  have hkI : c.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)) =
      Core.keyOf c.t (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)) :=
    c.key_eq (hc.res_of_find hind)
  have hkC : c.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) 0) =
      Core.keyOf c.t (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) 0) :=
    c.key_eq (hc.res_of_find hctor)
  rcases hread c hc ih hlt0 good ev hrc hb (Or.inl ⟨cvT, caps, hind⟩) hctor htbl hprop' hf hg with
    hcol | ⟨raw, hraw, use⟩
  · exact absurd hcol hnocol
  · have htbl' : c.env.find? (Ix.Kernel.projTableName
        (Core.keyOf c.t (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)))) =
        some (.projInfo tbl) := by
      rw [← hkI]
      exact htbl
    have hctor' : c.env.find? (Core.keyOf c.t (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) 0)) =
        some (.ctorInfo cvC nP nF) := by
      rw [← hkC]
      exact hctor
    have hproj : ∀ cm' : Ixon.Constant,
        recordOf c.E (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)) = some cm' →
        cm'.info = .iPrj ⟨(ZMod.val i).toUInt64, Core.ixAddr b⟩ := by
      intro cm' hcm'
      have h1 : Ix.Cert.recordAt c.E (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)) = some cm' :=
        (recordOf_eq_recordAt_decoded hRE.1 _).symm.trans hcm'
      have h2 : cm = cm' := Option.some.inj (hrec.symm.trans h1)
      rw [← h2]
      exact hinfo
    have hfT : ZMod.val f < tbl.numFields := by
      rw [hnF]
      exact hf
    exact GuardCerts.fireSem hcerts hRE hc.env.tableWf htbl' hctor' hproj
      (Core.ProjAux.val_toUInt64_toNat i) hraw use hfT hus hzero hprop

end IxVM.Refinement.Guard
