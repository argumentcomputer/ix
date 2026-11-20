import IxVMRefinement.Guard.Certificate
import IxVMRefinement.Guard.UseReading

/-! # The firing of a projection guard at a use, from the certificates and the reading of a run

The registry's projection step consumes `Core.ProjGuardFires c`, and a prefix carries
`Core.ProjTablesFire` for the tables it stores (`Core/ProjFire.lean`). This file produces both
from the certificates of the stored tables.

* `Core.ProjGuardRunReading`: **the reading of a use**, over the run's own store. Under the
  facts stated before the registry and the registry's induction hypothesis, a run of
  `KernelInfer::proj_guard` at a propositional structure's table, whose parameter and field
  counts are its stored constructor's, is a use observation (`Ix.Kernel.ProjGuardUse`) over the
  raw dictionary of every run store of the run, at the constructor's raw telescope read from that
  store. It is a theorem: `Core.projGuardRunReading` (`Guard.projGuardUse_of_run`).
* `Guard.projTableFires_of_cert_at`, `Guard.projTableFires_of_cert`: one table. Its
  certificate over a store that decodes its records, or over a witness store, and the reading
  give `Core.ProjTableFires` at that store, or at every record store for the witness store: the
  table fires at every context over the store, whatever its limit and call scope. The use is
  read over a store built from the use's own run (`exists_runStore_of_noCollision`), which agrees
  with the certificate's store on what both hold (`runStore_agree`), and the firing follows from
  the two (`fireSem_of_cert_use`).
* `Guard.projTablesFire_of_certs`: every stored table, from the certificates of all of them
  (`Guard.GuardCerts`). No fold uses this form: a prefix keeps the firing itself, and an
  install adds the new table's from its own certificate.
* `Guard.projGuardFires_of_certs`: the firing at one context, directly.

The three premises `Guard.GuardCerts.fireSem` asks beside the observation are discharged from
what the projection step has in hand: the table's well-formedness from the context's facts, the
member's projection record from the step's own load of the structure, and the index from its
being read off a field element.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel)

/-- **What a run of `KernelInfer::proj_guard` at a propositional structure's table is**, read
over the run's own store. The hypotheses are what the projection step has in hand, over the
facts stated before the registry (`ScopedCoreBase`): no firing of any table is assumed at the
context, and the registry's induction hypothesis covers the run's own calls. The conclusion is
the use observation over the raw dictionary of every run store of the run (a store that holds
the records the run hashed, `LoadedReads.RunStore`, `LoadedReads.HashedRecordsStored`). -/
def ProjGuardRunReading : Prop :=
  ∀ (c : ScopedCtx) (hc : ScopedCoreBase c) {calls0 : List (Call F)} (ih : IH c calls0)
    {x_rc x_block r : SourceValue F} {h h' : Heap F} {calls : List (Call F)} {i f : F}
    (hlt0 : calls.length < calls0.length) (good : CoreGood c calls)
    (ev : ObsFn W "KernelInfer::proj_guard" [x_rc, x_block, .field i, .field f] h r h' calls)
    {b : Bytes.Address} (hrc : c.rc h x_rc)
    (hb : Bytes.RepAddressRef addrTy h b x_block)
    (hres : c.FamAt (ixAddr b) (ZMod.val i))
    {cvC : Ix.Kernel.ConstantVal .anon} {nP nF : Nat} {tbl : Ix.Kernel.ProjTable .anon}
    (hctor : c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) =
      some (.ctorInfo cvC nP nF))
    (htbl : c.env.find? (Ix.Kernel.projTableName (c.κ (iprjAddr (ixAddr b) (ZMod.val i)))) =
      some (.projInfo tbl))
    (hprop : Ix.Kernel.Level.isEquiv tbl.structSort .zero = some true)
    (hnP : tbl.numParams = nP) (hnF : tbl.numFields = nF)
    (hf : ZMod.val f < nF) {g : KLevel} (hg : RepKLevel h' g r)
    {E' : Ixon.Env}, LoadedReads.RunStore calls E' → LoadedReads.HashedRecordsStored calls E' →
    ∃ raw, Guard.ctorRaw E' (ixAddr b) (ZMod.val i) 0 = some raw ∧
      Ix.Kernel.ProjGuardUse (GuardRaw.ofStore E') raw cvC.type tbl.numParams (ZMod.val f) g

/-- **The reading of a use holds** (`Guard.projGuardUse_of_run`). -/
theorem projGuardRunReading : ProjGuardRunReading := by
  intro c hc calls0 ih x_rc x_block r h h' calls i f hlt0 good ev b hrc hb hres cvC nP nF tbl
    hctor htbl hprop hnP hnF hf g hg E' hS hcov
  exact Guard.projGuardUse_of_run hc ih hlt0 good ev hrc hb hres hctor htbl hprop hnP hnF hf hg
    hS hcov

end IxVM.Refinement.Core

namespace IxVM.Refinement.Guard

open IxVM.Consistency
open Ix.Kernel (Expr ProjTable ConstantVal ProjGuardCert)

/-- In a store whose records decode exactly, the exact decoding of the stored bytes is the
decoded cache. -/
private theorem recordOf_eq_recordAt_decoded {E : Ixon.Env} (hd : Ingress.EnvDecoded E)
    (a : _root_.Address) : recordOf E a = Ix.Cert.recordAt E a := by
  unfold recordOf Ix.Cert.recordAt
  cases hget : E.consts.get? a with
  | none => rfl
  | some lc =>
    obtain ⟨c, hc, hdec⟩ := hd a lc hget
    change (Ixon.deConstantExact lc.rawBytes).toOption = lc.get?
    rw [hdec, hc]
    rfl

/-- **A table certified over a store that decodes its records fires at every context over that
store**, given the reading of a run: the member's projection record, its constructor's raw
telescope, positional level parameters and the table's certificate, all over the store, give
`Core.ProjTableFires` at the keys of the member and of its first constructor.

The reading is applied at whichever context a use occurs in: the limit and the call scope of
that context are arbitrary. The member the run names is the member the certificate holds
because the store's record at the member's projection address is that member's projection, as
the projection step's own load read it; the use's raw telescope is then the certificate's. -/
theorem projTableFires_of_cert_at (hread : Core.ProjGuardRunReading) {t : Ix.Kernel.RoleTable}
    {E : Ixon.Env} (hdec : Ingress.EnvDecoded E)
    {B : _root_.Address} {i : Nat} {tbl : ProjTable .anon} {cvC : ConstantVal .anon}
    {raw : Expr .anon} (hmem : MemberRecordAt E B i) (hraw : ctorRaw E B i 0 = some raw)
    (hpos : tbl.levelParams = List.range tbl.levelParams.length)
    (cert : ProjGuardCert (GuardRaw.ofStore E) raw cvC.type tbl) :
    Core.ProjTableFires t E (Core.keyOf t (Core.iprjAddr B i)) tbl
      (Core.keyOf t (Core.cprjAddr B i 0)) cvC := by
  intro c ht hE hc htblc hctorc calls0 ih x_rc x_block r h h' calls j f hlt0 good ev b hrc hb
    cvT caps hind cm hrec hinfo hk cvC' nP nF hctor hnP hnF hf g hg us hus hzero hprop
  subst ht
  subst hE
  obtain ⟨nP₀, nF₀, hkc⟩ := hctorc
  have hprop' : Ix.Kernel.Level.isEquiv tbl.structSort .zero = some true := hprop
  have hkI : c.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val j)) =
      Core.keyOf c.t (Core.iprjAddr (Core.ixAddr b) (ZMod.val j)) :=
    c.key_eq (hc.res_of_find hind)
  have hkC : c.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val j) 0) =
      Core.keyOf c.t (Core.cprjAddr (Core.ixAddr b) (ZMod.val j) 0) :=
    c.key_eq (hc.res_of_find hctor)
  have hproj : ∀ cm' : Ixon.Constant,
      recordOf c.E (Core.iprjAddr (Core.ixAddr b) (ZMod.val j)) = some cm' →
      cm'.info = .iPrj ⟨(ZMod.val j).toUInt64, Core.ixAddr b⟩ := by
    intro cm' hcm'
    have h1 : Ix.Cert.recordAt c.E (Core.iprjAddr (Core.ixAddr b) (ZMod.val j)) = some cm' :=
      (recordOf_eq_recordAt_decoded hdec _).symm.trans hcm'
    have h2 : cm = cm' := Option.some.inj (hrec.symm.trans h1)
    rw [← h2]
    exact hinfo
  have haddr : Core.iprjAddr (Core.ixAddr b) (ZMod.val j) = Core.iprjAddr B i :=
    Core.keyOf_inj hc.env.tableWf (hkI.symm.trans hk)
  obtain ⟨hB, hI⟩ := hmem.eq_of_addr hproj (Core.ProjAux.val_toUInt64_toNat j) haddr
  subst hB
  subst hI
  have htbl : c.env.find? (Ix.Kernel.projTableName
      (c.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val j)))) = some (.projInfo tbl) := by
    rw [hk]
    exact htblc
  -- the use, read over a store built from its own run
  obtain ⟨E', hS, hcov⟩ := exists_runStore_of_noCollision good.noCollision
  obtain ⟨raw', hraw', use⟩ := hread c hc ih hlt0 good ev hrc hb (Or.inl ⟨cvT, caps, hind⟩) hctor
    htbl hprop' hnP hnF hf hg hS hcov
  have hagree := runStore_agree hS good.noCollision
  have h1 : c.env.find? (Core.keyOf c.t (Core.cprjAddr (Core.ixAddr b) (ZMod.val j) 0)) =
      some (.ctorInfo cvC' nP nF) := by
    rw [← hkC]
    exact hctor
  rw [hkc] at h1
  have hcv : cvC = cvC' := (Ix.Kernel.ConstantInfo.ctorInfo.inj (Option.some.inj h1)).1
  subst hcv
  have hfT : ZMod.val f < tbl.numFields := by
    rw [hnF]
    exact hf
  have hlp : tbl.levelParams = List.range us.length := by
    rw [hus]
    exact hpos
  refine fireSem_of_cert_use hagree.1 hagree.2 hraw cert hraw' use hfT (fun φ => ?_) hprop
  rw [hlp]
  exact hzero φ

/-- **A certified table fires at every context over a record store for the certificate's
witness store**: the certificate, the member's record and the raw telescope move to the record
store (`Typing.RecordsFor`), where `projTableFires_of_cert_at` applies. -/
theorem projTableFires_of_cert (hread : Core.ProjGuardRunReading) {t : Ix.Kernel.RoleTable}
    {R E : Ixon.Env} (hRE : Typing.RecordsFor R E)
    {B : _root_.Address} {i : Nat} {tbl : ProjTable .anon} {cvC : ConstantVal .anon}
    {raw : Expr .anon} (hmem : MemberRecordAt R B i) (hraw : ctorRaw R B i 0 = some raw)
    (hpos : tbl.levelParams = List.range tbl.levelParams.length)
    (cert : ProjGuardCert (GuardRaw.ofStore R) raw cvC.type tbl) :
    Core.ProjTableFires t E (Core.keyOf t (Core.iprjAddr B i)) tbl
      (Core.keyOf t (Core.cprjAddr B i 0)) cvC :=
  projTableFires_of_cert_at hread hRE.1 (hmem.recordsFor hRE) (ctorRaw_recordsFor hRE hraw) hpos
    (cert.mono (GuardRaw.ofStore_extends_recordsFor hRE))

/-- **The certificates of the stored tables and the reading of a run give the limit-free firing
of every stored table**, over each record store for the witness store. -/
theorem projTablesFire_of_certs (hread : Core.ProjGuardRunReading) {t : Ix.Kernel.RoleTable}
    {R E : Ixon.Env} {env : Ix.Kernel.Env .anon} (hRE : Typing.RecordsFor R E)
    (hcerts : GuardCerts t R env) : Core.ProjTablesFire t E env := by
  intro k tbl htbl hprop
  obtain ⟨B, i, cvC, nP, nF, raw, hk, hmem, hctor, hraw, hpos, cert⟩ := hcerts k tbl htbl hprop
  subst hk
  exact ⟨_, cvC, nP, nF, hctor, projTableFires_of_cert hread hRE hmem hraw hpos cert⟩

/-- **The projection guards fire at every context over a record store for the witness store of
the certificates**, given the reading of a run: the context's limit, call scope and keying are
arbitrary. -/
theorem projGuardFires_of_certs (hread : Core.ProjGuardRunReading) {c : Core.ScopedCtx}
    (hc : Core.ScopedCoreBase c) {R : Ixon.Env} (hRE : Typing.RecordsFor R c.E)
    (hcerts : GuardCerts c.t R c.env) : Core.ProjGuardFires c :=
  (projTablesFire_of_certs hread hRE hcerts).fires hc

end IxVM.Refinement.Guard
