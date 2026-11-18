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
* `Core.ProjTableFires`, `Core.ProjTablesFire`: the same with no context fixed, one stored
  table at a time, at every context over a role table and a store that stores the table and its
  constructor. This form names no limit; it is kept by every step of the environment that
  keeps the lookups (`ProjTablesFire.step`), and it gives the firing at any context that stores
  the tables (`ProjTablesFire.fires`). `Guard.projTableFires_of_cert` produces it for one
  table from that table's certificate and the use reading, and `Guard.projTablesFire_of_certs`
  for every stored table from the carried certificates.
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

/-! ## The same, with no context: one stored table at every context -/

/-- **The stored projection table `tbl` of the structure at the key `k`, whose constructor
`cvC` is stored at `kc`, fires at every context** over the role table `t` and the store `E`:
at each context that stores the table and that constructor and has its core facts, a run of
`KernelInfer::proj_guard` at a member whose key is `k` fires the table's entry, as in
`ProjGuardFires`.

No limit, call scope or environment is fixed: the statement is kept by every extension of the
environment and by every change of limit. It is what a certificate and the use reading give of
one table (`Guard.projTableFires_of_cert`). -/
def ProjTableFires (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (k : KKey)
    (tbl : Ix.Kernel.ProjTable .anon) (kc : KKey) (cvC : Ix.Kernel.ConstantVal .anon) : Prop :=
  ∀ (c : ScopedCtx), c.t = t → c.E = E → ScopedCoreFacts c →
    c.env.find? (Ix.Kernel.projTableName k) = some (.projInfo tbl) →
    (∃ nP nF : Nat, c.env.find? kc = some (.ctorInfo cvC nP nF)) →
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
      (hk : c.κ (iprjAddr (ixAddr b) (ZMod.val i)) = k)
      {cvC' : Ix.Kernel.ConstantVal .anon} {nP nF : Nat}
      (hctor : c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) =
        some (.ctorInfo cvC' nP nF))
      (hnF : tbl.numFields = nF) (hf : ZMod.val f < nF) {g : KLevel} (hg : RepKLevel h' g r)
      {us : List KLevel} (hus : us.length = tbl.levelParams.length)
      (hzero : ∀ φ : Ix.Kernel.LevelParam → Nat,
        Ix.Kernel.Level.eval φ (Ix.Kernel.Level.subst (List.range us.length) us g) = 0),
      Ix.Kernel.Rules.FireSem (tbl.entry (ZMod.val f)) us

/-- **Every projection table of a propositional structure that `env` stores fires at every
context** over `t` and `E`, with its stored constructor. No limit occurs. -/
def ProjTablesFire (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon) : Prop :=
  ∀ (k : KKey) (tbl : Ix.Kernel.ProjTable .anon),
    env.find? (Ix.Kernel.projTableName k) = some (.projInfo tbl) →
    Ix.Kernel.Level.isEquiv tbl.structSort .zero = some true →
    ∃ (kc : KKey) (cvC : Ix.Kernel.ConstantVal .anon) (nP nF : Nat),
      env.find? kc = some (.ctorInfo cvC nP nF) ∧ ProjTableFires t E k tbl kc cvC

/-- **The tables of a context's environment firing everywhere give the firing at the context**:
what the registry's projection step consumes, read off the limit-free statement at the
context's own core facts. -/
theorem ProjTablesFire.fires {c : ScopedCtx} (hT : ProjTablesFire c.t c.E c.env)
    (hc : ScopedCoreFacts c) : ProjGuardFires c := by
  intro calls0 ih x_rc x_block r h h' calls i f hlt0 good ev b hrc hb cvT caps hind cm hrec hinfo
    cvC nP nF tbl hctor htbl hnF hf g hg us hus hzero hprop
  have hprop' : Ix.Kernel.Level.isEquiv tbl.structSort .zero = some true := hprop
  obtain ⟨kc, cvC₀, nP₀, nF₀, hkc, hfires⟩ := hT _ tbl htbl hprop'
  exact hfires c rfl rfl hc htbl ⟨nP₀, nF₀, hkc⟩ ih hlt0 good ev hrc hb hind hrec hinfo rfl hctor
    hnF hf hg hus hzero hprop

/-- **A step of the environment keeps the tables firing**: the step keeps every lookup, and a
table of a propositional structure it stores new comes with its stored constructor and its own
firing. A step that stores no such table needs nothing; no limit is involved. -/
theorem ProjTablesFire.step {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env env₂ : Ix.Kernel.Env .anon} (h : ProjTablesFire t E env)
    (hfind : ∀ (k : KKey) (ci : Ix.Kernel.ConstantInfo .anon),
      env.find? k = some ci → env₂.find? k = some ci)
    (hnew : ∀ (k : KKey) (tbl : Ix.Kernel.ProjTable .anon),
      env₂.find? (Ix.Kernel.projTableName k) = some (.projInfo tbl) →
      Ix.Kernel.Level.isEquiv tbl.structSort .zero = some true →
      env.find? (Ix.Kernel.projTableName k) = some (.projInfo tbl) ∨
      ∃ (kc : KKey) (cvC : Ix.Kernel.ConstantVal .anon) (nP nF : Nat),
        env₂.find? kc = some (.ctorInfo cvC nP nF) ∧ ProjTableFires t E k tbl kc cvC) :
    ProjTablesFire t E env₂ := by
  intro k tbl htbl hprop
  rcases hnew k tbl htbl hprop with hold | hn
  · obtain ⟨kc, cvC, nP, nF, hkc, hf⟩ := h k tbl hold hprop
    exact ⟨kc, cvC, nP, nF, hfind _ _ hkc, hf⟩
  · exact hn

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
    cvC nP nF tbl hctor htbl hnF hf g hg us hus hzero hprop
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

/-- **A certified table fires at every context over a record store for the certificate's
witness store**, given the use reading: the member's projection record, its constructor's raw
telescope, positional level parameters and the table's certificate over the witness store give
`Core.ProjTableFires` at the keys of the member and of its first constructor.

This is the certificate of one table of `GuardCerts`, with the reading applied at whichever
context a use occurs in: the limit and the call scope of that context are arbitrary. -/
theorem projTableFires_of_cert (hread : Core.ProjGuardUseReading) {t : Ix.Kernel.RoleTable}
    {R E : Ixon.Env} (hRE : Typing.RecordsFor R E) (hnocol : ¬ L1.EnvInternalCollision E)
    {B : _root_.Address} {i : Nat} {tbl : ProjTable .anon} {cvC : ConstantVal .anon}
    {raw : Expr .anon} (hmem : MemberRecordAt R B i) (hraw : ctorRaw R B i 0 = some raw)
    (hpos : tbl.levelParams = List.range tbl.levelParams.length)
    (cert : ProjGuardCert (GuardRaw.ofStore R) raw cvC.type tbl) :
    Core.ProjTableFires t E (Core.keyOf t (Core.iprjAddr B i)) tbl
      (Core.keyOf t (Core.cprjAddr B i 0)) cvC := by
  intro c ht hE hc htblc hctorc calls0 ih x_rc x_block r h h' calls j f hlt0 good ev b hrc hb
    cvT caps hind cm hrec hinfo hk cvC' nP nF hctor hnF hf g hg us hus hzero hprop
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
      (recordOf_eq_recordAt_decoded hRE.1 _).symm.trans hcm'
    have h2 : cm = cm' := Option.some.inj (hrec.symm.trans h1)
    rw [← h2]
    exact hinfo
  have haddr : Core.iprjAddr (Core.ixAddr b) (ZMod.val j) = Core.iprjAddr B i :=
    Core.keyOf_inj hc.env.tableWf (hkI.symm.trans hk)
  obtain ⟨hB, hI⟩ :=
    (hmem.recordsFor hRE).eq_of_addr hproj (Core.ProjAux.val_toUInt64_toNat j) haddr
  subst hB
  subst hI
  have htbl : c.env.find? (Ix.Kernel.projTableName
      (c.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val j)))) = some (.projInfo tbl) := by
    rw [hk]
    exact htblc
  rcases hread c hc ih hlt0 good ev hrc hb (Or.inl ⟨cvT, caps, hind⟩) hctor htbl hprop' hf hg with
    hcol | ⟨raw', hraw', use⟩
  · exact absurd hcol hnocol
  · have h1 : c.env.find? (Core.keyOf c.t (Core.cprjAddr (Core.ixAddr b) (ZMod.val j) 0)) =
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
    refine fireSem_of_cert hRE hraw cert hraw' use hfT (fun φ => ?_) hprop
    rw [hlp]
    exact hzero φ

/-- **The carried certificates and the use reading give the limit-free firing of every stored
table**, over each record store for the witness store that holds no blob and record of
different bytes at one address. -/
theorem projTablesFire_of_certs (hread : Core.ProjGuardUseReading) {t : Ix.Kernel.RoleTable}
    {R E : Ixon.Env} {env : Ix.Kernel.Env .anon} (hRE : Typing.RecordsFor R E)
    (hnocol : ¬ L1.EnvInternalCollision E) (hcerts : GuardCerts t R env) :
    Core.ProjTablesFire t E env := by
  intro k tbl htbl hprop
  obtain ⟨B, i, cvC, nP, nF, raw, hk, hmem, hctor, hraw, hpos, cert⟩ := hcerts k tbl htbl hprop
  subst hk
  exact ⟨_, cvC, nP, nF, hctor, projTableFires_of_cert hread hRE hnocol hmem hraw hpos cert⟩

end IxVM.Refinement.Guard
