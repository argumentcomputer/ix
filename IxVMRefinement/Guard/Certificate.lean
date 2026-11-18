import IxC.Kernel.Model.ProjGuardCert
import IxVMRefinement.Guard.CtorRaw
import IxVMRefinement.Decl.Native
import IxVMRefinement.Guard.Fields
import IxVMRefinement.Infer.Proj

/-! # The projection guard, as certificates over a witness store

`Ix.Kernel.ProjGuardCert` (`IxC/Kernel/Model/ProjGuardCert.lean`) is the certificate of one
projection table: the table's guards are `structProjGuards` at field sorts whose zero-sets are
those of the field classifier's signatures of the constructor's raw telescope. This file places
it over the stores of the proof.

* `ctorRaw E B i j` (`Guard/CtorRaw.lean`): the constructor's type as the classifier reads it, a
  function of the block record `E` holds at `B` and of `E`'s literal blobs.
* `GuardCerts t R env`: **the certificates of the stored tables, as one proposition**. Every
  projection table of a propositional structure that `env` stores is the table of a member
  whose projection record the witness store `R` holds (`MemberRecordAt`), with that member's
  first constructor stored and the table's certificate over the raw dictionary of `R`. It
  mentions no role context, no validation limit and no run. No fold carries it: a prefix carries
  the tables' firing in its load contract (`Core.ScopedLoadFacts.projFire`), which the install
  of a native block produces from the new table's certificate
  (`Guard.projTableFires_of_cert_at`).
* `GuardCerts.recordsFor`: the clause over `R` is the clause over every record store for `R`.
* `projGuardCert_of_checkNativeTable`: **install**. The table stage of IxC's native install,
  run at field sorts `sorts` (the caller's argument), stores a table whose certificate holds as
  soon as those sorts have the zero-sets of the classifier's signatures. The sorts to pass are
  the rules-tier sorts of the field domains that the reading of the installing run's checked
  field loop yields (`GuardData.check_prop_fields_sorts`). The levels the circuit itself
  computes are simplified (`level_imax a 0 = 0`): they equal those sorts at every assignment,
  not as syntax, which is all the certificate reads of them.
* `GuardCerts.fireSem`: **use**. The clause over `R`, and one use observed over any record store
  `E` for `R`, give `Rules.FireSem` at the use's levels. The store `E` is constrained by
  `Typing.RecordsFor R E` alone, and no limit occurs.
* `CheckedFieldsReading`, `ProjGuardUseReading`: the two statements that remain to be proved
  about the circuit (definitions, not theorems). The first reads the installing run's checked
  field loop as the hypotheses of the install theorem; it has the hypotheses of
  `Core.GuardData.check_prop_fields_sorts` and the load of the constructor. The second reads a
  run of `KernelInfer::proj_guard` at a propositional structure's table as the use observation
  `Ix.Kernel.ProjGuardUse` over the context's store; it has the hypotheses of
  `Core.ProjAux.proj_guard_rep` and the table's lookups, and is stated where the guard is
  consumed, at the consuming run's own context and limit. Both allow the store's internal
  collision as the alternative, as the raw dictionary's readings of a load do.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Guard

open IxVM.Consistency
open Ix.Kernel (Expr Level ProjTable ConstantInfo ConstantVal ProjGuardCert ProjGuardUse)
open Ix.Kernel.GuardClassifier (Lookup)

/-! ## The certificates of the stored tables -/

/-- **The store holds the projection record of member `i` of the block at `B`, at its
address**: a record whose content is the inductive projection `(i, B)`, with `i` a 64-bit
index. A member is named by this record, not by the address alone: the address is a hash, and
two members with one address have one record. -/
def MemberRecordAt (S : Ixon.Env) (B : _root_.Address) (i : Nat) : Prop :=
  ∃ cm : Ixon.Constant, recordOf S (Core.iprjAddr B i) = some cm ∧
    cm.info = .iPrj ⟨i.toUInt64, B⟩ ∧ i.toUInt64.toNat = i

/-- The record is held by every record store for the store. -/
theorem MemberRecordAt.recordsFor {R E : Ixon.Env} {B : _root_.Address} {i : Nat}
    (h : MemberRecordAt R B i) (hRE : Typing.RecordsFor R E) : MemberRecordAt E B i :=
  let ⟨cm, hcm, hinfo, hi⟩ := h
  ⟨cm, recordOf_recordsFor hRE _ _ hcm, hinfo, hi⟩

/-- **Two members with one projection address are one member**, where the store holds the
record of the first and any record it holds at the second's address is the second's projection
(what holds at every block a run hashed). -/
theorem MemberRecordAt.eq_of_addr {S : Ixon.Env} {B B' : _root_.Address} {i i' : Nat}
    (h : MemberRecordAt S B i)
    (hproj : ∀ cm : Ixon.Constant, recordOf S (Core.iprjAddr B' i') = some cm →
      cm.info = .iPrj ⟨i'.toUInt64, B'⟩)
    (hi' : i'.toUInt64.toNat = i') (haddr : Core.iprjAddr B' i' = Core.iprjAddr B i) :
    B' = B ∧ i' = i := by
  obtain ⟨cm, hcm, hinfo, hi⟩ := h
  have h1 := hproj cm (by rw [haddr]; exact hcm)
  rw [hinfo] at h1
  have h2 := Ixon.ConstantInfo.iPrj.inj h1
  have hB : B = B' := congrArg Ixon.InductiveProj.block h2
  have hidx : i.toUInt64 = i'.toUInt64 := congrArg Ixon.InductiveProj.idx h2
  exact ⟨hB.symm, (hi'.symm.trans (congrArg UInt64.toNat hidx.symm)).trans hi⟩

/-- **The projection guards of `env`, certified over the witness store `R`**: every projection
table `env` stores whose structure sort passes the zero test is the table of a member `(B, i)`
whose projection record `R` holds: the table's key is the key of the member's projection
address, `env` stores the member's first constructor, and the table has its certificate over
`R`'s raw dictionary at that constructor's raw telescope read from `R`, with level parameters
the positions `0, …, k - 1` (the numbering of the classifier's raw syntax and of the levels a
run computes).

The member is given with the table, as the record the store holds; it is not quantified over
every pair whose address has the table's key. The clause mentions no role context, no
validation limit and no run. -/
def GuardCerts (t : Ix.Kernel.RoleTable) (R : Ixon.Env) (env : Ix.Kernel.Env .anon) : Prop :=
  ∀ (k : Ix.Kernel.Key .anon) (tbl : ProjTable .anon),
    env.find? (Ix.Kernel.projTableName k) = some (.projInfo tbl) →
    Level.isEquiv tbl.structSort .zero = some true →
    ∃ (B : _root_.Address) (i : Nat) (cvC : ConstantVal .anon) (nP nF : Nat)
      (raw : Expr .anon),
      k = Core.keyOf t (Core.iprjAddr B i) ∧ MemberRecordAt R B i ∧
      env.find? (Core.keyOf t (Core.cprjAddr B i 0)) = some (.ctorInfo cvC nP nF) ∧
      ctorRaw R B i 0 = some raw ∧
      tbl.levelParams = List.range tbl.levelParams.length ∧
      ProjGuardCert (GuardRaw.ofStore R) raw cvC.type tbl

/-- **The clause over a witness store is the clause over each of its record stores.** A record
store is constrained by `Typing.RecordsFor` alone. -/
theorem GuardCerts.recordsFor {t : Ix.Kernel.RoleTable} {R E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} (h : GuardCerts t R env) (hRE : Typing.RecordsFor R E) :
    GuardCerts t E env := by
  intro k tbl htbl hprop
  obtain ⟨B, i, cvC, nP, nF, raw, hk, hrec, hctor, hraw, hpos, cert⟩ := h k tbl htbl hprop
  exact ⟨B, i, cvC, nP, nF, raw, hk, hrec.recordsFor hRE, hctor, ctorRaw_recordsFor hRE hraw,
    hpos, cert.mono (GuardRaw.ofStore_extends_recordsFor hRE)⟩

/-- An environment that stores no projection table carries the clause over every store. -/
theorem guardCerts_of_noTable {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {env : Ix.Kernel.Env .anon}
    (h : ∀ (k : Ix.Kernel.Key .anon) (tbl : ProjTable .anon),
      env.find? k ≠ some (.projInfo tbl)) : GuardCerts t R env :=
  fun _ tbl htbl _ => (h _ tbl htbl).elim

/-! ## Install -/

/-- **Install: the table IxC's native install stores carries the certificate of the sorts it
was run at.** `checkNativeTable` takes the field sorts as an argument; at a one-constructor
block without indices it stores the table whose guards are `structProjGuards` at them. If those
sorts have the zero-sets of the classifier's signatures of the constructor's raw telescope
(what each `checked_sort` of the installing run's field loop asserts), the stored table has
its certificate. -/
theorem projGuardCert_of_checkNativeTable {p : Ix.Kernel.NativeParts .anon}
    {cA : ConstantVal .anon × Nat} {sorts : List Level} {env env₂ : Ix.Kernel.Env .anon}
    (hidx : p.nIdx = 0)
    (htbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p [cA] [sorts] env =
      .ok env₂)
    {look : Lookup .anon} {raw : Expr .anon} {sigs : List Level} {fuel : Nat}
    (hsig : Ix.Kernel.GuardClassifier.fieldSignatures look fuel p.nP cA.2 [] raw = some sigs)
    (hzero : ∀ j, j < cA.2 → ∀ φ : Ix.Kernel.LevelParam → Nat,
      Level.eval φ (sorts.getD j .zero) = 0 ↔ Level.eval φ (sigs.getD j .zero) = 0) :
    ∃ tbl : ProjTable .anon,
      env₂ = ⟨.projInfo tbl :: env.consts⟩ ∧
      env₂.find? (Ix.Kernel.projTableName p.cvT.name) = some (.projInfo tbl) ∧
      tbl.numParams = p.nP ∧ tbl.numFields = cA.2 ∧ tbl.structSort = p.resSort ∧
      tbl.levelParams = p.cvT.levelParams ∧
      ProjGuardCert look raw cA.1.type tbl := by
  obtain ⟨tbl, henv, -, hfind, -, -, hnP, hnF, hlps, hsort, -, -, hguards, -⟩ :=
    Decl.checkNativeTable_struct_inv hidx htbl
  refine ⟨tbl, henv, hfind, hnP, hnF, hsort, hlps, ⟨sorts, sigs, fuel, ?_, ?_, ?_⟩⟩
  · rw [hnP, hnF]; exact hguards
  · rw [hnP, hnF]; exact hsig
  · intro j hj φ
    exact hzero j (hnF ▸ hj) φ

/-! ## Use -/

/-- **Use, for one table**: the certificate over a witness store `R` and a use observed over
any record store `E` for `R` give the rules tier's firing condition at the use's levels. -/
theorem fireSem_of_cert {R E : Ixon.Env} (hRE : Typing.RecordsFor R E)
    {B : _root_.Address} {i : Nat} {raw raw' cty : Expr .anon} {tbl : ProjTable .anon}
    {f : Nat} {g : Level} {us : List Level}
    (hraw : ctorRaw R B i 0 = some raw)
    (cert : ProjGuardCert (GuardRaw.ofStore R) raw cty tbl)
    (hraw' : ctorRaw E B i 0 = some raw')
    (use : ProjGuardUse (GuardRaw.ofStore E) raw' cty tbl.numParams f g)
    (hf : f < tbl.numFields)
    (hzero : ∀ φ : Ix.Kernel.LevelParam → Nat,
      Level.eval φ (Level.subst tbl.levelParams us g) = 0) :
    Ix.Kernel.Rules.FireSem (tbl.entry f) us := by
  have hsame : raw' = raw :=
    Option.some.inj (hraw'.symm.trans (ctorRaw_recordsFor hRE hraw))
  subst hsame
  exact cert.fireSem (GuardRaw.ofStore_extends_recordsFor hRE)
    ⟨fun _ _ _ h => h, fun _ _ _ h => h⟩ use hf hzero

/-- **Use: the clause and one use give `FireSem`**, over every record store `E` for the
witness store and at every level list. No role context and no validation limit occur: the same
clause serves a use under any of them.

The use names the member by the block `B` and the index `i` its run read. `hproj` and `hi` tie
that pair to the member the clause holds for the table: any record `E` holds at the member's
projection address is the member's projection (true of every block a run hashed, for a store
that decodes its records), and the index is a 64-bit one (true of an index read from a field
element). The table's well-formedness makes keys identify addresses. -/
theorem GuardCerts.fireSem {t : Ix.Kernel.RoleTable} {R E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} (h : GuardCerts t R env) (hRE : Typing.RecordsFor R E)
    (htwf : t.wf = true)
    {B : _root_.Address} {i : Nat} {tbl : ProjTable .anon} {cvC : ConstantVal .anon}
    {nP nF : Nat}
    (htbl : env.find? (Ix.Kernel.projTableName (Core.keyOf t (Core.iprjAddr B i))) =
      some (.projInfo tbl))
    (hctor : env.find? (Core.keyOf t (Core.cprjAddr B i 0)) = some (.ctorInfo cvC nP nF))
    (hproj : ∀ cm : Ixon.Constant, recordOf E (Core.iprjAddr B i) = some cm →
      cm.info = .iPrj ⟨i.toUInt64, B⟩)
    (hi : i.toUInt64.toNat = i)
    {raw' : Expr .anon} {f : Nat} {g : Level} {us : List Level}
    (hraw' : ctorRaw E B i 0 = some raw')
    (use : ProjGuardUse (GuardRaw.ofStore E) raw' cvC.type tbl.numParams f g)
    (hf : f < tbl.numFields) (hus : us.length = tbl.levelParams.length)
    (hzero : ∀ φ : Ix.Kernel.LevelParam → Nat,
      Level.eval φ (Level.subst (List.range us.length) us g) = 0) :
    Ix.Kernel.Rules.FireSem (tbl.entry f) us := by
  intro hprop
  obtain ⟨B₀, i₀, cvC₀, nP₀, nF₀, raw, hk, hrec, hctor₀, hraw, hpos, cert⟩ :=
    h _ tbl htbl hprop
  have haddr : Core.iprjAddr B i = Core.iprjAddr B₀ i₀ := Core.keyOf_inj htwf hk
  obtain ⟨hB, hii⟩ := (hrec.recordsFor hRE).eq_of_addr hproj hi haddr
  subst hB
  subst hii
  rw [hctor] at hctor₀
  have hcv : cvC = cvC₀ := (Ix.Kernel.ConstantInfo.ctorInfo.inj (Option.some.inj hctor₀)).1
  subst hcv
  have hlp : tbl.levelParams = List.range us.length := by rw [hus]; exact hpos
  refine fireSem_of_cert hRE hraw cert hraw' use hf (fun φ => ?_) hprop
  rw [hlp]
  exact hzero φ

end IxVM.Refinement.Guard

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel)

/-- **What a run of `KernelInfer::proj_guard` at a propositional structure's table has to be
read as** (the statement left to the refinement of the checked walk and of the runtime
classifier): under the hypotheses of `ProjAux.proj_guard_rep`, with the constructor and the
table the context's environment stores for the block member, the table's structure sort
passing the zero test and the field in range, the level `g` the run returns is a use
observation over the context's store, at the constructor's raw telescope read from that store.

It is stated at the consuming run's own context: any role table, any limit. With
`Guard.GuardCerts.fireSem` it gives the last premise of `Infer.proj` in
`ProjAux.infer_proj_common`. -/
def ProjGuardUseReading : Prop :=
  ∀ (c : ScopedCtx) (hc : ScopedCoreFacts c) {calls0 : List (Call F)} (ih : IH c calls0)
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
    (hf : ZMod.val f < nF) {g : KLevel} (hg : RepKLevel h' g r),
    L1.EnvInternalCollision c.E ∨
    ∃ raw, Guard.ctorRaw c.E (ixAddr b) (ZMod.val i) 0 = some raw ∧
      Ix.Kernel.ProjGuardUse (GuardRaw.ofStore c.E) raw cvC.type tbl.numParams (ZMod.val f) g

/-- **What the installing run's checked field loop has to be read as** (the statement left to
the refinement of the runtime classifier at the install): under the hypotheses of
`GuardData.check_prop_fields_sorts`, where the type pointer the loop walks is the type field
of the constructor the run loaded for member `i` of the block at `b`, there are field sorts
with their `FieldSortsJ` witness (the sorts to run IxC's table stage at) whose zero-sets are
those of the classifier's signatures of the constructor's raw telescope read from the
context's store. Its second to fourth conjuncts are the hypotheses of
`Guard.projGuardCert_of_checkNativeTable`. -/
def CheckedFieldsReading : Prop :=
  ∀ (c : ScopedCtx) (hc : ScopedCoreFacts c) {nP nF : Nat} {Γ : Nat → KExpr}
    {E residual body : KExpr} {parameters fvs : List KExpr}
    {rc level p r : SourceValue F} {np nf : F} {h h' : Heap F} {cs : List (Call F)}
    {u : KLevel} (hp : np.val = nP) (hf : nf.val = nF)
    (opened : Ix.Kernel.openPisAtFvars nP E 0 = some (parameters, residual))
    (openedFields : Ix.Kernel.openPisAtFvars nF residual nP = some (fvs, body))
    (hg : CoreGood c cs) (hrc : c.rc h rc) (hE : Tm c.κ 0 Γ h 0 E p)
    (represented : RepKLevel h u level) (zero : ∀ φ, Ix.Kernel.Level.eval φ u = 0)
    (ev : ObsFn W "KernelGuard::check_prop_fields"
      [rc, level, .field 1, .field 0, p, .field np, .field nf] h r h' cs)
    {b : Bytes.Address} {i : F} {bp ptr w₁ w₃ w₄ w₅ w₆ w₇ w₈ : SourceValue F}
    {h₀ m : Heap F} {cs₀ : List (Call F)}
    (load : ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field 0] h₀ ptr m cs₀)
    (good₀ : CoreGood c cs₀) (hb : Bytes.RepAddressRef addrTy h₀ b bp)
    (ld : loadValue m ptr = .ok (.construct kciEnum "Ctor" [w₁, p, w₃, w₄, w₅, w₆, w₇, w₈]))
    (hext : Heap.Extends m h),
    L1.EnvInternalCollision c.E ∨
    ∃ (sorts sigs : List KLevel) (fuel : Nat) (raw : KExpr),
      Ix.Kernel.Semantics.FieldSortsJ Ix.Kernel.Model.rulesJ c.env true false u nP fvs [] nF
        sorts ∧
      Guard.ctorRaw c.E (ixAddr b) (ZMod.val i) 0 = some raw ∧
      Ix.Kernel.GuardClassifier.fieldSignatures (GuardRaw.ofStore c.E) fuel nP nF [] raw =
        some sigs ∧
      ∀ j, j < nF → ∀ φ : Ix.Kernel.LevelParam → Nat,
        Ix.Kernel.Level.eval φ (sorts.getD j .zero) = 0 ↔
          Ix.Kernel.Level.eval φ (sigs.getD j .zero) = 0

end IxVM.Refinement.Core
