import IxC.Kernel.Model.ProjGuardCert
import IxVMRefinement.Guard.CtorRaw
import IxVMRefinement.Decl.Native
import IxVMRefinement.Guard.Fields
import IxVMRefinement.Infer.Proj

/-! # The projection guard, carried as certificates over a witness store

`Ix.Kernel.ProjGuardCert` (`IxC/Kernel/Model/ProjGuardCert.lean`) is the certificate of one
projection table: the table's guards are `structProjGuards` at field sorts whose zero-sets are
those of the field classifier's signatures of the constructor's raw telescope. This file places
it over the stores of the proof.

* `ctorRaw E B i j` (`Guard/CtorRaw.lean`): the constructor's type as the classifier reads it, a
  function of the block record `E` holds at `B` and of `E`'s literal blobs.
* `GuardCerts t R env`: **the carried clause**. Every projection table of a propositional
  structure that `env` stores has its certificate over the raw dictionary of the witness store
  `R`. It mentions no role context, no validation limit and no run.
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

/-! ## The carried clause -/

/-- **The projection guards of `env`, certified over the witness store `R`**: for every block
address `B` and member `i` whose projection table `env` stores, with the constructor `env`
stores for it, if the table's structure sort passes the zero test, the table has its
certificate over `R`'s raw dictionary at the constructor's raw telescope read from `R`, and
its level parameters are the positions `0, …, k - 1` (the numbering of the classifier's raw
syntax and of the levels a run computes).

The clause mentions no role context, no validation limit and no run: the role table enters
only through the keys of the two lookups in `env`. -/
def GuardCerts (t : Ix.Kernel.RoleTable) (R : Ixon.Env) (env : Ix.Kernel.Env .anon) : Prop :=
  ∀ (B : _root_.Address) (i : Nat) (tbl : ProjTable .anon) (cvC : ConstantVal .anon)
    (nP nF : Nat),
    env.find? (Ix.Kernel.projTableName (Core.keyOf t (Core.iprjAddr B i))) =
      some (.projInfo tbl) →
    env.find? (Core.keyOf t (Core.cprjAddr B i 0)) = some (.ctorInfo cvC nP nF) →
    Level.isEquiv tbl.structSort .zero = some true →
    ∃ raw, ctorRaw R B i 0 = some raw ∧
      tbl.levelParams = List.range tbl.levelParams.length ∧
      ProjGuardCert (GuardRaw.ofStore R) raw cvC.type tbl

/-- **The clause over a witness store is the clause over each of its record stores.** A record
store is constrained by `Typing.RecordsFor` alone. -/
theorem GuardCerts.recordsFor {t : Ix.Kernel.RoleTable} {R E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} (h : GuardCerts t R env) (hRE : Typing.RecordsFor R E) :
    GuardCerts t E env := by
  intro B i tbl cvC nP nF htbl hctor hprop
  obtain ⟨raw, hraw, hpos, cert⟩ := h B i tbl cvC nP nF htbl hctor hprop
  exact ⟨raw, ctorRaw_recordsFor hRE hraw, hpos,
    cert.mono (GuardRaw.ofStore_extends_recordsFor hRE)⟩

/-- An environment that stores no projection table carries the clause over every store. -/
theorem guardCerts_of_noTable {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {env : Ix.Kernel.Env .anon}
    (h : ∀ (k : Ix.Kernel.Key .anon) (tbl : ProjTable .anon),
      env.find? k ≠ some (.projInfo tbl)) : GuardCerts t R env :=
  fun _ _ tbl _ _ _ htbl _ _ => (h _ tbl htbl).elim

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

/-- **Use: the carried clause and one use give `FireSem`**, over every record store `E` for the
witness store and at every level list. No role context and no validation limit occur: the same
clause serves a use under any of them. -/
theorem GuardCerts.fireSem {t : Ix.Kernel.RoleTable} {R E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} (h : GuardCerts t R env) (hRE : Typing.RecordsFor R E)
    {B : _root_.Address} {i : Nat} {tbl : ProjTable .anon} {cvC : ConstantVal .anon}
    {nP nF : Nat}
    (htbl : env.find? (Ix.Kernel.projTableName (Core.keyOf t (Core.iprjAddr B i))) =
      some (.projInfo tbl))
    (hctor : env.find? (Core.keyOf t (Core.cprjAddr B i 0)) = some (.ctorInfo cvC nP nF))
    {raw' : Expr .anon} {f : Nat} {g : Level} {us : List Level}
    (hraw' : ctorRaw E B i 0 = some raw')
    (use : ProjGuardUse (GuardRaw.ofStore E) raw' cvC.type tbl.numParams f g)
    (hf : f < tbl.numFields) (hus : us.length = tbl.levelParams.length)
    (hzero : ∀ φ : Ix.Kernel.LevelParam → Nat,
      Level.eval φ (Level.subst (List.range us.length) us g) = 0) :
    Ix.Kernel.Rules.FireSem (tbl.entry f) us := by
  intro hprop
  obtain ⟨raw, hraw, hpos, cert⟩ := h B i tbl cvC nP nF htbl hctor hprop
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
