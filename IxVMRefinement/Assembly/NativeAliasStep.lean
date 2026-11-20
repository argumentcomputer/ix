import IxVMRefinement.Assembly.FoldClauseAlias
import IxVMRefinement.Assembly.NativeBlockEtaFields
import IxVMRefinement.Assembly.NativeBlockRetHeadIxon

/-! # The unit step of a one-type native block whose former is declared at a definition

A family such as `inductive R (α : Type) : Rel α`, with `Rel α := α → α → Prop`, is stored at
its declared type, and the telescope constant the later stages read is the telescope the
circuit builds from it. This module states the step of such a block once, in the form both
folds consume, and proves it from what the block's check gives.

* `checkNativeTable_of_indexed`, `NativeAtFacts.noTable`: **an install at a family with an
  index stores no projection table.** The circuit refuses a former declared at a definition
  that has no index, so this covers every such install.
* `HoldsBlock E₀ E B cb ind`: a record store that holds the block's records and the run's
  blobs. The step's own store is one; so is every record store for a witness store that holds
  them.
* `AliasInstallOut`: what the block's check puts in front of a prefix, read once: IxC's record
  of the install at the registered family (`NativeAtFacts`), whose telescope constant is the
  traced term; the opened head trace from the stored former (`FormerOpenTraceAt`); the family's
  data as the new environment stores it; the new constants with their names and readings; and,
  at every store that holds the block's records, the new constants as the store reads them
  (`BlockInstall`).
* `blockEta_of_indexed`, `blockTable_of_indexed`: at a family with an index the two bundles the
  load contract asks of an install hold by the index alone: such a family is not structure-like,
  has no η capability and no projection table.
* `famIxonRetHead_of_holds`: the constructors' literal return, a fact about the block's record,
  holds of the family at every store that holds the record.
* `AliasInstallOut.keeps`: **the install keeps the fold's clause at the opened head trace**, at
  every store that holds the block's records, every limit and every registry, registering the
  family. It discharges the five facts `FoldClauseWith.aliasInstall` asks at the new
  environment.
* `AliasUnitStep`: **the step, stated once.** From the clause at the store and the limit of the
  block's check: new constants and one family, with the clause kept at every admitted store,
  every limit and every registry extended by that family.
* `AliasUnitStep.unitStep`: the typing fold's `UnitStep (FoldExtra FormerOpenTraceAt t E)` at
  the walk's limit. The binding fold's form is `AliasUnitStep.overUnitStep`
  (`Assembly/NativeAliasStepOver.lean`).
* `aliasUnitStep_of_install`: the step from a producer of `AliasInstallOut` at each environment
  the step is asked at.
-/

universe u

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps Key)
open Ix.Kernel.Semantics (NativeFam NativeFamStored)

/-! ## No projection table at a family with an index -/

/-- **The table check keeps the environment at a family with an index.** -/
theorem checkNativeTable_of_indexed {p : Ix.Kernel.NativeParts .anon}
    {ctorsA : List (ConstantVal .anon × Nat)} {sortss : List (List Ix.Kernel.Level)}
    {X env₂ : Ix.Kernel.Env .anon}
    (h : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p ctorsA sortss X = .ok env₂)
    (hidx : p.nIdx ≠ 0) : env₂ = X := by
  unfold Ix.Kernel.checkNativeTable at h
  split at h
  · split at h
    · rename_i h0
      have h0' : p.nIdx = 0 := by simpa using h0
      exact absurd h0' hidx
    · injection h with hX
      exact hX.symm
  · injection h with hX
    exact hX.symm

/-- **An install at a family with an index stores no projection table**: a projection table
the new environment holds is one the old environment held. -/
theorem NativeAtFacts.noTable {env env₂ : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)}
    {nP nIdx : Nat} {p₀ : Ix.Kernel.NativeParts .anon} {fam : NativeFam .anon}
    (h : NativeAtFacts env env₂ blk nP nIdx p₀ fam) (hidx : fam.p.nIdx ≠ 0) :
    ∀ (k : Key .anon) (tbl : Ix.Kernel.ProjTable .anon),
      env₂.find? (Ix.Kernel.projTableName k) = some (.projInfo tbl) →
      env.find? (Ix.Kernel.projTableName k) = none → False := by
  obtain ⟨-, -, isRec, cvS, cvTa, caps, p₁, p, ctorsA, sortss, kinds, tfvs, trest, isorts, hfam,
    -, -, -, -, -, -, -, -, -, hTbl⟩ := h
  subst hfam
  intro k tbl hf hnone
  have hc : (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS caps :: env.consts⟩).consts =
      ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
        [.indInfo cvS caps]) ++ env.consts := by
    rw [Decl.consts_consSumCtors_eq]
    simp
  have henv : env₂ = ⟨((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      [.indInfo cvS caps]) ++ env.consts⟩ := by
    rw [checkNativeTable_of_indexed hTbl hidx]
    exact congrArg Ix.Kernel.Env.mk hc
  rw [henv] at hf
  rcases find?_append_cases (env := env) _ hf with hm | hold
  · rcases List.mem_append.mp hm with hct | hind
    · obtain ⟨c, -, hc'⟩ := List.mem_map.mp (List.mem_reverse.mp hct)
      exact nomatch hc'
    · exact nomatch (List.mem_singleton.mp hind)
  · rw [hnone] at hold
    exact nomatch hold

/-! ## Stores that hold the block -/

/-- **A record store that holds the block's records and the run's blobs**: it decodes every
record it holds; it holds the block `cb` of the one inductive member `ind` at `B`, the member's
projection record and each constructor's; and every blob of the run's store. -/
structure HoldsBlock (E₀ E : Ixon.Env) (B : _root_.Address) (cb : Ixon.Constant)
    (ind : Ixon.Inductive) : Prop where
  decoded : Ingress.EnvDecoded E
  block : recordOf E B = some cb
  former : recordOf E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind))
  ctors : ∀ j < ind.ctors.size,
    recordOf E (ctorAddr B 0 j) = some (constructorProjection B 0 j)
  blobs : ∀ a b, E₀.blobs.get? a = some b → E.blobs.get? a = some b

/-- The store a step runs against holds the block of its unit. -/
theorem HoldsBlock.of_stepStore {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    (hst : StepStore calls t E₀ E) (hrec : BlockUnitRecord E₀ B cb ind) :
    HoldsBlock E₀ E B cb ind where
  decoded := hst.decoded
  block := hst.held hrec.record
  former := hst.held hrec.former
  ctors := fun j hj => hst.held (hrec.ctors j hj)
  blobs := hst.runBlob

/-! ## What the install puts in front of a prefix -/

/-- **What the check of a block whose former is declared at a definition puts in front of a
prefix** (module docstring). `new` are the new constants, `fam` the registered family, whose
telescope constant is the traced term, and `caps` the stored former's capability record. -/
structure AliasInstallOut (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (B : _root_.Address) (cb : Ixon.Constant) (ind : Ixon.Inductive)
    (blk : List (ConstantInfo .anon)) (p₀ : Ix.Kernel.NativeParts .anon)
    (new : List (ConstantInfo .anon)) (fam : NativeFam .anon) (caps : IndCaps .anon) : Prop where
  /-- IxC's record of the install, at the registered family. -/
  facts : NativeAtFacts env ⟨new ++ env.consts⟩ blk ind.params.toNat ind.indices.toNat p₀ fam
  pin : Ix.Kernel.basisPinHit blk = none
  nonAux : Decl.DeclNonAux (.indDecl blk ind.params.toNat)
  /-- The member has an index. -/
  indexed : ind.indices.toNat ≠ 0
  nP : fam.p.nP = ind.params.toNat
  nIdx : fam.p.nIdx = ind.indices.toNat
  lenA : fam.ctorsA.length = ind.ctors.size
  famName : fam.p.cvT.name = Core.keyOf t (Core.iprjAddr B 0)
  famLevels : fam.p.cvT.levelParams = List.range ind.lvls.toNat
  ctorNames : ∀ (j : Nat) (cA : ConstantVal .anon × Nat), fam.ctorsA[j]? = some cA →
    cA.1.name = Core.keyOf t (Core.cprjAddr B 0 j)
  /-- The telescope constant has the traced binders of the stored former's type, and the
  family's sort is its traced sort. -/
  trace : FormerOpenTraceAt ⟨new ++ env.consts⟩ fam
  /-- The family as the new environment stores it. -/
  stored : NativeFamStored ⟨new ++ env.consts⟩ fam
  isProp : fam.p.isProp = (Ix.Kernel.Level.isEquiv fam.p.resSort .zero == some true)
  kinds : Ix.Kernel.classifyFixKinds (m := Ix.Kernel.CheckM .anon) fam.p.cvT.name
    fam.p.cvT.levelParams fam.p.nP fam.p.nIdx fam.ctorsA = .ok fam.p.kinds
  nodupA : (fam.ctorsA.map (·.1.name)).Nodup
  ctorFields : ∀ (j : Nat) (c cA : ConstantVal .anon × Nat), fam.p.ctors[j]? = some c →
    fam.ctorsA[j]? = some cA → cA.2 = c.2
  /-- No stored constructor type projects out of the family. -/
  noProj : BlockFamCtorNoProj fam
  /-- The constructors of the member return literally: a fact about the block's record. -/
  retHead : BlockCtorIxonRetHead cb ind
  /-- The new constants: distinct names, fresh, each at the key of a constant address of the
  record, which is an address of 32 bytes, and at each such address a constant that stores a
  reading of it over the run's records. -/
  nodup : (new.map (·.name)).Nodup
  fresh : ∀ ci ∈ new, env.find? ci.name = none
  reads : ∀ x, ConstAddrOf B cb x →
    ∃ ci ∈ new, ∃ ci₀, ci.name = keyOf t x ∧ Reads t E₀ x ci₀ ∧ StoredAs ci ci₀
  named : ∀ ci ∈ new, ∃ x, ConstAddrOf B cb x ∧ ci.name = keyOf t x ∧ x.hash.size = 32
  /-- The new constants as a store that holds the block's records reads them, at any limit. -/
  install : ∀ (E : Ixon.Env) (lim : Option Nat), HoldsBlock E₀ E B cb ind →
    BlockInstall ⟨E, env, t, lim⟩ new B cb ind caps

/-! ## The load contract's bundles at a family with an index -/

section Indexed

variable {c : Core.Ctx} {new : List (ConstantInfo .anon)} {B : _root_.Address}
  {cb : Ixon.Constant} {ind : Ixon.Inductive} {caps : IndCaps .anon}

/-- **The two η fields of the load contract at a new family with an index**: a load of the
member shows no index, so neither field has an instance. -/
theorem blockEta_of_indexed (hI : BlockInstall c new B cb ind caps)
    (hidx : ind.indices.toNat ≠ 0) : BlockEta c new := by
  refine ⟨?_, ?_⟩
  · intro ac b sa i j cvc cvT caps' cnP cnF us l bp ptr nl ty np u blk' idx h1 h2 cs1 hfC hname
      hpos ev good hb hld hfT hmod hpi hnz hsr hsa hm
    exfalso
    have hbh := Ingress.hashedBlockAt_of_get_ci_iprj (c := appCtx c new) good hb ev
    have hnC : cvc.name = (appCtx c new).stored.κ (Core.ixAddr ac) :=
      Core.WhnfAux.name_of_find hfC
    have hfam : FamNew (appCtx c new).stored new (Core.ixAddr b) (ZMod.val i) := by
      rcases hm with hm | hm
      · have hfC' : (appCtx c new).env.find?
            ((appCtx c new).stored.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) j)) =
              some (.ctorInfo cvc cnP cnF) := by
          rw [← hname, hnC]
          exact hfC
        exact Or.inr ⟨j, cvc, cnP, cnF, hfC', hm⟩
      · exact Or.inl ⟨cvT, caps', hfT, hm⟩
    obtain ⟨hbB, hi0⟩ := hI.famNew hbh (val_lt_uint64 i) hfam
    have hblock' : recordOf c.E (Core.ixAddr b) = some cb := by
      rw [hbB]
      exact hI.block
    obtain ⟨tyPtr, blkPtr, hld₀, hp56, hi56, hc56⟩ :=
      iprj_get_ci_value good.1 good.2 hb ev hblock' hI.muts hi0
    rw [hld₀] at hld
    have hv := Except.ok.inj hld
    simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hv
    obtain ⟨-, -, -, hm0, hn1, -⟩ := hv
    have e := field_count_eq hi56 hm0
    rw [ZMod.val_zero] at e
    exact hidx e.symm
  · intro pp ptr nl ty u blk' h1 h2 cs1 pa b i m cvT cvc caps' cnP cnF us l ev good hpa hld hb
      hfT hfC hmulti hsr hpi hnz hm
    exfalso
    have hx := get_ci_induct_addr ev good.2 hpa hld hb
    have hbh := Ingress.hashedBlockAt_of_get_ci_induct (c := appCtx c new) good ev hpa hld hb
    have hBi : Core.ixAddr b = B ∧ ZMod.val i = 0 := by
      rcases hm with hm | hm
      · obtain ⟨hk, -⟩ := hI.newInd hfT hm
        exact iprj_key_block hI.wf hI.decoded hI.held hI.formerRec hbh (val_lt_uint64 i)
          (by rw [← hx]; exact hk)
      · obtain ⟨j', hj', hk⟩ := hI.newCtor hfC hm
        obtain ⟨hbB, hi0, -⟩ :=
          cprj_key_block hI.wf hI.decoded hI.held (hI.ctorRec j' hj') hbh hk
        exact ⟨hbB, toUInt64_zero_of_lt (val_lt_uint64 i) hi0⟩
    obtain ⟨hbB, hi0⟩ := hBi
    have hxa : Core.ixAddr pa = Core.iprjAddr B 0 := by
      rw [hx, hbB, hi0]
    obtain ⟨hpv, hiv, hsz⟩ := hI.formerLoad ev good hpa hld hxa
    exact hidx (by rw [← hiv, ZMod.val_zero])

/-- **The projection table's bundle at a new family with an index**: no table is stored for
it, each stored constructor's telescope is IxC's, and a constructor found at one of the block's
constructor addresses is new. -/
theorem blockTable_of_indexed {blk : List (ConstantInfo .anon)}
    {p₀ : Ix.Kernel.NativeParts .anon} {fam : NativeFam .anon}
    (hI : BlockInstall c new B cb ind caps)
    (hinv : Decl.PrefixInv.{u} c.E c.t c.lim c.env)
    (hfacts : NativeAtFacts c.env (appCtx c new).env blk ind.params.toNat ind.indices.toNat p₀
      fam)
    (hidx : ind.indices.toNat ≠ 0)
    (hlenA : fam.ctorsA.length = ind.ctors.size)
    (hctorsA : ∀ (j : Nat) (cA : ConstantVal .anon × Nat), fam.ctorsA[j]? = some cA →
      cA.1.name = Core.keyOf c.t (Core.cprjAddr B 0 j))
    (hnoTbl : ∀ tbl : Ix.Kernel.ProjTable .anon, ConstantInfo.projInfo tbl ∉ new)
    (hfreshT : c.env.find? (Core.keyOf c.t (Core.iprjAddr B 0)) = none)
    (hfreshTbl : c.env.find?
      (Ix.Kernel.projTableName (Core.keyOf c.t (Core.iprjAddr B 0))) = none) :
    BlockTable c new B ind := by
  obtain ⟨-, -, isRec, cvS', cvTa, caps', p₁, q, ctorsB, sortss, kinds, tfvs, trest, isorts,
    hfam, hInd, hp, hCtors, -, -, -, -, -, -, hTbl⟩ := hfacts
  subst hfam
  have hlenA' : ctorsB.length = ind.ctors.size := hlenA
  have hctorsA' : ∀ (j : Nat) (cA : ConstantVal .anon × Nat), ctorsB[j]? = some cA →
      cA.1.name = Core.keyOf c.t (Core.cprjAddr B 0 j) := hctorsA
  obtain ⟨hlA, hlS, hall⟩ := hCtors
  obtain ⟨hnewC, -⟩ := new_mem_of_checkNativeTable hTbl
  have hstoredCtor : ∀ cA ∈ ctorsB, (appCtx c new).env.find? cA.1.name =
      some (.ctorInfo cA.1 q.nP cA.2) := fun cA hcA => hI.newFind _ (hnewC cA hcA)
  exact
    { table := fun hi0 _ => absurd hi0 hidx
      newTable := fun tbl htbl => absurd htbl (hnoTbl tbl)
      ctorTele := by
        intro j hj cvC nP nF hf
        have hjA : j < ctorsB.length := by rw [hlenA']; exact hj
        obtain ⟨cA, hcA⟩ : ∃ cA, ctorsB[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjA⟩
        have hnm := hctorsA' j cA hcA
        have hfind := hstoredCtor cA (List.mem_of_getElem? hcA)
        rw [hnm] at hfind
        rw [hfind] at hf
        injection hf with hf
        injection hf with h1 h2 h3
        subst h1 h2 h3
        obtain ⟨c0, hc0⟩ : ∃ c0, q.ctors[j]? = some c0 :=
          ⟨_, List.getElem?_eq_getElem (by rw [← hlA]; exact hjA)⟩
        obtain ⟨hc2, sorts, -, hrun⟩ := hall j c0 cA hc0 hcA
        obtain ⟨-, -, -, htele, -⟩ := Decl.sumCtorRunJ_struct_facts hrun
        rw [hc2]
        exact htele
      ctorAt := by
        intro hbh j cv nP nF hf
        rcases find?_append_cases (env := c.env) new hf with hm | hold
        · exact hm
        · exfalso
          have hne : (appCtx c new).stored.κ (Core.cprjAddr B 0 j) ≠ Core.unresolvedKey := by
            intro he
            rw [he, hinv.unresolved] at hold
            exact nomatch hold
          have hk : (appCtx c new).stored.κ (Core.cprjAddr B 0 j) =
              Core.keyOf c.t (Core.cprjAddr B 0 j) := (appCtx c new).stored.key_eq hne
          rw [hk] at hold
          obtain ⟨ci, hci⟩ := hinv.ctor_ind_stored hbh hold
          rw [hfreshT] at hci
          exact nomatch hci
      fire := by
        intro tbl htbl _
        exfalso
        rcases find?_append_cases (env := c.env) new htbl with hm | hold
        · exact hnoTbl tbl hm
        · rw [hfreshTbl] at hold
          exact nomatch hold }

end Indexed

/-! ## The constructors' literal return at a store that holds the block -/

/-- **A family named by the block's former has the constructors' literal return at every store
that holds the block's records**: the record data its key names is the block's. -/
theorem famIxonRetHead_of_holds {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {B : _root_.Address} {ind : Ixon.Inductive} {cb : Ixon.Constant} (ht : t.check = .ok ())
    (hH : HoldsBlock E₀ E B cb ind) (hmuts : cb.info = .muts #[.indc ind])
    (hI : BlockCtorIxonRetHead cb ind) {fam : NativeFam .anon}
    (hT : fam.p.cvT.name = Core.keyOf t (Core.iprjAddr B 0)) : FamIxonRetHead t E fam := by
  intro P cm ip cb' ms ind' hname hP hcm hblk hms hmem
  have hkey : keyOf t P = Core.keyOf t (Core.iprjAddr B 0) := hname.symm.trans hT
  have hPB : P = Core.iprjAddr B 0 :=
    Assembly.keyOf_injective (x := P) (y := Core.iprjAddr B 0) ht
      ((LoadedReads.keyOf_eq t P).trans hkey)
  subst hPB
  have hcm' : cm = memberProjection B 0 (.indc ind) :=
    Option.some.inj
      ((((recordOf_eq_recordAt_of_decoded hH.decoded _).trans hP).symm).trans hH.former)
  subst hcm'
  have hipEq : (⟨(0 : Nat).toUInt64, B⟩ : Ixon.InductiveProj) = ip := by
    have hinfo0 : (memberProjection B 0 (.indc ind)).info =
        .iPrj ⟨(0 : Nat).toUInt64, B⟩ := rfl
    rw [hinfo0] at hcm
    exact Ixon.ConstantInfo.iPrj.inj hcm
  have hipb : ip.block = B := by
    subst hipEq
    rfl
  have hipi : ip.idx.toNat = 0 := by
    subst hipEq
    show ((0 : Nat).toUInt64).toNat = 0
    decide
  have hcb : cb' = cb := by
    have h1 : recordOf E B = some cb' := by
      rw [← hipb]
      exact (recordOf_eq_recordAt_of_decoded hH.decoded _).trans hblk
    exact Option.some.inj (h1.symm.trans hH.block)
  rw [hcb, hmuts] at hms
  have hms' : ms = #[.indc ind] := (Ixon.ConstantInfo.muts.inj hms).symm
  subst hms'
  rw [hipi] at hmem
  have e : (some (.indc ind) : Option Ixon.MutConst) = some (.indc ind') := hmem
  have hind : ind' = ind := (Ixon.MutConst.indc.inj (Option.some.inj e)).symm
  rw [hcb, hind]
  exact hI

/-! ## The install keeps the clause -/

/-- **The install of a block whose former is declared at a definition keeps the fold's clause
at the opened head trace**, at every store that holds the block's records, every limit and
every registry, registering its family (module docstring). -/
theorem AliasInstallOut.keeps {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {blk : List (ConstantInfo .anon)}
    {p₀ : Ix.Kernel.NativeParts .anon} {new : List (ConstantInfo .anon)}
    {fam : NativeFam .anon} {caps : IndCaps .anon}
    (ht : t.check = .ok ()) (hrec : BlockUnitRecord E₀ B cb ind)
    (hO : AliasInstallOut t E₀ env B cb ind blk p₀ new fam caps)
    {E : Ixon.Env} {lim : Option Nat} {Reg : NativeFam .anon → Prop}
    (hH : HoldsBlock E₀ E B cb ind)
    (hC : FoldClauseWith.{u} FormerOpenTraceAt t E lim env Reg) :
    FoldClauseWith.{u} FormerOpenTraceAt t E lim ⟨new ++ env.consts⟩
      (fun f => Reg f ∨ f = fam) := by
  have htwf : t.wf = true := hC.tableWf
  have hI := hO.install E lim hH
  have hext : Ix.Kernel.EnvExt env ⟨new ++ env.consts⟩ := hO.facts.envExt
  -- the names of the new constants
  have hnres : ∀ cn ∈ new, cn.name ≠ Core.unresolvedKey := by
    intro cn hcn
    obtain ⟨x, -, hn, -⟩ := hO.named cn hcn
    rw [hn]
    exact keyOf_ne_unresolvedKey t x
  have hres : ∀ (k : Core.KKey) (ci : ConstantInfo .anon),
      (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? k = some ci → env.find? k = none →
      k ≠ Core.unresolvedKey := by
    intro k ci hf hnone
    rcases find?_append_cases new hf with hm | hold
    · rw [← Core.WhnfAux.name_of_find hf]
      exact hnres ci hm
    · rw [hnone] at hold
      cases hold
  have hnoTblNew : ∀ tbl : Ix.Kernel.ProjTable .anon, ConstantInfo.projInfo tbl ∉ new := by
    intro tbl hm
    obtain ⟨x, -, hn, -⟩ := hO.named _ hm
    have h' : keyOf t x = Ix.Kernel.projTableName tbl.structName := hn.symm
    exact Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf t x) h'
  have hkeys₂ : HashKeyed t ⟨new ++ env.consts⟩ :=
    HashKeyed.append htwf hC.hashKeyed fun ci hci => by
      obtain ⟨x, -, hn, hsz⟩ := hO.named ci hci
      exact Or.inl ⟨x, hn, hsz⟩
  -- η stability, from IxC's store step
  have hnaKeys : ∀ ci ∈ blk, Decl.NonAuxKey ci.name := fun ci hci =>
    (hO.nonAux.1 ci (by simpa [IxVM.Consistency.installs, hO.pin] using hci)).1
  have heta : Decl.EtaStable ⟨new ++ env.consts⟩ :=
    (hO.facts.foldStoreInv hO.pin hnaKeys hC.foldStore).etaStable
  -- the family's key is fresh in the prefix, and so is its table's
  have hfreshT : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none := by
    obtain ⟨ci, hci, ci₀, hname, -⟩ :=
      hO.reads (Core.iprjAddr B 0) (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)
    have h := hO.fresh ci hci
    rw [hname] at h
    exact h
  have hbaseT : (Core.keyOf t (Core.iprjAddr B 0)).base = Core.keyOf t (Core.iprjAddr B 0) :=
    Decl.base_of_isBaseKey (Decl.isBaseKey_keyOf t _)
  have hfreshTbl : env.find?
      (Ix.Kernel.projTableName (Core.keyOf t (Core.iprjAddr B 0))) = none :=
    hC.auxRoot.fresh_of_base_none (by
      show env.find? (Core.keyOf t (Core.iprjAddr B 0)).base = none
      rw [hbaseT]
      exact hfreshT)
  -- the load contract at the new environment
  have hT : BlockTable ⟨E, env, t, lim⟩ new B ind :=
    blockTable_of_indexed (c := ⟨E, env, t, lim⟩) hI hC.prefixInv hO.facts hO.indexed hO.lenA
      hO.ctorNames hnoTblNew hfreshT hfreshTbl
  have hEta : BlockEta ⟨E, env, t, lim⟩ new := blockEta_of_indexed hI hO.indexed
  have hloads := storedLoads_append (c := ⟨E, env, t, lim⟩) hC.loads hext hnres hC.etaStable
    (hI.newLoads hT hEta)
  -- the family read off the store
  obtain ⟨htele, hlps, hsort⟩ := hO.facts.famStage
  have hrecA : Ix.Cert.recordAt E (Core.iprjAddr B 0) =
      some (memberProjection B 0 (.indc ind)) :=
    (recordOf_eq_recordAt_of_decoded hH.decoded _).symm.trans hH.former
  have hrecB : Ix.Cert.recordAt E B = some cb :=
    (recordOf_eq_recordAt_of_decoded hH.decoded _).symm.trans hH.block
  have h0 : ((0 : Nat).toUInt64).toNat = 0 := by decide
  have hrecord : ∃ (P : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj)
      (cb' : Ixon.Constant) (ms : Array Ixon.MutConst) (ind' : Ixon.Inductive),
      fam.p.cvT.name = keyOf t P ∧ Ix.Cert.recordAt E P = some cm ∧ cm.info = .iPrj ip ∧
      Ix.Cert.recordAt E ip.block = some cb' ∧ cb'.info = .muts ms ∧
      ms[ip.idx.toNat]? = some (.indc ind') ∧
      fam.p.nP = ind'.params.toNat ∧ fam.p.nIdx = ind'.indices.toNat ∧
      fam.ctorsA.length = ind'.ctors.size ∧
      (∀ (j : Nat) (cA : ConstantVal .anon × Nat), fam.ctorsA[j]? = some cA →
        cA.1.name = keyOf t (Core.cprjAddr ip.block ip.idx.toNat j)) ∧
      InLogic cb' ∧ fam.p.cvT.levelParams = List.range ind'.lvls.toNat := by
    refine ⟨Core.iprjAddr B 0, memberProjection B 0 (.indc ind), ⟨(0 : Nat).toUInt64, B⟩, cb,
      #[.indc ind], ind, hO.famName, hrecA, rfl, hrecB, hrec.muts, ?_, hO.nP, hO.nIdx, hO.lenA,
      ?_, hrec.logic, hO.famLevels⟩
    · show (#[Ixon.MutConst.indc ind])[((0 : Nat).toUInt64).toNat]? = some (.indc ind)
      rw [h0]
      rfl
    · intro j cA hcA
      show cA.1.name = Core.keyOf t (Core.cprjAddr B ((0 : Nat).toUInt64).toNat j)
      rw [h0]
      exact hO.ctorNames j cA hcA
  have hread : FamRead (fun _ _ => True) t E ⟨new ++ env.consts⟩ fam :=
    { stored := hO.stored
      lps := hlps
      tele := htele
      sort := hsort
      isProp := hO.isProp
      kinds := hO.kinds
      nodup := hO.nodupA
      ctorFields := hO.ctorFields
      record := hrecord
      retHead := famIxonRetHead_of_holds ht hH hrec.muts hO.retHead hO.famName
      noProj := hO.noProj
      link := trivial }
  have hnewCtor := newCtor_of_blockInstall (E := E) (B := B) (ind := ind) hC.tableWf hH.decoded
    hH.ctors hI.bounds.2.2 hO.lenA hO.famName hO.ctorNames hO.facts.newCtor
  exact hC.aliasInstall hO.facts hO.pin hO.nonAux hres hloads heta hkeys₂ hread hO.trace hnewCtor

/-! ## The step, stated once -/

/-- **The unit step of a block whose former is declared at a definition, stated once** (module
docstring). `Ec` and `lc` are the store and the limit the block's check is read at; `Stores` are
the stores the clause is kept at. At every environment that extends `envT`, has distinct names,
satisfies the clause at `Ec` and `lc` with a registry `Reg`, stores every used reference of the
record that is not one of its own constant addresses (unless the reference is no in-logic
constant address of the run's store) and stores none of the record's constant addresses: there
are fresh constants `new` with distinct names and one family `fam` such that, at every store in
`Stores`, every limit and every registry `Reg'`, the clause at `env` with `Reg'` gives the
clause at `new ++ env` with `Reg'` extended by `fam`; every constant of `new` is at the key of
a constant address of the record; and at each constant address of the record `new` holds a
constant at that address's key that stores a reading of the address over the run's records. -/
def AliasUnitStep (t : Ix.Kernel.RoleTable) (envT : Ix.Kernel.Env .anon) (E₀ : Ixon.Env)
    (Stores : Ixon.Env → Prop) (Ec : Ixon.Env) (lc : Option Nat) (B : _root_.Address)
    (cb : Ixon.Constant) : Prop :=
  ∀ (env : Ix.Kernel.Env .anon) (Reg : NativeFam .anon → Prop),
    (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
    FoldClauseWith.{u} FormerOpenTraceAt t Ec lc env Reg →
    (∀ x, UsedRef E₀ B x →
      (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf B cb x ∨ ¬ NeedOk E₀ x) →
    (∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none) →
    ∃ (new : List (ConstantInfo .anon)) (fam : NativeFam .anon),
      (new.map (·.name)).Nodup ∧ (∀ ci ∈ new, env.find? ci.name = none) ∧
      (∀ (E : Ixon.Env) (lim : Option Nat) (Reg' : NativeFam .anon → Prop), Stores E →
        FoldClauseWith.{u} FormerOpenTraceAt t E lim env Reg' →
        FoldClauseWith.{u} FormerOpenTraceAt t E lim ⟨new ++ env.consts⟩
          (fun f => Reg' f ∨ f = fam)) ∧
      (∀ ci ∈ new, ∃ x, ConstAddrOf B cb x ∧ ci.name = keyOf t x) ∧
      (∀ x, ConstAddrOf B cb x →
        ∃ ci ∈ new, ∃ ci₀, ci.name = keyOf t x ∧ Reads t E₀ x ci₀ ∧ StoredAs ci ci₀)

/-- **The typing fold's step**: the step of the unit against a store the clause is kept at, at
the limit of its check, for the part of the fold's clause beside the prefix invariant. -/
theorem AliasUnitStep.unitStep {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon}
    {E₀ E : Ixon.Env} {Stores : Ixon.Env → Prop} {lim : Option Nat} {B : _root_.Address}
    {cb : Ixon.Constant} (hE : Stores E)
    (h : AliasUnitStep.{u} t envT E₀ Stores E lim B cb) :
    UnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt t E) t envT E₀ E lim B cb := by
  intro env hext hnd hinv hX href hfresh
  obtain ⟨⟨⟨⟨Reg, hR⟩, hkeys⟩, haux⟩, hlv⟩ := hX
  have hC : FoldClauseWith.{u} FormerOpenTraceAt t E lim env Reg :=
    FoldClauseWith.of_prefix hinv hR hkeys haux hlv
  obtain ⟨new, fam, hnd', hfr, hkeep, hnamed, hreads⟩ := h env Reg hext hnd hC href hfresh
  have hC' := hkeep E lim Reg hE hC
  refine ⟨new, hnd', hfr, hC'.prefixInv, hC'.extra, hreads, ?_⟩
  intro ci hci
  obtain ⟨x, hx, hn⟩ := hnamed ci hci
  exact Or.inl ⟨x, hx, hn⟩

/-- **The step from the install's output** at each environment the step is asked at: the
clause is kept at every store that holds the block's records. -/
theorem aliasUnitStep_of_install {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon}
    {E₀ Ec : Ixon.Env} {lc : Option Nat} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} (ht : t.check = .ok ()) (hrec : BlockUnitRecord E₀ B cb ind)
    (hout : ∀ (env : Ix.Kernel.Env .anon) (Reg : NativeFam .anon → Prop),
      (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
      FoldClauseWith.{u} FormerOpenTraceAt t Ec lc env Reg →
      (∀ x, UsedRef E₀ B x →
        (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf B cb x ∨ ¬ NeedOk E₀ x) →
      (∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none) →
      ∃ (blk : List (ConstantInfo .anon)) (p₀ : Ix.Kernel.NativeParts .anon)
        (new : List (ConstantInfo .anon)) (fam : NativeFam .anon) (caps : IndCaps .anon),
        AliasInstallOut t E₀ env B cb ind blk p₀ new fam caps) :
    AliasUnitStep.{u} t envT E₀ (fun E => HoldsBlock E₀ E B cb ind) Ec lc B cb := by
  intro env Reg hext hnd hC href hfresh
  obtain ⟨blk, p₀, new, fam, caps, hO⟩ := hout env Reg hext hnd hC href hfresh
  refine ⟨new, fam, hO.nodup, hO.fresh,
    fun E lim Reg' hH hC' => hO.keeps ht hrec hH hC', ?_, hO.reads⟩
  intro ci hci
  obtain ⟨x, hx, hn, -⟩ := hO.named ci hci
  exact ⟨x, hx, hn⟩

end IxVM.Refinement.Typing
