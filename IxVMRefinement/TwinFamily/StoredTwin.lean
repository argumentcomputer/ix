import IxVMRefinement.TwinFamily.Row
import IxVMRefinement.FamilyGraph.ProducersStored
import IxVMRefinement.Binding.FamilyWitness

/-! # The twin row's stored case, at the binding witness's selected family record

A typing run may accept a second family record `A` of a block `B` that the witness's environment
already stores (`twin A = some B`, `fam B = none`). Its canonical record is not one of this run's
records: it is the family record the binding half installed for `B`, which the witness selects
by block (`Binding.StoredFamilies`, `famOf B = some rb`), position by position over the
flattened family (`FamilyOf.FamilyOfBlock R B cb ms rb crb rs flat`), stored whole with its
companions (`FamilyInstalled`), and in the record form the binding's family check leaves it in
(`Binding.StoredFamiliesRForm`). This module states the stored case against that choice and
proves it with the twin's per-member step.

* `StoredTwinCanon`: what the stored case consumes of the witness's choice at one block: the
  selected record, its family over the flattened family, its constant addresses stored, and the
  record installed. `storedTwinCanon_of_selected`, `storedTwinCanon_of_block`: from
  `StoredFamilies`.
* `StoredTwinStepFam RFormS L`: the stored case of the twin row restated: the canonical record
  is the witness's selected one, with the selected records' form `RFormS`.
* `TwinOnStoredFlat`: the positional identity across the two records. The stored record's
  flattened family is the one derived from the block, entry by entry with parameters and levels
  (`Binding.StoredFamiliesFlat`); the twin's own family check reads the twin's record as the
  block's family over the same entries.
* `TwinSeamStored RFormS`: what the circuit side hands for a twin of a stored family: the facts
  `TwinSeam` hands, with the canonical record supplied by the witness instead of by a family
  check of this run.
* `twinTargetConcl_of_parts`, `unitStepTwin_of_concl`: the twin step's target conclusion from
  the facts of the parts, and the twin's unit step from that conclusion at every handed
  environment; the two halves of `twinStepTarget_of_facts` and `unitStepTwin_of_installed`
  without the graph's canonical record.
* `storedTwinStepFam_of`: `StoredTwinStepFam RFormS L` from `LinkLaws L`, `TwinSeamStored RFormS`
  and `TwinOnStoredFlat`.
* `StoredTwinBlock`, `storedTwinUnitStep`, `storedTwinSteps_of`: how the restated row gives the
  composition's stored conjunct (`FamilySteps`' last), from the witness's stored families with
  their form and the block of each stored twin being a stored modeled block of the witness's
  store. -/

universe u

namespace IxVM.Refinement.Typing.TwinFamily

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Refinement.Decl (twinPosRulesJ)
open IxVM.Refinement.Typing.FamilyAlias (FamilyCallAtLim)
open IxVM.Refinement.Binding (StoredFamilies StoredFamiliesRForm StoredFamiliesFlat
  StoredFormPred storedFamily_of_clause)
open IxVM.Refinement.Binding.FamilyFlat (FlatEntry RecordFlat BlockDerivedFlat)
open IxVM.Refinement.Binding.FamilyOf (FamilyOfBlock)
open Ix.Kernel (ConstantInfo)
open Ix.Kernel.Semantics (DeclRecTwinRunJ TwinRecPart twinModels twinRecs NativeFam)
open Ix.Kernel.Model (HasModel)

set_option linter.unusedVariables false

/-! ## The witness's choice at one block -/

/-- **The stored family record of a block, as the witness selects it**: the selected record
(`famOf B = some rb`), the block's family over the flattened family in the witness's store, the
record's constant addresses stored by the witness's environment, and the record installed there
(each recursor with its model companion). -/
structure StoredTwinCanon (t : Ix.Kernel.RoleTable) (R : Ixon.Env) (envT : Ix.Kernel.Env .anon)
    (famOf : _root_.Address → Option _root_.Address) (B rb : _root_.Address)
    (crb : Ixon.Constant) : Prop where
  selected : famOf B = some rb
  family : ∃ (cb : Ixon.Constant) (ms rs : Array Ixon.MutConst) (es : List FlatEntry) (off : Nat),
    FamilyOfBlock R B cb ms rb crb rs (es.map FlatEntry.addr) ∧ RecordFlat t R rb crb rs es ∧
      BlockDerivedFlat t R B off es
  stored : ∀ x, ConstAddrOf rb crb x → StoredAt t envT x
  installed : FamilyInstalled t envT rb crb
  recs : ∀ cb, recordOf R B = some cb → Binding.StoredFamilyRecs t R envT B cb rb crb
  levelsParams : Binding.StoreLevelsParams t R
  route : Route.blockRoute R B = some true

/-- **Canonical loaded form of each stored recursor member** (`TwinMemberLoaded`), projected
from `StoredTwinCanon`. -/
theorem StoredTwinCanon.recLoaded {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {R : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    {famOf : _root_.Address → Option _root_.Address} {B rb : _root_.Address}
    {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    (h : StoredTwinCanon t R envT famOf B rb crb)
    (hcb : recordOf R B = some cb) (hms : cb.info = .muts ms) (hrs : crb.info = .muts rs)
    (p : Ixon.RecursorProj) (rc : Ixon.Recursor) (cv : Ix.Kernel.ConstantVal .anon)
    (mI rP : Nat) (rules₀ : List (Ix.Kernel.RecRule .anon)) (cv' : Ix.Kernel.ConstantVal .anon)
    (mI' rP' : Nat) (rules' : List (Ix.Kernel.RecRule .anon))
    (hp : p.block = rb) (hm : rs[p.idx.toNat]? = some (.recr rc))
    (hRR : RecReads t (recordOf R) (fun x => R.blobs.get? x) crb (blockSelf t rb rs)
      (keyOf t (memberAddr rb p.idx.toNat (.recr rc))) rc (.recInfo cv mI rP rules₀))
    (hf : envT.find? (keyOf t (memberAddr rb p.idx.toNat (.recr rc))) =
      some (.recInfo cv' mI' rP' rules')) :
    TwinMemberLoaded crb rs p rc cv.levelParams cv.type rules₀ cv' rules' :=
  (h.recs cb hcb).recLoaded ht hms hrs p rc cv mI rP rules₀ cv' mI' rP' rules' hp hm hRR hf

/-- **No stored recursor type mentions any recursor key of the family record**, projected from
`StoredTwinCanon`. -/
theorem StoredTwinCanon.recNoSelf {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {famOf : _root_.Address → Option _root_.Address}
    {B rb : _root_.Address} {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    (h : StoredTwinCanon t R envT famOf B rb crb)
    (hcb : recordOf R B = some cb) (hms : cb.info = .muts ms) (hrs : crb.info = .muts rs)
    {k j : Nat} {rc_k rc_j : Ixon.Recursor} {cv' : Ix.Kernel.ConstantVal .anon}
    {mI' rP' : Nat} {rules' : List (Ix.Kernel.RecRule .anon)}
    (hk : rs[k]? = some (.recr rc_k)) (hj : rs[j]? = some (.recr rc_j))
    (hf : envT.find? (keyOf t (memberAddr rb k (.recr rc_k))) =
      some (.recInfo cv' mI' rP' rules')) :
    cv'.type.mentionsConst (keyOf t (memberAddr rb j (.recr rc_j))) = false :=
  (h.recs cb hcb).recNoSelf hms hrs hk hj hf

/-- **Level-count agreement of each stored recursor member** at the block's elimination offset,
projected from `StoredTwinCanon`. -/
theorem StoredTwinCanon.recLvls {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {famOf : _root_.Address → Option _root_.Address}
    {B rb : _root_.Address} {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    {es : List FlatEntry} {off : Nat}
    (h : StoredTwinCanon t R envT famOf B rb crb)
    (hcb : recordOf R B = some cb) (hms : cb.info = .muts ms) (hrs : crb.info = .muts rs)
    (hBD : BlockDerivedFlat t R B off es)
    {ind₀ : Ixon.Inductive} {k : Nat} {rc : Ixon.Recursor}
    (hm0 : ms[0]? = some (.indc ind₀)) (hk : rs[k]? = some (.recr rc)) :
    rc.lvls.toNat = ind₀.lvls.toNat + off :=
  (h.recs cb hcb).recLvls hms hrs hBD hm0 hk

/-- **The witness's choice at a selected record.** -/
theorem storedTwinCanon_of_selected {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {famOf : _root_.Address → Option _root_.Address}
    {B rb : _root_.Address} {crb : Ixon.Constant} (h : StoredFamilies t R envT famOf)
    (hflat : StoredFamiliesFlat t R famOf)
    (hsel : famOf B = some rb) (hcrb : recordOf R rb = some crb)
    (hroute : Route.blockRoute R B = some true) :
    StoredTwinCanon t R envT famOf B rb crb := by
  obtain ⟨cb, crb', ms, rs, es, off, hf, hrf, hbd⟩ := hflat B rb hsel
  have e : crb' = crb := Option.some.inj (hf.record.record.symm.trans hcrb)
  rw [e] at hf hrf
  obtain ⟨hst, hinst⟩ := h.installed B rb crb hsel hcrb
  exact ⟨hsel, ⟨cb, ms, rs, es, off, hf, hrf, hbd⟩, hst, hinst,
    fun cb' hcb' => h.recs B rb cb' crb hsel hcb' hcrb, h.levelsParams, hroute⟩

/-- **The witness's choice at a stored modeled block** (the first import of the typing half,
`Binding.storedFamily_of_clause`). -/
theorem storedTwinCanon_of_block {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {famOf : _root_.Address → Option _root_.Address}
    {B : _root_.Address} {cb : Ixon.Constant} (h : StoredFamilies t R envT famOf)
    (hflat : StoredFamiliesFlat t R famOf)
    (hB : recordOf R B = some cb) (hroute : Route.blockRoute R B = some true)
    (hst : ∀ x, ConstAddrOf B cb x → StoredAt t envT x) :
    ∃ rb crb, StoredTwinCanon t R envT famOf B rb crb := by
  obtain ⟨rb, ms, crb, rs, flat, hsel, hf, -, -⟩ := storedFamily_of_clause h hB hroute hst
  exact ⟨rb, crb, storedTwinCanon_of_selected h hflat hsel hf.record.record hroute⟩

/-! ## The restated stored case -/

/-- **The twin's step at the witness's selected family record** (the stored case of
`FamilyTwinRow`, restated): for a twin `A` of a block `B` with no family record in the graph,
whose family record the witness selects (`StoredTwinCanon`), with every selected record in the
form `RFormS`, the twin's step with `rb` as its canonical record. -/
def StoredTwinStepFam (RFormS : StoredFormPred)
    (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) : Prop :=
  ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
    (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
    (rank : _root_.Address → Nat), Claim.TopWalk calls t seeds E₀ lim Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon) (E : Ixon.Env)
      (fam twin : _root_.Address → Option _root_.Address)
      (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
      FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner →
      StepCtx.{u} calls t R envT E₀ E →
      ∀ famOf : _root_.Address → Option _root_.Address, StoredFamiliesRForm RFormS t R famOf →
      ∀ (A : _root_.Address) (c : Ixon.Constant) (B rb : _root_.Address) (crb : Ixon.Constant),
        Walked Top Inner A → recordOf E₀ A = some c → InLogic c → twin A = some B →
        fam B = none → StoredTwinCanon t R envT famOf B rb crb →
        UnitStepTwin.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
          t envT E₀ E lim A c rb crb

/-- **The positional identity across the two records**: a block of recursors `rb'` that a family
check of the block `B` in the run accepted, at the run's binding `bAddr`, is the block's family
over the stored record's flattened family, entry by entry with parameters and levels. The stored
record's entries `es` are derived from the block (`BlockDerivedFlat`, at the block's elimination
offset `off`) and read off the record (`RecordFlat`); the twin's own family check asserts the same
of the twin's record in the run's store (`check_nested_aux` with the changed `aux_all_in`, and
`check_recs`), and the two stores' readings of the block agree, so the twin's entries are `es`
(`FamilyFlat.blockDerivedFlat_unique`). Two auxiliaries over one container share an address and
differ in parameters or levels, so the entries, not the addresses, fix the positions. -/
def TwinOnStoredFlat : Prop :=
  ∀ (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (E₀ E R : Ixon.Env) (envT : Ix.Kernel.Env .anon) (B rb rb' : _root_.Address)
    (cb crb crb' : Ixon.Constant) (ms rs rs' : Array Ixon.MutConst)
    (es : List FlatEntry) (off : Nat) (lim : Option Nat) (cs : List (Call F)),
    t.check = .ok () → LoadedReads.RunStore calls E₀ → StepCtx.{u} calls t R envT E₀ E →
    FamilyOfBlock R B cb ms rb crb rs (es.map FlatEntry.addr) → RecordFlat t R rb crb rs es →
    BlockDerivedFlat t R B off es →
    FamRecRecord E₀ rb' crb' rs' → rs'.size ≠ 0 →
    FamilyCallAtLim calls bAddr t B rb' lim cs →
    FamilyOfBlock E₀ B cb ms rb' crb' rs' (es.map FlatEntry.addr) ∧ RecordFlat t E₀ rb' crb' rs' es

/-- **The circuit-side seam of the twin step for a stored family**, at the selected records' form
`RFormS`: `TwinSeam`'s facts, with the canonical record the witness's selected one (its family
over the flattened family in the witness's store, in the form `RFormS`) in place of a family
check of this run accepting it, and the twin on the same flattened family. -/
def TwinSeamStored (RFormS : StoredFormPred) : Prop :=
  ∀ (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (E₀ E R : Ixon.Env) (envT env : Ix.Kernel.Env .anon) (B rb rb' : _root_.Address)
    (cb crb crb' : Ixon.Constant) (ms rs rs' : Array Ixon.MutConst)
    (flat : List _root_.Address) (lim : Option Nat) (cs : List (Call F)),
    t.check = .ok () → LoadedReads.RunStore calls E₀ → StepCtx.{u} calls t R envT E₀ E →
    (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
    FamilyOfBlock R B cb ms rb crb rs flat → RFormS t R B rb →
    FamilyOfBlock E₀ B cb ms rb' crb' rs' flat →
    rs'.size ≠ 0 → rb' ≠ rb →
    FamilyCallAtLim calls bAddr t B rb' lim cs →
    Decl.PrefixInv.{u} E t lim env →
    (∀ x, UsedRef E₀ rb' x →
      (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf rb' crb' x ∨ ¬ NeedOk E₀ x) →
    FamilyInstalled t env rb crb →
    Binding.StoredFamilyRecs t R env B cb rb crb →
    (∀ x, ConstAddrOf rb' crb' x → env.find? (keyOf t x) = none) →
    (∀ x, ConstAddrOf rb' crb' x → Decl.KeyFree (keyOf t x)) →
    ∃ ds : List Decl.TwinMemberData,
      TwinDeclReads t E₀ rb' crb' (ds.map fun d => .recInfo d.cvW d.mI d.rP d.rulesW) ∧
      TwinPartsFacts t env rb crb (Decl.mkTwinRecParts env ds)
        (Decl.twinPeerRename (Decl.mkTwinRecParts env ds)) ∧
      TwinLoadFacts t E₀ env rb' crb' (Decl.mkTwinRecParts env ds) ∧
      ∀ w ∈ Decl.mkTwinRecParts env ds, ∀ (a : _root_.Address) (cHost : Ixon.Constant)
        (rc : Ixon.Recursor) (n : Nat) (p : _root_.Address) (cmP : Ixon.Constant)
        (ipP : Ixon.InductiveProj),
        w.cvW'.name = keyOf t a → RecHostAt E a cHost rc →
        recMotiveCarrierAt cHost rc 0 n = some p →
        Ix.Cert.recordAt E p = some cmP → cmP.info = .iPrj ipP → ¬ NativeAt E ipP.block

/-! ## The twin step from the facts of its parts, whatever supplies the canonical record -/

/-- **The twin step's target conclusion from the facts of the parts**: the second record's
declaration as read, IxC's twin record, each member stored as its reading with a model companion,
the companions and the reload after the step. The canonical record enters only through the facts
and `FamilyInstalled` (the proof of `twinStepTarget_of_facts`, after its seam). -/
theorem twinTargetConcl_of_parts {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {env : Ix.Kernel.Env .anon} {lim : Option Nat}
    {rb rb' : _root_.Address} {crb crb' : Ixon.Constant} {rs' : Array Ixon.MutConst}
    (ht : t.check = .ok ()) (hSS : StepStore calls t E₀ E) (hrb' : FamRecRecord E₀ rb' crb' rs')
    (hsz : rs'.size ≠ 0) (hinv : Decl.PrefixInv.{u} E t lim env) (haux : Decl.AuxRootSynced env)
    (hinst : FamilyInstalled t env rb crb)
    (hfresh : ∀ x, ConstAddrOf rb' crb' x → env.find? (keyOf t x) = none)
    (hparts : ∃ ds : List Decl.TwinMemberData,
      TwinDeclReads t E₀ rb' crb' (ds.map fun d => .recInfo d.cvW d.mI d.rP d.rulesW) ∧
      TwinPartsFacts t env rb crb (Decl.mkTwinRecParts env ds)
        (Decl.twinPeerRename (Decl.mkTwinRecParts env ds)) ∧
      TwinLoadFacts t E₀ env rb' crb' (Decl.mkTwinRecParts env ds)) :
    ∃ (blk : List (ConstantInfo .anon)) (env₂ : Ix.Kernel.Env .anon),
      TwinDeclReads t E₀ rb' crb' blk ∧
      DeclRecTwinRunJ twinPosRulesJ env blk env₂ ∧
      (∀ ci ∈ blk, ∃ c, env₂.find? ci.name = some c ∧ StoredAs c ci) ∧
      (∀ ci ∈ blk, HasModel env₂ ci.name) ∧
      Decl.CoreCompanions ⟨E, env₂, t, lim⟩ ∧
      (∀ ci, env₂.find? ci.name = some ci → env.find? ci.name = none →
        ∀ x, ci.name = keyOf t x → Decl.ReloadsAs E t env₂ ci) := by
  obtain ⟨ds, hreads, hF, hLd⟩ := hparts
  -- the parts copy the companions the environment stores
  have hmodel : ∀ w ∈ Decl.mkTwinRecParts env ds, ∀ cvm mval hint,
      env.find? (Ix.Kernel.auxKey w.kC .model) = some (.defnInfo cvm mval hint) →
        w.model? = some (cvm, mval, hint) := by
    intro w hw cvm mval hint h
    unfold Decl.mkTwinRecParts at hw
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp hw
    exact Decl.lookupModelInfo?_eq_some.mpr h
  -- the block is the parts' declared recursors
  have hblock : ds.map (fun d => ConstantInfo.recInfo d.cvW d.mI d.rP d.rulesW) =
      (Decl.mkTwinRecParts env ds).map (fun w => .recInfo w.cvW w.mI w.rP w.rulesW) := by
    unfold Decl.mkTwinRecParts
    simp only [List.map_map]
    rfl
  obtain ⟨ws, hws⟩ : ∃ ws, ws = Decl.mkTwinRecParts env ds := ⟨_, rfl⟩
  rw [← hws] at hF hLd hmodel hblock
  obtain ⟨blk, hb⟩ : ∃ blk, blk = ds.map (fun d => ConstantInfo.recInfo d.cvW d.mI d.rP d.rulesW) :=
    ⟨_, rfl⟩
  rw [← hb] at hreads hblock
  -- each part's name is the key of a constant address of the second record
  have hkeyOf : ∀ w ∈ ws, ∃ x, ConstAddrOf rb' crb' x ∧ w.cvW.name = keyOf t x := by
    intro w hw
    have hci : ConstantInfo.recInfo w.cvW w.mI w.rP w.rulesW ∈ blk := by
      rw [hblock]
      exact List.mem_map.mpr ⟨w, hw, rfl⟩
    obtain ⟨x, hx, hn, -⟩ := hreads.2.1 _ hci
    exact ⟨x, hx, hn⟩
  have hname_eq : ∀ w ∈ ws, w.cvW'.name = w.cvW.name := fun w hw => (hF.front w hw).name_eq
  have hnd : (ws.map (·.cvW.name)).Nodup := by
    have h := hreads.1
    rw [hblock, List.map_map] at h
    exact h
  have hnames : ((twinRecs ws ++ twinModels ws).map (·.name)).Nodup :=
    Decl.twinRecs_append_twinModels_nodup hnd hname_eq fun w hw k tk h => by
      obtain ⟨x, -, hn⟩ := hkeyOf w hw
      exact keyOf_nonAux t x k tk (hn.symm.trans h)
  have hfresh₂ : ∀ ci ∈ twinRecs ws ++ twinModels ws, env.find? ci.name = none :=
    Decl.twinRecs_append_twinModels_fresh hname_eq
      (fun w hw => by
        obtain ⟨x, hx, hn⟩ := hkeyOf w hw
        rw [hn]
        exact hfresh x hx)
      (fun w hw _ => by
        obtain ⟨x, hx, hn⟩ := hkeyOf w hw
        rw [hn]
        apply haux.fresh_of_base_none
        show env.find? (keyOf t x).base = none
        rw [keyOf_base]
        exact hfresh x hx)
  -- the record has a member, whose constant address the block reads
  have hblk : blk ≠ [] := by
    obtain ⟨m, hm⟩ : ∃ m, rs'[0]? = some m := ⟨rs'[0], by simp [Nat.pos_of_ne_zero hsz]⟩
    obtain ⟨ci, hci, -⟩ := hreads.2.2 _ (Or.inr ⟨rs', 0, m, hrb'.muts, hm, Or.inl rfl⟩)
    exact List.ne_nil_of_mem hci
  -- each checked twin recursor reloads after the step
  have hrelW : ∀ w ∈ ws, Decl.ReloadsAs E t ⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩
      (.recInfo w.cvW' w.mI w.rP w.rulesW') := by
    refine twinMember_reloads ht hSS hrb' hreads hblock hF.front hLd
      (fun k hk => find_isSome_append (find_isSome_append hk (twinModels ws)) (twinRecs ws))
      fun ci hci => ?_
    rw [hblock] at hci
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hci
    have hmem : ConstantInfo.recInfo w.cvW' w.mI w.rP w.rulesW' ∈
        twinRecs ws ++ (twinModels ws ++ env.consts) :=
      List.mem_append_left _ (List.mem_map.mpr ⟨w, hw, rfl⟩)
    have h := find_isSome_of_mem (env := ⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩) hmem
    have hn : (ConstantInfo.recInfo w.cvW' w.mI w.rP w.rulesW').name =
        (ConstantInfo.recInfo w.cvW w.mI w.rP w.rulesW).name := (hF.front w hw).name_eq
    rw [hn] at h
    exact h
  obtain ⟨hrun, hstored, hmodel, hcomp, hrel⟩ :=
    twinTarget_of_facts (lim := lim) hF hblock hblk hnames hfresh₂ hmodel hinst hinv.companions
      (twinRecs_recNotKAt hSS hrb' hreads hblock hF.front hLd) hrelW
  exact ⟨blk, _, hreads, hrun, hstored, hmodel, hcomp, hrel⟩

/-- **The twin's unit step from the target's conclusion at every handed environment**, and the
keeping of the clause (the proof of `unitStepTwin_of_installed`, after its target). -/
theorem unitStepTwin_of_concl {X : Ix.Kernel.Env .anon → Prop} {t : Ix.Kernel.RoleTable}
    {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env} {lim : Option Nat} {A rb : _root_.Address}
    {c crb : Ixon.Constant} (ht : t.check = .ok ())
    (hconcl : ∀ env : Ix.Kernel.Env .anon, (∀ ci ∈ envT.consts, ci ∈ env.consts) →
      (env.consts.map (·.name)).Nodup → Decl.PrefixInv.{u} E t lim env → X env →
      (∀ x, UsedRef E₀ A x →
        (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x ∨ ¬ NeedOk E₀ x) →
      (∀ x, ConstAddrOf A c x → env.find? (keyOf t x) = none) →
      ∃ (blk : List (ConstantInfo .anon)) (env₂ : Ix.Kernel.Env .anon),
        TwinDeclReads t E₀ A c blk ∧
        DeclRecTwinRunJ twinPosRulesJ env blk env₂ ∧
        (∀ ci ∈ blk, ∃ c', env₂.find? ci.name = some c' ∧ StoredAs c' ci) ∧
        (∀ ci ∈ blk, HasModel env₂ ci.name) ∧
        Decl.CoreCompanions ⟨E, env₂, t, lim⟩ ∧
        (∀ ci, env₂.find? ci.name = some ci → env.find? ci.name = none →
          ∀ x, ci.name = keyOf t x → Decl.ReloadsAs E t env₂ ci) ∧
        NewRecNotNative t E env env₂)
    (hkeep : TwinStepKeeps.{u} X t envT E₀ E lim A c) :
    UnitStepTwin.{u} X t envT E₀ E lim A c rb crb := by
  intro env hext hnd hinv hX href hrbS hfresh
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  obtain ⟨blk, env₂, hreads, hrun, hstored, hmodel, hcomp, hrel, hnotNat⟩ :=
    hconcl env hext hnd hinv hX href hfresh
  obtain ⟨hinv₂, hX₂⟩ :=
    hkeep env env₂ blk hext hnd hinv hX href hfresh hreads hrun hstored hmodel hcomp hrel hnotNat
  obtain ⟨ws, henv, hnd₂, hfr₂, hnames, hrecs, hmods⟩ := twinRun_parts hrun
  subst henv
  have hrecName : ∀ ci ∈ twinRecs ws, ∃ ci₀ ∈ blk, ci₀.name = ci.name := by
    intro ci hci
    have hm : ci.name ∈ blk.map (·.name) := by
      rw [← hnames]
      exact List.mem_map.mpr ⟨ci, hci, rfl⟩
    obtain ⟨ci₀, hci₀, he⟩ := List.mem_map.mp hm
    exact ⟨ci₀, hci₀, he⟩
  refine ⟨twinRecs ws ++ twinModels ws, hnd₂, hfr₂, hinv₂, hX₂, ?_, ?_⟩
  · intro x hx
    obtain ⟨ci₀, hci₀, hn₀⟩ := hreads.2.2 x hx
    obtain ⟨x', hx', hn', hrd⟩ := hreads.2.1 ci₀ hci₀
    have hxx : x' = x := keyOf_inj hroles (hn'.symm.trans hn₀)
    rw [hxx] at hrd
    obtain ⟨c', hc', hsa⟩ := hstored ci₀ hci₀
    rcases find?_append_cases (twinRecs ws ++ twinModels ws) hc' with hm | hold
    · refine ⟨c', hm, ci₀, ?_, hrd, hsa⟩
      rw [Core.WhnfAux.name_of_find hc', hn₀]
    · rw [hn₀, hfresh x hx] at hold
      cases hold
  · intro ci hci
    rcases List.mem_append.mp hci with hr | hmo
    · obtain ⟨ci₀, hci₀, he⟩ := hrecName ci hr
      obtain ⟨x, hx, hn, -⟩ := hreads.2.1 ci₀ hci₀
      exact Or.inl ⟨x, hx, he.symm.trans hn⟩
    · obtain ⟨ci', -, hk, -⟩ := hmods ci hmo
      exact Or.inr ⟨ci'.name, .model, hk⟩

/-! ## The stored case -/

/-- **The stored case of the twin row, at the witness's selected family record**, from the
twin's per-member seam for a stored family and the positional identity across the two records.
The run gives the twin's record and its family check (`FamilyRun.graph.twinRecord`,
`FamilyRun.checks`); the witness's choice gives the canonical record, its family over the
flattened family, its form and its installation (carried to every handed environment,
`familyInstalled_of_ext`); the twin is not the selected record, whose constant addresses the
witness stores, while the step is asked where the twin's are not stored. -/
theorem storedTwinStepFam_of {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {RFormS : StoredFormPred}
    (hseam : TwinSeamStored.{u} RFormS) (hpos : TwinOnStoredFlat.{u}) :
    StoredTwinStepFam.{u} RFormS L := by
  intro calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR hctx famOf hRF
    A c B rb crb hW hc hlog htw hnone hcanon
  obtain ⟨bAddrW, hWc, hG⟩ := hWalk
  have ht : t.check = .ok () := hWc.check_ok
  obtain ⟨cb, ms, rs, es, off, hfam, hrf, hbd⟩ := hcanon.family
  -- the twin's record
  obtain ⟨c₀, rs', hA₀, hsz⟩ := hFR.graph.twinRecord A B htw
  have hA : FamRecRecord E₀ A c rs' := by
    have e : c₀ = c := Option.some.inj (hA₀.record.symm.trans hc)
    rw [← e]
    exact hA₀
  -- the twin's family check, and its positions: the stored record's
  obtain ⟨bAddr, hC⟩ := hFR.checks
  obtain ⟨cs, hcall⟩ := hC.twinCall A B htw
  have hflatA : FamilyOfBlock E₀ B cb ms A c rs' (es.map FlatEntry.addr) :=
    (hpos calls bAddr t E₀ E R envT B rb A cb crb c ms rs rs' es off lim cs ht hWc.runStore hctx
      hfam hrf hbd hA hsz hcall).1
  generalize es.map FlatEntry.addr = flat at hfam hflatA
  refine unitStepTwin_of_concl ht ?_
    (twinStepKeeps_foldExtra (t := t) (envT := envT) (E₀ := E₀) (E := E) (lim := lim) hL
      fun x hx => constAddr_hash_size_of_block hA.muts hx).and_familyRecsModeled
  intro env hext hnd hinv hX href hfresh
  -- a step is asked only at an environment that extends the witness's and stores none of the
  -- twin's constant addresses, so none of them is the witness's
  have hns : ∀ x, ConstAddrOf A c x → ¬ StoredAt t envT x := by
    intro x hx hst
    obtain ⟨ci, hci, hname⟩ := hst
    have hs : (env.find? (keyOf t x)).isSome = true :=
      find_isSome_of_storedAt ⟨ci, hext ci hci, hname⟩
    rw [hfresh x hx] at hs
    simp at hs
  -- so the twin is not the selected record, whose constant addresses the witness stores
  have hne : A ≠ rb := by
    intro e
    obtain ⟨m, hm⟩ : ∃ m, rs'[0]? = some m := ⟨rs'[0], by simp [Nat.pos_of_ne_zero hsz]⟩
    have hx0 : ConstAddrOf A c (memberAddr A 0 m) := Or.inr ⟨rs', 0, m, hA.muts, hm, Or.inl rfl⟩
    have hcc : c = crb := by
      have h₁ := hctx.runRecord A c hc
      have h₂ := hctx.recordsFor.2.1 rb crb hfam.record.record
      rw [e] at h₁
      exact Option.some.inj (h₁.symm.trans h₂)
    have hx1 : ConstAddrOf rb crb (memberAddr A 0 m) := by
      rw [← e, ← hcc]
      exact hx0
    exact hns _ hx0 (hcanon.stored _ hx1)
  have hinst : FamilyInstalled t env rb crb := familyInstalled_of_ext hext hnd hcanon.installed
  have hrecs : Binding.StoredFamilyRecs t R env B cb rb crb :=
    (hcanon.recs cb hfam.block.record).mono_env hext hnd
  have hkey : ∀ x, ConstAddrOf A c x → Decl.KeyFree (keyOf t x) :=
    fun x hx => keyFree_of_not_stored hctx.shape ht (hns x hx)
  obtain ⟨ds, hreads, hF, hLd, hnotNat⟩ :=
    hseam calls bAddr t E₀ E R envT env B rb A cb crb c ms rs rs' flat lim cs ht hWc.runStore
      hctx hext hnd hfam (hRF B rb hcanon.selected) hflatA hsz hne hcall hinv href hinst hrecs
      hfresh hkey
  have hmodel : ∀ w ∈ Decl.mkTwinRecParts env ds, ∀ cvm mval hint,
      env.find? (Ix.Kernel.auxKey w.kC .model) = some (.defnInfo cvm mval hint) →
        w.model? = some (cvm, mval, hint) := by
    intro w hw cvm mval hint h
    unfold Decl.mkTwinRecParts at hw
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp hw
    exact Decl.lookupModelInfo?_eq_some.mpr h
  have hblock : ds.map (fun d => ConstantInfo.recInfo d.cvW d.mI d.rP d.rulesW) =
      (Decl.mkTwinRecParts env ds).map (fun w => .recInfo w.cvW w.mI w.rP w.rulesW) := by
    unfold Decl.mkTwinRecParts
    simp only [List.map_map]
    rfl
  obtain ⟨ws, hws⟩ : ∃ ws, ws = Decl.mkTwinRecParts env ds := ⟨_, rfl⟩
  rw [← hws] at hF hLd hmodel hblock hnotNat
  obtain ⟨blk, hb⟩ : ∃ blk, blk = ds.map (fun d => ConstantInfo.recInfo d.cvW d.mI d.rP d.rulesW) :=
    ⟨_, rfl⟩
  rw [← hb] at hreads hblock
  have hkeyOf : ∀ w ∈ ws, ∃ x, ConstAddrOf A c x ∧ w.cvW.name = keyOf t x := by
    intro w hw
    have hci : ConstantInfo.recInfo w.cvW w.mI w.rP w.rulesW ∈ blk := by
      rw [hblock]; exact List.mem_map.mpr ⟨w, hw, rfl⟩
    obtain ⟨x, hx, hn, -⟩ := hreads.2.1 _ hci
    exact ⟨x, hx, hn⟩
  have hname_eq : ∀ w ∈ ws, w.cvW'.name = w.cvW.name := fun w hw => (hF.front w hw).name_eq
  have hnd₂ : (ws.map (·.cvW.name)).Nodup := by
    have h := hreads.1; rw [hblock, List.map_map] at h; exact h
  have hnames : ((twinRecs ws ++ twinModels ws).map (·.name)).Nodup :=
    Decl.twinRecs_append_twinModels_nodup hnd₂ hname_eq fun w hw k tk h => by
      obtain ⟨x, -, hn⟩ := hkeyOf w hw; exact keyOf_nonAux t x k tk (hn.symm.trans h)
  have hfresh₂ : ∀ ci ∈ twinRecs ws ++ twinModels ws, env.find? ci.name = none :=
    Decl.twinRecs_append_twinModels_fresh hname_eq
      (fun w hw => by obtain ⟨x, hx, hn⟩ := hkeyOf w hw; rw [hn]; exact hfresh x hx)
      (fun w hw _ => by
        obtain ⟨x, hx, hn⟩ := hkeyOf w hw
        rw [hn]
        apply hX.1.1.2.fresh_of_base_none
        show env.find? (keyOf t x).base = none
        rw [keyOf_base]; exact hfresh x hx)
  have hblk : blk ≠ [] := by
    obtain ⟨m, hm⟩ : ∃ m, rs'[0]? = some m := ⟨rs'[0], by simp [Nat.pos_of_ne_zero hsz]⟩
    obtain ⟨ci, hci, -⟩ := hreads.2.2 _ (Or.inr ⟨rs', 0, m, hA.muts, hm, Or.inl rfl⟩)
    exact List.ne_nil_of_mem hci
  have hrelW : ∀ w ∈ ws, Decl.ReloadsAs E t ⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩
      (.recInfo w.cvW' w.mI w.rP w.rulesW') := by
    refine twinMember_reloads ht hctx.toStepStore hA hreads hblock hF.front hLd
      (fun k hk => find_isSome_append (find_isSome_append hk (twinModels ws)) (twinRecs ws))
      fun ci hci => ?_
    rw [hblock] at hci
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hci
    have hmem : ConstantInfo.recInfo w.cvW' w.mI w.rP w.rulesW' ∈
        twinRecs ws ++ (twinModels ws ++ env.consts) :=
      List.mem_append_left _ (List.mem_map.mpr ⟨w, hw, rfl⟩)
    have h := find_isSome_of_mem (env := ⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩) hmem
    have hn : (ConstantInfo.recInfo w.cvW' w.mI w.rP w.rulesW').name =
        (ConstantInfo.recInfo w.cvW w.mI w.rP w.rulesW).name := (hF.front w hw).name_eq
    rw [hn] at h
    exact h
  obtain ⟨hrun, hstored, hmodel₂, hcomp, hrel⟩ :=
    twinTarget_of_facts (lim := lim) hF hblock hblk hnames hfresh₂ hmodel hinst hinv.companions
      (twinRecs_recNotKAt hctx.toStepStore hA hreads hblock hF.front hLd) hrelW
  exact ⟨blk, _, hreads, hrun, hstored, hmodel₂, hcomp, hrel, newRecNotNative_of_twinParts hnotNat⟩

/-! ## What the composition consumes -/

/-- **The block of a twin with no family record in the graph is a stored modeled block of the
witness's store**: its record in the store, the store's dispatch answering the modeled route,
and its constant addresses stored by the witness's environment. -/
def StoredTwinBlock (t : Ix.Kernel.RoleTable) (R : Ixon.Env) (envT : Ix.Kernel.Env .anon)
    (fam twin : _root_.Address → Option _root_.Address) : Prop :=
  ∀ rb' B, twin rb' = some B → fam B = none →
    ∃ cb, recordOf R B = some cb ∧ Route.blockRoute R B = some true ∧
      ∀ x, ConstAddrOf B cb x → StoredAt t envT x

/-- **A stored twin's unit step** from the restated row: the witness selects the block's
family record (`storedTwinCanon_of_block`), whose constant addresses it stores, so the twin's
step is a plain step (`unitStep_of_twin_stored`). -/
theorem storedTwinUnitStep {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {RFormS : StoredFormPred} (hrow : StoredTwinStepFam.{u} RFormS L)
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address}
    {E₀ : Ixon.Env} {lim : Option Nat} {Top : _root_.Address → Prop}
    {rank : _root_.Address → Nat} (hWalk : Claim.TopWalk calls t seeds E₀ lim Top rank)
    {R : Ixon.Env} {envT : Ix.Kernel.Env .anon} {E : Ixon.Env}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hFR : FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner)
    (hctx : StepCtx.{u} calls t R envT E₀ E)
    {famOf : _root_.Address → Option _root_.Address} (hSF : StoredFamilies t R envT famOf)
    (hflat : StoredFamiliesFlat t R famOf) (hRF : StoredFamiliesRForm RFormS t R famOf)
    {A : _root_.Address} {c : Ixon.Constant} {B : _root_.Address} (hW : Walked Top Inner A)
    (hc : recordOf E₀ A = some c) (hlog : InLogic c) (htw : twin A = some B)
    (hnone : fam B = none) {cb : Ixon.Constant} (hB : recordOf R B = some cb)
    (hroute : Route.blockRoute R B = some true)
    (hst : ∀ x, ConstAddrOf B cb x → StoredAt t envT x) :
    UnitStep.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
      t envT E₀ E lim A c := by
  obtain ⟨rb, crb, hcanon⟩ := storedTwinCanon_of_block hSF hflat hB hroute hst
  exact unitStep_of_twin_stored hcanon.stored
    (hrow calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR hctx famOf hRF A c
      B rb crb hW hc hlog htw hnone hcanon)

/-- **The composition's stored conjunct from the restated row** (`FamilySteps`' last conjunct,
at one walk and witness): every stored twin's unit step, given the witness's stored families with
their form and that the block of each stored twin is a stored modeled block of its store. -/
theorem storedTwinSteps_of {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {RFormS : StoredFormPred} (hrow : StoredTwinStepFam.{u} RFormS L)
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address}
    {E₀ : Ixon.Env} {lim : Option Nat} {Top : _root_.Address → Prop}
    {rank : _root_.Address → Nat} (hWalk : Claim.TopWalk calls t seeds E₀ lim Top rank)
    {R : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hFR : FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner)
    (hfams : ∃ famOf, StoredFamilies t R envT famOf ∧ StoredFamiliesFlat t R famOf ∧
      StoredFamiliesRForm RFormS t R famOf)
    (hblock : StoredTwinBlock t R envT fam twin) :
    ∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c B, Walked Top Inner A →
      recordOf E₀ A = some c → InLogic c → twin A = some B → fam B = none →
      UnitStep.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
        t envT E₀ E lim A c := by
  intro E hctx A c B hW hc hlog htw hnone
  obtain ⟨famOf, hSF, hflat, hRF⟩ := hfams
  obtain ⟨cb, hB, hroute, hst⟩ := hblock A B htw hnone
  exact storedTwinUnitStep hrow hWalk hFR hctx hSF hflat hRF hW hc hlog htw hnone hB hroute hst

end IxVM.Refinement.Typing.TwinFamily
