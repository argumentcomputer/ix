import IxVMRefinement.FamilyGraph.ProducersRoute
import IxVMRefinement.FamilyGraph.ProducersStoredFam
import IxVMRefinement.TwinFamily.CallReconBridge

/-! # Unconditional discharge of the family-graph obligation

Closes the typing half's family-graph obligation completely, without any `familyGraph` or `Pref`
hypothesis:

* `FamilyStepsFamFull`: `FamilyStepsFam` with `Ix.Kernel.EnvWF envT` and `BoundaryFacts.whole`
  threaded from `OverWFam`;
* `typing_skeleton_over_familyFamFull`, `composed_skeleton_over_familyWFamFull`: the typing half
  and composed statement supplying `EnvWF envT` (from `FoldClauseWith.prefixInv.store.store.wf`)
  and `BoundaryFacts.whole` (from `OverWFam.facts.1.1.whole`);
* `familyGraphRowInnerFamT_closed`: produces the full graph, inner checks, family checks, stored
  twin blocks, and canonical twin selection at any walk with `FamCallsModeled`, `EnvWF`, and
  `BoundaryFacts.whole` via `FamRunCtx.batchGives_of_run`;
* `familyStepsFamFull_closed`, `familySteps_closedWF`: builds `FamilyStepsFamFull` for
  `Claim.TopWalk calls` with no `familyGraph` premise (taking `FamilyTwinRowFam` or
  `FamilyTwinRowFamClosed`);
* `circuitComposed_of_partsFamInnerWT_closed`, `circuitComposed_of_partsFamInnerWT_closedWF`: the
  composed public statement `IxVM.Consistency.CircuitComposed` with `familyGraph` and `Pref`
  eliminated. -/

universe u

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)
open IxVM.Refinement.Binding
open IxVM.Refinement.Endpoint
open TwinFamily (FamilyRecsModeled FamilyInstalled StoredTwinBlock)
open FamilyAlias (FamilyCallAtLim)

set_option linter.unusedVariables false

/-- **Block-wholeness of a witness environment** over record stores for `R`
(`BoundaryFacts.whole`). -/
abbrev WitnessWhole (t : Ix.Kernel.RoleTable) (R : Ixon.Env) (envT : Ix.Kernel.Env .anon) : Prop :=
  ∀ E, RecordsFor R E →
    ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
      (envT.find? (keyOf t a)).isSome = true → Ix.Cert.recordAt E a = some c →
      Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E B = some cb → cb.info = .muts ms →
      BlockStored t envT B ms

/-- **`FamilyStepsFam` with witness well-formedness (`EnvWF`) and block-wholeness
(`BoundaryFacts.whole`)** threaded from `OverWFam`. -/
def FamilyStepsFamFull (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (calls : List (Call F))
    (Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop) : Prop :=
  ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon), TableShape.{u} t (fun _ => True) R envT →
      ∀ famOf, StoredFamilies t R envT famOf → RecordsAgree E₀ R →
      (∃ E, StepCtx.{u} calls t R envT E₀ E) →
      Ix.Kernel.EnvWF envT → WitnessWhole t R envT →
      ∃ (rank' : _root_.Address → Nat) (fam twin : _root_.Address → Option _root_.Address)
        (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
        Walk t seeds E₀ lim Top rank' ∧
        FamilyGraph t envT E₀ Top rank' fam twin adv Inner ∧
        (∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c, Top A → Unclaimed fam A →
          recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = none → twin A = none →
          UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim A c) ∧
        (∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c, Inner A → Unclaimed fam A →
          recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = none → twin A = none →
          UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim A c) ∧
        (∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c rb crb rs, Top A →
          recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = some rb →
          FamRecRecord E₀ rb crb rs →
          UnitStepFamily.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
            t envT E₀ E lim A c rb crb (adv A)) ∧
        (∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c B rb crb, Walked Top Inner A →
          recordOf E₀ A = some c → InLogic c → twin A = some B → fam B = some rb →
          recordOf E₀ rb = some crb →
          UnitStepTwin.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
            t envT E₀ E lim A c rb crb) ∧
        (∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c B, Walked Top Inner A →
          recordOf E₀ A = some c → InLogic c → twin A = some B → fam B = none →
          UnitStep.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
            t envT E₀ E lim A c)

/-- **The typing half over the fold's clause and the family graph**, threading `EnvWF envT` and
`BoundaryFacts.whole` from `OverWFam`. -/
theorem typing_skeleton_over_familyFamFull {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop}
    {calls : List (Call F)} {d : Digest} (hb : Bounded calls)
    (hclaim : ClaimExport Walk calls d) (hlim : WalkLim Walk)
    (hgraph : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      TopGraph t E₀ seeds Top rank)
    (hsteps : FamilyStepsFamFull.{u} L calls Walk) :
    TypingSpecOn.{u} (OverWFam.{u} L) calls d := by
  intro bytes c hde hdig hscope V seeds hseeds ctx hctx tb t hadm R envT hW
  by_cases hnc : CollisionWith V (bytes :: tb :: committedFootprint) R calls
  · exact Or.inl hnc
  · refine Or.inr ?_
    have ht : t.check = .ok () :=
      ((Ix.Kernel.Admission.admitBinding_ok_iff _ _ t).mp hadm).wellFormed
    have hextra : ∀ x ∈ committedFootprint, x ∈ bytes :: tb :: committedFootprint :=
      fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
    rcases hclaim bytes c hde hdig hscope V seeds hseeds ctx hctx tb t hadm with
      hcol | ⟨E₀, lim, Top, rank, hS, hWalk⟩
    · exact (hnc (Or.inl hcol)).elim
    · have hF : BoundaryFacts t (fun _ => True) R envT := hW.facts.1.1
      obtain ⟨Reg, hR⟩ := hW.facts.1.2
      obtain ⟨famOf, hSF⟩ := hW.facts.2
      have hc : Carried lim := carried_of_typingLim (hlim t seeds E₀ lim Top rank hWalk)
      obtain ⟨E_m, hM⟩ := merged_exists E₀ R
      have hctx_m : StepCtx.{u} calls t R envT E₀ E_m :=
        ⟨hW.shape,
          hM.recordsFor hS.loaded hS.decoded hW.shape.committed hextra hnc,
          fun a c h => hM.run_record hS.loaded hS.decoded hextra hnc h,
          fun a b h => hM.run_blob hS.loaded hnc h,
          fun env lim => hM.good hS.loaded hW.shape.zeroFree hextra hnc hb env t lim⟩
      have hEnvWF : Ix.Kernel.EnvWF envT :=
        (hR E_m hctx_m.recordsFor lim hc (limWithin_all t lim)).prefixInv.store.store.wf
      obtain ⟨rank', fam, twin, adv, Inner, hWalk', hFG, hTop, hInner, hFam, hTwin,
        hTwinStored⟩ := hsteps t seeds E₀ lim Top rank hWalk R envT hW.shape famOf hSF
          (records_agree hS.loaded hnc) ⟨E_m, hctx_m⟩ hEnvWF hF.whole
      exact typing_skeleton_core_family_modeled (X := fun E => FoldExtra.{u} L t E) hW.shape
        (fun E hE => (hR E hE lim hc (limWithin_all t lim)).prefixInv) hF.whole
        (fun E hE => (hR E hE lim hc (limWithin_all t lim)).extra) ht hb hextra hnc hS
        (hgraph t seeds E₀ lim Top rank' hWalk') hFG hTop hInner hFam hTwin hTwinStored

/-- **The composed statement with `EnvWF` and `BoundaryFacts.whole` threaded to the typing
half**. -/
theorem composed_skeleton_over_familyWFamFull {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    {Fam : BRun → Ix.Kernel.RoleTable → Nat → Ixon.Env → Ixon.Env →
      (_root_.Address → Option _root_.Address) → (_root_.Address → _root_.Address → Prop) →
      (_root_.Address → _root_.Address → Prop) → Prop}
    {Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop}
    {callsA callsB : List (Call F)} {dA dB : Digest}
    (bindingClaimExport : BindingClaimExportObs Run callsB dB)
    (basisGroups : BasisOverW.{u} L Run)
    (groupAdmissions : AdmitsChain Run) (groupAdmissionReads : AdmitsReadsChain Run)
    (groupFamilies : FamiliesChain Run Fam)
    (groupClosure : AtGroups Run fun ρ t g => ClosureStepOverFamilyW.{u} L ρ t g (Fam ρ t g))
    (groupWithoutRoleUnit : AtGroups Run (RoleFreeShapes.{u} L))
    (operationRoleUnit : AtGroups Run (RoleUnitStepOverW.{u} (· ∈ RoleOps.opRoles) L))
    (standardAxiomRoleUnit : AtGroups Run (RoleUnitStepOverW.{u} (· ∈ standardAxioms) L))
    (hb : Bounded callsA) (hclaimA : ClaimExport Walk callsA dA) (hlim : WalkLim Walk)
    (hgraph : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      TopGraph t E₀ seeds Top rank)
    (hstepsA : FamilyStepsFamFull.{u} L callsA Walk) :
    ComposedSpec.{u} callsA callsB dA dB :=
  binding_discharge
    (binding_skeleton_overW bindingClaimExport basisGroups groupAdmissions groupAdmissionReads
      groupFamilies groupClosure groupWithoutRoleUnit operationRoleUnit standardAxiomRoleUnit)
    (typing_skeleton_over_familyFamFull hb hclaimA hlim hgraph hstepsA)

/-- **Unconditional family-graph row with inner checks and exports** at any walk whose run
satisfies `FamCallsModeled`, against a well-formed witness storing blocks whole. -/
theorem familyGraphRowInnerFamT_closed (Pref : RunPref)
    {calls : List (Call F)} (hfamMod : FamCallsModeled calls)
    (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
    (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
    (rank : _root_.Address → Nat) (hWalk : Claim.TopWalk calls t seeds E₀ lim Top rank)
    (R : Ixon.Env) (envT : Ix.Kernel.Env .anon) (hshape : TableShape.{u} t (fun _ => True) R envT)
    (famOf : _root_.Address → Option _root_.Address) (hSF : StoredFamilies t R envT famOf)
    (hagree : RecordsAgree E₀ R) (hstore : ∃ E, StepCtx.{u} calls t R envT E₀ E)
    (hEnvWF : Ix.Kernel.EnvWF envT) (hWhole : WitnessWhole t R envT) :
    ∃ (rank' : _root_.Address → Nat) (fam twin : _root_.Address → Option _root_.Address)
      (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop)
      (bAddr : _root_.Address),
      Claim.TopWalk calls t seeds E₀ lim Top rank' ∧
      FamilyRun calls t envT E₀ lim Top rank' fam twin adv Inner ∧
      InnerChecked calls bAddr t envT E₀ lim Top rank' fam twin Inner ∧
      FamilyChecksAt calls bAddr t E₀ lim fam twin adv Inner ∧
      StoredTwinBlock t R envT fam twin ∧
      ∀ B rb rb', fam B = some rb → twin rb' = some B →
        RecBlock E₀ rb ∧ (Pref calls bAddr t E₀ lim B rb' → Pref calls bAddr t E₀ lim B rb) := by
  obtain ⟨bAddr, hW, hG⟩ := hWalk
  obtain ⟨E, hctx⟩ := hstore
  let K : FamRunCtx := ⟨calls, bAddr, t, E₀, lim, Top, envT, Pref calls bAddr t E₀ lim⟩
  have hB : BatchGives K :=
    FamRunCtx.batchGives_of_run hW hG hagree hctx hfamMod hEnvWF hWhole
  have hreads : StoredTwinReads K R := storedTwinReads_of_walk hW hG hB hagree hctx
  obtain ⟨rank', hR⟩ : ∃ rank', FamilyRanked K rank' :=
    ⟨_, familyRanked_of_edges hW
      (rankEdges_of hW hG hB hshape (FamRunCtx.famEdge_acyclic hW hG hB))⟩
  have hblock := storedTwinBlock_of_reads hB hagree hreads
  obtain ⟨hFR, -⟩ :=
    familyRun_of K hB hW (noBatchFields_of _ hW) hR (storedTwinField_of_block hSF hblock)
  have hWalk' : Claim.TopWalk calls t seeds E₀ lim Top rank' :=
    topWalk_of_edges ⟨bAddr, hW, hG⟩ hR.closed hR.owner
  exact ⟨rank', _, _, _, _, bAddr, hWalk', hFR, innerChecked_of_gives hWalk' hFR
    (FamRunCtx.checks_of _ hB) (innerGives_of_owed hW hG hB hshape (innerOwed_of_walk hW)),
    FamRunCtx.checks_of _ hB, hblock, fun B rb rb' hf ht => FamRunCtx.twin_canonical hf ht⟩

/-- **The typing half's premise at the witness with its stored families, with `familyGraph`
discharged unconditionally.** -/
theorem familyStepsFamFull_closed {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {RFormS : StoredFormPred}
    (storedForm : StoredFormAt.{u} RFormS)
    (innerSteps : InnerStepsChecked.{u} L) (familyBlock : FamilyBlockRow.{u} L)
    (familyTwin : TwinFamily.FamilyTwinRowFam.{u} RFormS L)
    (standaloneDefinition : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind = .defn)
    (standaloneTheoremOrOpaque : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind ≠ .defn)
    (standaloneRecursor : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ rc : Ixon.Recursor, c.info = .recr rc)
    (definitionBlock : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ DefnBlock ms)
    (nativeBlockTelescope : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind)
    (nativeBlockAlias : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtAlias t E₀ B cb ind)
    (nativeBlockOtherTelescope : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerTeleOther t E₀ B cb ind)
    (calls : List (Call F)) (hfamMod : FamCallsModeled calls) :
    FamilyStepsFamFull.{u} L calls (Claim.TopWalk calls) := by
  intro t seeds E₀ lim Top rank₀ hWalk₀ R envT hshape famOf hSF hagree hstore hEnvWF hWhole
  obtain ⟨rank, fam, twin, adv, Inner, bAddr, hWalk, hFR, hIC, -, hblock, htwin_canon⟩ :=
    familyGraphRowInnerFamT_closed (fun _ _ t E₀ _ B r => RFormS t E₀ B r) hfamMod
      t seeds E₀ lim Top rank₀ hWalk₀ R envT hshape famOf hSF hagree hstore hEnvWF hWhole
  exact ⟨rank, fam, twin, adv, Inner, hWalk, hFR.graph,
    topUnitSteps_family standaloneDefinition standaloneTheoremOrOpaque standaloneRecursor
      definitionBlock nativeBlockTelescope nativeBlockAlias nativeBlockOtherTelescope hWalk hFR,
    innerSteps calls t seeds E₀ lim Top rank hWalk R envT fam twin adv Inner bAddr hFR hIC,
    fun E => familyBlock calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR,
    fun E hctx A c B rb crb hW hc hlog htw hrb hcrb =>
      TwinFamily.familyTwinStep_graph_of_row familyTwin hWalk hFR hctx hW hc hlog htw hrb hcrb
        (htwin_canon B rb A hrb htw).1 (htwin_canon B rb A hrb htw).2,
    TwinFamily.storedTwinSteps_of (TwinFamily.storedTwinStepFam_of_row familyTwin) hWalk hFR
      ⟨famOf, hSF, hSF.flat, storedForm t R envT famOf hshape hSF⟩ hblock⟩

/-- **The public statement `IxVM.Consistency.CircuitComposed` with `familyGraph` and `Pref`
discharged unconditionally.** -/
theorem circuitComposed_of_partsFamInnerWT_closed
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {Run : List (Call F) → Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    {Fam : List (Call F) → BRun → Ix.Kernel.RoleTable → Nat → Ixon.Env → Ixon.Env →
      (_root_.Address → Option _root_.Address) → (_root_.Address → _root_.Address → Prop) →
      (_root_.Address → _root_.Address → Prop) → Prop}
    {RFormS : StoredFormPred}
    (bindingClaimExport :
      SourceSoundBounded fun calls d => BindingClaimExportObs (Run calls) calls d)
    (basisGroups : ∀ calls, BasisOverW.{u} L (Run calls))
    (groupAdmissions : ∀ calls, AdmitsChain (Run calls))
    (groupAdmissionReads : ∀ calls, AdmitsReadsChain (Run calls))
    (groupFamilies : ∀ calls, FamiliesChain (Run calls) (Fam calls))
    (groupClosure : ∀ calls, AtGroups (Run calls) fun ρ t g =>
      ClosureStepOverFamilyW.{u} L ρ t g (Fam calls ρ t g))
    (groupWithoutRoleUnit : ∀ calls, AtGroups (Run calls) (RoleFreeShapes.{u} L))
    (operationRoleUnit :
      ∀ calls, AtGroups (Run calls) (RoleUnitStepOverW.{u} (· ∈ RoleOps.opRoles) L))
    (standardAxiomRoleUnit :
      ∀ calls, AtGroups (Run calls) (RoleUnitStepOverW.{u} (· ∈ standardAxioms) L))
    (storedForm : StoredFormAt.{u} RFormS)
    (innerSteps : InnerStepsChecked.{u} L) (familyBlock : FamilyBlockRow.{u} L)
    (familyTwin : TwinFamily.FamilyTwinRowFam.{u} RFormS L)
    (standaloneDefinition : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind = .defn)
    (standaloneTheoremOrOpaque : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind ≠ .defn)
    (standaloneRecursor : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ rc : Ixon.Recursor, c.info = .recr rc)
    (definitionBlock : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ DefnBlock ms)
    (nativeBlockTelescope : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind)
    (nativeBlockAlias : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtAlias t E₀ B cb ind)
    (nativeBlockOtherTelescope : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerTeleOther t E₀ B cb ind) :
    CircuitComposed.{u} := by
  unfold CircuitComposed
  refine circuitSound_of_bounded l0 ?_
  intro dB valueB heapB callsB evB hbB
  show CircuitSound fun callsA dA => ComposedSpec.{u} callsA callsB dA dB
  refine circuitSound_of_bounded l0 ?_
  intro dA valueA heapA callsA evA hbA
  show ComposedSpec.{u} callsA callsB dA dB
  exact composed_skeleton_over_familyWFamFull (bindingClaimExport dB valueB heapB callsB evB hbB)
    (basisGroups callsB) (groupAdmissions callsB) (groupAdmissionReads callsB)
    (groupFamilies callsB) (groupClosure callsB) (groupWithoutRoleUnit callsB)
    (operationRoleUnit callsB) (standardAxiomRoleUnit callsB) hbA
    (Claim.claimPhase_typing evA)
    (fun _ _ _ _ _ _ h => by
      obtain ⟨_, hW, _⟩ := h
      exact hW.topLim)
    (fun _ _ _ _ _ _ h => Claim.TopWalk.graph h)
    (familyStepsFamFull_closed storedForm innerSteps familyBlock familyTwin
      standaloneDefinition standaloneTheoremOrOpaque standaloneRecursor definitionBlock
      nativeBlockTelescope nativeBlockAlias nativeBlockOtherTelescope callsA
      (FamCallsModeled.of_verifyClaim evA))

/-- **The typing half's premise at the witness with its stored families, taking
`FamilyTwinRowFamClosed` and passing `InnerChecked`, `EnvWF`, `WitnessWhole`, and
`StoredFamilies.levelsParams` already in scope.** -/
theorem familySteps_closedWF {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {RFormS : StoredFormPred}
    (storedForm : StoredFormAt.{u} RFormS)
    (innerSteps : InnerStepsChecked.{u} L) (familyBlock : FamilyBlockRow.{u} L)
    (familyTwin : TwinFamily.FamilyTwinRowFamClosed.{u} RFormS L)
    (standaloneDefinition : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind = .defn)
    (standaloneTheoremOrOpaque : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind ≠ .defn)
    (standaloneRecursor : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ rc : Ixon.Recursor, c.info = .recr rc)
    (definitionBlock : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ DefnBlock ms)
    (nativeBlockTelescope : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind)
    (nativeBlockAlias : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtAlias t E₀ B cb ind)
    (nativeBlockOtherTelescope : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerTeleOther t E₀ B cb ind)
    (calls : List (Call F)) (hfamMod : FamCallsModeled calls) :
    FamilyStepsFamFull.{u} L calls (Claim.TopWalk calls) := by
  intro t seeds E₀ lim Top rank₀ hWalk₀ R envT hshape famOf hSF hagree hstore hEnvWF hWhole
  obtain ⟨rank, fam, twin, adv, Inner, bAddr, hWalk, hFR, hIC, -, hblock, htwin_canon⟩ :=
    familyGraphRowInnerFamT_closed (fun _ _ t E₀ _ B r => RFormS t E₀ B r) hfamMod
      t seeds E₀ lim Top rank₀ hWalk₀ R envT hshape famOf hSF hagree hstore hEnvWF hWhole
  exact ⟨rank, fam, twin, adv, Inner, hWalk, hFR.graph,
    topUnitSteps_family standaloneDefinition standaloneTheoremOrOpaque standaloneRecursor
      definitionBlock nativeBlockTelescope nativeBlockAlias nativeBlockOtherTelescope hWalk hFR,
    innerSteps calls t seeds E₀ lim Top rank hWalk R envT fam twin adv Inner bAddr hFR hIC,
    fun E => familyBlock calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR,
    fun E hctx A c B rb crb hW hc hlog htw hrb hcrb =>
      TwinFamily.familyTwinStep_graph_of_closed familyTwin hWalk hFR hIC hctx hEnvWF hWhole
        hSF.levelsParams hW hc hlog htw hrb hcrb
        (htwin_canon B rb A hrb htw).1 (htwin_canon B rb A hrb htw).2,
    TwinFamily.storedTwinSteps_of_closed familyTwin hWalk hFR hIC hEnvWF hWhole hSF.levelsParams
      ⟨famOf, hSF, hSF.flat, storedForm t R envT famOf hshape hSF⟩ hblock⟩

/-- **The public statement `IxVM.Consistency.CircuitComposed` taking `FamilyTwinRowFamClosed`.** -/
theorem circuitComposed_of_partsFamInnerWT_closedWF
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {Run : List (Call F) → Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    {Fam : List (Call F) → BRun → Ix.Kernel.RoleTable → Nat → Ixon.Env → Ixon.Env →
      (_root_.Address → Option _root_.Address) → (_root_.Address → _root_.Address → Prop) →
      (_root_.Address → _root_.Address → Prop) → Prop}
    {RFormS : StoredFormPred}
    (bindingClaimExport :
      SourceSoundBounded fun calls d => BindingClaimExportObs (Run calls) calls d)
    (basisGroups : ∀ calls, BasisOverW.{u} L (Run calls))
    (groupAdmissions : ∀ calls, AdmitsChain (Run calls))
    (groupAdmissionReads : ∀ calls, AdmitsReadsChain (Run calls))
    (groupFamilies : ∀ calls, FamiliesChain (Run calls) (Fam calls))
    (groupClosure : ∀ calls, AtGroups (Run calls) fun ρ t g =>
      ClosureStepOverFamilyW.{u} L ρ t g (Fam calls ρ t g))
    (groupWithoutRoleUnit : ∀ calls, AtGroups (Run calls) (RoleFreeShapes.{u} L))
    (operationRoleUnit :
      ∀ calls, AtGroups (Run calls) (RoleUnitStepOverW.{u} (· ∈ RoleOps.opRoles) L))
    (standardAxiomRoleUnit :
      ∀ calls, AtGroups (Run calls) (RoleUnitStepOverW.{u} (· ∈ standardAxioms) L))
    (storedForm : StoredFormAt.{u} RFormS)
    (innerSteps : InnerStepsChecked.{u} L) (familyBlock : FamilyBlockRow.{u} L)
    (familyTwin : TwinFamily.FamilyTwinRowFamClosed.{u} RFormS L)
    (standaloneDefinition : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind = .defn)
    (standaloneTheoremOrOpaque : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind ≠ .defn)
    (standaloneRecursor : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ rc : Ixon.Recursor, c.info = .recr rc)
    (definitionBlock : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ DefnBlock ms)
    (nativeBlockTelescope : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind)
    (nativeBlockAlias : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtAlias t E₀ B cb ind)
    (nativeBlockOtherTelescope : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerTeleOther t E₀ B cb ind) :
    CircuitComposed.{u} := by
  unfold CircuitComposed
  refine circuitSound_of_bounded l0 ?_
  intro dB valueB heapB callsB evB hbB
  show CircuitSound fun callsA dA => ComposedSpec.{u} callsA callsB dA dB
  refine circuitSound_of_bounded l0 ?_
  intro dA valueA heapA callsA evA hbA
  show ComposedSpec.{u} callsA callsB dA dB
  exact composed_skeleton_over_familyWFamFull (bindingClaimExport dB valueB heapB callsB evB hbB)
    (basisGroups callsB) (groupAdmissions callsB) (groupAdmissionReads callsB)
    (groupFamilies callsB) (groupClosure callsB) (groupWithoutRoleUnit callsB)
    (operationRoleUnit callsB) (standardAxiomRoleUnit callsB) hbA
    (Claim.claimPhase_typing evA)
    (fun _ _ _ _ _ _ h => by
      obtain ⟨_, hW, _⟩ := h
      exact hW.topLim)
    (fun _ _ _ _ _ _ h => Claim.TopWalk.graph h)
    (familySteps_closedWF storedForm innerSteps familyBlock familyTwin
      standaloneDefinition standaloneTheoremOrOpaque standaloneRecursor definitionBlock
      nativeBlockTelescope nativeBlockAlias nativeBlockOtherTelescope callsA
      (FamCallsModeled.of_verifyClaim evA))

end IxVM.Refinement.Typing
