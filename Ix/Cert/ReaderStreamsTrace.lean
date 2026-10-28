import Ix.Cert.TraceGood
import Ix.Cert.TraceSource
import Ix.Cert.BlockCollapse
import Ix.Cert.RecursorIndex
import Ix.Cert.StepsEncode
import Ix.Cert.ReaderStreamsUnits
import Ix.Cert.TraceStates
import Ix.Cert.SourceTotality
import Ix.Cert.ReadingKeys
import Ix.Cert.StepKeeps
import Ix.Cert.EvidenceTransfer
import Ix.Cert.UnchangedRules

/-! # The reader's streams from quotient Source's trace

`TraceSegments.unitsRead_of_needs` gives the reader's units of a closure once every cut of the
compile's record order into quotient Source's trace holds stored canonical records and gives each
lowered group what its kind needs (`TraceSegments.TraceNeeds`). This module discharges
`TraceNeeds` field by field (`traceNeeds`):
* `good`: `TraceGood.converted_good`;
* `levels`: `TraceSource.kept_levels`, from quotient Source's acceptance;
* an axiom's or quotient constant's `HeaderNeeds`: `TraceFold.lone_compiled`, with
  `TraceSource.axiom_nodup`/`quotient_nodup` and `axiom_noSelf`/`quotient_noSelf`;
* a block of definitions' `BlockNeeds`: `TraceFold.definitions_distinct`,
  `definitions_exactNames` and `BlockCollapse.block_collapse`;
* an inductive group's `InductiveNeeds` (`inductive_needs`): the fold's runs of its types and
  recursors (`GroupRuns.types_compiled`, `recursors_family`), the closure's recursor index
  (`RecursorIndex.closure_recursor_index`), the group's shape and level parameters
  (`TraceSource`), and its members' distinct names, which the reader's lowering checks
  (`inductive_distinct`).
The states' goodness (`TraceStates.trace_states_good`) and the definitions' hints are premises of
`traceNeeds`. `readerStreams` then gives `Obligation.ReaderStreams` through
`ReaderStreamsUnits.readerStreams_of_units`, from three statements about the compile: the
closure's record layout (`LayoutsHold`) and the definitions' hints (`SingletonsHinted`,
`BlocksHinted`). `compileCorrect_of` composes it with the other obligations of
`compileCorrect_unchanged`. The three statements are proved, and `compileCorrect` proves
`CompileCorrect` with no premises, in `Ix.Cert.CompileCorrectProof`. -/

namespace Ix.Cert.ReaderStreamsTrace

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileM Ix.CompileCert
open Ix.LeanIngress (ingressKey Group Converted FiberMap Graph QRepAt roleAtMap fiberAliasAt fiberHintsMap
  evAddr scheduleOf)
open Ix.Cert.ClosureLayout (Steps quotientGraph)
open Ix.Cert.SourcePrelude (Scheduled)
open Ix.Cert.TraceSegments (LoweredAt TraceNeeds StateGood scope fibers cutOf)
open Ix.Cert.InductiveCompile (indsOf indOf)

/-! ## Every scheduled item of a trace converts -/

/-- **Every item quotient Source's trace passes converts**: a refused conversion ends the trace. -/
theorem trace_scheduled {g : Graph} {start : State .source} {xs : List Scheduled} {rs : List (Read .source)}
    {st : State .source} {s : Ix.LeanIngress.CollapseState} {kb : Ix.LeanIngress.KeptBlocks}
    (h : SourcePrelude.Trace g start xs rs st s kb) : ∀ x ∈ xs, ∃ conv, x.1.2 = .ok conv := by
  induction h with
  | nil => intro x hx; cases hx
  | @«alias» xs rs st s kb x i _ hcol ih =>
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact ih y hy
    · rw [List.mem_singleton] at hy
      subst hy
      cases hc : y.1.2 with
      | error e =>
        rw [hc] at hcol
        simp [Ix.LeanIngress.collapseGroup] at hcol
      | ok conv => exact ⟨conv, rfl⟩
  | @lowered xs rs st s kb x s' kb' conv raw r dropped _ hc _ _ _ ih =>
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact ih y hy
    · rw [List.mem_singleton] at hy
      subst hy
      exact ⟨conv, hc⟩

/-! ## An inductive group's members have distinct names -/

/-- A block's member and constructor names, in the block's order, are its types' names and then
its constructors'. -/
theorem indsOf_keys_perm : ∀ (ts : List Ix.InductiveVal) (cs : List (Array Ix.ConstructorVal)),
    ts.length = cs.length →
    (((List.zipWith indOf ts cs).map MutConst.indc).flatMap Ix.CompileCert.Canon.keysOf).Perm
      (ts.map (·.cnst.name) ++ cs.flatMap fun a => a.toList.map (·.cnst.name))
  | [], [], _ => by simp
  | v :: ts, a :: cs, h => by
    have ih := indsOf_keys_perm ts cs (by simpa using h)
    simp only [List.zipWith_cons_cons, List.map_cons, List.flatMap_cons, Ix.CompileCert.Canon.keysOf,
      MutConst.name, MutConst.ctors, indOf, List.cons_append]
    exact List.Perm.cons _ ((ih.append_left _).trans (List.perm_append_comm_assoc _ _ _))
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem recs_keys : ∀ (l : List Ix.RecursorVal),
    (l.map MutConst.recr).flatMap Ix.CompileCert.Canon.keysOf = l.map (·.cnst.name)
  | [] => rfl
  | r :: l => by
    simp only [List.map_cons, List.flatMap_cons, Ix.CompileCert.Canon.keysOf, MutConst.name, MutConst.ctors,
      recs_keys l]
    rfl

/-- **A lowered inductive group's members have distinct names** (`InductiveNeeds.distinct`,
`recDistinct`): the reader's lowering declines a block whose declarations repeat a key
(`LowerDistinct.lowerInductive_names_nodup`), and the block's `indDecl` declares every type's,
constructor's and recursor's key, a function of its name. -/
theorem inductive_distinct {g : Graph} {ρ : FiberMap} {hints : CName .source → Option ReducibilityHint}
    {start : State .source} {ls : List Scheduled} {rs : List (Read .source)} {ℓ : Nat} {y : Scheduled}
    {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal}
    {c : Converted} {stS : State .source} {raw rd : Read .source}
    (low : LoweredAt g ρ hints start ls rs ℓ y (.inductive types ctors recs) c stS raw rd)
    (hcsize : ctors.size = types.size) :
    Ix.CompileCert.Canon.KeysDistinct ((indsOf types ctors).map MutConst.indc) ∧
      Ix.CompileCert.Canon.KeysDistinct (recs.toList.map MutConst.recr) := by
  obtain ⟨first, -, rfl, -⟩ := InductiveUnits.convertInductive_src
    (show Ix.LeanIngress.convertInductive types ctors recs = .ok c from low.converted)
  have hl : lowerInductive stS (Ix.LeanIngress.BlockRead.canon
      (Ix.LeanIngress.BlockRead.substKeys ρ (InductiveUnits.srcBlock types ctors recs first))) = .ok raw :=
    low.lowered
  obtain ⟨gens, d, hd, -, hnames⟩ := ReaderUnits.lowerInductive_decls hl
  have nd := LowerDistinct.lowerInductive_names_nodup hl
  rw [hd, List.flatMap_append] at nd
  have ndd : d.names.Nodup := by
    have := nd.sublist (List.sublist_append_right _ _)
    simpa using this
  let K : Ix.Name → CName .source := fun n => Ix.LeanIngress.Key.subst ρ (ingressKey n)
  have cvName : ∀ cv : CVal .source, ((Ix.LeanIngress.canonValM cv).run' {}).name = cv.name := fun cv => by
    rw [RecordReadings.canonValM_run]
  have hX : (Ix.LeanIngress.BlockRead.canon (Ix.LeanIngress.BlockRead.substKeys ρ
      (InductiveUnits.srcBlock types ctors recs first))).types.toList.map (·.1.name) =
      (types.toList.map (·.cnst.name)).map K := by
    simp only [Ix.LeanIngress.BlockRead.canon, Ix.LeanIngress.BlockRead.substKeys, InductiveUnits.srcBlock,
      Array.toList_map, List.map_map]
    refine List.map_congr_left fun v _ => ?_
    simp only [Function.comp_apply, InductiveUnits.srcType, cvName]
    rfl
  have hY : (Ix.LeanIngress.BlockRead.canon (Ix.LeanIngress.BlockRead.substKeys ρ
      (InductiveUnits.srcBlock types ctors recs first))).ctors.toList.map (·.1.name) =
      ((ctors.toList.flatMap (·.toList)).map (·.cnst.name)).map K := by
    simp only [Ix.LeanIngress.BlockRead.canon, Ix.LeanIngress.BlockRead.substKeys, InductiveUnits.srcBlock,
      Array.toList_map, List.map_map]
    refine List.map_congr_left fun c _ => ?_
    simp only [Function.comp_apply, InductiveUnits.srcCtor, cvName]
    rfl
  have hZ : (Ix.LeanIngress.BlockRead.canon (Ix.LeanIngress.BlockRead.substKeys ρ
      (InductiveUnits.srcBlock types ctors recs first))).recs.toList.map (·.1.name) =
      (recs.toList.map (·.cnst.name)).map K := by
    simp only [Ix.LeanIngress.BlockRead.canon, Ix.LeanIngress.BlockRead.substKeys, InductiveUnits.srcBlock,
      Array.toList_map, List.map_map]
    refine List.map_congr_left fun r _ => ?_
    simp only [Function.comp_apply, InductiveUnits.srcRec]
    split
    · rename_i c' _ _ _ heq
      have hn := congrArg Ix.Kernel.ConstantInfo.name heq
      rw [ReaderUnits.canonInfo_name] at hn
      exact hn.symm
    · rfl
  rw [hnames, hX, hY, hZ, ← List.map_append, ← List.map_append] at ndd
  have names := List.Pairwise.of_map (R := fun a b => a ≠ b) K (fun _ _ h e => h (congrArg K e)) ndd
  have hC : (ctors.toList.flatMap (·.toList)).map (·.cnst.name) =
      ctors.toList.flatMap fun a => a.toList.map (·.cnst.name) := by
    simp [List.map_flatMap]
  refine ⟨?_, ?_⟩
  · unfold Ix.CompileCert.Canon.KeysDistinct indsOf
    refine (indsOf_keys_perm types.toList ctors.toList (by simp [hcsize])).nodup_iff.mpr ?_
    rw [← hC]
    exact names.sublist (List.sublist_append_left _ _)
  · unfold Ix.CompileCert.Canon.KeysDistinct
    rw [recs_keys]
    exact names.sublist (List.sublist_append_right _ _)

/-! ## What the trace's lowered groups need -/

section Needs

variable {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env}
  {failures : Failures} {t : RoleTable} {envQ : Env .source}
  {hints : CName .source → Option ReducibilityHint}

/-- **What an inductive group's segment needs** (`InductiveNeeds`), for an inductive read of a
trace whose inductive reads are kept whole. -/
theorem inductive_needs (P : Premises env roots sub ixe failures t envQ) {preA : Prelude .anon}
    (prelude : preludeFor t = .ok preA) (b : Ix.RoleEvidence.Bundle)
    {μ : CheckMode} {ev : Evidences .source} {envS : Env .source} {pre : Prelude .source}
    {decls ds : Array (Declaration .source)} {rs : List (Read .source)}
    (acc : Cached.AcceptsRef μ ev ds.toList envS)
    (hflat : decls.toList = rs.flatMap (·.decls.toList)) (hds : ds = Frontend.preparePrelude pre.ix decls)
    {ls : List Scheduled} {L : List Address} (whole : CollapseWhole.InductiveWhole pre.state ls rs)
    (corder : ClosureOrder ixe (Seed ixe sub) (cutOf ixe t hints sub ls L).flatten)
    {ℓ : Nat} {y : Scheduled} {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)}
    {recs : Array Ix.RecursorVal} {c : Converted} {stS : State .source} {raw rd : Read .source}
    (low : LoweredAt (quotientGraph ixe t hints sub) (fibers ixe t) hints pre.state ls rs ℓ y
      (.inductive types ctors recs) c stS raw rd)
    {first : Ix.InductiveVal} (hfirst : types[0]? = some first) :
    TraceSegments.InductiveNeeds ixe sub t preA (cutOf ixe t hints sub ls L).flatten b types ctors recs first raw
      rd := by
  have hgr := low.group
  have hconv : Ix.LeanIngress.convertInductive types ctors recs = .ok c := low.converted
  obtain ⟨first', -, hceq, -⟩ := InductiveUnits.convertInductive_src hconv
  have kept : rd = raw := whole ℓ y rd _ raw low.item low.read low.conversion ⟨_, by rw [hceq]; rfl⟩
    (by rw [← low.state]; exact low.lowered)
  have idx := constructorIndices P.compiled
  have fbk := familyBlocks P.compiled
  obtain ⟨hcsize, positions⟩ := TraceSource.inductive_shape low
  obtain ⟨lpsEq, ctorLps, recShare⟩ := TraceSource.family_levels P (familyLevelParams P.compiled) low hfirst
  obtain ⟨nodup, recNodup⟩ := TraceSource.inductive_nodup acc hflat hds low kept hfirst
  obtain ⟨rlps, recLpsEq, rlNodup⟩ := TraceSource.recLevels_of recNodup recShare
  obtain ⟨distinct, recDistinct⟩ := inductive_distinct low hcsize
  have hrne : recs.toList ≠ [] := by
    obtain ⟨_, v, -, head, hrecs, -⟩ := GroupRuns.inductive_facts P hgr
    have hsize := (GroupRuns.blockRecursors_names hrecs).1
    have hv0 : 0 < v.all.size := (Array.getElem?_eq_some_iff.mp head).1
    intro h
    have := congrArg List.length h
    simp only [Array.length_toList, List.length_nil] at this
    omega
  have namesIn := ClosureLayout.converted_names_stored P hgr low.converted
  have typesIn : ∀ i (hi : i < types.size), ∃ ci, (types[i].cnst.name, ci) ∈ sub.consts.toList :=
    fun i hi => namesIn _ ((TraceSegments.inductive_names types ctors recs _).mpr (.inl ⟨i, hi, rfl⟩))
  have ctorsIn : ∀ i (hi : i < ctors.size) k (hk : k < ctors[i].size),
      ∃ ci, (ctors[i][k].cnst.name, ci) ∈ sub.consts.toList :=
    fun i hi k hk => namesIn _ ((TraceSegments.inductive_names types ctors recs _).mpr
      (.inr (.inl ⟨i, hi, k, hk, rfl⟩)))
  have recsIn : ∀ j (hj : j < recs.size), ∃ ci, (recs[j].cnst.name, ci) ∈ sub.consts.toList :=
    fun j hj => namesIn _ ((TraceSegments.inductive_names types ctors recs _).mpr (.inr (.inr ⟨j, hj, rfl⟩)))
  obtain ⟨snap₁, rep₁, all₁, r₁, c₁, fb₁, out₁, after₁, ran₁, claimed₁, blobs₁⟩ :=
    GroupRuns.types_compiled P fbk hgr distinct
  obtain ⟨snap₂, rep₂, all₂, r₂, c₂, fb₂, out₂, after₂, family, blobs₂⟩ :=
    GroupRuns.recursors_family P fbk hgr distinct
  obtain ⟨cenvR₁, allR₁, key₁, rr₁, cache₁, hr₁, pub₁, hrec₁⟩ := claimed₁
  obtain ⟨cenvR₂, allR₂, key₂, rr₂, cache₂, hr₂, pub₂, hrec₂, ran₂⟩ := family
  have lowered : Ix.LeanIngress.lower stS (c.quotient (fibers ixe t)) = .ok raw := by
    have h := low.lowered
    rw [hceq] at h ⊢
    exact h
  obtain ⟨index, entries⟩ := RecursorIndex.closure_recursor_index P (recursorSlotsUnique P.compiled)
    (recursorShapes P.compiled) (recursorsOwned P.compiled) (familyNamesStored P.compiled)
    (familyLevelParams P.compiled) prelude corder (StepsEncode.storedCanonical_of_compile P.compiled _) b
    (ClosureResolve.publishedResolve P) hgr hconv hfirst hcsize recLpsEq rlNodup hrne typesIn ctorsIn recsIn
    ran₁ hr₁ pub₁ hrec₁ hr₂ pub₂ hrec₂ ran₂ lowered
  exact {
    hcsize
    compiled := ⟨_, _, _, _, _, _, _, _, {
      ran₁
      claimed₁ := ⟨cenvR₁, allR₁, key₁, rr₁, cache₁, hr₁, pub₁, hrec₁⟩
      bound₁ := fb₁.bound idx
      blobs₁
      published₁ := fb₁.mentionsPublished P fun _ hm => TraceFold.types_mentioned P hgr hm
      family := ⟨cenvR₂, allR₂, key₂, rr₂, cache₂, hr₂, pub₂, hrec₂, ran₂⟩
      bound₂ := fb₂.bound idx
      blobs₂
      published₂ := fb₂.mentionsPublished P fun _ hm => TraceFold.recursors_mentioned P hgr hm
      index
      entries }⟩
    lpsEq
    ctorLps
    nodup
    positions
    recLevels := ⟨rlps, recLpsEq, rlNodup⟩
    hrne
    distinct
    noCtor := TraceSource.inductive_noCtor acc hflat hds low kept hcsize
    recDistinct }

/-- **What the trace's lowered groups need** (`TraceNeeds`), for a cut of the compile's record
order, from quotient Source's acceptance; the states' goodness and the definitions' hints are
premises. -/
theorem traceNeeds (P : Premises env roots sub ixe failures t envQ) {preA : Prelude .anon}
    (prelude : preludeFor t = .ok preA) (b : Ix.RoleEvidence.Bundle)
    {μ : CheckMode} {ev : Evidences .source} {envS : Env .source} {pre : Prelude .source}
    {decls ds : Array (Declaration .source)} {rs : List (Read .source)}
    (acc : Cached.AcceptsRef μ ev ds.toList envS)
    (hflat : decls.toList = rs.flatMap (·.decls.toList)) (hds : ds = Frontend.preparePrelude pre.ix decls)
    (scheduled : ∀ x ∈ (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList, ∃ conv, x.1.2 = .ok conv)
    {ls : List Scheduled} {L : List Address} (steps : Steps (quotientGraph ixe t hints sub) pre.state ls rs)
    (whole : CollapseWhole.InductiveWhole pre.state ls rs)
    (inTrace : ∀ y ∈ ls, y ∈ (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList)
    (corder : ClosureOrder ixe (Seed ixe sub) (cutOf ixe t hints sub ls L).flatten)
    (states : ∀ ℓ, StateGood (scope ixe t) ((rs.take ℓ).foldl State.commit pre.state))
    (singletons : ∀ {i : Nat} {ci : Ix.ConstantInfo},
      (quotientGraph ixe t hints sub).groups[i]? = some (.definitions #[ci]) →
        TraceSegments.DefinitionNeeds ixe sub hints ci)
    (blocks : ∀ {i : Nat} {members : Array Ix.ConstantInfo},
      (quotientGraph ixe t hints sub).groups[i]? = some (.definitions members) → 2 ≤ members.size →
        ∀ order : List Address, ∃ cenv benv output after,
          TraceSegments.BlockCompiled ixe sub t preA order hints (TraceSegments.defsOf members) cenv benv output
            after) :
    TraceNeeds ixe sub t preA b hints pre.state ls rs L where
  good _ _ _ hgr hconv := TraceGood.converted_good P scheduled hgr hconv
  states := states
  levels := TraceSource.kept_levels acc hflat hds
  definitions _ _ _ _ _ _ _ low := singletons low.group
  axioms _ _ v _ _ _ _ low := by
    obtain ⟨hsingle, hst⟩ := TraceFold.axiom_single low.group P
    exact ⟨TraceFold.lone_compiled P scheduled (constructorIndices P.compiled) low.group trivial hsingle hst
        (fun _ h => by cases h) (fun _ h => by cases h)
        (mentions := fun m => GraphWalk.Refs m (Ix.ConstantInfo.axiomInfo v).getCnst.type)
        fun _ hm => TraceFold.axiom_mentioned P low.group hm,
      TraceSource.axiom_nodup acc hflat hds low, TraceSource.axiom_noSelf acc hflat hds low⟩
  quotients _ _ v _ _ _ _ low := by
    obtain ⟨hsingle, hst⟩ := TraceFold.quot_single low.group P
    exact ⟨TraceFold.lone_compiled P scheduled (constructorIndices P.compiled) low.group trivial hsingle hst
        (fun _ h => by cases h) (fun _ h => by cases h)
        (mentions := fun m => GraphWalk.Refs m (Ix.ConstantInfo.quotInfo v).getCnst.type)
        fun _ hm => TraceFold.quot_mentioned P low.group hm,
      TraceSource.quotient_nodup acc hflat hds low, TraceSource.quotient_noSelf acc hflat hds low⟩
  blocks _ _ _ _ _ _ _ low two :=
    ⟨blocks low.group two _, TraceFold.definitions_distinct P low.group,
      TraceFold.definitions_exactNames P scheduled low.group two,
      BlockCollapse.block_collapse P scheduled steps inTrace low two⟩
  inductives _ _ _ _ _ _ _ _ _ _ low hfirst :=
    inductive_needs P prelude b acc hflat hds whole corder low hfirst

end Needs

/-! ## The reader's streams -/
/-- **Every accepted closure's compiled records lie as quotient Source's graph says**
(`ClosureLayout.Layout`). -/
def LayoutsHold : Prop :=
  ∀ {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env}
    {failures : Failures} {t : RoleTable} {envQ : Env .source}, Premises env roots sub ixe failures t envQ →
    (∀ x ∈ (scheduleOf (quotientGraph ixe t ((fiberHintsMap ixe)[·]?) sub)).zipIdx.toList,
      ∃ conv, x.1.2 = .ok conv) →
    ClosureLayout.Layout ixe (quotientGraph ixe t ((fiberHintsMap ixe)[·]?) sub)

/-- **A singleton definition compiles alone at the hint quotient Source reads it at**
(`TraceSegments.DefinitionNeeds`). -/
def SingletonsHinted : Prop :=
  ∀ {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env}
    {failures : Failures} {t : RoleTable} {envQ : Env .source}, Premises env roots sub ixe failures t envQ →
    (∀ x ∈ (scheduleOf (quotientGraph ixe t ((fiberHintsMap ixe)[·]?) sub)).zipIdx.toList,
      ∃ conv, x.1.2 = .ok conv) →
    ConstructorIndices env → ∀ {i : Nat} {ci : Ix.ConstantInfo},
      (quotientGraph ixe t ((fiberHintsMap ixe)[·]?) sub).groups[i]? = some (.definitions #[ci]) →
      TraceSegments.DefinitionNeeds ixe sub ((fiberHintsMap ixe)[·]?) ci

/-- **A block of several definitions compiles in Lean's order, each member at the hint quotient
Source reads it at** (`TraceSegments.BlockCompiled`). -/
def BlocksHinted : Prop :=
  ∀ {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env}
    {failures : Failures} {t : RoleTable} {envQ : Env .source}, Premises env roots sub ixe failures t envQ →
    (∀ x ∈ (scheduleOf (quotientGraph ixe t ((fiberHintsMap ixe)[·]?) sub)).zipIdx.toList,
      ∃ conv, x.1.2 = .ok conv) →
    ConstructorIndices env → ∀ {i : Nat} {members : Array Ix.ConstantInfo},
      (quotientGraph ixe t ((fiberHintsMap ixe)[·]?) sub).groups[i]? = some (.definitions members) →
      2 ≤ members.size → ∀ {preA : Prelude .anon} (order : List Address), ∃ cenv benv output after,
        TraceSegments.BlockCompiled ixe sub t preA order ((fiberHintsMap ixe)[·]?) (TraceSegments.defsOf members)
          cenv benv output after

/-- **The reader's streams of an accepted compiled closure** (`Obligation.ReaderStreams`), from
the closure's record layout and the definitions' hints; the states quotient Source reads from are
good (`TraceStates.trace_states_good`). -/
theorem readerStreams (layout : LayoutsHold) (singletons : SingletonsHinted) (blocks : BlocksHinted) :
    Obligation.ReaderStreams := by
  intro env roots sub ixe failures t envQ pre ds b P _ hpre hds hb
  refine ReaderStreamsUnits.readerStreams_of_units P hpre hds hb ?_
  intro preA rs fin s kb decls hA htrace hflat hdsEq
  -- quotient Source's acceptance, of the same prepared stream
  obtain ⟨-, pre', ds', hpre', hprep', acc⟩ := P.source
  obtain rfl : pre = pre' := Except.ok.inj (hpre.symm.trans hpre')
  obtain rfl : ds = ds' := Except.ok.inj (hds.symm.trans hprep')
  -- the renaming onto the bundle's addresses is injective on representatives
  obtain ⟨-, b', hb', -, -, hd, -⟩ := Ix.LeanIngress.prepareSourceCollapsedAtUsing_good hds
  rw [hb] at hb'
  cases hb'
  have tb := tableBound_of (defaultTable_check P.table) P.bound
  have hf : InjOn (evAddr ixe b) (QRepAt ixe (roleAtMap t)) :=
    (Ix.LeanIngress.evAddr_injOn tb hd).mono fun _ h => Or.inl h
  -- the preludes agree
  obtain ⟨-, -, -, ⟨t', preS, preA', ht', hS, hA', hagree⟩⟩ := P.evidence
  obtain rfl : t' = t := by
    rw [P.table] at ht'
    exact (Except.ok.inj ht').symm
  have bind_ok : ∀ (a : RoleTable) (g : RoleTable → Except String (Prelude .source)),
      ((Except.ok a : Except String RoleTable) >>= g) = g a := fun _ _ => rfl
  have hpreS : preludeFor (md := .source) t' = .ok pre := by
    unfold builtinPrelude at hpre
    rw [P.table, bind_ok] at hpre
    exact hpre
  obtain rfl : pre = preS := Except.ok.inj (hpreS.symm.trans hS)
  obtain rfl : preA = preA' := Except.ok.inj (hA.symm.trans hA')
  have scheduled := trace_scheduled htrace
  exact TraceSegments.unitsRead_of_needs P hA hf (ClosureResolve.publishedResolve P) htrace
    (layout P scheduled)
    fun ls L steps whole inTrace _ _ _ corder =>
      ⟨StepsEncode.storedCanonical_of_compile P.compiled _,
        traceNeeds P hA b acc hflat hdsEq scheduled steps whole inTrace corder
          (TraceStates.trace_states_good P scheduled hagree rs fin s kb htrace)
          (singletons P scheduled (constructorIndices P.compiled))
          fun hgr two order => blocks P scheduled (constructorIndices P.compiled) hgr two order⟩

/--
info: 'Ix.Cert.ReaderStreamsTrace.traceNeeds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms traceNeeds

/--
info: 'Ix.Cert.ReaderStreamsTrace.readerStreams' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms readerStreams

/-! ## The certified compiler's correctness -/

universe w

/-- **The certified compiler is correct** (`CompileCorrect`), from the closure's record layout and
the definitions' hints: every other obligation of `compileCorrect_unchanged` is proved. -/
theorem compileCorrect_of (layout : LayoutsHold) (singletons : SingletonsHinted) (blocks : BlocksHinted) :
    CompileCorrect.{w} :=
  compileCorrect_unchanged SourceTotality.sourceTotal (readerStreams layout singletons blocks)
    ReadingKeys.readingKeys StepKeeps.scheduleOwnership EvidenceTransfer.evidenceTransfer unchangedRules

/--
info: 'Ix.Cert.ReaderStreamsTrace.compileCorrect_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms compileCorrect_of

end Ix.Cert.ReaderStreamsTrace
