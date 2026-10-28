import Ix.Cert.LayoutExtra
import Ix.Cert.SingletonSegments
import Ix.Cert.Claims
import Ix.Cert.CompiledRefs

/-! # A published closure name's record resolves

`SingletonSegments.PublishedResolve ixe sub`: the record a closure name is published at resolves in
the artifact's store, as a lone record or as a projection of its block whose member has the
projection's kind (`publishedResolve`).

The name's record is a primary claim of its block's compile (`LayoutExtra.claimedIn_of`), and every
primary claim of a block compile resolves in a store holding the block (`runBlock_claims`):
* a lone constant's compile returns a lone record and no projection (`constantInfo_lone`);
* a mutual block's rows read as their members (`MutualArtifact.mutual_references`) when every
  inductive member's constructors are at their declared positions. A mutual block has no row only
  when it has no class, and the block compile refuses that block when it registers it
  (`registerMutsEntry`).

The constructor positions are Source's (`closure_positions`). The compiler copies a constructor's
declared index into the block record, so a constructor projection resolves only when that index
is the constructor's position. An accepted closure puts every inductive it stores in an inductive
group, and the group checks its constructors' indices. -/

namespace Ix.Cert.ClosureResolve

open Ix.Kernel.Reader (Store resolveSource)
open Ix.CompileM Ix.CompileCert
open Ix.CompileCert.Emission (Yields)
open Ix.LeanIngress (Group Converted inductiveGroup groupsOf componentGroup unplaced convert
  convertDefinitions definitionShape)
open Ix.CompileCert.Loop (idBind idPure except_bind_ok)

/-! ## Lone records -/

/-- A lone record resolves, as its own member 0, in every store. -/
theorem lone_resolves {c : Ixon.Constant} (h : BlockContext.lone c.info = true) (store : Store) (a : Address) :
    (resolveSource store a c).isSome = true := by
  cases hi : c.info <;> simp_all [BlockContext.lone, resolveSource]

/-- The canonical sharing keeps a lone info lone. -/
theorem built_lone {limits : Ix.Sharing.Exact.Limits} {info : Ixon.ConstantInfo} {refs : Array Address}
    {univs : Array Ixon.Univ} {out : Ixon.Constant} (ran : buildConstantWithSharing limits info refs univs = .ok out)
    (h : BlockContext.lone info = true) : BlockContext.lone out.info = true := by
  have erased := (SharingRoots.build_roots (md := .anon) limits info refs univs out ran).1
  cases info <;> cases hi : out.info <;>
    simp_all [BlockContext.lone, SharingRoots.erase, Ix.Sharing.Exact.mapRoots]

/-- A block finished from a lone info is a lone record with no projection. -/
theorem finish_lone {info : Ixon.ConstantInfo} (h : BlockContext.lone info = true) (blockMeta : Ixon.ConstantMeta) :
    Yields (finishConstantInfoWithSharing info blockMeta)
      (fun r => r.projections = #[] ∧ BlockContext.lone r.block.info = true) := by
  intro context before output after ran
  rw [Ix.CompileCert.EmissionBlocks.finish_run] at ran
  cases built : buildConstantWithSharing context.1.sharingLimits info before.refs before.univs with
  | error e => rw [built] at ran; cases ran
  | ok block =>
    rw [built] at ran
    simp only [Except.map, Prod.mk.injEq, Except.ok.injEq] at ran
    obtain ⟨rfl, -⟩ := ran
    exact ⟨rfl, built_lone built h⟩

theorem definitionDataInfo_lone (source : Ix.Def) :
    Yields (compileDefinitionDataInfo source)
      (fun r => r.projections = #[] ∧ BlockContext.lone r.block.info = true) := by
  unfold compileDefinitionDataInfo compileDefinitionDataBlock
  exact Yields.bindAny _ fun _ => Yields.bindAny _ fun d => by
    obtain ⟨a, b, c, e⟩ := d
    exact finish_lone (by rfl) _

/-- **A lone constant's compile returns a lone record and no projection**, for every kind but an
inductive's and a constructor's (the block compile sends those through the mutual compiler). -/
theorem constantInfo_lone (const : Ix.ConstantInfo) (hi : ∀ v, const = .inductInfo v → False)
    (hc : ∀ v, const = .ctorInfo v → False) :
    Yields (compileConstantInfo const)
      (fun r => r.projections = #[] ∧ BlockContext.lone r.block.info = true) := by
  cases const with
  | defnInfo v =>
    show Yields (compileDefinitionConstantInfo v) _
    unfold compileDefinitionConstantInfo withMutCtx
    rw [Ix.CompileCert.EmissionDispatch.compileDefinitionInfo_eq]
    exact Yields.withBlockEnv _ (definitionDataInfo_lone _)
  | thmInfo v =>
    show Yields (compileTheoremConstantInfo v) _
    unfold compileTheoremConstantInfo withMutCtx compileTheoremInfo
    exact Yields.withBlockEnv _ (definitionDataInfo_lone _)
  | opaqueInfo v =>
    show Yields (compileOpaqueConstantInfo v) _
    unfold compileOpaqueConstantInfo withMutCtx compileOpaqueInfo
    exact Yields.withBlockEnv _ (definitionDataInfo_lone _)
  | axiomInfo v =>
    show Yields (compileConstantInfoCore (.axiomInfo v)) _
    unfold compileConstantInfoCore withMutCtx
    refine Yields.withBlockEnv _ ?_
    show Yields (compileAxiomInfo v) _
    unfold compileAxiomInfo compileAxiomBlock
    exact Yields.bindAny _ fun _ => Yields.bindAny _ fun d => by
      obtain ⟨a, b, c⟩ := d
      exact finish_lone (by rfl) _
  | quotInfo v =>
    show Yields (compileQuotientConstantInfo v) _
    unfold compileQuotientConstantInfo withMutCtx compileQuotientInfo compileQuotientBlock
    exact Yields.withBlockEnv _ (Yields.bindAny _ fun _ => Yields.bindAny _ fun d => by
      obtain ⟨a, b, c⟩ := d
      exact finish_lone (by rfl) _)
  | recInfo v =>
    show Yields (compileRecursorConstantInfo v) _
    unfold compileRecursorConstantInfo withMutCtx compileRecursorInfo compileRecursorBlock
    exact Yields.withBlockEnv _ (Yields.bindAny _ fun _ => Yields.bindAny _ fun d => by
      obtain ⟨a, b, c⟩ := d
      exact finish_lone (by rfl) _)
  | inductInfo v => exact absurd rfl (hi v)
  | ctorInfo v => exact absurd rfl (hc v)

/-! ## A block compile's claims resolve -/

/-- **What a block's primary claims need to resolve**: a block with no projection is a lone
record, and every projection resolves in every store holding the block. -/
def ClaimsResolve (r : BlockResult) : Prop :=
  (r.projections.isEmpty = true → BlockContext.lone r.block.info = true) ∧
    ∀ p ∈ r.projections, ∀ store : Store, store r.blockAddr = some r.block →
      (resolveSource store (Address.admissionHash (Ixon.ser p.2.1)) p.2.1).isSome = true

/-- `ClaimsResolve` reads only a block's records. -/
theorem ClaimsResolve.transfer {r out : BlockResult} (h : ClaimsResolve out)
    (same : BlockRecords.recordsOf r = BlockRecords.recordsOf out) : ClaimsResolve r := by
  simp only [BlockRecords.recordsOf, Prod.mk.injEq] at same
  obtain ⟨hblock, -, haddr, hrows⟩ := same
  refine ⟨fun hempty => ?_, fun p hp store hs => ?_⟩
  · rw [hblock]
    apply h.1
    have hsize := congrArg Array.size hrows
    simp only [Array.size_map] at hsize
    simp only [Array.isEmpty_iff_size_eq_zero] at hempty ⊢
    omega
  · have hm : (p.1, p.2.1) ∈ out.projections.map fun p => (p.1, p.2.1) := by
      rw [← hrows]; exact Array.mem_map.mpr ⟨p, hp, rfl⟩
    obtain ⟨q, hq, e⟩ := Array.mem_map.mp hm
    have he : q.2.1 = p.2.1 := (Prod.mk.inj e).2
    rw [← he]
    exact h.2 q hq store (by rw [← haddr, ← hblock]; exact hs)

/-- A block info that is a mutual block. -/
def IsMuts : Ixon.ConstantInfo → Prop
  | .muts _ => True
  | _ => False

/-- A block the canonical sharing built is no projection. -/
theorem built_notPrj {c : Ixon.Constant} (h : BlockLayout.Built c) : BlockLayout.NotPrj c.info := by
  obtain ⟨limits, info, refs, univs, ran, hinfo⟩ := h
  have erased := (SharingRoots.build_roots (md := .anon) limits info refs univs c ran).1
  cases info <;> cases hc : c.info <;>
    simp_all [BlockLayout.NotPrj, SharingRoots.erase, Ix.Sharing.Exact.mapRoots]

/-- Every source-indexed reference is a reference. -/
theorem expectedReferences_some {owner : Address} {sources : List (List MutConst)} :
    ∀ x ∈ MutualProjections.expectedReferences owner sources, x.2.isSome = true := by
  intro x hx
  simp only [MutualProjections.expectedReferences, MutualProjections.sourceReferences, List.mem_flatMap,
    List.mem_cons, List.mem_map] at hx
  obtain ⟨⟨members, index⟩, -, source, -, hx⟩ := hx
  rcases hx with rfl | ⟨⟨ctor, position⟩, -, rfl⟩ <;> rfl

/-- A mutual block with no source-indexed reference has no class, when its classes are not empty. -/
theorem expectedReferences_nil {owner : Address} {sources : List (List MutConst)}
    (nonempty : ∀ members ∈ sources, members ≠ [])
    (h : MutualProjections.expectedReferences owner sources = []) : sources = [] := by
  cases sources with
  | nil => rfl
  | cons members rest =>
    exfalso
    cases members with
    | nil => exact nonempty [] List.mem_cons_self rfl
    | cons m ms =>
      simp [MutualProjections.expectedReferences, MutualProjections.sourceReferences, List.zipIdx_cons] at h

/-- Lean's order puts each member in a class of its own. -/
theorem sourceClasses_single {cs : Array MutConst} :
    ∀ members ∈ sourceClasses cs, ∃ x ∈ cs, members = [x] := by
  intro members hm
  unfold sourceClasses at hm
  try dsimp only at hm
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
  exact ⟨e.1, Array.fst_mem_of_mem_zipIdx (Ix.CompileCert.Canon.mem_qsort.1 (Array.mem_toList_iff.1 he)), rfl⟩

/-- **A mutual block compile's claims resolve**, in Lean's order over members whose constructors
are at their positions, unless the block is a mutual block without classes. -/
theorem mutual_claims {cs : Array MutConst}
    (positions : ∀ m ∈ cs, MutualProjections.ConstructorPositions m)
    {ctx : CompileEnv × BlockEnv} {before after : BlockState} {out : BlockResult}
    (ran : rawRun (compileMutualBlock (sourceClasses cs)) ctx before = (.ok out, after))
    (wire : out.block.wireWF) (classes : IsMuts out.block.info → sourceClasses cs ≠ []) :
    ClaimsResolve out := by
  have nonempty : ∀ members ∈ sourceClasses cs, members ≠ [] := by
    intro members hm
    obtain ⟨x, -, rfl⟩ := sourceClasses_single members hm
    exact List.cons_ne_nil x []
  have agree : MutualProjections.ClassesAgree (sourceClasses cs) := by
    intro members hm left hl right hr
    obtain ⟨x, -, rfl⟩ := sourceClasses_single members hm
    rw [List.mem_singleton.1 hl, List.mem_singleton.1 hr]
  have pos : ∀ source ∈ (sourceClasses cs).flatten, MutualProjections.ConstructorPositions source :=
    fun source hs => positions source ((LayoutExtra.sourceClasses_flat cs).2 source hs)
  have refs := MutualArtifact.mutual_references (sourceClasses cs) nonempty agree pos ctx before out after ran
  have built := (BlockLayout.compileMutualBlock_shape (sourceClasses cs) ctx before out after ran).built
  refine ⟨fun hempty => ?_, fun p hp store hs => ?_⟩
  · have hnil : out.projections = #[] := Array.isEmpty_iff.mp hempty
    cases hi : out.block.info with
    | defn _ | recr _ | axio _ | quot _ => rfl
    | dPrj _ | iPrj _ | rPrj _ | cPrj _ =>
      have := built_notPrj built
      rw [hi] at this
      exact this.elim
    | muts ms =>
      exfalso
      have read := refs (fun _ => some out.block) rfl wire
      rw [hnil] at read
      have hsources := expectedReferences_nil nonempty read.symm
      exact classes (by rw [hi]; trivial) hsources
  · have read := refs store hs wire
    have hrow : (p.1, resolveSource store (Address.admissionHash (Ixon.ser p.2.1)) p.2.1) ∈
        MutualProjections.readRows store (MutualProjections.logicalRows out.projections) := by
      simp only [MutualProjections.readRows, MutualProjections.logicalRows, List.map_map, List.mem_map]
      exact ⟨p, Array.mem_toList_iff.mpr hp, rfl⟩
    rw [read] at hrow
    exact expectedReferences_some _ hrow

/-- A mutual-block registration succeeds only for a block with a class. -/
theorem register_ok {cls : List (List MutConst)} {addr : Address} {ctx : CompileEnv × BlockEnv}
    {s s' : BlockState} {u : Unit} (h : rawRun (registerMutsEntry cls addr) ctx s = (.ok u, s')) : cls ≠ [] := by
  rintro rfl
  unfold registerMutsEntry at h
  simp [rawRun_throw] at h

theorem Returns.bind_register {P : BlockResult → Prop} {cls : List (List MutConst)} {addr : Address}
    {k : Unit → CompileM BlockResult} (h : cls ≠ [] → BlockRecords.Returns P (k ())) :
    BlockRecords.Returns P (registerMutsEntry cls addr >>= k) := by
  intro ctx s x s' ran
  obtain ⟨u, mid, hu, ran⟩ := bind_ok ran
  exact h (register_ok hu) ctx mid x s' ran

/-- **Constructor positions of a block's inductives**: every inductive the block compile reads at
a member lists constructors, under its constructor names, at their declared positions. -/
def PositionsIn (E : Ix.Environment) (all : Ix.Set Ix.Name) : Prop :=
  ∀ n, all.contains n = true → ∀ val, E.get? n = some (.inductInfo val) → ∀ cs : List Ix.ConstructorVal,
    List.Forall₂ (fun c ctor => E.get? c = some (.ctorInfo ctor)) val.ctors.toList cs →
      ∀ j (hj : j < cs.length), cs[j].cidx = j

/-- **The block compile's members loop reads members at their constructor positions.** -/
theorem members_positions (ctx : CompileEnv × BlockEnv) (all : Ix.Set Ix.Name) (pos : PositionsIn ctx.1.env all) :
    Claims.RunPost ctx (fun cs : Array MutConst => ∀ m ∈ cs, MutualProjections.ConstructorPositions m)
      (forIn all #[] fun n (acc : Array Ix.MutConst) => do
        match ← findConst n with
        | .inductInfo val => pure (ForInStep.yield (acc.push (← MutConst.mkIndc val)))
        | .defnInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromDefinitionVal val)))
        | .opaqueInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromOpaqueVal val)))
        | .thmInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromTheoremVal val)))
        | .recInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.recr val)))
        | _ => pure (ForInStep.yield acc)) := by
  rw [Std.HashSet.forIn_eq_forIn_toList]
  refine Claims.RunPost.forIn ctx _ _ all.toList (fun n hn acc hacc => ?_) #[] (by simp)
  have hin : all.contains n = true :=
    Std.HashSet.mem_iff_contains.1 (Std.HashSet.mem_of_mem_toList hn)
  have push : ∀ m, MutualProjections.ConstructorPositions m →
      ∀ m' ∈ acc.push m, MutualProjections.ConstructorPositions m' := by
    intro m hm m' hm'
    rcases Array.mem_push.1 hm' with hm' | rfl
    · exact hacc m' hm'
    · exact hm
  have none : ∀ m : MutConst, m.ctors = #[] → MutualProjections.ConstructorPositions m :=
    fun m h index inside => by simp [h] at inside
  refine Claims.RunPost.bind (Claims.RunPost.findConst ctx n) fun ci hci => ?_
  split
  · rename_i val
    refine Claims.RunPost.bind (q := MutualProjections.ConstructorPositions) ?_
      fun m hm => Claims.RunPost.pure (push m hm)
    intro s m s' ran
    obtain ⟨cs, looked, rfl⟩ := SourceConstructorPositions.mkIndc_lookups ctx val s (by rw [ran])
    intro index inside
    simp only [MutConst.ctors, List.size_toArray] at inside ⊢
    simpa using pos n hin val hci cs looked index inside
  · exact Claims.RunPost.pure (push _ (none _ rfl))
  · exact Claims.RunPost.pure (push _ (none _ rfl))
  · exact Claims.RunPost.pure (push _ (none _ rfl))
  · exact Claims.RunPost.pure (push _ (none _ rfl))
  · exact Claims.RunPost.pure hacc

/-- **A block compile's claims resolve**, when its inductives' constructors are at their
positions: a lone constant's compile is a lone record, and a mutual one's rows resolve
(`mutual_claims`); the block's `Muts` registration refuses a mutual block without classes. -/
theorem compileBlock_claims {ctx : CompileEnv × BlockEnv} {lo : Ix.Name} {all : Ix.Set Ix.Name}
    {s s' : BlockState} {r : BlockResult} (h : rawRun (compileBlock lo all) ctx s = (.ok r, s'))
    (pos : PositionsIn ctx.1.env all) (wire : r.block.wireWF) : ClaimsResolve r := by
  unfold compileBlock at h
  obtain ⟨const, s₁, hc, h⟩ := bind_ok h
  dsimp only at h
  -- the kind test (an inductive, a constructor, another constant), then the lone test
  split at h <;> split at h
  all_goals try (rename_i hcond; simp at hcond; done)
  -- left: an inductive's and a constructor's mutual compile, another constant's lone and mutual
  -- compiles
  rotate_left 2
  · obtain ⟨none, lone⟩ := constantInfo_lone _ (by assumption) (by assumption) ctx s₁ r s' h
    exact ⟨fun _ => lone, fun p hp => by rw [none] at hp; exact absurd hp (by simp)⟩
  all_goals
    obtain ⟨cs, s₂, hcs, h⟩ := bind_ok h
    obtain ⟨out, s₄, hout, h⟩ := bind_ok h
    have same : BlockRecords.recordsOf r = BlockRecords.recordsOf out := by
      revert h
      refine BlockRecords.Returns.elim
        (P := fun (x : BlockResult) => BlockRecords.recordsOf x = BlockRecords.recordsOf out) ?_
      repeat returns_step
    have classes : IsMuts out.block.info → sourceClasses cs ≠ [] := by
      intro hm
      obtain ⟨ms, hms⟩ : ∃ ms, out.block.info = .muts ms := by
        revert hm
        cases out.block.info <;> simp [IsMuts]
      revert h
      refine BlockRecords.Returns.elim (P := fun (_ : BlockResult) => sourceClasses cs ≠ []) ?_
      simp only [hms, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine BlockRecords.Returns.bind fun _ => ?_
      refine Returns.bind_register fun hne => ?_
      exact BlockRecords.Returns.pure hne
    have tail := And.intro same classes
    have positions := members_positions ctx all pos s₁ cs s₂ hcs
    have outWire : out.block.wireWF := by
      have hb := (Prod.mk.inj tail.1).1
      rw [← hb]
      exact wire
    exact (mutual_claims positions hout outWire tail.2).transfer tail.1

/-- **A block's claims resolve**, for a block whose inductives' constructors are at their
positions. -/
theorem runBlock_claims {cenv : CompileEnv} {all : Ix.Set Ix.Name} {lo : Ix.Name} {r : BlockResult}
    {cache : BlockState} (hr : runBlock cenv all lo = .ok (r, cache)) (pos : PositionsIn cenv.env all) :
    ClaimsResolve r :=
  compileBlock_claims (Ix.CompileCert.run_success (BlockRecords.runBlock_compiles hr)) pos
    (BlockWire.blocksWire _ _ _ _ _ hr)

/-! ## Constructor positions, from Source acceptance -/

/-- A component's group is never an inductive block's. -/
theorem componentGroup_not_inductive {env : Ix.Environment} {members : Ix.Set Ix.Name}
    {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal}
    (h : componentGroup env members = some (.inductive types ctors recs)) : False := by
  rw [Ix.Cert.SourceStoredNames.component_default] at h
  unfold Ix.LeanIngress.componentGroupUsing at h
  generalize (Array.filterMapM (m := Id) (fun x => env.consts.get? x) members.toArray :
    Array Ix.ConstantInfo) = cis at h
  dsimp only [Id.run, bind, pure] at h
  generalize (cis.filter (fun x => !Ix.LeanIngress.isFamily x)).qsort
    (fun a b => Ix.sourceOrderLt (a.blockPosition, a.getCnst.name)
      (b.blockPosition, b.getCnst.name)) = others at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · obtain ⟨l⟩ := others
        rcases l with _ | ⟨c, _ | ⟨c₂, rest⟩⟩
        · cases h
        · cases c <;> cases h
        · cases h

/-- **An inductive group of quotient Source's groups is the group of a block**, laid out with
recursor candidates the environment stores. -/
theorem groupsOf_inductive (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    ∀ types ctors recs, Group.inductive types ctors recs ∈ groupsOf env blocks →
      ∃ first cands, (∀ r ∈ cands, ∃ k, (k, Ix.ConstantInfo.recInfo r) ∈ env.consts.toList) ∧
        inductiveGroup env first cands = .inductive types ctors recs := by
  unfold groupsOf
  simp only [Id.run, Std.HashMap.forIn_eq_forIn_toList, idBind, idPure]
  refine SourceStoredNames.forIn_id_prop (I := fun acc : Array Group => ∀ types ctors recs,
      Group.inductive types ctors recs ∈ acc → ∃ first cands,
        (∀ r ∈ cands, ∃ k, (k, Ix.ConstantInfo.recInfo r) ∈ env.consts.toList) ∧
          inductiveGroup env first cands = .inductive types ctors recs) _ ?_ (fun _ h => h) _ ?_
  · intro x _ s hs
    split
    · exact hs
    · intro types ctors recs hm
      rcases Array.mem_push.mp hm with hm | heq
      · exact hs _ _ _ hm
      · unfold unplaced at heq
        split at heq <;> cases heq
  · refine SourceStoredNames.forIn_id_prop (I := fun acc : Array Group => ∀ types ctors recs,
        Group.inductive types ctors recs ∈ acc → ∃ first cands,
          (∀ r ∈ cands, ∃ k, (k, Ix.ConstantInfo.recInfo r) ∈ env.consts.toList) ∧
            inductiveGroup env first cands = .inductive types ctors recs) _ ?_ (fun _ h => h) _ ?_
    · intro x _ s hs
      split
      · rename_i g' hg'
        intro types ctors recs hm
        rcases Array.mem_push.mp hm with hm | heq
        · exact hs _ _ _ hm
        · rw [← heq] at hg'
          exact (componentGroup_not_inductive hg').elim
      · exact hs
    · refine SourceStoredNames.forIn_id_prop (I := fun acc : Array Group => ∀ types ctors recs,
          Group.inductive types ctors recs ∈ acc → ∃ first cands,
            (∀ r ∈ cands, ∃ k, (k, Ix.ConstantInfo.recInfo r) ∈ env.consts.toList) ∧
              inductiveGroup env first cands = .inductive types ctors recs) _ ?_ (fun _ h => h) _ ?_
      · intro x _ s hs
        split
        · split
          · intro types ctors recs hm
            rcases Array.mem_push.mp hm with hm | heq
            · exact hs _ _ _ hm
            · refine ⟨_, _, ?_, heq.symm⟩
              intro r hr
              refine (SourceStoredNames.forIn_id_prop
                (I := fun m : Ix.Map Ix.LeanIngress.TableName (Array Ix.RecursorVal) =>
                  ∀ key, ∀ r ∈ m.getD key #[], ∃ k, (k, Ix.ConstantInfo.recInfo r) ∈ env.consts.toList)
                (Q := fun m => ∀ r ∈ m.getD x.fst #[],
                  ∃ k, (k, Ix.ConstantInfo.recInfo r) ∈ env.consts.toList)
                _ ?_ (fun t ht => ht x.fst) _ ?_) r hr
              · intro y hy m hm
                split
                · rename_i rv hrv
                  split
                  · intro key r' hr'
                    simp only [ForInStep.value] at hr'
                    rw [Std.HashMap.getD_insert] at hr'
                    split at hr'
                    · rcases Array.mem_push.mp hr' with hr' | rfl
                      · exact hm _ r' hr'
                      · obtain ⟨a, b⟩ := y
                        simp only at hrv
                        subst hrv
                        exact ⟨a, hy⟩
                    · exact hm key r' hr'
                  · exact hm
                · exact hm
              · intro key r' hr'
                simp at hr'
          · exact hs
        · exact hs
      · intro _ _ _ hm
        exact absurd hm (Array.not_mem_empty _)

/-- A definitions group converts only definitions. -/
theorem convertDefinitions_shapes {ms : Array Ix.ConstantInfo} {c : Converted} (h : convertDefinitions ms = .ok c) :
    ∀ ci ∈ ms, (definitionShape ci).isSome = true := by
  unfold convertDefinitions at h
  obtain ⟨shapes, hshapes, -⟩ := except_bind_ok.mp h
  have each := ReaderUnits.array_mapM_ok hshapes
  intro ci hci
  obtain ⟨y, -, hy⟩ := SourceConstructorPositions.forall₂_mem each (Array.mem_toList_iff.mpr hci)
  revert hy
  cases hs : definitionShape ci <;> cases hv : Ix.LeanIngress.definitionValue ci <;> simp

/-- **A closure inductive's constructors are at their positions**: the accepted closure puts the
inductive in an inductive group (`stored_grouped`, `prepared_converts`), whose layout checks each
constructor's declared index against its position (`inductiveGroup_spec`, `ctors_agree`). -/
theorem closure_positions {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) {n : Ix.Name} {val : Ix.InductiveVal}
    (hn : sub.consts.get? n = some (.inductInfo val)) {cs : List Ix.ConstructorVal}
    (looked : List.Forall₂ (fun c ctor => sub.consts.get? c = some (.ctorInfo ctor)) val.ctors.toList cs) :
    ∀ j (hj : j < cs.length), cs[j].cidx = j := by
  obtain ⟨-, pre, ds, -, hprep, -⟩ := P.source
  have hcol := SourceDeclares.preparedAt_collapsed hprep
  obtain ⟨k, hk⟩ := SourceStoredNames.lookup_stored hn
  have named : ∀ k' ci', (k', ci') ∈ sub.consts.toList → ci'.getCnst.name = k' := fun k' ci' h =>
    inputsNamed P.compiled k' ci' (SourceStoredNames.stored_input P h)
  have unique : ∀ k' ci₁ ci₂, (k', ci₁) ∈ sub.consts.toList → (k', ci₂) ∈ sub.consts.toList → ci₁ = ci₂ := by
    intro k' ci₁ ci₂ h₁ h₂
    have e := SourceStoredNames.stored_get h₁
    rw [SourceStoredNames.stored_get h₂] at e
    exact (Option.some.inj e).symm
  -- a stored constant named `k` is the inductive: its key is its name
  have own : ∀ x ci, sub.consts.get? x = some ci → ci.getCnst.name = k → ci = .inductInfo val := by
    intro x ci hx hname
    obtain ⟨k', hk'⟩ := SourceStoredNames.lookup_stored hx
    have := named k' ci hk'
    rw [hname] at this
    subst this
    exact unique _ _ _ hk' hk
  obtain ⟨g, hg, hkg⟩ := SourceDeclares.stored_grouped sub _ hk
  obtain ⟨c, hc⟩ := SourceStoredNames.prepared_converts hcol g hg
  obtain ⟨k₁, ci₁, hk₁, hname₁, hkind₁⟩ := (LayoutExtra.groupsOf_kinded sub _ g hg c hc).1 k hkg
  cases own _ _ (SourceStoredNames.stored_get hk₁) hname₁
  cases g with
  | «inductive» types ctors recs =>
    obtain ⟨first, cands, hcands, hlayout⟩ := groupsOf_inductive sub _ types ctors recs hg
    obtain ⟨members, classes⟩ :=
      SourceConstructorPositions.inductiveGroup_spec sub first cands types ctors recs hlayout
    simp only [Group.names, Array.mem_append, Array.mem_map, Array.mem_flatMap] at hkg
    rcases hkg with (⟨v, hv, hvk⟩ | ⟨cs', hcs', ctor, hctor, hck⟩) | ⟨r, hr, hrk⟩
    · -- a type of the group
      obtain ⟨m, -, hmv⟩ := ReaderUnits.forall₂_mem_right members v (Array.mem_toList_iff.mpr hv)
      obtain ⟨present, -⟩ := SourceConstructorPositions.memberValue_some hmv
      cases own _ _ present hvk
      obtain ⟨cs₀, -, hclass⟩ := SourceConstructorPositions.forall₂_mem classes (Array.mem_toList_iff.mpr hv)
      obtain ⟨l, listed, rfl⟩ := Option.map_eq_some_iff.mp hclass
      have recorded := (SourceConstructorPositions.ctorsValue_forall₂ sub val.cnst.name).mp listed
      rw [Array.toList_zipIdx] at recorded
      obtain ⟨same, positions⟩ :=
        SourceConstructorPositions.ctors_agree sub val.cnst.name val.ctors.toList 0 recorded looked
      intro j hj
      subst same
      simpa using positions j hj
    · -- a constructor of the group: stored as a constructor
      exfalso
      obtain ⟨v, -, hclass⟩ := ReaderUnits.forall₂_mem_right classes cs' (Array.mem_toList_iff.mpr hcs')
      obtain ⟨l, listed, hl⟩ := Option.map_eq_some_iff.mp hclass
      have recorded := (SourceConstructorPositions.ctorsValue_forall₂ sub v.cnst.name).mp listed
      rw [← hl] at hctor
      obtain ⟨x, -, hx⟩ := ReaderUnits.forall₂_mem_right recorded ctor (by simpa using hctor)
      obtain ⟨present, -⟩ := SourceConstructorPositions.ctorValue_some hx
      cases own _ _ present hck
    · -- a recursor of the group: a stored recursor candidate
      exfalso
      obtain ⟨k₂, hk₂⟩ := hcands r (SourceStoredNames.blockRecursors_mem
        (SourceConstructorPositions.inductiveGroup_recursors sub first cands types ctors recs hlayout) r hr)
      cases own _ _ (SourceStoredNames.stored_get hk₂) hrk
  | definitions ms =>
    exfalso
    have := convertDefinitions_shapes hc _ hkind₁
    simp [definitionShape] at this
  | «axiom» v => cases hkind₁
  | quot v => cases hkind₁
  | invalid names e => cases hc

/-! ## Published records resolve -/

/-- **The constructors a closure block's inductives list are at their positions**: the block's
members are closure names, so are their constructors, and the closure's lookups are the
input's. -/
theorem closure_block_positions {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) {cenv : CompileEnv} {A : Ix.Set Ix.Name}
    (henv : ∀ x, cenv.env.get? x = env.consts.get? x) (hmembers : LayoutExtra.MembersIn sub A) :
    PositionsIn cenv.env A := by
  have hcl := P.source.1
  intro n hn val hval cs looked
  rw [henv] at hval
  have hsub : (sub.consts.get? n).isSome = true := hmembers n hn
  have hsame := CompiledRefs.closure_same hcl hsub
  refine closure_positions P (n := n) (hsame.trans hval) ?_
  refine SourceConstructorPositions.forall₂_mono_mem looked fun c hc ctor hctor => ?_
  rw [henv] at hctor
  have hcsub : (sub.consts.get? c).isSome = true :=
    CompiledRefs.sub_of_ref hcl hsub hval (FreshSnapshot.refsOf_induct val (Array.mem_toList_iff.mp hc))
      (by rw [hctor]; rfl)
  rw [CompiledRefs.closure_same hcl hcsub]
  exact hctor

/-- **A published closure name's record resolves in the artifact's store**
(`SingletonSegments.PublishedResolve`): the record is a primary claim of its block's compile
(`claimedIn_of`), whose claims resolve in a store holding the block (`runBlock_claims`), and the
artifact stores the block. -/
theorem publishedResolve {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) : SingletonSegments.PublishedResolve ixe sub := by
  intro n ci named hn hnamed c hc
  obtain ⟨cenv, A, k, r, cache, b, henv, -, hmembers, hr, hclaim, hstored, hblock⟩ :=
    LayoutExtra.claimedIn_of P n ci hn named.addr (by rw [ClosureLayout.addrOf, hnamed]; rfl)
  have wire := BlockWire.blocksWire _ _ _ _ _ hr
  have shape := BlockLayout.runBlock_shape hr
  have blockRec : recordAt ixe r.blockAddr = some r.block := by
    rw [shape.bytes] at hblock
    exact BlockLayout.recordAt_ser wire (BlockRecords.runBlock_bounded hr).1 hblock
  have claims := runBlock_claims hr (closure_block_positions P henv hmembers)
  unfold Resolution.claimWrites at hclaim
  split at hclaim
  · rename_i hempty
    simp only [List.mem_toArray, List.mem_singleton, Prod.mk.injEq] at hclaim
    obtain ⟨-, haddr, -⟩ := hclaim
    rw [haddr, blockRec] at hc
    cases hc
    exact lone_resolves (claims.1 hempty) _ _
  · obtain ⟨p, hp, e⟩ := Array.mem_map.mp hclaim
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, haddr, hbytes⟩ := e
    have pwire : p.2.1.wireWF := by
      rcases shape.rows p hp with same | ⟨pw, -, -⟩
      · rw [same]; exact wire
      · exact pw
    rw [← haddr, ← hbytes] at hstored
    have prec := BlockLayout.recordAt_ser pwire ((BlockRecords.runBlock_bounded hr).2 p hp) hstored
    rw [← haddr, prec] at hc
    cases hc
    rw [← haddr]
    exact claims.2 p hp _ blockRec

/--
info: 'Ix.Cert.ClosureResolve.publishedResolve' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms publishedResolve

/--
info: 'Ix.Cert.ClosureResolve.closure_positions' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closure_positions

end Ix.Cert.ClosureResolve
