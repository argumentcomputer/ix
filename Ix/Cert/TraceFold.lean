import Ix.Cert.GroupRuns
import Ix.Cert.BindingsResolve

/-! # The fold's facts in the trace's forms

`TraceSegments.TraceNeeds` asks, of the block the fold compiled for each of quotient Source's
groups, for the block's run, its claim, and facts about the fold's state the block was compiled
at. `GroupRuns` gives the run and the claim at the block's `FoldBlock`; this module gives the
rest, in the forms the segment theorems take:

* `FoldBlock.bound`: the snapshot's bindings resolve in the artifact (`BindingsResolve`);
* `FoldBlock.fresh_of`: the block's members are unbound at the snapshot;
* `GroupRuns.FoldBlock.blobsKept` (in `GroupRuns`): the blobs the run reads are the artifact's,
  since the block compile's tail after the members' compile only adds names (`GroupRuns.Grows`);
* `cacheRefs`: every entry of a compiled block's reference table is a mentioned name's binding
  or a blob of `runBlock`'s final state (`CompiledRefs.CacheRefs`);
* `FoldBlock.bound_exact`: every name the snapshot binds is exactly a key the input stores a
  constant under (a claim's name: a member's or constructor's own name, or a block's key, which
  is an element of a block of the input's condensation, `blockKey_exact`);
* `FoldBlock.mentionsPublished`: a name a closure constant's term mentions that the snapshot
  binds is a closure constant published at its binding under that exact name, with each group
  kind's mentions a closure constant's (`definitions_mentioned`, `definition_mentioned`,
  `axiom_mentioned`, `quot_mentioned`, `types_mentioned`, `recursors_mentioned`);
* `definitions_exactNames`, `definitions_distinct`: a block of definitions' members have distinct
  names, and a name a member mentions with a member's ingress key is that member;
* `singleton_compiled`, `lone_compiled`: a singleton group's constant compiles alone at its fold
  block, published at its record;
* `definitions_occ_input`: a name a block of definitions applies is an input constant. -/

namespace Ix.Cert.TraceFold

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState Ix.Cert.Resolution Ix.Cert.Schedule
open Ix.Cert.GroupRuns (FoldBlock)
open Ix.Cert.BlockContext (BoundResolve)

variable {env sub : Ix.Environment} {ixe : Ixon.Env} {failures : Failures} {snap : DriverAcc}
  {rep : Ix.Name} {all : Ix.Set Ix.Name} {r : BlockResult} {c : BlockState}

/-! ## The snapshot's bindings and the block's members -/

/-- **The snapshot's bindings resolve in the artifact** (`bound`, `bound₁`, `bound₂`), when the
input's inductives list their constructors at their positions. -/
theorem _root_.Ix.Cert.GroupRuns.FoldBlock.bound (fb : FoldBlock env sub ixe failures snap rep all r c)
    (idx : BindingsResolve.ConstructorIndices env) : BoundResolve ixe snap.cenv := by
  obtain ⟨_, _, _, hu, hrun, hsnap, -⟩ := fb.fold
  exact BindingsResolve.boundResolve_onRun hu idx hrun hsnap

/-- **The members of the block are unbound at the snapshot** (`BlockCompiled.fresh`). -/
theorem _root_.Ix.Cert.GroupRuns.FoldBlock.fresh_of {α : Type} (fb : FoldBlock env sub ixe failures snap rep all r c)
    {xs : List α} {name : α → Ix.Name} (mem : ∀ x ∈ xs, all.contains (name x) = true) :
    ∀ x ∈ xs, snap.cenv.nameToAddr.get? (name x) = none :=
  fun x hx => fb.fresh (name x) (mem x hx)

/-! ## The reference table at the merged cache -/

/-- **`RefTables.runBlock_refs` at `runBlock`'s final state** (`CompiledRefs.CacheRefs`): a lone
constant's compile ends there, and the block compile's tail after a mutual compile keeps every
blob it read (`GroupRuns.runBlock_paths`). -/
theorem cacheRefs : CompiledRefs.CacheRefs := by
  intro cenv all lo r c hr a ha
  obtain ⟨const, hconst, paths⟩ := GroupRuns.runBlock_paths hr
  rcases paths with ⟨hcond, hs⟩ | ⟨-, cs, out, s₄, hloop, hout, hext, hrec⟩
  · have hi : ∀ v, const = .inductInfo v → False := by
      rintro v rfl
      simp [GroupRuns.isIndConst] at hcond
    have hc : ∀ v, const = .ctorInfo v → False := by
      rintro v rfl
      simp [GroupRuns.isIndConst] at hcond
    obtain ⟨hI, same⟩ := RefTables.Holds.constantInfo (B := bindingView {})
      (N := fun x => all.contains x = true ∨ x = lo) hconst (Or.inr rfl) hi hc _ {} r c RefTables.refsOK_empty
      trivial hs
    exact hI.2 a (by rw [← same]; exact ha)
  · have members := RefTables.members_covers (cenv, { all, current := lo, mutCtx := default, univCtx := [] }) all
      (N := fun x => all.contains x = true ∨ x = lo) (fun x hx => .inl hx)
    rw [Std.HashSet.forIn_eq_forIn_toList] at members
    have cov := members {} cs {} hloop
    obtain ⟨hI, refs⟩ := RefTables.Holds.mutualBlock (B := bindingView {}) (sourceClasses cs)
      (fun cls hcls m hm => cov m (Claims.mem_sourceClasses hcls hm)) _ {} out s₄ RefTables.refsOK_empty trivial hout
    have block : r.block = out.block := (Prod.mk.inj hrec).1
    exact RefTables.Allowed.mono (hI.2 a (by rw [← refs, ← block]; exact ha)) hext


/-! ## The condensation's blocks hold the input's own keys

`Condense.blocksOfDisc_mem` reads a block's members up to `==` (the stored hash). Here they are
read exactly: a member of a block of the input's condensation is a key the input stores a
constant under. -/

theorem mem_toList_insert {β : Type} {m : Std.HashMap Ix.Name β} {a k : Ix.Name} {b v : β}
    (h : (k, v) ∈ (m.insert a b).toList) : k = a ∨ (k, v) ∈ m.toList := by
  rcases List.mem_cons.mp (Std.HashMap.toList_insert_perm.mem_iff.mp h) with e | hf
  · exact .inl (Prod.mk.inj e).1
  · exact .inr (List.mem_filter.mp hf).1

theorem set_mem_toList_insert {s : Ix.Set Ix.Name} {a x : Ix.Name} (h : x ∈ (s.insert a).toList) :
    x = a ∨ x ∈ s.toList := by
  have h' := Std.HashSet.toList_insert_perm.mem_iff.mp h
  split at h'
  · exact .inr h'
  · exact List.mem_cons.mp h'

/-- The driver's reference graph is keyed by the input's keys. -/
theorem envSerial_key {E : Ix.Environment} {n : Ix.Name} {rs : Ix.Set Ix.Name}
    (h : (n, rs) ∈ (Ix.GraphM.envSerial E).toList) : ∃ ci, (n, ci) ∈ E.consts.toList := by
  unfold Ix.GraphM.envSerial at h
  simp only [Id.run, Std.HashMap.forIn_eq_forIn_toList, List.forIn_pure_yield_eq_foldl] at h
  refine (Condense.foldl_inv (fun m : Ix.Map Ix.Name (Ix.Set Ix.Name) =>
      ∀ n rs, (n, rs) ∈ m.toList → ∃ ci, (n, ci) ∈ E.consts.toList) _ _ _ ?_ ?_) n rs h
  · intro n rs h
    simp at h
  · intro m x hx ih n rs h
    obtain ⟨k, ci⟩ := x
    dsimp only at h
    rcases mem_toList_insert h with rfl | h
    · exact ⟨ci, hx⟩
    · exact ih n rs h

/-- The ground graph is keyed by the input's keys. -/
theorem groundSplit_key {E : Ix.Environment} {n : Ix.Name} {rs : Ix.Set Ix.Name}
    (h : (n, rs) ∈ (groundSplit E).1.toList) : ∃ ci, (n, ci) ∈ E.consts.toList := by
  unfold groundSplit at h
  dsimp only at h
  split at h
  · exact envSerial_key h
  · rw [Std.HashMap.fold_eq_foldl_toList] at h
    refine (Condense.foldl_inv (fun m : Ix.Map Ix.Name (Ix.Set Ix.Name) =>
        ∀ n rs, (n, rs) ∈ m.toList → ∃ ci, (n, ci) ∈ E.consts.toList) _ _ _ ?_ ?_) n rs h
    · intro n rs h
      simp at h
    · intro m x hx ih n rs h
      split at h
      · exact ih n rs h
      · rcases mem_toList_insert h with rfl | h
        · exact envSerial_key hx
        · exact ih n rs h

/-- **A block's members are its discovery map's nodes, exactly.** -/
theorem blocksOfDisc_exact {bd : Std.HashMap UInt64 (Ix.Name × Ix.Name)} {rep x : Ix.Name}
    {all : Ix.Set Ix.Name} (h : (Condense.blocksOfDisc bd).get? rep = some all) (hx : x ∈ all.toList) :
    ∃ key val, bd.get? key = some val ∧ val.1 = x := by
  unfold Condense.blocksOfDisc at h
  simp only [Id.run, Std.HashMap.forIn_eq_forIn_toList, List.forIn_pure_yield_eq_foldl] at h
  change (List.foldl (fun (b : Ix.Map Ix.Name (Ix.Set Ix.Name) × Ix.Map Ix.Name Ix.Name) a =>
      (Std.HashMap.alter b.fst a.2.snd fun x => match x with
        | some s => some (Std.HashSet.insert s a.2.fst)
        | none => some {a.2.fst},
       Std.HashMap.insert b.snd a.2.fst a.2.snd)) (∅, ∅) bd.toList).fst.get? rep = some all at h
  refine Condense.foldl_inv (fun s : Ix.Map Ix.Name (Ix.Set Ix.Name) × Ix.Map Ix.Name Ix.Name => ∀ rep all x,
      s.1.get? rep = some all → x ∈ all.toList → ∃ key val, bd.get? key = some val ∧ val.1 = x) _ _ _
    (fun rep all x h _ => by rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at h; cases h)
    (fun s e he hs rep all x h hx => ?_) rep all x h hx
  have hbe : bd.get? e.1 = some e.2 := by
    rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.mem_toList_iff_getElem?_eq_some]
    exact he
  dsimp only at h
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_alter] at h
  split at h
  · rename_i same
    split at h
    · rename_i s hs'
      cases h
      rcases set_mem_toList_insert hx with e' | hx
      · exact ⟨e.1, e.2, hbe, e'.symm⟩
      · rw [Std.HashMap.getElem?_congr same, ← Std.HashMap.get?_eq_getElem?] at hs'
        exact hs _ _ x hs' hx
    · cases h
      rw [show ({e.2.1} : Ix.Set Ix.Name) = (∅ : Ix.Set Ix.Name).insert e.2.1 from rfl] at hx
      rcases set_mem_toList_insert hx with e' | hx
      · exact ⟨e.1, e.2, hbe, e'.symm⟩
      · simp at hx
  · rw [← Std.HashMap.get?_eq_getElem?] at h
    exact hs rep all x h hx

/-- **A block's members are its graph's keys, exactly.** -/
theorem block_exact {refs : Ix.Map Ix.Name (Ix.Set Ix.Name)} {rep x : Ix.Name} {all : Ix.Set Ix.Name}
    (h : (Ix.CondenseM.run refs).blocks.get? rep = some all) (hx : x ∈ all.toList) :
    ∃ rs, (x, rs) ∈ refs.toList := by
  obtain ⟨hr, hv, e⟩ := Condense.blocks_eq refs
  rw [e] at h
  obtain ⟨key, val, hval, rfl⟩ := blocksOfDisc_exact h hx
  obtain ⟨v, hv', rfl⟩ := Condense.discOf_get hval
  have hlt : v < (Condense.nodesOf refs).1.size := by simpa [Condense.namesOf] using hv'
  have hmem : (Condense.nodesOf refs).1[v] ∈ refs.toList := by
    rw [← (Condense.nodesOf_spec refs).1]
    exact Array.getElem_mem_toList hlt
  have e : (Condense.namesOf refs)[v] = ((Condense.nodesOf refs).1[v]).1 := by simp [Condense.namesOf]
  show ∃ rs, ((Condense.namesOf refs)[v], rs) ∈ refs.toList
  rw [e]
  exact ⟨_, hmem⟩

/-- **A block's key is a key the input stores a constant under.** -/
theorem blockKey_exact {E : Ix.Environment} {rep : Ix.Name} {all : Ix.Set Ix.Name}
    (h : (Ix.CondenseM.run (groundSplit E).1).blocks.get? rep = some all) :
    ∃ ci, (blockKey rep all, ci) ∈ E.consts.toList := by
  have hne := Condense.condense_nonempty h
  have ne : all.toArray ≠ #[] := by
    intro e
    have := congrArg Array.size e
    rw [Std.HashSet.size_toArray] at this
    rw [Std.HashSet.isEmpty_eq_size_eq_zero] at hne
    simp [this] at hne
  have hm : blockKey rep all ∈ all.toArray := canonicalKey_mem (dflt := rep) ne
  rw [← Std.HashSet.toArray_toList] at hm
  obtain ⟨rs, hrs⟩ := block_exact h (List.mem_toArray.mp hm)
  exact groundSplit_key hrs

/-! ## A binding of the fold is a key of the input -/

/-- **Every name a state the fold reaches binds is a key the input stores a constant under**:
the binding is a claim of a compiled block, the block's key or a projection's name, which is a
member's or a constructor's own name (`inputsNamed`). -/
theorem reach_exact {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (compiled : compileReport env = .ok (ixe, failures)) {init acc : DriverAcc}
    (empty : init.cenv.nameToAddr = {}) (reads : ∀ x, init.cenv.env.get? x = env.consts.get? x)
    (h : Reach (CompiledRefs.envBlocks env) init acc) {n : Ix.Name} {a : Address}
    (hn : acc.cenv.nameToAddr.get? n = some a) : ∃ ci, (n, ci) ∈ env.consts.toList := by
  obtain ⟨b, ⟨snap, pre, rep, all, hsnap, -, -, hall, -, hclaim⟩, -⟩ :=
    reach_provenance (provenance_of_empty empty) h n a hn
  have hE : ∀ x, snap.cenv.env.get? x = env.consts.get? x := fun x => by
    rw [reach_env hsnap]
    exact reads x
  have exactOf : ∀ k ci, env.consts.get? k = some ci → (ci.getCnst.name, ci) ∈ env.consts.toList := by
    intro k ci hk
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hk
    obtain ⟨k', -, hm⟩ := hk
    rw [inputsNamed compiled k' ci hm]
    exact hm
  generalize ho : auxBlockOutcome snap.cenv (blockKey rep all) all = o at hclaim
  cases o with
  | failed msg => exact False.elim hclaim
  | compiled r cs =>
    have hr := auxBlockOutcome_compiled ho
    have hclaim' : (n, a, b) ∈ claimWrites (blockKey rep all) r := hclaim
    rcases ClosureClaims.claim_name hclaim' with rfl | ⟨row, hrow, rfl⟩
    · exact blockKey_exact (E := { consts := env.consts }) hall
    · obtain ⟨m, ⟨k, ci, -, hci, hname, hctors⟩, hx⟩ :=
        Claims.compileBlock_names (run_success (BlockRecords.runBlock_compiles hr)) row hrow
      have hci' : env.consts.get? k = some ci := (hE k).symm.trans hci
      rcases hx with hx | ⟨ctor, hctor, hx⟩
      · rw [hx, hname]
        exact ⟨ci, exactOf k ci hci'⟩
      · obtain ⟨iv, c, -, -, hc⟩ := hctors ctor hctor
        have hc' : env.consts.get? c = some (.ctorInfo ctor) := (hE c).symm.trans hc
        rw [hx]
        exact ⟨_, exactOf c _ hc'⟩

/-- **A name the fold block's snapshot binds is a key the input stores a constant under.** -/
theorem _root_.Ix.Cert.GroupRuns.FoldBlock.bound_exact (compiled : compileReport env = .ok (ixe, failures))
    (fb : FoldBlock env sub ixe failures snap rep all r c) {n : Ix.Name} {a : Address}
    (hn : snap.cenv.nameToAddr.get? n = some a) : ∃ ci, (n, ci) ∈ env.consts.toList := by
  obtain ⟨_, cenv₀, sched, -, hrun, hsnap, -⟩ := fb.fold
  obtain ⟨-, h₀, henv, -⟩ := hrun
  exact reach_exact compiled ((init_nameToAddr _ _ _).trans h₀)
    (fun x => by rw [henv, ClosureClaims.view_get, ClosureClaims.input_get]) (onRun_reach hsnap) hn

theorem lookup_empty {cenv : CompileEnv} {m : Ix.Name} {a : Address} (h : lookupBinding cenv {} m = some a) :
    cenv.nameToAddr.get? m = some a := by
  have hnone : ((∅ : Bindings)).get? m = none := Std.HashMap.get?_eq_getElem?.trans Std.HashMap.getElem?_empty
  unfold lookupBinding at h
  rw [show ((({} : Bindings)).get? m) = none from hnone, Option.orElse_none] at h
  exact h

/-! ## Names the sources mention, published -/

/-- **A name a term of a closure constant mentions.** -/
def MentionedIn (env sub : Ix.Environment) (m : Ix.Name) : Prop :=
  ∃ x ci e, (sub.consts.get? x).isSome = true ∧ env.consts.get? x = some ci ∧ e ∈ termsOf ci ∧
    GraphWalk.Refs m e

theorem mentionedIn_of_stored {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    (hcl : IsClosure env roots sub) {x : Ix.Name} {ci : Ix.ConstantInfo} (hx : (x, ci) ∈ sub.consts.toList)
    {e : Ix.Expr} (he : e ∈ termsOf ci) {m : Ix.Name} (hr : GraphWalk.Refs m e) : MentionedIn env sub m := by
  have hs := SourceStoredNames.stored_get hx
  have hsome : (sub.consts.get? x).isSome = true := by rw [hs]; rfl
  exact ⟨x, ci, e, hsome, (CompiledRefs.closure_same hcl hsome).symm.trans hs, he, hr⟩

/-- **A mentioned name the snapshot binds is a closure constant published at its binding**, under
that exact name: the binding is a key of the input (`bound_exact`), so the closure holds it, the
snapshot's resolution publishes it, and the artifact's key that hashes like it is it
(`nameHashes_distinct`). -/
theorem _root_.Ix.Cert.GroupRuns.FoldBlock.mention_published {env : Ix.Environment} {roots : List Ix.Name}
    {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) (fb : FoldBlock env sub ixe failures snap rep all r c)
    {m : Ix.Name} (hm : MentionedIn env sub m) {a : Address} (hb : lookupBinding snap.cenv {} m = some a) :
    ∃ named', (m, named') ∈ ixe.named.toList ∧ named'.addr = a ∧ (sub.consts.get? m).isSome = true := by
  have hcl : IsClosure env roots sub := P.source.1
  have hn := lookup_empty hb
  obtain ⟨cm, hcm⟩ := fb.bound_exact P.compiled hn
  have hmE : (env.consts.get? m).isSome = true := by rw [SourceStoredNames.stored_get hcm]; rfl
  obtain ⟨x, ci, e, hx, hci, he, hr⟩ := hm
  have hsub := CompiledRefs.sub_of_ref hcl hx hci (GraphRefs.refsOf_mentions ci he hr) hmE
  obtain ⟨d, hd, hda⟩ := Option.map_eq_some_iff.mp (fb.resolved m a hsub hn)
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hd
  obtain ⟨k, hk, hmem⟩ := hd
  have keyOf : ∀ {β : Type} {mp : Std.HashMap Ix.Name β} {a : Ix.Name} {b : β}, (a, b) ∈ mp.toList →
      a ∈ mp.keys := fun h => by
    rw [← Std.HashMap.map_fst_toList_eq_keys]
    exact List.mem_map_of_mem (f := Prod.fst) h
  have e : k = m := nameHashes_distinct P.compiled k (List.mem_append_right _ (keyOf hmem)) m
    (List.mem_append_left _ (keyOf hcm)) (Ix.Cert.name_beq_iff.mp hk).symm
  subst e
  exact ⟨d, hmem, hda, hsub⟩

/-- **`MentionsPublished` at a fold block**, for names closure constants' terms mention. -/
theorem _root_.Ix.Cert.GroupRuns.FoldBlock.mentionsPublished {env : Ix.Environment} {roots : List Ix.Name}
    {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) (fb : FoldBlock env sub ixe failures snap rep all r c)
    {mentions : Ix.Name → Prop} (covered : ∀ m, mentions m → MentionedIn env sub m) :
    TraceSegments.MentionsPublished ixe sub snap.cenv mentions :=
  fun m _ hm hb => fb.mention_published P (covered m hm) hb


/-! ### Each kind's mentions are a closure constant's -/

section Kinds

variable {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env}
  {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
  {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint} {i : Nat}

open Ix.LeanIngress (Group)
open Ix.Cert.ClosureLayout (quotientGraph)
open Ix.Cert.InductiveCompile (indsOf indOf)

/-- A definitions, axiom or quotient group's constants are stored in the closure (with their kind). -/
theorem component_kinded {gr : Group}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some gr) (hc : GroupBlocks.Component gr) :
    LayoutExtra.NamesKinded sub gr := by
  obtain ⟨_, _, -, hcomp⟩ := GroupBlocks.component_of_groups sub (blocksOf sub) gr (Array.mem_of_getElem? hgr) hc
  exact LayoutExtra.componentGroup_kinded hcomp

/-- A definitions group's members are stored in the closure under their own names. -/
theorem members_stored (P : Premises env roots sub ixe failures t envQ) {members : Array Ix.ConstantInfo}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.definitions members)) :
    ∀ ci ∈ members, (ci.getCnst.name, ci) ∈ sub.consts.toList := by
  intro ci hci
  obtain ⟨k, hk⟩ := (component_kinded hgr trivial).2 members rfl ci hci
  rw [inputsNamed P.compiled k ci (SourceStoredNames.stored_input P hk)]
  exact hk

theorem sourceData_terms {ci : Ix.ConstantInfo} {d : Ix.Def} (h : EmissionDispatch.sourceData ci = some d) :
    d.type ∈ termsOf ci ∧ d.value ∈ termsOf ci := by
  cases ci <;> simp only [EmissionDispatch.sourceData, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp [termsOf, definitionValData, theoremValData, opaqueValData]

/-- **A block of definitions' mentions** (`BlockCompiled.published`'s). -/
theorem definitions_mentioned (P : Premises env roots sub ixe failures t envQ) {members : Array Ix.ConstantInfo}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.definitions members)) {m : Ix.Name}
    (hm : ∃ (j : Nat) (_ : j < (TraceSegments.defsOf members).length),
      GraphWalk.Refs m (TraceSegments.defsOf members)[j].type ∨
        GraphWalk.Refs m (TraceSegments.defsOf members)[j].value) :
    MentionedIn env sub m := by
  obtain ⟨j, hj, hr⟩ := hm
  have hmem : (TraceSegments.defsOf members)[j] ∈ members.toList.filterMap EmissionDispatch.sourceData :=
    List.getElem_mem hj
  obtain ⟨ci, hci, hd⟩ := List.mem_filterMap.mp hmem
  have hst := members_stored P hgr ci (Array.mem_toList_iff.mp hci)
  obtain ⟨ht, hv⟩ := sourceData_terms hd
  rcases hr with hr | hr
  · exact mentionedIn_of_stored P.source.1 hst ht hr
  · exact mentionedIn_of_stored P.source.1 hst hv hr

/-- **A singleton definition's mentions** (`DefinitionNeeds`' `defMentions`). -/
theorem definition_mentioned (P : Premises env roots sub ixe failures t envQ) {members : Array Ix.ConstantInfo}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.definitions members)) {ci : Ix.ConstantInfo}
    (hci : ci ∈ members) {m : Ix.Name} (hm : TraceSegments.defMentions ci m) : MentionedIn env sub m := by
  obtain ⟨source, hs, hr⟩ := hm
  have hst := members_stored P hgr ci hci
  obtain ⟨ht, hv⟩ := sourceData_terms hs
  rcases hr with hr | hr
  · exact mentionedIn_of_stored P.source.1 hst ht hr
  · exact mentionedIn_of_stored P.source.1 hst hv hr

/-- **An axiom's mentions** (`HeaderNeeds`'). -/
theorem axiom_mentioned (P : Premises env roots sub ixe failures t envQ) {v : Ix.AxiomVal}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.axiom v)) {m : Ix.Name}
    (hm : GraphWalk.Refs m (Ix.ConstantInfo.axiomInfo v).getCnst.type) : MentionedIn env sub m := by
  obtain ⟨k, ci, hk, -, hkind⟩ := (component_kinded hgr trivial).1 v.cnst.name (by simp [Group.names])
  have e : ci = .axiomInfo v := hkind
  subst e
  exact mentionedIn_of_stored P.source.1 hk (by simp [termsOf]) hm

/-- **A quotient constant's mentions** (`HeaderNeeds`'). -/
theorem quot_mentioned (P : Premises env roots sub ixe failures t envQ) {v : Ix.QuotVal}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.quot v)) {m : Ix.Name}
    (hm : GraphWalk.Refs m (Ix.ConstantInfo.quotInfo v).getCnst.type) : MentionedIn env sub m := by
  obtain ⟨k, ci, hk, -, hkind⟩ := (component_kinded hgr trivial).1 v.cnst.name (by simp [Group.names])
  have e : ci = .quotInfo v := hkind
  subst e
  exact mentionedIn_of_stored P.source.1 hk (by simp [termsOf]) hm

/-- A constructor list looked up is the lookups of names of the list. -/
theorem mapM_ctorOf_mem {E : Ix.Name → Option Ix.ConstantInfo} :
    ∀ {xs : List Ix.Name} {cs : List Ix.ConstructorVal}, xs.mapM (GroupRuns.ctorOf E) = some cs →
      ∀ cv ∈ cs, ∃ x ∈ xs, E x = some (.ctorInfo cv)
  | [], cs, h, cv, hcv => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    cases hcv
  | x :: xs, cs, h, cv, hcv => by
    cases hx : GroupRuns.ctorOf E x with
    | none => simp [List.mapM_cons, hx] at h
    | some b =>
      cases hxs : xs.mapM (GroupRuns.ctorOf E) with
      | none => simp [List.mapM_cons, hx, hxs] at h
      | some bs =>
        simp only [List.mapM_cons, hx, hxs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hcv with rfl | hcv
        · refine ⟨x, List.mem_cons_self, ?_⟩
          unfold GroupRuns.ctorOf at hx
          split at hx
          · rename_i cv' hcv'
            cases hx
            exact hcv'
          · cases hx
        · obtain ⟨y, hy, e⟩ := mapM_ctorOf_mem hxs cv hcv
          exact ⟨y, List.mem_cons_of_mem _ hy, e⟩

/-- **An inductive group's types' mentions** (`InductiveCompiled.published₁`'s): a type's, or a
constructor's, which the closure holds as a constructor its type lists. -/
theorem types_mentioned (P : Premises env roots sub ixe failures t envQ) {types : Array Ix.InductiveVal}
    {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.inductive types ctors recs)) {m : Ix.Name}
    (hm : ∃ i ∈ indsOf types ctors, ∃ e ∈ BlockEmission.memberSources (.indc i), GraphWalk.Refs m e) :
    MentionedIn env sub m := by
  have hcl : IsClosure env roots sub := P.source.1
  obtain ⟨-, -, -, -, -, hcsize, -, -, typeGet, -, ctorsOf⟩ := GroupRuns.inductive_facts P hgr
  obtain ⟨ind, hi, e, he, hr⟩ := hm
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hi
  have hjT : j < types.size := by simp [indsOf, hcsize] at hj; exact hj
  have hjC : j < ctors.size := by omega
  rw [InductiveCompile.indsOf_getElem hcsize hj] at he
  simp only [BlockEmission.memberSources, indOf, List.mem_cons, List.mem_map, Array.mem_toList_iff] at he
  obtain ⟨hget, hst⟩ := typeGet j hjT
  rcases he with rfl | ⟨cv, hcv, rfl⟩
  · exact mentionedIn_of_stored hcl hst (by simp [termsOf, Ix.ConstantInfo.getCnst]) hr
  · obtain ⟨c, hc, hcE⟩ := mapM_ctorOf_mem (ctorsOf j hjT hjC) cv (Array.mem_toList_iff.mpr hcv)
    have hsx : (sub.consts.get? types[j].cnst.name).isSome = true := by
      rw [SourceStoredNames.stored_get hst]; rfl
    have named : (cv.cnst.name == c) = true := FamilyGroups.named_of_get P.compiled hcE
    have hcE' : env.consts.get? cv.cnst.name = some (.ctorInfo cv) := by
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr named, ← Std.HashMap.get?_eq_getElem?]
      exact hcE
    have href : (refsOf (.inductInfo types[j])).contains cv.cnst.name = true := by
      rw [Std.HashSet.contains_congr named]
      exact FreshSnapshot.refsOf_induct _ (Array.mem_toList_iff.mp hc)
    have hsub := CompiledRefs.sub_of_ref hcl hsx hget href (by rw [hcE']; rfl)
    exact ⟨cv.cnst.name, .ctorInfo cv, cv.cnst.type, hsub, hcE', by simp [termsOf, Ix.ConstantInfo.getCnst], hr⟩

/-- **An inductive group's recursors' mentions** (`InductiveCompiled.published₂`'s). -/
theorem recursors_mentioned (P : Premises env roots sub ixe failures t envQ) {types : Array Ix.InductiveVal}
    {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.inductive types ctors recs)) {m : Ix.Name}
    (hm : ∃ r ∈ recs.toList, ∃ e ∈ BlockEmission.memberSources (.recr r), GraphWalk.Refs m e) :
    MentionedIn env sub m := by
  obtain ⟨_, _, _, _, hrecs, -⟩ := GroupRuns.inductive_facts P hgr
  obtain ⟨rv, hrv, e, he, hr⟩ := hm
  obtain ⟨k, hk, -⟩ := FamilyGroups.recsTable_mem
    (SourceStoredNames.blockRecursors_mem hrecs rv (Array.mem_toList_iff.mp hrv))
  exact mentionedIn_of_stored P.source.1 hk (by simpa [termsOf, BlockEmission.memberSources] using he) hr

end Kinds


/-! ## A block of definitions names its members exactly -/

section ExactNames

open Ix.Cert.DefinitionDeps (ConstOcc)
open Ix.Cert.ClosureLayout (addrOf quotientGraph)

/-- A constant a term applies is one it mentions. -/
theorem occ_refs {n : Ix.Name} : ∀ {e : Ix.Expr}, ConstOcc n e → GraphWalk.Refs n e
  | _, .const => .const BEq.rfl
  | _, .appF h => .appF (occ_refs h)
  | _, .appA h => .appA (occ_refs h)
  | _, .lamT h => .lamT (occ_refs h)
  | _, .lamB h => .lamB (occ_refs h)
  | _, .allT h => .allT (occ_refs h)
  | _, .allB h => .allB (occ_refs h)
  | _, .letT h => .letT (occ_refs h)
  | _, .letV h => .letV (occ_refs h)
  | _, .letB h => .letB (occ_refs h)
  | _, .proj h => .projStruct (occ_refs h)
  | _, .mdata h => .mdata (occ_refs h)

/-- **`BlockRefs.exactNames_of`, for the names the block's sources mention**: its `published`
and `sameKey` premises asked only at a mentioned name the block binds, and at its members. -/
theorem exactNames_bound (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    {bindings : Bindings} {before after : BlockState} {output : BlockResult}
    (clean : Emission.Clean bindings before) {defs : List Ix.Def} (two : 2 ≤ defs.length)
    (distinct : Canon.KeysDistinct (defs.map MutConst.defn))
    (ran : rawRun (compileMutualBlock ((defs.map MutConst.defn).map ([·]))) context before =
      (.ok output, after))
    (unresolved : ∀ d ∈ defs, bindings.get? d.name = none ∧ context.1.nameToAddr.get? d.name = none)
    {ixe : Ixon.Env} (acyclic : referenceCycle ixe = none) {B : Address}
    (stored : recordAt ixe B = some output.block)
    (owned : ∀ j (hj : j < defs.length), ∃ P c, addrOf ixe defs[j].name = some P ∧
      recordAt ixe P = some c ∧ ownerOf P c = B)
    (apart : ∀ j (hj : j < defs.length) k (hk : k < defs.length),
      addrOf ixe defs[j].name = addrOf ixe defs[k].name → j = k)
    (memberKey : ∀ k (hk : k < defs.length) j (hj : j < defs.length),
      Ix.LeanIngress.ingressKey defs[k].name = Ix.LeanIngress.ingressKey defs[j].name →
        addrOf ixe defs[k].name = addrOf ixe defs[j].name)
    (bound : ∀ i (hi : i < defs.length) n a, (ConstOcc n defs[i].type ∨ ConstOcc n defs[i].value) →
      lookupBinding context.1 bindings n = some a → addrOf ixe n = some a ∧
        ∀ j (hj : j < defs.length), Ix.LeanIngress.ingressKey n = Ix.LeanIngress.ingressKey defs[j].name →
          addrOf ixe n = addrOf ixe defs[j].name) :
    ∀ i (hi : i < defs.length) j (hj : j < defs.length) n,
      (ConstOcc n defs[i].type ∨ ConstOcc n defs[i].value) →
        Ix.LeanIngress.ingressKey n = Ix.LeanIngress.ingressKey defs[j].name → n = defs[j].name := by
  intro i hi j hj n hn hkey
  cases hc : (MutConst.ctx ((defs.map MutConst.defn).map ([·])))[n]? with
  | some k =>
    -- another member: members are published apart
    obtain ⟨hk, hname⟩ := DefinitionBlockReads.ctx_defs_val distinct hc
    rw [← hname] at hkey
    obtain rfl := apart k hk j hj (memberKey k hk j hj hkey)
    exact hname.symm
  | none =>
    -- a non-member: the block would reference member `j`'s record
    exfalso
    obtain ⟨a, hb, hmem⟩ := BlockRefs.mentioned_binding_ref context free clean two distinct ran unresolved hi hn hc
    obtain ⟨hpub, sameKey⟩ := bound i hi n a hn hb
    have same := sameKey j hj hkey
    obtain ⟨P, c, hP, hrec, hown⟩ := owned j hj
    have ha : a = P := by
      rw [hpub, hP] at same
      exact Option.some.inj same
    subst ha
    exact BlockRefs.no_self_reference acyclic stored hmem hrec hown

variable {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env}
  {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
  {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}

/-- **A mentioned name the snapshot binds is a closure constant's own name.** -/
theorem _root_.Ix.Cert.GroupRuns.FoldBlock.mention_stored (P : Premises env roots sub ixe failures t envQ)
    (fb : FoldBlock env sub ixe failures snap rep all r c) {m : Ix.Name} (hm : MentionedIn env sub m)
    {a : Address} (hb : lookupBinding snap.cenv {} m = some a) : ∃ ci, (m, ci) ∈ sub.consts.toList := by
  obtain ⟨cm, hcm⟩ := fb.bound_exact P.compiled (lookup_empty hb)
  obtain ⟨_, _, _, hsub⟩ := fb.mention_published P hm hb
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hsub
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hci
  obtain ⟨k, hk, hmem⟩ := hci
  have keyOf : ∀ {β : Type} {mp : Std.HashMap Ix.Name β} {a : Ix.Name} {b : β}, (a, b) ∈ mp.toList →
      a ∈ mp.keys := fun h => by
    rw [← Std.HashMap.map_fst_toList_eq_keys]
    exact List.mem_map_of_mem (f := Prod.fst) h
  have e : k = m := nameHashes_distinct P.compiled k
    (List.mem_append_left _ (keyOf (SourceStoredNames.stored_input P hmem))) m
    (List.mem_append_left _ (keyOf hcm)) (Ix.Cert.name_beq_iff.mp hk).symm
  subst e
  exact ⟨ci, hmem⟩

/-- A definitions group's sources are all its members'. -/
theorem defsOf_length {ig : Nat} {members : Array Ix.ConstantInfo}
    (hgr : (quotientGraph ixe t hints sub).groups[ig]? = some (.definitions members)) :
    (TraceSegments.defsOf members).length = members.size := by
  obtain ⟨_, _, -, hcomp⟩ := GroupBlocks.component_of_groups sub (blocksOf sub) _ (Array.mem_of_getElem? hgr) trivial
  obtain ⟨-, defsM⟩ := GroupRuns.componentGroup_sorted hcomp
  unfold TraceSegments.defsOf
  rw [GroupRuns.length_filterMap_of_isSome fun ci hci =>
    GroupRuns.sourceData_isSome (defsM ci (Array.mem_toList_iff.mp hci)), Array.length_toList]

/-- A definitions group's sources are closure constants' under their own names. -/
theorem defs_stored (P : Premises env roots sub ixe failures t envQ) {ig : Nat} {members : Array Ix.ConstantInfo}
    (hgr : (quotientGraph ixe t hints sub).groups[ig]? = some (.definitions members)) :
    ∀ j (hj : j < (TraceSegments.defsOf members).length),
      ∃ ci, ((TraceSegments.defsOf members)[j].name, ci) ∈ sub.consts.toList := by
  intro j hj
  have hmem : (TraceSegments.defsOf members)[j] ∈ members.toList.filterMap EmissionDispatch.sourceData :=
    List.getElem_mem hj
  obtain ⟨ci, hci, hd⟩ := List.mem_filterMap.mp hmem
  refine ⟨ci, ?_⟩
  rw [GroupRuns.sourceData_name hd]
  exact members_stored P hgr ci (Array.mem_toList_iff.mp hci)

/-- **`BlockNeeds.distinct`**: a definitions group's members have distinct names. -/
theorem definitions_distinct (P : Premises env roots sub ixe failures t envQ) {ig : Nat}
    {members : Array Ix.ConstantInfo}
    (hgr : (quotientGraph ixe t hints sub).groups[ig]? = some (.definitions members)) :
    Canon.KeysDistinct ((TraceSegments.defsOf members).map MutConst.defn) := by
  have hcl : IsClosure env roots sub := P.source.1
  obtain ⟨_, _, -, hcomp⟩ := GroupBlocks.component_of_groups sub (blocksOf sub) _ (Array.mem_of_getElem? hgr) trivial
  have distinctM := DefinitionPremises.componentGroup_distinct
    (fun k ci h => FamilyGroups.named_of_get P.compiled (hcl.mem_env h)) hcomp
  unfold Canon.KeysDistinct
  have flat : ((TraceSegments.defsOf members).map MutConst.defn).flatMap Canon.keysOf =
      (TraceSegments.defsOf members).map Ix.Def.name := by
    generalize TraceSegments.defsOf members = l
    induction l with
    | nil => rfl
    | cons d l ih => simp only [List.map_cons, List.flatMap_cons, ih]; rfl
  rw [flat]
  unfold TraceSegments.defsOf
  rw [List.map_filterMap]
  have pw : (members.toList.map (·.getCnst.name)).Pairwise (· ≠ ·) :=
    distinctM.imp fun {a b} h e => by
      subst e
      rw [RefTables.name_beq_self] at h
      cases h
  rw [List.pairwise_map] at pw
  refine pw.filterMap _ fun a a' h d hd d' hd' e => ?_
  simp only [Option.map_eq_some_iff] at hd hd'
  obtain ⟨x, hx, rfl⟩ := hd
  obtain ⟨x', hx', rfl⟩ := hd'
  rw [GroupRuns.sourceData_name hx, GroupRuns.sourceData_name hx'] at e
  exact h e

/-- **`BlockNeeds.exactNames`**: a name a definition of a block of two or more mentions with a
member's key is that member. The block's compile does not reference its own records
(`BlockRefs.no_self_reference`), its members are published apart (`BlockPublication.apart`), and
a mentioned name the block binds is a closure constant published at its binding
(`FoldBlock.mention_published`), with one ingress key giving one address (`GroupRuns.addr_of_key`;
no Source totality is needed). -/
theorem definitions_exactNames (P : Premises env roots sub ixe failures t envQ)
    (scheduled : ∀ x ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList,
      ∃ conv, x.1.2 = .ok conv)
    {ig : Nat} {members : Array Ix.ConstantInfo}
    (hgr : (quotientGraph ixe t hints sub).groups[ig]? = some (.definitions members)) (two : 2 ≤ members.size) :
    ∀ i (hi : i < (TraceSegments.defsOf members).length) j (hj : j < (TraceSegments.defsOf members).length) n,
      (ConstOcc n (TraceSegments.defsOf members)[i].type ∨ ConstOcc n (TraceSegments.defsOf members)[i].value) →
        Ix.LeanIngress.ingressKey n = Ix.LeanIngress.ingressKey (TraceSegments.defsOf members)[j].name →
          n = (TraceSegments.defsOf members)[j].name := by
  obtain ⟨snap, rep, all, r, c, fb, mem, out, after, ran, -, hrec⟩ := GroupRuns.definitions_run P scheduled hgr two
  have two' : 2 ≤ (TraceSegments.defsOf members).length := by rw [defsOf_length hgr]; exact two
  have dstored := defs_stored P hgr
  have insub : ∀ j (hj : j < (TraceSegments.defsOf members).length),
      (sub.consts.get? (TraceSegments.defsOf members)[j].name).isSome = true := fun j hj => by
    obtain ⟨ci, hci⟩ := dstored j hj
    rw [SourceStoredNames.stored_get hci]
    rfl
  have hblock : r.block = out.block := (Prod.mk.inj hrec).1
  refine exactNames_bound (snap.cenv, { all, current := blockKey rep all, mutCtx := default, univCtx := [] }) rfl
    BlockStart.clean_empty two' (definitions_distinct P hgr) ran
    (fun d hd => ⟨Std.HashMap.get?_eq_getElem?.trans Std.HashMap.getElem?_empty, fb.fresh d.name (mem d hd)⟩)
    (compileReport_checks P.compiled).2.2.1 (hblock ▸ BlockPublication.stored fb.ran fb.published)
    (BlockPublication.owned fb.ran fb.published two' ran hrec insub)
    (BlockPublication.apart fb.ran fb.published two' ran hrec insub)
    (fun k hk j hj key => GroupRuns.addr_of_key P (dstored k hk).choose_spec (dstored j hj).choose_spec key)
    (fun i hi n a hn hb => ?_)
  have hm : MentionedIn env sub n :=
    definitions_mentioned P hgr ⟨i, hi, hn.imp occ_refs occ_refs⟩
  obtain ⟨d, hmem, hda, -⟩ := fb.mention_published P hm hb
  obtain ⟨cn, hcn⟩ := fb.mention_stored P hm hb
  refine ⟨?_, fun j hj key => GroupRuns.addr_of_key P hcn (dstored j hj).choose_spec key⟩
  unfold addrOf
  rw [Std.HashMap.get?_eq_getElem?, (Std.HashMap.mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some.mp hmem).2,
    Option.map_some, hda]


/-- **A name a definition of a block of two or more applies is an input constant's key**: a
member, or a name the block's compile binds (`BlockRefs.mentioned_binding_ref`), which is a key
the input stores a constant under (`FoldBlock.bound_exact`). -/
theorem definitions_occ_input (P : Premises env roots sub ixe failures t envQ)
    (scheduled : ∀ x ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList,
      ∃ conv, x.1.2 = .ok conv)
    {ig : Nat} {members : Array Ix.ConstantInfo}
    (hgr : (quotientGraph ixe t hints sub).groups[ig]? = some (.definitions members)) (two : 2 ≤ members.size) :
    ∀ i (hi : i < (TraceSegments.defsOf members).length) n,
      (ConstOcc n (TraceSegments.defsOf members)[i].type ∨ ConstOcc n (TraceSegments.defsOf members)[i].value) →
        ∃ ci, (n, ci) ∈ env.consts.toList := by
  intro i hi n hn
  obtain ⟨snap, rep, all, r, c, fb, mem, out, after, ran, -, -⟩ := GroupRuns.definitions_run P scheduled hgr two
  have two' : 2 ≤ (TraceSegments.defsOf members).length := by rw [defsOf_length hgr]; exact two
  have distinct := definitions_distinct P hgr
  cases hc : (MutConst.ctx (((TraceSegments.defsOf members).map MutConst.defn).map ([·])))[n]? with
  | some k =>
    obtain ⟨hk, hname⟩ := DefinitionBlockReads.ctx_defs_val distinct hc
    obtain ⟨ci, hci⟩ := defs_stored P hgr k hk
    rw [← hname]
    exact ⟨ci, SourceStoredNames.stored_input P hci⟩
  | none =>
    obtain ⟨a, hb, -⟩ := BlockRefs.mentioned_binding_ref
      (snap.cenv, { all, current := blockKey rep all, mutCtx := default, univCtx := [] }) rfl BlockStart.clean_empty
      two' distinct ran
      (fun d hd => ⟨Std.HashMap.get?_eq_getElem?.trans Std.HashMap.getElem?_empty, fb.fresh d.name (mem d hd)⟩)
      hi hn hc
    exact fb.bound_exact P.compiled (lookup_empty hb)

end ExactNames


/-! ## Singletons: a lone constant's compile -/

section Lone

open Ix.LeanIngress (Group)
open Ix.Cert.ClosureLayout (addrOf quotientGraph)

variable {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env}
  {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
  {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}

/-- A nonempty set whose members are all `==` one name has one member. -/
theorem size_one {all : Ix.Set Ix.Name} {n : Ix.Name} (ne : all.isEmpty = false)
    (single : ∀ x, all.contains x = true → (x == n) = true) : all.size = 1 := by
  have hd := Std.HashSet.distinct_toList (m := all)
  rw [← Std.HashSet.length_toList]
  rcases h : all.toList with _ | ⟨x, _ | ⟨y, rest⟩⟩
  · have hz : all.size = 0 := by rw [← Std.HashSet.length_toList, h]; rfl
    rw [Std.HashSet.isEmpty_eq_size_eq_zero, hz] at ne
    cases ne
  · rfl
  · have hx := single x (GroupRuns.contains_of_listed (by rw [h]; exact List.mem_cons_self))
    have hy := single y (GroupRuns.contains_of_listed (by rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    rw [h] at hd
    have hxy := (List.pairwise_cons.mp hd).1 y List.mem_cons_self
    rw [BEq.trans hx (BEq.symm hy)] at hxy
    cases hxy

/-- **A singleton group's constant compiles alone, at its fold block** (`LoneCompiled.ran`,
`.stored`, `.addr`, `.blobs`): its block is its name alone (`GroupBlocks.single_block`), so the
block takes the lone path (`GroupRuns.runBlock_paths`), at `runBlock`'s final state, and its one
claim is the block record, published under the constant's name. -/
theorem singleton_compiled (P : Premises env roots sub ixe failures t envQ)
    (scheduled : ∀ x ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList,
      ∃ conv, x.1.2 = .ok conv)
    {ig : Nat} {gr : Group} (hgr : (quotientGraph ixe t hints sub).groups[ig]? = some gr)
    (hc : GroupBlocks.Component gr) {ci : Ix.ConstantInfo} (hsingle : gr.names = #[ci.getCnst.name])
    (hst : (ci.getCnst.name, ci) ∈ sub.consts.toList) (hi : ∀ v, ci ≠ .inductInfo v) (hct : ∀ v, ci ≠ .ctorInfo v) :
    ∃ snap rep all r c, FoldBlock env sub ixe failures snap rep all r c ∧
      rawRun (compileConstantInfo ci)
          (snap.cenv, { all, current := blockKey rep all, mutCtx := default, univCtx := [] }) {} = (.ok r, c) ∧
      recordAt ixe r.blockAddr = some r.block ∧ addrOf ixe ci.getCnst.name = some r.blockAddr ∧
      TraceSegments.BlobsKept ixe snap.cenv c := by
  obtain ⟨snap, rep, all, r, c, fb, ⟨a, b, hclaim⟩, hmem⟩ := GroupRuns.foldBlock_of P hst
  have hin := hmem fun cv e => hct cv e
  have single := GroupBlocks.single_block P scheduled hgr hc hsingle fb.block hin
  have hne := Condense.condense_nonempty fb.block
  have hsize := size_one hne single
  have hkey := single _ (blockKey_mem (lo := rep) hne)
  obtain ⟨const, hconst, paths⟩ := GroupRuns.runBlock_paths fb.ran
  have hci : env.consts.get? ci.getCnst.name = some ci :=
    SourceStoredNames.stored_get (SourceStoredNames.stored_input P hst)
  rw [fb.env, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr hkey, ← Std.HashMap.get?_eq_getElem?,
    hci] at hconst
  obtain rfl : const = ci := (Option.some.inj hconst).symm
  have hnot : GroupRuns.isIndConst const = false := by
    cases hci' : const with
    | inductInfo v => exact absurd hci' (hi v)
    | ctorInfo v => exact absurd hci' (hct v)
    | _ => rfl
  rcases paths with ⟨-, hs⟩ | ⟨hcond, -⟩
  · obtain ⟨hproj, -⟩ := ClosureResolve.constantInfo_lone const (fun v e => hi v e) (fun v e => hct v e) _ _ _ _ hs
    have hempty : r.projections.isEmpty = true := by rw [hproj]; rfl
    have hsub : (sub.consts.get? const.getCnst.name).isSome = true := by
      rw [SourceStoredNames.stored_get hst]; rfl
    obtain ⟨haddr, -⟩ := fb.published.claims _ _ _ hclaim hsub
    have hone : claimWrites (blockKey rep all) r = #[(blockKey rep all, r.blockAddr, r.blockBytes)] := by
      simp [claimWrites, hempty]
    rw [hone] at hclaim
    simp only [List.mem_toArray, List.mem_singleton, Prod.mk.injEq] at hclaim
    obtain ⟨-, rfl, -⟩ := hclaim
    exact ⟨snap, rep, all, r, c, fb, hs, BlockPublication.stored fb.ran fb.published, haddr, fb.blobs⟩
  · rw [hsize, hnot] at hcond
    cases hcond

/-- **`LoneCompiled` for a singleton group's constant**: `singleton_compiled`, with the snapshot's
bindings resolving (`FoldBlock.bound`) and its mentions published (`FoldBlock.mentionsPublished`). -/
theorem lone_compiled (P : Premises env roots sub ixe failures t envQ)
    (scheduled : ∀ x ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList,
      ∃ conv, x.1.2 = .ok conv)
    (idx : BindingsResolve.ConstructorIndices env)
    {ig : Nat} {gr : Group} (hgr : (quotientGraph ixe t hints sub).groups[ig]? = some gr)
    (hc : GroupBlocks.Component gr) {ci : Ix.ConstantInfo} (hsingle : gr.names = #[ci.getCnst.name])
    (hst : (ci.getCnst.name, ci) ∈ sub.consts.toList) (hi : ∀ v, ci ≠ .inductInfo v) (hct : ∀ v, ci ≠ .ctorInfo v)
    {mentions : Ix.Name → Prop} (covered : ∀ m, mentions m → MentionedIn env sub m) :
    ∃ cenv benv output after, TraceSegments.LoneCompiled ixe sub ci mentions cenv benv output after := by
  obtain ⟨snap, rep, all, r, c, fb, ran, stored, addr, blobs⟩ :=
    singleton_compiled P scheduled hgr hc hsingle hst hi hct
  exact ⟨snap.cenv, _, r, c, ran, stored, addr, fb.bound idx, blobs, fb.mentionsPublished P covered⟩

/-- A singleton definition group's constant: stored under its name, and no inductive or
constructor. -/
theorem definition_single {ig : Nat} {ci : Ix.ConstantInfo}
    (hgr : (quotientGraph ixe t hints sub).groups[ig]? = some (.definitions #[ci]))
    (P : Premises env roots sub ixe failures t envQ) :
    (Group.definitions #[ci]).names = #[ci.getCnst.name] ∧ (ci.getCnst.name, ci) ∈ sub.consts.toList ∧
      (∀ v, ci ≠ .inductInfo v) ∧ ∀ v, ci ≠ .ctorInfo v := by
  obtain ⟨_, _, -, hcomp⟩ := GroupBlocks.component_of_groups sub (blocksOf sub) _ (Array.mem_of_getElem? hgr) trivial
  obtain ⟨-, defsM⟩ := GroupRuns.componentGroup_sorted hcomp
  have hd := defsM ci (by simp)
  refine ⟨by simp [Group.names], members_stored P hgr ci (by simp), fun v e => ?_, fun v e => ?_⟩ <;>
    (subst e; simp [Ix.LeanIngress.isDefinition] at hd)

/-- An axiom group's constant, stored under its name. -/
theorem axiom_single {ig : Nat} {v : Ix.AxiomVal}
    (hgr : (quotientGraph ixe t hints sub).groups[ig]? = some (.axiom v))
    (P : Premises env roots sub ixe failures t envQ) :
    (Group.axiom v).names = #[(Ix.ConstantInfo.axiomInfo v).getCnst.name] ∧
      ((Ix.ConstantInfo.axiomInfo v).getCnst.name, .axiomInfo v) ∈ sub.consts.toList := by
  obtain ⟨k, ci, hk, hname, hkind⟩ := (component_kinded hgr trivial).1 v.cnst.name (by simp [Group.names])
  have e : ci = .axiomInfo v := hkind
  subst e
  refine ⟨by simp [Group.names, Ix.ConstantInfo.getCnst], ?_⟩
  rw [← inputsNamed P.compiled k _ (SourceStoredNames.stored_input P hk)] at hk
  exact hk

/-- A quotient group's constant, stored under its name. -/
theorem quot_single {ig : Nat} {v : Ix.QuotVal}
    (hgr : (quotientGraph ixe t hints sub).groups[ig]? = some (.quot v))
    (P : Premises env roots sub ixe failures t envQ) :
    (Group.quot v).names = #[(Ix.ConstantInfo.quotInfo v).getCnst.name] ∧
      ((Ix.ConstantInfo.quotInfo v).getCnst.name, .quotInfo v) ∈ sub.consts.toList := by
  obtain ⟨k, ci, hk, hname, hkind⟩ := (component_kinded hgr trivial).1 v.cnst.name (by simp [Group.names])
  have e : ci = .quotInfo v := hkind
  subst e
  refine ⟨by simp [Group.names, Ix.ConstantInfo.getCnst], ?_⟩
  rw [← inputsNamed P.compiled k _ (SourceStoredNames.stored_input P hk)] at hk
  exact hk

end Lone

end Ix.Cert.TraceFold

/-- info: 'Ix.Cert.TraceFold.cacheRefs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ix.Cert.TraceFold.cacheRefs

/-- info: 'Ix.Cert.GroupRuns.FoldBlock.mention_published' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ix.Cert.GroupRuns.FoldBlock.mention_published

/-- info: 'Ix.Cert.TraceFold.definitions_exactNames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ix.Cert.TraceFold.definitions_exactNames

/-- info: 'Ix.Cert.TraceFold.lone_compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ix.Cert.TraceFold.lone_compiled

/-- info: 'Ix.Cert.TraceFold.definitions_occ_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ix.Cert.TraceFold.definitions_occ_input

/-- info: 'Ix.Cert.TraceFold.types_mentioned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ix.Cert.TraceFold.types_mentioned
