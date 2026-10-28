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
  or a blob of `runBlock`'s final state (`CompiledRefs.CacheRefs`). -/

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

/-! ## C4: names the sources mention, published -/

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

end Ix.Cert.TraceFold

/-- info: 'Ix.Cert.TraceFold.cacheRefs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ix.Cert.TraceFold.cacheRefs
