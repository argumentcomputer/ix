import Ix.Cert.TraceFold

/-! # The closure's record layout

`ClosureLayout.Layout` says how the compile lays out the records of quotient Source's groups.
This module proves it for every accepted compiled closure whose schedule lets every group
through (`layouts_hold`):

* `block`: a group name's published record is a claim of its block's compile
  (`LayoutExtra.claimedIn_of`), whose block record is stored and is its own block
  (`BlockLayout.layoutBlock_of_claimed`);
* `extra`: the compile's role-record, recursor and literal-roles checks
  (`LayoutExtra.layout_extra_of`);
* `refs`: `CompiledRefs.compiledRefs_of`, read against quotient Source's graph by
  `LayoutRefs.layoutRefs_of_compiled`. Its premises are the fold's facts about each group name's
  block (`refsAt_of`).

The one new fact is that every member of a compiled block is published at a record the block owns
(`FoldBlock.owned`). The member has a claim in a block the fold compiled
(`GroupRuns.foldBlock_of`). That block holds the member (`claim_in_block`), so it is the block at
hand (`block_unique`). Two runs of one block claim the same names (`claim_transfer`), so the
member has a claim of this run, and the block owns that claim's record (`claim_owned`). -/

namespace Ix.Cert.LayoutsHold

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState Ix.Cert.Resolution
open Ix.Cert.GroupRuns (FoldBlock)
open Ix.Cert.ClosureLayout (addrOf quotientGraph)
open Ix.LeanIngress (Group scheduleOf)

/-! ## Blocks of a condensation -/

/-- **Two blocks of a condensation that hold one name are one block.** -/
theorem block_unique {refs : Ix.Map Ix.Name (Ix.Set Ix.Name)} {rep rep' x : Ix.Name}
    {all all' : Ix.Set Ix.Name} (hb : (Ix.CondenseM.run refs).blocks.get? rep = some all)
    (hx : all.contains x = true) (hb' : (Ix.CondenseM.run refs).blocks.get? rep' = some all')
    (hx' : all'.contains x = true) : all' = all := by
  obtain ⟨hr, hv, e⟩ := Condense.blocks_eq refs
  rw [e] at hb hb'
  obtain ⟨_, _, hbn, hrepn, hnn⟩ := Condense.blocksOfDisc_mem hb hx
  obtain ⟨vn, hvn, rfl⟩ := Condense.discOf_get hbn
  obtain ⟨_, _, hbm, hrepm, hnm⟩ := Condense.blocksOfDisc_mem hb' hx'
  obtain ⟨vm, hvm, rfl⟩ := Condense.discOf_get hbm
  dsimp only at hrepn hnn hrepm hnm
  obtain rfl : vm = vn := Condense.namesOf_inj hvm hvn (BEq.trans hnm (BEq.symm hnn))
  have hrr : (rep' == rep) = true := BEq.trans (BEq.symm hrepm) hrepn
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr hrr, ← Std.HashMap.get?_eq_getElem?, hb] at hb'
  exact (Option.some.inj hb').symm

/-- A nonempty block's key does not depend on the representative it defaults to. -/
theorem blockKey_congr {lo lo' : Ix.Name} {all : Ix.Set Ix.Name} (ne : all.isEmpty = false) :
    blockKey lo all = blockKey lo' all := by
  have hpos : 0 < all.toArray.size := by
    rw [Std.HashSet.size_toArray]
    rw [Std.HashSet.isEmpty_eq_size_eq_zero] at ne
    simpa [Nat.pos_iff_ne_zero] using ne
  unfold blockKey canonicalKey
  rw [Array.getElem?_eq_getElem hpos]
  rfl

/-- Names that hash alike read one constant. -/
theorem get_congr {env : Ix.Environment} {a b : Ix.Name} (h : (a == b) = true) :
    env.consts.get? a = env.consts.get? b := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr h]

/-- **A block's claim names a member of the block**, for a block of the input's condensation in a
compile that returns: the block's key, a name that hashes like a member, or a constructor of an
inductive member, which the compile report's family check puts in the inductive's block
(`familyBlocks`). -/
theorem claim_in_block {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (compiled : compileReport env = .ok (ixe, failures)) {cenv : CompileEnv}
    (henv : ∀ x, cenv.env.get? x = env.consts.get? x) {rep : Ix.Name} {all : Ix.Set Ix.Name}
    (hall : (CompiledRefs.envBlocks env).blocks.get? rep = some all) {r : BlockResult} {c : BlockState}
    (hr : runBlock cenv all (blockKey rep all) = .ok (r, c)) {n : Ix.Name} {a : Address} {b : ByteArray}
    (hclaim : (n, a, b) ∈ claimWrites (blockKey rep all) r) : all.contains n = true := by
  rcases ClosureClaims.claim_name hclaim with rfl | ⟨row, hrow, e⟩
  · exact blockKey_mem (Condense.condense_nonempty hall)
  have named : Claims.NamedEnv cenv.env := fun x ci h =>
    FamilyGroups.named_of_get compiled ((henv x).symm.trans h)
  rcases Claims.runBlock_owned named hr row hrow with ⟨m, hm, em⟩ | ⟨I, iv, cn, hI, hiv, hcn, ecn⟩
  · rw [← e, Std.HashSet.contains_congr em]
    exact hm
  rw [henv] at hiv
  have fam := (familyBlocks compiled rep all hall I hI).1 iv hiv
  rw [← e, Std.HashSet.contains_congr ecn, fam]
  rcases (fam I).mp hI with ⟨n', hn', e'⟩ | ⟨n', hn', iv', hiv', c', hc', e'⟩
  · exact .inr ⟨n', hn', iv, by rw [get_congr e']; exact hiv, cn, hcn, BEq.rfl⟩
  · -- a constructor that hashes like the inductive `I`
    obtain ⟨cv, hcv, -⟩ := ctorsBelong compiled n' iv' hiv' c' hc'
    rw [get_congr e', hiv] at hcv
    cases hcv

/-! ## Two runs of one block claim the same names -/

/-- A source's names as a mutual block's rows carry them: its own, then its constructors'. -/
def srcNames (src : MutConst) : List Ix.Name := src.name :: src.ctors.toList.map (·.cnst.name)

theorem zipIdx_map_fst {α β : Type} (f : α → β) :
    ∀ (l : List α) (k : Nat), (l.zipIdx k).map (fun p => f p.1) = l.map f
  | [], _ => rfl
  | a :: l, k => by simp [List.zipIdx_cons, zipIdx_map_fst f l (k + 1)]

theorem sourceRows_names (owner : Address) (index : UInt64) (src : MutConst) :
    (MutualProjections.sourceRows owner index src).map Prod.fst = srcNames src := by
  unfold MutualProjections.sourceRows srcNames
  rw [List.map_cons, List.map_map]
  congr 1
  rw [← zipIdx_map_fst (·.cnst.name) src.ctors.toList 0]
  apply List.map_congr_left
  rintro ⟨a, b⟩ -
  rfl

theorem rows_names (owner : Address) :
    ∀ (sources : List (List MutConst)) (k : Nat),
      ((sources.zipIdx k).flatMap fun p =>
        p.1.flatMap (MutualProjections.sourceRows owner p.2.toUInt64)).map Prod.fst =
        sources.flatten.flatMap srcNames
  | [], _ => rfl
  | members :: rest, k => by
    simp only [List.zipIdx_cons, List.flatMap_cons, List.map_append, rows_names owner rest (k + 1),
      List.flatten_cons, List.flatMap_append, List.map_flatMap, sourceRows_names]

theorem expectedRows_names (owner : Address) (sources : List (List MutConst)) :
    (MutualProjections.expectedRows owner sources).map Prod.fst = sources.flatten.flatMap srcNames :=
  rows_names owner sources 0

theorem flatten_singletons {α : Type} : ∀ L : List α, (L.map ([·])).flatten = L
  | [] => rfl
  | a :: L => by rw [List.map_cons, List.flatten_cons, flatten_singletons L]; rfl

theorem heads_singletons {α : Type} : ∀ L : List α, (L.map ([·])).filterMap List.head? = L
  | [] => rfl
  | a :: L => by
    show a :: (L.map ([·])).filterMap List.head? = a :: L
    rw [heads_singletons L]

/-- **The names of a mutual compile's rows are its sources'**, for one source per class: the
wrapper's rows (`MutualProjections.build_rows`), or a lone definition's or recursor's, which has
no constructors. -/
theorem mutual_names (L : List MutConst) :
    Emission.Yields (compileMutualBlock (L.map ([·])))
      (fun out => out.projections.toList.map Prod.fst = L.flatMap srcNames) := by
  refine ProjectionLayout.mutual_block _ _ ?_
  unfold compileMutualPayload
  refine Emission.Yields.bind (ProjectionLayout.payload_shapes _) fun compiled shape => ?_
  intro context before output after ran
  obtain ⟨-, -, built⟩ := ProjectionLayout.finish_mutual_ok context _ compiled.1 compiled.2.2 ran
  have logical : output.projections.toList.map Prod.fst =
      (MutualProjections.logicalRows output.projections).map Prod.fst := by
    simp [MutualProjections.logicalRows]
  rw [logical]
  have flat := flatten_singletons L
  obtain ⟨-, wrapped | collapsed⟩ :=
    MutualArtifact.build_cases _ _ compiled.1 compiled.2.2 before output built
  · obtain ⟨targets, metadata, -, -, proj⟩ := wrapped
    rw [proj, MutualProjections.build_rows, expectedRows_names, flat]
  · obtain ⟨-, ⟨kind, hk, kshape⟩, rows⟩ := collapsed
    rw [rows, List.map_map, flat]
    rw [heads_singletons, kshape] at shape
    rcases L with _ | ⟨src, _ | ⟨src', rest⟩⟩
    · simp at shape
    · have none : src.ctors = #[] := by
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at shape
        cases src with
        | defn d => rfl
        | recr v => rfl
        | indc v => rcases hk with rfl | rfl <;> simp [ProjectionLayout.sourceShape] at shape
      simp [srcNames, none]
    · simp at shape

/-- A run's projections' names, read from its records. -/
theorem projections_names {r out : BlockResult} (h : BlockRecords.recordsOf r = BlockRecords.recordsOf out) :
    r.projections.toList.map Prod.fst = out.projections.toList.map Prod.fst := by
  simp only [BlockRecords.recordsOf, Prod.mk.injEq] at h
  have := congrArg (fun a : Array (Ix.Name × Ixon.Constant) => a.toList.map Prod.fst) h.2.2.2
  simpa [List.map_map, Function.comp_def] using this

/-- Lean's order makes one class per member. -/
theorem sourceClasses_singletons (cs : Array MutConst) :
    ∃ L : List MutConst, sourceClasses cs = L.map ([·]) := by
  refine ⟨(sourceClasses cs).map (·.head!), ?_⟩
  rw [List.map_map]
  refine (List.map_id _).symm.trans (List.map_congr_left fun c hc => ?_)
  unfold sourceClasses at hc
  try dsimp only at hc
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 hc
  rfl

/-- **Two runs of one block, in states that read the same constants, project the same names**:
both take the lone path, with no projections, or both run the members' loop, which makes the
same members, whose mutual compile's rows carry their names (`mutual_names`). -/
theorem runBlock_names {cenv cenv' : CompileEnv} {all : Ix.Set Ix.Name} {k : Ix.Name}
    {r r' : BlockResult} {c c' : BlockState}
    (h : runBlock cenv all k = .ok (r, c)) (h' : runBlock cenv' all k = .ok (r', c'))
    (same : ∀ x, cenv.env.get? x = cenv'.env.get? x) :
    r.projections.toList.map Prod.fst = r'.projections.toList.map Prod.fst := by
  obtain ⟨const, hconst, paths⟩ := GroupRuns.runBlock_paths h
  obtain ⟨const', hconst', paths'⟩ := GroupRuns.runBlock_paths h'
  rw [← same, hconst] at hconst'
  obtain rfl := Option.some.inj hconst'
  rcases paths with ⟨hcond, hs⟩ | ⟨hcond, cs, out, s₄, hloop, hout, -, hrec⟩ <;>
    rcases paths' with ⟨hcond', hs'⟩ | ⟨hcond', cs', out', s₄', hloop', hout', -, hrec'⟩
  · have hi : ∀ v, const = .inductInfo v → False := by
      rintro v rfl
      simp [GroupRuns.isIndConst] at hcond
    have hc : ∀ v, const = .ctorInfo v → False := by
      rintro v rfl
      simp [GroupRuns.isIndConst] at hcond
    rw [Claims.constantInfo_lone const hi hc _ _ _ _ hs, Claims.constantInfo_lone const hi hc _ _ _ _ hs']
  · rw [hcond] at hcond'
    cases hcond'
  · rw [hcond] at hcond'
    cases hcond'
  · have e₁ := GroupRuns.membersLoop_eq _ _ hloop
    have e₂ := GroupRuns.membersLoop_eq _ _ hloop'
    have hcs : cs.toList = cs'.toList := by
      rw [e₁, e₂]
      congr 3
      funext x
      exact same x
    obtain rfl : cs = cs' := Array.toList_inj.mp hcs
    rw [projections_names hrec, projections_names hrec']
    obtain ⟨L, hL⟩ := sourceClasses_singletons cs
    rw [hL] at hout hout'
    rw [mutual_names L _ _ _ _ hout, mutual_names L _ _ _ _ hout']

/-- **A name a run of a block claims, another run of the block claims too**, in states that read
the same constants. -/
theorem claim_transfer {cenv cenv' : CompileEnv} {all : Ix.Set Ix.Name} {k : Ix.Name}
    {r r' : BlockResult} {c c' : BlockState}
    (h : runBlock cenv all k = .ok (r, c)) (h' : runBlock cenv' all k = .ok (r', c'))
    (same : ∀ x, cenv.env.get? x = cenv'.env.get? x) {n : Ix.Name} {a' : Address} {b' : ByteArray}
    (hn : (n, a', b') ∈ claimWrites k r') : ∃ a b, (n, a, b) ∈ claimWrites k r := by
  have names := runBlock_names h h' same
  have hsize : r.projections.size = r'.projections.size := by
    simpa using congrArg List.length names
  have hempty : r.projections.isEmpty = r'.projections.isEmpty := by
    simp [Array.isEmpty, hsize]
  unfold claimWrites at hn ⊢
  rw [hempty]
  cases e : r'.projections.isEmpty <;> simp only [e, Bool.false_eq_true, ↓reduceIte] at hn ⊢
  · obtain ⟨⟨pn, pc, pm⟩, hp', ep⟩ := Array.mem_map.mp hn
    simp only [Prod.mk.injEq] at ep
    have hmem : n ∈ r.projections.toList.map Prod.fst := by
      rw [names]
      exact List.mem_map.mpr ⟨(pn, pc, pm), Array.mem_toList_iff.mpr hp', ep.1⟩
    obtain ⟨⟨qn, qc, qm⟩, hq, rfl⟩ := List.mem_map.mp hmem
    exact ⟨_, _, Array.mem_map.mpr ⟨(qn, qc, qm), Array.mem_toList_iff.mp hq, rfl⟩⟩
  · simp only [List.mem_toArray, List.mem_singleton, Prod.mk.injEq] at hn
    obtain ⟨rfl, -, -⟩ := hn
    exact ⟨_, _, List.mem_toArray.mpr (List.mem_singleton.mpr rfl)⟩

/-! ## A claim's record, owned by its block -/

/-- **A claim's stored record is the block's record or one of its projections**, so the block
owns it. -/
theorem claim_owned {cenv : CompileEnv} {all : Ix.Set Ix.Name} {k : Ix.Name} {r : BlockResult}
    {c : BlockState} (hr : runBlock cenv all k = .ok (r, c)) {ixe : Ixon.Env}
    (stored : recordAt ixe r.blockAddr = some r.block) {n : Ix.Name} {P : Address} {b : ByteArray}
    (hclaim : (n, P, b) ∈ claimWrites k r) (hP : ixe.consts.get? P = some { buf := b, len := b.size }) :
    ∃ c', recordAt ixe P = some c' ∧ ownerOf P c' = r.blockAddr := by
  have shape := BlockLayout.runBlock_shape hr
  unfold claimWrites at hclaim
  split at hclaim
  · simp only [List.mem_toArray, List.mem_singleton, Prod.mk.injEq] at hclaim
    obtain ⟨-, rfl, rfl⟩ := hclaim
    exact ⟨r.block, stored, shape.built.owner _⟩
  · obtain ⟨p, hp, e⟩ := Array.mem_map.mp hclaim
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl, rfl⟩ := e
    rcases shape.rows p hp with same | ⟨pwire, -, powner⟩
    · rw [same, ← shape.bytes, ← shape.addr]
      exact ⟨r.block, stored, shape.built.owner _⟩
    · exact ⟨p.2.1, BlockLayout.recordAt_ser pwire ((BlockRecords.runBlock_bounded hr).2 p hp) hP, powner _⟩

section Fold

variable {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env}
  {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source} {snap : DriverAcc}
  {rep : Ix.Name} {all : Ix.Set Ix.Name} {r : BlockResult} {c : BlockState}

/-- **Every member of a fold block is published at a record the block owns.** The member is a
closure name, so the fold compiled a block that claims it (`GroupRuns.foldBlock_of`); that block
holds it (`claim_in_block`), so it is this block (`block_unique`), and this run claims the member
too (`claim_transfer`), at a record the block owns (`claim_owned`). -/
theorem _root_.Ix.Cert.GroupRuns.FoldBlock.owned (P : Premises env roots sub ixe failures t envQ)
    (fb : FoldBlock env sub ixe failures snap rep all r c) :
    ∀ x, all.contains x = true →
      ∃ P' c', addrOf ixe x = some P' ∧ recordAt ixe P' = some c' ∧ ownerOf P' c' = r.blockAddr := by
  intro x hx
  obtain ⟨x₀, ci, hx₀, hxx₀⟩ := LayoutExtra.stored_key (fb.members x hx)
  obtain ⟨snap', rep', all', r', c', fb', ⟨a', b', hclaim'⟩, -⟩ := GroupRuns.foldBlock_of P hx₀
  have hin' := claim_in_block P.compiled fb'.env fb'.block fb'.ran hclaim'
  have hin : all.contains x₀ = true := by
    rw [← Std.HashSet.contains_congr hxx₀]
    exact hx
  have same := block_unique fb.block hin fb'.block hin'
  subst all'
  have hkey : blockKey rep' all = blockKey rep all := blockKey_congr (Condense.condense_nonempty fb.block)
  have ran' := fb'.ran
  rw [hkey] at ran' hclaim'
  obtain ⟨a, b, hclaim⟩ := claim_transfer fb.ran ran' (fun y => by rw [fb.env, fb'.env]) hclaim'
  have hsub : (sub.consts.get? x₀).isSome = true := by
    rw [SourceStoredNames.stored_get hx₀]
    rfl
  obtain ⟨haddr, hb⟩ := fb.published.claims x₀ a b hclaim hsub
  obtain ⟨c'', hrec, hown⟩ := claim_owned fb.ran (BlockPublication.stored fb.ran fb.published) hclaim hb
  exact ⟨a, c'', (LayoutRefs.addrOf_congr hxx₀).trans haddr, hrec, hown⟩

/-- **A name a fold block's terms mention is a name a closure constant's term mentions**: a
member's, or a constructor's its inductive member lists, which the closure holds. -/
theorem _root_.Ix.Cert.GroupRuns.FoldBlock.mentionedIn (hcl : IsClosure env roots sub)
    (fb : FoldBlock env sub ixe failures snap rep all r c) {m : Ix.Name}
    (hm : RefTables.Mentioned snap.cenv.env (fun x => all.contains x = true ∨ x = blockKey rep all) m) :
    TraceFold.MentionedIn env sub m := by
  obtain ⟨x, e, hN, ⟨ci, hci, hte⟩, hme⟩ := hm
  have hxall : all.contains x = true :=
    hN.elim id fun h => h ▸ blockKey_mem (Condense.condense_nonempty fb.block)
  have hxsub := fb.members x hxall
  have hcix : env.consts.get? x = some ci := by
    rw [← fb.env]
    exact hci
  rcases hte with he | ⟨iv, cn, cv, rfl, hcn, hcv, rfl⟩
  · exact ⟨x, ci, e, hxsub, hcix, he, hme⟩
  · have hcnenv : env.consts.get? cn = some (.ctorInfo cv) := by
      rw [← fb.env]
      exact hcv
    have hcnsub := CompiledRefs.sub_of_ref hcl hxsub hcix (FreshSnapshot.refsOf_induct iv hcn)
      (by rw [hcnenv]; rfl)
    exact ⟨cn, .ctorInfo cv, cv.cnst.type, hcnsub, hcnenv, by simp [termsOf, Ix.ConstantInfo.getCnst], hme⟩

/-- **A mentioned name a fold block binds is published at its binding**, and is an input constant
(`FoldBlock.mention_published`). -/
theorem _root_.Ix.Cert.GroupRuns.FoldBlock.refsPublished (P : Premises env roots sub ixe failures t envQ)
    (fb : FoldBlock env sub ixe failures snap rep all r c) :
    ∀ m a, RefTables.Mentioned snap.cenv.env (fun x => all.contains x = true ∨ x = blockKey rep all) m →
      lookupBinding snap.cenv (bindingView {}) m = some a →
        addrOf ixe m = some a ∧ (env.consts.get? m).isSome = true := by
  intro m a hm hb
  obtain ⟨d, hmem, hda, hsub⟩ := fb.mention_published P (fb.mentionedIn P.source.1 hm) hb
  refine ⟨?_, ?_⟩
  · unfold addrOf
    rw [Std.HashMap.get?_eq_getElem?,
      (Std.HashMap.mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some.mp hmem).2, Option.map_some, hda]
  · rw [← CompiledRefs.closure_same P.source.1 hsub]
    exact hsub

/-- **`CompiledRefs.RefsAt` at a closure name's published address**, from the fold block that
claims it (`GroupRuns.foldBlock_of`). -/
theorem refsAt_of (P : Premises env roots sub ixe failures t envQ) {n : Ix.Name} {ci : Ix.ConstantInfo}
    (hst : (n, ci) ∈ sub.consts.toList) {Pa : Address} (hP : addrOf ixe n = some Pa) :
    (sub.consts.get? n).isSome = true ∧ CompiledRefs.RefsAt env ixe n Pa := by
  have hsub : (sub.consts.get? n).isSome = true := by
    rw [SourceStoredNames.stored_get hst]
    rfl
  obtain ⟨snap, rep, all, r, c, fb, ⟨a, b, hclaim⟩, -⟩ := GroupRuns.foldBlock_of P hst
  obtain ⟨haddr, hb⟩ := fb.published.claims n a b hclaim hsub
  rw [hP] at haddr
  obtain rfl := Option.some.inj haddr
  refine ⟨hsub, snap.cenv, rep, all, r, c, b, fb.block, claim_in_block P.compiled fb.env fb.block fb.ran hclaim,
    blockKey_mem (Condense.condense_nonempty fb.block), fb.ran, hclaim, hb,
    BlockPublication.stored fb.ran fb.published, fb.env, fun a h => ?_, fb.refsPublished P, fb.owned P⟩
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  rw [fb.blobs a v hv]
  rfl

/-- **Every closure name is a member of a block of the input's condensation**: the block that
claims it (`GroupRuns.foldBlock_of`, `claim_in_block`). -/
theorem inBlocks (P : Premises env roots sub ixe failures t envQ) :
    ∀ x, (sub.consts.get? x).isSome = true → FreshSnapshot.Member (CompiledRefs.envBlocks env) x := by
  intro x hx
  obtain ⟨x₀, ci, hx₀, hxx₀⟩ := LayoutExtra.stored_key hx
  obtain ⟨snap, rep, all, r, c, fb, ⟨a, b, hclaim⟩, -⟩ := GroupRuns.foldBlock_of P hx₀
  refine ⟨rep, all, fb.block, ?_⟩
  rw [Std.HashSet.contains_congr hxx₀]
  exact claim_in_block P.compiled fb.env fb.block fb.ran hclaim

/-- **A scheduled group's names are closure constants' keys**, when the schedule lets every group
through. -/
theorem group_stored (P : Premises env roots sub ixe failures t envQ)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    (scheduled : ∀ x ∈ (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList, ∃ conv, x.1.2 = .ok conv)
    {i : Nat} {gr : Group} (hgr : (quotientGraph ixe t hints sub).groups[i]? = some gr) :
    ∀ n ∈ gr.names, ∃ ci, (n, ci) ∈ sub.consts.toList := by
  obtain ⟨c0, hmem⟩ := Ix.LeanIngress.scheduleOf_complete _ (Array.getElem?_eq_some_iff.mp hgr).1
  obtain ⟨q, hq, hqe⟩ := Array.getElem_of_mem hmem
  have hx : ((i, c0), q) ∈ (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList :=
    Array.mem_toList_iff.mpr (Array.mem_zipIdx_iff_getElem?.mpr (by simp [hq, hqe]))
  obtain ⟨conv, hconv⟩ := scheduled _ hx
  obtain ⟨gr', c', hgr', hc, -⟩ := SourceTrace.graph_conversion (Ix.LeanIngress.scheduleOf_converted hmem hconv)
  obtain rfl : gr' = gr := Option.some.inj (hgr'.symm.trans hgr)
  exact ClosureLayout.converted_names_stored P hgr hc

end Fold

/-! ## The layout -/

/-- **The closure's record layout, at any hints**, when the schedule lets every group through. -/
theorem layout_of {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env}
    {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    (scheduled : ∀ x ∈ (scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList, ∃ conv, x.1.2 = .ok conv) :
    ClosureLayout.Layout ixe (quotientGraph ixe t hints sub) where
  block := BlockLayout.layoutBlock_of_claimed BlockWire.blocksWire fun _ _ hgr n hn a ha => by
    obtain ⟨ci, hci⟩ := group_stored P scheduled hgr n hn
    exact (LayoutExtra.claimedIn_of P n ci hci a ha).claimedAt
  refs := LayoutRefs.layoutRefs_of_compiled scheduled
    (CompiledRefs.compiledRefs_of P.source.1 P.compiled scheduled TraceFold.cacheRefs (blobsApart P.compiled)
      (compileReport_checks P.compiled).2.2.1 (inBlocks P) fun _ _ hgr n hn _ hPa => by
        obtain ⟨ci, hci⟩ := group_stored P scheduled hgr n hn
        exact refsAt_of P hci hPa)
  extra := LayoutExtra.layout_extra_of P hints

/-- **Every accepted closure's compiled records lie as quotient Source's graph says**
(`ClosureLayout.Layout`), at quotient Source's hints. -/
theorem layouts_hold :
    ∀ {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env}
      {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source},
      Premises env roots sub ixe failures t envQ →
      (∀ x ∈ (scheduleOf (quotientGraph ixe t ((Ix.LeanIngress.fiberHintsMap ixe)[·]?) sub)).zipIdx.toList,
        ∃ conv, x.1.2 = .ok conv) →
      ClosureLayout.Layout ixe (quotientGraph ixe t ((Ix.LeanIngress.fiberHintsMap ixe)[·]?) sub) :=
  fun P scheduled => layout_of P scheduled

end Ix.Cert.LayoutsHold

/--
info: 'Ix.Cert.LayoutsHold.layouts_hold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Cert.LayoutsHold.layouts_hold
