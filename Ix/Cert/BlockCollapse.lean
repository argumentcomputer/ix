import Ix.Cert.GroupRuns
import Ix.Cert.SourceRetained
import Ix.Cert.ClosureResolve

/-! # A block of several definitions is collapsed whole

Quotient Source lowers a group of several definitions to one declaration per member, at the
member's quotient key, and its collapse (`collapseRead`) keeps a declaration whose key no earlier
read declares and drops one whose key an earlier read declares. This module shows that the
collapse keeps such a read whole or drops it whole (`block_collapse`), the form
`TraceSegments.BlockNeeds.collapse` takes.

* **The collapse's two outcomes** (`collapseRead_whole_or_none`): a read of declarations with
  pairwise distinct keys, none of them generated, is kept whole when none of its keys is declared
  earlier, and dropped whole when every one is. This needs only the collapse's retained
  subsequence (`SourceRetained.collapseRead_retained`) and, per read, which keys earlier reads
  declare (`ClosureLayout.Steps`), not the collapse's state.
* **Distinct keys** (`block_raw_keys`): the lowering declares each member once, in the block's
  dependency order (`SourceDeclares.defOrder_perm`), and members at distinct addresses have
  distinct quotient keys: a block's members are published at distinct projections
  (`BlockPublication.apart`).
* **All or none of the keys declared earlier** (`earlier_block`): an earlier group with a name
  where a member is published holds a name where every member is. A name published at a
  definition projection is a definition that a block of several compiled (`dPrj_claimant`), so
  its group is a group of several definitions, whose block is the same record: the same address
  and so the same members' count, each published at the projection of its position. -/

namespace Ix.Cert.BlockCollapse

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileM Ix.CompileCert
open Ix.Cert.SourcePrelude (ReadInv ReadBad readStep readLoop readFinish forIn_id_inv_or_array SKey Scheduled)
open Ix.Cert.ClosureLayout (Steps quotientGraph addrOf qkey namesAt)
open Ix.Cert.TraceSegments (LoweredAt fibers defsOf)
open Ix.LeanIngress (CollapseState collapseRead Group Converted DefMember fiberAliasAt roleAtMap ingressKey
  isDefinition isFamily convert)

/-! ## The collapse's two outcomes -/

/-- **A collapsed read is its lowering with the kept declarations**: only the declarations and
the generated count change. -/
theorem collapseRead_form {s s' : CollapseState} {first : SKey} {raw r : Read .source}
    {dropped : Array SKey} (h : collapseRead s first raw = (s', .ok (r, dropped))) :
    r = { raw with decls := r.decls, generated := r.generated } := by
  have init : ReadInv s [] (none, s, #[], 0, #[]) :=
    ⟨rfl, .refl s, by simp, by simp, by simp, by simp, by simp⟩
  have inv := forIn_id_inv_or_array (ReadInv s) ReadBad
    (readStep first s.kept.size raw.generated) raw.decls.zipIdx
    (fun _ x _ a _ ha => by
      have hi := SourcePrelude.readStep_inv ha first s.kept.size raw.generated x
      cases hb : readStep first s.kept.size raw.generated x a <;> simpa only [hb] using hi) _ init
  change ReadInv s raw.decls.zipIdx.toList (readLoop s first raw) ∨ ReadBad (readLoop s first raw) at inv
  rw [SourcePrelude.collapseRead_eq] at h
  rcases inv with hi | hb
  · simp only [readFinish, hi.active, Prod.mk.injEq, Except.ok.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    rfl
  · obtain ⟨t, e, he⟩ := hb
    simp [readFinish, he] at h

/-- Two declarations of a list whose names are pairwise distinct, sharing a name, are one. -/
theorem eq_of_names : ∀ {l : List (Declaration .source)}, (l.flatMap Declaration.names).Nodup →
    ∀ {d d' : Declaration .source}, d ∈ l → d' ∈ l → ∀ {k : SKey}, k ∈ d.names → k ∈ d'.names → d = d'
  | [], _, _, _, hd, _, _, _, _ => by cases hd
  | x :: l, h, d, d', hd, hd', k, hk, hk' => by
    rw [List.flatMap_cons, List.nodup_append] at h
    obtain ⟨-, h₂, h₃⟩ := h
    rcases List.mem_cons.mp hd with rfl | hl <;> rcases List.mem_cons.mp hd' with rfl | hl'
    · rfl
    · exact absurd rfl (h₃ k hk k (List.mem_flatMap.mpr ⟨d', hl', hk'⟩))
    · exact absurd rfl (h₃ k hk' k (List.mem_flatMap.mpr ⟨d, hl, hk⟩))
    · exact eq_of_names h₂ hl hl' hk hk'

/-- Declarations whose names are pairwise distinct and never empty are distinct. -/
theorem nodup_of_names : ∀ {l : List (Declaration .source)}, (l.flatMap Declaration.names).Nodup →
    (∀ d ∈ l, d.names ≠ []) → l.Nodup
  | [], _, _ => List.nodup_nil
  | x :: l, h, named => by
    rw [List.flatMap_cons, List.nodup_append] at h
    obtain ⟨-, h₂, h₃⟩ := h
    refine List.nodup_cons.mpr ⟨fun hx => ?_, nodup_of_names h₂ fun d hd => named d (List.mem_cons_of_mem _ hd)⟩
    obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil _ (named x List.mem_cons_self)
    exact h₃ k hk k (List.mem_flatMap.mpr ⟨x, hx, hk⟩) rfl

/-- **A read is kept whole or dropped whole** by the collapse, when its declarations have
pairwise distinct, non-empty names and none is generated, given which names `E` earlier reads
declare: every name of the read is declared earlier or by the kept read, no kept name is declared
earlier, and when one name of the read is declared earlier, every one is. -/
theorem collapseRead_whole_or_none {s s' : CollapseState} {first : SKey} {raw rd : Read .source}
    {dropped : Array SKey} (h : collapseRead s first raw = (s', .ok (rd, dropped)))
    (hgen : raw.generated = 0) (distinct : (raw.decls.toList.flatMap Declaration.names).Nodup)
    (named : ∀ d ∈ raw.decls.toList, d.names ≠ []) (E : SKey → Prop)
    (declared : ∀ d ∈ raw.decls.toList, ∀ k ∈ d.names, E k ∨ ∃ d' ∈ rd.decls.toList, k ∈ d'.names)
    (fresh : ∀ d ∈ rd.decls.toList, ∀ k ∈ d.names, ¬ E k)
    (whole : ∀ d ∈ raw.decls.toList, ∀ k ∈ d.names, E k → ∀ d' ∈ raw.decls.toList, ∀ k' ∈ d'.names, E k') :
    rd = raw ∨ rd = { raw with decls := #[], generated := 0 } := by
  have form := collapseRead_form h
  obtain ⟨G, O, sub, keep, count, gens, -⟩ := SourceRetained.collapseRead_retained h
  have hG : G = [] := by
    cases G with
    | nil => rfl
    | cons x _ =>
      have := gens x List.mem_cons_self
      omega
  subst hG
  have hgen' : rd.generated = 0 := by simpa using count
  have within : ∀ d ∈ rd.decls.toList, d ∈ raw.decls.toList := (SourcePrelude.collapseRead_facts h).2.2.2.1
  by_cases hE : ∃ d ∈ raw.decls.toList, ∃ k ∈ d.names, E k
  · -- every name is declared earlier, so nothing is kept
    right
    obtain ⟨d₀, hd₀, k₀, hk₀, e₀⟩ := hE
    have empty : rd.decls = #[] := by
      apply Array.toList_inj.mp
      rw [Array.toList_empty]
      refine List.eq_nil_iff_forall_not_mem.mpr fun d hd => ?_
      obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil _ (named d (within d hd))
      exact fresh d hd k hk (whole d₀ hd₀ k₀ hk₀ e₀ d (within d hd) k hk)
    rw [form, empty, hgen']
  · -- no name is declared earlier, so everything is kept
    left
    have every : ∀ d ∈ raw.decls.toList, d ∈ rd.decls.toList := by
      intro d hd
      obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil _ (named d hd)
      rcases declared d hd k hk with e | ⟨d', hd', hk'⟩
      · exact absurd ⟨d, hd, k, hk, e⟩ hE
      · rw [eq_of_names distinct hd (within d' hd') hk hk']
        exact hd'
    have hsub : rd.decls.toList.Sublist raw.decls.toList := by
      rw [keep, List.nil_append]
      have := sub.map Prod.fst
      rwa [List.nil_append, List.zipIdx_map_fst] at this
    have nd := nodup_of_names distinct named
    have same : rd.decls.toList = raw.decls.toList :=
      hsub.eq_of_length (Nat.le_antisymm hsub.length_le (nd.length_le_of_subset every))
    rw [form, Array.toList_inj.mp same, hgen', ← hgen]

/-! ## A name published at a definition projection -/

/-- A built record is no definition projection. -/
theorem built_not_dPrj {c : Ixon.Constant} (built : BlockLayout.Built c) (p : Ixon.DefinitionProj) :
    c.info ≠ .dPrj p := by
  intro hi
  have h₁ := built.owner ⟨⟨#[]⟩⟩
  have h₂ := built.owner ⟨⟨#[0]⟩⟩
  simp only [ownerOf, hi] at h₁ h₂
  have := congrArg (fun a : Address => a.hash.size) (h₁.symm.trans h₂)
  exact absurd this (by decide)

/-- **A mutual block's rows at definition projections are its definitions'**: every row is the
block itself, or a row whose record is a definition projection names a definition-like source. -/
theorem mutual_dPrj_rows (sources : List (List MutConst)) :
    Emission.Yields (compileMutualBlock sources) (fun out => ∀ row ∈ out.projections, row.2.1 = out.block ∨
      ∀ p, row.2.1.info = .dPrj p → ∃ c ∈ sources, ∃ src ∈ c, GroupBlocks.IsDefn src ∧ row.1 = src.name) := by
  refine ProjectionLayout.mutual_block _ sources ?_
  unfold compileMutualPayload
  refine Emission.Yields.bindAny _ fun compiled => ?_
  intro context before output after ran
  obtain ⟨-, -, built⟩ := ProjectionLayout.finish_mutual_ok context sources compiled.1 compiled.2.2 ran
  obtain ⟨-, wrapped | collapsed⟩ :=
    MutualArtifact.build_cases _ sources compiled.1 compiled.2.2 before output built
  · obtain ⟨targets, metadata, -, -, proj⟩ := wrapped
    intro row hrow
    refine .inr fun p hp => ?_
    have hl := Claims.row_logical hrow
    rw [proj, MutualProjections.build_rows] at hl
    unfold MutualProjections.expectedRows at hl
    obtain ⟨⟨members, index⟩, hm, hl⟩ := List.mem_flatMap.1 hl
    obtain ⟨src, hsrc, hl⟩ := List.mem_flatMap.1 hl
    unfold MutualProjections.sourceRows at hl
    rcases List.mem_cons.1 hl with e | e
    · obtain ⟨e₁, e₂⟩ := Prod.mk.inj e
      refine ⟨members, Claims.mem_of_mem_zipIdx hm, src, hsrc, ?_, e₁⟩
      cases src with
      | defn d => trivial
      | indc i => rw [e₂] at hp; simp [MutualProjections.memberProjection] at hp
      | recr r => rw [e₂] at hp; simp [MutualProjections.memberProjection] at hp
    · obtain ⟨⟨ctor, ci⟩, -, he⟩ := List.mem_map.1 e
      rw [← (Prod.mk.inj he).2] at hp
      simp [MutualProjections.constructorProjection] at hp
  · obtain ⟨-, -, rows⟩ := collapsed
    intro row hrow
    refine .inl ?_
    have hl := Claims.row_logical hrow
    rw [rows] at hl
    obtain ⟨src, -, he⟩ := List.mem_map.1 hl
    exact (Prod.mk.inj he).2.symm

/-- A definition-like member a block's loop made, from a definition the environment holds. -/
def DefnSource (E : Ix.Environment) (m : MutConst) : Prop :=
  ∃ k ci, E.get? k = some ci ∧ isDefinition ci = true ∧ m.name = ci.getCnst.name

/-- **The members loop makes definition-like members only of definitions.** -/
theorem loop_defnSource (ctx : CompileEnv × BlockEnv) (l : List Ix.Name) (init : Array MutConst)
    (s s' : BlockState) (cs : Array MutConst)
    (h : rawRun (GroupBlocks.membersLoop l init) ctx s = (.ok cs, s'))
    (hinit : ∀ m ∈ init, GroupBlocks.IsDefn m → DefnSource ctx.1.env m) :
    ∀ m ∈ cs, GroupBlocks.IsDefn m → DefnSource ctx.1.env m := by
  refine LayoutExtra.forIn_rawRun_inv
    (fun (acc : Array MutConst) => ∀ m ∈ acc, GroupBlocks.IsDefn m → DefnSource ctx.1.env m)
    ?_ l init s s' cs hinit h
  intro n s₀ acc acc' s₁ hacc ran
  obtain ⟨c, mid, hfind, ran⟩ := bind_ok ran
  have hc := BlockRecords.findConst_ok hfind
  have push : ∀ y, (GroupBlocks.IsDefn y → DefnSource ctx.1.env y) →
      ∀ x ∈ acc.push y, GroupBlocks.IsDefn x → DefnSource ctx.1.env x := by
    intro y hy x hx
    rcases Array.mem_push.mp hx with hx | rfl
    · exact hacc x hx
    · exact hy
  cases c with
  | inductInfo val =>
    obtain ⟨y, mid', hy, ran⟩ := bind_ok ran
    rw [rawRun_pure] at ran
    cases ran
    refine push y fun hk => ?_
    unfold MutConst.mkIndc at hy
    obtain ⟨_, _, -, hy⟩ := bind_ok hy
    rw [rawRun_pure] at hy
    cases hy
    cases hk
  | defnInfo val =>
    rw [rawRun_pure] at ran
    cases ran
    exact push _ fun _ => ⟨n, _, hc, rfl, rfl⟩
  | opaqueInfo val =>
    rw [rawRun_pure] at ran
    cases ran
    exact push _ fun _ => ⟨n, _, hc, rfl, rfl⟩
  | thmInfo val =>
    rw [rawRun_pure] at ran
    cases ran
    exact push _ fun _ => ⟨n, _, hc, rfl, rfl⟩
  | recInfo val =>
    rw [rawRun_pure] at ran
    cases ran
    exact push _ fun hk => by cases hk
  | _ =>
    rw [rawRun_pure] at ran
    cases ran
    exact hacc

/-- A set whose every name is `==` to one name has at most one element. -/
theorem size_le_one {all : Ix.Set Ix.Name} {n : Ix.Name} (h : ∀ x, all.contains x = true → (x == n) = true) :
    all.size ≤ 1 := by
  rw [← Std.HashSet.length_toList]
  have hd := Std.HashSet.distinct_toList (m := all)
  match hl : all.toList with
  | [] => simp
  | [_] => simp
  | a :: b :: rest =>
    rw [hl] at hd
    have ha := h a (GroupRuns.contains_of_listed (by rw [hl]; simp))
    have hb := h b (GroupRuns.contains_of_listed (by rw [hl]; simp))
    have := (List.pairwise_cons.mp hd).1 b (by simp)
    rw [BEq.trans ha (BEq.symm hb)] at this
    cases this

/-- A set holding a name is not empty. -/
theorem size_pos {all : Ix.Set Ix.Name} {n : Ix.Name} (h : all.contains n = true) : 0 < all.size := by
  rw [← Std.HashSet.length_toList]
  obtain ⟨k, hk, -⟩ := GroupRuns.listed h
  exact List.length_pos_of_mem hk

section Compile

variable {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env}
  {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}

/-- **A closure name published at a definition projection is a definition a block of several
compiled**: its fold block's claim is a row of the block's mutual compile (a lone compile has no
rows, and the block's own record is no projection) made of a definition, and the block holds
the name and more. -/
theorem dPrj_claimant (P : Premises env roots sub ixe failures t envQ) {n : Ix.Name} {ci : Ix.ConstantInfo}
    (hm : (n, ci) ∈ sub.consts.toList) {A : Address} (hA : addrOf ixe n = some A) {cA : Ixon.Constant}
    (hc : recordAt ixe A = some cA) {p : Ixon.DefinitionProj} (hp : cA.info = .dPrj p) :
    isDefinition ci = true ∧ ∃ snap rep all r c, GroupRuns.FoldBlock env sub ixe failures snap rep all r c ∧
      all.contains n = true ∧ all.size ≠ 1 := by
  obtain ⟨snap, rep, all, r, c, fb, ⟨a, b, hclaim⟩, hmem⟩ := GroupRuns.foldBlock_of P hm
  have hs : (sub.consts.get? n).isSome = true := by rw [SourceStoredNames.stored_get hm]; rfl
  obtain ⟨ha, hb⟩ := fb.published.claims n a b hclaim hs
  obtain rfl : A = a := Option.some.inj (hA.symm.trans ha)
  have shape := BlockLayout.runBlock_shape fb.ran
  have wire := BlockWire.blocksWire _ _ _ _ _ fb.ran
  have blockRec := BlockPublication.stored fb.ran fb.published
  have notBlock : cA ≠ r.block := fun e => built_not_dPrj shape.built p (e ▸ hp)
  -- the claim is a row of the block, at its record
  have row : ∃ q ∈ r.projections, q.1 = n ∧ q.2.1 = cA := by
    unfold Resolution.claimWrites at hclaim
    split at hclaim
    · simp only [List.mem_toArray, List.mem_singleton, Prod.mk.injEq] at hclaim
      obtain ⟨-, rfl, -⟩ := hclaim
      rw [blockRec] at hc
      exact absurd (Option.some.inj hc).symm notBlock
    · obtain ⟨q, hq, e⟩ := Array.mem_map.mp hclaim
      simp only [Prod.mk.injEq] at e
      obtain ⟨e₁, rfl, rfl⟩ := e
      refine ⟨q, hq, e₁, ?_⟩
      rcases shape.rows q hq with same | proj
      · have := BlockLayout.recordAt_ser (by rw [same]; exact wire) hb
        rw [hc] at this
        exact (Option.some.inj this).symm
      · have := BlockLayout.recordAt_ser proj.1 hb
        rw [hc] at this
        exact (Option.some.inj this).symm
  obtain ⟨q, hq, hqn, hqc⟩ := row
  obtain ⟨const, hconst, paths⟩ := GroupRuns.runBlock_paths fb.ran
  rcases paths with ⟨hcond, hrun⟩ | ⟨hcond, cs, out, s₄, hloop, hout, -, hrec⟩
  · -- a lone compile has no rows
    have hind : GroupRuns.isIndConst const = false := by
      revert hcond
      cases GroupRuns.isIndConst const <;> simp
    have lone := ClosureResolve.constantInfo_lone const
      (fun v e => by subst e; simp [GroupRuns.isIndConst] at hind)
      (fun v e => by subst e; simp [GroupRuns.isIndConst] at hind) _ _ _ _ hrun
    rw [lone.1] at hq
    exact absurd hq (Array.not_mem_empty _)
  · -- a mutual compile's row at a definition projection is a definition's
    simp only [BlockRecords.recordsOf, Prod.mk.injEq] at hrec
    obtain ⟨hblock, -, -, hrows⟩ := hrec
    have hm' : (q.1, q.2.1) ∈ out.projections.map (fun p => (p.1, p.2.1)) := by
      rw [← hrows]
      exact Array.mem_map.mpr ⟨q, hq, rfl⟩
    obtain ⟨q', hq', e⟩ := Array.mem_map.mp hm'
    obtain ⟨e₁, e₂⟩ := Prod.mk.inj e
    rcases mutual_dPrj_rows (sourceClasses cs) _ _ _ _ hout q' hq' with same | defn
    · exact absurd (show cA = r.block by rw [← hqc, ← e₂, same, hblock]) notBlock
    obtain ⟨cl, hcl, src, hsrc, hdefn, hname⟩ := defn p (by rw [e₂, hqc]; exact hp)
    obtain ⟨k, ci', hk, hdef, hnm⟩ := loop_defnSource _ all.toList #[] {} {} cs hloop
      (fun m hm => by simp at hm) src (Claims.mem_sourceClasses hcl hsrc) hdefn
    have hk' := (fb.env k).symm.trans hk
    have hn : ci'.getCnst.name = n := by rw [← hnm, ← hname, e₁, hqn]
    have hci := FamilyGroups.same_stored P.compiled (SourceStoredNames.stored_input P hm) hk' hn
    rw [hci] at hdef
    have notCtor : ∀ cv, ci ≠ .ctorInfo cv := fun cv e => by rw [e] at hdef; simp [isDefinition] at hdef
    refine ⟨hdef, snap, rep, all, r, c, fb, hmem notCtor, fun h1 => ?_⟩
    -- a block of one name holding a definition compiles alone
    have hkey := Resolution.blockKey_mem (lo := rep) (Condense.condense_nonempty fb.block)
    have beq := GroupRuns.single_beq h1 hkey (hmem notCtor)
    rw [fb.env, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr beq, ← Std.HashMap.get?_eq_getElem?,
      SourceStoredNames.stored_get (SourceStoredNames.stored_input P hm)] at hconst
    have hcc := Option.some.inj hconst
    have notInd : GroupRuns.isIndConst ci = false := by
      revert hdef
      cases ci <;> simp [isDefinition, GroupRuns.isIndConst]
    rw [← hcc] at hcond
    simp [h1, notInd] at hcond

/-- The record a block of definitions publishes its member `j` at. -/
abbrev dProj (B : Address) (j : Nat) : Ixon.Constant := ⟨.dPrj ⟨j.toUInt64, B⟩, #[], #[], #[]⟩

/-- **A group of several definitions is published at a block's projections**: the block's record
is a block of as many definitions, member `j` is published at the projection of position `j`,
and members are published apart. -/
theorem members_at (P : Premises env roots sub ixe failures t envQ)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    (scheduled : ∀ x ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList,
      ∃ conv, x.1.2 = .ok conv)
    {i : Nat} {members : Array Ix.ConstantInfo} {c : Converted}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.definitions members))
    (hconv : convert (.definitions members) = .ok c) (two : 2 ≤ members.size) :
    ∃ (B : Address) (cB : Ixon.Constant) (ms : Array Ixon.MutConst), recordAt ixe B = some cB ∧
      cB.info = .muts ms ∧ ms.size = members.size ∧
      (∀ j (hj : j < members.size), addrOf ixe members[j].getCnst.name =
        some (Address.admissionHash (Ixon.ser (dProj B j))) ∧
        recordAt ixe (Address.admissionHash (Ixon.ser (dProj B j))) = some (dProj B j)) ∧
      ∀ j (hj : j < members.size) j' (hj' : j' < members.size),
        addrOf ixe members[j].getCnst.name = addrOf ixe members[j'].getCnst.name → j = j' := by
  obtain ⟨snap, rep, all, r, cc, fb, -, out, after, ran, -, hrec⟩ := GroupRuns.definitions_run P scheduled hgr two
  have hconv' : Ix.LeanIngress.convertDefinitions members = .ok c := hconv
  have views := TraceSegments.views_of_convert hconv' two
  have hlen : members.size = (defsOf members).length := by simpa using DefinitionBlocks.forall₂_length views
  have nameAt : ∀ j (hj : j < (defsOf members).length), members[j].getCnst.name = (defsOf members)[j].name := by
    intro j hj
    have hv := DefinitionBlocks.forall₂_getElem views j (by simp; omega) hj
    simp only [Array.getElem_toList] at hv
    exact (RecordReadings.sourceData_facts hv).1
  have insub : ∀ j (hj : j < (defsOf members).length), (sub.consts.get? (defsOf members)[j].name).isSome = true := by
    intro j hj
    obtain ⟨ci, hci⟩ := ClosureLayout.converted_names_stored P hgr hconv _
      ((TraceSegments.definitions_names members _).mpr ⟨j, by omega, nameAt j hj⟩)
    rw [SourceStoredNames.stored_get hci]
    rfl
  obtain ⟨-, pubs⟩ := BlockPublication.member_published fb.ran fb.published (by omega) ran hrec insub
  have apart := BlockPublication.apart fb.ran fb.published (by omega) ran hrec insub
  obtain ⟨ms, hinfo, hms, -⟩ := DefinitionSegments.block_info (by omega) ran
  have hblock : r.block = out.block := by
    simp only [BlockRecords.recordsOf, Prod.mk.injEq] at hrec
    exact hrec.1
  refine ⟨r.blockAddr, r.block, ms, BlockPublication.stored fb.ran fb.published, hblock ▸ hinfo, by omega,
    fun j hj => ?_, fun j hj j' hj' same => ?_⟩
  · rw [nameAt j (by omega)]
    exact pubs j (by omega)
  · rw [nameAt j (by omega), nameAt j' (by omega)] at same
    exact apart j (by omega) j' (by omega) same

/-- **Two closure names with one quotient key are published at one address.** -/
theorem addr_of_qkey (P : Premises env roots sub ixe failures t envQ) {n n' : Ix.Name} {ci ci' : Ix.ConstantInfo}
    (hn : (n, ci) ∈ sub.consts.toList) (hn' : (n', ci') ∈ sub.consts.toList)
    (key : qkey (fiberAliasAt ixe (roleAtMap t)) n = qkey (fiberAliasAt ixe (roleAtMap t)) n') :
    addrOf ixe n = addrOf ixe n' := by
  obtain ⟨named, hm, hget⟩ := SourceStoredNames.stored_published P hn
  obtain ⟨named', hm', hget'⟩ := SourceStoredNames.stored_published P hn'
  have e₁ := ReadingKeys.keyAddress_quotientKey (defaultTable_check P.table) P.bound P.agree hm
  have e₂ := ReadingKeys.keyAddress_quotientKey (defaultTable_check P.table) P.bound P.agree hm'
  have hq : quotientKey ixe t n = quotientKey ixe t n' := key
  rw [hq, e₂] at e₁
  unfold addrOf
  rw [hget, hget', Option.map_some, Option.map_some, e₁]

/-- **Two closure names published at one address have one quotient key.** -/
theorem qkey_of_addr (P : Premises env roots sub ixe failures t envQ) {n n' : Ix.Name} {ci ci' : Ix.ConstantInfo}
    (hn : (n, ci) ∈ sub.consts.toList) (hn' : (n', ci') ∈ sub.consts.toList)
    (same : addrOf ixe n = addrOf ixe n') :
    qkey (fiberAliasAt ixe (roleAtMap t)) n = qkey (fiberAliasAt ixe (roleAtMap t)) n' := by
  have tb := tableBound_of (defaultTable_check P.table) P.bound
  obtain ⟨named, hm, hget⟩ := SourceStoredNames.stored_published P hn
  obtain ⟨named', hm', hget'⟩ := SourceStoredNames.stored_published P hn'
  have ha : named.addr = named'.addr := by
    unfold addrOf at same
    rw [hget, hget'] at same
    exact Option.some.inj same
  exact Ix.LeanIngress.fiberAliasAt_addr_inj tb (P.agree n named hm) (by rw [P.agree n' named' hm', ha])

/-- **An earlier group with a name where a member is published has a name where every member
is**: the name is a definition that a block of several compiled (`dPrj_claimant`), so its group
is a group of several definitions, whose block is the member's block. -/
theorem earlier_block (P : Premises env roots sub ixe failures t envQ)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    (scheduled : ∀ x ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList,
      ∃ conv, x.1.2 = .ok conv)
    {i : Nat} {members : Array Ix.ConstantInfo} {c : Converted}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.definitions members))
    (hconv : convert (.definitions members) = .ok c) (two : 2 ≤ members.size)
    {i' : Nat} {gr' : Group} {c' : Converted}
    (hgr' : (quotientGraph ixe t hints sub).groups[i']? = some gr') (hconv' : convert gr' = .ok c')
    {n₀ : Ix.Name} (hn₀ : n₀ ∈ gr'.names) {a : Nat} (ha : a < members.size)
    (same : addrOf ixe n₀ = addrOf ixe members[a].getCnst.name) :
    ∀ b (hb : b < members.size), ∃ n₁ ∈ gr'.names, addrOf ixe n₁ = addrOf ixe members[b].getCnst.name := by
  obtain ⟨B, cB, ms, hB, hinfo, hms, addrs, -⟩ := members_at P scheduled hgr hconv two
  obtain ⟨ci₀, hci₀⟩ := ClosureLayout.converted_names_stored P hgr' hconv' n₀ hn₀
  obtain ⟨hA, hrecA⟩ := addrs a ha
  rw [hA] at same
  obtain ⟨hdef, snap, rep, all, r, cc, fb, hmemn, hsize⟩ := dPrj_claimant P hci₀ same hrecA (p := ⟨a.toUInt64, B⟩) rfl
  -- the group is a group of definitions
  obtain ⟨k, ci, hk, hname, hkind⟩ := (LayoutExtra.groupsOf_kinded sub (blocksOf sub) gr'
    (show gr' ∈ Ix.LeanIngress.groupsOf sub (blocksOf sub) from Array.mem_of_getElem? hgr') c' hconv').1 n₀ hn₀
  have hk' : k = n₀ := by
    rw [← hname, inputsNamed P.compiled k ci (SourceStoredNames.stored_input P hk)]
  rw [hk'] at hk
  have hci : ci = ci₀ := Option.some.inj
    ((SourceStoredNames.stored_get hk).symm.trans (SourceStoredNames.stored_get hci₀))
  rw [hci] at hkind
  have notFamily : isFamily ci₀ = false := by
    revert hdef
    cases ci₀ <;> simp [isDefinition, isFamily]
  cases gr' with
  | invalid ns e => simp [convert, throw, throwThe, MonadExceptOf.throw] at hconv'
  | «axiom» v =>
    simp only [LayoutExtra.GroupKind] at hkind
    rw [hkind] at hdef
    simp [isDefinition] at hdef
  | quot v =>
    simp only [LayoutExtra.GroupKind] at hkind
    rw [hkind] at hdef
    simp [isDefinition] at hdef
  | «inductive» types ctors recs =>
    simp only [LayoutExtra.GroupKind] at hkind
    rw [notFamily] at hkind
    cases hkind
  | definitions ms' =>
    obtain ⟨l⟩ := ms'
    rcases l with _ | ⟨x, _ | ⟨x', rest⟩⟩
    · simp [Group.names] at hn₀
    · -- a group of one definition compiles alone
      exfalso
      have hx : n₀ = x.getCnst.name := by simpa [Group.names] using hn₀
      have hsingle : (Group.definitions (List.toArray [x])).names = #[n₀] := by simp [Group.names, hx]
      have one := GroupBlocks.single_block P scheduled hgr' trivial hsingle fb.block hmemn
      have := size_le_one one
      have := size_pos hmemn
      omega
    · -- a group of several definitions, at the same block
      have two' : 2 ≤ (List.toArray (x :: x' :: rest)).size := by simp
      obtain ⟨B', cB', ms'', hB', hinfo', hms', addrs', -⟩ := members_at P scheduled hgr' hconv' two'
      obtain ⟨a', ha', hname'⟩ := (TraceSegments.definitions_names _ n₀).mp hn₀
      obtain ⟨hA', hrecA'⟩ := addrs' a' ha'
      rw [hname', same] at hA'
      have e := Option.some.inj hA'
      rw [← e] at hrecA'
      have eproj := Option.some.inj (hrecA.symm.trans hrecA')
      have hBB : B' = B := by
        simp only [dProj, Ixon.Constant.mk.injEq, Ixon.ConstantInfo.dPrj.injEq, Ixon.DefinitionProj.mk.injEq,
          and_true] at eproj
        exact eproj.2.symm
      rw [hBB] at hB' addrs'
      have hcB : cB' = cB := Option.some.inj (hB'.symm.trans hB)
      rw [hcB, hinfo] at hinfo'
      have hsame : ms'' = ms := (Ixon.ConstantInfo.muts.inj hinfo').symm
      rw [hsame] at hms'
      intro b hb
      exact ⟨_, (TraceSegments.definitions_names _ _).mpr ⟨b, by omega, rfl⟩,
        ((addrs' b (by omega)).1.trans (addrs b hb).1.symm)⟩

end Compile

/-! ## The read's keys -/

/-- Quotient Source's renaming of a group of definitions renames its members' keys, in order. -/
theorem quotient_names (ρ : Ix.LeanIngress.FiberMap)
    (hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint) (xs : Array DefMember) :
    ∃ ys : Array DefMember, ((Converted.definitions xs).withHints hints).quotient ρ = .definitions ys ∧
      ys.toList.map (·.cv.name) = xs.toList.map fun m => Ix.LeanIngress.Key.subst ρ m.cv.name := by
  refine ⟨_, rfl, ?_⟩
  simp only [Array.toList_map, List.map_map]
  refine List.map_congr_left fun m _ => ?_
  simp only [Function.comp_def, RecordReadings.defMember_canon, DefMember.substKeys,
    Ix.LeanIngress.ConstantVal.substKeys]
  split <;> rfl

/-- A lowering of definitions declares each member's key, one per declaration. -/
theorem lowered_names {st : State .source} {ys : Array DefMember} {raw : Read .source}
    (h : Ix.LeanIngress.lower st (.definitions ys) = .ok raw) :
    raw.decls.toList.flatMap Declaration.names = ys.toList.map (·.cv.name) ∧
      ∀ d ∈ raw.decls.toList, ∃ m ∈ ys.toList, d.names = [m.cv.name] := by
  obtain ⟨ds, hds, -, hF⟩ := DefinitionBlockReads.lower_defs h
  rw [hds, List.toList_toArray]
  clear hds h
  generalize ys.toList = L at hF ⊢
  induction hF with
  | nil => exact ⟨rfl, fun d hd => by cases hd⟩
  | @cons m d L ds hd _ ih =>
    obtain ⟨b, hd⟩ := hd
    have hn := ReaderUnits.lowerDefinition_names hd
    refine ⟨by simp only [List.flatMap_cons, List.map_cons, hn, ih.1, List.singleton_append], fun d' hd' => ?_⟩
    rcases List.mem_cons.mp hd' with rfl | hd'
    · exact ⟨m, List.mem_cons_self, hn⟩
    · obtain ⟨m', hm', e⟩ := ih.2 d' hd'
      exact ⟨m', List.mem_cons_of_mem _ hm', e⟩

/-- **Quotient Source's read of a group of several definitions has one declaration per member,
at the member's key**: none generated, each declaring one member's key, and no key twice when
distinct members have distinct keys. -/
theorem block_raw_keys {ρ : Ix.LeanIngress.FiberMap}
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    {members : Array Ix.ConstantInfo} {c : Converted} (hconv : Ix.LeanIngress.convertDefinitions members = .ok c)
    (two : 2 ≤ members.size) {st : State .source} {raw : Read .source}
    (hl : Ix.LeanIngress.lower st ((c.withHints hints).quotient ρ) = .ok raw)
    (inj : ∀ j (hj : j < members.size) j' (hj' : j' < members.size),
      Ix.LeanIngress.Key.subst ρ (ingressKey members[j].getCnst.name) =
        Ix.LeanIngress.Key.subst ρ (ingressKey members[j'].getCnst.name) → j = j') :
    raw.generated = 0 ∧ (raw.decls.toList.flatMap Declaration.names).Nodup ∧
      ∀ d ∈ raw.decls.toList, ∃ (j : Nat) (_ : j < members.size),
        d.names = [Ix.LeanIngress.Key.subst ρ (ingressKey members[j].getCnst.name)] := by
  obtain ⟨ms, order, hmsize, hms, hdef, rfl⟩ := DefinitionBlockReads.convertDefinitions_block hconv two
  obtain ⟨osize, onodup, olt⟩ := SourceDeclares.defOrder_perm hdef
  have hlt : ∀ k ∈ order.toList, k < members.size := by
    intro k hk
    have := olt k (Array.mem_toList_iff.mp hk)
    simp only [DefinitionBlocks.depsOf, Array.size_map] at this
    omega
  have nameOf : ∀ k (hk : k < members.size), ms[k]!.cv.name = ingressKey members[k].getCnst.name := by
    intro k hk
    obtain ⟨s, v, t', v', -, -, -, -, -, hmk⟩ := hms k hk
    have hm := Option.some.inj ((Array.getElem?_eq_getElem (by omega)).symm.trans hmk)
    rw [getElem!_pos ms k (by omega), hm]
  obtain ⟨ys, hq, hys⟩ := quotient_names ρ hints (order.map (ms[·]!))
  rw [hq] at hl
  obtain ⟨hnames, each⟩ := lowered_names hl
  obtain ⟨-, -, plain, -⟩ := DefinitionBlockReads.lower_defs hl
  have keys : raw.decls.toList.flatMap Declaration.names =
      order.toList.map fun k => Ix.LeanIngress.Key.subst ρ ms[k]!.cv.name := by
    simp only [hnames, hys, Array.toList_map, List.map_map, Function.comp_def]
  refine ⟨plain.generated, ?_, fun d hd => ?_⟩
  · rw [keys]
    refine List.pairwise_map.mpr (List.Pairwise.imp_of_mem (fun {k k'} hk hk' ne e => ne ?_) onodup)
    rw [nameOf k (hlt k hk), nameOf k' (hlt k' hk')] at e
    exact inj k (hlt k hk) k' (hlt k' hk') e
  · obtain ⟨m, hm, hdm⟩ := each d hd
    have hmk : m.cv.name ∈ raw.decls.toList.flatMap Declaration.names := by
      rw [hnames]
      exact List.mem_map_of_mem hm
    rw [keys] at hmk
    obtain ⟨k, hk, e⟩ := List.mem_map.mp hmk
    rw [nameOf k (hlt k hk)] at e
    exact ⟨k, hlt k hk, by rw [hdm, ← e]⟩

/-! ## A block of several definitions, kept or dropped whole -/

section Collapse

variable {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env}
  {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}

/-- **The collapse keeps a block of several definitions whole or drops it whole**
(`TraceSegments.BlockNeeds.collapse`), for a lowered item of quotient Source's trace. A member's
key that an earlier read declares is a name of an earlier group published where the member is
(`ClosureLayout.lowered_keys`, `addr_of_qkey`); that group has a name where every member is
(`earlier_block`), whose keys its read declares (`ClosureLayout.lowered_declares`, `Steps`). So
either every member's key is declared before the block's read, and the read keeps nothing, or
none is, and it keeps every declaration (`collapseRead_whole_or_none`), one per member with
distinct keys (`block_raw_keys`). -/
theorem block_collapse (P : Premises env roots sub ixe failures t envQ)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    (scheduled : ∀ x ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList,
      ∃ conv, x.1.2 = .ok conv)
    {start : State .source} {ls : List Scheduled} {rs : List (Read .source)}
    (steps : Steps (quotientGraph ixe t hints sub) start ls rs)
    (inTrace : ∀ y ∈ ls, y ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList)
    {ℓ : Nat} {y : Scheduled} {members : Array Ix.ConstantInfo} {c : Converted} {stS : State .source}
    {raw rd : Read .source}
    (low : LoweredAt (quotientGraph ixe t hints sub) (fibers ixe t) hints start ls rs ℓ y (.definitions members) c
      stS raw rd)
    (two : 2 ≤ members.size) :
    rd = raw ∨ rd = { raw with decls := #[], generated := 0 } := by
  obtain ⟨hy, hr, hgr, hconv, hc, hst, hl, s, s', dropped, hcol⟩ := low
  obtain ⟨hlen, stepsAt⟩ := steps
  obtain ⟨conv, raw', -, -, -, -, -, hc', hl', -, -, declared, keptFresh⟩ := stepsAt ℓ y rd hy hr
  rw [hc] at hc'
  cases hc'
  rw [← hst, hl] at hl'
  cases hl'
  have hconv' : Ix.LeanIngress.convertDefinitions members = .ok c := hconv
  -- each member is a closure name, published apart from the others
  have insub : ∀ j (hj : j < members.size), ∃ ci, (members[j].getCnst.name, ci) ∈ sub.consts.toList :=
    fun j hj => ClosureLayout.converted_names_stored P hgr hconv _
      ((TraceSegments.definitions_names members _).mpr ⟨j, hj, rfl⟩)
  obtain ⟨B, cB, ms, -, -, -, -, apart⟩ := members_at P scheduled hgr hconv two
  have inj : ∀ j (hj : j < members.size) j' (hj' : j' < members.size),
      Ix.LeanIngress.Key.subst (fibers ixe t) (ingressKey members[j].getCnst.name) =
        Ix.LeanIngress.Key.subst (fibers ixe t) (ingressKey members[j'].getCnst.name) → j = j' :=
    fun j hj j' hj' e => apart j hj j' hj' (addr_of_qkey P (insub j hj).choose_spec (insub j' hj').choose_spec e)
  obtain ⟨hgen, distinct, keys⟩ := block_raw_keys hconv' two hl inj
  -- a member's key declared before the read: every member's is
  let E : SKey → Prop := fun k => ∃ d' ∈ (rs.take ℓ).flatMap (·.decls.toList), k ∈ d'.names
  have closed : ∀ a (ha : a < members.size), E (qkey (fibers ixe t) members[a].getCnst.name) →
      ∀ b (hb : b < members.size), E (qkey (fibers ixe t) members[b].getCnst.name) := by
    rintro a ha ⟨d'', hd'', hk''⟩ b hb
    obtain ⟨r₀, hr₀, hdr₀⟩ := List.mem_flatMap.mp hd''
    obtain ⟨j, hj, hjr⟩ := List.mem_iff_getElem.mp hr₀
    have hjℓ : j < ℓ := by simp at hj; omega
    have hℓ : ℓ < rs.length := (List.getElem?_eq_some_iff.mp hr).1
    have hrj : rs[j]? = some r₀ := by
      rw [← hjr, List.getElem_take]
      exact List.getElem?_eq_getElem _
    obtain ⟨y', hy'⟩ : ∃ y', ls[j]? = some y' := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨conv', raw'', _, _, _, _, _, hc'', hl'', hcol'', -, declared'', -⟩ := stepsAt j y' r₀ hy' hrj
    have hy'x := inTrace y' (List.mem_of_getElem? hy')
    have hdraw := (SourcePrelude.collapseRead_facts hcol'').2.2.2.1 d'' hdr₀
    obtain ⟨n₀, hn₀, hkey⟩ := ClosureLayout.lowered_keys hy'x hc'' hl'' d'' hdraw _ hk''
      (ClosureLayout.qkey_not_aux _)
    obtain ⟨gr', c', hgr', hcv', -⟩ := ClosureLayout.scheduled_conversion hy'x hc''
    have hnm' : namesAt (quotientGraph ixe t hints sub) y' = gr'.names := by
      unfold namesAt
      rw [ClosureLayout.getElem!_of_getElem? hgr']
    rw [hnm'] at hn₀
    obtain ⟨ci₀, hci₀⟩ := ClosureLayout.converted_names_stored P hgr' hcv' n₀ hn₀
    have same := addr_of_qkey P hci₀ (insub a ha).choose_spec hkey.symm
    obtain ⟨n₁, hn₁, same₁⟩ := earlier_block P scheduled hgr hconv two hgr' hcv' hn₀ ha same b hb
    obtain ⟨ci₁, hci₁⟩ := ClosureLayout.converted_names_stored P hgr' hcv' n₁ hn₁
    have hq := qkey_of_addr P hci₁ (insub b hb).choose_spec same₁
    obtain ⟨d₁, hd₁, hkd₁⟩ := ClosureLayout.lowered_declares hy'x hc'' hl'' n₁ (hnm' ▸ hn₁)
    obtain ⟨d₂, hd₂, hkd₂⟩ := declared'' d₁ hd₁ _ hkd₁
    refine ⟨d₂, ?_, by rw [← hq]; exact hkd₂⟩
    obtain ⟨r₂, hr₂, hdr₂⟩ := List.mem_flatMap.mp hd₂
    have htk : rs.take (j + 1) = (rs.take ℓ).take (j + 1) := by rw [List.take_take]; congr 1; omega
    rw [htk] at hr₂
    exact List.mem_flatMap.mpr ⟨r₂, List.mem_of_mem_take hr₂, hdr₂⟩
  refine collapseRead_whole_or_none hcol hgen distinct (fun d hd => ?_) E (fun d hd k hk => ?_)
    (fun d hd k hk ⟨d', hd', hk'⟩ => keptFresh d hd k hk d' hd' hk') (fun d hd k hk e d' hd' k' hk' => ?_)
  · obtain ⟨j, _, hj⟩ := keys d hd
    rw [hj]
    exact List.cons_ne_nil _ _
  · -- a key of the read is declared by the reads up to it
    obtain ⟨d', hd', hk'⟩ := declared d hd k hk
    have htake : rs.take (ℓ + 1) = rs.take ℓ ++ [rd] := by
      simp [List.take_add_one, hr]
    rw [htake, List.flatMap_append, List.mem_append] at hd'
    rcases hd' with hd' | hd'
    · exact .inl ⟨d', hd', hk'⟩
    · exact .inr ⟨d', by simpa using hd', hk'⟩
  · obtain ⟨j, hj, hjn⟩ := keys d hd
    obtain ⟨j', hj', hjn'⟩ := keys d' hd'
    rw [hjn, List.mem_singleton] at hk
    rw [hjn', List.mem_singleton] at hk'
    subst hk hk'
    exact closed j hj e j' hj'

/--
info: 'Ix.Cert.BlockCollapse.block_collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms block_collapse

end Collapse

end Ix.Cert.BlockCollapse
