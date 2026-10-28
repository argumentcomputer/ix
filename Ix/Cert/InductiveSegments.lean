import Ix.Cert.DefinitionSegments
import Ix.Cert.InductiveCompile
import Ix.Cert.SourceOriginRead

/-! # An inductive group's segment of the closure order

Quotient Source lowers an inductive group (its types, constructors and recursors) to one read. The
compile builds two records for it: the inductive block in Lean's order, with a projection record
per type and per constructor, and the recursor family, a lone recursor record or a block of
recursors with a projection record each. The segment `ClosureLayout` cuts for the group holds the
inductive block's record, which reads as the Source read renamed, among records read to nothing:
the projections and the recursor family's record.

* `mutual_rows`, `inductive_rows`, `recursor_rows`: the compile's rows of a block.
* `inductive_published`, `recursor_published`: the artifact publishes each type and constructor at
  its projection of the inductive block, and each recursor at a record of the family that
  resolves to its position.
* `published_key`: the closure's context keys the reference a published closure name's record
  resolves to as the name's quotient key renamed.
* `closure_inductive_reads`: `InductiveCompile.compiled_inductive_unit_reads` in the closure's
  context, with the blocks' compile-side contexts `BlockContext.blockCtx` and the names
  `DefinitionSegments.ownNames`.
* `inductive_scoped`: quotient Source's read of an inductive group lies in the scope.
* `inductive_segment`: the group's segment reads as quotient Source's read, kept whole. -/

namespace Ix.Cert.InductiveSegments

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState
open Ix.Cert.ClosureSegments (SegmentReads InertAddrs InertAt)
open Ix.Cert.BlockContext (blockCtx BoundResolve)
open Ix.Cert.DefinitionSegments (ownNames own_external own_agree)
open Ix.Cert.InductiveCompile (indsOf)
open Ix.LeanIngress (evAddr QRepAt roleAtMap fiberAliasAt ingressKey)

variable {ixe : Ixon.Env} {order : List Address}

/-! ## What a projection record resolves to -/

theorem resolveSource_iPrj {s : Store} {a : Address} {c : Ixon.Constant} {p : Ixon.InductiveProj}
    (hi : c.info = .iPrj p) {q : ConstRef Address} (h : resolveSource s a c = some q) :
    q = .member p.block p.idx.toNat := by
  unfold resolveSource at h
  rw [hi] at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨blk, -, h⟩ := Option.bind_eq_some_iff.mp h
  cases hb : blk.info with
  | muts ms =>
    simp only [hb] at h
    obtain ⟨y, -, h⟩ := Option.bind_eq_some_iff.mp h
    cases y with
    | indc _ => cases h; rfl
    | defn _ => cases h
    | recr _ => cases h
  | _ => simp [hb] at h

theorem resolveSource_rPrj {s : Store} {a : Address} {c : Ixon.Constant} {p : Ixon.RecursorProj}
    (hi : c.info = .rPrj p) {q : ConstRef Address} (h : resolveSource s a c = some q) :
    q = .member p.block p.idx.toNat := by
  unfold resolveSource at h
  rw [hi] at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨blk, -, h⟩ := Option.bind_eq_some_iff.mp h
  cases hb : blk.info with
  | muts ms =>
    simp only [hb] at h
    obtain ⟨y, -, h⟩ := Option.bind_eq_some_iff.mp h
    cases y with
    | recr _ => cases h; rfl
    | defn _ => cases h
    | indc _ => cases h
  | _ => simp [hb] at h

theorem resolveSource_cPrj {s : Store} {a : Address} {c : Ixon.Constant} {p : Ixon.ConstructorProj}
    (hi : c.info = .cPrj p) {q : ConstRef Address} (h : resolveSource s a c = some q) :
    q = .ctor p.block p.idx.toNat p.cidx.toNat := by
  unfold resolveSource at h
  rw [hi] at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨blk, -, h⟩ := Option.bind_eq_some_iff.mp h
  cases hb : blk.info with
  | muts ms =>
    simp only [hb] at h
    obtain ⟨y, -, h⟩ := Option.bind_eq_some_iff.mp h
    cases y with
    | indc _ =>
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      rfl
    | defn _ => cases h
    | recr _ => cases h
  | _ => simp [hb] at h

/-- A record whose block is `B` makes `B` a record of a closure order holding the record. -/
theorem owner_in_order {S : Address → Prop} (corder : ClosureOrder ixe S order) {a : Address} {c : Ixon.Constant}
    (ha : a ∈ order) (hc : recordAt ixe a = some c) {B : Address} (hown : ownerOf a c = B) : B ∈ order := by
  by_cases e : B = a
  · rw [e]
    exact ha
  · exact (corder.complete _).mpr (.step ((corder.complete a).mp ha) ⟨c, hc, .inl ⟨hown, e⟩⟩)

/-! ## The compile's rows -/

/-- **A mutual block's rows**: one per class member and constructor, at its projection of the
block (`expectedRows`); or, when the block is a lone definition or recursor, every member at the
block itself. -/
theorem mutual_rows {context : CompileEnv × BlockEnv} {before after : BlockState} {output : BlockResult}
    (classes : List (List MutConst)) (nonempty : ∀ members ∈ classes, members ≠ [])
    (ran : rawRun (compileMutualBlock classes) context before = (.ok output, after)) :
    ∃ payloads : Array Ixon.MutConst, payloads.size = classes.length ∧ payloads.size < UInt64.size ∧
      payloads.toList.map ProjectionLayout.memberShape =
        (classes.filterMap List.head?).map ProjectionLayout.sourceShape ∧
      ((standaloneMutConstInfo? payloads = none ∧
          MutualProjections.logicalRows output.projections =
            MutualProjections.expectedRows output.blockAddr classes) ∨
        (standaloneMutConstInfo? payloads ≠ none ∧
          MutualProjections.logicalRows output.projections = classes.flatten.map fun s => (s.name, output.block))) := by
  unfold compileMutualBlock at ran
  dsimp only at ran
  unfold withMutCtx at ran
  rw [rawRun_withBlockEnv] at ran
  obtain ⟨_, _, -, compiled⟩ := bind_ok ran
  unfold compileMutualPayload at compiled
  obtain ⟨payload, middle, payloadRan, finished⟩ := bind_ok compiled
  have count := ProjectionLayout.payload_count _ nonempty _ _ _ _ payloadRan
  have shapes := ProjectionLayout.payload_shapes classes _ _ _ _ payloadRan
  obtain ⟨members, roots, metadata⟩ := payload
  dsimp only at finished count shapes
  obtain ⟨-, header, built⟩ := ProjectionLayout.finish_mutual_ok _ _ _ _ finished
  refine ⟨members, count, header.1, shapes, ?_⟩
  unfold buildCompiledMutualBlock at built
  cases hs : standaloneMutConstInfo? members with
  | none =>
    rw [hs] at built
    obtain ⟨block, -, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok built
    cases Except.ok.inj returned
    refine .inl ⟨rfl, ?_⟩
    dsimp only [BlockResult.mk']
    exact MutualProjections.build_rows _ _ _
  | some info =>
    rw [hs] at built
    obtain ⟨block, -, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok built
    cases Except.ok.inj returned
    refine .inr ⟨by simp, ?_⟩
    dsimp only [BlockResult.mk']
    exact MutualProjections.standalone_rows _ _ _

/-- The head of each singleton class is its member. -/
theorem heads_map {α : Type} (g : α → MutConst) :
    ∀ l : List α, ((l.map g).map ([·])).filterMap List.head? = l.map g
  | [] => rfl
  | _ :: l => congrArg (List.cons _) (heads_map g l)

/-- **An inductive block's rows**: each type at its projection, each constructor at its own. -/
theorem inductive_rows {context : CompileEnv × BlockEnv} {before after : BlockState} {output : BlockResult}
    {inds : List Ix.Ind}
    (ran : rawRun (compileMutualBlock ((inds.map MutConst.indc).map ([·]))) context before = (.ok output, after)) :
    inds.length < UInt64.size ∧
      (∀ i (hi : i < inds.length), (inds[i].name,
        MutualProjections.memberProjection output.blockAddr i.toUInt64 (.indc inds[i])) ∈
          MutualProjections.logicalRows output.projections) ∧
      ∀ i (hi : i < inds.length) k (hk : k < inds[i].ctors.size), (inds[i].ctors[k].cnst.name,
        MutualProjections.constructorProjection output.blockAddr i.toUInt64 k.toUInt64) ∈
          MutualProjections.logicalRows output.projections := by
  obtain ⟨payloads, hsize, hcount, shapes, rows⟩ := mutual_rows _ (fun m hm => by
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hm
    simp) ran
  rw [heads_map] at shapes
  have hnone : standaloneMutConstInfo? payloads = none := by
    rcases payloads with ⟨_ | ⟨m, _ | ⟨m₂, rest⟩⟩⟩
    · rfl
    · cases m with
      | indc _ => rfl
      | defn _ | recr _ =>
        exfalso
        cases inds with
        | nil => simp at shapes
        | cons i rest => simp [ProjectionLayout.memberShape, ProjectionLayout.sourceShape] at shapes
    · rfl
  have hrows : MutualProjections.logicalRows output.projections =
      MutualProjections.expectedRows output.blockAddr ((inds.map MutConst.indc).map ([·])) := by
    rcases rows with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd hnone h
  simp only [List.length_map] at hsize
  refine ⟨hsize ▸ hcount, fun i hi => ?_, fun i hi k hk => ?_⟩
  · rw [hrows]
    refine List.mem_flatMap.mpr ⟨([.indc inds[i]], i), ?_, ?_⟩
    · rw [List.mem_zipIdx_iff_getElem?]
      simp [hi]
    · simp [MutualProjections.sourceRows, MutConst.name]
  · rw [hrows]
    refine List.mem_flatMap.mpr ⟨([.indc inds[i]], i), ?_, ?_⟩
    · rw [List.mem_zipIdx_iff_getElem?]
      simp [hi]
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, MutualProjections.sourceRows,
        MutConst.ctors]
      refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(inds[i].ctors[k], k), ?_, rfl⟩)
      rw [List.mem_zipIdx_iff_getElem?]
      simp [hk]

/-- **A recursor family's rows**: each recursor at its projection of the family's block, or a lone
recursor at the block itself. -/
theorem recursor_rows {context : CompileEnv × BlockEnv} {before after : BlockState} {output : BlockResult}
    {recs : List Ix.RecursorVal} (hne : recs ≠ [])
    (ran : rawRun (compileMutualBlock ((recs.map MutConst.recr).map ([·]))) context before = (.ok output, after)) :
    recs.length < UInt64.size ∧
      ((∀ j (hj : j < recs.length), (recs[j].cnst.name,
          MutualProjections.memberProjection output.blockAddr j.toUInt64 (.recr recs[j])) ∈
            MutualProjections.logicalRows output.projections) ∨
        ∃ r, recs = [r] ∧ (r.cnst.name, output.block) ∈ MutualProjections.logicalRows output.projections) := by
  obtain ⟨payloads, hsize, hcount, -, rows⟩ := mutual_rows _ (fun m hm => by
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hm
    simp) ran
  simp only [List.length_map] at hsize
  refine ⟨hsize ▸ hcount, ?_⟩
  rcases rows with ⟨-, h⟩ | ⟨hs, h⟩
  · refine .inl fun j hj => ?_
    rw [h]
    refine List.mem_flatMap.mpr ⟨([.recr recs[j]], j), ?_, ?_⟩
    · rw [List.mem_zipIdx_iff_getElem?]
      simp [hj]
    · simp [MutualProjections.sourceRows, MutConst.name, MutConst.ctors]
  · refine .inr ?_
    rcases recs with _ | ⟨r, _ | ⟨r₂, rest⟩⟩
    · exact absurd rfl hne
    · refine ⟨r, rfl, ?_⟩
      rw [h]
      simp [MutConst.name]
    · exfalso
      rcases payloads with ⟨_ | ⟨m, _ | ⟨m₂, rest'⟩⟩⟩
      · simp at hsize
      · simp at hsize
      · exact hs rfl

/-! ## The compile's publications -/

/-- **A row of a claimed block is published**: a closure name the block's rows place at a
wire-valid record is published at that record's address, which holds it. -/
theorem row_published {sub : Ix.Environment} {key : Ix.Name} {r : BlockResult}
    (pub : BlockPublication.Published ixe sub key r) {output : BlockResult}
    (hrec : BlockRecords.recordsOf r = BlockRecords.recordsOf output) {name : Ix.Name} {proj : Ixon.Constant}
    (row : (name, proj) ∈ MutualProjections.logicalRows output.projections) (wire : proj.wireWF)
    (insub : (sub.consts.get? name).isSome = true) :
    ClosureLayout.addrOf ixe name = some (Address.admissionHash (Ixon.ser proj)) ∧
      recordAt ixe (Address.admissionHash (Ixon.ser proj)) = some proj := by
  simp only [BlockRecords.recordsOf, Prod.mk.injEq] at hrec
  obtain ⟨-, -, -, hproj⟩ := hrec
  have row' : (name, proj) ∈ MutualProjections.logicalRows r.projections := by
    unfold MutualProjections.logicalRows at row ⊢
    rw [← Array.toList_map, hproj, Array.toList_map]
    exact row
  obtain ⟨ha, hb⟩ := pub.claims _ _ _ (BlockPublication.row_claim row') insub
  exact ⟨ha, BlockLayout.recordAt_ser wire hb⟩

/-- A claimed block's facts: its address is its bytes' hash, it is built, and it is wire-valid. -/
theorem claimed_block {cenvR : CompileEnv} {all : Ix.Set Ix.Name} {key : Ix.Name} {r : BlockResult}
    {cache : BlockState} (hr : runBlock cenvR all key = .ok (r, cache))
    {output : BlockResult} (hrec : BlockRecords.recordsOf r = BlockRecords.recordsOf output) :
    output.blockAddr = Address.admissionHash (Ixon.ser output.block) ∧ output.blockAddr.hash.size = 32 ∧
      BlockLayout.Built output.block ∧ output.block.wireWF := by
  have hrec' := hrec
  simp only [BlockRecords.recordsOf, Prod.mk.injEq] at hrec'
  obtain ⟨hblock, -, haddr, -⟩ := hrec'
  have shape := BlockLayout.runBlock_shape hr
  have e : output.blockAddr = Address.admissionHash (Ixon.ser output.block) := by
    rw [← haddr, ← hblock, shape.addr, shape.bytes]
  refine ⟨e, by rw [e]; exact Ixon.Authenticated.admissionHash_width _, hblock ▸ shape.built,
    hblock ▸ BlockWire.blocksWire _ _ _ _ _ hr⟩

/-- **An inductive block's publications**: each type and each constructor is published at its
projection of the block, which the artifact holds. -/
theorem inductive_published {sub : Ix.Environment} {context : CompileEnv × BlockEnv} {before after : BlockState}
    {output : BlockResult} {inds : List Ix.Ind}
    (ran : rawRun (compileMutualBlock ((inds.map MutConst.indc).map ([·]))) context before = (.ok output, after))
    {cenvR : CompileEnv} {all : Ix.Set Ix.Name} {key : Ix.Name} {r : BlockResult} {cache : BlockState}
    (hr : runBlock cenvR all key = .ok (r, cache))
    (pub : BlockPublication.Published ixe sub key r) (hrec : BlockRecords.recordsOf r = BlockRecords.recordsOf output)
    (typesIn : ∀ i (hi : i < inds.length), (sub.consts.get? inds[i].name).isSome = true)
    (ctorsIn : ∀ i (hi : i < inds.length) k (hk : k < inds[i].ctors.size),
      (sub.consts.get? inds[i].ctors[k].cnst.name).isSome = true) :
    inds.length < UInt64.size ∧
      (∀ i (hi : i < inds.length), ∃ Q, ClosureLayout.addrOf ixe inds[i].name = some Q ∧
        recordAt ixe Q = some (MutualProjections.memberProjection output.blockAddr i.toUInt64 (.indc inds[i]))) ∧
      ∀ i (hi : i < inds.length) k (hk : k < inds[i].ctors.size),
        ∃ Q, ClosureLayout.addrOf ixe inds[i].ctors[k].cnst.name = some Q ∧
          recordAt ixe Q = some (MutualProjections.constructorProjection output.blockAddr i.toUInt64 k.toUInt64) := by
  obtain ⟨count, members, ctors⟩ := inductive_rows ran
  obtain ⟨-, width, -, -⟩ := claimed_block hr hrec
  refine ⟨count, fun i hi => ?_, fun i hi k hk => ?_⟩
  · exact ⟨_, row_published pub hrec (members i hi) (MutualProjections.member_wire _ width _ _) (typesIn i hi)⟩
  · exact ⟨_, row_published pub hrec (ctors i hi k hk) (MutualProjections.constructor_wire _ width _ _)
      (ctorsIn i hi k hk)⟩

/-- **The record a closure name is published at resolves**, under `PublishedResolve`. -/
theorem published_resolves {sub : Ix.Environment} (resolves : SingletonSegments.PublishedResolve ixe sub)
    {n : Ix.Name} {ci : Ix.ConstantInfo} (hn : (n, ci) ∈ sub.consts.toList) {Q : Address}
    (haddr : ClosureLayout.addrOf ixe n = some Q) {c : Ixon.Constant} (hc : recordAt ixe Q = some c) :
    ∃ q, resolveSource (recordAt ixe) Q c = some q := by
  have hget : ∃ named, ixe.named.get? n = some named ∧ named.addr = Q := by
    unfold ClosureLayout.addrOf at haddr
    obtain ⟨named, h, e⟩ := Option.map_eq_some_iff.mp haddr
    exact ⟨named, h, e⟩
  obtain ⟨named, hget, rfl⟩ := hget
  exact Option.isSome_iff_exists.mp (resolves n ci named hn hget c hc)

/-- **A recursor family's publications**: each recursor is published at a record of the family
that resolves to its position in the family. -/
theorem recursor_published {sub : Ix.Environment} (resolves : SingletonSegments.PublishedResolve ixe sub)
    {context : CompileEnv × BlockEnv} {before after : BlockState} {output : BlockResult}
    {recs : List Ix.RecursorVal} (hne : recs ≠ [])
    (ran : rawRun (compileMutualBlock ((recs.map MutConst.recr).map ([·]))) context before = (.ok output, after))
    {cenvR : CompileEnv} {all : Ix.Set Ix.Name} {key : Ix.Name} {r : BlockResult} {cache : BlockState}
    (hr : runBlock cenvR all key = .ok (r, cache))
    (pub : BlockPublication.Published ixe sub key r) (hrec : BlockRecords.recordsOf r = BlockRecords.recordsOf output)
    (recsIn : ∀ j (hj : j < recs.length), ∃ ci, (recs[j].cnst.name, ci) ∈ sub.consts.toList) :
    ∀ j (hj : j < recs.length), ∃ Q c, ClosureLayout.addrOf ixe recs[j].cnst.name = some Q ∧
      recordAt ixe Q = some c ∧ resolveSource (recordAt ixe) Q c = some (.member output.blockAddr j) ∧
        ownerOf Q c = output.blockAddr := by
  intro j hj
  obtain ⟨ci, hci⟩ := recsIn j hj
  have insub : (sub.consts.get? recs[j].cnst.name).isSome = true := by
    rw [SourceStoredNames.stored_get hci]
    rfl
  obtain ⟨hblock, width, built, wire⟩ := claimed_block hr hrec
  obtain ⟨count, rows⟩ := recursor_rows hne ran
  rcases rows with rows | ⟨r₀, hr₀, row⟩
  · obtain ⟨ha, hc⟩ := row_published pub hrec (rows j hj) (MutualProjections.member_wire _ width _ _) insub
    obtain ⟨q, hq⟩ := published_resolves resolves hci ha hc
    have e := resolveSource_rPrj rfl hq
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans hj count)] at e
    subst e
    exact ⟨_, _, ha, hc, hq, rfl⟩
  · subst hr₀
    have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    obtain ⟨ha, hc⟩ := row_published pub hrec row wire insub
    rw [← hblock] at ha hc
    obtain ⟨q, hq⟩ := published_resolves resolves hci ha hc
    have single := SingletonReads.lone_of built (fun ms e => by simp [resolveSource, e] at hq)
    have hval : resolveSource (recordAt ixe) output.blockAddr output.block = some (.member output.blockAddr 0) := by
      cases hi : output.block.info <;> simp_all [BlockContext.lone, resolveSource]
    exact ⟨_, _, ha, hc, hval, built.owner _⟩

/-! ## The closure's keys at published names -/

/-- **The closure's context keys the reference a published closure name's record resolves to** as
the name's quotient key renamed; the record is in the closure order. -/
theorem published_key {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {failures : Failures} {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ)
    {preA : Prelude .anon} (prelude : preludeFor t = .ok preA) (corder : ClosureOrder ixe (Seed ixe sub) order)
    (canonical : Stream.StoredCanonical ixe order) (b : Ix.RoleEvidence.Bundle) {n : Ix.Name} {ci : Ix.ConstantInfo}
    (hn : (n, ci) ∈ sub.consts.toList) {Q : Address} (haddr : ClosureLayout.addrOf ixe n = some Q)
    {c : Ixon.Constant} (hc : recordAt ixe Q = some c) {q : ConstRef Address}
    (hq : resolveSource (recordAt ixe) Q c = some q) :
    Q ∈ order ∧ (closureContext ixe t preA order).memberKey q = .ok ((quotientKey ixe t n).map (evAddr ixe b)) := by
  obtain ⟨named, hmem, hget⟩ := SourceStoredNames.stored_published P hn
  have hQ : named.addr = Q := by
    unfold ClosureLayout.addrOf at haddr
    rw [hget] at haddr
    exact Option.some.inj haddr
  have ha : Q ∈ order := (corder.complete _).mpr
    (.seed ⟨n, ci, named, SourceStoredNames.stored_get hn, hget, hQ⟩ (ClosureLayout.recordAt_contains hc))
  refine ⟨ha, ?_⟩
  rw [DefinitionSegments.closure_memberKey_at P prelude corder canonical ha hc hq, ← hQ]
  exact ClosureKeying.closure_keyAt P prelude canonical b hmem
    (by rw [hQ]; exact BlockContext.closure_resolve corder ha hc hq)

/-! ## Records read to nothing -/

theorem recrs_of : ∀ l : List Ixon.MutConst, (∀ x ∈ l, ∃ r, x = .recr r) →
    ∃ rs : List Ixon.Recursor, l = rs.map Ixon.MutConst.recr
  | [], _ => ⟨[], rfl⟩
  | x :: l, h => by
    obtain ⟨r, rfl⟩ := h x List.mem_cons_self
    obtain ⟨rs, rfl⟩ := recrs_of l fun y hy => h y (List.mem_cons_of_mem _ hy)
    exact ⟨r :: rs, rfl⟩

/-- **A recursor family's record** is a lone recursor or a block of the family's recursors. -/
theorem recursor_info {context : CompileEnv × BlockEnv} {before after : BlockState} {output : BlockResult}
    {recs : List Ix.RecursorVal}
    (ran : rawRun (compileMutualBlock ((recs.map MutConst.recr).map ([·]))) context before = (.ok output, after)) :
    (∃ r, output.block.info = .recr r) ∨
      ∃ rs : List Ixon.Recursor, output.block.info = .muts (rs.map Ixon.MutConst.recr).toArray ∧
        rs.length = recs.length := by
  have shape := ProjectionLayout.mutual_block_shape _ context before output after ran
  rw [heads_map] at shape
  cases hi : output.block.info with
  | recr r => exact .inl ⟨r, rfl⟩
  | muts ms =>
    rw [hi] at shape
    simp only [ProjectionLayout.blockShape, Option.some.injEq] at shape
    have each : ∀ x ∈ ms.toList, ∃ r, x = .recr r := by
      intro x hx
      have hx' : ProjectionLayout.memberShape x ∈ ms.toList.map ProjectionLayout.memberShape :=
        List.mem_map_of_mem hx
      rw [shape] at hx'
      obtain ⟨a, ha, h⟩ := List.mem_map.mp hx'
      obtain ⟨r', -, rfl⟩ := List.mem_map.mp ha
      cases x with
      | recr r => exact ⟨r, rfl⟩
      | defn _ => simp [ProjectionLayout.memberShape, ProjectionLayout.sourceShape] at h
      | indc _ => simp [ProjectionLayout.memberShape, ProjectionLayout.sourceShape] at h
    obtain ⟨rs, hrs⟩ := recrs_of _ each
    refine .inr ⟨rs, by rw [← hrs, Array.toArray_toList], ?_⟩
    have := congrArg List.length shape
    rw [hrs] at this
    simpa using this
  | defn _ =>
    exfalso
    rw [hi] at shape
    cases recs with
    | nil => simp [ProjectionLayout.blockShape] at shape
    | cons r rest => simp [ProjectionLayout.blockShape, ProjectionLayout.sourceShape] at shape
  | axio _ | quot _ | dPrj _ | iPrj _ | rPrj _ | cPrj _ =>
    rw [hi] at shape
    simp [ProjectionLayout.blockShape] at shape

/-- **A recursor family's record reads to nothing** where the context's recursor index holds every
recursor of the family. -/
theorem recursor_inert {cx : Ctx .anon} {owner : Address} {c : Ixon.Constant} {n : Nat}
    (info : (∃ r, c.info = .recr r) ∨ ∃ rs : List Ixon.Recursor, c.info = .muts (rs.map Ixon.MutConst.recr).toArray ∧
      rs.length = n) (hn : 0 < n)
    (indexed : ∀ j < n, cx.index.recs.contains (.member owner j) = true) : InertAt cx owner c := by
  intro stA
  rcases info with ⟨r, hr⟩ | ⟨rs, hrs, hlen⟩
  · exact ⟨{}, InductiveUnits.recr_inert cx stA owner c hr (indexed 0 hn), InductiveUnits.inert_empty⟩
  · exact ⟨{}, InductiveUnits.recrs_inert cx stA owner c rs hrs (fun j hj => indexed j (hlen ▸ hj)),
      InductiveUnits.inert_empty⟩

/-- **A projection record a closure name is published at reads to nothing** in the closure's
context, under `PublishedResolve`. -/
theorem published_inert {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {failures : Failures} {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ)
    {preA : Prelude .anon} (corder : ClosureOrder ixe (Seed ixe sub) order)
    (resolves : SingletonSegments.PublishedResolve ixe sub) {n : Ix.Name} {ci : Ix.ConstantInfo}
    (hn : (n, ci) ∈ sub.consts.toList) {a : Address} (haddr : ClosureLayout.addrOf ixe n = some a)
    {c : Ixon.Constant} (hc : recordAt ixe a = some c)
    (hproj : (∃ p, c.info = .dPrj p) ∨ (∃ p, c.info = .iPrj p) ∨ (∃ p, c.info = .rPrj p) ∨ ∃ p, c.info = .cPrj p) :
    InertAt (closureContext ixe t preA order) a c := by
  obtain ⟨named, -, hget⟩ := SourceStoredNames.stored_published P hn
  have ha' : named.addr = a := by
    unfold ClosureLayout.addrOf at haddr
    rw [hget] at haddr
    exact Option.some.inj haddr
  have ha : a ∈ order := (corder.complete _).mpr
    (.seed ⟨n, ci, named, SourceStoredNames.stored_get hn, hget, ha'⟩ (ClosureLayout.recordAt_contains hc))
  obtain ⟨q, hq⟩ := published_resolves resolves hn haddr hc
  have hres := BlockContext.closure_resolve (t := t) (preA := preA) corder ha hc hq
  have hstore := ClosureKeying.closure_store (t := t) (preA := preA) corder.nodup ha hc
  have h2 : resolveSource (closureContext ixe t preA order).store a c = some q := by
    have h := hres
    unfold resolve at h
    rw [hstore] at h
    exact h
  exact ClosureSegments.projection_inert _ _ _ hproj (by rw [h2]; rfl)

/-! ## Quotient Source's read of an inductive group -/

theorem good_of_base {md : Mode} {P : KeyScope md} : ∀ {k : Key md}, k.base.Good P → k.Good P
  | .aux k _, h => good_of_base (k := k) h
  | .id _, h => h
  | .role _, h => h

/-- **Quotient Source's read of an inductive group lies in the scope** of a good block: it declares
no basis block, its declarations' names are the block's names and auxiliary names over them, and
its blocks' names and its owners' type formers are the block's. -/
theorem inductive_scoped {P : KeyScope .source} {st : State .source} {rb : BlockRead .source}
    {r : Read .source} (hg : rb.Good P) (lowered : Ix.LeanIngress.lower st (.inductive rb) = .ok r) :
    StreamUnits.ReadScoped P r := by
  have lowS : lowerInductive st rb = .ok r := lowered
  obtain ⟨gens, hd, hgen, hblocks, -⟩ := CtxAgree.lowerInductive_ok lowS
  have named : ∀ k ∈ CtxAgree.blockNames rb, k.Good P := by
    intro k hk
    rw [SourceOriginRead.blockNames_eq] at hk
    rcases List.mem_append.mp hk with hk | hk
    · rcases List.mem_append.mp hk with hk | hk
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
        exact (hg.1 x hx).1
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
        exact (hg.2.1 x hx).1
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
      exact (hg.2.2.2 x hx).1.1
  refine ⟨SourcePrelude.lower_noBasis st _ r lowered, fun d hd' e he => ?_, fun x hx => ?_, fun o ho => ?_⟩
  · have hd'' : d ∈ gens ∨ d = CtxAgree.indDeclOf rb := by
      rw [hd] at hd'
      simpa using hd'
    rcases hd'' with hd'' | rfl
    · -- a generated declaration: its names are auxiliary names over the block's
      have hgenE : e ∈ CtxAgree.genEntries r := by
        simp only [CtxAgree.genEntries, hd, hgen, Array.toList_push, List.take_left]
        exact List.mem_flatMap.mpr ⟨d, hd'', he⟩
      obtain ⟨k, hk, hbase⟩ := List.mem_map.mp (SourceOriginRead.lowerInductive_bases lowS e hgenE)
      exact good_of_base (hbase ▸ CtxAgree.Key.good_base (named k hk))
    · exact named _ (by unfold CtxAgree.blockNames; exact List.mem_map_of_mem he)
  · rw [hblocks] at hx
    unfold CtxAgree.blocksOf at hx
    obtain ⟨ty, hty, rfl⟩ := List.mem_map.mp hx
    exact ((CtxAgree.blockRecOf_good hg).1 ty hty).1.1
  · exact (CtxAgree.lowerInductive_owners_good hg lowS o ho).1

/-- **A segment that holds a partner record among records read to nothing reads as its Source
read**, when the read is kept whole and lies in the scope. -/
theorem kept_segment {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md} {cx : Ctx md'}
    {stS : State md} {raw rd : Read md} {B : Address} {c : Ixon.Constant} {seg : List Address}
    (inScope : StreamUnits.ReadScoped P raw) (kept : rd = raw) (hc : recordAt ixe B = some c)
    (reads : ∀ stA : State md', StreamRename.StateRen f P stS stA →
      ∃ rA, readRecord cx stA B c = .ok rA ∧ StreamUnits.ReadRen f raw rA)
    (place : ∃ before after, seg = before ++ B :: after ∧ InertAddrs ixe cx before ∧ InertAddrs ixe cx after) :
    SegmentReads f P cx ixe stS rd seg := by
  subst kept
  obtain ⟨before, after, hseg, hb, ha⟩ := place
  exact .inr ⟨before, B, after, c, hseg, hc, inScope, reads, hb, ha⟩

/-! ## The inductive group's reading in the closure's context -/

/-- **An inductive group compiled in Lean's order reads in the closure's context, from every state
related to quotient Source's, as quotient Source's unit renamed.** The two compile-side contexts
are the blocks' (`blockCtx`) over the compiles' blobs, their names `ownNames`; the types',
constructors' and recursors' keys come from their published records (`inductive_published`,
`recursor_published`). The closure's recursor index entries for the block (`hindexed`, `hshape`,
`hrecs`, `entries`) stay premises. -/
theorem closure_inductive_reads {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {failures : Failures} {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ)
    {preA : Prelude .anon} (prelude : preludeFor t = .ok preA) (corder : ClosureOrder ixe (Seed ixe sub) order)
    (canonical : Stream.StoredCanonical ixe order) {b : Ix.RoleEvidence.Bundle}
    (hf : InjOn (evAddr ixe b) (QRepAt ixe (roleAtMap t))) (resolves : SingletonSegments.PublishedResolve ixe sub)
    {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal}
    {conv : Ix.LeanIngress.Converted} (src : Ix.LeanIngress.convertInductive types ctors recs = .ok conv)
    {first : Ix.InductiveVal} (hfirst : types[0]? = some first) (hcsize : ctors.size = types.size)
    (lpsEq : ∀ v ∈ types.toList, v.cnst.levelParams = first.cnst.levelParams)
    (ctorLps : ∀ cs ∈ ctors.toList, ∀ c ∈ cs.toList, c.cnst.levelParams = first.cnst.levelParams)
    (nodup : first.cnst.levelParams.toList.Nodup)
    (positions : ∀ i (hi : i < ctors.size) j (hj : j < ctors[i].size), ctors[i][j].cidx = j)
    {rlps : Array Ix.Name} (recLpsEq : ∀ r ∈ recs.toList, r.cnst.levelParams = rlps)
    (recNodup : rlps.toList.Nodup) (hrne : recs.toList ≠ [])
    (distinct : Canon.KeysDistinct ((indsOf types ctors).map MutConst.indc))
    (noCtor : ∀ i ∈ indsOf types ctors, ∀ e ∈ BlockEmission.memberSources (.indc i),
      ConstsSatisfy (fun n => ∀ i' ∈ indsOf types ctors, ∀ c ∈ i'.ctors.toList, n ≠ c.cnst.name) e)
    (recDistinct : Canon.KeysDistinct (recs.toList.map MutConst.recr))
    (typesIn : ∀ i (hi : i < types.size), ∃ ci, (types[i].cnst.name, ci) ∈ sub.consts.toList)
    (ctorsIn : ∀ i (hi : i < ctors.size) k (hk : k < ctors[i].size), ∃ ci, (ctors[i][k].cnst.name, ci) ∈ sub.consts.toList)
    (recsIn : ∀ j (hj : j < recs.size), ∃ ci, (recs[j].cnst.name, ci) ∈ sub.consts.toList)
    -- the inductive block
    {cenv₁ : CompileEnv} {benv₁ : BlockEnv} {out₁ : BlockResult} {after₁ : BlockState}
    (ran₁ : rawRun (compileMutualBlock (((indsOf types ctors).map MutConst.indc).map ([·]))) (cenv₁, benv₁) {} =
      (.ok out₁, after₁))
    {cenvR₁ : CompileEnv} {all₁ : Ix.Set Ix.Name} {key₁ : Ix.Name} {r₁ : BlockResult} {cache₁ : BlockState}
    (hr₁ : runBlock cenvR₁ all₁ key₁ = .ok (r₁, cache₁))
    (pub₁ : BlockPublication.Published ixe sub key₁ r₁) (hrec₁ : BlockRecords.recordsOf r₁ = BlockRecords.recordsOf out₁)
    (bound₁ : BoundResolve ixe cenv₁)
    (blobs₁ : ∀ a bytes, BlobWrites.readBlob cenv₁.blobs after₁ a = some bytes → ixe.blobs.get? a = some bytes)
    (published₁ : ∀ m a, (∃ i ∈ indsOf types ctors, ∃ e ∈ BlockEmission.memberSources (.indc i), GraphWalk.Refs m e) →
      lookupBinding cenv₁ {} m = some a →
        ∃ named', (m, named') ∈ ixe.named.toList ∧ named'.addr = a ∧ (sub.consts.get? m).isSome = true)
    -- the recursor family
    {cenv₂ : CompileEnv} {benv₂ : BlockEnv} {out₂ : BlockResult} {after₂ : BlockState}
    (ran₂ : rawRun (compileMutualBlock ((recs.toList.map MutConst.recr).map ([·]))) (cenv₂, benv₂) {} =
      (.ok out₂, after₂))
    {cenvR₂ : CompileEnv} {all₂ : Ix.Set Ix.Name} {key₂ : Ix.Name} {r₂ : BlockResult} {cache₂ : BlockState}
    (hr₂ : runBlock cenvR₂ all₂ key₂ = .ok (r₂, cache₂))
    (pub₂ : BlockPublication.Published ixe sub key₂ r₂) (hrec₂ : BlockRecords.recordsOf r₂ = BlockRecords.recordsOf out₂)
    (bound₂ : BoundResolve ixe cenv₂)
    (blobs₂ : ∀ a bytes, BlobWrites.readBlob cenv₂.blobs after₂ a = some bytes → ixe.blobs.get? a = some bytes)
    (published₂ : ∀ m a, (∃ r ∈ recs.toList, ∃ e ∈ BlockEmission.memberSources (.recr r), GraphWalk.Refs m e) →
      lookupBinding cenv₂ {} m = some a →
        ∃ named', (m, named') ∈ ixe.named.toList ∧ named'.addr = a ∧ (sub.consts.get? m).isSome = true)
    -- the closure's recursor index at the block
    {shape : BlockShape} (hindexed : (closureContext ixe t preA order).index.blocks[out₁.blockAddr]? = some shape)
    (hshape : shape.order = (List.range types.size).toArray)
    (hrecs : shape.recs.toList = (List.range recs.size).map fun j => ConstRef.member out₂.blockAddr j)
    (entries : ∀ j (hj : j < recs.size), ∃ entry mi, ∃ hmi : mi < types.size,
      (closureContext ixe t preA order).index.recs[ConstRef.member out₂.blockAddr j]? = some entry ∧
      recLps entry.large (List.range first.cnst.levelParams.size) = (SourceConversion.recNum first recs[j]).params ∧
      entry.major = .member out₁.blockAddr mi ∧ recs[j].rules.size = (ctors[mi]'(hcsize ▸ hmi)).size ∧
      (∀ k (hk : k < recs[j].rules.size),
        (closureContext ixe t preA order).memberKey (.ctor out₁.blockAddr mi k) =
          .ok (InductiveUnits.srcKey (fiberAliasAt ixe (roleAtMap t)) (evAddr ixe b) recs[j].rules[k].ctor)) ∧
      (CtxAgree.numNestedOf (InductiveUnits.srcBlock types ctors recs first) = 0 →
        some entry.motive = SourceConversion.motiveOf types recs[j]))
    -- quotient Source's side
    (good : ∀ rb, conv.quotient (fiberAliasAt ixe (roleAtMap t)) = .inductive rb →
      rb.Good (KeyScope.ofId (QRepAt ixe (roleAtMap t))))
    {stS : State .source}
    (typesGood : ∀ k : Key .source, k.Good (KeyScope.ofId (QRepAt ixe (roleAtMap t))) → ∀ p,
      stS.constTypes[k]? = some p → p.2.Good (KeyScope.ofId (QRepAt ixe (roleAtMap t))))
    (blocksGood : ∀ k : Key .source, k.Good (KeyScope.ofId (QRepAt ixe (roleAtMap t))) → ∀ bk,
      stS.indBlocks[k]? = some bk → bk.Good (KeyScope.ofId (QRepAt ixe (roleAtMap t))))
    {rS : Read .source}
    (lowered : Ix.LeanIngress.lower stS (conv.quotient (fiberAliasAt ixe (roleAtMap t))) = .ok rS) :
    out₁.blockAddr ∈ order ∧ recordAt ixe out₁.blockAddr = some out₁.block ∧
      out₂.blockAddr ∈ order ∧ recordAt ixe out₂.blockAddr = some out₂.block ∧
      InertAt (closureContext ixe t preA order) out₂.blockAddr out₂.block ∧
      StreamUnits.ReadScoped (KeyScope.ofId (QRepAt ixe (roleAtMap t))) rS ∧
      ∀ stA : State .anon, StreamRename.StateRen (evAddr ixe b) (KeyScope.ofId (QRepAt ixe (roleAtMap t))) stS stA →
        ∃ rA, readRecord (closureContext ixe t preA order) stA out₁.blockAddr out₁.block = .ok rA ∧
          StreamUnits.ReadRen (evAddr ixe b) rS rA := by
  have hlenI := InductiveCompile.indsOf_length hcsize
  -- the types and constructors are published at their projections
  have typesIn' : ∀ i (hi : i < (indsOf types ctors).length),
      (sub.consts.get? (indsOf types ctors)[i].name).isSome = true := by
    intro i hi
    obtain ⟨ci, hci⟩ := typesIn i (by omega)
    have e : (indsOf types ctors)[i].name = types[i].cnst.name := by simp [indsOf, InductiveCompile.indOf]
    rw [e, SourceStoredNames.stored_get hci]
    rfl
  have ctorsIn' : ∀ i (hi : i < (indsOf types ctors).length) k (hk : k < (indsOf types ctors)[i].ctors.size),
      (sub.consts.get? (indsOf types ctors)[i].ctors[k].cnst.name).isSome = true := by
    intro i hi k hk
    have hk' : k < (ctors[i]'(by omega)).size := by simpa [indsOf, InductiveCompile.indOf] using hk
    obtain ⟨ci, hci⟩ := ctorsIn i (by omega) k hk'
    have e : (indsOf types ctors)[i].ctors[k].cnst.name = (ctors[i]'(by omega))[k].cnst.name := by
      simp [indsOf, InductiveCompile.indOf]
    rw [e, SourceStoredNames.stored_get hci]
    rfl
  obtain ⟨countI, typesAt, ctorsAt⟩ := inductive_published ran₁ hr₁ pub₁ hrec₁ typesIn' ctorsIn'
  have stored₁ : recordAt ixe out₁.blockAddr = some out₁.block := by
    have hrec' := hrec₁
    simp only [BlockRecords.recordsOf, Prod.mk.injEq] at hrec'
    obtain ⟨hblock, -, haddr, -⟩ := hrec'
    rw [← haddr, ← hblock]
    exact BlockPublication.stored hr₁ pub₁
  have stored₂ : recordAt ixe out₂.blockAddr = some out₂.block := by
    have hrec' := hrec₂
    simp only [BlockRecords.recordsOf, Prod.mk.injEq] at hrec'
    obtain ⟨hblock, -, haddr, -⟩ := hrec'
    rw [← haddr, ← hblock]
    exact BlockPublication.stored hr₂ pub₂
  -- the types' keys
  have typeKeys : ∀ i (hi : i < types.size), ∃ Q, Q ∈ order ∧
      recordAt ixe Q = some (MutualProjections.memberProjection out₁.blockAddr i.toUInt64
        (.indc ((indsOf types ctors)[i]'(by omega)))) ∧
      (closureContext ixe t preA order).memberKey (.member out₁.blockAddr i) =
        .ok ((quotientKey ixe t types[i].cnst.name).map (evAddr ixe b)) := by
    intro i hi
    have hi' : i < (indsOf types ctors).length := by omega
    obtain ⟨Q, hQ, hc⟩ := typesAt i hi'
    have e : (indsOf types ctors)[i].name = types[i].cnst.name := by simp [indsOf, InductiveCompile.indOf]
    rw [e] at hQ
    obtain ⟨ci, hci⟩ := typesIn i hi
    obtain ⟨q, hq⟩ := published_resolves resolves hci hQ hc
    have hqv := resolveSource_iPrj rfl hq
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans hi' countI)] at hqv
    subst hqv
    obtain ⟨hQo, hkey⟩ := published_key P prelude corder canonical b hci hQ hc hq
    exact ⟨Q, hQo, hc, hkey⟩
  have hB₁ : out₁.blockAddr ∈ order := by
    have h0 : 0 < types.size := (Array.getElem?_eq_some_iff.mp hfirst).1
    obtain ⟨Q, hQo, hc, -⟩ := typeKeys 0 h0
    exact owner_in_order corder hQo hc rfl
  -- the recursors' records and keys
  have recsIn' : ∀ j (hj : j < recs.toList.length), ∃ ci, (recs.toList[j].cnst.name, ci) ∈ sub.consts.toList :=
    fun j hj => by simpa using recsIn j (by simpa using hj)
  have recAt := recursor_published resolves hrne ran₂ hr₂ pub₂ hrec₂ recsIn'
  have recKeys : ∀ j (hj : j < recs.size), ∃ Q, Q ∈ order ∧ ∃ c, recordAt ixe Q = some c ∧
      ownerOf Q c = out₂.blockAddr ∧
      (closureContext ixe t preA order).memberKey (.member out₂.blockAddr j) =
        .ok ((quotientKey ixe t recs[j].cnst.name).map (evAddr ixe b)) := by
    intro j hj
    obtain ⟨Q, c, hQ, hc, hq, hown⟩ := recAt j (by simpa using hj)
    obtain ⟨ci, hci⟩ := recsIn j hj
    simp only [Array.getElem_toList] at hQ
    obtain ⟨hQo, hkey⟩ := published_key P prelude corder canonical b hci hQ hc hq
    exact ⟨Q, hQo, c, hc, hown, hkey⟩
  have hB₂ : out₂.blockAddr ∈ order := by
    have h0 : 0 < recs.size := by
      rcases h : recs.toList with _ | ⟨r, rs⟩
      · exact absurd h hrne
      · have := congrArg List.length h
        simp only [Array.length_toList, List.length_cons] at this
        omega
    obtain ⟨Q, hQo, c, hc, hown, -⟩ := recKeys 0 h0
    exact owner_in_order corder hQo hc hown
  -- the blocks' compile-side contexts
  have refs₁ := SingletonReads.lone_refs (t := t) (preA := preA) hB₁ stored₁ blobs₁
  have refs₂ := SingletonReads.lone_refs (t := t) (preA := preA) hB₂ stored₂ blobs₂
  have external₁ := own_external (t := t) (preA := preA) corder hB₁ stored₁ (blob := fun a => cenv₁.blobs.get? a) bound₁
    (fun m => ∃ (i : Nat) (_ : i < types.size), types[i].cnst.name = m)
    (fun m => (quotientKey ixe t m).map (evAddr ixe b))
  have external₂ := own_external (t := t) (preA := preA) corder hB₂ stored₂ (blob := fun a => cenv₂.blobs.get? a) bound₂
    (fun m => ∃ (j : Nat) (_ : j < recs.size), recs[j].cnst.name = m)
    (fun m => (quotientKey ixe t m).map (evAddr ixe b))
  have agree₁ := fun m k hm h =>
    own_agree (cB := out₁.block) (blob := fun a => cenv₁.blobs.get? a) P prelude corder canonical b bound₁
      (fun m => ∃ (i : Nat) (_ : i < types.size), types[i].cnst.name = m) (M := fun m =>
      ∃ i ∈ indsOf types ctors, ∃ e ∈ BlockEmission.memberSources (.indc i), GraphWalk.Refs m e) published₁ m k hm h
  have agree₂ := fun m k hm h =>
    own_agree (cB := out₂.block) (blob := fun a => cenv₂.blobs.get? a) P prelude corder canonical b bound₂
      (fun m => ∃ (j : Nat) (_ : j < recs.size), recs[j].cnst.name = m) (M := fun m =>
      ∃ r ∈ recs.toList, ∃ e ∈ BlockEmission.memberSources (.recr r), GraphWalk.Refs m e) published₂ m k hm h
  -- the constructors' count fits the wire: the inductive block keeps its sources' headers
  obtain ⟨targets, -, hT⟩ := InductiveCompile.inductiveBlock_reads (fiberAliasAt ixe (roleAtMap t)) (evAddr ixe b)
    (cenv₁, benv₁) rfl (fun _ => rfl) external₁ (indsOf types ctors)
    (fun k hk => by
      refine .inl ⟨⟨k, by omega, ?_⟩, ?_⟩
      · simp [indsOf, InductiveCompile.indOf]
      · simp [indsOf, InductiveCompile.indOf]
        rfl)
    (fun i hi e he n key hn h => agree₁ n key ⟨i, hi, e, he, hn⟩ h)
    first.cnst.levelParams (by
      intro i hi
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi
      rw [InductiveCompile.indsOf_getElem hcsize hk]
      exact lpsEq _ (Array.getElem_mem_toList _))
    out₁.blockAddr (fun k hk => by
      obtain ⟨-, -, -, hkey⟩ := typeKeys k (by omega)
      have e : (indsOf types ctors)[k].name = types[k].cnst.name := by simp [indsOf, InductiveCompile.indOf]
      rw [e]
      exact hkey)
    distinct noCtor BlockStart.clean_empty ran₁ refs₁
  have ctorCount : ∀ i (hi : i < (indsOf types ctors).length), (indsOf types ctors)[i].ctors.size < UInt64.size := by
    intro i hi
    have hiT : i < targets.length := (InductiveCompile.forall₂_length hT) ▸ hi
    obtain ⟨⟨-, header, hctors⟩, -⟩ := InductiveCompile.forall₂_getElem hT i hi hiT
    have := InductiveCompile.forall₂_length hctors
    simp only [Array.length_toList] at this
    rw [this]
    exact header.2.2.2
  -- the constructors' keys
  have ctorKeys : ∀ i (hi : i < ctors.size) j (hj : j < ctors[i].size),
      (closureContext ixe t preA order).memberKey (.ctor out₁.blockAddr i j) =
        .ok ((quotientKey ixe t ctors[i][j].cnst.name).map (evAddr ixe b)) := by
    intro i hi j hj
    have hi' : i < (indsOf types ctors).length := by omega
    have hj' : j < (indsOf types ctors)[i].ctors.size := by simpa [indsOf, InductiveCompile.indOf] using hj
    obtain ⟨Q, hQ, hc⟩ := ctorsAt i hi' j hj'
    have e : (indsOf types ctors)[i].ctors[j].cnst.name = ctors[i][j].cnst.name := by
      simp [indsOf, InductiveCompile.indOf]
    rw [e] at hQ
    obtain ⟨ci, hci⟩ := ctorsIn i hi j hj
    obtain ⟨q, hq⟩ := published_resolves resolves hci hQ hc
    have hqv := resolveSource_cPrj rfl hq
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans hi' countI),
      Nat.mod_eq_of_lt (Nat.lt_trans hj' (ctorCount i hi'))] at hqv
    subst hqv
    exact (published_key P prelude corder canonical b hci hQ hc hq).2
  -- the recursor family's record reads to nothing: the closure's index holds its recursors
  have inert₂ : InertAt (closureContext ixe t preA order) out₂.blockAddr out₂.block := by
    refine recursor_inert (recursor_info ran₂) (List.length_pos_iff.mpr hrne) fun j hj => ?_
    obtain ⟨entry, -, -, hentry, -⟩ := entries j (by simpa using hj)
    rw [Std.HashMap.contains_eq_isSome_getElem?, hentry]
    rfl
  -- quotient Source's read lies in the scope
  have inScope : StreamUnits.ReadScoped (KeyScope.ofId (QRepAt ixe (roleAtMap t))) rS := by
    obtain ⟨first', -, hconv, -, -⟩ := InductiveUnits.convertInductive_src src
    have hq : conv.quotient (fiberAliasAt ixe (roleAtMap t)) = .inductive (Ix.LeanIngress.BlockRead.canon
        (Ix.LeanIngress.BlockRead.substKeys (fiberAliasAt ixe (roleAtMap t))
          (InductiveUnits.srcBlock types ctors recs first'))) := by
      rw [hconv]
      rfl
    have lowered' := lowered
    rw [hq] at lowered'
    exact inductive_scoped (good _ hq) lowered'
  -- the reading
  refine ⟨hB₁, stored₁, hB₂, stored₂, inert₂, inScope, ?_⟩
  exact InductiveCompile.compiled_inductive_unit_reads (fiberAliasAt ixe (roleAtMap t)) (evAddr ixe b)
    (P := KeyScope.ofId (QRepAt ixe (roleAtMap t))) (fun _ _ => trivial) hf src hfirst hcsize lpsEq ctorLps nodup
    positions recLpsEq recNodup hrne distinct noCtor recDistinct
    (cenv₁, benv₁) rfl (fun _ => rfl) external₁ (fun i hi => .inl ⟨⟨i, hi, rfl⟩, rfl⟩)
    (fun i hi e he n key hn h => agree₁ n key ⟨i, hi, e, he, hn⟩ h) BlockStart.clean_empty ran₁
    (cenv₂, benv₂) rfl (fun _ => rfl) external₂ (fun j hj => .inl ⟨⟨j, hj, rfl⟩, rfl⟩)
    (fun r hr e he n key hn h => agree₂ n key ⟨r, hr, e, he, hn⟩ h) BlockStart.clean_empty ran₂
    (closureContext ixe t preA order) out₁.blockAddr out₂.blockAddr
    (ClosureKeying.closure_store corder.nodup hB₁ stored₁) (ClosureKeying.closure_store corder.nodup hB₂ stored₂)
    refs₁ refs₂ (fun i hi => by obtain ⟨_, -, -, hkey⟩ := typeKeys i hi; exact hkey) ctorKeys
    (fun j hj => by obtain ⟨_, -, _, -, -, hkey⟩ := recKeys j hj; exact hkey)
    hindexed hshape hrecs entries good typesGood blocksGood lowered

/-! ## The inductive group's segment -/

/-- The projection kinds `ClosureSegments.projection_inert` reads to nothing. -/
abbrev IsProj (c : Ixon.Constant) : Prop :=
  (∃ p, c.info = .dPrj p) ∨ (∃ p, c.info = .iPrj p) ∨ (∃ p, c.info = .rPrj p) ∨ ∃ p, c.info = .cPrj p

/-- A record that is not its own block is a projection. -/
theorem proj_of_owner {a : Address} {c : Ixon.Constant} (h : ownerOf a c ≠ a) : IsProj c := by
  cases hi : c.info with
  | defn _ | recr _ | axio _ | quot _ | muts _ => simp [ownerOf, hi] at h
  | dPrj p => exact .inl ⟨p, hi⟩
  | iPrj p => exact .inr (.inl ⟨p, hi⟩)
  | rPrj p => exact .inr (.inr (.inl ⟨p, hi⟩))
  | cPrj p => exact .inr (.inr (.inr ⟨p, hi⟩))

/-- **An inductive group's segment reads as quotient Source's read**, from `closure_inductive_reads`'
facts, when the collapse keeps the read whole and the segment holds the inductive block's record
among the recursor family's record and projection records published for closure names. -/
theorem inductive_segment {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {failures : Failures} {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ)
    {preA : Prelude .anon} (corder : ClosureOrder ixe (Seed ixe sub) order)
    (resolves : SingletonSegments.PublishedResolve ixe sub) {b : Ix.RoleEvidence.Bundle}
    {B R : Address} {c₁ c₂ : Ixon.Constant} (stored₁ : recordAt ixe B = some c₁) (stored₂ : recordAt ixe R = some c₂)
    (inert₂ : InertAt (closureContext ixe t preA order) R c₂) {stS : State .source} {raw rd : Read .source}
    (inScope : StreamUnits.ReadScoped (KeyScope.ofId (QRepAt ixe (roleAtMap t))) raw)
    (reads : ∀ stA : State .anon, StreamRename.StateRen (evAddr ixe b) (KeyScope.ofId (QRepAt ixe (roleAtMap t))) stS stA →
      ∃ rA, readRecord (closureContext ixe t preA order) stA B c₁ = .ok rA ∧ StreamUnits.ReadRen (evAddr ixe b) raw rA)
    (kept : rd = raw) {seg : List Address}
    (place : ∃ before after, seg = before ++ B :: after ∧ ∀ a ∈ before ++ after, a = R ∨
      ∃ (n : Ix.Name) (ci : Ix.ConstantInfo) (c : Ixon.Constant), (n, ci) ∈ sub.consts.toList ∧
        ClosureLayout.addrOf ixe n = some a ∧ recordAt ixe a = some c ∧ IsProj c) :
    SegmentReads (evAddr ixe b) (KeyScope.ofId (QRepAt ixe (roleAtMap t))) (closureContext ixe t preA order) ixe
      stS rd seg := by
  obtain ⟨before, after, hseg, hin⟩ := place
  have inert : ∀ a ∈ before ++ after, ∀ c, recordAt ixe a = some c → InertAt (closureContext ixe t preA order) a c := by
    intro a ha c hc
    rcases hin a ha with rfl | ⟨n, ci, c', hn, haddr, hc', hproj⟩
    · rw [stored₂, Option.some.injEq] at hc
      subst hc
      exact inert₂
    · rw [hc', Option.some.injEq] at hc
      subst hc
      exact published_inert P corder resolves hn haddr hc' hproj
  exact kept_segment inScope kept stored₁ reads ⟨before, after, hseg,
    fun a ha => inert a (List.mem_append_left _ ha), fun a ha => inert a (List.mem_append_right _ ha)⟩

/-- **A compiled inductive block is a block of inductives**, one per member, each with its member's
number of constructors. -/
theorem inductive_block_info {context : CompileEnv × BlockEnv} {before after : BlockState} {output : BlockResult}
    {inds : List Ix.Ind}
    (ran : rawRun (compileMutualBlock ((inds.map MutConst.indc).map ([·]))) context before = (.ok output, after)) :
    ∃ ms : Array Ixon.MutConst, output.block.info = .muts ms ∧ ms.size = inds.length ∧
      ∀ i (y : Ixon.MutConst), ms[i]? = some y → ∃ v, ∃ hi : i < inds.length, y = .indc v ∧
        v.ctors.size = inds[i].ctors.size := by
  have shape := ProjectionLayout.mutual_block_shape _ context before output after ran
  rw [heads_map, List.map_map] at shape
  cases hinfo : output.block.info with
  | muts ms =>
    rw [hinfo] at shape
    simp only [ProjectionLayout.blockShape, Option.some.injEq] at shape
    refine ⟨ms, rfl, by simpa using congrArg List.length shape, fun i y hy => ?_⟩
    have h1 : (ms.toList.map ProjectionLayout.memberShape)[i]? = some (ProjectionLayout.memberShape y) := by
      simp [hy]
    rw [shape, List.getElem?_map, Option.map_eq_some_iff] at h1
    obtain ⟨a, ha, hsa⟩ := h1
    obtain ⟨hi, hai⟩ := List.getElem?_eq_some_iff.mp ha
    cases y with
    | indc v =>
      refine ⟨v, hi, rfl, ?_⟩
      simp only [Function.comp_apply, ProjectionLayout.sourceShape, ProjectionLayout.memberShape,
        ProjectionLayout.MemberShape.indc.injEq] at hsa
      have := congrArg List.length hsa
      simp only [List.length_map, Array.length_toList] at this
      rw [hai]
      omega
    | defn _ => simp [ProjectionLayout.sourceShape, ProjectionLayout.memberShape] at hsa
    | recr _ => simp [ProjectionLayout.sourceShape, ProjectionLayout.memberShape] at hsa
  | defn _ | recr _ =>
    exfalso
    rw [hinfo] at shape
    cases inds with
    | nil => simp [ProjectionLayout.blockShape] at shape
    | cons i rest => simp [ProjectionLayout.blockShape, ProjectionLayout.sourceShape] at shape
  | axio _ | quot _ | dPrj _ | iPrj _ | rPrj _ | cPrj _ =>
    rw [hinfo] at shape
    simp [ProjectionLayout.blockShape] at shape

/-- **A record an inductive block owns, and that resolves, names one of its types or constructors.** -/
theorem owned_inductive {B A : Address} {cB cm : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hB : recordAt ixe B = some cB) (hinfo : cB.info = .muts ms)
    (hind : ∀ (i : Nat) (y : Ixon.MutConst), ms[i]? = some y → ∃ v, y = Ixon.MutConst.indc v)
    (hown : ownerOf A cm = B) {q : ConstRef Address} (hq : resolveSource (recordAt ixe) A cm = some q) (ne : A ≠ B) :
    (∃ i v, ms[i]? = some (.indc v) ∧ i < UInt64.size ∧ q = .member B i) ∨
      ∃ i v k, ms[i]? = some (.indc v) ∧ k < v.ctors.size ∧ i < UInt64.size ∧ k < UInt64.size ∧ q = .ctor B i k := by
  cases hi : cm.info with
  | defn _ | recr _ | axio _ | quot _ | muts _ =>
    simp only [ownerOf, hi] at hown
    exact absurd hown ne
  | iPrj p =>
    simp only [ownerOf, hi] at hown
    subst hown
    unfold resolveSource at hq
    rw [hi] at hq
    simp only [Option.bind_eq_bind] at hq
    obtain ⟨_, -, hq⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨blk, hblk, hq⟩ := Option.bind_eq_some_iff.mp hq
    rw [hB, Option.some.injEq] at hblk
    subst hblk
    simp only [hinfo] at hq
    obtain ⟨y, hy, hq⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨v, rfl⟩ := hind _ _ hy
    cases hq
    exact .inl ⟨_, v, hy, UInt64.toNat_lt_size _, rfl⟩
  | cPrj p =>
    simp only [ownerOf, hi] at hown
    subst hown
    unfold resolveSource at hq
    rw [hi] at hq
    simp only [Option.bind_eq_bind] at hq
    obtain ⟨_, -, hq⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨blk, hblk, hq⟩ := Option.bind_eq_some_iff.mp hq
    rw [hB, Option.some.injEq] at hblk
    subst hblk
    simp only [hinfo] at hq
    obtain ⟨y, hy, hq⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨v, rfl⟩ := hind _ _ hy
    obtain ⟨ctor, hctor, hq⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.mp hq
    cases hq
    exact .inr ⟨_, v, _, hy, (Array.getElem?_eq_some_iff.mp hctor).1, UInt64.toNat_lt_size _,
      UInt64.toNat_lt_size _, rfl⟩
  | dPrj p | rPrj p =>
    exfalso
    simp only [ownerOf, hi] at hown
    subst hown
    unfold resolveSource at hq
    rw [hi] at hq
    simp only [Option.bind_eq_bind] at hq
    obtain ⟨_, -, hq⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨blk, hblk, hq⟩ := Option.bind_eq_some_iff.mp hq
    rw [hB, Option.some.injEq] at hblk
    subst hblk
    simp only [hinfo] at hq
    obtain ⟨y, hy, hq⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨v, rfl⟩ := hind _ _ hy
    cases hq

/-- **A closure name whose records include an inductive block's record is published where one of
the block's types or constructors is**: a name at the block record itself would not resolve, and
a name at a record the block owns resolves to a type's or constructor's position, which only that
member's projection resolves to. -/
theorem member_of_inductive {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {failures : Failures} {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ)
    {preA : Prelude .anon} (prelude : preludeFor t = .ok preA) (corder : ClosureOrder ixe (Seed ixe sub) order)
    (canonical : Stream.StoredCanonical ixe order) (resolves : SingletonSegments.PublishedResolve ixe sub)
    {B : Address} {cB : Ixon.Constant} {ms : Array Ixon.MutConst} (stored : recordAt ixe B = some cB)
    (hinfo : cB.info = .muts ms)
    (hind : ∀ (i : Nat) (y : Ixon.MutConst), ms[i]? = some y → ∃ v, y = Ixon.MutConst.indc v) (isMember : Ix.Name → Prop)
    (typeAt : ∀ i v, ms[i]? = some (.indc v) → i < UInt64.size → ∃ n Q c, isMember n ∧
      ClosureLayout.addrOf ixe n = some Q ∧ Q ∈ order ∧ recordAt ixe Q = some c ∧
        resolveSource (recordAt ixe) Q c = some (.member B i))
    (ctorAt : ∀ i v k, ms[i]? = some (.indc v) → k < v.ctors.size → i < UInt64.size → k < UInt64.size →
      ∃ n Q c, isMember n ∧ ClosureLayout.addrOf ixe n = some Q ∧ Q ∈ order ∧ recordAt ixe Q = some c ∧
        resolveSource (recordAt ixe) Q c = some (.ctor B i k))
    {m : Ix.Name} {cim : Ix.ConstantInfo} (hcim : (m, cim) ∈ sub.consts.toList)
    (hBm : B ∈ ClosureLayout.nameRecords ixe m) :
    ∃ n, isMember n ∧ ClosureLayout.addrOf ixe n = ClosureLayout.addrOf ixe m := by
  have compiled : compile env = .ok ixe := by unfold compile; rw [P.compiled]; rfl
  have auth := fun a c h => ClosureKeying.closure_authentic compiled P.evidence.2.1 prelude canonical (a := a) (c := c) h
  obtain ⟨namedm, -, hgetm⟩ := SourceStoredNames.stored_published P hcim
  have hm : ClosureLayout.addrOf ixe m = some namedm.addr := by
    unfold ClosureLayout.addrOf
    rw [hgetm]
    rfl
  have notAt : namedm.addr ≠ B := by
    intro e
    have h := resolves m cim namedm hcim hgetm cB (by rw [e]; exact stored)
    simp [resolveSource, hinfo] at h
  unfold ClosureLayout.nameRecords at hBm
  rw [hm] at hBm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hBm
  rcases hBm with e | e
  · exact absurd e.symm notAt
  · unfold ClosureLayout.blockAt at e
    cases hcm : recordAt ixe namedm.addr with
    | none => rw [hcm] at e; exact absurd e.symm notAt
    | some cm =>
      rw [hcm] at e
      dsimp only at e
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (resolves m cim namedm hcim hgetm cm hcm)
      have hAo : namedm.addr ∈ order := (corder.complete _).mpr
        (.seed ⟨m, cim, namedm, SourceStoredNames.stored_get hcim, hgetm, rfl⟩ (ClosureLayout.recordAt_contains hcm))
      have e₁ := BlockContext.closure_resolve (t := t) (preA := preA) corder hAo hcm hq
      rcases owned_inductive stored hinfo hind e.symm hq notAt with
        ⟨i, v, hy, hi, rfl⟩ | ⟨i, v, k, hy, hk, hi, hk', rfl⟩
      · obtain ⟨n, Q, c, hn, hQ, hQo, hc, hres⟩ := typeAt i v hy hi
        have e₂ := BlockContext.closure_resolve (t := t) (preA := preA) corder hQo hc hres
        exact ⟨n, hn, by rw [hQ, hm, ReadingKeys.resolve_inj auth e₂ e₁]⟩
      · obtain ⟨n, Q, c, hn, hQ, hQo, hc, hres⟩ := ctorAt i v k hy hk hi hk'
        have e₂ := BlockContext.closure_resolve (t := t) (preA := preA) corder hQo hc hres
        exact ⟨n, hn, by rw [hQ, hm, ReadingKeys.resolve_inj auth e₂ e₁]⟩

/-- A closure name's published record is a record of the closure order. -/
theorem published_in_order {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {failures : Failures} {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ)
    (corder : ClosureOrder ixe (Seed ixe sub) order) {n : Ix.Name} {ci : Ix.ConstantInfo}
    (hn : (n, ci) ∈ sub.consts.toList) {Q : Address} (haddr : ClosureLayout.addrOf ixe n = some Q)
    {c : Ixon.Constant} (hc : recordAt ixe Q = some c) : Q ∈ order := by
  obtain ⟨named, -, hget⟩ := SourceStoredNames.stored_published P hn
  have hQ : named.addr = Q := by
    unfold ClosureLayout.addrOf at haddr
    rw [hget] at haddr
    exact Option.some.inj haddr
  exact (corder.complete _).mpr
    (.seed ⟨n, ci, named, SourceStoredNames.stored_get hn, hget, hQ⟩ (ClosureLayout.recordAt_contains hc))

/-- **A kept inductive group's segment holds its block's record among records read to nothing**:
the recursor family's record and projections published for the group's names. No earlier lowered
group holds the block's record, since an earlier name whose records include it is published where a
type or constructor is (`member_of_inductive`), so it has that type's or constructor's quotient
key, which the group's read keeps and no earlier read declares (`DefinitionSegments.block_fresh`). -/
theorem inductive_place {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {failures : Failures} {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ)
    {preA : Prelude .anon} (prelude : preludeFor t = .ok preA) (corder : ClosureOrder ixe (Seed ixe sub) order)
    (canonical : Stream.StoredCanonical ixe order)
    {hints : CName .source → Option ReducibilityHint} {start : State .source} {ls : List SourcePrelude.Scheduled}
    {rs : List (Read .source)} (steps : ClosureLayout.Steps (ClosureLayout.quotientGraph ixe t hints sub) start ls rs)
    (inTrace : ∀ y ∈ ls, y ∈ (Ix.LeanIngress.scheduleOf (ClosureLayout.quotientGraph ixe t hints sub)).zipIdx.toList)
    {L : List Address} (hnd : L.Nodup) (hmem : ∀ a, a ∈ L ↔ ixe.consts.contains a = true)
    (resolves : SingletonSegments.PublishedResolve ixe sub) {ℓ : Nat} {y : SourcePrelude.Scheduled}
    {r : Read .source} (hy : ls[ℓ]? = some y) (hr : rs[ℓ]? = some r)
    {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal}
    (hcsize : ctors.size = types.size) (hpos : 0 < types.size) (hrne : recs.toList ≠ [])
    (typesIn : ∀ i (hi : i < types.size), ∃ ci, (types[i].cnst.name, ci) ∈ sub.consts.toList)
    (ctorsIn : ∀ i (hi : i < ctors.size) k (hk : k < ctors[i].size), ∃ ci, (ctors[i][k].cnst.name, ci) ∈ sub.consts.toList)
    (recsIn : ∀ j (hj : j < recs.size), ∃ ci, (recs[j].cnst.name, ci) ∈ sub.consts.toList)
    (hnames : ∀ n, n ∈ ClosureLayout.namesAt (ClosureLayout.quotientGraph ixe t hints sub) y ↔
      (∃ (i : Nat) (_ : i < types.size), types[i].cnst.name = n) ∨
      (∃ (i : Nat) (hi : i < ctors.size) (k : Nat) (_ : k < ctors[i].size), ctors[i][k].cnst.name = n) ∨
      ∃ (j : Nat) (_ : j < recs.size), recs[j].cnst.name = n)
    {context₁ : CompileEnv × BlockEnv} {before₁ after₁ : BlockState} {out₁ : BlockResult}
    (ran₁ : rawRun (compileMutualBlock (((indsOf types ctors).map MutConst.indc).map ([·]))) context₁ before₁ =
      (.ok out₁, after₁))
    {cenvR₁ : CompileEnv} {all₁ : Ix.Set Ix.Name} {key₁ : Ix.Name} {r₁ : BlockResult} {cache₁ : BlockState}
    (hr₁ : runBlock cenvR₁ all₁ key₁ = .ok (r₁, cache₁)) (pub₁ : BlockPublication.Published ixe sub key₁ r₁)
    (hrec₁ : BlockRecords.recordsOf r₁ = BlockRecords.recordsOf out₁)
    {context₂ : CompileEnv × BlockEnv} {before₂ after₂ : BlockState} {out₂ : BlockResult}
    (ran₂ : rawRun (compileMutualBlock ((recs.toList.map MutConst.recr).map ([·]))) context₂ before₂ =
      (.ok out₂, after₂))
    {cenvR₂ : CompileEnv} {all₂ : Ix.Set Ix.Name} {key₂ : Ix.Name} {r₂ : BlockResult} {cache₂ : BlockState}
    (hr₂ : runBlock cenvR₂ all₂ key₂ = .ok (r₂, cache₂)) (pub₂ : BlockPublication.Published ixe sub key₂ r₂)
    (hrec₂ : BlockRecords.recordsOf r₂ = BlockRecords.recordsOf out₂)
    (hdecl : ∀ n, ((∃ (i : Nat) (_ : i < types.size), types[i].cnst.name = n) ∨
        ∃ (i : Nat) (hi : i < ctors.size) (k : Nat) (_ : k < ctors[i].size), ctors[i][k].cnst.name = n) →
      ∃ d ∈ r.decls.toList, ClosureLayout.qkey (fiberAliasAt ixe (roleAtMap t)) n ∈ d.names) :
    ∃ before after, (ClosureLayout.segmentsOf L (ls.map fun y =>
        ClosureLayout.groupRecords ixe (ClosureLayout.namesAt (ClosureLayout.quotientGraph ixe t hints sub) y)) [])[ℓ]? =
          some (before ++ out₁.blockAddr :: after) ∧
      ∀ a ∈ before ++ after, a = out₂.blockAddr ∨
        ∃ (n : Ix.Name) (ci : Ix.ConstantInfo) (c : Ixon.Constant), (n, ci) ∈ sub.consts.toList ∧
          ClosureLayout.addrOf ixe n = some a ∧ recordAt ixe a = some c ∧ IsProj c := by
  have hlenI := InductiveCompile.indsOf_length hcsize
  have typeName : ∀ i (hi : i < (indsOf types ctors).length),
      (indsOf types ctors)[i].name = (types[i]'(by omega)).cnst.name := by
    intro i hi
    simp [indsOf, InductiveCompile.indOf]
  have ctorName : ∀ i (hi : i < (indsOf types ctors).length) k (hk : k < (indsOf types ctors)[i].ctors.size),
      (indsOf types ctors)[i].ctors[k].cnst.name =
        ((ctors[i]'(by omega))[k]'(by simpa [indsOf, InductiveCompile.indOf] using hk)).cnst.name := by
    intro i hi k hk
    simp [indsOf, InductiveCompile.indOf]
  have typesIn' : ∀ i (hi : i < (indsOf types ctors).length),
      (sub.consts.get? (indsOf types ctors)[i].name).isSome = true := by
    intro i hi
    obtain ⟨ci, hci⟩ := typesIn i (by omega)
    rw [typeName i hi, SourceStoredNames.stored_get hci]
    rfl
  have ctorsIn' : ∀ i (hi : i < (indsOf types ctors).length) k (hk : k < (indsOf types ctors)[i].ctors.size),
      (sub.consts.get? (indsOf types ctors)[i].ctors[k].cnst.name).isSome = true := by
    intro i hi k hk
    obtain ⟨ci, hci⟩ := ctorsIn i (by omega) k (by simpa [indsOf, InductiveCompile.indOf] using hk)
    rw [ctorName i hi k hk, SourceStoredNames.stored_get hci]
    rfl
  obtain ⟨countI, typesAt, ctorsAt⟩ := inductive_published ran₁ hr₁ pub₁ hrec₁ typesIn' ctorsIn'
  have stored₁ : recordAt ixe out₁.blockAddr = some out₁.block := by
    have hrec' := hrec₁
    simp only [BlockRecords.recordsOf, Prod.mk.injEq] at hrec'
    obtain ⟨hblock, -, haddr, -⟩ := hrec'
    rw [← haddr, ← hblock]
    exact BlockPublication.stored hr₁ pub₁
  obtain ⟨ms, hinfo, hms, hshape⟩ := inductive_block_info ran₁
  have recsIn' : ∀ j (hj : j < recs.toList.length), ∃ ci, (recs.toList[j].cnst.name, ci) ∈ sub.consts.toList :=
    fun j hj => by simpa using recsIn j (by simpa using hj)
  have recAt := recursor_published resolves hrne ran₂ hr₂ pub₂ hrec₂ recsIn'
  -- every record of a name of the group is the block, the recursor family, or a published projection
  have inC : ∀ a ∈ ClosureLayout.groupRecords ixe (ClosureLayout.namesAt (ClosureLayout.quotientGraph ixe t hints sub) y),
      a = out₁.blockAddr ∨ (a = out₂.blockAddr ∨ ∃ (n : Ix.Name) (ci : Ix.ConstantInfo) (c : Ixon.Constant),
        (n, ci) ∈ sub.consts.toList ∧ ClosureLayout.addrOf ixe n = some a ∧ recordAt ixe a = some c ∧ IsProj c) := by
    intro a ha
    obtain ⟨n, hn, ha⟩ := List.mem_flatMap.mp ha
    unfold ClosureLayout.nameRecords at ha
    rcases (hnames n).mp (Array.mem_toList_iff.mp hn) with ⟨i, hi, rfl⟩ | ⟨i, hi, k, hk, rfl⟩ | ⟨j, hj, rfl⟩
    · have hi' : i < (indsOf types ctors).length := by omega
      obtain ⟨Q, hQ, hc⟩ := typesAt i hi'
      rw [typeName i hi'] at hQ
      obtain ⟨ci, hci⟩ := typesIn i hi
      rw [hQ] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact .inr (.inr ⟨_, ci, _, hci, hQ, hc, .inr (.inl ⟨_, rfl⟩)⟩)
      · left
        unfold ClosureLayout.blockAt
        rw [hc]
        rfl
    · have hi' : i < (indsOf types ctors).length := by omega
      have hk' : k < (indsOf types ctors)[i].ctors.size := by simpa [indsOf, InductiveCompile.indOf] using hk
      obtain ⟨Q, hQ, hc⟩ := ctorsAt i hi' k hk'
      rw [ctorName i hi' k hk'] at hQ
      obtain ⟨ci, hci⟩ := ctorsIn i hi k hk
      rw [hQ] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact .inr (.inr ⟨_, ci, _, hci, hQ, hc, .inr (.inr (.inr ⟨_, rfl⟩))⟩)
      · left
        unfold ClosureLayout.blockAt
        rw [hc]
        rfl
    · obtain ⟨Q, c, hQ, hc, -, hown⟩ := recAt j (by simpa using hj)
      simp only [Array.getElem_toList] at hQ
      obtain ⟨ci, hci⟩ := recsIn j hj
      rw [hQ] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · by_cases e : a = out₂.blockAddr
        · exact .inr (.inl e)
        · exact .inr (.inr ⟨_, ci, c, hci, hQ, hc, proj_of_owner (by rw [hown]; exact fun h => e h.symm)⟩)
      · refine .inr (.inl ?_)
        unfold ClosureLayout.blockAt
        rw [hc]
        exact hown
  have inB : out₁.blockAddr ∈
      ClosureLayout.groupRecords ixe (ClosureLayout.namesAt (ClosureLayout.quotientGraph ixe t hints sub) y) := by
    have h0 : 0 < (indsOf types ctors).length := by omega
    obtain ⟨Q, hQ, hc⟩ := typesAt 0 h0
    rw [typeName 0 h0] at hQ
    refine List.mem_flatMap.mpr ⟨_, Array.mem_toList_iff.mpr ((hnames _).mpr (.inl ⟨0, hpos, rfl⟩)), ?_⟩
    have hb : ClosureLayout.blockAt ixe Q = out₁.blockAddr := by
      unfold ClosureLayout.blockAt
      rw [hc]
      rfl
    unfold ClosureLayout.nameRecords
    rw [hQ]
    show out₁.blockAddr ∈ [Q, ClosureLayout.blockAt ixe Q]
    rw [hb]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  -- the block's record is in no earlier group's records
  have hind : ∀ (i : Nat) (y : Ixon.MutConst), ms[i]? = some y → ∃ v, y = Ixon.MutConst.indc v := by
    intro i y hy
    obtain ⟨v, -, rfl, -⟩ := hshape i y hy
    exact ⟨v, rfl⟩
  have fresh := DefinitionSegments.block_fresh (isMember := fun n =>
      (∃ (i : Nat) (_ : i < types.size), types[i].cnst.name = n) ∨
        ∃ (i : Nat) (hi : i < ctors.size) (k : Nat) (_ : k < ctors[i].size), ctors[i][k].cnst.name = n)
    P steps inTrace hy hr
    (fun n hn => by
      rcases hn with ⟨i, hi, rfl⟩ | ⟨i, hi, k, hk, rfl⟩
      · exact typesIn i hi
      · exact ctorsIn i hi k hk)
    (fun m cim hcim hBm => member_of_inductive P prelude corder canonical resolves stored₁ hinfo hind _
      (fun i v hy hi64 => by
        obtain ⟨_, hi, -, -⟩ := hshape i _ hy
        have hiT : i < types.size := by omega
        obtain ⟨Q, hQ, hc⟩ := typesAt i hi
        rw [typeName i hi] at hQ
        obtain ⟨ci, hci⟩ := typesIn i hiT
        obtain ⟨q, hq⟩ := published_resolves resolves hci hQ hc
        have hqv := resolveSource_iPrj rfl hq
        simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hi64] at hqv
        subst hqv
        exact ⟨_, Q, _, .inl ⟨i, hiT, rfl⟩, hQ, published_in_order P corder hci hQ hc, hc, hq⟩)
      (fun i v k hy hk hi64 hk64 => by
        obtain ⟨v', hi, e, hsize⟩ := hshape i _ hy
        cases e
        have hk' : k < (indsOf types ctors)[i].ctors.size := by omega
        have hiC : i < ctors.size := by omega
        have hkC : k < (ctors[i]'hiC).size := by simpa [indsOf, InductiveCompile.indOf] using hk'
        obtain ⟨Q, hQ, hc⟩ := ctorsAt i hi k hk'
        rw [ctorName i hi k hk'] at hQ
        obtain ⟨ci, hci⟩ := ctorsIn i hiC k hkC
        obtain ⟨q, hq⟩ := published_resolves resolves hci hQ hc
        have hqv := resolveSource_cPrj rfl hq
        simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hk64] at hqv
        subst hqv
        exact ⟨_, Q, _, .inr ⟨i, hiC, k, hkC, rfl⟩, hQ, published_in_order P corder hci hQ hc, hc, hq⟩)
      hcim hBm)
    hdecl
  have hC : (ls.map fun y =>
      ClosureLayout.groupRecords ixe (ClosureLayout.namesAt (ClosureLayout.quotientGraph ixe t hints sub) y))[ℓ]? =
        some (ClosureLayout.groupRecords ixe (ClosureLayout.namesAt (ClosureLayout.quotientGraph ixe t hints sub) y)) := by
    rw [List.getElem?_map, hy]
    rfl
  rw [ClosureLayout.segmentsOf_get L _ [] ℓ _ hC]
  obtain ⟨s, t', hst, hin⟩ := DefinitionSegments.filter_place hnd
    ((hmem _).mpr (ClosureLayout.recordAt_contains stored₁)) inB fresh inC
  exact ⟨s, t', congrArg some hst, hin⟩

/--
info: 'Ix.Cert.InductiveSegments.closure_inductive_reads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closure_inductive_reads

/--
info: 'Ix.Cert.InductiveSegments.inductive_scoped' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms inductive_scoped

/--
info: 'Ix.Cert.InductiveSegments.inductive_segment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms inductive_segment

/--
info: 'Ix.Cert.InductiveSegments.inductive_place' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms inductive_place

end Ix.Cert.InductiveSegments
