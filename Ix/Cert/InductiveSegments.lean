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
  -- the reading
  refine ⟨hB₁, stored₁, hB₂, stored₂, ?_⟩
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

end Ix.Cert.InductiveSegments
