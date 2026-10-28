import Ix.Cert.SingletonSegments
import Ix.Cert.DefinitionBlockReads
import Ix.Cert.BlockPublication

/-! # A definition block's segment of the closure order

Quotient Source lowers a group of several definitions to one declaration per member, and the
compile builds one block record for it, with one projection record per member. The segment
`ClosureLayout` cuts for the group holds the block record among member projections; it reads as the
Source read when the block record reads as the lowering renamed and the projections read to
nothing.

* `ownNames`: the names a block is read at, its members at their quotient keys and every name the
  compile binds at the key the block's context reads there (`SingletonReads.blockNames` with several
  members).
* `block_members`: the artifact holds the block's record and publishes each member at its
  projection, which resolves to the member's position in the block; the closure's context keys that
  position as the member's quotient key renamed (`member_key`).
* `closure_block_reads`: `DefinitionBlockReads.definition_block_reads` in the closure's context, with
  the block's compile-side context `BlockContext.blockCtx` and its premises discharged.
* `definition_block_segment`: the group's segment reads as quotient Source's read, kept whole or
  dropped whole by the collapse. -/

namespace Ix.Cert.DefinitionSegments

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState
open Ix.Cert.ClosureSegments (SegmentReads InertAddrs InertAt)
open Ix.Cert.BlockContext (blockCtx BoundResolve)
open Ix.Cert.DefinitionDeps (ConstOcc)
open Ix.LeanIngress (evAddr QRepAt roleAtMap fiberAliasAt ingressKey)

variable {ixe : Ixon.Env} {order : List Address}

/-! ## The names a block is read at -/

/-- **The names a block compiled at `cenv` is read at**: each member (`selves`) at its key, and
every name the compile binds at the key the block's context reads at its binding. -/
def ownNames (cenv : CompileEnv) (cx₁ : Ctx .anon) (selves : Ix.Name → Prop) (key : Ix.Name → CName .anon)
    (m : Ix.Name) (k : CName .anon) : Prop :=
  (selves m ∧ k = key m) ∨ ∃ a, lookupBinding cenv ({}, {}) m = some a ∧ cx₁.keyAt a = .ok k

/-- **The block's context keys every name the compile binds.** -/
theorem own_external {t : RoleTable} {preA : Prelude .anon} {S : Address → Prop} (corder : ClosureOrder ixe S order)
    {blob : Address → Option ByteArray} {B : Address} {cB : Ixon.Constant} (hB : B ∈ order)
    (hcB : recordAt ixe B = some cB) {cenv : CompileEnv} (bound : BoundResolve ixe cenv) (selves : Ix.Name → Prop)
    (key : Ix.Name → CName .anon) :
    BindingsCorrect cenv ({}, {}) (blockCtx (closureContext ixe t preA order) ixe order cB.refs blob)
      (ownNames cenv (blockCtx (closureContext ixe t preA order) ixe order cB.refs blob) selves key) := by
  intro m a hb
  obtain ⟨c, hc, hres⟩ := bound m a hb
  obtain ⟨k, hk⟩ := BlockContext.keyAt_stored corder hB hcB hc hres
  exact ⟨k, hk, .inr ⟨a, hb, hk⟩⟩

/-- **At a mentioned closure name, the block's names are quotient Source's names renamed**, when
the compile binds the name at its published address and the members are keyed by their quotient
keys renamed. -/
theorem own_agree {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {failures : Failures}
    {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ) {preA : Prelude .anon}
    (prelude : preludeFor t = .ok preA) (corder : ClosureOrder ixe (Seed ixe sub) order)
    (canonical : Stream.StoredCanonical ixe order) (b : Ix.RoleEvidence.Bundle) {blob : Address → Option ByteArray}
    {cB : Ixon.Constant} {cenv : CompileEnv} (bound : BoundResolve ixe cenv) (selves : Ix.Name → Prop)
    {M : Ix.Name → Prop}
    (published : ∀ m a, M m → lookupBinding cenv ({}, {}) m = some a →
      ∃ named, (m, named) ∈ ixe.named.toList ∧ named.addr = a ∧ (sub.consts.get? m).isSome = true) :
    ∀ m k, M m →
      ownNames cenv (blockCtx (closureContext ixe t preA order) ixe order cB.refs blob) selves
        (fun n => (quotientKey ixe t n).map (evAddr ixe b)) m k →
      RecordReadings.sourceNames (fiberAliasAt ixe (roleAtMap t)) (evAddr ixe b) m k := by
  rintro m k hm (⟨-, rfl⟩ | h)
  · rfl
  · exact SingletonReads.agree (cB := cB) (blob := blob) P prelude corder canonical b bound m published m k hm (.inr h)

/-! ## The members' keys -/

/-- **In the closure's context a member reference is keyed as the record of the order that
resolves to it.** -/
theorem closure_memberKey_at {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {failures : Failures} {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ)
    {preA : Prelude .anon} (prelude : preludeFor t = .ok preA) (corder : ClosureOrder ixe (Seed ixe sub) order)
    (canonical : Stream.StoredCanonical ixe order) {a : Address} {c : Ixon.Constant} (ha : a ∈ order)
    (hc : recordAt ixe a = some c) {q : ConstRef Address} (hq : resolveSource (recordAt ixe) a c = some q) :
    (closureContext ixe t preA order).memberKey q = (closureContext ixe t preA order).keyAt a := by
  have compiled : compile env = .ok ixe := by unfold compile; rw [P.compiled]; rfl
  have auth := fun a c h => ClosureKeying.closure_authentic compiled P.evidence.2.1 prelude canonical (a := a) (c := c) h
  have hres := BlockContext.closure_resolve (t := t) (preA := preA) corder ha hc hq
  have hstore := ClosureKeying.closure_store (t := t) (preA := preA) corder.nodup ha hc
  have hq' : resolveSource (closureContext ixe t preA order).store a c = some q := by
    have h := hres
    unfold resolve at h
    rw [hstore] at h
    exact h
  have unique : ((Stream.decodedOf ixe order).map Prod.fst).Nodup := (Stream.decodedOf_keys ixe order).nodup corder.nodup
  have present : (a, c) ∈ Stream.decodedOf ixe order :=
    List.mem_filterMap.mpr ⟨a, ha, by simp [hc]⟩
  obtain ⟨a', ha'⟩ := ReaderClosureKeys.input_resolved_cached (md := .anon) t (Stream.decodedOf ixe order).toArray
    (preA.records ++ preA.evidence) (blobsOf ixe order) preA.blobs (hintsOf ixe)
    (Admission.projectionAddress Address.admissionHash) (by simpa only [List.toList_toArray] using unique)
    (by simpa only [List.mem_toArray] using present) hq'
  have ha'' : (closureContext ixe t preA order).keys.address[q]? = some a' := ha'
  have e : a' = a := ReadingKeys.resolve_inj auth ((closureContext ixe t preA order).keys.address_sound q a' ha'') hres
  rw [e] at ha''
  cases hrole : (closureContext ixe t preA order).roles.names[q]? with
  | some k =>
    rw [Ctx.memberKey_of_role hrole]
    symm
    rw [Ctx.keyAt_eq_ok]
    simp [keyOfAddress, hres, hrole]
  | none =>
    have hkey : (closureContext ixe t preA order).addressOf q = .ok a := by
      unfold Ctx.addressOf
      rw [ha'']
      rfl
    unfold Ctx.memberKey
    rw [hrole]
    simp only [hkey, bind, Except.bind]
    unfold Ctx.keyAt
    cases hb : (closureContext ixe t preA order).keys.byAddress[a]? with
    | some k => rfl
    | none => simp [hres, hrole, Mode.addressId?]

/-- A definition projection that resolves names its block's member at its index. -/
theorem resolveSource_dPrj {s : Store} {a : Address} {c : Ixon.Constant} {p : Ixon.DefinitionProj}
    (hi : c.info = .dPrj p) {q : ConstRef Address} (h : resolveSource s a c = some q) :
    q = .member p.block p.idx.toNat := by
  simp only [resolveSource, hi] at h
  revert h
  cases (emptyTables c) <;> simp [guard, bind, Option.bind]
  cases s p.block <;> simp
  rename_i cb
  cases cb.info <;> simp
  rename_i ms
  cases ms[p.idx.toNat]? <;> simp
  rename_i x
  cases x <;> simp [eq_comm]

/-- **A published member of a definition block**: its projection is a record of the order, resolves
to its position in the block, and the closure's context keys that position as the member's quotient
key renamed. -/
theorem member_key {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {failures : Failures} {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ)
    {preA : Prelude .anon} (prelude : preludeFor t = .ok preA) (corder : ClosureOrder ixe (Seed ixe sub) order)
    (canonical : Stream.StoredCanonical ixe order) (b : Ix.RoleEvidence.Bundle)
    (resolves : SingletonSegments.PublishedResolve ixe sub) {n : Ix.Name} {ci : Ix.ConstantInfo}
    (hn : (n, ci) ∈ sub.consts.toList) {Pa : Address} (haddr : ClosureLayout.addrOf ixe n = some Pa) {B : Address}
    {j : Nat} (hj : j < UInt64.size) {d : Ix.Def}
    (hrec : recordAt ixe Pa = some (MutualProjections.memberProjection B j.toUInt64 (.defn d))) :
    Pa ∈ order ∧
      resolveSource (recordAt ixe) Pa (MutualProjections.memberProjection B j.toUInt64 (.defn d)) =
        some (.member B j) ∧
      (closureContext ixe t preA order).memberKey (.member B j) = .ok ((quotientKey ixe t n).map (evAddr ixe b)) := by
  obtain ⟨named, hmem, hget⟩ := SourceStoredNames.stored_published P hn
  have hPa : named.addr = Pa := by
    unfold ClosureLayout.addrOf at haddr
    rw [hget] at haddr
    exact Option.some.inj haddr
  have ha : Pa ∈ order := (corder.complete _).mpr
    (.seed ⟨n, ci, named, SourceStoredNames.stored_get hn, hget, hPa⟩ (ClosureLayout.recordAt_contains hrec))
  have some := resolves n ci named hn hget _ (hPa ▸ hrec)
  rw [hPa] at some
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp some
  have hq' : q = .member B j := by
    rw [resolveSource_dPrj rfl hq]
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hj]
  subst hq'
  refine ⟨ha, hq, ?_⟩
  rw [closure_memberKey_at P prelude corder canonical ha hrec hq, ← hPa]
  exact ClosureKeying.closure_keyAt P prelude canonical b hmem
    (by rw [hPa]; exact BlockContext.closure_resolve corder ha hrec hq)

/-- **A claimed block of several definitions in the closure's order**: its record is a record of
the order, stored, and each member is published at its projection, a record of the order that
resolves to the member's position, which the closure's context keys as the member's quotient key
renamed. -/
theorem block_members {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {failures : Failures} {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ)
    {preA : Prelude .anon} (prelude : preludeFor t = .ok preA) (corder : ClosureOrder ixe (Seed ixe sub) order)
    (canonical : Stream.StoredCanonical ixe order) (b : Ix.RoleEvidence.Bundle)
    (resolves : SingletonSegments.PublishedResolve ixe sub) {defs : List Ix.Def} (two : 2 ≤ defs.length)
    (insub : ∀ j (hj : j < defs.length), ∃ ci, (defs[j].name, ci) ∈ sub.consts.toList)
    {context : CompileEnv × BlockEnv} {before after : BlockState} {output : BlockResult}
    (ran : rawRun (compileMutualBlock ((defs.map MutConst.defn).map ([·]))) context before = (.ok output, after))
    {cenvR : CompileEnv} {all : Ix.Set Ix.Name} {key : Ix.Name} {r : BlockResult} {cache : BlockState}
    {layout : Option Ixon.AuxLayout} (hr : runBlock cenvR all key = .ok (r, cache, layout))
    (pub : BlockPublication.Published ixe sub key r) (hrec : BlockRecords.recordsOf r = BlockRecords.recordsOf output) :
    output.blockAddr ∈ order ∧ recordAt ixe output.blockAddr = some output.block ∧
      ∀ j (hj : j < defs.length), ∃ Pa, ClosureLayout.addrOf ixe defs[j].name = some Pa ∧ Pa ∈ order ∧
        recordAt ixe Pa = some (MutualProjections.memberProjection output.blockAddr j.toUInt64 (.defn defs[j])) ∧
        resolveSource (recordAt ixe) Pa (MutualProjections.memberProjection output.blockAddr j.toUInt64 (.defn defs[j])) =
          some (.member output.blockAddr j) ∧
        (closureContext ixe t preA order).memberKey (.member output.blockAddr j) =
          .ok ((quotientKey ixe t defs[j].name).map (evAddr ixe b)) := by
  have hrec' := hrec
  simp only [BlockRecords.recordsOf, Prod.mk.injEq] at hrec'
  obtain ⟨hblock, -, haddr, -⟩ := hrec'
  have insub' : ∀ j (hj : j < defs.length), (sub.consts.get? defs[j].name).isSome = true := fun j hj => by
    obtain ⟨ci, hci⟩ := insub j hj
    rw [SourceStoredNames.stored_get hci]
    rfl
  obtain ⟨count, rows⟩ := BlockPublication.member_published hr pub two ran hrec insub'
  have stored : recordAt ixe output.blockAddr = some output.block := by
    rw [← haddr, ← hblock]
    exact BlockPublication.stored hr pub
  have each : ∀ j (hj : j < defs.length), ∃ Pa, ClosureLayout.addrOf ixe defs[j].name = some Pa ∧ Pa ∈ order ∧
      recordAt ixe Pa = some (MutualProjections.memberProjection output.blockAddr j.toUInt64 (.defn defs[j])) ∧
      resolveSource (recordAt ixe) Pa (MutualProjections.memberProjection output.blockAddr j.toUInt64 (.defn defs[j])) =
        some (.member output.blockAddr j) ∧
      (closureContext ixe t preA order).memberKey (.member output.blockAddr j) =
        .ok ((quotientKey ixe t defs[j].name).map (evAddr ixe b)) := by
    intro j hj
    obtain ⟨ha, hc⟩ := rows j hj
    rw [haddr] at ha hc
    obtain ⟨ci, hci⟩ := insub j hj
    obtain ⟨hPa, hq, hkey⟩ := member_key P prelude corder canonical b resolves hci ha (Nat.lt_trans hj count) hc
    exact ⟨_, ha, hPa, hc, hq, hkey⟩
  obtain ⟨P0, -, hP0, hc0, -, -⟩ := each 0 (by omega)
  refine ⟨?_, stored, each⟩
  by_cases e : output.blockAddr = P0
  · rw [e]
    exact hP0
  · exact (corder.complete _).mpr (.step ((corder.complete P0).mp hP0) ⟨_, hc0, .inl ⟨rfl, e⟩⟩)

/-! ## The block's reading in the closure's context -/

/-- **A compiled block of several definitions reads in the closure's context, from every state
related to quotient Source's, as quotient Source's group renamed.** The compile-side context is the
block's (`blockCtx`) over the compile's blobs, its names `ownNames`; the members' keys come from
their published projections (`block_members`). -/
theorem closure_block_reads {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {failures : Failures} {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ)
    {preA : Prelude .anon} (prelude : preludeFor t = .ok preA) (corder : ClosureOrder ixe (Seed ixe sub) order)
    (canonical : Stream.StoredCanonical ixe order) {b : Ix.RoleEvidence.Bundle}
    (hf : InjOn (evAddr ixe b) (QRepAt ixe (roleAtMap t))) (resolves : SingletonSegments.PublishedResolve ixe sub)
    {members : Array Ix.ConstantInfo} (two : 2 ≤ members.size) {defs : List Ix.Def}
    (views : List.Forall₂ (fun ci d => EmissionDispatch.sourceData ci = some d) members.toList defs)
    (insub : ∀ j (hj : j < defs.length), ∃ ci, (defs[j].name, ci) ∈ sub.consts.toList)
    (distinct : Canon.KeysDistinct (defs.map MutConst.defn))
    (exactNames : ∀ i (hi : i < defs.length) j (hj : j < defs.length) n,
      ConstOcc n defs[i].type ∨ ConstOcc n defs[i].value → ingressKey n = ingressKey defs[j].name → n = defs[j].name)
    {cenv : CompileEnv} {benv : BlockEnv} {output : BlockResult} {after : BlockState}
    (ran : rawRun (compileMutualBlock ((defs.map MutConst.defn).map ([·]))) (cenv, benv) {} = (.ok output, after))
    (fresh : ∀ d ∈ defs, cenv.nameToAddr.get? d.name = none)
    (unaliased : ∀ d ∈ defs, cenv.auxNameToAddr.get? d.name = none)
    {cenvR : CompileEnv} {all : Ix.Set Ix.Name} {key : Ix.Name} {r : BlockResult} {cache : BlockState}
    {layout : Option Ixon.AuxLayout} (hr : runBlock cenvR all key = .ok (r, cache, layout))
    (pub : BlockPublication.Published ixe sub key r) (hrec : BlockRecords.recordsOf r = BlockRecords.recordsOf output)
    (bound : BoundResolve ixe cenv)
    (blobs : ∀ a bytes, BlobWrites.readBlob cenv.blobs after a = some bytes → ixe.blobs.get? a = some bytes)
    (published : ∀ m a, (∃ (j : Nat) (hj : j < defs.length), GraphWalk.Refs m defs[j].type ∨ GraphWalk.Refs m defs[j].value) →
      lookupBinding cenv ({}, {}) m = some a →
        ∃ named', (m, named') ∈ ixe.named.toList ∧ named'.addr = a ∧ (sub.consts.get? m).isSome = true)
    {hints : CName .source → Option ReducibilityHint} {H : Nat → ReducibilityHint}
    (hinted : ∀ k (hk : k < defs.length),
      (closureContext ixe t preA order).hint (.member output.blockAddr k) = some (H k) ∧
        hints (ingressKey defs[k].name) = some (H k))
    {c : Ix.LeanIngress.Converted} (conv : Ix.LeanIngress.convertDefinitions members = .ok c)
    {stS : State .source}
    (ownersGood : ∀ k : Key .source, k.Good (KeyScope.ofId (QRepAt ixe (roleAtMap t))) → ∀ o,
      stS.projOwners[k]? = some o → o.Good (KeyScope.ofId (QRepAt ixe (roleAtMap t))))
    (good : ∀ qms, (c.withHints hints).quotient (fiberAliasAt ixe (roleAtMap t)) = .definitions qms →
      ∀ m ∈ qms.toList, m.cv.type.Good (KeyScope.ofId (QRepAt ixe (roleAtMap t))) ∧
        m.value.Good (KeyScope.ofId (QRepAt ixe (roleAtMap t))))
    {rS : Read .source}
    (lowered : Ix.LeanIngress.lower stS ((c.withHints hints).quotient (fiberAliasAt ixe (roleAtMap t))) = .ok rS)
    (levels : ∀ d ∈ rS.decls, DefinitionBlockReads.DeclNodup d) :
    ∀ stA : State .anon, StreamRename.StateRen (evAddr ixe b) (KeyScope.ofId (QRepAt ixe (roleAtMap t))) stS stA →
      ∃ rA, readRecord (closureContext ixe t preA order) stA output.blockAddr output.block = .ok rA ∧
        StreamRename.Plain rA ∧ rA.decls = rS.decls.map (Declaration.mapKeys (evAddr ixe b)) := by
  have hlen : members.size = defs.length := by
    simpa using DefinitionBlocks.forall₂_length views
  obtain ⟨hB, stored, each⟩ := block_members P prelude corder canonical b resolves (by omega) insub ran hr pub hrec
  exact DefinitionBlockReads.definition_block_reads (P := KeyScope.ofId (QRepAt ixe (roleAtMap t)))
    (fun _ _ => trivial) hf two views distinct exactNames (cenv, benv) rfl BlockStart.clean_empty ran
    (fun d hd => ⟨Std.HashMap.get?_eq_getElem?.trans Std.HashMap.getElem?_empty, fresh d hd⟩)
    (fun d hd => ⟨Std.HashMap.get?_eq_getElem?.trans Std.HashMap.getElem?_empty, unaliased d hd⟩)
    (cx₁ := blockCtx (closureContext ixe t preA order) ixe order output.block.refs (fun a => cenv.blobs.get? a))
    (fun _ => rfl)
    (own_external corder hB stored bound (fun m => ∃ (j : Nat) (hj : j < defs.length), defs[j].name = m)
      (fun m => (quotientKey ixe t m).map (evAddr ixe b)))
    (fun k hk => .inl ⟨⟨k, hk, rfl⟩, rfl⟩)
    (fun k hk n key hm hn => own_agree P prelude corder canonical b bound _ published n key ⟨k, hk, hm⟩ hn)
    (SingletonReads.lone_refs hB stored blobs)
    (fun k hk => by obtain ⟨_, -, -, -, -, hkey⟩ := each k hk; exact hkey)
    hinted conv ownersGood good lowered levels

/-! ## The segment -/

/-- **A segment that holds its partner record among records read to nothing reads as its Source
read**: a Source read of plain declarations whose collapse kept it whole (segment: the partner record
among inert records, read from every related state as the lowering renamed) or dropped it whole
(segment: nothing). -/
theorem partner_segment {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md} {cx : Ctx md'} {ixe : Ixon.Env}
    {stS : State md} {raw r : Read md} {B : Address} {c : Ixon.Constant} {seg : List Address}
    (plain : StreamRename.Plain raw) (collapse : r = raw ∨ r = { raw with decls := #[], generated := 0 })
    (basis : ∀ d ∈ raw.decls.toList, ∀ k, d ≠ .basisDecl k)
    (good : ∀ d ∈ raw.decls.toList, ∀ e ∈ CtxAgree.noteEntries d, e.1.Good P)
    (hc : recordAt ixe B = some c)
    (reads : ∀ stA : State md', StreamRename.StateRen f P stS stA →
      ∃ rA, readRecord cx stA B c = .ok rA ∧ StreamRename.Plain rA ∧ rA.decls = raw.decls.map (Declaration.mapKeys f))
    (kept : r = raw → ∃ before after, seg = before ++ B :: after ∧ InertAddrs ixe cx before ∧ InertAddrs ixe cx after)
    (dropped : r.decls = #[] → seg = []) :
    SegmentReads f P cx ixe stS r seg := by
  rcases collapse with rfl | rfl
  · obtain ⟨before, after, hseg, hb, ha⟩ := kept rfl
    refine .inr ⟨before, B, after, c, hseg, hc, ⟨basis, good, by simp [plain.blocks], by simp [plain.owners]⟩,
      fun stA hst => ?_, hb, ha⟩
    obtain ⟨rA, hr, pA, hdecls⟩ := reads stA hst
    exact ⟨rA, hr, ⟨⟨hdecls, by rw [pA.generated, plain.generated], by simp [pA.blocks, plain.blocks]⟩,
      by simp [pA.owners, plain.owners]⟩⟩
  · rw [dropped rfl]
    exact .inl ⟨⟨⟨rfl, plain.owners, plain.blocks⟩, rfl⟩, fun _ h => nomatch h⟩

/-- **Quotient Source's read of a group of several definitions**: plain, with one declaration per
member, none a basis block, each keyed by a member's ingress key renamed. -/
theorem block_read {ρ : Ix.LeanIngress.FiberMap} {hints : CName .source → Option ReducibilityHint}
    {H : Nat → ReducibilityHint} {members : Array Ix.ConstantInfo} (two : 2 ≤ members.size) {defs : List Ix.Def}
    (views : List.Forall₂ (fun ci d => EmissionDispatch.sourceData ci = some d) members.toList defs)
    (hinted : ∀ k (hk : k < defs.length), hints (ingressKey defs[k].name) = some (H k))
    {c : Ix.LeanIngress.Converted} (conv : Ix.LeanIngress.convertDefinitions members = .ok c)
    {stS : State .source} {rS : Read .source}
    (lowered : Ix.LeanIngress.lower stS ((c.withHints hints).quotient ρ) = .ok rS) :
    StreamRename.Plain rS ∧ ∀ d ∈ rS.decls.toList, (∀ k, d ≠ .basisDecl k) ∧
      ∀ e ∈ CtxAgree.noteEntries d, ∃ (j : Nat) (_ : j < defs.length),
        e.1 = Ix.LeanIngress.Key.subst ρ (ingressKey defs[j].name) := by
  have hlen : members.size = defs.length := by
    simpa using DefinitionBlocks.forall₂_length views
  obtain ⟨ms, order, hmsize, hms, hdef, rfl⟩ := DefinitionBlockReads.convertDefinitions_block conv two
  have hlt : ∀ k ∈ order.toList, k < defs.length := by
    intro k hk
    have := DefinitionOrder.defOrder_lt _ _ hdef k (Array.mem_toList_iff.mp hk)
    simp only [DefinitionBlocks.depsOf, Array.size_map] at this
    omega
  have nameOf : ∀ k (hk : k < defs.length), ms[k]!.cv.name = ingressKey defs[k].name := by
    intro k hk
    obtain ⟨s, v, t', v', -, -, -, -, -, hmk⟩ := hms k (by omega)
    have hm := Option.some.inj ((Array.getElem?_eq_getElem (by omega)).symm.trans hmk)
    rw [getElem!_pos ms k (by omega), hm]
    have view := DefinitionBlocks.forall₂_getElem views k (by simp; omega) hk
    simp only [Array.getElem_toList] at view
    rw [(RecordReadings.sourceData_facts view).1]
  rw [DefinitionBlockReads.quotient_defs (hints := hints) (H := H) fun k hk => by
    rw [nameOf k (hlt k (Array.mem_toList_iff.mpr hk))]
    exact hinted k (hlt k (Array.mem_toList_iff.mpr hk))] at lowered
  obtain ⟨ds, hds, plain, hF⟩ := DefinitionBlockReads.lower_defs lowered
  refine ⟨plain, fun d hd => ?_⟩
  rw [hds] at hd
  obtain ⟨m, hm, rw', hlow⟩ := ReaderUnits.forall₂_mem_right hF d (by simpa using hd)
  obtain ⟨basis, names⟩ := SingletonSegments.lowerDefinition_decl hlow
  rw [Array.toList_map] at hm
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hm
  refine ⟨basis, fun e he => ⟨k, hlt k hk, ?_⟩⟩
  rw [← nameOf k (hlt k hk), names e he, RecordReadings.quotientMember, RecordReadings.defMember_canon]
  rfl

/-- **A claimed member projection reads to nothing in the closure's context.** -/
theorem member_inert {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {failures : Failures} {t : RoleTable} {envQ : Env .source} (_P : Premises env roots sub ixe failures t envQ)
    {preA : Prelude .anon} (corder : ClosureOrder ixe (Seed ixe sub) order) {Pa B : Address} {j : UInt64}
    {d : Ix.Def} (hPo : Pa ∈ order) (hPc : recordAt ixe Pa = some (MutualProjections.memberProjection B j (.defn d)))
    {q : ConstRef Address}
    (hPq : resolveSource (recordAt ixe) Pa (MutualProjections.memberProjection B j (.defn d)) = some q) :
    InertAt (closureContext ixe t preA order) Pa (MutualProjections.memberProjection B j (.defn d)) := by
  have hres := BlockContext.closure_resolve (t := t) (preA := preA) corder hPo hPc hPq
  have hstore := ClosureKeying.closure_store (t := t) (preA := preA) corder.nodup hPo hPc
  have h2 : resolveSource (closureContext ixe t preA order).store Pa
      (MutualProjections.memberProjection B j (.defn d)) = some q := by
    have h := hres
    unfold resolve at h
    rw [hstore] at h
    exact h
  exact ClosureSegments.projection_inert _ _ _ (.inl ⟨_, rfl⟩) (by rw [h2]; rfl)

/-- **A group of several definitions' segment reads as quotient Source's read**, when the collapse
keeps the read whole or drops it whole, and a kept read's segment holds the block's record among
the members' projections. -/
theorem definition_block_segment {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {failures : Failures} {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ)
    {preA : Prelude .anon} (prelude : preludeFor t = .ok preA) (corder : ClosureOrder ixe (Seed ixe sub) order)
    (canonical : Stream.StoredCanonical ixe order) {b : Ix.RoleEvidence.Bundle}
    (hf : InjOn (evAddr ixe b) (QRepAt ixe (roleAtMap t))) (resolves : SingletonSegments.PublishedResolve ixe sub)
    {members : Array Ix.ConstantInfo} (two : 2 ≤ members.size) {defs : List Ix.Def}
    (views : List.Forall₂ (fun ci d => EmissionDispatch.sourceData ci = some d) members.toList defs)
    (insub : ∀ j (hj : j < defs.length), ∃ ci, (defs[j].name, ci) ∈ sub.consts.toList)
    (distinct : Canon.KeysDistinct (defs.map MutConst.defn))
    (exactNames : ∀ i (hi : i < defs.length) j (hj : j < defs.length) n,
      ConstOcc n defs[i].type ∨ ConstOcc n defs[i].value → ingressKey n = ingressKey defs[j].name → n = defs[j].name)
    {cenv : CompileEnv} {benv : BlockEnv} {output : BlockResult} {after : BlockState}
    (ran : rawRun (compileMutualBlock ((defs.map MutConst.defn).map ([·]))) (cenv, benv) {} = (.ok output, after))
    (fresh : ∀ d ∈ defs, cenv.nameToAddr.get? d.name = none)
    (unaliased : ∀ d ∈ defs, cenv.auxNameToAddr.get? d.name = none)
    {cenvR : CompileEnv} {all : Ix.Set Ix.Name} {key : Ix.Name} {r : BlockResult} {cache : BlockState}
    {layout : Option Ixon.AuxLayout} (hr : runBlock cenvR all key = .ok (r, cache, layout))
    (pub : BlockPublication.Published ixe sub key r) (hrec : BlockRecords.recordsOf r = BlockRecords.recordsOf output)
    (bound : BoundResolve ixe cenv)
    (blobs : ∀ a bytes, BlobWrites.readBlob cenv.blobs after a = some bytes → ixe.blobs.get? a = some bytes)
    (published : ∀ m a, (∃ (j : Nat) (hj : j < defs.length), GraphWalk.Refs m defs[j].type ∨ GraphWalk.Refs m defs[j].value) →
      lookupBinding cenv ({}, {}) m = some a →
        ∃ named', (m, named') ∈ ixe.named.toList ∧ named'.addr = a ∧ (sub.consts.get? m).isSome = true)
    {hints : CName .source → Option ReducibilityHint} {H : Nat → ReducibilityHint}
    (hinted : ∀ k (hk : k < defs.length),
      (closureContext ixe t preA order).hint (.member output.blockAddr k) = some (H k) ∧
        hints (ingressKey defs[k].name) = some (H k))
    {c : Ix.LeanIngress.Converted} (conv : Ix.LeanIngress.convertDefinitions members = .ok c)
    {stS : State .source}
    (ownersGood : ∀ k : Key .source, k.Good (KeyScope.ofId (QRepAt ixe (roleAtMap t))) → ∀ o,
      stS.projOwners[k]? = some o → o.Good (KeyScope.ofId (QRepAt ixe (roleAtMap t))))
    (good : ∀ qms, (c.withHints hints).quotient (fiberAliasAt ixe (roleAtMap t)) = .definitions qms →
      ∀ m ∈ qms.toList, m.cv.type.Good (KeyScope.ofId (QRepAt ixe (roleAtMap t))) ∧
        m.value.Good (KeyScope.ofId (QRepAt ixe (roleAtMap t))))
    {raw : Read .source}
    (lowered : Ix.LeanIngress.lower stS ((c.withHints hints).quotient (fiberAliasAt ixe (roleAtMap t))) = .ok raw)
    (levels : ∀ d ∈ raw.decls, DefinitionBlockReads.DeclNodup d)
    {rd : Read .source} (collapse : rd = raw ∨ rd = { raw with decls := #[], generated := 0 })
    {seg : List Address}
    (kept : rd = raw → ∃ before after, seg = before ++ output.blockAddr :: after ∧
      ∀ a ∈ before ++ after, ∃ (j : Nat) (_ : j < defs.length), ClosureLayout.addrOf ixe defs[j].name = some a)
    (empty : rd.decls = #[] → seg = []) :
    SegmentReads (evAddr ixe b) (KeyScope.ofId (QRepAt ixe (roleAtMap t))) (closureContext ixe t preA order) ixe
      stS rd seg := by
  have hlen : members.size = defs.length := by
    simpa using DefinitionBlocks.forall₂_length views
  obtain ⟨-, stored, each⟩ := block_members P prelude corder canonical b resolves (by omega) insub ran hr pub hrec
  have reads := closure_block_reads P prelude corder canonical hf resolves two views insub distinct exactNames ran
    fresh unaliased hr pub hrec bound blobs published hinted conv ownersGood good lowered levels
  obtain ⟨plain, scope⟩ := block_read two views (fun k hk => (hinted k hk).2) conv lowered
  refine partner_segment plain collapse (fun d hd => (scope d hd).1) (fun d hd e he => ?_) stored reads
    (fun e => ?_) empty
  · obtain ⟨j, hj, he'⟩ := (scope d hd).2 e he
    rw [he']
    obtain ⟨ci, hci⟩ := insub j hj
    obtain ⟨named, hmem, -⟩ := SourceStoredNames.stored_published P hci
    exact SingletonSegments.qkey_good (defaultTable_check P.table) P.bound P.agree hmem
  · obtain ⟨before, after', hseg, hin⟩ := kept e
    have inert : ∀ a ∈ before ++ after', ∀ c', recordAt ixe a = some c' →
        InertAt (closureContext ixe t preA order) a c' := by
      intro a ha c' hc'
      obtain ⟨j, hj, haj⟩ := hin a ha
      obtain ⟨Pa, hPa, hPo, hPc, hPq, -⟩ := each j hj
      rw [hPa, Option.some.injEq] at haj
      subst haj
      rw [hPc, Option.some.injEq] at hc'
      subst hc'
      exact member_inert P corder hPo hPc hPq
    exact ⟨before, after', hseg, fun a ha => inert a (List.mem_append_left _ ha),
      fun a ha => inert a (List.mem_append_right _ ha)⟩

/-! ## Where a definition block's segment lies -/

/-- A group of definitions, one per class, has one definition shape per member. -/
theorem heads_defn : ∀ l : List Ix.Def,
    (((l.map MutConst.defn).map ([·])).filterMap List.head?).map ProjectionLayout.sourceShape =
      l.map fun _ => ProjectionLayout.MemberShape.defn
  | [] => rfl
  | _ :: ds => congrArg (List.cons _) (heads_defn ds)

/-- **A compiled block of several definitions is a block of definitions**, one per member. -/
theorem block_info {context : CompileEnv × BlockEnv} {before after : BlockState} {output : BlockResult}
    {defs : List Ix.Def} (two : 2 ≤ defs.length)
    (ran : rawRun (compileMutualBlock ((defs.map MutConst.defn).map ([·]))) context before = (.ok output, after)) :
    ∃ ms : Array Ixon.MutConst, output.block.info = .muts ms ∧ ms.size = defs.length ∧
      ∀ x ∈ ms, ∃ d, x = .defn d := by
  have shape := ProjectionLayout.mutual_block_shape _ context before output after ran
  rw [heads_defn] at shape
  cases hi : output.block.info with
  | muts ms =>
    rw [hi] at shape
    simp only [ProjectionLayout.blockShape, Option.some.injEq] at shape
    refine ⟨ms, rfl, by simpa using congrArg List.length shape, fun x hx => ?_⟩
    have hx' : ProjectionLayout.memberShape x ∈ ms.toList.map ProjectionLayout.memberShape :=
      List.mem_map.mpr ⟨x, Array.mem_toList_iff.mpr hx, rfl⟩
    rw [shape] at hx'
    obtain ⟨_, _, h⟩ := List.mem_map.mp hx'
    cases x with
    | defn d => exact ⟨d, rfl⟩
    | indc _ => simp [ProjectionLayout.memberShape] at h
    | recr _ => simp [ProjectionLayout.memberShape] at h
  | defn _ | recr _ =>
    rw [hi] at shape
    simp only [ProjectionLayout.blockShape, Option.some.injEq] at shape
    have := congrArg List.length shape
    simp at this
    omega
  | axio _ | quot _ | dPrj _ | iPrj _ | rPrj _ | cPrj _ =>
    rw [hi] at shape
    simp [ProjectionLayout.blockShape] at shape

/-- **A record a block of definitions owns, and that resolves, names one of the block's
members.** -/
theorem owned_member {B A : Address} {cB cm : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hB : recordAt ixe B = some cB) (hinfo : cB.info = .muts ms) (hdefs : ∀ x ∈ ms, ∃ d, x = .defn d)
    (hown : ownerOf A cm = B) {q : ConstRef Address} (hq : resolveSource (recordAt ixe) A cm = some q)
    (ne : A ≠ B) : ∃ i, i < ms.size ∧ q = .member B i := by
  have hidx : ∀ (k : UInt64) (y : Ixon.MutConst), ms[k.toNat]? = some y → k.toNat < ms.size ∧ ∃ d, y = .defn d :=
    fun k y h => ⟨(Array.getElem?_eq_some_iff.mp h).1, hdefs y (Array.mem_of_getElem? h)⟩
  cases hi : cm.info with
  | defn _ | recr _ | axio _ | quot _ | muts _ =>
    simp only [ownerOf, hi] at hown
    exact absurd hown ne
  | dPrj p | iPrj p | rPrj p | cPrj p =>
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
    obtain ⟨hlt, d, rfl⟩ := hidx _ _ hy
    first
      | (cases hq; done)
      | (cases hq; exact ⟨_, hlt, rfl⟩)

/-- **A closure name whose records include a block of definitions' record is published where one of
its members is**: a name at the block record itself would not resolve, and a name at a record the
block owns resolves to a member's position, which only that member's projection resolves to. -/
theorem member_of_block {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {failures : Failures} {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ)
    {preA : Prelude .anon} (prelude : preludeFor t = .ok preA) (corder : ClosureOrder ixe (Seed ixe sub) order)
    (canonical : Stream.StoredCanonical ixe order) (resolves : SingletonSegments.PublishedResolve ixe sub)
    {defs : List Ix.Def} {B : Address} {cB : Ixon.Constant} {ms : Array Ixon.MutConst}
    (stored : recordAt ixe B = some cB) (hinfo : cB.info = .muts ms) (hms : ms.size = defs.length)
    (hdefs : ∀ x ∈ ms, ∃ d, x = .defn d)
    (each : ∀ j (hj : j < defs.length), ∃ Pa c, ClosureLayout.addrOf ixe defs[j].name = some Pa ∧ Pa ∈ order ∧
      recordAt ixe Pa = some c ∧ resolveSource (recordAt ixe) Pa c = some (.member B j))
    {m : Ix.Name} {cim : Ix.ConstantInfo} (hcim : (m, cim) ∈ sub.consts.toList)
    (hBm : B ∈ ClosureLayout.nameRecords ixe m) :
    ∃ (i : Nat) (_ : i < defs.length), ClosureLayout.addrOf ixe defs[i].name = ClosureLayout.addrOf ixe m := by
  have compiled : compile env = .ok ixe := by unfold compile; rw [P.compiled]; rfl
  have auth := fun a c h => ClosureKeying.closure_authentic compiled P.evidence.2.1 prelude canonical (a := a) (c := c) h
  obtain ⟨namedm, -, hgetm⟩ := SourceStoredNames.stored_published P hcim
  have hm : ClosureLayout.addrOf ixe m = some namedm.addr := by
    unfold ClosureLayout.addrOf
    rw [hgetm]
    rfl
  -- a name at the block's record would not resolve
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
      obtain ⟨i, hi, rfl⟩ := owned_member stored hinfo hdefs e.symm hq notAt
      have hi' : i < defs.length := hms ▸ hi
      obtain ⟨Pi, ci, hPi, hPio, hPic, hPiq⟩ := each i hi'
      have hAo : namedm.addr ∈ order := (corder.complete _).mpr
        (.seed ⟨m, cim, namedm, SourceStoredNames.stored_get hcim, hgetm, rfl⟩ (ClosureLayout.recordAt_contains hcm))
      have e₁ := BlockContext.closure_resolve (t := t) (preA := preA) corder hAo hcm hq
      have e₂ := BlockContext.closure_resolve (t := t) (preA := preA) corder hPio hPic hPiq
      exact ⟨i, hi', by rw [hPi, hm, ReadingKeys.resolve_inj auth e₁ e₂]⟩

/-- **No earlier lowered group holds a kept definition block's record**: an earlier name whose
records include it is published where a member is (`member_of_block`), so it has that member's
quotient key, which the block's read keeps and no earlier read declares (`Steps`). -/
theorem block_fresh {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {failures : Failures} {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ)
    {hints : CName .source → Option ReducibilityHint} {start : State .source} {ls : List SourcePrelude.Scheduled}
    {rs : List (Read .source)} (steps : ClosureLayout.Steps (ClosureLayout.quotientGraph ixe t hints sub) start ls rs)
    (inTrace : ∀ y ∈ ls, y ∈ (Ix.LeanIngress.scheduleOf (ClosureLayout.quotientGraph ixe t hints sub)).zipIdx.toList)
    {ℓ : Nat} {y : SourcePrelude.Scheduled} {r : Read .source} (hy : ls[ℓ]? = some y) (hr : rs[ℓ]? = some r)
    {defs : List Ix.Def} (insub : ∀ j (hj : j < defs.length), ∃ ci, (defs[j].name, ci) ∈ sub.consts.toList)
    {B : Address}
    (member : ∀ m cim, (m, cim) ∈ sub.consts.toList → B ∈ ClosureLayout.nameRecords ixe m →
      ∃ (i : Nat) (_ : i < defs.length), ClosureLayout.addrOf ixe defs[i].name = ClosureLayout.addrOf ixe m)
    (hdecl : ∀ j (hj : j < defs.length),
      ∃ d ∈ r.decls.toList, ClosureLayout.qkey (fiberAliasAt ixe (roleAtMap t)) defs[j].name ∈ d.names) :
    B ∉ ((ls.map fun y =>
      ClosureLayout.groupRecords ixe (ClosureLayout.namesAt (ClosureLayout.quotientGraph ixe t hints sub) y)).take ℓ).flatten := by
  obtain ⟨hlen, stepsAt⟩ := steps
  have tb := tableBound_of (defaultTable_check P.table) P.bound
  intro hprev
  rw [← List.map_take] at hprev
  obtain ⟨C, hCm, hBC⟩ := List.mem_flatten.mp hprev
  obtain ⟨y', hy'm, rfl⟩ := List.mem_map.mp hCm
  obtain ⟨j, hj, hjy⟩ := List.mem_iff_getElem.mp hy'm
  have hjℓ : j < ℓ := by simp at hj; omega
  have hℓ : ℓ < ls.length := (List.getElem?_eq_some_iff.mp hy).1
  have hy' : ls[j]? = some y' := by rw [← hjy, List.getElem_take]; exact List.getElem?_eq_getElem _
  obtain ⟨r', hr'⟩ : ∃ r', rs[j]? = some r' := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨conv', raw', -, -, -, -, -, hc', hl', -, -, hraw', -⟩ := stepsAt j y' r' hy' hr'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, keptFresh⟩ := stepsAt ℓ y r hy hr
  have hy'x := inTrace y' (List.mem_of_getElem? hy')
  obtain ⟨m, hm, hBm⟩ := List.mem_flatMap.mp hBC
  have hm' := Array.mem_toList_iff.mp hm
  -- `m`'s quotient key is declared before the block's read
  obtain ⟨d, hd, hkd⟩ := ClosureLayout.lowered_declares hy'x hc' hl' m hm'
  obtain ⟨d', hd', hkd'⟩ := hraw' d hd _ hkd
  have hd'ℓ : d' ∈ (rs.take ℓ).flatMap (·.decls.toList) := by
    obtain ⟨r₀, hr₀, hdr⟩ := List.mem_flatMap.mp hd'
    have htk : rs.take (j + 1) = (rs.take ℓ).take (j + 1) := by rw [List.take_take]; congr 1; omega
    rw [htk] at hr₀
    exact List.mem_flatMap.mpr ⟨r₀, List.mem_of_mem_take hr₀, hdr⟩
  -- `m` is a published closure name, published where a member is
  obtain ⟨gr', c', hgr', hcv', -⟩ := ClosureLayout.scheduled_conversion hy'x hc'
  have hnm' : ClosureLayout.namesAt (ClosureLayout.quotientGraph ixe t hints sub) y' = gr'.names := by
    unfold ClosureLayout.namesAt; rw [ClosureLayout.getElem!_of_getElem? hgr']
  obtain ⟨cim, hcim⟩ := ClosureLayout.converted_names_stored P hgr' hcv' m (hnm' ▸ hm')
  obtain ⟨namedm, hmm, hgetm⟩ := SourceStoredNames.stored_published P hcim
  obtain ⟨i, hi, hPi⟩ := member m cim hcim hBm
  -- so it has that member's quotient key
  obtain ⟨ci, hci⟩ := insub i hi
  obtain ⟨namedi, hmi, hgeti⟩ := SourceStoredNames.stored_published P hci
  have hai : namedi.addr = namedm.addr := by
    unfold ClosureLayout.addrOf at hPi
    rw [hgeti, hgetm] at hPi
    exact Option.some.inj hPi
  have hkey : ClosureLayout.qkey (fiberAliasAt ixe (roleAtMap t)) m =
      ClosureLayout.qkey (fiberAliasAt ixe (roleAtMap t)) defs[i].name :=
    Ix.LeanIngress.fiberAliasAt_addr_inj tb (by rw [P.agree m namedm hmm]) (by rw [P.agree _ namedi hmi, hai])
  obtain ⟨dn, hdn, hkdn⟩ := hdecl i hi
  exact keptFresh dn hdn _ hkdn d' hd'ℓ (hkey ▸ hkd')

/-- **A filtered segment that holds `B` holds it once, among elements its candidates allow**: the
order restricted to candidates `C` not in `D`, when `B` is a candidate not in `D` and every other
candidate satisfies `Q`. -/
theorem filter_place {L : List Address} (hnd : L.Nodup) {C D : List Address} {B : Address} {Q : Address → Prop}
    (hB : B ∈ L) (inC : B ∈ C) (notD : B ∉ D) (onC : ∀ a ∈ C, a = B ∨ Q a) :
    ∃ s t, L.filter (fun a => decide (a ∈ C ∧ a ∉ [] ++ D)) = s ++ B :: t ∧ ∀ a ∈ s ++ t, Q a := by
  have hBf : B ∈ L.filter (fun a => decide (a ∈ C ∧ a ∉ [] ++ D)) :=
    List.mem_filter.mpr ⟨hB, by simpa using ⟨inC, notD⟩⟩
  obtain ⟨s, t, hst⟩ := List.append_of_mem hBf
  have hnd' := hst ▸ hnd.filter (fun a => decide (a ∈ C ∧ a ∉ [] ++ D))
  refine ⟨s, t, hst, fun a ha => ?_⟩
  have ha' : a ∈ L.filter (fun a => decide (a ∈ C ∧ a ∉ [] ++ D)) := by
    rw [hst]
    rcases List.mem_append.mp ha with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  have haC : a ∈ C := (of_decide_eq_true (List.mem_filter.mp ha').2).1
  refine (onC a haC).resolve_left fun e => ?_
  subst e
  obtain ⟨-, hBt, hdisj⟩ := List.nodup_append.mp hnd'
  rcases List.mem_append.mp ha with h | h
  · exact hdisj _ h _ List.mem_cons_self rfl
  · exact (List.nodup_cons.mp hBt).1 h

/-- **A kept definition block's segment holds its record among its members' projections.** -/
theorem block_place {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {failures : Failures} {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ)
    {preA : Prelude .anon} (prelude : preludeFor t = .ok preA) (corder : ClosureOrder ixe (Seed ixe sub) order)
    (canonical : Stream.StoredCanonical ixe order) (b : Ix.RoleEvidence.Bundle)
    {hints : CName .source → Option ReducibilityHint} {start : State .source} {ls : List SourcePrelude.Scheduled}
    {rs : List (Read .source)} (steps : ClosureLayout.Steps (ClosureLayout.quotientGraph ixe t hints sub) start ls rs)
    (inTrace : ∀ y ∈ ls, y ∈ (Ix.LeanIngress.scheduleOf (ClosureLayout.quotientGraph ixe t hints sub)).zipIdx.toList)
    {L : List Address} (hnd : L.Nodup) (hmem : ∀ a, a ∈ L ↔ ixe.consts.contains a = true)
    (resolves : SingletonSegments.PublishedResolve ixe sub) {ℓ : Nat} {y : SourcePrelude.Scheduled}
    {r : Read .source} (hy : ls[ℓ]? = some y) (hr : rs[ℓ]? = some r)
    {defs : List Ix.Def} (two : 2 ≤ defs.length)
    (hnames : ∀ n, n ∈ ClosureLayout.namesAt (ClosureLayout.quotientGraph ixe t hints sub) y ↔
      ∃ (j : Nat) (_ : j < defs.length), defs[j].name = n)
    (insub : ∀ j (hj : j < defs.length), ∃ ci, (defs[j].name, ci) ∈ sub.consts.toList)
    {context : CompileEnv × BlockEnv} {before after : BlockState} {output : BlockResult}
    (ran : rawRun (compileMutualBlock ((defs.map MutConst.defn).map ([·]))) context before = (.ok output, after))
    {cenvR : CompileEnv} {all : Ix.Set Ix.Name} {key : Ix.Name} {r' : BlockResult} {cache : BlockState}
    {layout : Option Ixon.AuxLayout} (hr' : runBlock cenvR all key = .ok (r', cache, layout))
    (pub : BlockPublication.Published ixe sub key r') (hrec : BlockRecords.recordsOf r' = BlockRecords.recordsOf output)
    (hdecl : ∀ j (hj : j < defs.length),
      ∃ d ∈ r.decls.toList, ClosureLayout.qkey (fiberAliasAt ixe (roleAtMap t)) defs[j].name ∈ d.names) :
    ∃ before after, (ClosureLayout.segmentsOf L (ls.map fun y =>
        ClosureLayout.groupRecords ixe (ClosureLayout.namesAt (ClosureLayout.quotientGraph ixe t hints sub) y)) [])[ℓ]? =
          some (before ++ output.blockAddr :: after) ∧
      ∀ a ∈ before ++ after, ∃ (j : Nat) (_ : j < defs.length), ClosureLayout.addrOf ixe defs[j].name = some a := by
  obtain ⟨-, stored, each⟩ := block_members P prelude corder canonical b resolves two insub ran hr' pub hrec
  obtain ⟨ms, hinfo, hms, hdefs⟩ := block_info two ran
  have each' : ∀ j (hj : j < defs.length), ∃ Pa c, ClosureLayout.addrOf ixe defs[j].name = some Pa ∧ Pa ∈ order ∧
      recordAt ixe Pa = some c ∧ resolveSource (recordAt ixe) Pa c = some (.member output.blockAddr j) := by
    intro j hj
    obtain ⟨Pa, hPa, hPo, hPc, hPq, -⟩ := each j hj
    exact ⟨Pa, _, hPa, hPo, hPc, hPq⟩
  -- a member's records are its projection and the block
  have recs : ∀ j (hj : j < defs.length) Pa, ClosureLayout.addrOf ixe defs[j].name = some Pa →
      ClosureLayout.nameRecords ixe defs[j].name = [Pa, output.blockAddr] := by
    intro j hj Pa hPa
    obtain ⟨Pa', hPa', -, hPc, -⟩ := each j hj
    rw [hPa, Option.some.injEq] at hPa'
    subst hPa'
    simp only [ClosureLayout.nameRecords, hPa, ClosureLayout.blockAt, hPc]
    rfl
  have inC : ∀ a ∈ ClosureLayout.groupRecords ixe (ClosureLayout.namesAt (ClosureLayout.quotientGraph ixe t hints sub) y),
      a = output.blockAddr ∨ ∃ (j : Nat) (_ : j < defs.length), ClosureLayout.addrOf ixe defs[j].name = some a := by
    intro a ha
    obtain ⟨n, hn, ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨j, hj, rfl⟩ := (hnames n).mp (Array.mem_toList_iff.mp hn)
    obtain ⟨Pa, hPa, -⟩ := each j hj
    rw [recs j hj Pa hPa] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact .inr ⟨j, hj, hPa⟩
    · exact .inl rfl
  have inB : output.blockAddr ∈
      ClosureLayout.groupRecords ixe (ClosureLayout.namesAt (ClosureLayout.quotientGraph ixe t hints sub) y) := by
    obtain ⟨Pa, hPa, -⟩ := each 0 (by omega)
    refine List.mem_flatMap.mpr ⟨defs[0].name, Array.mem_toList_iff.mpr ((hnames _).mpr ⟨0, by omega, rfl⟩), ?_⟩
    rw [recs 0 (by omega) Pa hPa]
    simp
  have fresh := block_fresh P steps inTrace hy hr insub
    (fun m cim hcim hBm => member_of_block P prelude corder canonical resolves stored hinfo hms hdefs each' hcim hBm)
    hdecl
  have hC : (ls.map fun y =>
      ClosureLayout.groupRecords ixe (ClosureLayout.namesAt (ClosureLayout.quotientGraph ixe t hints sub) y))[ℓ]? =
        some (ClosureLayout.groupRecords ixe (ClosureLayout.namesAt (ClosureLayout.quotientGraph ixe t hints sub) y)) := by
    rw [List.getElem?_map, hy]
    rfl
  rw [ClosureLayout.segmentsOf_get L _ [] ℓ _ hC]
  obtain ⟨s, t', hst, hin⟩ := filter_place hnd ((hmem _).mpr (ClosureLayout.recordAt_contains stored)) inB fresh inC
  exact ⟨s, t', congrArg some hst, hin⟩

/--
info: 'Ix.Cert.DefinitionSegments.closure_block_reads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closure_block_reads

/--
info: 'Ix.Cert.DefinitionSegments.block_place' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms block_place

/--
info: 'Ix.Cert.DefinitionSegments.definition_block_segment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms definition_block_segment

end Ix.Cert.DefinitionSegments
