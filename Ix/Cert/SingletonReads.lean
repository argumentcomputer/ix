import Ix.Cert.BlockContext
import Ix.Cert.BlockLayout
import Ix.Cert.RecordReadings
import Ix.Cert.BlockStart

/-! # A compiled singleton reads in the closure's context as quotient Source's unit renamed

`RecordReadings` reads a compiled definition, axiom or quotient constant in the closure's context,
given a compile-side reading context `cx₁` and what it must satisfy. This module supplies them
from the closure (`closure_definition_reads`, `closure_axiom_reads`, `closure_quotient_reads`):

* `cx₁` is the block's context `BlockContext.blockCtx` at the record's references and the compile's
  blobs, and the names are `blockNames`: the constant's own name at its key, and every name the
  compile binds at the key `cx₁` reads at its binding. `cx₁` keys every binding (`external`, from
  `BlockContext.BoundResolve`); at a mentioned closure name it reads the name's quotient key
  renamed (`agree`, by `ClosureKeying.closure_keyAt`).
* The record is a lone record (`lone_of`): the block compile built it (`BlockLayout.ResultShape`),
  so it is no projection, and the artifact publishes an input name at it, so it is no block
  (`publishedReadable`). So its member is keyed as its address, in both contexts
  (`BlockContext.blockCtx_memberKey`, `BlockContext.closure_memberKey`).
* The closure's context reads the record's literal blobs as the compile does, when the artifact
  stores the blobs the compile read (`closure_blob`). -/

namespace Ix.Cert.SingletonReads

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState
open Ix.Cert.BlockContext (blockCtx blockStore BoundResolve Kept lone)
open Ix.LeanIngress (evAddr QRepAt roleAtMap fiberAliasAt ingressKey)

variable {ixe : Ixon.Env} {order : List Address}

/-! ## The closure's blobs -/

theorem fold_insert_keep : ∀ (l : List Address) {s : Std.HashSet Address} {x : Address}, s.contains x = true →
    (l.foldl (·.insert ·) s).contains x = true
  | [], _, _, h => h
  | _ :: l, _, _, h => fold_insert_keep l (by rw [Std.HashSet.contains_insert]; simp [h])

theorem fold_insert_has : ∀ (l : List Address) (s : Std.HashSet Address) {x : Address}, x ∈ l →
    (l.foldl (·.insert ·) s).contains x = true
  | [], _, _, h => nomatch h
  | y :: l, s, x, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact fold_insert_keep l (by rw [Std.HashSet.contains_insert]; simp)
    · exact fold_insert_has l _ h

theorem used_keep (ixe : Ixon.Env) : ∀ (l : List Address) {s : Std.HashSet Address} {x : Address}, s.contains x = true →
    (l.foldl (fun s a => match recordAt ixe a with
      | some c => c.refs.foldl (·.insert ·) s
      | none => s) s).contains x = true
  | [], _, _, h => h
  | a :: l, s, x, h => by
    rw [List.foldl_cons]
    refine used_keep ixe l ?_
    cases recordAt ixe a with
    | none => exact h
    | some c => dsimp only; rw [← Array.foldl_toList]; exact fold_insert_keep _ h

theorem used_has (ixe : Ixon.Env) {B : Address} {c : Ixon.Constant} (hc : recordAt ixe B = some c) {x : Address}
    (hx : x ∈ c.refs) : ∀ (l : List Address) (s : Std.HashSet Address), B ∈ l →
    (l.foldl (fun s a => match recordAt ixe a with
      | some c => c.refs.foldl (·.insert ·) s
      | none => s) s).contains x = true
  | [], _, h => nomatch h
  | a :: l, s, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · refine used_keep ixe l ?_
      rw [hc]; dsimp only; rw [← Array.foldl_toList]
      exact fold_insert_has _ _ (Array.mem_toList_iff.mpr hx)
    · exact used_has ixe hc hx l _ h

/-- **The closure's context reads a blob a record of the order references as the artifact
stores it.** -/
theorem closure_blob {t : RoleTable} {preA : Prelude .anon} {B : Address} {c : Ixon.Constant} (hB : B ∈ order)
    (hc : recordAt ixe B = some c) {a : Address} (ha : a ∈ c.refs) {bytes : ByteArray}
    (hb : ixe.blobs.get? a = some bytes) : (closureContext ixe t preA order).blob a = some bytes := by
  have hmem : (a, bytes) ∈ blobsOf ixe order := by
    unfold blobsOf
    refine List.mem_filter.mpr ⟨Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr ?_, used_has ixe hc ha order {} hB⟩
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hb
  change ((blobsOf ixe order ++ preA.blobs).foldl EvidenceTransfer.firstStep {})[a]? = some bytes
  rw [EvidenceTransfer.firstFold_get, EvidenceTransfer.lookup_eq_find, List.find?_append]
  simp only [Std.HashMap.getElem?_empty]
  cases hf : (blobsOf ixe order).find? (·.1 == a) with
  | some e =>
    obtain ⟨y, v⟩ := e
    have hy0 := List.find?_some hf
    have hy : y = a := beq_iff_eq.mp hy0
    subst hy
    have hm := List.mem_of_find?_eq_some hf
    unfold blobsOf at hm
    have hget : ixe.blobs.get? y = some v := by
      rw [Std.HashMap.get?_eq_getElem?]
      exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp (List.mem_filter.mp hm).1
    rw [hb] at hget
    cases hget
    rfl
  | none =>
    have := List.find?_eq_none.mp hf (a, bytes) hmem
    simp at this

/-! ## The names a block is read at -/

/-- **The names a block compiled at `cenv` is read at**: the constant's own name at its key, and
every name the compile binds at the key the block's context reads at its binding. -/
def blockNames (cenv : CompileEnv) (cx₁ : Ctx .anon) (self : Ix.Name) (selfKey : CName .anon) (m : Ix.Name)
    (k : CName .anon) : Prop :=
  (m = self ∧ k = selfKey) ∨ ∃ a, lookupBinding cenv {} m = some a ∧ cx₁.keyAt a = .ok k

/-- **The block's context keys every name the compile binds.** -/
theorem external {t : RoleTable} {preA : Prelude .anon} {S : Address → Prop} (corder : ClosureOrder ixe S order)
    {blob : Address → Option ByteArray} {B : Address} {cB : Ixon.Constant} (hB : B ∈ order)
    (hcB : recordAt ixe B = some cB) {cenv : CompileEnv} (bound : BoundResolve ixe cenv) (self : Ix.Name)
    (selfKey : CName .anon) :
    BindingsCorrect cenv {} (blockCtx (closureContext ixe t preA order) ixe order cB.refs blob)
      (blockNames cenv (blockCtx (closureContext ixe t preA order) ixe order cB.refs blob) self selfKey) := by
  intro m a hb
  obtain ⟨c, hc, hres⟩ := bound m a hb
  obtain ⟨k, hk⟩ := BlockContext.keyAt_stored corder hB hcB hc hres
  exact ⟨k, hk, .inr ⟨a, hb, hk⟩⟩

set_option maxRecDepth 4096 in
/-- **At a mentioned closure name, the block's names are quotient Source's names renamed**, when
the compile binds the name at its published address. -/
theorem agree {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {failures : Failures}
    {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ) {preA : Prelude .anon}
    (prelude : preludeFor t = .ok preA) (corder : ClosureOrder ixe (Seed ixe sub) order)
    (canonical : Stream.StoredCanonical ixe order) (b : Ix.RoleEvidence.Bundle) {blob : Address → Option ByteArray}
    {cB : Ixon.Constant} {cenv : CompileEnv} (bound : BoundResolve ixe cenv) (self : Ix.Name)
    {M : Ix.Name → Prop}
    (published : ∀ m a, M m → lookupBinding cenv {} m = some a →
      ∃ named, (m, named) ∈ ixe.named.toList ∧ named.addr = a ∧ (sub.consts.get? m).isSome = true) :
    ∀ m k, M m →
      blockNames cenv (blockCtx (closureContext ixe t preA order) ixe order cB.refs blob) self
        ((quotientKey ixe t self).map (evAddr ixe b)) m k →
      RecordReadings.sourceNames (fiberAliasAt ixe (roleAtMap t)) (evAddr ixe b) m k := by
  rintro m k hm (⟨rfl, rfl⟩ | ⟨a, hb, hk⟩)
  · rfl
  · obtain ⟨named, hmem, rfl, hsub⟩ := published m _ hm hb
    obtain ⟨c, hc, hres⟩ := bound m _ hb
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hres
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hsub
    have hget : ixe.named.get? m = some named := by
      rw [Std.HashMap.get?_eq_getElem?]
      exact (Std.HashMap.mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some.mp hmem).2
    have ha : named.addr ∈ order :=
      (corder.complete _).mpr (.seed ⟨m, ci, named, hci, hget, rfl⟩ (ClosureLayout.recordAt_contains hc))
    have h1 := (BlockContext.keyAt_iff (refs := cB.refs) (blob := blob) corder ha hc).mp hk
    rw [ClosureKeying.closure_keyAt P prelude canonical b hmem (BlockContext.closure_resolve corder ha hc hq)] at h1
    exact (Except.ok.inj h1).symm

/-! ## The record -/

/-- A built record that is no block is a lone record. -/
theorem lone_of {c : Ixon.Constant} (built : BlockLayout.Built c) (nb : ∀ ms, c.info ≠ .muts ms) :
    lone c.info = true := by
  have h1 := built.owner ⟨⟨#[]⟩⟩
  have h2 := built.owner ⟨⟨#[0]⟩⟩
  have apart : (⟨⟨#[]⟩⟩ : Address) ≠ ⟨⟨#[0]⟩⟩ := fun e => by
    have := congrArg (fun a : Address => a.hash.size) e
    exact absurd this (by decide)
  cases hi : c.info with
  | defn _ | recr _ | axio _ | quot _ => rfl
  | muts ms => exact absurd hi (nb ms)
  | dPrj p | iPrj p | rPrj p | cPrj p =>
    simp only [ownerOf, hi] at h1 h2
    exact absurd (h1.symm.trans h2) apart

/-- **The closure's context around a compiled lone record**: the record is lone and stored in the
closure's store, the closure keys its member as its name's quotient key renamed, and so does the
block's context. -/
theorem lone_keys {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {failures : Failures}
    {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ) {preA : Prelude .anon}
    (prelude : preludeFor t = .ok preA) (corder : ClosureOrder ixe (Seed ixe sub) order)
    (canonical : Stream.StoredCanonical ixe order) (b : Ix.RoleEvidence.Bundle) {blob : Address → Option ByteArray}
    {output : BlockResult} (shape : BlockLayout.ResultShape output) (hB : output.blockAddr ∈ order)
    (stored : recordAt ixe output.blockAddr = some output.block) {n : Ix.Name} {named : Ixon.Named}
    (hn : (n, named) ∈ ixe.named.toList) (haddr : named.addr = output.blockAddr) (input : env.consts.contains n = true) :
    (closureContext ixe t preA order).memberKey (.member output.blockAddr 0) =
        .ok ((quotientKey ixe t n).map (evAddr ixe b)) ∧
      (blockCtx (closureContext ixe t preA order) ixe order output.block.refs blob).memberKey
        (.member output.blockAddr 0) = .ok ((quotientKey ixe t n).map (evAddr ixe b)) ∧
      lone output.block.info = true := by
  have compiled : compile env = .ok ixe := by unfold compile; rw [P.compiled]; rfl
  obtain ⟨lc, hlc, header⟩ := publishedReadable P.compiled n named hn input
  rw [haddr] at hlc
  obtain ⟨c', hget', wire, enc⟩ := canonical _ hB lc hlc
  have hc' : c' = output.block := by
    unfold recordAt at stored
    rw [hlc] at stored
    simp only [Option.bind_some] at stored
    rw [hget'] at stored
    exact Option.some.inj stored
  subst hc'
  have single := lone_of shape.built (RecordHeaders.not_muts_of_header wire enc header)
  have hstore : (closureContext ixe t preA order).store output.blockAddr = some output.block :=
    ClosureKeying.closure_store corder.nodup hB stored
  have auth := fun a c h => ClosureKeying.closure_authentic compiled P.evidence.2.1 prelude canonical (a := a) (c := c) h
  have hres : resolve (closureContext ixe t preA order).store output.blockAddr = some (.member output.blockAddr 0) := by
    unfold resolve
    rw [hstore]
    cases hi : output.block.info <;> simp_all [lone, resolveSource]
  have hkey := ClosureKeying.closure_keyAt P prelude canonical b hn (by rw [haddr]; exact hres)
  rw [haddr] at hkey
  have hkey₁ := (BlockContext.keyAt_iff (refs := output.block.refs) (blob := blob) corder hB stored).mpr hkey
  have hstore₁ : (blockCtx (closureContext ixe t preA order) ixe order output.block.refs blob).store output.blockAddr = some output.block := by
    change blockStore _ ixe order output.block.refs output.blockAddr = some output.block
    rw [BlockContext.blockStore_kept (.inr (.inl ⟨hB, by rw [stored]; rfl⟩))]
    exact hstore
  exact ⟨(BlockContext.closure_memberKey auth hstore single).trans hkey,
    (BlockContext.blockCtx_memberKey hstore₁ single).trans hkey₁, single⟩

/-- The closure's context reads a compiled record's references as its block's context does,
when the artifact stores the blobs the compile read. -/
theorem lone_refs {t : RoleTable} {preA : Prelude .anon} {cenv : CompileEnv} {output : BlockResult}
    {after : BlockState} (hB : output.blockAddr ∈ order) (stored : recordAt ixe output.blockAddr = some output.block)
    (blobs : ∀ a bytes, BlobWrites.readBlob cenv.blobs after a = some bytes → ixe.blobs.get? a = some bytes) :
    RecordTransfer.RefsLe output.block
      (ExpressionRead.withBlockBlobs
        (blockCtx (closureContext ixe t preA order) ixe order output.block.refs (fun a => cenv.blobs.get? a)) after)
      (closureContext ixe t preA order) :=
  BlockContext.refsLe fun a ha bytes h => closure_blob hB stored ha (blobs a bytes h)

/-! ## The readings -/

/-- A definition quotient Source lowers passes the reader's safety policy. -/
theorem safe_of_lower {ci : Ix.ConstantInfo} {source : Ix.Def} (view : EmissionDispatch.sourceData ci = some source)
    {m0 : Ix.LeanIngress.DefMember} (conv : Ix.LeanIngress.convertDefinitions #[ci] = .ok (.definitions #[m0]))
    {ρ : Ix.LeanIngress.FiberMap} {h : ReducibilityHint} {stS : State .source} {rS : Read .source}
    (lowered : Ix.LeanIngress.lower stS (.definitions #[RecordReadings.quotientMember ρ m0 h]) = .ok rS) :
    safetyDeclineOf source.kind source.safety = none := by
  obtain ⟨-, -, -, -, shapeHint, hshape⟩ := RecordReadings.sourceData_facts view
  obtain ⟨s, v, t', v', hs, -, -, -, hm0⟩ := RecordReadings.convertDefinitions_single conv
  rw [hshape, Option.some.injEq] at hs
  subst hs
  simp only [Ix.LeanIngress.Converted.definitions.injEq, Array.mk.injEq, List.cons.injEq, and_true] at hm0
  subst hm0
  obtain ⟨decl, rw, lowS, -⟩ := RecordReadings.lower_definition lowered
  rw [RecordReadings.quotientMember, RecordReadings.defMember_canon] at lowS
  unfold lowerDefinition at lowS
  cases hd : safetyDeclineOf source.kind source.safety with
  | none => rfl
  | some why =>
    simp [Ix.LeanIngress.DefMember.substKeys, hd, declined, throw, throwThe, MonadExceptOf.throw, bind,
      Except.bind] at lowS

set_option maxRecDepth 4096 in
/-- **A compiled definition reads in the closure's context, from every state related to quotient
Source's, as quotient Source's unit renamed.** -/
theorem closure_definition_reads {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {failures : Failures} {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ)
    {preA : Prelude .anon} (prelude : preludeFor t = .ok preA) (corder : ClosureOrder ixe (Seed ixe sub) order)
    (canonical : Stream.StoredCanonical ixe order) {b : Ix.RoleEvidence.Bundle}
    (hf : InjOn (evAddr ixe b) (QRepAt ixe (roleAtMap t)))
    {ci : Ix.ConstantInfo} {source : Ix.Def} (view : EmissionDispatch.sourceData ci = some source)
    (input : env.consts.contains source.name = true) (nodup : source.levelParams.toList.Nodup)
    {cenv : CompileEnv} {benv : BlockEnv} {output : BlockResult} {after : BlockState}
    (ran : rawRun (compileConstantInfo ci) (cenv, benv) {} = (.ok output, after))
    (hB : output.blockAddr ∈ order) (stored : recordAt ixe output.blockAddr = some output.block)
    {named : Ixon.Named} (hn : (source.name, named) ∈ ixe.named.toList) (haddr : named.addr = output.blockAddr)
    (bound : BoundResolve ixe cenv)
    (blobs : ∀ a bytes, BlobWrites.readBlob cenv.blobs after a = some bytes → ixe.blobs.get? a = some bytes)
    (published : ∀ m a, (GraphWalk.Refs m source.type ∨ GraphWalk.Refs m source.value) →
      lookupBinding cenv {} m = some a →
        ∃ named', (m, named') ∈ ixe.named.toList ∧ named'.addr = a ∧ (sub.consts.get? m).isSome = true)
    {h : ReducibilityHint} (hint : hintsOf ixe (.member output.blockAddr 0) = some h)
    {m0 : Ix.LeanIngress.DefMember} (conv : Ix.LeanIngress.convertDefinitions #[ci] = .ok (.definitions #[m0]))
    {stS : State .source}
    (ownersGood : ∀ k : Key .source, k.Good (KeyScope.ofId (QRepAt ixe (roleAtMap t))) → ∀ o,
      stS.projOwners[k]? = some o → o.Good (KeyScope.ofId (QRepAt ixe (roleAtMap t))))
    (typeGood : (RecordReadings.quotientMember (fiberAliasAt ixe (roleAtMap t)) m0 h).cv.type.Good
      (KeyScope.ofId (QRepAt ixe (roleAtMap t))))
    (valueGood : (RecordReadings.quotientMember (fiberAliasAt ixe (roleAtMap t)) m0 h).value.Good
      (KeyScope.ofId (QRepAt ixe (roleAtMap t))))
    {rS : Read .source}
    (lowered : Ix.LeanIngress.lower stS
      (.definitions #[RecordReadings.quotientMember (fiberAliasAt ixe (roleAtMap t)) m0 h]) = .ok rS) :
    ∀ stA : State .anon, StreamRename.StateRen (evAddr ixe b) (KeyScope.ofId (QRepAt ixe (roleAtMap t))) stS stA →
      ∃ rA, readRecord (closureContext ixe t preA order) stA output.blockAddr output.block = .ok rA ∧
        StreamRename.Plain rA ∧ rA.decls = rS.decls.map (Declaration.mapKeys (evAddr ixe b)) := by
  obtain ⟨hname, -⟩ := RecordReadings.sourceData_facts view
  have shape := BlockLayout.compileConstantInfo_shape ci _ _ _ _ ran
  obtain ⟨mk, mk₁, -⟩ := lone_keys P prelude corder canonical b (blob := fun a => cenv.blobs.get? a) shape hB stored
    hn haddr input
  exact RecordReadings.definition_unit_reads (fun _ _ => trivial) hf view nodup (cenv, benv)
    BlockStart.clean_empty BlockStart.wire_empty (safe_of_lower view conv lowered) ran (fun _ => rfl)
    (external corder hB stored (blob := fun a => cenv.blobs.get? a) bound source.name _) mk₁ (.inl ⟨rfl, rfl⟩)
    (fun n k hm hk => agree P prelude corder canonical b bound source.name published n k hm hk)
    (lone_refs hB stored blobs) (mk.trans mk₁.symm) hint hint conv ownersGood typeGood valueGood lowered

/--
info: 'Ix.Cert.SingletonReads.closure_definition_reads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closure_definition_reads


/-- A type that names no constant by the singleton's own name is in the singleton's scope. -/
theorem scope_of {name : Ix.Name} {context : CompileEnv × BlockEnv} {names : Ix.Name → CName .anon → Prop}
    {e : Ix.Expr} (h : ConstsSatisfy (fun m => m ≠ name) e) :
    ConstsSatisfy (SelfName (EmissionDispatch.singletonContext name context).2 (fun _ => none) names) e :=
  constsSatisfy_mono (fun m hm index found => by
    obtain ⟨same, -⟩ := DefinitionReading.singleton_lookup name m index found
    exact absurd (Ix.CompileCert.Canon.nameCompareExact_eq_iff.mp same) hm) e h

set_option maxRecDepth 4096 in
/-- **A compiled axiom reads in the closure's context, from every state related to quotient
Source's, as quotient Source's unit renamed.** -/
theorem closure_axiom_reads {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {failures : Failures} {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ)
    {preA : Prelude .anon} (prelude : preludeFor t = .ok preA) (corder : ClosureOrder ixe (Seed ixe sub) order)
    (canonical : Stream.StoredCanonical ixe order) {b : Ix.RoleEvidence.Bundle}
    {v : Ix.AxiomVal} (input : env.consts.contains v.cnst.name = true) (nodup : v.cnst.levelParams.toList.Nodup)
    {cenv : CompileEnv} {benv : BlockEnv} {output : BlockResult} {after : BlockState}
    (ran : rawRun (compileConstantInfo (.axiomInfo v)) (cenv, benv) {} = (.ok output, after))
    (hB : output.blockAddr ∈ order) (stored : recordAt ixe output.blockAddr = some output.block)
    {named : Ixon.Named} (hn : (v.cnst.name, named) ∈ ixe.named.toList) (haddr : named.addr = output.blockAddr)
    (bound : BoundResolve ixe cenv)
    (blobs : ∀ a bytes, BlobWrites.readBlob cenv.blobs after a = some bytes → ixe.blobs.get? a = some bytes)
    (published : ∀ m a, GraphWalk.Refs m v.cnst.type → lookupBinding cenv {} m = some a →
      ∃ named', (m, named') ∈ ixe.named.toList ∧ named'.addr = a ∧ (sub.consts.get? m).isSome = true)
    (noSelf : ConstsSatisfy (fun m => m ≠ v.cnst.name) v.cnst.type)
    {cv0 : CVal .source} (conv : Ix.LeanIngress.convert (.axiom v) = .ok (.axiom cv0))
    {stS : State .source} {rS : Read .source}
    (lowered : Ix.LeanIngress.lower stS
      (.axiom (RecordReadings.quotientHeader (fiberAliasAt ixe (roleAtMap t)) cv0)) = .ok rS) :
    ∀ stA : State .anon, StreamRename.StateRen (evAddr ixe b) (KeyScope.ofId (QRepAt ixe (roleAtMap t))) stS stA →
      ∃ rA, readRecord (closureContext ixe t preA order) stA output.blockAddr output.block = .ok rA ∧
        StreamRename.Plain rA ∧ rA.decls = rS.decls.map (Declaration.mapKeys (evAddr ixe b)) := by
  have shape := BlockLayout.compileConstantInfo_shape _ _ _ _ _ ran
  obtain ⟨mk, mk₁, -⟩ := lone_keys P prelude corder canonical b (blob := fun a => cenv.blobs.get? a) shape hB stored
    hn haddr input
  exact RecordReadings.axiom_unit_reads nodup (cenv, benv) BlockStart.clean_empty BlockStart.wire_empty ran
    (fun _ => rfl) (external corder hB stored (blob := fun a => cenv.blobs.get? a) bound v.cnst.name _) mk₁
    (scope_of noSelf) (fun n k hm hk => agree P prelude corder canonical b bound v.cnst.name published n k hm hk)
    (lone_refs hB stored blobs) (mk.trans mk₁.symm) rfl conv lowered

set_option maxRecDepth 4096 in
/-- **A compiled quotient constant reads in the closure's context, from every state related to
quotient Source's, as quotient Source's unit renamed.** -/
theorem closure_quotient_reads {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {failures : Failures} {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ)
    {preA : Prelude .anon} (prelude : preludeFor t = .ok preA) (corder : ClosureOrder ixe (Seed ixe sub) order)
    (canonical : Stream.StoredCanonical ixe order) {b : Ix.RoleEvidence.Bundle}
    {v : Ix.QuotVal} (input : env.consts.contains v.cnst.name = true) (nodup : v.cnst.levelParams.toList.Nodup)
    {cenv : CompileEnv} {benv : BlockEnv} {output : BlockResult} {after : BlockState}
    (ran : rawRun (compileConstantInfo (.quotInfo v)) (cenv, benv) {} = (.ok output, after))
    (hB : output.blockAddr ∈ order) (stored : recordAt ixe output.blockAddr = some output.block)
    {named : Ixon.Named} (hn : (v.cnst.name, named) ∈ ixe.named.toList) (haddr : named.addr = output.blockAddr)
    (bound : BoundResolve ixe cenv)
    (blobs : ∀ a bytes, BlobWrites.readBlob cenv.blobs after a = some bytes → ixe.blobs.get? a = some bytes)
    (published : ∀ m a, GraphWalk.Refs m v.cnst.type → lookupBinding cenv {} m = some a →
      ∃ named', (m, named') ∈ ixe.named.toList ∧ named'.addr = a ∧ (sub.consts.get? m).isSome = true)
    (noSelf : ConstsSatisfy (fun m => m ≠ v.cnst.name) v.cnst.type)
    {kind : Ix.Kernel.QuotKind} {cv0 : CVal .source} (conv : Ix.LeanIngress.convert (.quot v) = .ok (.quot kind cv0))
    {stS : State .source} {rS : Read .source}
    (lowered : Ix.LeanIngress.lower stS
      (.quot kind (RecordReadings.quotientHeader (fiberAliasAt ixe (roleAtMap t)) cv0)) = .ok rS) :
    ∀ stA : State .anon, StreamRename.StateRen (evAddr ixe b) (KeyScope.ofId (QRepAt ixe (roleAtMap t))) stS stA →
      ∃ rA, readRecord (closureContext ixe t preA order) stA output.blockAddr output.block = .ok rA ∧
        StreamRename.Plain rA ∧ rA.decls = rS.decls.map (Declaration.mapKeys (evAddr ixe b)) := by
  have shape := BlockLayout.compileConstantInfo_shape _ _ _ _ _ ran
  obtain ⟨mk, mk₁, -⟩ := lone_keys P prelude corder canonical b (blob := fun a => cenv.blobs.get? a) shape hB stored
    hn haddr input
  exact RecordReadings.quotient_unit_reads nodup (cenv, benv) BlockStart.clean_empty BlockStart.wire_empty ran
    (fun _ => rfl) (external corder hB stored (blob := fun a => cenv.blobs.get? a) bound v.cnst.name _) mk₁
    (scope_of noSelf) (fun n k hm hk => agree P prelude corder canonical b bound v.cnst.name published n k hm hk)
    (lone_refs hB stored blobs) (mk.trans mk₁.symm) rfl conv lowered

/--
info: 'Ix.Cert.SingletonReads.closure_axiom_reads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closure_axiom_reads

/--
info: 'Ix.Cert.SingletonReads.closure_quotient_reads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closure_quotient_reads

end Ix.Cert.SingletonReads
