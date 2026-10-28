import Ix.Cert.SingletonReads
import Ix.Cert.ClosureLayout

/-! # A singleton group's segment of the closure order

Quotient Source lowers a definition, axiom or quotient constant to one declaration, and its
collapse keeps it or drops it (`collapseRead_one`). The segment `ClosureLayout` cuts for it is its
record, or nothing when the declaration was dropped. Either way the segment reads as the Source
read (`lone_segment`): a dropped read is inert, with an empty segment; a kept read is the
lowering, in the scope, and its record reads from every related state as the lowering renamed
(`SingletonReads.closure_*_reads`). `definition_segment`, `axiom_segment` and `quotient_segment`
put the two together. -/

namespace Ix.Cert.SingletonSegments

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState
open Ix.Cert.ClosureSegments (SegmentReads InertAddrs)
open Ix.Cert.BlockContext (BoundResolve lone)
open Ix.LeanIngress (evAddr QRepAt roleAtMap fiberAliasAt ingressKey)

/-! ## One declaration through the collapse -/

theorem id_pure {α : Type} (x : α) : (pure x : Id α) = x := rfl

theorem id_bind {α β : Type} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl

/-- **A read of one declaration collapses to itself or to nothing.** -/
theorem collapseRead_one {s s' : Ix.LeanIngress.CollapseState} {first : CName .source} {raw r : Read .source}
    {dropped : Array (CName .source)} (h : Ix.LeanIngress.collapseRead s first raw = (s', .ok (r, dropped)))
    {d : CDecl .source} (hd : raw.decls = #[d]) (hg : raw.generated = 0) :
    r = raw ∨ r = { raw with decls := #[], generated := 0 } := by
  rw [SourcePrelude.collapseRead_eq] at h
  unfold SourcePrelude.readLoop at h
  rw [hd, hg] at h
  have hz : (#[d] : Array (CDecl .source)).zipIdx = #[(d, 0)] := rfl
  rw [hz, ← Array.forIn_toList] at h
  rcases hstep : s.step first d with ⟨s1, res⟩
  cases res with
  | error e =>
    simp [SourcePrelude.readStep, hstep, SourcePrelude.readFinish, id_pure, id_bind] at h
  | ok b =>
    cases b
    · simp [SourcePrelude.readStep, hstep, SourcePrelude.readFinish, id_pure, id_bind] at h
      obtain ⟨-, rfl, -⟩ := h
      exact .inr rfl
    · simp [SourcePrelude.readStep, hstep, SourcePrelude.readFinish, id_pure, id_bind] at h
      obtain ⟨-, rfl, -⟩ := h
      left
      cases raw
      simp only at hd hg ⊢
      rw [hd, hg]

/-! ## The segment -/

/-- **A singleton's segment reads as its Source read**: a Source read of one plain declaration
whose collapse kept it (segment: its record, read from every related state as the lowering renamed)
or dropped it (segment: nothing). -/
theorem lone_segment {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md} {cx : Ctx md'} {ixe : Ixon.Env}
    {stS : State md} {raw r : Read md} {B : Address} {c : Ixon.Constant} {seg : List Address}
    (plain : StreamRename.Plain raw) (collapse : r = raw ∨ r = { raw with decls := #[], generated := 0 })
    (basis : ∀ d ∈ raw.decls.toList, ∀ k, d ≠ .basisDecl k)
    (good : ∀ d ∈ raw.decls.toList, ∀ e ∈ CtxAgree.noteEntries d, e.1.Good P)
    (hc : recordAt ixe B = some c)
    (reads : ∀ stA : State md', StreamRename.StateRen f P stS stA →
      ∃ rA, readRecord cx stA B c = .ok rA ∧ StreamRename.Plain rA ∧ rA.decls = raw.decls.map (Declaration.mapKeys f))
    (kept : r = raw → seg = [B]) (dropped : r.decls = #[] → seg = []) :
    SegmentReads f P cx ixe stS r seg := by
  rcases collapse with rfl | rfl
  · refine .inr ⟨[], B, [], c, kept rfl, hc, ⟨basis, good, by simp [plain.blocks], by simp [plain.owners]⟩,
      fun stA hst => ?_, (fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    obtain ⟨rA, hr, pA, hdecls⟩ := reads stA hst
    exact ⟨rA, hr, ⟨⟨hdecls, by rw [pA.generated, plain.generated], by simp [pA.blocks, plain.blocks]⟩,
      by simp [pA.owners, plain.owners]⟩⟩
  · rw [dropped rfl]
    exact .inl ⟨⟨⟨rfl, plain.owners, plain.blocks⟩, rfl⟩, fun _ h => nomatch h⟩

/-! ## The Source reads -/

/-- A definition's lowering declares its header's name, and no basis block. -/
theorem lowerDefinition_decl {md : Mode} {hint : Option ReducibilityHint} {st : State md}
    {heights : CName md → Nat} {cv : CVal md} {value : CExpr md} {kind : Ix.DefKind}
    {safety : Ix.DefinitionSafety} {decl : CDecl md} {rw : Bool}
    (h : lowerDefinition hint st heights cv value kind safety = .ok (decl, rw)) :
    (∀ k, decl ≠ .basisDecl k) ∧ ∀ e ∈ CtxAgree.noteEntries decl, e.1 = cv.name := by
  unfold lowerDefinition at h
  cases hs : safetyDeclineOf kind safety with
  | some why => simp [hs, declined, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  | none =>
    simp only [hs, pure, Except.pure] at h
    cases kind <;> (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; simp [CtxAgree.noteEntries])

/-- A key quotient Source gives a published name is in the scope of representatives. -/
theorem qkey_good {ixe : Ixon.Env} {t : RoleTable} (checked : t.check = .ok ()) (bound : PublishedRolesBound t ixe)
    (agree : PublishedAgree ixe) {n : Ix.Name} {named : Ixon.Named} (hn : (n, named) ∈ ixe.named.toList) :
    (Ix.LeanIngress.Key.subst (fiberAliasAt ixe (roleAtMap t)) (ingressKey n)).Good
      (KeyScope.ofId (QRepAt ixe (roleAtMap t))) :=
  Ix.LeanIngress.Key.subst_goodAt (tableBound_of checked bound) (ClosureKeying.ingressKey_good agree hn)

/-- **A singleton definition's Source read**: one plain declaration, no basis block, keyed by the
definition's quotient key. -/
theorem definition_raw {ixe : Ixon.Env} {t : RoleTable} {stS : State .source} {m0 : Ix.LeanIngress.DefMember}
    {h : ReducibilityHint} {raw : Read .source}
    (lowered : Ix.LeanIngress.lower stS
      (.definitions #[RecordReadings.quotientMember (fiberAliasAt ixe (roleAtMap t)) m0 h]) = .ok raw) :
    ∃ d, raw.decls = #[d] ∧ StreamRename.Plain raw ∧ (∀ k, d ≠ .basisDecl k) ∧
      ∀ e ∈ CtxAgree.noteEntries d, e.1 = Ix.LeanIngress.Key.subst (fiberAliasAt ixe (roleAtMap t)) m0.cv.name := by
  obtain ⟨decl, rw, lowS, rfl⟩ := RecordReadings.lower_definition lowered
  obtain ⟨basis, names⟩ := lowerDefinition_decl lowS
  refine ⟨decl, rfl, ⟨rfl, rfl, rfl⟩, basis, fun e he => ?_⟩
  rw [names e he, RecordReadings.quotientMember, RecordReadings.defMember_canon]
  rfl

/-- **A compiled singleton definition's segment reads as quotient Source's read.** -/
theorem definition_segment {ixe : Ixon.Env} {order : List Address} {env : Ix.Environment} {roots : List Ix.Name}
    {sub : Ix.Environment} {failures : Failures} {t : RoleTable} {envQ : Env .source}
    (P : Premises env roots sub ixe failures t envQ) {preA : Prelude .anon} (prelude : preludeFor t = .ok preA)
    (corder : ClosureOrder ixe (Seed ixe sub) order) (canonical : Stream.StoredCanonical ixe order)
    {b : Ix.RoleEvidence.Bundle} (hf : InjOn (evAddr ixe b) (QRepAt ixe (roleAtMap t)))
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
    {raw : Read .source}
    (lowered : Ix.LeanIngress.lower stS
      (.definitions #[RecordReadings.quotientMember (fiberAliasAt ixe (roleAtMap t)) m0 h]) = .ok raw)
    {s s' : Ix.LeanIngress.CollapseState} {first : CName .source} {r : Read .source} {dropped : Array (CName .source)}
    (collapse : Ix.LeanIngress.collapseRead s first raw = (s', .ok (r, dropped)))
    {seg : List Address} (kept : r = raw → seg = [output.blockAddr]) (empty : r.decls = #[] → seg = []) :
    SegmentReads (evAddr ixe b) (KeyScope.ofId (QRepAt ixe (roleAtMap t))) (closureContext ixe t preA order) ixe
      stS r seg := by
  obtain ⟨d, hd, plain, basis, names⟩ := definition_raw lowered
  obtain ⟨hname, -⟩ := RecordReadings.sourceData_facts view
  have reads := SingletonReads.closure_definition_reads P prelude corder canonical hf view input nodup ran hB stored
    hn haddr bound blobs published hint conv ownersGood typeGood valueGood lowered
  obtain ⟨s0, v0, t0, w0, -, -, -, -, hm0⟩ := RecordReadings.convertDefinitions_single conv
  cases hm0
  refine lone_segment plain (collapseRead_one collapse hd plain.generated) (fun d' hd' => ?_)
    (fun d' hd' e he => ?_) stored reads kept empty
  · rw [hd] at hd'
    simp only [List.mem_singleton] at hd'
    subst hd'
    exact basis
  rw [hd] at hd'
  simp only [List.mem_singleton] at hd'
  subst hd'
  rw [names e he, hname]
  exact qkey_good (defaultTable_check P.table) P.bound P.agree hn

/-- **A compiled axiom's segment reads as quotient Source's read.** -/
theorem axiom_segment {ixe : Ixon.Env} {order : List Address} {env : Ix.Environment} {roots : List Ix.Name}
    {sub : Ix.Environment} {failures : Failures} {t : RoleTable} {envQ : Env .source}
    (P : Premises env roots sub ixe failures t envQ) {preA : Prelude .anon} (prelude : preludeFor t = .ok preA)
    (corder : ClosureOrder ixe (Seed ixe sub) order) (canonical : Stream.StoredCanonical ixe order)
    {b : Ix.RoleEvidence.Bundle}
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
    {stS : State .source} {raw : Read .source}
    (lowered : Ix.LeanIngress.lower stS
      (.axiom (RecordReadings.quotientHeader (fiberAliasAt ixe (roleAtMap t)) cv0)) = .ok raw)
    {s s' : Ix.LeanIngress.CollapseState} {first : CName .source} {r : Read .source} {dropped : Array (CName .source)}
    (collapse : Ix.LeanIngress.collapseRead s first raw = (s', .ok (r, dropped)))
    {seg : List Address} (kept : r = raw → seg = [output.blockAddr]) (empty : r.decls = #[] → seg = []) :
    SegmentReads (evAddr ixe b) (KeyScope.ofId (QRepAt ixe (roleAtMap t))) (closureContext ixe t preA order) ixe
      stS r seg := by
  have reads := SingletonReads.closure_axiom_reads (b := b) P prelude corder canonical input nodup ran hB stored hn
    haddr bound blobs published noSelf conv lowered
  have unfolded : Ix.LeanIngress.lower stS (.axiom (RecordReadings.quotientHeader (fiberAliasAt ixe (roleAtMap t)) cv0)) =
      .ok { decls := #[.axiomDecl (RecordReadings.quotientHeader (fiberAliasAt ixe (roleAtMap t)) cv0)] } := rfl
  rw [unfolded, Except.ok.injEq] at lowered
  subst lowered
  obtain ⟨t', -, -, hc⟩ := RecordReadings.convert_axiom conv
  simp only [Ix.LeanIngress.Converted.axiom.injEq] at hc
  subst hc
  refine lone_segment ⟨rfl, rfl, rfl⟩ (collapseRead_one collapse rfl rfl) (fun d hd k => ?_) (fun d hd e he => ?_)
    stored reads kept empty
  · simp only [List.mem_singleton] at hd
    subst hd
    exact fun h => nomatch h
  · simp only [List.mem_singleton] at hd
    subst hd
    simp only [CtxAgree.noteEntries, List.mem_singleton] at he
    subst he
    rw [RecordReadings.quotientHeader_eq]
    exact qkey_good (defaultTable_check P.table) P.bound P.agree hn

/-- **A compiled quotient constant's segment reads as quotient Source's read.** -/
theorem quotient_segment {ixe : Ixon.Env} {order : List Address} {env : Ix.Environment} {roots : List Ix.Name}
    {sub : Ix.Environment} {failures : Failures} {t : RoleTable} {envQ : Env .source}
    (P : Premises env roots sub ixe failures t envQ) {preA : Prelude .anon} (prelude : preludeFor t = .ok preA)
    (corder : ClosureOrder ixe (Seed ixe sub) order) (canonical : Stream.StoredCanonical ixe order)
    {b : Ix.RoleEvidence.Bundle}
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
    {stS : State .source} {raw : Read .source}
    (lowered : Ix.LeanIngress.lower stS
      (.quot kind (RecordReadings.quotientHeader (fiberAliasAt ixe (roleAtMap t)) cv0)) = .ok raw)
    {s s' : Ix.LeanIngress.CollapseState} {first : CName .source} {r : Read .source} {dropped : Array (CName .source)}
    (collapse : Ix.LeanIngress.collapseRead s first raw = (s', .ok (r, dropped)))
    {seg : List Address} (kept : r = raw → seg = [output.blockAddr]) (empty : r.decls = #[] → seg = []) :
    SegmentReads (evAddr ixe b) (KeyScope.ofId (QRepAt ixe (roleAtMap t))) (closureContext ixe t preA order) ixe
      stS r seg := by
  have reads := SingletonReads.closure_quotient_reads (b := b) P prelude corder canonical input nodup ran hB stored hn
    haddr bound blobs published noSelf conv lowered
  have unfolded : Ix.LeanIngress.lower stS
      (.quot kind (RecordReadings.quotientHeader (fiberAliasAt ixe (roleAtMap t)) cv0)) =
      .ok { decls := #[.quotDecl kind (RecordReadings.quotientHeader (fiberAliasAt ixe (roleAtMap t)) cv0)] } := rfl
  rw [unfolded, Except.ok.injEq] at lowered
  subst lowered
  obtain ⟨t', -, hc⟩ := RecordReadings.convert_quot conv
  simp only [Ix.LeanIngress.Converted.quot.injEq] at hc
  obtain ⟨-, rfl⟩ := hc
  refine lone_segment ⟨rfl, rfl, rfl⟩ (collapseRead_one collapse rfl rfl) (fun d hd k => ?_) (fun d hd e he => ?_)
    stored reads kept empty
  · simp only [List.mem_singleton] at hd
    subst hd
    exact fun h => nomatch h
  · simp only [List.mem_singleton] at hd
    subst hd
    simp only [CtxAgree.noteEntries, List.mem_singleton] at he
    subst he
    rw [RecordReadings.quotientHeader_eq]
    exact qkey_good (defaultTable_check P.table) P.bound P.agree hn

/-! ## Where a singleton's segment lies -/

/-- **A published closure name's record resolves in the artifact's store**: a projection's
block is a block record holding a member of the projection's kind. -/
def PublishedResolve (ixe : Ixon.Env) (sub : Ix.Environment) : Prop :=
  ∀ n ci named, (n, ci) ∈ sub.consts.toList → ixe.named.get? n = some named → ∀ c,
    recordAt ixe named.addr = some c → (resolveSource (recordAt ixe) named.addr c).isSome = true

theorem filter_single : ∀ {L : List Address} {p : Address → Bool} {B : Address}, L.Nodup → B ∈ L →
    (∀ a ∈ L, p a = true ↔ a = B) → L.filter p = [B]
  | [], _, _, _, h, _ => nomatch h
  | x :: xs, p, B, hnd, hB, hp => by
    rw [List.nodup_cons] at hnd
    by_cases e : x = B
    · subst e
      rw [List.filter_cons_of_pos ((hp x List.mem_cons_self).mpr rfl),
        List.filter_eq_nil_iff.mpr fun a ha hpa => by
          have := (hp a (List.mem_cons_of_mem _ ha)).mp hpa
          subst this
          exact hnd.1 ha]
    · have hx : ¬ p x = true := fun h => e ((hp x List.mem_cons_self).mp h)
      rw [List.filter_cons_of_neg hx]
      exact filter_single hnd.2 ((List.mem_cons.mp hB).resolve_left (Ne.symm e))
        fun a ha => hp a (List.mem_cons_of_mem _ ha)

/-- A record that resolves in the artifact's store, and whose owner holds a lone record, is its
own owner. -/
theorem owner_lone {ixe : Ixon.Env} {P : Address} {cm : Ixon.Constant}
    (hres : (resolveSource (recordAt ixe) P cm).isSome = true) {c : Ixon.Constant}
    (hc : recordAt ixe (ownerOf P cm) = some c) (single : lone c.info = true) : ownerOf P cm = P := by
  cases hi : cm.info with
  | defn _ | recr _ | axio _ | quot _ | muts _ => simp [ownerOf, hi]
  | dPrj p | iPrj p | rPrj p | cPrj p =>
    simp only [ownerOf, hi] at hc ⊢
    simp only [resolveSource, hi, hc] at hres
    cases hci : c.info <;> simp_all [lone]

/-- **A kept singleton's segment is its record**: no earlier lowered group has the record, since
an earlier name at the record's address has the singleton's quotient key, which the singleton's
read keeps and no earlier read declares (`Steps`), and an earlier name's record projecting from
the record would not resolve. -/
theorem singleton_place {ixe : Ixon.Env} {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {failures : Failures} {t : RoleTable} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ)
    {hints : CName .source → Option ReducibilityHint} {start : State .source} {ls : List SourcePrelude.Scheduled}
    {rs : List (Read .source)} (steps : ClosureLayout.Steps (ClosureLayout.quotientGraph ixe t hints sub) start ls rs)
    (inTrace : ∀ y ∈ ls, y ∈ (Ix.LeanIngress.scheduleOf (ClosureLayout.quotientGraph ixe t hints sub)).zipIdx.toList)
    {L : List Address} (hnd : L.Nodup) (hmem : ∀ a, a ∈ L ↔ ixe.consts.contains a = true)
    (resolves : PublishedResolve ixe sub) {ℓ : Nat} {y : SourcePrelude.Scheduled} {r : Read .source}
    (hy : ls[ℓ]? = some y) (hr : rs[ℓ]? = some r) {n : Ix.Name}
    (hnames : ClosureLayout.namesAt (ClosureLayout.quotientGraph ixe t hints sub) y = #[n]) {B : Address}
    (hB : ClosureLayout.addrOf ixe n = some B) {c : Ixon.Constant} (hc : recordAt ixe B = some c)
    (single : lone c.info = true)
    (hdecl : ∃ d ∈ r.decls.toList, ClosureLayout.qkey (fiberAliasAt ixe (roleAtMap t)) n ∈ d.names) :
    (ClosureLayout.segmentsOf L (ls.map fun y =>
      ClosureLayout.groupRecords ixe (ClosureLayout.namesAt (ClosureLayout.quotientGraph ixe t hints sub) y)) [])[ℓ]? =
        some [B] := by
  obtain ⟨hlen, stepsAt⟩ := steps
  have tb := tableBound_of (defaultTable_check P.table) P.bound
  have hblk : ClosureLayout.blockAt ixe B = B := by
    unfold ClosureLayout.blockAt
    rw [hc]
    cases hi : c.info <;> simp_all [lone, ownerOf]
  have hC : (ls.map fun y =>
      ClosureLayout.groupRecords ixe (ClosureLayout.namesAt (ClosureLayout.quotientGraph ixe t hints sub) y))[ℓ]? =
        some [B, B] := by
    rw [List.getElem?_map, hy]
    simp [ClosureLayout.groupRecords, hnames, ClosureLayout.nameRecords, hB, hblk]
  rw [ClosureLayout.segmentsOf_get L _ [] ℓ _ hC]
  congr 1
  refine filter_single hnd ((hmem B).mpr (ClosureLayout.recordAt_contains hc)) fun a _ => ?_
  simp only [decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false, or_self,
    List.nil_append]
  refine ⟨fun h => h.1, ?_⟩
  intro hab
  rw [hab]
  refine ⟨rfl, fun hprev => ?_⟩
  -- the record of an earlier lowered group's name
  rw [← List.map_take] at hprev
  obtain ⟨C, hCm, hBC⟩ := List.mem_flatten.mp hprev
  obtain ⟨y', hy'm, rfl⟩ := List.mem_map.mp hCm
  obtain ⟨j, hj, hjy⟩ := List.mem_iff_getElem.mp hy'm
  have hjℓ : j < ℓ := by simp at hj; omega
  have hℓ : ℓ < ls.length := (List.getElem?_eq_some_iff.mp hy).1
  have hy' : ls[j]? = some y' := by rw [← hjy, List.getElem_take]; exact List.getElem?_eq_getElem _
  obtain ⟨r', hr'⟩ : ∃ r', rs[j]? = some r' := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨conv', raw', -, -, -, -, -, hc', hl', -, -, hraw', -⟩ := stepsAt j y' r' hy' hr'
  obtain ⟨conv, -, -, -, -, -, -, hconv, -, -, -, -, fresh⟩ := stepsAt ℓ y r hy hr
  have hy'x := inTrace y' (List.mem_of_getElem? hy')
  have hyx := inTrace y (List.mem_of_getElem? hy)
  obtain ⟨m, hm, hBm⟩ := List.mem_flatMap.mp hBC
  have hm' := Array.mem_toList_iff.mp hm
  -- `m`'s quotient key is declared before the singleton's read
  obtain ⟨d, hd, hkd⟩ := ClosureLayout.lowered_declares hy'x hc' hl' m hm'
  obtain ⟨d', hd', hkd'⟩ := hraw' d hd _ hkd
  have hd'ℓ : d' ∈ (rs.take ℓ).flatMap (·.decls.toList) := by
    obtain ⟨r'', hr'', hdr⟩ := List.mem_flatMap.mp hd'
    have htk : rs.take (j + 1) = (rs.take ℓ).take (j + 1) := by rw [List.take_take]; congr 1; omega
    rw [htk] at hr''
    exact List.mem_flatMap.mpr ⟨r'', List.mem_of_mem_take hr'', hdr⟩
  -- both names are published closure names
  obtain ⟨gr', c', hgr', hcv', -⟩ := ClosureLayout.scheduled_conversion hy'x hc'
  obtain ⟨gr, c0, hgr, hcv, -⟩ := ClosureLayout.scheduled_conversion hyx hconv
  have hnm' : ClosureLayout.namesAt (ClosureLayout.quotientGraph ixe t hints sub) y' = gr'.names := by
    unfold ClosureLayout.namesAt; rw [ClosureLayout.getElem!_of_getElem? hgr']
  have hnm : ClosureLayout.namesAt (ClosureLayout.quotientGraph ixe t hints sub) y = gr.names := by
    unfold ClosureLayout.namesAt; rw [ClosureLayout.getElem!_of_getElem? hgr]
  obtain ⟨cim, hcim⟩ := ClosureLayout.converted_names_stored P hgr' hcv' m (hnm' ▸ hm')
  obtain ⟨cin, hcin⟩ := ClosureLayout.converted_names_stored P hgr hcv n (by rw [← hnm, hnames]; simp)
  obtain ⟨namedm, hmm, hgetm⟩ := SourceStoredNames.stored_published P hcim
  obtain ⟨namedn, hmn, hgetn⟩ := SourceStoredNames.stored_published P hcin
  have hBn : namedn.addr = B := by
    unfold ClosureLayout.addrOf at hB; rw [hgetn] at hB; exact Option.some.inj hB
  -- the record is `m`'s own
  have hP : namedm.addr = B := by
    unfold ClosureLayout.nameRecords ClosureLayout.addrOf at hBm
    rw [hgetm] at hBm
    simp only [Option.map_some, List.mem_cons, List.not_mem_nil, or_false] at hBm
    rcases hBm with e | e
    · exact e.symm
    · unfold ClosureLayout.blockAt at e
      cases hcm : recordAt ixe namedm.addr with
      | none => rw [hcm] at e; exact e.symm
      | some cm =>
        rw [hcm] at e
        dsimp only at e
        rw [owner_lone (resolves m cim namedm hcim hgetm cm hcm) (by rw [← e]; exact hc) single] at e
        exact e.symm
  -- so it has the singleton's quotient key
  have hkey : ClosureLayout.qkey (fiberAliasAt ixe (roleAtMap t)) m = ClosureLayout.qkey (fiberAliasAt ixe (roleAtMap t)) n :=
    Ix.LeanIngress.fiberAliasAt_addr_inj tb (by rw [P.agree m namedm hmm, hP]) (by rw [P.agree n namedn hmn, hBn])
  obtain ⟨dn, hdn, hkdn⟩ := hdecl
  exact fresh dn hdn _ hkdn d' hd'ℓ (hkey ▸ hkd')

/--
info: 'Ix.Cert.SingletonSegments.definition_segment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms definition_segment

/--
info: 'Ix.Cert.SingletonSegments.axiom_segment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms axiom_segment

/--
info: 'Ix.Cert.SingletonSegments.quotient_segment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms quotient_segment

/--
info: 'Ix.Cert.SingletonSegments.singleton_place' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms singleton_place

end Ix.Cert.SingletonSegments
