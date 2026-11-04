import Ix.Cert.RecursorIndexFacts
import Ix.Cert.InductiveSegments
import Ix.Cert.FamilyGroups
import Ix.Cert.LowerTransfer
import Ix.Cert.ReaderFallback

/-! # The closure's recursor index at an inductive group's block

The closure's reading context indexes the recursors of the closure's records that it does not
file under a block only the prelude supplies, then of the prelude's records it does not shadow
and does not file under a block the closure supplies (`Ix.Kernel.Reader.indexedRecords`). A
closure record whose recursor members file under closure blocks is indexed (`order_scanned`). For an inductive group compiled in Lean's order, the block
the index files the group's recursors under is the inductive block, in member order, and its
recursors are the recursor family's members in family order, each with the entry quotient
Source's reading of the group needs (`closure_recursor_index`). These are the index premises of
`InductiveSegments.closure_inductive_reads`.

The report checks pin each input family recursor to the slot its name gives it
(`RecursorShapes`), make the slots of stored recursor members distinct
(`RecursorSlotsUnique`) and keep the index's recursors in their block's family
(`RecursorsOwned`). The analysis that files a closure record reads only closure records
(`analysis_closure`), so it files alike in the closure's context, where a prelude record never
files under a block the closure supplies (`scanned_cases`). A recursor filed under the group's
block is then one of the family's (`family_candidate`): it is filed so in the artifact's index
too, so `RecursorsOwned` makes it a published recursor of the family, whose slot puts it in the
family's record, at its own position. -/

namespace Ix.Cert.RecursorIndex

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileM Ix.CompileCert
open Ix.CompileCert.ReaderIndex (inductives orderFor orderValid From Coherent)
open Ix.Cert.ClosureLayout (blockAt addrOf nameRecords)
open Ix.LeanIngress (evAddr roleAtMap fiberAliasAt)

variable {ixe : Ixon.Env} {order : List Address} {t : RoleTable} {preA : Prelude .anon}

/-! ## The closure context's scanned records -/

/-- The records the closure context's recursor index scans. -/
abbrev scannedOf (ixe : Ixon.Env) (t : RoleTable) (preA : Prelude .anon) (order : List Address) :
    Array (Address × Ixon.Constant) :=
  indexedRecords (closureContext ixe t preA order).store (Stream.decodedOf ixe order).toArray
    (preA.records ++ preA.evidence)

theorem closure_index :
    (closureContext ixe t preA order).index =
      buildIndex (closureContext ixe t preA order).store (scannedOf ixe t preA order) := rfl

theorem closure_coherent (prelude : preludeFor t = .ok preA) (nodup : order.Nodup) :
    Coherent (closureContext ixe t preA order).store (scannedOf ixe t preA order) := fun a c h =>
  ReaderClosureKeys.context_coherent_of_nodup t (Stream.decodedOf ixe order).toArray (preA.records ++ preA.evidence)
    (blobsOf ixe order) preA.blobs (hintsOf ixe) (Admission.projectionAddress Address.admissionHash)
    (by simpa only [List.toList_toArray] using (Stream.decodedOf_keys ixe order).nodup nodup)
    (ReaderFallback.preludeFor_keys prelude) a c (ReaderClosureKeys.mem_indexed_scanned h)

theorem mem_decoded {a : Address} {c : Ixon.Constant} :
    (a, c) ∈ (Stream.decodedOf ixe order).toArray ↔ a ∈ order ∧ recordAt ixe a = some c := by
  simp only [List.mem_toArray, Stream.decodedOf, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨a', ha', c', hc', rfl, rfl⟩
    exact ⟨ha', hc'⟩
  · rintro ⟨ha, hc⟩
    exact ⟨a, ha, c, hc, rfl, rfl⟩

theorem known_contains {records : Array (Address × Ixon.Constant)} {a : Address} {c : Ixon.Constant}
    (h : (a, c) ∈ records) :
    (records.foldl (fun s (a, _) => s.insert a) ({} : Std.HashSet Address)).contains a = true := by
  rw [← Array.foldl_toList]
  have key : ∀ (xs : List (Address × Ixon.Constant)) (s : Std.HashSet Address),
      s.contains a = true ∨ (a, c) ∈ xs →
        (xs.foldl (fun s (a, _) => s.insert a) s).contains a = true := by
    intro xs
    induction xs with
    | nil =>
      intro s h
      rcases h with h | h
      · exact h
      · cases h
    | cons p xs ih =>
      intro s h
      obtain ⟨p₁, p₂⟩ := p
      rw [List.foldl_cons]
      apply ih
      rcases h with h | h
      · exact .inl (by rw [Std.HashSet.contains_insert, h, Bool.or_true])
      · rcases List.mem_cons.mp h with he | h
        · cases he
          exact .inl (by rw [Std.HashSet.contains_insert]; simp)
        · exact .inr h
  exact key _ _ (.inr (Array.mem_toList_iff.mpr h))

/-- **A closure record is scanned** when each of its recursor members that the closure context's
analysis files at all is filed under a block the closure stores (`Ix.Kernel.Reader.inputIndexed`). -/
theorem order_scanned {a : Address} {c : Ixon.Constant} (ha : a ∈ order) (hc : recordAt ixe a = some c)
    (filed : ∀ j r, (j, r) ∈ recursorMembers c → ∀ m cs mj b i,
      analyseRecursor (closureContext ixe t preA order).store a c r = some (m, cs, mj) →
      cs[0]? = some (.member b i) → b ∈ order ∧ (recordAt ixe b).isSome) :
    (a, c) ∈ scannedOf ixe t preA order := by
  simp only [scannedOf, indexedRecords, Array.mem_append, Array.mem_filter]
  refine .inl ⟨mem_decoded.mpr ⟨ha, hc⟩, ?_⟩
  unfold inputIndexed
  rw [Bool.or_eq_true]
  refine .inl (Array.all_eq_true'.mpr fun ⟨j, r⟩ hm => ?_)
  dsimp only
  cases han : analyseRecursor (closureContext ixe t preA order).store a c r with
  | none => rfl
  | some x =>
    obtain ⟨m, cs, mj⟩ := x
    dsimp only
    cases hcs : cs[0]? with
    | none => rfl
    | some q =>
      cases q with
      | ctor _ _ _ => rfl
      | member b i =>
        obtain ⟨hb, hrb⟩ := filed j r hm m cs mj b i han hcs
        obtain ⟨cb, hcb⟩ := Option.isSome_iff_exists.mp hrb
        exact known_contains (mem_decoded.mpr ⟨hb, hcb⟩)

/-- **A record's recursor members sit at distinct positions.** -/
theorem recursorMembers_unique {c : Ixon.Constant} {j : Nat} {r₁ r₂ : Ixon.Recursor}
    (h₁ : (j, r₁) ∈ recursorMembers c) (h₂ : (j, r₂) ∈ recursorMembers c) : r₁ = r₂ := by
  unfold recursorMembers at h₁ h₂
  split at h₁
  · rename_i r hi
    rw [hi] at h₂
    simp only [List.mem_toArray, List.mem_singleton, Prod.mk.injEq] at h₁ h₂
    rw [h₁.2, h₂.2]
  · rename_i ms hi
    rw [hi] at h₂
    simp only [Array.mem_filterMap] at h₁ h₂
    obtain ⟨⟨x₁, k₁⟩, hk₁, e₁⟩ := h₁
    obtain ⟨⟨x₂, k₂⟩, hk₂, e₂⟩ := h₂
    cases x₁ <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at e₁
    cases x₂ <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at e₂
    obtain ⟨rfl, rfl⟩ := e₁
    obtain ⟨rfl, rfl⟩ := e₂
    have g₁ := Array.mem_zipIdx_iff_getElem?.mp hk₁
    have g₂ := Array.mem_zipIdx_iff_getElem?.mp hk₂
    rw [g₁] at g₂
    simp only [Option.some.injEq, Ixon.MutConst.recr.injEq] at g₂
    exact g₂
  · simp at h₁

/-- **A record the closure context's index scans** is a closure record, or a prelude record none of
whose recursor members is analysed into a block the closure supplies. -/
theorem scanned_cases {a : Address} {c : Ixon.Constant} (h : (a, c) ∈ scannedOf ixe t preA order) :
    (a ∈ order ∧ recordAt ixe a = some c) ∨
      ∀ j r, (j, r) ∈ recursorMembers c → ∀ m cs mj b fi,
        analyseRecursor (closureContext ixe t preA order).store a c r = some (m, cs, mj) →
        cs[0]? = some (.member b fi) → b ∈ order → recordAt ixe b = none := by
  simp only [scannedOf, indexedRecords, Array.mem_append, Array.mem_filter, Bool.and_eq_true] at h
  rcases h with ⟨h, -⟩ | ⟨-, -, hfb⟩
  · exact .inl (mem_decoded.mp h)
  · refine .inr fun j r hm m cs mj b fi ha hcs hb => ?_
    cases hrb : recordAt ixe b with
    | none => rfl
    | some cb =>
      exfalso
      unfold fallbackIndexed at hfb
      have hall := Array.all_eq_true'.mp hfb (j, r) hm
      simp only [ha, hcs] at hall
      have hk := known_contains (records := (Stream.decodedOf ixe order).toArray) (mem_decoded.mpr ⟨hb, hrb⟩)
      rw [hk] at hall
      cases hall

/-! ## Analyses of closure records read closure records -/

theorem resolveSource_block {s : Store} {a : Address} {c : Ixon.Constant} {q : ConstRef Address}
    (h : resolveSource s a c = some q) : q.block = ownerOf a c := by
  cases hi : c.info with
  | defn _ | recr _ | axio _ | quot _ =>
    simp only [resolveSource, hi, Option.some.injEq] at h
    subst h
    simp [ownerOf, hi]
  | muts _ => simp [resolveSource, hi] at h
  | iPrj p => rw [InductiveSegments.resolveSource_iPrj hi h]; simp [ownerOf, hi]
  | rPrj p => rw [InductiveSegments.resolveSource_rPrj hi h]; simp [ownerOf, hi]
  | cPrj p => rw [InductiveSegments.resolveSource_cPrj hi h]; simp [ownerOf, hi]
  | dPrj p =>
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
      | defn _ => cases h; simp [ownerOf, hi]
      | indc _ => cases h
      | recr _ => cases h
    | _ => simp [hb] at h

/-- **A reference lookup of a closure record's analysis answers alike in the closure's
context**, with an answer in the closure. -/
theorem headRef_closure {S : Address → Prop} (corder : ClosureOrder ixe S order) {owner : Address}
    {c : Ixon.Constant} (ho : owner ∈ order) (hc : recordAt ixe owner = some c) (e : Ixon.Expr)
    (q : ConstRef Address) (h : headRef (recordAt ixe) owner c e = some q) :
    headRef (closureContext ixe t preA order).store owner c e = some q ∧ q.block ∈ order := by
  unfold headRef at h ⊢
  cases hap : appHead c spineFuel e
  case ref i us =>
    simp only [hap] at h ⊢
    obtain ⟨a, hia, hra⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ca, hca, hq⟩ := Option.bind_eq_some_iff.mp hra
    have hcontains : c.refs.contains a = true := Array.contains_iff_mem.mpr (Array.mem_of_getElem? hia)
    have ha : a ∈ order := (corder.complete _).mpr
      (.step ((corder.complete owner).mp ho) ⟨c, hc, .inr ⟨hcontains, ClosureLayout.recordAt_contains hca⟩⟩)
    refine ⟨Option.bind_eq_some_iff.mpr ⟨a, hia, BlockContext.closure_resolve corder ha hca hq⟩, ?_⟩
    rw [resolveSource_block hq]
    exact InductiveSegments.owner_in_order corder ha hca rfl
  case recur i us =>
    simp only [hap] at h ⊢
    refine ⟨h, ?_⟩
    have hb : q.block = owner := by
      split at h
      · split at h
        · cases h; rfl
        · cases h
      · split at h
        · cases h; rfl
        · cases h
    rw [hb]
    exact ho
  all_goals simp [hap] at h

/-- **A closure record's filing analysis files alike in the closure's context**, its carriers
and major premise in the closure. -/
theorem analysis_closure {S : Address → Prop} (corder : ClosureOrder ixe S order) {owner : Address}
    {c : Ixon.Constant} (ho : owner ∈ order) (hc : recordAt ixe owner = some c) {r : Ixon.Recursor}
    {y : Address × Nat × Array (ConstRef Address) × ConstRef Address}
    (h : recursorAnalysis? (recordAt ixe) owner c r = some y) :
    recursorAnalysis? (closureContext ixe t preA order).store owner c r = some y ∧
      (∀ q ∈ y.2.2.1, q.block ∈ order) ∧ y.2.2.2.block ∈ order :=
  recursorAnalysis_transfer (D := (· ∈ order)) (headRef_closure corder ho hc)
    (fun _ _ ha hbc => ClosureKeying.closure_store corder.nodup ha hbc) h

theorem inductiveAt_closure (nodup : order.Nodup) {mb : Address} {mi : Nat} {ind : Ixon.Inductive}
    (hmb : mb ∈ order) (h : inductiveAt (recordAt ixe) (.member mb mi) = some ind) :
    inductiveAt (closureContext ixe t preA order).store (.member mb mi) = some ind := by
  cases hcb : recordAt ixe mb with
  | none => simp [inductiveAt, hcb] at h
  | some cb =>
    have hs := ClosureKeying.closure_store (t := t) (preA := preA) nodup hmb hcb
    simp only [inductiveAt, hcb] at h
    simpa only [inductiveAt, hs] using h

/-! ## The group's names -/

section Group

variable {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {failures : Failures}
  {envQ : Env .source}

/-- **An inductive group's head**: its first type, stored under the name its block lists first,
and its types and recursors read off that block. -/
theorem group_head (P : Premises env roots sub ixe failures t envQ)
    {hints : CName .source → Option ReducibilityHint} {i : Nat}
    {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal}
    (hgr : (ClosureLayout.quotientGraph ixe t hints sub).groups[i]? = some (.inductive types ctors recs))
    {first : Ix.InductiveVal} (hfirst : types[0]? = some first) :
    ∃ n, (n, Ix.ConstantInfo.inductInfo first) ∈ env.consts.toList ∧ first.all[0]? = some n ∧
      first.cnst.name = n ∧ FamilyGroups.TypesOf sub first types ∧
      Ix.LeanIngress.blockRecursors first ((FamilyGroups.recsTable sub).getD n #[]) = .ok recs := by
  have hmem : Ix.LeanIngress.Group.inductive types ctors recs ∈
      Ix.LeanIngress.groupsOf sub (Ix.Cert.blocksOf sub) := Array.mem_of_getElem? hgr
  obtain ⟨n, v, hnv, head, hg⟩ := FamilyGroups.inductive_origin hmem
  rcases FamilyGroups.inductiveGroup_shape hg with ⟨_, _, e⟩ | ⟨types', ctors', recs', e, htypes, -, hrecs⟩
  · cases e
  obtain ⟨rfl, rfl, rfl⟩ := Ix.LeanIngress.Group.inductive.inj e
  have hlen : 0 < v.all.toList.length := by
    have := (Array.getElem?_eq_some_iff.mp head).1
    simpa using this
  have hlenT : 0 < types.toList.length := by
    have := (Array.getElem?_eq_some_iff.mp hfirst).1
    simpa using this
  obtain ⟨hget, -⟩ := InductiveCompile.forall₂_getElem htypes 0 hlen hlenT
  have h0 : v.all.toList[0] = n := by
    have := (Array.getElem?_eq_some_iff.mp head).2
    simpa using this
  have hT0 : types.toList[0] = first := by
    have := (Array.getElem?_eq_some_iff.mp hfirst).2
    simpa using this
  rw [h0, hT0, SourceStoredNames.stored_get hnv] at hget
  cases hget
  have hnE := SourceStoredNames.stored_input P hnv
  exact ⟨n, hnE, head, inputsNamed P.compiled n _ hnE, htypes, hrecs⟩

/-- **The group's types are stored under the names its block lists**, exactly. -/
theorem types_named (P : Premises env roots sub ixe failures t envQ) (names : FamilyNamesStored env)
    {n : Ix.Name} {first : Ix.InductiveVal} (hnE : (n, Ix.ConstantInfo.inductInfo first) ∈ env.consts.toList)
    {types : Array Ix.InductiveVal} (htypes : FamilyGroups.TypesOf sub first types) :
    types.size = first.all.size ∧
      ∀ i (hi : i < types.size) (hi' : i < first.all.size), types[i].cnst.name = first.all[i] := by
  have hlen := InductiveCompile.forall₂_length htypes
  simp only [Array.length_toList] at hlen
  refine ⟨hlen.symm, fun i hi hi' => ?_⟩
  obtain ⟨hget, -⟩ := InductiveCompile.forall₂_getElem htypes i (by simpa using hi') (by simpa using hi)
  simp only [Array.getElem_toList] at hget
  obtain ⟨ci, hci⟩ := names n _ hnE first.all[i]
    (by simp only [familyNamesOf, List.mem_append]; exact .inl (Array.getElem_mem_toList hi'))
  have hE := P.source.1.mem_env hget
  rw [SourceStoredNames.stored_get hci] at hE
  cases hE
  exact (inputsNamed P.compiled _ _ hci)

/-- **The group's recursors are stored input recursors of its head's family.** -/
theorem recs_stored (P : Premises env roots sub ixe failures t envQ) {n : Ix.Name} {first : Ix.InductiveVal}
    {recs : Array Ix.RecursorVal}
    (hrecs : Ix.LeanIngress.blockRecursors first ((FamilyGroups.recsTable sub).getD n #[]) = .ok recs) :
    ∀ j (hj : j < recs.size), (recs[j].cnst.name, Ix.ConstantInfo.recInfo recs[j]) ∈ env.consts.toList ∧
      recs[j].all[0]? = some n := by
  intro j hj
  obtain ⟨k, hk, h0⟩ := FamilyGroups.recsTable_mem
    (SourceStoredNames.blockRecursors_mem hrecs recs[j] (Array.getElem_mem hj))
  have hkE := SourceStoredNames.stored_input P hk
  have hname : recs[j].cnst.name = k := inputsNamed P.compiled k _ hkE
  rw [hname]
  exact ⟨hkE, h0⟩

end Group

/-! ## The group's two blocks -/

/-- **The inductive block's inductives**: one per type, the first with the first type's
level-parameter count. -/
theorem inductive_block_first {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)}
    (hcsize : ctors.size = types.size) {first : Ix.InductiveVal} (hfirst : types[0]? = some first)
    {context : CompileEnv × BlockEnv} {before after : BlockState} {output : BlockResult}
    (ran : rawRun (compileMutualBlock ((InductiveCompile.indsOf types ctors).map MutConst.indc))
      context before = (.ok output, after)) :
    ∃ ms, output.block.info = .muts ms ∧ (inductives ms).size = types.size ∧
      ∀ slot t₀, (inductives ms)[0]? = some (slot, t₀) → t₀.lvls.toNat = first.cnst.levelParams.size := by
  obtain ⟨ps, headers, same⟩ := block_headers ran
  obtain ⟨ts, rfl, hts⟩ := headers_indcs headers
  obtain ⟨ts', hinfo, herase⟩ := InductiveCompile.erase_indcs same
  have hts' : List.Forall₂ ProjectionLayout.IndHeader (InductiveCompile.indsOf types ctors) ts' :=
    forall₂_erase (R := ProjectionLayout.IndHeader) (T := ProjectionLayout.IndHeader)
      (S := fun t' t => SharingRoots.eraseMut (.indc t') = SharingRoots.eraseMut (.indc t))
      (fun _ _ _ h e => indHeader_erase h e) hts herase
  have hlen := InductiveCompile.forall₂_length hts'
  rw [InductiveCompile.indsOf_length hcsize] at hlen
  refine ⟨_, hinfo, by rw [inductives_indcs_size, ← hlen], fun slot t₀ h0 => ?_⟩
  rw [inductives_indcs_get] at h0
  obtain ⟨t', ht', he⟩ := Option.map_eq_some_iff.mp h0
  cases he
  have h0T : 0 < types.size := (Array.getElem?_eq_some_iff.mp hfirst).1
  obtain ⟨hl0, ht0⟩ := List.getElem?_eq_some_iff.mp ht'
  have hi : 0 < (InductiveCompile.indsOf types ctors).length := by rw [InductiveCompile.indsOf_length hcsize]; exact h0T
  have header := InductiveCompile.forall₂_getElem hts' 0 hi hl0
  rw [ht0, InductiveCompile.indsOf_getElem hcsize hi] at header
  have hf : types[0] = first := (Array.getElem?_eq_some_iff.mp hfirst).2
  rw [header.1]
  simp [InductiveCompile.indOf, hf]

/-- **The recursor family's record's members are the family's recursors**, by either compile
path, each with its header. -/
theorem family_block_members {recs : Array Ix.RecursorVal} (hrne : recs.toList ≠ []) {key₂ : Ix.Name}
    {context : CompileEnv × BlockEnv} {before after : BlockState} {output : BlockResult}
    (ran : rawRun (compileMutualBlock (recs.toList.map MutConst.recr)) context before =
        (.ok output, after) ∨
      ∃ r, recs.toList = [r] ∧ key₂ = r.cnst.name ∧
        rawRun (compileConstantInfo (.recInfo r)) context before = (.ok output, after)) :
    ∀ p rI, (p, rI) ∈ recursorMembers output.block → ∃ hp : p < recs.size, BlockEmission.RecHeader recs[p] rI := by
  intro p rI hm
  rcases ran with ran | ⟨r, hr, -, ran⟩
  · obtain ⟨ps, headers, same⟩ := block_headers ran
    obtain ⟨ts, rfl, hts⟩ := headers_recrs headers
    obtain ⟨hp, h⟩ := family_members hrne same hts p rI hm
    exact ⟨by simpa using hp, by simpa using h⟩
  · obtain ⟨t₁, same, header⟩ := lone_header ran
    have hts : List.Forall₂ BlockEmission.RecHeader recs.toList [t₁] := by rw [hr]; exact .cons header .nil
    obtain ⟨hp, h⟩ := family_members hrne same hts p rI hm
    exact ⟨by simpa using hp, by simpa using h⟩

/-! ## The family's slots -/

/-- **A published recursor sits at the family member its record resolves to.** -/
theorem publishedRecursor_at {x : Ix.Name} {Q R : Address} {c : Ixon.Constant} {j : Nat}
    (haddr : addrOf ixe x = some Q) (hc : recordAt ixe Q = some c)
    (hq : resolveSource (recordAt ixe) Q c = some (.member R j)) {o : Address} {j' : Nat}
    (hp : publishedRecursor? ixe x = some (o, j')) : o = R ∧ j' = j := by
  unfold addrOf at haddr
  obtain ⟨named, hn, rfl⟩ := Option.map_eq_some_iff.mp haddr
  have hs : storedRecord ixe named.addr = some c := hc
  unfold publishedRecursor? at hp
  simp only [hn, hs, bind, Option.bind_some] at hp
  cases hi : c.info with
  | rPrj p =>
    simp only [hi, pure, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    have := InductiveSegments.resolveSource_rPrj hi hq
    cases this
    exact ⟨rfl, rfl⟩
  | recr _ =>
    simp only [hi, pure, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    simp only [resolveSource, hi, Option.some.injEq, ConstRef.member.injEq] at hq
    exact ⟨hq.1, hq.2⟩
  | _ => simp [hi] at hp

/-- **What the report checks give of a group's recursor family**, at its compiled records:
the family's record holds the family's recursors, each with its header, and member `j` is
filed at the inductive block's motive `j`, its first carriers the block's members, its major
premise an inductive whose constructors are where its rules' constructors are published. -/
structure FamilyFacts (ixe : Ixon.Env) (first : Ix.InductiveVal) (recs : Array Ix.RecursorVal)
    (B R : Address) (cR : Ixon.Constant) : Prop where
  stored : recordAt ixe R = some cR
  members : ∀ p rI, (p, rI) ∈ recursorMembers cR → ∃ hp : p < recs.size, BlockEmission.RecHeader recs[p] rI
  named : ∀ j (hj : j < recs.size), namedMotive? first recs[j].cnst.name = some j
  slot : ∀ j (hj : j < recs.size), ∃ r cs mb mi ind, (j, r) ∈ recursorMembers cR ∧
    recursorAnalysis? (recordAt ixe) R cR r = some (B, j, cs, .member mb mi) ∧
    (∀ i < first.all.size, cs[i]? = some (.member B i)) ∧
    inductiveAt (recordAt ixe) (.member mb mi) = some ind ∧ ind.ctors.size = recs[j].rules.size ∧
    ∀ k (hk : k < recs[j].rules.size), ∃ cn, ixe.named.get? recs[j].rules[k].ctor = some cn ∧
      resolve (recordAt ixe) cn.addr = some (.ctor mb mi k)

/-- **The family's slots, from the report checks**: `RecursorShapes` files each recursor at the
motive its name gives it; that motive is at most its position (`namedMotive_le`) and the slots are
distinct (`RecursorSlotsUnique`), so it is its position. -/
theorem family_facts {env : Ix.Environment} (slots : RecursorSlotsUnique ixe) (shapes : RecursorShapes env ixe)
    {n : Ix.Name} {first : Ix.InductiveVal} (hgetn : env.consts.get? n = some (.inductInfo first))
    {fnamed : Ixon.Named} (hfn : ixe.named.get? n = some fnamed) {B R : Address}
    (hblk : blockAt ixe fnamed.addr = B) {recs : Array Ix.RecursorVal}
    (horder : ∀ j (hj : j < recs.size),
      (∃ hj' : j < first.all.size, Ix.LeanIngress.isStrName first.all[j] "rec" recs[j].cnst.name = true) ∨
      (first.all.size ≤ j ∧ j - first.all.size < first.numNested ∧
        Ix.LeanIngress.isStrName first.cnst.name s!"rec_{j - first.all.size + 1}" recs[j].cnst.name = true))
    (stored : ∀ j (hj : j < recs.size), (recs[j].cnst.name, Ix.ConstantInfo.recInfo recs[j]) ∈ env.consts.toList ∧
      recs[j].all[0]? = some n)
    (published : ∀ j (hj : j < recs.size), ∃ Q c, addrOf ixe recs[j].cnst.name = some Q ∧ recordAt ixe Q = some c ∧
      resolveSource (recordAt ixe) Q c = some (.member R j))
    {cR : Ixon.Constant} (hR : recordAt ixe R = some cR)
    (members : ∀ p rI, (p, rI) ∈ recursorMembers cR → ∃ hp : p < recs.size, BlockEmission.RecHeader recs[p] rI) :
    FamilyFacts ixe first recs B R cR := by
  -- each recursor's shape, at its named motive
  have shaped : ∀ j (hj : j < recs.size), ∃ m r cs mb mi ind, namedMotive? first recs[j].cnst.name = some m ∧
      (j, r) ∈ recursorMembers cR ∧ recursorAnalysis? (recordAt ixe) R cR r = some (B, m, cs, .member mb mi) ∧
      (∀ i < first.all.size, cs[i]? = some (.member B i)) ∧
      inductiveAt (recordAt ixe) (.member mb mi) = some ind ∧ ind.ctors.size = recs[j].rules.size ∧
      ∀ k (hk : k < recs[j].rules.size), ∃ cn, ixe.named.get? recs[j].rules[k].ctor = some cn ∧
        resolve (recordAt ixe) cn.addr = some (.ctor mb mi k) := by
    intro j hj
    obtain ⟨hE, h0⟩ := stored j hj
    obtain ⟨Q, c, haddr, hc, hq⟩ := published j hj
    obtain ⟨named, hnamed, -⟩ := Option.map_eq_some_iff.mp haddr
    obtain ⟨first', fv, m, fnamed', owner, j', c', r, cs, mb, mi, ind, h0', hfv, hm, hfn', hpub, hc', hmem, han,
      hcs, hind, hsize, hrules⟩ := shapes _ _ named hE hnamed
    rw [h0] at h0'
    cases h0'
    rw [hgetn] at hfv
    cases hfv
    rw [hfn] at hfn'
    cases hfn'
    obtain ⟨rfl, rfl⟩ := publishedRecursor_at haddr hc hq hpub
    rw [hR] at hc'
    cases hc'
    rw [hblk] at han hcs
    exact ⟨m, r, cs, mb, mi, ind, hm, hmem, han, hcs, hind, hsize, hrules⟩
  -- the named motive is the position
  have motive : ∀ j (hj : j < recs.size), namedMotive? first recs[j].cnst.name = some j := by
    intro j
    induction j using Nat.strongRecOn with
    | ind j ih =>
      intro hj
      obtain ⟨m, r, cs, mb, mi, ind, hm, hmem, han, -⟩ := shaped j hj
      have hle := namedMotive_le hm (horder j hj)
      rcases Nat.lt_or_eq_of_le hle with hlt | rfl
      · exfalso
        have him := ih m hlt (by omega)
        obtain ⟨m', r', cs', mb', mi', ind', hm', hmem', han', -⟩ := shaped m (by omega)
        rw [him] at hm'
        cases hm'
        have := slots.2 R R cR cR j m r r' (B, m) hR hR hmem hmem'
          (by simp [recursorSlot?, han]) (by simp [recursorSlot?, han'])
        omega
      · exact hm
  refine ⟨hR, members, motive, fun j hj => ?_⟩
  obtain ⟨m, r, cs, mb, mi, ind, hm, hmem, han, hcs, hind, hsize, hrules⟩ := shaped j hj
  rw [motive j hj] at hm
  cases hm
  exact ⟨r, cs, mb, mi, ind, hmem, han, hcs, hind, hsize, hrules⟩

/-! ## The candidates at the group's block -/

/-- **A record member a published name's records hold is that name's published member.** -/
theorem owner_of_nameRecords {x : Ix.Name} {o : Address} (ho : o ∈ nameRecords ixe x) {c : Ixon.Constant}
    (hc : recordAt ixe o = some c) {p : Nat} {rI : Ixon.Recursor} (hm : (p, rI) ∈ recursorMembers c)
    {x' : Ix.Name} (same : ixe.named.get? x' = ixe.named.get? x) {owner : Address} {j : Nat}
    (hp : publishedRecursor? ixe x' = some (owner, j)) : o = owner := by
  unfold nameRecords addrOf at ho
  cases hn : ixe.named.get? x with
  | none => rw [hn] at ho; simp at ho
  | some named =>
    rw [hn] at ho
    simp only [Option.map_some, List.mem_cons, List.not_mem_nil, or_false] at ho
    unfold publishedRecursor? at hp
    rw [same, hn] at hp
    simp only [bind, Option.bind_some] at hp
    cases hs : storedRecord ixe named.addr with
    | none => simp [hs] at hp
    | some c₄ =>
      have hr : recordAt ixe named.addr = some c₄ := hs
      simp only [hs, Option.bind_some] at hp
      have hblock : blockAt ixe named.addr = ownerOf named.addr c₄ := by simp [blockAt, hr]
      cases hi : c₄.info with
      | rPrj q =>
        simp only [hi, pure, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        rcases ho with rfl | rfl
        · rw [hr] at hc
          cases hc
          simp [recursorMembers, hi] at hm
        · rw [hblock]
          simp [ownerOf, hi]
      | recr _ =>
        simp only [hi, pure, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        rcases ho with rfl | rfl
        · rfl
        · rw [hblock]
          simp [ownerOf, hi]
      | _ => simp [hi] at hp

/-- **A candidate the closure's index could file under the group's block is a member of the
family's record, at its own position.** A prelude record never files under a block the closure
supplies; a closure record files at its artifact slot, which `RecursorsOwned` puts in the
family (it is filed so in the artifact's index), and the family's slots are its record's members'. -/
theorem family_candidate {env : Ix.Environment} {S : Address → Prop} (corder : ClosureOrder ixe S order)
    (slots : RecursorSlotsUnique ixe) (shapes : RecursorShapes env ixe) (owned : RecursorsOwned env ixe)
    {B : Address} {cB : Ixon.Constant} (hB : B ∈ order) (hcB : recordAt ixe B = some cB)
    {n : Ix.Name} {first : Ix.InductiveVal} (hgetn : env.consts.get? n = some (.inductInfo first))
    (hn0 : first.all[0]? = some n) {fnamed : Ixon.Named} (hfn : ixe.named.get? n = some fnamed)
    (hblk : blockAt ixe fnamed.addr = B) {recs : Array Ix.RecursorVal}
    (hsize : recs.size = first.all.size + first.numNested) {R : Address} {cR : Ixon.Constant}
    (fam : FamilyFacts ixe first recs B R cR) :
    ∀ ref entry, From (closureContext ixe t preA order).store (scannedOf ixe t preA order) ref entry →
      entry.block = B → ∃ p < recs.size, ref = .member R p ∧ entry.motive = p := by
  intro ref entry hfrom hblock
  obtain ⟨o, c, p, rI, cs, rfl, present, hm, han⟩ := analysis_of_from hfrom
  rw [hblock] at han
  obtain ⟨ha, fi, -, -, -, -, hcs, -⟩ := recursorAnalysis_spec.mp han
  rcases scanned_cases present with ⟨ho, hc⟩ | hfb
  rotate_left
  · exact absurd (hfb p rI hm _ _ _ B fi ha hcs hB) (by rw [hcB]; simp)
  -- the artifact's slot
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (slots.1 o c hc p rI hm)
  obtain ⟨y', hy', -⟩ := Option.map_eq_some_iff.mp hy
  have han' := (analysis_closure (t := t) (preA := preA) corder ho hc hy').1
  rw [han] at han'
  cases han'
  -- filed under the block in the artifact's index
  obtain ⟨first₁, slot₁, bc₁, ms₁, -, -, -, hfromA⟩ := from_of_analysis (records := storedRecords ixe)
    (mem_storedRecords hc) hm hy'
  obtain ⟨chosen, shapeA, -, -, -, hshapeA, hinA⟩ :=
    ReaderIndexDiscovery.buildIndex_unique_reference (recordAt ixe) (storedRecords ixe) (storedRecords_coherent ixe)
      _ _ hfromA (by
        intro other chosen' hother hb hmo
        obtain ⟨o₂, c₂, p₂, r₂, cs₂, rfl, present₂, hm₂, han₂⟩ := analysis_of_from hother
        have hc₂ := storedRecords_coherent ixe o₂ c₂ present₂
        have := slots.2 o₂ o c₂ c p₂ p r₂ rI (B, entry.motive) hc₂ hc hm₂ hm
          (by simp [recursorSlot?, han₂, hb, hmo]) (by simp [recursorSlot?, hy'])
        rw [this.1, this.2])
  -- the family the artifact's index files it in
  have hcontains : env.consts.contains n = true := by
    rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, hgetn]
    rfl
  have haddr : addrOf ixe n = some fnamed.addr := by unfold addrOf; rw [hfn]; rfl
  obtain ⟨first₂, hff, hall⟩ := owned B shapeA hshapeA n fnamed.addr hcontains haddr hblk
  have hf2 : first₂ = n := by
    rcases hff with ⟨iv, hiv, h0⟩ | ⟨cv, iv, hcv, -, -⟩ | ⟨rv, i', iv, hrv, -, -, -⟩
    · rw [hgetn] at hiv
      cases hiv
      rw [hn0] at h0
      exact (Option.some.inj h0).symm
    · rw [hgetn] at hcv; cases hcv
    · rw [hgetn] at hrv; cases hrv
  subst hf2
  obtain ⟨rn, rv, hrn, hrv0, hob⟩ := hall _ hinA
  -- its published recursor's slot is one of the family's
  obtain ⟨k, hkrn, hk⟩ := (Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList).mp
    (show env.consts[rn]? = some _ by rw [← Std.HashMap.get?_eq_getElem?]; exact hrn)
  have same : ixe.named.get? k = ixe.named.get? rn := by
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.getElem?_congr (BEq.symm hkrn)
  have hnamed : ∃ named, ixe.named.get? rn = some named := by
    unfold nameRecords addrOf at hob
    cases hn : ixe.named.get? rn with
    | none => rw [hn] at hob; simp at hob
    | some named => exact ⟨named, rfl⟩
  obtain ⟨named, hnamed⟩ := hnamed
  obtain ⟨first₃, fv, m₃, fnamed₃, owner₃, j₃, c₃, r₃, cs₃, mb₃, mi₃, ind₃, h0₃, hfv₃, hm₃, hfn₃, hpub₃, hc₃,
    hmem₃, han₃, -⟩ := shapes k rv named hk (by rw [same]; exact hnamed)
  rw [hrv0] at h0₃
  cases h0₃
  rw [hgetn] at hfv₃
  cases hfv₃
  rw [hfn] at hfn₃
  cases hfn₃
  rw [hblk] at han₃
  have hm₃lt : m₃ < recs.size := by rw [hsize]; exact namedMotive_lt hm₃
  obtain ⟨rm, csm, mbm, mim, -, hmemm, hanm, -⟩ := fam.slot m₃ hm₃lt
  have hown := slots.2 owner₃ R c₃ cR j₃ m₃ r₃ rm (B, m₃) hc₃ fam.stored hmem₃ hmemm
    (by simp [recursorSlot?, han₃]) (by simp [recursorSlot?, hanm])
  have ho' : o = owner₃ := owner_of_nameRecords hob hc hm same hpub₃
  have hoR : o = R := ho'.trans hown.1
  subst hoR
  rw [fam.stored] at hc
  cases hc
  obtain ⟨hp, -⟩ := fam.members p rI hm
  refine ⟨p, hp, rfl, ?_⟩
  obtain ⟨rp, csp, mbp, mip, -, hmemp, hanp, -⟩ := fam.slot p hp
  have hr := ReaderIndex.member_unique _ p rI rp hm hmemp
  subst hr
  rw [hanp] at hy'
  simp only [Option.some.injEq, Prod.mk.injEq] at hy'
  exact hy'.2.1.symm

/-! ## Quotient Source's motives -/

/-- **A non-nested family that quotient Source lowers has as many motives as types in every
recursor** (`lowerInductive`'s checks). -/
theorem quotient_motives {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)}
    {recs : Array Ix.RecursorVal} {conv : Ix.LeanIngress.Converted}
    (src : Ix.LeanIngress.convertInductive types ctors recs = .ok conv) {first : Ix.InductiveVal}
    (hfirst : types[0]? = some first) {ρ : Ix.LeanIngress.FiberMap} {stS : State .source} {rS : Read .source}
    (lowered : Ix.LeanIngress.lower stS (conv.quotient ρ) = .ok rS)
    (hn : CtxAgree.numNestedOf (InductiveUnits.srcBlock types ctors recs first) = 0) :
    ∀ j (hj : j < recs.size), recs[j].numMotives = types.size := by
  obtain ⟨first', hfirst', hconv, -, -⟩ := InductiveUnits.convertInductive_src src
  rw [hfirst] at hfirst'
  cases hfirst'
  have hq : conv.quotient ρ = .inductive (Ix.LeanIngress.BlockRead.canon
      (Ix.LeanIngress.BlockRead.substKeys ρ (InductiveUnits.srcBlock types ctors recs first))) := by
    rw [hconv]
    rfl
  rw [hq] at lowered
  obtain ⟨checks, -⟩ := LowerTransfer.lowerInductive_iff.mp
    (show lowerInductive stS (Ix.LeanIngress.BlockRead.canon (Ix.LeanIngress.BlockRead.substKeys ρ
      (InductiveUnits.srcBlock types ctors recs first))) = .ok rS from lowered)
  -- the renaming and canonical levels keep the counts
  have hcounts : ((Ix.LeanIngress.BlockRead.canon (Ix.LeanIngress.BlockRead.substKeys ρ
      (InductiveUnits.srcBlock types ctors recs first))).recs.map (·.2.1)) =
      (InductiveUnits.srcBlock types ctors recs first).recs.map (·.2.1) := by
    simp only [Ix.LeanIngress.BlockRead.canon, Ix.LeanIngress.BlockRead.substKeys, Array.map_map]
    congr 1
  have htypes : (Ix.LeanIngress.BlockRead.canon (Ix.LeanIngress.BlockRead.substKeys ρ
      (InductiveUnits.srcBlock types ctors recs first))).types.size = types.size := by
    simp [Ix.LeanIngress.BlockRead.canon, Ix.LeanIngress.BlockRead.substKeys, InductiveUnits.srcBlock]
  have hrec : ∀ j (hj : j < recs.size), ((InductiveUnits.srcBlock types ctors recs first).recs.map (·.2.1))[j]? =
      some (InductiveUnits.srcCounts types recs[j]) := by
    intro j hj
    simp [InductiveUnits.srcBlock, InductiveUnits.srcRec, hj]
  have hnest : CtxAgree.numNestedOf (Ix.LeanIngress.BlockRead.canon (Ix.LeanIngress.BlockRead.substKeys ρ
      (InductiveUnits.srcBlock types ctors recs first))) = 0 := by
    have e0 := congrArg (·[0]?) hcounts
    simp only [Array.getElem?_map] at e0
    unfold CtxAgree.numNestedOf at hn ⊢
    rw [htypes]
    cases h0 : (InductiveUnits.srcBlock types ctors recs first).recs[0]? with
    | none =>
      rw [h0] at e0
      cases h0' : (Ix.LeanIngress.BlockRead.canon (Ix.LeanIngress.BlockRead.substKeys ρ
          (InductiveUnits.srcBlock types ctors recs first))).recs[0]? with
      | none => rfl
      | some x => simp [h0'] at e0
    | some y =>
      rw [h0] at e0 hn
      cases h0' : (Ix.LeanIngress.BlockRead.canon (Ix.LeanIngress.BlockRead.substKeys ρ
          (InductiveUnits.srcBlock types ctors recs first))).recs[0]? with
      | none => simp [h0'] at e0
      | some x =>
        rw [h0'] at e0
        simp only [Option.map_some, Option.some.injEq] at e0
        obtain ⟨_, rc, _⟩ := x
        obtain ⟨_, rc', _⟩ := y
        simp only at e0 hn ⊢
        rw [e0]
        simpa [InductiveUnits.srcBlock] using hn
  rcases checks with hne | hall
  · exact absurd hnest hne
  intro j hj
  have hj' : j < (Ix.LeanIngress.BlockRead.canon (Ix.LeanIngress.BlockRead.substKeys ρ
      (InductiveUnits.srcBlock types ctors recs first))).recs.size := by
    have := congrArg Array.size hcounts
    simp only [Array.size_map] at this
    rw [this]
    simpa [InductiveUnits.srcBlock] using hj
  have hx := hall _ (Array.getElem_mem_toList hj')
  have ej := congrArg (·[j]?) hcounts
  simp only at ej
  rw [hrec j hj, Array.getElem?_map, Array.getElem?_eq_getElem hj', Option.map_some, Option.some.injEq] at ej
  have := hx.2.1
  rw [ej, htypes] at this
  exact this

theorem array_findIdx?_eq {α : Type} (xs : Array α) (p : α → Bool) : xs.findIdx? p = xs.toList.findIdx? p := by
  rcases xs with ⟨l⟩
  simp [List.findIdx?_toArray]

theorem filterMap_self {f : Nat → Option Nat} : ∀ (l : List Nat), (∀ i ∈ l, f i = some i) → l.filterMap f = l
  | [], _ => rfl
  | i :: l, h => by
    rw [List.filterMap_cons, h i List.mem_cons_self]
    exact congrArg _ (filterMap_self l fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem beqRaw_comm (a b : Ix.Name) : Ix.Name.beqRaw a b = Ix.Name.beqRaw b a := by
  cases h : Ix.Name.beqRaw b a
  · cases h' : Ix.Name.beqRaw a b
    · rfl
    · rw [Ix.Name.beqRaw_iff.mp h', Ix.Name.beqRaw_iff.mpr rfl] at h; cases h
  · rw [Ix.Name.beqRaw_iff.mp h]; exact Ix.Name.beqRaw_iff.mpr rfl

/-- **Quotient Source's motive of an own recursor is its position**: its name is `T.rec` for
the family's `j`-th member `T`, which is the `j`-th type's own name. -/
theorem motiveOf_eq {types : Array Ix.InductiveVal} {first : Ix.InductiveVal} {r : Ix.RecursorVal} {j : Nat}
    (hnames : types.size = first.all.size ∧
      ∀ i (hi : i < types.size) (hi' : i < first.all.size), types[i].cnst.name = first.all[i])
    (hj : j < first.all.size) (hw : Ix.LeanIngress.isStrName first.all[j] "rec" r.cnst.name = true)
    (hm : namedMotive? first r.cnst.name = some j) : SourceConversion.motiveOf types r = some j := by
  have hlist : types.toList.map (·.cnst.name) = first.all.toList := by
    apply List.ext_getElem
    · simp [hnames.1]
    · intro i h₁ h₂
      simp only [List.getElem_map, Array.getElem_toList]
      exact hnames.2 i (by simpa using h₁) (by simpa using h₂)
  cases hname : r.cnst.name with
  | str p s h =>
    rw [hname] at hw hm
    simp only [Ix.LeanIngress.isStrName, Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨rfl, hp⟩ := hw
    have hp := Ix.Name.beqRaw_iff.mp hp
    subst hp
    unfold SourceConversion.motiveOf
    rw [hname]
    simp only
    have hfind : first.all.toList.findIdx? (fun T => Ix.LeanIngress.isStrName T "rec" (.str first.all[j] "rec" h)) =
        types.findIdx? (Ix.Name.beqRaw ·.cnst.name first.all[j]) := by
      rw [array_findIdx?_eq, ← hlist, List.findIdx?_map]
      congr 1
      funext T
      simp [Ix.LeanIngress.isStrName, beqRaw_comm]
    rw [← hfind]
    unfold namedMotive? at hm
    cases hf : first.all.toList.findIdx? (fun T => Ix.LeanIngress.isStrName T "rec" (.str first.all[j] "rec" h)) with
    | none =>
      have := List.findIdx?_eq_none_iff.mp hf first.all[j] (Array.getElem_mem_toList hj)
      simp [Ix.LeanIngress.isStrName, Ix.Name.beqRaw_iff.mpr rfl] at this
    | some i =>
      rw [hf] at hm
      simpa [Option.orElse] using hm
  | _ => simp [hname, Ix.LeanIngress.isStrName] at hw

/-- The carrier order of carriers that are the block's members in order. -/
theorem orderFor_range {cs : Array (ConstRef Address)} {B : Address} {L : Nat}
    (h : ∀ i < L, cs[i]? = some (.member B i)) : orderFor cs B L = (List.range L).toArray := by
  have hL : L ≤ cs.size := by
    rcases Nat.eq_zero_or_pos L with hz | hpos
    · omega
    · have := (Array.getElem?_eq_some_iff.mp (h (L - 1) (by omega))).1
      omega
  have take : cs.toList.take L = (List.range L).map fun i => ConstRef.member B i := by
    apply List.ext_getElem
    · simp; omega
    · intro i h₁ h₂
      have hi : i < L := by simpa using h₂
      simp only [List.getElem_take, List.getElem_map, List.getElem_range, Array.getElem_toList]
      exact (Array.getElem?_eq_some_iff.mp (h i hi)).2
  apply Array.toList_inj.mp
  rw [orderFor, Array.toList_filterMap, Array.toList_extract, List.extract_eq_take_drop, List.drop_zero,
    Nat.sub_zero, take, List.filterMap_map]
  exact filterMap_self _ fun i _ => by simp

/-! ## The closure's recursor index at the group's block -/

/-- **The closure's recursor index at an inductive group's block**: the block's shape lists its
members in order and the recursor family's members in family order, and each member's entry is
filed at its position, with the family's level parameters, its major premise an inductive of
the closure whose constructors are keyed as its rules' constructors, and, for a family without
nested auxiliaries, quotient Source's motive. These are `InductiveSegments.closure_inductive_reads`'
index premises (`TraceSegments.InductiveCompiled.index`, `entries`). -/
theorem closure_recursor_index {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {failures : Failures} {envQ : Env .source} (P : Premises env roots sub ixe failures t envQ)
    (slots : RecursorSlotsUnique ixe) (shapes : RecursorShapes env ixe) (owned : RecursorsOwned env ixe)
    (names : FamilyNamesStored env) (levels : FamilyLevelParams env)
    (prelude : preludeFor t = .ok preA) (corder : ClosureOrder ixe (Seed ixe sub) order)
    (canonical : Stream.StoredCanonical ixe order) (b : Ix.RoleEvidence.Bundle)
    (resolves : SingletonSegments.PublishedResolve ixe sub)
    {hints : CName .source → Option ReducibilityHint} {i : Nat}
    {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal}
    (hgr : (ClosureLayout.quotientGraph ixe t hints sub).groups[i]? = some (.inductive types ctors recs))
    {conv : Ix.LeanIngress.Converted} (src : Ix.LeanIngress.convertInductive types ctors recs = .ok conv)
    {first : Ix.InductiveVal} (hfirst : types[0]? = some first) (hcsize : ctors.size = types.size)
    {rlps : Array Ix.Name} (recLpsEq : ∀ r ∈ recs.toList, r.cnst.levelParams = rlps)
    (recNodup : rlps.toList.Nodup) (hrne : recs.toList ≠ [])
    (typesIn : ∀ i (hi : i < types.size), ∃ ci, (types[i].cnst.name, ci) ∈ sub.consts.toList)
    (ctorsIn : ∀ i (hi : i < ctors.size) k (hk : k < ctors[i].size), ∃ ci, (ctors[i][k].cnst.name, ci) ∈ sub.consts.toList)
    (recsIn : ∀ j (hj : j < recs.size), ∃ ci, (recs[j].cnst.name, ci) ∈ sub.consts.toList)
    -- the inductive block
    {cenv₁ : CompileEnv} {benv₁ : BlockEnv} {out₁ : BlockResult} {after₁ : BlockState}
    (ran₁ : rawRun (compileMutualBlock ((InductiveCompile.indsOf types ctors).map MutConst.indc))
      (cenv₁, benv₁) {} = (.ok out₁, after₁))
    {cenvR₁ : CompileEnv} {all₁ : Ix.Set Ix.Name} {key₁ : Ix.Name} {r₁ : BlockResult} {cache₁ : BlockState}
    (hr₁ : runBlock cenvR₁ all₁ key₁ = .ok (r₁, cache₁))
    (pub₁ : BlockPublication.Published ixe sub key₁ r₁) (hrec₁ : BlockRecords.recordsOf r₁ = BlockRecords.recordsOf out₁)
    -- the recursor family: a block of several, or a lone recursor compiled as a single constant
    {cenv₂ : CompileEnv} {benv₂ : BlockEnv} {out₂ : BlockResult} {after₂ : BlockState}
    {cenvR₂ : CompileEnv} {all₂ : Ix.Set Ix.Name} {key₂ : Ix.Name} {r₂ : BlockResult} {cache₂ : BlockState}
    (hr₂ : runBlock cenvR₂ all₂ key₂ = .ok (r₂, cache₂))
    (pub₂ : BlockPublication.Published ixe sub key₂ r₂) (hrec₂ : BlockRecords.recordsOf r₂ = BlockRecords.recordsOf out₂)
    (ran₂ : rawRun (compileMutualBlock (recs.toList.map MutConst.recr)) (cenv₂, benv₂) {} =
        (.ok out₂, after₂) ∨
      ∃ r, recs.toList = [r] ∧ key₂ = r.cnst.name ∧
        rawRun (compileConstantInfo (.recInfo r)) (cenv₂, benv₂) {} = (.ok out₂, after₂))
    -- quotient Source's reading of the group
    {stS : State .source} {rS : Read .source}
    (lowered : Ix.LeanIngress.lower stS (conv.quotient (fiberAliasAt ixe (roleAtMap t))) = .ok rS) :
    (∃ shape : BlockShape, (closureContext ixe t preA order).index.blocks[out₁.blockAddr]? = some shape ∧
      shape.order = (List.range types.size).toArray ∧
      shape.recs.toList = (List.range recs.size).map fun j => ConstRef.member out₂.blockAddr j) ∧
    ∀ j (hj : j < recs.size), ∃ (entry : RecEntry) (mb : Address) (mi : Nat) (major : Ixon.Inductive),
      (closureContext ixe t preA order).index.recs[ConstRef.member out₂.blockAddr j]? = some entry ∧
      recLps entry.large (List.range first.cnst.levelParams.size) = (SourceConversion.recNum first recs[j]).params ∧
      entry.major = .member mb mi ∧ inductiveAt (closureContext ixe t preA order).store entry.major = some major ∧
      major.ctors.size = recs[j].rules.size ∧
      (∀ k (hk : k < recs[j].rules.size),
        (closureContext ixe t preA order).memberKey (.ctor mb mi k) =
          .ok (InductiveUnits.srcKey (fiberAliasAt ixe (roleAtMap t)) (evAddr ixe b) recs[j].rules[k].ctor)) ∧
      (CtxAgree.numNestedOf (InductiveUnits.srcBlock types ctors recs first) = 0 →
        some entry.motive = SourceConversion.motiveOf types recs[j]) := by
  have hcl : IsClosure env roots sub := P.source.1
  obtain ⟨n, hnE, hn0, hname, htypes, hrecs⟩ := group_head P hgr hfirst
  have hgetn : env.consts.get? n = some (.inductInfo first) := SourceStoredNames.stored_get hnE
  obtain ⟨hsize, horder⟩ := blockRecursors_at hrecs
  have tnames := types_named P names hnE htypes
  have rstored := recs_stored P hrecs
  have h0T : 0 < types.size := (Array.getElem?_eq_some_iff.mp hfirst).1
  have hf0 : types[0] = first := (Array.getElem?_eq_some_iff.mp hfirst).2
  -- the inductive block and the first type's publication
  have hlenI := InductiveCompile.indsOf_length hcsize
  have typesIn' : ∀ i (hi : i < (InductiveCompile.indsOf types ctors).length),
      (sub.consts.get? (InductiveCompile.indsOf types ctors)[i].name).isSome = true := by
    intro i hi
    obtain ⟨ci, hci⟩ := typesIn i (by omega)
    have e : (InductiveCompile.indsOf types ctors)[i].name = types[i].cnst.name := by
      simp [InductiveCompile.indsOf, InductiveCompile.indOf]
    rw [e, SourceStoredNames.stored_get hci]
    rfl
  have ctorsIn' : ∀ i (hi : i < (InductiveCompile.indsOf types ctors).length) k
      (hk : k < (InductiveCompile.indsOf types ctors)[i].ctors.size),
      (sub.consts.get? (InductiveCompile.indsOf types ctors)[i].ctors[k].cnst.name).isSome = true := by
    intro i hi k hk
    have hk' : k < (ctors[i]'(by omega)).size := by simpa [InductiveCompile.indsOf, InductiveCompile.indOf] using hk
    obtain ⟨ci, hci⟩ := ctorsIn i (by omega) k hk'
    have e : (InductiveCompile.indsOf types ctors)[i].ctors[k].cnst.name = (ctors[i]'(by omega))[k].cnst.name := by
      simp [InductiveCompile.indsOf, InductiveCompile.indOf]
    rw [e, SourceStoredNames.stored_get hci]
    rfl
  obtain ⟨-, typesAt, -⟩ := InductiveSegments.inductive_published ran₁ hr₁ pub₁ hrec₁ typesIn' ctorsIn'
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
  obtain ⟨Q₀, hQ₀, hc₀⟩ := typesAt 0 (by omega)
  have e0 : (InductiveCompile.indsOf types ctors)[0].name = n := by
    rw [InductiveCompile.indsOf_getElem hcsize]
    simp [InductiveCompile.indOf, hf0, hname]
  rw [e0] at hQ₀
  obtain ⟨fnamed, hfn, hfa⟩ : ∃ fnamed, ixe.named.get? n = some fnamed ∧ fnamed.addr = Q₀ := by
    unfold addrOf at hQ₀
    obtain ⟨fnamed, h, e⟩ := Option.map_eq_some_iff.mp hQ₀
    exact ⟨fnamed, h, e⟩
  have hblk : blockAt ixe fnamed.addr = out₁.blockAddr := by
    rw [hfa]
    simp [blockAt, hc₀, ownerOf, MutualProjections.memberProjection]
  have hB₁ : out₁.blockAddr ∈ order := by
    obtain ⟨ci, hci⟩ := typesIn 0 h0T
    have hQ₀' : addrOf ixe types[0].cnst.name = some Q₀ := by rw [hf0, hname]; exact hQ₀
    have hQo := InductiveSegments.published_in_order P corder hci hQ₀' hc₀
    exact InductiveSegments.owner_in_order corder hQo hc₀ (by simp [ownerOf, MutualProjections.memberProjection])
  -- the recursor family's publications and record
  have recsIn' : ∀ j (hj : j < recs.toList.length), ∃ ci, (recs.toList[j].cnst.name, ci) ∈ sub.consts.toList :=
    fun j hj => by simpa using recsIn j (by simpa using hj)
  have recAt := InductiveSegments.recursor_published resolves hrne hr₂ pub₂ hrec₂ ran₂ recsIn'
  have published : ∀ j (hj : j < recs.size), ∃ Q c, addrOf ixe recs[j].cnst.name = some Q ∧
      recordAt ixe Q = some c ∧ resolveSource (recordAt ixe) Q c = some (.member out₂.blockAddr j) := by
    intro j hj
    obtain ⟨Q, c, hQ, hc, hq, -⟩ := recAt j (by simpa using hj)
    simp only [Array.getElem_toList] at hQ
    exact ⟨Q, c, hQ, hc, hq⟩
  have h0R : 0 < recs.size := by
    rcases hr : recs.toList with _ | ⟨r, rs⟩
    · exact absurd hr hrne
    · have := congrArg List.length hr
      simp only [Array.length_toList, List.length_cons] at this
      omega
  have hB₂ : out₂.blockAddr ∈ order := by
    obtain ⟨Q, c, hQ, hc, -, hown⟩ := recAt 0 (by simpa using h0R)
    obtain ⟨ci, hci⟩ := recsIn 0 h0R
    simp only [Array.getElem_toList] at hQ
    exact InductiveSegments.owner_in_order corder (InductiveSegments.published_in_order P corder hci hQ hc) hc hown
  have fam := family_facts slots shapes hgetn hfn hblk horder rstored published stored₂ (family_block_members hrne ran₂)
  have cand := family_candidate (t := t) (preA := preA) corder slots shapes owned hB₁ stored₁ hgetn hn0 hfn hblk
    hsize fam
  obtain ⟨msB, hinfoB, hsizeB, hfirstB⟩ := inductive_block_first hcsize hfirst ran₁
  have coherent := closure_coherent (ixe := ixe) prelude corder.nodup
  have storeR := ClosureKeying.closure_store (t := t) (preA := preA) corder.nodup hB₂ stored₂
  have storeB := ClosureKeying.closure_store (t := t) (preA := preA) corder.nodup hB₁ stored₁
  -- each member's filing, in the closure's context
  have filed : ∀ j (hj : j < recs.size), ∃ r cs mb mi ind, (j, r) ∈ recursorMembers out₂.block ∧
      recursorAnalysis? (closureContext ixe t preA order).store out₂.blockAddr out₂.block r =
        some (out₁.blockAddr, j, cs, .member mb mi) ∧ mb ∈ order ∧
      (∀ i < first.all.size, cs[i]? = some (.member out₁.blockAddr i)) ∧
      inductiveAt (recordAt ixe) (.member mb mi) = some ind ∧ ind.ctors.size = recs[j].rules.size ∧
      ∀ k (hk : k < recs[j].rules.size), ∃ cn, ixe.named.get? recs[j].rules[k].ctor = some cn ∧
        resolve (recordAt ixe) cn.addr = some (.ctor mb mi k) := by
    intro j hj
    obtain ⟨r, cs, mb, mi, ind, hmem, han, hcs, hind, hisize, hrules⟩ := fam.slot j hj
    obtain ⟨hanS, -, hmb⟩ := analysis_closure (t := t) (preA := preA) corder hB₂ stored₂ han
    exact ⟨r, cs, mb, mi, ind, hmem, hanS, hmb, hcs, hind, hisize, hrules⟩
  -- every member files under the inductive block, which the closure stores, so the index scans
  -- the family's record
  have scanned₂ : (out₂.blockAddr, out₂.block) ∈ scannedOf ixe t preA order := by
    refine order_scanned hB₂ stored₂ fun j r hm m cs mj b i han hcs => ?_
    obtain ⟨hj, -⟩ := fam.members j r hm
    obtain ⟨r', cs', mb, mi, ind, hm', hanS, -⟩ := filed j hj
    cases recursorMembers_unique hm hm'
    obtain ⟨ha', fi, bc, ms, slot, first', hcar, -⟩ := recursorAnalysis_spec.mp hanS
    rw [han] at ha'
    cases ha'
    rw [hcs] at hcar
    cases hcar
    exact ⟨hB₁, by rw [stored₁]; rfl⟩
  -- each member is the one filed at its slot
  have entryOf : ∀ j (hj : j < recs.size), ∃ chosen shape,
      (closureContext ixe t preA order).index.recs[ConstRef.member out₂.blockAddr j]? = some chosen ∧
      chosen.block = out₁.blockAddr ∧ chosen.motive = j ∧
      (closureContext ixe t preA order).index.blocks[out₁.blockAddr]? = some shape := by
    intro j hj
    obtain ⟨r, cs, mb, mi, ind, hmem, hanS, -⟩ := filed j hj
    obtain ⟨fA, sA, bcA, msA, -, -, -, hfrom⟩ := from_of_analysis (records := scannedOf ixe t preA order)
      scanned₂ hmem hanS
    obtain ⟨chosen, shape, hrecs', hb, hm, hshape, -⟩ :=
      ReaderIndexDiscovery.buildIndex_unique_reference _ _ coherent _ _ hfrom (by
        intro other chosen' hother hb hm
        obtain ⟨p, -, rfl, hmp⟩ := cand other chosen' hother hb
        rw [← hmp, hm])
    exact ⟨chosen, shape, hrecs', hb, hm, hshape⟩
  -- the block's shape
  have hrecsEq := buildIndex_recs (closureContext ixe t preA order).store (scannedOf ixe t preA order)
  obtain ⟨c0, shape, hc0, hb0, -, hshape⟩ := entryOf 0 h0R
  have backed := ReaderIndexDiscovery.collect_backed (closureContext ixe t preA order).store
    (scannedOf ixe t preA order)
  have inPairs : ∀ j (hj : j < recs.size), (j, ConstRef.member out₂.blockAddr j) ∈
      (collected (closureContext ixe t preA order).store (scannedOf ixe t preA order)).2.getD out₁.blockAddr #[] := by
    intro j hj
    obtain ⟨chosen, -, hrecs', hb, hm, -⟩ := entryOf j hj
    rw [closure_index, hrecsEq] at hrecs'
    have := backed _ chosen hrecs'
    rw [hb, hm] at this
    exact this
  obtain ⟨pairs, hp, -⟩ := mem_getD (inPairs 0 h0R)
  obtain ⟨s, hs, rfl⟩ := buildIndex_at _ _ (show (buildIndex _ _).blocks[out₁.blockAddr]? = some shape from hshape) hp
  have origins := ReaderIndex.collect_origins (closureContext ixe t preA order).store (scannedOf ixe t preA order)
  refine ⟨⟨_, hshape, ?order, ?recs⟩, fun j hj => ?entries⟩
  case order =>
    obtain ⟨owner, c, j, r, motive, cs, major, fi, bc, ms, slot, first', present, hmem, ha, hcs, hbc, hms, hfirst',
      hv, horder'⟩ := (collect_inv _ _).1 _ s hs
    obtain ⟨fA, sA, bcA, msA, -, -, -, hfrom⟩ := from_of_analysis present hmem
      (recursorAnalysis_spec.mpr ⟨ha, fi, bc, ms, slot, first', hcs, hbc, hms, hfirst', hv⟩)
    obtain ⟨p, hp, href, -⟩ := cand _ _ hfrom rfl
    obtain ⟨hoR, hjp⟩ := ConstRef.member.inj href
    subst hoR
    rw [hjp] at hmem
    have hcR := coherent _ _ present
    rw [storeR] at hcR
    cases hcR
    obtain ⟨rp, csp, mbp, mip, -, hmemp, hanp, -, hcsp, -⟩ := filed p hp
    have hr := ReaderIndex.member_unique _ p r rp hmem hmemp
    subst hr
    have ha' := ha.symm.trans (recursorAnalysis_spec.mp hanp).1
    simp only [Option.some.injEq, Prod.mk.injEq] at ha'
    obtain ⟨-, rfl, -⟩ := ha'
    cases (hbc.symm.trans storeB)
    rw [hinfoB] at hms
    cases hms
    show s.order = _
    rw [horder', hsizeB, tnames.1, orderFor_range hcsp]
  case recs =>
    show ((pairs.qsort (fun x y => x.1 < y.1)).map (·.2)).toList = _
    refine sorted_eq_range ?_ ?_ ?_
    · have := (collect_inv (closureContext ixe t preA order).store (scannedOf ixe t preA order)).2 out₁.blockAddr
      rw [Std.HashMap.getD_eq_getD_getElem?, hp] at this
      exact this
    · intro x hx
      obtain ⟨entry, hentry, hb, hm⟩ := origins.2.1 _ pairs hp x hx
      obtain ⟨p, hp', href, hmp⟩ := cand _ _ (origins.1 _ entry hentry) hb
      exact ⟨by rw [← hm, hmp]; exact hp', by rw [href, ← hm, hmp]⟩
    · intro j hj
      have := inPairs j hj
      rw [Std.HashMap.getD_eq_getD_getElem?, hp] at this
      exact this
  case entries =>
    obtain ⟨chosen, -, hrecs', hb, hm, -⟩ := entryOf j hj
    obtain ⟨r, cs, mb, mi, ind, hmem, hanS, hmb, -, hind, hisize, hrules⟩ := filed j hj
    -- the filed entry is the member's analysis
    have hfromC := (ReaderIndex.buildIndex_valid _ _).1 _ chosen hrecs'
    obtain ⟨owner', c', pos', rec', cs', fi', bc', ms', slot', first', href, present', hmem', ha', -, hbc', hms',
      hfirst', -, hlarge⟩ := hfromC
    obtain ⟨hoR, hjp⟩ := ConstRef.member.inj href
    subst hoR
    subst hjp
    have hcR := coherent _ _ present'
    rw [storeR] at hcR
    cases hcR
    have hr := ReaderIndex.member_unique _ j rec' r hmem' hmem
    subst hr
    have haS := ha'.symm.trans (recursorAnalysis_spec.mp hanS).1
    simp only [Option.some.injEq, Prod.mk.injEq] at haS
    obtain ⟨-, -, hmajor⟩ := haS
    rw [hb] at hbc'
    cases (hbc'.symm.trans storeB)
    rw [hinfoB] at hms'
    cases hms'
    obtain ⟨hpj, header⟩ := fam.members j rec' hmem
    have hjrec : recs[j] ∈ recs.toList := Array.getElem_mem_toList hj
    refine ⟨chosen, mb, mi, ind, hrecs', ?large, hmajor, ?_, hisize, ?keys, ?motive⟩
    case large =>
      have hlvl := hfirstB _ _ hfirst'
      rw [hlarge, header.1, hlvl, recLpsEq _ hjrec]
      have hsizes := levels.2.2 _ _ n first (SourceStoredNames.stored_get (rstored j hj).1) (rstored j hj).2 hgetn
      rw [recLpsEq _ hjrec] at hsizes
      simp only [SourceConversion.recNum, recLpsEq _ hjrec]
      exact recLps_params recNodup hsizes
    · rw [hmajor]
      exact inductiveAt_closure corder.nodup hmb hind
    case keys =>
      intro k hk
      obtain ⟨cn, hcn, hres⟩ := hrules k hk
      have hrE := (rstored j hj).1
      obtain ⟨ci', hci'⟩ := names _ _ hrE recs[j].rules[k].ctor (by
        simp only [familyNamesOf, List.mem_append, List.mem_map]
        exact .inr ⟨recs[j].rules[k], Array.getElem_mem_toList hk, rfl⟩)
      obtain ⟨ciR, hciR⟩ := recsIn j hj
      have hreach : Reaches env roots recs[j].rules[k].ctor :=
        .step (FamilyGroups.reaches_of_sub hcl (by rw [SourceStoredNames.stored_get hciR]; rfl))
          ⟨_, SourceStoredNames.stored_get hrE, .inl (refsOf_rule recs[j] (Array.getElem_mem_toList hk))⟩
      have hsubget : sub.consts.get? recs[j].rules[k].ctor = some ci' :=
        ((hcl _).1 hreach).trans (SourceStoredNames.stored_get hci')
      obtain ⟨k', hk'⟩ := SourceStoredNames.lookup_stored hsubget
      have e1 := inputsNamed P.compiled _ _ (SourceStoredNames.stored_input P hk')
      have e2 := inputsNamed P.compiled _ _ hci'
      rw [e1] at e2
      subst e2
      obtain ⟨cc, hcc, hq⟩ := Option.bind_eq_some_iff.mp hres
      have haddr : addrOf ixe recs[j].rules[k].ctor = some cn.addr := by unfold addrOf; rw [hcn]; rfl
      exact (InductiveSegments.published_key P prelude corder canonical b hk' haddr hcc hq).2
    case motive =>
      intro hnest
      rw [hm]
      have hmot := quotient_motives src hfirst lowered hnest j hj
      have hlt := analyse_motive_lt ha'
      rw [hm, header.2.2.2.1, hmot, tnames.1] at hlt
      rcases horder j hj with ⟨hj', hw⟩ | ⟨hge, -, -⟩
      · exact (motiveOf_eq tnames hj' hw (fam.named j hj)).symm
      · omega

/--
info: 'Ix.Cert.RecursorIndex.family_candidate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms family_candidate

/--
info: 'Ix.Cert.RecursorIndex.closure_recursor_index' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closure_recursor_index

end Ix.Cert.RecursorIndex
