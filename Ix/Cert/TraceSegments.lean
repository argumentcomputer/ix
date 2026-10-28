import Ix.Cert.InductiveSegments

/-! # The trace's segments, read one by one

`ClosureLayout.unitsRead_of_layout` reduces the reader's units to `ClosureSegments.SegmentsRead`
for the segments `ClosureLayout` cuts the compile's record order into, one per lowered item of
quotient Source's trace. This module proves `SegmentsRead` index by index
(`segmentsRead_of_each`): the `ℓ`-th segment reads as the `ℓ`-th read from the state the reads
before it leave. At each index the lowered group is empty, a singleton definition, an axiom, a
quotient constant, a block of several definitions or an inductive group (`segmentsRead_of_needs`),
and its segment reads by the segment and placement theorems of its kind (`SingletonSegments`,
`DefinitionSegments`, `InductiveSegments`): `empty_at`, `definition_at`, `axiom_at`,
`quotient_at`, `block_at`, `inductive_at`.

What those theorems need beyond the trace is collected in `TraceNeeds`, per kind for the item's
lowering (`LoweredAt`):
* `DefinitionNeeds`, `HeaderNeeds`, `BlockNeeds`, `InductiveNeeds`: the compile's run of the
  group's block and its publication (`LoneCompiled`, `BlockCompiled`, `InductiveCompiled`),
  quotient Source's facts about the group, and the collapse's form for blocks and inductive
  groups;
* `ConvGood`: the group's quotient terms lie in the scope of representatives;
* `StateGood`: so do the entries of every state the trace's reads are read from.

The names of a group are closure constants (`ClosureLayout.converted_names_stored`), stored
and published under those names; each kind's placement premises (its names, its declared keys)
come from the group itself and its lowering (`ClosureLayout.lowered_declares`).
`unitsRead_of_needs` puts this together with `ClosureLayout.unitsRead_of_layout`. -/

namespace Ix.Cert.TraceSegments

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState
open Ix.Cert.ClosureSegments (SegmentReads SegmentsRead)
open Ix.Cert.ClosureLayout (Steps quotientGraph namesAt groupRecords segmentsOf addrOf qkey)
open Ix.Cert.BlockContext (BoundResolve lone)
open Ix.Cert.DefinitionDeps (ConstOcc)
open Ix.Cert.InductiveCompile (indsOf)
open Ix.Cert.SourcePrelude (Scheduled)
open Ix.LeanIngress (evAddr QRepAt roleAtMap fiberAliasAt ingressKey Group Converted Graph FiberMap)

variable {md md' : Mode}

/-! ## Segments read one by one -/

/-- **The segments of a trace read index by index**: each segment reads as its read from the
state the reads before it leave. -/
theorem segmentsRead_of_each {f : md.Id → md'.Id} {P : KeyScope md} {cx : Ctx md'} {ixe : Ixon.Env} :
    ∀ {start : State md} {rs : List (Read md)} {segs : List (List Address)}, segs.length = rs.length →
      (∀ ℓ r seg, rs[ℓ]? = some r → segs[ℓ]? = some seg →
        SegmentReads f P cx ixe ((rs.take ℓ).foldl State.commit start) r seg) →
      SegmentsRead f P cx ixe start rs segs
  | _, [], [], _, _ => .nil
  | _, [], _ :: _, h, _ => nomatch h
  | _, _ :: _, [], h, _ => nomatch h
  | start, r :: rs, seg :: segs, h, each =>
    .cons (each 0 r seg rfl rfl) (segmentsRead_of_each (by simpa using h) fun ℓ r' seg' hr hs => by
      have := each (ℓ + 1) r' seg' hr hs
      rwa [List.take_succ_cons, List.foldl_cons] at this)

/-! ## The scope and the cut -/

/-- The scope of quotient Source's keys at a compiled artifact: its representatives. -/
abbrev scope (ixe : Ixon.Env) (t : RoleTable) : KeyScope .source := KeyScope.ofId (QRepAt ixe (roleAtMap t))

/-- Quotient Source's renaming to representatives at a compiled artifact. -/
abbrev fibers (ixe : Ixon.Env) (t : RoleTable) : FiberMap := fiberAliasAt ixe (roleAtMap t)

/-- **The segments `ClosureLayout` cuts** the compile's record order `L` into, one per lowered
item of `ls`. -/
abbrev cutOf (ixe : Ixon.Env) (t : RoleTable) (hints : CName .source → Option ReducibilityHint)
    (sub : Ix.Environment) (ls : List Scheduled) (L : List Address) : List (List Address) :=
  segmentsOf L (ls.map fun y => groupRecords ixe (namesAt (quotientGraph ixe t hints sub) y)) []

/-- **A converted group's terms lie in a scope**: its definitions' types and values, its
inductive block, its axiom's or quotient constant's type. -/
def ConvGood (Q : KeyScope .source) : Converted → Prop
  | .definitions ms => ∀ m ∈ ms.toList, m.cv.type.Good Q ∧ m.value.Good Q
  | .inductive rb => rb.Good Q
  | .axiom cv => cv.type.Good Q
  | .quot _ cv => cv.type.Good Q

/-- **A state's entries at keys of a scope lie in the scope**: its owners, constant types and
inductive blocks. -/
structure StateGood (Q : KeyScope .source) (st : State .source) : Prop where
  owners : ∀ k : Key .source, k.Good Q → ∀ o, st.projOwners[k]? = some o → o.Good Q
  types : ∀ k : Key .source, k.Good Q → ∀ p, st.constTypes[k]? = some p → p.2.Good Q
  blocks : ∀ k : Key .source, k.Good Q → ∀ bk, st.indBlocks[k]? = some bk → bk.Good Q

/-- **The trace's `ℓ`-th lowered item** `y` converts its group `gr` to `c`, lowers it from the
state `stS` the reads before it leave to `raw`, and the collapse keeps `rd` of it. -/
structure LoweredAt (g : Graph) (ρ : FiberMap) (hints : CName .source → Option ReducibilityHint)
    (start : State .source) (ls : List Scheduled) (rs : List (Read .source)) (ℓ : Nat) (y : Scheduled)
    (gr : Group) (c : Converted) (stS : State .source) (raw rd : Read .source) : Prop where
  item : ls[ℓ]? = some y
  read : rs[ℓ]? = some rd
  group : g.groups[y.1.1]? = some gr
  converted : Ix.LeanIngress.convert gr = .ok c
  conversion : y.1.2 = .ok ((c.withHints hints).quotient ρ)
  state : stS = (rs.take ℓ).foldl State.commit start
  lowered : Ix.LeanIngress.lower stS ((c.withHints hints).quotient ρ) = .ok raw
  collapsed : ∃ s s' dropped, Ix.LeanIngress.collapseRead s gr.name raw = (s', .ok (rd, dropped))

/-! ## What each kind of group needs -/

section Needs

variable (ixe : Ixon.Env) (sub : Ix.Environment)

/-- **The blobs a compile read are the artifact's.** -/
def BlobsKept (cenv : CompileEnv) (after : BlockState) : Prop :=
  ∀ a bytes, BlobWrites.readBlob cenv.blobs after a = some bytes → ixe.blobs.get? a = some bytes

/-- **Every name the sources mention that the compile binds is a closure constant published at
its binding.** -/
def MentionsPublished (cenv : CompileEnv) (mentions : Ix.Name → Prop) : Prop :=
  ∀ m a, mentions m → lookupBinding cenv {} m = some a →
    ∃ named', (m, named') ∈ ixe.named.toList ∧ named'.addr = a ∧ (sub.consts.get? m).isSome = true

/-- **A block the fold claimed**: `runBlock` built it, the artifact publishes it, and its records
are `output`'s. -/
def Claimed (output : BlockResult) : Prop :=
  ∃ (cenvR : CompileEnv) (all : Ix.Set Ix.Name) (key : Ix.Name) (r : BlockResult) (cache : BlockState),
    runBlock cenvR all key = .ok (r, cache) ∧ BlockPublication.Published ixe sub key r ∧
      BlockRecords.recordsOf r = BlockRecords.recordsOf output

/-- **A constant compiled alone**: its run at the fold's snapshot, its record stored and
published under its name, the snapshot's bindings resolving, its blobs kept and the names its
sources mention published. -/
structure LoneCompiled (ci : Ix.ConstantInfo) (mentions : Ix.Name → Prop) (cenv : CompileEnv) (benv : BlockEnv)
    (output : BlockResult) (after : BlockState) : Prop where
  ran : rawRun (compileConstantInfo ci) (cenv, benv) {} = (.ok output, after)
  stored : recordAt ixe output.blockAddr = some output.block
  addr : addrOf ixe ci.getCnst.name = some output.blockAddr
  bound : BoundResolve ixe cenv
  blobs : BlobsKept ixe cenv after
  published : MentionsPublished ixe sub cenv mentions

/-- The names a definition's type and value mention. -/
def defMentions (ci : Ix.ConstantInfo) (m : Ix.Name) : Prop :=
  ∃ source, EmissionDispatch.sourceData ci = some source ∧
    (GraphWalk.Refs m source.type ∨ GraphWalk.Refs m source.value)

/-- **What a singleton definition's segment needs**: its compile, with its record's hint the one
quotient Source lowers it at. (Its level parameters are distinct where the collapse keeps it:
`TraceNeeds.levels`.) -/
structure DefinitionNeeds (hints : CName .source → Option ReducibilityHint) (ci : Ix.ConstantInfo) : Prop where
  compiled : ∃ cenv benv output after, LoneCompiled ixe sub ci (defMentions ci) cenv benv output after ∧
    ∃ h, hintsOf ixe (.member output.blockAddr 0) = some h ∧ hints (ingressKey ci.getCnst.name) = some h

/-- **What an axiom's or a quotient constant's segment needs**: its compile, and, where the
collapse keeps its declaration `raw` as the read `rd`, distinct level parameters and a type that
does not name the constant itself. -/
structure HeaderNeeds (ci : Ix.ConstantInfo) (raw rd : Read .source) : Prop where
  compiled : ∃ cenv benv output after,
    LoneCompiled ixe sub ci (fun m => GraphWalk.Refs m ci.getCnst.type) cenv benv output after
  nodup : rd = raw → ci.getCnst.levelParams.toList.Nodup
  noSelf : rd = raw → ConstsSatisfy (fun m => m ≠ ci.getCnst.name) ci.getCnst.type

/-- A group of definitions' sources, in the group's order. -/
def defsOf (members : Array Ix.ConstantInfo) : List Ix.Def :=
  members.toList.filterMap EmissionDispatch.sourceData

/-- **A block of several definitions compiled in Lean's order**: the run at the fold's snapshot,
with its members unbound there, the fold's claim of the block, the snapshot's bindings
resolving, its blobs kept, the names its sources mention published, and each member's hint in
the closure's context the one quotient Source lowers it at. -/
structure BlockCompiled (t : RoleTable) (preA : Prelude .anon) (order : List Address)
    (hints : CName .source → Option ReducibilityHint) (defs : List Ix.Def) (cenv : CompileEnv) (benv : BlockEnv)
    (output : BlockResult) (after : BlockState) : Prop where
  ran : rawRun (compileMutualBlock ((defs.map MutConst.defn).map ([·]))) (cenv, benv) {} = (.ok output, after)
  fresh : ∀ d ∈ defs, cenv.nameToAddr.get? d.name = none
  claimed : Claimed ixe sub output
  bound : BoundResolve ixe cenv
  blobs : BlobsKept ixe cenv after
  published : MentionsPublished ixe sub cenv fun m =>
    ∃ (j : Nat) (_ : j < defs.length), GraphWalk.Refs m defs[j].type ∨ GraphWalk.Refs m defs[j].value
  hinted : ∃ H : Nat → ReducibilityHint, ∀ k (hk : k < defs.length),
    (closureContext ixe t preA order).hint (.member output.blockAddr k) = some (H k) ∧
      hints (ingressKey defs[k].name) = some (H k)

/-- **What a block of several definitions' segment needs**: its compile; distinct members; every
name its sources mention with a member's key is that member; and the collapse keeping or dropping
it whole. (Its declarations' level parameters are distinct where the collapse keeps them:
`TraceNeeds.levels`.) -/
structure BlockNeeds (t : RoleTable) (preA : Prelude .anon) (order : List Address)
    (hints : CName .source → Option ReducibilityHint) (members : Array Ix.ConstantInfo) (raw rd : Read .source) :
    Prop where
  compiled : ∃ cenv benv output after, BlockCompiled ixe sub t preA order hints (defsOf members) cenv benv output after
  distinct : Canon.KeysDistinct ((defsOf members).map MutConst.defn)
  exactNames : ∀ i (hi : i < (defsOf members).length) j (hj : j < (defsOf members).length) n,
    ConstOcc n (defsOf members)[i].type ∨ ConstOcc n (defsOf members)[i].value →
      ingressKey n = ingressKey (defsOf members)[j].name → n = (defsOf members)[j].name
  collapse : rd = raw ∨ rd = { raw with decls := #[], generated := 0 }

/-- **An inductive group compiled in Lean's order**: the inductive block's run, the fold's claim,
bindings, blobs and mentioned names; the recursor family's (a block of several, or a lone
recursor compiled alone under its own name); and the closure's recursor index at the block. -/
structure InductiveCompiled (t : RoleTable) (preA : Prelude .anon) (order : List Address) (b : Ix.RoleEvidence.Bundle)
    (types : Array Ix.InductiveVal) (ctors : Array (Array Ix.ConstructorVal)) (recs : Array Ix.RecursorVal)
    (first : Ix.InductiveVal) (hcsize : ctors.size = types.size)
    (cenv₁ : CompileEnv) (benv₁ : BlockEnv) (out₁ : BlockResult) (after₁ : BlockState)
    (cenv₂ : CompileEnv) (benv₂ : BlockEnv) (out₂ : BlockResult) (after₂ : BlockState) : Prop where
  ran₁ : rawRun (compileMutualBlock (((indsOf types ctors).map MutConst.indc).map ([·]))) (cenv₁, benv₁) {} =
    (.ok out₁, after₁)
  claimed₁ : Claimed ixe sub out₁
  bound₁ : BoundResolve ixe cenv₁
  blobs₁ : BlobsKept ixe cenv₁ after₁
  published₁ : MentionsPublished ixe sub cenv₁ fun m =>
    ∃ i ∈ indsOf types ctors, ∃ e ∈ BlockEmission.memberSources (.indc i), GraphWalk.Refs m e
  family : ∃ (cenvR₂ : CompileEnv) (all₂ : Ix.Set Ix.Name) (key₂ : Ix.Name) (r₂ : BlockResult) (cache₂ : BlockState),
    runBlock cenvR₂ all₂ key₂ = .ok (r₂, cache₂) ∧ BlockPublication.Published ixe sub key₂ r₂ ∧
      BlockRecords.recordsOf r₂ = BlockRecords.recordsOf out₂ ∧
      (rawRun (compileMutualBlock ((recs.toList.map MutConst.recr).map ([·]))) (cenv₂, benv₂) {} =
          (.ok out₂, after₂) ∨
        ∃ r, recs.toList = [r] ∧ key₂ = r.cnst.name ∧
          rawRun (compileConstantInfo (.recInfo r)) (cenv₂, benv₂) {} = (.ok out₂, after₂))
  bound₂ : BoundResolve ixe cenv₂
  blobs₂ : BlobsKept ixe cenv₂ after₂
  published₂ : MentionsPublished ixe sub cenv₂ fun m =>
    ∃ r ∈ recs.toList, ∃ e ∈ BlockEmission.memberSources (.recr r), GraphWalk.Refs m e
  index : ∃ shape : BlockShape, (closureContext ixe t preA order).index.blocks[out₁.blockAddr]? = some shape ∧
    shape.order = (List.range types.size).toArray ∧
    shape.recs.toList = (List.range recs.size).map fun j => ConstRef.member out₂.blockAddr j
  entries : ∀ j (hj : j < recs.size), ∃ (entry : RecEntry) (mb : Address) (mi : Nat) (major : Ixon.Inductive),
    (closureContext ixe t preA order).index.recs[ConstRef.member out₂.blockAddr j]? = some entry ∧
    recLps entry.large (List.range first.cnst.levelParams.size) = (SourceConversion.recNum first recs[j]).params ∧
    entry.major = .member mb mi ∧ inductiveAt (closureContext ixe t preA order).store entry.major = some major ∧
    major.ctors.size = recs[j].rules.size ∧
    (∀ k (hk : k < recs[j].rules.size),
      (closureContext ixe t preA order).memberKey (.ctor mb mi k) =
        .ok (InductiveUnits.srcKey (fiberAliasAt ixe (roleAtMap t)) (evAddr ixe b) recs[j].rules[k].ctor)) ∧
    (CtxAgree.numNestedOf (InductiveUnits.srcBlock types ctors recs first) = 0 →
      some entry.motive = SourceConversion.motiveOf types recs[j])

/-- **What an inductive group's segment needs** (its first type `first`): its compile, the
group's shape (one constructor list per type, shared level parameters, constructor positions,
recursors sharing distinct level parameters, distinct members, constructors named by no type),
and the collapse keeping it whole. -/
structure InductiveNeeds (t : RoleTable) (preA : Prelude .anon) (order : List Address) (b : Ix.RoleEvidence.Bundle)
    (types : Array Ix.InductiveVal) (ctors : Array (Array Ix.ConstructorVal)) (recs : Array Ix.RecursorVal)
    (first : Ix.InductiveVal) (raw rd : Read .source) : Prop where
  hcsize : ctors.size = types.size
  compiled : ∃ cenv₁ benv₁ out₁ after₁ cenv₂ benv₂ out₂ after₂,
    InductiveCompiled ixe sub t preA order b types ctors recs first hcsize cenv₁ benv₁ out₁ after₁
      cenv₂ benv₂ out₂ after₂
  lpsEq : ∀ v ∈ types.toList, v.cnst.levelParams = first.cnst.levelParams
  ctorLps : ∀ cs ∈ ctors.toList, ∀ c ∈ cs.toList, c.cnst.levelParams = first.cnst.levelParams
  nodup : first.cnst.levelParams.toList.Nodup
  positions : ∀ i (hi : i < ctors.size) j (hj : j < ctors[i].size), ctors[i][j].cidx = j
  recLevels : ∃ rlps : Array Ix.Name, (∀ r ∈ recs.toList, r.cnst.levelParams = rlps) ∧ rlps.toList.Nodup
  hrne : recs.toList ≠ []
  distinct : Canon.KeysDistinct ((indsOf types ctors).map MutConst.indc)
  noCtor : ∀ i ∈ indsOf types ctors, ∀ e ∈ BlockEmission.memberSources (.indc i),
    ConstsSatisfy (fun n => ∀ i' ∈ indsOf types ctors, ∀ c ∈ i'.ctors.toList, n ≠ c.cnst.name) e
  recDistinct : Canon.KeysDistinct (recs.toList.map MutConst.recr)
  kept : rd = raw

end Needs

/-! ## Groups and their names -/

theorem contains_of_mem {env : Ix.Environment} {n : Ix.Name} {ci : Ix.ConstantInfo}
    (h : (n, ci) ∈ env.consts.toList) : env.consts.contains n = true := by
  rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, SourceStoredNames.stored_get h]
  rfl

theorem mem_map_name {α : Type} {xs : Array α} {f : α → Ix.Name} {n : Ix.Name} :
    n ∈ xs.map f ↔ ∃ (i : Nat) (_ : i < xs.size), f xs[i] = n := by
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := Array.mem_map.mp h
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact Array.mem_map.mpr ⟨_, Array.getElem_mem hi, rfl⟩

/-- An inductive group's names: its types', constructors' and recursors'. -/
theorem inductive_names (types : Array Ix.InductiveVal) (ctors : Array (Array Ix.ConstructorVal))
    (recs : Array Ix.RecursorVal) (n : Ix.Name) :
    n ∈ (Group.inductive types ctors recs).names ↔
      (∃ (i : Nat) (_ : i < types.size), types[i].cnst.name = n) ∨
      (∃ (i : Nat) (hi : i < ctors.size) (k : Nat) (_ : k < ctors[i].size), ctors[i][k].cnst.name = n) ∨
      ∃ (j : Nat) (_ : j < recs.size), recs[j].cnst.name = n := by
  have hC : n ∈ ctors.flatMap (·.map (·.cnst.name)) ↔
      ∃ (i : Nat) (hi : i < ctors.size) (k : Nat) (_ : k < ctors[i].size), ctors[i][k].cnst.name = n := by
    rw [Array.mem_flatMap]
    constructor
    · rintro ⟨cs, hcs, hn⟩
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hcs
      obtain ⟨k, hk, e⟩ := mem_map_name.mp hn
      exact ⟨i, hi, k, hk, e⟩
    · rintro ⟨i, hi, k, hk, e⟩
      exact ⟨ctors[i], Array.getElem_mem hi, mem_map_name.mpr ⟨k, hk, e⟩⟩
  simp only [Group.names, Array.mem_append]
  rw [mem_map_name, hC, mem_map_name, or_assoc]

/-- A group of definitions' names: its members'. -/
theorem definitions_names (members : Array Ix.ConstantInfo) (n : Ix.Name) :
    n ∈ (Group.definitions members).names ↔ ∃ (i : Nat) (_ : i < members.size), members[i].getCnst.name = n := by
  simp only [Group.names]
  exact mem_map_name

theorem forall₂_filterMap {α β : Type} (f : α → Option β) :
    ∀ (l : List α), (∀ x ∈ l, (f x).isSome = true) → List.Forall₂ (fun a b => f a = some b) l (l.filterMap f)
  | [], _ => .nil
  | x :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h x List.mem_cons_self)
    rw [List.filterMap_cons, hb]
    exact .cons hb (forall₂_filterMap f l fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- **A group of definitions that converts has its members' sources, in its order.** -/
theorem views_of_convert {members : Array Ix.ConstantInfo} {c : Converted}
    (h : Ix.LeanIngress.convertDefinitions members = .ok c) (two : 2 ≤ members.size) :
    List.Forall₂ (fun ci d => EmissionDispatch.sourceData ci = some d) members.toList (defsOf members) := by
  obtain ⟨ms, ord, -, hms, -⟩ := DefinitionBlockReads.convertDefinitions_block h two
  refine forall₂_filterMap _ _ fun ci hci => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hci
  obtain ⟨s, -, -, -, hs, -⟩ := hms k (by simpa using hk)
  simp only [Array.getElem_toList] at hs ⊢
  cases hm : members[k] <;> simp_all [Ix.LeanIngress.definitionShape, EmissionDispatch.sourceData]

/-! ## Reads that change nothing -/

/-- A read of no declaration collapses to itself with nothing generated. -/
theorem collapseRead_nil {s s' : Ix.LeanIngress.CollapseState} {first : CName .source} {raw r : Read .source}
    {dropped : Array (CName .source)} (h : Ix.LeanIngress.collapseRead s first raw = (s', .ok (r, dropped)))
    (hd : raw.decls = #[]) : r = { raw with decls := #[], generated := 0 } := by
  rw [SourcePrelude.collapseRead_eq] at h
  unfold SourcePrelude.readLoop at h
  rw [hd] at h
  have hz : (#[] : Array (CDecl .source)).zipIdx = #[] := rfl
  rw [hz, ← Array.forIn_toList] at h
  simp [SourcePrelude.readFinish, SingletonSegments.id_pure] at h
  obtain ⟨-, rfl, -⟩ := h
  rfl

/-- **An empty group of definitions has an empty segment, read as nothing.** -/
theorem empty_at {ixe : Ixon.Env} {cx : Ctx .anon} {f : Mode.Id .source → Mode.Id .anon} {P : KeyScope .source}
    {g : Graph} {ρ : FiberMap} {hints : CName .source → Option ReducibilityHint} {start : State .source}
    {ls : List Scheduled} {rs : List (Read .source)} {ℓ : Nat} {y : Scheduled} {c : Converted}
    {stS : State .source} {raw rd : Read .source}
    (low : LoweredAt g ρ hints start ls rs ℓ y (.definitions #[]) c stS raw rd)
    {seg : List Address} (empty : rd.decls = #[] → seg = []) : SegmentReads f P cx ixe stS rd seg := by
  obtain ⟨-, -, -, hconv, -, -, hl, s, s', dropped, hcol⟩ := low
  have hc : c = .definitions #[] := by
    have : Ix.LeanIngress.convertDefinitions #[] = .ok (.definitions #[]) := by
      simp [Ix.LeanIngress.convertDefinitions, Ix.LeanIngress.exprsOf]
      rfl
    exact (Except.ok.inj ((this.symm.trans hconv))).symm
  subst hc
  have hq : ((Converted.definitions #[]).withHints hints).quotient ρ = .definitions #[] := by
    simp [Converted.withHints, Converted.quotient, Converted.substKeys, Converted.canon]
  have hl' : Ix.LeanIngress.lower stS (.definitions #[]) = .ok raw := by rw [← hq]; exact hl
  obtain ⟨ds, hds, plain, hF⟩ := DefinitionBlockReads.lower_defs hl'
  cases hF
  have hraw : raw.decls = #[] := hds
  obtain rfl := collapseRead_nil hcol hraw
  rw [empty rfl]
  exact .inl ⟨⟨⟨rfl, plain.owners, plain.blocks⟩, rfl⟩, fun _ h => nomatch h⟩

/-- **A read the collapse drops whole has an empty segment, read as nothing.** -/
theorem dropped_reads {f : md.Id → md'.Id} {P : KeyScope md} {cx : Ctx md'} {ixe : Ixon.Env} {stS : State md}
    {raw rd : Read md} {seg : List Address} (plain : StreamRename.Plain raw)
    (h : rd = { raw with decls := #[], generated := 0 }) (empty : rd.decls = #[] → seg = []) :
    SegmentReads f P cx ixe stS rd seg := by
  subst h
  rw [empty rfl]
  exact .inl ⟨⟨⟨rfl, plain.owners, plain.blocks⟩, rfl⟩, fun _ h => nomatch h⟩

/-! ## A segment of each kind -/

section Kinds

variable {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env}
  {failures : Failures} {t : RoleTable} {envQ : Env .source}

/-- **A singleton definition's segment reads as its read.** -/
theorem definition_at (P : Premises env roots sub ixe failures t envQ) {preA : Prelude .anon}
    (prelude : preludeFor t = .ok preA) {b : Ix.RoleEvidence.Bundle}
    (hf : InjOn (evAddr ixe b) (QRepAt ixe (roleAtMap t)))
    (resolves : SingletonSegments.PublishedResolve ixe sub) {hints : CName .source → Option ReducibilityHint}
    {start : State .source} {ls : List Scheduled} {rs : List (Read .source)} {L : List Address}
    (steps : Steps (quotientGraph ixe t hints sub) start ls rs)
    (inTrace : ∀ y ∈ ls, y ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList)
    (hnd : L.Nodup) (hmem : ∀ a, a ∈ L ↔ ixe.consts.contains a = true)
    (corder : ClosureOrder ixe (Seed ixe sub) (cutOf ixe t hints sub ls L).flatten)
    (canonical : Stream.StoredCanonical ixe (cutOf ixe t hints sub ls L).flatten)
    {ℓ : Nat} {y : Scheduled} {ci : Ix.ConstantInfo} {c : Converted} {stS : State .source} {raw rd : Read .source}
    (low : LoweredAt (quotientGraph ixe t hints sub) (fibers ixe t) hints start ls rs ℓ y (.definitions #[ci]) c
      stS raw rd)
    (needs : DefinitionNeeds ixe sub hints ci) (stGood : StateGood (scope ixe t) stS)
    (good : ConvGood (scope ixe t) ((c.withHints hints).quotient (fibers ixe t)))
    (levels : rd = raw → ∀ d ∈ raw.decls.toList, DefinitionBlockReads.DeclNodup d)
    {seg : List Address} (hseg : (cutOf ixe t hints sub ls L)[ℓ]? = some seg) (empty : rd.decls = #[] → seg = []) :
    SegmentReads (evAddr ixe b) (scope ixe t) (closureContext ixe t preA (cutOf ixe t hints sub ls L).flatten) ixe
      stS rd seg := by
  obtain ⟨hy, hr, hgr, hconv, hc, -, hl, s, s', dropped, hcol⟩ := low
  have hyx := inTrace y (List.mem_of_getElem? hy)
  have hnm : namesAt (quotientGraph ixe t hints sub) y = #[ci.getCnst.name] := by
    unfold namesAt
    rw [ClosureLayout.getElem!_of_getElem? hgr]
    simp [Group.names]
  -- the key quotient Source declares for the definition
  have declares := ClosureLayout.lowered_declares hyx hc hl ci.getCnst.name (by rw [hnm]; simp)
  obtain ⟨cenv, benv, output, after, ⟨ran, stored, haddr, bound, blobs, published⟩, h, hint, hhint⟩ :=
    needs.compiled
  obtain ⟨m0, rfl, hm0, hm0l⟩ : ∃ m0 : Ix.LeanIngress.DefMember, c = .definitions #[m0] ∧
      m0.cv.name = ingressKey ci.getCnst.name ∧
      m0.cv.levelParams = (Ix.LeanIngress.Numbering.mk ci.getCnst.levelParams false).params := by
    obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := RecordReadings.convertDefinitions_single hconv
    exact ⟨_, rfl, rfl, rfl⟩
  have hconv' : Ix.LeanIngress.convertDefinitions #[ci] = .ok (.definitions #[m0]) := hconv
  obtain ⟨source, view⟩ : ∃ source, EmissionDispatch.sourceData ci = some source := by
    obtain ⟨s0, -, -, -, hs0, -⟩ := RecordReadings.convertDefinitions_single hconv'
    cases ci <;> simp_all [Ix.LeanIngress.definitionShape, EmissionDispatch.sourceData]
  obtain ⟨hname, hlps, -⟩ := RecordReadings.sourceData_facts view
  -- quotient Source's read at the record's hint
  have hq : ((Converted.definitions #[m0]).withHints hints).quotient (fibers ixe t) =
      .definitions #[RecordReadings.quotientMember (fibers ixe t) m0 h] := by
    simp only [Converted.withHints, Converted.quotient, Converted.substKeys, Converted.canon,
      List.map_toArray, List.map_cons, List.map_nil, hm0, hhint, RecordReadings.quotientMember]
  rw [hq] at hl good
  obtain ⟨typeGood, valueGood⟩ := good _ List.mem_cons_self
  -- a dropped definition reads to nothing
  obtain ⟨decl, rw', lowS, hraw⟩ := RecordReadings.lower_definition hl
  have plain : StreamRename.Plain raw := by subst hraw; exact ⟨rfl, rfl, rfl⟩
  rcases SingletonSegments.collapseRead_one hcol (by rw [hraw]) plain.generated with e | e
  rotate_left
  · exact dropped_reads plain e empty
  -- a kept one has distinct level parameters
  have nodup : source.levelParams.toList.Nodup := by
    have hd := levels e decl (by rw [hraw]; simp)
    have hn := DefinitionBlockReads.lowerDefinition_nodup lowS hd
    rw [DefinitionBlockReads.quotientMember_levelParams, hm0l] at hn
    rw [← hlps]
    exact DefinitionBlockReads.nodup_of_params hn
  -- the definition is a closure constant published at its record
  obtain ⟨ci', hci'⟩ := ClosureLayout.converted_names_stored P hgr hconv ci.getCnst.name (by
    simp [Group.names])
  obtain ⟨named, hmemN, hget⟩ := SourceStoredNames.stored_published P hci'
  have haddr' : named.addr = output.blockAddr := by
    unfold ClosureLayout.addrOf at haddr
    rw [hget] at haddr
    exact Option.some.inj haddr
  have input : env.consts.contains source.name = true := by
    rw [← hname]
    exact contains_of_mem (SourceStoredNames.stored_input P hci')
  have hB := InductiveSegments.published_in_order P corder hci' haddr stored
  have hn : (source.name, named) ∈ ixe.named.toList := hname ▸ hmemN
  refine SingletonSegments.definition_segment P prelude corder canonical hf view input nodup ran hB
    stored hn haddr' bound blobs (fun m a hm => published m a ⟨source, view, hm⟩) hint hconv' stGood.owners
    typeGood valueGood hl hcol (fun _ => ?_) empty
  -- a kept definition's segment is its record
  have shape := BlockLayout.compileConstantInfo_shape ci _ _ _ _ ran
  obtain ⟨-, -, single⟩ := SingletonReads.lone_keys P prelude corder canonical b
    (blob := fun a => cenv.blobs.get? a) shape hB stored hn haddr' input
  have place := SingletonSegments.singleton_place P steps inTrace hnd hmem resolves hy hr hnm haddr stored single
    (by subst e; exact declares)
  exact Option.some.inj (hseg.symm.trans place)

/-- **An axiom's segment reads as its read.** -/
theorem axiom_at (P : Premises env roots sub ixe failures t envQ) {preA : Prelude .anon}
    (prelude : preludeFor t = .ok preA) {b : Ix.RoleEvidence.Bundle}
    (resolves : SingletonSegments.PublishedResolve ixe sub) {hints : CName .source → Option ReducibilityHint}
    {start : State .source} {ls : List Scheduled} {rs : List (Read .source)} {L : List Address}
    (steps : Steps (quotientGraph ixe t hints sub) start ls rs)
    (inTrace : ∀ y ∈ ls, y ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList)
    (hnd : L.Nodup) (hmem : ∀ a, a ∈ L ↔ ixe.consts.contains a = true)
    (corder : ClosureOrder ixe (Seed ixe sub) (cutOf ixe t hints sub ls L).flatten)
    (canonical : Stream.StoredCanonical ixe (cutOf ixe t hints sub ls L).flatten)
    {ℓ : Nat} {y : Scheduled} {v : Ix.AxiomVal} {c : Converted} {stS : State .source} {raw rd : Read .source}
    (low : LoweredAt (quotientGraph ixe t hints sub) (fibers ixe t) hints start ls rs ℓ y (.axiom v) c stS raw rd)
    (needs : HeaderNeeds ixe sub (.axiomInfo v) raw rd)
    {seg : List Address} (hseg : (cutOf ixe t hints sub ls L)[ℓ]? = some seg) (empty : rd.decls = #[] → seg = []) :
    SegmentReads (evAddr ixe b) (scope ixe t) (closureContext ixe t preA (cutOf ixe t hints sub ls L).flatten) ixe
      stS rd seg := by
  obtain ⟨hy, hr, hgr, hconv, hc, -, hl, s, s', dropped, hcol⟩ := low
  have hyx := inTrace y (List.mem_of_getElem? hy)
  have hnm : namesAt (quotientGraph ixe t hints sub) y = #[v.cnst.name] := by
    unfold namesAt
    rw [ClosureLayout.getElem!_of_getElem? hgr]
    rfl
  have declares := ClosureLayout.lowered_declares hyx hc hl v.cnst.name (by rw [hnm]; simp)
  obtain ⟨cenv, benv, output, after, ran, stored, haddr, bound, blobs, published⟩ := needs.compiled
  have haddr : addrOf ixe v.cnst.name = some output.blockAddr := haddr
  obtain ⟨cv0, rfl⟩ : ∃ cv0, c = .axiom cv0 := by
    obtain ⟨_, -, -, rfl⟩ := RecordReadings.convert_axiom hconv
    exact ⟨_, rfl⟩
  -- a dropped axiom reads to nothing
  have hraw : raw = { decls := #[.axiomDecl (RecordReadings.quotientHeader (fibers ixe t) cv0)] } := by
    have unfolded : Ix.LeanIngress.lower stS (((Converted.axiom cv0).withHints hints).quotient (fibers ixe t)) =
        .ok { decls := #[.axiomDecl (RecordReadings.quotientHeader (fibers ixe t) cv0)] } := rfl
    exact (Except.ok.inj (unfolded.symm.trans hl)).symm
  have plain : StreamRename.Plain raw := by subst hraw; exact ⟨rfl, rfl, rfl⟩
  rcases SingletonSegments.collapseRead_one hcol (by rw [hraw]) plain.generated with e | e
  rotate_left
  · exact dropped_reads plain e empty
  obtain ⟨ci', hci'⟩ := ClosureLayout.converted_names_stored P hgr hconv v.cnst.name (by
    simp [Group.names])
  obtain ⟨named, hn, hget⟩ := SourceStoredNames.stored_published P hci'
  have haddr' : named.addr = output.blockAddr := by
    unfold ClosureLayout.addrOf at haddr
    rw [hget] at haddr
    exact Option.some.inj haddr
  have input : env.consts.contains v.cnst.name = true := contains_of_mem (SourceStoredNames.stored_input P hci')
  have hB := InductiveSegments.published_in_order P corder hci' haddr stored
  refine SingletonSegments.axiom_segment (b := b) P prelude corder canonical input (needs.nodup e) ran hB stored hn
    haddr' bound blobs published (needs.noSelf e) hconv hl hcol (fun _ => ?_) empty
  have shape := BlockLayout.compileConstantInfo_shape _ _ _ _ _ ran
  obtain ⟨-, -, single⟩ := SingletonReads.lone_keys P prelude corder canonical b
    (blob := fun a => cenv.blobs.get? a) shape hB stored hn haddr' input
  have place := SingletonSegments.singleton_place P steps inTrace hnd hmem resolves hy hr hnm haddr stored single
    (by subst e; exact declares)
  exact Option.some.inj (hseg.symm.trans place)

/-- **A quotient constant's segment reads as its read.** -/
theorem quotient_at (P : Premises env roots sub ixe failures t envQ) {preA : Prelude .anon}
    (prelude : preludeFor t = .ok preA) {b : Ix.RoleEvidence.Bundle}
    (resolves : SingletonSegments.PublishedResolve ixe sub) {hints : CName .source → Option ReducibilityHint}
    {start : State .source} {ls : List Scheduled} {rs : List (Read .source)} {L : List Address}
    (steps : Steps (quotientGraph ixe t hints sub) start ls rs)
    (inTrace : ∀ y ∈ ls, y ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList)
    (hnd : L.Nodup) (hmem : ∀ a, a ∈ L ↔ ixe.consts.contains a = true)
    (corder : ClosureOrder ixe (Seed ixe sub) (cutOf ixe t hints sub ls L).flatten)
    (canonical : Stream.StoredCanonical ixe (cutOf ixe t hints sub ls L).flatten)
    {ℓ : Nat} {y : Scheduled} {v : Ix.QuotVal} {c : Converted} {stS : State .source} {raw rd : Read .source}
    (low : LoweredAt (quotientGraph ixe t hints sub) (fibers ixe t) hints start ls rs ℓ y (.quot v) c stS raw rd)
    (needs : HeaderNeeds ixe sub (.quotInfo v) raw rd)
    {seg : List Address} (hseg : (cutOf ixe t hints sub ls L)[ℓ]? = some seg) (empty : rd.decls = #[] → seg = []) :
    SegmentReads (evAddr ixe b) (scope ixe t) (closureContext ixe t preA (cutOf ixe t hints sub ls L).flatten) ixe
      stS rd seg := by
  obtain ⟨hy, hr, hgr, hconv, hc, -, hl, s, s', dropped, hcol⟩ := low
  have hyx := inTrace y (List.mem_of_getElem? hy)
  have hnm : namesAt (quotientGraph ixe t hints sub) y = #[v.cnst.name] := by
    unfold namesAt
    rw [ClosureLayout.getElem!_of_getElem? hgr]
    rfl
  have declares := ClosureLayout.lowered_declares hyx hc hl v.cnst.name (by rw [hnm]; simp)
  obtain ⟨cenv, benv, output, after, ran, stored, haddr, bound, blobs, published⟩ := needs.compiled
  have haddr : addrOf ixe v.cnst.name = some output.blockAddr := haddr
  obtain ⟨kind, cv0, rfl⟩ : ∃ kind cv0, c = .quot kind cv0 := by
    obtain ⟨_, -, rfl⟩ := RecordReadings.convert_quot hconv
    exact ⟨_, _, rfl⟩
  -- a dropped quotient constant reads to nothing
  have hraw : raw = { decls := #[.quotDecl kind (RecordReadings.quotientHeader (fibers ixe t) cv0)] } := by
    have unfolded : Ix.LeanIngress.lower stS (((Converted.quot kind cv0).withHints hints).quotient (fibers ixe t)) =
        .ok { decls := #[.quotDecl kind (RecordReadings.quotientHeader (fibers ixe t) cv0)] } := rfl
    exact (Except.ok.inj (unfolded.symm.trans hl)).symm
  have plain : StreamRename.Plain raw := by subst hraw; exact ⟨rfl, rfl, rfl⟩
  rcases SingletonSegments.collapseRead_one hcol (by rw [hraw]) plain.generated with e | e
  rotate_left
  · exact dropped_reads plain e empty
  obtain ⟨ci', hci'⟩ := ClosureLayout.converted_names_stored P hgr hconv v.cnst.name (by
    simp [Group.names])
  obtain ⟨named, hn, hget⟩ := SourceStoredNames.stored_published P hci'
  have haddr' : named.addr = output.blockAddr := by
    unfold ClosureLayout.addrOf at haddr
    rw [hget] at haddr
    exact Option.some.inj haddr
  have input : env.consts.contains v.cnst.name = true := contains_of_mem (SourceStoredNames.stored_input P hci')
  have hB := InductiveSegments.published_in_order P corder hci' haddr stored
  refine SingletonSegments.quotient_segment (b := b) P prelude corder canonical input (needs.nodup e) ran hB stored hn
    haddr' bound blobs published (needs.noSelf e) hconv hl hcol (fun _ => ?_) empty
  have shape := BlockLayout.compileConstantInfo_shape _ _ _ _ _ ran
  obtain ⟨-, -, single⟩ := SingletonReads.lone_keys P prelude corder canonical b
    (blob := fun a => cenv.blobs.get? a) shape hB stored hn haddr' input
  have place := SingletonSegments.singleton_place P steps inTrace hnd hmem resolves hy hr hnm haddr stored single
    (by subst e; exact declares)
  exact Option.some.inj (hseg.symm.trans place)

/-- **A block of several definitions' segment reads as its read.** -/
theorem block_at (P : Premises env roots sub ixe failures t envQ) {preA : Prelude .anon}
    (prelude : preludeFor t = .ok preA) {b : Ix.RoleEvidence.Bundle}
    (hf : InjOn (evAddr ixe b) (QRepAt ixe (roleAtMap t)))
    (resolves : SingletonSegments.PublishedResolve ixe sub) {hints : CName .source → Option ReducibilityHint}
    {start : State .source} {ls : List Scheduled} {rs : List (Read .source)} {L : List Address}
    (steps : Steps (quotientGraph ixe t hints sub) start ls rs)
    (inTrace : ∀ y ∈ ls, y ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList)
    (hnd : L.Nodup) (hmem : ∀ a, a ∈ L ↔ ixe.consts.contains a = true)
    (corder : ClosureOrder ixe (Seed ixe sub) (cutOf ixe t hints sub ls L).flatten)
    (canonical : Stream.StoredCanonical ixe (cutOf ixe t hints sub ls L).flatten)
    {ℓ : Nat} {y : Scheduled} {members : Array Ix.ConstantInfo} {c : Converted} {stS : State .source}
    {raw rd : Read .source}
    (low : LoweredAt (quotientGraph ixe t hints sub) (fibers ixe t) hints start ls rs ℓ y (.definitions members) c
      stS raw rd)
    (two : 2 ≤ members.size)
    (needs : BlockNeeds ixe sub t preA (cutOf ixe t hints sub ls L).flatten hints members raw rd)
    (stGood : StateGood (scope ixe t) stS) (good : ConvGood (scope ixe t) ((c.withHints hints).quotient (fibers ixe t)))
    (levels : rd = raw → ∀ d ∈ raw.decls.toList, DefinitionBlockReads.DeclNodup d)
    {seg : List Address} (hseg : (cutOf ixe t hints sub ls L)[ℓ]? = some seg) (empty : rd.decls = #[] → seg = []) :
    SegmentReads (evAddr ixe b) (scope ixe t) (closureContext ixe t preA (cutOf ixe t hints sub ls L).flatten) ixe
      stS rd seg := by
  obtain ⟨hy, hr, hgr, hconv, hc, -, hl, -⟩ := low
  have hyx := inTrace y (List.mem_of_getElem? hy)
  have hconv' : Ix.LeanIngress.convertDefinitions members = .ok c := hconv
  have views := views_of_convert hconv' two
  have hlen : members.size = (defsOf members).length := by simpa using DefinitionBlocks.forall₂_length views
  -- each member's source is named as the member
  have nameAt : ∀ j (hj : j < (defsOf members).length), members[j].getCnst.name = (defsOf members)[j].name := by
    intro j hj
    have hv := DefinitionBlocks.forall₂_getElem views j (by simp; omega) hj
    simp only [Array.getElem_toList] at hv
    exact (RecordReadings.sourceData_facts hv).1
  have hnm : namesAt (quotientGraph ixe t hints sub) y = (Group.definitions members).names := by
    unfold namesAt
    rw [ClosureLayout.getElem!_of_getElem? hgr]
  have hnames : ∀ n, n ∈ namesAt (quotientGraph ixe t hints sub) y ↔
      ∃ (j : Nat) (_ : j < (defsOf members).length), (defsOf members)[j].name = n := by
    intro n
    rw [hnm, definitions_names]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, by omega, (nameAt j (by omega)).symm⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, by omega, nameAt j hj⟩
  have insub : ∀ j (hj : j < (defsOf members).length), ∃ ci, ((defsOf members)[j].name, ci) ∈ sub.consts.toList :=
    fun j hj => ClosureLayout.converted_names_stored P hgr hconv _ (hnm ▸ (hnames _).mpr ⟨j, hj, rfl⟩)
  obtain ⟨cenv, benv, output, after, ran, fresh, ⟨cenvR, all, key, r, cache, hr', pub, hrec⟩, bound, blobs,
    published, H, hinted⟩ := needs.compiled
  -- a dropped block reads to nothing
  obtain ⟨plain, -⟩ := DefinitionSegments.block_read two views (fun k hk => (hinted k hk).2) hconv' hl
  rcases needs.collapse with e | e
  rotate_left
  · exact dropped_reads plain e empty
  refine DefinitionSegments.definition_block_segment P prelude corder canonical hf resolves two views insub
    needs.distinct needs.exactNames ran fresh hr' pub hrec bound blobs published hinted hconv' stGood.owners
    (fun qms e => by rw [e] at good; exact good) hl (fun d hd => levels e d (Array.mem_toList_iff.mpr hd))
    (.inl e) (fun _ => ?_) empty
  subst e
  obtain ⟨before, after', hplace, hin⟩ := DefinitionSegments.block_place P prelude corder canonical b steps inTrace hnd
    hmem resolves hy hr (by omega) hnames insub ran hr' pub hrec
    (fun j hj => ClosureLayout.lowered_declares hyx hc hl _ ((hnames _).mpr ⟨j, hj, rfl⟩))
  exact ⟨before, after', Option.some.inj (hseg.symm.trans hplace), hin⟩

/-- **An inductive group's segment reads as its read.** -/
theorem inductive_at (P : Premises env roots sub ixe failures t envQ) {preA : Prelude .anon}
    (prelude : preludeFor t = .ok preA) {b : Ix.RoleEvidence.Bundle}
    (hf : InjOn (evAddr ixe b) (QRepAt ixe (roleAtMap t)))
    (resolves : SingletonSegments.PublishedResolve ixe sub) {hints : CName .source → Option ReducibilityHint}
    {start : State .source} {ls : List Scheduled} {rs : List (Read .source)} {L : List Address}
    (steps : Steps (quotientGraph ixe t hints sub) start ls rs)
    (inTrace : ∀ y ∈ ls, y ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList)
    (hnd : L.Nodup) (hmem : ∀ a, a ∈ L ↔ ixe.consts.contains a = true)
    (corder : ClosureOrder ixe (Seed ixe sub) (cutOf ixe t hints sub ls L).flatten)
    (canonical : Stream.StoredCanonical ixe (cutOf ixe t hints sub ls L).flatten)
    {ℓ : Nat} {y : Scheduled} {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)}
    {recs : Array Ix.RecursorVal} {c : Converted} {stS : State .source} {raw rd : Read .source}
    (low : LoweredAt (quotientGraph ixe t hints sub) (fibers ixe t) hints start ls rs ℓ y (.inductive types ctors recs)
      c stS raw rd)
    {first : Ix.InductiveVal} (hfirst : types[0]? = some first)
    (needs : InductiveNeeds ixe sub t preA (cutOf ixe t hints sub ls L).flatten b types ctors recs first raw rd)
    (stGood : StateGood (scope ixe t) stS) (good : ConvGood (scope ixe t) ((c.withHints hints).quotient (fibers ixe t)))
    {seg : List Address} (hseg : (cutOf ixe t hints sub ls L)[ℓ]? = some seg) :
    SegmentReads (evAddr ixe b) (scope ixe t) (closureContext ixe t preA (cutOf ixe t hints sub ls L).flatten) ixe
      stS rd seg := by
  obtain ⟨hy, hr, hgr, hconv, hc, -, hl, -⟩ := low
  have hyx := inTrace y (List.mem_of_getElem? hy)
  have hconv' : Ix.LeanIngress.convertInductive types ctors recs = .ok c := hconv
  obtain ⟨first', hfirst', rfl, -⟩ := InductiveUnits.convertInductive_src hconv'
  have hnm : namesAt (quotientGraph ixe t hints sub) y = (Group.inductive types ctors recs).names := by
    unfold namesAt
    rw [ClosureLayout.getElem!_of_getElem? hgr]
  have hnames : ∀ n, n ∈ namesAt (quotientGraph ixe t hints sub) y ↔
      (∃ (i : Nat) (_ : i < types.size), types[i].cnst.name = n) ∨
      (∃ (i : Nat) (hi : i < ctors.size) (k : Nat) (_ : k < ctors[i].size), ctors[i][k].cnst.name = n) ∨
      ∃ (j : Nat) (_ : j < recs.size), recs[j].cnst.name = n := fun n => by
    rw [hnm]
    exact inductive_names types ctors recs n
  have namesIn := ClosureLayout.converted_names_stored P hgr hconv
  have typesIn : ∀ i (hi : i < types.size), ∃ ci, (types[i].cnst.name, ci) ∈ sub.consts.toList :=
    fun i hi => namesIn _ ((inductive_names types ctors recs _).mpr (.inl ⟨i, hi, rfl⟩))
  have ctorsIn : ∀ i (hi : i < ctors.size) k (hk : k < ctors[i].size),
      ∃ ci, (ctors[i][k].cnst.name, ci) ∈ sub.consts.toList :=
    fun i hi k hk => namesIn _ ((inductive_names types ctors recs _).mpr (.inr (.inl ⟨i, hi, k, hk, rfl⟩)))
  have recsIn : ∀ j (hj : j < recs.size), ∃ ci, (recs[j].cnst.name, ci) ∈ sub.consts.toList :=
    fun j hj => namesIn _ ((inductive_names types ctors recs _).mpr (.inr (.inr ⟨j, hj, rfl⟩)))
  obtain ⟨cenv₁, benv₁, out₁, after₁, cenv₂, benv₂, out₂, after₂, ran₁, ⟨cenvR₁, all₁, key₁, r₁, cache₁, hr₁, pub₁,
    hrec₁⟩, bound₁, blobs₁, published₁, ⟨cenvR₂, all₂, key₂, r₂, cache₂, hr₂, pub₂, hrec₂, ran₂⟩, bound₂, blobs₂,
    published₂, ⟨shape, hindexed, hshape, hrecs⟩, entries⟩ := needs.compiled
  obtain ⟨rlps, recLpsEq, recNodup⟩ := needs.recLevels
  obtain ⟨-, stored₁, -, stored₂, inert₂, hscoped, reads⟩ := InductiveSegments.closure_inductive_reads P prelude corder
    canonical hf resolves hconv' hfirst needs.hcsize needs.lpsEq needs.ctorLps needs.nodup needs.positions recLpsEq
    recNodup needs.hrne needs.distinct needs.noCtor needs.recDistinct typesIn ctorsIn recsIn ran₁ hr₁ pub₁ hrec₁
    bound₁ blobs₁ published₁ hr₂ pub₂ hrec₂ ran₂ bound₂ blobs₂ published₂ hindexed hshape hrecs entries
    (fun rb e => by
      have g : ConvGood (scope ixe t) (Converted.quotient (fiberAliasAt ixe (roleAtMap t))
          (Converted.inductive (InductiveUnits.srcBlock types ctors recs first'))) := good
      rw [e] at g
      exact g)
    stGood.types stGood.blocks hl
  have hpos : 0 < types.size := (Array.getElem?_eq_some_iff.mp hfirst).1
  obtain ⟨before, after, hplace, hin⟩ := InductiveSegments.inductive_place P prelude corder canonical steps inTrace hnd
    hmem resolves hy hr needs.hcsize hpos needs.hrne typesIn ctorsIn recsIn hnames ran₁ hr₁ pub₁ hrec₁ hr₂ pub₂
    hrec₂ ran₂ (fun n hn => by
      rw [needs.kept]
      refine ClosureLayout.lowered_declares hyx hc hl n ((hnames n).mpr ?_)
      rcases hn with h | h
      · exact .inl h
      · exact .inr (.inl h))
  exact InductiveSegments.inductive_segment P corder resolves stored₁ stored₂ inert₂ hscoped reads needs.kept
    ⟨before, after, Option.some.inj (hseg.symm.trans hplace), hin⟩

end Kinds

/-! ## Every segment -/
/-- **What the trace's lowered groups need**, for the lowered items `ls` of a trace from `start`
with reads `rs`, read in the order the record order `L` is cut into: every group's quotient
terms and every state's entries in the scope, distinct level positions for every kept definition
(`TraceSource.kept_levels`), and each lowered group what its kind needs. -/
structure TraceNeeds (ixe : Ixon.Env) (sub : Ix.Environment) (t : RoleTable) (preA : Prelude .anon)
    (b : Ix.RoleEvidence.Bundle) (hints : CName .source → Option ReducibilityHint) (start : State .source)
    (ls : List Scheduled) (rs : List (Read .source)) (L : List Address) : Prop where
  good : ∀ (i : Nat) (gr : Group) (c : Converted), (quotientGraph ixe t hints sub).groups[i]? = some gr →
    Ix.LeanIngress.convert gr = .ok c → ConvGood (scope ixe t) ((c.withHints hints).quotient (fibers ixe t))
  states : ∀ ℓ, StateGood (scope ixe t) ((rs.take ℓ).foldl State.commit start)
  levels : ∀ (ℓ : Nat) (r : Read .source), rs[ℓ]? = some r → ∀ d ∈ r.decls.toList, DefinitionBlockReads.DeclNodup d
  definitions : ∀ ℓ y ci c stS raw rd,
    LoweredAt (quotientGraph ixe t hints sub) (fibers ixe t) hints start ls rs ℓ y (.definitions #[ci]) c stS raw rd →
    DefinitionNeeds ixe sub hints ci
  axioms : ∀ ℓ y v c stS raw rd,
    LoweredAt (quotientGraph ixe t hints sub) (fibers ixe t) hints start ls rs ℓ y (.axiom v) c stS raw rd →
    HeaderNeeds ixe sub (.axiomInfo v) raw rd
  quotients : ∀ ℓ y v c stS raw rd,
    LoweredAt (quotientGraph ixe t hints sub) (fibers ixe t) hints start ls rs ℓ y (.quot v) c stS raw rd →
    HeaderNeeds ixe sub (.quotInfo v) raw rd
  blocks : ∀ ℓ y members c stS raw rd,
    LoweredAt (quotientGraph ixe t hints sub) (fibers ixe t) hints start ls rs ℓ y (.definitions members) c
      stS raw rd →
    2 ≤ members.size → BlockNeeds ixe sub t preA (cutOf ixe t hints sub ls L).flatten hints members raw rd
  inductives : ∀ ℓ y types ctors recs c stS raw rd first,
    LoweredAt (quotientGraph ixe t hints sub) (fibers ixe t) hints start ls rs ℓ y (.inductive types ctors recs) c
      stS raw rd →
    types[0]? = some first →
    InductiveNeeds ixe sub t preA (cutOf ixe t hints sub ls L).flatten b types ctors recs first raw rd

/-- **The segments of quotient Source's trace read as its reads**, when each lowered group has
what its kind needs. -/
theorem segmentsRead_of_needs {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : RoleTable} {envQ : Env .source}
    (P : Premises env roots sub ixe failures t envQ) {preA : Prelude .anon}
    (prelude : preludeFor t = .ok preA) {b : Ix.RoleEvidence.Bundle}
    (hf : InjOn (evAddr ixe b) (QRepAt ixe (roleAtMap t)))
    (resolves : SingletonSegments.PublishedResolve ixe sub) {hints : CName .source → Option ReducibilityHint}
    {start : State .source} {ls : List Scheduled} {rs : List (Read .source)} {L : List Address}
    (steps : Steps (quotientGraph ixe t hints sub) start ls rs)
    (inTrace : ∀ y ∈ ls, y ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList)
    (hnd : L.Nodup) (hmem : ∀ a, a ∈ L ↔ ixe.consts.contains a = true)
    (corder : ClosureOrder ixe (Seed ixe sub) (cutOf ixe t hints sub ls L).flatten)
    (canonical : Stream.StoredCanonical ixe (cutOf ixe t hints sub ls L).flatten)
    (empty : ∀ (ℓ : Nat) (r : Read .source), rs[ℓ]? = some r → r.decls = #[] →
      (cutOf ixe t hints sub ls L)[ℓ]? = some [])
    (needs : TraceNeeds ixe sub t preA b hints start ls rs L) :
    SegmentsRead (evAddr ixe b) (scope ixe t) (closureContext ixe t preA (cutOf ixe t hints sub ls L).flatten) ixe
      start rs (cutOf ixe t hints sub ls L) := by
  refine segmentsRead_of_each (by rw [ClosureLayout.segmentsOf_length, List.length_map, steps.1])
    fun ℓ r seg hr hseg => ?_
  have hℓ : ℓ < ls.length := by rw [steps.1]; exact (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨y, hy⟩ : ∃ y, ls[ℓ]? = some y := ⟨_, List.getElem?_eq_getElem hℓ⟩
  obtain ⟨conv, raw, s, s', kb, kb', dropped, hc, hl, hcol, -, -, -⟩ := steps.2 ℓ y r hy hr
  have hyx := inTrace y (List.mem_of_getElem? hy)
  obtain ⟨gr, c, hgr, hconv, rfl⟩ := ClosureLayout.scheduled_conversion hyx hc
  rw [ClosureLayout.getElem!_of_getElem? hgr] at hcol
  have low : LoweredAt (quotientGraph ixe t hints sub) (fibers ixe t) hints start ls rs ℓ y gr c
      ((rs.take ℓ).foldl State.commit start) raw r :=
    ⟨hy, hr, hgr, hconv, hc, rfl, hl, s, s', dropped, hcol⟩
  have hempty : r.decls = #[] → seg = [] := fun h => Option.some.inj (hseg.symm.trans (empty ℓ r hr h))
  have cgood := needs.good y.1.1 gr c hgr hconv
  have hlevels : r = raw → ∀ d ∈ raw.decls.toList, DefinitionBlockReads.DeclNodup d := fun e d hd =>
    needs.levels ℓ r hr d (by rw [e]; exact hd)
  cases gr with
  | invalid ns e => simp [Ix.LeanIngress.convert, throw, throwThe, MonadExceptOf.throw] at hconv
  | «axiom» v =>
    exact axiom_at P prelude resolves steps inTrace hnd hmem corder canonical low (needs.axioms _ _ _ _ _ _ _ low)
      hseg hempty
  | quot v =>
    exact quotient_at P prelude resolves steps inTrace hnd hmem corder canonical low
      (needs.quotients _ _ _ _ _ _ _ low) hseg hempty
  | definitions members =>
    obtain ⟨l⟩ := members
    rcases l with _ | ⟨ci, _ | ⟨ci', rest⟩⟩
    · exact empty_at low hempty
    · exact definition_at P prelude hf resolves steps inTrace hnd hmem corder canonical low
        (needs.definitions _ _ _ _ _ _ _ low) (needs.states ℓ) cgood hlevels hseg hempty
    · exact block_at P prelude hf resolves steps inTrace hnd hmem corder canonical low (by simp)
        (needs.blocks _ _ _ _ _ _ _ low (by simp)) (needs.states ℓ) cgood hlevels hseg hempty
  | «inductive» types ctors recs =>
    obtain ⟨first, hfirst, -⟩ := InductiveUnits.convertInductive_src
      (show Ix.LeanIngress.convertInductive types ctors recs = .ok c from hconv)
    exact inductive_at P prelude hf resolves steps inTrace hnd hmem corder canonical low hfirst
      (needs.inductives _ _ _ _ _ _ _ _ _ _ low hfirst) (needs.states ℓ) cgood hseg

/-- **The reader's units from what the trace's lowered groups need**: for an accepted closure
whose compiled records lie as `Layout` says, quotient Source's trace from the prelude has the
reader's units once every cut of the compile's record order into the trace's segments holds
stored canonical records and gives each lowered group what its kind needs. -/
theorem unitsRead_of_needs {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : RoleTable} {envQ : Env .source}
    (P : Premises env roots sub ixe failures t envQ) {preA : Prelude .anon}
    (prelude : preludeFor t = .ok preA) {b : Ix.RoleEvidence.Bundle}
    (hf : InjOn (evAddr ixe b) (QRepAt ixe (roleAtMap t)))
    (resolves : SingletonSegments.PublishedResolve ixe sub) {hints : CName .source → Option ReducibilityHint}
    {pre : Prelude .source} {rs : List (Read .source)} {fin : State .source} {s : Ix.LeanIngress.CollapseState}
    {kb : Ix.LeanIngress.KeptBlocks}
    (htrace : SourcePrelude.Trace (quotientGraph ixe t hints sub) pre.state
      (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList rs fin s kb)
    (layout : ClosureLayout.Layout ixe (quotientGraph ixe t hints sub))
    (each : ∀ (ls : List Scheduled) (L : List Address), Steps (quotientGraph ixe t hints sub) pre.state ls rs →
      (∀ y ∈ ls, y ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList) →
      L.Nodup → (∀ a, a ∈ L ↔ ixe.consts.contains a = true) → L.Pairwise (fun a b => ¬ RecordRef ixe a b) →
      ClosureOrder ixe (Seed ixe sub) (cutOf ixe t hints sub ls L).flatten →
      Stream.StoredCanonical ixe (cutOf ixe t hints sub ls L).flatten ∧
        TraceNeeds ixe sub t preA b hints pre.state ls rs L) :
    ReaderStreamsUnits.UnitsRead ixe sub t preA b pre rs :=
  ClosureLayout.unitsRead_of_layout P htrace layout fun ls L steps inTrace hnd hmem hpw corder empty =>
    have needs := each ls L steps inTrace hnd hmem hpw corder
    ⟨needs.1, segmentsRead_of_needs P prelude hf resolves steps inTrace hnd hmem corder needs.1 empty needs.2⟩

/--
info: 'Ix.Cert.TraceSegments.segmentsRead_of_needs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms segmentsRead_of_needs

/--
info: 'Ix.Cert.TraceSegments.unitsRead_of_needs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms unitsRead_of_needs

end Ix.Cert.TraceSegments
