import Ix.Cert.BlockRecords
import Ix.CompileCert.MutualArtifact
import Ix.CompileCert.EmissionBlocks
import Ix.CompileCert.Canon.QSort

/-! # The names a block's compile claims

A block's compile (`Ix.CompileM.runBlock`) claims the names of its result's
projections (`Ix.Cert.Resolution.claimWrites`), or its key when there are
none. This file shows that each of them is a member's name or the name of a
constructor an inductive member lists:

* a mutual block's projections carry its members' names and their
  constructors' (`mutualBlock_names`), and a lone constant other than an
  inductive or a constructor has none (`constantInfo_lone`);
* so `runBlock`'s projections carry those names (`compileBlock_names`,
  `runBlock_owned`). -/

namespace Ix.Cert.Claims

open Ix Ix.CompileM

/-! ## A block compile's projection names -/

section names

open Ix.CompileCert.Emission (Yields)
open Ix.CompileCert.MutualProjections (logicalRows expectedRows sourceRows)

/-- `x` is the name of a member of `sources` or of a constructor such a
member carries. -/
def SourceName (sources : List MutConst) (x : Name) : Prop :=
  ∃ src ∈ sources, x = src.name ∨ ∃ ctor ∈ src.ctors, x = ctor.cnst.name

theorem mem_of_mem_zipIdx {α : Type} {l : List α} {x : α} {i : Nat} (h : (x, i) ∈ l.zipIdx) : x ∈ l :=
  List.fst_mem_of_mem_zipIdx h

theorem expectedRows_name {owner : Address} {sources : List MutConst} {x : Name}
    {c : Ixon.Constant} (h : (x, c) ∈ expectedRows owner sources) : SourceName sources x := by
  unfold expectedRows at h
  obtain ⟨⟨src, index⟩, hm, h⟩ := List.mem_flatMap.1 h
  refine ⟨src, mem_of_mem_zipIdx hm, ?_⟩
  unfold sourceRows at h
  rcases List.mem_cons.1 h with h | h
  · exact .inl (Prod.mk.inj h).1
  · obtain ⟨⟨ctor, ci⟩, hci, he⟩ := List.mem_map.1 h
    exact .inr ⟨ctor, Array.mem_toList_iff.1 (mem_of_mem_zipIdx hci), (Prod.mk.inj he).1.symm⟩

theorem row_logical {rows : Array Ix.CompileCert.MutualProjections.Row} {row : Ix.CompileCert.MutualProjections.Row} (h : row ∈ rows) :
    (row.1, row.2.1) ∈ logicalRows rows :=
  List.mem_map.2 ⟨row, Array.mem_toList_iff.2 h, rfl⟩

/-- **A mutual block's projections carry its members' names and their
constructors'**: the wrapper's rows (`MutualProjections.build_rows`), or a
collapsed block's, every member registered to it
(`MutualProjections.standalone_rows`). -/
theorem mutualBlock_names (sources : List MutConst) :
    Yields (compileMutualBlock sources) (fun out => ∀ row ∈ out.projections, SourceName sources row.1) := by
  refine Ix.CompileCert.ProjectionLayout.mutual_block _ sources ?_
  unfold compileMutualPayload
  refine Ix.CompileCert.Emission.Yields.bindAny _ fun compiled => ?_
  intro context before output after ran
  obtain ⟨-, -, built⟩ :=
    Ix.CompileCert.ProjectionLayout.finish_mutual_ok context sources compiled.1 compiled.2.2 ran
  obtain ⟨-, wrapped | collapsed⟩ :=
    Ix.CompileCert.MutualArtifact.build_cases _ sources compiled.1 compiled.2.2 before output built
  · obtain ⟨targets, metadata, -, -, proj⟩ := wrapped
    intro row hrow
    have hl := row_logical hrow
    rw [proj, Ix.CompileCert.MutualProjections.build_rows] at hl
    exact expectedRows_name hl
  · obtain ⟨-, -, rows⟩ := collapsed
    intro row hrow
    have hl := row_logical hrow
    rw [rows] at hl
    obtain ⟨src, hsrc, he⟩ := List.mem_map.1 hl
    exact ⟨src, hsrc, .inl (Prod.mk.inj he).1.symm⟩

/-- The block finisher returns no projections. -/
theorem finish_lone (info : Ixon.ConstantInfo) (blockMeta : Ixon.ConstantMeta) :
    Yields (finishConstantInfoWithSharing info blockMeta) (fun r => r.projections = #[]) := by
  intro context before output after ran
  rw [Ix.CompileCert.EmissionBlocks.finish_run] at ran
  cases built : buildConstantWithSharing context.1.sharingLimits info before.refs before.univs with
  | error e => rw [built] at ran; cases ran
  | ok block =>
    rw [built] at ran
    simp only [Except.map, Prod.mk.injEq, Except.ok.injEq] at ran
    obtain ⟨rfl, -⟩ := ran
    rfl

theorem definitionDataInfo_lone (source : Ix.Def) :
    Yields (compileDefinitionDataInfo source) (fun r => r.projections = #[]) := by
  unfold compileDefinitionDataInfo compileDefinitionDataBlock
  exact Yields.bindAny _ fun _ => Yields.bindAny _ fun d => by
    obtain ⟨a, b, c, e⟩ := d
    exact finish_lone _ _

/-- **A lone constant's compile returns no projections**, for every kind but
an inductive's and a constructor's (the block compile sends those through
the mutual compiler). -/
theorem constantInfo_lone (const : ConstantInfo) (hi : ∀ v, const = .inductInfo v → False)
    (hc : ∀ v, const = .ctorInfo v → False) :
    Yields (compileConstantInfo const) (fun r => r.projections = #[]) := by
  cases const with
  | defnInfo v =>
    show Yields (compileDefinitionConstantInfo v) _
    unfold compileDefinitionConstantInfo withMutCtx
    rw [Ix.CompileCert.EmissionDispatch.compileDefinitionInfo_eq]
    exact Yields.withBlockEnv _ (definitionDataInfo_lone _)
  | thmInfo v =>
    show Yields (compileTheoremConstantInfo v) _
    unfold compileTheoremConstantInfo withMutCtx compileTheoremInfo
    exact Yields.withBlockEnv _ (definitionDataInfo_lone _)
  | opaqueInfo v =>
    show Yields (compileOpaqueConstantInfo v) _
    unfold compileOpaqueConstantInfo withMutCtx compileOpaqueInfo
    exact Yields.withBlockEnv _ (definitionDataInfo_lone _)
  | axiomInfo v =>
    show Yields (compileConstantInfoCore (.axiomInfo v)) _
    unfold compileConstantInfoCore withMutCtx
    refine Yields.withBlockEnv _ ?_
    show Yields (compileAxiomInfo v) _
    unfold compileAxiomInfo compileAxiomBlock
    exact Yields.bindAny _ fun _ => Yields.bindAny _ fun d => by
      obtain ⟨a, b, c⟩ := d
      exact finish_lone _ _
  | quotInfo v =>
    show Yields (compileQuotientConstantInfo v) _
    unfold compileQuotientConstantInfo withMutCtx compileQuotientInfo compileQuotientBlock
    exact Yields.withBlockEnv _ (Yields.bindAny _ fun _ => Yields.bindAny _ fun d => by
      obtain ⟨a, b, c⟩ := d
      exact finish_lone _ _)
  | recInfo v =>
    show Yields (compileRecursorConstantInfo v) _
    unfold compileRecursorConstantInfo withMutCtx compileRecursorInfo compileRecursorBlock
    exact Yields.withBlockEnv _ (Yields.bindAny _ fun _ => Yields.bindAny _ fun d => by
      obtain ⟨a, b, c⟩ := d
      exact finish_lone _ _)
  | inductInfo v => exact absurd rfl (hi v)
  | ctorInfo v => exact absurd rfl (hc v)

end names

/-! ## The members a block compile reads -/

section members

open Ix.CompileCert (rawRun rawRun_pure bind_ok)

variable {α β γ σ : Type}

/-- Every successful run from the context `ctx` returns a value satisfying
`P`. -/
def RunPost (ctx : CompileEnv × BlockEnv) (P : α → Prop) (x : CompileM α) : Prop :=
  ∀ s v s', rawRun x ctx s = (.ok v, s') → P v

theorem RunPost.pure {ctx : CompileEnv × BlockEnv} {P : α → Prop} {a : α} (h : P a) :
    RunPost ctx P (Pure.pure a) := by
  intro s v s' hr
  rw [rawRun_pure] at hr
  cases hr
  exact h

theorem RunPost.bind {ctx : CompileEnv × BlockEnv} {x : CompileM α} {f : α → CompileM β} {q : α → Prop}
    {p : β → Prop} (hx : RunPost ctx q x) (hf : ∀ a, q a → RunPost ctx p (f a)) : RunPost ctx p (x >>= f) := by
  intro s v s' hr
  obtain ⟨a, m, ha, hb⟩ := bind_ok hr
  exact hf a (hx s a m ha) m v s' hb

theorem RunPost.throw {ctx : CompileEnv × BlockEnv} {P : α → Prop} (e : CompileError) :
    RunPost ctx P (throw e : CompileM α) := by
  intro s v s' hr
  rw [Ix.CompileCert.rawRun_throw] at hr
  cases hr

theorem RunPost.findConst (ctx : CompileEnv × BlockEnv) (n : Name) :
    RunPost ctx (fun c => ctx.1.env.get? n = some c) (findConst n) :=
  fun _ _ _ hr => Ix.Cert.BlockRecords.findConst_ok hr

/-- A loop over a list keeps an invariant its body keeps. -/
theorem RunPost.forIn (ctx : CompileEnv × BlockEnv) (I : σ → Prop) (body : γ → σ → CompileM (ForInStep σ)) :
    ∀ (l : List γ), (∀ x ∈ l, ∀ acc, I acc → RunPost ctx (fun st => I st.value) (body x acc)) →
      ∀ init, I init → RunPost ctx I (forIn l init body)
  | [], _, init, h => by rw [List.forIn_nil]; exact RunPost.pure h
  | x :: l, hb, init, h => by
    rw [List.forIn_cons]
    refine RunPost.bind (hb x List.mem_cons_self init h) fun st hst => ?_
    cases st with
    | done b => exact RunPost.pure hst
    | yield b =>
      exact RunPost.forIn ctx I body l (fun y hy => hb y (List.mem_cons_of_mem _ hy)) b hst

/-- The constructors `MutConst.mkIndc` collects are stored, as constructors,
under names of the list. -/
theorem collectCtors_post (ctx : CompileEnv × BlockEnv) (L : List Name) :
    ∀ (names : List Name) (acc : Array ConstructorVal),
      (∀ ctor ∈ acc, ∃ c ∈ L, ctx.1.env.get? c = some (.ctorInfo ctor)) → (∀ c ∈ names, c ∈ L) →
      RunPost ctx (fun out => ∀ ctor ∈ out, ∃ c ∈ L, ctx.1.env.get? c = some (.ctorInfo ctor))
        (collectMutConstConstructors names acc)
  | [], acc, h, _ => by
    rw [collectMutConstConstructors]
    exact RunPost.pure h
  | c :: rest, acc, h, hn => by
    rw [collectMutConstConstructors]
    refine RunPost.bind (RunPost.findConst ctx c) fun ci hci => ?_
    split
    · refine collectCtors_post ctx L rest _ (fun ctor hctor => ?_) (fun c' hc' => hn c' (by simp [hc']))
      rcases Array.mem_push.1 hctor with hctor | rfl
      · exact h ctor hctor
      · exact ⟨c, hn c (by simp), hci⟩
    · exact RunPost.throw _

theorem mkIndc_post (ctx : CompileEnv × BlockEnv) (val : InductiveVal) :
    RunPost ctx (fun m => m.name = val.cnst.name ∧
        ∀ ctor ∈ m.ctors, ∃ c ∈ val.ctors.toList, ctx.1.env.get? c = some (.ctorInfo ctor))
      (MutConst.mkIndc val) := by
  unfold MutConst.mkIndc
  exact RunPost.bind (collectCtors_post ctx val.ctors.toList _ #[] (by simp) fun _ h => h)
    fun ctors h => RunPost.pure ⟨rfl, h⟩

/-- A mutual source the block compile reads: the constant stored under a
member's name, with that constant's name, and, for an inductive, the
constructors stored under the names it lists. -/
def Member (E : Ix.Environment) (all : Ix.Set Name) (m : MutConst) : Prop :=
  ∃ n ci, all.contains n = true ∧ E.get? n = some ci ∧ m.name = ci.getCnst.name ∧
    ∀ ctor ∈ m.ctors, ∃ iv c, ci = .inductInfo iv ∧ c ∈ iv.ctors ∧ E.get? c = some (.ctorInfo ctor)

/-- **The block compile's members loop reads members**. -/
theorem members_post (ctx : CompileEnv × BlockEnv) (all : Ix.Set Name) :
    RunPost ctx (fun cs : Array MutConst => ∀ m ∈ cs, Member ctx.1.env all m)
      (forIn all #[] fun n (acc : Array Ix.MutConst) => do
        match ← findConst n with
        | .inductInfo val => pure (ForInStep.yield (acc.push (← MutConst.mkIndc val)))
        | .defnInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromDefinitionVal val)))
        | .opaqueInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromOpaqueVal val)))
        | .thmInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromTheoremVal val)))
        | .recInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.recr val)))
        | _ => pure (ForInStep.yield acc)) := by
  rw [Std.HashSet.forIn_eq_forIn_toList]
  refine RunPost.forIn ctx _ _ all.toList (fun n hn acc hacc => ?_) #[] (by simp)
  have hin : all.contains n = true :=
    Std.HashSet.mem_iff_contains.1 (Std.HashSet.mem_of_mem_toList hn)
  have push : ∀ m, Member ctx.1.env all m → ∀ m' ∈ acc.push m, Member ctx.1.env all m' := by
    intro m hm m' hm'
    rcases Array.mem_push.1 hm' with hm' | rfl
    · exact hacc m' hm'
    · exact hm
  refine RunPost.bind (RunPost.findConst ctx n) fun ci hci => ?_
  split
  · rename_i val
    refine RunPost.bind (mkIndc_post ctx val) fun m hm => RunPost.pure (push m ?_)
    refine ⟨n, _, hin, hci, hm.1, fun ctor hctor => ?_⟩
    obtain ⟨c, hc, hcs⟩ := hm.2 ctor hctor
    exact ⟨val, c, rfl, Array.mem_toList_iff.1 hc, hcs⟩
  · exact RunPost.pure (push _ ⟨n, _, hin, hci, rfl, fun ctor h => absurd h (by
      simp [Ix.MutConst.fromDefinitionVal, Ix.MutConst.ctors])⟩)
  · exact RunPost.pure (push _ ⟨n, _, hin, hci, rfl, fun ctor h => absurd h (by
      simp [Ix.MutConst.fromOpaqueVal, Ix.MutConst.ctors])⟩)
  · exact RunPost.pure (push _ ⟨n, _, hin, hci, rfl, fun ctor h => absurd h (by
      simp [Ix.MutConst.fromTheoremVal, Ix.MutConst.ctors])⟩)
  · exact RunPost.pure (push _ ⟨n, _, hin, hci, rfl, fun ctor h => absurd h (by
      simp [Ix.MutConst.ctors])⟩)
  · exact RunPost.pure hacc

/-- `x` is the name of a member the block compile reads, or of a constructor
such a member lists. -/
def MemberName (E : Ix.Environment) (all : Ix.Set Name) (x : Name) : Prop :=
  ∃ m, Member E all m ∧ (x = m.name ∨ ∃ ctor ∈ m.ctors, x = ctor.cnst.name)

/-- **Lean's order only arranges a block's members**: every class
`sourceMembers` returns holds members of its input. -/
theorem mem_sourceMembers {cs : Array MutConst} {x : MutConst}
    (hc : x ∈ sourceMembers cs) : x ∈ cs := by
  unfold sourceMembers at hc
  try dsimp only at hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
  exact Array.fst_mem_of_mem_zipIdx (Ix.CompileCert.Canon.mem_qsort.1 (Array.mem_toList_iff.1 he))

/-- **The block compile's projections carry members' names**: a lone
constant's compile has none (`constantInfo_lone`), and the mutual compile's
are its sources' (`mutualBlock_names`), which Lean's order only arranges
(`mem_sourceMembers`) and which the members loop reads (`members_post`). -/
theorem compileBlock_names {ctx : CompileEnv × BlockEnv} {lo : Name} {all : Ix.Set Name}
    {s s' : BlockState} {r : BlockResult}
    (h : rawRun (compileBlock lo all) ctx s = (.ok r, s')) :
    ∀ row ∈ r.projections, MemberName ctx.1.env all row.1 := by
  unfold compileBlock at h
  obtain ⟨const, s₁, hc, h⟩ := bind_ok h
  dsimp only at h
  -- the kind test, then the lone test
  split at h <;> split at h
  all_goals first
    | (rename_i hcond; simp at hcond; done)
    | (have none := constantInfo_lone _ (by assumption) (by assumption)
         ctx s₁ r s' h
       intro row hrow
       rw [none] at hrow
       exact absurd hrow (by simp))
    | (obtain ⟨cs, s₂, hcs, h⟩ := bind_ok h
       obtain ⟨out, s₄, hout, h⟩ := bind_ok h
       have same : Ix.Cert.BlockRecords.recordsOf r = Ix.Cert.BlockRecords.recordsOf out := by
         revert h
         refine Ix.Cert.BlockRecords.Returns.elim
           (P := fun (x : BlockResult) =>
             Ix.Cert.BlockRecords.recordsOf x = Ix.Cert.BlockRecords.recordsOf out) ?_
         repeat returns_step
       have members := members_post ctx all s₁ cs s₂ hcs
       have names := mutualBlock_names (sourceMembers cs) ctx s₂ out s₄ hout
       intro row hrow
       unfold Ix.Cert.BlockRecords.recordsOf at same
       have hmap : (row.1, row.2.1) ∈ out.projections.map (fun p => (p.1, p.2.1)) := by
         rw [← (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj same).2).2).2]
         exact Array.mem_map_of_mem hrow
       obtain ⟨row', hrow', he⟩ := Array.mem_map.1 hmap
       obtain ⟨src, hsrc, hname⟩ := names row' hrow'
       have hm := members src (mem_sourceMembers hsrc)
       rw [← (Prod.mk.inj he).1]
       exact ⟨src, hm, hname⟩)

end members

/-! ## The claims of a block compile -/

section claims

/-- `ci'` keeps `ci`'s name and, for an inductive, its constructors. -/
def Keeps (ci ci' : ConstantInfo) : Prop :=
  ci'.getCnst.name = ci.getCnst.name ∧
    ∀ iv', ci' = .inductInfo iv' → ∃ iv, ci = .inductInfo iv ∧ iv'.ctors = iv.ctors

/-- `E'` holds, under each name, a constant that keeps the name and constructors
of a constant `E` holds under a `==` name. -/
def Agrees (E E' : Ix.Environment) : Prop :=
  ∀ x ci', E'.get? x = some ci' → ∃ n ci, (n == x) = true ∧ E.get? n = some ci ∧ Keeps ci ci'

theorem Agrees.refl (E : Ix.Environment) : Agrees E E :=
  fun x ci h => ⟨x, ci, BEq.rfl, h, rfl, fun iv' h' => ⟨iv', h', rfl⟩⟩

/-- Every constant `E` holds carries a name `==` the one it is held under. -/
def NamedEnv (E : Ix.Environment) : Prop :=
  ∀ x ci, E.get? x = some ci → (ci.getCnst.name == x) = true

theorem Agrees.named {E E' : Ix.Environment} (ha : Agrees E E') (hn : NamedEnv E) : NamedEnv E' := by
  intro x ci' h
  obtain ⟨n, ci, hnx, hci, keeps⟩ := ha x ci' h
  rw [keeps.1]
  exact PartialEquivBEq.trans (hn n ci hci) hnx

/-- `x` hashes like a member of `all`, or like a constructor an inductive
member lists in `E`. -/
def Owned (E : Ix.Environment) (all : Ix.Set Name) (x : Name) : Prop :=
  (∃ m, all.contains m = true ∧ (x == m) = true) ∨
    ∃ I iv c, all.contains I = true ∧ E.get? I = some (.inductInfo iv) ∧ c ∈ iv.ctors ∧ (x == c) = true

theorem memberName_owned {E E' : Ix.Environment} {all : Ix.Set Name} {x : Name} (ha : Agrees E E')
    (hn : NamedEnv E) (h : MemberName E' all x) : Owned E all x := by
  have hn' := ha.named hn
  obtain ⟨m, ⟨n, ci', hin, hci', hname, hctors⟩, hx⟩ := h
  rcases hx with rfl | ⟨ctor, hctor, rfl⟩
  · exact .inl ⟨n, hin, by rw [hname]; exact hn' n ci' hci'⟩
  · obtain ⟨iv', c, rfl, hc, hcs⟩ := hctors ctor hctor
    obtain ⟨n₀, ci₀, hn₀, hci₀, -, kind⟩ := ha n _ hci'
    obtain ⟨iv₀, rfl, same⟩ := kind iv' rfl
    refine .inr ⟨n₀, iv₀, c, ?_, hci₀, same ▸ hc, hn' c _ hcs⟩
    rw [Std.HashSet.contains_congr hn₀]
    exact hin

end claims

/-- **The claims of a block compile**: every projection name of
`runBlock cenv all lo` hashes like a member of `all` or like a constructor an
inductive member lists, when every constant of `cenv.env` carries its name
(`compileBlock_names`). -/
theorem runBlock_owned {cenv : CompileEnv} {all : Ix.Set Name} {lo : Name} {r : BlockResult}
    {cache : BlockState}
    (hn : NamedEnv cenv.env) (h : runBlock cenv all lo = .ok (r, cache)) :
    ∀ row ∈ r.projections, Owned cenv.env all row.1 := by
  have names := compileBlock_names
    (Ix.CompileCert.run_success (Ix.Cert.BlockRecords.runBlock_compiles h))
  intro row hrow
  exact memberName_owned (Agrees.refl _) hn (names row hrow)

end Ix.Cert.Claims
