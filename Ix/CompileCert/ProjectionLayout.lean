import Ix.CompileCert.EmissionDispatch

/-! # Mutual layout: the folds' shapes, the write-back, the family's projections

What the compiler's folds keep of the source, and what the sharing
build's write-back keeps of the payload (CT-15's `ProjectionLayout`, R9a):

* the constructor fold keeps every constructor's header, as natural numbers
  (`constructors_headers`), and its registration name;
* the class fold retains one payload per class, its first member, so a
  mutual payload has one member per class with the representative's kind
  and constructor positions (`payload_shapes`, `payload_count`), and the
  mutual guard bounds the class count (`mutual_block_capacity`);
* the write-back keeps every member's kind and constructor positions
  (`writeback_shape`, `sharing_shape`): both are fields `erase` keeps, so
  they follow from R7b's one inversion (`SharingRoots.withRoots_inv`,
  `build_roots`);
* the class sort's guard leaves no empty class (`sort_nonempty`), which
  discharges `payload_count`'s premise for every sorted block, and the
  compiler's sort is `sortClasses Rules.compiler` on an address map of the
  state, which it leaves unchanged (`sort_run`, R9b);
* the standalone inductive family's block is `.muts #[.indc target]` with
  the source's constructor positions (`family_layout`), and its projection
  records resolve under the certified reader to the block's member and its
  constructors (`inductive_projection_resolves`,
  `constructor_projection_resolves`).

Ported from the donor `a9cf3607`, adapted: `Emission.Yields` for the
donor's `DeclarationHeaders.Returns`, `Address.admissionHash` for
`Address.blake3`, the write-back facts through `erase` (R07-17), no
`timedC`/`PhaseTimers`, and the mutual block's plan-head audit passed over
(a successful run passed it). Not ported: the donor's `ordered_nonempty`,
whose subject `orderRecursorFamily` is not on this tree (batch 3). Since
CQ2.18 the class sort is `Ix.Compile.Canon.sortClasses Rules.compiler`,
whose guard is what `sorted_nonempty` reads. -/

namespace Ix.CompileCert.ProjectionLayout

open Ix.CompileM Ix.CompileCert

/-! ## Constructors -/

/-- A compiled constructor's header fields, as natural numbers, are its
source's. -/
def CtorHeader (source : ConstructorVal) (target : Ixon.Constructor) : Prop :=
  target.lvls.toNat = source.cnst.levelParams.size ∧ target.cidx.toNat = source.cidx ∧
    target.params.toNat = source.numParams ∧ target.fields.toNat = source.numFields

theorem constructor_header (source : ConstructorVal) :
    Emission.Yields (compileConstructor source) (fun output => CtorHeader source output.1) := by
  unfold compileConstructor
  exact Emission.Yields.withCurrent _ (Emission.Yields.bindAny _ fun _ => Emission.Yields.bindAny _ fun typed =>
    Emission.constructorHeader source typed.1 typed.2)

theorem constructor_index (source : ConstructorVal) :
    Emission.Yields (compileConstructor source) (fun output => output.1.cidx.toNat = source.cidx) :=
  fun context before output after ran => (constructor_header source context before output after ran).2.1

/-- **The constructor fold** appends one compiled constructor per source
constructor, in order, each with its source's header, and registers each
under its source name. -/
theorem constructors_headers (sources : List ConstructorVal) (initial : InductiveConstructorCompileState) :
    Emission.Yields (compileInductiveConstructors sources initial) (fun output =>
      ∃ targets, output.ctors.toList = initial.ctors.toList ++ targets ∧
        List.Forall₂ CtorHeader sources targets ∧
        output.ctorMetaPairs.toList.map Prod.fst =
          initial.ctorMetaPairs.toList.map Prod.fst ++ sources.map (·.cnst.name)) := by
  induction sources generalizing initial with
  | nil => exact Emission.Yields.pure ⟨[], by simp, .nil, by simp⟩
  | cons source rest ih =>
    intro context before output after ran
    rw [compileInductiveConstructors] at ran
    obtain ⟨compiled, middle, first, last⟩ := bind_ok ran
    have header := constructor_header source context before compiled middle first
    obtain ⟨targets, ctors, headers, names⟩ := ih {
      ctors := initial.ctors.push compiled.1
      ctorMetaPairs := initial.ctorMetaPairs.push (source.cnst.name, compiled.2.1)
      ctorNameAddrs := initial.ctorNameAddrs.push source.cnst.name.getHash
      ctorExprs := initial.ctorExprs.push compiled.2.2 } context middle output after last
    refine ⟨compiled.1 :: targets, ?_, .cons header headers, ?_⟩
    · simpa only [Array.toList_push, List.append_assoc, List.singleton_append] using ctors
    · simpa only [Array.toList_push, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.singleton_append] using names

theorem headers_indices {sources : List ConstructorVal} {targets : List Ixon.Constructor}
    (headers : List.Forall₂ CtorHeader sources targets) :
    targets.map (fun ctor => ctor.cidx.toNat) = sources.map (·.cidx) := by
  induction headers with
  | nil => rfl
  | cons head _ ih => simp only [List.map_cons, head.2.1, ih]

theorem constructors_layout (sources : List ConstructorVal) (initial : InductiveConstructorCompileState) :
    Emission.Yields (compileInductiveConstructors sources initial) (fun output =>
      output.ctors.toList.map (fun ctor => ctor.cidx.toNat) =
        initial.ctors.toList.map (fun ctor => ctor.cidx.toNat) ++ sources.map (·.cidx) ∧
      output.ctorMetaPairs.toList.map Prod.fst =
        initial.ctorMetaPairs.toList.map Prod.fst ++ sources.map (·.cnst.name)) := by
  intro context before output after ran
  obtain ⟨targets, ctors, headers, names⟩ := constructors_headers sources initial context before output after ran
  refine ⟨?_, names⟩
  rw [ctors, List.map_append, headers_indices headers]

/-! ## Class and payload counts -/

theorem equivalents_count (sources : List MutConst) (initial : MutConstCompileState) :
    Emission.Yields (compileEquivalentMutConsts sources initial)
      (fun output => output.payloads.size = initial.payloads.size) := by
  induction sources generalizing initial with
  | nil => exact Emission.Yields.pure rfl
  | cons source rest ih =>
    rw [compileEquivalentMutConsts]
    exact Emission.Yields.bindAny _ fun member => ih (initial.addEquivalent member)

theorem class_count (sources : List MutConst) (initial : MutConstCompileState) :
    Emission.Yields (compileMutConstClass sources initial)
      (fun output => output.payloads.size = initial.payloads.size + if sources.isEmpty then 0 else 1) := by
  cases sources with
  | nil => exact Emission.Yields.pure (by simp)
  | cons source rest =>
    rw [compileMutConstClass]
    apply Emission.Yields.bindAny
    intro member
    simpa [MutConstCompileState.addRepresentative] using equivalents_count rest (initial.addRepresentative member)

theorem classes_count (sources : List (List MutConst)) (initial : MutConstCompileState) :
    Emission.Yields (compileMutConstClasses sources initial)
      (fun output => output.payloads.size = initial.payloads.size +
        (sources.filter fun members => !members.isEmpty).length) := by
  induction sources generalizing initial with
  | nil => exact Emission.Yields.pure (by simp)
  | cons source rest ih =>
    intro context before output after ran
    rw [compileMutConstClasses] at ran
    obtain ⟨middle, state, firstRun, lastRun⟩ := bind_ok ran
    have first := class_count source initial context before middle state firstRun
    have last := ih middle context state output after lastRun
    cases source <;> simp_all
    omega

/-- **One payload per class**: a block of non-empty classes compiles to as
many payloads as classes. -/
theorem payload_count (sources : List (List MutConst))
    (nonempty : ∀ members ∈ sources, members ≠ []) :
    Emission.Yields (compileMutConsts sources) (fun output => output.1.size = sources.length) := by
  have filtered : (sources.filter fun members => !members.isEmpty) = sources := by
    apply List.filter_eq_self.mpr
    intro members present
    cases members with
    | nil => exact False.elim (nonempty [] present rfl)
    | cons _ _ => rfl
  unfold compileMutConsts
  exact Emission.Yields.bind (classes_count sources {}) fun compiled count =>
    Emission.Yields.pure (by simpa [filtered] using count)

/-! ## The mutual finisher -/

/-- **The mutual finisher's inversion**: it changes no state, its count
guard admits the payload's headers, and it returns the pure builder's
result over the block's tables. -/
theorem finish_mutual_ok (context : CompileEnv × BlockEnv) (classes : List (List MutConst))
    (members : Array Ixon.MutConst) (metadata : Array (Ix.Name × Ixon.ConstantMeta)) {before after : BlockState}
    {output : BlockResult}
    (ran : rawRun (finishMutualCompilation classes members metadata) context before = (.ok output, after)) :
    after = before ∧ Ix.Sharing.Verify.ConstantInfoHeaderWF (.muts members) ∧
      buildCompiledMutualBlock context.1.sharingLimits classes members metadata before = .ok output := by
  unfold finishMutualCompilation at ran
  obtain ⟨done, middle, guarded, rest⟩ := bind_ok ran
  have same := EmissionDispatch.mutual_state members context before
  rw [guarded] at same
  change middle = before at same
  subst same
  have bounds := EmissionDispatch.mutual_counts members context middle done middle guarded
  obtain ⟨cache, cached, getRan, rest⟩ := bind_ok rest
  rw [rawRun_get] at getRan
  cases getRan
  obtain ⟨environment, environed, readRan, rest⟩ := bind_ok rest
  have readEq : rawRun (read : CompileM (CompileEnv × BlockEnv)) context middle = (.ok context, middle) := rfl
  rw [readEq] at readRan
  cases readRan
  try dsimp only at rest
  cases built : buildCompiledMutualBlock context.1.sharingLimits classes members metadata middle with
  | error error => rw [built] at rest; cases rest
  | ok result =>
    rw [built, rawRun_pure] at rest
    obtain ⟨values, states⟩ := Prod.mk.inj rest
    cases Except.ok.inj values
    exact ⟨states.symm, bounds, rfl⟩

theorem mutual_class_capacity (sources : List (List MutConst))
    (nonempty : ∀ members ∈ sources, members ≠ []) :
    Emission.Yields (compileMutualPayload sources) (fun _ => sources.length < UInt64.size) := by
  intro context before output after ran
  unfold compileMutualPayload at ran
  obtain ⟨compiled, middle, first, last⟩ := bind_ok ran
  have count := payload_count sources nonempty context before compiled middle first
  obtain ⟨_, bounded, _⟩ := finish_mutual_ok context sources compiled.1 compiled.2.2 last
  exact count ▸ bounded.1

/-- A successful mutual block is entered through its plan-head audit, then
the block's mutual context and preseed. -/
theorem mutual_block (post : BlockResult → Prop) (sources : List (List MutConst))
    (payload : Emission.Yields (compileMutualPayload sources) post) :
    Emission.Yields (compileMutualBlock sources) post := by
  unfold compileMutualBlock withMutCtx
  exact Emission.Yields.bindAny _ fun _ => Emission.Yields.withBlockEnv _
    (Emission.Yields.bindAny (preseedExprTables (mutualPreseedExprs sources)) fun _ => payload)

theorem mutual_block_capacity (sources : List (List MutConst))
    (nonempty : ∀ members ∈ sources, members ≠ []) :
    Emission.Yields (compileMutualBlock sources) (fun _ => sources.length < UInt64.size) :=
  mutual_block _ sources (mutual_class_capacity sources nonempty)

theorem mutual_class_index (sources : List (List MutConst))
    (nonempty : ∀ members ∈ sources, members ≠ []) (context : CompileEnv × BlockEnv)
    (before after : BlockState) (output : BlockResult)
    (ran : rawRun (compileMutualBlock sources) context before = (.ok output, after))
    (index : Nat) (inside : index < sources.length) : index.toUInt64.toNat = index :=
  Emission.exact_header index
    (Nat.lt_trans inside (mutual_block_capacity sources nonempty context before output after ran))

/-! ## The class sort leaves no empty class -/

/-- `sortClasses`'s guard: every class it returns is non-empty. -/
theorem sorted_nonempty (rules : Ix.Compile.Canon.Rules) (addresses : Ix.Name → Option Address)
    (sources : List MutConst) (classes : List (List MutConst)) (stats : Ix.Compile.Canon.SortStats)
    (ran : Ix.Compile.Canon.sortClasses rules addresses sources = .ok (classes, stats)) :
    ∀ members ∈ classes, members ≠ [] := by
  unfold Ix.Compile.Canon.sortClasses at ran
  split at ran
  · cases Except.ok.inj ran
    simp
  · simp only [bind, Except.bind] at ran
    split at ran
    · contradiction
    · split at ran
      · contradiction
      · split at ran
        · contradiction
        · have equal := Except.ok.inj ran
          cases equal
          simp_all [List.any_eq_true]
          intro members present equal
          subst members
          contradiction

theorem throwCmpError_fails (error : Ix.Compile.Canon.CmpError) (context : CompileEnv × BlockEnv)
    (state : BlockState) : ∃ failure, (rawRun (throwCmpError error : CompileM α) context state).1 = .error failure := by
  cases error <;> exact ⟨_, rfl⟩

/-- **The compiler's class sort returns no empty class.** -/
theorem sort_nonempty (sources : List MutConst) :
    Emission.Yields (sortConsts sources) (fun classes => ∀ members ∈ classes, members ≠ []) := by
  intro context before output after ran
  unfold sortConsts at ran
  dsimp only at ran
  split at ran
  · obtain ⟨_, _, thrown, _⟩ := bind_ok ran
    rw [rawRun_throw] at thrown
    cases thrown
  obtain ⟨addresses, middle', _, tail⟩ := bind_ok ran
  cases sorted : Ix.Compile.Canon.sortClasses Ix.Compile.Canon.Rules.compiler addresses sources with
  | error reason =>
    rw [sorted] at tail
    obtain ⟨failure, failed⟩ := throwCmpError_fails (α := List (List MutConst)) reason context middle'
    dsimp only at tail
    rw [tail] at failed
    cases failed
  | ok pair =>
    rw [sorted] at tail
    dsimp only at tail
    rw [rawRun_pure] at tail
    have equal := Except.ok.inj (congrArg Prod.fst tail)
    cases equal
    exact sorted_nonempty _ addresses sources pair.1 pair.2 sorted

theorem constAddrLookup_run (context : CompileEnv × BlockEnv) (state : BlockState) :
    ∃ addresses, rawRun constAddrLookup context state = (.ok addresses, state) := ⟨_, rfl⟩

/-- **The compiler's class sort is `sortClasses Rules.compiler`**, run on an
address map of the state, and leaves the state as it found it (R9b). -/
theorem sort_run (sources : List MutConst) {context : CompileEnv × BlockEnv} {before after : BlockState}
    {classes : List (List MutConst)} (ran : rawRun (sortConsts sources) context before = (.ok classes, after)) :
    after = before ∧ ∃ addresses stats,
      Ix.Compile.Canon.sortClasses Ix.Compile.Canon.Rules.compiler addresses sources = .ok (classes, stats) := by
  unfold sortConsts at ran
  dsimp only at ran
  split at ran
  · obtain ⟨_, _, thrown, _⟩ := bind_ok ran
    rw [rawRun_throw] at thrown
    cases thrown
  obtain ⟨addresses, middle, looked, tail⟩ := bind_ok ran
  obtain ⟨addresses', looked'⟩ := constAddrLookup_run context before
  rw [looked'] at looked
  cases looked
  cases sorted : Ix.Compile.Canon.sortClasses Ix.Compile.Canon.Rules.compiler addresses sources with
  | error reason =>
    rw [sorted] at tail
    obtain ⟨failure, failed⟩ := throwCmpError_fails (α := List (List MutConst)) reason context before
    dsimp only at tail
    rw [tail] at failed
    cases failed
  | ok pair =>
    rw [sorted] at tail
    dsimp only at tail
    rw [rawRun_pure] at tail
    cases tail
    exact ⟨rfl, addresses, pair.2, sorted⟩

/-! ## Member shapes -/

/-- The fields checked when a projection resolves its owning mutual member. -/
inductive MemberShape where
  | defn
  | indc (indices : List Nat)
  | recr
  deriving DecidableEq

def memberShape : Ixon.MutConst → MemberShape
  | .defn _ => .defn
  | .indc value => .indc (value.ctors.toList.map (fun ctor => ctor.cidx.toNat))
  | .recr _ => .recr

def sourceShape : MutConst → MemberShape
  | .defn _ => .defn
  | .indc value => .indc (value.ctors.toList.map (·.cidx))
  | .recr _ => .recr

theorem finish_inductive_layout (source : InductiveVal) (type : Ixon.Expr) (root : UInt64)
    (metadata : InductiveTypeCompileMeta) (constructors : InductiveConstructorCompileState) :
    Emission.Yields (finishInductiveCompilation source type root metadata constructors)
      (fun output => output.1.ctors = constructors.ctors ∧ output.2.2.1 = constructors.ctorMetaPairs) := by
  unfold finishInductiveCompilation
  with_reducible repeat' first
    | exact Emission.Yields.pure ⟨rfl, rfl⟩
    | refine Emission.Yields.bindAny _ (fun _ => ?_)

theorem finish_inductiveData_layout (source : Ix.Ind) (type : Ixon.Expr) (root : UInt64)
    (metadata : InductiveTypeCompileMeta) (constructors : InductiveConstructorCompileState) :
    Emission.Yields (finishInductiveDataCompilation source type root metadata constructors)
      (fun output => output.1.ctors = constructors.ctors ∧ output.2.2.1 = constructors.ctorMetaPairs) := by
  unfold finishInductiveDataCompilation
  with_reducible repeat' first
    | exact Emission.Yields.pure ⟨rfl, rfl⟩
    | refine Emission.Yields.bindAny _ (fun _ => ?_)

/-- A compiled inductive's header fields, as natural numbers, are its
source's, and its constructor count fits the wire. -/
def IndHeader (source : Ix.Ind) (target : Ixon.Inductive) : Prop :=
  target.lvls.toNat = source.levelParams.size ∧ target.params.toNat = source.numParams ∧
    target.indices.toNat = source.numIndices ∧ target.ctors.size < UInt64.size

/-- **The inductive emitter keeps the source's headers**: the inductive's,
every constructor's in source order, and the constructors' registration
names. -/
theorem inductiveData_headers (source : Ix.Ind) :
    Emission.Yields (compileInductiveData source) (fun output =>
      IndHeader source output.1 ∧ List.Forall₂ CtorHeader source.ctors.toList output.1.ctors.toList ∧
        output.2.2.1.toList.map Prod.fst = source.ctors.toList.map (·.cnst.name)) := by
  unfold compileInductiveData
  refine Emission.Yields.withCurrent _ (Emission.Yields.withUnivCtx _
    (Emission.Yields.bindAny _ fun _ => Emission.Yields.bindAny _ fun typed => ?_))
  obtain ⟨typeExpr, typeRoot⟩ := typed
  dsimp only
  refine Emission.Yields.bindAny _ fun metadata => Emission.Yields.bind (constructors_headers source.ctors.toList
    { ctorExprs := #[typeExpr] }) fun compiled layout => ?_
  intro context before output after ran
  have header := Emission.inductiveDataHeader source typeExpr typeRoot metadata compiled context before output after ran
  have shape := finish_inductiveData_layout source typeExpr typeRoot metadata compiled context before output after ran
  obtain ⟨targets, ctors, headers, names⟩ := layout
  refine ⟨header, ?_, ?_⟩
  · rw [shape.1, ctors]
    simpa using headers
  · rw [shape.2, names]
    simp

theorem inductiveData_layout (source : Ix.Ind) :
    Emission.Yields (compileInductiveData source) (fun output =>
      output.1.ctors.toList.map (fun ctor => ctor.cidx.toNat) = source.ctors.toList.map (·.cidx) ∧
      output.2.2.1.toList.map Prod.fst = source.ctors.toList.map (·.cnst.name)) := by
  intro context before output after ran
  obtain ⟨_, headers, names⟩ := inductiveData_headers source context before output after ran
  exact ⟨headers_indices headers, names⟩

theorem inductive_layout (source : InductiveVal) (constructors : Array ConstructorVal) :
    Emission.Yields (compileInductive source constructors) (fun output =>
      output.1.ctors.toList.map (fun ctor => ctor.cidx.toNat) = constructors.toList.map (·.cidx) ∧
      output.2.2.1.toList.map Prod.fst = constructors.toList.map (·.cnst.name)) := by
  rw [Emission.compileInductive_eq]
  exact inductiveData_layout (Emission.sourceData source constructors)

theorem member_shape (source : MutConst) : Emission.Yields (compileMutConstMember source)
    (fun output => memberShape output.payload = sourceShape source) := by
  cases source with
  | defn value =>
    exact Emission.Yields.bindAny _ fun _ => Emission.Yields.pure rfl
  | recr value =>
    exact Emission.Yields.bindAny _ fun _ => Emission.Yields.pure rfl
  | indc value =>
    exact Emission.Yields.bind (Emission.Yields.withCurrent value.name (inductiveData_layout value))
      fun compiled layout => Emission.Yields.pure (congrArg MemberShape.indc layout.1)

theorem equivalents_payloads (sources : List MutConst) (initial : MutConstCompileState) :
    Emission.Yields (compileEquivalentMutConsts sources initial)
      (fun output => output.payloads = initial.payloads) := by
  induction sources generalizing initial with
  | nil => exact Emission.Yields.pure rfl
  | cons source rest ih =>
    rw [compileEquivalentMutConsts]
    exact Emission.Yields.bindAny _ fun member => ih (initial.addEquivalent member)

theorem class_shapes (sources : List MutConst) (initial : MutConstCompileState) :
    Emission.Yields (compileMutConstClass sources initial) (fun output =>
      output.payloads.toList.map memberShape = initial.payloads.toList.map memberShape ++
        sources.head?.toList.map sourceShape) := by
  cases sources with
  | nil => exact Emission.Yields.pure (by simp)
  | cons source rest =>
    rw [compileMutConstClass]
    exact Emission.Yields.bind (member_shape source) fun member shape =>
      fun context before output after ran => by
        have same := equivalents_payloads rest (initial.addRepresentative member) context before output after ran
        simp [same, MutConstCompileState.addRepresentative, shape]

theorem classes_shapes (sources : List (List MutConst)) (initial : MutConstCompileState) :
    Emission.Yields (compileMutConstClasses sources initial) (fun output =>
      output.payloads.toList.map memberShape = initial.payloads.toList.map memberShape ++
        (sources.filterMap List.head?).map sourceShape) := by
  induction sources generalizing initial with
  | nil => exact Emission.Yields.pure (by simp)
  | cons source rest ih =>
    intro context before output after ran
    rw [compileMutConstClasses] at ran
    obtain ⟨middle, state, firstRun, lastRun⟩ := bind_ok ran
    have first := class_shapes source initial context before middle state firstRun
    have last := ih middle context state output after lastRun
    cases source <;> simpa [first, List.append_assoc, List.filterMap] using last

/-- **The retained payloads have the representatives' shapes**, one per
non-empty class, in class order. -/
theorem payload_shapes (sources : List (List MutConst)) : Emission.Yields (compileMutConsts sources)
    (fun output => output.1.toList.map memberShape = (sources.filterMap List.head?).map sourceShape) := by
  unfold compileMutConsts
  exact Emission.Yields.bind (classes_shapes sources {}) fun compiled shape =>
    Emission.Yields.pure (by simpa using shape)

/-! ## The write-back keeps shapes -/

theorem memberShape_erase (member : Ixon.MutConst) :
    memberShape (SharingRoots.eraseMut member) = memberShape member := by
  cases member <;>
    simp [memberShape, SharingRoots.eraseMut, Ix.Sharing.Exact.mapMutConstRoots, Function.comp_def]

def blockShape : Ixon.ConstantInfo → Option (List MemberShape)
  | .defn _ => some [.defn]
  | .recr _ => some [.recr]
  | .muts members => some (members.toList.map memberShape)
  | _ => none

theorem blockShape_erase (info : Ixon.ConstantInfo) :
    blockShape (SharingRoots.erase info) = blockShape info := by
  cases info with
  | muts members =>
    have each : ∀ member ∈ members.toList,
        memberShape (Ix.Sharing.Exact.mapMutConstRoots (fun _ => Ixon.Expr.sort 0) member) = memberShape member :=
      fun member _ => memberShape_erase member
    simp only [blockShape, SharingRoots.erase, Ix.Sharing.Exact.mapRoots, Array.toList_map, List.map_map,
      Option.some.injEq]
    exact List.map_congr_left each
  | _ => rfl

/-- Replacing shared expression roots preserves the member kind and every
constructor index consulted by the anonymous reference resolver. -/
theorem writeback_member_shape (source target : Ixon.MutConst) (roots rest : List Ixon.Expr)
    (ran : Ix.Sharing.Exact.withMutConstRoots source roots = .ok (target, rest)) :
    memberShape target = memberShape source := by
  rw [← memberShape_erase target, (SharingRoots.withMutConstRoots_inv ran).2, memberShape_erase]

theorem writeback_shape (source target : Ixon.ConstantInfo) (roots : Array Ixon.Expr)
    (ran : Ix.Sharing.Exact.withRoots source roots = .ok target) :
    blockShape target = blockShape source := by
  rw [← blockShape_erase target, (SharingRoots.withRoots_inv ran).2, blockShape_erase]

theorem erase_muts {info : Ixon.ConstantInfo} {sources : Array Ixon.MutConst}
    (same : SharingRoots.erase info = SharingRoots.erase (.muts sources)) :
    ∃ targets, info = .muts targets := by
  cases info with
  | muts targets => exact ⟨targets, rfl⟩
  | _ => cases same

theorem writeback_mutual_shape (sources : Array Ixon.MutConst) (roots : Array Ixon.Expr)
    (info : Ixon.ConstantInfo)
    (ran : Ix.Sharing.Exact.withRoots (.muts sources) roots = .ok info) :
    ∃ targets, info = .muts targets ∧ targets.toList.map memberShape = sources.toList.map memberShape := by
  obtain ⟨targets, rfl⟩ := erase_muts (SharingRoots.withRoots_inv ran).2
  exact ⟨targets, rfl, Option.some.inj (writeback_shape _ _ roots ran)⟩

/-- **The sharing build keeps the block's shape.** -/
theorem sharing_shape (limits : Ix.Sharing.Exact.Limits) (source : Ixon.ConstantInfo)
    (refs : Array Address) (univs : Array Ixon.Univ) (block : Ixon.Constant)
    (ran : buildConstantWithSharing limits source refs univs = .ok block) :
    blockShape block.info = blockShape source := by
  rw [← blockShape_erase block.info, (SharingRoots.build_roots (md := .anon) limits source refs univs block ran).1,
    blockShape_erase]

theorem sharing_mutual_shape (limits : Ix.Sharing.Exact.Limits) (sources : Array Ixon.MutConst)
    (refs : Array Address) (univs : Array Ixon.Univ) (block : Ixon.Constant)
    (ran : buildConstantWithSharing limits (.muts sources) refs univs = .ok block) :
    ∃ targets, block.info = .muts targets ∧ targets.toList.map memberShape = sources.toList.map memberShape := by
  obtain ⟨targets, info⟩ := erase_muts (SharingRoots.build_roots (md := .anon) limits _ refs univs block ran).1
  refine ⟨targets, info, ?_⟩
  have same := sharing_shape limits _ refs univs block ran
  rw [info] at same
  exact Option.some.inj same

/-! ## Block shapes -/

theorem standalone_shape (members : Array Ixon.MutConst) (info : Ixon.ConstantInfo)
    (chosen : standaloneMutConstInfo? members = some info) :
    blockShape info = some (members.toList.map memberShape) := by
  rcases members with ⟨members⟩
  cases members with
  | nil => change (none : Option Ixon.ConstantInfo) = some info at chosen; cases chosen
  | cons member rest =>
    cases rest with
    | cons next rest => change (none : Option Ixon.ConstantInfo) = some info at chosen; cases chosen
    | nil =>
      cases member with
      | defn value =>
        change some (Ixon.ConstantInfo.defn value) = some info at chosen
        cases Option.some.inj chosen
        rfl
      | indc value => change (none : Option Ixon.ConstantInfo) = some info at chosen; cases chosen
      | recr value =>
        change some (Ixon.ConstantInfo.recr value) = some info at chosen
        cases Option.some.inj chosen
        rfl

theorem build_mutual_shape (limits : Ix.Sharing.Exact.Limits) (classes : List (List MutConst))
    (members : Array Ixon.MutConst) (metadata : Array (Ix.Name × Ixon.ConstantMeta)) (state : BlockState)
    (output : BlockResult) (ran : buildCompiledMutualBlock limits classes members metadata state = .ok output) :
    blockShape output.block.info = some (members.toList.map memberShape) := by
  unfold buildCompiledMutualBlock at ran
  cases chosen : standaloneMutConstInfo? members with
  | some info =>
    simp only [chosen] at ran
    obtain ⟨block, built, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases Except.ok.inj returned
    exact (sharing_shape limits info state.refs state.univs block built).trans (standalone_shape members info chosen)
  | none =>
    simp only [chosen] at ran
    obtain ⟨block, built, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases Except.ok.inj returned
    exact sharing_shape limits (.muts members) state.refs state.univs block built

theorem finish_mutual_shape (classes : List (List MutConst)) (members : Array Ixon.MutConst)
    (metadata : Array (Ix.Name × Ixon.ConstantMeta)) :
    Emission.Yields (finishMutualCompilation classes members metadata)
      (fun output => blockShape output.block.info = some (members.toList.map memberShape)) := by
  intro context before output after ran
  obtain ⟨rfl, _, built⟩ := finish_mutual_ok context classes members metadata ran
  exact build_mutual_shape _ classes members metadata _ output built

theorem mutual_shape (sources : List (List MutConst)) : Emission.Yields (compileMutualPayload sources)
    (fun output => blockShape output.block.info = some ((sources.filterMap List.head?).map sourceShape)) := by
  intro context before output after ran
  unfold compileMutualPayload at ran
  obtain ⟨compiled, middle, first, last⟩ := bind_ok ran
  have shape := payload_shapes sources context before compiled middle first
  exact (finish_mutual_shape sources compiled.1 compiled.2.2 context middle output after last).trans
    (congrArg some shape)

/-- **A mutual block has one member per class, with its representative's
kind and constructor positions** (or collapses to a lone definition or
recursor). -/
theorem mutual_block_shape (sources : List (List MutConst)) : Emission.Yields (compileMutualBlock sources)
    (fun output => blockShape output.block.info = some ((sources.filterMap List.head?).map sourceShape)) :=
  mutual_block _ sources (mutual_shape sources)

/-! ## The standalone family -/

theorem singleton_inductive_shape (members : Array Ixon.MutConst) (indices : List Nat)
    (shape : members.toList.map memberShape = [.indc indices]) :
    ∃ target, members = #[.indc target] ∧ target.ctors.toList.map (fun ctor => ctor.cidx.toNat) = indices := by
  rcases members with ⟨members⟩
  cases members with
  | nil => simp at shape
  | cons member rest =>
    cases rest with
    | cons next rest => simp at shape
    | nil =>
      cases member with
      | defn value | recr value => simp [memberShape] at shape
      | indc value =>
        exact ⟨value, rfl, by simpa [memberShape] using shape⟩

theorem shared_inductive_shape (limits : Ix.Sharing.Exact.Limits) (source : Ixon.Inductive)
    (refs : Array Address) (univs : Array Ixon.Univ) (block : Ixon.Constant)
    (ran : buildConstantWithSharing limits (.muts #[.indc source]) refs univs = .ok block) :
    ∃ target, block.info = .muts #[.indc target] ∧
      target.ctors.toList.map (fun ctor => ctor.cidx.toNat) =
        source.ctors.toList.map (fun ctor => ctor.cidx.toNat) := by
  obtain ⟨members, info, shape⟩ := sharing_mutual_shape limits #[.indc source] refs univs block ran
  obtain ⟨target, rfl, indices⟩ := singleton_inductive_shape members
    (source.ctors.toList.map (fun ctor => ctor.cidx.toNat)) (by simpa [memberShape] using shape)
  exact ⟨target, info, indices⟩

/-- The family finisher's guard bounds the projection count. -/
theorem familyFinish_pairs (source : InductiveVal) (ind : Ixon.Inductive) (indMeta : Ixon.ConstantMeta)
    (pairs : Array (Ix.Name × Ixon.ConstantMeta)) :
    Emission.Yields (finishInductiveFamilyBlock source ind indMeta pairs) (fun _ => pairs.size < UInt64.size) := by
  unfold finishInductiveFamilyBlock
  exact Emission.Yields.bindAny _ fun _ => Emission.Yields.bind (Emission.Yields.count _ _) fun _ bounded =>
    Emission.Yields.bindAny _ fun _ => Emission.Yields.bindAny _ fun _ => Emission.Yields.pure bounded

theorem finish_inductive_shape (source : InductiveVal) (ind : Ixon.Inductive) (metadata : Ixon.ConstantMeta)
    (constructors : Array (Ix.Name × Ixon.ConstantMeta)) :
    Emission.Yields (finishInductiveFamilyBlock source ind metadata constructors)
      (fun output => ∃ target, output.block.info = .muts #[.indc target] ∧
        target.ctors.toList.map (fun ctor => ctor.cidx.toNat) = ind.ctors.toList.map (fun ctor => ctor.cidx.toNat) ∧
        output.projections = buildInductiveProjections source metadata constructors output.blockAddr) := by
  intro context before output after ran
  obtain ⟨_, built, wrapped⟩ := EmissionBlocks.familyFinish_ok source ind metadata constructors ran
  obtain ⟨target, info, indices⟩ := shared_inductive_shape context.1.sharingLimits ind before.refs before.univs
    output.block built
  refine ⟨target, info, indices, ?_⟩
  rw [wrapped]
  rfl

/-- The emitted standalone family retains source constructor positions and
registration keys. Metadata values remain uninterpreted. -/
def InductiveLayout (source : InductiveVal) (constructors : Array ConstructorVal) (output : BlockResult) : Prop :=
  ∃ target metadata pairs, output.block.info = .muts #[.indc target] ∧
    target.ctors.toList.map (fun ctor => ctor.cidx.toNat) = constructors.toList.map (·.cidx) ∧
    pairs.toList.map Prod.fst = constructors.toList.map (·.cnst.name) ∧
    pairs.size < UInt64.size ∧
    output.projections = buildInductiveProjections source metadata pairs output.blockAddr

theorem family_layout (source : InductiveVal) (constructors : Array ConstructorVal) :
    Emission.Yields (compileInductiveFamilyBlock source constructors) (InductiveLayout source constructors) := by
  intro context before output after ran
  unfold compileInductiveFamilyBlock at ran
  obtain ⟨compiled, middle, first, last⟩ := bind_ok ran
  have sourceLayout := inductive_layout source constructors context before compiled middle first
  obtain ⟨target, info, indices, projections⟩ := finish_inductive_shape source compiled.1 compiled.2.1
    compiled.2.2.1 context middle output after last
  have bound := familyFinish_pairs source compiled.1 compiled.2.1 compiled.2.2.1 context middle output after last
  exact ⟨target, compiled.2.1, compiled.2.2.1, info, indices.trans sourceLayout.1, sourceLayout.2, bound,
    projections⟩

theorem familyInfo_layout (source : InductiveVal) (constructors : Array ConstructorVal) :
    Emission.Yields (compileInductiveFamilyInfo source constructors) (InductiveLayout source constructors) := by
  unfold compileInductiveFamilyInfo
  exact Emission.Yields.bindAny _ fun _ => family_layout source constructors

/-- **Public dispatch of an inductive** returns its standalone family's
layout, over the constructors the dispatch resolves. -/
theorem dispatch_layout (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (source : InductiveVal) {before after : BlockState} {output : BlockResult}
    (ran : rawRun (compileConstantInfo (.inductInfo source)) context before = (.ok output, after)) :
    ∃ constructors, rawRun (lookupInductiveConstructors source)
        (EmissionDispatch.singletonContext source.cnst.name context) before = (.ok constructors, before) ∧
      InductiveLayout source constructors output := by
  rw [EmissionDispatch.inductive_run context free] at ran
  obtain ⟨constructors, found, compiled⟩ :=
    EmissionDispatch.family_run (EmissionDispatch.singletonContext source.cnst.name context) free source ran
  exact ⟨constructors, found, familyInfo_layout source constructors _ before output after compiled⟩

/-! ## The family's projections resolve -/

open Ix.Kernel.Reader (Store resolveSource emptyTables)

theorem inductive_projection_resolves (source : InductiveVal) (constructors : Array ConstructorVal)
    (output : BlockResult) (layout : InductiveLayout source constructors output)
    (store : Store) (stored : store output.blockAddr = some output.block) :
    ∃ projection metadata,
      output.projections[0]? = some (source.cnst.name, projection, metadata) ∧
      resolveSource store (Address.admissionHash (Ixon.ser projection)) projection =
        some (.member output.blockAddr 0) := by
  obtain ⟨target, metadata, pairs, info, _, _, _, projections⟩ := layout
  let projection : Ixon.Constant := ⟨.iPrj ⟨0, output.blockAddr⟩, #[], #[], #[]⟩
  refine ⟨projection, metadata, ?_, ?_⟩
  · simp [projections, buildInductiveProjections, projection, Array.getElem?_append]
  · simp [projection, resolveSource, emptyTables, stored, info, guard]

private theorem mapped_index {xs : Array α} {ys : Array β} {left : α → γ} {right : β → γ}
    (same : xs.toList.map left = ys.toList.map right) (index : Nat)
    (insideLeft : index < xs.size) (insideRight : index < ys.size) :
    left xs[index] = right ys[index] := by
  have row := congrArg (fun values : List γ => values[index]?) same
  simp only [List.getElem?_map, Array.getElem?_toList] at row
  rw [Array.getElem?_eq_getElem insideLeft, Array.getElem?_eq_getElem insideRight] at row
  exact Option.some.inj row

/-- A generated constructor projection resolves to the source position when
the source constructor declares that position. -/
theorem constructor_projection_resolves (source : InductiveVal) (constructors : Array ConstructorVal)
    (output : BlockResult) (layout : InductiveLayout source constructors output)
    (store : Store) (stored : store output.blockAddr = some output.block)
    (index : Nat) (inside : index < constructors.size) (sourceIndex : constructors[index].cidx = index) :
    ∃ projection metadata,
      output.projections[index + 1]? = some (constructors[index].cnst.name, projection, metadata) ∧
      resolveSource store (Address.admissionHash (Ixon.ser projection)) projection =
        some (.ctor output.blockAddr 0 index) := by
  obtain ⟨target, metadata, pairs, info, indices, names, bound, projections⟩ := layout
  have targetLength : target.ctors.size = constructors.size := by
    simpa using congrArg List.length indices
  have pairLength : pairs.size = constructors.size := by
    simpa using congrArg List.length names
  have targetInside : index < target.ctors.size := by omega
  have pairInside : index < pairs.size := by omega
  have sameName := mapped_index names index pairInside inside
  have naturalIndex := (mapped_index indices index targetInside inside).trans sourceIndex
  have exactIndex : index.toUInt64.toNat = index := Emission.exact_header index (Nat.lt_trans pairInside bound)
  have converted : target.ctors[index].cidx = index.toUInt64 := UInt64.toNat_inj.mp (naturalIndex.trans exactIndex.symm)
  let projection : Ixon.Constant := ⟨.cPrj ⟨0, index.toUInt64, output.blockAddr⟩, #[], #[], #[]⟩
  refine ⟨projection, pairs[index].2, ?_, ?_⟩
  · rw [projections]
    simp only [buildInductiveProjections]
    rw [Array.getElem?_append_right (by simp)]
    simp [Array.getElem?_eq_getElem pairInside, sameName, projection]
  · simp [projection, resolveSource, emptyTables, stored, info,
      exactIndex, Array.getElem?_eq_getElem targetInside, converted, guard]

end Ix.CompileCert.ProjectionLayout
