import Ix.CompileCert.FamilyWire

/-! Source positions retained by the actual constructor/mutual folds and
sharing. Standalone inductive projections resolve through the anonymous kernel
reader under explicit store and source-index conditions. Full source typing,
equivalent-member correspondence and declaration admission remain separate. -/

namespace Ix.CompileCert.ProjectionLayout

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame
open DeclarationHeaders (Returns)

theorem constructor_index (source : ConstructorVal) :
    Returns (compileConstructor source) (fun output => output.1.cidx.toNat = source.cidx) := by
  apply PayloadArrays.Returns.withCurrent
  exact Returns.bindAny _ fun _ => Returns.bindAny _ fun type =>
    fun context before output after ran =>
      (DeclarationHeaders.constructorHeader source type.1 type.2 context before output after ran).2.1

theorem constructors_layout (sources : List ConstructorVal) (initial : InductiveConstructorCompileState) :
    Returns (compileInductiveConstructors sources initial) (fun output =>
      output.ctors.toList.map (fun ctor => ctor.cidx.toNat) =
        initial.ctors.toList.map (fun ctor => ctor.cidx.toNat) ++ sources.map (·.cidx) ∧
      output.ctorMetaPairs.toList.map Prod.fst =
        initial.ctorMetaPairs.toList.map Prod.fst ++ sources.map (·.cnst.name)) := by
  induction sources generalizing initial with
  | nil => exact Returns.pure (by simp)
  | cons source rest ih =>
    intro context before output after ran
    rw [compileInductiveConstructors] at ran
    obtain ⟨compiled, middle, first, last⟩ := PreseedReferences.bind_ok _ _ context before output after ran
    have index := constructor_index source context before compiled middle first
    have tail := ih {
      ctors := initial.ctors.push compiled.1
      ctorMetaPairs := initial.ctorMetaPairs.push (source.cnst.name, compiled.2.1)
      ctorNameAddrs := initial.ctorNameAddrs.push source.cnst.name.getHash
      ctorExprs := initial.ctorExprs.push compiled.2.2 } context middle output after last
    simpa [List.append_assoc, index] using tail

theorem equivalents_count (sources : List MutConst) (initial : MutConstCompileState) :
    Returns (compileEquivalentMutConsts sources initial)
      (fun output => output.payloads.size = initial.payloads.size) := by
  induction sources generalizing initial with
  | nil => exact Returns.pure rfl
  | cons source rest ih =>
    rw [compileEquivalentMutConsts]
    exact Returns.bindAny _ fun member => ih (initial.addEquivalent member)

theorem class_count (sources : List MutConst) (initial : MutConstCompileState) :
    Returns (compileMutConstClass sources initial)
      (fun output => output.payloads.size = initial.payloads.size + if sources.isEmpty then 0 else 1) := by
  cases sources with
  | nil => exact Returns.pure (by simp)
  | cons source rest =>
    rw [compileMutConstClass]
    apply Returns.bindAny
    intro member
    simpa [MutConstCompileState.addRepresentative] using equivalents_count rest (initial.addRepresentative member)

theorem classes_count (sources : List (List MutConst)) (initial : MutConstCompileState) :
    Returns (compileMutConstClasses sources initial)
      (fun output => output.payloads.size = initial.payloads.size +
        (sources.filter fun members => !members.isEmpty).length) := by
  induction sources generalizing initial with
  | nil => exact Returns.pure (by simp)
  | cons source rest ih =>
    intro context before output after ran
    rw [compileMutConstClasses] at ran
    obtain ⟨middle, state, firstRun, lastRun⟩ := PreseedReferences.bind_ok _ _ context before output after ran
    have first := class_count source initial context before middle state firstRun
    have last := ih middle context state output after lastRun
    cases source <;> simp_all
    omega

theorem payload_count (sources : List (List MutConst))
    (nonempty : ∀ members ∈ sources, members ≠ []) :
    Returns (compileMutConsts sources) (fun output => output.1.size = sources.length) := by
  have filtered : (sources.filter fun members => !members.isEmpty) = sources := by
    apply List.filter_eq_self.mpr
    intro members present
    cases members with
    | nil => exact False.elim (nonempty [] present rfl)
    | cons _ _ => rfl
  exact Returns.bind (classes_count sources {}) fun compiled count =>
    Returns.pure (by simpa [filtered] using count)

theorem mutual_class_capacity (sources : List (List MutConst))
    (nonempty : ∀ members ∈ sources, members ≠ []) :
    Returns (compileMutualPayload sources) (fun _ => sources.length < UInt64.size) := by
  intro context before output after ran
  rw [compileMutualPayload] at ran
  obtain ⟨compiled, middle, first, last⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have count := payload_count sources nonempty context before compiled middle first
  change rawRun (finishMutualCompilation sources compiled.1 compiled.2.2) context middle = (.ok output, after) at last
  rw [finishMutualCompilation] at last
  obtain ⟨done, next, checked, _⟩ := PreseedReferences.bind_ok _ _ context middle output after last
  have bounded := PayloadArrays.mutual_counts compiled.1 context middle done next checked
  exact count ▸ bounded.1

theorem sorted_nonempty (rules : Ix.Compile.Canon.Rules) (addresses : Name → Option Address)
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

theorem sort_nonempty (sources : List MutConst) : Returns (sortConsts sources)
    (fun classes => ∀ members ∈ classes, members ≠ []) := by
  intro context before output after ran
  rw [sortConsts, DefinitionBlock.rawRun_timedC, sortConstsCore] at ran
  obtain ⟨addresses, middle, _, tail⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  cases sorted : Ix.Compile.Canon.sortClasses Ix.Compile.Canon.Rules.compiler addresses sources with
  | error reason =>
    rw [sorted] at tail
    cases congrArg Prod.fst tail
  | ok pair =>
    rw [sorted, rawRun_pure] at tail
    have equal := Except.ok.inj (congrArg Prod.fst tail)
    cases equal
    exact sorted_nonempty _ addresses sources pair.1 pair.2 sorted

theorem ordered_nonempty (classes : List (List MutConst))
    (nonempty : ∀ members ∈ classes, members ≠ []) :
    ∀ members ∈ orderRecursorFamily classes, members ≠ [] := by
  intro members present
  unfold orderRecursorFamily at present
  split at present
  · exact nonempty members present
  · simp only [Array.mem_toList_iff, Array.mem_map] at present
    obtain ⟨entry, sorted, rfl⟩ := present
    rw [Canon.mem_qsort] at sorted
    obtain ⟨pair, paired, rfl⟩ := Array.mem_map.mp sorted
    exact nonempty pair.1 (by simpa using Array.fst_mem_of_mem_zipIdx paired)

theorem mutual_block_capacity (sources : List (List MutConst))
    (nonempty : ∀ members ∈ sources, members ≠ []) :
    Returns (compileMutualBlock sources) (fun _ => sources.length < UInt64.size) := by
  unfold compileMutualBlock withMutCtx
  exact PayloadArrays.Returns.withBlockEnv (fun context => { context with mutCtx := MutConst.ctx sources })
    (Returns.bindAny (preseedExprTables (mutualPreseedExprs sources)) fun _ => mutual_class_capacity sources nonempty)

theorem mutual_class_index (sources : List (List MutConst))
    (nonempty : ∀ members ∈ sources, members ≠ []) (context : CompileEnv × BlockEnv)
    (before after : BlockState) (output : BlockResult)
    (ran : rawRun (compileMutualBlock sources) context before = (.ok output, after))
    (index : Nat) (inside : index < sources.length) : index.toUInt64.toNat = index :=
  DeclarationHeaders.exact_header index
    (Nat.lt_trans inside (mutual_block_capacity sources nonempty context before output after ran))

/-- The fields checked when a projection resolves its owning mutual member. -/
inductive MemberShape where
  | defn
  | indc (indices : List Nat)
  | recr

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
    Returns (finishInductiveCompilation source type root metadata constructors)
      (fun output => output.1.ctors = constructors.ctors ∧ output.2.2.1 = constructors.ctorMetaPairs) := by
  unfold finishInductiveCompilation
  with_reducible repeat' first
    | exact Returns.pure ⟨rfl, rfl⟩
    | refine Returns.bindAny _ (fun _ => ?_)

theorem finish_inductiveData_layout (source : Ind) (type : Ixon.Expr) (root : UInt64)
    (metadata : InductiveTypeCompileMeta) (constructors : InductiveConstructorCompileState) :
    Returns (finishInductiveDataCompilation source type root metadata constructors)
      (fun output => output.1.ctors = constructors.ctors ∧ output.2.2.1 = constructors.ctorMetaPairs) := by
  unfold finishInductiveDataCompilation
  with_reducible repeat' first
    | exact Returns.pure ⟨rfl, rfl⟩
    | refine Returns.bindAny _ (fun _ => ?_)

theorem inductive_layout (source : InductiveVal) (constructors : Array ConstructorVal) :
    Returns (compileInductive source constructors) (fun output =>
      output.1.ctors.toList.map (fun ctor => ctor.cidx.toNat) = constructors.toList.map (·.cidx) ∧
      output.2.2.1.toList.map Prod.fst = constructors.toList.map (·.cnst.name)) := by
  apply PayloadArrays.Returns.withCurrent
  apply PayloadArrays.Returns.withUnivCtx
  exact Returns.bindAny _ fun _ => Returns.bindAny _ fun type => Returns.bindAny _ fun metadata =>
    Returns.bind (constructors_layout constructors.toList { ctorExprs := #[type.1] }) fun compiled layout =>
      fun context before output after ran => by
        have shape := finish_inductive_layout source type.1 type.2 metadata compiled context before output after ran
        rw [shape.1, shape.2]
        simpa using layout

theorem inductiveData_layout (source : Ind) :
    Returns (compileInductiveData source) (fun output =>
      output.1.ctors.toList.map (fun ctor => ctor.cidx.toNat) = source.ctors.toList.map (·.cidx) ∧
      output.2.2.1.toList.map Prod.fst = source.ctors.toList.map (·.cnst.name)) := by
  apply PayloadArrays.Returns.withCurrent
  apply PayloadArrays.Returns.withUnivCtx
  exact Returns.bindAny _ fun _ => Returns.bindAny _ fun type => Returns.bindAny _ fun metadata =>
    Returns.bind (constructors_layout source.ctors.toList { ctorExprs := #[type.1] }) fun compiled layout =>
      fun context before output after ran => by
        have shape := finish_inductiveData_layout source type.1 type.2 metadata compiled context before output after ran
        rw [shape.1, shape.2]
        simpa using layout

theorem member_shape (source : MutConst) : Returns (compileMutConstMember source)
    (fun output => memberShape output.payload = sourceShape source) := by
  cases source with
  | defn value =>
    exact Returns.bindAny _ fun _ => Returns.pure rfl
  | recr value =>
    exact Returns.bindAny _ fun _ => Returns.pure rfl
  | indc value =>
    exact Returns.bind (PayloadArrays.Returns.withCurrent value.name (inductiveData_layout value))
      fun compiled layout => Returns.pure (congrArg MemberShape.indc layout.1)

theorem equivalents_payloads (sources : List MutConst) (initial : MutConstCompileState) :
    Returns (compileEquivalentMutConsts sources initial)
      (fun output => output.payloads = initial.payloads) := by
  induction sources generalizing initial with
  | nil => exact Returns.pure rfl
  | cons source rest ih =>
    rw [compileEquivalentMutConsts]
    exact Returns.bindAny _ fun member => ih (initial.addEquivalent member)

theorem class_shapes (sources : List MutConst) (initial : MutConstCompileState) :
    Returns (compileMutConstClass sources initial) (fun output =>
      output.payloads.toList.map memberShape = initial.payloads.toList.map memberShape ++
        sources.head?.toList.map sourceShape) := by
  cases sources with
  | nil => exact Returns.pure (by simp)
  | cons source rest =>
    rw [compileMutConstClass]
    exact Returns.bind (member_shape source) fun member shape =>
      fun context before output after ran => by
        have same := equivalents_payloads rest (initial.addRepresentative member) context before output after ran
        simp [same, MutConstCompileState.addRepresentative, shape]

theorem classes_shapes (sources : List (List MutConst)) (initial : MutConstCompileState) :
    Returns (compileMutConstClasses sources initial) (fun output =>
      output.payloads.toList.map memberShape = initial.payloads.toList.map memberShape ++
        (sources.filterMap List.head?).map sourceShape) := by
  induction sources generalizing initial with
  | nil => exact Returns.pure (by simp)
  | cons source rest ih =>
    intro context before output after ran
    rw [compileMutConstClasses] at ran
    obtain ⟨middle, state, firstRun, lastRun⟩ := PreseedReferences.bind_ok _ _ context before output after ran
    have first := class_shapes source initial context before middle state firstRun
    have last := ih middle context state output after lastRun
    cases source <;> simpa [first, List.append_assoc, List.filterMap] using last

theorem payload_shapes (sources : List (List MutConst)) : Returns (compileMutConsts sources)
    (fun output => output.1.toList.map memberShape = (sources.filterMap List.head?).map sourceShape) :=
  Returns.bind (classes_shapes sources {}) fun compiled shape => Returns.pure (by simpa using shape)

/-- Replacing shared expression roots preserves the member kind and every
constructor index consulted by the anonymous reference resolver. -/
theorem writeback_member_shape (source target : Ixon.MutConst) (roots rest : List Ixon.Expr)
    (ran : Ix.Sharing.Exact.withMutConstRoots source roots = .ok (target, rest)) :
    memberShape target = memberShape source := by
  cases source with
  | defn value =>
    simp only [Ix.Sharing.Exact.withMutConstRoots] at ran
    obtain ⟨⟨type, next⟩, _, tail⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    obtain ⟨⟨body, last⟩, _, finished⟩ := Ix.Sharing.Verify.except_bind_eq_ok tail
    cases congrArg Prod.fst (Except.ok.inj finished)
    rfl
  | recr value =>
    simp only [Ix.Sharing.Exact.withMutConstRoots] at ran
    obtain ⟨⟨type, next⟩, _, tail⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    obtain ⟨⟨bodies, last⟩, _, finished⟩ := Ix.Sharing.Verify.except_bind_eq_ok tail
    cases congrArg Prod.fst (Except.ok.inj finished)
    rfl
  | indc value =>
    simp only [Ix.Sharing.Exact.withMutConstRoots] at ran
    obtain ⟨⟨type, next⟩, _, tail⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    obtain ⟨⟨types, last⟩, read, finished⟩ := Ix.Sharing.Verify.except_bind_eq_ok tail
    cases congrArg Prod.fst (Except.ok.inj finished)
    have length := (Ix.Sharing.Verify.takeRoots_eq_ok read).1
    simp only [memberShape, Array.toList_map, List.map_map]
    congr 1
    have first := List.map_fst_zip (l₁ := value.ctors.toList) (l₂ := types)
      (by simpa using Nat.le_of_eq length.symm)
    simpa only [List.map_map, Function.comp_def] using
      congrArg (fun ctors => ctors.map (fun ctor : Ixon.Constructor => ctor.cidx.toNat)) first

theorem writeback_mutual_shape (sources : Array Ixon.MutConst) (roots : Array Ixon.Expr)
    (info : Ixon.ConstantInfo)
    (ran : Ix.Sharing.Exact.withRoots (.muts sources) roots = .ok info) :
    ∃ targets, info = .muts targets ∧ targets.toList.map memberShape = sources.toList.map memberShape := by
  simp only [Ix.Sharing.Exact.withRoots] at ran
  split at ran
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at ran
  rw [← Array.forIn_toList] at ran
  obtain ⟨finalState, loopRan, finished⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
  have layout := Ix.Sharing.Verify.forIn_except_inv
    (fun (remaining : List Ixon.MutConst) (state : Array Ixon.MutConst × List Ixon.Expr) =>
      state.1.toList.map memberShape ++ remaining.map memberShape = sources.toList.map memberShape) _
    (by
      intro source remaining state step prior ran
      obtain ⟨⟨target, rest⟩, written, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
      simp only [pure, Except.pure, Except.ok.injEq] at returned
      have same := writeback_member_shape source target state.2 rest written
      refine ⟨_, returned.symm, ?_⟩
      simpa [List.append_assoc, same] using prior)
    sources.toList (#[], roots.toList) finalState (by simp) loopRan
  simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at finished
  exact ⟨finalState.1, (Ix.Sharing.Verify.withRoots_tail finished).symm, by simpa using layout⟩

theorem sharing_mutual_shape (limits : Ix.Sharing.Exact.Limits) (sources : Array Ixon.MutConst)
    (refs : Array Address) (univs : Array Ixon.Univ) (block : Ixon.Constant)
    (ran : buildConstantWithSharing limits (.muts sources) refs univs = .ok block) :
    ∃ targets, block.info = .muts targets ∧ targets.toList.map memberShape = sources.toList.map memberShape := by
  obtain ⟨shared, info, _, _, written, built⟩ := Ix.Sharing.Verify.buildConstantWithSharing_eq_ok ran
  unfold withRootExprs at written
  cases result : Ix.Sharing.Exact.withRoots (.muts sources) shared.result.roots with
  | error reason => simp [result, Except.mapError] at written
  | ok target =>
    simp only [result, Except.mapError, Except.ok.injEq] at written
    subst info
    subst block
    exact writeback_mutual_shape sources shared.result.roots target result

def blockShape : Ixon.ConstantInfo → Option (List MemberShape)
  | .defn _ => some [.defn]
  | .recr _ => some [.recr]
  | .muts members => some (members.toList.map memberShape)
  | _ => none

theorem writeback_shape (source target : Ixon.ConstantInfo) (roots : Array Ixon.Expr)
    (ran : Ix.Sharing.Exact.withRoots source roots = .ok target) :
    blockShape target = blockShape source := by
  cases source with
  | muts members =>
    obtain ⟨targets, rfl, shape⟩ := writeback_mutual_shape members roots target ran
    exact congrArg some shape
  | defn value =>
    simp only [Ix.Sharing.Exact.withRoots] at ran
    split at ran
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at ran
    obtain ⟨⟨member, rest⟩, _, tail⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases member with
    | defn value =>
      simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
      cases Ix.Sharing.Verify.withRoots_tail tail
      rfl
    | _ => simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at tail
  | recr value =>
    simp only [Ix.Sharing.Exact.withRoots] at ran
    split at ran
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at ran
    obtain ⟨⟨member, rest⟩, _, tail⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases member with
    | recr value =>
      simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
      cases Ix.Sharing.Verify.withRoots_tail tail
      rfl
    | _ => simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at tail
  | axio value | quot value =>
    simp only [Ix.Sharing.Exact.withRoots] at ran
    split at ran
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at ran
    obtain ⟨⟨type, rest⟩, _, tail⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
    cases Ix.Sharing.Verify.withRoots_tail tail
    rfl
  | cPrj value | rPrj value | iPrj value | dPrj value =>
    simp only [Ix.Sharing.Exact.withRoots] at ran
    split at ran
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at ran
    simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at ran
    cases Ix.Sharing.Verify.withRoots_tail ran
    rfl

theorem sharing_shape (limits : Ix.Sharing.Exact.Limits) (source : Ixon.ConstantInfo)
    (refs : Array Address) (univs : Array Ixon.Univ) (block : Ixon.Constant)
    (ran : buildConstantWithSharing limits source refs univs = .ok block) :
    blockShape block.info = blockShape source := by
  obtain ⟨shared, info, _, _, written, built⟩ := Ix.Sharing.Verify.buildConstantWithSharing_eq_ok ran
  unfold withRootExprs at written
  cases result : Ix.Sharing.Exact.withRoots source shared.result.roots with
  | error reason => simp [result, Except.mapError] at written
  | ok target =>
    simp only [result, Except.mapError, Except.ok.injEq] at written
    subst info
    subst block
    exact writeback_shape source target shared.result.roots result

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
    (members : Array Ixon.MutConst) (metadata : Array (Name × Ixon.ConstantMeta)) (state : BlockState)
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
    (metadata : Array (Name × Ixon.ConstantMeta)) : Returns (finishMutualCompilation classes members metadata)
      (fun output => blockShape output.block.info = some (members.toList.map memberShape)) := by
  intro context before output after ran
  unfold finishMutualCompilation at ran
  obtain ⟨done, middle, guarded, rest⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have same := PayloadArrays.mutual_state members context before
  rw [guarded] at same
  dsimp only at same
  subst middle
  have readContext : rawRun (read : CompileM (CompileEnv × BlockEnv)) context before = (.ok context, before) := rfl
  simp only [rawRun_bind, rawRun_get, readContext, Ix.PhaseTimers.withPhase,
    Ix.PhaseTimers.enterV, Ix.PhaseTimers.exitV, ite_self] at rest
  cases built : buildCompiledMutualBlock context.1.sharingLimits classes members metadata before with
  | error reason => rw [built] at rest; cases rest
  | ok result =>
    rw [built, rawRun_pure] at rest
    cases Except.ok.inj (congrArg Prod.fst rest)
    exact build_mutual_shape _ classes members metadata before output built

theorem mutual_shape (sources : List (List MutConst)) : Returns (compileMutualPayload sources)
    (fun output => blockShape output.block.info = some ((sources.filterMap List.head?).map sourceShape)) := by
  intro context before output after ran
  rw [compileMutualPayload] at ran
  obtain ⟨compiled, middle, first, last⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have shape := payload_shapes sources context before compiled middle first
  exact (finish_mutual_shape sources compiled.1 compiled.2.2 context middle output after last).trans (congrArg some shape)

theorem mutual_block_shape (sources : List (List MutConst)) : Returns (compileMutualBlock sources)
    (fun output => blockShape output.block.info = some ((sources.filterMap List.head?).map sourceShape)) := by
  unfold compileMutualBlock withMutCtx
  exact PayloadArrays.Returns.withBlockEnv (fun context => { context with mutCtx := MutConst.ctx sources })
    (Returns.bindAny (preseedExprTables (mutualPreseedExprs sources)) fun _ => mutual_shape sources)

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
      target.ctors.toList.map (fun ctor => ctor.cidx.toNat) = source.ctors.toList.map (fun ctor => ctor.cidx.toNat) := by
  obtain ⟨members, info, shape⟩ := sharing_mutual_shape limits #[.indc source] refs univs block ran
  obtain ⟨target, rfl, indices⟩ := singleton_inductive_shape members
    (source.ctors.toList.map (fun ctor => ctor.cidx.toNat)) (by simpa [memberShape] using shape)
  exact ⟨target, info, indices⟩

theorem finish_inductive_shape (source : InductiveVal) (ind : Ixon.Inductive) (metadata : Ixon.ConstantMeta)
    (constructors : Array (Name × Ixon.ConstantMeta)) : Returns (finishInductiveFamilyBlock source ind metadata constructors)
      (fun output => ∃ target, output.block.info = .muts #[.indc target] ∧
        target.ctors.toList.map (fun ctor => ctor.cidx.toNat) = ind.ctors.toList.map (fun ctor => ctor.cidx.toNat) ∧
        output.projections = buildInductiveProjections source metadata constructors output.blockAddr) := by
  intro context before output after ran
  unfold finishInductiveFamilyBlock at ran
  obtain ⟨count, middle, guarded, rest⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have same := Interning.checkedTableCount_state "inductive constructors" source.ctors.size context before
  rw [guarded] at same
  dsimp only at same
  subst middle
  obtain ⟨pairCount, middle, pairGuarded, rest⟩ := PreseedReferences.bind_ok _ _ context before output after rest
  have pairSame := Interning.checkedTableCount_state "constructor projections" constructors.size context before
  rw [pairGuarded] at pairSame
  dsimp only at pairSame
  subst middle
  rw [rawRun_bind, rawRun_get] at rest
  obtain ⟨block, finalState, built, returned⟩ := PreseedReferences.bind_ok _ _ context before output after rest
  rw [DefinitionBlock.rawRun_timedC, FamilyWire.build_block_run] at built
  have buildResult := congrArg Prod.fst built
  have buildState := congrArg Prod.snd built
  dsimp only at buildState
  subst finalState
  rw [rawRun_pure] at returned
  cases Except.ok.inj (congrArg Prod.fst returned)
  obtain ⟨target, info, indices⟩ := shared_inductive_shape context.1.sharingLimits ind before.refs before.univs block buildResult
  exact ⟨target, info, indices, rfl⟩

/-- The emitted standalone family retains source constructor positions and
registration keys. Metadata values remain uninterpreted. -/
def InductiveLayout (source : InductiveVal) (constructors : Array ConstructorVal) (output : BlockResult) : Prop :=
  ∃ target metadata pairs, output.block.info = .muts #[.indc target] ∧
    target.ctors.toList.map (fun ctor => ctor.cidx.toNat) = constructors.toList.map (·.cidx) ∧
    pairs.toList.map Prod.fst = constructors.toList.map (·.cnst.name) ∧
    pairs.size < UInt64.size ∧
    output.projections = buildInductiveProjections source metadata pairs output.blockAddr

theorem family_layout (source : InductiveVal) (constructors : Array ConstructorVal) :
    Returns (compileInductiveFamilyBlock source constructors) (InductiveLayout source constructors) := by
  intro context before output after ran
  rw [compileInductiveFamilyBlock] at ran
  obtain ⟨compiled, middle, first, last⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have sourceLayout := inductive_layout source constructors context before compiled middle first
  obtain ⟨target, info, indices, projections⟩ := finish_inductive_shape source compiled.1 compiled.2.1 compiled.2.2.1
    context middle output after last
  have bound := DeclarationHeaders.projection_pairs_count source compiled.1 compiled.2.1 compiled.2.2.1
    context middle output after last
  exact ⟨target, compiled.2.1, compiled.2.2.1, info, indices.trans sourceLayout.1,
    sourceLayout.2, bound, projections⟩

theorem inductive_projection_resolves (source : InductiveVal) (constructors : Array ConstructorVal)
    (output : BlockResult) (layout : InductiveLayout source constructors output)
    (store : Kernel.Reader.Store) (stored : store output.blockAddr = some output.block) :
    ∃ projection metadata,
      output.projections[0]? = some (source.cnst.name, projection, metadata) ∧
      Kernel.Reader.resolveSource store (Address.blake3 (Ixon.ser projection)) projection =
        some (.member output.blockAddr 0) := by
  obtain ⟨target, metadata, pairs, info, _, _, _, projections⟩ := layout
  let projection : Ixon.Constant := ⟨.iPrj ⟨0, output.blockAddr⟩, #[], #[], #[]⟩
  refine ⟨projection, metadata, ?_, ?_⟩
  · simp [projections, buildInductiveProjections, projection, Array.getElem?_append]
  · simp [projection, Kernel.Reader.resolveSource, Kernel.Reader.emptyTables, stored, info, guard]

private theorem mapped_index {xs : Array α} {ys : Array β} {left : α → γ} {right : β → γ}
    (same : xs.toList.map left = ys.toList.map right) (index : Nat)
    (insideLeft : index < xs.size) (insideRight : index < ys.size) :
    left xs[index] = right ys[index] := by
  have row := congrArg (fun values : List γ => values[index]?) same
  simp only [List.getElem?_map, Array.getElem?_toList] at row
  rw [Array.getElem?_eq_getElem insideLeft, Array.getElem?_eq_getElem insideRight] at row
  exact Option.some.inj row

/-- A generated constructor projection resolves to the source position when
the source constructor declares that position. This source-layout condition
still needs to be discharged by the certified source-domain bridge. -/
theorem constructor_projection_resolves (source : InductiveVal) (constructors : Array ConstructorVal)
    (output : BlockResult) (layout : InductiveLayout source constructors output)
    (store : Kernel.Reader.Store) (stored : store output.blockAddr = some output.block)
    (index : Nat) (inside : index < constructors.size) (sourceIndex : constructors[index].cidx = index) :
    ∃ projection metadata,
      output.projections[index + 1]? = some (constructors[index].cnst.name, projection, metadata) ∧
      Kernel.Reader.resolveSource store (Address.blake3 (Ixon.ser projection)) projection =
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
  have exactIndex : index.toUInt64.toNat = index := DeclarationHeaders.exact_header index (Nat.lt_trans pairInside bound)
  have converted : target.ctors[index].cidx = index.toUInt64 := UInt64.toNat_inj.mp (naturalIndex.trans exactIndex.symm)
  let projection : Ixon.Constant := ⟨.cPrj ⟨0, index.toUInt64, output.blockAddr⟩, #[], #[], #[]⟩
  refine ⟨projection, pairs[index].2, ?_, ?_⟩
  · rw [projections]
    simp only [buildInductiveProjections]
    rw [Array.getElem?_append_right (by simp)]
    simp [Array.getElem?_eq_getElem pairInside, sameName, projection]
  · simp [projection, Kernel.Reader.resolveSource, Kernel.Reader.emptyTables, stored, info,
      exactIndex, Array.getElem?_eq_getElem targetInside, converted, guard]

end Ix.CompileCert.ProjectionLayout
