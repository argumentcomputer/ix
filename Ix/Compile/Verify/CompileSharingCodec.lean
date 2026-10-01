import Ix.Compile.Verify.CompileConstantCodec
import Ix.Compile.Verify.TieredWire

/-!
# Production sharing/constant-codec bridge

This bridge connects the compiler's canonical sharing builder
`Ix.CompileM.buildConstantWithSharing` and `BlockResult.mk'` to the declaration
compiler theorems. The builder shares the payload's roots
(`constantInfoRootExprs`) with `canonicalSharingTiered .tagN` and writes the
result back with `withRootExprs`; its output facts come from
`Tiered.canonicalSharingTiered_format` (`FormatOK`: every table entry and root
is wire-safe, the table count fits a `UInt64`, and Shares point backwards).
The builder fails when the construction does (a resource limit or an
internal error), so the theorems here describe successful builds, and
`SharingSucceeds` is the hypothesis under which a compile step succeeds.
-/

namespace Ix.Compile.Verify

/-- Every member of an expression array is in the expression codec's public
wire domain. -/
def ExprArrayWireWF (exprs : Array Ixon.Expr) : Prop :=
  ∀ expr ∈ exprs, expr.wireWF

/-- A safe array lookup remains safe when it falls back to a separately safe
expression. -/
theorem ExprArrayWireWF.getElem?_getD {exprs : Array Ixon.Expr}
    (hexprs : ExprArrayWireWF exprs) (idx : Nat) {fallback : Ixon.Expr}
    (hfallback : fallback.wireWF) :
    (exprs[idx]?.getD fallback).wireWF := by
  by_cases hidx : idx < exprs.size
  · rw [Array.getElem?_eq_getElem hidx, Option.getD_some]
    exact hexprs _ (Array.getElem_mem hidx)
  · rw [Array.getElem?_eq_none (Nat.le_of_not_gt hidx), Option.getD_none]
    exact hfallback

theorem ExprArrayWireWF.empty : ExprArrayWireWF #[] := by
  intro expr hmem
  simp at hmem

theorem updateRecursorRules_size (rules : Array Ixon.RecursorRule)
    (rewrittenExprs : Array Ixon.Expr) (startIdx : Nat) :
    (Ix.CompileM.updateRecursorRules rules rewrittenExprs startIdx).1.size =
      rules.size := by
  simp [Ix.CompileM.updateRecursorRules]

/-- Pointwise recursor-rule rewriting preserves every rule's expression wire
domain. -/
theorem updateRecursorRules_wireWF (rules : Array Ixon.RecursorRule)
    (rewrittenExprs : Array Ixon.Expr) (startIdx : Nat)
    (hrules : ∀ rule ∈ rules, rule.wireWF)
    (hrewritten : ExprArrayWireWF rewrittenExprs) :
    ∀ rule ∈ (Ix.CompileM.updateRecursorRules
      rules rewrittenExprs startIdx).1, rule.wireWF := by
  intro rule hmem
  unfold Ix.CompileM.updateRecursorRules at hmem
  obtain ⟨i, hi, heq⟩ := Array.mem_mapIdx.mp hmem
  subst rule
  change (rewrittenExprs[startIdx + i]?.getD rules[i].rhs).wireWF
  apply hrewritten.getElem?_getD
  exact hrules _ (Array.getElem_mem hi)

theorem updateConstructorTypes_size (ctors : Array Ixon.Constructor)
    (rewrittenExprs : Array Ixon.Expr) (startIdx : Nat) :
    (Ix.CompileM.updateConstructorTypes ctors rewrittenExprs startIdx).1.size =
      ctors.size := by
  simp [Ix.CompileM.updateConstructorTypes]

/-- Pointwise constructor rewriting preserves every constructor type's wire
domain. -/
theorem updateConstructorTypes_wireWF (ctors : Array Ixon.Constructor)
    (rewrittenExprs : Array Ixon.Expr) (startIdx : Nat)
    (hctors : ∀ ctor ∈ ctors, ctor.wireWF)
    (hrewritten : ExprArrayWireWF rewrittenExprs) :
    ∀ ctor ∈ (Ix.CompileM.updateConstructorTypes
      ctors rewrittenExprs startIdx).1, ctor.wireWF := by
  intro ctor hmem
  unfold Ix.CompileM.updateConstructorTypes at hmem
  obtain ⟨i, hi, heq⟩ := Array.mem_mapIdx.mp hmem
  subst ctor
  change (rewrittenExprs[startIdx + i]?.getD ctors[i].typ).wireWF
  apply hrewritten.getElem?_getD
  exact hctors _ (Array.getElem_mem hi)

/-- Every mutual member accumulated by the production updater is wire-safe. -/
def MutConstUpdateStateWireWF
    (state : Ix.CompileM.MutConstUpdateState) : Prop :=
  ∀ member ∈ state.result, member.wireWF

theorem MutConstUpdateStateWireWF.empty :
    MutConstUpdateStateWireWF
      ({} : Ix.CompileM.MutConstUpdateState) := by
  intro member hmem
  simp at hmem

theorem updateMutConst_wireWF (rewrittenExprs : Array Ixon.Expr)
    (state : Ix.CompileM.MutConstUpdateState) (member : Ixon.MutConst)
    (hstate : MutConstUpdateStateWireWF state)
    (hmember : member.wireWF)
    (hrewritten : ExprArrayWireWF rewrittenExprs) :
    MutConstUpdateStateWireWF
      (Ix.CompileM.updateMutConst rewrittenExprs state member) := by
  cases member with
  | defn definition =>
    intro resultMember hmem
    simp only [Ix.CompileM.updateMutConst] at hmem
    rw [Array.mem_push] at hmem
    rcases hmem with hmem | rfl
    · exact hstate _ hmem
    · exact ⟨hrewritten.getElem?_getD _ hmember.1,
        hrewritten.getElem?_getD _ hmember.2⟩
  | indc indInfo =>
    intro resultMember hmem
    simp only [Ix.CompileM.updateMutConst] at hmem
    rw [Array.mem_push] at hmem
    rcases hmem with hmem | rfl
    · exact hstate _ hmem
    · refine ⟨hrewritten.getElem?_getD _ hmember.1, ?_, ?_⟩
      · rw [updateConstructorTypes_size]
        exact hmember.2.1
      · exact updateConstructorTypes_wireWF _ _ _
          hmember.2.2 hrewritten
  | recr recursor =>
    intro resultMember hmem
    simp only [Ix.CompileM.updateMutConst] at hmem
    rw [Array.mem_push] at hmem
    rcases hmem with hmem | rfl
    · exact hstate _ hmem
    · refine ⟨hrewritten.getElem?_getD _ hmember.1, ?_, ?_⟩
      · rw [updateRecursorRules_size]
        exact hmember.2.1
      · exact updateRecursorRules_wireWF _ _ _ hmember.2.2 hrewritten

theorem updateMutConst_size (rewrittenExprs : Array Ixon.Expr)
    (state : Ix.CompileM.MutConstUpdateState) (member : Ixon.MutConst) :
    (Ix.CompileM.updateMutConst rewrittenExprs state member).result.size =
      state.result.size + 1 := by
  cases member <;> simp [Ix.CompileM.updateMutConst]

theorem updateMutConsts_size (members : Array Ixon.MutConst)
    (rewrittenExprs : Array Ixon.Expr) :
    (Ix.CompileM.updateMutConsts members rewrittenExprs).size =
      members.size := by
  unfold Ix.CompileM.updateMutConsts
  apply Array.foldl_induction
    (motive := fun i (state : Ix.CompileM.MutConstUpdateState) =>
      state.result.size = i)
  · simp
  · intro i state hstate
    rw [updateMutConst_size, hstate]

/-- The heterogeneous mutual-member fold preserves every nested expression
and counted child array in the public constant wire domain. -/
theorem updateMutConsts_wireWF (members : Array Ixon.MutConst)
    (rewrittenExprs : Array Ixon.Expr)
    (hmembers : ∀ member ∈ members, member.wireWF)
    (hrewritten : ExprArrayWireWF rewrittenExprs) :
    ∀ member ∈ Ix.CompileM.updateMutConsts members rewrittenExprs,
      member.wireWF := by
  unfold Ix.CompileM.updateMutConsts
  apply Array.foldl_induction
    (motive := fun _ state => MutConstUpdateStateWireWF state)
  · exact MutConstUpdateStateWireWF.empty
  · intro i state hstate
    apply updateMutConst_wireWF
    · exact hstate
    · exact hmembers _ (Array.getElem_mem i.isLt)
    · exact hrewritten

/-- The production cursor-order extractor agrees with the catalog's logical
expression view for every mutual-member variant. -/
theorem mutConstRootExprs_eq_exprs (member : Ixon.MutConst) :
    Ix.CompileM.mutConstRootExprs member = member.exprs := by
  cases member with
  | defn definition => rfl
  | recr recursor => rfl
  | indc indInfo =>
    simp only [Ix.CompileM.mutConstRootExprs, Ixon.MutConst.exprs,
      Ixon.Inductive.exprs]
    congr 1
    change List.map (fun constructor => constructor.typ)
        indInfo.ctors.toList =
      List.flatMap (fun constructor => [constructor.typ])
        indInfo.ctors.toList
    exact List.map_eq_flatMap

/-- The canonical production root array has exactly the catalog's expression
sequence, including flattened mutual members and recursor rules. -/
theorem constantInfoRootExprs_toList (info : Ixon.ConstantInfo) :
    (Ix.CompileM.constantInfoRootExprs info).toList = info.exprs := by
  cases info with
  | defn definition => rfl
  | recr recursor => rfl
  | axio axiomInfo => rfl
  | quot quotient => rfl
  | cPrj projection => rfl
  | rPrj projection => rfl
  | iPrj projection => rfl
  | dPrj projection => rfl
  | muts members =>
    simp only [Ix.CompileM.constantInfoRootExprs,
      Ixon.ConstantInfo.exprs]
    induction members.toList with
    | nil => rfl
    | cons member members ih =>
      simp only [List.flatMap_cons, mutConstRootExprs_eq_exprs, ih]

/-- The canonical sharing roots of one mutual member are exactly its
expression-bearing wire fields, so member wire safety covers every root. -/
theorem mutConstRootExprs_wireWF (member : Ixon.MutConst)
    (hmember : member.wireWF) :
    ∀ expr ∈ Ix.CompileM.mutConstRootExprs member, expr.wireWF := by
  cases member with
  | defn definition =>
    intro expr hmem
    simp [Ix.CompileM.mutConstRootExprs] at hmem
    rcases hmem with rfl | rfl
    · exact hmember.1
    · exact hmember.2
  | indc indInfo =>
    intro expr hmem
    simp only [Ix.CompileM.mutConstRootExprs, List.mem_cons,
      List.mem_map] at hmem
    rcases hmem with rfl | ⟨constructor, hconstructor, rfl⟩
    · exact hmember.1
    · exact hmember.2.2 constructor (by simpa using hconstructor)
  | recr recursor =>
    intro expr hmem
    simp only [Ix.CompileM.mutConstRootExprs, List.mem_cons,
      List.mem_map] at hmem
    rcases hmem with rfl | ⟨rule, hrule, rfl⟩
    · exact hmember.1
    · exact hmember.2.2 rule (by simpa using hrule)

/-- A wire-safe `ConstantInfo` automatically supplies a wire-safe canonical
sharing-root array.  This rules out a mismatch between the payload fields and
the roots consumed by the production singleton driver. -/
theorem constantInfoRootExprs_wireWF (info : Ixon.ConstantInfo)
    (hinfo : info.wireWF) :
    ExprArrayWireWF (Ix.CompileM.constantInfoRootExprs info) := by
  intro expr hmem
  cases info with
  | defn definition =>
    exact mutConstRootExprs_wireWF (.defn definition) hinfo expr
      (by simpa [Ix.CompileM.constantInfoRootExprs] using hmem)
  | recr recursor =>
    exact mutConstRootExprs_wireWF (.recr recursor) hinfo expr
      (by simpa [Ix.CompileM.constantInfoRootExprs] using hmem)
  | axio axiomInfo =>
    simp [Ix.CompileM.constantInfoRootExprs] at hmem
    subst expr
    exact hinfo
  | quot quotient =>
    simp [Ix.CompileM.constantInfoRootExprs] at hmem
    subst expr
    exact hinfo
  | cPrj projection =>
    simp [Ix.CompileM.constantInfoRootExprs] at hmem
  | rPrj projection =>
    simp [Ix.CompileM.constantInfoRootExprs] at hmem
  | iPrj projection =>
    simp [Ix.CompileM.constantInfoRootExprs] at hmem
  | dPrj projection =>
    simp [Ix.CompileM.constantInfoRootExprs] at hmem
  | muts members =>
    have hlist : expr ∈ members.toList.flatMap
        Ix.CompileM.mutConstRootExprs := by
      simpa [Ix.CompileM.constantInfoRootExprs] using hmem
    obtain ⟨member, hmember, hexpr⟩ := List.mem_flatMap.mp hlist
    exact mutConstRootExprs_wireWF member
      (hinfo.2 member (by simpa using hmember)) expr hexpr

/-! ## The canonical sharing builder -/

/-- The canonical sharing construction succeeds on the payload's roots under
`limits` and returns one root per input root: exactly when
`buildConstantWithSharing` succeeds (`buildConstantWithSharing_of_succeeds`). -/
def SharingSucceeds (limits : Ix.Sharing.Exact.Limits) (info : Ixon.ConstantInfo) :
    Prop :=
  ∃ r, Ix.Sharing.Exact.canonicalSharingTiered .tagN
      (Ix.CompileM.constantInfoRootExprs info) limits = .ok r ∧
    r.result.roots.size = (Ix.CompileM.constantInfoRootExprs info).size

/-- A successful build is the canonical construction of the payload's roots,
written back into the payload. -/
theorem buildConstantWithSharing_eq_ok {limits : Ix.Sharing.Exact.Limits}
    {info : Ixon.ConstantInfo} {refs : Array Address} {univs : Array Ixon.Univ}
    {block : Ixon.Constant}
    (h : Ix.CompileM.buildConstantWithSharing limits info refs univs = .ok block) :
    ∃ r, Ix.Sharing.Exact.canonicalSharingTiered .tagN
        (Ix.CompileM.constantInfoRootExprs info) limits = .ok r ∧
      r.result.roots.size = (Ix.CompileM.constantInfoRootExprs info).size ∧
      block = { info := Ix.CompileM.withRootExprs info r.result.roots,
                sharing := r.result.sharing, refs, univs } := by
  simp only [Ix.CompileM.buildConstantWithSharing] at h
  cases hr : Ix.Sharing.Exact.canonicalSharingTiered .tagN
      (Ix.CompileM.constantInfoRootExprs info) limits with
  | error e =>
    simp [hr, Except.mapError, bind, Except.bind] at h
  | ok r =>
    simp only [hr, Except.mapError] at h
    by_cases hs : r.result.roots.size = (Ix.CompileM.constantInfoRootExprs info).size
    · refine ⟨r, rfl, hs, ?_⟩
      simp [hs, bind, Except.bind, pure, Except.pure] at h
      exact h.symm
    · simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-- The builder's result when the canonical construction succeeds with one
root per input root. -/
theorem buildConstantWithSharing_of_canonical {limits : Ix.Sharing.Exact.Limits}
    {info : Ixon.ConstantInfo} {r : Ix.Sharing.Exact.TieredSharingResult}
    (hr : Ix.Sharing.Exact.canonicalSharingTiered .tagN
      (Ix.CompileM.constantInfoRootExprs info) limits = .ok r)
    (hs : r.result.roots.size = (Ix.CompileM.constantInfoRootExprs info).size)
    (refs : Array Address) (univs : Array Ixon.Univ) :
    Ix.CompileM.buildConstantWithSharing limits info refs univs =
      .ok { info := Ix.CompileM.withRootExprs info r.result.roots,
            sharing := r.result.sharing, refs, univs } := by
  simp [Ix.CompileM.buildConstantWithSharing, hr, Except.mapError, hs, bind, Except.bind,
    pure, Except.pure]

/-- Under `SharingSucceeds` the builder succeeds, whatever the tables. -/
theorem buildConstantWithSharing_of_succeeds {limits : Ix.Sharing.Exact.Limits}
    {info : Ixon.ConstantInfo} (h : SharingSucceeds limits info)
    (refs : Array Address) (univs : Array Ixon.Univ) :
    ∃ block, Ix.CompileM.buildConstantWithSharing limits info refs univs = .ok block := by
  obtain ⟨r, hr, hs⟩ := h
  exact ⟨_, buildConstantWithSharing_of_canonical hr hs refs univs⟩

/-- Writing wire-safe roots back preserves the payload's wire domain. -/
theorem withRootExprs_wireWF (info : Ixon.ConstantInfo) (rewritten : Array Ixon.Expr)
    (hinfo : info.wireWF) (hwire : ExprArrayWireWF rewritten) :
    (Ix.CompileM.withRootExprs info rewritten).wireWF := by
  cases info with
  | defn definition =>
    exact ⟨hwire.getElem?_getD 0 hinfo.1, hwire.getElem?_getD 1 hinfo.2⟩
  | recr recursor =>
    rw [show Ix.CompileM.withRootExprs (.recr recursor) rewritten =
        .recr { recursor with
          typ := rewritten[0]?.getD recursor.typ
          rules := (Ix.CompileM.updateRecursorRules recursor.rules rewritten 1).1 } by
      simp [Ix.CompileM.withRootExprs]]
    refine ⟨?_, ?_, ?_⟩
    · exact hwire.getElem?_getD 0 hinfo.1
    · rw [updateRecursorRules_size]
      exact hinfo.2.1
    · exact updateRecursorRules_wireWF _ _ _ hinfo.2.2 hwire
  | axio axiomInfo => exact hwire.getElem?_getD 0 hinfo
  | quot quotient => exact hwire.getElem?_getD 0 hinfo
  | cPrj projection => exact hinfo
  | rPrj projection => exact hinfo
  | iPrj projection => exact hinfo
  | dPrj projection => exact hinfo
  | muts members =>
    refine ⟨?_, ?_⟩
    · show (Ix.CompileM.updateMutConsts members rewritten).size < UInt64.size
      rw [updateMutConsts_size]
      exact hinfo.1
    · exact updateMutConsts_wireWF _ _ hinfo.2 hwire

/-- **Every block the compiler's sharing builds is in the constant codec's wire
domain**, for every `ConstantInfo` variant: the payload's fields are kept,
its roots and the table come from the canonical construction, and
`Tiered.canonicalSharingTiered_format` makes them wire-safe with a table count
below `2^64`. -/
theorem buildConstantWithSharing_wireWF {limits : Ix.Sharing.Exact.Limits}
    {info : Ixon.ConstantInfo} {state : Ix.CompileM.BlockState}
    {block : Ixon.Constant} (hinfo : info.wireWF)
    (htables : BlockWireTablesWF state)
    (h : Ix.CompileM.buildConstantWithSharing limits info
      state.refs state.univs = .ok block) :
    block.wireWF := by
  obtain ⟨r, hr, -, rfl⟩ := buildConstantWithSharing_eq_ok h
  obtain ⟨hentries, hroots, hcapacity, -, -⟩ := Tiered.canonicalSharingTiered_format hr
  refine ⟨withRootExprs_wireWF info _ hinfo ?_, hcapacity, ?_, htables.refsCount,
    htables.refs, htables.univsCount, htables.univs⟩
  · intro expr hmem
    exact hroots expr (by simpa using hmem)
  · intro expr hmem
    exact hentries expr (by simpa using hmem)

/-- When the canonical construction keeps a singleton axiom root and builds no
table, the builder yields exactly the unshared axiom assembly. -/
theorem buildConstantWithSharing_axiom_eq_unshared
    (limits : Ix.Sharing.Exact.Limits) (isUnsafe : Bool) (lvls : UInt64)
    (typ : Ixon.Expr) (state : Ix.CompileM.BlockState)
    {r : Ix.Sharing.Exact.TieredSharingResult}
    (hsharing : Ix.Sharing.Exact.canonicalSharingTiered .tagN #[typ] limits = .ok r)
    (hroots : r.result.roots = #[typ]) (htable : r.result.sharing = #[]) :
    Ix.CompileM.buildConstantWithSharing limits
        (.axio { isUnsafe, lvls, typ }) state.refs state.univs =
      .ok (unsharedAxiomConstant isUnsafe lvls typ state) := by
  have hr : Ix.Sharing.Exact.canonicalSharingTiered .tagN
      (Ix.CompileM.constantInfoRootExprs (.axio { isUnsafe, lvls, typ })) limits = .ok r :=
    hsharing
  rw [buildConstantWithSharing_of_canonical hr (by rw [hroots]; rfl)]
  simp [hroots, htable, Ix.CompileM.withRootExprs, unsharedAxiomConstant]

/-- When the canonical construction keeps both definition roots and builds no
table, the builder yields exactly the unshared definition assembly. -/
theorem buildConstantWithSharing_definition_eq_unshared
    (limits : Ix.Sharing.Exact.Limits) (kind : Ix.DefKind)
    (safety : Ix.DefinitionSafety) (lvls : UInt64) (typ value : Ixon.Expr)
    (state : Ix.CompileM.BlockState) {r : Ix.Sharing.Exact.TieredSharingResult}
    (hsharing : Ix.Sharing.Exact.canonicalSharingTiered .tagN #[typ, value] limits = .ok r)
    (hroots : r.result.roots = #[typ, value]) (htable : r.result.sharing = #[]) :
    Ix.CompileM.buildConstantWithSharing limits
        (.defn { kind, safety, lvls, typ, value }) state.refs state.univs =
      .ok (unsharedDefinitionConstant kind safety lvls typ value state) := by
  have hr : Ix.Sharing.Exact.canonicalSharingTiered .tagN
      (Ix.CompileM.constantInfoRootExprs (.defn { kind, safety, lvls, typ, value })) limits =
        .ok r := hsharing
  rw [buildConstantWithSharing_of_canonical hr (by rw [hroots]; rfl)]
  simp [hroots, htable, Ix.CompileM.withRootExprs, unsharedDefinitionConstant]


/-- `BlockResult.mk'` stores exactly the production constant serialization,
so every wire-well-formed block is recovered from its stored bytes. Metadata
and projections do not affect those bytes. -/
theorem BlockResult.mk'_codec_roundtrip
    (block : Ixon.Constant) (blockMeta : Ixon.ConstantMeta := .empty)
    (projections : Array
      (Ix.Name × Ixon.Constant × Ixon.ConstantMeta) := #[])
    (hblock : block.wireWF) :
    Ixon.deConstant
        (Ix.CompileM.BlockResult.mk' block blockMeta projections).blockBytes =
      .ok (Ix.CompileM.BlockResult.mk' block blockMeta projections).block := by
  change Ixon.deConstant (Ixon.ser block) = .ok block
  rw [show Ixon.ser block = Ixon.serConstant block from rfl]
  exact deConstant_serConstant block hblock

/-- Verification condition carried from a production declaration driver to
the serialized main block it returns. -/
def BlockResultCodecWF (result : Ix.CompileM.BlockResult) : Prop :=
  result.block.wireWF ∧
  Ixon.deConstant result.blockBytes = .ok result.block

theorem BlockResult.mk'_codecWF
    (block : Ixon.Constant) (blockMeta : Ixon.ConstantMeta := .empty)
    (projections : Array
      (Ix.Name × Ixon.Constant × Ixon.ConstantMeta) := #[])
    (hblock : block.wireWF) :
    BlockResultCodecWF
      (Ix.CompileM.BlockResult.mk' block blockMeta projections) := by
  exact ⟨hblock,
    BlockResult.mk'_codec_roundtrip block blockMeta projections hblock⟩

private theorem run_bind (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (action : Ix.CompileM.CompileM α)
    (next : α → Ix.CompileM.CompileM β) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state (action >>= next) =
      match Ix.CompileM.CompileM.run compileEnv blockEnv state action with
      | .error err => .error err
      | .ok (value, state') =>
        Ix.CompileM.CompileM.run compileEnv blockEnv state' (next value) := by
  simp [Ix.CompileM.CompileM.run, ReaderT.run_bind, ExceptT.run_bind,
    StateT.run_bind]
  generalize
    (ReaderT.run action (compileEnv, blockEnv)).run.run state = result
  rcases result with ⟨result, state'⟩
  cases result <;> rfl

theorem run_getBlockState_eq (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state Ix.CompileM.getBlockState =
      .ok (state, state) := rfl

theorem run_read_eq (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state read =
      .ok ((compileEnv, blockEnv), state) := rfl

theorem run_liftSharing_eq (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (x : Except Ix.CompileM.CompileError Ixon.Constant) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state (Ix.CompileM.liftSharing x) =
      match x with
      | .ok c => .ok (c, state)
      | .error e => .error e := by
  cases x <;> rfl

/-- A successful build of any wire-safe payload, wrapped in the production
`BlockResult`, stores bytes that decode exactly to the built block. This
includes all projection variants and both empty and nonempty sharing. -/
theorem BlockResult.constantInfo_codec_roundtrip
    {limits : Ix.Sharing.Exact.Limits} (info : Ixon.ConstantInfo)
    {state : Ix.CompileM.BlockState} {block : Ixon.Constant}
    (blockMeta : Ixon.ConstantMeta) (hinfo : info.wireWF)
    (htables : BlockWireTablesWF state)
    (h : Ix.CompileM.buildConstantWithSharing limits info
      state.refs state.univs = .ok block)
    (projections : Array
      (Ix.Name × Ixon.Constant × Ixon.ConstantMeta) := #[]) :
    Ixon.deConstant
        (Ix.CompileM.BlockResult.mk' block blockMeta projections).blockBytes =
      .ok block := by
  apply BlockResult.mk'_codec_roundtrip
  exact buildConstantWithSharing_wireWF hinfo htables h

/-- The production singleton-driver tail reads the current block state, runs
the canonical sharing builder under `CompileEnv.sharingLimits` and wraps its
result in the canonical `BlockResult`; it leaves the state unchanged, and it
fails exactly when the builder does. -/
theorem finishConstantWithSharing_run
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (info : Ixon.ConstantInfo) (blockMeta : Ixon.ConstantMeta := .empty) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.finishConstantWithSharing info blockMeta) =
      match Ix.CompileM.buildConstantWithSharing compileEnv.sharingLimits info
          state.refs state.univs with
      | .ok block => .ok (Ix.CompileM.BlockResult.mk' block blockMeta, state)
      | .error e => .error e := by
  simp only [Ix.CompileM.finishConstantWithSharing, Ix.CompileM.buildBlockConstant,
    run_bind, run_getBlockState_eq, run_read_eq, run_liftSharing_eq]
  cases Ix.CompileM.buildConstantWithSharing compileEnv.sharingLimits info
    state.refs state.univs <;> rfl

/-- When the builder succeeds, the singleton-driver tail returns that block in
a wire-safe, exactly decodable `BlockResult` and leaves the state unchanged. -/
theorem finishConstantWithSharing_run_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (info : Ixon.ConstantInfo) (blockMeta : Ixon.ConstantMeta)
    {block : Ixon.Constant} (hinfo : info.wireWF)
    (htables : BlockWireTablesWF state)
    (hbuild : Ix.CompileM.buildConstantWithSharing compileEnv.sharingLimits info
      state.refs state.univs = .ok block) :
    let result := Ix.CompileM.BlockResult.mk' block blockMeta
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.finishConstantWithSharing info blockMeta) =
        .ok (result, state) ∧
      BlockResultCodecWF result := by
  dsimp only
  constructor
  · rw [finishConstantWithSharing_run compileEnv blockEnv state info blockMeta, hbuild]
  · apply BlockResult.mk'_codecWF
    exact buildConstantWithSharing_wireWF hinfo htables hbuild

/-- `finishConstantInfoWithSharing` is `finishConstantWithSharing`. -/
theorem finishConstantInfoWithSharing_run
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (info : Ixon.ConstantInfo)
    (blockMeta : Ixon.ConstantMeta := .empty) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.finishConstantInfoWithSharing info blockMeta) =
      match Ix.CompileM.buildConstantWithSharing compileEnv.sharingLimits info
          state.refs state.univs with
      | .ok block => .ok (Ix.CompileM.BlockResult.mk' block blockMeta, state)
      | .error e => .error e :=
  finishConstantWithSharing_run compileEnv blockEnv state info blockMeta


/-- The outcome of a declaration run whose only possible failure is the
canonical sharing builder: either the run succeeds with a wire-safe, exactly
decodable `BlockResult`, or it fails with exactly the error the builder
returns on some payload and tables. This is the conclusion of the compiler
endpoint theorems; with the builder total (`SharingSucceeds`) only the first
case remains. -/
def SharingRunOK (limits : Ix.Sharing.Exact.Limits)
    (run : Except Ix.CompileM.CompileError
      (Ix.CompileM.BlockResult × Ix.CompileM.BlockState)) : Prop :=
  (∃ result state', run = .ok (result, state') ∧ BlockResultCodecWF result) ∨
  ∃ (info : Ixon.ConstantInfo) (state' : Ix.CompileM.BlockState)
    (err : Ix.CompileM.CompileError),
    Ix.CompileM.buildConstantWithSharing limits info state'.refs state'.univs =
      .error err ∧ run = .error err

/-- Every successful run covered by `SharingRunOK` returns a wire-safe, exactly
decodable block. -/
theorem SharingRunOK.codecWF {limits : Ix.Sharing.Exact.Limits}
    {run : Except Ix.CompileM.CompileError
      (Ix.CompileM.BlockResult × Ix.CompileM.BlockState)}
    (h : SharingRunOK limits run) {result : Ix.CompileM.BlockResult}
    {state' : Ix.CompileM.BlockState} (hrun : run = .ok (result, state')) :
    BlockResultCodecWF result := by
  rcases h with ⟨result', state'', hok, hcodec⟩ | ⟨_, _, err, _, herr⟩
  · rw [hrun] at hok
    cases hok
    exact hcodec
  · rw [hrun] at herr
    cases herr

/-- The singleton-driver tail on a wire-safe payload: it fails only when the
canonical sharing builder does, and otherwise returns a wire-safe, exactly
decodable block. -/
theorem finishConstantInfoWithSharing_run_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (info : Ixon.ConstantInfo) (blockMeta : Ixon.ConstantMeta)
    (hinfo : info.wireWF) (htables : BlockWireTablesWF state) :
    SharingRunOK compileEnv.sharingLimits
      (Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.finishConstantInfoWithSharing info blockMeta)) := by
  rw [finishConstantInfoWithSharing_run compileEnv blockEnv state info blockMeta]
  cases hbuild : Ix.CompileM.buildConstantWithSharing compileEnv.sharingLimits info
      state.refs state.univs with
  | ok block =>
    exact .inl ⟨_, _, rfl, BlockResult.mk'_codecWF block blockMeta #[]
      (buildConstantWithSharing_wireWF hinfo htables hbuild)⟩
  | error err => exact .inr ⟨info, state, err, hbuild, rfl⟩

/-- When the canonical sharing of the payload succeeds, so does the
singleton-driver tail, with a wire-safe, exactly decodable block. -/
theorem finishConstantInfoWithSharing_run_codecWF_of_succeeds
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (info : Ixon.ConstantInfo) (blockMeta : Ixon.ConstantMeta)
    (hinfo : info.wireWF) (htables : BlockWireTablesWF state)
    (hshare : SharingSucceeds compileEnv.sharingLimits info) :
    ∃ block,
      Ix.CompileM.buildConstantWithSharing compileEnv.sharingLimits info
          state.refs state.univs = .ok block ∧
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.finishConstantInfoWithSharing info blockMeta) =
        .ok (Ix.CompileM.BlockResult.mk' block blockMeta, state) ∧
      BlockResultCodecWF (Ix.CompileM.BlockResult.mk' block blockMeta) := by
  obtain ⟨block, hbuild⟩ := buildConstantWithSharing_of_succeeds hshare state.refs state.univs
  obtain ⟨hrun, hcodec⟩ := finishConstantWithSharing_run_codecWF compileEnv blockEnv state
    info blockMeta hinfo htables hbuild
  exact ⟨block, hbuild, hrun, hcodec⟩

/-- The ordinary axiom expression phase followed by a no-sharing canonical
build (the construction keeps the root and builds no table) yields stored
bytes that decode to the built block. -/
theorem compileExpr_run_ordinary_axiomBlock_noSharing_roundtrip
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (limits : Ix.Sharing.Exact.Limits)
    (isUnsafe : Bool) (lvls : UInt64) (blockMeta : Ixon.ConstantMeta)
    {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr} {r : Ix.Sharing.Exact.TieredSharingResult}
    (hsource : SupportedOrdinaryExpr levelSupport source)
    (hbound : ExprWireBound source)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) source = some target)
    (hsharing : Ix.Sharing.Exact.canonicalSharingTiered .tagN #[target] limits = .ok r)
    (hroots : r.result.roots = #[target]) (htable : r.result.sharing = #[]) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr source) =
        .ok ((target, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      (let block := unsharedAxiomConstant isUnsafe lvls target state'
       Ix.CompileM.buildConstantWithSharing limits
           (.axio { isUnsafe, lvls, typ := target }) state'.refs state'.univs =
         .ok block ∧
       block.wireWF ∧
         Ixon.deConstant
            (Ix.CompileM.BlockResult.mk' block blockMeta).blockBytes =
          .ok block) := by
  obtain ⟨root, state', hrun, hstate', hunshared, _⟩ :=
    compileExpr_run_ordinary_axiomConstant_roundtrip compileEnv blockEnv
      snapshot hfree hclosed hlevelFaithful hexprFaithful htables
      isUnsafe lvls hsource hbound hstate href
  refine ⟨root, state', hrun, hstate', ?_⟩
  dsimp only
  exact ⟨buildConstantWithSharing_axiom_eq_unshared limits isUnsafe lvls target state'
      hsharing hroots htable, hunshared,
    BlockResult.mk'_codec_roundtrip _ blockMeta #[] hunshared⟩

/-- The sequential definition expression phase followed by a no-sharing
canonical build yields stored bytes that decode to the built block. -/
theorem compileExpr_run_ordinary_definitionBlock_noSharing_roundtrip
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (limits : Ix.Sharing.Exact.Limits)
    (kind : Ix.DefKind) (safety : Ix.DefinitionSafety) (lvls : UInt64)
    (blockMeta : Ixon.ConstantMeta)
    {state : Ix.CompileM.BlockState}
    {sourceType sourceValue : Ix.Expr}
    {targetType targetValue : Ixon.Expr}
    {r : Ix.Sharing.Exact.TieredSharingResult}
    (hsourceType : SupportedOrdinaryExpr levelSupport sourceType)
    (hsourceValue : SupportedOrdinaryExpr levelSupport sourceValue)
    (hboundType : ExprWireBound sourceType)
    (hboundValue : ExprWireBound sourceValue)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hrefType : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) sourceType =
        some targetType)
    (hrefValue : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) sourceValue =
        some targetValue)
    (hsharing : Ix.Sharing.Exact.canonicalSharingTiered .tagN
      #[targetType, targetValue] limits = .ok r)
    (hroots : r.result.roots = #[targetType, targetValue])
    (htable : r.result.sharing = #[]) :
    ∃ typeRoot middle valueRoot state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr sourceType) =
        .ok ((targetType, typeRoot), middle) ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot middle ∧
      Ix.CompileM.CompileM.run compileEnv blockEnv middle
          (Ix.CompileM.compileExpr sourceValue) =
        .ok ((targetValue, valueRoot), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      (let block := unsharedDefinitionConstant kind safety lvls targetType
          targetValue state'
       Ix.CompileM.buildConstantWithSharing limits
           (.defn ⟨kind, safety, lvls, targetType, targetValue⟩)
           state'.refs state'.univs = .ok block ∧
       block.wireWF ∧
         Ixon.deConstant
            (Ix.CompileM.BlockResult.mk' block blockMeta).blockBytes =
          .ok block) := by
  obtain ⟨typeRoot, middle, valueRoot, state', htypeRun, hmiddle,
      hvalueRun, hstate', hunshared, _⟩ :=
    compileExpr_run_ordinary_definitionConstant_roundtrip compileEnv blockEnv
      snapshot hfree hclosed hlevelFaithful hexprFaithful htables
      kind safety lvls hsourceType hsourceValue hboundType hboundValue hstate
      hrefType hrefValue
  refine ⟨typeRoot, middle, valueRoot, state', htypeRun, hmiddle,
    hvalueRun, hstate', ?_⟩
  dsimp only
  exact ⟨buildConstantWithSharing_definition_eq_unshared limits kind safety lvls
      targetType targetValue state' hsharing hroots htable, hunshared,
    BlockResult.mk'_codec_roundtrip _ blockMeta #[] hunshared⟩

/-- The ordinary axiom expression phase followed by the canonical sharing
builder: every successful build is a wire-safe block whose stored bytes
decode exactly. -/
theorem compileExpr_run_ordinary_axiomBlock_roundtrip
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (isUnsafe : Bool) (lvls : UInt64) (blockMeta : Ixon.ConstantMeta)
    {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr}
    (hsource : SupportedOrdinaryExpr levelSupport source)
    (hbound : ExprWireBound source)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) source = some target) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr source) =
        .ok ((target, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      ∀ (limits : Ix.Sharing.Exact.Limits) (block : Ixon.Constant),
        Ix.CompileM.buildConstantWithSharing limits
            (.axio { isUnsafe, lvls, typ := target }) state'.refs state'.univs =
          .ok block →
        block.wireWF ∧
          Ixon.deConstant
              (Ix.CompileM.BlockResult.mk' block blockMeta).blockBytes =
            .ok block := by
  obtain ⟨root, state', hrun, hstate', hunshared, _⟩ :=
    compileExpr_run_ordinary_axiomConstant_roundtrip compileEnv blockEnv
      snapshot hfree hclosed hlevelFaithful hexprFaithful htables
      isUnsafe lvls hsource hbound hstate href
  have htables' : BlockWireTablesWF state' :=
    htables.of_exprTableView_eq hstate'.tables
  refine ⟨root, state', hrun, hstate', ?_⟩
  intro limits block hbuild
  have hblock := buildConstantWithSharing_wireWF
    (info := .axio { isUnsafe, lvls, typ := target }) hunshared.1 htables' hbuild
  exact ⟨hblock, BlockResult.mk'_codec_roundtrip _ blockMeta #[] hblock⟩

/-- Sequential ordinary compilation of a definition's type and value followed
by the canonical sharing builder: every successful build is a wire-safe,
exactly decodable block. -/
theorem compileExpr_run_ordinary_definitionBlock_roundtrip
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (kind : Ix.DefKind) (safety : Ix.DefinitionSafety) (lvls : UInt64)
    (blockMeta : Ixon.ConstantMeta)
    {state : Ix.CompileM.BlockState}
    {sourceType sourceValue : Ix.Expr}
    {targetType targetValue : Ixon.Expr}
    (hsourceType : SupportedOrdinaryExpr levelSupport sourceType)
    (hsourceValue : SupportedOrdinaryExpr levelSupport sourceValue)
    (hboundType : ExprWireBound sourceType)
    (hboundValue : ExprWireBound sourceValue)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hrefType : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) sourceType =
        some targetType)
    (hrefValue : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) sourceValue =
        some targetValue) :
    ∃ typeRoot middle valueRoot state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr sourceType) =
        .ok ((targetType, typeRoot), middle) ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot middle ∧
      Ix.CompileM.CompileM.run compileEnv blockEnv middle
          (Ix.CompileM.compileExpr sourceValue) =
        .ok ((targetValue, valueRoot), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      ∀ (limits : Ix.Sharing.Exact.Limits) (block : Ixon.Constant),
        Ix.CompileM.buildConstantWithSharing limits
            (.defn ⟨kind, safety, lvls, targetType, targetValue⟩)
            state'.refs state'.univs = .ok block →
        block.wireWF ∧
          Ixon.deConstant
              (Ix.CompileM.BlockResult.mk' block blockMeta).blockBytes =
            .ok block := by
  obtain ⟨typeRoot, middle, valueRoot, state', htypeRun, hmiddle,
      hvalueRun, hstate', hunshared, _⟩ :=
    compileExpr_run_ordinary_definitionConstant_roundtrip compileEnv blockEnv
      snapshot hfree hclosed hlevelFaithful hexprFaithful htables
      kind safety lvls hsourceType hsourceValue hboundType hboundValue hstate
      hrefType hrefValue
  have htables' : BlockWireTablesWF state' :=
    htables.of_exprTableView_eq hstate'.tables
  refine ⟨typeRoot, middle, valueRoot, state', htypeRun, hmiddle,
    hvalueRun, hstate', ?_⟩
  intro limits block hbuild
  have hblock := buildConstantWithSharing_wireWF
    (info := .defn ⟨kind, safety, lvls, targetType, targetValue⟩) hunshared.1 htables' hbuild
  exact ⟨hblock, BlockResult.mk'_codec_roundtrip _ blockMeta #[] hblock⟩

end Ix.Compile.Verify
