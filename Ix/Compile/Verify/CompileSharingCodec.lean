import Ix.Compile.Verify.CompileConstantCodec
import Ix.Compile.Verify.Sharing

/-!
# Production sharing/constant-codec bridge

This bridge connects the real `buildConstantWithSharing` and `BlockResult.mk'`
functions to the axiom and definition compiler theorems. The original exact
no-sharing equalities remain useful, while the complete results now cover
nonempty production sharing through the verified analysis/rewrite pipeline
and its explicit `UInt64` overflow fallback.
-/

namespace Ix.Compile.Verify

/-- When sharing analysis leaves a singleton axiom root unchanged, the actual
production builder is exactly the unshared axiom assembly. -/
theorem buildConstantWithSharing_axiom_eq_unshared
    (isUnsafe : Bool) (lvls : UInt64) (typ : Ixon.Expr)
    (state : Ix.CompileM.BlockState)
    (hsharing : Ix.Sharing.applySharing #[typ] = (#[typ], #[])) :
    Ix.CompileM.buildConstantWithSharing
        (.axio { isUnsafe, lvls, typ }) #[typ] state.refs state.univs =
      unsharedAxiomConstant isUnsafe lvls typ state := by
  simp [Ix.CompileM.buildConstantWithSharing, hsharing,
    unsharedAxiomConstant]

/-- When sharing analysis leaves both definition roots unchanged, the actual
production builder is exactly the unshared definition assembly. -/
theorem buildConstantWithSharing_definition_eq_unshared
    (kind : Ix.DefKind) (safety : Ix.DefinitionSafety) (lvls : UInt64)
    (typ value : Ixon.Expr) (state : Ix.CompileM.BlockState)
    (hsharing : Ix.Sharing.applySharing #[typ, value] =
      (#[typ, value], #[])) :
    Ix.CompileM.buildConstantWithSharing
        (.defn { kind, safety, lvls, typ, value }) #[typ, value]
        state.refs state.univs =
      unsharedDefinitionConstant kind safety lvls typ value state := by
  simp [Ix.CompileM.buildConstantWithSharing, hsharing,
    unsharedDefinitionConstant]

theorem buildConstantWithSharing_axiom_noSharing_wireWF
    {isUnsafe : Bool} {lvls : UInt64} {typ : Ixon.Expr}
    {state : Ix.CompileM.BlockState}
    (hsharing : Ix.Sharing.applySharing #[typ] = (#[typ], #[]))
    (htyp : typ.wireWF) (htables : BlockWireTablesWF state) :
    (Ix.CompileM.buildConstantWithSharing
      (.axio { isUnsafe, lvls, typ }) #[typ]
      state.refs state.univs).wireWF := by
  rw [buildConstantWithSharing_axiom_eq_unshared
    isUnsafe lvls typ state hsharing]
  exact unsharedAxiomConstant_wireWF htyp htables

theorem buildConstantWithSharing_definition_noSharing_wireWF
    {kind : Ix.DefKind} {safety : Ix.DefinitionSafety} {lvls : UInt64}
    {typ value : Ixon.Expr} {state : Ix.CompileM.BlockState}
    (hsharing : Ix.Sharing.applySharing #[typ, value] =
      (#[typ, value], #[]))
    (htyp : typ.wireWF) (hvalue : value.wireWF)
    (htables : BlockWireTablesWF state) :
    (Ix.CompileM.buildConstantWithSharing
      (.defn { kind, safety, lvls, typ, value }) #[typ, value]
      state.refs state.univs).wireWF := by
  rw [buildConstantWithSharing_definition_eq_unshared
    kind safety lvls typ value state hsharing]
  exact unsharedDefinitionConstant_wireWF htyp hvalue htables

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

/-- For every `ConstantInfo` variant, the production sharing builder preserves
the complete public constant wire domain.  The root array may be arbitrary:
present rewritten slots are safe by `applySharing_wireWF`, while absent slots
fall back to the wire-safe expressions already stored in `info`. -/
theorem buildConstantWithSharing_wireWF
    (info : Ixon.ConstantInfo) (rootExprs : Array Ixon.Expr)
    {state : Ix.CompileM.BlockState} (hinfo : info.wireWF)
    (hroots : ExprArrayWireWF rootExprs)
    (htables : BlockWireTablesWF state) :
    (Ix.CompileM.buildConstantWithSharing info rootExprs
      state.refs state.univs).wireWF := by
  let output := Ix.Sharing.applySharing rootExprs
  have houtput : Ix.Sharing.applySharing rootExprs = output := rfl
  rcases output with ⟨rewritten, sharing⟩
  have hwire := applySharing_wireWF rootExprs hroots
  have hcapacity := applySharing_capacity rootExprs
  rw [houtput] at hwire hcapacity
  cases info with
  | defn definition =>
    rw [show Ix.CompileM.buildConstantWithSharing (.defn definition)
        rootExprs state.refs state.univs =
        Ixon.Constant.mk
          (.defn { definition with
            typ := rewritten[0]?.getD definition.typ
            value := rewritten[1]?.getD definition.value })
          sharing state.refs state.univs by
      simp [Ix.CompileM.buildConstantWithSharing, houtput]]
    refine ⟨⟨?_, ?_⟩, hcapacity, hwire.2, htables.refsCount,
      htables.refs, htables.univsCount, htables.univs⟩
    · exact hwire.1.getElem?_getD 0 hinfo.1
    · exact hwire.1.getElem?_getD 1 hinfo.2
  | recr recursor =>
    rw [show Ix.CompileM.buildConstantWithSharing (.recr recursor)
        rootExprs state.refs state.univs =
        Ixon.Constant.mk
          (.recr { recursor with
            typ := rewritten[0]?.getD recursor.typ
            rules := (Ix.CompileM.updateRecursorRules
              recursor.rules rewritten 1).1 })
          sharing state.refs state.univs by
      simp [Ix.CompileM.buildConstantWithSharing, houtput]]
    refine ⟨⟨?_, ?_, ?_⟩, hcapacity, hwire.2, htables.refsCount,
      htables.refs, htables.univsCount, htables.univs⟩
    · exact hwire.1.getElem?_getD 0 hinfo.1
    · rw [updateRecursorRules_size]
      exact hinfo.2.1
    · exact updateRecursorRules_wireWF _ _ _ hinfo.2.2 hwire.1
  | axio axiomInfo =>
    rw [show Ix.CompileM.buildConstantWithSharing (.axio axiomInfo)
        rootExprs state.refs state.univs =
        Ixon.Constant.mk
          (.axio { axiomInfo with
            typ := rewritten[0]?.getD axiomInfo.typ })
          sharing state.refs state.univs by
      simp [Ix.CompileM.buildConstantWithSharing, houtput]]
    refine ⟨?_, hcapacity, hwire.2, htables.refsCount, htables.refs,
      htables.univsCount, htables.univs⟩
    exact hwire.1.getElem?_getD 0 hinfo
  | quot quotient =>
    rw [show Ix.CompileM.buildConstantWithSharing (.quot quotient)
        rootExprs state.refs state.univs =
        Ixon.Constant.mk
          (.quot { quotient with
            typ := rewritten[0]?.getD quotient.typ })
          sharing state.refs state.univs by
      simp [Ix.CompileM.buildConstantWithSharing, houtput]]
    refine ⟨?_, hcapacity, hwire.2, htables.refsCount, htables.refs,
      htables.univsCount, htables.univs⟩
    exact hwire.1.getElem?_getD 0 hinfo
  | cPrj projection =>
    rw [show Ix.CompileM.buildConstantWithSharing (.cPrj projection)
        rootExprs state.refs state.univs =
        Ixon.Constant.mk (.cPrj projection) sharing state.refs state.univs by
      simp [Ix.CompileM.buildConstantWithSharing, houtput]]
    exact ⟨hinfo, hcapacity, hwire.2, htables.refsCount, htables.refs,
      htables.univsCount, htables.univs⟩
  | rPrj projection =>
    rw [show Ix.CompileM.buildConstantWithSharing (.rPrj projection)
        rootExprs state.refs state.univs =
        Ixon.Constant.mk (.rPrj projection) sharing state.refs state.univs by
      simp [Ix.CompileM.buildConstantWithSharing, houtput]]
    exact ⟨hinfo, hcapacity, hwire.2, htables.refsCount, htables.refs,
      htables.univsCount, htables.univs⟩
  | iPrj projection =>
    rw [show Ix.CompileM.buildConstantWithSharing (.iPrj projection)
        rootExprs state.refs state.univs =
        Ixon.Constant.mk (.iPrj projection) sharing state.refs state.univs by
      simp [Ix.CompileM.buildConstantWithSharing, houtput]]
    exact ⟨hinfo, hcapacity, hwire.2, htables.refsCount, htables.refs,
      htables.univsCount, htables.univs⟩
  | dPrj projection =>
    rw [show Ix.CompileM.buildConstantWithSharing (.dPrj projection)
        rootExprs state.refs state.univs =
        Ixon.Constant.mk (.dPrj projection) sharing state.refs state.univs by
      simp [Ix.CompileM.buildConstantWithSharing, houtput]]
    exact ⟨hinfo, hcapacity, hwire.2, htables.refsCount, htables.refs,
      htables.univsCount, htables.univs⟩
  | muts members =>
    rw [show Ix.CompileM.buildConstantWithSharing (.muts members)
        rootExprs state.refs state.univs =
        Ixon.Constant.mk
          (.muts (Ix.CompileM.updateMutConsts members rewritten))
          sharing state.refs state.univs by
      simp [Ix.CompileM.buildConstantWithSharing, houtput]]
    refine ⟨⟨?_, ?_⟩, hcapacity, hwire.2, htables.refsCount,
      htables.refs, htables.univsCount, htables.univs⟩
    · rw [updateMutConsts_size]
      exact hinfo.1
    · exact updateMutConsts_wireWF _ _ hinfo.2 hwire.1

/-- With the canonical production root extractor, payload wire safety alone
discharges every expression-root obligation of the sharing builder. -/
theorem buildConstantWithSharing_canonical_wireWF
    (info : Ixon.ConstantInfo) {state : Ix.CompileM.BlockState}
    (hinfo : info.wireWF) (htables : BlockWireTablesWF state) :
    (Ix.CompileM.buildConstantWithSharing info
      (Ix.CompileM.constantInfoRootExprs info)
      state.refs state.univs).wireWF :=
  buildConstantWithSharing_wireWF info _ hinfo
    (constantInfoRootExprs_wireWF info hinfo) htables

/-- The production axiom builder lies in the constant codec's wire domain for
both empty and nonempty sharing results. -/
theorem buildConstantWithSharing_axiom_wireWF
    {isUnsafe : Bool} {lvls : UInt64} {typ : Ixon.Expr}
    {state : Ix.CompileM.BlockState}
    (htyp : typ.wireWF) (htables : BlockWireTablesWF state) :
    (Ix.CompileM.buildConstantWithSharing
      (.axio { isUnsafe, lvls, typ }) #[typ]
      state.refs state.univs).wireWF := by
  apply buildConstantWithSharing_wireWF
  · exact htyp
  · intro expr hmem
    simp at hmem
    subst expr
    exact htyp
  · exact htables

/-- The production quotient builder lies in the constant codec's wire domain
for both empty and nonempty sharing results. -/
theorem buildConstantWithSharing_quotient_wireWF
    {kind : Ix.QuotKind} {lvls : UInt64} {typ : Ixon.Expr}
    {state : Ix.CompileM.BlockState}
    (htyp : typ.wireWF) (htables : BlockWireTablesWF state) :
    (Ix.CompileM.buildConstantWithSharing
      (.quot { kind, lvls, typ }) #[typ]
      state.refs state.univs).wireWF := by
  apply buildConstantWithSharing_wireWF
  · exact htyp
  · intro expr hmem
    simp at hmem
    subst expr
    exact htyp
  · exact htables

/-- The production definition builder lies in the constant codec's wire
domain for both empty and nonempty sharing results. -/
theorem buildConstantWithSharing_definition_wireWF
    {kind : Ix.DefKind} {safety : Ix.DefinitionSafety} {lvls : UInt64}
    {typ value : Ixon.Expr} {state : Ix.CompileM.BlockState}
    (htyp : typ.wireWF) (hvalue : value.wireWF)
    (htables : BlockWireTablesWF state) :
    (Ix.CompileM.buildConstantWithSharing
      (.defn { kind, safety, lvls, typ, value }) #[typ, value]
      state.refs state.univs).wireWF := by
  apply buildConstantWithSharing_wireWF
  · exact ⟨htyp, hvalue⟩
  · intro expr hmem
    simp at hmem
    rcases hmem with rfl | rfl
    · exact htyp
    · exact hvalue
  · exact htables

/-- The production recursor builder preserves its counted rule array and lies
in the constant codec's wire domain for empty or nonempty sharing. -/
theorem buildConstantWithSharing_recursor_wireWF
    (recursor : Ixon.Recursor) (rootExprs : Array Ixon.Expr)
    {state : Ix.CompileM.BlockState} (hrecursor : recursor.wireWF)
    (hroots : ExprArrayWireWF rootExprs)
    (htables : BlockWireTablesWF state) :
    (Ix.CompileM.buildConstantWithSharing (.recr recursor) rootExprs
      state.refs state.univs).wireWF := by
  exact buildConstantWithSharing_wireWF
    (.recr recursor) rootExprs hrecursor hroots htables

/-- The production mutual-block builder preserves the member count and every
nested definition, inductive, constructor, recursor, and rule wire condition. -/
theorem buildConstantWithSharing_mutual_wireWF
    (members : Array Ixon.MutConst) (rootExprs : Array Ixon.Expr)
    {state : Ix.CompileM.BlockState}
    (hmembersCount : members.size < UInt64.size)
    (hmembers : ∀ member ∈ members, member.wireWF)
    (hroots : ExprArrayWireWF rootExprs)
    (htables : BlockWireTablesWF state) :
    (Ix.CompileM.buildConstantWithSharing (.muts members) rootExprs
      state.refs state.univs).wireWF := by
  exact buildConstantWithSharing_wireWF
    (.muts members) rootExprs ⟨hmembersCount, hmembers⟩ hroots htables

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

/-- Building any wire-safe `ConstantInfo` with any wire-safe sharing roots and
then wrapping it in the production `BlockResult` yields stored bytes that
decode exactly to the built block.  This includes all projection variants and
both empty and nonempty sharing results. -/
theorem BlockResult.constantInfo_codec_roundtrip
    (info : Ixon.ConstantInfo) (rootExprs : Array Ixon.Expr)
    {state : Ix.CompileM.BlockState} (blockMeta : Ixon.ConstantMeta)
    (hinfo : info.wireWF) (hroots : ExprArrayWireWF rootExprs)
    (htables : BlockWireTablesWF state)
    (projections : Array
      (Ix.Name × Ixon.Constant × Ixon.ConstantMeta) := #[]) :
    let block := Ix.CompileM.buildConstantWithSharing
      info rootExprs state.refs state.univs
    Ixon.deConstant
        (Ix.CompileM.BlockResult.mk'
          block blockMeta projections).blockBytes = .ok block := by
  dsimp only
  apply BlockResult.mk'_codec_roundtrip
  exact buildConstantWithSharing_wireWF
    info rootExprs hinfo hroots htables

/-- The production singleton-driver tail is observationally a read of the
current block state followed by the pure sharing builder and canonical
`BlockResult` constructor; it leaves the state unchanged. -/
theorem finishConstantWithSharing_run
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (info : Ixon.ConstantInfo) (rootExprs : Array Ixon.Expr)
    (blockMeta : Ixon.ConstantMeta := .empty) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.finishConstantWithSharing info rootExprs blockMeta) =
      .ok (Ix.CompileM.BlockResult.mk'
        (Ix.CompileM.buildConstantWithSharing
          info rootExprs state.refs state.univs)
        blockMeta, state) := by
  rfl

/-- The exact production tail used by singleton declaration branches returns
a wire-safe, exactly decodable block whenever compilation has established the
wire conditions for its payload, roots, and final tables. -/
theorem finishConstantWithSharing_run_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (info : Ixon.ConstantInfo) (rootExprs : Array Ixon.Expr)
    (blockMeta : Ixon.ConstantMeta) (hinfo : info.wireWF)
    (hroots : ExprArrayWireWF rootExprs)
    (htables : BlockWireTablesWF state) :
    let result := Ix.CompileM.BlockResult.mk'
      (Ix.CompileM.buildConstantWithSharing
        info rootExprs state.refs state.univs)
      blockMeta
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.finishConstantWithSharing info rootExprs blockMeta) =
        .ok (result, state) ∧
      BlockResultCodecWF result := by
  dsimp only
  constructor
  · exact finishConstantWithSharing_run
      compileEnv blockEnv state info rootExprs blockMeta
  · apply BlockResult.mk'_codecWF
    exact buildConstantWithSharing_wireWF
      info rootExprs hinfo hroots htables

/-- The canonical singleton-driver tail has the same exact run equation as
the arbitrary-root helper, specialized to roots derived from its payload. -/
theorem finishConstantInfoWithSharing_run
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (info : Ixon.ConstantInfo)
    (blockMeta : Ixon.ConstantMeta := .empty) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.finishConstantInfoWithSharing info blockMeta) =
      .ok (Ix.CompileM.BlockResult.mk'
        (Ix.CompileM.buildConstantWithSharing info
          (Ix.CompileM.constantInfoRootExprs info)
          state.refs state.univs)
        blockMeta, state) := by
  exact finishConstantWithSharing_run compileEnv blockEnv state info
    (Ix.CompileM.constantInfoRootExprs info) blockMeta

/-- Every wire-safe payload reaching the exact tail used by the six singleton
`compileConstantInfo` branches returns a wire-safe and exactly decodable main
block; no separate root-array hypothesis remains. -/
theorem finishConstantInfoWithSharing_run_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (info : Ixon.ConstantInfo) (blockMeta : Ixon.ConstantMeta)
    (hinfo : info.wireWF) (htables : BlockWireTablesWF state) :
    let result := Ix.CompileM.BlockResult.mk'
      (Ix.CompileM.buildConstantWithSharing info
        (Ix.CompileM.constantInfoRootExprs info)
        state.refs state.univs)
      blockMeta
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.finishConstantInfoWithSharing info blockMeta) =
        .ok (result, state) ∧
      BlockResultCodecWF result := by
  simpa [Ix.CompileM.finishConstantInfoWithSharing] using
    finishConstantWithSharing_run_codecWF compileEnv blockEnv state info
      (Ix.CompileM.constantInfoRootExprs info) blockMeta hinfo
      (constantInfoRootExprs_wireWF info hinfo) htables

/-- The actual axiom builder, including nonempty sharing, stores bytes that
decode to its block. -/
theorem BlockResult.axiom_codec_roundtrip
    {isUnsafe : Bool} {lvls : UInt64} {typ : Ixon.Expr}
    {state : Ix.CompileM.BlockState} (blockMeta : Ixon.ConstantMeta)
    (htyp : typ.wireWF) (htables : BlockWireTablesWF state) :
    let block := Ix.CompileM.buildConstantWithSharing
      (.axio { isUnsafe, lvls, typ }) #[typ] state.refs state.univs
    Ixon.deConstant
        (Ix.CompileM.BlockResult.mk' block blockMeta).blockBytes = .ok block := by
  dsimp only
  apply BlockResult.mk'_codec_roundtrip
  exact buildConstantWithSharing_axiom_wireWF htyp htables

/-- The actual quotient builder, including nonempty sharing, stores bytes that
decode to its block. -/
theorem BlockResult.quotient_codec_roundtrip
    {kind : Ix.QuotKind} {lvls : UInt64} {typ : Ixon.Expr}
    {state : Ix.CompileM.BlockState} (blockMeta : Ixon.ConstantMeta)
    (htyp : typ.wireWF) (htables : BlockWireTablesWF state) :
    let block := Ix.CompileM.buildConstantWithSharing
      (.quot { kind, lvls, typ }) #[typ] state.refs state.univs
    Ixon.deConstant
        (Ix.CompileM.BlockResult.mk' block blockMeta).blockBytes = .ok block := by
  dsimp only
  apply BlockResult.mk'_codec_roundtrip
  exact buildConstantWithSharing_quotient_wireWF htyp htables

/-- The actual definition builder, including nonempty sharing, stores bytes
that decode to its block. -/
theorem BlockResult.definition_codec_roundtrip
    {kind : Ix.DefKind} {safety : Ix.DefinitionSafety} {lvls : UInt64}
    {typ value : Ixon.Expr} {state : Ix.CompileM.BlockState}
    (blockMeta : Ixon.ConstantMeta) (htyp : typ.wireWF)
    (hvalue : value.wireWF) (htables : BlockWireTablesWF state) :
    let block := Ix.CompileM.buildConstantWithSharing
      (.defn { kind, safety, lvls, typ, value }) #[typ, value]
      state.refs state.univs
    Ixon.deConstant
        (Ix.CompileM.BlockResult.mk' block blockMeta).blockBytes = .ok block := by
  dsimp only
  apply BlockResult.mk'_codec_roundtrip
  exact buildConstantWithSharing_definition_wireWF htyp hvalue htables

/-- The actual recursor builder, including nonempty sharing, stores bytes that
decode to its block. -/
theorem BlockResult.recursor_codec_roundtrip
    (recursor : Ixon.Recursor) (rootExprs : Array Ixon.Expr)
    {state : Ix.CompileM.BlockState} (blockMeta : Ixon.ConstantMeta)
    (hrecursor : recursor.wireWF) (hroots : ExprArrayWireWF rootExprs)
    (htables : BlockWireTablesWF state) :
    let block := Ix.CompileM.buildConstantWithSharing
      (.recr recursor) rootExprs state.refs state.univs
    Ixon.deConstant
        (Ix.CompileM.BlockResult.mk' block blockMeta).blockBytes = .ok block := by
  dsimp only
  apply BlockResult.mk'_codec_roundtrip
  exact buildConstantWithSharing_recursor_wireWF
    recursor rootExprs hrecursor hroots htables

/-- The actual mutual-block builder, including nonempty sharing, stores bytes
that decode to its block. -/
theorem BlockResult.mutual_codec_roundtrip
    (members : Array Ixon.MutConst) (rootExprs : Array Ixon.Expr)
    {state : Ix.CompileM.BlockState} (blockMeta : Ixon.ConstantMeta)
    (hmembersCount : members.size < UInt64.size)
    (hmembers : ∀ member ∈ members, member.wireWF)
    (hroots : ExprArrayWireWF rootExprs)
    (htables : BlockWireTablesWF state) :
    let block := Ix.CompileM.buildConstantWithSharing
      (.muts members) rootExprs state.refs state.univs
    Ixon.deConstant
        (Ix.CompileM.BlockResult.mk' block blockMeta).blockBytes = .ok block := by
  dsimp only
  apply BlockResult.mk'_codec_roundtrip
  exact buildConstantWithSharing_mutual_wireWF members rootExprs
    hmembersCount hmembers hroots htables

/-- The actual no-sharing axiom builder, wrapped in the production block
result, stores bytes that decode to its block. -/
theorem BlockResult.axiom_noSharing_codec_roundtrip
    {isUnsafe : Bool} {lvls : UInt64} {typ : Ixon.Expr}
    {state : Ix.CompileM.BlockState} (blockMeta : Ixon.ConstantMeta)
    (hsharing : Ix.Sharing.applySharing #[typ] = (#[typ], #[]))
    (htyp : typ.wireWF) (htables : BlockWireTablesWF state) :
    let block := Ix.CompileM.buildConstantWithSharing
      (.axio { isUnsafe, lvls, typ }) #[typ] state.refs state.univs
    Ixon.deConstant
        (Ix.CompileM.BlockResult.mk' block blockMeta).blockBytes = .ok block := by
  dsimp only
  apply BlockResult.mk'_codec_roundtrip
  exact buildConstantWithSharing_axiom_noSharing_wireWF
    hsharing htyp htables

/-- The actual no-sharing definition builder, wrapped in the production block
result, stores bytes that decode to its block. -/
theorem BlockResult.definition_noSharing_codec_roundtrip
    {kind : Ix.DefKind} {safety : Ix.DefinitionSafety} {lvls : UInt64}
    {typ value : Ixon.Expr} {state : Ix.CompileM.BlockState}
    (blockMeta : Ixon.ConstantMeta)
    (hsharing : Ix.Sharing.applySharing #[typ, value] =
      (#[typ, value], #[]))
    (htyp : typ.wireWF) (hvalue : value.wireWF)
    (htables : BlockWireTablesWF state) :
    let block := Ix.CompileM.buildConstantWithSharing
      (.defn { kind, safety, lvls, typ, value }) #[typ, value]
      state.refs state.univs
    Ixon.deConstant
        (Ix.CompileM.BlockResult.mk' block blockMeta).blockBytes = .ok block := by
  dsimp only
  apply BlockResult.mk'_codec_roundtrip
  exact buildConstantWithSharing_definition_noSharing_wireWF
    hsharing htyp hvalue htables

/-- The ordinary axiom expression phase followed by the actual no-sharing
production block builder yields stored bytes that decode to the built block. -/
theorem compileExpr_run_ordinary_axiomBlock_noSharing_roundtrip
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
      (frozenRefCompileCtx compileEnv blockEnv snapshot) source = some target)
    (hsharing : Ix.Sharing.applySharing #[target] = (#[target], #[])) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr source) =
        .ok ((target, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      (let block := Ix.CompileM.buildConstantWithSharing
          (.axio { isUnsafe, lvls, typ := target }) #[target]
          state'.refs state'.univs
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
  have hblock :
      (Ix.CompileM.buildConstantWithSharing
        (.axio { isUnsafe, lvls, typ := target }) #[target]
        state'.refs state'.univs).wireWF := by
    rw [buildConstantWithSharing_axiom_eq_unshared
      isUnsafe lvls target state' hsharing]
    exact hunshared
  exact ⟨hblock, BlockResult.mk'_codec_roundtrip _ blockMeta #[] hblock⟩

/-- The sequential definition expression phase followed by the actual
no-sharing production block builder yields stored bytes that decode to the
built block. -/
theorem compileExpr_run_ordinary_definitionBlock_noSharing_roundtrip
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
        some targetValue)
    (hsharing : Ix.Sharing.applySharing #[targetType, targetValue] =
      (#[targetType, targetValue], #[])) :
    ∃ typeRoot middle valueRoot state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr sourceType) =
        .ok ((targetType, typeRoot), middle) ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot middle ∧
      Ix.CompileM.CompileM.run compileEnv blockEnv middle
          (Ix.CompileM.compileExpr sourceValue) =
        .ok ((targetValue, valueRoot), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      (let block := Ix.CompileM.buildConstantWithSharing
          (.defn ⟨kind, safety, lvls, targetType, targetValue⟩)
          #[targetType, targetValue]
          state'.refs state'.univs
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
  have hblock :
      (Ix.CompileM.buildConstantWithSharing
        (.defn ⟨kind, safety, lvls, targetType, targetValue⟩)
        #[targetType, targetValue]
        state'.refs state'.univs).wireWF := by
    rw [buildConstantWithSharing_definition_eq_unshared
      kind safety lvls targetType targetValue state' hsharing]
    exact hunshared
  exact ⟨hblock, BlockResult.mk'_codec_roundtrip _ blockMeta #[] hblock⟩

/-- The ordinary axiom expression phase followed by the complete production
sharing builder yields a wire-safe block whose stored bytes decode exactly. -/
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
      (let block := Ix.CompileM.buildConstantWithSharing
          (.axio { isUnsafe, lvls, typ := target }) #[target]
          state'.refs state'.univs
       block.wireWF ∧
         Ixon.deConstant
            (Ix.CompileM.BlockResult.mk' block blockMeta).blockBytes =
          .ok block) := by
  obtain ⟨root, state', hrun, hstate', hunshared, _⟩ :=
    compileExpr_run_ordinary_axiomConstant_roundtrip compileEnv blockEnv
      snapshot hfree hclosed hlevelFaithful hexprFaithful htables
      isUnsafe lvls hsource hbound hstate href
  have htables' : BlockWireTablesWF state' :=
    htables.of_exprTableView_eq hstate'.tables
  refine ⟨root, state', hrun, hstate', ?_⟩
  dsimp only
  have hblock := buildConstantWithSharing_axiom_wireWF
    (isUnsafe := isUnsafe) (lvls := lvls) hunshared.1 htables'
  exact ⟨hblock, BlockResult.mk'_codec_roundtrip _ blockMeta #[] hblock⟩

/-- Sequential ordinary compilation of a definition's type and value followed
by complete production sharing yields a wire-safe, exactly decodable block. -/
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
      (let block := Ix.CompileM.buildConstantWithSharing
          (.defn ⟨kind, safety, lvls, targetType, targetValue⟩)
          #[targetType, targetValue] state'.refs state'.univs
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
  have htables' : BlockWireTablesWF state' :=
    htables.of_exprTableView_eq hstate'.tables
  refine ⟨typeRoot, middle, valueRoot, state', htypeRun, hmiddle,
    hvalueRun, hstate', ?_⟩
  dsimp only
  have hblock := buildConstantWithSharing_definition_wireWF
    (kind := kind) (safety := safety) (lvls := lvls)
    hunshared.1.1 hunshared.1.2 htables'
  exact ⟨hblock, BlockResult.mk'_codec_roundtrip _ blockMeta #[] hblock⟩

end Ix.Compile.Verify
