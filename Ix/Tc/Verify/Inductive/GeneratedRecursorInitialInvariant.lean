import Ix.Tc.Verify.Inductive.GeneratedRecursorMemberFixture

/-!
# Concrete generated-recursor ingress invariant

This module discharges the finite, state-specific obligations needed to enter
the production `IndexedVec.rec` member check under active coordinated-block
authority.  It begins with collision freedom for the exact ingress plus
rule-population footprint.  The proof uses the coherent intern tables as
canonical finite maps; it does not assume injectivity of Blake3 outside that
run.
-/

namespace Ix.Tc.IndexedRecursiveFixture

open Lean4Lean
open Lean4Lean.InductiveFixtures
open Lean4Lean.InductiveReplayFixtures
open IndexedRecursiveCertificateFixture

local instance initialInvariantKConstDecidableEq :
    DecidableEq (KConst .anon) :=
  AnonStructural.constDecidableEq

local instance initialInvariantAddressDecidableEq : DecidableEq Address :=
  AnonStructural.addressDecidableEq

local instance initialInvariantKIdDecidableEq : DecidableEq (KId .anon) :=
  AnonStructural.idDecidableEq

local instance initialInvariantKUnivDecidableEq :
    DecidableEq (KUniv .anon) :=
  AnonStructural.decidableEqOfRoundtrip AnonStructural.Univ.ofKernel
    AnonStructural.Univ.toKernel AnonStructural.Univ.roundtrip

local instance initialInvariantKExprDecidableEq :
    DecidableEq (KExpr .anon) :=
  AnonStructural.exprDecidableEq

local instance initialInvariantVConstantDecidableEq :
    DecidableEq VConstant := by
  intro left right
  cases left
  cases right
  simp only [VConstant.mk.injEq]
  infer_instance

/-! ## Constructive collision freedom -/

/-- Every expression in the complete member-check footprint occurs in the
post-population intern table.  Old bindings are retained exactly and the
second support summand is, by definition, a genuinely new post binding. -/
theorem familyMemberSupport_populationSupport
    {expression : KExpr .anon}
    (supported : familyMemberSupport expression) :
    familyMemberRulePopulationAfter.env.intern.ExprSupport expression := by
  change familyMemberInitial.env.intern.ExprSupport expression ∨
    FamilyMemberPopulationNewExpr expression at supported
  rcases supported with old | new
  · rcases old with ⟨address, lookup⟩
    exact ⟨address, familyMemberRulePopulationExprExtends lookup⟩
  · rcases new with ⟨address, lookup, _absent⟩
    exact ⟨address, lookup⟩

/-- Equal expression addresses inside the exact finite run identify the same
post-population intern binding. -/
private theorem familyMemberSupport_expr_eq_of_addr_eq
    {left right : KExpr .anon}
    (leftSupported : familyMemberSupport left)
    (rightSupported : familyMemberSupport right)
    (addressEq : left.addr = right.addr) : left = right := by
  rcases familyMemberSupport_populationSupport leftSupported with
    ⟨leftKey, leftLookup⟩
  rcases familyMemberSupport_populationSupport rightSupported with
    ⟨rightKey, rightLookup⟩
  have leftKeyEq : left.addr = leftKey := by
    simpa [KExpr.internKey] using
      familyMemberRulePopulationInternWF.expr_key leftLookup
  have rightKeyEq : right.addr = rightKey := by
    simpa [KExpr.internKey] using
      familyMemberRulePopulationInternWF.expr_key rightLookup
  have keyEq : leftKey = rightKey :=
    leftKeyEq.symm.trans (addressEq.trans rightKeyEq)
  have valuesEq : some left = some right := by
    calc
      some left =
          familyMemberRulePopulationAfter.env.intern.exprs[leftKey]? :=
        leftLookup.symm
      _ = familyMemberRulePopulationAfter.env.intern.exprs[rightKey]? := by
        rw [keyEq]
      _ = some right := rightLookup
  exact Option.some.inj valuesEq

/-- Equal universe addresses inside the exact finite run identify the same
ingress intern binding.  Rule population introduces no new universes. -/
private theorem familyMemberSupport_univ_eq_of_addr_eq
    {left right : KUniv .anon}
    (leftSupported : familyMemberSupport.univ left)
    (rightSupported : familyMemberSupport.univ right)
    (addressEq : left.addr = right.addr) : left = right := by
  rcases leftSupported with ⟨leftKey, leftLookup⟩
  rcases rightSupported with ⟨rightKey, rightLookup⟩
  have leftKeyEq : left.addr = leftKey :=
    familyMemberInitial_internWF.univ_key leftLookup
  have rightKeyEq : right.addr = rightKey :=
    familyMemberInitial_internWF.univ_key rightLookup
  have keyEq : leftKey = rightKey :=
    leftKeyEq.symm.trans (addressEq.trans rightKeyEq)
  have valuesEq : some left = some right := by
    calc
      some left = familyMemberInitial.env.intern.univs[leftKey]? :=
        leftLookup.symm
      _ = familyMemberInitial.env.intern.univs[rightKey]? := by rw [keyEq]
      _ = some right := rightLookup
  exact Option.some.inj valuesEq

/-- The exact finite run support is collision-free by intern-table
functionality and key coherence.  No global address-injectivity hypothesis is
used. -/
theorem familyMemberSupport_collisionFree :
    familyMemberSupport.CollisionFree where
  expr := by
    intro left leftSupported right rightSupported addressEq
    have equality := familyMemberSupport_expr_eq_of_addr_eq
      leftSupported rightSupported addressEq
    simpa only [KExpr.eraseMeta_anon] using equality
  univ := by
    intro left leftSupported right rightSupported addressEq
    have equality := familyMemberSupport_univ_eq_of_addr_eq
      leftSupported rightSupported addressEq
    simpa only [KUniv.eraseMeta_anon] using equality

/-! ## Closed suffix representation -/

/-- The concrete suffix model represents only the empty semantic context.
This is recovered from membership in its singleton composite-digest scope,
not from equality of context hashes. -/
theorem familyMemberModel_represents_nil
    {lbr : UInt64} {ctxAddr : Address} {Delta : KVLCtx}
    (represented : familyMemberModel.keys.Represents lbr ctxAddr Delta) :
    Delta = [] := by
  rcases represented with
    ⟨_before, _after, _valid, _context, _run, captured⟩
  change Delta ∈ ([[]] : List KVLCtx) at captured
  exact List.mem_singleton.mp captured

/-! ## Typed trusted declaration inputs -/

/-- Syntax conditions under which a raw trusted declaration type can be
upgraded to the checked structural translation consumed by inference. -/
private def TrustedTypeSyntax (constant : KConst .anon) : Prop :=
  constant.ty.binderCore = true ∧
    constant.ty.Scoped 0 constant.lvls.toNat ∧
    constant.ty.size < UInt64.size

private instance trustedTypeSyntaxDecidable (constant : KConst .anon) :
    Decidable (TrustedTypeSyntax constant) := by
  unfold TrustedTypeSyntax
  infer_instance

private def familyMemberTypedConstants : List (KConst .anon) :=
  [natConcrete, zeroConcrete, succConcrete, familyConcrete, nilConcrete,
    consConcrete]

private theorem familyMemberTypedConstantSyntaxNative :
    familyMemberTypedConstants.all
      (fun constant => decide (TrustedTypeSyntax constant)) = true := by
  native_decide

private theorem familyMemberTypedConstantSyntax
    {constant : KConst .anon}
    (member : constant ∈ familyMemberTypedConstants) :
    TrustedTypeSyntax constant := by
  have all := List.all_eq_true.mp familyMemberTypedConstantSyntaxNative
  exact of_decide_eq_true (all constant member)

/-- A trusted declaration from the concrete Nat/IndexedVec environment has a
fully typed structural translation of its stored type.  The semantic typing
fact comes from admission; native evaluation establishes only the finite
source-syntax side conditions above. -/
private theorem familyMemberTrustedTypeTyped
    {id : KId .anon} {constant : KConst .anon} {name : Lean.Name}
    {info : VConstant}
    (resolved : TrustedConstRel RawProjRel.none familyAcceptedWorld id
      constant name info)
    (syntaxFacts : TrustedTypeSyntax constant) :
    TrKExprS familyAcceptedWorld.venv info.uvars
      familyAcceptedWorld.nameOf RawProjRel.none [] constant.ty info.type := by
  have typeScoped : constant.ty.Scoped 0 info.uvars := by
    simpa only [resolved.uvars] using syntaxFacts.2.1
  have raw : RawExprRel (uvars := info.uvars) familyAcceptedWorld.venv
      familyAcceptedWorld.nameOf RawProjRel.none [] constant.ty info.type := by
    simpa only [resolved.uvars] using resolved.type
  have pre := raw.toPreBinderCore_of_scoped syntaxFacts.1 typeScoped
    syntaxFacts.2.2
  obtain ⟨sortLevel, typeHasType⟩ := resolved.wf
  exact pre.upgradeBinderCoreOfWF familyAcceptedWorld.venvWF
    (Delta := []) (hDelta := trivial) syntaxFacts.1
    (by exact ⟨.sort sortLevel, typeHasType⟩)

private theorem familyMemberNatTrusted : familyAcceptedWorld.trusted natId :=
  familyMemberNatBlockTrusted (by native_decide)

private theorem familyMemberZeroTrusted :
    familyAcceptedWorld.trusted zeroId :=
  familyMemberNatBlockTrusted (by native_decide)

private theorem familyMemberSuccTrusted :
    familyAcceptedWorld.trusted succId :=
  familyMemberNatBlockTrusted (by native_decide)

private theorem familyMemberFamilyTrusted :
    familyAcceptedWorld.trusted familyId :=
  familyAtomicAdmission.memberTrusted (by simp [familyMembers_eq])

private theorem familyMemberNilTrusted : familyAcceptedWorld.trusted nilId :=
  familyAtomicAdmission.memberTrusted (by simp [familyMembers_eq])

private theorem familyMemberConsTrusted :
    familyAcceptedWorld.trusted consId :=
  familyAtomicAdmission.memberTrusted (by simp [familyMembers_eq])

private theorem familyMemberResolveNat :
    ∃ name info, TrustedConstRel RawProjRel.none familyAcceptedWorld natId
      natConcrete name info :=
  familyAtomicAdmission.trustedCatalog.resolve familyMemberNatTrusted
    (by simpa [familyAcceptedWorld,
      SemanticBlockTransitionCertificate.admittedWorld, world] using
      catalog_nat)

private theorem familyMemberResolveZero :
    ∃ name info, TrustedConstRel RawProjRel.none familyAcceptedWorld zeroId
      zeroConcrete name info :=
  familyAtomicAdmission.trustedCatalog.resolve familyMemberZeroTrusted
    (by simpa [familyAcceptedWorld,
      SemanticBlockTransitionCertificate.admittedWorld, world] using
      catalog_zero)

private theorem familyMemberResolveSucc :
    ∃ name info, TrustedConstRel RawProjRel.none familyAcceptedWorld succId
      succConcrete name info :=
  familyAtomicAdmission.trustedCatalog.resolve familyMemberSuccTrusted
    (by simpa [familyAcceptedWorld,
      SemanticBlockTransitionCertificate.admittedWorld, world] using
      catalog_succ)

private theorem familyMemberResolveFamily :
    ∃ name info, TrustedConstRel RawProjRel.none familyAcceptedWorld familyId
      familyConcrete name info :=
  familyAtomicAdmission.trustedCatalog.resolve familyMemberFamilyTrusted
    (by simpa [familyAcceptedWorld,
      SemanticBlockTransitionCertificate.admittedWorld, world] using
      catalog_family)

private theorem familyMemberResolveNil :
    ∃ name info, TrustedConstRel RawProjRel.none familyAcceptedWorld nilId
      nilConcrete name info :=
  familyAtomicAdmission.trustedCatalog.resolve familyMemberNilTrusted
    (by simpa [familyAcceptedWorld,
      SemanticBlockTransitionCertificate.admittedWorld, world] using
      catalog_nil)

private theorem familyMemberResolveCons :
    ∃ name info, TrustedConstRel RawProjRel.none familyAcceptedWorld consId
      consConcrete name info :=
  familyAtomicAdmission.trustedCatalog.resolve familyMemberConsTrusted
    (by simpa [familyAcceptedWorld,
      SemanticBlockTransitionCertificate.admittedWorld, world] using
      catalog_cons)

/-! ## Exact declaration typing -/

/-- Pin existential trusted resolution to the concrete Theory name and
constant installed by the two accepted fixture blocks. -/
private theorem familyMemberResolveExact
    {id : KId .anon} {constant : KConst .anon}
    {expectedName : Lean.Name} {expectedInfo : VConstant}
    (resolved : ∃ name info,
      TrustedConstRel RawProjRel.none familyAcceptedWorld id constant
        name info)
    (nameLookup : familyAcceptedWorld.nameOf id.addr = some expectedName)
    (infoLookup : familyAcceptedWorld.venv.constants expectedName =
      some expectedInfo) :
    TrustedConstRel RawProjRel.none familyAcceptedWorld id constant
      expectedName expectedInfo := by
  obtain ⟨name, info, relation⟩ := resolved
  have nameEq : name = expectedName :=
    Option.some.inj (relation.nameEq.symm.trans nameLookup)
  subst name
  have infoEq : info = expectedInfo :=
    Option.some.inj (relation.lookup.symm.trans infoLookup)
  subst info
  exact relation

private theorem familyMemberNatInfoLookup :
    familyAcceptedWorld.venv.constants ``Nat =
      some Lean4Lean.InductiveFixtures.natType.toVConstant := by
  native_decide

private theorem familyMemberZeroInfoLookup :
    familyAcceptedWorld.venv.constants ``Nat.zero =
      some Lean4Lean.InductiveFixtures.natType.ctors[0].toVConstant := by
  native_decide

private theorem familyMemberSuccInfoLookup :
    familyAcceptedWorld.venv.constants ``Nat.succ =
      some Lean4Lean.InductiveFixtures.natType.ctors[1].toVConstant := by
  native_decide

private theorem familyMemberFamilyInfoLookup :
    familyAcceptedWorld.venv.constants ``IndexedVec =
      some Lean4Lean.InductiveFixtures.indexedVecType.toVConstant := by
  native_decide

private theorem familyMemberNilInfoLookup :
    familyAcceptedWorld.venv.constants ``IndexedVec.nil =
      some Lean4Lean.InductiveFixtures.indexedVecType.ctors[0].toVConstant := by
  native_decide

private theorem familyMemberConsInfoLookup :
    familyAcceptedWorld.venv.constants ``IndexedVec.cons =
      some Lean4Lean.InductiveFixtures.indexedVecType.ctors[1].toVConstant := by
  native_decide

private theorem familyMemberResolveNatExact :
    TrustedConstRel RawProjRel.none familyAcceptedWorld natId natConcrete
      ``Nat Lean4Lean.InductiveFixtures.natType.toVConstant := by
  apply familyMemberResolveExact familyMemberResolveNat
  · simpa only [familyAcceptedWorld_nameOf_eq] using nameOf_nat
  · exact familyMemberNatInfoLookup

private theorem familyMemberResolveZeroExact :
    TrustedConstRel RawProjRel.none familyAcceptedWorld zeroId zeroConcrete
      ``Nat.zero
      Lean4Lean.InductiveFixtures.natType.ctors[0].toVConstant := by
  apply familyMemberResolveExact familyMemberResolveZero
  · simpa only [familyAcceptedWorld_nameOf_eq] using nameOf_zero
  · exact familyMemberZeroInfoLookup

private theorem familyMemberResolveSuccExact :
    TrustedConstRel RawProjRel.none familyAcceptedWorld succId succConcrete
      ``Nat.succ
      Lean4Lean.InductiveFixtures.natType.ctors[1].toVConstant := by
  apply familyMemberResolveExact familyMemberResolveSucc
  · simpa only [familyAcceptedWorld_nameOf_eq] using nameOf_succ
  · exact familyMemberSuccInfoLookup

private theorem familyMemberResolveFamilyExact :
    TrustedConstRel RawProjRel.none familyAcceptedWorld familyId familyConcrete
      ``IndexedVec
      Lean4Lean.InductiveFixtures.indexedVecType.toVConstant := by
  apply familyMemberResolveExact familyMemberResolveFamily
  · simpa only [familyAcceptedWorld_nameOf_eq] using nameOf_family
  · exact familyMemberFamilyInfoLookup

private theorem familyMemberResolveNilExact :
    TrustedConstRel RawProjRel.none familyAcceptedWorld nilId nilConcrete
      ``IndexedVec.nil
      Lean4Lean.InductiveFixtures.indexedVecType.ctors[0].toVConstant := by
  apply familyMemberResolveExact familyMemberResolveNil
  · simpa only [familyAcceptedWorld_nameOf_eq] using nameOf_nil
  · exact familyMemberNilInfoLookup

private theorem familyMemberResolveConsExact :
    TrustedConstRel RawProjRel.none familyAcceptedWorld consId consConcrete
      ``IndexedVec.cons
      Lean4Lean.InductiveFixtures.indexedVecType.ctors[1].toVConstant := by
  apply familyMemberResolveExact familyMemberResolveCons
  · simpa only [familyAcceptedWorld_nameOf_eq] using nameOf_cons
  · exact familyMemberConsInfoLookup

private theorem familyMemberNatTypeHasType :
    familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars []
      Lean4Lean.InductiveFixtures.natType.type
      (.sort (.succ (.succ .zero))) := by
  type_tac

private theorem familyMemberZeroTypeHasType :
    familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars []
      Lean4Lean.InductiveFixtures.natType.ctors[0].type
      Lean4Lean.InductiveFixtures.natType.type := by
  have hNat := familyMemberNatInfoLookup
  type_tac

private theorem familyMemberSuccTypeHasType :
    familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars []
      Lean4Lean.InductiveFixtures.natType.ctors[1].type
      (.sort (.succ .zero)) := by
  have raw : familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars []
      (.forallE (.const ``Nat []) (.const ``Nat []))
      (.sort (.imax (.succ .zero) (.succ .zero))) := by
    apply VEnv.HasType.forallE
    · exact VEnv.HasType.const familyMemberNatInfoLookup (by simp) rfl
    · exact VEnv.HasType.const familyMemberNatInfoLookup (by simp) rfl
  apply VEnv.IsDefEq.defeq
    (h1 := VEnv.IsDefEq.sortDF (by decide) (by decide) (by
      simpa using (VLevel.imax_self (a := VLevel.succ .zero))))
    raw

private theorem familyMemberFamilyTypeHasType :
    familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars []
      Lean4Lean.InductiveFixtures.indexedVecType.type
      (.sort (.max (.succ .zero) (.succ (.succ (.param 0))))) := by
  have raw : familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars []
      (.forallE (.sort (.succ (.param 0)))
        (.forallE (.const ``Nat []) (.sort (.succ (.param 0)))))
      (.sort (.imax (.succ (.succ (.param 0)))
        (.imax (.succ .zero) (.succ (.succ (.param 0)))))) := by
    apply VEnv.HasType.forallE
    · exact VEnv.HasType.sort (by decide)
    · apply VEnv.HasType.forallE
      · exact VEnv.HasType.const familyMemberNatInfoLookup (by simp) rfl
      · exact VEnv.HasType.sort (by decide)
  apply VEnv.IsDefEq.defeq
    (h1 := VEnv.IsDefEq.sortDF (by decide) (by decide) (by
      simp [VLevel.equiv_def, VLevel.eval, Lean.Nat.imax]))
    raw

private theorem familyMemberNilTypeHasType :
    familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars []
      Lean4Lean.InductiveFixtures.indexedVecType.ctors[0].type
      (.sort (.succ (.succ (.param 0)))) := by
  have raw : familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars []
      (.forallE (.sort (.succ (.param 0)))
        (.app
          (.app (.const ``IndexedVec [.param 0]) (.bvar 0))
          (.const ``Nat.zero [])))
      (.sort (.imax (.succ (.succ (.param 0))) (.succ (.param 0)))) := by
    have indexedVecApp : ∀ {Gamma : List VExpr} {alpha index : VExpr},
        familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars Gamma
          alpha (.sort (.succ (.param 0))) →
        familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars Gamma
          index (.const ``Nat []) →
        familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars Gamma
          (.app (.app (.const ``IndexedVec [.param 0]) alpha) index)
          (.sort (.succ (.param 0))) := by
      intro Gamma alpha index alphaTyped indexTyped
      have familyTyped : familyAcceptedWorld.venv.HasType
          familyMemberModel.keys.uvars Gamma (.const ``IndexedVec [.param 0])
          (.forallE (.sort (.succ (.param 0)))
            (.forallE (.const ``Nat []) (.sort (.succ (.param 0))))) := by
        exact VEnv.HasType.const' familyMemberFamilyInfoLookup
          (by decide) (by decide) rfl
      exact VEnv.HasType.app'
        (VEnv.HasType.app' familyTyped alphaTyped rfl) indexTyped rfl
    apply VEnv.HasType.forallE
    · exact VEnv.HasType.sort (by decide)
    · apply indexedVecApp
      · exact VEnv.HasType.bvar (by lookup_tac)
      · exact VEnv.HasType.const familyMemberZeroInfoLookup (by simp) rfl
  apply VEnv.IsDefEq.defeq
    (h1 := VEnv.IsDefEq.sortDF (by decide) (by decide) (by
      simp [VLevel.equiv_def, VLevel.eval, Lean.Nat.imax]))
    raw

private theorem familyMemberConsTypeHasType :
    familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars []
      Lean4Lean.InductiveFixtures.indexedVecType.ctors[1].type
      (.sort (.max (.succ (.succ (.param 0)))
        (.max (.succ .zero) (.succ (.param 0))))) := by
  have raw : familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars []
      Lean4Lean.InductiveFixtures.indexedVecType.ctors[1].type
      (.sort (.imax (.succ (.succ (.param 0)))
        (.imax (.succ .zero)
          (.imax (.succ (.param 0))
            (.imax (.succ (.param 0)) (.succ (.param 0))))))) := by
    have indexedVecApp : ∀ {Gamma : List VExpr} {alpha index : VExpr},
        familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars Gamma
          alpha (.sort (.succ (.param 0))) →
        familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars Gamma
          index (.const ``Nat []) →
        familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars Gamma
          (.app (.app (.const ``IndexedVec [.param 0]) alpha) index)
          (.sort (.succ (.param 0))) := by
      intro Gamma alpha index alphaTyped indexTyped
      have familyTyped : familyAcceptedWorld.venv.HasType
          familyMemberModel.keys.uvars Gamma (.const ``IndexedVec [.param 0])
          (.forallE (.sort (.succ (.param 0)))
            (.forallE (.const ``Nat []) (.sort (.succ (.param 0))))) := by
        exact VEnv.HasType.const' familyMemberFamilyInfoLookup
          (by decide) (by decide) rfl
      exact VEnv.HasType.app'
        (VEnv.HasType.app' familyTyped alphaTyped rfl) indexTyped rfl
    have natSuccApp : ∀ {Gamma : List VExpr} {index : VExpr},
        familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars Gamma
          index (.const ``Nat []) →
        familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars Gamma
          (.app (.const ``Nat.succ []) index) (.const ``Nat []) := by
      intro Gamma index indexTyped
      have succTyped : familyAcceptedWorld.venv.HasType
          familyMemberModel.keys.uvars Gamma (.const ``Nat.succ [])
          (.forallE (.const ``Nat []) (.const ``Nat [])) := by
        exact VEnv.HasType.const' familyMemberSuccInfoLookup
          (by decide) (by decide) rfl
      exact VEnv.HasType.app' succTyped indexTyped rfl
    change familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars []
      (.forallE (.sort (.succ (.param 0)))
        (.forallE (.const ``Nat [])
          (.forallE (.bvar 1)
            (.forallE
              (.app (.app (.const ``IndexedVec [.param 0]) (.bvar 2))
                (.bvar 1))
              (.app (.app (.const ``IndexedVec [.param 0]) (.bvar 3))
                (.app (.const ``Nat.succ []) (.bvar 2))))))) _
    apply VEnv.HasType.forallE
    · exact VEnv.HasType.sort (by decide)
    · apply VEnv.HasType.forallE
      · exact VEnv.HasType.const familyMemberNatInfoLookup (by simp) rfl
      · apply VEnv.HasType.forallE
        · exact VEnv.HasType.bvar (by lookup_tac)
        · apply VEnv.HasType.forallE
          · apply indexedVecApp
            · exact VEnv.HasType.bvar (by lookup_tac)
            · exact VEnv.HasType.bvar (by lookup_tac)
          · apply indexedVecApp
            · exact VEnv.HasType.bvar (by lookup_tac)
            · apply natSuccApp
              exact VEnv.HasType.bvar (by lookup_tac)
  apply VEnv.IsDefEq.defeq
    (h1 := VEnv.IsDefEq.sortDF (by decide) (by decide) (by
      simp [VLevel.equiv_def, VLevel.eval, Lean.Nat.imax]))
    raw

/-! ## Closed inference meanings -/

/-- Re-run the trusted raw type translation at the member checker's ambient
universe arity.  The concrete declaration's own arity controls its internal
parameter indices, but structural translation may occur in any larger
well-formed ambient universe context. -/
private theorem familyMemberTrustedTypeTypedAt
    {id : KId .anon} {constant : KConst .anon} {name : Lean.Name}
    {info : VConstant}
    (resolved : TrustedConstRel RawProjRel.none familyAcceptedWorld id
      constant name info)
    (syntaxFacts : TrustedTypeSyntax constant)
    (ambientScoped : constant.ty.Scoped 0 familyMemberModel.keys.uvars)
    (targetWF : VExpr.WF familyAcceptedWorld.venv
      familyMemberModel.keys.uvars [] info.type) :
    TrKExprS familyAcceptedWorld.venv familyMemberModel.keys.uvars
      familyAcceptedWorld.nameOf RawProjRel.none [] constant.ty info.type := by
  have raw := resolved.type.none_reindex
    (after := familyMemberModel.keys.uvars)
  have pre := raw.toPreBinderCore_of_scoped syntaxFacts.1 ambientScoped
    syntaxFacts.2.2
  exact pre.upgradeBinderCoreOfWF familyAcceptedWorld.venvWF
    (Delta := []) (hDelta := trivial) syntaxFacts.1 targetWF

private def familyMemberNatReference : KExpr .anon :=
  KExpr.mkConst natId #[] ()

private def familyMemberParamLevel : KUniv .anon := KUniv.mkParam 0 ()
private def familyMemberLevelOne : KUniv .anon :=
  KUniv.mkSucc KUniv.mkZero
private def familyMemberParamSucc : KUniv .anon :=
  KUniv.mkSucc familyMemberParamLevel
private def familyMemberParamSuccTwo : KUniv .anon :=
  KUniv.mkSucc familyMemberParamSucc
private def familyMemberLevelTwo : KUniv .anon :=
  KUniv.mkSucc familyMemberLevelOne
private def familyMemberFamilyResultLevel : KUniv .anon :=
  KUniv.mkMax familyMemberLevelOne familyMemberParamSuccTwo
private def familyMemberConsInnerResultLevel : KUniv .anon :=
  KUniv.mkMax familyMemberLevelOne familyMemberParamSucc
private def familyMemberConsResultLevel : KUniv .anon :=
  KUniv.mkMax familyMemberParamSuccTwo familyMemberConsInnerResultLevel

private theorem familyMemberFamilyResultLevel_raw :
    familyMemberFamilyResultLevel =
      KUniv.mkMaxRaw familyMemberLevelOne familyMemberParamSuccTwo := by
  native_decide

private theorem familyMemberConsInnerResultLevel_raw :
    familyMemberConsInnerResultLevel =
      KUniv.mkMaxRaw familyMemberLevelOne familyMemberParamSucc := by
  native_decide

private theorem familyMemberConsResultLevel_raw :
    familyMemberConsResultLevel =
      KUniv.mkMaxRaw familyMemberParamSuccTwo
        familyMemberConsInnerResultLevel := by
  native_decide

private theorem familyMemberFamilyResultLevel_toVLevel :
    familyMemberFamilyResultLevel.toVLevel =
      .max (.succ .zero) (.succ (.succ (.param 0))) := by
  rw [familyMemberFamilyResultLevel_raw, KUniv.toVLevel_mkMaxRaw]
  rfl

private theorem familyMemberConsResultLevel_toVLevel :
    familyMemberConsResultLevel.toVLevel =
      .max (.succ (.succ (.param 0)))
        (.max (.succ .zero) (.succ (.param 0))) := by
  rw [familyMemberConsResultLevel_raw, KUniv.toVLevel_mkMaxRaw,
    familyMemberConsInnerResultLevel_raw, KUniv.toVLevel_mkMaxRaw]
  rfl

private def familyMemberFamilyReference : KExpr .anon :=
  KExpr.mkConst familyId #[familyMemberParamLevel] ()

private def familyMemberZeroReference : KExpr .anon :=
  KExpr.mkConst zeroId #[] ()

private def familyMemberSuccReference : KExpr .anon :=
  KExpr.mkConst succId #[] ()

private def familyMemberSortOne : KExpr .anon :=
  KExpr.mkSort familyMemberLevelOne

private def familyMemberSortParamSucc : KExpr .anon :=
  KExpr.mkSort familyMemberParamSucc

private def familyMemberSortParamSuccTwo : KExpr .anon :=
  KExpr.mkSort familyMemberParamSuccTwo

private def familyMemberSortTwo : KExpr .anon :=
  KExpr.mkSort familyMemberLevelTwo

private def familyMemberSortFamilyResult : KExpr .anon :=
  KExpr.mkSort familyMemberFamilyResultLevel

private def familyMemberSortConsResult : KExpr .anon :=
  KExpr.mkSort familyMemberConsResultLevel

private def familyMemberFamilyBody : KExpr .anon :=
  KExpr.mkAll () () familyMemberNatReference familyMemberSortParamSucc

private theorem familyMemberNatReferenceTranslation {Delta : KVLCtx} :
    TrKExprS familyAcceptedWorld.venv familyMemberModel.keys.uvars
      familyAcceptedWorld.nameOf RawProjRel.none Delta
      familyMemberNatReference (.const ``Nat []) := by
  apply TrKExprS.const familyMemberResolveNatExact.nameEq
    familyMemberResolveNatExact.lookup
  · simp
  · native_decide

private theorem familyMemberZeroReferenceTranslation {Delta : KVLCtx} :
    TrKExprS familyAcceptedWorld.venv familyMemberModel.keys.uvars
      familyAcceptedWorld.nameOf RawProjRel.none Delta
      familyMemberZeroReference (.const ``Nat.zero []) := by
  apply TrKExprS.const familyMemberResolveZeroExact.nameEq
    familyMemberResolveZeroExact.lookup
  · simp
  · native_decide

private theorem familyMemberSuccReferenceTranslation {Delta : KVLCtx} :
    TrKExprS familyAcceptedWorld.venv familyMemberModel.keys.uvars
      familyAcceptedWorld.nameOf RawProjRel.none Delta
      familyMemberSuccReference (.const ``Nat.succ []) := by
  apply TrKExprS.const familyMemberResolveSuccExact.nameEq
    familyMemberResolveSuccExact.lookup
  · simp
  · native_decide

private theorem familyMemberFamilyReferenceTranslation {Delta : KVLCtx} :
    TrKExprS familyAcceptedWorld.venv familyMemberModel.keys.uvars
      familyAcceptedWorld.nameOf RawProjRel.none Delta
      familyMemberFamilyReference (.const ``IndexedVec [.param 0]) := by
  apply TrKExprS.const familyMemberResolveFamilyExact.nameEq
    familyMemberResolveFamilyExact.lookup
  · intro level member
    have levelEq : level = familyMemberParamLevel := by
      simpa [familyMemberFamilyReference] using member
    subst level
    decide
  · native_decide

private theorem familyMemberNatTypeTranslation :
    TrKExprS familyAcceptedWorld.venv familyMemberModel.keys.uvars
      familyAcceptedWorld.nameOf RawProjRel.none [] natConcrete.ty
      natType.type := by
  apply familyMemberTrustedTypeTypedAt familyMemberResolveNatExact
    (familyMemberTypedConstantSyntax (by
      simp [familyMemberTypedConstants]))
  · native_decide
  · exact ⟨_, familyMemberNatTypeHasType⟩

private theorem familyMemberZeroTypeTranslation :
    TrKExprS familyAcceptedWorld.venv familyMemberModel.keys.uvars
      familyAcceptedWorld.nameOf RawProjRel.none [] zeroConcrete.ty
      natType.ctors[0].type := by
  apply familyMemberTrustedTypeTypedAt familyMemberResolveZeroExact
    (familyMemberTypedConstantSyntax (by
      simp [familyMemberTypedConstants]))
  · native_decide
  · exact ⟨_, familyMemberZeroTypeHasType⟩

private theorem familyMemberSuccTypeTranslation :
    TrKExprS familyAcceptedWorld.venv familyMemberModel.keys.uvars
      familyAcceptedWorld.nameOf RawProjRel.none [] succConcrete.ty
      natType.ctors[1].type := by
  apply familyMemberTrustedTypeTypedAt familyMemberResolveSuccExact
    (familyMemberTypedConstantSyntax (by
      simp [familyMemberTypedConstants]))
  · native_decide
  · exact ⟨_, familyMemberSuccTypeHasType⟩

private theorem familyMemberFamilyTypeTranslation :
    TrKExprS familyAcceptedWorld.venv familyMemberModel.keys.uvars
      familyAcceptedWorld.nameOf RawProjRel.none [] familyConcrete.ty
      indexedVecType.type := by
  apply familyMemberTrustedTypeTypedAt familyMemberResolveFamilyExact
    (familyMemberTypedConstantSyntax (by
      simp [familyMemberTypedConstants]))
  · native_decide
  · exact ⟨_, familyMemberFamilyTypeHasType⟩

private theorem familyMemberNilTypeTranslation :
    TrKExprS familyAcceptedWorld.venv familyMemberModel.keys.uvars
      familyAcceptedWorld.nameOf RawProjRel.none [] nilConcrete.ty
      indexedVecType.ctors[0].type := by
  apply familyMemberTrustedTypeTypedAt familyMemberResolveNilExact
    (familyMemberTypedConstantSyntax (by
      simp [familyMemberTypedConstants]))
  · native_decide
  · exact ⟨_, familyMemberNilTypeHasType⟩

private theorem familyMemberConsTypeTranslation :
    TrKExprS familyAcceptedWorld.venv familyMemberModel.keys.uvars
      familyAcceptedWorld.nameOf RawProjRel.none [] consConcrete.ty
      indexedVecType.ctors[1].type := by
  apply familyMemberTrustedTypeTypedAt familyMemberResolveConsExact
    (familyMemberTypedConstantSyntax (by
      simp [familyMemberTypedConstants]))
  · native_decide
  · exact ⟨_, familyMemberConsTypeHasType⟩

private theorem familyMemberSortOneTranslation :
    TrKExprS familyAcceptedWorld.venv familyMemberModel.keys.uvars
      familyAcceptedWorld.nameOf RawProjRel.none [] familyMemberSortOne
      (.sort (.succ .zero)) := by
  exact TrKExprS.sort (by decide)

private theorem familyMemberSortParamSuccTranslation :
    TrKExprS familyAcceptedWorld.venv familyMemberModel.keys.uvars
      familyAcceptedWorld.nameOf RawProjRel.none []
      familyMemberSortParamSucc (.sort (.succ (.param 0))) := by
  exact TrKExprS.sort (by decide)

private theorem familyMemberSortParamSuccTwoTranslation :
    TrKExprS familyAcceptedWorld.venv familyMemberModel.keys.uvars
      familyAcceptedWorld.nameOf RawProjRel.none []
      familyMemberSortParamSuccTwo (.sort (.succ (.succ (.param 0)))) := by
  exact TrKExprS.sort (by decide)

private theorem familyMemberSortTwoTranslation :
    TrKExprS familyAcceptedWorld.venv familyMemberModel.keys.uvars
      familyAcceptedWorld.nameOf RawProjRel.none [] familyMemberSortTwo
      (.sort (.succ (.succ .zero))) := by
  exact TrKExprS.sort (by decide)

private theorem familyMemberSortFamilyResultTranslation :
    TrKExprS familyAcceptedWorld.venv familyMemberModel.keys.uvars
      familyAcceptedWorld.nameOf RawProjRel.none []
      familyMemberSortFamilyResult
      (.sort (.max (.succ .zero) (.succ (.succ (.param 0))))) := by
  rw [← familyMemberFamilyResultLevel_toVLevel]
  exact TrKExprS.sort (KUniv.toVLevel_mkMax_wf (by decide) (by decide))

private theorem familyMemberSortConsResultTranslation :
    TrKExprS familyAcceptedWorld.venv familyMemberModel.keys.uvars
      familyAcceptedWorld.nameOf RawProjRel.none []
      familyMemberSortConsResult
      (.sort (.max (.succ (.succ (.param 0)))
        (.max (.succ .zero) (.succ (.param 0))))) := by
  rw [← familyMemberConsResultLevel_toVLevel]
  exact TrKExprS.sort (KUniv.toVLevel_mkMax_wf (by decide)
    (KUniv.toVLevel_mkMax_wf (by decide) (by decide)))

private theorem familyMemberFamilyBodyTranslation :
    TrKExprS familyAcceptedWorld.venv familyMemberModel.keys.uvars
      familyAcceptedWorld.nameOf RawProjRel.none [] familyMemberFamilyBody
      (.forallE (.const ``Nat []) (.sort (.succ (.param 0)))) := by
  apply TrKExprS.all
  · exact ⟨_, VEnv.HasType.const familyMemberNatInfoLookup (by simp) rfl⟩
  · exact ⟨_, VEnv.HasType.sort (by decide)⟩
  · exact familyMemberNatReferenceTranslation
  · exact TrKExprS.sort (by decide)

private theorem familyMemberFamilyBodyHasType :
    familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars []
      (.forallE (.const ``Nat []) (.sort (.succ (.param 0))))
      (.sort (.max (.succ .zero) (.succ (.succ (.param 0))))) := by
  have raw : familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars []
      (.forallE (.const ``Nat []) (.sort (.succ (.param 0))))
      (.sort (.imax (.succ .zero) (.succ (.succ (.param 0))))) := by
    apply VEnv.HasType.forallE
    · exact VEnv.HasType.const familyMemberNatInfoLookup (by simp) rfl
    · exact VEnv.HasType.sort (by decide)
  apply VEnv.IsDefEq.defeq
    (h1 := VEnv.IsDefEq.sortDF (by decide) (by decide) (by
      simp [VLevel.equiv_def, VLevel.eval, Lean.Nat.imax]))
    raw

/-- Package one structural source translation, one structural cached-type
translation, and a Theory typing derivation as exact inference meaning. -/
private theorem familyMemberInferMeaningOfTyped
    {source ty : KExpr .anon} {sourceV tyV : VExpr}
    (sourceTr : TrKExprS familyAcceptedWorld.venv
      familyMemberModel.keys.uvars familyAcceptedWorld.nameOf
      RawProjRel.none [] source sourceV)
    (tyTr : TrKExprS familyAcceptedWorld.venv
      familyMemberModel.keys.uvars familyAcceptedWorld.nameOf
      RawProjRel.none [] ty tyV)
    (sourceTyped : familyAcceptedWorld.venv.HasType
      familyMemberModel.keys.uvars [] sourceV tyV) :
    InferMeaning RawProjRel.none familyAcceptedWorld
      familyMemberModel.keys.uvars [] source ty := by
  exact ⟨sourceV, sourceTr, tyV,
    tyTr.trKExpr familyAcceptedWorld.venvWF.ordered
      familyMemberWhnfTheory.literalWF
      familyMemberWhnfTheory.projections.wf trivial,
    sourceTyped⟩

private theorem familyMemberNilTypeInferMeaning :
    InferMeaning RawProjRel.none familyAcceptedWorld
      familyMemberModel.keys.uvars [] nilConcrete.ty
      familyMemberSortParamSuccTwo :=
  familyMemberInferMeaningOfTyped familyMemberNilTypeTranslation
    familyMemberSortParamSuccTwoTranslation familyMemberNilTypeHasType

private theorem familyMemberFamilyTypeInferMeaning :
    InferMeaning RawProjRel.none familyAcceptedWorld
      familyMemberModel.keys.uvars [] familyConcrete.ty
      familyMemberSortFamilyResult :=
  familyMemberInferMeaningOfTyped familyMemberFamilyTypeTranslation
    familyMemberSortFamilyResultTranslation familyMemberFamilyTypeHasType

private theorem familyMemberFamilyReferenceInferMeaning :
    InferMeaning RawProjRel.none familyAcceptedWorld
      familyMemberModel.keys.uvars [] familyMemberFamilyReference
      familyConcrete.ty := by
  apply familyMemberInferMeaningOfTyped familyMemberFamilyReferenceTranslation
    familyMemberFamilyTypeTranslation
  exact VEnv.HasType.const' familyMemberFamilyInfoLookup
    (by decide) (by decide) rfl

private theorem familyMemberNatTypeInferMeaning :
    InferMeaning RawProjRel.none familyAcceptedWorld
      familyMemberModel.keys.uvars [] natConcrete.ty familyMemberSortTwo :=
  familyMemberInferMeaningOfTyped familyMemberNatTypeTranslation
    familyMemberSortTwoTranslation familyMemberNatTypeHasType

private theorem familyMemberNatReferenceInferMeaning :
    InferMeaning RawProjRel.none familyAcceptedWorld
      familyMemberModel.keys.uvars [] familyMemberNatReference
      natConcrete.ty := by
  apply familyMemberInferMeaningOfTyped familyMemberNatReferenceTranslation
    familyMemberNatTypeTranslation
  exact VEnv.HasType.const familyMemberNatInfoLookup (by simp) rfl

private theorem familyMemberFamilyBodyInferMeaning :
    InferMeaning RawProjRel.none familyAcceptedWorld
      familyMemberModel.keys.uvars [] familyMemberFamilyBody
      familyMemberSortFamilyResult :=
  familyMemberInferMeaningOfTyped familyMemberFamilyBodyTranslation
    familyMemberSortFamilyResultTranslation familyMemberFamilyBodyHasType

private theorem familyMemberSortParamSuccInferMeaning :
    InferMeaning RawProjRel.none familyAcceptedWorld
      familyMemberModel.keys.uvars [] familyMemberSortParamSucc
      familyMemberSortParamSuccTwo :=
  familyMemberInferMeaningOfTyped familyMemberSortParamSuccTranslation
    familyMemberSortParamSuccTwoTranslation (VEnv.HasType.sort (by decide))

private theorem familyMemberSuccReferenceInferMeaning :
    InferMeaning RawProjRel.none familyAcceptedWorld
      familyMemberModel.keys.uvars [] familyMemberSuccReference
      succConcrete.ty := by
  apply familyMemberInferMeaningOfTyped familyMemberSuccReferenceTranslation
    familyMemberSuccTypeTranslation
  exact VEnv.HasType.const familyMemberSuccInfoLookup (by simp) rfl

private theorem familyMemberSuccTypeInferMeaning :
    InferMeaning RawProjRel.none familyAcceptedWorld
      familyMemberModel.keys.uvars [] succConcrete.ty familyMemberSortOne :=
  familyMemberInferMeaningOfTyped familyMemberSuccTypeTranslation
    familyMemberSortOneTranslation familyMemberSuccTypeHasType

private theorem familyMemberZeroReferenceInferMeaning :
    InferMeaning RawProjRel.none familyAcceptedWorld
      familyMemberModel.keys.uvars [] familyMemberZeroReference
      zeroConcrete.ty := by
  apply familyMemberInferMeaningOfTyped familyMemberZeroReferenceTranslation
    familyMemberZeroTypeTranslation
  exact VEnv.HasType.const familyMemberZeroInfoLookup (by simp) rfl

private theorem familyMemberConsTypeInferMeaning :
    InferMeaning RawProjRel.none familyAcceptedWorld
      familyMemberModel.keys.uvars [] consConcrete.ty
      familyMemberSortConsResult :=
  familyMemberInferMeaningOfTyped familyMemberConsTypeTranslation
    familyMemberSortConsResultTranslation familyMemberConsTypeHasType

/-! ## Warm inference cache census -/

/-- The complete semantic range of the reachable closed inference entries.
All remaining physical entries were created under temporary local contexts
and are intentionally classified as stale at this closed ingress. -/
private def FamilyMemberClosedInferPair
    (source ty : KExpr .anon) : Prop :=
  (source = nilConcrete.ty ∧ ty = familyMemberSortParamSuccTwo) ∨
  (source = familyConcrete.ty ∧ ty = familyMemberSortFamilyResult) ∨
  (source = familyMemberFamilyReference ∧ ty = familyConcrete.ty) ∨
  (source = natConcrete.ty ∧ ty = familyMemberSortTwo) ∨
  (source = familyMemberNatReference ∧ ty = natConcrete.ty) ∨
  (source = familyMemberFamilyBody ∧ ty = familyMemberSortFamilyResult) ∨
  (source = familyMemberSortParamSucc ∧
    ty = familyMemberSortParamSuccTwo) ∨
  (source = familyMemberSuccReference ∧ ty = succConcrete.ty) ∨
  (source = succConcrete.ty ∧ ty = familyMemberSortOne) ∨
  (source = familyMemberZeroReference ∧ ty = zeroConcrete.ty) ∨
  (source = consConcrete.ty ∧ ty = familyMemberSortConsResult)

private instance familyMemberClosedInferPairDecidable
    (source ty : KExpr .anon) :
    Decidable (FamilyMemberClosedInferPair source ty) := by
  unfold FamilyMemberClosedInferPair
  infer_instance

/-- Finite facts retained for each physical inference entry: the key has an
exact source witness, the cached type is interned, and every reachable closed
source belongs to the proved semantic range.  Ordinary inference entries may
not depend on the active recursor member. -/
private def FamilyMemberInferEntryCensus
    (entry : (Address × Address) × KExpr .anon) : Prop :=
  ∃ source,
    familyMemberInitial.env.intern.exprs[entry.1.1]? = some source ∧
      familyMemberInitial.env.intern.exprs[entry.2.addr]? = some entry.2 ∧
      (¬source.ContextScoped [] ∨
        FamilyMemberClosedInferPair source entry.2) ∧
      recursorId ∉ source.referenceIds ∧
      recursorId ∉ entry.2.referenceIds

private instance familyMemberInferEntryCensusDecidable
    (entry : (Address × Address) × KExpr .anon) :
    Decidable (FamilyMemberInferEntryCensus entry) := by
  unfold FamilyMemberInferEntryCensus
  infer_instance

private def familyMemberInferCacheCensus : Bool :=
  familyMemberInitial.env.inferCache.toList.all fun entry =>
    decide (FamilyMemberInferEntryCensus entry)

private theorem familyMemberInferCensusNative :
    familyMemberInferCacheCensus = true := by
  native_decide

private theorem familyMemberInferCensus_get
    {key : Address × Address} {ty : KExpr .anon}
    (lookup : familyMemberInitial.env.inferCache[key]? = some ty) :
    FamilyMemberInferEntryCensus (key, ty) := by
  have census := familyMemberInferCensusNative
  unfold familyMemberInferCacheCensus at census
  rw [List.all_eq_true] at census
  exact of_decide_eq_true <| census (key, ty)
    (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr lookup)

private theorem familyMemberClosedInferPair_meaning
    {source ty : KExpr .anon}
    (pair : FamilyMemberClosedInferPair source ty) :
    InferMeaning RawProjRel.none familyAcceptedWorld
      familyMemberModel.keys.uvars [] source ty := by
  rcases pair with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact familyMemberNilTypeInferMeaning
  · exact familyMemberFamilyTypeInferMeaning
  · exact familyMemberFamilyReferenceInferMeaning
  · exact familyMemberNatTypeInferMeaning
  · exact familyMemberNatReferenceInferMeaning
  · exact familyMemberFamilyBodyInferMeaning
  · exact familyMemberSortParamSuccInferMeaning
  · exact familyMemberSuccReferenceInferMeaning
  · exact familyMemberSuccTypeInferMeaning
  · exact familyMemberZeroReferenceInferMeaning
  · exact familyMemberConsTypeInferMeaning

/-! ## Warm WHNF cache census -/

/-- The only closed WHNF-cache source surviving at member-check ingress is
the Nat constant.  Every other entry is a stale local-scope identity entry.
The last conjunct keeps ordinary reduction caches independent of the active
recursor member. -/
private def FamilyMemberWhnfEntryCensus
    (entry : (Address × Address) × KExpr .anon) : Prop :=
  familyMemberInitial.env.intern.exprs[entry.1.1]? = some entry.2 ∧
    (¬entry.2.ContextScoped [] ∨ entry.2 = familyMemberNatReference) ∧
    recursorId ∉ entry.2.referenceIds

private instance familyMemberWhnfEntryCensusDecidable
    (entry : (Address × Address) × KExpr .anon) :
    Decidable (FamilyMemberWhnfEntryCensus entry) := by
  unfold FamilyMemberWhnfEntryCensus
  infer_instance

private def familyMemberWhnfCacheCensus
    (cache : Std.HashMap (Address × Address) (KExpr .anon)) : Bool :=
  cache.toList.all fun entry => decide (FamilyMemberWhnfEntryCensus entry)

private theorem familyMemberWhnfCacheCensus_get
    {cache : Std.HashMap (Address × Address) (KExpr .anon)}
    (census : familyMemberWhnfCacheCensus cache = true)
    {key : Address × Address} {value : KExpr .anon}
    (lookup : cache[key]? = some value) :
    FamilyMemberWhnfEntryCensus (key, value) := by
  unfold familyMemberWhnfCacheCensus at census
  rw [List.all_eq_true] at census
  exact of_decide_eq_true <| census (key, value)
    (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr lookup)

private theorem familyMemberWhnfCensusNative :
    familyMemberWhnfCacheCensus familyMemberInitial.env.whnfCache = true := by
  native_decide

private theorem familyMemberWhnfNoDeltaCensusNative :
    familyMemberWhnfCacheCensus
      familyMemberInitial.env.whnfNoDeltaCache = true := by
  native_decide

private theorem familyMemberWhnfCoreCensusNative :
    familyMemberWhnfCacheCensus
      familyMemberInitial.env.whnfCoreCache = true := by
  native_decide

/-- Any supported member-check expression that does not name the active
recursor refers only to already-trusted declarations. -/
private theorem familyMemberReferenceTrusted
    {expression : KExpr .anon} {id : KId .anon}
    (supported : familyMemberSupport expression)
    (reference : expression.References id)
    (notRecursor : recursorId ∉ expression.referenceIds) :
    familyAcceptedWorld.trusted id := by
  rcases familyMemberAuthorizedReferences
      (source := expression) (id := id) supported reference
    with trusted | active
  · exact trusted
  · have idEq : id = recursorId := by
      simpa [CacheAuthority.coordinatedBlock, recursorMembers_eq] using active
    subst id
    exact False.elim (notRecursor (KExpr.mem_referenceIds.mpr reference))

/-- The one reachable closed WHNF identity entry has a genuine structural
translation and hence reflexive Theory reduction meaning. -/
private theorem familyMemberNatReferenceWhnf :
    WhnfMeaning RawProjRel.none familyAcceptedWorld
      familyMemberModel.keys.uvars [] familyMemberNatReference
        familyMemberNatReference := by
  obtain ⟨name, info, resolved⟩ := familyMemberResolveNat
  have translated : TrKExprS familyAcceptedWorld.venv
      familyMemberModel.keys.uvars familyAcceptedWorld.nameOf
      RawProjRel.none [] familyMemberNatReference (.const name []) := by
    apply TrKExprS.const resolved.nameEq resolved.lookup
    · simp
    · have zeroUvars : natConcrete.lvls.toNat = 0 := by native_decide
      exact zeroUvars.symm.trans resolved.uvars
  exact WhnfMeaning.refl translated
    (translated.wf familyAcceptedWorld.venvWF.ordered
      familyMemberWhnfTheory.literalWF
      familyMemberWhnfTheory.projections.wf trivial)

/-- Lift one finite WHNF census fact to complete provenance in the full
inductive-aware K1/K2 semantic stack. -/
private theorem familyMemberWhnfEntryProvenance
    {kind : ExprCacheKind} (isWhnf : kind.IsWhnf)
    {key : Address × Address} {value : KExpr .anon}
    (census : FamilyMemberWhnfEntryCensus (key, value)) :
    CacheProvenance
      (kernelCacheSemanticsWithInductives familyMemberModel.keys
        RawProjRel.none)
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      familyMemberSupport (.expr kind key value) := by
  have valueSupported : familyMemberSupport value :=
    Or.inl ⟨key.1, census.1⟩
  have valueAddress : value.addr = key.1 := by
    simpa [KExpr.internKey] using
      familyMemberInitial_internWF.expr_key census.1
  refine ⟨⟨⟨value, valueSupported, valueAddress⟩, valueSupported⟩, ?_, ?_⟩
  · intro id references
    apply Or.inl
    rcases references with sourceReference | valueReference
    · obtain ⟨source, sourceSupported, sourceAddress, sourceReferences⟩ :=
        sourceReference
      have sourceEq : source = value :=
        familyMemberSupport_expr_eq_of_addr_eq sourceSupported valueSupported
          (sourceAddress.trans valueAddress.symm)
      subst source
      exact familyMemberReferenceTrusted valueSupported sourceReferences
        census.2.2
    · exact familyMemberReferenceTrusted valueSupported valueReference
        census.2.2
  · change WhnfCacheValid familyMemberModel.keys RawProjRel.none _
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      familyMemberSupport (.expr kind key value)
    cases isWhnf <;>
      intro source sourceSupported sourceAddress Delta represented sourceScoped
    all_goals
      have deltaEq : Delta = [] :=
        familyMemberModel_represents_nil represented
      subst Delta
      have sourceEq : source = value :=
        familyMemberSupport_expr_eq_of_addr_eq sourceSupported valueSupported
          (sourceAddress.trans valueAddress.symm)
      subst source
      rcases census.2.1 with stale | natEntry
      · exact False.elim (stale sourceScoped)
      · change value = familyMemberNatReference at natEntry
        subst value
        exact familyMemberNatReferenceWhnf

private theorem familyMemberWhnfProvenance
    {key : Address × Address} {value : KExpr .anon}
    (lookup : familyMemberInitial.env.whnfCache[key]? = some value) :
    CacheProvenance
      (kernelCacheSemanticsWithInductives familyMemberModel.keys
        RawProjRel.none)
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      familyMemberSupport (.expr .whnf key value) :=
  familyMemberWhnfEntryProvenance .whnf
    (familyMemberWhnfCacheCensus_get familyMemberWhnfCensusNative lookup)

private theorem familyMemberWhnfNoDeltaProvenance
    {key : Address × Address} {value : KExpr .anon}
    (lookup : familyMemberInitial.env.whnfNoDeltaCache[key]? = some value) :
    CacheProvenance
      (kernelCacheSemanticsWithInductives familyMemberModel.keys
        RawProjRel.none)
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      familyMemberSupport (.expr .whnfNoDelta key value) :=
  familyMemberWhnfEntryProvenance .whnfNoDelta
    (familyMemberWhnfCacheCensus_get familyMemberWhnfNoDeltaCensusNative
      lookup)

private theorem familyMemberWhnfCoreProvenance
    {key : Address × Address} {value : KExpr .anon}
    (lookup : familyMemberInitial.env.whnfCoreCache[key]? = some value) :
    CacheProvenance
      (kernelCacheSemanticsWithInductives familyMemberModel.keys
        RawProjRel.none)
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      familyMemberSupport (.expr .whnfCore key value) :=
  familyMemberWhnfEntryProvenance .whnfCore
    (familyMemberWhnfCacheCensus_get familyMemberWhnfCoreCensusNative lookup)

/-! ## Inference cache provenance -/

/-- Lift one finite inference census entry to semantic provenance.  Address
collision freedom identifies the ghost source with the canonical interned
source; suffix representation identifies the only reachable context with
the empty Theory context. -/
private theorem familyMemberInferEntryProvenance
    {kind : ExprCacheKind} (isInfer : kind.IsInfer)
    {key : Address × Address} {ty : KExpr .anon}
    (census : FamilyMemberInferEntryCensus (key, ty)) :
    CacheProvenance
      (kernelCacheSemanticsWithInductives familyMemberModel.keys
        RawProjRel.none)
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      familyMemberSupport (.expr kind key ty) := by
  obtain ⟨cachedSource, sourceLookup, tyLookup, reachable,
    sourceNoRecursor, tyNoRecursor⟩ := census
  have sourceSupported : familyMemberSupport cachedSource :=
    Or.inl ⟨key.1, sourceLookup⟩
  have tySupported : familyMemberSupport ty :=
    Or.inl ⟨ty.addr, tyLookup⟩
  have sourceAddress : cachedSource.addr = key.1 := by
    simpa [KExpr.internKey] using
      familyMemberInitial_internWF.expr_key sourceLookup
  refine ⟨⟨⟨cachedSource, sourceSupported, sourceAddress⟩, tySupported⟩,
    ?_, ?_⟩
  · intro id references
    apply Or.inl
    rcases references with sourceReference | tyReference
    · obtain ⟨source, supported, address, reference⟩ := sourceReference
      have sourceEq : source = cachedSource :=
        familyMemberSupport_expr_eq_of_addr_eq supported sourceSupported
          (address.trans sourceAddress.symm)
      subst source
      exact familyMemberReferenceTrusted sourceSupported reference
        sourceNoRecursor
    · exact familyMemberReferenceTrusted tySupported tyReference
        tyNoRecursor
  · have semantic :
        (∀ (source : KExpr .anon), familyMemberSupport source →
          source.addr = key.1 →
          ∀ (Delta : KVLCtx),
            familyMemberModel.keys.Represents source.lbr key.2 Delta →
            source.ContextScoped Delta →
            InferMeaning RawProjRel.none familyAcceptedWorld
              familyMemberModel.keys.uvars Delta source ty) := by
      intro source supported address Delta represented hscoped
      have deltaEq : Delta = [] :=
        familyMemberModel_represents_nil represented
      subst Delta
      have sourceEq : source = cachedSource :=
        familyMemberSupport_expr_eq_of_addr_eq supported sourceSupported
          (address.trans sourceAddress.symm)
      subst source
      rcases reachable with stale | pair
      · exact False.elim (stale hscoped)
      · exact familyMemberClosedInferPair_meaning pair
    cases isInfer with
    | infer =>
        simpa [kernelCacheSemanticsWithInductives, k1CacheSemantics,
          whnfCacheSemantics, WhnfCacheValid, unfoldCacheSemantics,
          UnfoldCacheValid, inferCacheSemantics, InferCacheValid,
          CacheAuthority.coordinatedBlock] using semantic
    | inferOnly =>
        simpa [kernelCacheSemanticsWithInductives, k1CacheSemantics,
          whnfCacheSemantics, WhnfCacheValid, unfoldCacheSemantics,
          UnfoldCacheValid, inferCacheSemantics, InferCacheValid,
          CacheAuthority.coordinatedBlock] using semantic

private theorem familyMemberInferProvenance
    {key : Address × Address} {ty : KExpr .anon}
    (lookup : familyMemberInitial.env.inferCache[key]? = some ty) :
    CacheProvenance
      (kernelCacheSemanticsWithInductives familyMemberModel.keys
        RawProjRel.none)
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      familyMemberSupport (.expr .infer key ty) :=
  familyMemberInferEntryProvenance .infer
    (familyMemberInferCensus_get lookup)

private theorem familyMemberInferOnlyCacheEmpty :
    familyMemberInitial.env.inferOnlyCache.toList = [] := by
  native_decide

/-! ## Empty cache families -/

private theorem hashMapLookupFalseOfToListNil
    {key value : Type} [BEq key] [Hashable key] [LawfulBEq key]
    {entries : Std.HashMap key value} (empty : entries.toList = [])
    {query : key} {result : value}
    (lookup : entries[query]? = some result) : False := by
  have member :=
    Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr lookup
  rw [empty] at member
  simp at member

private theorem hashSetContainsFalseOfToListNil
    {key : Type} [BEq key] [Hashable key] [LawfulBEq key]
    {entries : Std.HashSet key} (empty : entries.toList = [])
    {query : key} (contains : entries.contains query = true) : False := by
  have member := Std.HashSet.mem_toList.mpr
    (Std.HashSet.mem_iff_contains.mpr contains)
  rw [empty] at member
  simp at member

private theorem familyMemberWhnfNoDeltaCheapCacheEmpty :
    familyMemberInitial.env.whnfNoDeltaCheapCache.toList = [] := by
  native_decide

private theorem familyMemberWhnfCoreCheapCacheEmpty :
    familyMemberInitial.env.whnfCoreCheapCache.toList = [] := by
  native_decide

private theorem familyMemberDefEqCacheEmpty :
    familyMemberInitial.env.defEqCache.toList = [] := by
  native_decide

private theorem familyMemberDefEqCheapCacheEmpty :
    familyMemberInitial.env.defEqCheapCache.toList = [] := by
  native_decide

private theorem familyMemberDefEqFailureCacheEmpty :
    familyMemberInitial.env.defEqFailure.toList = [] := by
  native_decide

private theorem familyMemberUnfoldCacheEmpty :
    familyMemberInitial.env.unfoldCache.toList = [] := by
  native_decide

private theorem familyMemberNatSuccStuckCacheEmpty :
    familyMemberInitial.env.natSuccStuck.toList = [] := by
  native_decide

private theorem familyMemberIsPropCacheEmpty :
    familyMemberInitial.env.isPropCache.toList = [] := by
  native_decide

private theorem familyMemberIsRecCacheEmpty :
    familyMemberInitial.env.isRecCache.toList = [] := by
  native_decide

/-! ## Structural cache provenance -/

/-- The already-admitted Nat block remains an exact accepted block after the
family transaction. -/
private theorem familyMemberNatBlockAccepted :
    familyAcceptedWorld.AcceptedBlock natBlockId := by
  refine ⟨natMembers, ?_, ?_, ?_⟩
  · change familyAcceptedWorld.blocks natBlockId = some natMembers
    rw [← familyAtomicAdmission.promotion.le.blocks]
    change blockCatalog natBlockId = some natMembers
    native_decide
  · native_decide
  · intro id member
    have cases : id = natId ∨ id = zeroId ∨ id = succId := by
      simpa [natMembers] using member
    rcases cases with rfl | rfl | rfl
    · exact familyMemberNatTrusted
    · exact familyMemberZeroTrusted
    · exact familyMemberSuccTrusted

private theorem familyMemberNatBlockAuthorized :
    CacheAuthority.AuthorizesBlock
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      natBlockId :=
  CacheAuthority.AuthorizesBlock.mono
    CacheAuthority.stable_le_coordinatedBlock
    (CacheAuthority.authorizesBlock_of_accepted
      familyMemberNatBlockAccepted)

private theorem familyMemberFamilyBlockAuthorized :
    CacheAuthority.AuthorizesBlock
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      familyBlockId :=
  CacheAuthority.AuthorizesBlock.mono
    CacheAuthority.stable_le_coordinatedBlock
    (CacheAuthority.authorizesBlock_of_accepted familyBlockAccepted)

/-- Every generated type and rule right-hand side in either warm recursor
batch occurs in the concrete ingress intern table. -/
private def familyMemberRecursorPayloadsInterned : Bool :=
  familyMemberInitial.env.recursorCache.toList.all fun entry =>
    entry.2.all fun generated =>
      decide
          (familyMemberInitial.env.intern.exprs[generated.ty.addr]? =
            some generated.ty) &&
        generated.rules.all fun rule =>
          decide
            (familyMemberInitial.env.intern.exprs[rule.rhs.addr]? =
              some rule.rhs)

private theorem familyMemberRecursorPayloadsInternedNative :
    familyMemberRecursorPayloadsInterned = true := by
  native_decide

private theorem familyMemberRecursorPayloadInterned
    {block : KId .anon} {batch : Array (GeneratedRecursor .anon)}
    (lookup : familyMemberInitial.env.recursorCache[block]? = some batch)
    {generated : GeneratedRecursor .anon} (member : generated ∈ batch) :
    familyMemberInitial.env.intern.ExprSupport generated.ty ∧
      ∀ rule ∈ generated.rules,
        familyMemberInitial.env.intern.ExprSupport rule.rhs := by
  have outer := List.all_eq_true.mp
    familyMemberRecursorPayloadsInternedNative
  have batchCheck := outer (block, batch)
    (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr lookup)
  obtain ⟨generatedIndex, generatedBound, generatedEq⟩ :=
    Array.mem_iff_getElem.mp member
  subst generated
  have generatedCheck := Array.all_eq_true.mp batchCheck generatedIndex
    generatedBound
  obtain ⟨typeCheck, rulesCheck⟩ :=
    Bool.and_eq_true_iff.mp generatedCheck
  refine ⟨⟨batch[generatedIndex].ty.addr,
    of_decide_eq_true typeCheck⟩, ?_⟩
  intro rule ruleMember
  obtain ⟨ruleIndex, ruleBound, ruleEq⟩ :=
    Array.mem_iff_getElem.mp ruleMember
  subst rule
  have ruleCheck := Array.all_eq_true.mp rulesCheck ruleIndex ruleBound
  exact ⟨batch[generatedIndex].rules[ruleIndex].rhs.addr,
    of_decide_eq_true ruleCheck⟩

/-- Each warm recursor-cache key is one of the two exact immutable family
blocks present in the fixture. -/
private def familyMemberRecursorBlocksClassified : Bool :=
  familyMemberInitial.env.recursorCache.toList.all fun entry =>
    decide (entry.1 = natBlockId ∨ entry.1 = familyBlockId)

private theorem familyMemberRecursorBlocksClassifiedNative :
    familyMemberRecursorBlocksClassified = true := by
  native_decide

private theorem familyMemberRecursorBlockClassified
    {block : KId .anon} {batch : Array (GeneratedRecursor .anon)}
    (lookup : familyMemberInitial.env.recursorCache[block]? = some batch) :
    block = natBlockId ∨ block = familyBlockId := by
  have all := List.all_eq_true.mp
    familyMemberRecursorBlocksClassifiedNative
  exact of_decide_eq_true <| all (block, batch)
    (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr lookup)

/-- Positional owner identity for every generated entry in the two warm
batches.  The cache block address and declaration address remain distinct. -/
private def familyMemberRecursorOwnersClassified : Bool :=
  familyMemberInitial.env.recursorCache.toList.all fun entry =>
    entry.2.all fun generated =>
      decide
        ((entry.1 = natBlockId ∧ generated.indAddr = natId.addr) ∨
          (entry.1 = familyBlockId ∧ generated.indAddr = familyId.addr))

private theorem familyMemberRecursorOwnersClassifiedNative :
    familyMemberRecursorOwnersClassified = true := by
  native_decide

private theorem familyMemberRecursorOwnerClassified
    {block : KId .anon} {batch : Array (GeneratedRecursor .anon)}
    (lookup : familyMemberInitial.env.recursorCache[block]? = some batch)
    {generated : GeneratedRecursor .anon} (member : generated ∈ batch) :
    (block = natBlockId ∧ generated.indAddr = natId.addr) ∨
      (block = familyBlockId ∧ generated.indAddr = familyId.addr) := by
  have outer := List.all_eq_true.mp
    familyMemberRecursorOwnersClassifiedNative
  have batchCheck := outer (block, batch)
    (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr lookup)
  obtain ⟨index, bound, generatedEq⟩ :=
    Array.mem_iff_getElem.mp member
  subst generated
  exact of_decide_eq_true <| Array.all_eq_true.mp batchCheck index bound

private theorem familyMemberRecursorProvenance
    {block : KId .anon} {batch : Array (GeneratedRecursor .anon)}
    (lookup : familyMemberInitial.env.recursorCache[block]? = some batch) :
    CacheProvenance
      (kernelCacheSemanticsWithInductives familyMemberModel.keys
        RawProjRel.none)
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      familyMemberSupport (.recursor block batch) := by
  have payloadSupported :
      (CacheEntry.recursor block batch).SupportedBy familyMemberSupport := by
    intro generated member
    have interned := familyMemberRecursorPayloadInterned lookup member
    exact ⟨Or.inl interned.1,
      fun rule ruleMember => Or.inl (interned.2 rule ruleMember)⟩
  have generatedAuthorized : ∀ generated ∈ batch,
      ∃ id : KId .anon,
        (familyAcceptedWorld.trusted id ∨ id ∈ recursorMembers) ∧
          id.addr = generated.indAddr := by
    intro generated member
    rcases familyMemberRecursorOwnerClassified lookup member with
      ⟨_, owner⟩ | ⟨_, owner⟩
    · exact ⟨natId, .inl familyMemberNatTrusted, owner.symm⟩
    · exact ⟨familyId, .inl familyMemberFamilyTrusted, owner.symm⟩
  have blockAuthorized :
      CacheAuthority.AuthorizesBlock
        (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
        block := by
    rcases familyMemberRecursorBlockClassified lookup with rfl | rfl
    · exact familyMemberNatBlockAuthorized
    · exact familyMemberFamilyBlockAuthorized
  refine ⟨payloadSupported, ?_, ?_⟩
  · intro id references
    rcases references with
      ⟨generated, member, header | typeReference | ruleReferences⟩
    · obtain ⟨owner, authorized, ownerAddress⟩ :=
        generatedAuthorized generated member
      have idEq : id = owner :=
        KId.anon_eq_of_addr_eq (header.trans ownerAddress.symm)
      subst id
      rcases authorized with trusted | active
      · exact .inl trusted
      · exact .inr ⟨trivial, active⟩
    · rcases familyMemberAuthorizedReferences
          (payloadSupported generated member).1 typeReference with
        trusted | active
      · exact .inl trusted
      · exact .inr ⟨trivial, active⟩
    · obtain ⟨rule, ruleMember, reference⟩ := ruleReferences
      rcases familyMemberAuthorizedReferences
          ((payloadSupported generated member).2 rule ruleMember)
          reference with trusted | active
      · exact .inl trusted
      · exact .inr ⟨trivial, active⟩
  · change StructuralInductiveCacheValid CacheSemantics.blockErrorsOnly
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      familyMemberSupport (.recursor block batch)
    exact ⟨blockAuthorized, generatedAuthorized⟩

/-! ### Recursive-major index -/

private def familyMemberRecMajorsClassified : Bool :=
  familyMemberInitial.env.recMajorsCache.toList.all fun entry =>
    decide
      ((entry.1 = #[natId] ∧ entry.2 = natBlockId) ∨
        (entry.1 = #[familyId] ∧ entry.2 = familyBlockId))

private theorem familyMemberRecMajorsClassifiedNative :
    familyMemberRecMajorsClassified = true := by
  native_decide

private theorem familyMemberRecMajorsCensus
    {majors : Array (KId .anon)} {block : KId .anon}
    (lookup : familyMemberInitial.env.recMajorsCache[majors]? = some block) :
    (majors = #[natId] ∧ block = natBlockId) ∨
      (majors = #[familyId] ∧ block = familyBlockId) := by
  have all := List.all_eq_true.mp familyMemberRecMajorsClassifiedNative
  exact of_decide_eq_true <| all (majors, block)
    (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr lookup)

private theorem familyMemberRecMajorsProvenance
    {majors : Array (KId .anon)} {block : KId .anon}
    (lookup : familyMemberInitial.env.recMajorsCache[majors]? = some block) :
    CacheProvenance
      (kernelCacheSemanticsWithInductives familyMemberModel.keys
        RawProjRel.none)
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      familyMemberSupport (.recMajors majors block) := by
  rcases familyMemberRecMajorsCensus lookup with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have majorTrusted : ∀ id ∈ (#[natId] : Array (KId .anon)),
        familyAcceptedWorld.trusted id := by
      intro id member
      have idEq : id = natId := by simpa using member
      subst id
      exact familyMemberNatTrusted
    refine ⟨trivial, ?_, ?_⟩
    · intro id member
      exact .inl (majorTrusted id member)
    · change StructuralInductiveCacheValid CacheSemantics.blockErrorsOnly
        (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
        familyMemberSupport (.recMajors #[natId] natBlockId)
      exact ⟨familyMemberNatBlockAuthorized,
        fun id member => .inl (majorTrusted id member)⟩
  · have majorTrusted : ∀ id ∈ (#[familyId] : Array (KId .anon)),
        familyAcceptedWorld.trusted id := by
      intro id member
      have idEq : id = familyId := by simpa using member
      subst id
      exact familyMemberFamilyTrusted
    refine ⟨trivial, ?_, ?_⟩
    · intro id member
      exact .inl (majorTrusted id member)
    · change StructuralInductiveCacheValid CacheSemantics.blockErrorsOnly
        (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
        familyMemberSupport (.recMajors #[familyId] familyBlockId)
      exact ⟨familyMemberFamilyBlockAuthorized,
        fun id member => .inl (majorTrusted id member)⟩

/-! ### Peer-agreement markers -/

private def familyMemberBlockPeersClassified : Bool :=
  familyMemberInitial.env.blockPeerAgreementCache.toList.all fun block =>
    decide (block = natBlockId ∨ block = familyBlockId)

private theorem familyMemberBlockPeersClassifiedNative :
    familyMemberBlockPeersClassified = true := by
  native_decide

private theorem familyMemberBlockPeerCensus
    {block : KId .anon}
    (contains :
      familyMemberInitial.env.blockPeerAgreementCache.contains block = true) :
    block = natBlockId ∨ block = familyBlockId := by
  have all := List.all_eq_true.mp familyMemberBlockPeersClassifiedNative
  exact of_decide_eq_true <| all block <|
    Std.HashSet.mem_toList.mpr <|
      Std.HashSet.mem_iff_contains.mpr contains

private theorem familyMemberBlockPeerProvenance
    {block : KId .anon}
    (contains :
      familyMemberInitial.env.blockPeerAgreementCache.contains block = true) :
    CacheProvenance
      (kernelCacheSemanticsWithInductives familyMemberModel.keys
        RawProjRel.none)
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      familyMemberSupport (.blockPeer block) := by
  have authorized :
      CacheAuthority.AuthorizesBlock
        (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
        block := by
    rcases familyMemberBlockPeerCensus contains with rfl | rfl
    · exact familyMemberNatBlockAuthorized
    · exact familyMemberFamilyBlockAuthorized
  refine ⟨trivial, ?_, ?_⟩
  · intro id reference
    exact False.elim reference
  · change StructuralInductiveCacheValid CacheSemantics.blockErrorsOnly
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      familyMemberSupport (.blockPeer block)
    exact authorized

/-! ### Published block result -/

private def familyMemberBlockResultKeysClassified : Bool :=
  familyMemberInitial.env.blockCheckResults.toList.all fun entry =>
    decide (entry.1 = familyBlockId)

private theorem familyMemberBlockResultKeysClassifiedNative :
    familyMemberBlockResultKeysClassified = true := by
  native_decide

private theorem familyMemberFamilyBlockResult :
    familyMemberInitial.env.blockCheckResults[familyBlockId]? =
      some (.ok ()) := by
  simp [familyMemberInitial, TcState.withBlockCheckResult]

private theorem familyMemberBlockResultProvenance
    {block : KId .anon} {result : Except (TcError .anon) Unit}
    (lookup : familyMemberInitial.env.blockCheckResults[block]? =
      some result) :
    CacheProvenance
      (kernelCacheSemanticsWithInductives familyMemberModel.keys
        RawProjRel.none)
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      familyMemberSupport (.blockResult block result) := by
  have all := List.all_eq_true.mp
    familyMemberBlockResultKeysClassifiedNative
  have blockEq : block = familyBlockId := of_decide_eq_true <|
    all (block, result)
      (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr lookup)
  subst block
  have resultEq : result = .ok () := Option.some.inj <|
    lookup.symm.trans familyMemberFamilyBlockResult
  subst result
  exact CacheProvenance.blockSuccess
    (kernelCacheSemanticsWithInductives familyMemberModel.keys
      RawProjRel.none)
    (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
    familyMemberSupport familyBlockId familyBlockAccepted

/-! ## Complete initial invariant -/

/-- Every physical semantic cache entry in the reached production state has
finite support, authorized direct roots, and the meaning assigned by the
complete K1/K2/inductive cache stack. -/
theorem familyMemberInitial_cacheInvariant :
    CacheInvariant
      (kernelCacheSemanticsWithInductives familyMemberModel.keys
        RawProjRel.none)
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      familyMemberSupport familyMemberInitial.env := by
  intro entry entryPresent
  cases entryPresent with
  | whnf lookup => exact familyMemberWhnfProvenance lookup
  | whnfNoDelta lookup => exact familyMemberWhnfNoDeltaProvenance lookup
  | whnfNoDeltaCheap lookup =>
      exact False.elim <| hashMapLookupFalseOfToListNil
        familyMemberWhnfNoDeltaCheapCacheEmpty lookup
  | whnfCore lookup => exact familyMemberWhnfCoreProvenance lookup
  | whnfCoreCheap lookup =>
      exact False.elim <| hashMapLookupFalseOfToListNil
        familyMemberWhnfCoreCheapCacheEmpty lookup
  | infer lookup => exact familyMemberInferProvenance lookup
  | inferOnly lookup =>
      exact False.elim <| hashMapLookupFalseOfToListNil
        familyMemberInferOnlyCacheEmpty lookup
  | defEq lookup =>
      exact False.elim <| hashMapLookupFalseOfToListNil
        familyMemberDefEqCacheEmpty lookup
  | defEqCheap lookup =>
      exact False.elim <| hashMapLookupFalseOfToListNil
        familyMemberDefEqCheapCacheEmpty lookup
  | defEqFailure contains =>
      exact False.elim <| hashSetContainsFalseOfToListNil
        familyMemberDefEqFailureCacheEmpty contains
  | unfold lookup =>
      exact False.elim <| hashMapLookupFalseOfToListNil
        familyMemberUnfoldCacheEmpty lookup
  | natSuccStuck contains =>
      exact False.elim <| hashSetContainsFalseOfToListNil
        familyMemberNatSuccStuckCacheEmpty contains
  | isProp lookup =>
      exact False.elim <| hashMapLookupFalseOfToListNil
        familyMemberIsPropCacheEmpty lookup
  | isRec lookup =>
      exact False.elim <| hashMapLookupFalseOfToListNil
        familyMemberIsRecCacheEmpty lookup
  | recursor lookup => exact familyMemberRecursorProvenance lookup
  | recMajors lookup => exact familyMemberRecMajorsProvenance lookup
  | blockPeer contains => exact familyMemberBlockPeerProvenance contains
  | blockResult lookup => exact familyMemberBlockResultProvenance lookup

/-- Concrete active scoped invariant at the exact entry point of the
production `IndexedVec.rec` member check. -/
theorem familyMemberInitial_activeInvariant :
    ScopedActiveWhnfStateInv familyMemberModel .accelerated
      (kernelCacheSemanticsWithInductives familyMemberModel.keys
        RawProjRel.none)
      familyMemberSupport recursorMembers [] familyMemberInitial where
  active := {
    blockState := {
      core := familyMemberInitial_stateWF
      loadedBlocks := familyMemberInitial_loadedBlocks }
    internSupport := familyMemberSupport_coversInitial
    caches := familyMemberInitial_cacheInvariant
    equivalences := familyMemberInitial_equivalences }
  context := familyMemberInitial_context
  layer := familyMemberInitial_primitives
  inScope := familyMemberModel_initialInScope

/-- Premise-free canonicality of the selected stored `IndexedVec.rec`
artifact after the complete production member-check prelude and frozen-cache
tail. -/
theorem familyMemberCheckCanonicalConcrete :
    GeneratedRecursorSemantics.CanonicalCacheAcceptance indexedVecFinalEnv
      nameOf RawProjRel.none
      transaction.certificate.generation recursorBlockId recursorId
      recursorConcrete.ty 2 false 1 1 2 1 familyId recursorRules
      familyInstalledRecursors checkerMethods
      (ScopedActiveWhnfStateInv familyMemberModel .accelerated
        (kernelCacheSemanticsWithInductives familyMemberModel.keys
          RawProjRel.none)
        familyMemberSupport recursorMembers [])
      familyMemberPreparationAfter familyMemberCheckAfter :=
  familyMemberCheckCanonicalFromInitialActiveScoped
    familyMemberModel_uvars familyMemberArtifactSuccessor
    familyMemberModel_lazyFaultPreserves familyMemberAuthorizedReferences
    familyMemberModel_populationScopeTransition
    (fun _ support => familyMemberSupport_new support)
    familyMemberInitial_activeInvariant

end Ix.Tc.IndexedRecursiveFixture
