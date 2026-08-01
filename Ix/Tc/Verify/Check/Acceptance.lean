import Ix.Tc.Verify.Check.DeclarationValidation
import Ix.Tc.Verify.Infer.SortTypes
import Ix.Tc.Verify.State

/-!
# Standalone declaration acceptance and promotion

The operational checker should produce only the typing fact which differs by
declaration kind.  Fresh installation and trusted-world promotion are then
pure consequences of the existing pending-declaration model.

This keeps K3's critical implication explicit:

* an axiom is accepted only when its declared type is a Theory type;
* a definition, opaque definition, or theorem is accepted only when its
  value has its declared Theory type.

No field below assumes a `VDecl.WF` transition.
-/

namespace Ix.Tc

open Lean4Lean (VConstant VDecl VDefVal VEnv VExpr)

/-! ## Semantic results of the two checker pipelines -/

/-- Evidence retained after the production `infer type; ensureSortDirect`
pipeline.  The inferred kernel type and its structural translation are kept
explicit so the two operational calls have to agree on the same witness. -/
def TypeCheckEvidence (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) (uvars : Nat) (Delta : KVLCtx)
    (sourceV : VExpr) : Prop :=
  ∃ inferred : KExpr .anon, ∃ inferredV : VExpr,
    TrKExpr world.venv uvars world.nameOf trProj Delta inferred inferredV ∧
    world.venv.HasType uvars Delta.toCtx sourceV inferredV ∧
    ∃ sort : KUniv .anon,
      SortView world support uvars Delta inferredV sort

namespace TypeCheckEvidence

/-- Successful inference followed by successful sort exposure proves that
the checked source is a Theory type. -/
theorem isType
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {sourceV : VExpr}
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (h : TypeCheckEvidence trProj world support uvars Delta sourceV) :
    world.venv.IsType uvars Delta.toCtx sourceV := by
  obtain ⟨_, _, _, hsourceType, sort, hsort⟩ := h
  exact ⟨sort.toVLevel,
    hsourceType.defeqU_r world.venvWF hDelta.toCtx hsort.inputEq⟩

end TypeCheckEvidence

/-- Evidence retained after inferring a definition value and accepting the
production `isDefEq inferredType declaredType` comparison. -/
def ValueCheckEvidence (world : VerifyWorld) (uvars : Nat)
    (Delta : KVLCtx) (valueV declaredTypeV : VExpr) : Prop :=
  ∃ inferredTypeV : VExpr,
    world.venv.HasType uvars Delta.toCtx valueV inferredTypeV ∧
    world.venv.IsDefEqU uvars Delta.toCtx inferredTypeV declaredTypeV

namespace ValueCheckEvidence

/-- A true definitional-equality result transports the inferred value type
to the declaration's advertised type. -/
theorem hasType
    {world : VerifyWorld} {uvars : Nat} {Delta : KVLCtx}
    {valueV declaredTypeV : VExpr}
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (h : ValueCheckEvidence world uvars Delta valueV declaredTypeV) :
    world.venv.HasType uvars Delta.toCtx valueV declaredTypeV :=
  let ⟨_, hvalueType, heq⟩ := h
  hvalueType.defeqU_r world.venvWF hDelta.toCtx heq

end ValueCheckEvidence

/-- The declaration-local semantic fact established by successful checking,
before freshness is used to install it in a new Theory environment. -/
def StandaloneAccepted (env : VEnv) : VDecl → Prop
  | .axiom ci => ci.toVConstant.WF env
  | .def ci | .opaque ci => ci.WF env
  | .block _ | .example _ | .quot | .induct _ => False

/-- The semantic evidence retained from the two production checker paths.
The type-check result is recorded for definitions as well as axioms because
`checkConstMember` checks the advertised type before checking the value.
Only the value-check result is needed by Theory's `VDefVal.WF`; keeping both
premises makes the operational acceptance boundary exact. -/
inductive StandaloneCheckEvidence (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) : VDecl → Prop
  | axiom {ci : Lean4Lean.VConstVal} :
    TypeCheckEvidence trProj world support ci.uvars [] ci.type →
    StandaloneCheckEvidence trProj world support (.axiom ci)
  | defn {ci : Lean4Lean.VDefVal} :
    TypeCheckEvidence trProj world support ci.uvars [] ci.type →
    ValueCheckEvidence world ci.uvars [] ci.value ci.type →
    StandaloneCheckEvidence trProj world support (.def ci)
  | opaque {ci : Lean4Lean.VDefVal} :
    TypeCheckEvidence trProj world support ci.uvars [] ci.type →
    ValueCheckEvidence world ci.uvars [] ci.value ci.type →
    StandaloneCheckEvidence trProj world support (.opaque ci)

namespace StandaloneCheckEvidence

/-- The exact successful checker evidence implies the declaration-local
Theory acceptance fact.  The empty translation context is well formed by
definition, so no ambient typing assumption enters this implication. -/
theorem accepted
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {decl : VDecl}
    (h : StandaloneCheckEvidence trProj world support decl) :
    StandaloneAccepted world.venv decl := by
  cases h with
  | «axiom» htype =>
      exact TypeCheckEvidence.isType (by trivial) htype
  | defn _ hvalue =>
      exact ValueCheckEvidence.hasType (by trivial) hvalue
  | «opaque» _ hvalue =>
      exact ValueCheckEvidence.hasType (by trivial) hvalue

end StandaloneCheckEvidence

/-- The complete declaration-local result expected from K3: a validated raw
declaration has an exact untyped Theory translation, and the checker has
supplied the semantic evidence appropriate to its declaration kind. -/
structure StandaloneCheckResult (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (id : KId .anon)
    (concrete : KConst .anon) (decl : VDecl) : Prop where
  ingress : PreDeclRel world.venv world.nameOf trProj id concrete decl
  evidence : StandaloneCheckEvidence trProj world support decl

namespace StandaloneCheckResult

/-- A complete standalone result is semantically accepted independently of
freshness and promotion. -/
theorem accepted
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {id : KId .anon} {concrete : KConst .anon} {decl : VDecl}
    (h : StandaloneCheckResult trProj world support id concrete decl) :
    StandaloneAccepted world.venv decl :=
  h.evidence.accepted

end StandaloneCheckResult

namespace RawDeclRel

/-- A semantically accepted raw standalone declaration can be installed in
the Theory environment when its pending target name is fresh. -/
theorem wfOfAccepted
    {env : VEnv} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {id : KId .anon} {c : KConst .anon}
    {d : VDecl}
    (hraw : RawDeclRel env nameOf trProj id c d)
    (hfresh : ∀ ⦃name⦄, nameOf id.addr = some name →
      env.constants name = none)
    (haccepted : StandaloneAccepted env d) :
    ∃ env', VDecl.WF env d env' := by
  cases hraw with
  | @«axiom» nm lps isUnsafe lvls ty name tyV hname hty =>
      let ci : VConstant := { uvars := lvls.toNat, type := tyV }
      let env' : VEnv :=
        { env with constants := fun candidate =>
            if name = candidate then some ci
            else env.constants candidate }
      have hadd : env.addConst name ci = some env' := by
        simp [VEnv.addConst, hfresh hname, env', ci]
      exact ⟨env', VDecl.WF.axiom (by simpa [ci] using haccepted) hadd⟩
  | @defn nm lps kind safety hints lvls ty val leanAll block name tyV valV d
      hname hty hval hkind =>
      let ci : VDefVal :=
        { name, uvars := lvls.toNat, type := tyV, value := valV }
      let env' : VEnv :=
        { env with constants := fun candidate =>
            if name = candidate then some ci.toVConstant
            else env.constants candidate }
      have hadd : env.addConst name ci.toVConstant = some env' := by
        simp [VEnv.addConst, hfresh hname, env', ci]
      cases hkind with
      | defn =>
          exact ⟨env'.addDefEq ci.toDefEq, VDecl.WF.def haccepted hadd⟩
      | opaq | thm => exact ⟨env', VDecl.WF.opaque haccepted hadd⟩

end RawDeclRel

namespace PendingDecl

/-- Acceptance plus the existing pending-state invariant is sufficient for
one exact ghost promotion.  The concrete checker state is unchanged. -/
theorem promoteOfAccepted
    {trProj : RawProjRel} {world : VerifyWorld}
    {s : TcState .anon} {id : KId .anon} {d : VDecl}
    (hstate : TcStateWF trProj s world)
    (hpending : PendingDecl trProj world id d)
    (haccepted : StandaloneAccepted world.venv d) :
    ∃ world',
      Promotes world (fun target => target = id) world' ∧
      TcStateWF trProj s world' ∧
      TrustedDecl trProj world' id d := by
  obtain ⟨concrete, hcatalog, hraw, huntrusted, hclosed, hfresh⟩ :=
    hpending
  obtain ⟨venv', hwf⟩ := hraw.wfOfAccepted hfresh haccepted
  exact hstate.promote
    ⟨concrete, hcatalog, hraw, huntrusted, hclosed, hfresh⟩ hwf

/-- Validator scope, exact raw ingress, and successful checker evidence
assemble into the K3 result and one trusted-world promotion.  In particular,
scope alone cannot promote a declaration, and semantic evidence alone cannot
choose a translation for the concrete Ix syntax. -/
theorem checkResultAndPromote
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {s : TcState .anon} {id : KId .anon} {decl : VDecl}
    {concrete : KConst .anon}
    (hstate : TcStateWF trProj s world)
    (hprojection : trProj.SubstCompatible)
    (hliterals : ∀ literal, world.venv.ContainsLits literal)
    (hpending : PendingDecl trProj world id decl)
    (hcatalog : world.catalog id = some concrete)
    (hscope : StandaloneScope concrete)
    (hevidence : StandaloneCheckEvidence trProj world support decl) :
    StandaloneCheckResult trProj world support id concrete decl ∧
      ∃ world',
        Promotes world (fun target => target = id) world' ∧
        TcStateWF trProj s world' ∧
        TrustedDecl trProj world' id decl := by
  have hingress := hpending.toPre_of_scope
    hprojection hliterals hcatalog hscope
  exact ⟨⟨hingress, hevidence⟩,
    promoteOfAccepted hstate hpending hevidence.accepted⟩

/-- End-to-end K3 assembly at the standalone validation boundary.  The exact
production validator supplies raw scoping, while checker evidence supplies
semantic acceptance; together they produce the pre-translation result and a
fresh trusted-world promotion. -/
theorem checkValidatedResultAndPromote
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {s after : TcState .anon} {id : KId .anon} {decl : VDecl}
    {concrete : KConst .anon}
    (hstate : TcStateWF trProj s world)
    (hprojection : trProj.SubstCompatible)
    (hliterals : ∀ literal, world.venv.ContainsLits literal)
    (hpending : PendingDecl trProj world id decl)
    (hcatalog : world.catalog id = some concrete)
    (hresources : StandaloneValidationResources support concrete)
    (hcollision : support.CollisionFree)
    {methods : Methods .anon}
    (hvalidation :
      (RecM.validateConstWellScoped concrete).run methods s = .ok () after)
    (hevidence : StandaloneCheckEvidence trProj world support decl) :
    StandaloneCheckResult trProj world support id concrete decl ∧
      ∃ world',
        Promotes world (fun target => target = id) world' ∧
        TcStateWF trProj s world' ∧
        TrustedDecl trProj world' id decl :=
  checkResultAndPromote hstate hprojection hliterals hpending hcatalog
    (RecM.validateConstWellScoped_sound hresources hcollision hvalidation)
    hevidence

end PendingDecl

end Ix.Tc
