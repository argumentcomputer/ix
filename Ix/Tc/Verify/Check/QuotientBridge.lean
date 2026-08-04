import Ix.Tc.Verify.Check.QuotientAdmission
import Ix.Tc.Verify.Whnf.RuntimeContracts
import Ix.Tc.Check

/-!
# Production quotient bridge

The production checker observes quotient primitives one physical declaration
at a time. Their Theory meaning is nevertheless one atomic `addQuot`
transaction. This module retains the four exact `checkQuot` executions,
converts their digest comparisons to semantic type equality under a scoped
collision hypothesis, and commits a completed `QuotientAdmission` as one
trusted-log event.
-/

namespace Ix.Tc

open Lean4Lean (VEnv)

namespace RecM

private theorem throw_run {alpha : Type} (methods : Methods .anon)
    (state : TcState .anon) (err : TcError .anon) :
    (throw err : RecM .anon alpha).run methods state = .error err state :=
  rfl

private theorem throw_bind_run {alpha beta : Type}
    (methods : Methods .anon) (state : TcState .anon) (err : TcError .anon)
    (next : alpha → RecM .anon beta) :
    ((throw err >>= next) : RecM .anon beta).run methods state =
      .error err state :=
  rfl

/-- Reaching the successful return of the post-routing body means its exact
canonical type-address guard passed. -/
theorem checkQuotBody_success_typeAddress
    {methods : Methods .anon} {p : Primitives .anon}
    {expectedKind kind : Ix.QuotKind} {levels : UInt64}
    {type : KExpr .anon} {before after : TcState .anon}
    (hrun : (checkQuotBody p expectedKind kind levels type).run methods
      before = .ok () after) :
    type.addr = (canonicalQuotType p kind).addr := by
  cases kind
  all_goals
    by_contra hne
    have hguard := (bne_iff_ne.mpr hne)
    simp [checkQuotBody, hguard] at hrun
    all_goals (repeat' split at hrun)
    all_goals simp_all [throw_bind_run, throw_run]

/-- Reaching the successful return also means the exact role-specific
universe-arity guard passed. -/
theorem checkQuotBody_success_levels
    {methods : Methods .anon} {p : Primitives .anon}
    {expectedKind kind : Ix.QuotKind} {levels : UInt64}
    {type : KExpr .anon} {before after : TcState .anon}
    (hrun : (checkQuotBody p expectedKind kind levels type).run methods
      before = .ok () after) :
    levels = match kind with
      | .lift => 2
      | .type | .ctor | .ind => 1 := by
  cases kind
  all_goals
    by_contra hne
    have hguard := (bne_iff_ne.mpr hne)
    simp [checkQuotBody, hguard] at hrun
    all_goals (repeat' split at hrun)
    all_goals simp_all [throw_bind_run, throw_run]

/-- Successful address routing exposes the exact post-routing body. This
private inversion lemma keeps every guard consequence tied to the real
`checkQuot` wrapper without duplicating its four-way route proof. -/
private theorem checkQuot_success_body
    {methods : Methods .anon} {id : KId .anon} {kind : Ix.QuotKind}
    {levels : UInt64} {type : KExpr .anon}
    {before after : TcState .anon}
    (hrun : (checkQuot id kind levels type).run methods before =
      .ok () after) :
    ∃ expectedKind,
      (checkQuotBody before.prims expectedKind kind levels type).run methods
        before = .ok () after := by
  unfold checkQuot at hrun
  rw [ReaderT.run_bind] at hrun
  change EStateM.bind
    ((prims : RecM .anon (Primitives .anon)).run methods) _ before =
      .ok () after at hrun
  unfold EStateM.bind at hrun
  rw [prims_run] at hrun
  simp only at hrun
  by_cases htype : id.addr = before.prims.quotType.addr
  · simp only [htype, beq_self_eq_true, ↓reduceIte, pure_bind] at hrun
    exact ⟨.type, hrun⟩
  · have htype' : (id.addr == before.prims.quotType.addr) = false :=
      beq_eq_false_iff_ne.mpr htype
    rw [htype'] at hrun
    simp only [Bool.false_eq_true, ↓reduceIte] at hrun
    by_cases hctor : id.addr = before.prims.quotCtor.addr
    · simp only [hctor, beq_self_eq_true, ↓reduceIte, pure_bind] at hrun
      exact ⟨.ctor, hrun⟩
    · have hctor' : (id.addr == before.prims.quotCtor.addr) = false :=
        beq_eq_false_iff_ne.mpr hctor
      rw [hctor'] at hrun
      simp only [Bool.false_eq_true, ↓reduceIte] at hrun
      by_cases hlift : id.addr = before.prims.quotLift.addr
      · simp only [hlift, beq_self_eq_true, ↓reduceIte, pure_bind] at hrun
        exact ⟨.lift, hrun⟩
      · have hlift' : (id.addr == before.prims.quotLift.addr) = false :=
          beq_eq_false_iff_ne.mpr hlift
        rw [hlift'] at hrun
        simp only [Bool.false_eq_true, ↓reduceIte] at hrun
        by_cases hind : id.addr = before.prims.quotInd.addr
        · simp only [hind, beq_self_eq_true, ↓reduceIte, pure_bind] at hrun
          exact ⟨.ind, hrun⟩
        · have hind' : (id.addr == before.prims.quotInd.addr) = false :=
            beq_eq_false_iff_ne.mpr hind
          rw [hind'] at hrun
          simp only [Bool.false_eq_true, ↓reduceIte, throw_bind_run] at hrun
          contradiction

/-- A successful production quotient check reached the body selected by the
primitive address table, so the declaration type passed the canonical digest
guard for its declared role. -/
theorem checkQuot_success_typeAddress
    {methods : Methods .anon} {id : KId .anon} {kind : Ix.QuotKind}
    {levels : UInt64} {type : KExpr .anon}
    {before after : TcState .anon}
    (hrun : (checkQuot id kind levels type).run methods before =
      .ok () after) :
    type.addr = (canonicalQuotType before.prims kind).addr := by
  obtain ⟨expectedKind, hbody⟩ := checkQuot_success_body hrun
  exact checkQuotBody_success_typeAddress hbody

/-- Production success pins the universe arity to `1/1/2/1` for
`Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind`. -/
theorem checkQuot_success_levels
    {methods : Methods .anon} {id : KId .anon} {kind : Ix.QuotKind}
    {levels : UInt64} {type : KExpr .anon}
    {before after : TcState .anon}
    (hrun : (checkQuot id kind levels type).run methods before =
      .ok () after) :
    levels = match kind with
      | .lift => 2
      | .type | .ctor | .ind => 1 := by
  obtain ⟨expectedKind, hbody⟩ := checkQuot_success_body hrun
  cases kind <;> exact checkQuotBody_success_levels hbody

/-- On the scoped finite run support, successful digest comparison identifies
the complete canonical quotient type, not merely its Blake3 address. -/
theorem checkQuot_success_type
    {methods : Methods .anon} {id : KId .anon} {kind : Ix.QuotKind}
    {levels : UInt64} {type : KExpr .anon}
    {before after : TcState .anon} {support : RunSupport}
    (hcollision : support.CollisionFree)
    (htype : support type)
    (hcanonical : support (canonicalQuotType before.prims kind))
    (hrun : (checkQuot id kind levels type).run methods before =
      .ok () after) :
    type = canonicalQuotType before.prims kind := by
  have herase := hcollision.expr htype hcanonical
    (checkQuot_success_typeAddress hrun)
  simpa only [KExpr.eraseMeta_anon] using herase

end RecM

/-! ## Four-check production evidence -/

/-- The four physical quotient declarations together with successful runs of
the exact production guard. The `Quot.lift` run includes the complete
`checkEqType`/`Eq.refl` prerequisite because that call is inside
`checkQuotBody`; no separate Boolean surrogate is admitted here. -/
structure CheckedQuotientBundle (catalog : Catalog) (methods : Methods .anon)
    (state : TcState .anon) where
  quotTypeLevels : UInt64
  quotTypeType : KExpr .anon
  quotTypeCatalog : catalog state.prims.quotType =
    some (.quot () () .type quotTypeLevels quotTypeType)
  quotTypeRun :
    (RecM.checkQuot state.prims.quotType .type quotTypeLevels quotTypeType).run
      methods state = .ok () state
  quotCtorLevels : UInt64
  quotCtorType : KExpr .anon
  quotCtorCatalog : catalog state.prims.quotCtor =
    some (.quot () () .ctor quotCtorLevels quotCtorType)
  quotCtorRun :
    (RecM.checkQuot state.prims.quotCtor .ctor quotCtorLevels quotCtorType).run
      methods state = .ok () state
  quotLiftLevels : UInt64
  quotLiftType : KExpr .anon
  quotLiftCatalog : catalog state.prims.quotLift =
    some (.quot () () .lift quotLiftLevels quotLiftType)
  quotLiftRun :
    (RecM.checkQuot state.prims.quotLift .lift quotLiftLevels quotLiftType).run
      methods state = .ok () state
  quotIndLevels : UInt64
  quotIndType : KExpr .anon
  quotIndCatalog : catalog state.prims.quotInd =
    some (.quot () () .ind quotIndLevels quotIndType)
  quotIndRun :
    (RecM.checkQuot state.prims.quotInd .ind quotIndLevels quotIndType).run
      methods state = .ok () state

/-- The finite address-faithfulness scope consumed by the four production
digest comparisons. It names both operands of every comparison explicitly. -/
structure QuotientCheckScope
    {catalog : Catalog} {methods : Methods .anon} {state : TcState .anon}
    (checks : CheckedQuotientBundle catalog methods state) where
  support : RunSupport
  collision : support.CollisionFree
  quotType : support checks.quotTypeType
  canonicalType : support (RecM.canonicalQuotType state.prims .type)
  quotCtor : support checks.quotCtorType
  canonicalCtor : support (RecM.canonicalQuotType state.prims .ctor)
  quotLift : support checks.quotLiftType
  canonicalLift : support (RecM.canonicalQuotType state.prims .lift)
  quotInd : support checks.quotIndType
  canonicalInd : support (RecM.canonicalQuotType state.prims .ind)

namespace CheckedQuotientBundle

theorem quotTypeCanonical
    {catalog : Catalog} {methods : Methods .anon} {state : TcState .anon}
    (checks : CheckedQuotientBundle catalog methods state)
    (scope : QuotientCheckScope checks) :
    checks.quotTypeType = RecM.canonicalQuotType state.prims .type :=
  RecM.checkQuot_success_type scope.collision scope.quotType
    scope.canonicalType checks.quotTypeRun

theorem quotCtorCanonical
    {catalog : Catalog} {methods : Methods .anon} {state : TcState .anon}
    (checks : CheckedQuotientBundle catalog methods state)
    (scope : QuotientCheckScope checks) :
    checks.quotCtorType = RecM.canonicalQuotType state.prims .ctor :=
  RecM.checkQuot_success_type scope.collision scope.quotCtor
    scope.canonicalCtor checks.quotCtorRun

theorem quotLiftCanonical
    {catalog : Catalog} {methods : Methods .anon} {state : TcState .anon}
    (checks : CheckedQuotientBundle catalog methods state)
    (scope : QuotientCheckScope checks) :
    checks.quotLiftType = RecM.canonicalQuotType state.prims .lift :=
  RecM.checkQuot_success_type scope.collision scope.quotLift
    scope.canonicalLift checks.quotLiftRun

theorem quotIndCanonical
    {catalog : Catalog} {methods : Methods .anon} {state : TcState .anon}
    (checks : CheckedQuotientBundle catalog methods state)
    (scope : QuotientCheckScope checks) :
    checks.quotIndType = RecM.canonicalQuotType state.prims .ind :=
  RecM.checkQuot_success_type scope.collision scope.quotInd
    scope.canonicalInd checks.quotIndRun

theorem quotTypeLevels_eq
    {catalog : Catalog} {methods : Methods .anon} {state : TcState .anon}
    (checks : CheckedQuotientBundle catalog methods state) :
    checks.quotTypeLevels = 1 := by
  simpa using RecM.checkQuot_success_levels checks.quotTypeRun

theorem quotCtorLevels_eq
    {catalog : Catalog} {methods : Methods .anon} {state : TcState .anon}
    (checks : CheckedQuotientBundle catalog methods state) :
    checks.quotCtorLevels = 1 := by
  simpa using RecM.checkQuot_success_levels checks.quotCtorRun

theorem quotLiftLevels_eq
    {catalog : Catalog} {methods : Methods .anon} {state : TcState .anon}
    (checks : CheckedQuotientBundle catalog methods state) :
    checks.quotLiftLevels = 2 := by
  simpa using RecM.checkQuot_success_levels checks.quotLiftRun

theorem quotIndLevels_eq
    {catalog : Catalog} {methods : Methods .anon} {state : TcState .anon}
    (checks : CheckedQuotientBundle catalog methods state) :
    checks.quotIndLevels = 1 := by
  simpa using RecM.checkQuot_success_levels checks.quotIndRun

end CheckedQuotientBundle

/-! ## Lean4Lean semantic transaction input -/

/-- Canonical semantic proposition for the transaction supplied by
Lean4Lean's quotient-environment proof. This is deliberately independent of
the physical catalog: the production runs above establish that the four
catalog types are these canonical expressions.

Until Lean4Lean's `addQuot.WF` checker-closure theorem is constructive, callers
may carry this proposition as the narrow temporary assumption. Making it a
`Prop` prevents the boundary from supplying executable data. The Ix bridge
itself introduces no axiom and exposes every premise that the future upstream
theorem must discharge. -/
inductive CanonicalQuotientSemanticTransaction
    (nameOf : Address → Option Lean.Name) (trProj : RawProjRel)
    (prims : Primitives .anon) (before after : VEnv) : Prop where
  | intro
      (ready : before.QuotReady)
      (env₁ : VEnv)
      (quotTypeName : nameOf prims.quotType.addr = some ``Quot)
      (quotTypeTranslated : TrKConstant .safe before nameOf trProj
        (.quot () () .type 1 (RecM.canonicalQuotType prims .type))
        Lean4Lean.quotConst)
      (quotTypeRaw : RawExprRel (uvars := 1) before nameOf trProj []
        (RecM.canonicalQuotType prims .type) Lean4Lean.quotConst.type)
      (addQuotType : before.addConst ``Quot Lean4Lean.quotConst = some env₁)
      (env₂ : VEnv)
      (quotCtorName : nameOf prims.quotCtor.addr = some ``Quot.mk)
      (quotCtorTranslated : TrKConstant .safe env₁ nameOf trProj
        (.quot () () .ctor 1 (RecM.canonicalQuotType prims .ctor))
        Lean4Lean.quotMkConst)
      (quotCtorRaw : RawExprRel (uvars := 1) env₁ nameOf trProj []
        (RecM.canonicalQuotType prims .ctor) Lean4Lean.quotMkConst.type)
      (addQuotCtor : env₁.addConst ``Quot.mk Lean4Lean.quotMkConst = some env₂)
      (env₃ : VEnv)
      (quotLiftName : nameOf prims.quotLift.addr = some ``Quot.lift)
      (quotLiftTranslated : TrKConstant .safe env₂ nameOf trProj
        (.quot () () .lift 2 (RecM.canonicalQuotType prims .lift))
        Lean4Lean.quotLiftConst)
      (quotLiftRaw : RawExprRel (uvars := 2) env₂ nameOf trProj []
        (RecM.canonicalQuotType prims .lift) Lean4Lean.quotLiftConst.type)
      (addQuotLift : env₂.addConst ``Quot.lift Lean4Lean.quotLiftConst = some env₃)
      (env₄ : VEnv)
      (quotIndName : nameOf prims.quotInd.addr = some ``Quot.ind)
      (quotIndTranslated : TrKConstant .safe env₃ nameOf trProj
        (.quot () () .ind 1 (RecM.canonicalQuotType prims .ind))
        Lean4Lean.quotIndConst)
      (quotIndRaw : RawExprRel (uvars := 1) env₃ nameOf trProj []
        (RecM.canonicalQuotType prims .ind) Lean4Lean.quotIndConst.type)
      (addQuotInd : env₃.addConst ``Quot.ind Lean4Lean.quotIndConst = some env₄)
      (final : env₄.addDefEq Lean4Lean.quotDefEq = after)

namespace CheckedQuotientBundle

/-- Combine four successful physical checks with the canonical Lean4Lean
transaction. Production supplies exact roles, arities, and collision-safe
types; the semantic input supplies the ordered `addQuot` meaning. -/
theorem toAdmission
    {catalog : Catalog} {methods : Methods .anon} {state : TcState .anon}
    (checks : CheckedQuotientBundle catalog methods state)
    (scope : QuotientCheckScope checks)
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {before after : VEnv}
    (semantic : CanonicalQuotientSemanticTransaction nameOf trProj
      state.prims before after) :
    QuotientAdmission catalog nameOf trProj state.prims before after := by
  rcases semantic with ⟨hready, env₁, htypeName, htypeTranslated, htypeRaw,
    haddType, env₂, hctorName, hctorTranslated, hctorRaw, haddCtor, env₃,
    hliftName, hliftTranslated, hliftRaw, haddLift, env₄, hindName,
    hindTranslated, hindRaw, haddInd, hfinal⟩
  refine ⟨hready, ?_⟩
  unfold QuotientBundleAdmission
  refine ⟨checks.quotTypeLevels, checks.quotTypeType, env₁,
    checks.quotTypeCatalog, htypeName, ?_, ?_, haddType, ?_⟩
  · simpa only [checks.quotTypeLevels_eq, checks.quotTypeCanonical scope] using
      htypeTranslated
  · simpa only [checks.quotTypeLevels_eq, checks.quotTypeCanonical scope] using
      htypeRaw
  · refine ⟨checks.quotCtorLevels, checks.quotCtorType, env₂,
      checks.quotCtorCatalog, hctorName, ?_, ?_, haddCtor, ?_⟩
    · simpa only [checks.quotCtorLevels_eq,
        checks.quotCtorCanonical scope] using hctorTranslated
    · simpa only [checks.quotCtorLevels_eq,
        checks.quotCtorCanonical scope] using hctorRaw
    · refine ⟨checks.quotLiftLevels, checks.quotLiftType, env₃,
        checks.quotLiftCatalog, hliftName, ?_, ?_, haddLift, ?_⟩
      · simpa only [checks.quotLiftLevels_eq,
          checks.quotLiftCanonical scope] using hliftTranslated
      · simpa only [checks.quotLiftLevels_eq,
          checks.quotLiftCanonical scope] using hliftRaw
      · refine ⟨checks.quotIndLevels, checks.quotIndType, env₄,
          checks.quotIndCatalog, hindName, ?_, ?_, haddInd, hfinal⟩
        · simpa only [checks.quotIndLevels_eq,
            checks.quotIndCanonical scope] using hindTranslated
        · simpa only [checks.quotIndLevels_eq,
            checks.quotIndCanonical scope] using hindRaw

end CheckedQuotientBundle

/-! ## Atomic trusted-log publication -/

/-- Exactly the four physical identifiers named by the primitive table.
This predicate is the trust-set delta for one quotient semantic transaction. -/
inductive QuotientMembers (prims : Primitives .anon) : KId .anon → Prop
  | quotType : QuotientMembers prims prims.quotType
  | quotCtor : QuotientMembers prims prims.quotCtor
  | quotLift : QuotientMembers prims prims.quotLift
  | quotInd : QuotientMembers prims prims.quotInd

namespace QuotientAdmission

/-- Replaying the single Lean4Lean quotient declaration after a well-formed
prefix produces a well-formed post-environment. -/
theorem afterWF
    {catalog : Catalog} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {prims : Primitives .anon}
    {before after : VEnv}
    (h : QuotientAdmission catalog nameOf trProj prims before after)
    (hbefore : before.WF) : after.WF := by
  obtain ⟨history, hhistory⟩ := hbefore
  exact ⟨.quot :: history, .decl h.wf hhistory⟩

/-- Every member of a completed quotient transaction has closed provenance
in the final Theory environment. Earlier member translations are transported
through the remaining insertions and the final quotient equation. -/
theorem entry
    {catalog : Catalog} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {prims : Primitives .anon}
    {before after : VEnv}
    (h : QuotientAdmission catalog nameOf trProj prims before after)
    (hafter : after.WF) {id : KId .anon}
    (hmember : QuotientMembers prims id) :
    TrustedCatalogEntry trProj catalog nameOf after id := by
  have hbundle := h.bundle
  unfold QuotientBundleAdmission at hbundle
  obtain ⟨typeLevels, typeType, env₁, hcatType, hnameType, htrType,
    hrawType, haddType, h₁⟩ := hbundle
  obtain ⟨ctorLevels, ctorType, env₂, hcatCtor, hnameCtor, htrCtor,
    hrawCtor, haddCtor, h₂⟩ := h₁
  obtain ⟨liftLevels, liftType, env₃, hcatLift, hnameLift, htrLift,
    hrawLift, haddLift, h₃⟩ := h₂
  obtain ⟨indLevels, indType, env₄, hcatInd, hnameInd, htrInd,
    hrawInd, haddInd, hfinal⟩ := h₃
  have henv₄ : env₄ ≤ after := by
    rw [← hfinal]
    exact VEnv.addDefEq_le
  have henv₃ : env₃ ≤ after :=
    (VEnv.addConst_le haddInd).trans henv₄
  have henv₂ : env₂ ≤ after :=
    (VEnv.addConst_le haddLift).trans henv₃
  have henv₁ : env₁ ≤ after :=
    (VEnv.addConst_le haddCtor).trans henv₂
  have henv₀ : before ≤ after :=
    (VEnv.addConst_le haddType).trans henv₁
  have hordered := hafter.ordered
  cases hmember with
  | quotType =>
      have hlookup := h.bundle.quotType
      exact .quotient hcatType .quotType hnameType
        (htrType.mono henv₀) (hrawType.mono henv₀) hlookup
        (hordered.constWF hlookup)
  | quotCtor =>
      have hlookup := h.bundle.quotCtor
      exact .quotient hcatCtor .quotCtor hnameCtor
        (htrCtor.mono henv₁) (hrawCtor.mono henv₁) hlookup
        (hordered.constWF hlookup)
  | quotLift =>
      have hlookup := h.bundle.quotLift
      exact .quotient hcatLift .quotLift hnameLift
        (htrLift.mono henv₂) (hrawLift.mono henv₂) hlookup
        (hordered.constWF hlookup)
  | quotInd =>
      have hlookup := h.bundle.quotInd
      exact .quotient hcatInd .quotInd hnameInd
        (htrInd.mono henv₃) (hrawInd.mono henv₃) hlookup
        (hordered.constWF hlookup)

/-- The ghost world obtained by publishing all four quotient members in one
semantic-log event. Catalog, block topology, and address naming stay fixed. -/
def admittedWorld
    {trProj : RawProjRel} {world : VerifyWorld}
    {prims : Primitives .anon} {after : VEnv}
    (h : QuotientAdmission world.catalog world.nameOf trProj prims
      world.venv after) : VerifyWorld where
  catalog := world.catalog
  blocks := world.blocks
  trusted := fun id => QuotientMembers prims id ∨ world.trusted id
  venv := after
  nameOf := world.nameOf
  venvWF := h.afterWF world.venvWF
  trustedCatalogued := by
    intro id htrusted
    rcases htrusted with hmember | hold
    · obtain ⟨concrete, _, _, hcatalog, _, _⟩ :=
        (h.entry (h.afterWF world.venvWF) hmember).lookup
      exact ⟨concrete, hcatalog⟩
    · exact world.trustedCatalogued hold

/-- Atomic quotient publication is a monotone world extension. -/
theorem le_admittedWorld
    {trProj : RawProjRel} {world : VerifyWorld}
    {prims : Primitives .anon} {after : VEnv}
    (h : QuotientAdmission world.catalog world.nameOf trProj prims
      world.venv after) :
    world ≤ h.admittedWorld :=
  ⟨rfl, rfl, rfl, fun {_} hold => Or.inr hold, h.le⟩

/-- The post-trust predicate is exact: only a quotient member can be added by
this transaction. -/
theorem exactPromotion
    {trProj : RawProjRel} {world : VerifyWorld}
    {prims : Primitives .anon} {after : VEnv}
    (h : QuotientAdmission world.catalog world.nameOf trProj prims
      world.venv after) :
    ExactPromotion world (QuotientMembers prims) h.admittedWorld := by
  refine ⟨h.le_admittedWorld, ?_⟩
  intro id
  rfl

/-- Commit the completed quotient transaction as one trusted-log event. No
proper prefix of the four insertion chain reaches this theorem. -/
theorem trustedCatalog
    {trProj : RawProjRel} {world : VerifyWorld}
    {prims : Primitives .anon} {after : VEnv}
    (h : QuotientAdmission world.catalog world.nameOf trProj prims
      world.venv after)
    (hrel : TrustedCatalogRel trProj world) :
    TrustedCatalogRel trProj h.admittedWorld := by
  change TrustedCatalogLog trProj world.catalog world.nameOf
    (fun id => QuotientMembers prims id ∨ world.trusted id) after
  exact TrustedCatalogLog.semanticBlock hrel h.le
    (h.afterWF world.venvWF)
    (fun {_} hmember => h.entry (h.afterWF world.venvWF) hmember)

/-- The public atomic result starts with every quotient member fresh and
packages exact trust-set growth with the consumer-facing trusted catalog
relation. Freshness rules out a previously authoritative proper prefix. -/
theorem admit
    {trProj : RawProjRel} {world : VerifyWorld}
    {prims : Primitives .anon} {after : VEnv}
    (h : QuotientAdmission world.catalog world.nameOf trProj prims
      world.venv after)
    (hfresh : ∀ ⦃id⦄, QuotientMembers prims id → ¬world.trusted id)
    (hrel : TrustedCatalogRel trProj world) :
    (∀ ⦃id⦄, QuotientMembers prims id → ¬world.trusted id) ∧
      ExactPromotion world (QuotientMembers prims) h.admittedWorld ∧
      TrustedCatalogRel trProj h.admittedWorld :=
  ⟨hfresh, h.exactPromotion, h.trustedCatalog hrel⟩

/-- Each of the four roles is trusted after the atomic publication. -/
theorem memberTrusted
    {trProj : RawProjRel} {world : VerifyWorld}
    {prims : Primitives .anon} {after : VEnv}
    (h : QuotientAdmission world.catalog world.nameOf trProj prims
      world.venv after) {id : KId .anon}
    (hmember : QuotientMembers prims id) :
    h.admittedWorld.trusted id :=
  Or.inl hmember

/-- Conversely, an identifier newly trusted by the quotient publication is
one of the four primitive-table members. -/
theorem newlyTrustedMember
    {trProj : RawProjRel} {world : VerifyWorld}
    {prims : Primitives .anon} {after : VEnv}
    (h : QuotientAdmission world.catalog world.nameOf trProj prims
      world.venv after) {id : KId .anon}
    (hafter : h.admittedWorld.trusted id)
    (hbefore : ¬world.trusted id) :
    QuotientMembers prims id :=
  h.exactPromotion.newlyTrusted hafter hbefore

end QuotientAdmission

namespace CheckedQuotientBundle

/-- Final ghost world of the complete production-to-semantics quotient
bridge. This definition is intentionally unavailable from an individual
member check: it requires the full four-run bundle and semantic transaction. -/
def admittedWorld
    {methods : Methods .anon} {state : TcState .anon}
    {trProj : RawProjRel} {world : VerifyWorld} {after : VEnv}
    (checks : CheckedQuotientBundle world.catalog methods state)
    (scope : QuotientCheckScope checks)
    (semantic : CanonicalQuotientSemanticTransaction world.nameOf trProj
      state.prims world.venv after) : VerifyWorld :=
  (checks.toAdmission scope semantic).admittedWorld

/-- Rebase the unchanged concrete checker state across the ghost-only atomic
quotient publication. Loaded/catalog agreement is preserved because the
catalog is immutable, and the intern table is untouched. -/
theorem admittedStateWF
    {methods : Methods .anon} {state : TcState .anon}
    {trProj : RawProjRel} {world : VerifyWorld} {after : VEnv}
    (checks : CheckedQuotientBundle world.catalog methods state)
    (scope : QuotientCheckScope checks)
    (semantic : CanonicalQuotientSemanticTransaction world.nameOf trProj
      state.prims world.venv after)
    (hstate : TcStateWF trProj state world) :
    TcStateWF trProj state (checks.admittedWorld scope semantic) := by
  let admission := checks.toAdmission scope semantic
  change TcStateWF trProj state admission.admittedWorld
  exact
    { trustedCatalog := admission.trustedCatalog hstate.trustedCatalog
      loaded := (LoadedAgrees.world_iff admission.le_admittedWorld).mp
        hstate.loaded
      intern := hstate.intern }

/-- End-to-end quotient bridge: a coherent concrete/ghost state, four exact
production runs, scoped collision freedom, freshness, and the Lean4Lean
semantic transaction yield one exact four-member promotion and one trusted-log
event while preserving the checker-state invariant. -/
theorem admitAtomically
    {methods : Methods .anon} {state : TcState .anon}
    {trProj : RawProjRel} {world : VerifyWorld} {after : VEnv}
    (checks : CheckedQuotientBundle world.catalog methods state)
    (scope : QuotientCheckScope checks)
    (semantic : CanonicalQuotientSemanticTransaction world.nameOf trProj
      state.prims world.venv after)
    (hstate : TcStateWF trProj state world)
    (hfresh : ∀ ⦃id⦄,
      QuotientMembers state.prims id → ¬world.trusted id) :
    (∀ ⦃id⦄, QuotientMembers state.prims id → ¬world.trusted id) ∧
      ExactPromotion world (QuotientMembers state.prims)
        (checks.admittedWorld scope semantic) ∧
      TrustedCatalogRel trProj (checks.admittedWorld scope semantic) ∧
      TcStateWF trProj state (checks.admittedWorld scope semantic) := by
  have hadmission :=
    (checks.toAdmission scope semantic).admit hfresh hstate.trustedCatalog
  exact ⟨hadmission.1, hadmission.2.1, hadmission.2.2,
    checks.admittedStateWF scope semantic hstate⟩

end CheckedQuotientBundle

end Ix.Tc
