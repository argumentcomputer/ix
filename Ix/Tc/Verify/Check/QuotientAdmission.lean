import Ix.Tc.Verify.Env
import Ix.Tc.Primitive
import Lean4Lean.Theory.Typing.QuotLemmas

/-!
# Atomic quotient admission

`KConst.quot` declarations are physically standalone entries, but their
semantic meaning is not four independent axioms. Lean4Lean installs `Quot`,
`Quot.mk`, `Quot.lift`, and `Quot.ind` in order and then registers one quotient
definitional equation. This file records the corresponding address-keyed Ix
boundary without granting a successful check of any one member authority over
the other three.

The relation deliberately retains each intermediate `VEnv`: later primitive
types mention earlier primitives, so translating all four against the initial
environment would be false. The production-checker proof still has to
construct this relation from the four exact `checkQuot` successes and the
`Eq`/`Eq.refl` prerequisite. Once it does, the theorems below close the atomic
Lean4Lean transition without another oracle.
-/

namespace Ix.Tc

open Lean4Lean (VDecl VEnv VConstant)

/-- One address-keyed quotient insertion in the exact environment where its
type is interpreted. The final conjunct prevents a prefix from masquerading
as the whole quotient bundle. -/
def QuotientAdmissionStep
    (catalog : Catalog) (nameOf : Address → Option Lean.Name)
    (trProj : RawProjRel) (id : KId .anon) (name : Lean.Name)
    (kind : Ix.QuotKind) (semantic : VConstant)
    (Next : VEnv → Prop) (before : VEnv) : Prop :=
  ∃ levels type after,
    catalog id = some (.quot () () kind levels type) ∧
    nameOf id.addr = some name ∧
    TrKConstant .safe before nameOf trProj
      (.quot () () kind levels type) semantic ∧
    before.addConst name semantic = some after ∧
    Next after

namespace QuotientAdmissionStep

/-- Compose one witnessed insertion with the remaining `Option` chain. -/
theorem bind
    {catalog : Catalog} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {id : KId .anon} {name : Lean.Name}
    {kind : Ix.QuotKind} {semantic : VConstant}
    {Next : VEnv → Prop} {before final : VEnv} {tail : VEnv → Option VEnv}
    (hnext : ∀ env, Next env → tail env = some final)
    (h : QuotientAdmissionStep catalog nameOf trProj id name kind
      semantic Next before) :
    before.addConst name semantic >>= tail = some final := by
  obtain ⟨levels, type, after, hcatalog, hname, htranslated, hadd,
    htail⟩ := h
  rw [hadd]
  exact hnext after htail

/-- Each step extends the Theory environment when its continuation does. -/
theorem le
    {catalog : Catalog} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {id : KId .anon} {name : Lean.Name}
    {kind : Ix.QuotKind} {semantic : VConstant}
    {Next : VEnv → Prop} {before final : VEnv}
    (hnext : ∀ env, Next env → env ≤ final)
    (h : QuotientAdmissionStep catalog nameOf trProj id name kind
      semantic Next before) :
    before ≤ final := by
  obtain ⟨levels, type, after, hcatalog, hname, htranslated, hadd,
    htail⟩ := h
  exact (VEnv.addConst_le hadd).trans (hnext after htail)

end QuotientAdmissionStep

/-- The complete address-keyed analogue of Lean4Lean's four-step
`AddQuot1` chain. The final equality installs the quotient defeq only after
all four exact constants have been added. -/
def QuotientBundleAdmission
    (catalog : Catalog) (nameOf : Address → Option Lean.Name)
    (trProj : RawProjRel) (prims : Primitives .anon)
    (before after : VEnv) : Prop :=
  QuotientAdmissionStep catalog nameOf trProj prims.quotType ``Quot
    .type Lean4Lean.quotConst (before := before) fun env₁ =>
  QuotientAdmissionStep catalog nameOf trProj prims.quotCtor ``Quot.mk
    .ctor Lean4Lean.quotMkConst (before := env₁) fun env₂ =>
  QuotientAdmissionStep catalog nameOf trProj prims.quotLift ``Quot.lift
    .lift Lean4Lean.quotLiftConst (before := env₂) fun env₃ =>
  QuotientAdmissionStep catalog nameOf trProj prims.quotInd ``Quot.ind
    .ind Lean4Lean.quotIndConst (before := env₃) fun env₄ =>
  env₄.addDefEq Lean4Lean.quotDefEq = after

/-- The complete semantic acceptance input: the pre-environment already has
the canonical `Eq`, and the four-member Ix bundle follows the exact atomic
Theory insertion chain. -/
structure QuotientAdmission
    (catalog : Catalog) (nameOf : Address → Option Lean.Name)
    (trProj : RawProjRel) (prims : Primitives .anon)
    (before after : VEnv) : Prop where
  ready : before.QuotReady
  bundle :
    QuotientBundleAdmission catalog nameOf trProj prims before after

namespace QuotientBundleAdmission

/-- Atomic admission contains exact catalog witnesses for all four primitive
roles. In particular, no successful prefix is a bundle witness. -/
theorem catalogEntries
    {catalog : Catalog} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {prims : Primitives .anon}
    {before after : VEnv}
    (h : QuotientBundleAdmission catalog nameOf trProj prims before after) :
    (∃ levels type,
      catalog prims.quotType = some (.quot () () .type levels type)) ∧
    (∃ levels type,
      catalog prims.quotCtor = some (.quot () () .ctor levels type)) ∧
    (∃ levels type,
      catalog prims.quotLift = some (.quot () () .lift levels type)) ∧
    (∃ levels type,
      catalog prims.quotInd = some (.quot () () .ind levels type)) := by
  unfold QuotientBundleAdmission at h
  obtain ⟨typeLevels, typeType, env₁, htype, _, _, _, h₁⟩ := h
  obtain ⟨ctorLevels, ctorType, env₂, hctor, _, _, _, h₂⟩ := h₁
  obtain ⟨liftLevels, liftType, env₃, hlift, _, _, _, h₃⟩ := h₂
  obtain ⟨indLevels, indType, env₄, hind, _, _, _, h₄⟩ := h₃
  exact ⟨⟨typeLevels, typeType, htype⟩,
    ⟨ctorLevels, ctorType, hctor⟩,
    ⟨liftLevels, liftType, hlift⟩,
    ⟨indLevels, indType, hind⟩⟩

/-- The address-keyed primitive table is tied to the four distinct Lean
names used by the Theory transition. -/
theorem nameAssignments
    {catalog : Catalog} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {prims : Primitives .anon}
    {before after : VEnv}
    (h : QuotientBundleAdmission catalog nameOf trProj prims before after) :
    nameOf prims.quotType.addr = some ``Quot ∧
    nameOf prims.quotCtor.addr = some ``Quot.mk ∧
    nameOf prims.quotLift.addr = some ``Quot.lift ∧
    nameOf prims.quotInd.addr = some ``Quot.ind := by
  unfold QuotientBundleAdmission at h
  obtain ⟨_, _, _, _, htype, _, _, h₁⟩ := h
  obtain ⟨_, _, _, _, hctor, _, _, h₂⟩ := h₁
  obtain ⟨_, _, _, _, hlift, _, _, h₃⟩ := h₂
  obtain ⟨_, _, _, _, hind, _, _, h₄⟩ := h₃
  exact ⟨htype, hctor, hlift, hind⟩

/-- A complete Ix bundle witness executes Lean4Lean's production-order
`addQuot` operation exactly. -/
theorem toAddQuot
    {catalog : Catalog} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {prims : Primitives .anon}
    {before after : VEnv}
    (h : QuotientBundleAdmission catalog nameOf trProj prims before after) :
    before.addQuot = some after := by
  unfold QuotientBundleAdmission at h
  unfold VEnv.addQuot
  apply h.bind
  intro env₁ h₁
  apply h₁.bind
  intro env₂ h₂
  apply h₂.bind
  intro env₃ h₃
  apply h₃.bind
  intro env₄ h₄
  simp only [h₄]

/-- Atomic quotient admission extends, rather than replacing, the prior
Theory environment. -/
theorem le
    {catalog : Catalog} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {prims : Primitives .anon}
    {before after : VEnv}
    (h : QuotientBundleAdmission catalog nameOf trProj prims before after) :
    before ≤ after := by
  unfold QuotientBundleAdmission at h
  apply h.le
  intro env₁ h₁
  apply h₁.le
  intro env₂ h₂
  apply h₂.le
  intro env₃ h₃
  apply h₃.le
  intro env₄ h₄
  rw [← h₄]
  exact VEnv.addDefEq_le

/-- The completed bundle installs the exact `Quot` type constant. -/
theorem quotType
    {catalog : Catalog} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {prims : Primitives .anon}
    {before after : VEnv}
    (h : QuotientBundleAdmission catalog nameOf trProj prims before after) :
    after.constants ``Quot = some Lean4Lean.quotConst :=
  VEnv.addQuot_quot h.toAddQuot

/-- The completed bundle installs the exact quotient constructor. -/
theorem quotCtor
    {catalog : Catalog} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {prims : Primitives .anon}
    {before after : VEnv}
    (h : QuotientBundleAdmission catalog nameOf trProj prims before after) :
    after.constants ``Quot.mk = some Lean4Lean.quotMkConst :=
  VEnv.addQuot_quotMk h.toAddQuot

/-- The completed bundle installs the exact computational eliminator. -/
theorem quotLift
    {catalog : Catalog} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {prims : Primitives .anon}
    {before after : VEnv}
    (h : QuotientBundleAdmission catalog nameOf trProj prims before after) :
    after.constants ``Quot.lift = some Lean4Lean.quotLiftConst :=
  VEnv.addQuot_quotLift h.toAddQuot

/-- The completed bundle installs the exact propositional eliminator. -/
theorem quotInd
    {catalog : Catalog} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {prims : Primitives .anon}
    {before after : VEnv}
    (h : QuotientBundleAdmission catalog nameOf trProj prims before after) :
    after.constants ``Quot.ind = some Lean4Lean.quotIndConst :=
  VEnv.addQuot_quotInd h.toAddQuot

/-- The quotient reduction equation is available only after the entire
bundle has been admitted. -/
theorem quotientDefEq
    {catalog : Catalog} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {prims : Primitives .anon}
    {before after : VEnv}
    (h : QuotientBundleAdmission catalog nameOf trProj prims before after) :
    after.defeqs Lean4Lean.quotDefEq :=
  VEnv.addQuot_defeq h.toAddQuot

end QuotientBundleAdmission

namespace QuotientAdmission

/-- The complete Ix-side witness constructs one Lean4Lean quotient
declaration transition; no member can be promoted separately. -/
theorem wf
    {catalog : Catalog} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {prims : Primitives .anon}
    {before after : VEnv}
    (h : QuotientAdmission catalog nameOf trProj prims before after) :
    VDecl.WF before .quot after :=
  .quot h.ready h.bundle.toAddQuot

/-- The atomic acceptance witness is monotone in the semantic environment. -/
theorem le
    {catalog : Catalog} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {prims : Primitives .anon}
    {before after : VEnv}
    (h : QuotientAdmission catalog nameOf trProj prims before after) :
    before ≤ after :=
  h.bundle.le

end QuotientAdmission

end Ix.Tc
