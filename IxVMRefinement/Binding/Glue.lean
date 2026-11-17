import IxVMRefinement.Binding.Close

/-! # The step of one group from its parts, and the fold with the reading clause

`StepCore` at a group is the closure of the group, then its role unit by kind, then the close
(`bnd_close`). This file states the parts as named interfaces and proves the step from them.

* `ClosureStep X ρ t g` (target T2b): from the invariant below `g` at `R`, `env` and the
  admission of `g`, a store `R₁` between `R` and `R'` that lacks only role-unit records, and a
  grown environment with the invariant below `g` at `R₁`, and the group's roles that are no role
  unit stored as their records declare them (`GroupKept`).
* `RoleNoneFacts X t g` (T3a's inputs): at a group with no role unit, what `bnd_close` needs
  beyond the closure: the stored shapes below `g + 1`, the group's fabricated roles' keys, the
  literal support at group 45, and the extra clause carried.
* `RoleUnitStep P X ρ t g` (T3b for `P` the operations, T3c for `P` the standard axioms): a
  group whose one role is a role unit: from the invariant below `g` at the closure's store and
  environment, and the record added at the role's address, the invariant below `g + 1`.
* `stepCoreR_of_parts`: the step from the parts and the store congruence of the invariant
  (`BndCongr`, target T1c).

The closure reads the new records over the fold's own store, and reloads them at every store
for it, so it needs `AdmitsReads` beside `Admits` (`Steps.lean`). `StepCore` does not take it, so
the step is stated as `StepCoreR` (with it), and the fold, the binding half and the composed
statement are restated over `StepCoreR` with the chain of `AdmitsReads` as one more hypothesis
(`fold_groups_r`, `binding_skeleton_r`, `composed_skeleton_r`).
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

/-! ## Stores -/

/-- `R` holds no more than `R'`, with the same entries. -/
def StoreLe (R R' : Ixon.Env) : Prop :=
  (∀ a lc, R.consts.get? a = some lc → R'.consts.get? a = some lc) ∧
  ∀ a b, R.blobs.get? a = some b → R'.blobs.get? a = some b

/-- **`R'` is `R₁` and the record at `a`.** -/
def AddsAt (R₁ R' : Ixon.Env) (a : _root_.Address) : Prop :=
  (∀ x lc, R₁.consts.get? x = some lc → R'.consts.get? x = some lc) ∧
  (∀ x lc, R'.consts.get? x = some lc → R₁.consts.get? x = some lc ∨ x = a) ∧
  ∀ x b, R'.blobs.get? x = some b ↔ R₁.blobs.get? x = some b

/-- **The invariant depends on the store only through its entries** (target T1c). -/
def BndCongr (X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop) :
    Prop :=
  ∀ (t : Ix.Kernel.RoleTable) (G : Nat → Prop) (R R' : Ixon.Env) (env : Ix.Kernel.Env .anon),
    (∀ a, R.consts.get? a = R'.consts.get? a) → (∀ a, R.blobs.get? a = R'.blobs.get? a) →
    Bnd.{u} X t G R env → Bnd.{u} X t G R' env

/-! ## The parts of a group's step -/

/-- **The group's roles that are no role unit, stored as their records declare them**: the
kept roles and the prelude roles of `g`. -/
def GroupKept (t : Ix.Kernel.RoleTable) (g : Nat) (R : Ixon.Env) (env : Ix.Kernel.Env .anon) :
    Prop :=
  (∀ r ∈ roleGroup g, keptRole r → ¬ (r ∈ RoleOps.opRoles ∨ r ∈ standardAxioms) →
    ∀ a, t.addressOf? r = some a →
      ∃ ci, env.find? (Ix.Kernel.Key.role r) = some ci ∧
        (PinnedBasis ci ∨ KeptIn t (recordOf R) (fun x => R.blobs.get? x) a ci)) ∧
  (∀ r ∈ roleGroup g, r ∈ preludeRoles → ∀ a, t.addressOf? r = some a →
    ∃ ci, env.find? (Ix.Kernel.Key.role r) = some ci ∧
      (PinnedBasis ci ∨ KeptIn t (recordOf R) (fun x => R.blobs.get? x) a ci))

/-- **(T2b) The closure of group `g`** (module docstring). -/
def ClosureStep (X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (ρ : BRun) (t : Ix.Kernel.RoleTable) (g : Nat) : Prop :=
  ∀ (R R' : Ixon.Env) (env : Ix.Kernel.Env .anon),
    Bnd.{u} X t (· < g) R env → Admits ρ t g R R' → AdmitsReads ρ t R R' →
    ∃ (R₁ : Ixon.Env) (env₁ : Ix.Kernel.Env .anon),
      StoreLe R R₁ ∧ StoreLe R₁ R' ∧
      (∀ x b, R'.blobs.get? x = some b → R₁.blobs.get? x = some b) ∧
      (∀ a, (R'.consts.get? a).isSome = true → R₁.consts.get? a = none → RoleUnitAt t g a) ∧
      (∀ ci ∈ env.consts, ci ∈ env₁.consts) ∧
      Bnd.{u} X t (· < g) R₁ env₁ ∧ GroupKept t g R₁ env₁

/-- **What `bnd_close` needs at a group with no role unit beyond its closure** (T3a's inputs;
producers: the shapes (T5b), the kept anchors' keys, the literal support from the shapes). -/
def RoleNoneFacts (X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (t : Ix.Kernel.RoleTable) (g : Nat) : Prop :=
  ∀ (R : Ixon.Env) (env : Ix.Kernel.Env .anon),
    Bnd.{u} X t (· < g) R env → GroupKept t g R env →
      Shapes (· < g + 1) env ∧
      (∀ r ∈ roleGroup g, Core.fabricatedRole r = true → ∀ a, t.addressOf? r = some a →
        ∃ ci, env.find? (Core.keyOf t a) = some ci) ∧
      (g = 45 → Ix.Kernel.strLitSupported env = true) ∧
      (X t (· < g) R env → X t (· < g + 1) R env)

/-- **(T3b, T3c) The step of a group whose one role is a role unit** (module docstring); `P` is
membership in the operations or in the standard axioms. -/
def RoleUnitStep (P : Ix.Kernel.Role → Prop)
    (X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (ρ : BRun) (t : Ix.Kernel.RoleTable) (g : Nat) : Prop :=
  ∀ (r : Ix.Kernel.Role) (a : _root_.Address) (R R₁ R' : Ixon.Env) (env₁ : Ix.Kernel.Env .anon),
    roleGroup g = [r] → P r → t.addressOf? r = some a → Admits ρ t g R R' →
    Bnd.{u} X t (· < g) R₁ env₁ → AddsAt R₁ R' a →
    ∃ env' : Ix.Kernel.Env .anon, (∀ ci ∈ env₁.consts, ci ∈ env'.consts) ∧
      Bnd.{u} X t (· < g + 1) R' env'

/-- **The step of group `g`, with the reading clause** (`StepCore` with `AdmitsReads`, for the
groups below `g`). -/
def StepCoreR (X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (ρ : BRun) (t : Ix.Kernel.RoleTable) (g : Nat) : Prop :=
  ∀ (R R' : Ixon.Env) (env : Ix.Kernel.Env .anon),
    Bnd.{u} X t (· < g) R env → Admits ρ t g R R' → AdmitsReads ρ t R R' →
      ∃ env' : Ix.Kernel.Env .anon, (∀ ci ∈ env.consts, ci ∈ env'.consts) ∧
        Bnd.{u} X t (· < g + 1) R' env'

/-! ## The step from its parts -/

set_option maxRecDepth 100000 in
private theorem unit_single_all : (List.range 77).all (fun g =>
    (roleGroup g).all (fun r =>
      decide ((r ∈ RoleOps.opRoles ∨ r ∈ standardAxioms) → roleGroup g = [r]))) = true := by
  decide +kernel

/-- **A group holding a role unit holds that role alone** (decided). -/
theorem roleGroup_unit {g : Nat} {r : Ix.Kernel.Role} (hr : r ∈ roleGroup g)
    (hk : r ∈ RoleOps.opRoles ∨ r ∈ standardAxioms) : roleGroup g = [r] := by
  have hg : g < 77 := by
    by_contra hn
    rw [roleGroup_eq_nil (by rw [groups_length]; omega)] at hr
    cases hr
  have h1 : decide ((r ∈ RoleOps.opRoles ∨ r ∈ standardAxioms) → roleGroup g = [r]) = true :=
    List.all_eq_true.mp (List.all_eq_true.mp unit_single_all g (List.mem_range.mpr hg)) r hr
  exact of_decide_eq_true h1 hk

private theorem literal_anchor : ∀ r ∈ literalRoles, r ∈ shapeAnchors := by decide

set_option maxRecDepth 100000 in
private theorem literal_le : ∀ r ∈ literalRoles, Ix.SpecDigest.groupOf r ≤ 45 := by
  decide +kernel

/-- **The step of group `g` from its parts** (module docstring). -/
theorem stepCoreR_of_parts
    {X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {ρ : BRun} {t : Ix.Kernel.RoleTable} {g : Nat} (hall : AllBound t) (htwf : t.wf = true)
    (hg6 : 6 ≤ g)
    (hg : g < 77) (hcongr : BndCongr.{u} X) (hcl : ClosureStep.{u} X ρ t g)
    (hnone : RoleNoneFacts.{u} X t g)
    (hop : RoleUnitStep.{u} (· ∈ RoleOps.opRoles) X ρ t g)
    (hax : RoleUnitStep.{u} (· ∈ standardAxioms) X ρ t g) :
    StepCoreR.{u} X ρ t g := by
  intro R R' env hb hadm hrd
  obtain ⟨R₁, env₁, hRR₁, hR₁R', hblobs, hunit, hext, hb₁, hkept⟩ := hcl R R' env hb hadm hrd
  by_cases hu : ∃ r ∈ roleGroup g, r ∈ RoleOps.opRoles ∨ r ∈ standardAxioms
  · obtain ⟨r, hr, hk⟩ := hu
    have hsingle : roleGroup g = [r] := roleGroup_unit hr hk
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hall r)
    have hadds : AddsAt R₁ R' a := by
      refine ⟨hR₁R'.1, fun x lc hx => ?_, fun x b => ⟨hblobs x b, hR₁R'.2 x b⟩⟩
      cases h₁ : R₁.consts.get? x with
      | some lc' =>
        have e : some lc' = some lc := (hR₁R'.1 x lc' h₁).symm.trans hx
        exact Or.inl e
      | none =>
        obtain ⟨r', hr', ha', -⟩ := hunit x (by rw [hx]; rfl) h₁
        rw [hsingle] at hr'
        have er : r' = r := List.mem_singleton.mp hr'
        rw [er, ha] at ha'
        exact Or.inr (Option.some.inj ha').symm
    rcases hk with hk | hk
    · obtain ⟨env', hext', hb'⟩ := hop r a R R₁ R' env₁ hsingle hk ha hadm hb₁ hadds
      exact ⟨env', fun ci h => hext' ci (hext ci h), hb'⟩
    · obtain ⟨env', hext', hb'⟩ := hax r a R R₁ R' env₁ hsingle hk ha hadm hb₁ hadds
      exact ⟨env', fun ci h => hext' ci (hext ci h), hb'⟩
  · have hnu : ∀ r ∈ roleGroup g, ¬ (r ∈ RoleOps.opRoles ∨ r ∈ standardAxioms) :=
      fun r hr hk => hu ⟨r, hr, hk⟩
    obtain ⟨hshapes, hfab, hlit, hX⟩ := hnone R₁ env₁ hb₁ hkept
    have hlitKeys : g = 45 → ∀ r ∈ literalRoles, Core.fabricatedRole r = true →
        ∀ a, t.addressOf? r = some a → ∃ ci, env₁.find? (Core.keyOf t a) = some ci := by
      intro h45 r hrl hf a ha
      by_cases hlt : Ix.SpecDigest.groupOf r < g
      · obtain ⟨ci, hci, -⟩ := hb₁.shape.kept _ r a hlt (role_mem_roleGroup r)
          (Or.inl (Or.inr (literal_anchor r hrl))) ha
        rw [Core.keyOf_of_addressOf htwf ha]
        exact ⟨ci, hci⟩
      · have hle : Ix.SpecDigest.groupOf r ≤ 45 := literal_le r hrl
        have hgr : Ix.SpecDigest.groupOf r = g := by omega
        have hmem : r ∈ roleGroup g := by
          rw [← hgr]
          exact role_mem_roleGroup r
        exact hfab r hmem hf a ha
    have hraise : RaiseAt t env₁ g :=
      raiseAt_of_noOps hg6 (fun r hr hop' => hnu r hr (Or.inl hop')) hfab
        (fun h45 => ⟨hlit h45, hlitKeys h45⟩)
    have hb₂ : Bnd.{u} X t (· < g + 1) R₁ env₁ :=
      bnd_close hall hg hb₁ (fun r hr hkr a ha => hkept.1 r hr hkr (hnu r hr) a ha) hkept.2
        hshapes hraise hX
    have hsame : ∀ x, R₁.consts.get? x = R'.consts.get? x := by
      intro x
      cases h₁ : R₁.consts.get? x with
      | some lc => exact (hR₁R'.1 x lc h₁).symm
      | none =>
        cases h' : R'.consts.get? x with
        | none => rfl
        | some lc =>
          obtain ⟨r', hr', -, hk'⟩ := hunit x (by rw [h']; rfl) h₁
          exact absurd hk' (hnu r' hr')
    have hsameB : ∀ x, R₁.blobs.get? x = R'.blobs.get? x := by
      intro x
      cases h₁ : R₁.blobs.get? x with
      | some b => exact (hR₁R'.2 x b h₁).symm
      | none =>
        cases h' : R'.blobs.get? x with
        | none => rfl
        | some b =>
          have := hblobs x b h'
          rw [h₁] at this
          cases this
    exact ⟨env₁, hext, hcongr t _ R₁ R' env₁ hsame hsameB hb₂⟩

/-! ## The fold, the binding half and the composed statement over `StepCoreR` -/

/-- **The reading clause of each group's admission** (the group's walk export). -/
def AdmitsReadsChain (Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop) : Prop :=
  ∀ t ρ Rs, Run t ρ Rs → ∀ g, 6 ≤ g → g < 77 → AdmitsReads ρ t (Rs g) (Rs (g + 1))

/-- **The step at each group, with the reading clause.** -/
def GroupStepsR (X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop) : Prop :=
  ∀ t ρ Rs, Run t ρ Rs → AllBound t → ∀ g, 6 ≤ g → g < 77 → StepCoreR.{u} X ρ t g

/-- **The step at each group from its parts** (T6 for the steps). -/
theorem groupStepsR_of_parts
    {X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop} (hcongr : BndCongr.{u} X)
    (hwf : ∀ t ρ Rs, Run t ρ Rs → t.wf = true)
    (hparts : ∀ t ρ Rs, Run t ρ Rs → AllBound t → ∀ g, 6 ≤ g → g < 77 →
      ClosureStep.{u} X ρ t g ∧ RoleNoneFacts.{u} X t g ∧
        RoleUnitStep.{u} (· ∈ RoleOps.opRoles) X ρ t g ∧
        RoleUnitStep.{u} (· ∈ standardAxioms) X ρ t g) :
    GroupStepsR.{u} X Run := by
  intro t ρ Rs hrun hall g hg6 hg
  obtain ⟨hcl, hnone, hop, hax⟩ := hparts t ρ Rs hrun hall g hg6 hg
  exact stepCoreR_of_parts hall (hwf t ρ Rs hrun) hg6 hg hcongr hcl hnone hop hax

/-- **The invariant below every group from 6 to 77**, over `StepCoreR`. -/
theorem fold_groups_r
    {X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {ρ : BRun} {t : Ix.Kernel.RoleTable} {Rs : Nat → Ixon.Env} {env₆ : Ix.Kernel.Env .anon}
    (hbase : Bnd.{u} X t (· < 6) (Rs 6) env₆)
    (hadm : ∀ g, 6 ≤ g → g < 77 → Admits ρ t g (Rs g) (Rs (g + 1)))
    (hrd : ∀ g, 6 ≤ g → g < 77 → AdmitsReads ρ t (Rs g) (Rs (g + 1)))
    (hstep : ∀ g, 6 ≤ g → g < 77 → StepCoreR.{u} X ρ t g) :
    ∀ g, 6 ≤ g → g ≤ 77 → ∃ env : Ix.Kernel.Env .anon,
      (∀ ci ∈ env₆.consts, ci ∈ env.consts) ∧ Bnd.{u} X t (· < g) (Rs g) env := by
  intro g hg
  induction g, hg using Nat.le_induction with
  | base => exact fun _ => ⟨env₆, fun _ h => h, hbase⟩
  | succ g hg ih =>
    intro hg77
    obtain ⟨env, hext, hb⟩ := ih (by omega)
    obtain ⟨env', hext', hb'⟩ := hstep g hg (by omega) (Rs g) (Rs (g + 1)) env hb
      (hadm g hg (by omega)) (hrd g hg (by omega))
    exact ⟨env', fun ci h => hext' ci (hext ci h), hb'⟩

/-- **The binding half for `BW X`, over `StepCoreR`.** -/
theorem binding_skeleton_r
    {X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    {calls : List (Call F)} {d : Digest}
    (hclaim : BindingClaimExport Run calls d) (hbase : BasisBase.{u} X Run)
    (hadm : AdmitsChain Run) (hrd : AdmitsReadsChain Run) (hstep : GroupStepsR.{u} X Run)
    (hX : XAllGroups X) :
    BindingSpecOn.{u} (BW.{u} X) calls d := by
  intro bytes spec a hde hdig V
  rcases hclaim bytes spec a hde hdig V with hcol | ⟨tb, t, htb, hadmt, hall, ρ, Rs, hload, hrun⟩
  · exact Or.inl hcol
  · obtain ⟨env₆, hb6⟩ := hbase t ρ Rs hrun hall
    obtain ⟨env, -, hb⟩ := fold_groups_r hb6 (hadm t ρ Rs hrun) (hrd t ρ Rs hrun)
      (hstep t ρ Rs hrun hall) 77 (by omega) (Nat.le_refl 77)
    have hlast := hadm t ρ Rs hrun 76 (by omega) (by omega)
    exact Or.inr ⟨tb, t, Rs 77, env, htb, hadmt, hall,
      loadedBy_sub hload hlast.loaded hlast.loadedBlobs, bw_of_bnd (hX t (Rs 77) env) hb⟩

/-- **The composed statement over `StepCoreR`**: `composed_skeleton_carried` with the steps
taken with the reading clause. -/
theorem composed_skeleton_r
    {X : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    {Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop}
    {callsA callsB : List (Call F)} {dA dB : Digest}
    (hclaimB : BindingClaimExport Run callsB dB) (hbase : BasisBase.{u} (StoreX X) Run)
    (hadm : AdmitsChain Run) (hrd : AdmitsReadsChain Run)
    (hstepB : GroupStepsR.{u} (StoreX X) Run)
    (hb : Bounded callsA) (hclaimA : ClaimExport Walk callsA dA) (hlim : WalkLim Walk)
    (hgraph : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      TopGraph t E₀ seeds Top rank)
    (hstepA : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      ∀ R envT E, StepCtx.{u} callsA t R envT E₀ E →
        ∀ A c, Top A → recordOf E₀ A = some c → InLogic c → UnitKind c →
          UnitStep.{u} (X t E) t envT E₀ E lim A c) :
    ComposedSpec.{u} callsA callsB dA dB :=
  binding_discharge
    (binding_skeleton_r hclaimB hbase hadm hrd hstepB (xAllGroups_storeX X))
    (typing_skeleton_carried hb hclaimA hlim hgraph hstepA)

end IxVM.Refinement.Binding
