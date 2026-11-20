import IxVMRefinement.Binding.ClauseInvariant
import IxVMRefinement.Binding.OpInstall
import IxVMRefinement.Binding.IntEqns

/-! # The binding fold over the fold's clause: the step from its parts, the fold, both halves

* `bndOver_of_beforeRaise`: **the raise past a group**. From the invariant before the raise
  (`BeforeRaise`) to the invariant below `g + 1`: the clause at the top carried limit below
  `g + 1` is raised from the group's validation limit (`prefixInv_top_succ`), and lowered to
  every other carried limit within the groups below `g + 1`. Neither move needs anything beside
  `BeforeRaise`: the load contract's firing of the stored projection tables names no limit.
* `beforeRaise_of_kept`: the invariant before the raise at a group with no role unit, from its
  closure, the stored shapes and what the raise needs.
* `groupStepOver_of_parts`: **the step of a group from its parts**: the closure; at a group with
  no role unit the stored shapes (`RoleFreeShapes`; the fabricated roles' keys and the literal
  support at group 45 are derived here); and at a group whose role is a role unit, that unit's
  step.
* `fold_groups_over`: the invariant below every group from 6 to 77.
* `binding_skeleton_over`: **the binding half** for the internal part `OverW L`, from named
  hypotheses, each about an observed run.
* `typing_skeleton_over`: the typing half for the same internal part.
* `composed_skeleton_over`: the composed statement.
* `bndOver_basis_at`, `basisOver_of_run`: the invariant below group 6, for every well-formed
  table that pins the prelude and binds every role.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)
open IxVM.Refinement.TableInhabit (basisEnv)
open IxVM.Refinement.StoreInhabit (basisStore)

/-! ## The top carried limit -/

/-- The top carried limit within the first `n` groups is a carried limit. -/
theorem carried_topLim (n : Nat) : Carried (topLim n) := by
  by_cases hn : n < 77
  · rw [topLim_valLimit hn]
    exact carried_valLimit n
  · rw [topLim_none (by omega)]
    exact Or.inl rfl

/-- The top carried limit within the first `n` groups is within them. -/
theorem limWithin_topLim (t : Ix.Kernel.RoleTable) (n : Nat) :
    LimWithin (· < n) t (topLim n) := by
  by_cases hn : n < 77
  · rw [topLim_valLimit hn]
    exact limWithin_below t n
  · intro r _ _
    exact Nat.lt_of_lt_of_le (RoleVal.groupOf_lt_77 r) (by omega)

/-! ## The raise past a group -/

section Raise

variable {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} {t : Ix.Kernel.RoleTable}
  {g : Nat} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}

/-- **The invariant below `g + 1` from the invariant before the raise past `g`** (module
docstring). -/
theorem bndOver_of_beforeRaise (hall : AllBound t) (hg : g < 77)
    (h : BeforeRaise.{u} L t g R env) :
    BndOver.{u} L t (· < g + 1) R env := by
  obtain ⟨Reg, hR⟩ := h.clause
  refine ⟨h.shape, ⟨Reg, fun E hE lim hc hw => ?_⟩, h.facts⟩
  have h0 := hR E hE (some (valLimit g)) (carried_valLimit g) (limWithin_below t g)
  have hp0 : Decl.PrefixInv.{u} E t (topLim g) env := by
    rw [topLim_valLimit hg]
    exact h0.prefixInv
  have htop : Decl.PrefixInv.{u} E t (topLim (g + 1)) env :=
    prefixInv_top_succ hg hp0 h.raise
  have hinv : Decl.PrefixInv.{u} E t lim env :=
    prefixInv_lower htop (fun r hf => inForce_top hall hc hw hf)
  exact FoldClauseWith.of_prefix hinv h0.registry h0.hashKeyed h0.auxRoot
    ⟨h0.thmLevels, h0.storeArR⟩

/-- **The invariant before the raise at a group with no role unit**: the invariant below `g`,
the group's kept and prelude roles stored as their records declare them, the stored shapes
below `g + 1`, and what the raise past `g` needs. -/
theorem beforeRaise_of_kept (hall : AllBound t) (hb : BndOver.{u} L t (· < g) R env)
    (hkept : ∀ r ∈ roleGroup g, keptRole r → ∀ a, t.addressOf? r = some a →
      ∃ ci, env.find? (Ix.Kernel.Key.role r) = some ci ∧
        (PinnedBasis ci ∨ KeptIn t (recordOf R) (fun x => R.blobs.get? x) a ci))
    (hprel : ∀ r ∈ roleGroup g, r ∈ preludeRoles → ∀ a, t.addressOf? r = some a →
      ∃ ci, env.find? (Ix.Kernel.Key.role r) = some ci ∧
        (PinnedBasis ci ∨ KeptIn t (recordOf R) (fun x => R.blobs.get? x) a ci))
    (hshapes : Shapes (· < g + 1) env) (hraise : RaiseAt t env g) :
    BeforeRaise.{u} L t g R env := by
  have hs := hb.shape
  have hf := hb.facts
  refine ⟨?_, hb.clause, ?_, hraise⟩
  · exact {
      needsClosed := fun k hk r hr => by
        have h1 := groupNeeded_lt hr
        have h2 : k < g + 1 := hk
        show Ix.SpecDigest.groupOf r < g + 1
        omega
      bound := fun _ _ r _ => hall r
      prelude := hs.prelude
      literals := hs.literals
      hashed := hs.hashed
      usedClosed := hs.usedClosed
      committed := hs.committed
      zeroFree := hs.zeroFree
      kept := fun k r a hk hr hkr ha => by
        by_cases hkg : k < g
        · exact hs.kept k r a hkg hr hkr ha
        · have hk' : k < g + 1 := hk
          have e : k = g := by omega
          rw [e] at hr
          exact hkept r hr hkr a ha
      reading := hs.reading
      pins := hs.pins
      preludeKept := fun k r a hk hr hp ha => by
        by_cases hkg : k < g
        · exact hs.preludeKept k r a hkg hr hp ha
        · have hk' : k < g + 1 := hk
          have e : k = g := by omega
          rw [e] at hr
          exact hprel r hr hp a ha
      model := hs.model }
  · exact {
      whole := hf.whole
      opsPinned := hf.opsPinned
      opsAdmitted := fun r hr hst => Nat.lt_succ_of_lt (hf.opsAdmitted r hr hst)
      shapes := hshapes }

end Raise

/-! ## The step of a group from its parts -/

private theorem literalRoles_anchor : ∀ r ∈ literalRoles, r ∈ shapeAnchors := by decide

set_option maxRecDepth 100000 in
private theorem literalRoles_le : ∀ r ∈ literalRoles, Ix.SpecDigest.groupOf r ≤ 45 := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem natRoles_groups :
    Ix.SpecDigest.groupOf .nat < 41 ∧ Ix.SpecDigest.groupOf .natZero < 41 ∧
      Ix.SpecDigest.groupOf .natSucc < 41 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

private theorem valLimit_45 : valLimit 45 = 41 := by decide

/-- **The step of group `g` from its parts** (module docstring). -/
theorem groupStepOver_of_parts {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} {ρ : BRun}
    {t : Ix.Kernel.RoleTable} {g : Nat} (hall : AllBound t) (htwf : t.wf = true)
    (hg6 : 6 ≤ g) (hg : g < 77)
    (hcl : ClosureStepOver.{u} L ρ t g) (hnone : RoleFreeShapes.{u} L ρ t g)
    (hop : RoleUnitStepOver.{u} (· ∈ RoleOps.opRoles) L ρ t g)
    (hax : RoleUnitStepOver.{u} (· ∈ standardAxioms) L ρ t g) :
    GroupStepOver.{u} L ρ t g := by
  intro R R' env hb hadm hrd
  obtain ⟨R₁, env₁, hRR₁, hR₁R', hblobs, hunit, hext, hb₁, hkept, hrec₁⟩ := hcl R R' env hb hadm hrd
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
    · obtain ⟨env', hext', hb'⟩ := hop r a R R₁ R' env₁ hsingle hk ha hadm hrd hb₁ hadds
      exact ⟨env', fun ci h => hext' ci (hext ci h),
        bndOver_of_beforeRaise hall hg hb'⟩
    · obtain ⟨env', hext', hb'⟩ := hax r a R R₁ R' env₁ hsingle hk ha hadm hrd hb₁ hadds
      exact ⟨env', fun ci h => hext' ci (hext ci h),
        bndOver_of_beforeRaise hall hg hb'⟩
  · have hnu : ∀ r ∈ roleGroup g, ¬ (r ∈ RoleOps.opRoles ∨ r ∈ standardAxioms) :=
      fun r hr hk => hu ⟨r, hr, hk⟩
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
    have hrec' : ∀ x c, recordOf R' x = some c → (∀ ms, c.info ≠ .muts ms) →
        (env₁.find? (keyOf t x)).isSome = true := by
      intro x c hrc hnm
      rw [← recordOf_storeCongr hsame] at hrc
      exact hrec₁ x c hrc hnm
    have hshapes : Shapes (· < g + 1) env₁ := hnone hnu R R₁ R' env₁ hadm hrd hR₁R' hb₁ hkept hrec'
    have hfab := fabKeys_of_groupKept htwf hg6 hnu hkept
    have hlit : g = 45 → Ix.Kernel.strLitSupported env₁ = true ∧
        ∀ r ∈ literalRoles, Core.fabricatedRole r = true → ∀ a, t.addressOf? r = some a →
          ∃ ci, env₁.find? (Core.keyOf t a) = some ci := by
      intro h45
      refine ⟨?_, fun r hrl hf a ha => ?_⟩
      · obtain ⟨E, hE⟩ := OpInstall.recordsFor_exists hb₁.shape.committed
        obtain ⟨Reg, hR⟩ := hb₁.clause
        have hC := hR E hE (some (valLimit g)) (carried_valLimit g) (limWithin_below t g)
        obtain ⟨h1, h2, h3⟩ := natRoles_groups
        have hlim : ∀ n, some (valLimit g) = some n → n = 41 := by
          intro n hn
          rw [h45, valLimit_45] at hn
          exact (Option.some.inj hn).symm
        have hnat : Ix.Kernel.natLitSupported env₁ = true :=
          hC.companions.natLit ⟨hall .nat, fun n hn => by rw [hlim n hn]; exact h1⟩
            ⟨hall .natZero, fun n hn => by rw [hlim n hn]; exact h2⟩
            ⟨hall .natSucc, fun n hn => by rw [hlim n hn]; exact h3⟩
        refine strLitSupported_of_shapes hnat hshapes (fun r hr => ?_)
        have hle := literalRoles_le r hr
        show Ix.SpecDigest.groupOf r < g + 1
        omega
      · by_cases hlt : Ix.SpecDigest.groupOf r < g
        · obtain ⟨ci, hci, -⟩ := hb₁.shape.kept _ r a hlt (role_mem_roleGroup r)
            (Or.inl (Or.inr (literalRoles_anchor r hrl))) ha
          rw [Core.keyOf_of_addressOf htwf ha]
          exact ⟨ci, hci⟩
        · have hle : Ix.SpecDigest.groupOf r ≤ 45 := literalRoles_le r hrl
          have hgr : Ix.SpecDigest.groupOf r = g := by omega
          have hmem : r ∈ roleGroup g := by
            rw [← hgr]
            exact role_mem_roleGroup r
          exact hfab r hmem hf a ha
    have htail : g = 76 → Core.PrimEqnEnv env₁ := fun h76 => by
      subst h76
      exact primEqnEnv_of_bndOver hall hb₁ hshapes
    have hraise : RaiseAt t env₁ g :=
      raiseAt_of_noOps hg6 (fun r hr hop' => hnu r hr (Or.inl hop')) hfab hlit htail
    have hB : BeforeRaise.{u} L t g R₁ env₁ :=
      beforeRaise_of_kept hall hb₁ (fun r hr hkr a ha => hkept.1 r hr hkr (hnu r hr) a ha)
        hkept.2 hshapes hraise
    have hb₂ : BndOver.{u} L t (· < g + 1) R₁ env₁ :=
      bndOver_of_beforeRaise hall hg hB
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
    exact ⟨env₁, hext, bndOver_storeCongr hsame hsameB hb₂⟩

/-! ## The fold -/

/-- **The invariant below every group from 6 to 77.** -/
theorem fold_groups_over {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} {ρ : BRun}
    {t : Ix.Kernel.RoleTable} {Rs : Nat → Ixon.Env} {env₆ : Ix.Kernel.Env .anon}
    (hbase : BndOver.{u} L t (· < 6) (Rs 6) env₆)
    (hadm : ∀ g, 6 ≤ g → g < 77 → Admits ρ t g (Rs g) (Rs (g + 1)))
    (hrd : ∀ g, 6 ≤ g → g < 77 → AdmitsReads ρ t (Rs g) (Rs (g + 1)))
    (hstep : ∀ g, 6 ≤ g → g < 77 → GroupStepOver.{u} L ρ t g) :
    ∀ g, 6 ≤ g → g ≤ 77 → ∃ env : Ix.Kernel.Env .anon,
      (∀ ci ∈ env₆.consts, ci ∈ env.consts) ∧ BndOver.{u} L t (· < g) (Rs g) env := by
  intro g hg
  induction g, hg using Nat.le_induction with
  | base => exact fun _ => ⟨env₆, fun _ h => h, hbase⟩
  | succ g hg ih =>
    intro hg77
    obtain ⟨env, hext, hb⟩ := ih (by omega)
    obtain ⟨env', hext', hb'⟩ := hstep g hg (by omega) (Rs g) (Rs (g + 1)) env hb
      (hadm g hg (by omega)) (hrd g hg (by omega))
    exact ⟨env', fun ci h => hext' ci (hext ci h), hb'⟩

/-- **The invariant on the 77 groups gives a table witness on every group**, for the internal
part `OverW L`. -/
theorem overW_of_bndOver {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {t : Ix.Kernel.RoleTable} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (h : BndOver.{u} L t (· < 77) R env) :
    TableWitness.{u} (OverW.{u} L) t (fun _ => True) R env := by
  have hs : TableShape.{u} t (fun g => g < Ix.SpecDigest.groups.length) R env := by
    rw [groups_length]
    exact h.shape
  exact ⟨hs.of_all_groups,
    ⟨h.facts.whole, h.facts.opsPinned, fun _ _ _ => trivial,
      Shapes.mono (fun r _ => RoleVal.groupOf_lt_77 r) h.facts.shapes⟩,
    xAllGroups_foldClauseOver L t R env h.clause⟩

/-! ## The named hypotheses -/

/-- **A statement about each group from 6 to 76 of a run of a well-formed table that binds every
role.** -/
def AtGroups (Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop)
    (P : BRun → Ix.Kernel.RoleTable → Nat → Prop) : Prop :=
  ∀ t ρ Rs, Run t ρ Rs → AllBound t → t.check = .ok () → ∀ g, 6 ≤ g → g < 77 → P ρ t g

/-- **The six basis groups**: the invariant below group 6 at the store `Rs 6`. -/
def BasisOver (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop) : Prop :=
  ∀ t ρ Rs, Run t ρ Rs → AllBound t → t.check = .ok () →
    ∃ env, BndOver.{u} L t (· < 6) (Rs 6) env

/-! ## The binding half -/

/-- **The binding half over the fold's clause**, for the internal part `OverW L`. Its
hypotheses: the claim's export with the observed run record; the six basis groups; the
admission of each group and its reading clause; and for each group from 6 to 76 of a run, the
closure, the stored shapes where the group has no role unit, the step of an operation and the
step of a standard axiom. -/
theorem binding_skeleton_over {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    {calls : List (Call F)} {d : Digest}
    (bindingClaimExport : BindingClaimExportObs Run calls d)
    (basisGroups : BasisOver.{u} L Run)
    (groupAdmissions : AdmitsChain Run) (groupAdmissionReads : AdmitsReadsChain Run)
    (groupClosure : AtGroups Run (ClosureStepOver.{u} L))
    (groupWithoutRoleUnit : AtGroups Run (RoleFreeShapes.{u} L))
    (operationRoleUnit : AtGroups Run (RoleUnitStepOver.{u} (· ∈ RoleOps.opRoles) L))
    (standardAxiomRoleUnit : AtGroups Run (RoleUnitStepOver.{u} (· ∈ standardAxioms) L)) :
    BindingSpecOn.{u} (OverW.{u} L) calls d := by
  intro bytes spec a hde hdig V
  rcases bindingClaimExport bytes spec a hde hdig V with
    hcol | ⟨tb, t, htb, hadmt, hall, E₀, rank, Rs, hload, hrun⟩
  · exact Or.inl hcol
  · have ht : t.check = .ok () :=
      ((Ix.Kernel.Admission.admitBinding_ok_iff _ _ t).mp hadmt).wellFormed
    have htwf : t.wf = true := wf_of_check ht
    obtain ⟨env₆, hb6⟩ := basisGroups t _ Rs hrun hall ht
    obtain ⟨env, -, hb⟩ := fold_groups_over hb6 (groupAdmissions t _ Rs hrun)
      (groupAdmissionReads t _ Rs hrun)
      (fun g hg6 hg => groupStepOver_of_parts hall htwf hg6 hg
        (groupClosure t _ Rs hrun hall ht g hg6 hg)
        (groupWithoutRoleUnit t _ Rs hrun hall ht g hg6 hg)
        (operationRoleUnit t _ Rs hrun hall ht g hg6 hg)
        (standardAxiomRoleUnit t _ Rs hrun hall ht g hg6 hg)) 77 (by omega) (Nat.le_refl 77)
    have hlast := groupAdmissions t _ Rs hrun 76 (by omega) (by omega)
    exact Or.inr ⟨tb, t, Rs 77, env, htb, hadmt, hall,
      loadedBy_sub hload hlast.loaded hlast.loadedBlobs, overW_of_bndOver hb⟩

/-! ## The typing half and the composed statement -/

/-- **The typing half for the internal part `OverW L`**: the witness's clause is read at the
walk's limit, which a typing claim's context carries; the prefix invariant there is the
clause's, and the steps keep the part of the clause beside it. -/
theorem typing_skeleton_over {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop}
    {calls : List (Call F)} {d : Digest} (hb : Bounded calls)
    (hclaim : ClaimExport Walk calls d) (hlim : WalkLim Walk)
    (hgraph : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      TopGraph t E₀ seeds Top rank)
    (hstep : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      ∀ R envT E, StepCtx.{u} calls t R envT E₀ E →
        ∀ A c, Top A → recordOf E₀ A = some c → InLogic c → UnitKind c →
          UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim A c) :
    TypingSpecOn.{u} (OverW.{u} L) calls d := by
  intro bytes c hde hdig hscope V seeds hseeds ctx hctx tb t hadm R envT hW
  by_cases hnc : CollisionWith V (bytes :: tb :: committedFootprint) R calls
  · exact Or.inl hnc
  · refine Or.inr ?_
    have ht : t.check = .ok () :=
      ((Ix.Kernel.Admission.admitBinding_ok_iff _ _ t).mp hadm).wellFormed
    have hextra : ∀ x ∈ committedFootprint, x ∈ bytes :: tb :: committedFootprint :=
      fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
    rcases hclaim bytes c hde hdig hscope V seeds hseeds ctx hctx tb t hadm with
      hcol | ⟨E₀, lim, Top, rank, hS, hWalk⟩
    · exact (hnc (Or.inl hcol)).elim
    · have hF : BoundaryFacts t (fun _ => True) R envT := hW.facts.1
      obtain ⟨Reg, hR⟩ := hW.facts.2
      have hc : Carried lim := carried_of_typingLim (hlim t seeds E₀ lim Top rank hWalk)
      exact typing_skeleton_core_lim (X := fun E => FoldExtra.{u} L t E) hW.shape
        (fun E hE => (hR E hE lim hc (limWithin_all t lim)).prefixInv) hF.whole
        (fun E hE => (hR E hE lim hc (limWithin_all t lim)).extra) ht hb hextra hnc hS
        (hgraph t seeds E₀ lim Top rank hWalk)
        (fun E hE => hstep t seeds E₀ lim Top rank hWalk R envT E hE)

/-- **The composed statement with the fold's clause on both sides**, the binding half from its
named hypotheses and the typing half from the walk, its limit and its steps. -/
theorem composed_skeleton_over {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    {Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop}
    {callsA callsB : List (Call F)} {dA dB : Digest}
    (bindingClaimExport : BindingClaimExportObs Run callsB dB)
    (basisGroups : BasisOver.{u} L Run)
    (groupAdmissions : AdmitsChain Run) (groupAdmissionReads : AdmitsReadsChain Run)
    (groupClosure : AtGroups Run (ClosureStepOver.{u} L))
    (groupWithoutRoleUnit : AtGroups Run (RoleFreeShapes.{u} L))
    (operationRoleUnit : AtGroups Run (RoleUnitStepOver.{u} (· ∈ RoleOps.opRoles) L))
    (standardAxiomRoleUnit : AtGroups Run (RoleUnitStepOver.{u} (· ∈ standardAxioms) L))
    (hb : Bounded callsA) (hclaimA : ClaimExport Walk callsA dA) (hlim : WalkLim Walk)
    (hgraph : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      TopGraph t E₀ seeds Top rank)
    (hstepA : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      ∀ R envT E, StepCtx.{u} callsA t R envT E₀ E →
        ∀ A c, Top A → recordOf E₀ A = some c → InLogic c → UnitKind c →
          UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim A c) :
    ComposedSpec.{u} callsA callsB dA dB :=
  binding_discharge
    (binding_skeleton_over bindingClaimExport basisGroups groupAdmissions groupAdmissionReads
      groupClosure groupWithoutRoleUnit operationRoleUnit standardAxiomRoleUnit)
    (typing_skeleton_over hb hclaimA hlim hgraph hstepA)

/-! ## The six basis groups -/

/-- **The invariant below group 6 at every well-formed table that pins the prelude and binds
every role**, at the store of the basis rows and the environment of the pins, with the empty
registry. -/
theorem bndOver_basis_at (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ()) (hpre : PreludePinned t)
    (hall : AllBound t) : BndOver.{u} L t (· < 6) basisStore basisEnv :=
  BndOver.of_bnd (bnd_basis_at ht hpre hall (foldClauseOver_basis_at L ht hpre hall))

/-- **The basis hypothesis of the fold** for every run whose table pins the prelude and whose
store after the basis groups has the basis rows' entries. -/
theorem basisOver_of_run (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    (hrun : ∀ t ρ Rs, Run t ρ Rs → PreludePinned t ∧
      (∀ a, (Rs 6).consts.get? a = basisStore.consts.get? a) ∧
      ∀ a, (Rs 6).blobs.get? a = basisStore.blobs.get? a) :
    BasisOver.{u} L Run := by
  intro t ρ Rs hr hall ht
  obtain ⟨hpre, hc, hb⟩ := hrun t ρ Rs hr
  exact ⟨basisEnv, bndOver_storeCongr (fun a => (hc a).symm) (fun a => (hb a).symm)
    (bndOver_basis_at L ht hpre hall)⟩

end IxVM.Refinement.Binding
