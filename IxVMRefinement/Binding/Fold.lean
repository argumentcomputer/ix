import IxVMRefinement.Binding.Raise

/-! # The binding half over explicit interfaces

`binding_skeleton` proves the binding half of the consistency statement
(`IxVM.Consistency.BindingSpecOn`, with `FactsWith X` for the witness's internal part, the form
`typing_skeleton` is stated for) from five named hypotheses, each the interface of a layer
proved elsewhere:

* `BindingClaimExport Run`: the claim layer. For an accepted `binding spec a` claim, the run
  hashed a collision, or it hashed table bytes that admit at `a` as a table binding every role,
  and there are a run view `ρ` (records loaded by the run) and a store sequence `Rs` with
  `Run t ρ Rs` (an abstract predicate: the claim layer chooses what evidence it carries).
* `BasisBase X Run`: the six basis groups. The invariant on the groups below 6, at the store
  `Rs 6` and some environment.
* `AdmitsChain Run`: the group's walk export. The run's admission of each group `g` from 6 to
  76 takes `Rs g` to `Rs (g + 1)` (`Admits`).
* `GroupSteps X Run`: the steps by kind. `StepCore` at each group from 6 to 76, below it.
* `XAllGroups X`: the extra clause on the 77 groups is the extra clause on every group.

What is proved here, with no further hypothesis: the iteration from group 6 to group 77
(`fold_groups`), the transfer of the invariant on the 77 groups to a table witness on every
group (`witness_of_bnd`: the prefix invariant at every limit is lowered from the one at no
limit, with the guard), that the final store is records the run loaded, and the composition
with the typing half (`composed_skeleton`, through `binding_discharge`).
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

/-! ## The iteration -/

section Fold

variable {X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
  {ρ : BRun} {t : Ix.Kernel.RoleTable} {Rs : Nat → Ixon.Env} {env₆ : Ix.Kernel.Env .anon}

/-- **The invariant on the groups below `g`, for every `g` from 6 to 77**, from the invariant
below 6, the admission of each group and the step at each group. -/
theorem fold_groups (hall : AllBound t) (hbase : Bnd.{u} X t (· < 6) (Rs 6) env₆)
    (hadm : ∀ g, 6 ≤ g → g < 77 → Admits ρ t g (Rs g) (Rs (g + 1)))
    (hstep : ∀ g, 6 ≤ g → g < 77 → StepCore.{u} X ρ t (· < g) g) :
    ∀ g, 6 ≤ g → g ≤ 77 → ∃ env : Ix.Kernel.Env .anon,
      (∀ ci ∈ env₆.consts, ci ∈ env.consts) ∧ Bnd.{u} X t (· < g) (Rs g) env := by
  intro g hg
  induction g, hg using Nat.le_induction with
  | base => exact fun _ => ⟨env₆, fun _ h => h, hbase⟩
  | succ g hg ih =>
    intro hg77
    obtain ⟨env, hext, hb⟩ := ih (by omega)
    obtain ⟨env', hext', hb'⟩ := hstep g hg (by omega) (Rs g) (Rs (g + 1)) env
      (fun r _ => hall r) (fun r hr => groupNeeded_lt hr) (limWithin_below t g) hb
      (hadm g hg (by omega))
    refine ⟨env', fun ci h => hext' ci (hext ci h), ?_⟩
    refine hb'.congr fun k => ⟨fun h => ?_, fun h => ?_⟩
    · show k < g + 1
      rcases h with h | h
      · have h' : k < g := h
        omega
      · omega
    · have h' : k < g + 1 := h
      show k < g ∨ k = g
      omega

end Fold

/-! ## From the 77 groups to a table witness -/

/-- Every role's group is below 77, so on the 77 groups no limit puts a role of a group outside
them in force. -/
theorem limWithin_none (t : Ix.Kernel.RoleTable) : LimWithin (· < 77) t none :=
  fun r _ _ => RoleVal.groupOf_lt_77 r

/-- **The invariant on the 77 groups gives a table witness on every group**, for the internal
part `FactsWith X`: the prefix invariant at every limit is lowered from the one at no limit (a
carried limit within the 77 groups). -/
theorem witness_of_bnd
    {X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {t : Ix.Kernel.RoleTable} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (hX : X t (· < 77) R env → X t (fun _ => True) R env) (h : Bnd.{u} X t (· < 77) R env) :
    TableWitness.{u} (FactsWith.{u} X) t (fun _ => True) R env := by
  have hs : TableShape.{u} t (fun g => g < Ix.SpecDigest.groups.length) R env := by
    rw [groups_length]
    exact h.shape
  refine ⟨hs.of_all_groups, ?_⟩
  have hF : Facts.{u} t (fun _ => True) R env :=
    { inv := fun E hE lim _ =>
        prefixInv_lower (h.facts.inv E hE none (Or.inl rfl) (limWithin_none t))
          (fun r hf => ⟨hf.1, fun n (hn : none = some n) => nomatch hn⟩)
      whole := h.facts.whole }
  exact ⟨hF, hX h.extra⟩

/-- A store held by the records the run loaded is loaded by the run. -/
theorem loadedBy_sub {calls : List (Call F)} {E₀ R : Ixon.Env} (hload : LoadedBy calls E₀)
    (hc : ∀ a lc, R.consts.get? a = some lc → E₀.consts.get? a = some lc)
    (hb : ∀ a b, R.blobs.get? a = some b → E₀.blobs.get? a = some b) : LoadedBy calls R :=
  ⟨fun a lc h => hload.1 a lc (hc a lc h), fun a b h => hload.2 a b (hb a b h)⟩

/-! ## The named hypotheses -/

/-- **The binding claim's export, as the fold takes it** (claim layer): for an accepted
`binding spec a` claim and any view, the run hashed a collision, or it hashed table bytes that
admit at `a` as a table binding every role, and there are a run view whose records the run
loaded and a store sequence that the claim layer's `Run` relates to the table. -/
def BindingClaimExport (Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop)
    (calls : List (Call F)) (d : Digest) : Prop :=
  ∀ (bytes : ByteArray) (spec a : _root_.Address), Ix.Claim.de bytes = .ok (.binding spec a) →
    packDigest (Address.blake3Pure bytes) = d → ∀ V : View,
      V.HashedCollision (bytes :: committedFootprint) calls ∨
        ∃ (tb : ByteArray) (t : Ix.Kernel.RoleTable),
          Hashed calls tb ∧
          Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨a, tb⟩ = .ok t ∧
          AllBound t ∧
          ∃ (ρ : BRun) (Rs : Nat → Ixon.Env), LoadedBy calls ρ.E₀ ∧ Run t ρ Rs

/-- **The six basis groups** (basis step): the invariant below group 6 at the store `Rs 6`. -/
def BasisBase (X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop) : Prop :=
  ∀ t ρ Rs, Run t ρ Rs → AllBound t → ∃ env, Bnd.{u} X t (· < 6) (Rs 6) env

/-- **The admission of each group** (the group's walk export): `Rs g` to `Rs (g + 1)` for
every group from 6 to 76. -/
def AdmitsChain (Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop) : Prop :=
  ∀ t ρ Rs, Run t ρ Rs → ∀ g, 6 ≤ g → g < 77 → Admits ρ t g (Rs g) (Rs (g + 1))

/-- **The step at each group** (the steps by kind): `StepCore` below `g` for every group from
6 to 76. -/
def GroupSteps (X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop) : Prop :=
  ∀ t ρ Rs, Run t ρ Rs → AllBound t → ∀ g, 6 ≤ g → g < 77 → StepCore.{u} X ρ t (· < g) g

/-- **The extra clause on the 77 groups is the extra clause on every group.** -/
def XAllGroups (X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop) :
    Prop :=
  ∀ t R env, X t (· < 77) R env → X t (fun _ => True) R env

theorem xAllGroups_true : XAllGroups (fun _ _ _ _ => True) :=
  fun _ _ _ _ => trivial

/-! ## The skeleton -/

/-- **The binding half over explicit interfaces** (module docstring). -/
theorem binding_skeleton
    {X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    {calls : List (Call F)} {d : Digest}
    (hclaim : BindingClaimExport Run calls d) (hbase : BasisBase.{u} X Run)
    (hadm : AdmitsChain Run) (hstep : GroupSteps.{u} X Run) (hX : XAllGroups X) :
    BindingSpecOn.{u} (FactsWith.{u} X) calls d := by
  intro bytes spec a hde hdig V
  rcases hclaim bytes spec a hde hdig V with hcol | ⟨tb, t, htb, hadmt, hall, ρ, Rs, hload, hrun⟩
  · exact Or.inl hcol
  · obtain ⟨env₆, hb6⟩ := hbase t ρ Rs hrun hall
    obtain ⟨env, -, hb⟩ := fold_groups hall hb6 (hadm t ρ Rs hrun)
      (hstep t ρ Rs hrun hall) 77 (by omega) (Nat.le_refl 77)
    have hlast := hadm t ρ Rs hrun 76 (by omega) (by omega)
    exact Or.inr ⟨tb, t, Rs 77, env, htb, hadmt, hall,
      loadedBy_sub hload hlast.loaded hlast.loadedBlobs, witness_of_bnd (hX t (Rs 77) env) hb⟩

/-- **The composed statement over explicit interfaces**: the binding half from
`binding_skeleton` and the typing half from `typing_skeleton`, for one extra clause `X`, give
`ComposedSpec` (`binding_discharge`). -/
theorem composed_skeleton
    {X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    {Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop}
    {callsA callsB : List (Call F)} {dA dB : Digest}
    (hclaimB : BindingClaimExport Run callsB dB) (hbase : BasisBase.{u} X Run)
    (hadm : AdmitsChain Run) (hstepB : GroupSteps.{u} X Run) (hX : XAllGroups X)
    (hb : Bounded callsA) (hclaimA : ClaimExport Walk callsA dA)
    (hgraph : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      TopGraph t E₀ seeds Top rank)
    (hstepA : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      ∀ R envT E, StepCtx.{u} callsA t R envT E₀ E →
        ∀ A c, Top A → recordOf E₀ A = some c → InLogic c → UnitKind c →
          UnitStep.{u} (X t (fun _ => True) R) t envT E₀ E lim A c) :
    ComposedSpec.{u} callsA callsB dA dB :=
  binding_discharge (binding_skeleton hclaimB hbase hadm hstepB hX)
    (typing_skeleton hb hclaimA hgraph hstepA)

end IxVM.Refinement.Binding
