import IxVMRefinement.FamilyGraph.CheckedKinds
import IxVMRefinement.FamilyGraph.SkeletonModeled

/-! # The typing half composed over the family graph

The composed statement steps every top-walked unit by a plain `UnitStep`
(`Endpoint.unitSteps_of_kinds`, then `Binding.typing_skeleton_over`). A modeled block installs
its family record with itself, so its step is no plain `UnitStep`; this module states the typing
half's premise over the family graph and proves it from the rows the family kinds become:

* `FamilyRun`: what an accepted run gives of its family records, advice and twins at a walk and
  a witness: the graph, every top-walked non-empty block of recursors claimed or a twin, every
  top-walked block the run routes as modeled with a family record (an empty one included),
  and the family check of each family record and each twin at the walk's limit;
* the rows: `FamilyGraphRow` (the run's `FamilyRun`), `InnerCheckedRow` (the circuit side of
  the units a family check checks), `FamilyBlockRow` (`UnitStepFamily` of a block with its
  family record), `FamilyTwinRow` (`UnitStepTwin` of a second family record), the last two at
  the clause with the family recursors' companions beside it;
* `topUnitSteps_family`: the step of every top-walked unit that has no family record and is no
  twin from the kinds proved for the plain fold: a one-type block off the native route and a
  block of two or more inductive types are on the modeled route, so they have a family record;
  an unclaimed non-empty block of recursors that is no twin does not exist;
* `FamilySteps`, `familySteps_of_parts`, `familySteps_of_rows`: the typing half's premise over
  the family graph, from the rows (and, at the opened head trace, from the proved kinds and the
  telescope block's step stated once for every checked unit);
* `typing_skeleton_over_family`, `composed_skeleton_over_family`: `typing_skeleton_over` and
  `composed_skeleton_over` with that premise in place of the plain one. -/

universe u

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)
open IxVM.Refinement.Binding
open IxVM.Refinement.Endpoint
open TwinFamily (FamilyRecsModeled FamilyInstalled)
open FamilyAlias (FamilyCallAtLim)

set_option linter.unusedVariables false

/-! ## What the run gives of its families, and the rows -/

/-- **An advice-record check of the record at `a` among the calls `cs`**, under a role context
at `lim` with the table at the binding `bAddr`. -/
def AdviceCheckIn (cs : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (lim : Option Nat) (a : _root_.Address) : Prop :=
  ∃ (h h' : Aiur.Heap F)
    (rc xa seen wset r : Aiur.SourceValue F) (cs₁ : List (Call F)),
    Claim.RCLimRep t bAddr lim h rc ∧ Core.S0.addr h xa a ∧
    Aiur.Generic.SourceSemantics.ObsFn Obs.W "KernelModeled::check_advice_record"
      [rc, xa, seen, wset] h r h' cs₁ ∧ (∀ cl ∈ cs₁, cl ∈ cs)

/-- **A container recursor's check of the record at `a` among the calls `cs`**, under a role
context at `lim` with the table at the binding `bAddr`. -/
def ContainerRecCheckIn (cs : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (lim : Option Nat) (a : _root_.Address) : Prop :=
  ∃ (h h' : Aiur.Heap F)
    (rc xa ib r : Aiur.SourceValue F) (cs₁ : List (Call F)),
    Claim.RCLimRep t bAddr lim h rc ∧ Core.S0.addr h xa a ∧
    Aiur.Generic.SourceSemantics.ObsFn Obs.W "KernelModeled::check_container_rec"
      [rc, xa, ib] h r h' cs₁ ∧ (∀ cl ∈ cs₁, cl ∈ cs)

/-- **What an accepted run gives of its family records, advice and twins, at a walk and a
witness** (module docstring). `innerCall`: every inner record was checked by the family check
of a family record or of a twin, under the family check's own context at the walk's limit and
one binding: an advice record that is no projection record by its advice-record check, a
container's recursor by its check, a twin reached only through a container's recursor
projection by a family check at its own address nested in that check (its own checks are the
twin step's, not `InnerChecked`'s). An advice entry of a family check that is not in the graph's
advice owns no constant address and uses nothing in Lean's logic (a projection record of an
earlier advice block). -/
structure FamilyRun (calls : List (Call F)) (t : Ix.Kernel.RoleTable)
    (envT : Ix.Kernel.Env .anon) (E₀ : Ixon.Env) (lim : Option Nat)
    (Top : _root_.Address → Prop) (rank : _root_.Address → Nat)
    (fam twin : _root_.Address → Option _root_.Address)
    (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop) : Prop where
  graph : FamilyGraph t envT E₀ Top rank fam twin adv Inner
  /-- A top-walked non-empty block of recursors with a constant address the witness's
  environment does not store is a block's family record or a twin. -/
  claimed : ∀ (A : _root_.Address) (c : Ixon.Constant) (ms : Array Ixon.MutConst), Top A →
    recordOf E₀ A = some c → c.info = .muts ms → 0 < ms.size →
    (∀ m ∈ ms.toList, ∃ r, m = Ixon.MutConst.recr r) →
    (∃ x, ConstAddrOf A c x ∧ ¬ StoredAt t envT x) →
    (∃ B, fam B = some A) ∨ ∃ B, twin A = some B
  /-- A top-walked block of inductive types in Lean's logic the run routes as modeled, with a
  constant address the witness's environment does not store, has a family record (possibly
  empty). A block the witness already stores is no unit: the fold does not step it.
  (`ModeledRouteAt` reads the run's observations of the dispatch, so it holds of a record the
  dispatch never saw: the field is asked of blocks of inductive types only, the records the
  dispatch reads; and of blocks in Lean's logic, since the modeled arm of `check_const` runs
  the family check only for a safe inductive.) -/
  modeled : ∀ B cb (ms : Array Ixon.MutConst), Top B → recordOf E₀ B = some cb → InLogic cb →
    cb.info = .muts ms → (∀ m ∈ ms.toList, ∃ ind, m = Ixon.MutConst.indc ind) →
    ModeledRouteAt calls B →
    (∃ x, ConstAddrOf B cb x ∧ ¬ StoredAt t envT x) → ∃ rb, fam B = some rb
  famCall : ∀ B rb, fam B = some rb → ModeledRouteAt calls B ∧
    ∃ bAddr cs, FamilyCallAtLim calls bAddr t B rb lim cs ∧
      ∀ a, AdviceIn cs a → adv B a ∨
        ((∀ ca x, recordOf E₀ a = some ca → ¬ ConstAddrOf a ca x) ∧
          ∀ x, UsedRef E₀ a x → ¬ NeedOk E₀ x)
  twinCall : ∀ rb' B, twin rb' = some B → ∃ bAddr cs, FamilyCallAtLim calls bAddr t B rb' lim cs
  innerCall : ∃ bAddr, ∀ a, Inner a → ∃ B rb cs,
    (fam B = some rb ∨ twin rb = some B) ∧ FamilyCallAtLim calls bAddr t B rb lim cs ∧
    ((AdviceCheckIn cs bAddr t lim a ∧ ∀ c, recordOf E₀ a = some c → ¬ IsProj c) ∨
      ContainerRecCheckIn cs bAddr t lim a ∨
      ∃ B' cs', twin a = some B' ∧ FamilyCallAtLim calls bAddr t B' a lim cs' ∧
        ∀ cl ∈ cs', cl ∈ cs)
  /-- A twin of a block with no family record in the graph (a block the witness's environment
  stores) is a second record of a family record the witness's environment stores whole, each
  recursor with its model companion (from the binding half: `StoredFamiliesInstalled`). -/
  storedTwin : ∀ rb' B, twin rb' = some B → fam B = none →
    ∃ rb crb, (∀ x, ConstAddrOf rb crb x → StoredAt t envT x) ∧ FamilyInstalled t envT rb crb

/-- **Row `familyGraph`**: at every walk of an accepted typing claim and every witness of the
table's shape, a rank of the same walk and the run's family records, advice, inner records and
twins at that rank. The walk constrains its rank only between top-walked addresses
(`topWalk_of_rankOrder`); the records a family check checks are ranked by the run's family
checks, between the walk's ranks (`topWalk_scale` leaves room). -/
def FamilyGraphRow : Prop :=
  ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
    (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
    (rank : _root_.Address → Nat), Claim.TopWalk calls t seeds E₀ lim Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon), TableShape.{u} t (fun _ => True) R envT →
      ∃ (rank' : _root_.Address → Nat) (fam twin : _root_.Address → Option _root_.Address)
        (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
        Claim.TopWalk calls t seeds E₀ lim Top rank' ∧
        FamilyRun calls t envT E₀ lim Top rank' fam twin adv Inner

/-- **Row `innerChecked`**: what the run gives of the records a family check checks, beside the
graph (`InnerChecked`: checked at the walk's limit, no inert reference, used references below,
the kinds of an inner block). -/
def InnerCheckedRow : Prop :=
  ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
    (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
    (rank : _root_.Address → Nat), Claim.TopWalk calls t seeds E₀ lim Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon)
      (fam twin : _root_.Address → Option _root_.Address)
      (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
      FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner →
      ∃ bAddr, InnerChecked calls bAddr t envT E₀ lim Top rank fam twin Inner

/-- **Row `familyBlock`**: the step of a top-walked block with a family record (possibly
empty), handed its advice and what the advice uses, at the fold's clause with the family
recursors' companions beside it. -/
def FamilyBlockRow (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) : Prop :=
  ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
    (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
    (rank : _root_.Address → Nat), Claim.TopWalk calls t seeds E₀ lim Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon) (E : Ixon.Env)
      (fam twin : _root_.Address → Option _root_.Address)
      (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
      FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner →
      StepCtx.{u} calls t R envT E₀ E →
      ∀ (A : _root_.Address) (c : Ixon.Constant) (rb : _root_.Address) (crb : Ixon.Constant)
        (rs : Array Ixon.MutConst), Top A → recordOf E₀ A = some c → InLogic c → UnitKind c →
        fam A = some rb → FamRecRecord E₀ rb crb rs →
        UnitStepFamily.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
          t envT E₀ E lim A c rb crb (adv A)

/-- **Row `familyTwin`**: the step of a second family record of a block, handed the block's
family record stored, at the fold's clause with the family recursors' companions beside it.
The block's family record is the graph's (`fam B = some rb`, installed by the block's unit
earlier in the fold), or one the witness's environment stores whole with its companions
(`fam B = none`, `FamilyRun.storedTwin`). -/
def FamilyTwinRow (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) : Prop :=
  ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
    (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
    (rank : _root_.Address → Nat), Claim.TopWalk calls t seeds E₀ lim Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon) (E : Ixon.Env)
      (fam twin : _root_.Address → Option _root_.Address)
      (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
      FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner →
      StepCtx.{u} calls t R envT E₀ E →
      ∀ (A : _root_.Address) (c : Ixon.Constant) (B rb : _root_.Address) (crb : Ixon.Constant),
        Walked Top Inner A → recordOf E₀ A = some c → InLogic c → twin A = some B →
        ((fam B = some rb ∧ recordOf E₀ rb = some crb) ∨
          (fam B = none ∧ (∀ x, ConstAddrOf rb crb x → StoredAt t envT x) ∧
            FamilyInstalled t envT rb crb)) →
        UnitStepTwin.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
          t envT E₀ E lim A c rb crb

/-- A twin's step at a family record the witness's environment stores is a plain step: every
environment the fold reaches extends the witness's, so the record's addresses are found. -/
theorem unitStep_of_twin_stored {X : Ix.Kernel.Env .anon → Prop} {t : Ix.Kernel.RoleTable}
    {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env} {lim : Option Nat} {A rb : _root_.Address}
    {c crb : Ixon.Constant} (hst : ∀ x, ConstAddrOf rb crb x → StoredAt t envT x)
    (h : UnitStepTwin.{u} X t envT E₀ E lim A c rb crb) : UnitStep.{u} X t envT E₀ E lim A c :=
  fun env hext hnd hinv hX hrefs hfresh => h env hext hnd hinv hX hrefs
    (fun x hx => by
      obtain ⟨ci, hci, hname⟩ := hst x hx
      exact find_isSome_of_storedAt ⟨ci, hext ci hci, hname⟩) hfresh

/-- The first member's address of a non-empty block is a constant address of it. -/
theorem constAddr_member0 {A : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hinfo : c.info = .muts ms) (h0 : 0 < ms.size) : ConstAddrOf A c (memberAddr A 0 ms[0]) :=
  Or.inr ⟨ms, 0, ms[0], hinfo, Array.getElem?_eq_getElem h0, Or.inl rfl⟩

/-! ## The top-walked units without a family record -/

/-- **The step of every top-walked unit that no block claims, that has no family record and is
no twin**, from the steps of the kinds of the plain fold: as `Endpoint.unitSteps_of_kinds`,
where a one-type block off the native route and a block of two or more inductive types are on
the modeled route, hence have a family record (`FamilyRun.modeled`), and a non-empty block of
recursors is claimed or a twin (`FamilyRun.claimed`). -/
theorem topUnitSteps_family
    {X : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop} {calls : List (Call F)}
    (standaloneDefinition : WalkedUnitStep.{u} X fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind = .defn)
    (standaloneTheoremOrOpaque : WalkedUnitStep.{u} X fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind ≠ .defn)
    (standaloneRecursor : WalkedUnitStep.{u} X fun _ _ _ _ c =>
      ∃ rc : Ixon.Recursor, c.info = .recr rc)
    (definitionBlock : WalkedUnitStep.{u} X fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ DefnBlock ms)
    (nativeBlockTelescope : WalkedUnitStep.{u} X fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind)
    (nativeBlockAlias : WalkedUnitStep.{u} X fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtAlias t E₀ B cb ind)
    (nativeBlockOtherTelescope : WalkedUnitStep.{u} X fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerTeleOther t E₀ B cb ind)
    {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (hWalk : Claim.TopWalk calls t seeds E₀ lim Top rank)
    {R : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hFR : FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner) :
    ∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c, Top A → Unclaimed fam A →
      recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = none → twin A = none →
      UnitStep.{u} (X t E) t envT E₀ E lim A c := by
  intro E hctx A c hT hU hc hlog hk hfa htw
  have hneed := Claim.TopWalk.need hWalk hT hc hk hlog
  obtain ⟨bAddr, hW, hG⟩ := hWalk
  have ht : t.check = .ok () := hW.check_ok
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  have hinert : InertClause t c := hW.inertClause hT hc
  have hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c :=
    coverAt_of_graph hG hctx.shape htwf hT hc hneed
  have hcanon₀ : L1.CanonicalHashCoverage E₀ calls := by
    intro bytes value hashed size exactRead
    obtain ⟨entry, stored, bytesEq, cached⟩ := hW.hashedStored bytes value hashed size
      (L1.deConstant_of_deConstantExact exactRead) exactRead
    refine ⟨⟨entry, value, stored, cached, ?_⟩, rfl⟩
    rw [bytesEq]
    exact exactRead
  have hcanon : L1.CanonicalHashCoverage E calls :=
    Assembly.canonicalHashCoverage_frame hcanon₀ hctx.recordsFor.1
      (fun a v h => hctx.runRecord a v ((hW.runStore.recordOf_eq_recordAt a).trans h))
  have hchk : (∃ ms, c.info = .muts ms ∧
        ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t A ms k lim) ∨
      Claim.CheckedLimAt calls bAddr t A lim := by
    obtain ⟨c', hc', h⟩ := hW.checked A hT
    have e : c' = c := Option.some.inj (hc'.symm.trans hc)
    rw [e] at h
    exact h
  have step : ∀ {Kind : List (Call F) → Ix.Kernel.RoleTable → Ixon.Env → _root_.Address →
      Ixon.Constant → Prop}, WalkedUnitStep.{u} X Kind → Kind calls t E₀ A c →
      UnitStep.{u} (X t E) t envT E₀ E lim A c := by
    intro Kind h hkind env hext hnd hinv hXe href hfresh
    have hns : ∀ x, ConstAddrOf A c x → ¬ StoredAt t envT x := by
      intro x hx hst
      obtain ⟨ci, hci, hname⟩ := hst
      have hs : (env.find? (keyOf t x)).isSome = true :=
        find_isSome_of_storedAt ⟨ci, hext ci hci, hname⟩
      rw [hfresh x hx] at hs
      simp at hs
    exact h calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog hkind
      ht hW.runStore hW.hashedStored hctx.toStepStore hcanon hinert hcover hchk hns
      (fun x hx => keyFree_of_not_stored hctx.shape ht (hns x hx))
      env hext hnd hinv hXe href hfresh
  have hnoFam : ∀ ms : Array Ixon.MutConst, c.info = .muts ms →
      (∀ m ∈ ms.toList, ∃ ind, m = Ixon.MutConst.indc ind) →
      (∃ x, ConstAddrOf A c x ∧ ¬ StoredAt t envT x) → ¬ ModeledRouteAt calls A := by
    intro ms hinfo hall hun hroute
    obtain ⟨rb, hrb⟩ := hFR.modeled A c ms hT hc hlog hinfo hall hroute hun
    rw [hfa] at hrb
    cases hrb
  -- a step is asked only at an environment that extends the witness's and stores none of the
  -- record's constant addresses, so a record the witness stores at an address needs none
  have byUnit : ∀ x, ConstAddrOf A c x → (¬ StoredAt t envT x → False) →
      UnitStep.{u} (X t E) t envT E₀ E lim A c := by
    intro x hx hcontra env hext _ _ _ _ hfresh
    exfalso
    refine hcontra fun hst => ?_
    obtain ⟨ci, hci, hname⟩ := hst
    have hs : (env.find? (keyOf t x)).isSome = true :=
      find_isSome_of_storedAt ⟨ci, hext ci hci, hname⟩
    rw [hfresh x hx] at hs
    simp at hs
  rcases hk with ⟨d, hinfo⟩ | ⟨rc, hinfo⟩ | ⟨ms, hinfo⟩
  · by_cases hkind : d.kind = .defn
    · exact step standaloneDefinition ⟨d, hinfo, hkind⟩
    · exact step standaloneTheoremOrOpaque ⟨d, hinfo, hkind⟩
  · exact step standaloneRecursor ⟨rc, hinfo⟩
  · by_cases hdefs : DefnBlock ms
    · exact step definitionBlock ⟨ms, hinfo, hdefs⟩
    · by_cases hone : ∃ ind : Ixon.Inductive, ms = #[.indc ind]
      · obtain ⟨ind, hms⟩ := hone
        rw [hms] at hinfo
        have hmem := hG.members A c #[.indc ind] hT hc hinfo 0 (.indc ind) (by rfl)
        have hrec : BlockUnitRecord E₀ A c ind :=
          ⟨hc, hinfo, hlog, hmem.1, fun j hj => hmem.2 ind j rfl hj⟩
        by_cases hnat : NativeRouteAt calls A
        · rcases formerAt_cases t E₀ A c ind with htele | halias | hother
          · exact step nativeBlockTelescope ⟨ind, hrec, hnat, htele⟩
          · exact step nativeBlockAlias ⟨ind, hrec, hnat, halias⟩
          · exact step nativeBlockOtherTelescope ⟨ind, hrec, hnat, hother⟩
        · have hx0 := constAddr_member0 (A := A) hinfo (by simp)
          exact byUnit _ hx0 fun hns =>
            hnoFam _ hinfo (fun m hm => ⟨ind, by simpa using hm⟩) ⟨_, hx0, hns⟩
              (modeled_of_offNativeRoute hW.runStore hctx.toStepStore hcanon
              hrec hchk hnat).1
      · rcases hW.otherBlock_cases hT hc hinfo hdefs (fun ind h => hone ⟨ind, h⟩) with
          ⟨hsize, hall⟩ | ⟨hpos, hall⟩
        · have hx0 := constAddr_member0 (A := A) hinfo (by omega)
          exact byUnit _ hx0 fun hns =>
            hnoFam ms hinfo hall ⟨_, hx0, hns⟩
              (modeledRouteAt_of_multi ht hctx.toStepStore hc hinfo hsize hall).1
        · have hx0 := constAddr_member0 (A := A) hinfo hpos
          exact byUnit _ hx0 fun hns => by
            rcases hFR.claimed A c ms hT hc hinfo hpos hall ⟨_, hx0, hns⟩ with ⟨B, hB⟩ | ⟨B, hB⟩
            · exact hU B hB
            · rw [htw] at hB
              cases hB

/-! ## The typing half's premise over the family graph -/

/-- **The typing half's premise over the family graph**: at every walk and every witness of the
table's shape, a rank of the same walk, a family graph at it and the four kinds of step the
family skeleton asks (`typing_skeleton_core_family_modeled`). It replaces the premise "a plain
`UnitStep` of every top-walked unit" of `Binding.typing_skeleton_over`. -/
def FamilySteps (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (calls : List (Call F))
    (Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop) : Prop :=
  ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon), TableShape.{u} t (fun _ => True) R envT →
      ∃ (rank' : _root_.Address → Nat) (fam twin : _root_.Address → Option _root_.Address)
        (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
        Walk t seeds E₀ lim Top rank' ∧
        FamilyGraph t envT E₀ Top rank' fam twin adv Inner ∧
        (∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c, Top A → Unclaimed fam A →
          recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = none → twin A = none →
          UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim A c) ∧
        (∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c, Inner A → Unclaimed fam A →
          recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = none → twin A = none →
          UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim A c) ∧
        (∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c rb crb rs, Top A →
          recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = some rb →
          FamRecRecord E₀ rb crb rs →
          UnitStepFamily.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
            t envT E₀ E lim A c rb crb (adv A)) ∧
        (∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c B rb crb, Walked Top Inner A →
          recordOf E₀ A = some c → InLogic c → twin A = some B → fam B = some rb →
          recordOf E₀ rb = some crb →
          UnitStepTwin.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
            t envT E₀ E lim A c rb crb) ∧
        (∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c B, Walked Top Inner A →
          recordOf E₀ A = some c → InLogic c → twin A = some B → fam B = none →
          UnitStep.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
            t envT E₀ E lim A c)

/-- **The typing half's premise from the rows**, for any link: the graph row, the step of the
units a family check checks (`innerSteps`), the family block and twin rows, and the kinds of the
plain fold for the other top-walked units. -/
theorem familySteps_of_parts {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (familyGraph : FamilyGraphRow.{u})
    (innerSteps : ∀ (calls : List (Call F)) t seeds E₀ lim Top rank,
      Claim.TopWalk calls t seeds E₀ lim Top rank →
      ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon)
        (fam twin : _root_.Address → Option _root_.Address)
        (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
        FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner →
        ∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c, Inner A → Unclaimed fam A →
          recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = none → twin A = none →
          UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim A c)
    (familyBlock : FamilyBlockRow.{u} L) (familyTwin : FamilyTwinRow.{u} L)
    (standaloneDefinition : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind = .defn)
    (standaloneTheoremOrOpaque : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind ≠ .defn)
    (standaloneRecursor : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ rc : Ixon.Recursor, c.info = .recr rc)
    (definitionBlock : WalkedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ DefnBlock ms)
    (nativeBlockTelescope : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind)
    (nativeBlockAlias : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtAlias t E₀ B cb ind)
    (nativeBlockOtherTelescope : WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerTeleOther t E₀ B cb ind)
    (calls : List (Call F)) :
    FamilySteps.{u} L calls (Claim.TopWalk calls) := by
  intro t seeds E₀ lim Top rank₀ hWalk₀ R envT hshape
  obtain ⟨rank, fam, twin, adv, Inner, hWalk, hFR⟩ :=
    familyGraph calls t seeds E₀ lim Top rank₀ hWalk₀ R envT hshape
  exact ⟨rank, fam, twin, adv, Inner, hWalk, hFR.graph,
    topUnitSteps_family standaloneDefinition standaloneTheoremOrOpaque standaloneRecursor
      definitionBlock nativeBlockTelescope nativeBlockAlias nativeBlockOtherTelescope hWalk hFR,
    innerSteps calls t seeds E₀ lim Top rank hWalk R envT fam twin adv Inner hFR,
    fun E => familyBlock calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR,
    fun E hctx A c B rb crb hW hc hlog htw hrb hcrb =>
      familyTwin calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR hctx A c B
        rb crb hW hc hlog htw (Or.inl ⟨hrb, hcrb⟩),
    fun E hctx A c B hW hc hlog htw hnone => by
      obtain ⟨rb, crb, hst, hinst⟩ := hFR.storedTwin A B htw hnone
      exact unitStep_of_twin_stored hst
        (familyTwin calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR hctx A c
          B rb crb hW hc hlog htw (Or.inr ⟨hnone, hst, hinst⟩))⟩

/-- **The typing half's premise from the rows at the opened head trace**: the proved kinds of
the plain fold are passed in, the telescope block's step is stated once for every checked unit
(its top-walked form is an instance, `walkedUnitStep_of_checked`), and the units a family check
checks are stepped by the same kind proofs (`innerUnitSteps_of_kinds`) from the circuit-side
row `innerChecked`. -/
theorem familySteps_of_rows (familyGraph : FamilyGraphRow.{u})
    (innerChecked : InnerCheckedRow)
    (familyBlock : FamilyBlockRow.{u} FormerOpenTraceAt)
    (familyTwin : FamilyTwinRow.{u} FormerOpenTraceAt)
    (nativeBlockTelescope :
      CheckedUnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt) fun calls t E₀ B cb =>
        ∃ ind : Ixon.Inductive,
          BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind)
    (calls : List (Call F)) :
    FamilySteps.{u} FormerOpenTraceAt calls (Claim.TopWalk calls) :=
  familySteps_of_parts familyGraph
    (fun calls t seeds E₀ lim Top rank hWalk R envT fam twin adv Inner hFR => by
      obtain ⟨bAddr, hIC⟩ :=
        innerChecked calls t seeds E₀ lim Top rank hWalk R envT fam twin adv Inner hFR
      obtain ⟨bAddrW, hW, hG⟩ := hWalk
      exact innerUnitSteps_of_kinds nativeBlockTelescope hG hFR.graph hIC hW.check_ok
        hW.runStore hW.hashedStored)
    familyBlock familyTwin
    (standaloneDefinition_foldExtra linkLaws_formerOpenTrace)
    (standaloneTheoremOrOpaque_foldExtra linkLaws_formerOpenTrace)
    (standaloneRecursor_of_freshNotBasis freshRecursorMajorNotBasis_walked)
    (definitionBlock_of_nonempty (definitionBlock_foldExtra linkLaws_formerOpenTrace))
    (walkedUnitStep_of_checked nativeBlockTelescope)
    nativeBlockAlias_walked
    nativeBlockOtherTelescope_step
    calls

/-! ## The typing half and the composed statement over the family graph -/

/-- **The typing half over the fold's clause, over the family graph**: `typing_skeleton_over`
with the premise `FamilySteps` in place of a plain step of every top-walked unit. -/
theorem typing_skeleton_over_family {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop}
    {calls : List (Call F)} {d : Digest} (hb : Bounded calls)
    (hclaim : ClaimExport Walk calls d) (hlim : WalkLim Walk)
    (hgraph : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      TopGraph t E₀ seeds Top rank)
    (hsteps : FamilySteps.{u} L calls Walk) :
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
      obtain ⟨rank', fam, twin, adv, Inner, hWalk', hFG, hTop, hInner, hFam, hTwin,
        hTwinStored⟩ := hsteps t seeds E₀ lim Top rank hWalk R envT hW.shape
      exact typing_skeleton_core_family_modeled (X := fun E => FoldExtra.{u} L t E) hW.shape
        (fun E hE => (hR E hE lim hc (limWithin_all t lim)).prefixInv) hF.whole
        (fun E hE => (hR E hE lim hc (limWithin_all t lim)).extra) ht hb hextra hnc hS
        (hgraph t seeds E₀ lim Top rank' hWalk') hFG hTop hInner hFam hTwin hTwinStored

/-- **The composed statement with the fold's clause on both sides, the typing half over the
family graph**: `composed_skeleton_over` with `FamilySteps` in place of the plain step. -/
theorem composed_skeleton_over_family {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
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
    (hstepsA : FamilySteps.{u} L callsA Walk) :
    ComposedSpec.{u} callsA callsB dA dB :=
  binding_discharge
    (binding_skeleton_over bindingClaimExport basisGroups groupAdmissions groupAdmissionReads
      groupClosure groupWithoutRoleUnit operationRoleUnit standardAxiomRoleUnit)
    (typing_skeleton_over_family hb hclaimA hlim hgraph hstepsA)

end IxVM.Refinement.Typing
