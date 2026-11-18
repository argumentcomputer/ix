import IxVMRefinement.FamilyAlias.ClaimRow
import IxVMRefinement.FamilyAlias.BlockLoads
import IxVMRefinement.FamilyAlias.UnitFree
import IxVMRefinement.Assembly.TypingDefnStep
import IxVMRefinement.Assembly.TypingBasisProj

/-! # The family row from the facts of the family check

`familyBlockRow_of_check`: the residual theorem's row `familyBlock` (`FamilyBlockRow`) from the
circuit side's facts that read the family check (`FamilyBlockCheckRow`): the seam, the
companion facts of each recursor the step stores, and the three load facts at its new constants
that read the family check (`FamilyLoadsCheck`; the other eleven are `FamLoadCtx.newLoads`, from
the store, the records, the route fact and the walk's check of the block,
`famLoadCtx_of_step`). The other two facts
`familyBlockRow_of_circuit` takes from the circuit side are proved at the row:

* `famBlockRecord_of_run`: the block's record is a block of inductives with its member and
  constructor projection records (`FamilyRun.famInd`, the walk's `TopGraph.members`);
* `famModeledAt_of_run`: the route fact at the block (`ModeledAt E A`), from the run-level
  modeled route of the family check (`FamilyChecksAt.famCall`), the walk's dispatch on the
  block's first member (`MemberCheckedLimAt.dispatch`), the dispatch's functionality and the
  run's coverage (`modeledAt_of_modeledRoute`);

and `hclaim` is `familyClaimRow`. Three of the load facts need the run beyond the route fact:
`famUnitFree_of_run` (a block of one inductive whose member has no index and one constructor
has a field in it: the dispatch at the store answers `1`, `famBlockRoute_of_run`, while the
walk's modeled constructor loop gives a field-less constructor the shape the dispatch answers `0`
at, `modeledCtor_trees`), the stored constructor's counts (`storedAs_ctor`), and the
constructors' shapes at a block of one inductive (`famCtorTrees_of_run`), which with the
dispatch's answer `1` refute the recursion scan's answer `0` at its member. -/

universe u

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (NativeFam DeclIndRenRunJ)
open IxVM.Refinement.Typing.TwinFamily (FamilyRecsModeled)
open IxVM.Refinement.Decl.FamilyAlias (AliasGroup famJ FamilyAdvice FamilyCheckFacts)

set_option linter.unusedVariables false

/-- **The block's record at the family row**: a block of inductives whose member and
constructor projection records the run's store holds. -/
theorem famBlockRecord_of_run {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat} {envT : Ix.Kernel.Env .anon}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hTW : Claim.TopWalk calls t seeds E₀ lim Top rank)
    (hrun : FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner)
    {A rb : _root_.Address} {c : Ixon.Constant} (hTop : Top A) (hc : recordOf E₀ A = some c)
    (hlog : InLogic c) (hfam : fam A = some rb) : ∃ ms, FamBlockRecord E₀ A c ms := by
  obtain ⟨-, -, hG⟩ := hTW
  obtain ⟨cb, ms, hcb, hmuts, hall⟩ := hrun.famInd A rb hfam
  have e : cb = c := Option.some.inj (hcb.symm.trans hc)
  rw [e] at hmuts
  exact ⟨ms,
    { record := hc
      muts := hmuts
      indcs := hall
      logic := hlog
      members := fun i m hm => (hG.members A c ms hTop hc hmuts i m hm).1
      ctors := fun i ind j hm hj => (hG.members A c ms hTop hc hmuts i _ hm).2 ind j rfl hj }⟩

/-- **The route fact at the block of the family row**: the family check runs on the modeled
route of the block (`FamilyChecksAt.famCall`), the walk's check of the block's first member
observed the dispatch on it, and the dispatch's answer is a function of the store's records, so
no good run answers `0` at the block. -/
theorem famModeledAt_of_run {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {E : Ixon.Env}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hTW : Claim.TopWalk calls t seeds E₀ lim Top rank)
    (hrun : FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner)
    (hctx : StepCtx.{u} calls t R envT E₀ E)
    {A rb : _root_.Address} {c : Ixon.Constant} (hTop : Top A) (hc : recordOf E₀ A = some c)
    (hfam : fam A = some rb) : ModeledAt E A := by
  obtain ⟨bAddr', hC⟩ := hrun.checks
  have hroute : ModeledRouteAt calls A := (hC.famCall A rb hfam).1
  obtain ⟨bAddr, hW, -⟩ := hTW
  obtain ⟨cb, ms, hcb, hmuts, hall⟩ := hrun.famInd A rb hfam
  have e : cb = c := Option.some.inj (hcb.symm.trans hc)
  rw [e] at hmuts
  obtain ⟨-, cb', hcb', -, x, hx, -⟩ := hrun.graph.famUnit A rb hfam
  have e' : cb' = c := Option.some.inj (hcb'.symm.trans hc)
  rw [e'] at hx
  have hpos : 0 < ms.size := by
    rcases hx with ⟨-, hs⟩ | ⟨ms', i, m, hms', hm, -⟩
    · exact (standalone_not_block hs ⟨ms, hmuts⟩).elim
    · have e2 : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hmuts)
      rw [e2] at hm
      have hmem : m ∈ ms.toList := by simpa using Array.mem_of_getElem? hm
      simpa using List.length_pos_of_mem hmem
  have hchk : (∃ ms, c.info = .muts ms ∧
        ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t A ms k lim) ∨
      Claim.CheckedLimAt calls bAddr t A lim := by
    obtain ⟨c', hc', h⟩ := hW.checked A hTop
    have e3 : c' = c := Option.some.inj (hc'.symm.trans hc)
    rw [e3] at h
    exact h
  have hm0 : Claim.MemberCheckedLimAt calls bAddr t A ms 0 lim :=
    Claim.membersChecked_of_block hW.runStore hc hmuts hchk 0 hpos
  have hobs := Claim.MemberCheckedLimAt.dispatch hW.runStore hall hm0
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
  exact modeledAt_of_modeledRoute (c := ⟨E, Ix.Kernel.Env.empty, t, none⟩)
    (hctx.good Ix.Kernel.Env.empty none) hcanon hroute hobs

/-- **The dispatch at the block of the family row answers `1` at the store**: the walk's
observation of the dispatch on the block's first member answers non-zero (the family check's
modeled route), and it agrees with `Route.blockRoute`, known where the run's coverage holds. -/
theorem famBlockRoute_of_run {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {E : Ixon.Env}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hTW : Claim.TopWalk calls t seeds E₀ lim Top rank)
    (hrun : FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner)
    (hctx : StepCtx.{u} calls t R envT E₀ E)
    {A rb : _root_.Address} {c : Ixon.Constant} (hTop : Top A) (hc : recordOf E₀ A = some c)
    (hfam : fam A = some rb) : Route.blockRoute E A = some true := by
  obtain ⟨bAddr', hC⟩ := hrun.checks
  have hroute : ModeledRouteAt calls A := (hC.famCall A rb hfam).1
  obtain ⟨bAddr, hW, -⟩ := hTW
  obtain ⟨cb, ms, hcb, hmuts, hall⟩ := hrun.famInd A rb hfam
  have e : cb = c := Option.some.inj (hcb.symm.trans hc)
  rw [e] at hmuts
  obtain ⟨-, cb', hcb', -, x, hx, -⟩ := hrun.graph.famUnit A rb hfam
  have e' : cb' = c := Option.some.inj (hcb'.symm.trans hc)
  rw [e'] at hx
  have hpos : 0 < ms.size := by
    rcases hx with ⟨-, hs⟩ | ⟨ms', i, m, hms', hm, -⟩
    · exact (standalone_not_block hs ⟨ms, hmuts⟩).elim
    · have e2 : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hmuts)
      rw [e2] at hm
      have hmem : m ∈ ms.toList := by simpa using Array.mem_of_getElem? hm
      simpa using List.length_pos_of_mem hmem
  have hchk : (∃ ms, c.info = .muts ms ∧
        ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t A ms k lim) ∨
      Claim.CheckedLimAt calls bAddr t A lim := by
    obtain ⟨c', hc', h⟩ := hW.checked A hTop
    have e3 : c' = c := Option.some.inj (hc'.symm.trans hc)
    rw [e3] at h
    exact h
  have hm0 : Claim.MemberCheckedLimAt calls bAddr t A ms 0 lim :=
    Claim.membersChecked_of_block hW.runStore hc hmuts hchk 0 hpos
  obtain ⟨bp, r, h, h', cs, b, ev, hsub, hb, hbA⟩ :=
    Claim.MemberCheckedLimAt.dispatch hW.runStore hall hm0
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
  have g : Core.Good ⟨E, Ix.Kernel.Env.empty, t, none⟩ cs :=
    (hctx.good Ix.Kernel.Env.empty none).sub hsub
  have hag := Route.block_is_modeled_agrees (E := E) g.1 g.2 hb ev
  obtain ⟨v, hv⟩ := hag.known (canonicalHashCoverage_sub hsub hcanon)
  have hr := hag.value v hv
  have hne := hroute bp r h h' cs b ev hsub hb hbA
  rw [← hbA]
  cases v with
  | false => exact absurd (hr.trans Route.bit_false) hne
  | true => exact hv

/-- **A block of one inductive at the family row whose member has no index and one constructor
has a field in that constructor**: at a field-less one the walk's modeled constructor loop gives
the constructor's stored type, after its parameters, the shape of a constant applied to
variables (`modeledCtor_trees`), where the dispatch's scan answers `0`; but the dispatch answers
`1` at the store (`famBlockRoute_of_run`). -/
theorem famUnitFree_of_run {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {E : Ixon.Env}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hTW : Claim.TopWalk calls t seeds E₀ lim Top rank)
    (hrun : FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner)
    (hctx : StepCtx.{u} calls t R envT E₀ E)
    {A rb : _root_.Address} {c : Ixon.Constant} (hTop : Top A) (hc : recordOf E₀ A = some c)
    (hlog : InLogic c) (hfam : fam A = some rb) :
    ∀ ind, c.info = .muts #[.indc ind] → ind.indices.toNat = 0 → ind.ctors.size = 1 →
      ∀ ct, ind.ctors[0]? = some ct → ct.fields.toNat ≠ 0 := by
  intro ind hmuts hidx hsz ct hct hf0
  have hR := famBlockRoute_of_run hTW hrun hctx hTop hc hfam
  have hmod := famModeledAt_of_run hTW hrun hctx hTop hc hfam
  obtain ⟨ms, hB⟩ := famBlockRecord_of_run hTW hrun hTop hc hlog hfam
  have hms : ms = #[.indc ind] := Ixon.ConstantInfo.muts.inj (hB.muts.symm.trans hmuts)
  subst hms
  obtain ⟨bAddr, hW, -⟩ := hTW
  have hchk : (∃ ms, c.info = .muts ms ∧
        ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t A ms k lim) ∨
      Claim.CheckedLimAt calls bAddr t A lim := by
    obtain ⟨c', hc', h⟩ := hW.checked A hTop
    have e3 : c' = c := Option.some.inj (hc'.symm.trans hc)
    rw [e3] at h
    exact h
  have hm0 : Claim.MemberCheckedLimAt calls bAddr t A #[.indc ind] 0 lim :=
    Claim.membersChecked_of_block hW.runStore hc hmuts hchk 0 Nat.zero_lt_one
  have hdec : L1.EnvDecoded E := hctx.recordsFor.1
  have hrec : ∀ a d, recordOf E₀ a = some d → recordOf E a = some d := fun a d hd' =>
    (recordOf_eq_recordAt_of_decoded hdec a).trans (hctx.runRecord a d hd')
  obtain ⟨ct', T, Bd, hct', -, hET, hpeel, hhd, hlen, hat⟩ :=
    modeledCtor_trees (c := ⟨E, Ix.Kernel.Env.empty, t, none⟩)
      (hctx.good Ix.Kernel.Env.empty none) (hrec _ _ hc) hmuts
      (hrec _ _ (hB.members 0 (.indc ind) rfl)) hmod hm0 0 (by omega)
  have e4 : ct' = ct := Option.some.inj (hct'.symm.trans hct)
  subst ct'
  rw [hf0, Nat.add_zero] at hpeel
  rw [hidx, Nat.add_zero] at hlen
  have hargs : ∀ X ∈ Bd.args, X = .atom := by
    intro X hX
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hX
    have hklt : k < Bd.args.length := (List.getElem?_eq_some_iff.mp hk).1
    rw [hat k (by omega)] at hk
    exact (Option.some.inj hk).symm
  have hans := ctorAnswer_spine_atoms (isInd := Route.isIndAt E) hET hpeel hhd hargs
  have hctl : ind.ctors.toList = [ct] := by
    obtain ⟨x, hx⟩ := Claim.array_of_size_one ind.ctors hsz
    rw [hx] at hct
    have e5 : x = ct := by simpa using hct
    simp [hx, e5]
  rw [blockRoute_one (hrec _ _ hc) hmuts hctl, hans] at hR
  exact Bool.false_ne_true (Option.some.inj hR)

/-- **The constructors' shapes at a block of one inductive at the family row**: the walk's check
of the member ran the modeled constructor loop (the route fact refutes the native branch), whose
return-type check gives each constructor's stored type, read as the dispatch reads it, a
telescope of its parameters and fields into a constant applied to `params + indices` arguments,
the first `params` of them atoms (`modeledCtor_trees`). -/
theorem famCtorTrees_of_run {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {E : Ixon.Env}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hTW : Claim.TopWalk calls t seeds E₀ lim Top rank)
    (hrun : FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner)
    (hctx : StepCtx.{u} calls t R envT E₀ E)
    {A rb : _root_.Address} {c : Ixon.Constant} (hTop : Top A) (hc : recordOf E₀ A = some c)
    (hlog : InLogic c) (hfam : fam A = some rb) :
    ∀ ind, c.info = .muts #[.indc ind] → ∀ j < ind.ctors.size,
      ∃ (ct : Ixon.Constructor) (T Bd : Route.ScanTree),
        ind.ctors[j]? = some ct ∧ ct.params.toNat = ind.params.toNat ∧
        Route.ExprTree c.refs.toList
          (L1.blockRecurAddrs A (#[.indc ind] : Array Ixon.MutConst).toList)
          c.sharing.toList 4294967295 ct.typ T ∧
        T.peel (ct.params.toNat + ct.fields.toNat) = some Bd ∧ (∃ a, Bd.head = .const a) ∧
        Bd.args.length = ct.params.toNat + ind.indices.toNat ∧
        ∀ k < ct.params.toNat, Bd.args[k]? = some .atom := by
  intro ind hmuts
  have hmod := famModeledAt_of_run hTW hrun hctx hTop hc hfam
  obtain ⟨ms, hB⟩ := famBlockRecord_of_run hTW hrun hTop hc hlog hfam
  have hms : ms = #[.indc ind] := Ixon.ConstantInfo.muts.inj (hB.muts.symm.trans hmuts)
  subst hms
  obtain ⟨bAddr, hW, -⟩ := hTW
  have hchk : (∃ ms, c.info = .muts ms ∧
        ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t A ms k lim) ∨
      Claim.CheckedLimAt calls bAddr t A lim := by
    obtain ⟨c', hc', h⟩ := hW.checked A hTop
    have e3 : c' = c := Option.some.inj (hc'.symm.trans hc)
    rw [e3] at h
    exact h
  have hm0 : Claim.MemberCheckedLimAt calls bAddr t A #[.indc ind] 0 lim :=
    Claim.membersChecked_of_block hW.runStore hc hmuts hchk 0 Nat.zero_lt_one
  have hdec : L1.EnvDecoded E := hctx.recordsFor.1
  have hrec : ∀ a d, recordOf E₀ a = some d → recordOf E a = some d := fun a d hd' =>
    (recordOf_eq_recordAt_of_decoded hdec a).trans (hctx.runRecord a d hd')
  exact modeledCtor_trees (c := ⟨E, Ix.Kernel.Env.empty, t, none⟩)
    (hctx.good Ix.Kernel.Env.empty none) (hrec _ _ hc) hmuts
    (hrec _ _ (hB.members 0 (.indc ind) rfl)) hmod hm0

/-- **The stored constant of a declared constructor is a constructor with its counts.** -/
theorem storedAs_ctor {ci : ConstantInfo .anon} {cv₀ : ConstantVal .anon} {nP nF : Nat}
    (h : StoredAs ci (.ctorInfo cv₀ nP nF)) : ∃ cv, ci = .ctorInfo cv nP nF := by
  obtain ⟨-, h2⟩ := h
  cases ci with
  | ctorInfo cv nP' nF' =>
    obtain ⟨e1, e2⟩ := h2
    exact ⟨cv, by rw [e1, e2]⟩
  | axiomInfo _ => exact False.elim h2
  | defnInfo _ _ _ => exact False.elim h2
  | thmInfo _ _ => exact False.elim h2
  | indInfo _ _ => exact False.elim h2
  | recInfo _ _ _ _ => exact False.elim h2
  | projInfo _ => exact False.elim h2

/-- **The stored constant of a declared inductive is an inductive with its name and level
parameters.** -/
theorem storedAs_ind {ci : ConstantInfo .anon} {cv₀ : ConstantVal .anon}
    {caps₀ : Ix.Kernel.IndCaps .anon} (h : StoredAs ci (.indInfo cv₀ caps₀)) :
    ∃ cv caps, ci = .indInfo cv caps ∧ cv.name = cv₀.name ∧ cv.levelParams = cv₀.levelParams := by
  obtain ⟨⟨hn, hl, -⟩, h2⟩ := h
  cases ci with
  | indInfo cv caps => exact ⟨cv, caps, rfl, hn, hl⟩
  | axiomInfo _ => exact False.elim h2
  | defnInfo _ _ _ => exact False.elim h2
  | thmInfo _ _ => exact False.elim h2
  | ctorInfo _ _ _ => exact False.elim h2
  | recInfo _ _ _ _ => exact False.elim h2
  | projInfo _ => exact False.elim h2

/-- **The stored constant of a declared constructor is a constructor with its name, level
parameters and counts.** -/
theorem storedAs_ctor_val {ci : ConstantInfo .anon} {cv₀ : ConstantVal .anon} {nP nF : Nat}
    (h : StoredAs ci (.ctorInfo cv₀ nP nF)) :
    ∃ cv, ci = .ctorInfo cv nP nF ∧ cv.name = cv₀.name ∧ cv.levelParams = cv₀.levelParams := by
  obtain ⟨⟨hn, hl, -⟩, h2⟩ := h
  cases ci with
  | ctorInfo cv nP' nF' =>
    obtain ⟨e1, e2⟩ := h2
    exact ⟨cv, by rw [e1, e2], hn, hl⟩
  | axiomInfo _ => exact False.elim h2
  | defnInfo _ _ _ => exact False.elim h2
  | thmInfo _ _ => exact False.elim h2
  | indInfo _ _ => exact False.elim h2
  | recInfo _ _ _ _ => exact False.elim h2
  | projInfo _ => exact False.elim h2

/-- A constant value with the given name and level parameters. -/
theorem constVal_eta {cv : ConstantVal .anon} {n : Ix.Kernel.Key .anon}
    {lps : List Ix.Kernel.LevelParam} (hn : cv.name = n) (hl : cv.levelParams = lps) :
    cv = ⟨n, lps, cv.type⟩ := by
  subst hn hl
  rfl

/-- **What the family step gives the load facts** (`FamLoadCtx`), at each environment the step's
record is taken at: the store's records at the two records' addresses (the run's, decoded), the
route fact, the new constants: the members at the keys of the two records' constant addresses
(`famStep_consts`, `FamDeclReads`), the aliases definitions at derived keys; the first
constructor of a block of one inductive stored with the record's counts (its reading and
`StoredAs`); `hfree`, a field in that constructor where the member has no index and one
constructor (`famUnitFree_of_run`); the dispatch's answer `1` at the store
(`famBlockRoute_of_run`); the constructors' shapes at a block of one inductive
(`famCtorTrees_of_run`); the registry's facts at the prefix (`PrefixInv.scopedCoreFacts`). -/
theorem famLoadCtx_of_step {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env} (hctx : StepCtx.{u} calls t R envT E₀ E)
    {A rb : _root_.Address} {c crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    (hB : FamBlockRecord E₀ A c ms) (hrb : FamRecRecord E₀ rb crb rs) (hroute : ModeledAt E A)
    (hfree : ∀ ind, c.info = .muts #[.indc ind] → ind.indices.toNat = 0 →
      ind.ctors.size = 1 → ∀ ct, ind.ctors[0]? = some ct → ct.fields.toNat ≠ 0)
    (hrouteT : Route.blockRoute E A = some true)
    (htrees : ∀ ind, c.info = .muts #[.indc ind] → ∀ j < ind.ctors.size,
      ∃ (ct : Ixon.Constructor) (T Bd : Route.ScanTree),
        ind.ctors[j]? = some ct ∧ ct.params.toNat = ind.params.toNat ∧
        Route.ExprTree c.refs.toList
          (L1.blockRecurAddrs A (#[.indc ind] : Array Ixon.MutConst).toList)
          c.sharing.toList 4294967295 ct.typ T ∧
        T.peel (ct.params.toNat + ct.fields.toNat) = some Bd ∧ (∃ a, Bd.head = .const a) ∧
        Bd.args.length = ct.params.toNat + ind.indices.toNat ∧
        ∀ k < ct.params.toNat, Bd.args[k]? = some .atom)
    {lim : Option Nat} {env : Ix.Kernel.Env .anon} {h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon}
    {aliases blk new : List (ConstantInfo .anon)} (hinv : Decl.PrefixInv.{u} E t lim env)
    (hg : AliasGroup env h aliases) (hreads : FamDeclReads t E₀ A c rb crb blk)
    (hd : DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk ⟨new ++ env.consts⟩)
    (hst : ∀ ci ∈ blk, ∃ c', (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? ci.name = some c' ∧
      StoredAs c' ci)
    (hcanon : FamilyMembersCanon t E₀ A c ms ⟨new ++ env.consts⟩) :
    FamLoadCtx ⟨E, env, t, lim⟩ new A c ms rb crb rs := by
  have hdec : L1.EnvDecoded E := hctx.recordsFor.1
  have hrec : ∀ a d, recordOf E₀ a = some d → recordOf E a = some d := fun a d hd' =>
    (recordOf_eq_recordAt_of_decoded hdec a).trans (hctx.runRecord a d hd')
  obtain ⟨new', henv, hnewN, -⟩ := famStep_consts hd
  have h2 : new ++ env.consts = (new' ++ aliases) ++ env.consts := congrArg Ix.Kernel.Env.consts henv
  have hnew : new = new' ++ aliases := List.append_cancel_right h2
  exact
    { wf := hinv.tableWf
      decoded := hdec
      held := hashedBlockProjectionsHeld_of_decoded hdec
      muts := hB.muts
      indcs := hB.indcs
      rmuts := hrb.muts
      recrs := hrb.recrs
      members := fun i m hm => hrec _ _ (hB.members i m hm)
      ctors := fun i ind j hm hj => hrec _ _ (hB.ctors i ind j hm hj)
      rmembers := fun i m hm => hrec _ _ (hrb.members i m hm)
      record := hrec _ _ hB.record
      route := hroute
      newName := by
        intro cn hcn
        rw [hnew] at hcn
        rcases List.mem_append.mp hcn with hm | hm
        · obtain ⟨ci, hci, hn⟩ := hnewN cn hm
          obtain ⟨x, hx, hk, -⟩ := hreads.2.1 ci hci
          exact Or.inl ⟨x, hx, hn.trans hk⟩
        · exact Or.inr ⟨(AliasGroup.defn_of_mem hg cn hm).1, AliasGroup.name_aux hg cn hm⟩
      found := by
        intro x hx
        obtain ⟨ci, hci, hk⟩ := hreads.2.2.1 x hx
        obtain ⟨c', hc', -⟩ := hst ci hci
        rw [hk] at hc'
        exact ⟨c', hc'⟩
      unitFree := fun ind hms => hfree ind (hB.muts.trans (by rw [hms]))
      ctorCounts := by
        intro ind ct hms hct ci hci
        have hpos : 0 < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hct).1
        have hget0 : ms[0]? = some (.indc ind) := by
          subst hms
          rfl
        have hx : FamAddr A c rb crb (Core.cprjAddr A 0 0) :=
          Or.inl (Or.inr ⟨ms, 0, .indc ind, hB.muts, hget0, Or.inr ⟨ind, 0, rfl, hpos, rfl⟩⟩)
        obtain ⟨ci₀, hci₀, hk⟩ := hreads.2.2.1 _ hx
        obtain ⟨y, -, hy, hry⟩ := hreads.2.1 ci₀ hci₀
        have hyx : y = Core.cprjAddr A 0 0 := Core.keyOf_inj hinv.tableWf (hy.symm.trans hk)
        rw [hyx] at hry
        obtain ⟨c', hc', hR⟩ := hry
        have e : c' = constructorProjection A 0 0 :=
          Option.some.inj (hc'.symm.trans (hB.ctors 0 ind 0 hget0 hpos))
        subst e
        have hinfo : (constructorProjection A 0 0).info =
            .cPrj ⟨(0 : Nat).toUInt64, (0 : Nat).toUInt64, A⟩ := rfl
        rw [hinfo] at hR
        obtain ⟨cb', ms', ind', ct', hcb', hms', hind', hct', -, -, -, -, ty, -, hci₀eq⟩ := hR
        have e1 : cb' = c := Option.some.inj (hcb'.symm.trans hB.record)
        subst cb'
        have e2 : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hB.muts)
        subst ms'
        have e3 : ind' = ind := by
          have e : ms[((0 : Nat).toUInt64).toNat]? = some (.indc ind) := hget0
          exact Ixon.MutConst.indc.inj (Option.some.inj (hind'.symm.trans e))
        subst ind'
        have e4 : ct' = ct := by
          have e : ind.ctors[((0 : Nat).toUInt64).toNat]? = some ct := hct
          exact Option.some.inj (hct'.symm.trans e)
        subst ct'
        obtain ⟨c'', hf'', hsa⟩ := hst ci₀ hci₀
        rw [hk] at hf''
        have e5 : c'' = ci := Option.some.inj (hf''.symm.trans hci)
        subst c''
        rw [hci₀eq] at hsa
        exact storedAs_ctor hsa
      routeTrue := hrouteT
      ctorTrees := fun ind hms => htrees ind (hB.muts.trans (by rw [hms]))
      core := hinv.scopedCoreFacts
      check := Core.RoleClosure.check_ok_of_wf hinv.tableWf
      used := hcanon.used
      indForm := by
        intro i ind hi hm
        have hx : FamAddr A c rb crb (Core.iprjAddr A i) :=
          Or.inl (Or.inr ⟨ms, i, .indc ind, hB.muts, hm, Or.inl rfl⟩)
        obtain ⟨ci₀, hci₀, hk⟩ := hreads.2.2.1 _ hx
        obtain ⟨y, -, hy, hry⟩ := hreads.2.1 ci₀ hci₀
        have hyx : y = Core.iprjAddr A i := Core.keyOf_inj hinv.tableWf (hy.symm.trans hk)
        rw [hyx] at hry
        obtain ⟨c', hc', hR⟩ := hry
        have e : c' = memberProjection A i (.indc ind) :=
          Option.some.inj (hc'.symm.trans (hB.members i (.indc ind) hm))
        subst e
        have hinfo : (memberProjection A i (.indc ind)).info = .iPrj ⟨i.toUInt64, A⟩ := rfl
        rw [hinfo] at hR
        obtain ⟨cb', ms', ind', ⟨hcb', hms', hind', -, -, -⟩, ty₀, caps₀, hty, hci₀eq⟩ := hR
        have e1 : cb' = c := Option.some.inj (hcb'.symm.trans hB.record)
        subst e1
        have e2 : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hB.muts)
        subst e2
        have hm' : ms'[(i.toUInt64).toNat]? = some (.indc ind) := by
          rw [toNat_toUInt64_of_lt hi]
          exact hm
        have e3 : ind' = ind := Ixon.MutConst.indc.inj (Option.some.inj (hind'.symm.trans hm'))
        subst e3
        obtain ⟨c'', hf'', hsa⟩ := hst ci₀ hci₀
        rw [hk] at hf''
        rw [hci₀eq] at hsa
        obtain ⟨cv, caps, hcv, hn, hl⟩ := storedAs_ind hsa
        subst hcv
        obtain ⟨hlbb, hdef, hcan⟩ := hcanon.ind i ind' ty₀ cv caps hi hm hty hf''
        have hn' : cv.name = Core.keyOf t (Core.iprjAddr A i) := hn
        have hl' : cv.levelParams = List.range ind'.lvls.toNat := hl
        have ecv : (ConstantInfo.indInfo cv caps) =
            .indInfo ⟨Core.keyOf t (Core.iprjAddr A i), List.range ind'.lvls.toNat, cv.type⟩ caps := by
          rw [← constVal_eta hn' hl']
        exact ⟨ty₀, cv.type, caps,
          ReaderReads.exprReader_mono (blob := fun y => E₀.blobs.get? y)
            (blob' := fun y => E.blobs.get? y) hctx.runBlob hty,
          hlbb, hdef, hcan, hf''.trans (congrArg some ecv)⟩
      ctorForm := by
        intro i ind j ct hi hj hm hct
        have hjlt : j < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hct).1
        have hx : FamAddr A c rb crb (Core.cprjAddr A i j) :=
          Or.inl (Or.inr ⟨ms, i, .indc ind, hB.muts, hm, Or.inr ⟨ind, j, rfl, hjlt, rfl⟩⟩)
        obtain ⟨ci₀, hci₀, hk⟩ := hreads.2.2.1 _ hx
        obtain ⟨y, -, hy, hry⟩ := hreads.2.1 ci₀ hci₀
        have hyx : y = Core.cprjAddr A i j := Core.keyOf_inj hinv.tableWf (hy.symm.trans hk)
        rw [hyx] at hry
        obtain ⟨c', hc', hR⟩ := hry
        have e : c' = constructorProjection A i j :=
          Option.some.inj (hc'.symm.trans (hB.ctors i ind j hm hjlt))
        subst e
        have hinfo : (constructorProjection A i j).info =
            .cPrj ⟨i.toUInt64, j.toUInt64, A⟩ := rfl
        rw [hinfo] at hR
        obtain ⟨cb', ms', ind', ct', hcb', hms', hind', hct', hcidx, -, -, -, ty₀, hty, hci₀eq⟩ := hR
        have e1 : cb' = c := Option.some.inj (hcb'.symm.trans hB.record)
        subst e1
        have e2 : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hB.muts)
        subst e2
        have hm' : ms'[(i.toUInt64).toNat]? = some (.indc ind) := by
          rw [toNat_toUInt64_of_lt hi]
          exact hm
        have e3 : ind' = ind := Ixon.MutConst.indc.inj (Option.some.inj (hind'.symm.trans hm'))
        subst e3
        have hct2 : ind'.ctors[(j.toUInt64).toNat]? = some ct := by
          rw [toNat_toUInt64_of_lt hj]
          exact hct
        have e4 : ct' = ct := Option.some.inj (hct'.symm.trans hct2)
        subst e4
        have hcj : ct'.cidx.toNat = j := hcidx.trans (toNat_toUInt64_of_lt hj)
        obtain ⟨c'', hf'', hsa⟩ := hst ci₀ hci₀
        rw [hk] at hf''
        rw [hci₀eq] at hsa
        obtain ⟨cv, hcv, hn, hl⟩ := storedAs_ctor_val hsa
        subst hcv
        obtain ⟨hlbb, hdef, hcan⟩ := hcanon.ctor i ind' j ct' ty₀ cv _ _ hi hj hm hct hty hf''
        have hn' : cv.name = Core.keyOf t (Core.cprjAddr A i j) := hn
        have hl' : cv.levelParams = List.range ct'.lvls.toNat := hl
        have ecv : (ConstantInfo.ctorInfo cv ct'.params.toNat ct'.fields.toNat) =
            .ctorInfo ⟨Core.keyOf t (Core.cprjAddr A i j), List.range ct'.lvls.toNat, cv.type⟩
              ct'.params.toNat ct'.fields.toNat := by
          rw [← constVal_eta hn' hl']
        exact ⟨hcj, ty₀, cv.type,
          ReaderReads.exprReader_mono (blob := fun y => E₀.blobs.get? y)
            (blob' := fun y => E.blobs.get? y) hctx.runBlob hty,
          hlbb, hdef, hcan, hf''.trans (congrArg some ecv)⟩ }

/-- **What the circuit side's family check hands the step of the block at `A` with its family
record at `rb`**: the seam, the companion facts of each recursor the step stores, and the load
facts that reach its new constants (the fields of `FamilyBlockCircuit` that read the family
check). -/
structure FamilyBlockCheck (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (t : Ix.Kernel.RoleTable) (envT : Ix.Kernel.Env .anon) (E₀ E : Ixon.Env) (lim : Option Nat)
    (A : _root_.Address) (c : Ixon.Constant) (rb : _root_.Address) (crb : Ixon.Constant)
    (adv : _root_.Address → Prop) (fam : _root_.Address → Option _root_.Address) : Prop where
  /-- The seam: the family as read and the facts of its check, at each environment the step is
  handed. -/
  seam : ∀ env : Ix.Kernel.Env .anon,
    (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
    Decl.PrefixInv.{u} E t lim env →
    (FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env) →
    (∀ x, UsedRef E₀ A x ∨ UsedRef E₀ rb x →
      (env.find? (keyOf t x)).isSome = true ∨ FamAddr A c rb crb x ∨ ¬ NeedOk E₀ x) →
    (∀ a, adv a → ∀ ca, recordOf E₀ a = some ca → ∀ x, ConstAddrOf a ca x →
      (env.find? (keyOf t x)).isSome = true) →
    (∀ a, adv a → ∀ x, UsedRef E₀ a x →
      (env.find? (keyOf t x)).isSome = true ∨ FamAddr A c rb crb x ∨ ¬ NeedOk E₀ x) →
    (∀ x, FamAddr A c rb crb x → env.find? (keyOf t x) = none) →
    ∃ (blk : List (ConstantInfo .anon)) (adv' : FamilyAdvice)
      (tys : List IxVM.Refinement.Core.KExpr)
      (rhsss : List (List IxVM.Refinement.Core.KExpr)),
      FamDeclReads t E₀ A c rb crb blk ∧ FamilyCheckFacts env blk adv' tys rhsss
  /-- The companion facts of each recursor the step stores. -/
  recs : ∀ (env : Ix.Kernel.Env .anon) (h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon)
    (aliases blk new : List (ConstantInfo .anon)),
    Decl.PrefixInv.{u} E t lim env → AliasGroup env h aliases →
    FamDeclReads t E₀ A c rb crb blk →
    DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk ⟨new ++ env.consts⟩ →
    (∀ ci ∈ blk, ∃ c', (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? ci.name = some c' ∧
      StoredAs c' ci) →
    ∀ cv mI rP rls, ConstantInfo.recInfo cv mI rP rls ∈ new →
      RecCompanionFacts ⟨E, ⟨new ++ env.consts⟩, t, lim⟩ cv mI rP rls
  /-- The seam of the loads: the circuit loads each new inductive and constructor in its
  canonical annotated form. -/
  canon : ∀ (env : Ix.Kernel.Env .anon) (h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon)
    (aliases blk new : List (ConstantInfo .anon)),
    Decl.PrefixInv.{u} E t lim env → AliasGroup env h aliases →
    FamDeclReads t E₀ A c rb crb blk →
    DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk ⟨new ++ env.consts⟩ →
    (∀ ci ∈ blk, ∃ c', (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? ci.name = some c' ∧
      StoredAs c' ci) →
    ∀ ms, c.info = .muts ms → FamilyMembersCanon t E₀ A c ms ⟨new ++ env.consts⟩
  /-- The load facts at the step's new constants that read the family check. -/
  loads : ∀ (env : Ix.Kernel.Env .anon) (h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon)
    (aliases blk new : List (ConstantInfo .anon)),
    Decl.PrefixInv.{u} E t lim env → AliasGroup env h aliases →
    FamDeclReads t E₀ A c rb crb blk →
    DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk ⟨new ++ env.consts⟩ →
    (∀ ci ∈ blk, ∃ c', (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? ci.name = some c' ∧
      StoredAs c' ci) →
    FamilyLoadsCheck (appCtx ⟨E, env, t, lim⟩ new).stored new

/-- **The facts of the family check at every block with a family record**, at the hypotheses of
the row `familyBlock`. -/
def FamilyBlockCheckRow (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) : Prop :=
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
        FamilyBlockCheck.{u} L t envT E₀ E lim A c rb crb (adv A) fam

/-- **The circuit side's facts at the family row from those of the family check**: the block's
record and the route fact are proved at the row. -/
theorem familyBlockCircuitRow_of_check {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hchk : FamilyBlockCheckRow.{u} L) : FamilyBlockCircuitRow.{u} L := by
  intro calls t seeds E₀ lim Top rank hTW R envT E fam twin adv Inner hrun hctx A c rb crb rs
    hTop hc hlog hkind hfam hrb
  have hK := hchk calls t seeds E₀ lim Top rank hTW R envT E fam twin adv Inner hrun hctx A c rb
    crb rs hTop hc hlog hkind hfam hrb
  obtain ⟨ms, hB⟩ := famBlockRecord_of_run hTW hrun hTop hc hlog hfam
  have hroute : ModeledAt E A := famModeledAt_of_run hTW hrun hctx hTop hc hfam
  have hfree := famUnitFree_of_run hTW hrun hctx hTop hc hlog hfam
  have hrouteT := famBlockRoute_of_run hTW hrun hctx hTop hc hfam
  have htrees := famCtorTrees_of_run hTW hrun hctx hTop hc hlog hfam
  exact
    { seam := hK.seam
      block := ⟨ms, hB⟩
      route := hroute
      recs := hK.recs
      loads := fun env h aliases blk new hinv hg hreads hd hst =>
        (famLoadCtx_of_step hctx hB hrb hroute hfree hrouteT htrees hinv hg hreads hd hst
          (hK.canon env h aliases blk new hinv hg hreads hd hst ms hB.muts)).newLoads
          (hK.loads env h aliases blk new hinv hg hreads hd hst) }

/-- **The row `familyBlock` from the facts of the family check** (module docstring). -/
theorem familyBlockRow_of_check {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) (hchk : FamilyBlockCheckRow.{u} L) : FamilyBlockRow.{u} L :=
  familyBlockRow_of_circuit hL (familyBlockCircuitRow_of_check hchk) familyClaimRow

end IxVM.Refinement.Typing.FamilyAlias
