import IxVMRefinement.FamilyGraph.Composition
import IxVMRefinement.FamilyGraph.ProducersRank

/-! # The graph row's producer: the run's family records, twins, advice and inner records

`FamilyGraphRow` asks, at a walk and a witness, a rank of the walk and the run's family records,
twins, advice and inner records with `FamilyRun`. This module makes the choices and assembles
`FamilyRun` from what the circuit's functions give:

* `FamRunCtx`: the run the choices are made for (the walk's calls, binding, table, store, limit
  and top-walked set, the witness's environment) and `Pref`, the form rule (c) prefers for a
  block's family record (the reconstruction's);
* `FamRunCtx.fam`: a top-walked non-empty block of inductive types routed as modeled, with a
  constant address the witness's environment does not store, installs the record of one of its
  family checks at the walk's binding and limit, one in the preferred form where there is one;
* `FamRunCtx.twin`: a top-walked non-empty block of recursors with such an address that no block
  claims is a twin of a top-walked modeled block of inductive types it is the record of a family
  check of;
* `FamRunCtx.adv`: an advice record with a constant address among the calls of the installed
  family check; `FamRunCtx.Inner`: a record with a constant address that the walk did not reach,
  checked as advice (no projection record) or as a container's recursor by the family check of a
  family record or of a twin;
* `BatchGives`: what the functions the circuit batch changes must give, one field per function;
* `NoBatchFields`: the facts read off functions the batch does not change, not yet proved here;
* `FamilyRanking`: the rank (a topological re-ranking of the walk's order with advice before its
  block and a block before its family record or twin), not yet proved here;
* `familyRun_of`: `FamilyRun` at the choices, and rule (c)'s fact: a block that has a twin has its
  family record in the preferred form;
* `familyGraphRow_of_parts`: the row. -/

universe u

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open TwinFamily (FamilyInstalled)
open FamilyAlias (FamilyCallAtLim)

set_option linter.unusedVariables false

/-! ## Kinds of blocks -/

/-- **A non-empty block of inductive types.** -/
def IndBlock (E₀ : Ixon.Env) (B : _root_.Address) : Prop :=
  ∃ cb ms, recordOf E₀ B = some cb ∧ cb.info = .muts ms ∧ 0 < ms.size ∧
    ∀ m ∈ ms.toList, ∃ ind, m = Ixon.MutConst.indc ind

/-- **A non-empty block of recursors.** -/
def RecBlock (E₀ : Ixon.Env) (A : _root_.Address) : Prop :=
  ∃ c rs, recordOf E₀ A = some c ∧ c.info = .muts rs ∧ 0 < rs.size ∧
    ∀ m ∈ rs.toList, ∃ r, m = Ixon.MutConst.recr r

theorem muts_indc_recr_absurd {ms : Array Ixon.MutConst} (hpos : 0 < ms.size)
    (hi : ∀ m ∈ ms.toList, ∃ ind, m = Ixon.MutConst.indc ind)
    (hr : ∀ m ∈ ms.toList, ∃ r, m = Ixon.MutConst.recr r) : False := by
  have h0 : ms[0]? = some ms[0] := Array.getElem?_eq_getElem hpos
  have h0' : ms.toList[0]? = some ms[0] := by simpa only [Array.getElem?_toList] using h0
  have hmem : ms[0] ∈ ms.toList := List.mem_of_getElem? h0'
  obtain ⟨ind, e1⟩ := hi _ hmem
  obtain ⟨r, e2⟩ := hr _ hmem
  rw [e1] at e2
  cases e2

/-- A non-empty block of recursors is no block of inductive types. -/
theorem RecBlock.not_indBlock {E₀ : Ixon.Env} {A : _root_.Address} (hr : RecBlock E₀ A) :
    ¬ IndBlock E₀ A := by
  rintro ⟨cb, ms, hcb, hms, hpos, hall⟩
  obtain ⟨c, rs, hc, hrs, -, hallr⟩ := hr
  have e : c = cb := Option.some.inj (hc.symm.trans hcb)
  subst e
  have e' : rs = ms := Ixon.ConstantInfo.muts.inj (hrs.symm.trans hms)
  subst e'
  exact muts_indc_recr_absurd hpos hall hallr

/-- A family record is no non-empty block of inductive types. -/
theorem FamRecRecord.not_indBlock {E₀ : Ixon.Env} {rb : _root_.Address} {crb : Ixon.Constant}
    {rs : Array Ixon.MutConst} (h : FamRecRecord E₀ rb crb rs) : ¬ IndBlock E₀ rb := by
  rintro ⟨cb, ms, hcb, hms, hpos, hall⟩
  have e : crb = cb := Option.some.inj (h.record.symm.trans hcb)
  subst e
  have e' : rs = ms := Ixon.ConstantInfo.muts.inj (h.muts.symm.trans hms)
  subst e'
  exact muts_indc_recr_absurd hpos hall h.recrs

/-- A block with a constant address is non-empty. -/
theorem constAddr_muts_pos {A x : _root_.Address} {c : Ixon.Constant}
    {ms : Array Ixon.MutConst} (hinfo : c.info = .muts ms) (hx : ConstAddrOf A c x) :
    0 < ms.size := by
  rcases hx with ⟨-, hs⟩ | ⟨ms', i, m, hms', hm, -⟩
  · exact (standalone_not_block hs ⟨ms, hinfo⟩).elim
  · rw [hinfo] at hms'
    have e : ms = ms' := Ixon.ConstantInfo.muts.inj hms'
    rw [← e] at hm
    have hm' : ms.toList[i]? = some m := by simpa only [Array.getElem?_toList] using hm
    have hpos := List.length_pos_of_mem (List.mem_of_getElem? hm')
    simpa using hpos

/-! ## The choices -/

/-- **The run the family graph is chosen for**: the walk's calls, binding, table, store, limit
and top-walked set, the witness's environment, and the form rule (c) prefers for a block's
family record. -/
structure FamRunCtx where
  calls : List (Call F)
  bAddr : _root_.Address
  t : Ix.Kernel.RoleTable
  E₀ : Ixon.Env
  lim : Option Nat
  Top : _root_.Address → Prop
  envT : Ix.Kernel.Env .anon
  /-- The family record at `rb` of the block at `B` is in the preferred form. -/
  Pref : _root_.Address → _root_.Address → Prop

namespace FamRunCtx

variable (K : FamRunCtx)

/-- **A family check of the block at `B` with the family record at `rb`**, at the walk's binding
and limit. -/
def FamCheck (B rb : _root_.Address) : Prop :=
  ∃ cs, FamilyCallAtLim K.calls K.bAddr K.t B rb K.lim cs

/-- The record has a constant address the witness's environment does not store. -/
def Unstored (A : _root_.Address) : Prop :=
  ∃ c x, recordOf K.E₀ A = some c ∧ ConstAddrOf A c x ∧ ¬ StoredAt K.t K.envT x

/-- **A block the fold steps with a family record**: top-walked, in Lean's logic, a non-empty
block of inductive types routed as modeled, with a constant address the witness's environment
does not store. -/
def FamBlock (B : _root_.Address) : Prop :=
  K.Top B ∧ ModeledRouteAt K.calls B ∧ IndBlock K.E₀ B ∧ K.Unstored B ∧
    ∀ cb, recordOf K.E₀ B = some cb → InLogic cb

open Classical in
/-- **The family record a block installs**: the record of a family check of the block, one in
the preferred form where there is one. -/
noncomputable def fam (B : _root_.Address) : Option _root_.Address :=
  if h : K.FamBlock B ∧ ∃ rb, K.FamCheck B rb then
    if hp : ∃ rb, K.FamCheck B rb ∧ K.Pref B rb then some (Classical.choose hp)
    else some (Classical.choose h.2)
  else none

/-- **`rb'` is a twin of the block at `B`**: a top-walked non-empty block of recursors with a
constant address the witness's environment does not store, that no block claims, the record of a
family check of the top-walked non-empty block of inductive types `B` routed as modeled. -/
def TwinOf (rb' B : _root_.Address) : Prop :=
  K.Top rb' ∧ RecBlock K.E₀ rb' ∧ K.Unstored rb' ∧ Unclaimed K.fam rb' ∧ K.FamCheck B rb' ∧
    K.Top B ∧ ModeledRouteAt K.calls B ∧ IndBlock K.E₀ B

open Classical in
/-- **The block a twin is a second family record of.** -/
noncomputable def twin (rb' : _root_.Address) : Option _root_.Address :=
  if h : ∃ B, K.TwinOf rb' B then some (Classical.choose h) else none

open Classical in
/-- **The calls of one family check of the block at `B` with the record at `rb`.** -/
noncomputable def famCalls (B rb : _root_.Address) : List (Call F) :=
  if h : K.FamCheck B rb then Classical.choose h else []

/-- **The advice of a block**: an advice record with a constant address among the calls of the
family check of the record the block installs. -/
def adv (B a : _root_.Address) : Prop :=
  ∃ rb, K.fam B = some rb ∧ AdviceIn (K.famCalls B rb) a ∧
    ∃ ca x, recordOf K.E₀ a = some ca ∧ ConstAddrOf a ca x

/-- **The inner records**: a record with a constant address that the walk did not reach,
checked at the walk's binding and limit, by the family check of a family record or of a twin, as
advice that is no projection record or as a container's recursor. -/
def Inner (a : _root_.Address) : Prop :=
  ¬ K.Top a ∧ (∃ ca x, recordOf K.E₀ a = some ca ∧ ConstAddrOf a ca x) ∧
    ∃ B rb, (K.fam B = some rb ∨ K.twin rb = some B) ∧
      ((AdviceCheckIn (K.famCalls B rb) K.bAddr K.t K.lim a ∧
          ∀ c, recordOf K.E₀ a = some c → ¬ IsProj c) ∨
        ContainerRecCheckIn (K.famCalls B rb) K.bAddr K.t K.lim a)

variable {K}

theorem famCalls_spec {B rb : _root_.Address} (h : K.FamCheck B rb) :
    FamilyCallAtLim K.calls K.bAddr K.t B rb K.lim (K.famCalls B rb) := by
  unfold famCalls
  rw [dite_eq_left h]
  exact Classical.choose_spec h

theorem fam_some {B rb : _root_.Address} (h : K.fam B = some rb) :
    K.FamBlock B ∧ K.FamCheck B rb ∧
      ((∃ rb', K.FamCheck B rb' ∧ K.Pref B rb') → K.Pref B rb) := by
  unfold fam at h
  by_cases hc : K.FamBlock B ∧ ∃ rb, K.FamCheck B rb
  · rw [dite_eq_left hc] at h
    by_cases hp : ∃ rb, K.FamCheck B rb ∧ K.Pref B rb
    · rw [dite_eq_left hp] at h
      have e := Option.some.inj h
      subst e
      exact ⟨hc.1, (Classical.choose_spec hp).1, fun _ => (Classical.choose_spec hp).2⟩
    · rw [dite_eq_right hp] at h
      have e := Option.some.inj h
      subst e
      exact ⟨hc.1, Classical.choose_spec hc.2, fun h' => absurd h' hp⟩
  · rw [dite_eq_right hc] at h
    cases h

theorem fam_of {B rb : _root_.Address} (hB : K.FamBlock B) (hc : K.FamCheck B rb) :
    ∃ rb', K.fam B = some rb' := by
  have hc' : K.FamBlock B ∧ ∃ rb, K.FamCheck B rb := ⟨hB, rb, hc⟩
  unfold fam
  rw [dite_eq_left hc']
  by_cases hp : ∃ rb, K.FamCheck B rb ∧ K.Pref B rb
  · rw [dite_eq_left hp]
    exact ⟨_, rfl⟩
  · rw [dite_eq_right hp]
    exact ⟨_, rfl⟩

theorem twin_some {rb' B : _root_.Address} (h : K.twin rb' = some B) : K.TwinOf rb' B := by
  unfold twin at h
  by_cases hc : ∃ B, K.TwinOf rb' B
  · rw [dite_eq_left hc] at h
    have e := Option.some.inj h
    subst e
    exact Classical.choose_spec hc
  · rw [dite_eq_right hc] at h
    cases h

theorem twin_of {rb' B : _root_.Address} (h : K.TwinOf rb' B) : ∃ B', K.twin rb' = some B' := by
  have hc : ∃ B, K.TwinOf rb' B := ⟨B, h⟩
  unfold twin
  rw [dite_eq_left hc]
  exact ⟨_, rfl⟩

theorem famCheck_of_inner {B rb : _root_.Address} (h : K.fam B = some rb ∨ K.twin rb = some B) :
    K.FamCheck B rb := by
  rcases h with h | h
  · exact (fam_some h).2.1
  · obtain ⟨-, -, -, -, hc, -⟩ := twin_some h
    exact hc

end FamRunCtx

/-! ## What the run's functions give -/

/-- **What the functions the circuit batch changes must give**, at the choices (premises; each
field names its function). -/
structure BatchGives (K : FamRunCtx) : Prop where
  /-- `check_const`, its `Rec` arm (the batch removes the refusal of a modeled recursor, so the
  arm runs `check_family` on the recursor's family block): a top-walked non-empty block of
  recursors is the record of a family check of a top-walked non-empty block of inductive types
  routed as modeled. -/
  recArm : ∀ A, K.Top A → RecBlock K.E₀ A →
    ∃ B, K.FamCheck B A ∧ K.Top B ∧ ModeledRouteAt K.calls B ∧ IndBlock K.E₀ B
  /-- `canonical_rules_at_pos`, syntactic after the batch: a family record's recursor types are
  the reconstruction over its block's types, so a record with a constant address is the family
  record of one block. -/
  blockOf : ∀ B B' rb crb x, K.FamCheck B rb → K.FamCheck B' rb → recordOf K.E₀ rb = some crb →
    ConstAddrOf rb crb x → B = B'
  /-- `canonical_rules_at_pos`, rule (c): of two family records of one block, the second
  top-walked, one is in the preferred form. Under review: the prototype's comparison chooses
  per recursor, so two records may mix the forms; the statement waits for that ruling. -/
  form : ∀ B rb rb', K.FamCheck B rb → K.FamCheck B rb' → rb ≠ rb' → K.Top rb' →
    RecBlock K.E₀ rb' → K.Pref B rb ∨ K.Pref B rb'
  /-- `check_family` with the batch's `assert_no_role` (no role bound at a family recursor) and
  `canonical_rules_at_pos` naming every type and constructor of the block, with the witness's
  store closed under used references: the witness's environment stores no constant address of
  the family record of a block it does not store whole. -/
  fresh : ∀ B rb crb x, K.FamCheck B rb → K.FamBlock B → recordOf K.E₀ rb = some crb →
    ConstAddrOf rb crb x → ¬ StoredAt K.t K.envT x

/-- **The facts read off functions the batch does not change**, at the choices (not yet proved
here; each field names its source). -/
structure NoBatchFields (K : FamRunCtx) : Prop where
  /-- `check_const`'s `Induct` arms, `check_modeled_block`: a block the fold steps with a family
  record had a family check at the walk's binding and limit. -/
  modeledCall : ∀ B, K.FamBlock B → ∃ rb, K.FamCheck B rb
  /-- The unfolding of `check_family` (regenerated by the batch) to `family_recs` and
  `check_recs` (unchanged): a family check's record is a block of recursors in Lean's logic
  with its member projections stored. -/
  record : ∀ B rb, K.FamCheck B rb → ∃ crb rs, FamRecRecord K.E₀ rb crb rs
  /-- `check_advice_record`'s projection arms: an advice record without a constant address uses
  nothing a step has to find (a projection of an earlier advice block uses that block). -/
  adviceNoAddr : ∀ B rb a, K.fam B = some rb → AdviceIn (K.famCalls B rb) a →
    (∀ ca x, recordOf K.E₀ a = some ca → ¬ ConstAddrOf a ca x) →
    ∀ x, UsedRef K.E₀ a x → ¬ NeedOk K.E₀ x
  /-- `check_advice_records`, `check_advice_record`'s arms: an advice record with a constant
  address was checked at the walk's binding and limit (so it is top-walked or inner), is no
  family record, and is in Lean's logic. -/
  adviceChecked : ∀ B a, K.adv B a →
    (K.Top a ∨ K.Inner a) ∧ Unclaimed K.fam a ∧ ∀ ca, recordOf K.E₀ a = some ca → InLogic ca
  /-- `check_muts_all` (an advice block's members): their projection records are stored. -/
  innerMembers : ∀ B c ms, K.Inner B → recordOf K.E₀ B = some c → c.info = .muts ms →
    ∀ i m, ms[i]? = some m →
      recordOf K.E₀ (memberAddr B i m) = some (memberProjection B i m) ∧
      ∀ ind j, m = .indc ind → j < ind.ctors.size →
        recordOf K.E₀ (ctorAddr B i j) = some (constructorProjection B i j)
  /-- `check_advice_record` has no axiom or quotient arm; a container's recursor has a
  recursor's reading (`rec_family_block`). -/
  innerKind : ∀ a c, K.Inner a → recordOf K.E₀ a = some c →
    (∀ ax, c.info ≠ .axio ax) ∧ ∀ q, c.info ≠ .quot q

/-- **The rank of the family graph** at a rank `rank'`: the walk's edges kept (a used reference
of a top-walked record is top-walked below it or covered; a projection record's block is below
it), a family record the run checked after its block, advice before its block, a twin after its
block, and what a family record and an inner record use stored, covered, their own, or owned
below them (the latter two from the batch's `family_refs_go`, `assert_inner_refs_safe`,
`check_advice_record` and `container_refs_ok`, with item 11, a projection reference names a
member of its block, through the ranking). Only the walk's edges are kept, not every comparison
of the walk's rank: two top-walked records without an edge may change order. -/
structure FamilyRanked (K : FamRunCtx) (rank' : _root_.Address → Nat) : Prop where
  closed : ∀ a x, K.Top a → UsedRef K.E₀ a x → (K.Top x ∧ rank' x < rank' a) ∨ Covered K.t x
  owner : ∀ a c, K.Top a → recordOf K.E₀ a = some c → IsProj c →
    K.Top (Ix.Cert.ownerOf a c) ∧ rank' (Ix.Cert.ownerOf a c) < rank' a
  after : ∀ B rb, K.fam B = some rb → Walked K.Top K.Inner rb → rank' B < rank' rb
  advBelow : ∀ B a, K.adv B a → rank' a < rank' B
  twinAfter : ∀ rb' B rb, K.twin rb' = some B → K.fam B = some rb → rank' B < rank' rb'
  famClosed : ∀ B rb x, K.fam B = some rb → UsedRef K.E₀ rb x → NeedOk K.E₀ x →
    StoredAt K.t K.envT x ∨ Covered K.t x ∨
      (∃ cb, recordOf K.E₀ B = some cb ∧ ConstAddrOf B cb x) ∨
      (∃ crb, recordOf K.E₀ rb = some crb ∧ ConstAddrOf rb crb x) ∨
      OwnedBelow K.E₀ K.Top K.Inner rank' K.fam (rank' B) x
  innerClosed : ∀ a x, K.Inner a → UsedRef K.E₀ a x → NeedOk K.E₀ x →
    StoredAt K.t K.envT x ∨ Covered K.t x ∨
      (∃ c, recordOf K.E₀ a = some c ∧ ConstAddrOf a c x) ∨
      OwnedBelow K.E₀ K.Top K.Inner rank' K.fam (rank' a) x

/-- **The family graph's stored twins** (the field `FamilyRun.storedTwin` at the choices; to be
restated against the stored family the binding fold exposes). -/
def StoredTwinField (K : FamRunCtx) : Prop :=
  ∀ rb' B, K.twin rb' = some B → K.fam B = none →
    ∃ rb crb, (∀ x, ConstAddrOf rb crb x → StoredAt K.t K.envT x) ∧
      FamilyInstalled K.t K.envT rb crb

/-! ## The family run at the choices -/

/-- **`FamilyRun` at the choices**, and rule (c)'s fact: a block that has a twin has its family
record in the preferred form. -/
theorem familyRun_of (K : FamRunCtx) {rank' : _root_.Address → Nat}
    (hB : BatchGives K) (hO : NoBatchFields K) (hR : FamilyRanked K rank')
    (hST : StoredTwinField K) :
    FamilyRun K.calls K.t K.envT K.E₀ K.lim K.Top rank' K.fam K.twin K.adv K.Inner ∧
      ∀ B rb rb', K.fam B = some rb → K.twin rb' = some B → K.Pref B rb := by
  refine ⟨{ graph := ?graph, claimed := ?claimed, modeled := ?modeled,
            famInductive := ?famInductive,
            checks := ⟨K.bAddr, { famCall := ?famCall, twinCall := ?twinCall,
              innerCall := ?innerCall }⟩,
            storedTwin := hST }, ?form⟩
  case graph =>
    exact
    { famBlock := fun B rb h => (FamRunCtx.fam_some h).1.1
      famUnit := fun B rb h => by
        obtain ⟨⟨hT, -, hIB, ⟨c, x, hc, hx, hns⟩, hlogic⟩, -, -⟩ := FamRunCtx.fam_some h
        refine ⟨fun B' hB' => ?_, c, hc, hlogic c hc, x, hx, hns⟩
        obtain ⟨crb, rs, hF⟩ := hO.record B' B (FamRunCtx.fam_some hB').2.1
        exact hF.not_indBlock hIB
      famRecord := fun B rb h => hO.record B rb (FamRunCtx.fam_some h).2.1
      famAfter := hR.after
      famInj := fun B B' rb x crb h h' hcrb hx =>
        hB.blockOf B B' rb crb x (FamRunCtx.fam_some h).2.1 (FamRunCtx.fam_some h').2.1 hcrb hx
      famFresh := fun B rb crb x h hcrb hx =>
        hB.fresh B rb crb x (FamRunCtx.fam_some h).2.1 (FamRunCtx.fam_some h).1 hcrb hx
      famClosed := hR.famClosed
      advEarlier := fun B a h => by
        obtain ⟨hw, hu, hl⟩ := hO.adviceChecked B a h
        exact ⟨hw, hu, hR.advBelow B a h, hl⟩
      innerRecord := fun a h => by
        obtain ⟨-, ⟨ca, x, hca, -⟩, -⟩ := h
        exact ⟨ca, hca⟩
      innerMembers := hO.innerMembers
      innerKind := hO.innerKind
      innerClosed := hR.innerClosed
      twinBlock := fun rb' B h => by
        obtain ⟨-, -, -, hU, -⟩ := FamRunCtx.twin_some h
        cases hf : K.fam B with
        | none => exact Or.inr rfl
        | some rb =>
          refine Or.inl ⟨rb, rfl, fun e => ?_, hR.twinAfter rb' B rb h hf⟩
          subst e
          exact hU B hf
      twinWalked := fun rb' B h => by
        obtain ⟨hT, hRB, -, hU, -⟩ := FamRunCtx.twin_some h
        refine ⟨Or.inl hT, hU, ?_⟩
        cases hf : K.fam rb' with
        | none => rfl
        | some r => exact (hRB.not_indBlock (FamRunCtx.fam_some hf).1.2.2.1).elim
      twinRecord := fun rb' B h => by
        obtain ⟨-, ⟨c, rs', hc, hrs', hpos, -⟩, -, -, hFC, -⟩ := FamRunCtx.twin_some h
        obtain ⟨crb, rs, hF⟩ := hO.record B rb' hFC
        have e : crb = c := Option.some.inj (hF.record.symm.trans hc)
        subst e
        have e' : rs = rs' := Ixon.ConstantInfo.muts.inj (hF.muts.symm.trans hrs')
        subst e'
        exact ⟨_, _, hF, by omega⟩ }
  case claimed =>
    intro A c ms hT hc hinfo hpos hall hun
    obtain ⟨x, hx, hns⟩ := hun
    obtain ⟨B, hFC, hTB, hMB, hIB⟩ := hB.recArm A hT ⟨c, ms, hc, hinfo, hpos, hall⟩
    by_cases hcl : ∃ B', K.fam B' = some A
    · exact Or.inl hcl
    · have hU : Unclaimed K.fam A := fun B' h => hcl ⟨B', h⟩
      obtain ⟨B', hB'⟩ := FamRunCtx.twin_of (K := K) (rb' := A) (B := B)
        ⟨hT, ⟨c, ms, hc, hinfo, hpos, hall⟩, ⟨c, x, hc, hx, hns⟩, hU, hFC, hTB, hMB, hIB⟩
      exact Or.inr ⟨B', hB'⟩
  case modeled =>
    intro B cb ms hT hc hlog hinfo hall hroute hun
    obtain ⟨x, hx, hns⟩ := hun
    have hFB : K.FamBlock B :=
      ⟨hT, hroute, ⟨cb, ms, hc, hinfo, constAddr_muts_pos hinfo hx, hall⟩, ⟨cb, x, hc, hx, hns⟩,
        fun cb' hcb' => by
          rw [hc] at hcb'
          cases hcb'
          exact hlog⟩
    obtain ⟨rb, hFC⟩ := hO.modeledCall B hFB
    exact FamRunCtx.fam_of hFB hFC
  case famInductive =>
    intro B rb h
    obtain ⟨cb, ms, hcb, hms, -, hall⟩ := (FamRunCtx.fam_some h).1.2.2.1
    exact ⟨cb, ms, hcb, hms, hall⟩
  case famCall =>
    intro B rb h
    obtain ⟨⟨-, hroute, -⟩, hFC, -⟩ := FamRunCtx.fam_some h
    refine ⟨hroute, K.famCalls B rb, FamRunCtx.famCalls_spec hFC, fun a ha => ?_⟩
    by_cases hca : ∃ ca x, recordOf K.E₀ a = some ca ∧ ConstAddrOf a ca x
    · exact Or.inl ⟨rb, h, ha, hca⟩
    · have hno : ∀ ca x, recordOf K.E₀ a = some ca → ¬ ConstAddrOf a ca x :=
        fun ca x hrec hx => hca ⟨ca, x, hrec, hx⟩
      exact Or.inr ⟨hno, hO.adviceNoAddr B rb a h ha hno⟩
  case twinCall =>
    intro rb' B h
    obtain ⟨-, -, -, -, hFC, -⟩ := FamRunCtx.twin_some h
    exact ⟨K.famCalls B rb', FamRunCtx.famCalls_spec hFC⟩
  case innerCall =>
    intro a h
    obtain ⟨-, -, B, rb, hor, hchk⟩ := h
    exact ⟨B, rb, K.famCalls B rb, hor,
      FamRunCtx.famCalls_spec (FamRunCtx.famCheck_of_inner hor),
      hchk.elim Or.inl fun h => Or.inr (Or.inl h)⟩
  case form =>
    intro B rb rb' h ht
    obtain ⟨hTr, hRB, -, hU, hFC', -⟩ := FamRunCtx.twin_some ht
    obtain ⟨-, hFC, hpref⟩ := FamRunCtx.fam_some h
    have hne : rb ≠ rb' := fun e => by
      subst e
      exact hU B h
    rcases hB.form B rb rb' hFC hFC' hne hTr hRB with hp | hp
    · exact hp
    · exact hpref ⟨rb', hFC', hp⟩

/-! ## The row -/

/-- **A premise at every walk and witness**: `P` of the run's choices with the form `Pref`. -/
def AtWalk (Pref : _root_.Address → _root_.Address → Prop)
    (P : FamRunCtx → (_root_.Address → Nat) → Prop) : Prop :=
  ∀ (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (seeds : List _root_.Address) (E₀ : Ixon.Env) (lim : Option Nat)
    (Top : _root_.Address → Prop) (rank : _root_.Address → Nat),
    Claim.TopWalkCore calls bAddr t seeds E₀ lim Top rank → TopGraph t E₀ seeds Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon), TableShape.{u} t (fun _ => True) R envT →
      P ⟨calls, bAddr, t, E₀, lim, Top, envT, Pref⟩ rank

/-- **The walk at another rank that keeps its edges**: a used reference of a top-walked record
top-walked below it or covered, a projection record's block below it. -/
theorem topWalk_of_edges {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank rank' : _root_.Address → Nat}
    (h : Claim.TopWalk calls t seeds E₀ lim Top rank)
    (hclosed : ∀ a x, Top a → UsedRef E₀ a x → (Top x ∧ rank' x < rank' a) ∨ Covered t x)
    (howner : ∀ a c, Top a → recordOf E₀ a = some c → IsProj c →
      Top (Ix.Cert.ownerOf a c) ∧ rank' (Ix.Cert.ownerOf a c) < rank' a) :
    Claim.TopWalk calls t seeds E₀ lim Top rank' := by
  obtain ⟨bAddr, hW, hG⟩ := h
  exact ⟨bAddr, ⟨hW.topLim, hW.table, hW.runStore, hW.hashedStored, hW.seedsTop, hW.record,
    hclosed, howner, hW.seedLogic, hW.seedNotInert, hW.checked, hW.refsNotInert, hW.refsNotBlock,
    hW.safeRefs⟩, ⟨hG.seedsTop, hG.record, hclosed, howner, hG.members, hG.projMember,
    hG.standing, hG.seedLogic⟩⟩

/-- **The ranking**: at every walk and witness, a rank of the family graph at the choices (one
lemma: the walk's edges with advice before its block and a block before its family record or
twin, re-ranked topologically; not yet proved here). -/
def FamilyRanking (Pref : _root_.Address → _root_.Address → Prop) : Prop :=
  AtWalk.{u} Pref fun K _ => ∃ rank', FamilyRanked K rank'

/-- **Row `familyGraph` from what the run's functions give**: the batch's (`BatchGives`), the
facts of unchanged functions not yet proved here (`NoBatchFields`), the ranking, and the stored
twins' field (to be restated). Rule (c)'s fact is `familyRun_of`'s second part. -/
theorem familyGraphRow_of_parts (Pref : _root_.Address → _root_.Address → Prop)
    (batch : AtWalk.{u} Pref fun K _ => BatchGives K)
    (noBatch : AtWalk.{u} Pref fun K _ => NoBatchFields K)
    (ranking : FamilyRanking.{u} Pref)
    (storedTwin : AtWalk.{u} Pref fun K _ => StoredTwinField K) :
    FamilyGraphRow.{u} := by
  intro calls t seeds E₀ lim Top rank hWalk R envT hshape
  obtain ⟨bAddr, hW, hG⟩ := hWalk
  obtain ⟨rank', hR⟩ := ranking calls bAddr t seeds E₀ lim Top rank hW hG R envT hshape
  obtain ⟨hFR, -⟩ := familyRun_of ⟨calls, bAddr, t, E₀, lim, Top, envT, Pref⟩
    (batch calls bAddr t seeds E₀ lim Top rank hW hG R envT hshape)
    (noBatch calls bAddr t seeds E₀ lim Top rank hW hG R envT hshape) hR
    (storedTwin calls bAddr t seeds E₀ lim Top rank hW hG R envT hshape)
  exact ⟨rank', _, _, _, _, topWalk_of_edges ⟨bAddr, hW, hG⟩ hR.closed hR.owner, hFR⟩

end IxVM.Refinement.Typing
