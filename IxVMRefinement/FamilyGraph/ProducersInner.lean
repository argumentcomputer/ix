import IxVMRefinement.FamilyGraph.InnerCheckedOwed
import IxVMRefinement.FamilyGraph.ProducersAcyclic
import IxVMRefinement.FamilyGraph.ProducersInnerRefs
import IxVMRefinement.FamilyGraph.CompositionFam
import IxVMRefinement.Claim.RefSafetyExcept
import IxVM.Obs.KernelModeled

/-! # The records a family check checks, at the graph producer's choices

The row `innerChecked` asks `InnerChecked` of every family run, whose inner records need not be
the graph producer's. At the producer's choices (`FamRunCtx`) every inner record is listed by
the own advice walk of a family check of a top-walked block (a scope check) or witnessed by one
as a container's recursor, so what the walk and the family check's reference facts
(`FamilyCheckFacts`) give settles the record's own addresses. This module states what is owed of the
inner records there, beside what the graph row is owed, and composes both:

* `Decl.check_advice_records_nodup`, `FamilyOwnAdvice.walk_nil`, `FamilyCallOwn.listed_nodup`,
  `FamilyCallOwn.listed_inj`: a family check's own advice walk lists no address twice.
  `check_advice_records` refuses an address already in its seen set (`addr_set_member(a, seen)`
  is asserted `0`) before checking it and inserts it after, and `check_family` starts the walk
  from the empty set;
* `FamRunCtx.inner_ownRef`: an inner record that is no twin uses one of its own constant
  addresses only where the witness's environment stores it or it is covered. The proof reads
  the scope check's facts: an earlier listed record is no projection record and is not the
  record itself (no address is listed twice, `FamilyCallOwn.listed_inj`); a witness of the basis
  is stored, a covered one covered; a witness at the end of a dependency path from the block, or
  a constant address of one, is top-walked with its block, which the inner record is not; a
  container's recursor's witness is a standalone recursor or a member of a block of recursors,
  which an advice record is not;
* `InnerOwed`: what is owed of the inner records at the choices: no inert used reference and a
  covered or `NeedOk` used reference (`assert_inner_refs_safe`);
* `innerGives_of_owed`, `innerChecked_at`: `InnerGives` and `InnerChecked` at the choices;
* `FamilyGraphInnerOwed`: what the graph row and the inner records are owed together;
  `FamilyGraphRowInner`, `familyGraphRowInner_of_owed`: the graph row with `InnerChecked` at the
  same choices; `familyGraphRow_of_inner`: the graph row alone;
* `InnerStepsChecked`, `innerStepsChecked_of_kinds`, `familySteps_of_graphInner`,
  `circuitComposed_of_partsFamInner`: the typing half's premise and the public statement's
  composition with the inner steps read at the graph's own choices. -/

universe u

/-! ## No address listed twice by a family check's own advice walk -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Library Aiur.Library.List Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core
open IxVM.Refinement.Claim (RepAddrSet rbtree_set_lookup_spec rbtree_set_insert_spec)
open IxVM (F)

set_option linter.unusedVariables false

/-- **The advice walk lists no address twice**: from the listed advice addresses `advAs` and a
seen set that represents the addresses `S`, no listed address is in `S` (the walk asserts the
membership test `0` at each) and the listed addresses are pairwise distinct (each is inserted
into the seen set of the rest of the walk). -/
theorem check_advice_records_nodup {rc wset : SourceValue F} :
    ∀ (advAs : List Bytes.Address) (S : List _root_.Address)
      {x_advice x_seen r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h advAs x_advice →
      RepAddrSet h S x_seen →
      ObsFn Obs.W "KernelModeled::check_advice_records" [rc, x_advice, x_seen, wset] h r h' cs →
      (∀ b ∈ advAs, ixAddr b ∉ S) ∧ (advAs.map ixAddr).Nodup
  | [], S, x_advice, x_seen, r, h, h', cs, hadv_rep, hseen, ev =>
    ⟨fun _ hb => (nomatch hb), List.nodup_nil⟩
  | a :: rest, S, x_advice, x_seen, r, h, h', cs, hadv_rep, hseen, ev => by
    match Obs.«KernelModeled::check_advice_records».obs ev with
    | .Nil (ld12 := ld12) .. =>
      cases Lib.rep_nil_of_load hadv_rep ld12
    | .Cons (m90 := m90) (ld12 := ld12) (ev_mfihupbr := ev_seen) (heq_sefkntmx := heq_seen)
        (ev_xzbngsxs := ev_wset) (ev102 := ev102) (ev170 := ev170) (ev140 := ev140) .. =>
      subst heq_seen
      obtain ⟨a', rest', heq_cons, ha_rep, hrest_rep⟩ := Lib.rep_cons_of_load hadv_rep ld12
      injection heq_cons with ha_eq hrest_eq
      subst ha_eq hrest_eq
      have hnot : ixAddr a ∉ S := by
        obtain ⟨_, ev6, _⟩ := Obs.«KernelClaim::addr_set_member».obs ev_seen
        rw [← Obs.Names.«RBTreeMap::rbtree_map_lookup_or_default<Field>».symbol] at ev6
        obtain ⟨hr, -⟩ := rbtree_set_lookup_spec ha_rep hseen ev6
        intro hin
        rw [ite_eq_left hin] at hr
        exact absurd (Value.field.inj hr) zero_ne_one
      have ext_90 : Heap.Extends h m90 :=
        (ObsFn.heap_extends ev_seen).trans
          ((ObsFn.heap_extends ev_wset).trans (ObsFn.heap_extends ev102))
      rw [← Obs.Names.«RBTreeMap::rbtree_map_insert<Field>».symbol] at ev170
      obtain ⟨ext_160, hseen1⟩ :=
        rbtree_set_insert_spec (Bytes.repAddressRef_heapMono₂ addrTy ext_90 ha_rep)
          (hseen.mono ext_90) ev170
      obtain ⟨hout, hnd⟩ :=
        check_advice_records_nodup rest (ixAddr a :: S)
          (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) (ext_90.trans ext_160)
            hrest_rep)
          hseen1 ev140
      refine ⟨fun b hb => ?_, ?_⟩
      · rcases List.mem_cons.mp hb with rfl | hrm
        · exact hnot
        · exact fun hin => hout b hrm (List.mem_cons_of_mem _ hin)
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hmem => ?_, hnd⟩
        obtain ⟨b, hb, hba⟩ := List.mem_map.mp hmem
        exact hout b hb (by rw [hba]; exact List.mem_cons_self)

end IxVM.Refinement.Decl

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

section Listed

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.Obs

/-- **The family check's own advice walk, from the empty set**: as `FamilyOwnAdvice.walk`, with
the seen set the walk starts from, the empty tree. -/
theorem FamilyOwnAdvice.walk_nil {x_rc x_block x_rec_block : SourceValue F} {h : Heap F}
    {r : SourceValue F} {h' : Heap F} {calls : List (Call F)} {advAs : List Bytes.Address}
    (w : FamilyOwnAdvice x_rc x_block x_rec_block h r h' calls advAs) :
    ∃ (m m' : Heap F) (xadv wset v : SourceValue F) (cs₁ : List (Call F)),
      Heap.Extends h m ∧ RepList addrListEnum (Bytes.RepAddressRef addrTy) m advAs xadv ∧
      ObsFn Obs.W "KernelModeled::check_advice_records"
        [x_rc, xadv, .construct addrMapEnum "Nil" [], wset] m v m' cs₁ ∧
      ∀ cl ∈ cs₁, cl ∈ calls := by
  match w with
  | .mk (ev_ws := ev_ws) (wset := wset) (ev_asb := ev_asb) (m_adv := m_adv) (m_adv' := m_adv')
      (x_advice := x_advice) (v_adv := v_adv) (cs_adv := cs_adv) (ev_adv := ev_adv)
      (ext_h_ws := ext_h_ws) (ext_asb_adv := ext_asb_adv) (advRep := advRep)
      (sub_adv := sub_adv) .. =>
    exact ⟨m_adv, m_adv', x_advice, wset, v_adv, cs_adv,
      ext_h_ws.trans (ev_ws.heap_extends.trans (ev_asb.heap_extends.trans ext_asb_adv)),
      advRep, ev_adv, sub_adv⟩

/-- **A family check's own advice walk lists no address twice**: the walk starts from the empty
set (`FamilyOwnAdvice.walk_nil`), and refuses an address it has seen
(`Decl.check_advice_records_nodup`). -/
theorem FamilyOwnAdvice.listed_nodup {x_rc x_block x_rec_block : SourceValue F} {h : Heap F}
    {r : SourceValue F} {h' : Heap F} {calls : List (Call F)} {advAs : List Bytes.Address}
    (w : FamilyOwnAdvice x_rc x_block x_rec_block h r h' calls advAs) :
    (advAs.map ixAddr).Nodup := by
  obtain ⟨m, m', xadv, wset, v, cs₁, -, hadv, ev, -⟩ := w.walk_nil
  exact (Decl.check_advice_records_nodup advAs [] hadv (Claim.RepAddrSet.nil m) ev).2

/-- The own advice list of an observed family check has no address twice. -/
theorem FamilyCallOwn.listed_nodup {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {B rb : _root_.Address} {lim : Option Nat} {cs : List (Call F)}
    {advAs : List Bytes.Address} (hown : FamilyCallOwn calls bAddr t B rb lim cs advAs) :
    (advAs.map ixAddr).Nodup := by
  obtain ⟨h, h', rc, xb, xrb, r, -, -, -, -, w, -, -⟩ := hown
  exact w.listed_nodup

/-- **Two positions of a family check's own advice list with one address are one position.** -/
theorem FamilyCallOwn.listed_inj {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {B rb : _root_.Address} {lim : Option Nat} {cs : List (Call F)}
    {advAs : List Bytes.Address} (hown : FamilyCallOwn calls bAddr t B rb lim cs advAs)
    {j k : Nat} {b b' : Bytes.Address} (hj : advAs[j]? = some b) (hk : advAs[k]? = some b')
    (hbb : ixAddr b = ixAddr b') : j = k := by
  have hjl : j < (advAs.map ixAddr).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hj).1
  refine (List.Nodup.getElem?_inj hjl hown.listed_nodup).mp ?_
  rw [List.getElem?_map, List.getElem?_map, hj, hk, Option.map_some, Option.map_some, hbb]

end Listed

/-! ## The inner records' own addresses at the choices -/

section Own

variable {K : FamRunCtx} {seeds : List _root_.Address} {rank : _root_.Address → Nat}

/-- A constant address of a record the run checked (top-walked or inner) is the record itself,
or holds a projection record whose block is the record. -/
theorem FamRunCtx.walkedConstAddr_cases
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : FamilyCheckFacts K)
    {D x : _root_.Address} {cD : Ixon.Constant} (hD : K.Top D ∨ K.Inner D)
    (hc : recordOf K.E₀ D = some cD) (hx : ConstAddrOf D cD x) :
    (x = D ∧ Standalone cD) ∨
      ∃ P, recordOf K.E₀ x = some P ∧ IsProj P ∧ Ix.Cert.ownerOf x P = D := by
  rcases hx with h | ⟨ms, i, m, hms, hm, hx⟩
  · exact Or.inl h
  · right
    rcases hD with hT | hI
    · exact hG.block_record hT hc hms hm hx
    · obtain ⟨hmem, hctor⟩ := FamRunCtx.innerMembers_of hW hB D cD ms hI hc hms i m hm
      rcases hx with hx | ⟨ind, j, hind, hj, hx⟩
      · rw [hx]
        exact ⟨_, hmem, memberProjection_isProj D i m, ownerOf_memberProjection _ D i m⟩
      · rw [hx]
        exact ⟨_, hctor ind j hind hj, constructorProjection_isProj D i j,
          ownerOf_constructorProjection _ D i j⟩

/-- **Two records the run checked share no constant address.** -/
theorem FamRunCtx.walkedConstAddr_unique
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : FamilyCheckFacts K)
    {D D' x : _root_.Address} {cD cD' : Ixon.Constant} (hD : K.Top D ∨ K.Inner D)
    (hD' : K.Top D' ∨ K.Inner D') (hc : recordOf K.E₀ D = some cD)
    (hc' : recordOf K.E₀ D' = some cD') (hx : ConstAddrOf D cD x) (hx' : ConstAddrOf D' cD' x) :
    D = D' := by
  rcases FamRunCtx.walkedConstAddr_cases hW hG hB hD hc hx with ⟨h1, hs1⟩ | ⟨P, hP, hp, ho⟩ <;>
    rcases FamRunCtx.walkedConstAddr_cases hW hG hB hD' hc' hx' with
      ⟨h2, hs2⟩ | ⟨P', hP', hp', ho'⟩
  · exact h1.symm.trans h2
  · rw [h1, hc] at hP'
    rw [← Option.some.inj hP'] at hp'
    exact (standalone_not_proj hs1 hp').elim
  · rw [h2, hc'] at hP
    rw [← Option.some.inj hP] at hp
    exact (standalone_not_proj hs2 hp).elim
  · have e : P = P' := Option.some.inj (hP.symm.trans hP')
    subst e
    exact ho.symm.trans ho'

/-- **A constant address of an inner record is not top-walked**: it is the record, or a
projection record whose block, the record, the walk would reach. -/
theorem FamRunCtx.inner_constAddr_not_top
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : FamilyCheckFacts K)
    {a x : _root_.Address} {c : Ixon.Constant} (hIa : K.Inner a) (hc : recordOf K.E₀ a = some c)
    (hx : ConstAddrOf a c x) (hTx : K.Top x) : False := by
  rcases FamRunCtx.walkedConstAddr_cases hW hG hB (Or.inr hIa) hc hx with ⟨hxa, -⟩ |
    ⟨P, hP, hp, ho⟩
  · rw [hxa] at hTx
    exact hIa.1 hTx
  · have hT := (hG.owner x P hTx hP hp).1
    rw [ho] at hT
    exact hIa.1 hT

/-- **A witness of a scope check that is a constant address of an inner record is stored or
covered**: a basis role's address is stored (`basis_stored`); a dependency path from the
top-walked block makes the witness, or the block it is a constant address of, top-walked
(`dep_top`), which no constant address of an inner record is. -/
theorem FamRunCtx.inner_witBase_kept
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : FamilyCheckFacts K) {R : Ixon.Env}
    (hshape : TableShape.{u} K.t (fun _ => True) R K.envT)
    {B rb a x : _root_.Address} {cs : List (Call F)} {c : Ixon.Constant}
    (hS : K.ScopeAt B rb cs) (hIa : K.Inner a) (hc : recordOf K.E₀ a = some c)
    (hx : ConstAddrOf a c x) (hwb : K.WitBase B x) :
    StoredAt K.t K.envT x ∨ Covered K.t x := by
  have htwf : K.t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [hW.check_ok]
    rfl
  rcases hwb with ⟨ro, hro, ha⟩ | hcov | hdep | ⟨ib, cib, hdep, hcib, hxib⟩
  · exact Or.inl (basis_stored hshape htwf hro ha)
  · exact Or.inr hcov
  · exact (FamRunCtx.inner_constAddr_not_top hW hG hB hIa hc hx
      (dep_top hW hdep hS.2.1).1).elim
  · have hTib := (dep_top hW hdep hS.2.1).1
    have e := FamRunCtx.walkedConstAddr_unique hW hG hB (Or.inl hTib) (Or.inr hIa) hcib hc hxib hx
    rw [e] at hTib
    exact (hIa.1 hTib).elim

/-- **A reference of a top-walked block's closure that is a constant address of an inner record
is covered**: a used reference of the block is top-walked or covered; a constant address of the
block, or of the block a used reference projects from, would make the inner record the
top-walked block. -/
theorem FamRunCtx.inner_blockRef_covered
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : FamilyCheckFacts K)
    {D a x : _root_.Address} {c : Ixon.Constant} (hTD : K.Top D) (hIa : K.Inner a)
    (hc : recordOf K.E₀ a = some c) (hx : ConstAddrOf a c x) (hbr : K.BlockRef D x) :
    Covered K.t x := by
  rcases hbr with hu | ⟨cD, hcD, hxD⟩ | ⟨q, cq, cO, huq, hcq, hpq, hcO, hxO, hcov⟩
  · rcases hW.closed D x hTD hu with ⟨hTx, -⟩ | hcov
    · exact (FamRunCtx.inner_constAddr_not_top hW hG hB hIa hc hx hTx).elim
    · exact hcov
  · have e := FamRunCtx.walkedConstAddr_unique hW hG hB (Or.inl hTD) (Or.inr hIa) hcD hc hxD hx
    rw [e] at hTD
    exact (hIa.1 hTD).elim
  · rcases hW.closed D q hTD huq with ⟨hTq, -⟩ | hcq'
    · have hTO := (hW.owner q cq hTq hcq hpq).1
      have e :=
        FamRunCtx.walkedConstAddr_unique hW hG hB (Or.inl hTO) (Or.inr hIa) hcO hc hxO hx
      rw [e] at hTO
      exact (hIa.1 hTO).elim
    · exact hcov hcq'

/-- **A container's recursor a scope check witnesses, if it is a constant address of an inner
record that is no block of recursors, is stored or covered**: a standalone witness is the inner
record itself, whose used references are of the closure of a top-walked block or witnesses of
the check; any other is a member of a block of recursors with a family check, which the inner
record would then be. -/
theorem FamRunCtx.inner_contWitness_kept
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : FamilyCheckFacts K) {R : Ixon.Env}
    (hshape : TableShape.{u} K.t (fun _ => True) R K.envT)
    {B rb a x : _root_.Address} {cs : List (Call F)} {c : Ixon.Constant}
    (hS : K.ScopeAt B rb cs) (hIa : K.Inner a) (hc : recordOf K.E₀ a = some c)
    (hnr : ¬ RecBlock K.E₀ a) (hu : UsedRef K.E₀ a x) (hx : ConstAddrOf a c x)
    (hcw : K.ContWitness cs B x) :
    StoredAt K.t K.envT x ∨ Covered K.t x := by
  by_cases hcov : Covered K.t x
  · exact Or.inr hcov
  obtain ⟨ib, hdep, -, -, hstand, hkind⟩ := hB.contWitness B rb cs x hS hcw hcov
  have hTib := (dep_top hW hdep hS.2.1).1
  rcases hkind with ⟨cx, hcx, hsx⟩ | ⟨a'', ca'', cs', hca'', hx'', hRB, hfc'', -⟩
  · rcases FamRunCtx.walkedConstAddr_cases hW hG hB (Or.inr hIa) hc hx with ⟨hxa, -⟩ |
      ⟨P, hP, hpP, -⟩
    · have hu' : UsedRef K.E₀ x x := by
        rw [hxa]
        rw [hxa] at hu
        exact hu
      rcases hstand cx hcx hsx x hu' with hbr | hwb
      · exact Or.inr (FamRunCtx.inner_blockRef_covered hW hG hB hTib hIa hc hx hbr)
      · exact FamRunCtx.inner_witBase_kept hW hG hB hshape hS hIa hc hx hwb
    · have e := Option.some.inj (hcx.symm.trans hP)
      subst e
      exact (standalone_not_proj hsx hpP).elim
  · obtain ⟨crb, rs, hF⟩ := FamRunCtx.record_of hW ib a'' ⟨cs', hfc''⟩
    have e : crb = ca'' := Option.some.inj (hF.record.symm.trans hca'')
    subst e
    obtain ⟨P, hP, hpP, hoP⟩ := hF.constAddr hx''
    rcases FamRunCtx.walkedConstAddr_cases hW hG hB (Or.inr hIa) hc hx with ⟨hxa, hsa⟩ |
      ⟨P', hP', -, hoP'⟩
    · rw [hxa, hc] at hP
      rw [← Option.some.inj hP] at hpP
      exact (standalone_not_proj hsa hpP).elim
    · have e2 : P = P' := Option.some.inj (hP.symm.trans hP')
      subst e2
      have e3 : a'' = a := hoP.symm.trans hoP'
      rw [e3] at hRB
      exact (hnr hRB).elim

/-- **An inner record that is no twin uses one of its own constant addresses only where the
witness's environment stores it or it is covered** (module docstring). -/
theorem FamRunCtx.inner_ownRef
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : FamilyCheckFacts K) {R : Ixon.Env}
    (hshape : TableShape.{u} K.t (fun _ => True) R K.envT) :
    ∀ a c x, K.Inner a → K.twin a = none → recordOf K.E₀ a = some c → UsedRef K.E₀ a x →
      ConstAddrOf a c x → StoredAt K.t K.envT x ∨ Covered K.t x := by
  intro a c x hIa htw hc hu hx
  obtain ⟨hnT, -, hcase⟩ := id hIa
  rcases hcase with ⟨B, rb, cs, hS, ⟨advAs, hown, b, hbmem, hba⟩ |
      ⟨hwit, -, hcovA, ca, hca, hsA⟩⟩ | ⟨B', hN⟩
  · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hbmem
    subst hba
    rcases hB.adviceRefs B rb cs advAs hS hown k b hk x hu with
      ⟨j, b', hjk, hj, hxb', hnp⟩ | ⟨j, b', c', hjk, hj, hc', hx'⟩ | hwb | hcw
    · rcases FamRunCtx.walkedConstAddr_cases hW hG hB (Or.inr hIa) hc hx with ⟨hxa, -⟩ |
        ⟨P, hP, hpP, -⟩
      · have e := hown.listed_inj hj hk (hxb'.trans hxa)
        omega
      · exact (hnp P hP hpP).elim
    · have hWa' : K.Top (Core.ixAddr b') ∨ K.Inner (Core.ixAddr b') := by
        by_cases hT' : K.Top (Core.ixAddr b')
        · exact Or.inl hT'
        · exact Or.inr ⟨hT', ⟨c', x, hc', hx'⟩, Or.inl ⟨B, rb, cs, hS,
            Or.inl ⟨advAs, hown, b', List.mem_of_getElem? hj, rfl⟩⟩⟩
      have e := FamRunCtx.walkedConstAddr_unique hW hG hB hWa' (Or.inr hIa) hc' hc hx' hx
      have e' := hown.listed_inj hj hk e
      omega
    · exact FamRunCtx.inner_witBase_kept hW hG hB hshape hS hIa hc hx hwb
    · exact FamRunCtx.inner_contWitness_kept hW hG hB hshape hS hIa hc
        (FamRunCtx.listedNotRec_of hW hS hown hk) hu hx hcw
  · have e : ca = c := Option.some.inj (hca.symm.trans hc)
    rw [e] at hsA
    obtain ⟨ib, hdep, -, -, hstand, -⟩ := hB.contWitness B rb cs a hS hwit hcovA
    have hTib := (dep_top hW hdep hS.2.1).1
    rcases hstand c hc hsA x hu with hbr | hwb
    · exact Or.inr (FamRunCtx.inner_blockRef_covered hW hG hB hTib hIa hc hx hbr)
    · exact FamRunCtx.inner_witBase_kept hW hG hB hshape hS hIa hc hx hwb
  · obtain ⟨B'', h''⟩ := FamRunCtx.nestedTwin_of hN
    rw [htw] at h''
    cases h''

end Own

/-! ## What is owed of the inner records at the choices -/

/-- **What is owed of the records a family check checks, at the graph producer's choices**
(proved from `FamRunCtx.inner_ref_safe` at every top-level walk). -/
structure InnerOwed (K : FamRunCtx) : Prop where
  /-- `assert_inner_refs_safe` in `check_advice_record` and `container_refs_check`: its
  `assert_safe_used_refs` runs `assert_ref_allowed` at every used reference of an inner record. -/
  notInert : ∀ a x, K.Inner a → K.twin a = none → UsedRef K.E₀ a x → ¬ InertAt K.t x
  /-- The uncovered branch of `assert_safe_used_refs` (the referenced record and its owner are
  not unsafe) and `assert_used_not_block` with `assert_not_block_ref`. -/
  needOk : ∀ a x, K.Inner a → K.twin a = none → UsedRef K.E₀ a x →
    Covered K.t x ∨ NeedOk K.E₀ x

/-- **`InnerOwed` holds at every top-level walk** (`FamRunCtx.inner_ref_safe`). -/
theorem innerOwed_of_walk {K : FamRunCtx} {seeds : List _root_.Address}
    {rank : _root_.Address → Nat}
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank) :
    InnerOwed K :=
  ⟨fun _ _ hIa htw hu => (FamRunCtx.inner_ref_safe hW hIa htw hu).1,
    fun _ _ hIa htw hu => (FamRunCtx.inner_ref_safe hW hIa htw hu).2⟩

section Gives

variable {K : FamRunCtx} {seeds : List _root_.Address} {rank : _root_.Address → Nat}

/-- **`InnerGives` at the choices**: the inert and `NeedOk` fields from `InnerOwed`, the
own-address field from `FamRunCtx.inner_ownRef`. -/
theorem innerGives_of_owed
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hG : TopGraph K.t K.E₀ seeds K.Top rank) (hB : FamilyCheckFacts K) {R : Ixon.Env}
    (hshape : TableShape.{u} K.t (fun _ => True) R K.envT) (hIO : InnerOwed K) :
    InnerGives K.calls K.bAddr K.t K.envT K.E₀ K.lim K.Top K.Inner K.fam K.twin :=
  ⟨fun a x hIa _ htw _ hu => hIO.notInert a x hIa htw hu,
    fun a x hIa htw _ hu => hIO.needOk a x hIa htw hu,
    fun a c x hIa _ htw _ hc hu hx =>
      FamRunCtx.inner_ownRef hW hG hB hshape a c x hIa htw hc hu hx⟩

end Gives

/-! ## The graph row with the inner records -/

/-- **Row `familyGraph` with the records its family checks check**: as `FamilyGraphRow`, and
`InnerChecked` at the same choices. -/
def FamilyGraphRowInner : Prop :=
  ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
    (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
    (rank : _root_.Address → Nat), Claim.TopWalk calls t seeds E₀ lim Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon), TableShape.{u} t (fun _ => True) R envT →
      ∃ (rank' : _root_.Address → Nat) (fam twin : _root_.Address → Option _root_.Address)
        (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
        Claim.TopWalk calls t seeds E₀ lim Top rank' ∧
        FamilyRun calls t envT E₀ lim Top rank' fam twin adv Inner ∧
        ∃ bAddr, InnerChecked calls bAddr t envT E₀ lim Top rank' fam twin Inner

/-- `FamilyGraphRowInner` forgets the inner records' facts. -/
theorem familyGraphRow_of_inner (h : FamilyGraphRowInner.{u}) : FamilyGraphRow.{u} := by
  intro calls t seeds E₀ lim Top rank hWalk R envT hshape
  obtain ⟨rank', fam, twin, adv, Inner, hW', hFR, -⟩ :=
    h calls t seeds E₀ lim Top rank hWalk R envT hshape
  exact ⟨rank', fam, twin, adv, Inner, hW', hFR⟩

/-- **What the graph row and the records its family checks check are owed**, at the twin
preference `Pref`: at every walk and witness, the run's facts the graph reads (`FamilyCheckFacts`) and
the stored twins' field (`StoredTwinField`), at the run's choices (`InnerOwed` is proved by
`innerOwed_of_walk`). -/
def FamilyGraphInnerOwed (Pref : RunPref) : Prop :=
  AtWalk.{u} Pref fun K _ => FamilyCheckFacts K ∧ StoredTwinField K

/-- `FamilyGraphInnerOwed` gives `FamilyGraphOwed`. -/
theorem familyGraphOwed_of_inner {Pref : RunPref} (h : FamilyGraphInnerOwed.{u} Pref) :
    FamilyGraphOwed.{u} Pref :=
  h

/-- **The graph row with the inner records, from what they are owed**: the ranking and
`FamilyRun` at the choices (as `familyGraphRowPref_of_facts`), and `InnerChecked` at the same
choices from `InnerGives` (`innerGives_of_owed`, `innerOwed_of_walk`, `innerChecked_of_gives`) at
the binding of the run's family checks, the walk's. -/
theorem familyGraphRowInner_of_owed {Pref : RunPref} (h : FamilyGraphInnerOwed.{u} Pref) :
    FamilyGraphRowInner.{u} := by
  intro calls t seeds E₀ lim Top rank hWalk R envT hshape
  obtain ⟨bAddr, hW, hG⟩ := hWalk
  obtain ⟨hB, hST⟩ := h calls bAddr t seeds E₀ lim Top rank hW hG R envT hshape
  obtain ⟨rank', hR⟩ : ∃ rank',
      FamilyRanked ⟨calls, bAddr, t, E₀, lim, Top, envT, Pref calls bAddr t E₀ lim⟩ rank' :=
    ⟨_, familyRanked_of_edges hW
      (rankEdges_of hW hG hB hshape (FamRunCtx.famEdge_acyclic hW hG hB))⟩
  obtain ⟨hFR, -⟩ :=
    familyRun_of ⟨calls, bAddr, t, E₀, lim, Top, envT, Pref calls bAddr t E₀ lim⟩ hB hW
      (containerKindFact_of _ hW) hR hST
  have hWalk' : Claim.TopWalk calls t seeds E₀ lim Top rank' :=
    topWalk_of_edges ⟨bAddr, hW, hG⟩ hR.closed hR.owner
  exact ⟨rank', _, _, _, _, hWalk', hFR, bAddr, innerChecked_of_gives hWalk' hFR
    (FamRunCtx.checks_of _ hB) (innerGives_of_owed hW hG hB hshape (innerOwed_of_walk hW))⟩

/-! ## The composition -/

/-- **The step of every record a family check checked, where the run gives `InnerChecked` of
it**: the premise of `familySteps_of_graphInner` for those units, stated at every family run with
`InnerChecked` at some binding (the inner records' facts are read with the graph's choices). -/
def InnerStepsChecked (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) : Prop :=
  ∀ (calls : List (Call F)) t seeds E₀ lim Top rank,
    Claim.TopWalk calls t seeds E₀ lim Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon)
      (fam twin : _root_.Address → Option _root_.Address)
      (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop)
      (bAddr : _root_.Address),
      FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner →
      InnerChecked calls bAddr t envT E₀ lim Top rank fam twin Inner →
      ∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c, Inner A → Unclaimed fam A →
        recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = none → twin A = none →
        UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim A c

/-- **The inner steps at the opened head trace**, from the step of every checked one-type native
block declared at its telescope: the other kinds' steps are proved for every checked unit
(`innerUnitSteps_of_kinds`; the body of `Endpoint.innerUnitSteps_of_innerChecked`). -/
theorem innerStepsChecked_of_kinds
    (nativeBlockTelescope :
      CheckedUnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt) fun calls t E₀ B cb =>
        ∃ ind : Ixon.Inductive,
          BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind) :
    InnerStepsChecked.{u} FormerOpenTraceAt := by
  intro calls t seeds E₀ lim Top rank hWalk R envT fam twin adv Inner bAddr hFR hIC
  obtain ⟨bAddrW, hW, hG⟩ := hWalk
  exact innerUnitSteps_of_kinds nativeBlockTelescope hG hFR.graph hIC hW.check_ok hW.runStore
    hW.hashedStored

/-- **The typing half's premise from the rows, the inner records read with the graph's
choices**: `familySteps_of_parts` with `FamilyGraphRowInner` in place of `FamilyGraphRow` and
the inner steps asked only where the run gives `InnerChecked`. -/
theorem familySteps_of_graphInner {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (familyGraph : FamilyGraphRowInner.{u}) (innerSteps : InnerStepsChecked.{u} L)
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
  obtain ⟨rank, fam, twin, adv, Inner, hWalk, hFR, bAddr, hIC⟩ :=
    familyGraph calls t seeds E₀ lim Top rank₀ hWalk₀ R envT hshape
  exact ⟨rank, fam, twin, adv, Inner, hWalk, hFR.graph,
    topUnitSteps_family standaloneDefinition standaloneTheoremOrOpaque standaloneRecursor
      definitionBlock nativeBlockTelescope nativeBlockAlias nativeBlockOtherTelescope hWalk hFR,
    innerSteps calls t seeds E₀ lim Top rank hWalk R envT fam twin adv Inner bAddr hFR hIC,
    fun E => familyBlock calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR,
    fun E hctx A c B rb crb hW hc hlog htw hrb hcrb =>
      familyTwin calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR hctx A c B
        rb crb hW hc hlog htw (Or.inl ⟨hrb, hcrb⟩),
    fun E hctx A c B hW hc hlog htw hnone => by
      obtain ⟨rb, crb, hst, hinst⟩ := hFR.storedTwin A B htw hnone
      exact unitStep_of_twin_stored hst
        (familyTwin calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR hctx A c
          B rb crb hW hc hlog htw (Or.inr ⟨hnone, hst, hinst⟩))⟩

/-- **The public statement from the open obligations, the inner records read with the graph's
choices**: `Endpoint.circuitComposed_of_partsFam` with `FamilyGraphRowInner` in place of
`FamilyGraphRow` and `InnerStepsChecked` in place of the inner steps at every family run. -/
theorem circuitComposed_of_partsFamInner
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {Run : List (Call F) → Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    {Fam : List (Call F) → BRun → Ix.Kernel.RoleTable → Nat → Ixon.Env → Ixon.Env →
      (_root_.Address → Option _root_.Address) → (_root_.Address → _root_.Address → Prop) →
      (_root_.Address → _root_.Address → Prop) → Prop}
    (bindingClaimExport :
      SourceSoundBounded fun calls d => BindingClaimExportObs (Run calls) calls d)
    (basisGroups : ∀ calls, BasisOverW.{u} L (Run calls))
    (groupAdmissions : ∀ calls, AdmitsChain (Run calls))
    (groupAdmissionReads : ∀ calls, AdmitsReadsChain (Run calls))
    (groupFamilies : ∀ calls, FamiliesChain (Run calls) (Fam calls))
    (groupClosure : ∀ calls, AtGroups (Run calls) fun ρ t g =>
      ClosureStepOverFamilyW.{u} L ρ t g (Fam calls ρ t g))
    (groupWithoutRoleUnit : ∀ calls, AtGroups (Run calls) (RoleFreeShapes.{u} L))
    (operationRoleUnit :
      ∀ calls, AtGroups (Run calls) (RoleUnitStepOverW.{u} (· ∈ RoleOps.opRoles) L))
    (standardAxiomRoleUnit :
      ∀ calls, AtGroups (Run calls) (RoleUnitStepOverW.{u} (· ∈ standardAxioms) L))
    (familyGraph : FamilyGraphRowInner.{u}) (innerSteps : InnerStepsChecked.{u} L)
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
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerTeleOther t E₀ B cb ind) :
    CircuitComposed.{u} := by
  unfold CircuitComposed
  refine circuitSound_of_bounded circuitToSource ?_
  intro dB valueB heapB callsB evB hbB
  show CircuitSound fun callsA dA => ComposedSpec.{u} callsA callsB dA dB
  refine circuitSound_of_bounded circuitToSource ?_
  intro dA valueA heapA callsA evA hbA
  show ComposedSpec.{u} callsA callsB dA dB
  exact composed_skeleton_over_familyW (bindingClaimExport dB valueB heapB callsB evB hbB)
    (basisGroups callsB) (groupAdmissions callsB) (groupAdmissionReads callsB)
    (groupFamilies callsB) (groupClosure callsB) (groupWithoutRoleUnit callsB)
    (operationRoleUnit callsB) (standardAxiomRoleUnit callsB) hbA
    (Claim.claimPhase_typing evA)
    (fun _ _ _ _ _ _ h => by
      obtain ⟨_, hW, _⟩ := h
      exact hW.topLim)
    (fun _ _ _ _ _ _ h => Claim.TopWalk.graph h)
    (familySteps_of_graphInner familyGraph innerSteps familyBlock familyTwin standaloneDefinition
      standaloneTheoremOrOpaque standaloneRecursor definitionBlock nativeBlockTelescope
      nativeBlockAlias nativeBlockOtherTelescope callsA)

end IxVM.Refinement.Typing
