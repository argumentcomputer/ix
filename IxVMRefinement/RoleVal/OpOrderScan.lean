import IxVMRefinement.RoleVal.GroupWalkLim
import IxVMRefinement.Decl.NativeCommon

/-! # The operation-order scan of the well-founded block

Below the well-founded block a walk checks, at every reference to a role-bound record, that an
operation reached is in force (`KernelRoles::assert_op_reached_in_order`, in `walk_ctx`). Inside
the block (groups 33 to 40, all validated at limit 33) that check is off and
`KernelRoles::op_order_scan` stands in for it: from an operation's record and from each
certificate's references it follows used references and a projection's block, and at every
operation reached asserts that it is in force or among the group's needs.

This file specifies the scan's reach, for the three functions that call each other:
`op_order_scan` (one address), `op_order_scan_refs` (the references of one record),
`op_order_scan_list` (a reference list).

* `ScanSeam x_tbl x_lim x_needs h₀ Ok`: what one call of `op_order_scan` gives, as a premise:
  the scan stops at the address with `Ok`, or it calls `op_order_scan_refs` on it. It is a
  premise because `op_order_scan` is the function that changes (below); the other two have
  their observations and are specified from them.
* `ScanEntry`, `ScanClosed`: the scan's closure: a record the scan entered is bytes the run
  hashed, and its block (if it is a projection) and every reference it uses are `Ok` (the scan
  stopped there) or entered.
* `op_order_scan_refs_spec`, `op_order_scan_list_spec`: the scan from a record, and from a
  reference list, enters a closed list of records.
* `unwalkedAnchorsInForce`, `unwalkedAnchorsInForce_iff`, `inForce_block_cases`: the seventeen
  anchors in force in the well-founded block whose validation does not walk their record
  (decided over the 108 roles), and what the other roles in force there are.
* `ScanStopsAt`: where the scan stops, in the form the source is to take: at an operation in
  force or needed (asserted), and at a role in force that is no operation unless it is one of
  those seventeen. `OpOrderScanStep` is `ScanSeam` at that predicate: the statement the
  regenerated observation of `op_order_scan` has to give.

Why `op_order_scan` changes. As the source stands, the scan stops at every role in force that
is no operation, on the ground that such a record was checked in its own group's validation
under the per-reference rule. That is so for a walked role, a walked anchor and a standard
axiom's references; the quotient package is bound at committed records and no walk passes an
inert axiom. It is not so for the seventeen anchors here, and a walk does not stop at them:
an accepted run can check a later well-founded operation's record inside an earlier one's
group (executed on the stage-3 artifact). The scan is to go on through those anchors.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.RoleVal

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

/-! ## The roles in force in the well-founded block -/

/-- **The anchors in force in the well-founded block whose validation does not walk their
record**: seventeen roles, each compared with its specification by type only. -/
def unwalkedAnchorsInForce : List Ix.Kernel.Role :=
  [.true, .trueIntro, .reduceBool, .reduceNat, .notProp, .decidable, .decidableIsTrue,
   .decidableIsFalse, .natLe, .int, .intOfNat, .intNegSucc, .intLe, .bitVec, .bitVecOfNat,
   .byteArray, .byteArrayEmpty]

set_option maxRecDepth 100000 in
/-- They are the anchors of a group below 33 at which `anchor_walked` answers 0. -/
theorem unwalkedAnchorsInForce_iff (ro : Ix.Kernel.Role) :
    ro ∈ unwalkedAnchorsInForce ↔
      (Ix.SpecDigest.groupOf ro < 33 ∧ roleSpecKindNat ro = 1 ∧ anchorWalked ro = false) := by
  cases ro <;> decide

set_option maxRecDepth 100000 in
/-- **Every role in force in the well-founded block**: its validation walks its bound record
(a walked role or a walked anchor), or it is of the quotient package, a standard axiom, an
inert axiom, or one of the seventeen anchors. -/
theorem inForce_block_cases (ro : Ix.Kernel.Role) :
    Ix.SpecDigest.groupOf ro < 33 →
      roleWalksBound ro = true ∨ anchorWalked ro = true ∨ isQuotRole ro = true ∨
        roleSpecKindNat ro = 3 ∨ roleSpecKindNat ro = 4 ∨ ro ∈ unwalkedAnchorsInForce := by
  cases ro <;> decide

set_option maxRecDepth 100000 in
/-- The operations are of groups 7 to 13 and 33 to 40: at a limit above 40 all are in force. -/
theorem operation_group (ro : Ix.Kernel.Role) :
    roleSpecKindNat ro = 2 →
      (7 ≤ Ix.SpecDigest.groupOf ro ∧ Ix.SpecDigest.groupOf ro ≤ 13) ∨
        (33 ≤ Ix.SpecDigest.groupOf ro ∧ Ix.SpecDigest.groupOf ro ≤ 40) := by
  cases ro <;> decide

/-! ## The scan's closure -/

/-- **A record the scan entered**, with the addresses `within` entered: bytes the run hashed
that decode to a record whose block (itself, if it is no projection) and whose every used
reference is `Ok` (the scan stopped there) or entered. -/
def ScanEntry (calls : List (Call F)) (Ok : _root_.Address → Prop)
    (within : List _root_.Address) (x : _root_.Address) : Prop :=
  ∃ (rawBytes : ByteArray) (c : Ixon.Constant),
    rawBytes.size < 4294967296 ∧ Hashed calls rawBytes ∧ Address.blake3Pure rawBytes = x ∧
    Ixon.deConstant rawBytes = .ok c ∧ Ixon.deConstantExact rawBytes = .ok c ∧
    (Ok (Ix.Cert.ownerOf x c) ∨ Ix.Cert.ownerOf x c ∈ within) ∧
    ∀ j : Nat, (hj : j < c.refs.toList.length) → j ∈ BaseSeams.usedRefIdxs c →
      Ok c.refs.toList[j] ∨ c.refs.toList[j] ∈ within

/-- **The entered records are closed.** -/
def ScanClosed (calls : List (Call F)) (Ok : _root_.Address → Prop)
    (entered : List _root_.Address) : Prop :=
  ∀ x ∈ entered, ScanEntry calls Ok entered x

theorem ScanEntry.mono {cs₁ cs₂ : List (Call F)} {Ok : _root_.Address → Prop}
    {w₁ w₂ : List _root_.Address} {x : _root_.Address}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (hw : ∀ y ∈ w₁, y ∈ w₂) (h : ScanEntry cs₁ Ok w₁ x) :
    ScanEntry cs₂ Ok w₂ x := by
  obtain ⟨rawBytes, c, hsz, hh, hb, hde, hdeExact, hown, hrefs⟩ := h
  refine ⟨rawBytes, c, hsz, Claim.hashed_mono hsub hh, hb, hde, hdeExact, ?_, ?_⟩
  · rcases hown with h | h
    · exact Or.inl h
    · exact Or.inr (hw _ h)
  · intro j hj hu
    rcases hrefs j hj hu with h | h
    · exact Or.inl h
    · exact Or.inr (hw _ h)

theorem ScanClosed.mono {cs₁ cs₂ : List (Call F)} {Ok : _root_.Address → Prop}
    {entered : List _root_.Address} (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂)
    (h : ScanClosed cs₁ Ok entered) : ScanClosed cs₂ Ok entered :=
  fun x hx => (h x hx).mono hsub (fun _ hy => hy)

theorem scanClosed_nil (calls : List (Call F)) (Ok : _root_.Address → Prop) :
    ScanClosed calls Ok [] :=
  fun _ hx => (nomatch hx)

theorem ScanClosed.append {calls : List (Call F)} {Ok : _root_.Address → Prop}
    {e₁ e₂ : List _root_.Address} (h₁ : ScanClosed calls Ok e₁) (h₂ : ScanClosed calls Ok e₂) :
    ScanClosed calls Ok (e₁ ++ e₂) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact (h₁ x h).mono (fun _ hc => hc) (fun _ hy => List.mem_append_left _ hy)
  · exact (h₂ x h).mono (fun _ hc => hc) (fun _ hy => List.mem_append_right _ hy)

/-! ## One call of `op_order_scan`, as a premise -/

/-- **What one call of `KernelRoles::op_order_scan` gives the scan's specification**, for calls
at heaps that extend `h₀` with the table, limit and needs `x_tbl`, `x_lim`, `x_needs`: the scan
stops at the address with `Ok`, or it calls `op_order_scan_refs` on the address, inside the
call. -/
def ScanSeam (x_tbl x_lim x_needs : SourceValue F) (h₀ : Heap F)
    (Ok : _root_.Address → Prop) : Prop :=
  ∀ (a : _root_.Address) (x_a r : SourceValue F) (h h' : Heap F) (calls : List (Call F)),
    Heap.Extends h₀ h → BaseSeams.addr h x_a a →
    ObsFn W "KernelRoles::op_order_scan" [x_tbl, x_lim, x_needs, x_a] h r h' calls →
    Ok a ∨ ∃ (r' : SourceValue F) (h₁ h₂ : Heap F) (cs : List (Call F)),
      Heap.Extends h h₁ ∧
      ObsFn W "KernelRoles::op_order_scan_refs" [x_tbl, x_lim, x_needs, x_a] h₁ r' h₂ cs ∧
      (∀ cl ∈ cs, cl ∈ calls) ∧ cs.length < calls.length

/-! ## The scan from a record and from a reference list -/

private theorem refs_size_lt_bound_scan {rawBytes : ByteArray} {c : Ixon.Constant}
    (hsz : rawBytes.size < 4294967296)
    (hdeExact : Ixon.deConstantExact rawBytes = .ok c) :
    c.refs.size < 8589934592 := by
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound rawBytes c hdeExact
  have hrefs : c.refs.size ≤ c.resourceSize := by
    dsimp [Ixon.Constant.resourceSize]
    omega
  omega

private theorem scan_fuel_aux {x_tbl x_lim x_needs : SourceValue F} {h₀ : Heap F}
    {Ok : _root_.Address → Prop} (seam : ScanSeam x_tbl x_lim x_needs h₀ Ok) :
    ∀ (fuel : Nat),
      (∀ {a : _root_.Address} {x_a r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
         calls.length ≤ fuel → Heap.Extends h₀ h → BaseSeams.addr h x_a a →
         ObsFn W "KernelRoles::op_order_scan_refs" [x_tbl, x_lim, x_needs, x_a] h r h' calls →
         ∃ entered : List _root_.Address, a ∈ entered ∧ ScanClosed calls Ok entered) ∧
      (∀ {i : Nat} {refs : List _root_.Address} {idxs : List Nat}
         {x_refs x_used r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
         calls.length ≤ fuel → Heap.Extends h₀ h →
         i + refs.length < 8589934592 →
         RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem h refs x_refs →
         Claim.RepSortedIdxFrom h idxs i x_used →
         ObsFn W "KernelRoles::op_order_scan_list"
           [x_tbl, x_lim, x_needs, x_refs, x_used, .field (i : F)] h r h' calls →
         ∃ entered : List _root_.Address, ScanClosed calls Ok entered ∧
           ∀ j : Nat, (hj : j < refs.length) → i + j ∈ idxs →
             Ok refs[j] ∨ refs[j] ∈ entered) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    -- one address: the seam, then the scan of its record's references
    have scanAt : ∀ {b : _root_.Address} {x_b r : SourceValue F} {h h' : Heap F}
        {cs : List (Call F)}, cs.length < fuel → Heap.Extends h₀ h → BaseSeams.addr h x_b b →
        ObsFn W "KernelRoles::op_order_scan" [x_tbl, x_lim, x_needs, x_b] h r h' cs →
        ∃ entered : List _root_.Address, ScanClosed cs Ok entered ∧ (Ok b ∨ b ∈ entered) := by
      intro b x_b r h h' cs hlt hbase hb evs
      rcases seam b x_b r h h' cs hbase hb evs with hok | ⟨r', h₁, h₂, cs', hext, evr, hsub, hlen⟩
      · exact ⟨[], scanClosed_nil cs Ok, Or.inl hok⟩
      · obtain ⟨entered, hmem, hcl⟩ :=
          (ih cs'.length (by omega)).1 (Nat.le_refl _) (hbase.trans hext)
            (BaseSeams.addr_mono hext hb) evr
        exact ⟨entered, hcl.mono hsub, Or.inr hmem⟩
    refine ⟨?_, ?_⟩
    · intro a x_a r h h' calls hfuel hbase ha ev
      obtain ⟨m2, cs12, x_info, w39, x_refs, w40, w41, v407, m408, cs410, cs419, v426, m457,
        cs465, ev14, sg415, ev467, ev421, hc482⟩ :=
        Obs.«KernelRoles::op_order_scan_refs».obs ev
      obtain ⟨ext1, rawBytes, c, hsz, hh_load, hblk, hde, hdeExact, hrep, _⟩ :=
        Claim.load_verified_constant_de ha ev14
      have hlen410 : cs410.length < calls.length := by
        rw [hc482]
        simp only [List.length_cons, List.length_append]
        omega
      have hseg : Heap.Extends m2 m408 ∧ ∃ entered₁ : List _root_.Address,
          ScanClosed cs410 Ok entered₁ ∧
          (Ok (Ix.Cert.ownerOf a c) ∨ Ix.Cert.ownerOf a c ∈ entered₁ ∨
            Ix.Cert.ownerOf a c = a) := by
        obtain ⟨infoVal, _, _, _, _, hv_c, hinfo, _, _, _, _⟩ := hrep
        injection hv_c with _ _ hargs_c
        simp only [List.cons.injEq] at hargs_c
        rw [← hargs_c.1] at hinfo
        rcases sg415 with
          ⟨w104, x_b, cs118, hv81, ev120, hc153⟩ |
          ⟨w183, w184, x_b, cs203, hne155, hv160, ev205, hc238⟩ |
          ⟨w268, x_b, cs282, hne155, hne240, hv245, ev284, hc317⟩ |
          ⟨w347, x_b, cs361, hne155, hne240, hne319, hv324, ev363, hc396⟩ |
          ⟨wM, vM, mM, csM, hne155, hne240, hne319, hne398, hvM, evM, heqM, hrM, hhM, hcM⟩ |
          ⟨hne155, hne240, hne319, hne398, hneM, he404, he405, hc406⟩
        · rw [hv81] at hinfo
          cases hc_i : c.info <;> rw [hc_i] at hinfo
          case iPrj p =>
            obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
            rw [hpv] at hpv_eq
            injection hpv_eq with _ _ h1
            simp only [List.cons.injEq, and_true] at h1
            injection h1 with _ _ hpargs
            simp only [List.cons.injEq, and_true] at hpargs
            rw [← hpargs.2] at hblk_addr
            have hown : Ix.Cert.ownerOf a c = p.block := by simp [Ix.Cert.ownerOf, hc_i]
            have hlt : cs118.length < fuel := by
              have : cs118.length < cs410.length := by rw [hc153]; simp
              omega
            obtain ⟨entered₁, hcl, hmem⟩ := scanAt hlt (hbase.trans ext1) hblk_addr ev120
            refine ⟨ev120.heap_extends, entered₁,
              hcl.mono (fun cl hcl' => by rw [hc153]; simp [hcl']), ?_⟩
            rw [hown]
            rcases hmem with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        · rw [hv160] at hinfo
          cases hc_i : c.info <;> rw [hc_i] at hinfo
          case cPrj p =>
            obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
            rw [hpv] at hpv_eq
            injection hpv_eq with _ _ h1
            simp only [List.cons.injEq, and_true] at h1
            injection h1 with _ _ hpargs
            simp only [List.cons.injEq, and_true] at hpargs
            rw [← hpargs.2.2] at hblk_addr
            have hown : Ix.Cert.ownerOf a c = p.block := by simp [Ix.Cert.ownerOf, hc_i]
            have hlt : cs203.length < fuel := by
              have : cs203.length < cs410.length := by rw [hc238]; simp
              omega
            obtain ⟨entered₁, hcl, hmem⟩ := scanAt hlt (hbase.trans ext1) hblk_addr ev205
            refine ⟨ev205.heap_extends, entered₁,
              hcl.mono (fun cl hcl' => by rw [hc238]; simp [hcl']), ?_⟩
            rw [hown]
            rcases hmem with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        · rw [hv245] at hinfo
          cases hc_i : c.info <;> rw [hc_i] at hinfo
          case rPrj p =>
            obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
            rw [hpv] at hpv_eq
            injection hpv_eq with _ _ h1
            simp only [List.cons.injEq, and_true] at h1
            injection h1 with _ _ hpargs
            simp only [List.cons.injEq, and_true] at hpargs
            rw [← hpargs.2] at hblk_addr
            have hown : Ix.Cert.ownerOf a c = p.block := by simp [Ix.Cert.ownerOf, hc_i]
            have hlt : cs282.length < fuel := by
              have : cs282.length < cs410.length := by rw [hc317]; simp
              omega
            obtain ⟨entered₁, hcl, hmem⟩ := scanAt hlt (hbase.trans ext1) hblk_addr ev284
            refine ⟨ev284.heap_extends, entered₁,
              hcl.mono (fun cl hcl' => by rw [hc317]; simp [hcl']), ?_⟩
            rw [hown]
            rcases hmem with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        · rw [hv324] at hinfo
          cases hc_i : c.info <;> rw [hc_i] at hinfo
          case dPrj p =>
            obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
            rw [hpv] at hpv_eq
            injection hpv_eq with _ _ h1
            simp only [List.cons.injEq, and_true] at h1
            injection h1 with _ _ hpargs
            simp only [List.cons.injEq, and_true] at hpargs
            rw [← hpargs.2] at hblk_addr
            have hown : Ix.Cert.ownerOf a c = p.block := by simp [Ix.Cert.ownerOf, hc_i]
            have hlt : cs361.length < fuel := by
              have : cs361.length < cs410.length := by rw [hc396]; simp
              omega
            obtain ⟨entered₁, hcl, hmem⟩ := scanAt hlt (hbase.trans ext1) hblk_addr ev363
            refine ⟨ev363.heap_extends, entered₁,
              hcl.mono (fun cl hcl' => by rw [hc396]; simp [hcl']), ?_⟩
            rw [hown]
            rcases hmem with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        · -- a block: the scan asserts it is not modeled, and its owner is itself
          have hown : Ix.Cert.ownerOf a c = a := by
            unfold Ix.Cert.ownerOf
            cases hc_i : c.info <;> rw [hc_i] at hinfo <;> try rfl
            all_goals
              obtain ⟨pv, hv', _⟩ := hinfo
              first
                | exact absurd hv' (hne155 [_] rfl)
                | exact absurd hv' (hne240 [_] rfl)
                | exact absurd hv' (hne319 [_] rfl)
                | exact absurd hv' (hne398 [_] rfl)
          refine ⟨by subst hhM; exact evM.heap_extends, [], scanClosed_nil cs410 Ok,
            Or.inr (Or.inr hown)⟩
        · have hown : Ix.Cert.ownerOf a c = a := by
            unfold Ix.Cert.ownerOf
            cases hc_i : c.info <;> rw [hc_i] at hinfo <;> try rfl
            all_goals
              obtain ⟨pv, hv', _⟩ := hinfo
              first
                | exact absurd hv' (hne155 [_] rfl)
                | exact absurd hv' (hne240 [_] rfl)
                | exact absurd hv' (hne319 [_] rfl)
                | exact absurd hv' (hne398 [_] rfl)
          refine ⟨by subst he405; exact Heap.Extends.refl _, [], scanClosed_nil cs410 Ok,
            Or.inr (Or.inr hown)⟩
      obtain ⟨ext_seg, entered₁, hcl₁, hown⟩ := hseg
      obtain ⟨ext_idx, hidxs⟩ := Claim.const_idxs_of_spec (hrep.mono ext_seg) ev467
      have hrefs_rep :
          RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem m457 c.refs.toList
            x_refs := by
        obtain ⟨_, _, refsPtr, _, _, hv_c, _, _, hr_list, _, _⟩ := hrep
        injection hv_c with _ _ hargs_c
        simp only [List.cons.injEq] at hargs_c
        rw [← hargs_c.2.2.1] at hr_list
        exact repList_heapMono₂ _ Claim.repAddrElem_heapMono₂ (ext_seg.trans ext_idx) hr_list
      have hrefs_bound : 0 + c.refs.toList.length < 8589934592 := by
        rw [Nat.zero_add, Array.length_toList]
        exact refs_size_lt_bound_scan hsz hdeExact
      have ev421' : ObsFn W "KernelRoles::op_order_scan_list"
          [x_tbl, x_lim, x_needs, x_refs, v426, .field ((0 : Nat) : F)] m457 r h' cs419 := by
        rw [Nat.cast_zero]
        exact ev421
      have hlen419 : cs419.length < calls.length := by
        rw [hc482]
        simp only [List.length_cons, List.length_append]
        omega
      obtain ⟨entered₂, hcl₂, hlist⟩ :=
        (ih cs419.length (by omega)).2 (i := 0) (Nat.le_refl _)
          (hbase.trans (ext1.trans (ext_seg.trans ext_idx))) hrefs_bound hrefs_rep hidxs ev421'
      have hsub1 : ∀ cl ∈ cs410, cl ∈ calls := fun cl hcl => by rw [hc482]; simp [hcl]
      have hsub2 : ∀ cl ∈ cs419, cl ∈ calls := fun cl hcl => by rw [hc482]; simp [hcl]
      have hsub0 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => by rw [hc482]; simp [hcl]
      refine ⟨a :: (entered₁ ++ entered₂), List.mem_cons_self .., ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · refine ⟨rawBytes, c, hsz, Claim.hashed_mono hsub0 hh_load, hblk, hde, hdeExact, ?_, ?_⟩
        · rcases hown with h | h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ (List.mem_append_left _ h))
          · exact Or.inr (by rw [h]; exact List.mem_cons_self ..)
        · intro j hj hu
          rcases hlist j hj (by rw [Nat.zero_add]; exact hu) with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ (List.mem_append_right _ h))
      · rcases List.mem_append.mp hx' with h | h
        · exact (hcl₁ x h).mono hsub1
            (fun _ hy => List.mem_cons_of_mem _ (List.mem_append_left _ hy))
        · exact (hcl₂ x h).mono hsub2
            (fun _ hy => List.mem_cons_of_mem _ (List.mem_append_right _ hy))
    · intro i refs idxs x_refs x_used r h h' calls hfuel hbase hbound hrefs hidxs ev
      cases Obs.«KernelRoles::op_order_scan_list».obs ev with
      | Nil ld12 he22 he23 hc24 =>
        obtain rfl := Lib.rep_nil_of_load hrefs ld12
        exact ⟨[], scanClosed_nil calls Ok, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
      | Cons x_b x_rest m_pop cs_pop x_hit x_next_used v125 m126 cs128 cs137 v145
          ld12 ev_pop sg133 op194 ev139 hc196 =>
        obtain ⟨b, rest, rfl, hb_rep, hrest_rep⟩ := Lib.rep_cons_of_load hrefs ld12
        have hi : i < 72057594037927936 := by simp at hbound; omega
        obtain ⟨rfl, hiff_pop, hidxs_next⟩ := Claim.sorted_pop_spec idxs hi hidxs ev_pop
        have hlen128 : cs128.length ≤ calls.length := by
          rw [hc196]
          simp only [List.length_cons, List.length_append]
          omega
        have hseg : Heap.Extends h m126 ∧ ∃ entered₁ : List _root_.Address,
            ScanClosed cs128 Ok entered₁ ∧ (i ∈ idxs → Ok b ∨ b ∈ entered₁) := by
          cases sg133 with
          | n1 cs80 _ ev82 hc115 =>
            have hlt : cs80.length < fuel := by
              have : cs80.length < cs128.length := by
                rw [hc115]
                simp only [List.length_cons, List.length_append]
                omega
              omega
            obtain ⟨entered₁, hcl, hmem⟩ := scanAt hlt hbase hb_rep ev82
            exact ⟨ev82.heap_extends, entered₁,
              hcl.mono (fun cl hcl' => by rw [hc115]; simp [hcl']), fun _ => hmem⟩
          | other hne116 he122 he123 hc124 =>
            refine ⟨?_, [], scanClosed_nil cs128 Ok, fun hin => absurd (hiff_pop.mpr hin) hne116⟩
            subst he123
            exact Heap.Extends.refl _
        obtain ⟨ext1, entered₁, hcl₁, hhead⟩ := hseg
        obtain rfl := Decl.evalBinOp_add_one i op194
        have hbound' : (i + 1) + rest.length < 8589934592 := by simp at hbound; omega
        have hlen137 : cs137.length < calls.length := by
          rw [hc196]
          simp only [List.length_cons, List.length_append]
          omega
        obtain ⟨entered₂, hcl₂, htail⟩ :=
          (ih cs137.length (by omega)).2 (Nat.le_refl _) (hbase.trans ext1) hbound'
            (repList_heapMono₂ _ Claim.repAddrElem_heapMono₂ ext1 hrest_rep)
            (hidxs_next.mono ext1) ev139
        have hsub1 : ∀ cl ∈ cs128, cl ∈ calls := fun cl hcl => by rw [hc196]; simp [hcl]
        have hsub2 : ∀ cl ∈ cs137, cl ∈ calls := fun cl hcl => by rw [hc196]; simp [hcl]
        refine ⟨entered₁ ++ entered₂, (hcl₁.mono hsub1).append (hcl₂.mono hsub2),
          fun j hj hij => ?_⟩
        cases j with
        | zero =>
          rcases hhead (by simpa using hij) with h0 | h0
          · exact Or.inl (by simpa using h0)
          · exact Or.inr (List.mem_append_left _ (by simpa using h0))
        | succ j' =>
          have hj' : j' < rest.length := by simpa using hj
          have hij' : i + 1 + j' ∈ idxs := by
            rw [show i + 1 + j' = i + (j' + 1) by omega]
            exact hij
          rcases htail j' hj' hij' with h1 | h1
          · exact Or.inl (by simpa using h1)
          · exact Or.inr (List.mem_append_right _ (by simpa using h1))

/-- **The scan from a record** (`KernelRoles::op_order_scan_refs`): it enters a closed list of
records holding the record. -/
theorem op_order_scan_refs_spec {x_tbl x_lim x_needs : SourceValue F} {h₀ : Heap F}
    {Ok : _root_.Address → Prop} (seam : ScanSeam x_tbl x_lim x_needs h₀ Ok)
    {a : _root_.Address} {x_a r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hbase : Heap.Extends h₀ h) (ha : BaseSeams.addr h x_a a)
    (ev : ObsFn W "KernelRoles::op_order_scan_refs" [x_tbl, x_lim, x_needs, x_a] h r h' calls) :
    ∃ entered : List _root_.Address, a ∈ entered ∧ ScanClosed calls Ok entered :=
  (scan_fuel_aux seam calls.length).1 (Nat.le_refl _) hbase ha ev

/-- **The scan from a reference list** (`KernelRoles::op_order_scan_list`): each reference at a
used position is one the scan stopped at, or a record of a closed list of entered records. -/
theorem op_order_scan_list_spec {x_tbl x_lim x_needs : SourceValue F} {h₀ : Heap F}
    {Ok : _root_.Address → Prop} (seam : ScanSeam x_tbl x_lim x_needs h₀ Ok)
    {i : Nat} {refs : List _root_.Address} {idxs : List Nat}
    {x_refs x_used r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hbase : Heap.Extends h₀ h) (hbound : i + refs.length < 8589934592)
    (hrefs : RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem h refs x_refs)
    (hidxs : Claim.RepSortedIdxFrom h idxs i x_used)
    (ev : ObsFn W "KernelRoles::op_order_scan_list"
      [x_tbl, x_lim, x_needs, x_refs, x_used, .field (i : F)] h r h' calls) :
    ∃ entered : List _root_.Address, ScanClosed calls Ok entered ∧
      ∀ j : Nat, (hj : j < refs.length) → i + j ∈ idxs → Ok refs[j] ∨ refs[j] ∈ entered :=
  (scan_fuel_aux seam calls.length).2 (Nat.le_refl _) hbase hbound hrefs hidxs ev

/-! ## Where the scan stops, in the form the source is to take -/

/-- **Where the scan stops**: at a record bound to an operation, which it asserts in force at
the limit or among the group's needs; and at a record bound to a role in force that is no
operation, unless the role is an anchor whose validation does not walk its record. -/
def ScanStopsAt (t : Ix.Kernel.RoleTable) (n : Nat) (needs : List Ix.Kernel.Role)
    (a : _root_.Address) : Prop :=
  ∃ ro : Ix.Kernel.Role, t.addressOf? ro = some a ∧
    ((roleSpecKindNat ro = 2 ∧ (Ix.SpecDigest.groupOf ro < n ∨ ro ∈ needs)) ∨
      (roleSpecKindNat ro ≠ 2 ∧ Ix.SpecDigest.groupOf ro < n ∧
        ¬ (roleSpecKindNat ro = 1 ∧ anchorWalked ro = false)))

/-- **The step of the scan after the change of `KernelRoles::op_order_scan`**, as the statement
its regenerated observation has to give: under the table `t` and the needs `needs` (role
numbers), a call at an address stops there (`ScanStopsAt`) or calls `op_order_scan_refs` on
it. -/
def OpOrderScanStep : Prop :=
  ∀ (t : Ix.Kernel.RoleTable) (bAddr : _root_.Address) (n : Nat) (needs : List Ix.Kernel.Role)
    (x_tbl x_needs : SourceValue F) (h₀ : Heap F),
    n < 4294967296 → Claim.TableFullRep t bAddr h₀ x_tbl →
    RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h₀ (needs.map (·.idx)) x_needs →
    ScanSeam x_tbl (.field (n : F)) x_needs h₀ (ScanStopsAt t n needs)

/-- **An operation's record the scan reaches is in force or needed**: a stop of the scan at a
record bound to an operation is one the scan asserted. -/
theorem ScanStopsAt.operation {t : Ix.Kernel.RoleTable} {n : Nat}
    {needs : List Ix.Kernel.Role} {a : _root_.Address} (hwf : t.wf = true)
    (h : ScanStopsAt t n needs a) {ro : Ix.Kernel.Role} (ha : t.addressOf? ro = some a)
    (hop : roleSpecKindNat ro = 2) (hinj : ∀ r₁ r₂ : Ix.Kernel.Role,
      t.addressOf? r₁ = some a → t.addressOf? r₂ = some a → r₁ = r₂) :
    Ix.SpecDigest.groupOf ro < n ∨ ro ∈ needs := by
  obtain ⟨ro', ha', hcase⟩ := h
  have e : ro' = ro := hinj ro' ro ha' ha
  subst e
  rcases hcase with ⟨_, hok⟩ | ⟨hne, _, _⟩
  · exact hok
  · exact absurd hop hne

end IxVM.Refinement.RoleVal
