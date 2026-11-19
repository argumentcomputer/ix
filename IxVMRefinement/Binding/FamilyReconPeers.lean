import IxVMRefinement.Binding.FamilyFlatBuild
import IxVMRefinement.Binding.FamilyReconMember

/-! # The peer recursors of a family record

`KernelCheck::check_recursor_canonical_at` lists, entry by entry of the flattened family, the
recursor of the family record whose major premise is over the entry (`build_peer_recs`,
`find_peer_recursor_with_spec`, `find_peer_rec_spec_walk`): the first recursor whose major premise
is headed by the entry's type and, at an auxiliary entry, taken at the entry's parameters and
levels. The reconstruction's model takes the record's own recursors in order
(`FamilyRecon.recAddrs`).

* `parentNp`, `PeerMatch`, `MatchAt`: the parameter count the search reads at a major premise's
  head (`get_ci`'s `Induct` arm, `0` at any other constant), and the search's test of one recursor
  against an entry, as a property of the recursor's type in the canonical reading.
* `extract_aux_spec_params_spec`: `KernelCheck::extract_aux_spec_params` on a recursor type
  whose major premise is headed by a constant cell.
* `peer_match_spec`: the test the walk computes for one recursor is `PeerMatch`.
* `find_peer_rec_spec_walk_spec`, `find_peer_recursor_with_spec_spec`: the search returns the
  projection address of the first recursor matching the entry.
* `AuxParamsOwn`: an auxiliary entry has as many parameters as the inductive type at its
  address declares. `matchAt_own`, `matchAt_sound`, `matchAt_first`: over `RecordFlat` entries with
  `AuxParamsOwn`, recursor `k` matches entry `k`, a recursor matching an entry is over an entry
  with its address and, among auxiliaries, its parameters and levels, so among different entries
  (`FlatDistinct.no_earlier_match`) no recursor before `k` matches entry `k`.
* `recAddrs_eq_range`: the record's member addresses are its recursors' projection addresses.
* **`build_peer_recs_spec`**: an observed `build_peer_recs` on the flattened family of a family
  record returns `FamilyRecon.recAddrs`, as many addresses as entries; `build_peer_recs_hyp` is
  the same in the shape `FamilyRecon.check_recursor_canonical_at_spec` takes it.
* `extract_aux_spec_params_from_rec_own`, `extract_aux_occ_us_own`: the parameters and the levels
  `check_recursor_canonical_at` reads of a recursor at an auxiliary entry are the entry's, where
  the parameter count it passes is the entry's (`AuxParamsOwn` at the parent the caller loaded).

The parameter count: the circuit takes an auxiliary's parameters as the major premise's first
`pnp` arguments, `pnp` the parameter count of the inductive type heading the major premise
itself, while `RecordFlat` takes as many as the entry has parameters, a count the derivation sets
from the head of the nested occurrence that introduced the entry's block. The two agree where
every type of that block declares the head's parameter count. The circuit asserts this of a block
when it checks the block's own types (`KernelCheck::peer_agree_walk`,
`KernelModeled::block_nparams`), not at the family check of a block that nests it, so here it is
the premise `AuxParamsOwn`.

* `NestedParamsAgree E B`: every type of a block other than `B` reads, at its own address, the
  parameter count of any inductive type of that block; a property of the store alone.
  `auxParamsOwn_of_derived`, `auxParamsOwn_of_blockDerived`: with it, the family derived from `B`
  (`BlockDerivedFlat`) has `AuxParamsOwn`. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option autoImplicit false

namespace IxVM.Refinement.Binding.FamilyReconPeers

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Consistency
open IxVM.Refinement.Binding.FamilyFlat
open IxVM.Refinement.Binding.FamilyOf
open IxVM.Refinement.Binding.FamilyFlatRecord
open IxVM.Refinement.Binding.FamilyFlatBuild
open IxVM.Refinement.Binding.FamilyRecon
open IxVM.Refinement.Typing
open IxVM.Refinement.Core (W KExpr KLevel KKey kexprEnum kexprListEnum addrTy ixAddr)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open IxVM (F)

/-! ## The search's test of one recursor against an entry -/

/-- **The parameter count the search reads at a major premise's head** (`get_ci`'s `Induct` arm;
`0` at a constant of another kind). -/
def parentNp (E : Ixon.Env) (a : _root_.Address) : Nat :=
  match indInfoAt E a with
  | some (some i) => i.np
  | _ => 0

/-- **The search's test of a major premise's type `d` against an entry**
(`find_peer_rec_spec_walk`'s `is_match`): `d` is headed by the entry's type and, at an auxiliary
entry, its first arguments, as many as that type declares parameters, lowered past `low`
binders, are the entry's parameters and its head's levels the entry's. -/
def PeerMatch (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (low : Nat) (d : KExpr)
    (e : FlatEntry) : Prop :=
  ∃ ls, Ix.Kernel.Expr.getAppFn d = .const (keyOf t e.addr) ls ∧
    (e.aux = true →
      ((Ix.Kernel.Expr.getAppArgs d).take (parentNp E e.addr)).map
          (Ix.Kernel.Expr.lowerBVars low 0) = e.params ∧ ls = e.levels)

/-- **Recursor `j` of the record matches the entry**: its major premise's type, in the canonical
reading, passes the search's test. -/
def MatchAt (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (rb : _root_.Address)
    (crb : Ixon.Constant) (rs : Array Ixon.MutConst) (j : Nat) (e : FlatEntry) : Prop :=
  ∃ (rc : Ixon.Recursor) (ty d : KExpr), rs[j]? = some (.recr rc) ∧
    loadedAt t (fun x => E.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat (mutsRoot rs j)
      rc.typ = some ty ∧
    binderDomAfter (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) ty =
      some d ∧
    PeerMatch t E (rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) d e

/-- **An auxiliary entry has as many parameters as the inductive type at its address declares.**
The derivation gives every type of a nested occurrence's block the occurrence's parameters, as
many as the occurrence's head declares, so this holds where the types of one block declare one
parameter count. -/
def AuxParamsOwn (E : Ixon.Env) (es : List FlatEntry) : Prop :=
  ∀ e ∈ es, e.aux = true → parentNp E e.addr = e.params.length

/-! ## `extract_aux_spec_params` -/

/-- **`KernelCheck::extract_aux_spec_params`** on a recursor type represented exactly whose major
premise is headed by a constant cell: the major premise's first `pnp` arguments, lowered past the
motives, minors and indices (`FamilyFlat.occParamsLower`). -/
theorem extract_aux_spec_params_spec {κ : _root_.Address → KKey}
    {np nmot nmin ni pnp : Nat}
    (hN : np + nmot + nmin + ni < 288230376151711744) (hpnp : pnp < 288230376151711744)
    {ty : KExpr} {x_ty xm xa xls r : SourceValue F} {h h' : Heap F}
    {cs root : List (Call F)}
    (hM : MajorConst h x_ty (np + nmot + nmin + ni) xm xa xls) (hty : TmOExact κ h ty x_ty)
    (ev : ObsFn W "KernelCheck::extract_aux_spec_params"
      [x_ty, .field (np : F), .field (nmot : F), .field (nmin : F), .field (ni : F),
        .field (pnp : F)] h r h' cs)
    (hbd : Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root) :
    Heap.Extends h h' ∧ ∃ d ys, binderDomAfter (np + nmot + nmin + ni) ty = some d ∧
      occParamsLower ((Ix.Kernel.Expr.getAppArgs d).take pnp) (nmot + nmin + ni) = some ys ∧
      RepList kexprListEnum (TmOExact κ) h' ys r := by
  obtain ⟨v1, x9, x17, v37, m38, cs48, x_major_ty, w86, w87, m104, cs115, x__head, x_args,
    cs145, v148, v149, m151, cs159, x184, op32, op24, op16, ev50, ld78, ev117, ev161, op199,
    op191, ev147, hc203⟩ := Obs.«KernelCheck::extract_aux_spec_params».obs ev
  have hv1 := sum4_ok op32 op24 op16
  subst hv1
  obtain ⟨hm, hxm⟩ := hM.peel hN ev50 ld78
  subst hm hxm
  obtain ⟨d, a, ls, As, hdom, hdeq, ⟨k, hd_tm⟩, -, -⟩ := hM.sem hty
  obtain ⟨hd, sp, H, As', htup, hH, hAs, hdE⟩ :=
    IxVM.Refinement.Decl.collect_spine_exact ev117 hd_tm
  injection htup with hl
  injection hl with h1 hl
  injection hl with h2 _
  subst h1 h2
  obtain ⟨a', ls', hHe, -, -⟩ := TmOExact.const_of_load ⟨k, hH⟩ (hM.head ev117)
  have hargsd : Ix.Kernel.Expr.getAppArgs d = As' := by
    rw [hdE, hHe, IxVM.Refinement.Decl.getAppArgs_mkAppN]
    rfl
  have hAs' : RepList kexprListEnum (TmOExact κ) m104 As' x_args :=
    repList_imp' (fun x p hx => ⟨k, hx⟩) hAs
  have hval : ((pnp : F)).val = pnp := FamilyOfCall.val_cast_lt_u58 hpnp
  have htake := Lib.Lists.take_spec (t := .ptr (.named "KernelTypes::KExprNode" []))
    (tmOExact_heapMono₂ (κ := κ))
    (by rw [Obs.Names.«Lists::take<&KernelTypes::KExprNode>».symbol]; exact ev161)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hAs')
  rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol, hval] at htake
  obtain ⟨-, htk⟩ := htake
  have hlow : v149 = .field ((nmot + nmin + ni : Nat) : F) := by
    simp only [evalBinOp, Except.ok.injEq] at op199
    subst op199
    simp only [evalBinOp, Except.ok.injEq] at op191
    rw [← op191]
    push_cast
    rfl
  subst hlow
  have bL : Bounded cs145 :=
    RomBound.bounded_mono hbd fun c hc' => by rw [hc203]; simp [hc']
  obtain ⟨ext, ys, hys, hrep⟩ := spec_params_lower_spec (root := root) (by omega) _ htk ev147 bL
    (fun c hc' => hroot c (by rw [hc203]; simp [hc']))
  refine ⟨ev117.heap_extends.trans (ev161.heap_extends.trans ext), d, ys, hdom, ?_, hrep⟩
  rw [hargsd]
  exact hys

/-! ## The test of one recursor -/

/-- The search's test on a major premise's type that is a constant applied. -/
theorem peerMatch_mkAppN {t : Ix.Kernel.RoleTable} (htwf : t.wf = true) {E : Ixon.Env}
    {low : Nat} {d : KExpr} {e : FlatEntry} {a : _root_.Address} {ls : List KLevel}
    {As : List KExpr} (hd : d = Ix.Kernel.Expr.mkAppN (.const (keyOf t a) ls) As) :
    PeerMatch t E low d e ↔
      a = e.addr ∧ (e.aux = true →
        (As.take (parentNp E a)).map (Ix.Kernel.Expr.lowerBVars low 0) = e.params ∧
          ls = e.levels) := by
  have hfn : Ix.Kernel.Expr.getAppFn d = .const (keyOf t a) ls := by
    rw [hd]
    exact getAppFn_const_mkAppN _ _ _
  have hargs : Ix.Kernel.Expr.getAppArgs d = As := by
    rw [hd, IxVM.Refinement.Decl.getAppArgs_mkAppN]
    rfl
  unfold PeerMatch
  rw [hfn, hargs]
  constructor
  · rintro ⟨ls', hc, haux⟩
    injection hc with hk hl
    have ha : a = e.addr := IxVM.Refinement.Core.keyOf_inj htwf hk
    subst hl
    subst ha
    exact ⟨rfl, haux⟩
  · rintro ⟨ha, haux⟩
    subst ha
    exact ⟨ls, rfl, haux⟩

/-- **The two factors of the test at an auxiliary entry**: the parameters
`extract_aux_spec_params` reads, compared by `spec_params_zeta_eq`, and the levels
`extract_aux_occ_us` reads, compared by `level_list_struct_eq`. -/
theorem aux_factors {κ : _root_.Address → KKey} (hinj : Function.Injective κ)
    {np nmot nmin ni pnp : Nat}
    (hN : np + nmot + nmin + ni < 288230376151711744) (hpnp : pnp < 288230376151711744)
    {ty d : KExpr} {ls us : List KLevel} {sp : List KExpr}
    {x_ty xm xa xls w0 w1 w2 w3 w4 w5 x_sp x_us v_sp x y v_us r : SourceValue F}
    {m m1 m2 m3 h' : Heap F} {cs1 cs2 cs3 cs4 root : List (Call F)}
    (hM : MajorConst m x_ty (np + nmot + nmin + ni) xm xa xls) (hty : TmOExact κ m ty x_ty)
    (hdom : binderDomAfter (np + nmot + nmin + ni) ty = some d)
    (rls : RepKLevelList m ls xls)
    (rsp : RepList kexprListEnum (TmOExact κ) m sp x_sp) (rus : RepKLevelList m us x_us)
    (ev1 : ObsFn W "KernelCheck::extract_aux_spec_params"
      [x_ty, .field (np : F), .field (nmot : F), .field (nmin : F), .field (ni : F),
        .field (pnp : F)] m v_sp m1 cs1)
    (ev2 : ObsFn W "KernelCheck::spec_params_zeta_eq" [v_sp, x_sp] m1 x m2 cs2)
    (ev3 : ObsFn W "KernelCheck::extract_aux_occ_us"
      [.construct "KernelTypes::KConstantInfo" "Rec"
        [w0, x_ty, .field (np : F), .field (ni : F), .field (nmot : F), .field (nmin : F),
          w1, w2, w3, w4, w5]] m2 v_us m3 cs3)
    (ev4 : ObsFn W "KernelCheck::level_list_struct_eq" [v_us, x_us] m3 y h' cs4)
    (op : evalBinOp .mul x y = .ok r)
    (b1 : Bounded cs1) (hroot : ∀ c ∈ cs1, c ∈ root) (b2 : Bounded cs2) :
    Heap.Extends m h' ∧
      (r = .field 1 ↔
        (((Ix.Kernel.Expr.getAppArgs d).take pnp).map
            (Ix.Kernel.Expr.lowerBVars (nmot + nmin + ni) 0) = sp ∧ ls = us)) := by
  obtain ⟨ext1, d', ys, hdom', hys, hrep⟩ :=
    extract_aux_spec_params_spec (root := root) hN hpnp hM hty ev1 b1 hroot
  have hdd : d' = d := Option.some.inj (hdom'.symm.trans hdom)
  subst hdd
  have hyeq := occParamsLower_eq _ _ _ hys
  have hx := spec_params_zeta_eq_exact hinj hrep (tmOExactList_mono ext1 rsp) b2 ev2
  have ext2 := ev2.heap_extends
  obtain ⟨hus, ext3⟩ := extract_aux_occ_us_spec hN (hM.mono (ext1.trans ext2)) ev3
  subst hus
  have ext123 := ext1.trans (ext2.trans ext3)
  obtain ⟨hy, hm⟩ := level_list_struct_eq_exact (rls.mono ext123) (rus.mono ext123) ev4
  subst hm hx hy
  refine ⟨ext123, ?_⟩
  rw [mul_ite_eq_one op, hyeq]

section Run

variable {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}

/-- **The test the walk computes for one recursor** (`is_match`), on a recursor's loaded payload
whose type is represented exactly against a represented entry: it is `1` exactly when the major
premise's type passes `PeerMatch`. -/
theorem peer_match_spec (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {ty : KExpr} {np nmot nmin ni : Nat}
    (hN : np + nmot + nmin + ni < 288230376151711744)
    {e : FlatEntry} {ta : Bytes.Address} (hta : ixAddr ta = e.addr)
    {x_ty w0 w1 w2 w3 w4 w5 xwrap xm xrest xall xcur xrb x_ta x_sp x_us xself xpos res :
      SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hty : TmOExact (keyOf t) h ty x_ty) (rta : Bytes.RepAddressRef addrTy h ta x_ta)
    (rsp : RepList kexprListEnum (TmOExact (keyOf t)) h e.params x_sp)
    (rus : RepKLevelList h e.levels x_us)
    (sg : Obs.«KernelCheck::find_peer_rec_spec_walk».Seg1
      (.construct "KernelTypes::KConstantInfo" "Rec"
        [w0, x_ty, .field (np : F), .field (ni : F), .field (nmot : F), .field (nmin : F),
          w1, w2, w3, w4, w5])
      xwrap xm xrest xall xcur xrb x_ta x_sp x_us (auxVal e.aux) xself xpos h res h' cs)
    (hsub : ∀ c ∈ cs, c ∈ calls) :
    Heap.Extends h h' ∧ ∃ d, binderDomAfter (np + nmot + nmin + ni) ty = some d ∧
      (res = .field 1 ↔ PeerMatch t E₀ (nmot + nmin + ni) d e) := by
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  have hinj := keyOf_injective' htwf
  have bsub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → Bounded cs' :=
    fun hs => RomBound.bounded_mono hbd fun c hc => hsub c (hs c hc)
  have h0 : (.field 0 : SourceValue F) = .field ((0 : Nat) : F) := by simp
  match sg with
  | .other (hne672 := hne) .. => exact (hne _ rfl rfl).elim
  | .Rec_Induct_n1_n0 (cs271 := cs271) (hv140 := hv) (ev216 := evP) (ev273 := evG) (ld267 := ld)
      (ev367 := evA) (hv411 := hax) (he412 := hr) (he413 := hh) (hc414 := hc) .. =>
    have hargs := (Value.construct.inj hv).2.2
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl, -⟩ := hargs
    obtain ⟨ext1, xmaj, xls, hM⟩ := rec_to_parent_addr_major hN evP
    obtain ⟨d, a, ls, As, hdom, hdeq, -, ra, rls⟩ := hM.sem (hty.mono ext1)
    have ext2 := evG.heap_extends
    obtain ⟨hv1, hm⟩ := Lib.address_eq_spec evA (Bytes.repAddressRef_heapMono₂ addrTy ext2 ra)
      (Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans ext2) rta)
    have hat : a = ta := by
      by_contra hna
      rw [ite_eq_right hna] at hv1
      exact absurd (Value.field.inj hv1) (by decide)
    subst hm hh
    refine ⟨ext1.trans ext2, d, hdom, ?_⟩
    rw [hr, peerMatch_mkAppN htwf hdeq]
    exact ⟨fun _ => ⟨by rw [hat, hta], fun hx => by
      rw [auxVal_eq_zero.mp hax] at hx; cases hx⟩, fun _ => rfl⟩
  | .Rec_Induct_n1_other (cs271 := cs271) (cs430 := cs430) (cs_hhuvezky := csZ) (hv140 := hv)
      (ev216 := evP) (ev273 := evG) (ld267 := ld) (ev367 := evA) (hne415 := hnax)
      (ev432 := evX) (ev_ixrbdajz := evZ) (ev_zxqvbypw := evO) (ev_vyjmrjll := evL)
      (op_asvnvwhr := op) (hc503 := hc) .. =>
    have hargs := (Value.construct.inj hv).2.2
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl, -⟩ := hargs
    obtain ⟨ext1, xmaj, xls, hM⟩ := rec_to_parent_addr_major hN evP
    obtain ⟨d, a, ls, As, hdom, hdeq, -, ra, rls⟩ := hM.sem (hty.mono ext1)
    have hsubG : ∀ c ∈ cs271, c ∈ calls := fun c hc' => hsub c (by rw [hc]; simp [hc'])
    obtain ⟨i, ba, hinfo, hnl, hnpb, e1, e3, hba, rba⟩ :=
      (indInfo_of_load hS hH hbd ra evG hsubG ld).1 _ _ _ _ _ _ _ _ rfl
    subst e3
    have ext2 := evG.heap_extends
    obtain ⟨hv1, hm⟩ := Lib.address_eq_spec evA (Bytes.repAddressRef_heapMono₂ addrTy ext2 ra)
      (Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans ext2) rta)
    have hat : a = ta := by
      by_contra hna
      rw [ite_eq_right hna] at hv1
      exact absurd (Value.field.inj hv1) (by decide)
    subst hm
    have haux : e.aux = true := by
      cases hx : e.aux with
      | true => rfl
      | false => exact (hnax (auxVal_eq_zero.mpr hx)).elim
    have ext12 := ext1.trans ext2
    obtain ⟨ext3, hiff⟩ := aux_factors (root := calls) hinj hN (by omega) (hM.mono ext2)
      (hty.mono ext12) hdom (rls.mono ext2) (tmOExactList_mono ext12 rsp) (rus.mono ext12)
      evX evZ evO evL op (bsub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      (bsub fun c hc' => by rw [hc]; simp [hc'])
    have hargsd : Ix.Kernel.Expr.getAppArgs d = As := by
      rw [hdeq, IxVM.Refinement.Decl.getAppArgs_mkAppN]
      rfl
    have hnp : parentNp E₀ (ixAddr a) = i.np := by simp only [parentNp, hinfo]
    refine ⟨ext12.trans ext3, d, hdom, ?_⟩
    rw [hiff, peerMatch_mkAppN htwf hdeq, hargsd, hnp]
    exact ⟨fun hx => ⟨by rw [hat, hta], fun _ => hx⟩, fun hx => hx.2 haux⟩
  | .Rec_Induct_other (hv140 := hv) (ev216 := evP) (ev273 := evG) (ld267 := ld)
      (ev367 := evA) (hne504 := hne) (he508 := hr) (he509 := hh) (hc510 := hc) .. =>
    have hargs := (Value.construct.inj hv).2.2
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl, -⟩ := hargs
    obtain ⟨ext1, xmaj, xls, hM⟩ := rec_to_parent_addr_major hN evP
    obtain ⟨d, a, ls, As, hdom, hdeq, -, ra, rls⟩ := hM.sem (hty.mono ext1)
    have ext2 := evG.heap_extends
    obtain ⟨hv1, hm⟩ := Lib.address_eq_spec evA (Bytes.repAddressRef_heapMono₂ addrTy ext2 ra)
      (Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans ext2) rta)
    have hat : a ≠ ta := by
      intro heq
      rw [ite_eq_left heq] at hv1
      exact hne hv1
    subst hm hh
    refine ⟨ext1.trans ext2, d, hdom, ?_⟩
    rw [hr, peerMatch_mkAppN htwf hdeq]
    exact ⟨fun hx => absurd (Value.field.inj hx) (by decide),
      fun hx => (hat (ixAddr_inj (hx.1.trans hta.symm))).elim⟩
  | .Rec_other_n1_n0 (hv140 := hv) (ev216 := evP) (ev273 := evG) (ld267 := ld)
      (ev528 := evA) (hv572 := hax) (he573 := hr) (he574 := hh) (hc575 := hc) .. =>
    have hargs := (Value.construct.inj hv).2.2
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl, -⟩ := hargs
    obtain ⟨ext1, xmaj, xls, hM⟩ := rec_to_parent_addr_major hN evP
    obtain ⟨d, a, ls, As, hdom, hdeq, -, ra, rls⟩ := hM.sem (hty.mono ext1)
    have ext2 := evG.heap_extends
    obtain ⟨hv1, hm⟩ := Lib.address_eq_spec evA (Bytes.repAddressRef_heapMono₂ addrTy ext2 ra)
      (Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans ext2) rta)
    have hat : a = ta := by
      by_contra hna
      rw [ite_eq_right hna] at hv1
      exact absurd (Value.field.inj hv1) (by decide)
    subst hm hh
    refine ⟨ext1.trans ext2, d, hdom, ?_⟩
    rw [hr, peerMatch_mkAppN htwf hdeq]
    exact ⟨fun _ => ⟨by rw [hat, hta], fun hx => by
      rw [auxVal_eq_zero.mp hax] at hx; cases hx⟩, fun _ => rfl⟩
  | .Rec_other_n1_other (cs271 := cs271) (hv140 := hv) (ev216 := evP) (ev273 := evG)
      (ld267 := ld) (hne511 := hnI) (ev528 := evA) (hne576 := hnax) (ev593 := evX)
      (ev_isvacogw := evZ) (ev_svabrqkr := evO) (ev_qskuhyzy := evL) (op_dmwxqesc := op)
      (hc664 := hc) .. =>
    have hargs := (Value.construct.inj hv).2.2
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl, -⟩ := hargs
    obtain ⟨ext1, xmaj, xls, hM⟩ := rec_to_parent_addr_major hN evP
    obtain ⟨d, a, ls, As, hdom, hdeq, -, ra, rls⟩ := hM.sem (hty.mono ext1)
    have hsubG : ∀ c ∈ cs271, c ∈ calls := fun c hc' => hsub c (by rw [hc]; simp [hc'])
    have hinfo := (indInfo_of_load hS hH hbd ra evG hsubG ld).2 hnI
    have ext2 := evG.heap_extends
    obtain ⟨hv1, hm⟩ := Lib.address_eq_spec evA (Bytes.repAddressRef_heapMono₂ addrTy ext2 ra)
      (Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans ext2) rta)
    have hat : a = ta := by
      by_contra hna
      rw [ite_eq_right hna] at hv1
      exact absurd (Value.field.inj hv1) (by decide)
    subst hm
    have haux : e.aux = true := by
      cases hx : e.aux with
      | true => rfl
      | false => exact (hnax (auxVal_eq_zero.mpr hx)).elim
    have ext12 := ext1.trans ext2
    rw [h0] at evX
    obtain ⟨ext3, hiff⟩ := aux_factors (root := calls) hinj hN (by omega) (hM.mono ext2)
      (hty.mono ext12) hdom (rls.mono ext2) (tmOExactList_mono ext12 rsp) (rus.mono ext12)
      evX evZ evO evL op (bsub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      (bsub fun c hc' => by rw [hc]; simp [hc'])
    have hargsd : Ix.Kernel.Expr.getAppArgs d = As := by
      rw [hdeq, IxVM.Refinement.Decl.getAppArgs_mkAppN]
      rfl
    have hnp : parentNp E₀ (ixAddr a) = 0 := by simp only [parentNp, hinfo]
    refine ⟨ext12.trans ext3, d, hdom, ?_⟩
    rw [hiff, peerMatch_mkAppN htwf hdeq, hargsd, hnp]
    exact ⟨fun hx => ⟨by rw [hat, hta], fun _ => hx⟩, fun hx => hx.2 haux⟩
  | .Rec_other_other (hv140 := hv) (ev216 := evP) (ev273 := evG) (ld267 := ld)
      (ev528 := evA) (hne665 := hne) (he669 := hr) (he670 := hh) (hc671 := hc) .. =>
    have hargs := (Value.construct.inj hv).2.2
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl, -⟩ := hargs
    obtain ⟨ext1, xmaj, xls, hM⟩ := rec_to_parent_addr_major hN evP
    obtain ⟨d, a, ls, As, hdom, hdeq, -, ra, rls⟩ := hM.sem (hty.mono ext1)
    have ext2 := evG.heap_extends
    obtain ⟨hv1, hm⟩ := Lib.address_eq_spec evA (Bytes.repAddressRef_heapMono₂ addrTy ext2 ra)
      (Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans ext2) rta)
    have hat : a ≠ ta := by
      intro heq
      rw [ite_eq_left heq] at hv1
      exact hne hv1
    subst hm hh
    refine ⟨ext1.trans ext2, d, hdom, ?_⟩
    rw [hr, peerMatch_mkAppN htwf hdeq]
    exact ⟨fun hx => absurd (Value.field.inj hx) (by decide),
      fun hx => (hat (ixAddr_inj (hx.1.trans hta.symm))).elim⟩

/-! ## The walk over the record's recursors -/

/-- **The projection address of a recursor of the record and its load**: the address is the
recursor's constant address, the payload a `Rec` with the recursor's counts, its type pointer
representing the canonical reading exactly. -/
theorem recLoad_prefix_addr (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hR : FamRecRecord E₀ rb crb rs) (hlv : RecLevelsDefined t E₀ rb crb rs)
    (hrs_lt : rs.size < 8589934592) {bR : Bytes.Address} (hbR : ixAddr bR = rb)
    {k : Nat} {rc : Ixon.Recursor} (hrk : rs[k]? = some (.recr rc))
    {x_all x_rb v63 p109 v101 : SourceValue F}
    {h m64 m102 : Heap F} {cs74 cs115 : List (Call F)}
    (hall : RepList L1.mutConstListEnum L1.RepMutConst h rs.toList x_all)
    (hrb : Bytes.RepAddressRef addrTy h bR x_rb)
    (ev76 : ObsFn W "Ingress::projection_addr" [x_all, x_rb, .field (k : F)] h v63 m64 cs74)
    (ev117 : ObsFn W "Ingress::get_ci" [v63] m64 p109 m102 cs115)
    (ld111 : loadValue m102 p109 = .ok v101)
    (hsub115 : ∀ c ∈ cs115, c ∈ calls) :
    Heap.Extends h m102 ∧
    ∃ (ty : KExpr) (x_ty w0 w1 w2 w3 w4 w5 : SourceValue F) (aW : Bytes.Address),
      v101 = .construct "KernelTypes::KConstantInfo" "Rec"
        [w0, x_ty, .field (rc.params.toNat : F), .field (rc.indices.toNat : F),
          .field (rc.motives.toNat : F), .field (rc.minors.toNat : F), w1, w2, w3, w4, w5] ∧
      loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
        (mutsRoot rs k) rc.typ = some ty ∧
      TmOExact (keyOf t) m102 ty x_ty ∧
      rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat <
        288230376151711744 ∧
      Bytes.RepAddressRef addrTy m102 aW v63 ∧
      ixAddr aW = IxVM.Refinement.Core.rprjAddr rb k := by
  have hklt : k < rs.size := (Array.getElem?_eq_some_iff.mp hrk).1
  have hkval : ((k : F)).val = k := FamilyOfCall.val_cast_lt_u58 (by omega)
  obtain ⟨ext1, -, -, mc, aW, hget, haW, haW_eq⟩ :=
    L1.projection_addr_spec (Route.membersRep_of_repMutConstList hall) hrb ev76
  rw [hkval, Array.getElem?_toList, hrk] at hget
  have hmc : mc = .recr rc := (Option.some.inj hget).symm
  subst hmc
  rw [hkval, hbR, ← LoadedReads.memberAddr_eq_projAddr, LoadedReads.memberAddr_recr] at haW_eq
  obtain ⟨ty, x_ty, w1, w2, w3, w4, w5, hci, hloaded, htm, hnp, hni, hnmot, hnmin⟩ :=
    recMember_load ht hbd hS hR hlv (Nat.lt_trans hklt (Nat.lt_trans hrs_lt (by decide))) hrk
      haW_eq haW ev117 hsub115 ld111
  exact ⟨ext1.trans ev117.heap_extends, ty, x_ty, _, w1, w2, w3, w4, w5, aW, hci, hloaded, htm,
    by omega, Bytes.repAddressRef_heapMono₂ addrTy ev117.heap_extends haW, haW_eq⟩

/-- **`KernelCheck::find_peer_rec_spec_walk`** over the recursors of a family record from
position `pos`, against a represented entry that recursor `k ≥ pos` matches and no recursor
before `k` does: it returns recursor `k`'s projection address. -/
theorem find_peer_rec_spec_walk_spec (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hR : FamRecRecord E₀ rb crb rs) (hlv : RecLevelsDefined t E₀ rb crb rs)
    (hrs_lt : rs.size < 8589934592) {bR : Bytes.Address} (hbR : ixAddr bR = rb)
    {e : FlatEntry} {k : Nat} (hk : MatchAt t E₀ rb crb rs k e)
    (hfirst : ∀ j, j < k → ¬ MatchAt t E₀ rb crb rs j e)
    {ta : Bytes.Address} (hta : ixAddr ta = e.addr)
    {x_all x_rb x_ta x_sp x_us x_self : SourceValue F} :
    ∀ (cur : List Ixon.MutConst) (pos : Nat) {x_cur r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      cur = rs.toList.drop pos → pos ≤ k →
      RepList L1.mutConstListEnum L1.RepMutConst h rs.toList x_all →
      RepList L1.mutConstListEnum L1.RepMutConst h cur x_cur →
      Bytes.RepAddressRef addrTy h bR x_rb → Bytes.RepAddressRef addrTy h ta x_ta →
      RepList kexprListEnum (TmOExact (keyOf t)) h e.params x_sp →
      RepKLevelList h e.levels x_us →
      ObsFn W "KernelCheck::find_peer_rec_spec_walk"
        [x_all, x_cur, x_rb, x_ta, x_sp, x_us, auxVal e.aux, x_self, .field (pos : F)]
        h r h' cs →
      (∀ c ∈ cs, c ∈ calls) →
      Heap.Extends h h' ∧ ∃ a : Bytes.Address, Bytes.RepAddressRef addrTy h' a r ∧
        ixAddr a = IxVM.Refinement.Core.rprjAddr rb k := by
  have hklt : k < rs.size := by
    obtain ⟨rc, ty, d, hrk, -⟩ := hk
    exact (Array.getElem?_eq_some_iff.mp hrk).1
  intro cur
  induction cur with
  | nil =>
    intro pos x_cur r h h' cs hcur hpos
    have hle := List.drop_eq_nil_iff.mp hcur.symm
    rw [Array.length_toList] at hle
    omega
  | cons m rest ih =>
    intro pos x_cur r h h' cs hcur hpos hall hcurR hrb rta rsp rus ev hsub
    have hm0 : rs[pos]? = some m := by
      have h1 : (rs.toList.drop pos)[0]? = some m := by rw [← hcur]; rfl
      rw [List.getElem?_drop, Nat.add_zero, Array.getElem?_toList] at h1
      exact h1
    have hrestE : rest = rs.toList.drop (pos + 1) := by
      have h1 := congrArg List.tail hcur
      rw [List.tail_drop] at h1
      exact h1
    obtain ⟨rc, rfl⟩ :=
      hR.recrs m (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hm0))
    match Obs.«KernelCheck::find_peer_rec_spec_walk».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hcurR ld
    | .Cons_other (ld12 := ld) (hne789 := hne) .. =>
      obtain ⟨m', rest', he, hm, hrestR⟩ := Lib.rep_cons_of_load hcurR ld
      injection he with h1 h2
      subst h1 h2
      obtain ⟨rv, hrv, -⟩ := hm
      exact absurd hrv (hne [rv] rfl)
    | .Cons_Recr_n1 (cs115 := cs115) (cs682 := cs682) (ld12 := ld) (ev76 := ev76)
        (ev117 := ev117) (ld111 := ld111) (sg687 := sg) (he703 := hr) (he704 := hh)
        (hc705 := hc) .. =>
      obtain ⟨ext, ty, x_ty, w0, w1, w2, w3, w4, w5, aW, hci, hloaded, htm, hN, haW, haW_eq⟩ :=
        recLoad_prefix_addr ht hbd hS hR hlv hrs_lt hbR hm0 hall hrb ev76 ev117 ld111
          (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      subst hci
      obtain ⟨ext2, d, hdom, hiff⟩ := peer_match_spec ht hbd hS hH hN hta htm
        (Bytes.repAddressRef_heapMono₂ addrTy ext rta) (tmOExactList_mono ext rsp)
        (rus.mono ext) sg (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      have hmatch : MatchAt t E₀ rb crb rs pos e :=
        ⟨rc, ty, d, hm0, hloaded, hdom, hiff.mp rfl⟩
      have hpk : pos = k := by
        by_contra hne
        exact hfirst pos (by omega) hmatch
      rw [hr, hh]
      exact ⟨ext.trans ext2, aW, Bytes.repAddressRef_heapMono₂ addrTy ext2 haW,
        by rw [← hpk]; exact haW_eq⟩
    | .Cons_Recr_other (cs115 := cs115) (cs682 := cs682) (cs713 := cs713) (ld12 := ld)
        (ev76 := ev76) (ev117 := ev117) (ld111 := ld111) (sg687 := sg) (hne706 := hne1)
        (op_ojlhvlfm := op) (ev715 := evR) (hc788 := hc) .. =>
      obtain ⟨m', rest', he, hm, hrestR⟩ := Lib.rep_cons_of_load hcurR ld
      injection he with h1 h2
      subst h1 h2
      obtain ⟨ext, ty, x_ty, w0, w1, w2, w3, w4, w5, aW, hci, hloaded, htm, hN, haW, haW_eq⟩ :=
        recLoad_prefix_addr ht hbd hS hR hlv hrs_lt hbR hm0 hall hrb ev76 ev117 ld111
          (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      subst hci
      obtain ⟨ext2, d, hdom, hiff⟩ := peer_match_spec ht hbd hS hH hN hta htm
        (Bytes.repAddressRef_heapMono₂ addrTy ext rta) (tmOExactList_mono ext rsp)
        (rus.mono ext) sg (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      have hpk : pos ≠ k := by
        intro hpk
        obtain ⟨rc', ty', d', hrk', hl', hd', hpm'⟩ := hk
        rw [← hpk, hm0] at hrk'
        have hrc : rc = rc' := Ixon.MutConst.recr.inj (Option.some.inj hrk')
        subst hrc
        rw [← hpk, hloaded] at hl'
        have hty : ty = ty' := Option.some.inj hl'
        subst hty
        rw [hdom] at hd'
        have hdd : d = d' := Option.some.inj hd'
        subst hdd
        exact hne1 (hiff.mpr hpm')
      obtain rfl := binop_add_one_nat op
      have extA := ext.trans ext2
      obtain ⟨ext', res⟩ := ih (pos + 1) hrestE (by omega)
        (RepLinkedList.mono L1.repMutConst_heapMono₂ extA hall)
        (RepLinkedList.mono L1.repMutConst_heapMono₂ extA hrestR)
        (Bytes.repAddressRef_heapMono₂ addrTy extA hrb)
        (Bytes.repAddressRef_heapMono₂ addrTy extA rta) (tmOExactList_mono extA rsp)
        (rus.mono extA) evR (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      exact ⟨extA.trans ext', res⟩

/-- **`KernelCheck::find_peer_recursor_with_spec`** on a family record, against a represented
entry that recursor `k` matches and no recursor before `k` does: recursor `k`'s projection
address. -/
theorem find_peer_recursor_with_spec_spec (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hR : FamRecRecord E₀ rb crb rs) (hlv : RecLevelsDefined t E₀ rb crb rs)
    {bR : Bytes.Address} (hbR : ixAddr bR = rb)
    {e : FlatEntry} {k : Nat} (hk : MatchAt t E₀ rb crb rs k e)
    (hfirst : ∀ j, j < k → ¬ MatchAt t E₀ rb crb rs j e)
    {ta : Bytes.Address} (hta : ixAddr ta = e.addr)
    {x_rb x_ta x_sp x_us x_self r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrb : Bytes.RepAddressRef addrTy h bR x_rb) (rta : Bytes.RepAddressRef addrTy h ta x_ta)
    (rsp : RepList kexprListEnum (TmOExact (keyOf t)) h e.params x_sp)
    (rus : RepKLevelList h e.levels x_us)
    (ev : ObsFn W "KernelCheck::find_peer_recursor_with_spec"
      [x_rb, x_ta, x_sp, x_us, auxVal e.aux, x_self] h r h' cs)
    (hsub : ∀ c ∈ cs, c ∈ calls) :
    Heap.Extends h h' ∧ ∃ a : Bytes.Address, Bytes.RepAddressRef addrTy h' a r ∧
      ixAddr a = IxVM.Refinement.Core.rprjAddr rb k := by
  have hrec : recordOf E₀ (ixAddr bR) = some crb := by rw [hbR]; exact hR.record
  match Obs.«KernelCheck::find_peer_recursor_with_spec».obs ev with
  | .Muts (cs12 := csL) (cs92 := csW) (ev14 := evL) (ev94 := evW) (hc158 := hc) .. =>
    obtain ⟨msPtr, hxm, hlist, hlt⟩ := Decl.load_block_info hS hrb evL
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hrec hR.muts
    have hxe := (List.cons.inj (Value.construct.inj hxm).2.2).1
    subst hxe
    have extL := evL.heap_extends
    obtain ⟨ext, res⟩ := find_peer_rec_spec_walk_spec ht hbd hS hH hR hlv hlt hbR hk hfirst hta
      rs.toList 0 (by simp) (Nat.zero_le _) hlist hlist
      (Bytes.repAddressRef_heapMono₂ addrTy extL hrb)
      (Bytes.repAddressRef_heapMono₂ addrTy extL rta) (tmOExactList_mono extL rsp)
      (rus.mono extL) (by simpa using evW) (fun c hc' => hsub c (by rw [hc]; simp [hc']))
    exact ⟨extL.trans ext, res⟩
  | .other (cs12 := csL) (ev14 := evL) (hne159 := hne) (hc166 := hc) .. =>
    obtain ⟨msPtr, hxm, -, -⟩ := Decl.load_block_info hS hrb evL
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hrec hR.muts
    exact absurd hxm (hne [msPtr] rfl)

end Run

/-! ## The first recursor matching an entry is the entry's own -/

section Model

variable {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {rb : _root_.Address} {crb : Ixon.Constant}
  {rs : Array Ixon.MutConst} {es : List FlatEntry}

/-- **Recursor `k` matches entry `k`.** -/
theorem matchAt_own (hflat : RecordFlat t E rb crb rs es) (hown : AuxParamsOwn E es)
    {k : Nat} {rc : Ixon.Recursor} {e : FlatEntry} (hrk : rs[k]? = some (.recr rc))
    (hek : es[k]? = some e) : MatchAt t E rb crb rs k e := by
  obtain ⟨ty, d, hl, hd, hfn, haux⟩ := hflat k rc e hrk hek
  refine ⟨rc, ty, d, hrk, hl, hd, e.levels, hfn, fun hx => ⟨?_, rfl⟩⟩
  rw [hown e (List.mem_of_getElem? hek) hx]
  exact haux hx

/-- **A recursor matching an entry is over an entry at its address**, and, the two auxiliaries,
with its parameters and levels. -/
theorem matchAt_sound (htwf : t.wf = true) (hflat : RecordFlat t E rb crb rs es)
    (hown : AuxParamsOwn E es) {j : Nat} {e ej : FlatEntry} (hej : es[j]? = some ej)
    (hm : MatchAt t E rb crb rs j e) :
    ej.addr = e.addr ∧
      (e.aux = true → ej.aux = true → ej.params = e.params ∧ ej.levels = e.levels) := by
  obtain ⟨rc, ty, d, hrk, hl, hd, ls, hfn, haux⟩ := hm
  obtain ⟨ty', d', hl', hd', hfn', haux'⟩ := hflat j rc ej hrk hej
  rw [hl] at hl'
  have hty : ty = ty' := Option.some.inj hl'
  subst hty
  rw [hd] at hd'
  have hdd : d = d' := Option.some.inj hd'
  subst hdd
  rw [hfn] at hfn'
  injection hfn' with hkk hll
  have ha : e.addr = ej.addr := IxVM.Refinement.Core.keyOf_inj htwf hkk
  refine ⟨ha.symm, fun hx hy => ?_⟩
  obtain ⟨hp, hlv⟩ := haux hx
  have hp' := haux' hy
  rw [← hown ej (List.mem_of_getElem? hej) hy, ← ha] at hp'
  exact ⟨hp'.symm.trans hp, by rw [← hll, hlv]⟩

/-- **No recursor before `k` matches entry `k`** of a family of different entries
(`FlatDistinct.no_earlier_match` at the search's test). -/
theorem matchAt_first (htwf : t.wf = true) (hflat : RecordFlat t E rb crb rs es)
    (hown : AuxParamsOwn E es) (hd : FlatDistinct es) {k : Nat} {e : FlatEntry}
    (hek : es[k]? = some e) (j : Nat) (hj : j < k) : ¬ MatchAt t E rb crb rs j e := by
  classical
  intro hm
  have hf := hd.no_earlier_match (p := fun j e' => decide (MatchAt t E rb crb rs j e'))
    (fun j e' ej hej hp => matchAt_sound htwf hflat hown hej (of_decide_eq_true hp)) hek j hj
  exact of_decide_eq_false hf hm

/-- **The record's member addresses are its recursors' projection addresses**, in order. -/
theorem recAddrs_eq_range (hR : FamRecRecord E rb crb rs) :
    recAddrs rb rs = (List.range rs.size).map (IxVM.Refinement.Core.rprjAddr rb) := by
  apply List.ext_getElem?
  intro i
  unfold recAddrs
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_zipIdx]
  by_cases hi : i < rs.size
  · have hm : rs.toList[i]? = some rs[i] := by
      rw [Array.getElem?_toList]; exact Array.getElem?_eq_getElem hi
    obtain ⟨rc, hrc⟩ := hR.recrs rs[i] (List.mem_of_getElem? hm)
    rw [hm, hrc, List.getElem?_range hi]
    simp [LoadedReads.memberAddr_recr]
  · have hm : rs.toList[i]? = none := by
      rw [Array.getElem?_toList]; exact Array.getElem?_eq_none (by omega)
    have hr : (List.range rs.size)[i]? = none :=
      List.getElem?_eq_none (by rw [List.length_range]; omega)
    rw [hm, hr]
    rfl

end Model

/-! ## The parameter count of an auxiliary entry, from the derivation -/

section Thread

variable {V : FlatView} {B : _root_.Address} {I : List FlatEntry → Prop}

/-- `FamilyFlat.appCase` keeps a property of the entries that every nested occurrence keeps, the
occurrence's head an inductive type of another block read at some address, its parameters as
many as the head declares. -/
theorem appCase_inv_head
    (hstep : ∀ (ca : _root_.Address) (i : IndInfo) ms sp us acc, V.ci ca = some (some i) →
      (i.blk == B) = false → V.members i.blk = some ms → sp.length = i.np → I acc →
      I (addBlockMembers ms sp us acc))
    {rec : KExpr → Nat → List FlatEntry → Option (List FlatEntry)}
    (hr : ∀ e d acc r, I acc → rec e d acc = some r → I r)
    {hd : KExpr} {args : List KExpr} {d : Nat} {acc r : List FlatEntry} (hacc : I acc)
    (h : appCase rec V B hd args d acc = some r) : I r := by
  have hs : ∀ acc r, I acc → scanList (fun x acc => rec x d acc) args acc = some r → I r :=
    fun acc r => scanList_inv (fun x acc r => hr x d acc r) args acc r
  unfold appCase at h
  cases hk : constOf hd with
  | none =>
    simp only [hk] at h
    cases h1 : rec hd d acc with
    | none => simp [h1] at h
    | some a =>
      simp only [h1] at h
      exact hs a r (hr hd d acc a hacc h1) h
  | some p =>
    obtain ⟨c, us⟩ := p
    simp only [hk] at h
    cases ha : V.addr c with
    | none => simp [ha] at h
    | some ca =>
      simp only [ha] at h
      cases hc : V.ci ca with
      | none => simp [hc] at h
      | some x =>
        cases x with
        | none =>
          simp only [hc] at h
          exact hs acc r hacc h
        | some i =>
          simp only [hc] at h
          cases hn : nestedAt V B i args with
          | none => simp [hn] at h
          | some b =>
            cases b with
            | false =>
              simp only [hn] at h
              exact hs acc r hacc h
            | true =>
              simp only [hn] at h
              cases hm : V.members i.blk with
              | none => simp [hm] at h
              | some ms =>
                simp only [hm] at h
                cases hl : occParamsLower (args.take i.np) d with
                | none => simp [hl] at h
                | some sp =>
                  simp only [hl, Option.some.injEq] at h
                  subst h
                  have hb : (i.blk == B) = false ∧ ¬ args.length < i.np := by
                    unfold nestedAt at hn
                    cases hbb : (i.blk == B || decide (args.length < i.np)) with
                    | true => simp [hbb] at hn
                    | false =>
                      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hbb
                      exact hbb
                  have hlen : sp.length = i.np := by
                    rw [occParamsLower_eq _ _ _ hl, List.length_map, List.length_take]
                    omega
                  exact hstep ca i ms sp us acc hc hb.1 hm hlen hacc

theorem occScanF_inv_head
    (hstep : ∀ (ca : _root_.Address) (i : IndInfo) ms sp us acc, V.ci ca = some (some i) →
      (i.blk == B) = false → V.members i.blk = some ms → sp.length = i.np → I acc →
      I (addBlockMembers ms sp us acc)) :
    ∀ (n : Nat) (e : KExpr) (d : Nat) (acc r : List FlatEntry), I acc →
      occScanF V B n e d acc = some r → I r := by
  intro n
  induction n with
  | zero => intro e d acc r _ h; simp [occScanF] at h
  | succ n ih =>
    intro e d acc r hacc h
    simp only [occScanF] at h
    cases hm : mentions V B e with
    | none => simp [hm] at h
    | some b =>
      cases b with
      | false =>
        simp only [hm, Option.some.injEq] at h
        subst h; exact hacc
      | true =>
        simp only [hm] at h
        cases e with
        | app f a =>
          simp only at h
          exact appCase_inv_head hstep ih hacc h
        | lam t b m =>
          simp only at h
          cases h1 : occScanF V B n t d acc with
          | none => simp [h1] at h
          | some a1 =>
            simp only [h1] at h
            exact ih b (d + 1) a1 r (ih t d acc a1 hacc h1) h
        | forallE t b m =>
          simp only at h
          cases h1 : occScanF V B n t d acc with
          | none => simp [h1] at h
          | some a1 =>
            simp only [h1] at h
            exact ih b (d + 1) a1 r (ih t d acc a1 hacc h1) h
        | letE t v b l =>
          simp only at h
          cases h1 : occScanF V B n t d acc with
          | none => simp [h1] at h
          | some a1 =>
            simp only [h1] at h
            cases h2 : occScanF V B n v d a1 with
            | none => simp [h2] at h
            | some a2 =>
              simp only [h2] at h
              exact ih b (d + 1) a2 r (ih v d a1 a2 (ih t d acc a1 hacc h1) h2) h
        | proj s i x =>
          simp only at h
          exact ih x d acc r hacc h
        | bvar _ => simp only [Option.some.injEq] at h; subst h; exact hacc
        | fvar _ _ => simp only [Option.some.injEq] at h; subst h; exact hacc
        | sort _ => simp only [Option.some.injEq] at h; subst h; exact hacc
        | const _ _ => simp only [Option.some.injEq] at h; subst h; exact hacc
        | lit _ => simp only [Option.some.injEq] at h; subst h; exact hacc

theorem ctorsLoop_inv_head
    (hstep : ∀ (ca : _root_.Address) (i : IndInfo) ms sp us acc, V.ci ca = some (some i) →
      (i.blk == B) = false → V.members i.blk = some ms → sp.length = i.np → I acc →
      I (addBlockMembers ms sp us acc))
    (i : IndInfo) (aux : Bool) (sp : List KExpr) (us : List KLevel) :
    ∀ (cs : List Nat) (acc r : List FlatEntry), I acc →
      ctorsLoop V B i aux sp us cs acc = some r → I r := by
  intro cs
  induction cs with
  | nil =>
    intro acc r hacc h
    simp only [ctorsLoop, Option.some.injEq] at h
    subst h; exact hacc
  | cons c cs ih =>
    intro acc r hacc h
    simp only [ctorsLoop] at h
    cases h1 : ctorScan V B i aux sp us acc c with
    | none => simp [h1] at h
    | some a =>
      simp only [h1] at h
      refine ih a r ?_ h
      unfold ctorScan at h1
      cases hc : V.ctorType i.blk i.idx c with
      | none => simp [hc] at h1
      | some cty =>
        simp only [hc] at h1
        cases hb : ctorBody aux i.np sp (exprInstLevels us cty) with
        | none => simp [hb] at h1
        | some body =>
          simp only [hb] at h1
          exact occScanF_inv_head hstep _ body 0 acc a hacc h1

theorem nestedWalk_inv_head
    (hstep : ∀ (ca : _root_.Address) (i : IndInfo) ms sp us acc, V.ci ca = some (some i) →
      (i.blk == B) = false → V.members i.blk = some ms → sp.length = i.np → I acc →
      I (addBlockMembers ms sp us acc)) :
    ∀ (n i : Nat) (acc r : List FlatEntry), I acc → nestedWalk V B n i acc = some r → I r := by
  intro n
  induction n with
  | zero => intro i acc r _ h; simp [nestedWalk] at h
  | succ n ih =>
    intro i acc r hacc h
    simp only [nestedWalk] at h
    cases hi : acc[i]? with
    | none =>
      simp only [hi, Option.some.injEq] at h
      subst h; exact hacc
    | some e =>
      simp only [hi] at h
      cases hc : V.ci e.addr with
      | none => simp [hc] at h
      | some x =>
        cases x with
        | none => simp [hc] at h
        | some info =>
          simp only [hc] at h
          cases hs : ctorsScan V B info e.aux e.params e.levels acc with
          | none => simp [hs] at h
          | some a =>
            simp only [hs] at h
            exact ih (i + 1) a r
              (ctorsLoop_inv_head hstep info e.aux e.params e.levels _ acc a hacc hs) h

end Thread

/-- **The types of a nested block declare one parameter count**: every type a block other than
`B` lists reads, at its own address, the parameter count of any inductive type of that block the
store reads. The circuit asserts it of a block where it checks the block's types
(`KernelCheck::peer_agree_walk`, `KernelModeled::block_nparams`). -/
def NestedParamsAgree (E : Ixon.Env) (B : _root_.Address) : Prop :=
  ∀ (ca a : _root_.Address) (i : IndInfo) (ms : List _root_.Address),
    indInfoAt E ca = some (some i) → (i.blk == B) = false → membersAt E i.blk = some ms →
    a ∈ ms → parentNp E a = i.np

theorem addBlockMembers_own {E : Ixon.Env} {sp : List KExpr} {us : List KLevel} {np : Nat}
    (hsp : sp.length = np) :
    ∀ (ms : List _root_.Address) (acc : List FlatEntry), (∀ m ∈ ms, parentNp E m = np) →
      AuxParamsOwn E acc → AuxParamsOwn E (addBlockMembers ms sp us acc) := by
  intro ms
  induction ms with
  | nil => intro acc _ hacc; exact hacc
  | cons m ms ih =>
    intro acc hms hacc
    simp only [addBlockMembers]
    apply ih _ (fun m' hm' => hms m' (List.mem_cons_of_mem _ hm'))
    by_cases hin : auxEntryIn acc m sp us = true
    · rw [ite_eq_left hin]; exact hacc
    · rw [ite_eq_right hin]
      intro e he hx
      rcases List.mem_append.mp he with he | he
      · exact hacc e he hx
      · rw [List.mem_singleton] at he
        subst he
        rw [hms m List.mem_cons_self, hsp]

/-- **`AuxParamsOwn` of the flattened family derived from a block**, where the types of every
nested block declare one parameter count: the derivation gives each type of a nested occurrence's
block the occurrence's parameters, as many as the occurrence's head declares. -/
theorem auxParamsOwn_of_derived {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {B : _root_.Address}
    (hagree : NestedParamsAgree E B) {off n : Nat} {es : List FlatEntry}
    (h : derivedFlatAt (FlatView.ofStore t E) B off n = some es) : AuxParamsOwn E es := by
  unfold derivedFlatAt at h
  cases hm : (FlatView.ofStore t E).members B with
  | none => simp [hm] at h
  | some ms =>
    simp only [hm] at h
    cases ho : originals (FlatView.ofStore t E) off ms with
    | none => simp [ho] at h
    | some os =>
      simp only [ho] at h
      obtain ⟨-, hnaux⟩ := originals_shape ms os ho
      refine nestedWalk_inv_head (I := AuxParamsOwn E)
        (fun ca i msb sp us acc hci hb hmb hsp hacc =>
          addBlockMembers_own hsp msb acc (fun m hm' => hagree ca m i msb hci hb hmb hm') hacc)
        n 0 os es ?_ h
      intro e he hx
      rw [hnaux e he] at hx
      cases hx

/-- `AuxParamsOwn` of a family derived from a block (`BlockDerivedFlat`). -/
theorem auxParamsOwn_of_blockDerived {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {B : _root_.Address} (hagree : NestedParamsAgree E B) {off : Nat} {es : List FlatEntry}
    (h : BlockDerivedFlat t E B off es) : AuxParamsOwn E es := by
  obtain ⟨-, n, hn⟩ := h
  exact auxParamsOwn_of_derived hagree hn

/-- The parameter count read at an inductive type's address. -/
theorem parentNp_of_indInfo {E : Ixon.Env} {a : _root_.Address} {i : IndInfo}
    (h : indInfoAt E a = some (some i)) : parentNp E a = i.np := by
  simp only [parentNp, h]

/-! ## `build_peer_recs` -/

section Build

variable {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}

/-- **`KernelCheck::build_peer_recs`** over the entries of the flattened family from position
`k`: the projection addresses of the recursors from `k`. -/
theorem build_peer_recs_walk (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hR : FamRecRecord E₀ rb crb rs) (hlv : RecLevelsDefined t E₀ rb crb rs)
    {es : List FlatEntry} (hflat : RecordFlat t E₀ rb crb rs es) (hd : FlatDistinct es)
    (hown : AuxParamsOwn E₀ es) (hlen : es.length = rs.size)
    {bR : Bytes.Address} (hbR : ixAddr bR = rb) {x_rb x_self : SourceValue F} :
    ∀ (l : List FlatEntry) (k : Nat) {x_flat r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      l = es.drop k →
      RepList flatListEnum (FlatEntryRepExact (keyOf t)) h l x_flat →
      Bytes.RepAddressRef addrTy h bR x_rb →
      ObsFn W "KernelCheck::build_peer_recs" [x_flat, x_rb, x_self] h r h' cs →
      (∀ c ∈ cs, c ∈ calls) →
      Heap.Extends h h' ∧ ∃ as : List Bytes.Address,
        RepList IxVM.Refinement.Core.addrListEnum (Bytes.RepAddressRef addrTy) h' as r ∧
          as.map ixAddr = (List.range' k l.length).map (IxVM.Refinement.Core.rprjAddr rb) := by
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  intro l
  induction l with
  | nil =>
    intro k x_flat r h h' cs _ hes _ ev _
    match Obs.«KernelCheck::build_peer_recs».obs ev with
    | .Nil (he24 := hr) (hm23 := hh) .. =>
      rw [hr, hh]
      exact ⟨Heap.Extends.snoc _ _, [], Lib.rep_store_nil h, rfl⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hcons
  | cons e l ih =>
    intro k x_flat r h h' cs hl hes hrb ev hsub
    have hek : es[k]? = some e := by
      have h1 : (es.drop k)[0]? = some e := by rw [← hl]; rfl
      rw [List.getElem?_drop, Nat.add_zero] at h1
      exact h1
    have hlE : l = es.drop (k + 1) := by
      have h1 := congrArg List.tail hl
      rw [List.tail_drop] at h1
      exact h1
    have hklt : k < rs.size := by
      rw [← hlen]
      exact (List.getElem?_eq_some_iff.mp hek).1
    obtain ⟨rc, hrk⟩ : ∃ rc, rs[k]? = some (.recr rc) := by
      have hm : rs.toList[k]? = some rs[k] := by
        rw [Array.getElem?_toList]; exact Array.getElem?_eq_getElem hklt
      obtain ⟨rc, hrc⟩ := hR.recrs rs[k] (List.mem_of_getElem? hm)
      exact ⟨rc, by rw [Array.getElem?_eq_getElem hklt, hrc]⟩
    match Obs.«KernelCheck::build_peer_recs».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    | .Cons (m83 := m83) (m154 := m154) (ld12 := ld) (ev95 := evF) (he140 := hr) (hm139 := hh)
        (ev164 := evR) (hc189 := hc) .. =>
      obtain ⟨e', es', h1, he', hes'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with he1 hes1
      subst he1 hes1
      obtain ⟨xa, xps, xls, ae, htup, rae, hae, hsp, hou⟩ := he'
      injection htup with htl
      injection htl with h1 htl
      injection htl with h2 htl
      injection htl with h3 htl
      injection htl with h4
      subst h1 h2 h3 h4
      obtain ⟨ext1, a, ra, haeq⟩ := find_peer_recursor_with_spec_spec ht hbd hS hH hR hlv hbR
        (matchAt_own hflat hown hrk hek) (matchAt_first htwf hflat hown hd hek) hae hrb rae
        hsp hou evF (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      obtain ⟨ext2, as, has, hmap⟩ := ih (k + 1) hlE (flatList_mono ext1 hes')
        (Bytes.repAddressRef_heapMono₂ addrTy ext1 hrb) evR
        (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      rw [hr, hh]
      refine ⟨ext1.trans (ext2.trans (Heap.Extends.snoc _ _)), a :: as,
        Lib.rep_store_cons (Bytes.repAddressRef_heapMono₂ addrTy)
          (Bytes.repAddressRef_heapMono₂ addrTy ext2 ra) has, ?_⟩
      rw [List.length_cons, List.range'_succ, List.map_cons, List.map_cons, haeq, hmap]

/-- **`KernelCheck::build_peer_recs` on the flattened family of a family record** returns the
record's recursors in order (`FamilyRecon.recAddrs`), one for each entry: over entries that
differ (`FlatDistinct`), each with its recursor's major premise over it (`RecordFlat`) and, at an
auxiliary, with its type's own parameter count (`AuxParamsOwn`), the first recursor the search
finds for entry `k` is recursor `k`. -/
theorem build_peer_recs_spec (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hR : FamRecRecord E₀ rb crb rs) (hlv : RecLevelsDefined t E₀ rb crb rs)
    {es : List FlatEntry} (hflat : RecordFlat t E₀ rb crb rs es) (hd : FlatDistinct es)
    (hown : AuxParamsOwn E₀ es) (hlen : es.length = rs.size)
    {bR : Bytes.Address} (hbR : ixAddr bR = rb)
    {x_flat x_rb x_self r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hes : RepList flatListEnum (FlatEntryRepExact (keyOf t)) h es x_flat)
    (hrb : Bytes.RepAddressRef addrTy h bR x_rb)
    (ev : ObsFn W "KernelCheck::build_peer_recs" [x_flat, x_rb, x_self] h r h' cs)
    (hsub : ∀ c ∈ cs, c ∈ calls) :
    Heap.Extends h h' ∧ ∃ as : List Bytes.Address,
      RepList IxVM.Refinement.Core.addrListEnum (Bytes.RepAddressRef addrTy) h' as r ∧
        as.map ixAddr = recAddrs rb rs ∧ as.length = es.length := by
  obtain ⟨ext, as, has, hmap⟩ := build_peer_recs_walk ht hbd hS hH hR hlv hflat hd hown hlen hbR
    es 0 (by simp) hes hrb ev hsub
  rw [← List.range_eq_range', hlen] at hmap
  refine ⟨ext, as, has, by rw [hmap, recAddrs_eq_range hR], ?_⟩
  have h1 := congrArg List.length hmap
  rw [List.length_map, List.length_map, List.length_range] at h1
  rw [h1, hlen]

/-- **`build_peer_recs` as `FamilyRecon.check_recursor_canonical_at_spec` takes it**: at the
record's address held on the call's heap, every observed `build_peer_recs` on the represented
family, on a heap extending it, returns `FamilyRecon.recAddrs`. -/
theorem build_peer_recs_hyp (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hR : FamRecRecord E₀ rb crb rs) (hlv : RecLevelsDefined t E₀ rb crb rs)
    {es : List FlatEntry} (hflat : RecordFlat t E₀ rb crb rs es) (hd : FlatDistinct es)
    (hown : AuxParamsOwn E₀ es) (hlen : es.length = rs.size)
    {arb : Bytes.Address} (hbR : ixAddr arb = rb) {x_rb x_addr : SourceValue F} {h : Heap F}
    (hrb : Bytes.RepAddressRef addrTy h arb x_rb) :
    ∀ {m m' : Heap F} {v x_flat : SourceValue F} {cs' : List (Call F)},
      ObsFn W "KernelCheck::build_peer_recs" [x_flat, x_rb, x_addr] m v m' cs' →
      Heap.Extends h m → IxVM.Consistency.Bounded cs' → (∀ c ∈ cs', c ∈ calls) →
      RepList flatListEnum (FlatEntryRepExact (keyOf t)) m es x_flat →
      ∃ as : List Bytes.Address,
        RepList IxVM.Refinement.Core.addrListEnum (Bytes.RepAddressRef addrTy) m' as v ∧
          as.map ixAddr = recAddrs rb rs := by
  intro m m' v x_flat cs' ev ext _ hsub hes
  obtain ⟨-, as, has, hmap, -⟩ := build_peer_recs_spec ht hbd hS hH hR hlv hflat hd hown hlen hbR
    hes (Bytes.repAddressRef_heapMono₂ addrTy ext hrb) ev hsub
  exact ⟨as, has, hmap⟩

end Build

/-! ## The parameters and levels a member check reads at an auxiliary entry -/

/-- **`KernelCheck::extract_aux_spec_params_from_rec` at the entry's parameter count**: on a
recursor whose major premise, in the represented type, is taken at the entry's parameters
(`RecordFlat`'s clause), the parameters read at a count that is the entry's are the entry's. -/
theorem extract_aux_spec_params_from_rec_own {κ : _root_.Address → KKey}
    {np nmot nmin ni pnp : Nat}
    (hN : np + nmot + nmin + ni < 288230376151711744) (hpnp : pnp < 288230376151711744)
    {ty d : KExpr} {e : FlatEntry}
    {x_ty xm xa xls w17 w18 w19 w20 w21 w22 r : SourceValue F} {h h' : Heap F}
    {cs root : List (Call F)}
    (hM : MajorConst h x_ty (np + nmot + nmin + ni) xm xa xls) (hty : TmOExact κ h ty x_ty)
    (hdom : binderDomAfter (np + nmot + nmin + ni) ty = some d)
    (hpar : e.aux = true →
      ((Ix.Kernel.Expr.getAppArgs d).take e.params.length).map
        (Ix.Kernel.Expr.lowerBVars (nmot + nmin + ni) 0) = e.params)
    (hcount : e.aux = true → pnp = e.params.length)
    (ev : ObsFn W "KernelCheck::extract_aux_spec_params_from_rec"
      [.construct "KernelTypes::KConstantInfo" "Rec"
        [w17, x_ty, .field (np : F), .field (ni : F), .field (nmot : F), .field (nmin : F),
          w18, w19, w20, w21, w22], .field (pnp : F)] h r h' cs)
    (hbd : Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root) :
    Heap.Extends h h' ∧ ∃ sp, RepList kexprListEnum (TmOExact κ) h' sp r ∧
      (e.aux = true → sp = e.params) := by
  obtain ⟨ext, d', ys, hdom', hys, hrep⟩ :=
    extract_aux_spec_params_from_rec_spec (root := root) hN hpnp hM hty ev hbd hroot
  have hdd : d' = d := Option.some.inj (hdom'.symm.trans hdom)
  subst hdd
  refine ⟨ext, ys, hrep, fun hx => ?_⟩
  rw [occParamsLower_eq _ _ _ hys, hcount hx]
  exact hpar hx

/-- **`KernelCheck::extract_aux_occ_us` at an entry**: on a recursor whose major premise, in the
represented type, is headed by a constant at the entry's levels (`RecordFlat`'s clause), the
levels read are the entry's. -/
theorem extract_aux_occ_us_own {κ : _root_.Address → KKey} {np nmot nmin ni : Nat}
    (hN : np + nmot + nmin + ni < 288230376151711744)
    {ty d : KExpr} {e : FlatEntry} {kk : KKey}
    {x_ty xm xa xls w17 w18 w19 w20 w21 w22 r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (hM : MajorConst h x_ty (np + nmot + nmin + ni) xm xa xls) (hty : TmOExact κ h ty x_ty)
    (hdom : binderDomAfter (np + nmot + nmin + ni) ty = some d)
    (hfn : Ix.Kernel.Expr.getAppFn d = .const kk e.levels)
    (ev : ObsFn W "KernelCheck::extract_aux_occ_us"
      [.construct "KernelTypes::KConstantInfo" "Rec"
        [w17, x_ty, .field (np : F), .field (ni : F), .field (nmot : F), .field (nmin : F),
          w18, w19, w20, w21, w22]] h r h' cs) :
    Heap.Extends h h' ∧ RepKLevelList h' e.levels r := by
  obtain ⟨hr, ext⟩ := extract_aux_occ_us_spec hN hM ev
  obtain ⟨d', a, ls, As, hdom', hdeq, -, -, rls⟩ := hM.sem hty
  have hdd : d' = d := Option.some.inj (hdom'.symm.trans hdom)
  subst hdd
  rw [hdeq, getAppFn_const_mkAppN] at hfn
  injection hfn with _ hl
  subst hl
  rw [hr]
  exact ⟨ext, rls.mono ext⟩

end IxVM.Refinement.Binding.FamilyReconPeers
