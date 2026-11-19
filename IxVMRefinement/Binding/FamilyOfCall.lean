import IxVMRefinement.FamilyGraph.ProducersCarriers
import IxVMRefinement.FamilyGraph.ProducersRefs
import IxVMRefinement.FamilyAlias.CallRecs
import IxVMRefinement.Binding.FamilyFlat
import IxVMRefinement.Binding.PayloadDirectLoads
import IxVMRefinement.Binding.PayloadCoreSpecs

/-! # The family record of a block, read off an observed family check

`Binding.FamilyOf.FamilyOfBlock` states, on the raw Ixon readers `motiveCarrierAt` and
`majorHeadAt`, that a family record eliminates the flattened family of its block position by
position. This module reads those clauses off an observed `KernelModeled::check_family`, at any
limit.

* `peel_add`, `check_carriers_go_raw`, `check_carriers_raw`: `KernelModeled::check_carriers` on
  a raw converted recursor type reads, at every motive `j` below the count of the block's types,
  the carrier `motiveCarrierAt` reads: the `j`-th type of the block.
* `peel_n_foralls_raw58`, `peel_n_foralls_peelForalls`, `rec_to_parent_addr_both`:
  `KernelCheck::rec_to_parent_addr` on a recursor type held both raw and exactly returns the
  address `majorHeadAt` reads, and that address's constant heads the major premise's type in the
  represented term.
* `recMember_readers`: one iteration of `KernelModeled::check_recs`: the motive count, the
  carriers of the motives of the block's own types, and the major premise's address, which is the
  one the canonical reading of the recursor's type (`FamilyFlat.loadedAt`) names.
* `checkRecs_member`, `FamilyCallReaders`, `familyCall_readers`: the same of every recursor of
  the family record of an observed family check.
* `familyCall_block_indcs`, `build_recur_addrs_hashed`, `familyCall_block_members`,
  `famBlockRecord_of_call`: the block of an observed family check is a non-empty block of
  inductive types whose projection records are stored. That the block is in Lean's logic and that
  its constructors' projection records are stored are not read off the family check here.
* `FamilyCallReaders.major_of_recordFlat`: the correspondence of positions (`major`) at every
  position, the nested auxiliaries included, from the record's entries in the canonical reading
  (`FamilyFlat.RecordFlat`).
* `familyOfBlock_of_readers`, `familyOfBlock_of_call`: `FamilyOfBlock`, taking of the flattened
  family its count, its first entries, `RecordFlat`, and the carriers of the motives past the
  block's own types (`KernelModeled::check_carriers` reads only the block's own).
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding.FamilyOfCall

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)
open IxVM.Refinement.Typing
open IxVM.Refinement.Binding.FamilyOf
open IxVM.Refinement.Decl (TmExact)

/-! ## The raw readers along a telescope -/

/-- **Peeling binders composes.** -/
theorem peel_add (c : Ixon.Constant) :
    ∀ (n m : Nat) (e e' : Ixon.Expr), peel c n e = some e' → peel c (n + m) e = peel c m e'
  | 0, m, e, e', h => by
    simp only [peel, Option.some.injEq] at h
    subst h
    rw [Nat.zero_add]
  | n + 1, m, e, e', h => by
    rw [Nat.add_right_comm]
    simp only [peel] at h ⊢
    cases hn : node c e with
    | all d b =>
      rw [hn] at h
      exact peel_add c n m b e' h
    | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | app _ _ | lam _ _
    | letE _ _ _ _ _ | share _ =>
      rw [hn] at h
      cases h

/-- The body after one more binder. -/
theorem peel_succ_of_all (c : Ixon.Constant) {n : Nat} {e e' d b : Ixon.Expr}
    (h : peel c n e = some e') (hn : node c e' = .all d b) : peel c (n + 1) e = some b := by
  rw [peel_add c n 1 e e' h]
  simp only [peel, hn]

/-! ## `check_carriers` at every motive -/

/-- **`KernelModeled::check_carriers_go` on a raw converted term**: the binder at every position
`j` of the listed addresses has a domain whose last binder domain is headed by a reference to the
`j`-th address. -/
theorem check_carriers_go_raw {crb : Ixon.Constant} {blobs : List (_root_.Address × ByteArray)} :
    ∀ (as : List Bytes.Address) {bound : Nat} {e : Ixon.Expr} {x_e x_ta r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      L1.RawConvExpr crb.refs.toList [] crb.univs.toList crb.sharing.toList blobs h bound e x_e →
      RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h as x_ta →
      ObsFn Obs.W "KernelModeled::check_carriers_go" [x_e, x_ta] h r h' cs →
      ∀ (j : Nat) (a : Bytes.Address), as[j]? = some a →
        ∃ e' m d n, peel crb j e = some e' ∧ domOf crb e' = some m ∧
          lastDom crb n m = some d ∧ refHeadAt crb n d = some (Core.ixAddr a)
  | [], _, _, _, _, _, _, _, _, _, _, _ => by
    intro j a hj
    simp at hj
  | b₀ :: bs, bound, e, x_e, x_ta, r, h, h', cs, raw, hta, ev => by
    match Obs.«KernelModeled::check_carriers_go».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hta ld
    | .Cons (m78 := m78) (m170 := m170) (ld12 := ld12) (ld53 := ld53) (ev103 := ev103)
        (ev90 := ev90) (ld137 := ld137) (ev180 := ev180) (heq203 := heq203) (ev209 := ev209) .. =>
      obtain ⟨_, _, hcons, ht_rep, hrest_rep⟩ := Lib.rep_cons_of_load hta ld12
      injection hcons with hb_eq hbs_eq
      subst hb_eq hbs_eq
      obtain ⟨b₂, ed, eb, hnd₁, raw_d, raw_b⟩ := rawConvExpr_forall_inv raw ld53
      obtain ⟨rfl, -, n₁, b₃, ed', hld, raw_d'⟩ :=
        last_binder_dom_raw_aux _ (Nat.le_refl _) raw_d ev103
      obtain ⟨ext_sp, -, n₂, b₄, raw_sp, hns_sp⟩ :=
        collect_spine_raw_aux _ (Nat.le_refl _) raw_d' ev90
      obtain ⟨rIdx, uIdxs, a_c, d_c, hnd_sp, href_c, hd_c, hra_c⟩ :=
        rawConvExpr_const_inv raw_sp ld137
      rw [node_of_not_share hns_sp] at hnd_sp
      have ht_sp := Bytes.repAddressRef_heapMono₂ Core.addrTy ext_sp ht_rep
      obtain ⟨heq_c, rfl⟩ := Lib.address_eq_spec ev180 hra_c ht_sp
      have hd_eq : d_c = b₀ := by
        by_cases hdb : d_c = b₀
        · exact hdb
        · rw [ite_eq_right hdb] at heq_c
          exact absurd (Value.field.inj (heq203.symm.trans heq_c)) (by decide)
      subst hd_eq
      intro j a hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        refine ⟨e, ed, ed', max n₁ n₂, rfl, ?_,
          lastDom_mono crb ed' n₁ (max n₁ n₂) ed hld (Nat.le_max_left _ _), ?_⟩
        · simp only [domOf, hnd₁]
        · have hrefAt : refHeadAt crb n₂ ed' = some (Core.ixAddr d_c) := by
            unfold refHeadAt
            rw [hnd_sp, hd_c]
            exact href_c
          exact refHeadAt_mono hrefAt (Nat.le_max_right _ _)
      | succ j =>
        have hj' : bs[j]? = some a := by simpa using hj
        obtain ⟨e', m, d, n, hp, hdm, hl, hr⟩ :=
          check_carriers_go_raw bs (raw_b.mono ext_sp (fun _ hm => hm))
            (repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext_sp hrest_rep)
            ev209 j a hj'
        refine ⟨e', m, d, n, ?_, hdm, hl, hr⟩
        rw [Nat.add_comm, peel_add crb 1 j e eb (by simp only [peel, hnd₁])]
        exact hp

/-- **`KernelModeled::check_carriers` on a raw converted recursor type**: motive `j` of the
recursor is over the `j`-th listed address, at every position of the list. -/
theorem check_carriers_raw {crb : Ixon.Constant} {rc : Ixon.Recursor}
    {blobs : List (_root_.Address × ByteArray)} {as : List Bytes.Address}
    {x_ty x_ta r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hnp : rc.params.toNat < 72057594037927936)
    (raw : L1.RawConvExpr crb.refs.toList [] crb.univs.toList crb.sharing.toList blobs h
      4294967295 rc.typ x_ty)
    (hta : RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h as x_ta)
    (ev : ObsFn Obs.W "KernelModeled::check_carriers"
      [x_ty, .field (rc.params.toNat : F), x_ta] h r h' cs) :
    ∀ (j : Nat) (a : Bytes.Address), as[j]? = some a →
      ∃ n, motiveCarrierAt crb rc j n = some (Core.ixAddr a) := by
  match Obs.«KernelModeled::check_carriers».obs ev with
  | .run (ev20 := ev20) (ev6 := ev6) .. =>
    obtain ⟨rfl, -, b₁, e₁, hpeel, raw₁⟩ := peel_n_foralls_raw rc.params.toNat hnp raw ev20
    intro j a hj
    obtain ⟨e', m, d, n, hp, hdm, hl, hr⟩ := check_carriers_go_raw as raw₁ hta ev6 j a hj
    refine ⟨n, ?_⟩
    unfold motiveCarrierAt
    rw [peel_add crb rc.params.toNat j rc.typ e₁ hpeel, hp]
    dsimp only [bind, Option.bind]
    rw [hdm]
    dsimp only [bind, Option.bind]
    rw [hl]
    exact hr

/-! ## The major premise: the raw reader and the canonical reading name one address -/

/-- A natural number below `2^58` is its own value in the field. -/
theorem val_cast_lt_u58 {n : Nat} (hn : n < 288230376151711744) : ((n : F)).val = n := by
  have hlt : n < Aiur.Library.U32.Goldilocks.modulus := by
    change n < 18446744069414584321
    omega
  change (n : ZMod Aiur.Library.U32.Goldilocks.modulus).val = n
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]

/-- **`KernelCheck::peel_n_foralls` on a raw converted term** peels `n` binders (`peel`), at any
count below `2^58` (a recursor's parameters, motives, minors and indices together). -/
theorem peel_n_foralls_raw58 {c : Ixon.Constant} {recurAddrs : List _root_.Address}
    {blobs : List (_root_.Address × ByteArray)} :
    ∀ (n : Nat) {bound : Nat} {e : Ixon.Expr} {kp r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      n < 288230376151711744 →
      L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e kp →
      ObsFn Obs.W "KernelCheck::peel_n_foralls" [kp, .field (n : F)] h r h' cs →
      h' = h ∧
        ∃ b' e', peel c n e = some e' ∧
          L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h b' e' r
  | 0, bound, e, kp, r, h, h', cs, _, raw, ev => by
    match Obs.«KernelCheck::peel_n_foralls».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh
      exact ⟨rfl, bound, e, rfl, raw⟩
    | .other (hne19 := hne) .. => exact (hne (by simp)).elim
  | n + 1, bound, e, kp, r, h, h', cs, hlt, raw, ev => by
    have hne0 : (.field ((n + 1 : Nat) : F) : SourceValue F) ≠ .field 0 := by
      intro he
      have hv := congrArg ZMod.val (Value.field.inj he)
      rw [val_cast_lt_u58 hlt] at hv
      simp at hv
    match Obs.«KernelCheck::peel_n_foralls».obs ev with
    | .n0 (hv14 := hv) .. => exact (hne0 hv).elim
    | .other (v66 := v66) (ld34 := ld) (op87 := op) (ev64 := ev64) .. =>
      have hv66 : v66 = .field (n : F) := by
        simp only [evalBinOp, Except.ok.injEq] at op
        rw [← op]
        push_cast
        ring_nf
      subst hv66
      obtain ⟨b₁, ed, eb, hnd, -, raw_b⟩ := rawConvExpr_forall_inv raw ld
      obtain ⟨hh, b₂, e', hpeel, raw'⟩ := peel_n_foralls_raw58 n (by omega) raw_b ev64
      refine ⟨hh, b₂, e', ?_, raw'⟩
      simp only [peel, hnd]
      exact hpeel

/-- **`KernelCheck::peel_n_foralls` on an exactly represented term** peels `n` binders
(`FamilyFlat.peelForalls`). -/
theorem peel_n_foralls_peelForalls {κ : _root_.Address → KKey} {Γ : Nat → KExpr} :
    ∀ (n : Nat) {k : Nat} {E : KExpr} {kp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 288230376151711744 →
      TmExact κ 0 Γ h k E kp →
      ObsFn Obs.W "KernelCheck::peel_n_foralls" [kp, .field (n : F)] h r h' cs →
      ∃ E', FamilyFlat.peelForalls n E = some E' ∧ TmExact κ 0 Γ h (k + n) E' r
  | 0, k, E, kp, r, h, h', cs, _, hE, ev => by
    match Obs.«KernelCheck::peel_n_foralls».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh
      exact ⟨E, rfl, hE⟩
    | .other (hne19 := hne) .. => exact (hne (by simp)).elim
  | n + 1, k, E, kp, r, h, h', cs, hlt, hE, ev => by
    have hne0 : (.field ((n + 1 : Nat) : F) : SourceValue F) ≠ .field 0 := by
      intro he
      have hv := congrArg ZMod.val (Value.field.inj he)
      rw [val_cast_lt_u58 hlt] at hv
      simp at hv
    match Obs.«KernelCheck::peel_n_foralls».obs ev with
    | .n0 (hv14 := hv) .. => exact (hne0 hv).elim
    | .other (v66 := v66) (ld34 := ld) (op87 := op) (ev64 := ev64) .. =>
      have hv66 : v66 = .field (n : F) := by
        simp only [evalBinOp, Except.ok.injEq] at op
        rw [← op]
        push_cast
        ring_nf
      subst hv66
      obtain ⟨T, B, ℓ, rfl, -, hb, -⟩ := hE.forallE_of_load ld
      obtain ⟨E', hp, hE'⟩ := peel_n_foralls_peelForalls n (by omega) hb ev64
      refine ⟨E', ?_, ?_⟩
      · simp only [FamilyFlat.peelForalls]
        exact hp
      · rw [show k + (n + 1) = k + 1 + n by omega]
        exact hE'

/-- **`KernelCheck::rec_to_parent_addr` on a recursor type held both raw and exactly**: the
address it returns is the one `majorHeadAt` reads off the record, and the constant heading the
major premise's type in the represented term is that address's. -/
theorem rec_to_parent_addr_both {t : Ix.Kernel.RoleTable} {crb : Ixon.Constant}
    {rc : Ixon.Recursor} {blobs : List (_root_.Address × ByteArray)} {Γ : Nat → KExpr}
    {E : KExpr} {x_ty r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hN : rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat <
      288230376151711744)
    (raw : L1.RawConvExpr crb.refs.toList [] crb.univs.toList crb.sharing.toList blobs h
      4294967295 rc.typ x_ty)
    (htm : TmExact (Core.keyOf t) 0 Γ h 0 E x_ty)
    (ev : ObsFn Obs.W "KernelCheck::rec_to_parent_addr"
      [x_ty, .field (rc.params.toNat : F), .field (rc.motives.toNat : F),
        .field (rc.minors.toNat : F), .field (rc.indices.toNat : F)] h r h' cs) :
    ∃ a : Bytes.Address, Bytes.RepAddressRef Core.addrTy h' a r ∧
      (∃ n, majorHeadAt crb rc n = some (Core.ixAddr a)) ∧
      ∃ d ls, FamilyFlat.binderDomAfter
          (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) E = some d ∧
        d.getAppFn = .const (Core.keyOf t (Core.ixAddr a)) ls := by
  obtain ⟨v1, x9, x17, v37, m38, cs48, x_major_ty, w86, w87, m104, cs115, x_head, w132, x_caddr,
    w162, op32, op24, op16, ev50, ld78, ev117, ld154, hr_eq, hh_eq, _⟩ :=
    Obs.«KernelCheck::rec_to_parent_addr».obs ev
  subst hr_eq hh_eq
  have hx17 : x17 = .field ((rc.params.toNat : F) + (rc.motives.toNat : F)) := by
    simp only [evalBinOp, Except.ok.injEq] at op32; exact op32.symm
  subst hx17
  have hx9 : x9 = .field ((rc.params.toNat : F) + (rc.motives.toNat : F) +
      (rc.minors.toNat : F)) := by
    simp only [evalBinOp, Except.ok.injEq] at op24; exact op24.symm
  subst hx9
  have hv1 : v1 = .field ((rc.params.toNat + rc.motives.toNat + rc.minors.toNat +
      rc.indices.toNat : Nat) : F) := by
    simp only [evalBinOp, Except.ok.injEq] at op16
    rw [← op16]
    push_cast
    rfl
  subst hv1
  obtain ⟨hh, b₁, e₁, hpeel, raw₁⟩ := peel_n_foralls_raw58 _ hN raw ev50
  subst hh
  obtain ⟨E', hpE, hE'⟩ := peel_n_foralls_peelForalls _ hN htm ev50
  obtain ⟨b₂, ed, eb, hnd₁, raw_d, -⟩ := rawConvExpr_forall_inv raw₁ ld78
  obtain ⟨T, B, ℓ, rfl, hT, -, -⟩ := hE'.forallE_of_load ld78
  obtain ⟨ext_sp, -, n₂, b₄, raw_sp, hns_sp⟩ :=
    collect_spine_raw_aux _ (Nat.le_refl _) raw_d ev117
  obtain ⟨rIdx, uIdxs, a_c, d_c, hnd_sp, href_c, hd_c, hra_c⟩ :=
    rawConvExpr_const_inv raw_sp ld154
  rw [node_of_not_share hns_sp] at hnd_sp
  obtain ⟨hd, sp, H, As, htup, hH, -, hTeq⟩ := Decl.collect_spine_exact ev117 hT
  injection htup with hl
  injection hl with hhd _
  subst hhd
  have hconst : ∃ a ls, H = .const (Core.keyOf t (Core.ixAddr a)) ls ∧
      Bytes.RepAddressRef Core.addrTy h' a r := by
    cases hH with
    | const cell ra _ =>
      obtain ⟨-, hxs⟩ := Core.load_cell cell ld154
      injection hxs with hcx _
      subst hcx
      exact ⟨_, _, rfl, ra⟩
    | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | app cell _ _ | lam cell _ _ _
    | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _
    | proj cell _ _ =>
      exact (Core.load_cell_ne cell ld154 (by decide)).elim
  obtain ⟨a, ls, rfl, hra⟩ := hconst
  have ha : a = d_c := Bytes.repAddressRef_inj U32.Goldilocks.compatible hra hra_c
  subst ha
  refine ⟨a, hra, ⟨n₂, ?_⟩, T, ls, ?_, ?_⟩
  · unfold majorHeadAt
    rw [hpeel]
    dsimp only [bind, Option.bind]
    have hdom : domOf crb e₁ = some ed := by simp only [domOf, hnd₁]
    rw [hdom]
    dsimp only [bind, Option.bind]
    unfold refHeadAt
    rw [hnd_sp, hd_c]
    exact href_c
  · unfold FamilyFlat.binderDomAfter
    rw [hpE]
  · rw [hTeq, Core.ModeledAux.getAppFn_mkAppN]
    rfl

/-! ## One member of `check_recs` -/

/-- **What one iteration of `KernelModeled::check_recs` gives of the raw readers**, for the
recursor `rc` at position `k` of the family record: its motive count is the count the loop
carries; motive `j` is over the `j`-th listed type address (`check_carriers`); and the address
`majorHeadAt` reads is the constant heading the major premise's type in the canonical reading of
the recursor's type (`FamilyFlat.loadedAt`; `rec_to_parent_addr`). -/
theorem recMember_readers
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hR : FamRecRecord E₀ rb crb rs)
    {typeAs : List Bytes.Address}
    {rcV tys recs models src dst aset s n kV np uo bnl fam form r : SourceValue F}
    {h h' : Heap F} {cs_rec : List (Call F)}
    (hsub : FamilyAlias.CallSub cs_rec calls)
    (C : FamilyAlias.CheckRecsCons rcV tys recs models src dst aset s n kV np uo bnl fam form r
      h h' cs_rec)
    {k : Nat} {rc : Ixon.Recursor} {aRec : Bytes.Address}
    (hk_u64 : k < UInt64.size) (hrk : rs[k]? = some (.recr rc))
    (haRec_eq : ixAddr aRec = rprjAddr rb k)
    (htys_rep : RepList addrListEnum (Bytes.RepAddressRef addrTy) h typeAs tys)
    (haRec_rep : Bytes.RepAddressRef addrTy h aRec C.x) :
    (n = .field (rc.motives.toNat : F) ∧ rc.motives.toNat < 72057594037927936) ∧
    (∀ (j : Nat) (a : Bytes.Address), typeAs[j]? = some a →
      ∃ m, motiveCarrierAt crb rc j m = some (ixAddr a)) ∧
    ∃ a : _root_.Address, (∃ m, majorHeadAt crb rc m = some a) ∧
      ∃ ty d ls, FamilyFlat.loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs)
          rc.lvls.toNat (FamilyFlat.mutsRoot rs k) rc.typ = some ty ∧
        FamilyFlat.binderDomAfter
          (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) ty = some d ∧
        d.getAppFn = .const (Core.keyOf t a) ls := by
  have hsub_getRec : FamilyAlias.CallSub C.evGetRec.cs calls :=
    fun cl hcl => hsub cl (C.evGetRec.sub cl hcl)
  obtain ⟨_, cRec, hhRec, hbaRec, hexRec, -, htrRec⟩ :=
    L1.get_ci_block_trace_spec (bounded_sub hsub_getRec hbd) haRec_rep C.evGetRec.obs
  have hrecAtRec : Ix.Cert.recordAt E₀ (ixAddr aRec) = some (memberProjection rb k (.recr rc)) := by
    rw [← hS.recordOf_eq_recordAt, haRec_eq, ← LoadedReads.memberAddr_recr]
    exact hR.members k (.recr rc) hrk
  have hcRec_eq : cRec = memberProjection rb k (.recr rc) :=
    hS.record_eq hrecAtRec (Core.hashed_mono hsub_getRec hhRec) hbaRec hexRec
  subst hcRec_eq
  unfold L1.GetCIBlockTraceResult at htrRec
  simp only [memberProjection] at htrRec
  obtain ⟨_, _, crb', rs', rc', blobs, tree, vRec, hhBlk, hbaBlk, hexBlk, hmuts', hrk', hhp,
      built, hldv, hrepRec⟩ := htrRec
  have hcrb_eq : crb' = crb :=
    hS.record_eq ((hS.recordOf_eq_recordAt rb).symm.trans hR.record)
      (Core.hashed_mono hsub_getRec hhBlk) hbaBlk hexBlk
  subst crb'
  have hrs_eq : rs' = rs := Ixon.ConstantInfo.muts.inj (hmuts'.symm.trans hR.muts)
  subst rs'
  have hk_toNat : k.toUInt64.toNat = k := by
    change (UInt64.ofNat k).toNat = k
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt hk_u64
  rw [hk_toNat, Array.getElem?_toList, hrk] at hrk'
  have hrc_eq : rc' = rc := Ixon.MutConst.recr.inj (Option.some.inj hrk').symm
  subst rc'
  rw [hk_toNat] at hrepRec
  obtain ⟨hlvls_lt, hnp_lt, hni_lt, hnmot_lt, hnmin_lt, hk_lt, tyPtr, rulesPtr, blkPtr, bBlk,
      planT, hbBlk_eq, hbBlk_ref, hvRec_eq, rty, hpT, hlT, hrlsTrace⟩ := hrepRec
  have hvRec_ld := Except.ok.inj (C.ldRec.symm.trans hldv)
  rw [hvRec_eq] at hvRec_ld
  injection hvRec_ld with _ _ hargs_r
  injection hargs_r with hnl_eq hargs_r
  injection hargs_r with hty_eq hargs_r
  injection hargs_r with hnp_eq hargs_r
  injection hargs_r with hni_eq hargs_r
  injection hargs_r with hn_eq hargs_r
  injection hargs_r with hnmin_eq hargs_r
  subst hty_eq
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hrun := hS.blobs bs (Core.hashed_mono hsub_getRec hhx)
    rwa [hxa] at hrun
  have hagree : L1.BlobReadAgreement (readCtx t (fun x => E₀.blobs.get? x)).blob blobs :=
    L1.BlobReadAgreement.of_mem hblob
  have hself0 : ∀ i x, ([] : List _root_.Address)[i]? = some x →
      ∃ m k, blockSelf t rb rs i = some m ∧ m = .ok k := fun _ _ hx => by simp at hx
  obtain ⟨tyP, hreadP⟩ := LoadedReads.exprReader_read_ok ht (param := id)
    (self := blockSelf t rb rs) rty hself0 hblob
  have hcall_scope : (⟨"KernelCheck::validate_expr_well_scoped",
      [C.ty, .field 0, .field (rc.lvls.toNat : F)], C.m473⟩ : Call F) ∈ calls := by
    rw [← hnl_eq]; exact hsub _ C.evScope.mem
  have evScope' : ObsFn Obs.W "KernelCheck::validate_expr_well_scoped"
      [C.ty, .field 0, .field (rc.lvls.toNat : F)] C.m473 C.vScope C.m511 C.evScope.cs := by
    rw [← hnl_eq]; exact C.evScope.obs
  obtain ⟨_, htyP_lbb, htyP_def⟩ :=
    Assembly.validate_expr_well_scoped_spec hbd hlvls_lt rty
      (C.ext391.trans C.evCarriers.extends) hreadP evScope' hcall_scope
  have hrdP : (exprReader t (fun x => E₀.blobs.get? x) crb
      (Ix.Kernel.Reader.recParam (List.range rc.lvls.toNat)) (blockSelf t rb rs)).read rc.typ =
      .ok tyP := by
    rw [Assembly.recParam_range]; exact hreadP
  have hself_nil : ∀ i x m k', ([] : List _root_.Address)[i]? = some x →
      blockSelf t rb rs i = some m → m = .ok k' → k' = Core.keyOf t x := fun _ _ _ _ hx => by
    simp at hx
  obtain ⟨tyA, hcanon, -, htm⟩ :=
    FamilyAlias.annotation_canon_gen_exact ht (ps := List.range rc.lvls.toNat)
      (by rw [List.length_range]) (by rw [List.length_range]; exact hlvls_lt)
      hself_nil hagree rty built hpT hlT hrdP htyP_lbb
      htyP_def
  have hloaded : FamilyFlat.loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs)
      rc.lvls.toNat (FamilyFlat.mutsRoot rs k) rc.typ = some tyA := by
    unfold FamilyFlat.loadedAt
    rw [hreadP]
    exact hcanon
  have htm0 : TmExact (Core.keyOf t) 0 (fun _ => .sort .zero) C.m67 0 tyA C.ty := by
    have h0 := htm 0 (fun _ => .sort .zero)
    rwa [Decl.posOf_range] at h0
  have ext_67_669 : Heap.Extends C.m67 C.m669 := by
    have e1 : Heap.Extends C.m561 C.mNil1 := by rw [C.hNil1]; exact Heap.Extends.snoc _ _
    have e2 : Heap.Extends C.mRen C.mNil2 := by rw [C.hNil2]; exact Heap.Extends.snoc _ _
    have e3 : Heap.Extends C.mLP C.mNilSort := by rw [C.hNilSort]; exact Heap.Extends.snoc _ _
    exact C.ext391.trans (C.evCarriers.extends.trans (C.evScope.extends.trans
      (C.evNoMent.extends.trans (e1.trans (C.evPeel1.extends.trans (C.evRen.extends.trans
        (e2.trans (C.evPeel2.extends.trans (C.evParamEq.extends.trans (C.evPins.extends.trans
          (C.evLowerPins.extends.trans (e3.trans (C.evSort.extends.trans C.ext669)))))))))))))
  have evPar' : ObsFn Obs.W "KernelCheck::rec_to_parent_addr"
      [C.ty, .field (rc.params.toNat : F), .field (rc.motives.toNat : F),
        .field (rc.minors.toNat : F), .field (rc.indices.toNat : F)]
      C.m669 C.parAddr C.m698 C.evParent.cs := by
    rw [← hnp_eq, ← hn_eq, ← hnmin_eq, ← hni_eq]; exact C.evParent.obs
  obtain ⟨a, -, hmaj, d, ls, hdom, hfn⟩ :=
    rec_to_parent_addr_both (by omega) (rty.mono ext_67_669 (fun _ hm => hm))
      (htm0.mono ext_67_669) evPar'
  have evCarriers' : ObsFn Obs.W "KernelModeled::check_carriers"
      [C.ty, .field (rc.params.toNat : F), tys] C.m391 C.vCarriers C.m473 C.evCarriers.cs := by
    rw [← hnp_eq]; exact C.evCarriers.obs
  have htys_391 : RepList addrListEnum (Bytes.RepAddressRef addrTy) C.m391 typeAs tys :=
    RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
      (C.evGetRec.extends.trans C.ext391) htys_rep
  exact ⟨⟨hn_eq, hnmot_lt⟩,
    check_carriers_raw hnp_lt (rty.mono C.ext391 (fun _ hm => hm)) htys_391 evCarriers',
    ixAddr a, hmaj, tyA, d, ls, hloaded, hdom, hfn⟩

/-! ## Every member of `check_recs` -/

/-- **Every listed recursor address has its iteration of `KernelModeled::check_recs`**: a `Cons`
step whose head is that address, at a heap extending the loop's and with calls among the
loop's. -/
theorem checkRecs_member :
    ∀ (as : List Bytes.Address)
      {rcV tys recs models src dst aset s n kV np uo bnl fam form r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h as recs →
      ObsFn Obs.W "KernelModeled::check_recs"
        [rcV, tys, recs, models, src, dst, aset, s, n, kV, np, uo, bnl, fam, form] h r h' cs →
      ∀ (i : Nat) (a : Bytes.Address), as[i]? = some a →
        ∃ (recs' models' s' kV' form' r' : SourceValue F) (h1 h1' : Heap F)
          (cs1 : List (Call F))
          (C : FamilyAlias.CheckRecsCons rcV tys recs' models' src dst aset s' n kV' np uo bnl
            fam form' r' h1 h1' cs1),
          Heap.Extends h h1 ∧ FamilyAlias.CallSub cs1 cs ∧
            Bytes.RepAddressRef addrTy h1 a C.x
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    intro i a hi
    simp at hi
  | b :: rest, rcV, tys, recs, models, src, dst, aset, s, n, kV, np, uo, bnl, fam, form, r, h,
      h', cs, hrep, ev => by
    rcases FamilyAlias.checkRecs_step ev with ⟨ld, -, -⟩ | ⟨⟨C⟩⟩
    · cases Lib.rep_nil_of_load hrep ld
    · obtain ⟨_, _, he, hb_rep, hrest_rep⟩ := Lib.rep_cons_of_load hrep C.ldRecs
      injection he with hb_eq hrest_eq
      subst hb_eq hrest_eq
      intro i a hi
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        exact ⟨recs, models, s, kV, form, r, h, h', cs, C, Heap.Extends.refl h,
          fun _ hcl => hcl, hb_rep⟩
      | succ i =>
        have hi' : rest[i]? = some a := by simpa using hi
        have ext : Heap.Extends h C.m892 := C.ext_h_m838.trans C.evRules.extends
        obtain ⟨recs', models', s', kV', form', r', h1, h1', cs1, C', ext1, hsub1, ha⟩ :=
          checkRecs_member rest
            (repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ addrTy) ext hrest_rep)
            C.evNext.obs i a hi'
        exact ⟨recs', models', s', kV', form', r', h1, h1', cs1, C', ext.trans ext1,
          fun cl hcl => C.evNext.sub cl (hsub1 cl hcl), ha⟩

/-! ## The readers of an observed family check -/

/-- **What an observed family check gives of the family record's raw readers.** The block at `B`
is a block record `cb` with members `ms`, the family record at `rb` a block of recursors `crb`
with members `rs`, and for every recursor `r` of the family record: it has one motive per member
of the record (`motives`); its motive `j` is over the `j`-th type of the block, at every type of
the block (`carriers`); and the address `majorHeadAt` reads off it is the constant heading the
major premise's type in the canonical reading of its type (`major`). -/
structure FamilyCallReaders (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (B rb : _root_.Address)
    (cb crb : Ixon.Constant) (ms rs : Array Ixon.MutConst) : Prop where
  blockRecord : recordOf E₀ B = some cb
  blockMuts : cb.info = .muts ms
  record : FamRecRecord E₀ rb crb rs
  motives : ∀ (k : Nat) (r : Ixon.Recursor), rs[k]? = some (Ixon.MutConst.recr r) →
    r.motives.toNat = rs.size
  carriers : ∀ (k : Nat) (r : Ixon.Recursor), rs[k]? = some (Ixon.MutConst.recr r) →
    ∀ (j : Nat) (m : Ixon.MutConst), ms[j]? = some m →
      ∃ n, motiveCarrierAt crb r j n = some (memberAddr B j m)
  major : ∀ (k : Nat) (r : Ixon.Recursor), rs[k]? = some (Ixon.MutConst.recr r) →
    ∃ a : _root_.Address, (∃ n, majorHeadAt crb r n = some a) ∧
      ∃ ty d ls, FamilyFlat.loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs)
          r.lvls.toNat (FamilyFlat.mutsRoot rs k) r.typ = some ty ∧
        FamilyFlat.binderDomAfter
          (r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat) ty = some d ∧
        d.getAppFn = .const (Core.keyOf t a) ls

/-- **The raw readers of the family record of an observed family check**, at any limit
(`FamilyCallReaders`). -/
theorem familyCall_readers {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs) :
    ∃ cb crb ms rs, FamilyCallReaders t E₀ B rb cb crb ms rs := by
  obtain ⟨crb, rs, hc, hlog, hrs, hall, hmem⟩ := familyCall_record_block hS hH hfc
  have hR : FamRecRecord E₀ rb crb rs := ⟨hc, hrs, hall, hlog, hmem⟩
  obtain ⟨h, h', rc, xb, xrb, r, -, ⟨bB, hbB, rfl⟩, ⟨bR, hbR, rfl⟩, ev, -, hsub⟩ := hfc
  obtain ⟨C⟩ := FamilyAlias.checkFamily_chain ev
  have ext_0_453 : Heap.Extends h C.m453 :=
    (check_family_seg1_extends C.sg112).trans C.ext_m105_m453
  -- the block
  have hsubLoad : ∀ cl ∈ C.evLoadBlk.cs, cl ∈ calls :=
    fun cl hcl => hsub cl (C.evLoadBlk.sub cl hcl)
  obtain ⟨cb, ms, hbl, hms_rep⟩ :=
    Claim.load_block_head (Bytes.repAddressRef_heapMono₂ addrTy ext_0_453 hbB) C.evLoadBlk.obs
  obtain ⟨hBrec, hBmuts⟩ := (hbl.mono hsubLoad).stored hH
  -- the type addresses
  have ext_501_652 : Heap.Extends C.m501 C.m652 :=
    C.evLenMem.extends.trans (C.evIndcCnt.extends.trans C.evNParams.extends)
  have hmems652 : Core.Specs.Callees.MembersRep C.m652 ms.toList C.members :=
    Route.membersRep_of_repMutConstList (hms_rep.mono L1.repMutConst_heapMono₂ ext_501_652)
  have hb652 : Bytes.RepAddressRef addrTy C.m652 bB xb :=
    Bytes.repAddressRef_heapMono₂ addrTy
      (ext_0_453.trans (C.evLoadBlk.extends.trans ext_501_652)) hbB
  obtain ⟨-, as_ty, has_ty, hmap_ty⟩ := L1.build_recur_addrs_spec hmems652 hb652 C.evTypes.obs
  -- the recursor addresses
  have ext_674_784 : Heap.Extends C.m674 C.m784 :=
    C.evTypeMods.extends.trans (C.evCtors.extends.trans
      (C.evLenCtors.extends.trans C.evCtorMods.extends))
  have ext_0_784 : Heap.Extends h C.m784 :=
    ext_0_453.trans (C.evLoadBlk.extends.trans (ext_501_652.trans
      (C.evTypes.extends.trans ext_674_784)))
  have hbR784 : Bytes.RepAddressRef addrTy C.m784 bR xrb :=
    Bytes.repAddressRef_heapMono₂ addrTy ext_0_784 hbR
  have hsubRecs : ∀ cl ∈ C.evRecs.cs, cl ∈ calls :=
    fun cl hcl => hsub cl (C.evRecs.sub cl hcl)
  obtain ⟨as_rc, has_rc, hmap_rc⟩ :=
    FamilyAlias.family_recs_list hH hbR784 C.evRecs.obs hsubRecs hR
  have hrsz := FamilyAlias.family_recs_bound hS hH hbR784 C.evRecs.obs hsubRecs hR
  have hrlen : as_rc.length = rs.size := by
    have e := congrArg List.length hmap_rc
    simpa only [List.length_map, List.length_mapIdx, Array.length_toList] using e
  obtain ⟨hnRecs, -⟩ := Decl.addrList_length_spec
    (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
      (C.evNoRole.extends.trans C.evNoTypeRole.extends) has_rc) C.evLenRecs.obs
  -- the heaps of the loop
  have ext_840_978 : Heap.Extends C.m840 C.m978 :=
    C.evNoRole.extends.trans (C.evNoTypeRole.extends.trans (C.evLenRecs.extends.trans
      (C.evRecMods.extends.trans (C.evSrcTail.extends.trans (C.evSrc.extends.trans
        (C.evDstTail.extends.trans C.evDst.extends))))))
  have ext_840_1293 : Heap.Extends C.m840 C.m1293 := ext_840_978.trans C.ext_m978_m1293
  have ext_674_1293 : Heap.Extends C.m674 C.m1293 :=
    ext_674_784.trans (C.evRecs.extends.trans ext_840_1293)
  have has_rc1293 := repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ addrTy)
    ext_840_1293 has_rc
  have has_ty1293 := repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ addrTy)
    ext_674_1293 has_ty
  have hsubLoop : FamilyAlias.CallSub C.evCheckRecs.cs calls :=
    fun cl hcl => hsub cl (C.evCheckRecs.sub cl hcl)
  -- one member
  have hmember : ∀ (k : Nat) (rc' : Ixon.Recursor), rs[k]? = some (Ixon.MutConst.recr rc') →
      rc'.motives.toNat = rs.size ∧
      (∀ (j : Nat) (a : Bytes.Address), as_ty[j]? = some a →
        ∃ m, motiveCarrierAt crb rc' j m = some (ixAddr a)) ∧
      ∃ a : _root_.Address, (∃ m, majorHeadAt crb rc' m = some a) ∧
        ∃ ty d ls, FamilyFlat.loadedAt t (fun x => E₀.blobs.get? x) crb
            (blockSelf t (ixAddr bR) rs) rc'.lvls.toNat (FamilyFlat.mutsRoot rs k) rc'.typ =
              some ty ∧
          FamilyFlat.binderDomAfter
            (rc'.params.toNat + rc'.motives.toNat + rc'.minors.toNat + rc'.indices.toNat) ty =
              some d ∧
          d.getAppFn = .const (Core.keyOf t a) ls := by
    intro k rc' hk
    have hklt : k < rs.size := (Array.getElem?_eq_some_iff.mp hk).1
    have hkL : rs.toList[k]? = some (.recr rc') := by rw [Array.getElem?_toList]; exact hk
    have h1 : (as_rc.map ixAddr)[k]? = some (rprjAddr (ixAddr bR) k) := by
      rw [hmap_rc, List.getElem?_mapIdx, hkL]
      rfl
    rw [List.getElem?_map] at h1
    obtain ⟨a_k, ha_k, ha_k_eq⟩ := Option.map_eq_some_iff.mp h1
    obtain ⟨recs', models', s', kV', form', r', h1, h1', cs1, C', ext1, hsub1, ha_rep⟩ :=
      checkRecs_member as_rc has_rc1293 C.evCheckRecs.obs k a_k ha_k
    obtain ⟨⟨hn_eq, hmot_lt⟩, hcar, hmaj⟩ :=
      recMember_readers ht hbd hS hR (fun cl hcl => hsubLoop cl (hsub1 cl hcl)) C'
        (Nat.lt_trans hklt (Nat.lt_trans hrsz (by decide))) hk ha_k_eq
        (repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ addrTy) ext1 has_ty1293) ha_rep
    refine ⟨?_, hcar, hmaj⟩
    have he : ((rc'.motives.toNat : Nat) : F) = ((as_rc.length : Nat) : F) :=
      Value.field.inj (hn_eq.symm.trans hnRecs)
    have hv := congrArg ZMod.val he
    rw [val_cast_lt_u58 (by omega), val_cast_lt_u58 (by omega)] at hv
    rw [hv, hrlen]
  refine ⟨cb, crb, ms, rs, hBrec, hBmuts, hR, fun k r hk => (hmember k r hk).1, ?_,
    fun k r hk => (hmember k r hk).2.2⟩
  intro k r hk j m hj
  have hjL : ms.toList[j]? = some m := by rw [Array.getElem?_toList]; exact hj
  have h1 : (as_ty.map ixAddr)[j]? = some (memberAddr (ixAddr bB) j m) := by
    rw [hmap_ty, List.getElem?_mapIdx, hjL, LoadedReads.memberAddr_eq_projAddr]
    rfl
  rw [List.getElem?_map] at h1
  obtain ⟨a_j, ha_j, ha_j_eq⟩ := Option.map_eq_some_iff.mp h1
  obtain ⟨n, hn⟩ := (hmember k r hk).2.1 j a_j ha_j
  exact ⟨n, ha_j_eq ▸ hn⟩

/-! ## The block of an observed family check -/

/-- **The block of an observed family check is a block of inductive types of the run's store.** -/
theorem familyCall_block_indcs {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs) :
    ∃ cb ms, recordOf E₀ B = some cb ∧ cb.info = .muts ms ∧ 0 < ms.size ∧
      ∀ m ∈ ms.toList, ∃ ind, m = Ixon.MutConst.indc ind := by
  obtain ⟨cb, ms, hcb, hms, hpos, hfilt⟩ := familyCall_block_indc_nonempty hS hH hfc
  refine ⟨cb, ms, hcb, hms, hpos, fun m hm => ?_⟩
  rw [← Array.length_toList] at hfilt
  have hall := List.length_filter_eq_length_iff.mp hfilt m hm
  cases m with
  | indc ind => exact ⟨ind, rfl⟩
  | defn d => simp [Core.Specs.Callees.isIndc, Core.isIndc] at hall
  | recr r => simp [Core.Specs.Callees.isIndc, Core.isIndc] at hall

/-- A natural number at most `2^56` is its own value in the field. -/
theorem val_cast_le_u56 {n : Nat} (hn : n ≤ 72057594037927936) : ((n : F)).val = n :=
  val_cast_lt_u58 (by omega)

/-- **`Ingress::build_recur_addrs_walk` hashes every member's projection record.** -/
theorem build_recur_addrs_walk_hashed {ms : List Ixon.MutConst} {b : Bytes.Address} :
    ∀ (cur : List Ixon.MutConst) {k : Nat} {x_all x_blk x_cur r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      k ≤ 72057594037927936 →
      Core.Specs.Callees.MembersRep h ms x_all →
      Bytes.RepAddressRef Core.addrTy h b x_blk →
      Core.Specs.Callees.MembersRep h cur x_cur →
      (∀ j m', cur[j]? = some m' → ms[k + j]? = some m') →
      ObsFn Obs.W "Ingress::build_recur_addrs_walk" [x_all, x_blk, x_cur, .field (k : F)]
        h r h' cs →
      ∀ j m', cur[j]? = some m' → Hashed cs (Ixon.serConstant
        ⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b) (k + j) m', #[], #[], #[], #[]⟩)
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by intro _ _ hj; simp at hj
  | m :: rest, k, x_all, x_blk, x_cur, r, h, h', cs, hk, hms, hb, hcur, hsuf, ev => by
    rcases Obs.«Ingress::build_recur_addrs_walk».obs ev with
      ⟨ld12, _, _, _⟩ |
      ⟨w36, x_rest, v55, v56, m58, cs66, m94, cs102, v108,
        ld12, he51, hm50, ev68, op143, ev104, hc145⟩
    · cases Lib.rep_nil_of_load hcur ld12
    · obtain ⟨m', rest', he, _, hrest⟩ := Lib.rep_cons_of_load hcur ld12
      injection he with hm_eq hrest_eq
      subst m' rest'
      obtain ⟨ext1, hk_lt, -, mc, -, hget_mc, -, -, hhash⟩ :=
        L1.projection_addr_hashed_spec hms hb ev68
      rw [val_cast_le_u56 hk] at hk_lt hget_mc hhash
      have hmc_eq : mc = m := by
        have h0 := hsuf 0 m rfl
        rw [Nat.add_zero, hget_mc] at h0
        exact Option.some.inj h0
      subst mc
      simp only [evalBinOp, Except.ok.injEq] at op143
      have hv108 : v108 = .field (((k + 1 : Nat) : F)) := by
        rw [← op143]; push_cast; rfl
      rw [hv108] at ev104
      have hmono : HeapMono₂ Core.Specs.Callees.MutShape := fun _ _ _ _ _ rep => rep
      have htl := build_recur_addrs_walk_hashed rest (k := k + 1) (by omega)
        (hms.mono hmono ext1)
        (Bytes.repAddressRef_heapMono₂ Core.addrTy ext1 hb)
        (hrest.mono hmono ext1)
        (fun j m' hj => by
          have hstep := hsuf (j + 1) m' hj
          have hadd : k + 1 + j = k + (j + 1) := by omega
          rwa [hadd])
        ev104
      intro j m' hj
      cases j with
      | zero =>
        obtain rfl : m = m' := by simpa using hj
        exact Core.hashed_mono (fun cl hcl => by rw [hc145]; simp [hcl]) hhash
      | succ j =>
        have h1 := htl j m' (by simpa using hj)
        rw [show k + 1 + j = k + (j + 1) by omega] at h1
        exact Core.hashed_mono (fun cl hcl => by rw [hc145]; simp [hcl]) h1

/-- **`Ingress::build_recur_addrs` hashes every member's projection record.** -/
theorem build_recur_addrs_hashed {ms : List Ixon.MutConst} {b : Bytes.Address}
    {x_members x_block r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hms : Core.Specs.Callees.MembersRep h ms x_members)
    (hb : Bytes.RepAddressRef Core.addrTy h b x_block)
    (ev : ObsFn Obs.W "Ingress::build_recur_addrs" [x_members, x_block] h r h' cs) :
    ∀ i m, ms[i]? = some m → Hashed cs (Ixon.serConstant
      ⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b) i m, #[], #[], #[], #[]⟩) := by
  obtain ⟨cs4, ev6, hc38⟩ := Obs.«Ingress::build_recur_addrs».obs ev
  have ev6' : ObsFn Obs.W "Ingress::build_recur_addrs_walk"
      [x_members, x_block, x_members, .field ((0 : Nat) : F)] h r h' cs4 := by
    simpa using ev6
  intro i m hm
  have h1 := build_recur_addrs_walk_hashed ms (k := 0) (Nat.zero_le _) hms hb hms
    (fun j m' hj => by simpa using hj) ev6' i m hm
  rw [Nat.zero_add] at h1
  exact Core.hashed_mono (fun cl hcl => by rw [hc38]; simp [hcl]) h1

/-- **The block of an observed family check, with its types' projection records**: a non-empty
block of inductive types of the run's store, each type's projection record stored
(`Ingress::build_recur_addrs` hashes it). -/
theorem familyCall_block_members {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs) :
    ∃ cb ms, recordOf E₀ B = some cb ∧ cb.info = .muts ms ∧ 0 < ms.size ∧
      (∀ m ∈ ms.toList, ∃ ind, m = Ixon.MutConst.indc ind) ∧
      ∀ i m, ms[i]? = some m →
        recordOf E₀ (memberAddr B i m) = some (memberProjection B i m) := by
  obtain ⟨cb, ms, hcb, hms, hpos, hall⟩ := familyCall_block_indcs hS hH hfc
  refine ⟨cb, ms, hcb, hms, hpos, hall, ?_⟩
  obtain ⟨h, h', rc, xb, xrb, r, -, ⟨bB, hbB, rfl⟩, -, ev, -, hsub⟩ := hfc
  obtain ⟨C⟩ := FamilyAlias.checkFamily_chain ev
  have ext_0_453 : Heap.Extends h C.m453 :=
    (check_family_seg1_extends C.sg112).trans C.ext_m105_m453
  have hsubLoad : ∀ cl ∈ C.evLoadBlk.cs, cl ∈ calls :=
    fun cl hcl => hsub cl (C.evLoadBlk.sub cl hcl)
  obtain ⟨cb', ms', hbl, hms_rep⟩ :=
    Claim.load_block_head (Bytes.repAddressRef_heapMono₂ addrTy ext_0_453 hbB) C.evLoadBlk.obs
  obtain ⟨hBrec, hBmuts⟩ := (hbl.mono hsubLoad).stored hH
  have e1 : cb' = cb := Option.some.inj (hBrec.symm.trans hcb)
  subst e1
  have e2 : ms' = ms := Ixon.ConstantInfo.muts.inj (hBmuts.symm.trans hms)
  subst e2
  have ext_501_652 : Heap.Extends C.m501 C.m652 :=
    C.evLenMem.extends.trans (C.evIndcCnt.extends.trans C.evNParams.extends)
  have hmems652 : Core.Specs.Callees.MembersRep C.m652 ms'.toList C.members :=
    Route.membersRep_of_repMutConstList (hms_rep.mono L1.repMutConst_heapMono₂ ext_501_652)
  have hb652 : Bytes.RepAddressRef addrTy C.m652 bB xb :=
    Bytes.repAddressRef_heapMono₂ addrTy
      (ext_0_453.trans (C.evLoadBlk.extends.trans ext_501_652)) hbB
  have hhash := build_recur_addrs_hashed hmems652 hb652 C.evTypes.obs
  intro i m hm
  have hmL : ms'.toList[i]? = some m := by rw [Array.getElem?_toList]; exact hm
  obtain ⟨ind, rfl⟩ := hall m (List.mem_of_getElem? hmL)
  have hh : Hashed calls (Ixon.serConstant
      ⟨Core.Specs.Callees.memberProjInfo (ixAddr bB) i (.indc ind), #[], #[], #[], #[]⟩) :=
    Core.hashed_mono (fun cl hcl => hsub cl (C.evTypes.sub cl hcl)) (hhash i _ hmL)
  have hwf : (⟨Core.Specs.Callees.memberProjInfo (ixAddr bB) i (.indc ind), #[], #[], #[],
      #[]⟩ : Ixon.Constant).wireWF := L1.projConstant_wireWF_iPrj i.toUInt64 bB
  have hrecraw := Claim.recordOf_of_hashed hH hh (serConstant_iprj_size_lt i.toUInt64 bB)
    (Ixon.Verify.deConstantExact_serConstant _ hwf)
  rw [LoadedReads.memberAddr_eq_projAddr]
  exact hrecraw

/-- **The block's record facts, from an observed family check**: the record, its members, that
they are inductive types and their projection records are the family check's own
(`familyCall_block_members`); that the block is in Lean's logic (`hlog`) and that its
constructors' projection records are stored (`hct`) are taken. -/
theorem famBlockRecord_of_call {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hcb : recordOf E₀ B = some cb) (hms : cb.info = .muts ms) (hlog : InLogic cb)
    (hct : ∀ i ind j, ms[i]? = some (Ixon.MutConst.indc ind) → j < ind.ctors.size →
      recordOf E₀ (ctorAddr B i j) = some (constructorProjection B i j)) :
    FamBlockRecord E₀ B cb ms := by
  obtain ⟨cb', ms', hcb', hms', -, hall, hmem⟩ := familyCall_block_members hS hH hfc
  have e1 : cb' = cb := Option.some.inj (hcb'.symm.trans hcb)
  subst e1
  have e2 : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hms)
  subst e2
  exact ⟨hcb, hms, hall, hlog, hmem, hct⟩

/-! ## The family record of the block, position by position -/

/-- **The correspondence of positions, from the record's entries in the canonical reading**
(`FamilyFlat.RecordFlat`): the address `majorHeadAt` reads off recursor `k` is entry `k`'s. The
canonical reading's head and the raw reader's are one address (`FamilyCallReaders.major`), and a
valid table keys addresses injectively. -/
theorem FamilyCallReaders.major_of_recordFlat {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {B rb : _root_.Address} {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    (ht : t.check = .ok ()) (hF : FamilyCallReaders t E₀ B rb cb crb ms rs)
    {es : List FamilyFlat.FlatEntry} (hflat : FamilyFlat.RecordFlat t E₀ rb crb rs es) :
    ∀ (k : Nat) (r : Ixon.Recursor) (a : _root_.Address),
      rs[k]? = some (Ixon.MutConst.recr r) → (es.map FamilyFlat.FlatEntry.addr)[k]? = some a →
      ∃ n, majorHeadAt crb r n = some a := by
  intro k r a hk ha
  rw [List.getElem?_map] at ha
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨ty, d, hty, hd, hfn, -⟩ := hflat k r e hk he
  obtain ⟨a', hmaj, ty', d', ls, hty', hd', hfn'⟩ := hF.major k r hk
  have e1 : ty' = ty := Option.some.inj (hty'.symm.trans hty)
  subst e1
  have e2 : d' = d := Option.some.inj (hd'.symm.trans hd)
  subst e2
  rw [hfn] at hfn'
  have hkey : IxVM.Consistency.keyOf t e.addr = Core.keyOf t a' :=
    (Ix.Kernel.Expr.const.inj hfn').1
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  have haddr : e.addr = a' :=
    Core.keyOf_inj htwf ((LoadedReads.keyOf_eq t e.addr).symm.trans hkey)
  rw [haddr]
  exact hmaj

/-- **The family record of a block, position by position, from the readers of its family
check.** The block's record facts `hB`, and of the flattened family `es`: one entry per recursor
(`hcov`), the block's types first (`horig`), recursor `k`'s major premise over entry `k` in the
canonical reading (`hflat`), and each recursor's motives past the block's own types over their
entries (`haux`, the nested auxiliaries: `KernelModeled::check_carriers` reads only the motives
of the block's own types). -/
theorem familyOfBlock_of_readers {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {B rb : _root_.Address} {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    (ht : t.check = .ok ()) (hF : FamilyCallReaders t E₀ B rb cb crb ms rs)
    (hB : FamBlockRecord E₀ B cb ms) {es : List FamilyFlat.FlatEntry}
    (hcov : es.length = rs.size)
    (horig : ∀ (i : Nat) (m : Ixon.MutConst), ms[i]? = some m →
      (es.map FamilyFlat.FlatEntry.addr)[i]? = some (memberAddr B i m))
    (hflat : FamilyFlat.RecordFlat t E₀ rb crb rs es)
    (haux : ∀ (k : Nat) (r : Ixon.Recursor), rs[k]? = some (Ixon.MutConst.recr r) →
      ∀ (j : Nat) (a : _root_.Address), ms.size ≤ j →
        (es.map FamilyFlat.FlatEntry.addr)[j]? = some a →
        ∃ n, motiveCarrierAt crb r j n = some a) :
    FamilyOfBlock E₀ B cb ms rb crb rs (es.map FamilyFlat.FlatEntry.addr) where
  block := hB
  record := hF.record
  covers := by rw [List.length_map]; exact hcov
  originals := horig
  motives := fun k r hk => by rw [List.length_map, hcov]; exact hF.motives k r hk
  carriers := by
    intro k r hk j a hj
    rcases Nat.lt_or_ge j ms.size with hlt | hge
    · have hm : ms[j]? = some ms[j] := Array.getElem?_eq_getElem hlt
      have ha : a = memberAddr B j ms[j] := Option.some.inj (hj.symm.trans (horig j _ hm))
      rw [ha]
      exact hF.carriers k r hk j _ hm
    · exact haux k r hk j a hge hj
  major := fun k r a hk ha => hF.major_of_recordFlat ht hflat k r a hk ha

/-- **The family record of a block, position by position, from an observed family check** of
the block at `B` with the record at `rb`, at any limit. Of the family check itself: the family
record's facts, its motive counts, the carriers of the motives of the block's own types
(`KernelModeled::check_carriers`) and the address each major premise names
(`KernelCheck::rec_to_parent_addr`). Taken of the flattened family `es`: `hcov`, `horig`, `hflat`
and `haux` (`familyOfBlock_of_readers`); taken of the block: its record facts `hB`. -/
theorem familyOfBlock_of_call {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs)
    {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    (hB : FamBlockRecord E₀ B cb ms)
    (hrec : recordOf E₀ rb = some crb) (hmuts : crb.info = .muts rs)
    {es : List FamilyFlat.FlatEntry} (hcov : es.length = rs.size)
    (horig : ∀ (i : Nat) (m : Ixon.MutConst), ms[i]? = some m →
      (es.map FamilyFlat.FlatEntry.addr)[i]? = some (memberAddr B i m))
    (hflat : FamilyFlat.RecordFlat t E₀ rb crb rs es)
    (haux : ∀ (k : Nat) (r : Ixon.Recursor), rs[k]? = some (Ixon.MutConst.recr r) →
      ∀ (j : Nat) (a : _root_.Address), ms.size ≤ j →
        (es.map FamilyFlat.FlatEntry.addr)[j]? = some a →
        ∃ n, motiveCarrierAt crb r j n = some a) :
    FamilyOfBlock E₀ B cb ms rb crb rs (es.map FamilyFlat.FlatEntry.addr) := by
  obtain ⟨cb', crb', ms', rs', hF⟩ := familyCall_readers ht hbd hS hH hfc
  have e1 : cb' = cb := Option.some.inj (hF.blockRecord.symm.trans hB.record)
  subst e1
  have e2 : ms' = ms := Ixon.ConstantInfo.muts.inj (hF.blockMuts.symm.trans hB.muts)
  subst e2
  have e3 : crb' = crb := Option.some.inj (hF.record.record.symm.trans hrec)
  subst e3
  have e4 : rs' = rs := Ixon.ConstantInfo.muts.inj (hF.record.muts.symm.trans hmuts)
  subst e4
  exact familyOfBlock_of_readers ht hF hB hcov horig hflat haux

end IxVM.Refinement.Binding.FamilyOfCall
