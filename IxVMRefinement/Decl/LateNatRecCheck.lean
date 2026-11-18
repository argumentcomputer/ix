import IxVMRefinement.Decl.LateNatRules
import IxVMRefinement.Decl.LateFindPeer
import IxVMRefinement.Decl.LateFormerTele
import IxVMRefinement.Core.Rekey

/-! # The native recursor comparison of a late recursor

`KernelCheck::nat_rec_check(rc, rec, addr, parent, parent_addr, univ_offset)` checks a recursor
against the one the native route generates from its parent inductive: the level and the motive and
minor counts, the generated type `structRecTyR` against the declared type up to `WrapRelSem`, and
each generated rule `structRecRhsR` against the declared rule up to `WrapRelSem`. The legacy
specification (`nat_rec_check_spec`) is stated under the unrestricted load contract, at the
table's keying, at member `0` of a two-member block, and for a parent type whose raw heap term
is a syntactic telescope. Here it is restated

* with the parent at any member index `idx` of its block;
* for a standalone recursor record (its block field is its own address, so the peer search answers
  the recursor itself: `find_peer_standalone_spec`);
* for a parent type read only through `Tm` (it may hold a `let`; the former telescope then takes a
  weak head normal form: `scoped_nat_former_tele_bounded`);
* with two keyings. The type part (former telescope, motive, minors, generated type and its
  `wrap_rel`) runs under a scoped context `c` whose calls are all allowed: its terms mention only
  stored constants. The rule part (`nat_check_rules`) mentions the recursor constant itself, which
  `c.κ` does not resolve, so it runs under a second keying `κ₂` that keeps every key `c.κ`
  resolves, at a lookup `find₂` related to the loads by `WrapLoads`. -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (Expr Level LevelParam ConstantVal ConstantInfo RecRule Declaration)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- A term read through `Tm` has a raw reading: the same heap syntax with its `let` cells kept. -/
theorem lateRec_tm_raw {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p : SourceValue F}
    (rep : Tm κ d Γ h k E p) : ∃ R, RawTm κ d Γ h k R E p := by
  induction rep with
  | bvarLocal cell hs hi => exact ⟨_, .bvarLocal cell hs hi⟩
  | bvarFree cell hs hk hd => exact ⟨_, .bvarFree cell hs hk hd⟩
  | sort cell rl hu => exact ⟨_, .sort cell rl hu⟩
  | const cell ra rls hus => exact ⟨_, .const cell ra rls hus⟩
  | app cell _ _ ihf iha =>
    obtain ⟨_, hf⟩ := ihf
    obtain ⟨_, ha⟩ := iha
    exact ⟨_, .app cell hf ha⟩
  | @lam k addr tp bp lp T B ℓ cell _ _ rl iht ihb =>
    obtain ⟨_, ht⟩ := iht
    obtain ⟨_, hb⟩ := ihb
    exact ⟨_, .lam (mR := bmeta ℓ) cell ht hb rl⟩
  | @forallE k addr tp bp lp T B ℓ cell _ _ rl iht ihb =>
    obtain ⟨_, ht⟩ := iht
    obtain ⟨_, hb⟩ := ihb
    exact ⟨_, .forallE (mR := bmeta ℓ) cell ht hb rl⟩
  | letE cell _ _ _ iht ihv ihb =>
    obtain ⟨_, ht⟩ := iht
    obtain ⟨_, hv⟩ := ihv
    obtain ⟨_, hb⟩ := ihb
    exact ⟨_, .letE (mR := default) cell ht hv hb⟩
  | litNat cell rl hc => exact ⟨_, .litNat cell rl hc⟩
  | litStr cell rb hs => exact ⟨_, .litStr cell rb hs⟩
  | proj cell ra _ ihe =>
    obtain ⟨_, he⟩ := ihe
    exact ⟨_, .proj cell ra he⟩

/-- A raw reading under a keying that keeps every resolved key. -/
theorem lateRec_rawTm_rekey_mono {κ₁ κ₂ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p : SourceValue F} (rep : RawTm κ₁ d Γ h k R E p)
    (keep : ∀ x, κ₁ x ≠ unresolvedKey → κ₂ x = κ₁ x) : RawTm κ₂ d Γ h k R E p := by
  induction rep with
  | bvarLocal cell hs hi => exact .bvarLocal cell hs hi
  | bvarFree cell hs hk hd => exact .bvarFree cell hs hk hd
  | sort cell rl hu => exact .sort cell rl hu
  | @const k addr ap lsp a ls us res cell ra rls hus =>
    have e := keep (ixAddr a) res.ne
    have : Resolved (κ₂ (ixAddr a)) := ⟨by rw [e]; exact res.ne⟩
    rw [← e]
    exact .const cell ra rls hus
  | app cell _ _ ihf iha => exact .app cell ihf iha
  | lam cell _ _ rl iht ihb => exact .lam cell iht ihb rl
  | forallE cell _ _ rl iht ihb => exact .forallE cell iht ihb rl
  | letE cell _ _ _ iht ihv ihb => exact .letE cell iht ihv ihb
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | @proj k addr ap ep a i Re E res pm cell ra _ ih =>
    have e := keep (ixAddr a) res.ne
    have : Resolved (κ₂ (ixAddr a)) := ⟨by rw [e]; exact res.ne⟩
    have : ProjPermitted κ₂ (ixAddr a) := ProjPermitted.of_keep keep pm
    rw [← e]
    exact .proj cell ra ih

/-- The constructor load witness at member `idx` under a keying that keeps every key the first
resolves, when the member's constructor projections resolve under the first. -/
theorem NatCtorLoadI.rekey_mono {κ₁ κ₂ : _root_.Address → KKey} {b₀ : Bytes.Address}
    {idx k : Nat} {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)}
    {x_block : SourceValue F} {cs : List (Call F)}
    (hload : NatCtorLoadI κ₁ b₀ idx k ctors_info x_block cs)
    (keep : ∀ x, κ₁ x ≠ unresolvedKey → κ₂ x = κ₁ x)
    (hCres : ∀ i, i < ctors_info.length → κ₁ (cprjAddr (ixAddr b₀) idx i) ≠ unresolvedKey) :
    NatCtorLoadI κ₂ b₀ idx k ctors_info x_block cs := by
  intro j hj p9 hp m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50 hs hb ev ld info hinfo
  obtain ⟨h1, h2, h3⟩ :=
    hload j hj p9 hp m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50 hs hb ev ld info hinfo
  exact ⟨h1.trans (keep _ (hCres j hj)).symm, h2, lateRec_rawTm_rekey_mono h3 keep⟩

private theorem lateRec_getAppFn_mkAppN_eq : ∀ (As : List KExpr) (f : KExpr),
    (Expr.mkAppN f As).getAppFn = f.getAppFn
  | [], _ => rfl
  | a :: As, f => by
    show (Expr.mkAppN (.app f a) As).getAppFn = f.getAppFn
    rw [lateRec_getAppFn_mkAppN_eq As (.app f a)]
    rfl

private theorem lateRec_nat_app_n_head {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} :
    ∀ {Args : List KExpr} {a : Bytes.Address} {ls : List KLevel} {pf pargs r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      AppHeadConstLvls h a ls pf →
      RepList kexprListEnum (fun h E p => Tm κ d Γ h k E p) h Args pargs →
      ObsFn W "KernelCheck::nat_app_n" [pf, pargs] h r h' cs →
      AppHeadConstLvls h' a ls r := by
  intro Args
  induction Args with
  | nil =>
    intro a ls pf pargs r h h' cs hf hargs ev
    match Obs.«KernelCheck::nat_app_n».obs ev with
    | .Nil (he21 := hr) (he22 := hh) .. =>
      subst hr hh; exact hf
    | .Cons (ld12 := ld12) .. =>
      have ld12' : loadValue h pargs = .ok (.construct kexprListEnum "Cons" [_, _]) := ld12
      cases hargs with | nil cell => exact (load_cell_ne cell ld12' (by decide)).elim
  | cons _ _ ih =>
    intro a ls pf pargs r h h' cs hf hargs ev
    match Obs.«KernelCheck::nat_app_n».obs ev with
    | .Nil (ld12 := ld12) .. =>
      have ld12' : loadValue h pargs = .ok (.construct kexprListEnum "Nil" []) := ld12
      cases hargs with | cons cell _ _ => exact (load_cell_ne cell ld12' (by decide)).elim
    | .Cons (m50 := m50) (ld12 := ld12) (hm58 := hm58) (ev46 := ev46) .. =>
      obtain ⟨_, _, heq, _, has⟩ := RepList.cons_of_load hargs ld12
      injection heq with h1 h2; subst h1 h2
      have ext50 : Heap.Extends h m50 := by rw [hm58]; exact Heap.Extends.snoc _ _
      have happ : AppHeadConstLvls m50 a ls (.ptr (.enum kexprEnum) h.length) := by
        rw [hm58]
        exact .app (by simp; rfl) (hf.mono (Heap.Extends.snoc _ _))
      exact ih happ (tmRepList_mono ext50 has) ev46

private theorem lateRec_forallDomHeadLvls_replace_pis
    {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {T : KKey} {a : Bytes.Address} {ls : List KLevel} {m : Nat} :
    ∀ (cnt : Nat) {k : Nat} {tele : KExpr} {ppw ptele pb r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      cnt < 2147483648 →
      Tm κ d Γ h k tele ptele →
      ForallDomHeadLvls κ d Γ h T a ls m (k + cnt) pb →
      ObsFn W "KernelCheck::nat_replace_pis"
        [ppw, .field (cnt : F), ptele, pb, .field 0] h r h' cs →
      ForallDomHeadLvls κ d Γ h' T a ls (cnt + m) k r
  | 0, k, _, _, _, _, _, _, _, _, _, _, hpb, ev => by
    match Obs.«KernelCheck::nat_replace_pis».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh
      simpa [Nat.zero_add] using hpb
    | .other_n0 (hne19 := hne) .. => exact (hne rfl).elim
    | .other_other (hne19 := hne) .. => exact (hne rfl).elim
  | cnt + 1, k, tele, ppw, ptele, pb, r, h, h', cs, hcnt, htele, hpb, ev => by
    have hne0 : (.field ((cnt + 1 : Nat) : F) : SourceValue F) ≠ .field 0 :=
      succ_field_ne_zero (by omega)
    match Obs.«KernelCheck::nat_replace_pis».obs ev with
    | .n0 (hv14 := hv) .. =>
      exact absurd hv hne0
    | .other_other (hne163 := hne) .. =>
      exact (hne rfl).elim
    | .other_n0 (x_ty := xty) (v54 := v54) (m55 := m55) (ld33 := ld) (op93 := op) (ev67 := ev')
        (he134 := hr) (hm133 := hm) .. =>
      subst hr hm
      obtain ⟨_, B, _, rfl, _, hb, _⟩ := htele.forallE_of_load ld
      rw [evalBinOp_sub_succ cnt op] at ev'
      have hpb' : ForallDomHeadLvls κ d Γ h T a ls m ((k + 1) + cnt) pb := by
        rwa [show (k + 1) + cnt = k + (cnt + 1) by omega]
      have ih_out := lateRec_forallDomHeadLvls_replace_pis cnt (by omega) hb hpb' ev'
      have hsucc :
          ForallDomHeadLvls κ d Γ
            (m55 ++ [.construct kexprEnum "Forall" [xty, v54, ppw]])
            T a ls ((cnt + m) + 1) k (.ptr (.enum kexprEnum) m55.length) :=
        .succ (by simp; exact ⟨rfl, rfl⟩) (ih_out.mono (Heap.Extends.snoc _ _))
      rwa [show (cnt + 1) + m = (cnt + m) + 1 by omega]

/-- **The native recursor comparison of a late recursor.** `KernelCheck::nat_rec_check` on a
standalone recursor record and its parent inductive at member `idx` of its block verifies the
level count, the motive and minor counts, the generated type `structRecTyR` against the declared
type up to `WrapRelSem c.env.find?` (under the scoped context `c`), and every generated rule
`structRecRhsR` against the declared rule up to `WrapRelSem find₂` (under the keying `κ₂`, which
keeps every key `c.κ` resolves and resolves the recursor). -/
theorem late_nat_rec_check_spec {c : ScopedCtx} (hc : ScopedCoreFacts c)
    (hall : ∀ cl, c.allowed cl)
    {κ₂ : _root_.Address → KKey} {find₂ : KKey → Option (ConstantInfo .anon)}
    (hkeep : ∀ x, c.κ x ≠ unresolvedKey → κ₂ x = c.κ x)
    (hwl₂ : WrapLoads c.toCtx κ₂ find₂)
    {cst : Ixon.Constant} {rc' : Ixon.Recursor}
    {T recC : KKey} {b₀ bT bRec bRB : Bytes.Address} {idx k nP nIdx : Nat} {large : Bool}
    {tty₀ rec_ty₀ : KExpr}
    {tbs₀ : List (KExpr × Ix.Kernel.BinderMeta)} {tsort₀ : KExpr}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)}
    {rls : List (RecRule .anon)}
    {x_rc x_nlvls x_ty x_n_mot x_n_min x_rules w_k w_u x_rec_blk w_ridx : SourceValue F}
    {x_pty w_p1 w_p2 w_pu x_block : SourceValue F}
    {x_addr x_parent_addr r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    [Resolved (κ₂ (ixAddr bRec))]
    (hT_ind : ∃ cv caps, c.env.find? T = some (.indInfo cv caps))
    (hrecblk : Ix.Cert.recordAt c.E (ixAddr bRB) = some cst)
    (hcst : cst.info = .recr rc')
    (hT : c.κ (ixAddr bT) = T)
    (hκ₂_inj : ∀ a : Bytes.Address, κ₂ (ixAddr a) = T → a = bT)
    (hRec : κ₂ (ixAddr bRec) = recC)
    (hidx : idx < 4294967296)
    (hCres : ∀ i, i < ctors_info.length → c.κ (cprjAddr (ixAddr b₀) idx i) ≠ unresolvedKey)
    (hk_lt : k < 2147483648)
    (hnP_lt : nP < 2147483648)
    (hnIdx_lt : nIdx < 2147483648)
    (hnCtors_lt : ctors_info.length < 2147483648)
    (hnall_lt : nP + 1 + ctors_info.length + nIdx + 1 < 4294967296)
    (hlps_tty : tty₀.allLevelParamsDefined (List.range k) = true)
    (hsT₀ : tty₀.stripPis (nP + nIdx) = some (tbs₀, tsort₀))
    (hwf_all : ∀ info ∈ ctors_info,
      NatCtorInfoWf T k large nP nIdx ctors_info.length info)
    (hrls_len : rls.length = ctors_info.length)
    (hload : NatCtorLoadI c.κ b₀ idx k ctors_info x_block cs)
    (hgood : CoreGood c cs)
    (hrc : RCRep c.t c.lim h x_rc)
    (hb₀_blk : Bytes.RepAddressRef addrTy h b₀ x_block)
    (hbRB : Bytes.RepAddressRef addrTy h bRB x_rec_blk)
    (hbT : Bytes.RepAddressRef addrTy h bT x_parent_addr)
    (hbRec : Bytes.RepAddressRef addrTy h bRec x_addr)
    (hpty : Tm c.κ 0 (fun _ => default) h 0 tty₀ x_pty)
    (hrec_ty : Tm c.κ 0 (fun _ => default) h 0
      (posOf (if large then k :: List.range k else List.range k) rec_ty₀) x_ty)
    (hrules : RulesRep κ₂ h
      (if large then k :: List.range k else List.range k) 0 x_rules rls)
    (ev : ObsFn W "KernelCheck::nat_rec_check"
      [x_rc,
        .construct kciEnum "Rec"
          [x_nlvls, x_ty, .field (nP : F), .field (nIdx : F), x_n_mot, x_n_min,
            x_rules, w_k, w_u, x_rec_blk, w_ridx],
        x_addr,
        .construct kciEnum "Induct"
          [.field (k : F), x_pty, w_p1, w_p2, .field (ctors_info.length : F),
            w_pu, x_block, .field (idx : F)],
        x_parent_addr,
        .field ((if large then 1 else 0 : Nat) : F)]
      h r h' cs) :
    let rlps := if large then k :: List.range k else List.range k
    let elim := if large then k else 0
    let ctors₀ := ctors_info.map (fun info => (info.1, info.2.1, info.2.2.2.1, info.2.2.2.2))
    x_nlvls = .field (rlps.length : F) ∧
    x_n_mot = .field 1 ∧
    x_n_min = .field (ctors_info.length : F) ∧
    (∃ recTy,
      Ix.Kernel.structRecTyR T (List.range k) elim large nP nIdx tty₀ ctors₀ = some recTy ∧
      WrapRelSem c.env.find? recTy rec_ty₀) ∧
    (∀ a_d ls_d,
      ForallRightHeadLvls h a_d ls_d (nP + 1 + ctors_info.length + nIdx) x_ty →
      ls_d = (List.range k).map (fun i => Level.param ((if large then 1 else 0) + i))) ∧
    ∀ j (hlt : j < rls.length) (hj : j < ctors_info.length),
      (rls[j]'hlt).nfields = (ctors_info[j]'hj).2.1 ∧
      ∃ rhsG,
        Ix.Kernel.structRecRhsR T (List.range k) elim large nP nIdx tty₀ ctors₀
          recC (rlps.map .param) j = some rhsG ∧
        WrapRelSem find₂ rhsG (rls[j]'hlt).rhs := by
  intro rlps elim ctors₀
  dsimp only [rlps, elim, ctors₀]
  -- The keys of the parent and of the member's constructors under both keyings
  have hTres : c.κ (ixAddr bT) ≠ unresolvedKey := by
    obtain ⟨cvT, capsT, hfindT⟩ := hT_ind
    have hf : c.env.find? (c.κ (ixAddr bT)) = some (.indInfo cvT capsT) := by
      rw [hT]; exact hfindT
    exact hc.res_of_find hf
  have hTinst : Resolved (c.κ (ixAddr bT)) := ⟨hTres⟩
  have hT₂ : κ₂ (ixAddr bT) = T := (hkeep _ hTres).trans hT
  have hκ_inj : ∀ a : Bytes.Address, c.κ (ixAddr a) = T → a = bT := by
    intro a ha
    have hres : c.κ (ixAddr a) ≠ unresolvedKey := by rw [ha, ← hT]; exact hTres
    exact hκ₂_inj a ((hkeep _ hres).trans ha)
  have hCres₂ : ∀ i, i < ctors_info.length → κ₂ (cprjAddr (ixAddr b₀) idx i) ≠ unresolvedKey := by
    intro i hi
    rw [hkeep _ (hCres i hi)]
    exact hCres i hi
  have hload₂ : NatCtorLoadI κ₂ b₀ idx k ctors_info x_block cs := hload.rekey_mono hkeep hCres
  have hwl₁ : WrapLoads c.toCtx c.κ c.env.find? := WrapLoads.of_scoped hc.loads hall
  have hbnd : IxVM.Consistency.Bounded cs := hgood.bounded
  let n := ctors_info.length
  let uoff := if large then 1 else 0
  let ℓ_c : KLevel := if large then Level.param 0 else Level.zero
  let rlps' := if large then k :: List.range k else List.range k
  let clvls := (List.range k).map (fun idx => Level.param (uoff + idx))
  have hrlps_len : k + uoff = rlps'.length := by
    dsimp only [uoff, rlps']
    cases large <;> simp
  rcases Obs.«KernelCheck::nat_rec_check».obs ev with
    ⟨x_nlvls', x_ty', x_n_p', x_n_i', x_n_mot', x_n_min', x_rules', w13, w14, x_rec_blk', w15,
      x_pnlvls', x_pty', w83, w84, x_num_ctors', w85, x_block', x_idx',
      v138, v218, m219, cs229, v298, m299, cs301, m308, m324, v381, m382, cs384,
      v390, m391, cs401, v406, m439, v451, m452, cs462, m482, v512, m513, cs523,
      v527, m536, cs544, v547, v548, m550, cs558, m578, cs586, v604, m605, cs615,
      m645, m668, v701, m702, cs712, v716, m725, cs733, v736, v737, m739, cs747,
      v750, x758, m784, cs792, v810, m811, cs821, v825, m827, v839, x846, m865, cs873,
      v876, m879, cs887, m906, v925, m926, cs936, v941, m959, cs967, v971, m1002,
      v1044, m1045, cs1055, v1152, m1153, cs1163, m1193, v1246, m1249, cs1257,
      v1283, m1284, cs1294, m1317, cs1345, v1361, m1455, cs1463,
      hv11, hv81, op159, heq162, heq189, heq217, ev231, sg306, hm318, hm332, sg389,
      op435, hm447, ev403, ev464, hm492, ev560, ev588, ev546, ev525, hm653, hm676, ev617,
      op773, op765, ev749, ev794, ev735, ev714, hm835, op861, op853, ev889, hm914, ev875, ev823,
      op993, ev969, hm1010, ev938, ev1057, hm1201, ev1165, ev1259, heq1282,
      hm1325, ev1296, ev1465, ev1347, hcalls⟩
  subst hcalls
  -- Unify `Rec` and `Induct` constructor fields
  injection hv11 with _ _ hr_args
  injection hr_args with h1 hr_args; injection hr_args with h2 hr_args
  injection hr_args with h3 hr_args; injection hr_args with h4 hr_args
  injection hr_args with h5 hr_args; injection hr_args with h6 hr_args
  injection hr_args with h7 hr_args; injection hr_args with _ hr_args
  injection hr_args with _ hr_args; injection hr_args with h10 _
  subst h1 h2 h3 h4 h5 h6 h7 h10
  injection hv81 with _ _ hp_args
  injection hp_args with hp1 hp_args; injection hp_args with hp2 hp_args
  injection hp_args with _ hp_args; injection hp_args with _ hp_args
  injection hp_args with hp5 hp_args; injection hp_args with _ hp_args
  injection hp_args with hp7 hp_args; injection hp_args with hp8
  subst hp1 hp2 hp5 hp7 hp8
  -- Header equalities
  have hv138_eq : v138 = .field (rlps'.length : F) := by
    rw [evalBinOp_add_nat k uoff op159, hrlps_len]
  have hnlvls_eq : x_nlvls = .field (rlps'.length : F) := heq162.trans hv138_eq
  -- Step 1: `clvls`, `pw` (`Seg1`), `never = .succ .zero`, and `Seg2` (`v381`)
  have hlps_219 : RepKLevelList m219 clvls v218 :=
    nat_build_param_lvls_range_spec
      (by dsimp only [uoff]; cases large <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
        have := hk_lt <;> omega)
      ev231
  have hseg1 : RepKLevel m299 ℓ_c v298 ∧ Heap.Extends m219 m299 ∧ cs301 = [] := by
    cases sg306 with
    | n1 hv268 he273 hm272 hc284 =>
      subst he273 hm272 hc284
      have hl_true : large = true := by
        cases large with
        | true => rfl
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_zero] at hv268
          exact absurd (Value.field.inj hv268.symm) one_ne_zero
      subst hl_true
      exact ⟨(RepKLevel.allocParam m219 (by decide : 0 < 4294967296)).1,
        Heap.Extends.snoc _ _, rfl⟩
    | other hne285 he293 hm292 hc297 =>
      subst he293 hm292 hc297
      have hl_false : large = false := by
        cases large with
        | false => rfl
        | true => exact absurd rfl hne285
      subst hl_false
      exact ⟨(RepKLevel.allocZero m219).1, Heap.Extends.snoc _ _, rfl⟩
  rcases hseg1 with ⟨hpw_299, ext_219_299, hcs301⟩
  subst hcs301
  have ext_299_324 : Heap.Extends m299 m324 := by rw [hm332]; exact Heap.Extends.snoc _ _
  have ext_324_308 : Heap.Extends m324 m308 := by rw [hm318]; exact Heap.Extends.snoc _ _
  have hzero_324 : RepKLevel m324 .zero (.ptr (.enum "KernelTypes::KLevelNode") m299.length) := by
    rw [hm332]; exact (RepKLevel.allocZero m299).1
  have hnever_308 : RepKLevel m308 (.succ .zero)
      (.ptr (.enum "KernelTypes::KLevelNode") m324.length) := by
    rw [hm318]; exact (RepKLevel.allocSucc hzero_324).1
  have ext_h_308 := ev231.heap_extends.trans
    (ext_219_299.trans (ext_299_324.trans ext_324_308))
  have hseg2 : Tm c.κ 0 (fun _ => default) m382 0 (posOf rlps' tty₀) v381 ∧
      Heap.Extends m308 m382 := by
    cases sg389 with
    | n0 hv349 he351 he352 hc353 =>
      subst he351 he352 hc353
      have hl_false : large = false := by
        cases large with
        | false => rfl
        | true =>
          simp only [↓reduceIte, Nat.cast_one] at hv349
          exact absurd (Value.field.inj hv349) one_ne_zero
      subst hl_false
      refine ⟨?_, Heap.Extends.refl _⟩
      dsimp only [rlps']
      simp only [Bool.false_eq_true, ↓reduceIte, posOf_range]
      exact hpty.mono ext_h_308
    | other cs_inst hne354 ev_inst hc_inst =>
      have hl_true : large = true := by
        cases large with
        | true => rfl
        | false => exact absurd rfl hne354
      subst hl_true
      have hbnd_inst : IxVM.Consistency.Bounded cs_inst :=
        RomBound.bounded_mono hbnd (fun x hx => by rw [hc_inst]; simp [hx])
      have hlps_308 := RepKLevelList.mono hlps_219
        (ext_219_299.trans (ext_299_324.trans ext_324_308))
      have hlv_rep : LvListRep m308 ((List.range k).map (fun idx => Level.param (1 + idx))) v218 :=
        ⟨_, hlps_308, LvEqList.refl _⟩
      obtain ⟨Rp, hRp⟩ := lateRec_tm_raw hpty
      have hinst := expr_inst_levels_rawTm hbnd_inst (hRp.mono ext_h_308) hlv_rep ev_inst
      simp only [List.length_map, List.length_range] at hinst
      have hinst_tm := hinst.toTm
      dsimp only [rlps']
      simp only [↓reduceIte]
      rw [posOf_large_eq_inst_shifted k hlps_tty]
      exact ⟨hinst_tm, ev_inst.heap_extends⟩
  rcases hseg2 with ⟨htm_381, ext_308_382⟩
  -- Step 2: `nat_former_tele` (through `whnf` at a non-binder node) + `peel_n_foralls`
  rw [evalBinOp_add_nat nP nIdx op435] at ev403
  have ext_382_439 : Heap.Extends m382 m439 := by rw [hm447]; exact Heap.Extends.snoc _ _
  have hsT_all := ilp_stripPis rlps' (posLevels rlps') (nP + nIdx) hsT₀
  change (posOf rlps' tty₀).stripPis (nP + nIdx) = _ at hsT_all
  have hs_isSome : ((posOf rlps' tty₀).stripPis (nP + nIdx)).isSome = true := by
    simp [hsT_all]
  have htypes : TypesRep c.κ (fun _ => default) m439 0
      (.ptr (.enum kexprListEnum) m382.length) := by
    rw [hm447]
    exact typesRep_alloc_nil c.κ (fun _ => default) m382
  have ext_h_439 : Heap.Extends h m439 := ext_h_308.trans (ext_308_382.trans ext_382_439)
  have hgood_ft : CoreGood c cs401 := hgood.sub (fun x hx => by simp [hx])
  obtain ⟨_, htty_390⟩ := scoped_nat_former_tele_bounded hc (nP + nIdx) (by omega) hs_isSome
    (hrc.mono ext_h_439) htypes (ghostScoped_zero _) hgood_ft (htm_381.mono ext_382_439) ev403
  obtain ⟨hm452_eq, tbsP, itele_pos, hsT_pos, _, hitele0⟩ :=
    peel_n_foralls_tm_spec nP (by omega) htty_390 ev464
  have hitele_tm : Tm c.κ 0 (fun _ => default) m452 nP itele_pos v451 := by
    rw [hm452_eq]
    simpa [Nat.zero_add] using hitele0
  -- Step 3: `motive_ty` (`v604`)
  have ext_308_452 : Heap.Extends m308 m452 := by
    rw [hm452_eq]
    exact ext_308_382.trans (ext_382_439.trans ev403.heap_extends)
  have ext_452_482 : Heap.Extends m452 m482 := by rw [hm492]; exact Heap.Extends.snoc _ _
  have ext_h_482 := ext_h_308.trans (ext_308_452.trans ext_452_482)
  have hT_const1 : Tm c.κ 0 (fun _ => default) m482 (nP + nIdx) (.const T clvls)
      (.ptr (.enum kexprEnum) m452.length) := by
    rw [← hT]
    exact .const (by rw [hm492]; simp)
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_482 hbT)
      (RepKLevelList.mono hlps_219
        (ext_219_299.trans (ext_299_324.trans (ext_324_308.trans (ext_308_452.trans ext_452_482)))))
      (LvEqList.refl _)
  have hps_m1 := nat_ps_at_spec (κ := c.κ) (d := 0) (Γ := fun _ => default)
    nP nIdx (nP + nIdx) (by omega) (by omega) ev560
  have hps_m2 := nat_ps_at_spec (κ := c.κ) (d := 0) (Γ := fun _ => default)
    nIdx 0 (nP + nIdx) (by omega) (by omega) ev588
  have hcat_m := kexpr_list_concat_spec' ev546 (tmRepList_mono ev588.heap_extends hps_m1) hps_m2
  have ext_482_536 := ev560.heap_extends.trans (ev588.heap_extends.trans ev546.heap_extends)
  have hfam_m := nat_app_n_spec (hT_const1.mono ext_482_536) hcat_m ev525
  have hfam_m' : Tm c.κ 0 (fun _ => default) m513 (nP + nIdx)
      (cFamI T clvls nP nIdx 0 0) v512 := by
    simpa [cFamI] using hfam_m
  have ext_513_668 : Heap.Extends m513 m668 := by rw [hm676]; exact Heap.Extends.snoc _ _
  have ext_668_645 : Heap.Extends m668 m645 := by rw [hm653]; exact Heap.Extends.snoc _ _
  have ext_308_513 := ext_308_452.trans
    (ext_452_482.trans (ext_482_536.trans ev525.heap_extends))
  have ext_299_513 := ext_299_324.trans (ext_324_308.trans ext_308_513)
  have hsrt_668 : Tm c.κ 0 (fun _ => default) m668 (nP + nIdx + 1) (.sort ℓ_c)
      (.ptr (.enum kexprEnum) m513.length) := by
    exact .sort (by rw [hm676]; simp)
      (repKLevel_heapMono₂ (ext_299_513.trans ext_513_668) hpw_299)
      (fun _ => rfl)
  have ext_308_645 := ext_308_513.trans (ext_513_668.trans ext_668_645)
  have hnever_645 := repKLevel_heapMono₂ ext_308_645 hnever_308
  have hmot_body_645 : Tm c.κ 0 (fun _ => default) m645 (nP + nIdx)
      (.forallE (cFamI T clvls nP nIdx 0 0) (.sort ℓ_c) { pw := .never })
      (.ptr (.enum kexprEnum) m668.length) := by
    exact .forallE (by rw [hm653]; simp)
      (hfam_m'.mono (ext_513_668.trans ext_668_645))
      (hsrt_668.mono ext_668_645)
      hnever_645
  have ext_452_645 := ext_452_482.trans
    (ext_482_536.trans (ev525.heap_extends.trans (ext_513_668.trans ext_668_645)))
  obtain ⟨motiveTy, hmot_ite, hmot_tm⟩ :=
    nat_replace_pis_spec nIdx (by omega) hnever_645
      (hitele_tm.mono ext_452_645) hmot_body_645 ev617
  simp only [↓reduceIte] at hmot_ite
  have hmot_eq : cMotiveTyI T clvls ℓ_c nP nIdx itele_pos = some motiveTy := hmot_ite
  -- Step 4: `major` (`v925`)
  rw [evalBinOp_add_one n op773] at op765
  rw [evalBinOp_add_nat (n + 1) nIdx op765] at ev749
  have hps_j1 := nat_ps_at_spec (κ := c.κ) (d := 0) (Γ := fun _ => default)
    nP (n + 1 + nIdx) (nP + (n + 1) + nIdx) (by omega) (by omega) ev749
  have hps_j2 := nat_ps_at_spec (κ := c.κ) (d := 0) (Γ := fun _ => default)
    nIdx 0 (nP + (n + 1) + nIdx) (by omega) (by omega) ev794
  have hcat_j := kexpr_list_concat_spec' ev735 (tmRepList_mono ev794.heap_extends hps_j1) hps_j2
  have ext_482_725 := ext_482_536.trans (ev525.heap_extends.trans (ext_513_668.trans
    (ext_668_645.trans (ev617.heap_extends.trans (ev749.heap_extends.trans
      (ev794.heap_extends.trans ev735.heap_extends))))))
  have hT_const2 : Tm c.κ 0 (fun _ => default) m725 (nP + (n + 1) + nIdx)
      (.const T clvls) (.ptr (.enum kexprEnum) m452.length) := by
    rw [← hT]
    exact .const (ext_482_725.getElem?_eq (by rw [hm492]; simp))
      (Bytes.repAddressRef_heapMono₂ addrTy (ext_h_482.trans ext_482_725) hbT)
      (RepKLevelList.mono hlps_219
        (ext_219_299.trans (ext_299_324.trans (ext_324_308.trans
          (ext_308_452.trans (ext_452_482.trans ext_482_725))))))
      (LvEqList.refl _)
  have hfam_j := nat_app_n_spec hT_const2 hcat_j ev714
  have hT_head2 : AppHeadConstLvls m725 bT clvls (.ptr (.enum kexprEnum) m452.length) :=
    .const (ext_482_725.getElem?_eq (by rw [hm492]; simp))
      (Bytes.repAddressRef_heapMono₂ addrTy (ext_h_482.trans ext_482_725) hbT)
      (RepKLevelList.mono hlps_219
        (ext_219_299.trans (ext_299_324.trans (ext_324_308.trans
          (ext_308_452.trans (ext_452_482.trans ext_482_725))))))
  have hfam_head := lateRec_nat_app_n_head hT_head2 hcat_j ev714
  have hfam_j' : Tm c.κ 0 (fun _ => default) m702 (nP + (n + 1) + nIdx)
      (cFamI T clvls nP nIdx (n + 1) 0) v701 := by
    simpa [cFamI] using hfam_j
  rw [evalBinOp_add_nat nIdx n op861] at op853
  rw [evalBinOp_add_one (nIdx + n) op853] at hm835
  have ext_702_827 : Heap.Extends m702 m827 := by rw [hm835]; exact Heap.Extends.snoc _ _
  have hbvar_mot_j : Tm c.κ 0 (fun _ => default) m827 (nP + (n + 1) + nIdx + 1)
      (.bvar (nIdx + n + 1)) (.ptr (.enum kexprEnum) m702.length) := by
    rw [hm835]
    exact tm_bvarLocal_nat (by simp) (by dsimp only [n]; omega) (by dsimp only [n]; omega)
  have hps_idx1 := nat_ps_at_spec (κ := c.κ) (d := 0) (Γ := fun _ => default)
    nIdx 1 (nP + (n + 1) + nIdx + 1) (by omega) (by dsimp only [n]; omega) ev889
  have ext_879_906 : Heap.Extends m879 m906 := by rw [hm914]; exact Heap.Extends.snoc _ _
  have hbvar0_906 : Tm c.κ 0 (fun _ => default) m906 (nP + (n + 1) + nIdx + 1)
      (.bvar 0) (.ptr (.enum kexprEnum) m879.length) := by
    rw [hm914]
    exact tm_bvarLocal_nat (n := 0) (by simp) (by omega) (by omega)
  have hsnoc_j := SubstAux.ksnoc
    (R := fun h E p => Tm c.κ 0 (fun _ => default) h (nP + (n + 1) + nIdx + 1) E p)
    (fun _ _ _ _ ext r => Tm.mono ext r) ev875
    (tmRepList_mono ext_879_906 hps_idx1) hbvar0_906
  have ext_827_865 := ev889.heap_extends.trans (ext_879_906.trans ev875.heap_extends)
  have hmot_app_j := nat_app_n_spec (hbvar_mot_j.mono ext_827_865) hsnoc_j ev823
  rw [evalBinOp_add_one n op993] at ev969
  have hbnd_lj : IxVM.Consistency.Bounded cs967 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have ext_702_811 := ext_702_827.trans (ext_827_865.trans ev823.heap_extends)
  have ext_452_811 := ext_452_482.trans
    (ext_482_725.trans (ev714.heap_extends.trans ext_702_811))
  have hitele_lift := expr_lift_local_spec (Nat.zero_le nP) (by omega) (by decide)
    hbnd_lj (hitele_tm.mono ext_452_811) ev969
  have ext_959_1002 : Heap.Extends m959 m1002 := by rw [hm1010]; exact Heap.Extends.snoc _ _
  have ext_299_1002 := ext_299_513.trans (ext_513_668.trans (ext_668_645.trans
    (ev617.heap_extends.trans (ev749.heap_extends.trans (ev794.heap_extends.trans
      (ev735.heap_extends.trans (ev714.heap_extends.trans
        (ext_702_811.trans (ev969.heap_extends.trans ext_959_1002)))))))))
  have hpw_1002 := repKLevel_heapMono₂ ext_299_1002 hpw_299
  have hmaj_core : Tm c.κ 0 (fun _ => default) m1002 ((nP + (n + 1)) + nIdx)
      (.forallE (cFamI T clvls nP nIdx (n + 1) 0)
        (Expr.mkAppN (.bvar (nIdx + n + 1)) (Ix.Kernel.structPsAt 1 nIdx ++ [.bvar 0]))
        { pw := ℓ_c.zeronessOf })
      (.ptr (.enum kexprEnum) m959.length) := by
    exact .forallE (by rw [hm1010]; simp)
      (hfam_j'.mono (ext_702_811.trans (ev969.heap_extends.trans ext_959_1002)))
      (hmot_app_j.mono (ev969.heap_extends.trans ext_959_1002))
      hpw_1002
  have hmaj_core_head :
      ForallDomHeadLvls c.κ 0 (fun _ => default) m1002
        T bT clvls 0 ((nP + (n + 1)) + nIdx) (.ptr (.enum kexprEnum) m959.length) :=
    .zero (by rw [hm1010]; simp; exact ⟨rfl, rfl⟩)
      (hfam_j'.mono (ext_702_811.trans (ev969.heap_extends.trans ext_959_1002)))
      (by simp [cFamI, lateRec_getAppFn_mkAppN_eq]; rfl)
      (hfam_head.mono (ext_702_811.trans (ev969.heap_extends.trans ext_959_1002)))
  obtain ⟨major, hmaj_ite, hmaj_tm⟩ :=
    nat_replace_pis_spec nIdx (by omega) hpw_1002
      (hitele_lift.mono ext_959_1002) hmaj_core ev938
  have hmaj_head :=
    lateRec_forallDomHeadLvls_replace_pis nIdx (by omega)
      (hitele_lift.mono ext_959_1002) hmaj_core_head ev938
  simp only [↓reduceIte] at hmaj_ite
  have hmaj_tm' : Tm c.κ 0 (fun _ => default) m926 (nP + 1 + n) major v925 := by
    rwa [show nP + 1 + n = nP + (n + 1) by omega]
  have hmaj_head' :
      ForallDomHeadLvls c.κ 0 (fun _ => default) m926
        T bT clvls nIdx (nP + 1 + n) v925 := by
    rwa [show nIdx = nIdx + 0 by omega, show nP + 1 + n = nP + (n + 1) by omega]
  -- Step 5: `nat_minors` (`isLam = false`) + outer `Forall` + `nat_replace_pis` (`recTy_c`)
  have ext_299_926 := ext_299_1002.trans ev938.heap_extends
  have ext_h_926 := ev231.heap_extends.trans (ext_219_299.trans ext_299_926)
  have hload_min : NatCtorLoadI c.κ b₀ idx k ctors_info x_block cs1055 :=
    hload.mono_calls (fun x hx => by simp [hx])
  have hgood_min : Good c.toCtx cs1055 := hgood.raw.sub (fun x hx => by simp [hx])
  have hbnd_min : IxVM.Consistency.Bounded cs1055 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have ev1057' : ObsFn W "KernelCheck::nat_minors"
      [x_block, .field (idx : F), x_parent_addr, v218, .field (nP : F), .field (nIdx : F), v298,
        .field (n : F), .field ((if large then 1 else 0 : Nat) : F),
        .field ((0 : Nat) : F), v925, .field ((if false then 1 else 0 : Nat) : F)]
      m926 v1044 m1045 cs1055 := by
    simpa using ev1057
  obtain ⟨minors, hmin_eq, hmin_tm⟩ :=
    natI_minors_spec (c := c.toCtx) hT hκ_inj hidx hCres (by omega) hwf_all n 0 (by omega)
      hload_min hgood_min hbnd_min
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_926 hb₀_blk)
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_926 hbT)
      (RepKLevelList.mono hlps_219 (ext_219_299.trans ext_299_926))
      (repKLevel_heapMono₂ ext_299_926 hpw_299)
      hmaj_tm' ev1057'
  have hmin_head :=
    natI_forallDomHeadLvls_minors (κ := c.κ) (idx := idx) (nIdx := nIdx) (large := large)
      (by omega) n 0 (by omega) hmaj_head' (by simpa using ev1057)
  simp only [Bool.false_eq_true, ↓reduceIte, List.drop_zero, Nat.add_zero] at hmin_eq hmin_tm hmin_head
  have ext_1045_1193 : Heap.Extends m1045 m1193 := by rw [hm1201]; exact Heap.Extends.snoc _ _
  have ext_605_1193 := ev749.heap_extends.trans (ev794.heap_extends.trans
    (ev735.heap_extends.trans (ev714.heap_extends.trans (ext_702_811.trans
      (ev969.heap_extends.trans (ext_959_1002.trans (ev938.heap_extends.trans
        (ev1057.heap_extends.trans ext_1045_1193))))))))
  have ext_299_1193 := ext_299_926.trans (ev1057.heap_extends.trans ext_1045_1193)
  have hpw_1193 := repKLevel_heapMono₂ ext_299_1193 hpw_299
  have hforall_mot : Tm c.κ 0 (fun _ => default) m1193 (0 + nP)
      (.forallE motiveTy minors { pw := ℓ_c.zeronessOf })
      (.ptr (.enum kexprEnum) m1045.length) := by
    rw [Nat.zero_add]
    exact .forallE (by rw [hm1201]; simp)
      (hmot_tm.mono ext_605_1193)
      (hmin_tm.mono ext_1045_1193)
      hpw_1193
  have hforall_mot_head :
      ForallDomHeadLvls c.κ 0 (fun _ => default) m1193
        T bT clvls ((n + nIdx) + 1) (0 + nP) (.ptr (.enum kexprEnum) m1045.length) := by
    rw [Nat.zero_add]
    exact .succ (by rw [hm1201]; simp; exact ⟨rfl, rfl⟩) (hmin_head.mono ext_1045_1193)
  have ext_391_1193 : Heap.Extends m391 m1193 := by
    rw [← hm452_eq]
    exact ext_452_645.trans (ev617.heap_extends.trans ext_605_1193)
  obtain ⟨recTy_c, hrecTy_ite, hrecTy_tm⟩ :=
    nat_replace_pis_spec nP (by omega) hpw_1193
      (htty_390.mono ext_391_1193) hforall_mot ev1165
  have hrecTy_head :=
    lateRec_forallDomHeadLvls_replace_pis nP (by omega)
      (htty_390.mono ext_391_1193) hforall_mot_head ev1165
  have hrecTy_head' :
      ForallDomHeadLvls c.κ 0 (fun _ => default) m1153
        T bT clvls (nP + 1 + n + nIdx) 0 v1152 := by
    rwa [show nP + 1 + n + nIdx = nP + ((n + nIdx) + 1) by omega]
  simp only [↓reduceIte] at hrecTy_ite
  -- Connect `recTy_c` to `posOf rlps' recTy` via `posOf_structRecTyR`
  have hcRecTy_eq :
      cRecTy T clvls ℓ_c nP nIdx (posOf rlps' tty₀)
        (ctors_info.map fun inf => (inf.1, inf.2.1, posOf rlps' inf.2.2.2.1, inf.2.2.2.2)) =
      some recTy_c := by
    unfold cRecTy
    dsimp only
    rw [hsT_pos]
    dsimp only [Option.bind]
    rw [hmot_eq]
    dsimp only [Option.bind]
    simp only [List.length_map]
    rw [hmaj_ite]
    dsimp only [Option.bind]
    rw [hmin_eq]
    dsimp only [Option.bind]
    exact hrecTy_ite
  have hcs₀ : ∀ entry ∈ ctors₀,
      (∃ cbs cbody, entry.2.2.1.stripPis (nP + entry.2.1) = some (cbs, cbody)) ∧
      ∀ i ∈ entry.2.2.2, i < entry.2.1 := by
    intro entry hentry
    simp only [ctors₀, List.mem_map] at hentry
    obtain ⟨inf, hinf_mem, rfl⟩ := hentry
    have hwf_inf := hwf_all inf hinf_mem
    obtain ⟨cbs, _, cbody, hsC⟩ := hwf_inf.strip_C
    exact ⟨⟨cbs, _, hsC⟩, fun i hi => (hwf_inf.rec_spines i hi).1⟩
  have hpos_ty := posOf_structRecTyR k large T nP nIdx tty₀ ctors₀ ⟨tbs₀, tsort₀, hsT₀⟩ hcs₀
  dsimp only at hpos_ty
  rw [← clvls_eq_subst_params k large] at hpos_ty
  have hmap_cs :
      (ctors₀.map fun entry => (entry.1, entry.2.1, posOf rlps' entry.2.2.1, entry.2.2.2)) =
      (ctors_info.map fun inf => (inf.1, inf.2.1, posOf rlps' inf.2.2.2.1, inf.2.2.2.2)) := by
    simp [ctors₀, List.map_map, Function.comp_def]
  rw [hmap_cs, hcRecTy_eq] at hpos_ty
  rw [Option.map_eq_some_iff] at hpos_ty
  obtain ⟨recTy, hrecTy, hpos_recTy⟩ := hpos_ty
  rw [← hpos_recTy] at hrecTy_tm
  -- Step 6: `wrap_rel` on `recTy`, under the scoped context
  subst heq1282
  have ext_h_1153 := ev231.heap_extends.trans
    (ext_219_299.trans (ext_299_1193.trans ev1165.heap_extends))
  have hgood_wty : Good c.toCtx cs1257 := hgood.raw.sub (fun x hx => by simp [hx])
  have hwrap_ty_pos := wrapL_rel_spec hwl₁ hgood_wty hrecTy_tm (hrec_ty.mono ext_h_1153) ev1259
  have hwrap_ty : WrapRelSem c.env.find? recTy rec_ty₀ :=
    WrapRelSem.of_posOf_perm (rlps_perm k large) hwrap_ty_pos
  -- Step 7: the peer search answers the recursor itself; `build_rec_lvls_list`;
  -- `nat_check_rules` under the keying `κ₂`
  have ext_1249_1317 : Heap.Extends m1249 m1317 := by rw [hm1325]; exact Heap.Extends.snoc _ _
  have ext_h_1317 := ext_h_1153.trans (ev1259.heap_extends.trans ext_1249_1317)
  have hgood_peer : Good c.toCtx cs1294 := hgood.raw.sub (fun x hx => by simp [hx])
  obtain ⟨hv1283, _⟩ := find_peer_standalone_spec hc.loads hrecblk hcst hgood_peer
    (Bytes.repAddressRef_heapMono₂ addrTy ext_h_1317 hbRB) ev1296
  rw [hv1283] at ev1347
  rw [hnlvls_eq] at ev1465
  have hrlvls_1455 := build_rec_lvls_list_spec
    (by dsimp only [rlps']; cases large <;>
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_range] <;>
      have := hk_lt <;> omega) ev1465
  have ext_h_1455 := ext_h_1317.trans (ev1296.heap_extends.trans ev1465.heap_extends)
  have ext_605_1455 := ext_605_1193.trans (ev1165.heap_extends.trans
    (ev1259.heap_extends.trans (ext_1249_1317.trans
      (ev1296.heap_extends.trans ev1465.heap_extends))))
  have ext_391_1455 := ext_391_1193.trans (ev1165.heap_extends.trans
    (ev1259.heap_extends.trans (ext_1249_1317.trans
      (ev1296.heap_extends.trans ev1465.heap_extends))))
  have ext_299_1455 := ext_299_1193.trans (ev1165.heap_extends.trans
    (ev1259.heap_extends.trans (ext_1249_1317.trans
      (ev1296.heap_extends.trans ev1465.heap_extends))))
  have hload_rules : NatCtorLoadI κ₂ b₀ idx k ctors_info x_block cs1345 :=
    hload₂.mono_calls (fun x hx => by simp [hx])
  have hgood_rules : Good c.toCtx cs1345 := hgood.raw.sub (fun x hx => by simp [hx])
  have hbnd_rules : IxVM.Consistency.Bounded cs1345 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have ev1347' : ObsFn W "KernelCheck::nat_check_rules"
      [x_rules, x_block, .field (idx : F), x_parent_addr, v218, .field (nP : F), .field (nIdx : F),
        v298, .field (n : F), .field ((if large then 1 else 0 : Nat) : F),
        v390, v604, x_addr, v1361, .field ((0 : Nat) : F)]
      m1455 r h' cs1345 := by
    simpa using ev1347
  have hrules_ok := natI_check_rules_spec (c := c.toCtx) (κ := κ₂) (bRec := bRec)
    hwl₂ hT₂ hκ₂_inj hRec hidx hCres₂ hnCtors_lt hnP_lt hwf_all
    hsT₀ hsT_pos hmot_eq 0 (by omega)
    (hrules.mono ext_h_1455) hload_rules hgood_rules hbnd_rules
    (Bytes.repAddressRef_heapMono₂ addrTy ext_h_1455 hb₀_blk)
    (Bytes.repAddressRef_heapMono₂ addrTy ext_h_1455 hbT)
    (Bytes.repAddressRef_heapMono₂ addrTy ext_h_1455 hbRec)
    (RepKLevelList.mono hlps_219 (ext_219_299.trans ext_299_1455))
    hrlvls_1455
    (repKLevel_heapMono₂ ext_299_1455 hpw_299)
    ((htty_390.mono ext_391_1455).rekey_mono hkeep)
    ((hmot_tm.mono ext_605_1455).rekey_mono hkeep)
    ev1347'
  have hhead_eq :
      ∀ a_d ls_d,
        ForallRightHeadLvls h a_d ls_d (nP + 1 + n + nIdx) x_ty →
        ls_d = clvls := by
    intro a_d ls_d hright
    exact (wrapL_rel_forallDomHeadLvls hwl₁ hT_ind (nP + 1 + n + nIdx)
      hgood_wty hrecTy_head' (hright.mono ext_h_1153) ev1259).symm
  refine ⟨hnlvls_eq, heq189, heq217, ⟨recTy, hrecTy, hwrap_ty⟩, hhead_eq, ?_⟩
  intro j hlt hj
  have h0_j : 0 + j < ctors_info.length := by simpa using hj
  simpa using hrules_ok j hlt h0_j

end IxVM.Refinement.Decl
