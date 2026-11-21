import IxVMRefinement.Assembly.PointCtors
import IxVMRefinement.Assembly.BlockRouteFunctional

/-! # A modeled block of one inductive type has no field-less sole constructor

The dispatch `KernelModeled::block_is_modeled` sends a block of one inductive type to the modeled
route only where the scan of its constructors (`ctors_nested`, after each constructor's
parameters) finds a nested occurrence: an application headed by an inductive outside the block
whose arguments mention a member. Its answer is `Route.blockRoute`, a function of the store.

* `nestedN_spine_atoms`, `ctorAnswer_spine_atoms`, `blockRoute_one`: on the pure route
  function, a constructor whose type, after its parameters, is a constant applied to atoms
  answers `0`, and a block of one inductive with one constructor answers that constructor's
  answer.
* `assert_first_args_atoms`, `ctor_return_tree`: `KernelCheck::check_ctor_return_type` on a term
  of a given shape: after the parameters and fields the term is a constant applied to
  `n_params + n_indices` arguments, the first `n_params` of them variables.
* `modeledCtor_trees`: the walk's check of the member of a one-type block that is modeled at the
  store runs the modeled constructor loop (`check_modeled_ctors`), whose return-type check gives
  every constructor's stored type that shape.

So a constructor with no field of a member with no index is such a spine of atoms, and a block
whose only member has one constructor and no index, and whose dispatch answers `1`, has a field
in that constructor (the row lemma `famUnitFree_of_run`, `FamilyAlias/BlockRowCheck.lean`). -/

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency
open IxVM.Refinement.Route

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## The pure route function -/

theorem foldr_orElse_false :
    ∀ l : List (Option Bool), (∀ o ∈ l, o = some false) → l.foldr orElse (some false) = some false
  | [], _ => rfl
  | o :: l, h => by
    rw [List.foldr_cons, h o List.mem_cons_self,
      foldr_orElse_false l (fun o' ho' => h o' (List.mem_cons_of_mem _ ho'))]
    try rfl

/-- **The scan answers `0` on a constant applied to atoms.** -/
theorem nestedN_spine_atoms (isInd : _root_.Address → Option Bool) (M : List _root_.Address) :
    ∀ (n : Nat) (B : ScanTree), B.size ≤ n → (∃ a, B.head = .const a) →
      (∀ X ∈ B.args, X = .atom) → nestedN isInd M n B = some false := by
  intro n B hn hhd hargs
  cases n with
  | zero =>
    have := B.size_pos
    omega
  | succ n =>
    cases B with
    | atom => rfl
    | const a => rfl
    | lam t b =>
      obtain ⟨a, ha⟩ := hhd
      cases ha
    | all t b =>
      obtain ⟨a, ha⟩ := hhd
      cases ha
    | letE t v b =>
      obtain ⟨a, ha⟩ := hhd
      cases ha
    | proj x =>
      obtain ⟨a, ha⟩ := hhd
      cases ha
    | app f x =>
      obtain ⟨a, ha⟩ := hhd
      have hany : ((ScanTree.app f x).args.any fun A => A.mentions M) = false := by
        rw [List.any_eq_false]
        intro A hA
        rw [hargs A hA]
        exact Bool.false_ne_true
      have hhere : hereOf isInd M (ScanTree.app f x).head
          ((ScanTree.app f x).args.any fun A => A.mentions M)
          (nestedN isInd M n (ScanTree.app f x).head) = some false := by
        rw [hany]
        unfold hereOf
        rw [ha]
        show hereConst isInd a (memB M a) false = some false
        cases memB M a <;> rfl
      have hn1 : 1 ≤ n := by
        simp only [ScanTree.size] at hn
        have := f.size_pos
        have := x.size_pos
        omega
      have hfold : ((ScanTree.app f x).args.map (nestedN isInd M n)).foldr orElse (some false) =
          some false := by
        apply foldr_orElse_false
        intro o ho
        obtain ⟨A, hA, rfl⟩ := List.mem_map.mp ho
        rw [hargs A hA]
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        rfl
      have key : nestedN isInd M (n + 1) (.app f x) =
          orElse (hereOf isInd M (ScanTree.app f x).head
            ((ScanTree.app f x).args.any fun A => A.mentions M)
            (nestedN isInd M n (ScanTree.app f x).head))
            (((ScanTree.app f x).args.map (nestedN isInd M n)).foldr orElse (some false)) := rfl
      rw [key, hhere, hfold]
      try rfl

/-- **A constructor whose type, after its parameters, is a constant applied to atoms answers
`0`.** -/
theorem ctorAnswer_spine_atoms {isInd : _root_.Address → Option Bool}
    {M refs : List _root_.Address} {sharing : List Ixon.Expr} {ct : Ixon.Constructor}
    {T B : ScanTree} (hT : ExprTree refs M sharing 4294967295 ct.typ T)
    (hp : T.peel ct.params.toNat = some B) (hhd : ∃ a, B.head = .const a)
    (hargs : ∀ X ∈ B.args, X = .atom) :
    ctorAnswer isInd M refs sharing ct = some false := by
  have hT' := exprTree?_of hT
  cases hm : B.mentions M
  · simp only [ctorAnswer, hT', hp, ctorBody, hm]
  · simp only [ctorAnswer, hT', hp, ctorBody, hm]
    exact nestedN_spine_atoms isInd M B.size B (Nat.le_refl _) hhd hargs

/-- **The dispatch at a block of one inductive with one constructor** is that constructor's
answer. -/
theorem blockRoute_one {E : Ixon.Env} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {ct : Ixon.Constructor} (hrec : recordOf E B = some cb)
    (hm : cb.info = .muts #[.indc ind]) (hct : ind.ctors.toList = [ct]) :
    blockRoute E B = orElse (ctorAnswer (isIndAt E)
      (Ingress.blockRecurAddrs B (#[.indc ind] : Array Ixon.MutConst).toList) cb.refs.toList
      cb.sharing.toList ct) (some false) := by
  have h1 : blockRoute E B = recordRoute E B cb := by
    unfold blockRoute
    rw [hrec]
    try rfl
  have h2 : recordRoute E B cb = mutsRoute E B cb #[.indc ind] := by
    unfold recordRoute
    rw [hm]
    try rfl
  have h3 : mutsRoute E B cb #[.indc ind] = oneRoute E B cb #[.indc ind] := rfl
  have h4 : oneRoute E B cb #[.indc ind] =
      (ind.ctors.toList.map (ctorAnswer (isIndAt E)
        (Ingress.blockRecurAddrs B (#[.indc ind] : Array Ixon.MutConst).toList) cb.refs.toList
        cb.sharing.toList)).foldr orElse (some false) := rfl
  rw [h1, h2, h3, h4, hct]
  try rfl

/-! ## The return-type check on a term of a given shape -/

theorem treeAt_atom_of_bvar {h : Heap F} {p : SourceValue F} {T : ScanTree}
    {xs : List (SourceValue F)} (ht : TreeAt h p T)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KExprNode" "BVar" xs)) : T = .atom := by
  cases ht with
  | bvar _ => rfl
  | srt _ => rfl
  | lit _ => rfl
  | const hl _ | app hl _ _ | lam hl _ _ | all hl _ _ | letE hl _ _ _ | proj hl _ =>
    rw [hl] at ld
    injection ld with ld
    injection ld with _ htag _
    exact absurd htag (by decide)

/-- **`assert_first_args_are_param_bvars` from argument `i`**: the next `m` arguments are
variables. -/
theorem assert_first_args_atoms :
    ∀ (m : Nat) {Ts : List ScanTree} {np i : Nat} {sp nf r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      m + i = np → np < 18446744069414584321 →
      RepList Core.kexprListEnum (fun h₀ X p₀ => TreeAt h₀ p₀ X) h Ts sp →
      ObsFn Obs.W "KernelCheck::assert_first_args_are_param_bvars"
        [sp, .field (np : F), nf, .field (i : F)] h r h' cs →
      ∀ k < m, Ts[k]? = some .atom := by
  intro m
  induction m with
  | zero =>
    intro Ts np i sp nf r h h' cs _ _ _ _ k hk
    omega
  | succ m ih =>
    intro Ts np i sp nf r h h' cs hmi hnp hTs ev k hk
    match Obs.«KernelCheck::assert_first_args_are_param_bvars».obs ev with
    | .n0 (op17 := op) .. =>
      have hzero : (.field ((0 : Nat) : F) : SourceValue F) = .field ((np - i : Nat) : F) := by
        simpa using Decl.evalBinOp_sub_nat (by omega : i ≤ np) op
      have := Decl.nat_eq_of_field_eq_bounded (by decide) (by omega) hzero
      omega
    | .other (ld44 := ldc) (ld73 := ldb) (op192 := opi) (ev153 := evr) .. =>
      obtain ⟨z, zs, rfl, hz, hzs⟩ := Core.RepList.cons_of_load hTs ldc
      have hza : z = .atom := treeAt_atom_of_bvar hz ldb
      have hv := Decl.evalBinOp_add_nat i 1 opi
      subst hv
      cases k with
      | zero =>
        subst hza
        rfl
      | succ k =>
        exact ih (i := i + 1) (by omega) hnp hzs evr k (by omega)

/-- **`check_ctor_return_type` on a term of shape `T`**: after `n_params + n_fields` binders,
`T` is a constant applied to `n_params + n_indices` arguments whose first `n_params` are
variables. -/
theorem ctor_return_tree {T : ScanTree} {pcty pnl pblk r : SourceValue F} {nP nI nF : Nat}
    {i : F} {h h' : Heap F} {cs : List (Call F)} (hbound : Bounded cs)
    (hnPF : nP + nF < 18446744069414584321) (hnPI : nP + nI < 18446744069414584321)
    (hT : TreeAt h pcty T)
    (ev : ObsFn Core.W "KernelCheck::check_ctor_return_type"
      [pcty, .field (nP : F), .field (nI : F), .field (nF : F), pnl, pblk, .field i]
      h r h' cs) :
    ∃ B, T.peel (nP + nF) = some B ∧ (∃ a, B.head = .const a) ∧ B.args.length = nP + nI ∧
      ∀ k < nP, B.args[k]? = some .atom := by
  match Obs.«KernelCheck::check_ctor_return_type».obs ev with
  | .run (m2 := m2) (m41 := m41) (x_head := xhd) (x_args := xargs) (m109 := m109)
      (m147 := m147) (m197 := m197) (op37 := op_pf) (ev14 := ev_peel) (ev54 := ev_sp)
      (ld90 := ld_hd) (ev121 := ev_par) (ev159 := ev_lvls) (ev207 := ev_len) (op229 := op_pi)
      (heq232 := heq_len) (ev246 := ev_bv) (hc397 := hc) .. =>
    subst hc
    rw [Decl.evalBinOp_add_nat nP nF op_pf] at ev_peel
    obtain ⟨B, hpeel, hB⟩ := peel_n_foralls_tree (nP + nF) hnPF hT ev_peel
    obtain ⟨hd, sp, htup, hH, hAs⟩ := collect_spine_tree B.size (Nat.le_refl _) hB ev_sp
    injection htup with hl
    injection hl with h1 hl
    injection hl with h2
    subst h1 h2
    obtain ⟨a, ha, -⟩ := hH.const_inv ld_hd
    have hAs147 := hAs.mono treeAt_heapMono₂
      (ev_par.heap_extends.trans ev_lvls.heap_extends)
    obtain ⟨hv_len, hm197⟩ := Core.SubstAux.klength ev_len hAs147
    rw [hm197] at ev_bv
    rw [Decl.evalBinOp_add_nat nP nI op_pi, hv_len] at heq_len
    have hAs_lt : B.args.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbound
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [xargs], m147⟩)
        (by simp) List.mem_cons_self hAs147
    have hlen : B.args.length = nP + nI :=
      Decl.nat_eq_of_field_eq_bounded (by omega) hnPI heq_len
    have hat := assert_first_args_atoms nP (i := 0) (by omega) (by omega) hAs147 ev_bv
    exact ⟨B, hpeel, ⟨Core.ixAddr a, ha⟩, hlen, hat⟩

/-! ## The walk's check of a modeled member -/

/-- **The constructors of the member of a one-type block modeled at the store**: the walk's
check of the member (`MemberCheckedLimAt`) took the modeled branch of the `Induct` arm (the native
one observes the dispatch answering `0`, which `ModeledAt` refutes) and ran the modeled
constructor loop, whose return-type check gives each constructor's stored type, read as the
dispatch reads it (`ExprTree`), a telescope of its parameters and fields into a constant applied
to `n_params + n_indices` arguments, the first `n_params` of them variables; the constructor's
parameter count is the member's. -/
theorem modeledCtor_trees {calls : List (Call F)} {c : Core.Ctx} (hg : Core.Good c calls)
    {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable} {lim : Option Nat} {B : _root_.Address}
    {cb : Ixon.Constant} {ind : Ixon.Inductive}
    (hblock : recordOf c.E B = some cb) (hmuts : cb.info = .muts #[.indc ind])
    (hproj : recordOf c.E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)))
    (hmod : ModeledAt c.E B)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim) :
    ∀ j < ind.ctors.size, ∃ (ct : Ixon.Constructor) (T Bd : ScanTree),
      ind.ctors[j]? = some ct ∧ ct.params.toNat = ind.params.toNat ∧
      ExprTree cb.refs.toList (Ingress.blockRecurAddrs B (#[.indc ind] : Array Ixon.MutConst).toList)
        cb.sharing.toList 4294967295 ct.typ T ∧
      T.peel (ct.params.toNat + ct.fields.toNat) = some Bd ∧ (∃ a, Bd.head = .const a) ∧
      Bd.args.length = ct.params.toNat + ind.indices.toNat ∧
      ∀ k < ct.params.toNat, Bd.args[k]? = some .atom := by
  intro j hj
  obtain ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmem, hblk, ev_pa, -, hsub_pa, -, -, ev_ld, -, hsub_ld, hld,
    ev_chk, -, hsub_chk⟩ := hchk
  obtain ⟨b', hb', hb'B⟩ := hblk
  obtain ⟨-, -, -, mc, a, hget, ha, hax, -⟩ := Ingress.projection_addr_hashed_spec hmem hb' ev_pa
  have hv0 : ZMod.val ((0 : Nat) : F) = 0 := by simp
  rw [hv0] at hget hax
  have hmc : mc = .indc ind := by
    have e : (#[Ixon.MutConst.indc ind] : Array Ixon.MutConst).toList[0]? = some (.indc ind) := rfl
    exact Option.some.inj (hget.symm.trans e)
  subst hmc
  have hax' : Core.ixAddr a = Core.iprjAddr B 0 := by
    rw [← hb'B]
    exact hax.trans (LoadedReads.memberAddr_eq_projAddr _ 0 (.indc ind)).symm
  have hg_ld : Core.Good c cs_load := hg.sub hsub_ld
  have hg_chk : Core.Good c cs_chk := hg.sub hsub_chk
  -- the load of the member's projection record
  obtain ⟨rawBytes, c', hh, haddr, hex, htv, hres⟩ := Ingress.get_ci_block_trace_spec hg_ld.2 ha ev_ld
  have hrecA : recordOf c.E (Core.ixAddr a) = some (memberProjection B 0 (.indc ind)) := by
    rw [hax']
    exact hproj
  obtain ⟨lc, hgetA, hdecA⟩ := LoadedReads.recordOf_inv hrecA
  have hb0 : rawBytes = lc.rawBytes := Core.load_escape hgetA hg_ld.1 rawBytes hh haddr
  have hc : c' = memberProjection B 0 (.indc ind) := by
    rw [hb0, hdecA] at hex
    exact (Except.ok.inj hex).symm
  subst hc
  unfold Ingress.GetCIBlockTraceResult at hres
  have hinfo : (memberProjection B 0 (.indc ind)).info = .iPrj ⟨(0 : Nat).toUInt64, B⟩ := rfl
  rw [hinfo] at hres
  obtain ⟨hidx, blkBytes, cb', ms', ind', blobs, tree, plan, v₀, hhB, haB, hexB, hcb, hms,
    hhp, built, planned, hld₀, hraw, hlev⟩ := hres
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hblock
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hg_ld.1 blkBytes hhB haB
  have hcB : cb' = cb := by
    rw [hbB, hdecB] at hexB
    exact (Except.ok.inj hexB).symm
  subst cb'
  have hmsEq : ms' = #[.indc ind] := Ixon.ConstantInfo.muts.inj (hcb.symm.trans hmuts)
  subst ms'
  have hi' : (⟨(0 : Nat).toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat = 0 :=
    toNat_toUInt64_of_lt (by decide)
  rw [hi'] at hms hraw
  have hiEq : ind' = ind := by
    have e : (#[Ixon.MutConst.indc ind] : Array Ixon.MutConst).toList[0]? = some (.indc ind) :=
      rfl
    exact Ixon.MutConst.indc.inj (Option.some.inj (hms.symm.trans e))
  subst ind'
  have hvv : v₀ = v := Except.ok.inj (hld₀.symm.trans hld)
  subst v₀
  obtain ⟨hlvls, hp56, hi56, hc56, hidx56, tyPtr, blkPtr, b, hb_eq, hb_rep, hv, rty⟩ := hraw
  subst hv
  have hbB' : Core.ixAddr b = B := hb_eq
  -- the route: the native branch is refuted, the modeled branch ran its constructor loop
  rcases induct_native_or_ctors ev_chk with ⟨mb, ma, mcs, modeRun, hextN, hsubN⟩ |
      ⟨uarg, mcb, mca, mcr, mccs, hu, ctorsRun, hextC, hsubC⟩
  · have hgN : Core.Good c mcs := hg_chk.sub hsubN
    exact absurd (show NativeAt c.E B from ⟨blkPtr, mb, ma, mcs, b, modeRun, hgN.1, hgN.2,
      Bytes.repAddressRef_heapMono₂ Core.addrTy hextN hb_rep, hbB'⟩) hmod
  obtain ⟨s, rfl⟩ : ∃ s : F, uarg = .field s := by
    rcases hu with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨_, rfl⟩
  have hsubC' : ∀ cl ∈ mccs, cl ∈ calls := fun cl hcl => hsub_chk cl (hsubC cl hcl)
  obtain ⟨st⟩ := modeled_ctor_runs (b := b) (start := mcb) hc56 ind.ctors.size 0 (by omega)
    (Heap.Extends.refl _) hsubC' (Bytes.repAddressRef_heapMono₂ Core.addrTy hextC hb_rep)
    ctorsRun j (Nat.zero_le _) hj
  -- the slot's record
  have hval_j : ZMod.val ((j : Nat) : F) = j :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  have hgL : Core.Good c st.loadCalls := hg.sub st.loadSubset
  obtain ⟨-, -, -, blkBytes₂, cb₂, ms₂, ind₂, ct, blobs₂, v₂, hhB₂, haB₂, hexB₂, -, hcb₂, hms₂,
    hct₂, hhp₂, hldv₂, hraw₂⟩ := Ingress.get_ci_cprj_spec hgL.2 st.blockRep st.loaded
  have hbB₂ : blkBytes₂ = lcB.rawBytes :=
    Core.load_escape hgetB hgL.1 blkBytes₂ hhB₂ (haB₂.trans hbB')
  have hcB₂ : cb₂ = cb := by
    rw [hbB₂, hdecB] at hexB₂
    exact (Except.ok.inj hexB₂).symm
  subst cb₂
  have hmsEq₂ : ms₂ = #[.indc ind] := Ixon.ConstantInfo.muts.inj (hcb₂.symm.trans hmuts)
  subst ms₂
  rw [hv0] at hms₂
  have hind₂ : ind₂ = ind := by
    have e : (#[Ixon.MutConst.indc ind] : Array Ixon.MutConst).toList[0]? = some (.indc ind) :=
      rfl
    exact Ixon.MutConst.indc.inj (Option.some.inj (hms₂.symm.trans e))
  subst ind₂
  rw [hval_j] at hct₂
  have hctj : ind.ctors[j]? = some ct := by
    rw [← Array.getElem?_toList]
    exact hct₂
  have hvv₂ : v₂ = .construct Core.kciEnum "Ctor" [st.nl, st.ty, st.parent, st.member, st.slot,
      st.numParams, st.numFields, st.unsafeFlag] :=
    Except.ok.inj (hldv₂.symm.trans st.tag)
  obtain ⟨hclv, hccidx, hcpar, hcf, -, tyPtrC, blkPtrC, bC, -, -, hvC, rtyC⟩ := hraw₂
  rw [hvC] at hvv₂
  injection hvv₂ with _ _ hargs
  injection hargs with hnl hargs; injection hargs with hty_eq hargs
  injection hargs with _ hargs; injection hargs with _ hargs
  injection hargs with hsl hargs; injection hargs with hnp_eq hargs
  injection hargs with hnf_eq _
  have hparN : ct.params.toNat = ind.params.toNat :=
    Decl.nat_eq_of_field_eq_bounded (by omega) (by omega) (hnp_eq.trans st.paramsChecked)
  -- the stored type's shape, carried to the return-type check
  obtain ⟨T, hET, hTA⟩ := treeAt_of_rawConv rtyC
  have e_scope_sort : Heap.Extends st.scopeBefore st.sortBefore := by
    have e1 := st.scopeRun.heap_extends
    rw [st.nilTypes]
    exact e1.trans (Heap.Extends.snoc _ _)
  have e_ret : Heap.Extends st.after st.retBefore :=
    st.extended.trans (e_scope_sort.trans (st.sortRun.heap_extends.trans st.sortToRet))
  have hTR : TreeAt st.retBefore tyPtrC T := hTA.mono e_ret
  have retRun := st.retRun
  rw [← hnf_eq, ← hty_eq] at retRun
  have hgR : Core.Good c st.retCalls := hg.sub st.retSubset
  obtain ⟨Bd, hpeel, hhd, hlen, hat⟩ :=
    ctor_return_tree hgR.2 (by omega) (by omega) hTR retRun
  refine ⟨ct, T, Bd, hctj, hparN, ?_, ?_, hhd, ?_, ?_⟩
  · rw [hbB'] at hET
    exact hET
  · rw [hparN]
    exact hpeel
  · rw [hparN]
    exact hlen
  · rw [hparN]
    exact hat

end IxVM.Refinement.Typing.FamilyAlias
