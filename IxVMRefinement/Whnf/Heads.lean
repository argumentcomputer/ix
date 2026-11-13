import IxVMRefinement.Whnf.Prim

/-! # Step lemmas of `KernelWhnf`: constant heads without δ, ι at a structural head, and the
projections of a major

`whnf_nd_const_head` is `whnf_const_head` without δ: the natives (where the whole application
is closed, for the `Nat` family), the projection-function shortcut, quotient ι and the recursor
dispatch, each continued by `whnf_nd` (a K reduct by `whnf`). `whnf_struct_core_const` takes ι
at a recursor head whose level count matches (`try_iota`), the major's inductive read off the
recursor's type (`KernelCheck::rec_to_parent_addr`, at positional level parameters: `posOf`
keeps the head constant of every binder domain). `apply_n_projs` applies a head to the
projections `i, i + 1, …` of a major. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace WhnfAux

/-- A loaded `Rec` represents a stored recursor, with its counts. -/
theorem recr_full {κ : _root_.Address → KKey} {h : Heap F}
    {nl ty np ni nm nmi rules k u blk idx : SourceValue F} {ci : Ix.Kernel.ConstantInfo .anon}
    (r : CIRep κ h (.construct kciEnum "Rec" [nl, ty, np, ni, nm, nmi, rules, k, u, blk, idx]) ci) :
    ∃ (cv : Ix.Kernel.ConstantVal .anon) (mI rP : Nat) (rls : List (Ix.Kernel.RecRule .anon))
      (p i m mi : F), ci = .recInfo cv mI rP rls ∧ ValRep κ h nl ty cv ∧
      np = .field p ∧ ni = .field i ∧ nm = .field m ∧ nmi = .field mi ∧
      (mI : F) = p + m + mi + i ∧ mI < 288230376151711744 := by
  generalize hv : (Value.construct kciEnum "Rec" [nl, ty, np, ni, nm, nmi, rules, k, u, blk, idx] :
    SourceValue F) = v at r
  cases r
  case recr hv' hnp hni hnm hnmi hrP hmI hcounts hrules hk hkey =>
    injection hv with _ _ hl
    simp only [List.cons.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hl
    exact ⟨_, _, _, _, _, _, _, _, rfl, hv', hnp, hni, hnm, hnmi, hmI, hcounts.2⟩
  all_goals (injection hv with _ hc _; exact absurd hc (by decide))

/-- `Lists::length` on a level list. -/
theorem lv_length {ls : List KLevel} {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KLevelNode>» [l] h r h' cs)
    (hl : RepList klevelListEnum RepKLevel h ls l) : r = .field (ls.length : F) ∧ h' = h :=
  Lib.Lists.length_spec (t := .ptr (.named "KernelTypes::KLevelNode" [])) (R := RepKLevel)
    (by rw [Obs.Names.«Lists::length<&KernelTypes::KLevelNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol]; exact hl)

/-- Two counts below `2^39` whose difference is `0` in the field are equal. -/
theorem len_eq_of_sub {m n : Nat} (hm : m < 2 ^ 39) (hn : n < 2 ^ 39)
    (op : evalBinOp .sub (.field (m : F) : SourceValue F) (.field (n : F)) = .ok (.field 0)) :
    m = n := by
  have h1 : ((m : ℕ) : F) = ((n : ℕ) : F) :=
    sub_eq_zero.mp (NatAux.field_inj (NatAux.sub_ok op)).symm
  have h39 : (2 : ℕ) ^ 39 = 549755813888 := by norm_num
  exact (NatAux.natCast_inj (by omega) (by omega)).mp h1

/-- A binder domain of a level-instantiated telescope is the instantiated domain. -/
theorem piDomAt_ilp (ks : List Ix.Kernel.LevelParam) (vs : List KLevel) :
    ∀ (n : Nat) (e : KExpr),
      piDomAt n (e.instantiateLevelParams ks vs) =
        (piDomAt n e).map (·.instantiateLevelParams ks vs) := by
  intro n
  induction n with
  | zero => intro e; cases e <;> rfl
  | succ n ih => intro e; cases e <;> first | rfl | exact ih _

/-- A level instantiation that is a constant is the instantiation of that constant. -/
theorem const_of_ilp (ks : List Ix.Kernel.LevelParam) (vs : List KLevel) {k : KKey}
    {us' : List KLevel} {e : KExpr} (h : e.instantiateLevelParams ks vs = .const k us') :
    ∃ us0, e = .const k us0 := by
  cases e <;> first
    | (simp only [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.const.injEq] at h
       exact ⟨_, by rw [h.1]⟩)
    | (simp [Ix.Kernel.Expr.instantiateLevelParams] at h)

/-- **The major's inductive, read off the positional recursor type**: the head constant of the
domain of binder `mI` of `posOf ps T` is that of `T`'s. -/
theorem majorHead_of_pos {c : Ctx} {cv : Ix.Kernel.ConstantVal .anon} {mI : Nat}
    {a : Bytes.Address} {dom : KExpr} {us' : List KLevel}
    (hdom : piDomAt mI (posOf cv.levelParams cv.type) = some dom)
    (hfn : dom.getAppFn = .const (c.κ (ixAddr a)) us') : Specs.Whnf.MajorHead c cv mI a := by
  rw [posOf, piDomAt_ilp] at hdom
  obtain ⟨dom0, hd0, rfl⟩ := Option.map_eq_some_iff.mp hdom
  have hfn' : (dom0.instantiateLevelParams cv.levelParams (posLevels cv.levelParams)).getAppFn =
      .const (c.κ (ixAddr a)) us' := hfn
  rw [Ix.Kernel.Expr.getAppFn_instantiateLevelParams] at hfn'
  obtain ⟨us0, hus0⟩ := const_of_ilp _ _ hfn'
  exact ⟨us0, by rw [hd0]; simp [hus0]⟩

/-- The projections `j, j + 1, …, j + m` of a major: the first, then those from `j + 1`. -/
theorem projs_succ (k : KKey) (M : KExpr) (j : F) (m : Nat) :
    ((List.range (m + 1)).map fun t =>
        (Ix.Kernel.Expr.proj k (ZMod.val (j + (t : F))) M : KExpr)) =
      (Ix.Kernel.Expr.proj k (ZMod.val j) M : KExpr) ::
        ((List.range m).map fun t =>
          (Ix.Kernel.Expr.proj k (ZMod.val (j + 1 + (t : F))) M : KExpr)) := by
  first
    | (simp only [bind_pure_comp, List.map_eq_map, List.map_map, List.range_succ_eq_map,
        List.map_cons, Function.comp_def, Nat.cast_zero, add_zero, Nat.cast_succ,
        List.cons.injEq, true_and]
       apply List.map_congr_left
       intro t _
       congr 2
       ring)
    | (simp [List.range_succ_eq_map, Function.comp_def, add_assoc, add_comm]; done)
    | (simp [List.range_succ_eq_map, Function.comp_def]
       apply List.map_congr_left
       intro t _
       congr 2
       ring)

/-! ## `whnf_nd_const_head`'s native segment -/

theorem nd_seg_ext {fam op rc addr lvls hd sp types : SourceValue F} {h h' : Heap F}
    {r : SourceValue F} {cs : List (Call F)}
    (sg : Obs.«KernelWhnf::whnf_nd_const_head».Seg1 fam op rc addr lvls hd sp types h r h' cs) :
    Heap.Extends h h' := by
  rcases sg with ⟨m70, hv57, he62, hm78, he89, hc90⟩ |
    ⟨v96, m97, cs107, m127, cs138, cs156, hne91, hv95, ev109, ev140, ev158, hc199⟩ |
    ⟨v96, m97, cs107, v126, m127, cs138, m216, hne91, hv95, ev109, ev140, hne200, he208, hm224,
      he235, hc236⟩ |
    ⟨cs244, hne91, hne237, ev246, hc287⟩
  · rw [he89, hm78]; exact Heap.Extends.snoc _ _
  · exact (ObsFn.heap_extends ev109).trans
      ((ObsFn.heap_extends ev140).trans (ObsFn.heap_extends ev158))
  · rw [he235, hm224]
    exact (ObsFn.heap_extends ev109).trans
      ((ObsFn.heap_extends ev140).trans (Heap.Extends.snoc _ _))
  · exact ObsFn.heap_extends ev246

/-- The native segment's tags `1` and `2` are `try_prim_dispatch`'s. -/
theorem nd_seg_prim (c : Ctx) {fam op rc addr lvls hd sp types : SourceValue F} {h h' : Heap F}
    {t : F} {x : SourceValue F} {cs : List (Call F)}
    (sg : Obs.«KernelWhnf::whnf_nd_const_head».Seg1 fam op rc addr lvls hd sp types h
      (.tuple [.field t, x]) h' cs)
    (ht : t = 1 ∨ t = 2) (ih : IH c cs) (good : Good c cs) (hrc : c.rc h rc) {d : Nat}
    {Γ : Nat → KExpr} (htypes : c.types Γ h d types) {a : Bytes.Address} {us : List KLevel}
    {As : List KExpr} (ha : RepAddr h a addr) (hus : LvListRep h us lvls)
    (hAs : c.tml d Γ h As sp) :
    ∃ E, c.tm d Γ h' E x ∧
      Red c.env d (Specs.Whnf.mkAppN (.const (c.κ (ixAddr a)) us) As) E := by
  rcases sg with ⟨m70, hv57, he62, hm78, he89, hc90⟩ |
    ⟨v96, m97, cs107, m127, cs138, cs156, hne91, hv95, ev109, ev140, ev158, hc199⟩ |
    ⟨v96, m97, cs107, v126, m127, cs138, m216, hne91, hv95, ev109, ev140, hne200, he208, hm224,
      he235, hc236⟩ |
    ⟨cs244, hne91, hne237, ev246, hc287⟩
  · exact (tag12_absurd ht he62).elim
  · subst hc199
    have ext := (ObsFn.heap_extends ev109).trans (ObsFn.heap_extends ev140)
    exact ih.get (.whnf .try_prim_dispatch) (by lt_calls) ev158 rc addr lvls sp types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes) a us
      As (Bytes.repAddressRef_heapMono₂ addrTy ext ha) (LvListRep.mono ext hus)
      (tml_mono ext hAs) t x rfl ht
  · exact (tag12_absurd ht he208).elim
  · subst hc287
    exact ih.get (.whnf .try_prim_dispatch) (by lt_calls) ev246 rc addr lvls sp types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes a us As ha hus hAs t x rfl ht

end WhnfAux

/-! ## `whnf_struct_core_const` -/

/-- `KernelWhnf::whnf_struct_core_const`: at a recursor of the right level count, ι
(`try_iota`, the major's inductive from `rec_to_parent_addr`) continued by `whnf_struct_core`;
any other head is stuck. -/
theorem whnf_struct_core_const_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_struct_core_const" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.whnf_struct_core_const c args h r h' calls := by
  intro rc addr lvls hd sp types hargs good hrc d Γ htypes a us As ha hus hH hAs
  subst hargs
  rcases Obs.«KernelWhnf::whnf_struct_core_const».obs ev with
    ⟨m2, p10, cs16, x_rnl, x_rec_ty, x_nparams, x_nindices, x_nmotives, x_nminors, x_rules, w33,
      w34, w35, w36, x101, m103, cs112, m129, cs140, v154, m233, cs241, x_reduced, cs305, ev18,
      ld12, ev114, op108, ev243, ev142, ev307, hc332⟩ |
    ⟨m2, p10, cs16, x_rnl, x_rec_ty, x_nparams, x_nindices, x_nmotives, x_nminors, x_rules, w33,
      w34, w35, w36, x101, m103, cs112, v128, m129, cs140, v154, m233, cs241, cs339, ev18, ld12,
      ev114, op108, ev243, ev142, ev341, hc358⟩ |
    ⟨m2, p10, cs16, x_rnl, x_rec_ty, x_nparams, x_nindices, x_nmotives, x_nminors, x_rules, w33,
      w34, w35, w36, v92, x101, m103, cs112, cs366, ev18, ld12, ev114, op108, hne359, ev368,
      hc385⟩ |
    ⟨v1, m2, p10, cs16, cs393, ev18, ld12, hne386, ev395, hc412⟩
  · -- ι, continued
    subst hc332
    have e0 := ObsFn.heap_extends ev18
    obtain ⟨ci, hfind, v, hld, hci⟩ := ih.get (.callees .get_ci) (by lt_calls) ev18 addr a rfl
      (good.sub fun x hx => by simp [hx]) ha
    rw [ld12] at hld
    injection hld with hv
    subst hv
    obtain ⟨cv, mI, rP, rls, p, i, m, mi, rfl, hval, hnp, hni, hnm, hnmi, hmI, hmIlt⟩ :=
      WhnfAux.recr_full hci
    subst hnp hni hnm hnmi
    obtain ⟨ls, hls, hEq⟩ := hus
    have hls2 : RepKLevelList m2 ls lvls := hls.mono e0
    obtain ⟨rfl, hm103⟩ := WhnfAux.lv_length ev114 (by rw [klevelListEnum_eq]; exact hls2)
    obtain ⟨hnl, hnl32, hnd, hty⟩ := hval
    subst hnl
    have hb39 : ls.length < 2 ^ 39 :=
      RomBound.bounded_length_lt good.2
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [lvls], m2⟩) (by simp)
        (by simp) hls2
    subst hm103
    have hlen : ls.length = cv.levelParams.length :=
      WhnfAux.len_eq_of_sub hb39 (lt_trans hnl32 (by norm_num)) op108
    have hlenus : us.length = cv.levelParams.length := by
      rw [WhnfAux.evalEqList_length us ls (hEq fun _ => 0), hlen]
    obtain ⟨a', dom, us', ha', hdom, hfn⟩ := ih.get (.callees .rec_to_parent_addr) (by lt_calls)
      ev243 x_rec_ty p m mi i rfl (good.sub fun x hx => by simp [hx]) _ hty
    have hval' : ZMod.val (p + m + mi + i) = mI := by
      rw [← hmI]; exact NatAux.val_natCast (by omega)
    rw [hval'] at hdom
    have hmaj := WhnfAux.majorHead_of_pos hdom hfn
    have e1 := ObsFn.heap_extends ev243
    have ext := e0.trans e1
    obtain ⟨E, hE, hred⟩ := ih.get (.whnf .try_iota) (by lt_calls) ev142 rc x_rec_ty lvls sp _ _
      _ _ x_rules types hd v154 rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ
      (types_mono ext htypes) _ us _ w33 cv mI rP rls a' As
      ⟨⟨hfind, w34, w35, w36, hci.mono e1⟩, ⟨ls, hls.mono ext, hEq⟩⟩ hlenus ha' hmaj
      (Tm.mono ext hH) (tml_mono ext hAs) 1 x_reduced rfl (.inl rfl)
    have ext' := ext.trans (ObsFn.heap_extends ev142)
    obtain ⟨E', hE', hred'⟩ := ih.get (.whnf .whnf_struct_core) (by lt_calls) ev307 rc x_reduced
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext' hrc) d Γ
      (types_mono ext' htypes) E hE
    exact ⟨E', hE', .trans hred hred'⟩
  · -- ι takes no step: stuck
    subst hc358
    have ext := (ObsFn.heap_extends ev18).trans ((ObsFn.heap_extends ev114).trans
      ((ObsFn.heap_extends ev243).trans (ObsFn.heap_extends ev142)))
    exact ⟨_, ih.get (.whnf .apply_spine) (by lt_calls) ev341 hd sp rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 _ As (Tm.mono ext hH) (tml_mono ext hAs), .refl⟩
  · -- another level count: stuck
    subst hc385
    have ext := (ObsFn.heap_extends ev18).trans (ObsFn.heap_extends ev114)
    exact ⟨_, ih.get (.whnf .apply_spine) (by lt_calls) ev368 hd sp rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 _ As (Tm.mono ext hH) (tml_mono ext hAs), .refl⟩
  · -- not a recursor: stuck
    subst hc412
    have ext := ObsFn.heap_extends ev18
    exact ⟨_, ih.get (.whnf .apply_spine) (by lt_calls) ev395 hd sp rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 _ As (Tm.mono ext hH) (tml_mono ext hAs), .refl⟩

/-! ## `whnf_nd_const_head` -/

/-- `KernelWhnf::whnf_nd_const_head`: the natives (`try_prim_dispatch`, for the `Nat` family only
where the whole application is closed), then by the loaded constant: a definition's projection
shortcut; quotient ι; the recursor dispatch; each continued by `whnf_nd` (the K reduct by
`whnf`); any other head is stuck. -/
theorem whnf_nd_const_head_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_nd_const_head" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.whnf_nd_const_head c args h r h' calls := by
  intro rc addr lvls hd sp types hargs good hrc d Γ htypes a us As ha hus hH hAs
  subst hargs
  have p := Obs.«KernelWhnf::whnf_nd_const_head».obs ev
  cases p
  case n1_bind m2 cs12 x_fam x__op m289 cs291 x_reduced cs328 ev14 sg296 ev330 hc =>
    subst hc
    have e0 := ObsFn.heap_extends ev14
    obtain ⟨E, hE, hred⟩ := WhnfAux.nd_seg_prim c sg296 (.inl rfl) (ih.mono (by lt_calls))
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) (types_mono e0 htypes)
      (Bytes.repAddressRef_heapMono₂ addrTy e0 ha) (LvListRep.mono e0 hus) (tml_mono e0 hAs)
    have ext := e0.trans (WhnfAux.nd_seg_ext sg296)
    obtain ⟨E', hE', hred'⟩ := ih.get (.whnf .whnf_nd) (by lt_calls) ev330 rc x_reduced types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes) E hE
    exact ⟨E', hE', .trans hred hred'⟩
  case n2_bind m2 cs12 x_fam x__op m289 cs291 x_stuck ev14 sg296 he375 he376 hc =>
    subst hc he375 he376
    have e0 := ObsFn.heap_extends ev14
    exact WhnfAux.nd_seg_prim c sg296 (.inr rfl) (ih.mono (by lt_calls))
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) (types_mono e0 htypes)
      (Bytes.repAddressRef_heapMono₂ addrTy e0 ha) (LvListRep.mono e0 hus) (tml_mono e0 hAs)
  case other_Defn_n1_bind m2 cs12 x_fam x__op v288 m289 cs291 m382 p389 cs395 x_nl w422 x_value
      w423 w424 m451 cs461 x_reduced cs527 ev14 sg296 ev397 ld391 ev463 ev529 hc =>
    subst hc
    have ext := (ObsFn.heap_extends ev14).trans (WhnfAux.nd_seg_ext sg296)
    obtain ⟨ci, hfind, v, hld, hci⟩ := ih.get (.callees .get_ci) (by lt_calls) ev397 addr a rfl
      (good.sub fun x hx => by simp [hx]) (Bytes.repAddressRef_heapMono₂ addrTy ext ha)
    rw [ld391] at hld
    injection hld with hv
    subst hv
    obtain ⟨cv, V, hn, rfl, ⟨hnl, -, hnd, -⟩, hV⟩ := CIRep.defn_inv hci
    have ext2 := ext.trans (ObsFn.heap_extends ev397)
    obtain ⟨E, hE, hred⟩ := ih.get (.whnf .try_reduce_projection_definition) (by lt_calls) ev463
      x_value x_nl lvls sp rfl (good.sub fun x hx => by simp [hx]) d Γ _ cv V hn us As hfind hV
      hnd hnl (LvListRep.mono ext2 hus) (tml_mono ext2 hAs) x_reduced rfl
    have ext3 := ext2.trans (ObsFn.heap_extends ev463)
    obtain ⟨E', hE', hred'⟩ := ih.get (.whnf .whnf_nd) (by lt_calls) ev529 rc x_reduced types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext3 hrc) d Γ (types_mono ext3 htypes) E hE
    exact ⟨E', hE', .trans hred hred'⟩
  case other_Defn_other m2 cs12 x_fam x__op v288 m289 cs291 m382 p389 cs395 x_nl w422 x_value w423
      w424 v450 m451 cs461 cs561 ev14 sg296 ev397 ld391 ev463 ev563 hc =>
    subst hc
    have ext := (ObsFn.heap_extends ev14).trans ((WhnfAux.nd_seg_ext sg296).trans
      ((ObsFn.heap_extends ev397).trans (ObsFn.heap_extends ev463)))
    exact ⟨_, ih.get (.whnf .apply_spine) (by lt_calls) ev563 hd sp rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 _ As (Tm.mono ext hH) (tml_mono ext hAs), .refl⟩
  case other_Quot_n1_bind m2 cs12 x_fam x__op v288 m289 cs291 m382 p389 cs395 w588 w589 w590 m607
      cs617 x_reduced cs691 ev14 sg296 ev397 ld391 ev619 ev693 hc =>
    subst hc
    have ext := (ObsFn.heap_extends ev14).trans ((WhnfAux.nd_seg_ext sg296).trans
      (ObsFn.heap_extends ev397))
    obtain ⟨E, hE, hred⟩ := ih.get (.whnf .try_quot_iota) (by lt_calls) ev619 rc addr lvls sp types
      rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes) a
      us As (Bytes.repAddressRef_heapMono₂ addrTy ext ha) (LvListRep.mono ext hus)
      (tml_mono ext hAs) x_reduced rfl
    have ext' := ext.trans (ObsFn.heap_extends ev619)
    obtain ⟨E', hE', hred'⟩ := ih.get (.whnf .whnf_nd) (by lt_calls) ev693 rc x_reduced types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext' hrc) d Γ (types_mono ext' htypes) E hE
    exact ⟨E', hE', .trans hred hred'⟩
  case other_Quot_other m2 cs12 x_fam x__op v288 m289 cs291 m382 p389 cs395 w588 w589 w590 v606
      m607 cs617 cs725 ev14 sg296 ev397 ld391 ev619 ev727 hc =>
    subst hc
    have ext := (ObsFn.heap_extends ev14).trans ((WhnfAux.nd_seg_ext sg296).trans
      ((ObsFn.heap_extends ev397).trans (ObsFn.heap_extends ev619)))
    exact ⟨_, ih.get (.whnf .apply_spine) (by lt_calls) ev727 hd sp rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 _ As (Tm.mono ext hH) (tml_mono ext hAs), .refl⟩
  case other_Rec_n1_bind m2 cs12 x_fam x__op v288 m289 cs291 m382 p389 cs395 x_rnl x_rec_ty
      x_nparams x_nindices x_nmotives x_nminors x_rules x_k_flag w752 w753 w754 m811 cs822
      x_reduced cs950 ev14 sg296 ev397 ld391 ev824 ev952 hc =>
    subst hc
    have ext0 := (ObsFn.heap_extends ev14).trans (WhnfAux.nd_seg_ext sg296)
    obtain ⟨ci, hfind, v, hld, hci⟩ := ih.get (.callees .get_ci) (by lt_calls) ev397 addr a rfl
      (good.sub fun x hx => by simp [hx]) (Bytes.repAddressRef_heapMono₂ addrTy ext0 ha)
    rw [ld391] at hld
    injection hld with hv
    subst hv
    obtain ⟨cv, mI, rP, rls, rfl⟩ := CIRep.recr_inv hci
    have ext := ext0.trans (ObsFn.heap_extends ev397)
    obtain ⟨E, hE, hred⟩ := ih.get (.whnf .red_rec) (by lt_calls) ev824 rc _ _ lvls hd sp _ _ _ _ _
      _ types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ
      (types_mono ext htypes) _ us cv mI rP rls As
      ⟨⟨hfind, _, _, _, hci⟩, LvListRep.mono ext hus⟩ (Tm.mono ext hH) (tml_mono ext hAs) 1
      x_reduced rfl (.inl rfl)
    have ext' := ext.trans (ObsFn.heap_extends ev824)
    obtain ⟨E', hE', hred'⟩ := ih.get (.whnf .whnf_nd) (by lt_calls) ev952 rc x_reduced types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext' hrc) d Γ (types_mono ext' htypes) E hE
    exact ⟨E', hE', .trans hred hred'⟩
  case other_Rec_n2_bind m2 cs12 x_fam x__op v288 m289 cs291 m382 p389 cs395 x_rnl x_rec_ty
      x_nparams x_nindices x_nmotives x_nminors x_rules x_k_flag w752 w753 w754 m811 cs822 x_stuck
      ev14 sg296 ev397 ld391 ev824 he997 he998 hc =>
    subst hc he997 he998
    have ext0 := (ObsFn.heap_extends ev14).trans (WhnfAux.nd_seg_ext sg296)
    obtain ⟨ci, hfind, v, hld, hci⟩ := ih.get (.callees .get_ci) (by lt_calls) ev397 addr a rfl
      (good.sub fun x hx => by simp [hx]) (Bytes.repAddressRef_heapMono₂ addrTy ext0 ha)
    rw [ld391] at hld
    injection hld with hv
    subst hv
    obtain ⟨cv, mI, rP, rls, rfl⟩ := CIRep.recr_inv hci
    have ext := ext0.trans (ObsFn.heap_extends ev397)
    exact ih.get (.whnf .red_rec) (by lt_calls) ev824 rc _ _ lvls hd sp _ _ _ _ _
      _ types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ
      (types_mono ext htypes) _ us cv mI rP rls As
      ⟨⟨hfind, _, _, _, hci⟩, LvListRep.mono ext hus⟩ (Tm.mono ext hH) (tml_mono ext hAs) 2
      _ rfl (.inr (.inl rfl))
  case other_Rec_n3_bind m2 cs12 x_fam x__op v288 m289 cs291 m382 p389 cs395 x_rnl x_rec_ty
      x_nparams x_nindices x_nmotives x_nminors x_rules x_k_flag w752 w753 w754 m811 cs822
      x_k_reduct cs1021 ev14 sg296 ev397 ld391 ev824 ev1023 hc =>
    subst hc
    have ext0 := (ObsFn.heap_extends ev14).trans (WhnfAux.nd_seg_ext sg296)
    obtain ⟨ci, hfind, v, hld, hci⟩ := ih.get (.callees .get_ci) (by lt_calls) ev397 addr a rfl
      (good.sub fun x hx => by simp [hx]) (Bytes.repAddressRef_heapMono₂ addrTy ext0 ha)
    rw [ld391] at hld
    injection hld with hv
    subst hv
    obtain ⟨cv, mI, rP, rls, rfl⟩ := CIRep.recr_inv hci
    have ext := ext0.trans (ObsFn.heap_extends ev397)
    obtain ⟨E, hE, hred⟩ := ih.get (.whnf .red_rec) (by lt_calls) ev824 rc _ _ lvls hd sp _ _ _ _ _
      _ types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ
      (types_mono ext htypes) _ us cv mI rP rls As
      ⟨⟨hfind, _, _, _, hci⟩, LvListRep.mono ext hus⟩ (Tm.mono ext hH) (tml_mono ext hAs) 3
      x_k_reduct rfl (.inr (.inr rfl))
    have ext' := ext.trans (ObsFn.heap_extends ev824)
    obtain ⟨E', hE', hred'⟩ := ih.get (.whnf .whnf) (by lt_calls) ev1023 rc x_k_reduct types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext' hrc) d Γ (types_mono ext' htypes) E hE
    exact ⟨E', hE', .trans hred hred'⟩
  case other_Rec_other m2 cs12 x_fam x__op v288 m289 cs291 m382 p389 cs395 x_rnl x_rec_ty
      x_nparams x_nindices x_nmotives x_nminors x_rules x_k_flag w752 w753 w754 v810 m811 cs822
      cs1055 ev14 sg296 ev397 ld391 ev824 ev1057 hc =>
    subst hc
    have ext := (ObsFn.heap_extends ev14).trans ((WhnfAux.nd_seg_ext sg296).trans
      ((ObsFn.heap_extends ev397).trans (ObsFn.heap_extends ev824)))
    exact ⟨_, ih.get (.whnf .apply_spine) (by lt_calls) ev1057 hd sp rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 _ As (Tm.mono ext hH) (tml_mono ext hAs), .refl⟩
  case other_other m2 cs12 x_fam x__op v288 m289 cs291 v381 m382 p389 cs395 cs1082 ev14 sg296
      ev397 ld391 hne581 hne745 hne1075 ev1084 hc =>
    subst hc
    have ext := (ObsFn.heap_extends ev14).trans ((WhnfAux.nd_seg_ext sg296).trans
      (ObsFn.heap_extends ev397))
    exact ⟨_, ih.get (.whnf .apply_spine) (by lt_calls) ev1084 hd sp rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 _ As (Tm.mono ext hH) (tml_mono ext hAs), .refl⟩

/-! ## `apply_n_projs` -/

/-- `KernelWhnf::apply_n_projs`: the head applied to the projections `i, …, n_fields - 1` of the
major. -/
theorem apply_n_projs_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::apply_n_projs" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.apply_n_projs c args h r h' calls := by
  intro hd par major nf i hargs good d Γ H p M n j hH hp hM hn hi
  subst hargs hn hi
  rcases Obs.«KernelWhnf::apply_n_projs».obs ev with
    ⟨op17, he25, he26, hc27⟩ |
    ⟨v1, m33, cs74, v81, m83, op17, hne28, hm43, hm91, op145, ev76, hc147⟩
  · subst he25 he26
    have hnj : n - j = 0 := (NatAux.field_inj (NatAux.sub_ok op17)).symm
    exact ⟨0, by rw [Nat.cast_zero, add_zero]; exact (sub_eq_zero.mp hnj).symm, hH⟩
  · subst hc147
    obtain rfl := NatAux.add_ok op145
    have e1 : Heap.Extends h m33 := by rw [hm43]; exact Heap.Extends.snoc _ _
    have e2 : Heap.Extends m33 m83 := by rw [hm91]; exact Heap.Extends.snoc _ _
    have hcell : Tm c.κ d Γ m33 0 (.proj (c.κ (ixAddr p)) (ZMod.val j) M)
        (.ptr (.enum kexprEnum) h.length) := by
      subst hm43
      exact .proj List.getElem?_concat_length
        (Bytes.repAddressRef_heapMono₂ addrTy (Heap.Extends.snoc _ _) hp)
        (Tm.mono (Heap.Extends.snoc _ _) hM)
    have happ : Tm c.κ d Γ m83 0 (.app H (.proj (c.κ (ixAddr p)) (ZMod.val j) M))
        (.ptr (.enum kexprEnum) m33.length) := by
      subst hm91
      exact Tm.store_app (Tm.mono e1 hH) hcell
    have ext := e1.trans e2
    obtain ⟨m', hm', hrep⟩ := ih.get (.whnf .apply_n_projs) (by lt_calls) ev76 _ par major _ _ rfl
      (good.sub fun x hx => by simp [hx]) d Γ _ p M n (j + 1) happ
      (Bytes.repAddressRef_heapMono₂ addrTy ext hp) (Tm.mono ext hM) rfl rfl
    refine ⟨m' + 1, by rw [← hm']; push_cast; ring, ?_⟩
    rw [WhnfAux.projs_succ]
    exact hrep

end IxVM.Refinement.Core
