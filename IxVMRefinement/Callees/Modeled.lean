import IxVMRefinement.Core.Registry
import IxVMRefinement.Core.Open
import IxVMRefinement.Core.RomBound
import IxVMRefinement.Lib.Bytes
import IxVMRefinement.Lib.Lists
import IxVMRefinement.Obs.KernelCheck0
import IxVMRefinement.Obs.KernelCheck2
import IxVMRefinement.Obs.KernelModeled0

/-! # Recursor parent scan and modeled-route gates

Step lemmas for:
* `KernelCheck::rec_to_parent_addr` (via `KernelCheck::peel_n_foralls`),
* `KernelModeled::block_is_multi` and `KernelModeled::block_is_modeled`
  (via `KernelModeled::muts_indc_count`),
* `KernelModeled::proj_ctor` (via `KernelModeled::assert_proj_allowed`),
* `KernelModeled::defeq_list_ok`. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ModeledAux

macro "callees_lt" : tactic =>
  `(tactic| (simp only [List.length_cons, List.length_append]; omega))

theorem getAppFn_mkAppN : ∀ (As : List KExpr) (f : KExpr),
    (Ix.Kernel.Expr.mkAppN f As).getAppFn = f.getAppFn
  | [], _ => rfl
  | a :: As, f => by
    show (Ix.Kernel.Expr.mkAppN (.app f a) As).getAppFn = f.getAppFn
    rw [getAppFn_mkAppN As (.app f a)]
    rfl

theorem getAppArgs_mkAppN : ∀ (As : List KExpr) (f : KExpr),
    (Ix.Kernel.Expr.mkAppN f As).getAppArgs = f.getAppArgs ++ As
  | [], f => by simp [Ix.Kernel.Expr.mkAppN]
  | a :: As, f => by
    show (Ix.Kernel.Expr.mkAppN (.app f a) As).getAppArgs = f.getAppArgs ++ a :: As
    rw [getAppArgs_mkAppN As (.app f a)]
    simp [Ix.Kernel.Expr.getAppArgs]

theorem piDomAt_of_stripPis :
    ∀ {n : Nat} {T dom body : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)}
      {bm : Ix.Kernel.BinderMeta},
      T.stripPis n = some (bs, .forallE dom body bm) →
      piDomAt n T = some dom := by
  intro n
  induction n with
  | zero =>
    intro T dom body bs bm h
    simp only [Ix.Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨-, rfl⟩
    rfl
  | succ n ih =>
    intro T dom body bs bm h
    cases T with
    | forallE ty b m =>
      simp only [Ix.Kernel.Expr.stripPis, Option.map_eq_some_iff] at h
      rcases h with ⟨⟨bs', rest⟩, hstrip, -, rfl⟩
      exact ih hstrip
    | _ => simp [Ix.Kernel.Expr.stripPis] at h

theorem peel_n_foralls_aux (c : Ctx) :
    ∀ (m : Nat) {n : F} {x_e r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
      {d k : Nat} {Γ : Nat → KExpr} {T : KExpr},
      ZMod.val n = m →
      c.tmk d Γ k h T x_e →
      ObsFn W "KernelCheck::peel_n_foralls" [x_e, .field n] h r h' calls →
      h' = h ∧ ∃ (bs : List (KExpr × Ix.Kernel.BinderMeta)) (B : KExpr),
        T.stripPis m = some (bs, B) ∧ c.tmk d Γ (k + m) h B r := by
  intro m
  induction m with
  | zero =>
    intro n x_e r h h' calls d k Γ T hval hT ev
    have hn0 : n = 0 := (ZMod.val_eq_zero n).mp hval
    subst hn0
    cases Obs.«KernelCheck::peel_n_foralls».obs ev with
    | n0 _ rfl rfl _ =>
      exact ⟨rfl, [], T, rfl, by simpa using hT⟩
    | other _ _ _ _ _ hne19 _ _ _ _ =>
      exact (hne19 rfl).elim
  | succ m ih =>
    intro n x_e r h h' calls d k Γ T hval hT ev
    have hn0 : n ≠ 0 := by
      intro e; subst e; simp at hval
    cases Obs.«KernelCheck::peel_n_foralls».obs ev with
    | n0 hv14 _ _ _ =>
      exact (hn0 (Value.field.inj hv14)).elim
    | other w42 x_body w43 cs62 v66 _ ld34 op87 ev64 _ =>
      obtain ⟨T0, B0, ℓ, rfl, -, hB0, -⟩ := hT.forallE_of_load ld34
      have hv66 : v66 = .field (n - 1) := by
        simp only [evalBinOp, Except.ok.injEq] at op87
        exact op87.symm
      subst hv66
      have hval' : ZMod.val (n - 1) = m := by
        have hs := Lib.val_sub_one hn0
        omega
      obtain ⟨rfl, bs, B, hstrip, hB⟩ := ih hval' hB0 ev64
      refine ⟨rfl, (T0, bmeta ℓ) :: bs, B, ?_, ?_⟩
      · simp [Ix.Kernel.Expr.stripPis, hstrip]
      · rwa [show k + (m + 1) = k + 1 + m by omega]

theorem natCast_inj_lt {a b : Nat} (ha : a < 2 ^ 39) (hb : b < 2 ^ 39)
    (h : (a : F) = (b : F)) : a = b := by
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt (Nat.lt_trans ha (by decide)),
      ZMod.val_natCast_of_lt (Nat.lt_trans hb (by decide))] at hv
  exact hv

theorem muts_indc_count_spec :
    ∀ {ms : List Ixon.MutConst} {x_members r : SourceValue F} {h h' : Heap F}
      {calls : List (Call F)},
      Specs.Callees.MembersRep h ms x_members →
      ObsFn W "KernelModeled::muts_indc_count" [x_members] h r h' calls →
      r = .field ((ms.filter Specs.Callees.isIndc).length : F) ∧ h' = h := by
  intro ms
  induction ms with
  | nil =>
    intro x_members r h h' calls hms ev
    cases Obs.«KernelModeled::muts_indc_count».obs ev with
    | Nil _ rfl rfl _ => simp
    | Cons_Indc _ _ _ _ _ ld12 _ _ _ _ | Cons_other _ _ _ ld12 _ _ _ =>
      obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hms ld12
      cases he
  | cons m rest ih =>
    intro x_members r h h' calls hms ev
    cases Obs.«KernelModeled::muts_indc_count».obs ev with
    | Nil ld12 _ _ _ =>
      cases Lib.rep_nil_of_load hms ld12
    | Cons_Indc x_rest w56 x62 m64 cs73 ld12 ev75 rfl op69 _ =>
      obtain ⟨z, zs, he, ⟨x, hmc⟩, hzs⟩ := Lib.rep_cons_of_load hms ld12
      injection he with rfl rfl
      obtain ⟨rfl, rfl⟩ := ih hzs ev75
      have hr : r = .field (((rest.filter Specs.Callees.isIndc).length : F) + 1) := by
        simp only [evalBinOp, Except.ok.injEq] at op69
        exact op69.symm
      subst hr
      cases m with
      | indc _ =>
        have hi : Specs.Callees.isIndc (.indc ‹_›) = true := rfl
        rw [List.filter_cons_of_pos hi, List.length_cons, Nat.cast_add, Nat.cast_one]
        exact ⟨rfl, rfl⟩
      | defn _ | recr _ =>
        rw [Specs.Callees.mutCtor] at hmc
        injection hmc with _ hc _
        exact absurd hc (by decide)
    | Cons_other x_m x_rest cs93 ld12 hne86 ev95 _ =>
      obtain ⟨z, zs, he, ⟨x, hmc⟩, hzs⟩ := Lib.rep_cons_of_load hms ld12
      injection he with rfl rfl
      obtain ⟨rfl, rfl⟩ := ih hzs ev95
      cases m with
      | indc _ =>
        exact (hne86 [x] rfl hmc).elim
      | defn _ =>
        have hi : ¬ Specs.Callees.isIndc (.defn ‹_›) = true := by decide
        rw [List.filter_cons_of_neg hi]
        exact ⟨rfl, rfl⟩
      | recr _ =>
        have hi : ¬ Specs.Callees.isIndc (.recr ‹_›) = true := by decide
        rw [List.filter_cons_of_neg hi]
        exact ⟨rfl, rfl⟩

theorem infoShape_muts_inv {h : Heap F} {info : Ixon.ConstantInfo} {lp : SourceValue F}
    (hi : Specs.Callees.InfoShape h info (.construct "Ixon::ConstantInfo" "Muts" [lp])) :
    ∃ ms : Array Ixon.MutConst, info = .muts ms ∧ Specs.Callees.MembersRep h ms.toList lp := by
  cases info with
  | muts ms =>
    rcases hi with ⟨lp', he, hms⟩
    injection he with _ _ hl
    injection hl with rfl _
    exact ⟨ms, rfl, hms⟩
  | defn _ | recr _ | axio _ | quot _ | cPrj _ | rPrj _ | iPrj _ | dPrj _ =>
    rcases hi with ⟨_, he⟩
    injection he with _ hc _
    exact absurd hc (by decide)

theorem infoShape_not_muts {h : Heap F} {info : Ixon.ConstantInfo} {x_info : SourceValue F}
    (hi : Specs.Callees.InfoShape h info x_info)
    (hne : ∀ vs : List (SourceValue F), vs.length = 1 →
      x_info ≠ .construct "Ixon::ConstantInfo" "Muts" vs) :
    ∀ ms, info ≠ .muts ms := by
  intro ms h
  subst h
  rcases hi with ⟨lp, rfl, -⟩
  exact hne [lp] rfl rfl

theorem fewInductives_of_modeled_zero (c : Ctx) {bp : SourceValue F} {b : Bytes.Address}
    {h h' : Heap F} {cs : List (Call F)}
    (hbim : Specs.Callees.block_is_modeled c [bp] h (.field 0) h' cs)
    (good : Good c cs) (hb : RepAddr h b bp) :
    FewInductives c (ixAddr b) := by
  intro cst ms hcst hinfo
  by_contra hgt
  have h2 : 2 ≤ (ms.toList.filter isIndc).length := by omega
  have h01 := (hbim bp b rfl good hb cst hcst).1 ⟨ms, hinfo, h2⟩
  exact absurd (Value.field.inj h01) (by decide)

end ModeledAux

/-- `KernelCheck::rec_to_parent_addr`: peels `p + m + mi + i` leading binders of a closed recursor
type and returns the head constant address of the next binder's domain. -/
theorem rec_to_parent_addr_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelCheck::rec_to_parent_addr" args h r h' calls) (ih : IH c calls) :
    Specs.Callees.rec_to_parent_addr c args h r h' calls := by
  intro ty p m mi i hargs good T hT
  subst hargs
  obtain ⟨v1, x9, x17, v37, m38, cs48, x_major_ty, w86, w87, m104, cs115, x_head, w132, x_caddr,
    w162, op32, op24, op16, ev50, ld78, ev117, ld154, he174, he175, hc176⟩ :=
    Obs.«KernelCheck::rec_to_parent_addr».obs ev
  have hx17 : x17 = .field (p + m) := by simp only [evalBinOp, Except.ok.injEq] at op32; exact op32.symm
  subst hx17
  have hx9 : x9 = .field (p + m + mi) := by simp only [evalBinOp, Except.ok.injEq] at op24; exact op24.symm
  subst hx9
  have hv1 : v1 = .field (p + m + mi + i) := by simp only [evalBinOp, Except.ok.injEq] at op16; exact op16.symm
  subst hv1
  obtain ⟨rfl, bs, B, hstrip, hB⟩ :=
    ModeledAux.peel_n_foralls_aux c (ZMod.val (p + m + mi + i)) rfl
      (hT 0 (fun _ => .sort .zero)) ev50
  obtain ⟨dom, B0, ℓ, rfl, hdom, -, -⟩ := hB.forallE_of_load ld78
  have hpi : piDomAt (ZMod.val (p + m + mi + i)) T = some dom :=
    ModeledAux.piDomAt_of_stripPis hstrip
  obtain ⟨hd, sp, H, As, he, hH, -, rfl⟩ :=
    ih.get (.subst .collect_spine) (by subst hc176; ModeledAux.callees_lt) ev117 x_major_ty rfl
      (good.sub (by subst hc176; intro z hz; simp [hz])) 0 (fun _ => .sort .zero)
      (0 + ZMod.val (p + m + mi + i)) dom hdom
  injection he with h1
  simp only [List.cons.injEq, and_true] at h1
  rcases h1 with ⟨rfl, rfl⟩
  obtain ⟨a, us, rfl, ha, -⟩ := hH.const_of_load ld154
  subst he174 he175
  refine ⟨a, Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr a)) us) As, us, ha, hpi, ?_⟩
  rw [ModeledAux.getAppFn_mkAppN]
  rfl

/-- `KernelModeled::block_is_multi`: returns `0` or `1`, and for a record of `c.E` at `b`, returns
`1` iff the record is a mutual block with at least two inductive members. -/
theorem block_is_multi_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelModeled::block_is_multi" args h r h' calls) (ih : IH c calls) :
    Specs.Callees.block_is_multi c args h r h' calls := by
  intro bp b hargs good hb
  subst hargs
  cases Obs.«KernelModeled::block_is_multi».obs ev with
  | Muts_n0 m2 cs12 w39 w40 w41 w42 x_members m90 cs101 ev14 ev103 he116 he117 hc118 =>
    subst he116 he117
    refine ⟨.inl rfl, fun cst hcst => ?_⟩
    have hgood1 : Good c cs12 := good.sub (by rw [hc118]; intro z hz; simp [hz])
    obtain ⟨-, hshape⟩ :=
      ih.get (.callees .load_verified_constant) (by rw [hc118]; ModeledAux.callees_lt)
        ev14 bp b rfl hgood1 hb
    rcases hshape cst hcst with ⟨info, sh, rf, un, bd, he, hinfo⟩
    injection he with _ _ hl; injection hl with rfl _
    obtain ⟨ms, hms_eq, hms⟩ := ModeledAux.infoShape_muts_inv hinfo
    have hcall : (⟨"KernelModeled::muts_indc_count", [x_members], m2⟩ : Call F) ∈ calls := by
      rw [hc118]; simp
    have hlen : ms.toList.length < 2 ^ 39 :=
      RomBound.bounded_length_lt good.2 hcall (by simp) hms
    have hflen : (ms.toList.filter Specs.Callees.isIndc).length < 2 ^ 39 :=
      Nat.lt_of_le_of_lt (List.length_filter_le _ _) hlen
    obtain ⟨hcnt, -⟩ := ModeledAux.muts_indc_count_spec hms ev103
    have hk0 : (ms.toList.filter Specs.Callees.isIndc).length = 0 :=
      (ModeledAux.natCast_inj_lt (by decide) hflen (Value.field.inj hcnt)).symm
    constructor
    · intro h01; exact absurd (Value.field.inj h01) (by decide)
    · rintro ⟨ms', hms', h2⟩
      rw [hms_eq] at hms'; injection hms' with rfl
      omega
  | Muts_n1 m2 cs12 w39 w40 w41 w42 x_members m90 cs101 ev14 ev103 he124 he125 hc126 =>
    subst he124 he125
    refine ⟨.inl rfl, fun cst hcst => ?_⟩
    have hgood1 : Good c cs12 := good.sub (by rw [hc126]; intro z hz; simp [hz])
    obtain ⟨-, hshape⟩ :=
      ih.get (.callees .load_verified_constant) (by rw [hc126]; ModeledAux.callees_lt)
        ev14 bp b rfl hgood1 hb
    rcases hshape cst hcst with ⟨info, sh, rf, un, bd, he, hinfo⟩
    injection he with _ _ hl; injection hl with rfl _
    obtain ⟨ms, hms_eq, hms⟩ := ModeledAux.infoShape_muts_inv hinfo
    have hcall : (⟨"KernelModeled::muts_indc_count", [x_members], m2⟩ : Call F) ∈ calls := by
      rw [hc126]; simp
    have hlen : ms.toList.length < 2 ^ 39 :=
      RomBound.bounded_length_lt good.2 hcall (by simp) hms
    have hflen : (ms.toList.filter Specs.Callees.isIndc).length < 2 ^ 39 :=
      Nat.lt_of_le_of_lt (List.length_filter_le _ _) hlen
    obtain ⟨hcnt, -⟩ := ModeledAux.muts_indc_count_spec hms ev103
    have hk1 : (ms.toList.filter Specs.Callees.isIndc).length = 1 :=
      (ModeledAux.natCast_inj_lt (a := 1) (by decide) hflen (by simpa using Value.field.inj hcnt)).symm
    constructor
    · intro h01; exact absurd (Value.field.inj h01) (by decide)
    · rintro ⟨ms', hms', h2⟩
      rw [hms_eq] at hms'; injection hms' with rfl
      omega
  | Muts_other m2 cs12 w39 w40 w41 w42 x_members v89 m90 cs101 ev14 ev103 hne119 hne127
      he131 he132 hc133 =>
    subst he131 he132
    refine ⟨.inr rfl, fun cst hcst => ?_⟩
    have hgood1 : Good c cs12 := good.sub (by rw [hc133]; intro z hz; simp [hz])
    obtain ⟨-, hshape⟩ :=
      ih.get (.callees .load_verified_constant) (by rw [hc133]; ModeledAux.callees_lt)
        ev14 bp b rfl hgood1 hb
    rcases hshape cst hcst with ⟨info, sh, rf, un, bd, he, hinfo⟩
    injection he with _ _ hl; injection hl with rfl _
    obtain ⟨ms, hms_eq, hms⟩ := ModeledAux.infoShape_muts_inv hinfo
    obtain ⟨hcnt, -⟩ := ModeledAux.muts_indc_count_spec hms ev103
    subst hcnt
    have hk_ne0 : (ms.toList.filter Specs.Callees.isIndc).length ≠ 0 := by
      intro h0; exact hne119 (by simp [h0])
    have hk_ne1 : (ms.toList.filter Specs.Callees.isIndc).length ≠ 1 := by
      intro h1; exact hne127 (by simp [h1])
    exact ⟨fun _ => ⟨ms, hms_eq, by omega⟩, fun _ => rfl⟩
  | other m2 cs12 x_info w39 w40 w41 w42 ev14 hne134 he138 he139 hc140 =>
    subst he138 he139
    refine ⟨.inl rfl, fun cst hcst => ?_⟩
    have hgood1 : Good c cs12 := good.sub (by rw [hc140]; intro z hz; simp [hz])
    obtain ⟨-, hshape⟩ :=
      ih.get (.callees .load_verified_constant) (by rw [hc140]; ModeledAux.callees_lt)
        ev14 bp b rfl hgood1 hb
    rcases hshape cst hcst with ⟨info, sh, rf, un, bd, he, hinfo⟩
    injection he with _ _ hl; injection hl with rfl _
    have hnm := ModeledAux.infoShape_not_muts hinfo hne134
    constructor
    · intro h01; exact absurd (Value.field.inj h01) (by decide)
    · rintro ⟨ms, hms, -⟩; exact (hnm ms hms).elim

/-- `KernelModeled::block_is_modeled`: returns `1` at a block of two or more inductives and `0` at
a record with zero inductive members. -/
theorem block_is_modeled_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelModeled::block_is_modeled" args h r h' calls) (ih : IH c calls) :
    Specs.Callees.block_is_modeled c args h r h' calls := by
  intro bp b hargs good hb cst hcst
  subst hargs
  cases Obs.«KernelModeled::block_is_modeled».obs ev with
  | Muts_n0 m2 cs12 w39 w40 w41 w42 x_members m90 cs101 ev14 ev103 he116 he117 hc118 =>
    subst he116 he117
    have hgood1 : Good c cs12 := good.sub (by rw [hc118]; intro z hz; simp [hz])
    obtain ⟨-, hshape⟩ :=
      ih.get (.callees .load_verified_constant) (by rw [hc118]; ModeledAux.callees_lt)
        ev14 bp b rfl hgood1 hb
    rcases hshape cst hcst with ⟨info, sh, rf, un, bd, he, hinfo⟩
    injection he with _ _ hl; injection hl with rfl _
    obtain ⟨ms, hms_eq, hms⟩ := ModeledAux.infoShape_muts_inv hinfo
    have hcall : (⟨"KernelModeled::muts_indc_count", [x_members], m2⟩ : Call F) ∈ calls := by
      rw [hc118]; simp
    have hlen : ms.toList.length < 2 ^ 39 :=
      RomBound.bounded_length_lt good.2 hcall (by simp) hms
    have hflen : (ms.toList.filter Specs.Callees.isIndc).length < 2 ^ 39 :=
      Nat.lt_of_le_of_lt (List.length_filter_le _ _) hlen
    obtain ⟨hcnt, -⟩ := ModeledAux.muts_indc_count_spec hms ev103
    have hk0 : (ms.toList.filter Specs.Callees.isIndc).length = 0 :=
      (ModeledAux.natCast_inj_lt (by decide) hflen (Value.field.inj hcnt)).symm
    refine ⟨?_, fun _ => rfl⟩
    rintro ⟨ms', hms', h2⟩
    rw [hms_eq] at hms'; injection hms' with rfl
    omega
  | Muts_n1 m2 cs12 w39 w40 w41 w42 x_members m90 cs101 _ _ _ _ _ _ _ _ ev14 ev103 _ _ _ hc241 =>
    have hgood1 : Good c cs12 := good.sub (by rw [hc241]; intro z hz; simp [hz])
    obtain ⟨-, hshape⟩ :=
      ih.get (.callees .load_verified_constant) (by rw [hc241]; ModeledAux.callees_lt)
        ev14 bp b rfl hgood1 hb
    rcases hshape cst hcst with ⟨info, sh, rf, un, bd, he, hinfo⟩
    injection he with _ _ hl; injection hl with rfl _
    obtain ⟨ms, hms_eq, hms⟩ := ModeledAux.infoShape_muts_inv hinfo
    have hcall : (⟨"KernelModeled::muts_indc_count", [x_members], m2⟩ : Call F) ∈ calls := by
      rw [hc241]; simp
    have hlen : ms.toList.length < 2 ^ 39 :=
      RomBound.bounded_length_lt good.2 hcall (by simp) hms
    have hflen : (ms.toList.filter Specs.Callees.isIndc).length < 2 ^ 39 :=
      Nat.lt_of_le_of_lt (List.length_filter_le _ _) hlen
    obtain ⟨hcnt, -⟩ := ModeledAux.muts_indc_count_spec hms ev103
    have hk1 : (ms.toList.filter Specs.Callees.isIndc).length = 1 :=
      (ModeledAux.natCast_inj_lt (a := 1) (by decide) hflen (by simpa using Value.field.inj hcnt)).symm
    constructor
    · rintro ⟨ms', hms', h2⟩
      rw [hms_eq] at hms'; injection hms' with rfl
      omega
    · intro h0
      have := h0 ms hms_eq
      omega
  | Muts_other m2 cs12 w39 w40 w41 w42 x_members v89 m90 cs101 ev14 ev103 hne119 hne242
      he246 he247 hc248 =>
    subst he246 he247
    have hgood1 : Good c cs12 := good.sub (by rw [hc248]; intro z hz; simp [hz])
    obtain ⟨-, hshape⟩ :=
      ih.get (.callees .load_verified_constant) (by rw [hc248]; ModeledAux.callees_lt)
        ev14 bp b rfl hgood1 hb
    rcases hshape cst hcst with ⟨info, sh, rf, un, bd, he, hinfo⟩
    injection he with _ _ hl; injection hl with rfl _
    obtain ⟨ms, hms_eq, hms⟩ := ModeledAux.infoShape_muts_inv hinfo
    obtain ⟨hcnt, -⟩ := ModeledAux.muts_indc_count_spec hms ev103
    subst hcnt
    refine ⟨fun _ => rfl, ?_⟩
    intro h0
    exact absurd (by simp [h0 ms hms_eq]) hne119
  | other m2 cs12 x_info w39 w40 w41 w42 ev14 hne249 he253 he254 hc255 =>
    subst he253 he254
    have hgood1 : Good c cs12 := good.sub (by rw [hc255]; intro z hz; simp [hz])
    obtain ⟨-, hshape⟩ :=
      ih.get (.callees .load_verified_constant) (by rw [hc255]; ModeledAux.callees_lt)
        ev14 bp b rfl hgood1 hb
    rcases hshape cst hcst with ⟨info, sh, rf, un, bd, he, hinfo⟩
    injection he with _ _ hl; injection hl with rfl _
    have hnm := ModeledAux.infoShape_not_muts hinfo hne249
    refine ⟨?_, fun _ => rfl⟩
    rintro ⟨ms, hms, -⟩
    exact (hnm ms hms).elim

/-- `KernelModeled::proj_ctor`: asserts `block_is_modeled(block) = 0` (`FewInductives`) and loads
the constructor projection record `(i, 0, block)`. -/
theorem proj_ctor_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelModeled::proj_ctor" args h r h' calls) (ih : IH c calls) :
    Specs.Callees.proj_ctor c args h r h' calls := by
  intro bp i b hargs good hb
  subst hargs
  obtain ⟨v1, m2, cs12, cs26, ev14, ev28, hc52⟩ := Obs.«KernelModeled::proj_ctor».obs ev
  obtain ⟨v12, m15, cs23, ev25, heq40, -, hm2, hc45⟩ :=
    Obs.«KernelModeled::assert_proj_allowed».obs ev14
  subst heq40 hm2
  have hgood1 : Good c cs23 :=
    good.sub (by rw [hc52, hc45]; intro z hz; simp [hz])
  have hbim := ih.get (.callees .block_is_modeled)
    (by rw [hc52, hc45]; ModeledAux.callees_lt) ev25
  have hfew : FewInductives c (ixAddr b) :=
    ModeledAux.fewInductives_of_modeled_zero c hbim hgood1 hb
  have hgood2 : Good c cs26 :=
    good.sub (by rw [hc52]; intro z hz; simp [hz])
  have hb' : RepAddr m15 b bp := Bytes.repAddressRef_heapMono₂ addrTy ev25.heap_extends hb
  obtain ⟨ci, hfind, hci⟩ :=
    ih.get (.callees .get_ci_cprj) (by rw [hc52]; ModeledAux.callees_lt) ev28
      bp i 0 b rfl hgood2 hb'
  rw [ZMod.val_zero] at hfind
  exact ⟨hfew, ci, hfind, hci⟩

/-- `KernelModeled::defeq_list_ok`: pairwise `DefEq` on two represented term lists when the answer
is nonzero. -/
theorem defeq_list_ok_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelModeled::defeq_list_ok" args h r h' calls) (ih : IH c calls) :
    Specs.Callees.defeq_list_ok c args h r h' calls := by
  intro rc xs ys types hargs good hrc d Γ htypes As Bs hAs hBs hr
  subst hargs
  cases Obs.«KernelModeled::defeq_list_ok».obs ev with
  | Nil_Nil ld12 ld31 _ _ _ =>
    have hAs0 := Lib.rep_nil_of_load hAs ld12
    have hBs0 := Lib.rep_nil_of_load hBs ld31
    subst hAs0 hBs0
    exact .nil
  | Nil_other _ _ _ _ he46 _ _ =>
    exact (hr he46).elim
  | Cons_Nil _ _ _ _ he85 _ _ =>
    exact (hr he85).elim
  | Cons_Cons_other _ _ _ _ _ _ _ _ _ _ _ he199 _ _ =>
    exact (hr he199).elim
  | Cons_Cons_n1 x_x x_xr x_y x_yr m106 cs117 cs159 ld12 ld77 ev119 ev161 hc194 =>
    obtain ⟨A, As', heA, hA, hAs'⟩ := Lib.rep_cons_of_load hAs ld12
    obtain ⟨B, Bs', heB, hB, hBs'⟩ := Lib.rep_cons_of_load hBs ld77
    subst heA heB
    have hgood1 : Good c cs117 := good.sub (by rw [hc194]; intro z hz; simp [hz])
    have hde := ih.get (.defEq .k_is_def_eq) (by rw [hc194]; ModeledAux.callees_lt) ev119
      rc x_x x_y types rfl hgood1 hrc d Γ htypes A B hA hB (by decide)
    have ext := ev119.heap_extends
    have hgood2 : Good c cs159 := good.sub (by rw [hc194]; intro z hz; simp [hz])
    have hrest := ih.get (.callees .defeq_list_ok) (by rw [hc194]; ModeledAux.callees_lt) ev161
      rc x_xr x_yr types rfl hgood2 (RCRep.mono ext hrc) d Γ ⟨htypes.1.mono ext, htypes.2⟩
      As' Bs' (TmL.mono ext hAs') (TmL.mono ext hBs') hr
    exact .cons hde hrest

end IxVM.Refinement.Core
