import IxVMRefinement.DefEq.Basic
import IxVMRefinement.Lib.Words
import IxC.Kernel.Rules.Transport

/-! # Step lemmas of `KernelDefEq`: the rebase, the structural tiers and the slow tiers

* **The rebase** (`k_def_eq_rebase`): the inputs lowered past their unused innermost `g` opened
  variables (`expr_glb`, `lbr_min`, `expr_lower`) are the same images at depth `d - g`, where the
  context list without its first `g` entries (`Lists::drop`) is a segment of the same ghost
  context (`typesRep_drop`); the inner `DefEq` is moved back to depth `d` by `DefEq.lift`, which
  fixes the images (they are scoped at `d - g`, `renFV_lift_of_wscoped`).
* **Node by node** (`k_is_def_eq_struct_safe`, `k_is_def_eq_struct_go`,
  `k_is_def_eq_struct_bounded`): equal variables have equal images; sorts at levels
  `level_equal` accepts (`DefEq.sort`); one constant at levels `level_list_eq` accepts
  (`DefEq.const`); literals of equal data; applications (`DefEq.app`); projections
  (`DefEq.proj`); binders compared under the left domain (`types_store_cons`, `tmk_open`,
  `defEq_lam_left`, `defEq_forallE_left`).
* **The slow tiers** chain reducts by `Red.trans` and carry a comparison of reducts back to the
  originals by `DefEq.redBoth`. -/

namespace IxVM.Refinement.Core.DefEqAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red DefEq DefEqList)

set_option linter.unusedVariables false

/-! ## Pairs and answers -/

private theorem tuple2_inj {a b c d : SourceValue F}
    (h : (.tuple [a, b] : SourceValue F) = .tuple [c, d]) : a = c ∧ b = d := by
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at h
  exact h

/-- A pair with first component `0` has no answer other than `0`. -/
private theorem ans_contra {r x y ans : SourceValue F} (h0 : r = .tuple [.field 0, y])
    (h1 : r = .tuple [ans, x]) (hans : ans ≠ .field 0) : False :=
  hans (tuple2_inj (h1.symm.trans h0)).1

private theorem val_zero' : ZMod.val (0 : F) = 0 := ZMod.val_zero

/-! ## The context list without its innermost entries -/

theorem segEntries_length (Γ : Nat → KExpr) (d n : Nat) : (segEntries Γ d n).length = n := by
  simp [segEntries]

/-- **Dropping the innermost `g` entries of a segment ending at `d`** leaves a segment ending at
`d - g`. -/
theorem segEntries_drop (Γ : Nat → KExpr) : ∀ (g d n : Nat), g ≤ n → n ≤ d →
    (segEntries Γ d n).drop g = segEntries Γ (d - g) (n - g)
  | 0, d, n, _, _ => by simp
  | g + 1, d, n, hg, hn => by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    rw [segEntries_succ, List.drop_succ_cons, segEntries_drop Γ g d' n' (by omega) (by omega),
      show d' + 1 - (g + 1) = d' - g by omega, show n' + 1 - (g + 1) = n' - g by omega]

private theorem seg_length {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {xs : List (Nat × KExpr)} {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [l] h r h' cs)
    (hl : RepList kexprListEnum (SegEntryRep κ Γ) h xs l) :
    r = .field (xs.length : F) ∧ h' = h :=
  Lib.Lists.length_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) (R := SegEntryRep κ Γ)
    (by rw [Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)

private theorem seg_drop {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {xs : List (Nat × KExpr)} {l r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [l, .field n] h r h' cs)
    (hl : RepList kexprListEnum (SegEntryRep κ Γ) h xs l) :
    ZMod.val n ≤ xs.length ∧
      RepList kexprListEnum (SegEntryRep κ Γ) h (xs.drop (ZMod.val n)) r ∧ h' = h := by
  have := Lib.Lists.drop_spec (t := .ptr (.named "KernelTypes::KExprNode" []))
    (R := SegEntryRep κ Γ) _ rfl
    (by rw [Obs.Names.«Lists::drop<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)
  rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at this
  exact this

/-- **`Lists::drop` on a context list**: without its innermost `g` entries, a context list at
depth `d` is one at depth `d - g`, and `g ≤ d`. -/
theorem typesRep_drop {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F} {d : Nat}
    {p q : SourceValue F} {n : F} {cs : List (Call F)} {h' : Heap F}
    (r : TypesRep κ Γ h d p)
    (ev : ObsFn W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [p, .field n] h q h' cs) :
    ZMod.val n ≤ d ∧ TypesRep κ Γ h (d - ZMod.val n) q ∧ h' = h := by
  obtain ⟨m, hm, hl⟩ := r.toRepList
  obtain ⟨hg, hq, rfl⟩ := seg_drop ev hl
  rw [segEntries_length] at hg
  rw [segEntries_drop Γ (ZMod.val n) d m hg hm] at hq
  exact ⟨by omega, TypesRep.ofRepList (by omega) hq, rfl⟩

/-! ## Index windows -/

private theorem idxAll_heap_mono {h h' : Heap F} {P Q : Nat → F → Prop}
    (ext : Heap.Extends h h') (hPQ : ∀ n i, P n i → Q n i) :
    ∀ {m : Nat} {p : SourceValue F}, Specs.Subst.IdxAll h P m p → Specs.Subst.IdxAll h' Q m p := by
  intro m p hp
  induction hp with
  | bvar cell hP => exact .bvar (ext.getElem?_eq cell) (hPQ _ _ hP)
  | sort cell => exact .sort (ext.getElem?_eq cell)
  | const cell => exact .const (ext.getElem?_eq cell)
  | lit cell => exact .lit (ext.getElem?_eq cell)
  | app cell _ _ ihf iha => exact .app (ext.getElem?_eq cell) ihf iha
  | lam cell _ _ iht ihb => exact .lam (ext.getElem?_eq cell) iht ihb
  | forallE cell _ _ iht ihb => exact .forallE (ext.getElem?_eq cell) iht ihb
  | letE cell _ _ _ iht ihv ihb => exact .letE (ext.getElem?_eq cell) iht ihv ihb
  | proj cell _ ihe => exact .proj (ext.getElem?_eq cell) ihe

/-- A window free of indices stays so in a larger heap, and so does a smaller window. -/
private theorem noIdx_mono {h h' : Heap F} {lo hi lo' hi' : Nat} {p : SourceValue F}
    (ext : Heap.Extends h h') (hlo : lo ≤ lo') (hhi : hi' ≤ hi)
    (hp : Specs.Subst.NoIdx h lo hi p) : Specs.Subst.NoIdx h' lo' hi' p :=
  idxAll_heap_mono (P := fun m i => ZMod.val i < lo + m ∨ hi + m ≤ ZMod.val i)
    (Q := fun m i => ZMod.val i < lo' + m ∨ hi' + m ≤ ZMod.val i) ext
    (fun m i (hm : ZMod.val i < lo + m ∨ hi + m ≤ ZMod.val i) =>
      (by omega : ZMod.val i < lo' + m ∨ hi' + m ≤ ZMod.val i)) hp

private theorem min_le_left' {x y : F} {a : Nat} (hx : ZMod.val x ≤ a) :
    ZMod.val (if ZMod.val x < ZMod.val y then x else y) ≤ a := by
  by_cases hxy : ZMod.val x < ZMod.val y
  · rw [ite_eq_left hxy]; exact hx
  · rw [ite_eq_right hxy]; omega

private theorem min_le_right' {x y : F} {a : Nat} (hy : ZMod.val y ≤ a) :
    ZMod.val (if ZMod.val x < ZMod.val y then x else y) ≤ a := by
  by_cases hxy : ZMod.val x < ZMod.val y
  · rw [ite_eq_left hxy]; omega
  · rw [ite_eq_right hxy]; exact hy

/-- **The rebase's count** (`lbr_min(lbr_min(ga, gb), y)`) is at most each glb. -/
private theorem min3_le {ga gb : Nat} {y : F} {v : SourceValue F} (hga : ga < 4294967296)
    (hgb : gb < 4294967296)
    (hv : v = .field (if ZMod.val (if ZMod.val (ga : F) < ZMod.val (gb : F) then (ga : F)
        else (gb : F)) < ZMod.val y then (if ZMod.val (ga : F) < ZMod.val (gb : F) then (ga : F)
        else (gb : F)) else y)) :
    ∃ s : F, v = .field s ∧ ZMod.val s ≤ ga ∧ ZMod.val s ≤ gb := by
  have ea : ZMod.val (ga : F) = ga :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  have eb : ZMod.val (gb : F) = gb :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  exact ⟨_, hv, min_le_left' (min_le_left' (le_of_eq ea)),
    min_le_left' (min_le_right' (le_of_eq eb))⟩

/-! ## Level lists -/

private theorem klev_load {h : Heap F} {p : SourceValue F} {c : String}
    {xs : List (SourceValue F)}
    (hl : loadValue h p = .ok (.construct Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» c xs)) :
    loadValue h p = .ok (.construct IxVM.Refinement.KernelLevels.klevelListEnum c xs) := by
  rw [← klevelListEnum_eq]; exact hl

end IxVM.Refinement.Core.DefEqAux

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red DefEq DefEqList)
open DefEqAux

set_option linter.unusedVariables false

/-! ## Level lists, binders, projections -/

/-- `KernelDefEq::level_list_eq`: pointwise `level_equal`, of equal lengths. -/
theorem level_list_eq_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::level_list_eq" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.level_list_eq c args h r h' calls := by
  intro a b hargs good us vs hus hvs hr
  subst hargs
  obtain ⟨ls, hls, hul⟩ := hus
  obtain ⟨ms, hms, hvm⟩ := hvs
  rcases Obs.«KernelDefEq::level_list_eq».obs ev with
    ⟨ld12, ld31, he39, he40, hc41⟩ |
    ⟨v20, ld12, ld31, hne42, he46, he47, hc48⟩ |
    ⟨x_x, x_xs, ld12, ld77, he85, he86, hc87⟩ |
    ⟨x_x, x_xs, x_y, x_ys, m106, cs117, ld12, ld77, ev119, he140, he141, hc142⟩ |
    ⟨x_x, x_xs, x_y, x_ys, v105, m106, cs117, cs150, ld12, ld77, ev119, hne143, ev152, hc169⟩
  · obtain rfl := RepList.nil_of_load hls (klev_load ld12)
    obtain rfl := RepList.nil_of_load hms (klev_load ld31)
    exact hul.trans hvm.symm
  · exact absurd he46 hr
  · exact absurd he85 hr
  · exact absurd he140 hr
  · subst hc169
    obtain ⟨l, ls', rfl, hl, hls'⟩ := RepList.cons_of_load hls (klev_load ld12)
    obtain ⟨m, ms', rfl, hm, hms'⟩ := RepList.cons_of_load hms (klev_load ld77)
    obtain ⟨hy, ext⟩ := ih.get (.levelOps .level_equal) (by lt_calls) ev119 x_x x_y rfl
      (good.sub fun x hx => by simp [hx]).2 l m hl hm
    have hlm : LvEq l m :=
      lvEq_of_levelEqual (LvEq.refl l) (LvEq.refl m) (of_ite_field_ne_zero hy hne143)
    have hrest := ih.get (.defEq .level_list_eq) (by lt_calls) ev152 x_xs x_ys rfl
      (good.sub fun x hx => by simp [hx]) ls' ms'
      ⟨ls', IxVM.Refinement.KernelLevels.RepKLevelList.mono hls' ext, LvEqList.refl ls'⟩
      ⟨ms', IxVM.Refinement.KernelLevels.RepKLevelList.mono hms' ext, LvEqList.refl ms'⟩ hr
    have hc : LvEqList (l :: ls') (m :: ms') := fun φ => ⟨hlm φ, hrest φ⟩
    exact hul.trans (hc.trans hvm.symm)

/-- `KernelDefEq::de_binder`: equal binder data (`pw_eq`), equal domains, equal bodies under
the left domain pushed on the context list. -/
theorem de_binder_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::de_binder" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.de_binder c args h r h' calls := by
  intro rc ta ba la tb bb lb types hargs good hrc d Γ htypes TA BA ℓa TB BB ℓb hTA hBA hla hTB
    hBB hlb hr
  subst hargs
  rcases Obs.«KernelDefEq::de_binder».obs ev with
    ⟨m2, cs13, m37, cs48, cs90, m119, ev15, ev50, hm127, ev92, hc147⟩ |
    ⟨m2, cs13, v36, m37, cs48, ev15, ev50, hne148, he152, he153, hc154⟩ |
    ⟨v1, m2, cs13, ev15, hne155, he159, he160, hc161⟩
  · subst hm127 hc147
    have e0 := ObsFn.heap_extends ev15
    have x1 := e0.trans (ObsFn.heap_extends ev50)
    obtain ⟨hpw, -⟩ := ih.get (.levels .pw_eq) (by lt_calls) ev15 la lb rfl
      (good.sub fun x hx => by simp [hx]) ℓa ℓb hla hlb
    have hz : ℓa.zeronessOf = ℓb.zeronessOf := of_ite_field_ne_zero hpw field_one_ne_zero
    have hT := ih.get (.defEq .k_is_def_eq) (by lt_calls) ev50 rc ta tb types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) TA TB
      (Tm.mono e0 hTA) (Tm.mono e0 hTB) field_one_ne_zero
    have x2 := x1.trans (Heap.Extends.snoc m37 (.construct kexprListEnum "Cons" [ta, types]))
    have hB := ih.get (.defEq .k_is_def_eq) (by lt_calls) ev92 rc ba bb _ rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono x2 hrc) (d + 1) _
      (types_store_cons (types_mono x1 htypes) (Tm.mono x1 hTA)) _ _
      (tmk_open (T := TA) (Tm.mono x2 hBA)) (tmk_open (T := TA) (Tm.mono x2 hBB)) hr
    exact ⟨defEq_lam_left hT hB hz, defEq_forallE_left hT hB hz⟩
  · exact absurd he152 hr
  · exact absurd he159 hr

/-- `KernelDefEq::de_proj`: one structure address, one field, equal scrutinees. -/
theorem de_proj_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::de_proj" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.de_proj c args h r h' calls := by
  intro rc sa ia ea sb ib eb types hargs good hrc a b i j ha hb hia hib d Γ htypes EA EB hEA hEB
    hr
  subst hargs hia hib
  rcases Obs.«KernelDefEq::de_proj».obs ev with
    ⟨m2, cs13, cs62, ev15, op52, ev64, hc97⟩ |
    ⟨m2, cs13, v36, ev15, op52, hne98, he102, he103, hc104⟩ |
    ⟨v1, m2, cs13, ev15, hne105, he109, he110, hc111⟩
  · subst hc97
    obtain ⟨hy, -⟩ := Lib.address_eq_spec ev15 ha hb
    obtain rfl : a = b := of_ite_field_ne_zero hy field_one_ne_zero
    obtain ⟨k, hik, hjk⟩ := eq_of_sub_field op52
    injection hik with hik
    injection hjk with hjk
    subst hik hjk
    have e0 := ObsFn.heap_extends ev15
    exact .proj (ih.get (.defEq .k_is_def_eq) (by lt_calls) ev64 rc ea eb types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) EA EB
      (Tm.mono e0 hEA) (Tm.mono e0 hEB) hr)
  · exact absurd he102 hr
  · exact absurd he109 hr

/-- `KernelDefEq::try_same_proj_head_app`: projection heads compared by `de_proj`, then the
arguments pairwise (`DefEq.app` along the spine). -/
theorem try_same_proj_head_app_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::try_same_proj_head_app" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.try_same_proj_head_app c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  rcases Obs.«KernelDefEq::try_same_proj_head_app».obs ev with
    ⟨m2, cs12, x_ah, x_aa, m37, cs47, x_bh, x_ba, m72, cs83, ev14, ev49, ev85, he98, he99,
      hc100⟩ |
    ⟨m2, cs12, x_ah, x_aa, m37, cs47, x_bh, x_ba, v71, m72, cs83, m106, x114, y115, m116, cs125,
      cs139, x_sa, x_ia, x_ea, x_sb, x_ib, x_eb, m223, cs234, cs308, ev14, ev49, ev85, hne101,
      ev127, ev141, op121, ld165, ld199, ev236, ev310, hc343⟩ |
    ⟨m2, cs12, x_ah, x_aa, m37, cs47, x_bh, x_ba, v71, m72, cs83, m106, x114, y115, m116, cs125,
      cs139, x_sa, x_ia, x_ea, x_sb, x_ib, x_eb, v222, m223, cs234, ev14, ev49, ev85, hne101,
      ev127, ev141, op121, ld165, ld199, ev236, hne344, he348, he349, hc350⟩ |
    ⟨m2, cs12, x_ah, x_aa, m37, cs47, x_bh, x_ba, v71, m72, cs83, m106, x114, y115, m116, cs125,
      cs139, x_sa, x_ia, x_ea, v188, ev14, ev49, ev85, hne101, ev127, ev141, op121, ld165, ld199,
      hne351, he355, he356, hc357⟩ |
    ⟨m2, cs12, x_ah, x_aa, m37, cs47, x_bh, x_ba, v71, m72, cs83, m106, x114, y115, m116, cs125,
      cs139, v154, ev14, ev49, ev85, hne101, ev127, ev141, op121, ld165, hne358, he362, he363,
      hc364⟩ |
    ⟨m2, cs12, x_ah, x_aa, m37, cs47, x_bh, x_ba, v71, m72, cs83, v105, m106, x114, y115, m116,
      cs125, cs139, ev14, ev49, ev85, hne101, ev127, ev141, op121, hne365, he369, he370, hc371⟩
  · exact absurd he98 hr
  · subst hc343
    have e14 := ObsFn.heap_extends ev14
    have e49 := ObsFn.heap_extends ev49
    have e236 := ObsFn.heap_extends ev236
    have x37 : Heap.Extends m37 m106 := (ObsFn.heap_extends ev85).trans
      ((ObsFn.heap_extends ev127).trans (ObsFn.heap_extends ev141))
    have x2 : Heap.Extends m2 m106 := e49.trans x37
    have x0 : Heap.Extends h m106 := e14.trans x2
    obtain ⟨hd, sp, H, As, he1, hH, hAs, rfl⟩ := ih.get (.subst .collect_spine) (by lt_calls)
      ev14 a rfl (good.sub fun x hx => by simp [hx]) d Γ 0 A hA
    obtain ⟨rfl, rfl⟩ := tuple2_inj he1
    obtain ⟨hd', sp', H', Bs, he2, hH', hBs, rfl⟩ := ih.get (.subst .collect_spine) (by lt_calls)
      ev49 b rfl (good.sub fun x hx => by simp [hx]) d Γ 0 B (Tm.mono e14 hB)
    obtain ⟨rfl, rfl⟩ := tuple2_inj he2
    obtain ⟨a1, i, EA, rfl, rfl, ha1, hEA⟩ := (Tm.mono x2 hH).proj_of_load ld165
    obtain ⟨b1, j, EB, rfl, rfl, hb1, hEB⟩ := (Tm.mono x37 hH').proj_of_load ld199
    have hP := ih.get (.defEq .de_proj) (by lt_calls) ev236 rc x_sa _ x_ea x_sb _ x_eb types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono x0 hrc) a1 b1 i j ha1 hb1 rfl rfl d Γ
      (types_mono x0 htypes) EA EB hEA hEB field_one_ne_zero
    have x1 := x0.trans e236
    exact defEq_mkAppN_congr (ih.get (.defEq .de_args) (by lt_calls) ev310 rc x_aa x_ba types
      rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x1 hrc) d Γ (types_mono x1 htypes) As
      Bs (tml_mono (x2.trans e236) hAs) (tml_mono (x37.trans e236) hBs) hr) hP
  · exact absurd he348 hr
  · exact absurd he355 hr
  · exact absurd he362 hr
  · exact absurd he369 hr

/-! ## The rebase -/

/-- `KernelDefEq::k_def_eq_rebase`: with `g = 0`, the comparison under the trimmed context
list; otherwise the inputs lowered past their unused innermost `g` opened variables, compared
at depth `d - g` under the trimmed shorter list, and the `DefEq` moved back to `d`
(`DefEq.lift`, which fixes the scoped images). -/
theorem k_def_eq_rebase_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_def_eq_rebase" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.k_def_eq_rebase c args h r h' calls := by
  intro rc a b types base hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  rcases Obs.«KernelDefEq::k_def_eq_rebase».obs ev with
    ⟨m2, cs12, v15, v16, m18, cs26, v29, v30, m32, cs40, m59, cs67, m86, cs94, cs122, v128, m151,
      cs159, ev42, ev69, ev28, ev96, ev14, ev161, ev124, hc178⟩ |
    ⟨v1, m2, cs12, v15, v16, m18, cs26, v29, v30, m32, cs40, m59, cs67, m86, cs94, cs186, v190,
      v191, v192, m201, cs209, m236, cs244, m271, cs279, v282, v283, m285, cs293, ev42, ev69,
      ev28, ev96, ev14, hne179, ev211, ev246, ev295, op325, ev281, ev188, hc328⟩
  · subst hc178
    have x0 : Heap.Extends h m2 := (ObsFn.heap_extends ev42).trans
      ((ObsFn.heap_extends ev69).trans ((ObsFn.heap_extends ev28).trans
        ((ObsFn.heap_extends ev96).trans (ObsFn.heap_extends ev14))))
    have ht := ih.get (.subst .ctx_trim) (by lt_calls) ev161 types base rfl
      (good.sub fun x hx => by simp [hx]) Γ d (types_mono x0 htypes)
    have x1 := x0.trans (ObsFn.heap_extends ev161)
    exact ih.get (.defEq .k_is_def_eq_core) (by lt_calls) ev124 rc a b v128 rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono x1 hrc) d Γ ht A B (Tm.mono x1 hA)
      (Tm.mono x1 hB) hr
  · subst hc328
    have e42 := ObsFn.heap_extends ev42
    have e69 := ObsFn.heap_extends ev69
    have e28 := ObsFn.heap_extends ev28
    have e96 := ObsFn.heap_extends ev96
    have e14 := ObsFn.heap_extends ev14
    have e211 := ObsFn.heap_extends ev211
    have e246 := ObsFn.heap_extends ev246
    have e295 := ObsFn.heap_extends ev295
    have e281 := ObsFn.heap_extends ev281
    -- the two glbs, at cutoff `0`
    have hA0 : c.tmk d Γ (ZMod.val (0 : F)) h A a := by rw [val_zero']; exact hA
    have hB0 : c.tmk d Γ (ZMod.val (0 : F)) m32 B b := by rw [val_zero']; exact Tm.mono e42 hB
    obtain ⟨-, ga, rfl, hga, hna⟩ := ih.get (.subst .expr_glb) (by lt_calls) ev42 a 0 rfl
      (good.sub fun x hx => by simp [hx]) (by rw [val_zero']; omega)
    obtain ⟨-, gb, rfl, hgb, hnb⟩ := ih.get (.subst .expr_glb) (by lt_calls) ev69 b 0 rfl
      (good.sub fun x hx => by simp [hx]) (by rw [val_zero']; omega)
    -- the count `g`
    obtain ⟨-, -, -, rfl⟩ := ih.get (.subst .lbr_min) (by lt_calls) ev28 _ _ rfl
      (good.sub fun x hx => by simp [hx])
    have x18 : Heap.Extends h m18 := e42.trans (e69.trans e28)
    obtain ⟨n1, -, hl1⟩ := (types_mono x18 htypes).1.toRepList
    obtain ⟨rfl, -⟩ := seg_length ev96 hl1
    obtain ⟨-, -, -, hv1⟩ := ih.get (.subst .lbr_min) (by lt_calls) ev14 _ _ rfl
      (good.sub fun x hx => by simp [hx])
    obtain ⟨s, rfl, hsa, hsb⟩ := min3_le hga hgb hv1
    -- the dropped context list, at depth `d - g`
    have x2 : Heap.Extends h m2 := x18.trans (e96.trans e14)
    have x236 : Heap.Extends h m236 := x2.trans (e211.trans e246)
    obtain ⟨hgd, hdrop, -⟩ := typesRep_drop (types_mono x236 htypes).1 ev295
    have hs : GhostScoped Γ (d - ZMod.val s) := fun j hj => htypes.2 j (by omega)
    have ht := ih.get (.subst .ctx_trim) (by lt_calls) ev281 v282 v283 rfl
      (good.sub fun x hx => by simp [hx]) Γ (d - ZMod.val s) ⟨hdrop.mono e295, hs⟩
    -- the lowered terms
    have hAl : c.tm (d - ZMod.val s) Γ m201 A v190 := by
      have := ih.get (.subst .expr_lower) (by lt_calls) ev211 a s 0 rfl
        (good.sub fun x hx => by simp [hx]) 0 (ZMod.val s) (Nat.zero_add _).symm (Nat.zero_le _)
        d Γ A hgd (Tm.mono x2 hA0)
        (noIdx_mono x2 (by omega) (by omega) (hna d Γ A hA0))
      rwa [val_zero', Nat.sub_zero] at this
    have hBl : c.tm (d - ZMod.val s) Γ m236 B v191 := by
      have := ih.get (.subst .expr_lower) (by lt_calls) ev246 b s 0 rfl
        (good.sub fun x hx => by simp [hx]) 0 (ZMod.val s) (Nat.zero_add _).symm (Nat.zero_le _)
        d Γ B hgd (Tm.mono (e69.trans (e28.trans (e96.trans (e14.trans e211)))) hB0)
        (noIdx_mono (e69.trans (e28.trans (e96.trans (e14.trans e211)))) (by omega) (by omega)
          (hnb d Γ B hB0))
      rwa [val_zero', Nat.sub_zero] at this
    have x271 : Heap.Extends h m271 := x236.trans (e295.trans e281)
    have hin := ih.get (.defEq .k_is_def_eq_core) (by lt_calls) ev188 rc v190 v191 v192 rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono x271 hrc) (d - ZMod.val s) Γ ht A B
      (Tm.mono (e246.trans (e295.trans e281)) hAl) (Tm.mono (e295.trans e281) hBl) hr
    have hl := Ix.Kernel.Rules.DefEq.lift (Ix.Kernel.EnvExt.refl c.env) hc.env.storeClosed
      (g := ZMod.val s) hin
    rw [Ix.Kernel.Rules.renFV_lift_of_wscoped (Nat.le_refl _) (Tm.wscopedB hs hAl),
      Ix.Kernel.Rules.renFV_lift_of_wscoped (Nat.le_refl _) (Tm.wscopedB hs hBl),
      Nat.sub_add_cancel hgd] at hl
    exact hl

/-! ## Node by node -/

/-- `KernelDefEq::k_is_def_eq_struct_safe`: equal variables, sorts, binders. -/
theorem k_is_def_eq_struct_safe_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq_struct_safe" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.k_is_def_eq_struct_safe c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  rcases Obs.«KernelDefEq::k_is_def_eq_struct_safe».obs ev with
    ⟨x_i, x_j, cs52, v55, ld12, ld36, op69, ev54, hc72⟩ |
    ⟨x_i, v25, ld12, ld36, hne73, he77, he78, hc79⟩ |
    ⟨x_la, x_lb, cs119, ld12, ld103, ev121, hc138⟩ |
    ⟨x_la, v92, ld12, ld103, hne139, he143, he144, hc145⟩ |
    ⟨x_ty_a, x_body_a, x_la, x_ty_b, x_body_b, x_lb, cs205, ld12, ld179, ev207, hc272⟩ |
    ⟨x_ty_a, x_body_a, x_la, v168, ld12, ld179, hne273, he277, he278, hc279⟩ |
    ⟨x_ty_a, x_body_a, x_la, x_ty_b, x_body_b, x_lb, cs339, ld12, ld313, ev341, hc406⟩ |
    ⟨x_ty_a, x_body_a, x_la, v302, ld12, ld313, hne407, he411, he412, hc413⟩ |
    ⟨v1, ld12, hne80, hne146, hne280, hne414, he418, he419, hc420⟩
  · obtain ⟨hy, -⟩ := Lib.is_zero_spec ev54
    have h0 : v55 = .field 0 := of_ite_field_ne_zero hy hr
    subst h0
    obtain ⟨k, rfl, rfl⟩ := eq_of_sub_field op69
    obtain rfl := bvar_images_eq hA ld12 hB ld36 rfl
    exact .refl
  · exact absurd he77 hr
  · subst hc138
    obtain ⟨u, rfl, l, hl, hul⟩ := hA.sort_of_load ld12
    obtain ⟨v, rfl, m, hm, hvm⟩ := hB.sort_of_load ld103
    obtain ⟨hy, -⟩ := ih.get (.levelOps .level_equal) (by lt_calls) ev121 x_la x_lb rfl
      (good.sub fun x hx => by simp [hx]).2 l m hl hm
    exact .sort (lvEq_of_levelEqual hul hvm (of_ite_field_ne_zero hy hr))
  · exact absurd he143 hr
  · subst hc272
    obtain ⟨TA, BA, ℓa, rfl, hTA, hBA, hla⟩ := hA.lam_of_load ld12
    obtain ⟨TB, BB, ℓb, rfl, hTB, hBB, hlb⟩ := hB.lam_of_load ld179
    exact (ih.get (.defEq .de_binder) (by lt_calls) ev207 rc x_ty_a x_body_a x_la x_ty_b x_body_b
      x_lb types rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes TA BA ℓa TB BB ℓb hTA
      hBA hla hTB hBB hlb hr).1
  · exact absurd he277 hr
  · subst hc406
    obtain ⟨TA, BA, ℓa, rfl, hTA, hBA, hla⟩ := hA.forallE_of_load ld12
    obtain ⟨TB, BB, ℓb, rfl, hTB, hBB, hlb⟩ := hB.forallE_of_load ld313
    exact (ih.get (.defEq .de_binder) (by lt_calls) ev341 rc x_ty_a x_body_a x_la x_ty_b x_body_b
      x_lb types rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes TA BA ℓa TB BB ℓb hTA
      hBA hla hTB hBB hlb hr).2
  · exact absurd he411 hr
  · exact absurd he418 hr

/-- `KernelDefEq::k_is_def_eq_struct`: `k_is_def_eq_struct_go`. -/
theorem k_is_def_eq_struct_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq_struct" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.k_is_def_eq_struct c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  obtain ⟨cs4, ev6, hc39⟩ := Obs.«KernelDefEq::k_is_def_eq_struct».obs ev
  subst hc39
  exact ih.get (.defEq .k_is_def_eq_struct_go) (by lt_calls) ev6 rc a b types rfl
    (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB hr

/-- `KernelDefEq::k_is_def_eq_struct_go`: node by node; a constant or application pair that
does not compare falls back to the lazy-δ application comparison; a `λ` against another node is
η-expanded; a `Nat` literal against another node is expanded one layer (`Red.natLit`). -/
theorem k_is_def_eq_struct_go_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq_struct_go" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.k_is_def_eq_struct_go c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  rcases Obs.«KernelDefEq::k_is_def_eq_struct_go».obs ev with
    ⟨x_i, x_j, ld12, ld36, op65, he72, he73, hc74⟩ |
    ⟨x_i, x_j, v49, ld12, ld36, op65, hne75, he79, he80, hc81⟩ |
    ⟨x_i, v25, ld12, ld36, hne82, he86, he87, hc88⟩ |
    ⟨x_la, x_lb, cs128, ld12, ld112, ev130, hc147⟩ |
    ⟨x_la, v101, ld12, ld112, hne148, he152, he153, hc154⟩ |
    ⟨x_addr_a, x_lvls_a, x_addr_b, x_lvls_b, m202, cs213, cs239, ld12, ld183, ev215, ev241,
      hc258⟩ |
    ⟨x_addr_a, x_lvls_a, x_addr_b, x_lvls_b, v201, m202, cs213, cs266, ld12, ld183, ev215, hne259,
      ev268, hc301⟩ |
    ⟨x_addr_a, x_lvls_a, v172, cs309, ld12, ld183, hne302, ev311, hc344⟩ |
    ⟨x_fa, x_xa, x_fb, x_xb, m392, cs403, cs445, ld12, ld373, ev405, ev447, hc480⟩ |
    ⟨x_fa, x_xa, x_fb, x_xb, v391, m392, cs403, m486, cs497, cs539, ld12, ld373, ev405, hne481,
      ev499, ev541, hc574⟩ |
    ⟨x_fa, x_xa, x_fb, x_xb, v391, m392, cs403, v485, m486, cs497, ld12, ld373, ev405, hne481,
      ev499, hne575, he579, he580, hc581⟩ |
    ⟨x_fa, x_xa, v362, cs589, ld12, ld373, hne582, ev591, hc624⟩ |
    ⟨x_ta, x_ba, x_la, x_tb, x_bb, x_lb, cs684, ld12, ld658, ev686, hc751⟩ |
    ⟨x_ta, x_ba, x_la, v647, cs759, ld12, ld658, hne752, ev761, hc810⟩ |
    ⟨x_ta, x_ba, x_la, x_tb, x_bb, x_lb, cs870, ld12, ld844, ev872, hc937⟩ |
    ⟨x_ta, x_ba, x_la, v833, ld12, ld844, hne938, he942, he943, hc944⟩ |
    ⟨w952, w953, w954, ld12, he970, he971, hc972⟩ |
    ⟨x_la, x_lb, cs1012, ld12, ld996, ev1014, hc1031⟩ |
    ⟨v985, w1052, cs1061, v1065, m1076, cs1084, ld12, ld996, hne1032, ev1086, ev1063, hc1117⟩ |
    ⟨v985, w1125, ld12, ld996, hne1032, he1131, he1132, hc1133⟩ |
    ⟨x_struct_a, x_fidx_a, x_ea, x_struct_b, x_fidx_b, x_eb, cs1194, ld12, ld1168, ev1196,
      hc1261⟩ |
    ⟨x_struct_a, x_fidx_a, x_ea, v1157, ld12, ld1168, hne1262, he1266, he1267, hc1268⟩
  · obtain ⟨k, rfl, rfl⟩ := eq_of_sub_field op65
    obtain rfl := bvar_images_eq hA ld12 hB ld36 rfl
    exact .refl
  · exact absurd he79 hr
  · exact absurd he86 hr
  · subst hc147
    obtain ⟨u, rfl, l, hl, hul⟩ := hA.sort_of_load ld12
    obtain ⟨v, rfl, m, hm, hvm⟩ := hB.sort_of_load ld112
    obtain ⟨hy, -⟩ := ih.get (.levelOps .level_equal) (by lt_calls) ev130 x_la x_lb rfl
      (good.sub fun x hx => by simp [hx]).2 l m hl hm
    exact .sort (lvEq_of_levelEqual hul hvm (of_ite_field_ne_zero hy hr))
  · exact absurd he152 hr
  · subst hc258
    obtain ⟨a1, us, rfl, ha1, hus⟩ := hA.const_of_load ld12
    obtain ⟨a2, vs, rfl, ha2, hvs⟩ := hB.const_of_load ld183
    obtain ⟨hy, -⟩ := Lib.address_eq_spec ev215 ha1 ha2
    obtain rfl : a1 = a2 := of_ite_field_ne_zero hy field_one_ne_zero
    have e0 := ObsFn.heap_extends ev215
    exact .const (ih.get (.defEq .level_list_eq) (by lt_calls) ev241 x_lvls_a x_lvls_b rfl
      (good.sub fun x hx => by simp [hx]) us vs (LvListRep.mono e0 hus) (LvListRep.mono e0 hvs)
      hr)
  · subst hc301
    have e0 := ObsFn.heap_extends ev215
    exact ih.get (.defEq .try_lazy_delta_app) (by lt_calls) ev268 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) A B
      (Tm.mono e0 hA) (Tm.mono e0 hB) hr
  · subst hc344
    exact ih.get (.defEq .try_lazy_delta_app) (by lt_calls) ev311 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB hr
  · subst hc480
    have e0 := ObsFn.heap_extends ev405
    exact ih.get (.defEq .try_lazy_delta_app) (by lt_calls) ev447 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) A B
      (Tm.mono e0 hA) (Tm.mono e0 hB) hr
  · subst hc574
    have e0 := (ObsFn.heap_extends ev405).trans (ObsFn.heap_extends ev499)
    exact ih.get (.defEq .try_lazy_delta_app) (by lt_calls) ev541 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) A B
      (Tm.mono e0 hA) (Tm.mono e0 hB) hr
  · subst hc581
    obtain ⟨Fa, Xa, rfl, hFa, hXa⟩ := hA.app_of_load ld12
    obtain ⟨Fb, Xb, rfl, hFb, hXb⟩ := hB.app_of_load ld373
    have e0 := ObsFn.heap_extends ev405
    exact .app (ih.get (.defEq .k_is_def_eq) (by lt_calls) ev405 rc x_fa x_fb types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes Fa Fb hFa hFb hne481)
      (ih.get (.defEq .k_is_def_eq) (by lt_calls) ev499 rc x_xa x_xb types rfl
        (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) Xa Xb
        (Tm.mono e0 hXa) (Tm.mono e0 hXb) hne575)
  · subst hc624
    exact ih.get (.defEq .try_lazy_delta_app) (by lt_calls) ev591 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB hr
  · subst hc751
    obtain ⟨TA, BA, ℓa, rfl, hTA, hBA, hla⟩ := hA.lam_of_load ld12
    obtain ⟨TB, BB, ℓb, rfl, hTB, hBB, hlb⟩ := hB.lam_of_load ld658
    exact (ih.get (.defEq .de_binder) (by lt_calls) ev686 rc x_ta x_ba x_la x_tb x_bb x_lb types
      rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes TA BA ℓa TB BB ℓb hTA hBA hla hTB
      hBB hlb hr).1
  · subst hc810
    obtain ⟨TA, BA, ℓa, rfl, hTA, hBA, hla⟩ := hA.lam_of_load ld12
    exact ih.get (.defEq .try_eta_expand) (by lt_calls) ev761 rc x_ta x_ba x_la b types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes TA BA ℓa B hTA hBA hla hB hr
  · subst hc937
    obtain ⟨TA, BA, ℓa, rfl, hTA, hBA, hla⟩ := hA.forallE_of_load ld12
    obtain ⟨TB, BB, ℓb, rfl, hTB, hBB, hlb⟩ := hB.forallE_of_load ld844
    exact (ih.get (.defEq .de_binder) (by lt_calls) ev872 rc x_ta x_ba x_la x_tb x_bb x_lb types
      rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes TA BA ℓa TB BB ℓb hTA hBA hla hTB
      hBB hlb hr).2
  · exact absurd he942 hr
  · exact absurd he970 hr
  · subst hc1031
    obtain ⟨la, hla, -⟩ := tm_lit_data hA ld12
    obtain ⟨lb, hlb, -⟩ := tm_lit_data hB ld996
    obtain ⟨hy, -⟩ := ih.get (.levels .literal_eq) (by lt_calls) ev1014 x_la x_lb rfl
      (good.sub fun x hx => by simp [hx]) la lb hla hlb
    obtain rfl := lit_images_eq hA ld12 hB ld996 hla hlb (of_ite_field_ne_zero hy hr)
    exact .refl
  · subst hc1117
    obtain ⟨A', hA', hred⟩ := ih.get (.whnf .nat_lit_to_ctor_or_self) (by lt_calls) ev1086 rc a
      rfl (good.sub fun x hx => by simp [hx]) hrc d Γ A hA
    have e0 := ObsFn.heap_extends ev1086
    exact .redL hred (ih.get (.defEq .k_is_def_eq_struct_go) (by lt_calls) ev1063 rc v1065 b types
      rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) A' B
      hA' (Tm.mono e0 hB) hr)
  · exact absurd he1131 hr
  · subst hc1261
    obtain ⟨a1, i, EA, rfl, rfl, ha1, hEA⟩ := hA.proj_of_load ld12
    obtain ⟨b1, j, EB, rfl, rfl, hb1, hEB⟩ := hB.proj_of_load ld1168
    exact ih.get (.defEq .de_proj) (by lt_calls) ev1196 rc x_struct_a _ x_ea x_struct_b _ x_eb
      types rfl (good.sub fun x hx => by simp [hx]) hrc a1 b1 i j ha1 hb1 rfl rfl d Γ htypes EA EB
      hEA hEB hr
  · exact absurd he1266 hr

/-- `KernelDefEq::k_is_def_eq_struct_bounded`: node by node with a credit of head
normalizations (`k_is_def_eq_struct_spend` where the nodes do not match); binder bodies under
the left domain pushed on the context list. -/
theorem k_is_def_eq_struct_bounded_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq_struct_bounded" args h r h' calls)
    (ih : IH c calls) : Specs.DefEq.k_is_def_eq_struct_bounded c args h r h' calls := by
  intro rc a b credit types hargs good hrc d Γ htypes A B hA hB ans rest hr hans
  subst hargs
  rcases Obs.«KernelDefEq::k_is_def_eq_struct_bounded».obs ev with
    ⟨x_i, x_j, ld12, ld36, op65, he76, he90, hc91⟩ |
    ⟨x_i, x_j, v49, ld12, ld36, op65, hne92, he100, he114, hc115⟩ |
    ⟨x_i, v25, cs123, ld12, ld36, hne116, ev125, hc166⟩ |
    ⟨x_la, x_lb, v205, m209, cs217, ld12, ld190, he207, ev219, he243, hc244⟩ |
    ⟨x_la, v179, cs252, ld12, ld190, hne245, ev254, hc295⟩ |
    ⟨x_addr_a, x_lvls_a, x_addr_b, x_lvls_b, m343, cs354, v379, m383, cs391, ld12, ld324, ev356,
      he381, ev393, he417, hc418⟩ |
    ⟨x_addr_a, x_lvls_a, x_addr_b, x_lvls_b, v342, m343, cs354, cs426, ld12, ld324, ev356, hne419,
      ev428, hc469⟩ |
    ⟨x_addr_a, x_lvls_a, v313, cs477, ld12, ld324, hne470, ev479, hc520⟩ |
    ⟨x_fa, x_xa, x_fb, x_xb, m568, cs579, x_rest, cs643, ld12, ld549, ev581, ev645, hc686⟩ |
    ⟨x_fa, x_xa, x_fb, x_xb, m568, cs579, w693, x_rest, ld12, ld549, ev581, he708, he722,
      hc723⟩ |
    ⟨x_fa, x_xa, v538, cs732, ld12, ld549, hne725, ev734, hc775⟩ |
    ⟨x_ta, x_ba, x_la, x_tb, x_bb, x_lb, m833, cs844, m868, cs879, x_rest, m941, cs974, ld12,
      ld809, ev846, ev881, hm951, ev976, hc1017⟩ |
    ⟨x_ta, x_ba, x_la, x_tb, x_bb, x_lb, m833, cs844, m868, cs879, w1024, x_rest, ld12, ld809,
      ev846, ev881, he1039, he1053, hc1054⟩ |
    ⟨x_ta, x_ba, x_la, x_tb, x_bb, x_lb, v832, m833, cs844, ld12, ld809, ev846, hne1056, he1064,
      he1078, hc1079⟩ |
    ⟨x_ta, x_ba, x_la, v798, cs1087, ld12, ld809, hne1080, ev1089, hc1130⟩ |
    ⟨x_ta, x_ba, x_la, x_tb, x_bb, x_lb, m1188, cs1199, m1223, cs1234, x_rest, m1296, cs1329,
      ld12, ld1164, ev1201, ev1236, hm1306, ev1331, hc1372⟩ |
    ⟨x_ta, x_ba, x_la, x_tb, x_bb, x_lb, m1188, cs1199, m1223, cs1234, w1379, x_rest, ld12,
      ld1164, ev1201, ev1236, he1394, he1408, hc1409⟩ |
    ⟨x_ta, x_ba, x_la, x_tb, x_bb, x_lb, v1187, m1188, cs1199, ld12, ld1164, ev1201, hne1411,
      he1419, he1433, hc1434⟩ |
    ⟨x_ta, x_ba, x_la, v1153, cs1442, ld12, ld1164, hne1435, ev1444, hc1485⟩ |
    ⟨x_la, x_lb, v1524, m1528, cs1536, ld12, ld1509, he1526, ev1538, he1562, hc1563⟩ |
    ⟨x_la, v1498, cs1571, ld12, ld1509, hne1564, ev1573, hc1614⟩ |
    ⟨x_struct_a, x_fidx_a, x_ea, x_struct_b, x_fidx_b, x_eb, m1672, cs1683, cs1732, ld12, ld1648,
      ev1685, op1722, ev1734, hc1775⟩ |
    ⟨x_struct_a, x_fidx_a, x_ea, x_struct_b, x_fidx_b, x_eb, m1672, cs1683, v1706, ld12, ld1648,
      ev1685, op1722, hne1776, he1784, he1798, hc1799⟩ |
    ⟨x_struct_a, x_fidx_a, x_ea, x_struct_b, x_fidx_b, x_eb, v1671, m1672, cs1683, cs1807, ld12,
      ld1648, ev1685, hne1800, ev1809, hc1850⟩ |
    ⟨x_struct_a, x_fidx_a, x_ea, v1637, cs1858, ld12, ld1648, hne1851, ev1860, hc1901⟩ |
    ⟨v1, cs1909, ld12, hne167, hne296, hne521, hne776, hne1131, hne1486, hne1615, hne1902, ev1911,
      hc1952⟩
  -- equal variables
  · obtain ⟨k, rfl, rfl⟩ := eq_of_sub_field op65
    obtain rfl := bvar_images_eq hA ld12 hB ld36 rfl
    exact .refl
  · exact (ans_contra he100 hr hans).elim
  · subst hc166
    exact ih.get (.defEq .k_is_def_eq_struct_spend) (by lt_calls) ev125 rc a b credit types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB ans rest hr hans
  -- sorts
  · subst he207 hc244
    obtain ⟨rfl, -⟩ := tuple2_inj hr
    obtain ⟨u, rfl, l, hl, hul⟩ := hA.sort_of_load ld12
    obtain ⟨v, rfl, m, hm, hvm⟩ := hB.sort_of_load ld190
    obtain ⟨hy, -⟩ := ih.get (.levelOps .level_equal) (by lt_calls) ev219 x_la x_lb rfl
      (good.sub fun x hx => by simp [hx]).2 l m hl hm
    exact .sort (lvEq_of_levelEqual hul hvm (of_ite_field_ne_zero hy hans))
  · subst hc295
    exact ih.get (.defEq .k_is_def_eq_struct_spend) (by lt_calls) ev254 rc a b credit types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB ans rest hr hans
  -- constants
  · subst he381 hc418
    obtain ⟨rfl, -⟩ := tuple2_inj hr
    obtain ⟨a1, us, rfl, ha1, hus⟩ := hA.const_of_load ld12
    obtain ⟨a2, vs, rfl, ha2, hvs⟩ := hB.const_of_load ld324
    obtain ⟨hy, -⟩ := Lib.address_eq_spec ev356 ha1 ha2
    obtain rfl : a1 = a2 := of_ite_field_ne_zero hy field_one_ne_zero
    have e0 := ObsFn.heap_extends ev356
    exact .const (ih.get (.defEq .level_list_eq) (by lt_calls) ev393 x_lvls_a x_lvls_b rfl
      (good.sub fun x hx => by simp [hx]) us vs (LvListRep.mono e0 hus) (LvListRep.mono e0 hvs)
      hans)
  · subst hc469
    have e0 := ObsFn.heap_extends ev356
    exact ih.get (.defEq .k_is_def_eq_struct_spend) (by lt_calls) ev428 rc a b credit types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) A B
      (Tm.mono e0 hA) (Tm.mono e0 hB) ans rest hr hans
  · subst hc520
    exact ih.get (.defEq .k_is_def_eq_struct_spend) (by lt_calls) ev479 rc a b credit types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB ans rest hr hans
  -- applications
  · subst hc686
    obtain ⟨Fa, Xa, rfl, hFa, hXa⟩ := hA.app_of_load ld12
    obtain ⟨Fb, Xb, rfl, hFb, hXb⟩ := hB.app_of_load ld549
    have e0 := ObsFn.heap_extends ev581
    exact .app (ih.get (.defEq .k_is_def_eq_struct_bounded) (by lt_calls) ev581 rc x_fa x_fb credit
      types rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes Fa Fb hFa hFb (.field 1)
      x_rest rfl field_one_ne_zero)
      (ih.get (.defEq .k_is_def_eq_struct_bounded) (by lt_calls) ev645 rc x_xa x_xb x_rest types
        rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) Xa
        Xb (Tm.mono e0 hXa) (Tm.mono e0 hXb) ans rest hr hans)
  · exact (ans_contra he708 hr hans).elim
  · subst hc775
    exact ih.get (.defEq .k_is_def_eq_struct_spend) (by lt_calls) ev734 rc a b credit types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB ans rest hr hans
  -- λ
  · subst hm951 hc1017
    obtain ⟨TA, BA, ℓa, rfl, hTA, hBA, hla⟩ := hA.lam_of_load ld12
    obtain ⟨TB, BB, ℓb, rfl, hTB, hBB, hlb⟩ := hB.lam_of_load ld809
    have e0 := ObsFn.heap_extends ev846
    have x1 := e0.trans (ObsFn.heap_extends ev881)
    obtain ⟨hpw, -⟩ := ih.get (.levels .pw_eq) (by lt_calls) ev846 x_la x_lb rfl
      (good.sub fun x hx => by simp [hx]) ℓa ℓb hla hlb
    have hz : ℓa.zeronessOf = ℓb.zeronessOf := of_ite_field_ne_zero hpw field_one_ne_zero
    have hT := ih.get (.defEq .k_is_def_eq_struct_bounded) (by lt_calls) ev881 rc x_ta x_tb credit
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ
      (types_mono e0 htypes) TA TB (Tm.mono e0 hTA) (Tm.mono e0 hTB) (.field 1) x_rest rfl
      field_one_ne_zero
    have x2 := x1.trans (Heap.Extends.snoc m868 (.construct kexprListEnum "Cons" [x_ta, types]))
    have hBd := ih.get (.defEq .k_is_def_eq_struct_bounded) (by lt_calls) ev976 rc x_ba x_bb x_rest
      _ rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x2 hrc) (d + 1) _
      (types_store_cons (types_mono x1 htypes) (Tm.mono x1 hTA)) _ _
      (tmk_open (T := TA) (Tm.mono x2 hBA)) (tmk_open (T := TA) (Tm.mono x2 hBB)) ans rest hr
      hans
    exact defEq_lam_left hT hBd hz
  · exact (ans_contra he1039 hr hans).elim
  · exact (ans_contra he1064 hr hans).elim
  · subst hc1130
    exact ih.get (.defEq .k_is_def_eq_struct_spend) (by lt_calls) ev1089 rc a b credit types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB ans rest hr hans
  -- ∀
  · subst hm1306 hc1372
    obtain ⟨TA, BA, ℓa, rfl, hTA, hBA, hla⟩ := hA.forallE_of_load ld12
    obtain ⟨TB, BB, ℓb, rfl, hTB, hBB, hlb⟩ := hB.forallE_of_load ld1164
    have e0 := ObsFn.heap_extends ev1201
    have x1 := e0.trans (ObsFn.heap_extends ev1236)
    obtain ⟨hpw, -⟩ := ih.get (.levels .pw_eq) (by lt_calls) ev1201 x_la x_lb rfl
      (good.sub fun x hx => by simp [hx]) ℓa ℓb hla hlb
    have hz : ℓa.zeronessOf = ℓb.zeronessOf := of_ite_field_ne_zero hpw field_one_ne_zero
    have hT := ih.get (.defEq .k_is_def_eq_struct_bounded) (by lt_calls) ev1236 rc x_ta x_tb
      credit types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ
      (types_mono e0 htypes) TA TB (Tm.mono e0 hTA) (Tm.mono e0 hTB) (.field 1) x_rest rfl
      field_one_ne_zero
    have x2 := x1.trans (Heap.Extends.snoc m1223 (.construct kexprListEnum "Cons" [x_ta, types]))
    have hBd := ih.get (.defEq .k_is_def_eq_struct_bounded) (by lt_calls) ev1331 rc x_ba x_bb
      x_rest _ rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x2 hrc) (d + 1) _
      (types_store_cons (types_mono x1 htypes) (Tm.mono x1 hTA)) _ _
      (tmk_open (T := TA) (Tm.mono x2 hBA)) (tmk_open (T := TA) (Tm.mono x2 hBB)) ans rest hr
      hans
    exact defEq_forallE_left hT hBd hz
  · exact (ans_contra he1394 hr hans).elim
  · exact (ans_contra he1419 hr hans).elim
  · subst hc1485
    exact ih.get (.defEq .k_is_def_eq_struct_spend) (by lt_calls) ev1444 rc a b credit types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB ans rest hr hans
  -- literals
  · subst he1526 hc1563
    obtain ⟨rfl, -⟩ := tuple2_inj hr
    obtain ⟨la, hla, -⟩ := tm_lit_data hA ld12
    obtain ⟨lb, hlb, -⟩ := tm_lit_data hB ld1509
    obtain ⟨hy, -⟩ := ih.get (.levels .literal_eq) (by lt_calls) ev1538 x_la x_lb rfl
      (good.sub fun x hx => by simp [hx]) la lb hla hlb
    obtain rfl := lit_images_eq hA ld12 hB ld1509 hla hlb (of_ite_field_ne_zero hy hans)
    exact .refl
  · subst hc1614
    exact ih.get (.defEq .k_is_def_eq_struct_spend) (by lt_calls) ev1573 rc a b credit types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB ans rest hr hans
  -- projections
  · subst hc1775
    obtain ⟨a1, i, EA, rfl, rfl, ha1, hEA⟩ := hA.proj_of_load ld12
    obtain ⟨b1, j, EB, rfl, rfl, hb1, hEB⟩ := hB.proj_of_load ld1648
    obtain ⟨hy, -⟩ := Lib.address_eq_spec ev1685 ha1 hb1
    obtain rfl : a1 = b1 := of_ite_field_ne_zero hy field_one_ne_zero
    obtain ⟨k, hik, hjk⟩ := eq_of_sub_field op1722
    injection hik with hik
    injection hjk with hjk
    subst hik hjk
    have e0 := ObsFn.heap_extends ev1685
    exact .proj (ih.get (.defEq .k_is_def_eq_struct_bounded) (by lt_calls) ev1734 rc x_ea x_eb
      credit types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ
      (types_mono e0 htypes) EA EB (Tm.mono e0 hEA) (Tm.mono e0 hEB) ans rest hr hans)
  · exact (ans_contra he1784 hr hans).elim
  · subst hc1850
    have e0 := ObsFn.heap_extends ev1685
    exact ih.get (.defEq .k_is_def_eq_struct_spend) (by lt_calls) ev1809 rc a b credit types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) A B
      (Tm.mono e0 hA) (Tm.mono e0 hB) ans rest hr hans
  · subst hc1901
    exact ih.get (.defEq .k_is_def_eq_struct_spend) (by lt_calls) ev1860 rc a b credit types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB ans rest hr hans
  · subst hc1952
    exact ih.get (.defEq .k_is_def_eq_struct_spend) (by lt_calls) ev1911 rc a b credit types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB ans rest hr hans

/-- `KernelDefEq::k_is_def_eq_struct_spend`: one credit spent on head-normalizing both sides,
then `Nat` offsets, the lazy-δ loop, or the bounded structural comparison of the loop's
reducts. -/
theorem k_is_def_eq_struct_spend_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq_struct_spend" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.k_is_def_eq_struct_spend c args h r h' calls := by
  intro rc a b credit types hargs good hrc d Γ htypes A B hA hB ans rest hr hans
  subst hargs
  rcases Obs.«KernelDefEq::k_is_def_eq_struct_spend».obs ev with
    ⟨hv14, he19, he32, hc33⟩ |
    ⟨v38, v55, m56, cs66, v93, m94, cs104, m132, cs143, x_eq, hne34, op53, ev68, ev106, ev145,
      he200, he215, hc216⟩ |
    ⟨v38, v55, m56, cs66, v93, m94, cs104, v131, m132, cs143, m221, cs232, w281, w282, hne34,
      op53, ev68, ev106, ev145, ev234, he303, he317, hc318⟩ |
    ⟨v38, v55, m56, cs66, v93, m94, cs104, v131, m132, cs143, m221, cs232, w325, x_fa, x_fb, cs344,
      hne34, op53, ev68, ev106, ev145, ev234, ev346, hc387⟩
  · exact (ans_contra he19 hr hans).elim
  all_goals
    first | subst hc216 | subst hc318 | subst hc387
    obtain ⟨Aw, hAw, hra⟩ := ih.get (.whnf .whnf_nd) (by lt_calls) ev68 rc a types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A hA
    have e0 := ObsFn.heap_extends ev68
    obtain ⟨Bw, hBw, hrb⟩ := ih.get (.whnf .whnf_nd) (by lt_calls) ev106 rc b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) B
      (Tm.mono e0 hB)
    have e1 := ObsFn.heap_extends ev106
    have x1 := e0.trans e1
  · subst he200
    obtain ⟨rfl, -⟩ := tuple2_inj hr
    exact .redBoth hra hrb (ih.get (.defEq .try_def_eq_nat) (by lt_calls) ev145 rc v55 v93 types
      rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x1 hrc) d Γ (types_mono x1 htypes) Aw Bw
      (Tm.mono e1 hAw) hBw x_eq rfl hans)
  · have x2 := x1.trans (ObsFn.heap_extends ev145)
    obtain ⟨_, _, _, _, _, _, hd⟩ := ih.get (.defEq .lazy_delta_loop) (by lt_calls) ev234 rc v55
      v93 (.field 8) types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x2 hrc) d Γ
      (types_mono x2 htypes) Aw Bw (Tm.mono (e1.trans (ObsFn.heap_extends ev145)) hAw)
      (Tm.mono (ObsFn.heap_extends ev145) hBw) _ _ _ rfl
    exact .redBoth hra hrb (hd field_one_ne_zero)
  · have e2 := ObsFn.heap_extends ev145
    have x2 := x1.trans e2
    obtain ⟨FA, FB, hFA, hFB, hraF, hrbF, -⟩ := ih.get (.defEq .lazy_delta_loop) (by lt_calls)
      ev234 rc v55 v93 (.field 8) types rfl (good.sub fun x hx => by simp [hx])
      (RCRep.mono x2 hrc) d Γ (types_mono x2 htypes) Aw Bw (Tm.mono (e1.trans e2) hAw)
      (Tm.mono e2 hBw) _ _ _ rfl
    have x3 := x2.trans (ObsFn.heap_extends ev234)
    exact .redBoth (.trans hra hraF) (.trans hrb hrbF)
      (ih.get (.defEq .k_is_def_eq_struct_bounded) (by lt_calls) ev346 rc x_fa x_fb v38 types rfl
        (good.sub fun x hx => by simp [hx]) (RCRep.mono x3 hrc) d Γ (types_mono x3 htypes) FA FB
        hFA hFB ans rest hr hans)

/-! ## The structure tree -/

/-- `KernelDefEq::k_is_def_eq_structure_tree_app`: two applications, function and argument
compared by the structure tree (`DefEq.app`). -/
theorem k_is_def_eq_structure_tree_app_step (c : Ctx) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq_structure_tree_app" args h r h' calls)
    (ih : IH c calls) : Specs.DefEq.k_is_def_eq_structure_tree_app c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  rcases Obs.«KernelDefEq::k_is_def_eq_structure_tree_app».obs ev with
    ⟨x_af, x_ax, x_bf, x_bx, m60, cs71, cs113, ld12, ld41, ev73, ev115, hc148⟩ |
    ⟨x_af, x_ax, x_bf, x_bx, v59, m60, cs71, ld12, ld41, ev73, hne149, he153, he154, hc155⟩ |
    ⟨x_af, x_ax, v30, ld12, ld41, hne156, he160, he161, hc162⟩ |
    ⟨v1, ld12, hne163, he167, he168, hc169⟩
  · subst hc148
    obtain ⟨Fa, Xa, rfl, hFa, hXa⟩ := hA.app_of_load ld12
    obtain ⟨Fb, Xb, rfl, hFb, hXb⟩ := hB.app_of_load ld41
    have e0 := ObsFn.heap_extends ev73
    exact .app (ih.get (.defEq .k_is_def_eq_structure_tree) (by lt_calls) ev73 rc x_af x_bf types
      rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes Fa Fb hFa hFb field_one_ne_zero)
      (ih.get (.defEq .k_is_def_eq_structure_tree) (by lt_calls) ev115 rc x_ax x_bx types rfl
        (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) Xa Xb
        (Tm.mono e0 hXa) (Tm.mono e0 hXb) hr)
  · exact absurd he153 hr
  · exact absurd he160 hr
  · exact absurd he167 hr

/-- `KernelDefEq::k_is_def_eq_structure_tree`: the bounded structural tier, projection-headed
spines, then application nodes. -/
theorem k_is_def_eq_structure_tree_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq_structure_tree" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.k_is_def_eq_structure_tree c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  rcases Obs.«KernelDefEq::k_is_def_eq_structure_tree».obs ev with
    ⟨m2, cs13, w62, ev15, he74, he75, hc76⟩ |
    ⟨v1, m2, cs13, m81, cs92, ev15, ev94, he131, he132, hc133⟩ |
    ⟨v1, m2, cs13, v80, m81, cs92, cs141, ev15, ev94, hne134, ev143, hc176⟩
  · subst hc76
    exact ih.get (.defEq .k_is_def_eq_struct_bounded) (by lt_calls) ev15 rc a b (.field 8) types
      rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB (.field 1) w62 rfl
      field_one_ne_zero
  · subst hc133
    have e0 := ObsFn.heap_extends ev15
    exact ih.get (.defEq .try_same_proj_head_app) (by lt_calls) ev94 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) A B
      (Tm.mono e0 hA) (Tm.mono e0 hB) field_one_ne_zero
  · subst hc176
    have e0 := (ObsFn.heap_extends ev15).trans (ObsFn.heap_extends ev94)
    exact ih.get (.defEq .k_is_def_eq_structure_tree_app) (by lt_calls) ev143 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) A B
      (Tm.mono e0 hA) (Tm.mono e0 hB) hr

/-! ## The slow tiers -/

/-- `KernelDefEq::k_is_def_eq_slow`: string literals, then `k_is_def_eq_slow_nd`. -/
theorem k_is_def_eq_slow_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq_slow" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.k_is_def_eq_slow c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  rcases Obs.«KernelDefEq::k_is_def_eq_slow».obs ev with
    ⟨m2, cs13, ev15, he52, he53, hc54⟩ | ⟨v1, m2, cs13, cs62, ev15, hne55, ev64, hc97⟩
  · subst hc54
    exact ih.get (.defEq .try_string_lit_pair) (by lt_calls) ev15 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB field_one_ne_zero
  · subst hc97
    have e0 := ObsFn.heap_extends ev15
    exact ih.get (.defEq .k_is_def_eq_slow_nd) (by lt_calls) ev64 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) A B
      (Tm.mono e0 hA) (Tm.mono e0 hB) hr

/-- `KernelDefEq::k_is_def_eq_slow_nd`: both sides head-normalized by `whnf_struct_core`,
compared structurally and by spines, then `k_is_def_eq_slow_nd_after_core`. -/
theorem k_is_def_eq_slow_nd_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq_slow_nd" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.k_is_def_eq_slow_nd c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  rcases Obs.«KernelDefEq::k_is_def_eq_slow_nd».obs ev with
    ⟨v1, m2, cs12, v39, m40, cs50, m78, cs89, ev14, ev52, ev91, he128, he129, hc130⟩ |
    ⟨v1, m2, cs12, v39, m40, cs50, v77, m78, cs89, m136, cs147, ev14, ev52, ev91, hne131, ev149,
      he186, he187, hc188⟩ |
    ⟨v1, m2, cs12, v39, m40, cs50, v77, m78, cs89, v135, m136, cs147, cs196, ev14, ev52, ev91,
      hne131, ev149, hne189, ev198, hc247⟩
  all_goals
    first | subst hc130 | subst hc188 | subst hc247
    obtain ⟨Ac, hAc, hra⟩ := ih.get (.whnf .whnf_struct_core) (by lt_calls) ev14 rc a types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A hA
    have e0 := ObsFn.heap_extends ev14
    obtain ⟨Bc, hBc, hrb⟩ := ih.get (.whnf .whnf_struct_core) (by lt_calls) ev52 rc b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) B
      (Tm.mono e0 hB)
    have e1 := ObsFn.heap_extends ev52
    have x1 := e0.trans e1
  · exact .redBoth hra hrb (ih.get (.defEq .k_is_def_eq_struct_safe) (by lt_calls) ev91 rc v1 v39
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x1 hrc) d Γ
      (types_mono x1 htypes) Ac Bc (Tm.mono e1 hAc) hBc field_one_ne_zero)
  · have e2 := ObsFn.heap_extends ev91
    have x2 := x1.trans e2
    exact .redBoth hra hrb (ih.get (.defEq .try_def_eq_app) (by lt_calls) ev149 rc v1 v39 types
      rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x2 hrc) d Γ (types_mono x2 htypes) Ac
      Bc (Tm.mono (e1.trans e2) hAc) (Tm.mono e2 hBc) field_one_ne_zero)
  · have e2 := (ObsFn.heap_extends ev91).trans (ObsFn.heap_extends ev149)
    have x2 := x1.trans e2
    exact ih.get (.defEq .k_is_def_eq_slow_nd_after_core) (by lt_calls) ev198 rc a b v1 v39 types
      rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x2 hrc) d Γ (types_mono x2 htypes) A B
      Ac Bc (Tm.mono x2 hA) (Tm.mono x2 hB) (Tm.mono (e1.trans e2) hAc) (Tm.mono e2 hBc) hra hrb
      hr

/-- `KernelDefEq::k_is_def_eq_slow_nd_after_core`: the reducts head-normalized further
(`whnf_nd`), compared structurally and by spines, then `k_is_def_eq_slow2`. -/
theorem k_is_def_eq_slow_nd_after_core_step (c : Ctx) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq_slow_nd_after_core" args h r h' calls)
    (ih : IH c calls) : Specs.DefEq.k_is_def_eq_slow_nd_after_core c args h r h' calls := by
  intro rc oa ob a b types hargs good hrc d Γ htypes A0 B0 A B hA0 hB0 hA hB hra0 hrb0 hr
  subst hargs
  rcases Obs.«KernelDefEq::k_is_def_eq_slow_nd_after_core».obs ev with
    ⟨v1, m2, cs12, v39, m40, cs50, m78, cs89, ev14, ev52, ev91, he128, he129, hc130⟩ |
    ⟨v1, m2, cs12, v39, m40, cs50, v77, m78, cs89, m136, cs147, ev14, ev52, ev91, hne131, ev149,
      he186, he187, hc188⟩ |
    ⟨v1, m2, cs12, v39, m40, cs50, v77, m78, cs89, v135, m136, cs147, cs196, ev14, ev52, ev91,
      hne131, ev149, hne189, ev198, hc247⟩
  all_goals
    first | subst hc130 | subst hc188 | subst hc247
    obtain ⟨Aw, hAw, hra⟩ := ih.get (.whnf .whnf_nd) (by lt_calls) ev14 rc a types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A hA
    have e0 := ObsFn.heap_extends ev14
    obtain ⟨Bw, hBw, hrb⟩ := ih.get (.whnf .whnf_nd) (by lt_calls) ev52 rc b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) B
      (Tm.mono e0 hB)
    have e1 := ObsFn.heap_extends ev52
    have x1 := e0.trans e1
  · exact .redBoth (.trans hra0 hra) (.trans hrb0 hrb) (ih.get (.defEq .k_is_def_eq_struct_safe)
      (by lt_calls) ev91 rc v1 v39 types rfl (good.sub fun x hx => by simp [hx])
      (RCRep.mono x1 hrc) d Γ (types_mono x1 htypes) Aw Bw (Tm.mono e1 hAw) hBw field_one_ne_zero)
  · have e2 := ObsFn.heap_extends ev91
    have x2 := x1.trans e2
    exact .redBoth (.trans hra0 hra) (.trans hrb0 hrb) (ih.get (.defEq .try_def_eq_app)
      (by lt_calls) ev149 rc v1 v39 types rfl (good.sub fun x hx => by simp [hx])
      (RCRep.mono x2 hrc) d Γ (types_mono x2 htypes) Aw Bw (Tm.mono (e1.trans e2) hAw)
      (Tm.mono e2 hBw) field_one_ne_zero)
  · have e2 := (ObsFn.heap_extends ev91).trans (ObsFn.heap_extends ev149)
    have x2 := x1.trans e2
    exact ih.get (.defEq .k_is_def_eq_slow2) (by lt_calls) ev198 rc oa ob v1 v39 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono x2 hrc) d Γ (types_mono x2 htypes) A0 B0 Aw
      Bw (Tm.mono x2 hA0) (Tm.mono x2 hB0) (Tm.mono (e1.trans e2) hAw) (Tm.mono e2 hBw)
      (.trans hra0 hra) (.trans hrb0 hrb) hr

/-- `KernelDefEq::k_is_def_eq_slow2`: the rescue tier, the lazy-δ loop, then
`slow2_after_delta` on the loop's reducts. -/
theorem k_is_def_eq_slow2_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq_slow2" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.k_is_def_eq_slow2 c args h r h' calls := by
  intro rc oa ob a b types hargs good hrc d Γ htypes A0 B0 A B hA0 hB0 hA hB hra0 hrb0 hr
  subst hargs
  rcases Obs.«KernelDefEq::k_is_def_eq_slow2».obs ev with
    ⟨m2, cs13, x_eq, ev15, he67, he68, hc69⟩ |
    ⟨v1, m2, cs13, m74, cs85, w134, w135, ev15, ev87, he152, he153, hc154⟩ |
    ⟨v1, m2, cs13, m74, cs85, w161, x_fa, x_fb, cs180, ev15, ev87, ev182, hc231⟩
  · subst he67 hc69
    exact .redBoth hra0 hrb0 (ih.get (.defEq .de_rescue_tier) (by lt_calls) ev15 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB r rfl hr)
  · subst hc154
    have e0 := ObsFn.heap_extends ev15
    obtain ⟨_, _, _, _, _, _, hd⟩ := ih.get (.defEq .lazy_delta_loop) (by lt_calls) ev87 rc a b
      (.field 16) types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ
      (types_mono e0 htypes) A B (Tm.mono e0 hA) (Tm.mono e0 hB) _ _ _ rfl
    exact .redBoth hra0 hrb0 (hd field_one_ne_zero)
  · subst hc231
    have e0 := ObsFn.heap_extends ev15
    obtain ⟨FA, FB, hFA, hFB, hraF, hrbF, -⟩ := ih.get (.defEq .lazy_delta_loop) (by lt_calls)
      ev87 rc a b (.field 16) types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d
      Γ (types_mono e0 htypes) A B (Tm.mono e0 hA) (Tm.mono e0 hB) _ _ _ rfl
    have x1 := e0.trans (ObsFn.heap_extends ev87)
    exact ih.get (.defEq .slow2_after_delta) (by lt_calls) ev182 rc oa ob x_fa x_fb types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono x1 hrc) d Γ (types_mono x1 htypes) A0 B0 FA
      FB (Tm.mono x1 hA0) (Tm.mono x1 hB0) hFA hFB (.trans hra0 hraF) (.trans hrb0 hrbF) hr

/-- `KernelDefEq::slow2_after_delta`: the bounded structural tier and the structure tree on the
lazy-δ reducts, then the eager fallback on the originals. -/
theorem slow2_after_delta_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::slow2_after_delta" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.slow2_after_delta c args h r h' calls := by
  intro rc oa ob a b types hargs good hrc d Γ htypes A0 B0 A B hA0 hB0 hA hB hra0 hrb0 hr
  subst hargs
  rcases Obs.«KernelDefEq::slow2_after_delta».obs ev with
    ⟨m2, cs13, w62, ev15, he74, he75, hc76⟩ |
    ⟨v1, m2, cs13, m81, cs92, ev15, ev94, he131, he132, hc133⟩ |
    ⟨v1, m2, cs13, v80, m81, cs92, cs141, ev15, ev94, hne134, ev143, hc176⟩
  · subst hc76
    exact .redBoth hra0 hrb0 (ih.get (.defEq .k_is_def_eq_struct_bounded) (by lt_calls) ev15 rc a
      b (.field 8) types rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB
      (.field 1) w62 rfl field_one_ne_zero)
  · subst hc133
    have e0 := ObsFn.heap_extends ev15
    exact .redBoth hra0 hrb0 (ih.get (.defEq .k_is_def_eq_structure_tree) (by lt_calls) ev94 rc a
      b types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ
      (types_mono e0 htypes) A B (Tm.mono e0 hA) (Tm.mono e0 hB) field_one_ne_zero)
  · subst hc176
    have e0 := (ObsFn.heap_extends ev15).trans (ObsFn.heap_extends ev94)
    exact ih.get (.defEq .slow2_eager_fallback) (by lt_calls) ev143 rc oa ob types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) A0 B0
      (Tm.mono e0 hA0) (Tm.mono e0 hB0) hr

/-- `KernelDefEq::slow2_eager_fallback`: both sides head-normalized (`whnf`), the rescue tier,
η both ways, then the structural comparison. -/
theorem slow2_eager_fallback_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::slow2_eager_fallback" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.slow2_eager_fallback c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  rcases Obs.«KernelDefEq::slow2_eager_fallback».obs ev with
    ⟨v1, m2, cs12, v39, m40, cs50, m78, cs89, x_eq, ev14, ev52, ev91, he143, he144, hc145⟩ |
    ⟨v1, m2, cs12, v39, m40, cs50, v77, m78, cs89, m150, cs161, ev14, ev52, ev91, ev163, he200,
      he201, hc202⟩ |
    ⟨v1, m2, cs12, v39, m40, cs50, v77, m78, cs89, v149, m150, cs161, cs210, ev14, ev52, ev91,
      ev163, hne203, ev212, hc245⟩
  all_goals
    first | subst hc145 | subst hc202 | subst hc245
    obtain ⟨Aw, hAw, hra⟩ := ih.get (.whnf .whnf) (by lt_calls) ev14 rc a types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A hA
    have e0 := ObsFn.heap_extends ev14
    obtain ⟨Bw, hBw, hrb⟩ := ih.get (.whnf .whnf) (by lt_calls) ev52 rc b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) B
      (Tm.mono e0 hB)
    have e1 := ObsFn.heap_extends ev52
    have x1 := e0.trans e1
  · subst he143
    exact .redBoth hra hrb (ih.get (.defEq .de_rescue_tier) (by lt_calls) ev91 rc v1 v39 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono x1 hrc) d Γ (types_mono x1 htypes) Aw Bw
      (Tm.mono e1 hAw) hBw r rfl hr)
  · have e2 := ObsFn.heap_extends ev91
    have x2 := x1.trans e2
    exact .redBoth hra hrb (ih.get (.defEq .try_eta_swap) (by lt_calls) ev163 rc v1 v39 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono x2 hrc) d Γ (types_mono x2 htypes) Aw Bw
      (Tm.mono (e1.trans e2) hAw) (Tm.mono e2 hBw) field_one_ne_zero)
  · have e2 := (ObsFn.heap_extends ev91).trans (ObsFn.heap_extends ev163)
    have x2 := x1.trans e2
    exact .redBoth hra hrb (ih.get (.defEq .k_is_def_eq_struct) (by lt_calls) ev212 rc v1 v39
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono x2 hrc) d Γ
      (types_mono x2 htypes) Aw Bw (Tm.mono (e1.trans e2) hAw) (Tm.mono e2 hBw) hr)

end IxVM.Refinement.Core
