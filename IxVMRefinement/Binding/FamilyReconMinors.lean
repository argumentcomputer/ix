import IxVMRefinement.Binding.FamilyReconFlat
import IxVMRefinement.Obs.KernelCheck10
import IxVMRefinement.Obs.KernelCheck11

/-! # The minor premises of the reconstructed recursor type on `TmOExact`

This module refines the minor-premise builders of `KernelCheck` against the store-free model
(`FamilyReconModel`), on `TmOExact`, `RepList` and `FlatEntryRepExact`:

* `list_lift_each_spec`: `KernelCheck::list_lift_each`;
* `build_ctor_app_params_spec`: `KernelCheck::build_ctor_app_params` (`ctorAppParams`);
* `build_ih_doms_spec`: `KernelCheck::build_ih_doms` (`ihDoms`);
* `build_minor_at_depth_spec`: `KernelCheck::build_minor_at_depth` (`minorAt`);
* `build_minor_doms_spec`: `KernelCheck::build_minor_doms` (`minorDoms`);
* `build_all_minors_walk_spec`, `build_all_minors_spec`: `KernelCheck::build_all_minors_walk`,
  `KernelCheck::build_all_minors` (`allMinors`).

The constructor reads of `build_minor_doms` (`Ingress::get_ci_cprj`,
`KernelCheck::projection_addr_ctor`) enter as the single-call predicates `CtorAnswers` and
`CtorAddrAnswers`. -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Binding.FamilyFlat (FlatEntry exprInstLevels)
open IxVM.Refinement.Core (W KExpr KLevel KKey kexprEnum kexprListEnum addrTy ixAddr Resolved)
open IxVM.Refinement.Decl (TmExact)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open IxVM (F)

set_option maxHeartbeats 2400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Lists of terms and of field-encoded naturals -/

section ListHelpers

private theorem kexpr_drop_nat {R : Heap F → KExpr → SourceValue F → Prop} {xs : List KExpr}
    {l r : SourceValue F} {n : Nat} (hn : n < 18446744069414584321) {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [l, .field (n : F)] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) :
    RepList kexprListEnum R h (xs.drop n) r ∧ h' = h := by
  have := Lib.Lists.drop_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) (R := R) _ rfl
    (by rw [Obs.Names.«Lists::drop<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)
  rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol, fval_natCast hn] at this
  exact this.2

private theorem list_length_gen {α : Type} {R : Heap F → α → SourceValue F → Prop}
    {xs : List α} {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [l] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) : r = .field (xs.length : F) ∧ h' = h :=
  Lib.Lists.length_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) (R := R)
    (by rw [Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)

private theorem list_concat_gen {α : Type} {R : Heap F → α → SourceValue F → Prop}
    (hR : HeapMono₂ R)
    {xs ys : List α} {a b r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::concat<&KernelTypes::KExprNode>» [a, b] h r h' cs)
    (ha : RepList kexprListEnum R h xs a) (hb : RepList kexprListEnum R h ys b) :
    RepList kexprListEnum R h' (xs ++ ys) r := by
  have := Lib.Lists.concat_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) hR
    (by rw [Obs.Names.«Lists::concat<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact ha)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hb)
  rwa [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at this

private theorem field_length {ns : List Nat} {l r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<Field>» [l] h r h' cs)
    (hl : RepList fieldListEnum RepNatField h ns l) : r = .field (ns.length : F) ∧ h' = h :=
  Lib.Lists.length_spec (t := .field) (R := RepNatField)
    (by rw [Obs.Names.«Lists::length<Field>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<Field>».symbol]; exact hl)

/-- `Lists::lookup_or_default(ns, i, 0)` on field-encoded naturals is `ns[i]?.getD 0`. -/
private theorem field_lookup_or_zero {ns : List Nat} {l r : SourceValue F} {i : Nat}
    (hi : i < 18446744069414584321) {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::lookup_or_default<Field>» [l, .field (i : F), .field 0] h r h'
      cs)
    (hl : RepList fieldListEnum RepNatField h ns l) :
    r = .field (((ns[i]?).getD 0 : Nat) : F) ∧ h' = h := by
  obtain ⟨hh, hcase⟩ := Lib.Lists.lookup_or_default_spec (t := .field) (R := RepNatField)
    (by rw [Obs.Names.«Lists::lookup_or_default<Field>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<Field>».symbol]; exact hl)
  rw [fval_natCast hi] at hcase
  refine ⟨?_, hh⟩
  rcases hcase with ⟨x, hx, hr⟩ | ⟨hlen, hr⟩
  · rw [hx]; exact hr
  · rw [List.getElem?_eq_none (by omega), hr]; simp

/-- The shape of a represented list: its spine alone. -/
theorem shape_of_rep {α : Type} {en : String} {R : Heap F → α → SourceValue F → Prop}
    {h : Heap F} {xs : List α} {p : SourceValue F} (rep : RepList en R h xs p) :
    RepList en (fun _ (_ : Unit) _ => True) h (List.replicate xs.length ()) p := by
  induction rep with
  | nil cell => exact .nil cell
  | cons cell _ _ ih => exact .cons cell trivial ih

theorem shape_heapMono₂ : HeapMono₂ (fun (_ : Heap F) (_ : Unit) (_ : SourceValue F) => True) :=
  fun _ _ _ _ _ _ => trivial

variable {κ : _root_.Address → KKey}

/-- **An `App` cell** applies a represented head to a represented argument. -/
theorem tmOExact_app_cell {h : Heap F} {A B : KExpr} {xa xb : SourceValue F}
    (hA : TmOExact κ h A xa) (hB : TmOExact κ h B xb) :
    TmOExact κ (h ++ [.construct kexprEnum "App" [xa, xb]]) (.app A B)
      (.ptr (.enum kexprEnum) h.length) := by
  have ext : Heap.Extends h (h ++ [.construct kexprEnum "App" [xa, xb]]) := Heap.Extends.snoc _ _
  obtain ⟨k₁, r₁⟩ := hA
  obtain ⟨k₂, r₂⟩ := hB
  exact ⟨max k₁ k₂, .app (by simp)
    (tmExact_depth_le (r₁.mono ext) _ (Nat.le_max_left _ _))
    (tmExact_depth_le (r₂.mono ext) _ (Nat.le_max_right _ _))⟩

/-- **`KernelCheck::list_lift_each(es, shift, 0)`** lifts every term by `shift` at the cutoff
`cut`. -/
theorem list_lift_each_spec {shift cut : Nat} (hs : shift < 4611686018427387904)
    (hcut : cut < 4294967296) :
    ∀ (Es : List KExpr) {xes r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelCheck::list_lift_each" [xes, .field (shift : F), .field (cut : F)] h r h'
        cs → IxVM.Consistency.Bounded cs → RepList kexprListEnum (TmOExact κ) h Es xes →
      RepList kexprListEnum (TmOExact κ) h' (Es.map fun e => e.liftLooseBVars shift cut) r := by
  intro Es
  induction Es with
  | nil =>
    intro xes r h h' cs ev hbnd hE
    match Obs.«KernelCheck::list_lift_each».obs ev with
    | .Nil (he24 := hr) (hm23 := hm) .. => subst hr hm; exact Lib.rep_store_nil h
    | .Cons (ld12 := ld) .. =>
      obtain ⟨z, zs, hzs, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hE ld
      cases hzs
  | cons E Es ih =>
    intro xes r h h' cs ev hbnd hE
    match Obs.«KernelCheck::list_lift_each».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hE ld
    | .Cons (x_e := xe) (x_rest := xrest) (v54 := v54) (v55 := v55) (m57 := m57) (cs65 := cs65)
        (m93 := m93) (cs101 := cs101) (ld12 := ld) (he50 := hr) (hm49 := hm) (ev67 := ev67)
        (ev103 := ev103) (hc128 := hc) =>
      subst hr hm
      obtain ⟨z, zs, hzs, hz, hzs'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hE ld
      injection hzs with hz1 hz2
      subst hz1 hz2
      have b1 : IxVM.Consistency.Bounded cs65 :=
        RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])
      have b2 : IxVM.Consistency.Bounded cs101 :=
        RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])
      have hd := expr_lift_tmOExact hs hcut b1 hz ev67
      have ext1 : Heap.Extends h m57 := ObsFn.heap_extends ev67
      have hrest := ih ev103 b2 (tmOExactList_mono ext1 hzs')
      have ext2 : Heap.Extends m57 m93 := ObsFn.heap_extends ev103
      exact Lib.rep_store_cons tmOExact_heapMono₂ (TmOExact.mono ext2 hd) hrest

/-- **`KernelCheck::build_ctor_app_params`** is `ctorAppParams`: the head applied to the
recursor's parameters, or at an auxiliary to the entry's parameters lifted. -/
theorem build_ctor_app_params_spec {nrp depthNow : Nat} {aux : Bool} {sp : List KExpr}
    (hd : depthNow < 4611686018427387904) (hpos : 1 ≤ depthNow) (hle : nrp ≤ depthNow)
    {xh xown xsp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {H : KExpr}
    (ev : ObsFn W "KernelCheck::build_ctor_app_params"
      [xh, xown, .field (nrp : F), .field (depthNow : F), auxVal aux, xsp] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hH : TmOExact κ h H xh)
    (hsp : RepList kexprListEnum (TmOExact κ) h sp xsp) :
    TmOExact κ h' (ctorAppParams H nrp depthNow aux sp) r := by
  match Obs.«KernelCheck::build_ctor_app_params».obs ev with
  | .n0 (cs18 := cs1) (hv14 := hv) (op52 := op) (ev20 := ev1) (hc60 := hc) .. =>
    obtain rfl : aux = false := auxVal_eq_zero.mp hv
    obtain rfl := binop_sub_one_nat hpos op
    exact build_apply_bvars_decreasing_spec (by omega) (by omega) (by omega) ev1 hH
  | .other (cs68 := cs1) (hne61 := hne) (op101 := op) (ev70 := ev1) (hc104 := hc) .. =>
    obtain rfl : aux = true := by
      cases haux : aux
      · exact (hne (auxVal_eq_zero.mpr haux)).elim
      · rfl
    obtain rfl := binop_sub_nat hle op
    exact apply_spec_params_lifted_spec (by omega) sp ev1
      (RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])) hH hsp

end ListHelpers

/-! ## `build_ih_doms` -/

section Minors

variable {κ : _root_.Address → KKey}

/-- **`KernelCheck::build_ih_doms`** is `ihDoms`: the minor premise's inductive-hypothesis
binders, one for each recursive field, from the fields' head-normalized telescopes. The motive
variables are below the minor's saved depth (`hmb`, `hrm`), every recursive field index is a
field (`hri`), and the counts fit. -/
theorem build_ih_doms_spec {rm : List Nat} {norm : List KExpr} {fop : List Nat}
    {motiveBase nFields minorSaved : Nat} {elim : KLevel}
    (hms : minorSaved < 1099511627776) (hnf : nFields < 1099511627776)
    (hmb : motiveBase < minorSaved) (hrm : ∀ m ∈ rm, motiveBase + m < minorSaved)
    (hfop : ∀ n ∈ fop, n < 4294967296) :
    ∀ (ri : List Nat) (k : Nat), k + ri.length < 1099511627776 → (∀ i ∈ ri, i < nFields) →
      ∀ {xri xrm xnorm xfop xelim r : SourceValue F} {h h' : Heap F} {cs root : List (Call F)},
      ObsFn W "KernelCheck::build_ih_doms"
        [xri, xrm, xnorm, xfop, .field (motiveBase : F), .field (nFields : F),
          .field (minorSaved : F), .field (k : F), xelim] h r h' cs →
      IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ root) →
      RepList fieldListEnum RepNatField h ri xri →
      RepList fieldListEnum RepNatField h rm xrm →
      RepList kexprListEnum (TmOExact κ) h norm xnorm →
      RepList fieldListEnum RepNatField h fop xfop →
      RepKLevel h elim xelim →
      Heap.Extends h h' ∧
        ∃ ih, ihDoms rm norm fop motiveBase nFields minorSaved elim k ri = some ih ∧
          RepList kexprListEnum (TmOExact κ) h' ih r := by
  intro ri
  induction ri with
  | nil =>
    intro k hk hri xri xrm xnorm xfop xelim r h h' cs root ev hbnd hroot rri rrm rnorm rfop rel
    match Obs.«KernelCheck::build_ih_doms».obs ev with
    | .Nil (he24 := hr) (hm23 := hm) .. =>
      subst hr hm
      exact ⟨Heap.Extends.snoc _ _, [], rfl, Lib.rep_store_nil h⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨z, zs, hzs, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load rri ld
      cases hzs
  | cons fieldIdx rest ih =>
    intro k hk hri xri xrm xnorm xfop xelim r h h' cs root ev hbnd hroot rri rrm rnorm rfop rel
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    match Obs.«KernelCheck::build_ih_doms».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load rri ld
    | .Cons (x_field_idx := xfi) (x_rest := xrest) (v46 := v46) (m47 := m47) (v83 := v83)
        (m84 := m84) (v120 := v120) (x128 := x128) (v147 := v147) (m148 := m148)
        (cs188 := cs188) (v177 := v177) (m178 := m178) (v192 := v192) (x207 := x207)
        (m233 := m233) (cs244 := cs244) (x_forall_doms := xfd) (x_inner_body := xib)
        (v271 := v271) (m272 := m272) (v293 := v293) (v311 := v311) (x319 := x319)
        (y320 := y320) (v346 := v346) (x354 := x354) (y355 := y355) (m382 := m382)
        (cs_tifcvrfj := cssp) (x_dom_args := xda) (v420 := v420) (m421 := m421) (m451 := m451)
        (v473 := v473) (m474 := m474) (m504 := m504) (v526 := v526) (m527 := m527)
        (m564 := m564) (v594 := v594) (m595 := m595) (v641 := v641) (m650 := m650)
        (cs658 := cs658) (v668 := v668) (ld12 := ld) (ev59 := ev59) (ev96 := ev96)
        (op143 := op143) (op135 := op135) (ev160 := ev160) (op222 := op222) (op214 := op214)
        (ev190 := ev190) (ev246 := ev246) (ev284 := ev284) (op308 := op308) (op334 := op334)
        (op343 := op343) (op326 := op326) (op369 := op369) (op378 := op378) (op361 := op361)
        (ev_pexuhviy := evsp) (ev433 := ev433) (hm461 := hm461) (ev486 := ev486)
        (hm514 := hm514) (ev539 := ev539) (hm574 := hm574) (ev607 := ev607) (he636 := hr)
        (hm635 := hm) (op732 := op732) (ev660 := ev660) (hc741 := hc) .. =>
      obtain ⟨z, zs, hzs, hz, rrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load rri ld
      injection hzs with hz1 hz2
      subst hz1 hz2
      obtain rfl : xfi = .field (fieldIdx : F) := hz
      have hfi : fieldIdx < nFields := hri fieldIdx (by simp)
      simp only [List.length_cons] at hk
      -- the entry and its parameter count
      obtain ⟨rfl, rfl⟩ := field_lookup_or_zero (by omega) ev59 rrm
      have hmem : motiveBase + (rm[k]?).getD 0 < minorSaved := by
        cases hg : rm[k]? with
        | none => simpa using hmb
        | some x => simpa using hrm x (List.mem_of_getElem? hg)
      obtain ⟨rfl, rfl⟩ := field_lookup_or_zero (by omega) ev96 rfop
      have htnp : (fop[(rm[k]?).getD 0]?).getD 0 < 4294967296 := by
        cases hg : fop[(rm[k]?).getD 0]? with
        | none => simp
        | some x => simpa using hfop x (List.mem_of_getElem? hg)
      obtain rfl := binop_add_nat op143
      obtain rfl := binop_add_nat op135
      -- the field's telescope, lifted over the later fields and the earlier hypotheses
      obtain ⟨⟨dom, hdom, rdom⟩, rfl⟩ := kexpr_lookup ev160 rnorm
      rw [fval_natCast (by omega)] at hdom
      obtain rfl := binop_sub_nat (Nat.le_of_lt hfi) op222
      obtain rfl := binop_add_nat op214
      have ev190' : ObsFn W "KernelSubst::expr_lift"
          [v147, .field ((nFields - fieldIdx + k : Nat) : F), .field ((0 : Nat) : F)] m148 v177 m178
          cs188 := by simpa using ev190
      have rlift := expr_lift_tmOExact (by omega) (by decide)
        (sub fun c hc' => by rw [hc]; simp [hc']) rdom ev190'
      have e1 : Heap.Extends m148 m178 := ObsFn.heap_extends ev190
      obtain ⟨xl, xb, he, e2, rfd, rinner⟩ := peel_leading_foralls_spec ev246
        (sub fun c hc' => by rw [hc]; simp [hc']) rlift
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he
      obtain ⟨rfl, rfl⟩ := he
      have hnxs : (peelAll (dom.liftLooseBVars (nFields - fieldIdx + k) 0)).1.length < 2 ^ 39 :=
        RomBound.bounded_length_lt hbnd
          (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [xfd], m233⟩)
          (by rw [hc]; simp) (by simp) rfd
      obtain ⟨rfl, rfl⟩ := kexpr_length ev284 rfd
      obtain rfl := binop_add_nat op308
      obtain rfl := binop_sub_one_nat (by omega) op334
      obtain rfl := binop_add_nat op343
      obtain rfl := binop_sub_nat (by omega) op326
      obtain rfl := binop_sub_one_nat (by omega) op369
      obtain rfl := binop_add_nat op378
      obtain rfl := binop_sub_nat (by omega) op361
      -- the motive applied to the indices
      obtain ⟨-, -, rargs⟩ := collect_spine_zeta_spec rinner
        (sub fun c hc' => by rw [hc]; simp [hc']) evsp
      have e3 : Heap.Extends m272 m382 := ObsFn.heap_extends evsp
      obtain ⟨rdrop, rfl⟩ := kexpr_drop_nat (by omega) ev433 rargs
      subst hm461
      have e4 : Heap.Extends m421 (m421 ++ [.construct kexprEnum "BVar" [.field
          ((minorSaved + nFields + k +
            (peelAll (dom.liftLooseBVars (nFields - fieldIdx + k) 0)).1.length - 1 -
            (motiveBase + (rm[k]?).getD 0) : Nat) : F)]]) := Heap.Extends.snoc _ _
      have rwi := apply_spine_expr_spec _ ev486
        (tmOExact_bvar_cell (κ := κ) (h := m421) (by omega)) (tmOExactList_mono e4 rdrop)
      have e5 : Heap.Extends _ m474 := ObsFn.heap_extends ev486
      -- the field applied to its telescope's variables
      subst hm514
      have e6 : Heap.Extends m474 (m474 ++ [.construct kexprEnum "BVar" [.field
          ((minorSaved + nFields + k +
            (peelAll (dom.liftLooseBVars (nFields - fieldIdx + k) 0)).1.length - 1 -
            (minorSaved + fieldIdx) : Nat) : F)]]) := Heap.Extends.snoc _ _
      have rfa := build_apply_xs_spec (κ := κ) (by omega) ev539
        (tmOExact_bvar_cell (κ := κ) (h := m474) (by omega))
      have e7 : Heap.Extends _ m527 := ObsFn.heap_extends ev539
      subst hm574
      have rapp := tmOExact_app_cell ((rwi.mono e6).mono e7) rfa
      have e8 : Heap.Extends m527 (m527 ++ [.construct kexprEnum "App" [v473, v526]]) :=
        Heap.Extends.snoc _ _
      have e28 : Heap.Extends m272 (m527 ++ [.construct kexprEnum "App" [v473, v526]]) :=
        e3.trans (e4.trans (e5.trans (e6.trans (e7.trans e8))))
      have rihd := wrap_foralls_spec _ ev607 rapp (tmOExactList_mono e28 rfd)
        ((rel.mono (e1.trans e2)).mono e28)
      have e9 : Heap.Extends _ m595 := ObsFn.heap_extends ev607
      have e09 : Heap.Extends m148 m595 := (e1.trans e2).trans (e28.trans e9)
      -- the remaining hypotheses
      obtain rfl := binop_add_one_nat op732
      obtain ⟨e10, ihr, hihr, rihr⟩ := ih (k + 1) (by omega)
        (fun i hi => hri i (by simp [hi])) ev660 (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc']))
        (fieldList_mono e09 rrest) (fieldList_mono e09 rrm) (tmOExactList_mono e09 rnorm)
        (fieldList_mono e09 rfop) (rel.mono e09)
      subst hr hm
      refine ⟨ObsFn.heap_extends ev, _, ?_,
        Lib.rep_store_cons tmOExact_heapMono₂ (rihd.mono e10) rihr⟩
      simp only [ihDoms, hdom, hihr, Option.map_some]

/-! ## `build_minor_at_depth` -/

/-- A recursive field's entry is an entry of the flattened family. -/
theorem isRecField_lt {V : ReconView} {es : List FlatEntry} {l : Nat} {e : KExpr} {m : Nat}
    (h : isRecField V es l e = some m) : m < es.length := by
  unfold isRecField at h
  split at h
  · split at h
    · unfold flatFindMatching at h
      exact (List.findIdx?_eq_some_iff_findIdx_eq.mp h).1
    · cases h
  · cases h

/-- What `fieldsClassify` returns: one domain and one head-normalized type for each leading
binder, recursive field indices below the field count, entries inside the family. -/
theorem fieldsClassify_facts {V : ReconView} {f : Nat} {es : List FlatEntry} {liftBy : Nat} :
    ∀ (E : KExpr) (fidx : Nat) {ds ns : List KExpr} {ri rm : List Nat} {ret : KExpr},
      fieldsClassify V f es liftBy fidx E = some (ds, ri, rm, ret, ns) →
      ds.length = (peelAll E).1.length ∧ ns.length = ds.length ∧
        (∀ i ∈ ri, i < fidx + ds.length) ∧ (∀ m ∈ rm, m < es.length) := by
  intro E
  induction E with
  | forallE d b m ihd ihb =>
    intro fidx ds ns ri rm ret h
    simp only [fieldsClassify] at h
    cases hw : whnfTele V f f d with
    | none => rw [hw] at h; cases h
    | some nd =>
      rw [hw] at h
      simp only at h
      cases hr : fieldsClassify V f es liftBy (fidx + 1) b with
      | none => rw [hr] at h; cases h
      | some t =>
        obtain ⟨ds', ri', rm', ret', ns'⟩ := t
        rw [hr] at h
        simp only at h
        obtain ⟨h1, h2, h3, h4⟩ := ihb (fidx + 1) hr
        cases hf : isRecField V es (liftBy + fidx) nd with
        | none =>
          rw [hf] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
          refine ⟨by simp [peelAll, h1], by simp [h2], fun i hi => ?_, h4⟩
          have := h3 i hi
          simp only [List.length_cons]
          omega
        | some mm =>
          rw [hf] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
          refine ⟨by simp [peelAll, h1], by simp [h2], fun i hi => ?_, fun x hx => ?_⟩
          · simp only [List.length_cons]
            rcases List.mem_cons.mp hi with rfl | hi
            · omega
            · have := h3 i hi
              omega
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact isRecField_lt hf
            · exact h4 x hx
  | _ =>
    intro fidx ds ns ri rm ret h
    simp only [fieldsClassify, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    simp [peelAll]

/-- **`KernelCheck::build_minor_at_depth`** is `minorAt`: the minor premise of one constructor,
at the minors before it, on `TmOExact`. The constructor's parameters that are not instantiated
by the entry's are among the recursor's (`hown`), its field telescope has fewer than `2^32`
binders (`hfields`), the motive variables are among the recursor's motives (`hself`, `hmot`),
and the counts fit. -/
theorem build_minor_at_depth_spec (hinj : Function.Injective κ) {V : ReconView}
    {root : List (Call F)}
    (hA : AddrOf κ V) (hD : DefnAnswers root κ V) (hI : IndAnswers root κ V)
    (hC : CtorOfAnswers root V) (hM : ModeledAnswers root V)
    {es : List FlatEntry} {fop : List Nat} {cty : KExpr} {nOwn : Nat} {aux : Bool}
    {sp : List KExpr} {us : List KLevel} {nrp nMot prev motiveBase selfMemIdx : Nat}
    {elim : KLevel} {ca : Bytes.Address} (hres : Resolved (κ (ixAddr ca)))
    (hsize : nrp + nMot + prev < 1099511627776)
    (hself : motiveBase + selfMemIdx < nrp + nMot)
    (hmot : motiveBase + es.length ≤ nrp + nMot)
    (hfop : ∀ n ∈ fop, n < 4294967296)
    (hnOwn : nOwn < 72057594037927936)
    (hown : ∀ i, i < nOwn → ¬ (aux = true ∧ i < sp.length) → i < nrp)
    (hfields : ∀ f after, peelCtorParams V f nrp 0 aux sp nOwn 0 (exprInstLevels us cty) =
      some after → (peelAll after).1.length < 4294967296)
    {xrc xca xcty xsp xus xflat xfop xelim r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::build_minor_at_depth"
      [xrc, xca, xcty, .field (nOwn : F), auxVal aux, xsp, xus, xflat, xfop, .field (nrp : F),
        .field (nMot : F), .field (prev : F), .field (motiveBase : F), .field (selfMemIdx : F),
        xelim] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (rca : Bytes.RepAddressRef addrTy h ca xca) (rcty : TmOExact κ h cty xcty)
    (rsp : RepList kexprListEnum (TmOExact κ) h sp xsp) (rus : RepKLevelList h us xus)
    (res : RepList flatListEnum (FlatEntryRepExact κ) h es xflat)
    (rfop : RepList fieldListEnum RepNatField h fop xfop) (rel : RepKLevel h elim xelim) :
    Heap.Extends h h' ∧ ∃ M, TmOExact κ h' M r ∧
      Eventually fun f => minorAt V f es fop (κ (ixAddr ca)) cty nOwn aux sp us nrp nMot prev
        motiveBase selfMemIdx elim = some M := by
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono hbnd hs
  match Obs.«KernelCheck::build_minor_at_depth».obs ev with
  | .run (v1 := v1) (m2 := m2) (cs12 := cs12) (v31 := v31) (x39 := x39) (v58 := v58)
      (v76 := v76) (m77 := m77) (cs87 := cs87) (v114 := v114) (m115 := m115) (cs125 := cs125)
      (m199 := m199) (cs210 := cs210) (m245 := m245) (m258 := m258) (m271 := m271)
      (m284 := m284) (x_pf_doms := xpd) (x_rec_indices := xri) (x_rec_member_idxs := xrm)
      (x_pf_ret := xpr) (x_pf_norm := xpn) (v346 := v346) (m347 := m347) (v368 := v368)
      (m369 := m369) (cs379 := cs379) (v405 := v405) (m406 := m406) (cs416 := cs416)
      (v442 := v442) (m443 := m443) (cs453 := cs453) (v480 := v480) (m481 := m481)
      (v502 := v502) (v520 := v520) (m539 := m539) (cs_craqfzwq := cssp) (x_ret_args := xra)
      (v577 := v577) (m578 := m578) (v607 := v607) (m608 := m608) (cs618 := cs618)
      (v644 := v644) (x652 := x652) (y653 := y653) (m680 := m680) (v702 := v702)
      (m703 := m703) (m733 := m733) (v763 := v763) (m764 := m764) (cs774 := cs774)
      (v825 := v825) (m826 := m826) (m871 := m871) (v901 := v901) (m902 := m902)
      (cs912 := cs912) (v986 := v986) (m987 := m987) (ev14 := ev14) (op54 := op54)
      (op46 := op46) (op73 := op73) (ev89 := ev89) (ev127 := ev127) (hm253 := hm253)
      (hm266 := hm266) (hm279 := hm279) (hm292 := hm292) (ev212 := ev212) (ev359 := ev359)
      (ev381 := ev381) (ev418 := ev418) (ev455 := ev455) (ev493 := ev493) (op517 := op517)
      (op535 := op535) (ev_vhmrnmut := evsp) (ev590 := ev590) (ev620 := ev620)
      (op667 := op667) (op676 := op676) (op659 := op659) (hm690 := hm690) (ev715 := ev715)
      (hm743 := hm743) (ev776 := ev776) (ev838 := ev838) (hm881 := hm881) (ev914 := ev914)
      (ev999 := ev999) (ev1029 := ev1029) (hc1054 := hc) .. =>
    -- the constructor's type at the entry's levels, past its parameters
    have rI := expr_inst_levels_tmOExact (sub fun c hc' => by rw [hc]; simp [hc']) rcty rus ev14
    have e1 := ObsFn.heap_extends ev14
    obtain rfl := binop_add_nat op54
    obtain rfl := binop_add_nat op46
    obtain rfl := binop_add_nat op73
    have e2 := ObsFn.heap_extends ev89
    have e02 := e1.trans e2
    have rsp2 := tmOExactList_mono e02 rsp
    have hspl : sp.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbnd
        (c := ⟨"KernelCheck::peel_ctor_params_subst", [xrc, v1, .field (nOwn : F),
          .field (nrp : F), .field 0, auxVal aux, xsp, .field 0, v76], m77⟩)
        (by rw [hc]; simp) (by simp) rsp2
    have ev127' : ObsFn W "KernelCheck::peel_ctor_params_subst"
        [xrc, v1, .field (nOwn : F), .field (nrp : F), .field ((0 : Nat) : F), auxVal aux, xsp,
          .field ((0 : Nat) : F), v76] m77 v114 m115 cs125 := by simpa using ev127
    obtain ⟨e3, after, rafter, hpeel⟩ := peel_ctor_params_subst_spec hA hD hI hC hM
      (depth := nrp) (lift := 0) (by omega) (by decide) (by omega) nOwn 0 (by omega)
      (fun i _ hi hni => hown i (by omega) hni) ev127'
      (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) (rI.mono e2) rsp2
    have hflen : (peelAll after).1.length < 4294967296 := by
      obtain ⟨a, ha⟩ := hpeel
      exact hfields a after (ha a le_rfl)
    -- its fields, classified
    have x1 : Heap.Extends m115 m245 := by rw [hm253]; exact Heap.Extends.snoc _ _
    have x2 : Heap.Extends m245 m258 := by rw [hm266]; exact Heap.Extends.snoc _ _
    have x3 : Heap.Extends m258 m271 := by rw [hm279]; exact Heap.Extends.snoc _ _
    have x4 : Heap.Extends m271 m284 := by rw [hm292]; exact Heap.Extends.snoc _ _
    have rd0 : RepList kexprListEnum (TmOExact κ) m245 []
        (.ptr (.enum kexprListEnum) m115.length) := by rw [hm253]; exact Lib.rep_store_nil m115
    have rr0 : RepList fieldListEnum RepNatField m258 []
        (.ptr (.enum fieldListEnum) m245.length) := by rw [hm266]; exact Lib.rep_store_nil m245
    have rm0 : RepList fieldListEnum RepNatField m271 []
        (.ptr (.enum fieldListEnum) m258.length) := by rw [hm279]; exact Lib.rep_store_nil m258
    have rn0 : RepList kexprListEnum (TmOExact κ) m284 []
        (.ptr (.enum kexprListEnum) m271.length) := by rw [hm292]; exact Lib.rep_store_nil m271
    have e4 : Heap.Extends m115 m284 := x1.trans (x2.trans (x3.trans x4))
    have e04 : Heap.Extends h m284 := e02.trans (e3.trans e4)
    obtain ⟨e5, xds, xri1, xrm1, xret, xns, ds, ns, ri, rm, ret, he, rds, rri, rrm, rret, rns,
        hfc⟩ :=
      walk_fields_classify_nil_spec hinj hA hD hI hC hM (liftBy := 0) (by omega)
        (by simpa using ev212) (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) (rafter.mono e4)
        (flatList_mono e04 res) (tmOExactList_mono (x2.trans (x3.trans x4)) rd0)
        (fieldList_mono (x3.trans x4) rr0) (fieldList_mono x4 rm0) rn0
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
    obtain ⟨afc, hafc⟩ := hfc
    obtain ⟨hdl, hnl, hril, hrml⟩ := fieldsClassify_facts _ 0 (hafc afc le_rfl)
    have hds : ds.length < 4294967296 := by omega
    obtain ⟨rfl, rfl⟩ := kexpr_length ev359 rds
    -- the field binders, the normalized telescopes and the return type over the motives and
    -- the earlier minors
    have e6 := ObsFn.heap_extends ev381
    have rfd : RepList kexprListEnum (TmOExact κ) m369 (liftIndices ds (nMot + prev)) v368 :=
      list_lift_indices_spec (κ := κ) (shift := nMot + prev) (by omega) ds 0 (by omega)
        (by simpa using ev381) (sub fun c hc' => by rw [hc]; simp [hc']) rds
    have e7 := ObsFn.heap_extends ev418
    have rnd : RepList kexprListEnum (TmOExact κ) m406 (liftIndices ns (nMot + prev)) v405 :=
      list_lift_indices_spec (κ := κ) (shift := nMot + prev) (by omega) ns 0 (by omega)
        (by simpa using ev418) (sub fun c hc' => by rw [hc]; simp [hc'])
        (tmOExactList_mono e6 rns)
    have e8 := ObsFn.heap_extends ev455
    have rrt := expr_lift_tmOExact (shift := nMot + prev) (cut := ds.length) (by omega) hds
      (sub fun c hc' => by rw [hc]; simp [hc']) (rret.mono (e6.trans e7)) ev455
    have rri' := fieldList_mono (e6.trans (e7.trans e8)) rri
    have hril' : ri.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbnd (c := ⟨Obs.Names.«Lists::length<Field>», [xri], m443⟩)
        (by rw [hc]; simp) (by simp) rri'
    obtain ⟨rfl, rfl⟩ := field_length ev493 rri'
    obtain rfl := binop_add_nat op517
    obtain rfl := binop_add_nat op535
    -- the motive applied to the return type's indices
    obtain ⟨-, -, rargs⟩ := collect_spine_zeta_spec rrt
      (sub fun c hc' => by rw [hc]; simp [hc']) evsp
    have e9 := ObsFn.heap_extends evsp
    obtain ⟨rdrop, rfl⟩ := kexpr_drop_nat (by omega) ev590 rargs
    have rlifted := list_lift_each_spec (κ := κ) (shift := ri.length) (cut := 0) (by omega)
      (by decide) _ (by simpa using ev620) (sub fun c hc' => by rw [hc]; simp [hc']) rdrop
    have e10 := ObsFn.heap_extends ev620
    obtain rfl := binop_sub_one_nat (by omega) op667
    obtain rfl := binop_add_nat op676
    obtain rfl := binop_sub_nat (by omega) op659
    subst hm690
    have rwi := apply_spine_expr_spec _ ev715
      (tmOExact_bvar_cell (κ := κ) (h := m608) (by omega))
      (tmOExactList_mono (Heap.Extends.snoc _ _) rlifted)
    have e11 : Heap.Extends m608 m703 :=
      (Heap.Extends.snoc _ _).trans (ObsFn.heap_extends ev715)
    -- the constructor applied to its parameters and fields
    subst hm743
    have e12 : Heap.Extends m703 (m703 ++ [.construct kexprEnum "Const" [xca, xus]]) :=
      Heap.Extends.snoc _ _
    have eA : Heap.Extends h m703 :=
      e04.trans (e5.trans (e6.trans (e7.trans (e8.trans (e9.trans (e10.trans e11))))))
    have rhead : TmOExact κ (m703 ++ [.construct kexprEnum "Const" [xca, xus]])
        (.const (κ (ixAddr ca)) us) (.ptr (.enum kexprEnum) m703.length) :=
      haveI := hres
      ⟨0, .const (by simp) (Bytes.repAddressRef_heapMono₂ addrTy (eA.trans e12) rca)
        ((rus.mono eA).mono e12)⟩
    have rwp := build_ctor_app_params_spec (κ := κ) (nrp := nrp)
      (depthNow := nrp + nMot + prev + (ds.length + ri.length)) (aux := aux) (by omega)
      (by omega) (by omega) ev776 (sub fun c hc' => by rw [hc]; simp [hc']) rhead
      (tmOExactList_mono (eA.trans e12) rsp)
    have e13 := ObsFn.heap_extends ev776
    have rcapp := build_apply_field_bvars_spec (κ := κ) (nf := ds.length)
      (nb := ds.length + ri.length) (by omega) (by omega) ev838 rwp
    have e14 := ObsFn.heap_extends ev838
    subst hm881
    have rconc := tmOExact_app_cell ((rwi.mono e12).mono (e13.trans e14)) rcapp
    have e15 : Heap.Extends m826 (m826 ++ [.construct kexprEnum "App" [v702, v825]]) :=
      Heap.Extends.snoc _ _
    have eB : Heap.Extends h (m826 ++ [.construct kexprEnum "App" [v702, v825]]) :=
      eA.trans (e12.trans (e13.trans (e14.trans e15)))
    have eN : Heap.Extends m406 (m826 ++ [.construct kexprEnum "App" [v702, v825]]) :=
      e8.trans (e9.trans (e10.trans (e11.trans (e12.trans (e13.trans (e14.trans e15))))))
    -- the inductive hypotheses, then the binders
    obtain ⟨e16, ih, hih, rih⟩ := build_ih_doms_spec (κ := κ) (rm := rm)
      (norm := liftIndices ns (nMot + prev)) (fop := fop) (motiveBase := motiveBase)
      (nFields := ds.length) (minorSaved := nrp + nMot + prev) (elim := elim) (by omega)
      (by omega) (by omega) (fun m hm => by have := hrml m hm; omega) hfop ri 0 (by omega)
      (fun i hi => by have := hril i hi; omega) (by simpa using ev914)
      (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      (fieldList_mono (e6.trans (e7.trans eN)) rri) (fieldList_mono (e6.trans (e7.trans eN)) rrm)
      (tmOExactList_mono eN rnd) (fieldList_mono eB rfop) (rel.mono eB)
    have rw1 := wrap_foralls_spec _ ev999 (rconc.mono e16) rih ((rel.mono eB).mono e16)
    have e17 := ObsFn.heap_extends ev999
    have rw2 := wrap_foralls_spec _ ev1029 rw1
      (tmOExactList_mono (e7.trans (eN.trans (e16.trans e17))) rfd)
      ((rel.mono eB).mono (e16.trans e17))
    refine ⟨ObsFn.heap_extends ev, _, rw2, ?_⟩
    refine (hpeel.and ⟨afc, hafc⟩).mono fun f hpf => ?_
    simp only [minorAt, hpf.1, hpf.2, hih]

/-! ## `build_minor_doms` -/

/-- **`Ingress::get_ci_cprj` matches `V.ctor`**, for a load that is one of the calls `calls` and
whose own calls are among them: the constructor it loads at a block, a member position and a
constructor position (both below `2^56`) is the view's, its type represented and its parameter
count below `2^56`. -/
def CtorAnswers (calls : List (Call F)) (κ : _root_.Address → KKey) (V : ReconView) : Prop :=
  ∀ {xblk p ci : SourceValue F} {h m : Heap F} {cs : List (Call F)} {ba : Bytes.Address}
    {i c : Nat}, i < 72057594037927936 → c < 72057594037927936 →
    Bytes.RepAddressRef addrTy h ba xblk →
    ObsFn W "Ingress::get_ci_cprj" [xblk, .field (i : F), .field (c : F)] h p m cs →
    (⟨"Ingress::get_ci_cprj", [xblk, .field (i : F), .field (c : F)], h⟩ : Call F) ∈ calls →
    (∀ c ∈ cs, c ∈ calls) →
    loadValue m p = .ok ci →
    ∀ xnl xty xb xind xcidx xnp xnf xuns,
      ci = .construct "KernelTypes::KConstantInfo" "Ctor"
        [xnl, xty, xb, xind, xcidx, xnp, xnf, xuns] →
      ∃ (cty : KExpr) (np : Nat), V.ctor (ixAddr ba) i c = some (cty, np) ∧
        np < 72057594037927936 ∧ TmOExact κ m cty xty ∧ xnp = .field (np : F)

/-- **`KernelCheck::projection_addr_ctor` matches `V.ctorAddr`**, for a call that is one of the
calls `calls` and whose own calls are among them: the address it computes, at positions below
`2^56`, is keyed as the view's constructor address, at a key that resolves. -/
def CtorAddrAnswers (calls : List (Call F)) (κ : _root_.Address → KKey) (V : ReconView) : Prop :=
  ∀ {xblk r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {ba : Bytes.Address}
    {i c : Nat}, i < 72057594037927936 → c < 72057594037927936 →
    Bytes.RepAddressRef addrTy h ba xblk →
    ObsFn W "KernelCheck::projection_addr_ctor" [.field (i : F), .field (c : F), xblk] h r h'
      cs →
    (⟨"KernelCheck::projection_addr_ctor", [.field (i : F), .field (c : F), xblk], h⟩ :
      Call F) ∈ calls →
    (∀ c ∈ cs, c ∈ calls) →
    ∃ ca : Bytes.Address, Bytes.RepAddressRef addrTy h' ca r ∧
      κ (ixAddr ca) = V.key (V.ctorAddr (ixAddr ba) i c) ∧ Resolved (κ (ixAddr ca))

/-- **A constructor fits the reconstruction at an entry**: its parameters the entry's do not
instantiate are among the recursor's, and past its parameters it has fewer than `2^32` fields. -/
def CtorFits (V : ReconView) (nrp : Nat) (aux : Bool) (sp : List KExpr) (us : List KLevel)
    (cty : KExpr) (np : Nat) : Prop :=
  (∀ i, i < np → ¬ (aux = true ∧ i < sp.length) → i < nrp) ∧
    ∀ f after, peelCtorParams V f nrp 0 aux sp np 0 (exprInstLevels us cty) = some after →
      (peelAll after).1.length < 4294967296

/-- **`KernelCheck::build_minor_doms`** returns one term for each remaining constructor: the
spine of its result alone, with no premise on what it reads. -/
theorem build_minor_doms_shape {nctors : Nat} (hnc : nctors < 72057594037927936) :
    ∀ (n cidx : Nat), nctors - cidx = n → cidx ≤ nctors →
      ∀ {x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 xprev xelim r : SourceValue F}
        {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelCheck::build_minor_doms"
        [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, .field (nctors : F), xprev,
          .field (cidx : F), xelim] h r h' cs →
      RepList kexprListEnum (fun _ (_ : Unit) _ => True) h' (List.replicate n ()) r := by
  intro n
  induction n with
  | zero =>
    intro cidx hn0 hle x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 xprev xelim r h h' cs ev
    match Obs.«KernelCheck::build_minor_doms».obs ev with
    | .n0 (he28 := hr) (hm27 := hm) .. => subst hr hm; exact Lib.rep_store_nil h
    | .other (op17 := op) (hne33 := hne) .. =>
      have := binop_sub_ne_nat op hne
      omega
  | succ n ih =>
    intro cidx hn1 hle x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 xprev xelim r h h' cs ev
    match Obs.«KernelCheck::build_minor_doms».obs ev with
    | .n0 (op17 := op) .. =>
      have := binop_sub_eq_zero_nat (by omega) (by omega) op
      omega
    | .other (v177 := v177) (v320 := v320) (m329 := m329) (v355 := v355) (he315 := hr)
        (hm314 := hm) (op483 := op) (ev339 := ev1) .. =>
      obtain rfl := binop_add_one_nat op
      have := ih (cidx + 1) (by omega) (by omega) ev1
      subst hr hm
      exact Lib.rep_store_cons shape_heapMono₂ trivial this

/-- **`KernelCheck::build_minor_doms`** is `minorDoms`: the minor premises of the constructors
from `cidx` on of the inductive at `blk`, position `idx`, after `prev` minors. -/
theorem build_minor_doms_spec (hinj : Function.Injective κ) {V : ReconView}
    {root : List (Call F)}
    (hA : AddrOf κ V) (hD : DefnAnswers root κ V) (hI : IndAnswers root κ V)
    (hC : CtorOfAnswers root V) (hM : ModeledAnswers root V) (hCt : CtorAnswers root κ V)
    (hCa : CtorAddrAnswers root κ V)
    {es : List FlatEntry} {fop : List Nat} {aux : Bool} {sp : List KExpr} {us : List KLevel}
    {nrp nMot motiveBase selfMemIdx : Nat} {elim : KLevel} {blk : Bytes.Address}
    {idx nctors : Nat} (hidx : idx < 72057594037927936) (hnc : nctors < 72057594037927936)
    (hself : motiveBase + selfMemIdx < nrp + nMot)
    (hmot : motiveBase + es.length ≤ nrp + nMot)
    (hfop : ∀ n ∈ fop, n < 4294967296)
    (hfit : ∀ c cty np, V.ctor (ixAddr blk) idx c = some (cty, np) →
      CtorFits V nrp aux sp us cty np) :
    ∀ (n cidx prev : Nat), nctors - cidx = n → cidx ≤ nctors →
      nrp + nMot + prev + n < 1099511627776 →
      ∀ {xrc xma xsp xus xflat xfop xblk xelim r : SourceValue F} {h h' : Heap F}
        {cs : List (Call F)},
      ObsFn W "KernelCheck::build_minor_doms"
        [xrc, xma, auxVal aux, xsp, xus, xflat, xfop, .field (nrp : F), .field (nMot : F),
          .field (motiveBase : F), .field (selfMemIdx : F), xblk, .field (idx : F),
          .field (nctors : F), .field (prev : F), .field (cidx : F), xelim] h r h' cs →
      IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ root) →
      RepList kexprListEnum (TmOExact κ) h sp xsp → RepKLevelList h us xus →
      RepList flatListEnum (FlatEntryRepExact κ) h es xflat →
      RepList fieldListEnum RepNatField h fop xfop →
      Bytes.RepAddressRef addrTy h blk xblk → RepKLevel h elim xelim →
      Heap.Extends h h' ∧ ∃ ms, RepList kexprListEnum (TmOExact κ) h' ms r ∧ ms.length = n ∧
        Eventually fun f => minorDoms V f es fop aux sp us nrp nMot motiveBase selfMemIdx
          (ixAddr blk) idx elim prev (List.range' cidx n) = some ms := by
  intro n
  induction n with
  | zero =>
    intro cidx prev hn0 hle hsize xrc xma xsp xus xflat xfop xblk xelim r h h' cs ev hbnd
      hroot rsp rus res rfop rblk rel
    match Obs.«KernelCheck::build_minor_doms».obs ev with
    | .n0 (he28 := hr) (hm27 := hm) .. =>
      subst hr hm
      exact ⟨Heap.Extends.snoc _ _, [], Lib.rep_store_nil h, rfl, Eventually.always fun _ => rfl⟩
    | .other (op17 := op) (hne33 := hne) .. =>
      have := binop_sub_ne_nat op hne
      omega
  | succ n ih =>
    intro cidx prev hn1 hle hsize xrc xma xsp xus xflat xfop xblk xelim r h h' cs ev hbnd
      hroot rsp rus res rfop rblk rel
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    match Obs.«KernelCheck::build_minor_doms».obs ev with
    | .n0 (op17 := op) .. =>
      have := binop_sub_eq_zero_nat (by omega) (by omega) op
      omega
    | .other (m38 := m38) (p45 := p45) (x_ctor_ty := xcty) (x_np := xnp) (v139 := v139)
        (m140 := m140) (cs188 := cs188) (v177 := v177) (m178 := m178) (v320 := v320)
        (m329 := m329) (cs337 := cs337) (v354 := v354) (v355 := v355) (ev53 := ev53)
        (ld47 := ld47) (ev152 := ev152) (ev190 := ev190) (he315 := hr) (hm314 := hm)
        (op468 := op468) (op483 := op483) (ev339 := ev339) (hc492 := hc) .. =>
      -- the constructor and its address
      obtain ⟨cty, np, hctor, hnp, rcty, rfl⟩ :=
        hCt hidx (by omega) rblk ev53 (hroot _ (by rw [hc]; simp))
          (fun c hc' => hroot c (by rw [hc]; simp [hc'])) ld47 _ _ _ _ _ _ _ _ rfl
      have e1 := ObsFn.heap_extends ev53
      obtain ⟨ca, rca, hkey, hres⟩ :=
        hCa hidx (by omega) (Bytes.repAddressRef_heapMono₂ addrTy e1 rblk) ev152
          (hroot _ (by rw [hc]; simp)) (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      have e2 := ObsFn.heap_extends ev152
      have e02 := e1.trans e2
      obtain ⟨hown, hfields⟩ := hfit cidx cty np hctor
      -- its minor premise
      obtain ⟨e3, Mn, rMn, hMn⟩ := build_minor_at_depth_spec hinj hA hD hI hC hM hres
        (by omega) hself hmot hfop hnp hown hfields ev190
        (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) rca (rcty.mono e2)
        (tmOExactList_mono e02 rsp) (rus.mono e02) (flatList_mono e02 res)
        (fieldList_mono e02 rfop) (rel.mono e02)
      -- the remaining constructors
      obtain rfl := binop_add_one_nat op468
      obtain rfl := binop_add_one_nat op483
      have e03 := e02.trans e3
      obtain ⟨e4, ms, rms, hlen, hrec⟩ := ih (cidx + 1) (prev + 1) (by omega) (by omega)
        (by omega) ev339 (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) (tmOExactList_mono e03 rsp)
        (rus.mono e03) (flatList_mono e03 res) (fieldList_mono e03 rfop)
        (Bytes.repAddressRef_heapMono₂ addrTy e03 rblk) (rel.mono e03)
      subst hr hm
      refine ⟨ObsFn.heap_extends ev, Mn :: ms,
        Lib.rep_store_cons tmOExact_heapMono₂ (rMn.mono e4) rms, by simp [hlen], ?_⟩
      refine (hMn.and hrec).mono fun f hf => ?_
      simp only [List.range'_succ, minorDoms, hctor, ← hkey, hf.1, hf.2, Option.map_some]

/-! ## `build_all_minors` -/

/-- Every entry `flatOwnParams` counts is an inductive type of the view. -/
theorem flatOwnParams_ind {V : ReconView} :
    ∀ {es : List FlatEntry} {fop : List Nat}, flatOwnParams V es = some fop →
      ∀ e ∈ es, ∃ d, V.ind e.addr = some (some d) := by
  intro es
  induction es with
  | nil => intro fop _ e he; cases he
  | cons e0 es ih =>
    intro fop h e he
    simp only [flatOwnParams] at h
    cases h0 : V.ind e0.addr with
    | none => rw [h0] at h; cases h
    | some o =>
      cases o with
      | none => rw [h0] at h; cases h
      | some d =>
        cases h1 : flatOwnParams V es with
        | none => rw [h0, h1] at h; cases h
        | some ns =>
          rcases List.mem_cons.mp he with rfl | he
          · exact ⟨d, h0⟩
          · exact ih h1 e he

/-- **`KernelCheck::build_all_minors_walk`** is `allMinors`: the minor premises of the entries
`es` of the flattened family `fullEs`, from position `pos`, after `prev` minors. Every entry is
an inductive type of the view (`hind`; the circuit skips any other constant, where the model
has no value), every constructor fits (`hfit`), and the spine of the result fits (`hres`). -/
theorem build_all_minors_walk_spec (hinj : Function.Injective κ) {V : ReconView}
    {root : List (Call F)}
    (hA : AddrOf κ V) (hD : DefnAnswers root κ V) (hI : IndAnswers root κ V)
    (hC : CtorOfAnswers root V) (hM : ModeledAnswers root V) (hCt : CtorAnswers root κ V)
    (hCa : CtorAddrAnswers root κ V)
    {fullEs : List FlatEntry} {fop : List Nat} {nrp nMot motiveBase : Nat} {elim : KLevel}
    (hmot : motiveBase + fullEs.length ≤ nrp + nMot)
    (hfop : ∀ n ∈ fop, n < 4294967296) :
    ∀ (es : List FlatEntry) (prev pos : Nat)
      {xrc xflat xfull xfop xelim r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelCheck::build_all_minors_walk"
        [xrc, xflat, xfull, xfop, .field (nrp : F), .field (nMot : F), .field (motiveBase : F),
          .field (prev : F), .field (pos : F), xelim] h r h' cs →
      IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ root) →
      RepList flatListEnum (FlatEntryRepExact κ) h es xflat →
      RepList flatListEnum (FlatEntryRepExact κ) h fullEs xfull →
      RepList fieldListEnum RepNatField h fop xfop → RepKLevel h elim xelim →
      (∀ e ∈ es, ∃ d, V.ind e.addr = some (some d)) →
      (∀ e ∈ es, ∀ d, V.ind e.addr = some (some d) → ∀ c cty np,
        V.ctor d.blk d.idx c = some (cty, np) → CtorFits V nrp e.aux e.params e.levels cty np) →
      motiveBase + pos + es.length ≤ nrp + nMot →
      (∀ ms : List Unit, RepList kexprListEnum (fun _ _ _ => True) h' ms r →
        nrp + nMot + prev + ms.length < 1099511627776) →
      Heap.Extends h h' ∧ ∃ ms, RepList kexprListEnum (TmOExact κ) h' ms r ∧
        Eventually fun f => allMinors V f fullEs fop nrp nMot motiveBase elim es prev pos =
          some ms := by
  intro es
  induction es with
  | nil =>
    intro prev pos xrc xflat xfull xfop xelim r h h' cs ev hbnd hroot res rfull rfop rel
      hind hfit hpos hres
    match Obs.«KernelCheck::build_all_minors_walk».obs ev with
    | .Nil (he24 := hr) (hm23 := hm) .. =>
      subst hr hm
      exact ⟨Heap.Extends.snoc _ _, [], Lib.rep_store_nil h, Eventually.always fun _ => rfl⟩
    | .Cons_Induct (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load res ld
      cases hcons
  | cons e rest ih =>
    intro prev pos xrc xflat xfull xfop xelim r h h' cs ev hbnd hroot res rfull rfop rel
      hind hfit hpos hres
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    simp only [List.length_cons] at hpos
    match Obs.«KernelCheck::build_all_minors_walk».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load res ld
    | .Cons_Induct (x_rest := xrest) (x_member_addr := xma) (x_is_aux := xaux)
        (x_spec_params := xsp) (x_occ_us := xus) (m83 := m83) (p90 := p90)
        (x_num_ctors := xnc) (x_mem_block_addr := xblk) (x_mem_ind_idx := xidx) (v168 := v168)
        (m169 := m169) (cs179 := cs179) (v317 := v317) (m318 := m318) (v339 := v339)
        (m340 := m340) (cs350 := cs350) (v360 := v360) (v361 := v361) (ld12 := ld)
        (ev98 := ev98) (ld92 := ld92) (ev181 := ev181) (ev330 := ev330) (op425 := op425)
        (op441 := op441) (ev352 := ev352) (ev455 := ev455) (hc472 := hc) .. =>
      obtain ⟨e', rest', h1, he, rrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load res ld
      injection h1 with he1 hes1
      subst he1 hes1
      obtain ⟨xm', xsp', xou', ae, htup, rae, hae, rsp, rou⟩ := he
      injection htup with hl
      injection hl with h1 hl
      injection hl with h2 hl
      injection hl with h3 hl
      injection hl with h4
      subst h1 h2 h3 h4
      -- the entry's inductive type
      obtain ⟨d, ba, hd, -, -, -, hnc, hidx, -, -, -, -, rfl, hblk, rblk, rfl⟩ :=
        (hI rae ev98 (hroot _ (by rw [hc]; simp))
          (fun c hc' => hroot c (by rw [hc]; simp [hc'])) ld92).1 _ _ _ _ _ _ _ _ rfl
      rw [hae] at hd
      have e1 := ObsFn.heap_extends ev98
      have ev181' : ObsFn W "KernelCheck::build_minor_doms"
          [xrc, xma, auxVal e.aux, xsp, xus, xfull, xfop, .field (nrp : F),
            .field (nMot : F), .field (motiveBase : F), .field (pos : F), xblk,
            .field (d.idx : F), .field (d.nctors : F), .field (prev : F),
            .field ((0 : Nat) : F), xelim] m83 v168 m169 cs179 := by simpa using ev181
      -- the spine of its minors, then the remaining entries
      have rshape := build_minor_doms_shape hnc d.nctors 0 (Nat.sub_zero _) (Nat.zero_le _)
        ev181'
      have e2 := ObsFn.heap_extends ev181
      have e12 := e1.trans e2
      obtain ⟨hv317, rfl⟩ := list_length_gen ev330 rshape
      simp only [List.length_replicate] at hv317
      subst hv317
      obtain rfl := binop_add_nat op425
      obtain rfl := binop_add_one_nat op441
      have e3 := ObsFn.heap_extends ev352
      have rshape3 := repList_heapMono₂ kexprListEnum shape_heapMono₂ e3 rshape
      obtain ⟨-, msr, rmsr, hrec⟩ := ih (prev + d.nctors) (pos + 1) ev352
        (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) (flatList_mono e12 rrest)
        (flatList_mono e12 rfull) (fieldList_mono e12 rfop) (rel.mono e12)
        (fun x hx => hind x (by simp [hx])) (fun x hx => hfit x (by simp [hx])) (by omega)
        (fun ms' hms' => by
          have := hres _ (list_concat_gen shape_heapMono₂ ev455 rshape3 hms')
          simp only [List.length_append, List.length_replicate] at this
          omega)
      have hb := hres _ (list_concat_gen shape_heapMono₂ ev455 rshape3 (shape_of_rep rmsr))
      simp only [List.length_append, List.length_replicate] at hb
      -- its minors
      obtain ⟨-, ms, rms, hlen, hmd⟩ := build_minor_doms_spec hinj hA hD hI hC hM hCt hCa
        (blk := ba) hidx hnc (by omega : motiveBase + pos < nrp + nMot) hmot hfop
        (fun c cty np hc' => hfit e (by simp) d hd c cty np (by rw [← hblk]; exact hc'))
        d.nctors 0 prev (Nat.sub_zero _) (Nat.zero_le _) (by omega) ev181'
        (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) (tmOExactList_mono e1 rsp)
        (rou.mono e1) (flatList_mono e1 rfull) (fieldList_mono e1 rfop) rblk (rel.mono e1)
      have rall := list_concat_gen tmOExact_heapMono₂ ev455 (tmOExactList_mono e3 rms) rmsr
      refine ⟨ObsFn.heap_extends ev, ms ++ msr, rall, (hmd.and hrec).mono fun f hf => ?_⟩
      have hf1 := hf.1
      rw [hblk] at hf1
      simp only [allMinors, hd, List.range_eq_range', hf1, hlen, hf.2, Option.map_some]
    | .Cons_other (x_member_addr := xma) (x_is_aux := xaux) (x_spec_params := xsp)
        (x_occ_us := xus) (ld12 := ld) (ev98 := ev98) (ld92 := ld92) (hne473 := hne)
        (hc571 := hc) .. =>
      obtain ⟨e', rest', h1, he, rrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load res ld
      injection h1 with he1 hes1
      subst he1 hes1
      obtain ⟨xm', xsp', xou', ae, htup, rae, hae, rsp, rou⟩ := he
      injection htup with hl
      injection hl with h1 hl
      subst h1
      have hnone := (hI rae ev98 (hroot _ (by rw [hc]; simp))
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) ld92).2 hne
      obtain ⟨d, hd⟩ := hind e (by simp)
      rw [hae, hd] at hnone
      cases hnone

/-- **`KernelCheck::build_all_minors`** is `allMinors` from the first entry: on represented
inputs it returns the list of the minor premises of the reconstructed recursor type. Every
entry of the family is an inductive type of the view (`hind`), every constructor fits
(`hfit`), the motive variables are among the recursor's motives (`hmot`), and the spine of the
result, with the parameters and the motives, fits (`hres`). -/
theorem build_all_minors_spec (hinj : Function.Injective κ) {V : ReconView}
    {root : List (Call F)}
    (hA : AddrOf κ V) (hD : DefnAnswers root κ V) (hI : IndAnswers root κ V)
    (hC : CtorOfAnswers root V) (hM : ModeledAnswers root V) (hCt : CtorAnswers root κ V)
    (hCa : CtorAddrAnswers root κ V)
    {es : List FlatEntry} {fop : List Nat} {nrp nMot motiveBase : Nat} {elim : KLevel}
    (hmot : motiveBase + es.length ≤ nrp + nMot)
    (hfop : ∀ n ∈ fop, n < 4294967296)
    (hind : ∀ e ∈ es, ∃ d, V.ind e.addr = some (some d))
    (hfit : ∀ e ∈ es, ∀ d, V.ind e.addr = some (some d) → ∀ c cty np,
      V.ctor d.blk d.idx c = some (cty, np) → CtorFits V nrp e.aux e.params e.levels cty np)
    {xrc xflat xfop xelim r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::build_all_minors"
      [xrc, xflat, xfop, .field (nrp : F), .field (nMot : F), .field (motiveBase : F), xelim]
      h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (res : RepList flatListEnum (FlatEntryRepExact κ) h es xflat)
    (rfop : RepList fieldListEnum RepNatField h fop xfop) (rel : RepKLevel h elim xelim)
    (hres : ∀ ms : List Unit, RepList kexprListEnum (fun _ _ _ => True) h' ms r →
      nrp + nMot + ms.length < 1099511627776) :
    Heap.Extends h h' ∧ ∃ ms, RepList kexprListEnum (TmOExact κ) h' ms r ∧
      Eventually fun f => allMinors V f es fop nrp nMot motiveBase elim es 0 0 = some ms := by
  match Obs.«KernelCheck::build_all_minors».obs ev with
  | .run (cs4 := cs4) (ev6 := ev6) (hc85 := hc) =>
    have ev6' : ObsFn W "KernelCheck::build_all_minors_walk"
        [xrc, xflat, xflat, xfop, .field (nrp : F), .field (nMot : F), .field (motiveBase : F),
          .field ((0 : Nat) : F), .field ((0 : Nat) : F), xelim] h r h' cs4 := by simpa using ev6
    exact build_all_minors_walk_spec hinj hA hD hI hC hM hCt hCa hmot hfop es 0 0 ev6'
      (RomBound.bounded_mono hbnd fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) res res rfop rel hind hfit (by omega)
      (fun ms hms => by have := hres ms hms; omega)

end Minors

end IxVM.Refinement.Binding.FamilyRecon
