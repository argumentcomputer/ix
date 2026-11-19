import IxVMRefinement.Binding.FamilyReconFlat
import IxVMRefinement.Decl.Common

/-! # The reconstructed rules of a family record, and the stored rules against them

The rule side of a family check (`KernelCheck::canonical_rules_at_pos`): the circuit builds the
right-hand side of every rule of a recursor (`populate_rules`, constructor by constructor
`build_rule_rhs`, whose inductive hypotheses `apply_ihs_full` applies), at the minor premises the
entries before the recursor's leave it (`ctors_before_pos`), and compares each stored rule with
it under the λs of the recursor type (`compare_rules`, `rule_lam_doms`). Each function refines
its model in `FamilyReconModel` on `TmOExact`:

* `ctors_before_pos_spec` (`ctorsBefore`);
* `apply_ihs_full_spec` (`applyIhs`), `build_rule_rhs_spec` (`ruleBody`), `populate_rules_spec`
  (`ruleBodies`);
* `peel_n_foralls_tmOExact` (`peelForalls`), `rule_lam_doms_spec` (`LamsAlong`),
  `compare_rules_spec` (`RuleFollows` at every stored rule that has a reconstructed body, with the
  rule's constructor index its position and its field count the constructor's);
* `rules_at_pos_spec`: the three calls of `canonical_rules_at_pos` together give
  `ruleBodiesAt`, `ctorsBefore` and `RuleFollows` at every stored rule, as `MemberRecon` states
  them.

What the specs take of the store and of the terms: `CprjAnswers` (`Ingress::get_ci_cprj` against
the view's constructors, at the loads among a run's calls, with the field count a rule is
asserted to have), `StoredRuleRep` (a
stored rule as the circuit holds it) and `CtorTeleSmall` (a constructor's telescopes are below
the circuit's cutoff bound).

The model facts the specs read: `fieldsClassify_shape` (the recursive fields' indices and entries
are in range), `ruleBodies_length`, and `allMinors_ctors` with `rules_minors_of_allMinors` (where
the reconstruction has its minor premises, every constructor is one of the view's and a
recursor's rules name minors among them). -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Binding.FamilyFlat (FlatEntry peelForalls exprInstLevels)
open IxVM.Refinement.Core (W KExpr KLevel KKey bmeta kexprEnum kexprListEnum addrTy addrListEnum
  ixAddr Resolved ExprLvEq krrEnum krrListEnum)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open IxVM.Refinement.Decl (TmExact)
open IxVM (F)

set_option maxHeartbeats 2400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## `ctors_before_pos` -/

section CtorsBefore

variable {κ : _root_.Address → KKey}

/-- Every entry of a flattened family whose parameter counts are read is an inductive type. -/
theorem ind_of_flatOwnParams {V : ReconView} :
    ∀ {es : List FlatEntry} {fop : List Nat}, flatOwnParams V es = some fop →
      ∀ e ∈ es, ∃ d, V.ind e.addr = some (some d)
  | [], _, _, e, he => by cases he
  | e₀ :: es, fop, h, e, he => by
    simp only [flatOwnParams] at h
    cases hi : V.ind e₀.addr with
    | none => rw [hi] at h; cases h
    | some o =>
      cases o with
      | none => rw [hi] at h; cases h
      | some d =>
        cases hr : flatOwnParams V es with
        | none => rw [hi, hr] at h; cases h
        | some ns =>
          rcases List.mem_cons.mp he with rfl | he'
          · exact ⟨d, hi⟩
          · exact ind_of_flatOwnParams hr e he'

/-- **`KernelCheck::ctors_before_pos(flat, target, cur)`** is `ctorsBefore` at the positions left
to the target, over a flattened family of inductive types: the constructors of the entries from
`cur` up to `target`. (At an entry that is no inductive type the circuit counts no constructor
where the model has no value, whence `hind`.) -/
theorem ctors_before_pos_spec {V : ReconView} {root : List (Call F)}
    (hI : IndAnswers root κ V) {target : Nat} (htarget : target < 9223372036854775808) :
    ∀ (es : List FlatEntry) (cur : Nat) {xflat r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)}, cur ≤ target →
      (∀ e ∈ es, ∃ d, V.ind e.addr = some (some d)) →
      ObsFn W "KernelCheck::ctors_before_pos" [xflat, .field (target : F), .field (cur : F)] h r
        h' cs →
      (∀ c ∈ cs, c ∈ root) →
      RepList flatListEnum (FlatEntryRepExact κ) h es xflat →
      Heap.Extends h h' ∧
        ∃ n, ctorsBefore V es (target - cur) = some n ∧ r = .field (n : F) := by
  intro es
  induction es with
  | nil =>
    intro cur xflat r h h' cs hle hind ev hroot hes
    have hext : Heap.Extends h h' := ObsFn.heap_extends ev
    match Obs.«KernelCheck::ctors_before_pos».obs ev with
    | .n0 (op17 := op) (he24 := hr) .. =>
      obtain rfl := binop_sub_eq_zero_nat (by omega) (by omega) op
      exact ⟨hext, 0, by simp [ctorsBefore], by simpa using hr⟩
    | .other_Nil (op17 := op) (hne27 := hne) (he50 := hr) .. =>
      have hne' := binop_sub_ne_nat op hne
      obtain ⟨k, hk⟩ : ∃ k, target - cur = k + 1 := ⟨target - cur - 1, by omega⟩
      exact ⟨hext, 0, by rw [hk]; rfl, by simpa using hr⟩
    | .other_Cons (ld42 := ld) .. =>
      obtain ⟨z, zs, hzs, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hzs
  | cons e es ih =>
    intro cur xflat r h h' cs hle hind ev hroot hes
    have hext : Heap.Extends h h' := ObsFn.heap_extends ev
    match Obs.«KernelCheck::ctors_before_pos».obs ev with
    | .n0 (op17 := op) (he24 := hr) .. =>
      obtain rfl := binop_sub_eq_zero_nat (by omega) (by omega) op
      exact ⟨hext, 0, by simp [ctorsBefore], by simpa using hr⟩
    | .other_Nil (ld42 := ld) .. =>
      cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    | .other_Cons (x_rest := xrest) (x_addr := xaddr) (v109 := ci) (m110 := m1) (v208 := vn)
        (m209 := m2) (cs229 := cs2) (y218 := vy) (v234 := vc) (op17 := op) (hne27 := hne)
        (ld42 := ld) (ev125 := evci) (ld119 := ldci) (sg216 := sg) (op262 := opc) (ev231 := evr)
        (op224 := opr) (hc264 := hc) .. =>
      have hne' := binop_sub_ne_nat op hne
      obtain ⟨k, hk⟩ : ∃ k, target - cur = k + 1 := ⟨target - cur - 1, by omega⟩
      obtain ⟨z, zs, hzs, hz, hzs'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection hzs with hz1 hz2
      subst hz1 hz2
      obtain ⟨xa, xps, xls, a, hp, ra, ha, -, -⟩ := hz
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp
      obtain ⟨rfl, -, -, -⟩ := hp
      obtain ⟨d₀, hd₀⟩ := hind e (List.mem_cons_self ..)
      have hans := hI ra evci (hroot _ (by rw [hc]; simp))
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) ldci
      obtain ⟨d, hd, rfl, rfl⟩ : ∃ d : IndData, V.ind e.addr = some (some d) ∧
          vn = .field (d.nctors : F) ∧ m2 = m1 := by
        match sg with
        | .Induct (hv148 := hv) (he198 := hr1) (he199 := hm) .. =>
          obtain ⟨d, ba, hd, -, -, -, -, -, -, -, -, -, hnc, -⟩ := hans.1 _ _ _ _ _ _ _ _ hv
          rw [ha] at hd
          exact ⟨d, hd, by rw [hr1, hnc], hm⟩
        | .other (hne201 := hno) .. =>
          have := hans.2 hno
          rw [ha, hd₀] at this
          cases this
      obtain rfl := binop_add_one_nat opc
      have ext1 : Heap.Extends h m2 := ObsFn.heap_extends evci
      obtain ⟨-, n, hn, rfl⟩ := ih (cur + 1) (by omega)
        (fun e' he' => hind e' (List.mem_cons_of_mem _ he')) evr
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) (flatList_mono ext1 hzs')
      obtain rfl := binop_add_nat opr
      refine ⟨hext, d.nctors + n, ?_, rfl⟩
      rw [hk]
      have hk' : target - (cur + 1) = k := by omega
      rw [hk'] at hn
      simp only [ctorsBefore, hd, hn]

end CtorsBefore

/-! ## A stored rule's λs along a telescope -/

section Lams

variable {κ : _root_.Address → KKey}

/-- **`KernelCheck::peel_n_foralls(e, n)`** on `TmOExact` is `peelForalls`; no allocation. -/
theorem peel_n_foralls_tmOExact :
    ∀ (n : Nat) {E : KExpr} {p r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 18446744069414584320 → TmOExact κ h E p →
      ObsFn W "KernelCheck::peel_n_foralls" [p, .field (n : F)] h r h' cs →
      h' = h ∧ ∃ E', peelForalls n E = some E' ∧ TmOExact κ h E' r
  | 0, E, p, r, h, h', cs, _, hE, ev => by
    match Obs.«KernelCheck::peel_n_foralls».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh
      exact ⟨rfl, E, rfl, hE⟩
    | .other (hne19 := hne) .. => exact (hne (by simp)).elim
  | n + 1, E, p, r, h, h', cs, hn, hE, ev => by
    match Obs.«KernelCheck::peel_n_foralls».obs ev with
    | .n0 (hv14 := hv) .. => exact (field_succ_ne_zero n (by omega) hv).elim
    | .other (ld34 := ld) (op87 := op) (ev64 := e1) .. =>
      obtain rfl := evalBinOp_sub_succ n op
      obtain ⟨D, B, ℓ, rfl, -, hb, -⟩ := TmOExact.forallE_of_load hE ld
      obtain ⟨hh, E', hp, hE'⟩ := peel_n_foralls_tmOExact n (by omega) hb e1
      exact ⟨hh, E', by simpa only [peelForalls] using hp, hE'⟩

/-- **`KernelCheck::rule_lam_doms(l, p, n, elim)`** is `LamsAlong`: the term under `n` λs of `l`,
each with the datum of the elimination level and the domain of the corresponding binder of `p`
(the circuit finds the two domains structurally equal, so they are one term). -/
theorem rule_lam_doms_spec {elim : KLevel} {xelim : SourceValue F} :
    ∀ (n : Nat) {L P : KExpr} {xl xp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 18446744069414584320 →
      ObsFn W "KernelCheck::rule_lam_doms" [xl, xp, .field (n : F), xelim] h r h' cs →
      TmOExact κ h L xl → TmOExact κ h P xp → RepKLevel h elim xelim →
      Heap.Extends h h' ∧ ∃ R, LamsAlong elim n L P R ∧ TmOExact κ h' R r
  | 0, L, P, xl, xp, r, h, h', cs, _, ev, hL, hP, hel => by
    match Obs.«KernelCheck::rule_lam_doms».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh
      exact ⟨Heap.Extends.refl _, L, .zero, hL⟩
    | .other (hne19 := hne) .. => exact (hne (by simp)).elim
  | n + 1, L, P, xl, xp, r, h, h', cs, hn, ev, hL, hP, hel => by
    have hext : Heap.Extends h h' := ObsFn.heap_extends ev
    match Obs.«KernelCheck::rule_lam_doms».obs ev with
    | .n0 (hv14 := hv) .. => exact (field_succ_ne_zero n (by omega) hv).elim
    | .other (m71 := m1) (m154 := m2) (ld34 := ld) (ev81 := evpw) (heq104 := hpw) (ld116 := ldp)
        (ev164 := eveq) (heq187 := heq) (op225 := op) (ev193 := evr) .. =>
      obtain rfl := evalBinOp_sub_succ n op
      obtain ⟨Dl, Bl, ℓ, rfl, hDl, hBl, hl⟩ := TmOExact.lam_of_load hL ld
      have hz := pw_eq_exact hl hel evpw
      rw [hpw] at hz
      have hzero : ℓ.zeronessOf = elim.zeronessOf := by
        by_contra hne
        rw [ite_eq_right hne] at hz
        exact absurd (Value.field.inj hz) (by decide)
      have ext1 : Heap.Extends h m1 := ObsFn.heap_extends evpw
      obtain ⟨Dp, Bp, ℓp, rfl, hDp, hBp, -⟩ := TmOExact.forallE_of_load (hP.mono ext1) ldp
      obtain ⟨k₁, r₁⟩ := hDl.mono ext1
      obtain ⟨k₂, r₂⟩ := hDp
      subst heq
      have hdom : Dl = Dp := IxVM.Refinement.Decl.kexpr_struct_eq_one
        (tmExact_depth_le r₁ (max k₁ k₂) (Nat.le_max_left _ _))
        (tmExact_depth_le r₂ (max k₁ k₂) (Nat.le_max_right _ _)) eveq
      subst hdom
      have ext2 : Heap.Extends m1 m2 := ObsFn.heap_extends eveq
      obtain ⟨-, R, hR, hr⟩ := rule_lam_doms_spec n (by omega) evr
        (hBl.mono (ext1.trans ext2)) (hBp.mono ext2) (hel.mono (ext1.trans ext2))
      exact ⟨hext, R, .succ hzero (ExprLvEq.refl _) hR, hr⟩

end Lams

/-! ## The shape of a constructor's classified fields -/

/-- A recursive field's entry is a position of the flattened family. -/
theorem isRecField_lt {V : ReconView} {es : List FlatEntry} {liftBy : Nat} {e : KExpr} {m : Nat}
    (h : isRecField V es liftBy e = some m) : m < es.length := by
  unfold isRecField at h
  split at h
  · split at h
    · exact (List.findIdx?_eq_some_iff_getElem.mp h).1
    · cases h
  · cases h

/-- **The shape of `fieldsClassify`'s answer**: one domain for each leading binder and one
normalized type for each domain, as many recursive fields as entries for them, every recursive
field's index below the fields' count past the first index, and every entry a position of the
flattened family. -/
theorem fieldsClassify_shape {V : ReconView} {f : Nat} {es : List FlatEntry} {liftBy : Nat} :
    ∀ (E : KExpr) (fidx : Nat) {ds ns : List KExpr} {ri rm : List Nat} {ret : KExpr},
      fieldsClassify V f es liftBy fidx E = some (ds, ri, rm, ret, ns) →
      ds.length = (peelAll E).1.length ∧ ns.length = ds.length ∧ ri.length = rm.length ∧
        (∀ i ∈ ri, i < fidx + ds.length) ∧ ∀ m ∈ rm, m < es.length := by
  intro E
  induction E with
  | forallE d b bm _ ihb =>
    intro fidx ds ns ri rm ret h
    cases hw : whnfTele V f f d with
    | none => simp only [fieldsClassify, hw] at h; cases h
    | some nd =>
      cases hr : fieldsClassify V f es liftBy (fidx + 1) b with
      | none => simp only [fieldsClassify, hw, hr] at h; cases h
      | some q =>
        obtain ⟨ds', ri', rm', ret', ns'⟩ := q
        obtain ⟨h1, h2, h3, h4, h5⟩ := ihb (fidx + 1) hr
        cases hf : isRecField V es (liftBy + fidx) nd with
        | none =>
          simp only [fieldsClassify, hw, hr, hf, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, -, rfl⟩ := h
          refine ⟨by simp [peelAll, h1], by simp [h2], h3, fun i hi => ?_, h5⟩
          have := h4 i hi
          simp only [List.length_cons]
          omega
        | some m =>
          simp only [fieldsClassify, hw, hr, hf, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, -, rfl⟩ := h
          refine ⟨by simp [peelAll, h1], by simp [h2], by simp [h3], fun i hi => ?_,
            fun m' hm' => ?_⟩
          · simp only [List.length_cons]
            rcases List.mem_cons.mp hi with rfl | hi'
            · omega
            · have := h4 i hi'
              omega
          · rcases List.mem_cons.mp hm' with rfl | hm''
            · exact isRecField_lt hf
            · exact h5 m' hm''
  | _ =>
    intro fidx ds ns ri rm ret h
    simp only [fieldsClassify, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, -, rfl⟩ := h
    simp [peelAll]

/-! ## `apply_ihs_full` -/

section Ihs

variable {κ : _root_.Address → KKey}

/-- `Lists::lookup_or_default(xs, i, 0)` on a list of naturals. -/
theorem natField_lookup_or_default {ns : List Nat} {l r : SourceValue F} {i : Nat}
    (hi : i < 18446744069414584321) {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::lookup_or_default<Field>» [l, .field (i : F), .field 0] h r
      h' cs)
    (hl : RepList fieldListEnum RepNatField h ns l) :
    r = .field (((ns[i]?).getD 0 : Nat) : F) ∧ h' = h := by
  obtain ⟨hh, hcase⟩ := Lib.Lists.lookup_or_default_spec (t := .field) (R := RepNatField)
    (by rw [Obs.Names.«Lists::lookup_or_default<Field>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<Field>».symbol]; exact hl)
  rw [fval_natCast hi] at hcase
  rcases hcase with ⟨x, hx, hr⟩ | ⟨hlen, hr⟩
  · exact ⟨by rw [hx]; exact hr, hh⟩
  · refine ⟨?_, hh⟩
    have hnone : ns[i]? = none := List.getElem?_eq_none (by omega)
    rw [hnone, hr]
    simp

/-- `Lists::lookup_or_default(as, i, d)` on a list of addresses, inside the list. -/
theorem addr_lookup_or_default {pas : List Bytes.Address} {l r dflt : SourceValue F} {i : Nat}
    (hi : i < pas.length) (hi' : i < 18446744069414584321) {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::lookup_or_default<&[Field; 32]>» [l, .field (i : F), dflt] h
      r h' cs)
    (hl : RepList addrListEnum (Bytes.RepAddressRef addrTy) h pas l) :
    (∃ a, pas[i]? = some a ∧ Bytes.RepAddressRef addrTy h a r) ∧ h' = h := by
  obtain ⟨hh, hcase⟩ := Lib.Lists.lookup_or_default_spec (t := .ptr (.array .field 32))
    (R := Bytes.RepAddressRef addrTy)
    (by rw [Obs.Names.«Lists::lookup_or_default<&[Field; 32]>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&[Field; 32]>».symbol]; exact hl)
  rw [fval_natCast hi'] at hcase
  rcases hcase with ⟨x, hx, hr⟩ | ⟨hlen, -⟩
  · exact ⟨⟨x, hx, hr⟩, hh⟩
  · omega

/-- `Lists::drop(xs, n)` on a list of terms. -/
theorem kexpr_drop {R : Heap F → KExpr → SourceValue F → Prop} {xs : List KExpr}
    {l r : SourceValue F} {n : Nat} (hn : n < 18446744069414584321) {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [l, .field (n : F)] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) : RepList kexprListEnum R h (xs.drop n) r ∧ h' = h := by
  obtain ⟨-, hdrop, hh⟩ := Lib.Lists.drop_spec (t := .ptr (.named "KernelTypes::KExprNode" []))
    (R := R) _ rfl
    (by rw [Obs.Names.«Lists::drop<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)
  rw [fval_natCast hn, Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hdrop
  exact ⟨hdrop, hh⟩

/-- **An `App` cell** applies two represented terms. -/
theorem tmOExact_app_cell {h : Heap F} {Fn A : KExpr} {xf xa : SourceValue F}
    (hf : TmOExact κ h Fn xf) (ha : TmOExact κ h A xa) :
    TmOExact κ (h ++ [.construct kexprEnum "App" [xf, xa]]) (.app Fn A)
      (.ptr (.enum kexprEnum) h.length) := by
  have ext : Heap.Extends h (h ++ [.construct kexprEnum "App" [xf, xa]]) := Heap.Extends.snoc _ _
  obtain ⟨k₁, r₁⟩ := hf
  obtain ⟨k₂, r₂⟩ := ha
  exact ⟨max k₁ k₂, .app (by simp) (tmExact_depth_le (r₁.mono ext) _ (Nat.le_max_left _ _))
    (tmExact_depth_le (r₂.mono ext) _ (Nat.le_max_right _ _))⟩

/-- **A `Const` cell** at an address whose key resolves. -/
theorem tmOExact_const_cell {h : Heap F} {a : Bytes.Address} {ls : List KLevel}
    {xa xls : SourceValue F} (hres : Resolved (κ (ixAddr a)))
    (ra : Bytes.RepAddressRef addrTy h a xa) (rls : RepKLevelList h ls xls) :
    TmOExact κ (h ++ [.construct kexprEnum "Const" [xa, xls]]) (.const (κ (ixAddr a)) ls)
      (.ptr (.enum kexprEnum) h.length) := by
  have ext : Heap.Extends h (h ++ [.construct kexprEnum "Const" [xa, xls]]) :=
    Heap.Extends.snoc _ _
  exact ⟨0, .const (by simp) (Bytes.repAddressRef_heapMono₂ addrTy ext ra) (rls.mono ext)⟩

/-- **`KernelCheck::apply_ihs_full`** is `applyIhs`: the head applied to one inductive hypothesis
for each recursive field, the peer recursor of the field's entry applied to the parameters,
motives, minors, the field type's indices and the field. The recursive fields are below the
field count and their entries are positions of the peers (at an entry past the peers the circuit
names the zero address where the model has no value); the keying is the view's (`hK`) and
resolves at every address (`hres`). -/
theorem apply_ihs_full_spec {V : ReconView} (hK : ∀ a, V.key a = κ a)
    (hres : ∀ a : _root_.Address, Resolved (κ a))
    {rm : List Nat} {norm : List KExpr} {pas : List Bytes.Address} {fop : List Nat}
    {nP nMot nMin nFields : Nat} {recLvls : List KLevel} {elim : KLevel}
    (hcnt : nP + nMot + nMin < 288230376151711744) (hnf : nFields < 4294967296)
    (hrmb : ∀ m ∈ rm, m < pas.length) (hfopb : ∀ n ∈ fop, n < 72057594037927936)
    {root : List (Call F)} :
    ∀ (ri : List Nat) (k : Nat) {H : KExpr}
      {xh xri xrm xnorm xpeers xfop xlvls xelim r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)}, k + ri.length ≤ rm.length → (∀ i ∈ ri, i < nFields) →
      ObsFn W "KernelCheck::apply_ihs_full"
        [xh, xri, xrm, xnorm, xpeers, xfop, .field (nP : F), .field (nMot : F),
          .field (nMin : F), .field (nFields : F), xlvls, .field (k : F), xelim] h r h' cs →
      IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ root) →
      TmOExact κ h H xh → RepList fieldListEnum RepNatField h ri xri →
      RepList fieldListEnum RepNatField h rm xrm →
      RepList kexprListEnum (TmOExact κ) h norm xnorm →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h pas xpeers →
      RepList fieldListEnum RepNatField h fop xfop → RepKLevelList h recLvls xlvls →
      RepKLevel h elim xelim →
      Heap.Extends h h' ∧ ∃ B,
        applyIhs V rm norm (pas.map ixAddr) fop nP nMot nMin nFields recLvls elim H k ri =
          some B ∧ TmOExact κ h' B r := by
  intro ri
  induction ri with
  | nil =>
    intro k H xh xri xrm xnorm xpeers xfop xlvls xelim r h h' cs hk hri ev hbnd hroot hH hxri
      hxrm hxnorm hxpeers hxfop hxlvls hxelim
    match Obs.«KernelCheck::apply_ihs_full».obs ev with
    | .Nil (he21 := hr) (he22 := hh) .. =>
      subst hr hh
      exact ⟨Heap.Extends.refl _, H, rfl, hH⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨z, zs, hzs, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hxri ld
      cases hzs
  | cons fieldIdx rest ih =>
    intro k H xh xri xrm xnorm xpeers xfop xlvls xelim r h h' cs hk hri ev hbnd hroot hH hxri
      hxrm hxnorm hxpeers hxfop hxlvls hxelim
    have hext : Heap.Extends h h' := ObsFn.heap_extends ev
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    match Obs.«KernelCheck::apply_ihs_full».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hxri ld
    | .Cons (x_field_idx := xfi) (x_rest := xrest) (v41 := vmem) (m42 := m42) (v78 := vtarget)
        (m79 := m79) (m110 := m110) (v121 := vtnp) (m122 := m122) (v158 := vdepth)
        (x166 := x166) (x174 := x174) (v194 := vdom) (m195 := m195) (v224 := vs1) (m225 := m225) (cs235 := csl1)
        (v239 := vsh1) (v270 := vlifted) (m271 := m271) (v285 := vsh2) (m318 := m318)
        (x_forall_doms := xfds) (x_inner_body := xinner) (v356 := vnxs) (m357 := m357)
        (v378 := vinner) (m397 := m397) (v427 := vwp) (m428 := m428) (v443 := vst1)
        (v480 := vwm) (m481 := m481) (v496 := vst2) (x518 := x518) (v542 := vwmin)
        (m543 := m543) (v558 := vst3) (x580 := x580) (x588 := x588) (m614 := m614)
        (x__dh := xdh) (x_dargs := xdargs) (v652 := vidx) (m653 := m653) (v682 := vwidx)
        (m683 := m683) (v712 := vfb) (x720 := x720) (x728 := x728) (m748 := m748)
        (v770 := vfapp) (m771 := m771) (m808 := m808) (v838 := vih) (m839 := m839)
        (m877 := m877) (v924 := vk1)
        (ld12 := ld) (ev54 := evmem) (hm118 := hm110) (ev91 := evtarget) (ev134 := evtnp)
        (op189 := op189) (op181 := op181) (op173 := op173) (ev207 := evdom) (op261 := op261)
        (ev237 := evl1) (op307 := op307) (ev283 := evl2) (ev331 := evpeel) (ev369 := evlen)
        (op393 := op393) (hm407 := hm397) (op472 := op472) (ev440 := evwp) (op533 := op533)
        (op525 := op525) (ev493 := evwm) (op603 := op603) (op595 := op595) (op587 := op587)
        (ev555 := evwmin) (ev_dbxiljsh := evspine) (ev665 := evdrop) (ev695 := evapp)
        (op743 := op743) (op735 := op735) (op727 := op727) (hm758 := hm748) (ev783 := evxs)
        (hm818 := hm808) (ev851 := evlams) (hm887 := hm877) (op1016 := op1016) (ev912 := evrec)
        (hc1025 := hc) .. =>
      -- the recursive field's index
      obtain ⟨z, zs, hzs, hz, hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hxri ld
      injection hzs with hz1 hz2
      subst hz1 hz2
      obtain rfl : xfi = .field (fieldIdx : F) := hz
      have hfi : fieldIdx < nFields := hri fieldIdx (List.mem_cons_self ..)
      simp only [List.length_cons] at hk
      -- its entry
      have hrmlen : rm.length < 2 ^ 39 :=
        RomBound.bounded_length_lt hbnd
          (c := ⟨Obs.Names.«Lists::lookup_or_default<Field>», [xrm, .field (k : F), .field 0], h⟩)
          (by rw [hc]; simp) (by simp) hxrm
      obtain ⟨rfl, hm42⟩ := natField_lookup_or_default (by omega) evmem hxrm
      obtain rfl := hm42.symm
      have hmemlt : (rm[k]?).getD 0 < pas.length := by
        rw [List.getElem?_eq_getElem (by omega : k < rm.length)]
        exact hrmb _ (List.getElem_mem _)
      generalize hmi : (rm[k]?).getD 0 = memIdx at *
      -- the peer recursor of the entry
      subst hm110
      have ext110 : Heap.Extends h (h ++ [.tuple (List.replicate 32 (.field 0))]) :=
        Heap.Extends.snoc _ _
      have hpaslen : pas.length < 2 ^ 39 :=
        RomBound.bounded_length_lt hbnd
          (c := ⟨Obs.Names.«Lists::lookup_or_default<&[Field; 32]>», [xpeers, .field (memIdx : F),
            .ptr (.tuple (List.map Value.type (List.replicate 32 ((.field 0) : SourceValue F))))
              h.length], h ++ [.tuple (List.replicate 32 (.field 0))]⟩)
          (by rw [hc]; simp) (by simp)
          (repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ addrTy) ext110 hxpeers)
      obtain ⟨⟨a, ha, ra⟩, hm79⟩ := addr_lookup_or_default hmemlt (by omega) evtarget
        (repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ addrTy) ext110 hxpeers)
      obtain rfl := hm79.symm
      -- the entry's parameter count
      obtain ⟨rfl, hm122⟩ := natField_lookup_or_default (by omega) evtnp
        (fieldList_mono ext110 hxfop)
      obtain rfl := hm122.symm
      have htnp : (fop[memIdx]?).getD 0 < 72057594037927936 := by
        cases hfm : fop[memIdx]? with
        | none => simp
        | some x => exact hfopb x (List.mem_of_getElem? hfm)
      generalize htn : (fop[memIdx]?).getD 0 = tnp at *
      -- depths
      obtain rfl := binop_add_nat op189
      obtain rfl := binop_add_nat op181
      obtain rfl := binop_add_nat op173
      -- the field's normalized type, lifted twice
      obtain rfl := binop_sub_nat (by omega) op261
      have evl1' : ObsFn W "KernelSubst::expr_lift"
          [vdom, .field ((nFields - fieldIdx : Nat) : F), .field ((0 : Nat) : F)] m195 vs1 m225
          csl1 := by simpa using evl1
      obtain ⟨⟨dom, hdom, hdomr⟩, hm195⟩ := kexpr_lookup evdom (tmOExactList_mono ext110 hxnorm)
      obtain rfl := hm195.symm
      rw [fval_natCast (by omega)] at hdom
      have hs1 := expr_lift_tmOExact (by omega) (by decide)
        (sub fun c hc' => by rw [hc]; simp [hc']) hdomr evl1'
      have ext225 : Heap.Extends _ m225 := ObsFn.heap_extends evl1
      obtain rfl := binop_add_nat op307
      have hlifted := expr_lift_tmOExact (by omega) hnf
        (sub fun c hc' => by rw [hc]; simp [hc']) hs1 evl2
      have ext271 : Heap.Extends m225 m271 := ObsFn.heap_extends evl2
      -- its telescope
      obtain ⟨xl, xb, htup, ext318, hfds, hinner⟩ := peel_leading_foralls_spec evpeel
        (sub fun c hc' => by rw [hc]; simp [hc']) hlifted
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
      obtain ⟨rfl, rfl⟩ := htup
      generalize hdomL : (dom.liftLooseBVars (nFields - fieldIdx) 0).liftLooseBVars (nMot + nMin)
        nFields = domL at *
      have hnxs : (peelAll domL).1.length < 2 ^ 39 :=
        RomBound.bounded_length_lt hbnd
          (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [xfds], m318⟩)
          (by rw [hc]; simp) (by simp) hfds
      obtain ⟨rfl, hm357⟩ := kexpr_length evlen hfds
      obtain rfl := hm357.symm
      obtain rfl := binop_add_nat op393
      generalize hfdsl : (peelAll domL).1.length = nxs at *
      -- the peer recursor applied to the parameters, motives and minors
      subst hm397
      have ext0 := ext110.trans (ext225.trans (ext271.trans ext318))
      have hconst := tmOExact_const_cell (κ := κ) (hres (ixAddr a))
        (Bytes.repAddressRef_heapMono₂ addrTy (ext225.trans (ext271.trans ext318)) ra)
        (hxlvls.mono ext0)
      have ext397 : Heap.Extends m318
          (m318 ++ [.construct "KernelTypes::KExprNode" "Const" [vtarget, xlvls]]) :=
        Heap.Extends.snoc _ _
      obtain rfl := binop_sub_one_nat (by omega) op472
      have hwp := build_apply_bvars_decreasing_spec (κ := κ) (by omega) (by omega) (by omega)
        evwp hconst
      obtain rfl := binop_sub_one_nat (by omega) op533
      obtain rfl := binop_sub_nat (by omega) op525
      have hwm := build_motive_apps_spec (κ := κ) (by omega) (by omega) (by omega) evwm hwp
      obtain rfl := binop_sub_one_nat (by omega) op603
      obtain rfl := binop_sub_nat (by omega) op595
      obtain rfl := binop_sub_nat (by omega) op587
      have hwmin := build_minor_apps_spec (κ := κ) (by omega) (by omega) (by omega) evwmin hwm
      have ext428 : Heap.Extends _ m428 := ObsFn.heap_extends evwp
      have ext481 : Heap.Extends m428 m481 := ObsFn.heap_extends evwm
      have ext543 : Heap.Extends m481 m543 := ObsFn.heap_extends evwmin
      have ext1 := ext397.trans (ext428.trans (ext481.trans ext543))
      -- the field type's indices
      obtain ⟨-, -, hargs⟩ := collect_spine_zeta_spec (hinner.mono ext1)
        (sub fun c hc' => by rw [hc]; simp [hc']) evspine
      have ext614 : Heap.Extends m543 m614 := ObsFn.heap_extends evspine
      obtain ⟨hdropped, hm653⟩ := kexpr_drop (by omega) evdrop hargs
      obtain rfl := hm653.symm
      have hwidx := apply_spine_expr_spec (κ := κ) _ evapp (hwmin.mono ext614) hdropped
      have ext683 : Heap.Extends m614 m683 := ObsFn.heap_extends evapp
      -- the field applied to its arguments
      obtain rfl := binop_sub_one_nat (by omega) op743
      obtain rfl := binop_sub_nat (by omega) op735
      obtain rfl := binop_add_nat op727
      subst hm748
      have hfapp := build_apply_xs_spec (κ := κ) (by omega) evxs
        (tmOExact_bvar_cell (κ := κ) (h := m683) (b := nFields - 1 - fieldIdx + nxs) (by omega))
      have ext748 : Heap.Extends m683
          (m683 ++ [.construct "KernelTypes::KExprNode" "BVar"
            [.field ((nFields - 1 - fieldIdx + nxs : Nat) : F)]]) := Heap.Extends.snoc _ _
      have ext771 : Heap.Extends _ m771 := ObsFn.heap_extends evxs
      -- the inductive hypothesis
      subst hm808
      have hinnerApp := tmOExact_app_cell (hwidx.mono (ext748.trans ext771)) hfapp
      have ext808 : Heap.Extends m771
          (m771 ++ [.construct "KernelTypes::KExprNode" "App" [vwidx, vfapp]]) :=
        Heap.Extends.snoc _ _
      have ext2 := ext614.trans (ext683.trans (ext748.trans (ext771.trans ext808)))
      have hih := wrap_lams_spec (κ := κ) _ evlams hinnerApp
        (tmOExactList_mono (ext1.trans ext2) hfds) (hxelim.mono (ext0.trans (ext1.trans ext2)))
      have ext839 : Heap.Extends _ m839 := ObsFn.heap_extends evlams
      subst hm877
      have extAll := ext0.trans (ext1.trans (ext2.trans ext839))
      have hhead := tmOExact_app_cell (hH.mono extAll) hih
      have ext877 : Heap.Extends m839
          (m839 ++ [.construct "KernelTypes::KExprNode" "App" [xh, vih]]) := Heap.Extends.snoc _ _
      have extF := extAll.trans ext877
      -- the remaining recursive fields
      obtain rfl := binop_add_one_nat op1016
      obtain ⟨-, B, hB, hBr⟩ := ih (k + 1) (by omega)
        (fun i hi => hri i (List.mem_cons_of_mem _ hi)) evrec
        (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hhead (fieldList_mono extF hrest)
        (fieldList_mono extF hxrm) (tmOExactList_mono extF hxnorm)
        (repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ addrTy) extF hxpeers)
        (fieldList_mono extF hxfop) (hxlvls.mono extF) (hxelim.mono extF)
      refine ⟨hext, B, ?_, hBr⟩
      have hpeer : (pas.map ixAddr)[memIdx]? = some (ixAddr a) := by
        rw [List.getElem?_map, ha]
        rfl
      simp only [applyIhs, hmi, hpeer, hdom, htn, hdomL, hfdsl, hK]
      exact hB

end Ihs

/-! ## `build_rule_rhs` -/

/-- **The two telescopes a rule is built from are short**: a constructor's type (at the entry's
levels) past its parameters, as it stands and with the parameters instantiated, has fewer than
`2^32` leading binders. (The circuit counts the first's binders in the field and lifts at the
count as a cutoff, which its lifting reads below `2^32`.) -/
def CtorTeleSmall (V : ReconView) (cty : KExpr) (nOwn : Nat) (us : List KLevel) (aux : Bool)
    (sp : List KExpr) : Prop :=
  (∀ raw, peelForalls nOwn (exprInstLevels us cty) = some raw →
      (peelAll raw).1.length < 4294967296) ∧
    ∀ f after, peelCtorParams V f nOwn 0 aux sp nOwn 0 (exprInstLevels us cty) = some after →
      (peelAll after).1.length < 4294967296

section RuleRhs

variable {κ : _root_.Address → KKey}

/-- **`KernelCheck::build_rule_rhs`** is `ruleBody` at every large enough fuel: the minor premise
of the constructor applied to its fields and to the inductive hypotheses of the recursive ones.
The rule's minor premise is one of the recursor's (`hminor`: the circuit computes its variable by
a subtraction in the field), and there is a peer for each entry (`hpeers`). -/
theorem build_rule_rhs_spec (hinj : Function.Injective κ) {V : ReconView}
    {root : List (Call F)}
    (hA : AddrOf κ V) (hD : DefnAnswers root κ V) (hI : IndAnswers root κ V)
    (hC : CtorOfAnswers root V) (hM : ModeledAnswers root V) (hK : ∀ a, V.key a = κ a)
    (hres : ∀ a : _root_.Address, Resolved (κ a))
    {es : List FlatEntry} {fop : List Nat} {pas : List Bytes.Address} {cty : KExpr}
    {minorIdx nP nMot nMin nOwn : Nat} {us recLvls : List KLevel} {aux : Bool} {sp : List KExpr}
    {elim : KLevel} (hcnt : nP + nMot + nMin < 288230376151711744) (hminor : minorIdx < nMin)
    (hown : nOwn < 72057594037927936) (hpeers : pas.length = es.length)
    (hfopb : ∀ n ∈ fop, n < 72057594037927936) (hsmall : CtorTeleSmall V cty nOwn us aux sp)
    {xrc xcty xus xlvls xflat xpeers xfop xsp xelim r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::build_rule_rhs"
      [xrc, xcty, .field (minorIdx : F), .field (nP : F), .field (nMot : F), .field (nMin : F),
        .field (nOwn : F), xus, xlvls, xflat, xpeers, xfop, auxVal aux, xsp, xelim] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (hcty : TmOExact κ h cty xcty) (hus : RepKLevelList h us xus)
    (hlvls : RepKLevelList h recLvls xlvls)
    (hes : RepList flatListEnum (FlatEntryRepExact κ) h es xflat)
    (hxpeers : RepList addrListEnum (Bytes.RepAddressRef addrTy) h pas xpeers)
    (hxfop : RepList fieldListEnum RepNatField h fop xfop)
    (hsp : RepList kexprListEnum (TmOExact κ) h sp xsp) (hel : RepKLevel h elim xelim) :
    Heap.Extends h h' ∧ ∃ B, TmOExact κ h' B r ∧
      Eventually fun f => ruleBody V f es fop (pas.map ixAddr) cty minorIdx nP nMot nMin nOwn us
        recLvls aux sp elim = some B := by
  have hext : Heap.Extends h h' := ObsFn.heap_extends ev
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono hbnd hs
  match Obs.«KernelCheck::build_rule_rhs».obs ev with
  | .run (v1 := vinst) (m2 := m2) (v31 := vraw) (m32 := m32) (v61 := vnf) (m62 := m62)
      (cs72 := cs72) (v90 := vdepth) (x98 := x98) (x106 := x106) (v126 := vpt) (m127 := m127)
      (v164 := vafter) (m165 := m165) (cs175 := cs175) (m249 := m249) (cs260 := cs260)
      (m295 := m295) (m308 := m308) (m321 := m321) (m334 := m334) (x_field_doms := xds)
      (x_rec_indices := xri) (x_rec_member_idxs := xrm) (x__ret_ty := xret)
      (x_norm_doms := xns) (v407 := vlen) (m410 := m410) (v437 := vmv) (x445 := x445)
      (y446 := y446) (x462 := x462) (m482 := m482) (v504 := vwf) (m505 := m505)
      (cs552 := cs552)
      (ev14 := evinst) (ev_voldfhzh := evraw) (ev74 := evcount) (op121 := op121)
      (op113 := op113) (op105 := op105) (ev139 := evctx) (ev177 := evpeel) (hm303 := hm295)
      (hm316 := hm308) (hm329 := hm321) (hm342 := hm334) (ev262 := evwalk) (ev420 := evlen)
      (heq436 := heqlen) (op460 := op460) (op477 := op477) (op469 := op469) (op452 := op452)
      (hm492 := hm482) (ev517 := evfb) (ev554 := evihs) (hc658 := hc) .. =>
    -- the constructor's type at the entry's levels, and its field count
    have hinst := expr_inst_levels_tmOExact (sub fun c hc' => by rw [hc]; simp [hc']) hcty hus
      evinst
    have ext2 : Heap.Extends h m2 := ObsFn.heap_extends evinst
    obtain ⟨raw, hraw, hrawr⟩ := peel_n_foralls_zeta_spec nOwn (by omega) hinst
      (sub fun c hc' => by rw [hc]; simp [hc']) evraw
    have ext32 : Heap.Extends m2 m32 := ObsFn.heap_extends evraw
    have evcount' : ObsFn W "KernelCheck::count_foralls_body" [vraw, .field ((0 : Nat) : F)] m32
        vnf m62 cs72 := by simpa using evcount
    have hvnf := count_foralls_body_spec evcount' (sub fun c hc' => by rw [hc]; simp [hc'])
      hrawr
    rw [Nat.zero_add] at hvnf
    subst hvnf
    have hnFs := hsmall.1 raw hraw
    generalize hnF : (peelAll raw).1.length = nF at *
    have ext62 : Heap.Extends m32 m62 := ObsFn.heap_extends evcount
    obtain rfl := binop_add_nat op121
    obtain rfl := binop_add_nat op113
    obtain rfl := binop_add_nat op105
    have ext127 : Heap.Extends m62 m127 := ObsFn.heap_extends evctx
    have extA : Heap.Extends h m127 := ext2.trans (ext32.trans (ext62.trans ext127))
    -- the type past its parameters, instantiated
    have evpeel' : ObsFn W "KernelCheck::peel_ctor_params_subst"
        [xrc, vinst, .field (nOwn : F), .field (nOwn : F), .field ((0 : Nat) : F), auxVal aux,
          xsp, .field ((0 : Nat) : F), vpt] m127 vafter m165 cs175 := by simpa using evpeel
    have hsplen : sp.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbnd
        (c := ⟨"KernelCheck::peel_ctor_params_subst", [xrc, vinst, .field (nOwn : F),
          .field (nOwn : F), .field 0, auxVal aux, xsp, .field 0, vpt], m127⟩)
        (by rw [hc]; simp) (by simp) (tmOExactList_mono extA hsp)
    obtain ⟨ext165, after, hafter, ⟨a1, ha1⟩⟩ := peel_ctor_params_subst_spec hA hD hI hC hM
      (depth := nOwn) (lift := 0) (aux := aux) (Ps := sp) (by omega) (by decide) (by omega)
      nOwn 0 (by omega) (fun i _ hi _ => by omega) evpeel'
      (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      (hinst.mono (ext32.trans (ext62.trans ext127))) (tmOExactList_mono extA hsp)
    have hafters := hsmall.2 a1 after (ha1 a1 le_rfl)
    -- its fields, classified
    have e295 : Heap.Extends m165 m295 := by rw [hm295]; exact Heap.Extends.snoc _ _
    have e308 : Heap.Extends m295 m308 := by rw [hm308]; exact Heap.Extends.snoc _ _
    have e321 : Heap.Extends m308 m321 := by rw [hm321]; exact Heap.Extends.snoc _ _
    have e334 : Heap.Extends m321 m334 := by rw [hm334]; exact Heap.Extends.snoc _ _
    have hnilD : RepList kexprListEnum (TmOExact κ) m295 []
        (.ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m165.length) := by
      rw [hm295]; exact Lib.rep_store_nil m165
    have hnilR : RepList fieldListEnum RepNatField m308 []
        (.ptr (.enum Obs.Names.«Lists::Node<Field>») m295.length) := by
      rw [hm308]; exact Lib.rep_store_nil m295
    have hnilRM : RepList fieldListEnum RepNatField m321 []
        (.ptr (.enum Obs.Names.«Lists::Node<Field>») m308.length) := by
      rw [hm321]; exact Lib.rep_store_nil m308
    have hnilN : RepList kexprListEnum (TmOExact κ) m334 []
        (.ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m321.length) := by
      rw [hm334]; exact Lib.rep_store_nil m321
    have extB : Heap.Extends m165 m334 := e295.trans (e308.trans (e321.trans e334))
    have evwalk' : ObsFn W "KernelCheck::walk_fields_classify"
        [xrc, vafter, xflat,
          .ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m165.length,
          .ptr (.enum Obs.Names.«Lists::Node<Field>») m295.length,
          .ptr (.enum Obs.Names.«Lists::Node<Field>») m308.length,
          .ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m321.length,
          .field 0, .field ((0 : Nat) : F), vpt] m334 (.tuple [xds, xri, xrm, xret, xns]) m249
        cs260 := by simpa using evwalk
    obtain ⟨ext249, xds', xri', xrm', xret', xns', ds, ns, ri, rm, ret, htup, hds, hri, hrm, -,
        hns, ⟨a2, ha2⟩⟩ :=
      walk_fields_classify_nil_spec hinj hA hD hI hC hM (es := es) (liftBy := 0) (by omega)
        evwalk' (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) (hafter.mono extB)
        (flatList_mono (extA.trans (ext165.trans extB)) hes)
        (tmOExactList_mono (e308.trans (e321.trans e334)) hnilD)
        (fieldList_mono (e321.trans e334) hnilR) (fieldList_mono e334 hnilRM) hnilN
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
    obtain ⟨rfl, rfl, rfl, -, rfl⟩ := htup
    obtain ⟨hsh1, -, hsh3, hsh4, hsh5⟩ := fieldsClassify_shape after 0 (ha2 a2 le_rfl)
    obtain ⟨rfl, hm410⟩ := kexpr_length evlen hds
    obtain rfl := hm410.symm
    have hlen : ds.length = nF :=
      natCast_inj_small (by omega) (by omega) (Value.field.inj heqlen)
    -- the minor premise applied to the fields
    obtain rfl := binop_sub_one_nat (by omega) op460
    obtain rfl := binop_add_nat op477
    obtain rfl := binop_add_nat op469
    obtain rfl := binop_sub_nat (by omega) op452
    have e482 : Heap.Extends m249 m482 := by rw [hm482]; exact Heap.Extends.snoc _ _
    have hbase : TmOExact κ m482 (.bvar (nP + nMot + nMin + nF - 1 - (nP + nMot + minorIdx)))
        (.ptr (.enum kexprEnum) m249.length) := by
      rw [hm482]; exact tmOExact_bvar_cell (by omega)
    have hwf := build_apply_field_bvars_spec (κ := κ) (by omega) (Nat.le_refl nF) evfb hbase
    have ext505 : Heap.Extends m482 m505 := ObsFn.heap_extends evfb
    have extC : Heap.Extends m249 m505 := e482.trans ext505
    have extD : Heap.Extends h m505 :=
      extA.trans (ext165.trans (extB.trans (ext249.trans extC)))
    -- and to the inductive hypotheses
    have evihs' : ObsFn W "KernelCheck::apply_ihs_full"
        [vwf, xri, xrm, xns, xpeers, xfop, .field (nP : F), .field (nMot : F), .field (nMin : F),
          .field (nF : F), xlvls, .field ((0 : Nat) : F), xelim] m505 r h' cs552 := by
      simpa using evihs
    obtain ⟨-, B, hB, hBr⟩ := apply_ihs_full_spec hK hres hcnt hnFs
      (fun m hm => by rw [hpeers]; exact hsh5 m hm) hfopb ri 0 (by omega)
      (fun i hi => by have := hsh4 i hi; omega) evihs'
      (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hwf (fieldList_mono extC hri)
      (fieldList_mono extC hrm) (tmOExactList_mono extC hns)
      (repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ addrTy) extD hxpeers)
      (fieldList_mono extD hxfop) (hlvls.mono extD) (hel.mono extD)
    refine ⟨hext, B, hBr, ⟨max a1 a2, fun f hf => ?_⟩⟩
    simp only [ruleBody, hraw, ha1 f (by omega), ha2 f (by omega), hnF, hlen, ↓reduceIte]
    exact hB

end RuleRhs

/-! ## `populate_rules` -/

/-- **`Ingress::get_ci_cprj` matches `V.ctor`**, for a load that is one of the calls `calls` and
whose own calls are among them, at an inductive position and a constructor index below `2^56`:
where it loads a constructor, the view has the constructor's type and parameter count, the count
below `2^56` with its field count, the type represented exactly; the field count is the one `NF`
gives the constructor (a functional reading of the store ties two records' rules of one
constructor to one count). Where it loads another kind the view has no constructor there. -/
def CprjAnswers (calls : List (Call F)) (κ : _root_.Address → KKey) (V : ReconView)
    (NF : _root_.Address → Nat → Nat → Nat → Prop) : Prop :=
  ∀ {xblk p ci : SourceValue F} {h m : Heap F} {cs : List (Call F)} {ba : Bytes.Address}
    {i c : Nat}, Bytes.RepAddressRef addrTy h ba xblk → i < 72057594037927936 →
    c < 72057594037927936 →
    ObsFn W "Ingress::get_ci_cprj" [xblk, .field (i : F), .field (c : F)] h p m cs →
    (⟨"Ingress::get_ci_cprj", [xblk, .field (i : F), .field (c : F)], h⟩ : Call F) ∈ calls →
    (∀ c' ∈ cs, c' ∈ calls) →
    loadValue m p = .ok ci →
    (∀ xnl xty xb xi xci xnp xnf xu,
      ci = .construct "KernelTypes::KConstantInfo" "Ctor" [xnl, xty, xb, xi, xci, xnp, xnf, xu] →
      ∃ (cty : KExpr) (np nf : Nat), V.ctor (ixAddr ba) i c = some (cty, np) ∧
        np < 72057594037927936 ∧ nf < 72057594037927936 ∧ TmOExact κ m cty xty ∧
        xnp = .field (np : F) ∧ xnf = .field (nf : F) ∧ NF (ixAddr ba) i c nf) ∧
    ((∀ vs : List (SourceValue F), vs.length = 8 →
        ci ≠ .construct "KernelTypes::KConstantInfo" "Ctor" vs) →
      V.ctor (ixAddr ba) i c = none)

/-- One rule body for each constructor. -/
theorem ruleBodies_length {V : ReconView} {f : Nat} {es : List FlatEntry} {fop : List Nat}
    {peers : List _root_.Address} {nP nMot nMin : Nat} {us recLvls : List KLevel} {aux : Bool}
    {sp : List KExpr} {elim : KLevel} {blk : _root_.Address} {idx off : Nat} :
    ∀ (cs : List Nat) {bodies : List KExpr},
      ruleBodies V f es fop peers nP nMot nMin us recLvls aux sp elim blk idx off cs =
        some bodies → bodies.length = cs.length
  | [], bodies, h => by
    simp only [ruleBodies, Option.some.injEq] at h
    subst h
    rfl
  | c :: cs, bodies, h => by
    simp only [ruleBodies] at h
    cases hc : V.ctor blk idx c with
    | none => simp only [hc] at h; cases h
    | some q =>
      obtain ⟨cty, np⟩ := q
      cases hb : ruleBody V f es fop peers cty (off + c) nP nMot nMin np us recLvls aux sp elim
        with
      | none => simp only [hc, hb] at h; cases h
      | some b =>
        cases hr : ruleBodies V f es fop peers nP nMot nMin us recLvls aux sp elim blk idx off cs
          with
        | none => simp only [hc, hb, hr, Option.map_none] at h; cases h
        | some bs =>
          simp only [hc, hb, hr, Option.map_some, Option.some.injEq] at h
          subst h
          simp [ruleBodies_length cs hr]

section Populate

variable {κ : _root_.Address → KKey}

/-- **`KernelCheck::populate_rules`** from the constructor `cidx` is `ruleBodies` over the
constructors from `cidx` on, at every large enough fuel: the rule body of each, its minor premise
the `off + c`-th. Every constructor of the inductive is one of the view's (`hctors`: at a load
that is no constructor the circuit ends the list where the model has no value), and the rules'
minor premises are among the recursor's (`hoff`). -/
theorem populate_rules_spec (hinj : Function.Injective κ) {V : ReconView}
    {root : List (Call F)}
    (hA : AddrOf κ V) (hD : DefnAnswers root κ V) (hI : IndAnswers root κ V)
    (hC : CtorOfAnswers root V) (hM : ModeledAnswers root V) (hK : ∀ a, V.key a = κ a)
    (hres : ∀ a : _root_.Address, Resolved (κ a))
    {NF : _root_.Address → Nat → Nat → Nat → Prop} (hP : CprjAnswers root κ V NF)
    {es : List FlatEntry} {fop : List Nat} {pas : List Bytes.Address} {ba : Bytes.Address}
    {idx off numCtors nP nMot nMin : Nat} {us recLvls : List KLevel} {aux : Bool}
    {sp : List KExpr} {elim : KLevel} (hcnt : nP + nMot + nMin < 288230376151711744)
    (hoff : off + numCtors ≤ nMin) (hnc : numCtors < 72057594037927936)
    (hidx : idx < 72057594037927936)
    (hpeers : pas.length = es.length) (hfopb : ∀ n ∈ fop, n < 72057594037927936)
    (hctors : ∀ c, c < numCtors → V.ctor (ixAddr ba) idx c ≠ none)
    (hsmall : ∀ c cty np, c < numCtors → V.ctor (ixAddr ba) idx c = some (cty, np) →
      CtorTeleSmall V cty np us aux sp) :
    ∀ (n cidx : Nat) {xrc xblk xus xlvls xflat xpeers xfop xsp xelim r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)}, cidx + n = numCtors →
      ObsFn W "KernelCheck::populate_rules"
        [xrc, .field (numCtors : F), .field (off : F), xblk, .field (idx : F), .field (nP : F),
          .field (nMot : F), .field (nMin : F), xus, xlvls, xflat, xpeers, xfop, auxVal aux, xsp,
          .field (cidx : F), xelim] h r h' cs →
      IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ root) →
      Bytes.RepAddressRef addrTy h ba xblk → RepKLevelList h us xus →
      RepKLevelList h recLvls xlvls → RepList flatListEnum (FlatEntryRepExact κ) h es xflat →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h pas xpeers →
      RepList fieldListEnum RepNatField h fop xfop →
      RepList kexprListEnum (TmOExact κ) h sp xsp → RepKLevel h elim xelim →
      Heap.Extends h h' ∧ ∃ bodies, RepList kexprListEnum (TmOExact κ) h' bodies r ∧
        Eventually fun f => ruleBodies V f es fop (pas.map ixAddr) nP nMot nMin us recLvls aux
          sp elim (ixAddr ba) idx off (List.range' cidx n) = some bodies := by
  intro n
  induction n with
  | zero =>
    intro cidx xrc xblk xus xlvls xflat xpeers xfop xsp xelim r h h' cs hsum ev hbnd hroot hba
      hus hlvls hes hxpeers hxfop hsp hel
    have hext : Heap.Extends h h' := ObsFn.heap_extends ev
    match Obs.«KernelCheck::populate_rules».obs ev with
    | .n0 (he28 := hr) (hm27 := hm) .. =>
      subst hr hm
      exact ⟨hext, [], Lib.rep_store_nil h, Eventually.always fun _ => rfl⟩
    | .other_Ctor (op17 := op) (hne33 := hne) .. =>
      exact absurd (by omega) (binop_sub_ne_nat op hne)
    | .other_other (op17 := op) (hne33 := hne) .. =>
      exact absurd (by omega) (binop_sub_ne_nat op hne)
  | succ n ih =>
    intro cidx xrc xblk xus xlvls xflat xpeers xfop xsp xelim r h h' cs hsum ev hbnd hroot hba
      hus hlvls hes hxpeers hxfop hsp hel
    have hext : Heap.Extends h h' := ObsFn.heap_extends ev
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    match Obs.«KernelCheck::populate_rules».obs ev with
    | .n0 (op17 := op) .. =>
      have := binop_sub_eq_zero_nat (by omega) (by omega) op
      omega
    | .other_other (ev53 := evci) (ld47 := ldci) (hne466 := hno) (hc478 := hc) .. =>
      exact absurd ((hP hba hidx (by omega) evci (hroot _ (by rw [hc]; simp))
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) ldci).2 hno) (hctors cidx (by omega))
    | .other_Ctor (m38 := m38) (x_ctor_ty := xcty) (x_np := xnp) (v140 := vmi) (v158 := vb)
        (m159 := m159) (v301 := vrest) (m310 := m310) (v336 := vc1) (ev53 := evci)
        (ld47 := ldci) (op155 := opmi) (ev171 := evrhs) (he296 := hr) (hm295 := hm)
        (op456 := opc) (ev320 := evrec) (hc465 := hc) .. =>
      obtain ⟨cty, np, nf, hctor, hnp, -, hcty, rfl, -, -⟩ :=
        (hP hba hidx (by omega) evci (hroot _ (by rw [hc]; simp))
          (fun c hc' => hroot c (by rw [hc]; simp [hc'])) ldci).1 _ _ _ _ _ _ _ _ rfl
      obtain rfl := binop_add_nat opmi
      have ext38 : Heap.Extends h m38 := ObsFn.heap_extends evci
      obtain ⟨ext159, B, hB, ⟨a1, ha1⟩⟩ := build_rule_rhs_spec hinj hA hD hI hC hM hK hres hcnt
        (by omega) hnp hpeers hfopb (hsmall cidx cty np (by omega) hctor) evrhs
        (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hcty (hus.mono ext38)
        (hlvls.mono ext38) (flatList_mono ext38 hes)
        (repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ addrTy) ext38 hxpeers)
        (fieldList_mono ext38 hxfop) (tmOExactList_mono ext38 hsp) (hel.mono ext38)
      obtain rfl := binop_add_one_nat opc
      have ext2 : Heap.Extends h m159 := ext38.trans ext159
      obtain ⟨ext310, bodies, hbodies, ⟨a2, ha2⟩⟩ := ih (cidx + 1) (by omega) evrec
        (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc']))
        (Bytes.repAddressRef_heapMono₂ addrTy ext2 hba) (hus.mono ext2) (hlvls.mono ext2)
        (flatList_mono ext2 hes)
        (repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ addrTy) ext2 hxpeers)
        (fieldList_mono ext2 hxfop) (tmOExactList_mono ext2 hsp) (hel.mono ext2)
      subst hr hm
      refine ⟨hext, B :: bodies,
        Lib.rep_store_cons tmOExact_heapMono₂ (hB.mono ext310) hbodies,
        ⟨max a1 a2, fun f hf => ?_⟩⟩
      rw [List.range'_succ]
      simp only [ruleBodies, hctor, ha1 f (by omega), ha2 f (by omega), Option.map_some]

end Populate

/-! ## `compare_rules` -/

/-- **A stored rule as the circuit holds it** (`KernelTypes::KRecRule::Mk(cidx, nfields, rhs)`):
the constructor index, the field count and the right-hand side, represented exactly. -/
def StoredRuleRep (κ : _root_.Address → KKey) (h : Heap F) (ru : Nat × Nat × KExpr)
    (v : SourceValue F) : Prop :=
  ∃ xrhs, v = .construct krrEnum "Mk" [.field (ru.1 : F), .field (ru.2.1 : F), xrhs] ∧
    ru.1 < 18446744069414584321 ∧ ru.2.1 < 72057594037927936 ∧ TmOExact κ h ru.2.2 xrhs

theorem storedRuleRep_heapMono₂ {κ : _root_.Address → KKey} : HeapMono₂ (StoredRuleRep κ) :=
  fun _ _ _ _ ext h =>
    let ⟨xrhs, hv, h1, h2, hr⟩ := h
    ⟨xrhs, hv, h1, h2, hr.mono ext⟩

section Compare

variable {κ : _root_.Address → KKey}

/-- **`KernelCheck::compare_rules`** from the position `pos`: the stored rules are no more than
the reconstructed bodies where these reach the constructor count, and every stored rule that has
a reconstructed body names the constructor at its position, a constructor of the inductive, has
the constructor's field count (`NF`), and follows the body under the λs of the recursor type
(`RuleFollows`, its minor premise the `minorOff + pos + j`-th). The circuit finds the λs'
domains and the body structurally equal to the type's and the reconstruction's, so the
relations of `RuleFollows` hold as equalities. -/
theorem compare_rules_spec {V : ReconView} {NF : _root_.Address → Nat → Nat → Nat → Prop}
    {root : List (Call F)}
    (hP : CprjAnswers root κ V NF) {ty : KExpr} {elim : KLevel} {ba : Bytes.Address}
    {nP nMot nMin numCtors minorOff idx : Nat} (hcnt : nP + nMot + nMin < 288230376151711744)
    (hoff : minorOff + numCtors ≤ nMin) (hnc : numCtors < 72057594037927936)
    (hidx : idx < 72057594037927936) :
    ∀ (stored : List (Nat × Nat × KExpr)) (canon : List KExpr) (pos : Nat)
      {xstored xcanon xblk xelim xty r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      pos ≤ numCtors →
      ObsFn W "KernelCheck::compare_rules"
        [xstored, xcanon, .field (nP : F), .field (nMot : F), .field (nMin : F), xblk,
          .field (idx : F), .field (numCtors : F), .field (pos : F), xelim, xty,
          .field (minorOff : F)] h r h' cs →
      IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ root) →
      RepList krrListEnum (StoredRuleRep κ) h stored xstored →
      RepList kexprListEnum (TmOExact κ) h canon xcanon → TmOExact κ h ty xty →
      RepKLevel h elim xelim → Bytes.RepAddressRef addrTy h ba xblk →
      Heap.Extends h h' ∧ (pos + canon.length = numCtors → stored.length ≤ canon.length) ∧
        ∀ (j : Nat) (ru : Nat × Nat × KExpr) (cb : KExpr), stored[j]? = some ru →
          canon[j]? = some cb →
          ru.1 = pos + j ∧ pos + j < numCtors ∧ NF (ixAddr ba) idx (pos + j) ru.2.1 ∧
            RuleFollows ty nP nMot nMin (minorOff + pos + j) ru.2.1 elim ru.2.2 cb := by
  intro stored
  induction stored with
  | nil =>
    intro canon pos xstored xcanon xblk xelim xty r h h' cs hpos ev hbnd hroot hst hcanon hty
      hel hba
    exact ⟨ObsFn.heap_extends ev, fun _ => Nat.zero_le _, fun j ru cb hj => by simp at hj⟩
  | cons ru₀ rest ih =>
    intro canon pos xstored xcanon xblk xelim xty r h h' cs hpos ev hbnd hroot hst hcanon hty
      hel hba
    have hext : Heap.Extends h h' := ObsFn.heap_extends ev
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    -- what both paths of a stored rule read
    have head : ∀ {xrest xcidx xnf xrhs vlt xcnf p157 : SourceValue F} {m115 m150 : Heap F}
        {cs123 cs163 : List (Call F)} {w1 w2 w3 w4 w5 w6 w7 : SourceValue F},
        loadValue h xstored = .ok (.construct Obs.Names.«Lists::Node<KernelTypes::KRecRule>»
          "Cons" [.construct "KernelTypes::KRecRule" "Mk" [xcidx, xnf, xrhs], xrest]) →
        xcidx = .field (pos : F) →
        ObsFn W "UInt32::less_than_fields" [xcidx, .field (numCtors : F)] h vlt m115 cs123 →
        vlt = .field 1 →
        ObsFn W "Ingress::get_ci_cprj" [xblk, .field (idx : F), xcidx] m115 p157 m150 cs163 →
        (⟨"Ingress::get_ci_cprj", [xblk, .field (idx : F), xcidx], m115⟩ : Call F) ∈ root →
        (∀ c ∈ cs163, c ∈ root) →
        loadValue m150 p157 = .ok (.construct "KernelTypes::KConstantInfo" "Ctor"
          [w1, w2, w3, w4, w5, w6, xcnf, w7]) →
        xnf = xcnf →
        h = m115 ∧ xcidx = .field (pos : F) ∧ xnf = .field (ru₀.2.1 : F) ∧ ru₀.1 = pos ∧
          pos < numCtors ∧ NF (ixAddr ba) idx pos ru₀.2.1 ∧ TmOExact κ h ru₀.2.2 xrhs ∧
          RepList krrListEnum (StoredRuleRep κ) h rest xrest := by
      intro xrest xcidx xnf xrhs vlt xcnf p157 m115 m150 cs123 cs163 w1 w2 w3 w4 w5 w6 w7 ld
        hci evlt hlt evci hself hsubc ldci hnfeq
      obtain ⟨z, zs, hzs, hz, hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hst ld
      injection hzs with hz1 hz2
      subst hz1 hz2
      obtain ⟨xrhs', hv, hcib, hnfb, hrhs⟩ := hz
      simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      have hcidx : ru₀.1 = pos := natCast_inj_small hcib (by omega) (Value.field.inj hci)
      obtain ⟨hiff, hm115⟩ := ltf_nat hcib (by omega) evlt
      have hlt' : ru₀.1 < numCtors := hiff.mp hlt
      subst hm115
      obtain ⟨cty, np, nf, -, -, hnf, -, -, rfl, hNF⟩ :=
        (hP hba hidx (by omega) evci hself hsubc ldci).1 _ _ _ _ _ _ _ _ rfl
      have hnfe : ru₀.2.1 = nf :=
        natCast_inj_small (by omega) (by omega) (Value.field.inj hnfeq)
      rw [hcidx] at hNF
      rw [← hnfe] at hNF
      exact ⟨rfl, hci, rfl, hcidx, by omega, hNF, hrhs, hrest⟩
    match Obs.«KernelCheck::compare_rules».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hst ld
    | .Cons_Nil (m150 := m150) (ld12 := ld) (heq100 := hci) (ev125 := evlt) (heq148 := hlt)
        (ev165 := evci) (ld159 := ldci) (heq288 := hnfeq) (ld302 := ldc) (hc314 := hc) .. =>
      obtain ⟨rfl, -, -, -, hposlt, -, -, -⟩ := head ld hci evlt hlt evci
        (hroot _ (by rw [hc]; simp)) (fun c hc' => hroot c (by rw [hc]; simp [hc'])) ldci hnfeq
      have ext150 : Heap.Extends h m150 := ObsFn.heap_extends evci
      obtain rfl := IxVM.Refinement.Core.RepList.nil_of_load (tmOExactList_mono ext150 hcanon) ldc
      exact ⟨hext, fun hc => by simp at hc; omega, fun j ru cb _ hj => by simp at hj⟩
    | .Cons_Cons (x_rest := xrest) (x_cidx := xcidx) (x_nf := xnf) (x_rhs := xrhs)
        (m115 := m115) (m150 := m150) (x_cbody := xcbody) (x_crest := xcrest) (v332 := vpre)
        (x340 := x340) (v359 := vminor) (v377 := vap) (m378 := m378) (m424 := m424)
        (p431 := pmd) (v441 := vpeel) (x455 := x455) (x_mdom := xmdom) (v494 := vfp)
        (m495 := m495) (cs505 := cs505) (v509 := vsh) (v540 := vsb) (m541 := m541)
        (v597 := veq) (m600 := m600) (v648 := vpos1)
        (ld12 := ld) (heq100 := hci) (ev125 := evlt) (heq148 := hlt) (ev165 := evci)
        (ld159 := ldci) (heq288 := hnfeq) (ld302 := ldc) (op355 := op355) (op347 := op347)
        (op374 := op374) (ev390 := evl1) (op470 := op470) (op462 := op462) (ev439 := evpeel)
        (ld433 := ldmd) (op531 := op531) (ev507 := evlift) (ev553 := evl2) (ev610 := eveq)
        (heq633 := heq) (op721 := op721) (ev639 := evrec) (hc744 := hc) .. =>
      obtain ⟨rfl, rfl, rfl, hcidx, hposlt, hNF, hrhs, hrest⟩ :=
        head ld hci evlt hlt evci (hroot _ (by rw [hc]; simp))
          (fun c hc' => hroot c (by rw [hc]; simp [hc'])) ldci hnfeq
      have ext150 : Heap.Extends h m150 := ObsFn.heap_extends evci
      obtain ⟨cb₀, crest, hcs, hcb, hcrest⟩ :=
        IxVM.Refinement.Core.RepList.cons_of_load (tmOExactList_mono ext150 hcanon) ldc
      subst hcs
      have hnfb : ru₀.2.1 < 72057594037927936 := by
        obtain ⟨z, zs, hzs, ⟨_, _, _, hb, _⟩, _⟩ :=
          IxVM.Refinement.Core.RepList.cons_of_load hst ld
        injection hzs with hz1 _
        subst hz1
        exact hb
      -- the λs of the parameters, motives and minors
      obtain rfl := binop_add_nat op355
      obtain rfl := binop_add_nat op347
      obtain rfl := binop_add_nat op374
      obtain ⟨ext378, R1, hl1, hR1⟩ := rule_lam_doms_spec (κ := κ) (nP + nMot + nMin) (by omega)
        evl1 (hrhs.mono ext150) (hty.mono ext150) (hel.mono ext150)
      -- the rule's minor premise
      obtain rfl := binop_add_nat op470
      obtain rfl := binop_add_nat op462
      obtain ⟨hm424, E', hpeel, hE'⟩ := peel_n_foralls_tmOExact (κ := κ)
        (nP + nMot + (minorOff + pos)) (by omega) (hty.mono (ext150.trans ext378)) evpeel
      obtain rfl := hm424.symm
      obtain ⟨mdom, mrest, ℓ, rfl, hmdom, -, -⟩ := TmOExact.forallE_of_load hE' ldmd
      obtain rfl := binop_sub_nat (by omega) op531
      have evlift' : ObsFn W "KernelSubst::expr_lift"
          [xmdom, .field ((nMin - (minorOff + pos) : Nat) : F), .field ((0 : Nat) : F)] m378 vfp
          m495 cs505 := by simpa using evlift
      have hfp := expr_lift_tmOExact (by omega) (by decide)
        (sub fun c hc' => by rw [hc]; simp [hc']) hmdom evlift'
      have ext495 : Heap.Extends m378 m495 := ObsFn.heap_extends evlift
      -- the λs of the fields, and the body
      obtain ⟨ext541, sb, hl2, hsb⟩ := rule_lam_doms_spec (κ := κ) ru₀.2.1 (by omega) evl2
        (hR1.mono ext495) hfp (hel.mono (ext150.trans (ext378.trans ext495)))
      subst heq
      obtain ⟨k₁, r₁⟩ := hsb
      obtain ⟨k₂, r₂⟩ := hcb.mono (ext378.trans (ext495.trans ext541))
      have hbody : sb = cb₀ := IxVM.Refinement.Decl.kexpr_struct_eq_one
        (tmExact_depth_le r₁ (max k₁ k₂) (Nat.le_max_left _ _))
        (tmExact_depth_le r₂ (max k₁ k₂) (Nat.le_max_right _ _)) eveq
      subst hbody
      have hfollows : RuleFollows ty nP nMot nMin (minorOff + pos) ru₀.2.1 elim ru₀.2.2 sb :=
        ⟨R1, mdom, mrest, sb, bmeta ℓ, hl1, hpeel, hl2, ExprLvEq.refl _⟩
      -- the remaining rules
      obtain rfl := binop_add_one_nat op721
      have ext600 : Heap.Extends m541 m600 := ObsFn.heap_extends eveq
      have extA : Heap.Extends h m600 :=
        ext150.trans (ext378.trans (ext495.trans (ext541.trans ext600)))
      obtain ⟨-, hlen, hrec⟩ := ih crest (pos + 1) (by omega) evrec
        (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc']))
        (repList_heapMono₂ _ storedRuleRep_heapMono₂ extA hrest)
        (tmOExactList_mono (ext378.trans (ext495.trans (ext541.trans ext600))) hcrest)
        (hty.mono extA) (hel.mono extA) (Bytes.repAddressRef_heapMono₂ addrTy extA hba)
      refine ⟨hext, fun hc => ?_, fun j ru cb hj hcj => ?_⟩
      · simp only [List.length_cons] at hc ⊢
        have := hlen (by omega)
        omega
      · cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj hcj
          subst hj hcj
          exact ⟨hcidx, hposlt, hNF, hfollows⟩
        | succ j =>
          simp only [List.getElem?_cons_succ] at hj hcj
          obtain ⟨h1, h2, h3, h4⟩ := hrec j ru cb hj hcj
          refine ⟨by omega, by omega, ?_, ?_⟩
          · rwa [show pos + (j + 1) = pos + 1 + j by omega]
          · rwa [show minorOff + pos + (j + 1) = minorOff + (pos + 1) + j by omega]

end Compare

/-! ## The minors a recursor's rules name -/

/-- One minor premise for each constructor, each constructor one of the view's. -/
theorem minorDoms_shape {V : ReconView} {f : Nat} {fullEs : List FlatEntry} {fop : List Nat}
    {aux : Bool} {sp : List KExpr} {us : List KLevel} {nrp nMot motiveBase selfMemIdx : Nat}
    {blk : _root_.Address} {idx : Nat} {elim : KLevel} :
    ∀ (cs : List Nat) (prev : Nat) {ms : List KExpr},
      minorDoms V f fullEs fop aux sp us nrp nMot motiveBase selfMemIdx blk idx elim prev cs =
        some ms → ms.length = cs.length ∧ ∀ c ∈ cs, V.ctor blk idx c ≠ none
  | [], prev, ms, h => by
    simp only [minorDoms, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun c hc => by cases hc⟩
  | c :: cs, prev, ms, h => by
    cases hc : V.ctor blk idx c with
    | none => simp only [minorDoms, hc] at h; cases h
    | some q =>
      obtain ⟨cty, np⟩ := q
      cases hm : minorAt V f fullEs fop (V.key (V.ctorAddr blk idx c)) cty np aux sp us nrp nMot
        prev motiveBase selfMemIdx elim with
      | none => simp only [minorDoms, hc, hm] at h; cases h
      | some m =>
        cases hr : minorDoms V f fullEs fop aux sp us nrp nMot motiveBase selfMemIdx blk idx elim
          (prev + 1) cs with
        | none => simp only [minorDoms, hc, hm, hr, Option.map_none] at h; cases h
        | some ms' =>
          simp only [minorDoms, hc, hm, hr, Option.map_some, Option.some.injEq] at h
          subst h
          obtain ⟨h1, h2⟩ := minorDoms_shape cs (prev + 1) hr
          refine ⟨by simp [h1], fun c' hc' => ?_⟩
          rcases List.mem_cons.mp hc' with rfl | hc''
          · rw [hc]; exact Option.some_ne_none _
          · exact h2 c' hc''

/-- **Where the reconstruction has its minor premises, a recursor's rules name minors among
them**: every constructor of an entry is one of the view's, and the constructors of the entries
before a position, with the position's own, are no more than the minors. -/
theorem allMinors_ctors {V : ReconView} {f : Nat} {fullEs : List FlatEntry} {fop : List Nat}
    {nrp nMot motiveBase : Nat} {elim : KLevel} :
    ∀ (es : List FlatEntry) (prev pos : Nat) {ms : List KExpr},
      allMinors V f fullEs fop nrp nMot motiveBase elim es prev pos = some ms →
      ∀ (k : Nat) (ek : FlatEntry) (d : IndData), es[k]? = some ek →
        V.ind ek.addr = some (some d) →
        (∀ c, c < d.nctors → V.ctor d.blk d.idx c ≠ none) ∧
          ∃ cb, ctorsBefore V es k = some cb ∧ cb + d.nctors ≤ ms.length
  | [], prev, pos, ms, h, k, ek, d, hk, _ => by simp at hk
  | e :: rest, prev, pos, ms, h, k, ek, d, hk, hd => by
    cases hi : V.ind e.addr with
    | none => simp only [allMinors, hi] at h; cases h
    | some o =>
      cases o with
      | none => simp only [allMinors, hi] at h; cases h
      | some i =>
        cases hm : minorDoms V f fullEs fop e.aux e.params e.levels nrp nMot motiveBase pos i.blk
          i.idx elim prev (List.range i.nctors) with
        | none => simp only [allMinors, hi, hm] at h; cases h
        | some ms₁ =>
          cases hr : allMinors V f fullEs fop nrp nMot motiveBase elim rest (prev + ms₁.length)
            (pos + 1) with
          | none => simp only [allMinors, hi, hm, hr, Option.map_none] at h; cases h
          | some ms₂ =>
            simp only [allMinors, hi, hm, hr, Option.map_some, Option.some.injEq] at h
            subst h
            obtain ⟨hl, hc⟩ := minorDoms_shape _ _ hm
            simp only [List.length_range] at hl
            cases k with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
              subst hk
              rw [hi] at hd
              simp only [Option.some.injEq] at hd
              subst hd
              refine ⟨fun c hlt => hc c (List.mem_range.mpr hlt), 0, by simp [ctorsBefore], ?_⟩
              simp only [List.length_append]
              omega
            | succ k =>
              simp only [List.getElem?_cons_succ] at hk
              obtain ⟨h1, cb, hcb, hle⟩ := allMinors_ctors rest _ _ hr k ek d hk hd
              refine ⟨h1, i.nctors + cb, by simp only [ctorsBefore, hi, hcb], ?_⟩
              simp only [List.length_append]
              omega

/-- **The rule side's two facts about the minors, from the reconstructed minor premises**: where
`allMinors` has a value, every constructor of the entry at `k` is one of the view's, and the
constructors before `k` with the entry's own are no more than the minor premises. -/
theorem rules_minors_of_allMinors {V : ReconView} {f : Nat} {es : List FlatEntry}
    {fop : List Nat} {nrp nMot motiveBase : Nat} {elim : KLevel} {minDoms : List KExpr}
    (hmin : allMinors V f es fop nrp nMot motiveBase elim es 0 0 = some minDoms) {k : Nat}
    {ek : FlatEntry} {self : IndData} (hek : es[k]? = some ek)
    (hself : V.ind ek.addr = some (some self)) :
    (∀ c, c < self.nctors → V.ctor self.blk self.idx c ≠ none) ∧
      ∀ cbk, ctorsBefore V es k = some cbk → cbk + self.nctors ≤ minDoms.length := by
  obtain ⟨h1, cb, hcb, hle⟩ := allMinors_ctors es 0 0 hmin k ek self hek hself
  refine ⟨h1, fun cbk hcbk => ?_⟩
  rw [hcb] at hcbk
  obtain rfl := Option.some.inj hcbk
  exact hle

/-! ## The rules of a recursor at its position -/

section AtPos

variable {κ : _root_.Address → KKey}

/-- **The rule side of `KernelCheck::canonical_rules_at_pos`**: its calls of `ctors_before_pos`,
`populate_rules` and `compare_rules` at the entry `k` of the flattened family, an inductive type
of the view, give what `MemberRecon` states of a recursor's rules: the reconstructed bodies
(`ruleBodiesAt`, at every large enough fuel, with the peers' addresses), the constructors before
the position (`ctorsBefore`), and, at every stored rule, that it is the rule of the constructor
at its position, with the constructor's field count (`NF`), and follows the reconstructed body
under the λs of the recursor type (`RuleFollows`). The stored rules are no more than the
constructors. -/
theorem rules_at_pos_spec (hinj : Function.Injective κ) {V : ReconView}
    {root : List (Call F)}
    (hA : AddrOf κ V) (hD : DefnAnswers root κ V) (hI : IndAnswers root κ V)
    (hC : CtorOfAnswers root V) (hM : ModeledAnswers root V) (hK : ∀ a, V.key a = κ a)
    (hres : ∀ a : _root_.Address, Resolved (κ a))
    {NF : _root_.Address → Nat → Nat → Nat → Prop} (hP : CprjAnswers root κ V NF)
    {es : List FlatEntry} {fop : List Nat} {pas : List Bytes.Address} {ba : Bytes.Address}
    {k off nP nMot nMin nl : Nat} {ek : FlatEntry} {self : IndData} {ty : KExpr}
    (hek : es[k]? = some ek) (hself : V.ind ek.addr = some (some self))
    (hblk : self.blk = ixAddr ba) (hfop : flatOwnParams V es = some fop)
    (hk : k < 9223372036854775808) (hcnt : nP + nMot + nMin < 288230376151711744)
    (hnc : self.nctors < 72057594037927936) (hidx : self.idx < 72057594037927936)
    (hpeers : pas.length = es.length) (hfopb : ∀ n ∈ fop, n < 72057594037927936)
    (hoff : ∀ cbk, ctorsBefore V es k = some cbk → cbk + self.nctors ≤ nMin)
    (hctors : ∀ c, c < self.nctors → V.ctor (ixAddr ba) self.idx c ≠ none)
    (hsmall : ∀ c cty np, c < self.nctors → V.ctor (ixAddr ba) self.idx c = some (cty, np) →
      CtorTeleSmall V cty np ek.levels ek.aux ek.params)
    {stored : List (Nat × Nat × KExpr)}
    {xrc xflat xblk xus xlvls xpeers xfop xsp xelim xrules xty vcb vcanon r : SourceValue F}
    {h₀ h₁ h₂ h₃ : Heap F} {cs₁ cs₂ cs₃ : List (Call F)}
    (evcb : ObsFn W "KernelCheck::ctors_before_pos" [xflat, .field (k : F), .field 0] h₀ vcb h₁
      cs₁)
    (evpop : ObsFn W "KernelCheck::populate_rules"
      [xrc, .field (self.nctors : F), vcb, xblk, .field (self.idx : F), .field (nP : F),
        .field (nMot : F), .field (nMin : F), xus, xlvls, xflat, xpeers, xfop, auxVal ek.aux,
        xsp, .field 0, xelim] h₁ vcanon h₂ cs₂)
    (evcmp : ObsFn W "KernelCheck::compare_rules"
      [xrules, vcanon, .field (nP : F), .field (nMot : F), .field (nMin : F), xblk,
        .field (self.idx : F), .field (self.nctors : F), .field 0, xelim, xty, vcb] h₂ r h₃ cs₃)
    (hb₂ : IxVM.Consistency.Bounded cs₂) (hb₃ : IxVM.Consistency.Bounded cs₃)
    (hr₁ : ∀ c ∈ cs₁, c ∈ root) (hr₂ : ∀ c ∈ cs₂, c ∈ root) (hr₃ : ∀ c ∈ cs₃, c ∈ root)
    (hes : RepList flatListEnum (FlatEntryRepExact κ) h₀ es xflat)
    (hba : Bytes.RepAddressRef addrTy h₀ ba xblk) (hus : RepKLevelList h₀ ek.levels xus)
    (hlvls : RepKLevelList h₀ ((List.range nl).map Ix.Kernel.Level.param) xlvls)
    (hxpeers : RepList addrListEnum (Bytes.RepAddressRef addrTy) h₀ pas xpeers)
    (hxfop : RepList fieldListEnum RepNatField h₀ fop xfop)
    (hsp : RepList kexprListEnum (TmOExact κ) h₀ ek.params xsp)
    (hel : RepKLevel h₀ (elimLevel off) xelim)
    (hst : RepList krrListEnum (StoredRuleRep κ) h₂ stored xrules)
    (hty : TmOExact κ h₂ ty xty) :
    Heap.Extends h₀ h₁ ∧ Heap.Extends h₁ h₂ ∧ Heap.Extends h₂ h₃ ∧
      ∃ (cbk : Nat) (bodies : List KExpr), ctorsBefore V es k = some cbk ∧
        (Eventually fun f =>
          ruleBodiesAt V f es off nP nMot nMin nl k (pas.map ixAddr) = some bodies) ∧
        stored.length ≤ self.nctors ∧
        ∀ (c : Nat) (ru : Nat × Nat × KExpr), stored[c]? = some ru →
          ru.1 = c ∧ c < self.nctors ∧ NF (ixAddr ba) self.idx c ru.2.1 ∧
            ∃ cb, bodies[c]? = some cb ∧
              RuleFollows ty nP nMot nMin (cbk + c) ru.2.1 (elimLevel off) ru.2.2 cb := by
  have evcb' : ObsFn W "KernelCheck::ctors_before_pos"
      [xflat, .field (k : F), .field ((0 : Nat) : F)] h₀ vcb h₁ cs₁ := by simpa using evcb
  obtain ⟨ext1, cbk, hcbk, rfl⟩ := ctors_before_pos_spec hI hk es 0 (Nat.zero_le k)
    (ind_of_flatOwnParams hfop) evcb' hr₁ hes
  rw [Nat.sub_zero] at hcbk
  have hoff' := hoff cbk hcbk
  have evpop' : ObsFn W "KernelCheck::populate_rules"
      [xrc, .field (self.nctors : F), .field (cbk : F), xblk, .field (self.idx : F),
        .field (nP : F), .field (nMot : F), .field (nMin : F), xus, xlvls, xflat, xpeers, xfop,
        auxVal ek.aux, xsp, .field ((0 : Nat) : F), xelim] h₁ vcanon h₂ cs₂ := by
    simpa using evpop
  obtain ⟨ext2, bodies, hbodies, hev⟩ := populate_rules_spec hinj hA hD hI hC hM hK hres hP
    hcnt hoff' hnc hidx hpeers hfopb hctors hsmall self.nctors 0 (Nat.zero_add _) evpop' hb₂ hr₂
    (Bytes.repAddressRef_heapMono₂ addrTy ext1 hba) (hus.mono ext1) (hlvls.mono ext1)
    (flatList_mono ext1 hes)
    (repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ addrTy) ext1 hxpeers)
    (fieldList_mono ext1 hxfop) (tmOExactList_mono ext1 hsp) (hel.mono ext1)
  have hblen : bodies.length = self.nctors := by
    obtain ⟨a, ha⟩ := hev
    simpa using ruleBodies_length _ (ha a (Nat.le_refl a))
  have evcmp' : ObsFn W "KernelCheck::compare_rules"
      [xrules, vcanon, .field (nP : F), .field (nMot : F), .field (nMin : F), xblk,
        .field (self.idx : F), .field (self.nctors : F), .field ((0 : Nat) : F), xelim, xty,
        .field (cbk : F)] h₂ r h₃ cs₃ := by simpa using evcmp
  have ext12 : Heap.Extends h₀ h₂ := ext1.trans ext2
  obtain ⟨ext3, hle, hfacts⟩ := compare_rules_spec hP hcnt hoff' hnc hidx stored bodies 0
    (Nat.zero_le _) evcmp' hb₃ hr₃ hst hbodies hty (hel.mono ext12)
    (Bytes.repAddressRef_heapMono₂ addrTy ext12 hba)
  have hsl : stored.length ≤ bodies.length := hle (by omega)
  refine ⟨ext1, ext2, ext3, cbk, bodies, hcbk, hev.mono fun f hf => ?_, by omega,
    fun c ru hc => ?_⟩
  · simp only [ruleBodiesAt, hek, hself, hfop, hcbk]
    rw [hblk]
    rw [← List.range_eq_range'] at hf
    exact hf
  · have hclt : c < stored.length := (List.getElem?_eq_some_iff.mp hc).1
    have hcb : bodies[c]? = some bodies[c] := List.getElem?_eq_getElem (by omega)
    obtain ⟨h1, h2, h3, h4⟩ := hfacts c ru _ hc hcb
    rw [Nat.zero_add] at h1 h2 h3
    rw [Nat.add_zero] at h4
    exact ⟨h1, h2, h3, _, hcb, h4⟩

end AtPos

end IxVM.Refinement.Binding.FamilyRecon
