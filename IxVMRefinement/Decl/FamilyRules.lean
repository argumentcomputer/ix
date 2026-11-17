import IxVMRefinement.Decl.FamilyIotaRuleInv

/-! # The rule loops of a modeled recursor (`check_rules_go`, `check_rules`)

`KernelModeled::check_rules` reads the recursor's major premise (`rec_major_pins`), loads its
inductive, compares the stored rule count with the inductive's constructor count, and runs
`KernelModeled::check_rules_go` over the stored rules from index `0`. Each iteration reads the
rule's iota theorem address from the advice stream (`get_address`), the constructor projection
`projection_addr_ctor(iidx, j, iblock)` and its constant (a `Ctor`, whose parameter count is the
inductive's and whose field count is the rule's), and calls `check_iota_rule`.

What is stated here are plain call facts over the observation, one record per stored rule:

* `CheckIotaRuleInvR.mono`: the inversion record of `check_iota_rule` over a larger call list.
* `RuleStepR`: one iteration of `check_rules_go` at rule index `j`: the stored rule's fields, the
  advice address read, the constructor projection and its load, and the `check_iota_rule` call
  (its arguments, its heap, its membership in the calls) with its inversion record.
* `RuleStepsR`: the iterations over a stored rule list, each with the rule it reads
  (`RuleRepExact`) and the advice address the stream yields.
* `check_rules_go_stepsR`, `check_rules_stepsR`: the observations yield those records; the
  latter also gives the inductive's load and the rule count. -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open Ix.Kernel (RecRule LevelParam)

set_option linter.unusedVariables false

/-- **The inversion record over a larger call list**: every call membership and sub-call
containment of `CheckIotaRuleInvR` carries over to a call list that contains the record's. -/
def CheckIotaRuleInvR.mono
    {rc rm nl ty_r rp ni rhs cprj cty cnp cnf ilvls pins t_addr src dst aset : SourceValue F}
    {h : Heap F} {calls calls' : List (Call F)} (hs : SubCalls calls' calls)
    (inv : CheckIotaRuleInvR rc rm nl ty_r rp ni rhs cprj cty cnp cnf ilvls pins t_addr src dst
      aset h calls) :
    CheckIotaRuleInvR rc rm nl ty_r rp ni rhs cprj cty cnp cnf ilvls pins t_addr src dst aset h
      calls' :=
  { inv with
    call_plen := hs _ inv.call_plen
    sub_sc := hs.trans inv.sub_sc
    sub_rhs_m := hs.trans inv.sub_rhs_m
    sub_rhs_inf := hs.trans inv.sub_rhs_inf
    sub_aset := hs.trans inv.sub_aset
    sub_tci := hs.trans inv.sub_tci
    sub_raddr := hs.trans inv.sub_raddr
    call_tlen := hs _ inv.call_tlen
    call_llen := hs _ inv.call_llen
    sub_pd := hs.trans inv.sub_pd
    sub_ctyl := hs.trans inv.sub_ctyl
    sub_csp0 := hs.trans inv.sub_csp0
    sub_cty_ren := hs.trans inv.sub_cty_ren
    sub_crest := hs.trans inv.sub_crest
    sub_csp := hs.trans inv.sub_csp
    call_clen := hs _ inv.call_clen
    sub_deidx := hs.trans inv.sub_deidx
    sub_ty_m := hs.trans inv.sub_ty_m
    sub_dt1 := hs.trans inv.sub_dt1
    sub_dt2 := hs.trans inv.sub_dt2
    sub_cty_ren2 := hs.trans inv.sub_cty_ren2
    sub_crestp := hs.trans inv.sub_crestp
    sub_lt1 := hs.trans inv.sub_lt1
    sub_lt2 := hs.trans inv.sub_lt2
    sub_derhs := hs.trans inv.sub_derhs
    sub_tl := hs.trans inv.sub_tl
    sub_detl := hs.trans inv.sub_detl
    sub_tr := hs.trans inv.sub_tr
    sub_detr := hs.trans inv.sub_detr
    sub_ta := hs.trans inv.sub_ta
    sub_deta := hs.trans inv.sub_deta }

/-- **One iteration of `KernelModeled::check_rules_go`**, at rule index `j`, on the rule list
`rules` at heap `h` and stream `s`: the stored rule's fields (`Mk(w_idx, rnf, rhs)`), the advice
address `t` read from the stream, the constructor projection `cprj` and its loaded `Ctor` (with
`cnp = inp` and `rnf = cnf` asserted), and the `check_iota_rule` call at heap `h_ci` with its
inversion record, every call a member of `calls`. -/
structure RuleStepR (rc rm nl ty rp ni iblock iidx inp ilvls pins src dst aset : SourceValue F)
    (j : Nat) (rules : SourceValue F) (h : Heap F) (s : SourceValue F) (calls : List (Call F)) where
  w_idx : SourceValue F
  rnf : SourceValue F
  rhs : SourceValue F
  rest : SourceValue F
  ld_rules : loadValue h rules = .ok (.construct Obs.Names.«Lists::Node<KernelTypes::KRecRule>»
    "Cons" [.construct "KernelTypes::KRecRule" "Mk" [w_idx, rnf, rhs], rest])
  t : SourceValue F
  s2 : SourceValue F
  h_ga : Heap F
  cs_ga : List (Call F)
  call_ga : (⟨"IxonDeserialize::get_address", [s], h⟩ : Call F) ∈ calls
  ev_ga : ObsFn W "IxonDeserialize::get_address" [s] h (.tuple [t, s2]) h_ga cs_ga
  cprj : SourceValue F
  h_cprj : Heap F
  cs_cprj : List (Call F)
  call_cprj : (⟨"KernelCheck::projection_addr_ctor", [iidx, .field (j : F), iblock], h_ga⟩ : Call F)
    ∈ calls
  ev_cprj : ObsFn W "KernelCheck::projection_addr_ctor" [iidx, .field (j : F), iblock] h_ga cprj
    h_cprj cs_cprj
  sub_cprj : SubCalls calls cs_cprj
  p_ci : SourceValue F
  h_ci : Heap F
  cs_ci : List (Call F)
  call_ci : (⟨"Ingress::get_ci", [cprj], h_cprj⟩ : Call F) ∈ calls
  ev_ci : ObsFn W "Ingress::get_ci" [cprj] h_cprj p_ci h_ci cs_ci
  sub_ci : SubCalls calls cs_ci
  w_cnl : SourceValue F
  cty : SourceValue F
  w_cblk : SourceValue F
  w_cind : SourceValue F
  w_cidx : SourceValue F
  cnp : SourceValue F
  cnf : SourceValue F
  w_cu : SourceValue F
  ld_ci : loadValue h_ci p_ci = .ok (.construct "KernelTypes::KConstantInfo" "Ctor"
    [w_cnl, cty, w_cblk, w_cind, w_cidx, cnp, cnf, w_cu])
  hcnp : cnp = inp
  hrnf : rnf = cnf
  r_iota : SourceValue F
  h_iota : Heap F
  cs_iota : List (Call F)
  call_iota : (⟨"KernelModeled::check_iota_rule",
    [rc, rm, nl, ty, rp, ni, rhs, cprj, cty, cnp, cnf, ilvls, pins, t, src, dst, aset], h_ci⟩ : Call F)
    ∈ calls
  ev_iota : ObsFn W "KernelModeled::check_iota_rule"
    [rc, rm, nl, ty, rp, ni, rhs, cprj, cty, cnp, cnf, ilvls, pins, t, src, dst, aset]
    h_ci r_iota h_iota cs_iota
  sub_iota : SubCalls calls cs_iota
  inv : CheckIotaRuleInvR rc rm nl ty rp ni rhs cprj cty cnp cnf ilvls pins t src dst aset h_ci calls

/-- **The iterations of `check_rules_go` over a stored rule list**, from rule index `j`, on the
list pointer `rules` at heap `h` and the advice stream `s` holding `bytes`: for each stored rule,
the iteration's record (`RuleStepR`), the rule it reads (`RuleRepExact` at index `j`), and the
advice address `a_t` the stream yields (the bytes' prefix, represented by the read value `t`);
at the end of the list, the loop's output stream and heap. -/
def RuleStepsR (κ : _root_.Address → KKey) (ps : List LevelParam)
    (rc rm nl ty rp ni iblock iidx inp ilvls pins src dst aset : SourceValue F)
    (s_out : SourceValue F) (h' : Heap F) (calls : List (Call F)) :
    Nat → List (RecRule .anon) → SourceValue F → Heap F → List UInt8 → SourceValue F → Prop
  | _, [], _, h, _, s => s_out = s ∧ h' = h
  | j, rl :: rls, rules, h, bytes, s =>
    ∃ (st : RuleStepR rc rm nl ty rp ni iblock iidx inp ilvls pins src dst aset j rules h s calls)
      (a_t : Bytes.Address) (rem : List UInt8),
      RuleRepExact κ h ps j (.construct krrEnum "Mk" [st.w_idx, st.rnf, st.rhs]) rl ∧
      bytes = a_t.toList ++ rem ∧ Bytes.RepAddressRef addrTy st.h_ga a_t st.t ∧
      L1.Stream st.h_ga rem st.s2 ∧ st.cs_ga = [] ∧
      RuleStepsR κ ps rc rm nl ty rp ni iblock iidx inp ilvls pins src dst aset s_out h' calls
        (j + 1) rls st.rest st.h_iota rem st.s2

/-- **`KernelModeled::check_rules_go`, rule by rule**: over a stored rule list (`RulesRepExact`
from index `j`) and an advice stream, an observation of the loop yields one `RuleStepR` per
stored rule, its calls members of any call list containing the loop's. -/
theorem check_rules_go_stepsR {κ : _root_.Address → KKey} {ps : List LevelParam}
    {rc rm nl ty rp ni iblock iidx inp ilvls pins src dst aset s_out : SourceValue F}
    {h' : Heap F} :
    ∀ (rls : List (RecRule .anon)) (j : Nat) {rules s : SourceValue F} {bytes : List UInt8}
      {h : Heap F} {cs calls : List (Call F)},
      SubCalls calls cs →
      RulesRepExact κ h ps j rules rls →
      L1.Stream h bytes s →
      ObsFn W "KernelModeled::check_rules_go"
        [rc, rm, nl, ty, rp, ni, rules, iblock, iidx, inp, ilvls, pins, src, dst, aset, s,
          .field (j : F)]
        h s_out h' cs →
      RuleStepsR κ ps rc rm nl ty rp ni iblock iidx inp ilvls pins src dst aset s_out h' calls
        j rls rules h bytes s := by
  intro rls
  induction rls with
  | nil =>
    intro j rules s bytes h cs calls hsub hrls hstr ev
    match Obs.«KernelModeled::check_rules_go».obs ev with
    | .Nil (he21 := hr) (he22 := hh) .. => exact ⟨hr, hh⟩
    | .Cons (ld12 := ld) .. =>
      cases hrls with
      | nil cell => exact absurd ld (by simp [loadValue_enum_cell cell])
  | cons rl rls ih =>
    intro j rules s bytes h cs calls hsub hrls hstr ev
    match Obs.«KernelModeled::check_rules_go».obs ev with
    | .Nil (ld12 := ld) .. =>
      cases hrls with
      | cons cell _ _ => exact absurd ld (by simp [loadValue_enum_cell cell])
    | .Cons (x_rest := x_rest) (m42 := m42) (cs52 := cs52) (x_t := x_t) (x_s2 := x_s2)
        (v76 := v76) (m77 := m77) (w100 := w100) (x_rnf := x_rnf) (x_rhs := x_rhs)
        (v116 := v_cprj) (m117 := m117) (cs127 := cs127) (m155 := m155) (p163 := p163)
        (cs169 := cs169) (w186 := w186) (x_cty := x_cty) (w187 := w187) (w188 := w188)
        (w189 := w189) (x_cnp := x_cnp) (x_cnf := x_cnf) (w190 := w190) (cs290 := cs290)
        (cs432 := cs432) (v451 := v451)
        (ld12 := ld) (ev54 := ev_ga) (ev129 := ev_cprj) (ev171 := ev_ci) (ld165 := ld_ci)
        (heq258 := heq_cnp) (heq286 := heq_rnf) (ev292 := ev_iota) (op577 := op_j1)
        (ev434 := ev_rec) (hc579 := hc) =>
      subst hc
      -- the call list of the iteration, in order
      have call_ga := hsub.cons_head
      have s1 := hsub.cons_tail.append_right
      have call_cprj := s1.cons_head
      have sub_cprj := s1.cons_tail.append_left
      have s2 := s1.cons_tail.append_right
      have call_ci := s2.cons_head
      have sub_ci := s2.cons_tail.append_left
      have s3 := s2.cons_tail.append_right
      have call_iota := s3.cons_head
      have sub_iota := s3.cons_tail.append_left
      have sub_rec := s3.cons_tail.append_right.cons_tail
      -- the stored rule read
      cases hrls with
      | cons cell hrl_rep hrls_rest =>
        obtain ⟨_, heq_cons⟩ := load_cell cell ld
        injection heq_cons with hmk hrest_eq
        injection hrest_eq with hrest_eq
        rw [hmk] at hrl_rep
        rw [hrest_eq] at hrls_rest
        -- the advice address
        obtain ⟨a_t, rem, x_t', x_s2', hbytes, htup_ga, ha_t, hstr_mid, ext_ga, hcs_ga⟩ :=
          get_address_spec hstr ev_ga
        injection htup_ga with hl; injection hl with h1 hl; injection hl with h2; subst x_t' x_s2'
        -- the rule's inversion
        obtain ⟨inv⟩ := check_iota_rule_invR ev_iota
        -- the next index
        have hj1_eq : v451 = .field ((j + 1 : Nat) : F) := by
          rw [SubstAux.add_ok op_j1, Nat.cast_add, Nat.cast_one]
        rw [hj1_eq] at ev_rec
        have ext_m42_m77 := ev_cprj.heap_extends.trans
          (ev_ci.heap_extends.trans ev_iota.heap_extends)
        have ext_h_m77 := ext_ga.trans ext_m42_m77
        have hrest_out := ih (j + 1) sub_rec (hrls_rest.mono ext_h_m77)
          (hstr_mid.mono ext_m42_m77) ev_rec
        exact ⟨
          { w_idx := w100, rnf := x_rnf, rhs := x_rhs, rest := x_rest, ld_rules := ld,
            t := x_t, s2 := x_s2, h_ga := m42, cs_ga := cs52, call_ga, ev_ga,
            cprj := v_cprj, h_cprj := m117, cs_cprj := cs127, call_cprj, ev_cprj, sub_cprj,
            p_ci := p163, h_ci := m155, cs_ci := cs169, call_ci, ev_ci, sub_ci,
            w_cnl := w186, cty := x_cty, w_cblk := w187, w_cind := w188, w_cidx := w189,
            cnp := x_cnp, cnf := x_cnf, w_cu := w190, ld_ci, hcnp := heq_cnp, hrnf := heq_rnf,
            r_iota := v76, h_iota := m77, cs_iota := cs290, call_iota, ev_iota, sub_iota,
            inv := inv.mono sub_iota },
          a_t, rem, hrl_rep, hbytes, ha_t, hstr_mid, hcs_ga, hrest_out⟩

/-- **`KernelModeled::check_rules`, rule by rule**: the major premise read
(`rec_major_pins(ty, rp, ni) = (iaddr, ilvls, pins)`), the inductive's load (`Induct` with
parameter count `inp`, constructor count `inct`, block `iblock` and index `iidx`), the rule count
(`inct` is the stored rule list's length), and the rule loop from index `0` with one `RuleStepR`
per stored rule. -/
theorem check_rules_stepsR {κ : _root_.Address → KKey} {ps : List LevelParam}
    {rc rm nl ty rp ni rules src dst aset s s_out : SourceValue F} {rls : List (RecRule .anon)}
    {bytes : List UInt8} {h h' : Heap F} {calls : List (Call F)}
    (hbd : IxVM.Consistency.Bounded calls)
    (hrls : RulesRepExact κ h ps 0 rules rls)
    (hstr : L1.Stream h bytes s)
    (ev : ObsFn W "KernelModeled::check_rules" [rc, rm, nl, ty, rp, ni, rules, src, dst, aset, s]
      h s_out h' calls) :
    ∃ (iaddr ilvls pins : SourceValue F) (h_rmp : Heap F) (cs_rmp : List (Call F))
      (p_ind : SourceValue F) (h_ind : Heap F) (cs_ind : List (Call F))
      (w_inl w_ity inp w_ini inct w_iu iblock iidx : SourceValue F),
      (⟨"KernelModeled::rec_major_pins", [ty, rp, ni], h⟩ : Call F) ∈ calls ∧
      ObsFn W "KernelModeled::rec_major_pins" [ty, rp, ni] h (.tuple [iaddr, ilvls, pins])
        h_rmp cs_rmp ∧
      SubCalls calls cs_rmp ∧
      (⟨"Ingress::get_ci", [iaddr], h_rmp⟩ : Call F) ∈ calls ∧
      ObsFn W "Ingress::get_ci" [iaddr] h_rmp p_ind h_ind cs_ind ∧
      SubCalls calls cs_ind ∧
      loadValue h_ind p_ind = .ok (.construct "KernelTypes::KConstantInfo" "Induct"
        [w_inl, w_ity, inp, w_ini, inct, w_iu, iblock, iidx]) ∧
      inct = .field (rls.length : F) ∧ rls.length < 2 ^ 39 ∧
      (⟨"KernelModeled::check_rules_go",
        [rc, rm, nl, ty, rp, ni, rules, iblock, iidx, inp, ilvls, pins, src, dst, aset, s,
          .field 0], h_ind⟩ : Call F) ∈ calls ∧
      RuleStepsR κ ps rc rm nl ty rp ni iblock iidx inp ilvls pins src dst aset s_out h' calls
        0 rls rules h_ind bytes s := by
  have hsub : SubCalls calls calls := SubCalls.refl calls
  match Obs.«KernelModeled::check_rules».obs ev with
  | .run (m2 := m2) (cs12 := cs12) (x_iaddr := x_iaddr) (x_ilvls := x_ilvls)
      (x_pins := x_pins) (m58 := m58) (p66 := p66) (cs72 := cs72)
      (w89 := w89) (w90 := w90) (x_inp := x_inp) (w91 := w91) (x_inct := x_inct) (w92 := w92)
      (x_iblock := x_iblock) (x_iidx := x_iidx)
      (v144 := v144) (m147 := m147) (cs155 := cs155) (cs177 := cs177)
      (ev14 := ev_rmp) (ev74 := ev_ci) (ld68 := ld_ci) (ev157 := ev_rlen)
      (heq173 := heq_inct) (ev179 := ev_go) (hc315 := hc) .. =>
    subst hc
    have call_rmp := hsub.cons_head
    have sub_rmp := hsub.cons_tail.append_left
    have s1 := hsub.cons_tail.append_right
    have call_ci := s1.cons_head
    have sub_ci := s1.cons_tail.append_left
    have s2 := s1.cons_tail.append_right
    have call_rlen := s2.cons_head
    have s3 := s2.cons_tail.append_right
    have call_go := s3.cons_head
    have sub_go := s3.cons_tail
    have ext_rmp_ci := ev_rmp.heap_extends.trans ev_ci.heap_extends
    obtain ⟨hrlen_f, hrlen_lt, hm147_eq⟩ :=
      rulesRepExact_length hbd call_rlen ev_rlen (hrls.mono ext_rmp_ci)
    subst m147
    have ev_go' := ev_go
    rw [show (.field 0 : SourceValue F) = .field ((0 : Nat) : F) by simp] at ev_go'
    have hsteps := check_rules_go_stepsR rls 0 sub_go (hrls.mono ext_rmp_ci)
      (hstr.mono ext_rmp_ci) ev_go'
    exact ⟨x_iaddr, x_ilvls, x_pins, m2, cs12, p66, m58, cs72,
      w89, w90, x_inp, w91, x_inct, w92, x_iblock, x_iidx,
      call_rmp, ev_rmp, sub_rmp, call_ci, ev_ci, sub_ci, ld_ci,
      heq_inct.symm.trans hrlen_f, hrlen_lt, call_go, hsteps⟩

end IxVM.Refinement.Decl
