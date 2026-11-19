import IxVMRefinement.Binding.FamilyFlatObs
import IxVMRefinement.Claim.TopProj
import IxVMRefinement.Obs.KernelCheck4
import IxVMRefinement.Obs.KernelCheck5
import IxVMRefinement.Obs.KernelCheck9
import IxVMRefinement.Obs.KernelCheck10
import IxVMRefinement.Obs.KernelCheck11
import IxVMRefinement.Obs.KernelCheck12

/-! # Reconstruction builders on `TmOExact`

Refines the circuit's recursor-type and recursor-rule builders against `FamilyReconModel` over
`ReconView.ofStore t E₀` on `TmOExact` and `FlatEntryRepExact`:

* List-operation wrappers (`kexpr_{drop,reverse,concat,lookup}_spec`, `field_{length,lookup_or_default}_spec`,
  `addr_lookup_or_default_spec`), ROM-bounded leading-binder count (`peelAll_length_le_of_bounded`),
  and pure length/range invariants on `fieldsClassify` (`fieldsClassify_lengths_and_bounds`);
* Elementary term/level/address builders (`build_rec_lvls_list_spec`, `list_lift_each_spec`,
  `build_major_args_for_member_spec`, `build_major_args_for_self_spec`,
  `build_ctor_app_params_spec`, `projection_addr_ctor_exact`);
* Flat-list queries and peer recursor resolution (`build_flat_own_params_spec`,
  `ctors_before_pos_spec`, `flatPeerDistinct_of_buildFlatAuxStep`, `build_peer_recs_spec` proving
  `peers = recAddrs rb rs` unconditionally under `UsedClosed R` + `RecordFlatAux`);
* Minor premises, motives, and the full reconstructed recursor type (`build_ih_doms_spec`,
  `build_minor_at_depth_spec`, `build_minor_doms_spec`, `build_all_minors_spec`,
  `build_motive_type_flat_spec`, `build_all_motives_spec`, `build_rec_type_from_spec`,
  `build_rec_type_spec`);
* Reconstructed recursor rule bodies (`apply_ihs_full_spec`, `build_rule_rhs_spec`,
  `populate_rules_spec`). -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency
open IxVM.Refinement.Binding.FamilyFlat
open IxVM.Refinement.Core (W KExpr KLevel KKey bmeta kexprEnum kexprListEnum kciEnum
  addrTy addrListEnum ixAddr)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList klevelEnum klevelListEnum)

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Section 1: Generic list wrappers, ROM `peelAll` bound, and `fieldsClassify` bounds -/

private abbrev fieldTyG : Generic.Ty := .field

private abbrev addrTyG : Generic.Ty :=
  .ptr (.array .field 32)

private abbrev kexprTyG : Generic.Ty :=
  .ptr (.named "KernelTypes::KExprNode" [])

theorem kexpr_drop_spec {R : Heap F → KExpr → SourceValue F → Prop} {xs : List KExpr}
    {l r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [l, .field n] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) :
    n.val ≤ xs.length ∧ RepList kexprListEnum R h (xs.drop n.val) r ∧ h' = h := by
  rw [← Obs.Names.«Lists::drop<&KernelTypes::KExprNode>».symbol] at ev
  change RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» R h xs l at hl
  rw [← Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hl
  have ⟨h1, h2, h3⟩ := Lib.Lists.drop_spec (t := kexprTyG) n.val rfl ev hl
  rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at h2
  exact ⟨h1, h2, h3⟩

theorem kexpr_reverse_spec {R : Heap F → KExpr → SourceValue F → Prop} (hR : HeapMono₂ R)
    {xs : List KExpr} {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::reverse<&KernelTypes::KExprNode>» [l] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) :
    RepList kexprListEnum R h' xs.reverse r := by
  rw [← Obs.Names.«Lists::reverse<&KernelTypes::KExprNode>».symbol] at ev
  change RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» R h xs l at hl
  rw [← Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hl
  have hr := Lib.Lists.reverse_spec (t := kexprTyG) hR ev hl
  rwa [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hr

theorem kexpr_unit_reverse_spec {xs : List Unit} {l r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::reverse<&KernelTypes::KExprNode>» [l] h r h' cs)
    (hl : RepList kexprListEnum (fun _ (_ : Unit) _ => True) h xs l) :
    RepList kexprListEnum (fun _ (_ : Unit) _ => True) h' xs.reverse r := by
  rw [← Obs.Names.«Lists::reverse<&KernelTypes::KExprNode>».symbol] at ev
  change RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» _ h xs l at hl
  rw [← Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hl
  have hr := Lib.Lists.reverse_spec (t := kexprTyG) (R := fun _ (_ : Unit) _ => True)
    (fun _ _ _ _ _ t => t) ev hl
  rwa [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hr

theorem kexpr_concat_spec {R : Heap F → KExpr → SourceValue F → Prop} (hR : HeapMono₂ R)
    {xs ys : List KExpr} {a b r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::concat<&KernelTypes::KExprNode>» [a, b] h r h' cs)
    (ha : RepList kexprListEnum R h xs a) (hb : RepList kexprListEnum R h ys b) :
    RepList kexprListEnum R h' (xs ++ ys) r := by
  rw [← Obs.Names.«Lists::concat<&KernelTypes::KExprNode>».symbol] at ev
  change RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» R h xs a at ha
  change RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» R h ys b at hb
  rw [← Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at ha hb
  have hr := Lib.Lists.concat_spec (t := kexprTyG) hR ev ha hb
  rwa [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hr

theorem kexpr_unit_concat_spec {xs ys : List Unit} {a b r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::concat<&KernelTypes::KExprNode>» [a, b] h r h' cs)
    (ha : RepList kexprListEnum (fun _ (_ : Unit) _ => True) h xs a)
    (hb : RepList kexprListEnum (fun _ (_ : Unit) _ => True) h ys b) :
    RepList kexprListEnum (fun _ (_ : Unit) _ => True) h' (xs ++ ys) r := by
  rw [← Obs.Names.«Lists::concat<&KernelTypes::KExprNode>».symbol] at ev
  change RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» _ h xs a at ha
  change RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» _ h ys b at hb
  rw [← Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at ha hb
  have hr := Lib.Lists.concat_spec (t := kexprTyG) (R := fun _ (_ : Unit) _ => True)
    (fun _ _ _ _ _ t => t) ev ha hb
  rwa [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hr

theorem kexpr_lookup_spec {R : Heap F → KExpr → SourceValue F → Prop} {xs : List KExpr}
    {l r : SourceValue F} {i : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>» [l, .field i] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) :
    (∃ x, xs[i.val]? = some x ∧ R h x r) ∧ h' = h := by
  rw [← Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>».symbol] at ev
  change RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» R h xs l at hl
  rw [← Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hl
  exact Lib.Lists.lookup_spec (t := kexprTyG) ev hl

theorem field_length_spec {R : Heap F → Nat → SourceValue F → Prop} {xs : List Nat}
    {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<Field>» [l] h r h' cs)
    (hl : RepList fieldListEnum R h xs l) :
    r = .field (xs.length : F) ∧ h' = h := by
  rw [← Obs.Names.«Lists::length<Field>».symbol] at ev
  change RepList Obs.Names.«Lists::Node<Field>» R h xs l at hl
  rw [← Obs.Names.«Lists::Node<Field>».symbol] at hl
  exact Lib.Lists.length_spec (t := fieldTyG) ev hl

theorem field_lookup_or_default_spec {xs : List Nat} {l r dflt : SourceValue F} {i : F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::lookup_or_default<Field>» [l, .field i, dflt] h r h' cs)
    (hl : RepList fieldListEnum RepNatField h xs l) :
    h' = h ∧ ((∃ x, xs[i.val]? = some x ∧ r = .field (x : F)) ∨ (i.val = xs.length ∧ r = dflt)) := by
  rw [← Obs.Names.«Lists::lookup_or_default<Field>».symbol] at ev
  change RepList Obs.Names.«Lists::Node<Field>» RepNatField h xs l at hl
  rw [← Obs.Names.«Lists::Node<Field>».symbol] at hl
  exact Lib.Lists.lookup_or_default_spec (t := fieldTyG) ev hl

theorem addr_lookup_or_default_spec {xs : List Bytes.Address} {l r dflt : SourceValue F} {i : F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::lookup_or_default<&[Field; 32]>» [l, .field i, dflt] h r h' cs)
    (hl : RepList addrListEnum (Bytes.RepAddressRef addrTy) h xs l) :
    h' = h ∧ ((∃ x, xs[i.val]? = some x ∧ Bytes.RepAddressRef addrTy h x r) ∨
      (i.val = xs.length ∧ r = dflt)) := by
  rw [← Obs.Names.«Lists::lookup_or_default<&[Field; 32]>».symbol] at ev
  change RepList Obs.Names.«Lists::Node<&[Field; 32]>» (Bytes.RepAddressRef addrTy) h xs l at hl
  rw [← Obs.Names.«Lists::Node<&[Field; 32]>».symbol] at hl
  exact Lib.Lists.lookup_or_default_spec (t := addrTyG) ev hl

private theorem repList_length_lt_obs {en : String} {α : Type*}
    {R : Heap F → α → SourceValue F → Prop} {xs : List α} {p : SourceValue F}
    {nm : String} {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    {cs cs' rootCalls : List (Call F)}
    (hbd : Bounded rootCalls) (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    (_ev : ObsFn W nm args h r h' cs')
    (hmem : (⟨nm, args, h⟩ : Call F) ∈ cs) (hp : p ∈ args)
    (hrep : RepList en R h xs p) : xs.length < 2 ^ 39 :=
  RomBound.bounded_length_lt hbd (hsub ⟨nm, args, h⟩ hmem) hp hrep

private theorem represents_ptr_inv_b {rom : ROM F} {h : Heap F} {t : Aiur.Ty} {loc : Nat}
    {w : Value F} (r : Represents rom h (.ptr t loc) w) :
    ∃ stored address encoded, h[loc]? = some stored ∧ (address, encoded) ∈ rom.entries ∧
      Represents rom h stored encoded ∧ w = .ptr encoded.type address := by
  generalize hv : (Value.ptr t loc : SourceValue F) = v at r
  cases r with
  | ptr hs hmem hrep =>
    injection hv with _ h2; subst h2
    exact ⟨_, _, _, hs, hmem, hrep, rfl⟩
  | field => cases hv
  | tuple _ => cases hv
  | construct _ => cases hv

private theorem represents_construct_inv_b {rom : ROM F} {h : Heap F} {en tag : String}
    {args : List (SourceValue F)} {w : Value F} (r : Represents rom h (.construct en tag args) w) :
    ∃ encArgs, w = .construct en tag encArgs ∧ List.Forall₂ (Represents rom h) args encArgs := by
  generalize hv : (Value.construct en tag args : SourceValue F) = v at r
  cases r with
  | construct items =>
    injection hv with h1 h2 h3; subst h1 h2 h3
    exact ⟨_, rfl, items⟩
  | field => cases hv
  | tuple _ => cases hv
  | ptr _ _ _ => cases hv

private theorem peelAll_length_le_count_aux {rom : ROM F} {κ : _root_.Address → KKey}
    {rootCalls : List (Call F)}
    (hvalid : rom.Valid) (hbound : ROMAddressesAtMost rom (2 ^ 39))
    (hcar : ∀ c ∈ rootCalls, ∀ v ∈ c.args, ∃ w, Represents rom c.heap v w)
    {E : KExpr} {xty xacc r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::count_foralls_body" [xty, xacc] h r h' cs)
    (hmem : (⟨"KernelCheck::count_foralls_body", [xty, xacc], h⟩ : Call F) ∈ rootCalls)
    (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    (hE : TmOExact κ h E xty)
    (seen : List (F × Nat))
    (hnodup : (seen.map Prod.fst).Nodup)
    (hrom : ∀ p ∈ seen, ∃ v, (p.1, v) ∈ rom.entries)
    (hsz : ∀ p ∈ seen, ∀ (h_x : Heap F) (E_x : KExpr) (px : SourceValue F),
      Represents rom h_x px (.ptr (.enum kexprEnum) p.1) →
      TmOExact κ h_x E_x px → exprSize E_x = p.2)
    (hlt : ∀ p ∈ seen, exprSize E < p.2) :
    (peelAll E).1.length + seen.length ≤ 2 ^ 39 := by
  have hbd_cs : Bounded cs := ⟨rom, hvalid, hbound, fun c hc => hcar c (hsub c hc)⟩
  match Obs.«KernelCheck::count_foralls_body».obs ev with
  | .Forall (x_body := xbody) (cs40 := cs1) (v44 := v1) (ld12 := ld)
      (ev42 := e1) (hc67 := hc) .. =>
    obtain ⟨D, B, ℓ, rfl, -, hB, -⟩ := TmOExact.forallE_of_load hE ld
    obtain ⟨w, hrep⟩ := hcar _ hmem xty (by simp)
    cases xty with
    | ptr ty loc =>
      simp only [loadValue] at ld
      cases hget : h[loc]? with
      | none => rw [hget] at ld; cases ld
      | some stored =>
        by_cases hty_ne : Value.type stored ≠ ty
        · simp [loadValue, hget, hty_ne] at ld
        · simp only [loadValue, hget, hty_ne, ↓reduceIte, pure, Except.pure, bind, Except.bind,
            Except.ok.injEq] at ld
          obtain ⟨w1, w2, hst⟩ : ∃ w1 w2, stored = .construct kexprEnum "Forall" [w1, xbody, w2] :=
            ⟨_, _, ld.symm⟩
          obtain ⟨s, addr, enc, hs, hmem_r, hrep_c, rfl⟩ := represents_ptr_inv_b hrep
          rw [hget] at hs; cases hs
          rw [hst] at hrep_c
          obtain ⟨ws, henc, -⟩ := represents_construct_inv_b hrep_c
          have hty_enc : enc.type = .enum kexprEnum := by rw [henc]; simp [Value.type]
          rw [hty_enc] at hrep
          have hnotmem : addr ∉ seen.map Prod.fst := by
            intro hin
            obtain ⟨p, hp, hpeq⟩ := List.mem_map.mp hin
            have heq := hsz p hp h (.forallE D B (bmeta ℓ)) (.ptr ty loc)
              (by rw [hpeq]; exact hrep) hE
            have := hlt p hp
            omega
          have hltB : exprSize B < exprSize (.forallE D B (bmeta ℓ)) := by simp [exprSize]
          have hlt_cs : cs1.length < cs.length := by rw [hc]; simp
          have hrec := peelAll_length_le_count_aux hvalid hbound hcar e1
            (hsub _ (by rw [hc]; simp)) (fun c hc' => hsub c (by rw [hc]; simp [hc']))
            hB ((addr, exprSize (.forallE D B (bmeta ℓ))) :: seen)
            (by simp [List.nodup_cons, hnotmem, hnodup])
            (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp
              · exact ⟨enc, hmem_r⟩
              · exact hrom p hp)
            (fun p hp h_x E_x px hrx hEx => by
              rcases List.mem_cons.mp hp with rfl | hp
              · exact exprSize_eq_of_represents hvalid hrx hrep hEx hE
              · exact hsz p hp h_x E_x px hrx hEx)
            (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp
              · exact hltB
              · exact Nat.lt_trans hltB (hlt p hp))
          simp only [peelAll, List.length_cons] at hrec ⊢
          omega
    | _ => simp [loadValue] at ld
  | .Let (x_v := xv) (x_b := xb) (v_qjjhbakm := v') (m_fhppzpwh := m')
      (cs_yqrxeseo := cs1) (cs_fsonrmiw := cs2) (ld12 := ld) (ev_gemvpjgn := e1)
      (ev_krdhokor := e2) (hc_qubwlzze := hc) .. =>
    obtain ⟨T, V, B, rfl, -, hv, hb⟩ := TmOExact.letE_of_load hE ld
    have b1 : Bounded cs1 := RomBound.bounded_mono hbd_cs (fun c hc' => by rw [hc]; simp [hc'])
    have hv' := expr_inst1_tmOExact b1 hb hv e1
    have hlt_cs : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    exact peelAll_length_le_count_aux hvalid hbound hcar e2
      (hsub _ (by rw [hc]; simp)) (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      hv' seen hnodup hrom hsz hlt
  | .other (ld12 := ld) (hne68 := hnf) (hne_ttotnwna := hnl) .. =>
    have hp := peelAll_of_not_forall_not_let hE ld hnf hnl
    rw [hp]
    have hle := RomBound.length_le_of_nodup hbound hnodup (fun a ha => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      exact hrom p hp)
    simpa using hle
termination_by cs.length

/-- Every `TmOExact` term passed to `count_foralls_body` inside a `Bounded` trace has at most
`2 ^ 39` leading `Forall` binders. -/
theorem peelAll_length_le_of_count_foralls {κ : _root_.Address → KKey} {E : KExpr}
    {xty xacc r : SourceValue F} {h h' : Heap F} {cs cs_outer rootCalls : List (Call F)}
    (hbd : Bounded rootCalls) (hsub_o : ∀ c ∈ cs_outer, c ∈ rootCalls)
    (ev : ObsFn W "KernelCheck::count_foralls_body" [xty, xacc] h r h' cs)
    (hmem : (⟨"KernelCheck::count_foralls_body", [xty, xacc], h⟩ : Call F) ∈ cs_outer)
    (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    (hE : TmOExact κ h E xty) : (peelAll E).1.length ≤ 2 ^ 39 := by
  obtain ⟨rom, hvalid, hbound, hcar⟩ := hbd
  have h1 := peelAll_length_le_count_aux hvalid hbound hcar ev (hsub_o _ hmem) hsub hE []
    List.nodup_nil (fun _ hm => nomatch hm) (fun _ hm => nomatch hm) (fun _ hm => nomatch hm)
  simpa using h1

/-- **`walk_fields_classify`** always produces a domain list whose length equals
`acc.length + (peelAll E).1.length` (no arithmetic bound needed). -/
theorem walk_fields_classify_doms_len {κ : _root_.Address → KKey} {E : KExpr}
    {acc : List Unit}
    {xrc xty xflat xdoms xrec xrecmem xnorm xfidx xlb xtys r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::walk_fields_classify"
      [xrc, xty, xflat, xdoms, xrec, xrecmem, xnorm, xfidx, xlb, xtys] h r h' cs)
    (hbnd : Bounded cs) (hE : TmOExact κ h E xty)
    (hdoms : RepList kexprListEnum (fun _ (_ : Unit) _ => True) h acc xdoms) :
    ∃ (xds xri xrm xret xns : SourceValue F) (ds : List Unit),
      r = .tuple [xds, xri, xrm, xret, xns] ∧
      ds.length = acc.length + (peelAll E).1.length ∧
      RepList kexprListEnum (fun _ (_ : Unit) _ => True) h' ds xds := by
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → Bounded cs' :=
    fun hs => RomBound.bounded_mono hbnd hs
  match Obs.«KernelCheck::walk_fields_classify».obsx ev with
  | .Forall_n1_bind (x_dom := xdom) (x_body := xbody) (m37 := m1) (m75 := m2)
      (m122 := m3) (m153 := m4) (m184 := m5) (m243 := m6) (m274 := m7) (cs307 := cs3)
      (ld12 := ld) (ev49 := evw) (ev87 := evrecf)
      (hm132 := hm3) (hm163 := hm4) (hm194 := hm5) (hm253 := hm6) (hm284 := hm7)
      (ev309 := evnext) (hc398 := hc) .. =>
    subst hm3 hm4 hm5 hm6 hm7
    obtain ⟨D, B, ℓ, rfl, -, hB, -⟩ := TmOExact.forallE_of_load hE ld
    have ext12 := evw.heap_extends.trans evrecf.heap_extends
    have ext3 : Heap.Extends m2 (m2 ++ [.construct kexprListEnum "Cons" [xdom, xdoms]]) :=
      Heap.Extends.snoc _ _
    have ext37 : Heap.Extends (m2 ++ [.construct kexprListEnum "Cons" [xdom, xdoms]]) m7 :=
      (Heap.Extends.snoc _ _).trans ((Heap.Extends.snoc _ _).trans
        ((Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)))
    have hdoms' : RepList kexprListEnum (fun _ (_ : Unit) _ => True) m7 (() :: acc)
        (.ptr (.enum kexprListEnum) m2.length) :=
      repList_heapMono₂ kexprListEnum (fun _ _ _ _ _ t => t) ext37
        (Lib.rep_store_cons (fun _ _ _ _ _ t => t) trivial
          (repList_heapMono₂ kexprListEnum (fun _ _ _ _ _ t => t) ext12 hdoms))
    have hlt : cs3.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨xds, xri, xrm, xret, xns, ds, hr, hlen, hrep⟩ :=
      walk_fields_classify_doms_len evnext (sub fun c hc' => by rw [hc]; simp [hc'])
        (hB.mono (ext12.trans (ext3.trans ext37))) hdoms'
    refine ⟨xds, xri, xrm, xret, xns, ds, hr, ?_, hrep⟩
    simp only [peelAll, List.length_cons] at hlen ⊢; omega
  | .Forall_other (x_dom := xdom) (x_body := xbody) (m37 := m1) (m75 := m2)
      (m122 := m3) (m153 := m4) (m184 := m5) (cs405 := cs3)
      (ld12 := ld) (ev49 := evw) (ev87 := evrecf)
      (hm132 := hm3) (hm163 := hm4) (hm194 := hm5)
      (ev407 := evnext) (hc496 := hc) .. =>
    subst hm3 hm4 hm5
    obtain ⟨D, B, ℓ, rfl, -, hB, -⟩ := TmOExact.forallE_of_load hE ld
    have ext12 := evw.heap_extends.trans evrecf.heap_extends
    have ext3 : Heap.Extends m2 (m2 ++ [.construct kexprListEnum "Cons" [xdom, xdoms]]) :=
      Heap.Extends.snoc _ _
    have ext35 : Heap.Extends (m2 ++ [.construct kexprListEnum "Cons" [xdom, xdoms]]) m5 :=
      (Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)
    have hdoms' : RepList kexprListEnum (fun _ (_ : Unit) _ => True) m5 (() :: acc)
        (.ptr (.enum kexprListEnum) m2.length) :=
      repList_heapMono₂ kexprListEnum (fun _ _ _ _ _ t => t) ext35
        (Lib.rep_store_cons (fun _ _ _ _ _ t => t) trivial
          (repList_heapMono₂ kexprListEnum (fun _ _ _ _ _ t => t) ext12 hdoms))
    have hlt : cs3.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨xds, xri, xrm, xret, xns, ds, hr, hlen, hrep⟩ :=
      walk_fields_classify_doms_len evnext (sub fun c hc' => by rw [hc]; simp [hc'])
        (hB.mono (ext12.trans (ext3.trans ext35))) hdoms'
    refine ⟨xds, xri, xrm, xret, xns, ds, hr, ?_, hrep⟩
    simp only [peelAll, List.length_cons] at hlen ⊢; omega
  | .Let (cs_wgevuyab := cs2) (ld12 := ld)
      (ev_gfkycmwo := e1) (ev_wojvmxdy := e2) (hc_qubwlzze := hc) .. =>
    obtain ⟨T, V0, B, rfl, -, hv, hb⟩ := TmOExact.letE_of_load hE ld
    have hv' := expr_inst1_tmOExact (sub fun c hc' => by rw [hc]; simp [hc']) hb hv e1
    have hlt : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    exact walk_fields_classify_doms_len e2 (sub fun c hc' => by rw [hc]; simp [hc']) hv'
      (repList_heapMono₂ kexprListEnum (fun _ _ _ _ _ t => t) e1.heap_extends hdoms)
  | .other (v503 := xds) (v504 := xri) (v505 := xrm) (v507 := xns)
      (ld12 := ld) (hne497 := hnf) (hne_ttotnwna := hnl) (he508 := hr)
      (ev520 := evr1) (ev540 := evr2) (ev560 := evr3) (ev587 := evr4) (he596 := hh) .. =>
    subst hr hh
    have hp := peelAll_of_not_forall_not_let hE ld hnf hnl
    have hrev := kexpr_unit_reverse_spec evr1 hdoms
    have ext := evr2.heap_extends.trans (evr3.heap_extends.trans evr4.heap_extends)
    refine ⟨xds, xri, xrm, xty, xns, acc.reverse, rfl, by simp [hp],
      repList_heapMono₂ kexprListEnum (fun _ _ _ _ _ t => t) ext hrev⟩
termination_by cs.length

theorem addrIn_substParamFor {S : _root_.Address → Prop} {κ : _root_.Address → KKey}
    {j nrp : Nat} {aux : Bool} {sp : List KExpr} (hsp : ∀ e ∈ sp, AddrIn S κ e) :
    AddrIn S κ (substParamFor j nrp aux sp) := by
  unfold substParamFor
  cases aux
  · trivial
  · cases h : sp[j]? with
    | none => trivial
    | some s => exact hsp s (List.mem_of_getElem? h)

theorem addrIn_peelMotiveParams {S : _root_.Address → Prop} {κ : _root_.Address → KKey}
    {nrp : Nat} {aux : Bool} {sp : List KExpr} (hsp : ∀ e ∈ sp, AddrIn S κ e) :
    ∀ (n j : Nat) (E E' : KExpr),
      peelMotiveParams nrp aux sp n j E = some E' → AddrIn S κ E → AddrIn S κ E' := by
  intro n
  induction n with
  | zero =>
    intro j E E' h hE
    simp only [peelMotiveParams, Option.some.injEq] at h
    exact h ▸ hE
  | succ n ih =>
    intro j E E' h hE
    simp only [peelMotiveParams] at h
    cases E with
    | forallE d b m =>
      simp only [isForall] at h
      exact ih (j + 1) _ E' h (addrIn_instantiate1Lift (addrIn_substParamFor hsp) hE.2)
    | _ => simp [isForall] at h

/-- **Parameter-count coherence for a `FlatEntry`**: original members have at most `nrp`
parameters, auxiliary members supply at least their own inductive's parameters in `e.params`, and
every constructor of the member agrees with its inductive's parameter count. -/
def FlatEntryParamsOk (V : ReconView) (nrp : Nat) (e : FlatEntry) : Prop :=
  ∀ d, V.ind e.addr = some (some d) →
    (e.aux = false → d.np ≤ nrp) ∧
    (e.aux = true → d.np ≤ e.params.length) ∧
    (∀ c cty cnp, V.ctor d.blk d.idx c = some (cty, cnp) → cnp = d.np)

/-- Pure length and index bounds on `fieldsClassify`: `ns.length = ds.length`, `rm.length = ri.length`,
every recorded field index lies in `[fidx, fidx + ds.length)`, and every recorded member index is
`< es.length`. -/
theorem fieldsClassify_lengths_and_bounds {V : ReconView} {f : Nat} {es : List FlatEntry}
    {liftBy : Nat} :
    ∀ (E : KExpr) (fidx : Nat) (ds ns : List KExpr) (ri rm : List Nat) (ret : KExpr),
      fieldsClassify V f es liftBy fidx E = some (ds, ri, rm, ret, ns) →
      ns.length = ds.length ∧ rm.length = ri.length ∧
      (∀ fi ∈ ri, fidx ≤ fi ∧ fi < fidx + ds.length) ∧
      (∀ m ∈ rm, m < es.length) := by
  intro E
  induction E with
  | forallE d b m ihD ihB =>
    intro fidx ds ns ri rm ret h
    simp only [fieldsClassify] at h
    cases hw : whnfTele V f f d with
    | none => simp [hw] at h
    | some nd =>
      simp only [hw] at h
      cases hr : fieldsClassify V f es liftBy (fidx + 1) b with
      | none => simp [hr] at h
      | some res =>
        rcases res with ⟨ds', ri', rm', ret', ns'⟩
        simp only [hr] at h
        obtain ⟨hns, hrm, hri, hrmb⟩ := ihB (fidx + 1) ds' ns' ri' rm' ret' hr
        cases his : isRecField V es (liftBy + fidx) nd with
        | none =>
          simp only [his, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
          refine ⟨by simp [hns], hrm, ?_, hrmb⟩
          intro fi hfi
          have ⟨h1, h2⟩ := hri fi hfi
          simp only [List.length_cons]; omega
        | some memIdx =>
          simp only [his, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
          have hmem_lt : memIdx < es.length := by
            unfold isRecField at his
            cases hfn : (peelAll nd).2.getAppFn <;> simp [hfn] at his
            case const k us =>
              cases hka : V.addr k with
              | none => simp [hka] at his
              | some a =>
                simp only [hka, flatFindMatching] at his
                exact (List.findIdx?_eq_some_iff_findIdx_eq.mp his).1
          refine ⟨by simp [hns], by simp [hrm], ?_, ?_⟩
          · intro fi hfi
            rcases List.mem_cons.mp hfi with rfl | hfi
            · simp only [List.length_cons]; omega
            · have ⟨h1, h2⟩ := hri fi hfi
              simp only [List.length_cons]; omega
          · intro m hm
            rcases List.mem_cons.mp hm with rfl | hm
            · exact hmem_lt
            · exact hrmb m hm
  | _ =>
    intro fidx ds ns ri rm ret h
    simp only [fieldsClassify, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, (fun _ hm => nomatch hm), (fun _ hm => nomatch hm)⟩

/-! ## Section 2: Elementary term, level, and constructor-address builders -/

/-- **`KernelCheck::build_rec_lvls_list`** builds `((List.range total).drop i).map KLevel.param`. -/
theorem build_rec_lvls_list_spec (total : Nat) (ht : total < 4294967296) :
    ∀ (rem i : Nat), i + rem = total →
      ∀ {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        ObsFn W "KernelCheck::build_rec_lvls_list" [.field (total : F), .field (i : F)] h r h' cs →
        RepKLevelList h' (((List.range total).drop i).map Ix.Kernel.Level.param) r := by
  intro rem
  induction rem with
  | zero =>
    intro i hi r h h' cs ev
    match Obs.«KernelCheck::build_rec_lvls_list».obs ev with
    | .n0 (he28 := hr0) (hm27 := hm0) .. =>
      cases hr0; cases hm0
      have hdrop : (List.range total).drop i = [] := List.drop_eq_nil_of_le (by rw [List.length_range]; omega)
      rw [hdrop, List.map_nil]
      have hrep := (RepKLevelList.allocNil h).1
      rwa [IxVM.Refinement.Levels.klevelList_names] at hrep
    | .other (op17 := op) (hne33 := hne) .. =>
      have : i = total := by omega
      subst this
      simp only [evalBinOp, sub_self, Except.ok.injEq] at op
      exact (hne op.symm).elim
  | succ rem ih =>
    intro i hi r h h' cs ev
    match Obs.«KernelCheck::build_rec_lvls_list».obs ev with
    | .n0 (op17 := op) .. =>
      have := binop_sub_eq_zero_nat (by omega) (by omega) op
      omega
    | .other (v46 := vrest) (m48 := m1) (m69 := m2) (v81 := vi1)
        (he41 := hr0) (hm40 := hm0) (hm56 := hm1) (op102 := op1) (ev79 := evrec) .. =>
      cases hr0; cases hm0; cases hm1
      obtain rfl := binop_add_one_nat op1
      have hrec := ih (i + 1) (by omega) evrec
      have hdrop : (List.range total).drop i = i :: (List.range total).drop (i + 1) := by
        have hlt : i < (List.range total).length := by simp; omega
        rw [List.drop_eq_getElem_cons hlt]; simp
      rw [hdrop, List.map_cons]
      have ext1 : Heap.Extends h (h ++ [.construct klevelEnum "Param" [.field (i : F)]]) :=
        Heap.Extends.snoc _ _
      have hp : RepKLevel m2 (.param i) (.ptr (.enum klevelEnum) h.length) :=
        (RepKLevel.param (by omega) (by simp)).mono evrec.heap_extends
      have hrep := (RepKLevelList.allocCons hp hrec).1
      rwa [IxVM.Refinement.Levels.klevelList_names] at hrep

/-- **`KernelCheck::list_lift_each`** lifts every element of a `TmOExact` list by `shift` at
cutoff `cut`, preserving `AddrIn S κ`. -/
theorem list_lift_each_spec {S : _root_.Address → Prop} {κ : _root_.Address → KKey}
    {shift cut : Nat} (hs : shift < 4611686018427387904) (hc : cut < 4611686018427387904) :
    ∀ (es : List KExpr) {xes r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelCheck::list_lift_each" [xes, .field (shift : F), .field (cut : F)] h r h' cs →
      Bounded cs →
      RepList kexprListEnum (TmOExact κ) h es xes →
      (∀ e ∈ es, AddrIn S κ e) →
      RepList kexprListEnum (TmOExact κ) h' (es.map fun e => e.liftLooseBVars shift cut) r ∧
      (∀ e ∈ es.map (fun e => e.liftLooseBVars shift cut), AddrIn S κ e) := by
  intro es
  induction es with
  | nil =>
    intro xes r h h' cs ev _ hes _
    match Obs.«KernelCheck::list_lift_each».obs ev with
    | .Nil (he24 := hr0) (hm23 := hm0) .. =>
      cases hr0; cases hm0
      exact ⟨Lib.rep_store_nil h, fun _ hm => nomatch hm⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hcons
  | cons e rest ih =>
    intro xes r h h' cs ev hbnd hes hIn
    match Obs.«KernelCheck::list_lift_each».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    | .Cons (x_e := xe) (x_rest := xrest) (v54 := ve') (v55 := vrest') (m57 := m1)
        (cs65 := cs1) (m93 := m2) (cs101 := cs2)
        (ld12 := ld) (he50 := hr0) (hm49 := hm0) (ev67 := evl) (ev103 := evrec) (hc128 := hcs) .. =>
      cases hr0; cases hm0
      obtain ⟨e', rest', h1, he, hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with h1e h1r; subst h1e h1r
      have bnd1 : Bounded cs1 := RomBound.bounded_mono hbnd (fun c hc' => by rw [hcs]; simp [hc'])
      have bnd2 : Bounded cs2 := RomBound.bounded_mono hbnd (fun c hc' => by rw [hcs]; simp [hc'])
      have hl := expr_lift_tmOExact hs hc bnd1 he evl
      obtain ⟨hrep_rest, hrestIn⟩ := ih evrec bnd2
        (tmOExactList_mono evl.heap_extends hrest) (fun y hy => hIn y (List.mem_cons_of_mem _ hy))
      refine ⟨Lib.rep_store_cons tmOExact_heapMono₂ (hl.mono evrec.heap_extends) hrep_rest, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hm
      · exact addrIn_liftLooseBVars shift (hIn e (List.mem_cons_self ..))
      · exact hrestIn y hm

/-- **`KernelCheck::build_major_args_for_member`** refines
`if aux then specParamsLifted head sp depth else majorParams head nrp depth`. -/
theorem build_major_args_for_member_spec {κ : _root_.Address → KKey}
    {nrp depth : Nat} {aux : Bool} {H : KExpr} {sp : List KExpr}
    {xh xsp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hnd : nrp + depth < 4611686018427387904)
    (hbnd : Bounded cs) (hH : TmOExact κ h H xh)
    (hsp : RepList kexprListEnum (TmOExact κ) h sp xsp)
    (ev : ObsFn W "KernelCheck::build_major_args_for_member"
      [xh, .field (nrp : F), .field (depth : F), auxVal aux, xsp] h r h' cs) :
    TmOExact κ h' (if aux then specParamsLifted H sp depth else majorParams H nrp depth) r := by
  match Obs.«KernelCheck::build_major_args_for_member».obs ev with
  | .n0 (hv14 := hv) (ev20 := evp) .. =>
    have hf : aux = false := auxVal_eq_zero.mp hv
    subst hf; simp only [Bool.false_eq_true, ↓reduceIte]
    exact build_major_params_spec (by omega) evp hH
  | .other (cs60 := cs1) (hne53 := hne) (ev62 := evs) (hc87 := hc) .. =>
    have ht : aux = true := by
      cases h : aux
      · exact (hne (auxVal_eq_zero.mpr h)).elim
      · rfl
    subst ht; simp only [↓reduceIte]
    exact apply_spec_params_lifted_spec (by omega) sp evs
      (RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])) hH hsp

/-- **`KernelCheck::build_major_args_for_self`** refines
`if aux then specParamsLifted head sp specLift else appBVarsDec head nrp topBVar`. -/
theorem build_major_args_for_self_spec {κ : _root_.Address → KKey}
    {nrp topBVar specLift : Nat} {aux : Bool} {H : KExpr} {sp : List KExpr}
    {xh xsp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hn : nrp < 9223372036854775808) (htop : topBVar < 9223372036854775808)
    (hntop : nrp ≤ topBVar + 1) (hsl : specLift < 4611686018427387904)
    (hbnd : Bounded cs) (hH : TmOExact κ h H xh)
    (hsp : RepList kexprListEnum (TmOExact κ) h sp xsp)
    (ev : ObsFn W "KernelCheck::build_major_args_for_self"
      [xh, .field (nrp : F), .field (topBVar : F), .field (specLift : F), auxVal aux, xsp]
      h r h' cs) :
    TmOExact κ h' (if aux then specParamsLifted H sp specLift else appBVarsDec H nrp topBVar) r := by
  match Obs.«KernelCheck::build_major_args_for_self».obs ev with
  | .n1 (cs18 := cs1) (hv14 := hv) (ev20 := evs) (hc45 := hc) .. =>
    have ht : aux = true := auxVal_eq_one.mp hv
    subst ht; simp only [↓reduceIte]
    exact apply_spec_params_lifted_spec hsl sp evs
      (RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])) hH hsp
  | .other (hne46 := hne) (ev55 := evd) .. =>
    have hf : aux = false := by
      cases h : aux
      · rfl
      · exact (hne (auxVal_eq_one.mpr h)).elim
    subst hf; simp only [Bool.false_eq_true, ↓reduceIte]
    exact build_apply_bvars_decreasing_spec hn htop hntop evd hH

/-- **`KernelCheck::build_ctor_app_params`** refines `ctorAppParams H nrp depthNow aux sp`. -/
theorem build_ctor_app_params_spec {κ : _root_.Address → KKey}
    {nOwn nrp depthNow : Nat} {aux : Bool} {H : KExpr} {sp : List KExpr}
    {xh xsp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hd : depthNow < 4611686018427387904) (h1 : 1 ≤ depthNow) (hle : nrp ≤ depthNow)
    (hbnd : Bounded cs) (hH : TmOExact κ h H xh)
    (hsp : RepList kexprListEnum (TmOExact κ) h sp xsp)
    (ev : ObsFn W "KernelCheck::build_ctor_app_params"
      [xh, .field (nOwn : F), .field (nrp : F), .field (depthNow : F), auxVal aux, xsp]
      h r h' cs) :
    TmOExact κ h' (ctorAppParams H nrp depthNow aux sp) r := by
  match Obs.«KernelCheck::build_ctor_app_params».obs ev with
  | .n0 (hv14 := hv) (op52 := op) (ev20 := evd) .. =>
    have hf : aux = false := auxVal_eq_zero.mp hv
    subst hf; simp only [ctorAppParams]
    obtain rfl := binop_sub_one_nat h1 op
    exact build_apply_bvars_decreasing_spec (by omega) (by omega) (by omega) evd hH
  | .other (cs68 := cs1) (hne61 := hne) (op101 := op) (ev70 := evs) (hc104 := hc) .. =>
    have ht : aux = true := by
      cases h : aux
      · exact (hne (auxVal_eq_zero.mpr h)).elim
      · rfl
    subst ht; simp only [ctorAppParams]
    obtain rfl := binop_sub_nat hle op
    exact apply_spec_params_lifted_spec (by omega) sp evs
      (RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])) hH hsp

/-- **`KernelCheck::projection_addr_ctor`** hashes the constructor projection record `(i, j, blk)`
to `IxVM.Consistency.ctorAddr (ixAddr ba) i j`, needing only `Bounded cs`. -/
theorem projection_addr_ctor_exact {i j : Nat} {ba : Bytes.Address}
    {xblk r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hi : i < 18446744069414584321) (hj : j < 18446744069414584321)
    (hbnd : Bounded cs) (rba : Bytes.RepAddressRef addrTy h ba xblk)
    (ev : ObsFn W "KernelCheck::projection_addr_ctor" [.field (i : F), .field (j : F), xblk]
      h r h' cs) :
    ∃ a : Bytes.Address, Bytes.RepAddressRef addrTy h' a r ∧
      ixAddr a = IxVM.Consistency.ctorAddr (ixAddr ba) i j := by
  obtain ⟨v1, m2, cs12, v23, m24, cs34, m114, m127, m140, m153, v165, m166, cs176, m189, cs204,
    ev14, ev36, hm122, hm135, hm148, hm161, hm197, ev178, ev206, hc215⟩ :=
    Obs.«KernelCheck::projection_addr_ctor».obs ev
  obtain ⟨ni, hni, hxi, rfl, hm2⟩ := Lib.u64_from_field_spec ev14
  obtain ⟨nj, hnj, hxj, rfl, hm24⟩ := Lib.u64_from_field_spec ev36
  injection hxi with hxi; injection hxj with hxj
  have hni_eq : ni = i := by
    have h1 := fval_natCast (n := ni) (by omega)
    have h2 := fval_natCast (n := i) hi
    have := congrArg ZMod.val hxi; omega
  have hnj_eq : nj = j := by
    have h1 := fval_natCast (n := nj) (by omega)
    have h2 := fval_natCast (n := j) hj
    have := congrArg ZMod.val hxj; omega
  subst hni_eq hnj_eq
  have e1 : Heap.Extends m24 m114 := by rw [hm122]; exact Heap.Extends.snoc _ _
  have e2 : Heap.Extends m114 m127 := by rw [hm135]; exact Heap.Extends.snoc _ _
  have e3 : Heap.Extends m127 m140 := by rw [hm148]; exact Heap.Extends.snoc _ _
  have e4 : Heap.Extends m140 m153 := by rw [hm161]; exact Heap.Extends.snoc _ _
  have e5 : Heap.Extends m153 m189 := by rw [hm197]; exact Heap.Extends.snoc _ _
  have extH : Heap.Extends h m189 := by
    rw [← hm2, ← hm24]; exact e1.trans (e2.trans (e3.trans (e4.trans e5)))
  have c1 : m189[m24.length]? = some (.construct IxVM.Refinement.Core.Specs.Callees.ixExprListEnum "Nil" []) :=
    (e2.trans (e3.trans (e4.trans e5))).getElem?_eq (by rw [hm122]; simp)
  have c2 : m189[m114.length]? = some (.construct addrListEnum "Nil" []) :=
    (e3.trans (e4.trans e5)).getElem?_eq (by rw [hm135]; simp)
  have c3 : m189[m127.length]? = some (.construct IxVM.Refinement.Core.Specs.Callees.ixUnivListEnum "Nil" []) :=
    (e4.trans e5).getElem?_eq (by rw [hm148]; simp)
  have c4 : m189[m140.length]? = some (.construct IxVM.Refinement.Core.Specs.Callees.ixBinderListEnum "Nil" []) :=
    e5.getElem?_eq (by rw [hm161]; simp)
  have c5 : m189[m153.length]? = some (.construct IxVM.Refinement.Core.byteListEnum "Nil" []) := by
    rw [hm197]; simp
  have hrepi : RepU64 m189 ni.toUInt64 (TagN.u64Value ni) := by
    have e := Lib.repU64_ofNatLT m189 (m := ni) (Nat.lt_trans hni (by decide))
    rwa [UInt64.ofNatLT_eq_ofNat] at e
  have hrepj : RepU64 m189 nj.toUInt64 (TagN.u64Value nj) := by
    have e := Lib.repU64_ofNatLT m189 (m := nj) (Nat.lt_trans hnj (by decide))
    rwa [UInt64.ofNatLT_eq_ofNat] at e
  let info : Ixon.ConstantInfo := .cPrj ⟨ni.toUInt64, nj.toUInt64, ixAddr ba⟩
  have hinfo : IxVM.Refinement.Core.Specs.Callees.ProjInfoRep m189 info
      (.construct "Ixon::ConstantInfo" "CPrj"
        [.construct "Ixon::ConstructorProj" "Mk"
          [TagN.u64Value ni, TagN.u64Value nj, xblk]]) :=
    ⟨TagN.u64Value ni, TagN.u64Value nj, xblk, ba, rfl, hrepi, hrepj,
      Bytes.repAddressRef_heapMono₂ addrTy extH rba, rfl⟩
  obtain ⟨_, hbytes⟩ := L1.put_constant_proj_spec (info := info) (rest := [])
    ⟨_, _, _, _, _, rfl, hinfo, RepLinkedList.nil c1, RepLinkedList.nil c2,
      RepLinkedList.nil c3, RepLinkedList.nil c4⟩
    (RepLinkedList.nil c5) ev178
  rw [List.append_nil] at hbytes
  have hlen : ((Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩).data.toList).length < 4294967296 := by
    simpa only [ByteArray.size, Array.length_toList] using
      Claim.serConstant_cprj_size_lt ni.toUInt64 nj.toUInt64 ba
  obtain ⟨_, a, ha, ha_eq⟩ := L1.bytes_to_addr_native_spec hlen hbytes ev206
  refine ⟨a, ha, ?_⟩
  rw [ha_eq, Array.toArray_toList]
  rfl

/-! ## Section 3: Flat-list queries and zero-collision peer recursor resolution -/

/-- **`KernelCheck::build_flat_own_params`** refines `flatOwnParams (ReconView.ofStore t E₀) es`
when every entry of `es` is a held inductive type in `E₀`. -/
theorem build_flat_own_params_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R)) :
    ∀ (es : List FlatEntry) {xflat r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      (∀ c ∈ cs, c ∈ rootCalls) →
      RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h es xflat →
      (∀ e ∈ es, Held R e.addr ∧ ∃ info, indDataAt t E₀ e.addr = some (some info)) →
      ObsFn W "KernelCheck::build_flat_own_params" [xflat] h r h' cs →
      ∃ fop : List Nat,
        flatOwnParams (ReconView.ofStore t E₀) es = some fop ∧
        fop.length = es.length ∧
        (∀ n ∈ fop, n < 72057594037927936) ∧
        RepList fieldListEnum RepNatField h' fop r := by
  have hIA : IndAnswers rootCalls (Held R) (Core.keyOf t) (ReconView.ofStore t E₀) :=
    indAnswers_ofStore ht hwf hS hH hbd hRsub hcl hlv
  intro es
  induction es with
  | nil =>
    intro xflat r h h' cs _ hes _ ev
    match Obs.«KernelCheck::build_flat_own_params».obs ev with
    | .Nil (he24 := hr0) (hm23 := hm0) .. =>
      cases hr0; cases hm0
      exact ⟨[], rfl, rfl, (fun _ hm => nomatch hm), Lib.rep_store_nil h⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hcons
  | cons e rest ih =>
    intro xflat r h h' cs hsub hes hall ev
    match Obs.«KernelCheck::build_flat_own_params».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    | .Cons (x_rest := xrest) (x_member_addr := xa) (v82 := vci) (m83 := m1) (p90 := pci)
        (cs96 := cs1) (v181 := vnp) (m182 := m2) (v199 := vrest) (m208 := m3) (cs216 := cs3)
        (ld12 := ld) (ev98 := evci) (ld92 := ldci) (sg189 := sg)
        (he194 := hr0) (hm193 := hm0) (ev218 := evrec) (hc227 := hc) .. =>
      cases hr0; cases hm0
      obtain ⟨e', rest', h1, he', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with h1e h1r; subst h1e h1r
      obtain ⟨_, _, _, ae, htup, rae, hae, -, -⟩ := he'
      injection htup with hl; injection hl with hxa _; subst hxa
      obtain ⟨hSe, info0, hinfo0⟩ := hall e (List.mem_cons_self ..)
      rw [← hae] at hSe hinfo0
      obtain ⟨hInd, hOther⟩ := hIA
        (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hSe rae evci ldci
      have hsg : ∃ info, indDataAt t E₀ (ixAddr ae) = some (some info) ∧
          info.np < 72057594037927936 ∧ vnp = .field (info.np : F) ∧ m2 = m1 := by
        cases sg with
        | Induct _ _ _ _ _ _ _ _ hv hr hh _ =>
          obtain ⟨info, _, hia, -, hnp56, -, -, -, -, -, -, -, hnpEq, -⟩ := hInd _ _ _ _ _ _ _ _ hv
          exact ⟨info, hia, hnp56, hr.trans hnpEq, hh⟩
        | other hne _ _ _ =>
          have hnone := hOther hne
          change indDataAt t E₀ (ixAddr ae) = some none at hnone
          rw [hinfo0] at hnone; cases hnone
      obtain ⟨info, hia, hnp56, rfl, rfl⟩ := hsg
      obtain ⟨fop, hfop, hlen, hlt56, hrep⟩ := ih
        (fun c hc' => hsub c (by rw [hc]; simp [hc']))
        (flatList_mono evci.heap_extends hrest)
        (fun x hx => hall x (List.mem_cons_of_mem _ hx)) evrec
      refine ⟨info.np :: fop, ?_, by simp [hlen], ?_,
        Lib.rep_store_cons repNatField_heapMono₂ rfl hrep⟩
      · simp only [flatOwnParams]
        rw [show (ReconView.ofStore t E₀).ind e.addr = some (some info) from by
            change indDataAt t E₀ e.addr = some (some info); rwa [← hae], hfop]
      · intro n hn
        rcases List.mem_cons.mp hn with rfl | hn
        · exact hnp56
        · exact hlt56 n hn

/-- Pure sum of constructor counts over a list of `FlatEntry`s. -/
noncomputable def flatTotalCtors (V : ReconView) : List FlatEntry → Option Nat
  | [] => some 0
  | e :: es =>
    match V.ind e.addr, flatTotalCtors V es with
    | some (some i), some n => some (i.nctors + n)
    | _, _ => none

theorem ctorsBefore_le_flatTotalCtors (V : ReconView) :
    ∀ (es : List FlatEntry) (k tot cb : Nat),
      flatTotalCtors V es = some tot → ctorsBefore V es k = some cb → cb ≤ tot := by
  intro es
  induction es with
  | nil =>
    intro k tot cb htot hcb
    simp only [flatTotalCtors, Option.some.injEq] at htot; subst htot
    cases k <;> simp only [ctorsBefore, Option.some.injEq] at hcb <;> omega
  | cons e rest ih =>
    intro k tot cb htot hcb
    simp only [flatTotalCtors] at htot
    cases hi : V.ind e.addr with
    | none => simp [hi] at htot
    | some opt =>
      cases opt with
      | none => simp [hi] at htot
      | some info =>
        cases ht : flatTotalCtors V rest with
        | none => simp [hi, ht] at htot
        | some n =>
          simp only [hi, ht, Option.some.injEq] at htot; subst htot
          cases k with
          | zero =>
            simp only [ctorsBefore, Option.some.injEq] at hcb; omega
          | succ k' =>
            simp only [ctorsBefore, hi] at hcb
            cases hcb' : ctorsBefore V rest k' with
            | none => simp [hcb'] at hcb
            | some cb' =>
              simp only [hcb', Option.some.injEq] at hcb; subst hcb
              have := ih k' n cb' ht hcb'; omega

/-- **`KernelCheck::ctors_before_pos`** refines `ctorsBefore (ReconView.ofStore t E₀) es
(target - cur)` when every entry of `es` is a held inductive type and total constructor count
fits below `2 ^ 63`. -/
theorem ctors_before_pos_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R)) :
    ∀ (es : List FlatEntry) (target cur tot : Nat)
      {xflat r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      cur ≤ target → target < 9223372036854775808 → tot < 9223372036854775808 →
      flatTotalCtors (ReconView.ofStore t E₀) es = some tot →
      (∀ c ∈ cs, c ∈ rootCalls) →
      RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h es xflat →
      (∀ e ∈ es, Held R e.addr) →
      ObsFn W "KernelCheck::ctors_before_pos"
        [xflat, .field (target : F), .field (cur : F)] h r h' cs →
      ∃ cb : Nat,
        ctorsBefore (ReconView.ofStore t E₀) es (target - cur) = some cb ∧
        cb ≤ tot ∧ r = .field (cb : F) := by
  have hIA : IndAnswers rootCalls (Held R) (Core.keyOf t) (ReconView.ofStore t E₀) :=
    indAnswers_ofStore ht hwf hS hH hbd hRsub hcl hlv
  intro es
  induction es with
  | nil =>
    intro target cur tot xflat r h h' cs hle ht_lt htot_lt htot _ hes _ ev
    match Obs.«KernelCheck::ctors_before_pos».obs ev with
    | .n0 (he24 := hr0) .. =>
      cases hr0
      refine ⟨0, ?_, Nat.zero_le _, rfl⟩
      cases hdiff : target - cur <;> rfl
    | .other_Nil (he50 := hr0) .. =>
      cases hr0
      refine ⟨0, ?_, Nat.zero_le _, rfl⟩
      cases hdiff : target - cur <;> rfl
    | .other_Cons (ld42 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hcons
  | cons e rest ih =>
    intro target cur tot xflat r h h' cs hle ht_lt htot_lt htot hsub hes hheld ev
    simp only [flatTotalCtors] at htot
    cases hi : (ReconView.ofStore t E₀).ind e.addr with
    | none => simp [hi] at htot
    | some opt =>
      cases opt with
      | none => simp [hi] at htot
      | some info0 =>
        cases htot' : flatTotalCtors (ReconView.ofStore t E₀) rest with
        | none => simp [hi, htot'] at htot
        | some tot' =>
          simp only [hi, htot', Option.some.injEq] at htot; subst htot
          match Obs.«KernelCheck::ctors_before_pos».obs ev with
          | .n0 (op17 := op) (he24 := hr0) .. =>
            cases hr0
            have heq := binop_sub_eq_zero_nat (by omega) (by omega) op
            rw [show target - cur = 0 by omega]
            exact ⟨0, rfl, Nat.zero_le _, rfl⟩
          | .other_Nil (ld42 := ld) .. =>
            cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
          | .other_Cons (x_rest := xrest) (x_addr := xa) (v109 := vci) (m110 := m1)
              (p117 := pci) (cs123 := cs1) (v208 := vnc) (m209 := m2) (y218 := yrest)
              (cs229 := cs3) (v234 := vcur1)
              (op17 := op0) (hne27 := hne0) (ld42 := ld) (ev125 := evci) (ld119 := ldci)
              (sg216 := sg) (op262 := op1) (ev231 := evrec) (op224 := opadd) (hc264 := hc) .. =>
            have hne_ct : cur ≠ target := binop_sub_ne_nat op0 hne0
            obtain ⟨e', rest', h1, he', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
            injection h1 with h1e h1r; subst h1e h1r
            obtain ⟨_, _, _, ae, htup, rae, hae, -, -⟩ := he'
            injection htup with hl; injection hl with hxa _; subst hxa
            have hSe : Held R (ixAddr ae) := hae ▸ hheld e (List.mem_cons_self ..)
            obtain ⟨hInd, hOther⟩ := hIA
              (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hSe rae evci ldci
            have hsg : vnc = .field (info0.nctors : F) ∧ m2 = m1 := by
              cases sg with
              | Induct _ _ _ _ _ _ _ _ hv hr hh _ =>
                obtain ⟨info, _, hia, -, -, -, -, -, -, -, -, -, -, -, hncEq, -⟩ := hInd _ _ _ _ _ _ _ _ hv
                change indDataAt t E₀ e.addr = some (some info0) at hi
                rw [← hae] at hi
                have hinfo_eq := Option.some.inj (Option.some.inj (hia.symm.trans hi))
                subst hinfo_eq
                exact ⟨hr.trans hncEq, hh⟩
              | other hne _ _ _ =>
                have hnone := hOther hne
                change indDataAt t E₀ (ixAddr ae) = some none at hnone
                change indDataAt t E₀ e.addr = some (some info0) at hi
                rw [← hae] at hi; rw [hi] at hnone; cases hnone
            obtain ⟨rfl, rfl⟩ := hsg
            obtain rfl := binop_add_one_nat op1
            obtain ⟨cb', hcb', hcb'_le, rfl⟩ := ih target (cur + 1) tot' (by omega) ht_lt (by omega)
              htot' (fun c hc' => hsub c (by rw [hc]; simp [hc']))
              (flatList_mono evci.heap_extends hrest)
              (fun x hx => hheld x (List.mem_cons_of_mem _ hx)) evrec
            obtain rfl := binop_add_nat opadd
            have hdiff : target - cur = (target - (cur + 1)) + 1 := by omega
            refine ⟨info0.nctors + cb', ?_, by omega, rfl⟩
            rw [hdiff]
            simp only [ctorsBefore, hi, hcb']

/-- Stronger per-member flattened-family witness linking recursor `k` of `rb` to `es[k]` with the
target inductive's `IndInfo` and full `info.np` prefix for auxiliaries. Implies `RecordFlat`. -/
def RecordFlatAux (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (rb : _root_.Address)
    (crb : Ixon.Constant) (rs : Array Ixon.MutConst) (es : List FlatEntry) : Prop :=
  es.length = rs.size ∧
  (∀ k, k < rs.size → ∃ r, rs[k]? = some (.recr r)) ∧
  ∀ (k : Nat) (r : Ixon.Recursor) (e : FlatEntry),
    rs[k]? = some (.recr r) → es[k]? = some e →
    ∃ ty d info,
      loadedAt t (fun x => E.blobs.get? x) crb (blockSelf t rb rs) r.lvls.toNat
        (mutsRoot rs k) r.typ = some ty ∧
      binderDomAfter (r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat)
        ty = some d ∧
      Ix.Kernel.Expr.getAppFn d = .const (keyOf t e.addr) e.levels ∧
      indInfoAt E e.addr = some (some info) ∧
      (e.aux = true →
        ((Ix.Kernel.Expr.getAppArgs d).take info.np).map
            (Ix.Kernel.Expr.lowerBVars (r.motives.toNat + r.minors.toNat + r.indices.toNat) 0) =
          e.params)

theorem RecordFlatAux.toRecordFlat {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst} {es : List FlatEntry}
    (h : RecordFlatAux t E rb crb rs es) : RecordFlat t E rb crb rs es := by
  intro k r e hk he
  obtain ⟨ty, d, info, hty, hd, hfn, -, haux⟩ := h.2.2 k r e hk he
  refine ⟨ty, d, hty, hd, hfn, fun ha => ?_⟩
  have hsp := haux ha
  have hlen : e.params.length = (d.getAppArgs.take info.np).length := by
    rw [← hsp, List.length_map]
  have htk : d.getAppArgs.take e.params.length = d.getAppArgs.take info.np := by
    rw [hlen, List.length_take]
    by_cases hle : info.np ≤ d.getAppArgs.length
    · rw [Nat.min_eq_left hle]
    · rw [Nat.min_eq_right (by omega), List.take_length, List.take_of_length_le (by omega)]
  rw [htk, hsp]

/-- Pairwise distinguishability of entries in `es` for `find_peer_rec_spec_walk`: no earlier
entry `i < j` can match entry `j` on `(addr)` (for non-auxiliaries) or `(addr, params, levels)`
(for auxiliaries, where every earlier matching address is also auxiliary). -/
def FlatPeerDistinct (es : List FlatEntry) : Prop :=
  ∀ (i j : Nat) (ei ej : FlatEntry), i < j → es[i]? = some ei → es[j]? = some ej →
    if ej.aux then
      ei.addr ≠ ej.addr ∨ (ei.aux = true ∧ (ei.params ≠ ej.params ∨ ei.levels ≠ ej.levels))
    else
      ei.addr ≠ ej.addr

private theorem indcAddrs_mem_spec (prim : _root_.Address) :
    ∀ (cur : List Ixon.MutConst) (pos : Nat) (a : _root_.Address),
      a ∈ indcAddrs prim pos cur →
      ∃ off ind, cur[off]? = some (.indc ind) ∧ a = memberAddr prim (pos + off) (.indc ind) := by
  intro cur
  induction cur with
  | nil => intro _ _ ha; simp [indcAddrs] at ha
  | cons m rest ih =>
    intro pos a ha
    cases m with
    | indc ind =>
      simp only [indcAddrs, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact ⟨0, ind, rfl, by simp⟩
      · obtain ⟨off, ind', hget, heq⟩ := ih (pos + 1) a ha
        exact ⟨off + 1, ind', hget, by rwa [show pos + (off + 1) = (pos + 1) + off by omega]⟩
    | defn _ | recr _ =>
      simp only [indcAddrs] at ha
      obtain ⟨off, ind', hget, heq⟩ := ih (pos + 1) a ha
      exact ⟨off + 1, ind', hget, by rwa [show pos + (off + 1) = (pos + 1) + off by omega]⟩

private theorem indcAddrs_nodup_of_usedClosed {R E₀ : Ixon.Env} {prim : _root_.Address}
    {cprim : Ixon.Constant} {msp : Array Ixon.MutConst}
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hSp : Held R prim) (hcprimE : recordOf E₀ prim = some cprim)
    (hmsp : cprim.info = .muts msp) (hsz : msp.size < 18446744069414584321) :
    ∀ (cur : List Ixon.MutConst) (pos : Nat),
      pos + cur.length = msp.size →
      (∀ i m, cur[i]? = some m → msp[pos + i]? = some m) →
      (indcAddrs prim pos cur).Nodup := by
  have hcprimR : recordOf R prim = some cprim := by
    obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hSp
    have := Option.some.inj ((hRsub _ _ hc').symm.trans hcprimE)
    subst this; exact hc'
  intro cur
  induction cur with
  | nil => intro _ _ _; exact List.nodup_nil
  | cons m rest ih =>
    intro pos hlen hidx
    have hidx' : ∀ i m', rest[i]? = some m' → msp[(pos + 1) + i]? = some m' := fun i m' hi => by
      have h1 := hidx (i + 1) m' (by simpa using hi)
      rwa [show pos + (i + 1) = (pos + 1) + i by omega] at h1
    cases m with
    | defn _ | recr _ =>
      simp only [indcAddrs]
      exact ih (pos + 1) (by simp at hlen; omega) hidx'
    | indc ind =>
      simp only [indcAddrs, List.nodup_cons]
      refine ⟨fun hin => ?_, ih (pos + 1) (by simp at hlen; omega) hidx'⟩
      obtain ⟨off, ind', hget, heq⟩ := indcAddrs_mem_spec prim rest (pos + 1) _ hin
      have hpos_m : msp[pos]? = some (.indc ind) := by simpa using hidx 0 (.indc ind) rfl
      have hoff_m : msp[(pos + 1) + off]? = some (.indc ind') := hidx' off (.indc ind') hget
      have h1 := (hcl.2 prim cprim msp hcprimR hmsp pos (.indc ind) hpos_m).1
      have h2 := (hcl.2 prim cprim msp hcprimR hmsp ((pos + 1) + off) (.indc ind') hoff_m).1
      rw [heq] at h1
      have hproj := Option.some.inj (h1.symm.trans h2)
      simp only [memberProjection, Ixon.Constant.mk.injEq, Ixon.ConstantInfo.iPrj.injEq,
        Ixon.InductiveProj.mk.injEq] at hproj
      have hlt1 : pos < UInt64.size := by
        have : UInt64.size = 18446744073709551616 := rfl
        have := (Array.getElem?_eq_some_iff.mp hpos_m).1; omega
      have hlt2 : (pos + 1) + off < UInt64.size := by
        have : UInt64.size = 18446744073709551616 := rfl
        have := (Array.getElem?_eq_some_iff.mp hoff_m).1; omega
      have hu : pos.toUInt64.toNat = ((pos + 1) + off).toUInt64.toNat :=
        congrArg UInt64.toNat hproj.1.1
      change (UInt64.ofNat pos).toNat = (UInt64.ofNat ((pos + 1) + off)).toNat at hu
      rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt1,
        Nat.mod_eq_of_lt hlt2] at hu
      omega

private theorem originals_map_addr {V : FlatView} {off : Nat} :
    ∀ (as : List _root_.Address) (os : List FlatEntry),
      originals V off as = some os → os.map (·.addr) = as := by
  intro as
  induction as with
  | nil =>
    intro os h; simp only [originals, Option.some.injEq] at h; subst h; rfl
  | cons a rest ih =>
    intro os h
    simp only [originals] at h
    cases hc : V.ci a with
    | none => simp [hc] at h
    | some opt =>
      cases opt with
      | none => simp [hc] at h
      | some info =>
        cases ho : originals V off rest with
        | none => simp [hc, ho] at h
        | some os' =>
          simp only [hc, ho, Option.some.injEq] at h; subst h
          simp [ih os' ho]

private theorem buildFlatAuxStep_peerDistinct {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst} {prim : _root_.Address} :
    ∀ (cur : List Ixon.MutConst) (pos : Nat) (acc res : List FlatEntry),
      buildFlatAuxStep t E₀ rb crb rs prim pos cur acc = some res →
      (∀ e ∈ acc, e.aux = false → ∃ info, indInfoAt E₀ e.addr = some (some info) ∧ info.blk = prim) →
      FlatPeerDistinct acc →
      FlatPeerDistinct res := by
  intro cur
  induction cur with
  | nil =>
    intro _ acc res h _ hpd
    simp only [buildFlatAuxStep, Option.some.injEq] at h; subst h; exact hpd
  | cons m rest ih =>
    intro pos acc res h hnonaux hpd
    cases m with
    | defn _ | indc _ => exact ih (pos + 1) acc res h hnonaux hpd
    | recr rc =>
      simp only [buildFlatAuxStep] at h
      cases hty : loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
          (mutsRoot rs pos) rc.typ with
      | none => simp only [hty] at h; cases h
      | some ty =>
        simp only [hty] at h
        cases hd : binderDomAfter
            (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) ty with
        | none => simp [hd] at h
        | some d =>
          simp only [hd] at h
          cases hfn : d.getAppFn with
          | const k us =>
            simp only [hfn] at h
            cases hka : keyAddr t k with
            | none => simp [hka] at h
            | some paddr =>
              simp only [hka] at h
              cases hinfo : indInfoAt E₀ paddr with
              | none => simp [hinfo] at h
              | some opt =>
                cases opt with
                | none =>
                  simp only [hinfo] at h
                  exact ih (pos + 1) acc res h hnonaux hpd
                | some info =>
                  simp only [hinfo] at h
                  by_cases hblk : info.blk == prim
                  · simp only [hblk, ↓reduceIte] at h
                    exact ih (pos + 1) acc res h hnonaux hpd
                  · simp only [hblk, Bool.false_eq_true, ↓reduceIte] at h
                    have hne_prim : info.blk ≠ prim := fun heq => hblk (by simp [heq])
                    set sp := (d.getAppArgs.take info.np).map
                      (Ix.Kernel.Expr.lowerBVars (rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) 0)
                    by_cases hin : auxEntryIn acc paddr sp us
                    · simp only [hin, ↓reduceIte] at h
                      exact ih (pos + 1) acc res h hnonaux hpd
                    · simp only [hin, Bool.false_eq_true, ↓reduceIte] at h
                      let newE : FlatEntry := ⟨paddr, true, sp, us⟩
                      have hnonaux' : ∀ e ∈ acc ++ [newE], e.aux = false →
                          ∃ info', indInfoAt E₀ e.addr = some (some info') ∧ info'.blk = prim := by
                        intro e he hf
                        simp only [List.mem_append, List.mem_singleton] at he
                        rcases he with hm | rfl
                        · exact hnonaux e hm hf
                        · cases hf
                      have hpd' : FlatPeerDistinct (acc ++ [newE]) := by
                        intro i j ei ej hij hi hj
                        by_cases hj_lt : j < acc.length
                        · rw [List.getElem?_append_left (by omega)] at hi
                          rw [List.getElem?_append_left hj_lt] at hj
                          exact hpd i j ei ej hij hi hj
                        · have hj_eq : j = acc.length := by
                            have := (List.getElem?_eq_some_iff.mp hj).1
                            simp only [List.length_append, List.length_singleton] at this
                            omega
                          subst hj_eq
                          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
                            List.getElem?_cons_zero, Option.some.injEq] at hj
                          subst hj
                          rw [List.getElem?_append_left hij] at hi
                          have hei_mem : ei ∈ acc := List.mem_of_getElem? hi
                          simp only [newE, ↓reduceIte]
                          cases haux_i : ei.aux with
                          | false =>
                            left
                            intro had_eq
                            obtain ⟨info_i, hinfo_i, hblk_i⟩ := hnonaux ei hei_mem haux_i
                            rw [had_eq, hinfo] at hinfo_i
                            injection hinfo_i with h1; injection h1 with h2
                            rw [← h2] at hblk_i
                            exact hne_prim hblk_i
                          | true =>
                            by_cases had_eq : ei.addr = paddr
                            · right
                              refine ⟨rfl, ?_⟩
                              by_cases hsp_eq : ei.params = sp
                              · right; intro hus_eq
                                have hany : auxEntryIn acc paddr sp us = true :=
                                  List.any_eq_true.mpr ⟨ei, hei_mem, by
                                    simp [haux_i, had_eq, hsp_eq, hus_eq]⟩
                                exact hin hany
                              · exact .inl hsp_eq
                            · exact .inl had_eq
                      exact ih (pos + 1) (acc ++ [newE]) res h hnonaux' hpd'
          | _ => simp [hfn] at h

/-- Under `UsedClosed R`, any flattened list `flat` built by `originals` + `buildFlatAuxStep`
satisfies `FlatPeerDistinct flat` (with zero collision hypothesis). -/
theorem flatPeerDistinct_of_buildFlatAuxStep {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env}
    {rb prim : _root_.Address} {crb cprim : Ixon.Constant} {rs msp : Array Ixon.MutConst}
    {off : Nat} {os flat : List FlatEntry}
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hSp : Held R prim) (hcprimE : recordOf E₀ prim = some cprim)
    (hmsp : cprim.info = .muts msp) (hsz : msp.size < 18446744069414584321)
    (horig : originals (FlatView.ofStore t E₀) off (indcAddrs prim 0 msp.toList) = some os)
    (hos_props : ∀ e ∈ os, e.aux = false ∧
      ∃ idx ind, msp[idx]? = some (.indc ind) ∧ e.addr = memberAddr prim idx (.indc ind))
    (haux : buildFlatAuxStep t E₀ rb crb rs prim 0 rs.toList os = some flat) :
    FlatPeerDistinct flat := by
  have hcprimR : recordOf R prim = some cprim := by
    obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hSp
    have := Option.some.inj ((hRsub _ _ hc').symm.trans hcprimE)
    subst this; exact hc'
  have hnodup_addrs : (os.map (·.addr)).Nodup := by
    rw [originals_map_addr _ os horig]
    exact indcAddrs_nodup_of_usedClosed hRsub hcl hSp hcprimE hmsp hsz msp.toList 0
      (by simp) (fun i m hm => by simpa [← Array.getElem?_toList] using hm)
  have hnonaux_os : ∀ e ∈ os, e.aux = false →
      ∃ info, indInfoAt E₀ e.addr = some (some info) ∧ info.blk = prim := by
    intro e he _
    obtain ⟨-, idx, ind, hget, had⟩ := hos_props e he
    have hprojR := (hcl.2 prim cprim msp hcprimR hmsp idx (.indc ind) hget).1
    have hprojE := hRsub _ _ hprojR
    have hidx64 : idx.toUInt64.toNat = idx := by
      have : UInt64.size = 18446744073709551616 := rfl
      have := (Array.getElem?_eq_some_iff.mp hget).1
      change (UInt64.ofNat idx).toNat = idx
      rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
    refine ⟨⟨ind.lvls.toNat, ind.params.toNat, ind.ctors.size, prim, idx⟩, ?_, rfl⟩
    unfold indInfoAt
    simp only [had, hprojE, memberProjection, hcprimE, hmsp, hidx64, hget]
  have hpd_os : FlatPeerDistinct os := by
    intro i j ei ej hij hi hj
    have hfj : ej.aux = false := (hos_props ej (List.mem_of_getElem? hj)).1
    simp only [hfj, Bool.false_eq_true, ↓reduceIte]
    intro heq
    have hi_lt : i < (os.map (·.addr)).length := by
      rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hi).1
    have hj_lt : j < (os.map (·.addr)).length := by
      rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hj).1
    have hget_i : (os.map (·.addr))[i]'hi_lt = ei.addr := by
      rw [List.getElem_map, (List.getElem_of_getElem? hi).2]
    have hget_j : (os.map (·.addr))[j]'hj_lt = ej.addr := by
      rw [List.getElem_map, (List.getElem_of_getElem? hj).2]
    have hidx_eq := (List.nodup_iff_injective_getElem.mp hnodup_addrs)
      (a₁ := ⟨i, hi_lt⟩) (a₂ := ⟨j, hj_lt⟩) (hget_i.trans (heq.trans hget_j.symm))
    have : i = j := congrArg Fin.val hidx_eq
    omega
  exact buildFlatAuxStep_peerDistinct rs.toList 0 os flat haux hnonaux_os hpd_os

/-- **`KernelCheck::find_peer_rec_spec_walk`** on a `RecordFlatAux` + `FlatPeerDistinct` block
returns `memberAddr rb targetIdx (.recr r_target)` when started at `pos ≤ targetIdx`. -/
theorem find_peer_rec_spec_walk_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    {rba : Bytes.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {es : List FlatEntry} {targetIdx : Nat} {te : FlatEntry}
    (hSrb : Held R (ixAddr rba)) (hcrbE : recordOf E₀ (ixAddr rba) = some crb)
    (hmuts : crb.info = .muts rs)
    (hRF : RecordFlatAux t E₀ (ixAddr rba) crb rs es)
    (hPD : FlatPeerDistinct es) (htarget : es[targetIdx]? = some te) :
    ∀ (cur : List Ixon.MutConst) (pos : Nat)
      {xall xcur xrba xtaddr xtsp xtus xself r : SourceValue F}
      {tba : Bytes.Address} {h h' : Heap F} {cs : List (Call F)},
      pos + cur.length = rs.size →
      pos ≤ targetIdx →
      (∀ i m, cur[i]? = some m → rs[pos + i]? = some m) →
      (∀ c ∈ cs, c ∈ rootCalls) →
      Core.Specs.Callees.MembersRep h rs.toList xall →
      Core.Specs.Callees.MembersRep h cur xcur →
      Bytes.RepAddressRef addrTy h rba xrba →
      Bytes.RepAddressRef addrTy h tba xtaddr → ixAddr tba = te.addr →
      RepList kexprListEnum (TmOExact (Core.keyOf t)) h te.params xtsp →
      RepKLevelList h te.levels xtus →
      ObsFn W "KernelCheck::find_peer_rec_spec_walk"
        [xall, xcur, xrba, xtaddr, xtsp, xtus, auxVal te.aux, xself, .field (pos : F)] h r h' cs →
      ∃ (rc_t : Ixon.Recursor) (ma : Bytes.Address),
        rs[targetIdx]? = some (.recr rc_t) ∧
        Bytes.RepAddressRef addrTy h' ma r ∧
        ixAddr ma = memberAddr (ixAddr rba) targetIdx (.recr rc_t) := by
  have hinj : Function.Injective (Core.keyOf t) := fun _ _ he => Core.keyOf_inj hwf he
  intro cur
  induction cur with
  | nil =>
    intro pos _ _ _ _ _ _ _ _ _ _ _ _ hlen hle _ _ _ _ _ _ _ _ _ _
    have hlt : targetIdx < rs.size := by
      have := (List.getElem?_eq_some_iff.mp htarget).1; rw [← hRF.1]; exact this
    have hlen' : pos = rs.size := by simpa using hlen
    omega
  | cons m rest ih =>
    intro pos xall xcur xrba xtaddr xtsp xtus xself r tba h h' cs
      hlen hle hidx hsub hall hcur rrba rtba htba htsp htus ev
    have hm_at : rs[pos]? = some m := by simpa using hidx 0 m rfl
    have hpos_lt_rs : pos < rs.size := (Array.getElem?_eq_some_iff.mp hm_at).1
    have hidx' : ∀ i m', rest[i]? = some m' → rs[(pos + 1) + i]? = some m' := fun i m' hi => by
      have h1 := hidx (i + 1) m' (by simpa using hi)
      rwa [show pos + (i + 1) = (pos + 1) + i by omega] at h1
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → ∀ c ∈ cs', c ∈ rootCalls :=
      fun hs c hc => hsub c (hs c hc)
    -- `rs[pos]` must be `.recr rc` since `RecordFlatAux` says all members of `rs` are recursors.
    obtain ⟨rc, hrc_at⟩ := hRF.2.1 pos hpos_lt_rs
    have hm_eq : m = .recr rc := Option.some.inj (hm_at.symm.trans hrc_at)
    subst hm_eq
    have hpos_lt_es : pos < es.length := by rw [hRF.1]; exact hpos_lt_rs
    let ep := es[pos]'hpos_lt_es
    have hep_at : es[pos]? = some ep := List.getElem?_eq_getElem hpos_lt_es
    obtain ⟨ty_p, d_p, info_p, hty_p, hd_p, hfn_p, hinfo_p, haux_p⟩ := hRF.2.2 pos rc ep hrc_at hep_at
    -- Helper analyzing `Seg1` on `rs[pos] = .recr rc`
    have seg_eval : ∀ {vci v63 m1 m2 p109 cs1 cs2 m3 vr cs3}
        (evpa : ObsFn W "Ingress::projection_addr" [xall, xrba, .field (pos : F)] h v63 m1 cs1)
        (evci : ObsFn W "Ingress::get_ci" [v63] m1 p109 m2 cs2)
        (ldci : loadValue m2 p109 = .ok vci)
        (sg : Obs.«KernelCheck::find_peer_rec_spec_walk».Seg1 vci v63
          (.construct "Ixon::MutConst" "Recr" [v63]) xall xall xcur xrba xtaddr xtsp xtus
          (auxVal te.aux) xself (.field (pos : F)) m2 vr m3 cs3),
        True := fun _ _ _ _ => trivial
    match Obs.«KernelCheck::find_peer_rec_spec_walk».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hcur ld
    | .Cons_other (ld12 := ld) (hne789 := hne) .. =>
      obtain ⟨m', _, h1, hm', -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hcur ld
      injection h1 with h1m _; subst h1m
      obtain ⟨_, hshape⟩ := hm'
      exact (hne _ rfl hshape).elim
    | .Cons_Recr_n1 (v63 := vp) (m64 := m1) (cs74 := cs1) (v101 := vci) (m102 := m2)
        (p109 := pci) (cs115 := cs2) (m680 := m3) (cs682 := cs3)
        (ld12 := ld) (ev76 := evpa) (ev117 := evci) (ld111 := ldci) (sg687 := sg)
        (he703 := hr0) (he704 := hh0) (hc705 := hc) .. =>
      cases hr0; cases hh0
      have hrs_lt : rs.size < 2 ^ 39 := by
        have hlt := repList_length_lt_obs hbd hsub evpa (by rw [hc]; simp) (by simp) hall
        simpa using hlt
      obtain ⟨ext1, -, -, mc, ma, hmc, rma, hma⟩ := L1.projection_addr_spec hall rrba evpa
      rw [fval_natCast (by omega)] at hmc hma
      have hmc' : rs[pos]? = some mc := by rw [← Array.getElem?_toList]; exact hmc
      have hmc_eq : mc = .recr rc := Option.some.inj (hmc'.symm.trans hrc_at)
      subst hmc_eq
      have hma_eq : ixAddr ma = memberAddr (ixAddr rba) pos (.recr rc) := hma
      obtain ⟨ty, tyPtr, rulesPtr, blkPtr, ba', hshape, -, hnp, hni, hnm, hnmi, -,
        hloaded, htm, htyIn, -, -, -⟩ :=
        recrLoad_ofStore ht hwf hS hH hbd hRsub hcl hlv
          (sub fun c hc' => by rw [hc]; simp [hc']) hSrb hcrbE hmuts hrc_at hma_eq rma evci ldci
      have hty_eq : ty = ty_p := Option.some.inj (hloaded.symm.trans hty_p)
      subst ty
      -- If `pos = targetIdx`, done immediately! If `pos < targetIdx`, `sg` returning `1` contradicts `hPD`.
      by_cases hpeq : pos = targetIdx
      · subst hpeq
        have ext_m1_m3 := evci.heap_extends.trans (by
          cases sg with
          | Rec_Induct_n1_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evpar evci2 _ evaeq _ _ hh _ =>
            subst hh; exact evpar.heap_extends.trans (evci2.heap_extends.trans evaeq.heap_extends)
          | Rec_Induct_n1_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evpar evci2 _ evaeq _ evsp evseq evus evueq _ _ =>
            exact evpar.heap_extends.trans (evci2.heap_extends.trans (evaeq.heap_extends.trans
              (evsp.heap_extends.trans (evseq.heap_extends.trans (evus.heap_extends.trans evueq.heap_extends)))))
          | Rec_Induct_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ _ =>
            exact absurd (Value.field.inj hr) (by decide)
          | Rec_other_n1_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evpar evci2 _ _ evaeq _ _ hh _ =>
            subst hh; exact evpar.heap_extends.trans (evci2.heap_extends.trans evaeq.heap_extends)
          | Rec_other_n1_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evpar evci2 _ _ evaeq _ evsp evseq evus evueq _ _ =>
            exact evpar.heap_extends.trans (evci2.heap_extends.trans (evaeq.heap_extends.trans
              (evsp.heap_extends.trans (evseq.heap_extends.trans (evus.heap_extends.trans evueq.heap_extends)))))
          | Rec_other_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ _ =>
            exact absurd (Value.field.inj hr) (by decide)
          | other _ hr _ _ => exact absurd (Value.field.inj hr) (by decide))
        exact ⟨rc, ma, hrc_at, Bytes.repAddressRef_heapMono₂ addrTy ext_m1_m3 rma, hma_eq⟩
      · exfalso
        have hlt_pt : pos < targetIdx := by omega
        have hdist := hPD pos targetIdx ep te hlt_pt hep_at htarget
        have ext02 := ext1.trans evci.heap_extends
        cases sg with
        | Rec_Induct_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ _ =>
          exact absurd (Value.field.inj hr) (by decide)
        | Rec_other_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ _ =>
          exact absurd (Value.field.inj hr) (by decide)
        | other hne _ _ _ => exact (hne _ rfl hshape).elim
        | Rec_Induct_n1_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            hv evpar evci2 _ evaeq hv0 _ _ _ =>
          have htf : te.aux = false := auxVal_eq_zero.mp hv0
          simp only [htf, Bool.false_eq_true, ↓reduceIte] at hdist
          rw [hshape] at hv; injection hv with _ _ hl
          injection hl with _ hl; injection hl with h1 hl; injection hl with h2 hl
          injection hl with h3 hl; injection hl with h4 hl; injection hl with h5 _
          subst h1 h2 h3 h4 h5
          obtain ⟨d', pa, us', hd', hfn', rpa, -⟩ := rec_to_parent_addr_spec (by omega) htm evpar
          have hd_eq : d' = d_p := Option.some.inj (hd'.symm.trans hd_p); subst d'
          have hfn_eq := hfn'.symm.trans hfn_p
          injection hfn_eq with hk _
          have hpa_eq : ixAddr pa = ep.addr := hinj hk
          obtain ⟨hveq, -⟩ := Lib.address_eq_spec evaeq
            (Bytes.repAddressRef_heapMono₂ addrTy evci2.heap_extends rpa)
            (Bytes.repAddressRef_heapMono₂ addrTy (ext02.trans (evpar.heap_extends.trans evci2.heap_extends)) rtba)
          by_cases hsame : pa = tba
          · exact hdist (hpa_eq.symm.trans ((congrArg ixAddr hsame).trans htba))
          · rw [ite_eq_right hsame] at hveq; exact absurd (Value.field.inj hveq) (by decide)
        | Rec_other_n1_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            hv evpar evci2 _ _ evaeq hv0 _ _ _ =>
          have htf : te.aux = false := auxVal_eq_zero.mp hv0
          simp only [htf, Bool.false_eq_true, ↓reduceIte] at hdist
          rw [hshape] at hv; injection hv with _ _ hl
          injection hl with _ hl; injection hl with h1 hl; injection hl with h2 hl
          injection hl with h3 hl; injection hl with h4 hl; injection hl with h5 _
          subst h1 h2 h3 h4 h5
          obtain ⟨d', pa, us', hd', hfn', rpa, -⟩ := rec_to_parent_addr_spec (by omega) htm evpar
          have hd_eq : d' = d_p := Option.some.inj (hd'.symm.trans hd_p); subst d'
          have hfn_eq := hfn'.symm.trans hfn_p
          injection hfn_eq with hk _
          have hpa_eq : ixAddr pa = ep.addr := hinj hk
          obtain ⟨hveq, -⟩ := Lib.address_eq_spec evaeq
            (Bytes.repAddressRef_heapMono₂ addrTy evci2.heap_extends rpa)
            (Bytes.repAddressRef_heapMono₂ addrTy (ext02.trans (evpar.heap_extends.trans evci2.heap_extends)) rtba)
          by_cases hsame : pa = tba
          · exact hdist (hpa_eq.symm.trans ((congrArg ixAddr hsame).trans htba))
          · rw [ite_eq_right hsame] at hveq; exact absurd (Value.field.inj hveq) (by decide)
        | Rec_other_n1_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            hv evpar evci2 ldci2 hneI _ _ _ _ _ _ _ hcs =>
          rw [hshape] at hv; injection hv with _ _ hl
          injection hl with _ hl; injection hl with h1 hl; injection hl with h2 hl
          injection hl with h3 hl; injection hl with h4 hl; injection hl with h5 _
          subst h1 h2 h3 h4 h5
          obtain ⟨d', pa, us', hd', hfn', rpa, -⟩ := rec_to_parent_addr_spec (by omega) htm evpar
          have hd_eq : d' = d_p := Option.some.inj (hd'.symm.trans hd_p); subst d'
          have hfn_eq := hfn'.symm.trans hfn_p
          injection hfn_eq with hk _
          have hpa_eq : ixAddr pa = ep.addr := hinj hk
          have hSpa : Held R (ixAddr pa) := by
            have hfnIn := addrIn_getAppFn (addrIn_binderDomAfter htyIn hd')
            rw [hfn'] at hfnIn; exact hfnIn (ixAddr pa) rfl
          obtain ⟨-, hOther⟩ := indInfo_of_get_ci hS hH hbd hRsub hcl
            (sub fun c hc' => by rw [hc, hcs]; simp [hc']) hSpa rpa evci2 ldci2
          have hnone := hOther hneI
          rw [hpa_eq, hinfo_p] at hnone; cases hnone
        | Rec_Induct_n1_other _ _ _ _ _ _ _ _ _ _ _ _ m_par _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ _ _ _ _ _ _ _ _ _
            hv evpar evci2 ldci2 evaeq hne0 evsp evseq evus evueq opmul hcs =>
          have htt : te.aux = true := by
            cases h' : te.aux
            · exact (hne0 (auxVal_eq_zero.mpr h')).elim
            · rfl
          simp only [htt, ↓reduceIte] at hdist
          rw [hshape] at hv; injection hv with _ _ hl
          injection hl with _ hl; injection hl with h1 hl; injection hl with h2 hl
          injection hl with h3 hl; injection hl with h4 hl; injection hl with h5 _
          subst h1 h2 h3 h4 h5
          obtain ⟨d', pa, us', hd', hfn', rpa, hmaj⟩ := rec_to_parent_addr_spec (by omega) htm evpar
          have hd_eq : d' = d_p := Option.some.inj (hd'.symm.trans hd_p); subst d'
          have hfn_eq := hfn'.symm.trans hfn_p
          injection hfn_eq with hk hus_eq
          have hpa_eq : ixAddr pa = ep.addr := hinj hk
          subst us'
          have hSpa : Held R (ixAddr pa) := by
            have hfnIn := addrIn_getAppFn (addrIn_binderDomAfter htyIn hd')
            rw [hfn'] at hfnIn; exact hfnIn (ixAddr pa) rfl
          obtain ⟨hInd, -⟩ := indInfo_of_get_ci hS hH hbd hRsub hcl
            (sub fun c hc' => by rw [hc, hcs]; simp [hc']) hSpa rpa evci2 ldci2
          obtain ⟨info', -, hinfo', -, hnp56, -, -, -, -, hnpEq, -, -, -, -⟩ :=
            hInd _ _ _ _ _ _ _ _ rfl
          rw [hpa_eq, hinfo_p] at hinfo'
          have hinfo_eq := Option.some.inj (Option.some.inj hinfo')
          subst info'
          obtain ⟨hveq, rfl⟩ := Lib.address_eq_spec evaeq
            (Bytes.repAddressRef_heapMono₂ addrTy evci2.heap_extends rpa)
            (Bytes.repAddressRef_heapMono₂ addrTy (ext02.trans (evpar.heap_extends.trans evci2.heap_extends)) rtba)
          have hsame : pa = tba := by
            by_contra hne_pt
            rw [ite_eq_right hne_pt] at hveq; exact absurd (Value.field.inj hveq) (by decide)
          have had_eq : ep.addr = te.addr := hpa_eq.symm.trans ((congrArg ixAddr hsame).trans htba)
          rcases hdist with hne_ad | ⟨hep_aux, hne_su⟩
          · exact hne_ad had_eq
          · subst hnpEq
            have ext_par_m := evci2.heap_extends
            have ext_2_m := evpar.heap_extends.trans ext_par_m
            obtain ⟨d2, hd2, -, hrep_sp, -⟩ := extract_aux_spec_params_spec
              (by omega) hnp56 ext_par_m hmaj
              (RomBound.bounded_mono hbd (sub fun c hc' => by rw [hc, hcs]; simp [hc']))
              (htm.mono ext_2_m) htyIn evsp
            have hd2_eq : d2 = d_p := Option.some.inj (hd2.symm.trans hd_p); subst d2
            rw [haux_p hep_aux] at hrep_sp
            have ext_0_sp := ext02.trans (ext_2_m.trans evsp.heap_extends)
            have hseq := spec_params_zeta_eq_exact hinj hrep_sp
              (tmOExactList_mono ext_0_sp htsp)
              (RomBound.bounded_mono hbd (sub fun c hc' => by rw [hc, hcs]; simp [hc'])) evseq
            have ext_par_u := ext_par_m.trans (evsp.heap_extends.trans evseq.heap_extends)
            have ext_2_u := evpar.heap_extends.trans ext_par_u
            rw [hshape] at evus
            obtain ⟨d3, pa3, us3, hd3, hfn3, hrep_us⟩ := extract_aux_occ_us_spec
              (by omega) ext_par_u hmaj (htm.mono ext_2_u) evus
            have hd3_eq : d3 = d_p := Option.some.inj (hd3.symm.trans hd_p); subst d3
            have hfn3_eq := hfn3.symm.trans hfn_p
            injection hfn3_eq with _ hus3; subst us3
            obtain ⟨hueq, -⟩ := level_list_struct_eq_exact hrep_us
              (htus.mono (ext_0_sp.trans (evseq.heap_extends.trans evus.heap_extends))) evueq
            rcases hne_su with hne_sp | hne_us
            · rw [ite_eq_right hne_sp] at hseq
              rw [hseq, hueq] at opmul
              split at opmul <;> simp [evalBinOp] at opmul
            · rw [ite_eq_right hne_us] at hueq
              rw [hseq, hueq] at opmul
              split at opmul <;> simp [evalBinOp] at opmul
    | .Cons_Recr_other (x_rest := xrest) (v63 := vp) (m64 := m1) (cs74 := cs1) (v101 := vci)
        (m102 := m2) (p109 := pci) (cs115 := cs2) (v679 := vmatch) (m680 := m3) (cs682 := cs3)
        (cs713 := cs4) (v_fgheehtv := vpos1)
        (ld12 := ld) (ev76 := evpa) (ev117 := evci) (ld111 := ldci) (sg687 := sg)
        (hne706 := hne1) (op_ojlhvlfm := op1) (ev715 := evrec) (hc788 := hc) .. =>
      obtain ⟨m', rest', h1, -, hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hcur ld
      injection h1 with h1m h1r; subst h1m h1r
      have hrs_lt : rs.size < 2 ^ 39 := by
        have hlt := repList_length_lt_obs hbd hsub evpa (by rw [hc]; simp) (by simp) hall
        simpa using hlt
      obtain ⟨ext1, -, -, mc, ma, hmc, rma, hma⟩ := L1.projection_addr_spec hall rrba evpa
      rw [fval_natCast (by omega)] at hmc hma
      have hmc' : rs[pos]? = some mc := by rw [← Array.getElem?_toList]; exact hmc
      have hmc_eq : mc = .recr rc := Option.some.inj (hmc'.symm.trans hrc_at)
      subst hmc_eq
      have hma_eq : ixAddr ma = memberAddr (ixAddr rba) pos (.recr rc) := hma
      obtain ⟨ty, tyPtr, rulesPtr, blkPtr, ba', hshape, -, hnp, hni, hnm, hnmi, -,
        hloaded, htm, htyIn, -, -, -⟩ :=
        recrLoad_ofStore ht hwf hS hH hbd hRsub hcl hlv
          (sub fun c hc' => by rw [hc]; simp [hc']) hSrb hcrbE hmuts hrc_at hma_eq rma evci ldci
      have hty_eq : ty = ty_p := Option.some.inj (hloaded.symm.trans hty_p)
      subst ty
      have ext02 := ext1.trans evci.heap_extends
      have ext23 : Heap.Extends m2 m3 := by
        cases sg with
        | Rec_Induct_n1_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ _ =>
          exact (hne1 hr).elim
        | Rec_Induct_n1_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evpar evci2 _ evaeq _ evsp evseq evus evueq _ _ =>
          exact evpar.heap_extends.trans (evci2.heap_extends.trans (evaeq.heap_extends.trans
            (evsp.heap_extends.trans (evseq.heap_extends.trans (evus.heap_extends.trans evueq.heap_extends)))))
        | Rec_Induct_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evpar evci2 _ evaeq _ _ hh _ =>
          subst hh; exact evpar.heap_extends.trans (evci2.heap_extends.trans evaeq.heap_extends)
        | Rec_other_n1_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ _ =>
          exact (hne1 hr).elim
        | Rec_other_n1_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evpar evci2 _ _ evaeq _ evsp evseq evus evueq _ _ =>
          exact evpar.heap_extends.trans (evci2.heap_extends.trans (evaeq.heap_extends.trans
            (evsp.heap_extends.trans (evseq.heap_extends.trans (evus.heap_extends.trans evueq.heap_extends)))))
        | Rec_other_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evpar evci2 _ _ evaeq _ _ hh _ =>
          subst hh; exact evpar.heap_extends.trans (evci2.heap_extends.trans evaeq.heap_extends)
        | other _ _ hh _ => subst hh; exact Heap.Extends.refl _
      -- Rule out `pos = targetIdx`: at `pos = targetIdx`, `sg` MUST return `1`, contradicting `hne1`!
      have hne_pt : pos ≠ targetIdx := by
        intro hpeq; subst hpeq
        have hep_eq : ep = te := Option.some.inj (hep_at.symm.trans htarget)
        rw [hep_eq] at hfn_p hinfo_p haux_p
        cases sg with
        | Rec_Induct_n1_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ _ =>
          exact hne1 hr
        | Rec_other_n1_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ _ =>
          exact hne1 hr
        | other hne _ _ _ => exact hne _ rfl hshape
        | Rec_Induct_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            hv evpar evci2 _ evaeq hne_a _ _ _ =>
          rw [hshape] at hv; injection hv with _ _ hl
          injection hl with _ hl; injection hl with h1 hl; injection hl with h2 hl
          injection hl with h3 hl; injection hl with h4 hl; injection hl with h5 _
          subst h1 h2 h3 h4 h5
          obtain ⟨d', pa, us', hd', hfn', rpa, -⟩ := rec_to_parent_addr_spec (by omega) htm evpar
          have hd_eq : d' = d_p := Option.some.inj (hd'.symm.trans hd_p); subst d'
          have hfn_eq := hfn'.symm.trans hfn_p
          injection hfn_eq with hk _
          have hpa_eq : ixAddr pa = te.addr := hinj hk
          have hsame : pa = tba := ixAddr_inj (hpa_eq.trans htba.symm)
          obtain ⟨hveq, -⟩ := Lib.address_eq_spec evaeq
            (Bytes.repAddressRef_heapMono₂ addrTy evci2.heap_extends rpa)
            (Bytes.repAddressRef_heapMono₂ addrTy (ext02.trans (evpar.heap_extends.trans evci2.heap_extends)) rtba)
          rw [ite_eq_left hsame] at hveq; exact hne_a hveq
        | Rec_other_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            hv evpar evci2 _ _ evaeq hne_a _ _ _ =>
          rw [hshape] at hv; injection hv with _ _ hl
          injection hl with _ hl; injection hl with h1 hl; injection hl with h2 hl
          injection hl with h3 hl; injection hl with h4 hl; injection hl with h5 _
          subst h1 h2 h3 h4 h5
          obtain ⟨d', pa, us', hd', hfn', rpa, -⟩ := rec_to_parent_addr_spec (by omega) htm evpar
          have hd_eq : d' = d_p := Option.some.inj (hd'.symm.trans hd_p); subst d'
          have hfn_eq := hfn'.symm.trans hfn_p
          injection hfn_eq with hk _
          have hpa_eq : ixAddr pa = te.addr := hinj hk
          have hsame : pa = tba := ixAddr_inj (hpa_eq.trans htba.symm)
          obtain ⟨hveq, -⟩ := Lib.address_eq_spec evaeq
            (Bytes.repAddressRef_heapMono₂ addrTy evci2.heap_extends rpa)
            (Bytes.repAddressRef_heapMono₂ addrTy (ext02.trans (evpar.heap_extends.trans evci2.heap_extends)) rtba)
          rw [ite_eq_left hsame] at hveq; exact hne_a hveq
        | Rec_other_n1_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            hv evpar evci2 ldci2 hneI _ _ _ _ _ _ _ hcs =>
          rw [hshape] at hv; injection hv with _ _ hl
          injection hl with _ hl; injection hl with h1 hl; injection hl with h2 hl
          injection hl with h3 hl; injection hl with h4 hl; injection hl with h5 _
          subst h1 h2 h3 h4 h5
          obtain ⟨d', pa, us', hd', hfn', rpa, -⟩ := rec_to_parent_addr_spec (by omega) htm evpar
          have hd_eq : d' = d_p := Option.some.inj (hd'.symm.trans hd_p); subst d'
          have hfn_eq := hfn'.symm.trans hfn_p
          injection hfn_eq with hk _
          have hpa_eq : ixAddr pa = te.addr := hinj hk
          have hSpa : Held R (ixAddr pa) := by
            have hfnIn := addrIn_getAppFn (addrIn_binderDomAfter htyIn hd')
            rw [hfn'] at hfnIn; exact hfnIn (ixAddr pa) rfl
          obtain ⟨-, hOther⟩ := indInfo_of_get_ci hS hH hbd hRsub hcl
            (sub fun c hc' => by rw [hc, hcs]; simp [hc']) hSpa rpa evci2 ldci2
          have hnone := hOther hneI
          rw [hpa_eq, hinfo_p] at hnone; cases hnone
        | Rec_Induct_n1_other _ _ _ _ _ _ _ _ _ _ _ _ m_par _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ _ _ _ _ _ _ _ _ _
            hv evpar evci2 ldci2 evaeq hne0 evsp evseq evus evueq opmul hcs =>
          have htt : te.aux = true := by
            cases h' : te.aux
            · exact (hne0 (auxVal_eq_zero.mpr h')).elim
            · rfl
          rw [hshape] at hv; injection hv with _ _ hl
          injection hl with _ hl; injection hl with h1 hl; injection hl with h2 hl
          injection hl with h3 hl; injection hl with h4 hl; injection hl with h5 _
          subst h1 h2 h3 h4 h5
          obtain ⟨d', pa, us', hd', hfn', rpa, hmaj⟩ := rec_to_parent_addr_spec (by omega) htm evpar
          have hd_eq : d' = d_p := Option.some.inj (hd'.symm.trans hd_p); subst d'
          have hfn_eq := hfn'.symm.trans hfn_p
          injection hfn_eq with hk hus_eq
          have hpa_eq : ixAddr pa = te.addr := hinj hk
          subst us'
          have hSpa : Held R (ixAddr pa) := by
            have hfnIn := addrIn_getAppFn (addrIn_binderDomAfter htyIn hd')
            rw [hfn'] at hfnIn; exact hfnIn (ixAddr pa) rfl
          obtain ⟨hInd, -⟩ := indInfo_of_get_ci hS hH hbd hRsub hcl
            (sub fun c hc' => by rw [hc, hcs]; simp [hc']) hSpa rpa evci2 ldci2
          obtain ⟨info', -, hinfo', -, hnp56, -, -, -, -, hnpEq, -, -, -, -⟩ :=
            hInd _ _ _ _ _ _ _ _ rfl
          rw [hpa_eq, hinfo_p] at hinfo'
          have hinfo_eq := Option.some.inj (Option.some.inj hinfo')
          subst info'
          subst hnpEq
          have ext_par_m := evci2.heap_extends.trans evaeq.heap_extends
          have ext_2_m := evpar.heap_extends.trans ext_par_m
          obtain ⟨d2, hd2, -, hrep_sp, -⟩ := extract_aux_spec_params_spec
            (by omega) hnp56 ext_par_m hmaj
            (RomBound.bounded_mono hbd (sub fun c hc' => by rw [hc, hcs]; simp [hc']))
            (htm.mono ext_2_m) htyIn evsp
          have hd2_eq : d2 = d_p := Option.some.inj (hd2.symm.trans hd_p); subst d2
          rw [haux_p htt] at hrep_sp
          have ext_0_sp := ext02.trans (ext_2_m.trans evsp.heap_extends)
          have hseq := spec_params_zeta_eq_exact hinj hrep_sp
            (tmOExactList_mono ext_0_sp htsp)
            (RomBound.bounded_mono hbd (sub fun c hc' => by rw [hc, hcs]; simp [hc'])) evseq
          have ext_par_u := ext_par_m.trans (evsp.heap_extends.trans evseq.heap_extends)
          have ext_2_u := evpar.heap_extends.trans ext_par_u
          rw [hshape] at evus
          obtain ⟨d3, pa3, us3, hd3, hfn3, hrep_us⟩ := extract_aux_occ_us_spec
            (by omega) ext_par_u hmaj (htm.mono ext_2_u) evus
          have hd3_eq : d3 = d_p := Option.some.inj (hd3.symm.trans hd_p); subst d3
          have hfn3_eq := hfn3.symm.trans hfn_p
          injection hfn3_eq with _ hus3; subst us3
          obtain ⟨hueq, -⟩ := level_list_struct_eq_exact hrep_us
            (htus.mono (ext_0_sp.trans (evseq.heap_extends.trans evus.heap_extends))) evueq
          simp only [↓reduceIte] at hseq hueq
          rw [hseq, hueq] at opmul
          simp only [evalBinOp, mul_one, Except.ok.injEq] at opmul
          exact hne1 opmul.symm
      obtain rfl := binop_add_one_nat op1
      have ext03 := ext02.trans ext23
      exact ih (pos + 1) (by simp at hlen; omega) (by omega) hidx'
        (sub fun c hc' => by rw [hc]; simp [hc'])
        (repList_heapMono₂ _ (fun _ _ _ _ _ h => h) ext03 hall)
        (repList_heapMono₂ _ (fun _ _ _ _ _ h => h) ext03 hrest)
        (Bytes.repAddressRef_heapMono₂ addrTy ext03 rrba)
        (Bytes.repAddressRef_heapMono₂ addrTy ext03 rtba) htba
        (tmOExactList_mono ext03 htsp) (htus.mono ext03) evrec

/-- **`KernelCheck::find_peer_recursor_with_spec`** returns the `targetIdx`-th member address of
`rb` under `RecordFlatAux` and `FlatPeerDistinct`. -/
theorem find_peer_recursor_with_spec_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    {rba tba : Bytes.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {es : List FlatEntry} {targetIdx : Nat} {te : FlatEntry}
    {xrba xtaddr xtsp xtus xself r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    (hSrb : Held R (ixAddr rba)) (hcrbE : recordOf E₀ (ixAddr rba) = some crb)
    (hmuts : crb.info = .muts rs)
    (hRF : RecordFlatAux t E₀ (ixAddr rba) crb rs es)
    (hPD : FlatPeerDistinct es) (htarget : es[targetIdx]? = some te)
    (rrba : Bytes.RepAddressRef addrTy h rba xrba)
    (rtba : Bytes.RepAddressRef addrTy h tba xtaddr) (htba : ixAddr tba = te.addr)
    (htsp : RepList kexprListEnum (TmOExact (Core.keyOf t)) h te.params xtsp)
    (htus : RepKLevelList h te.levels xtus)
    (ev : ObsFn W "KernelCheck::find_peer_recursor_with_spec"
      [xrba, xtaddr, xtsp, xtus, auxVal te.aux, xself] h r h' cs) :
    ∃ (rc_t : Ixon.Recursor) (ma : Bytes.Address),
      rs[targetIdx]? = some (.recr rc_t) ∧
      Bytes.RepAddressRef addrTy h' ma r ∧
      ixAddr ma = memberAddr (ixAddr rba) targetIdx (.recr rc_t) := by
  match Obs.«KernelCheck::find_peer_recursor_with_spec».obs ev with
  | .Muts (m2 := m1) (cs12 := cs1) (x_members := xmem) (cs92 := cs2)
      (ev14 := evld) (ev94 := evwalk) (hc158 := hc) .. =>
    obtain ⟨xm, _, _, _, _, hv, hms⟩ := load_verified_muts_of_record hS
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hcrbE hmuts rrba evld
    injection hv with _ _ hl; injection hl with hm _; injection hm with _ _ hml
    injection hml with hx; subst hx
    have evwalk' : ObsFn W "KernelCheck::find_peer_rec_spec_walk"
        [xmem, xmem, xrba, xtaddr, xtsp, xtus, auxVal te.aux, xself, .field ((0 : Nat) : F)]
        m1 r h' cs2 := by simpa using evwalk
    exact find_peer_rec_spec_walk_spec ht hwf hS hH hbd hRsub hcl hlv hSrb hcrbE hmuts
      hRF hPD htarget rs.toList 0 (by simp) (Nat.zero_le _)
      (fun i m hm => by simpa [← Array.getElem?_toList] using hm)
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hms hms
      (Bytes.repAddressRef_heapMono₂ addrTy evld.heap_extends rrba)
      (Bytes.repAddressRef_heapMono₂ addrTy evld.heap_extends rtba) htba
      (tmOExactList_mono evld.heap_extends htsp) (htus.mono evld.heap_extends) evwalk'
  | .other (cs12 := cs1) (ev14 := evld) (hne159 := hne) (hc166 := hc) .. =>
    obtain ⟨xm, _, _, _, _, hv, -⟩ := load_verified_muts_of_record hS
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hcrbE hmuts rrba evld
    injection hv with _ _ hl; injection hl with hm _
    exact (hne [xm] rfl hm).elim

private theorem build_peer_recs_aux {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    {rba : Bytes.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {fullEs : List FlatEntry}
    (hSrb : Held R (ixAddr rba)) (hcrbE : recordOf E₀ (ixAddr rba) = some crb)
    (hmuts : crb.info = .muts rs)
    (hRF : RecordFlatAux t E₀ (ixAddr rba) crb rs fullEs)
    (hPD : FlatPeerDistinct fullEs) :
    ∀ (cur : List FlatEntry) (off : Nat)
      {xflat xrba xself r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      off + cur.length = fullEs.length →
      (∀ i e, cur[i]? = some e → fullEs[off + i]? = some e) →
      (∀ c ∈ cs, c ∈ rootCalls) →
      RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h cur xflat →
      Bytes.RepAddressRef addrTy h rba xrba →
      ObsFn W "KernelCheck::build_peer_recs" [xflat, xrba, xself] h r h' cs →
      ∃ peers : List Bytes.Address,
        RepList addrListEnum (Bytes.RepAddressRef addrTy) h' peers r ∧
        peers.map ixAddr = (recAddrs (ixAddr rba) rs).drop off := by
  intro cur
  induction cur with
  | nil =>
    intro off xflat xrba xself r h h' cs hlen _ _ hcur _ ev
    match Obs.«KernelCheck::build_peer_recs».obs ev with
    | .Nil (he24 := hr0) (hm23 := hm0) .. =>
      cases hr0; cases hm0
      refine ⟨[], Lib.rep_store_nil h, ?_⟩
      have hge : (recAddrs (ixAddr rba) rs).length ≤ off := by
        simp only [recAddrs, List.length_map, List.length_zipIdx, Array.length_toList]
        simp only [List.length_nil, Nat.add_zero] at hlen
        rw [← hRF.1]; omega
      rw [List.drop_eq_nil_of_le hge]; rfl
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hcur ld
      cases hcons
  | cons e rest ih =>
    intro off xflat xrba xself r h h' cs hlen hidx hsub hcur rrba ev
    match Obs.«KernelCheck::build_peer_recs».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hcur ld
    | .Cons (x_rest := xrest) (x_member_addr := xa) (x_is_aux := xaux) (x_sp := xsp)
        (x_ou := xus) (v82 := vpeer) (m83 := m1) (cs93 := cs1) (v145 := vrest) (m154 := m2)
        (cs162 := cs2) (ld12 := ld) (ev95 := evf) (he140 := hr0) (hm139 := hm0)
        (ev164 := evrec) (hc189 := hc) .. =>
      cases hr0; cases hm0
      obtain ⟨e', rest', h1, he', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hcur ld
      injection h1 with h1e h1r; subst h1e h1r
      obtain ⟨xa', xsp', xus', tba, htup, rtba, htba, htsp, htus⟩ := he'
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
      obtain ⟨rfl, rfl, rfl, rfl⟩ := htup
      have htarget : fullEs[off]? = some e := by simpa using hidx 0 e rfl
      obtain ⟨rc_t, ma, hrc_t, rma, hma⟩ := find_peer_recursor_with_spec_spec
        ht hwf hS hH hbd hRsub hcl hlv (fun c hc' => hsub c (by rw [hc]; simp [hc']))
        hSrb hcrbE hmuts hRF hPD htarget rrba rtba htba htsp htus evf
      have hidx' : ∀ i e', rest[i]? = some e' → fullEs[(off + 1) + i]? = some e' := fun i e' hi => by
        have h1 := hidx (i + 1) e' (by simpa using hi)
        rwa [show off + (i + 1) = (off + 1) + i by omega] at h1
      obtain ⟨peers, hrep_p, hmap_p⟩ := ih (off + 1) (by simp at hlen; omega) hidx'
        (fun c hc' => hsub c (by rw [hc]; simp [hc']))
        (flatList_mono evf.heap_extends hrest)
        (Bytes.repAddressRef_heapMono₂ addrTy evf.heap_extends rrba) evrec
      refine ⟨ma :: peers,
        Lib.rep_store_cons (Bytes.repAddressRef_heapMono₂ addrTy)
          (Bytes.repAddressRef_heapMono₂ addrTy evrec.heap_extends rma) hrep_p, ?_⟩
      have hoff_lt : off < (recAddrs (ixAddr rba) rs).length := by
        simp only [recAddrs, List.length_map, List.length_zipIdx, Array.length_toList]
        have := (Array.getElem?_eq_some_iff.mp hrc_t).1; omega
      rw [List.drop_eq_getElem_cons hoff_lt, List.map_cons, hmap_p]
      apply congrArg (· :: _)
      rw [hma]
      have hget : rs[off]'(by have := (Array.getElem?_eq_some_iff.mp hrc_t).1; exact this) = .recr rc_t :=
        (List.getElem_of_getElem? (by rw [Array.getElem?_toList]; exact hrc_t)).2
      simp only [recAddrs, List.getElem_map, List.getElem_zipIdx, Nat.zero_add,
        Array.getElem_toList, hget]

/-- **`KernelCheck::build_peer_recs`** produces `recAddrs (ixAddr rba) rs` unconditionally under
`UsedClosed R`, `RecordFlatAux`, and `FlatPeerDistinct`. -/
theorem build_peer_recs_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    {rba : Bytes.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {es : List FlatEntry} {xflat xrba xself r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    (hSrb : Held R (ixAddr rba)) (hcrbE : recordOf E₀ (ixAddr rba) = some crb)
    (hmuts : crb.info = .muts rs)
    (hRF : RecordFlatAux t E₀ (ixAddr rba) crb rs es)
    (hPD : FlatPeerDistinct es)
    (hes : RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h es xflat)
    (rrba : Bytes.RepAddressRef addrTy h rba xrba)
    (ev : ObsFn W "KernelCheck::build_peer_recs" [xflat, xrba, xself] h r h' cs) :
    ∃ peers : List Bytes.Address,
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h' peers r ∧
      peers.map ixAddr = recAddrs (ixAddr rba) rs := by
  simpa using build_peer_recs_aux ht hwf hS hH hbd hRsub hcl hlv hSrb hcrbE hmuts hRF hPD
    es 0 (by omega) (fun i e hi => by simpa using hi) hsub hes rrba ev

/-! ## Section 4: Inductive hypotheses, minor premises, motives, and recursor type -/

private theorem addrIn_appBVarsDown {S : _root_.Address → Prop} {κ : _root_.Address → KKey}
    {H : KExpr} {n : Nat} (hH : AddrIn S κ H) :
    AddrIn S κ (appBVarsDown H n) :=
  addrIn_appSpine hH (fun _ hx => by simp only [List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; trivial)

/-- **`KernelCheck::build_ih_doms`** refines `ihDoms rm norm fop motiveBase nFields minorSaved elim k ri`
on `TmOExact`, preserving `AddrIn S κ`. -/
theorem build_ih_doms_spec {S : _root_.Address → Prop} {κ : _root_.Address → KKey}
    {rm fop : List Nat} {norm : List KExpr}
    {motiveBase nFields minorSaved : Nat} {elim : KLevel}
    {xrm xnorm xfop xelim : SourceValue F}
    (hmb : motiveBase + fop.length ≤ minorSaved)
    (hbound : minorSaved + nFields + rm.length < 4611686018427387904)
    (hnorm_len : norm.length = nFields)
    (hfop56 : ∀ n ∈ fop, n < 72057594037927936)
    (hrm_lt : ∀ m ∈ rm, m < fop.length) :
    ∀ (ri : List Nat) (k : Nat) {xri r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      k + ri.length = rm.length →
      (∀ fi ∈ ri, fi < nFields) →
      Bounded cs →
      RepList fieldListEnum RepNatField h ri xri →
      RepList fieldListEnum RepNatField h rm xrm →
      RepList kexprListEnum (TmOExact κ) h norm xnorm →
      (∀ e ∈ norm, AddrIn S κ e) →
      RepList fieldListEnum RepNatField h fop xfop →
      RepKLevel h elim xelim →
      ObsFn W "KernelCheck::build_ih_doms"
        [xri, xrm, xnorm, xfop, .field (motiveBase : F), .field (nFields : F),
          .field (minorSaved : F), .field (k : F), xelim] h r h' cs →
      ∃ ihs : List KExpr,
        ihDoms rm norm fop motiveBase nFields minorSaved elim k ri = some ihs ∧
        RepList kexprListEnum (TmOExact κ) h' ihs r ∧
        (∀ e ∈ ihs, AddrIn S κ e) := by
  intro ri
  induction ri with
  | nil =>
    intro k xri r h h' cs _ _ _ hri _ _ _ _ _ ev
    match Obs.«KernelCheck::build_ih_doms».obs ev with
    | .Nil (he24 := hr0) (hm23 := hm0) .. =>
      cases hr0; cases hm0
      exact ⟨[], rfl, Lib.rep_store_nil h, fun _ hm => nomatch hm⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hri ld
      cases hcons
  | cons fieldIdx rest ih =>
    intro k xri r h h' cs hklen hfi_lt hbnd hri hrm hnorm hnormIn hfop helim ev
    have bnd : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    match Obs.«KernelCheck::build_ih_doms».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hri ld
    | .Cons (x_field_idx := xfi) (x_rest := xrest) (v46 := vmem) (m47 := m1) (cs57 := cs1)
        (v83 := vtnp) (m84 := m2) (cs94 := cs2) (v120 := vdepth) (x128 := x128)
        (v147 := vdom) (m148 := m3) (cs158 := cs3) (v177 := vdomL) (m178 := m4) (cs188 := cs4)
        (v192 := vlift) (x207 := x207) (m233 := m5) (cs244 := cs5)
        (x_forall_doms := xfds) (x_inner_body := xinner) (v271 := vnfds) (m272 := m6)
        (cs282 := cs6) (v293 := vinnerD) (v311 := vmotB) (x319 := x319) (y320 := y320)
        (v346 := vfldB) (x354 := x354) (y355 := y355) (m382 := m7) (cs_tifcvrfj := cs7)
        (x_dom_args := xdargs) (v420 := vidxArgs) (m421 := m8) (cs431 := cs8)
        (m451 := m9) (v473 := vwithIdx) (m474 := m10) (cs484 := cs9)
        (m504 := m11) (v526 := vfldApp) (m527 := m12) (cs537 := cs10)
        (m564 := m13) (v594 := vih) (m595 := m14) (cs605 := cs11)
        (v641 := vrest) (m650 := m15) (cs658 := cs12) (v668 := vk1)
        (ld12 := ld) (ev59 := evrm) (ev96 := evfop) (op143 := op_d1) (op135 := op_d2)
        (ev160 := evnorm) (op222 := op_l1) (op214 := op_l2) (ev190 := evlift)
        (ev246 := evpeel) (ev284 := evlen) (op308 := op_id)
        (op334 := op_m1) (op343 := op_m2) (op326 := op_m3)
        (op369 := op_f1) (op378 := op_f2) (op361 := op_f3)
        (ev_pexuhviy := evsp) (ev433 := evdrop) (hm461 := hm_b1) (ev486 := evapp1)
        (hm514 := hm_b2) (ev539 := evxs) (hm574 := hm_ap) (ev607 := evwrap)
        (he636 := hr0) (hm635 := hm0) (op732 := opk1) (ev660 := evrec) (hc741 := hc) .. =>
      cases hr0; cases hm0
      obtain ⟨fi', rest', h1, hfi, hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hri ld
      injection h1 with h1f h1r; subst h1f h1r
      rw [hfi] at evnorm op_l1 op_f2 hc
      have hfi_cur : fieldIdx < nFields := hfi_lt fieldIdx (List.mem_cons_self ..)
      have hk_lt : k < rm.length := by simp only [List.length_cons] at hklen; omega
      obtain ⟨hm1, hrm_res⟩ := field_lookup_or_default_spec evrm hrm
      subst m1
      rw [fval_natCast (by omega)] at hrm_res
      obtain ⟨memIdx, hrm_k, rfl⟩ : ∃ m, rm[k]? = some m ∧ vmem = .field (m : F) := by
        rcases hrm_res with ⟨x, hx, hv⟩ | ⟨heq, _⟩
        · exact ⟨x, hx, hv⟩
        · omega
      have hmem_lt : memIdx < fop.length := hrm_lt memIdx (List.mem_of_getElem? hrm_k)
      obtain ⟨hm2, hfop_res⟩ := field_lookup_or_default_spec evfop hfop
      subst m2
      rw [fval_natCast (by omega)] at hfop_res
      obtain ⟨tnp, hfop_m, rfl⟩ : ∃ x, fop[memIdx]? = some x ∧ vtnp = .field (x : F) := by
        rcases hfop_res with ⟨x, hx, hv⟩ | ⟨heq, _⟩
        · exact ⟨x, hx, hv⟩
        · omega
      have htnp56 : tnp < 72057594037927936 := hfop56 tnp (List.mem_of_getElem? hfop_m)
      obtain rfl := binop_add_nat op_d1
      obtain rfl := binop_add_nat op_d2
      obtain ⟨⟨dom, hnorm_fi, hdom⟩, hm3⟩ := kexpr_lookup_spec evnorm hnorm
      subst m3
      rw [fval_natCast (by omega)] at hnorm_fi
      have hdomIn : AddrIn S κ dom := hnormIn dom (List.mem_of_getElem? hnorm_fi)
      obtain rfl := binop_sub_nat (by omega) op_l1
      obtain rfl := binop_add_nat op_l2
      have evlift' : ObsFn W "KernelSubst::expr_lift"
          [vdom, .field ((nFields - fieldIdx + k : Nat) : F), .field ((0 : Nat) : F)]
          h vdomL m4 cs4 := by simpa using evlift
      have hdomL := expr_lift_tmOExact (by omega) (by decide)
        (bnd fun c hc' => by rw [hc]; simp [hc']) hdom evlift'
      have hdomLIn : AddrIn S κ (dom.liftLooseBVars (nFields - fieldIdx + k) 0) :=
        addrIn_liftLooseBVars _ hdomIn
      obtain ⟨xl, xb, htupP, ext45, hfds, hinner⟩ := peel_leading_foralls_spec evpeel
        (bnd fun c hc' => by rw [hc]; simp [hc']) hdomL
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupP
      obtain ⟨rfl, rfl⟩ := htupP
      obtain ⟨rfl, hm6⟩ := kexpr_length_spec evlen hfds
      subst m6
      have hfds_lt : (peelAll (dom.liftLooseBVars (nFields - fieldIdx + k) 0)).1.length < 2 ^ 39 :=
        repList_length_lt_obs hbnd (fun _ h => h) evlen (by rw [hc]; simp) (by simp) hfds
      set domL := dom.liftLooseBVars (nFields - fieldIdx + k) 0
      set fds := (peelAll domL).1
      set inner := (peelAll domL).2
      set innerDepth := minorSaved + nFields + k + fds.length
      have ⟨hfdsIn, hinnerIn⟩ := addrIn_peelAll hdomLIn
      obtain rfl := binop_add_nat op_id
      have hinnerD_ge : 1 ≤ innerDepth := by omega
      have hinnerD_lt : innerDepth < 9223372036854775808 := by omega
      obtain rfl := binop_sub_one_nat hinnerD_ge op_m1
      obtain rfl := binop_add_nat op_m2
      obtain rfl := binop_sub_nat (by omega) op_m3
      obtain rfl := binop_sub_one_nat hinnerD_ge op_f1
      obtain rfl := binop_add_nat op_f2
      obtain rfl := binop_sub_nat (by omega) op_f3
      obtain ⟨-, -, hdargs⟩ := collect_spine_zeta_spec hinner
        (bnd fun c hc' => by rw [hc]; simp [hc']) evsp
      obtain ⟨-, hidxArgs, hm8⟩ := kexpr_drop_spec evdrop hdargs
      subst m8
      rw [fval_natCast (by omega)] at hidxArgs
      have hidxArgsIn : ∀ e ∈ inner.getAppArgs.drop tnp, AddrIn S κ e :=
        fun e he => addrIn_getAppArgs hinnerIn e (List.mem_of_mem_drop he)
      have ext_m7_m9 : Heap.Extends m7 m9 := by rw [hm_b1]; exact Heap.Extends.snoc _ _
      have hb1 : TmOExact κ m9 (.bvar (innerDepth - 1 - (motiveBase + memIdx)))
          (.ptr (.enum kexprEnum) m7.length) := by
        rw [hm_b1]; exact tmOExact_bvar_cell (by omega)
      have hwithIdx := apply_spine_expr_spec (inner.getAppArgs.drop tnp) evapp1 hb1
        (tmOExactList_mono ext_m7_m9 hidxArgs)
      have ext_m10_m11 : Heap.Extends m10 m11 := by rw [hm_b2]; exact Heap.Extends.snoc _ _
      have hb2 : TmOExact κ m11 (.bvar (innerDepth - 1 - (minorSaved + fieldIdx)))
          (.ptr (.enum kexprEnum) m10.length) := by
        rw [hm_b2]; exact tmOExact_bvar_cell (by omega)
      have hfldApp := build_apply_xs_spec (by omega) evxs hb2
      have ext_m12_m13 : Heap.Extends m12 m13 := by rw [hm_ap]; exact Heap.Extends.snoc _ _
      have happ_tm : TmOExact κ m13
          (.app (appSpine (.bvar (innerDepth - 1 - (motiveBase + memIdx))) (inner.getAppArgs.drop tnp))
            (appBVarsDown (.bvar (innerDepth - 1 - (minorSaved + fieldIdx))) fds.length))
          (.ptr (.enum kexprEnum) m12.length) := by
        obtain ⟨k1, r1⟩ := hwithIdx.mono (ext_m10_m11.trans (evxs.heap_extends.trans ext_m12_m13))
        obtain ⟨k2, r2⟩ := hfldApp.mono ext_m12_m13
        exact ⟨max k1 k2, .app (by rw [hm_ap]; simp)
          (tmExact_depth_le r1 _ (Nat.le_max_left _ _))
          (tmExact_depth_le r2 _ (Nat.le_max_right _ _))⟩
      have ext_m5_m13 : Heap.Extends m5 m13 :=
        evsp.heap_extends.trans (ext_m7_m9.trans
          (evapp1.heap_extends.trans (ext_m10_m11.trans (evxs.heap_extends.trans ext_m12_m13))))
      have ext_0_m13 : Heap.Extends h m13 :=
        evlift.heap_extends.trans (ext45.trans ext_m5_m13)
      have hih_tm := wrap_foralls_spec fds evwrap happ_tm (tmOExactList_mono ext_m5_m13 hfds)
        (helim.mono ext_0_m13)
      have ext_0_m14 := ext_0_m13.trans evwrap.heap_extends
      obtain rfl := binop_add_one_nat opk1
      obtain ⟨ihs, hihs, hrep_ihs, hihsIn⟩ := ih (k + 1)
        (by simp only [List.length_cons] at hklen; omega)
        (fun fi hfi => hfi_lt fi (List.mem_cons_of_mem _ hfi))
        (bnd fun c hc' => by rw [hc]; simp [hc'])
        (fieldList_mono ext_0_m14 hrest) (fieldList_mono ext_0_m14 hrm)
        (tmOExactList_mono ext_0_m14 hnorm) hnormIn (fieldList_mono ext_0_m14 hfop)
        (helim.mono ext_0_m14) evrec
      have hheadIn : AddrIn S κ (wrapForalls
          (.app (appSpine (.bvar (innerDepth - 1 - (motiveBase + memIdx))) (inner.getAppArgs.drop tnp))
            (appBVarsDown (.bvar (innerDepth - 1 - (minorSaved + fieldIdx))) fds.length))
          fds elim) := by
        refine addrIn_wrapForalls (fun d hd => hfdsIn d hd) ⟨?_, ?_⟩
        · exact addrIn_appSpine trivial hidxArgsIn
        · exact addrIn_appBVarsDown trivial
      refine ⟨_ :: ihs, ?_, Lib.rep_store_cons tmOExact_heapMono₂ (hih_tm.mono evrec.heap_extends) hrep_ihs, ?_⟩
      · simp only [ihDoms, hnorm_fi, hrm_k, hfop_m, Option.getD_some, hihs, Option.map_some]
        rfl
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact hheadIn
        · exact hihsIn e he

private theorem addrIn_liftIndices {S : _root_.Address → Prop} {κ : _root_.Address → KKey}
    {ds : List KExpr} {shift : Nat} (h : ∀ d ∈ ds, AddrIn S κ d) :
    ∀ e ∈ liftIndices ds shift, AddrIn S κ e := by
  intro e he
  simp only [liftIndices, List.mem_map] at he
  obtain ⟨⟨d, idx⟩, hmem, rfl⟩ := he
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hmem
  simp only [List.length_zipIdx, List.getElem_zipIdx] at hj hget
  have hd : d ∈ ds := by rw [← (Prod.mk.inj hget).1]; exact List.getElem_mem hj
  exact addrIn_liftLooseBVars shift (h d hd)

private theorem addrIn_appBVarsDec {S : _root_.Address → Prop} {κ : _root_.Address → KKey}
    {H : KExpr} {n start : Nat} (hH : AddrIn S κ H) :
    AddrIn S κ (appBVarsDec H n start) :=
  addrIn_appSpine hH (fun _ hx => by simp only [List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; trivial)

private theorem addrIn_fieldBVars {S : _root_.Address → Prop} {κ : _root_.Address → KKey}
    {H : KExpr} {nf nb : Nat} (hH : AddrIn S κ H) :
    AddrIn S κ (fieldBVars H nf nb) :=
  addrIn_appSpine hH (fun _ hx => by simp only [List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; trivial)

private theorem addrIn_majorParams {S : _root_.Address → Prop} {κ : _root_.Address → KKey}
    {H : KExpr} {n depth : Nat} (hH : AddrIn S κ H) :
    AddrIn S κ (majorParams H n depth) :=
  addrIn_appSpine hH (fun _ hx => by simp only [List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; trivial)

private theorem addrIn_conclIndices {S : _root_.Address → Prop} {κ : _root_.Address → KKey}
    {H : KExpr} {n : Nat} (hH : AddrIn S κ H) :
    AddrIn S κ (conclIndices H n) :=
  addrIn_appSpine hH (fun _ hx => by simp only [List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; trivial)

private theorem addrIn_specParamsLifted {S : _root_.Address → Prop} {κ : _root_.Address → KKey}
    {H : KExpr} {sp : List KExpr} {depth : Nat} (hH : AddrIn S κ H) (hsp : ∀ e ∈ sp, AddrIn S κ e) :
    AddrIn S κ (specParamsLifted H sp depth) :=
  addrIn_appSpine hH (fun _ hx => by
    simp only [List.mem_map] at hx; obtain ⟨e, he, rfl⟩ := hx
    exact addrIn_liftLooseBVars depth (hsp e he))

private theorem addrIn_ctorAppParams {S : _root_.Address → Prop} {κ : _root_.Address → KKey}
    {H : KExpr} {nrp depthNow : Nat} {aux : Bool} {sp : List KExpr}
    (hH : AddrIn S κ H) (hsp : ∀ e ∈ sp, AddrIn S κ e) :
    AddrIn S κ (ctorAppParams H nrp depthNow aux sp) := by
  cases aux
  · exact addrIn_appBVarsDec hH
  · exact addrIn_specParamsLifted hH hsp

/-- **`KernelCheck::build_minor_at_depth`** refines `minorAt (ReconView.ofStore t E₀)` at
`Eventually` on `TmOExact`, preserving `AddrIn (Held R)`. -/
theorem build_minor_at_depth_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    (hM : ModeledAnswers rootCalls (Held R) (ReconView.ofStore t E₀))
    {es : List FlatEntry} {fop : List Nat} {ca : Bytes.Address} {cty : KExpr}
    {nOwn nrp nMot prevMinors motiveBase selfMemIdx : Nat}
    {aux : Bool} {sp : List KExpr} {us : List KLevel} {elim : KLevel}
    {xrc xca xcty xsp xus xflat xfop xelim r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    (hnOwn : nOwn < 72057594037927936) (hnrp : nrp < 72057594037927936)
    (hnp_ok : ∀ i, i < nOwn → ¬ (aux = true ∧ i < sp.length) → i < nrp)
    (hnMot : nMot = es.length) (hprev : prevMinors < 2 ^ 39)
    (hmBase : motiveBase = nrp) (hself : selfMemIdx < nMot)
    (hfop_len : fop.length = es.length) (hfop56 : ∀ n ∈ fop, n < 72057594037927936)
    (hSca : Held R (ixAddr ca))
    (rca : Bytes.RepAddressRef addrTy h ca xca)
    (hcty : TmOExact (Core.keyOf t) h cty xcty) (hctyIn : AddrIn (Held R) (Core.keyOf t) cty)
    (hsp : RepList kexprListEnum (TmOExact (Core.keyOf t)) h sp xsp)
    (hspIn : ∀ e ∈ sp, AddrIn (Held R) (Core.keyOf t) e)
    (hus : RepKLevelList h us xus)
    (hes : RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h es xflat)
    (hfop : RepList fieldListEnum RepNatField h fop xfop)
    (helim : RepKLevel h elim xelim)
    (ev : ObsFn W "KernelCheck::build_minor_at_depth"
      [xrc, xca, xcty, .field (nOwn : F), auxVal aux, xsp, xus, xflat, xfop,
        .field (nrp : F), .field (nMot : F), .field (prevMinors : F),
        .field (motiveBase : F), .field (selfMemIdx : F), xelim] h r h' cs) :
    ∃ M : KExpr,
      Eventually (fun f => minorAt (ReconView.ofStore t E₀) f es fop
        (Core.keyOf t (ixAddr ca)) cty nOwn aux sp us nrp nMot prevMinors motiveBase selfMemIdx
        elim = some M) ∧
      TmOExact (Core.keyOf t) h' M r ∧
      AddrIn (Held R) (Core.keyOf t) M := by
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → ∀ c ∈ cs', c ∈ rootCalls :=
    fun hs c hc => hsub c (hs c hc)
  have bnd : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → Bounded cs' :=
    fun hs => RomBound.bounded_mono hbd (sub hs)
  have hinj : Function.Injective (Core.keyOf t) := fun _ _ he => Core.keyOf_inj hwf he
  have hA : AddrOf (Core.keyOf t) (ReconView.ofStore t E₀) := addrOf_ofStore (E₀ := E₀) hwf
  have hD : DefnAnswers rootCalls (Held R) (Core.keyOf t) (ReconView.ofStore t E₀) :=
    defnAnswers_ofStore ht hwf hS hH hbd hRsub hcl hlv
  have hI : IndAnswers rootCalls (Held R) (Core.keyOf t) (ReconView.ofStore t E₀) :=
    indAnswers_ofStore ht hwf hS hH hbd hRsub hcl hlv
  have hC : CtorOfAnswers rootCalls (Held R) (ReconView.ofStore t E₀) :=
    ctorOfAnswers_ofStore hS hH hbd hRsub hcl
  match Obs.«KernelCheck::build_minor_at_depth».obs ev with
  | .run (v1 := vctyI) (m2 := m1) (cs12 := cs1) (v31 := vminSaved) (x39 := x39) (v58 := vbelow)
      (v76 := vptypes) (m77 := m2) (cs87 := cs2) (v114 := vafter) (m115 := m3) (cs125 := cs3)
      (m199 := m4) (cs210 := cs4) (m245 := m3a) (m258 := m3b) (m271 := m3c) (m284 := m3d)
      (x_pf_doms := xpfd) (x_rec_indices := xri) (x_rec_member_idxs := xrm)
      (x_pf_ret := xret) (x_pf_norm := xnorm)
      (v346 := vnf) (m347 := m5) (cs357 := cs5) (v368 := vdomsL) (m369 := m6) (cs379 := cs6)
      (v405 := vnormL) (m406 := m7) (cs416 := cs7) (v442 := vretL) (m443 := m8) (cs453 := cs8)
      (v480 := vnri) (m481 := m9) (cs491 := cs9) (v502 := vnb) (v520 := vdepthNow)
      (m539 := m10) (cs_craqfzwq := cs10) (x_ret_args := xretArgs)
      (v577 := vretDrop) (m578 := m11) (cs588 := cs11) (v607 := vretIdx) (m608 := m12) (cs618 := cs12)
      (v644 := vmotB) (x652 := x652) (y653 := y653) (m680 := m13)
      (v702 := vwithIdx) (m703 := m14) (cs713 := cs13) (m733 := m15)
      (v763 := vctorP) (m764 := m16) (cs774 := cs14) (v825 := vctorApp) (m826 := m17) (cs836 := cs15)
      (m871 := m18) (v901 := vih) (m902 := m19) (cs912 := cs16)
      (v986 := vw1) (m987 := m20) (cs997 := cs17) (cs1027 := cs18)
      (ev14 := evinst) (op54 := op_ms1) (op46 := op_ms2) (op73 := op_bel)
      (ev89 := evrpc) (ev127 := evpeel)
      (hm253 := hm3a) (hm266 := hm3b) (hm279 := hm3c) (hm292 := hm3d) (ev212 := evwfc)
      (ev359 := evlen1) (ev381 := evli1) (ev418 := evli2) (ev455 := evliftRet)
      (ev493 := evlen2) (op517 := op_nb) (op535 := op_dn)
      (ev_vhmrnmut := evsp) (ev590 := evdrop) (ev620 := evle)
      (op667 := op_mb1) (op676 := op_mb2) (op659 := op_mb3)
      (hm690 := hm13) (ev715 := evapp1) (hm743 := hm15) (ev776 := evcp) (ev838 := evfb)
      (hm881 := hm18) (ev914 := ovih) (ev999 := evw1) (ev1029 := evw2) (hc1054 := hc) .. =>
    have hes_lt : es.length < 2 ^ 39 :=
      repList_length_lt_obs hbd hsub evrpc (by rw [hc]; simp) (by simp)
        (flatList_mono evinst.heap_extends hes)
    have hctyI := expr_inst_levels_tmOExact (bnd fun c hc' => by rw [hc]; simp [hc']) hcty hus evinst
    have hctyIIn : AddrIn (Held R) (Core.keyOf t) (exprInstLevels us cty) :=
      addrIn_exprInstLevels hctyIn
    obtain rfl := binop_add_nat op_ms1
    obtain rfl := binop_add_nat op_ms2
    obtain rfl := binop_add_nat op_bel
    have ext02 := evinst.heap_extends.trans evrpc.heap_extends
    have evpeel' : ObsFn W "KernelCheck::peel_ctor_params_subst"
        [xrc, vctyI, .field (nOwn : F), .field (nrp : F), .field ((0 : Nat) : F),
          auxVal aux, xsp, .field ((0 : Nat) : F), vptypes] m2 vafter m3 cs3 := by simpa using evpeel
    have hsp_lt : sp.length < 2 ^ 39 :=
      repList_length_lt_obs hbd hsub evpeel' (by rw [hc]; simp) (by simp)
        (tmOExactList_mono ext02 hsp)
    obtain ⟨ext23, after, hafter, hafterIn, hev_peel⟩ :=
      peel_ctor_params_subst_spec hA hD hI hC hM (by omega) (by decide) (by omega) hspIn
        nOwn 0 (by omega) (fun i _ hi hni => hnp_ok i (by omega) hni)
        evpeel' (bnd fun c hc' => by rw [hc]; simp [hc']) (sub fun c hc' => by rw [hc]; simp [hc'])
        (hctyI.mono evrpc.heap_extends) hctyIIn (tmOExactList_mono ext02 hsp)
    have ext3a : Heap.Extends m3 m3a := by rw [hm3a]; exact Heap.Extends.snoc _ _
    have ext3b : Heap.Extends m3a m3b := by rw [hm3b]; exact Heap.Extends.snoc _ _
    have ext3c : Heap.Extends m3b m3c := by rw [hm3c]; exact Heap.Extends.snoc _ _
    have ext3d : Heap.Extends m3c m3d := by rw [hm3d]; exact Heap.Extends.snoc _ _
    have ext3_d := ext3a.trans (ext3b.trans (ext3c.trans ext3d))
    have ext0_3d := ext02.trans (ext23.trans ext3_d)
    have hnil1 : RepList kexprListEnum (TmOExact (Core.keyOf t)) m3d []
        (.ptr (.enum kexprListEnum) m3.length) :=
      tmOExactList_mono (ext3b.trans (ext3c.trans ext3d)) (by rw [hm3a]; exact Lib.rep_store_nil m3)
    have hnil2 : RepList fieldListEnum RepNatField m3d []
        (.ptr (.enum fieldListEnum) m3a.length) :=
      fieldList_mono (ext3c.trans ext3d) (by rw [hm3b]; exact Lib.rep_store_nil m3a)
    have hnil3 : RepList fieldListEnum RepNatField m3d []
        (.ptr (.enum fieldListEnum) m3b.length) :=
      fieldList_mono ext3d (by rw [hm3c]; exact Lib.rep_store_nil m3b)
    have hnil4 : RepList kexprListEnum (TmOExact (Core.keyOf t)) m3d []
        (.ptr (.enum kexprListEnum) m3c.length) := by
      rw [hm3d]; exact Lib.rep_store_nil m3c
    have hnil1U : RepList kexprListEnum (fun _ (_ : Unit) _ => True) m3d []
        (.ptr (.enum kexprListEnum) m3.length) :=
      repList_heapMono₂ kexprListEnum (fun _ _ _ _ _ t => t) (ext3b.trans (ext3c.trans ext3d))
        (by rw [hm3a]; exact Lib.rep_store_nil m3)
    have evwfc' : ObsFn W "KernelCheck::walk_fields_classify"
        [xrc, vafter, xflat, .ptr (.enum kexprListEnum) m3.length,
          .ptr (.enum fieldListEnum) m3a.length, .ptr (.enum fieldListEnum) m3b.length,
          .ptr (.enum kexprListEnum) m3c.length, .field 0, .field ((0 : Nat) : F), vptypes]
        m3d (.tuple [xpfd, xri, xrm, xret, xnorm]) m4 cs4 := by simpa using evwfc
    have hpeel_len : (peelAll after).1.length < 2 ^ 39 := by
      obtain ⟨_, _, _, _, _, dsU, htupU, hlenU, hrepU⟩ :=
        walk_fields_classify_doms_len evwfc' (bnd fun c hc' => by rw [hc]; simp [hc'])
          (hafter.mono ext3_d) hnil1U
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupU
      obtain ⟨rfl, -, -, -, -⟩ := htupU
      have hltU := repList_length_lt_obs hbd hsub evlen1 (by rw [hc]; simp) (by simp) hrepU
      simp only [List.length_nil, Nat.zero_add] at hlenU; omega
    obtain ⟨ext_3d_4, _, _, _, _, _, pfDoms, pfNorm, ri, rm, pfRet, htup,
        hpfd, hri, hrm, hret, hnorm, hpfdIn, hretIn, hnormIn, hev_wfc⟩ :=
      walk_fields_classify_nil_spec hinj hA hD hI hC hM (by omega) evwfc'
        (bnd fun c hc' => by rw [hc]; simp [hc']) (sub fun c hc' => by rw [hc]; simp [hc'])
        (hafter.mono ext3_d) hafterIn (flatList_mono ext0_3d hes) hnil1 hnil2 hnil3 hnil4
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := htup
    have ⟨f_wfc, hf_wfc⟩ := hev_wfc
    obtain ⟨hnorm_len, hrm_len, hri_lt, hrm_lt⟩ :=
      fieldsClassify_lengths_and_bounds after 0 pfDoms pfNorm ri rm pfRet (hf_wfc f_wfc (Nat.le_refl _))
    simp only [Nat.zero_add] at hri_lt
    obtain ⟨rfl, hm5⟩ := kexpr_length_spec evlen1 hpfd
    subst m5
    have hnf_lt : pfDoms.length < 2 ^ 39 :=
      repList_length_lt_obs hbd hsub evlen1 (by rw [hc]; simp) (by simp) hpfd
    have evli1' : ObsFn W "KernelCheck::list_lift_indices"
        [xpfd, .field ((nMot + prevMinors : Nat) : F), .field ((0 : Nat) : F)] m4 vdomsL m6 cs6 := by
      simpa using evli1
    have hdomsL := list_lift_indices_spec (by omega) pfDoms 0 (by omega) evli1'
      (bnd fun c hc' => by rw [hc]; simp [hc']) hpfd
    have evli2' : ObsFn W "KernelCheck::list_lift_indices"
        [xnorm, .field ((nMot + prevMinors : Nat) : F), .field ((0 : Nat) : F)] m6 vnormL m7 cs7 := by
      simpa using evli2
    have hnormL := list_lift_indices_spec (by omega) pfNorm 0 (by omega) evli2'
      (bnd fun c hc' => by rw [hc]; simp [hc']) (tmOExactList_mono evli1.heap_extends hnorm)
    have hretL := expr_lift_tmOExact (by omega) (by omega)
      (bnd fun c hc' => by rw [hc]; simp [hc'])
      (hret.mono (evli1.heap_extends.trans evli2.heap_extends)) evliftRet
    have hretLIn : AddrIn (Held R) (Core.keyOf t) (pfRet.liftLooseBVars (nMot + prevMinors) pfDoms.length) :=
      addrIn_liftLooseBVars _ hretIn
    have ext48 := evli1.heap_extends.trans (evli2.heap_extends.trans evliftRet.heap_extends)
    obtain ⟨rfl, hm9⟩ := field_length_spec evlen2 (fieldList_mono ext48 hri)
    subst m9
    have hri_len_lt : ri.length < 2 ^ 39 :=
      repList_length_lt_obs hbd hsub evlen2 (by rw [hc]; simp) (by simp) (fieldList_mono ext48 hri)
    obtain rfl := binop_add_nat op_nb
    obtain rfl := binop_add_nat op_dn
    set nFields := pfDoms.length
    set minorSaved := nrp + nMot + prevMinors
    set below := nMot + prevMinors
    set depthNow := minorSaved + (nFields + ri.length)
    obtain ⟨-, -, hretArgs⟩ := collect_spine_zeta_spec hretL
      (bnd fun c hc' => by rw [hc]; simp [hc']) evsp
    obtain ⟨-, hretDrop, hm11⟩ := kexpr_drop_spec evdrop hretArgs
    subst m11
    rw [fval_natCast (by omega)] at hretDrop
    have evle' : ObsFn W "KernelCheck::list_lift_each"
        [vretDrop, .field (ri.length : F), .field ((0 : Nat) : F)] m10 vretIdx m12 cs12 := by
      simpa using evle
    obtain ⟨hretIdx, hretIdxIn⟩ := list_lift_each_spec (by omega) (by decide) _ evle'
      (bnd fun c hc' => by rw [hc]; simp [hc']) hretDrop
      (fun e he => addrIn_getAppArgs hretLIn e (List.mem_of_mem_drop he))
    have hdn_ge : 1 ≤ depthNow := by omega
    obtain rfl := binop_sub_one_nat hdn_ge op_mb1
    obtain rfl := binop_add_nat op_mb2
    obtain rfl := binop_sub_nat (by omega) op_mb3
    have ext_12_13 : Heap.Extends m12 m13 := by rw [hm13]; exact Heap.Extends.snoc _ _
    have hbmot : TmOExact (Core.keyOf t) m13
        (.bvar (depthNow - 1 - (motiveBase + selfMemIdx))) (.ptr (.enum kexprEnum) m12.length) := by
      rw [hm13]; exact tmOExact_bvar_cell (by omega)
    have hwithIdx := apply_spine_expr_spec
      (((pfRet.liftLooseBVars (nMot + prevMinors) pfDoms.length).getAppArgs.drop nOwn).map
        (Ix.Kernel.Expr.liftLooseBVars ri.length 0))
      evapp1 hbmot (tmOExactList_mono ext_12_13 hretIdx)
    have ext_0_4 := ext0_3d.trans ext_3d_4
    have ext_4_14 := ext48.trans (evsp.heap_extends.trans (evle.heap_extends.trans
      (ext_12_13.trans evapp1.heap_extends)))
    have ext_14_15 : Heap.Extends m14 m15 := by rw [hm15]; exact Heap.Extends.snoc _ _
    have ext_0_15 := ext_0_4.trans (ext_4_14.trans ext_14_15)
    have hconstC : TmOExact (Core.keyOf t) m15 (.const (Core.keyOf t (ixAddr ca)) us)
        (.ptr (.enum kexprEnum) m14.length) :=
      ⟨0, .const (by rw [hm15]; simp)
        (Bytes.repAddressRef_heapMono₂ addrTy ext_0_15 rca) (hus.mono ext_0_15)⟩
    have hctorP := build_ctor_app_params_spec (by omega) hdn_ge (by omega)
      (bnd fun c hc' => by rw [hc]; simp [hc']) hconstC (tmOExactList_mono ext_0_15 hsp) evcp
    have hctorApp := build_apply_field_bvars_spec (by omega) (by omega) evfb hctorP
    have ext_17_18 : Heap.Extends m17 m18 := by rw [hm18]; exact Heap.Extends.snoc _ _
    have ext_14_18 := ext_14_15.trans (evcp.heap_extends.trans (evfb.heap_extends.trans ext_17_18))
    have happ_body : TmOExact (Core.keyOf t) m18
        (.app (appSpine (.bvar (depthNow - 1 - (motiveBase + selfMemIdx)))
            (((pfRet.liftLooseBVars below nFields).getAppArgs.drop nOwn).map
              fun e => e.liftLooseBVars ri.length 0))
          (fieldBVars (ctorAppParams (.const (Core.keyOf t (ixAddr ca)) us) nrp depthNow aux sp)
            nFields (nFields + ri.length)))
        (.ptr (.enum kexprEnum) m17.length) := by
      obtain ⟨k1, r1⟩ := hwithIdx.mono ext_14_18
      obtain ⟨k2, r2⟩ := hctorApp.mono ext_17_18
      exact ⟨max k1 k2, .app (by rw [hm18]; simp)
        (tmExact_depth_le r1 _ (Nat.le_max_left _ _))
        (tmExact_depth_le r2 _ (Nat.le_max_right _ _))⟩
    have ext_0_18 := ext_0_4.trans (ext_4_14.trans ext_14_18)
    have ext_7_18 := evliftRet.heap_extends.trans (evsp.heap_extends.trans (evle.heap_extends.trans
      (ext_12_13.trans (evapp1.heap_extends.trans ext_14_18))))
    have ovih' : ObsFn W "KernelCheck::build_ih_doms"
        [xri, xrm, vnormL, xfop, .field (motiveBase : F), .field (nFields : F),
          .field (minorSaved : F), .field ((0 : Nat) : F), xelim] m18 vih m19 cs16 := by
      simpa using ovih
    have hnormL_len : (liftIndices pfNorm below).length = nFields := by
      simp [liftIndices, hnorm_len]
    obtain ⟨ihs, hihs, hrep_ihs, hihsIn⟩ := build_ih_doms_spec
      (S := Held R) (κ := Core.keyOf t) (rm := rm) (fop := fop) (norm := liftIndices pfNorm below)
      (by omega) (by omega) hnormL_len hfop56 (fun m hm => by rw [hfop_len]; exact hrm_lt m hm)
      ri 0 (by omega) (fun fi hfi => (hri_lt fi hfi).2)
      (bnd fun c hc' => by rw [hc]; simp [hc'])
      (fieldList_mono (ext_4_14.trans ext_14_18) hri)
      (fieldList_mono (ext_4_14.trans ext_14_18) hrm)
      (tmOExactList_mono ext_7_18 (by simpa [liftIndices] using hnormL))
      (addrIn_liftIndices hnormIn)
      (fieldList_mono ext_0_18 hfop) (helim.mono ext_0_18) ovih'
    have hw1 := wrap_foralls_spec ihs evw1 (happ_body.mono ovih.heap_extends) hrep_ihs
      (helim.mono (ext_0_18.trans ovih.heap_extends))
    have ext_6_20 := evli2.heap_extends.trans (ext_7_18.trans (ovih.heap_extends.trans evw1.heap_extends))
    have hw2 := wrap_foralls_spec (liftIndices pfDoms below) evw2 hw1
      (tmOExactList_mono ext_6_20 (by simpa [liftIndices] using hdomsL))
      (helim.mono (ext_0_18.trans (ovih.heap_extends.trans evw1.heap_extends)))
    refine ⟨_, (hev_peel.and hev_wfc).mono fun f ⟨hpf, hwfcf⟩ => ?_, hw2, ?_⟩
    · simp only [minorAt, hpf, hwfcf, hihs]
    · refine addrIn_wrapForalls (addrIn_liftIndices hpfdIn)
        (addrIn_wrapForalls hihsIn ⟨addrIn_appSpine trivial hretIdxIn,
          addrIn_fieldBVars (addrIn_ctorAppParams (fun x hx => by
            have := hinj hx; subst this; exact hSca) hspIn)⟩)

/-- Pure `Unit`-list length extraction for `KernelCheck::build_minor_doms` (requires no bound
on `prevMinors`). -/
theorem build_minor_doms_rawLen {numCtors : Nat} (hnc : numCtors < 9223372036854775808) :
    ∀ (rem c : Nat), c + rem = numCtors →
      ∀ {xrc xm xaux xsp xus xflat xfop xnrp xnmot xmb xself xblk xidx xprev xelim r : SourceValue F}
        {h h' : Heap F} {cs : List (Call F)},
        ObsFn W "KernelCheck::build_minor_doms"
          [xrc, xm, xaux, xsp, xus, xflat, xfop, xnrp, xnmot, xmb, xself, xblk, xidx,
            .field (numCtors : F), xprev, .field (c : F), xelim] h r h' cs →
        RepList kexprListEnum (fun _ (_ : Unit) _ => True) h' (List.replicate rem ()) r := by
  intro rem
  induction rem with
  | zero =>
    intro c hc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r h h' cs ev
    match Obs.«KernelCheck::build_minor_doms».obs ev with
    | .n0 (he28 := hr0) (hm27 := hm0) .. =>
      cases hr0; cases hm0; exact Lib.rep_store_nil h
    | .other (op17 := op) (hne33 := hne) .. =>
      have : c = numCtors := by omega
      subst this; simp only [evalBinOp, sub_self, Except.ok.injEq] at op
      exact (hne op.symm).elim
  | succ rem ih =>
    intro c hc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r h h' cs ev
    match Obs.«KernelCheck::build_minor_doms».obs ev with
    | .n0 (op17 := op) .. =>
      have := binop_sub_eq_zero_nat (by omega) (by omega) op; omega
    | .other (v355 := vc1) (he315 := hr0) (hm314 := hm0) (op483 := op1) (ev339 := evrec) .. =>
      cases hr0; cases hm0
      obtain rfl := binop_add_one_nat op1
      have hrec := ih (c + 1) (by omega) evrec
      exact Lib.rep_store_cons (fun _ _ _ _ _ t => t) trivial hrec

/-- Pure `Unit`-list length extraction for `KernelCheck::build_all_minors_walk`: returns a list
of length equal to `flatTotalCtors (ReconView.ofStore t E₀) es` without bounding `prevMinors`. -/
theorem build_all_minors_walk_rawLen {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R)) :
    ∀ (es : List FlatEntry)
      {xrc xflat xfull xfop xnrp xnmot xmb xprev xpos xelim r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      (∀ c ∈ cs, c ∈ rootCalls) →
      RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h es xflat →
      (∀ e ∈ es, Held R e.addr ∧ ∃ info, indDataAt t E₀ e.addr = some (some info)) →
      ObsFn W "KernelCheck::build_all_minors_walk"
        [xrc, xflat, xfull, xfop, xnrp, xnmot, xmb, xprev, xpos, xelim] h r h' cs →
      ∃ tot : Nat,
        flatTotalCtors (ReconView.ofStore t E₀) es = some tot ∧
        RepList kexprListEnum (fun _ (_ : Unit) _ => True) h' (List.replicate tot ()) r := by
  have hIA : IndAnswers rootCalls (Held R) (Core.keyOf t) (ReconView.ofStore t E₀) :=
    indAnswers_ofStore ht hwf hS hH hbd hRsub hcl hlv
  intro es
  induction es with
  | nil =>
    intro xrc xflat xfull xfop xnrp xnmot xmb xprev xpos xelim r h h' cs _ hes _ ev
    match Obs.«KernelCheck::build_all_minors_walk».obs ev with
    | .Nil (he24 := hr0) (hm23 := hm0) .. =>
      cases hr0; cases hm0
      exact ⟨0, rfl, Lib.rep_store_nil h⟩
    | .Cons_Induct (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hcons
  | cons e rest ih =>
    intro xrc xflat xfull xfop xnrp xnmot xmb xprev xpos xelim r h h' cs hsub hes hall ev
    match Obs.«KernelCheck::build_all_minors_walk».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    | .Cons_other (x_member_addr := xa) (v82 := vci) (m83 := m1) (p90 := pci) (cs96 := cs1)
        (ld12 := ld) (ev98 := evci) (ld92 := ldci) (hne473 := hne) (hc571 := hc) .. =>
      obtain ⟨e', _, h1, he', -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with h1e _; subst h1e
      obtain ⟨_, _, _, ae, htup, rae, hae, -, -⟩ := he'
      injection htup with hl; injection hl with hxa _; subst hxa
      obtain ⟨hSe, _, hinfo0⟩ := hall e (List.mem_cons_self ..)
      rw [← hae] at hSe hinfo0
      obtain ⟨-, hOther⟩ := hIA
        (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hSe rae evci ldci
      have hnone := hOther hne
      change indDataAt t E₀ (ixAddr ae) = some none at hnone
      rw [hinfo0] at hnone; cases hnone
    | .Cons_Induct (x_rest := xrest) (x_member_addr := xa) (x_is_aux := xaux)
        (x_spec_params := xsp) (x_occ_us := xus) (m83 := m1) (p90 := pci) (cs96 := cs1)
        (x_num_ctors := xnc) (x_mem_block_addr := xblk) (x_mem_ind_idx := xidx)
        (v168 := vms) (m169 := m2) (cs179 := cs2) (m318 := m3)
        (v339 := vrest) (m340 := m4) (cs350 := cs4) (ld12 := ld) (ev98 := evci) (ld92 := ldci)
        (ev181 := evmd) (ev330 := evlen) (ev352 := evrec) (ev455 := evcat) (hc472 := hc) .. =>
      obtain ⟨e', rest', h1, he', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with h1e h1r; subst h1e h1r
      obtain ⟨_, _, _, ae, htup, rae, hae, -, -⟩ := he'
      injection htup with hl; injection hl with hxa _; subst hxa
      obtain ⟨hSe, -, -⟩ := hall e (List.mem_cons_self ..)
      rw [← hae] at hSe
      obtain ⟨hInd, -⟩ := hIA
        (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hSe rae evci ldci
      obtain ⟨info, _, hia, -, -, -, hnc56, -, -, -, -, -, -, -, hncEq, -⟩ :=
        hInd _ _ _ _ _ _ _ _ rfl
      subst hncEq
      have evmd' : ObsFn W "KernelCheck::build_minor_doms"
          [xrc, xa, xaux, xsp, xus, xfull, xfop, xnrp, xnmot, xmb, xpos, xblk, xidx,
            .field (info.nctors : F), xprev, .field ((0 : Nat) : F), xelim] m1 vms m2 cs2 := by
        simpa using evmd
      have hms_raw := build_minor_doms_rawLen (by omega) info.nctors 0 (by omega) evmd'
      have ext_1_3 := evmd.heap_extends.trans evlen.heap_extends
      obtain ⟨tot', htot', hrest_raw⟩ := ih (fun c hc' => hsub c (by rw [hc]; simp [hc']))
        (flatList_mono (evci.heap_extends.trans ext_1_3) hrest)
        (fun x hx => hall x (List.mem_cons_of_mem _ hx)) evrec
      have hcat := kexpr_unit_concat_spec evcat
        (RepLinkedList.mono (fun _ _ _ _ _ t => t) (evlen.heap_extends.trans evrec.heap_extends) hms_raw)
        hrest_raw
      rw [← List.replicate_add] at hcat
      refine ⟨info.nctors + tot', ?_, hcat⟩
      simp only [flatTotalCtors]
      rw [show (ReconView.ofStore t E₀).ind e.addr = some (some info) from by
          change indDataAt t E₀ e.addr = some (some info); rwa [← hae], htot']

/-- **`KernelCheck::build_minor_doms`** refines `minorDoms (ReconView.ofStore t E₀)` at
`Eventually` on `TmOExact`, preserving `AddrIn (Held R)`. -/
theorem build_minor_doms_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    (hM : ModeledAnswers rootCalls (Held R) (ReconView.ofStore t E₀))
    {es : List FlatEntry} {fop : List Nat} {aux : Bool} {sp : List KExpr} {us : List KLevel}
    {nrp nMot motiveBase selfMemIdx idx numCtors : Nat} {ba : Bytes.Address} {elim : KLevel}
    {xrc xm xsp xus xflat xfop xblk xelim : SourceValue F}
    (hnrp : nrp < 72057594037927936) (hnMot : nMot = es.length)
    (hmBase : motiveBase = nrp) (hself : selfMemIdx < nMot)
    (hidx : idx < 72057594037927936) (hnc : numCtors < 72057594037927936)
    (hfop_len : fop.length = es.length) (hfop56 : ∀ n ∈ fop, n < 72057594037927936)
    (hSblk : Held R (ixAddr ba))
    (hctorsHeld : ∀ c, c < numCtors → Held R (IxVM.Consistency.ctorAddr (ixAddr ba) idx c))
    (hcnp_ok : ∀ c cty cnp, (ReconView.ofStore t E₀).ctor (ixAddr ba) idx c = some (cty, cnp) →
      ∀ i, i < cnp → ¬ (aux = true ∧ i < sp.length) → i < nrp) :
    ∀ (rem prev c : Nat), c + rem = numCtors → prev + rem < 2 ^ 39 →
      ∀ {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        (∀ cl ∈ cs, cl ∈ rootCalls) →
        RepList kexprListEnum (TmOExact (Core.keyOf t)) h sp xsp →
        (∀ e ∈ sp, AddrIn (Held R) (Core.keyOf t) e) →
        RepKLevelList h us xus →
        RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h es xflat →
        RepList fieldListEnum RepNatField h fop xfop →
        Bytes.RepAddressRef addrTy h ba xblk →
        RepKLevel h elim xelim →
        ObsFn W "KernelCheck::build_minor_doms"
          [xrc, xm, auxVal aux, xsp, xus, xflat, xfop, .field (nrp : F), .field (nMot : F),
            .field (motiveBase : F), .field (selfMemIdx : F), xblk, .field (idx : F),
            .field (numCtors : F), .field (prev : F), .field (c : F), xelim] h r h' cs →
        ∃ ms : List KExpr,
          ms.length = rem ∧
          Eventually (fun f => minorDoms (ReconView.ofStore t E₀) f es fop aux sp us nrp nMot
            motiveBase selfMemIdx (ixAddr ba) idx elim prev ((List.range numCtors).drop c) = some ms) ∧
          RepList kexprListEnum (TmOExact (Core.keyOf t)) h' ms r ∧
          (∀ m ∈ ms, AddrIn (Held R) (Core.keyOf t) m) := by
  intro rem
  induction rem with
  | zero =>
    intro prev c hc _ r h h' cs _ _ _ _ _ _ _ _ ev
    match Obs.«KernelCheck::build_minor_doms».obs ev with
    | .n0 (he28 := hr0) (hm27 := hm0) .. =>
      cases hr0; cases hm0
      have hdrop : (List.range numCtors).drop c = [] :=
        List.drop_eq_nil_of_le (by rw [List.length_range]; omega)
      rw [hdrop]
      exact ⟨[], rfl, Eventually.always fun _ => rfl, Lib.rep_store_nil h, fun _ hm => nomatch hm⟩
    | .other (op17 := op) (hne33 := hne) .. =>
      have : c = numCtors := by omega
      subst this; simp only [evalBinOp, sub_self, Except.ok.injEq] at op
      exact (hne op.symm).elim
  | succ rem ih =>
    intro prev c hc hcap r h h' cs hsub hsp hspIn hus hes hfop rba helim ev
    have sub : ∀ {cs' : List (Call F)}, (∀ cl ∈ cs', cl ∈ cs) → ∀ cl ∈ cs', cl ∈ rootCalls :=
      fun hs cl hcl' => hsub cl (hs cl hcl')
    match Obs.«KernelCheck::build_minor_doms».obs ev with
    | .n0 (op17 := op) .. =>
      have := binop_sub_eq_zero_nat (by omega) (by omega) op; omega
    | .other (m38 := m1) (p45 := pci) (cs51 := cs1) (x_ctor_ty := xcty) (x_np := xnp)
        (v139 := vca) (m140 := m2) (cs150 := cs2) (v177 := vmin) (m178 := m3) (cs188 := cs3)
        (v320 := vrest) (m329 := m4) (cs337 := cs4) (v354 := vprev1) (v355 := vc1)
        (ev53 := evct) (ld47 := ldct) (ev152 := evca) (ev190 := evmin)
        (he315 := hr0) (hm314 := hm0) (op468 := op1) (op483 := op2) (ev339 := evrec) (hc492 := hcs) .. =>
      cases hr0; cases hm0
      obtain ⟨cty, _, np, _, tyPtr, _, _, _, _, hshape, hctorAt, -, -, hnp56, -, hcty, hctyIn, -, -⟩ :=
        ctorLoad_ofStore ht hwf hS hbd hRsub hcl hlv (by omega) (by omega)
          (sub fun cl hcl' => by rw [hcs]; simp [hcl']) hSblk rba evct ldct
      injection hshape with _ _ hl
      injection hl with _ hl; injection hl with h1 hl; injection hl with _ hl
      injection hl with _ hl; injection hl with _ hl; injection hl with h2 _
      subst h1 h2
      obtain ⟨ca, rca, hca_eq⟩ := projection_addr_ctor_exact (by omega) (by omega)
        (RomBound.bounded_mono hbd (sub fun cl hcl' => by rw [hcs]; simp [hcl']))
        (Bytes.repAddressRef_heapMono₂ addrTy evct.heap_extends rba) evca
      have ext02 := evct.heap_extends.trans evca.heap_extends
      have hSca : Held R (ixAddr ca) := hca_eq.symm ▸ hctorsHeld c (by omega)
      obtain ⟨M, hevM, hM_tm, hMIn⟩ := build_minor_at_depth_spec ht hwf hS hH hbd hRsub hcl hlv hM
        (sub fun cl hcl' => by rw [hcs]; simp [hcl']) hnp56 hnrp
        (hcnp_ok c cty np hctorAt) hnMot (by omega) hmBase hself
        hfop_len hfop56 hSca rca (hcty.mono evca.heap_extends) hctyIn
        (tmOExactList_mono ext02 hsp) hspIn (hus.mono ext02) (flatList_mono ext02 hes)
        (fieldList_mono ext02 hfop) (helim.mono ext02) evmin
      obtain rfl := binop_add_one_nat op1
      obtain rfl := binop_add_one_nat op2
      have ext03 := ext02.trans evmin.heap_extends
      obtain ⟨ms, hms_len, hev_ms, hrep_ms, hmsIn⟩ := ih (prev + 1) (c + 1) (by omega) (by omega)
        (sub fun cl hcl' => by rw [hcs]; simp [hcl'])
        (tmOExactList_mono ext03 hsp) hspIn (hus.mono ext03) (flatList_mono ext03 hes)
        (fieldList_mono ext03 hfop) (Bytes.repAddressRef_heapMono₂ addrTy ext03 rba)
        (helim.mono ext03) evrec
      have hdrop : (List.range numCtors).drop c = c :: (List.range numCtors).drop (c + 1) := by
        have hlt : c < (List.range numCtors).length := by simp; omega
        rw [List.drop_eq_getElem_cons hlt]; simp
      refine ⟨M :: ms, by simp [hms_len], (hevM.and hev_ms).mono fun f ⟨hfM, hfms⟩ => ?_,
        Lib.rep_store_cons tmOExact_heapMono₂ (hM_tm.mono evrec.heap_extends) hrep_ms, ?_⟩
      · rw [hdrop]
        simp only [minorDoms]
        rw [show (ReconView.ofStore t E₀).ctor (ixAddr ba) idx c = some (cty, np) from hctorAt]
        dsimp only
        rw [show (ReconView.ofStore t E₀).ctorAddr (ixAddr ba) idx c = ixAddr ca from hca_eq.symm,
          show (ReconView.ofStore t E₀).key = Core.keyOf t from rfl, hfM, hfms]
        rfl
      · intro m hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hMIn
        · exact hmsIn m hm

private theorem ctors_held_of_indDataAt {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env}
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    {a : _root_.Address} {info : IndData} (hSa : Held R a)
    (hia : indDataAt t E₀ a = some (some info)) :
    Held R info.blk ∧ ∀ c, c < info.nctors → Held R (IxVM.Consistency.ctorAddr info.blk info.idx c) := by
  unfold indDataAt at hia
  cases hca : recordOf E₀ a with
  | none => simp [hca] at hia
  | some c =>
    rw [hca] at hia
    cases hci : c.info with
    | iPrj p =>
      simp only [hci] at hia
      have hpb : Held R p.block := by
        obtain ⟨cR, hcR⟩ := Option.isSome_iff_exists.mp hSa
        have hce : cR = c := Option.some.inj ((hRsub a cR hcR).symm.trans hca)
        subst hce
        have := (hcl.1 a cR hcR).1
        simpa [Ix.Cert.ownerOf, hci] using this
      obtain ⟨cbR, hcbR⟩ := Option.isSome_iff_exists.mp hpb
      have hcbE := hRsub p.block cbR hcbR
      rw [hcbE] at hia
      cases hmuts : cbR.info with
      | muts ms =>
        simp only [hmuts] at hia
        cases hms : ms[p.idx.toNat]? with
        | none => simp [hms] at hia
        | some mc =>
          cases mc with
          | indc ind =>
            simp only [hms] at hia
            cases hld : loadedAt t (fun x => E₀.blobs.get? x) cbR (blockSelf t p.block ms)
                ind.lvls.toNat (mutsRoot ms p.idx.toNat) ind.typ with
            | none => simp only [hld] at hia; cases hia
            | some ty =>
              simp only [hld, Option.some.injEq] at hia
              subst hia
              refine ⟨hpb, fun j hj => ?_⟩
              have hheld := (hcl.2 p.block cbR ms hcbR hmuts p.idx.toNat (.indc ind) hms).2
                ind rfl j hj
              exact Option.isSome_iff_exists.mpr ⟨_, hheld⟩
          | _ => simp [hms] at hia
      | _ => simp [hmuts] at hia
    | _ => simp [hci] at hia

/-- **`KernelCheck::build_all_minors_walk`** refines `allMinors (ReconView.ofStore t E₀)` at
`Eventually` on `TmOExact`, preserving `AddrIn (Held R)`. -/
theorem build_all_minors_walk_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    (hM : ModeledAnswers rootCalls (Held R) (ReconView.ofStore t E₀))
    {fullEs : List FlatEntry} {fop : List Nat} {nrp nMot motiveBase : Nat} {elim : KLevel}
    {xrc xfull xfop xelim : SourceValue F}
    (hnrp : nrp < 72057594037927936) (hnMot : nMot = fullEs.length)
    (hmBase : motiveBase = nrp)
    (hfop_len : fop.length = fullEs.length) (hfop56 : ∀ n ∈ fop, n < 72057594037927936) :
    ∀ (es : List FlatEntry) (prev pos tot : Nat)
      {xflat r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      pos + es.length = fullEs.length →
      prev + tot < 2 ^ 39 →
      flatTotalCtors (ReconView.ofStore t E₀) es = some tot →
      (∀ cl ∈ cs, cl ∈ rootCalls) →
      RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h es xflat →
      RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h fullEs xfull →
      RepList fieldListEnum RepNatField h fop xfop →
      RepKLevel h elim xelim →
      (∀ e ∈ es, Held R e.addr ∧ (∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p) ∧
        FlatEntryParamsOk (ReconView.ofStore t E₀) nrp e) →
      ObsFn W "KernelCheck::build_all_minors_walk"
        [xrc, xflat, xfull, xfop, .field (nrp : F), .field (nMot : F), .field (motiveBase : F),
          .field (prev : F), .field (pos : F), xelim] h r h' cs →
      ∃ ms : List KExpr,
        ms.length = tot ∧
        Eventually (fun f => allMinors (ReconView.ofStore t E₀) f fullEs fop nrp nMot motiveBase
          elim es prev pos = some ms) ∧
        RepList kexprListEnum (TmOExact (Core.keyOf t)) h' ms r ∧
        (∀ m ∈ ms, AddrIn (Held R) (Core.keyOf t) m) := by
  have hIA : IndAnswers rootCalls (Held R) (Core.keyOf t) (ReconView.ofStore t E₀) :=
    indAnswers_ofStore ht hwf hS hH hbd hRsub hcl hlv
  intro es
  induction es with
  | nil =>
    intro prev pos tot xflat r h h' cs _ _ htot _ hes _ _ _ _ ev
    simp only [flatTotalCtors, Option.some.injEq] at htot; subst htot
    match Obs.«KernelCheck::build_all_minors_walk».obs ev with
    | .Nil (he24 := hr0) (hm23 := hm0) .. =>
      cases hr0; cases hm0
      exact ⟨[], rfl, Eventually.always fun _ => rfl, Lib.rep_store_nil h, fun _ hm => nomatch hm⟩
    | .Cons_Induct (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hcons
  | cons e rest ih =>
    intro prev pos tot xflat r h h' cs hposlen hcap htot hsub hes hfull hfop helim hesS ev
    have sub : ∀ {cs' : List (Call F)}, (∀ cl ∈ cs', cl ∈ cs) → ∀ cl ∈ cs', cl ∈ rootCalls :=
      fun hs cl hcl' => hsub cl (hs cl hcl')
    simp only [flatTotalCtors] at htot
    cases hi : (ReconView.ofStore t E₀).ind e.addr with
    | none => simp [hi] at htot
    | some opt =>
      cases opt with
      | none => simp [hi] at htot
      | some info0 =>
        cases htot' : flatTotalCtors (ReconView.ofStore t E₀) rest with
        | none => simp [hi, htot'] at htot
        | some tot' =>
          simp only [hi, htot', Option.some.injEq] at htot; subst htot
          match Obs.«KernelCheck::build_all_minors_walk».obs ev with
          | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
          | .Cons_other (x_member_addr := xa) (v82 := vci) (m83 := m1) (p90 := pci) (cs96 := cs1)
              (ld12 := ld) (ev98 := evci) (ld92 := ldci) (hne473 := hne) (hc571 := hcs) .. =>
            obtain ⟨e', _, h1, he', -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
            injection h1 with h1e _; subst h1e
            obtain ⟨_, _, _, ae, htup, rae, hae, -, -⟩ := he'
            injection htup with hl; injection hl with hxa _; subst hxa
            have hSe : Held R (ixAddr ae) := hae ▸ (hesS e (List.mem_cons_self ..)).1
            obtain ⟨-, hOther⟩ := hIA
              (sub fun cl hcl' => by rw [hcs]; simp [hcl']) hSe rae evci ldci
            have hnone := hOther hne
            change indDataAt t E₀ (ixAddr ae) = some none at hnone
            change indDataAt t E₀ e.addr = some (some info0) at hi
            rw [← hae] at hi; rw [hi] at hnone; cases hnone
          | .Cons_Induct (x_rest := xrest) (x_member_addr := xa) (x_is_aux := xaux)
              (x_spec_params := xsp) (x_occ_us := xus) (m83 := m1) (p90 := pci) (cs96 := cs1)
              (x_num_ctors := xnc) (x_mem_block_addr := xblk) (x_mem_ind_idx := xidx)
              (v168 := vms) (m169 := m2) (cs179 := cs2) (v317 := vmlen) (m318 := m3)
              (v339 := vrest) (m340 := m4) (cs350 := cs4) (v360 := vprev') (v361 := vpos')
              (ld12 := ld) (ev98 := evci) (ld92 := ldci) (ev181 := evmd) (ev330 := evlen)
              (op425 := op_p) (op441 := op_pos) (ev352 := evrec) (ev455 := evcat) (hc472 := hcs) .. =>
            obtain ⟨e', rest', h1, he', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
            injection h1 with h1e h1r; subst h1e h1r
            obtain ⟨xa', xsp', xus', ae, htup, rae, hae, hsp, hus⟩ := he'
            simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
            obtain ⟨rfl, rfl, rfl, rfl⟩ := htup
            obtain ⟨hSe, hspIn, heP⟩ := hesS e (List.mem_cons_self ..)
            have hSe' : Held R (ixAddr ae) := hae ▸ hSe
            obtain ⟨hInd, -⟩ := hIA
              (sub fun cl hcl' => by rw [hcs]; simp [hcl']) hSe' rae evci ldci
            obtain ⟨info, ba, hia, -, -, -, hnc56, hidx56, -, -, -, -, -, -, hncEq, hba, rba, hidxEq⟩ :=
              hInd _ _ _ _ _ _ _ _ rfl
            change indDataAt t E₀ e.addr = some (some info0) at hi
            rw [← hae] at hi
            have hinfo_eq := Option.some.inj (Option.some.inj (hia.symm.trans hi))
            subst info
            subst hncEq hidxEq
            obtain ⟨hSblk, hctorsH⟩ := ctors_held_of_indDataAt hRsub hcl hSe' hia
            rw [← hba] at hSblk hctorsH
            have hia_e : (ReconView.ofStore t E₀).ind e.addr = some (some info0) := by
              change indDataAt t E₀ e.addr = some (some info0); rwa [← hae]
            obtain ⟨hP_orig, hP_aux, hP_ctor⟩ := heP info0 hia_e
            have evmd' : ObsFn W "KernelCheck::build_minor_doms"
                [xrc, xa, auxVal e.aux, xsp, xus, xfull, xfop, .field (nrp : F),
                  .field (nMot : F), .field (motiveBase : F), .field (pos : F), xblk,
                  .field (info0.idx : F), .field (info0.nctors : F), .field (prev : F),
                  .field ((0 : Nat) : F), xelim] m1 vms m2 cs2 := by simpa using evmd
            obtain ⟨ms1, hms1_len, hev1, hrep1, hms1In⟩ := build_minor_doms_spec
              ht hwf hS hH hbd hRsub hcl hlv hM hnrp hnMot hmBase
              (by rw [hnMot]; simp only [List.length_cons] at hposlen; omega) hidx56 hnc56 hfop_len hfop56
              hSblk hctorsH (fun c cty cnp hct i hi_lt hni => by
                rw [← hba] at hP_ctor
                have hcnp_eq := hP_ctor c cty cnp hct
                cases hax : e.aux
                · have := hP_orig hax; omega
                · have := hP_aux hax; exfalso; exact hni ⟨hax, by omega⟩)
              info0.nctors prev 0 (by omega) (by omega)
              (sub fun cl hcl' => by rw [hcs]; simp [hcl'])
              (tmOExactList_mono evci.heap_extends hsp) hspIn (hus.mono evci.heap_extends)
              (flatList_mono evci.heap_extends hfull) (fieldList_mono evci.heap_extends hfop)
              rba (helim.mono evci.heap_extends) evmd'
            simp only [List.drop_zero] at hev1
            obtain ⟨rfl, rfl⟩ := kexpr_length_spec evlen hrep1
            obtain rfl := binop_add_nat op_p
            obtain rfl := binop_add_one_nat op_pos
            have ext02 := evci.heap_extends.trans evmd.heap_extends
            obtain ⟨ms2, hms2_len, hev2, hrep2, hms2In⟩ := ih (prev + ms1.length) (pos + 1) tot'
              (by simp only [List.length_cons] at hposlen; omega) (by omega) htot'
              (sub fun cl hcl' => by rw [hcs]; simp [hcl'])
              (flatList_mono ext02 hrest) (flatList_mono ext02 hfull)
              (fieldList_mono ext02 hfop) (helim.mono ext02)
              (fun x hx => hesS x (List.mem_cons_of_mem _ hx)) evrec
            have hcat := kexpr_concat_spec tmOExact_heapMono₂ evcat
              (tmOExactList_mono evrec.heap_extends hrep1) hrep2
            refine ⟨ms1 ++ ms2, by simp [hms1_len, hms2_len],
              (hev1.and hev2).mono fun f ⟨hf1, hf2⟩ => ?_, hcat, ?_⟩
            · simp only [allMinors]
              rw [hia_e]; dsimp only
              rw [← hba, hf1]; dsimp only
              rw [hf2]; rfl
            · intro m hm
              rcases List.mem_append.mp hm with h1 | h2
              · exact hms1In m h1
              · exact hms2In m h2

/-- **`KernelCheck::build_all_minors`** refines `allMinors` starting from `prev = 0, pos = 0`
once the total minor count fits below `2 ^ 39`. -/
theorem build_all_minors_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    (hM : ModeledAnswers rootCalls (Held R) (ReconView.ofStore t E₀))
    {es : List FlatEntry} {fop : List Nat} {nrp nMot motiveBase tot : Nat} {elim : KLevel}
    {xrc xflat xfop xelim r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hnrp : nrp < 72057594037927936) (hnMot : nMot = es.length) (hmBase : motiveBase = nrp)
    (hfop_len : fop.length = es.length) (hfop56 : ∀ n ∈ fop, n < 72057594037927936)
    (htot_lt : tot < 2 ^ 39) (htot : flatTotalCtors (ReconView.ofStore t E₀) es = some tot)
    (hsub : ∀ cl ∈ cs, cl ∈ rootCalls)
    (hes : RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h es xflat)
    (hfop : RepList fieldListEnum RepNatField h fop xfop)
    (helim : RepKLevel h elim xelim)
    (hesS : ∀ e ∈ es, Held R e.addr ∧ (∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p) ∧
      FlatEntryParamsOk (ReconView.ofStore t E₀) nrp e)
    (ev : ObsFn W "KernelCheck::build_all_minors"
      [xrc, xflat, xfop, .field (nrp : F), .field (nMot : F), .field (motiveBase : F), xelim]
      h r h' cs) :
    ∃ ms : List KExpr,
      ms.length = tot ∧
      Eventually (fun f => allMinors (ReconView.ofStore t E₀) f es fop nrp nMot motiveBase
        elim es 0 0 = some ms) ∧
      RepList kexprListEnum (TmOExact (Core.keyOf t)) h' ms r ∧
      (∀ m ∈ ms, AddrIn (Held R) (Core.keyOf t) m) := by
  match Obs.«KernelCheck::build_all_minors».obs ev with
  | .run (cs4 := cs1) (ev6 := evw) (hc85 := hc) .. =>
    have evw' : ObsFn W "KernelCheck::build_all_minors_walk"
        [xrc, xflat, xflat, xfop, .field (nrp : F), .field (nMot : F), .field (motiveBase : F),
          .field ((0 : Nat) : F), .field ((0 : Nat) : F), xelim] h r h' cs1 := by simpa using evw
    exact build_all_minors_walk_spec ht hwf hS hH hbd hRsub hcl hlv hM hnrp hnMot hmBase
      hfop_len hfop56 es 0 0 tot (by omega) (by omega) htot
      (fun cl hcl' => hsub cl (by rw [hc]; simp [hcl'])) hes hes hfop helim hesS evw'

/-- **`KernelCheck::build_motive_type_flat`** refines `motiveType (ReconView.ofStore t E₀)` at
`Eventually` on `TmOExact`, preserving `AddrIn (Held R)`. -/
theorem build_motive_type_flat_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    (hM : ModeledAnswers rootCalls (Held R) (ReconView.ofStore t E₀))
    {ma : Bytes.Address} {indTy : KExpr} {nOwn nIdx nrp : Nat} {us : List KLevel}
    {elim : KLevel} {aux : Bool} {sp : List KExpr}
    {xrc xma xty xus xelim xsp xptypes r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hnOwn : nOwn < 72057594037927936) (hnIdx : nIdx < 72057594037927936)
    (hnrp : nrp < 72057594037927936)
    (hnp_ok : ∀ i, i < nOwn → ¬ (aux = true ∧ i < sp.length) → i < nrp)
    (hsub : ∀ cl ∈ cs, cl ∈ rootCalls)
    (hSma : Held R (ixAddr ma))
    (rma : Bytes.RepAddressRef addrTy h ma xma)
    (hty : TmOExact (Core.keyOf t) h indTy xty) (htyIn : AddrIn (Held R) (Core.keyOf t) indTy)
    (hus : RepKLevelList h us xus) (helim : RepKLevel h elim xelim)
    (hsp : RepList kexprListEnum (TmOExact (Core.keyOf t)) h sp xsp)
    (hspIn : ∀ e ∈ sp, AddrIn (Held R) (Core.keyOf t) e)
    (ev : ObsFn W "KernelCheck::build_motive_type_flat"
      [xrc, xma, xty, .field (nOwn : F), .field (nIdx : F), xus, xelim, .field (nrp : F),
        auxVal aux, xsp, xptypes] h r h' cs) :
    ∃ M : KExpr,
      Eventually (fun f => motiveType (ReconView.ofStore t E₀) f (ixAddr ma) indTy nOwn nIdx us
        elim nrp aux sp = some M) ∧
      TmOExact (Core.keyOf t) h' M r ∧
      AddrIn (Held R) (Core.keyOf t) M := by
  have sub : ∀ {cs' : List (Call F)}, (∀ cl ∈ cs', cl ∈ cs) → ∀ cl ∈ cs', cl ∈ rootCalls :=
    fun hs cl hcl' => hsub cl (hs cl hcl')
  have bnd : ∀ {cs' : List (Call F)}, (∀ cl ∈ cs', cl ∈ cs) → Bounded cs' :=
    fun hs => RomBound.bounded_mono hbd (sub hs)
  have hA : AddrOf (Core.keyOf t) (ReconView.ofStore t E₀) := addrOf_ofStore (E₀ := E₀) hwf
  have hD : DefnAnswers rootCalls (Held R) (Core.keyOf t) (ReconView.ofStore t E₀) :=
    defnAnswers_ofStore ht hwf hS hH hbd hRsub hcl hlv
  have hI : IndAnswers rootCalls (Held R) (Core.keyOf t) (ReconView.ofStore t E₀) :=
    indAnswers_ofStore ht hwf hS hH hbd hRsub hcl hlv
  have hC : CtorOfAnswers rootCalls (Held R) (ReconView.ofStore t E₀) :=
    ctorOfAnswers_ofStore hS hH hbd hRsub hcl
  match Obs.«KernelCheck::build_motive_type_flat».obs ev with
  | .run (v1 := vtyI) (m2 := m1) (cs12 := cs1) (v31 := vafter) (m32 := m2) (cs42 := cs2)
      (v92 := vidxD) (m93 := m3) (cs103 := cs3) (m139 := m4) (v169 := vargs) (m170 := m5)
      (cs180 := cs4) (v223 := vmaj) (m224 := m6) (cs234 := cs5) (m261 := m7) (m284 := m9)
      (m300 := m8) (m313 := m10) (cs354 := cs6)
      (ev14 := evinst) (ev44 := evpeel) (ev105 := evidx) (hm149 := hm4) (ev182 := evma)
      (ev236 := evmi) (hm271 := hm7) (hm294 := hm9) (hm308 := hm8) (hm323 := hm10)
      (ev356 := evwrap) (hc381 := hc) .. =>
    have htyI := expr_inst_levels_tmOExact (bnd fun c hc' => by rw [hc]; simp [hc']) hty hus evinst
    have htyIIn : AddrIn (Held R) (Core.keyOf t) (exprInstLevels us indTy) :=
      addrIn_exprInstLevels htyIn
    have evpeel' : ObsFn W "KernelCheck::peel_motive_params_subst"
        [vtyI, .field (nOwn : F), .field (nrp : F), auxVal aux, xsp, .field ((0 : Nat) : F)]
        m1 vafter m2 cs2 := by simpa using evpeel
    have hsp_lt : sp.length < 2 ^ 39 :=
      repList_length_lt_obs hbd hsub evpeel' (by rw [hc]; simp) (by simp)
        (tmOExactList_mono evinst.heap_extends hsp)
    obtain ⟨after, hpeel_eq, hafter⟩ := peel_motive_params_subst_spec (by omega) (by omega)
      nOwn 0 (by omega) (fun i _ hi hni => hnp_ok i (by omega) hni)
      evpeel' (bnd fun c hc' => by rw [hc]; simp [hc']) htyI
      (tmOExactList_mono evinst.heap_extends hsp)
    have hafterIn : AddrIn (Held R) (Core.keyOf t) after :=
      addrIn_peelMotiveParams hspIn nOwn 0 _ _ hpeel_eq htyIIn
    obtain ⟨ext23, idxDoms, hidxD, hidxIn, hev_idx⟩ := collect_index_doms_spec hA hD hI hC hM nIdx
      (by omega) evidx (bnd fun c hc' => by rw [hc]; simp [hc'])
      (sub fun c hc' => by rw [hc]; simp [hc']) hafter hafterIn
    have ext03 := evinst.heap_extends.trans (evpeel.heap_extends.trans ext23)
    have ext34 : Heap.Extends m3 m4 := by rw [hm4]; exact Heap.Extends.snoc _ _
    have ext04 := ext03.trans ext34
    have hhead : TmOExact (Core.keyOf t) m4 (.const (Core.keyOf t (ixAddr ma)) us)
        (.ptr (.enum kexprEnum) m3.length) :=
      ⟨0, .const (by rw [hm4]; simp)
        (Bytes.repAddressRef_heapMono₂ addrTy ext04 rma) (hus.mono ext04)⟩
    have hwithArgs := build_major_args_for_member_spec (by omega)
      (bnd fun c hc' => by rw [hc]; simp [hc']) hhead (tmOExactList_mono ext04 hsp) evma
    have hmaj := build_major_indices_spec (by omega) evmi hwithArgs
    have ext67 : Heap.Extends m6 m7 := by rw [hm7]; exact Heap.Extends.snoc _ _
    have ext78 : Heap.Extends m7 m8 := by rw [hm8]; exact Heap.Extends.snoc _ _
    have ext89 : Heap.Extends m8 m9 := by rw [hm9]; exact Heap.Extends.snoc _ _
    have ext9_10 : Heap.Extends m9 m10 := by rw [hm10]; exact Heap.Extends.snoc _ _
    have ext07 := ext04.trans (evma.heap_extends.trans (evmi.heap_extends.trans ext67))
    have ext6_10 := ext67.trans (ext78.trans (ext89.trans ext9_10))
    have hsrt : TmOExact (Core.keyOf t) m10 (.sort elim) (.ptr (.enum kexprEnum) m6.length) :=
      ⟨0, .sort ((ext78.trans (ext89.trans ext9_10)).getElem?_eq (by rw [hm7]; simp))
        (helim.mono (ext07.trans (ext78.trans (ext89.trans ext9_10))))⟩
    have hzero : RepKLevel m8 .zero (.ptr (.enum klevelEnum) m7.length) :=
      RepKLevel.zero (by rw [hm8]; simp)
    have hnever : RepKLevel m9 (.succ .zero) (.ptr (.enum klevelEnum) m8.length) :=
      RepKLevel.succ (by rw [hm9]; simp) (hzero.mono ext89)
    have hbody : TmOExact (Core.keyOf t) m10
        (.forallE (appBVarsDown (if aux then specParamsLifted (.const (Core.keyOf t (ixAddr ma)) us) sp nIdx
          else majorParams (.const (Core.keyOf t (ixAddr ma)) us) nrp nIdx) nIdx) (.sort elim)
          (bmeta (.succ .zero)))
        (.ptr (.enum kexprEnum) m9.length) := by
      obtain ⟨k1, r1⟩ := hmaj.mono ext6_10
      obtain ⟨k2, r2⟩ := hsrt
      exact ⟨max k1 k2, .forallE (by rw [hm10]; simp)
        (tmExact_depth_le r1 _ (Nat.le_max_left _ _))
        (tmExact_depth_le r2 _ (Nat.le_succ_of_le (Nat.le_max_right _ _))) (hnever.mono ext9_10)⟩
    have ext3_10 := ext34.trans (evma.heap_extends.trans (evmi.heap_extends.trans ext6_10))
    have hres := wrap_foralls_spec idxDoms evwrap hbody (tmOExactList_mono ext3_10 hidxD)
      (hnever.mono ext9_10)
    refine ⟨_, hev_idx.mono fun f hf => ?_, hres, ?_⟩
    · simp only [motiveType, hpeel_eq]
      cases hcd : collectDoms (ReconView.ofStore t E₀) f nIdx after with
      | none => simp [hcd] at hf
      | some p =>
        simp only [hcd, Option.map_some, Option.some.injEq] at hf
        subst hf; rfl
    · refine addrIn_wrapForalls hidxIn ⟨addrIn_appBVarsDown ?_, trivial⟩
      have hheadIn : AddrIn (Held R) (Core.keyOf t) (.const (Core.keyOf t (ixAddr ma)) us) :=
        fun x hx => by have := Core.keyOf_inj hwf hx; subst this; exact hSma
      cases aux
      · exact addrIn_majorParams hheadIn
      · exact addrIn_specParamsLifted hheadIn hspIn

/-- **`KernelCheck::build_all_motives_walk`** refines `allMotives (ReconView.ofStore t E₀)` at
`Eventually` on `TmOExact`, preserving `AddrIn (Held R)`. -/
theorem build_all_motives_walk_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    (hM : ModeledAnswers rootCalls (Held R) (ReconView.ofStore t E₀))
    {elim : KLevel} {nrp : Nat} {xrc xelim xptypes : SourceValue F}
    (hnrp : nrp < 72057594037927936) :
    ∀ (es : List FlatEntry) (j : Nat) {xflat r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      j + es.length < 4611686018427387904 →
      (∀ cl ∈ cs, cl ∈ rootCalls) →
      RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h es xflat →
      RepKLevel h elim xelim →
      (∀ e ∈ es, Held R e.addr ∧ (∃ info, indDataAt t E₀ e.addr = some (some info)) ∧
        (∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p) ∧
        FlatEntryParamsOk (ReconView.ofStore t E₀) nrp e) →
      ObsFn W "KernelCheck::build_all_motives_walk"
        [xrc, xflat, xelim, .field (nrp : F), .field (j : F), xptypes] h r h' cs →
      ∃ ms : List KExpr,
        Eventually (fun f => allMotives (ReconView.ofStore t E₀) f elim nrp es j = some ms) ∧
        RepList kexprListEnum (TmOExact (Core.keyOf t)) h' ms r ∧
        (∀ m ∈ ms, AddrIn (Held R) (Core.keyOf t) m) := by
  have hIA : IndAnswers rootCalls (Held R) (Core.keyOf t) (ReconView.ofStore t E₀) :=
    indAnswers_ofStore ht hwf hS hH hbd hRsub hcl hlv
  intro es
  induction es with
  | nil =>
    intro j xflat r h h' cs _ _ hes _ _ ev
    match Obs.«KernelCheck::build_all_motives_walk».obs ev with
    | .Nil (he24 := hr0) (hm23 := hm0) .. =>
      cases hr0; cases hm0
      exact ⟨[], Eventually.always fun _ => rfl, Lib.rep_store_nil h, fun _ hm => nomatch hm⟩
    | .Cons_Induct (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hcons
  | cons e rest ih =>
    intro j xflat r h h' cs hjlen hsub hes helim hall ev
    have sub : ∀ {cs' : List (Call F)}, (∀ cl ∈ cs', cl ∈ cs) → ∀ cl ∈ cs', cl ∈ rootCalls :=
      fun hs cl hcl' => hsub cl (hs cl hcl')
    have bnd : ∀ {cs' : List (Call F)}, (∀ cl ∈ cs', cl ∈ cs) → Bounded cs' :=
      fun hs => RomBound.bounded_mono hbd (sub hs)
    match Obs.«KernelCheck::build_all_motives_walk».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    | .Cons_other (x_member_addr := xa) (v82 := vci) (m83 := m1) (p90 := pci) (cs96 := cs1)
        (ld12 := ld) (ev98 := evci) (ld92 := ldci) (hne393 := hne) (hc451 := hcs) .. =>
      obtain ⟨e', _, h1, he', -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with h1e _; subst h1e
      obtain ⟨_, _, _, ae, htup, rae, hae, -, -⟩ := he'
      injection htup with hl; injection hl with hxa _; subst hxa
      obtain ⟨hSe, ⟨_, hinfo0⟩, -⟩ := hall e (List.mem_cons_self ..)
      rw [← hae] at hSe hinfo0
      obtain ⟨-, hOther⟩ := hIA
        (sub fun cl hcl' => by rw [hcs]; simp [hcl']) hSe rae evci ldci
      have hnone := hOther hne
      change indDataAt t E₀ (ixAddr ae) = some none at hnone
      rw [hinfo0] at hnone; cases hnone
    | .Cons_Induct (x_rest := xrest) (x_member_addr := xa) (x_is_aux := xaux)
        (x_spec_params := xsp) (x_occ_us := xus) (m83 := m1) (p90 := pci) (cs96 := cs1)
        (x_m_ind_ty := xty) (x_m_own_params := xnp) (x_m_n_indices := xni)
        (v168 := vmt) (m169 := m2) (cs179 := cs2) (v270 := vmtL) (m271 := m3) (cs281 := cs3)
        (v316 := vrest) (m325 := m4) (cs333 := cs4) (v340 := vj1)
        (ld12 := ld) (ev98 := evci) (ld92 := ldci) (ev181 := evmt) (ev283 := evlift)
        (he311 := hr0) (hm310 := hm0) (op383 := op1) (ev335 := evrec) (hc392 := hcs) .. =>
      cases hr0; cases hm0
      obtain ⟨e', rest', h1, he', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with h1e h1r; subst h1e h1r
      obtain ⟨xa', xsp', xus', ae, htup, rae, hae, hsp, hus⟩ := he'
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
      obtain ⟨rfl, rfl, rfl, rfl⟩ := htup
      obtain ⟨hSe, -, hspIn, heP⟩ := hall e (List.mem_cons_self ..)
      have hSe' : Held R (ixAddr ae) := hae ▸ hSe
      obtain ⟨hInd, -⟩ := hIA
        (sub fun cl hcl' => by rw [hcs]; simp [hcl']) hSe' rae evci ldci
      obtain ⟨info, _, hia, -, hnp56, hni56, -, -, -, hty_tm, htyIn, -, hnpEq, hniEq, -⟩ :=
        hInd _ _ _ _ _ _ _ _ rfl
      subst hnpEq hniEq
      have hia_e : (ReconView.ofStore t E₀).ind e.addr = some (some info) := by
        change indDataAt t E₀ e.addr = some (some info); rwa [← hae]
      obtain ⟨hP_orig, hP_aux, -⟩ := heP info hia_e
      obtain ⟨mt, hev_mt, hmt, hmtIn⟩ := build_motive_type_flat_spec ht hwf hS hH hbd hRsub hcl hlv hM
        hnp56 hni56 hnrp (fun i hi_lt hni => by
          cases hax : e.aux
          · have := hP_orig hax; omega
          · have := hP_aux hax; exfalso; exact hni ⟨hax, by omega⟩)
        (sub fun cl hcl' => by rw [hcs]; simp [hcl']) hSe'
        (Bytes.repAddressRef_heapMono₂ addrTy evci.heap_extends rae) hty_tm htyIn
        (hus.mono evci.heap_extends) (helim.mono evci.heap_extends)
        (tmOExactList_mono evci.heap_extends hsp) hspIn evmt
      have evlift' : ObsFn W "KernelSubst::expr_lift"
          [vmt, .field (j : F), .field ((0 : Nat) : F)] m2 vmtL m3 cs3 := by simpa using evlift
      have hmtL := expr_lift_tmOExact (by simp only [List.length_cons] at hjlen; omega) (by decide)
        (bnd fun cl hcl' => by rw [hcs]; simp [hcl']) hmt evlift'
      obtain rfl := binop_add_one_nat op1
      have ext03 := evci.heap_extends.trans (evmt.heap_extends.trans evlift.heap_extends)
      obtain ⟨ms, hev_ms, hrep_ms, hmsIn⟩ := ih (j + 1)
        (by simp only [List.length_cons] at hjlen; omega)
        (sub fun cl hcl' => by rw [hcs]; simp [hcl'])
        (flatList_mono ext03 hrest) (helim.mono ext03)
        (fun x hx => hall x (List.mem_cons_of_mem _ hx)) evrec
      refine ⟨mt.liftLooseBVars j 0 :: ms, (hev_mt.and hev_ms).mono fun f ⟨hf1, hf2⟩ => ?_,
        Lib.rep_store_cons tmOExact_heapMono₂ (hmtL.mono evrec.heap_extends) hrep_ms, ?_⟩
      · simp only [allMotives]
        rw [show (ReconView.ofStore t E₀).ind e.addr = some (some info) from by
            change indDataAt t E₀ e.addr = some (some info); rwa [← hae]]
        dsimp only
        rw [show e.addr = ixAddr ae from hae.symm, hf1, hf2]
        rfl
      · intro m hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact addrIn_liftLooseBVars j hmtIn
        · exact hmsIn m hm

/-- **`KernelCheck::build_all_motives`** refines `allMotives (ReconView.ofStore t E₀)` from `j = 0`. -/
theorem build_all_motives_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    (hM : ModeledAnswers rootCalls (Held R) (ReconView.ofStore t E₀))
    {es : List FlatEntry} {elim : KLevel} {nrp : Nat}
    {xrc xflat xelim r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hnrp : nrp < 72057594037927936) (hes_lt : es.length < 4611686018427387904)
    (hsub : ∀ cl ∈ cs, cl ∈ rootCalls)
    (hes : RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h es xflat)
    (helim : RepKLevel h elim xelim)
    (hall : ∀ e ∈ es, Held R e.addr ∧ (∃ info, indDataAt t E₀ e.addr = some (some info)) ∧
      (∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p) ∧
      FlatEntryParamsOk (ReconView.ofStore t E₀) nrp e)
    (ev : ObsFn W "KernelCheck::build_all_motives"
      [xrc, xflat, xelim, .field (nrp : F)] h r h' cs) :
    ∃ ms : List KExpr,
      Eventually (fun f => allMotives (ReconView.ofStore t E₀) f elim nrp es 0 = some ms) ∧
      RepList kexprListEnum (TmOExact (Core.keyOf t)) h' ms r ∧
      (∀ m ∈ ms, AddrIn (Held R) (Core.keyOf t) m) := by
  match Obs.«KernelCheck::build_all_motives».obs ev with
  | .run (cs4 := cs2) (v12 := vpt) (m48 := m1) (ev58 := evrpc) (ev6 := evw) (hc83 := hc) .. =>
    have evw' : ObsFn W "KernelCheck::build_all_motives_walk"
        [xrc, xflat, xelim, .field (nrp : F), .field ((0 : Nat) : F), vpt] m1 r h' cs2 := by
      simpa using evw
    exact build_all_motives_walk_spec ht hwf hS hH hbd hRsub hcl hlv hM hnrp es 0 (by omega)
      (fun cl hcl' => hsub cl (by rw [hc]; simp [hcl']))
      (flatList_mono evrpc.heap_extends hes) (helim.mono evrpc.heap_extends) hall evw'

/-- **`KernelCheck::build_rec_type_from`** refines `recTypeAt (ReconView.ofStore t E₀)` at
`Eventually` on `TmOExact`, also exporting `flatTotalCtors < 2 ^ 39`. -/
theorem build_rec_type_from_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    (hM : ModeledAnswers rootCalls (Held R) (ReconView.ofStore t E₀))
    {es : List FlatEntry} {e0 ek : FlatEntry} {prim self : IndData} {fop : List Nat}
    {nP nI off k : Nat} {xrc xpty xity xindnl xelim xflat xfop r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hoff : off ≤ 1) (hnP : nP < 72057594037927936) (hnI : nI < 72057594037927936)
    (hprim_nl : prim.nl < 4294967296) (hni_eq : self.ni = nI)
    (he0 : es[0]? = some e0) (hek : es[k]? = some ek)
    (hprim_ind : indDataAt t E₀ e0.addr = some (some prim))
    (hself_ind : indDataAt t E₀ ek.addr = some (some self))
    (hfop_eq : flatOwnParams (ReconView.ofStore t E₀) es = some fop)
    (hfop_len : fop.length = es.length) (hfop56 : ∀ n ∈ fop, n < 72057594037927936)
    (hsub : ∀ cl ∈ cs, cl ∈ rootCalls)
    (hprimTy : TmOExact (Core.keyOf t) h prim.ty xpty)
    (hprimTyIn : AddrIn (Held R) (Core.keyOf t) prim.ty)
    (helim : RepKLevel h (elimLevel off) xelim)
    (hes : RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h es xflat)
    (hfop : RepList fieldListEnum RepNatField h fop xfop)
    (hall : ∀ e ∈ es, Held R e.addr ∧ (∃ info, indDataAt t E₀ e.addr = some (some info)) ∧
      (∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p) ∧
      FlatEntryParamsOk (ReconView.ofStore t E₀) nP e)
    (ev : ObsFn W "KernelCheck::build_rec_type_from"
      [xrc, xpty, .field (prim.nl : F), xity, xindnl, .field (nP : F), .field (nI : F),
        xelim, .field (off : F), xflat, xfop, .field (k : F)] h r h' cs) :
    ∃ (Rty : KExpr) (tot : Nat),
      flatTotalCtors (ReconView.ofStore t E₀) es = some tot ∧ tot < 2 ^ 39 ∧
      Eventually (fun f => recTypeAt (ReconView.ofStore t E₀) f es off nP k = some Rty) ∧
      TmOExact (Core.keyOf t) h' Rty r := by
  have sub : ∀ {cs' : List (Call F)}, (∀ cl ∈ cs', cl ∈ cs) → ∀ cl ∈ cs', cl ∈ rootCalls :=
    fun hs cl hcl' => hsub cl (hs cl hcl')
  have bnd : ∀ {cs' : List (Call F)}, (∀ cl ∈ cs', cl ∈ cs) → Bounded cs' :=
    fun hs => RomBound.bounded_mono hbd (sub hs)
  have hA : AddrOf (Core.keyOf t) (ReconView.ofStore t E₀) := addrOf_ofStore (E₀ := E₀) hwf
  have hD : DefnAnswers rootCalls (Held R) (Core.keyOf t) (ReconView.ofStore t E₀) :=
    defnAnswers_ofStore ht hwf hS hH hbd hRsub hcl hlv
  have hI : IndAnswers rootCalls (Held R) (Core.keyOf t) (ReconView.ofStore t E₀) :=
    indAnswers_ofStore ht hwf hS hH hbd hRsub hcl hlv
  have hC : CtorOfAnswers rootCalls (Held R) (ReconView.ofStore t E₀) :=
    ctorOfAnswers_ofStore hS hH hbd hRsub hcl
  have hk_lt : k < es.length := (List.getElem?_eq_some_iff.mp hek).1
  match Obs.«KernelCheck::build_rec_type_from».obs ev with
  | .run (v1 := vnMot) (m2 := m1) (cs12 := cs1) (v32 := vpUs) (m33 := m2) (cs43 := cs2)
      (m70 := m4) (cs81 := cs4) (v85 := vptyI) (m96 := m3) (cs104 := cs3) (m131 := m3a)
      (x_param_doms := xpdoms) (v159 := vmotD) (m160 := m5) (cs170 := cs5)
      (v205 := vminD) (m206 := m6) (cs216 := cs6) (v275 := vnMin) (m276 := m7) (cs286 := cs7)
      (m298 := m8) (cs308 := cs8) (x_self_addr := xsa) (x_self_is_aux := xsaux)
      (x_self_spec_params := xssp) (x_self_occ_us := xsus)
      (m351 := m9) (p358 := pci) (cs364 := cs9) (x_self_ind_ty := xsty) (x_self_own_params := xsnp)
      (v424 := vstyI) (m425 := m10) (cs435 := cs10) (v454 := vsafter) (m455 := m11) (cs465 := cs11)
      (v515 := vidxRaw) (m516 := m13) (cs526 := cs13) (v532 := vrev) (m555 := m12) (cs563 := cs12)
      (v574 := vidxL) (m575 := m14) (cs585 := cs14) (v589 := vnmotmin)
      (m621 := m15) (v651 := vpre) (x659 := x659) (x667 := x667)
      (v687 := vwithA) (m688 := m16) (cs698 := cs15) (v703 := vpre1) (v704 := vspecL) (x742 := x742)
      (v775 := vmaj) (m776 := m17) (cs786 := cs16) (v812 := vpreP1) (v829 := vmotB)
      (x837 := x837) (y838 := y838) (m865 := m18) (v887 := vconclI) (m888 := m19) (cs898 := cs17)
      (m925 := m21) (m949 := m20) (m969 := m22) (v1007 := vw1) (m1008 := m23) (cs1018 := cs18)
      (v1045 := vw2) (m1046 := m24) (cs1056 := cs19) (v1083 := vw3) (m1084 := m25) (cs1094 := cs20)
      (cs1124 := cs21)
      (ev14 := evlenF) (ev45 := evplvls) (ev106 := evinst1) (hm139 := hm3a) (ev83 := evcolP)
      (ev172 := evmots) (ev218 := evmins) (ev288 := evlenM) (ev310 := evfma)
      (ev366 := evci) (ld360 := ldci) (ev437 := evinst2) (ev467 := evpeel)
      (ev565 := evrev) (ev528 := evcolI) (op611 := op_mm) (ev587 := evli)
      (hm631 := hm15) (op682 := op_p1) (op674 := op_p2) (op666 := op_p3)
      (op734 := op_pm1) (op757 := op_sl1) (op749 := op_sl2) (ev700 := evselfA)
      (ev788 := evmajI) (op827 := op_pp1) (op852 := op_pp2) (op861 := op_npk) (op844 := op_mb)
      (hm875 := hm18) (ev900 := evconcl) (hm935 := hm21) (hm957 := hm20) (hm979 := hm22)
      (ev1020 := evw1) (ev1058 := evw2) (ev1096 := evw3) (ev1126 := evw4) (hc1151 := hc) .. =>
    obtain ⟨rfl, hm1⟩ := flat_length_spec evlenF hes
    subst m1
    have hes_lt : es.length < 2 ^ 39 :=
      repList_length_lt_obs hbd hsub evlenF (by rw [hc]; simp) (by simp) hes
    have evplvls' : ObsFn W "KernelCheck::build_param_lvls_range"
        [.field (off : F), .field (prim.nl : F), .field ((0 : Nat) : F)] h vpUs m2 cs2 := by
      simpa using evplvls
    have hpUs := build_param_lvls_range_spec off prim.nl (by omega) prim.nl 0 (by omega) evplvls'
    simp only [List.drop_zero] at hpUs
    have hptyI := expr_inst_levels_tmOExact (bnd fun c hc' => by rw [hc]; simp [hc'])
      (hprimTy.mono evplvls.heap_extends) hpUs evinst1
    have ext3a : Heap.Extends m3 m3a := by rw [hm3a]; exact Heap.Extends.snoc _ _
    have ext0_3a := evplvls.heap_extends.trans (evinst1.heap_extends.trans ext3a)
    obtain ⟨ext_3a_4, xl, xa, paramDoms, afterP, htupP, hpdoms, -, -, -, hev_pdoms⟩ :=
      collect_n_doms_whnf_spec hA hD hI hC hM nP (by omega) evcolP
        (bnd fun c hc' => by rw [hc]; simp [hc']) (sub fun c hc' => by rw [hc]; simp [hc'])
        (hptyI.mono ext3a) (addrIn_exprInstLevels hprimTyIn)
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupP
    obtain ⟨rfl, rfl⟩ := htupP
    have ext04 := ext0_3a.trans ext_3a_4
    obtain ⟨motDoms, hev_mots, hmotD, -⟩ := build_all_motives_spec ht hwf hS hH hbd hRsub hcl hlv hM
      hnP (by omega) (sub fun c hc' => by rw [hc]; simp [hc'])
      (flatList_mono ext04 hes) (helim.mono ext04) hall evmots
    have ext05 := ext04.trans evmots.heap_extends
    -- Extract total minor count `< 2 ^ 39` via `build_all_minors_walk_rawLen` + `Bounded` on `evlenM`!
    obtain ⟨tot, htot, hraw_min⟩ : ∃ tot,
        flatTotalCtors (ReconView.ofStore t E₀) es = some tot ∧
        RepList kexprListEnum (fun _ (_ : Unit) _ => True) m6 (List.replicate tot ()) vminD := by
      match Obs.«KernelCheck::build_all_minors».obs evmins with
      | .run (cs4 := cs6a) (ev6 := evmw) (hc85 := hc6) .. =>
        exact build_all_minors_walk_rawLen ht hwf hS hH hbd hRsub hcl hlv es
          (sub fun c hc' => by rw [hc]; simp [hc6, hc']) (flatList_mono ext05 hes)
          (fun e he => ⟨(hall e he).1, (hall e he).2.1⟩) evmw
    have htot_lt : tot < 2 ^ 39 := by
      have hlt := repList_length_lt_obs hbd hsub evlenM (by rw [hc]; simp) (by simp) hraw_min
      simpa using hlt
    obtain ⟨minDoms, hmin_len, hev_mins, hminD, -⟩ := build_all_minors_spec ht hwf hS hH hbd
      hRsub hcl hlv hM hnP rfl rfl hfop_len hfop56 htot_lt htot
      (sub fun c hc' => by rw [hc]; simp [hc'])
      (flatList_mono ext05 hes) (fieldList_mono ext05 hfop) (helim.mono ext05)
      (fun e he => ⟨(hall e he).1, (hall e he).2.2.1, (hall e he).2.2.2⟩) evmins
    obtain ⟨rfl, hm7⟩ := kexpr_length_spec evlenM hminD
    subst m7
    have ext06 := ext05.trans evmins.heap_extends
    obtain ⟨hm8, ek', hek', hself_rep⟩ := flat_member_at_spec es k (by omega) (by omega) evfma
      (flatList_mono ext06 hes)
    subst m8
    have hek_eq : ek' = ek := Option.some.inj (hek'.symm.trans hek)
    subst ek'
    obtain ⟨xsa', xssp', xsus', sa, htupS, rsa, hsa, hssp, hsus⟩ := hself_rep
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupS
    obtain ⟨rfl, rfl, rfl, rfl⟩ := htupS
    obtain ⟨hSek, -, hsspIn, hekP⟩ := hall ek (List.mem_of_getElem? hek)
    have hSek' : Held R (ixAddr sa) := hsa ▸ hSek
    obtain ⟨hInd, -⟩ := hI
      (sub fun c hc' => by rw [hc]; simp [hc']) hSek' rsa evci ldci
    obtain ⟨self', _, hself', -, hsnp56, -, -, -, -, hsty_tm, hstyIn, -, hsnpEq, -⟩ :=
      hInd _ _ _ _ _ _ _ _ rfl
    have hself_ind_e : (ReconView.ofStore t E₀).ind ek.addr = some (some self) := hself_ind
    rw [← hsa] at hself_ind
    have hself_eq := Option.some.inj (Option.some.inj (hself'.symm.trans hself_ind))
    subst self'
    subst hsnpEq
    obtain ⟨hP_orig, hP_aux, -⟩ := hekP self hself_ind_e
    have hstyI := expr_inst_levels_tmOExact (bnd fun c hc' => by rw [hc]; simp [hc'])
      hsty_tm (hsus.mono evci.heap_extends) evinst2
    have evpeel' : ObsFn W "KernelCheck::peel_motive_params_subst"
        [vstyI, .field (self.np : F), .field (nP : F), auxVal ek.aux, xssp, .field ((0 : Nat) : F)]
        m10 vsafter m11 cs11 := by simpa using evpeel
    have ext6_10 := evci.heap_extends.trans evinst2.heap_extends
    have hssp_lt : ek.params.length < 2 ^ 39 :=
      repList_length_lt_obs hbd hsub evpeel' (by rw [hc]; simp) (by simp)
        (tmOExactList_mono ext6_10 hssp)
    obtain ⟨selfAfter, hpeel_eq, hselfAfter⟩ := peel_motive_params_subst_spec
      (by omega) (by omega) self.np 0 (by omega)
      (fun i _ hi hni => by
        cases hax : ek.aux
        · have := hP_orig hax; omega
        · have := hP_aux hax; exfalso; exact hni ⟨hax, by omega⟩)
      evpeel' (bnd fun c hc' => by rw [hc]; simp [hc'])
      hstyI (tmOExactList_mono ext6_10 hssp)
    have hselfAfterIn : AddrIn (Held R) (Core.keyOf t) selfAfter :=
      addrIn_peelMotiveParams hsspIn self.np 0 _ _ hpeel_eq (addrIn_exprInstLevels hstyIn)
    obtain ⟨ext12_13, idxRaw, hidxRaw, -, hev_idx⟩ := collect_index_doms_spec hA hD hI hC hM nI
      (by omega) evcolI (bnd fun c hc' => by rw [hc]; simp [hc'])
      (sub fun c hc' => by rw [hc]; simp [hc'])
      (hselfAfter.mono evrev.heap_extends) hselfAfterIn
    have hidxRaw_len : idxRaw.length ≤ 2 ^ 39 := by
      have hlt := repList_length_lt_obs hbd hsub evli (by rw [hc]; simp) (by simp) hidxRaw
      omega
    obtain rfl := binop_add_nat op_mm
    have evli' : ObsFn W "KernelCheck::list_lift_indices"
        [vidxRaw, .field ((es.length + minDoms.length : Nat) : F), .field ((0 : Nat) : F)]
        m13 vidxL m14 cs14 := by simpa using evli
    have hidxL := list_lift_indices_spec (by omega) idxRaw 0 (by omega) evli'
      (bnd fun c hc' => by rw [hc]; simp [hc']) hidxRaw
    have ext14_15 : Heap.Extends m14 m15 := by rw [hm15]; exact Heap.Extends.snoc _ _
    have ext6_15 := ext6_10.trans (evpeel.heap_extends.trans (evrev.heap_extends.trans
      (ext12_13.trans (evli.heap_extends.trans ext14_15))))
    have hhead : TmOExact (Core.keyOf t) m15 (.const (Core.keyOf t (ixAddr sa)) ek.levels)
        (.ptr (.enum kexprEnum) m14.length) :=
      ⟨0, .const (by rw [hm15]; simp)
        (Bytes.repAddressRef_heapMono₂ addrTy ext6_15 rsa) (hsus.mono ext6_15)⟩
    obtain rfl := binop_add_nat op_p1
    obtain rfl := binop_add_nat op_p2
    obtain rfl := binop_add_nat op_p3
    set pre := nP + es.length + minDoms.length + nI
    have hpre_ge : 1 ≤ pre := by omega
    obtain rfl := binop_sub_one_nat hpre_ge op_pm1
    obtain rfl := binop_add_nat op_sl1
    obtain rfl := binop_add_nat op_sl2
    have hwithA := build_major_args_for_self_spec (by omega) (by omega) (by omega) (by omega)
      (bnd fun c hc' => by rw [hc]; simp [hc']) hhead (tmOExactList_mono ext6_15 hssp) evselfA
    have hmaj := build_major_indices_spec (by omega) evmajI hwithA
    obtain rfl := binop_add_one_nat op_pp1
    obtain rfl := binop_sub_one_nat (by omega) op_pp2
    have hsub_cancel : pre + 1 - 1 = pre := by omega
    rw [hsub_cancel] at op_mb
    obtain rfl := binop_add_nat op_npk
    obtain rfl := binop_sub_nat (by omega) op_mb
    have ext17_18 : Heap.Extends m17 m18 := by rw [hm18]; exact Heap.Extends.snoc _ _
    have hbmot : TmOExact (Core.keyOf t) m18 (.bvar (pre - (nP + k)))
        (.ptr (.enum kexprEnum) m17.length) := by
      rw [hm18]; exact tmOExact_bvar_cell (by omega)
    have hconclI := apply_indices_in_conclusion_spec (by omega) evconcl hbmot
    have ext19_20 : Heap.Extends m19 m20 := by rw [hm20]; exact Heap.Extends.snoc _ _
    have ext20_21 : Heap.Extends m20 m21 := by rw [hm21]; exact Heap.Extends.snoc _ _
    have ext21_22 : Heap.Extends m21 m22 := by rw [hm22]; exact Heap.Extends.snoc _ _
    have hb0 : TmOExact (Core.keyOf t) m20 (.bvar 0) (.ptr (.enum kexprEnum) m19.length) := by
      rw [hm20]; exact tmOExact_bvar_cell (by decide)
    have hconcl : TmOExact (Core.keyOf t) m21
        (.app (conclIndices (.bvar (pre - (nP + k))) nI) (.bvar 0))
        (.ptr (.enum kexprEnum) m20.length) := by
      obtain ⟨k1, r1⟩ := hconclI.mono (ext19_20.trans ext20_21)
      obtain ⟨k2, r2⟩ := hb0.mono ext20_21
      exact ⟨max k1 k2, .app (by rw [hm21]; simp)
        (tmExact_depth_le r1 _ (Nat.le_max_left _ _))
        (tmExact_depth_le r2 _ (Nat.le_max_right _ _))⟩
    have ext17_22 := ext17_18.trans (evconcl.heap_extends.trans (ext19_20.trans (ext20_21.trans ext21_22)))
    have ext14_22 := ext14_15.trans (evselfA.heap_extends.trans (evmajI.heap_extends.trans ext17_22))
    have ext6_22 := ext6_15.trans (evselfA.heap_extends.trans (evmajI.heap_extends.trans ext17_22))
    have ext0_22 := ext06.trans ext6_22
    have hcore : TmOExact (Core.keyOf t) m22
        (.forallE
          (appBVarsDown (if ek.aux then specParamsLifted (.const (Core.keyOf t (ixAddr sa)) ek.levels)
            ek.params (es.length + minDoms.length + nI)
            else appBVarsDec (.const (Core.keyOf t (ixAddr sa)) ek.levels) nP (pre - 1)) nI)
          (.app (conclIndices (.bvar (pre - (nP + k))) nI) (.bvar 0))
          (bmeta (elimLevel off)))
        (.ptr (.enum kexprEnum) m21.length) := by
      obtain ⟨k1, r1⟩ := hmaj.mono ext17_22
      obtain ⟨k2, r2⟩ := hconcl.mono ext21_22
      exact ⟨max k1 k2, .forallE (by rw [hm22]; simp)
        (tmExact_depth_le r1 _ (Nat.le_max_left _ _))
        (tmExact_depth_le r2 _ (Nat.le_succ_of_le (Nat.le_max_right _ _))) (helim.mono ext0_22)⟩
    have hw1 := wrap_foralls_spec (liftIndices idxRaw (es.length + minDoms.length)) evw1 hcore
      (tmOExactList_mono ext14_22 (by simpa [liftIndices] using hidxL)) (helim.mono ext0_22)
    have hw2 := wrap_foralls_spec minDoms evw2 hw1
      (tmOExactList_mono (ext6_22.trans evw1.heap_extends) hminD)
      (helim.mono (ext0_22.trans evw1.heap_extends))
    have ext5_24 := evmins.heap_extends.trans (ext6_22.trans (evw1.heap_extends.trans evw2.heap_extends))
    have hw3 := wrap_foralls_spec motDoms evw3 hw2 (tmOExactList_mono ext5_24 hmotD)
      (helim.mono (ext05.trans ext5_24))
    have ext4_25 := evmots.heap_extends.trans (ext5_24.trans evw3.heap_extends)
    have hw4 := wrap_foralls_spec paramDoms evw4 hw3 (tmOExactList_mono ext4_25 hpdoms)
      (helim.mono (ext04.trans ext4_25))
    refine ⟨_, tot, htot, htot_lt,
      ((hev_pdoms.and hev_mots).and (hev_mins.and hev_idx)).mono fun f ⟨⟨hfp, hfm⟩, ⟨hfmin, hfi⟩⟩ => ?_,
      hw4⟩
    simp only [recTypeAt, he0, hek, hfop_eq]
    rw [show (ReconView.ofStore t E₀).ind e0.addr = some (some prim) from hprim_ind,
      hself_ind_e]
    dsimp only
    rw [hfp, hfm]
    dsimp only
    rw [hfmin, hpeel_eq, hni_eq, hsa]
    dsimp only
    cases hcd : collectDoms (ReconView.ofStore t E₀) f nI selfAfter with
    | none => simp [hcd] at hfi
    | some p =>
      simp only [hcd, Option.map_some, Option.some.injEq] at hfi
      subst hfi; rfl

/-- **`KernelCheck::build_rec_type`** refines `recTypeAt (ReconView.ofStore t E₀)` at `Eventually`
on `TmOExact`, also exporting `flatTotalCtors < 2 ^ 39`. -/
theorem build_rec_type_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    (hM : ModeledAnswers rootCalls (Held R) (ReconView.ofStore t E₀))
    {es : List FlatEntry} {e0 ek : FlatEntry} {prim self : IndData} {fop : List Nat}
    {nP nI off k : Nat} {xrc xity xindnl xelim xflat xfop r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hoff : off ≤ 1) (hnP : nP < 72057594037927936) (hnI : nI < 72057594037927936)
    (hni_eq : self.ni = nI)
    (he0 : es[0]? = some e0) (hek : es[k]? = some ek)
    (hprim_ind : indDataAt t E₀ e0.addr = some (some prim))
    (hself_ind : indDataAt t E₀ ek.addr = some (some self))
    (hfop_eq : flatOwnParams (ReconView.ofStore t E₀) es = some fop)
    (hfop_len : fop.length = es.length) (hfop56 : ∀ n ∈ fop, n < 72057594037927936)
    (hsub : ∀ cl ∈ cs, cl ∈ rootCalls)
    (helim : RepKLevel h (elimLevel off) xelim)
    (hes : RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h es xflat)
    (hfop : RepList fieldListEnum RepNatField h fop xfop)
    (hall : ∀ e ∈ es, Held R e.addr ∧ (∃ info, indDataAt t E₀ e.addr = some (some info)) ∧
      (∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p) ∧
      FlatEntryParamsOk (ReconView.ofStore t E₀) nP e)
    (ev : ObsFn W "KernelCheck::build_rec_type"
      [xrc, xity, xindnl, .field (nP : F), .field (nI : F),
        xelim, .field (off : F), xflat, xfop, .field (k : F)] h r h' cs) :
    ∃ (Rty : KExpr) (tot : Nat),
      flatTotalCtors (ReconView.ofStore t E₀) es = some tot ∧ tot < 2 ^ 39 ∧
      Eventually (fun f => recTypeAt (ReconView.ofStore t E₀) f es off nP k = some Rty) ∧
      TmOExact (Core.keyOf t) h' Rty r := by
  have sub : ∀ {cs' : List (Call F)}, (∀ cl ∈ cs', cl ∈ cs) → ∀ cl ∈ cs', cl ∈ rootCalls :=
    fun hs cl hcl' => hsub cl (hs cl hcl')
  have hI : IndAnswers rootCalls (Held R) (Core.keyOf t) (ReconView.ofStore t E₀) :=
    indAnswers_ofStore ht hwf hS hH hbd hRsub hcl hlv
  match Obs.«KernelCheck::build_rec_type».obs ev with
  | .other (m2 := m1) (cs13 := cs1) (x_prim_addr := xpa) (x__pia := xpia)
      (x__pisp := xpisp) (x__piou := xpiou) (v57 := vci) (m58 := m2) (p66 := pci) (cs72 := cs2)
      (ev15 := evfma) (ev74 := evci) (ld68 := ldci) (hne238 := hne) (hc344 := hc) .. =>
    have evfma' : ObsFn W "KernelCheck::flat_member_at" [xflat, .field ((0 : Nat) : F)]
        h (.tuple [xpa, xpia, xpisp, xpiou]) m1 cs1 := by
      simpa using evfma
    have h0lt : 0 < es.length := (List.getElem?_eq_some_iff.mp he0).1
    obtain ⟨hm1, e0', he0', hrep0⟩ := flat_member_at_spec es 0 h0lt (by decide) evfma' hes
    subst m1
    have he0_eq : e0' = e0 := Option.some.inj (he0'.symm.trans he0); subst e0'
    obtain ⟨_, _, _, pa, htup, rpa, hpa, -, -⟩ := hrep0
    injection htup with hl; injection hl with h1 _; subst h1
    have hSe0 : Held R (ixAddr pa) := hpa ▸ (hall e0 (List.mem_of_getElem? he0)).1
    obtain ⟨-, hOther⟩ := hI
      (sub fun c hc' => by rw [hc]; simp [hc']) hSe0 rpa evci ldci
    have hnone := hOther hne
    change indDataAt t E₀ (ixAddr pa) = some none at hnone
    rw [← hpa] at hprim_ind; rw [hprim_ind] at hnone; cases hnone
  | .Induct (m2 := m1) (cs13 := cs1) (x_prim_addr := xpa) (x__pia := xpia)
      (x__pisp := xpisp) (x__piou := xpiou) (m58 := m2) (p66 := pci) (cs72 := cs2)
      (x_prim_nlvls := xpnl) (x_prim_ty := xpty) (cs138 := cs3)
      (ev15 := evfma) (ev74 := evci) (ld68 := ldci) (ev140 := evfrom) (hc237 := hc) .. =>
    have evfma' : ObsFn W "KernelCheck::flat_member_at" [xflat, .field ((0 : Nat) : F)]
        h (.tuple [xpa, xpia, xpisp, xpiou]) m1 cs1 := by
      simpa using evfma
    have h0lt : 0 < es.length := (List.getElem?_eq_some_iff.mp he0).1
    obtain ⟨hm1, e0', he0', hrep0⟩ := flat_member_at_spec es 0 h0lt (by decide) evfma' hes
    subst m1
    have he0_eq : e0' = e0 := Option.some.inj (he0'.symm.trans he0); subst e0'
    obtain ⟨_, _, _, pa, htup, rpa, hpa, -, -⟩ := hrep0
    injection htup with hl; injection hl with h1 _; subst h1
    have hSe0 : Held R (ixAddr pa) := hpa ▸ (hall e0 (List.mem_of_getElem? he0)).1
    obtain ⟨hInd, -⟩ := hI
      (sub fun c hc' => by rw [hc]; simp [hc']) hSe0 rpa evci ldci
    obtain ⟨prim', _, hprim', hnl32, -, -, -, -, hnlEq, hpty, hptyIn, -⟩ := hInd _ _ _ _ _ _ _ _ rfl
    rw [← hpa] at hprim_ind
    have hpeq := Option.some.inj (Option.some.inj (hprim'.symm.trans hprim_ind))
    subst prim'
    subst hnlEq
    exact build_rec_type_from_spec ht hwf hS hH hbd hRsub hcl hlv hM hoff hnP hnI hnl32 hni_eq
      he0 hek (by rwa [← hpa]) hself_ind hfop_eq hfop_len hfop56
      (sub fun c hc' => by rw [hc]; simp [hc']) hpty hptyIn (helim.mono evci.heap_extends)
      (flatList_mono evci.heap_extends hes) (fieldList_mono evci.heap_extends hfop) hall evfrom

/-! ## Section 5: Reconstructed recursor rule bodies -/

/-- **`KernelCheck::apply_ihs_full`** refines `applyIhs (ReconView.ofStore t E₀)` on `TmOExact`. -/
theorem apply_ihs_full_spec {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {rm fop : List Nat} {norm : List KExpr} {peers : List Bytes.Address}
    {nP nMot nMin nFields : Nat} {recLvls : List KLevel} {elim : KLevel}
    {xrm xnorm xpeers xfop xrlvls xelim : SourceValue F}
    (hbound : nP + nMot + nMin + nFields < 4611686018427387904 - 2 ^ 39)
    (hrm_lt_b : rm.length < 4611686018427387904)
    (hfop_lt_b : fop.length < 4611686018427387904)
    (hnorm_len : norm.length = nFields)
    (hpeers_len : peers.length = fop.length)
    (hfop56 : ∀ n ∈ fop, n < 72057594037927936)
    (hrm_lt : ∀ m ∈ rm, m < fop.length) :
    ∀ (ri : List Nat) (k : Nat) {H : KExpr} {xh xri r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      k + ri.length = rm.length →
      (∀ fi ∈ ri, fi < nFields) →
      Bounded cs →
      TmOExact (Core.keyOf t) h H xh →
      RepList fieldListEnum RepNatField h ri xri →
      RepList fieldListEnum RepNatField h rm xrm →
      RepList kexprListEnum (TmOExact (Core.keyOf t)) h norm xnorm →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h peers xpeers →
      RepList fieldListEnum RepNatField h fop xfop →
      RepKLevelList h recLvls xrlvls →
      RepKLevel h elim xelim →
      ObsFn W "KernelCheck::apply_ihs_full"
        [xh, xri, xrm, xnorm, xpeers, xfop, .field (nP : F), .field (nMot : F),
          .field (nMin : F), .field (nFields : F), xrlvls, .field (k : F), xelim] h r h' cs →
      ∃ B : KExpr,
        applyIhs (ReconView.ofStore t E₀) rm norm (peers.map ixAddr) fop nP nMot nMin nFields
          recLvls elim H k ri = some B ∧
        TmOExact (Core.keyOf t) h' B r := by
  intro ri
  induction ri with
  | nil =>
    intro k H xh xri r h h' cs _ _ _ hH hri _ _ _ _ _ _ ev
    match Obs.«KernelCheck::apply_ihs_full».obs ev with
    | .Nil (he21 := hr0) (he22 := hh0) .. =>
      cases hr0; cases hh0; exact ⟨H, rfl, hH⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hri ld
      cases hcons
  | cons fieldIdx rest ih =>
    intro k H xh xri r h h' cs hklen hfi_lt hbnd hH hri hrm hnorm hpeers hfop hrlvls helim ev
    have bnd : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    match Obs.«KernelCheck::apply_ihs_full».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hri ld
    | .Cons (x_field_idx := xfi) (x_rest := xrest) (v41 := vmem) (m42 := m1) (cs52 := cs1)
        (v78 := vpeer) (m79 := m3) (cs89 := cs2) (m110 := m2) (v121 := vtnp) (m122 := m4)
        (cs132 := cs3) (v158 := vbaseD) (x166 := x166) (x174 := x174)
        (v194 := vdom) (m195 := m5) (cs205 := cs4) (v224 := vdomL1) (m225 := m6) (cs235 := cs5)
        (v239 := vdiff1) (v270 := vdomL2) (m271 := m7) (cs281 := cs6) (v285 := vmm)
        (m318 := m8) (cs329 := cs7) (x_forall_doms := xfds) (x_inner_body := xinner)
        (v356 := vnfds) (m357 := m9) (cs367 := cs8) (v378 := vinnerD) (m397 := m10)
        (v427 := vwp) (m428 := m11) (cs438 := cs9) (v443 := vid1)
        (v480 := vwm) (m481 := m12) (cs491 := cs10) (v496 := vid2) (x518 := x518)
        (v542 := vwmin) (m543 := m13) (cs553 := cs11) (v558 := vid3) (x580 := x580) (x588 := x588)
        (m614 := m14) (cs_sigqtzlz := cs12) (x_dargs := xdargs)
        (v652 := vidxArgs) (m653 := m15) (cs663 := cs13) (v682 := vwithIdx) (m683 := m16)
        (cs693 := cs14) (v712 := vfb) (x720 := x720) (x728 := x728) (m748 := m17)
        (v770 := vfldApp) (m771 := m18) (cs781 := cs15) (m808 := m19)
        (v838 := vih) (m839 := m20) (cs849 := cs16) (m877 := m21) (cs910 := cs17) (v924 := vk1)
        (ld12 := ld) (ev54 := evrm) (hm118 := hm2) (ev91 := evpeer) (ev134 := evfop)
        (op189 := op_b1) (op181 := op_b2) (op173 := op_b3) (ev207 := evnorm)
        (op261 := op_d1) (ev237 := evl1) (op307 := op_mm) (ev283 := evl2)
        (ev331 := evpeel) (ev369 := evlen) (op393 := op_id) (hm407 := hm10)
        (op472 := op_p1) (ev440 := evap) (op533 := op_m1) (op525 := op_m2) (ev493 := evam)
        (op603 := op_n1) (op595 := op_n2) (op587 := op_n3) (ev555 := evan)
        (ev_dbxiljsh := evsp) (ev665 := evdrop) (ev695 := evapp1)
        (op743 := op_f1) (op735 := op_f2) (op727 := op_f3) (hm758 := hm17)
        (ev783 := evxs) (hm818 := hm19) (ev851 := evwl) (hm887 := hm21)
        (op1016 := opk1) (ev912 := evrec) (hc1025 := hc) .. =>
      obtain ⟨fi', rest', h1, hfi, hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hri ld
      injection h1 with h1f h1r; subst h1f h1r
      rw [hfi] at evnorm op_d1 op_f2 hc
      have hfi_cur : fieldIdx < nFields := hfi_lt fieldIdx (List.mem_cons_self ..)
      have hk_lt : k < rm.length := by simp only [List.length_cons] at hklen; omega
      obtain ⟨hm1, hrm_res⟩ := field_lookup_or_default_spec evrm hrm
      subst m1
      rw [fval_natCast (by omega)] at hrm_res
      obtain ⟨memIdx, hrm_k, rfl⟩ : ∃ m, rm[k]? = some m ∧ vmem = .field (m : F) := by
        rcases hrm_res with ⟨x, hx, hv⟩ | ⟨heq, _⟩
        · exact ⟨x, hx, hv⟩
        · omega
      have hmem_lt : memIdx < fop.length := hrm_lt memIdx (List.mem_of_getElem? hrm_k)
      have ext02 : Heap.Extends h m2 := by rw [hm2]; exact Heap.Extends.snoc _ _
      obtain ⟨hm3, hpeer_res⟩ := addr_lookup_or_default_spec evpeer
        (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) ext02 hpeers)
      subst m3
      rw [fval_natCast (by omega)] at hpeer_res
      obtain ⟨tba, hpeer_m, rtba⟩ : ∃ x, peers[memIdx]? = some x ∧ Bytes.RepAddressRef addrTy m2 x vpeer := by
        rcases hpeer_res with ⟨x, hx, hr⟩ | ⟨heq, _⟩
        · exact ⟨x, hx, hr⟩
        · omega
      obtain ⟨hm4, hfop_res⟩ := field_lookup_or_default_spec evfop (fieldList_mono ext02 hfop)
      subst m4
      rw [fval_natCast (by omega)] at hfop_res
      obtain ⟨tnp, hfop_m, rfl⟩ : ∃ x, fop[memIdx]? = some x ∧ vtnp = .field (x : F) := by
        rcases hfop_res with ⟨x, hx, hv⟩ | ⟨heq, _⟩
        · exact ⟨x, hx, hv⟩
        · omega
      have htnp56 : tnp < 72057594037927936 := hfop56 tnp (List.mem_of_getElem? hfop_m)
      obtain rfl := binop_add_nat op_b1
      obtain rfl := binop_add_nat op_b2
      obtain rfl := binop_add_nat op_b3
      obtain ⟨⟨dom, hnorm_fi, hdom⟩, hm5⟩ := kexpr_lookup_spec evnorm (tmOExactList_mono ext02 hnorm)
      subst m5
      rw [fval_natCast (by omega)] at hnorm_fi
      obtain rfl := binop_sub_nat (by omega) op_d1
      have evl1' : ObsFn W "KernelSubst::expr_lift"
          [vdom, .field ((nFields - fieldIdx : Nat) : F), .field ((0 : Nat) : F)] m2 vdomL1 m6 cs5 := by
        simpa using evl1
      have hdomL1 := expr_lift_tmOExact (by omega) (by decide)
        (bnd fun c hc' => by rw [hc]; simp [hc']) hdom evl1'
      obtain rfl := binop_add_nat op_mm
      have hdomL2 := expr_lift_tmOExact (by omega) (by omega)
        (bnd fun c hc' => by rw [hc]; simp [hc']) hdomL1 evl2
      obtain ⟨xl, xb, htupP, ext78, hfds, hinner⟩ := peel_leading_foralls_spec evpeel
        (bnd fun c hc' => by rw [hc]; simp [hc']) hdomL2
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupP
      obtain ⟨rfl, rfl⟩ := htupP
      obtain ⟨rfl, hm9⟩ := kexpr_length_spec evlen hfds
      subst m9
      set domL := (dom.liftLooseBVars (nFields - fieldIdx) 0).liftLooseBVars (nMot + nMin) nFields
      set fds := (peelAll domL).1
      set inner := (peelAll domL).2
      have hfds_lt : fds.length < 2 ^ 39 :=
        repList_length_lt_obs hbnd (fun _ h => h) evlen (by rw [hc]; simp) (by simp) hfds
      obtain rfl := binop_add_nat op_id
      set innerDepth := nP + nMot + nMin + nFields + fds.length
      have hid_ge : 1 ≤ innerDepth := by omega
      have ext28 := evl1.heap_extends.trans (evl2.heap_extends.trans ext78)
      have ext8_10 : Heap.Extends m8 m10 := by rw [hm10]; exact Heap.Extends.snoc _ _
      have ext0_10 := ext02.trans (ext28.trans ext8_10)
      have hconstT : TmOExact (Core.keyOf t) m10 (.const (Core.keyOf t (ixAddr tba)) recLvls)
          (.ptr (.enum kexprEnum) m8.length) :=
        ⟨0, .const (by rw [hm10]; simp)
          (Bytes.repAddressRef_heapMono₂ addrTy (ext28.trans ext8_10) rtba)
          (hrlvls.mono ext0_10)⟩
      obtain rfl := binop_sub_one_nat hid_ge op_p1
      have hwp := build_apply_bvars_decreasing_spec (by omega) (by omega) (by omega) evap hconstT
      obtain rfl := binop_sub_one_nat hid_ge op_m1
      obtain rfl := binop_sub_nat (by omega) op_m2
      have hwm := build_motive_apps_spec (by omega) (by omega) (by omega) evam hwp
      obtain rfl := binop_sub_one_nat hid_ge op_n1
      obtain rfl := binop_sub_nat (by omega) op_n2
      obtain rfl := binop_sub_nat (by omega) op_n3
      have hwmin := build_minor_apps_spec (by omega) (by omega) (by omega) evan hwm
      have ext8_13 := ext8_10.trans (evap.heap_extends.trans (evam.heap_extends.trans evan.heap_extends))
      obtain ⟨-, -, hdargs⟩ := collect_spine_zeta_spec (hinner.mono ext8_13)
        (bnd fun c hc' => by rw [hc]; simp [hc']) evsp
      obtain ⟨-, hidxArgs, hm15⟩ := kexpr_drop_spec evdrop hdargs
      subst m15
      rw [fval_natCast (by omega)] at hidxArgs
      have hwithIdx := apply_spine_expr_spec (inner.getAppArgs.drop tnp) evapp1
        (hwmin.mono evsp.heap_extends) hidxArgs
      obtain rfl := binop_sub_one_nat (by omega) op_f1
      obtain rfl := binop_sub_nat (by omega) op_f2
      obtain rfl := binop_add_nat op_f3
      have ext16_17 : Heap.Extends m16 m17 := by rw [hm17]; exact Heap.Extends.snoc _ _
      have hbfb : TmOExact (Core.keyOf t) m17 (.bvar (nFields - 1 - fieldIdx + fds.length))
          (.ptr (.enum kexprEnum) m16.length) := by
        rw [hm17]; exact tmOExact_bvar_cell (by omega)
      have hfldApp := build_apply_xs_spec (by omega) evxs hbfb
      have ext18_19 : Heap.Extends m18 m19 := by rw [hm19]; exact Heap.Extends.snoc _ _
      have happ_ih : TmOExact (Core.keyOf t) m19
          (.app (appSpine (appBVarsDec (appBVarsDec (appBVarsDec (.const (Core.keyOf t (ixAddr tba)) recLvls)
              nP (innerDepth - 1)) nMot (innerDepth - 1 - nP)) nMin (innerDepth - 1 - nP - nMot))
              (inner.getAppArgs.drop tnp))
            (appBVarsDown (.bvar (nFields - 1 - fieldIdx + fds.length)) fds.length))
          (.ptr (.enum kexprEnum) m18.length) := by
        obtain ⟨k1, r1⟩ := hwithIdx.mono (ext16_17.trans (evxs.heap_extends.trans ext18_19))
        obtain ⟨k2, r2⟩ := hfldApp.mono ext18_19
        exact ⟨max k1 k2, .app (by rw [hm19]; simp)
          (tmExact_depth_le r1 _ (Nat.le_max_left _ _))
          (tmExact_depth_le r2 _ (Nat.le_max_right _ _))⟩
      have ext8_19 := ext8_13.trans (evsp.heap_extends.trans (evapp1.heap_extends.trans
        (ext16_17.trans (evxs.heap_extends.trans ext18_19))))
      have ext0_19 := ext02.trans (ext28.trans ext8_19)
      have hih_lam := wrap_lams_spec fds evwl happ_ih (tmOExactList_mono ext8_19 hfds) (helim.mono ext0_19)
      have ext20_21 : Heap.Extends m20 m21 := by rw [hm21]; exact Heap.Extends.snoc _ _
      have ext0_21 := ext0_19.trans (evwl.heap_extends.trans ext20_21)
      have hnextH : TmOExact (Core.keyOf t) m21
          (.app H (wrapLams (.app (appSpine (appBVarsDec (appBVarsDec (appBVarsDec
              (.const (Core.keyOf t (ixAddr tba)) recLvls) nP (innerDepth - 1)) nMot (innerDepth - 1 - nP))
              nMin (innerDepth - 1 - nP - nMot)) (inner.getAppArgs.drop tnp))
            (appBVarsDown (.bvar (nFields - 1 - fieldIdx + fds.length)) fds.length)) fds elim))
          (.ptr (.enum kexprEnum) m20.length) := by
        obtain ⟨k1, r1⟩ := hH.mono ext0_21
        obtain ⟨k2, r2⟩ := hih_lam.mono ext20_21
        exact ⟨max k1 k2, .app (by rw [hm21]; simp)
          (tmExact_depth_le r1 _ (Nat.le_max_left _ _))
          (tmExact_depth_le r2 _ (Nat.le_max_right _ _))⟩
      obtain rfl := binop_add_one_nat opk1
      obtain ⟨B, hB, hBtm⟩ := ih (k + 1) (by simp only [List.length_cons] at hklen; omega)
        (fun fi hfi => hfi_lt fi (List.mem_cons_of_mem _ hfi))
        (bnd fun c hc' => by rw [hc]; simp [hc']) hnextH
        (fieldList_mono ext0_21 hrest) (fieldList_mono ext0_21 hrm)
        (tmOExactList_mono ext0_21 hnorm)
        (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) ext0_21 hpeers)
        (fieldList_mono ext0_21 hfop) (hrlvls.mono ext0_21) (helim.mono ext0_21) evrec
      have hmap_get : (peers.map ixAddr)[memIdx]? = some (ixAddr tba) := by
        rw [List.getElem?_map, hpeer_m]; rfl
      refine ⟨B, ?_, hBtm⟩
      simp only [applyIhs]
      rw [hrm_k, Option.getD_some, hmap_get, hnorm_fi, hfop_m]
      dsimp only
      rw [Option.getD_some, show (ReconView.ofStore t E₀).key = Core.keyOf t from rfl, hB]

/-- **`KernelCheck::build_rule_rhs`** refines `ruleBody (ReconView.ofStore t E₀)` at `Eventually`
on `TmOExact`. -/
theorem build_rule_rhs_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    (hM : ModeledAnswers rootCalls (Held R) (ReconView.ofStore t E₀))
    {es : List FlatEntry} {fop : List Nat} {peers : List Bytes.Address}
    {cty : KExpr} {minorIdx nP nMot nMin nOwn : Nat}
    {us recLvls : List KLevel} {aux : Bool} {sp : List KExpr} {elim : KLevel}
    {xrc xcty xus xrlvls xflat xpeers xfop xsp xelim r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hnP : nP < 72057594037927936) (hnMot : nMot < 72057594037927936)
    (hnMin : nMin < 72057594037927936) (hnOwn : nOwn < 72057594037927936)
    (hminor_lt : minorIdx < nMin)
    (hfop_len : fop.length = es.length) (hfop_lt_b : fop.length < 4611686018427387904)
    (hpeers_len : peers.length = fop.length)
    (hfop56 : ∀ n ∈ fop, n < 72057594037927936)
    (hsub : ∀ cl ∈ cs, cl ∈ rootCalls)
    (hcty : TmOExact (Core.keyOf t) h cty xcty) (hctyIn : AddrIn (Held R) (Core.keyOf t) cty)
    (hus : RepKLevelList h us xus) (hrlvls : RepKLevelList h recLvls xrlvls)
    (hes : RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h es xflat)
    (hpeers : RepList addrListEnum (Bytes.RepAddressRef addrTy) h peers xpeers)
    (hfop : RepList fieldListEnum RepNatField h fop xfop)
    (hsp : RepList kexprListEnum (TmOExact (Core.keyOf t)) h sp xsp)
    (hspIn : ∀ e ∈ sp, AddrIn (Held R) (Core.keyOf t) e)
    (helim : RepKLevel h elim xelim)
    (ev : ObsFn W "KernelCheck::build_rule_rhs"
      [xrc, xcty, .field (minorIdx : F), .field (nP : F), .field (nMot : F), .field (nMin : F),
        .field (nOwn : F), xus, xrlvls, xflat, xpeers, xfop, auxVal aux, xsp, xelim] h r h' cs) :
    ∃ B : KExpr,
      Eventually (fun f => ruleBody (ReconView.ofStore t E₀) f es fop (peers.map ixAddr) cty
        minorIdx nP nMot nMin nOwn us recLvls aux sp elim = some B) ∧
      TmOExact (Core.keyOf t) h' B r := by
  have sub : ∀ {cs' : List (Call F)}, (∀ cl ∈ cs', cl ∈ cs) → ∀ cl ∈ cs', cl ∈ rootCalls :=
    fun hs cl hcl' => hsub cl (hs cl hcl')
  have bnd : ∀ {cs' : List (Call F)}, (∀ cl ∈ cs', cl ∈ cs) → Bounded cs' :=
    fun hs => RomBound.bounded_mono hbd (sub hs)
  have hinj : Function.Injective (Core.keyOf t) := fun _ _ he => Core.keyOf_inj hwf he
  have hA : AddrOf (Core.keyOf t) (ReconView.ofStore t E₀) := addrOf_ofStore (E₀ := E₀) hwf
  have hD : DefnAnswers rootCalls (Held R) (Core.keyOf t) (ReconView.ofStore t E₀) :=
    defnAnswers_ofStore ht hwf hS hH hbd hRsub hcl hlv
  have hI : IndAnswers rootCalls (Held R) (Core.keyOf t) (ReconView.ofStore t E₀) :=
    indAnswers_ofStore ht hwf hS hH hbd hRsub hcl hlv
  have hC : CtorOfAnswers rootCalls (Held R) (ReconView.ofStore t E₀) :=
    ctorOfAnswers_ofStore hS hH hbd hRsub hcl
  match Obs.«KernelCheck::build_rule_rhs».obs ev with
  | .run (v1 := vctyI) (m2 := m1) (cs12 := cs1) (v31 := vraw) (m32 := m2) (cs_mdzbjznf := cs2)
      (v61 := vnf) (m62 := m3) (cs72 := cs3) (v90 := vtot) (x98 := x98) (x106 := x106)
      (v126 := vptypes) (m127 := m4) (cs137 := cs4) (v164 := vafter) (m165 := m5) (cs175 := cs5)
      (m249 := m6) (cs260 := cs6) (m295 := m5a) (m308 := m5b) (m321 := m5c) (m334 := m5d)
      (x_field_doms := xfds) (x_rec_indices := xri) (x_rec_member_idxs := xrm)
      (x__ret_ty := xret) (x_norm_doms := xnorm) (v407 := vnf2) (m410 := m7) (cs418 := cs7)
      (v437 := vminB) (x445 := x445) (y446 := y446) (x462 := x462) (m482 := m8)
      (v504 := vhead) (m505 := m9) (cs515 := cs8) (cs552 := cs9)
      (ev14 := evinst) (ev_voldfhzh := evpz) (ev74 := evcnt)
      (op121 := op_t1) (op113 := op_t2) (op105 := op_t3)
      (ev139 := evrpc) (ev177 := evpeel)
      (hm303 := hm5a) (hm316 := hm5b) (hm329 := hm5c) (hm342 := hm5d) (ev262 := evwfc)
      (ev420 := evlen) (heq436 := heqnf)
      (op460 := op_m1) (op477 := op_m2) (op469 := op_m3) (op452 := op_m4)
      (hm492 := hm8) (ev517 := evfb) (ev554 := evih) (hc658 := hc) .. =>
    have hctyI := expr_inst_levels_tmOExact (bnd fun c hc' => by rw [hc]; simp [hc']) hcty hus evinst
    obtain ⟨raw, hraw_peel, hraw⟩ := peel_n_foralls_zeta_spec nOwn (by omega) hctyI
      (bnd fun c hc' => by rw [hc]; simp [hc']) evpz
    have hraw_len : (peelAll raw).1.length ≤ 2 ^ 39 :=
      peelAll_length_le_of_count_foralls hbd hsub evcnt (by rw [hc]; simp)
        (sub fun c hc' => by rw [hc]; simp [hc']) hraw
    have evcnt' : ObsFn W "KernelCheck::count_foralls_body" [vraw, .field ((0 : Nat) : F)]
        m2 vnf m3 cs3 := by simpa using evcnt
    have hvnf_eq := count_foralls_body_spec evcnt' (bnd fun c hc' => by rw [hc]; simp [hc']) hraw
    subst hvnf_eq
    simp only [Nat.zero_add] at op_t3 heqnf evfb evih hc
    set nFields := (peelAll raw).1.length
    obtain rfl := binop_add_nat op_t1
    obtain rfl := binop_add_nat op_t2
    obtain rfl := binop_add_nat op_t3
    have ext04 := evinst.heap_extends.trans (evpz.heap_extends.trans
      (evcnt.heap_extends.trans evrpc.heap_extends))
    have evpeel' : ObsFn W "KernelCheck::peel_ctor_params_subst"
        [xrc, vctyI, .field (nOwn : F), .field (nOwn : F), .field ((0 : Nat) : F),
          auxVal aux, xsp, .field ((0 : Nat) : F), vptypes] m4 vafter m5 cs5 := by simpa using evpeel
    have hsp_lt : sp.length < 2 ^ 39 :=
      repList_length_lt_obs hbd hsub evpeel' (by rw [hc]; simp) (by simp)
        (tmOExactList_mono ext04 hsp)
    obtain ⟨ext45, after, hafter, hafterIn, hev_peel⟩ :=
      peel_ctor_params_subst_spec hA hD hI hC hM (by omega) (by decide) (by omega) hspIn
        nOwn 0 (by omega) (fun i _ hi _ => by omega)
        evpeel' (bnd fun c hc' => by rw [hc]; simp [hc']) (sub fun c hc' => by rw [hc]; simp [hc'])
        (hctyI.mono (evpz.heap_extends.trans (evcnt.heap_extends.trans evrpc.heap_extends)))
        (addrIn_exprInstLevels hctyIn) (tmOExactList_mono ext04 hsp)
    have ext5a : Heap.Extends m5 m5a := by rw [hm5a]; exact Heap.Extends.snoc _ _
    have ext5b : Heap.Extends m5a m5b := by rw [hm5b]; exact Heap.Extends.snoc _ _
    have ext5c : Heap.Extends m5b m5c := by rw [hm5c]; exact Heap.Extends.snoc _ _
    have ext5d : Heap.Extends m5c m5d := by rw [hm5d]; exact Heap.Extends.snoc _ _
    have ext5_d := ext5a.trans (ext5b.trans (ext5c.trans ext5d))
    have ext0_5d := ext04.trans (ext45.trans ext5_d)
    have hnil1 : RepList kexprListEnum (TmOExact (Core.keyOf t)) m5d []
        (.ptr (.enum kexprListEnum) m5.length) :=
      tmOExactList_mono (ext5b.trans (ext5c.trans ext5d)) (by rw [hm5a]; exact Lib.rep_store_nil m5)
    have hnil2 : RepList fieldListEnum RepNatField m5d []
        (.ptr (.enum fieldListEnum) m5a.length) :=
      fieldList_mono (ext5c.trans ext5d) (by rw [hm5b]; exact Lib.rep_store_nil m5a)
    have hnil3 : RepList fieldListEnum RepNatField m5d []
        (.ptr (.enum fieldListEnum) m5b.length) :=
      fieldList_mono ext5d (by rw [hm5c]; exact Lib.rep_store_nil m5b)
    have hnil4 : RepList kexprListEnum (TmOExact (Core.keyOf t)) m5d []
        (.ptr (.enum kexprListEnum) m5c.length) := by
      rw [hm5d]; exact Lib.rep_store_nil m5c
    have hnil1U : RepList kexprListEnum (fun _ (_ : Unit) _ => True) m5d []
        (.ptr (.enum kexprListEnum) m5.length) :=
      repList_heapMono₂ kexprListEnum (fun _ _ _ _ _ t => t) (ext5b.trans (ext5c.trans ext5d))
        (by rw [hm5a]; exact Lib.rep_store_nil m5)
    have evwfc' : ObsFn W "KernelCheck::walk_fields_classify"
        [xrc, vafter, xflat, .ptr (.enum kexprListEnum) m5.length,
          .ptr (.enum fieldListEnum) m5a.length, .ptr (.enum fieldListEnum) m5b.length,
          .ptr (.enum kexprListEnum) m5c.length, .field 0, .field ((0 : Nat) : F), vptypes]
        m5d (.tuple [xfds, xri, xrm, xret, xnorm]) m6 cs6 := by simpa using evwfc
    have hafter_len : (peelAll after).1.length < 2 ^ 39 := by
      obtain ⟨_, _, _, _, _, dsU, htupU, hlenU, hrepU⟩ :=
        walk_fields_classify_doms_len evwfc' (bnd fun c hc' => by rw [hc]; simp [hc'])
          (hafter.mono ext5_d) hnil1U
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupU
      obtain ⟨rfl, -, -, -, -⟩ := htupU
      have hltU := repList_length_lt_obs hbd hsub evlen (by rw [hc]; simp) (by simp) hrepU
      simp only [List.length_nil, Nat.zero_add] at hlenU; omega
    obtain ⟨ext_5d_6, _, _, _, _, _, fds, norm, ri, rm, ret, htup,
        hfds, hri, hrm, -, hnorm, -, -, -, hev_wfc⟩ :=
      walk_fields_classify_nil_spec hinj hA hD hI hC hM (by omega) evwfc'
        (bnd fun c hc' => by rw [hc]; simp [hc']) (sub fun c hc' => by rw [hc]; simp [hc'])
        (hafter.mono ext5_d) hafterIn (flatList_mono ext0_5d hes) hnil1 hnil2 hnil3 hnil4
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
    obtain ⟨rfl, rfl, rfl, -, rfl⟩ := htup
    have ⟨f_wfc, hf_wfc⟩ := hev_wfc
    obtain ⟨hnorm_len, hrm_len, hri_lt, hrm_lt⟩ :=
      fieldsClassify_lengths_and_bounds after 0 fds norm ri rm ret (hf_wfc f_wfc (Nat.le_refl _))
    simp only [Nat.zero_add] at hri_lt
    obtain ⟨rfl, hm7⟩ := kexpr_length_spec evlen hfds
    subst m7
    have hfds_lt : fds.length < 2 ^ 39 :=
      repList_length_lt_obs hbd hsub evlen (by rw [hc]; simp) (by simp) hfds
    have hnf_eq : fds.length = nFields :=
      natCast_inj_small (by omega) (by omega) (Value.field.inj heqnf)
    have htot_ge : 1 ≤ nP + nMot + nMin + nFields := by omega
    obtain rfl := binop_sub_one_nat htot_ge op_m1
    obtain rfl := binop_add_nat op_m2
    obtain rfl := binop_add_nat op_m3
    obtain rfl := binop_sub_nat (by omega) op_m4
    have ext68 : Heap.Extends m6 m8 := by rw [hm8]; exact Heap.Extends.snoc _ _
    have hbm : TmOExact (Core.keyOf t) m8
        (.bvar (nP + nMot + nMin + nFields - 1 - (nP + nMot + minorIdx)))
        (.ptr (.enum kexprEnum) m6.length) := by
      rw [hm8]; exact tmOExact_bvar_cell (by omega)
    have hhead := build_apply_field_bvars_spec (by omega) (Nat.le_refl _) evfb hbm
    have ext69 := ext68.trans evfb.heap_extends
    have ext09 := ext0_5d.trans (ext_5d_6.trans ext69)
    have evih' : ObsFn W "KernelCheck::apply_ihs_full"
        [vhead, xri, xrm, xnorm, xpeers, xfop, .field (nP : F), .field (nMot : F),
          .field (nMin : F), .field (nFields : F), xrlvls, .field ((0 : Nat) : F), xelim]
        m9 r h' cs9 := by simpa using evih
    have hri_len_lt : ri.length < 2 ^ 39 :=
      repList_length_lt_obs hbd hsub evih' (by rw [hc]; simp) (by simp) (fieldList_mono ext69 hri)
    obtain ⟨B, hB, hBtm⟩ := apply_ihs_full_spec (t := t) (E₀ := E₀)
      (by omega) (by omega) hfop_lt_b (by omega) hpeers_len hfop56
      (fun m hm => by rw [hfop_len]; exact hrm_lt m hm)
      ri 0 (by omega) (fun fi hfi => by have := (hri_lt fi hfi).2; omega)
      (bnd fun c hc' => by rw [hc]; simp [hc']) hhead
      (fieldList_mono ext69 hri) (fieldList_mono ext69 hrm) (tmOExactList_mono ext69 hnorm)
      (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) ext09 hpeers)
      (fieldList_mono ext09 hfop) (hrlvls.mono ext09) (helim.mono ext09) evih'
    refine ⟨B, (hev_peel.and hev_wfc).mono fun f ⟨hpf, hwfcf⟩ => ?_, hBtm⟩
    simp only [ruleBody, hraw_peel, hpf, hwfcf, hnf_eq, ↓reduceIte, hB]

/-- **`KernelCheck::populate_rules`** refines `ruleBodies (ReconView.ofStore t E₀)` at
`Eventually` on `TmOExact`. -/
theorem populate_rules_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    (hM : ModeledAnswers rootCalls (Held R) (ReconView.ofStore t E₀))
    {es : List FlatEntry} {fop : List Nat} {peers : List Bytes.Address}
    {ba : Bytes.Address} {numCtors selfOff idx nP nMot nMin : Nat}
    {us recLvls : List KLevel} {aux : Bool} {sp : List KExpr} {elim : KLevel}
    {xrc xblk xus xrlvls xflat xpeers xfop xsp xelim : SourceValue F}
    (hnc : numCtors < 72057594037927936) (hidx : idx < 72057594037927936)
    (hnP : nP < 72057594037927936) (hnMot : nMot < 72057594037927936)
    (hnMin : nMin < 72057594037927936) (hoff_le : selfOff + numCtors ≤ nMin)
    (hfop_len : fop.length = es.length) (hfop_lt_b : fop.length < 4611686018427387904)
    (hpeers_len : peers.length = fop.length)
    (hfop56 : ∀ n ∈ fop, n < 72057594037927936)
    (hSblk : Held R (ixAddr ba)) :
    ∀ (rem c : Nat), c + rem = numCtors →
      ∀ {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        (∀ cl ∈ cs, cl ∈ rootCalls) →
        Bytes.RepAddressRef addrTy h ba xblk →
        RepKLevelList h us xus → RepKLevelList h recLvls xrlvls →
        RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h es xflat →
        RepList addrListEnum (Bytes.RepAddressRef addrTy) h peers xpeers →
        RepList fieldListEnum RepNatField h fop xfop →
        RepList kexprListEnum (TmOExact (Core.keyOf t)) h sp xsp →
        (∀ e ∈ sp, AddrIn (Held R) (Core.keyOf t) e) →
        RepKLevel h elim xelim →
        ObsFn W "KernelCheck::populate_rules"
          [xrc, .field (numCtors : F), .field (selfOff : F), xblk, .field (idx : F),
            .field (nP : F), .field (nMot : F), .field (nMin : F), xus, xrlvls, xflat, xpeers,
            xfop, auxVal aux, xsp, .field (c : F), xelim] h r h' cs →
        ∃ bodies : List KExpr,
          Eventually (fun f => ruleBodies (ReconView.ofStore t E₀) f es fop (peers.map ixAddr)
            nP nMot nMin us recLvls aux sp elim (ixAddr ba) idx selfOff
            ((List.range numCtors).drop c) = some bodies) ∧
          RepList kexprListEnum (TmOExact (Core.keyOf t)) h' bodies r := by
  intro rem
  induction rem with
  | zero =>
    intro c hc r h h' cs _ _ _ _ _ _ _ _ _ _ ev
    match Obs.«KernelCheck::populate_rules».obs ev with
    | .n0 (he28 := hr0) (hm27 := hm0) .. =>
      cases hr0; cases hm0
      have hdrop : (List.range numCtors).drop c = [] :=
        List.drop_eq_nil_of_le (by rw [List.length_range]; omega)
      rw [hdrop]
      exact ⟨[], Eventually.always fun _ => rfl, Lib.rep_store_nil h⟩
    | .other_Ctor (op17 := op) (hne33 := hne) .. | .other_other (op17 := op) (hne33 := hne) .. =>
      have : c = numCtors := by omega
      subst this; simp only [evalBinOp, sub_self, Except.ok.injEq] at op
      exact (hne op.symm).elim
  | succ rem ih =>
    intro c hc r h h' cs hsub rba hus hrlvls hes hpeers hfop hsp hspIn helim ev
    have sub : ∀ {cs' : List (Call F)}, (∀ cl ∈ cs', cl ∈ cs) → ∀ cl ∈ cs', cl ∈ rootCalls :=
      fun hs cl hcl' => hsub cl (hs cl hcl')
    match Obs.«KernelCheck::populate_rules».obs ev with
    | .n0 (op17 := op) .. =>
      have := binop_sub_eq_zero_nat (by omega) (by omega) op; omega
    | .other_other (m38 := m1) (p45 := pci) (cs51 := cs1)
        (ev53 := evct) (ld47 := ldct) (hne466 := hne) (hc478 := hcs) .. =>
      obtain ⟨_, _, _, _, _, _, _, _, _, hshape, -⟩ := ctorLoad_ofStore ht hwf hS hbd hRsub hcl hlv
        (by omega) (by omega) (sub fun cl hcl' => by rw [hcs]; simp [hcl']) hSblk rba evct ldct
      exact (hne _ rfl hshape).elim
    | .other_Ctor (m38 := m1) (p45 := pci) (cs51 := cs1) (x_ctor_ty := xcty) (x_np := xnp)
        (v140 := vminIdx) (v158 := vrhs) (m159 := m2) (cs169 := cs2) (v301 := vrest) (m310 := m3)
        (cs318 := cs3) (v336 := vc1)
        (ev53 := evct) (ld47 := ldct) (op155 := op_off) (ev171 := evrhs)
        (he296 := hr0) (hm295 := hm0) (op456 := op1) (ev320 := evrec) (hc465 := hcs) .. =>
      cases hr0; cases hm0
      obtain ⟨cty, _, np, _, tyPtr, _, _, _, _, hshape, hctorAt, -, -, hnp56, -, hcty, hctyIn, -, -⟩ :=
        ctorLoad_ofStore ht hwf hS hbd hRsub hcl hlv (by omega) (by omega)
          (sub fun cl hcl' => by rw [hcs]; simp [hcl']) hSblk rba evct ldct
      injection hshape with _ _ hl
      injection hl with _ hl; injection hl with h1 hl; injection hl with _ hl
      injection hl with _ hl; injection hl with _ hl; injection hl with h2 _
      subst h1 h2
      obtain rfl := binop_add_nat op_off
      obtain ⟨B, hevB, hB⟩ := build_rule_rhs_spec ht hwf hS hH hbd hRsub hcl hlv hM
        hnP hnMot hnMin hnp56 (by omega) hfop_len hfop_lt_b hpeers_len hfop56
        (sub fun cl hcl' => by rw [hcs]; simp [hcl']) hcty hctyIn
        (hus.mono evct.heap_extends) (hrlvls.mono evct.heap_extends)
        (flatList_mono evct.heap_extends hes)
        (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) evct.heap_extends hpeers)
        (fieldList_mono evct.heap_extends hfop) (tmOExactList_mono evct.heap_extends hsp) hspIn
        (helim.mono evct.heap_extends) evrhs
      obtain rfl := binop_add_one_nat op1
      have ext02 := evct.heap_extends.trans evrhs.heap_extends
      obtain ⟨bodies, hev_bs, hrep_bs⟩ := ih (c + 1) (by omega)
        (sub fun cl hcl' => by rw [hcs]; simp [hcl'])
        (Bytes.repAddressRef_heapMono₂ addrTy ext02 rba) (hus.mono ext02) (hrlvls.mono ext02)
        (flatList_mono ext02 hes)
        (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) ext02 hpeers)
        (fieldList_mono ext02 hfop) (tmOExactList_mono ext02 hsp) hspIn (helim.mono ext02) evrec
      have hdrop : (List.range numCtors).drop c = c :: (List.range numCtors).drop (c + 1) := by
        have hlt : c < (List.range numCtors).length := by simp; omega
        rw [List.drop_eq_getElem_cons hlt]; simp
      refine ⟨B :: bodies, (hevB.and hev_bs).mono fun f ⟨hfB, hfbs⟩ => ?_,
        Lib.rep_store_cons tmOExact_heapMono₂ (hB.mono evrec.heap_extends) hrep_bs⟩
      rw [hdrop]
      simp only [ruleBodies]
      rw [show (ReconView.ofStore t E₀).ctor (ixAddr ba) idx c = some (cty, np) from hctorAt]
      dsimp only
      rw [hfB, hfbs]
      rfl

end IxVM.Refinement.Binding.FamilyRecon
