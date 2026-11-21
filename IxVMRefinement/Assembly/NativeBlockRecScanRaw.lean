import IxVMRefinement.Iota.Scan
import IxVMRefinement.Core.AllSteps
import IxVMRefinement.Decl.NativeFront
import IxC.Kernel.Verify.Inductives.FixInv
import IxC.Kernel.Verify.InstLevels
import IxC.Kernel.Verify.Subst

/-! # The runs of the circuit's `struct_is_rec` scans, read directly

The raw part of `NativeBlockRecScan.lean`, importable without the native block step:
`rs_addr_in`, `rs_mentions`, `rs_scan_fields` (the mention scans by their own induction, at any
keying), `rs_scan_ctors`, `rs_scan_members`, `rs_is_rec` (the runs, exposing each constructor
slot's `Ingress::get_ci_cprj` observation), `tm_mentions_false`, `tm_fieldsClean_doms` (a clean
heap term's image). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core.Specs.Whnf
  (HeapClean ForallChain NotForallNode ChainEnd FieldsClean)

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

/-! ## The mention scans, without the registry -/

/-- `se_addr_in` by its own induction. -/
theorem rs_addr_in (N : Nat) :
    ∀ {ap xs r : SourceValue F} {h h' : Heap F} {calls : List (Call F)} {a : Bytes.Address}
      {ms : List Bytes.Address},
      calls.length < N → ObsFn W "KernelWhnf::se_addr_in" [ap, xs] h r h' calls →
      RepAddr h a ap → RepList addrListEnum RepAddr h ms xs →
      r = .field (if a ∈ ms then 1 else 0) ∧ h' = h := by
  induction N with
  | zero => intro _ _ _ _ _ _ _ _ hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ N ihN =>
    intro ap xs r h h' calls a ms hlt ev ha hms
    rcases Obs.«KernelWhnf::se_addr_in».obs ev with
      ⟨ld12, he20, he21, hc22⟩ |
      ⟨x_x, x_rest, m41, cs52, ld12, ev54, he75, he76, hc77⟩ |
      ⟨x_x, x_rest, v40, m41, cs52, cs85, ld12, ev54, hne78, ev87, hc104⟩
    · obtain rfl := RepList.nil_of_load hms ld12
      exact ⟨by simp [he20], he21⟩
    · obtain ⟨b, ms', rfl, hb, -⟩ := RepList.cons_of_load hms ld12
      obtain ⟨hr1, rfl⟩ := Lib.address_eq_spec ev54 ha hb
      have hab : a = b := by
        by_contra hne
        rw [ite_eq_right hne] at hr1
        exact NatAux.field_one_ne_zero hr1
      subst hab
      exact ⟨by simp [he75], he76⟩
    · obtain ⟨b, ms', rfl, hb, hms'⟩ := RepList.cons_of_load hms ld12
      obtain ⟨hr1, rfl⟩ := Lib.address_eq_spec ev54 ha hb
      have hab : a ≠ b := by
        intro e
        rw [ite_eq_left e] at hr1
        exact hne78 hr1
      subst hc104
      obtain ⟨hr, hh⟩ := ihN (by simp only [List.length_cons, List.length_append] at hlt; omega)
        ev87 ha hms'
      refine ⟨?_, hh⟩
      rw [hr]
      simp [hab]

/-- `se_mentions` by its own induction, at any context's keying. -/
theorem rs_mentions (c : ScopedCtx) (N : Nat) :
    ∀ {e xs r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
      {ms : List Bytes.Address} {d : Nat} {Γ : Nat → KExpr} {k : Nat} {E : KExpr},
      calls.length < N → ObsFn W "KernelWhnf::se_mentions" [e, xs] h r h' calls →
      RepList addrListEnum RepAddr h ms xs → c.tmk d Γ k h E e → r ≠ .field 1 →
      HeapClean (· ∈ ms) h e := by
  induction N with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ N ihN =>
    intro e xs r h h' calls ms d Γ k E hlt ev hms hE hr
    rcases Obs.«KernelWhnf::se_mentions».obs ev with
      ⟨x_a, w20, cs34, ld12, ev36, hc53⟩ |
      ⟨x_f, x_x, m72, cs83, ld12, ev85, he106, he107, hc108⟩ |
      ⟨x_f, x_x, v71, m72, cs83, cs116, ld12, ev85, hne109, ev118, hc135⟩ |
      ⟨x_t, x_b, w143, m160, cs171, ld12, ev173, he194, he195, hc196⟩ |
      ⟨x_t, x_b, w143, v159, m160, cs171, cs204, ld12, ev173, hne197, ev206, hc223⟩ |
      ⟨x_t, x_b, w231, m248, cs259, ld12, ev261, he282, he283, hc284⟩ |
      ⟨x_t, x_b, w231, v247, m248, cs259, cs292, ld12, ev261, hne285, ev294, hc311⟩ |
      ⟨x_t, x_v, x_b, m335, cs346, ld12, ev348, he369, he370, hc371⟩ |
      ⟨x_t, x_v, x_b, v334, m335, cs346, m377, cs388, ld12, ev348, hne372, ev390, he411, he412,
        hc413⟩ |
      ⟨x_t, x_v, x_b, v334, m335, cs346, v376, m377, cs388, cs421, ld12, ev348, hne372, ev390,
        hne414, ev423, hc440⟩ |
      ⟨w448, w449, x_inner, cs468, ld12, ev470, hc487⟩ |
      ⟨v1, ld12, hne54, hne136, hne224, hne312, hne441, hne488, he492, he493, hc494⟩
    · obtain ⟨a, us, rfl, ha, -⟩ := hE.const_of_load ld12
      subst hc53
      obtain ⟨hr', -⟩ := rs_addr_in (cs34.length + 1) (Nat.lt_succ_self _) ev36 ha hms
      refine .const ld12 ha ?_
      intro hm
      have hm' : a ∈ ms := hm
      apply hr
      rw [hr']
      simp [hm']
    · exact absurd he106 hr
    · obtain ⟨Ef, Ea, rfl, hf, hx⟩ := hE.app_of_load ld12
      subst hc135
      have ext := ObsFn.heap_extends ev85
      have c1 := ihN (by simp only [List.length_cons, List.length_append] at hlt; omega)
        ev85 hms hf hne109
      have c2 := ihN (by simp only [List.length_cons, List.length_append] at hlt; omega)
        ev118 (se_addrs_mono ext hms) (Tm.mono ext hx) hr
      exact .app ld12 c1 (heapClean_of_extends ext hx c2)
    · exact absurd he194 hr
    · obtain ⟨T, B, ℓ, rfl, ht, hb, -⟩ := hE.lam_of_load ld12
      subst hc223
      have ext := ObsFn.heap_extends ev173
      have c1 := ihN (by simp only [List.length_cons, List.length_append] at hlt; omega)
        ev173 hms ht hne197
      have c2 := ihN (by simp only [List.length_cons, List.length_append] at hlt; omega)
        ev206 (se_addrs_mono ext hms) (Tm.mono ext hb) hr
      exact .lam ld12 c1 (heapClean_of_extends ext hb c2)
    · exact absurd he282 hr
    · obtain ⟨T, B, ℓ, rfl, ht, hb, -⟩ := hE.forallE_of_load ld12
      subst hc311
      have ext := ObsFn.heap_extends ev261
      have c1 := ihN (by simp only [List.length_cons, List.length_append] at hlt; omega)
        ev261 hms ht hne285
      have c2 := ihN (by simp only [List.length_cons, List.length_append] at hlt; omega)
        ev294 (se_addrs_mono ext hms) (Tm.mono ext hb) hr
      exact .forallE ld12 c1 (heapClean_of_extends ext hb c2)
    · exact absurd he369 hr
    · exact absurd he411 hr
    · obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := hE.letE_of_load ld12
      subst hc440
      have ext1 := ObsFn.heap_extends ev348
      have ext2 := ObsFn.heap_extends ev390
      have c1 := ihN (by simp only [List.length_cons, List.length_append] at hlt; omega)
        ev348 hms ht hne372
      have c2 := ihN (by simp only [List.length_cons, List.length_append] at hlt; omega)
        ev390 (se_addrs_mono ext1 hms) (Tm.mono ext1 hv) hne414
      have c3 := ihN (by simp only [List.length_cons, List.length_append] at hlt; omega)
        ev423 (se_addrs_mono (ext1.trans ext2) hms) (Tm.mono (ext1.trans ext2) hb) hr
      exact .letE ld12 c1 (heapClean_of_extends ext1 hv c2)
        (heapClean_of_extends (ext1.trans ext2) hb c3)
    · obtain ⟨a, i, Es, -, rfl, -, hes⟩ := hE.proj_of_load ld12
      subst hc487
      have c1 := ihN (by simp only [List.length_cons, List.length_append] at hlt; omega)
        ev470 hms hes hr
      exact .proj ld12 c1
    · cases hE with
      | bvarLocal cell _ _ => exact .bvar (loadValue_enum_cell cell)
      | bvarFree cell _ _ _ => exact .bvar (loadValue_enum_cell cell)
      | sort cell _ _ => exact .srt (loadValue_enum_cell cell)
      | litNat cell _ _ => exact .lit (loadValue_enum_cell cell)
      | litStr cell _ _ => exact .lit (loadValue_enum_cell cell)
      | const cell _ _ _ =>
        rw [loadValue_enum_cell cell] at ld12
        injection ld12 with hv
        exact (hne54 _ (by rfl) hv.symm).elim
      | app cell _ _ =>
        rw [loadValue_enum_cell cell] at ld12
        injection ld12 with hv
        exact (hne136 _ (by rfl) hv.symm).elim
      | lam cell _ _ _ =>
        rw [loadValue_enum_cell cell] at ld12
        injection ld12 with hv
        exact (hne224 _ (by rfl) hv.symm).elim
      | forallE cell _ _ _ =>
        rw [loadValue_enum_cell cell] at ld12
        injection ld12 with hv
        exact (hne312 _ (by rfl) hv.symm).elim
      | letE cell _ _ _ =>
        rw [loadValue_enum_cell cell] at ld12
        injection ld12 with hv
        exact (hne441 _ (by rfl) hv.symm).elim
      | proj cell _ _ =>
        rw [loadValue_enum_cell cell] at ld12
        injection ld12 with hv
        exact (hne488 _ (by rfl) hv.symm).elim

/-- `se_scan_fields` by its own induction, at any context's keying. -/
theorem rs_scan_fields (c : ScopedCtx) (N : Nat) :
    ∀ {ty xs r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
      {ms : List Bytes.Address} {d : Nat} {Γ : Nat → KExpr} {k : Nat} {T : KExpr},
      calls.length < N → ObsFn W "KernelWhnf::se_scan_fields" [ty, xs] h r h' calls →
      RepList addrListEnum RepAddr h ms xs → c.tmk d Γ k h T ty → r ≠ .field 1 →
      ∃ ds q, ForallChain h ty ds q ∧ ChainEnd h q ∧ ∀ dp ∈ ds, HeapClean (· ∈ ms) h dp := by
  induction N with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ N ihN =>
    intro ty xs r h h' calls ms d Γ k T hlt ev hms hT hr
    rcases Obs.«KernelWhnf::se_scan_fields».obs ev with
      ⟨x_dom, x_body, w20, m37, cs48, ld12, ev50, he71, he72, hc73⟩ |
      ⟨x_dom, x_body, w20, v36, m37, cs48, cs81, ld12, ev50, hne74, ev83, hc100⟩ |
      ⟨w108, w109, w110, ld12, he126, he127, hc128⟩ |
      ⟨v1, ld12, hne101, hne129, he133, he134, hc135⟩
    · exact absurd he71 hr
    · subst hc100
      obtain ⟨T0, B, ℓ, rfl, hT0, hB, -⟩ := hT.forallE_of_load ld12
      have hdom := rs_mentions c (cs48.length + 1) (Nat.lt_succ_self _) ev50 hms hT0 hne74
      have e1 := ObsFn.heap_extends ev50
      obtain ⟨ds, q, hch37, hq37, hcl37⟩ :=
        ihN (by simp only [List.length_cons, List.length_append] at hlt; omega) ev83
          (se_addrs_mono e1 hms) (Tm.mono e1 hB) hr
      obtain ⟨hch, hq, hcl⟩ := forallChain_of_extends e1 hch37 hq37 hcl37 hB
      refine ⟨x_dom :: ds, q, .cons ld12 hch, hq, fun dp hdp => ?_⟩
      rcases List.mem_cons.mp hdp with rfl | hdp
      · exact hdom
      · exact hcl dp hdp
    · exact absurd he126 hr
    · refine ⟨[], ty, .nil, ?_, fun dp hdp => (List.not_mem_nil hdp).elim⟩
      cases hT with
      | forallE cell _ _ _ =>
        rw [loadValue_enum_cell cell] at ld12
        injection ld12 with hv
        exact (hne101 _ (by rfl) hv.symm).elim
      | letE cell _ _ _ =>
        rw [loadValue_enum_cell cell] at ld12
        injection ld12 with hv
        exact (hne129 _ (by rfl) hv.symm).elim
      | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
      | app cell _ _ | lam cell _ _ _ | litNat cell _ _ | litStr cell _ _
      | proj cell _ _ =>
        exact ⟨_, _, loadValue_enum_cell cell, by decide, by decide⟩

/-! ## The scans' runs, with each constructor load exposed -/

/-- **`struct_scan_ctors` read slot by slot**: an answer other than `1` means every slot
`j + t < n` was loaded by an observed `Ingress::get_ci_cprj` (its calls among the scan's), and the
loaded type, wherever represented, has clean fields after `p` binders at the scan's final heap. -/
theorem rs_scan_ctors (c : ScopedCtx) (K : Nat) :
    ∀ {blk xs r : SourceValue F} {i n p j : F} {h h' : Heap F} {calls : List (Call F)}
      {ms : List Bytes.Address},
      ZMod.val (n - j) = K →
      ObsFn W "KernelWhnf::struct_scan_ctors" [blk, .field i, .field n, .field p, xs, .field j]
        h r h' calls →
      RepList addrListEnum RepAddr h ms xs → r ≠ .field 1 →
      ∀ t < K, ∃ (h1 h2 : Heap F) (ptr : SourceValue F) (cs1 : List (Call F))
        (nl ty : SourceValue F) (rest : List (SourceValue F)),
        Heap.Extends h h1 ∧ Heap.Extends h2 h' ∧
        ObsFn W "Ingress::get_ci_cprj" [blk, .field i, .field (j + (t : F))] h1 ptr h2 cs1 ∧
        (∀ x ∈ cs1, x ∈ calls) ∧
        loadValue h2 ptr = .ok (.construct kciEnum "Ctor" (nl :: ty :: rest)) ∧
        ((∃ d Γ k T, c.tmk d Γ k h2 T ty) → FieldsClean h' (ZMod.val p) ms ty) := by
  induction K with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t ht; exact absurd ht (Nat.not_lt_zero _)
  | succ K ihK =>
    intro blk xs r i n p j h h' calls ms hK ev hms hr
    rcases Obs.«KernelWhnf::struct_scan_ctors».obs ev with
      ⟨op17, he24, he25, hc26⟩ |
      ⟨v1, m32, p39, cs45, w88, x_cty, w89, w90, w91, w92, w93, w94, v135, m136, cs146, m166,
        cs177, op17, hne27, ev47, ld41, ev148, ev179, he200, he201, hc202⟩ |
      ⟨v1, m32, p39, cs45, w88, x_cty, w89, w90, w91, w92, w93, w94, v135, m136, cs146, v165,
        m166, cs177, cs210, v218, op17, hne27, ev47, ld41, ev148, ev179, hne203, op267, ev212,
        hc269⟩ |
      ⟨v1, v31, m32, p39, cs45, op17, hne27, ev47, ld41, hne270, he274, he275, hc276⟩
    · have h0 : n - j = 0 := (NatAux.field_inj (NatAux.sub_ok op17)).symm
      rw [h0, ZMod.val_zero] at hK
      exact absurd hK (Nat.succ_ne_zero K).symm
    · exact absurd he200 hr
    · have hv := NatAux.sub_ok op17
      subst hv
      have hnj : n - j ≠ 0 := fun e => hne27 (by rw [e])
      have hv2 := NatAux.add_ok op267
      subst hv2 hc269
      have e1 := ObsFn.heap_extends ev47
      have e1' := ObsFn.heap_extends ev148
      have e2 := ObsFn.heap_extends ev179
      have e3 := ObsFn.heap_extends ev212
      have hK' : ZMod.val (n - (j + 1)) = K := by
        have hs := Lib.val_sub_one hnj
        rw [show n - (j + 1) = n - j - 1 by ring]
        omega
      have hrec := ihK hK' ev212 (se_addrs_mono (e1.trans (e1'.trans e2)) hms) hr
      intro t ht
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · refine ⟨h, m32, p39, cs45, w88, x_cty, [w89, w90, w91, w92, w93, w94], Heap.Extends.refl _,
          e1'.trans (e2.trans e3), ?_, fun x hx => by simp [hx], ld41, ?_⟩
        · simpa using ev47
        · rintro ⟨d, Γ, k, T, hT⟩
          obtain ⟨rfl, ds1, hch1, hle1, -⟩ := se_peel_tol_aux c (cs146.length + 1)
            (Nat.lt_succ_self _) ev148 p rfl d Γ k T hT
          obtain ⟨E1, hE1⟩ := tm_forallChain hch1 hT
          obtain ⟨ds2, q, hch2, hq, hcl⟩ := rs_scan_fields c (cs177.length + 1)
            (Nat.lt_succ_self _) ev179 (se_addrs_mono e1 hms) hE1 hne203
          refine ⟨ds1 ++ ds2, q, forallChain_mono (e2.trans e3) (forallChain_append hch1 hch2),
            chainEnd_mono (e2.trans e3) hq, ?_⟩
          intro dp hdp
          exact heapClean_mono (e2.trans e3) (hcl dp (se_mem_drop_append hle1 hdp))
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        obtain ⟨h1, h2, ptr, cs1, nl, ty, rest, eh1, eh2, evc, hsub, ldc, hfc⟩ :=
          hrec t' (by omega)
        refine ⟨h1, h2, ptr, cs1, nl, ty, rest, (e1.trans (e1'.trans e2)).trans eh1, eh2, ?_,
          fun x hx => by simp [hsub x hx], ldc, hfc⟩
        have e : j + ((t' + 1 : Nat) : F) = j + 1 + (t' : F) := by push_cast; ring
        rw [e]
        exact evc
    · exact absurd he274 hr

/-- **`struct_scan_members` read member by member**: an answer other than `1` means every
listed member was loaded by an observed `Ingress::get_ci`, and where the loaded value is an
inductive, its constructors were scanned (`struct_scan_ctors`, answer other than `1`). -/
theorem rs_scan_members (N : Nat) :
    ∀ {msp xs r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
      {ms membs : List Bytes.Address},
      calls.length < N →
      ObsFn W "KernelWhnf::struct_scan_members" [msp, xs] h r h' calls →
      RepList addrListEnum RepAddr h ms msp → RepList addrListEnum RepAddr h membs xs →
      r ≠ .field 1 →
      ∀ m ∈ ms, ∃ (xm ptr : SourceValue F) (h1 h2 : Heap F) (cs1 : List (Call F))
        (v : SourceValue F),
        Heap.Extends h h1 ∧ RepAddr h1 m xm ∧
        ObsFn W "Ingress::get_ci" [xm] h1 ptr h2 cs1 ∧ (∀ x ∈ cs1, x ∈ calls) ∧
        loadValue h2 ptr = .ok v ∧
        ∀ (w72 w73 np w74 nc w75 blk idx : SourceValue F),
          v = .construct kciEnum "Induct" [w72, w73, np, w74, nc, w75, blk, idx] →
          ∃ (rr : SourceValue F) (h3 : Heap F) (cs3 : List (Call F)),
            ObsFn W "KernelWhnf::struct_scan_ctors" [blk, idx, nc, np, xs, .field 0] h2 rr h3 cs3 ∧
            (∀ x ∈ cs3, x ∈ calls) ∧ rr ≠ .field 1 ∧ Heap.Extends h3 h' ∧
            RepList addrListEnum RepAddr h2 membs xs := by
  induction N with
  | zero => intro _ _ _ _ _ _ _ _ hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ N ihN =>
    intro msp xs r h h' calls ms membs hlt ev hms hmembs hr
    rcases Obs.«KernelWhnf::struct_scan_members».obs ev with
      ⟨ld12, he20, he21, hc22⟩ |
      ⟨x_m, x_rest, m41, p49, cs55, w72, w73, x_n_params, w74, x_num_ctors, w75, x_block, x_idx,
        m117, cs128, ld12, ev57, ld51, ev130, he182, he183, hc184⟩ |
      ⟨x_m, x_rest, m41, p49, cs55, w72, w73, x_n_params, w74, x_num_ctors, w75, x_block, x_idx,
        v116, m117, cs128, cs192, ld12, ev57, ld51, ev130, hne185, ev194, hc211⟩ |
      ⟨x_m, x_rest, v40, m41, p49, cs55, cs219, ld12, ev57, ld51, hne212, ev221, hc238⟩
    · obtain rfl := RepList.nil_of_load hms ld12
      intro m hm
      simp at hm
    · exact absurd he182 hr
    · obtain ⟨a, ms', rfl, ha, hms'⟩ := RepList.cons_of_load hms ld12
      subst hc211
      have e1 := ObsFn.heap_extends ev57
      have e2 := ObsFn.heap_extends ev130
      have e3 := ObsFn.heap_extends ev194
      have hrest := ihN (by simp only [List.length_cons, List.length_append] at hlt; omega)
        ev194 (se_addrs_mono (e1.trans e2) hms') (se_addrs_mono (e1.trans e2) hmembs) hr
      intro m hm
      rcases List.mem_cons.mp hm with rfl | hm'
      · refine ⟨x_m, p49, h, m41, cs55, _, Heap.Extends.refl _, ha, ev57,
          fun x hx => by simp [hx], ld51, ?_⟩
        intro a72 a73 anp a74 anc a75 ablk aidx hv
        injection hv with _ _ hv
        simp only [List.cons.injEq, and_true] at hv
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv
        exact ⟨v116, m117, cs128, ev130, fun x hx => by simp [hx], hne185, e3,
          se_addrs_mono e1 hmembs⟩
      · obtain ⟨xm, ptr, h1, h2, cs1, v, eh, hrep, evg, hsub, ldv, hscan⟩ := hrest m hm'
        refine ⟨xm, ptr, h1, h2, cs1, v, (e1.trans e2).trans eh, hrep, evg,
          fun x hx => by simp [hsub x hx], ldv, ?_⟩
        intro a72 a73 anp a74 anc a75 ablk aidx hv
        obtain ⟨rr, h3, cs3, evs, hsub3, hrr, e33, hmb⟩ := hscan a72 a73 anp a74 anc a75 ablk aidx hv
        exact ⟨rr, h3, cs3, evs, fun x hx => by simp [hsub3 x hx], hrr, e33, hmb⟩
    · obtain ⟨a, ms', rfl, ha, hms'⟩ := RepList.cons_of_load hms ld12
      subst hc238
      have e1 := ObsFn.heap_extends ev57
      have hrest := ihN (by simp only [List.length_cons, List.length_append] at hlt; omega)
        ev221 (se_addrs_mono e1 hms') (se_addrs_mono e1 hmembs) hr
      intro m hm
      rcases List.mem_cons.mp hm with rfl | hm'
      · refine ⟨x_m, p49, h, m41, cs55, v40, Heap.Extends.refl _, ha, ev57,
          fun x hx => by simp [hx], ld51, ?_⟩
        intro a72 a73 anp a74 anc a75 ablk aidx hv
        exact (hne212 _ (by rfl) hv).elim
      · obtain ⟨xm, ptr, h1, h2, cs1, v, eh, hrep, evg, hsub, ldv, hscan⟩ := hrest m hm'
        refine ⟨xm, ptr, h1, h2, cs1, v, e1.trans eh, hrep, evg,
          fun x hx => by simp [hsub x hx], ldv, ?_⟩
        intro a72 a73 anp a74 anc a75 ablk aidx hv
        obtain ⟨rr, h3, cs3, evs, hsub3, hrr, e33, hmb⟩ := hscan a72 a73 anp a74 anc a75 ablk aidx hv
        exact ⟨rr, h3, cs3, evs, fun x hx => by simp [hsub3 x hx], hrr, e33, hmb⟩

/-- **`struct_is_rec`'s run at an answer other than `1`**: the parent loaded as an inductive, the
block's member list computed, and that list scanned against itself. -/
theorem rs_is_rec {sp r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::struct_is_rec" [sp] h r h' calls) (hr : r ≠ .field 1) :
    ∃ (m2 : Heap F) (p9 : SourceValue F) (cs15 : List (Call F))
      (w42 w43 w44 w45 w46 w47 x_block w48 : SourceValue F) (m90 : Heap F) (v116 : SourceValue F)
      (m117 : Heap F) (cs127 cs149 : List (Call F)),
      ObsFn W "Ingress::get_ci" [sp] h p9 m2 cs15 ∧ (∀ x ∈ cs15, x ∈ calls) ∧
      loadValue m2 p9 =
        .ok (.construct kciEnum "Induct" [w42, w43, w44, w45, w46, w47, x_block, w48]) ∧
      Heap.Extends m2 m90 ∧
      ObsFn W "KernelWhnf::struct_block_member_addrs" [sp, x_block] m90 v116 m117 cs127 ∧
      (∀ x ∈ cs127, x ∈ calls) ∧
      ObsFn W "KernelWhnf::struct_scan_members" [v116, v116] m117 r h' cs149 ∧
      (∀ x ∈ cs149, x ∈ calls) := by
  rcases Obs.«KernelWhnf::struct_is_rec».obs ev with
    ⟨m2, p9, cs15, w42, w43, w44, w45, w46, w47, x_block, w48, m90, cs101, v116, m117, cs127,
      cs149, ev17, ld11, ev103, ev129, ev151, hc168⟩ |
    ⟨m2, p9, cs15, w42, w43, w44, w45, w46, w47, x_block, w48, v89, m90, cs101, ev17, ld11, ev103,
      hne169, he173, he174, hc175⟩ |
    ⟨v1, m2, p9, cs15, ev17, ld11, hne176, he180, he181, hc182⟩
  · subst hc168
    exact ⟨m2, p9, cs15, w42, w43, w44, w45, w46, w47, x_block, w48, m90, v116, m117, cs127, cs149,
      ev17, fun x hx => by simp [hx], ld11, ObsFn.heap_extends ev103, ev129,
      fun x hx => by simp [hx], ev151, fun x hx => by simp [hx]⟩
  · exact absurd he173 hr
  · exact absurd he180 hr

/-! ## A clean heap term's image -/

/-- **A clean heap term mentions no constant at `T`** in its image, where every address keyed `T`
is a member and no projection is permitted at one, and the opened variables' types do not mention
`T`. -/
theorem tm_mentions_false {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {T : KKey} {ms : List Bytes.Address}
    (hΓ : ∀ j, (Γ j).mentionsConst T = false)
    (hc : ∀ a : Bytes.Address, κ (ixAddr a) = T → a ∈ ms)
    (hp : ∀ a : Bytes.Address, κ (ixAddr a) = T → ¬ ProjPermitted κ (ixAddr a)) :
    ∀ {k : Nat} {E : KExpr} {p : SourceValue F}, Tm κ d Γ h k E p →
      HeapClean (· ∈ ms) h p → E.mentionsConst T = false := by
  intro k E p rep
  induction rep with
  | bvarLocal cell _ _ => intro _; rfl
  | bvarFree cell _ _ _ => intro _; exact hΓ _
  | sort cell _ _ => intro _; rfl
  | litNat cell _ _ => intro _; rfl
  | litStr cell _ _ => intro _; rfl
  | @const k addr ap lsp a ls us res cell ra rls hus =>
    intro hcl
    cases hcl with
    | const hl ha hP =>
      obtain ⟨-, hxs⟩ := load_cell cell hl
      injection hxs with e1 _
      subst e1
      have hab := addr_det ra ha
      rw [← hab] at hP
      have hne : κ (ixAddr a) ≠ T := fun heq => hP (hc a heq)
      simp [Ix.Kernel.Expr.mentionsConst, hne]
    | bvar hl | srt hl | lit hl | app hl _ _ | lam hl _ _ | forallE hl _ _ | letE hl _ _ _
    | proj hl _ => exact (load_cell_ne cell hl (by decide)).elim
  | app cell _ _ ihf iha =>
    intro hcl
    cases hcl with
    | app hl hx hy =>
      obtain ⟨-, hxs⟩ := load_cell cell hl
      injection hxs with e1 hrest
      injection hrest with e2
      subst e1 e2
      simp [Ix.Kernel.Expr.mentionsConst, ihf hx, iha hy]
    | bvar hl | srt hl | lit hl | const hl _ _ | lam hl _ _ | forallE hl _ _ | letE hl _ _ _
    | proj hl _ => exact (load_cell_ne cell hl (by decide)).elim
  | lam cell _ _ _ iht ihb =>
    intro hcl
    cases hcl with
    | lam hl hx hy =>
      obtain ⟨-, hxs⟩ := load_cell cell hl
      injection hxs with e1 hrest
      injection hrest with e2 _
      subst e1 e2
      simp [Ix.Kernel.Expr.mentionsConst, iht hx, ihb hy]
    | bvar hl | srt hl | lit hl | const hl _ _ | app hl _ _ | forallE hl _ _ | letE hl _ _ _
    | proj hl _ => exact (load_cell_ne cell hl (by decide)).elim
  | forallE cell _ _ _ iht ihb =>
    intro hcl
    cases hcl with
    | forallE hl hx hy =>
      obtain ⟨-, hxs⟩ := load_cell cell hl
      injection hxs with e1 hrest
      injection hrest with e2 _
      subst e1 e2
      simp [Ix.Kernel.Expr.mentionsConst, iht hx, ihb hy]
    | bvar hl | srt hl | lit hl | const hl _ _ | app hl _ _ | lam hl _ _ | letE hl _ _ _
    | proj hl _ => exact (load_cell_ne cell hl (by decide)).elim
  | letE cell _ _ _ iht ihv ihb =>
    intro hcl
    cases hcl with
    | letE hl hx hy hz =>
      obtain ⟨-, hxs⟩ := load_cell cell hl
      injection hxs with e1 hrest
      injection hrest with e2 hrest'
      injection hrest' with e3
      subst e1 e2 e3
      exact Decl.mentionsConst_instantiate1Lift_false (ihb hz) (fun _ => ihv hy)
    | bvar hl | srt hl | lit hl | const hl _ _ | app hl _ _ | lam hl _ _ | forallE hl _ _
    | proj hl _ => exact (load_cell_ne cell hl (by decide)).elim
  | @proj k addr ap ep a i E' res perm cell ra re ihe =>
    intro hcl
    cases hcl with
    | proj hl he =>
      obtain ⟨-, hxs⟩ := load_cell cell hl
      injection hxs with _ hrest
      injection hrest with _ hrest'
      injection hrest' with e3
      subst e3
      have hne : κ (ixAddr a) ≠ T := fun heq => hp a heq perm
      simp [Ix.Kernel.Expr.mentionsConst, ihe he, hne]
    | bvar hl | srt hl | lit hl | const hl _ _ | app hl _ _ | lam hl _ _ | forallE hl _ _
    | letE hl _ _ _ => exact (load_cell_ne cell hl (by decide)).elim

/-- **The domains of a clean chain, in the image**: along a maximal `∀` chain of a represented
term whose domains from index `m` on are clean, the image's binder domains from `m` on mention no
constant at `T`. -/
theorem tm_fieldsClean_doms {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {T : KKey} {ms : List Bytes.Address}
    (hΓ : ∀ j, (Γ j).mentionsConst T = false)
    (hc : ∀ a : Bytes.Address, κ (ixAddr a) = T → a ∈ ms)
    (hp : ∀ a : Bytes.Address, κ (ixAddr a) = T → ¬ ProjPermitted κ (ixAddr a))
    {p q : SourceValue F} {ds : List (SourceValue F)} (fc : ForallChain h p ds q) :
    ChainEnd h q → ∀ (m : Nat), (∀ dp ∈ ds.drop m, HeapClean (· ∈ ms) h dp) →
      ∀ {k : Nat} {E : KExpr}, Tm κ d Γ h k E p →
      ∀ (n : Nat) (bs : List (KExpr × Ix.Kernel.BinderMeta)) (body : KExpr),
        E.stripPis n = some (bs, body) →
        ∀ i, m ≤ i → i < n → ((bs.getD i default).1).mentionsConst T = false := by
  induction fc with
  | @nil q' =>
    intro hq m _ k E hE n bs body hs i hmi hin
    exfalso
    obtain ⟨ctor, xs, hl, hne1, hne2⟩ := hq
    cases n with
    | zero => omega
    | succ n' =>
      cases hE with
      | forallE cell _ _ _ => exact hne1 (load_cell cell hl).1.symm
      | letE cell _ _ _ => exact hne2 (load_cell cell hl).1.symm
      | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
      | app cell _ _ | lam cell _ _ _ | litNat cell _ _ | litStr cell _ _ | proj cell _ _ =>
        simp [Ix.Kernel.Expr.stripPis] at hs
  | @cons p' dom cod lvl q' ds' hl _ ih =>
    intro hq m hcl k E hE n bs body hs i hmi hin
    obtain ⟨T0, B, ℓ, rfl, hT0, hB, -⟩ := hE.forallE_of_load hl
    cases n with
    | zero => omega
    | succ n' =>
      cases hb : B.stripPis n' with
      | none => simp [Ix.Kernel.Expr.stripPis, hb] at hs
      | some r =>
        obtain ⟨bs', body'⟩ := r
        simp [Ix.Kernel.Expr.stripPis, hb] at hs
        obtain ⟨rfl, rfl⟩ := hs
        cases i with
        | zero =>
          have hm0 : m = 0 := by omega
          subst hm0
          have hdom : HeapClean (· ∈ ms) h dom := hcl dom (by simp)
          simpa using tm_mentions_false hΓ hc hp hT0 hdom
        | succ i' =>
          have hcl' : ∀ dp ∈ ds'.drop (m - 1), HeapClean (· ∈ ms) h dp := by
            intro dp hdp
            apply hcl dp
            rcases Nat.eq_zero_or_pos m with rfl | hmpos
            · simp only [Nat.zero_sub, List.drop_zero] at hdp
              simp [hdp]
            · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
              simpa using hdp
          have := ih hq (m - 1) hcl' hB n' bs' body' hb i' (by omega) (by omega)
          simpa using this

end IxVM.Refinement.Core
