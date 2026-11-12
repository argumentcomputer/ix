import IxVMRefinement.Nat.Basic

/-! # `KernelKlimbs`: successor, addition, subtraction, comparison, normalization

Step lemmas of the limb functions that do not multiply: each takes the derivation's path, reads
its callees' registered specs from the induction hypothesis and the word specs from the library,
and computes the limbs' value. Carries and borrows are words' bits (`add_words`, `sub_words`),
so the arithmetic is natural arithmetic modulo `2^64` (`omega`). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open NatAux

set_option linter.unusedVariables false

namespace NatAux

/-- `klimbs_succ`'s spec from its content on limb lists. -/
theorem succ_spec_of {h h' : Heap F} {a r : SourceValue F}
    (key : ∀ ls, LRep h ls a → ∃ ls', LRep h' ls' r ∧ limbsVal ls' = limbsVal ls + 1 ∧
      (Canon ls → Canon ls')) (n : Nat) :
    (RepLimbs h n a → RepLimbs h' (n + 1) r) ∧
      (Specs.Nat.RepLimbsC h n a → Specs.Nat.RepLimbsC h' (n + 1) r) := by
  refine ⟨fun ⟨ls, hl, hv⟩ => ?_, fun ⟨ls, hl, hv, hc⟩ => ?_⟩
  · obtain ⟨ls', hl', hv', -⟩ := key ls hl
    exact ⟨ls', hl', by rw [hv', hv]⟩
  · obtain ⟨ls', hl', hv', hc'⟩ := key ls hl
    exact ⟨ls', hl', by rw [hv', hv], hc' hc⟩

end NatAux

/-! ## `klimbs_succ` -/

/-- `klimbs_succ(n)`: `n + 1`, canonical on canonical input. -/
theorem klimbs_succ_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_succ" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_succ c args h r h' calls := by
  intro a hargs good n
  subst hargs
  refine succ_spec_of ?_ n
  intro ls hl
  rcases Obs.«KernelKlimbs::klimbs_succ».obs ev with
    ⟨m95, ld, rfl, rfl, rfl, -⟩ |
    ⟨x_limb, x_rest, m126, cs136, x_sum, x_carry, m239, cs250, ld, ev1, ev2, rfl, rfl, -⟩ |
    ⟨x_limb, x_rest, m126, cs136, x_sum, x_carry, v238, m239, cs250, v303, m312, cs320, ld, ev1,
      ev2, hne, rfl, rfl, ev3, hc⟩
  · -- `Nil`: the list `[1]`
    obtain rfl := lrep_nil_of_load hl ld
    obtain ⟨w1, hw1, hr1⟩ := word_one h
    refine ⟨[w1], lrep_store_cons hr1 (lrep_store_nil h), ?_, fun _ => ?_⟩
    · simp [limbsVal_cons, limbsVal_nil, hw1]
    · exact canon_cons_of_pos canon_nil (by simp [limbsVal_cons, limbsVal_nil, hw1])
  · -- no carry out of the low limb
    obtain ⟨l, ls0, rfl, hl0, hls0⟩ := lrep_cons_of_load hl ld
    obtain ⟨w1, hw1, hr1⟩ := word_one h
    obtain ⟨rfl, rfl, rfl⟩ := add_words hl0 hr1 ev1
    obtain ⟨hcy, rfl⟩ := to_field ev2
    have hlb := toNat_lt l
    have hlt : l.toNat + w1.toNat < B64 := (carry_zero_iff (by omega)).mp (field_inj hcy)
    obtain ⟨w, hw, hr⟩ := word_of h (Nat.mod_lt (l.toNat + w1.toNat) (by decide))
    refine ⟨w :: ls0, lrep_store_cons hr hls0, ?_, fun hcn => ?_⟩
    · rw [limbsVal_cons, limbsVal_cons]; omega
    · exact canon_cons_of_pos (canon_tail hcn) (by rw [limbsVal_cons]; omega)
  · -- a carry: the low limb wraps to `0` and the rest is incremented
    obtain ⟨l, ls0, rfl, hl0, hls0⟩ := lrep_cons_of_load hl ld
    obtain ⟨w1, hw1, hr1⟩ := word_one h
    obtain ⟨rfl, rfl, rfl⟩ := add_words hl0 hr1 ev1
    obtain ⟨rfl, rfl⟩ := to_field ev2
    have hlb := toNat_lt l
    have hge : B64 ≤ l.toNat + w1.toNat := by
      by_contra hlt
      exact hne (by rw [(carry_zero_iff (by omega)).mpr (by omega)])
    subst hc
    have hspec := ih.get (.nat .klimbs_succ) (by nat_lt_calls) ev3 x_rest rfl
      (good.sub fun x hx => by simp [hx]) (limbsVal ls0)
    obtain ⟨w, hw, hr⟩ := word_of h (Nat.mod_lt (l.toNat + w1.toNat) (by decide))
    by_cases hcn : Canon (l :: ls0)
    · obtain ⟨ls1, hls1, hv1, hc1⟩ := hspec.2 ⟨ls0, hls0, rfl, canon_tail hcn⟩
      refine ⟨w :: ls1, lrep_store_cons hr hls1, ?_, fun _ => ?_⟩
      · rw [limbsVal_cons, limbsVal_cons, hv1]; omega
      · exact canon_cons_of_pos hc1 (by rw [limbsVal_cons, hv1]; omega)
    · obtain ⟨ls1, hls1, hv1⟩ := hspec.1 ⟨ls0, hls0, rfl⟩
      exact ⟨w :: ls1, lrep_store_cons hr hls1,
        by rw [limbsVal_cons, limbsVal_cons, hv1]; omega, fun hc' => absurd hc' hcn⟩

/-! ## `klimbs_add_carry`, `klimbs_add` -/

/-- `klimbs_add_carry(a, b, carry)` with a carry bit: `a + b + carry`. -/
theorem klimbs_add_carry_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_add_carry" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_add_carry c args h r h' calls := by
  intro a b k hargs good hk n m ⟨la, hla, rfl⟩ ⟨lb, hlb, rfl⟩
  subst hargs
  rcases Obs.«KernelKlimbs::klimbs_add_carry».obs ev with
    ⟨ld, hv, hr, hh, -⟩ |
    ⟨cs45, ld, hne, ev1, hc⟩ |
    ⟨x_la, x_ra, ld, ld2, hv, hr, hh, -⟩ |
    ⟨x_la, x_ra, cs118, ld, ld2, hne, ev1, hc⟩ |
    ⟨x_la, x_ra, x_lb, x_rb, m148, cs158, x_sum1, x_carry1, m204, cs214, v234, m243, cs251,
      x_sum2, x_carry2, v330, m331, x338, y339, m340, cs349, cs363, v383, m392, cs400,
      ld, ld2, ev1, ev2, ev3, ev4, ev5, op, rfl, rfl, ev6, hc⟩
  · -- `a` empty, no carry: `b`
    obtain rfl := lrep_nil_of_load hla ld
    rw [hr, hh]
    have h0 := field_eq_zero_val hv
    exact ⟨lb, hlb, by lv_omega⟩
  · -- `a` empty, a carry: `b + 1`
    obtain rfl := lrep_nil_of_load hla ld
    subst hc
    have hk1 : ZMod.val k = 1 := by have := field_ne_zero_val hne; omega
    obtain ⟨ls', hl', hv'⟩ := (ih.get (.nat .klimbs_succ) (by nat_lt_calls) ev1 b rfl
      (good.sub fun x hx => by simp [hx]) (limbsVal lb)).1 ⟨lb, hlb, rfl⟩
    exact ⟨ls', hl', by lv_omega⟩
  · -- `b` empty, no carry: `a`
    obtain rfl := lrep_nil_of_load hlb ld2
    rw [hr, hh]
    have h0 := field_eq_zero_val hv
    exact ⟨la, hla, by lv_omega⟩
  · -- `b` empty, a carry: `a + 1`
    obtain rfl := lrep_nil_of_load hlb ld2
    subst hc
    have hk1 : ZMod.val k = 1 := by have := field_ne_zero_val hne; omega
    obtain ⟨ls', hl', hv'⟩ := (ih.get (.nat .klimbs_succ) (by nat_lt_calls) ev1 a rfl
      (good.sub fun x hx => by simp [hx]) (limbsVal la)).1 ⟨la, hla, rfl⟩
    exact ⟨ls', hl', by lv_omega⟩
  · -- two limbs and the carry: the low limb of the sum, then the rest with the carry out
    obtain ⟨x, la0, rfl, hx, hla0⟩ := lrep_cons_of_load hla ld
    obtain ⟨y, lb0, rfl, hy, hlb0⟩ := lrep_cons_of_load hlb ld2
    have hxb := toNat_lt x
    have hyb := toNat_lt y
    obtain ⟨rfl, rfl, rfl⟩ := add_words hx hy ev1
    obtain ⟨rfl, rfl, -⟩ := from_field ev2
    obtain ⟨ws, hws, hrs⟩ := word_of h (Nat.mod_lt (x.toNat + y.toNat) (by decide))
    obtain ⟨wk, hwk, hrk⟩ := word_lowByte h (k := k) (by omega)
    obtain ⟨rfl, rfl, rfl⟩ := add_words hrs hrk ev3
    obtain ⟨rfl, rfl⟩ := to_field ev4
    obtain ⟨rfl, rfl⟩ := to_field ev5
    rw [add_ok op, ← Nat.cast_add] at ev6
    subst hc
    have hbit : (x.toNat + y.toNat) / B64 +
        (ws.toNat + wk.toNat) / B64 ≤ 1 := by omega
    have hval : ZMod.val ((((x.toNat + y.toNat) / B64 +
        (ws.toNat + wk.toNat) / B64 : Nat)) : F) =
        (x.toNat + y.toNat) / B64 + (ws.toNat + wk.toNat) / B64 := val_natCast (by omega)
    obtain ⟨ls', hl', hv'⟩ := ih.get (.nat .klimbs_add_carry) (by nat_lt_calls) ev6 x_ra x_rb _ rfl
      (good.sub fun x hx => by simp [hx]) (by rw [hval]; exact hbit) (limbsVal la0) (limbsVal lb0)
      ⟨la0, hla0, rfl⟩ ⟨lb0, hlb0, rfl⟩
    rw [hval] at hv'
    obtain ⟨w2, hw2, hr2⟩ := word_of h (Nat.mod_lt (ws.toNat + wk.toNat) (by decide))
    refine ⟨w2 :: ls', lrep_store_cons hr2 hl', ?_⟩
    rw [limbsVal_cons, limbsVal_cons, limbsVal_cons, hv']
    omega

/-- `klimbs_add(a, b)`: `a + b`. -/
theorem klimbs_add_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_add" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_add c args h r h' calls := by
  intro a b hargs good n m ha hb
  subst hargs
  obtain ⟨cs4, ev6, hc⟩ := Obs.«KernelKlimbs::klimbs_add».obs ev
  subst hc
  have := ih.get (.nat .klimbs_add_carry) (by nat_lt_calls) ev6 a b 0 rfl
    (good.sub fun x hx => by simp [hx]) (by rw [val_zero]; decide) n m ha hb
  rwa [val_zero, Nat.add_zero] at this

/-! ## `klimbs_sub_borrow` -/

/-- `klimbs_sub_borrow(a, b, borrow)` with a borrow bit: the borrow out, and the difference when
it is `0`. -/
theorem klimbs_sub_borrow_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_sub_borrow" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_sub_borrow c args h r h' calls := by
  intro a b β hargs good hβ n m ⟨la, hla, rfl⟩ ⟨lb, hlb, rfl⟩
  subst hargs
  rcases Obs.«KernelKlimbs::klimbs_sub_borrow».obs ev with
    ⟨m45, ld, ld2, rfl, rfl, rfl, -⟩ |
    ⟨w73, w74, m86, cs97, m118, ld, ld2, ev1, rfl, rfl, rfl, hc⟩ |
    ⟨w73, w74, v85, m86, cs97, m149, ld, ld2, ev1, hne, rfl, rfl, rfl, hc⟩ |
    ⟨x_la, x_ra, ld, ld2, hv, hr, hh, -⟩ |
    ⟨x_la, x_ra, m245, cs255, x_diff, x_br, m358, cs368, m382, x_rest_res, x_br2, m433,
      ld, ld2, hne, ev1, rfl, ev2, rfl, rfl, rfl, hc⟩ |
    ⟨x_la, x_ra, x_lb, x_rb, m490, cs500, x_sum1, x_br1, m546, cs556, v576, m585, cs593,
      x_sum2, x_br2, v672, m691, cs701, x_rest_res, x_br_final, m760,
      ld, ld2, ev1, ev2, ev3, op, ev4, rfl, rfl, rfl, hc⟩
  · -- both empty: the borrow passes through
    obtain rfl := lrep_nil_of_load hla ld
    obtain rfl := lrep_nil_of_load hlb ld2
    rcases bit_cases hβ with ⟨rfl, h0⟩ | ⟨rfl, h1⟩
    · exact ⟨_, 0, rfl, .inl ⟨rfl, by lv_omega, ⟨[], lrep_store_nil h, by lv_omega⟩⟩⟩
    · exact ⟨_, 1, rfl, .inr ⟨rfl, by lv_omega⟩⟩
  · -- `a` empty, `b` of value `0`: as both empty
    obtain rfl := lrep_nil_of_load hla ld
    subst hc
    have hz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev1 b rfl
      (good.sub fun x hx => by simp [hx]) (limbsVal lb) ⟨lb, hlb, rfl⟩
    have hm0 : limbsVal lb = 0 := by
      by_contra hne
      rw [if_neg hne] at hz
      exact field_one_ne_zero hz
    rcases bit_cases hβ with ⟨rfl, h0⟩ | ⟨rfl, h1⟩
    · exact ⟨_, 0, rfl, .inl ⟨rfl, by lv_omega, ⟨[], lrep_store_nil m86, by lv_omega⟩⟩⟩
    · exact ⟨_, 1, rfl, .inr ⟨rfl, by lv_omega⟩⟩
  · -- `a` empty, `b` not `0`: a borrow out
    obtain rfl := lrep_nil_of_load hla ld
    subst hc
    have hz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev1 b rfl
      (good.sub fun x hx => by simp [hx]) (limbsVal lb) ⟨lb, hlb, rfl⟩
    have hm0 : limbsVal lb ≠ 0 := by
      intro h0
      rw [if_pos h0] at hz
      exact hne hz
    exact ⟨_, 1, rfl, .inr ⟨rfl, by lv_omega⟩⟩
  · -- `b` empty, no borrow: `a`
    obtain rfl := lrep_nil_of_load hlb ld2
    rw [hr, hh]
    have h0 := field_eq_zero_val hv
    obtain rfl : β = 0 := field_inj hv
    exact ⟨a, 0, rfl, .inl ⟨rfl, by lv_omega, ⟨la, hla, by lv_omega⟩⟩⟩
  · -- `b` empty, a borrow: decrement the low limb, then the rest with its borrow
    obtain rfl := lrep_nil_of_load hlb ld2
    obtain ⟨x, la0, rfl, hx, hla0⟩ := lrep_cons_of_load hla ld
    have hxb := toNat_lt x
    have hβ1 : ZMod.val β = 1 := by have := field_ne_zero_val hne; omega
    obtain ⟨w1, hw1, hr1⟩ := word_one h
    obtain ⟨rfl, rfl, rfl⟩ := sub_words hx hr1 ev1
    obtain ⟨bb, hbb, hbbc⟩ := ite_bit (x.toNat < w1.toNat)
    rw [hbb] at ev2
    subst hc
    have hbbv : ZMod.val (bb : F) = bb := val_natCast (by omega)
    obtain ⟨res, bf, hpair, hcase⟩ := ih.get (.nat .klimbs_sub_borrow) (by nat_lt_calls) ev2 x_ra _ _ rfl
      (good.sub fun x hx => by simp [hx]) (by rw [hbbv]; omega) (limbsVal la0) 0
      ⟨la0, lrep_mono (Heap.Extends.snoc _ _) hla0, rfl⟩ ⟨[], lrep_store_nil h, rfl⟩
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    rw [hbbv] at hcase
    obtain ⟨wd, hwd, hrd⟩ := word_of h (Nat.mod_lt (x.toNat + B64 - w1.toNat) (by decide))
    rcases hcase with ⟨rfl, hle, ⟨ls', hl', hv'⟩⟩ | ⟨rfl, hlt⟩
    · refine ⟨_, 0, rfl, .inl ⟨rfl, ?_, ⟨wd :: ls', lrep_store_cons hrd hl', ?_⟩⟩⟩
      · rw [limbsVal_cons]; lv_omega
      · rw [limbsVal_cons, limbsVal_cons, hv']; lv_omega
    · exact ⟨_, 1, rfl, .inr ⟨rfl, by rw [limbsVal_cons]; lv_omega⟩⟩
  · -- two limbs: subtract them, then the borrow, then the rest with the borrows out
    obtain ⟨x, la0, rfl, hx, hla0⟩ := lrep_cons_of_load hla ld
    obtain ⟨y, lb0, rfl, hy, hlb0⟩ := lrep_cons_of_load hlb ld2
    have hxb := toNat_lt x
    have hyb := toNat_lt y
    obtain ⟨rfl, rfl, rfl⟩ := sub_words hx hy ev1
    obtain ⟨rfl, rfl, -⟩ := from_field ev2
    obtain ⟨ws, hws, hrs⟩ := word_of h (Nat.mod_lt (x.toNat + B64 - y.toNat) (by decide))
    obtain ⟨wβ, hwβ, hrβ⟩ := word_lowByte h (k := β) (by omega)
    obtain ⟨rfl, rfl, rfl⟩ := sub_words hrs hrβ ev3
    obtain ⟨b1, hb1, hb1c⟩ := ite_bit (x.toNat < y.toNat)
    obtain ⟨b2, hb2, hb2c⟩ := ite_bit (ws.toNat < wβ.toNat)
    rw [hb1, hb2] at op
    rw [add_ok op, ← Nat.cast_add] at ev4
    subst hc
    have hbits : b1 + b2 ≤ 1 := by omega
    have hbv : ZMod.val ((b1 + b2 : Nat) : F) = b1 + b2 := val_natCast (by omega)
    obtain ⟨res, bf, hpair, hcase⟩ := ih.get (.nat .klimbs_sub_borrow) (by nat_lt_calls) ev4 x_ra x_rb _
      rfl (good.sub fun x hx => by simp [hx]) (by rw [hbv]; exact hbits) (limbsVal la0)
      (limbsVal lb0) ⟨la0, hla0, rfl⟩ ⟨lb0, hlb0, rfl⟩
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    rw [hbv] at hcase
    obtain ⟨w2, hw2, hr2⟩ := word_of h (Nat.mod_lt (ws.toNat + B64 - wβ.toNat) (by decide))
    rcases hcase with ⟨rfl, hle, ⟨ls', hl', hv'⟩⟩ | ⟨rfl, hlt⟩
    · refine ⟨_, 0, rfl, .inl ⟨rfl, ?_, ⟨w2 :: ls', lrep_store_cons hr2 hl', ?_⟩⟩⟩
      · rw [limbsVal_cons, limbsVal_cons]; omega
      · rw [limbsVal_cons, limbsVal_cons, limbsVal_cons, hv']; omega
    · exact ⟨_, 1, rfl, .inr ⟨rfl, by rw [limbsVal_cons, limbsVal_cons]; omega⟩⟩

/-! ## `klimbs_normalize`, `klimbs_sub`, `klimbs_le`, `klimbs_dec`, `klimbs_is_zero` -/

/-- `klimbs_normalize(n)`: the same value, canonical. -/
theorem klimbs_normalize_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_normalize" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_normalize c args h r h' calls := by
  intro a hargs good n ⟨ls, hl, rfl⟩
  subst hargs
  rcases Obs.«KernelKlimbs::klimbs_normalize».obs ev with
    ⟨ld, rfl, rfl, -⟩ |
    ⟨x_limb, x_rest, v46, m47, cs57, m88, cs99, ld, ev1, ld2, ev2, rfl, rfl, hc⟩ |
    ⟨x_limb, x_rest, v46, m47, cs57, m88, cs99, m146, ld, ev1, ld2, ev2, rfl, rfl, rfl, hc⟩ |
    ⟨x_limb, x_rest, v46, m47, cs57, v68, ld, ev1, ld2, hne, rfl, rfl, hc⟩
  · -- `Nil`
    obtain rfl := lrep_nil_of_load hl ld
    exact ⟨[], lrep_store_nil h, rfl, canon_nil⟩
  · -- the rest normalizes to `Nil` and the limb is `0`: `Nil`
    obtain ⟨l, ls0, rfl, hl0, hls0⟩ := lrep_cons_of_load hl ld
    subst hc
    obtain ⟨ls1, hls1, hv1, hc1⟩ := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev1 x_rest rfl
      (good.sub fun x hx => by simp [hx]) (limbsVal ls0) ⟨ls0, hls0, rfl⟩
    obtain rfl := lrep_nil_of_load hls1 ld2
    obtain ⟨hz, rfl⟩ := is_zero_word hl0 ev2
    have hl0z : l.toNat = 0 := by
      by_contra hne
      rw [if_neg hne] at hz
      exact field_one_ne_zero hz
    refine ⟨[], lrep_store_nil _, ?_, canon_nil⟩
    rw [limbsVal_cons]
    lv_omega
  · -- the rest normalizes to `Nil` and the limb is not `0`: the limb alone
    obtain ⟨l, ls0, rfl, hl0, hls0⟩ := lrep_cons_of_load hl ld
    subst hc
    obtain ⟨ls1, hls1, hv1, hc1⟩ := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev1 x_rest rfl
      (good.sub fun x hx => by simp [hx]) (limbsVal ls0) ⟨ls0, hls0, rfl⟩
    obtain rfl := lrep_nil_of_load hls1 ld2
    obtain ⟨hz, rfl⟩ := is_zero_word hl0 ev2
    have hl0z : l.toNat ≠ 0 := by
      intro h0
      rw [if_pos h0] at hz
      exact field_one_ne_zero hz.symm
    refine ⟨[l], lrep_store_cons hl0 (lrep_store_nil _), ?_, ?_⟩
    · rw [limbsVal_cons, limbsVal_cons]; lv_omega
    · exact canon_cons_of_pos canon_nil (by rw [limbsVal_cons]; lv_omega)
  · -- the rest normalizes to a nonempty list: the limb in front of it
    obtain ⟨l, ls0, rfl, hl0, hls0⟩ := lrep_cons_of_load hl ld
    subst hc
    obtain ⟨ls1, hls1, hv1, hc1⟩ := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev1 x_rest rfl
      (good.sub fun x hx => by simp [hx]) (limbsVal ls0) ⟨ls0, hls0, rfl⟩
    have hne1 : ls1 ≠ [] := rep_cons_of_not_nil hls1 ld2 hne
    have hpos := limbsVal_pos_of_ne_nil hc1 hne1
    refine ⟨l :: ls1, lrep_store_cons hl0 hls1, ?_, ?_⟩
    · rw [limbsVal_cons, limbsVal_cons, hv1]
    · exact canon_cons_of_pos hc1 (by rw [limbsVal_cons]; omega)

/-- `klimbs_sub(a, b)`: truncated subtraction, canonical. -/
theorem klimbs_sub_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_sub" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_sub c args h r h' calls := by
  intro a b hargs good n m ha hb
  subst hargs
  rcases Obs.«KernelKlimbs::klimbs_sub».obs ev with
    ⟨m2, cs12, x_result, ev1, rfl, rfl, hc⟩ |
    ⟨m2, cs12, x_result, cs95, ev1, ev2, hc⟩
  · -- a borrow out: `0`
    subst hc
    obtain ⟨res, bf, hpair, hcase⟩ := ih.get (.nat .klimbs_sub_borrow) (by nat_lt_calls) ev1 a b 0
      rfl (good.sub fun x hx => by simp [hx]) (by rw [val_zero]; decide) n m ha hb
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hpair
    obtain ⟨rfl, hbf⟩ := hpair
    rw [val_zero] at hcase
    rcases hcase with ⟨rfl, -, -⟩ | ⟨-, hlt⟩
    · exact absurd (field_inj hbf) one_ne_zero
    · exact ⟨[], lrep_store_nil m2, by lv_omega, canon_nil⟩
  · -- no borrow out: the difference, normalized
    subst hc
    obtain ⟨res, bf, hpair, hcase⟩ := ih.get (.nat .klimbs_sub_borrow) (by nat_lt_calls) ev1 a b 0
      rfl (good.sub fun x hx => by simp [hx]) (by rw [val_zero]; decide) n m ha hb
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hpair
    obtain ⟨rfl, hbf⟩ := hpair
    rw [val_zero] at hcase
    rcases hcase with ⟨-, -, hrep⟩ | ⟨rfl, -⟩
    · have := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev2 x_result rfl
        (good.sub fun x hx => by simp [hx]) (n - m - 0) hrep
      simpa using this
    · exact absurd (field_inj hbf).symm one_ne_zero

/-- `klimbs_le(a, b)`: `1` exactly when `a ≤ b`. -/
theorem klimbs_le_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_le" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_le c args h r h' calls := by
  intro a b hargs good n m ha hb
  subst hargs
  rcases Obs.«KernelKlimbs::klimbs_le».obs ev with
    ⟨v1, m2, cs12, ev1, ld, rfl, rfl, hc⟩ |
    ⟨v1, m2, cs12, v31, ev1, ld, hne, rfl, rfl, hc⟩
  · subst hc
    obtain ⟨ls, hl, hv, hcn⟩ := ih.get (.nat .klimbs_sub) (by nat_lt_calls) ev1 a b rfl
      (good.sub fun x hx => by simp [hx]) n m ha hb
    obtain rfl := lrep_nil_of_load hl ld
    rw [limbsVal_nil] at hv
    rw [if_pos (by omega)]
  · subst hc
    obtain ⟨ls, hl, hv, hcn⟩ := ih.get (.nat .klimbs_sub) (by nat_lt_calls) ev1 a b rfl
      (good.sub fun x hx => by simp [hx]) n m ha hb
    have hpos := limbsVal_pos_of_ne_nil hcn (rep_cons_of_not_nil hl ld hne)
    rw [if_neg (by omega)]

/-- `klimbs_dec(a)`: `a - 1`, canonical. -/
theorem klimbs_dec_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_dec" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_dec c args h r h' calls := by
  intro a hargs good n ha
  subst hargs
  obtain ⟨m2, m83, cs98, rfl, rfl, ev1, hc⟩ := Obs.«KernelKlimbs::klimbs_dec».obs ev
  subst hc
  obtain ⟨w1, hw1, hr1⟩ := word_one h
  exact ih.get (.nat .klimbs_sub) (by nat_lt_calls) ev1 a _ rfl
    (good.sub fun x hx => by simp [hx]) n 1
    (repLimbs_mono ((Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)) ha)
    ⟨[w1], lrep_store_cons hr1 (lrep_store_nil h), by simp [limbsVal_cons, limbsVal_nil, hw1]⟩

/-- `klimbs_is_zero(x)`: `1` exactly when the value is `0`. -/
theorem klimbs_is_zero_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_is_zero" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_is_zero c args h r h' calls := by
  intro a hargs good n ha
  subst hargs
  rcases Obs.«KernelKlimbs::klimbs_is_zero».obs ev with
    ⟨m2, p10, cs16, ev1, ld, rfl, rfl, hc⟩ |
    ⟨v1, m2, p10, cs16, ev1, ld, hne, rfl, rfl, hc⟩
  · subst hc
    obtain ⟨ls, hl, hv, hcn⟩ := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev1 a rfl
      (good.sub fun x hx => by simp [hx]) n ha
    obtain rfl := lrep_nil_of_load hl ld
    rw [limbsVal_nil] at hv
    rw [if_pos hv.symm]
  · subst hc
    obtain ⟨ls, hl, hv, hcn⟩ := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev1 a rfl
      (good.sub fun x hx => by simp [hx]) n ha
    have hpos := limbsVal_pos_of_ne_nil hcn (rep_cons_of_not_nil hl ld hne)
    rw [if_neg (by omega)]

/-! ## `divmod_256`, `klimbs_shl_limbs` -/

/-- `divmod_256(x, q)`: `(x mod 256, q + x div 256)`, at `x < 2^32`. -/
theorem divmod_256_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::divmod_256" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.divmod_256 c args h r h' calls := by
  intro x q hargs good
  subst hargs
  have v256 : ZMod.val (256 : F) = 256 := by
    have := val_natCast (n := 256) (by decide)
    simpa using this
  rcases Obs.«KernelKlimbs::divmod_256».obs ev with
    ⟨m2, cs13, ev1, hr, hh, hc⟩ |
    ⟨m2, cs13, cs64, v67, v68, ev1, op1, op2, ev2, hc⟩
  · -- `x < 256`: the digit is `x`, the quotient unchanged
    obtain ⟨hx, -, hr1, -, hh1⟩ := Lib.less_than_fields_field ev1
    have hlt : ZMod.val x < 256 := by
      have := hr1.mp rfl
      rwa [v256] at this
    refine ⟨lt_of_lt_of_eq hx (by norm_num), ?_, hh.trans hh1⟩
    rw [hr, Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt, natCast_val, Nat.cast_zero, add_zero]
  · -- `x ≥ 256`: one more in the quotient, on `x - 256`
    obtain ⟨hx, -, hr1, -, hh1⟩ := Lib.less_than_fields_field ev1
    have hge : 256 ≤ ZMod.val x := by
      by_contra hlt
      have := hr1.mpr (by rw [v256]; omega)
      exact field_one_ne_zero this.symm
    subst hc
    rw [sub_ok op1, add_ok op2] at ev2
    obtain ⟨-, hr, hh'⟩ := ih.get (.nat .divmod_256) (by nat_lt_calls) ev2 _ _ rfl
      (good.sub fun x hx => by simp [hx])
    have hsub : ZMod.val (x - 256) = ZMod.val x - 256 := by
      rw [val_sub (by rw [v256]; exact hge), v256]
    rw [hsub] at hr
    refine ⟨lt_of_lt_of_eq hx (by norm_num), ?_, hh'.trans hh1⟩
    have e1 : (ZMod.val x - 256) % 256 = ZMod.val x % 256 := by omega
    have e2 : ZMod.val x / 256 = (ZMod.val x - 256) / 256 + 1 := by omega
    have e3 : q + 1 + (((ZMod.val x - 256) / 256 : Nat) : F) =
        q + ((ZMod.val x / 256 : Nat) : F) := by
      rw [e2]; push_cast; ring
    rw [hr, e1, e3]

/-- `klimbs_shl_limbs(x, shift)`: `x * 2^(64 * shift)`. -/
theorem klimbs_shl_limbs_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_shl_limbs" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_shl_limbs c args h r h' calls := by
  intro a s hargs good n ha
  subst hargs
  rcases Obs.«KernelKlimbs::klimbs_shl_limbs».obs ev with
    ⟨hv, hr, hh, -⟩ |
    ⟨m24, cs114, v118, hne, rfl, op, ev1, hc⟩
  · rw [hr, hh, field_inj hv, val_zero]
    simpa using ha
  · subst hc
    rw [sub_ok op] at ev1
    have hs0 : s ≠ 0 := fun e => hne (by rw [e])
    obtain ⟨ls, hl, rfl⟩ := ha
    obtain ⟨w0, hw0, hr0⟩ := word_zero h
    have hrep : RepLimbs (h ++ [.construct limbListEnum "Cons" [.tuple [.field 0, .field 0, .field 0,
        .field 0, .field 0, .field 0, .field 0, .field 0], a]]) (B64 * limbsVal ls)
        (.ptr (.enum limbListEnum) h.length) :=
      ⟨w0 :: ls, lrep_store_cons hr0 hl, by rw [limbsVal_cons, hw0, Nat.zero_add]⟩
    have := ih.get (.nat .klimbs_shl_limbs) (by nat_lt_calls) ev1 _ (s - 1) rfl
      (good.sub fun x hx => by simp [hx]) _ hrep
    rw [val_sub_one hs0] at this
    have hpos : 0 < ZMod.val s := Nat.pos_of_ne_zero (fun e => hs0 ((ZMod.val_eq_zero s).mp e))
    have e : B64 * limbsVal ls * 2 ^ (64 * (ZMod.val s - 1)) =
        limbsVal ls * 2 ^ (64 * ZMod.val s) := by
      obtain ⟨t, ht⟩ : ∃ t, ZMod.val s = t + 1 := ⟨ZMod.val s - 1, by omega⟩
      rw [ht, Nat.add_sub_cancel, show 64 * (t + 1) = 64 * t + 64 by ring, Nat.pow_add,
        show (2 : Nat) ^ 64 = 18446744073709551616 by norm_num]
      ring
    rwa [e] at this

/-! ## Bitwise operations -/

namespace NatAux

theorem testBit_split {a x : Nat} (ha : a < 2 ^ 64) (i : Nat) :
    (a + B64 * x).testBit i = if i < 64 then a.testBit i else x.testBit (i - 64) := by
  rw [show a + B64 * x = 2 ^ 64 * x + a by ring]
  exact Nat.testBit_two_pow_mul_add x ha i

theorem land_split {a b x y : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (a + B64 * x) &&& (b + B64 * y) = (a &&& b) + B64 * (x &&& y) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, testBit_split ha, testBit_split hb,
    testBit_split (Nat.and_lt_two_pow a hb)]
  by_cases hi : i < 64 <;> simp [hi]

theorem lor_split {a b x y : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (a + B64 * x) ||| (b + B64 * y) = (a ||| b) + B64 * (x ||| y) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, testBit_split ha, testBit_split hb,
    testBit_split (Nat.or_lt_two_pow ha hb)]
  by_cases hi : i < 64 <;> simp [hi]

theorem xor_split {a b x y : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (a + B64 * x) ^^^ (b + B64 * y) = (a ^^^ b) + B64 * (x ^^^ y) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, testBit_split ha, testBit_split hb,
    testBit_split (Nat.xor_lt_two_pow ha hb)]
  by_cases hi : i < 64 <;> simp [hi]

theorem toNat_lt_two_pow (w : UInt64) : w.toNat < 2 ^ 64 := w.toNat_lt

end NatAux

/-- `klimbs_land(a, b)`: `Nat.land a b`. -/
theorem klimbs_land_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_land" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_land c args h r h' calls := by
  intro a b hargs good n m ⟨la, hla, rfl⟩ ⟨lb, hlb, rfl⟩
  subst hargs
  rcases Obs.«KernelKlimbs::klimbs_land».obs ev with
    ⟨ld, rfl, rfl, -⟩ |
    ⟨x_la, x_ra, ld, ld2, rfl, rfl, -⟩ |
    ⟨x_la, x_ra, x_lb, x_rb, v99, v100, m102, cs110, m130, cs138, ld, ld2, rfl, rfl, ev1, ev2, hc⟩
  · obtain rfl := lrep_nil_of_load hla ld
    exact ⟨[], lrep_store_nil h, by rw [limbsVal_nil]; exact (Nat.zero_and _).symm⟩
  · obtain rfl := lrep_nil_of_load hlb ld2
    exact ⟨[], lrep_store_nil h, by rw [limbsVal_nil]; exact (Nat.and_zero _).symm⟩
  · obtain ⟨x, la0, rfl, hx, hla0⟩ := lrep_cons_of_load hla ld
    obtain ⟨y, lb0, rfl, hy, hlb0⟩ := lrep_cons_of_load hlb ld2
    obtain ⟨hr1, rfl⟩ := and_words hx hy ev1
    subst hc
    obtain ⟨ls', hl', hv'⟩ := ih.get (.nat .klimbs_land) (by nat_lt_calls) ev2 x_ra x_rb rfl
      (good.sub fun x hx => by simp [hx]) (limbsVal la0) (limbsVal lb0) ⟨la0, hla0, rfl⟩
      ⟨lb0, hlb0, rfl⟩
    refine ⟨(x &&& y) :: ls', lrep_store_cons hr1 hl', ?_⟩
    rw [limbsVal_cons, limbsVal_cons, limbsVal_cons, hv', UInt64.toNat_and]
    exact (land_split (toNat_lt_two_pow x) (toNat_lt_two_pow y)).symm

/-- `klimbs_lor(a, b)`: `Nat.lor a b`. -/
theorem klimbs_lor_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_lor" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_lor c args h r h' calls := by
  intro a b hargs good n m ⟨la, hla, rfl⟩ ⟨lb, hlb, rfl⟩
  subst hargs
  rcases Obs.«KernelKlimbs::klimbs_lor».obs ev with
    ⟨ld, hr, hh, -⟩ |
    ⟨x_la, x_ra, ld, ld2, hr, hh, -⟩ |
    ⟨x_la, x_ra, x_lb, x_rb, v89, v90, m92, cs100, m120, cs128, ld, ld2, rfl, rfl, ev1, ev2, hc⟩
  · obtain rfl := lrep_nil_of_load hla ld
    rw [hr, hh]
    exact ⟨lb, hlb, by rw [limbsVal_nil]; exact (Nat.zero_or _).symm⟩
  · obtain rfl := lrep_nil_of_load hlb ld2
    rw [hr, hh]
    exact ⟨la, hla, by rw [limbsVal_nil]; exact (Nat.or_zero _).symm⟩
  · obtain ⟨x, la0, rfl, hx, hla0⟩ := lrep_cons_of_load hla ld
    obtain ⟨y, lb0, rfl, hy, hlb0⟩ := lrep_cons_of_load hlb ld2
    obtain ⟨hr1, rfl⟩ := or_words hx hy ev1
    subst hc
    obtain ⟨ls', hl', hv'⟩ := ih.get (.nat .klimbs_lor) (by nat_lt_calls) ev2 x_ra x_rb rfl
      (good.sub fun x hx => by simp [hx]) (limbsVal la0) (limbsVal lb0) ⟨la0, hla0, rfl⟩
      ⟨lb0, hlb0, rfl⟩
    refine ⟨(x ||| y) :: ls', lrep_store_cons hr1 hl', ?_⟩
    rw [limbsVal_cons, limbsVal_cons, limbsVal_cons, hv', UInt64.toNat_or]
    exact (lor_split (toNat_lt_two_pow x) (toNat_lt_two_pow y)).symm

/-- `klimbs_xor_op(a, b)`: `Nat.xor a b`. -/
theorem klimbs_xor_op_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_xor_op" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_xor_op c args h r h' calls := by
  intro a b hargs good n m ⟨la, hla, rfl⟩ ⟨lb, hlb, rfl⟩
  subst hargs
  rcases Obs.«KernelKlimbs::klimbs_xor_op».obs ev with
    ⟨ld, hr, hh, -⟩ |
    ⟨x_la, x_ra, ld, ld2, hr, hh, -⟩ |
    ⟨x_la, x_ra, x_lb, x_rb, v89, v90, m92, cs100, m120, cs128, ld, ld2, rfl, rfl, ev1, ev2, hc⟩
  · obtain rfl := lrep_nil_of_load hla ld
    rw [hr, hh]
    exact ⟨lb, hlb, by rw [limbsVal_nil]; exact (Nat.zero_xor _).symm⟩
  · obtain rfl := lrep_nil_of_load hlb ld2
    rw [hr, hh]
    exact ⟨la, hla, by rw [limbsVal_nil]; exact (Nat.xor_zero _).symm⟩
  · obtain ⟨x, la0, rfl, hx, hla0⟩ := lrep_cons_of_load hla ld
    obtain ⟨y, lb0, rfl, hy, hlb0⟩ := lrep_cons_of_load hlb ld2
    obtain ⟨hr1, rfl⟩ := xor_words hx hy ev1
    subst hc
    obtain ⟨ls', hl', hv'⟩ := ih.get (.nat .klimbs_xor_op) (by nat_lt_calls) ev2 x_ra x_rb rfl
      (good.sub fun x hx => by simp [hx]) (limbsVal la0) (limbsVal lb0) ⟨la0, hla0, rfl⟩
      ⟨lb0, hlb0, rfl⟩
    refine ⟨(x ^^^ y) :: ls', lrep_store_cons hr1 hl', ?_⟩
    rw [limbsVal_cons, limbsVal_cons, limbsVal_cons, hv', UInt64.toNat_xor]
    exact (xor_split (toNat_lt_two_pow x) (toNat_lt_two_pow y)).symm

end IxVM.Refinement.Core
