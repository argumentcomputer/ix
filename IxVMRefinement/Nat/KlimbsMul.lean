import IxVMRefinement.Nat.Klimbs
import IxVMRefinement.Nat.WordMul
import IxVMRefinement.Core.RomBound

/-! # `KernelKlimbs`: multiplication, division, gcd, powers, shifts; the division helpers

Step lemmas of the limb functions built on multiplication and division, and of `IxVMCompat`'s
long division (`ordinary_div_mod`, `divide_grow`). Each reads its callees' registered specs
from the induction hypothesis: `klimbs_div_mod`'s quotient and remainder are those of
`ordinary_div_mod`, normalized (the circuit's own check of the pair is not needed for the
claim). The multiplier's shift counter is bounded by the multiplicand's length, which the
ROM bounds (`RomBound.bounded_length_lt`). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open NatAux

set_option linter.unusedVariables false

namespace NatAux

theorem pow_even {n m : Nat} (h : m % 2 = 0) : (n * n) ^ (m / 2) = n ^ m := by
  rw [← pow_two, ← pow_mul]
  congr 1
  omega

theorem pow_odd {n m : Nat} (h : m % 2 = 1) : n * (n * n) ^ (m / 2) = n ^ m := by
  rw [← pow_two, ← pow_mul, ← pow_succ']
  congr 1
  omega

theorem gcd_step (n m : Nat) : Nat.gcd m (n % m) = Nat.gcd n m := by
  rw [Nat.gcd_comm n m, Nat.gcd_rec m n, Nat.gcd_comm]

/-- **One step of doubling division**: from the quotient and remainder by `2m`, those by
`m`. -/
theorem div_mod_double {n m : Nat} (hm : 0 < m) :
    (n % (m + m) < m → n / m = n / (m + m) + n / (m + m) ∧ n % m = n % (m + m)) ∧
      (m ≤ n % (m + m) →
        n / m = n / (m + m) + n / (m + m) + 1 ∧ n % m = n % (m + m) - m) := by
  have hd := Nat.div_add_mod n (m + m)
  have hlt := Nat.mod_lt n (show 0 < m + m by omega)
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · refine (Nat.div_mod_unique hm).mpr ⟨?_, hr⟩
    nlinarith [hd]
  · refine (Nat.div_mod_unique hm).mpr ⟨?_, by omega⟩
    obtain ⟨e, he⟩ : ∃ e, n % (m + m) = m + e := ⟨n % (m + m) - m, by omega⟩
    rw [he, show m + e - m = e by omega]
    rw [he] at hd
    nlinarith [hd]

theorem pow40 : (2 : Nat) ^ 40 = 1099511627776 := by norm_num

theorem pow39 : (2 : Nat) ^ 39 = 549755813888 := by norm_num

end NatAux

/-! ## Multiplication -/

/-- `klimbs_mul_outer(a, b, acc, shift)`: `acc + a * b * 2^(64 * shift)`, at a shift plus the
multiplicand's length below `2^40`. -/
theorem klimbs_mul_outer_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_mul_outer" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_mul_outer c args h r h' calls := by
  intro a b acc s hargs good ls m k hl hb hacc hlen
  subst hargs
  rcases Obs.«KernelKlimbs::klimbs_mul_outer».obs ev with
    ⟨ld, hr, hh, -⟩ |
    ⟨x_a_limb, x_rest, v41, m42, cs52, v136, m137, cs147, v166, m167, cs177, cs199, v205,
      ld, ev1, ev2, ev3, op, ev4, hc⟩
  · obtain rfl := lrep_nil_of_load hl ld
    rw [hr, hh]
    simpa [limbsVal_nil] using hacc
  · obtain ⟨x, ls0, rfl, hx, hls0⟩ := lrep_cons_of_load hl ld
    subst hc
    obtain ⟨w0, hw0, hr0⟩ := word_zero h
    have e1 := ObsFn.heap_extends ev1
    have e2 := ObsFn.heap_extends ev2
    have e3 := ObsFn.heap_extends ev3
    have h1 := ih.get (.nat .klimbs_mul_single) (by nat_lt_calls) ev1 _ b _ rfl
      (good.sub fun x hx => by simp [hx]) x w0 m hx hr0 hb
    have h2 := ih.get (.nat .klimbs_shl_limbs) (by nat_lt_calls) ev2 _ s rfl
      (good.sub fun x hx => by simp [hx]) _ h1
    have h3 := ih.get (.nat .klimbs_add) (by nat_lt_calls) ev3 acc _ rfl
      (good.sub fun x hx => by simp [hx]) k _ (repLimbs_mono (e1.trans e2) hacc) h2
    rw [add_ok op] at ev4
    simp only [List.length_cons, pow40] at hlen
    have hs1 : ZMod.val (s + 1) = ZMod.val s + 1 := val_add_one (by omega)
    have h4 := ih.get (.nat .klimbs_mul_outer) (by nat_lt_calls) ev4 x_rest b _ (s + 1) rfl
      (good.sub fun x hx => by simp [hx]) ls0 m _ (lrep_mono (e1.trans (e2.trans e3)) hls0)
      (repLimbs_mono (e1.trans (e2.trans e3)) hb) h3 (by rw [hs1, pow40]; omega)
    rw [hs1] at h4
    have e : k + (x.toNat * m + w0.toNat) * 2 ^ (64 * ZMod.val s) +
        limbsVal ls0 * m * 2 ^ (64 * (ZMod.val s + 1)) =
        k + limbsVal (x :: ls0) * m * 2 ^ (64 * ZMod.val s) := by
      rw [limbsVal_cons, hw0, show 64 * (ZMod.val s + 1) = 64 * ZMod.val s + 64 by ring,
        Nat.pow_add, show (2 : Nat) ^ 64 = 18446744073709551616 by norm_num]
      ring
    rwa [e] at h4

/-- `klimbs_mul(a, b)`: `a * b`. -/
theorem klimbs_mul_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_mul" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_mul c args h r h' calls := by
  rintro a b hargs good n m ⟨la, hla, rfl⟩ hb
  subst hargs
  obtain ⟨cs4, m26, rfl, ev6, hc⟩ := Obs.«KernelKlimbs::klimbs_mul».obs ev
  subst hc
  have ext : Heap.Extends h (h ++ [.construct limbListEnum "Nil" []]) := Heap.Extends.snoc _ _
  have hlen : la.length < 2 ^ 39 :=
    RomBound.bounded_length_lt good.2
      (c := ⟨"KernelKlimbs::klimbs_mul_outer",
        [a, b, .ptr (.enum limbListEnum) h.length, .field 0],
        h ++ [.construct limbListEnum "Nil" []]⟩) (by simp) (by simp) (lrep_mono ext hla)
  have := ih.get (.nat .klimbs_mul_outer) (by nat_lt_calls) ev6 a b _ 0 rfl
    (good.sub fun x hx => by simp [hx]) la m 0 (lrep_mono ext hla) (repLimbs_mono ext hb)
    ⟨[], lrep_store_nil h, rfl⟩ (by rw [pow39] at hlen; rw [val_zero, pow40]; omega)
  simpa [val_zero] using this

/-! ## Division -/

/-- `klimbs_div_mod(a, b)`: `(a / b, a % b)`, both canonical. -/
theorem klimbs_div_mod_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_div_mod" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_div_mod c args h r h' calls := by
  intro a b hargs good n m ha hb
  subst hargs
  rcases Obs.«KernelKlimbs::klimbs_div_mod».obs ev with
    ⟨m2, cs12, x_q_hint, x_r_hint, v44, m45, cs55, v66, m67, cs77, v88, m89, cs99, v118, m119,
      cs129, v132, m134, cs142, v161, m162, cs172, v194, m197, cs205, m232, cs243, v269, m272,
      cs280, ev1, ev2, ev3, ev4, ev5, ev6, ev7, ev8, heq1, ev9, ev10, heq2, rfl, rfl, hc⟩ |
    ⟨m2, cs12, x_q_hint, x_r_hint, v44, m45, cs55, v66, m67, cs77, v88, m89, cs99, v118, m119,
      cs129, v132, m134, cs142, v161, m162, cs172, v194, m197, cs205, m232, cs243, v335, m338,
      cs346, v349, m352, cs360, ev1, ev2, ev3, ev4, ev5, ev6, ev7, ev8, heq1, ev9, ev10, ev11,
      heq2, rfl, rfl, hc⟩
  · subst hc
    obtain ⟨q, rr, hpair, hq, hrr⟩ := ih.get (.nat .ordinary_div_mod) (by nat_lt_calls) ev1 a b rfl
      (good.sub fun x hx => by simp [hx]) n m ha hb
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    have hq' := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev2 _ rfl
      (good.sub fun x hx => by simp [hx]) _ hq
    have hr' := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev3 _ rfl
      (good.sub fun x hx => by simp [hx]) _ (repLimbs_mono (ObsFn.heap_extends ev2) hrr)
    have ext := (ObsFn.heap_extends ev4).trans ((ObsFn.heap_extends ev5).trans
      ((ObsFn.heap_extends ev6).trans ((ObsFn.heap_extends ev7).trans
        ((ObsFn.heap_extends ev8).trans ((ObsFn.heap_extends ev9).trans
          (ObsFn.heap_extends ev10))))))
    exact ⟨_, _, rfl, repLimbsC_mono ((ObsFn.heap_extends ev3).trans ext) hq',
      repLimbsC_mono ext hr'⟩
  · subst hc
    obtain ⟨q, rr, hpair, hq, hrr⟩ := ih.get (.nat .ordinary_div_mod) (by nat_lt_calls) ev1 a b rfl
      (good.sub fun x hx => by simp [hx]) n m ha hb
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    have hq' := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev2 _ rfl
      (good.sub fun x hx => by simp [hx]) _ hq
    have hr' := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev3 _ rfl
      (good.sub fun x hx => by simp [hx]) _ (repLimbs_mono (ObsFn.heap_extends ev2) hrr)
    have ext := (ObsFn.heap_extends ev4).trans ((ObsFn.heap_extends ev5).trans
      ((ObsFn.heap_extends ev6).trans ((ObsFn.heap_extends ev7).trans
        ((ObsFn.heap_extends ev8).trans ((ObsFn.heap_extends ev9).trans
          ((ObsFn.heap_extends ev10).trans (ObsFn.heap_extends ev11)))))))
    exact ⟨_, _, rfl, repLimbsC_mono ((ObsFn.heap_extends ev3).trans ext) hq',
      repLimbsC_mono ext hr'⟩

/-- `klimbs_div(a, b)`: `a / b`, canonical. -/
theorem klimbs_div_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_div" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_div c args h r h' calls := by
  intro a b hargs good n m ha hb
  subst hargs
  obtain ⟨m2, cs13, x_q, w38, ev1, rfl, rfl, hc⟩ := Obs.«KernelKlimbs::klimbs_div».obs ev
  subst hc
  obtain ⟨q, rr, hpair, hq, -⟩ := ih.get (.nat .klimbs_div_mod) (by nat_lt_calls) ev1 a b rfl
    (good.sub fun x hx => by simp [hx]) n m ha hb
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hpair
  obtain ⟨rfl, -⟩ := hpair
  exact hq

/-- `klimbs_mod(a, b)`: `a % b`, canonical. -/
theorem klimbs_mod_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_mod" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_mod c args h r h' calls := by
  intro a b hargs good n m ha hb
  subst hargs
  obtain ⟨m2, cs13, w38, x_r, ev1, rfl, rfl, hc⟩ := Obs.«KernelKlimbs::klimbs_mod».obs ev
  subst hc
  obtain ⟨q, rr, hpair, -, hrr⟩ := ih.get (.nat .klimbs_div_mod) (by nat_lt_calls) ev1 a b rfl
    (good.sub fun x hx => by simp [hx]) n m ha hb
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hpair
  obtain ⟨-, rfl⟩ := hpair
  exact hrr

/-- `klimbs_gcd(a, b)`: `Nat.gcd a b`. -/
theorem klimbs_gcd_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_gcd" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_gcd c args h r h' calls := by
  intro a b hargs good n m ha hb
  subst hargs
  rcases Obs.«KernelKlimbs::klimbs_gcd».obs ev with
    ⟨m2, cs13, ev1, hr, hh, hc⟩ |
    ⟨m2, cs13, cs40, v44, m53, cs61, ev1, ev2, ev3, hc⟩
  · subst hc
    have hz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev1 b rfl
      (good.sub fun x hx => by simp [hx]) m hb
    have hm0 : m = 0 := by
      by_contra hne
      rw [ite_eq_right hne] at hz
      exact field_one_ne_zero hz
    rw [hr, hh, hm0, Nat.gcd_zero_right]
    exact repLimbs_mono (ObsFn.heap_extends ev1) ha
  · subst hc
    have hz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev1 b rfl
      (good.sub fun x hx => by simp [hx]) m hb
    have hm0 : m ≠ 0 := by
      intro h0
      rw [ite_eq_left h0] at hz
      exact field_one_ne_zero hz.symm
    have e1 := ObsFn.heap_extends ev1
    have hmod := ih.get (.nat .klimbs_mod) (by nat_lt_calls) ev2 a b rfl
      (good.sub fun x hx => by simp [hx]) n m (repLimbs_mono e1 ha) (repLimbs_mono e1 hb)
    have e2 := ObsFn.heap_extends ev2
    have hg := ih.get (.nat .klimbs_gcd) (by nat_lt_calls) ev3 b v44 rfl
      (good.sub fun x hx => by simp [hx]) m (n % m) (repLimbs_mono (e1.trans e2) hb)
      (RepLimbsC.toRepLimbs hmod)
    rwa [gcd_step] at hg

/-! ## Powers and shifts -/

/-- `klimbs_pow(base, exp)`: `base ^ exp`. -/
theorem klimbs_pow_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_pow" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_pow c args h r h' calls := by
  intro a b hargs good n m ha hb
  subst hargs
  rcases Obs.«KernelKlimbs::klimbs_pow».obs ev with
    ⟨m2, cs13, m103, ev1, rfl, rfl, rfl, hc⟩ |
    ⟨m2, cs13, m122, m203, m216, cs226, x_half, x_r, v258, m259, cs269, v272, v273, m275, cs283,
      v286, m288, cs296, m316, cs324, m336, cs347, ev1, rfl, rfl, ev2, ev3, ev4, ev5, ev6, ev7,
      hr, hh, hc⟩ |
    ⟨m2, cs13, m122, m203, m216, cs226, x_half, x_r, v258, m259, cs269, v272, v273, m275, cs283,
      v286, m288, cs296, m316, cs324, m336, cs347, cs374, ev1, rfl, rfl, ev2, ev3, ev4, ev5, ev6,
      ev7, ev8, hc⟩
  · -- exponent `0`: `[1]`
    subst hc
    have hz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev1 b rfl
      (good.sub fun x hx => by simp [hx]) m hb
    have hm0 : m = 0 := by
      by_contra hne
      rw [ite_eq_right hne] at hz
      exact field_one_ne_zero hz
    obtain ⟨w1, hw1, hr1⟩ := word_one h
    exact ⟨[w1], lrep_store_cons hr1 (lrep_store_nil m2), by
      simp [limbsVal_cons, limbsVal_nil, hw1, hm0]⟩
  all_goals
    subst hc
    have hz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev1 b rfl
      (good.sub fun x hx => by simp [hx]) m hb
    have hm0 : m ≠ 0 := by
      intro h0
      rw [ite_eq_left h0] at hz
      exact field_one_ne_zero hz.symm
    have e1 := ObsFn.heap_extends ev1
    obtain ⟨w2, hw2, hr2⟩ := word_two h
    obtain ⟨q, rr, hpair, hq, hrr⟩ := ih.get (.nat .klimbs_div_mod) (by nat_lt_calls) ev2 b _ rfl
      (good.sub fun x hx => by simp [hx]) m 2
      (repLimbs_mono (e1.trans ((Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _))) hb)
      ⟨[w2], lrep_store_cons hr2 (lrep_store_nil _), by simp [limbsVal_cons, limbsVal_nil, hw2]⟩
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    have e2 := ObsFn.heap_extends ev2
    have ext0 : Heap.Extends h m216 :=
      e1.trans (((Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)).trans e2)
    have hsq := ih.get (.nat .klimbs_mul) (by nat_lt_calls) ev3 a a rfl
      (good.sub fun x hx => by simp [hx]) n n (repLimbs_mono ext0 ha) (repLimbs_mono ext0 ha)
    have e3 := ObsFn.heap_extends ev3
    have hsq' := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev4 _ rfl
      (good.sub fun x hx => by simp [hx]) _ hsq
    have e4 := ObsFn.heap_extends ev4
    have hhalf := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev5 _ rfl
      (good.sub fun x hx => by simp [hx]) _ (repLimbs_mono (e3.trans e4) (RepLimbsC.toRepLimbs hq))
    have e5 := ObsFn.heap_extends ev5
    have hp := ih.get (.nat .klimbs_pow) (by nat_lt_calls) ev6 _ _ rfl
      (good.sub fun x hx => by simp [hx]) _ _
      (repLimbs_mono e5 (RepLimbsC.toRepLimbs hsq')) (RepLimbsC.toRepLimbs hhalf)
    have e6 := ObsFn.heap_extends ev6
    have hz2 := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev7 _ rfl
      (good.sub fun x hx => by simp [hx]) _
      (repLimbs_mono (e3.trans (e4.trans (e5.trans e6))) (RepLimbsC.toRepLimbs hrr))
  · -- even exponent: the square's power
    have hm2 : m % 2 = 0 := by
      by_contra hne
      rw [ite_eq_right hne] at hz2
      exact field_one_ne_zero hz2
    rw [hr, hh]
    rw [← pow_even hm2]
    exact repLimbs_mono (ObsFn.heap_extends ev7) hp
  · -- odd exponent: one more factor of the base
    have hm2 : m % 2 = 1 := by
      have hne : m % 2 ≠ 0 := by
        intro h0
        rw [ite_eq_left h0] at hz2
        exact field_one_ne_zero hz2.symm
      omega
    have e7 := ObsFn.heap_extends ev7
    have hm := ih.get (.nat .klimbs_mul) (by nat_lt_calls) ev8 a _ rfl
      (good.sub fun x hx => by simp [hx]) n _
      (repLimbs_mono (ext0.trans (e3.trans (e4.trans (e5.trans (e6.trans e7))))) ha)
      (repLimbs_mono e7 hp)
    rwa [pow_odd hm2] at hm

/-- `klimbs_shl(a, n)`: `a * 2^n`. -/
theorem klimbs_shl_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_shl" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_shl c args h r h' calls := by
  intro a b hargs good n m ha hb
  subst hargs
  obtain ⟨m2, m83, cs98, v102, m111, cs119, rfl, rfl, ev1, ev2, hc⟩ :=
    Obs.«KernelKlimbs::klimbs_shl».obs ev
  subst hc
  obtain ⟨w2, hw2, hr2⟩ := word_two h
  have ext0 : Heap.Extends h ((h ++ [.construct limbListEnum "Nil" []]) ++
      [.construct limbListEnum "Cons" [.tuple [.field 2, .field 0, .field 0, .field 0, .field 0,
        .field 0, .field 0, .field 0], .ptr (.enum limbListEnum) h.length]]) :=
    (Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)
  have hp := ih.get (.nat .klimbs_pow) (by nat_lt_calls) ev1 _ b rfl
    (good.sub fun x hx => by simp [hx]) 2 m
    ⟨[w2], lrep_store_cons hr2 (lrep_store_nil h), by simp [limbsVal_cons, limbsVal_nil, hw2]⟩
    (repLimbs_mono ext0 hb)
  have hm := ih.get (.nat .klimbs_mul) (by nat_lt_calls) ev2 a _ rfl
    (good.sub fun x hx => by simp [hx]) n (2 ^ m)
    (repLimbs_mono (ext0.trans (ObsFn.heap_extends ev1)) ha) hp
  rw [← Nat.shiftLeft_eq] at hm
  exact hm

/-- `klimbs_shr(a, n)`: `a / 2^n`. -/
theorem klimbs_shr_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_shr" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_shr c args h r h' calls := by
  intro a b hargs good n m ha hb
  subst hargs
  obtain ⟨m2, m83, cs98, v102, m111, cs119, rfl, rfl, ev1, ev2, hc⟩ :=
    Obs.«KernelKlimbs::klimbs_shr».obs ev
  subst hc
  obtain ⟨w2, hw2, hr2⟩ := word_two h
  have ext0 : Heap.Extends h ((h ++ [.construct limbListEnum "Nil" []]) ++
      [.construct limbListEnum "Cons" [.tuple [.field 2, .field 0, .field 0, .field 0, .field 0,
        .field 0, .field 0, .field 0], .ptr (.enum limbListEnum) h.length]]) :=
    (Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)
  have hp := ih.get (.nat .klimbs_pow) (by nat_lt_calls) ev1 _ b rfl
    (good.sub fun x hx => by simp [hx]) 2 m
    ⟨[w2], lrep_store_cons hr2 (lrep_store_nil h), by simp [limbsVal_cons, limbsVal_nil, hw2]⟩
    (repLimbs_mono ext0 hb)
  have hd := ih.get (.nat .klimbs_div) (by nat_lt_calls) ev2 a _ rfl
    (good.sub fun x hx => by simp [hx]) n (2 ^ m)
    (repLimbs_mono (ext0.trans (ObsFn.heap_extends ev1)) ha) hp
  rw [← Nat.shiftRight_eq_div_pow] at hd
  exact RepLimbsC.toRepLimbs hd

/-! ## The division helpers (`IxVMCompat`) -/

/-- `IxVMCompat::divide_grow(a, b)` at a nonzero divisor: `(a / b, a % b)`. -/
theorem divide_grow_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "IxVMCompat::divide_grow" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.divide_grow c args h r h' calls := by
  intro a b hargs good n m ha hb hm
  subst hargs
  rcases Obs.«IxVMCompat::divide_grow».obs ev with
    ⟨m2, cs13, m42, ev1, rfl, rfl, rfl, hc⟩ |
    ⟨v1, m2, cs13, m68, cs78, v82, m91, cs99, x_q, x_r, v131, m132, cs142, m162, cs173,
      ev1, hne, ev2, ev3, ev4, ev5, rfl, rfl, hc⟩ |
    ⟨v1, m2, cs13, m68, cs78, v82, m91, cs99, x_q, x_r, v131, m132, cs142, v161, m162, cs173,
      v223, v224, m227, cs235, m247, cs255, ev1, hne, ev2, ev3, ev4, ev5, hne2, rfl, ev6, ev7,
      rfl, hc⟩
  · -- `b > a`: `(0, a)`
    subst hc
    have hle := ih.get (.nat .klimbs_le) (by nat_lt_calls) ev1 b a rfl
      (good.sub fun x hx => by simp [hx]) m n hb ha
    have hlt : n < m := by
      by_contra hge
      rw [ite_eq_left (by omega)] at hle
      exact field_one_ne_zero hle.symm
    refine ⟨_, _, rfl, ⟨[], lrep_store_nil m2, ?_⟩, ?_⟩
    · simp [Nat.div_eq_of_lt hlt, limbsVal_nil]
    · rw [Nat.mod_eq_of_lt hlt]
      exact repLimbs_mono ((ObsFn.heap_extends ev1).trans (Heap.Extends.snoc _ _)) ha
  all_goals
    subst hc
    have hle := ih.get (.nat .klimbs_le) (by nat_lt_calls) ev1 b a rfl
      (good.sub fun x hx => by simp [hx]) m n hb ha
    have e1 := ObsFn.heap_extends ev1
    have h2m := ih.get (.nat .klimbs_add) (by nat_lt_calls) ev2 b b rfl
      (good.sub fun x hx => by simp [hx]) m m (repLimbs_mono e1 hb) (repLimbs_mono e1 hb)
    have e2 := ObsFn.heap_extends ev2
    obtain ⟨q, rr, hpair, hq, hrr⟩ := ih.get (.nat .divide_grow) (by nat_lt_calls) ev3 a _ rfl
      (good.sub fun x hx => by simp [hx]) n (m + m) (repLimbs_mono (e1.trans e2) ha) h2m
      (by omega)
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    have e3 := ObsFn.heap_extends ev3
    have h2q := ih.get (.nat .klimbs_add) (by nat_lt_calls) ev4 _ _ rfl
      (good.sub fun x hx => by simp [hx]) _ _ hq hq
    have e4 := ObsFn.heap_extends ev4
    have hle2 := ih.get (.nat .klimbs_le) (by nat_lt_calls) ev5 b _ rfl
      (good.sub fun x hx => by simp [hx]) m _
      (repLimbs_mono (e1.trans (e2.trans (e3.trans e4))) hb) (repLimbs_mono e4 hrr)
    have hdd := div_mod_double (n := n) hm
  · -- the remainder by `2b` is below `b`
    have hlt : n % (m + m) < m := by
      by_contra hge
      rw [ite_eq_left (by omega)] at hle2
      exact field_one_ne_zero hle2.symm
    obtain ⟨hq', hr'⟩ := hdd.1 hlt
    refine ⟨_, _, rfl, ?_, ?_⟩
    · rw [hq']; exact repLimbs_mono (ObsFn.heap_extends ev5) h2q
    · rw [hr']; exact repLimbs_mono (e4.trans (ObsFn.heap_extends ev5)) hrr
  · -- the remainder by `2b` is at least `b`
    have hge : m ≤ n % (m + m) := by
      by_contra hlt
      rw [ite_eq_right (by omega)] at hle2
      exact hne2 hle2
    obtain ⟨hq', hr'⟩ := hdd.2 hge
    have e5 := ObsFn.heap_extends ev5
    have hs := (ih.get (.nat .klimbs_succ) (by nat_lt_calls) ev6 _ rfl
      (good.sub fun x hx => by simp [hx]) _).1 (repLimbs_mono e5 h2q)
    have e6 := ObsFn.heap_extends ev6
    have hd := ih.get (.nat .klimbs_sub) (by nat_lt_calls) ev7 _ _ rfl
      (good.sub fun x hx => by simp [hx]) _ m
      (repLimbs_mono (e4.trans (e5.trans e6)) hrr)
      (repLimbs_mono (e1.trans (e2.trans (e3.trans (e4.trans (e5.trans e6))))) hb)
    refine ⟨_, _, rfl, ?_, ?_⟩
    · rw [hq']; exact repLimbs_mono (ObsFn.heap_extends ev7) hs
    · rw [hr']; exact RepLimbsC.toRepLimbs hd

/-- `IxVMCompat::ordinary_div_mod(a, b)`: `(a / b, a % b)`, `(0, a)` at `b = 0`. -/
theorem ordinary_div_mod_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "IxVMCompat::ordinary_div_mod" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.ordinary_div_mod c args h r h' calls := by
  intro a b hargs good n m ha hb
  subst hargs
  rcases Obs.«IxVMCompat::ordinary_div_mod».obs ev with
    ⟨v1, m2, cs12, v23, m24, cs34, m46, cs57, m78, ev1, ev2, ev3, rfl, rfl, rfl, hc⟩ |
    ⟨v1, m2, cs12, v23, m24, cs34, v45, m46, cs57, cs106, ev1, ev2, ev3, hne, ev4, hc⟩
  · subst hc
    have hna := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev1 a rfl
      (good.sub fun x hx => by simp [hx]) n ha
    have e1 := ObsFn.heap_extends ev1
    have hnb := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev2 b rfl
      (good.sub fun x hx => by simp [hx]) m (repLimbs_mono e1 hb)
    have e2 := ObsFn.heap_extends ev2
    have hz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev3 _ rfl
      (good.sub fun x hx => by simp [hx]) m (RepLimbsC.toRepLimbs hnb)
    have hm0 : m = 0 := by
      by_contra hne
      rw [ite_eq_right hne] at hz
      exact field_one_ne_zero hz
    have e3 := ObsFn.heap_extends ev3
    refine ⟨_, _, rfl, ⟨[], lrep_store_nil m46, ?_⟩, ?_⟩
    · simp [hm0, limbsVal_nil]
    · rw [hm0, Nat.mod_zero]
      exact repLimbs_mono (e2.trans (e3.trans (Heap.Extends.snoc _ _))) (RepLimbsC.toRepLimbs hna)
  · subst hc
    have hna := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev1 a rfl
      (good.sub fun x hx => by simp [hx]) n ha
    have e1 := ObsFn.heap_extends ev1
    have hnb := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev2 b rfl
      (good.sub fun x hx => by simp [hx]) m (repLimbs_mono e1 hb)
    have e2 := ObsFn.heap_extends ev2
    have hz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev3 _ rfl
      (good.sub fun x hx => by simp [hx]) m (RepLimbsC.toRepLimbs hnb)
    have hm0 : m ≠ 0 := by
      intro h0
      rw [ite_eq_left h0] at hz
      exact hne hz
    have e3 := ObsFn.heap_extends ev3
    exact ih.get (.nat .divide_grow) (by nat_lt_calls) ev4 _ _ rfl
      (good.sub fun x hx => by simp [hx]) n m
      (repLimbs_mono (e2.trans e3) (RepLimbsC.toRepLimbs hna))
      (repLimbs_mono e3 (RepLimbsC.toRepLimbs hnb)) (by omega)

/-! ## `klimbs_mul_single` -/

/-- `klimbs_mul_single(a_limb, b, carry)`: `a_limb * b + carry`. The high word of each limb
product plus a carry never wraps (`x * z / 2^64 ≤ 2^64 - 2`). -/
theorem klimbs_mul_single_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelKlimbs::klimbs_mul_single" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_mul_single c args h r h' calls := by
  rintro al b cr hargs good x y m hx hy ⟨lb, hlb, rfl⟩
  subst hargs
  rcases Obs.«KernelKlimbs::klimbs_mul_single».obs ev with
    ⟨m21, cs32, ld, ev1, rfl, rfl, -⟩ |
    ⟨m21, cs32, m79, ld, ev1, rfl, rfl, rfl, -⟩ |
    ⟨x_b_limb, x_rest, m111, cs122, x_lo, x_hi, m158, cs169, x_sum, x_carry_out, m205, cs216,
      v240, m249, cs257, ld, ev1, ev2, ev3, rfl, rfl, ev4, hc⟩ |
    ⟨x_b_limb, x_rest, m111, cs122, x_lo, x_hi, m158, cs169, x_sum, x_carry_out, v204, m205,
      cs216, v298, m307, cs315, v320, m336, cs344, ld, ev1, ev2, ev3, hne, rfl, rfl, ev4, ev5, hc⟩
  · -- no limb left, no carry: `Nil`
    obtain rfl := lrep_nil_of_load hlb ld
    obtain ⟨hz, -⟩ := is_zero_word hy ev1
    have hy0 : y.toNat = 0 := by
      by_contra hne
      rw [ite_eq_right hne] at hz
      exact field_one_ne_zero hz
    exact ⟨[], lrep_store_nil m21, by simp [limbsVal_nil, hy0]⟩
  · -- no limb left, a carry: the carry alone
    obtain rfl := lrep_nil_of_load hlb ld
    exact ⟨[y], lrep_store_cons hy (lrep_store_nil m21), by simp [limbsVal_cons, limbsVal_nil]⟩
  · -- a limb, no carry out of the low word
    obtain ⟨z, lb0, rfl, hz, hlb0⟩ := lrep_cons_of_load hlb ld
    obtain ⟨hmul, hm1⟩ := NatLib.u64_mul_spec hx hz ev1
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hmul
    obtain ⟨rfl, rfl⟩ := hmul
    rw [hm1] at ev2
    have hxb := toNat_lt x
    have hzb := toNat_lt z
    have hyb := toNat_lt y
    obtain ⟨wl, hwl, hrl⟩ := word_of h (Nat.mod_lt (x.toNat * z.toNat) (by decide))
    obtain ⟨rfl, rfl, rfl⟩ := add_words hrl hy ev2
    obtain ⟨hcy, rfl⟩ := to_field ev3
    have hwlb := toNat_lt wl
    have hlt : wl.toNat + y.toNat < B64 := (carry_zero_iff (by omega)).mp (field_inj hcy)
    have hPB : x.toNat * z.toNat / B64 < B64 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      nlinarith
    obtain ⟨wh, hwh, hrh⟩ := word_of h hPB
    subst hc
    obtain ⟨ls', hl', hv'⟩ := ih.get (.nat .klimbs_mul_single) (by nat_lt_calls) ev4 _ _ _ rfl
      (good.sub fun x hx => by simp [hx]) x wh (limbsVal lb0) hx hrh ⟨lb0, hlb0, rfl⟩
    obtain ⟨ws, hws, hrs⟩ := word_of h (Nat.mod_lt (wl.toNat + y.toNat) (by decide))
    refine ⟨ws :: ls', lrep_store_cons hrs hl', ?_⟩
    rw [limbsVal_cons, limbsVal_cons, hv', hws, Nat.mod_eq_of_lt hlt, hwl, hwh]
    nlinarith [Nat.mod_add_div (x.toNat * z.toNat) B64]
  · -- a limb, a carry out of the low word: the high word is incremented
    obtain ⟨z, lb0, rfl, hz, hlb0⟩ := lrep_cons_of_load hlb ld
    obtain ⟨hmul, hm1⟩ := NatLib.u64_mul_spec hx hz ev1
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hmul
    obtain ⟨rfl, rfl⟩ := hmul
    rw [hm1] at ev2
    have hxb := toNat_lt x
    have hzb := toNat_lt z
    have hyb := toNat_lt y
    obtain ⟨wl, hwl, hrl⟩ := word_of h (Nat.mod_lt (x.toNat * z.toNat) (by decide))
    obtain ⟨rfl, rfl, rfl⟩ := add_words hrl hy ev2
    obtain ⟨rfl, rfl⟩ := to_field ev3
    have hwlb := toNat_lt wl
    have hge : B64 ≤ wl.toNat + y.toNat := by
      by_contra hlt
      exact hne (by rw [(carry_zero_iff (by omega)).mpr (by omega)])
    have hPB : x.toNat * z.toNat / B64 + 1 < B64 := by
      have hle : x.toNat * z.toNat ≤ (B64 - 1) * (B64 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h1 := Nat.div_le_div_right (c := B64) hle
      have e : (B64 - 1) * (B64 - 1) / B64 = B64 - 2 := by norm_num
      omega
    obtain ⟨wh, hwh, hrh⟩ := word_of h (show x.toNat * z.toNat / B64 < B64 by omega)
    obtain ⟨rfl, hm2⟩ := Lib.u64_wrapping_succ_spec hrh ev4
    rw [hm2] at ev5
    obtain ⟨wh1, hwh1, hrh1⟩ := word_of h (Nat.mod_lt (wh.toNat + 1) (by decide))
    subst hc
    obtain ⟨ls', hl', hv'⟩ := ih.get (.nat .klimbs_mul_single) (by nat_lt_calls) ev5 _ _ _ rfl
      (good.sub fun x hx => by simp [hx]) x wh1 (limbsVal lb0) hx hrh1 ⟨lb0, hlb0, rfl⟩
    obtain ⟨ws, hws, hrs⟩ := word_of h (Nat.mod_lt (wl.toNat + y.toNat) (by decide))
    have hm_ws : (wl.toNat + y.toNat) % B64 = wl.toNat + y.toNat - B64 := by omega
    have hm_wh : (wh.toNat + 1) % B64 = wh.toNat + 1 := Nat.mod_eq_of_lt (by omega)
    refine ⟨ws :: ls', lrep_store_cons hrs hl', ?_⟩
    rw [limbsVal_cons, limbsVal_cons, hv', hws, hm_ws, hwh1, hm_wh, hwh]
    have h2 : wl.toNat + y.toNat - B64 + B64 = wl.toNat + y.toNat := Nat.sub_add_cancel hge
    nlinarith [Nat.mod_add_div (x.toNat * z.toNat) B64]

end IxVM.Refinement.Core
