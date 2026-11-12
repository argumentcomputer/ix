import IxVMRefinement.Obs.KernelLevels
import IxVMRefinement.Core.Obs
import Ix.IxVM.Refinement.LevelsObs
import Ix.IxVM.Consistency.Statement
import Mathlib.Data.List.Forall2

/-! # The level comparisons over observed, bounded derivations

`Ix.IxVM.Refinement.KernelLevels` proves `level_leq` and `level_equal` against the pure
`levelLeq`, `levelEqual` over the unbounded semantics (`EvalFn`), under the hypothesis that
the offsets the normalizer reaches stay below `OB` (`levelSucc l < OB`). This module removes
that hypothesis for observed derivations with at most `2^39` distinct calls of each memoized
callee (the consistency statement's `Bounded`).

**Where the bound comes from.** Not from the comparisons alone. Every
`UInt32::less_than_fields` bounds the two values it compares by `2^32` itself
(`u32LessThanFields_bounded`), but the normalizer's running offset `k` is a field element
incremented once per successor, and some offsets are never compared: `normalize_aux` on
`zero` at an offset `k ≡ 0` returns its accumulator without any comparison, so `succ^p zero`
(with `p` the characteristic) would normalize as `zero`. What excludes it is the memo bound:
the `normalize_aux` calls along a path carry the offsets `k, k + 1, k + 2, …` as their third
argument, distinct field elements, so reaching the offset `n` takes `n + 1` distinct calls of
the memoized `normalize_aux` (`normalize_chain`, `chain_lt`). Field arguments are
represented by themselves, so this needs no ROM validity.

**What this gives.** `levelLeq_obs` and `levelEqual_obs`: on represented levels, a bounded
observed derivation answers `levelLeq` and `levelEqual`, with no other hypothesis. -/

namespace IxVM.Refinement.Levels

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.KernelLevels
open IxVM.Consistency (MemoCallsAtMost memoCall)

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- Membership of a call in a concatenation of call lists. -/
macro "chainsub" : tactic =>
  `(tactic| first
    | (intro x hx; simp only [List.mem_cons, List.mem_append] at hx ⊢; tauto)
    | (intro x hx; simp only [List.mem_cons, List.mem_append]; tauto))

/-! ## Reading a level node -/

theorem load_klevel {h : Heap F} {addr : Nat} {c c' : String} {xs xs' : List (SourceValue F)}
    (cell : h[addr]? = some (.construct klevelEnum c xs))
    (ld : loadValue h (.ptr (.enum klevelEnum) addr) =
      .ok (.construct "KernelTypes::KLevelNode" c' xs')) :
    c = c' ∧ xs = xs' := by
  rw [loadValue_enum_cell cell] at ld
  injection ld with hv
  injection hv with _ hc hx
  exact ⟨hc, hx⟩

theorem rep_zero_of_load {h : Heap F} {l : Ix.Kernel.Level} {p : SourceValue F}
    (rep : RepKLevel h l p)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "Zero" [])) : l = .zero := by
  cases rep with
  | zero _ => rfl
  | succ cell _ | max cell _ _ | imax cell _ _ | param _ cell =>
    exact absurd (load_klevel cell ld).1 (by decide)

theorem rep_succ_of_load {h : Heap F} {l : Ix.Kernel.Level} {p x : SourceValue F}
    (rep : RepKLevel h l p)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "Succ" [x])) :
    ∃ u, l = .succ u ∧ RepKLevel h u x := by
  cases rep with
  | succ cell ih =>
    obtain ⟨-, hx⟩ := load_klevel cell ld
    injection hx with hx _
    subst hx
    exact ⟨_, rfl, ih⟩
  | zero cell | max cell _ _ | imax cell _ _ | param _ cell =>
    exact absurd (load_klevel cell ld).1 (by decide)

theorem rep_max_of_load {h : Heap F} {l : Ix.Kernel.Level} {p x y : SourceValue F}
    (rep : RepKLevel h l p)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "Max" [x, y])) :
    ∃ u v, l = .max u v ∧ RepKLevel h u x ∧ RepKLevel h v y := by
  cases rep with
  | max cell ihu ihv =>
    obtain ⟨-, hx⟩ := load_klevel cell ld
    injection hx with hx hy
    injection hy with hy _
    subst hx hy
    exact ⟨_, _, rfl, ihu, ihv⟩
  | zero cell | succ cell _ | imax cell _ _ | param _ cell =>
    exact absurd (load_klevel cell ld).1 (by decide)

theorem rep_imax_of_load {h : Heap F} {l : Ix.Kernel.Level} {p x y : SourceValue F}
    (rep : RepKLevel h l p)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "IMax" [x, y])) :
    ∃ u v, l = .imax u v ∧ RepKLevel h u x ∧ RepKLevel h v y := by
  cases rep with
  | imax cell ihu ihv =>
    obtain ⟨-, hx⟩ := load_klevel cell ld
    injection hx with hx hy
    injection hy with hy _
    subst hx hy
    exact ⟨_, _, rfl, ihu, ihv⟩
  | zero cell | succ cell _ | max cell _ _ | param _ cell =>
    exact absurd (load_klevel cell ld).1 (by decide)

theorem rep_param_of_load {h : Heap F} {l : Ix.Kernel.Level} {p x : SourceValue F}
    (rep : RepKLevel h l p)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "Param" [x])) :
    ∃ n, l = .param n := by
  cases rep with
  | param _ _ => exact ⟨_, rfl⟩
  | zero cell | succ cell _ | max cell _ _ | imax cell _ _ =>
    exact absurd (load_klevel cell ld).1 (by decide)

theorem evalBinOp_add_field {a b : F} {r : SourceValue F}
    (h : evalBinOp .add (.field a : SourceValue F) (.field b) = .ok r) : r = .field (a + b) := by
  have hv : evalBinOp .add (.field a : SourceValue F) (.field b) = .ok (.field (a + b)) := rfl
  rw [hv] at h
  injection h with h
  exact h.symm

/-! ## Chains of `normalize_aux` calls -/

/-- **Calls of `normalize_aux` at the offsets `k + j`, for `lo ≤ j ≤ n`**, among `cs`. -/
def AuxChain (cs : List (Call F)) (k : F) (lo n : Nat) : Prop :=
  ∀ j, lo ≤ j → j ≤ n → ∃ c ∈ cs, c.name = "KernelLevels::normalize_aux" ∧
    ∃ x y z : SourceValue F, c.args = [x, y, .field (k + (j : F)), z]

theorem AuxChain.mono {cs cs' : List (Call F)} {k : F} {lo n : Nat}
    (hc : AuxChain cs k lo n) (hsub : ∀ x ∈ cs, x ∈ cs') : AuxChain cs' k lo n :=
  fun j h1 h2 =>
    let ⟨c, hmem, rest⟩ := hc j h1 h2
    ⟨c, hsub c hmem, rest⟩

theorem AuxChain.lo_mono {cs : List (Call F)} {k : F} {lo lo' n : Nat}
    (hc : AuxChain cs k lo n) (hlo : lo ≤ lo') : AuxChain cs k lo' n :=
  fun j h1 h2 => hc j (Nat.le_trans hlo h1) h2

theorem AuxChain.empty {cs : List (Call F)} {k : F} {lo n : Nat} (hn : n < lo) :
    AuxChain cs k lo n :=
  fun j h1 h2 => absurd (Nat.lt_of_le_of_lt h2 hn) (Nat.not_lt.mpr h1)

theorem AuxChain.max {cs : List (Call F)} {k : F} {lo n₁ n₂ : Nat}
    (h₁ : AuxChain cs k lo n₁) (h₂ : AuxChain cs k lo n₂) :
    AuxChain cs k lo (Max.max n₁ n₂) := by
  intro j hlo hj
  by_cases hj1 : j ≤ n₁
  · exact h₁ j hlo hj1
  · exact h₂ j hlo (by omega)

theorem AuxChain.shift {cs : List (Call F)} {k : F} {n : Nat}
    (hc : AuxChain cs (k + 1) 0 n) : AuxChain cs k 1 (n + 1) := by
  intro j hlo hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  obtain ⟨c, hmem, hn, x, y, z, hargs⟩ := hc i (Nat.zero_le _) (by omega)
  refine ⟨c, hmem, hn, x, y, z, ?_⟩
  rw [hargs]
  have : k + 1 + (i : F) = k + ((i + 1 : Nat) : F) := by push_cast; ring
  rw [this]

theorem AuxChain.self {ptr path acc : SourceValue F} {h : Heap F} {cs : List (Call F)} {k : F} :
    AuxChain ((⟨"KernelLevels::normalize_aux", [ptr, path, .field k, acc], h⟩ : Call F) :: cs)
      k 0 0 := by
  intro j _ hj
  obtain rfl : j = 0 := by omega
  exact ⟨_, List.mem_cons_self .., rfl, ptr, path, acc, by simp⟩

theorem AuxChain.cons_self {ptr path acc : SourceValue F} {h : Heap F} {cs : List (Call F)}
    {k : F} {n : Nat} (hc : AuxChain cs k 1 n) :
    AuxChain ((⟨"KernelLevels::normalize_aux", [ptr, path, .field k, acc], h⟩ : Call F) :: cs)
      k 0 n := by
  intro j hlo hj
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · exact AuxChain.self 0 (Nat.le_refl _) (Nat.le_refl _)
  · obtain ⟨c, hmem, rest⟩ := hc j hpos hj
    exact ⟨c, List.mem_cons_of_mem _ hmem, rest⟩

/-- **The `normalize_aux` calls of a normalization reach every offset up to `normArgSucc`.**
For `normalize_aux(l, path, k, acc)`, the call itself and its calls carry the offsets
`k + j` for every `j ≤ normArgSucc fuel (.inl l)`; for `normalize_imax_dispatch(a, b, …)`,
its calls carry `k + j` for every `1 ≤ j ≤ normArgSucc fuel (.inr (a, b))` (offset `k` is
carried by the caller). The fuel is the model's; the statement holds at every fuel. -/
theorem normalize_chain (fuel : Nat) :
    ∀ (arg : Sum Ix.Kernel.Level (Ix.Kernel.Level × Ix.Kernel.Level)) {h h' : Heap F}
      {path acc r : SourceValue F} {k : F} {cs : List (Call F)},
      (match arg with
       | .inl l => ∀ {ptrL : SourceValue F}, RepKLevel h l ptrL →
           ObsFn IxVM.source.world "KernelLevels::normalize_aux" [ptrL, path, .field k, acc]
             h r h' cs →
           AuxChain ((⟨"KernelLevels::normalize_aux", [ptrL, path, .field k, acc], h⟩ : Call F)
             :: cs) k 0 (normArgSucc fuel (.inl l))
       | .inr (a, b) => ∀ {ptrA ptrB : SourceValue F}, RepKLevel h a ptrA →
           RepKLevel h b ptrB →
           ObsFn IxVM.source.world "KernelLevels::normalize_imax_dispatch"
             [ptrA, ptrB, path, .field k, acc] h r h' cs →
           AuxChain cs k 1 (normArgSucc fuel (.inr (a, b)))) := by
  induction fuel with
  | zero =>
    intro arg h h' path acc r k cs
    rcases arg with l | ⟨a, b⟩
    · intro ptrL _ _
      simp only [normArgSucc]
      exact AuxChain.self
    · intro ptrA ptrB _ _ _
      simp only [normArgSucc]
      exact AuxChain.empty (by omega)
  | succ fuel ih =>
    intro arg h h' path acc r k cs
    rcases arg with l | ⟨a, b⟩
    · intro ptrL repL ev
      cases Obs.«KernelLevels::normalize_aux».obs ev with
      | Zero cs23 ld ev25 hc =>
        obtain rfl := rep_zero_of_load repL ld
        simp only [normArgSucc]
        exact AuxChain.self
      | Succ x_inner cs66 v71 ld op ev68 hc =>
        obtain ⟨u, rfl, hu⟩ := rep_succ_of_load repL ld
        obtain rfl := evalBinOp_add_field op
        subst hc
        simp only [normArgSucc]
        exact AuxChain.cons_self (AuxChain.shift (ih (.inl u) hu ev68))
      | Max x_a x_b cs130 v136 m159 cs167 ld ev169 ev132 hc =>
        obtain ⟨u, v, rfl, hu, hv⟩ := rep_max_of_load repL ld
        subst hc
        have hA := ih (.inl u) hu ev169
        have hB := ih (.inl v) (hv.mono ev169.heap_extends) ev132
        simp only [normArgSucc]
        exact AuxChain.max (hA.mono (by chainsub)) (hB.mono (by chainsub))
      | IMax x_u x_b cs223 ld ev225 hc =>
        obtain ⟨u, b, rfl, hu, hb⟩ := rep_imax_of_load repL ld
        subst hc
        have hD := ih (.inr (u, b)) hu hb ev225
        simp only [normArgSucc]
        exact AuxChain.cons_self (hD.mono (by chainsub))
      | Param_n1_bind _ _ _ _ _ _ _ _ ld =>
        obtain ⟨n, rfl⟩ := rep_param_of_load repL ld
        simp only [normArgSucc]
        exact AuxChain.self
      | Param_n0_other_n0 _ _ _ _ ld =>
        obtain ⟨n, rfl⟩ := rep_param_of_load repL ld
        simp only [normArgSucc]
        exact AuxChain.self
      | Param_n0_other_other _ _ _ _ _ ld =>
        obtain ⟨n, rfl⟩ := rep_param_of_load repL ld
        simp only [normArgSucc]
        exact AuxChain.self
    · intro ptrA ptrB repA repB ev
      cases Obs.«KernelLevels::normalize_imax_dispatch».obs ev with
      | Zero cs23 ld ev25 hc =>
        obtain rfl := rep_zero_of_load repB ld
        simp only [normArgSucc]
        exact AuxChain.empty (by omega)
      | Succ x_v cs66 v71 v72 m103 cs111 ld op ev113 ev68 hc =>
        obtain ⟨v, rfl, hv⟩ := rep_succ_of_load repB ld
        obtain rfl := evalBinOp_add_field op
        subst hc
        have hA := ih (.inl a) repA ev113
        have hV := ih (.inl v) (hv.mono ev113.heap_extends) ev68
        simp only [normArgSucc]
        exact AuxChain.max ((hA.lo_mono (by omega)).mono (by chainsub))
          ((AuxChain.shift hV).mono (by chainsub))
      | Max x_v x_w cs167 v174 m204 cs212 ld ev214 ev169 hc =>
        obtain ⟨v, w, rfl, hv, hw⟩ := rep_max_of_load repB ld
        subst hc
        have ext := ev214.heap_extends
        have h1 := ih (.inr (a, v)) repA hv ev214
        have h2 := ih (.inr (a, w)) (repA.mono ext) (hw.mono ext) ev169
        simp only [normArgSucc]
        exact AuxChain.max (h1.mono (by chainsub)) (h2.mono (by chainsub))
      | IMax x_v x_w cs276 v283 m313 cs321 ld ev323 ev278 hc =>
        obtain ⟨v, w, rfl, hv, hw⟩ := rep_imax_of_load repB ld
        subst hc
        have ext := ev323.heap_extends
        have h1 := ih (.inr (a, w)) repA hw ev323
        have h2 := ih (.inr (v, w)) (hv.mono ext) (hw.mono ext) ev278
        simp only [normArgSucc]
        exact AuxChain.max (h2.mono (by chainsub)) (h1.mono (by chainsub))
      | Param_n1_bind x_idx m378 cs389 x_new_path cs429 v435 m458 cs466 v469 m474 cs482 ld
          ev391 ev484 ev468 ev431 hc =>
        obtain ⟨n, rfl⟩ := rep_param_of_load repB ld
        subst hc
        have ext := (ev391.heap_extends.trans ev484.heap_extends).trans ev468.heap_extends
        have hA := ih (.inl a) (repA.mono ext) ev431
        simp only [normArgSucc]
        exact (hA.lo_mono (by omega)).mono (by chainsub)
      | Param_n0_other x_idx m378 cs389 w538 v611 m612 cs614 cs623 ld ev391 sg ev625 hc =>
        obtain ⟨n, rfl⟩ := rep_param_of_load repB ld
        subst hc
        have ext2 : Heap.Extends m378 m612 := by
          cases sg with
          | n0 _ _ he _ =>
            subst he
            exact Heap.Extends.refl _
          | other _ _ ev577 _ => exact ev577.heap_extends
        have hA := ih (.inl a) (repA.mono (ev391.heap_extends.trans ext2)) ev625
        simp only [normArgSucc]
        exact (hA.lo_mono (by omega)).mono (by chainsub)

/-! ## Distinct offsets need distinct keys -/

/-- `normalize_aux` is memoized: the compiler keeps it as a function with memo rows. -/
theorem aux_memoized : memoCall IxVM.source "KernelLevels::normalize_aux" = true := by
  decide +kernel

theorem represents_field_inv {rom : ROM F} {h : Heap F} {x : F} {w : Value F}
    (r : Represents rom h (.field x) w) : w = .field x := by
  generalize hp : (Value.field x : SourceValue F) = p at r
  cases r with
  | field =>
    injection hp with hx
    rw [hx]
  | tuple _ => cases hp
  | construct _ => cases hp
  | ptr _ _ _ => cases hp

theorem forall₂_four {α β : Type} {R : α → β → Prop} {a b c d : α} {ws : List β}
    (h : List.Forall₂ R [a, b, c, d] ws) :
    ∃ wa wb wc wd, ws = [wa, wb, wc, wd] ∧ R a wa ∧ R b wb ∧ R c wc ∧ R d wd := by
  obtain ⟨wa, u1, ha, h1, rfl⟩ := List.forall₂_cons_left_iff.mp h
  obtain ⟨wb, u2, hb, h2, rfl⟩ := List.forall₂_cons_left_iff.mp h1
  obtain ⟨wc, u3, hc, h3, rfl⟩ := List.forall₂_cons_left_iff.mp h2
  obtain ⟨wd, u4, hd, h4, rfl⟩ := List.forall₂_cons_left_iff.mp h3
  rw [List.forall₂_nil_left_iff] at h4
  subst h4
  exact ⟨wa, wb, wc, wd, rfl, ha, hb, hc, hd⟩

/-- **A chain of `normalize_aux` offsets from `0` is shorter than the memo bound.** The
calls at offsets `0, 1, …, n` have pairwise different third arguments (distinct field
elements below the characteristic), and a field argument is represented by itself, so they
need `n + 1` distinct keys of the memoized `normalize_aux`. -/
theorem chain_lt {rom : ROM F} {calls : List (Call F)}
    (bound : MemoCallsAtMost IxVM.source rom calls (2 ^ 39)) {n : Nat}
    (chain : AuxChain calls 0 0 n) : n < 2 ^ 39 := by
  by_contra hlt
  have hge : 2 ^ 39 ≤ n := Nat.le_of_not_lt hlt
  obtain ⟨keys, hlen, cover⟩ := bound "KernelLevels::normalize_aux" aux_memoized
  have pick : ∀ j : Fin (2 ^ 39 + 1), ∃ key ∈ keys, ∃ wx wy wz : Value F,
      key = [wx, wy, .field (((j : Nat) : F)), wz] := by
    intro j
    have hj := j.isLt
    obtain ⟨c, hc, hn, x, y, z, hargs⟩ := chain j (Nat.zero_le _) (by omega)
    obtain ⟨key, hkey, hfa⟩ := cover c hc hn
    rw [hargs] at hfa
    obtain ⟨wx, wy, wf, wz, rfl, -, -, hf, -⟩ := forall₂_four hfa
    refine ⟨_, hkey, wx, wy, wz, ?_⟩
    rw [represents_field_inv hf, zero_add]
  let f : Fin (2 ^ 39 + 1) → List (Value F) := fun j => Classical.choose (pick j)
  have hf : ∀ j, f j ∈ keys ∧ ∃ wx wy wz : Value F, f j = [wx, wy, .field (((j : Nat) : F)), wz] :=
    fun j => Classical.choose_spec (pick j)
  have inj : Function.Injective f := by
    intro j j' heq
    obtain ⟨_, wx, wy, wz, h1⟩ := hf j
    obtain ⟨_, wx', wy', wz', h2⟩ := hf j'
    rw [heq, h2] at h1
    simp only [List.cons.injEq, Value.field.injEq] at h1
    exact Fin.ext (natCast_lt_inj j.isLt j'.isLt h1.2.2.1.symm
      (by norm_num [Aiur.Library.U32.Goldilocks.modulus])
      (by norm_num [Aiur.Library.U32.Goldilocks.modulus]))
  have hnd : ((List.finRange (2 ^ 39 + 1)).map f).Nodup := (List.nodup_finRange _).map inj
  have hsub : (List.finRange (2 ^ 39 + 1)).map f ⊆ keys := by
    intro k hk
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hk
    exact (hf j).1
  have hle := (hnd.subperm hsub).length_le
  simp only [List.length_map, List.length_finRange] at hle
  omega

theorem two_pow_39_lt_OB : 2 ^ 39 < OB := by decide

/-- **`level_normalize(l)` carries a chain up to `levelSucc l`.** -/
theorem levelNormalize_chain {x_l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {l : Ix.Kernel.Level}
    (ev : ObsFn IxVM.source.world "KernelLevels::level_normalize" [x_l] h r h' cs)
    (rep : RepKLevel h l x_l) : AuxChain cs 0 0 (levelSucc l) := by
  cases Obs.«KernelLevels::level_normalize».obs ev with
  | run m2 m19 m35 m54 m67 v79 m80 cs90 m105 cs133 hm12 hm27 hm43 hm62 hm75 hm113 ev92 ev135 hc =>
    subst hc
    have ext : Heap.Extends h m105 := by
      subst hm113 hm12 hm75 hm27 hm62 hm43
      exact (((((Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)).trans
        (Heap.Extends.snoc _ _)).trans (Heap.Extends.snoc _ _)).trans
        (Heap.Extends.snoc _ _)).trans (Heap.Extends.snoc _ _)
    exact (normalize_chain (normFuel (.inl l)) (.inl l) (rep.mono ext) ev92).mono (by chainsub)

/-- **The offsets of a bounded normalization stay below `2^39`.** -/
theorem levelNormalize_succ_lt {x_l r : SourceValue F} {h h' : Heap F} {cs calls : List (Call F)}
    {l : Ix.Kernel.Level}
    (ev : ObsFn IxVM.source.world "KernelLevels::level_normalize" [x_l] h r h' cs)
    (rep : RepKLevel h l x_l) {rom : ROM F}
    (bound : MemoCallsAtMost IxVM.source rom calls (2 ^ 39)) (hsub : ∀ x ∈ cs, x ∈ calls) :
    levelSucc l < OB :=
  lt_trans (chain_lt bound ((levelNormalize_chain ev rep).mono hsub)) two_pow_39_lt_OB

/-! ## `level_leq` and `level_equal` over bounded derivations -/

/-- **`level_leq` answers `levelLeq`** on represented levels, in a bounded derivation. -/
theorem levelLeq_obs {x_a x_b r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {la lb : Ix.Kernel.Level}
    (ev : ObsFn IxVM.source.world "KernelLevels::level_leq" [x_a, x_b] h r h' cs)
    {rom : ROM F} (bound : MemoCallsAtMost IxVM.source rom cs (2 ^ 39))
    (repA : RepKLevel h la x_a) (repB : RepKLevel h lb x_b) :
    r = .field (if levelLeq la lb then 1 else 0) ∧ Heap.Extends h h' := by
  cases Obs.«KernelLevels::level_leq».obs ev with
  | n1 m2 cs13 ev15 he36 he37 hc =>
    obtain ⟨hr, rfl⟩ := levelEq_refines repA repB ev15.erase
    subst he36 he37
    have heq : (la == lb) = true := by
      by_contra hne
      simp [hne] at hr
    exact ⟨by simp [levelLeq, heq], Heap.Extends.refl _⟩
  | n0_Zero m2 cs13 ev15 ld he63 he64 hc =>
    obtain ⟨-, rfl⟩ := levelEq_refines repA repB ev15.erase
    obtain rfl := rep_zero_of_load repA ld
    subst he63 he64
    exact ⟨by simp [levelLeq], Heap.Extends.refl _⟩
  | n0_other m2 cs13 v44 cs73 v76 v77 m79 cs87 m99 cs107 ev15 ld hne66 ev89 ev109 ev75 hc =>
    obtain ⟨hr, rfl⟩ := levelEq_refines repA repB ev15.erase
    have hne : (la == lb) = false := by
      cases hb : (la == lb)
      · rfl
      · simp [hb] at hr
    have hnz : la ≠ .zero := by
      rintro rfl
      cases repA with
      | zero cell =>
        rw [loadValue_enum_cell cell] at ld
        injection ld with hv
        exact hne66 [] rfl hv.symm
    subst hc
    obtain ⟨repNA, ext1⟩ := levelNormalize_refines repA
      (levelNormalize_succ_lt ev89 repA bound (by chainsub)) ev89.erase
    obtain ⟨repNB, ext2⟩ := levelNormalize_refines (repB.mono ext1)
      (levelNormalize_succ_lt ev109 (repB.mono ext1) bound (by chainsub)) ev109.erase
    obtain ⟨hr', rfl⟩ := nlLe_refines (repNA.mono ext2) repNB ev75.erase
    have hlev : levelLeq la lb = nlLe (levelNormalize la) (levelNormalize lb) := by
      cases la with
      | zero => exact absurd rfl hnz
      | _ => simp [levelLeq, hne]
    exact ⟨by rw [hr', hlev], ext1.trans ext2⟩

/-- **`level_equal` answers `levelEqual`** on represented levels, in a bounded derivation. -/
theorem levelEqual_obs {x_a x_b r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {la lb : Ix.Kernel.Level}
    (ev : ObsFn IxVM.source.world "KernelLevels::level_equal" [x_a, x_b] h r h' cs)
    {rom : ROM F} (bound : MemoCallsAtMost IxVM.source rom cs (2 ^ 39))
    (repA : RepKLevel h la x_a) (repB : RepKLevel h lb x_b) :
    r = .field (if levelEqual la lb then 1 else 0) ∧ Heap.Extends h h' := by
  cases Obs.«KernelLevels::level_equal».obs ev with
  | n1 m2 cs13 ev15 he36 he37 hc =>
    obtain ⟨hr, rfl⟩ := levelEq_refines repA repB ev15.erase
    subst he36 he37
    have heq : (la == lb) = true := by
      by_contra hne
      simp [hne] at hr
    exact ⟨by simp [levelEqual, heq], Heap.Extends.refl _⟩
  | n0 m2 cs13 cs47 v50 v51 m53 cs61 m73 cs81 ev15 ev63 ev83 ev49 hc =>
    obtain ⟨hr, rfl⟩ := levelEq_refines repA repB ev15.erase
    have hne : (la == lb) = false := by
      cases hb : (la == lb)
      · rfl
      · simp [hb] at hr
    subst hc
    obtain ⟨repNA, ext1⟩ := levelNormalize_refines repA
      (levelNormalize_succ_lt ev63 repA bound (by chainsub)) ev63.erase
    obtain ⟨repNB, ext2⟩ := levelNormalize_refines (repB.mono ext1)
      (levelNormalize_succ_lt ev83 (repB.mono ext1) bound (by chainsub)) ev83.erase
    obtain ⟨hr', rfl⟩ := nlEq_refines (repNA.mono ext2) repNB ev49.erase
    have hlev : levelEqual la lb = nlEq (levelNormalize la) (levelNormalize lb) := by
      simp [levelEqual, hne]
    exact ⟨by rw [hr', hlev], ext1.trans ext2⟩

end IxVM.Refinement.Levels
