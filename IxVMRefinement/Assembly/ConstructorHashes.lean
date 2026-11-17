import IxVMRefinement.Core.CallHeaps
import IxVMRefinement.Callees.ProjAddr
import IxVMRefinement.Obs.KernelCheck
import Ix.IxVM.Consistency.ReaderFootprint

/-! # Constructor hashes observed during block checking -/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)

private theorem small_field_val {n : Nat} (hn : n < 72057594037927936) : (n : F).val = n :=
  ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)

/-- Every constructor reached by the native block loop has its actual projection wrapper
hashed, including constructors not mentioned by any expression or recursor. -/
theorem native_constructor_hashed (ctx : Core.ScopedCtx)
    {n i j : Nat} {block : Aiur.Library.Bytes.Address}
    (hn : n < 72057594037927936) (hi : i < 72057594037927936) (hj : j < n) :
    ∀ m k : Nat,
      ∀ {rc ty np ni nl bp level safety result : SourceValue F}
        {before after : Heap F} {calls : List (Call F)},
      m + k = n → k ≤ j → Core.RepAddr before block bp →
      ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
        [rc, ty, np, ni, .field (n : F), nl, bp, .field (i : F), level, safety, .field (k : F)]
        before result after calls →
      Hashed calls (Ixon.serConstant
        (IxVM.Consistency.constructorProjection (Core.ixAddr block) i j)) := by
  intro m
  induction m with
  | zero =>
    intro k rc ty np ni nl bp level safety result before after calls hmk hkj hb ev
    omega
  | succ m ih =>
    intro k rc ty np ni nl bp level safety result before after calls hmk hkj hb ev
    have hk : k < n := by omega
    have hkv := small_field_val (Nat.lt_trans hk hn)
    have hnv := small_field_val hn
    have hiv := small_field_val hi
    match Obs.«KernelCheck::check_inductive_shape_ctors».obs ev with
    | .n0 op _ _ _ =>
      simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op
      have heq := congrArg ZMod.val (sub_eq_zero.mp op)
      rw [hnv, hkv] at heq
      omega
    | .other (m716 := hashHeap) (m725 := nextHeap)
        (cs735 := hashCalls) (v778 := nextIndex)
        (ev737 := hashRun) (op862 := add) (ev767 := nextRun) (hc864 := events) .. =>
      by_cases hkj : k = j
      · subst j
        have hmem :
            (⟨"KernelCheck::projection_addr_ctor", [.field (i : F), .field (k : F), bp],
              hashHeap⟩ : Call F) ∈ calls := by rw [events]; simp
        have hext := (ev.call_heap_bounds hmem).1
        have hhash := Core.projection_addr_ctor_hashed ctx hashRun
          (Aiur.Library.Bytes.repAddressRef_heapMono₂ Core.addrTy hext hb)
        have hsub : ∀ cl ∈ hashCalls, cl ∈ calls := by rw [events]; intro cl hc; simp [hc]
        have result := Core.hashed_mono hsub hhash
        simpa only [IxVM.Consistency.constructorProjection, hiv, hkv] using result
      · have hmem :
            (⟨"KernelCheck::check_inductive_shape_ctors",
              [rc, ty, np, ni, .field (n : F), nl, bp, .field (i : F), level, safety, nextIndex],
              nextHeap⟩ : Call F) ∈ calls := by rw [events]; simp
        have hext := (ev.call_heap_bounds hmem).1
        have hnext : nextIndex = .field ((k + 1 : Nat) : F) := by
          simp only [evalBinOp, Except.ok.injEq] at add
          simpa only [Nat.cast_add, Nat.cast_one] using add.symm
        rw [hnext] at nextRun
        have hrest := ih (k + 1) (by omega) (by omega)
          (Aiur.Library.Bytes.repAddressRef_heapMono₂ Core.addrTy hext hb) nextRun
        apply Core.hashed_mono _ hrest
        rw [events]
        intro cl hc
        simp [hc]

/-- The modeled block loop commits the same constructor projection bytes. -/
theorem modeled_constructor_hashed (ctx : Core.ScopedCtx)
    {n i j : Nat} {block : Aiur.Library.Bytes.Address}
    (hn : n < 72057594037927936) (hi : i < 72057594037927936) (hj : j < n) :
    ∀ m k : Nat,
      ∀ {rc np ni nl bp safety result : SourceValue F}
        {before after : Heap F} {calls : List (Call F)},
      m + k = n → k ≤ j → Core.RepAddr before block bp →
      ObsFn Core.W "KernelCheck::check_modeled_ctors"
        [rc, np, ni, .field (n : F), nl, bp, .field (i : F), safety, .field (k : F)]
        before result after calls →
      Hashed calls (Ixon.serConstant
        (IxVM.Consistency.constructorProjection (Core.ixAddr block) i j)) := by
  intro m
  induction m with
  | zero =>
    intro k rc np ni nl bp safety result before after calls hmk hkj hb ev
    omega
  | succ m ih =>
    intro k rc np ni nl bp safety result before after calls hmk hkj hb ev
    have hk : k < n := by omega
    have hkv := small_field_val (Nat.lt_trans hk hn)
    have hnv := small_field_val hn
    have hiv := small_field_val hi
    match Obs.«KernelCheck::check_modeled_ctors».obs ev with
    | .n0 op _ _ _ =>
      simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op
      have heq := congrArg ZMod.val (sub_eq_zero.mp op)
      rw [hnv, hkv] at heq
      omega
    | .other (m430 := hashHeap) (m551 := nextHeap)
        (cs510 := hashCalls) (v599 := nextIndex)
        (ev512 := hashRun) (op669 := add) (ev590 := nextRun) (hc671 := events) .. =>
      by_cases hkj : k = j
      · subst j
        have hmem :
            (⟨"KernelCheck::projection_addr_ctor", [.field (i : F), .field (k : F), bp],
              hashHeap⟩ : Call F) ∈ calls := by rw [events]; simp
        have hext := (ev.call_heap_bounds hmem).1
        have hhash := Core.projection_addr_ctor_hashed ctx hashRun
          (Aiur.Library.Bytes.repAddressRef_heapMono₂ Core.addrTy hext hb)
        have hsub : ∀ cl ∈ hashCalls, cl ∈ calls := by rw [events]; intro cl hc; simp [hc]
        have result := Core.hashed_mono hsub hhash
        simpa only [IxVM.Consistency.constructorProjection, hiv, hkv] using result
      · have hmem :
            (⟨"KernelCheck::check_modeled_ctors",
              [rc, np, ni, .field (n : F), nl, bp, .field (i : F), safety, nextIndex],
              nextHeap⟩ : Call F) ∈ calls := by rw [events]; simp
        have hext := (ev.call_heap_bounds hmem).1
        have hnext : nextIndex = .field ((k + 1 : Nat) : F) := by
          simp only [evalBinOp, Except.ok.injEq] at add
          simpa only [Nat.cast_add, Nat.cast_one] using add.symm
        rw [hnext] at nextRun
        have hrest := ih (k + 1) (by omega) (by omega)
          (Aiur.Library.Bytes.repAddressRef_heapMono₂ Core.addrTy hext hb) nextRun
        apply Core.hashed_mono _ hrest
        rw [events]
        intro cl hc
        simp [hc]

end IxVM.Refinement.Assembly
