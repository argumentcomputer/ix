import IxVMRefinement.Assembly.NativeAliasTeleWalk

/-! # Stability of the actual syntactic telescope test

The former guard and telescope builder test the same pointer at different heaps. The test
only reads its syntactic binder spine, so a successful answer is retained along heap extension.
This statement uses heap cells and observations, not a converse from the zeta-read kernel type.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core

/-- A successful test exposes the actual syntactic cells, including its terminal sort cell. -/
theorem former_is_tele_one_cells :
    ∀ (n : Nat) {p : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 18446744069414584321 →
      ObsFn W "KernelCheck::former_is_tele" [p, .field (n : F)] h (.field 1) h' cs →
      ∃ level, TeleShape h n p level
  | 0, p, h, h', cs, _, ev => by
    match Obs.«KernelCheck::former_is_tele».obs ev with
    | .n0_Srt (w34 := level) (ld26 := ld) .. => exact ⟨level, ld⟩
    | .n0_other (he47 := hr) .. => exact nomatch hr
    | .other_Forall (hne50 := hne) .. | .other_other (hne50 := hne) .. =>
      exact absurd rfl hne
  | n + 1, p, h, h', cs, hlt, ev => by
    match Obs.«KernelCheck::former_is_tele».obs ev with
    | .n0_Srt (hv14 := hv) .. | .n0_other (hv14 := hv) .. =>
      exact absurd hv (succ_field_ne_zero_bounded hlt)
    | .other_other (he125 := hr) .. => exact nomatch hr
    | .other_Forall (w73 := dom) (x_b := body) (w74 := metaPtr) (ld65 := ld)
        (op118 := op) (ev95 := rest) .. =>
      rw [evalBinOp_sub_succ n op] at rest
      obtain ⟨level, tail⟩ := former_is_tele_one_cells n (by omega) rest
      exact ⟨level, dom, body, metaPtr, ld, tail⟩

/-- The same actual cells force a successful answer, regardless of the observed derivation. -/
theorem former_is_tele_of_cells :
    ∀ (n : Nat) {p level r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 18446744069414584321 → TeleShape h n p level →
      ObsFn W "KernelCheck::former_is_tele" [p, .field (n : F)] h r h' cs → r = .field 1
  | 0, p, level, r, h, h', cs, _, shape, ev => by
    match Obs.«KernelCheck::former_is_tele».obs ev with
    | .n0_Srt (he40 := hr) .. => exact hr
    | .n0_other (ld26 := ld) (hne43 := hn) .. =>
      exact (hn [level] rfl (Except.ok.inj (ld.symm.trans shape))).elim
    | .other_Forall (hne50 := hne) .. | .other_other (hne50 := hne) .. =>
      exact absurd rfl hne
  | n + 1, p, level, r, h, h', cs, hlt, ⟨dom, body, metaPtr, cell, tail⟩, ev => by
    match Obs.«KernelCheck::former_is_tele».obs ev with
    | .n0_Srt (hv14 := hv) .. | .n0_other (hv14 := hv) .. =>
      exact absurd hv (succ_field_ne_zero_bounded hlt)
    | .other_other (ld65 := ld) (hne121 := hn) .. =>
      exact (hn [dom, body, metaPtr] rfl (Except.ok.inj (ld.symm.trans cell))).elim
    | .other_Forall (ld65 := ld) (op118 := op) (ev95 := rest) .. =>
      have he := Except.ok.inj (cell.symm.trans ld)
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      rw [evalBinOp_sub_succ n op] at rest
      exact former_is_tele_of_cells n (by omega) tail rest

/-- A successful former test cannot become unsuccessful merely by growing the heap. -/
theorem former_is_tele_one_stable {n : Nat} {p r : SourceValue F}
    {h h' H H' : Heap F} {cs ds : List (Call F)} (hn : n < 18446744069414584321)
    (hext : Heap.Extends h H)
    (first : ObsFn W "KernelCheck::former_is_tele" [p, .field (n : F)] h (.field 1) h' cs)
    (second : ObsFn W "KernelCheck::former_is_tele" [p, .field (n : F)] H r H' ds) :
    r = .field 1 := by
  obtain ⟨level, shape⟩ := former_is_tele_one_cells n hn first
  exact former_is_tele_of_cells n hn (shape.mono hext) second

end IxVM.Refinement.Decl
