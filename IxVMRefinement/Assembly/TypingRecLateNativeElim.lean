import IxVMRefinement.Assembly.TypingRecLateRules

/-! # The large-eliminator verdict is a bit

The circuit's `is_large_eliminator` answers `1`, `0`, or the answer of `check_large_prop_ctor`,
which answers `0` or the answer of `check_large_walk_fields`, which answers `0` or the answer of
`all_bvars_in_args`, which answers `0` or `1`. This module reads that the verdict is the field
image of `0` or `1`, and that the canonical comparison hands it, as the universe offset, to
`nat_rec_check`:

* `all_bvars_in_args_bool`, `check_large_walk_fields_bool`, `check_large_prop_ctor_bool`: by
  strong induction on the length of the call list, each walk answers `0` or `1`;
* `is_large_eliminator_bool`: the verdict, at any argument list, is `0` or `1`;
* `canonical_full_nat_rec_bool`: the canonical comparison at an inductive parent runs
  `nat_rec_check` with universe offset the field image of `if large then 1 else 0`.
-/

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency

local macro "rec_lt_calls" : tactic =>
  `(tactic| (simp only [List.length_cons, List.length_append]; omega))

/-! ## Arity -/

/-- **An observed call has as many arguments as its function has parameters.** -/
theorem obsFn_args_length_of_lookup {s : Source F} {name : String} {sf : SourceFunction F}
    (hfn : s.program.sourceFunction? name = some sf)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {cs : List (Call F)}
    (ev : ObsFn s.world name args h r h' cs) : args.length = sf.params.length := by
  cases ev with
  | intro prepared _ =>
    simp only [Source.world, sourceWorld, hfn, SourceFunction.prepare] at prepared
    split at prepared
    · rename_i hc
      have hl := congrArg List.length hc.1
      simp only [List.length_map] at hl
      exact hl.symm
    · cases prepared
  | returned prepared _ =>
    simp only [Source.world, sourceWorld, hfn, SourceFunction.prepare] at prepared
    split at prepared
    · rename_i hc
      have hl := congrArg List.length hc.1
      simp only [List.length_map] at hl
      exact hl.symm
    · cases prepared

/-- A list of length five is a list of five entries. -/
theorem list_eq_five {α : Type _} {l : List α} (hl : l.length = 5) :
    ∃ a b c d e, l = [a, b, c, d, e] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, rest⟩⟩⟩⟩⟩⟩
  all_goals first
    | exact ⟨_, _, _, _, _, rfl⟩
    | (simp only [List.length_cons, List.length_nil] at hl; omega)

/-! ## The walks answer `0` or `1` -/

/-- **`all_bvars_in_args` answers `0` or `1`.** -/
theorem all_bvars_in_args_bool {bvars args : SourceValue F} {h h' : Heap F} {r : SourceValue F}
    {cs : List (Call F)}
    (ev : ObsFn Obs.W "KernelCheck::all_bvars_in_args" [bvars, args] h r h' cs) :
    r = .field 0 ∨ r = .field 1 :=
  ObsFn.strong_induction (world := Obs.W)
    (fun fname ag _ rr _ _ => fname = "KernelCheck::all_bvars_in_args" →
      ∀ aa bb, ag = [aa, bb] → rr = .field 0 ∨ rr = .field 1)
    (fun _ _ _ _ _ _ ev_i ih_i hfn _ _ hag => by
      subst hfn hag
      match Obs.«KernelCheck::all_bvars_in_args».obs ev_i with
      | .Nil (he20 := he) .. => exact Or.inr he
      | .Cons_n0 (he75 := he) .. => exact Or.inl he
      | .Cons_other (ev87 := ev_r) (hc104 := hc_r) .. =>
        subst hc_r
        exact ih_i _ _ _ _ _ _ (by rec_lt_calls) ev_r rfl _ _ rfl)
    _ _ _ _ _ _ ev rfl bvars args rfl

/-- **`check_large_walk_fields` answers `0` or `1`.** -/
theorem check_large_walk_fields_bool {rc ty nf fi tys bvs : SourceValue F} {h h' : Heap F}
    {r : SourceValue F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "KernelCheck::check_large_walk_fields" [rc, ty, nf, fi, tys, bvs]
      h r h' cs) :
    r = .field 0 ∨ r = .field 1 :=
  ObsFn.strong_induction (world := Obs.W)
    (fun fname ag _ rr _ _ => fname = "KernelCheck::check_large_walk_fields" →
      ∀ a1 a2 a3 a4 a5 a6, ag = [a1, a2, a3, a4, a5, a6] → rr = .field 0 ∨ rr = .field 1)
    (fun _ _ _ _ _ _ ev_i ih_i hfn _ _ _ _ _ _ hag => by
      subst hfn hag
      match Obs.«KernelCheck::check_large_walk_fields».obs ev_i with
      | .n0 (ev69 := ev_b) .. => exact all_bvars_in_args_bool ev_b
      | .other_Forall (ev327 := ev_r) (hc384 := hc_r) .. =>
        subst hc_r
        exact ih_i _ _ _ _ _ _ (by rec_lt_calls) ev_r rfl _ _ _ _ _ _ rfl
      | .other_other (he389 := he) .. => exact Or.inl he)
    _ _ _ _ _ _ ev rfl rc ty nf fi tys bvs rfl

/-- **`check_large_prop_ctor` answers `0` or `1`.** -/
theorem check_large_prop_ctor_bool {rc ty np nf tys : SourceValue F} {h h' : Heap F}
    {r : SourceValue F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "KernelCheck::check_large_prop_ctor" [rc, ty, np, nf, tys] h r h' cs) :
    r = .field 0 ∨ r = .field 1 :=
  ObsFn.strong_induction (world := Obs.W)
    (fun fname ag _ rr _ _ => fname = "KernelCheck::check_large_prop_ctor" →
      ∀ a1 a2 a3 a4 a5, ag = [a1, a2, a3, a4, a5] → rr = .field 0 ∨ rr = .field 1)
    (fun _ _ _ _ _ _ ev_i ih_i hfn _ _ _ _ _ hag => by
      subst hfn hag
      match Obs.«KernelCheck::check_large_prop_ctor».obs ev_i with
      | .n0 (ev20 := ev_w) .. => exact check_large_walk_fields_bool ev_w
      | .other_Forall (ev150 := ev_r) (hc199 := hc_r) .. =>
        subst hc_r
        exact ih_i _ _ _ _ _ _ (by rec_lt_calls) ev_r rfl _ _ _ _ _ rfl
      | .other_other (he204 := he) .. => exact Or.inl he)
    _ _ _ _ _ _ ev rfl rc ty np nf tys rfl

/-! ## The verdict -/

/-- **`is_large_eliminator` answers `0` or `1`**: the level is never zero (`1`), the family is
not solo (`0`), it has no constructor (`1`), its single constructor is absent (`0`), has no
field (`1`), is not a constructor (`0`), or the walk over its fields answers; more than one
constructor (`0`). -/
theorem is_large_eliminator_bool {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    {cs : List (Call F)} (ev : ObsFn Obs.W "KernelCheck::is_large_eliminator" args h r h' cs) :
    r = .field 0 ∨ r = .field 1 := by
  have hlen := obsFn_args_length_of_lookup (s := IxVM.source)
    IxVM.KernelCheck.is_large_eliminator.lookup ev
  have h5 : args.length = 5 := by
    first
      | exact hlen.trans rfl
      | (rw [hlen]; rfl)
      | (rw [hlen]; decide)
      | (simp [IxVM.KernelCheck.is_large_eliminator] at hlen; exact hlen)
  obtain ⟨a1, a2, a3, a4, a5, rfl⟩ := list_eq_five h5
  match Obs.«KernelCheck::is_large_eliminator».obs ev with
  | .n1 (he28 := he) .. => exact Or.inr he
  | .other_n0 (he49 := he) .. => exact Or.inl he
  | .other_other_n0 (he70 := he) .. => exact Or.inr he
  | .other_other_n1_n0 (he118 := he) .. => exact Or.inl he
  | .other_other_n1_other_Ctor_n0 (he200 := he) .. => exact Or.inr he
  | .other_other_n1_other_Ctor_other (ev212 := ev') .. => exact check_large_prop_ctor_bool ev'
  | .other_other_n1_other_other (he264 := he) .. => exact Or.inl he
  | .other_other_other (he272 := he) .. => exact Or.inl he

/-- A field value that is `0` or `1` is the field image of a bit. -/
theorem field_bool_of {v : SourceValue F} (hv : v = .field 0 ∨ v = .field 1) :
    ∃ large : Bool, v = .field ((if large then 1 else 0 : Nat) : F) := by
  rcases hv with rfl | rfl
  · refine ⟨false, ?_⟩
    simp
  · refine ⟨true, ?_⟩
    simp

/-! ## The canonical comparison's universe offset -/

/-- **The canonical comparison at an inductive parent runs `nat_rec_check` with a bit as
universe offset**: the offset is the large-eliminator verdict, the field image of
`if large then 1 else 0`; at a heap after the comparison's own, within its calls. -/
theorem canonical_full_nat_rec_bool
    {rc levels type parameters indices motives minors rules k unsafeFlag block position address
      parentLevels parentType parentParams parentIndices constructors parentUnsafe parentBlock
      parentIndex parent result : SourceValue F}
    {heap final : Heap F} {calls : List (Call F)}
    (observed : ObsFn Obs.W "KernelCheck::check_recursor_canonical_full"
      [rc, .construct "KernelTypes::KConstantInfo" "Rec"
        [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block,
          position], address,
        .construct "KernelTypes::KConstantInfo" "Induct"
          [parentLevels, parentType, parentParams, parentIndices, constructors, parentUnsafe,
            parentBlock, parentIndex], parent]
      heap result final calls) :
    ∃ (large : Bool) (natHeap : Heap F) (natCalls : List (Call F)),
      Heap.Extends heap natHeap ∧
      ObsFn Obs.W "KernelCheck::nat_rec_check"
        [rc, .construct "KernelTypes::KConstantInfo" "Rec"
          [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block,
            position], address,
          .construct "KernelTypes::KConstantInfo" "Induct"
            [parentLevels, parentType, parentParams, parentIndices, constructors, parentUnsafe,
              parentBlock, parentIndex], parent, .field ((if large then 1 else 0 : Nat) : F)]
        natHeap result final natCalls ∧
      (∀ cl ∈ natCalls, cl ∈ calls) := by
  match Obs.«KernelCheck::check_recursor_canonical_full».obs observed with
  | .other (hne568 := hne) .. =>
    exact absurd rfl (hne [_, _, _, _, _, _, _, _] rfl)
  | .Induct (m272 := m272) (m329 := m329) (m281 := m281) (m389 := m389) (m342 := m342)
      (m417 := m417) (v341 := univOffset) (cs516 := natCalls)
      (sg279 := seg) (hm337 := hm337) (ev293 := sortRun) (ev399 := soloRun) (ev354 := largeRun)
      (ev429 := majorRun) (ev518 := natRun) (hc567 := children) .. =>
    have e1 : Heap.Extends heap m272 := by
      match seg with
      | .n1 (ev159 := e) (he201 := hh) .. =>
        rw [hh]
        exact e.heap_extends
      | .other (hm245 := e1) (hm259 := e2) (he269 := e3) .. =>
        rw [e3, e1, e2]
        exact (Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)
    have ext : Heap.Extends heap m417 :=
      e1.trans <| (ext_of_eq_snoc hm337).trans <| sortRun.heap_extends.trans <|
        soloRun.heap_extends.trans <| largeRun.heap_extends.trans majorRun.heap_extends
    obtain ⟨large, hlarge⟩ := field_bool_of (is_large_eliminator_bool largeRun)
    rw [hlarge] at natRun
    refine ⟨large, m417, natCalls, ext, natRun, ?_⟩
    intro call member
    rw [children]
    simp [member]

end IxVM.Refinement.Typing
