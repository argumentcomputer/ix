import IxVMRefinement.Obs.KernelWhnf1

/-! # Inductive heads in the actual evaluator trace

The evaluator reconstructs an inductive head's application after primitive dispatch declines.
This fact uses the actual selected metadata load, not rigidity of arbitrary Rules.Red proofs.
A nonempty universe list supplies the primitive-dispatch exclusion directly from control flow.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open Obs (W)

/-- Primitive acceleration is unavailable at a nonempty universe list. -/
theorem primitive_dispatch_zero_of_cons
    {rc address levels headLevel tail spine types result : SourceValue F}
    {heap final : Heap F} {calls : List (Call F)}
    (levelList : loadValue heap levels = .ok
      (.construct Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» "Cons" [headLevel, tail]))
    (observed : ObsFn W "KernelWhnf::try_prim_dispatch"
      [rc, address, levels, spine, types] heap result final calls) :
    ∃ value, result = .tuple [.field 0, value] := by
  cases Obs.«KernelWhnf::try_prim_dispatch».obs observed with
  | Nil_n1 _ _ _ _ empty _ _ _ => rw [levelList] at empty; cases empty
  | Nil_other _ _ _ _ _ empty _ _ _ _ _ _ => rw [levelList] at empty; cases empty
  | other _ _ _ _ answer _ _ _ => exact ⟨_, answer⟩

/-- If the actual primitive call declines and the selected metadata load is inductive,
constant-head evaluation only reconstructs the original application spine. Both premises
are restricted to child traces of this particular call. -/
theorem whnf_const_head_inductive_spine
    {rc address levels head spine types result : SourceValue F}
    {heap final : Heap F} {calls : List (Call F)}
    (observed : ObsFn W "KernelWhnf::whnf_const_head"
      [rc, address, levels, head, spine, types] heap result final calls)
    (noPrimitive : ∀ value middle children,
      ObsFn W "KernelWhnf::try_prim_dispatch" [rc, address, levels, spine, types]
        heap value middle children →
      (∀ call ∈ children, call ∈ calls) → ∃ unused, value = .tuple [.field 0, unused])
    (inductiveLoads : ∀ before pointer after children,
      (⟨"Ingress::get_ci", [address], before⟩ : Call F) ∈ calls →
      (∀ call ∈ children, call ∈ calls) →
      ObsFn W "Ingress::get_ci" [address] before pointer after children →
      ∃ fields, loadValue after pointer =
        .ok (.construct "KernelTypes::KConstantInfo" "Induct" fields)) :
    ∃ middle children,
      Heap.Extends heap middle ∧
      ObsFn W "KernelWhnf::apply_spine" [head, spine] middle result final children ∧
      (⟨"KernelWhnf::apply_spine", [head, spine], middle⟩ : Call F) ∈ calls ∧
      (∀ call ∈ children, call ∈ calls) := by
  have incompatible {before after : Heap F} {pointer : SourceValue F} {children : List (Call F)}
      {tag : String} {fields : List (SourceValue F)}
      (different : tag ≠ "Induct")
      (member : (⟨"Ingress::get_ci", [address], before⟩ : Call F) ∈ calls)
      (included : ∀ call ∈ children, call ∈ calls)
      (loaded : ObsFn W "Ingress::get_ci" [address] before pointer after children)
      (payload : loadValue after pointer = .ok (.construct "KernelTypes::KConstantInfo" tag fields)) : False := by
    obtain ⟨actualFields, actual⟩ := inductiveLoads before pointer after children member included loaded
    rw [payload] at actual
    have tagEq := (Value.construct.inj (Except.ok.inj actual)).2.1
    exact different tagEq
  match Obs.«KernelWhnf::whnf_const_head».obs observed with
  | .n1_bind (ev14 := primitive) (hc113 := allCalls) .. =>
    obtain ⟨_, answer⟩ := noPrimitive _ _ _ primitive (by rw [allCalls]; intro call member; simp [member])
    have impossible : (1 : F) = 0 := Value.field.inj (List.cons.inj (Value.tuple.inj answer)).1
    exact (one_ne_zero impossible).elim
  | .n2_bind (ev14 := primitive) (hc135 := allCalls) .. =>
    obtain ⟨_, answer⟩ := noPrimitive _ _ _ primitive (by rw [allCalls]; intro call member; simp [member])
    have impossible : (2 : F) = 0 := Value.field.inj (List.cons.inj (Value.tuple.inj answer)).1
    exact ((by decide : (2 : F) ≠ 0) impossible).elim
  | .other_Defn_n1_bind (ev155 := loaded) (ld149 := payload) (hc312 := allCalls) .. =>
    exact (incompatible (by decide) (by rw [allCalls]; simp)
      (by rw [allCalls]; intro call member; simp [member]) loaded payload).elim
  | .other_Defn_other_n1_bind (ev155 := loaded) (ld149 := payload) (hc403 := allCalls) .. =>
    exact (incompatible (by decide) (by rw [allCalls]; simp)
      (by rw [allCalls]; intro call member; simp [member]) loaded payload).elim
  | .other_Defn_other_other (ev155 := loaded) (ld149 := payload) (hc429 := allCalls) .. =>
    exact (incompatible (by decide) (by rw [allCalls]; simp)
      (by rw [allCalls]; intro call member; simp [member]) loaded payload).elim
  | .other_Thm (ev155 := loaded) (ld149 := payload) (hc477 := allCalls) .. =>
    exact (incompatible (by decide) (by rw [allCalls]; simp)
      (by rw [allCalls]; intro call member; simp [member]) loaded payload).elim
  | .other_Quot_n1_bind (ev155 := loaded) (ld149 := payload) (hc615 := allCalls) .. =>
    exact (incompatible (by decide) (by rw [allCalls]; simp)
      (by rw [allCalls]; intro call member; simp [member]) loaded payload).elim
  | .other_Quot_other (ev155 := loaded) (ld149 := payload) (hc641 := allCalls) .. =>
    exact (incompatible (by decide) (by rw [allCalls]; simp)
      (by rw [allCalls]; intro call member; simp [member]) loaded payload).elim
  | .other_Rec_n1_bind (ev155 := loaded) (ld149 := payload) (hc874 := allCalls) .. =>
    exact (incompatible (by decide) (by rw [allCalls]; simp)
      (by rw [allCalls]; intro call member; simp [member]) loaded payload).elim
  | .other_Rec_n2_bind (ev155 := loaded) (ld149 := payload) (hc896 := allCalls) .. =>
    exact (incompatible (by decide) (by rw [allCalls]; simp)
      (by rw [allCalls]; intro call member; simp [member]) loaded payload).elim
  | .other_Rec_n3_bind (ev155 := loaded) (ld149 := payload) (hc945 := allCalls) .. =>
    exact (incompatible (by decide) (by rw [allCalls]; simp)
      (by rw [allCalls]; intro call member; simp [member]) loaded payload).elim
  | .other_Rec_other (ev155 := loaded) (ld149 := payload) (hc971 := allCalls) .. =>
    exact (incompatible (by decide) (by rw [allCalls]; simp)
      (by rw [allCalls]; intro call member; simp [member]) loaded payload).elim
  | .other_other (m140 := middle) (cs979 := children) (ev14 := primitive)
      (ev155 := loaded) (ev981 := rebuilt) (hc998 := allCalls) .. =>
    exact ⟨middle, children, primitive.heap_extends.trans loaded.heap_extends, rebuilt,
      by rw [allCalls]; simp,
      by rw [allCalls]; intro call member; simp [member]⟩

/-- The universe-list guard supplies primitive exclusion for the polymorphic case. -/
theorem whnf_const_head_polymorphic_inductive
    {rc address levels headLevel tail head spine types result : SourceValue F}
    {heap final : Heap F} {calls : List (Call F)}
    (observed : ObsFn W "KernelWhnf::whnf_const_head"
      [rc, address, levels, head, spine, types] heap result final calls)
    (levelList : loadValue heap levels = .ok
      (.construct Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» "Cons" [headLevel, tail]))
    (inductiveLoads : ∀ before pointer after children,
      (⟨"Ingress::get_ci", [address], before⟩ : Call F) ∈ calls →
      (∀ call ∈ children, call ∈ calls) →
      ObsFn W "Ingress::get_ci" [address] before pointer after children →
      ∃ fields, loadValue after pointer =
        .ok (.construct "KernelTypes::KConstantInfo" "Induct" fields)) :
    ∃ middle children,
      Heap.Extends heap middle ∧
      ObsFn W "KernelWhnf::apply_spine" [head, spine] middle result final children ∧
      (⟨"KernelWhnf::apply_spine", [head, spine], middle⟩ : Call F) ∈ calls ∧
      (∀ call ∈ children, call ∈ calls) :=
  whnf_const_head_inductive_spine observed
    (fun _ _ _ primitive _ => primitive_dispatch_zero_of_cons levelList primitive) inductiveLoads

end IxVM.Refinement.Decl
