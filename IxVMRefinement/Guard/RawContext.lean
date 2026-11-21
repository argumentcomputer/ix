import IxVMRefinement.Assembly.GuardRawHead
import IxVMRefinement.Core.RawKeyed
import IxVMRefinement.Guard.InferRep

/-! # Exact physical raw context lists for structural classification

Context entries retain their raw syntax at some sufficient variable bound. The representation
is produced from every actual scoped TypesRep and is preserved by the runtime context lookup
and its capture-avoiding lift.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core

/-- A physical raw expression with an existential ambient bound. -/
def RawAny (κ : _root_.Address → KKey) (h : Heap F) (R : KExpr) (p : SourceValue F) : Prop :=
  ∃ k, RawExprRep κ h k R p

/-- A raw context list in its actual newest-first order. -/
abbrev RawContext (κ : _root_.Address → KKey) (h : Heap F) (entries : List KExpr)
    (p : SourceValue F) : Prop := RepList kexprListEnum (RawAny κ) h entries p

theorem RawAny.mono {κ : _root_.Address → KKey} {h h' : Heap F} {R : KExpr} {p : SourceValue F}
    (rep : RawAny κ h R p) (extension : Heap.Extends h h') : RawAny κ h' R p := by
  obtain ⟨k, rep⟩ := rep
  exact ⟨k, rep.mono extension⟩

theorem RawContext.mono {κ : _root_.Address → KKey} {h h' : Heap F}
    {entries : List KExpr} {p : SourceValue F} (rep : RawContext κ h entries p)
    (extension : Heap.Extends h h') : RawContext κ h' entries p :=
  repList_heapMono₂ kexprListEnum (fun _ _ _ _ ext rep => rep.mono ext) extension rep

/-- Every scoped context supplies a fixed-key physical raw list; no semantic equality to the
original ghost entries is assumed. -/
theorem RawContext.ofTypes (rawKey : _root_.Address → KKey) [∀ a, Resolved (rawKey a)]
    {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F} {d : Nat} {p : SourceValue F}
    (represented : TypesRep κ Γ h d p) : ∃ entries, RawContext rawKey h entries p := by
  induction represented with
  | nil cell => exact ⟨[], .nil cell⟩
  | cons cell type _ rest =>
    obtain ⟨R, raw⟩ := RawExprRep.ofOpenTm_keyed rawKey type
    obtain ⟨entries, tail⟩ := rest
    exact ⟨R :: entries, .cons cell ⟨_, raw⟩ tail⟩

theorem RawAny.det {κ : _root_.Address → KKey} {h : Heap F} {R S : KExpr} {p : SourceValue F}
    (first : RawAny κ h R p) (second : RawAny κ h S p) : R = S := by
  obtain ⟨k, E, first⟩ := first
  obtain ⟨j, E', second⟩ := second
  exact (first.weaken_bound (Nat.le_max_left k j)).raw_det
    (second.weaken_bound (Nat.le_max_right k j))

theorem RawContext.det {κ : _root_.Address → KKey} {h : Heap F}
    {first second : List KExpr} {p : SourceValue F}
    (left : RawContext κ h first p) (right : RawContext κ h second p) : first = second :=
  IxVMRep.repList_det (fun a b => a.det b) left right

/-- The actual context lookup returns exactly the stored raw entry lifted across the skipped
binders. Its successful list lookup and bounded call trace supply the shift bound. -/
theorem RawContext.lookup {κ : _root_.Address → KKey} {h h' : Heap F}
    {entries : List KExpr} {context r : SourceValue F} {index : F} {calls : List (Call F)}
    (represented : RawContext κ h entries context) (bounded : IxVM.Consistency.Bounded calls)
    (observed : ObsFn W "KernelInfer::types_lookup" [context, .field index] h r h' calls) :
    ∃ entry, entries[index.val]? = some entry ∧
      RawAny κ h' (entry.liftLooseBVars (index.val + 1) 0) r := by
  obtain ⟨value, loaded, lookupCalls, liftCalls, shift, lookup, added, lifted, events⟩ :=
    Obs.«KernelInfer::types_lookup».obs observed
  obtain ⟨⟨entry, selected, raw⟩, sameHeap⟩ := SubstAux.klookup lookup represented
  have listBound : entries.length < 549755813888 := by
    have bound := RomBound.bounded_length_lt bounded
      (c := ⟨Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>», [context, .field index], h⟩)
      (by rw [events]; simp) (by simp) represented
    simpa using bound
  have indexBound := (List.getElem?_eq_some_iff.mp selected).1
  have shiftValue : (index + 1).val = index.val + 1 := NatAux.val_add_one (by omega)
  have shiftEq : shift = .field (index + 1) := NatAux.add_ok added
  subst shiftEq sameHeap
  obtain ⟨k, raw⟩ := raw
  have output := raw.lift (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
    (by rw [shiftValue]; omega) lifted
  refine ⟨entry, selected, k + (index + 1).val, ?_⟩
  simpa only [shiftValue, ZMod.val_zero] using output

end IxVM.Refinement.Decl
