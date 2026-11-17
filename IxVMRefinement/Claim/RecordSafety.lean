import IxVMRefinement.Claim.Walk
import IxVMRefinement.L1.Ingress
import IxVMRefinement.Obs.KernelClaim

/-! # Observed record-owner and safety queries

The source-conditioned reference guard must take its safe branch when the source and owner
are in logic. These converse safety specifications complement the existing zero-result
specifications; they do not assume the branch the guard took.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Claim
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

/-- A definition accepted by the reader's safety policy reports zero unsafe status. -/
theorem defn_is_unsafe_ci_safe_spec {d : Ixon.Definition} {xk xs r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hk : RepDefKind d.kind xk) (hs : RepDefinitionSafety d.safety xs)
    (hlogic : Ix.Kernel.Reader.safetyDecline d = none)
    (ev : ObsFn Obs.W "Ingress::defn_is_unsafe_ci" [xk, xs] h r h' calls) :
    r = .field 0 ∧ h' = h := by
  have hk' : xk = L1.repDefKindVal d.kind := by
    cases he : d.kind <;> simpa only [RepDefKind, L1.repDefKindVal, he] using hk
  have hs' : xs = L1.repDefSafetyVal d.safety := by
    cases he : d.safety <;> simpa only [RepDefinitionSafety, L1.repDefSafetyVal, he] using hs
  rw [hk', hs'] at ev
  have hf : L1.defnIsUnsafeCI d = false := by
    cases hk : d.kind <;> cases hs : d.safety <;>
      simp_all [Ix.Kernel.Reader.safetyDecline, Ix.Kernel.Reader.safetyDeclineOf, L1.defnIsUnsafeCI]
  obtain ⟨hr, hh⟩ := L1.defn_is_unsafe_ci_spec ev
  exact ⟨by simpa only [hf, L1.repBoolField] using hr, hh⟩

/-- A list of safe constructors reports zero, without changing the heap. -/
theorem ctors_unsafe_safe_spec (ctors : List Ixon.Constructor) :
    ∀ {h h' : Heap F} {ptr r : SourceValue F} {calls : List (Call F)},
      RepList Obs.Names.«Lists::Node<Ixon::Constructor>» RepConstructor h ctors ptr →
      (∀ c ∈ ctors, c.isUnsafe = false) →
      ObsFn Obs.W "KernelClaim::ctors_unsafe" [ptr] h r h' calls → r = .field 0 ∧ h' = h := by
  induction ctors with
  | nil =>
    intro h h' ptr r calls rep hs ev
    match Obs.«KernelClaim::ctors_unsafe».obs ev with
    | .Nil (he20 := hr) (he21 := hh) .. => exact ⟨hr, hh⟩
    | .Cons_n0 (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hb, _⟩ := Lib.rep_cons_of_load rep ld
      cases hb
  | cons ctor rest ih =>
    intro h h' ptr r calls rep hs ev
    match Obs.«KernelClaim::ctors_unsafe».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load rep ld
    | .Cons_n0 (ld12 := ld) (ev116 := ev116) .. =>
      obtain ⟨_, _, he, _, hrest⟩ := Lib.rep_cons_of_load rep ld
      injection he with he1 he2
      subst he1 he2
      exact ih hrest (fun c hc => hs c (List.mem_cons_of_mem _ hc)) ev116
    | .Cons_other (ld12 := ld) (hne126 := hn) .. =>
      obtain ⟨_, _, he, hctor, _⟩ := Lib.rep_cons_of_load rep ld
      injection he with he1 he2
      subst he1 he2
      obtain ⟨u, _, _, hv, hu, _⟩ := hctor
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      have hu0 : u = .field 0 := by simpa [RepBool, hs ctor (List.mem_cons_self)] using hu
      exact (hn (hargs.1.trans hu0)).elim

private theorem mut_unsafe_safe_spec {mc : Ixon.MutConst} {m rest ms r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hm : RepMutConst h mc m) (hl : InLogicMut mc)
    (ev : Obs.«KernelClaim::muts_unsafe».Seg1 m rest ms h r h' calls) :
    r = .field 0 ∧ h' = h := by
  match ev with
  | .Defn (hv54 := hv54) (ev116 := ev116) .. =>
    cases mc with
    | indc _ | recr _ => obtain ⟨_, hv, _⟩ := hm; rw [hv54] at hv; simp at hv
    | defn d =>
      obtain ⟨dv, hv, k, s, _, _, _, hd, hk, hs, _⟩ := hm
      rw [hd, hv54] at hv
      injection hv with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ hargs
      simp only [List.cons.injEq] at hargs
      rw [← hargs.1] at hk
      rw [← hargs.2.1] at hs
      exact defn_is_unsafe_ci_safe_spec hk hs hl ev116
  | .Indc_n0 (hv140 := hv140) (ev216 := ev216) .. =>
    cases mc with
    | defn _ | recr _ => obtain ⟨_, hv, _⟩ := hm; rw [hv140] at hv; simp at hv
    | indc ind =>
      obtain ⟨iv, hv, u, _, cp, hi, _, _, hctors⟩ := hm
      rw [hi, hv140] at hv
      injection hv with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      rw [← hargs.2.2.2.2.2] at hctors
      exact ctors_unsafe_safe_spec ind.ctors.toList hctors hl.2 ev216
  | .Indc_other (hv140 := hv140) (hne226 := hn) .. =>
    cases mc with
    | defn _ | recr _ => obtain ⟨_, hv, _⟩ := hm; rw [hv140] at hv; simp at hv
    | indc ind =>
      obtain ⟨iv, hv, u, _, _, hi, hu, _⟩ := hm
      rw [hi, hv140] at hv
      injection hv with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      have hu0 : u = .field 0 := by simpa [RepBool, hl.1] using hu
      exact (hn (hargs.1.trans hu0)).elim
  | .Recr (hv239 := hv239) (he316 := hr) (he317 := hh) .. =>
    cases mc with
    | defn _ | indc _ => obtain ⟨_, hv, _⟩ := hm; rw [hv239] at hv; simp at hv
    | recr rc =>
      obtain ⟨rv, hv, _, u, _, _, hrv, _, hu, _⟩ := hm
      rw [hrv, hv239] at hv
      injection hv with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ hargs
      simp only [List.cons.injEq] at hargs
      have hu0 : u = .field 0 := by simpa [RepBool, hl] using hu
      exact ⟨hr.trans (hargs.2.1.trans hu0), hh⟩

/-- A block whose members are all in logic reports zero unsafe status. -/
theorem muts_unsafe_safe_spec (members : List Ixon.MutConst) :
    ∀ {h h' : Heap F} {ptr r : SourceValue F} {calls : List (Call F)},
      RepList Obs.Names.«Lists::Node<Ixon::MutConst>» RepMutConst h members ptr →
      (∀ m ∈ members, InLogicMut m) →
      ObsFn Obs.W "KernelClaim::muts_unsafe" [ptr] h r h' calls → r = .field 0 ∧ h' = h := by
  induction members with
  | nil =>
    intro h h' ptr r calls rep hs ev
    match Obs.«KernelClaim::muts_unsafe».obs ev with
    | .Nil (he20 := hr) (he21 := hh) .. => exact ⟨hr, hh⟩
    | .Cons_n0 (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hb, _⟩ := Lib.rep_cons_of_load rep ld
      cases hb
  | cons mc rest ih =>
    intro h h' ptr r calls rep hs ev
    match Obs.«KernelClaim::muts_unsafe».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load rep ld
    | .Cons_n0 (ld12 := ld) (sg329 := seg) (ev349 := ev349) .. =>
      obtain ⟨_, _, he, hm, hrest⟩ := Lib.rep_cons_of_load rep ld
      injection he with he1 he2
      subst he1 he2
      obtain ⟨_, rfl⟩ := mut_unsafe_safe_spec hm (hs mc (List.mem_cons_self)) seg
      exact ih hrest (fun m hm => hs m (List.mem_cons_of_mem _ hm)) ev349
    | .Cons_other (ld12 := ld) (sg329 := seg) (hne359 := hn) .. =>
      obtain ⟨_, _, he, hm, _⟩ := Lib.rep_cons_of_load rep ld
      injection he with he1 he2
      subst he1 he2
      exact (hn (mut_unsafe_safe_spec hm (hs mc (List.mem_cons_self)) seg).1).elim

end IxVM.Refinement.Claim
