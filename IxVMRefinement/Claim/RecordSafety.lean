import IxVMRefinement.Claim.Walk
import IxVMRefinement.Ingress.Ingress
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
  have hk' : xk = Ingress.repDefKindVal d.kind := by
    cases he : d.kind <;> simpa only [RepDefKind, Ingress.repDefKindVal, he] using hk
  have hs' : xs = Ingress.repDefSafetyVal d.safety := by
    cases he : d.safety <;> simpa only [RepDefinitionSafety, Ingress.repDefSafetyVal, he] using hs
  rw [hk', hs'] at ev
  have hf : Ingress.defnIsUnsafeCI d = false := by
    rcases d with ⟨kind, safety, asserts, lvls, typ, val⟩
    cases kind <;> cases safety <;> first | rfl | cases hlogic
  obtain ⟨hr, hh⟩ := Ingress.defn_is_unsafe_ci_spec ev
  exact ⟨by simpa [hf, Ingress.repBoolField] using hr, hh⟩

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
      have hsafety : rc.isUnsafe = false := hl
      have hu0 : u = .field 0 := by simpa [RepBool, hsafety] using hu
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

private theorem repConstant_info_of_shape {h : Heap F} {c : Ixon.Constant}
    {info sh rf un bd : SourceValue F}
    (hc : RepConstant h c (.construct "Ixon::Constant" "Mk" [info, sh, rf, un, bd])) :
    RepConstantInfo h c.info info := by
  obtain ⟨info', sh', rf', un', bd', hv, hi, _⟩ := hc
  simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv
  rcases hv with ⟨rfl, _, _, _, _⟩
  exact hi

/-- The source helper returns the record's actual owner address and does not allocate. -/
theorem record_owner_spec {a : _root_.Address} {c : Ixon.Constant}
    {ap cp r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ha : BaseSeams.addr h ap a) (hc : RepConstant h c cp)
    (ev : ObsFn Obs.W "KernelClaim::record_owner" [ap, cp] h r h' calls) :
    h' = h ∧ BaseSeams.addr h r (Ix.Cert.ownerOf a c) := by
  match Obs.«KernelClaim::record_owner».obs ev with
  | .DPrj (hv15 := hv) (he95 := hr) (he96 := hh) .. =>
    subst hh
    subst hr
    rw [hv] at hc
    have hi := repConstant_info_of_shape hc
    cases hinfo : c.info <;> rw [hinfo] at hi
    case dPrj p =>
      obtain ⟨pv, hpv, bp, hbp, hab⟩ := hi
      rw [hbp] at hpv
      simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hpv
      rcases hpv with ⟨_, hb⟩
      exact ⟨rfl, by simpa only [Ix.Cert.ownerOf, hinfo, hb] using hab⟩
    all_goals obtain ⟨_, bad, _⟩ := hi; simp at bad
  | .IPrj (hv15 := hv) (he139 := hr) (he140 := hh) .. =>
    subst hh
    subst hr
    rw [hv] at hc
    have hi := repConstant_info_of_shape hc
    cases hinfo : c.info <;> rw [hinfo] at hi
    case iPrj p =>
      obtain ⟨pv, hpv, bp, hbp, hab⟩ := hi
      rw [hbp] at hpv
      simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hpv
      rcases hpv with ⟨_, hb⟩
      exact ⟨rfl, by simpa only [Ix.Cert.ownerOf, hinfo, hb] using hab⟩
    all_goals obtain ⟨_, bad, _⟩ := hi; simp at bad
  | .CPrj (hv15 := hv) (he189 := hr) (he190 := hh) .. =>
    subst hh
    subst hr
    rw [hv] at hc
    have hi := repConstant_info_of_shape hc
    cases hinfo : c.info <;> rw [hinfo] at hi
    case cPrj p =>
      obtain ⟨pv, hpv, bp, hbp, hab⟩ := hi
      rw [hbp] at hpv
      simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hpv
      rcases hpv with ⟨_, _, hb⟩
      exact ⟨rfl, by simpa only [Ix.Cert.ownerOf, hinfo, hb] using hab⟩
    all_goals obtain ⟨_, bad, _⟩ := hi; simp at bad
  | .RPrj (hv15 := hv) (he233 := hr) (he234 := hh) .. =>
    subst hh
    subst hr
    rw [hv] at hc
    have hi := repConstant_info_of_shape hc
    cases hinfo : c.info <;> rw [hinfo] at hi
    case rPrj p =>
      obtain ⟨pv, hpv, bp, hbp, hab⟩ := hi
      rw [hbp] at hpv
      simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hpv
      rcases hpv with ⟨_, hb⟩
      exact ⟨rfl, by simpa only [Ix.Cert.ownerOf, hinfo, hb] using hab⟩
    all_goals obtain ⟨_, bad, _⟩ := hi; simp at bad
  | .other (hv15 := hv) (hne99 := hnd) (hne143 := hni) (hne193 := hnc) (hne237 := hnr)
      (he242 := hr) (he243 := hh) .. =>
    subst hh
    subst hr
    rw [hv] at hc
    have hi := repConstant_info_of_shape hc
    cases hinfo : c.info <;> rw [hinfo] at hi
    case dPrj _ => obtain ⟨pv, hpv, _⟩ := hi; exact (hnd [pv] rfl hpv).elim
    case iPrj _ => obtain ⟨pv, hpv, _⟩ := hi; exact (hni [pv] rfl hpv).elim
    case cPrj _ => obtain ⟨pv, hpv, _⟩ := hi; exact (hnc [pv] rfl hpv).elim
    case rPrj _ => obtain ⟨pv, hpv, _⟩ := hi; exact (hnr [pv] rfl hpv).elim
    all_goals exact ⟨rfl, by simpa only [Ix.Cert.ownerOf, hinfo] using ha⟩


/-- The record actually loaded by a safety query; if that record is in logic, its answer is zero. -/
theorem record_unsafe_safe_spec {x_addr : SourceValue F} {addr : _root_.Address}
    {r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ha : BaseSeams.addr h x_addr addr)
    (ev : ObsFn Obs.W "KernelClaim::record_unsafe" [x_addr] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (rawBytes : ByteArray) (c : Ixon.Constant),
      rawBytes.size < 4294967296 ∧ Hashed calls rawBytes ∧
      Address.blake3Pure rawBytes = addr ∧
      Ixon.deConstant rawBytes = .ok c ∧
      Ixon.deConstantExact rawBytes = .ok c ∧ (InLogic c → r = .field 0) := by
  rcases Obs.«KernelClaim::record_unsafe».obs ev with
    ⟨m2, cs12, _, _, _, _, x_kind, x_safety, _, _, _, _, cs142, ev14, ev144, hc161⟩ |
    ⟨m2, cs12, _, _, _, _, _, x_is_unsafe, _, _, _, _, _, _, _, ev14, he245, rfl, hc247⟩ |
    ⟨m2, cs12, _, _, _, _, x_is_unsafe, _, _, ev14, he295, rfl, hc297⟩ |
    ⟨m2, cs12, _, _, _, _, x_members, cs314, ev14, ev316, hc325⟩ |
    ⟨m2, cs12, x_info, _, _, _, _, ev14, hne163, hne249, hne299, hne326, he330, rfl, hc332⟩
  · obtain ⟨ext1, rawBytes, c, hsz, hh, hblk, hde, hdeExact, hrep, _⟩ := load_verified_constant_de ha ev14
    obtain ⟨infoVal, _, _, _, _, hv, hinfo, _, _, _, _⟩ := hrep
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo
    cases hc : c.info <;> rw [hc] at hinfo
    case defn d =>
      obtain ⟨dv, hdv_eq, kVal, sVal, _, _, _, hdv, hk, hs, _, _, _⟩ := hinfo
      rw [hdv] at hdv_eq
      injection hdv_eq with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ hdargs
      simp only [List.cons.injEq] at hdargs
      rw [← hdargs.1] at hk
      rw [← hdargs.2.1] at hs
      refine ⟨ev.heap_extends, rawBytes, c, hsz,
        hashed_mono (fun cl hcl => by rw [hc161]; simp [hcl]) hh, hblk, hde, hdeExact, ?_⟩
      intro hlogic
      have hsafety : Ix.Kernel.Reader.safetyDecline d = none := by
        simpa only [InLogic, hc] using hlogic
      exact (defn_is_unsafe_ci_safe_spec hk hs hsafety ev144).1
    all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')

  · obtain ⟨ext1, rawBytes, c, hsz, hh, hblk, hde, hdeExact, hrep, _⟩ := load_verified_constant_de ha ev14
    obtain ⟨infoVal, _, _, _, _, hv, hinfo, _, _, _, _⟩ := hrep
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo
    cases hc : c.info <;> rw [hc] at hinfo
    case recr rc =>
      obtain ⟨rv, hrv_eq, _, uVal, _, _, hrv, _, hu, _, _⟩ := hinfo
      rw [hrv] at hrv_eq
      injection hrv_eq with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ hrargs
      simp only [List.cons.injEq] at hrargs
      refine ⟨ev.heap_extends, rawBytes, c, hsz,
        hashed_mono (fun cl hcl => by rw [hc247]; simp [hcl]) hh, hblk, hde, hdeExact, ?_⟩
      intro hlogic
      have hsafety : rc.isUnsafe = false := by simpa only [InLogic, hc] using hlogic
      have hu0 : uVal = .field 0 := by simpa [RepBool, hsafety] using hu
      exact he245.trans (hrargs.2.1.trans hu0)
    all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')

  · obtain ⟨ext1, rawBytes, c, hsz, hh, hblk, hde, hdeExact, hrep, _⟩ := load_verified_constant_de ha ev14
    obtain ⟨infoVal, _, _, _, _, hv, hinfo, _, _, _, _⟩ := hrep
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo
    cases hc : c.info <;> rw [hc] at hinfo
    case axio a =>
      obtain ⟨av, hav_eq, uVal, _, hav, hu, _⟩ := hinfo
      rw [hav] at hav_eq
      injection hav_eq with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ haargs
      simp only [List.cons.injEq] at haargs
      refine ⟨ev.heap_extends, rawBytes, c, hsz,
        hashed_mono (fun cl hcl => by rw [hc297]; simp [hcl]) hh, hblk, hde, hdeExact, ?_⟩
      intro hlogic
      have hsafety : a.isUnsafe = false := by simpa only [InLogic, hc] using hlogic
      have hu0 : uVal = .field 0 := by simpa [RepBool, hsafety] using hu
      exact he295.trans (haargs.1.trans hu0)
    all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')

  · obtain ⟨ext1, rawBytes, c, hsz, hh, hblk, hde, hdeExact, hrep, _⟩ := load_verified_constant_de ha ev14
    obtain ⟨infoVal, _, _, _, _, hv, hinfo, _, _, _, _⟩ := hrep
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo
    cases hc : c.info <;> rw [hc] at hinfo
    case muts ms =>
      obtain ⟨mv, hmv_eq, hms⟩ := hinfo
      injection hmv_eq with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      rw [← h1] at hms
      refine ⟨ev.heap_extends, rawBytes, c, hsz,
        hashed_mono (fun cl hcl => by rw [hc325]; simp [hcl]) hh, hblk, hde, hdeExact, ?_⟩
      intro hlogic
      have hsafety : ∀ m ∈ ms.toList, InLogicMut m := by simpa only [InLogic, hc] using hlogic
      exact (muts_unsafe_safe_spec ms.toList hms hsafety ev316).1
    all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
  · obtain ⟨_, rawBytes, c, hsz, hh, hblk, hde, hdeExact, _, _⟩ :=
      load_verified_constant_de ha ev14
    exact ⟨ev.heap_extends, rawBytes, c, hsz,
      hashed_mono (fun cl hcl => by rw [hc332]; simp [hcl]) hh, hblk, hde, hdeExact,
      fun _ => he330⟩


end IxVM.Refinement.Claim
