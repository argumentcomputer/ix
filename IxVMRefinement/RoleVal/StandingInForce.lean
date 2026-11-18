import IxVMRefinement.Claim.TopStanding
import IxVMRefinement.Claim.TopDefn
import IxVMRefinement.RoleVal.GroupAdmit

/-! # Standing in force

`KernelRoles::axiom_standing` answers nonzero at a role-bound address only if
`KernelRoles::role_of` answers nonzero there, and at a limit `n` that answer is a role whose
group is below `n`. `Claim.axiom_standing_lim_spec` and `Claim.checkedLimAt_standing` give the
standing role and drop that it is in force; the lemmas here keep it. The old statements are
their corollaries (`axiom_standing_lim_spec_of_inForce`, `checkedLimAt_standing_of_inForce`).
-/

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Claim
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

/-- **A nonzero standing answer is a standard axiom role in force**: the role is bound at the
address, and at a limit `n` its group is below `n`. -/
theorem axiom_standing_inForce_lim_spec {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address}
    {lim : Option Nat} {rc ap r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrc : RCLimRep t bAddr lim h rc) (ha : S0.addr h ap a) (hin : ¬ InertAt t a)
    (ev : ObsFn W "KernelRoles::axiom_standing" [rc, ap] h r h' cs) (hne : r ≠ .field 0) :
    ∃ ro ∈ Typing.standingRoles, t.addressOf? ro = some a ∧
      ∀ n, lim = some n → Ix.SpecDigest.groupOf ro < n := by
  match Obs.«KernelRoles::axiom_standing».obs ev with
  | .n0 (ev14 := ev14) (ev58 := ev58) (ev36 := ev36) (ev114 := ev114) (ev92 := ev92) .. =>
    obtain ⟨rfl, htbl⟩ := role_ctx_table_lim_spec hrc ev14
    obtain ⟨rfl, rfl, -⟩ := addr_index_lookup htbl ha ev58 ev36
    obtain ⟨rfl, rfl, -⟩ := Decl.role_ctx_axioms_nil hrc.axiomsNil ev114
    rw [← Obs.Names.«RBTreeMap::rbtree_map_lookup_or_default<Field>».symbol] at ev92
    match Obs.«RBTreeMap::rbtree_map_lookup_or_default».obs ev92 with
    | .Nil (he18 := he) .. => exact (hne he).elim
    | .Node_n1 (hv26 := hv) .. => simp [addrMapEnum] at hv
    | .Node_other_n0 (hv26 := hv) .. => simp [addrMapEnum] at hv
    | .Node_other_other (hv26 := hv) .. => simp [addrMapEnum] at hv
  | .other_n0 (he170 := he) .. => exact (hne he).elim
  | .other_other_n0 (he212 := he) .. => exact (hne he).elim
  | .other_other_other (ev14 := ev14) (ev58 := ev58) (ev36 := ev36)
      (hne130 := hn) (ev147 := ev147) (hne173 := hs) (ev191 := ev191) (hne215 := hro) .. =>
    obtain ⟨rfl, htbl⟩ := role_ctx_table_lim_spec hrc ev14
    obtain ⟨rfl, rfl, hi⟩ := addr_index_lookup htbl ha ev58 ev36
    rcases hi with ⟨hz, -⟩ | ⟨ro, hr, hb⟩
    · exact (hn hz).elim
    · have ext := ev147.heap_extends
      obtain ⟨-, hof⟩ :=
        RoleVal.role_of_admit_spec (hrc.mono ext).toRCRep (S0.addr_mono ext ha) ev191
      have hforce : ∀ n, lim = some n → Ix.SpecDigest.groupOf ro < n := by
        rcases hof with hz | ⟨ro', -, hb', hn'⟩
        · exact (hro hz).elim
        · have hk := (keyOf_of_addressOf htbl.1 hb').symm.trans (keyOf_of_addressOf htbl.1 hb)
          injection hk with e
          subst e
          exact fun n hl => (hn' n hl).1
      rw [hr] at ev147
      rcases Decl.axiom_role_standing_spec ev147 hs with h | h | h | h
      · subst ro; exact ⟨.propext, by decide, hb, hforce⟩
      · subst ro; exact ⟨.choice, by decide, hb, hforce⟩
      · subst ro; exact ⟨.quotSound, by decide, hb, hforce⟩
      · exact (hin ⟨ro, h, hb⟩).elim

/-- The standing answer's old specification, as a corollary. -/
theorem axiom_standing_lim_spec_of_inForce {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address}
    {lim : Option Nat} {rc ap r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrc : RCLimRep t bAddr lim h rc) (ha : S0.addr h ap a) (hin : ¬ InertAt t a)
    (ev : ObsFn W "KernelRoles::axiom_standing" [rc, ap] h r h' cs) (hne : r ≠ .field 0) :
    ∃ ro ∈ Typing.standingRoles, t.addressOf? ro = some a := by
  obtain ⟨ro, hm, hb, -⟩ := axiom_standing_inForce_lim_spec hrc ha hin ev hne
  exact ⟨ro, hm, hb⟩

/-- **The standing role of a checked axiom or quotient record, in force for an axiom**: the
role is bound at the address, and for an axiom record at a limit `n` its group is below `n`. -/
theorem checkedLimAt_standing_inForce {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {bAddr a : _root_.Address} {lim : Option Nat} {c : Ixon.Constant}
    (hS : LoadedReads.RunStore calls E₀) (hc : recordOf E₀ a = some c)
    (hl : InLogic c) (hin : ¬ InertAt t a)
    (hk : (∃ ax, c.info = .axio ax) ∨ ∃ q, c.info = .quot q)
    (hchk : CheckedLimAt calls bAddr t a lim) :
    ∃ ro ∈ Typing.standingRoles, t.addressOf? ro = some a ∧
      ((∃ ax, c.info = .axio ax) → ∀ n, lim = some n → Ix.SpecDigest.groupOf ro < n) := by
  rcases hk with ⟨ax, hax⟩ | ⟨q, hq⟩
  swap
  · obtain ⟨ro, hm', hb⟩ := checkedLimAt_standing hS hc hl hin (Or.inr ⟨q, hq⟩) hchk
    refine ⟨ro, hm', hb, fun ⟨ax, hax⟩ => ?_⟩
    rw [hq] at hax
    cases hax
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    _, hrc, ha_pre, ha_chk, ev_ld, _, hsub_ld, hld, ev_chk, _, _⟩ := hchk
  obtain ⟨ab, hab, rfl⟩ := ha_pre
  obtain ⟨bytes, c', hh, hba, hde, htrace⟩ := L1.get_ci_trace_spec hab ev_ld
  have hr : Ix.Cert.recordAt E₀ (ixAddr ab) = some c :=
    (hS.recordOf_eq_recordAt _).symm.trans hc
  have hcc : c' = c := hS.record_eq hr (Core.hashed_mono hsub_ld hh) hba hde
  subst c'
  · have hsafe : ax.isUnsafe = false := by simpa only [InLogic, hax] using hl
    simp only [L1.GetCITraceResult, hax] at htrace
    obtain ⟨_, _, v', _, _, hld', htr⟩ := htrace
    have hv : v' = v := Except.ok.inj (hld'.symm.trans hld)
    subst v'
    obtain ⟨_, tp, _, hv, _⟩ := htr
    rw [hv] at ev_chk
    simp only [hsafe, L1.repBoolField] at ev_chk
    obtain ⟨_, _, _, vstand, mscope, _, malloc, _, _, _, _, _, _, evscope, hm,
      evsort, evsafe, evstand, hne, _⟩ := Decl.check_const_axiom_inv ev_chk
    have ext : Heap.Extends mscope malloc := by rw [hm]; exact Heap.Extends.snoc _ _
    have ext' := evscope.heap_extends.trans (ext.trans (evsort.heap_extends.trans
      evsafe.heap_extends))
    obtain ⟨ro, hm', hb, hforce⟩ :=
      axiom_standing_inForce_lim_spec (hrc.mono ext') (S0.addr_mono ext' ha_chk) hin evstand hne
    exact ⟨ro, hm', hb, fun _ => hforce⟩

/-- **A nonzero standing answer, with no premise on inert roles**: a role bound at the address
whose group is below the limit, a standing role or an inert role. -/
theorem axiom_standing_role_lim_spec {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address}
    {lim : Option Nat} {rc ap r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrc : RCLimRep t bAddr lim h rc) (ha : S0.addr h ap a)
    (ev : ObsFn W "KernelRoles::axiom_standing" [rc, ap] h r h' cs) (hne : r ≠ .field 0) :
    ∃ ro, t.addressOf? ro = some a ∧ (∀ n, lim = some n → Ix.SpecDigest.groupOf ro < n) ∧
      (ro ∈ Typing.standingRoles ∨ ro.inert = true) := by
  match Obs.«KernelRoles::axiom_standing».obs ev with
  | .n0 (ev14 := ev14) (ev58 := ev58) (ev36 := ev36) (ev114 := ev114) (ev92 := ev92) .. =>
    obtain ⟨rfl, htbl⟩ := role_ctx_table_lim_spec hrc ev14
    obtain ⟨rfl, rfl, -⟩ := addr_index_lookup htbl ha ev58 ev36
    obtain ⟨rfl, rfl, -⟩ := Decl.role_ctx_axioms_nil hrc.axiomsNil ev114
    rw [← Obs.Names.«RBTreeMap::rbtree_map_lookup_or_default<Field>».symbol] at ev92
    match Obs.«RBTreeMap::rbtree_map_lookup_or_default».obs ev92 with
    | .Nil (he18 := he) .. => exact (hne he).elim
    | .Node_n1 (hv26 := hv) .. => simp [addrMapEnum] at hv
    | .Node_other_n0 (hv26 := hv) .. => simp [addrMapEnum] at hv
    | .Node_other_other (hv26 := hv) .. => simp [addrMapEnum] at hv
  | .other_n0 (he170 := he) .. => exact (hne he).elim
  | .other_other_n0 (he212 := he) .. => exact (hne he).elim
  | .other_other_other (ev14 := ev14) (ev58 := ev58) (ev36 := ev36)
      (hne130 := hn) (ev147 := ev147) (hne173 := hs) (ev191 := ev191) (hne215 := hro) .. =>
    obtain ⟨rfl, htbl⟩ := role_ctx_table_lim_spec hrc ev14
    obtain ⟨rfl, rfl, hi⟩ := addr_index_lookup htbl ha ev58 ev36
    rcases hi with ⟨hz, -⟩ | ⟨ro, hr, hb⟩
    · exact (hn hz).elim
    · have ext := ev147.heap_extends
      obtain ⟨-, hof⟩ :=
        RoleVal.role_of_admit_spec (hrc.mono ext).toRCRep (S0.addr_mono ext ha) ev191
      have hforce : ∀ n, lim = some n → Ix.SpecDigest.groupOf ro < n := by
        rcases hof with hz | ⟨ro', -, hb', hn'⟩
        · exact (hro hz).elim
        · have hk := (keyOf_of_addressOf htbl.1 hb').symm.trans (keyOf_of_addressOf htbl.1 hb)
          injection hk with e
          subst e
          exact fun n hl => (hn' n hl).1
      rw [hr] at ev147
      rcases Decl.axiom_role_standing_spec ev147 hs with h | h | h | h
      · subst ro; exact ⟨.propext, hb, hforce, Or.inl (by decide)⟩
      · subst ro; exact ⟨.choice, hb, hforce, Or.inl (by decide)⟩
      · subst ro; exact ⟨.quotSound, hb, hforce, Or.inl (by decide)⟩
      · exact ⟨ro, hb, hforce, Or.inr h⟩

/-- **The role at a checked axiom or quotient record, with no premise on inert roles**: for an
axiom record, a role bound at the address in force at the limit, a standing role or an inert
role; for a quotient record, a standing role bound at the address. -/
theorem checkedLimAt_standing_role {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {bAddr a : _root_.Address} {lim : Option Nat} {c : Ixon.Constant}
    (hS : LoadedReads.RunStore calls E₀) (hc : recordOf E₀ a = some c)
    (hl : InLogic c)
    (hk : (∃ ax, c.info = .axio ax) ∨ ∃ q, c.info = .quot q)
    (hchk : CheckedLimAt calls bAddr t a lim) :
    ∃ ro, t.addressOf? ro = some a ∧
      (((∃ ax, c.info = .axio ax) ∧ (∀ n, lim = some n → Ix.SpecDigest.groupOf ro < n) ∧
          (ro ∈ Typing.standingRoles ∨ ro.inert = true)) ∨
        ((∃ q, c.info = .quot q) ∧ ro ∈ Typing.standingRoles)) := by
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    _, hrc, ha_pre, ha_chk, ev_ld, _, hsub_ld, hld, ev_chk, _, _⟩ := hchk
  obtain ⟨ab, hab, rfl⟩ := ha_pre
  obtain ⟨bytes, c', hh, hba, hde, htrace⟩ := L1.get_ci_trace_spec hab ev_ld
  have hr : Ix.Cert.recordAt E₀ (ixAddr ab) = some c :=
    (hS.recordOf_eq_recordAt _).symm.trans hc
  have hcc : c' = c := hS.record_eq hr (Core.hashed_mono hsub_ld hh) hba hde
  subst c'
  rcases hk with ⟨ax, hax⟩ | ⟨q, hq⟩
  · have hsafe : ax.isUnsafe = false := by simpa only [InLogic, hax] using hl
    simp only [L1.GetCITraceResult, hax] at htrace
    obtain ⟨_, _, v', _, _, hld', htr⟩ := htrace
    have hv : v' = v := Except.ok.inj (hld'.symm.trans hld)
    subst v'
    obtain ⟨_, tp, _, hv, _⟩ := htr
    rw [hv] at ev_chk
    simp only [hsafe, L1.repBoolField] at ev_chk
    obtain ⟨_, _, _, vstand, mscope, _, malloc, _, _, _, _, _, _, evscope, hm,
      evsort, evsafe, evstand, hne, _⟩ := Decl.check_const_axiom_inv ev_chk
    have ext : Heap.Extends mscope malloc := by rw [hm]; exact Heap.Extends.snoc _ _
    have ext' := evscope.heap_extends.trans (ext.trans (evsort.heap_extends.trans
      evsafe.heap_extends))
    obtain ⟨ro, hb, hforce, hrole⟩ :=
      axiom_standing_role_lim_spec (hrc.mono ext') (S0.addr_mono ext' ha_chk) evstand hne
    exact ⟨ro, hb, Or.inl ⟨⟨ax, hax⟩, hforce, hrole⟩⟩
  · simp only [L1.GetCITraceResult, hq] at htrace
    obtain ⟨_, _, v', _, _, hld', htr⟩ := htrace
    have hv : v' = v := Except.ok.inj (hld'.symm.trans hld)
    subst v'
    obtain ⟨_, tp, _, hv, _⟩ := htr
    rw [hv] at ev_chk
    obtain ⟨_, _, _, mscope, _, malloc, _, _, _, _, _, evscope, hm,
      evsort, evsafe, evquot, _⟩ := Decl.check_const_quot_inv ev_chk
    have ext : Heap.Extends mscope malloc := by rw [hm]; exact Heap.Extends.snoc _ _
    have ext' := evscope.heap_extends.trans (ext.trans (evsort.heap_extends.trans
      evsafe.heap_extends))
    obtain ⟨ro, hm', hb⟩ := check_quot_lim_standing (hrc.mono ext') (S0.addr_mono ext' ha_chk) evquot
    exact ⟨ro, hb, Or.inr ⟨⟨q, hq⟩, hm'⟩⟩

/-- The checked record's old standing specification, as a corollary. -/
theorem checkedLimAt_standing_of_inForce {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {bAddr a : _root_.Address} {lim : Option Nat} {c : Ixon.Constant}
    (hS : LoadedReads.RunStore calls E₀) (hc : recordOf E₀ a = some c)
    (hl : InLogic c) (hin : ¬ InertAt t a)
    (hk : (∃ ax, c.info = .axio ax) ∨ ∃ q, c.info = .quot q)
    (hchk : CheckedLimAt calls bAddr t a lim) :
    ∃ ro ∈ Typing.standingRoles, t.addressOf? ro = some a := by
  obtain ⟨ro, hm, hb, -⟩ := checkedLimAt_standing_inForce hS hc hl hin hk hchk
  exact ⟨ro, hm, hb⟩

end IxVM.Refinement.Claim
