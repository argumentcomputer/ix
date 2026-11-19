import IxVMRefinement.Claim.TopReach
import IxVMRefinement.Decl.Value

/-! # Standing of reached axioms and quotients

The role lookups below use the full table representation at the actual optional limit.
They require neither a prefix model nor an unrestricted core-load contract. The checked
record producer uses the run store to identify the loader's bytes, then extracts the
axiom-standing or quotient-role observation. Reachable non-block origins exclude inert
axioms. The reachable graph consumes the edge-safety clause produced by the guarded walk.
-/

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Claim
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

/-- A full context at either limit has no user axioms. -/
theorem RCLimRep.axiomsNil {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} {h : Heap F} {rc : SourceValue F} (hrc : RCLimRep t bAddr lim h rc) :
    Decl.RCAxiomsNil h rc := by
  obtain ⟨tbl, -, ⟨n, -, -, hl⟩ | ⟨-, hl⟩⟩ := hrc.cases
  · exact ⟨_, hl, Or.inl ⟨tbl, .field (n : F), rfl⟩⟩
  · exact ⟨_, hl, Or.inr ⟨tbl, rfl⟩⟩

/-- A successful role test binds the address to that role, at either optional limit. -/
theorem role_is_lim_spec {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address}
    {lim : Option Nat} {ro : Ix.Kernel.Role} {rc ap : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hrc : RCLimRep t bAddr lim h rc) (ha : S0.addr h ap a)
    (ev : ObsFn W "KernelRoles::role_is" [rc, ap, .field (roleNum ro)] h (.field 1) h' cs) :
    t.addressOf? ro = some a := by
  match Obs.«KernelRoles::role_is».obs ev with
  | .n0_n0 (he88 := he) .. => exact (one_ne_zero (Value.field.inj he)).elim
  | .other (he102 := he) .. => exact (one_ne_zero (Value.field.inj he)).elim
  | .n0_other (x10 := x10) (ev23 := ev23) (op47 := op47) (op17 := op17) .. =>
    have hidx := (role_index_of_lim_spec hrc ha ev23).2
    obtain rfl := RolesAux.evalBinOp_add_field_inv op47
    obtain ⟨x, hx1, hx2⟩ := RolesAux.evalBinOp_sub_eq_zero_inv op17
    have hx : x10 = .field (roleNum ro + 1) := hx1.trans hx2.symm
    rcases hidx with ⟨hz, -⟩ | ⟨ro', hr, hb⟩
    · exact (RolesAux.roleNum_add_one_ne_zero ro (Value.field.inj (hx.symm.trans hz))).elim
    · obtain rfl := RolesAux.roleNum_add_one_inj (Value.field.inj (hx.symm.trans hr))
      exact hb

/-- Without user axioms or an inert role, a nonzero standing answer is a standard axiom role. -/
theorem axiom_standing_lim_spec {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address}
    {lim : Option Nat} {rc ap r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrc : RCLimRep t bAddr lim h rc) (ha : S0.addr h ap a) (hin : ¬ InertAt t a)
    (ev : ObsFn W "KernelRoles::axiom_standing" [rc, ap] h r h' cs) (hne : r ≠ .field 0) :
    ∃ ro ∈ Typing.standingRoles, t.addressOf? ro = some a := by
  match Obs.«KernelRoles::axiom_standing».obs ev with
  | .n0 (ev14 := ev14) (ev58 := ev58) (ev36 := ev36) (ev114 := ev114) (ev92 := ev92) .. =>
    obtain ⟨rfl, htbl⟩ := role_ctx_table_lim_spec hrc ev14
    obtain ⟨rfl, rfl, -⟩ := addr_index_lookup htbl ha ev58 ev36
    obtain ⟨rfl, rfl, -⟩ := Decl.role_ctx_axioms_nil hrc.axiomsNil ev114
    rw [← Obs.Names.«RBTreeMap::rbtree_map_lookup_or_default<Field>».symbol] at ev92
    match Obs.«RBTreeMap::rbtree_map_lookup_or_default».obs ev92 with
    | .Nil (he18 := he) .. => exact (hne he).elim
    | .Node_n0 (hv_yxogouup := hv) .. => simp [addrMapEnum] at hv
    | .Node_n1 (hv_yxogouup := hv) .. => simp [addrMapEnum] at hv
    | .Node_other (hv_yxogouup := hv) .. => simp [addrMapEnum] at hv
  | .other_n0 (he170 := he) .. => exact (hne he).elim
  | .other_other_n0 (he212 := he) .. => exact (hne he).elim
  | .other_other_other (ev14 := ev14) (ev58 := ev58) (ev36 := ev36)
      (hne130 := hn) (ev147 := ev147) (hne173 := hs) .. =>
    obtain ⟨rfl, htbl⟩ := role_ctx_table_lim_spec hrc ev14
    obtain ⟨rfl, rfl, hi⟩ := addr_index_lookup htbl ha ev58 ev36
    rcases hi with ⟨hz, -⟩ | ⟨ro, hr, hb⟩
    · exact (hn hz).elim
    · rw [hr] at ev147
      rcases Decl.axiom_role_standing_spec ev147 hs with h | h | h | h
      · subst ro; exact ⟨.propext, by decide, hb⟩
      · subst ro; exact ⟨.choice, by decide, hb⟩
      · subst ro; exact ⟨.quotSound, by decide, hb⟩
      · exact (hin ⟨ro, h, hb⟩).elim

/-- Every successful quotient check pins the address to the quotient role of its kind. -/
theorem check_quot_lim_standing {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address}
    {lim : Option Nat} {rc ap kind r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrc : RCLimRep t bAddr lim h rc) (ha : S0.addr h ap a)
    (ev : ObsFn W "KernelCheck::check_quot" [rc, ap, kind] h r h' cs) :
    ∃ ro ∈ Typing.standingRoles, t.addressOf? ro = some a := by
  obtain ⟨_, _, _, _, _, _, seg, ev100, heq, -, -, -⟩ := Obs.«KernelCheck::check_quot».obs ev
  rw [heq] at ev100
  match seg with
  | .Typ (ev22 := ev22) .. =>
    obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::role_quot».obs ev22
    exact ⟨.quot, by decide, role_is_lim_spec (ro := .quot) hrc ha ev100⟩
  | .Ctor (ev36 := ev36) .. =>
    obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::role_quot_mk».obs ev36
    exact ⟨.quotMk, by decide, role_is_lim_spec (ro := .quotMk) hrc ha ev100⟩
  | .Lift (ev50 := ev50) .. =>
    obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::role_quot_lift».obs ev50
    exact ⟨.quotLift, by decide, role_is_lim_spec (ro := .quotLift) hrc ha ev100⟩
  | .Ind (ev64 := ev64) .. =>
    obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::role_quot_ind».obs ev64
    exact ⟨.quotInd, by decide, role_is_lim_spec (ro := .quotInd) hrc ha ev100⟩

/-- The standing role is produced from the actual check of an in-logic axiom or quotient. -/
theorem checkedLimAt_standing {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {bAddr a : _root_.Address} {lim : Option Nat} {c : Ixon.Constant}
    (hS : LoadedReads.RunStore calls E₀) (hc : recordOf E₀ a = some c)
    (hl : InLogic c) (hin : ¬ InertAt t a)
    (hk : (∃ ax, c.info = .axio ax) ∨ ∃ q, c.info = .quot q)
    (hchk : CheckedLimAt calls bAddr t a lim) :
    ∃ ro ∈ Typing.standingRoles, t.addressOf? ro = some a := by
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
    have ext' := evscope.heap_extends.trans (ext.trans (evsort.heap_extends.trans evsafe.heap_extends))
    exact axiom_standing_lim_spec (hrc.mono ext') (S0.addr_mono ext' ha_chk) hin evstand hne
  · simp only [L1.GetCITraceResult, hq] at htrace
    obtain ⟨_, _, v', _, _, hld', htr⟩ := htrace
    have hv : v' = v := Except.ok.inj (hld'.symm.trans hld)
    subst v'
    obtain ⟨_, tp, _, hv, _⟩ := htr
    rw [hv] at ev_chk
    obtain ⟨_, _, _, mscope, _, malloc, _, _, _, _, _, evscope, hm,
      evsort, evsafe, evquot, _⟩ := Decl.check_const_quot_inv ev_chk
    have ext : Heap.Extends mscope malloc := by rw [hm]; exact Heap.Extends.snoc _ _
    have ext' := evscope.heap_extends.trans (ext.trans (evsort.heap_extends.trans evsafe.heap_extends))
    exact check_quot_lim_standing (hrc.mono ext') (S0.addr_mono ext' ha_chk) evquot

/-- Reached axioms/quotients have standing once their safety is produced. No standing
hypothesis is assumed: checks and the seed/ref/owner origins supply it. -/
theorem TopWalkCore.reach_standing
    {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (hW : TopWalkCore calls bAddr t seeds E₀ lim Top rank)
    (hsafe : ∀ a, TopReach t E₀ seeds a → SourceSafe E₀ a) :
    StandingAt t E₀ (TopReach t E₀ seeds) := by
  intro a c ha hc hk
  have hnb : ¬ Typing.IsBlock c := by
    rintro ⟨ms, hm⟩
    rcases hk with ⟨ax, hax⟩ | ⟨q, hq⟩
    · cases hax.symm.trans hm
    · cases hq.symm.trans hm
  obtain ⟨c', hc', hchk⟩ := hW.checked a (hW.reach_subset ha)
  have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst c'
  rcases hchk with ⟨ms, hm, _⟩ | hchk
  · exact (hnb ⟨ms, hm⟩).elim
  · exact checkedLimAt_standing hW.runStore hc (hsafe a ha c hc).1
      (hW.reach_not_inert_of_not_block ha hc hnb) hk hchk

/-- The unchanged assembly graph follows from the concrete checks and guarded edge safety. -/
theorem TopWalkCore.reach_graph
    {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (hW : TopWalkCore calls bAddr t seeds E₀ lim Top rank)
    (hedge : ∀ a x, Top a → SourceSafe E₀ a → Typing.UsedRef E₀ a x →
      ¬ Typing.Covered t x → SourceSafe E₀ x) :
    Typing.TopGraph t E₀ seeds (TopReach t E₀ seeds) rank :=
  hW.restrictReach.graph (hW.reach_standing fun _ ha => hW.reach_safe hedge ha)

end IxVM.Refinement.Claim
