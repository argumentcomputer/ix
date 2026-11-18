import IxVMRefinement.RoleVal.TableParseLoad
import IxVMRefinement.Binding.TableAdmitsCheck
import IxVMRefinement.Binding.ClaimExport

/-! # The loaded role table admits: from the parse and the evidence clauses

`LoadedTableAdmits` (`Binding/ClaimExport.lean`) from the load's parse
(`RoleVal.load_role_table_parse`: the bytes hashed are the binding section of `parsedTable`, its
hash the binding address, the node holding exactly its pairs and evidence), the loop
`assert_all_roles_bound` (every role bound, through `RoleVal.assert_all_roles_bound_spec`, which
reads only `Core.TableRep`), and two closed statements about observed runs, the clauses of
`RoleTable.check` the circuit establishes outside the load's parse:

* `LoadEvidenceHasEquations`: the load's `evidence_roles_have_equations` over the evidence map it
  built: every entry read is a role with equations;
* `ValidationsCheckEvidence`: the roles' validations under `admit_all_groups`: every evidence
  entry of a role with equations matches them, and every role with equations has one.

Everything else of `check` (version, no role and no address twice, block and dependency closure)
is read off the parse and the bound roles here.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Refinement.Core

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

/-! ## The two clauses established outside the parse -/

/-- **The load's `evidence_roles_have_equations`**: over an evidence map with exactly the entries
`le`, the observed walk gives every entry's role equations. -/
def LoadEvidenceHasEquations : Prop :=
  ∀ (le : List (Ix.Kernel.Role × List (Ix.Kernel.Evidence _root_.Address)))
    (ents : List (Nat × SourceValue F)) (evMap v : SourceValue F) (hE hE' : Heap F)
    (cs : List (Call F)),
    RoleVal.RoleMapEntries roleEvMapEnum hE ents evMap → RoleVal.EvidenceEntriesOf hE le ents →
    ObsFn Core.W "KernelRoles::evidence_roles_have_equations" [evMap] hE v hE' cs →
    ∀ p ∈ le, RoleVal.roleHasEquations p.1 = true

/-- **The evidence clauses of `RoleTable.check` that the roles' validations establish**: for a
table node whose maps hold only `t`'s entries (`Core.TableRep`), `t`'s evidence roles distinct,
every role bound, and the observed loops `assert_all_roles_bound` and `admit_all_groups` on it,
every evidence entry of a role with equations matches its equations, and every role with
equations has an entry. -/
def ValidationsCheckEvidence : Prop :=
  ∀ (t : Ix.Kernel.RoleTable) (x_tbl v r : SourceValue F) (h₁ h₂ h' : Heap F)
    (cs₂ cs₃ : List (Call F)),
    Core.TableRep t h₁ x_tbl → (t.evidence.toList.map (·.1)).Nodup →
    (∀ p ∈ t.evidence.toList, p.2.size < 256) → AllBound t →
    ObsFn Core.W "KernelRoles::assert_all_roles_bound" [x_tbl, .field 0] h₁ v h₂ cs₂ →
    ObsFn Core.W "KernelRoles::admit_all_groups" [x_tbl, .field 0] h₂ r h' cs₃ →
    (∀ p ∈ t.evidence.toList, RoleVal.roleHasEquations p.1 = true →
      (p.2.size == ((Ix.Kernel.Role.spec (md := .anon)) p.1).evidenceAllowed.length &&
        (p.2.toList.zip ((Ix.Kernel.Role.spec (md := .anon)) p.1).evidenceAllowed).all
          (fun x => x.1.allowedBy x.2)) = true) ∧
    (∀ ro : Ix.Kernel.Role, RoleVal.roleHasEquations ro = true →
      ro ∈ t.evidence.toList.map (·.1))

/-! ## Helpers -/

private theorem find_fst_of_mem_nodup {l : List (Ix.Kernel.Role × _root_.Address)}
    (hnd : (l.map (·.1)).Nodup) {ro : Ix.Kernel.Role} {a : _root_.Address}
    (hm : (ro, a) ∈ l) :
    (l.find? (·.1 == ro)).map (·.2) = some a := by
  induction l with
  | nil => cases hm
  | cons p ls ih =>
    rcases p with ⟨r', a'⟩
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [List.find?]
    by_cases heq : (r' == ro) = true
    · rw [heq]
      have hr : r' = ro := beq_iff_eq.mp heq
      subst hr
      rcases List.mem_cons.mp hm with hhead | htail
      · injection hhead with _ ha
        subst ha
        rfl
      · exact absurd (List.mem_map_of_mem (f := (·.1)) htail) hnd.1
    · have hfalse : (r' == ro) = false := Bool.eq_false_iff.mpr heq
      rw [hfalse]
      rcases List.mem_cons.mp hm with hhead | htail
      · injection hhead with hr _
        subst hr
        exact absurd (beq_self_eq_true ro) heq
      · exact ih hnd.2 htail

theorem roles_nodup {α : Type} {l : List (Ix.Kernel.Role × α)}
    (h : l.Pairwise (fun p q => p.1.idx < q.1.idx)) : (l.map (·.1)).Nodup :=
  List.pairwise_map.mpr (h.imp fun hlt heq => by rw [heq] at hlt; exact Nat.lt_irrefl _ hlt)

set_option maxRecDepth 100000 in
theorem evidenceAllowed_isEmpty_eq' (ro : Ix.Kernel.Role) :
    ((Ix.Kernel.Role.spec (md := .anon)) ro).evidenceAllowed.isEmpty =
      !RoleVal.roleHasEquations ro := by
  cases ro <;> decide

theorem admitBinding_of {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hh : Address.admissionHash b.bytes = b.address)
    (hof : Ix.Kernel.RoleTable.ofBytes b.bytes = some t) (hchk : t.check = .ok ()) :
    Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t := by
  unfold Ix.Kernel.Admission.admitBinding
  simp only [hh, decide_true, ↓reduceIte, hof, hchk] <;> rfl

/-! ## The theorem -/

/-- **The loaded table admits, from the two clauses established outside the parse.** -/
theorem loadedTableAdmits_of (hval : ValidationsCheckEvidence)
    (hhas : LoadEvidenceHasEquations) : LoadedTableAdmits := by
  intro a x_a x_tbl v r h h₁ h₂ h' cs₁ cs₂ cs₃ ha ev_load ev_bound ev_admit
  obtain ⟨bytes, lb, le, hE, evMap, vE, hE', csE, evEnts, hhashed, hblk, hwire, henc, hascB,
    hascE, hnode, -, hentE, hevE, ev_eq⟩ := RoleVal.load_role_table_parse ha ev_load
  obtain ⟨t, ht⟩ : ∃ t, RoleVal.parsedTable Ix.Kernel.specVersion lb le = t := ⟨_, rfl⟩
  rw [ht] at hwire henc
  have hroles : t.bound.toList = lb.map (fun p => (p.1, ixAddr p.2)) := by
    rw [← ht]; simp [RoleVal.parsedTable]
  have hevs : t.evidence.toList = le.map (fun p => (p.1, p.2.toArray)) := by
    rw [← ht]; simp [RoleVal.parsedTable]
  have hver : t.version = Ix.Kernel.specVersion := by rw [← ht]; rfl
  have haddr : ∀ ro b, (ro, b) ∈ lb → t.addressOf? ro = some (ixAddr b) := by
    intro ro b hm
    unfold Ix.Kernel.RoleTable.addressOf?
    rw [← Array.find?_toList, hroles]
    exact find_fst_of_mem_nodup (roles_nodup (List.pairwise_map.mpr hascB))
      (List.mem_map.mpr ⟨(ro, b), hm, rfl⟩)
  obtain ⟨bp, byRole, byAddr, evm, ents, es, evEnts', hl, hbp, hent, hbnd, hbst, hidx, hevm,
    hev⟩ := hnode
  -- the sound representation of `t`
  have hBound : RoleMapAll roleAddrMapEnum (BoundEntry t) h₁ byRole := by
    refine hent.toAll (fun q hq => ?_)
    obtain ⟨p, hp, hk, hrep⟩ := RoleVal.forall₂_mem_right hbnd q hq
    exact ⟨p.1, p.2, by rw [hk], hrep, haddr p.1 p.2 hp⟩
  have hIndex : ∀ p ∈ es, IndexEntry t h₁ p.1 p.2 := by
    intro p hp
    rcases (hidx p.1 p.2).mp hp with h0 | ⟨ro, hm, hw⟩
    · cases h0
    · exact ⟨ro, hw, haddr ro p.1 hm⟩
  have hEvid : RoleMapAll roleEvMapEnum (EvidenceEntry t) h₁ evm := by
    refine hevm.toAll (fun q hq => ?_)
    obtain ⟨p, hp, hk, hrep⟩ := RoleVal.forall₂_mem_right hev q hq
    refine ⟨p.1, p.2.toArray, by rw [hk], ?_, by simpa using hrep⟩
    rw [hevs]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  have htrep : Core.TableRep t h₁ x_tbl :=
    ⟨bp, byRole, byAddr, evm, hl, hBound, Claim.addrMapAll_of_rbtreeEntries hbst.1 hIndex, hEvid⟩
  -- every role is bound
  have hallb : AllBound t := fun ro =>
    RoleVal.assert_all_roles_bound_spec 108 0 rfl htrep
      (by rw [Nat.cast_zero]; exact ev_bound) ro (Nat.zero_le _)
  have hall : ∀ ro : Ix.Kernel.Role, ro ∈ t.bound.toList.map (·.1) := by
    intro ro
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hallb ro)
    exact List.mem_map.mpr ⟨(ro, a'), Claim.mem_bound_of_addressOf_eq_some ha', rfl⟩
  -- no role, no address, no evidence role twice
  have hrnd : (t.bound.toList.map (·.1)).Nodup := by
    rw [hroles]
    exact roles_nodup (List.pairwise_map.mpr hascB)
  have hend : (t.evidence.toList.map (·.1)).Nodup := by
    rw [hevs]
    exact roles_nodup (List.pairwise_map.mpr hascE)
  have hinj : ∀ p ∈ lb, ∀ q ∈ lb, p.2 = q.2 → p.1 = q.1 := by
    intro p hp q hq he
    have h1 : (p.2, (.field (roleNum p.1 + 1) : SourceValue F)) ∈ es :=
      (hidx _ _).mpr (.inr ⟨p.1, hp, rfl⟩)
    have hq' : (q.1, p.2) ∈ lb := by rw [he]; exact hq
    have h2 : (p.2, (.field (roleNum q.1 + 1) : SourceValue F)) ∈ es :=
      (hidx _ _).mpr (.inr ⟨q.1, hq', rfl⟩)
    have e := (Claim.lookupEntries_eq_of_mem (dflt := .field 0) hbst.2 h1).symm.trans
      (Claim.lookupEntries_eq_of_mem hbst.2 h2)
    exact RolesAux.roleNum_add_one_inj (Value.field.inj e)
  have hand : (t.bound.toList.map (·.2)).Nodup := by
    rw [hroles, List.map_map]
    exact List.pairwise_map.mpr (hascB.imp_of_mem (fun {p q} hp hq hlt heq => by
      have e := hinj p hp q hq (Claim.ixAddr_injective heq)
      rw [e] at hlt
      exact Nat.lt_irrefl _ hlt))
  -- the evidence clauses
  have hsz : ∀ p ∈ t.evidence.toList, p.2.size < 256 := fun p hp =>
    (((Ix.Kernel.RoleTable.wireWF_iff t).mp hwire).2.2.2.2.1 p hp).1
  obtain ⟨hvA, hvB⟩ := hval t x_tbl v r h₁ h₂ h' cs₂ cs₃ htrep hend hsz hallb ev_bound ev_admit
  have hheq := hhas le evEnts evMap vE hE hE' csE hentE hevE ev_eq
  have hevc : ∀ p ∈ t.evidence.toList,
      ((Ix.Kernel.Role.spec (md := .anon)) p.1).evidenceAllowed.isEmpty = false ∧
      (p.2.size == ((Ix.Kernel.Role.spec (md := .anon)) p.1).evidenceAllowed.length &&
        (p.2.toList.zip ((Ix.Kernel.Role.spec (md := .anon)) p.1).evidenceAllowed).all
          (fun x => x.1.allowedBy x.2)) = true := by
    intro p hp
    have hp' := hp
    rw [hevs] at hp'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp'
    have hq1 : RoleVal.roleHasEquations q.1 = true := hheq q hq
    refine ⟨?_, hvA _ hp hq1⟩
    rw [evidenceAllowed_isEmpty_eq', hq1]
    rfl
  have hcov : ∀ ro : Ix.Kernel.Role,
      ((Ix.Kernel.Role.spec (md := .anon)) ro).evidenceAllowed.isEmpty = false →
      ro ∈ t.evidence.toList.map (·.1) := by
    intro ro hE0
    apply hvB ro
    have e := evidenceAllowed_isEmpty_eq' ro
    rw [hE0] at e
    cases hr : RoleVal.roleHasEquations ro
    · rw [hr] at e
      cases e
    · rfl
  have hchk : t.check = .ok () := check_ok_of hver hrnd hand hall hend hevc hcov
  have hwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [hchk]
    rfl
  refine ⟨⟨bytes.toArray⟩, t, hhashed, ?_, hwf, bp, byRole, byAddr, evm, hl, hbp, hBound,
    ⟨es, hbst, hIndex, ?_⟩, hEvid⟩
  · refine admitBinding_of (by rw [Address.admissionHash_eq]; exact hblk) ?_ hchk
    refine (Ix.Kernel.RoleTable.ofBytes_eq_some_iff _ _).mpr ⟨hwire, ?_⟩
    unfold Ix.Kernel.RoleTable.toBytes
    rw [henc]
  · intro ro a' hm
    rw [hroles] at hm
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hm
    simp only [Prod.mk.injEq] at hqe
    obtain ⟨rfl, rfl⟩ := hqe
    exact ⟨q.2, rfl, (hidx _ _).mpr (.inr ⟨q.1, hq, rfl⟩)⟩

/-! ## The load's `evidence_roles_have_equations` -/


theorem op_equation_count_val {ro : Ix.Kernel.Role} {r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {g : F}
    (ht : RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_count.body)
      (roleNum ro) = some g)
    (ev : ObsFn W "KernelRoleSpec::op_equation_count" [.field (roleNum ro)] h r h' calls) :
    r = .field g ∧ h' = h := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.op_equation_count.lookup
    (by simp [IxVM.KernelRoleSpec.op_equation_count, ControlLower.hasControl]) ev
  have hp : (IxVM.KernelRoleSpec.op_equation_count.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["r"] := rfl
  have hb : IxVM.KernelRoleSpec.op_equation_count.body =
      .matchValue (.var "r") (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_count.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨_, _, bs3, body4, _, _, d7, sel8, d9, -⟩ := d0.matchValue_inv
  obtain ⟨l10, rfl, -⟩ := d7.var_inv
  simp at l10
  subst l10
  obtain ⟨rfl, rfl⟩ := RolesAux.selectArm_litTable ht sel8
  obtain ⟨rfl, rfl, -⟩ := d9.literal_inv
  exact ⟨rfl, rfl⟩

theorem eqns_equation_count_val {ro : Ix.Kernel.Role} {r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {g : F}
    (ht : RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.eqns_equation_count.body)
      (roleNum ro) = some g)
    (ev : ObsFn W "KernelRoleSpec::eqns_equation_count" [.field (roleNum ro)] h r h' calls) :
    r = .field g ∧ h' = h := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.eqns_equation_count.lookup
    (by simp [IxVM.KernelRoleSpec.eqns_equation_count, ControlLower.hasControl]) ev
  have hp : (IxVM.KernelRoleSpec.eqns_equation_count.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["r"] := rfl
  have hb : IxVM.KernelRoleSpec.eqns_equation_count.body =
      .matchValue (.var "r") (RolesAux.matchArms IxVM.KernelRoleSpec.eqns_equation_count.body) :=
    rfl
  rw [hp, hb] at d0
  obtain ⟨_, _, bs3, body4, _, _, d7, sel8, d9, -⟩ := d0.matchValue_inv
  obtain ⟨l10, rfl, -⟩ := d7.var_inv
  simp at l10
  subst l10
  obtain ⟨rfl, rfl⟩ := RolesAux.selectArm_litTable ht sel8
  obtain ⟨rfl, rfl, -⟩ := d9.literal_inv
  exact ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- The two equation counts of a role (decided over the 108 roles): both tables answer, and
their sum is zero for a role without equations only. -/
theorem counts_table (ro : Ix.Kernel.Role) :
    (match RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_count.body)
        (roleNum ro),
      RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.eqns_equation_count.body)
        (roleNum ro) with
     | some g₁, some g₂ => decide (g₁ + g₂ = 0) || RoleVal.roleHasEquations ro
     | _, _ => false) = true := by
  cases ro <;> decide +kernel

/-- **The walk of `evidence_roles_have_equations`**: every key of the evidence map is a role
with equations. -/
theorem evidence_roles_have_equations_walk {h₀ : Heap F} :
    ∀ {ents : List (Nat × SourceValue F)} {tree : SourceValue F},
      RoleVal.RoleMapEntries roleEvMapEnum h₀ ents tree →
      (∀ q ∈ ents, ∃ ro : Ix.Kernel.Role, ro.idx = q.1) →
      ∀ {v : SourceValue F} {h h' : Heap F} {cs : List (Call F)}, Heap.Extends h₀ h →
        ObsFn W "KernelRoles::evidence_roles_have_equations" [tree] h v h' cs →
        ∀ q ∈ ents, ∀ ro : Ix.Kernel.Role, ro.idx = q.1 → RoleVal.roleHasEquations ro = true := by
  intro ents tree he
  induction he with
  | nil => intro _ _ _ _ _ _ _ q hq; cases hq
  | @node c k v0 lp rp lv rv ls rs hl hr rl rr ihl ihr =>
    intro hkeys v h h' cs ext ev q hq ro hro
    match Obs.«KernelRoles::evidence_roles_have_equations».obs ev with
    | .Nil (hv15 := hv) .. =>
      injection hv with _ hc _
      exact absurd hc (by decide)
    | .Node (hv27 := hv) (ev101 := ev101) (ev115 := ev115) (op95 := op95) (ev80 := ev80)
        (heq130 := heq) (ld154 := ldl) (ev144 := evl) (ld171 := ldr) (ev161 := evr) .. =>
      injection hv with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, hxr, -, hxl, hxr'⟩ := hargs
      subst hxr hxl hxr'
      have ext70 := ext.trans (ev101.heap_extends.trans (ev115.heap_extends.trans
        ev80.heap_extends))
      obtain rfl := Claim.loadValue_eq_inj ldl (ext70.loadValue_eq hl)
      have ext132 := ext70.trans evl.heap_extends
      obtain rfl := Claim.loadValue_eq_inj ldr (ext132.loadValue_eq hr)
      simp only [List.append_assoc, List.singleton_append, List.mem_append, List.mem_cons] at hq
      have hkeysL : ∀ q ∈ ls, ∃ ro : Ix.Kernel.Role, ro.idx = q.1 :=
        fun q hq => hkeys q (by simp [hq])
      have hkeysR : ∀ q ∈ rs, ∃ ro : Ix.Kernel.Role, ro.idx = q.1 :=
        fun q hq => hkeys q (by simp [hq])
      rcases hq with hq | rfl | hq
      · exact ihl hkeysL ext70 evl q hq ro hro
      · -- this node's key
        simp only at hro
        subst hro
        have htab := counts_table ro
        cases h1 : RolesAux.evalLitTable
            (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_count.body) (roleNum ro) with
        | none => rw [h1] at htab; cases htab
        | some g₁ =>
          cases h2 : RolesAux.evalLitTable
              (RolesAux.matchArms IxVM.KernelRoleSpec.eqns_equation_count.body) (roleNum ro) with
          | none => rw [h1, h2] at htab; cases htab
          | some g₂ =>
            rw [h1, h2] at htab
            obtain ⟨rfl, -⟩ := op_equation_count_val h1 ev101
            obtain ⟨rfl, -⟩ := eqns_equation_count_val h2 ev115
            simp only [evalBinOp, Except.ok.injEq] at op95
            subst op95
            obtain ⟨hz, -⟩ := Lib.is_zero_spec ev80
            rw [heq] at hz
            have hne : g₁ + g₂ ≠ 0 := by
              intro h0
              rw [h0] at hz
              simp at hz
            simpa [hne] using htab
      · exact ihr hkeysR ext132 evr q hq ro hro

/-- **`LoadEvidenceHasEquations` holds of every observed load.** -/
theorem loadEvidenceHasEquations : LoadEvidenceHasEquations := by
  intro le ents evMap v hE hE' cs hent hev ev p hp
  obtain ⟨q, hq, hk, -⟩ := RoleVal.forall₂_mem_left hev p hp
  have hkeys : ∀ q ∈ ents, ∃ ro : Ix.Kernel.Role, ro.idx = q.1 := by
    intro q hq
    obtain ⟨p', -, hk', -⟩ := RoleVal.forall₂_mem_right hev q hq
    exact ⟨p'.1, hk'.symm⟩
  exact evidence_roles_have_equations_walk hent hkeys (Heap.Extends.refl _) ev q hq p.1 hk.symm

/-- **The loaded table admits, from the evidence clauses of the roles' validations.** -/
theorem loadedTableAdmits_of_validations (hval : ValidationsCheckEvidence) :
    LoadedTableAdmits :=
  loadedTableAdmits_of hval loadEvidenceHasEquations

end IxVM.Refinement.Binding
