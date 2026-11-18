import IxVMRefinement.RoleVal.GroupAdmit
import IxVMRefinement.Claim.TopWalkCheck

/-! # The walk of a role's bound record in its validation, at the group's validation limit

`KernelRoles::validate_role` walks the record bound to a role (`KernelClaim::run_check_transitive`
under the role context of the group's validation) for a block member outside the quotient
package, an operation, a definition specified by equations (`roleWalksBound`), and for the
fourteen anchors `KernelRoles::anchor_walked` lists (`anchorWalked`: `Bool` and `And` with their
constructors and recursor, `List` with its constructors, `String`, `String.ofList`, `Char`,
`Char.ofNat`).

* `anchor_walked_full`: the value of `anchor_walked` at a role.
* `validate_role_bound_walk`: the observed walk itself: the `run_check_transitive` call on the
  role's bound address under the role context at the group's validation limit, among the
  validation's calls.
* `validate_role_lim_walks`: what that walk records, with its limit kept: a closed list of
  records each checked under the role context at the group's validation limit
  (`Claim.TopRec … (some (groupValLimit g))`, `Claim.TopRecsClosed`), holding the role's bound
  record. A reference of a walked record is a record of the list or is bound to a walked role
  in force at the limit (`Claim.CoveredAt`), which that role's own group walks.
* `ValidateRoleIn.lim_walks`: the same from the observed validation of the role.

`validate_role_full_walks` (in `GroupAdmit`) gives the walked records of a `roleWalksBound`
role with the limit of each check left existential and no record for an anchor; this file is
the form the binding fold's admission reads.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.RoleVal

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

/-! ## `KernelRoles::anchor_walked` -/

/-- The value `KernelRoles::anchor_walked` gives a role. -/
def anchorWalkedF (ro : Ix.Kernel.Role) : F :=
  (RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoles.anchor_walked.body)
    (roleNum ro)).getD 0

/-- **An anchor whose bound record its validation walks.** -/
def anchorWalked (ro : Ix.Kernel.Role) : Bool := decide (anchorWalkedF ro = 1)

set_option maxRecDepth 100000 in
theorem anchor_walked_table (ro : Ix.Kernel.Role) :
    RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoles.anchor_walked.body)
      (roleNum ro) = some (anchorWalkedF ro) := by
  cases ro <;> decide

theorem anchor_walked_full {ro : Ix.Kernel.Role} {r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn W "KernelRoles::anchor_walked" [.field (roleNum ro)] h r h' calls) :
    r = .field (anchorWalkedF ro) ∧ h' = h := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoles.anchor_walked.lookup
    (by simp [IxVM.KernelRoles.anchor_walked, ControlLower.hasControl]) ev
  have hp : (IxVM.KernelRoles.anchor_walked.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["r"] := rfl
  have hb : IxVM.KernelRoles.anchor_walked.body =
      .matchValue (.var "r") (RolesAux.matchArms IxVM.KernelRoles.anchor_walked.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨v1, m2, bs3, body4, _, _, d7, sel8, d9, -⟩ := d0.matchValue_inv
  obtain ⟨l10, rfl, -⟩ := d7.var_inv
  simp at l10
  subst l10
  obtain ⟨rfl, rfl⟩ := RolesAux.selectArm_litTable (anchor_walked_table ro) sel8
  obtain ⟨rfl, rfl, -⟩ := d9.literal_inv
  exact ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- The walked anchors are the fourteen the source lists. -/
theorem anchorWalked_iff (ro : Ix.Kernel.Role) :
    anchorWalked ro = true ↔
      ro ∈ [Ix.Kernel.Role.bool, .boolFalse, .boolTrue, .boolRec, .and, .andIntro, .andRec,
        .list, .listNil, .listCons, .string, .stringOfList, .char, .charOfNat] := by
  cases ro <;> decide

set_option maxRecDepth 100000 in
/-- A role whose bound record is walked is specified as a block member, an anchor, an operation
or by equations. -/
theorem specKind_of_boundWalk (ro : Ix.Kernel.Role) :
    (roleWalksBound ro = true ∨ anchorWalked ro = true) →
      roleSpecKindNat ro = 0 ∨ roleSpecKindNat ro = 1 ∨ roleSpecKindNat ro = 2 ∨
        roleSpecKindNat ro = 5 := by
  cases ro <;> decide

set_option maxRecDepth 100000 in
/-- Among the block members, the walked ones are `roleWalksBound`. -/
theorem walksBound_of_specKind_zero (ro : Ix.Kernel.Role) :
    roleSpecKindNat ro = 0 → (roleWalksBound ro = true ∨ anchorWalked ro = true) →
      roleWalksBound ro = true := by
  cases ro <;> decide

set_option maxRecDepth 100000 in
/-- Among the anchors, the walked ones are `anchorWalked`. -/
theorem anchorWalkedF_of_specKind_one (ro : Ix.Kernel.Role) :
    roleSpecKindNat ro = 1 → (roleWalksBound ro = true ∨ anchorWalked ro = true) →
      anchorWalkedF ro = 1 := by
  cases ro <;> decide

/-! ## The observed walk of the bound record -/

/-- **The walk of a role's bound record in its validation, as observed**: for a role whose
bound record the validation walks, the `KernelClaim::run_check_transitive` call on the bound
address under the role context at the group's validation limit, among the validation's calls. -/
theorem validate_role_bound_walk {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {g : Nat} {ro : Ix.Kernel.Role}
    {x_rc x_tbl r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : Claim.RCFullRep t bAddr (groupValLimit g) h x_rc)
    (htbl : Claim.TableFullRep t bAddr h x_tbl)
    (ev : ObsFn W "KernelRoles::validate_role" [x_rc, x_tbl, .field (roleNum ro)] h r h' calls)
    (hw : roleWalksBound ro = true ∨ anchorWalked ro = true) :
    ∃ (a : _root_.Address) (x_a r_w : SourceValue F) (h_w h_w' : Heap F)
      (cs_w : List (Call F)),
      t.addressOf? ro = some a ∧
      Claim.RCFullRep t bAddr (groupValLimit g) h_w x_rc ∧
      S0.addr h_w x_a a ∧
      ObsFn W "KernelClaim::run_check_transitive" [x_rc, x_a] h_w r_w h_w' cs_w ∧
      ∀ cl ∈ cs_w, cl ∈ calls := by
  cases Obs.«KernelRoles::validate_role».obs ev with
  | n0 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs140
      ev14 ev47 _ ev80 ev100 _ ev124 ev142 hc183 =>
    obtain ⟨ext_ba, a, ha_m2, had⟩ := role_bound_addr_uncond htbl.toTableRep ev14
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    have hsk : roleSpecKindNat ro = 0 := by
      cases ro <;> first | exact absurd (Value.field.inj hsk_f) (by decide) | rfl
    have hwb : roleWalksBound ro = true := walksBound_of_specKind_zero ro hsk hw
    have ext_m111 : Heap.Extends m2 m111 :=
      ev47.heap_extends.trans (ev80.heap_extends.trans
        (ev100.heap_extends.trans ev124.heap_extends))
    have hrc_m111 := hrc.mono (ext_ba.trans ext_m111)
    have ha_m111 := S0.addr_mono ext_m111 ha_m2
    cases Obs.«KernelRoles::validate_member».obs ev142 with
    | n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m198' _ cs221'
        ev14' ev50' ev70' ev36' ev101' _ ev208' _ ev223' hc240' =>
      have ext_w : Heap.Extends m111 m198' :=
        ev14'.heap_extends.trans (ev50'.heap_extends.trans (ev70'.heap_extends.trans
          (ev36'.heap_extends.trans (ev101'.heap_extends.trans ev208'.heap_extends))))
      have hsub : ∀ cl ∈ cs221', cl ∈ calls := fun cl hm => by
        rw [hc183]; simp [show cl ∈ cs140 by rw [hc240']; simp [hm]]
      exact ⟨a, _, _, _, _, _, had, hrc_m111.mono ext_w, S0.addr_mono ext_w ha_m111, ev223',
        hsub⟩
    | n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m472' _ cs623'
        ev14' ev50' ev70' ev36' ev101' _ ev319' ev389' ev376' _ ev482' _ _ _ _ _ ev625' hc642' =>
      have ext_w : Heap.Extends m111 m472' :=
        ev14'.heap_extends.trans (ev50'.heap_extends.trans (ev70'.heap_extends.trans
          (ev36'.heap_extends.trans (ev101'.heap_extends.trans (ev319'.heap_extends.trans
            (ev389'.heap_extends.trans (ev376'.heap_extends.trans ev482'.heap_extends)))))))
      have hsub : ∀ cl ∈ cs623', cl ∈ calls := fun cl hm => by
        rw [hc183]; simp [show cl ∈ cs140 by rw [hc642']; simp [hm]]
      exact ⟨a, _, _, _, _, _, had, hrc_m111.mono ext_w, S0.addr_mono ext_w ha_m111, ev625',
        hsub⟩
    | n2 _ _ _ _ _ _ _ _ _ _ _ _ m88' _ _ _ _ _ _ _ _ _ _ _ _ cs735'
        ev14' ev50' ev70' ev36' ev101' _ ev737' hc754' =>
      have ext_w : Heap.Extends m111 m88' :=
        ev14'.heap_extends.trans (ev50'.heap_extends.trans (ev70'.heap_extends.trans
          (ev36'.heap_extends.trans ev101'.heap_extends)))
      have hsub : ∀ cl ∈ cs735', cl ∈ calls := fun cl hm => by
        rw [hc183]; simp [show cl ∈ cs140 by rw [hc754']; simp [hm]]
      exact ⟨a, _, _, _, _, _, had, hrc_m111.mono ext_w, S0.addr_mono ext_w ha_m111, ev737',
        hsub⟩
    | n3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev101' _ _ _ _ _ _ _ _ =>
      obtain ⟨_, hmk⟩ := role_member_kind_lt3_of_walks hsk hwb ev101'
      rcases hmk with hmk | hmk | hmk <;> exact absurd (Value.field.inj hmk) (by decide)
    | n4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev101' _ _ =>
      obtain ⟨_, hmk⟩ := role_member_kind_lt3_of_walks hsk hwb ev101'
      rcases hmk with hmk | hmk | hmk <;> exact absurd (Value.field.inj hmk) (by decide)
    | n5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev101' _ _ =>
      obtain ⟨_, hmk⟩ := role_member_kind_lt3_of_walks hsk hwb ev101'
      rcases hmk with hmk | hmk | hmk <;> exact absurd (Value.field.inj hmk) (by decide)
    | n6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev101' _ _ =>
      obtain ⟨_, hmk⟩ := role_member_kind_lt3_of_walks hsk hwb ev101'
      rcases hmk with hmk | hmk | hmk <;> exact absurd (Value.field.inj hmk) (by decide)
    | n7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev101' _ _ =>
      obtain ⟨_, hmk⟩ := role_member_kind_lt3_of_walks hsk hwb ev101'
      rcases hmk with hmk | hmk | hmk <;> exact absurd (Value.field.inj hmk) (by decide)
  | n1 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs192
      ev14 ev47 _ ev80 ev100 _ ev124 ev194 hc227 =>
    obtain ⟨ext_ba, a, ha_m2, had⟩ := role_bound_addr_uncond htbl.toTableRep ev14
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    have hsk : roleSpecKindNat ro = 1 := by
      cases ro <;> first | exact absurd (Value.field.inj hsk_f) (by decide) | rfl
    have hF1 : anchorWalkedF ro = 1 := anchorWalkedF_of_specKind_one ro hsk hw
    have ext_h_m111 : Heap.Extends h m111 :=
      ext_ba.trans (ev47.heap_extends.trans (ev80.heap_extends.trans
        (ev100.heap_extends.trans ev124.heap_extends)))
    match Obs.«KernelRoles::validate_anchor».obs ev194 with
    | .n1 (m46 := a46) (m127 := a127) (m140 := a140) (m606 := a606) (m615 := a615)
        (m657 := a657) (cs644 := csw) (ev14 := e14) (ev36 := e36) (ev86 := e86) (ev58 := e58)
        (hm135 := hm) (ev108 := e108) (ev152 := e152) (sg613 := sg) (ev628 := e628)
        (ev667 := e667) (ev646 := e646) (hc684 := hca) .. =>
      have ext_sg : Heap.Extends a140 a606 := by
        cases sg <;> exact ObsFn.heap_extends (by assumption)
      have ext_snoc : Heap.Extends a46 a127 := by
        rw [hm]
        exact Heap.Extends.snoc a46 _
      have ext_a : Heap.Extends m111 a615 :=
        e14.heap_extends.trans (e36.heap_extends.trans (e86.heap_extends.trans
          (e58.heap_extends.trans (ext_snoc.trans (e108.heap_extends.trans
            (e152.heap_extends.trans (ext_sg.trans e628.heap_extends)))))))
      obtain ⟨ext_ba2, a', ha', had'⟩ :=
        role_bound_addr_uncond ((htbl.mono (ext_h_m111.trans ext_a)).toTableRep) e667
      have ha_eq : a' = a := by
        rw [had] at had'
        exact (Option.some.inj had').symm
      subst ha_eq
      have hsub : ∀ cl ∈ csw, cl ∈ calls := fun cl hm' => by
        rw [hc227]; simp [show cl ∈ cs192 by rw [hca]; simp [hm']]
      exact ⟨a', _, _, _, _, _, had, hrc.mono (ext_h_m111.trans (ext_a.trans ext_ba2)), ha',
        e646, hsub⟩
    | .other (ev628 := e628) (hne685 := hne) .. =>
      obtain ⟨hv, -⟩ := anchor_walked_full e628
      rw [hF1] at hv
      exact absurd hv hne
  | n2 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs236
      ev14 ev47 _ ev80 ev100 _ ev124 ev238 hc279 =>
    obtain ⟨ext_ba, a, ha_m2, had⟩ := role_bound_addr_uncond htbl.toTableRep ev14
    have ext_m111 : Heap.Extends m2 m111 :=
      ev47.heap_extends.trans (ev80.heap_extends.trans
        (ev100.heap_extends.trans ev124.heap_extends))
    match Obs.«KernelRoles::validate_op».obs ev238 with
    | .other (heq575 := hbad) .. => exact (zero_ne_one (Value.field.inj hbad)).elim
    | .Defn (m2 := rawHeap) (m200 := m102_op) (m209 := m111_op) (cs270 := cs172)
        (ev14 := rawLoad) (sg207 := sg109) (ev242 := ev144) (ev221 := ev123) (ev272 := ev174)
        (hc544 := hc320) .. =>
      have ext_safe : Heap.Extends rawHeap m102_op := by
        cases sg109 with
        | Safe _ _ he64 _ => rw [he64]
        | other _ heq95 _ _ _ => exact absurd (Value.field.inj heq95) zero_ne_one
      have ext_sg : Heap.Extends m111 m102_op := rawLoad.heap_extends.trans ext_safe
      have ext_w : Heap.Extends m111 m111_op :=
        ext_sg.trans (ev144.heap_extends.trans ev123.heap_extends)
      have hsub_a : ∀ cl ∈ cs172, cl ∈ calls := fun cl hm => by
        rw [hc279]; simp [show cl ∈ cs236 by rw [hc320]; simp [hm]]
      exact ⟨a, _, _, _, _, _, had, hrc.mono (ext_ba.trans (ext_m111.trans ext_w)),
        S0.addr_mono (ext_m111.trans ext_w) ha_m2, ev174, hsub_a⟩
  | n3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    have hsk : roleSpecKindNat ro = 3 := by
      cases ro <;> first | exact absurd (Value.field.inj hsk_f) (by decide) | rfl
    rcases specKind_of_boundWalk ro hw with h0 | h1 | h2 | h5 <;> omega
  | n4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    have hsk : roleSpecKindNat ro = 4 := by
      cases ro <;> first | exact absurd (Value.field.inj hsk_f) (by decide) | rfl
    rcases specKind_of_boundWalk ro hw with h0 | h1 | h2 | h5 <;> omega
  | n5 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs376
      ev14 ev47 _ ev80 ev100 _ ev124 ev378 hc419 =>
    obtain ⟨ext_ba, a, ha_m2, had⟩ := role_bound_addr_uncond htbl.toTableRep ev14
    have ext_m111 : Heap.Extends m2 m111 :=
      ev47.heap_extends.trans (ev80.heap_extends.trans
        (ev100.heap_extends.trans ev124.heap_extends))
    obtain ⟨_, _, _, _, _, _, m101_eq, _, _, m130_eq, _, _, m151_eq, _, _, m182_eq, _,
      v209, m210, cs220, v239, m240, cs250, v280, v281, m283, cs291, m303, cs311, cs326,
      _, sg108, ev140, _, ev192, ev163, ev222, ev252, ev293, ev313, heq322, ev328, hc368⟩ :=
      Obs.«KernelRoles::validate_eqns».obs ev378
    have ext_sg : Heap.Extends m111 m101_eq := by
      cases sg108 with
      | Safe _ _ he63 _ => rw [he63]
      | other _ heq94 _ _ _ => exact absurd (Value.field.inj heq94) zero_ne_one
    have ext_w : Heap.Extends m111 m151_eq :=
      ext_sg.trans (ev140.heap_extends.trans (ev192.heap_extends.trans ev163.heap_extends))
    have hsub_a : ∀ cl ∈ cs220, cl ∈ calls := fun cl hm => by
      rw [hc419]; simp [show cl ∈ cs376 by rw [hc368]; simp [hm]]
    exact ⟨a, _, _, _, _, _, had, hrc.mono (ext_ba.trans (ext_m111.trans ext_w)),
      S0.addr_mono (ext_m111.trans ext_w) ha_m2, ev222, hsub_a⟩

/-! ## The walked records, at the limit -/

/-- **What the walk of a role's bound record records, with its limit**: a closed list of records
each checked under the role context at the group's validation limit, holding the role's bound
record. -/
theorem validate_role_lim_walks {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {g : Nat} {ro : Ix.Kernel.Role}
    {x_rc x_tbl r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : Claim.RCFullRep t bAddr (groupValLimit g) h x_rc)
    (htbl : Claim.TableFullRep t bAddr h x_tbl)
    (ev : ObsFn W "KernelRoles::validate_role" [x_rc, x_tbl, .field (roleNum ro)] h r h' calls)
    (hw : roleWalksBound ro = true ∨ anchorWalked ro = true) :
    ∃ (a : _root_.Address) (recs : List (Claim.TopRec calls bAddr t (some (groupValLimit g)))),
      t.addressOf? ro = some a ∧ Claim.TopRecsClosed recs ∧ a ∈ recs.map (·.addr) := by
  obtain ⟨a, x_a, r_w, h_w, h_w', cs_w, had, hrc_w, ha_w, ev_w, hsub⟩ :=
    validate_role_bound_walk hrc htbl ev hw
  obtain ⟨-, recs, hmem, hcl, -⟩ :=
    Claim.run_check_transitive_lim_spec (lim := some (groupValLimit g))
      (show Claim.RCLimRep t bAddr (some (groupValLimit g)) h_w x_rc from hrc_w) ha_w ev_w
  refine ⟨a, recs.map (Claim.TopRec.mono hsub), had, hcl.mono hsub, ?_⟩
  rw [Claim.map_addr_topRec_mono]
  exact hmem

/-- **The same from the observed validation of the role.** -/
theorem ValidateRoleIn.lim_walks {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {g : Nat} {ro : Ix.Kernel.Role}
    (hv : ValidateRoleIn calls bAddr t g ro)
    (hw : roleWalksBound ro = true ∨ anchorWalked ro = true) :
    ∃ (a : _root_.Address) (recs : List (Claim.TopRec calls bAddr t (some (groupValLimit g)))),
      t.addressOf? ro = some a ∧ Claim.TopRecsClosed recs ∧ a ∈ recs.map (·.addr) := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsub⟩ := hv
  obtain ⟨a, recs, had, hcl, hmem⟩ := validate_role_lim_walks hrc htbl ev hw
  refine ⟨a, recs.map (Claim.TopRec.mono hsub), had, hcl.mono hsub, ?_⟩
  rw [Claim.map_addr_topRec_mono]
  exact hmem

/-! ## The evidence theorems of a role specified by equations -/

/-- **What an observed walk records, with its limit**: a closed list of records each checked
under the role context at the walk's limit, holding the walked address. -/
theorem RunCheckFullIn.lim_walks {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {n : Nat} {addr : _root_.Address}
    (hv : RunCheckFullIn calls bAddr t n addr) :
    ∃ recs : List (Claim.TopRec calls bAddr t (some n)),
      Claim.TopRecsClosed recs ∧ addr ∈ recs.map (·.addr) := by
  obtain ⟨h_w, h_w', rc, ap, r_w, cs_w, hrc, ha, ev, hsub⟩ := hv
  obtain ⟨-, recs, hmem, hcl, -⟩ :=
    Claim.run_check_transitive_lim_spec (lim := some n)
      (show Claim.RCLimRep t bAddr (some n) h_w rc from hrc) ha ev
  refine ⟨recs.map (Claim.TopRec.mono hsub), hcl.mono hsub, ?_⟩
  rw [Claim.map_addr_topRec_mono]
  exact hmem

/-- **The evidence theorems of a role specified by equations, walked at the group's validation
limit**: each `.proof thm` entry of the role's evidence is a record of a closed list of records
checked under the role context at the group's validation limit. -/
theorem ValidateRoleIn.eqns_evidence_walks {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {g : Nat} {ro : Ix.Kernel.Role}
    (hv : ValidateRoleIn calls bAddr t g ro) (h5 : roleSpecKindNat ro = 5)
    {arr : Array (Ix.Kernel.Evidence _root_.Address)} {thm : _root_.Address}
    (hm : (ro, arr) ∈ t.evidence.toList) (hthm : Ix.Kernel.Evidence.proof thm ∈ arr.toList) :
    ∃ recs : List (Claim.TopRec calls bAddr t (some (groupValLimit g))),
      Claim.TopRecsClosed recs ∧ thm ∈ recs.map (·.addr) := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsub⟩ := hv
  exact ((validate_role_eqns_evidence_observed hrc htbl ev h5 arr thm hm hthm).mono
    hsub).lim_walks

/-! ## The references of an operation's certificates -/

/-- **A reference walked under the context `walk_ctx` gives it, at the limit**: it was asked
about (`Claim.RefAllowedIn`), and it is bound to a walked role in force at the limit
(`Claim.CoveredAt`: its own group walks it, and `walk_ctx` hands the walk that group's context),
or it is a record of a closed list of records checked under the role context at the limit. -/
theorem RefWalkedUnderCtxIn.lim_walks {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {n : Nat} {b : _root_.Address}
    (hv : RefWalkedUnderCtxIn calls bAddr t n b) :
    Claim.RefAllowedIn calls t bAddr (some n) b ∧
    (Claim.CoveredAt t (some n) b ∨
      ∃ recs : List (Claim.TopRec calls bAddr t (some n)),
        Claim.TopRecsClosed recs ∧ b ∈ recs.map (·.addr)) := by
  obtain ⟨⟨h₀, h₀', x_rc₀, x_b₀, r₀, cs₀, hrc₀, hb₀, ev₀, hs₀⟩,
    h₁, h₂, h₃, x_rc, x_b, rc', r_w, cs_c, cs_w, hrc, hb, evc, evw, hsub⟩ := hv
  refine ⟨⟨h₀, h₀', x_rc₀, x_b₀, r₀, cs₀, hrc₀, hb₀, ev₀, hs₀⟩, ?_⟩
  obtain ⟨ext, hcase⟩ :=
    Claim.walk_ctx_lim_spec (lim := some n)
      (show Claim.RCLimRep t bAddr (some n) h₁ x_rc from hrc) hb evc
  rcases hcase with hrc' | ⟨hcov, -⟩
  · right
    subst hrc'
    obtain ⟨-, recs, hmem, hcl, -⟩ :=
      Claim.run_check_transitive_lim_spec (lim := some n)
        (show Claim.RCLimRep t bAddr (some n) h₂ _ from hrc.mono ext) (S0.addr_mono ext hb) evw
    refine ⟨recs.map (Claim.TopRec.mono hsub), hcl.mono hsub, ?_⟩
    rw [Claim.map_addr_topRec_mono]
    exact hmem
  · exact Or.inl hcov

/-- **The references of an operation's certificate, walked at the group's validation limit**:
for a `.proof thm` entry of the operation's evidence, the certificate's record is bytes the
validation hashed, the run guarded its references other than the operation's address
(`CertRefsGuardedIn`), and each reference it uses other than the operation's own address was asked
about (`Claim.RefAllowedIn`) and is bound to a walked role in force at the limit, or is a record
of a closed list of records checked under the role context at the group's validation limit. The
certificate's record is not walked. -/
theorem ValidateRoleIn.op_certificate_walks {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {g : Nat} {ro : Ix.Kernel.Role}
    (hv : ValidateRoleIn calls bAddr t g ro) (h2 : roleSpecKindNat ro = 2)
    {arr : Array (Ix.Kernel.Evidence _root_.Address)} {thm a : _root_.Address}
    (ha : t.addressOf? ro = some a) (hm : (ro, arr) ∈ t.evidence.toList)
    (hthm : Ix.Kernel.Evidence.proof thm ∈ arr.toList) :
    ∃ (rawBytes : ByteArray) (c : Ixon.Constant),
      rawBytes.size < 4294967296 ∧ Hashed calls rawBytes ∧ Address.blake3Pure rawBytes = thm ∧
      Ixon.deConstantExact rawBytes = .ok c ∧
      CertRefsGuardedIn calls bAddr t (groupValLimit g) a c ∧
      ∀ j : Nat, (hj : j < c.refs.toList.length) → j ∈ S0.usedRefIdxs c →
        c.refs.toList[j] ≠ a →
        Claim.RefAllowedIn calls t bAddr (some (groupValLimit g)) c.refs.toList[j] ∧
        (Claim.CoveredAt t (some (groupValLimit g)) c.refs.toList[j] ∨
          ∃ recs : List (Claim.TopRec calls bAddr t (some (groupValLimit g))),
            Claim.TopRecsClosed recs ∧ c.refs.toList[j] ∈ recs.map (·.addr)) := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsub⟩ := hv
  obtain ⟨rawBytes, c, hsz, hh, hb, hde, hg, hw⟩ :=
    (validate_role_op_certificates_observed hrc htbl ev h2 arr thm a ha hm hthm).mono hsub
  exact ⟨rawBytes, c, hsz, hh, hb, hde, hg, fun j hj hu hne => (hw j hj hu hne).lim_walks⟩

end IxVM.Refinement.RoleVal
