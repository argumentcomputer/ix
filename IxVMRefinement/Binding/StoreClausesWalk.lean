import IxVMRefinement.Binding.RunStores

/-! # The admission clauses that read a group's walk

For the store sequence `groupStore t E₀` of `IxVMRefinement.Binding.RunStores`, the clauses of a
group's admission that read what the group's validations walked.

* `GroupWalked calls bAddr t E₀ g recs`: `recs` is a closed list of records walked under the
  role context at the group's validation limit that holds the bound record of every role of the
  group whose validation walks it, every reference of the group's standard axiom that is
  not covered, and every reference that is not covered of a proof in the evidence of a role of
  the group, other than the role's own address (`roleEvidence_walked`). `groupWalked_exists`
  produces one from the observed validations of the group's roles.
* `GroupReach.listed`: an address the group's admission reaches is a record of the list.
* `walkRank recs`: the rank of an address in the group's admission: the least depth of a record
  of the list at it, and one more than every depth for an address the list does not hold (a
  projection record added beside its block, the group's standard axiom).
* The clauses, each for `groupStore t E₀ Pay g` and `groupStore t E₀ Pay (g + 1)`:
  `groupStore_kept`,
  `groupStore_rankUsed`, `groupStore_rankOwner`, `groupStore_projMember`,
  `groupStore_usedClosed` (one step), `groupStore_usedClosed_all` and
  `groupStore_evidenceRefs`; and `groupStore_checked`, the check of every new unit of this store,
  the unit's half of `FamilyAdmits.checked` (the admission has no check clause of its own).

What a group's payload adds (`PayAdds`) is read through `PayloadFacts t E₀ Pay`, the facts the
clauses need of the records the payload reaches, which no walk reaches (`payAdds_cases`); with no
payload they hold (`payloadFacts_none`). `groupStore_rankUsed` and `groupStore_rankOwner` are the
walk's rank, stated at a group without payload.

Two premises are named and not produced here:

* `BasisRolesStored t`: the bound record of a walked role of a group below 6 is a basis row
  (from the prelude pin);
* `AxiomRolesDeclared t E₀`: the record the table binds a standard axiom to is a safe axiom
  record of the run (from `KernelRoles::validate_standard_axiom`, whose observed call matches
  the loaded constant as an axiom and asserts it safe).
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.StoreInhabit (basisStore)

/-! ## Record kinds -/

theorem unitKind_not_proj {c : Ixon.Constant} (hu : UnitKind c) (hp : IsProj c) : False := by
  rcases hu with ⟨d, h⟩ | ⟨rc, h⟩ | hb
  · exact standalone_not_proj (Or.inl ⟨d, h⟩) hp
  · exact standalone_not_proj (Or.inr (Or.inl ⟨rc, h⟩)) hp
  · exact proj_not_block hp hb

theorem unitKind_not_axiom {c : Ixon.Constant} {ax : Ixon.Axiom} (hu : UnitKind c)
    (h : c.info = .axio ax) : False := by
  rcases hu with ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ <;> (rw [h] at h'; cases h')

theorem proj_not_axiom {c : Ixon.Constant} {ax : Ixon.Axiom} (hp : IsProj c)
    (h : c.info = .axio ax) : False := by
  rcases hp with ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ <;> (rw [h] at h'; cases h')

/-- A record that is no projection record is its own owner. -/
theorem ownerOf_of_not_proj {a : _root_.Address} {c : Ixon.Constant} (h : ¬ IsProj c) :
    Ix.Cert.ownerOf a c = a := by
  unfold Ix.Cert.ownerOf
  cases hi : c.info with
  | dPrj p => exact absurd (Or.inl ⟨p, hi⟩) h
  | iPrj p => exact absurd (Or.inr (Or.inl ⟨p, hi⟩)) h
  | cPrj p => exact absurd (Or.inr (Or.inr (Or.inl ⟨p, hi⟩))) h
  | rPrj p => exact absurd (Or.inr (Or.inr (Or.inr ⟨p, hi⟩))) h
  | _ => rfl

section Walk

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env} {Pay : PayloadRel}

/-! ## The records a group's validations walked -/

/-- **A closed list of records the validations of group `g` walked**, holding the group's
roots (module docstring). -/
structure GroupWalked (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (g : Nat)
    (recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))) : Prop where
  closed : Claim.TopRecsClosed recs
  roots : ∀ r ∈ roleGroup g,
    (RoleVal.roleWalksBound r = true ∨ RoleVal.anchorWalked r = true) →
    ∀ a, t.addressOf? r = some a → ∃ x ∈ recs, x.addr = a
  axiomRefs : ∀ r ∈ roleGroup g, r ∈ standardAxioms → ∀ a, t.addressOf? r = some a →
    ∀ x, UsedRef E₀ a x → ¬ Claim.CoveredAt t (some (valLimit g)) x → ∃ y ∈ recs, y.addr = x
  evidenceRefs : ∀ r ∈ roleGroup g, ∀ (arr : Array (Ix.Kernel.Evidence _root_.Address))
    (thm x : _root_.Address), (r, arr) ∈ t.evidence.toList →
    Ix.Kernel.Evidence.proof thm ∈ arr.toList → UsedRef E₀ thm x → t.addressOf? r ≠ some x →
    ¬ Claim.CoveredAt t (some (valLimit g)) x → ∃ y ∈ recs, y.addr = x

/-- The table a role's validation reads is well formed. -/
theorem RoleValidationIn.wf {g : Nat} {r : Ix.Kernel.Role}
    (hv : RoleValidationIn calls bAddr t g r) : t.wf = true := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsub⟩ := hv
  exact htbl.1

set_option maxRecDepth 100000 in
/-- A role with equations is an operation (kind 2) or a definition specified by equations
(kind 5). -/
theorem specKind_of_roleHasEquations {ro : Ix.Kernel.Role}
    (he : RoleVal.roleHasEquations ro = true) :
    RoleVal.roleSpecKindNat ro = 2 ∨ RoleVal.roleSpecKindNat ro = 5 := by
  cases ro <;> first | exact absurd he (by decide) | decide

/-- **The roles with evidence**: at a well-formed table a role with an evidence entry is an
operation or a definition specified by equations. -/
theorem evidence_specKind (hwf : t.wf = true) {r : Ix.Kernel.Role}
    {arr : Array (Ix.Kernel.Evidence _root_.Address)} (hm : (r, arr) ∈ t.evidence.toList) :
    RoleVal.roleSpecKindNat r = 2 ∨ RoleVal.roleSpecKindNat r = 5 :=
  specKind_of_roleHasEquations (RoleVal.evidence_roleHasEquations_of_wf hwf hm)

/-- **Closed lists for the entries of a list, joined**: one closed list that holds, for every
entry, the addresses the entry's own list holds. -/
theorem topRecs_cover {α : Type} {lim : Option Nat} (P : α → _root_.Address → Prop) :
    ∀ (es : List α), (∀ e ∈ es, ∃ recs : List (Claim.TopRec calls bAddr t lim),
      Claim.TopRecsClosed recs ∧ ∀ x, P e x → ∃ y ∈ recs, y.addr = x) →
    ∃ recs : List (Claim.TopRec calls bAddr t lim), Claim.TopRecsClosed recs ∧
      ∀ e ∈ es, ∀ x, P e x → ∃ y ∈ recs, y.addr = x
  | [], _ => ⟨[], by simp [Claim.TopRecsClosed], fun e he => by cases he⟩
  | e :: es, h => by
    obtain ⟨r₁, hc₁, h₁⟩ := h e (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨r₂, hc₂, h₂⟩ := topRecs_cover P es (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    refine ⟨r₁ ++ r₂, hc₁.append hc₂, fun e' he' x hx => ?_⟩
    rcases List.mem_cons.mp he' with h' | h'
    · rw [h'] at hx
      obtain ⟨y, hy, hya⟩ := h₁ x hx
      exact ⟨y, List.mem_append_left _ hy, hya⟩
    · obtain ⟨y, hy, hya⟩ := h₂ e' h' x hx
      exact ⟨y, List.mem_append_right _ hy, hya⟩

/-- **The references the proofs in a role's evidence use**, other than the role's own address
and not covered at the group's validation limit, are records of a closed list walked under the
role context at the group's validation limit: an equation theorem is walked with its closure
(`RoleVal.ValidateRoleIn.eqns_evidence_walks`), a certificate's references one by one
(`RoleVal.ValidateRoleIn.op_certificate_walks`). -/
theorem roleEvidence_walked (hH : LoadedReads.HashedRecordsStored calls E₀) {g : Nat}
    {r : Ix.Kernel.Role} (hv : RoleValidationIn calls bAddr t g r) :
    ∃ recs : List (Claim.TopRec calls bAddr t (some (valLimit g))), Claim.TopRecsClosed recs ∧
      ∀ (arr : Array (Ix.Kernel.Evidence _root_.Address)) (thm x : _root_.Address),
        (r, arr) ∈ t.evidence.toList → Ix.Kernel.Evidence.proof thm ∈ arr.toList →
        UsedRef E₀ thm x → t.addressOf? r ≠ some x →
        ¬ Claim.CoveredAt t (some (valLimit g)) x → ∃ y ∈ recs, y.addr = x := by
  have hwf := hv.wf
  have hv' : RoleVal.ValidateRoleIn calls bAddr t g r := hv
  by_cases hex : ∃ arr₀, (r, arr₀) ∈ t.evidence.toList
  swap
  · exact ⟨[], by simp [Claim.TopRecsClosed], fun arr _ _ hm => absurd ⟨arr, hm⟩ hex⟩
  obtain ⟨arr₀, hm₀⟩ := hex
  rcases evidence_specKind hwf hm₀ with h2 | h5
  · -- an operation: the references of each certificate, other than the operation's address
    obtain ⟨a, had, -⟩ := (RoleValidationIn.walks hv).1
    have hcover := topRecs_cover (calls := calls) (bAddr := bAddr) (t := t)
      (lim := some (valLimit g))
      (fun (e : Ix.Kernel.Evidence _root_.Address) (x : _root_.Address) =>
        ∃ thm, e = .proof thm ∧ UsedRef E₀ thm x ∧ x ≠ a ∧
          ¬ Claim.CoveredAt t (some (valLimit g)) x) arr₀.toList
    obtain ⟨recs, hcl, hcov⟩ := hcover (by
      intro e he
      cases e with
      | defeq =>
        refine ⟨[], by simp [Claim.TopRecsClosed], fun x hx => ?_⟩
        obtain ⟨_, h, _⟩ := hx
        cases h
      | proof thm =>
        obtain ⟨rawBytes, c, hsz, hh, hbl, hde, -, hw⟩ :=
          RoleVal.ValidateRoleIn.op_certificate_walks hv' h2 had hm₀ he
        have hrec : recordOf E₀ thm = some c := by
          obtain ⟨lc, hget, hraw, -⟩ :=
            hH rawBytes c hh hsz (L1.deConstant_of_deConstantExact hde) hde
          rw [hbl] at hget
          unfold recordOf
          rw [hget]
          simp [hraw, hde, Except.toOption]
        have hidx := topRecs_cover (calls := calls) (bAddr := bAddr) (t := t)
          (lim := some (valLimit g))
          (fun (j : Nat) (x : _root_.Address) => ∃ hj : j < c.refs.toList.length,
            j ∈ Core.S0.usedRefIdxs c ∧ c.refs.toList[j] = x ∧ x ≠ a ∧
              ¬ Claim.CoveredAt t (some (valLimit g)) x) (List.range c.refs.toList.length)
        obtain ⟨recs, hcl, hj⟩ := hidx (by
          intro j _
          by_cases hP : ∃ hj : j < c.refs.toList.length, j ∈ Core.S0.usedRefIdxs c ∧
              c.refs.toList[j] ≠ a ∧ ¬ Claim.CoveredAt t (some (valLimit g)) c.refs.toList[j]
          · obtain ⟨hjl, hju, hjne, hjnc⟩ := hP
            rcases (hw j hjl hju hjne).2 with hcov' | ⟨recs, hcl, hmem⟩
            · exact absurd hcov' hjnc
            · refine ⟨recs, hcl, fun x hx => ?_⟩
              obtain ⟨_, _, hxe, _, _⟩ := hx
              obtain ⟨y, hy, hya⟩ := List.mem_map.mp hmem
              exact ⟨y, hy, hya.trans hxe⟩
          · refine ⟨[], by simp [Claim.TopRecsClosed], fun x hx => ?_⟩
            obtain ⟨hjl, hju, hxe, hxa, hnc⟩ := hx
            exact (hP ⟨hjl, hju, by rw [hxe]; exact hxa, by rw [hxe]; exact hnc⟩).elim)
        refine ⟨recs, hcl, fun x hx => ?_⟩
        obtain ⟨thm', heq, hu, hxa, hnc⟩ := hx
        have e : thm' = thm := (Ix.Kernel.Evidence.proof.inj heq).symm
        rw [e] at hu
        obtain ⟨c', i, hc', hi, hx⟩ := hu
        have ec : c' = c := Option.some.inj (hc'.symm.trans hrec)
        rw [ec] at hi hx
        obtain ⟨hlt, hxe⟩ := Array.getElem?_eq_some_iff.mp hx
        have hlt' : i < c.refs.toList.length := by simpa using hlt
        exact hj i (List.mem_range.mpr hlt') x
          ⟨hlt', by rw [Assembly.usedRefIdxs_eq]; exact hi, by simpa using hxe, hxa, hnc⟩)
    refine ⟨recs, hcl, fun arr thm x hm hthm hu hne hnc => ?_⟩
    have e := RoleVal.evidence_eq_of_wf hwf hm hm₀
    rw [e] at hthm
    have hxa : x ≠ a := fun hx => hne (by rw [hx]; exact had)
    exact hcov _ hthm x ⟨thm, rfl, hu, hxa, hnc⟩
  · -- a definition specified by equations: each theorem with its closure
    have hcover := topRecs_cover (calls := calls) (bAddr := bAddr) (t := t)
      (lim := some (valLimit g))
      (fun (e : Ix.Kernel.Evidence _root_.Address) (x : _root_.Address) => e = .proof x)
      arr₀.toList
    obtain ⟨recs, hcl, hcov⟩ := hcover (by
      intro e he
      cases e with
      | defeq =>
        refine ⟨[], by simp [Claim.TopRecsClosed], fun x hx => ?_⟩
        cases hx
      | proof thm =>
        obtain ⟨recs, hcl, hmem⟩ := RoleVal.ValidateRoleIn.eqns_evidence_walks hv' h5 hm₀ he
        refine ⟨recs, hcl, fun x hx => ?_⟩
        have e : thm = x := Ix.Kernel.Evidence.proof.inj hx
        rw [e] at hmem
        obtain ⟨y, hy, hya⟩ := List.mem_map.mp hmem
        exact ⟨y, hy, hya⟩)
    refine ⟨recs, hcl, fun arr thm x hm hthm hu hne hnc => ?_⟩
    have e := RoleVal.evidence_eq_of_wf hwf hm hm₀
    rw [e] at hthm
    obtain ⟨y, hy, hya⟩ := hcov _ hthm thm rfl
    obtain ⟨c', i, hc', hi, hx⟩ := hu
    have hrec := topRec_recordOf hH y
    rw [hya] at hrec
    have ec : c' = y.c := Option.some.inj (hc'.symm.trans hrec)
    rw [ec] at hi hx
    obtain ⟨-, hrest⟩ := (hcl y hy).2 i (by rw [Assembly.usedRefIdxs_eq]; exact hi) x hx
    rcases hrest with ⟨-, r', hr', e', -⟩ | hcov'
    · exact ⟨r', hr', e'⟩
    · exact absurd hcov' hnc

/-- **The walks of one role**: from its observed validation, a closed list that holds its bound
record if the validation walks it, the references of its record that are not covered if it
is a standard axiom, and the references the proofs in its evidence use (`roleEvidence_walked`). -/
theorem roleWalked_exists (hH : LoadedReads.HashedRecordsStored calls E₀) {g : Nat}
    {r : Ix.Kernel.Role} (hv : RoleValidationIn calls bAddr t g r) :
    ∃ recs : List (Claim.TopRec calls bAddr t (some (valLimit g))), Claim.TopRecsClosed recs ∧
      ((RoleVal.roleWalksBound r = true ∨ RoleVal.anchorWalked r = true) →
        ∀ a, t.addressOf? r = some a → ∃ x ∈ recs, x.addr = a) ∧
      (r ∈ standardAxioms → ∀ a, t.addressOf? r = some a → ∀ x, UsedRef E₀ a x →
        ¬ Claim.CoveredAt t (some (valLimit g)) x → ∃ y ∈ recs, y.addr = x) ∧
      (∀ (arr : Array (Ix.Kernel.Evidence _root_.Address)) (thm x : _root_.Address),
        (r, arr) ∈ t.evidence.toList → Ix.Kernel.Evidence.proof thm ∈ arr.toList →
        UsedRef E₀ thm x → t.addressOf? r ≠ some x →
        ¬ Claim.CoveredAt t (some (valLimit g)) x → ∃ y ∈ recs, y.addr = x) := by
  have h1 : ∃ recs₁ : List (Claim.TopRec calls bAddr t (some (valLimit g))),
      Claim.TopRecsClosed recs₁ ∧
      ((RoleVal.roleWalksBound r = true ∨ RoleVal.anchorWalked r = true) →
        ∀ a, t.addressOf? r = some a → ∃ x ∈ recs₁, x.addr = a) := by
    by_cases hw : RoleVal.roleWalksBound r = true ∨ RoleVal.anchorWalked r = true
    · obtain ⟨a, recs, had, hcl, hmem, -⟩ := RoleValidationIn.checked_bound hH hv hw
      refine ⟨recs, hcl, fun _ a' ha' => ?_⟩
      have e : a' = a := Option.some.inj (ha'.symm.trans had)
      rw [e]
      obtain ⟨x, hx, hxa⟩ := List.mem_map.mp hmem
      exact ⟨x, hx, hxa⟩
    · exact ⟨[], by simp [Claim.TopRecsClosed], fun h => absurd h hw⟩
  have h2 : ∃ recs₂ : List (Claim.TopRec calls bAddr t (some (valLimit g))),
      Claim.TopRecsClosed recs₂ ∧
      (r ∈ standardAxioms → ∀ a, t.addressOf? r = some a → ∀ x, UsedRef E₀ a x →
        ¬ Claim.CoveredAt t (some (valLimit g)) x → ∃ y ∈ recs₂, y.addr = x) := by
    by_cases hs : r ∈ standardAxioms
    · obtain ⟨a, rawBytes, c, recs, had, hsz, hh, hblk, hde, hdeE, hcl, hrefs⟩ :=
        RoleVal.ValidateRoleIn.axiom_refs (show RoleVal.ValidateRoleIn calls bAddr t g r from hv)
          ((RoleVal.specKind_three_iff r).mpr hs)
      refine ⟨recs, hcl, fun _ a' ha' x hu hnc => ?_⟩
      have e : a' = a := Option.some.inj (ha'.symm.trans had)
      rw [e] at hu
      have hrec : recordOf E₀ a = some c := by
        obtain ⟨lc, hget, hraw, -⟩ := hH rawBytes c hh hsz hde hdeE
        rw [hblk] at hget
        unfold recordOf
        rw [hget]
        simp [hraw, hdeE, Except.toOption]
      obtain ⟨c', i, hc', hi, hx⟩ := hu
      have ec : c' = c := Option.some.inj (hc'.symm.trans hrec)
      rw [ec] at hi hx
      obtain ⟨hlt, hxe⟩ := Array.getElem?_eq_some_iff.mp hx
      have hlt' : i < c.refs.toList.length := by simpa using hlt
      have hused : i ∈ Core.S0.usedRefIdxs c := by
        rw [Assembly.usedRefIdxs_eq]
        exact hi
      obtain ⟨-, hrest⟩ := hrefs i hlt' hused
      have hxl : c.refs.toList[i]'hlt' = x := by simpa using hxe
      rw [hxl] at hrest
      rcases hrest with ⟨-, hin⟩ | hcov
      · obtain ⟨y, hy, hya⟩ := List.mem_map.mp hin
        exact ⟨y, hy, hya⟩
      · exact absurd hcov hnc
    · exact ⟨[], by simp [Claim.TopRecsClosed], fun h => absurd h hs⟩
  obtain ⟨recs₁, hc₁, hw₁⟩ := h1
  obtain ⟨recs₂, hc₂, hw₂⟩ := h2
  obtain ⟨recs₃, hc₃, hw₃⟩ := roleEvidence_walked hH hv
  refine ⟨recs₁ ++ recs₂ ++ recs₃, (hc₁.append hc₂).append hc₃, fun hw a ha => ?_,
    fun hs a ha x hu hnc => ?_, fun arr thm x hm hthm hu hne hnc => ?_⟩
  · obtain ⟨x, hx, e⟩ := hw₁ hw a ha
    exact ⟨x, List.mem_append_left _ (List.mem_append_left _ hx), e⟩
  · obtain ⟨y, hy, e⟩ := hw₂ hs a ha x hu hnc
    exact ⟨y, List.mem_append_left _ (List.mem_append_right _ hy), e⟩
  · obtain ⟨y, hy, e⟩ := hw₃ arr thm x hm hthm hu hne hnc
    exact ⟨y, List.mem_append_right _ hy, e⟩

/-- **A group's validations walked a closed list holding the group's roots.** -/
theorem groupWalked_exists (hH : LoadedReads.HashedRecordsStored calls E₀) {g : Nat}
    (hval : ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r) :
    ∃ recs, GroupWalked calls bAddr t E₀ g recs := by
  have haux : ∀ rs : List Ix.Kernel.Role, (∀ r ∈ rs, r ∈ roleGroup g) →
      ∃ recs : List (Claim.TopRec calls bAddr t (some (valLimit g))),
        Claim.TopRecsClosed recs ∧
        (∀ r ∈ rs, (RoleVal.roleWalksBound r = true ∨ RoleVal.anchorWalked r = true) →
          ∀ a, t.addressOf? r = some a → ∃ x ∈ recs, x.addr = a) ∧
        (∀ r ∈ rs, r ∈ standardAxioms → ∀ a, t.addressOf? r = some a → ∀ x, UsedRef E₀ a x →
          ¬ Claim.CoveredAt t (some (valLimit g)) x → ∃ y ∈ recs, y.addr = x) ∧
        (∀ r ∈ rs, ∀ (arr : Array (Ix.Kernel.Evidence _root_.Address)) (thm x : _root_.Address),
          (r, arr) ∈ t.evidence.toList → Ix.Kernel.Evidence.proof thm ∈ arr.toList →
          UsedRef E₀ thm x → t.addressOf? r ≠ some x →
          ¬ Claim.CoveredAt t (some (valLimit g)) x → ∃ y ∈ recs, y.addr = x) := by
    intro rs
    induction rs with
    | nil =>
      intro _
      exact ⟨[], by simp [Claim.TopRecsClosed], (fun r hr => by cases hr),
        (fun r hr => by cases hr), (fun r hr => by cases hr)⟩
    | cons r rs ih =>
      intro hsub
      obtain ⟨recs, hcl, hw, hs, he⟩ := ih (fun r' hr' => hsub r' (List.mem_cons_of_mem _ hr'))
      obtain ⟨recs', hcl', hw', hs', he'⟩ :=
        roleWalked_exists (E₀ := E₀) hH (hval r (hsub r (List.mem_cons.mpr (Or.inl rfl))))
      refine ⟨recs' ++ recs, hcl'.append hcl, fun r₁ hr₁ hwk a ha => ?_,
        fun r₁ hr₁ hst a ha x hu hnc => ?_, fun r₁ hr₁ arr thm x hm hthm hu hne hnc => ?_⟩
      · rcases List.mem_cons.mp hr₁ with e | hr₁
        · rw [e] at hwk ha
          obtain ⟨x, hx, e'⟩ := hw' hwk a ha
          exact ⟨x, List.mem_append_left _ hx, e'⟩
        · obtain ⟨x, hx, e'⟩ := hw r₁ hr₁ hwk a ha
          exact ⟨x, List.mem_append_right _ hx, e'⟩
      · rcases List.mem_cons.mp hr₁ with e | hr₁
        · rw [e] at hst ha
          obtain ⟨y, hy, e'⟩ := hs' hst a ha x hu hnc
          exact ⟨y, List.mem_append_left _ hy, e'⟩
        · obtain ⟨y, hy, e'⟩ := hs r₁ hr₁ hst a ha x hu hnc
          exact ⟨y, List.mem_append_right _ hy, e'⟩
      · rcases List.mem_cons.mp hr₁ with e | hr₁
        · rw [e] at hm hne
          obtain ⟨y, hy, e'⟩ := he' arr thm x hm hthm hu hne hnc
          exact ⟨y, List.mem_append_left _ hy, e'⟩
        · obtain ⟨y, hy, e'⟩ := he r₁ hr₁ arr thm x hm hthm hu hne hnc
          exact ⟨y, List.mem_append_right _ hy, e'⟩
  obtain ⟨recs, hcl, hw, hs, he⟩ := haux (roleGroup g) (fun _ h => h)
  exact ⟨recs, ⟨hcl, hw, hs, he⟩⟩

/-- **An address the group's admission reaches is a record of the group's walk.** -/
theorem GroupReach.listed (hH : LoadedReads.HashedRecordsStored calls E₀) {g : Nat}
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) {a : _root_.Address}
    (h : GroupReach t E₀ g a) : ∃ r ∈ recs, r.addr = a := by
  induction h with
  | root hr hwk had => exact hw.roots _ hr hwk _ had
  | axiomRef hr hs had hu hnc => exact hw.axiomRefs _ hr hs _ had _ hu hnc
  | @ref a x _ hu hnc ih =>
    obtain ⟨r, hr, hra⟩ := ih
    obtain ⟨c, i, hc, hi, hx⟩ := hu
    have hrec := topRec_recordOf hH r
    rw [hra] at hrec
    have ec : c = r.c := Option.some.inj (hc.symm.trans hrec)
    rw [ec] at hi hx
    obtain ⟨-, hrest⟩ := (hw.closed r hr).2 i
      (by rw [Assembly.usedRefIdxs_eq]; exact hi) x hx
    rcases hrest with ⟨-, r', hr', e, -⟩ | hcov
    · exact ⟨r', hr', e⟩
    · exact absurd hcov hnc
  | @owner a c _ hc hp ih =>
    obtain ⟨r, hr, hra⟩ := ih
    have hrec := topRec_recordOf hH r
    rw [hra] at hrec
    have ec : c = r.c := Option.some.inj (hc.symm.trans hrec)
    rw [ec] at hp ⊢
    obtain ⟨r', hr', e, -⟩ := (hw.closed r hr).1 hp
    rw [hra] at e
    exact ⟨r', hr', e⟩
  | evidenceRef hr hm hthm hu hne hnc => exact hw.evidenceRefs _ hr _ _ _ hm hthm hu hne hnc

/-! ## The rank -/

/-- The greatest depth of a list of walked records. -/
def maxDepth {lim : Option Nat} : List (Claim.TopRec calls bAddr t lim) → Nat
  | [] => 0
  | r :: rs => max r.depth (maxDepth rs)

theorem depth_le_maxDepth {lim : Option Nat} :
    ∀ {recs : List (Claim.TopRec calls bAddr t lim)} {r : Claim.TopRec calls bAddr t lim},
      r ∈ recs → r.depth ≤ maxDepth recs
  | [], _, h => by cases h
  | r' :: rs, r, h => by
    show r.depth ≤ max r'.depth (maxDepth rs)
    rcases List.mem_cons.mp h with e | h'
    · rw [e]
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (depth_le_maxDepth h') (Nat.le_max_right _ _)

/-- **The rank of an address in a group's admission** (module docstring). -/
noncomputable def walkRank {lim : Option Nat} (recs : List (Claim.TopRec calls bAddr t lim))
    (a : _root_.Address) : Nat :=
  @ite _ (∃ r ∈ recs, r.addr = a) (Classical.propDecidable _) (Claim.topRank recs a)
    (maxDepth recs + 1)

theorem walkRank_listed {lim : Option Nat} {recs : List (Claim.TopRec calls bAddr t lim)}
    {a : _root_.Address} (h : ∃ r ∈ recs, r.addr = a) :
    ∃ r ∈ recs, r.addr = a ∧ r.depth = walkRank recs a := by
  obtain ⟨r, hr, hra⟩ := h
  have hmem : ∃ r ∈ recs, r.addr = a ∧ r.depth = Claim.topRank recs a :=
    Nat.sInf_mem (s := {d | ∃ r ∈ recs, r.addr = a ∧ r.depth = d}) ⟨r.depth, r, hr, hra, rfl⟩
  have e : walkRank recs a = Claim.topRank recs a := by
    unfold walkRank
    exact ite_eq_left ⟨r, hr, hra⟩
  rw [e]
  exact hmem

theorem walkRank_le {lim : Option Nat} {recs : List (Claim.TopRec calls bAddr t lim)}
    {r : Claim.TopRec calls bAddr t lim} (hr : r ∈ recs) : walkRank recs r.addr ≤ r.depth := by
  have e : walkRank recs r.addr = Claim.topRank recs r.addr := by
    unfold walkRank
    exact ite_eq_left ⟨r, hr, rfl⟩
  rw [e]
  exact Nat.sInf_le ⟨r, hr, rfl, rfl⟩

theorem walkRank_unlisted {lim : Option Nat} {recs : List (Claim.TopRec calls bAddr t lim)}
    {a : _root_.Address} (h : ¬ ∃ r ∈ recs, r.addr = a) :
    walkRank recs a = maxDepth recs + 1 := by
  unfold walkRank
  exact ite_eq_right h

/-- A listed address has a smaller rank than an address the list does not hold. -/
theorem walkRank_listed_lt_unlisted {lim : Option Nat}
    {recs : List (Claim.TopRec calls bAddr t lim)} {x a : _root_.Address}
    (hx : ∃ r ∈ recs, r.addr = x) (ha : ¬ ∃ r ∈ recs, r.addr = a) :
    walkRank recs x < walkRank recs a := by
  rw [walkRank_unlisted ha]
  obtain ⟨ym, hym, -, hymd⟩ := walkRank_listed hx
  have hle := depth_le_maxDepth hym
  omega

/-- **A used reference of a listed record that is not covered has a smaller rank.** -/
theorem walkRank_used_lt (hH : LoadedReads.HashedRecordsStored calls E₀) {g : Nat}
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) {a x : _root_.Address} {c : Ixon.Constant}
    {i : Nat} (hl : ∃ r ∈ recs, r.addr = a) (hE : recordOf E₀ a = some c)
    (hi : i ∈ usedRefIdxs c) (hx : c.refs[i]? = some x)
    (hcov : ¬ Claim.CoveredAt t (some (valLimit g)) x) :
    walkRank recs x < walkRank recs a := by
  obtain ⟨rm, hrm, hrma, hrmd⟩ := walkRank_listed hl
  have hrec := topRec_recordOf hH rm
  rw [hrma] at hrec
  have ecm : c = rm.c := Option.some.inj (hE.symm.trans hrec)
  rw [ecm] at hi hx
  obtain ⟨-, hrest⟩ := (hw.closed rm hrm).2 i
    (by rw [Assembly.usedRefIdxs_eq]; exact hi) x hx
  rcases hrest with ⟨-, r', hr', e', hlt⟩ | hcov'
  · have hle := walkRank_le hr'
    rw [e'] at hle
    omega
  · exact absurd hcov' hcov

/-- **The block of a listed projection record is listed at a smaller rank.** -/
theorem walkRank_owner_lt (hH : LoadedReads.HashedRecordsStored calls E₀) {g : Nat}
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) {a : _root_.Address} {c : Ixon.Constant}
    (hl : ∃ r ∈ recs, r.addr = a) (hE : recordOf E₀ a = some c) (hp : IsProj c) :
    walkRank recs (Ix.Cert.ownerOf a c) < walkRank recs a := by
  obtain ⟨rm, hrm, hrma, hrmd⟩ := walkRank_listed hl
  have hrec := topRec_recordOf hH rm
  rw [hrma] at hrec
  have ecm : c = rm.c := Option.some.inj (hE.symm.trans hrec)
  rw [ecm] at hp ⊢
  obtain ⟨r', hr', e', hlt⟩ := (hw.closed rm hrm).1 hp
  rw [hrma] at e'
  have hle := walkRank_le hr'
  rw [e'] at hle
  omega

/-! ## What a group adds, record by record -/

/-- **The bound record of a walked role of a group below 6 is a basis row.** -/
def BasisRolesStored (t : Ix.Kernel.RoleTable) : Prop :=
  ∀ r, Ix.SpecDigest.groupOf r < 6 → walkedRole r = true → ∀ a, t.addressOf? r = some a →
    (basisStore.consts.get? a).isSome = true

/-- **The record the table binds a standard axiom to is a safe axiom record of the run.** -/
def AxiomRolesDeclared (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) : Prop :=
  ∀ r ∈ standardAxioms, ∀ a, t.addressOf? r = some a →
    ∃ c ax, recordOf E₀ a = some c ∧ c.info = .axio ax ∧ ax.isUnsafe = false

/-! ## The records the payload adds -/

/-- **What the store's clauses need of the records a group's payload reaches**, at every group:
the payload's records are records of the run; a block reached so has its member and constructor
projection records; a projection record reached so is at a member's or a constructor's address
of its block; each such record is in Lean's logic; none is an axiom or quotient record.

Status: premises, not proved of any run. No walk of the group reaches these records: the family
check of the block reads them (`KernelModeled::check_family`), and what it establishes of each is
not exported. Where each fact comes from in the source, all under the group's validation context:
* `record`: `Ingress::load_verified_constant` in `KernelModeled::check_advice_record` (an advice
  record), `KernelModeled::check_container_rec` through `KernelClaim::run_check` (a container
  recursor), `KernelModeled::check_family`'s load of the family record (`check_recs`); a used
  reference of a payload record that is not covered is an advice record, a projection of an
  advice block or a witness (`KernelModeled::advice_refs_ok`, `container_refs_ok`), a witness is
  walked (`check_witness` kind 0, `KernelClaim::run_check_transitive`), lies on a path from the
  block (`walk_path`, kinds 1 to 3, which loads each record it passes) or is a container recursor;
* `blockMembers`: an advice block is checked by `KernelClaim::check_muts_all`, the family record
  by `check_recs` (each member against the block's flattened family);
* `projMember`: an advice `IPrj`/`CPrj` record is asserted to project from an advice block
  (`check_advice_record`), and a witness of kind 3 is compared with the computed projection
  address (`KernelDefEq::compute_iprj_addr`, `KernelCheck::projection_addr_ctor`);
* `logic`: `check_advice_record` admits only safe definitions, theorems, safe recursors and safe
  inductive blocks (`muts_all_safe`); a container recursor and the family record are checked by
  their blocks' routes;
* `notAxiomLike`: `check_advice_record` has no arm for an axiom or a quotient record; a container
  recursor is a recursor (`rec_family_block`); the family record is a block of recursors. -/
structure PayloadFacts (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (Pay : PayloadRel) : Prop where
  record : ∀ g a, PayReach t E₀ Pay g a → ∃ c, recordOf E₀ a = some c
  blockMembers : ∀ g B c ms, PayReach t E₀ Pay g B → recordOf E₀ B = some c → c.info = .muts ms →
    ∀ i m, ms[i]? = some m →
      recordOf E₀ (memberAddr B i m) = some (memberProjection B i m) ∧
      ∀ ind j, m = .indc ind → j < ind.ctors.size →
        recordOf E₀ (ctorAddr B i j) = some (constructorProjection B i j)
  projMember : ∀ g a c, PayReach t E₀ Pay g a → recordOf E₀ a = some c → IsProj c →
    ∃ cb, recordOf E₀ (Ix.Cert.ownerOf a c) = some cb ∧ ConstAddrOf (Ix.Cert.ownerOf a c) cb a
  logic : ∀ g a c, PayReach t E₀ Pay g a → recordOf E₀ a = some c → InLogic c
  notAxiomLike : ∀ g a c, PayReach t E₀ Pay g a → recordOf E₀ a = some c → ¬ IsAxiomLike c

/-- **With no payload there is nothing to assume.** -/
theorem payloadFacts_none (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) :
    PayloadFacts t E₀ noPayload where
  record := fun _ _ h => (PayReach.none h).elim
  blockMembers := fun _ _ _ _ h => (PayReach.none h).elim
  projMember := fun _ _ _ h => (PayReach.none h).elim
  logic := fun _ _ _ h => (PayReach.none h).elim
  notAxiomLike := fun _ _ _ h => (PayReach.none h).elim

/-- **What the payload of a group adds** is a record reached through the payload, or a
projection record beside a block reached so. -/
theorem payAdds_cases (hP : PayloadFacts t E₀ Pay) {g : Nat} {a : _root_.Address}
    (h : PayAdds t E₀ Pay g a) :
    (PayReach t E₀ Pay g a ∧ ∃ c, recordOf E₀ a = some c) ∨
    (∃ B cB, PayReach t E₀ Pay g B ∧ recordOf E₀ B = some cB ∧ IsBlock cB ∧
      ∃ p, recordOf E₀ a = some p ∧ IsProj p ∧ Ix.Cert.ownerOf a p = B ∧ p.refs = #[] ∧
        ConstAddrOf B cB a) := by
  rcases h with hr | ⟨B, cB, hB, hcB, ⟨ms, hms⟩, hca⟩
  · exact Or.inl ⟨hr, hP.record g a hr⟩
  · refine Or.inr ⟨B, cB, hB, hcB, ⟨ms, hms⟩, ?_⟩
    rcases hca with ⟨-, hst⟩ | ⟨ms', i, m, hms', hm, hx⟩
    · exact (standalone_not_block hst ⟨ms, hms⟩).elim
    · have e : ms' = ms := by
        rw [hms] at hms'
        exact (Ixon.ConstantInfo.muts.inj hms').symm
      rw [e] at hm
      obtain ⟨h1, h2⟩ := hP.blockMembers g B cB ms hB hcB hms i m hm
      rcases hx with hx | ⟨ind, j, hind, hj, hx⟩
      · rw [hx]
        exact ⟨_, h1, memberProjection_isProj _ _ _, ownerOf_memberProjection _ _ _ _,
          by cases m <;> rfl, Or.inr ⟨ms, i, m, hms, hm, Or.inl rfl⟩⟩
      · rw [hx]
        exact ⟨_, h2 ind j hind hj, constructorProjection_isProj _ _ _,
          ownerOf_constructorProjection _ _ _ _, rfl,
          Or.inr ⟨ms, i, m, hms, hm, Or.inr ⟨ind, j, hind, hj, rfl⟩⟩⟩

/-- **What the admission of a group adds is a record of the group's walk, a projection record
beside a walked block, the group's standard axiom, or what its payload adds.** -/
theorem groupAdds_cases (hC : CollisionFreeRun calls E₀) (hax : AxiomRolesDeclared t E₀)
    {g : Nat} {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) {a : _root_.Address}
    (h : GroupAdds t E₀ Pay g a) :
    (GroupReach t E₀ g a ∧ ∃ r ∈ recs, r.addr = a) ∨
    (∃ r ∈ recs, GroupReach t E₀ g r.addr ∧ IsBlock r.c ∧
      ∃ p, recordOf E₀ a = some p ∧ IsProj p ∧ Ix.Cert.ownerOf a p = r.addr ∧ p.refs = #[] ∧
        ConstAddrOf r.addr r.c a) ∨
    (∃ ro ∈ roleGroup g, ro ∈ standardAxioms ∧ t.addressOf? ro = some a ∧
      ∃ c ax, recordOf E₀ a = some c ∧ c.info = .axio ax ∧ ax.isUnsafe = false) ∨
    PayAdds t E₀ Pay g a := by
  rcases h with (hr | ⟨B, cB, hB, hcB, ⟨ms, hms⟩, hca⟩ | ⟨ro, hro, hs, had⟩) | hpay
  rotate_right
  · exact Or.inr (Or.inr (Or.inr hpay))
  · exact Or.inl ⟨hr, hr.listed hC.hashedStored hw⟩
  · obtain ⟨y, hy, hyB⟩ := hB.listed hC.hashedStored hw
    have hrec := topRec_recordOf hC.hashedStored y
    rw [hyB] at hrec
    have ec : cB = y.c := Option.some.inj (hcB.symm.trans hrec)
    rw [ec] at hms hca
    rw [← hyB] at hB hca
    refine Or.inr (Or.inl ⟨y, hy, hB, ⟨ms, hms⟩, ?_⟩)
    rcases hca with ⟨-, hst⟩ | ⟨ms', i, m, hms', hm, hx⟩
    · exact (standalone_not_block hst ⟨ms, hms⟩).elim
    · have e : ms' = ms := by
        rw [hms] at hms'
        exact (Ixon.ConstantInfo.muts.inj hms').symm
      rw [e] at hm
      obtain ⟨h1, h2⟩ := topRec_block_members hC.runStore hC.hashedStored y hms hm
      rcases hx with hx | ⟨ind, j, hind, hj, hx⟩
      · rw [hx]
        exact ⟨_, h1, memberProjection_isProj _ _ _, ownerOf_memberProjection _ _ _ _,
          by cases m <;> rfl, Or.inr ⟨ms, i, m, hms, hm, Or.inl rfl⟩⟩
      · rw [hx]
        exact ⟨_, h2 ind j hind hj, constructorProjection_isProj _ _ _,
          ownerOf_constructorProjection _ _ _ _, rfl,
          Or.inr ⟨ms, i, m, hms, hm, Or.inr ⟨ind, j, hind, hj, rfl⟩⟩⟩
  · obtain ⟨c, ax, hc, hinfo, hsafe⟩ := hax ro hs a had
    exact Or.inr (Or.inr (Or.inl ⟨ro, hro, hs, had, c, ax, hc, hinfo, hsafe⟩))

/-- **A covered reference is held by the store before the group.** -/
theorem storedBelow_of_covered (hbr : BasisRolesStored t) {g : Nat} {x : _root_.Address}
    (hcov : Claim.CoveredAt t (some (valLimit g)) x) : StoredBelow t E₀ Pay g x := by
  obtain ⟨r, had, hw, hlt⟩ := hcov
  have hlt' : Ix.SpecDigest.groupOf r < g :=
    Nat.lt_of_lt_of_le (hlt (valLimit g) rfl) (valLimit_le g)
  by_cases h6 : Ix.SpecDigest.groupOf r < 6
  · exact Or.inl (hbr r h6 hw x had)
  · have hwb : RoleVal.roleWalksBound r = true := by
      rw [← Claim.walkedRole_eq_roleWalksBound]
      exact hw
    exact Or.inr ⟨Ix.SpecDigest.groupOf r, Nat.le_of_not_lt h6, hlt',
      GroupAdds.reach (GroupReach.root (role_mem_roleGroup r) (Or.inl hwb) had)⟩

/-- **A stored address holds a record of the run.** -/
theorem storedBelow_record (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hP : PayloadFacts t E₀ Pay)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) {g : Nat} {x : _root_.Address}
    (h : StoredBelow t E₀ Pay g x) : ∃ c, recordOf E₀ x = some c := by
  rcases h with hbas | ⟨k, hk6, hk, hadd⟩
  · obtain ⟨lc, hlc⟩ := Option.isSome_iff_exists.mp hbas
    obtain ⟨c, hmem, -⟩ := StoreInhabit.store_get?_inv hlc
    have h6 : recordOf (groupStore t E₀ Pay 6) x = some c := by
      rw [groupStore_six]
      exact StoreInhabit.store_record_of_mem hmem
    exact ⟨c, ((groupStore_recordOf hb (Nat.le_refl 6)).mp h6).2⟩
  · obtain ⟨recs, hw⟩ := hws k
    rcases groupAdds_cases hC hax hw hadd with ⟨-, r, hr, hra⟩ | ⟨r, hr, -, -, p, hp, -⟩ |
        ⟨ro, hro, hs, had, c, ax, hc, -⟩ | hpay
    · rw [← hra]
      exact ⟨r.c, topRec_recordOf hC.hashedStored r⟩
    · exact ⟨p, hp⟩
    · exact ⟨c, hc⟩
    · rcases payAdds_cases hP hpay with ⟨-, hrec⟩ | ⟨-, -, -, -, -, p, hp, -⟩
      · exact hrec
      · exact ⟨p, hp⟩

/-- **An address the group adds is new in its admission or was held before.** -/
theorem new_or_stored (hb : BasisRowsLoaded E₀) {g : Nat} (hg : 6 ≤ g) {x : _root_.Address}
    {c : Ixon.Constant} (hadd : GroupAdds t E₀ Pay g x) (hc : recordOf E₀ x = some c) :
    New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) x ∨
      (recordOf (groupStore t E₀ Pay g) x).isSome = true := by
  have h6 : 6 ≤ g + 1 := Nat.le_succ_of_le hg
  by_cases hs : StoredBelow t E₀ Pay g x
  · right
    rw [(groupStore_recordOf hb hg).mpr ⟨hs, hc⟩]
    rfl
  · left
    refine ⟨?_, ?_⟩
    · rw [(groupStore_recordOf hb h6).mpr ⟨storedBelow_of_adds hg hadd, hc⟩]
      rfl
    · cases hr : recordOf (groupStore t E₀ Pay g) x with
      | none => rfl
      | some c' => exact absurd ((groupStore_recordOf hb hg).mp hr).1 hs

/-! ## The clauses -/

/-- **`Admits.kept`**: the record of every kept or prelude role of the group is held after its
admission. -/
theorem groupStore_kept (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) {g : Nat} (hg : 6 ≤ g)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) :
    ∀ r ∈ roleGroup g, (keptRole r ∨ r ∈ preludeRoles) → ∀ a, t.addressOf? r = some a →
      (recordOf (groupStore t E₀ Pay (g + 1)) a).isSome = true := by
  intro r hr hk a had
  have h6 : 6 ≤ g + 1 := Nat.le_succ_of_le hg
  have hgr : 6 ≤ Ix.SpecDigest.groupOf r := by
    rw [groupOf_of_mem_roleGroup hr]
    exact hg
  have hadds : GroupAdds t E₀ Pay g a ∧ ∃ c, recordOf E₀ a = some c := by
    rcases kept_walked hgr hk with hwk | hwk | hs
    · obtain ⟨x, hx, hxa⟩ := hw.roots r hr (Or.inl hwk) a had
      refine ⟨GroupAdds.reach (GroupReach.root hr (Or.inl hwk) had), x.c, ?_⟩
      rw [← hxa]
      exact topRec_recordOf hC.hashedStored x
    · obtain ⟨x, hx, hxa⟩ := hw.roots r hr (Or.inr hwk) a had
      refine ⟨GroupAdds.reach (GroupReach.root hr (Or.inr hwk) had), x.c, ?_⟩
      rw [← hxa]
      exact topRec_recordOf hC.hashedStored x
    · obtain ⟨c, ax, hc, -, -⟩ := hax r hs a had
      exact ⟨GroupAdds.stdAxiom hr hs had, c, hc⟩
  obtain ⟨hadd, c, hc⟩ := hadds
  rw [(groupStore_recordOf hb h6).mpr ⟨storedBelow_of_adds hg hadd, hc⟩]
  rfl

/-- **Every new unit of the store that its walk adds was checked** under the role context at
the group's validation limit; a new unit the walk does not add is reached through the group's
payload (whose check is the payload's family check: `FamilyAdmits.checked`). -/
theorem groupStore_checked (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hP : PayloadFacts t E₀ Pay) {g : Nat} (hg : 6 ≤ g)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) :
    ∀ a c, New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) a →
      recordOf (groupStore t E₀ Pay (g + 1)) a = some c → UnitKind c →
      UnitCheckedAt calls bAddr t E₀ a (some (valLimit g)) ∨ PayReach t E₀ Pay g a := by
  intro a c hnew hc hunit
  have h6 : 6 ≤ g + 1 := Nat.le_succ_of_le hg
  obtain ⟨-, -, -, hadd, -⟩ := new_groupStore hb hg hnew
  have hE : recordOf E₀ a = some c := ((groupStore_recordOf hb h6).mp hc).2
  rcases groupAdds_cases hC hax hw hadd with ⟨-, r, hr, hra⟩ | ⟨r, hr, -, -, p, hp, hproj, -⟩ |
      ⟨ro, hro, hs, had, c₂, ax, hc₂, hinfo, -⟩ | hpay
  rotate_right
  · rcases payAdds_cases hP hpay with ⟨hr, -⟩ | ⟨-, -, -, -, -, p, hp, hproj, -⟩
    · exact Or.inr hr
    · have e : p = c := Option.some.inj (hp.symm.trans hE)
      rw [e] at hproj
      exact (unitKind_not_proj hunit hproj).elim
  · left
    rw [← hra]
    exact unitCheckedAt_of_topRec hC.hashedStored r
  · have e : p = c := Option.some.inj (hp.symm.trans hE)
    rw [e] at hproj
    exact (unitKind_not_proj hunit hproj).elim
  · have e : c₂ = c := Option.some.inj (hc₂.symm.trans hE)
    rw [e] at hinfo
    exact (unitKind_not_axiom hunit hinfo).elim

/-- **`Admits.rankUsed`**: a reference a new record uses is new at a smaller rank, or held
before. -/
theorem groupStore_rankUsed (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀) (hP : PayloadFacts t E₀ Pay)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) {g : Nat} (hg : 6 ≤ g)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs)
    (hnp : ∀ B a, ¬ Pay g B a) :
    ∀ a x, New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) a →
      UsedRef (groupStore t E₀ Pay (g + 1)) a x →
      (New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) x ∧
          walkRank recs x < walkRank recs a) ∨
        (recordOf (groupStore t E₀ Pay g) x).isSome = true := by
  intro a x hnew hused
  have h6 : 6 ≤ g + 1 := Nat.le_succ_of_le hg
  obtain ⟨-, -, -, hadd, -⟩ := new_groupStore hb hg hnew
  obtain ⟨c, i, hc, hi, hx⟩ := hused
  have hE : recordOf E₀ a = some c := ((groupStore_recordOf hb h6).mp hc).2
  have huE : UsedRef E₀ a x := ⟨c, i, hE, hi, hx⟩
  by_cases hcov : Claim.CoveredAt t (some (valLimit g)) x
  · right
    have hs : StoredBelow t E₀ Pay g x := storedBelow_of_covered hbr hcov
    obtain ⟨cx, hcx⟩ := storedBelow_record hC hb hax hP hws hs
    rw [(groupStore_recordOf hb hg).mpr ⟨hs, hcx⟩]
    rfl
  · have hreach : GroupReach t E₀ g x ∧ walkRank recs x < walkRank recs a := by
      rcases groupAdds_cases hC hax hw hadd with ⟨hra, hl⟩ |
          ⟨r, hr, -, -, p, hp, -, -, hrefs, -⟩ | ⟨ro, hro, hs, had, -⟩ | hpay
      rotate_right
      · exact (hpay.noPayload hnp).elim
      · exact ⟨GroupReach.ref hra huE hcov,
          walkRank_used_lt hC.hashedStored hw hl hE hi hx hcov⟩
      · exfalso
        have e : p = c := Option.some.inj (hp.symm.trans hE)
        rw [e] at hrefs
        rw [hrefs] at hx
        simp at hx
      · have hrx : GroupReach t E₀ g x := GroupReach.axiomRef hro hs had huE hcov
        refine ⟨hrx, ?_⟩
        by_cases hl : ∃ r ∈ recs, r.addr = a
        · exact walkRank_used_lt hC.hashedStored hw hl hE hi hx hcov
        · exact walkRank_listed_lt_unlisted (hrx.listed hC.hashedStored hw) hl
    obtain ⟨hrx, hlt⟩ := hreach
    obtain ⟨y, hy, hya⟩ := hrx.listed hC.hashedStored hw
    have hcx : recordOf E₀ x = some y.c := by
      rw [← hya]
      exact topRec_recordOf hC.hashedStored y
    rcases new_or_stored hb hg (GroupAdds.reach hrx) hcx with hn | hs
    · exact Or.inl ⟨hn, hlt⟩
    · exact Or.inr hs

/-- **`Admits.rankOwner`**: a new projection record's block is new at a smaller rank, or held
before. -/
theorem groupStore_rankOwner (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) {g : Nat} (hg : 6 ≤ g)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs)
    (hnp : ∀ B a, ¬ Pay g B a) :
    ∀ a c, New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) a →
      recordOf (groupStore t E₀ Pay (g + 1)) a = some c → IsProj c →
      (New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) (Ix.Cert.ownerOf a c) ∧
          walkRank recs (Ix.Cert.ownerOf a c) < walkRank recs a) ∨
        (recordOf (groupStore t E₀ Pay g) (Ix.Cert.ownerOf a c)).isSome = true := by
  intro a c hnew hc hp
  have h6 : 6 ≤ g + 1 := Nat.le_succ_of_le hg
  obtain ⟨-, -, -, hadd, -⟩ := new_groupStore hb hg hnew
  have hE : recordOf E₀ a = some c := ((groupStore_recordOf hb h6).mp hc).2
  have hown : GroupReach t E₀ g (Ix.Cert.ownerOf a c) ∧
      walkRank recs (Ix.Cert.ownerOf a c) < walkRank recs a := by
    rcases groupAdds_cases hC hax hw hadd with ⟨hra, hl⟩ |
        ⟨r, hr, hrB, -, p, hp', -, hown, -, -⟩ | ⟨ro, hro, hs, had, c₂, ax, hc₂, hinfo, -⟩ | hpay
    rotate_right
    · exact (hpay.noPayload hnp).elim
    · exact ⟨GroupReach.owner hra hE hp, walkRank_owner_lt hC.hashedStored hw hl hE hp⟩
    · have e : p = c := Option.some.inj (hp'.symm.trans hE)
      rw [e] at hown
      by_cases hl : ∃ r ∈ recs, r.addr = a
      · refine ⟨?_, walkRank_owner_lt hC.hashedStored hw hl hE hp⟩
        rw [hown]
        exact hrB
      · rw [hown]
        exact ⟨hrB, walkRank_listed_lt_unlisted ⟨r, hr, rfl⟩ hl⟩
    · exfalso
      have e : c₂ = c := Option.some.inj (hc₂.symm.trans hE)
      rw [e] at hinfo
      exact proj_not_axiom hp hinfo
  obtain ⟨hro, hlt⟩ := hown
  obtain ⟨y, hy, hya⟩ := hro.listed hC.hashedStored hw
  have hcx : recordOf E₀ (Ix.Cert.ownerOf a c) = some y.c := by
    rw [← hya]
    exact topRec_recordOf hC.hashedStored y
  rcases new_or_stored hb hg (GroupAdds.reach hro) hcx with hn | hs
  · exact Or.inl ⟨hn, hlt⟩
  · exact Or.inr hs

/-- **`Admits.projMember`**: a new projection record is at a member's or a constructor's
address of its block, which the store after the admission holds. -/
theorem groupStore_projMember (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hP : PayloadFacts t E₀ Pay) {g : Nat} (hg : 6 ≤ g)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) :
    ∀ a c, New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) a →
      recordOf (groupStore t E₀ Pay (g + 1)) a = some c → IsProj c →
      ∃ cb, recordOf (groupStore t E₀ Pay (g + 1)) (Ix.Cert.ownerOf a c) = some cb ∧
        ConstAddrOf (Ix.Cert.ownerOf a c) cb a := by
  intro a c hnew hc hp
  have h6 : 6 ≤ g + 1 := Nat.le_succ_of_le hg
  obtain ⟨-, -, -, hadd, -⟩ := new_groupStore hb hg hnew
  have hE : recordOf E₀ a = some c := ((groupStore_recordOf hb h6).mp hc).2
  have hblock : GroupAdds t E₀ Pay g (Ix.Cert.ownerOf a c) ∧
      ∃ cb, recordOf E₀ (Ix.Cert.ownerOf a c) = some cb ∧
        ConstAddrOf (Ix.Cert.ownerOf a c) cb a := by
    rcases groupAdds_cases hC hax hw hadd with ⟨hra, r, hr, hra'⟩ |
        ⟨r, hr, hrB, -, p, hp', -, hown, -, hca⟩ | ⟨ro, hro, hs, had, c₂, ax, hc₂, hinfo, -⟩ |
        hpay
    rotate_right
    · rcases payAdds_cases hP hpay with ⟨hra, -⟩ | ⟨B, cB, hB, hcB, -, p, hp', -, hown, -, hca⟩
      · exact ⟨GroupAdds.payReach (PayReach.owner hra hE hp), hP.projMember g a c hra hE hp⟩
      · have e : p = c := Option.some.inj (hp'.symm.trans hE)
        rw [e] at hown
        rw [hown]
        exact ⟨GroupAdds.payReach hB, cB, hcB, hca⟩
    · refine ⟨GroupAdds.reach (GroupReach.owner hra hE hp), ?_⟩
      have hrec := topRec_recordOf hC.hashedStored r
      rw [hra'] at hrec
      have ec : c = r.c := Option.some.inj (hE.symm.trans hrec)
      have hpr : IsProj r.c := by
        rw [← ec]
        exact hp
      have hpm := topRec_proj_member hC.runStore hC.hashedStored r hpr
      rw [hra', ← ec] at hpm
      exact hpm
    · have e : p = c := Option.some.inj (hp'.symm.trans hE)
      rw [e] at hown
      rw [hown]
      exact ⟨GroupAdds.reach hrB, r.c, topRec_recordOf hC.hashedStored r, hca⟩
    · exfalso
      have e : c₂ = c := Option.some.inj (hc₂.symm.trans hE)
      rw [e] at hinfo
      exact proj_not_axiom hp hinfo
  obtain ⟨hro, cb, hcb, hca⟩ := hblock
  exact ⟨cb, (groupStore_recordOf hb h6).mpr ⟨storedBelow_of_adds hg hro, hcb⟩, hca⟩

/-- **A reference a new record uses is held after the group**: covered, it was held before;
otherwise the group reaches it, by its walk or through its payload. -/
theorem groupStore_used_held (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀) (hP : PayloadFacts t E₀ Pay)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) {g : Nat} (hg : 6 ≤ g)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) :
    ∀ a x, New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) a →
      UsedRef (groupStore t E₀ Pay (g + 1)) a x →
      (recordOf (groupStore t E₀ Pay (g + 1)) x).isSome = true := by
  intro a x hnew hused
  have h6 : 6 ≤ g + 1 := Nat.le_succ_of_le hg
  obtain ⟨-, -, -, hadd, -⟩ := new_groupStore hb hg hnew
  obtain ⟨c, i, hc, hi, hx⟩ := hused
  have hE : recordOf E₀ a = some c := ((groupStore_recordOf hb h6).mp hc).2
  have huE : UsedRef E₀ a x := ⟨c, i, hE, hi, hx⟩
  have hheld : ∀ y, StoredBelow t E₀ Pay (g + 1) y →
      (recordOf (groupStore t E₀ Pay (g + 1)) y).isSome = true := by
    intro y hy
    obtain ⟨cy, hcy⟩ := storedBelow_record hC hb hax hP hws hy
    rw [(groupStore_recordOf hb h6).mpr ⟨hy, hcy⟩]
    rfl
  by_cases hcov : Claim.CoveredAt t (some (valLimit g)) x
  · exact hheld x (storedBelow_succ (storedBelow_of_covered hbr hcov))
  · apply hheld x
    apply storedBelow_of_adds hg
    rcases groupAdds_cases hC hax hw hadd with ⟨hra, -⟩ |
        ⟨r, hr, -, -, p, hp, -, -, hrefs, -⟩ | ⟨ro, hro, hs, had, -⟩ | hpay
    · exact GroupAdds.reach (GroupReach.ref hra huE hcov)
    · exfalso
      have e : p = c := Option.some.inj (hp.symm.trans hE)
      rw [e] at hrefs
      rw [hrefs] at hx
      simp at hx
    · exact GroupAdds.reach (GroupReach.axiomRef hro hs had huE hcov)
    · rcases payAdds_cases hP hpay with ⟨hra, -⟩ | ⟨-, -, -, -, -, p, hp, -, -, hrefs, -⟩
      · exact GroupAdds.payReach (PayReach.ref hra huE hcov)
      · exfalso
        have e : p = c := Option.some.inj (hp.symm.trans hE)
        rw [e] at hrefs
        rw [hrefs] at hx
        simp at hx

/-- **`Admits.usedClosed`, one step**: the store after a group's admission is closed under what
its records use, if the store before it is. -/
theorem groupStore_usedClosed (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀) (hP : PayloadFacts t E₀ Pay)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) {g : Nat} (hg : 6 ≤ g)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) (hprev : UsedClosed (groupStore t E₀ Pay g)) :
    UsedClosed (groupStore t E₀ Pay (g + 1)) := by
  have h6 : 6 ≤ g + 1 := Nat.le_succ_of_le hg
  have hmono : ∀ x cx, recordOf (groupStore t E₀ Pay g) x = some cx →
      recordOf (groupStore t E₀ Pay (g + 1)) x = some cx := by
    intro x cx h
    obtain ⟨hs, hE⟩ := (groupStore_recordOf hb hg).mp h
    exact (groupStore_recordOf hb h6).mpr ⟨storedBelow_succ hs, hE⟩
  have hmonoS : ∀ x, (recordOf (groupStore t E₀ Pay g) x).isSome = true →
      (recordOf (groupStore t E₀ Pay (g + 1)) x).isSome = true := by
    intro x h
    obtain ⟨cx, hcx⟩ := Option.isSome_iff_exists.mp h
    rw [hmono x cx hcx]
    rfl
  have hnewOf : ∀ x cx, recordOf (groupStore t E₀ Pay (g + 1)) x = some cx →
      ¬ StoredBelow t E₀ Pay g x →
      New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) x ∧ GroupAdds t E₀ Pay g x := by
    intro x cx hcx hold
    have hnew : New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) x := by
      refine ⟨?_, ?_⟩
      · rw [hcx]
        rfl
      · cases hr : recordOf (groupStore t E₀ Pay g) x with
        | none => rfl
        | some c' => exact absurd ((groupStore_recordOf hb hg).mp hr).1 hold
    obtain ⟨-, -, -, hadd, -⟩ := new_groupStore hb hg hnew
    exact ⟨hnew, hadd⟩
  obtain ⟨hp1, hp2⟩ := hprev
  refine ⟨fun a c hc => ?_, fun B c ms hc hms i m hm => ?_⟩
  · have hE : recordOf E₀ a = some c := ((groupStore_recordOf hb h6).mp hc).2
    by_cases hold : StoredBelow t E₀ Pay g a
    · obtain ⟨ho, hu⟩ := hp1 a c ((groupStore_recordOf hb hg).mpr ⟨hold, hE⟩)
      exact ⟨hmonoS _ ho, fun i hi x hx => hmonoS _ (hu i hi x hx)⟩
    · obtain ⟨hnew, -⟩ := hnewOf a c hc hold
      refine ⟨?_, fun i hi x hx => ?_⟩
      · by_cases hpr : IsProj c
        · obtain ⟨cb, hcb, -⟩ := groupStore_projMember hC hb hax hP hg hw a c hnew hc hpr
          rw [hcb]
          rfl
        · rw [ownerOf_of_not_proj hpr, hc]
          rfl
      · exact groupStore_used_held hC hb hbr hax hP hws hg hw a x hnew ⟨c, i, hc, hi, hx⟩
  · have hE : recordOf E₀ B = some c := ((groupStore_recordOf hb h6).mp hc).2
    by_cases hold : StoredBelow t E₀ Pay g B
    · obtain ⟨h1, h2⟩ := hp2 B c ms ((groupStore_recordOf hb hg).mpr ⟨hold, hE⟩) hms i m hm
      exact ⟨hmono _ _ h1, fun ind hind j hj => hmono _ _ (h2 ind hind j hj)⟩
    · obtain ⟨-, hadd⟩ := hnewOf B c hc hold
      rcases groupAdds_cases hC hax hw hadd with ⟨hrB, r, hr, hrB'⟩ |
          ⟨r, hr, -, -, p, hp, hproj, -⟩ | ⟨ro, hro, hs, had, c₂, ax, hc₂, hinfo, -⟩ | hpay
      rotate_right
      · rcases payAdds_cases hP hpay with ⟨hrB, -⟩ | ⟨-, -, -, -, -, p, hp, hproj, -⟩
        · obtain ⟨h1, h2⟩ := hP.blockMembers g B c ms hrB hE hms i m hm
          have hca1 : GroupAdds t E₀ Pay g (memberAddr B i m) :=
            Or.inr (Or.inr ⟨B, c, hrB, hE, ⟨ms, hms⟩, Or.inr ⟨ms, i, m, hms, hm, Or.inl rfl⟩⟩)
          refine ⟨(groupStore_recordOf hb h6).mpr ⟨storedBelow_of_adds hg hca1, h1⟩,
            fun ind hind j hj => ?_⟩
          have hca2 : GroupAdds t E₀ Pay g (ctorAddr B i j) :=
            Or.inr (Or.inr ⟨B, c, hrB, hE, ⟨ms, hms⟩,
              Or.inr ⟨ms, i, m, hms, hm, Or.inr ⟨ind, j, hind, hj, rfl⟩⟩⟩)
          exact (groupStore_recordOf hb h6).mpr ⟨storedBelow_of_adds hg hca2, h2 ind j hind hj⟩
        · exfalso
          have e : p = c := Option.some.inj (hp.symm.trans hE)
          rw [e] at hproj
          exact proj_not_block hproj ⟨ms, hms⟩
      · have hrec := topRec_recordOf hC.hashedStored r
        rw [hrB'] at hrec
        have ec : c = r.c := Option.some.inj (hE.symm.trans hrec)
        have hms' : r.c.info = .muts ms := by
          rw [← ec]
          exact hms
        obtain ⟨h1, h2⟩ := topRec_block_members hC.runStore hC.hashedStored r hms' hm
        rw [hrB'] at h1 h2
        have hca1 : GroupAdds t E₀ Pay g (memberAddr B i m) :=
          Or.inl (Or.inr (Or.inl ⟨B, c, hrB, hE, ⟨ms, hms⟩,
            Or.inr ⟨ms, i, m, hms, hm, Or.inl rfl⟩⟩))
        refine ⟨(groupStore_recordOf hb h6).mpr ⟨storedBelow_of_adds hg hca1, h1⟩,
          fun ind hind j hj => ?_⟩
        have hca2 : GroupAdds t E₀ Pay g (ctorAddr B i j) :=
          Or.inl (Or.inr (Or.inl ⟨B, c, hrB, hE, ⟨ms, hms⟩,
            Or.inr ⟨ms, i, m, hms, hm, Or.inr ⟨ind, j, hind, hj, rfl⟩⟩⟩))
        exact (groupStore_recordOf hb h6).mpr ⟨storedBelow_of_adds hg hca2, h2 ind j hind hj⟩
      · exfalso
        have e : p = c := Option.some.inj (hp.symm.trans hE)
        rw [e] at hproj
        exact proj_not_block hproj ⟨ms, hms⟩
      · exfalso
        have e : c₂ = c := Option.some.inj (hc₂.symm.trans hE)
        rw [e] at hinfo
        rw [hinfo] at hms
        cases hms

/-- **`Admits.usedClosed`**: every store of the sequence is closed under what its records
use. -/
theorem groupStore_usedClosed_all (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀) (hP : PayloadFacts t E₀ Pay)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) :
    ∀ g, 6 ≤ g → UsedClosed (groupStore t E₀ Pay g) := by
  intro g
  induction g with
  | zero =>
    intro hg
    omega
  | succ n ih =>
    intro hg
    by_cases h : n + 1 = 6
    · rw [h, groupStore_six]
      exact StoreInhabit.store_usedClosed
    · obtain ⟨recs, hw⟩ := hws n
      exact groupStore_usedClosed hC hb hbr hax hP hws (by omega) hw (ih (by omega))

/-- **`Admits.evidenceRefs`**: the store after a group's admission holds the record at every
reference a proof in the evidence of a role of the group uses, other than the role's own
address: a reference covered at the group's validation limit was held before, any other is
reached by the group's admission. -/
theorem groupStore_evidenceRefs (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀) (hP : PayloadFacts t E₀ Pay)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) {g : Nat} (hg : 6 ≤ g)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) :
    ∀ r ∈ roleGroup g, ∀ (arr : Array (Ix.Kernel.Evidence _root_.Address))
      (thm x : _root_.Address), (r, arr) ∈ t.evidence.toList →
      Ix.Kernel.Evidence.proof thm ∈ arr.toList → UsedRef E₀ thm x →
      t.addressOf? r ≠ some x → (recordOf (groupStore t E₀ Pay (g + 1)) x).isSome = true := by
  intro r hr arr thm x hm hthm hu hne
  have h6 : 6 ≤ g + 1 := Nat.le_succ_of_le hg
  by_cases hcov : Claim.CoveredAt t (some (valLimit g)) x
  · have hs : StoredBelow t E₀ Pay g x := storedBelow_of_covered hbr hcov
    obtain ⟨cx, hcx⟩ := storedBelow_record hC hb hax hP hws hs
    rw [(groupStore_recordOf hb h6).mpr ⟨storedBelow_succ hs, hcx⟩]
    rfl
  · have hrx : GroupReach t E₀ g x := GroupReach.evidenceRef hr hm hthm hu hne hcov
    obtain ⟨y, hy, hya⟩ := hrx.listed hC.hashedStored hw
    have hcx : recordOf E₀ x = some y.c := by
      rw [← hya]
      exact topRec_recordOf hC.hashedStored y
    rw [(groupStore_recordOf hb h6).mpr ⟨storedBelow_of_adds hg (GroupAdds.reach hrx), hcx⟩]
    rfl

end Walk

end IxVM.Refinement.Binding
