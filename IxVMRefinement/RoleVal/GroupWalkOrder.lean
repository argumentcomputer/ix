import IxVMRefinement.RoleVal.GroupWalkLim
import IxVMRefinement.Claim.TopWalkOrder

/-! # The walks of a role's validation, with the operation order of what they walk

The forms of `IxVMRefinement.RoleVal.GroupWalkLim` with `Claim.TopRecsOrdered`: every used
reference of a record the validation walks is `Claim.OpOrderedAt` or covered at the group's
validation limit (`walk_ctx`'s `assert_op_reached_in_order`).

* `ValidateRoleIn.lim_walks_ordered`: the walk of the role's bound record.
* `RunCheckFullIn.lim_walks_ordered`, `ValidateRoleIn.eqns_evidence_walks_ordered`: an observed
  walk; the evidence theorems of a role specified by equations.
* `RefWalkedUnderCtxIn.lim_walks_ordered`, `ValidateRoleIn.op_certificate_walks_ordered`: a
  reference walked under `walk_ctx`, which is itself ordered; the references of an operation's
  certificates. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.RoleVal

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core

set_option linter.unusedVariables false

/-- **The walk of a role's bound record, ordered.** -/
theorem ValidateRoleIn.lim_walks_ordered {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {g : Nat} {ro : Ix.Kernel.Role}
    (hv : ValidateRoleIn calls bAddr t g ro)
    (hw : roleWalksBound ro = true ∨ anchorWalked ro = true) :
    ∃ (a : _root_.Address) (recs : List (Claim.TopRec calls bAddr t (some (groupValLimit g)))),
      t.addressOf? ro = some a ∧ Claim.TopRecsClosed recs ∧ Claim.TopRecsOrdered recs ∧
        a ∈ recs.map (·.addr) := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsub⟩ := hv
  obtain ⟨a, x_a, r_w, h_w, h_w', cs_w, had, hrc_w, ha_w, ev_w, hsub_w⟩ :=
    validate_role_bound_walk hrc htbl ev hw
  obtain ⟨-, recs, hmem, hcl, hord, -⟩ :=
    Claim.run_check_transitive_lim_ordered (lim := some (groupValLimit g))
      (show Claim.RCLimRep t bAddr (some (groupValLimit g)) h_w x_rc from hrc_w) ha_w ev_w
  have hs : ∀ cl ∈ cs_w, cl ∈ calls := fun cl hcl => hsub cl (hsub_w cl hcl)
  refine ⟨a, recs.map (Claim.TopRec.mono hs), had, hcl.mono hs, hord.mono hs, ?_⟩
  rw [Claim.map_addr_topRec_mono]
  exact hmem

/-- **An observed walk, ordered.** -/
theorem RunCheckFullIn.lim_walks_ordered {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {n : Nat} {addr : _root_.Address}
    (hv : RunCheckFullIn calls bAddr t n addr) :
    ∃ recs : List (Claim.TopRec calls bAddr t (some n)),
      Claim.TopRecsClosed recs ∧ Claim.TopRecsOrdered recs ∧ addr ∈ recs.map (·.addr) := by
  obtain ⟨h_w, h_w', rc, ap, r_w, cs_w, hrc, ha, ev, hsub⟩ := hv
  obtain ⟨-, recs, hmem, hcl, hord, -⟩ :=
    Claim.run_check_transitive_lim_ordered (lim := some n)
      (show Claim.RCLimRep t bAddr (some n) h_w rc from hrc) ha ev
  refine ⟨recs.map (Claim.TopRec.mono hsub), hcl.mono hsub, hord.mono hsub, ?_⟩
  rw [Claim.map_addr_topRec_mono]
  exact hmem

/-- **The evidence theorems of a role specified by equations, walked and ordered.** -/
theorem ValidateRoleIn.eqns_evidence_walks_ordered {calls : List (Call F)}
    {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable} {g : Nat} {ro : Ix.Kernel.Role}
    (hv : ValidateRoleIn calls bAddr t g ro) (h5 : roleSpecKindNat ro = 5)
    {arr : Array (Ix.Kernel.Evidence _root_.Address)} {thm : _root_.Address}
    (hm : (ro, arr) ∈ t.evidence.toList) (hthm : Ix.Kernel.Evidence.proof thm ∈ arr.toList) :
    ∃ recs : List (Claim.TopRec calls bAddr t (some (groupValLimit g))),
      Claim.TopRecsClosed recs ∧ Claim.TopRecsOrdered recs ∧ thm ∈ recs.map (·.addr) := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsub⟩ := hv
  exact ((validate_role_eqns_evidence_observed hrc htbl ev h5 arr thm hm hthm).mono
    hsub).lim_walks_ordered

/-- **A reference walked under the context `walk_ctx` gives it, ordered**: the reference itself
is ordered (`walk_ctx`'s assertion), and it is covered or a record of a closed, ordered list. -/
theorem RefWalkedUnderCtxIn.lim_walks_ordered {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {n : Nat} {b : _root_.Address}
    (hv : RefWalkedUnderCtxIn calls bAddr t n b) :
    Claim.OpOrderedAt t (some n) b ∧
    (Claim.CoveredAt t (some n) b ∨
      ∃ recs : List (Claim.TopRec calls bAddr t (some n)),
        Claim.TopRecsClosed recs ∧ Claim.TopRecsOrdered recs ∧ b ∈ recs.map (·.addr)) := by
  obtain ⟨⟨h₀, h₀', x_rc₀, x_b₀, r₀, cs₀, hrc₀, hb₀, ev₀, hs₀⟩,
    h₁, h₂, h₃, x_rc, x_b, rc', r_w, cs_c, cs_w, hrc, hb, evc, evw, hsub⟩ := hv
  refine ⟨Claim.walk_ctx_ordered (lim := some n)
    (show Claim.RCLimRep t bAddr (some n) h₁ x_rc from hrc) hb evc, ?_⟩
  obtain ⟨ext, hcase⟩ :=
    Claim.walk_ctx_lim_spec (lim := some n)
      (show Claim.RCLimRep t bAddr (some n) h₁ x_rc from hrc) hb evc
  rcases hcase with hrc' | ⟨hcov, -⟩
  · right
    subst hrc'
    obtain ⟨-, recs, hmem, hcl, hord, -⟩ :=
      Claim.run_check_transitive_lim_ordered (lim := some n)
        (show Claim.RCLimRep t bAddr (some n) h₂ _ from hrc.mono ext) (S0.addr_mono ext hb) evw
    refine ⟨recs.map (Claim.TopRec.mono hsub), hcl.mono hsub, hord.mono hsub, ?_⟩
    rw [Claim.map_addr_topRec_mono]
    exact hmem
  · exact Or.inl hcov

/-- **The references of an operation's certificate, walked and ordered**: each reference the
certificate uses other than the operation's own address is ordered, and covered or a record of
a closed, ordered list walked at the group's validation limit. -/
theorem ValidateRoleIn.op_certificate_walks_ordered {calls : List (Call F)}
    {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable} {g : Nat} {ro : Ix.Kernel.Role}
    (hv : ValidateRoleIn calls bAddr t g ro) (h2 : roleSpecKindNat ro = 2)
    {arr : Array (Ix.Kernel.Evidence _root_.Address)} {thm a : _root_.Address}
    (ha : t.addressOf? ro = some a) (hm : (ro, arr) ∈ t.evidence.toList)
    (hthm : Ix.Kernel.Evidence.proof thm ∈ arr.toList) :
    ∃ (rawBytes : ByteArray) (c : Ixon.Constant),
      rawBytes.size < 4294967296 ∧ Hashed calls rawBytes ∧ Address.blake3Pure rawBytes = thm ∧
      Ixon.deConstantExact rawBytes = .ok c ∧
      ∀ j : Nat, (hj : j < c.refs.toList.length) → j ∈ S0.usedRefIdxs c →
        c.refs.toList[j] ≠ a →
        Claim.OpOrderedAt t (some (groupValLimit g)) c.refs.toList[j] ∧
        (Claim.CoveredAt t (some (groupValLimit g)) c.refs.toList[j] ∨
          ∃ recs : List (Claim.TopRec calls bAddr t (some (groupValLimit g))),
            Claim.TopRecsClosed recs ∧ Claim.TopRecsOrdered recs ∧
              c.refs.toList[j] ∈ recs.map (·.addr)) := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsub⟩ := hv
  obtain ⟨rawBytes, c, hsz, hh, hb, hde, hg, hw⟩ :=
    (validate_role_op_certificates_observed hrc htbl ev h2 arr thm a ha hm hthm).mono hsub
  exact ⟨rawBytes, c, hsz, hh, hb, hde, fun j hj hu hne => (hw j hj hu hne).lim_walks_ordered⟩

end IxVM.Refinement.RoleVal
