import IxVMRefinement.Obs.KernelModeled2
import IxVMRefinement.Obs.KernelModeled3
import IxVMRefinement.Obs.KernelModeled4
import IxVMRefinement.Obs.KernelModeled5

/-! # What an observed family check calls, read off its paths

Call-level reading lemmas for `KernelModeled::check_family` and the functions on its path whose
assertions the facts of one family check (`FamilyAlias.FamilyCallFacts`) rest on. Each lemma
reads one function's generated path and names the calls it makes, with their arguments and the
values the source asserts, each call among the caller's calls with its own calls; the semantic
reading of those calls is left to the facts' producer.

* `checkFamily_calls`: the family check's renaming source (the types, then the constructors, then
  the recursors), its three member checks (`members_val`) with the lists of members each member's
  type may not name (all the members for a type; the constructors and the recursors for a
  constructor; the recursors for a recursor), the family record's recursors (`family_recs`), the
  role assertion at them (`assert_no_role`), the order assertion at the family record
  (`KernelRoles::assert_in_order`), the family record's reference check (`family_refs_ok`) and the
  recursors' check (`check_recs`) from the first recursor with no form fixed;
* `memberVal_reads`: a member against its model (`member_val`): the model is advice, the
  member's loaded type names none of the listed members, the model is a definition at the
  member's level count whose type is the member's type renamed, structurally;
* `familyRefsOk_inner`, `assertInnerRefsSafe_calls`: the family record's references are checked
  with the walk's inner assertions (`KernelClaim::assert_safe_used_refs` from no exclusion, and
  `assert_used_not_block`) on its reference table and its used indices;
* `checkRecs_step`: at each recursor of the family record, the loaded recursor declares no K, is
  safe, has its block's parameter count, its type is well scoped at its level count and names no
  recursor of the family, the renaming leaves its parameter domains as they are, and its rules are
  checked (`check_rules`), then the next recursor. -/

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- **A call of `f` at `args` returning `v`, among `calls`**, with its own calls among them. -/
def CalledInR (calls : List (Call F)) (f : String) (args : List (SourceValue F))
    (v : SourceValue F) : Prop :=
  ∃ (h₁ h₂ : Heap F) (cs : List (Call F)),
    ObsFn Obs.W f args h₁ v h₂ cs ∧ (⟨f, args, h₁⟩ : Call F) ∈ calls ∧ ∀ cl ∈ cs, cl ∈ calls

/-- **A call of `f` at `args` among `calls`**, with its own calls among them. -/
def CalledIn (calls : List (Call F)) (f : String) (args : List (SourceValue F)) : Prop :=
  ∃ v, CalledInR calls f args v

/-! ## `check_family` -/

/-- **The calls of an observed family check** (module docstring). -/
theorem checkFamily_calls {rc b rb : SourceValue F} {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelModeled::check_family" [rc, b, rb] h r h' calls) :
    ∃ (tys ctors recs ctorRec src tyM ctorM recM dst aset later wset s n np uo bnl :
        SourceValue F),
      CalledInR calls Obs.Names.«Lists::concat<&[Field; 32]>» [ctors, recs] ctorRec ∧
      CalledInR calls Obs.Names.«Lists::concat<&[Field; 32]>» [tys, ctorRec] src ∧
      CalledInR calls Obs.Names.«Lists::concat<&[Field; 32]>» [ctors, recs] later ∧
      CalledIn calls "KernelModeled::members_val" [tys, tyM, src, dst, aset, src] ∧
      CalledIn calls "KernelModeled::members_val" [ctors, ctorM, src, dst, aset, later] ∧
      CalledIn calls "KernelModeled::members_val" [recs, recM, src, dst, aset, recs] ∧
      CalledInR calls "KernelModeled::family_recs" [rb] recs ∧
      CalledIn calls "KernelModeled::assert_no_role" [rc, recs] ∧
      CalledIn calls "KernelRoles::assert_in_order" [rc, rb] ∧
      CalledIn calls "KernelModeled::family_refs_ok" [rc, rb, b, wset] ∧
      CalledIn calls "KernelModeled::check_recs"
        [rc, tys, recs, recM, src, dst, aset, s, n, .field 0, np, uo, bnl, recs, .field 0] := by
  match Obs.«KernelModeled::check_family».obs ev with
  | .run (ev960 := eC1) (ev939 := eC2) (ev_gkddqxhv := eL) (ev_edyzsqzv := eTys)
      (ev_ittpynob := eCtors) (ev_biaifgpd := eRecM) (ev852 := eRecs) (ev_ursqbimm := eRole)
      (ev_yqjbwijz := eOrd) (ev1305 := eRefs) (ev1343 := eChk) (hc1474 := hc) .. =>
    refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      ⟨_, _, _, eC1, ?_, ?_⟩, ⟨_, _, _, eC2, ?_, ?_⟩, ⟨_, _, _, eL, ?_, ?_⟩,
      ⟨_, _, _, _, eTys, ?_, ?_⟩, ⟨_, _, _, _, eCtors, ?_, ?_⟩, ⟨_, _, _, _, eRecM, ?_, ?_⟩,
      ⟨_, _, _, eRecs, ?_, ?_⟩, ⟨_, _, _, _, eRole, ?_, ?_⟩, ⟨_, _, _, _, eOrd, ?_, ?_⟩,
      ⟨_, _, _, _, eRefs, ?_, ?_⟩, ⟨_, _, _, _, eChk, ?_, ?_⟩⟩ <;>
    first
      | (rw [hc]; simp; done)
      | (intro cl hcl; rw [hc]; simp [hcl])

/-! ## `member_val` -/

/-- **A member against its model** (`member_val`, module docstring). -/
theorem memberVal_reads {m md src dst aset later : SourceValue F} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelModeled::member_val" [m, md, src, dst, aset, later] h r h' calls) :
    ∃ (p ci nl ty pm nlm mty w₁ w₂ w₃ ren : SourceValue F) (hp hm : Heap F),
      CalledInR calls "KernelClaim::addr_set_member" [md, aset] (.field 1) ∧
      (∃ (h₁ : Heap F) (cs : List (Call F)), ObsFn Obs.W "Ingress::get_ci" [m] h₁ p hp cs ∧
        (⟨"Ingress::get_ci", [m], h₁⟩ : Call F) ∈ calls ∧ ∀ cl ∈ cs, cl ∈ calls) ∧
      loadValue hp p = .ok ci ∧
      CalledInR calls "KernelModeled::ci_lvls_type" [ci] (.tuple [nl, ty]) ∧
      CalledInR calls "KernelModeled::expr_mentions_addrs" [ty, later] (.field 0) ∧
      (∃ (h₁ : Heap F) (cs : List (Call F)), ObsFn Obs.W "Ingress::get_ci" [md] h₁ pm hm cs ∧
        (⟨"Ingress::get_ci", [md], h₁⟩ : Call F) ∈ calls ∧ ∀ cl ∈ cs, cl ∈ calls) ∧
      loadValue hm pm =
        .ok (.construct "KernelTypes::KConstantInfo" "Defn" [nlm, mty, w₁, w₂, w₃]) ∧
      nl = nlm ∧
      CalledInR calls "KernelModeled::rename" [ty, src, dst] ren ∧
      CalledInR calls "KernelCheck::kexpr_struct_eq" [ren, mty] (.field 1) := by
  match Obs.«KernelModeled::member_val».obs ev with
  | .run (ev25 := e25) (heq48 := q48) (ev78 := e78) (ld72 := l72) (ev62 := e62)
      (ev_nczzuuzf := eM) (heq_pbkckosz := qM) (ev117 := e117) (ld111 := l111) (heq187 := q187)
      (ev226 := e226) (ev212 := e212) (heq264 := q264) (hc269 := hc) .. =>
    subst q48 qM q264
    refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _,
      ⟨_, _, _, e25, ?_, ?_⟩, ⟨_, _, e78, ?_, ?_⟩, l72, ⟨_, _, _, e62, ?_, ?_⟩,
      ⟨_, _, _, eM, ?_, ?_⟩, ⟨_, _, e117, ?_, ?_⟩, l111, q187, ⟨_, _, _, e226, ?_, ?_⟩,
      ⟨_, _, _, e212, ?_, ?_⟩⟩ <;>
    first
      | (rw [hc]; simp; done)
      | (intro cl hcl; rw [hc]; simp [hcl])

/-! ## The family record's references -/

/-- **`family_refs_ok` checks the family record's references with the walk's inner assertions**:
it loads the family record and runs `assert_inner_refs_safe` on its reference table and its used
indices. -/
theorem familyRefsOk_inner {rc rb b wset : SourceValue F} {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelModeled::family_refs_ok" [rc, rb, b, wset] h r h' calls) :
    ∃ (w₁ w₂ refs w₃ w₄ used : SourceValue F),
      CalledInR calls "Ingress::load_verified_constant" [rb]
        (.construct "Ixon::Constant" "Mk" [w₁, w₂, refs, w₃, w₄]) ∧
      CalledInR calls "KernelClaim::const_idxs_of"
        [.construct "Ixon::Constant" "Mk" [w₁, w₂, refs, w₃, w₄]] used ∧
      CalledIn calls "KernelModeled::assert_inner_refs_safe" [rc, refs, used] := by
  match Obs.«KernelModeled::family_refs_ok».obs ev with
  | .run (ev14 := e14) (ev_ozxzdina := eIdx) (ev_tnqzszcy := eIn) (hc222 := hc) .. =>
    refine ⟨_, _, _, _, _, _, ⟨_, _, _, e14, ?_, ?_⟩, ⟨_, _, _, eIdx, ?_, ?_⟩,
      ⟨_, _, _, _, eIn, ?_, ?_⟩⟩ <;>
    first
      | (rw [hc]; simp; done)
      | (intro cl hcl; rw [hc]; simp [hcl])

/-- **The walk's inner assertions on a record's references** (`assert_inner_refs_safe`): the
used-reference safety check from no exclusion, and the block check of each used reference. -/
theorem assertInnerRefsSafe_calls {rc refs used : SourceValue F} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelModeled::assert_inner_refs_safe" [rc, refs, used] h r h' calls) :
    CalledIn calls "KernelClaim::assert_safe_used_refs"
        [rc, refs, used, .field 0,
          .construct Obs.Names.«RBTreeMap::RBTreeMap<Field>» "Nil" []] ∧
      CalledIn calls "KernelModeled::assert_used_not_block" [refs, used, .field 0] := by
  match Obs.«KernelModeled::assert_inner_refs_safe».obs ev with
  | .run (ev_mxwoukvn := eS) (ev_hemnmxwe := eB) (hc_sgljalbe := hc) .. =>
    refine ⟨⟨_, _, _, _, eS, ?_, ?_⟩, ⟨_, _, _, _, eB, ?_, ?_⟩⟩ <;>
    first
      | (rw [hc]; simp; done)
      | (intro cl hcl; rw [hc]; simp [hcl])

/-! ## `check_recs` -/

/-- **One step of the recursors' check** (`check_recs`, module docstring): the list is empty, or
its first recursor is loaded with no K and safe, at its block's parameter count, its type is well
scoped at its level count and names no recursor of the family, its parameter domains are those of
its renaming, its rules are checked, and the check goes on at the rest. -/
theorem checkRecs_step {rc tys recs models src dst aset s n k np uo bnl fam form : SourceValue F}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelModeled::check_recs"
      [rc, tys, recs, models, src, dst, aset, s, n, k, np, uo, bnl, fam, form] h r h' calls) :
    loadValue h recs = .ok (.construct Obs.Names.«Lists::Node<&[Field; 32]>» "Nil" []) ∨
    ∃ (x rest rm mrest p nl ty rnp ni nmot nmin rules w₁ w₂ ren nil₁ nil₂ w₃ w₄ pd pdm rp s' k'
        form' : SourceValue F) (hp : Heap F),
      loadValue h recs = .ok (.construct Obs.Names.«Lists::Node<&[Field; 32]>» "Cons" [x, rest]) ∧
      loadValue h models =
        .ok (.construct Obs.Names.«Lists::Node<&[Field; 32]>» "Cons" [rm, mrest]) ∧
      (∃ cs, ObsFn Obs.W "Ingress::get_ci" [x] h p hp cs ∧ ∀ cl ∈ cs, cl ∈ calls) ∧
      loadValue hp p = .ok (.construct "KernelTypes::KConstantInfo" "Rec"
        [nl, ty, rnp, ni, nmot, nmin, rules, .field 0, .field 0, w₁, w₂]) ∧
      rnp = np ∧
      CalledIn calls "KernelCheck::validate_expr_well_scoped" [ty, .field 0, nl] ∧
      CalledInR calls "KernelModeled::expr_mentions_addrs" [ty, fam] (.field 0) ∧
      CalledInR calls "KernelModeled::peel_collect" [ty, rnp, nil₁] (.tuple [w₃, pd]) ∧
      CalledInR calls "KernelModeled::rename" [ty, src, dst] ren ∧
      CalledInR calls "KernelModeled::peel_collect" [ren, rnp, nil₂] (.tuple [w₄, pdm]) ∧
      CalledInR calls "KernelCheck::spec_params_ptr_eq" [pd, pdm] (.field 1) ∧
      CalledInR calls "KernelModeled::check_rules"
        [rc, rm, nl, ty, rp, ni, rules, src, dst, aset, s] s' ∧
      CalledInR calls "KernelModeled::check_recs"
        [rc, tys, rest, mrest, src, dst, aset, s', n, k', np, uo, bnl, fam, form'] r := by
  match Obs.«KernelModeled::check_recs».obs ev with
  | .Nil (ld12 := l12) .. => exact Or.inl l12
  | .Cons (ld12 := l12) (ld51 := l51) (ev82 := e82) (ld76 := l76) (heq190 := qk)
      (heq217 := qu) (heq245 := qnp) (ev523 := eScope) (ev571 := eMent) (heq594 := qM)
      (ev_uprevpxl := eP1) (ev_svgicqcr := eRen) (ev_oqkxxxxs := eP2) (ev_eejlfykm := eEq)
      (heq_wxopjlsu := qEq) (ev904 := eRules) (ev1016 := eNext) (hc1137 := hc) .. =>
    subst qk qu qM qEq
    refine Or.inr ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      l12, l51, ⟨_, e82, ?_⟩, l76, qnp, ⟨_, _, _, _, eScope, ?_, ?_⟩, ⟨_, _, _, eMent, ?_, ?_⟩,
      ⟨_, _, _, eP1, ?_, ?_⟩, ⟨_, _, _, eRen, ?_, ?_⟩, ⟨_, _, _, eP2, ?_, ?_⟩,
      ⟨_, _, _, eEq, ?_, ?_⟩, ⟨_, _, _, eRules, ?_, ?_⟩, ⟨_, _, _, eNext, ?_, ?_⟩⟩ <;>
    first
      | (rw [hc]; simp; done)
      | (intro cl hcl; rw [hc]; simp [hcl])

end IxVM.Refinement.Typing.FamilyAlias
