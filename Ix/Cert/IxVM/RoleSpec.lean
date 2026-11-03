import IxC.Kernel.Ixon.RoleSpecTable
import Ix.IxVM.RoleSpecGen

/-! # Certified `RoleSpec` Correspondence (`IxVM` ↔ `IxC`)

This module connects `Ix.IxVM.RoleSpecGen` (including its Formal Aiur emitter
`renderFormalAiur : Except String String` for `module KernelRoleSpec`) with the
flattened DAG specification model in `IxC.Kernel.Ixon.RoleSpecTable`.

Specifically, it establishes:
1. `roleIdx r = r.idx` for every `r : Role`, and `Role.all.length = 103`.
2. `checkGroups` succeeds (`checkGroups = .ok ()`), ensuring `groupOrder` covers
   every role in `Role.all` with closed blocks and causally ordered dependencies.
3. Every role `r : Role` has well-formed specification expressions (`r.specAllClosedWF = Bool.true`),
   so its anchor type (`buildAnchorType`), axiom type (`buildAxiomType`), operation/equation
   type (`buildEqnType`), unconditional equations (`buildOpEqs`), closed equation/certificate
   statements (`buildEqnList`), and block member types (`buildRoleBlockExpected`)
   faithfully reconstruct `Ix.Kernel.Role.spec r` under any `RoleTable` resolver `t.keyOf`.
4. `evidenceAllowedCode` faithfully encodes `Option Bool` entries in `(r.spec).evidenceAllowed`:
   `0` (`none`: either), `1` (`some true`: defeq only), and `2` (`some false`: proof only).
-/

namespace Ix.Cert.IxVM

open Ix.Kernel
open IxVM.RoleSpecGen

/-- `RoleSpecGen.roleIdx` agrees identically with `Role.idx` (`Role.all.idxOf`). -/
theorem roleIdx_eq_idx (r : Role) : roleIdx r = r.idx := rfl

/-- `Role.all` has exactly `103` roles. -/
theorem role_count_eq : Role.all.length = 103 := by decide

/-- `Role.specVersion` is `3`. -/
theorem spec_version_eq : specVersion = 3 := rfl

set_option maxRecDepth 65536 in
private theorem checkGroups_isOk : checkGroups.isOk = Bool.true := by decide

/-- `RoleSpecGen.checkGroups` succeeds (`Except.ok ()`), certifying that:
- `groups` covers every role in `Role.all` without duplicates,
- each group equals `r.block` for every `r` in the group,
- every dependency `d ∈ r.deps` appears in an earlier group, and
- well-founded operation groups and equation groups form the expected tail blocks. -/
theorem checkGroups_ok : checkGroups = .ok () := by
  have hok := checkGroups_isOk
  cases h : checkGroups with
  | error e => rw [h] at hok; nomatch hok
  | ok u => cases u; rfl

set_option maxRecDepth 65536 in
/-- `firstWellFoundedGroup` succeeds. -/
theorem firstWellFoundedGroup_isOk : firstWellFoundedGroup.isOk = Bool.true := by decide

set_option maxRecDepth 65536 in
/-- `firstEquationGroup` succeeds. -/
theorem firstEquationGroup_isOk : (firstEquationGroup).isOk = Bool.true := by decide

/-- `evidenceAllowedCode` faithfully encodes `Option Bool` entries of `(r.spec).evidenceAllowed`:
- `0` iff `b = none` (either defeq or proof)
- `1` iff `b = some true` (defeq only)
- `2` iff `b = some false` (proof only) -/
theorem evidenceAllowedCode_spec (b : Option Bool) :
    evidenceAllowedCode b =
      match b with
      | none => 0
      | some Bool.true => 1
      | some Bool.false => 2 := rfl

/-- Decoding `evidenceAllowedCode b` recovers `b : Option Bool`. -/
def decodeEvidenceAllowed (code : Nat) : Option Bool :=
  match code with
  | 0 => none
  | 1 => some Bool.true
  | _ => some Bool.false

theorem decodeEvidenceAllowed_evidenceAllowedCode (b : Option Bool) :
    decodeEvidenceAllowed (evidenceAllowedCode b) = b := by
  cases b with
  | none => rfl
  | some b => cases b <;> rfl

/-- **Master Role Specification DAG Soundness Theorem**:
For any role `r : Role`, `RoleTable` `t`, level parameter list `ps`, and closed
specification expression `e` appearing in `r.spec` (`e.specClosedWF ps = Bool.true`),
if every role reference in `e` resolves via `t.keyOf` (`substRoleKeysM t.keyOf e = some e'`),
then `buildSpecExpr ps e {}` builds a DAG table `(idx, tbl)` whose evaluation
`evalSpecExpr t.keyOf ps tbl e.dagDepth idx` produces `some e'`. -/
theorem role_spec_dag_sound (t : RoleTable) (ps : List LevelParam) (e e' : Expr .anon)
    (hwf : e.specClosedWF ps = Bool.true)
    (hsub : substRoleKeysM t.keyOf e = some e') :
    ∃ idx tbl,
      buildSpecExpr ps e {} = some (idx, tbl) ∧
      evalSpecExpr t.keyOf ps tbl e.dagDepth idx = some e' := by
  obtain ⟨idx, tbl, hb, -, hev⟩ := buildSpecExpr_spec t.keyOf ps e {} hwf hsub
  exact ⟨idx, tbl, hb, hev⟩

/-- **Identity Role Specification Reconstruction**:
Evaluating the DAG built by `buildSpecExpr ps e {}` under `RoleTable.roleKeyOf`
(`fun r => some (.role r)`) produces `some e.erasePw`. -/
theorem role_spec_dag_roleKeyOf (ps : List LevelParam) (e : Expr .anon)
    (hwf : e.specClosedWF ps = Bool.true) :
    ∃ idx tbl,
      buildSpecExpr ps e {} = some (idx, tbl) ∧
      evalSpecExpr RoleTable.roleKeyOf ps tbl e.dagDepth idx = some e.erasePw := by
  obtain ⟨idx, tbl, hb, -, hev⟩ := buildSpecExpr_eval_roleKeyOf ps e {} hwf
  exact ⟨idx, tbl, hb, hev⟩

end Ix.Cert.IxVM
