import IxVMRefinement.RoleOps.Interface
import IxC.Kernel.Rules.Transport
import IxC.Kernel.Verify.BridgeWfImp

/-! # The interface from the form a circuit check takes

The checker handles terms in annotated form (a `let` replaced by its reduct, binder data
written), so the term it checks is its own annotation, and it checks a certificate's applied
proof in a context that has one entry per variable of the statement: depth 3 for a statement
with one hypothesis, depth 4 for one with two. The kernel's record states every certificate at
depth 4. These lemmas produce the interface of `Interface.lean` from facts of that form.

* `OpFront.of_stored`: the definition's check on terms with no `let`.
* `CertFacts.of_frame`: one certificate from the typing of the applied proof term, with no
  `let`, at depth `2 + (number of hypotheses)`. A derivation at depth 3 is moved to depth 4
  (`Infer.lift`, `DefEq.lift`); the applied term and the statement are unchanged, since they
  mention only the variables below 3.
-/

namespace IxVM.Refinement.RoleOps

open IxVM.Refinement.Core (KExpr KKey)
open IxVM.Refinement.Decl (noLetExpr annot_refl_of_noLetExpr infer_constsResolve)
open Ix.Kernel (Env Expr natDivModNames natName divModCertStmts divModCertApplied)
open Ix.Kernel.Rules (Annot Red DefEq Infer)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- **The definition's check, on terms with no `let`**: a closed term with no `let` is its own
annotation. -/
theorem OpFront.of_stored {env : Env .anon} {ty val : KExpr}
    (htc : ty.looseBVarsBounded 0 = true) (htf : ty.hasFvar = false)
    (htn : noLetExpr ty = true) (htl : ty.allLevelParamsDefined [] = true)
    (hts : ∃ s u, Infer env .full 0 ty s ∧ Red env 0 s (.sort u))
    (hvc : val.looseBVarsBounded 0 = true) (hvf : val.hasFvar = false)
    (hvn : noLetExpr val = true) (hvl : val.allLevelParamsDefined [] = true)
    (hvt : ∃ vt, Infer env .full 0 val vt ∧ DefEq env 0 vt ty) :
    OpFront env ty val ty val :=
  ⟨htc, htf, annot_refl_of_noLetExpr htn htf htc 0, htl, hts, hvc, hvf,
    annot_refl_of_noLetExpr hvn hvf hvc 0, hvl, hvt⟩

private theorem certStmts_all_shape :
    (natDivModNames : List KKey).all (fun c => (divModCertStmts c).all (fun st =>
      st.2.wscopedB 2 && (st.1.length == 1 || st.1.length == 2))) = true := by
  decide +kernel

/-- A certificate statement's equation mentions only the two `Nat` variables, and it has one or
two hypotheses. -/
theorem certStmts_shape {c : KKey} (hc : c ∈ natDivModNames) :
    ∀ st ∈ divModCertStmts c,
      st.2.wscopedB 2 = true ∧ (st.1.length = 1 ∨ st.1.length = 2) := by
  intro st hst
  have h : (st.2.wscopedB 2 && (st.1.length == 1 || st.1.length == 2)) = true :=
    List.all_eq_true.mp (List.all_eq_true.mp certStmts_all_shape c hc) st hst
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact h

/-- **One certificate, from the typing of the applied proof at the statement's own depth.**
`P` is the proof term with the operation already replaced by `val`, closed, with no `let` and
no level parameter; applied to the statement's variables it has, at depth
`2 + (number of hypotheses)`, a type convertible to the statement's equation. -/
theorem CertFacts.of_frame {env : Env .anon} {c : KKey} {val : KExpr}
    {st : List KExpr × KExpr} {P : KExpr} (hS : Ix.Kernel.Open.StoreInv env)
    (hc : c ∈ natDivModNames) (hst : st ∈ divModCertStmts c) (hvf : val.hasFvar = false)
    (hcl : P.looseBVarsBounded 0 = true) (hnf : P.hasFvar = false) (hnl : noLetExpr P = true)
    (hlv : P.allLevelParamsDefined [] = true)
    (htyped : ∃ tp,
      Infer env .full (2 + st.1.length)
          (divModCertApplied P (st.1.map (Expr.substConst0 c val))) tp ∧
        DefEq env (2 + st.1.length) tp (Expr.substConst0 c val st.2)) :
    CertFacts env c val st P := by
  obtain ⟨tp, hinf, hde⟩ := htyped
  obtain ⟨hyps, eqE⟩ := st
  obtain ⟨heqw, hlen⟩ := certStmts_shape hc (hyps, eqE) hst
  have hhyps : ∀ hyp ∈ hyps, hyp.wscopedB 2 = true :=
    (Ix.Kernel.divModCertStmts_wscopedB hc (hyps, eqE) hst).1
  have hPann : Annot 4 P P := annot_refl_of_noLetExpr hnl hnf hcl 4
  cases hyps with
  | nil =>
    have hlen' : (0 : Nat) = 1 ∨ (0 : Nat) = 2 := hlen
    omega
  | cons h1 tl =>
    cases tl with
    | nil =>
      -- one hypothesis: the check is at depth 3, the record at depth 4
      have hinf3 : Infer env .full 3
          (.app (.app (.app P (.fvar 0 (.const natName []))) (.fvar 1 (.const natName [])))
            (.fvar 2 (Expr.substConst0 c val h1))) tp := hinf
      have hde3 : DefEq env 3 tp (Expr.substConst0 c val eqE) := hde
      have hPres : P.constsResolve env = true := by
        cases hinf3 with
        | app hf _ _ _ =>
          cases hf with
          | app hf2 _ _ _ =>
            cases hf2 with
            | app hP _ _ _ => exact infer_constsResolve hP hS hnf
      have hPw : P.wscopedB 3 = true := Ix.Kernel.wscopedB_of_not_hasFvar hnf
      have h1w : (Expr.substConst0 c val h1).wscopedB 2 = true :=
        Ix.Kernel.wscopedB_substConst0 hvf h1 (hhyps h1 (by simp))
      have happw : (Expr.app (.app (.app P (.fvar 0 (.const natName [])))
          (.fvar 1 (.const natName []))) (.fvar 2 (Expr.substConst0 c val h1))).wscopedB 3
            = true := by
        simp [Expr.wscopedB, hPw, h1w]
      have hinf4 := Ix.Kernel.Rules.Infer.lift (Ix.Kernel.EnvExt.refl env) hS.storeClosed
        (p := 3) (g := 1) hinf3
      have hde4 := Ix.Kernel.Rules.DefEq.lift (Ix.Kernel.EnvExt.refl env) hS.storeClosed
        (p := 3) (g := 1) hde3
      rw [Ix.Kernel.Rules.renFV_lift_of_wscoped (Nat.le_refl 3) happw] at hinf4
      rw [Ix.Kernel.Rules.renFV_lift_of_wscoped (by omega : 2 ≤ 3)
        (Ix.Kernel.wscopedB_substConst0 hvf eqE heqw)] at hde4
      refine ⟨hcl, hnf, hlv, hPres, _, _, ?_, hinf4, hde4⟩
      exact .app (.app (.app hPann (.fvar (by decide))) (.fvar (by decide)))
        (.fvar (by decide))
    | cons h2 tl2 =>
      cases tl2 with
      | nil =>
        -- two hypotheses: the check is at depth 4, as the record
        have hinf4 : Infer env .full 4
            (.app (.app (.app (.app P (.fvar 0 (.const natName [])))
              (.fvar 1 (.const natName []))) (.fvar 2 (Expr.substConst0 c val h1)))
              (.fvar 3 (Expr.substConst0 c val h2))) tp := hinf
        have hde4 : DefEq env 4 tp (Expr.substConst0 c val eqE) := hde
        have hPres : P.constsResolve env = true := by
          cases hinf4 with
          | app hf _ _ _ =>
            cases hf with
            | app hf2 _ _ _ =>
              cases hf2 with
              | app hf3 _ _ _ =>
                cases hf3 with
                | app hP _ _ _ => exact infer_constsResolve hP hS hnf
        refine ⟨hcl, hnf, hlv, hPres, _, _, ?_, hinf4, hde4⟩
        exact .app (.app (.app (.app hPann (.fvar (by decide))) (.fvar (by decide)))
          (.fvar (by decide))) (.fvar (by decide))
      | cons h3 tl3 =>
        have hlen' : tl3.length + 1 + 1 + 1 = 1 ∨ tl3.length + 1 + 1 + 1 = 2 := hlen
        omega

end IxVM.Refinement.RoleOps
