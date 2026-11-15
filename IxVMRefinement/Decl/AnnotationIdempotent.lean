import IxC.Kernel.Verify.Leaves
import IxC.Kernel.Verify.InferLeaves
import IxC.Kernel.Verify.Mono
import IxC.Kernel.Verify.ExceptBind

/-! # Re-annotating an actual annotation result

The annotation pass is a fixed point on its scoped, bounded outputs. Written binder metadata
is retained; a datum computed as `never` is recomputed from the same already annotated body.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel

private theorem choice_bind {md : Mode} {α β : Type} {condition : Prop} [Decidable condition]
    (left right : CheckM md α) (continuation : α → CheckM md β) :
    (if condition then left >>= continuation else right >>= continuation) =
      ((if condition then left else right) >>= continuation) := by
  by_cases h : condition <;> simp only [h, ↓reduceIte]

private theorem choosePw_idempotent {md : Mode} {old written : PropWhen} {compute : CheckM md PropWhen}
    (checked : (if !pwWritten old then compute else pure old) = .ok written) :
    (if !pwWritten written then compute else pure written) = .ok written := by
  by_cases before : pwWritten old = true
  · have same : old = written := by
      simpa only [before, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Pure.pure, Except.pure, Except.ok.injEq] using checked
    subst written
    exact checked
  · have computed : compute = .ok written := by simpa [before] using checked
    by_cases after : pwWritten written = true
    · simp only [after, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rfl
    · simpa [after] using computed

private theorem annotation_reclose {md : Mode} {mode : CheckMode} {env : Env md}
    {fuel d : Nat} {ty body out : Expr md}
    (tyScope : Expr.WScoped d ty) (bodyScope : Expr.WScoped d body)
    (bodyBounded : body.looseBVarsBounded 1 = true)
    (run : annotateCore mode env fuel (d + 1) (body.instantiate1 (.fvar d ty)) = .ok out) :
    (out.abstract1 d).instantiate1 (.fvar d ty) = out := by
  have hw := tyScope.instantiate1 0 bodyScope
  have hb : (body.instantiate1 (.fvar d ty)).looseBVarsBounded 0 = true :=
    looseBVarsBounded_instantiate1 _ 0 bodyBounded
  have bounded := annotateCore_looseBVars fuel _ run hb
  have leaves := annotateCore_leaves_sub fuel _ run hw hb
  apply abstract1_instantiate1 out 0 ?_ bounded
  apply Expr.fvarConsistent_of_leafCond
  intro leaf present sameIndex
  rcases Expr.fvarLeaves_instantiate1 body 0 (leaves leaf present) with inBody | inVar
  · have lt := Expr.fvarLeaves_lt_of_wscoped bodyScope leaf inBody
    omega
  · simp only [Expr.fvarLeaves, List.mem_cons] at inVar
    rcases inVar with rfl | inTy
    · rfl
    · have lt := Expr.fvarLeaves_lt_of_wscoped tyScope leaf inTy
      omega

/-- A successful annotation is idempotent at the same fuel on scoped, bounded input. -/
theorem annotateCore_idempotent {md : Mode} {mode : CheckMode} {env : Env md}
    {fuel d : Nat} {e out : Expr md}
    (run : annotateCore mode env fuel d e = .ok out)
    (scope : Expr.WScoped d e) (bounded : e.looseBVarsBounded 0 = true) :
    annotateCore mode env fuel d out = .ok out := by
  induction fuel generalizing d e out with
  | zero => cases run
  | succ fuel ih =>
    cases e with
    | bvar i =>
      have original := run
      rw [annotateCore_succ] at run
      simp only [annotateBody, Pure.pure, Except.pure, Except.ok.injEq] at run
      subst out
      exact original
    | sort level =>
      have original := run
      rw [annotateCore_succ] at run
      simp only [annotateBody, Pure.pure, Except.pure, Except.ok.injEq] at run
      subst out
      exact original
    | const name levels =>
      have original := run
      rw [annotateCore_succ] at run
      simp only [annotateBody, Pure.pure, Except.pure, Except.ok.injEq] at run
      subst out
      exact original
    | fvar idx ty =>
      have original := run
      rw [annotateCore_succ] at run
      simp only [annotateBody] at run
      split at run
      · have same := Except.ok.inj run
        subst out
        exact original
      · cases run
    | lit literal =>
      have original := run
      rw [annotateCore_succ] at run
      cases literal <;> simp only [annotateBody] at run
      all_goals
        split at run
        · have same := Except.ok.inj run
          subst out
          exact original
        · cases run
    | app f a =>
      obtain ⟨f', a', hf, ha, rfl⟩ := annotateCore_app_inv run
      simp only [Expr.WScoped] at scope
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at bounded
      have hf' := ih hf scope.1 bounded.1
      have ha' := ih ha scope.2 bounded.2
      simp only [annotateCore_succ, annotateBody, annotate_def, hf', ha',
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    | forallE ty body bm =>
      simp only [Expr.WScoped] at scope
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at bounded
      rw [annotateCore_succ] at run
      simp only [annotateBody, annotate_def] at run
      obtain ⟨ty', hty, rest⟩ := exceptBind_ok run
      obtain ⟨body', hbody, rest⟩ := exceptBind_ok rest
      rw [choice_bind] at rest
      obtain ⟨pw, hpw, result⟩ := exceptBind_ok rest
      have same := Except.ok.inj result
      subst out
      have htyScope := annotateCore_WScoped fuel ty hty scope.1
      have hty' := ih hty scope.1 bounded.1
      have hbody' := ih hbody (htyScope.instantiate1 0 scope.2)
        (looseBVarsBounded_instantiate1 _ 0 bounded.2)
      have round := annotation_reclose htyScope scope.2 bounded.2 hbody
      rw [annotateCore_succ]
      simp only [annotateBody, annotate_def, hty', round, hbody', Bind.bind, Except.bind]
      have next := congrArg (fun action : CheckM md PropWhen =>
        action >>= fun newPw => (pure (Expr.forallE ty' (body'.abstract1 d) { bm with pw := newPw }) :
          CheckM md (Expr md))) (choosePw_idempotent hpw)
      simpa only [← choice_bind, Bind.bind, Except.bind, Pure.pure, Except.pure] using next
    | lam ty body bm =>
      simp only [Expr.WScoped] at scope
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at bounded
      rw [annotateCore_succ] at run
      simp only [annotateBody, annotate_def] at run
      obtain ⟨ty', hty, rest⟩ := exceptBind_ok run
      obtain ⟨body', hbody, rest⟩ := exceptBind_ok rest
      rw [choice_bind] at rest
      obtain ⟨pw, hpw, result⟩ := exceptBind_ok rest
      have same := Except.ok.inj result
      subst out
      have htyScope := annotateCore_WScoped fuel ty hty scope.1
      have hty' := ih hty scope.1 bounded.1
      have hbody' := ih hbody (htyScope.instantiate1 0 scope.2)
        (looseBVarsBounded_instantiate1 _ 0 bounded.2)
      have round := annotation_reclose htyScope scope.2 bounded.2 hbody
      rw [annotateCore_succ]
      simp only [annotateBody, annotate_def, hty', round, hbody', Bind.bind, Except.bind]
      have next := congrArg (fun action : CheckM md PropWhen =>
        action >>= fun newPw => (pure (Expr.lam ty' (body'.abstract1 d) { bm with pw := newPw }) :
          CheckM md (Expr md))) (choosePw_idempotent hpw)
      simpa only [← choice_bind, Bind.bind, Except.bind, Pure.pure, Except.pure] using next
    | letE ty value body lmeta =>
      obtain ⟨_, _, _, _, hbody, _⟩ := annotateCore_letE_inv run
      simp only [Expr.WScoped] at scope
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at bounded
      have fixed := ih hbody (Expr.WScoped.instantiate1_gen scope.2.1 0 scope.2.2)
        (looseBVarsBounded_instantiate1_gen bounded.1.2 bounded.2)
      exact annotateCore_mono (Nat.le_succ fuel) fixed
    | proj T i e =>
      obtain ⟨e', tt, te, he, ht, hw, sn, us, entry, hhead, hentry, hparams, rfl⟩ :=
        annotateCore_proj_inv run
      simp only [Expr.WScoped] at scope
      simp only [Expr.looseBVarsBounded] at bounded
      have he' := ih he scope bounded
      simp only [annotateCore_succ, annotateBody, annotate_def, inferTypeIO_def, whnf_def,
        he', ht, hw, hhead, hentry, hparams, Bind.bind, Except.bind, Pure.pure, Except.pure,
        ↓reduceIte]

end IxVM.Refinement.Decl
