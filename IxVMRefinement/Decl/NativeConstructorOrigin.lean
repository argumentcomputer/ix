
/-- The exact computed constructor telescope before the final annotation pass. All fields
are the normalizer's real strip, opening, and domain-normalization calls. -/
def ConstructorRebuildRun {md : Mode} (env : Env md) (fuel : Nat) (T : Key md)
    (nP nF : Nat) (initial rebuilt : Expr md) : Prop :=
  ∃ parameters closedResidual parameterVars openedResidual fields residual,
    initial.stripPis nP = some (parameters, closedResidual) ∧
    openPisAtFvars nP initial 0 = some (parameterVars, openedResidual) ∧
    normFieldDoms (fueledOps .verified fuel) env T nP nF openedResidual = .ok (fields, residual) ∧
    rebuilt = closeTelescope
      (List.zipWith (fun (x : Expr md) (b : Expr md × BinderMeta) => (x.fvarTypeD, b.2))
        parameterVars parameters ++ fields) 0 residual

/-- The recorded computation determines one rebuilt expression. -/
theorem ConstructorRebuildRun.unique {md : Mode} {env : Env md} {fuel nP nF : Nat} {T : Key md}
    {initial left right : Expr md}
    (leftRun : ConstructorRebuildRun env fuel T nP nF initial left)
    (rightRun : ConstructorRebuildRun env fuel T nP nF initial right) : left = right := by
  obtain ⟨lp, lc, lvars, lo, lf, lr, ls, lopen, lnorm, leftEq⟩ := leftRun
  obtain ⟨rp, rc, rvars, ro, rf, rr, rs, ropen, rnorm, rightEq⟩ := rightRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (ls.symm.trans rs))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (lopen.symm.trans ropen))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (lnorm.symm.trans rnorm))
  exact leftEq.trans rightEq.symm

/-- Actual normalization supplies its single computed telescope and the exact final branch. -/
theorem normCtorVal_rebuild_trace {md : Mode} {env : Env md} {fuel nP nF : Nat} {T : Key md}
    {raw initial checked : ConstantVal md}
    (run : normCtorVal (fueledOps .verified fuel) env T nP nF raw initial = .ok checked) :
    ∃ rebuilt, ConstructorRebuildRun env fuel T nP nF initial.type rebuilt ∧
      (checked = initial ∨
        checkConstantVal (fueledOps .verified fuel) env { raw with type := rebuilt } = .ok checked) := by
  unfold normCtorVal at run
  obtain ⟨⟨parameters, closedResidual⟩, stripped, run⟩ := exceptBind_ok run
  obtain ⟨⟨parameterVars, openedResidual⟩, opened, run⟩ := exceptBind_ok run
  obtain ⟨⟨fields, residual⟩, normalized, run⟩ := exceptBind_ok run
  refine ⟨_, ⟨parameters, closedResidual, parameterVars, openedResidual, fields, residual,
    unwrapOr_ok stripped, unwrapOr_ok opened, normalized, rfl⟩, ?_⟩
  dsimp only at run
  split at run
  · exact .inl (Except.ok.inj run).symm
  · exact .inr run

end IxVM.Refinement.Decl
