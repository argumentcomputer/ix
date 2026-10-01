module

public import ConLeche.Verify.BridgeWfImp
public import ConLeche.Verify.ExceptBind

public section

/-!
# The direct simple-structure install: environment well-formedness

`EnvWF` for the environments `checkStruct` walks through — one
per installed constant — at the pure fueled run.  The consumer is the
cached driver's run bridge (`ConLeche/Verify/Cached/BridgeCSDecl.lean`,
`checkStructS_run`), which threads the well-formedness of every
intermediate environment through the per-stage simulations.

Every fact is read off the stage's own guards: each install stores an
annotated constant whose type (and, for the recursor, whose rule's
right-hand side; for a projection entry, whose stored type) was
checked closed, level-defined, resolving and bound *by the stage
itself*, so the inversions here are shape walks (`exceptBind_ok` /
`split`) that keep exactly those guards.
-/

namespace ConLeche

variable {mode : CheckMode}

/-- A thrown step never succeeds. -/
private theorem structThrow_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (throw e : CheckM α) = .ok a) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The shape walk's closers: every non-surviving goal holds a
`throw … = .ok _` (possibly under a join point's zeta step). -/
local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact structThrow_ne_ok (by assumption))
        | (exfalso; exact structThrow_ne_ok
            (by simpa [bind, Except.bind] using ‹_›)))

/-- A successful `unwrapOr` names its option. -/
theorem unwrapOr_ok {α : Type} {x : Option α} {e : CheckError} {a : α}
    (h : (unwrapOr x e : CheckM α) = .ok a) : x = some a := by
  cases x with
  | none => exact absurd h (by simp [unwrapOr, throw, throwThe, MonadExceptOf.throw])
  | some b =>
    simp only [unwrapOr, pure, Except.pure, Except.ok.injEq] at h
    rw [h]

/-- Introduction for `ConstWF` with the clause types spelled out (the
`thmInfo` clause defaulted, as every constant installed by the direct
path is an inductive-kind one). -/
theorem structConstWF {env : Env} {c : ConstantInfo}
    (h1 : c.toConstantVal.type.hasFvar = false)
    (h2 : c.toConstantVal.type.allLevelParamsDefined
      c.toConstantVal.levelParams = true)
    (h3 : c.toConstantVal.type.constsResolve env = true)
    (h4 : c.toConstantVal.type.looseBVarsBounded 0 = true)
    (h5 : ∀ cv value hint, c = .defnInfo cv value hint →
      value.hasFvar = false ∧
      value.allLevelParamsDefined cv.levelParams = true ∧
      value.constsResolve env = true ∧
      value.looseBVarsBounded 0 = true)
    (h6 : ∀ cv mI rP rules, c = .recInfo cv mI rP rules →
      ∀ r, r ∈ rules →
        (RecRule.rhs r).hasFvar = false ∧
        (RecRule.rhs r).allLevelParamsDefined cv.levelParams = true ∧
        (RecRule.rhs r).constsResolve env = true ∧
        (RecRule.rhs r).looseBVarsBounded 0 = true ∧
        ∀ lvls pins, RecRule.fire r = .nested lvls pins →
          rP ≤ mI ∧
          (∀ l ∈ lvls, l.allParamsDefined cv.levelParams = true) ∧
          (∀ pin ∈ pins, pin.hasFvar = false ∧
            pin.allLevelParamsDefined cv.levelParams = true ∧
            pin.constsResolve env = true ∧
            pin.looseBVarsBounded rP = true) ∧
          ∃ pre dom body bm D,
            cv.type.stripPis mI = some (pre, .forallE dom body bm) ∧
            dom.getAppFn = .const D lvls ∧
            dom.getAppArgs =
              pins.map (Expr.liftLooseBVars (mI - rP) 0) ++
                (List.range (mI - rP)).map
                  (fun i => Expr.bvar (mI - rP - 1 - i)))
    (h8 : ∀ tbl, c = .projInfo tbl →
      tbl.bodies.size = tbl.numFields ∧
      ∀ (i : Nat) (b : Expr), tbl.bodies[i]? = some b →
        b.hasFvar = false ∧
        b.allLevelParamsDefined tbl.levelParams = true ∧
        b.constsResolve env = true ∧
        b.looseBVarsBounded (tbl.numParams + 1) = true := by
        intro tbl h
        exact ConstantInfo.noConfusion h)
    (h9 : IndCapsWF c := by
        intro cv caps h
        exact ConstantInfo.noConfusion h) :
    ConstWF env c := ⟨h1, h2, h3, h4, h5, h6, h8, h9⟩

/-- A checked inductive-kind cons is well-formed (its `ConstWF` is the
four type-slot facts; every value clause is refuted by the kind). -/
theorem envWF_cons_ind {env : Env} (henv : EnvWF env)
    {cvA : ConstantVal} {caps : IndCaps} {F : Nat} {cv : ConstantVal}
    (hccv : checkConstantVal (fueledOps mode F) env cv = .ok cvA)
    (hcaps : IndCapsWF (.indInfo cvA caps)) :
    EnvWF ⟨.indInfo cvA caps :: env.consts⟩ := by
  obtain ⟨htf, htp, htr, htb⟩ := checkConstantVal_typeWF hccv
  exact EnvWF.cons henv (structConstWF htf htp
    (Expr.constsResolve_mono htr) htb
    (fun _ _ _ heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq)
    (by intro tbl h; exact ConstantInfo.noConfusion h)
    hcaps)

/-! ## Stage 5: the projection table (task #175 S1) -/

/-- The table stage's run, inverted: the bodies are the generator's,
they pass the scoping guard, the table name is fresh, and the output
is the table consed. -/
theorem checkStructProjTable_inv {env envOut : Env} {T C : Name}
    {lps : List Name} {nP nF : Nat} {rs : Level} {guards : List Level}
    {cvCa : ConstantVal}
    (h : checkStructProjTable (m := CheckM) T C lps nP nF rs guards off cvCa env
      = .ok envOut) :
    ∃ bodies : Array Expr,
      structProjBodies T nP nF cvCa.type = some bodies ∧
      (bodies.size = nF ∧ bodies.all (fun b => !b.hasFvar &&
        b.allLevelParamsDefined lps && b.constsResolve env &&
        b.looseBVarsBounded (nP + 1)) = true) ∧
      (List.range nF).all (fun j => (env.find? (projFnName T j)).isNone) = true ∧
      env.find? (projTableName T) = none ∧
      envOut = ⟨.projInfo ⟨T, lps, nP, C, nF, rs, bodies, guards, off⟩
        :: env.consts⟩ := by
  unfold checkStructProjTable at h
  obtain ⟨bodies, hb, h⟩ := exceptBind_ok h
  have hb' := unwrapOr_ok hb
  repeat' first
    | (obtain ⟨_, _, h⟩ := exceptBind_ok h)
    | split at h
  all_goals first
    | (try dsimp only at h
       simp only [pure, Except.pure, Except.ok.injEq] at h
       refine ⟨bodies, hb', by assumption, by assumption,
         Option.isNone_iff_eq_none.mp (by assumption), h.symm⟩)
    | close_throw

/-- The projection-table stage at the run level (task #175 S1): the
environment it produces is well-formed — the table's constant type is
the closed `Sort 1`, and the bodies' scoping is the stage's own guard. -/
theorem direct_table_wf {env envOut : Env} (henv : EnvWF env)
    {T C : Name} {lps : List Name} {nP nF : Nat} {rs : Level}
    {guards : List Level} {off : Nat} {cvCa : ConstantVal}
    (h : checkStructProjTable (m := CheckM) T C lps nP nF rs guards off cvCa env
      = .ok envOut) :
    EnvWF envOut := by
  obtain ⟨bodies, -, ⟨hsize, hall⟩, -, -, rfl⟩ := checkStructProjTable_inv h
  refine EnvWF.cons henv (structConstWF rfl rfl rfl rfl
    (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq) ?_)
  intro tbl heq
  obtain rfl := ConstantInfo.projInfo.inj heq
  refine ⟨hsize, fun i b hb => ?_⟩
  have hmem : b ∈ bodies := Array.mem_of_getElem? hb
  have hb' := (Array.all_eq_true_iff_forall_mem.mp hall) b hmem
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hb'
  exact ⟨hb'.1.1.1, hb'.1.1.2, Expr.constsResolve_mono hb'.1.2, hb'.2⟩

end ConLeche
