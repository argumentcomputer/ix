import Ix.Compiler.IxIR0.ProjectionSafe

/-!
# Projection-free completeness for call-aware traces

`ProjectionSafe.Eval` intentionally rejects the erased evaluator's absorbing
`proj erased` case. This module supplies the complementary structural route:
when every reachable expression is syntactically projection-free, every
successful ordinary evaluation admits a call-aware trace. Closure bodies and
recursor rules are covered through an explicit value/context invariant, so the
result includes dynamically entered calls rather than only the surface term.
-/

namespace Ix.Compiler.IxIR0.ProjectionFree

/-- Executable syntax check used by the structural completeness theorem. -/
def syntaxSafe : IxIR0.Expr → Bool
  | .var _ | .ref _ | .lit _ | .erased => true
  | .app function argument => syntaxSafe function && syntaxSafe argument
  | .lam _ body => syntaxSafe body
  | .letE _ value body => syntaxSafe value && syntaxSafe body
  | .proj _ _ => false

/-- A source expression contains no projection node. -/
abbrev ExprSafe (expr : IxIR0.Expr) : Prop := syntaxSafe expr = true

/-- Every executable body stored by a declaration is projection-free. -/
def declSafe : IxIR0.Decl → Bool
  | .defn _ body => syntaxSafe body
  | .ctor _ _ | .extern _ => true
  | .recursor _ _ rules => rules.all fun rule => syntaxSafe rule.rhs

/-- Runtime values retain the projection-free invariant on captured closure
environments and bodies. Constructor and PAP arguments are checked
recursively. -/
inductive ValueSafe : IxIR0.Value → Prop where
  | clos {uses env body} :
      (∀ value ∈ env, ValueSafe value) →
      ExprSafe body →
      ValueSafe (.clos uses env body)
  | pap {head args} :
      (∀ value ∈ args, ValueSafe value) →
      ValueSafe (.pap head args)
  | ctor {address tag args} :
      (∀ value ∈ args, ValueSafe value) →
      ValueSafe (.ctor address tag args)
  | lit {literal} : ValueSafe (.lit literal)
  | erased : ValueSafe .erased

/-- Pointwise projection-freedom for a runtime environment or argument list. -/
def ValuesSafe (values : List IxIR0.Value) : Prop :=
  ∀ value ∈ values, ValueSafe value

namespace ValuesSafe

theorem nil : ValuesSafe [] := by simp [ValuesSafe]

theorem cons {value : IxIR0.Value} {values : List IxIR0.Value}
    (hvalue : ValueSafe value) (hvalues : ValuesSafe values) :
    ValuesSafe (value :: values) := by
  intro candidate hmem
  simp only [List.mem_cons] at hmem
  rcases hmem with rfl | hmem
  · exact hvalue
  · exact hvalues candidate hmem

theorem append {left right : List IxIR0.Value}
    (hleft : ValuesSafe left) (hright : ValuesSafe right) :
    ValuesSafe (left ++ right) := by
  intro value hmem
  rw [List.mem_append] at hmem
  exact hmem.elim (hleft value) (hright value)

theorem reverse {values : List IxIR0.Value} (hvalues : ValuesSafe values) :
    ValuesSafe values.reverse := by
  intro value hmem
  exact hvalues value (List.mem_reverse.mp hmem)

theorem drop {values : List IxIR0.Value} (hvalues : ValuesSafe values)
    (count : Nat) : ValuesSafe (values.drop count) := by
  intro value hmem
  exact hvalues value (List.mem_of_mem_drop hmem)

theorem dropLast {values : List IxIR0.Value}
    (hvalues : ValuesSafe values) : ValuesSafe values.dropLast := by
  intro value hmem
  exact hvalues value (List.dropLast_subset values hmem)

theorem getLast? {values : List IxIR0.Value} {value : IxIR0.Value}
    (hvalues : ValuesSafe values) (hlast : values.getLast? = some value) :
    ValueSafe value := by
  obtain ⟨initial, heq⟩ := List.getLast?_eq_some_iff.mp hlast
  apply hvalues value
  rw [heq]
  simp

end ValuesSafe

namespace ValueSafe

/-- Constructor fields exposed by `majorCtor` inherit the runtime value
invariant. Nat-literal peeling creates only another safe literal. -/
theorem majorCtor {natLit : Bool} {major : IxIR0.Value} {tag : Nat}
    {fields : List IxIR0.Value} (hvalue : ValueSafe major)
    (hrun : IxIR0.majorCtor natLit major = .ok (tag, fields)) :
    ValuesSafe fields := by
  cases hvalue with
  | clos _ _ => simp [IxIR0.majorCtor] at hrun
  | pap _ => simp [IxIR0.majorCtor] at hrun
  | ctor hargs =>
      simp only [IxIR0.majorCtor] at hrun
      cases Except.ok.inj hrun
      exact hargs
  | lit =>
      rename_i literal
      cases literal with
      | str string => simp [IxIR0.majorCtor] at hrun
      | nat number =>
          cases number with
          | zero =>
              cases natLit with
              | false => simp [IxIR0.majorCtor] at hrun
              | true =>
                  simp [IxIR0.majorCtor] at hrun
                  rcases hrun with ⟨rfl, rfl⟩
                  exact ValuesSafe.nil
          | succ number =>
              cases natLit with
              | false => simp [IxIR0.majorCtor] at hrun
              | true =>
                  simp [IxIR0.majorCtor] at hrun
                  rcases hrun with ⟨rfl, rfl⟩
                  exact ValuesSafe.cons .lit ValuesSafe.nil
  | erased => simp [IxIR0.majorCtor] at hrun

end ValueSafe

/-- Projection-free declarations and safe oracle results form the closed-world
invariant needed to follow references, recursor rules, and extern calls. -/
structure CtxSafe (ctx : IxIR0.Ctx) : Prop where
  env : ∀ address declaration,
    ctx.env address = some declaration → declSafe declaration = true
  oracle : ∀ address args result,
    ValuesSafe args →
    ctx.oracle address args = some result →
    ValueSafe result

private def CompleteAt (ctx : IxIR0.Ctx) (fuel : Nat) : Prop :=
  (∀ env expr result,
    ValuesSafe env → ExprSafe expr →
    IxIR0.eval ctx fuel env expr = .ok result →
    IxIR0.ProjectionSafe.Eval ctx fuel env expr result ∧ ValueSafe result) ∧
  (∀ function argument result,
    ValueSafe function → ValueSafe argument →
    IxIR0.apply ctx fuel function argument = .ok result →
    IxIR0.ProjectionSafe.Apply ctx fuel function argument result ∧
      ValueSafe result) ∧
  (∀ head args result,
    ValuesSafe args →
    IxIR0.saturate ctx fuel head args = .ok result →
    IxIR0.ProjectionSafe.Saturate ctx fuel head args result ∧
      ValueSafe result) ∧
  (∀ head args result,
    ValuesSafe args →
    IxIR0.fire ctx fuel head args = .ok result →
    IxIR0.ProjectionSafe.Fire ctx fuel head args result ∧ ValueSafe result)

private theorem bindOk {error alpha beta : Type} (value : alpha)
    (next : alpha → Except error beta) :
    (Except.ok value >>= next) = next value := rfl

private theorem completeAt {ctx : IxIR0.Ctx} (hctx : CtxSafe ctx) :
    ∀ fuel, CompleteAt ctx fuel := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro env expr result henv hexpr hrun
        simp [IxIR0.eval.eq_def] at hrun
      · intro function argument result hfunction hargument hrun
        simp [IxIR0.apply.eq_def] at hrun
      · intro head args result hargs hrun
        simp [IxIR0.saturate.eq_def] at hrun
      · intro head args result hargs hrun
        simp [IxIR0.fire.eq_def] at hrun
  | succ fuel ih =>
      obtain ⟨ihEval, ihApply, ihSaturate, ihFire⟩ := ih
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro env expr result henv hexpr hrun
        cases expr with
        | var index =>
            rw [IxIR0.eval.eq_def] at hrun
            dsimp only at hrun
            cases hlookup : env[index]? with
            | none => rw [hlookup] at hrun; contradiction
            | some value =>
                rw [hlookup] at hrun
                injection hrun with hresult
                subst result
                obtain ⟨hindex, hget⟩ :=
                  List.getElem?_eq_some_iff.mp hlookup
                exact ⟨.var hlookup,
                  henv value (List.mem_iff_getElem.mpr
                    ⟨index, hindex, hget⟩)⟩
        | lit literal =>
            rw [IxIR0.eval.eq_def] at hrun
            injection hrun with hresult
            subst result
            exact ⟨.lit, .lit⟩
        | erased =>
            rw [IxIR0.eval.eq_def] at hrun
            injection hrun with hresult
            subst result
            exact ⟨.erased, .erased⟩
        | lam uses body =>
            rw [IxIR0.eval.eq_def] at hrun
            injection hrun with hresult
            subst result
            exact ⟨.lam, .clos henv hexpr⟩
        | letE uses value body =>
            have hparts := Bool.and_eq_true_iff.mp hexpr
            rw [IxIR0.eval.eq_def] at hrun
            dsimp only at hrun
            cases hvalueRun : IxIR0.eval ctx fuel env value with
            | error error => rw [hvalueRun] at hrun; contradiction
            | ok bound =>
                rw [hvalueRun] at hrun
                obtain ⟨hvalueTrace, hbound⟩ :=
                  ihEval env value bound henv hparts.1 hvalueRun
                obtain ⟨hbodyTrace, hresult⟩ :=
                  ihEval (bound :: env) body result
                    (ValuesSafe.cons hbound henv) hparts.2 hrun
                exact ⟨.letE hvalueTrace hbodyTrace, hresult⟩
        | app function argument =>
            have hparts := Bool.and_eq_true_iff.mp hexpr
            rw [IxIR0.eval.eq_def] at hrun
            dsimp only at hrun
            cases hfunctionRun : IxIR0.eval ctx fuel env function with
            | error error => rw [hfunctionRun] at hrun; contradiction
            | ok functionValue =>
                rw [hfunctionRun] at hrun
                cases hargumentRun : IxIR0.eval ctx fuel env argument with
                | error error => rw [hargumentRun] at hrun; contradiction
                | ok argumentValue =>
                    rw [hargumentRun] at hrun
                    obtain ⟨hfunctionTrace, hfunction⟩ :=
                      ihEval env function functionValue henv hparts.1
                        hfunctionRun
                    obtain ⟨hargumentTrace, hargument⟩ :=
                      ihEval env argument argumentValue henv hparts.2
                        hargumentRun
                    obtain ⟨happlyTrace, hresult⟩ :=
                      ihApply functionValue argumentValue result hfunction
                        hargument hrun
                    exact ⟨.app hfunctionTrace hargumentTrace happlyTrace,
                      hresult⟩
        | proj index source => cases hexpr
        | ref address =>
            rw [IxIR0.eval.eq_def] at hrun
            dsimp only at hrun
            cases hlookup : ctx.env address with
            | none => rw [hlookup] at hrun; contradiction
            | some declaration =>
                rw [hlookup] at hrun
                have hdeclaration := hctx.env address declaration hlookup
                cases declaration with
                | defn world body =>
                    obtain ⟨hbodyTrace, hresult⟩ :=
                      ihEval [] body result ValuesSafe.nil hdeclaration hrun
                    exact ⟨.refDefn hlookup hbodyTrace, hresult⟩
                | ctor tag arity =>
                    obtain ⟨hsaturateTrace, hresult⟩ :=
                      ihSaturate (.ctor address tag arity) [] result
                        ValuesSafe.nil hrun
                    exact ⟨.refCtor hlookup hsaturateTrace, hresult⟩
                | recursor numArgs natLit rules =>
                    injection hrun with hresult
                    subst result
                    exact ⟨.refRecursor hlookup, .pap ValuesSafe.nil⟩
                | extern arity =>
                    obtain ⟨hsaturateTrace, hresult⟩ :=
                      ihSaturate (.ext address arity) [] result
                        ValuesSafe.nil hrun
                    exact ⟨.refExtern hlookup hsaturateTrace, hresult⟩
      · intro function argument result hfunction hargument hrun
        cases hfunction with
        | clos henv hbody =>
            rw [IxIR0.apply.eq_def] at hrun
            obtain ⟨hbodyTrace, hresult⟩ :=
              ihEval _ _ _ (ValuesSafe.cons hargument henv) hbody hrun
            exact ⟨.clos hbodyTrace, hresult⟩
        | pap hargs =>
            rw [IxIR0.apply.eq_def] at hrun
            obtain ⟨hsaturateTrace, hresult⟩ :=
              ihSaturate _ _ _
                (ValuesSafe.append hargs
                  (ValuesSafe.cons hargument ValuesSafe.nil)) hrun
            exact ⟨.pap hsaturateTrace, hresult⟩
        | ctor hargs =>
            rw [IxIR0.apply.eq_def] at hrun
            contradiction
        | lit =>
            rw [IxIR0.apply.eq_def] at hrun
            contradiction
        | erased =>
            rw [IxIR0.apply.eq_def] at hrun
            injection hrun with hresult
            subst result
            exact ⟨.erased, .erased⟩
      · intro head args result hargs hrun
        rw [IxIR0.saturate.eq_def] at hrun
        dsimp only at hrun
        by_cases hlength : args.length = head.arity
        · simp only [beq_iff_eq.mpr hlength, if_true] at hrun
          obtain ⟨hfireTrace, hresult⟩ := ihFire head args result hargs hrun
          exact ⟨.full hlength hfireTrace, hresult⟩
        · have hbeq : (args.length == head.arity) = false := by
            exact Bool.eq_false_iff.mpr fun htrue =>
              hlength (beq_iff_eq.mp htrue)
          simp only [hbeq, Bool.false_eq_true, if_false] at hrun
          injection hrun with hresult
          subst result
          exact ⟨.pending hlength, .pap hargs⟩
      · intro head args result hargs hrun
        cases head with
        | ctor address tag arity =>
            rw [IxIR0.fire.eq_def] at hrun
            injection hrun with hresult
            subst result
            exact ⟨.ctor, .ctor hargs⟩
        | ext address arity =>
            rw [IxIR0.fire.eq_def] at hrun
            dsimp only at hrun
            cases horacle : ctx.oracle address args with
            | none => rw [horacle] at hrun; contradiction
            | some value =>
                rw [horacle] at hrun
                injection hrun with hresult
                subst result
                exact ⟨.extern horacle,
                  hctx.oracle address args value hargs horacle⟩
        | rec_ address arity =>
            rw [IxIR0.fire.eq_def] at hrun
            dsimp only at hrun
            cases hlookup : ctx.env address with
            | none => rw [hlookup] at hrun; contradiction
            | some declaration =>
                rw [hlookup] at hrun
                have hdeclaration := hctx.env address declaration hlookup
                cases declaration with
                | defn world body => contradiction
                | ctor tag ctorArity => contradiction
                | extern externArity => contradiction
                | recursor numArgs natLit rules =>
                    dsimp only at hrun
                    cases hlast : args.getLast? with
                    | none => rw [hlast] at hrun; contradiction
                    | some major =>
                        rw [hlast] at hrun
                        dsimp only at hrun
                        cases hmajor : IxIR0.majorCtor natLit major with
                        | error error =>
                            rw [hmajor] at hrun
                            contradiction
                        | ok pair =>
                            rcases pair with ⟨tag, fields⟩
                            rw [hmajor, bindOk] at hrun
                            dsimp only at hrun
                            cases hrule : rules[tag]? with
                            | none => rw [hrule] at hrun; contradiction
                            | some rule =>
                                rw [hrule] at hrun
                                dsimp only at hrun
                                by_cases hfields : fields.length = rule.fields
                                · have hfieldBeq :
                                      (fields.length != rule.fields) = false := by
                                    simp [hfields]
                                  rw [hfieldBeq] at hrun
                                  obtain ⟨hruleIndex, hruleGet⟩ :=
                                    Array.getElem?_eq_some_iff.mp hrule
                                  have hruleSafe :=
                                    (Array.all_eq_true.mp hdeclaration)
                                      tag hruleIndex
                                  rw [hruleGet] at hruleSafe
                                  have hmajorSafe :=
                                    ValuesSafe.getLast? hargs hlast
                                  have hfieldsSafe :=
                                    hmajorSafe.majorCtor hmajor
                                  have hbodyEnv : ValuesSafe
                                      (fields.reverse ++
                                        args.dropLast.reverse ++
                                        [.pap (.rec_ address arity) []]) :=
                                    by
                                      simpa only [List.append_assoc] using
                                        ValuesSafe.append hfieldsSafe.reverse
                                          (ValuesSafe.append
                                            hargs.dropLast.reverse
                                            (ValuesSafe.cons
                                              (.pap ValuesSafe.nil)
                                              ValuesSafe.nil))
                                  obtain ⟨hbodyTrace, hresult⟩ :=
                                    ihEval _ rule.rhs result hbodyEnv
                                      hruleSafe hrun
                                  exact ⟨.recursor hlookup hlast hmajor hrule
                                    hfields hbodyTrace, hresult⟩
                                · have hfieldBne :
                                      (fields.length != rule.fields) = true := by
                                    simp [hfields]
                                  rw [hfieldBne] at hrun
                                  contradiction

/-- Every successful evaluation of a projection-free closed-world state has
an exact call-aware trace at the same fuel. -/
theorem Eval.of_run {ctx : IxIR0.Ctx} (hctx : CtxSafe ctx)
    {fuel : Nat} {env : List IxIR0.Value} {expr : IxIR0.Expr}
    {result : IxIR0.Value} (henv : ValuesSafe env) (hexpr : ExprSafe expr)
    (hrun : IxIR0.eval ctx fuel env expr = .ok result) :
    IxIR0.ProjectionSafe.Eval ctx fuel env expr result :=
  (completeAt hctx fuel).1 env expr result henv hexpr hrun |>.1

/-- The completeness construction also records that its result preserves the
runtime projection-free invariant. -/
theorem Eval.resultSafe {ctx : IxIR0.Ctx} (hctx : CtxSafe ctx)
    {fuel : Nat} {env : List IxIR0.Value} {expr : IxIR0.Expr}
    {result : IxIR0.Value} (henv : ValuesSafe env) (hexpr : ExprSafe expr)
    (hrun : IxIR0.eval ctx fuel env expr = .ok result) : ValueSafe result :=
  (completeAt hctx fuel).1 env expr result henv hexpr hrun |>.2

end Ix.Compiler.IxIR0.ProjectionFree
