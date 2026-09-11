import Ix.Compiler.IxIR0.ProjectionSafe

/-!
# Dynamic IxIR₀ execution profiles

Evaluator fuel is a totality index, not a cost.  This module instead records
the semantic events that actually occur along a successful execution.  The
profile is additive across expression subcomputations, application spines,
closure entry, and recursor-rule entry, so recursion contributes once per
dynamically selected rule rather than once per source syntax occurrence.

The event vocabulary is intentionally source-facing.  A lowering proof may
relate it to IxIR₁ allocation and reference-count counters without asserting
that one source event is intrinsically one target instruction.
-/

namespace Ix.Compiler.IxIR0.DynamicCost

/-- Source events retained by the dynamic cost model. -/
inductive Event where
  | evalVar
  | evalLit
  | evalErased
  | evalLam
  | evalLet
  | evalApp
  | evalProj
  | evalRefDefn
  | evalRefCtor
  | evalRefRecursor
  | evalRefExtern
  | applyClosure
  | applyPap
  | applyErased
  | saturatePending
  | saturateFull
  | fireConstructor
  | fireExtern
  | fireRecursor
  deriving BEq, DecidableEq, Repr

/-- A compact additive summary of one dynamic source trace. -/
@[ext] structure Profile where
  evals : Nat := 0
  applies : Nat := 0
  saturations : Nat := 0
  constructorFires : Nat := 0
  closureValues : Nat := 0
  papValues : Nat := 0
  recursorFires : Nat := 0
  externFires : Nat := 0
  projections : Nat := 0
  /-- A conservative count of source-owned roots that lowering may have to
  retain explicitly.  Unlike the event counters, this quantity carries the
  dynamic width of closure environments, PAP prefixes, and recursor fields. -/
  retains : Nat := 0
  deriving BEq, DecidableEq, Repr

instance : Zero Profile := ⟨{}⟩

instance : Add Profile where
  add left right :=
    { evals := left.evals + right.evals
      applies := left.applies + right.applies
      saturations := left.saturations + right.saturations
      constructorFires := left.constructorFires + right.constructorFires
      closureValues := left.closureValues + right.closureValues
      papValues := left.papValues + right.papValues
      recursorFires := left.recursorFires + right.recursorFires
      externFires := left.externFires + right.externFires
      projections := left.projections + right.projections
      retains := left.retains + right.retains }

@[simp] theorem Profile.zero_evals : (0 : Profile).evals = 0 := rfl
@[simp] theorem Profile.zero_applies : (0 : Profile).applies = 0 := rfl
@[simp] theorem Profile.zero_saturations :
    (0 : Profile).saturations = 0 := rfl
@[simp] theorem Profile.zero_constructorFires :
    (0 : Profile).constructorFires = 0 := rfl
@[simp] theorem Profile.zero_closureValues :
    (0 : Profile).closureValues = 0 := rfl
@[simp] theorem Profile.zero_papValues :
    (0 : Profile).papValues = 0 := rfl
@[simp] theorem Profile.zero_recursorFires :
    (0 : Profile).recursorFires = 0 := rfl
@[simp] theorem Profile.zero_externFires :
    (0 : Profile).externFires = 0 := rfl
@[simp] theorem Profile.zero_projections :
    (0 : Profile).projections = 0 := rfl
@[simp] theorem Profile.zero_retains : (0 : Profile).retains = 0 := rfl

@[simp] theorem Profile.add_evals (left right : Profile) :
    (left + right).evals = left.evals + right.evals := rfl
@[simp] theorem Profile.add_applies (left right : Profile) :
    (left + right).applies = left.applies + right.applies := rfl
@[simp] theorem Profile.add_saturations (left right : Profile) :
    (left + right).saturations =
      left.saturations + right.saturations := rfl
@[simp] theorem Profile.add_constructorFires (left right : Profile) :
    (left + right).constructorFires =
      left.constructorFires + right.constructorFires := rfl
@[simp] theorem Profile.add_closureValues (left right : Profile) :
    (left + right).closureValues =
      left.closureValues + right.closureValues := rfl
@[simp] theorem Profile.add_papValues (left right : Profile) :
    (left + right).papValues = left.papValues + right.papValues := rfl
@[simp] theorem Profile.add_recursorFires (left right : Profile) :
    (left + right).recursorFires =
      left.recursorFires + right.recursorFires := rfl
@[simp] theorem Profile.add_externFires (left right : Profile) :
    (left + right).externFires =
      left.externFires + right.externFires := rfl
@[simp] theorem Profile.add_projections (left right : Profile) :
    (left + right).projections =
      left.projections + right.projections := rfl
@[simp] theorem Profile.add_retains (left right : Profile) :
    (left + right).retains = left.retains + right.retains := rfl

theorem Profile.zero_add (profile : Profile) : 0 + profile = profile := by
  ext <;> simp

theorem Profile.add_zero (profile : Profile) : profile + 0 = profile := by
  ext <;> simp

theorem Profile.add_assoc (left middle right : Profile) :
    left + middle + right = left + (middle + right) := by
  ext <;> simp [Nat.add_assoc]

theorem Profile.add_comm (left right : Profile) :
    left + right = right + left := by
  ext <;> simp [Nat.add_comm]

/-- The one-event contribution to a dynamic profile. -/
def tick : Event → Profile
  | .evalVar | .evalLit | .evalErased | .evalLet | .evalApp |
      .evalRefDefn | .evalRefCtor | .evalRefExtern =>
      { evals := 1 }
  | .evalLam =>
      { evals := 1, closureValues := 1 }
  | .evalProj =>
      { evals := 1, projections := 1 }
  | .evalRefRecursor =>
      { evals := 1, papValues := 1 }
  | .applyClosure | .applyPap | .applyErased =>
      { applies := 1 }
  | .saturatePending =>
      { saturations := 1, papValues := 1 }
  | .saturateFull =>
      { saturations := 1 }
  | .fireConstructor =>
      { constructorFires := 1 }
  | .fireExtern =>
      { externFires := 1 }
  | .fireRecursor =>
      { recursorFires := 1 }

/-- Dynamic-width contribution for operations that may become one target
`dup` per retained source root.  Counting candidates is conservative:
scalars and ownership moves may execute without an RC instruction. -/
def retain (count : Nat) : Profile := { retains := count }

/-! ## Costed call-aware traces -/

mutual

  /-- A projection-safe expression trace annotated with its additive dynamic
  profile. -/
  inductive Eval (ctx : Ctx) :
      Nat → List Value → Expr → Value → Profile → Prop where
    | var {fuel env index value} :
        env[index]? = some value →
        Eval ctx (fuel + 1) env (.var index) value
          (tick .evalVar + retain 1)
    | lit {fuel env literal} :
        Eval ctx (fuel + 1) env (.lit literal) (.lit literal)
          (tick .evalLit)
    | erased {fuel env} :
        Eval ctx (fuel + 1) env .erased .erased (tick .evalErased)
    | lam {fuel env uses body} :
        Eval ctx (fuel + 1) env (.lam uses body) (.clos uses env body)
          (tick .evalLam + retain env.length)
    | letE {fuel env uses value body bound result valueCost bodyCost} :
        Eval ctx fuel env value bound valueCost →
        Eval ctx fuel (bound :: env) body result bodyCost →
        Eval ctx (fuel + 1) env (.letE uses value body) result
          (valueCost + bodyCost + tick .evalLet)
    | app {fuel env function argument functionValue argumentValue result
        functionCost argumentCost applyCost} :
        Eval ctx fuel env function functionValue functionCost →
        Eval ctx fuel env argument argumentValue argumentCost →
        Apply ctx fuel functionValue argumentValue result applyCost →
        Eval ctx (fuel + 1) env (.app function argument) result
          (functionCost + argumentCost + applyCost + tick .evalApp)
    | proj {fuel env index source address tag fields result sourceCost} :
        Eval ctx fuel env source (.ctor address tag fields) sourceCost →
        fields[index]? = some result →
        Eval ctx (fuel + 1) env (.proj index source) result
          (sourceCost + tick .evalProj + retain 1)
    | refDefn {fuel env address world body result bodyCost} :
        ctx.env address = some (.defn world body) →
        Eval ctx fuel [] body result bodyCost →
        Eval ctx (fuel + 1) env (.ref address) result
          (bodyCost + tick .evalRefDefn)
    | refCtor {fuel env address tag arity result saturateCost} :
        ctx.env address = some (.ctor tag arity) →
        Saturate ctx fuel (.ctor address tag arity) [] result saturateCost →
        Eval ctx (fuel + 1) env (.ref address) result
          (saturateCost + tick .evalRefCtor)
    | refRecursor {fuel env address numArgs natLit rules} :
        ctx.env address = some (.recursor numArgs natLit rules) →
        Eval ctx (fuel + 1) env (.ref address)
          (.pap (.rec_ address (numArgs + 1)) []) (tick .evalRefRecursor)
    | refExtern {fuel env address arity result saturateCost} :
        ctx.env address = some (.extern arity) →
        Saturate ctx fuel (.ext address arity) [] result saturateCost →
        Eval ctx (fuel + 1) env (.ref address) result
          (saturateCost + tick .evalRefExtern)

  /-- One dynamically entered source application. -/
  inductive Apply (ctx : Ctx) :
      Nat → Value → Value → Value → Profile → Prop where
    | clos {fuel uses env body argument result bodyCost} :
        Eval ctx fuel (argument :: env) body result bodyCost →
        Apply ctx (fuel + 1) (.clos uses env body) argument result
          (bodyCost + tick .applyClosure + retain env.length)
    | pap {fuel head captured argument result saturateCost} :
        Saturate ctx fuel head (captured ++ [argument]) result
          saturateCost →
        Apply ctx (fuel + 1) (.pap head captured) argument result
          (saturateCost + tick .applyPap + retain captured.length)
    | erased {fuel argument} :
        Apply ctx (fuel + 1) .erased argument .erased (tick .applyErased)

  /-- One source saturation decision. -/
  inductive Saturate (ctx : Ctx) :
      Nat → Head → List Value → Value → Profile → Prop where
    | pending {fuel head args} :
        args.length ≠ head.arity →
        Saturate ctx (fuel + 1) head args (.pap head args)
          (tick .saturatePending)
    | full {fuel head args result fireCost} :
        args.length = head.arity →
        Fire ctx fuel head args result fireCost →
        Saturate ctx (fuel + 1) head args result
          (fireCost + tick .saturateFull)

  /-- A fired constructor, extern, or recursor head.  The recursor case
  includes the complete profile of the selected rule body. -/
  inductive Fire (ctx : Ctx) :
      Nat → Head → List Value → Value → Profile → Prop where
    | ctor {fuel address tag arity args} :
        Fire ctx (fuel + 1) (.ctor address tag arity) args
          (.ctor address tag args) (tick .fireConstructor)
    | extern {fuel address arity args result} :
        ctx.oracle address args = some result →
        Fire ctx (fuel + 1) (.ext address arity) args result
          (tick .fireExtern)
    | recursor {fuel address arity numArgs natLit rules args major tag fields
        rule result bodyCost} :
        ctx.env address = some (.recursor numArgs natLit rules) →
        args.getLast? = some major →
        majorCtor natLit major = .ok (tag, fields) →
        rules[tag]? = some rule →
        fields.length = rule.fields →
        Eval ctx fuel
          (fields.reverse ++ args.dropLast.reverse ++
            [.pap (.rec_ address arity) []])
          rule.rhs result bodyCost →
        Fire ctx (fuel + 1) (.rec_ address arity) args result
          (bodyCost + tick .fireRecursor + retain fields.length)

end

mutual

  /-- Every existing call-aware expression trace admits an additive dynamic
  profile. -/
  theorem Eval.ofTrace {ctx : Ctx} {fuel : Nat} {env : List Value}
      {expr : Expr} {value : Value}
      (htrace : ProjectionSafe.Eval ctx fuel env expr value) :
      ∃ profile, Eval ctx fuel env expr value profile := by
    cases htrace with
    | var hlookup => exact ⟨tick .evalVar + retain 1, .var hlookup⟩
    | lit => exact ⟨tick .evalLit, .lit⟩
    | erased => exact ⟨tick .evalErased, .erased⟩
    | lam => exact ⟨tick .evalLam + retain _, .lam⟩
    | letE hvalue hbody =>
        obtain ⟨valueCost, hvalueCost⟩ := Eval.ofTrace hvalue
        obtain ⟨bodyCost, hbodyCost⟩ := Eval.ofTrace hbody
        exact ⟨valueCost + bodyCost + tick .evalLet,
          .letE hvalueCost hbodyCost⟩
    | app hfunction hargument happly =>
        obtain ⟨functionCost, hfunctionCost⟩ := Eval.ofTrace hfunction
        obtain ⟨argumentCost, hargumentCost⟩ := Eval.ofTrace hargument
        obtain ⟨applyCost, happlyCost⟩ := Apply.ofTrace happly
        exact ⟨functionCost + argumentCost + applyCost + tick .evalApp,
          .app hfunctionCost hargumentCost happlyCost⟩
    | proj hsource hfield =>
        obtain ⟨sourceCost, hsourceCost⟩ := Eval.ofTrace hsource
        exact ⟨sourceCost + tick .evalProj + retain 1,
          .proj hsourceCost hfield⟩
    | refDefn hdecl hbody =>
        obtain ⟨bodyCost, hbodyCost⟩ := Eval.ofTrace hbody
        exact ⟨bodyCost + tick .evalRefDefn, .refDefn hdecl hbodyCost⟩
    | refCtor hdecl hsaturate =>
        obtain ⟨saturateCost, hsaturateCost⟩ :=
          Saturate.ofTrace hsaturate
        exact ⟨saturateCost + tick .evalRefCtor,
          .refCtor hdecl hsaturateCost⟩
    | refRecursor hdecl =>
        exact ⟨tick .evalRefRecursor, .refRecursor hdecl⟩
    | refExtern hdecl hsaturate =>
        obtain ⟨saturateCost, hsaturateCost⟩ :=
          Saturate.ofTrace hsaturate
        exact ⟨saturateCost + tick .evalRefExtern,
          .refExtern hdecl hsaturateCost⟩

  theorem Apply.ofTrace {ctx : Ctx} {fuel : Nat}
      {function argument result : Value}
      (htrace : ProjectionSafe.Apply ctx fuel function argument result) :
      ∃ profile, Apply ctx fuel function argument result profile := by
    cases htrace with
    | clos hbody =>
        obtain ⟨bodyCost, hbodyCost⟩ := Eval.ofTrace hbody
        exact ⟨bodyCost + tick .applyClosure + retain _, .clos hbodyCost⟩
    | pap hsaturate =>
        obtain ⟨saturateCost, hsaturateCost⟩ :=
          Saturate.ofTrace hsaturate
        exact ⟨saturateCost + tick .applyPap + retain _,
          .pap hsaturateCost⟩
    | erased => exact ⟨tick .applyErased, .erased⟩

  theorem Saturate.ofTrace {ctx : Ctx} {fuel : Nat} {head : Head}
      {args : List Value} {result : Value}
      (htrace : ProjectionSafe.Saturate ctx fuel head args result) :
      ∃ profile, Saturate ctx fuel head args result profile := by
    cases htrace with
    | pending hlength =>
        exact ⟨tick .saturatePending, .pending hlength⟩
    | full hlength hfire =>
        obtain ⟨fireCost, hfireCost⟩ := Fire.ofTrace hfire
        exact ⟨fireCost + tick .saturateFull, .full hlength hfireCost⟩

  theorem Fire.ofTrace {ctx : Ctx} {fuel : Nat} {head : Head}
      {args : List Value} {result : Value}
      (htrace : ProjectionSafe.Fire ctx fuel head args result) :
      ∃ profile, Fire ctx fuel head args result profile := by
    cases htrace with
    | ctor => exact ⟨tick .fireConstructor, .ctor⟩
    | extern horacle => exact ⟨tick .fireExtern, .extern horacle⟩
    | recursor hdecl hlast hmajor hrule hfields hbody =>
        obtain ⟨bodyCost, hbodyCost⟩ := Eval.ofTrace hbody
        exact ⟨bodyCost + tick .fireRecursor + retain _,
          .recursor hdecl hlast hmajor hrule hfields hbodyCost⟩

end

/-! ## Forgetting and constructing profiles -/

mutual

  /-- Forget the cost annotation and recover the existing call-aware trace. -/
  theorem Eval.toTrace {ctx : Ctx} {fuel : Nat} {env : List Value}
      {expr : Expr} {value : Value} {profile : Profile}
      (hcost : Eval ctx fuel env expr value profile) :
      ProjectionSafe.Eval ctx fuel env expr value := by
    cases hcost with
    | var hlookup => exact .var hlookup
    | lit => exact .lit
    | erased => exact .erased
    | lam => exact .lam
    | letE hvalue hbody => exact .letE hvalue.toTrace hbody.toTrace
    | app hfunction hargument happly =>
        exact .app hfunction.toTrace hargument.toTrace happly.toTrace
    | proj hsource hfield => exact .proj hsource.toTrace hfield
    | refDefn hdecl hbody => exact .refDefn hdecl hbody.toTrace
    | refCtor hdecl hsaturate => exact .refCtor hdecl hsaturate.toTrace
    | refRecursor hdecl => exact .refRecursor hdecl
    | refExtern hdecl hsaturate => exact .refExtern hdecl hsaturate.toTrace

  theorem Apply.toTrace {ctx : Ctx} {fuel : Nat}
      {function argument result : Value} {profile : Profile}
      (hcost : Apply ctx fuel function argument result profile) :
      ProjectionSafe.Apply ctx fuel function argument result := by
    cases hcost with
    | clos hbody => exact .clos hbody.toTrace
    | pap hsaturate => exact .pap hsaturate.toTrace
    | erased => exact .erased

  theorem Saturate.toTrace {ctx : Ctx} {fuel : Nat} {head : Head}
      {args : List Value} {result : Value} {profile : Profile}
      (hcost : Saturate ctx fuel head args result profile) :
      ProjectionSafe.Saturate ctx fuel head args result := by
    cases hcost with
    | pending hlength => exact .pending hlength
    | full hlength hfire => exact .full hlength hfire.toTrace

  theorem Fire.toTrace {ctx : Ctx} {fuel : Nat} {head : Head}
      {args : List Value} {result : Value} {profile : Profile}
      (hcost : Fire ctx fuel head args result profile) :
      ProjectionSafe.Fire ctx fuel head args result := by
    cases hcost with
    | ctor => exact .ctor
    | extern horacle => exact .extern horacle
    | recursor hdecl hlast hmajor hrule hfields hbody =>
        exact .recursor hdecl hlast hmajor hrule hfields hbody.toTrace

end


theorem Eval.run {ctx : Ctx} {fuel : Nat} {env : List Value}
    {expr : Expr} {value : Value} {profile : Profile}
    (hcost : Eval ctx fuel env expr value profile) :
    eval ctx fuel env expr = .ok value :=
  hcost.toTrace.run

theorem Apply.run {ctx : Ctx} {fuel : Nat}
    {function argument result : Value} {profile : Profile}
    (hcost : Apply ctx fuel function argument result profile) :
    apply ctx fuel function argument = .ok result :=
  hcost.toTrace.run

theorem Saturate.run {ctx : Ctx} {fuel : Nat} {head : Head}
    {args : List Value} {result : Value} {profile : Profile}
    (hcost : Saturate ctx fuel head args result profile) :
    saturate ctx fuel head args = .ok result :=
  hcost.toTrace.run

theorem Fire.run {ctx : Ctx} {fuel : Nat} {head : Head}
    {args : List Value} {result : Value} {profile : Profile}
    (hcost : Fire ctx fuel head args result profile) :
    fire ctx fuel head args = .ok result :=
  hcost.toTrace.run

/-- Every expression execution contributes one `eval` event independently of
the evaluator fuel used to justify termination. -/
theorem Eval.evals_pos {ctx : Ctx} {fuel : Nat} {env : List Value}
    {expr : Expr} {value : Value} {profile : Profile}
    (hcost : Eval ctx fuel env expr value profile) :
    0 < profile.evals := by
  cases hcost <;> simp [tick] <;> omega

/-- Surface evaluator sites in an expression.  Lambda bodies and referenced
declarations are counted when they are dynamically entered, rather than at
the site that merely creates or names them. -/
def surfaceEvals : Expr → Nat
  | .var _ | .ref _ | .lit _ | .erased | .lam _ _ => 1
  | .letE _ value body => surfaceEvals value + surfaceEvals body + 1
  | .app function argument =>
      surfaceEvals function + surfaceEvals argument + 1
  | .proj _ source => surfaceEvals source + 1

/-- A dynamic trace contains at least the surface evaluation sites of the
expression it enters.  Called closure and recursor bodies can only add to
this lower bound. -/
theorem Eval.surfaceEvals_le {ctx : Ctx} {fuel : Nat} {env : List Value}
    {expr : Expr} {value : Value} {profile : Profile}
    (hcost : Eval ctx fuel env expr value profile) :
    surfaceEvals expr ≤ profile.evals := by
  induction expr generalizing fuel env value profile with
  | var index =>
      cases hcost
      simp [surfaceEvals, tick, retain]
  | ref address =>
      cases hcost <;> simp [surfaceEvals, tick]
  | app function argument ihFunction ihArgument =>
      cases hcost with
      | app hfunction hargument happly =>
          have hfunctionBound := ihFunction hfunction
          have hargumentBound := ihArgument hargument
          simp [surfaceEvals, tick] at *
          omega
  | lam uses body =>
      cases hcost
      simp [surfaceEvals, tick, retain]
  | letE uses bound body ihBound ihBody =>
      cases hcost with
      | letE hbound hbody =>
          have hboundBound := ihBound hbound
          have hbodyBound := ihBody hbody
          simp [surfaceEvals, tick] at *
          omega
  | proj index source ihSource =>
      cases hcost with
      | proj hsource hfield =>
          have hsourceBound := ihSource hsource
          simp [surfaceEvals, tick, retain] at *
          omega
  | lit literal =>
      cases hcost
      simp [surfaceEvals, tick]
  | erased =>
      cases hcost
      simp [surfaceEvals, tick]

/-- A closed source expression has `profile` when some exact call-aware
successful trace has that annotation.  Fuel is existential and remains
separate from the profile. -/
def Profiled (ctx : Ctx) (expr : Expr) (value : Value)
    (profile : Profile) : Prop :=
  ∃ fuel, Eval ctx fuel [] expr value profile

theorem Profiled.run {ctx : Ctx} {expr : Expr} {value : Value}
    {profile : Profile} (hprofile : Profiled ctx expr value profile) :
    ∃ fuel, eval ctx fuel [] expr = .ok value := by
  obtain ⟨fuel, hcost⟩ := hprofile
  exact ⟨fuel, hcost.run⟩

theorem Profiled.evals_pos {ctx : Ctx} {expr : Expr} {value : Value}
    {profile : Profile} (hprofile : Profiled ctx expr value profile) :
    0 < profile.evals := by
  obtain ⟨_, hcost⟩ := hprofile
  exact hcost.evals_pos

theorem Profiled.ofTrace {ctx : Ctx} {fuel : Nat} {expr : Expr}
    {value : Value}
    (htrace : ProjectionSafe.Eval ctx fuel [] expr value) :
    ∃ profile, Profiled ctx expr value profile := by
  obtain ⟨profile, hcost⟩ := Eval.ofTrace htrace
  exact ⟨profile, fuel, hcost⟩

/-! ## Additive application spines -/

/-- A dynamically executed curried application spine.  Each entered body is
represented by its `Apply` profile, and the spine profile is their sum. -/
inductive Applies (ctx : Ctx) :
    Value → List Value → Value → Profile → Prop where
  | nil {value : Value} : Applies ctx value [] value 0
  | cons {fuel : Nat} {function argument middle result : Value}
      {arguments : List Value} {stepCost restCost : Profile} :
      Apply ctx fuel function argument middle stepCost →
      Applies ctx middle arguments result restCost →
      Applies ctx function (argument :: arguments) result
        (stepCost + restCost)

/-- Dependent state-threaded traversal of a dynamically costed application
spine. Clients receive the exact head application profile, the original
profiled tail derivation, and the recursively produced result while the
initial value, remaining arguments, final value, and additive profile stay
synchronized. -/
theorem Applies.traverse
    {ctx : Ctx}
    {Result : Value → List Value → Value → Profile → Prop}
    (hnil : ∀ value, Result value [] value 0)
    (hcons : ∀ {fuel : Nat} {function argument middle result : Value}
        {arguments : List Value} {stepCost restCost : Profile},
      Apply ctx fuel function argument middle stepCost →
      Applies ctx middle arguments result restCost →
      Result middle arguments result restCost →
      Result function (argument :: arguments) result
        (stepCost + restCost))
    {function result : Value} {arguments : List Value} {cost : Profile}
    (happly : Applies ctx function arguments result cost) :
    Result function arguments result cost := by
  induction happly with
  | nil => exact hnil _
  | cons hstep htail ih => exact hcons hstep htail ih

/-- Application-spine concatenation is profile addition. -/
theorem Applies.append {ctx : Ctx}
    {function middle result : Value} {left right : List Value}
    {leftCost rightCost : Profile}
    (hleft : Applies ctx function left middle leftCost)
    (hright : Applies ctx middle right result rightCost) :
    Applies ctx function (left ++ right) result (leftCost + rightCost) := by
  exact (Applies.traverse
    (Result := fun currentFunction currentArguments currentMiddle currentCost =>
      ∀ {currentResult : Value} {rightArguments : List Value}
          {rightCost : Profile},
        Applies ctx currentMiddle rightArguments currentResult rightCost →
        Applies ctx currentFunction (currentArguments ++ rightArguments)
          currentResult (currentCost + rightCost))
    (hnil := by
      intro value currentResult rightArguments currentCost hright
      simpa [Profile.zero_add] using hright)
    (hcons := by
      intro fuel currentFunction argument currentMiddle currentResult
        currentArguments stepCost restCost hstep htail ih finalResult
        rightArguments rightCost hright
      simpa only [List.cons_append, Profile.add_assoc] using
        Applies.cons hstep (ih hright))
    hleft) hright

/-- One final application contributes exactly its own profile. -/
theorem Applies.snoc {ctx : Ctx}
    {function middle result argument : Value} {arguments : List Value}
    {spineCost stepCost : Profile} {fuel : Nat}
    (hspine : Applies ctx function arguments middle spineCost)
    (hstep : Apply ctx fuel middle argument result stepCost) :
    Applies ctx function (arguments ++ [argument]) result
      (spineCost + stepCost) := by
  apply hspine.append
  simpa [Profile.add_zero] using (Applies.cons hstep Applies.nil)

/-- Every bounded call-aware application trace receives an additive profile;
the fuel bound remains only the termination measure. -/
theorem Applies.ofTrace {ctx : Ctx} {limit : Nat}
    {function result : Value} {arguments : List Value}
    (htrace : ProjectionSafe.AppliesBelow ctx limit function arguments
      result) :
    ∃ profile, Applies ctx function arguments result profile := by
  exact ProjectionSafe.AppliesBelow.traverse
    (Result := fun currentFunction currentArguments currentResult =>
      ∃ profile,
        Applies ctx currentFunction currentArguments currentResult profile)
    (hnil := fun _ => ⟨0, .nil⟩)
    (hcons := by
      intro currentFunction argument currentMiddle currentResult
        currentArguments fuel hfuel hstep htail ih
      obtain ⟨stepCost, hstepCost⟩ := Apply.ofTrace hstep
      obtain ⟨restCost, hrestCost⟩ := ih
      exact ⟨stepCost + restCost, .cons hstepCost hrestCost⟩)
    htrace

end Ix.Compiler.IxIR0.DynamicCost
