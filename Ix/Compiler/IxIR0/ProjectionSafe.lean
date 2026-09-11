import Ix.Compiler.IxIR0.Eval

/-!
# Call-aware projection-safe IxIR₀ execution

`IxIR0.eval` deliberately maps projection from `erased` to `erased`. That is
the right erasure semantics, but IxIR₁ lowers a runtime projection to a
concrete fetch, where the same shape is ordinary stuckness. Successful target
progress therefore needs more than an `IxIR0.eval = .ok` equation.

The four mutually inductive traces below mirror the four mutually recursive
IxIR₀ evaluator functions at their exact fuel. They retain every executed
expression body, including closure bodies and recursor rules reached through
`apply`/`saturate`/`fire`, and intentionally have no constructor for projection
from `erased`. This makes source evaluator fuel available as the well-founded
measure for total-correctness proofs whose target fuel is existential.
-/

namespace Ix.Compiler.IxIR0.ProjectionSafe

open Ix.Compiler.Ixon (Address Uses)

mutual

  /-- A successful `eval` trace in which every dynamically reached projection
  scrutinizes a constructor. -/
  inductive Eval (ctx : Ctx) :
      Nat → List Value → Expr → Value → Prop where
    | var {fuel : Nat} {env : List Value} {index : Nat} {value : Value} :
        env[index]? = some value →
        Eval ctx (fuel + 1) env (.var index) value
    | lit {fuel : Nat} {env : List Value} {literal : Literal} :
        Eval ctx (fuel + 1) env (.lit literal) (.lit literal)
    | erased {fuel : Nat} {env : List Value} :
        Eval ctx (fuel + 1) env .erased .erased
    | lam {fuel : Nat} {env : List Value} {uses : Uses} {body : Expr} :
        Eval ctx (fuel + 1) env (.lam uses body) (.clos uses env body)
    | letE {fuel : Nat} {env : List Value} {uses : Uses}
        {value body : Expr} {bound result : Value} :
        Eval ctx fuel env value bound →
        Eval ctx fuel (bound :: env) body result →
        Eval ctx (fuel + 1) env (.letE uses value body) result
    | app {fuel : Nat} {env : List Value} {function argument : Expr}
        {functionValue argumentValue result : Value} :
        Eval ctx fuel env function functionValue →
        Eval ctx fuel env argument argumentValue →
        Apply ctx fuel functionValue argumentValue result →
        Eval ctx (fuel + 1) env (.app function argument) result
    | proj {fuel : Nat} {env : List Value} {index : Nat} {source : Expr}
        {address : Address} {tag : Nat} {fields : List Value}
        {result : Value} :
        Eval ctx fuel env source (.ctor address tag fields) →
        fields[index]? = some result →
        Eval ctx (fuel + 1) env (.proj index source) result
    | refDefn {fuel : Nat} {env : List Value} {address : Address}
        {world : Ix.Compiler.Ixon.Owned} {body : Expr} {result : Value} :
        ctx.env address = some (.defn world body) →
        Eval ctx fuel [] body result →
        Eval ctx (fuel + 1) env (.ref address) result
    | refCtor {fuel : Nat} {env : List Value} {address : Address}
        {tag arity : Nat} {result : Value} :
        ctx.env address = some (.ctor tag arity) →
        Saturate ctx fuel (.ctor address tag arity) [] result →
        Eval ctx (fuel + 1) env (.ref address) result
    | refRecursor {fuel : Nat} {env : List Value} {address : Address}
        {numArgs : Nat} {natLit : Bool} {rules : Array RecRule} :
        ctx.env address = some (.recursor numArgs natLit rules) →
        Eval ctx (fuel + 1) env (.ref address)
          (.pap (.rec_ address (numArgs + 1)) [])
    | refExtern {fuel : Nat} {env : List Value} {address : Address}
        {arity : Nat} {result : Value} :
        ctx.env address = some (.extern arity) →
        Saturate ctx fuel (.ext address arity) [] result →
        Eval ctx (fuel + 1) env (.ref address) result

  /-- A successful call-aware `apply` trace. Closure entry is where the
  dynamically selected body re-enters `Eval`. -/
  inductive Apply (ctx : Ctx) : Nat → Value → Value → Value → Prop where
    | clos {fuel : Nat} {uses : Uses} {env : List Value} {body : Expr}
        {argument result : Value} :
        Eval ctx fuel (argument :: env) body result →
        Apply ctx (fuel + 1) (.clos uses env body) argument result
    | pap {fuel : Nat} {head : Head} {captured : List Value}
        {argument result : Value} :
        Saturate ctx fuel head (captured ++ [argument]) result →
        Apply ctx (fuel + 1) (.pap head captured) argument result
    | erased {fuel : Nat} {argument : Value} :
        Apply ctx (fuel + 1) .erased argument .erased

  /-- A successful `saturate` trace. -/
  inductive Saturate (ctx : Ctx) :
      Nat → Head → List Value → Value → Prop where
    | pending {fuel : Nat} {head : Head} {args : List Value} :
        args.length ≠ head.arity →
        Saturate ctx (fuel + 1) head args (.pap head args)
    | full {fuel : Nat} {head : Head} {args : List Value}
        {result : Value} :
        args.length = head.arity →
        Fire ctx fuel head args result →
        Saturate ctx (fuel + 1) head args result

  /-- A successful `fire` trace. The recursor constructor retains the exact
  selected rule-body execution and hence any projections reached inside it. -/
  inductive Fire (ctx : Ctx) :
      Nat → Head → List Value → Value → Prop where
    | ctor {fuel : Nat} {address : Address} {tag arity : Nat}
        {args : List Value} :
        Fire ctx (fuel + 1) (.ctor address tag arity) args
          (.ctor address tag args)
    | extern {fuel : Nat} {address : Address} {arity : Nat}
        {args : List Value} {result : Value} :
        ctx.oracle address args = some result →
        Fire ctx (fuel + 1) (.ext address arity) args result
    | recursor {fuel : Nat} {address : Address} {arity numArgs : Nat}
        {natLit : Bool} {rules : Array RecRule} {args : List Value}
        {major : Value} {tag : Nat} {fields : List Value}
        {rule : RecRule} {result : Value} :
        ctx.env address = some (.recursor numArgs natLit rules) →
        args.getLast? = some major →
        majorCtor natLit major = .ok (tag, fields) →
        rules[tag]? = some rule →
        fields.length = rule.fields →
        Eval ctx fuel
          (fields.reverse ++ args.dropLast.reverse ++
            [.pap (.rec_ address arity) []])
          rule.rhs result →
        Fire ctx (fuel + 1) (.rec_ address arity) args result

end

private theorem bindOk {error alpha beta : Type} (value : alpha)
    (next : alpha → Except error beta) :
    (Except.ok value >>= next) = next value := rfl

mutual

  /-- A safe evaluation trace executes successfully at its recorded fuel. -/
  theorem Eval.run {ctx : Ctx} {fuel : Nat} {env : List Value}
      {expr : Expr} {value : Value}
      (htrace : Eval ctx fuel env expr value) :
      eval ctx fuel env expr = .ok value := by
    cases htrace with
    | var hlookup =>
        rw [eval.eq_def]
        dsimp only
        rw [hlookup]
    | lit => rw [eval.eq_def]
    | erased => rw [eval.eq_def]
    | lam => rw [eval.eq_def]
    | letE hvalue hbody =>
        rw [eval.eq_def]
        dsimp only
        rw [hvalue.run, bindOk]
        exact hbody.run
    | app hfunction hargument happly =>
        rw [eval.eq_def]
        dsimp only
        rw [hfunction.run, bindOk, hargument.run, bindOk]
        exact happly.run
    | proj hsource hfield =>
        rw [eval.eq_def]
        dsimp only
        rw [hsource.run, bindOk]
        simp only
        rw [hfield]
    | refDefn hdecl hbody =>
        rw [eval.eq_def]
        dsimp only
        rw [hdecl]
        exact hbody.run
    | refCtor hdecl hsaturate =>
        rw [eval.eq_def]
        dsimp only
        rw [hdecl]
        exact hsaturate.run
    | refRecursor hdecl =>
        rw [eval.eq_def]
        dsimp only
        rw [hdecl]
    | refExtern hdecl hsaturate =>
        rw [eval.eq_def]
        dsimp only
        rw [hdecl]
        exact hsaturate.run

  /-- A safe application trace executes successfully at its recorded fuel. -/
  theorem Apply.run {ctx : Ctx} {fuel : Nat} {function argument result : Value}
      (htrace : Apply ctx fuel function argument result) :
      apply ctx fuel function argument = .ok result := by
    cases htrace with
    | clos hbody =>
        rw [apply.eq_def]
        exact hbody.run
    | pap hsaturate =>
        rw [apply.eq_def]
        exact hsaturate.run
    | erased => rw [apply.eq_def]

  /-- A safe saturation trace executes successfully at its recorded fuel. -/
  theorem Saturate.run {ctx : Ctx} {fuel : Nat} {head : Head}
      {args : List Value} {result : Value}
      (htrace : Saturate ctx fuel head args result) :
      saturate ctx fuel head args = .ok result := by
    cases htrace with
    | pending hlength =>
        rw [saturate.eq_def]
        dsimp only
        simp [hlength]
    | full hlength hfire =>
        rw [saturate.eq_def]
        dsimp only
        simp only [beq_iff_eq.mpr hlength, if_true]
        exact hfire.run

  /-- A safe firing trace executes successfully at its recorded fuel. -/
  theorem Fire.run {ctx : Ctx} {fuel : Nat} {head : Head}
      {args : List Value} {result : Value}
      (htrace : Fire ctx fuel head args result) :
      fire ctx fuel head args = .ok result := by
    cases htrace with
    | ctor => rw [fire.eq_def]
    | extern horacle =>
        rw [fire.eq_def]
        dsimp only
        rw [horacle]
    | recursor hdecl hlast hmajor hrule hfields hbody =>
        rw [fire.eq_def]
        dsimp only
        rw [hdecl]
        dsimp only
        rw [hlast]
        dsimp only
        rw [hmajor, bindOk]
        dsimp only
        rw [hrule]
        dsimp only
        simp only [hfields, bne_self_eq_false]
        exact hbody.run

end

/-- A reference trace is independent of the ambient local environment: every
reference constructor evaluates its declaration from the closed environment. -/
theorem Eval.ref_closed {ctx : Ctx} {fuel : Nat} {env : List Value}
    {address : Address} {value : Value}
    (htrace : Eval ctx fuel env (.ref address) value) :
    Eval ctx fuel [] (.ref address) value := by
  cases htrace with
  | refDefn hdecl hbody => exact .refDefn hdecl hbody
  | refCtor hdecl hsaturate => exact .refCtor hdecl hsaturate
  | refRecursor hdecl => exact .refRecursor hdecl
  | refExtern hdecl hsaturate => exact .refExtern hdecl hsaturate

mutual

  /-- Projection-safe evaluation is monotone in fuel. -/
  theorem Eval.mono {ctx : Ctx} {fuel : Nat} {env : List Value}
      {expr : Expr} {value : Value}
      (htrace : Eval ctx fuel env expr value) :
      Eval ctx (fuel + 1) env expr value := by
    cases htrace with
    | var hlookup => exact .var hlookup
    | lit => exact .lit
    | erased => exact .erased
    | lam => exact .lam
    | letE hvalue hbody => exact .letE hvalue.mono hbody.mono
    | app hfunction hargument happly =>
        exact .app hfunction.mono hargument.mono happly.mono
    | proj hsource hfield => exact .proj hsource.mono hfield
    | refDefn hdecl hbody => exact .refDefn hdecl hbody.mono
    | refCtor hdecl hsaturate => exact .refCtor hdecl hsaturate.mono
    | refRecursor hdecl => exact .refRecursor hdecl
    | refExtern hdecl hsaturate => exact .refExtern hdecl hsaturate.mono

  /-- Projection-safe application is monotone in fuel. -/
  theorem Apply.mono {ctx : Ctx} {fuel : Nat}
      {function argument result : Value}
      (htrace : Apply ctx fuel function argument result) :
      Apply ctx (fuel + 1) function argument result := by
    cases htrace with
    | clos hbody => exact .clos hbody.mono
    | pap hsaturate => exact .pap hsaturate.mono
    | erased => exact .erased

  /-- Projection-safe saturation is monotone in fuel. -/
  theorem Saturate.mono {ctx : Ctx} {fuel : Nat} {head : Head}
      {args : List Value} {result : Value}
      (htrace : Saturate ctx fuel head args result) :
      Saturate ctx (fuel + 1) head args result := by
    cases htrace with
    | pending hlength => exact .pending hlength
    | full hlength hfire => exact .full hlength hfire.mono

  /-- Projection-safe firing is monotone in fuel. -/
  theorem Fire.mono {ctx : Ctx} {fuel : Nat} {head : Head}
      {args : List Value} {result : Value}
      (htrace : Fire ctx fuel head args result) :
      Fire ctx (fuel + 1) head args result := by
    cases htrace with
    | ctor => exact .ctor
    | extern horacle => exact .extern horacle
    | recursor hdecl hlast hmajor hrule hfields hbody =>
        exact .recursor hdecl hlast hmajor hrule hfields hbody.mono

end

theorem Eval.mono_le {ctx : Ctx} {smaller larger : Nat}
    {env : List Value} {expr : Expr} {value : Value}
    (hbound : smaller ≤ larger) (htrace : Eval ctx smaller env expr value) :
    Eval ctx larger env expr value := by
  induction hbound with
  | refl => exact htrace
  | step hbound ih => exact ih.mono

theorem Apply.mono_le {ctx : Ctx} {smaller larger : Nat}
    {function argument result : Value}
    (hbound : smaller ≤ larger)
    (htrace : Apply ctx smaller function argument result) :
    Apply ctx larger function argument result := by
  induction hbound with
  | refl => exact htrace
  | step hbound ih => exact ih.mono

theorem Saturate.mono_le {ctx : Ctx} {smaller larger : Nat}
    {head : Head} {args : List Value} {result : Value}
    (hbound : smaller ≤ larger)
    (htrace : Saturate ctx smaller head args result) :
    Saturate ctx larger head args result := by
  induction hbound with
  | refl => exact htrace
  | step hbound ih => exact ih.mono

theorem Fire.mono_le {ctx : Ctx} {smaller larger : Nat}
    {head : Head} {args : List Value} {result : Value}
    (hbound : smaller ≤ larger)
    (htrace : Fire ctx smaller head args result) :
    Fire ctx larger head args result := by
  induction hbound with
  | refl => exact htrace
  | step hbound ih => exact ih.mono

/-- A call-aware n-ary application spine whose every individual application
executes strictly below one enclosing source-evaluator fuel.  The common
bound is the well-founded index used by lowering progress: entering a closure
or recursor rule exposes an `Eval` trace at a strictly smaller fuel. -/
inductive AppliesBelow (ctx : Ctx) (limit : Nat) :
    Value → List Value → Value → Prop where
  | nil {value : Value} : AppliesBelow ctx limit value [] value
  | cons {fuel : Nat} {function argument middle result : Value}
      {arguments : List Value} :
      fuel < limit →
      Apply ctx fuel function argument middle →
      AppliesBelow ctx limit middle arguments result →
      AppliesBelow ctx limit function (argument :: arguments) result

/-- Dependent traversal of a bounded application spine. Clients receive the
exact head fuel bound and application trace, the original tail derivation,
and the recursively produced result while the initial value, remaining
arguments, and final value stay synchronized. -/
theorem AppliesBelow.traverse {ctx : Ctx} {limit : Nat}
    {Result : Value → List Value → Value → Prop}
    (hnil : ∀ value, Result value [] value)
    (hcons : ∀ {function argument middle result : Value}
        {arguments : List Value} {fuel : Nat},
      fuel < limit →
      Apply ctx fuel function argument middle →
      AppliesBelow ctx limit middle arguments result →
      Result middle arguments result →
      Result function (argument :: arguments) result)
    {function result : Value} {arguments : List Value}
    (hspine : AppliesBelow ctx limit function arguments result) :
    Result function arguments result := by
  induction hspine with
  | nil => exact hnil _
  | cons hfuel hstep htail ih => exact hcons hfuel hstep htail ih

/-- Increasing the enclosing source-fuel bound preserves a safe spine. -/
theorem AppliesBelow.mono_limit {ctx : Ctx} {smaller larger : Nat}
    {function result : Value} {arguments : List Value}
    (hspine : AppliesBelow ctx smaller function arguments result)
    (hbound : smaller ≤ larger) :
    AppliesBelow ctx larger function arguments result := by
  exact AppliesBelow.traverse
    (Result := fun currentFunction currentArguments currentResult =>
      AppliesBelow ctx larger currentFunction currentArguments currentResult)
    (hnil := fun _ => .nil)
    (hcons := by
      intro currentFunction argument currentMiddle currentResult
        currentArguments fuel hfuel hstep htail ih
      exact .cons (Nat.lt_of_lt_of_le hfuel hbound) hstep ih)
    hspine

/-- Applying one safe prefix and then another applies their concatenation. -/
theorem AppliesBelow.append {ctx : Ctx} {limit : Nat}
    {function middle result : Value} {left right : List Value}
    (hleft : AppliesBelow ctx limit function left middle)
    (hright : AppliesBelow ctx limit middle right result) :
    AppliesBelow ctx limit function (left ++ right) result := by
  exact (AppliesBelow.traverse
    (Result := fun currentFunction currentArguments currentResult =>
      ∀ {remaining final},
        AppliesBelow ctx limit currentResult remaining final →
        AppliesBelow ctx limit currentFunction
          (currentArguments ++ remaining) final)
    (hnil := by
      intro value remaining final hremaining
      simpa using hremaining)
    (hcons := by
      intro currentFunction argument currentMiddle currentResult
        currentArguments fuel hfuel hstep htail ih remaining final hremaining
      exact .cons hfuel hstep (ih hremaining))
    hleft) hright

/-- Add one final safe application to a completed spine. -/
theorem AppliesBelow.snoc {ctx : Ctx} {limit fuel : Nat}
    {function middle result argument : Value} {arguments : List Value}
    (hspine : AppliesBelow ctx limit function arguments middle)
    (hfuel : fuel < limit)
    (hstep : Apply ctx fuel middle argument result) :
    AppliesBelow ctx limit function (arguments ++ [argument]) result :=
  hspine.append (.cons hfuel hstep .nil)

/-- Split at the same numeric boundary used by `take`/`drop` call lowering. -/
theorem AppliesBelow.splitAt {ctx : Ctx} {limit : Nat}
    {function result : Value} {arguments : List Value}
    (hspine : AppliesBelow ctx limit function arguments result)
    (count : Nat) :
    ∃ middle,
      AppliesBelow ctx limit function (arguments.take count) middle ∧
      AppliesBelow ctx limit middle (arguments.drop count) result := by
  exact (AppliesBelow.traverse
    (Result := fun currentFunction currentArguments currentResult =>
      ∀ currentCount,
        ∃ middle,
          AppliesBelow ctx limit currentFunction
              (currentArguments.take currentCount) middle ∧
            AppliesBelow ctx limit middle
              (currentArguments.drop currentCount) currentResult)
    (hnil := by
      intro value currentCount
      simp
      exact ⟨value, .nil, .nil⟩)
    (hcons := by
      intro currentFunction argument currentMiddle currentResult
        currentArguments fuel hfuel hstep htail ih currentCount
      cases currentCount with
      | zero => exact ⟨currentFunction, .nil, .cons hfuel hstep htail⟩
      | succ currentCount =>
        obtain ⟨middle, hprefix, hsuffix⟩ := ih currentCount
        exact ⟨middle, .cons hfuel hstep hprefix, hsuffix⟩)
    hspine) count

/-- Split a bounded safe application spine at an arbitrary list boundary. -/
theorem AppliesBelow.split {ctx : Ctx} {limit : Nat}
    {function result : Value} :
    ∀ {left right : List Value},
      AppliesBelow ctx limit function (left ++ right) result →
      ∃ middle,
        AppliesBelow ctx limit function left middle ∧
        AppliesBelow ctx limit middle right result := by
  intro left right hspine
  simpa using AppliesBelow.splitAt hspine left.length

/-- A single safe application below the enclosing fuel is a singleton
application spine. -/
theorem Apply.toAppliesBelow {ctx : Ctx} {limit fuel : Nat}
    {function argument result : Value}
    (htrace : Apply ctx fuel function argument result)
    (hbound : fuel < limit) :
    AppliesBelow ctx limit function [argument] result :=
  .cons hbound htrace .nil

/-- Pointwise argument evaluations below one enclosing expression fuel. -/
inductive EvalsBelow (ctx : Ctx) (limit : Nat) (env : List Value) :
    List Expr → List Value → Prop where
  | nil : EvalsBelow ctx limit env [] []
  | cons {fuel : Nat} {expr : Expr} {value : Value}
      {expressions : List Expr} {values : List Value} :
      fuel < limit →
      Eval ctx fuel env expr value →
      EvalsBelow ctx limit env expressions values →
      EvalsBelow ctx limit env (expr :: expressions) (value :: values)

/-- Dependent lockstep traversal of bounded projection-safe argument traces.
Each callback receives the exact fuel bound, head trace, and original tail
derivation together with the recursively produced result. -/
theorem EvalsBelow.traverse {ctx : Ctx} {limit : Nat} {env : List Value}
    {Result : List Expr → List Value → Prop}
    (hnil : Result [] [])
    (hcons : ∀ {fuel : Nat} {expr : Expr} {value : Value}
        {expressions : List Expr} {values : List Value},
      fuel < limit →
      Eval ctx fuel env expr value →
      EvalsBelow ctx limit env expressions values →
      Result expressions values →
      Result (expr :: expressions) (value :: values))
    {expressions : List Expr} {values : List Value}
    (hargs : EvalsBelow ctx limit env expressions values) :
    Result expressions values := by
  induction hargs with
  | nil => exact hnil
  | cons hfuel heval htail ih => exact hcons hfuel heval htail ih

theorem EvalsBelow.mono_limit {ctx : Ctx} {smaller larger : Nat}
    {env : List Value} {expressions : List Expr} {values : List Value}
    (hargs : EvalsBelow ctx smaller env expressions values)
    (hbound : smaller ≤ larger) :
    EvalsBelow ctx larger env expressions values := by
  exact EvalsBelow.traverse
    (Result := fun currentExpressions currentValues =>
      EvalsBelow ctx larger env currentExpressions currentValues)
    (hnil := .nil)
    (hcons := by
      intro fuel expr value currentExpressions currentValues hfuel heval
        htail ih
      exact .cons (Nat.lt_of_lt_of_le hfuel hbound) heval ih)
    hargs

@[simp] theorem EvalsBelow.lengths {ctx : Ctx} {limit : Nat}
    {env : List Value} {expressions : List Expr} {values : List Value}
    (hargs : EvalsBelow ctx limit env expressions values) :
    expressions.length = values.length := by
  exact EvalsBelow.traverse
    (Result := fun currentExpressions currentValues =>
      currentExpressions.length = currentValues.length)
    (hnil := rfl)
    (hcons := by
      intro fuel expr value currentExpressions currentValues hfuel heval
        htail ih
      simp [ih])
    hargs

/-- Exact-fuel argument safety is inherited by every prefix. -/
theorem EvalsBelow.take {ctx : Ctx} {limit : Nat}
    {env : List Value} {expressions : List Expr} {values : List Value}
    (hargs : EvalsBelow ctx limit env expressions values) (count : Nat) :
    EvalsBelow ctx limit env (expressions.take count) (values.take count) := by
  exact (EvalsBelow.traverse
    (Result := fun currentExpressions currentValues =>
      ∀ currentCount,
        EvalsBelow ctx limit env (currentExpressions.take currentCount)
          (currentValues.take currentCount))
    (hnil := by
      intro currentCount
      simp
      exact .nil)
    (hcons := by
      intro fuel expr value currentExpressions currentValues hfuel heval
        htail ih currentCount
      cases currentCount with
      | zero => exact .nil
      | succ currentCount =>
        simpa using EvalsBelow.cons hfuel heval (ih currentCount))
    hargs) count

/-- Exact-fuel argument safety is inherited by every suffix. -/
theorem EvalsBelow.drop {ctx : Ctx} {limit : Nat}
    {env : List Value} {expressions : List Expr} {values : List Value}
    (hargs : EvalsBelow ctx limit env expressions values) (count : Nat) :
    EvalsBelow ctx limit env (expressions.drop count) (values.drop count) := by
  exact (EvalsBelow.traverse
    (Result := fun currentExpressions currentValues =>
      ∀ currentCount,
        EvalsBelow ctx limit env (currentExpressions.drop currentCount)
          (currentValues.drop currentCount))
    (hnil := by
      intro currentCount
      simp
      exact .nil)
    (hcons := by
      intro fuel expr value currentExpressions currentValues hfuel heval
        htail ih currentCount
      cases currentCount with
      | zero => exact .cons hfuel heval htail
      | succ currentCount => simpa using ih currentCount)
    hargs) count

/-- A flattened expression spine at one enclosing source-evaluator fuel.
Every application and argument trace is strictly below `limit`; the head may
itself use exactly `limit` when the spine is empty. -/
inductive Spine (ctx : Ctx) (limit : Nat) (env : List Value) :
    Expr → List Expr → Value → Prop where
  | intro {headFuel : Nat} {headValue : Value}
      {head : Expr} {arguments : List Expr} {result : Value}
      {argumentValues : List Value} :
      headFuel ≤ limit →
      Eval ctx headFuel env head headValue →
      EvalsBelow ctx limit env arguments argumentValues →
      AppliesBelow ctx limit headValue argumentValues result →
      Spine ctx limit env head arguments result

/-- Invert a safe application expression without forgetting any predecessor
trace or its exact one-step fuel equation. -/
theorem Eval.app_inv {ctx : Ctx} {fuel : Nat} {env : List Value}
    {function argument : Expr} {result : Value}
    (htrace : Eval ctx fuel env (.app function argument) result) :
    ∃ previous functionValue argumentValue,
      fuel = previous + 1 ∧
      Eval ctx previous env function functionValue ∧
      Eval ctx previous env argument argumentValue ∧
      Apply ctx previous functionValue argumentValue result := by
  cases htrace with
  | app hfunction hargument happly =>
      exact ⟨_, _, _, rfl, hfunction, hargument, happly⟩

/-- Any safe expression is the empty-argument spine at its exact fuel. -/
theorem Spine.of_eval_nil {ctx : Ctx} {fuel : Nat} {env : List Value}
    {expr : Expr} {value : Value}
    (htrace : Eval ctx fuel env expr value) :
    Spine ctx fuel env expr [] value :=
  .intro (Nat.le_refl _) htrace .nil .nil

/-- Flatten one more left-associated application while preserving the common
source-fuel bound and the exact dynamically entered `Apply` trace. -/
theorem Spine.flattenApp {ctx : Ctx} {limit : Nat} {env : List Value}
    {function argument : Expr} {arguments : List Expr} {result : Value}
    (hspine : Spine ctx limit env (.app function argument) arguments result) :
    Spine ctx limit env function (argument :: arguments) result := by
  cases hspine with
  | @intro headFuel headValue _ _ _ argumentValues hheadBound hhead
      harguments happlies =>
      obtain ⟨previous, functionValue, argumentValue, hfuel, hfunction,
        hargument, happly⟩ := hhead.app_inv
      subst headFuel
      exact .intro (by omega) hfunction
        (.cons (by omega) hargument harguments)
        (.cons (by omega) happly happlies)

/-- Singleton specialization used by the expression-lowering application
branch. -/
theorem Spine.of_eval_app {ctx : Ctx} {fuel : Nat} {env : List Value}
    {function argument : Expr} {result : Value}
    (htrace : Eval ctx fuel env (.app function argument) result) :
    Spine ctx fuel env function [argument] result :=
  (Spine.of_eval_nil htrace).flattenApp

/-- Fuel-free call-aware projection-safe termination. -/
def Terminates (ctx : Ctx) (env : List Value) (expr : Expr)
    (value : Value) : Prop :=
  ∃ fuel, Eval ctx fuel env expr value

end Ix.Compiler.IxIR0.ProjectionSafe
