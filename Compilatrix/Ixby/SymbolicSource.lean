import Compilatrix.Ixby.Basic

/-! A conservative symbolic IxIR₀ evaluator. Parameters remain opaque: a
successful symbolic derivation is valid for every substitution of runtime
values. Inspecting an opaque parameter is rejected, never guessed. -/

namespace Compilatrix.Ixby.SymbolicSource

open Ixon (Address Uses)
open IxIR0 (Expr Head Literal)

inductive Value where
  | parameter (index : Nat)
  | clos (uses : Uses) (env : List Value) (body : Expr)
  | pap (head : Head) (args : List Value)
  | ctor (address : Address) (tag : Nat) (fields : List Value)
  | lit (literal : Literal)
  | erased
  deriving Repr, Inhabited

def Value.instantiate (input : Nat → IxIR0.Value) : Value → IxIR0.Value
  | .parameter index => input index
  | .clos uses env body => .clos uses (env.map (Value.instantiate input)) body
  | .pap head args => .pap head (args.map (Value.instantiate input))
  | .ctor address tag fields => .ctor address tag (fields.map (Value.instantiate input))
  | .lit literal => .lit literal
  | .erased => .erased

def majorCtor (natLit : Bool) : Value → Option (Nat × List Value)
  | .ctor _ tag fields => some (tag, fields)
  | .lit (.nat n) => if natLit then
      match n with
      | 0 => some (0, [])
      | n + 1 => some (1, [.lit (.nat n)])
    else none
  | _ => none

mutual
  def eval (ctx : IxIR0.Ctx) : Nat → List Value → Expr → Option Value
    | 0, _, _ => none
    | fuel + 1, env, expr => match expr with
      | .var index => env[index]?
      | .lit literal => some (.lit literal)
      | .erased => some .erased
      | .lam uses body => some (.clos uses env body)
      | .letE _ value body => do
          let value ← eval ctx fuel env value
          eval ctx fuel (value :: env) body
      | .app fn arg => do
          let fn ← eval ctx fuel env fn
          let arg ← eval ctx fuel env arg
          apply ctx fuel fn arg
      | .proj field expr => do
          match ← eval ctx fuel env expr with
          | .ctor _ _ fields => fields[field]?
          | .erased => some .erased
          | _ => none
      | .ref address => do
          match ← ctx.env address with
          | .defn _ body => eval ctx fuel [] body
          | .ctor tag arity => saturate ctx fuel (.ctor address tag arity) []
          | .recursor pre _ _ => some (.pap (.rec_ address (pre + 1)) [])
          | .extern _ => none
  def apply (ctx : IxIR0.Ctx) : Nat → Value → Value → Option Value
    | 0, _, _ => none
    | fuel + 1, fn, arg => match fn with
      | .clos _ env body => eval ctx fuel (arg :: env) body
      | .pap head args => saturate ctx fuel head (args ++ [arg])
      | .erased => some .erased
      | _ => none
  def saturate (ctx : IxIR0.Ctx) : Nat → Head → List Value → Option Value
    | 0, _, _ => none
    | fuel + 1, head, args =>
        if args.length == head.arity then fire ctx fuel head args
        else some (.pap head args)
  def fire (ctx : IxIR0.Ctx) : Nat → Head → List Value → Option Value
    | 0, _, _ => none
    | fuel + 1, head, args => match head with
      | .ctor address tag _ => some (.ctor address tag args)
      | .ext _ _ => none
      | .rec_ address arity => do
          let .recursor _ natLit rules ← ctx.env address | none
          let major ← args.getLast?
          let (tag, fields) ← majorCtor natLit major
          let rule ← rules[tag]?
          if fields.length != rule.fields then none
          else
            eval ctx fuel
              (fields.reverse ++ args.dropLast.reverse ++ [.pap (.rec_ address arity) []]) rule.rhs
end

private theorem majorCtor_sound {natLit value tag fields}
    (accepted : majorCtor natLit value = some (tag, fields))
    (input : Nat → IxIR0.Value) :
    IxIR0.majorCtor natLit (value.instantiate input) =
      .ok (tag, fields.map (Value.instantiate input)) := by
  cases value <;> try simp [majorCtor] at accepted
  · rcases accepted with ⟨rfl, rfl⟩
    simp [Value.instantiate, IxIR0.majorCtor]
  · rename_i literal
    cases literal with
    | str _ => simp at accepted
    | nat n =>
      cases natLit <;> cases n <;> simp only [Bool.false_eq_true,
        ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at accepted
      all_goals try contradiction
      all_goals rcases accepted with ⟨rfl, rfl⟩
      all_goals simp [Value.instantiate, IxIR0.majorCtor]

private def SoundAt (fuel : Nat) : Prop :=
  (∀ ctx env expr value, eval ctx fuel env expr = some value → ∀ input,
    IxIR0.eval ctx fuel (env.map (Value.instantiate input)) expr = .ok (value.instantiate input)) ∧
  (∀ ctx fn arg value, apply ctx fuel fn arg = some value → ∀ input,
    IxIR0.apply ctx fuel (fn.instantiate input) (arg.instantiate input) = .ok (value.instantiate input)) ∧
  (∀ ctx head args value, saturate ctx fuel head args = some value → ∀ input,
    IxIR0.saturate ctx fuel head (args.map (Value.instantiate input)) = .ok (value.instantiate input)) ∧
  (∀ ctx head args value, fire ctx fuel head args = some value → ∀ input,
    IxIR0.fire ctx fuel head (args.map (Value.instantiate input)) = .ok (value.instantiate input))

private theorem soundAt : ∀ fuel, SoundAt fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ctx env expr value h; simp [eval] at h
    · intro ctx fn arg value h; simp [apply] at h
    · intro ctx head args value h; simp [saturate] at h
    · intro ctx head args value h; simp [fire] at h
  | succ fuel ih =>
    obtain ⟨ihE, ihA, ihS, ihF⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ctx env expr value h input
      cases expr with
      | var index =>
        simp only [eval] at h
        simp [IxIR0.eval, List.getElem?_map, h]
      | lit literal =>
        simp only [eval, Option.some.injEq] at h
        subst value
        simp [Value.instantiate, IxIR0.eval]
      | erased =>
        simp only [eval, Option.some.injEq] at h
        subst value
        simp [Value.instantiate, IxIR0.eval]
      | lam uses body =>
        simp only [eval, Option.some.injEq] at h
        subst value
        simp [Value.instantiate, IxIR0.eval]
      | letE uses expr body =>
        simp only [eval, Bind.bind, Option.bind_eq_some_iff] at h
        obtain ⟨bound, hv, hb⟩ := h
        simpa [IxIR0.eval, ihE _ _ _ _ hv input, Bind.bind, Except.bind] using ihE _ _ _ _ hb input
      | app fn arg =>
        simp only [eval, Bind.bind, Option.bind_eq_some_iff] at h
        obtain ⟨f, hf, a, ha, happ⟩ := h
        simpa [IxIR0.eval, ihE _ _ _ _ hf input, ihE _ _ _ _ ha input, Bind.bind, Except.bind] using
          ihA _ _ _ _ happ input
      | proj field expr =>
        simp only [eval, Bind.bind, Option.bind_eq_some_iff] at h
        obtain ⟨object, ho, hp⟩ := h
        have evaluated := ihE _ _ _ _ ho input
        cases object <;> simp [Value.instantiate] at evaluated
        all_goals simp only [IxIR0.eval, evaluated, Bind.bind, Except.bind]
        all_goals try simp at hp
        · simp [List.getElem?_map, hp]
        · subst value; simp [Value.instantiate]
      | ref address =>
        simp only [eval, Bind.bind, Option.bind_eq_some_iff] at h
        obtain ⟨decl, hd, hr⟩ := h
        cases decl with
        | defn uses body =>
          simpa [IxIR0.eval, hd] using ihE _ _ _ _ hr input
        | ctor tag arity =>
          simpa [IxIR0.eval, hd] using ihS _ _ _ _ hr input
        | recursor pre natLit rules =>
          simp only [Option.some.injEq] at hr
          subst value
          simp [IxIR0.eval, hd, Value.instantiate]
        | extern arity => simp at hr
    · intro ctx fn arg value h input
      cases fn <;> simp only [apply] at h
      all_goals try contradiction
      · simpa [IxIR0.apply, Value.instantiate] using ihE _ _ _ _ h input
      · simpa [IxIR0.apply, Value.instantiate, List.map_append] using ihS _ _ _ _ h input
      · simp only [Option.some.injEq] at h
        subst value
        simp [IxIR0.apply, Value.instantiate]
    · intro ctx head args value h input
      simp only [saturate] at h
      split at h
      · rename_i arity
        simpa [IxIR0.saturate, arity] using ihF _ _ _ _ h input
      · rename_i arity
        simp only [Option.some.injEq] at h
        subst value
        simp [IxIR0.saturate, arity, Value.instantiate]
    · intro ctx head args value h input
      cases head with
      | ctor address tag arity =>
        simp only [fire, Option.some.injEq] at h
        subst value
        simp [IxIR0.fire, Value.instantiate]
      | ext address arity => simp [fire] at h
      | rec_ address arity =>
        simp only [fire, Bind.bind, Option.bind_eq_some_iff] at h
        obtain ⟨decl, hd, h⟩ := h
        cases decl <;> try contradiction
        rename_i pre natLit rules
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨major, hm, pair, hc, rule, hr, h⟩ := h
        rcases pair with ⟨tag, fields⟩
        split at h
        · contradiction
        · rename_i fieldsEq
          have concreteMajor := majorCtor_sound hc input
          have last : (args.map (Value.instantiate input)).getLast? =
              some (major.instantiate input) := by
            simp [List.getLast?_map, hm]
          simpa [IxIR0.fire, hd, last, concreteMajor, hr, fieldsEq, Bind.bind, Except.bind,
            List.map_append, List.map_reverse, List.map_dropLast, Value.instantiate] using
            ihE _ _ _ _ h input

/-- Structural substitution theorem. The fuel bounds symbolic checking once;
the conclusion quantifies over every runtime value substitution. -/
theorem eval_sound {ctx fuel env expr value}
    (accepted : eval ctx fuel env expr = some value) (input : Nat → IxIR0.Value) :
    IxIR0.eval ctx fuel (env.map (Value.instantiate input)) expr = .ok (value.instantiate input) :=
  (soundAt fuel).1 _ _ _ _ accepted input

end Compilatrix.Ixby.SymbolicSource
