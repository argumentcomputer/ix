import Ix.Compiler.IxIR0.ProjectionSafe
import Ix.Compiler.IxIR0.ReaddressSim

/-!
# Projection-safe trace transport across IxIR₀ readdressing

Evaluator equivariance transports the observable `Except` result of a run.
The lowering progress proof consumes a stronger witness: the mutually
inductive `ProjectionSafe.Eval`/`Apply`/`Saturate`/`Fire` trace retaining every
dynamically entered body.  This module transports that witness structurally.

Unlike full evaluator equivalence, a successful trace only observes successful
declaration and oracle lookups.  `Ctx.TraceRenames` therefore states exactly
that one-way requirement.  In particular it relates the validator's literal
raw environment directly to the final addressed environment; no stable alias
has to be inserted on the proof-facing side.
-/

namespace Ix.Compiler.IxIR0.Readdress

open Ix.Compiler.Ixon (Address)

namespace Ctx

/-- One-way context compatibility sufficient to rename a successful
projection-safe trace. -/
structure TraceRenames (rename : Address → Address)
    (before after : IxIR0.Ctx) : Prop where
  env : ∀ {address declaration},
    before.env address = some declaration →
      after.env (rename address) =
        some (MutualBlock.Concrete.Decl.mapAddresses rename declaration)
  oracle : ∀ {address arguments result},
    before.oracle address arguments = some result →
      after.oracle (rename address)
          (ValueList.mapAddresses rename arguments) =
        some (Value.mapAddresses rename result)

/-- Exact evaluator-context renaming entails the one-way trace relation. -/
theorem Renames.toTraceRenames {rename : Address → Address}
    {before after : IxIR0.Ctx}
    (contexts : Renames rename before after) :
    TraceRenames rename before after := by
  constructor
  · intro address declaration hlookup
    rw [contexts.env address, hlookup]
    rfl
  · intro address arguments result horacle
    rw [contexts.oracle address arguments, horacle]
    rfl

end Ctx

namespace ProjectionSafe

mutual

  /-- Rename every address retained by an exact projection-safe evaluation
  trace. -/
  theorem Eval.mapAddresses {rename : Address → Address}
      {before after : IxIR0.Ctx}
      (contexts : Ctx.TraceRenames rename before after)
      {fuel : Nat} {environment : List Value} {expression : Expr}
      {result : Value}
      (trace : IxIR0.ProjectionSafe.Eval before fuel environment expression
        result) :
      IxIR0.ProjectionSafe.Eval after fuel
        (ValueList.mapAddresses rename environment)
        (MutualBlock.Concrete.Expr.mapAddresses rename expression)
        (Value.mapAddresses rename result) := by
    cases trace with
    | var hlookup =>
        simp only [MutualBlock.Concrete.Expr.mapAddresses]
        apply IxIR0.ProjectionSafe.Eval.var
        simpa using congrArg (Option.map (Value.mapAddresses rename)) hlookup
    | lit =>
        simp only [MutualBlock.Concrete.Expr.mapAddresses,
          Value.mapAddresses]
        exact .lit
    | erased =>
        simp only [MutualBlock.Concrete.Expr.mapAddresses,
          Value.mapAddresses]
        exact .erased
    | lam =>
        simp only [MutualBlock.Concrete.Expr.mapAddresses,
          Value.mapAddresses]
        exact .lam
    | letE hvalue hbody =>
        simp only [MutualBlock.Concrete.Expr.mapAddresses]
        exact .letE (Eval.mapAddresses contexts hvalue)
          (by simpa using Eval.mapAddresses contexts hbody)
    | app hfunction hargument happly =>
        simp only [MutualBlock.Concrete.Expr.mapAddresses]
        exact .app (Eval.mapAddresses contexts hfunction)
          (Eval.mapAddresses contexts hargument)
          (Apply.mapAddresses contexts happly)
    | proj hsource hfield =>
        simp only [MutualBlock.Concrete.Expr.mapAddresses]
        have hsource' := Eval.mapAddresses contexts hsource
        simp only [Value.mapAddresses] at hsource'
        apply IxIR0.ProjectionSafe.Eval.proj hsource'
        simpa using congrArg (Option.map (Value.mapAddresses rename)) hfield
    | refDefn hlookup hbody =>
        simp only [MutualBlock.Concrete.Expr.mapAddresses]
        exact .refDefn
          (by simpa [MutualBlock.Concrete.Decl.mapAddresses] using
            contexts.env hlookup)
          (by simpa using Eval.mapAddresses contexts hbody)
    | refCtor hlookup hsaturate =>
        simp only [MutualBlock.Concrete.Expr.mapAddresses]
        exact .refCtor
          (by simpa [MutualBlock.Concrete.Decl.mapAddresses] using
            contexts.env hlookup)
          (by simpa [Head.mapAddresses, ValueList.mapAddresses] using
            Saturate.mapAddresses contexts hsaturate)
    | refRecursor hlookup =>
        simp only [MutualBlock.Concrete.Expr.mapAddresses,
          Value.mapAddresses, Head.mapAddresses, ValueList.mapAddresses]
        exact .refRecursor
          (by simpa [MutualBlock.Concrete.Decl.mapAddresses] using
            contexts.env hlookup)
    | refExtern hlookup hsaturate =>
        simp only [MutualBlock.Concrete.Expr.mapAddresses]
        exact .refExtern
          (by simpa [MutualBlock.Concrete.Decl.mapAddresses] using
            contexts.env hlookup)
          (by simpa [Head.mapAddresses, ValueList.mapAddresses] using
            Saturate.mapAddresses contexts hsaturate)

  /-- Rename every address retained by an exact projection-safe application
  trace. -/
  theorem Apply.mapAddresses {rename : Address → Address}
      {before after : IxIR0.Ctx}
      (contexts : Ctx.TraceRenames rename before after)
      {fuel : Nat} {function argument result : Value}
      (trace : IxIR0.ProjectionSafe.Apply before fuel function argument
        result) :
      IxIR0.ProjectionSafe.Apply after fuel
        (Value.mapAddresses rename function)
        (Value.mapAddresses rename argument)
        (Value.mapAddresses rename result) := by
    cases trace with
    | clos hbody =>
        simp only [Value.mapAddresses]
        exact .clos (by simpa using Eval.mapAddresses contexts hbody)
    | pap hsaturate =>
        simp only [Value.mapAddresses]
        exact .pap (by simpa using Saturate.mapAddresses contexts hsaturate)
    | erased =>
        simp only [Value.mapAddresses]
        exact .erased

  /-- Rename every address retained by an exact projection-safe saturation
  trace. -/
  theorem Saturate.mapAddresses {rename : Address → Address}
      {before after : IxIR0.Ctx}
      (contexts : Ctx.TraceRenames rename before after)
      {fuel : Nat} {head : Head} {arguments : List Value} {result : Value}
      (trace : IxIR0.ProjectionSafe.Saturate before fuel head arguments
        result) :
      IxIR0.ProjectionSafe.Saturate after fuel
        (Head.mapAddresses rename head)
        (ValueList.mapAddresses rename arguments)
        (Value.mapAddresses rename result) := by
    cases trace with
    | pending hlength =>
        simp only [Value.mapAddresses]
        exact .pending (by simpa using hlength)
    | full hlength hfire =>
        exact .full (by simpa using hlength)
          (Fire.mapAddresses contexts hfire)

  /-- Rename every address retained by an exact projection-safe firing
  trace. -/
  theorem Fire.mapAddresses {rename : Address → Address}
      {before after : IxIR0.Ctx}
      (contexts : Ctx.TraceRenames rename before after)
      {fuel : Nat} {head : Head} {arguments : List Value} {result : Value}
      (trace : IxIR0.ProjectionSafe.Fire before fuel head arguments result) :
      IxIR0.ProjectionSafe.Fire after fuel
        (Head.mapAddresses rename head)
        (ValueList.mapAddresses rename arguments)
        (Value.mapAddresses rename result) := by
    cases trace with
    | ctor =>
        simp only [Head.mapAddresses, Value.mapAddresses]
        exact .ctor
    | extern horacle => exact .extern (contexts.oracle horacle)
    | @recursor fuel address arity numArgs natLit rules arguments major tag
        fields rule result hlookup hlast hmajor hrule hfields hbody =>
        apply IxIR0.ProjectionSafe.Fire.recursor (contexts.env hlookup)
        · simpa using congrArg (Option.map (Value.mapAddresses rename)) hlast
        · simpa [mapMajorResult] using
            congrArg (mapMajorResult rename) hmajor
        · simpa using congrArg
            (Option.map (MutualBlock.Concrete.RecRule.mapAddresses rename))
            hrule
        · simpa [MutualBlock.Concrete.RecRule.mapAddresses] using hfields
        · simpa [MutualBlock.Concrete.RecRule.mapAddresses,
            Value.mapAddresses, Head.mapAddresses] using
            Eval.mapAddresses contexts hbody

end

/-- Transport a bounded safe application spine pointwise. -/
theorem AppliesBelow.mapAddresses {rename : Address → Address}
    {before after : IxIR0.Ctx}
    (contexts : Ctx.TraceRenames rename before after)
    {limit : Nat} {function result : Value} {arguments : List Value}
    (trace : IxIR0.ProjectionSafe.AppliesBelow before limit function
      arguments result) :
    IxIR0.ProjectionSafe.AppliesBelow after limit
      (Value.mapAddresses rename function)
      (ValueList.mapAddresses rename arguments)
      (Value.mapAddresses rename result) := by
  exact IxIR0.ProjectionSafe.AppliesBelow.traverse
    (Result := fun currentFunction currentArguments currentResult =>
      IxIR0.ProjectionSafe.AppliesBelow after limit
        (Value.mapAddresses rename currentFunction)
        (ValueList.mapAddresses rename currentArguments)
        (Value.mapAddresses rename currentResult))
    (hnil := by
      intro value
      simp only [ValueList.mapAddresses]
      exact .nil)
    (hcons := by
      intro currentFunction argument currentMiddle currentResult
        currentArguments fuel hfuel hstep htail ih
      simpa only [ValueList.mapAddresses] using
        IxIR0.ProjectionSafe.AppliesBelow.cons hfuel
          (Apply.mapAddresses contexts hstep) ih)
    trace

/-- Transport pointwise bounded argument-evaluation traces. -/
theorem EvalsBelow.mapAddresses {rename : Address → Address}
    {before after : IxIR0.Ctx}
    (contexts : Ctx.TraceRenames rename before after)
    {limit : Nat} {environment : List Value}
    {expressions : List Expr} {values : List Value}
    (trace : IxIR0.ProjectionSafe.EvalsBelow before limit environment
      expressions values) :
    IxIR0.ProjectionSafe.EvalsBelow after limit
      (ValueList.mapAddresses rename environment)
      (expressions.map (MutualBlock.Concrete.Expr.mapAddresses rename))
      (ValueList.mapAddresses rename values) := by
  exact IxIR0.ProjectionSafe.EvalsBelow.traverse
    (Result := fun currentExpressions currentValues =>
      IxIR0.ProjectionSafe.EvalsBelow after limit
        (ValueList.mapAddresses rename environment)
        (currentExpressions.map
          (MutualBlock.Concrete.Expr.mapAddresses rename))
        (ValueList.mapAddresses rename currentValues))
    (hnil := by
      simp only [List.map, ValueList.mapAddresses]
      exact .nil)
    (hcons := by
      intro fuel expr value currentExpressions currentValues hfuel heval
        htail ih
      simpa only [List.map, ValueList.mapAddresses] using
        IxIR0.ProjectionSafe.EvalsBelow.cons hfuel
          (Eval.mapAddresses contexts heval) ih)
    trace

/-- Transport a flattened call-aware expression spine. -/
theorem Spine.mapAddresses {rename : Address → Address}
    {before after : IxIR0.Ctx}
    (contexts : Ctx.TraceRenames rename before after)
    {limit : Nat} {environment : List Value}
    {head : Expr} {arguments : List Expr} {result : Value}
    (trace : IxIR0.ProjectionSafe.Spine before limit environment head
      arguments result) :
    IxIR0.ProjectionSafe.Spine after limit
      (ValueList.mapAddresses rename environment)
      (MutualBlock.Concrete.Expr.mapAddresses rename head)
      (arguments.map (MutualBlock.Concrete.Expr.mapAddresses rename))
      (Value.mapAddresses rename result) := by
  cases trace with
  | intro hbound hhead harguments happlies =>
      exact .intro hbound (Eval.mapAddresses contexts hhead)
        (EvalsBelow.mapAddresses contexts harguments)
        (AppliesBelow.mapAddresses contexts happlies)

/-- Fuel-free projection-safe termination is invariant under a trace
renaming. -/
theorem Terminates.mapAddresses {rename : Address → Address}
    {before after : IxIR0.Ctx}
    (contexts : Ctx.TraceRenames rename before after)
    {environment : List Value} {expression : Expr} {result : Value}
    (trace : IxIR0.ProjectionSafe.Terminates before environment expression
      result) :
    IxIR0.ProjectionSafe.Terminates after
      (ValueList.mapAddresses rename environment)
      (MutualBlock.Concrete.Expr.mapAddresses rename expression)
      (Value.mapAddresses rename result) := by
  obtain ⟨fuel, trace⟩ := trace
  exact ⟨fuel, Eval.mapAddresses contexts trace⟩

end ProjectionSafe

namespace Result

/-- Literal proof-facing context emitted by the legacy eraser, with no
derived-key aliases. -/
def rawCtx (_result : Result) (groups : List Group)
    (oracle : Oracle := fun _ _ => none) : IxIR0.Ctx :=
  { env := Env.ofList (rawDeclarations groups), oracle }

/-- A successful whole-program audit relates the literal raw environment
directly to the emitted addressed environment for every successful lookup. -/
theorem traceRenames_rawCtx {result : Result}
    {reserved : List Address} {groups : List Group} {main : Expr}
    (haudit : result.semanticAudit reserved groups main = true)
    (beforeOracle afterOracle : Oracle)
    (horacle : ∀ address arguments,
      afterOracle
          (MutualBlock.Renaming.apply result.addressMap address)
          (ValueList.mapAddresses
            (MutualBlock.Renaming.apply result.addressMap) arguments) =
        (beforeOracle address arguments).map
          (Value.mapAddresses
            (MutualBlock.Renaming.apply result.addressMap))) :
    Ctx.TraceRenames (MutualBlock.Renaming.apply result.addressMap)
      (result.rawCtx groups beforeOracle)
      (result.addressedCtx afterOracle) := by
  constructor
  · intro address declaration hlookup
    change Env.ofList (rawDeclarations groups) address = some declaration at hlookup
    change Env.ofList result.declarations
      (MutualBlock.Renaming.apply result.addressMap address) = _
    exact result.lookup_eq_mapAddresses haudit hlookup
  · intro address arguments value hlookup
    change beforeOracle address arguments = some value at hlookup
    change afterOracle
      (MutualBlock.Renaming.apply result.addressMap address)
      (ValueList.mapAddresses
        (MutualBlock.Renaming.apply result.addressMap) arguments) = _
    rw [horacle address arguments, hlookup]
    rfl

/-- The exact call-aware trace consumed by lowering progress survives a
successful whole-program readdressing. -/
theorem projectionSafeEval_of_audit {result : Result}
    {reserved : List Address} {groups : List Group} {main : Expr}
    (haudit : result.semanticAudit reserved groups main = true)
    (beforeOracle afterOracle : Oracle)
    (horacle : ∀ address arguments,
      afterOracle
          (MutualBlock.Renaming.apply result.addressMap address)
          (ValueList.mapAddresses
            (MutualBlock.Renaming.apply result.addressMap) arguments) =
        (beforeOracle address arguments).map
          (Value.mapAddresses
            (MutualBlock.Renaming.apply result.addressMap)))
    {traceFuel : Nat} {environment : List Value} {expression : Expr}
    {value : Value}
    (trace : IxIR0.ProjectionSafe.Eval
      (result.rawCtx groups beforeOracle) traceFuel environment expression
      value) :
    IxIR0.ProjectionSafe.Eval (result.addressedCtx afterOracle) traceFuel
      (ValueList.mapAddresses
        (MutualBlock.Renaming.apply result.addressMap) environment)
      (MutualBlock.Concrete.Expr.mapAddresses
        (MutualBlock.Renaming.apply result.addressMap) expression)
      (Value.mapAddresses
        (MutualBlock.Renaming.apply result.addressMap) value) :=
  ProjectionSafe.Eval.mapAddresses
    (result.traceRenames_rawCtx haudit beforeOracle afterOracle horacle)
    trace

/-- Closed main specialization, rewriting the structural image to the exact
main retained by the addressed result. -/
theorem projectionSafeMain_of_audit {result : Result}
    {reserved : List Address} {groups : List Group} {main : Expr}
    (haudit : result.semanticAudit reserved groups main = true)
    (beforeOracle afterOracle : Oracle)
    (horacle : ∀ address arguments,
      afterOracle
          (MutualBlock.Renaming.apply result.addressMap address)
          (ValueList.mapAddresses
            (MutualBlock.Renaming.apply result.addressMap) arguments) =
        (beforeOracle address arguments).map
          (Value.mapAddresses
            (MutualBlock.Renaming.apply result.addressMap)))
    {traceFuel : Nat} {value : Value}
    (trace : IxIR0.ProjectionSafe.Eval
      (result.rawCtx groups beforeOracle) traceFuel [] main value) :
    IxIR0.ProjectionSafe.Eval (result.addressedCtx afterOracle) traceFuel []
      result.main
      (Value.mapAddresses
        (MutualBlock.Renaming.apply result.addressMap) value) := by
  rw [result.main_eq_mapAddresses haudit]
  simpa using result.projectionSafeEval_of_audit haudit beforeOracle
    afterOracle horacle trace

end Result

end Ix.Compiler.IxIR0.Readdress
