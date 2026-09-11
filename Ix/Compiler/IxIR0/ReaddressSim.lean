import Ix.Compiler.IxIR0.Eval
import Ix.Compiler.IxIR0.Readdress

/-!
# Semantic transport for IxIR₀ address renaming

Cycle-safe mutual blocks replace transient declaration keys with keys derived
from the canonical symbolic block.  IxIR₀ runtime values retain global
addresses in constructors, partial applications, closures, and errors, so the
semantic statement maps the entire evaluator state rather than only source
expressions.

`Ctx.Renames` isolates the two assumptions the evaluator needs: exact forward
declaration lookup and an oracle that commutes with the same structural map.
The concrete theorem at the end obtains the declaration half directly from a
successful whole-program readdressing audit.
-/

namespace Ix.Compiler.IxIR0

open Ix.Compiler.Ixon (Address)

namespace Readdress

namespace Head

/-- Rename every declaration identity retained by a global head. -/
def mapAddresses (rename : Address → Address) : Head → Head
  | .ctor address tag arity => .ctor (rename address) tag arity
  | .rec_ address arity => .rec_ (rename address) arity
  | .ext address arity => .ext (rename address) arity

end Head

/-! Values and value lists are mutually recursive because closures and
constructor/PAP payloads contain further values. -/

mutual

/-- Structural address action on an IxIR₀ runtime value. -/
def Value.mapAddresses (rename : Address → Address) (value : Value) : Value :=
  match value with
  | .clos uses environment body =>
      .clos uses (ValueList.mapAddresses rename environment)
        (MutualBlock.Concrete.Expr.mapAddresses rename body)
  | .pap head arguments =>
      .pap (Head.mapAddresses rename head)
        (ValueList.mapAddresses rename arguments)
  | .ctor address tag arguments =>
      .ctor (rename address) tag (ValueList.mapAddresses rename arguments)
  | .lit literal => .lit literal
  | .erased => .erased
termination_by sizeOf value

/-- Structural address action on a runtime environment or argument list. -/
def ValueList.mapAddresses (rename : Address → Address)
    (values : List Value) : List Value :=
  match values with
  | [] => []
  | value :: rest =>
      Value.mapAddresses rename value :: ValueList.mapAddresses rename rest
termination_by sizeOf values

end

namespace Err

/-- Rename the address payload of evaluator failures. -/
def mapAddresses (rename : Address → Address) : Err → Err
  | .fuel => .fuel
  | .stuck message => .stuck message
  | .oracleMissing address => .oracleMissing (rename address)
  | .unknownRef address => .unknownRef (rename address)

end Err

/-- Structural address action on an evaluator result. -/
def mapResult (rename : Address → Address) :
    Except Err Value → Except Err Value
  | .ok value => .ok (Value.mapAddresses rename value)
  | .error error => .error (Err.mapAddresses rename error)

/-- Structural address action on the result of viewing a recursor major. -/
def mapMajorResult (rename : Address → Address) :
    Except Err (Nat × List Value) → Except Err (Nat × List Value)
  | .ok (tag, fields) => .ok (tag, ValueList.mapAddresses rename fields)
  | .error error => .error (Err.mapAddresses rename error)

namespace Ctx

/-- Exact evaluator-context compatibility for an address renaming. -/
structure Renames (rename : Address → Address)
    (before after : Ctx) : Prop where
  env : ∀ address,
    after.env (rename address) =
      (before.env address).map
        (MutualBlock.Concrete.Decl.mapAddresses rename)
  oracle : ∀ address arguments,
    after.oracle (rename address)
        (ValueList.mapAddresses rename arguments) =
      (before.oracle address arguments).map
        (Value.mapAddresses rename)

end Ctx

/-! ## Structural laws used by evaluator transport -/

@[simp] theorem Head.arity_mapAddresses (rename : Address → Address)
    (head : Head) :
    (Head.mapAddresses rename head).arity = head.arity := by
  cases head <;> rfl

@[simp] theorem ValueList.mapAddresses_nil (rename : Address → Address) :
    ValueList.mapAddresses rename [] = [] := by
  simp [ValueList.mapAddresses]

@[simp] theorem ValueList.mapAddresses_cons (rename : Address → Address)
    (value : Value) (rest : List Value) :
    ValueList.mapAddresses rename (value :: rest) =
      Value.mapAddresses rename value :: ValueList.mapAddresses rename rest :=
  by simp [ValueList.mapAddresses]

@[simp] theorem ValueList.mapAddresses_eq_map (rename : Address → Address)
    (values : List Value) :
    ValueList.mapAddresses rename values =
      values.map (Value.mapAddresses rename) := by
  induction values with
  | nil => simp
  | cons value rest ih => simp [ih]

@[simp] theorem ValueList.length_mapAddresses (rename : Address → Address)
    (values : List Value) :
    (ValueList.mapAddresses rename values).length = values.length := by
  simp [ValueList.mapAddresses_eq_map]

@[simp] theorem ValueList.mapAddresses_append (rename : Address → Address)
    (left right : List Value) :
    ValueList.mapAddresses rename (left ++ right) =
      ValueList.mapAddresses rename left ++
        ValueList.mapAddresses rename right := by
  simp [ValueList.mapAddresses_eq_map]

@[simp] theorem ValueList.mapAddresses_reverse (rename : Address → Address)
    (values : List Value) :
    ValueList.mapAddresses rename values.reverse =
      (ValueList.mapAddresses rename values).reverse := by
  simp [ValueList.mapAddresses_eq_map]

@[simp] theorem ValueList.mapAddresses_dropLast
    (rename : Address → Address) (values : List Value) :
    ValueList.mapAddresses rename values.dropLast =
      (ValueList.mapAddresses rename values).dropLast := by
  simp [ValueList.mapAddresses_eq_map]

@[simp] theorem ValueList.getElem?_mapAddresses
    (rename : Address → Address) (values : List Value) (index : Nat) :
    (ValueList.mapAddresses rename values)[index]? =
      (values[index]?).map (Value.mapAddresses rename) := by
  simp [ValueList.mapAddresses_eq_map]

@[simp] theorem ValueList.getLast?_mapAddresses
    (rename : Address → Address) (values : List Value) :
    (ValueList.mapAddresses rename values).getLast? =
      values.getLast?.map (Value.mapAddresses rename) := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      cases rest with
      | nil => simp
      | cons next tail => simpa using ih

@[simp] theorem majorCtor_mapAddresses (rename : Address → Address)
    (natLit : Bool) (value : Value) :
    majorCtor natLit (Value.mapAddresses rename value) =
      mapMajorResult rename (majorCtor natLit value) := by
  cases value with
  | clos uses environment body => simp [Value.mapAddresses, majorCtor,
      mapMajorResult, Err.mapAddresses]
  | pap head arguments => simp [Value.mapAddresses, majorCtor,
      mapMajorResult, Err.mapAddresses]
  | ctor address tag arguments =>
      simp [Value.mapAddresses, majorCtor, mapMajorResult]
  | lit literal =>
      cases literal with
      | str string => simp [Value.mapAddresses, majorCtor, mapMajorResult,
          Err.mapAddresses]
      | nat number =>
          cases natLit <;> cases number <;>
            simp [Value.mapAddresses, majorCtor, mapMajorResult,
              Err.mapAddresses]
  | erased => simp [Value.mapAddresses, majorCtor, mapMajorResult,
      Err.mapAddresses]

@[simp] theorem mapResult_ok (rename : Address → Address) (value : Value) :
    mapResult rename (.ok value) = .ok (Value.mapAddresses rename value) := rfl

@[simp] theorem mapResult_error (rename : Address → Address) (error : Err) :
    mapResult rename (.error error) = .error (Err.mapAddresses rename error) :=
  rfl

@[simp] theorem Err.mapAddresses_fuel (rename : Address → Address) :
    Err.mapAddresses rename .fuel = .fuel := rfl

@[simp] theorem Err.mapAddresses_stuck (rename : Address → Address)
    (message : String) :
    Err.mapAddresses rename (.stuck message) = .stuck message := rfl

@[simp] theorem Err.mapAddresses_oracleMissing
    (rename : Address → Address) (address : Address) :
    Err.mapAddresses rename (.oracleMissing address) =
      .oracleMissing (rename address) := rfl

@[simp] theorem Err.mapAddresses_unknownRef
    (rename : Address → Address) (address : Address) :
    Err.mapAddresses rename (.unknownRef address) =
      .unknownRef (rename address) := rfl

@[simp] private theorem except_ok_bind {Error Value Result : Type}
    (value : Value) (next : Value → Except Error Result) :
    (Except.ok value >>= next) = next value := rfl

@[simp] private theorem except_error_bind {Error Value Result : Type}
    (error : Error) (next : Value → Except Error Result) :
    (Except.error error >>= next) = Except.error error := rfl

/-! ## Fueled evaluator equivariance -/

/-- All four mutually recursive evaluator entries commute with an address map
at one common fuel index. -/
structure EvalTransportAt (rename : Address → Address)
    (before after : Ctx) (fuel : Nat) : Prop where
  eval : ∀ (environment : List Value) (expression : Expr),
    IxIR0.eval after fuel (ValueList.mapAddresses rename environment)
        (MutualBlock.Concrete.Expr.mapAddresses rename expression) =
      mapResult rename (IxIR0.eval before fuel environment expression)
  applyValue : ∀ (function argument : Value),
    IxIR0.apply after fuel (Value.mapAddresses rename function)
        (Value.mapAddresses rename argument) =
      mapResult rename (IxIR0.apply before fuel function argument)
  saturate : ∀ (head : Head) (arguments : List Value),
    IxIR0.saturate after fuel (Head.mapAddresses rename head)
        (ValueList.mapAddresses rename arguments) =
      mapResult rename (IxIR0.saturate before fuel head arguments)
  fire : ∀ (head : Head) (arguments : List Value),
    IxIR0.fire after fuel (Head.mapAddresses rename head)
        (ValueList.mapAddresses rename arguments) =
      mapResult rename (IxIR0.fire before fuel head arguments)

/-- Exact evaluator equivariance at every fuel. -/
theorem evalTransportAt {rename : Address → Address} {before after : Ctx}
    (contexts : Ctx.Renames rename before after) :
    ∀ fuel, EvalTransportAt rename before after fuel := by
  intro fuel
  induction fuel with
  | zero =>
      constructor <;> intros <;>
        simp [IxIR0.eval, IxIR0.apply, IxIR0.saturate, IxIR0.fire,
          mapResult, Err.mapAddresses]
  | succ fuel smaller =>
      refine {
        eval := ?_
        applyValue := ?_
        saturate := ?_
        fire := ?_ }
      · intro environment expression
        cases expression with
        | var index =>
            cases hlookup : environment[index]? with
            | none =>
                simp [IxIR0.eval,
                  MutualBlock.Concrete.Expr.mapAddresses, hlookup,
                  mapResult, Err.mapAddresses]
            | some value =>
                simp [IxIR0.eval,
                  MutualBlock.Concrete.Expr.mapAddresses, hlookup,
                  mapResult]
        | ref address =>
            simp only [IxIR0.eval,
              MutualBlock.Concrete.Expr.mapAddresses, contexts.env address]
            cases hdeclaration : before.env address with
            | none => simp [mapResult, Err.mapAddresses]
            | some declaration =>
                simp only [Option.map_some]
                cases declaration with
                | defn result body =>
                    simpa [MutualBlock.Concrete.Decl.mapAddresses] using
                      smaller.eval [] body
                | ctor tag arity =>
                    simpa [MutualBlock.Concrete.Decl.mapAddresses,
                      Head.mapAddresses] using
                      smaller.saturate (.ctor address tag arity) []
                | recursor numArgs natLit rules =>
                    simp [MutualBlock.Concrete.Decl.mapAddresses,
                      Value.mapAddresses, Head.mapAddresses, mapResult]
                | extern arity =>
                    simpa [MutualBlock.Concrete.Decl.mapAddresses,
                      Head.mapAddresses] using
                      smaller.saturate (.ext address arity) []
        | app function argument =>
            simp only [IxIR0.eval,
              MutualBlock.Concrete.Expr.mapAddresses]
            rw [smaller.eval environment function]
            cases hfunction : IxIR0.eval before fuel environment function with
            | error error => simp [mapResult]
            | ok functionValue =>
                simp only [mapResult, except_ok_bind]
                rw [smaller.eval environment argument]
                cases hargument : IxIR0.eval before fuel environment argument with
                | error error => simp [mapResult]
                | ok argumentValue =>
                    simp only [mapResult, except_ok_bind]
                    exact smaller.applyValue functionValue argumentValue
        | lam uses body =>
            simp [IxIR0.eval, MutualBlock.Concrete.Expr.mapAddresses,
              Value.mapAddresses, mapResult]
        | letE uses value body =>
            simp only [IxIR0.eval,
              MutualBlock.Concrete.Expr.mapAddresses]
            rw [smaller.eval environment value]
            cases hvalue : IxIR0.eval before fuel environment value with
            | error error => simp [mapResult]
            | ok result =>
                simp only [mapResult, except_ok_bind]
                simpa only [ValueList.mapAddresses_cons, mapResult] using
                  smaller.eval (result :: environment) body
        | proj index struct =>
            simp only [IxIR0.eval,
              MutualBlock.Concrete.Expr.mapAddresses]
            rw [smaller.eval environment struct]
            cases hstruct : IxIR0.eval before fuel environment struct with
            | error error => simp [mapResult]
            | ok value =>
                simp only [mapResult, except_ok_bind]
                cases value with
                | clos uses captured body =>
                    simp [Value.mapAddresses, Err.mapAddresses]
                | pap head arguments =>
                    simp [Value.mapAddresses, Err.mapAddresses]
                | ctor address tag arguments =>
                    cases hfield : arguments[index]? with
                    | none =>
                        simp [Value.mapAddresses, hfield,
                          Err.mapAddresses]
                    | some field =>
                        simp [Value.mapAddresses, hfield]
                | lit literal =>
                    simp [Value.mapAddresses, Err.mapAddresses]
                | erased => simp [Value.mapAddresses]
        | lit literal =>
            simp [IxIR0.eval, MutualBlock.Concrete.Expr.mapAddresses,
              Value.mapAddresses, mapResult]
        | erased =>
            simp [IxIR0.eval, MutualBlock.Concrete.Expr.mapAddresses,
              Value.mapAddresses, mapResult]
      · intro function argument
        cases function with
        | clos uses environment body =>
            simpa [IxIR0.apply, Value.mapAddresses] using
              smaller.eval (argument :: environment) body
        | pap head arguments =>
            simpa [IxIR0.apply, Value.mapAddresses] using
              smaller.saturate head (arguments ++ [argument])
        | ctor address tag arguments =>
            simp [IxIR0.apply, Value.mapAddresses, mapResult,
              Err.mapAddresses]
        | lit literal =>
            simp [IxIR0.apply, Value.mapAddresses, mapResult,
              Err.mapAddresses]
        | erased => simp [IxIR0.apply, Value.mapAddresses, mapResult]
      · intro head arguments
        simp only [IxIR0.saturate, Head.arity_mapAddresses,
          ValueList.length_mapAddresses]
        split
        · exact smaller.fire head arguments
        · simp [Value.mapAddresses, mapResult]
      · intro head arguments
        cases head with
        | ctor address tag arity =>
            simp [IxIR0.fire, Head.mapAddresses, Value.mapAddresses,
              mapResult]
        | ext address arity =>
            simp only [IxIR0.fire, Head.mapAddresses,
              contexts.oracle address arguments]
            cases horacle : before.oracle address arguments with
            | none => simp [mapResult, Err.mapAddresses]
            | some value => simp [mapResult]
        | rec_ address arity =>
            simp only [IxIR0.fire, Head.mapAddresses, contexts.env address]
            cases hdeclaration : before.env address with
            | none => simp [mapResult, Err.mapAddresses]
            | some declaration =>
                simp only [Option.map_some]
                cases declaration with
                | defn result body =>
                    simp [MutualBlock.Concrete.Decl.mapAddresses,
                      mapResult, Err.mapAddresses]
                | ctor tag declarationArity =>
                    simp [MutualBlock.Concrete.Decl.mapAddresses,
                      mapResult, Err.mapAddresses]
                | extern declarationArity =>
                    simp [MutualBlock.Concrete.Decl.mapAddresses,
                      mapResult, Err.mapAddresses]
                | recursor numArgs natLit rules =>
                    simp only [MutualBlock.Concrete.Decl.mapAddresses,
                      ValueList.getLast?_mapAddresses]
                    cases hlast : arguments.getLast? with
                    | none =>
                        simp [mapResult, Err.mapAddresses]
                    | some major =>
                        simp only [Option.map_some]
                        rw [majorCtor_mapAddresses]
                        cases hmajor : majorCtor natLit major with
                        | error error =>
                            simp [mapMajorResult, mapResult]
                        | ok taggedFields =>
                            rcases taggedFields with ⟨tag, fields⟩
                            simp only [mapMajorResult,
                              except_ok_bind, Array.getElem?_map]
                            cases hrule : rules[tag]? with
                            | none =>
                                simp [mapResult, Err.mapAddresses]
                            | some rule =>
                                simp only [Option.map_some,
                                  MutualBlock.Concrete.RecRule.mapAddresses]
                                by_cases hfields : fields.length != rule.fields
                                · simp [hfields, mapResult, Err.mapAddresses]
                                · have heq : fields.length = rule.fields := by
                                    simpa using hfields
                                  simp only [ValueList.length_mapAddresses]
                                  simp only [heq, bne_self_eq_false,
                                    Bool.false_eq_true, if_false]
                                  have henvironment :
                                      ValueList.mapAddresses rename
                                          (fields.reverse ++
                                            arguments.dropLast.reverse ++
                                            [.pap (.rec_ address arity) []]) =
                                        (ValueList.mapAddresses rename fields).reverse ++
                                          (ValueList.mapAddresses rename arguments).dropLast.reverse ++
                                          [.pap (.rec_ (rename address) arity) []] := by
                                    simp [Value.mapAddresses,
                                      Head.mapAddresses]
                                  rw [← henvironment]
                                  exact smaller.eval
                                    (fields.reverse ++
                                      arguments.dropLast.reverse ++
                                      [.pap (.rec_ address arity) []])
                                    rule.rhs

/-! ## Public evaluator transport interface -/

/-- Expression evaluation is equivariant under every compatible context
renaming. -/
theorem eval_mapAddresses {rename : Address → Address}
    {before after : Ctx} (contexts : Ctx.Renames rename before after)
    (fuel : Nat) (environment : List Value) (expression : Expr) :
    IxIR0.eval after fuel (ValueList.mapAddresses rename environment)
        (MutualBlock.Concrete.Expr.mapAddresses rename expression) =
      mapResult rename (IxIR0.eval before fuel environment expression) :=
  (evalTransportAt contexts fuel).eval environment expression

/-- Closed evaluation is the structural address image of source evaluation. -/
theorem Ctx.run_mapAddresses {rename : Address → Address}
    {before after : Ctx} (contexts : Ctx.Renames rename before after)
    (expression : Expr) (fuel : Nat := 100000) :
    after.run (MutualBlock.Concrete.Expr.mapAddresses rename expression) fuel =
      mapResult rename (before.run expression fuel) := by
  simpa [Ctx.run] using eval_mapAddresses contexts fuel [] expression

/-! ## Certified whole-program readdressing contexts -/

private theorem envOfList_some_mem
    {entries : List (Address × Decl)} {address : Address}
    {declaration : Decl}
    (hlookup : Env.ofList entries address = some declaration) :
    (address, declaration) ∈ entries := by
  unfold Env.ofList at hlookup
  obtain ⟨entry, hfind, hvalue⟩ := Option.map_eq_some_iff.mp hlookup
  rcases entry with ⟨entryAddress, entryDeclaration⟩
  have hbeq : entryAddress == address :=
    List.find?_some
      (p := fun entry : Address × Decl => entry.1 == address) hfind
  have haddress : entryAddress = address := Address.eq_of_beq hbeq
  have hdeclaration : entryDeclaration = declaration := by
    simpa using hvalue
  subst entryAddress
  subst entryDeclaration
  exact List.mem_of_find?_eq_some hfind

/-- The audited main is exactly the address-map image of the raw main. -/
theorem Result.main_eq_mapAddresses {result : Result}
    {reserved : List Address} {groups : List Group} {main : Expr}
    (haudit : result.semanticAudit reserved groups main = true) :
    result.main =
      MutualBlock.Concrete.Expr.mapAddresses
        (MutualBlock.Renaming.apply result.addressMap) main := by
  simp only [Result.semanticAudit, Bool.and_eq_true] at haudit
  have himage : result.imageAudit groups main = true := haudit.1.1.1
  simp only [Result.imageAudit, Bool.and_eq_true] at himage
  exact (beq_iff_eq).mp himage.2

/-- Every successful raw environment lookup has the certified renamed lookup
in the emitted environment. -/
theorem Result.lookup_eq_mapAddresses {result : Result}
    {reserved : List Address} {groups : List Group} {main : Expr}
    (haudit : result.semanticAudit reserved groups main = true)
    {address : Address} {declaration : Decl}
    (hlookup : Env.ofList (rawDeclarations groups) address =
      some declaration) :
    Env.ofList result.declarations
        (MutualBlock.Renaming.apply result.addressMap address) =
      some (MutualBlock.Concrete.Decl.mapAddresses
        (MutualBlock.Renaming.apply result.addressMap) declaration) := by
  simp only [Result.semanticAudit, Bool.and_eq_true] at haudit
  have hmember : (address, declaration) ∈ rawDeclarations groups :=
    envOfList_some_mem hlookup
  have hlookupAudit : result.lookupAudit groups = true := haudit.1.2
  simp only [Result.lookupAudit] at hlookupAudit
  have hentry := (List.all_eq_true.mp hlookupAudit)
    (address, declaration) hmember
  cases hemitted : Env.ofList result.declarations
      (MutualBlock.Renaming.apply result.addressMap address) with
  | none => simp [hlookup, hemitted] at hentry
  | some emitted =>
      have hequal : emitted =
          MutualBlock.Concrete.Decl.mapAddresses
            (MutualBlock.Renaming.apply result.addressMap) declaration :=
        (beq_iff_eq).mp (by simpa [hlookup, hemitted] using hentry)
      simp [hequal]

/-- Every successful emitted lookup is already a fixed point of the completed
address map. -/
theorem Result.lookup_stable {result : Result}
    {reserved : List Address} {groups : List Group} {main : Expr}
    (haudit : result.semanticAudit reserved groups main = true)
    {address : Address} {declaration : Decl}
    (hlookup : Env.ofList result.declarations address = some declaration) :
    MutualBlock.Concrete.Decl.mapAddresses
        (MutualBlock.Renaming.apply result.addressMap) declaration =
      declaration := by
  simp only [Result.semanticAudit, Bool.and_eq_true] at haudit
  have hmember : (address, declaration) ∈ result.declarations :=
    envOfList_some_mem hlookup
  have hstableAudit : result.stableLookupAudit = true := haudit.2
  simp only [Result.stableLookupAudit] at hstableAudit
  have hentry := (List.all_eq_true.mp hstableAudit)
    (address, declaration) hmember
  exact (beq_iff_eq).mp (by simpa [hlookup] using hentry)

/-- The theorem-facing source environment retains every raw lookup and adds
only stable aliases for newly derived keys.  These aliases make the forward
context relation total without changing any lookup the raw evaluator could
already perform. -/
def Result.preAddressEnv (result : Result) (groups : List Group) : Env :=
  fun address =>
    match Env.ofList (rawDeclarations groups) address with
    | some declaration => some declaration
    | none =>
        Env.ofList result.declarations
          (MutualBlock.Renaming.apply result.addressMap address)

/-- Evaluator context for the emitted content-addressed declarations. -/
def Result.addressedCtx (result : Result)
    (oracle : Oracle := fun _ _ => none) : Ctx :=
  { env := Env.ofList result.declarations, oracle }

/-- Evaluator context for the raw declarations and their stable aliases. -/
def Result.preAddressCtx (result : Result) (groups : List Group)
    (oracle : Oracle := fun _ _ => none) : Ctx :=
  { env := result.preAddressEnv groups, oracle }

@[simp] theorem Result.preAddressCtx_env_of_lookup
    (result : Result) (groups : List Group) (oracle : Oracle)
    {address : Address} {declaration : Decl}
    (hlookup : Env.ofList (rawDeclarations groups) address =
      some declaration) :
    (result.preAddressCtx groups oracle).env address = some declaration := by
  simp [Result.preAddressCtx, Result.preAddressEnv, hlookup]

/-- A successful audit plus an oracle-equivariance premise constructs the
complete context relation consumed by evaluator transport. -/
theorem Result.renames_preAddressCtx {result : Result}
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
    Ctx.Renames (MutualBlock.Renaming.apply result.addressMap)
      (result.preAddressCtx groups beforeOracle)
      (result.addressedCtx afterOracle) := by
  constructor
  · intro address
    simp only [Result.preAddressCtx, Result.addressedCtx,
      Result.preAddressEnv]
    cases hraw : Env.ofList (rawDeclarations groups) address with
    | some declaration =>
        simpa [hraw] using result.lookup_eq_mapAddresses haudit hraw
    | none =>
        simp only
        cases hemitted : Env.ofList result.declarations
            (MutualBlock.Renaming.apply result.addressMap address) with
        | none => simp
        | some declaration =>
            have hstable := result.lookup_stable haudit hemitted
            simp [hstable]
  · exact horacle

/-- A concrete successful readdressing preserves a closed run exactly. -/
theorem run_of_run_eq_ok
    {reserved : List Address} {groups : List Group} {main : Expr}
    {result : Result}
    (hrun : Readdress.run reserved groups main = .ok result)
    (beforeOracle afterOracle : Oracle)
    (horacle : ∀ address arguments,
      afterOracle
          (MutualBlock.Renaming.apply result.addressMap address)
          (ValueList.mapAddresses
            (MutualBlock.Renaming.apply result.addressMap) arguments) =
        (beforeOracle address arguments).map
          (Value.mapAddresses
            (MutualBlock.Renaming.apply result.addressMap)))
    (fuel : Nat := 100000) :
    (result.addressedCtx afterOracle).run result.main fuel =
      mapResult (MutualBlock.Renaming.apply result.addressMap)
        ((result.preAddressCtx groups beforeOracle).run main fuel) := by
  have haudit := semanticAudit_of_run_eq_ok hrun
  rw [result.main_eq_mapAddresses haudit]
  exact Ctx.run_mapAddresses
    (result.renames_preAddressCtx haudit beforeOracle afterOracle horacle)
    main fuel

/-- Closed programs with no extern oracle need no compatibility premise. -/
theorem run_emptyOracle_of_run_eq_ok
    {reserved : List Address} {groups : List Group} {main : Expr}
    {result : Result}
    (hrun : Readdress.run reserved groups main = .ok result)
    (fuel : Nat := 100000) :
    (result.addressedCtx).run result.main fuel =
      mapResult (MutualBlock.Renaming.apply result.addressMap)
        ((result.preAddressCtx groups).run main fuel) := by
  apply run_of_run_eq_ok hrun (fun _ _ => none) (fun _ _ => none) _ fuel
  intro address arguments
  rfl

/-- Successful raw execution therefore yields the structurally renamed value
under the emitted declarations. -/
theorem run_success_of_run_eq_ok
    {reserved : List Address} {groups : List Group} {main : Expr}
    {result : Result}
    (hrun : Readdress.run reserved groups main = .ok result)
    (beforeOracle afterOracle : Oracle)
    (horacle : ∀ address arguments,
      afterOracle
          (MutualBlock.Renaming.apply result.addressMap address)
          (ValueList.mapAddresses
            (MutualBlock.Renaming.apply result.addressMap) arguments) =
        (beforeOracle address arguments).map
          (Value.mapAddresses
            (MutualBlock.Renaming.apply result.addressMap)))
    {fuel : Nat} {value : Value}
    (hsource :
      (result.preAddressCtx groups beforeOracle).run main fuel = .ok value) :
    (result.addressedCtx afterOracle).run result.main fuel =
      .ok (Value.mapAddresses
        (MutualBlock.Renaming.apply result.addressMap) value) := by
  rw [run_of_run_eq_ok hrun beforeOracle afterOracle horacle fuel, hsource]
  rfl

end Readdress

end Ix.Compiler.IxIR0
