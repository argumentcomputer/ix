module

public import LSpec
public import Ix.Kernel
public import Ix.Kernel.SourceOwnership
public import Ix.Kernel.SourceConversion
public import Tests.Ix.Kernel.IxonFixtures

/-!
Production regressions for the consistency fragment, polymorphic constant
inference, dependent binders, and applications. These execute the lazy loader, inference, and serial driver
on content-addressed Ixon declarations. The theorems and their resource
premises are checked separately by `IxKernelConsistency`.
-/

namespace Tests.Kernel.Consistency

open LSpec Ix.Kernel Tests.Kernel.Fixtures

private def allSucceeded (env : Ixon.Env) (expected : Nat) (cfg : CheckCfg := {}) : Bool :=
  match checkEnvAnon env cfg with
  | .ok results => results.size == expected && results.all (·.err?.isNone)
  | .error _ => false

private def rowFailed (env : Ixon.Env) (target : Address) : Bool :=
  match checkEnvAnon env with
  | .ok results => results.any fun row => row.addr == target && row.err?.isSome
  | .error _ => false

/-- `P : Prop`, `p : P`, then definition/theorem/opaque aliases of `p`.
The axiom set supplies `p`; the definitions introduce no additional axiom. -/
private def aliasEnvironment : Ixon.Env := Id.run do
  let (env, proposition) := storeConst {}
    ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.zero]⟩
  let (env, witness) := storeConst env
    ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[proposition], #[]⟩
  let (env, first) := storeConst env
    ⟨.defn ⟨.defn, .safe, 0, .ref 0 #[], .ref 1 #[]⟩,
      #[], #[proposition, witness], #[]⟩
  let (env, second) := storeConst env
    ⟨.defn ⟨.thm, .safe, 0, .ref 0 #[], .ref 1 #[]⟩,
      #[], #[proposition, first], #[]⟩
  let (env, _) := storeConst env
    ⟨.defn ⟨.opaq, .safe, 0, .ref 0 #[], .ref 1 #[]⟩,
      #[], #[proposition, second], #[]⟩
  return env

private def sortEnvironment : Ixon.Env := Id.run do
  let definition : Ix.DefKind → Ixon.Constant := fun kind =>
    ⟨.defn ⟨kind, .safe, 0, .sort 1, .sort 0⟩, #[], #[], #[.zero, .succ .zero]⟩
  let (env, _) := storeConst {} (definition .defn)
  let (env, _) := storeConst env (definition .opaq)
  return env

private def failedAlias : Ixon.Env × Address := Id.run do
  let (env, carrier) := envA
  let (env, witness) := storeConst env
    ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[carrier], #[]⟩
  -- The witness has type A, whereas this definition declares Prop.
  return storeConst env
    ⟨.defn ⟨.defn, .safe, 0, .sort 0, .ref 0 #[]⟩,
      #[], #[witness], #[.zero]⟩

private def mismatchedSort : Ixon.Env × Address :=
  storeConst {}
    ⟨.defn ⟨.defn, .safe, 0, .sort 0, .sort 0⟩, #[], #[], #[.zero]⟩

private def missingReference : Ixon.Env × Address :=
  storeConst {}
    ⟨.defn ⟨.defn, .safe, 0, .sort 0, .ref 0 #[]⟩,
      #[], #[Address.blake3 "atomic-fragment-missing-reference".toUTF8], #[.zero]⟩

private def cases : TestSeq :=
  test "atomic fragment: source axioms and transitive aliases check"
    (allSucceeded aliasEnvironment 5)
  ++ test "atomic fragment: alias checks survive cache clearing at every item"
    (allSucceeded aliasEnvironment 5 { clearEvery := 1 })
  ++ test "atomic fragment: closed sort definitions check with persistent caches"
    (allSucceeded sortEnvironment 2 { clearEvery := 0 })
  ++ test "atomic fragment: closed sort definitions check with fresh caches"
    (allSucceeded sortEnvironment 2 { clearEvery := 1 })
  ++ test "atomic fragment: value/type mismatch is an error row inside public ok"
    (let (env, target) := failedAlias; rowFailed env target)
  ++ test "atomic fragment: Sort 0 does not inhabit Sort 0"
    (let (env, target) := mismatchedSort; rowFailed env target)
  ++ test "atomic fragment: an unresolved reference is not an admitted axiom"
    (let (env, target) := missingReference; rowFailed env target)
  ++ test "atomic fragment: empty input returns an empty successful result"
    (allSucceeded {} 0)

/-- A polymorphic identity axiom with a dependent function type. Inferring its
reference substitutes under binders without invoking binder inference. -/
private def polymorphicIdentity : Ixon.Env × Address :=
  storeConst {}
    ⟨.axio ⟨false, 1, .leanAll (.sort 0) (.leanAll (.var 0) (.var 1))⟩,
      #[], #[], #[.var 0]⟩

/-- Specializations at Prop and Type, followed by ordinary aliases. The source
axiom stays polymorphic while each admitted definition is monomorphic. -/
private def specializationEnvironment : Ixon.Env := Id.run do
  let (env, identity) := polymorphicIdentity
  let type := Ixon.Expr.leanAll (.sort 0) (.leanAll (.var 0) (.var 1))
  let (env, propIdentity) := storeConst env
    ⟨.defn ⟨.defn, .safe, 0, type, .ref 0 #[0]⟩, #[], #[identity], #[.zero]⟩
  let (env, typeIdentity) := storeConst env
    ⟨.defn ⟨.opaq, .safe, 0, type, .ref 0 #[0]⟩, #[], #[identity], #[.succ .zero]⟩
  let (env, _) := storeConst env
    ⟨.defn ⟨.thm, .safe, 0, type, .ref 0 #[]⟩, #[], #[propIdentity], #[.zero]⟩
  let (env, _) := storeConst env
    ⟨.defn ⟨.defn, .safe, 0, type, .ref 0 #[]⟩,
      #[], #[typeIdentity], #[.succ .zero]⟩
  return env

private def failedSpecialization (arguments : Array UInt64) (level : Ixon.Univ) :
    Ixon.Env × Address :=
  let (env, identity) := polymorphicIdentity
  storeConst env
    ⟨.defn ⟨.defn, .safe, 0,
      .leanAll (.sort 0) (.leanAll (.var 0) (.var 1)), .ref 0 arguments⟩,
      #[], #[identity], #[level]⟩

private def levelOne : KUniv .anon := .mkSucc .mkZero
private def levelTwo : KUniv .anon := .mkSucc levelOne

private def identityType : KExpr .anon :=
  .mkAll () () (.mkSort levelOne) (.mkAll () () (.mkVar 0 ()) (.mkVar 1 ()))

/-- Two occurrences of the same instantiated reference exercise both the
level-argument array and the walker's per-call memo reuse. -/
private def polymorphicReferences : Ixon.Env × Address × Address := Id.run do
  let (env, carrier) := storeConst {}
    ⟨.axio ⟨false, 1, .sort 0⟩, #[], #[], #[.var 0]⟩
  let (env, function) := storeConst env
    ⟨.axio ⟨false, 1, .leanAll (.ref 0 #[0]) (.ref 0 #[0])⟩,
      #[], #[carrier], #[.var 0]⟩
  return (env, function, carrier)

private def polymorphicLet : Ixon.Env × Address :=
  storeConst {}
    ⟨.axio ⟨false, 1,
      .letE false (.sort 1) (.sort 0) (.leanAll (.var 0) (.var 1))⟩,
      #[], #[], #[.var 0, .succ (.var 0)]⟩

private def simplifyingUniverses : Ixon.Env × Address :=
  storeConst {}
    ⟨.axio ⟨false, 2, .sort 0⟩, #[], #[],
      #[.imax (.max (.var 0) (.var 1)) (.var 1)]⟩

private def referenceSpecialization : Ixon.Env :=
  let (env, function, carrier) := polymorphicReferences
  (storeConst env
    ⟨.defn ⟨.defn, .safe, 0,
      .leanAll (.ref 0 #[0]) (.ref 0 #[0]), .ref 1 #[0]⟩,
      #[], #[carrier, function], #[.succ .zero]⟩).1

private def simplifiedSpecialization : Ixon.Env :=
  let (env, source) := simplifyingUniverses
  (storeConst env
    ⟨.defn ⟨.defn, .safe, 0, .sort 0, .ref 0 #[1, 0]⟩,
      #[], #[source], #[.zero, .succ (.succ .zero)]⟩).1

private def wrongSpecializationType : Ixon.Env × Address :=
  let (env, identity) := polymorphicIdentity
  storeConst env
    ⟨.defn ⟨.defn, .safe, 0,
      .leanAll (.sort 0) (.leanAll (.var 0) (.var 1)), .ref 0 #[1]⟩,
      #[], #[identity], #[.zero, .succ .zero]⟩

private def inferStored (fixture : Ixon.Env × Address) (arguments : Array (KUniv .anon))
    (expected : KExpr .anon) (inferOnly := false) (warmIntern := false) : Bool :=
  let action : TcM .anon (KExpr .anon) := do
    if warmIntern then
      let _ ← TcM.intern expected
    TcM.infer (.mkConst ⟨fixture.2, ()⟩ arguments)
  match action { TcState.newLazyAnon fixture.1 with inferOnly } with
  | .ok type after =>
      type.addr == expected.addr && after.env.consts.size > 0 &&
        (if inferOnly then after.env.inferOnlyCache.size == 1
          else after.env.inferCache.size == 1)
  | .error _ _ => false

private def arityRejected (arguments : Array (KUniv .anon)) : Bool :=
  match TcM.infer (.mkConst ⟨polymorphicIdentity.2, ()⟩ arguments)
      (TcState.newLazyAnon polymorphicIdentity.1) with
  | .error (.univParamMismatch expected actual) after =>
      expected == 1 && actual == arguments.size && after.env.inferCache.isEmpty
  | _ => false

private def polymorphicCases : TestSeq :=
  test "polymorphic constant: lazy inference substitutes a dependent function type"
    (inferStored polymorphicIdentity #[levelOne] identityType)
  ++ test "polymorphic constant: inference-only policy records its own cache partition"
    (inferStored polymorphicIdentity #[levelOne] identityType true)
  ++ test "polymorphic constant: an existing interned result is reused on a cache miss"
    (inferStored polymorphicIdentity #[levelOne] identityType false true)
  ++ test "polymorphic constant: shared nested references retain their universe arguments"
    (let (env, function, carrier) := polymorphicReferences
      let type := KExpr.mkConst ⟨carrier, ()⟩ #[levelOne]
      inferStored (env, function) #[levelOne] (.mkAll () () type type))
  ++ test "polymorphic constant: substitution preserves let and de Bruijn structure"
    (inferStored polymorphicLet #[levelOne]
      (.mkLet () (.mkSort levelTwo) (.mkSort levelOne)
        (.mkAll () () (.mkVar 0 ()) (.mkVar 1 ())) false))
  ++ test "polymorphic constant: imax with zero simplifies the returned sort"
    (inferStored simplifyingUniverses #[levelTwo, .mkZero] (.mkSort .mkZero))
  ++ test "polymorphic constant: swapped universe arguments change imax's result"
    (inferStored simplifyingUniverses #[.mkZero, levelTwo] (.mkSort levelTwo))
  ++ test "polymorphic constant: missing universe arguments reject before cache insertion"
    (arityRejected #[])
  ++ test "polymorphic constant: excess universe arguments reject before cache insertion"
    (arityRejected #[levelOne, levelTwo])
  ++ test "universe instantiation: nonempty arguments reject an out-of-range parameter"
    (match TcM.instantiateUnivParams (.mkSort (.mkParam 1 ())) #[.mkZero]
        (TcState.ofEnvAnon {}) with
      | .error (.univParamOutOfRange index count) _ => index == 1 && count == 1
      | _ => false : Bool)
  -- This deliberately invalid input records why the refinement theorem needs
  -- declaration scope: the production empty shortcut performs no range check.
  ++ test "universe instantiation: empty shortcut requires an external scope invariant"
    (match TcM.instantiateUnivParams (.mkSort (.mkParam 0 ())) #[]
        (TcState.ofEnvAnon {}) with
      | .ok (.sort (.param index _ _) _) _ => index == 0
      | _ => false : Bool)

private def specializationCases : TestSeq :=
  test "polymorphic environment: Prop and Type specializations and transitive aliases check"
    (allSucceeded specializationEnvironment 5 { clearEvery := 0 })
  ++ test "polymorphic environment: specializations check with fresh per-item caches"
    (allSucceeded specializationEnvironment 5 { clearEvery := 1 })
  ++ test "polymorphic environment: specialized types preserve nested interface references"
    (allSucceeded referenceSpecialization 3)
  ++ test "polymorphic environment: simplified imax type passes declaration conversion"
    (allSucceeded simplifiedSpecialization 2)
  ++ test "polymorphic environment: a different declared specialization fails conversion"
    (let (env, target) := wrongSpecializationType; rowFailed env target)
  ++ test "polymorphic environment: missing universe arguments fail declaration admission"
    (let (env, target) := failedSpecialization #[] .zero; rowFailed env target)
  ++ test "polymorphic environment: excess universe arguments fail declaration admission"
    (let (env, target) := failedSpecialization #[0, 0] .zero; rowFailed env target)
  ++ test "polymorphic environment: a monomorphic body cannot retain a universe parameter"
    (let (env, target) := failedSpecialization #[0] (.var 0); rowFailed env target)

/-- Real function bodies, with no source axiom supplying their values:
`idProp (P : Prop) (p : P) : P := p`, its Type analogue, and a theorem alias. -/
private def binderEnvironment : Ixon.Env := Id.run do
  let type := Ixon.Expr.leanAll (.sort 0) (.leanAll (.var 0) (.var 1))
  let value := Ixon.Expr.leanLam (.sort 0) (.leanLam (.var 0) (.var 0))
  let (env, propIdentity) := storeConst {}
    ⟨.defn ⟨.defn, .safe, 0, type, value⟩, #[], #[], #[.zero]⟩
  let (env, _) := storeConst env
    ⟨.defn ⟨.opaq, .safe, 0, type, value⟩, #[], #[], #[.succ .zero]⟩
  let (env, _) := storeConst env
    ⟨.defn ⟨.thm, .safe, 0, type, .ref 0 #[]⟩, #[], #[propIdentity], #[.zero]⟩
  return env

private def failedBinder (body : Ixon.Expr) : Ixon.Env × Address :=
  storeConst {}
    ⟨.defn ⟨.defn, .safe, 0,
      .leanAll (.sort 0) (.leanAll (.var 0) (.var 1)),
      .leanLam (.sort 0) (.leanLam (.var 0) body)⟩, #[], #[], #[.zero]⟩

/-- Inferring the same older local after a dependent push must reuse its
concrete type. Both cache partitions and scope cleanup are observable here. -/
private def dependentLocalCache (inferOnly : Bool) : Bool :=
  let propType := KExpr.mkSort (m := .anon) .mkZero
  let action : RecM .anon Bool := RecM.withLctxScope do
    let (first, firstId) ← TcM.openBinder () () propType (.mkVar 0 ())
    let firstType ← RecM.inferCall first
    let (_, secondId) ← TcM.openBinder () () first (.mkVar 1 ())
    let cachedType ← RecM.inferCall first
    let state ← get
    let key ← TcM.inferKey first
    return firstId != secondId && firstType.addr == propType.addr &&
      cachedType.addr == propType.addr && state.lctx.size == 2 &&
      (if inferOnly then state.env.inferOnlyCache[key]?.isSome
        else state.env.inferCache[key]?.isSome)
  match TcM.runRec action { TcState.ofEnvAnon {} with inferOnly } with
  | .ok passed after => passed && after.lctx.size == 0 && after.env.nextFVarId == 2
  | .error _ _ => false

private def nestedBinderInference (inferOnly : Bool) : Bool :=
  let propType := KExpr.mkSort (m := .anon) .mkZero
  let type := KExpr.mkAll () () propType (.mkAll () () (.mkVar 0 ()) (.mkVar 1 ()))
  let body := KExpr.mkLam () () propType (.mkLam () () (.mkVar 0 ()) (.mkVar 0 ()))
  match TcM.infer body { TcState.ofEnvAnon {} with inferOnly } with
  | .ok inferred after => inferred.addr == type.addr && after.lctx.size == 0 &&
      after.env.nextFVarId == 2
  | .error _ _ => false

private def binderCases : TestSeq :=
  test "binder environment: real Prop and Type identity bodies and theorem alias check"
    (allSucceeded binderEnvironment 3 { clearEvery := 0 })
  ++ test "binder environment: identity bodies check with fresh per-item caches"
    (allSucceeded binderEnvironment 3 { clearEvery := 1 })
  ++ test "binder inference: nested dependent lambdas close their local context"
    (nestedBinderInference false)
  ++ test "binder inference: inference-only lambdas return the same closed type"
    (nestedBinderInference true)
  ++ test "binder cache: full-mode lookup survives a newer dependent local"
    (dependentLocalCache false)
  ++ test "binder cache: inference-only lookup survives a newer dependent local"
    (dependentLocalCache true)
  ++ test "binder environment: returning the type variable instead of its witness fails"
    (let (env, target) := failedBinder (.var 1); rowFailed env target)
  ++ test "binder environment: an escaping bound variable fails validation"
    (let (env, target) := failedBinder (.var 2); rowFailed env target)

private def monomorphicIdentity (level : Ixon.Univ) (env : Ixon.Env := {}) : Ixon.Env × Address :=
  storeConst env
    ⟨.defn ⟨.defn, .safe, 0,
      .leanAll (.sort 0) (.leanAll (.var 0) (.var 1)),
      .leanLam (.sort 0) (.leanLam (.var 0) (.var 0))⟩, #[], #[], #[level]⟩

/-- Real definitions call an earlier identity at Prop and Type. A theorem
then calls the first wrapper, exercising a second semantic dependency. -/
private def applicationEnvironment : Ixon.Env := Id.run do
  let (env, propIdentity) := monomorphicIdentity .zero
  let (env, typeIdentity) := monomorphicIdentity (.succ .zero) env
  let type := Ixon.Expr.leanAll (.sort 0) (.leanAll (.var 0) (.var 1))
  let value := Ixon.Expr.leanLam (.sort 0) (.leanLam (.var 0)
    (.app (.app (.ref 0 #[]) (.var 1)) (.var 0)))
  let (env, wrapper) := storeConst env
    ⟨.defn ⟨.defn, .safe, 0, type, value⟩, #[], #[propIdentity], #[.zero]⟩
  let (env, _) := storeConst env
    ⟨.defn ⟨.thm, .safe, 0, type, value⟩, #[], #[wrapper], #[.zero]⟩
  let (env, _) := storeConst env
    ⟨.defn ⟨.opaq, .safe, 0, type, value⟩, #[], #[typeIdentity], #[.succ .zero]⟩
  return env

/-- `(P Q : Prop) → (P → Q) → P → Q`, with body `f p`. -/
private def localApplication : Ixon.Env :=
  let functionType := Ixon.Expr.leanAll (.var 1) (.var 1)
  (storeConst {}
    ⟨.defn ⟨.defn, .safe, 0,
      .leanAll (.sort 0) (.leanAll (.sort 0)
        (.leanAll functionType (.leanAll (.var 2) (.var 2)))),
      .leanLam (.sort 0) (.leanLam (.sort 0)
        (.leanLam functionType (.leanLam (.var 2) (.app (.var 1) (.var 0)))))⟩,
      #[], #[], #[.zero]⟩).1

/-- `(A : Type) → (B : A → Type) → ((x : A) → B x) → (x : A) → B x`.
Substitution must retain both active locals in the resulting `B x`. -/
private def dependentApplication : Ixon.Env :=
  let familyType := Ixon.Expr.leanAll (.var 0) (.sort 0)
  let functionType := Ixon.Expr.leanAll (.var 1) (.app (.var 1) (.var 0))
  (storeConst {}
    ⟨.defn ⟨.defn, .safe, 0,
      .leanAll (.sort 0) (.leanAll familyType
        (.leanAll functionType (.leanAll (.var 2) (.app (.var 2) (.var 0))))),
      .leanLam (.sort 0) (.leanLam familyType
        (.leanLam functionType (.leanLam (.var 2) (.app (.var 1) (.var 0)))))⟩,
      #[], #[], #[.succ .zero]⟩).1

/-- `(P : Prop) → ((P → P) → P) → P`, with body `f (fun p => p)`.
The function supplies the expected Pi's validity for the lambda argument. -/
private def lambdaArgument : Ixon.Env :=
  let functionType := Ixon.Expr.leanAll (.leanAll (.var 0) (.var 1)) (.var 1)
  (storeConst {}
    ⟨.defn ⟨.defn, .safe, 0,
      .leanAll (.sort 0) (.leanAll functionType (.var 1)),
      .leanLam (.sort 0) (.leanLam functionType
        (.app (.var 0) (.leanLam (.var 1) (.var 0))))⟩,
      #[], #[], #[.zero]⟩).1

private def failedApplication : Ixon.Env × Address :=
  let (env, identity) := monomorphicIdentity .zero
  storeConst env
    ⟨.defn ⟨.defn, .safe, 0,
      .leanAll (.sort 0) (.leanAll (.var 0) (.var 1)),
      .leanLam (.sort 0) (.leanLam (.var 0)
        (.app (.app (.ref 0 #[]) (.var 1)) (.var 1)))⟩,
      #[], #[identity], #[.zero]⟩

/-- Inspect the exact dependent result before leaving the scope. A repeated
application must preserve it when the production inference cache is warm. -/
private def applicationLocalResult : Bool :=
  let (env, identity) := monomorphicIdentity .zero
  let propType := KExpr.mkSort (m := .anon) .mkZero
  let action : RecM .anon Bool := RecM.withLctxScope do
    let (proposition, _) ← TcM.openBinder () () propType (.mkVar 0 ())
    let (witness, _) ← TcM.openBinder () () proposition (.mkVar 0 ())
    let term := KExpr.mkApp (.mkApp (.mkConst ⟨identity, ()⟩ #[]) proposition) witness
    let first ← RecM.inferCall term
    let second ← RecM.inferCall term
    let state ← get
    return first.addr == proposition.addr && second.addr == proposition.addr && state.lctx.size == 2
  match TcM.runRec action (TcState.newLazyAnon env) with
  | .ok passed after => passed && after.lctx.size == 0 && after.env.nextFVarId == 2
  | .error _ _ => false

/-- Put a direct lambda application beneath `A` and `a : A`, in the proof,
data, and universe-polymorphic regimes. -/
private def storeLambdaCall (env : Ixon.Env) (body : Ixon.Expr)
    (level : Ixon.Univ) (universes : UInt64 := 0) : Ixon.Env × Address :=
  storeConst env
    ⟨.defn ⟨.defn, .safe, universes,
      .leanAll (.sort 0) (.leanAll (.var 0) (.var 1)),
      .leanLam (.sort 0) (.leanLam (.var 0) body)⟩,
      #[], #[], #[level]⟩

private def directLambdaEnvironment : Ixon.Env := Id.run do
  let body := Ixon.Expr.app (.leanLam (.var 1) (.var 0)) (.var 0)
  let (env, _) := storeLambdaCall {} body .zero
  let (env, _) := storeLambdaCall env body (.succ .zero)
  return (storeLambdaCall env body (.var 0) 1).1

/-- The first lambda application returns another function, which is applied
again. Both application nodes need synthesis independently of their head. -/
private def returnedLambdaEnvironment : Ixon.Env := Id.run do
  let fn := Ixon.Expr.leanLam (.var 1) (.leanLam (.var 2) (.var 1))
  let body := Ixon.Expr.app (.app fn (.var 0)) (.var 0)
  let (env, _) := storeLambdaCall {} body .zero
  return (storeLambdaCall env body (.succ .zero)).1

/-- `((fun f : A → A => f a) (fun x : A => x))`. The lambda body's
application derives a bound that the enclosing lambda can reuse. -/
private def higherOrderLambdaEnvironment : Ixon.Env := Id.run do
  let functionType := Ixon.Expr.leanAll (.var 1) (.var 2)
  let fn := Ixon.Expr.leanLam functionType (.app (.var 0) (.var 1))
  let body := Ixon.Expr.app fn (.leanLam (.var 1) (.var 0))
  let (env, _) := storeLambdaCall {} body .zero
  return (storeLambdaCall env body (.succ .zero)).1

/-- `(fun y : A => f y) x`, with the dependent family in Prop or Type.
The generated codomain stays dependent through opening and abstraction. -/
private def dependentLambdaEnvironment : Ixon.Env := Id.run do
  let familyType := Ixon.Expr.leanAll (.var 0) (.sort 1)
  let functionType := Ixon.Expr.leanAll (.var 1) (.app (.var 1) (.var 0))
  let type := Ixon.Expr.leanAll (.sort 0) (.leanAll familyType
    (.leanAll functionType (.leanAll (.var 2) (.app (.var 2) (.var 0)))))
  let body := Ixon.Expr.app (.leanLam (.var 3) (.app (.var 2) (.var 0))) (.var 0)
  let value := Ixon.Expr.leanLam (.sort 0) (.leanLam familyType
    (.leanLam functionType (.leanLam (.var 2) body)))
  let (env, _) := storeConst {}
    ⟨.defn ⟨.defn, .safe, 0, type, value⟩, #[], #[], #[.succ .zero, .zero]⟩
  return (storeConst env
    ⟨.defn ⟨.defn, .safe, 0, type, value⟩, #[], #[], #[.succ .zero, .succ .zero]⟩).1

private def sortLambdaCall (declared : UInt64) : Ixon.Env × Address :=
  storeConst {}
    ⟨.defn ⟨.defn, .safe, 0, .sort declared,
      .app (.leanLam (.sort 1) (.var 0)) (.sort 0)⟩,
      #[], #[], #[.zero, .succ .zero]⟩

/-- The earlier axiom's own type check contains a direct lambda application.
The alias reuses that exact declared type, taking hash conversion. -/
private def appliedDeclarationType : Ixon.Env := Id.run do
  let type := Ixon.Expr.app (.leanLam (.sort 1) (.var 0)) (.sort 0)
  let (env, proposition) := storeConst {}
    ⟨.axio ⟨false, 0, type⟩, #[], #[], #[.zero, .succ .zero]⟩
  return (storeConst env
    ⟨.defn ⟨.defn, .safe, 0, type, .ref 0 #[]⟩,
      #[], #[proposition], #[.zero, .succ .zero]⟩).1

private def lambdaApplicationLocalResult : Bool :=
  let propType := KExpr.mkSort (m := .anon) .mkZero
  let action : RecM .anon Bool := RecM.withLctxScope do
    let (proposition, _) ← TcM.openBinder () () propType (.mkVar 0 ())
    let (witness, _) ← TcM.openBinder () () proposition (.mkVar 0 ())
    let term := KExpr.mkApp (.mkLam () () proposition (.mkVar 0 ())) witness
    let first ← RecM.inferCall term
    let second ← RecM.inferCall term
    let state ← get
    return first.addr == proposition.addr && second.addr == proposition.addr && state.lctx.size == 2
  match TcM.runRec action (TcState.ofEnvAnon {}) with
  | .ok passed after => passed && after.lctx.size == 0 && after.env.nextFVarId == 3
  | .error _ _ => false

/-- The value's inferred type is `A`, but its declared type is
`(fun X : Sort u => X) A`. The final declaration comparison must reduce. -/
private def betaDeclaredType (level : Ixon.Univ) (universes : UInt64 := 0)
    (wrongValue : Bool := false) : Ixon.Env × Address := Id.run do
  let (env, carrier) := storeConst {}
    ⟨.axio ⟨false, universes, .sort 0⟩, #[], #[], #[level]⟩
  let (env, witness) := storeConst env
    ⟨.axio ⟨false, universes, .ref 0 (if universes == 0 then #[] else #[0])⟩,
      #[], #[carrier], #[level]⟩
  let arguments := if universes == 0 then #[] else #[0]
  return storeConst env
    ⟨.defn ⟨.defn, .safe, universes,
      .app (.leanLam (.sort 0) (.var 0)) (.ref 0 arguments),
      .ref (if wrongValue then 0 else 1) arguments⟩,
      #[], #[carrier, witness], #[level]⟩

/-- Substitution through the returned Pi changes both occurrences of the
family parameter. The value is an identity function at the concrete type. -/
private def betaDeclaredFunction (level : Ixon.Univ) : Ixon.Env := Id.run do
  let (env, carrier) := storeConst {}
    ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[level]⟩
  return (storeConst env
    ⟨.defn ⟨.defn, .safe, 0,
      .app (.leanLam (.sort 0) (.leanAll (.var 0) (.var 1))) (.ref 0 #[]),
      .leanLam (.ref 0 #[]) (.var 0)⟩,
      #[], #[carrier], #[level]⟩).1

/-- Observe the unequal initial type hashes and successful repeated
conversion, in addition to the public environment-check regressions. -/
private def betaDeclaredComparison : Bool :=
  let (env, target) := betaDeclaredType .zero
  let action : RecM .anon Bool := do
    let concrete ← TcM.getConst (m := .anon) ⟨target, ()⟩
    let .defn _ _ _ _ _ _ type value _ _ := concrete | return false
    let inferred ← RecM.inferCall value
    let reduced ← RecM.whnfCoreFlagsRec type .DEF_EQ_CORE
    let first ← RecM.isDefEqCall inferred type
    let second ← RecM.isDefEqCall inferred type
    return inferred != type && reduced == inferred && first && second
  match TcM.runRec action (TcState.newLazyAnon env) with
  | .ok passed _ => passed
  | .error _ _ => false

/-- A beta result can retain a lambda and outer registered locals. This
checks capture avoidance in the simultaneous walker used by WHNF. -/
private def betaUnderBinder : Bool :=
  let action : RecM .anon Bool := RecM.withLctxScope do
    let (carrier, _) ← TcM.openBinder (m := .anon) () () (.mkSort .mkZero) (.mkVar 0 ())
    let (value, _) ← TcM.openBinder (m := .anon) () () carrier (.mkVar 0 ())
    let body := KExpr.mkLam () () carrier (.mkVar 1 ())
    let term := KExpr.mkApp (.mkLam () () carrier body) value
    let _ ← RecM.inferCall term
    let result ← RecM.whnfCoreFlagsRec term .FULL
    return result == KExpr.mkLam () () carrier value
  match TcM.runRec action (TcState.ofEnvAnon {}) with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

/-- Observe one production step, including the exact consumed prefix. The
partial cases retain binders; the function case exposes a new lambda only
after substitution and therefore leaves its argument for a later step. -/
private def multiBetaLocalResult (shape : Nat) : Bool :=
  let action : RecM .anon Bool := RecM.withLctxScope do
    let (carrier, _) ← TcM.openBinder (m := .anon) () () (.mkSort .mkZero) (.mkVar 0 ())
    let (first, _) ← TcM.openBinder (m := .anon) () () carrier (.mkVar 0 ())
    let (second, _) ← TcM.openBinder (m := .anon) () () carrier (.mkVar 0 ())
    let three := KExpr.mkLam () () (.mkSort .mkZero)
      (.mkLam () () (.mkVar 0 ()) (.mkLam () () (.mkVar 1 ()) (.mkVar 1 ())))
    let identity := KExpr.mkLam () () carrier (.mkVar 0 ())
    let head := if shape == 3 then
        KExpr.mkLam () () (.mkAll () () carrier carrier) (.mkVar 0 ())
      else if shape == 4 then
        KExpr.mkLam () () (.mkSort .mkZero) (.mkLam () () (.mkVar 0 ()) second)
      else three
    let arguments := if shape == 1 || shape == 4 then #[carrier, first]
      else if shape == 2 then #[carrier]
      else if shape == 3 then #[identity, first]
      else if shape == 5 then #[carrier, carrier, second]
      else #[carrier, first, second]
    let term := KExpr.mkAppN head arguments
    if shape == 5 then
      try
        let _ ← RecM.inferCall term
        return false
      catch _ => return true
    let _ ← RecM.inferCall term
    let expected := if shape == 1 then KExpr.mkLam () () carrier first
      else if shape == 2 then KExpr.mkLam () () carrier (.mkLam () () carrier (.mkVar 1 ()))
      else if shape == 3 then KExpr.mkApp identity first
      else if shape == 4 then second
      else first
    let (rawHead, rawArguments) := term.collectSpine
    let (_, consumed) := RecM.consumeBetaLams rawHead rawArguments
    let beforeStep ← get
    let .next result ← RecM.whnfCoreWithFlagsStep term .FULL | return false
    let cheap ← TcM.runIntern (cheapBetaReduce term)
    let afterStep ← get
    return consumed == (if shape == 3 then #[identity] else arguments) &&
      result == expected && result != term && first != second &&
      afterStep.env.nextFVarId == beforeStep.env.nextFVarId && afterStep.lctx.size == beforeStep.lctx.size &&
      cheap == (if shape == 1 || shape == 2 then term else expected)
  match TcM.runRec action (TcState.ofEnvAnon {}) with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

/-- Distinct carrier addresses make selecting the wrong argument observable.
The second carrier retains an unused universe-table entry to distinguish its
content-addressed declaration from the first carrier's identical type. -/
private def multiBetaDeclaredType (level : Ixon.Univ) (universes : UInt64 := 0)
    (dependent wrongValue : Bool := false) : Ixon.Env × Address := Id.run do
  let (env, carrier) := storeConst {}
    ⟨.axio ⟨false, universes, .sort 0⟩, #[], #[], #[level]⟩
  let (env, otherCarrier) := storeConst env
    ⟨.axio ⟨false, universes, .sort 0⟩, #[], #[], #[level, .succ level]⟩
  let arguments := if universes == 0 then #[] else #[0]
  let (env, witness) := storeConst env
    ⟨.axio ⟨false, universes, .ref 0 arguments⟩, #[], #[carrier], #[level]⟩
  let (env, otherWitness) := storeConst env
    ⟨.axio ⟨false, universes, .ref 0 arguments⟩, #[], #[otherCarrier], #[level]⟩
  let head := Ixon.Expr.leanLam (.sort 0)
    (.leanLam (if dependent then .var 0 else .sort 0) (.var 1))
  return storeConst env
    ⟨.defn ⟨.defn, .safe, universes,
      .app (.app head (.ref 0 arguments)) (.ref (if dependent then 2 else 1) arguments),
      .ref (if wrongValue then 3 else 2) arguments⟩,
      #[], #[carrier, otherCarrier, witness, otherWitness], #[level]⟩

/-- The declared type reduces to `F A` after consuming just its first
argument. The untouched suffix is essential to matching the witness's type. -/
private def multiBetaDeclaredSuffix (level : Ixon.Univ) : Ixon.Env := Id.run do
  let (env, carrier) := storeConst {}
    ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[level]⟩
  let functionType := Ixon.Expr.leanAll (.sort 0) (.sort 0)
  let (env, family) := storeConst env
    ⟨.axio ⟨false, 0, functionType⟩, #[], #[], #[level]⟩
  let (env, witness) := storeConst env
    ⟨.axio ⟨false, 0, .app (.ref 0 #[]) (.ref 1 #[])⟩, #[], #[family, carrier], #[]⟩
  return (storeConst env
    ⟨.defn ⟨.defn, .safe, 0,
      .app (.app (.leanLam functionType (.var 0)) (.ref 0 #[])) (.ref 1 #[]),
      .ref 2 #[]⟩, #[], #[family, carrier, witness], #[level]⟩).1

/-- The lambda body returns a local whose declared type is a beta redex.
Observe the changed synthesized codomain, including reuse beneath another
binder and inside both recursive application positions. -/
private def cheapLambdaLocalResult (shape : Nat) (level : KUniv .anon := .mkZero) : Bool :=
  let sort := KExpr.mkSort (m := .anon) level
  let action : RecM .anon Bool := RecM.withLctxScope do
    let (carrier, _) ← TcM.openBinder () () sort (.mkVar 0 ())
    let (witness, _) ← TcM.openBinder () () carrier (.mkVar 0 ())
    let head := if shape == 1 then
        KExpr.mkLam () () sort (.mkLam () () (.mkVar 0 ()) (.mkVar 1 ()))
      else KExpr.mkLam () () sort (if shape == 2 then carrier else .mkVar 0 ())
    let sourceType := KExpr.mkAppN head (if shape == 1 then #[carrier, witness] else #[carrier])
    let sourceSort ← RecM.inferCall sourceType
    let lambda := KExpr.mkLam () () sourceType (.mkVar 0 ())
    let expectedLambda := KExpr.mkAll () () sourceType carrier
    let term ← if shape == 3 then
        pure (KExpr.mkLam () () carrier lambda)
      else if shape == 4 then do
        let (argument, _) ← TcM.openBinder () () sourceType (.mkVar 0 ())
        pure (KExpr.mkApp lambda argument)
      else if shape == 5 then do
        let consumerType := KExpr.mkAll () () expectedLambda carrier
        let _ ← RecM.inferCall consumerType
        let (consumer, _) ← TcM.openBinder () () consumerType (.mkVar 0 ())
        pure (KExpr.mkApp consumer lambda)
      else pure lambda
    let expected := if shape == 3 then KExpr.mkAll () () carrier expectedLambda
      else if shape == 4 || shape == 5 then carrier else expectedLambda
    let before ← get
    let inferred ← RecM.inferCall term
    let repeated ← RecM.inferCall term
    let after ← get
    let reduced ← TcM.runIntern (cheapBetaReduce sourceType)
    return sourceSort == sort && (cheapBetaPlan? sourceType).isSome && sourceType != reduced &&
      reduced == carrier && inferred == expected && repeated == expected && after.lctx.size == before.lctx.size
  match TcM.runRec action (TcState.ofEnvAnon {}) with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

/-- An earlier declaration retains a beta-redex type. Returning its value
from a new lambda reduces that type during inference, before abstraction. -/
private def cheapLambdaConstant (level : Ixon.Univ) (universes : UInt64 := 0)
    (multiple wrongValue : Bool := false) : Ixon.Env × Address := Id.run do
  let (env, carrier) := storeConst {}
    ⟨.axio ⟨false, universes, .sort 0⟩, #[], #[], #[level]⟩
  let arguments := if universes == 0 then #[] else #[0]
  let (env, witness) := storeConst env
    ⟨.axio ⟨false, universes, .ref 0 arguments⟩, #[], #[carrier], #[level]⟩
  let type := if multiple then
      Ixon.Expr.app (.app (.leanLam (.sort 0) (.leanLam (.var 0) (.var 1))) (.ref 0 arguments))
        (.ref 1 arguments)
    else .app (.leanLam (.sort 0) (.var 0)) (.ref 0 arguments)
  let (env, value) := storeConst env
    ⟨.axio ⟨false, universes, type⟩, #[], #[carrier, witness], #[level]⟩
  return storeConst env
    ⟨.defn ⟨.defn, .safe, universes,
      .leanAll (.ref 0 arguments) (.ref 0 arguments),
      .leanLam (.ref 0 arguments) (.ref (if wrongValue then 0 else 1) arguments)⟩,
      #[], #[carrier, value], #[level]⟩

private def cheapLambdaConstantResult : Bool :=
  let (env, target) := cheapLambdaConstant .zero 0 true
  let action : RecM .anon Bool := do
    let concrete ← TcM.getConst (m := .anon) ⟨target, ()⟩
    let .defn _ _ _ _ _ _ type value _ _ := concrete | return false
    let .lam _ _ domain body _ := value | return false
    let original ← RecM.inferCall body
    let inferred ← RecM.inferCall value
    let reduced ← TcM.runIntern (cheapBetaReduce original)
    return (cheapBetaPlan? original).isSome && original != reduced && reduced == domain && inferred == type
  match TcM.runRec action (TcState.newLazyAnon env) with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

/-- Application substitutes into an earlier checked codomain containing a
beta redex. With two parameters, the second domain is `B x` and the final
carrier is `C x y`, so both substitutions affect the generated type. -/
private def cheapApplicationType (level : Ixon.Univ) (universes : UInt64 := 0)
    (dependent wrongArgument : Bool := false) : Ixon.Env × Address := Id.run do
  let (env, carrier) := storeConst {}
    ⟨.axio ⟨false, universes, .sort 0⟩, #[], #[], #[level]⟩
  let arguments := if universes == 0 then #[] else #[0]
  let (env, family) := storeConst env
    ⟨.axio ⟨false, universes, .leanAll (.ref 0 arguments) (.sort 0)⟩,
      #[], #[carrier], #[level]⟩
  let secondDomain := Ixon.Expr.app (.ref 1 arguments) (.var 0)
  let (env, dependentFamily) := storeConst env
    ⟨.axio ⟨false, universes, .leanAll (.ref 0 arguments) (.leanAll secondDomain (.sort 0))⟩,
      #[], #[carrier, family], #[level]⟩
  let result := if dependent then
      Ixon.Expr.app (.app (.ref 2 arguments) (.var 1)) (.var 0)
    else .app (.ref 1 arguments) (.var 0)
  let redex := Ixon.Expr.app (.leanLam (.sort 0) (.var 0)) result
  let functionType := Ixon.Expr.leanAll (.ref 0 arguments)
    (if dependent then .leanAll secondDomain redex else redex)
  let (env, function) := storeConst env
    ⟨.axio ⟨false, universes, functionType⟩, #[], #[carrier, family, dependentFamily], #[level]⟩
  let call := if dependent then
      Ixon.Expr.app (.app (.ref 3 arguments) (.var 1)) (.var (if wrongArgument then 1 else 0))
    else .app (.ref 3 arguments) (if wrongArgument then .ref 0 arguments else .var 0)
  return storeConst env
    ⟨.defn ⟨.defn, .safe, universes,
      .leanAll (.ref 0 arguments) (if dependent then .leanAll secondDomain result else result),
      .leanLam (.ref 0 arguments) (if dependent then .leanLam secondDomain call else call)⟩,
      #[], #[carrier, family, dependentFamily, function], #[level]⟩

private def cheapApplicationTypeResult (dependent : Bool) (level : Ixon.Univ := .zero) : Bool :=
  let (env, target) := cheapApplicationType level 0 dependent
  let action : RecM .anon Bool := RecM.withLctxScope do
    let concrete ← TcM.getConst (m := .anon) ⟨target, ()⟩
    let .defn _ _ _ _ _ _ type value _ _ := concrete | return false
    let .lam name bi domain body _ := value | return false
    let .all _ _ _ codomain _ := type | return false
    let (opened, first, _) ← TcM.openBinderWithFV name bi domain body
    let expected ← TcM.runIntern (instantiateRev codomain #[first])
    let (call, expected) ← if dependent then do
        let .lam name bi domain body _ := opened | return false
        let .all _ _ expectedDomain codomain _ := expected | return false
        if domain != expectedDomain then return false
        let (call, second, _) ← TcM.openBinderWithFV name bi domain body
        let .app firstCall _ _ := call | return false
        let .all _ _ partialDomain _ _ ← RecM.inferCall firstCall | return false
        if partialDomain != domain then return false
        let expected ← TcM.runIntern (instantiateRev codomain #[second])
        pure (call, expected)
      else pure (opened, expected)
    let original ← RecM.inferCall call
    let reduced ← TcM.runIntern (cheapBetaReduce original)
    let before ← get
    let inferred ← RecM.inferCall value
    let repeated ← RecM.inferCall value
    let after ← get
    return (cheapBetaPlan? original).isSome && original != reduced && reduced == expected &&
      inferred == type && repeated == type && after.lctx.size == before.lctx.size
  match TcM.runRec action (TcState.newLazyAnon env) with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

/-- The checked function type has a variable-headed codomain `F A` or
`F A B`. Substituting a lambda for `F` creates the beta prefix. The function
itself is the dependent identity, so its source axioms only declare carriers. -/
private def exposedLambdaType (level : Ixon.Univ) (universes : UInt64 := 0)
    (shape wrong : Nat := 0) : Ixon.Env × Address := Id.run do
  let (env, carrier) := storeConst {}
    ⟨.axio ⟨false, universes, .sort 0⟩, #[], #[], #[level]⟩
  let (env, otherCarrier) := storeConst env
    ⟨.axio ⟨false, universes, .sort 0⟩, #[], #[], #[level, .succ level]⟩
  let arguments := if universes == 0 then #[] else #[0]
  let familyType := Ixon.Expr.leanAll (.sort 0)
    (if shape == 2 then .leanAll (.sort 0) (.sort 0) else .sort 0)
  let applied : Ixon.Expr → Ixon.Expr := fun head =>
    if shape == 2 then .app (.app head (.ref 0 arguments)) (.ref 1 arguments)
    else .app head (.ref (if shape == 1 then 1 else 0) arguments)
  let (env, function) := storeConst env
    ⟨.defn ⟨.defn, .safe, universes,
      .leanAll familyType (.leanAll (applied (.var 0)) (applied (.var 1))),
      .leanLam familyType (.leanLam (applied (.var 0)) (.var 0))⟩,
      #[], #[carrier, otherCarrier], #[level]⟩
  let family := Ixon.Expr.leanLam (.sort 0)
    (if shape == 2 then .leanLam (.sort 0) (.var 1)
      else if shape == 1 then .ref 0 arguments else .var 0)
  let supplied := if wrong == 1 then Ixon.Expr.leanLam (.sort 0) (.sort 0) else family
  return storeConst env
    ⟨.defn ⟨.defn, .safe, universes,
      .leanAll (applied family) (.ref 0 arguments),
      .leanLam (applied family)
        (.app (.app (.ref 2 arguments) supplied) (if wrong == 2 then .ref 0 arguments else .var 0))⟩,
      #[], #[carrier, otherCarrier, function], #[level]⟩

private def exposedLambdaTypeResult (shape : Nat) (level : Ixon.Univ := .zero) : Bool :=
  let (env, target) := exposedLambdaType level 0 shape
  let action : RecM .anon Bool := RecM.withLctxScope do
    let concrete ← TcM.getConst (m := .anon) ⟨target, ()⟩
    let .defn _ _ _ _ _ _ type value _ _ := concrete | return false
    let .lam name bi domain body _ := value | return false
    let .all _ _ _ expected _ := type | return false
    let (fn, arguments) := body.collectSpine
    let some supplied := arguments[0]? | return false
    let .all fnName fnBi fnDomain fnBody _ ← RecM.inferCall fn | return false
    let suppliedType ← RecM.inferCall supplied
    let (openedType, originalHead, _) ← TcM.openBinderWithFV fnName fnBi fnDomain fnBody
    let .all _ _ _ originalCodomain _ := openedType | return false
    let (call, _) ← TcM.openBinder name bi domain body
    let generated ← RecM.inferCall call
    let (generatedHead, generatedArguments) := generated.collectSpine
    let reduced ← TcM.runIntern (cheapBetaReduce generated)
    let before ← get
    let inferred ← RecM.inferCall value
    let repeated ← RecM.inferCall value
    let after ← get
    return originalCodomain.collectSpine.1 == originalHead && (cheapBetaPlan? originalCodomain).isNone &&
      suppliedType == fnDomain && generatedHead == supplied && (cheapBetaPlan? generated).isSome &&
      (peelLamsN generatedArguments.size generatedHead).2 == (if shape == 2 then 2 else 1) &&
      generated != reduced && reduced == expected && inferred == type && repeated == type &&
      before.lctx.size == after.lctx.size
  match TcM.runRec action (TcState.newLazyAnon env) with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

/-- The function parameter depends on two earlier arguments. Its original
codomain is `F x`; the supplied constant family creates a new beta step only
after substituting the carrier and its witness. -/
private def dependentExposedLambdaType (level : Ixon.Univ) (universes : UInt64 := 0)
    (wrong : Bool := false) : Ixon.Env × Address := Id.run do
  let arguments := if universes == 0 then #[] else #[0]
  let (env, carrier) := storeConst {}
    ⟨.axio ⟨false, universes, .sort 0⟩, #[], #[], #[level]⟩
  let (env, witness) := storeConst env
    ⟨.axio ⟨false, universes, .ref 0 arguments⟩, #[], #[carrier], #[level]⟩
  let familyType := Ixon.Expr.leanAll (.var 1) (.sort 0)
  let (env, function) := storeConst env
    ⟨.defn ⟨.defn, .safe, universes,
      .leanAll (.sort 0) (.leanAll (.var 0)
        (.leanAll familyType (.leanAll (.app (.var 0) (.var 1)) (.app (.var 1) (.var 2))))),
      .leanLam (.sort 0) (.leanLam (.var 0)
        (.leanLam familyType (.leanLam (.app (.var 0) (.var 1)) (.var 0))))⟩,
      #[], #[], #[level]⟩
  let family := Ixon.Expr.leanLam (.ref 0 arguments) (.ref 0 arguments)
  let supplied := if wrong then Ixon.Expr.leanLam (.sort 0) (.ref 0 arguments) else family
  let domain := Ixon.Expr.app family (.ref 1 arguments)
  return storeConst env
    ⟨.defn ⟨.defn, .safe, universes, .leanAll domain (.ref 0 arguments),
      .leanLam domain (.app (.app (.app (.app (.ref 2 arguments)
        (.ref 0 arguments)) (.ref 1 arguments)) supplied) (.var 0))⟩,
      #[], #[carrier, witness, function], #[level]⟩

private def dependentExposedLambdaTypeResult (level : Ixon.Univ) : Bool :=
  let (env, target) := dependentExposedLambdaType level
  let action : RecM .anon Bool := RecM.withLctxScope do
    let concrete ← TcM.getConst (m := .anon) ⟨target, ()⟩
    let .defn _ _ _ _ _ _ type value _ _ := concrete | return false
    let .lam name bi domain body _ := value | return false
    let .all _ _ _ expected _ := type | return false
    let (fn, arguments) := body.collectSpine
    let some carrier := arguments[0]? | return false
    let some witness := arguments[1]? | return false
    let some family := arguments[2]? | return false
    let .all aName aBi aDomain aBody _ ← RecM.inferCall fn | return false
    let (afterA, originalA, _) ← TcM.openBinderWithFV aName aBi aDomain aBody
    let .all xName xBi xDomain xBody _ := afterA | return false
    let (afterX, originalX, _) ← TcM.openBinderWithFV xName xBi xDomain xBody
    let .all fName fBi fDomain fBody _ := afterX | return false
    let .all _ _ originalDomain _ _ := fDomain | return false
    let (afterF, originalF, _) ← TcM.openBinderWithFV fName fBi fDomain fBody
    let .all _ _ _ originalCodomain _ := afterF | return false
    let appliedPrefix := KExpr.mkAppN fn #[carrier, witness]
    let .all _ _ specializedDomain _ _ ← RecM.inferCall appliedPrefix | return false
    let .all _ _ specializedCarrier _ _ := specializedDomain | return false
    let familyType ← RecM.inferCall family
    let (call, _) ← TcM.openBinder name bi domain body
    let generated ← RecM.inferCall call
    let (generatedHead, generatedArguments) := generated.collectSpine
    let reduced ← TcM.runIntern (cheapBetaReduce generated)
    let before ← get
    let inferred ← RecM.inferCall value
    let repeated ← RecM.inferCall value
    let after ← get
    return originalDomain == originalA && xDomain == originalA &&
      originalCodomain.collectSpine == (originalF, #[originalX]) &&
      (cheapBetaPlan? originalCodomain).isNone && specializedCarrier == carrier &&
      specializedDomain == familyType && generatedHead == family && generatedArguments == #[witness] &&
      (cheapBetaPlan? generated).isSome && generated != reduced && reduced == expected &&
      inferred == type && repeated == type && before.lctx.size == after.lctx.size
  match TcM.runRec action (TcState.newLazyAnon env) with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

/-- Supplying a partial lambda application joins its existing arguments
to the variable-headed codomain's arguments. Dependent initial arguments
and caller locals exercise both substitution cutoffs and argument order. -/
private def composedLambdaType (level : Ixon.Univ) (universes : UInt64 := 0)
    (shape wrong : Nat := 0) : Ixon.Env × Address := Id.run do
  let levels := if universes == 0 then #[] else #[0]
  let (env, carrier) := storeConst {}
    ⟨.axio ⟨false, universes, .sort 0⟩, #[], #[], #[level]⟩
  let (env, otherCarrier) := storeConst env
    ⟨.axio ⟨false, universes, .sort 0⟩, #[], #[], #[level, .succ level]⟩
  let (env, witness) := storeConst env
    ⟨.axio ⟨false, universes, .ref 0 levels⟩, #[], #[carrier], #[level]⟩
  let familyType := Ixon.Expr.leanAll (.sort 0) (.sort 0)
  let (env, function) := storeConst env
    ⟨.defn ⟨.defn, .safe, universes,
      .leanAll familyType (.leanAll (.app (.var 0) (.ref 0 levels)) (.app (.var 1) (.ref 0 levels))),
      .leanLam familyType (.leanLam (.app (.var 0) (.ref 0 levels)) (.var 0))⟩,
      #[], #[otherCarrier], #[level]⟩
  let head := Ixon.Expr.leanLam (.sort 0)
    (if shape >= 2 then .leanLam (.var 0) (.leanLam (.sort 0) (.var 2))
      else .leanLam (.sort 0) (if shape == 1 then .ref 0 levels else .var 1))
  let familyAt : Ixon.Expr → Ixon.Expr → Ixon.Expr := fun type value =>
    if shape >= 2 then .app (.app head type) value
    else .app head (if shape == 1 then .ref 1 levels else type)
  let family := familyAt (.ref 0 levels) (.ref 2 levels)
  let domain := Ixon.Expr.app family (.ref 1 levels)
  let supplied := if wrong == 1 then familyAt (.ref 0 levels) (.ref 0 levels)
    else if wrong == 2 then
      .app (.leanLam (.sort 0) (.leanLam (.sort 0) (.var 0))) (.ref 0 levels)
    else family
  let type := if shape == 3 then
      Ixon.Expr.leanAll (.sort 0) (.leanAll (.var 0)
        (.leanAll (.app (familyAt (.var 1) (.var 0)) (.ref 1 levels)) (.var 2)))
    else .leanAll domain (.ref 0 levels)
  let value := if shape == 3 then
      Ixon.Expr.leanLam (.sort 0) (.leanLam (.var 0)
        (.leanLam (.app (familyAt (.var 1) (.var 0)) (.ref 1 levels))
          (.app (.app (.ref 3 levels) (familyAt (.var 2) (.var 1))) (.var 0))))
    else .leanLam domain (.app (.app (.ref 3 levels) supplied) (.var 0))
  return storeConst env
    ⟨.defn ⟨.defn, .safe, universes, type, value⟩,
      #[], #[carrier, otherCarrier, witness, function], #[level]⟩

private def composedLambdaTypeResult (shape : Nat) (level : Ixon.Univ) : Bool :=
  let (env, target) := composedLambdaType level 0 shape
  let action : RecM .anon Bool := RecM.withLctxScope do
    let concrete ← TcM.getConst (m := .anon) ⟨target, ()⟩
    let .defn _ _ _ _ _ _ type value _ _ := concrete | return false
    let .lam name bi domain body _ := value | return false
    let .all _ _ _ expected _ := type | return false
    let (fn, arguments) := body.collectSpine
    let some supplied := arguments[0]? | return false
    let .app .. := supplied | return false
    let (suppliedHead, initialArguments) := supplied.collectSpine
    let .all fnName fnBi fnDomain fnBody _ ← RecM.inferCall fn | return false
    let suppliedType ← RecM.inferCall supplied
    let (openedType, originalHead, _) ← TcM.openBinderWithFV fnName fnBi fnDomain fnBody
    let .all _ _ _ originalCodomain _ := openedType | return false
    let (call, _) ← TcM.openBinder name bi domain body
    let generated ← RecM.inferCall call
    let (generatedHead, generatedArguments) := generated.collectSpine
    let consumed := (peelLamsN generatedArguments.size generatedHead).2
    let reduced ← TcM.runIntern (cheapBetaReduce generated)
    let before ← get
    let inferred ← RecM.inferCall value
    let repeated ← RecM.inferCall value
    let after ← get
    return originalCodomain.collectSpine.1 == originalHead && (cheapBetaPlan? originalCodomain).isNone &&
      suppliedType == fnDomain && generatedHead == suppliedHead && generatedHead != supplied &&
      generatedArguments == initialArguments ++ originalCodomain.collectSpine.2 &&
      initialArguments.size == (if shape >= 2 then 2 else 1) && consumed == initialArguments.size + 1 &&
      (cheapBetaPlan? generated).isSome && generated != reduced && reduced == expected &&
      inferred == type && repeated == type && before.lctx.size == after.lctx.size
  match TcM.runRec action (TcState.newLazyAnon env) with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

/-- The outer lambda applies its parameter. Its first beta step exposes
the supplied lambda's separate prefix; the next step consumes that prefix.
Shape 4 also changes the outer body's inferred type from a beta sort to
the sort itself. Shape 6 retains an application suffix after the second step. -/
private def repeatedBetaDeclaredType (level : Ixon.Univ) (universes : UInt64 := 0)
    (shape wrong : Nat := 0) (wrappers : Nat := 0) : Ixon.Env × Address := Id.run do
  let levels := if universes == 0 then #[] else #[0]
  let betaSort := Ixon.Expr.app (.leanLam (.sort 1) (.var 0)) (.sort 0)
  let carrierSort := if shape == 4 then betaSort else .sort 0
  let (env, carrier) := storeConst {}
    ⟨.axio ⟨false, universes, carrierSort⟩, #[], #[], #[level, .succ level]⟩
  let (env, otherCarrier) := storeConst env
    ⟨.axio ⟨false, universes, carrierSort⟩, #[], #[], #[level, .succ level, .succ (.succ level)]⟩
  let familyType := Ixon.Expr.leanAll (.sort 0) (.sort 0)
  let (env, family) := storeConst env
    ⟨.axio ⟨false, universes, familyType⟩, #[], #[], #[level]⟩
  let (env, witness) := storeConst env
    ⟨.axio ⟨false, universes,
      if shape == 6 then .app (.ref 0 levels) (.ref 1 levels) else .ref 0 levels⟩,
      #[], if shape == 6 then #[family, carrier] else #[carrier], #[level]⟩
  let domain := if shape == 4 then Ixon.Expr.leanAll betaSort betaSort
    else if shape == 5 then .leanAll (.sort 0) (.leanAll (.var 0) (.sort 0))
    else familyType
  let mut supplied := if wrong == 1 then Ixon.Expr.leanLam (.sort 1) (.var 0)
    else if shape == 1 then .leanLam (.sort 0) (.ref 0 levels)
    else if shape == 2 then .app (.leanLam (.sort 0) (.leanLam (.sort 0) (.var 1))) (.ref 0 levels)
    else if shape == 3 then
      .app (.app (.leanLam (.sort 0) (.leanLam (.var 0) (.leanLam (.sort 0) (.var 2))))
        (.ref 0 levels)) (.ref (if wrong == 3 then 0 else 2) levels)
    else if shape == 4 then .app (.leanLam (.sort 1) (.leanLam (.var 0) (.var 0))) betaSort
    else if shape == 5 then .leanLam (.sort 0) (.leanLam (.var 0) (.var 1))
    else if shape == 6 then .app (.leanLam familyType (.var 0)) (.ref 3 levels)
    else .leanLam (.sort 0) (.var 0)
  for _ in List.range wrappers do
    supplied := .app (.leanLam domain (.var 0)) supplied
  let body := if shape == 5 then
      Ixon.Expr.app (.app (.var 0) (.ref 0 levels)) (.ref (if wrong == 3 then 0 else 2) levels)
    else .app (.var 0) (.ref (if shape == 1 || shape == 2 || shape == 3 || wrong == 2 then 1 else 0) levels)
  return storeConst env
    ⟨.defn ⟨.defn, .safe, universes, .app (.leanLam domain body) supplied, .ref 2 levels⟩,
      #[], #[carrier, otherCarrier, witness, family], #[level, .succ level]⟩

/-- Observe the two actual WHNF steps and the change of lambda head.
The second result must be exactly the value's already inferred type. -/
private def repeatedBetaDeclaredResult (shape : Nat) (level : Ixon.Univ) : Bool :=
  let (env, target) := repeatedBetaDeclaredType level 0 shape
  let action : RecM .anon Bool := do
    let concrete ← TcM.getConst (m := .anon) ⟨target, ()⟩
    let .defn _ _ _ _ _ _ type value _ _ := concrete | return false
    let .app outer supplied _ := type | return false
    let .lam _ _ _ body _ := outer | return false
    let expected ← RecM.inferCall value
    let .sort .. ← RecM.inferCall type | return false
    let (suppliedHead, initialArguments) := supplied.collectSpine
    let firstConsumed := (RecM.consumeBetaLams type.collectSpine.1 type.collectSpine.2).2
    let before ← get
    let .next middle ← RecM.whnfCoreWithFlagsStep type .DEF_EQ_CORE | return false
    let (middleHead, middleArguments) := middle.collectSpine
    let secondConsumed := (RecM.consumeBetaLams middleHead middleArguments).2
    let .next result ← RecM.whnfCoreWithFlagsStep middle .DEF_EQ_CORE | return false
    let after ← get
    let converted ← RecM.isDefEqCall expected type
    return firstConsumed == #[supplied] && middleHead == suppliedHead && middleHead != outer &&
      middleArguments == initialArguments ++ body.collectSpine.2 &&
      secondConsumed.size == (if shape == 3 then 3 else if shape >= 2 && shape <= 5 then 2 else 1) &&
      result == expected && type != middle && middle != result && converted &&
      after.lctx.size == before.lctx.size && after.env.nextFVarId == before.env.nextFVarId
  match TcM.runRec action (TcState.newLazyAnon env) with
  | .ok passed _ => passed
  | .error _ _ => false

private def repeatedBetaChangedBodyType (level : Ixon.Univ) (wrappers : Nat := 0) : Bool :=
  let (env, target) := repeatedBetaDeclaredType level 0 4 0 wrappers
  let action : RecM .anon Bool := RecM.withLctxScope do
    let concrete ← TcM.getConst (m := .anon) ⟨target, ()⟩
    let .defn _ _ _ _ _ _ (.app outer _ _) _ _ _ := concrete | return false
    let .lam name bi domain body _ := outer | return false
    let .all _ _ _ codomain _ ← RecM.inferCall outer | return false
    let (opened, _) ← TcM.openBinder name bi domain body
    let bodyType ← RecM.inferCall opened
    let reduced ← TcM.runIntern (cheapBetaReduce bodyType)
    return bodyType != codomain && (cheapBetaPlan? bodyType).isSome && reduced == codomain &&
      match codomain with | .sort .. => true | _ => false
  match TcM.runRec action (TcState.newLazyAnon env) with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

private def repeatedBetaCases : TestSeq :=
  test "successive beta: a supplied identity provides the second lambda origin in Prop and Type"
    (allSucceeded (repeatedBetaDeclaredType .zero).1 5 &&
      allSucceeded (repeatedBetaDeclaredType (.succ .zero)).1 5)
  ++ test "successive beta: a captured carrier survives a distinct body argument"
    (allSucceeded (repeatedBetaDeclaredType .zero 0 1).1 5 &&
      allSucceeded (repeatedBetaDeclaredType (.succ .zero) 0 1).1 5)
  ++ test "successive beta: a partial lambda joins its initial and body arguments"
    (allSucceeded (repeatedBetaDeclaredType .zero 0 2).1 5 &&
      allSucceeded (repeatedBetaDeclaredType (.succ .zero) 0 2).1 5)
  ++ test "successive beta: dependent initial and body arguments keep their order"
    (allSucceeded (repeatedBetaDeclaredType .zero 0 3).1 5 &&
      allSucceeded (repeatedBetaDeclaredType (.succ .zero) 0 5).1 5)
  ++ test "successive beta: changed body typing retains the original argument checks"
    (allSucceeded (repeatedBetaDeclaredType .zero 0 4).1 5 &&
      allSucceeded (repeatedBetaDeclaredType (.succ .zero) 0 4).1 5)
  ++ test "successive beta: the second prefix leaves the remaining family application"
    (allSucceeded (repeatedBetaDeclaredType .zero 0 6).1 5 &&
      allSucceeded (repeatedBetaDeclaredType (.succ .zero) 0 6).1 5)
  ++ test "successive beta: both origins and the changed body type retain universe parameters"
    ((List.range 7).all fun shape => allSucceeded (repeatedBetaDeclaredType (.var 0) 1 shape).1 5)
  ++ test "successive beta: the same declarations check with fresh per-item caches"
    ((List.range 7).all fun shape => allSucceeded (repeatedBetaDeclaredType .zero 0 shape).1 5 { clearEvery := 1 })
  ++ test "successive beta: both WHNF steps return the exact expected type in Prop and Type"
    ((List.range 7).all fun shape => repeatedBetaDeclaredResult shape .zero &&
      repeatedBetaDeclaredResult shape (.succ .zero))
  ++ test "successive beta: cheap beta changes the original body's type hash"
    (repeatedBetaChangedBodyType .zero && repeatedBetaChangedBodyType (.succ .zero))
  ++ test "successive beta: a supplied lambda with a different domain is rejected"
    (let (env, target) := repeatedBetaDeclaredType .zero 0 0 1; rowFailed env target)
  ++ test "successive beta: selecting the other carrier cannot type the original witness"
    (let (env, target) := repeatedBetaDeclaredType .zero 0 0 2; rowFailed env target)
  ++ test "successive beta: initial and body arguments must inhabit their dependent domains"
    (let (env, first) := repeatedBetaDeclaredType .zero 0 3 3
     let (otherEnv, second) := repeatedBetaDeclaredType .zero 0 5 3
     rowFailed env first && rowFailed otherEnv second)

/-- Every wrapper returns its function argument. The application suffix
survives each newly exposed prefix; the final prefix may consume a dependent
carrier/witness pair. The declared type always normalizes to the carrier. -/
private def betaTraceDeclaredType (level : Ixon.Univ) (universes : UInt64 := 0)
    (wrappers : Nat := 2) (dependent : Bool := false) (wrong : Nat := 0) : Ixon.Env × Address := Id.run do
  let levels := if universes == 0 then #[] else #[0]
  let (env, carrier) := storeConst {}
    ⟨.axio ⟨false, universes, .sort 0⟩, #[], #[], #[level]⟩
  let (env, otherCarrier) := storeConst env
    ⟨.axio ⟨false, universes, .sort 0⟩, #[], #[], #[level, .succ level]⟩
  let (env, witness) := storeConst env
    ⟨.axio ⟨false, universes, .ref 0 levels⟩, #[], #[carrier], #[level]⟩
  let family := Ixon.Expr.leanAll (.sort 0)
    (if dependent then .leanAll (.var 0) (.sort 0) else .sort 0)
  let mut function := Ixon.Expr.leanLam (.sort 0)
    (if dependent then .leanLam (.var 0) (.var 1) else .var 0)
  for _ in List.range wrappers do
    function := .app (.leanLam family (.var 0)) function
  let mut type := Ixon.Expr.app function (.ref (if wrong == 1 then 1 else 0) levels)
  if dependent then type := .app type (.ref (if wrong == 2 then 0 else 2) levels)
  return storeConst env
    ⟨.defn ⟨.defn, .safe, universes, type, .ref 2 levels⟩,
      #[], #[carrier, otherCarrier, witness], #[level]⟩

/-- Compare individual production steps, the explicitly bounded driver,
and the uncached WHNF entry point from the same loaded state. An exact
reduction-count budget must exhaust before the final `.done` iteration. -/
private def betaTraceLoopResult (level : Ixon.Univ) (wrappers : Nat)
    (dependent : Bool) (flags : WhnfFlags) : Bool :=
  let (env, target) := betaTraceDeclaredType level 0 wrappers dependent
  let action : RecM .anon Bool := do
    let .defn _ _ _ _ _ _ type value _ _ ← TcM.getConst (m := .anon) ⟨target, ()⟩ | return false
    let expected ← RecM.inferCall value
    let .sort .. ← RecM.inferCall type | return false
    let before ← get
    let mut current := type
    for index in List.range (wrappers + 1) do
      let (head, arguments) := current.collectSpine
      let consumed := (RecM.consumeBetaLams head arguments).2.size
      if consumed != (if index == wrappers && dependent then 2 else 1) then return false
      let .next next ← RecM.whnfCoreWithFlagsStep current flags | return false
      if next == current then return false
      current := next
    let .done terminal ← RecM.whnfCoreWithFlagsStep current flags | return false
    let stepped ← get
    if terminal != expected then return false
    set before
    let exhausted ← try
      let _ ← RecM.runBounded (fun term => RecM.whnfCoreWithFlagsStep term flags) (wrappers + 1) type
      pure false
    catch error => pure (match error with | .maxRecDepth => true | _ => false)
    let exhaustedState ← get
    set before
    let bounded ← RecM.runBounded (fun term => RecM.whnfCoreWithFlagsStep term flags) (wrappers + 2) type
    set before
    let normalized ← RecM.whnfCoreWithFlagsUncached type flags
    let after ← get
    return exhausted && bounded == expected && normalized == expected &&
      after.env.intern.exprs.size == stepped.env.intern.exprs.size &&
      exhaustedState.env.intern.exprs.size == stepped.env.intern.exprs.size &&
      after.lctx.size == before.lctx.size && after.env.nextFVarId == before.env.nextFVarId
  match TcM.runRec action (TcState.newLazyAnon env) with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

private def betaTraceCases : TestSeq :=
  test "beta trace: three prefixes preserve a returned function and its suffix in Prop and Type"
    (allSucceeded (betaTraceDeclaredType .zero).1 4 &&
      allSucceeded (betaTraceDeclaredType (.succ .zero)).1 4)
  ++ test "beta trace: twelve prefixes preserve dependent final arguments in Prop and Type"
    (allSucceeded (betaTraceDeclaredType .zero 0 11 true).1 4 &&
      allSucceeded (betaTraceDeclaredType (.succ .zero) 0 11 true).1 4)
  ++ test "beta trace: successive returned functions retain declaration universe parameters"
    (allSucceeded (betaTraceDeclaredType (.var 0) 1 4).1 4 &&
      allSucceeded (betaTraceDeclaredType (.var 0) 1 4 true).1 4)
  ++ test "beta trace: longer declarations check with fresh per-item caches"
    (allSucceeded (betaTraceDeclaredType .zero 0 4).1 4 { clearEvery := 1 } &&
      allSucceeded (betaTraceDeclaredType (.succ .zero) 0 4 true).1 4 { clearEvery := 1 })
  ++ test "beta trace: both WHNF policies agree with individual steps and the exact loop bound"
    ([0, 2, 5].all fun wrappers => [WhnfFlags.FULL, .DEF_EQ_CORE].all fun flags =>
      betaTraceLoopResult .zero wrappers false flags && betaTraceLoopResult (.succ .zero) wrappers false flags)
  ++ test "beta trace: the final dependent prefix consumes two arguments before the done iteration"
    ([0, 2, 5].all fun wrappers => [WhnfFlags.FULL, .DEF_EQ_CORE].all fun flags =>
      betaTraceLoopResult .zero wrappers true flags && betaTraceLoopResult (.succ .zero) wrappers true flags)
  ++ test "beta trace: a different carrier after four prefixes cannot type the original witness"
    (let (env, target) := betaTraceDeclaredType .zero 0 3 false 1; rowFailed env target)
  ++ test "beta trace: a retained dependent argument must still inhabit its selected carrier"
    (let (env, target) := betaTraceDeclaredType .zero 0 3 true 2; rowFailed env target)

/-- Substitute a supplied function under two retained dependent binders,
then expose an arbitrary chain of returned functions. Shape 0 reduces the
declared type to a carrier, shape 1 reduces the value to its witness, and
shape 2 returns a lambda whose body still contains the supplied function. -/
private def hereditaryBetaDeclaration (level : Ixon.Univ) (universes : UInt64 := 0)
    (wrappers shape wrong : Nat := 0) : Ixon.Env × Address := Id.run do
  let levels := if universes == 0 then #[] else #[0]
  let (env, carrier) := storeConst {}
    ⟨.axio ⟨false, universes, .sort 0⟩, #[], #[], #[level]⟩
  let (env, otherCarrier) := storeConst env
    ⟨.axio ⟨false, universes, .sort 0⟩, #[], #[], #[level, .succ level]⟩
  let (env, witness) := storeConst env
    ⟨.axio ⟨false, universes, .ref 0 levels⟩, #[], #[carrier], #[level]⟩
  let family := Ixon.Expr.leanAll (.sort 0)
    (.leanAll (.var 0) (if shape == 0 then .sort 0 else .var 1))
  let mut supplied := Ixon.Expr.leanLam (.sort 0)
    (.leanLam (.var 0) (if shape == 0 then .var 1 else .var 0))
  for _ in List.range wrappers do
    supplied := .app (.leanLam family (.var 0)) supplied
  let outer := Ixon.Expr.leanLam family
    (.leanLam (.sort 0) (.leanLam (.var 0) (.app (.app (.var 2) (.var 1)) (.var 0))))
  let mut source := Ixon.Expr.app outer supplied
  if shape != 2 then
    source := .app (.app source (.ref (if wrong == 1 then 1 else 0) levels))
      (.ref (if wrong == 2 then 0 else 2) levels)
  let type := if shape == 0 then source else if shape == 1 then .ref 0 levels else family
  let value := if shape == 0 then .ref 2 levels else source
  return storeConst env
    ⟨.defn ⟨.defn, .safe, universes, type, value⟩,
      #[], #[carrier, otherCarrier, witness], #[level]⟩

private def observeBetaPath (source expected : KExpr .anon) (counts : List Nat)
    (flags : WhnfFlags) : RecM .anon Bool := do
  let originalType ← RecM.inferCall source
  let before ← get
  let mut current := source
  for count in counts do
    let (head, arguments) := current.collectSpine
    if (RecM.consumeBetaLams head arguments).2.size != count then return false
    let .next next ← RecM.whnfCoreWithFlagsStep current flags | return false
    if next == current then return false
    current := next
  let .done terminal ← RecM.whnfCoreWithFlagsStep current flags | return false
  let stepped ← get
  set before
  let normalized ← RecM.whnfCoreWithFlagsUncached source flags
  let after ← get
  let terminalType ← RecM.inferCall terminal
  let sameType ← RecM.isDefEqCall originalType terminalType
  return terminal == expected && normalized == expected && sameType &&
    after.env.intern.exprs.size == stepped.env.intern.exprs.size &&
    after.lctx.size == before.lctx.size && after.env.nextFVarId == before.env.nextFVarId

private def hereditaryBetaResult (level : Ixon.Univ) (wrappers shape : Nat)
    (flags : WhnfFlags) : Bool :=
  let (env, target) := hereditaryBetaDeclaration level 0 wrappers shape
  let action : RecM .anon Bool := do
    let .defn _ _ _ _ _ _ type value _ _ ← TcM.getConst (m := .anon) ⟨target, ()⟩ | return false
    let source := if shape == 0 then type else value
    let (_, arguments) := source.collectSpine
    if shape == 2 then
      let .app _ supplied _ := source | return false
      let originalType ← RecM.inferCall source
      let before ← get
      let .next result ← RecM.whnfCoreWithFlagsStep source flags | return false
      let .lam _ _ _ (.lam _ _ _ (.app (.app captured _ _) _ _) _) _ := result | return false
      let .done terminal ← RecM.whnfCoreWithFlagsStep result flags | return false
      set before
      let normalized ← RecM.whnfCoreWithFlagsUncached source flags
      let resultType ← RecM.inferCall result
      return captured == supplied && terminal == result && normalized == result &&
        originalType == type && resultType == type
    else
      let some witness := arguments[2]? | return false
      let expected ← if shape == 0 then RecM.inferCall value else pure witness
      observeBetaPath source expected (3 :: List.replicate wrappers 1 ++ [2]) flags
  match TcM.runRec action (TcState.newLazyAnon env) with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

private def changedBodyBetaPath (level : Ixon.Univ) (wrappers : Nat) : Bool :=
  let (env, target) := repeatedBetaDeclaredType level 0 4 0 wrappers
  let action : RecM .anon Bool := do
    let .defn _ _ _ _ _ _ type value _ _ ← TcM.getConst (m := .anon) ⟨target, ()⟩ | return false
    let expected ← RecM.inferCall value
    observeBetaPath type expected (1 :: List.replicate wrappers 1 ++ [2]) .DEF_EQ_CORE
  match TcM.runRec action (TcState.newLazyAnon env) with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

private def hereditaryBetaCases : TestSeq :=
  test "hereditary beta: supplied functions cross two dependent binders in Prop and Type"
    ([0, 1, 2].all fun shape => [0, 4, 11].all fun wrappers =>
      allSucceeded (hereditaryBetaDeclaration .zero 0 wrappers shape).1 4 &&
      allSucceeded (hereditaryBetaDeclaration (.succ .zero) 0 wrappers shape).1 4)
  ++ test "hereditary beta: retained dependent binders preserve declaration universe parameters"
    ([0, 1, 2].all fun shape => allSucceeded (hereditaryBetaDeclaration (.var 0) 1 4 shape).1 4)
  ++ test "hereditary beta: all three substitution shapes check with fresh per-item caches"
    ([0, 1, 2].all fun shape =>
      allSucceeded (hereditaryBetaDeclaration .zero 0 4 shape).1 4 { clearEvery := 1 })
  ++ test "hereditary beta: both WHNF policies consume three binders and each later returned function"
    ([0, 4, 11].all fun wrappers => [WhnfFlags.FULL, .DEF_EQ_CORE].all fun flags =>
      hereditaryBetaResult .zero wrappers 0 flags && hereditaryBetaResult (.succ .zero) wrappers 0 flags)
  ++ test "hereditary beta: a term reduction preserves the original carrier type and returns its witness"
    ([0, 4].all fun wrappers => [WhnfFlags.FULL, .DEF_EQ_CORE].all fun flags =>
      hereditaryBetaResult .zero wrappers 1 flags && hereditaryBetaResult (.succ .zero) wrappers 1 flags)
  ++ test "hereditary beta: WHNF stops at a returned lambda retaining the supplied function in its body"
    ([0, 4].all fun wrappers => [WhnfFlags.FULL, .DEF_EQ_CORE].all fun flags =>
      hereditaryBetaResult .zero wrappers 2 flags && hereditaryBetaResult (.succ .zero) wrappers 2 flags)
  ++ test "hereditary beta: repeated returned functions preserve the lambda's changed body type"
    ([1, 4, 11].all fun wrappers =>
      allSucceeded (repeatedBetaDeclaredType .zero 0 4 0 wrappers).1 5 &&
      allSucceeded (repeatedBetaDeclaredType (.succ .zero) 0 4 0 wrappers).1 5 &&
      repeatedBetaChangedBodyType .zero wrappers && changedBodyBetaPath .zero wrappers &&
      changedBodyBetaPath (.succ .zero) wrappers)
  ++ test "hereditary beta: changed body types retain universe parameters and fresh-cache checks"
    (allSucceeded (repeatedBetaDeclaredType (.var 0) 1 4 0 4).1 5 &&
      allSucceeded (repeatedBetaDeclaredType .zero 0 4 0 4).1 5 { clearEvery := 1 })
  ++ test "hereditary beta: substituting a different carrier rejects the retained dependent witness"
    ([0, 1].all fun shape => let (env, target) := hereditaryBetaDeclaration .zero 0 4 shape 1
      rowFailed env target)
  ++ test "hereditary beta: a carrier cannot inhabit its own retained witness domain"
    ([0, 1].all fun shape => let (env, target) := hereditaryBetaDeclaration .zero 0 4 shape 2
      rowFailed env target)

/-- The axiom's type exposes a Pi by beta reduction. In the dependent
variant its first application returns another beta redex, so the next
argument check must expose a second Pi. -/
private def piExposureDeclaration (level : Ixon.Univ) (universes : UInt64 := 0)
    (dependent : Bool := false) (wrong : Nat := 0) : Ixon.Env × Address := Id.run do
  let levels := if universes == 0 then #[] else #[0]
  let (env, carrier) := storeConst {}
    ⟨.axio ⟨false, universes, .sort 0⟩, #[], #[], #[level]⟩
  let (env, otherCarrier) := storeConst env
    ⟨.axio ⟨false, universes, .sort 0⟩, #[], #[], #[level, .succ level]⟩
  let (env, witness) := storeConst env
    ⟨.axio ⟨false, universes, .ref 0 levels⟩, #[], #[carrier], #[level]⟩
  let family := Ixon.Expr.leanLam (.sort 0) (.leanAll (.var 0) (.var 1))
  let type := if dependent then
      Ixon.Expr.app (.leanLam (.sort 0) (.leanAll (.sort 0) (.app family (.var 0)))) (.ref 0 levels)
    else .app family (.ref 0 levels)
  let (env, function) := storeConst env
    ⟨.axio ⟨false, universes, type⟩, #[], #[carrier], #[level]⟩
  let fn := if dependent then Ixon.Expr.app (.ref 3 levels) (.ref (if wrong == 1 then 1 else 0) levels)
    else .ref 3 levels
  return storeConst env
    ⟨.defn ⟨.defn, .safe, universes, .ref 0 levels, .app fn (.ref (if wrong == 2 then 0 else 2) levels)⟩,
      #[], #[carrier, otherCarrier, witness, function], #[level]⟩

private def localPiExposure (level : Ixon.Univ) (universes : UInt64 := 0)
    (wrong : Bool := false) : Ixon.Env × Address :=
  let family := Ixon.Expr.leanLam (.sort 0) (.leanAll (.var 0) (.var 1))
  let type := Ixon.Expr.leanAll (.sort 0)
    (.leanAll (.var 0) (.leanAll (.app family (.var 1)) (.var 2)))
  let value := Ixon.Expr.leanLam (.sort 0)
    (.leanLam (.var 0) (.leanLam (.app family (.var 1)) (.app (.var 0) (.var (if wrong then 2 else 1)))))
  storeConst {} ⟨.defn ⟨.defn, .safe, universes, type, value⟩, #[], #[], #[level]⟩

/-- Inspect the actual public cache writes and exact shared-fuel charge.
A second call uses the populated outer cache with zero fuel and no recursive
methods, even while native reduction is active. -/
private def observePiExposure (source domain body : KExpr .anon) (instrumented noAccel : Bool) : RecM .anon Bool := do
  let .app .. := source | return false
  modify fun state => { state with
    env := { state.env with whnfCache := {}, whnfNoDeltaCache := {}, whnfCoreCache := {} }
    ctxAddrCache := {}, recFuel := 1, stats := instrumented, stepTrace := instrumented,
    whnfCalls := 17, whnfMisses := 11, noAccel, inNativeReduce := false }
  let before ← get
  let (foundDomain, foundBody) ← RecM.ensureForallDirect source
  let after ← get
  let key ← TcM.whnfKey source
  let expected := KExpr.mkAll () () domain body
  let warm := { after with inNativeReduce := true }
  match (RecM.ensureForallDirect source).run (methodsN 0) warm with
  | .error _ _ => return false
  | .ok (warmDomain, warmBody) reused =>
      return foundDomain == domain && foundBody == body && warmDomain == domain && warmBody == body &&
        after.env.whnfCache[key]? == some expected && after.env.whnfNoDeltaCache[key]? == some expected &&
        after.env.whnfCoreCache[key]? == some expected && after.recFuel == 0 && reused.recFuel == 0 &&
        after.whnfCalls == (if instrumented then 18 else 17) &&
        after.whnfMisses == (if instrumented then 12 else 11) &&
        reused.whnfCalls == (if instrumented then 19 else 17) && reused.whnfMisses == after.whnfMisses &&
        after.lctx.size == before.lctx.size && after.ctxId == before.ctxId &&
        after.env.nextFVarId == before.env.nextFVarId && reused.inNativeReduce &&
        after.ctxAddrCache.size == (if source.lbr == 0 || before.ctx.isEmpty then 0 else 1) &&
        reused.ctxAddrCache.size == after.ctxAddrCache.size &&
        reused.env.intern.exprs.size == after.env.intern.exprs.size

private def piExposureInferenceResult (typeLevel dependent instrumented noAccel : Bool) : Bool :=
  let (env, target) := piExposureDeclaration (if typeLevel then .succ .zero else .zero) 0 dependent
  let action : RecM .anon Bool := do
    let .defn _ _ _ _ _ _ expected value _ _ ← TcM.getConst (m := .anon) ⟨target, ()⟩ | return false
    let (head, arguments) := value.collectSpine
    if dependent then
      let firstType ← RecM.inferCall head
      let sort := KExpr.mkSort (if typeLevel then levelOne else .mkZero)
      let family := KExpr.mkLam () () sort (.mkAll () () (.mkVar 0 ()) (.mkVar 1 ()))
      let before ← get
      let exposed ← observePiExposure firstType sort (.mkApp family (.mkVar 0 ())) instrumented noAccel
      set before
      if !exposed || arguments.size != 2 then return false
    let .app fn arg _ := value | return false
    let functionType ← RecM.inferCall fn
    let argumentType ← RecM.inferCall arg
    let before ← get
    let exposed ← observePiExposure functionType expected expected instrumented noAccel
    set before
    let result ← RecM.inferCall value
    return exposed && argumentType == expected && result == expected
  match TcM.runRec action (TcState.newLazyAnon env) with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

private def localPiExposureResult (typeLevel : Bool) : Bool :=
  let (env, target) := localPiExposure (if typeLevel then .succ .zero else .zero)
  let action : RecM .anon Bool := RecM.withLctxScope do
    let .defn _ _ _ _ _ _ _ value _ _ ← TcM.getConst (m := .anon) ⟨target, ()⟩ | return false
    let mut opened := value
    for _ in List.range 3 do
      let .lam name bi domain body _ := opened | return false
      opened := (← TcM.openBinder name bi domain body).1
    let .app fn arg _ := opened | return false
    let functionType ← RecM.inferCall fn
    let expected ← RecM.inferCall arg
    let before ← get
    let exposed ← observePiExposure functionType expected expected true true
    set before
    let result ← RecM.inferCall opened
    return exposed && result == expected && before.lctx.size == 3
  match TcM.runRec action (TcState.newLazyAnon env) with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

private def legacyPiExposureKey : Bool :=
  let sort := KExpr.mkSort levelOne
  let source := KExpr.mkApp (.mkLam () () sort (.mkAll () () (.mkVar 0 ()) (.mkVar 1 ()))) (.mkVar 0 ())
  let action : RecM .anon Bool := do
    TcM.pushLocal sort
    TcM.pushLocal sort
    observePiExposure source (.mkVar 0 ()) (.mkVar 1 ()) true false
  match TcM.runRec action (TcState.newLazyAnon {}) with
  | .ok passed after => passed && after.ctx.size == 2
  | .error _ _ => false

private def piExposureCases : TestSeq :=
  test "Pi exposure: beta function types check in Prop and Type"
    (allSucceeded (piExposureDeclaration .zero).1 5 &&
      allSucceeded (piExposureDeclaration (.succ .zero)).1 5)
  ++ test "Pi exposure: successive arguments each expose their dependent function type"
    (allSucceeded (piExposureDeclaration .zero 0 true).1 5 &&
      allSucceeded (piExposureDeclaration (.succ .zero) 0 true).1 5)
  ++ test "Pi exposure: function and argument types retain universe parameters"
    (allSucceeded (piExposureDeclaration (.var 0) 1).1 5 &&
      allSucceeded (piExposureDeclaration (.var 0) 1 true).1 5)
  ++ test "Pi exposure: declarations check with fresh per-item caches"
    ([false, true].all fun dependent =>
      allSucceeded (piExposureDeclaration (.succ .zero) 0 dependent).1 5 { clearEvery := 1 })
  ++ test "Pi exposure: all three public caches contain the Pi and warm hits need no fuel"
    ([false, true].all fun typeLevel => [false, true].all fun dependent =>
      [false, true].all fun instrumented => [false, true].all fun noAccel =>
        piExposureInferenceResult typeLevel dependent instrumented noAccel)
  ++ test "Pi exposure: dependent local function types check beneath three binders"
    (allSucceeded (localPiExposure .zero).1 1 && allSucceeded (localPiExposure (.succ .zero)).1 1 &&
      allSucceeded (localPiExposure (.var 0) 1).1 1 { clearEvery := 1 })
  ++ test "Pi exposure: public reduction preserves opened locals and scope cleanup"
    (localPiExposureResult false && localPiExposureResult true)
  ++ test "Pi exposure: legacy context keys memoize the reachable suffix"
    legacyPiExposureKey
  ++ test "Pi exposure: choosing another carrier rejects the dependent witness"
    (let (env, target) := piExposureDeclaration .zero 0 true 1; rowFailed env target)
  ++ test "Pi exposure: a carrier cannot replace the checked witness"
    ([false, true].all fun dependent =>
      let (env, target) := piExposureDeclaration .zero 0 dependent 2; rowFailed env target)
  ++ test "Pi exposure: a local carrier cannot inhabit its own function domain"
    (let (env, target) := localPiExposure .zero 0 true; rowFailed env target)

private def applicationCases : TestSeq :=
  test "application environment: Prop/Type identity calls and transitive theorem calls check"
    (allSucceeded applicationEnvironment 5 { clearEvery := 0 })
  ++ test "application environment: calls check with fresh per-item caches"
    (allSucceeded applicationEnvironment 5 { clearEvery := 1 })
  ++ test "application environment: a local function checks its argument against a distinct domain"
    (allSucceeded localApplication 1)
  ++ test "application environment: a dependent local function returns the substituted family"
    (allSucceeded dependentApplication 1)
  ++ test "application environment: a local function accepts a checked lambda argument"
    (allSucceeded lambdaArgument 1)
  ++ test "application inference: exact local result survives cache reuse and scope cleanup"
    applicationLocalResult
  ++ test "application environment: passing the proposition instead of its witness fails"
    (let (env, target) := failedApplication; rowFailed env target)
  ++ test "application environment: applying a proof with no function type fails"
    (let (env, target) := failedBinder (.app (.var 0) (.var 0)); rowFailed env target)
  ++ test "synthesis environment: direct lambda calls check in Prop, Type, and at a universe parameter"
    (allSucceeded directLambdaEnvironment 3 { clearEvery := 0 })
  ++ test "synthesis environment: direct lambda calls check with fresh per-item caches"
    (allSucceeded directLambdaEnvironment 3 { clearEvery := 1 })
  ++ test "synthesis environment: a direct lambda call returns a function that can be applied again"
    (allSucceeded returnedLambdaEnvironment 2)
  ++ test "synthesis environment: function and argument lambdas retain application bounds"
    (allSucceeded higherOrderLambdaEnvironment 2)
  ++ test "synthesis environment: dependent lambda bodies synthesize in Prop and Type"
    (allSucceeded dependentLambdaEnvironment 2)
  ++ test "synthesis environment: a direct lambda call returns the expected universe term"
    (allSucceeded (sortLambdaCall 1).1 1)
  ++ test "synthesis environment: an earlier declared type can itself contain a direct lambda call"
    (allSucceeded appliedDeclarationType 2)
  ++ test "synthesis inference: a direct lambda result survives cache reuse and scope cleanup"
    lambdaApplicationLocalResult
  ++ test "synthesis environment: a proposition cannot be used as its own witness argument"
    (let (env, target) := failedBinder (.app (.leanLam (.var 1) (.var 0)) (.var 1)); rowFailed env target)
  ++ test "synthesis environment: a direct lambda cannot return Sort 0 at type Sort 0"
    (let (env, target) := sortLambdaCall 0; rowFailed env target)
  ++ test "synthesis environment: a lambda domain must pass its executed sort check"
    (let (env, target) := failedBinder (.app (.leanLam (.var 0) (.var 0)) (.var 0)); rowFailed env target)
  ++ test "beta conversion: declared types reduce in Prop and Type"
    (allSucceeded (betaDeclaredType .zero).1 3 &&
      allSucceeded (betaDeclaredType (.succ .zero)).1 3)
  ++ test "beta conversion: declared types reduce at every universe instance"
    (allSucceeded (betaDeclaredType (.var 0) 1).1 3)
  ++ test "beta conversion: declarations check with fresh per-item caches"
    (allSucceeded (betaDeclaredType .zero).1 3 { clearEvery := 1 })
  ++ test "beta conversion: substitution enters a returned dependent function type"
    (allSucceeded (betaDeclaredFunction .zero) 2 &&
      allSucceeded (betaDeclaredFunction (.succ .zero)) 2)
  ++ test "beta conversion: unequal initial hashes convert and reuse the result"
    betaDeclaredComparison
  ++ test "beta reduction: returned lambdas preserve outer locals without capture"
    betaUnderBinder
  ++ test "beta conversion: reducing a declared proposition cannot make it its own proof"
    (let (env, target) := betaDeclaredType .zero 0 true; rowFailed env target)

private def multiBetaCases : TestSeq :=
  test "multi beta: three dependent arguments retain outer-to-inner order" (multiBetaLocalResult 0)
  ++ test "multi beta: two consumed binders leave a capture-free lambda" (multiBetaLocalResult 1)
  ++ test "multi beta: one consumed binder substitutes through two remaining domains" (multiBetaLocalResult 2)
  ++ test "multi beta: a newly exposed lambda retains the unconsumed argument suffix" (multiBetaLocalResult 3)
  ++ test "cheap beta: a closed body selects the original outer local" (multiBetaLocalResult 4)
  ++ test "multi beta: the dependent argument must inhabit the selected carrier" (multiBetaLocalResult 5)
  ++ test "multi beta admission: distinct carrier arguments reduce in Prop and Type"
    (allSucceeded (multiBetaDeclaredType .zero).1 5 &&
      allSucceeded (multiBetaDeclaredType (.succ .zero)).1 5)
  ++ test "multi beta admission: declared universe parameters survive simultaneous substitution"
    (allSucceeded (multiBetaDeclaredType (.var 0) 1).1 5)
  ++ test "multi beta admission: the second lambda domain depends on the first argument"
    (allSucceeded (multiBetaDeclaredType .zero 0 true).1 5 &&
      allSucceeded (multiBetaDeclaredType (.succ .zero) 0 true).1 5)
  ++ test "multi beta admission: conversion succeeds with fresh per-item caches"
    (allSucceeded (multiBetaDeclaredType .zero).1 5 { clearEvery := 1 })
  ++ test "multi beta admission: rebuilding the suffix retains the family application"
    (allSucceeded (multiBetaDeclaredSuffix .zero) 4 &&
      allSucceeded (multiBetaDeclaredSuffix (.succ .zero)) 4)
  ++ test "multi beta admission: selecting a witness of the other carrier is rejected"
    (let (env, target) := multiBetaDeclaredType .zero 0 false true; rowFailed env target)

private def cheapLambdaCases : TestSeq :=
  test "lambda cheap beta: a checked local type reduces in Prop and Type"
    (cheapLambdaLocalResult 0 && cheapLambdaLocalResult 0 (.mkSucc .mkZero))
  ++ test "lambda cheap beta: a dependent two-lambda type reduces before abstraction"
    (cheapLambdaLocalResult 1)
  ++ test "lambda cheap beta: a closed body retains the earlier local"
    (cheapLambdaLocalResult 2)
  ++ test "lambda cheap beta: a retained local type crosses another binder"
    (cheapLambdaLocalResult 3)
  ++ test "lambda cheap beta: the changed lambda type is used in function position"
    (cheapLambdaLocalResult 4)
  ++ test "lambda cheap beta: the changed lambda type is used in argument position"
    (cheapLambdaLocalResult 5)
  ++ test "lambda cheap beta admission: earlier declaration types reduce in Prop and Type"
    (allSucceeded (cheapLambdaConstant .zero).1 4 &&
      allSucceeded (cheapLambdaConstant (.succ .zero)).1 4)
  ++ test "lambda cheap beta admission: retained declaration checks support universe parameters"
    (allSucceeded (cheapLambdaConstant (.var 0) 1).1 4)
  ++ test "lambda cheap beta admission: earlier checks retain dependent argument domains"
    (allSucceeded (cheapLambdaConstant .zero 0 true).1 4 &&
      allSucceeded (cheapLambdaConstant (.var 0) 1 true).1 4)
  ++ test "lambda cheap beta admission: reduction survives per-item cache clearing"
    (allSucceeded (cheapLambdaConstant .zero 0 true).1 4 { clearEvery := 1 })
  ++ test "lambda cheap beta inference: the original and reduced body types have different hashes"
    cheapLambdaConstantResult
  ++ test "lambda cheap beta admission: returning a carrier in place of its witness is rejected"
    (let (env, target) := cheapLambdaConstant .zero 0 true true; rowFailed env target)

private def cheapApplicationCases : TestSeq :=
  test "application type beta: substituted codomains check in Prop and Type"
    (allSucceeded (cheapApplicationType .zero).1 5 &&
      allSucceeded (cheapApplicationType (.succ .zero)).1 5)
  ++ test "application type beta: an earlier codomain check retains universe parameters"
    (allSucceeded (cheapApplicationType (.var 0) 1).1 5)
  ++ test "application type beta: the second parameter depends on the first argument"
    (allSucceeded (cheapApplicationType .zero 0 true).1 5 &&
      allSucceeded (cheapApplicationType (.succ .zero) 0 true).1 5)
  ++ test "application type beta: dependent parameters retain universe parameters"
    (allSucceeded (cheapApplicationType (.var 0) 1 true).1 5)
  ++ test "application type beta: dependent substitutions survive per-item cache clearing"
    (allSucceeded (cheapApplicationType .zero 0 true).1 5 { clearEvery := 1 })
  ++ test "application type beta: a single argument changes the generated body type before abstraction"
    (cheapApplicationTypeResult false && cheapApplicationTypeResult false (.succ .zero))
  ++ test "application type beta: two arguments update the later domain and the exact reduced result"
    (cheapApplicationTypeResult true && cheapApplicationTypeResult true (.succ .zero))
  ++ test "application type beta: passing the carrier as its own witness is rejected"
    (let (env, target) := cheapApplicationType .zero 0 false true; rowFailed env target)
  ++ test "application type beta: the first argument cannot replace the dependent second argument"
    (let (env, target) := cheapApplicationType .zero 0 true true; rowFailed env target)

private def exposedLambdaCases : TestSeq :=
  test "exposed type lambda: a function parameter becomes a lambda in Prop and Type"
    (allSucceeded (exposedLambdaType .zero).1 4 && allSucceeded (exposedLambdaType (.succ .zero)).1 4)
  ++ test "exposed type lambda: the substituted lambda retains a different captured carrier"
    (allSucceeded (exposedLambdaType .zero 0 1).1 4 &&
      allSucceeded (exposedLambdaType (.succ .zero) 0 1).1 4)
  ++ test "exposed type lambda: the argument contributes two checked leading lambdas"
    (allSucceeded (exposedLambdaType .zero 0 2).1 4 &&
      allSucceeded (exposedLambdaType (.succ .zero) 0 2).1 4)
  ++ test "exposed type lambda: the new prefixes retain universe parameters"
    (allSucceeded (exposedLambdaType (.var 0) 1).1 4 &&
      allSucceeded (exposedLambdaType (.var 0) 1 1).1 4 &&
      allSucceeded (exposedLambdaType (.var 0) 1 2).1 4)
  ++ test "exposed type lambda: later dependent arguments work with fresh per-item caches"
    (allSucceeded (exposedLambdaType .zero).1 4 { clearEvery := 1 } &&
      allSucceeded (exposedLambdaType .zero 0 2).1 4 { clearEvery := 1 })
  ++ test "exposed type lambda: a variable-headed original type gains one beta step"
    (exposedLambdaTypeResult 0 && exposedLambdaTypeResult 0 (.succ .zero))
  ++ test "exposed type lambda: the closed-body plan preserves the captured carrier"
    (exposedLambdaTypeResult 1 && exposedLambdaTypeResult 1 (.succ .zero))
  ++ test "exposed type lambda: the variable plan consumes the new two-lambda prefix in order"
    (exposedLambdaTypeResult 2 && exposedLambdaTypeResult 2 (.succ .zero))
  ++ test "exposed type lambda: a lambda with the wrong function type is rejected"
    (let (env, target) := exposedLambdaType .zero 0 0 1; rowFailed env target)
  ++ test "exposed type lambda: a carrier cannot replace the later dependent witness"
    (let (env, target) := exposedLambdaType .zero 0 2 2; rowFailed env target)
  ++ test "exposed type lambda: earlier arguments specialize the function parameter in Prop and Type"
    (allSucceeded (dependentExposedLambdaType .zero).1 4 &&
      allSucceeded (dependentExposedLambdaType (.succ .zero)).1 4)
  ++ test "exposed type lambda: earlier dependent substitutions preserve universe parameters"
    (allSucceeded (dependentExposedLambdaType (.var 0) 1).1 4)
  ++ test "exposed type lambda: earlier dependent substitutions survive fresh per-item caches"
    (allSucceeded (dependentExposedLambdaType .zero).1 4 { clearEvery := 1 })
  ++ test "exposed type lambda: the earlier carrier and witness reach the new beta step exactly"
    (dependentExposedLambdaTypeResult .zero && dependentExposedLambdaTypeResult (.succ .zero))
  ++ test "exposed type lambda: a supplied family must use its specialized dependent domain"
    (let (env, target) := dependentExposedLambdaType .zero 0 true; rowFailed env target)
  ++ test "composed type lambda: existing and outer arguments share a prefix in Prop and Type"
    (allSucceeded (composedLambdaType .zero).1 5 &&
      allSucceeded (composedLambdaType (.succ .zero)).1 5)
  ++ test "composed type lambda: a closed body retains a captured carrier"
    (allSucceeded (composedLambdaType .zero 0 1).1 5 &&
      allSucceeded (composedLambdaType (.succ .zero) 0 1).1 5)
  ++ test "composed type lambda: existing dependent arguments keep their checked order"
    (allSucceeded (composedLambdaType .zero 0 2).1 5 &&
      allSucceeded (composedLambdaType (.succ .zero) 0 2).1 5)
  ++ test "composed type lambda: caller locals survive substitution beneath the remaining parameter"
    (allSucceeded (composedLambdaType .zero 0 3).1 5 &&
      allSucceeded (composedLambdaType (.succ .zero) 0 3).1 5)
  ++ test "composed type lambda: both plans and dependent initial arguments preserve universe parameters"
    (allSucceeded (composedLambdaType (.var 0) 1).1 5 &&
      allSucceeded (composedLambdaType (.var 0) 1 1).1 5 &&
      allSucceeded (composedLambdaType (.var 0) 1 2).1 5 &&
      allSucceeded (composedLambdaType (.var 0) 1 3).1 5)
  ++ test "composed type lambda: the shared spine survives fresh per-item caches"
    (allSucceeded (composedLambdaType .zero).1 5 { clearEvery := 1 } &&
      allSucceeded (composedLambdaType .zero 0 3).1 5 { clearEvery := 1 })
  ++ test "composed type lambda: a variable plan consumes one argument from each origin"
    (composedLambdaTypeResult 0 .zero && composedLambdaTypeResult 0 (.succ .zero))
  ++ test "composed type lambda: the closed-body plan uses the combined argument list"
    (composedLambdaTypeResult 1 .zero && composedLambdaTypeResult 1 (.succ .zero))
  ++ test "composed type lambda: a three-step prefix preserves the dependent initial argument"
    (composedLambdaTypeResult 2 .zero && composedLambdaTypeResult 2 (.succ .zero))
  ++ test "composed type lambda: an initial argument must inhabit its specialized domain"
    (let (env, target) := composedLambdaType .zero 0 2 1; rowFailed env target)
  ++ test "composed type lambda: swapping the selected argument cannot change the declared carrier"
    (let (env, target) := composedLambdaType .zero 0 0 2; rowFailed env target)

/-- Call a polymorphic identity from a monomorphic function body. Universe
indices select entries in the declaration's explicit level table. -/
private def storePolymorphicCall (env : Ixon.Env) (identity : Address)
    (levels : Array Ixon.Univ) (domain : UInt64) (arguments : Array UInt64)
    (kind : Ix.DefKind := .defn) : Ixon.Env × Address :=
  storeConst env
    ⟨.defn ⟨kind, .safe, 0,
      .leanAll (.sort domain) (.leanAll (.var 0) (.var 1)),
      .leanLam (.sort domain) (.leanLam (.var 0)
        (.app (.app (.ref 0 arguments) (.var 1)) (.var 0)))⟩,
      #[], #[identity], levels⟩

private def polymorphicApplicationEnvironment : Ixon.Env := Id.run do
  let (env, identity) := polymorphicIdentity
  let (env, propCall) := storePolymorphicCall env identity #[.zero] 0 #[0]
  let (env, _) := storePolymorphicCall env identity #[.succ .zero] 0 #[0] .opaq
  let (env, _) := storePolymorphicCall env propCall #[.zero] 0 #[] .thm
  return env

/-- The source type retains a compound level until its two parameters are
substituted. This exercises simplification inside the returned Pi domain. -/
private def computedIdentity (level : Ixon.Univ) : Ixon.Env × Address :=
  storeConst {}
    ⟨.axio ⟨false, 2, .leanAll (.sort 0) (.leanAll (.var 0) (.var 1))⟩,
      #[], #[], #[level]⟩

private def simplifiedPolymorphicCall (imax : Bool) : Ixon.Env :=
  let (env, identity) := computedIdentity
    (if imax then .imax (.var 0) (.var 1) else .max (.var 0) (.var 1))
  let levels := if imax then #[.succ (.succ .zero), .zero] else #[.zero, .succ .zero]
  (storePolymorphicCall env identity levels 1 #[0, 1]).1

/-- A declaration type containing instantiated references must stay closed
when inferred beneath an unrelated active local. -/
private def scopedPolymorphicReferences : Bool :=
  let (env, function, carrier) := polymorphicReferences
  let propType := KExpr.mkSort (m := .anon) .mkZero
  let carrierType := KExpr.mkConst (m := .anon) ⟨carrier, ()⟩ #[levelOne]
  let expected := KExpr.mkAll () () carrierType carrierType
  let action : RecM .anon Bool := RecM.withLctxScope do
    let _ ← TcM.openBinder () () propType (.mkVar 0 ())
    let inferred ← RecM.inferCall (.mkConst ⟨function, ()⟩ #[levelOne])
    return inferred.addr == expected.addr && inferred.lbr == 0 && (← get).lctx.size == 1
  match TcM.runRec action (TcState.newLazyAnon env) with
  | .ok passed after => passed && after.lctx.size == 0 && after.env.nextFVarId == 1
  | .error _ _ => false

/-- Different level instances use different inference keys, while neither
returned type can capture the active local. -/
private def scopedPolymorphicInstances : Bool :=
  let propType := KExpr.mkSort (m := .anon) .mkZero
  let propIdentity := KExpr.mkAll () () propType (.mkAll () () (.mkVar 0 ()) (.mkVar 1 ()))
  let action : RecM .anon Bool := RecM.withLctxScope do
    let _ ← TcM.openBinder () () propType (.mkVar 0 ())
    let first ← RecM.inferCall (.mkConst ⟨polymorphicIdentity.2, ()⟩ #[.mkZero])
    let second ← RecM.inferCall (.mkConst ⟨polymorphicIdentity.2, ()⟩ #[levelOne])
    let state ← get
    return first.addr == propIdentity.addr && second.addr == identityType.addr &&
      first.addr != second.addr && first.lbr == 0 && second.lbr == 0 &&
      state.env.inferCache.size == 2 && state.lctx.size == 1
  match TcM.runRec action (TcState.newLazyAnon polymorphicIdentity.1) with
  | .ok passed after => passed && after.lctx.size == 0 && after.env.nextFVarId == 1
  | .error _ _ => false

private def polymorphicApplicationCases : TestSeq :=
  test "polymorphic calls: Prop/Type instances and a transitive theorem check"
    (allSucceeded polymorphicApplicationEnvironment 4 { clearEvery := 0 })
  ++ test "polymorphic calls: function bodies check with fresh per-item caches"
    (allSucceeded polymorphicApplicationEnvironment 4 { clearEvery := 1 })
  ++ test "polymorphic calls: max simplification exposes the Type domain"
    (allSucceeded (simplifiedPolymorphicCall false) 2)
  ++ test "polymorphic calls: imax simplification exposes the Prop domain"
    (allSucceeded (simplifiedPolymorphicCall true) 2)
  ++ test "polymorphic inference: nested reference arguments stay closed under an active local"
    scopedPolymorphicReferences
  ++ test "polymorphic inference: distinct instances retain closed types and separate cache keys"
    scopedPolymorphicInstances
  ++ test "polymorphic calls: a Type argument cannot use the Prop instance"
    (let (env, identity) := polymorphicIdentity
      let (env, target) := storePolymorphicCall env identity #[.zero, .succ .zero] 1 #[0]
      rowFailed env target)
  ++ test "polymorphic calls: missing universe arguments reject inside a function body"
    (let (env, identity) := polymorphicIdentity
      let (env, target) := storePolymorphicCall env identity #[.zero] 0 #[]
      rowFailed env target)
  ++ test "polymorphic calls: excess universe arguments reject inside a function body"
    (let (env, identity) := polymorphicIdentity
      let (env, target) := storePolymorphicCall env identity #[.zero] 0 #[0, 0]
      rowFailed env target)

/-- Every wrapper repeats the same closed carrier in its declared domain,
codomain, and lambda domain. The second and later references hit the cache
even when the driver clears caches before every declaration. -/
private def repeatedReferenceEnvironment : Ixon.Env := Id.run do
  let (env, function, carrier) := polymorphicReferences
  let wrapper : Address → Ixon.Univ → Array UInt64 → Ix.DefKind → Ixon.Constant :=
    fun callee level arguments kind =>
      ⟨.defn ⟨kind, .safe, 0,
        .leanAll (.ref 0 #[0]) (.ref 0 #[0]),
        .leanLam (.ref 0 #[0]) (.app (.ref 1 arguments) (.var 0))⟩,
        #[], #[carrier, callee], #[level]⟩
  let (env, first) := storeConst env (wrapper function .zero #[0] .defn)
  let (env, _) := storeConst env (wrapper function (.succ .zero) #[0] .opaq)
  let (env, _) := storeConst env (wrapper first .zero #[] .thm)
  return env

/-- The selected entry is populated by real inference, then reused in two
different local scopes. Cache keys and closed returned types stay stable. -/
private def cachedInferenceAcrossScopes (term expected : KExpr .anon)
    (state : TcState .anon) : Bool :=
  let inferOnly := state.inferOnly
  let propType := KExpr.mkSort (m := .anon) .mkZero
  let action : RecM .anon Bool := do
    let first ← RecM.inferCall term
    let key ← TcM.inferKey term
    let initial ← get
    let reuse : RecM .anon Bool := RecM.withLctxScope do
      let _ ← TcM.openBinder () () propType (.mkVar 0 ())
      let activeKey ← TcM.inferKey term
      let result ← RecM.inferCall term
      return activeKey == key && result.addr == expected.addr && result.lbr == 0 &&
        (← get).lctx.size == 1
    let second ← reuse
    let third ← reuse
    let final ← get
    return first.addr == expected.addr && second && third &&
      (if inferOnly then initial.env.inferOnlyCache[key]?.isSome &&
        final.env.inferOnlyCache.size == initial.env.inferOnlyCache.size && final.env.inferCache.isEmpty
      else initial.env.inferCache[key]?.isSome &&
        final.env.inferCache.size == initial.env.inferCache.size && final.env.inferOnlyCache.isEmpty)
  match TcM.runRec action state with
  | .ok passed after => passed && after.lctx.size == 0 && after.env.nextFVarId == 2
  | .error _ _ => false

private def cachedConstantAcrossScopes (source : Ixon.Env × Address)
    (arguments : Array (KUniv .anon)) (expected : KExpr .anon) (inferOnly : Bool) : Bool :=
  cachedInferenceAcrossScopes (.mkConst ⟨source.2, ()⟩ arguments) expected
    { TcState.newLazyAnon source.1 with inferOnly }

/-- A deliberately different result in the ineligible partition makes the
selection policy observable. Full mode must compute a checked answer when
only that entry exists; inference-only mode must prefer a full result. -/
private def inferenceCachePriority (term knownType : KExpr .anon)
    (initial : TcState .anon) (fullHit : Bool) : Bool :=
  let sentinel := KExpr.mkSort (m := .anon) .mkZero
  let action : RecM .anon Bool := do
    let expected ← RecM.inferOnlyCall term
    let key ← TcM.inferKey term
    modify fun state => { state with inferOnly := fullHit, env := { state.env with
      inferCache := if fullHit then state.env.inferCache.insert key expected else state.env.inferCache
      inferOnlyCache := state.env.inferOnlyCache.insert key sentinel } }
    let result ← RecM.inferCall term
    let state ← get
    return result.addr == knownType.addr && result.addr != sentinel.addr &&
      state.env.inferCache[key]?.any (fun cached => cached.addr == expected.addr) &&
      state.env.inferOnlyCache[key]?.any (fun cached => cached.addr == sentinel.addr)
  match TcM.runRec action initial with
  | .ok passed _ => passed
  | .error _ _ => false

private def constantCachePriority (fullHit : Bool) : Bool :=
  inferenceCachePriority (.mkConst ⟨polymorphicIdentity.2, ()⟩ #[levelOne]) identityType
    (TcState.newLazyAnon polymorphicIdentity.1) fullHit

/-- Alternating two instances after their first use must retrieve the type
for that instance, while retaining only two closed constant cache entries. -/
private def repeatedConstantInstances : Bool :=
  let propType := KExpr.mkSort (m := .anon) .mkZero
  let propIdentity := KExpr.mkAll () () propType (.mkAll () () (.mkVar 0 ()) (.mkVar 1 ()))
  let propTerm := KExpr.mkConst (m := .anon) ⟨polymorphicIdentity.2, ()⟩ #[.mkZero]
  let typeTerm := KExpr.mkConst (m := .anon) ⟨polymorphicIdentity.2, ()⟩ #[levelOne]
  let action : RecM .anon Bool := do
    let _ ← RecM.inferCall propTerm
    let _ ← RecM.inferCall typeTerm
    let propResult ← RecM.inferCall propTerm
    let typeResult ← RecM.inferCall typeTerm
    return propTerm.addr != typeTerm.addr && propResult.addr == propIdentity.addr &&
      typeResult.addr == identityType.addr && (← get).env.inferCache.size == 2
  match TcM.runRec action (TcState.newLazyAnon polymorphicIdentity.1) with
  | .ok passed _ => passed
  | .error _ _ => false

private def constantCacheCases : TestSeq :=
  test "constant cache: repeated carrier references and transitive calls check"
    (allSucceeded repeatedReferenceEnvironment 5 { clearEvery := 0 })
  ++ test "constant cache: repeated references within one declaration survive per-item clearing"
    (allSucceeded repeatedReferenceEnvironment 5 { clearEvery := 1 })
  ++ test "constant cache: polymorphic full results survive two fresh local scopes"
    (cachedConstantAcrossScopes polymorphicIdentity #[levelOne] identityType false)
  ++ test "constant cache: polymorphic inference-only results survive two fresh local scopes"
    (cachedConstantAcrossScopes polymorphicIdentity #[levelOne] identityType true)
  ++ test "constant cache: empty universe substitution reuses a monomorphic definition type"
    (cachedConstantAcrossScopes (monomorphicIdentity (.succ .zero)) #[] identityType false)
  ++ test "constant cache: repeated max substitution retains its simplified type"
    (cachedConstantAcrossScopes (computedIdentity (.max (.var 0) (.var 1)))
      #[.mkZero, levelOne] identityType false)
  ++ test "constant cache: repeated imax substitution retains its simplified type"
    (let propType := KExpr.mkSort (m := .anon) .mkZero
      let expected := KExpr.mkAll () () propType (.mkAll () () (.mkVar 0 ()) (.mkVar 1 ()))
      cachedConstantAcrossScopes (computedIdentity (.imax (.var 0) (.var 1)))
        #[levelOne, .mkZero] expected true)
  ++ test "constant cache: inference-only mode gives the full result priority"
    (constantCachePriority true)
  ++ test "constant cache: full mode ignores an inference-only answer and checks the constant"
    (constantCachePriority false)
  ++ test "constant cache: alternating universe instances retrieve their own cached types"
    repeatedConstantInstances

/-- Repeated `Sort u` domains in both the declaration and its value exercise
sort hits under fresh local scopes: `fun P Q p q => p`, at Prop and Type. -/
private def repeatedSortEnvironment : Ixon.Env := Id.run do
  let definition : Ixon.Univ → Ix.DefKind → Ixon.Constant := fun level kind =>
    ⟨.defn ⟨kind, .safe, 0,
      .leanAll (.sort 0) (.leanAll (.sort 0)
        (.leanAll (.var 1) (.leanAll (.var 1) (.var 3)))),
      .leanLam (.sort 0) (.leanLam (.sort 0)
        (.leanLam (.var 1) (.leanLam (.var 1) (.var 1))))⟩, #[], #[], #[level]⟩
  let (env, _) := storeConst {} (definition .zero .defn)
  let (env, _) := storeConst env (definition (.succ .zero) .opaq)
  return env

/-- Warm a constant, then infer a sort and another instance of the loaded
constant inside a scope. Both successful cleanup and an error from an
inference-only call retain the original entry and the intervening writes. -/
private def constantCacheThroughInference (inferOnly fail : Bool) : Bool :=
  let id : KId .anon := ⟨polymorphicIdentity.2, ()⟩
  let term := KExpr.mkConst (m := .anon) id #[levelOne]
  let other := KExpr.mkConst (m := .anon) id #[.mkZero]
  let propType := KExpr.mkSort (m := .anon) .mkZero
  let propIdentity := KExpr.mkAll () () propType (.mkAll () () (.mkVar 0 ()) (.mkVar 1 ()))
  let action : RecM .anon Bool := do
    let first ← RecM.inferCall term
    let key ← TcM.inferKey term
    let otherKey ← TcM.inferKey other
    let sortKey ← TcM.inferKey propType
    let initial ← get
    let expectedExit ← try
      RecM.withLctxScope do
        let _ ← TcM.openBinder () () propType (.mkVar 0 ())
        let _ ← RecM.inferCall propType
        let _ ← RecM.inferCall other
        if fail then
          let _ ← RecM.inferOnlyCall (.mkFVar ⟨99⟩ ())
          return false
        return true
    catch _ => pure fail
    let later ← get
    let cache := if inferOnly then later.env.inferOnlyCache else later.env.inferCache
    let opposite := if inferOnly then later.env.inferCache else later.env.inferOnlyCache
    let reused ← RecM.inferCall term
    return expectedExit && first.addr == identityType.addr && reused.addr == first.addr &&
      key != otherKey && key != sortKey && otherKey != sortKey &&
      cache[key]?.any (fun cached => cached.addr == first.addr) &&
      cache[otherKey]?.any (fun cached => cached.addr == propIdentity.addr) &&
      cache[sortKey]?.any (fun cached => cached.addr == (.mkSort levelOne : KExpr .anon).addr) &&
      opposite.isEmpty && later.env.consts.size == initial.env.consts.size &&
      (later.env.get? id).map (·.ty.addr) == (initial.env.get? id).map (·.ty.addr) &&
      later.lctx.size == 0 && later.env.nextFVarId == 1 && later.inferOnly == inferOnly
  match TcM.runRec action { TcState.newLazyAnon polymorphicIdentity.1 with inferOnly } with
  | .ok passed _ => passed
  | .error _ _ => false

/-- Populate both partitions, clear them through the production operation,
then re-infer with a loaded source under the selected policy. -/
private def inferenceAfterClearing (inferOnly : Bool) : Bool :=
  let id : KId .anon := ⟨polymorphicIdentity.2, ()⟩
  let term := KExpr.mkConst (m := .anon) id #[levelOne]
  let propType := KExpr.mkSort (m := .anon) .mkZero
  let action : RecM .anon Bool := do
    let _ ← RecM.inferOnlyCall term
    let _ ← RecM.inferCall term
    let _ ← RecM.inferOnlyCall propType
    let _ ← RecM.inferCall propType
    let key ← TcM.inferKey term
    let sortKey ← TcM.inferKey propType
    let populated ← get
    modify fun state => { state with inferOnly, env := state.env.clearReductionCaches }
    let cleared ← get
    let constantResult ← RecM.inferCall term
    let sortResult ← RecM.inferCall propType
    let final ← get
    let cache := if inferOnly then final.env.inferOnlyCache else final.env.inferCache
    let opposite := if inferOnly then final.env.inferCache else final.env.inferOnlyCache
    return populated.env.inferCache.size == 2 && populated.env.inferOnlyCache.size == 2 &&
      cleared.env.inferCache.isEmpty && cleared.env.inferOnlyCache.isEmpty &&
      (cleared.env.get? id).isSome && cleared.env.consts.size == populated.env.consts.size &&
      constantResult.addr == identityType.addr && sortResult.addr == (.mkSort levelOne : KExpr .anon).addr &&
      cache[key]?.isSome && cache[sortKey]?.isSome && cache.size == 2 && opposite.isEmpty
  match TcM.runRec action (TcState.newLazyAnon polymorphicIdentity.1) with
  | .ok passed _ => passed
  | .error _ _ => false

private def cacheInvariantCases : TestSeq :=
  test "cache invariants: repeated sort domains check with persistent caches"
    (allSucceeded repeatedSortEnvironment 2 { clearEvery := 0 })
  ++ test "cache invariants: repeated sort domains check with per-item clearing"
    (allSucceeded repeatedSortEnvironment 2 { clearEvery := 1 })
  ++ test "cache invariants: full sort results survive two fresh scopes"
    (cachedInferenceAcrossScopes (.mkSort .mkZero) (.mkSort levelOne) (TcState.ofEnvAnon {}))
  ++ test "cache invariants: inference-only sort results survive two fresh scopes"
    (cachedInferenceAcrossScopes (.mkSort .mkZero) (.mkSort levelOne)
      { TcState.ofEnvAnon {} with inferOnly := true })
  ++ test "cache invariants: sort inference gives the full result priority"
    (inferenceCachePriority (.mkSort .mkZero) (.mkSort levelOne) (TcState.ofEnvAnon {}) true)
  ++ test "cache invariants: full sort inference ignores the inference-only entry"
    (inferenceCachePriority (.mkSort .mkZero) (.mkSort levelOne) (TcState.ofEnvAnon {}) false)
  ++ test "cache invariants: full entries survive other inference and scope cleanup"
    (constantCacheThroughInference false false)
  ++ test "cache invariants: inference-only entries survive other inference and scope cleanup"
    (constantCacheThroughInference true false)
  ++ test "cache invariants: full entries and policy survive failed inference-only scope"
    (constantCacheThroughInference false true)
  ++ test "cache invariants: inference-only entries and policy survive failed scope"
    (constantCacheThroughInference true true)
  ++ test "cache invariants: clearing both partitions permits fresh full inference"
    (inferenceAfterClearing false)
  ++ test "cache invariants: clearing both partitions permits fresh inference-only synthesis"
    (inferenceAfterClearing true)

/-- Preserve warm constant and sort entries through entire recursive calls.
The application checks a lambda argument; the lambda itself uses the watched
constant twice. Replaying the composite result also exercises a root cache hit.
These are operational preservation cases; composite cache-hit typing remains
a separate refinement boundary. -/
private def cacheAfterComposite (shape : Nat) (inferOnly stats surroundingScope : Bool) : Bool :=
  let id : KId .anon := ⟨polymorphicIdentity.2, ()⟩
  let watched := KExpr.mkConst (m := .anon) id #[levelOne]
  let sortType := KExpr.mkSort (m := .anon) levelOne
  let useIdentity : KExpr .anon → KExpr .anon := fun arg =>
    .mkApp (.mkApp watched (.mkVar 1 ())) arg
  let body := KExpr.mkLam () () sortType
    (.mkLam () () (.mkVar 0 ()) (useIdentity (useIdentity (.mkVar 0 ()))))
  let application := KExpr.mkApp (.mkApp (.mkConst id #[levelTwo]) identityType) body
  let term := if shape == 0 then identityType else if shape == 1 then body else application
  let expected := if shape == 0 then KExpr.mkSort levelTwo else identityType
  let action : RecM .anon Bool := do
    let constantType ← RecM.inferCall watched
    let sortResult ← RecM.inferCall sortType
    let key ← TcM.inferKey watched
    let sortKey ← TcM.inferKey sortType
    let initial ← get
    RecM.withLctxScope do
      if surroundingScope then
        let _ ← TcM.openBinder () () sortType (.mkVar 0 ())
        pure ()
      let activeSize := (← get).lctx.size
      let rootKey ← TcM.inferKey term
      let result ← RecM.inferCall term
      let after ← get
      let cache := if inferOnly then after.env.inferOnlyCache else after.env.inferCache
      let oldCache := if inferOnly then initial.env.inferOnlyCache else initial.env.inferCache
      let opposite := if inferOnly then after.env.inferCache else after.env.inferOnlyCache
      let replay ← RecM.inferCall term
      let constantReuse ← RecM.inferCall watched
      let sortReuse ← RecM.inferCall sortType
      let final ← get
      return result.addr == expected.addr && result.lbr == 0 && replay.addr == result.addr &&
        constantReuse.addr == constantType.addr && constantType.addr == identityType.addr &&
        sortReuse.addr == sortResult.addr && sortResult.addr == (.mkSort levelTwo : KExpr .anon).addr &&
        rootKey != key && rootKey != sortKey && key != sortKey &&
        cache[key]?.map (·.addr) == oldCache[key]?.map (·.addr) &&
        cache[sortKey]?.map (·.addr) == oldCache[sortKey]?.map (·.addr) &&
        cache[rootKey]?.any (fun cached => cached.addr == result.addr) &&
        cache.size > oldCache.size && opposite.isEmpty &&
        after.env.consts.size == initial.env.consts.size &&
        (after.env.get? id).map (·.ty.addr) == (initial.env.get? id).map (·.ty.addr) &&
        after.lctx.size == activeSize && after.inferOnly == inferOnly &&
        (if stats && shape != 0 then after.deqCalls > initial.deqCalls
         else after.deqCalls == initial.deqCalls) && final.deqCalls == after.deqCalls
  match TcM.runRec action { TcState.newLazyAnon polymorphicIdentity.1 with inferOnly, stats } with
  | .ok passed after => passed && after.lctx.size == 0 && after.inferOnly == inferOnly
  | .error _ _ => false

private def recursiveCacheEnvironment : Ixon.Env := Id.run do
  let (env, identity) := polymorphicIdentity
  let nestedCall : Ixon.Expr → Ixon.Expr := fun arg =>
    .app (.app (.ref 0 #[0]) (.var 1)) arg
  let definition : Ixon.Univ → Ix.DefKind → Ixon.Constant := fun level kind =>
    ⟨.defn ⟨kind, .safe, 0,
      .leanAll (.sort 0) (.leanAll (.var 0) (.var 1)),
      .leanLam (.sort 0) (.leanLam (.var 0) (nestedCall (nestedCall (.var 0))))⟩,
      #[], #[identity], #[level]⟩
  let (env, _) := storeConst env (definition (.succ .zero) .defn)
  let (env, _) := storeConst env (definition (.succ (.succ .zero)) .opaq)
  return env

private def recursiveCacheCases : TestSeq :=
  test "recursive cache: full dependent type inference retains warm sort and constant entries"
    (cacheAfterComposite 0 false false false)
  ++ test "recursive cache: inference-only dependent type inference retains warm entries"
    (cacheAfterComposite 0 true false false)
  ++ test "recursive cache: nested lambda applications retain repeatedly used constant entries"
    (cacheAfterComposite 1 false false false)
  ++ test "recursive cache: application with a lambda argument retains warm entries"
    (cacheAfterComposite 2 false false false)
  ++ test "recursive cache: hash-conversion statistics preserve entries and root replay is read-only"
    (cacheAfterComposite 2 false true false)
  ++ test "recursive cache: nested inference preserves an existing outer local scope"
    (cacheAfterComposite 2 false true true)
  ++ test "recursive cache: nested polymorphic calls check with persistent caches"
    (allSucceeded recursiveCacheEnvironment 3 { clearEvery := 0 })
  ++ test "recursive cache: nested polymorphic calls check with per-item clearing"
    (allSucceeded recursiveCacheEnvironment 3 { clearEvery := 1 })

/-- Sharing and recursor-rule conversion exercise the restricted converter
state. These fixtures test lookup and inference, not recursor or quotient admission. -/
private def lazyCacheDependency (kind : Nat) : Ixon.Constant :=
  let type := Ixon.Expr.leanAll (.sort 0) (.leanAll (.var 0) (.var 1))
  let value := Ixon.Expr.leanLam (.sort 0) (.leanLam (.var 0) (.var 0))
  let info := match kind with
    | 0 => Ixon.ConstantInfo.axio ⟨false, 0, .share 0⟩
    | 1 => .defn ⟨.defn, .safe, 0, .share 0, .share 1⟩
    | 2 => .recr ⟨false, false, 0, 0, 0, 0, 0, .share 0,
        #[⟨0, .share 1⟩, ⟨1, .share 1⟩]⟩
    | _ => .quot ⟨.type, 0, .share 0⟩
  ⟨info, #[type, value], #[], #[.succ .zero]⟩

/-- Warm A, infer a cold B directly or inside a recursive body, and reuse A.
The new declaration and block are retained while both old cache slots survive. -/
private def cacheAcrossLazyDependency (kind shape : Nat) (inferOnly : Bool) : Bool :=
  let (source, warmAddr) := polymorphicIdentity
  let (source, coldAddr) := storeConst source (lazyCacheDependency kind)
  let warmId : KId .anon := ⟨warmAddr, ()⟩
  let coldId : KId .anon := ⟨coldAddr, ()⟩
  let warm := KExpr.mkConst (m := .anon) warmId #[levelOne]
  let cold := KExpr.mkConst (m := .anon) coldId #[]
  let sortType := KExpr.mkSort (m := .anon) levelOne
  let body := KExpr.mkLam () () sortType (.mkLam () () (.mkVar 0 ())
    (.mkApp (.mkApp cold (.mkVar 1 ())) (.mkVar 0 ())))
  let term := if shape == 0 then cold else if shape == 1 then body else
    KExpr.mkApp (.mkApp (.mkConst warmId #[levelTwo]) identityType) body
  let action : RecM .anon Bool := do
    let expected ← RecM.inferCall warm
    let key ← TcM.inferKey warm
    RecM.withLctxScope do
      let _ ← TcM.openBinder () () sortType (.mkVar 0 ())
      let before ← get
      let result ← RecM.inferCall term
      let loaded ← get
      let reused ← RecM.inferCall warm
      let replay ← RecM.inferCall term
      let _ ← liftM (TcM.lazyIngressAddr (m := .anon) coldAddr)
      let after ← get
      return expected.addr == identityType.addr && result.addr == expected.addr &&
        reused.addr == expected.addr && replay.addr == result.addr && warmAddr != coldAddr &&
        (before.env.get? coldId).isNone && (loaded.env.get? coldId).isSome &&
        loaded.env.consts.size == before.env.consts.size + 1 &&
        (loaded.env.get? warmId).map (·.ty.addr) == (before.env.get? warmId).map (·.ty.addr) &&
        loaded.env.blocks[coldId]?.any (fun members => members.size == 1 &&
          members[0]?.any (fun member => member.addr == coldAddr)) &&
        loaded.env.inferCache[key]?.map (·.addr) == before.env.inferCache[key]?.map (·.addr) &&
        loaded.env.inferOnlyCache[key]?.map (·.addr) == before.env.inferOnlyCache[key]?.map (·.addr) &&
        loaded.faultedAddrs.contains coldAddr && loaded.faultedAddrs.contains warmAddr &&
        loaded.lctx.size == before.lctx.size && loaded.inferOnly == inferOnly &&
        loaded.env.nextFVarId >= before.env.nextFVarId &&
        after.env.inferCache.size == loaded.env.inferCache.size &&
        after.env.inferOnlyCache.size == loaded.env.inferOnlyCache.size &&
        after.env.intern.exprs.size == loaded.env.intern.exprs.size &&
        after.env.intern.univs.size == loaded.env.intern.univs.size &&
        after.env.consts.size == loaded.env.consts.size && after.deqCalls == loaded.deqCalls
  match TcM.runRec action { TcState.newLazyAnon source with inferOnly, stats := true } with
  | .ok passed after => passed && after.lctx.size == 0 && after.inferOnly == inferOnly
  | .error _ _ => false

/-- Errors retain partial intern progress and the fault marker. Retrying a
failed address is deduplicated and returns unknownConst without reconversion. -/
private def cacheAcrossLazyFailure (kind : Nat) (inferOnly : Bool) : Bool :=
  let (source, warmAddr) := polymorphicIdentity
  let missing := Address.blake3 "consistency-lazy-cache-missing".toUTF8
  let wrong := Address.blake3 "consistency-lazy-cache-wrong-hash".toUTF8
  let level : Ixon.Univ := .succ (.succ (.succ (.succ (.succ .zero))))
  let broken : Ixon.Constant := if kind == 2 then
    ⟨.defn ⟨.defn, .safe, 0, .sort 0, .share 9⟩, #[], #[], #[level]⟩
    else ⟨.recr ⟨false, false, 0, 0, 0, 0, 0, .sort 0,
      #[⟨0, .sort 0⟩, ⟨1, .share 9⟩]⟩, #[], #[], #[level]⟩
  let (source, coldAddr) := if kind == 0 then (source, missing)
    else if kind == 1 then
      ({source with consts := source.consts.insert wrong (.ofConstant (lazyCacheDependency 0))}, wrong)
    else storeConst source broken
  let warmId : KId .anon := ⟨warmAddr, ()⟩
  let coldId : KId .anon := ⟨coldAddr, ()⟩
  let warm := KExpr.mkConst (m := .anon) warmId #[levelOne]
  let action : RecM .anon Bool := do
    let expected ← RecM.inferCall warm
    let key ← TcM.inferKey warm
    RecM.withLctxScope do
      let _ ← TcM.openBinder () () (.mkSort levelOne) (.mkVar 0 ())
      let before ← get
      let rejected ← try
        let _ ← RecM.inferCall (.mkConst coldId #[])
        pure false
      catch err =>
        let fragment := if kind == 0 then "unknown constant" else if kind == 1 then
          "fails integrity check" else "invalid Share index 9"
        pure (((toString err).splitOn fragment).length > 1)
      let failed ← get
      let deduplicated ← try
        let _ ← liftM (TcM.getConst coldId)
        pure false
      catch err =>
        match err with
        | .unknownConst addr => pure (addr == coldAddr)
        | _ => pure false
      let reused ← RecM.inferCall warm
      let after ← get
      return rejected && deduplicated && reused.addr == expected.addr &&
        (failed.env.get? coldId).isNone && failed.env.consts.size == before.env.consts.size &&
        failed.env.blocks.size == before.env.blocks.size && failed.faultedAddrs.contains coldAddr &&
        (failed.env.get? warmId).map (·.ty.addr) == (before.env.get? warmId).map (·.ty.addr) &&
        failed.env.inferCache[key]?.map (·.addr) == before.env.inferCache[key]?.map (·.addr) &&
        failed.env.inferOnlyCache[key]?.map (·.addr) == before.env.inferOnlyCache[key]?.map (·.addr) &&
        failed.env.inferCache.size == before.env.inferCache.size &&
        failed.env.inferOnlyCache.size == before.env.inferOnlyCache.size &&
        (if kind >= 2 then failed.env.intern.exprs.size > before.env.intern.exprs.size &&
          failed.env.intern.univs.size > before.env.intern.univs.size
         else failed.env.intern.exprs.size == before.env.intern.exprs.size &&
          failed.env.intern.univs.size == before.env.intern.univs.size) &&
        failed.lctx.size == before.lctx.size && failed.env.nextFVarId == before.env.nextFVarId &&
        failed.inferOnly == inferOnly && after.env.intern.exprs.size == failed.env.intern.exprs.size &&
        after.env.intern.univs.size == failed.env.intern.univs.size
  match TcM.runRec action { TcState.newLazyAnon source with inferOnly } with
  | .ok passed after => passed && after.lctx.size == 0 && after.inferOnly == inferOnly
  | .error _ _ => false

private def lazyCacheCases : TestSeq :=
  test "lazy cache: fresh axiom loading retains a warm full witness"
    (cacheAcrossLazyDependency 0 0 false)
  ++ test "lazy cache: fresh definition loading retains an inference-only witness"
    (cacheAcrossLazyDependency 1 0 true)
  ++ test "lazy cache: recursor rule conversion retains a warm witness"
    (cacheAcrossLazyDependency 2 0 false)
  ++ test "lazy cache: quotient conversion retains a warm witness"
    (cacheAcrossLazyDependency 3 0 false)
  ++ test "lazy cache: a lambda loads a cold dependency and retains a warm witness"
    (cacheAcrossLazyDependency 1 1 false)
  ++ test "lazy cache: an application loads a dependency inside its lambda argument"
    (cacheAcrossLazyDependency 1 2 false)
  ++ test "lazy cache: a missing source preserves warm entries and records the fault"
    (cacheAcrossLazyFailure 0 false)
  ++ test "lazy cache: an integrity failure preserves warm entries and records the fault"
    (cacheAcrossLazyFailure 1 true)
  ++ test "lazy cache: a failed definition retains partial conversion and the full witness"
    (cacheAcrossLazyFailure 2 false)
  ++ test "lazy cache: a failed recursor retains partial conversion and the inference-only witness"
    (cacheAcrossLazyFailure 3 true)

/-- Populate both partitions so every block regression checks two live slots. -/
private def warmBothCaches (term : KExpr .anon) : RecM .anon (KExpr .anon) := do
  let policy := (← get).inferOnly
  modify fun state => {state with inferOnly := true}
  let _ ← RecM.inferCall term
  modify fun state => {state with inferOnly := false}
  let result ← RecM.inferCall term
  modify fun state => {state with inferOnly := policy}
  return result

private def warmSlotsRetained (key : Address × Address) (before after : TcState .anon) : Bool :=
  before.env.inferCache[key]?.isSome && before.env.inferOnlyCache[key]?.isSome &&
  after.env.inferCache[key]?.map (·.addr) == before.env.inferCache[key]?.map (·.addr) &&
  after.env.inferOnlyCache[key]?.map (·.addr) == before.env.inferOnlyCache[key]?.map (·.addr)

private def cacheBlock (recursor : Bool) : Ixon.Constant :=
  let type := Ixon.Expr.leanAll (.sort 0) (.leanAll (.var 0) (.var 1))
  let value := Ixon.Expr.leanLam (.sort 0) (.leanLam (.var 0) (.var 0))
  let first : Ixon.MutConst := .defn ⟨.defn, .safe, 0, .share 0, .recur 1 #[]⟩
  let second : Ixon.MutConst := if recursor then
    .recr ⟨false, false, 0, 0, 0, 0, 0, .share 0, #[⟨0, .share 1⟩, ⟨1, .share 1⟩]⟩
    else .defn ⟨.defn, .safe, 0, .share 0, .share 1⟩
  ⟨.muts #[first, second], #[type, value], #[], #[.succ .zero]⟩

/-- A projection loads the whole block. A partial preload warms the first
member without recording the block; publication must preserve that member too. -/
private def cacheAcrossBlock (recursor preloaded : Bool) (shape : Nat) (inferOnly : Bool) : Bool :=
  let (source, warmAddr) := polymorphicIdentity
  let block := cacheBlock recursor
  let (source, blockAddr) := storeMutsWithProjs source block
  let first : KId .anon := ⟨defnProjAddr blockAddr 0, ()⟩
  let second : KId .anon := ⟨if recursor then recrProjAddr blockAddr 1 else defnProjAddr blockAddr 1, ()⟩
  let requested := if preloaded || recursor then second else first
  let sibling := if preloaded || recursor then first else second
  let warmId : KId .anon := ⟨warmAddr, ()⟩
  let warm := KExpr.mkConst (m := .anon) warmId #[levelOne]
  let cold := KExpr.mkConst (m := .anon) requested #[]
  let sortType := KExpr.mkSort (m := .anon) levelOne
  let body := KExpr.mkLam () () sortType (.mkLam () () (.mkVar 0 ())
    (.mkApp (.mkApp cold (.mkVar 1 ())) (.mkVar 0 ())))
  let term := if shape == 0 then cold else if shape == 1 then body else
    KExpr.mkApp (.mkApp (.mkConst warmId #[levelTwo]) identityType) body
  let action : RecM .anon Bool := do
    let expected ← warmBothCaches warm
    let key ← TcM.inferKey warm
    if preloaded then
      let state ← get
      let .ok trace converted := prepareAnonBlock source block blockAddr state.env | return false
      let some entry := trace.allEntries[0]? | return false
      modify fun state => {state with env := converted.insert entry.1 entry.2}
      let _ ← warmBothCaches (.mkConst first #[])
    let firstKey ← TcM.inferKey (.mkConst first #[])
    let before ← get
    let result ← RecM.inferCall term
    let loaded ← get
    let reused ← RecM.inferCall warm
    let replay ← RecM.inferCall term
    let beforeDedup ← get
    let _ ← liftM (TcM.lazyIngressAddr (m := .anon) sibling.addr)
    let after ← get
    let overlap := if preloaded then
      warmSlotsRetained firstKey before loaded &&
      match before.env.get? first, loaded.env.get? first with
      | some (.defn (kind := k) (safety := s) (hints := h) (lvls := l) (ty := t) (val := v) (block := b) ..),
        some (.defn (kind := k') (safety := s') (hints := h') (lvls := l') (ty := t') (val := v') (block := b') ..) =>
          k == k' && s == s' && h == h' && l == l' && t.addr == t'.addr && v.addr == v'.addr && b == b'
      | _, _ => false
      else true
    return result.addr == expected.addr && expected.addr == identityType.addr &&
      reused.addr == expected.addr && replay.addr == result.addr && overlap &&
      warmSlotsRetained key before loaded && (before.env.get? requested).isNone &&
      !before.env.blocks.contains ⟨blockAddr, ()⟩ &&
      (loaded.env.get? first).isSome && (loaded.env.get? second).isSome &&
      loaded.env.consts.size == before.env.consts.size + (if preloaded then 1 else 2) &&
      loaded.env.blocks[(⟨blockAddr, ()⟩ : KId .anon)]?.any (fun members => members == #[first, second]) &&
      !beforeDedup.faultedAddrs.contains sibling.addr && after.faultedAddrs.contains sibling.addr &&
      after.env.consts.size == beforeDedup.env.consts.size &&
      after.env.intern.exprs.size == beforeDedup.env.intern.exprs.size &&
      after.env.intern.univs.size == beforeDedup.env.intern.univs.size &&
      after.env.inferCache.size == beforeDedup.env.inferCache.size &&
      after.env.inferOnlyCache.size == beforeDedup.env.inferOnlyCache.size &&
      after.env.nextFVarId == beforeDedup.env.nextFVarId && after.inferOnly == inferOnly
  match TcM.runRec action { TcState.newLazyAnon source with inferOnly } with
  | .ok passed _ => passed
  | .error _ _ => false

/-- Inductive and constructor projections exercise flattened publication.
This tests loader framing, without claiming inductive admission soundness. -/
private def cacheAcrossInductiveBlock (constructor : Bool) : Bool :=
  let (source, blockAddr) := envInductive
  let (source, warmAddr) := storeConst source
    ⟨.axio ⟨false, 1, .leanAll (.sort 0) (.leanAll (.var 0) (.var 1))⟩, #[], #[], #[.var 0]⟩
  let induct : KId .anon := ⟨indcProjAddr blockAddr 0, ()⟩
  let ctor : KId .anon := ⟨ctorProjAddr blockAddr 0 0, ()⟩
  let warm := KExpr.mkConst (m := .anon) ⟨warmAddr, ()⟩ #[levelOne]
  let action : RecM .anon Bool := do
    let expected ← warmBothCaches warm
    let key ← TcM.inferKey warm
    let before ← get
    let result ← RecM.inferCall (.mkConst (if constructor then ctor else induct) #[])
    let loaded ← get
    let reused ← RecM.inferCall warm
    return warmSlotsRetained key before loaded && reused.addr == expected.addr &&
      result.addr == (if constructor then (KExpr.mkConst induct #[]).addr else sort1K.addr) &&
      loaded.env.consts.size == before.env.consts.size + 2 &&
      loaded.env.blocks[(⟨blockAddr, ()⟩ : KId .anon)]?.any (fun members => members == #[induct, ctor]) &&
      match loaded.env.get? induct, loaded.env.get? ctor with
      | some (.indc (ctors := ctors) ..), some (.ctor (induct := parent) ..) =>
          ctors == #[ctor] && parent == induct
      | _, _ => false
  match TcM.runRec action (TcState.newLazyAnon source) with
  | .ok passed _ => passed
  | .error _ _ => false

/-- A failure can retain partial conversion, or even a complete publication
when the requested block root has no declaration entry. Retries deduplicate. -/
private def cacheAcrossBlockFailure (kind : Nat) : Bool :=
  let (source, warmAddr) := polymorphicIdentity
  let level : Ixon.Univ := .succ (.succ (.succ (.succ (.succ .zero))))
  let first : Ixon.MutConst := .defn ⟨.defn, .safe, 0, .sort 0, .sort 0⟩
  let second : Ixon.MutConst := .defn ⟨.defn, .safe, 0, .sort 0,
    if kind == 3 then .share 9 else .sort 0⟩
  let (source, blockAddr) := storeMutsWithProjs source ⟨.muts #[first, second], #[], #[], #[level]⟩
  let firstAddr := defnProjAddr blockAddr 0
  let secondAddr := defnProjAddr blockAddr 1
  let source := if kind == 0 then {source with consts := source.consts.erase blockAddr}
    else if kind == 1 then
      {source with consts := source.consts.insert blockAddr (.ofConstant (lazyCacheDependency 0))}
    else if kind == 2 then {source with consts := source.consts.erase secondAddr} else source
  let requested : KId .anon := ⟨if kind == 4 then blockAddr else firstAddr, ()⟩
  let warm := KExpr.mkConst (m := .anon) ⟨warmAddr, ()⟩ #[levelOne]
  let action : RecM .anon Bool := do
    let expected ← warmBothCaches warm
    let key ← TcM.inferKey warm
    let before ← get
    let rejected ← try
      let _ ← liftM (TcM.getConst requested)
      pure false
    catch err =>
      let fragment := if kind == 0 then "absent" else if kind == 1 then "fails integrity check"
        else if kind == 2 then "not present in env" else if kind == 3 then "invalid Share index 9"
        else "unknown constant"
      pure (((toString err).splitOn fragment).length > 1)
    let failed ← get
    let retry ← try
      let _ ← liftM (TcM.getConst requested)
      pure false
    catch err =>
      match err with
      | .unknownConst addr => pure (addr == requested.addr)
      | _ => pure false
    let reused ← RecM.inferCall warm
    let after ← get
    return rejected && retry && reused.addr == expected.addr && warmSlotsRetained key before failed &&
      (failed.env.get? requested).isNone && failed.faultedAddrs.contains requested.addr &&
      failed.env.consts.size == before.env.consts.size + (if kind == 4 then 2 else 0) &&
      failed.env.blocks.size == before.env.blocks.size + (if kind == 4 then 1 else 0) &&
      (if kind == 4 then (failed.env.get? ⟨firstAddr, ()⟩).isSome &&
        (failed.env.get? ⟨secondAddr, ()⟩).isSome else true) &&
      failed.env.inferCache.size == before.env.inferCache.size &&
      failed.env.inferOnlyCache.size == before.env.inferOnlyCache.size &&
      (if kind >= 2 then failed.env.intern.exprs.size > before.env.intern.exprs.size &&
        failed.env.intern.univs.size > before.env.intern.univs.size
       else failed.env.intern.exprs.size == before.env.intern.exprs.size &&
        failed.env.intern.univs.size == before.env.intern.univs.size) &&
      failed.env.nextFVarId == before.env.nextFVarId && failed.inferOnly == before.inferOnly &&
      after.env.consts.size == failed.env.consts.size &&
      after.env.intern.exprs.size == failed.env.intern.exprs.size &&
      after.env.intern.univs.size == failed.env.intern.univs.size
  match TcM.runRec action (TcState.newLazyAnon source) with
  | .ok passed _ => passed
  | .error _ _ => false

private def blockCacheCases : TestSeq :=
  test "block cache: a definition projection loads both members and preserves both warm slots"
    (cacheAcrossBlock false false 0 false)
  ++ test "block cache: partial publication retains a cached sibling in full mode"
    (cacheAcrossBlock false true 0 false)
  ++ test "block cache: partial publication retains a cached sibling in inference-only mode"
    (cacheAcrossBlock false true 0 true)
  ++ test "block cache: a lambda loads a mutual dependency and preserves both warm slots"
    (cacheAcrossBlock false false 1 false)
  ++ test "block cache: an application loads a mutual dependency inside its lambda argument"
    (cacheAcrossBlock false false 2 false)
  ++ test "block cache: a recursor projection loads the whole block and converts its rules"
    (cacheAcrossBlock true false 0 false)
  ++ test "block cache: an inductive projection publishes its constructors and retains warm slots"
    (cacheAcrossInductiveBlock false)
  ++ test "block cache: a constructor projection publishes its inductive and retains warm slots"
    (cacheAcrossInductiveBlock true)
  ++ test "block cache: a missing parent retains both warm slots"
    (cacheAcrossBlockFailure 0)
  ++ test "block cache: a corrupt parent retains both warm slots"
    (cacheAcrossBlockFailure 1)
  ++ test "block cache: a missing later projection retains partial conversion without publication"
    (cacheAcrossBlockFailure 2)
  ++ test "block cache: a failed later member retains partial conversion without publication"
    (cacheAcrossBlockFailure 3)
  ++ test "block cache: an unknown root retains a completed block publication and both warm slots"
    (cacheAcrossBlockFailure 4)

private def internKeysCoherent (table : InternTable .anon) : Bool :=
  table.univs.toList.all (fun (key, level) => level.addr == key) &&
  table.exprs.toList.all (fun (key, term) => term.internKey == key)

/-- Deriving the loop bound must also work on source trees deeper than the
runtime call stack. Build the expected value independently in forward order. -/
private def coherentDeepUniverse : Bool := Id.run do
  let depth := 4096
  let mut source : Ixon.Univ := .zero
  let mut expected : KUniv .anon := .mkZero
  for _ in [0:depth] do
    source := .succ source
    expected := .mkSucc expected
  return match convertUnivTree source .empty with
    | .ok result table => result.addr == expected.addr && table.univs.size == depth + 1 &&
        table.exprs.isEmpty && internKeysCoherent table
    | .error _ _ => false

private def coherentUniverseBranches : Bool :=
  let source := Ixon.Univ.imax (.max (.var 0) (.succ .zero)) (.max (.var 1) (.var 2))
  let expected := KUniv.mkIMax (m := .anon) (.mkMax (.mkParam 0 ()) levelOne)
    (.mkMax (.mkParam 1 ()) (.mkParam 2 ()))
  match convertUnivTree source .empty with
  | .ok result table => result.addr == expected.addr && internKeysCoherent table
  | .error _ _ => false

private def coherentDeepExpression (binder : Bool) : Bool := Id.run do
  let depth := 4096
  let mut source : Ixon.Expr := .var 0
  let mut expected : KExpr .anon := .mkVar 0 ()
  let baseVar := KExpr.mkVar (m := .anon) 0 ()
  let sort := KExpr.mkSort (m := .anon) levelOne
  for _ in [0:depth] do
    if binder then
      source := .leanLam (.sort 0) source
      expected := .mkLam () () sort expected
    else
      source := .app source (.var 0)
      expected := .mkApp expected baseVar
  let ctx : IngressCtx := {sharing := #[], refs := #[], univs := #[.succ .zero], mutCtx := #[]}
  return match convertExpr {} ctx source {} .empty with
    | .ok (result, cache) table => result.addr == expected.addr && internKeysCoherent table &&
        table.exprs.size == depth + (if binder then 2 else 1) &&
        cache.univCache.size == (if binder then 1 else 0)
    | .error _ _ => false

/-- A long acyclic sharing chain nearly consumes the derived step bound.
Both forward and backward references must finish and memoize every expansion. -/
private def coherentSharingChain (forward : Bool) : Bool :=
  let depth := 2048
  let sharing : Array Ixon.Expr := (Array.range depth).map fun idx =>
    if forward then
      if idx + 1 < depth then .share (idx + 1).toUInt64 else .var 7
    else if idx == 0 then .var 7 else .share (idx - 1).toUInt64
  let root := Ixon.Expr.share (if forward then 0 else (depth - 1).toUInt64)
  let ctx : IngressCtx := {sharing, refs := #[], univs := #[], mutCtx := #[]}
  let expected := KExpr.mkVar (m := .anon) 7 ()
  match convertExpr {} ctx root {} .empty with
  | .ok (result, cache) table => result.addr == expected.addr && internKeysCoherent table &&
      table.exprs.size == 1 && table.univs.isEmpty && cache.exprCache.size == depth &&
      cache.exprCache.toList.all (fun (_, value) => value.addr == expected.addr)
  | .error _ _ => false

private def coherentSharedDiamond : Bool :=
  let sharing := #[Ixon.Expr.leanLam (.sort 0) (.var 0)]
  let ctx : IngressCtx := {sharing, refs := #[], univs := #[.succ .zero], mutCtx := #[]}
  let function := KExpr.mkLam (m := .anon) () () (.mkSort levelOne) (.mkVar 0 ())
  match convertExpr {} ctx (.app (.share 0) (.share 0)) {} .empty with
  | .ok (result, cache) table => result.addr == (KExpr.mkApp function function).addr &&
      internKeysCoherent table && cache.exprCache.size == 1 && cache.univCache.size == 1 &&
      table.exprs.size == 4
  | .error _ _ => false

private def coherentUnusedCycle : Bool :=
  let ctx : IngressCtx := {sharing := #[.share 0], refs := #[], univs := #[], mutCtx := #[]}
  match convertExpr {} ctx (.var 0) {} .empty with
  | .ok (result, cache) table => result.addr == (KExpr.mkVar (m := .anon) 0 ()).addr &&
      internKeysCoherent table && cache.exprCache.isEmpty && table.exprs.size == 1
  | .error _ _ => false

/-- Cyclic source sharing now returns a bounded diagnostic through the real
fault hook. Warm entries and coherent partial conversion survive the error. -/
private def coherenceAfterCyclicLoad (block : Bool) : Bool :=
  let (source, warmAddr) := polymorphicIdentity
  let level : Ixon.Univ := .succ (.succ (.succ (.succ (.succ .zero))))
  let broken : Ixon.Definition := ⟨.defn, .safe, 0, .sort 0, .share 0⟩
  let info := if block then Ixon.ConstantInfo.muts
    #[.defn ⟨.defn, .safe, 0, .sort 0, .sort 0⟩, .defn broken] else .defn broken
  let sharing := if block then #[Ixon.Expr.share 1, .share 0] else #[Ixon.Expr.share 0]
  let constant : Ixon.Constant := ⟨info, sharing, #[], #[level]⟩
  let (source, storedAddr) := if block then storeMutsWithProjs source constant else storeConst source constant
  let requested : KId .anon := ⟨if block then defnProjAddr storedAddr 1 else storedAddr, ()⟩
  let warm := KExpr.mkConst (m := .anon) ⟨warmAddr, ()⟩ #[levelOne]
  let action : RecM .anon Bool := do
    let expected ← warmBothCaches warm
    let key ← TcM.inferKey warm
    let before ← get
    let rejected ← try
      let _ ← liftM (TcM.getConst requested)
      pure false
    catch err => pure (((toString err).splitOn "conversion step bound exhausted").length > 1)
    let failed ← get
    let retry ← try
      let _ ← liftM (TcM.getConst requested)
      pure false
    catch err =>
      match err with
      | .unknownConst addr => pure (addr == requested.addr)
      | _ => pure false
    let reused ← RecM.inferCall warm
    let after ← get
    return rejected && retry && reused.addr == expected.addr && warmSlotsRetained key before failed &&
      internKeysCoherent before.env.intern && internKeysCoherent failed.env.intern &&
      failed.env.intern.exprs.size > before.env.intern.exprs.size &&
      failed.env.intern.univs.size > before.env.intern.univs.size &&
      failed.env.consts.size == before.env.consts.size && failed.env.blocks.size == before.env.blocks.size &&
      failed.env.inferCache.size == before.env.inferCache.size &&
      failed.env.inferOnlyCache.size == before.env.inferOnlyCache.size &&
      failed.env.nextFVarId == before.env.nextFVarId && failed.faultedAddrs.contains requested.addr &&
      after.env.intern.exprs.size == failed.env.intern.exprs.size &&
      after.env.intern.univs.size == failed.env.intern.univs.size
  match TcM.runRec action (TcState.newLazyAnon source) with
  | .ok passed _ => passed
  | .error _ _ => false

private def ingressCoherenceCases : TestSeq :=
  test "ingress coherence: deep universe conversion uses a bounded worklist"
    coherentDeepUniverse
  ++ test "ingress coherence: bounded universe conversion retains max/imax normalization"
    coherentUniverseBranches
  ++ test "ingress coherence: deep application conversion and its counting pass finish"
    (coherentDeepExpression false)
  ++ test "ingress coherence: deep binder conversion retains universe memoization"
    (coherentDeepExpression true)
  ++ test "ingress coherence: a long forward sharing chain fits the source-derived bound"
    (coherentSharingChain true)
  ++ test "ingress coherence: a long backward sharing chain fits the source-derived bound"
    (coherentSharingChain false)
  ++ test "ingress coherence: repeated sharing is converted once"
    coherentSharedDiamond
  ++ test "ingress coherence: an unused cyclic sharing entry is not expanded"
    coherentUnusedCycle
  ++ test "ingress coherence: cyclic standalone sharing fails with coherent partial state"
    (coherenceAfterCyclicLoad false)
  ++ test "ingress coherence: cyclic block sharing retains warm witnesses without publication"
    (coherenceAfterCyclicLoad true)

private def ownedRows (kind : Nat) : Bool :=
  let first := Address.blake3 "ownership-first".toUTF8
  let second := Address.blake3 "ownership-second".toUTF8
  let key : KId .anon := ⟨Address.blake3 "ownership-key".toUTF8, ()⟩
  let rows : List OwnershipRow := match kind with
    | 0 => []
    | 1 => [⟨first, #[key], false⟩, ⟨second, #[key], false⟩]
    | 2 => [⟨key.addr, #[], true⟩, ⟨first, #[key], false⟩]
    | 3 => [⟨first, #[key, key], false⟩, ⟨first, #[key], false⟩]
    | _ => [⟨first, #[], true⟩, ⟨second, #[], true⟩]
  ownershipRowsCheck rows == (kind == 0 || kind >= 3)

private def ownershipInventory : Bool :=
  let ind : Ixon.Inductive :=
    ⟨false, 0, 0, 0, .sort 0,
      #[⟨false, 0, 0, 0, 0, .sort 0⟩, ⟨false, 0, 1, 0, 0, .sort 0⟩]⟩
  let constant : Ixon.Constant :=
    ⟨.muts #[.defn ⟨.defn, .safe, 0, .sort 0, .sort 0⟩,
      .recr ⟨false, false, 0, 0, 0, 0, 0, .sort 0, #[]⟩, .indc ind], #[], #[], #[.succ .zero]⟩
  let (source, block) := storeMutsWithProjs {} constant
  let expected : Array (KId .anon) := #[⟨defnProjAddr block 0, ()⟩, ⟨recrProjAddr block 1, ()⟩,
    ⟨indcProjAddr block 2, ()⟩, ⟨ctorProjAddr block 2 0, ()⟩, ⟨ctorProjAddr block 2 1, ()⟩]
  sourceOwnershipCheck source && blockProjectionIds block constant == expected &&
    match convertAnonBlock source constant block .empty with
    | .ok trace _ => trace.allEntries.map (·.1) == expected
    | .error _ _ => false

private def loadedBlocksMatchOwnership (rows : List OwnershipRow) (env : AnonEnv) : Bool :=
  rows.all fun row => row.projections.all fun id =>
    (env.get? id).isNone || env.blocks.contains ⟨row.addr, ()⟩

/-- Partial external insertion lies outside the invariant even if its value
would agree with a later publication; the general overlap theorem still covers it. -/
private def ownershipDetectsPartialPreload : Bool :=
  let constant := cacheBlock false
  let (source, block) := storeMutsWithProjs {} constant
  let rows := sourceOwnershipRows source
  match prepareAnonBlock source constant block {} with
  | .error _ _ => false
  | .ok trace converted =>
      match trace.allEntries[0]? with
      | none => false
      | some entry =>
          sourceOwnershipCheck source && loadedBlocksMatchOwnership rows converted &&
          !loadedBlocksMatchOwnership rows (converted.insert entry.1 entry.2) &&
          loadedBlocksMatchOwnership rows (insertMutsEntriesState converted trace.allEntries)

private def ownershipCorruptSource : Bool :=
  let constant := cacheBlock false
  let (source, block) := storeMutsWithProjs {} constant
  let source := {source with consts := source.consts.insert block (.ofConstant (cacheBlock true))}
  sourceOwnershipCheck source &&
    !(sourceOwnershipRows source).any (fun row => row.addr == block) &&
    match TcM.getConst (m := .anon) ⟨defnProjAddr block 0, ()⟩ (TcState.newLazyAnon source) with
    | .ok _ _ => false
    | .error err after =>
        ((toString err).splitOn "fails integrity check").length > 1 &&
        after.env.consts.isEmpty && after.env.blocks.isEmpty

/-- One fixed source mixes standalone, definition, recursor, and inductive
loads, plus failures before and after publication. Check the invariant and both
warm cache slots after every call, in both inference modes. -/
private def ownershipAcrossLoads (inferOnly rootFirst : Bool) : Bool :=
  let (source, indBlock) := envInductive
  let (source, warmAddr) := storeConst source
    ⟨.axio ⟨false, 1, .leanAll (.sort 0) (.leanAll (.var 0) (.var 1))⟩, #[], #[], #[.var 0]⟩
  let (source, defBlock) := storeMutsWithProjs source (cacheBlock false)
  let (source, recBlock) := storeMutsWithProjs source (cacheBlock true)
  let broken : Ixon.Constant := ⟨.muts
    #[.defn ⟨.defn, .safe, 0, .sort 0, .sort 0⟩,
      .defn ⟨.defn, .safe, 0, .sort 0, .share 77⟩], #[], #[], #[.succ (.succ (.succ .zero))]⟩
  let (source, brokenBlock) := storeMutsWithProjs source broken
  let rows := sourceOwnershipRows source
  let warm := KExpr.mkConst (m := .anon) ⟨warmAddr, ()⟩ #[levelOne]
  let first : KId .anon := ⟨defnProjAddr defBlock 0, ()⟩
  let second : KId .anon := ⟨recrProjAddr recBlock 1, ()⟩
  let ctor : KId .anon := ⟨ctorProjAddr indBlock 0 0, ()⟩
  let brokenId : KId .anon := ⟨defnProjAddr brokenBlock 0, ()⟩
  let action : RecM .anon Bool := do
    let expected ← warmBothCaches warm
    let key ← TcM.inferKey warm
    let initial ← get
    let keeps (state : TcState .anon) := loadedBlocksMatchOwnership rows state.env &&
      warmSlotsRetained key initial state
    let rootRejected ← if rootFirst then
      try
        let _ ← liftM (TcM.getConst (m := .anon) ⟨defBlock, ()⟩)
        pure false
      catch err =>
        match err with
        | .unknownConst addr => pure (addr == defBlock)
        | _ => pure false
      else pure true
    let rootState ← get
    let firstType ← RecM.inferCall (.mkConst first #[])
    let firstState ← get
    let secondType ← RecM.inferCall (.mkConst second #[])
    let secondState ← get
    let failed ← try
      let _ ← liftM (TcM.getConst brokenId)
      pure false
    catch err => pure (((toString err).splitOn "invalid Share index 77").length > 1)
    let failedState ← get
    let _ ← RecM.inferCall (.mkConst ctor #[])
    let final ← get
    let reused ← RecM.inferCall warm
    return sourceOwnershipCheck source && keeps initial && rootRejected && keeps rootState &&
      firstType.addr == expected.addr && secondType.addr == expected.addr &&
      keeps firstState && keeps secondState && failed && keeps failedState && keeps final &&
      reused.addr == expected.addr &&
      !failedState.env.blocks.contains ⟨brokenBlock, ()⟩ &&
      (failedState.env.get? brokenId).isNone &&
      final.env.blocks.contains ⟨defBlock, ()⟩ && final.env.blocks.contains ⟨recBlock, ()⟩ &&
      final.env.blocks.contains ⟨indBlock, ()⟩ && final.inferOnly == inferOnly
  match TcM.runRec action {TcState.newLazyAnon source with inferOnly} with
  | .ok passed _ => passed
  | .error _ _ => false

private def sourceOwnershipCases : TestSeq :=
  test "source ownership: empty inventory is accepted" (ownedRows 0)
  ++ test "source ownership: different blocks cannot own the same projection" (ownedRows 1)
  ++ test "source ownership: standalone/projection overlap is rejected" (ownedRows 2)
  ++ test "source ownership: repeated keys within one block are accepted" (ownedRows 3)
  ++ test "source ownership: independent standalones are accepted" (ownedRows 4)
  ++ test "source ownership: mixed block inventory matches all converted member and constructor keys"
    ownershipInventory
  ++ test "source ownership: partial external insertion is detected until its block is recorded"
    ownershipDetectsPartialPreload
  ++ test "source ownership: corrupt headers are excluded and actual loading rejects them"
    ownershipCorruptSource
  ++ test "source ownership: full inference retains the invariant across mixed loads and failures"
    (ownershipAcrossLoads false false)
  ++ test "source ownership: inference-only calls retain the invariant across mixed loads and failures"
    (ownershipAcrossLoads true false)
  ++ test "source ownership: publication before a full-mode root error retains the invariant"
    (ownershipAcrossLoads false true)
  ++ test "source ownership: publication before an inference-only root error retains the invariant"
    (ownershipAcrossLoads true true)

/-- A recursive call loads one block, then a constant call loads a different
block. Check ownership, intern keys, scope cleanup, and both warm cache slots
at each boundary, including a final hit on the whole recursive expression. -/
private def stateAcrossRecursiveLoads (shape : Nat) (inferOnly stats surroundingScope : Bool) : Bool :=
  let (source, indBlock) := envInductive
  let (source, warmAddr) := storeConst source
    ⟨.axio ⟨false, 1, .leanAll (.sort 0) (.leanAll (.var 0) (.var 1))⟩, #[], #[], #[.var 0]⟩
  let (source, defBlock) := storeMutsWithProjs source (cacheBlock false)
  let (source, nextBlock) := storeMutsWithProjs source (cacheBlock true)
  let rows := sourceOwnershipRows source
  let warm := KExpr.mkConst (m := .anon) ⟨warmAddr, ()⟩ #[levelOne]
  let first : KId .anon := ⟨if shape == 0 then indcProjAddr indBlock 0 else defnProjAddr defBlock 0, ()⟩
  let next : KId .anon := ⟨recrProjAddr nextBlock 1, ()⟩
  let cold := KExpr.mkConst first #[]
  let sortType := KExpr.mkSort (m := .anon) levelOne
  let body := KExpr.mkLam () () sortType (.mkLam () () (.mkVar 0 ())
    (.mkApp (.mkApp cold (.mkVar 1 ())) (.mkVar 0 ())))
  let term := if shape == 0 then KExpr.mkAll () () cold cold
    else if shape == 1 then body
    else KExpr.mkApp (.mkApp (.mkConst ⟨warmAddr, ()⟩ #[levelTwo]) identityType) body
  let expected := if shape == 0 then sortType else identityType
  let action : RecM .anon Bool := do
    let warmType ← warmBothCaches warm
    let key ← TcM.inferKey warm
    let initial ← get
    let keeps (state : TcState .anon) := loadedBlocksMatchOwnership rows state.env &&
      internKeysCoherent state.env.intern && warmSlotsRetained key initial state
    RecM.withLctxScope do
      if surroundingScope then
        let _ ← TcM.openBinder () () sortType (.mkVar 0 ())
        pure ()
      let active ← get
      let rootKey ← TcM.inferKey term
      let result ← RecM.inferCall term
      let recursive ← get
      let nextType ← RecM.inferCall (.mkConst next #[])
      let successor ← get
      let reused ← RecM.inferCall warm
      let replay ← RecM.inferCall term
      let final ← get
      let cache := if inferOnly then successor.env.inferOnlyCache else successor.env.inferCache
      return sourceOwnershipCheck source && keeps initial && keeps active && keeps recursive &&
        keeps successor && keeps final && result.addr == expected.addr && result.lbr == 0 &&
        nextType.addr == identityType.addr && reused.addr == warmType.addr &&
        warmType.addr == identityType.addr && replay.addr == result.addr && rootKey != key &&
        cache[rootKey]?.any (fun cached => cached.addr == result.addr) &&
        (active.env.get? first).isNone && (recursive.env.get? first).isSome &&
        (recursive.env.get? next).isNone && (successor.env.get? next).isSome &&
        recursive.env.blocks.contains ⟨if shape == 0 then indBlock else defBlock, ()⟩ &&
        !recursive.env.blocks.contains ⟨nextBlock, ()⟩ &&
        successor.env.blocks.contains ⟨nextBlock, ()⟩ &&
        recursive.env.consts.size == active.env.consts.size + 2 &&
        successor.env.consts.size == recursive.env.consts.size + 2 &&
        recursive.env.intern.exprs.size > active.env.intern.exprs.size &&
        recursive.lctx.size == active.lctx.size && successor.lctx.size == active.lctx.size &&
        recursive.inferOnly == inferOnly && successor.inferOnly == inferOnly &&
        recursive.env.nextFVarId > active.env.nextFVarId &&
        (if stats && shape != 0 then recursive.deqCalls > active.deqCalls
         else recursive.deqCalls == active.deqCalls) &&
        final.deqCalls == successor.deqCalls && final.env.nextFVarId == successor.env.nextFVarId &&
        final.env.consts.size == successor.env.consts.size &&
        final.env.intern.exprs.size == successor.env.intern.exprs.size &&
        final.env.intern.univs.size == successor.env.intern.univs.size
  match TcM.runRec action {TcState.newLazyAnon source with inferOnly, stats} with
  | .ok passed after => passed && after.lctx.size == 0 && after.inferOnly == inferOnly &&
      loadedBlocksMatchOwnership rows after.env && internKeysCoherent after.env.intern
  | .error _ _ => false

private def recursiveStateCases : TestSeq :=
  test "recursive state: forall inference and a later constant retain ownership, coherence, and warm slots"
    (stateAcrossRecursiveLoads 0 false false false)
  ++ test "recursive state: inference-only forall and later loading retain an outer scope"
    (stateAcrossRecursiveLoads 0 true true true)
  ++ test "recursive state: lambda opening and closing retain resources for the next block"
    (stateAcrossRecursiveLoads 1 false false false)
  ++ test "recursive state: lambda conversion statistics and scope cleanup retain both invariants"
    (stateAcrossRecursiveLoads 1 false true true)
  ++ test "recursive state: application with a lazy lambda argument permits subsequent block loading"
    (stateAcrossRecursiveLoads 2 false false false)
  ++ test "recursive state: nested application and later cache replay retain both invariants"
    (stateAcrossRecursiveLoads 2 false true true)

/-- Compare every anonymous field, including recursive syntax and annotations.
The production expression/level BEq instances compare addresses only. -/
private def sameSourceLevel : KUniv .anon → KUniv .anon → Bool
  | .zero a, .zero b => a == b
  | .succ a ah, .succ b bh => ah == bh && sameSourceLevel a b
  | .max a b ah, .max c d bh | .imax a b ah, .imax c d bh =>
      ah == bh && sameSourceLevel a c && sameSourceLevel b d
  | .param a _ ah, .param b _ bh => a == b && ah == bh
  | _, _ => false

private def sameSourceExpr (left right : KExpr .anon) : Bool :=
  left.addr == right.addr && left.lbr == right.lbr && left.count0 == right.count0 &&
  left.hasFVars == right.hasFVars && match left, right with
  | .var a _ _, .var b _ _ => a == b
  | .fvar a _ _, .fvar b _ _ => a == b
  | .sort a _, .sort b _ => sameSourceLevel a b
  | .const a us _, .const b vs _ => a.addr == b.addr && us.size == vs.size &&
      (us.zip vs).all (fun (u, v) => sameSourceLevel u v)
  | .app a b _, .app c d _ | .lam _ _ a b _, .lam _ _ c d _ |
      .all _ _ a b _, .all _ _ c d _ => sameSourceExpr a c && sameSourceExpr b d
  | .letE _ a b c nd _, .letE _ d e f md _ => nd == md &&
      sameSourceExpr a d && sameSourceExpr b e && sameSourceExpr c f
  | .prj a i v _, .prj b j w _ => a.addr == b.addr && i == j && sameSourceExpr v w
  | .nat a ah _, .nat b bh _ => a == b && ah == bh
  | .str a ah _, .str b bh _ => a == b && ah == bh
  | _, _ => false

private def sameStandalone : KConst .anon → KConst .anon → Bool
  | .axio _ _ isUnsafe n ty, .axio _ _ isUnsafe' n' ty' =>
      isUnsafe == isUnsafe' && n == n' && sameSourceExpr ty ty'
  | .quot _ _ kind n ty, .quot _ _ kind' n' ty' =>
      kind == kind' && n == n' && sameSourceExpr ty ty'
  | .defn _ _ kind safety hints n ty val _ block,
      .defn _ _ kind' safety' hints' n' ty' val' _ block' =>
      kind == kind' && safety == safety' && hints == hints' && n == n' &&
      sameSourceExpr ty ty' && sameSourceExpr val val' && block.addr == block'.addr
  | .recr _ _ k isUnsafe n p i m s block idx ty rules _,
      .recr _ _ k' isUnsafe' n' p' i' m' s' block' idx' ty' rules' _ =>
      k == k' && isUnsafe == isUnsafe' && n == n' && p == p' && i == i' && m == m' &&
      s == s' && block.addr == block'.addr && idx == idx' && sameSourceExpr ty ty' &&
      rules.size == rules'.size && (rules.zip rules').all (fun (a, b) =>
        a.fields == b.fields && sameSourceExpr a.rhs b.rhs)
  | _, _ => false

private def sourceCatalogMatches (source : Ixon.Env) (env : AnonEnv) : Bool :=
  env.consts.toList.all fun (id, concrete) => match predictStandalone? source id.addr with
    | .ok (some expected) => sameStandalone concrete expected
    | _ => true

/-- Check independent expected fields, actual cold and warm conversion, and
publication by the verified lazy loader. -/
private def predictionMatches (source : Ixon.Env) (addr : Address) (expected : KConst .anon) : Bool :=
  match getConstVerified source addr true, predictStandalone? source addr with
  | .ok (some constant), .ok (some predicted) =>
      match convertAnonStandalone source addr constant .empty with
      | .ok cold table =>
          match convertAnonStandalone source addr constant table,
              TcM.getConst (m := .anon) ⟨addr, ()⟩ (TcState.newLazyAnon source) with
          | .ok warm after, .ok loaded state =>
              sameStandalone predicted expected && sameStandalone cold expected &&
              sameStandalone warm expected && sameStandalone loaded expected &&
              sourceCatalogMatches source state.env && internKeysCoherent after &&
              after.exprs.size == table.exprs.size && after.univs.size == table.univs.size
          | _, _ => false
      | .error _ _ => false
  | _, _ => false

private def predictionShared (kind : Nat) : Bool :=
  let (source, addr) := storeConst {} (lazyCacheDependency kind)
  let value := KExpr.mkLam (m := .anon) () () (.mkSort levelOne)
    (.mkLam () () (.mkVar 0 ()) (.mkVar 0 ()))
  let expected := match kind with
    | 0 => KConst.axio () () false 0 identityType
    | 1 => .defn () () .defn .safe (.regular 0) 0 identityType value () ⟨addr, ()⟩
    | 2 => .recr () () false false 0 0 0 0 0 ⟨addr, ()⟩ 0 identityType
        #[⟨(), 0, value⟩, ⟨(), 1, value⟩] ()
    | _ => .quot () () .type 0 identityType
  predictionMatches source addr expected

/-- All expression forms, both let flags, literal blobs, self/reference level
arguments, normalization, and anonymous reducibility hints in one declaration. -/
private def predictionRichDefinition : Bool :=
  let (source, carrier) := envA
  let (source, natBlob) := source.storeBlob ⟨(42 : Nat).toBytesLE⟩
  let (source, strBlob) := source.storeBlob "héllo".toUTF8
  let shared := Ixon.Expr.leanAll (.sort 0) (.var 0)
  let typ := Ixon.Expr.leanAll (.sort 1)
    (.letE true (.share 0) (.recur 0 #[1, 0])
      (.prj 0 2 (.app (.ref 0 #[0, 0]) (.var 0))))
  let value := Ixon.Expr.letE false (.sort 1) (.nat 1)
    (.leanLam (.sort 0) (.app (.str 2) (.share 0)))
  let level : Ixon.Univ := .imax (.max (.var 0) (.var 1)) (.var 1)
  let constant : Ixon.Constant := ⟨.defn ⟨.opaq, .unsaf, 2, typ, value⟩,
    #[shared], #[carrier, natBlob, strBlob], #[level, .imax (.succ .zero) .zero]⟩
  let (source, addr) := storeConst source constant
  let source := {source with anonHints := source.anonHints.insert addr (.regular 37)}
  let u := KUniv.mkIMax (.mkMax (.mkParam 0 ()) (.mkParam 1 ())) (.mkParam 1 ())
  let sort := KExpr.mkSort (m := .anon) u
  let prop := KExpr.mkSort (m := .anon) .mkZero
  let shared := KExpr.mkAll () () sort (.mkVar 0 ())
  let typ := KExpr.mkAll () () prop
    (.mkLet () shared (.mkConst ⟨addr, ()⟩ #[.mkZero, u])
      (.mkPrj ⟨carrier, ()⟩ 2 (.mkApp (.mkConst ⟨carrier, ()⟩ #[u, u]) (.mkVar 0 ()))) true)
  let value := KExpr.mkLet () prop (.mkNat 42 natBlob)
    (.mkLam () () sort (.mkApp (.mkStr "héllo" strBlob) shared)) false
  predictionMatches source addr (.defn () () .opaq .unsaf (.regular 37) 2 typ value () ⟨addr, ()⟩)

private def predictionRecursorFields : Bool :=
  let (source, addr) := storeConst {}
    ⟨.recr ⟨true, true, 2, 3, 4, 5, 6, .sort 0,
      #[⟨7, .recur 0 #[0]⟩, ⟨8, .sort 0⟩]⟩, #[], #[], #[.var 1]⟩
  let u := KUniv.mkParam (m := .anon) 1 ()
  let ty := KExpr.mkSort u
  predictionMatches source addr (.recr () () true true 2 3 4 5 6 ⟨addr, ()⟩ 0 ty
    #[⟨(), 7, .mkConst ⟨addr, ()⟩ #[u]⟩, ⟨(), 8, ty⟩] ())

/-- The prediction remains independent of a poisoned intern entry. This
intentionally violates finite collision freedom while keeping the same hash. -/
private def predictionCollisionBoundary (levelCollision : Bool) : Bool :=
  let (source, addr) := envA
  match getConstVerified source addr true, predictStandalone? source addr with
  | .ok (some constant), .ok (some predicted) =>
      let forged := KExpr.sort levelOne {predicted.ty.info with lbr := 9, count0 := 8}
      let levels := (∅ : Std.HashMap Address (KUniv .anon)).insert
        levelOne.addr (.param 9 () levelOne.addr)
      let expressions := (∅ : Std.HashMap Address (KExpr .anon)).insert predicted.ty.addr forged
      let table : InternTable .anon := if levelCollision then
          {InternTable.empty with univs := levels}
        else {InternTable.empty with exprs := expressions}
      match convertAnonStandalone source addr constant table with
      | .ok actual _ => actual.ty.addr == predicted.ty.addr && !sameStandalone actual predicted &&
          sameSourceExpr predicted.ty (.mkSort levelOne)
      | .error _ _ => false
  | _, _ => false

private def predictionFailure (kind : Nat) : Bool :=
  let broken : Ixon.Expr := match kind with
    | 0 => .share 9
    | 1 => .sort 9
    | 2 => .ref 9 #[]
    | 3 => .recur 9 #[]
    | _ => .share 0
  let constant : Ixon.Constant :=
    ⟨.defn ⟨.defn, .safe, 0, .sort 0, broken⟩, #[.share 0], #[], #[.succ .zero]⟩
  let (source, addr) := storeConst {} constant
  match predictStandalone? source addr, convertAnonStandalone source addr constant .empty with
  | .error predicted, .error actual table => predicted == actual && !table.exprs.isEmpty &&
      !table.univs.isEmpty && internKeysCoherent table &&
      !(ConversionRecipe.standalone source addr constant).exprs.isEmpty
  | _, _ => false

private def predictionCatalogSelection : Bool :=
  let (source, block) := storeMutsWithProjs {} (cacheBlock false)
  let missing := Address.blake3 "source-prediction-missing".toUTF8
  let bad := Address.blake3 "source-prediction-corrupt".toUTF8
  let source := {source with consts := source.consts.insert bad (.ofConstant axiomA)}
  match predictStandalone? source block, predictStandalone? source (defnProjAddr block 0),
      predictStandalone? source missing, predictStandalone? source bad with
  | .ok none, .ok none, .ok none, .error _ => true
  | _, _, _, _ => false

/-- A recursive call loads a standalone; a mixed block load and another
standalone follow. The source catalog is checked at each actual boundary. -/
private def sourceAcrossRecursiveLoads (shape : Nat) (inferOnly surroundingScope : Bool) : Bool :=
  let (source, warmAddr) := polymorphicIdentity
  let constant := if shape == 0 then axiomA else lazyCacheDependency 1
  let (source, coldAddr) := storeConst source constant
  let (source, block) := storeMutsWithProjs source (cacheBlock true)
  let (source, nextAddr) := storeConst source (lazyCacheDependency 3)
  let warm := KExpr.mkConst (m := .anon) ⟨warmAddr, ()⟩ #[levelOne]
  let cold := KExpr.mkConst (m := .anon) ⟨coldAddr, ()⟩ #[]
  let sort := KExpr.mkSort (m := .anon) levelOne
  let body := KExpr.mkLam () () sort (.mkLam () () (.mkVar 0 ())
    (.mkApp (.mkApp cold (.mkVar 1 ())) (.mkVar 0 ())))
  let term := if shape == 0 then KExpr.mkAll () () cold cold else if shape == 1 then body
    else KExpr.mkApp (.mkApp (.mkConst ⟨warmAddr, ()⟩ #[levelTwo]) identityType) body
  let action : RecM .anon Bool := do
    let expected ← warmBothCaches warm
    let key ← TcM.inferKey warm
    let initial ← get
    let keeps (state : TcState .anon) := sourceCatalogMatches source state.env &&
      internKeysCoherent state.env.intern && warmSlotsRetained key initial state
    RecM.withLctxScope do
      if surroundingScope then
        let _ ← TcM.openBinder () () sort (.mkVar 0 ())
        pure ()
      let active ← get
      let result ← RecM.inferCall term
      let recursive ← get
      let _ ← liftM (TcM.getConst (m := .anon) ⟨recrProjAddr block 1, ()⟩)
      let mixed ← get
      let next ← RecM.inferCall (.mkConst ⟨nextAddr, ()⟩ #[])
      let successor ← get
      let replay ← RecM.inferCall term
      let reused ← RecM.inferCall warm
      let final ← get
      return sourceOwnershipCheck source && keeps initial && keeps active && keeps recursive &&
        keeps mixed && keeps successor && keeps final &&
        sameSourceExpr result (if shape == 0 then sort else identityType) &&
        sameSourceExpr next identityType && sameSourceExpr replay result && sameSourceExpr reused expected &&
        (active.env.get? ⟨coldAddr, ()⟩).isNone && (recursive.env.get? ⟨coldAddr, ()⟩).isSome &&
        (mixed.env.get? ⟨nextAddr, ()⟩).isNone && (successor.env.get? ⟨nextAddr, ()⟩).isSome &&
        mixed.env.blocks.contains ⟨block, ()⟩ && recursive.lctx.size == active.lctx.size &&
        successor.lctx.size == active.lctx.size && final.env.nextFVarId == successor.env.nextFVarId &&
        final.env.intern.exprs.size == successor.env.intern.exprs.size &&
        final.env.intern.univs.size == successor.env.intern.univs.size
  match TcM.runRec action {TcState.newLazyAnon source with inferOnly, stats := true} with
  | .ok passed after => passed && sourceCatalogMatches source after.env && after.lctx.size == 0
  | .error _ _ => false

private def sourceAgreementCases : TestSeq :=
  test "source prediction: shared axiom matches cold/warm conversion and lazy publication" (predictionShared 0)
  ++ test "source prediction: shared definition body matches complete expected fields" (predictionShared 1)
  ++ test "source prediction: recursor rules preserve sharing and distinct field counts" (predictionShared 2)
  ++ test "source prediction: quotient fields match actual lazy loading" (predictionShared 3)
  ++ test "source prediction: every expression form, normalized universes, blobs, and hints agree"
    predictionRichDefinition
  ++ test "source prediction: recursor flags, counts, block identity, and self references agree"
    predictionRecursorFields
  ++ test "source prediction: equal hashes do not hide different expression annotations"
    (predictionCollisionBoundary false)
  ++ test "source prediction: equal hashes do not hide different universe trees"
    (predictionCollisionBoundary true)
  ++ test "source prediction: missing share retains the same error and partial intern state" (predictionFailure 0)
  ++ test "source prediction: missing universe retains the same error and partial intern state" (predictionFailure 1)
  ++ test "source prediction: missing reference retains the same error and partial intern state" (predictionFailure 2)
  ++ test "source prediction: missing recursive member retains the same error and partial state" (predictionFailure 3)
  ++ test "source prediction: cyclic sharing returns the same bounded error" (predictionFailure 4)
  ++ test "source prediction: blocks, projections, missing addresses, and corrupt source remain distinct"
    predictionCatalogSelection
  ++ test "source agreement: forall inference retains readings through mixed and later standalone loads"
    (sourceAcrossRecursiveLoads 0 false false)
  ++ test "source agreement: inference-only forall retains readings under an outer scope"
    (sourceAcrossRecursiveLoads 0 true true)
  ++ test "source agreement: lambda opening and closing retain readings for subsequent loading"
    (sourceAcrossRecursiveLoads 1 false false)
  ++ test "source agreement: lambda inference retains readings under an outer scope"
    (sourceAcrossRecursiveLoads 1 false true)
  ++ test "source agreement: application retains readings for subsequent mixed and standalone loading"
    (sourceAcrossRecursiveLoads 2 false false)
  ++ test "source agreement: application replay and surrounding scope retain the catalog"
    (sourceAcrossRecursiveLoads 2 false true)

/-- Check the two concrete maps against a finite source catalog. A cached
constant must also retain the complete declaration that produced its type. -/
private def sourceCacheMatches (source : Ixon.Env)
    (catalog : Array (KExpr .anon × KExpr .anon)) (state : TcState .anon) : Bool :=
  catalog.all fun (term, expected) =>
    let loaded := match term with
      | .sort .. => true
      | .const id _ _ => match predictStandalone? source id.addr, state.env.get? id with
          | .ok (some predicted), some actual => sameStandalone actual predicted
          | _, _ => false
      | _ => false
    let valid := fun cached => match cached with
      | none => true
      | some actual => sameSourceExpr actual expected && loaded
    let key := (term.addr, emptyCtxAddr)
    valid state.env.inferCache[key]? && valid state.env.inferOnlyCache[key]?

/-- Start with empty caches, write both policies at the same constant key,
infer recursively, load a block, retain partial failure state, load another
standalone, replay hits, then clear and repopulate the caches. -/
private def sourceCacheHistory (shape : Nat) (outerScope finalOnly : Bool) : Bool :=
  let (source, warmAddr) := polymorphicIdentity
  let (source, coldAddr) := storeConst source (if shape == 0 then axiomA else lazyCacheDependency 1)
  let (source, block) := storeMutsWithProjs source (cacheBlock true)
  let (source, nextAddr) := storeConst source (lazyCacheDependency 3)
  let (source, badAddr) := storeConst source
    ⟨.defn ⟨.defn, .safe, 0, .sort 0, .share 9⟩, #[], #[],
      #[.succ (.succ (.succ (.succ (.succ .zero))))]⟩
  let warm := KExpr.mkConst (m := .anon) ⟨warmAddr, ()⟩ #[levelOne]
  let warmTwo := KExpr.mkConst (m := .anon) ⟨warmAddr, ()⟩ #[levelTwo]
  let twoType := KExpr.mkAll (m := .anon) () () (.mkSort levelTwo)
    (.mkAll () () (.mkVar 0 ()) (.mkVar 1 ()))
  let cold := KExpr.mkConst (m := .anon) ⟨coldAddr, ()⟩ #[]
  let next := KExpr.mkConst (m := .anon) ⟨nextAddr, ()⟩ #[]
  let prop := KExpr.mkSort (m := .anon) .mkZero
  let sort := KExpr.mkSort (m := .anon) levelOne
  let sortTwo := KExpr.mkSort (m := .anon) levelTwo
  let coldType := if shape == 0 then sort else identityType
  let catalog := #[(warm, identityType), (warmTwo, twoType), (cold, coldType),
    (next, identityType), (prop, sort), (sort, sortTwo), (sortTwo, .mkSort (.mkSucc levelTwo))]
  let body := KExpr.mkLam () () sort (.mkLam () () (.mkVar 0 ())
    (.mkApp (.mkApp cold (.mkVar 1 ())) (.mkVar 0 ())))
  let term := if shape == 0 then KExpr.mkAll () () cold cold else if shape == 1 then body
    else KExpr.mkApp (.mkApp warmTwo identityType) body
  let action : RecM .anon Bool := do
    let initial ← get
    modify fun state => {state with inferOnly := true}
    let onlyType ← RecM.inferCall warm
    let only ← get
    modify fun state => {state with inferOnly := false}
    let fullType ← RecM.inferCall warm
    let full ← get
    RecM.withLctxScope do
      if outerScope then
        let _ ← TcM.openBinder () () sort (.mkVar 0 ())
        pure ()
      modify fun state => {state with inferOnly := shape == 0 && finalOnly}
      let active ← get
      let result ← RecM.inferCall term
      let recursive ← get
      let _ ← liftM (TcM.getConst (m := .anon) ⟨recrProjAddr block 1, ()⟩)
      let mixed ← get
      let rejected ← try
        let _ ← liftM (TcM.getConst (m := .anon) ⟨badAddr, ()⟩)
        pure false
      catch error => pure (((toString error).splitOn "invalid Share index 9").length > 1)
      let failed ← get
      let nextType ← RecM.inferCall next
      let distinctType ← RecM.inferCall warmTwo
      let successor ← get
      let replay ← RecM.inferCall term
      modify fun state => {state with inferOnly := true}
      let reused ← RecM.inferCall warm
      let final ← get
      modify fun state => {state with env := state.env.clearReductionCaches, inferOnly := finalOnly}
      let cleared ← get
      let rebuilt ← RecM.inferCall warm
      let after ← get
      let key := (warm.addr, emptyCtxAddr)
      return sourceOwnershipCheck source && initial.env.inferCache.isEmpty &&
        initial.env.inferOnlyCache.isEmpty &&
        #[initial, only, full, active, recursive, mixed, failed, successor, final, cleared, after].all
          (fun state => sourceCacheMatches source catalog state && sourceCatalogMatches source state.env &&
            internKeysCoherent state.env.intern) &&
        only.env.inferCache[key]?.isNone && only.env.inferOnlyCache[key]?.isSome &&
        full.env.inferCache[key]?.isSome && full.env.inferOnlyCache[key]?.isSome &&
        sameSourceExpr onlyType identityType && sameSourceExpr fullType identityType &&
        sameSourceExpr result (if shape == 0 then sort else identityType) &&
        sameSourceExpr nextType identityType && sameSourceExpr distinctType twoType &&
        sameSourceExpr replay result && sameSourceExpr reused identityType && sameSourceExpr rebuilt identityType &&
        (active.env.get? ⟨coldAddr, ()⟩).isNone && (recursive.env.get? ⟨coldAddr, ()⟩).isSome &&
        rejected && failed.faultedAddrs.contains badAddr &&
        failed.env.intern.exprs.size > mixed.env.intern.exprs.size &&
        failed.env.consts.size == mixed.env.consts.size && mixed.env.blocks.contains ⟨block, ()⟩ &&
        successor.lctx.size == active.lctx.size && final.env.nextFVarId == successor.env.nextFVarId &&
        cleared.env.inferCache.isEmpty && cleared.env.inferOnlyCache.isEmpty &&
        cleared.env.consts.size == final.env.consts.size &&
        (if finalOnly then after.env.inferCache[key]?.isNone && after.env.inferOnlyCache[key]?.isSome
         else after.env.inferCache[key]?.isSome && after.env.inferOnlyCache[key]?.isNone)
  match TcM.runRec action {TcState.newLazyAnon source with stats := true} with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

private def sourceCacheMissingDeclaration : Bool :=
  let (source, addr) := polymorphicIdentity
  let term := KExpr.mkConst (m := .anon) ⟨addr, ()⟩ #[levelOne]
  let before := TcState.newLazyAnon source
  let forged := {before with env := {before.env with
    inferCache := before.env.inferCache.insert (term.addr, emptyCtxAddr) identityType}}
  sourceCacheMatches source #[(term, identityType)] before &&
    !sourceCacheMatches source #[(term, identityType)] forged

/-- A different input forged at the same key can overwrite a valid result.
The finite key domain rules out exactly this case in the preservation proof. -/
private def sourceCacheForeignWrite : Bool :=
  let (source, addr) := polymorphicIdentity
  let term := KExpr.mkConst (m := .anon) ⟨addr, ()⟩ #[levelOne]
  let prop := KExpr.mkSort (m := .anon) .mkZero
  let forged := KExpr.app term prop {(KExpr.mkApp term prop).info with addr := term.addr}
  match TcM.infer forged (TcState.newLazyAnon source) with
  | .ok result after => sameSourceExpr result (.mkAll () () prop prop) &&
      after.env.inferCache[(term.addr, emptyCtxAddr)]?.isSome &&
      !sourceCacheMatches source #[(term, identityType)] after
  | .error _ _ => false

private def sourceCacheCases : TestSeq :=
  test "source cache: empty/full/only caches survive forall, loading, failures, and clearing"
    (sourceCacheHistory 0 false false)
  ++ test "source cache: inference-only forall and repopulation retain an outer scope"
    (sourceCacheHistory 0 true true)
  ++ test "source cache: lambda leaves establish agreement at written catalog keys"
    (sourceCacheHistory 1 false false)
  ++ test "source cache: lambda history retains both policies and loaded dependencies"
    (sourceCacheHistory 1 true true)
  ++ test "source cache: application history preserves distinct universe instances"
    (sourceCacheHistory 2 false false)
  ++ test "source cache: application history survives scopes, replay, and clearing"
    (sourceCacheHistory 2 true true)
  ++ test "source cache: a correct cached type with a missing declaration violates coverage"
    sourceCacheMissingDeclaration
  ++ test "source cache: a forged same-key application violates source result agreement"
    sourceCacheForeignWrite

/-- Replay a full result with no recursive methods or shared fuel. A
different inference-only entry makes full-result priority observable. -/
private def compositeReplayAt (source expected : KExpr .anon) (state : TcState .anon) : Bool :=
  let key := (source.addr, emptyCtxAddr)
  let sentinel := KExpr.mkSort (m := .anon) (.mkSucc levelTwo)
  source.lbr == 0 && expected != sentinel && state.env.inferCache[key]? == some expected &&
    [false, true].all fun inferOnly =>
      let before := { state with recFuel := 0, inferOnly, env := { state.env with
        inferOnlyCache := state.env.inferOnlyCache.insert key sentinel } }
      match (RecM.infer source).run (methodsN 0) before with
      | .error _ _ => false
      | .ok result after => result == expected && after.recFuel == 0 &&
          after.env.inferCache[key]? == some expected && after.env.inferOnlyCache[key]? == some sentinel &&
          after.env.intern.exprs.size == before.env.intern.exprs.size &&
          after.env.nextFVarId == before.env.nextFVarId && after.lctx.size == before.lctx.size &&
          after.ctxId == before.ctxId && after.deqCalls == before.deqCalls

private def compositeCacheSource (shape : Nat) : KExpr .anon × KExpr .anon :=
  let sort := KExpr.mkSort (m := .anon) levelOne
  let type := KExpr.mkAll () () sort sort
  let lambda := KExpr.mkLam () () sort (.mkVar 0 ())
  if shape == 0 then (.mkApp lambda (.mkSort .mkZero), sort)
  else if shape == 1 then (type, .mkSort levelTwo)
  else (lambda, type)

/-- Actual composite checks remain cached through a recursive call that
loads a polymorphic dependency, two scopes, and repeated hits. Clearing
invalidates the hit, and another full check establishes it again. -/
private def compositeCacheHistory (shape : Nat) : Bool :=
  let (source, expected) := compositeCacheSource shape
  let action : RecM .anon Bool := do
    let initial ← RecM.inferCall source
    if initial != expected || !compositeReplayAt source expected (← get) then return false
    let unrelated := KExpr.mkApp (.mkConst ⟨polymorphicIdentity.2, ()⟩ #[levelOne]) (.mkSort .mkZero)
    let _ ← RecM.inferCall unrelated
    if !compositeReplayAt source expected (← get) then return false
    for _ in [0, 1] do
      let passed ← RecM.withLctxScope do
        let _ ← TcM.openBinder () () (.mkSort levelOne) (.mkVar 0 ())
        let result ← RecM.inferCall source
        return result == expected && compositeReplayAt source expected (← get)
      if !passed then return false
    modify fun state => { state with env := state.env.clearReductionCaches }
    let cleared ← get
    if cleared.env.inferCache[(source.addr, emptyCtxAddr)]?.isSome then return false
    match (RecM.infer source).run (methodsN 0) cleared with
    | .error .maxRecFuel _ => pure ()
    | _ => return false
    let result ← RecM.inferCall source
    return result == expected && compositeReplayAt source expected (← get)
  match TcM.runRec action (TcState.newLazyAnon polymorphicIdentity.1) with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

/-- A real inference-only check cannot justify a full-mode cache hit. The
subsequent validating call must execute before zero-fuel replay is possible. -/
private def compositeOnlyCache (shape : Nat) : Bool :=
  let (source, expected) := compositeCacheSource shape
  let action : RecM .anon Bool := do
    let only ← RecM.inferOnlyCall source
    let before ← get
    let key := (source.addr, emptyCtxAddr)
    if only != expected || before.env.inferCache[key]?.isSome ||
        before.env.inferOnlyCache[key]? != some expected then return false
    match (RecM.infer source).run (methodsN 0) before with
    | .error .maxRecFuel _ => pure ()
    | _ => return false
    let full ← RecM.inferCall source
    return full == expected && compositeReplayAt source expected (← get)
  match TcM.runRec action (TcState.newLazyAnon {}) with
  | .ok passed _ => passed
  | .error _ _ => false

/-- The watched lambda survives application inference with beta Pi
exposure or lambda inference whose body type changes under cheap beta.
The application case also repeats cold and warm public Pi exposure. -/
private def compositeAcrossBetaInference (changedLambda typeLevel : Bool) : Bool :=
  let level := if typeLevel then Ixon.Univ.succ .zero else .zero
  let (env, target) := if changedLambda then cheapLambdaConstant level 0 true
    else piExposureDeclaration level
  let (watched, watchedType) := compositeCacheSource 2
  let action : RecM .anon Bool := do
    let initial ← RecM.inferCall watched
    if initial != watchedType then return false
    let .defn _ _ _ _ _ _ expected value _ _ ← TcM.getConst (m := .anon) ⟨target, ()⟩ | return false
    let result ← RecM.inferCall value
    if result != expected || !compositeReplayAt watched watchedType (← get) ||
        !compositeReplayAt value expected (← get) then return false
    if changedLambda then
      let .lam _ _ _ body _ := value | return false
      let original ← RecM.inferCall body
      let reduced ← TcM.runIntern (cheapBetaReduce original)
      return original != reduced && compositeReplayAt value expected (← get)
    else
      let .app fn _ _ := value | return false
      let functionType ← RecM.inferCall fn
      let exposed ← observePiExposure functionType expected expected true false
      if !exposed || !compositeReplayAt value expected (← get) then return false
      let (domain, body) ← RecM.ensureForallDirect functionType
      return domain == expected && body == expected && compositeReplayAt value expected (← get)
  match TcM.runRec action (TcState.newLazyAnon env) with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

/-- A cached lambda is subsequently used as a checked function and reduced.
Its original full check must still supply the lambda's domain and body. -/
private def compositeCachedLambdaBeta : Bool :=
  let (lambda, type) := compositeCacheSource 2
  let argument := KExpr.mkSort (m := .anon) .mkZero
  let application := KExpr.mkApp lambda argument
  let action : RecM .anon Bool := do
    let result ← RecM.inferCall lambda
    if result != type || !compositeReplayAt lambda type (← get) then return false
    let applicationType ← RecM.inferCall application
    let reduced ← RecM.whnfCoreWithFlagsUncached application .DEF_EQ_CORE
    let reducedType ← RecM.inferCall reduced
    return reduced == argument && applicationType == reducedType &&
      compositeReplayAt lambda type (← get) && compositeReplayAt application applicationType (← get)
  match TcM.runRec action (TcState.newLazyAnon {}) with
  | .ok passed _ => passed
  | .error _ _ => false

/-- Identical binder syntax opened in different scopes receives different
free-variable IDs, expression addresses, and cached dependent types. -/
private def compositeLocalCacheKeys : Bool :=
  let action : RecM .anon Bool := do
    let checkScope : RecM .anon (Bool × Address × Address) := RecM.withLctxScope do
      let (carrier, _) ← TcM.openBinder () () (.mkSort levelOne) (.mkVar 0 ())
      let source := KExpr.mkLam () () carrier (.mkVar 0 ())
      let expected := KExpr.mkAll () () carrier carrier
      let result ← RecM.inferCall source
      return (result == expected && compositeReplayAt source expected (← get), source.addr, expected.addr)
    let first ← checkScope
    let second ← checkScope
    return first.1 && second.1 && first.2.1 != second.2.1 && first.2.2 != second.2.2
  match TcM.runRec action (TcState.newLazyAnon {}) with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

/-- A cached dependent lambda and its Pi type capture two locals. New
loaded declarations and two more dependent locals intervene before the
lambda is applied and reduced; the same raw cache entries remain valid. -/
private def compositeCapturedTransport (typeLevel : Bool) : Bool :=
  let sortLevel := if typeLevel then levelOne else KUniv.mkZero
  let sort := KExpr.mkSort (m := .anon) sortLevel
  let action : RecM .anon Bool := RecM.withLctxScope do
    let (carrier, _) ← TcM.openBinder () () sort (.mkVar 0 ())
    let (family, _) ← TcM.openBinder () () (.mkAll () () carrier sort) (.mkVar 0 ())
    let innerDomain := KExpr.mkApp family (.mkVar 0 ())
    let source := KExpr.mkLam () () carrier (.mkLam () () innerDomain (.mkVar 0 ()))
    let expected := KExpr.mkAll () () carrier
      (.mkAll () () innerDomain (.mkApp family (.mkVar 1 ())))
    let piType ← RecM.inferCall expected
    let initial ← RecM.inferCall source
    let before ← get
    if initial != expected || !compositeReplayAt source expected before ||
        !compositeReplayAt expected piType before then return false
    let unrelated := KExpr.mkApp (.mkConst ⟨polymorphicIdentity.2, ()⟩ #[levelOne]) (.mkSort .mkZero)
    let _ ← RecM.inferCall unrelated
    if (← get).env.consts.size ≤ before.env.consts.size then return false
    let used ← RecM.withLctxScope do
      let (argument, _) ← TcM.openBinder () () carrier (.mkVar 0 ())
      let argumentType := KExpr.mkApp family argument
      let (witness, _) ← TcM.openBinder () () argumentType (.mkVar 0 ())
      let replayed ← RecM.inferCall source
      let checkedPi ← RecM.inferCall expected
      if replayed != expected || checkedPi != piType ||
          !compositeReplayAt source expected (← get) || !compositeReplayAt expected piType (← get) then
        return false
      let application := KExpr.mkApp (.mkApp source argument) witness
      let inferred ← RecM.inferCall application
      let reduced ← RecM.whnfCoreWithFlagsUncached application .DEF_EQ_CORE
      let reducedType ← RecM.inferCall reduced
      return inferred == argumentType && reduced == witness && reducedType == argumentType &&
        compositeReplayAt source expected (← get) && compositeReplayAt expected piType (← get) &&
        compositeReplayAt application argumentType (← get)
    if !used || (← get).lctx.size != before.lctx.size then return false
    modify fun state => { state with env := state.env.clearReductionCaches }
    match (RecM.infer source).run (methodsN 0) (← get) with
    | .error .maxRecFuel _ => pure ()
    | _ => return false
    let rebuiltPi ← RecM.inferCall expected
    let rebuilt ← RecM.inferCall source
    return rebuilt == expected && rebuiltPi == piType && compositeReplayAt source expected (← get) &&
      compositeReplayAt expected piType (← get)
  match TcM.runRec action (TcState.newLazyAnon polymorphicIdentity.1) with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

/-- The cached Pi retains its variable-headed codomain before declaration
growth and local insertion. Supplying the previously checked lambda then
creates the generated beta redex used by lambda inference. -/
private def compositeCodomainTransport (shape : Nat) (level : Ixon.Univ) : Bool :=
  let (env, target) := exposedLambdaType level 0 shape
  let (env, extra) := storeConst env
    ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.succ (.succ level)]⟩
  let action : RecM .anon Bool := RecM.withLctxScope do
    let .defn _ _ _ _ _ _ expected value _ _ ← TcM.getConst (m := .anon) ⟨target, ()⟩ | return false
    let .lam name bi domain body _ := value | return false
    let .all _ _ _ codomain _ := expected | return false
    let (fn, arguments) := body.collectSpine
    let some supplied := arguments[0]? | return false
    let functionType ← RecM.inferCall fn
    let typeSort ← RecM.inferCall functionType
    let suppliedType ← RecM.inferCall supplied
    let before ← get
    if !compositeReplayAt functionType typeSort before || !compositeReplayAt supplied suppliedType before then
      return false
    let _ ← RecM.inferCall (.mkConst ⟨extra, ()⟩ #[])
    if (← get).env.consts.size ≤ before.env.consts.size then return false
    let (call, _) ← TcM.openBinder name bi domain body
    let (carrier, _) ← TcM.openBinder () () (.mkSort levelOne) (.mkVar 0 ())
    let _ ← TcM.openBinder () () carrier (.mkVar 0 ())
    let typeReplayed ← RecM.inferCall functionType
    let lambdaReplayed ← RecM.inferCall supplied
    if typeReplayed != typeSort || lambdaReplayed != suppliedType then return false
    let generated ← RecM.inferCall call
    let reduced ← TcM.runIntern (cheapBetaReduce generated)
    let inferred ← RecM.inferCall value
    return (cheapBetaPlan? generated).isSome && generated != reduced && reduced == codomain &&
      inferred == expected && compositeReplayAt functionType typeSort (← get) &&
      compositeReplayAt supplied suppliedType (← get) && compositeReplayAt value expected (← get)
  match TcM.runRec action (TcState.newLazyAnon env) with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

/-- Compare both entire maps, including temporary-local and composite keys. -/
private def exactInferenceCaches (full only : List (KExpr .anon × KExpr .anon)) (state : TcState .anon) : Bool :=
  let expected (entries : List (KExpr .anon × KExpr .anon)) := entries.foldl
    (fun (cache : Std.HashMap (Address × Address) (KExpr .anon)) (source, result) =>
      cache.insert (source.addr, emptyCtxAddr) result) ∅
  let sameMap (actual predicted : Std.HashMap (Address × Address) (KExpr .anon)) :=
    actual.size == predicted.size && predicted.toList.all fun (key, result) => actual[key]? == some result
  sameMap state.env.inferCache (expected full) && sameMap state.env.inferOnlyCache (expected only)

/-- Whole-map expectations follow actual child calls and parent publications.
Entries from exited local scopes remain recorded; loading and partial failure
preserve both maps, and clearing begins a new set of publications. -/
private def compositeExactCacheHistory (initialOnly : Bool) : Bool :=
  let (source, warm) := polymorphicIdentity
  let (source, bad) := storeConst source
    ⟨.defn ⟨.defn, .safe, 0, .sort 0, .share 9⟩, #[], #[],
      #[.succ (.succ (.succ (.succ (.succ .zero))))]⟩
  let prop := KExpr.mkSort (m := .anon) .mkZero
  let sort := KExpr.mkSort (m := .anon) levelOne
  let sortTwo := KExpr.mkSort (m := .anon) levelTwo
  let pi := KExpr.mkAll () () sort sort
  let lambda := KExpr.mkLam () () sort (.mkVar 0 ())
  let application := KExpr.mkApp lambda prop
  let first := [(sort, sortTwo), (pi, sortTwo)]
  let only := if initialOnly then first else []
  let action : RecM .anon Bool := do
    if !exactInferenceCaches [] [] (← get) then return false
    let inferredPi ← if initialOnly then RecM.inferOnlyCall pi else RecM.inferCall pi
    if inferredPi != sortTwo || !exactInferenceCaches (if initialOnly then [] else first) only (← get) then
      return false
    let lambdaLocal := KExpr.mkFVar ⟨(← get).env.nextFVarId⟩ ()
    let inferredLambda ← RecM.inferCall lambda
    let checked := (if initialOnly then [] else first) ++ [(sort, sortTwo), (lambdaLocal, sort), (lambda, pi)]
    if inferredLambda != pi || !exactInferenceCaches checked only (← get) then return false
    let inferredApplication ← RecM.inferCall application
    let applied := checked ++ [(prop, sort), (application, sort)]
    if inferredApplication != sort || !exactInferenceCaches applied only (← get) then return false
    let fullPi ← RecM.inferCall pi
    let completed := applied ++ [(pi, sortTwo)]
    let onlyReplay ← RecM.inferOnlyCall application
    if fullPi != sortTwo || onlyReplay != sort || !exactInferenceCaches completed only (← get) then return false
    let (scopedLocal, scopePassed) ← RecM.withLctxScope do
      let (scopedLocal, _) ← TcM.openBinder () () sort (.mkVar 0 ())
      let localType ← RecM.inferCall scopedLocal
      return (scopedLocal, localType == sort && exactInferenceCaches (completed ++ [(scopedLocal, sort)]) only (← get))
    let retained := completed ++ [(scopedLocal, sort)]
    if !scopePassed || (← get).lctx.size != 0 || !exactInferenceCaches retained only (← get) then return false
    let _ ← TcM.getConst (m := .anon) ⟨warm, ()⟩
    if !exactInferenceCaches retained only (← get) then return false
    let rejected ← try
      let _ ← TcM.getConst (m := .anon) ⟨bad, ()⟩
      pure false
    catch _ => pure true
    if !rejected || !(← get).faultedAddrs.contains bad || !exactInferenceCaches retained only (← get) then return false
    modify fun state => {state with env := state.env.clearReductionCaches}
    if !exactInferenceCaches [] [] (← get) then return false
    let nextLocal := KExpr.mkFVar ⟨(← get).env.nextFVarId⟩ ()
    let rebuilt ← RecM.inferCall application
    return rebuilt == sort && nextLocal != lambdaLocal && exactInferenceCaches
      [(sort, sortTwo), (nextLocal, sort), (lambda, pi), (prop, sort), (application, sort)] [] (← get)
  match TcM.runRec action {TcState.newLazyAnon source with stats := true} with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

/-- The occupied-key frame needs no collision assumption: even a forged
different source hits the old full entry before executing recursive writes.
Semantic reuse separately requires the history's finite collision data. -/
private def compositeOccupiedForeignKey : Bool :=
  let (source, addr) := polymorphicIdentity
  let constant := KExpr.mkConst (m := .anon) ⟨addr, ()⟩ #[levelOne]
  let prop := KExpr.mkSort (m := .anon) .mkZero
  let forged := KExpr.app constant prop {(KExpr.mkApp constant prop).info with addr := constant.addr}
  match TcM.infer constant (TcState.newLazyAnon source) with
  | .error _ _ => false
  | .ok result state =>
      let before := {state with recFuel := 0, env := {state.env with
        inferOnlyCache := state.env.inferOnlyCache.insert (constant.addr, emptyCtxAddr) prop}}
      [false, true].all fun inferOnly =>
        match (RecM.infer forged).run (methodsN 0) {before with inferOnly} with
        | .error _ _ => false
        | .ok replay after => replay == result && result == identityType &&
            exactInferenceCaches [(constant, identityType)] [(constant, prop)] after &&
            after.env.nextFVarId == before.env.nextFVarId && after.recFuel == 0

/-- Let inference publishes its domain, value, opened body and parent in
the full map. Temporary-local entries survive cleanup, while replay at zero
fuel allocates no local and clearing forces fresh child publications. -/
private def letExactCacheHistory : Bool :=
  let prop := KExpr.mkSort (m := .anon) .mkZero
  let sort := KExpr.mkSort (m := .anon) levelOne
  let sortTwo := KExpr.mkSort (m := .anon) levelTwo
  let body := KExpr.mkLam () () (.mkVar 0 ()) (.mkVar 0 ())
  let source := KExpr.mkLet () sort prop body false
  let expected := KExpr.mkAll () () prop prop
  let action : RecM .anon Bool := do
    let checkFresh : RecM .anon Bool := do
      let start ← get
      let letLocal := KExpr.mkFVar ⟨start.env.nextFVarId⟩ ()
      let lambdaLocal := KExpr.mkFVar ⟨start.env.nextFVarId + 1⟩ ()
      let openedBody := KExpr.mkLam () () letLocal (.mkVar 0 ())
      let bodyType := KExpr.mkAll () () letLocal letLocal
      let result ← RecM.inferCall source
      let finished ← get
      return result == expected && finished.lctx.size == start.lctx.size &&
        finished.env.nextFVarId == start.env.nextFVarId + 2 && finished.deqCalls > start.deqCalls &&
        exactInferenceCaches [(sort, sortTwo), (prop, sort), (letLocal, sort), (lambdaLocal, letLocal),
          (openedBody, bodyType), (source, expected)] [] finished
    if !(← checkFresh) then return false
    let checked ← get
    for policy in [false, true] do
      match (RecM.infer source).run (methodsN 0) {checked with inferOnly := policy} with
      | .ok result replayed =>
          if result != expected || replayed.env.nextFVarId != checked.env.nextFVarId ||
              replayed.env.inferCache.size != checked.env.inferCache.size ||
              replayed.env.inferOnlyCache.size != 0 then return false
      | .error _ _ => return false
    modify fun state => {state with env := state.env.clearReductionCaches}
    return ← checkFresh
  match TcM.runRec action {TcState.newLazyAnon {} with stats := true} with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

/-- The inferred body type is a let-local application. Closing and value
substitution expose a lambda; cheap beta returns the declared proposition. -/
private def letGeneratedBetaEnvironment : Ixon.Env × Address := Id.run do
  let domain := Ixon.Expr.leanAll (.sort 0) (.sort 0)
  let identity := Ixon.Expr.leanLam (.sort 0) (.var 0)
  let (env, proposition) := storeConst {}
    ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.zero]⟩
  let (env, witness) := storeConst env
    ⟨.axio ⟨false, 0, .leanAll domain (.app (.var 0) (.ref 0 #[]))⟩,
      #[], #[proposition], #[.zero]⟩
  return storeConst env
    ⟨.defn ⟨.thm, .safe, 0, .ref 0 #[],
      .letE false domain identity (.app (.ref 1 #[]) (.var 0))⟩,
      #[], #[proposition, witness], #[.zero]⟩

private def letGeneratedTypeBeta : Bool :=
  let (source, target) := letGeneratedBetaEnvironment
  let action : RecM .anon Bool := do
    let .defn _ _ _ _ _ _ expected term _ _ ← TcM.getConst (m := .anon) ⟨target, ()⟩ | return false
    let .letE name domain value body _ _ := term | return false
    let .sort .. ← RecM.inferCall domain | return false
    let valueType ← RecM.inferCall value
    if valueType != domain then return false
    let changed ← RecM.withLctxScope do
      let (opened, fresh) ← TcM.openLet name domain value body
      let bodyType ← RecM.inferCall opened
      let closed ← TcM.runIntern (abstractFVars bodyType #[fresh])
      let substituted ← TcM.runIntern (subst closed value 0)
      let reduced ← TcM.runIntern (cheapBetaReduce substituted)
      return bodyType.hasFVars && bodyType != expected && substituted != expected &&
        (cheapBetaPlan? substituted).isSome && reduced == expected && !reduced.hasFVars
    if !changed || (← get).lctx.size != 0 then return false
    let result ← RecM.inferCall term
    return result == expected && compositeReplayAt term expected (← get)
  match TcM.runRec action (TcState.newLazyAnon source) with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

private def letNestedCapture : Bool :=
  let sort := KExpr.mkSort (m := .anon) levelOne
  let action : RecM .anon Bool := RecM.withLctxScope do
    let (carrier, _) ← TcM.openBinder () () sort (.mkVar 0 ())
    let inner := KExpr.mkLet () sort (.mkVar 0 ())
      (.mkLam () () (.mkVar 0 ()) (.mkVar 0 ())) false
    let term := KExpr.mkLet () sort carrier inner false
    let result ← RecM.inferCall term
    let expected := KExpr.mkAll () () carrier carrier
    return result == expected && result.hasFVars && (← get).lctx.size == 1 &&
      compositeReplayAt term expected (← get)
  match TcM.runRec action (TcState.newLazyAnon {}) with
  | .ok passed after => passed && after.lctx.size == 0
  | .error _ _ => false

private def letFailureCleanup : Bool :=
  let prop := KExpr.mkSort (m := .anon) .mkZero
  let sort := KExpr.mkSort (m := .anon) levelOne
  let sortTwo := KExpr.mkSort (m := .anon) levelTwo
  let sortThree := KExpr.mkSort (m := .anon) (.mkSucc levelTwo)
  let badValue := KExpr.mkLet () prop prop (.mkVar 0 ()) false
  let badBody := KExpr.mkLet () sort prop (.mkFVar ⟨99⟩ ()) false
  let rejectsValue := match TcM.infer badValue (TcState.newLazyAnon {}) with
    | .error .declTypeMismatch after => after.lctx.size == 0 && after.env.nextFVarId == 0 &&
        exactInferenceCaches [(prop, sort)] [(sort, sortTwo), (sortTwo, sortThree)] after
    | _ => false
  let cleansBody := match TcM.infer badBody (TcState.newLazyAnon {}) with
    | .error _ after => after.lctx.size == 0 && after.env.nextFVarId == 1 &&
        exactInferenceCaches [(sort, sortTwo), (prop, sort)] [] after
    | _ => false
  rejectsValue && cleansBody

private def recursiveLetPositions : Bool :=
  let prop := KExpr.mkSort (m := .anon) .mkZero
  let sort := KExpr.mkSort (m := .anon) levelOne
  let sortTwo := KExpr.mkSort (m := .anon) levelTwo
  let alias := KExpr.mkLet () sort prop (.mkVar 0 ()) false
  let functionType := KExpr.mkAll () () sort sort
  let functionValue := KExpr.mkLam () () sort (.mkVar 0 ())
  let function := KExpr.mkLet () functionType functionValue (.mkVar 0 ()) false
  let samples := [
    (KExpr.mkLam () () alias (.mkVar 0 ()), KExpr.mkAll () () alias alias),
    (KExpr.mkLam () () prop (.mkLet () prop (.mkVar 0 ()) (.mkVar 0 ()) false),
      KExpr.mkAll () () prop prop),
    (KExpr.mkAll () () sort (.mkLet () sort (.mkVar 0 ()) (.mkVar 0 ()) false), sortTwo),
    (KExpr.mkApp function prop, sort),
    (KExpr.mkLet () sort alias (.mkLam () () (.mkVar 0 ()) (.mkVar 0 ())) false,
      KExpr.mkAll () () alias alias)]
  samples.all fun (source, expected) =>
    match TcM.infer source (TcState.newLazyAnon {}) with
    | .ok result after => result == expected && after.lctx.size == 0 &&
        after.env.inferCache[(source.addr, emptyCtxAddr)]? == some expected &&
        compositeReplayAt source expected after
    | .error _ _ => false

private def recursiveLetEnvironment : Ixon.Env := Id.run do
  let alias := Ixon.Expr.letE false (.sort 1) (.sort 0) (.var 0)
  let firstType := Ixon.Expr.leanAll alias alias
  let firstValue := Ixon.Expr.leanLam alias (.var 0)
  let (env, _) := storeConst {}
    ⟨.defn ⟨.defn, .safe, 0, firstType, firstValue⟩, #[], #[], #[.zero, .succ .zero]⟩
  let secondType := Ixon.Expr.leanAll (.sort 0) (.sort 0)
  let secondValue := Ixon.Expr.leanLam (.sort 0) (.letE false (.sort 0) (.var 0) (.var 0))
  let (env, _) := storeConst env
    ⟨.defn ⟨.defn, .safe, 0, secondType, secondValue⟩, #[], #[], #[.zero]⟩
  return env

private def recursiveLetFailureCleanup : Bool :=
  let prop := KExpr.mkSort (m := .anon) .mkZero
  let invalid := KExpr.mkLet () prop prop (.mkVar 0 ()) false
  let source := KExpr.mkLam () () prop invalid
  match TcM.infer source (TcState.newLazyAnon {}) with
  | .error .declTypeMismatch after => after.lctx.size == 0 && after.env.nextFVarId == 1 &&
      !after.env.inferCache.contains (source.addr, emptyCtxAddr) &&
      !after.env.inferCache.contains (invalid.addr, emptyCtxAddr)
  | _ => false

private def sortExposureEnvironment (level : Ixon.Univ) (universes : UInt64 := 0) (withZeta : Bool := false)
    (withHead : Bool := false) :
    Ixon.Env × Array Address := Id.run do
  -- References pass the parameter itself, even when the tested level is composite.
  let arguments := if universes == 0 then #[] else #[2]
  let levels := #[level, .succ level] ++ if universes == 0 then #[] else #[.var 0]
  let function := Ixon.Expr.leanLam (.sort 1) (.var 0)
  let functionType := Ixon.Expr.leanAll (.sort 1) (.sort 1)
  let head := if withHead then Ixon.Expr.letE false functionType
    (.app (.leanLam functionType (.var 0)) function) (.var 0) else function
  let betaSort := Ixon.Expr.app head (.sort 0)
  let betaSort := if withZeta then Ixon.Expr.letE false (.sort 1) betaSort (.var 0) else betaSort
  let (env, carrier) := storeConst {}
    ⟨.axio ⟨false, universes, betaSort⟩, #[], #[], levels⟩
  let (env, witness) := storeConst env
    ⟨.axio ⟨false, universes, .ref 0 arguments⟩, #[], #[carrier], levels⟩
  let (env, otherCarrier) := storeConst env
    ⟨.axio ⟨false, universes, .sort 0⟩, #[], #[], levels⟩
  let betaCarrier := Ixon.Expr.app (.leanLam (.sort 0) (.var 0)) (.ref 0 arguments)
  let (env, betaWitness) := storeConst env
    ⟨.axio ⟨false, universes, betaCarrier⟩, #[], #[otherCarrier], levels⟩
  let domain := Ixon.Expr.ref 0 arguments
  let identityType := Ixon.Expr.leanAll domain domain
  let samples := [
    (identityType, Ixon.Expr.leanLam domain (.var 0)),
    (Ixon.Expr.sort 0, identityType),
    (domain, Ixon.Expr.letE false domain (.ref 1 arguments) (.var 0)),
    (identityType, Ixon.Expr.leanLam domain (.letE false domain (.var 0) (.var 0))),
    (Ixon.Expr.leanAll domain (.ref 2 arguments), Ixon.Expr.leanLam domain (.ref 3 arguments))]
  let mut env := env
  let mut targets := #[]
  for (type, value) in samples do
    let (next, target) := storeConst env
      ⟨.defn ⟨.defn, .safe, universes, type, value⟩,
        #[], #[carrier, witness, otherCarrier, betaWitness], levels⟩
    env := next
    targets := targets.push target
  return (env, targets)

/-- The domain's full inference cache keeps its original beta type while
sort exposure writes the normalized sort only to the three WHNF caches. -/
private def sortExposureInferencePaths (typeLevel warm instrumented noAccel : Bool)
    (lowerWarm : Nat := 0) (withZeta : Bool := false) (withHead : Bool := false) : Bool :=
  let level := if typeLevel then levelOne else KUniv.mkZero
  let (env, targets) := sortExposureEnvironment (if typeLevel then .succ .zero else .zero) 0 withZeta withHead
  (List.range 5).all fun shape =>
    let action : RecM .anon Bool := do
      let .defn _ _ _ _ _ _ expected value _ _ ← TcM.getConst (m := .anon) ⟨targets[shape]!, ()⟩ | return false
      let domain := match value with
        | .lam _ _ domain _ _ | .all _ _ domain _ _ | .letE _ domain _ _ _ _ => domain
        | _ => value
      let original ← RecM.inferCall domain
      if withZeta then
        let .letE .. := original | return false
      else
        let .app .. := original | return false
      let bodyType ← match shape, value with
        | 4, .lam _ _ _ (.const id _ _) _ => pure (← TcM.getConst id).ty
        | _, _ => pure original
      modify fun state => { state with recFuel := 1, inNativeReduce := false, stats := instrumented, noAccel }
      if lowerWarm != 0 then
        let normalized ← if lowerWarm == 1 then RecM.whnfCore original else RecM.whnfNoDelta original
        if normalized != KExpr.mkSort level then return false
        if lowerWarm == 2 then
          modify fun state => { state with env := { state.env with whnfCoreCache := {} } }
      if warm then
        let exposed ← RecM.ensureSortDirect original
        if exposed != level then return false
        let warmed := { (← get) with inNativeReduce := true }
        match (RecM.ensureSortDirect original).run (methodsN 0) warmed with
        | .error _ _ => return false
        | .ok exposed reused =>
            if exposed != level || reused.recFuel != 0 || !reused.inNativeReduce ||
                !exactInferenceCaches [(domain, original)] [] reused then return false
            set reused
      let result ← RecM.inferCall value
      let after ← get
      let first := KExpr.mkFVar (m := .anon) ⟨0⟩ ()
      let second := KExpr.mkFVar (m := .anon) ⟨1⟩ ()
      let children := match shape, value with
        | 0, _ => [(first, domain)]
        | 1, _ => []
        | 2, .letE _ _ witness _ _ _ => [(witness, domain), (first, domain)]
        | 3, _ => [(first, domain), (second, domain),
            (KExpr.mkLet () domain first (.mkVar 0 ()) false, domain)]
        | 4, .lam _ _ _ body _ => [(body, bodyType)]
        | _, _ => []
      let sort := KExpr.mkSort (m := .anon) level
      let key := (original.addr, emptyCtxAddr)
      return result == expected && after.recFuel == 0 && after.lctx.size == 0 &&
        after.env.nextFVarId == (if shape == 3 then 2 else 1) && after.inNativeReduce == warm &&
        after.env.whnfCache[key]? == some sort && after.env.whnfNoDeltaCache[key]? == some sort &&
        after.env.whnfCoreCache[key]? == (if lowerWarm == 2 then none else some sort) &&
        exactInferenceCaches ((domain, original) :: (children ++ [(value, expected)])) [] after &&
        compositeReplayAt value expected after
    match TcM.runRec action (TcState.newLazyAnon env) with
    | .ok passed _ => passed
    | .error _ _ => false

private inductive WhnfWarmLayer
  | cold | core | noDelta | full
  deriving BEq

/-- Warm entries come from the actual layer that produces them. Keep
unrelated entries in every map and discard lower entries when isolating an
upper hit. The trial starts with fresh key memoization. -/
private def mixedWhnfCaches (shape : Nat) (layer : WhnfWarmLayer)
    (legacy native instrumented noAccel inferOnly : Bool) (withZeta : Bool := false) : Bool :=
  let prop := KExpr.mkSort (m := .anon) .mkZero
  let sort := KExpr.mkSort (m := .anon) levelOne
  let argument := if legacy then KExpr.mkVar 0 () else prop
  let body := if shape == 0 then prop else if shape == 1 then
      KExpr.mkAll () () (.mkVar 0 ()) (.mkVar 1 ())
    else KExpr.mkLam () () (.mkVar 0 ()) (.mkVar 1 ())
  let expected := if shape == 0 then prop else if shape == 1 then
      KExpr.mkAll () () argument (if legacy then .mkVar 1 () else prop)
    else KExpr.mkLam () () argument (if legacy then .mkVar 1 () else prop)
  let source := if withZeta then KExpr.mkLet () sort argument
      (.mkApp (.mkLam () () sort (.mkLet () sort (.mkVar 0 ()) body false)) (.mkVar 0 ())) false
    else KExpr.mkApp (.mkLam () () sort body) argument
  let sameMap (actual predicted : Std.HashMap (Address × Address) (KExpr .anon)) :=
    actual.size == predicted.size && predicted.toList.all fun (key, result) => actual[key]? == some result
  let action : RecM .anon Bool := do
    if legacy then
      TcM.pushLocal sort
      TcM.pushLocal sort
    let seed : Std.HashMap (Address × Address) (KExpr .anon) :=
      (∅ : Std.HashMap (Address × Address) (KExpr .anon)).insert (prop.addr, emptyCtxAddr) prop
    modify fun state => { state with env := { state.env with
      whnfCache := seed, whnfNoDeltaCache := seed, whnfCoreCache := seed,
      whnfNoDeltaCheapCache := seed, whnfCoreCheapCache := seed,
      inferCache := state.env.inferCache.insert (prop.addr, emptyCtxAddr) sort,
      inferOnlyCache := state.env.inferOnlyCache.insert (sort.addr, emptyCtxAddr) (.mkSort levelTwo) } }
    match layer with
    | .cold => pure ()
    | .core => if (← RecM.whnfCore source) != expected then return false
    | .noDelta =>
        if (← RecM.whnfNoDelta source) != expected then return false
        modify fun state => { state with env := { state.env with whnfCoreCache := seed } }
    | .full =>
        if (← RecM.whnf source) != expected then return false
        modify fun state => { state with env := { state.env with whnfCoreCache := seed, whnfNoDeltaCache := seed } }
    modify fun state => { state with
      ctxAddrCache := {},
      recFuel := if layer == .full then 0 else 1, inNativeReduce := native,
      stats := instrumented, stepTrace := instrumented, whnfCalls := 17, whnfMisses := 11, noAccel, inferOnly }
    let before ← get
    let methods := if layer == .full then methodsN 0 else methodsN 2
    match (RecM.whnf source).run methods before with
    | .error _ _ => return false
    | .ok result after =>
        let .ok key keyed := TcM.whnfKey source after | return false
        let core := if layer == .cold || layer == .core then before.env.whnfCoreCache.insert key expected
          else before.env.whnfCoreCache
        let noDelta := if native || layer == .full then before.env.whnfNoDeltaCache
          else before.env.whnfNoDeltaCache.insert key expected
        let full := if native || layer == .full then before.env.whnfCache
          else before.env.whnfCache.insert key expected
        let replayRun := match layer with
          | .cold | .core => (RecM.whnfCore source).run (methodsN 0) after
          | .noDelta => (RecM.whnfNoDelta source).run (methodsN 0) after
          | .full => (RecM.whnf source).run (methodsN 0) after
        let .ok replay replayed := replayRun | return false
        return result == expected && replay == expected && after.recFuel == 0 && replayed.recFuel == 0 &&
          after.whnfCalls == (if instrumented then 18 else 17) &&
          after.whnfMisses == (if instrumented && layer != .full then 12 else 11) &&
          sameMap after.env.whnfCoreCache core && sameMap after.env.whnfNoDeltaCache noDelta &&
          sameMap after.env.whnfCache full && sameMap after.env.whnfCoreCheapCache before.env.whnfCoreCheapCache &&
          sameMap after.env.whnfNoDeltaCheapCache before.env.whnfNoDeltaCheapCache &&
          sameMap after.env.inferCache before.env.inferCache && sameMap after.env.inferOnlyCache before.env.inferOnlyCache &&
          after.lctx.size == before.lctx.size && after.ctx.size == before.ctx.size && after.ctxId == before.ctxId &&
          after.env.nextFVarId == before.env.nextFVarId && after.inNativeReduce == native && after.inferOnly == inferOnly &&
          after.ctxAddrCache.size == (if legacy then 1 else 0) && keyed.ctxAddrCache.size == after.ctxAddrCache.size &&
          sameMap replayed.env.whnfCoreCache core && sameMap replayed.env.whnfNoDeltaCache noDelta &&
          sameMap replayed.env.whnfCache full && replayed.env.intern.exprs.size == after.env.intern.exprs.size
  match TcM.runRec action (TcState.newLazyAnon {}) with
  | .ok passed _ => passed
  | .error _ _ => false

private def mixedWhnfFuelFailure (layer : WhnfWarmLayer) (withZeta : Bool := false) : Bool :=
  let prop := KExpr.mkSort (m := .anon) .mkZero
  let source := KExpr.mkApp (.mkLam () () (.mkSort levelOne) (.mkVar 0 ())) prop
  let source := if withZeta then KExpr.mkLet () (.mkSort levelOne) source (.mkVar 0 ()) false else source
  let action : RecM .anon Bool := do
    match layer with
    | .core => discard <| RecM.whnfCore source
    | .noDelta => discard <| RecM.whnfNoDelta source
    | _ => pure ()
    modify fun state => { state with recFuel := 0, stats := true, whnfCalls := 17, whnfMisses := 11 }
    let before ← get
    match (RecM.whnf source).run (methodsN 2) before with
    | .error .maxRecFuel after =>
        return after.recFuel == 0 && after.whnfCalls == 18 && after.whnfMisses == 12 &&
          after.env.whnfCache.size == 0 && after.env.whnfCoreCache.size == before.env.whnfCoreCache.size &&
          after.env.whnfNoDeltaCache.size == before.env.whnfNoDeltaCache.size
    | _ => return false
  match TcM.runRec action (TcState.newLazyAnon {}) with
  | .ok passed _ => passed
  | .error _ _ => false

private def mixedWhnfCases : TestSeq :=
  [WhnfWarmLayer.cold, .core, .noDelta, .full].foldl (fun suite layer => suite ++
    test s!"mixed WHNF: layer {reprStr (match layer with | .cold => 0 | .core => 1 | .noDelta => 2 | .full => 3)} preserves exact maps, fuel, and keys"
      ((List.range 3).all fun shape => [false, true].all fun legacy => [false, true].all fun native =>
        [false, true].all fun instrumented => [false, true].all fun noAccel => [false, true].all fun inferOnly =>
          mixedWhnfCaches shape layer legacy native instrumented noAccel inferOnly))
    (test "mixed WHNF: lower cache hits do not bypass the public miss fuel check"
      ([WhnfWarmLayer.cold, .core, .noDelta].all fun layer => mixedWhnfFuelFailure layer))

/-- Alternate two explicit lets with beta. A dependent result forces
substitution beneath its remaining binder, and every reduction counts toward
the actual bounded loop before its final unchanged iteration. -/
private def letWhnfLoopResult (typeLevel : Bool) (flags : WhnfFlags) (shape : Nat) : Bool :=
  let carrier := KExpr.mkSort (m := .anon) (if typeLevel then levelOne else .mkZero)
  let carrierType := KExpr.mkSort (m := .anon) (if typeLevel then levelTwo else levelOne)
  let body := if shape == 0 then KExpr.mkVar 0 () else if shape == 1 then
      KExpr.mkAll () () (.mkVar 0 ()) (.mkVar 1 ())
    else KExpr.mkLam () () (.mkVar 0 ()) (.mkVar 0 ())
  let expected := if shape == 0 then carrier else if shape == 1 then
      KExpr.mkAll () () carrier carrier
    else KExpr.mkLam () () carrier (.mkVar 0 ())
  let source := KExpr.mkLet () carrierType carrier
    (.mkApp (.mkLam () () carrierType (.mkLet () carrierType (.mkVar 0 ()) body false)) (.mkVar 0 ())) false
  let action : RecM .anon Bool := do
    let inferred ← RecM.inferCall source
    let expectedType ← RecM.inferCall expected
    if !(← RecM.isDefEq inferred expectedType) then return false
    let before ← get
    let mut current := source
    for isLet in [true, false, true] do
      if isLet then
        let .letE .. := current | return false
      else
        let .app .. := current | return false
      let .next next ← RecM.whnfCoreWithFlagsStep current flags | return false
      current := next
    let .done terminal ← RecM.whnfCoreWithFlagsStep current flags | return false
    let stepped ← get
    if !sameSourceExpr terminal expected then return false
    match (RecM.runBounded (fun term => RecM.whnfCoreWithFlagsStep term flags) 3 source).run (methodsN 2) before with
    | .error .maxRecDepth exhausted =>
        if exhausted.env.intern.exprs.size != stepped.env.intern.exprs.size then return false
    | _ => return false
    match (RecM.runBounded (fun term => RecM.whnfCoreWithFlagsStep term flags) 4 source).run (methodsN 2) before with
    | .ok result after =>
        return sameSourceExpr result expected && after.env.intern.exprs.size == stepped.env.intern.exprs.size &&
          after.recFuel == before.recFuel && after.lctx.size == before.lctx.size &&
          after.env.nextFVarId == before.env.nextFVarId
    | _ => return false
  match TcM.runRec action (TcState.newLazyAnon {}) with
  | .ok passed _ => passed
  | .error _ _ => false

/-- Recursive head calls may contain their own beta steps and cache writes.
Their method depth is separate from the enclosing two-iteration loop. -/
private def headWhnfLoopResult (depth : Nat) (typeLevel : Bool) (flags : WhnfFlags)
    (shape : Nat) (warm native : Bool) (innerWarm otherPartition : Bool := false) : Bool :=
  let carrier := KExpr.mkSort (m := .anon) (if typeLevel then levelOne else .mkZero)
  let carrierType := KExpr.mkSort (m := .anon) (if typeLevel then levelTwo else levelOne)
  let body := if shape == 0 then KExpr.mkVar 0 () else if shape == 1 then
      KExpr.mkAll () () (.mkVar 0 ()) (.mkVar 1 ())
    else KExpr.mkLam () () (.mkVar 0 ()) (.mkVar 0 ())
  let expected := if shape == 0 then carrier else if shape == 1 then
      KExpr.mkAll () () carrier carrier
    else KExpr.mkLam () () carrier (.mkVar 0 ())
  let function := KExpr.mkLam () () carrierType body
  let sameMap (actual predicted : Std.HashMap (Address × Address) (KExpr .anon)) :=
    actual.size == predicted.size && predicted.toList.all fun (key, result) => actual[key]? == some result
  let action : RecM .anon Bool := do
    let functionType ← RecM.inferCall function
    let identity := KExpr.mkLam () () functionType (.mkVar 0 ())
    let identityType := KExpr.mkAll () () functionType functionType
    let inner := KExpr.mkLet () identityType
      (.mkApp (.mkLam () () identityType (.mkVar 0 ())) identity) (.mkVar 0 ()) false
    let value := if depth == 0 then function else if depth == 1 then
      KExpr.mkApp identity function else KExpr.mkApp inner function
    let head := KExpr.mkLet () functionType value (.mkVar 0 ()) false
    let source := KExpr.mkApp head carrier
    let inferred ← RecM.inferCall source
    let expectedType ← RecM.inferCall expected
    if !(← RecM.isDefEq inferred expectedType) then return false
    let seed : Std.HashMap (Address × Address) (KExpr .anon) :=
      (∅ : Std.HashMap (Address × Address) (KExpr .anon)).insert (carrierType.addr, emptyCtxAddr) carrierType
    modify fun state => { state with
      recFuel := 0, inNativeReduce := native, ctxAddrCache := {},
      env := { state.env with
        whnfCache := seed, whnfNoDeltaCache := seed, whnfCoreCache := seed,
        whnfNoDeltaCheapCache := seed, whnfCoreCheapCache := seed } }
    if depth == 2 && innerWarm then
      let innerFlags := if otherPartition then
        (if flags.isFull then WhnfFlags.DEF_EQ_CORE else .FULL) else flags
      if (← RecM.whnfCoreWithFlags inner innerFlags) != identity then return false
    if warm then
      if (← RecM.whnfCoreWithFlags head flags) != function then return false
    let before ← get
    let budget := if warm then 1 else if depth == 2 && innerWarm && !otherPartition then 2 else depth + 1
    let headKey := (head.addr, emptyCtxAddr)
    let parentKey := (source.addr, emptyCtxAddr)
    let writes := if depth == 2 then (seed.insert (inner.addr, emptyCtxAddr) identity).insert headKey function
      else seed.insert headKey function
    let maps (after : TcState .anon) (selected : Std.HashMap (Address × Address) (KExpr .anon)) :=
      sameMap after.env.whnfCoreCache (if flags.isFull then selected else before.env.whnfCoreCache) &&
      sameMap after.env.whnfCoreCheapCache (if flags.isFull then before.env.whnfCoreCheapCache else selected) &&
      sameMap after.env.whnfNoDeltaCache seed && sameMap after.env.whnfNoDeltaCheapCache seed &&
      sameMap after.env.whnfCache seed && sameMap after.env.inferCache before.env.inferCache &&
      sameMap after.env.inferOnlyCache before.env.inferOnlyCache
    match (RecM.runBounded (fun term => RecM.whnfCoreWithFlagsStep term flags) 2 source).run
        (methodsN (budget - 1)) before with
    | .error .maxRecFuel _ => pure ()
    | _ => return false
    let .error .maxRecDepth exhausted :=
      (RecM.runBounded (fun term => RecM.whnfCoreWithFlagsStep term flags) 1 source).run
        (methodsN budget) before | return false
    if !maps exhausted writes then return false
    let .ok rawResult reduced := (RecM.runBounded (fun term => RecM.whnfCoreWithFlagsStep term flags) 2 source).run
      (methodsN budget) before | return false
    if !sameSourceExpr rawResult expected || !maps reduced writes ||
        reduced.env.intern.exprs.size != exhausted.env.intern.exprs.size then return false
    match (RecM.whnfCoreWithFlags source flags).run (methodsN budget) before with
    | .error _ _ => return false
    | .ok result after =>
        let published := writes.insert parentKey result
        let .ok replay reused := (RecM.whnfCoreWithFlags source flags).run (methodsN 0) after | return false
        return sameSourceExpr result expected && replay == result && maps after published && maps reused published &&
          after.recFuel == 0 && reused.recFuel == 0 && after.inNativeReduce == native &&
          after.lctx.size == before.lctx.size && after.env.nextFVarId == before.env.nextFVarId &&
          after.ctxAddrCache.size == 0 && after.env.intern.exprs.size == reduced.env.intern.exprs.size &&
          reused.env.intern.exprs.size == after.env.intern.exprs.size
  match TcM.runRec action (TcState.newLazyAnon {}) with
  | .ok passed _ => passed
  | .error _ _ => false

/-- The parent, its head, and a third query use different legacy radii.
Memoizing the head must preserve even a preexisting parent digest. -/
private def headWhnfLegacyKeys (retained : Bool) : Bool :=
  let sort := KExpr.mkSort (m := .anon) levelOne
  let function := KExpr.mkLam () () sort (.mkLam () () sort (.mkVar 2 ()))
  let functionType := KExpr.mkAll () () sort (.mkAll () () sort sort)
  let head := KExpr.mkLet () functionType function (.mkVar 0 ()) false
  let source := KExpr.mkApp head (.mkVar 2 ())
  let query := KExpr.mkVar (m := .anon) 1 ()
  let expected := KExpr.mkLam () () sort (.mkVar 1 ())
  let action : RecM .anon Bool := do
    for _ in [0, 1, 2] do TcM.pushLocal sort
    modify fun state => { state with recFuel := 0, ctxAddrCache :=
      if retained then (∅ : Std.HashMap (Address × UInt64) Address).insert (state.ctxId, source.lbr) sort.addr else {} }
    let before ← get
    let .ok parentKey _ := TcM.whnfKey source before | return false
    let .ok headKey _ := TcM.whnfKey head before | return false
    let .ok queryKey _ := TcM.whnfKey query before | return false
    let .ok result after := (RecM.whnfCore source).run (methodsN 1) before | return false
    let .ok parentAgain _ := TcM.whnfKey source after | return false
    let .ok headAgain _ := TcM.whnfKey head after | return false
    let .ok queryAgain _ := TcM.whnfKey query after | return false
    let .ok replay reused := (RecM.whnfCore source).run (methodsN 0) after | return false
    return source.lbr == 3 && head.lbr == 1 && query.lbr == 2 && sameSourceExpr result expected && replay == result &&
      parentAgain == parentKey && headAgain == headKey && queryAgain == queryKey &&
      after.ctxAddrCache.size == 2 && reused.ctxAddrCache.size == 2 &&
      after.env.whnfCoreCache.size == 2 && after.env.whnfCoreCache[headKey]? == some function &&
      after.env.whnfCoreCache[parentKey]? == some result && after.ctxId == before.ctxId &&
      after.ctx.size == before.ctx.size && after.recFuel == 0 &&
      (!retained || parentKey.2 == sort.addr)
  match TcM.runRec action (TcState.newLazyAnon {}) with
  | .ok passed _ => passed
  | .error _ _ => false

/-- Compare every WHNF partition, including keys from exited local scopes. -/
private def exactWhnfCaches (full noDelta noDeltaCheap core coreCheap : List (KExpr .anon × KExpr .anon))
    (state : TcState .anon) : Bool :=
  let expected (entries : List (KExpr .anon × KExpr .anon)) := entries.foldl
    (fun (cache : Std.HashMap (Address × Address) (KExpr .anon)) (source, result) =>
      cache.insert (source.addr, emptyCtxAddr) result) ∅
  let sameMap (actual predicted : Std.HashMap (Address × Address) (KExpr .anon)) :=
    actual.size == predicted.size && predicted.toList.all fun (key, result) => actual[key]? == some result
  sameMap state.env.whnfCache (expected full) && sameMap state.env.whnfNoDeltaCache (expected noDelta) &&
    sameMap state.env.whnfNoDeltaCheapCache (expected noDeltaCheap) &&
    sameMap state.env.whnfCoreCache (expected core) && sameMap state.env.whnfCoreCheapCache (expected coreCheap)

/-- A history mixes real publications and hits across all supported layers.
Partial loop failure and a failing local scope retain their completed writes;
clearing discards them, and a new call rebuilds the required entries. -/
private def whnfExactCacheHistory (typeLevel nativeFirst inferOnly noAccel : Bool) : Bool :=
  let carrier := KExpr.mkSort (m := .anon) (if typeLevel then levelOne else .mkZero)
  let carrierType := KExpr.mkSort (m := .anon) (if typeLevel then levelTwo else levelOne)
  let identity := KExpr.mkLam () () carrierType (.mkVar 0 ())
  let identityType := KExpr.mkAll () () carrierType carrierType
  let head := KExpr.mkLet () identityType identity (.mkVar 0 ()) false
  let parent := KExpr.mkApp head carrier
  let other := KExpr.mkApp (.mkLam () () carrierType (.mkAll () () (.mkVar 0 ()) (.mkVar 1 ()))) carrier
  let otherResult := KExpr.mkAll () () carrier carrier
  let builder := KExpr.mkLam () () carrierType (.mkLam () () (.mkVar 0 ()) (.mkVar 0 ()))
  let builderType := KExpr.mkAll () () carrierType (.mkAll () () (.mkVar 0 ()) (.mkVar 1 ()))
  let builderHead := KExpr.mkLet () builderType builder (.mkVar 0 ()) false
  let maps (full noDelta core cheap : List (KExpr .anon × KExpr .anon)) (state : TcState .anon) :=
    exactWhnfCaches full noDelta [] core cheap state && exactInferenceCaches [] [] state
  let action : RecM .anon Bool := do
    modify fun state => {state with recFuel := 0, stats := true, inNativeReduce := nativeFirst, inferOnly, noAccel}
    if !maps [] [] [] [] (← get) then return false
    let .ok warmed afterHead := (RecM.whnfCore head).run (methodsN 0) (← get) | return false
    set afterHead
    let first := [(head, identity)]
    if warmed != identity || !maps [] [] first [] (← get) then return false
    let .error .maxRecDepth exhausted :=
      (RecM.runBounded (fun term => RecM.whnfCoreWithFlagsStep term .DEF_EQ_CORE) 1 parent).run
        (methodsN 1) (← get) | return false
    set exhausted
    if !maps [] [] first first (← get) then return false
    modify fun state => {state with recFuel := 1}
    let .ok reduced afterParent := (RecM.whnf parent).run (methodsN 1) (← get) | return false
    set afterParent
    let published := [(parent, carrier)]
    let upper := if nativeFirst then [] else published
    let core := first ++ published
    if reduced != carrier || (← get).recFuel != 0 || !maps upper upper core first (← get) then return false
    let .ok different afterOther := (RecM.whnfCoreWithFlags other .DEF_EQ_CORE).run (methodsN 1) (← get) | return false
    set afterOther
    let cheap := first ++ [(other, otherResult)]
    if different != otherResult || !maps upper upper core cheap (← get) then return false
    let runScope (expectedLocal : KExpr .anon) (failAfter : Bool) : RecM .anon Bool := do
      let scopeAction : RecM .anon Bool := RecM.withLctxScope do
        let (openedCarrier, _) ← TcM.openBinder () () carrierType (.mkVar 0 ())
        if openedCarrier != expectedLocal then return false
        let source := KExpr.mkApp builderHead openedCarrier
        let expected := KExpr.mkLam () () openedCarrier (.mkVar 0 ())
        modify fun state => {state with recFuel := 1, inNativeReduce := false, inferOnly := !state.inferOnly}
        let .ok value after := (RecM.whnf source).run (methodsN 1) (← get) | return false
        set after
        if !sameSourceExpr value expected then return false
        if failAfter then throw (.other "WHNF history scope failure")
        return true
      if failAfter then
        try
          discard scopeAction
          return false
        catch error =>
          return match error with
            | .other message => message == "WHNF history scope failure"
            | _ => false
      else scopeAction
    let firstLocal := KExpr.mkFVar ⟨(← get).env.nextFVarId⟩ ()
    if !(← runScope firstLocal false) then return false
    let firstScoped := (KExpr.mkApp builderHead firstLocal, KExpr.mkLam () () firstLocal (.mkVar 0 ()))
    let scopedCore := core ++ [(builderHead, builder), firstScoped]
    let scopedUpper := upper ++ [firstScoped]
    if (← get).lctx.size != 0 || !maps scopedUpper scopedUpper scopedCore cheap (← get) then return false
    let secondLocal := KExpr.mkFVar ⟨(← get).env.nextFVarId⟩ ()
    if secondLocal == firstLocal || !(← runScope secondLocal true) then return false
    let secondScoped := (KExpr.mkApp builderHead secondLocal, KExpr.mkLam () () secondLocal (.mkVar 0 ()))
    let finalCore := scopedCore ++ [secondScoped]
    let finalUpper := scopedUpper ++ [secondScoped]
    if (← get).lctx.size != 0 || !maps finalUpper finalUpper finalCore cheap (← get) then return false
    modify fun state => {state with recFuel := if nativeFirst then 1 else 0}
    let .ok replay afterReplay := (RecM.whnf parent).run (methodsN 0) (← get) | return false
    set afterReplay
    let replayedUpper := finalUpper ++ published
    if replay != carrier || (← get).recFuel != 0 || !maps replayedUpper replayedUpper finalCore cheap (← get) then return false
    let nextLocal := (← get).env.nextFVarId
    modify fun state => {state with recFuel := 1, env := state.env.clearReductionCaches}
    let cleared ← get
    if !maps [] [] [] [] cleared then return false
    match (RecM.whnf parent).run (methodsN 0) cleared with
    | .error .maxRecFuel failed => if !maps [] [] [] [] failed then return false
    | _ => return false
    let .ok rebuilt afterRebuild := (RecM.whnf parent).run (methodsN 1) cleared | return false
    let .ok lastReplay final := (RecM.whnf parent).run (methodsN 0) afterRebuild | return false
    return rebuilt == carrier && lastReplay == carrier && maps published published core [] final &&
      final.recFuel == 0 && final.lctx.size == 0 && final.env.nextFVarId == nextLocal && final.inferOnly == inferOnly
  match TcM.runRec action (TcState.newLazyAnon {}) with
  | .ok passed _ => passed
  | .error _ _ => false

/-- Lookup alone cannot identify the query's source: forged metadata can
hit a real prior publication. Clearing exposes the different computation. -/
private def whnfForeignHistoryKey (native : Bool) : Bool := Id.run do
  let prop := KExpr.mkSort (m := .anon) .mkZero
  let sort := KExpr.mkSort (m := .anon) levelOne
  let source := KExpr.mkApp (.mkLam () () sort (.mkVar 0 ())) prop
  let alien := KExpr.mkApp (.mkLam () () sort (.mkAll () () (.mkVar 0 ()) (.mkVar 1 ()))) prop
  let forged := match alien with
    | .app function argument info => KExpr.app function argument {info with addr := source.addr}
    | _ => alien
  let expected := KExpr.mkAll () () prop prop
  let before := {TcState.newLazyAnon {} with recFuel := 1}
  let .ok result stored := (RecM.whnf source).run (methodsN 1) before | return false
  let .ok replay after := (RecM.whnf forged).run (methodsN 0) {stored with recFuel := 0, inNativeReduce := native} | return false
  let .ok fresh _ := (RecM.whnf forged).run (methodsN 1)
    {after with recFuel := 1, inNativeReduce := false, env := after.env.clearReductionCaches} | return false
  return result == prop && replay == prop && !sameSourceExpr source forged && fresh == expected &&
    exactWhnfCaches [(source, prop)] [(source, prop)] [] [(source, prop)] [] after && after.recFuel == 0

private def letWhnfCases : TestSeq :=
  [WhnfWarmLayer.cold, .core, .noDelta, .full].foldl (fun suite layer => suite ++
    test s!"let WHNF: layer {reprStr (match layer with | .cold => 0 | .core => 1 | .noDelta => 2 | .full => 3)} preserves exact maps across let-beta-let reduction"
      ((List.range 3).all fun shape => [false, true].all fun legacy => [false, true].all fun native =>
        [false, true].all fun instrumented => [false, true].all fun noAccel => [false, true].all fun inferOnly =>
          mixedWhnfCaches shape layer legacy native instrumented noAccel inferOnly true))
    (test "let WHNF: lower cache hits still require the public miss charge"
      ([WhnfWarmLayer.cold, .core, .noDelta].all fun layer => mixedWhnfFuelFailure layer true)
    ++ test "let WHNF: every let and beta step consumes one loop iteration before the final done"
      ([false, true].all fun typeLevel => [WhnfFlags.FULL, .DEF_EQ_CORE].all fun flags =>
        (List.range 3).all fun shape => letWhnfLoopResult typeLevel flags shape))
  ++ test "let sort exposure: all binder forms retain their unreduced original type across cache layers"
    ([false, true].all fun typeLevel => [false, true].all fun instrumented => [false, true].all fun noAccel =>
      [0, 1, 2].all fun lowerWarm => sortExposureInferencePaths typeLevel false instrumented noAccel lowerWarm true)
  ++ test "let sort exposure: retained outer hits work without recursive methods or remaining fuel"
    ([false, true].all fun typeLevel => [false, true].all fun instrumented => [false, true].all fun noAccel =>
      sortExposureInferencePaths typeLevel true instrumented noAccel 0 true)
  ++ test "let sort exposure: declarations retain parameters under persistent and cleared caches"
    ([0, 1].all fun clearEvery =>
      allSucceeded (sortExposureEnvironment .zero 0 true).1 9 { clearEvery } &&
      allSucceeded (sortExposureEnvironment (.succ .zero) 0 true).1 9 { clearEvery } &&
      allSucceeded (sortExposureEnvironment (.var 0) 1 true).1 9 { clearEvery })

private def sortExposureFailures (withZeta : Bool := false) (withHead : Bool := false) : Bool :=
  let function := Ixon.Expr.leanLam (.sort 1) (.leanAll (.var 0) (.var 1))
  let head := if withHead then Ixon.Expr.letE false (.leanAll (.sort 1) (.sort 1)) function (.var 0) else function
  let betaPi := Ixon.Expr.app head (.sort 0)
  let betaPi := if withZeta then Ixon.Expr.letE false (.sort 1) betaPi (.var 0) else betaPi
  let (env, carrierAddr) := storeConst {}
    ⟨.axio ⟨false, 0, betaPi⟩, #[], #[], #[.zero, .succ .zero]⟩
  (List.range 3).all fun shape =>
    let carrier := KExpr.mkConst (m := .anon) ⟨carrierAddr, ()⟩ #[]
    let prop := KExpr.mkSort (m := .anon) .mkZero
    let source := if shape == 0 then KExpr.mkLam () () carrier (.mkVar 0 ())
      else if shape == 1 then KExpr.mkLet () carrier prop (.mkVar 0 ()) false
      else KExpr.mkAll () () prop carrier
    match TcM.getConst (m := .anon) ⟨carrierAddr, ()⟩ (TcState.newLazyAnon env) with
    | .error _ _ => false
    | .ok concrete loaded =>
        match TcM.infer source loaded with
        | .error .typeExpected failed =>
            let children := if shape == 2 then [(prop, KExpr.mkSort levelOne)] else []
            failed.lctx.size == 0 && failed.env.nextFVarId == (if shape == 2 then 1 else 0) &&
              failed.env.whnfCache[(concrete.ty.addr, emptyCtxAddr)]? == some (KExpr.mkAll () () prop prop) &&
              exactInferenceCaches ((carrier, concrete.ty) :: children) [] failed
        | _ => false

private def sortExposureCases : TestSeq :=
  test "sort exposure: dependent types, lambdas, and lets check in Prop and Type under both cache policies"
    ([Ixon.Univ.zero, .succ .zero].all fun level =>
      [0, 1].all fun clearEvery => allSucceeded (sortExposureEnvironment level).1 9 { clearEvery })
  ++ test "sort exposure: binder validation and changed body beta retain declaration universe parameters"
    ([Ixon.Univ.var 0, .max (.var 0) (.succ (.var 0))].all fun level =>
      [0, 1].all fun clearEvery => allSucceeded (sortExposureEnvironment level 1).1 9 { clearEvery })
  ++ test "sort exposure: cold binder checks preserve exact child caches and publish their returned types"
    ([false, true].all fun typeLevel => [false, true].all fun instrumented =>
      [false, true].all fun noAccel => sortExposureInferencePaths typeLevel false instrumented noAccel)
  ++ test "sort exposure: warm binder checks and zero-method exposure need no remaining reduction fuel"
    ([false, true].all fun typeLevel => [false, true].all fun instrumented =>
      [false, true].all fun noAccel => sortExposureInferencePaths typeLevel true instrumented noAccel)
  ++ test "sort exposure: a core hit retains original child types through binder, lambda, and let inference"
    ([false, true].all fun typeLevel => [false, true].all fun instrumented =>
      [false, true].all fun noAccel => sortExposureInferencePaths typeLevel false instrumented noAccel 1)
  ++ test "sort exposure: an isolated no-delta hit publishes the outer result and preserves exited-scope histories"
    ([false, true].all fun typeLevel => [false, true].all fun instrumented =>
      [false, true].all fun noAccel => sortExposureInferencePaths typeLevel false instrumented noAccel 2)
  ++ test "sort exposure: a reduced Pi is rejected as a sort and failed binder scopes restore locals"
    sortExposureFailures
  ++ test "let sort exposure: a let returning a Pi is rejected and failed binder scopes restore locals"
    (sortExposureFailures true)

private def headWhnfCases : TestSeq :=
  (List.range 3).foldl (fun suite depth => suite ++
    [false, true].foldl (fun suite warm => suite ++
      test s!"application head WHNF: depth {depth}, warm {warm}, preserves nested writes and both fuel bounds"
        ([false, true].all fun typeLevel => [WhnfFlags.FULL, .DEF_EQ_CORE].all fun flags =>
          (List.range 3).all fun shape => [false, true].all fun native =>
            headWhnfLoopResult depth typeLevel flags shape warm native)) .done)
    (test "application head WHNF: distinct legacy radii retain all keys through head memoization"
      ([false, true].all headWhnfLegacyKeys))
  ++ test "application head WHNF: an isolated inner hit reduces method depth and supplies later parent hits"
    ([false, true].all fun typeLevel => [WhnfFlags.FULL, .DEF_EQ_CORE].all fun flags =>
      (List.range 3).all fun shape => [false, true].all fun warm => [false, true].all fun native =>
        headWhnfLoopResult 2 typeLevel flags shape warm native true)
  ++ test "application head WHNF: an inner hit in the other partition preserves the cold method bound"
    ([false, true].all fun typeLevel => [WhnfFlags.FULL, .DEF_EQ_CORE].all fun flags =>
      (List.range 3).all fun shape => [false, true].all fun native =>
        headWhnfLoopResult 2 typeLevel flags shape false native true true)
  ++ test "WHNF cache history: complete maps survive scopes, partial failures, intervening calls, and clearing"
    ([false, true].all fun typeLevel => [false, true].all fun native =>
      [false, true].all fun inferOnly => [false, true].all fun noAccel =>
        whnfExactCacheHistory typeLevel native inferOnly noAccel)
  ++ test "WHNF cache history: forged source metadata demonstrates the finite collision boundary"
    ([false, true].all whnfForeignHistoryKey)
  ++ test "application head sort exposure: nested callbacks retain all binder child types across cache layers"
    ([false, true].all fun typeLevel => [false, true].all fun instrumented => [false, true].all fun noAccel =>
      [0, 1, 2].all fun lowerWarm => sortExposureInferencePaths typeLevel false instrumented noAccel lowerWarm false true)
  ++ test "application head sort exposure: outer hits replay without recursive methods or fuel"
    ([false, true].all fun typeLevel => [false, true].all fun instrumented => [false, true].all fun noAccel =>
      sortExposureInferencePaths typeLevel true instrumented noAccel 0 false true)
  ++ test "application head sort exposure: nested heads and lets reach parameterized declaration admission"
    ([0, 1].all fun clearEvery => [false, true].all fun withZeta =>
      allSucceeded (sortExposureEnvironment .zero 0 withZeta true).1 9 { clearEvery } &&
      allSucceeded (sortExposureEnvironment (.succ .zero) 0 withZeta true).1 9 { clearEvery } &&
      allSucceeded (sortExposureEnvironment (.var 0) 1 withZeta true).1 9 { clearEvery })
  ++ test "application head sort exposure: a returned Pi is rejected and failed scopes restore locals"
    (sortExposureFailures false true)

private def letCases : TestSeq :=
  test "let inference: dependent type substitution retains exact child caches, replay, and fresh rebuilding"
    letExactCacheHistory
  ++ test "let inference: substitution exposes the generated type's selected cheap-beta redex"
    letGeneratedTypeBeta
  ++ test "let inference: generated beta types reach theorem admission with persistent and cleared caches"
    (allSucceeded letGeneratedBetaEnvironment.1 3 { clearEvery := 0 } &&
      allSucceeded letGeneratedBetaEnvironment.1 3 { clearEvery := 1 })
  ++ test "let inference: nested lets preserve an older captured dependent local through both closures"
    letNestedCapture
  ++ test "let inference: bad values are checked and failed bodies restore scope without publishing the parent"
    letFailureCleanup
  ++ test "recursive let inference: binder domains, binder bodies, function positions, and nested values compose"
    recursiveLetPositions
  ++ test "recursive let admission: composite declared types and bodies survive persistent and cleared caches"
    (allSucceeded recursiveLetEnvironment 2 { clearEvery := 0 } &&
      allSucceeded recursiveLetEnvironment 2 { clearEvery := 1 })
  ++ test "recursive let inference: an invalid inner value unwinds both scopes without parent publication"
    recursiveLetFailureCleanup

private def compositeCacheCases : TestSeq :=
  test "composite cache: applications survive lazy inference, scopes, replay, and clearing"
    (compositeCacheHistory 0)
  ++ test "composite cache: Pi checks survive lazy inference, scopes, replay, and clearing"
    (compositeCacheHistory 1)
  ++ test "composite cache: lambda checks survive lazy inference, scopes, replay, and clearing"
    (compositeCacheHistory 2)
  ++ test "composite cache: inference-only applications cannot supply full-mode hits"
    (compositeOnlyCache 0)
  ++ test "composite cache: inference-only Pi checks cannot supply full-mode hits"
    (compositeOnlyCache 1)
  ++ test "composite cache: inference-only lambdas cannot supply full-mode hits"
    (compositeOnlyCache 2)
  ++ test "composite cache: beta application and cold/warm Pi exposure preserve full results"
    (compositeAcrossBetaInference false false && compositeAcrossBetaInference false true)
  ++ test "composite cache: changed cheap-beta lambda inference preserves full results"
    (compositeAcrossBetaInference true false && compositeAcrossBetaInference true true)
  ++ test "composite cache: a reused lambda remains usable in later checked beta reduction"
    compositeCachedLambdaBeta
  ++ test "composite cache: fresh local IDs separate captured lambda keys and result types"
    compositeLocalCacheKeys
  ++ test "composite cache: captured dependent lambdas survive model growth, nested locals, beta, and clearing"
    (compositeCapturedTransport false && compositeCapturedTransport true)
  ++ test "composite cache: transported Pi codomain and supplied-lambda checks justify later cheap beta"
    ([0, 1, 2].all fun shape => compositeCodomainTransport shape .zero &&
      compositeCodomainTransport shape (.succ .zero))
  ++ test "cache history: both complete maps retain every child and parent publication across scopes, loading, and clearing"
    (compositeExactCacheHistory false && compositeExactCacheHistory true)
  ++ test "cache history: occupied full keys hit before recursive writes even for different syntax"
    compositeOccupiedForeignKey

/-- Definitions declare their own parameters. A two-parameter alias uses
`max u v` to instantiate a one-parameter definition; a wrapper applies that
alias beneath binders. Subsequent declarations specialize them at Prop and
Type, and an unused parameter still contributes to the declaration's arity. -/
private def polymorphicDefinitionEnvironment : Ixon.Env × Array (Address × UInt64) := Id.run do
  let type (index : UInt64) := Ixon.Expr.leanAll (.sort index)
    (.leanAll (.var 0) (.var 1))
  let value (index : UInt64) := Ixon.Expr.leanLam (.sort index)
    (.leanLam (.var 0) (.var 0))
  let (env, identity) := storeConst {}
    ⟨.defn ⟨.defn, .safe, 1, type 0, value 0⟩, #[], #[], #[.var 0]⟩
  let (env, opaqueIdentity) := storeConst env
    ⟨.defn ⟨.opaq, .safe, 1, type 0, value 0⟩, #[], #[], #[.var 0]⟩
  let universes := #[Ixon.Univ.var 0, .var 1, .max (.var 0) (.var 1)]
  let (env, alias) := storeConst env
    ⟨.defn ⟨.defn, .safe, 2, type 2, .ref 0 #[2]⟩, #[], #[identity], universes⟩
  let (env, wrapper) := storeConst env
    ⟨.defn ⟨.defn, .safe, 2, type 2,
      .leanLam (.sort 2) (.leanLam (.var 0)
        (.app (.app (.ref 0 #[0, 1]) (.var 1)) (.var 0)))⟩,
      #[], #[alias], universes⟩
  let (env, propInstance) := storeConst env
    ⟨.defn ⟨.thm, .safe, 0, type 0, .ref 0 #[0]⟩, #[], #[identity], #[.zero]⟩
  let (env, typeInstance) := storeConst env
    ⟨.defn ⟨.opaq, .safe, 0, type 1, .ref 0 #[0, 1]⟩,
      #[], #[alias], #[.zero, .succ .zero]⟩
  let (env, unused) := storeConst env
    ⟨.defn ⟨.thm, .safe, 2, type 0, .ref 0 #[]⟩, #[], #[propInstance], #[.zero]⟩
  let (env, sortFamily) := storeConst env
    ⟨.defn ⟨.defn, .safe, 2, .sort 1, .sort 0⟩, #[], #[],
      #[.imax (.var 0) (.var 1), .succ (.imax (.var 0) (.var 1))]⟩
  return (env, #[(identity, 1), (opaqueIdentity, 1), (alias, 2), (wrapper, 2),
    (propInstance, 0), (typeInstance, 0), (unused, 2), (sortFamily, 2)])

private def admittedUniverseInstances : Bool :=
  let (source, catalog) := polymorphicDefinitionEnvironment
  let action : TcM .anon Bool := do
    for (addr, arity) in catalog do
      let declaration ← TcM.getConst ⟨addr, ()⟩
      match declaration with
      | .defn (lvls := count) .. => if count != arity then return false
      | _ => return false
    let requests := #[(catalog[0]!.1, #[.mkZero], KUniv.mkZero (m := .anon)),
      (catalog[0]!.1, #[levelOne], levelOne),
      (catalog[2]!.1, #[.mkZero, levelTwo], levelTwo),
      (catalog[2]!.1, #[levelTwo, .mkZero], levelTwo),
      (catalog[3]!.1, #[.mkZero, .mkZero], .mkZero),
      (catalog[3]!.1, #[levelOne, levelTwo], levelTwo),
      (catalog[6]!.1, #[levelOne, levelTwo], .mkZero)]
    for (addr, arguments, level) in requests do
      let expected := KExpr.mkAll () () (.mkSort level)
        (.mkAll () () (.mkVar 0 ()) (.mkVar 1 ()))
      let result ← TcM.infer (.mkConst ⟨addr, ()⟩ arguments)
      if !sameSourceExpr result expected then return false
    return true
  allSucceeded source catalog.size &&
    match action (TcState.newLazyAnon source) with
    | .ok result _ => result
    | .error _ _ => false

private def badPolymorphicDefinition (arity : UInt64) (bodyLevel : Ixon.Univ)
    (kind : Ix.DefKind := .defn) : Ixon.Env × Address :=
  storeConst {}
    ⟨.defn ⟨kind, .safe, arity,
      .leanAll (.sort 0) (.leanAll (.var 0) (.var 1)),
      .leanLam (.sort 1) (.leanLam (.var 0) (.var 0))⟩,
      #[], #[], #[.var 0, bodyLevel]⟩

private def polymorphicDefinitionCases : TestSeq :=
  test "polymorphic admission: definitions, opaque values, reparameterized aliases, and wrappers check"
    (allSucceeded polymorphicDefinitionEnvironment.1 8 { clearEvery := 0 })
  ++ test "polymorphic admission: declaration parameters survive clearing at every item"
    (allSucceeded polymorphicDefinitionEnvironment.1 8 { clearEvery := 1 })
  ++ test "polymorphic admission: declared arities and distinct universe instances are retained"
    admittedUniverseInstances
  ++ test "polymorphic admission: an undeclared type parameter is rejected"
    (let (source, target) := badPolymorphicDefinition 0 (.var 0); rowFailed source target)
  ++ test "polymorphic admission: an out-of-range parameter in the value is rejected"
    (let (source, target) := badPolymorphicDefinition 1 (.var 1); rowFailed source target)
  ++ test "polymorphic admission: a different in-range parameter cannot justify the declared type"
    (let (source, target) := badPolymorphicDefinition 2 (.var 1); rowFailed source target)
  ++ test "polymorphic admission: a theorem cannot have an arbitrary sort-valued codomain"
    (let (source, target) := badPolymorphicDefinition 1 (.var 0) .thm; rowFailed source target)
  ++ test "polymorphic admission: an unused declared parameter still requires an argument"
    (let (source, catalog) := polymorphicDefinitionEnvironment
      match TcM.infer (.mkConst ⟨catalog[6]!.1, ()⟩ #[.mkZero]) (TcState.newLazyAnon source) with
      | .error (.univParamMismatch expected actual) _ => expected == 2 && actual == 1
      | _ => false : Bool)

public def suite : List TestSeq :=
  [cases, polymorphicCases, specializationCases, binderCases, applicationCases, multiBetaCases, cheapLambdaCases,
    cheapApplicationCases, exposedLambdaCases, repeatedBetaCases, betaTraceCases, hereditaryBetaCases, piExposureCases,
    polymorphicApplicationCases, constantCacheCases, cacheInvariantCases, recursiveCacheCases,
    lazyCacheCases, blockCacheCases, ingressCoherenceCases, sourceOwnershipCases, recursiveStateCases,
    sourceAgreementCases, sourceCacheCases, compositeCacheCases, letCases, sortExposureCases, mixedWhnfCases, letWhnfCases,
    headWhnfCases,
    polymorphicDefinitionCases]

end Tests.Kernel.Consistency
