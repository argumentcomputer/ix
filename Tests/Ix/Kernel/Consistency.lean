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
  [cases, polymorphicCases, specializationCases, binderCases, applicationCases,
    polymorphicApplicationCases, constantCacheCases, cacheInvariantCases, recursiveCacheCases,
    lazyCacheCases, blockCacheCases, ingressCoherenceCases, sourceOwnershipCases, recursiveStateCases,
    sourceAgreementCases, sourceCacheCases, polymorphicDefinitionCases]

end Tests.Kernel.Consistency
