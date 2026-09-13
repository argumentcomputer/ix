module

public import LSpec
public import Ix.Kernel
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

public def suite : List TestSeq :=
  [cases, polymorphicCases, specializationCases, binderCases, applicationCases,
    polymorphicApplicationCases, constantCacheCases, cacheInvariantCases, recursiveCacheCases,
    lazyCacheCases, blockCacheCases, ingressCoherenceCases]

end Tests.Kernel.Consistency
