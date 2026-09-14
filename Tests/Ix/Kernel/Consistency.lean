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

public def suite : List TestSeq :=
  [cases, polymorphicCases, specializationCases, binderCases, applicationCases,
    polymorphicApplicationCases, constantCacheCases, cacheInvariantCases, recursiveCacheCases]

end Tests.Kernel.Consistency
