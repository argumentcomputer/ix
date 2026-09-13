module

public import LSpec
public import Ix.Kernel
public import Tests.Ix.Kernel.IxonFixtures

/-!
Production regressions for the atomic consistency fragment and polymorphic
constant inference. These execute the lazy loader, inference, and serial driver
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

public def suite : List TestSeq := [cases, polymorphicCases, specializationCases]

end Tests.Kernel.Consistency
