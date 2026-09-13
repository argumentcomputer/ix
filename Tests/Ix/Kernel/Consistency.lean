module

public import LSpec
public import Ix.Kernel
public import Tests.Ix.Kernel.IxonFixtures

/-!
Production regressions for the atomic consistency fragment. These execute
the lazy serial driver on content-addressed Ixon declarations. The fragment's
theorems and resource premises are checked by `IxKernelConsistency`.
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

public def suite : List TestSeq := [cases]

end Tests.Kernel.Consistency
