module

public import Tests.Ix.Kernel.IxonFixtures

/-!
Definition-cycle regressions through the real content-addressed source loader
and public checker. The logical examples either have no axioms or assume only
`P : Prop`. A separate internal-state test checks cycles across block boundaries.
-/

namespace Tests.Kernel.DefinitionDependencies

open LSpec Ix.Kernel Tests.Kernel.Fixtures

private def propSource : Ixon.Env × Address :=
  storeConst {} ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.zero]⟩

/-- A hash-verified declaration of every proposition, with no source axioms.
The relative self-reference is encoded without any assumed hash collision. -/
private def axiomFreeCycleSource (kind : Ix.DefKind) : Ixon.Env × Address :=
  storeConst {}
    ⟨.defn ⟨kind, .safe, 0, .leanAll (.sort 0) (.var 0), .recur 0 #[]⟩,
      #[], #[], #[.zero]⟩

private def cycleSource (kind : Ix.DefKind) (asBlock : Bool)
    (value : Ixon.Expr := .recur 0 #[]) (safety : Ix.DefinitionSafety := .safe)
    (sharing : Array Ixon.Expr := #[]) : Ixon.Env × Address :=
  let (source, proposition) := propSource
  let declaration : Ixon.Definition := ⟨kind, safety, 0, .ref 0 #[], value⟩
  if asBlock then
    let (source, block) := storeMutsWithProjs source
      ⟨.muts #[.defn declaration], sharing, #[proposition], #[]⟩
    (source, defnProjAddr block 0)
  else
    storeConst source ⟨.defn declaration, sharing, #[proposition], #[]⟩

private def cyclicError (source : Ixon.Env) (target : Address)
    (clearEvery : Nat := 0) : Bool :=
  match checkEnvAnon source { clearEvery } with
  | .ok rows => rows.any fun row =>
      row.addr == target && match row.err? with
        | some message => ("cyclic definition dependency").isPrefixOf message
        | _ => false
  | .error _ => false

private def rejectsCycle (fixture : Ixon.Env × Address) : Bool :=
  cyclicError fixture.1 fixture.2 0 && cyclicError fixture.1 fixture.2 1

private def mutualCycle : Ixon.Env × Address :=
  let (source, proposition) := propSource
  storeMutsWithProjs source
    ⟨.muts #[
      .defn ⟨.thm, .safe, 0, .ref 0 #[], .recur 1 #[]⟩,
      .defn ⟨.opaq, .safe, 0, .ref 0 #[], .recur 0 #[]⟩],
      #[], #[proposition], #[]⟩

private def typeCycle : Ixon.Env × Address :=
  let (source, _) := propSource
  storeConst source
    ⟨.defn ⟨.defn, .safe, 0, .recur 0 #[], .sort 0⟩, #[], #[], #[.zero]⟩

private def acyclicSource : Ixon.Env × Address := Id.run do
  let (source, proposition) := propSource
  let (source, witness) := storeConst source
    ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[proposition], #[]⟩
  -- Forward reference, shared dependency, and mixed safe definition kinds.
  -- The let initializer repeats the same shared leaf as its body.
  storeMutsWithProjs source
    ⟨.muts #[
      .defn ⟨.thm, .safe, 0, .ref 0 #[], .recur 2 #[]⟩,
      .defn ⟨.opaq, .safe, 0, .ref 0 #[], .recur 2 #[]⟩,
      .defn ⟨.defn, .safe, 0, .ref 0 #[],
        .letE true (.ref 0 #[]) (.share 0) (.share 0)⟩],
      #[.ref 1 #[]], #[proposition, witness], #[]⟩

private def acyclicPasses (clearEvery : Nat) : Bool :=
  match checkEnvAnon acyclicSource.1 { clearEvery } with
  | .ok rows => rows.size == 5 && rows.all (·.err?.isNone)
  | .error _ => false

private def everyMemberSharesFailure : Bool :=
  let (source, block) := mutualCycle
  let action : TcM .anon Bool := do
    let mut messages : Array String := #[]
    for member in #[0, 1, 0] do
      try
        TcM.checkConst ⟨defnProjAddr block member, ()⟩
        return false
      catch
        | .other message => messages := messages.push message
        | _ => return false
    return messages.size == 3 && messages.all (· == messages[0]!) &&
      ("cyclic definition dependency").isPrefixOf messages[0]!
  match action (TcState.newLazyAnon source) with
  | .ok result _ => result
  | .error _ _ => false

private def nonlogicalPasses (safety : Ix.DefinitionSafety) : Bool :=
  let (source, _) := cycleSource .defn false (.recur 0 #[]) safety
  match checkEnvAnon source with
  | .ok rows => rows.size == 2 && rows.all (·.err?.isNone)
  | .error _ => false

/-- These deliberately constructed internal keys are not content hashes.
The dependency traversal must follow edges across coordinated blocks too. -/
private def rejectsSeparatedBlocks : Bool :=
  let first : KId .anon := ⟨Address.blake3 "separated-cycle-first".toUTF8, ()⟩
  let second : KId .anon := ⟨Address.blake3 "separated-cycle-second".toUTF8, ()⟩
  let type := KExpr.mkAll () () (.mkSort .mkZero) (.mkVar 0 ())
  let declaration (block target : KId .anon) : KConst .anon :=
    .defn () () .defn .safe (.regular 0) 0 type (.mkConst target #[]) () block
  let env := ({} : AnonEnv)
    |>.insert first (declaration first second)
    |>.insert second (declaration second first)
    |>.insertBlock first #[first]
    |>.insertBlock second #[second]
  [first, second].all fun requested =>
    match TcM.checkConst requested (.ofEnvAnon env) with
    | .error (.other message) _ => ("cyclic definition dependency").isPrefixOf message
    | _ => false

/-- Serialized-source regressions shared with the Rust differential suite.
The last two fields are the exact target count and expected failure count. -/
public def parityFixtures : Array (String × Ixon.Env × Nat × Nat) := #[
  ("axiom-free-theorem-cycle", (axiomFreeCycleSource .thm).1, 1, 1),
  ("axiom-free-definition-cycle", (axiomFreeCycleSource .defn).1, 1, 1),
  ("axiom-free-opaque-cycle", (axiomFreeCycleSource .opaq).1, 1, 1),
  ("standalone-cycle", (cycleSource .thm false).1, 2, 1),
  ("one-member-cycle", (cycleSource .thm true).1, 2, 1),
  ("mutual-cycle", mutualCycle.1, 3, 2),
  ("type-cycle", typeCycle.1, 2, 1),
  ("shared-cycle", (cycleSource .opaq true (.share 0) .safe #[.recur 0 #[]]).1, 2, 1),
  ("acyclic-block", acyclicSource.1, 5, 0),
  ("partial-cycle", (cycleSource .defn false (.recur 0 #[]) .part).1, 2, 0),
  ("unsafe-cycle", (cycleSource .defn false (.recur 0 #[]) .unsaf).1, 2, 0)
]

public def suite : List TestSeq := [
  ([Ix.DefKind.defn, .thm, .opaq].foldl (init := .done) fun tests kind =>
    tests ++ test s!"definition dependencies: an axiom-free {repr kind} cannot prove every proposition by self-reference"
      (rejectsCycle (axiomFreeCycleSource kind)))
  ++ test "definition dependencies: a cycle across separate internal blocks is rejected"
    rejectsSeparatedBlocks
  ++ test "definition dependencies: a standalone theorem cannot justify itself"
    (rejectsCycle (cycleSource .thm false))
  ++ test "definition dependencies: a one-member mutual theorem cannot justify itself"
    (rejectsCycle (cycleSource .thm true))
  ++ test "definition dependencies: safe definitions cannot justify themselves"
    (rejectsCycle (cycleSource .defn false))
  ++ test "definition dependencies: opaque values cannot justify themselves"
    (rejectsCycle (cycleSource .opaq false))
  ++ test "definition dependencies: a two-member cycle is rejected"
    (let (source, block) := mutualCycle; rejectsCycle (source, defnProjAddr block 0))
  ++ test "definition dependencies: circular declaration types are rejected"
    (rejectsCycle typeCycle)
  ++ test "definition dependencies: let initializers cannot hide a cycle"
    (rejectsCycle (cycleSource .thm false
      (.letE true (.ref 0 #[]) (.recur 0 #[]) (.recur 0 #[]))))
  ++ test "definition dependencies: shared syntax cannot hide a cycle"
    (rejectsCycle (cycleSource .thm true (.share 0) .safe #[.recur 0 #[]]))
  ++ test "definition dependencies: binder bodies cannot hide a cycle"
    (rejectsCycle (cycleSource .defn false
      (.leanLam (.ref 0 #[]) (.recur 0 #[]))))
  ++ test "definition dependencies: every member replays the same cycle failure"
    everyMemberSharesFailure
  ++ test "definition dependencies: acyclic forward references and shared leaves check"
    (acyclicPasses 0)
  ++ test "definition dependencies: acyclic blocks check with clearing at every item"
    (acyclicPasses 1)
  ++ test "definition dependencies: partial definitions retain their safety policy"
    (nonlogicalPasses .part)
  ++ test "definition dependencies: unsafe definitions retain their safety policy"
    (nonlogicalPasses .unsaf)
]

end Tests.Kernel.DefinitionDependencies
