import Compilatrix.IxIR2.WireBorrow
import Compilatrix.IxIR2.WireJson
import Compilatrix.CallReuse.Observations
import Compilatrix.Borrow.Sources

/-! Complete syntax vectors and actual source-compiled snapshot witnesses.
The syntax vector deliberately contains invalid ownership/control flow; its
role is codec coverage. The source witnesses cross addressed, checked ingress
and execute the actual decoded program with the decoded finite context. -/

namespace Compilatrix.IxIR2.Wire.Examples

open Lean Compilatrix.Ixon Compilatrix.IxIR

def need (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def fixturePolicy : Policy :=
  { semantics := semanticsVersion, validator := validatorVersion
    lowering := "wire-fixture/1", passes := #[], layout := "fixture-layout/1"
    credits := .callLocalV0 }

def scalarFunction (literal : IxIR0.Literal) : Function :=
  { signature := { params := #[], result := .shared, papSafe := false }
    blocks := #[{ valueParams := #[], creditParams := #[], instructions := #[]
                  terminator := .ret (.lit literal) }] }

def scalarArtifact (literal : IxIR0.Literal := .nat 42) : Artifact :=
  { policy := fixturePolicy, dependencies := #[], layouts := #[], schemas := #[]
    scalarLeaves := #[], program := { declarations := [], main := scalarFunction literal } }

def layoutA : Layout :=
  let preimage := "fixture-layout/a/1".toUTF8
  ⟨Address.blake3 preimage, preimage⟩

def layoutB : Layout :=
  let preimage := "fixture-layout/b/1".toUTF8
  ⟨Address.blake3 preimage, preimage⟩

def cidA : CtorId := ⟨Address.replicate 0xa0, 0, 1⟩
def cidB : CtorId := ⟨Address.replicate 0xb0, 2, 3⟩
def symbolA : Address := Address.replicate 0xa1
def symbolB : Address := Address.replicate 0xb1
def externSymbol : Address := Address.replicate 0xee

def coherent : Artifact :=
  { scalarArtifact with
    dependencies := #[⟨"source", Address.replicate 0x11⟩, ⟨"analysis", Address.replicate 0x22⟩]
    layouts := #[layoutA, layoutB]
    schemas := #[⟨.unique, cidA, ⟨layoutA.identity, #[]⟩⟩,
      ⟨.shared, cidB, ⟨layoutB.identity, #[.shared, .unique]⟩⟩] }

def edgeA : Edge := ⟨1, #[.reg 0, .lit (.nat (2 ^ 64)), .erased], #[0, 1]⟩
def edgeB : Edge := ⟨2, #[], #[]⟩

def allInstructions : Array Instr := #[
  .move (.reg 1),
  .alloc .unique cidA #[.reg 0, .lit (.nat 0), .erased],
  .allocWith 2 .shared cidB #[.lit (.str "λ🙂\n"), .reg 3],
  .discardCredit 4, .takeUnique (.reg 5) cidA, .resetShared (.reg 6) cidB,
  .retainShared (.reg 7), .releaseShared (.reg 8), .dropUnique (.reg 9),
  .freeUnique (.reg 10) cidA, .fetch (.reg 11) cidB 1,
  .call symbolA #[.reg 12, .erased], .callSelf #[.reg 13],
  .papp symbolB #[.lit (.nat 128)], .apply (.reg 14) #[.reg 15],
  .extern externSymbol #[.lit (.nat (2 ^ 448 - 1))]]

def allTerminators : Array Terminator := #[
  .jump edgeA,
  .switchValue (.reg 0) #[⟨cidA, edgeA⟩, ⟨cidB, edgeB⟩] (some ⟨edgeB, edgeA⟩),
  .branchCredit 1 edgeA edgeB, .ret (.lit (.str "é")),
  .tailCall symbolA #[.reg 0], .tailCallSelf #[.reg 1],
  .switchValue .erased #[] none]

def cyclicFunction (other : Address) : Function :=
  { scalarFunction (.nat 7) with
    blocks := #[{ valueParams := #[], creditParams := #[], instructions := #[.call other #[]]
                  terminator := .ret (.reg 0) }] }

def allSyntax : Artifact :=
  { coherent with
    policy := { fixturePolicy with passes := #["pass-a/1", "pass-b/1"], allowExtern := true }
    scalarLeaves := #[⟨.main, 0, 2, cidA⟩, ⟨.declaration symbolA, 2 ^ 64, 1, cidB⟩]
    program :=
      { declarations := [(symbolA, .fn (cyclicFunction symbolB)),
          (symbolB, .fn (cyclicFunction symbolA)), (externSymbol, .extern 2)]
        main :=
          { signature := { params := #[⟨.unique, .owned⟩, ⟨.shared, .borrowed⟩]
                           result := .shared, papSafe := true }
            blocks := allTerminators.mapIdx fun index terminator =>
              { valueParams := #[.scalar, .owned .unique, .owned .shared,
                  .borrowed .unique .caller, .borrowed .shared (.value 1)]
                creditParams := #[.required layoutA.identity, .optional layoutB.identity]
                instructions := if index == 0 then allInstructions else #[]
                terminator } } } }

def resultJson (result : Eval.Result) : Json := Json.mkObj [
  ("store", toJson result.store), ("value", toJson result.value),
  ("control_remaining", toJson result.controlRemaining),
  ("heap_remaining", toJson result.heapRemaining)]

def execute (artifact : Artifact) : Except String Eval.Result :=
  (Eval.Policy.runMain artifact.policy.credits
    (Eval.Context.ofProgram artifact.program artifact.context.schemas)
    .physical artifact.program 10000 10000).mapError reprStr

def release (result : Eval.Result) : Except String Eval.Store := do
  let (store, _) ← (Eval.releaseShared 10000 result.store result.value).mapError reprStr
  need (store.live == 0 && store.heap.allocs == store.heap.frees) "snapshot result was not fully reclaimed"
  return store

structure Case where
  name : String
  artifact : Artifact
  bytes : ByteArray
  summary : Json
  snapshot : Json

def makeCase (name : String) (artifact : Artifact) (checked : Bool)
    (origin : Json := Json.null) (observation : Option Json := none) : Except String Case := do
  let encoded ← artifact.encodeChecked {}
  let addressed ← Artifact.decodeAddressed {} encoded.bytes artifact.address
  need (addressed.artifact == artifact) s!"{name}: decoded snapshot changed its in-memory value"
  let validation ← if checked then do
      let ingress ← Artifact.ingest {} Validate.defaultLimits encoded.bytes artifact.address
      need (ingress.artifact == artifact) s!"{name}: checked ingress changed the snapshot"
      pure (Json.mkObj [("status", toJson "checked"), ("stats", toJson ingress.checked.stats)])
    else pure (Json.mkObj [("status", toJson "syntax-only")])
  let execution ← match observation with
    | none => pure Json.null
    | some expected => do
        let original ← execute artifact
        let decoded ← execute addressed.artifact
        need (resultJson original == resultJson decoded) s!"{name}: decoded physical execution changed"
        let released ← release decoded
        need (toJson decoded.store == (← expected.getObjVal? "store") &&
          toJson released == (← expected.getObjVal? "reclaimed"))
          s!"{name}: decoded execution disagrees with the source-certified observation"
        pure (Json.mkObj [("original", resultJson original), ("decoded", resultJson decoded),
          ("reclaimed", toJson released), ("source_value", ← expected.getObjVal? "value")])
  let summary := Json.mkObj [
    ("name", toJson name), ("binary", toJson s!"{name}.ixir2"),
    ("snapshot", toJson s!"{name}.json"), ("bytes", toJson encoded.bytes.size),
    ("root", toJson artifact.address.toHex), ("checked", toJson checked),
    ("source", origin), ("execution", toJson observation.isSome)]
  return {
    name, artifact, bytes := encoded.bytes, summary
    snapshot := Json.mkObj [("format", toJson formatId), ("summary", summary),
      ("artifact", artifactJson artifact), ("validation", validation), ("execution", execution)] }

private def withSource (artifact : Artifact) (root : Address) : Artifact :=
  { artifact with dependencies := artifact.dependencies.push ⟨"ixon-entry", root⟩ }

def mapCases (name : String) (values : List Nat) (replacement : Nat)
    (aliased : Bool) (uniquePrefix : Nat := 0) : Except String (Array Case) := do
  let source ← Compilatrix.CallReuse.Examples.source values replacement aliased uniquePrefix
  let evidence ← Compilatrix.CallReuse.Examples.runCase name values replacement aliased uniquePrefix
  let compilation ← source.compile.mapError reprStr
  let .recovered _ lowered := compilation.outcome | throw "snapshot map source was not lowered"
  let baseline := withSource (ofCompiled lowered.attached) source.root
  let selected := withSource (ofCallReuse lowered.attached lowered.reuse) source.root
  need (baseline.program != selected.program && baseline.address != selected.address)
    "selected physical map body did not change snapshot identity"
  need (baseline.dependencies == selected.dependencies) "pass changed the original dependency roots"
  let observations ← evidence.snapshot.getObjVal? "observations"
  let origin := Json.mkObj [("family", toJson "recursive-map"), ("entry", toJson source.root.toHex),
    ("values", toJson values), ("replacement", toJson replacement), ("aliased", toJson aliased),
    ("unique_prefix", toJson uniquePrefix)]
  let before ← makeCase s!"{name}-baseline" baseline true origin
    (some (← observations.getObjVal? "baseline_physical"))
  let after ← makeCase s!"{name}-reuse" selected true origin
    (some (← observations.getObjVal? "selected_physical"))
  return #[before, after]

private def borrowObservation (result : Eval.Result) (number : Nat) : Except String Json := do
  let reclaimed ← release result
  need (result.value == .lit (.nat number)) "borrow source value changed"
  return Json.mkObj [("store", toJson result.store), ("reclaimed", toJson reclaimed),
    ("value", toJson number)]

def borrowCases (depth : Nat) (successor : Bool) : Except String (Array Case) := do
  let source ← Compilatrix.Borrow.Examples.source depth successor
  let attached ← source.compile.mapError reprStr
  let selection := Compilatrix.Borrow.select attached
  let improved ← selection.attempt.mapError reprStr
  let baseline := withSource (ofCompiled attached.compiled) source.root
  let borrowed := withSource (ofBorrow attached selection) source.root
  need (baseline.program != borrowed.program && baseline.address != borrowed.address)
    "borrowed signatures did not change snapshot identity"
  let origin := Json.mkObj [("family", toJson "borrowed-call"), ("entry", toJson source.root.toHex),
    ("depth", toJson depth), ("successor", toJson successor), ("number", toJson improved.source.number)]
  let before ← execute baseline
  let after ← execute borrowed
  need (toJson before.store == toJson improved.target.before.result.store &&
    toJson after.store == toJson improved.target.after.result.store)
    "snapshot borrow programs differ from source-certified selection"
  let base ← makeCase s!"borrow-{depth}-{if successor then "succ" else "zero"}-baseline"
    baseline true origin (some (← borrowObservation before improved.source.number))
  let selected ← makeCase s!"borrow-{depth}-{if successor then "succ" else "zero"}-selected"
    borrowed true origin (some (← borrowObservation after improved.source.number))
  let fallback := Compilatrix.Borrow.select attached { maxAttempts := 0 }
  let kept := withSource (ofBorrow attached fallback) source.root
  need (!fallback.attempt.isOk && kept == baseline && kept.address == baseline.address)
    "rejected borrow pass changed the complete snapshot or its root"
  return #[base, selected]

def cases : Except String (Array Case) := do
  let mut result := #[← makeCase "all-syntax" allSyntax false, ← makeCase "finite-context" coherent true]
  for (name, values, replacement, aliased, uniquePrefix) in [
      ("map-empty", [], 7, false, 0), ("map-hot", [0, 1, 2 ^ 64], 42, false, 0),
      ("map-mixed", [1, 2, 3], 9, true, 1)] do
    result := result ++ (← mapCases name values replacement aliased uniquePrefix)
  result := result ++ (← borrowCases 0 false) ++ (← borrowCases 2 true)
  return result

end Compilatrix.IxIR2.Wire.Examples
