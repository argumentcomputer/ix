import Ix.Compiler.IxIR1.Lower

/-!
# Seeded well-moded IxIR₀ program generation

A deterministic property corpus for the IxIR₀ → IxIR₁ differential boundary.
Positive templates generate closed programs inside the lowerer's current
ownership fragment and must pass source/target tree agreement plus target
leak-freedom.  Adversarial templates sit exactly one mode boundary outside
that fragment and must fail lowering with a pinned diagnostic.

Generation has no ambient randomness.  Every case records the corpus seed,
case index, and PRNG state at the start of the case; `replay` reconstructs it
directly.  Template-preserving shrink candidates retain the same expected
outcome, so a mismatch can be minimized without turning into an unrelated
open or ill-shaped expression.
-/

namespace Ix.Compiler.IxIR1.WellModedGen

open Ix.Compiler.Ixon (Owned)
open Ix.Compiler.IxIR0
open Ix.Compiler.IxIR0.Examples
open Ix.Compiler.IxIR1.Lower

def defaultSeed : UInt64 := 0x243f6a8885a308d3
def defaultCases : Nat := 280

/-! ## Replayable deterministic entropy -/

abbrev GenM := StateM UInt64

def next : GenM UInt64 := do
  let state ← get
  let state' := state * 6364136223846793005 + 1442695040888963407
  set state'
  return state'

def choose (bound : Nat) : GenM Nat := do
  if bound == 0 then return 0
  return (← next).toNat % bound

def chooseBool : GenM Bool := do
  return (← choose 2) == 1

def chooseNat : GenM Nat := choose 7

def chooseNatList : GenM (List Nat) := do
  let length ← choose 5
  let mut values := []
  for _ in [:length] do
    values := (← chooseNat) :: values
  return values.reverse

/-! ## Closed program schemas -/

inductive NatForm where
  | ctor
  | literal
  deriving BEq, DecidableEq, Repr, Inhabited

def NatForm.expr : NatForm → Nat → Expr
  | .ctor, n => natE n
  | .literal, n => .lit (.nat n)

def chooseNatForm : GenM NatForm := do
  if ← chooseBool then return .ctor else return .literal

inductive Kind where
  | natAdd
  | externAdd
  | sharedDuplicate
  | sharedProjection
  | sharedDead
  | listLength
  | listAppend
  | capturedLambda
  | dynamicPap
  | partialAdd
  | uniquePair
  | linearPair
  | linearIdentity
  | affineDead
  | mixedDropFst
  | mixedDropSnd
  | erasedApp
  | erasedProjection
  | freezeNeeded
  | dereliction
  | duplicateUnique
  | deadLinear
  | uniqueProjection
  | nonManyLambda
  | partialNonMany
  | sharedCallAtUnique
  | uniqueCapture
  | uniqueRecursor
  deriving BEq, DecidableEq, Repr, Inhabited

def allKinds : Array Kind := #[
  .natAdd,
  .externAdd,
  .sharedDuplicate,
  .sharedProjection,
  .sharedDead,
  .listLength,
  .listAppend,
  .capturedLambda,
  .dynamicPap,
  .partialAdd,
  .uniquePair,
  .linearPair,
  .linearIdentity,
  .affineDead,
  .mixedDropFst,
  .mixedDropSnd,
  .erasedApp,
  .erasedProjection,
  .freezeNeeded,
  .dereliction,
  .duplicateUnique,
  .deadLinear,
  .uniqueProjection,
  .nonManyLambda,
  .partialNonMany,
  .sharedCallAtUnique,
  .uniqueCapture,
  .uniqueRecursor]

inductive Template where
  | natAdd (leftForm rightForm : NatForm) (left right : Nat)
  | externAdd (left right : Nat)
  | sharedDuplicate (value : Nat)
  | sharedProjection (field left right : Nat)
  | sharedDead (dead kept : Nat)
  | listLength (values : List Nat)
  | listAppend (left right : List Nat)
  | capturedLambda (captured argument : Nat)
  | dynamicPap (leftForm rightForm : NatForm) (left right : Nat)
  | partialAdd (form : NatForm) (value : Nat)
  | uniquePair (left right : Nat)
  | linearPair (left right : Nat)
  | linearIdentity (value : Nat)
  | affineDead (dead kept : Nat)
  | mixedDropFst (dead kept : Nat)
  | mixedDropSnd (kept dead : Nat)
  | erasedApp (argument : Nat)
  | erasedProjection (field : Nat)
  | freezeNeeded (value : Nat)
  | dereliction (value : Nat)
  | duplicateUnique (value : Nat)
  | deadLinear (dead kept : Nat)
  | uniqueProjection (field left right : Nat)
  | nonManyLambda (argument result : Nat)
  | partialNonMany (argument : Nat)
  | sharedCallAtUnique (left right kept : Nat)
  | uniqueCapture (value : Nat)
  | uniqueRecursor (major : Nat)
  deriving BEq, DecidableEq, Repr, Inhabited

def Template.kind : Template → Kind
  | .natAdd .. => .natAdd
  | .externAdd .. => .externAdd
  | .sharedDuplicate .. => .sharedDuplicate
  | .sharedProjection .. => .sharedProjection
  | .sharedDead .. => .sharedDead
  | .listLength .. => .listLength
  | .listAppend .. => .listAppend
  | .capturedLambda .. => .capturedLambda
  | .dynamicPap .. => .dynamicPap
  | .partialAdd .. => .partialAdd
  | .uniquePair .. => .uniquePair
  | .linearPair .. => .linearPair
  | .linearIdentity .. => .linearIdentity
  | .affineDead .. => .affineDead
  | .mixedDropFst .. => .mixedDropFst
  | .mixedDropSnd .. => .mixedDropSnd
  | .erasedApp .. => .erasedApp
  | .erasedProjection .. => .erasedProjection
  | .freezeNeeded .. => .freezeNeeded
  | .dereliction .. => .dereliction
  | .duplicateUnique .. => .duplicateUnique
  | .deadLinear .. => .deadLinear
  | .uniqueProjection .. => .uniqueProjection
  | .nonManyLambda .. => .nonManyLambda
  | .partialNonMany .. => .partialNonMany
  | .sharedCallAtUnique .. => .sharedCallAtUnique
  | .uniqueCapture .. => .uniqueCapture
  | .uniqueRecursor .. => .uniqueRecursor

private def app2 (fn left right : Expr) : Expr :=
  .app (.app fn left) right

def Template.expr : Template → Expr
  | .natAdd leftForm rightForm left right =>
    app2 (.ref natAddDef) (leftForm.expr left) (rightForm.expr right)
  | .externAdd left right =>
    app2 (.ref natAddExt) (.lit (.nat left)) (.lit (.nat right))
  | .sharedDuplicate value =>
    .letE .many (natE value)
      (app2 (.ref pairMk) (.var 0) (.var 0))
  | .sharedProjection field left right =>
    .proj (field % 2) (app2 (.ref pairMk) (natE left) (natE right))
  | .sharedDead dead kept =>
    .letE .many (natE dead) (natE kept)
  | .listLength values =>
    .app (.ref lengthDef) (listE natE values)
  | .listAppend left right =>
    app2 (.ref appendDef) (listE natE left) (listE natE right)
  | .capturedLambda captured argument =>
    .app
      (.lam .many
        (.app
          (.lam .many (app2 (.ref natAddDef) (.var 1) (.var 0)))
          (natE argument)))
      (natE captured)
  | .dynamicPap leftForm rightForm left right =>
    .letE .many (.app (.ref natAddDef) (leftForm.expr left))
      (.app (.var 0) (rightForm.expr right))
  | .partialAdd form value =>
    .app (.ref natAddDef) (form.expr value)
  | .uniquePair left right =>
    app2 (.ref pairMk) (natE left) (natE right)
  | .linearPair left right =>
    .letE .linear (natE left)
      (.letE .linear (natE right)
        (app2 (.ref pairMk) (.var 1) (.var 0)))
  | .linearIdentity value =>
    .letE .linear (natE value) (.var 0)
  | .affineDead dead kept =>
    .letE .affine (natE dead) (natE kept)
  | .mixedDropFst dead kept =>
    app2 (.ref dropFstDef) (natE dead) (natE kept)
  | .mixedDropSnd kept dead =>
    app2 (.ref dropSndDef) (natE kept) (natE dead)
  | .erasedApp argument =>
    .app .erased (natE argument)
  | .erasedProjection field =>
    .proj field .erased
  | .freezeNeeded value =>
    .letE .linear (natE value) (.app (.ref natSucc) (.var 0))
  | .dereliction value =>
    .letE .many (natE value) (.app (.ref natSucc) (.var 0))
  | .duplicateUnique value =>
    .letE .linear (natE value)
      (app2 (.ref pairMk) (.var 0) (.var 0))
  | .deadLinear dead kept =>
    .letE .linear (natE dead) (natE kept)
  | .uniqueProjection field left right =>
    .letE .linear (app2 (.ref pairMk) (natE left) (natE right))
      (.proj (field % 2) (.var 0))
  | .nonManyLambda argument result =>
    .app (.lam .affine (.lit (.nat result))) (natE argument)
  | .partialNonMany argument =>
    .app (.ref dropFstDef) (natE argument)
  | .sharedCallAtUnique left right kept =>
    .letE .affine
      (app2 (.ref natAddDef) (natE left) (natE right))
      (natE kept)
  | .uniqueCapture value =>
    .letE .linear (natE value) (.lam .many (.var 1))
  | .uniqueRecursor major =>
    .letE .linear (natE major)
      (.app
        (.app
          (.app (.ref natRec) (natE 0))
          (.lam .many (.lam .many (.app (.ref natSucc) (.var 0)))))
        (.var 0))

inductive Expectation where
  | differential (world : Owned)
  | lowerError (world : Owned) (message : String)
  deriving BEq, DecidableEq, Repr, Inhabited

def Template.expectation : Template → Expectation
  | .uniquePair .. | .linearPair .. | .linearIdentity .. | .affineDead .. =>
    .differential .unique
  | .freezeNeeded .. =>
    .lowerError .shared RestrictionKind.freeze.diagnostic
  | .dereliction .. =>
    .lowerError .unique "dereliction: shared value at unique demand"
  | .duplicateUnique .. =>
    .lowerError .unique "unique variable used more than once"
  | .deadLinear .. => .lowerError .shared "unused linear binding"
  | .uniqueProjection .. =>
    .lowerError .shared RestrictionKind.uniqueDestructuring.diagnostic
  | .nonManyLambda .. | .partialNonMany .. =>
    .lowerError .shared RestrictionKind.sharedFunctionValues.diagnostic
  | .sharedCallAtUnique .. =>
    .lowerError .shared "call result is shared at unique demand"
  | .uniqueCapture .. =>
    .lowerError .shared RestrictionKind.uniqueCapture.diagnostic
  | .uniqueRecursor .. =>
    .lowerError .shared RestrictionKind.modeMonomorphicRecursors.diagnostic
  | _ => .differential .shared

def genTemplate : Kind → GenM Template
  | .natAdd => do
    return .natAdd (← chooseNatForm) (← chooseNatForm)
      (← chooseNat) (← chooseNat)
  | .externAdd => return .externAdd (← chooseNat) (← chooseNat)
  | .sharedDuplicate => return .sharedDuplicate (← chooseNat)
  | .sharedProjection =>
    return .sharedProjection (← choose 2) (← chooseNat) (← chooseNat)
  | .sharedDead => return .sharedDead (← chooseNat) (← chooseNat)
  | .listLength => return .listLength (← chooseNatList)
  | .listAppend => return .listAppend (← chooseNatList) (← chooseNatList)
  | .capturedLambda => return .capturedLambda (← chooseNat) (← chooseNat)
  | .dynamicPap => do
    return .dynamicPap (← chooseNatForm) (← chooseNatForm)
      (← chooseNat) (← chooseNat)
  | .partialAdd => return .partialAdd (← chooseNatForm) (← chooseNat)
  | .uniquePair => return .uniquePair (← chooseNat) (← chooseNat)
  | .linearPair => return .linearPair (← chooseNat) (← chooseNat)
  | .linearIdentity => return .linearIdentity (← chooseNat)
  | .affineDead => return .affineDead (← chooseNat) (← chooseNat)
  | .mixedDropFst => return .mixedDropFst (← chooseNat) (← chooseNat)
  | .mixedDropSnd => return .mixedDropSnd (← chooseNat) (← chooseNat)
  | .erasedApp => return .erasedApp (← chooseNat)
  | .erasedProjection => return .erasedProjection (← choose 4)
  | .freezeNeeded => return .freezeNeeded (← chooseNat)
  | .dereliction => return .dereliction (← chooseNat)
  | .duplicateUnique => return .duplicateUnique (← chooseNat)
  | .deadLinear => return .deadLinear (← chooseNat) (← chooseNat)
  | .uniqueProjection =>
    return .uniqueProjection (← choose 2) (← chooseNat) (← chooseNat)
  | .nonManyLambda => return .nonManyLambda (← chooseNat) (← chooseNat)
  | .partialNonMany => return .partialNonMany (← chooseNat)
  | .sharedCallAtUnique =>
    return .sharedCallAtUnique (← chooseNat) (← chooseNat) (← chooseNat)
  | .uniqueCapture => return .uniqueCapture (← chooseNat)
  | .uniqueRecursor => return .uniqueRecursor (← chooseNat)

/-! ## Template-preserving shrinking -/

private def shrinkNat (value : Nat) : List Nat :=
  if value == 0 then []
  else [0, value / 2].eraseDups

private def shrinkNatList (values : List Nat) : List (List Nat) :=
  if values.isEmpty then []
  else
    let zeros := values.map fun _ => 0
    ([[], values.take (values.length / 2)] ++
      if zeros == values then [] else [zeros]).eraseDups

private def shrinkPair (make : Nat → Nat → Template) (left right : Nat) :
    List Template :=
  (shrinkNat left).map (make · right) ++
    (shrinkNat right).map (make left)

private def shrinkTriple (make : Nat → Nat → Nat → Template)
    (first second third : Nat) : List Template :=
  (shrinkNat first).map (make · second third) ++
    (shrinkNat second).map (make first · third) ++
    (shrinkNat third).map (make first second)

def Template.shrinks : Template → List Template
  | .natAdd leftForm rightForm left right =>
    (if leftForm == .ctor then [.natAdd .literal rightForm left right] else []) ++
    (if rightForm == .ctor then [.natAdd leftForm .literal left right] else []) ++
    shrinkPair (.natAdd leftForm rightForm) left right
  | .externAdd left right => shrinkPair .externAdd left right
  | .sharedDuplicate value => (shrinkNat value).map .sharedDuplicate
  | .sharedProjection field left right =>
    shrinkPair (.sharedProjection field) left right
  | .sharedDead dead kept => shrinkPair .sharedDead dead kept
  | .listLength values => (shrinkNatList values).map .listLength
  | .listAppend left right =>
    (shrinkNatList left).map (.listAppend · right) ++
      (shrinkNatList right).map (.listAppend left)
  | .capturedLambda captured argument =>
    shrinkPair .capturedLambda captured argument
  | .dynamicPap leftForm rightForm left right =>
    (if leftForm == .ctor then [.dynamicPap .literal rightForm left right]
      else []) ++
    (if rightForm == .ctor then [.dynamicPap leftForm .literal left right]
      else []) ++
    shrinkPair (.dynamicPap leftForm rightForm) left right
  | .partialAdd form value =>
    (if form == .ctor then [.partialAdd .literal value] else []) ++
      (shrinkNat value).map (.partialAdd form)
  | .uniquePair left right => shrinkPair .uniquePair left right
  | .linearPair left right => shrinkPair .linearPair left right
  | .linearIdentity value => (shrinkNat value).map .linearIdentity
  | .affineDead dead kept => shrinkPair .affineDead dead kept
  | .mixedDropFst dead kept => shrinkPair .mixedDropFst dead kept
  | .mixedDropSnd kept dead => shrinkPair .mixedDropSnd kept dead
  | .erasedApp argument => (shrinkNat argument).map .erasedApp
  | .erasedProjection field => (shrinkNat field).map .erasedProjection
  | .freezeNeeded value => (shrinkNat value).map .freezeNeeded
  | .dereliction value => (shrinkNat value).map .dereliction
  | .duplicateUnique value => (shrinkNat value).map .duplicateUnique
  | .deadLinear dead kept => shrinkPair .deadLinear dead kept
  | .uniqueProjection field left right =>
    shrinkTriple .uniqueProjection field left right
  | .nonManyLambda argument result =>
    shrinkPair .nonManyLambda argument result
  | .partialNonMany argument => (shrinkNat argument).map .partialNonMany
  | .sharedCallAtUnique left right kept =>
    shrinkTriple .sharedCallAtUnique left right kept
  | .uniqueCapture value => (shrinkNat value).map .uniqueCapture
  | .uniqueRecursor major => (shrinkNat major).map .uniqueRecursor

/-! ## Cases, replay, checking, and failure minimization -/

structure Replay where
  seed : UInt64
  index : Nat
  state : UInt64
  deriving BEq, DecidableEq, Repr, Inhabited

structure Case where
  replayToken : Replay
  kind : Kind
  template : Template
  deriving BEq, DecidableEq, Repr, Inhabited

def generateAt (seed : UInt64) (index : Nat) (state : UInt64) :
    Case × UInt64 :=
  let kind := allKinds[index % allKinds.size]!
  let (template, nextState) := (genTemplate kind).run state
  (⟨⟨seed, index, state⟩, kind, template⟩, nextState)

def replay (token : Replay) : Case :=
  (generateAt token.seed token.index token.state).1

def Case.holds (test : Case) : Bool :=
  match test.template.expectation with
  | .differential world => diffExpr test.template.expr world
  | .lowerError world message => lowersErr test.template.expr world message

def Case.withTemplate (test : Case) (template : Template) : Case :=
  { test with kind := template.kind, template }

inductive FailureKind where
  | replayDrift
  | shrinkExpectationDrift
  | propertyMismatch
  deriving BEq, DecidableEq, Repr, Inhabited

structure Failure where
  kind : FailureKind
  original : Case
  minimized : Case
  deriving BEq, DecidableEq, Repr, Inhabited

def minimizeFailure : Nat → Case → Case
  | 0, test => test
  | fuel + 1, test =>
    match test.template.shrinks.find? fun template =>
        !(test.withTemplate template).holds with
    | none => test
    | some template => minimizeFailure fuel (test.withTemplate template)

def checkCorpus (seed : UInt64 := defaultSeed)
    (count : Nat := defaultCases) : Option Failure := Id.run do
  let mut state := seed
  for index in [:count] do
    let (test, nextState) := generateAt seed index state
    if replay test.replayToken != test then
      return some ⟨.replayDrift, test, test⟩
    if !test.template.shrinks.all fun template =>
        template.expectation == test.template.expectation then
      return some ⟨.shrinkExpectationDrift, test, test⟩
    if !test.holds then
      return some ⟨.propertyMismatch, test, minimizeFailure 128 test⟩
    state := nextState
  return none

/-! ## A stable corpus fingerprint -/

private def mix (hash value : UInt64) : UInt64 :=
  hash * 1099511628211 + value + 1469598103934665603

private def mixNat (hash : UInt64) (value : Nat) : UInt64 :=
  mix hash value.toUInt64

private def mixForm (hash : UInt64) : NatForm → UInt64
  | .ctor => mix hash 0
  | .literal => mix hash 1

private def mixList (hash : UInt64) (values : List Nat) : UInt64 :=
  values.foldl mixNat (mixNat hash values.length)

def Template.fingerprint : Template → UInt64
  | .natAdd lf rf left right =>
    mixNat (mixNat (mixForm (mixForm (mix 0 0) lf) rf) left) right
  | .externAdd left right => mixNat (mixNat (mix 0 1) left) right
  | .sharedDuplicate value => mixNat (mix 0 2) value
  | .sharedProjection field left right =>
    mixNat (mixNat (mixNat (mix 0 3) field) left) right
  | .sharedDead dead kept => mixNat (mixNat (mix 0 4) dead) kept
  | .listLength values => mixList (mix 0 5) values
  | .listAppend left right => mixList (mixList (mix 0 6) left) right
  | .capturedLambda captured argument =>
    mixNat (mixNat (mix 0 7) captured) argument
  | .dynamicPap lf rf left right =>
    mixNat (mixNat (mixForm (mixForm (mix 0 8) lf) rf) left) right
  | .partialAdd form value => mixNat (mixForm (mix 0 9) form) value
  | .uniquePair left right => mixNat (mixNat (mix 0 10) left) right
  | .linearPair left right => mixNat (mixNat (mix 0 11) left) right
  | .linearIdentity value => mixNat (mix 0 12) value
  | .affineDead dead kept => mixNat (mixNat (mix 0 13) dead) kept
  | .mixedDropFst dead kept => mixNat (mixNat (mix 0 14) dead) kept
  | .mixedDropSnd kept dead => mixNat (mixNat (mix 0 15) kept) dead
  | .erasedApp argument => mixNat (mix 0 16) argument
  | .erasedProjection field => mixNat (mix 0 17) field
  | .freezeNeeded value => mixNat (mix 0 18) value
  | .dereliction value => mixNat (mix 0 19) value
  | .duplicateUnique value => mixNat (mix 0 20) value
  | .deadLinear dead kept => mixNat (mixNat (mix 0 21) dead) kept
  | .uniqueProjection field left right =>
    mixNat (mixNat (mixNat (mix 0 22) field) left) right
  | .nonManyLambda argument result =>
    mixNat (mixNat (mix 0 23) argument) result
  | .partialNonMany argument => mixNat (mix 0 24) argument
  | .sharedCallAtUnique left right kept =>
    mixNat (mixNat (mixNat (mix 0 25) left) right) kept
  | .uniqueCapture value => mixNat (mix 0 26) value
  | .uniqueRecursor major => mixNat (mix 0 27) major

structure Summary where
  checked : Nat
  differential : Nat
  expectedRejections : Nat
  allKindsSeen : Bool
  finalState : UInt64
  fingerprint : UInt64
  deriving BEq, DecidableEq, Repr, Inhabited

def summarize (seed : UInt64 := defaultSeed)
    (count : Nat := defaultCases) : Summary := Id.run do
  let mut state := seed
  let mut differential := 0
  let mut expectedRejections := 0
  let mut seen := Array.replicate allKinds.size false
  let mut fingerprint : UInt64 := 0xcbf29ce484222325
  for index in [:count] do
    let (test, nextState) := generateAt seed index state
    match test.template.expectation with
    | .differential _ => differential := differential + 1
    | .lowerError .. => expectedRejections := expectedRejections + 1
    seen := seen.set! (index % allKinds.size) true
    fingerprint := mix fingerprint test.template.fingerprint
    state := nextState
  return ⟨count, differential, expectedRejections,
    seen.all (fun covered => covered), state, fingerprint⟩

#guard allKinds.size == 28

end Ix.Compiler.IxIR1.WellModedGen
