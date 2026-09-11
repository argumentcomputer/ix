import Ix.Compiler.IxIR1.Lower

/-!
# Counter-level thesis evidence

Paired IxIR₀ programs are lowered and executed twice: once with all runtime
values shared, and once with the strongest modes the current restriction wall
admits.  `eraseModes` makes "same program" executable rather than editorial:
each pair has identical syntax after removing `Uses` annotations.

The observations include the result digest and exact IxIR₁ instruction
counters both before and after releasing the result.  These are deterministic
interpreter counts, not wall-clock claims.  The present compiler still cannot
destructure unique data and emits no `reuse`; accordingly this first suite
measures construction and reclamation only and pins `reuses = 0` on both sides.
-/

namespace Ix.Compiler.IxIR1.ThesisBench

open Ix.Compiler.Ixon (Address Owned Uses)
open Ix.Compiler.IxIR0
open Ix.Compiler.IxIR0.Examples
open Ix.Compiler.IxIR1.Lower

/-! ## Mode-insensitive program shape -/

/-- Forget the lowering-only mode annotations from an IxIR₀ expression. -/
def eraseModes : Expr → Expr
  | .var index => .var index
  | .ref address => .ref address
  | .app function argument =>
      .app (eraseModes function) (eraseModes argument)
  | .lam _ body => .lam .many (eraseModes body)
  | .letE _ value body =>
      .letE .many (eraseModes value) (eraseModes body)
  | .proj index value => .proj index (eraseModes value)
  | .lit literal => .lit literal
  | .erased => .erased

/-! ## Executable observations -/

structure CounterSnapshot where
  allocs : Nat
  reuses : Nat
  frees : Nat
  rcops : Nat
  live : Nat
  deriving BEq, Repr

def CounterSnapshot.ofStore (store : Store) : CounterSnapshot :=
  { allocs := store.allocs
    reuses := store.reuses
    frees := store.frees
    rcops := store.rcops
    live := store.live }

inductive ResultDigest where
  | nat (value : Nat)
  | natPair (first second : Nat)
  deriving BEq, Repr

def digestTree? (tree : Tree) : Option ResultDigest :=
  match natT? tree with
  | some value => some (.nat value)
  | none =>
    match tree with
    | .ctorT address 0 [first, second] => do
      if address != pairMk then none
      let first ← natT? first
      let second ← natT? second
      pure (.natPair first second)
    | _ => none

structure Observation where
  result : ResultDigest
  beforeRelease : CounterSnapshot
  afterRelease : CounterSnapshot
  deriving BEq, Repr

/-- Compile, execute, decode, and release one closed benchmark. -/
def observe (decls : List (Address × IxIR0.Decl)) (expression : Expr)
    (world : Owned) : Option Observation := do
  let (targetDecls, code) ←
    (lowerAll decls expression world).toOption
  let ctx : Ctx :=
    { decls := Env.ofList targetDecls, oracle := tgtOracle }
  let (store, value) ← (runMain ctx code).toOption
  let tree ← treeOfR store 1000 value
  let result ← digestTree? tree
  let released ← (releaseResult ctx 100000 store value).toOption
  pure
    { result
      beforeRelease := .ofStore store
      afterRelease := .ofStore released }

structure BenchmarkReport where
  name : String
  sameProgram : Bool
  allShared : Option Observation
  modeDirected : Option Observation
  deriving BEq, Repr

/-! ## Three paired programs -/

/-- Build the same pair of unary naturals entirely in the shared world. -/
def sharedPair : Expr :=
  .letE .many (natE 2) (.letE .many (natE 3)
    (.app (.app (.ref pairMk) (.var 1)) (.var 0)))

/-- The identical pair construction with linear bindings and a unique result. -/
def modePair : Expr :=
  .letE .linear (natE 2) (.letE .linear (natE 3)
    (.app (.app (.ref pairMk) (.var 1)) (.var 0)))

/-- Construct `2̂`, discard it, and return `1̂` in the shared world. -/
def sharedDead : Expr := .letE .many (natE 2) (natE 1)

/-- The identical dead-value program with affine reclamation. -/
def modeDead : Expr := .letE .affine (natE 2) (natE 1)

private def keepSecondAddress : Address := synthAddr 700

private def sharedKeepSecondBody : Expr :=
  .lam .many (.lam .many (.var 0))

private def modeKeepSecondBody : Expr :=
  .lam .affine (.lam .many (.var 0))

private def sharedKeepSecondDecls : List (Address × IxIR0.Decl) :=
  declList ++ [(keepSecondAddress, .defn .shared sharedKeepSecondBody)]

private def modeKeepSecondDecls : List (Address × IxIR0.Decl) :=
  declList ++ [(keepSecondAddress, .defn .shared modeKeepSecondBody)]

/-- Apply `fun _ y => y` to unary `1̂` and `2̂`.  Only the first
parameter's mode changes between declaration sets; the result stays shared. -/
def keepSecondMain : Expr :=
  .app (.app (.ref keepSecondAddress) (natE 1)) (natE 2)

def reports : List BenchmarkReport :=
  [ { name := "pair-tree"
      sameProgram := eraseModes sharedPair == eraseModes modePair
      allShared := observe declList sharedPair .shared
      modeDirected := observe declList modePair .unique }
  , { name := "dead-tree"
      sameProgram := eraseModes sharedDead == eraseModes modeDead
      allShared := observe declList sharedDead .shared
      modeDirected := observe declList modeDead .unique }
  , { name := "dead-parameter"
      sameProgram :=
        eraseModes sharedKeepSecondBody == eraseModes modeKeepSecondBody
      allShared := observe sharedKeepSecondDecls keepSecondMain .shared
      modeDirected := observe modeKeepSecondDecls keepSecondMain .shared } ]

private def snapshot (allocs reuses frees rcops live : Nat) :
    CounterSnapshot :=
  { allocs, reuses, frees, rcops, live }

private def observation (result : ResultDigest)
    (beforeRelease afterRelease : CounterSnapshot) : Observation :=
  { result, beforeRelease, afterRelease }

def expectedReports : List BenchmarkReport :=
  [ { name := "pair-tree", sameProgram := true
      allShared := some <| observation (.natPair 2 3)
        (snapshot 8 0 0 0 8) (snapshot 8 0 8 8 0)
      modeDirected := some <| observation (.natPair 2 3)
        (snapshot 8 0 0 0 8) (snapshot 8 0 8 0 0) }
  , { name := "dead-tree", sameProgram := true
      allShared := some <| observation (.nat 1)
        (snapshot 5 0 3 3 2) (snapshot 5 0 5 5 0)
      modeDirected := some <| observation (.nat 1)
        (snapshot 5 0 3 0 2) (snapshot 5 0 5 0 0) }
  , { name := "dead-parameter", sameProgram := true
      allShared := some <| observation (.nat 2)
        (snapshot 5 0 2 2 3) (snapshot 5 0 5 5 0)
      modeDirected := some <| observation (.nat 2)
        (snapshot 5 0 2 0 3) (snapshot 5 0 5 3 0) } ]

#guard reports == expectedReports

structure CounterTotals where
  allocs : Nat := 0
  reuses : Nat := 0
  frees : Nat := 0
  rcops : Nat := 0
  deriving BEq, Repr

def CounterTotals.addSnapshot (total : CounterTotals)
    (snapshot : CounterSnapshot) : CounterTotals :=
  { allocs := total.allocs + snapshot.allocs
    reuses := total.reuses + snapshot.reuses
    frees := total.frees + snapshot.frees
    rcops := total.rcops + snapshot.rcops }

def releasedTotals (select : BenchmarkReport → Option Observation) :
    List BenchmarkReport → CounterTotals
  | [] => {}
  | report :: rest =>
    let tail := releasedTotals select rest
    match select report with
    | some observed => tail.addSnapshot observed.afterRelease
    | none => tail

def allSharedTotals : CounterTotals :=
  releasedTotals (fun report => report.allShared) reports

def modeDirectedTotals : CounterTotals :=
  releasedTotals (fun report => report.modeDirected) reports

def savedRcOps : Nat := allSharedTotals.rcops - modeDirectedTotals.rcops

#guard allSharedTotals ==
  ({ allocs := 18, reuses := 0, frees := 18, rcops := 18 } :
    CounterTotals)
#guard modeDirectedTotals ==
  ({ allocs := 18, reuses := 0, frees := 18, rcops := 3 } :
    CounterTotals)
#guard savedRcOps == 15

/-! ## Mode-adversarial boundaries

These pairs share one mode-erased expression shape but sit on opposite sides
of a static rule.  The exact diagnostics prevent a different rejection from
accidentally satisfying the fixture. -/

def sharedDuplicate : Expr :=
  .letE .many (natE 1)
    (.app (.app (.ref pairMk) (.var 0)) (.var 0))

def linearDuplicate : Expr :=
  .letE .linear (natE 1)
    (.app (.app (.ref pairMk) (.var 0)) (.var 0))

def deadLinear : Expr := .letE .linear (natE 2) (natE 1)

def compileError? (expression : Expr) (world : Owned) : Option String :=
  match lowerAll declList expression world with
  | .ok _ => none
  | .error message => some message

structure AdversarialReport where
  name : String
  sameProgram : Bool
  accepted : Bool
  rejectedError : Option String
  deriving BEq, Repr

def adversarialReports : List AdversarialReport :=
  [ { name := "duplicate-shared-vs-linear"
      sameProgram := eraseModes sharedDuplicate == eraseModes linearDuplicate
      accepted := (lowerAll declList sharedDuplicate .shared).isOk
      rejectedError := compileError? linearDuplicate .unique }
  , { name := "dead-affine-vs-linear"
      sameProgram := eraseModes modeDead == eraseModes deadLinear
      accepted := (lowerAll declList modeDead .unique).isOk
      rejectedError := compileError? deadLinear .unique } ]

#guard adversarialReports ==
  [ { name := "duplicate-shared-vs-linear", sameProgram := true
      accepted := true
      rejectedError := some "unique variable used more than once" }
  , { name := "dead-affine-vs-linear", sameProgram := true
      accepted := true
      rejectedError := some "unused linear binding" } ]

def mismatchRejections : List (String × Option String) :=
  [ ("dereliction", compileError?
      (.letE .many (natE 1) (.app (.ref natSucc) (.var 0))) .unique)
  , ("freeze", compileError?
      (.letE .linear (natE 1) (.app (.ref natSucc) (.var 0))) .shared) ]

#guard mismatchRejections ==
  [ ("dereliction", some "dereliction: shared value at unique demand")
  , ("freeze", some
      "freeze not in v0: unique value at non-unique sink (see docs/compiler/lowering-restrictions.md)") ]

end Ix.Compiler.IxIR1.ThesisBench
