import Ix.Claim
import Ix.Address
import Ix.Meta
import Ix.CompileM
import Ix.Cronos
import Ix.Ixon.Expr
import Ix.Address
import Batteries

open Batteries (RBMap)

-- TODO: Make this configurable along with caching
def numRuns : Nat := 5

-- Get the average Cronos time in nanoseconds. Used when all timings correspond to the same function
def avgTime (c : Cronos) : Nat :=
  let timings := c.data.valuesList
  timings.sum / timings.length

-- TODO: If I don't print the result, Lean doesn't compute it despite using `never_extract`
-- Prevent Lean compiler from optimizing away function call
@[never_extract]
def blackBox {α β : Type} [Repr β] (f : α → β) (a : α) : IO Unit := do
  let ret := f a
  IO.println $ reprStr ret

def putStrNat (tup : String × Nat) : Ixon.PutM := do
  Ixon.putExpr <| .strl tup.fst
  Ixon.putExpr (.natl tup.snd)

def putCron (cron: Cronos) : Ixon.PutM := do
  Ixon.putArray (fun x => putStrNat x) cron.data.toList

def toIxon (c : Cronos) : ByteArray := Ixon.runPut (putCron c)

def getStrNat : Ixon.GetM (String × Nat) := do
  match (← Ixon.getExpr) with
  | .strl s =>
    match (← Ixon.getExpr) with
    | .natl n => return (s, n)
    | x => throw s!"expected Expr.Nat, got {repr x}"
  | x => throw s!"expected Expr.String, got {repr x}"

def getCron : Ixon.GetM Cronos := do
  let c ← (Ixon.getArray getStrNat).run
  return { refs := RBMap.empty, data := RBMap.ofList c compare}

def fromIxon (ixon: ByteArray) : Except String Cronos := Ixon.runGet getCron ixon

def cron : Cronos :=
  let cron' := Cronos.new
  { cron' with data := cron'.data.insert "hey" 1}

--#eval match fromIxon (toIxon cron) with
--  | Except.ok c    => IO.println $ repr c.data
--  | Except.error e => IO.println s!"error: {e}"
  --FS.writeFile

instance : Ixon.Serialize (RBMap String Nat compare) where
  put xs := (Ixon.runPut ∘ (Ixon.putArray (fun x => putStrNat x))) xs.toList
  get xs := (Ixon.runGet (Ixon.getArray getStrNat) xs).map (fun x => RBMap.ofList x compare)

--#eval (Ixon.Serialize.get (Ixon.Serialize.put cron.data) : Except String (RBMap String Nat compare))

def getStr : Ixon.GetM String := do
  match (← Ixon.getExpr) with
  | .strl s => return s
  | x => throw s!"expected Expr.String, got {repr x}"

instance : Ixon.Serialize (List String) where
  put xs := (Ixon.runPut ∘ (Ixon.putArray (fun x => Ixon.putExpr (.strl x)))) xs
  get := Ixon.runGet (Ixon.getArray getStr)

-- TODO
-- Load db from `~/.ix/benches/<hash>`, where `hash` is the SHA of the ixon data
--def loadCache (c : Cronos): IO Unit := do


-- TODO: Which data should be hashed for benchmark comparison? I think just the keys (aka bench names)
-- Store `Cronos` db as ixon on disk
def storeCache (c : Cronos) : IO Unit := do
  let ixon := Ixon.Serialize.put c.data.keysList
  let addr := Address.blake3 ixon
  let _output ← IO.Process.run {cmd := "mkdir", args := #["-p", "~/.ix/benches"] }
  --IO.FS.writeBinFile s!"~/.ix/benches/{addr.toString}" ixon

-- TODO: Add warm-up time to prevent slow first runs
-- TODO: Make sure compiler isn't caching partial evaluation result for future runs of the same function
def benchmark {α β : Type} [Repr β] (benches : List (String × (α → β) × α)) : IO Cronos := do
  let mut benchTimes := Cronos.new
  for (name,f,a) in benches do
    let mut cron := Cronos.new
    for run in List.range numRuns do
      let benchName := s!"{name} run {run}"
      cron ← cron.clock benchName
      blackBox f a
      cron ← cron.clock benchName
    let avg := avgTime cron
    IO.println avg
    benchTimes := { benchTimes with data := benchTimes.data.insert name avg }
  IO.println benchTimes.summary
  return benchTimes

partial def fib (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 1
  | n' => fib (n' - 1) + fib (n' - 2)

-- TODO: Make a DSL or otherwise allow functions that can take multiple arguments, without needing to input a tuple
-- See Criterion syntax at http://www.serpentine.com/criterion/tutorial.html
-- Expected input
--benchmark [
--  "fib" fib 1,
--  "add" add 1 2,
--]
-- Actual input
--#eval benchmark [
--  ("fib 1", fib, 1),
--  ("fib 2", fib, 2),
--  ("fib 30", fib, 30)
--  ]
