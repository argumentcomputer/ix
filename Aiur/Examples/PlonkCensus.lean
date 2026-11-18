import Aiur.Plonk.Schema
import Aiur.Plonk.Template

open Aiur.Plonk Aiur.Plonk.Lower

def groupOf (n : String) : String :=
  if n.startsWith "<table:" then "fixed"
  else if n == "Blake3::compress" then "blake3"
  else if n.startsWith "BN254G1" || n.startsWith "BN254Fq" || n.startsWith "KzgMsm" then "g1fq"
  else if n.startsWith "KzgBlake3" || n.startsWith "KzgTranscript" then "glue"
  else "other"

def Aiur.Plonk.Lower.Census.plus (a b : Census) : Census :=
  ⟨a.constraint + b.constraint, a.count + b.count, a.fingerprint + b.fingerprint,
   a.logup + b.logup, a.pool + b.pool, a.commit + b.commit⟩

def main (args : List String) : IO Unit := do
  let path := args.headD "target/e2e-l3/plonk-prepared/prepared/schema.json"
  let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
  let src ← IO.ofExcept (Schema.source j)
  let mut pool : Pool := {}
  let mut groups : Std.HashMap String Census := {}
  let mut lines : Array (Nat × String) := #[]
  for t in src.tables do
    let (c, p) := lowerTable t pool
    pool := p
    let poolDelta := 0
    groups := groups.insert (groupOf t.name) ((groups.getD (groupOf t.name) {}).plus c)
    lines := lines.push (c.total + poolDelta, s!"{t.name} rows {t.rows} total {c.total} {repr c}")
  for (_, l) in lines.qsort (fun a b => a.1 > b.1) |>.extract 0 25 do IO.println l
  let mut all : Census := {}
  for (g, c) in groups.toList do
    IO.println s!"{g}: {c.total} {repr c}"
    all := all.plus c
  IO.println s!"pool gates {pool.gates.size}"
  IO.println s!"ALL tables {all.total} + pool {pool.gates.size} = {all.total + pool.gates.size}"

def checkAll (args : List String) : IO Unit := do
  let path := args.headD "target/e2e-l3/plonk-prepared/prepared/schema.json"
  let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
  let src ← IO.ofExcept (Schema.source j)
  let mut ok := 0
  let mut bad := 0
  for t in src.tables do
    if Lower.Table.uniform t then
      match Lower.checkUniform t with
      | .ok () => ok := ok + 1
      | .error e => bad := bad + 1; IO.println e
  IO.println s!"uniform tables checked: {ok} accepted, {bad} rejected"
