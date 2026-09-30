import Runner.Report

open Runner System

def usage : String :=
  "usage: runner COMMAND [OPTIONS] OUT\n\
   \n\
   build     [--fixtures a,b] [--compilatrix CMD] [--closures DIR] [--probe PATH] [--cc CC]\n\
   check     [--fixtures a,b]\n\
   calibrate [--cpu N] [--target-ms T] [--fixtures a,b]\n\
   measure   [--profile process|entry] [--cpu N] [--blocks B] [--fixtures a,b]\n\
   perf      [--cpu N] [--perf PATH] [--runs R] [--fixtures a,b]\n\
   report\n\
   \n\
   Run from benchmarks/runner; fixtures come from ../fixtures/manifest.json."

/-- Options as `--name value` pairs and one positional OUT. -/
def parse : List String → Except String (List (String × String) × Option String)
  | [] => .ok ([], none)
  | flag :: value :: rest =>
    if flag.startsWith "--" then do
      let (opts, out) ← parse rest
      return ((flag.drop 2 |>.toString, value) :: opts, out)
    else do
      let (opts, out) ← parse (value :: rest)
      if out.isSome then throw usage
      return (opts, some flag)
  | [last] => if last.startsWith "--" then .error usage else .ok ([], some last)

def main (args : List String) : IO UInt32 := do
  let root : FilePath := "../fixtures"
  try
    let manifest ← Manifest.load (root / "manifest.json")
    let (command, rest) ← match args with
      | c :: r => pure (c, r)
      | [] => throw (IO.userError usage)
    let (opts, out) ← IO.ofExcept (parse rest |>.mapError IO.userError)
    let some out := out | throw (IO.userError usage)
    let get (name : String) : Option String := (opts.find? (·.1 == name)).map (·.2)
    let nat (name : String) (default : Nat) : IO Nat :=
      match get name with
      | none => pure default
      | some v => match v.toNat? with
        | some n => pure n
        | none => throw (IO.userError s!"--{name} expects a number, got {v}")
    let known := match command with
      | "build" => ["fixtures", "compilatrix", "closures", "probe", "cc"]
      | "check" => ["fixtures"]
      | "calibrate" => ["cpu", "target-ms", "fixtures"]
      | "measure" => ["profile", "cpu", "blocks", "fixtures"]
      | "perf" => ["cpu", "perf", "runs", "fixtures"]
      | _ => []
    for (name, _) in opts do
      unless known.contains name do throw (IO.userError s!"unknown option --{name}\n{usage}")
    let only := (get "fixtures").map (·.splitOn ",")
    match command with
    | "build" =>
      build manifest root out {
        fixtures := only
        compilatrix := ((get "compilatrix").map (·.splitOn " " |>.filter (!·.isEmpty))).getD
          ["../../.lake/build/bin/compilatrix"]
        closures := (get "closures").getD "../../fixtures/ixon-v3/bench-k1"
        probe := (get "probe").map FilePath.mk
        cc := (get "cc").getD "cc" }
    | "check" => check manifest root out only
    | "calibrate" => calibrate manifest out (← nat "cpu" 2) (← nat "target-ms" 250) only
    | "measure" =>
      match (get "profile").getD "process" with
      | "process" => measureProcess manifest out (← nat "cpu" 2) (← nat "blocks" 10) only
      | "entry" => measureEntry manifest out (← nat "cpu" 2) (← nat "blocks" 10) only
      | p => throw (IO.userError s!"unknown profile {p}")
    | "perf" => perfAll manifest out (← nat "cpu" 2) ((get "perf").getD "perf") (← nat "runs" 3) only
    | "report" => report manifest out
    | _ => throw (IO.userError usage)
    return 0
  catch error =>
    IO.eprintln s!"runner: {error}"
    return 1
