import Runner.Report

open Runner System

def usage : String :=
  "usage: runner COMMAND [OPTIONS] OUT\n\
   \n\
   build     [--fixtures a,b] [--ixcc CMD] [--closures DIR] [--probe PATH] [--cc CC]\n\
   \x20         [--variant NAME=DIR[,NAME=DIR...]]\n\
   check     [--fixtures a,b]\n\
   calibrate [--cpu N] [--target-ms T] [--fixtures a,b] [--rows r,s,ixcc@*]\n\
   measure   [--profile process|entry] [--cpu N] [--blocks B] [--fixtures a,b] [--rows ...]\n\
   \x20         [--gate MAXBUSY [--gate-wait S] [--gate-attempts A]]   (entry profile)\n\
   perf      [--cpu N] [--perf PATH] [--runs R] [--fixtures a,b] [--rows ...] [--gate MAXBUSY]\n\
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
      | "build" => ["fixtures", "ixcc", "closures", "probe", "cc", "variant"]
      | "check" => ["fixtures"]
      | "calibrate" => ["cpu", "target-ms", "fixtures", "rows"]
      | "measure" => ["profile", "cpu", "blocks", "fixtures", "rows", "gate", "gate-wait", "gate-attempts"]
      | "perf" => ["cpu", "perf", "runs", "fixtures", "rows", "gate", "gate-wait"]
      | _ => []
    for (name, _) in opts do
      unless known.contains name do throw (IO.userError s!"unknown option --{name}\n{usage}")
    let only := (get "fixtures").map (·.splitOn ",")
    let rows := (get "rows").map (·.splitOn ",")
    -- --gate MAXBUSY: wait for quiet blocks and rerun disturbed ones
    let gate : IO (Option Gate) := do
      if (get "gate").isNone then return none
      return some { maxBusy := ← nat "gate" 1, maxWaitS := ← nat "gate-wait" 1800,
                    attempts := ← nat "gate-attempts" 5 }
    match command with
    | "build" =>
      let variants ← ((get "variant").map (·.splitOn ",") |>.getD []).mapM fun spec =>
        match spec.splitOn "=" with
        | [name, dir] =>
          if name.isEmpty || !name.all (fun c => c.isAlphanum || c == '-' || c == '_') then
            throw (IO.userError s!"bad variant name in {spec}")
          else do pure (name, ← IO.FS.realPath dir)
        | _ => throw (IO.userError s!"--variant expects NAME=DIR, got {spec}")
      build manifest root out {
        variants
        fixtures := only
        ixcc := ((get "ixcc").map (·.splitOn " " |>.filter (!·.isEmpty))).getD
          ["../../.lake/build/bin/ixcc"]
        closures := (get "closures").getD "../../fixtures/ixon-v4/bench-k1"
        probe := (get "probe").map FilePath.mk
        cc := (get "cc").getD "cc" }
    | "check" => check manifest root out only
    | "calibrate" => calibrate manifest out (← nat "cpu" 2) (← nat "target-ms" 250) only rows
    | "measure" =>
      match (get "profile").getD "process" with
      | "process" => measureProcess manifest out (← nat "cpu" 2) (← nat "blocks" 10) only
      | "entry" => measureEntry manifest out (← nat "cpu" 2) (← nat "blocks" 10) only rows (← gate)
      | p => throw (IO.userError s!"unknown profile {p}")
    | "perf" => perfAll manifest out (← nat "cpu" 2) ((get "perf").getD "perf") (← nat "runs" 3) only rows (← gate)
    | "report" => report manifest out
    | _ => throw (IO.userError usage)
    return 0
  catch error =>
    IO.eprintln s!"runner: {error}"
    return 1
