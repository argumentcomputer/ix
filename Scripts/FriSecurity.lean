import Ix.Aiur.FriSecurity

/-! `lake exe fri-security`: FRI soundness estimates for a key's instance under
its own or candidate parameters. See `Ix/Aiur/FriSecurity.lean` for the bounds
and `docs/stark-parameters.md` for their use. -/

open Aiur.FriSecurity

def usage : String := "usage: fri-security [STATISTICS | -] [--instance LOG_TRACE,COLUMNS,CONSTRAINTS,MAX_DEGREE,LOOKUP_ROWS,LOOKUP_WIDTH]
    [--log-blowup N] [--queries N] [--query-pow N] [--commit-pow N] [--log-arity N]
    [--parameters LOG_BLOWUP,QUERIES,COMMIT_POW,QUERY_POW]... [--drop I,J,...] [--set I:LOG_HEIGHT:MAIN,...] [--table]

STATISTICS is the JSON of `stark-verifier statistics KEY PROOF` (an Aiur proof)
or `fri_sizing --statistics outer-vk.bin` (the compression stage's FRI key), or
- for standard input. --instance gives an instance's facts directly instead.
Each --parameters set gets its own report; the other options override the
key's parameters, which default to Aiur's when only --instance is given.
--table prints one line per parameter set with each regime's weakest term."

def natList (s : String) : Except String (List Nat) :=
  (s.splitOn ",").filter (· != "") |>.mapM fun x =>
    x.trimAscii.toString.toNat?.elim (.error s!"not a number: {x}") .ok

structure Options where
  statistics : Option String := none
  inst : Option Instance := none
  overrides : List (Parameters → Parameters) := []
  sets : Array (Nat × Nat × Nat × Nat) := #[]
  drop : List Nat := []
  shapes : List (Nat × Nat × Nat) := []
  table : Bool := false

def parse : List String → Options → Except String Options
  | [], o => .ok o
  | "--table" :: rest, o => parse rest { o with table := true }
  | flag :: value :: rest, o => do
    let one : Except String Nat := value.toNat?.elim (.error s!"{flag}: not a number") .ok
    match flag with
    | "--queries" => let v ← one; parse rest { o with overrides := o.overrides ++ [({ · with queries := v })] }
    | "--query-pow" => let v ← one; parse rest { o with overrides := o.overrides ++ [({ · with queryPow := v })] }
    | "--commit-pow" => let v ← one; parse rest { o with overrides := o.overrides ++ [({ · with commitPow := v })] }
    | "--log-arity" => let v ← one; parse rest { o with overrides := o.overrides ++ [({ · with logArity := v })] }
    | "--log-blowup" => let v ← one; parse rest { o with overrides := o.overrides ++ [({ · with logBlowup := v })] }
    | "--parameters" =>
      match ← natList value with
      | [b, q, c, p] => parse rest { o with sets := o.sets.push (b, q, c, p) }
      | _ => .error "--parameters takes LOG_BLOWUP,QUERIES,COMMIT_POW,QUERY_POW"
    | "--instance" =>
      match ← natList value with
      | [lt, columns, constraints, degree, rows, width] =>
        parse rest { o with inst := some {
          logTrace := lt, columns, constraints, maxDegree := degree,
          lookupRows := rows, lookupWidth := width } }
      | _ => .error "--instance takes six numbers"
    | "--drop" => do parse rest { o with drop := ← natList value }
    | "--set" => do
      let shapes ← ((value.splitOn ",").filter (· != "")).mapM fun item => do
        match ← natList (item.replace ":" ",") with
        | [i, logHeight, main] => pure (i, logHeight, main)
        | _ => .error "--set takes I:LOG_HEIGHT:MAIN"
      parse rest { o with shapes }
    | _ =>
      if o.statistics.isNone && !flag.startsWith "--" then
        parse (value :: rest) { o with statistics := some flag }
      else .error s!"unknown option {flag}"
  | [path], o =>
    if o.statistics.isNone && !path.startsWith "--" then .ok { o with statistics := some path }
    else .error s!"unknown option {path}"

def readKey (path : String) : IO Key := do
  let text ← if path == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile path
  IO.ofExcept <| Lean.Json.parse text >>= Key.fromJson?

def tableRow (inst : Instance) (p : Parameters) : String :=
  let cells := (terms inst p).map fun r =>
    let (name, bits) := r.limit
    s!"{fmt bits} ({name})"
  s!"| {p.logBlowup} | {p.queries} | {p.commitPow} | {p.queryPow} | {p.conjecturedBits} | " ++
    " | ".intercalate cells.toList ++ " |"

def main (args : List String) : IO UInt32 := do
  if args.isEmpty || args.contains "--help" then
    IO.println usage
    let p := Parameters.default
    IO.println s!"\nAiur default: log_blowup {p.logBlowup}, {p.queries} queries, commit pow \
      {p.commitPow}, query pow {p.queryPow}: {p.conjecturedBits} conjectured query bits \
      (floor {Aiur.minConjecturedSecurityBits})"
    return if args.isEmpty then 1 else 0
  match parse args {} with
  | .error e => IO.eprintln s!"{e}\n{usage}"; return 2
  | .ok o =>
    let key : Key ← match o.statistics, o.inst with
      | some path, none => readKey path
      | none, some _ => pure { parameters := Parameters.default, circuits := #[] }
      | _, _ => IO.eprintln "give STATISTICS or --instance, not both"; return 2
    let circuits := applyOverrides key.circuits o.drop o.shapes
    let inst := o.inst.getD (instanceOf circuits)
    let base := o.overrides.foldl (fun p f => f p) key.parameters
    let sets := if o.sets.isEmpty then #[base] else o.sets.map fun (b, q, c, pw) =>
      { base with logBlowup := b, queries := q, commitPow := c, queryPow := pw }
    if o.table then
      IO.println s!"instance: trace 2^{inst.logTrace}, {inst.columns} batched columns, \
        {inst.constraints} constraints, max degree {inst.maxDegree}, lookup rows \
        {inst.lookupRows}, lookup width {inst.lookupWidth}"
      let names := (terms inst base).map fun r => (r.name.splitOn ", m=").headD r.name
      IO.println s!"| log_blowup | queries | commit pow | query pow | conjectured | \
        {" | ".intercalate names.toList} |"
      for p in sets do IO.println (tableRow inst p)
    else
      let source := if o.inst.isSome then "given instance" else
        s!"{key.circuits.size} circuits ({circuits.size} after overrides)" ++
          (key.shards.map (s!", {·} shards")).getD "" ++
          (key.proofBytes.map (s!", {·} proof bytes")).getD ""
      for p in sets do IO.println (report source inst p)
    return 0
