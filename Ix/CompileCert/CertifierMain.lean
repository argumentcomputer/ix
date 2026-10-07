import Ix.CompileCert.StrongCertifier

/-! The `compile-certify` command (`Ix.CompileCert.Certifier.runW`, then with
`--strong` the S path `Ix.CompileCert.Strong.runStrong`). -/

open Ix.CompileCert.Certifier

def usage : String :=
  "usage: compile-certify (--file <source.lean> | --modules <A,B,...>) <env.ixe> <out-prefix> \
  [--budget <nodes>] [--workers <n>] [--row-budget <ms>] [--explain <name>]* [--receipts-only] \
  [--strong | --strong-only [--strong-roots <A,B,...>] [--strong-every <k>] [--strong-max-cone <n>] [--strong-tasks <n>]]\n  writes <out-prefix>.tsv (one row per constant), \
  <out-prefix>.classes.tsv, <out-prefix>.proj.tsv, <out-prefix>.receipts.tsv (projection lowering receipts), \
  <out-prefix>.receipts.statements, <out-prefix>.json, <out-prefix>.ixonly.tsv (artifact names with no Lean \
  constant) and, when W+ proposes rows, <out-prefix>.rows.tsv (each row's pre-screen time and verdict); \
  --row-budget: the pre-screen time budget of one W+ row (ms, default 60000; 0 checks no row); exit 0 iff something is \
  certified, nothing is rejected and every raw projection on a non-direct structure-like has a receipt;\n  --receipts-only: the projection measurement and receipts without the W check (exit 0 iff no refusal);\n  \
  --strong: after W, the strong-model endpoint S per cone (every W-certified constant, or the given roots, or every k-th \
  plus the projection functions); writes <out-prefix>.strong.tsv, .strong.cones.tsv, .strong.classes.tsv, .strong.json; \
  exit 0 iff additionally something is S-certified and nothing is S-rejected"

def parse : List String → Option Config
  | "--file" :: path :: ixe :: out :: rest => options { lean := .file path, ixe, out } rest
  | "--modules" :: mods :: ixe :: out :: rest =>
    options { lean := .modules ((mods.splitOn ",").toArray.map String.toName), ixe, out } rest
  | _ => none
where
  options (cfg : Config) : List String → Option Config
    | [] => some cfg
    | "--budget" :: n :: rest => n.toNat?.bind fun b => options { cfg with budget := b } rest
    | "--workers" :: n :: rest => n.toNat?.bind fun w => options { cfg with workers := w } rest
    | "--row-budget" :: n :: rest => n.toNat?.bind fun b => options { cfg with rowBudget := b } rest
    | "--explain" :: n :: rest => options { cfg with explain := cfg.explain.push n.toName } rest
    | "--receipts-only" :: rest => options { cfg with receiptsOnly := true } rest
    | "--strong" :: rest => options { cfg with strong := true } rest
    | "--strong-only" :: rest => options { cfg with strong := true, strongOnly := true } rest
    | "--strong-roots" :: rs :: rest =>
      options { cfg with strongRoots := (rs.splitOn ",").toArray.map String.toName } rest
    | "--strong-every" :: n :: rest => n.toNat?.bind fun k => options { cfg with strongEvery := k } rest
    | "--strong-max-cone" :: n :: rest => n.toNat?.bind fun k => options { cfg with strongMaxCone := k } rest
    | "--strong-tasks" :: n :: rest => n.toNat?.bind fun k => options { cfg with strongTasks := k } rest
    | _ => none

def main (args : List String) : IO UInt32 := do
  match parse args with
  | none => IO.eprintln usage; return 2
  | some cfg =>
    let (code, state) ← runW cfg
    let mut code := code
    if cfg.strong then
      if let some w := state then
        let strongCode ← Ix.CompileCert.Strong.runStrong cfg w
        code := max code strongCode
    -- exit at once, without waiting for background tasks: a W+ pre-screen row left running
    -- past its time budget (the checker's pure code cannot be cancelled) would otherwise
    -- keep the process alive after its report, at the runtime's finalization
    (← IO.getStdout).flush
    (← IO.getStderr).flush
    IO.Process.exit code.toUInt8
