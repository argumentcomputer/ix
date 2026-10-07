import Ix.CompileCert.StrongCertifier

/-! The `compile-certify` command (`Ix.CompileCert.Certifier.runW`, then with
`--strong` the S path `Ix.CompileCert.Strong.runStrong`). -/

open Ix.CompileCert.Certifier

def usage : String :=
  "usage: compile-certify (--file <source.lean> | --modules <A,B,...>) <env.ixe> <out-prefix> \
  [--budget <nodes>] [--workers <n>] [--row-budget <ms>] [--refold] [--no-value-rows] [--explain <name>]* [--receipts-only] \
  [--strong | --strong-only [--strong-roots <A,B,...>] [--strong-every <k>] [--strong-max-cone <n>] [--strong-tasks <n>] \
  [--strong-plan] [--strong-global] [--explain-global] [--strong-changed]]\n  writes <out-prefix>.tsv (one row per constant), \
  <out-prefix>.classes.tsv, <out-prefix>.proj.tsv, <out-prefix>.receipts.tsv (projection lowering receipts), \
  <out-prefix>.receipts.statements, <out-prefix>.json, <out-prefix>.ixonly.tsv (artifact names with no Lean \
  constant), <out-prefix>.sizes.tsv (distinct Expr objects and tree size of every declaration with at least 4096 \
  objects) and, when W+ proposes rows, <out-prefix>.rows.tsv (each row's pre-screen time and verdict); \
  --budget: the size budget of one declaration (distinct Expr objects of its type, value and rules, default 2^28); \
  --row-budget: the pre-screen time budget of one W+ row (ms, default 60000; 0 checks no row); --refold: fold the W+ \
  support with the artifact again instead of continuing the admission's fold (measurement); --no-value-rows: \
  match transported clique members by Lean's eq_def only, without the value rows of package V (control; with \
  value rows the run also writes <out-prefix>.values.tsv); exit 0 iff something is \
  certified, nothing is rejected and every raw projection on a non-direct structure-like has a receipt;\n  --receipts-only: the projection measurement and receipts without the W check (exit 0 iff no refusal);\n  \
  --strong: after W, the strong-model endpoint S per cone (every W-certified constant, or the given roots, or every k-th \
  plus the projection functions); writes <out-prefix>.strong.tsv, .strong.cones.tsv, .strong.classes.tsv, .strong.json; \
  exit 0 iff additionally something is S-certified and nothing is S-rejected;\n  \
  --strong-plan: the cones S would run (the same order, batches and budget), none run, each counted as accepted; \
  writes <out-prefix>.strong.plan.tsv and .strong.plan.names.tsv and no S verdict;\n  \
  --strong-global: before the cover, one cone over every W-certified (direct or raw) constant whose closure stays among \
  them; the cover decides the rest (and everything, if the global cone is refused);\n  \
  --explain-global: the stages of the global cone, timed (diagnostics, no verdict);\n  \
  --strong-changed: after the strong cones, S at the value level (M7 S+a) for the constants W certifies by a W+ route \
  outside a changed inductive block (theorems, definitions with a value row) and their users, as one cone (each root \
  on its own if that cone is refused); a changed block, image recursor or type row stays S-unsupported (S+b), a \
  transported clique member without a value row S-unsupported (package V)"

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
    | "--refold" :: rest => options { cfg with refold := true } rest
    | "--no-value-rows" :: rest => options { cfg with valueRows := false } rest
    | "--strong" :: rest => options { cfg with strong := true } rest
    | "--strong-only" :: rest => options { cfg with strong := true, strongOnly := true } rest
    | "--strong-plan" :: rest => options { cfg with strong := true, strongPlan := true } rest
    | "--strong-global" :: rest => options { cfg with strong := true, strongGlobal := true } rest
    | "--explain-global" :: rest => options { cfg with strong := true, explainGlobal := true } rest
    | "--strong-changed" :: rest => options { cfg with strong := true, strongChanged := true } rest
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
