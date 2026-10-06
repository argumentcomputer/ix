import Ix.CompileCert.Certifier

/-! The `compile-certify` command (`Ix.CompileCert.Certifier.run`). -/

open Ix.CompileCert.Certifier

def usage : String :=
  "usage: compile-certify (--file <source.lean> | --modules <A,B,...>) <env.ixe> <out-prefix> \
  [--budget <nodes>] [--workers <n>] [--explain <name>]* [--receipts-only]\n  writes <out-prefix>.tsv (one row per constant), \
  <out-prefix>.classes.tsv, <out-prefix>.proj.tsv, <out-prefix>.receipts.tsv (projection lowering receipts), \
  <out-prefix>.receipts.statements and <out-prefix>.json; exit 0 iff something is \
  certified, nothing is rejected and every raw projection on a non-direct structure-like has a receipt;\n  --receipts-only: the projection measurement and receipts without the W check (exit 0 iff no refusal)"

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
    | "--explain" :: n :: rest => options { cfg with explain := cfg.explain.push n.toName } rest
    | "--receipts-only" :: rest => options { cfg with receiptsOnly := true } rest
    | _ => none

def main (args : List String) : IO UInt32 := do
  match parse args with
  | some cfg => run cfg
  | none => IO.eprintln usage; return 2
