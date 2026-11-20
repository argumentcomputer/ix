import IxAICli
import IxAIData.Pipeline

/-!
# `ixai`: the trusted side of the training pipeline

* `ixai data FILE`: write the config, dataset header and items for an untrusted trainer.
* `ixai [--format F] train FILE`: write the reference trajectory computed by the specification.
* `ixai check FILE [--job NAME | --job-digest HEX] [--weights HEX]`: verify a trajectory written
  by any trainer, step by step, against the consumer's job (default `default`), never the file's
  own header (`IxAIVerify.Trajectory`).
* `ixai aiur-chain DIR`: verify the per-step Aiur proofs of the full run against the committed
  program and the specification (`IxAIVerify.Aiur`); `ixai aiur-diagnose DIR` reads the prover's
  reports instead, as a diagnostic that verifies nothing.
* `ixai package-assemble [--out DIR] [--plonk-key FILE]`: write the trainer's side of the model
  package of the full run (`docs/verification.md`), by default into `.truthmines/package/full`;
  with `--plonk-key` its `aiur-exec` route names that terminal PLONK verifying key.
* `ixai premises (extract|run) SCOPE`: the premise-selection dataset (`IxAIData`, `docs/data.md`).
* `ixai bench [tiny|small|full]`: the IxBench v0 report (`IxAIBench`); `full` adds the M2b
  typed-questions report, which `ixai bench typed` runs alone (`typed-sweep`: its config sweep;
  `typed-refute`: refutation hit rates by budget; `typed-cert`: the certified `prop-hard` section at
  smaller budgets; `typed-xhard`: the Tseitin family `prop-xhard`, with `typed-xhard-sweep`,
  `export-xhard DIR` and `score-xhard DIR` for its batches); `ixai bench export DIR` and
  `ixai bench score DIR`: batches for an LLM baseline (v0 and M2b kinds) and their scoring.

Formats: `fx` (fixed point, default), `bf16`, `f32`; the text format is in
`IxAIVerify.Trajectory`.

This executable links the benchmarks; `ixai-verify` is the consumer's verifier without them. The
commands are in `IxAICli`, one module per concern; this file only dispatches.
-/

open IxAI IxAIVerify IxAIVerify.Cli IxAICli

/-- `package-assemble [--out DIR] [--plonk-key FILE]`. -/
def packageAssembleCommand (args : List String) : IO UInt32 := do
  let rec known : List String → Bool
    | k :: _ :: rest => (k == "--out" || k == "--plonk-key") && known rest
    | [] => true
    | [_] => false
  unless known args do
    IO.println "usage: ixai [--format fx|bf16|f32] (data|train|check) FILE"; return 2
  packageAssemble ((flag args "--out").map System.FilePath.mk |>.getD packageDir)
    ((flag args "--plonk-key").map System.FilePath.mk)

def usageError (msg : String) : IO UInt32 := do
  IO.eprintln s!"ixai: {msg}"
  IO.eprintln "usage: ixai [--format fx|bf16|f32] (data|train|check) FILE; ixai certified DIR SIZE [CHUNK]; ixai formats [SEEDS LRS]; ixai reward BUNDLE [--out FILE]"
  return 2

def main (args : List String) : IO UInt32 := do
  let (fmt, rest) := match args with
    | "--format" :: f :: rest => (f, rest)
    | rest => ("fx", rest)
  match rest with
  | ["data", f] => writeData f fmt; return 0
  | ["train", f] => writeTrajectory f fmt
  | "check" :: f :: flags => trajectoryCommand f flags
  | ["claims", dir, size] => writeClaims dir size
  | ["chain", dir, size] => writeChain dir size
  | ["certified", dir, size] => writeCertified dir size
  | ["certified", dir, size, k] => match k.toNat? with
    | some k@(_ + 1) => writeCertifiedChunked dir size k
    | _ => usageError s!"chunk size must be a positive integer, not {repr k}"
  | ["weights", size] => writeWeights size
  | ["forge", dir, size] => writeForged dir size
  | ["mines", path] => mines path
  | ["reward", bundle] => reward bundle rewardsDefault
  | ["reward", bundle, "--out", out] => reward bundle out
  | ["reward-submit", bundle, task, file] => rewardSubmit bundle task file
  | ["sandbox-compile", bundle, file] => sandboxCompile bundle file
  | ["rl", size] => rlRun size
  | ["formats"] => formats [7] [1, 2, 4, 8]
  | ["formats", seeds, lrs] =>
    match (seeds.splitOn ",").mapM String.toNat?, (lrs.splitOn ",").mapM String.toInt? with
    | some ss, some ls => formats ss ls
    | _, _ => usageError s!"formats takes comma-separated integers: seeds (natural) and learning rates, not {repr seeds} {repr lrs}"
  | ["aiur-chain", dir] => aiurChain dir
  | ["aiur-diagnose", dir] => aiurDiagnose dir
  | "package-assemble" :: flags => packageAssembleCommand flags
  | "premises" :: rest => IxAIData.main rest
  | "bench" :: rest => bench rest
  | ["blake3", f] => do IO.println (IxAI.blake3 (← IO.FS.readBinFile f)).hex; return 0
  | _ => IO.println "usage: ixai [--format fx|bf16|f32] (data|train|check) FILE"; return 2
