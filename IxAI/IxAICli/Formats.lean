import IxAIVerify.Trajectory
import IxAI.Formats

/-!
# `ixai formats`: numeric format comparison
-/

namespace IxAICli

open IxAI IxAIVerify

/- Closed subterms such as a reference training run would otherwise become module initializers,
run at every start of `ixai` whatever the command. -/
set_option compiler.extract_closed false

/-- Train the MLP once in format `α` and report accuracy and native training time. Results are
printed before the clock is read again, so the timing covers the computation. -/
def formatRun (α : Type) [Arith α] [DecidableEq α] [Enc α] (name : String) (c : TrainConfig)
    (d test : Dataset) : IO Unit := do
  let t0 ← IO.monoMsNow
  let links : List (Link (MLP α) (List Nat)) := c.run d
  let final := chainEnd c.init links
  let ok := c.inv final
  IO.println s!"{name}\tlr {c.lrRaw}\ttrain {final.accuracy d}%\ttest {final.accuracy test}%\tbounded {ok}"
  let t1 ← IO.monoMsNow
  IO.println s!"  {links.length} steps in {t1 - t0} ms"

/-- Quality and native cost of each numeric format on the same data, schedule and initial draws,
across learning rates. -/
def formats (seeds : List Nat) (lrs : List Int) : IO UInt32 := do
  let d := ({} : DataSpec).generate
  let test := Dataset.generate 4242 200 3
  IO.println s!"majority baseline: train {(d.items.size - d.positives) * 100 / d.items.size}%, test {(test.items.size - test.positives) * 100 / test.items.size}%"
  for seed in seeds do
    for lr in lrs do
      let c := { defaultConfig with lrRaw := lr, seed := seed.toUInt64 }
      IO.println s!"seed {seed}"
      formatRun Fx "fx8" c d test
      formatRun (FxN 12) "fx12" c d test
      formatRun (FxN 16) "fx16" c d test
      formatRun (FxN 24) "fx24" c d test
      formatRun (Bfp 8) "bfp8" c d test
      formatRun (Bfp 12) "bfp12" c d test
      formatRun (Bfp 16) "bfp16" c d test
      formatRun BF16 "bf16" c d test
      formatRun F32 "f32" c d test
  return 0

end IxAICli
