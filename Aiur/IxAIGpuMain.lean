import IxAIGpuHost.Host

/-!
`ixai_gpu`: deterministic GPU training of `IxAICore` decision models.

```text
ixai_gpu train SEED HIDDEN LR EPOCHS BATCH TRAIN TEST   final weights, as `ixai weights`
ixai_gpu keys SEED HIDDEN LR EPOCHS BATCH TRAIN TEST    every step's hint keys
ixai_gpu check CASES [PATH]                             `ixai-gpu-export random` cases
ixai_gpu package DIR [N]                                Fixed::step packages of the full run
ixai_gpu bench NIN NHIDDEN NOUT BATCH [REPS]            one step's time, best of REPS (5)
```
`PATH` selects the GEMM path (`IxAIGpuHost.Context.setPath`): 0 default, 1 CUDA cores only,
2 tensor cores wherever the operands fit.
The configuration is the triage spec's `IxAICore.Config`, field by field.
-/

def configOf (args : List String) : Option IxAICore.Config :=
  match args.map String.toNat? with
  | [some seed, some hidden, some lr, some epochs, some batch, some train, some test] =>
    some { seed, hidden, lrRaw := lr, epochs, batch, trainSize := train, testSize := test }
  | _ => none

def usage : String :=
  "usage: ixai_gpu (train|keys) SEED HIDDEN LR EPOCHS BATCH TRAIN TEST | check CASES [PATH] | package DIR [N] | bench NIN NHIDDEN NOUT BATCH [REPS]"

def run : List String → IO UInt32
  | "train" :: rest => match configOf rest with
    | some c => do IxAIGpuHost.train c; return 0
    | none => do IO.eprintln usage; return 2
  | "keys" :: rest => match configOf rest with
    | some c => do IxAIGpuHost.keys c; return 0
    | none => do IO.eprintln usage; return 2
  | ["check", cases] => do IxAIGpuHost.check cases; return 0
  | ["check", cases, path] => match path.toNat? with
    | some p => do IxAIGpuHost.check cases p; return 0
    | none => do IO.eprintln usage; return 2
  | ["package", dir] => do IxAIGpuHost.package dir IxAIAiur.fullConfig.schedule.length; return 0
  | ["package", dir, n] => match n.toNat? with
    | some n => do IxAIGpuHost.package dir n; return 0
    | none => do IO.eprintln usage; return 2
  | "bench" :: rest => match rest.map String.toNat? with
    | [some i, some h, some o, some b] => benchWith i h o b 5
    | [some i, some h, some o, some b, some reps] => benchWith i h o b (max 1 reps)
    | _ => do IO.eprintln usage; return 2
  | _ => do IO.eprintln usage; return 2
where
  benchWith (i h o b reps : Nat) : IO UInt32 := do
    return if ← IxAIGpuHost.bench ⟨i, h, o⟩ b reps then 0 else 1

def main (args : List String) : IO UInt32 := do
  try run args
  catch e =>
    IO.eprintln s!"ixai_gpu: {e}"
    return (1 : UInt32)
