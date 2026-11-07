import Tests.FormalChecks.Controller
import Tests.FormalChecks.Cuda
import Tests.FormalChecks.Ranges

/-!
The formal backend's check drivers, run by `tools/ixvm/check-formal.sh`:

- `controller`: resident proving and cross-record IxVM proofs;
- `cuda`: grouped, sharded CPU/CUDA proof and key parity (`--cpu-only` for the
  CPU controls);
- `ranges`: the range split of a one-shard proof.
-/

def main (args : List String) : IO UInt32 := do
  match args with
  | "controller" :: rest => Tests.FormalChecks.Controller.main rest
  | "cuda" :: rest => Tests.FormalChecks.Cuda.main rest
  | "ranges" :: rest => Tests.FormalChecks.Ranges.main rest
  | _ =>
    IO.eprintln "usage: formal-checks controller|cuda|ranges ARGS…"
    return 2
