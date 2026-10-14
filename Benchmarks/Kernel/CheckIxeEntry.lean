import Benchmarks.Kernel.CheckIxeFold
import Ix.Ixon.Authenticated

/-! # The certified entry over an environment check's accepted records (untrusted harness)

`kernel-check-ixe --entry <mode> <input.ixe>` runs the certified Ixon entry
at BLAKE3, `Ixon.Authenticated.checkBytes`, once over the records the
environment check would accept (selected as `--fold` selects them,
`CheckIxeFold.acceptedRecords`), submitted as their exact `.ixe` bytes in
the check order, with the `.ixe`'s blobs and the compiler's reducibility
hints, and reports the verdict, the number of installed constants and the
timings on stderr. The `.ixe` is loaded eagerly (`Ixon.deEnv`, which
verifies every hash itself); the load and the selection are not timed with
the entry.

Modes:
* `authenticated`: the entry, `preflight → uniqueKeys → authenticate →
  decodeRecords → reader → fold`.
* `unauthenticated`: the same stages without `authenticate`, composed from
  the entry's own functions (`Admission.checkBytesWith` minus the one
  stage): the entry as it ran before authentication, for comparison.
* `hash`: authentication alone (`Admission.authenticate`), at the
  admission hash (the Rust BLAKE3) and at pure BLAKE3 (`Address.blake3Pure`).

Run one at a time, each in its own process, with no concurrent build. -/

namespace Benchmarks.Kernel.CheckIxeEntry

open Ix.Kernel.Reader
open Benchmarks.Kernel.CheckIxeStep

/-- Bounds wide enough for a whole compiled library. -/
def limits : Ix.Kernel.Admission.Limits := ⟨1 <<< 22, 1 <<< 22, 1 <<< 34, 1 <<< 28, 1 <<< 26⟩

def millis (t0 t1 : Nat) : Nat := (t1 - t0) / 1000000

/-- The entry's stages without authentication, at the committed tables. -/
def unauthenticated (records : Ix.Kernel.Admission.Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint) :
    Except Ix.Kernel.Admission.Error Ix.Kernel.Env := do
  let pins ← defaultPins.mapError .prelude
  let pre ← builtinPrelude.mapError .prelude
  let natPins ← builtinNatOpPins.mapError .prelude
  (Ix.Kernel.Admission.preflight limits records blobs).mapError .ofBytes
  (Ix.Kernel.Admission.uniqueKeys records blobs).mapError .ofBytes
  let constants ← (Ix.Kernel.Admission.decodeRecords limits records).mapError .ofBytes
  Ix.Kernel.Admission.checkConstantsWith pins pre natPins constants blobs hint

def verdict : Except Ix.Kernel.Admission.Error Ix.Kernel.Env → String
  | .ok env => s!"accepted, {env.consts.length} constants installed"
  | .error e => s!"{repr e.outcome}: {e}"

def run (args : List String) : IO UInt32 := do
  let [mode, input] := args
    | IO.eprintln "usage: kernel-check-ixe --entry authenticated|unauthenticated|hash <input.ixe>"; return 2
  let started ← IO.monoMsNow
  let env ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile input))
  let mut store : RecordStore := {}
  for (address, lazy) in env.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  let pins ← IO.ofExcept defaultPins
  let pre ← IO.ofExcept builtinPrelude
  let hints := Hints.ofStore store env.anonHints
  let s := setup store (env.blobs[·]?) pins pre hints.lookup
  let (selected, dropped) ← IO.lazyPure fun _ => CheckIxeFold.acceptedRecords s
  -- exact `.ixe` bytes; a prelude record the `.ixe` lacks is the entry's own
  let records : Ix.Kernel.Admission.Records := selected.toList.filterMap fun (a, _) =>
    (env.consts[a]?).map fun lazy => (a, lazy.rawBytes)
  let blobs : Ix.Kernel.Ingress.Blobs := (env.blobs.toArray.qsort fun x y => x.1.cmpBytes y.1 == .lt).toList
  let recordBytes := Ix.Kernel.Admission.payloadBytes records
  let blobBytes := Ix.Kernel.Admission.payloadBytes blobs
  IO.eprintln s!"entry: {env.consts.size} records in the .ixe; {records.length} submitted \
    ({recordBytes} bytes; dropped {dropped} primary records the environment check declines or blocks), \
    {blobs.length} blobs ({blobBytes} bytes); load and selection {(← IO.monoMsNow) - started} ms"
  match mode with
  | "hash" =>
    let t0 ← IO.monoNanosNow
    let ffi ← IO.lazyPure fun _ => Ix.Kernel.Admission.authenticate Address.admissionHash records blobs
    let t1 ← IO.monoNanosNow
    let spec ← IO.lazyPure fun _ => Ix.Kernel.Admission.authenticate Address.blake3Pure records blobs
    let t2 ← IO.monoNanosNow
    let word (ok : Bool) : String := if ok then "authentic" else "refused"
    IO.eprintln s!"entry: authenticate at the admission hash (Rust BLAKE3): {word ffi.isOk} in {millis t0 t1} ms"
    IO.eprintln s!"entry: authenticate at pure BLAKE3: {word spec.isOk} in {millis t1 t2} ms"
    return if ffi.isOk && spec.isOk then 0 else 1
  | "authenticated" | "unauthenticated" =>
    let t0 ← IO.monoNanosNow
    let result ← IO.lazyPure fun _ =>
      if mode == "authenticated" then Ixon.Authenticated.checkBytes limits records blobs hints.lookup
      else unauthenticated records blobs hints.lookup
    let t1 ← IO.monoNanosNow
    IO.eprintln s!"entry: {mode}: {verdict result} in {millis t0 t1} ms; \
      peak RSS {(← statusKb "VmHWM:") / 1024} MB"
    return if result.isOk then 0 else 1
  | _ => IO.eprintln s!"unknown mode {mode}"; return 2

end Benchmarks.Kernel.CheckIxeEntry
