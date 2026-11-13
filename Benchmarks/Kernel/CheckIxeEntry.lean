import Benchmarks.Kernel.CheckIxeFold
import Ix.Ixon.Authenticated
import IxCK.Host.Limits

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
def limits : Ix.Kernel.Admission.Limits :=
  { maxRecords := 1 <<< 22, maxBlobs := 1 <<< 22, maxTotalBytes := 1 <<< 34,
    maxRecordBytes := 1 <<< 28, maxRecordUnivNodes := 1 <<< 26 }

def millis (t0 t1 : Nat) : Nat := (t1 - t0) / 1000000

/-- The entry's stages without authentication, at the selected actual context. -/
def unauthenticated (table : Ix.Kernel.RoleTable) (pre : Prelude .anon)
    (records : Ix.Kernel.Admission.Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint) :
    Except Ix.Kernel.Admission.Error (Ix.Kernel.Env .anon) := do
  (Ix.Kernel.Admission.preflight limits records blobs).mapError .ofBytes
  (Ix.Kernel.Admission.uniqueKeys records blobs).mapError .ofBytes
  let constants ← (Ix.Kernel.Admission.decodeWithin limits records).mapError .ofBytes
  Ix.Kernel.Admission.checkConstantsWith Address.blake3 table pre constants blobs hint limits.fold

def verdict : Except Ix.Kernel.Admission.Error (Ix.Kernel.Env .anon) → String
  | .ok env => s!"accepted, {env.consts.length} constants installed"
  | .error e => s!"{repr e.outcome}: {e}"

/-- `limits` under the `IX_KERNEL_*` variables (`Ix.Kernel.Host.resolve`; `IX_KERNEL_WORKERS` bounds
phase B's tasks); a malformed one is an error. -/
def limitsFromEnv : IO Ix.Kernel.Admission.Limits := do
  match ← Ix.Kernel.Host.resolveIO limits (fun _ => none) with
  | .ok s => return s.limits
  | .error e => throw (IO.userError e)

def run (args : List String) : IO UInt32 := do
  let [mode, input] := args
    | IO.eprintln "usage: kernel-check-ixe --entry authenticated|unauthenticated|user|hash|depth <input.ixe>"; return 2
  let limits ← limitsFromEnv
  let started ← IO.monoMsNow
  let env ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile input) limits.maxDepth)
  let mut store : RecordStore := {}
  for (address, lazy) in env.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  let (table, pre) ← IO.ofExcept (Ix.KernelCheck.Binding.context env)
  let binding ← match env.roleBinding with
    | some raw => pure (⟨raw.address, raw.bytes⟩ : Ix.Kernel.Admission.Binding)
    | none => IO.ofExcept Ix.Kernel.Admission.defaultBinding
  let hints := Hints.ofStore store env.anonHints
  let s := setup store (env.blobs[·]?) table pre hints.lookup
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
  | "depth" =>
    -- the depth limit's two stages beside the decoding they surround, each timed alone
    let t0 ← IO.monoNanosNow
    let scan ← IO.lazyPure fun _ => Ix.Kernel.Admission.scanDepths limits records
    let t1 ← IO.monoNanosNow
    let decoded ← IO.lazyPure fun _ => Ix.Kernel.Admission.decodeRecords limits records
    let t2 ← IO.monoNanosNow
    let expanded ← IO.lazyPure fun _ => match decoded with
      | .ok constants => Ix.Kernel.Admission.expandedDepths limits constants
      | .error e => .error e
    let t3 ← IO.monoNanosNow
    let deepest ← IO.lazyPure fun _ => records.foldl (fun m (_, bytes) =>
      max m (((Ix.Kernel.Admission.Depth.record limits.maxDepth bytes).toOption).getD 0)) 0
    let word (r : Except Ix.Kernel.Admission.ByteError Unit) : String :=
      match r with | .ok () => "within" | .error e => s!"{repr e}"
    IO.eprintln s!"entry: depth scan {word scan} in {millis t0 t1} ms; decodeRecords 
      {if decoded.isOk then "ok" else "failed"} in {millis t1 t2} ms; expanded depths {word expanded} in 
      {millis t2 t3} ms; deepest stored nesting {deepest} (maxDepth {limits.maxDepth}); 
      {records.length} records, workers {repr limits.workers}"
    return if scan.isOk && expanded.isOk then 0 else 1
  | "user" =>
    -- the entry with user axioms admitted (`checkBytesWithUserAxioms`): phase B runs over every
    -- record even when the input holds an axiom the strict entry declines
    let t0 ← IO.monoNanosNow
    let result ← IO.lazyPure fun _ =>
      Ix.Kernel.Admission.checkBytesWithUserAxioms Address.admissionHash binding pre limits records blobs
        hints.lookup
    let t1 ← IO.monoNanosNow
    IO.eprintln s!"entry: user: {verdict result} in {millis t0 t1} ms; peak RSS {(← statusKb "VmHWM:") / 1024} MB"
    return if result.isOk then 0 else 1
  | "authenticated" | "unauthenticated" =>
    let t0 ← IO.monoNanosNow
    let result ← IO.lazyPure fun _ =>
      if mode == "authenticated" then
        Ix.Kernel.Admission.checkBytesWith Address.admissionHash binding pre limits records blobs hints.lookup
      else unauthenticated table pre records blobs hints.lookup
    let t1 ← IO.monoNanosNow
    IO.eprintln s!"entry: {mode}: {verdict result} in {millis t0 t1} ms; \
      peak RSS {(← statusKb "VmHWM:") / 1024} MB"
    return if result.isOk then 0 else 1
  | _ => IO.eprintln s!"unknown mode {mode}"; return 2

end Benchmarks.Kernel.CheckIxeEntry
