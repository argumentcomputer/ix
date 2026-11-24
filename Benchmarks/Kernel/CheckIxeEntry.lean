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

/-- The entry's stages without authentication, at the selected actual context. -/
def unauthenticated (table : Ix.Kernel.RoleTable) (pre : Prelude .anon)
    (records : Ix.Kernel.Admission.Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint) :
    Except Ix.Kernel.Admission.Error (Ix.Kernel.Env .anon) := do
  (Ix.Kernel.Admission.preflight limits records blobs).mapError .ofBytes
  (Ix.Kernel.Admission.uniqueKeys records blobs).mapError .ofBytes
  let constants ← (Ix.Kernel.Admission.decodeRecords limits records).mapError .ofBytes
  Ix.Kernel.Admission.checkConstantsWith Address.blake3 table pre constants blobs hint

def verdict : Except Ix.Kernel.Admission.Error (Ix.Kernel.Env .anon) → String
  | .ok env => s!"accepted, {env.consts.length} constants installed"
  | .error e => s!"{repr e.outcome}: {e}"

structure Options where
  mode : String := ""
  input : System.FilePath := ⟨""⟩
  strict? : Option Bool := none
  requireRoots : Array String := #[]

def usage : String :=
  "usage: kernel-check-ixe --entry [--strict|--allow-dropped] [--require-roots <r1,r2,...>] \
   authenticated|unauthenticated|hash <input.ixe>"

def parseArgs (args : List String) : Option Options :=
  go args {} #[]
where
  go : List String → Options → Array String → Option Options
    | "--strict" :: rest, o, pos => go rest { o with strict? := some true } pos
    | "--allow-dropped" :: rest, o, pos => go rest { o with strict? := some false } pos
    | "--require-roots" :: list :: rest, o, pos =>
      let rs := CheckIxeFold.parseRequireRoots list
      if rs.isEmpty then none else go rest { o with requireRoots := o.requireRoots ++ rs } pos
    | a :: rest, o, pos => if a.startsWith "--" then none else go rest o (pos.push a)
    | [], o, pos => match pos.toList with
      | [mode, input] => some { o with mode, input }
      | _ => none

def run (args : List String) : IO UInt32 := do
  let some options := parseArgs args
    | IO.eprintln usage; return 2
  let mode := options.mode
  let input := options.input
  -- `--entry authenticated` is fail-closed on dropped records by default unless
  -- `--allow-dropped` is explicitly passed.
  let strict := options.strict?.getD (mode == "authenticated")
  let started ← IO.monoMsNow
  let env ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile input))
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
    ({recordBytes} bytes; dropped {dropped} records the environment check declines, blocks, or orphans), \
    {blobs.length} blobs ({blobBytes} bytes); load and selection {(← IO.monoMsNow) - started} ms"
  if strict && (dropped > 0 || records.length != env.consts.size || selected.size != s.store.size) then
    IO.eprintln s!"entry: strict failure: dropped {dropped} record(s), submitted {records.length} of \
      {env.consts.size} .ixe record(s) (selected {selected.size} of {s.store.size} store record(s))"
    return 1
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
    unless ffi.isOk && spec.isOk do return 1
    unless options.requireRoots.isEmpty do
      let kept : Std.HashSet Address := selected.foldl (fun acc (a, _) => acc.insert a) {}
      let mut missing : Array String := #[]
      for name in options.requireRoots do
        match env.named[Ix.Name.fromLeanName (CheckIxeFold.parseRootName name)]? with
        | none => missing := missing.push s!"{name} (absent from .ixe named metadata)"
        | some entry =>
          if !kept.contains entry.addr then
            missing := missing.push s!"{name} (record {entry.addr} not in selected batch)"
      unless missing.isEmpty do
        IO.eprintln s!"entry: required roots missing ({missing.size}):"
        for m in missing do IO.eprintln s!"  {m}"
        return 1
    return 0
  | "authenticated" | "unauthenticated" =>
    let t0 ← IO.monoNanosNow
    let result ← IO.lazyPure fun _ =>
      if mode == "authenticated" then
        Ix.Kernel.Admission.checkBytesWith Address.admissionHash binding pre limits records blobs hints.lookup
      else unauthenticated table pre records blobs hints.lookup
    let t1 ← IO.monoNanosNow
    IO.eprintln s!"entry: {mode}: {verdict result} in {millis t0 t1} ms; \
      peak RSS {(← statusKb "VmHWM:") / 1024} MB"
    match result with
    | .error _ => return 1
    | .ok kenv =>
      unless options.requireRoots.isEmpty do
        let installed : Std.HashSet (Ix.Kernel.Key .anon) :=
          kenv.consts.foldl (fun acc ci => acc.insert ci.name) {}
        let missing := CheckIxeFold.checkRequiredRoots env s.cx installed options.requireRoots
        unless missing.isEmpty do
          IO.eprintln s!"entry: required roots missing or unaccepted ({missing.size}):"
          for m in missing do IO.eprintln s!"  {m}"
          return 1
      return 0
  | _ => IO.eprintln s!"unknown mode {mode}"; return 2

end Benchmarks.Kernel.CheckIxeEntry
