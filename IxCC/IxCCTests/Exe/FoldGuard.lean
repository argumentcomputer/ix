import IxCCTests.Exe.Run
import IxCCTests.Anf.FoldGuard

/-! The fold guard's front-door reproducers (`tests-exe`'s fold-guard part): the closure `ix
compile` wrote of `fixtures/fold/Fold.lean`, every root through what `ixcc compile` runs
(`Recheck.ingress`, `Cli.compileText`) and what `ixcc check-cert` runs on its certificate's text
(`Cli.checkText`), each root in its own process (`tests-exe --fold-root ROOT [EXE]`), so that an
abort fails one assertion instead of the suite, and its time and peak memory are its own.

Before the shrink walk bounded its folds (`Anf.Walk.foldable`), the exponents past `2 ^ 32 − 1`
aborted `ixcc compile` (`INTERNAL PANIC: Nat.pow exponent is too big`), `2 ^ (2 ^ 32 − 1)` built a
512 MiB literal, and `mulChain32` passed 24 GiB. Each root must now compile and recheck to the same
object within the bounds below, with every literal of its final Anf below `2 ^ 2048`; with `--run`
its executable on `5` prints Lean's value, or ends with `natOverflow` where the bound leaves a
primitive (or a literal operand) past a native word. -/

namespace IxCCTests.Exe.FoldGuard

open IxCC IxCCTests.Src
open System

def dir : FilePath := "fixtures/fold"

/-- Each root (in `IxCCTests.Fold`) and its executable's result on `5`: the number it prints, or
`none` for `natOverflow` (status 3). Lean's value differs from the executable's only past a native
word. -/
def roots : List (String × Option Nat) :=
  [("powIn", some 9), ("powOut", none), ("powOneIn", some 6), ("powOneOut", some 6),
   ("shlIn", some 6), ("shlOut", none), ("powMod100", some 7),
   ("pow0At", some 5), ("pow0Past", some 5), ("pow1At", some 6), ("pow1Past", some 6),
   ("pow2At", none), ("pow2Past", none), ("pow1Far", none),
   ("shl0Past", some 5), ("shl1At", none), ("shl1Past", none), ("shl2Past", none),
   ("mulChain32", none), ("litIn", some 7), ("litOut", none)]

/-- Milliseconds one root's compile and recheck may take in its process (ingress included). -/
def msBound : Nat := 10000

/-- Peak resident memory (kB) one root's process may reach. -/
def kbBound : Nat := 1048576

/-- The child: compile `root` and recheck its certificate's text; with `exe`, also write its
executable. Prints one line of `key=value` fields. -/
def child (root : String) (exe : Option FilePath) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile (dir / "anonymous.ixe")
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (dir / "consumer.equations.json")))
  let t0 ← IO.monoMsNow
  let inp ← IO.ofExcept ((Recheck.ingress bytes json ["IxCCTests.Fold." ++ root]).mapError (·.render))
  let cfg := Recheck.Config.forInput {} inp
  let compiled ← IO.lazyPure fun _ => Cli.compileText .off cfg inp
  let t1 ← IO.monoMsNow
  match compiled with
  | .error e => IO.println s!"compile=refused message={e.render}"; return 0
  | .ok (text, _, art) =>
    let checked ← IO.lazyPure fun _ => Cli.checkText cfg inp text
    let t2 ← IO.monoMsNow
    match checked with
    | .error e => IO.println s!"compile=ok check=refused message={e.render}"; return 0
    | .ok (_, art') =>
      let maxLit := (IxCCTests.Anf.FoldGuard.summary art.anf).2
      if let some f := exe then
        match ← IxCCTests.Exe.build f art {} with
        | .ok () => pure ()
        | .error e => IO.println s!"compile=ok check=ok exe=refused message={e.render}"; return 0
      IO.println s!"compile=ok check=ok same={art.object == art'.object} litbits={maxLit.log2 + 1} \
        compileMs={t1 - t0} checkMs={t2 - t1} peakKb={← IxCCTests.Anf.FoldGuard.peakKb}"
      return 0

/-- The value of `key=` in a child's line. -/
def field (line key : String) : Option String :=
  ((line.splitOn " ").find? (·.startsWith (key ++ "="))).map fun t => "=".intercalate (t.splitOn "=").tail

def part (a : Assert) (o : IxCCTests.Exe.Suite.Options) (work : FilePath) : IO (Array String) := do
  let guard ← IO.Process.output {
    cmd := "sha256sum", args := #["--status", "--check", (dir / "manifest.sha256").toString] }
  expect a (guard.exitCode == 0) "fixtures/fold: the fixture's identity changed (manifest.sha256)"
  let self ← IO.appPath
  let mut slowest := 0
  let mut peak := 0
  let mut ran := 0
  let mut overflows := 0
  for (root, want) in roots do
    let exe := work / s!"fold-{root}"
    let args := #["--fold-root", root] ++ (if o.run then #[exe.toString] else #[])
    let out ← IO.Process.output { cmd := self.toString, args }
    expect a (out.exitCode == 0)
      s!"{root}: the compile's process ended with {out.exitCode}: {out.stderr.trimAscii.toString}"
    let line := ((out.stdout.splitOn "\n").filter (·.startsWith "compile=")).headD ""
    expect a (field line "compile" == some "ok" && field line "check" == some "ok")
      s!"{root}: not compiled and rechecked: {line}"
    expect a (field line "same" == some "true") s!"{root}: the recheck's object differs: {line}"
    let num := fun k => ((field line k).bind String.toNat?).getD 0
    let ms := num "compileMs" + num "checkMs"
    expect a ((field line "litbits").isSome && num "litbits" ≤ 2 * Anf.Walk.foldBits)
      s!"{root}: a literal of {num "litbits"} bits in the final Anf"
    expect a (ms ≤ msBound) s!"{root}: compile and recheck took {ms} ms (bound {msBound})"
    expect a (0 < num "peakKb" && num "peakKb" ≤ kbBound)
      s!"{root}: peak memory {num "peakKb"} kB (bound {kbBound})"
    slowest := max slowest ms
    peak := max peak (num "peakKb")
    if o.run then
      let r ← IxCCTests.Exe.run exe ["5"]
      let ok := match want with
        | some v => r.code == 0 && r.obs == toString v
        | none => r.code == 67 && (r.stderr.splitOn "natOverflow").length > 1
      let wanted := match want with
        | some v => toString v
        | none => "natOverflow"
      expect a ok s!"{root} 5: {r.outcome} {r.obs} {r.stderr.trimAscii.toString}, expected {wanted}"
      if want.isNone then overflows := overflows + 1
      ran := ran + 1
  let runs := if o.run then s!"; natively on 5: {ran} run, {ran - overflows} print Lean's value, \
    {overflows} end with natOverflow" else "; natively: skipped (no --run)"
  return #[s!"{roots.length} roots compiled and rechecked to the same object, each in its own \
    process, every final literal below 2^{2 * Anf.Walk.foldBits}; slowest {slowest} ms (bound \
    {msBound}), largest peak {peak} kB (bound {kbBound}){runs}"]

end IxCCTests.Exe.FoldGuard
