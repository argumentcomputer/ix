import Runner.Measure

/-! Summaries: per fixture and row, the median over blocks; per fixture, the
ratio of each row to `lean-clang` with a percentile-bootstrap interval over
paired blocks; per rung, the geometric mean of those ratios. A ratio above 1
means the row is slower than `lean-clang`. -/

namespace Runner

open Lean System

def median (values : Array Float) : Float :=
  let sorted := values.qsort (· < ·)
  if sorted.isEmpty then 0
  else if sorted.size % 2 == 1 then sorted[sorted.size / 2]!
  else (sorted[sorted.size / 2 - 1]! + sorted[sorted.size / 2]!) / 2

/-- Percentile bootstrap of the median paired ratio (deterministic resampling). -/
def bootstrap (ratios : Array Float) (rounds : Nat := 2000) : Float × Float := Id.run do
  if ratios.isEmpty then return (0, 0)
  let mut state : UInt64 := 0x243f6a8885a308d3
  let mut estimates : Array Float := #[]
  for _ in [:rounds] do
    let mut resample : Array Float := #[]
    for _ in [:ratios.size] do
      state := state ^^^ (state <<< 13)
      state := state ^^^ (state >>> 7)
      state := state ^^^ (state <<< 17)
      resample := resample.push ratios[state.toNat % ratios.size]!
    estimates := estimates.push (median resample)
  let sorted := estimates.qsort (· < ·)
  return (sorted[rounds * 25 / 1000]!, sorted[rounds * 975 / 1000]!)

/-- Fixed-point decimal text with `digits` fractional digits. -/
def fmt (value : Float) (digits : Nat := 3) : String :=
  let scaled := (value.abs * (10 : Float) ^ digits.toFloat).round.toUInt64.toNat
  let whole := scaled / 10 ^ digits
  let frac := toString (scaled % 10 ^ digits)
  let sign := if value < 0 then "-" else ""
  if digits == 0 then s!"{sign}{whole}"
  else s!"{sign}{whole}.{"".pushn '0' (digits - frac.length)}{frac}"

def report (manifest : Manifest) (out : FilePath) : IO Unit := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile (out / "samples.json")))
  let samples ← IO.ofExcept do
    (← (← json.getObjVal? "samples").getArr?).mapM fun s => do
      return (← (← s.getObjVal? "fixture").getStr?, ← (← s.getObjVal? "row").getStr?,
        ← (← s.getObjVal? "block").getNat?, ← (← s.getObjVal? "ns").getNat?)
  let env := json.getObjValD "environment"
  let mut lines : Array String := #[
    "# Local benchmark report", "",
    s!"Host: {env.getObjValD "cpu_model" |>.compress}, worker CPU {env.getObjValD "worker_cpu" |>.compress}, governor {env.getObjValD "governor" |>.compress}, load {env.getObjValD "loadavg" |>.compress}.",
    s!"Blocks per fixture: {json.getObjValD "blocks" |>.compress}. Whole-process wall time; ratio = row / lean-clang (above 1 is slower); 95% percentile-bootstrap intervals over paired blocks.", "",
    "| Fixture | Rung | lean-clang ms | clang-O2 ms | clang-O3 ms | clang-O2 / lean-clang | clang-O3 / lean-clang |",
    "| --- | --- | ---: | ---: | ---: | ---: | ---: |"]
  let mut rungRatios : Array (String × String × Float) := #[]
  let mut rows : Array Json := #[]
  for fixture in manifest.fixtures do
    let of (row : String) := samples.filter fun (f, r, _, _) => f == fixture.name && r == row
    let base := of "lean-clang"
    if base.isEmpty then continue
    let ms (row : String) := median ((of row).map fun (_, _, _, ns) => ns.toFloat / 1e6)
    let paired (row : String) : Array Float := (of row).filterMap fun (_, _, block, ns) =>
      (base.find? fun (_, _, b, _) => b == block).map fun (_, _, _, baseNs) => ns.toFloat / baseNs.toFloat
    let cell (row : String) : String :=
      let ratios := paired row
      let (low, high) := bootstrap ratios
      s!"{fmt (median ratios)} [{fmt low}, {fmt high}]"
    for row in ["clang-O2", "clang-O3"] do
      rungRatios := rungRatios.push (fixture.rung, row, median (paired row))
    lines := lines.push s!"| {fixture.name} | {fixture.rung} | {fmt (ms "lean-clang") 1} | {fmt (ms "clang-O2") 1} | {fmt (ms "clang-O3") 1} | {cell "clang-O2"} | {cell "clang-O3"} |"
    rows := rows.push (Json.mkObj [("fixture", Json.str fixture.name), ("rung", Json.str fixture.rung),
      ("median_ms", Json.mkObj (["lean-clang", "clang-O2", "clang-O3"].map fun r => (r, toJson (ms r)))),
      ("ratio_to_lean_clang", Json.mkObj (["clang-O2", "clang-O3"].map fun r => (r, toJson (median (paired r)))))])
  lines := lines ++ #["", "| Rung | Row | Geomean ratio to lean-clang | Fixtures |", "| --- | --- | ---: | ---: |"]
  for rung in ["K1", "K2", "K3"] do
    for row in ["clang-O2", "clang-O3"] do
      let values := rungRatios.filterMap fun (r, w, v) => if r == rung && w == row && v > 0 then some v else none
      unless values.isEmpty do
        let geo := Float.exp ((values.foldl (fun acc v => acc + Float.log v) 0) / values.size.toFloat)
        lines := lines.push s!"| {rung} | {row} | {fmt geo} | {values.size} |"
  IO.FS.writeFile (out / "report.md") ("\n".intercalate lines.toList ++ "\n")
  IO.FS.writeFile (out / "report.json") ((Json.mkObj [("environment", env), ("fixtures", Json.arr rows)]).pretty ++ "\n")
  IO.println s!"wrote {out / "report.md"}"

end Runner
