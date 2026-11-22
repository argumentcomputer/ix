import IxCC.Cfg.Rc.Public
import IxCC.Recheck.Produce
import IxCCTests.Rt.Native
import Lean.Data.Json.FromToJson

/-! Native behavior controls for real source calls and complete output drops
in one tight arena, in a test executable IxCC writes of the object. Two
decoders check full values (the independent decoder `IxCCTests.Rt.Decoder` on
the live region, `Rt.readback` on the dump); separate free-address-set oracles
inspect every cell after every drop. No full runtime or Cfg simulation theorem
is assumed by this experiment. -/

namespace IxCCTests.Rt.Rc.ReuseSupport
set_option autoImplicit false
open IxCC Lean System

def listObs (xs : List Nat) : Sem.Obs :=
  xs.foldr (fun n tail => .ctor 1 [.nat n, tail]) (.ctor 0 [])

/-- Independent input/output formulas retained from the real-source `List.reverse` fixture's oracle.
-/
def expected (root : String) (n seed : Nat) : Sem.Obs :=
  let ascending := (List.range n).map (seed + ·)
  if root == "sharedReverse" then
    .ctor 0 [listObs ((List.range n).map fun i => seed + (n - 1 - i)), listObs ascending]
  else if root == "reverseRepeated" then listObs (List.replicate n seed)
  else listObs ascending

def inputs (root : String) : List (Nat × Nat) :=
  let maxN := if root == "reverseRepeated" then 64 else 128
  (List.range 50).map (fun i => (maxN, 100 + 3 * i)) ++
    [(0, 7), (1, 42), (4, 3), (7, 0), (32, 11), (maxN, 100)]

def capacity (root : String) : Nat :=
  24 * (if root == "sharedReverse" then 257 else if root == "reverseRepeated" then 65 else 129)

/-- The arena: the capacity and the context block, at least 4 KiB. -/
def regionSize (root : String) : Nat := max 4096 (capacity root + 640)

/-- The test executable's memory: a 1 MiB stack and the arena. -/
def mem (root : String) : IxCCTests.Exe.TestShell.Mem := { stack := 1048576, region := regionSize root }

def class3Allocation : Cfg.Instr → Bool
  | .bind _ (.alloc c _ _) => c.fieldless || c.arity == 2
  | _ => true

def command (logs : FilePath) (label cmd : String) (args : Array String) : IO Unit := do
  let before ← IO.monoMsNow
  let result ← IO.Process.output { cmd, args }
  let elapsed := (← IO.monoMsNow) - before
  IO.FS.writeFile (logs / s!"{label}.stdout") result.stdout
  IO.FS.writeFile (logs / s!"{label}.stderr") result.stderr
  IO.FS.writeFile (logs / s!"{label}.json") ((Json.mkObj [
    ("command", toJson cmd), ("args", toJson args), ("elapsed_ms", toJson elapsed),
    ("exit", toJson result.exitCode.toNat)]).pretty ++ "\n")
  unless result.exitCode == 0 do throw (IO.userError s!"{label}: inspect preserved diagnostics")

def link (logs : FilePath) (root symbol : String) (object : ByteArray) : IO FilePath := do
  let obj := logs / s!"reuse-{root}.o"
  let exe := logs / s!"reuse-{root}"
  IO.FS.writeBinFile obj object
  match IxCCTests.Exe.TestShell.writeExe (mem root) [X86.Exe.initSymbol, symbol, "cx_drop"] object with
  | .ok bytes =>
    IO.FS.writeBinFile exe bytes
    IO.setAccessRights exe { user := { read := true, write := true, execution := true } }
  | .error e => throw (IO.userError s!"{root}: no test executable: {e}")
  command logs s!"artifacts-{root}" "sha256sum" #[obj.toString, exe.toString]
  return exe

def follow (m : X86.Memory) (allowed : List X86.Word) :
    Nat → X86.Word → List X86.Word → Except String (List X86.Word)
  | 0, p, seen => if p == 0 then pure seen else throw "free chain exceeds allocated cell count"
  | fuel + 1, p, seen => do
    if p == 0 then return seen
    unless allowed.contains p do throw "free chain contains a non-cell address"
    if seen.contains p then throw "duplicate cell or cycle in free chain"
    follow m allowed fuel (m.read64 p) (p :: seen)

def verifyFree (cap : Nat) (before after : IxCCTests.Rt.Native.Line) : IO Unit := do
  unless after.status == 0 && after.ok && !after.init && after.obs == some "#0" do
    throw (IO.userError "invalid output-drop evidence")
  let some pre := before.dump | throw (IO.userError "missing live dump")
  let some post := after.dump | throw (IO.userError "missing reclaimed dump")
  unless pre.base == post.base && pre.start == post.start && pre.bump == post.bump &&
      post.bump == post.start + UInt64.ofNat cap && post.bytes.size == cap do
    throw (IO.userError "arena address/bump changed or dump incomplete")
  let allowed := (List.range (cap / 24)).map fun i => post.start + UInt64.ofNat (24 * i)
  let got ← IO.ofExcept (follow (post.memory (max 4096 (640 + cap))) allowed allowed.length after.value [])
  unless got.length == allowed.length && allowed.all got.contains do
    throw (IO.userError "not every allocated address was reclaimed exactly once")

/-! ## The session through a test executable

`runShell` runs the session in a test executable IxCC writes of the object
(`IxCCTests.Exe.TestShell`, calling `cx_init`, the root and `cx_drop`): one
initialization of a region of `max 4096 (capacity + 640)` bytes with a 1 MiB
stack, then per input the root call, the complete value decoded by the
independent decoder and by `Rt.readback` over the region (which must agree),
the result dynamically unique, the object area, `cx_drop` of the result, the
bump pointer unchanged and every allocated cell on the free chain exactly once
with the other size classes empty, then the free head and the object area
again. Until X1 this session was a C harness; this is that harness transcribed
to Lean, check for check (114,820 checks over the three roots), with the same
rows. Its check of its own region mapping is a check that the region reads
back zero-filled, and the one of its guarded stack a check that the memory is
one the test shell supports. -/

/-- The bytes `[base + 16, bump)` and the region's bounds. -/
structure Region where
  base : Nat
  size : Nat
  bump : Nat
  live : ByteArray

def Region.memory (r : Region) : X86.Memory := IxCCTests.Rt.Native.liveMemory r.base r.size r.bump r.live
def Region.readable (r : Region) (a n : Nat) : Bool := r.base + 16 ≤ a && a + n ≤ r.base + r.size
def Region.word (r : Region) (a : Nat) : Nat := (r.memory.read64 (UInt64.ofNat a)).toNat
/-- `ctx_field(offset)`: the word at `region + 64 + offset`. -/
def Region.ctx (r : Region) (offset : Int) : Nat := r.word (Int.toNat (r.base + 64 + offset))

def readRegion (s : IxCCTests.Exe.Session.Session) (base size : Nat) : IO Region := do
  let bump := (IxCCTests.Exe.Session.word (← IxCCTests.Exe.Session.read s (base + 16) 48) 8).toNat
  unless base + 16 ≤ bump && bump ≤ base + size do
    throw (IO.userError s!"the bump pointer {bump} is outside the region")
  return { base, size, bump, live := ← IxCCTests.Exe.Session.read s (base + 16) (bump - (base + 16)) }

def Region.dump (r : Region) (start : Nat) : IxCCTests.Rt.Native.Dump :=
  { base := UInt64.ofNat r.base, start := UInt64.ofNat start, bump := UInt64.ofNat r.bump
    bytes := (r.live.extract (start - (r.base + 16)) (r.bump - (r.base + 16))).data }

/-- The session in the test executable `exe`: its rows, its summary line and
its check count. -/
def runShell (exe : FilePath) (root : String) (sig : Rt.Sig) (ty : Rt.FoTy) :
    IO (List IxCCTests.Rt.Native.Line × String × Nat) := do
  let checks ← IO.mkRef 0
  let calls ← IO.mkRef 0
  let require (c : Bool) (label : String) : IO Unit := do
    checks.modify (· + 1)
    unless c do throw (IO.userError s!"FAIL call {← calls.get}: {label}")
  let cap := capacity root
  let size := regionSize root
  let m := mem root
  let base := m.base
  IxCCTests.Exe.Session.withSession exe (seconds := some 30) fun s => do
    require (0 < cap && cap ≤ 24 * 4096) "bounded typed reuse case"
    require ((IxCCTests.Rt.Decoder.parseType ty.encode).isSome && (IxCCTests.Rt.Decoder.parseSig sig.encode).isSome)
      "valid independent decoder type"
    let fresh ← IxCCTests.Exe.Session.read s base size
    require (fresh.data.all (· == 0)) "private arena mapping"
    require m.ok "guarded native stack"
    IxCCTests.Exe.Session.writeWord s (base + 16) m.budget
    let (r, _, ok) ← IxCCTests.Exe.Session.call s 0 [base, size, m.budget]
    require (r == 0 && ok) "single initialization status and ABI"
    let init ← readRegion s base size
    let start := init.ctx (-40)
    let limit := init.ctx (-32)
    require (start % 64 == 0 && init.readable start cap && start + cap ≤ limit)
      "bounded actual cx_init arena contains expected high water"
    require (limit == base + size) "actual cx_init limit matches mapped region"
    let mut rows : Array IxCCTests.Rt.Native.Line := #[]
    for (n, seed) in inputs root do
      calls.modify (· + 1)
      let (r, result, ok) ← IxCCTests.Exe.Session.call s 1 [base, n, seed]
      require (r == 0 && ok) "actual source root status and ABI"
      let live ← readRegion s base size
      let bump := live.bump
      let obs ← IxCCTests.Rt.Native.decodeBoth exe sig ty base size bump live.live (size / 8) result
      require obs.isSome "complete constructor-tree decoding"
      if result &&& 1 == 0 then
        require (live.readable result.toNat 8) "bounded independent word read"
        require (live.word result.toNat >>> 32 == 0) "dynamically unique output root"
      require (start ≤ bump && live.readable start (bump - start)) "bounded full object dump"
      rows := rows.push { status := 0, value := result, ok := true, obs
                          dump := some (live.dump start) }
      let (r, v, ok) ← IxCCTests.Exe.Session.call s 2 [base, result.toNat]
      require (r == 0 && v == 1 && ok) "generated complete output-drop status and ABI"
      let post ← readRegion s base size
      require (post.ctx (-40) == bump) "release does not change bump"
      -- all_reclaimed
      require (bump == start + cap && cap % 24 == 0)
        "same tight arena: bump stable at capacity without reinitialization"
      require (post.ctx (-32) == base + size) "cx_init arena limit unchanged"
      let cells := cap / 24
      require (cells ≤ 4096) "bounded independent free-chain oracle"
      let mut seen : Array Bool := Array.replicate cells false
      let mut p := post.ctx 24
      let mut count := 0
      for _ in List.range (cells + 1) do
        if p == 0 then break
        require (p ≥ start && p < bump && (p - start) % 24 == 0) "free cell is an exact allocated address"
        let index := (p - start) / 24
        require (!seen[index]!) "no duplicate free cell or cycle"
        seen := seen.set! index true
        count := count + 1
        require (post.readable p 8) "bounded independent word read"
        p := post.word p
      require (count == cells) "every allocated cell is reclaimed exactly once"
      for i in List.range cells do require seen[i]! "no leaked allocated address"
      for c in List.range 71 do
        if c + 1 != 3 then require (post.ctx (8 * (c + 1)) == 0) "other size classes remain empty"
      rows := rows.push { status := 0, value := UInt64.ofNat (post.ctx 24), ok := true, obs := some "#0"
                          dump := some (post.dump start) }
      require (start ≤ bump && post.readable start (bump - start)) "bounded full object dump"
    require ((← calls.get) ≥ 50) "at least fifty real-source calls in one arena"
    let summary := s!"PASS init=1 calls={← calls.get} capacity={cap} region={size} checks={← checks.get}; \
      complete values, all cells reclaimed, stable bump, no host metadata writes after init"
    return (rows.toList, summary, ← checks.get)

/-- The rows' checks: complete values by the independent decoder (the rows'
observations) and by `Rt.readback` of the dump, each against the independent
formula, and every allocated address reclaimed exactly once. -/
def checkRows (root : String) (sig : Rt.Sig) (ty : Rt.FoTy) (rows : List IxCCTests.Rt.Native.Line) : IO Unit := do
  let cases := inputs root
  unless rows.length == 2 * cases.length do throw (IO.userError "missing result/release pair")
  let mut remaining := rows
  for (n, seed) in cases do
    let live :: released :: rest := remaining | throw (IO.userError "missing pair")
    remaining := rest
    let want := expected root n seed
    unless live.status == 0 && live.ok && !live.init && live.obs == some (Rt.renderObs want) do
      throw (IO.userError s!"{root} {n} {seed}: independent full observation differs")
    unless live.readback (max 4096 (640 + capacity root)) sig ty == some want do
      throw (IO.userError s!"{root} {n} {seed}: independent full Lean memory observation differs")
    verifyFree (capacity root) live released

/-- A row as text: `status value ok obs`, then its `dump base start bump hex` line. -/
def renderRow (l : IxCCTests.Rt.Native.Line) : String :=
  let hex (b : UInt8) : String :=
    let d := fun (n : UInt8) => if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)
    String.ofList [d (b / 16), d (b % 16)]
  l.render ++ "\n" ++ match l.dump with
    | some d => s!"dump {d.base} {d.start} {d.bump} " ++ String.join (d.bytes.toList.map hex) ++ "\n"
    | none => ""

/-- The session for `root` in the test executable `exe` (`link`), its rows
checked, with its rows, summary and timing kept in `logs`. -/
def runDriver (logs exe : FilePath) (root : String) (sig : Rt.Sig) (ty : Rt.FoTy) : IO Json := do
  let cases := inputs root
  let begin ← IO.monoMsNow
  let (rows, summary, checks) ← runShell exe root sig ty
  let elapsed := (← IO.monoMsNow) - begin
  IO.FS.writeFile (logs / s!"{root}.stdout") (String.join (rows.map renderRow))
  IO.FS.writeFile (logs / s!"{root}.stderr") (summary ++ "\n")
  IO.FS.writeFile (logs / s!"{root}.json") ((Json.mkObj [
    ("executable", toJson exe.toString), ("elapsed_ms", toJson elapsed), ("checks", toJson checks),
    ("inputs", toJson (cases.map fun (n, s) => [n, s]))]).pretty ++ "\n")
  checkRows root sig ty rows
  IO.println s!"PASS {root}: {cases.length} same-arena real-source calls/drops; full values (two decoders) and all \
    addresses reclaimed; {checks} session checks"
  return Json.mkObj [("root", toJson root), ("calls", toJson cases.length),
    ("capacity_bytes", toJson (capacity root)),
    ("region_bytes", toJson (regionSize root)), ("native_elapsed_ms", toJson elapsed),
    ("evidence", toJson summary)]

end IxCCTests.Rt.Rc.ReuseSupport
