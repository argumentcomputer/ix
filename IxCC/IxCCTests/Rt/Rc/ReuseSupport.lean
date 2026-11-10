import IxCC.Cfg.Rc.Public
import IxCC.Recheck.Produce
import IxCCTests.Rt.Native
import Lean.Data.Json.FromToJson

/-! Native behavior controls for real source calls and complete output drops
in one tight arena. Independent C and Lean decoders check full values; separate
free-address-set oracles inspect every cell after every drop. No full runtime
or Cfg simulation theorem is assumed by this experiment. -/

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
  command logs s!"link-{root}" "cc" #["-std=c11", "-O1", "-Wall", "-Wextra", "-Werror",
    "-Wl,--fatal-warnings", "-no-pie", "-I.", s!"-DENTRY={symbol}",
    "fixtures/x86/rc-reuse-driver.c", obj.toString, "-o", exe.toString]
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

def runDriver (logs exe : FilePath) (root : String) (sig : Rt.Sig) (ty : Rt.FoTy) : IO Json := do
  let cases := inputs root
  let args := #["--kill-after=5", "30", exe.toString, "--capacity", toString (capacity root),
    "--type", ty.encode, "--sig", sig.encode]
  let begin ← IO.monoMsNow
  let child ← IO.Process.spawn {
    cmd := "timeout", args, stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.putStr (String.join (cases.map fun (n, seed) => s!"{n} {seed}\n"))
  stdin.flush
  let out ← child.stdout.readToEnd
  let err ← child.stderr.readToEnd
  let status ← child.wait
  let elapsed := (← IO.monoMsNow) - begin
  IO.FS.writeFile (logs / s!"{root}.stdout") out
  IO.FS.writeFile (logs / s!"{root}.stderr") err
  IO.FS.writeFile (logs / s!"{root}.json") ((Json.mkObj [
    ("command", toJson "timeout"), ("args", toJson args), ("elapsed_ms", toJson elapsed),
    ("exit", toJson status.toNat), ("inputs", toJson (cases.map fun (n, s) => [n, s]))]).pretty ++ "\n")
  unless status == 0 do throw (IO.userError s!"{root}: native repeated-call driver failed")
  let some rows := IxCCTests.Rt.Native.parse out true false |
    throw (IO.userError "malformed native repeated-call output")
  unless rows.length == 2 * cases.length do throw (IO.userError "missing result/release pair")
  let mut remaining := rows
  for (n, seed) in cases do
    let live :: released :: rest := remaining | throw (IO.userError "missing pair")
    remaining := rest
    let want := expected root n seed
    unless live.status == 0 && live.ok && !live.init && live.obs == some (Rt.renderObs want) do
      throw (IO.userError s!"{root} {n} {seed}: independent full C observation differs")
    unless live.readback (max 4096 (640 + capacity root)) sig ty == some want do
      throw (IO.userError s!"{root} {n} {seed}: independent full Lean memory observation differs")
    verifyFree (capacity root) live released
  IO.println s!"PASS {root}: {cases.length} same-arena real-source calls/drops; full C+Lean values and all addresses reclaimed"
  return Json.mkObj [("root", toJson root), ("calls", toJson cases.length),
    ("capacity_bytes", toJson (capacity root)),
    ("region_bytes", toJson (max 4096 (640 + capacity root))), ("native_elapsed_ms", toJson elapsed),
    ("c_evidence", toJson err)]

end IxCCTests.Rt.Rc.ReuseSupport
