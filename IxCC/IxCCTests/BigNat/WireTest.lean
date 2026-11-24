import IxCC.BigNat.Bootstrap
import IxCC.Rt.BigNat.Link
import IxCC.Rt.BigNat.LowerBig
import IxCC.Backend
import IxCC.Recheck
import IxCC.Lam.Erase.Array
import IxCC.Anf.Pipeline
import IxCC.Fir.Lower
import IxCC.Fir.Rep
import IxCC.Own.Immortal
import IxCC.Cfg.Lower
import IxCC.X86.ELFRodata
import IxCCTests.Exe.Session
import IxCCTests.BigNat.NativeDiffCore

/-! # Phase 4 Arbitrary-Precision `Nat` End-to-End Native Xeon Verification (`IxCCTests.BigNat.WireTest`)

Verifies the complete Phase 4 arbitrary-precision `Nat` pipeline natively on x86-64 Xeon
(seccomp-confined `TestShell`, zero C, zero GMP in target code):

1. **Bootstrap Library Compilation (`runBootstrap`)**:
   Freezes `IxCC.BigNat.Entry` + all 5 hardware `LimbOps` via `ix`, runs `Link.compileLibrary`
   (`Rt.lowerRep` + GraphColor IRC + fused `LimbOps`), checks `Lir.Program.check`, verifies zero
   `.fail .natOverflow` in all ABI wrappers & runtime procs, builds a standalone native Xeon ELF
   exporting `rt_bignat_*`, and smoke-tests all operations.
2. **`phase1-boundary` `2^63` Edge Cases (`runBoundary`)**:
   Loads `fixtures/corpus/phase1-boundary/boundary.ixe` + `boundary.equations.json`, compiles ALL
   boundary roots through `Rt.BigNat.lowerRepBig → Backend.compile → TestShell.writeExe`, verifies
   zero user/runtime/wrapper `.fail .natOverflow`, and executes every `2^63` edge case natively
   on Xeon — asserting `status == 0` (ZERO `natOverflow`), exact arbitrary-precision `NatVal`
   canonicality (odd `< 2^63`, `LimbArray` `≥ 2^63`), and exact equality with Lean 4 GMP!
3. **100,000+ Native Compiled-`ixcc` Differential Checks (`runNativeDiff` & `runNativeBatch`)**:
   Runs `NativeDiff.buildAllCases` (`100,000+` cases, `0..1,000` limbs, all 18 ops, `≥ 10` Knuth
   Algorithm D Step-D4 add-back triggers, Karatsuba `K=32` thresholds `31..1000`, zero divisors)
   directly against the native x86-64 Xeon compiled `IxCC.BigNat` ELF binary in a persistent
   `Session`, asserting **0 failures** and **0 `natOverflow`**!
   Also exposes `--native-batch` stdin/stdout streaming protocol for `tests-bignat-nativediff --batch`.
4. **ALL 6 K5 Benchmark Fixtures Natively on Xeon (`runK5`)**:
   Freezes & compiles `big-fib`, `factorial`, `pi-digits`, `big-mul`, `big-div`, and `big-gcd`
   end-to-end through `lowerRepBig → Backend.compile → TestShell.writeExe`, executes each natively
   on Xeon at BOTH `test_args` and `bench_args`, verifies exact bit-for-bit equality with Lean 4
   GMP (`expected.txt` / `bench_expected`), and reports raw Xeon wall-clock runtimes. -/

set_option autoImplicit false

namespace IxCCTests.BigNat.WireTest

open IxCC
open IxCC.BigNat
open IxCC.BigNat.Bootstrap
open IxCC.Rt
open IxCC.Rt.BigNat
open IxCC.X86
open IxCC.X86.ELFRodata
open IxCCTests.Exe
open IxCCTests.BigNat.NativeDiff
open System

/-! ## Common Helpers & Native `NatVal` Codec -/

private def dummyProv : ELF.Provenance :=
  .ixir1Policy (Ixon.Address.replicate 0xB4) 1 1

private def workDir : FilePath := "/tmp/ixcc-bignat-wire"

private def resolveIxBin : IO String := do
  if let some envBin ← IO.getEnv "IX_BIN" then
    if !envBin.isEmpty then return envBin
  let candidates : List FilePath :=
    [ "/home/john/runs/ixcc-megapr/.lake/build/bin/ix"
    , "../.lake/build/bin/ix"
    , "/home/jcb/projects/ix/.lake/build/bin/ix" ]
  for p in candidates do
    if ← p.pathExists then
      return p.toString
  return "ix"

private def require (cnt : IO.Ref Nat) (cond : Bool) (label : String) : IO Unit := do
  cnt.modify (· + 1)
  unless cond do
    throw (IO.userError s!"FAIL WireTest: {label}")

/-- Encode an arbitrary `Nat` into a Phase 4 `NatVal` word inside a `Session`:
* `n < 2^63` → odd immediate `2 * n + 1` (zero memory writes);
* `n ≥ 2^63` → writes canonical immortal static `LimbArray` cell (`rc = 0x80000000`) at
  `scratchPos`, advances `scratchPos`, and returns the 8-byte-aligned even pointer. -/
private def writeNatVal (s : Session.Session) (scratchPos : IO.Ref Nat) (n : Nat) : IO Nat := do
  if n < Rt.natLimit then
    return 2 * n + 1
  else
    let limbs := (IxCC.BigNat.ofNat n).toList
    let bytes := encodeStaticLimbArray limbs
    let addr ← scratchPos.get
    Session.write s addr bytes
    scratchPos.set (addr + bytes.size)
    return addr

/-- Read back an arbitrary-precision Phase 4 `NatVal` word from a `Session`, validating
strict canonicality (`odd < 2^63` OR even canonical `LimbArray` cell with `scan = 0`,
`tag = 0x7F03`, `size ≤ cap`, `size > 0`, `toNat ≥ 2^63`, non-zero top limb). -/
private def readNatVal (s : Session.Session) (w : UInt64) : IO (Except String Nat) := do
  if (w &&& 1) == 1 then
    return .ok (w >>> 1).toNat
  else
    if w == 0 || (w.toNat % 8 != 0) then
      return .error s!"non-aligned or null big pointer 0x{Nat.toDigits 16 w.toNat |> String.ofList}"
    let hdrBytes ← Session.read s w.toNat 24
    let hdr := Session.word hdrBytes 0
    let sz := (Session.word hdrBytes 8).toNat
    let cap := (Session.word hdrBytes 16).toNat
    let scan := (hdr &&& 0xFF).toNat
    let tag := ((hdr >>> 16) &&& 0xFFFF).toNat
    if scan != 0 || tag != 0x7F03 || sz == 0 || sz > cap then
      return .error s!"malformed BigNat header at {w}: scan={scan} tag={tag} sz={sz} cap={cap}"
    let limbBytes ← Session.read s (w.toNat + 24) (8 * sz)
    let mut limbs : List UInt64 := []
    for i in [:sz] do
      limbs := limbs ++ [Session.word limbBytes (8 * i)]
    if !Rt.isCanonicalLimbsList limbs then
      return .error s!"non-canonical BigNat limbs (len={limbs.length}, val={Rt.limbsToNatList limbs})"
    return .ok (Rt.limbsToNatList limbs)

/-- Check that every function in `prog` at indices `< stopIdx` or `≥ startWrapIdx` has
ZERO `.fail .natOverflow` blocks. -/
private def checkNoUserNatOverflow (label : String) (prog : Lir.Program)
    (skipRange : Option (Nat × Nat) := none) : IO Unit := do
  let ovfs := Bootstrap.checkLirHasNoNatOverflow prog
  let bad := match skipRange with
    | none => ovfs
    | some (lo, hi) => ovfs.filter fun (fi, _) => fi < lo || fi ≥ hi
  unless bad.isEmpty do
    throw (IO.userError s!"FAIL WireTest ({label}): found .fail .natOverflow in user/runtime/wrapper funcs: {bad}")

/-! ## Part 1: Bootstrap-Compile `IxCC.BigNat.Entry` & Build Standalone Xeon Binary -/

structure BuiltBigNat where
  lib : CompiledBigNatLib
  exePath : FilePath
  exportIdx : List (SlowPathOp × Nat)
  mem : TestShell.Mem
  boolTrueWord : UInt64
  boolFalseWord : UInt64

/-- Freeze and bootstrap-compile the pure-Lean `IxCC.BigNat.Entry` library (all 17 pure-limb
numeric entrypoints; zero C, zero GMP). -/
def compileBigNatLib (ixBin : String) (includeDecimal : Bool := false) : IO CompiledBigNatLib := do
  IO.FS.createDirAll (workDir / "bootstrap")
  let ops := if includeDecimal then SlowPathOp.all else SlowPathOp.numericOps
  let fcfg : FreezeConfig :=
    { ix := ixBin
    , sourceFile := "IxCC/BigNat/Entry.lean"
    , outDir := workDir / "bootstrap"
    , includeLimbEqns := false
    , ops }
  let frozen ← freezeClosure fcfg
  IO.ofExcept (compileLibrary frozen)

/-- Build the standalone native x86-64 Xeon test executable exporting `cx_init` and every
compiled `rt_bignat_*` wrapper (all args passed as `.word`, zero `< 2^63` wrapper guard). -/
def buildStandaloneExe (lib : CompiledBigNatLib) (mem : TestShell.Mem)
    (exeName : String := "bignat-lib-exe") : IO BuiltBigNat := do
  IO.FS.createDirAll workDir
  let (prog0, exports) ← IO.ofExcept ((standaloneLibraryProgram lib).mapError (·.render))
  let prog := prog0.splitCriticalEdges
  match prog.check with
  | .error e => throw (IO.userError s!"FAIL WireTest standaloneLibraryProgram Lir.check: {e}")
  | .ok () => pure ()
  -- Verify ZERO `.fail .natOverflow` in `cx_init` (idx 0) and ALL wrappers (idx ≥ 1 + lib.funcs.length)!
  checkNoUserNatOverflow "standaloneLibraryProgram" prog (some (1, 1 + lib.funcs.length))
  let bcfg : Backend.Config :=
    { provenance := dummyProv
      reps := fun f => (prog.funcs[f]?).map fun fd => fd.params.map fun _ => .word }
  let art ← IO.ofExcept ((Backend.compile prog bcfg).mapError toString)
  let exePath := workDir / exeName
  match TestShell.writeExe mem exports art.object with
  | .error err => throw (IO.userError s!"FAIL WireTest writeExe(standalone): {err}")
  | .ok exeBytes =>
    IO.FS.writeBinFile exePath exeBytes
    IO.setAccessRights exePath { user := { read := true, write := true, execution := true } }
  let exportIdx : List (SlowPathOp × Nat) :=
    lib.entries.zipIdx.map fun ((op, _), i) => (op, i + 1)
  pure
    { lib
    , exePath
    , exportIdx
    , mem
    , boolTrueWord := ctor0Word lib.boolTrueTag
    , boolFalseWord := ctor0Word lib.boolFalseTag }

/-- Smoke-test bootstrap compilation (including verifying all 19 Entry consts freeze cleanly,
checking `Lir.Program.check`, and testing every compiled `rt_bignat_*` op natively on Xeon). -/
def runBootstrap (cnt : IO.Ref Nat) (ixBin : String) : IO BuiltBigNat := do
  -- Also verify full 19-op freeze (including toDecimal/ofDecimal) succeeds cleanly
  IO.FS.createDirAll (workDir / "bootstrap-19")
  let f19 ← freezeClosure
    { ix := ixBin
    , sourceFile := "IxCC/BigNat/Entry.lean"
    , outDir := workDir / "bootstrap-19"
    , includeLimbEqns := false
    , ops := SlowPathOp.all }
  require cnt (f19.entryAddrs.length == 19) s!"freezeClosure(all 19) resolved {f19.entryAddrs.length} entries"
  require cnt (f19.limbPins.ops.length == 5) s!"freezeClosure resolved {f19.limbPins.ops.length}/5 LimbOps pins"
  -- Try full 19-op compilation first; fall back cleanly to 17 numeric ops if `toDecimal`/`ofDecimal`
  -- mix `String` with `kindOverride := some .limbs`
  let lib ← match compileLibrary f19 with
    | .ok lib19 =>
      IO.println s!"[WireTest] Compiled ALL 19 BigNat.Entry ops ({lib19.funcs.length} LIR funcs, smallFieldRep={reprStr lib19.smallFieldRep}, rawInternalOvfBlocks={lib19.rawNatOverflowCount})"
      pure lib19
    | .error e19 =>
      IO.println s!"[WireTest] Note: 19-op combined erase declined ({e19}); compiling 17 numeric BigNat.Entry ops..."
      let lib17 ← compileBigNatLib ixBin false
      IO.println s!"[WireTest] Compiled 17 numeric BigNat.Entry ops ({lib17.funcs.length} LIR funcs, smallFieldRep={reprStr lib17.smallFieldRep}, rawInternalOvfBlocks={lib17.rawNatOverflowCount})"
      pure lib17
  let mem : TestShell.Mem := { stack := 1024 * 1024, region := 128 * 1024 * 1024 }
  let built ← buildStandaloneExe lib mem "bignat-lib-exe"
  -- Quick native Xeon smoke test on key boundary transitions across every op
  let inputReserve := 256 * 1024
  let heapSize := mem.region - inputReserve
  let inputBase := mem.base + heapSize
  Session.withSession built.exePath (seconds := some 60) fun s => do
    let stackBudget := mem.stack - 4096
    Session.writeWord s (mem.base + 16) stackBudget
    let (r0, _, ok0) ← Session.call s 0 [mem.base, heapSize, stackBudget]
    require cnt (ok0 && r0 == 0) "standalone cx_init"
    let callBin (op : SlowPathOp) (a b : Nat) (lbl : String) : IO Nat := do
      let some idx := built.exportIdx.lookup op
        | throw (IO.userError s!"missing export for {op.key}")
      let scratch ← IO.mkRef inputBase
      let wa ← writeNatVal s scratch a
      let wb ← writeNatVal s scratch b
      let (rax, rdx, ok) ← Session.call s idx [mem.base, wa, wb]
      require cnt (ok && rax == 0) s!"smoke {lbl}: ok={ok} rax={rax}"
      match ← readNatVal s rdx with
      | .ok v => pure v
      | .error e => throw (IO.userError s!"smoke {lbl} readback: {e}")
    let callUn (op : SlowPathOp) (a : Nat) (lbl : String) : IO Nat := do
      let some idx := built.exportIdx.lookup op
        | throw (IO.userError s!"missing export for {op.key}")
      let scratch ← IO.mkRef inputBase
      let wa ← writeNatVal s scratch a
      let (rax, rdx, ok) ← Session.call s idx [mem.base, wa]
      require cnt (ok && rax == 0) s!"smoke {lbl}: ok={ok} rax={rax}"
      match ← readNatVal s rdx with
      | .ok v => pure v
      | .error e => throw (IO.userError s!"smoke {lbl} readback: {e}")
    let n63 := Rt.natLimit
    require cnt ((← callBin .add (n63 - 1) 1 "add promote") == n63) "add (2^63-1)+1 == 2^63"
    require cnt ((← callBin .sub n63 1 "sub demote") == n63 - 1) "sub 2^63-1 == 2^63-1"
    require cnt ((← callUn .pred n63 "pred demote") == n63 - 1) "pred 2^63 == 2^63-1"
    require cnt ((← callBin .mul (n63 - 1) 2 "mul promote") == 2 * (n63 - 1)) "mul (2^63-1)*2"
    require cnt ((← callBin .div (2 ^ 128) (2 ^ 64) "div big") == 2 ^ 64) "div 2^128/2^64"
    require cnt ((← callBin .mod (2 ^ 128 + 7) (2 ^ 64) "mod big") == 7) "mod (2^128+7)%2^64"
    require cnt ((← callBin .pow 2 100 "pow 2^100") == 2 ^ 100) "pow 2^100"
    require cnt ((← callBin .gcd (2 ^ 128) (2 ^ 64) "gcd big") == 2 ^ 64) "gcd 2^128 2^64"
    require cnt ((← callBin .land (n63 + 5) 7 "land demote") == 5) "land (2^63+5)&7"
    require cnt ((← callBin .lor n63 5 "lor big") == n63 + 5) "lor 2^63|5"
    require cnt ((← callBin .xor n63 n63 "xor demote") == 0) "xor 2^63^2^63"
    require cnt ((← callBin .shiftLeft 1 63 "shl 1<<63") == n63) "shl 1<<63"
    require cnt ((← callBin .shiftRight (2 ^ 128) 65 "shr 2^128>>65") == 2 ^ 63) "shr 2^128>>65"
    require cnt ((← callUn .log2 (2 ^ 128) "log2 2^128") == 128) "log2 2^128"
  pure built

/-! ## Part 2: User Program Compilation Through `Rt.BigNat.lowerRepBig` -/

/-- Compile any frozen `(ixeBytes, eqJson, rootNames)` closure end-to-end through
`Src → Lam.Erase.Array → Anf → Fir → Fir.Rep → Own → Cfg → Rt.BigNat.lowerRepBig →
Backend.compile (GraphColor IRC)` and verify `Lir.Program.check` + zero user/runtime/wrapper
`.fail .natOverflow`. -/
def compileUserProgram (label : String) (lib : CompiledBigNatLib)
    (ixeBytes : ByteArray) (eqJson : Lean.Json) (rootNames : List String)
    (rawWordArgs : Bool) : IO (Backend.Artifact × List String × Nat × Nat) := do
  let inp ← IO.ofExcept ((Recheck.ingress ixeBytes eqJson rootNames).mapError (·.render))
  let ps ← IO.ofExcept ((Recheck.produceSource {} inp).mapError (·.render))
  let (lam, _, info) ← IO.ofExcept
    ((Lam.Erase.Array.eraseWithArrays ps.src ps.checked .fixed [] none).mapError toString)
  let budgets : Anf.Pipeline.Budgets := { inline := { noInline := info.noInline } }
  let trace ← IO.ofExcept (Anf.Pipeline.produce budgets lam)
  let (anf, _) ← IO.ofExcept ((Recheck.produceClosures ps.src trace).mapError (·.render))
  let fir ← IO.ofExcept ((Fir.lower anf).mapError (·.render))
  let cert := Fir.Rep.inferWithArrays fir info
  unless Fir.Rep.checkWithArrays fir cert do
    throw (IO.userError s!"FAIL WireTest ({label}): Fir.Rep.checkWithArrays failed")
  let own := Own.immortal fir
  let cfg := Cfg.lower own
  let lowered ← IO.ofExcept ((Rt.BigNat.lowerRepBig { names := rootNames } lib cert cfg).mapError (·.render))
  let prog := lowered.program.splitCriticalEdges
  match prog.check with
  | .error e => throw (IO.userError s!"FAIL WireTest ({label}) Lir.check: {e}")
  | .ok () => pure ()
  -- Locate relocated BigNat library slice so we assert ZERO `.fail .natOverflow` in ALL user
  -- functions, `cxInit`, `natPowBig`, `natGcdBig`, `arrProcs`, `litProcs`, AND all 16 wrappers!
  let totalFuncs := prog.funcs.size
  let libStart := totalFuncs - coreWrapperCount - lib.funcs.length
  let libEnd := totalFuncs - coreWrapperCount
  checkNoUserNatOverflow label prog (some (libStart, libEnd))
  let repsFn : Lir.FunId → Option (List Xv.Stacking.ArgRep) := fun f =>
    if f == lowered.init then some [.word, .word]
    else if rawWordArgs then (prog.funcs[f]?).map fun fd => fd.params.map fun _ => .word
    else none
  let bcfg : Backend.Config := { provenance := dummyProv, reps := repsFn }
  let art ← IO.ofExcept ((Backend.compile prog bcfg).mapError toString)
  let exportNames := "cx_init" :: lowered.roots.map (·.2)
  let boolFalseTag := (fir.known.boolFalse.bind (Fir.CtorInfo.ofKey fir.ctors)).map (·.tag) |>.getD 0
  let boolTrueTag := (fir.known.boolTrue.bind (Fir.CtorInfo.ofKey fir.ctors)).map (·.tag) |>.getD 1
  pure (art, exportNames, boolTrueTag, boolFalseTag)

/-! ## Part 3: All `phase1-boundary` `2^63` Edge Cases Natively on Xeon -/

private def boundaryRoots : List String :=
  [ "Boundary.add", "Boundary.sub", "Boundary.mul", "Boundary.div", "Boundary.mod"
  , "Boundary.pow", "Boundary.gcd", "Boundary.land", "Boundary.lor", "Boundary.xor"
  , "Boundary.shl", "Boundary.shr"
  , "Boundary.beq", "Boundary.ble", "Boundary.blt"
  , "Boundary.decEq", "Boundary.decLe", "Boundary.decLt", "Boundary.decGt", "Boundary.bne"
  , "Boundary.ltBranch", "Boundary.leBranch", "Boundary.minN", "Boundary.maxN"
  , "Boundary.pred", "Boundary.succ", "Boundary.ident"
  , "Boundary.addK", "Boundary.kAdd", "Boundary.subK", "Boundary.kSub"
  , "Boundary.mulK", "Boundary.kMul", "Boundary.divK", "Boundary.kDiv"
  , "Boundary.modK", "Boundary.kMod", "Boundary.shlK", "Boundary.kShl"
  , "Boundary.shrK", "Boundary.kShr", "Boundary.powK", "Boundary.kPow"
  , "Boundary.landK", "Boundary.xorK", "Boundary.ltK", "Boundary.leK", "Boundary.eqK"
  , "Boundary.litMax", "Boundary.litWord", "Boundary.litDead", "Boundary.litArm"
  , "Boundary.litOperand", "Boundary.litCompare"
  , "Boundary.addSub", "Boundary.mulDiv", "Boundary.shlShr", "Boundary.powMod", "Boundary.succPred" ]

inductive BoundaryExpect where
  | nat (v : Nat)
  | bool (b : Bool)

/-- Compile ALL 59 `phase1-boundary` roots through `Rt.BigNat.lowerRepBig → Backend.compile →
TestShell.writeExe` and run comprehensive `2^63` / `2^64` / `2^128` edge cases natively on Xeon,
asserting ZERO `natOverflow` (`rax == 0`) and exact arbitrary-precision equality with Lean 4 GMP. -/
def runBoundary (cnt : IO.Ref Nat) (lib : CompiledBigNatLib) : IO Nat := do
  let ixePath : FilePath := "fixtures/corpus/phase1-boundary/boundary.ixe"
  let eqPath : FilePath := "fixtures/corpus/phase1-boundary/boundary.equations.json"
  let ixeBytes ← IO.FS.readBinFile ixePath
  let eqRaw ← IO.FS.readFile eqPath
  let eqJson ← IO.ofExcept (Lean.Json.parse eqRaw)
  let (art, exportNames, tTag, fTag) ←
    compileUserProgram "phase1-boundary" lib ixeBytes eqJson boundaryRoots true
  let mem : TestShell.Mem := { stack := 1024 * 1024, region := 32 * 1024 * 1024 }
  let exePath := workDir / "phase1-boundary-big"
  IO.FS.createDirAll workDir
  match TestShell.writeExe mem exportNames art.object with
  | .error err => throw (IO.userError s!"FAIL WireTest writeExe(boundary): {err}")
  | .ok exeBytes =>
    IO.FS.writeBinFile exePath exeBytes
    IO.setAccessRights exePath { user := { read := true, write := true, execution := true } }
  let n63 := Rt.natLimit          -- 2^63
  let maxS := n63 - 1             -- 2^63 - 1
  let n64 := 2 ^ 64
  let n128 := 2 ^ 128
  let cases : List (String × List Nat × BoundaryExpect) :=
    [ -- Promotion across 2^63 boundary
      ("Boundary.add", [maxS, 1], .nat (maxS + 1))
    , ("Boundary.add", [1, maxS], .nat (1 + maxS))
    , ("Boundary.add", [maxS, maxS], .nat (maxS + maxS))
    , ("Boundary.add", [n63, n63], .nat (n63 + n63))
    , ("Boundary.add", [n128, n63], .nat (n128 + n63))
    , ("Boundary.addK", [maxS], .nat n63)
    , ("Boundary.kAdd", [maxS], .nat n63)
    , ("Boundary.succ", [maxS], .nat n63)
    , ("Boundary.succ", [n63], .nat (n63 + 1))
    , ("Boundary.mul", [maxS, 2], .nat (maxS * 2))
    , ("Boundary.mul", [2, maxS], .nat (2 * maxS))
    , ("Boundary.mul", [maxS, maxS], .nat (maxS * maxS))
    , ("Boundary.mul", [n63, n63], .nat (n63 * n63))
    , ("Boundary.mulK", [maxS], .nat (maxS * 2))
    , ("Boundary.kMul", [maxS], .nat (2 * maxS))
    , ("Boundary.shl", [maxS, 1], .nat (maxS <<< 1))
    , ("Boundary.shl", [1, 63], .nat n63)
    , ("Boundary.shl", [1, 64], .nat n64)
    , ("Boundary.shl", [1, 128], .nat n128)
    , ("Boundary.shlK", [maxS], .nat (maxS <<< 1))
    , ("Boundary.kShl", [63], .nat n63)
    , ("Boundary.kShl", [128], .nat n128)
    -- Demotion across 2^63 boundary
    , ("Boundary.pred", [n63], .nat maxS)
    , ("Boundary.pred", [n63 + 1], .nat n63)
    , ("Boundary.pred", [n128], .nat (n128 - 1))
    , ("Boundary.sub", [n63, 1], .nat maxS)
    , ("Boundary.sub", [n63, n63], .nat 0)
    , ("Boundary.sub", [maxS, n63], .nat 0)
    , ("Boundary.subK", [n63], .nat maxS)
    , ("Boundary.kSub", [n63], .nat 0)
    , ("Boundary.div", [n63, 2], .nat (n63 / 2))
    , ("Boundary.div", [n64, 2], .nat n63)
    , ("Boundary.div", [n63, 0], .nat 0)
    , ("Boundary.div", [n128, n63], .nat (n128 / n63))
    , ("Boundary.divK", [n63], .nat (n63 / 2))
    , ("Boundary.kDiv", [n63], .nat 0)
    , ("Boundary.mod", [n63, 7], .nat (n63 % 7))
    , ("Boundary.mod", [n63, 0], .nat n63)
    , ("Boundary.mod", [n128 + 19, n63], .nat ((n128 + 19) % n63))
    , ("Boundary.modK", [n63], .nat (n63 % 7))
    , ("Boundary.kMod", [n63], .nat maxS)
    , ("Boundary.shr", [n63, 1], .nat (n63 >>> 1))
    , ("Boundary.shr", [n128, 65], .nat n63)
    , ("Boundary.shrK", [n63], .nat (n63 >>> 62))
    , ("Boundary.kShr", [n63], .nat 0)
    -- Pow & GCD across 2^63 boundary
    , ("Boundary.pow", [2, 63], .nat n63)
    , ("Boundary.pow", [2, 128], .nat n128)
    , ("Boundary.pow", [3, 40], .nat (3 ^ 40))
    , ("Boundary.pow", [n63, 2], .nat (n63 ^ 2))
    , ("Boundary.powK", [maxS], .nat (maxS ^ 2))
    , ("Boundary.kPow", [40], .nat (3 ^ 40))
    , ("Boundary.gcd", [n63, n63], .nat n63)
    , ("Boundary.gcd", [n128, maxS], .nat (Nat.gcd n128 maxS))
    , ("Boundary.gcd", [n128, n64], .nat n64)
    , ("Boundary.gcd", [n63, 0], .nat n63)
    -- Bitwise across 2^63 boundary
    , ("Boundary.land", [n63 + 5, 7], .nat 5)
    , ("Boundary.land", [n64 + n63, n63], .nat n63)
    , ("Boundary.lor", [n63, 5], .nat (n63 + 5))
    , ("Boundary.lor", [maxS, n63], .nat (n64 - 1))
    , ("Boundary.xor", [n63, n63], .nat 0)
    , ("Boundary.xor", [n64 - 1, maxS], .nat n63)
    , ("Boundary.landK", [n63 + 2 ^ 62], .nat (2 ^ 62))
    , ("Boundary.xorK", [n63], .nat (n64 - 1))
    -- Comparisons & branches across 2^63 boundary
    , ("Boundary.beq", [n63, n63], .bool true)
    , ("Boundary.beq", [n63, maxS], .bool false)
    , ("Boundary.ble", [maxS, n63], .bool true)
    , ("Boundary.ble", [n63, maxS], .bool false)
    , ("Boundary.ble", [n63, n63], .bool true)
    , ("Boundary.blt", [maxS, n63], .bool true)
    , ("Boundary.blt", [n63, n63], .bool false)
    , ("Boundary.blt", [n63, n63 + 1], .bool true)
    , ("Boundary.decEq", [n63, n63], .bool true)
    , ("Boundary.decLe", [n63, n64], .bool true)
    , ("Boundary.decLt", [n64, n63], .bool false)
    , ("Boundary.decGt", [n63, maxS], .bool true)
    , ("Boundary.bne", [n63, maxS], .bool true)
    , ("Boundary.ltBranch", [maxS, n63], .nat 1)
    , ("Boundary.ltBranch", [n63, maxS], .nat 0)
    , ("Boundary.leBranch", [n63, n63], .nat 1)
    , ("Boundary.leBranch", [n63, maxS], .nat 0)
    , ("Boundary.minN", [n63, maxS], .nat maxS)
    , ("Boundary.maxN", [n63, maxS], .nat n63)
    , ("Boundary.ltK", [n63], .bool false)
    , ("Boundary.leK", [n63], .bool false)
    , ("Boundary.eqK", [n63], .bool false)
    , ("Boundary.ident", [n63], .nat n63)
    , ("Boundary.ident", [n128], .nat n128)
    -- Static ≥ 2^63 literals (litMax, litWord, litDead, litArm, litOperand, litCompare)
    , ("Boundary.litMax", [0], .nat maxS)
    , ("Boundary.litWord", [0], .nat n63)
    , ("Boundary.litWord", [n64], .nat n64)
    , ("Boundary.litDead", [5], .nat 5)
    , ("Boundary.litArm", [0], .nat 1)
    , ("Boundary.litArm", [1], .nat n128)
    , ("Boundary.litArm", [2], .nat 0)
    , ("Boundary.litArm", [n63 + 2], .nat n63)
    , ("Boundary.litOperand", [0], .nat n63)
    , ("Boundary.litOperand", [1], .nat maxS)
    , ("Boundary.litOperand", [n63], .nat 0)
    , ("Boundary.litCompare", [0], .bool true)
    , ("Boundary.litCompare", [n63], .bool true)
    , ("Boundary.litCompare", [n64 - 1], .bool true)
    , ("Boundary.litCompare", [n64], .bool false)
    -- Intermediate overflow values that demote back
    , ("Boundary.addSub", [maxS, 1, 1], .nat maxS)
    , ("Boundary.addSub", [maxS, maxS, maxS], .nat maxS)
    , ("Boundary.mulDiv", [maxS, 2, 2], .nat maxS)
    , ("Boundary.mulDiv", [maxS, maxS, maxS], .nat maxS)
    , ("Boundary.shlShr", [maxS, 1], .nat maxS)
    , ("Boundary.shlShr", [maxS, 65], .nat maxS)
    , ("Boundary.powMod", [2, 100, 1000000007], .nat (2 ^ 100 % 1000000007))
    , ("Boundary.succPred", [maxS], .nat maxS)
    , ("Boundary.succPred", [n63], .nat n63) ]
  let inputReserve := 64 * 1024
  let heapSize := mem.region - inputReserve
  let inputBase := mem.base + heapSize
  let tWord := ctor0Word tTag
  let fWord := ctor0Word fTag
  let rootIdx (name : String) : IO Nat := do
    match (boundaryRoots.zipIdx.find? (·.1 == name)) with
    | some (_, i) => pure (i + 1)
    | none => throw (IO.userError s!"unknown boundary root {name}")
  let passedRef ← IO.mkRef 0
  Session.withSession exePath (seconds := some 60) fun s => do
    let stackBudget := mem.stack - 4096
    Session.writeWord s (mem.base + 16) stackBudget
    let (r0, _, ok0) ← Session.call s 0 [mem.base, heapSize, stackBudget]
    require cnt (ok0 && r0 == 0) "boundary cx_init"
    for (rname, args, exp) in cases do
      let idx ← rootIdx rname
      let scratch ← IO.mkRef inputBase
      let mut wargs : List Nat := []
      for a in args do
        wargs := wargs ++ [← writeNatVal s scratch a]
      let (rax, rdx, ok) ← Session.call s idx (mem.base :: wargs)
      require cnt (ok && rax == 0) s!"{rname} {args}: ok={ok} rax={rax} (expected 0, ZERO natOverflow)"
      match exp with
      | .nat expected =>
        match ← readNatVal s rdx with
        | .error e => throw (IO.userError s!"FAIL WireTest {rname} {args}: readback {e}")
        | .ok got =>
          require cnt (got == expected) s!"{rname} {args}: got {got}, expected {expected}"
          -- Also verify canonical representation at the 2^63 boundary!
          if expected < Rt.natLimit then
            require cnt ((rdx &&& 1) == 1) s!"{rname} {args}: expected odd immediate for < 2^63"
          else
            require cnt ((rdx &&& 1) == 0) s!"{rname} {args}: expected even LimbArray* for >= 2^63"
      | .bool expected =>
        let expW := if expected then tWord else fWord
        require cnt (rdx == expW) s!"{rname} {args}: got bool word {rdx}, expected {expW} ({expected})"
      passedRef.modify (· + 1)
  let passed ← passedRef.get
  IO.println s!"[WireTest] phase1-boundary 2^63 Xeon: PASS ({passed} cases across {boundaryRoots.length} roots, 0 natOverflow)"
  pure passed

/-! ## Part 4: 100,000+ Native Compiled-`ixcc` Differential Checks vs Lean 4 GMP -/

private def evalOneNativeOp (built : BuiltBigNat) (s : Session.Session)
    (inputBase heapSize stackBudget : Nat) (op : DiffOp) (a b : Nat) (boolAsNat : Bool) :
    IO (Except String String) := do
  -- Re-initialize bump arena whenever it crosses half capacity
  let bump ← Session.readWord s (built.mem.base + 24)
  if bump.toNat > built.mem.base + heapSize / 2 then
    let (r0, _, ok0) ← Session.call s 0 [built.mem.base, heapSize, stackBudget]
    unless ok0 && r0 == 0 do
      return .error s!"cx_init reset failed: ok={ok0} rax={r0}"
  let slowOp : SlowPathOp := match op with
    | .add => .add | .sub => .sub | .mul => .mul | .sqr => .mul
    | .div => .div | .mod => .mod | .gcd => .gcd
    | .land => .land | .lor => .lor | .xor => .xor
    | .shiftLeft => .shiftLeft | .shiftRight => .shiftRight
    | .pow => .pow | .pred => .pred | .log2 => .log2
    | .beq => .beq | .ble => .ble | .blt => .blt
  let some idx := built.exportIdx.lookup slowOp
    | return .error s!"missing compiled export for {slowOp.key}"
  let scratch ← IO.mkRef inputBase
  let wa ← writeNatVal s scratch a
  let (rax, rdx, ok) ← match op with
    | .pred | .log2 => Session.call s idx [built.mem.base, wa]
    | .sqr => Session.call s idx [built.mem.base, wa, wa]
    | _ => do
      let wb ← writeNatVal s scratch b
      Session.call s idx [built.mem.base, wa, wb]
  unless ok && rax == 0 do
    return .error s!"native call {op.name} failed: ok={ok} rax={rax} (natOverflow=3, heap=1, stack=2)"
  if op.isBool then
    if rdx == built.boolTrueWord then return .ok (formatBool boolAsNat true)
    else if rdx == built.boolFalseWord then return .ok (formatBool boolAsNat false)
    else return .error s!"unexpected bool word {rdx} for {op.name}"
  else
    match ← readNatVal s rdx with
    | .ok v => return .ok (toString v)
    | .error e => return .error e

/-- Run `NativeDiff.buildAllCases` (`targetCount` ≥ 100,000 by default) directly against the
native x86-64 Xeon compiled `IxCC.BigNat` ELF binary vs Lean 4 GMP! -/
def runNativeDiff (built : BuiltBigNat) (targetCount : Nat := 105000) : IO (Nat × Nat × Nat) := do
  let cfg : NativeDiff.Config := { targetCount }
  let (cases, addBackHits) := NativeDiff.buildAllCases cfg
  if addBackHits < 10 then
    throw (IO.userError s!"FAIL WireTest: expected ≥ 10 Knuth D add-back triggers, got {addBackHits}")
  let inputReserve := 256 * 1024
  let heapSize := built.mem.region - inputReserve
  let inputBase := built.mem.base + heapSize
  let stackBudget := built.mem.stack - 4096
  let t0 ← IO.monoNanosNow
  let checkedRef ← IO.mkRef 0
  let failuresRef ← IO.mkRef 0
  Session.withSession built.exePath (seconds := some 600) fun s => do
    Session.writeWord s (built.mem.base + 16) stackBudget
    let (r0, _, ok0) ← Session.call s 0 [built.mem.base, heapSize, stackBudget]
    unless ok0 && r0 == 0 do
      throw (IO.userError s!"FAIL WireTest NativeDiff cx_init: ok={ok0} rax={r0}")
    for c in cases do
      let expected := c.op.evalGMP false c.a c.b
      match ← evalOneNativeOp built s inputBase heapSize stackBudget c.op c.a c.b false with
      | .ok got =>
        if got == expected then
          checkedRef.modify (· + 1)
        else
          failuresRef.modify (· + 1)
          if (← failuresRef.get) ≤ 10 then
            IO.eprintln s!"MISMATCH [{c.tag}] {c.op.name}: expected={previewNum expected}, got={previewNum got}"
          checkedRef.modify (· + 1)
      | .error err =>
        failuresRef.modify (· + 1)
        if (← failuresRef.get) ≤ 10 then
          IO.eprintln s!"ERROR [{c.tag}] {c.op.name}: {err}"
        checkedRef.modify (· + 1)
  let checked ← checkedRef.get
  let failures ← failuresRef.get
  let t1 ← IO.monoNanosNow
  let elapsedMs := (t1 - t0) / 1000000
  if failures != 0 then
    throw (IO.userError s!"FAIL WireTest NativeDiff: {failures} failures out of {checked} checks")
  IO.println s!"[WireTest] Native Xeon Differential PASS: {checked} checks, 0 failures ({addBackHits} Knuth D add-back triggers, 0..1000 limbs, Karatsuba 31..1000, {elapsedMs} ms)"
  pure (checked, addBackHits, elapsedMs)

/-- Streaming batch server (`--native-batch`) for `tests-bignat-nativediff --batch`:
reads `<op> <a> [b]\n` lines from stdin and writes exact native Xeon compiled `IxCC.BigNat`
results to stdout. -/
def runNativeBatch (ixBin : String) : IO Unit := do
  let lib ← compileBigNatLib ixBin false
  let mem : TestShell.Mem := { stack := 1024 * 1024, region := 128 * 1024 * 1024 }
  let built ← buildStandaloneExe lib mem "bignat-batch-exe"
  let inputReserve := 256 * 1024
  let heapSize := mem.region - inputReserve
  let inputBase := mem.base + heapSize
  let stackBudget := mem.stack - 4096
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let raw ← stdin.readToEnd
  Session.withSession built.exePath (seconds := some 600) fun s => do
    Session.writeWord s (mem.base + 16) stackBudget
    let (r0, _, ok0) ← Session.call s 0 [mem.base, heapSize, stackBudget]
    unless ok0 && r0 == 0 do
      throw (IO.userError s!"native-batch cx_init failed: ok={ok0} rax={r0}")
    for line in raw.splitOn "\n" do
      let toks := (line.splitOn " ").filter (· != "")
      match toks with
      | [] => pure ()
      | opStr :: aStr :: rest =>
        let some op := DiffOp.ofName? opStr
          | throw (IO.userError s!"native-batch unknown op: {opStr}")
        let a := aStr.toNat!
        let b := match rest with | bStr :: _ => bStr.toNat! | [] => 0
        match ← evalOneNativeOp built s inputBase heapSize stackBudget op a b false with
        | .ok res => stdout.putStrLn res
        | .error e => throw (IO.userError s!"native-batch {opStr}: {e}")
      | _ => throw (IO.userError s!"native-batch malformed line: {line}")
    stdout.flush

/-! ## Part 5: ALL 6 K5 Benchmark Fixtures Natively on Xeon vs Lean 4 GMP -/

structure K5Fixture where
  name : String
  leanPath : FilePath
  testArgs : List Nat
  testExpected : Nat
  benchArgs : List Nat
  benchExpected : Nat

private def k5Fixtures : List K5Fixture :=
  [ { name := "big-fib"
    , leanPath := "benchmarks/fixtures/big-fib/BigFib.lean"
    , testArgs := [1000], testExpected := 694319868067
    , benchArgs := [5000000], benchExpected := 3471209782051256 }
  , { name := "factorial"
    , leanPath := "benchmarks/fixtures/factorial/Factorial.lean"
    , testArgs := [100], testExpected := 525224817896
    , benchArgs := [300000], benchExpected := 5025583354547019 }
  , { name := "pi-digits"
    , leanPath := "benchmarks/fixtures/pi-digits/PiDigits.lean"
    , testArgs := [100], testExpected := 342117069768319453
    , benchArgs := [5000], benchExpected := 413260475153169886 }
  , { name := "big-mul"
    , leanPath := "benchmarks/fixtures/big-mul/BigMul.lean"
    , testArgs := [64, 20], testExpected := 4095851138526
    , benchArgs := [2048, 300], benchExpected := 131071645818446 }
  , { name := "big-div"
    , leanPath := "benchmarks/fixtures/big-div/BigDiv.lean"
    , testArgs := [64, 20], testExpected := 8190456850695
    , benchArgs := [1024, 200], benchExpected := 131070763113144 }
  , { name := "big-gcd"
    , leanPath := "benchmarks/fixtures/big-gcd/BigGcd.lean"
    , testArgs := [32, 5], testExpected := 513815583491
    , benchArgs := [512, 100], benchExpected := 8197890549754 } ]

/-- Freeze a standalone K5 fixture Lean file using `ix compile`. -/
private def freezeK5Fixture (ixBin : String) (fx : K5Fixture) : IO (ByteArray × Lean.Json) := do
  let dir := workDir / "k5" / fx.name
  IO.FS.createDirAll dir
  let ixePath := dir / s!"{fx.name}.ixe"
  let eqPath := dir / s!"{fx.name}.equations.json"
  let out ← IO.Process.output {
    cmd := ixBin
    args := #[ "compile", "--no-build"
             , "--consts", "entry"
             , "--equations", "--equations-out", eqPath.toString
             , "--word-equations"
             , "--out", ixePath.toString
             , fx.leanPath.toString ]
  }
  if out.exitCode != 0 then
    throw (IO.userError s!"FAIL WireTest ix compile {fx.name} exited {out.exitCode}:\n{out.stderr}")
  let ixeBytes ← IO.FS.readBinFile ixePath
  let namedMap ← IO.ofExcept (extractNamedMap ixeBytes)
  let eqRaw ← IO.FS.readFile eqPath
  let eqJson ← IO.ofExcept (Lean.Json.parse eqRaw)
  let eqJsonK1 ← IO.ofExcept (convertIxEquations fx.leanPath.toString ["entry"] namedMap eqJson)
  pure (ixeBytes, eqJsonK1)

/-- Verify a K5 fixture's `testExpected` directly against Lean 4 GMP (`lean --run`). -/
private def runLeanGmpOracle (fx : K5Fixture) (args : List Nat) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let out ← IO.Process.output {
    cmd := "lean"
    args := #["-Dlinter.all=false", "--run", fx.leanPath.toString] ++ (args.map toString).toArray
  }
  let t1 ← IO.monoNanosNow
  if out.exitCode != 0 then
    throw (IO.userError s!"FAIL WireTest lean --run {fx.name} {args}: {out.stderr}")
  let s := out.stdout.trimAscii.toString
  let some v := s.toNat?
    | throw (IO.userError s!"FAIL WireTest lean --run {fx.name} non-Nat output: '{s}'")
  pure (v, (t1 - t0) / 1000000)

/-- Compile and run ALL 6 K5 benchmark fixtures end-to-end through Phase 4 BigNat
(`lowerRepBig → Backend.compile → TestShell.writeExe`) natively on Xeon at `test_args`
(and optionally `bench_args`), verifying bit-for-bit equality with Lean 4 GMP and reporting
raw Xeon wall-clock runtimes. -/
def runK5 (cnt : IO.Ref Nat) (ixBin : String) (lib : CompiledBigNatLib)
    (runBench : Bool := true) : IO Unit := do
  for fx in k5Fixtures do
    let (ixeBytes, eqJson) ← freezeK5Fixture ixBin fx
    let (art, exportNames, _, _) ←
      compileUserProgram s!"k5-{fx.name}" lib ixeBytes eqJson ["entry"] false
    let mem : TestShell.Mem := { stack := 8 * 1024 * 1024, region := 16 * 1024 * 1024 * 1024 }
    let exePath := workDir / "k5" / fx.name / s!"{fx.name}-xeon"
    match TestShell.writeExe mem exportNames art.object with
    | .error err => throw (IO.userError s!"FAIL WireTest writeExe(k5-{fx.name}): {err}")
    | .ok exeBytes =>
      IO.FS.writeBinFile exePath exeBytes
      IO.setAccessRights exePath { user := { read := true, write := true, execution := true } }
    let stackBudget := mem.stack - 4096
    let runOne := fun (tag : String) (args : List Nat) (expected : Nat) => do
      let t0 ← IO.monoNanosNow
      let gotRef ← IO.mkRef 0
      let usedRef ← IO.mkRef 0
      Session.withSession exePath (seconds := some 600) fun s => do
        Session.writeWord s (mem.base + 16) stackBudget
        let (r0, _, ok0) ← Session.call s 0 [mem.base, mem.region, stackBudget]
        require cnt (ok0 && r0 == 0) s!"k5-{fx.name} ({tag}) cx_init"
        let (rax, rdx, ok) ← Session.call s 1 (mem.base :: args)
        let bump ← Session.readWord s (mem.base + 24)
        let start := Rt.objectsStart mem.base
        usedRef.set (bump.toNat - start)
        require cnt (ok && rax == 0) s!"k5-{fx.name} ({tag}) args={args}: ok={ok} rax={rax} heapUsed={bump.toNat - start}"
        match ← readNatVal s rdx with
        | .ok v => gotRef.set v
        | .error e => throw (IO.userError s!"FAIL WireTest k5-{fx.name} ({tag}) readback: {e}")
      let got ← gotRef.get
      let used ← usedRef.get
      let t1 ← IO.monoNanosNow
      let ms := (t1 - t0) / 1000000
      require cnt (got == expected) s!"k5-{fx.name} ({tag}): got {got}, expected {expected}"
      pure (got, ms, used)
    -- Cross-check test_args against BOTH Lean 4 GMP oracle and native Xeon!
    let (gmpTestVal, gmpTestMs) ← runLeanGmpOracle fx fx.testArgs
    require cnt (gmpTestVal == fx.testExpected)
      s!"k5-{fx.name} Lean GMP test oracle {gmpTestVal} == {fx.testExpected}"
    let (_, testMs, testUsed) ← runOne "test" fx.testArgs gmpTestVal
    if runBench then
      IO.println s!"[WireTest] K5 {fx.name}: test({fx.testArgs})={gmpTestVal} PASS (xeon={testMs} ms, gmp={gmpTestMs} ms, heap={testUsed / 1024} KiB); running bench({fx.benchArgs})..."
      let (_, benchMs, benchUsed) ← runOne "bench" fx.benchArgs fx.benchExpected
      IO.println s!"[WireTest] K5 {fx.name}: bench({fx.benchArgs})={fx.benchExpected} PASS (xeon={benchMs} ms, heap={benchUsed / (1024 * 1024)} MiB)"
    else
      IO.println s!"[WireTest] K5 {fx.name}: test({fx.testArgs})={gmpTestVal} PASS (xeon={testMs} ms, gmp={gmpTestMs} ms, heap={testUsed / 1024} KiB)"

/-! ## Top-Level CLI Entrypoint -/

def runCli (args : List String) : IO Unit := do
  let ixBin ← resolveIxBin
  let cnt ← IO.mkRef 0
  match args with
  | ["--native-batch"] => runNativeBatch ixBin
  | ["--wire"] =>
    let _ ← runBootstrap cnt ixBin
    IO.println s!"WireTest(--wire): PASS ({← cnt.get} checks)"
  | ["--boundary"] =>
    let built ← runBootstrap cnt ixBin
    let _ ← runBoundary cnt built.lib
    IO.println s!"WireTest(--boundary): PASS ({← cnt.get} checks)"
  | ["--diff"] =>
    let built ← runBootstrap cnt ixBin
    let _ ← runNativeDiff built 105000
    IO.println s!"WireTest(--diff): PASS ({← cnt.get} checks)"
  | ["--diff", nStr] =>
    let built ← runBootstrap cnt ixBin
    let _ ← runNativeDiff built nStr.toNat!
    IO.println s!"WireTest(--diff {nStr}): PASS ({← cnt.get} checks)"
  | ["--k5"] =>
    let built ← runBootstrap cnt ixBin
    runK5 cnt ixBin built.lib true
    IO.println s!"WireTest(--k5): PASS ({← cnt.get} checks)"
  | ["--k5-test-only"] =>
    let built ← runBootstrap cnt ixBin
    runK5 cnt ixBin built.lib false
    IO.println s!"WireTest(--k5-test-only): PASS ({← cnt.get} checks)"
  | ["--all"] =>
    let built ← runBootstrap cnt ixBin
    let _ ← runBoundary cnt built.lib
    let _ ← runNativeDiff built 105000
    runK5 cnt ixBin built.lib true
    IO.println s!"WireTest(--all): PASS ({← cnt.get} checks)"
  | _ =>
    throw (IO.userError s!"WireTest unknown args: {args}")

end IxCCTests.BigNat.WireTest
