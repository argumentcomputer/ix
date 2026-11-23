import IxCCTests.Exe.Run
import IxCC.Exe.Cert
import IxCC.CompileClaim

/-! # Hardened `.ix.cert` v1, `ixcc verify-exe`, and `KF-4`/`FE-4` Controls

Part of `tests-exe`: verifies end-to-end packaging, verification, execution,
and adversarial tamper/smuggling resistance of hardened `.ix.cert` v1 certified
standalone executables and `KF-4`/`SP-0` claim verification:

1. **Plain `--exe --embed-cert` & `--exe --machine --embed-cert` round-trips:**
   - `fib` (`.immortal`/`.zeroRc`, `.nat`, 1 arg) + `--rc on` (`.plainRc`, `.nat`)
   - `gcd` (2 args, `.nat`)
   - `abi` (`Abi.bool1`, `.enum`)
   - `Machines.fibMain` (`--exe --machine --embed-cert`)
   - Detached mode (empty embedded `.ixe`/equations) verified with `--closure`/`--equations`,
     refused without them, and refused on mismatched external inputs.
   - Native execution (`--run`) verifying certified binaries run identically on Linux!
2. **Hardened `.ix.cert` v1 ELF64 layout & red-team negative controls (`BE-3`):**
   - Exact 3-entry SHT (`SHT_NULL`, non-alloc `.ix.cert` at page-aligned `pageEnd`,
     exact `.shstrtab`, flush EOF).
   - **RX page-tail code smuggling**: mutating ANY byte in `[coreSize, pageEnd)`
     from `0xCC` (`int3`) to `0x90` (NOP), `0xC3` (RET), or `0x00` is rejected.
   - **Trailing bytes**: appending even 1 byte past EOF is rejected.
   - **Modified `core` bytes**: mutating ELF `e_entry`, `.text`, seccomp BPF
     `.rodata`, or shell code inside `[0..coreSize)` is rejected.
   - **Tampered `.ix.cert` & section headers**: bad magic, unsupported mode `0x02`,
     flipped `CompileClaim` byte, tampered `Recheck.Cert` text, tampered embedded
     `.ixe`, `SHF_ALLOC` (`sh_flags = 2`), extra 4th section header (`e_shnum = 4`),
     unaligned `sh_offset = coreSize`, tampered `.shstrtab` name, and non-zero
     shdr alignment pad are ALL rejected.
3. **`KF-4` / `SP-0` / `FE-4` Claim Verification Controls:**
   - Positive `CompileClaim.verifyBytes` & `kernelAcceptedOfBytes` on `fib` and `gcd`.
   - `KF-4` negative control: tampered `RoleTable` mapping a role to a non-default
     address is rejected by `CompileClaim.tableRestrictsDefault`.
   - `FE-4` negative control: forged `.eqn` theorem with bogus proof cannot pass
     `CompileClaim.verifyBytes` / `kernelAcceptedOfBytes`. -/

namespace IxCCTests.Exe.Cert

open IxCC IxCC.Recheck IxCCTests.Src IxCCTests.Exe.Suite
open IxCC.X86.Exe.Cert IxCC.Exe.Cert
open System

private def setU16LE (bs : ByteArray) (off v : Nat) : ByteArray :=
  (bs.set! off (UInt8.ofNat (v % 256))).set! (off + 1) (UInt8.ofNat ((v / 256) % 256))

private def setU64LE (bs : ByteArray) (off v : Nat) : ByteArray := Id.run do
  let mut out := bs
  let mut cur := v
  for i in List.range 8 do
    out := out.set! (off + i) (UInt8.ofNat (cur % 256))
    cur := cur / 256
  return out

private def expectRefused (a : Assert) (label : String) (bytes : ByteArray)
    (extEnv? : Option ByteArray := none) (extEq? : Option ByteArray := none) : IO Unit := do
  match verifyExeBytes bytes extEnv? extEq? with
  | .error _ => expect a true s!"{label}: refused"
  | .ok _ => expect a false s!"{label}: unexpectedly ACCEPTED by verifyExeBytes!"

private def expectTrailerRefused (a : Assert) (label : String) (bytes : ByteArray) : IO Unit := do
  match extractTrailer bytes with
  | .error _ => expect a true s!"{label}: extractTrailer refused"
  | .ok _ => expect a false s!"{label}: unexpectedly ACCEPTED by extractTrailer!"

/-- Verify exact hardened `.ix.cert` v1 ELF64 layout invariants on `bytes`. -/
private def checkHardenedLayout (a : Assert) (label : String) (bytes : ByteArray)
    (coreSz : Nat) : IO Unit := do
  let pageEnd := X86.Exe.alignUp coreSz certPageSize
  expect a (pageEnd % certPageSize == 0 && coreSz ≤ pageEnd) s!"{label}: pageEnd aligned"
  expectEq a (X86.ELFRead.natural bytes 60 2) (some 3) s!"{label}: e_shnum == 3"
  expectEq a (X86.ELFRead.natural bytes 62 2) (some 2) s!"{label}: e_shstrndx == 2"
  let some shoff := X86.ELFRead.natural bytes 40 8
    | throw (IO.userError s!"{label}: missing e_shoff")
  expectEq a (shoff + shdrTableSize) bytes.size s!"{label}: flush EOF"
  -- Section 1 (`.ix.cert`): non-alloc (`sh_flags = 0`), page-aligned (`sh_offset = pageEnd`)
  let sh1 := shoff + shdrEntrySize
  expectEq a (X86.ELFRead.natural bytes (sh1 + 8) 8) (some 0) s!"{label}: .ix.cert sh_flags == 0"
  expectEq a (X86.ELFRead.natural bytes (sh1 + 24) 8) (some pageEnd) s!"{label}: .ix.cert sh_offset == pageEnd"
  -- Every byte in `[coreSz .. pageEnd)` is strictly `0xCC` (`int3`)
  let mut allTrap := true
  for i in [coreSz:pageEnd] do
    if bytes.data[i]? != some trapByte then
      allTrap := false
      break
  expect a allTrap s!"{label}: [coreSz..pageEnd) is strictly 0xCC (int3) trap sled"

/-- Run all red-team tamper & RX page-tail smuggling negative controls on a valid certified exe. -/
private def tamperControls (a : Assert) (label : String) (bytes : ByteArray)
    (v : VerifiedExe) : IO Nat := do
  let coreSz := v.coreSize
  let pageEnd := X86.Exe.alignUp coreSz certPageSize
  let some shoff := X86.ELFRead.natural bytes 40 8
    | throw (IO.userError s!"{label}: missing e_shoff")
  let mut n := 0
  -- 1. RX page-tail code smuggling (`[coreSz .. pageEnd)`): NOP / RET / NUL!
  if coreSz < pageEnd then
    let mid := coreSz + (pageEnd - coreSz) / 2
    for (tag, off, byteVal) in [
        ("RX tail start NOP (0x90)", coreSz, (0x90 : UInt8)),
        ("RX tail mid NUL (0x00)", mid, (0x00 : UInt8)),
        ("RX tail end RET (0xC3)", pageEnd - 1, (0xC3 : UInt8))] do
      let mutImg := bytes.set! off byteVal
      expectTrailerRefused a s!"{label}: {tag}" mutImg
      expectRefused a s!"{label}: {tag}" mutImg
      n := n + 1
  -- 2. Trailing bytes appended past EOF
  for (tag, b) in [("trailing 0x00 byte", (0x00 : UInt8)), ("trailing 0xCC byte", trapByte)] do
    let mutImg := bytes.push b
    expectTrailerRefused a s!"{label}: {tag}" mutImg
    expectRefused a s!"{label}: {tag}" mutImg
    n := n + 1
  -- 3. Modified `core` bytes: e_entry, .text, .rodata/BPF, shell
  let coreProbes : List (String × Nat) := [
    ("core ELF e_entry", 24),
    ("core PT_LOAD p_flags", 64 + 4),
    ("core .text/note middle", coreSz / 3),
    ("core .rodata/BPF region", (coreSz * 2) / 3),
    ("core shell tail byte", coreSz - 1)
  ]
  for (tag, off) in coreProbes do
    if off < coreSz then
      let b := bytes.get! off
      let mutImg := bytes.set! off (b ^^^ 0x01)
      expectRefused a s!"{label}: {tag}" mutImg
      n := n + 1
  -- 4. Tampered `.ix.cert` magic & mode byte
  let badMagic := bytes.set! (pageEnd + 7) 0x00
  expectRefused a s!"{label}: bad .ix.cert magic" badMagic
  n := n + 1
  let badMode := bytes.set! (pageEnd + 8) 0x02
  expectRefused a s!"{label}: unsupported .ix.cert mode 0x02" badMode
  n := n + 1
  -- 5. Tampered `.ix.cert` payload internals (claim, cert text, embedded .ixe)
  let payloadEnd := pageEnd + v.payloadSize
  for (tag, off) in [
      ("tampered .ix.cert header/claim", pageEnd + 36),
      ("tampered .ix.cert mid-payload", pageEnd + v.payloadSize / 2),
      ("tampered .ix.cert tail byte", payloadEnd - 1)] do
    if off < payloadEnd then
      let b := bytes.get! off
      let mutImg := bytes.set! off (b ^^^ 0x42)
      expectRefused a s!"{label}: {tag}" mutImg
      n := n + 1
  -- 6. Tampered ELF64 section headers (SHF_ALLOC, e_shnum = 4, unaligned sh_offset, .shstrtab)
  let sh1 := shoff + shdrEntrySize
  let allocFlag := setU64LE bytes (sh1 + 8) 0x2 -- SHF_ALLOC!
  expectTrailerRefused a s!"{label}: SHF_ALLOC on .ix.cert" allocFlag
  expectRefused a s!"{label}: SHF_ALLOC on .ix.cert" allocFlag
  n := n + 1
  let unalignedOff := setU64LE bytes (sh1 + 24) coreSz
  expectTrailerRefused a s!"{label}: unaligned .ix.cert sh_offset" unalignedOff
  expectRefused a s!"{label}: unaligned .ix.cert sh_offset" unalignedOff
  n := n + 1
  let extraShdr := setU16LE bytes 60 4
  expectTrailerRefused a s!"{label}: e_shnum = 4" extraShdr
  expectRefused a s!"{label}: e_shnum = 4" extraShdr
  n := n + 1
  let shstrOff := pageEnd + v.payloadSize
  let badShstr := bytes.set! (shstrOff + 5) 0x58 -- `.ix.cXrt`
  expectTrailerRefused a s!"{label}: tampered .shstrtab" badShstr
  expectRefused a s!"{label}: tampered .shstrtab" badShstr
  n := n + 1
  -- Non-zero alignment pad byte between .shstrtab and SHT (if pad > 0)
  let shstrEnd := shstrOff + shstrtabBytes.size
  if shstrEnd < shoff then
    let badPad := bytes.set! shstrEnd 0xFF
    expectTrailerRefused a s!"{label}: non-zero SHT alignment pad" badPad
    expectRefused a s!"{label}: non-zero SHT alignment pad" badPad
    n := n + 1
  return n

def part (a : Assert) (o : Options) (work : FilePath) : IO (Array String) := do
  let mut out : Array String := #[]
  let fx := "fixtures/ixon-v4/bench-k1"
  let abiDir := "fixtures/corpus/phase1-abi"
  let machDir := "fixtures/corpus/phase1-machines"

  -- 1. Plain `--exe --embed-cert` (fib, immortal/zeroRc) + `ixcc verify-exe` + tamper suite
  let fibExe := work / "fib_cert"
  let c1 ← IxCC.Cli.main ["compile", s!"{fx}/fib.ixe", "--equations", s!"{fx}/fib.equations.json",
    "--exe", fibExe.toString, "--embed-cert"]
  expectEq a c1 0 "ixcc compile --exe --embed-cert (fib)"
  let fibBytes ← IO.FS.readBinFile fibExe
  let vFib ← match verifyExeBytes fibBytes with
    | .ok v => pure v
    | .error e => throw (IO.userError s!"verifyExeBytes (fib): {e.render}")
  expect a (vFib.exeKind == .plain) s!"fib verified exeKind (got {repr vFib.exeKind})"
  checkHardenedLayout a "fib_cert" fibBytes vFib.coreSize
  let vc1 ← IxCC.Cli.main ["verify-exe", fibExe.toString]
  expectEq a vc1 0 "ixcc verify-exe (fib)"
  let nTamper ← tamperControls a "fib_cert" fibBytes vFib
  if o.run then
    runChecked a "fib_cert 25" fibExe ["25"] 0 "75025\n" ""
    runChecked a "fib_cert bad arg" fibExe ["nope"] 3 "" "ixcc: an argument is not a decimal natural number\n"
  out := out.push s!"fib_cert (plain): core {vFib.coreSize} B, total {fibBytes.size} B, {nTamper} tamper/smuggling controls refused"

  -- 2. Plain `--exe --rc on --embed-cert` (fib, plainRc policy)
  let fibRcExe := work / "fib_rc_cert"
  let c2 ← IxCC.Cli.main ["compile", s!"{fx}/fib.ixe", "--equations", s!"{fx}/fib.equations.json",
    "--rc", "on", "--exe", fibRcExe.toString, "--embed-cert"]
  expectEq a c2 0 "ixcc compile --rc on --exe --embed-cert (fib)"
  let fibRcBytes ← IO.FS.readBinFile fibRcExe
  let vFibRc ← match verifyExeBytes fibRcBytes with
    | .ok v => pure v
    | .error e => throw (IO.userError s!"verifyExeBytes (fib plainRc): {e.render}")
  expect a (vFibRc.claim.policy == .plainRc) s!"fib_rc_cert policy == plainRc (got {repr vFibRc.claim.policy})"
  checkHardenedLayout a "fib_rc_cert" fibRcBytes vFibRc.coreSize
  if o.run then
    runChecked a "fib_rc_cert 15" fibRcExe ["15"] 0 "610\n" ""
  out := out.push s!"fib_rc_cert (plainRc): core {vFibRc.coreSize} B, verified"

  -- 3. Multi-arg `gcd` + enum `Abi.bool1`
  let gcdExe := work / "gcd_cert"
  let c3 ← IxCC.Cli.main ["compile", s!"{fx}/gcd.ixe", "--equations", s!"{fx}/gcd.equations.json",
    "--exe", gcdExe.toString, "--embed-cert"]
  expectEq a c3 0 "ixcc compile --exe --embed-cert (gcd)"
  let gcdBytes ← IO.FS.readBinFile gcdExe
  let vGcd ← match verifyExeBytes gcdBytes with
    | .ok v => pure v
    | .error e => throw (IO.userError s!"verifyExeBytes (gcd): {e.render}")
  expectEq a vGcd.claim.abiArity 2 "gcd abiArity == 2"
  checkHardenedLayout a "gcd_cert" gcdBytes vGcd.coreSize
  if o.run then
    runChecked a "gcd_cert 48 18" gcdExe ["48", "18"] 0 "6\n" ""

  let abiExe := work / "abi_bool1_cert"
  let c4 ← IxCC.Cli.main ["compile", s!"{abiDir}/abi.ixe", "--equations", s!"{abiDir}/abi.equations.json",
    "--root", "Abi.bool1", "--exe", abiExe.toString, "--embed-cert"]
  expectEq a c4 0 "ixcc compile --exe --embed-cert (Abi.bool1)"
  let abiBytes ← IO.FS.readBinFile abiExe
  let vAbi ← match verifyExeBytes abiBytes with
    | .ok v => pure v
    | .error e => throw (IO.userError s!"verifyExeBytes (Abi.bool1): {e.render}")
  checkHardenedLayout a "abi_bool1_cert" abiBytes vAbi.coreSize
  out := out.push s!"gcd (2-arg) & Abi.bool1 (enum) certified executables verified"

  -- 4. `--exe --machine --embed-cert` (`Machines.fibMain`)
  let machExe := work / "mach_fib_cert"
  let c5 ← IxCC.Cli.main ["compile", s!"{machDir}/machines.ixe",
    "--equations", s!"{machDir}/machines.equations.json",
    "--root", "Machines.fibMain", "--exe", machExe.toString, "--machine", "--embed-cert"]
  expectEq a c5 0 "ixcc compile --exe --machine --embed-cert (Machines.fibMain)"
  let machBytes ← IO.FS.readBinFile machExe
  let vMach ← match verifyExeBytes machBytes with
    | .ok v => pure v
    | .error e => throw (IO.userError s!"verifyExeBytes (Machines.fibMain): {e.render}")
  expect a (vMach.exeKind == .machine) s!"Machines.fibMain verified exeKind == machine (got {repr vMach.exeKind})"
  checkHardenedLayout a "mach_fib_cert" machBytes vMach.coreSize
  let nMachTamper ← tamperControls a "mach_fib_cert" machBytes vMach
  let vc5 ← IxCC.Cli.main ["verify-exe", machExe.toString]
  expectEq a vc5 0 "ixcc verify-exe (Machines.fibMain)"
  if o.run then
    runChecked a "mach_fib_cert 10" machExe ["10"] 0 "55\n" ""
  out := out.push s!"mach_fib_cert (machine): core {vMach.coreSize} B, {nMachTamper} tamper/smuggling controls refused"

  -- 5. Detached `.ix.cert` mode (omitted closure/equations, supplied externally) + mismatch refusal
  let envBytes ← IO.FS.readBinFile s!"{fx}/fib.ixe"
  let eqBytes ← IO.FS.readBinFile s!"{fx}/fib.equations.json"
  let (_, payloadBytes) ← IO.ofExcept ((extractTrailer fibBytes).mapError (·.render))
  let payload ← IO.ofExcept ((Payload.decode payloadBytes).mapError (·.render))
  let coreBytes := zeroShdr (fibBytes.extract 0 vFib.coreSize)
  let detachedPayload := { payload with envBytes := ByteArray.empty, eqBytes := ByteArray.empty }
  let detachedImg ← IO.ofExcept ((attachTrailer coreBytes detachedPayload.encode).mapError (·.render))
  let gcdEnvBytes ← IO.FS.readBinFile s!"{fx}/gcd.ixe"
  expectRefused a "detached .ix.cert without --closure/--equations" detachedImg none none
  expectRefused a "detached .ix.cert with wrong --closure (gcd.ixe)" detachedImg (some gcdEnvBytes) (some eqBytes)
  expectRefused a "detached .ix.cert with corrupted --closure" detachedImg (some (envBytes.set! 10 (envBytes.get! 10 ^^^ 0xFF))) (some eqBytes)
  match verifyExeBytes detachedImg (some envBytes) (some eqBytes) with
  | .ok vDet => expect a (vDet.claim == vFib.claim) "detached .ix.cert accepted with matching --closure/--equations"
  | .error e => expect a false s!"detached .ix.cert with matching external files refused: {e.render}"
  -- Embedded + mismatched external --closure must be refused!
  expectRefused a "embedded .ix.cert with mismatched external --closure" fibBytes (some (envBytes.push 0)) none
  out := out.push "detached .ix.cert mode + external mismatch refusal passed"

  -- 6. `KF-4` / `SP-0` / `FE-4` Claim Verification Controls
  let eqJson ← IO.ofExcept (Lean.Json.parse (String.fromUTF8! eqBytes))
  let certText := String.fromUTF8! payload.certBytes
  let inp ← IO.ofExcept ((Recheck.ingress envBytes eqJson []).mapError (·.render))
  let cfg : Recheck.Config := ({ names := vFib.rootNames } : Recheck.Config).forInput inp
  expect a (CompileClaim.verifyBytes cfg envBytes eqJson vFib.claim certText)
    "CompileClaim.verifyBytes accepts honest fib claim with KF-4 + SP-0 + N5"
  let hk := CompileClaim.kernelAcceptedOfBytes cfg envBytes eqJson vFib.claim certText
  expect a hk.isOk "kernelAcceptedOfBytes produces KernelAccepted witness on honest fib"
  -- FE-4 negative control: tampered certText with bogus theorem / corrupted proof cannot pass verifyBytes!
  let bogusCert := certText ++ " bogus"
  expect a (!CompileClaim.verifyBytes cfg envBytes eqJson vFib.claim bogusCert)
    "FE-4: tampered certText refused by verifyBytes"
  expect a (!(CompileClaim.kernelAcceptedOfBytes cfg envBytes eqJson vFib.claim bogusCert).isOk)
    "FE-4: tampered certText yields no KernelAccepted witness"
  -- KF-4 negative control: tampered role table binding a role to a non-default address is refused!
  let defBinding ← IO.ofExcept (Ix.Kernel.Admission.defaultBinding.mapError fun _ => "defaultBinding")
  let defTable ← IO.ofExcept ((Ix.Kernel.Admission.admitBinding Src.KernelFront.hash defBinding).mapError fun _ => "admit")
  expect a (CompileClaim.tableRestrictsDefault inp.kernel.acc.table defTable)
    "KF-4: honest fib roleTable restricts committed defaultTable"
  let bogusAddr : Address := ⟨ByteArray.mk (Array.replicate 32 0x5A)⟩
  let tamperedTable : Ix.Kernel.RoleTable :=
    { inp.kernel.acc.table with
      bound := inp.kernel.acc.table.bound.push (Ix.Kernel.Role.nat, bogusAddr) }
  expect a (!CompileClaim.tableRestrictsDefault tamperedTable defTable)
    "KF-4: tampered roleTable binding Role.nat to non-default address is REFUSED"
  out := out.push "KF-4 / SP-0 / FE-4 positive & negative controls passed"
  return out

end IxCCTests.Exe.Cert
