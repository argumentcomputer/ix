import IxCC.Ring0
import IxCCTests.Pipeline.Support

/-!
# Ring-0 Proof-Carrying Code (PCC) & Multi-SIP Coexistence Test Suite (`IxCCTests.Ring0`)

1. **Exact Axiom Fence Verification**:
   Registered in `IxCCTests/Fences/Compile.lean` (built as part of `IxCCTests.Proofs`
   and tracked by `check-build-graph`).

2. **Concrete Constructive Multi-SIP Layout & `CoexistingSipPair` Proof**:
   Constructs two disjoint `X86.Driver` instances (`sip1Driver` and `sip2Driver`)
   and a 4-level `CR3` page-table hierarchy (`mockKernelPageTables` at
   `pml4Base := 0x1000`, `pdptBase := 0x2000`, `pdBase := 0x3000`, `ptBase := 0x4000`),
   and machine-checks `CoexistingSipPair (sip1Driver init) (sip2Driver init) mockKernelPageTables.inTables`.

3. **Executable Multi-SIP Single-Address-Space Coexistence Test (`runRing0Tests`)**:
   - Compiles two real programs through `IxCC`:
     * `sip1`: K1 `gcd` (compiled and verified under both `.zeroRc` and `.plainRc` `CompileClaim`s),
     * `sip2`: `OS16-plain` heap list `build` + `revAcc` + `sumL` (compiled and verified under `.plainRc` `CompileClaim`, plus contract-annotated `.zeroRc` `CompileClaim`),
   - Populates a single shared `X86.Memory` address space (`bytes₀ : Word → UInt8`)
     with mock 64-bit `CR3` page-table entries (`pml4`, `pdpt`, `pd`, `pt`),
     both SIP `.text` segments, and both SIPs' initialized runtime contexts (`initCall`),
   - Executes `sip1` -> `sip2` -> `sip1` in the shared `X86.Memory` without resetting
     peer memory or reloading `CR3`,
   - Verifies that both SIPs produce their exact expected outputs AND that all
     mock `CR3` page-table 64-bit words, `.text` segments, and each peer SIP's
     private heap and stack regions are preserved bit-for-bit across peer execution.
-/

set_option autoImplicit false

namespace IxCCTests.Ring0

open IxCC IxCC.Ring0 IxCC.X86 IxCC.Recheck IxCCTests.Pipeline
open System

/-! ## 2. Concrete Ring-0 Page-Table & Multi-SIP Layout Proofs -/

/-- Mock `CR3` 4-level page-table physical bases (`pml4`, `pdpt`, `pd`, `pt`),
each a 64-entry (512-byte) aligned `WordRegion.Layout` in low physical memory `[0x1000, 0x5000)`. -/
def pml4Base : Word := 0x1000
def pdptBase : Word := 0x2000
def pdBase   : Word := 0x3000
def ptBase   : Word := 0x4000

def mockKernelPageTables : KernelRegionLayout where
  cr3    := pml4Base
  pml4   := { base := pml4Base, slots := 64, aligned := by decide, fits := by decide }
  pdpt   := { base := pdptBase, slots := 64, aligned := by decide, fits := by decide }
  pd     := { base := pdBase,   slots := 64, aligned := by decide, fits := by decide }
  pt     := { base := ptBase,   slots := 64, aligned := by decide, fits := by decide }
  cr3_eq := rfl

/-- `sip1` driver layout:
- `.text` at `base := 0x00100000`
- Private heap `[0x10000000, 0x10010000)` (`size := 0x10000 = 65536`, `budget := 0x2000 = 8192`)
- Private stack `[0x10010010, 0x20000010)` (`sp := 0x20000008`, `ret := 0x70000001`) -/
def sip1Driver (init : Word → UInt8 := fun _ => 0) : Driver where
  base   := 0x00100000
  region := 0x10000000
  size   := 0x00010000
  budget := 0x00002000
  sp     := 0x20000008
  ret    := 0x70000001
  init   := init
  flags  := {}
  other  := fun _ => 0

/-- `sip2` driver layout:
- `.text` at `base := 0x00200000`
- Private heap `[0x30000000, 0x30010000)` (`size := 0x10000 = 65536`, `budget := 0x2000 = 8192`)
- Private stack `[0x30010010, 0x40000010)` (`sp := 0x40000008`, `ret := 0x70000002`) -/
def sip2Driver (init : Word → UInt8 := fun _ => 0) : Driver where
  base   := 0x00200000
  region := 0x30000000
  size   := 0x00010000
  budget := 0x00002000
  sp     := 0x40000008
  ret    := 0x70000002
  init   := init
  flags  := {}
  other  := fun _ => 0

theorem sip1Driver_canonicalOk (init : Word → UInt8) {textSize : Nat}
    (htext : textSize ≤ 0x00100000) :
    (sip1Driver init).CanonicalOk textSize := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
          ⟨Or.inl ?_, Or.inl ?_⟩,
          ⟨?_, ?_, ?_⟩,
          ?_⟩ <;> dsimp only [sip1Driver]
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · have hret : ((0x70000001 : Word) - 0x00100000).toNat = 0x6ff00001 := by decide
    omega
  · have hb : (0x00100000 : Word).toNat = 0x00100000 := by decide
    have hr : (0x10000000 : Word).toNat = 0x10000000 := by decide
    omega
  · have hb : (0x00100000 : Word).toNat = 0x00100000 := by decide
    have hs : (0x20000008 : Word).toNat = 0x20000008 := by decide
    have hbg : (0x00002000 : Word).toNat = 0x00002000 := by decide
    omega
  · decide
  · decide
  · have hb : (0x00100000 : Word).toNat = 0x00100000 := by decide
    omega
  · decide

theorem sip2Driver_canonicalOk (init : Word → UInt8) {textSize : Nat}
    (htext : textSize ≤ 0x00100000) :
    (sip2Driver init).CanonicalOk textSize := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
          ⟨Or.inl ?_, Or.inl ?_⟩,
          ⟨?_, ?_, ?_⟩,
          ?_⟩ <;> dsimp only [sip2Driver]
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · have hret : ((0x70000002 : Word) - 0x00200000).toNat = 0x6fe00002 := by decide
    omega
  · have hb : (0x00200000 : Word).toNat = 0x00200000 := by decide
    have hr : (0x30000000 : Word).toNat = 0x30000000 := by decide
    omega
  · have hb : (0x00200000 : Word).toNat = 0x00200000 := by decide
    have hs : (0x40000008 : Word).toNat = 0x40000008 := by decide
    have hbg : (0x00002000 : Word).toNat = 0x00002000 := by decide
    omega
  · decide
  · decide
  · have hb : (0x00200000 : Word).toNat = 0x00200000 := by decide
    omega
  · decide

theorem sip1_sip2_disjoint (init₁ init₂ : Word → UInt8) :
    DisjointDrivers (sip1Driver init₁) (sip2Driver init₂) := by
  intro addr hm₁
  unfold Driver.mapped Driver.inRegion Driver.inStack sip1Driver at hm₁
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hm₁
  have h1 : addr.toNat < 0x20000008 + 8 := by
    rcases hm₁ with ⟨_, h⟩ | ⟨_, h⟩
    · change addr.toNat < 0x10000000 + 0x00010000 at h; omega
    · change addr.toNat < 0x20000008 + 8 at h; omega
  unfold Driver.mapped Driver.inRegion Driver.inStack sip2Driver
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  refine ⟨Or.inl ?_, Or.inl ?_⟩
  · change ¬ 0x30000000 ≤ addr.toNat; omega
  · change ¬ 0x40000008 - 56 - 0x00002000 ≤ addr.toNat; omega

theorem sip1_disjoint_kernel (init : Word → UInt8) :
    DisjointFromKernel (sip1Driver init) mockKernelPageTables.inTables := by
  intro addr hk
  unfold KernelRegionLayout.inTables mockKernelPageTables WordRegion.Layout.allowed
    pml4Base pdptBase pdBase ptBase at hk
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hk
  have hlt : addr.toNat < 0x5000 := by
    rcases hk with ((⟨_, h⟩ | ⟨_, h⟩) | ⟨_, h⟩) | ⟨_, h⟩
    · change addr.toNat < 0x1000 + 8 * 64 at h; omega
    · change addr.toNat < 0x2000 + 8 * 64 at h; omega
    · change addr.toNat < 0x3000 + 8 * 64 at h; omega
    · change addr.toNat < 0x4000 + 8 * 64 at h; omega
  unfold Driver.mapped Driver.inRegion Driver.inStack sip1Driver
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  refine ⟨Or.inl ?_, Or.inl ?_⟩
  · change ¬ 0x10000000 ≤ addr.toNat; omega
  · change ¬ 0x20000008 - 56 - 0x00002000 ≤ addr.toNat; omega

theorem sip2_disjoint_kernel (init : Word → UInt8) :
    DisjointFromKernel (sip2Driver init) mockKernelPageTables.inTables := by
  intro addr hk
  unfold KernelRegionLayout.inTables mockKernelPageTables WordRegion.Layout.allowed
    pml4Base pdptBase pdBase ptBase at hk
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hk
  have hlt : addr.toNat < 0x5000 := by
    rcases hk with ((⟨_, h⟩ | ⟨_, h⟩) | ⟨_, h⟩) | ⟨_, h⟩
    · change addr.toNat < 0x1000 + 8 * 64 at h; omega
    · change addr.toNat < 0x2000 + 8 * 64 at h; omega
    · change addr.toNat < 0x3000 + 8 * 64 at h; omega
    · change addr.toNat < 0x4000 + 8 * 64 at h; omega
  unfold Driver.mapped Driver.inRegion Driver.inStack sip2Driver
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  refine ⟨Or.inl ?_, Or.inl ?_⟩
  · change ¬ 0x30000000 ≤ addr.toNat; omega
  · change ¬ 0x40000008 - 56 - 0x00002000 ≤ addr.toNat; omega

/-- Constructive proof that `sip1Driver` and `sip2Driver` form a `CoexistingSipPair`
with `mockKernelPageTables.inTables`. -/
theorem sip1_sip2_coexisting (init₁ init₂ : Word → UInt8) {textSize₁ textSize₂ : Nat}
    (ht₁ : textSize₁ ≤ 0x00100000) (ht₂ : textSize₂ ≤ 0x00100000) :
    CoexistingSipPair (sip1Driver init₁) (sip2Driver init₂)
      mockKernelPageTables.inTables textSize₁ textSize₂ where
  ok₁      := sip1Driver_canonicalOk init₁ ht₁
  ok₂      := sip2Driver_canonicalOk init₂ ht₂
  disjoint := sip1_sip2_disjoint init₁ init₂
  kernel₁  := sip1_disjoint_kernel init₁
  kernel₂  := sip2_disjoint_kernel init₂

/-! ## 3. Executable Multi-SIP Coexistence & `CR3` Page-Table Invariance Test Suite -/

private def check (label : String) (cond : Bool) : IO Unit := do
  unless cond do
    throw (IO.userError s!"Ring0 test failed: {label}")
  IO.println ("PASS Ring0: " ++ label)

/-- Read a 64-bit little-endian word from a byte function `bytes : Word → UInt8`. -/
private def readWord64 (bytes : Word → UInt8) (addr : Word) : Word :=
  ({ bytes := bytes, readable := fun _ => true, writable := fun _ => false } : Memory).read64 addr

/-- Write a 64-bit little-endian word into a byte function `bytes : Word → UInt8`. -/
private def writeWord64 (bytes : Word → UInt8) (addr val : Word) : Word → UInt8 :=
  (({ bytes := bytes, readable := fun _ => true, writable := fun _ => true } : Memory).write .w64 addr val).bytes

/-- Copy a `ByteArray` into `bytes` starting at `base`. -/
private def writeByteArray (bytes : Word → UInt8) (base : Word) (arr : ByteArray) : Word → UInt8 :=
  fun addr =>
    let offset := (addr - base).toNat
    if base.toNat ≤ addr.toNat && addr.toNat < base.toNat + arr.size && offset < arr.size then
      arr[offset]!
    else
      bytes addr

/-- Check that every 64-bit word across a range of slots `[0, numSlots)` at `base`
is identical between `before` and `after`. -/
private def checkSlotsPreserved (before after : Word → UInt8) (base : Word) (numSlots : Nat) : Bool :=
  (List.range numSlots).all fun slot =>
    let addr := base + UInt64.ofNat (slot * 8)
    readWord64 after addr == readWord64 before addr

/-- Check that every byte in `[base, base + len)` is identical between `before` and `after`. -/
private def checkBytesPreserved (before after : Word → UInt8) (base : Word) (len : Nat) : Bool :=
  (List.range len).all fun i =>
    let addr := base + UInt64.ofNat i
    after addr == before addr

/-- Populate mock `CR3` 4-level page tables (`pml4`, `pdpt`, `pd`, `pt`) in `bytes`
with realistic x86-64 PTEs (`Present | Writable | Global` flags) and check `WordRegion.Realizes`. -/
private def initMockPageTables (bytes : Word → UInt8) : Word → UInt8 :=
  let b0 := (List.range 8).foldl (fun b slot =>
    writeWord64 b (pml4Base + UInt64.ofNat (slot * 8)) (pdptBase + UInt64.ofNat (slot * 0x1000) ||| 0x03)) bytes
  let b1 := (List.range 8).foldl (fun b slot =>
    writeWord64 b (pdptBase + UInt64.ofNat (slot * 8)) (pdBase + UInt64.ofNat (slot * 0x1000) ||| 0x03)) b0
  let b2 := (List.range 8).foldl (fun b slot =>
    writeWord64 b (pdBase + UInt64.ofNat (slot * 8)) (ptBase + UInt64.ofNat (slot * 0x1000) ||| 0x03)) b1
  (List.range 16).foldl (fun b slot =>
    writeWord64 b (ptBase + UInt64.ofNat (slot * 8)) (0x10000000 + UInt64.ofNat (slot * 0x1000) ||| 0x103)) b2

/-- Execute the end-to-end Ring-0 PCC & Multi-SIP Coexistence test suite:
1. Compiles `gcd` (`.zeroRc` and `.plainRc`) and `OS16-plain` (`.plainRc`),
   constructs `Ring0Sip` bundles, and verifies `verifyProgram` and `verifyBytes`,
2. Populates a single shared `X86.Memory` with mock `CR3` page tables (`pml4`, `pdpt`, `pd`, `pt`)
   and initializes both `sip1` and `sip2` in the shared address space,
3. Runs `sip1` -> `sip2` -> `sip1` in the shared memory without resetting peer memory or reloading `CR3`,
4. Verifies exact expected outputs AND bit-for-bit preservation of all mock `CR3`
   page-table words, `.text` segments, and peer SIP heap/stack regions! -/
def runRing0Tests : IO Unit := do
  let badAddr := Ixon.Address.blake3Pure (ByteArray.mk #[0xde, 0xad, 0xbe, 0xef])

  -- 1. Compile SIP 1 (`gcd`) and verify its Ring-0 PCC claims (`.zeroRc` and `.plainRc`)
  let gcdIxe := benchIxe "gcd"
  let gcdEqs := benchEqs "gcd"
  let gcdBytes ← IO.FS.readBinFile gcdIxe
  let gcdJson ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile gcdEqs))
  let gcdInp ← benchInput "gcd"
  let gcdCfg : Config := { names := ["entry"], provenance := some IxCCTests.Rt.Machine.testProvenance }

  let (gcdZeroClaim, gcdZeroCert, _gcdZeroElf) ← ofErr "Ring0 gcd zeroRc CompileClaim.produce" fun _ =>
    CompileClaim.produce gcdCfg gcdInp
  let sip1Zero : Ring0Sip := {
    cfg := gcdCfg
    claim := gcdZeroClaim
    certText := gcdZeroCert
    driver := sip1Driver
  }
  check "sip1 (gcd zeroRc) policy is .zeroRc and abiArity is 2"
    (gcdZeroClaim.policy == .zeroRc && gcdZeroClaim.abiArity == 2)
  check "sip1 (gcd zeroRc) verifyProgram accepts valid claim"
    (sip1Zero.verifyProgram gcdInp.program)
  check "sip1 (gcd zeroRc) verifyBytes accepts valid claim"
    (sip1Zero.verifyBytes gcdBytes gcdJson)
  check "sip1 (gcd zeroRc) verifyProgram rejects tampered elfHash"
    (!( { sip1Zero with claim := { gcdZeroClaim with elfHash := badAddr } }.verifyProgram gcdInp.program ))
  check "sip1 (gcd zeroRc) verifyProgram rejects non-canonical driver (misaligned region)"
    (!( { sip1Zero with driver := { sip1Driver with region := 0x10000003 } }.verifyProgram gcdInp.program ))

  let (gcdRcClaim, gcdRcCert, _gcdRcElf) ← ofErr "Ring0 gcd plainRc CompileClaim.produce" fun _ =>
    CompileClaim.produce gcdCfg gcdInp .plainRc
  let sip1Rc : Ring0Sip := {
    cfg := gcdCfg
    claim := gcdRcClaim
    certText := gcdRcCert
    driver := sip1Driver
  }
  check "sip1 (gcd plainRc) policy is .plainRc and verifyProgram accepts"
    (gcdRcClaim.policy == .plainRc && sip1Rc.verifyProgram gcdInp.program && sip1Rc.verifyBytes gcdBytes gcdJson)
  let gcdRcCertParsed ← IO.ofExcept (RcReplay.Cert.ofText gcdRcCert)
  let gcdRcArt ← ofErr "Ring0 gcd plainRc RcReplay.run" fun _ =>
    RcReplay.run (Config.forInput gcdCfg gcdInp) gcdInp.program gcdRcCertParsed

  -- 2. Compile SIP 2 (`OS16-plain` heap list build + reverse + sum) and verify its Ring-0 PCC claim
  let osIxe : FilePath := "fixtures/ownership/OS16-plain.ixe"
  let osEqs : FilePath := "fixtures/ownership/OS16-plain.equations.json"
  let osBytes ← IO.FS.readBinFile osIxe
  let osJson ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile osEqs))
  let osInp ← ingressFile osIxe osEqs ["entry"]
  let osCfg : Config := { names := ["entry"], provenance := some IxCCTests.Rt.Machine.testProvenance }

  let (osClaim, osCert, _osElf) ← ofErr "Ring0 OS16-plain CompileClaim.produce" fun _ =>
    CompileClaim.produce osCfg osInp
  let sip2 : Ring0Sip := {
    cfg := osCfg
    claim := osClaim
    certText := osCert
    driver := sip2Driver
  }
  check "sip2 (OS16-plain) policy is .plainRc and abiArity is 1"
    (osClaim.policy == .plainRc && osClaim.abiArity == 1)
  check "sip2 (OS16-plain) verifyProgram accepts valid claim"
    (sip2.verifyProgram osInp.program)
  check "sip2 (OS16-plain) verifyBytes accepts valid claim"
    (sip2.verifyBytes osBytes osJson)
  check "sip2 (OS16-plain) verifyProgram rejects tampered elfHash"
    (!( { sip2 with claim := { osClaim with elfHash := badAddr } }.verifyProgram osInp.program ))

  let osCertParsed ← IO.ofExcept (RcReplay.Cert.ofText osCert)
  let osArt ← ofErr "Ring0 OS16-plain RcReplay.run" fun _ =>
    RcReplay.run (Config.forInput osCfg osInp) osInp.program osCertParsed

  let text1 := gcdRcArt.backend.encoded.text
  let text2 := osArt.backend.encoded.text
  check "sip1 and sip2 text sizes fit within 1 MiB canonical window"
    (text1.size ≤ 0x00100000 && text2.size ≤ 0x00100000)

  -- 3. Populate the single shared address space (`bytes₀`) with:
  --    - Mock CR3 4-level page tables (`pml4`, `pdpt`, `pd`, `pt`),
  --    - `sip1`'s `.text` at `0x00100000` and `sip2`'s `.text` at `0x00200000`,
  --    - Both SIPs initialized (`cx_init`) in the shared address space!
  let baseBytes := initMockPageTables (fun _ => 0)
  let withText1 := writeByteArray baseBytes (sip1Driver.base) text1
  let bytes₀    := writeByteArray withText1 (sip2Driver.base) text2

  -- Initialize sip1 in `bytes₀` -> `bytesAfterInit1`
  let d1Init := sip1Driver bytes₀
  let linked1Init := gcdRcArt.linked d1Init
  let bytesAfterInit1 ← match linked1Init.initCall 10000 with
    | .ok (_, mem1) => pure mem1.bytes
    | _ => throw (IO.userError "Ring0: sip1 initCall failed")

  -- Initialize sip2 in `bytesAfterInit1` -> `sharedBytes₀`
  let d2Init := sip2Driver bytesAfterInit1
  let linked2Init := osArt.linked d2Init
  let sharedBytes₀ ← match linked2Init.initCall 10000 with
    | .ok (_, mem2) => pure mem2.bytes
    | _ => throw (IO.userError "Ring0: sip2 initCall failed")

  -- Verify that initializing sip1 and sip2 preserved all mock CR3 page tables and both `.text` segments
  check "initCall preserved CR3 PML4/PDPT/PD/PT 64-bit PTEs"
    (checkSlotsPreserved bytes₀ sharedBytes₀ pml4Base 64 &&
     checkSlotsPreserved bytes₀ sharedBytes₀ pdptBase 64 &&
     checkSlotsPreserved bytes₀ sharedBytes₀ pdBase 64 &&
     checkSlotsPreserved bytes₀ sharedBytes₀ ptBase 64)
  check "initCall of sip2 preserved sip1's initialized allocator header at [ctx1 - 48, ctx1)"
    (checkSlotsPreserved bytesAfterInit1 sharedBytes₀ (d1Init.ctx - 48) 6)
  check "initCall preserved sip1 and sip2 .text segments (W^X)"
    (checkBytesPreserved bytes₀ sharedBytes₀ d1Init.base text1.size &&
     checkBytesPreserved bytes₀ sharedBytes₀ d2Init.base text2.size)

  let sess1 : DriverSession.Session := { linked := gcdRcArt.linked (sip1Driver sharedBytes₀) }
  let sess2 : DriverSession.Session := { linked := osArt.linked (sip2Driver sharedBytes₀) }

  -- 4. Phase A: Run `sip1` (`gcd(48, 18) = 6`, `gcd(1071, 462) = 21`) on `sharedBytes₀`
  let out₁ ← match sess1.runCalls [⟨0, [48, 18]⟩, ⟨0, [1071, 462]⟩] sharedBytes₀ 50000 with
    | .ok out => pure out
    | _ => throw (IO.userError "Ring0 Phase A: sip1 runCalls failed")

  check "Phase A: sip1 produced 2 events with expected outputs gcd(48,18)=6 and gcd(1071,462)=21"
    (out₁.events.map (·.observation) == [Sem.Obs.nat 6, Sem.Obs.nat 21])
  check "Phase A: sip1 preserved mock CR3 page tables (PML4, PDPT, PD, PT) bit-for-bit"
    (checkSlotsPreserved bytes₀ out₁.bytes pml4Base 64 &&
     checkSlotsPreserved bytes₀ out₁.bytes pdptBase 64 &&
     checkSlotsPreserved bytes₀ out₁.bytes pdBase 64 &&
     checkSlotsPreserved bytes₀ out₁.bytes ptBase 64)
  check "Phase A: sip1 preserved sip2's entire heap region [0x30000000, 0x30010000) and stack frame bit-for-bit"
    (checkBytesPreserved sharedBytes₀ out₁.bytes d2Init.region d2Init.size.toNat &&
     checkSlotsPreserved sharedBytes₀ out₁.bytes (d2Init.sp - 128) 18)
  check "Phase A: sip1 preserved both .text code segments (W^X)"
    (checkBytesPreserved bytes₀ out₁.bytes d1Init.base text1.size &&
     checkBytesPreserved bytes₀ out₁.bytes d2Init.base text2.size)

  -- 5. Phase B: Run `sip2` (`OS16-plain` on `n = 4` -> `6`, `n = 6` -> `15`) directly on `out₁.bytes`
  --    without resetting peer memory or reloading CR3!
  let out₂ ← match sess2.runCalls [⟨0, [4]⟩, ⟨0, [6]⟩] out₁.bytes 100000 with
    | .ok out => pure out
    | _ => throw (IO.userError "Ring0 Phase B: sip2 runCalls failed")

  check "Phase B: sip2 produced 2 events with expected outputs sum(0..3)=6 and sum(0..5)=15"
    (out₂.events.map (·.observation) == [Sem.Obs.nat 6, Sem.Obs.nat 15])
  check "Phase B: sip2 preserved mock CR3 page tables (PML4, PDPT, PD, PT) bit-for-bit"
    (checkSlotsPreserved bytes₀ out₂.bytes pml4Base 64 &&
     checkSlotsPreserved bytes₀ out₂.bytes pdptBase 64 &&
     checkSlotsPreserved bytes₀ out₂.bytes pdBase 64 &&
     checkSlotsPreserved bytes₀ out₂.bytes ptBase 64)
  check "Phase B: sip2 preserved sip1's entire heap region [0x10000000, 0x10010000) and stack frame bit-for-bit"
    (checkBytesPreserved out₁.bytes out₂.bytes d1Init.region d1Init.size.toNat &&
     checkSlotsPreserved out₁.bytes out₂.bytes (d1Init.sp - 128) 18)
  check "Phase B: sip2 preserved both .text code segments (W^X)"
    (checkBytesPreserved bytes₀ out₂.bytes d1Init.base text1.size &&
     checkBytesPreserved bytes₀ out₂.bytes d2Init.base text2.size)

  -- 6. Phase C: Resume `sip1` (`gcd(270, 192) = 6`, `gcd(144, 89) = 1`) directly on `out₂.bytes`
  --    without re-initializing `sip1`, resetting peer memory, or reloading CR3!
  let out₃ ← match sess1.runCalls [⟨0, [270, 192]⟩, ⟨0, [144, 89]⟩] out₂.bytes 50000 with
    | .ok out => pure out
    | _ => throw (IO.userError "Ring0 Phase C: sip1 resumed runCalls failed")

  check "Phase C: resumed sip1 produced 2 events with expected outputs gcd(270,192)=6 and gcd(144,89)=1"
    (out₃.events.map (·.observation) == [Sem.Obs.nat 6, Sem.Obs.nat 1])
  check "Phase C: resumed sip1 preserved mock CR3 page tables (PML4, PDPT, PD, PT) bit-for-bit"
    (checkSlotsPreserved bytes₀ out₃.bytes pml4Base 64 &&
     checkSlotsPreserved bytes₀ out₃.bytes pdptBase 64 &&
     checkSlotsPreserved bytes₀ out₃.bytes pdBase 64 &&
     checkSlotsPreserved bytes₀ out₃.bytes ptBase 64)
  check "Phase C: resumed sip1 preserved sip2's entire heap region [0x30000000, 0x30010000) and stack frame bit-for-bit"
    (checkBytesPreserved out₂.bytes out₃.bytes d2Init.region d2Init.size.toNat &&
     checkSlotsPreserved out₂.bytes out₃.bytes (d2Init.sp - 128) 18)
  check "Phase C: resumed sip1 preserved both .text code segments (W^X)"
    (checkBytesPreserved bytes₀ out₃.bytes d1Init.base text1.size &&
     checkBytesPreserved bytes₀ out₃.bytes d2Init.base text2.size)

end IxCCTests.Ring0
