import IxCC.CompileClaim
import IxCC.X86.Driver
import IxCC.X86.DriverSession
import IxCC.X86.WordRegion
import IxCC.X86.StreamPermissions
import IxCC.X86.StreamSpec
import IxCC.X86.Table.Op
import IxCC.X86.Table.Index

/-!
# Ring-0 Certified-Compilation Admission & Multi-SIP Coexistence (`IxCC.Ring0`)

Executable definitions, instruction-table opcode checks, driver canonicality
checkers, and layout structures for Ring-0 **Software-Isolated Processes (SIPs)**
coexisting in a single shared x86-64 address space.

Proof-heavy frame lemmas, end-to-end admission soundness (`verifyRing0Sip_sound`),
the non-faulting theorem `admittedRing0Sip_call_not_goesWrong` and the conditional
frame theorems (`multi_sip_frame`, `pairwiseDisjointSips_frame`) live in
`IxCC.Ring0.Proof` (`A8-5`).

## Scope and Hardware Adequacy Boundary (`A3-1..A3-9`, `A6-1`, `A6-5`, `A6-9`)

1. **Instruction-Table Privilege Absence & Control-Flow Encoding (`S9`, `A3-4`)**:
   - Every row `o ∈ X86.Op.rows` and every entry in `X86.Table.index` is checked
     at the opcode-descriptor level (`!EncDesc.isPrivilegedOrSystemOpcode (X86.desc o).enc`)
     to exclude privileged, system-control, interrupt, and port-I/O opcodes
     (`0F 00`/`0F 01` `lgdt`/`lidt`/`lmsw`/`swapgs`/`invlpg`, `0F 05`/`0F 07`
     `syscall`/`sysret`, `0F 20`–`0F 23` `mov cr/dr`, `0F 30`–`0F 35`
     `wrmsr`/`rdmsr`, legacy `in`/`out`, `cli`/`sti`, `hlt`, `int`, `iret`).
   - Every control-flow row in `X86.Op.rows` uses direct PC-relative 32-bit
     displacement (`OpEn.D32` for `call`, `jmp`, `jcc`) or `OpEn.ZO` (`ret`),
     with zero indirect branch rows (`jmp r/m64` or `call r/m64`). Note that
     `ret` pops its target from the stack frame; stack-slot integrity is a
     semantic property established by the backend simulation proof (`Recheck.sound`
     / `RcReplay.sound`), not by `Stream.check` alone.

2. **Certified-Compilation Admission & Driver Checking (`S2`, `S4`, `A3-1`, `A3-9`)**:
   - `Ring0Sip.verifyProgram` runs `CompileClaim.verifyProgram` (which replays
     the full compiler certificate via `Recheck.run`, `Recheck.runWithContracts`,
     or `Recheck.RcReplay.run` and checks `elfHash`, `target`, `abiArity`, and
     observable root signatures) AND checks `sip.driver.checkCanonical textSize`
     so `sip.driver.CanonicalOk textSize` is verified executable data, never an
     unverified external hypothesis.
   - `Ring0Sip.verifyBytes` defaults to `typecheck := true` (`Ixon.V3.Tc.checkEnv`).

3. **Hardware Assumptions Outside the Byte Model (`A3-3`, `A3-5`, `A3-6`)**:
   - The `X86.ByteEval` / `X86.ObjectEval` model represents user-visible registers
     and a permission-checked byte memory `D.mapped` with separate instruction
     fetch from `text : ByteArray`. It has no page tables, interrupts, exceptions,
     TLBs, MMIO or speculation. No theorem here takes a hardware premise, so
     carrying a result to physical CPL0 execution relies on these assumptions:
     - page tables map `.text` read-only and executable with no writable alias,
       and data read-write and no-execute;
     - `CR0.WP = 1`, so CPL0 stores cannot write to read-only pages;
     - interrupts, NMI, `#DF` and `#MC` either stay masked during a call or switch
       stacks through the IST, so no frame lands on a SIP stack near its budget;
     - `D.mapped` is ordinary RAM, with no MMIO or DMA control registers;
     - speculative-execution mitigations are the deployment's concern.
   - One `CR3` maps every SIP's data writable, so hardware does not fault on a
     store into a peer the way the model does. Confinement therefore rests on the
     model never faulting: `admittedRing0Sip_call_not_goesWrong` establishes that
     for one call on a source-safe input. It says nothing about an input on which
     the source is stuck, or about state carried between calls.
-/

set_option autoImplicit false

namespace IxCC.X86.Memory

/-- Read a single byte at `addr` from `m` (alias for `m.bytes addr`). -/
@[simp] def readByte (m : Memory) (addr : Word) : UInt8 :=
  m.bytes addr

end IxCC.X86.Memory

namespace IxCC.X86

/-- Classification of the 31 unprivileged user-mode x86-64 mnemonic constructors in `X86.Mnemonic`. -/
inductive MnemonicCategory where
  | alu
  | bitShiftRotate
  | dataMoveAddress
  | conditionalData
  | stackTransfer
  | directControlFlow
  deriving BEq, DecidableEq, Repr, Inhabited

namespace Mnemonic

/-- Classify each `X86.Mnemonic` into its unprivileged computation or control-flow family. -/
def category : Mnemonic → MnemonicCategory
  | .add | .or | .and | .sub | .xor | .cmp | .test
  | .not | .neg | .imul | .mul | .div => .alu
  | .shl | .shr | .sar | .rol | .ror | .bswap => .bitShiftRotate
  | .mov | .movzx | .movsx | .movsxd | .lea => .dataMoveAddress
  | .setcc _ | .cmovcc _ => .conditionalData
  | .push | .pop => .stackTransfer
  | .call | .jmp | .jcc _ | .ret => .directControlFlow

/-- Total classifier witnessing that every constructor of `X86.Mnemonic` belongs
to the unprivileged user-mode vocabulary. Note (`A3-4`): because `X86.Mnemonic`
only defines unprivileged constructors, the substantive opcode-byte privilege
exclusion check is `EncDesc.isPrivilegedOrSystemOpcode` over `(X86.desc o).enc`. -/
def isUnprivileged (m : Mnemonic) : Bool :=
  match m with
  | .add | .or | .and | .sub | .xor | .cmp | .test
  | .not | .neg
  | .shl | .shr | .sar | .rol | .ror
  | .bswap
  | .mov | .movzx | .movsx | .movsxd | .lea | .imul | .mul | .div
  | .setcc _ | .cmovcc _
  | .push | .pop
  | .call | .jmp | .jcc _ | .ret => true

/-- Every constructor in `X86.Mnemonic` satisfies `isUnprivileged`. -/
@[simp] theorem all_unprivileged (m : Mnemonic) : m.isUnprivileged = true := by
  cases m <;> rfl

end Mnemonic

/-- Genuine opcode-byte check (`S9`, `A3-4`, `A6-9`): returns `true` iff the
encoding descriptor `(enc.map, enc.opcode)` matches any x86-64 privileged,
system-control, interrupt, or port-I/O opcode in the Intel SDM:
- Two-byte map (`0F`):
  * `0F 00` / `0F 01`: `SLDT`/`STR`/`LLDT`/`LTR`/`VERR`/`VERW` and
    `SGDT`/`SIDT`/`LGDT`/`LIDT`/`SMSW`/`LMSW`/`INVLPG`/`SWAPGS`
  * `0F 05` / `0F 07`: `SYSCALL` / `SYSRET`
  * `0F 06` / `0F 08` / `0F 09`: `CLTS` / `INVD` / `WBINVD`
  * `0F 20`–`0F 23`: `MOV CRn` / `MOV DRn`
  * `0F 30`–`0F 35`: `WRMSR` / `RDTSC` / `RDMSR` / `RDPMC` / `SYSENTER` / `SYSEXIT`
- Legacy one-byte map:
  * `0x6C`–`0x6F`: `INS` / `OUTS` (string port I/O)
  * `0xE4`–`0xE7` and `0xEC`–`0xEF`: `IN` / `OUT` (port I/O)
  * `0xCC` / `0xCD` / `0xCE` / `0xCF`: `INT3` / `INT imm8` / `INTO` / `IRETQ`
  * `0xF4`: `HLT`
  * `0xFA` / `0xFB`: `CLI` / `STI` -/
def EncDesc.isPrivilegedOrSystemOpcode (enc : EncDesc) : Bool :=
  match enc.map with
  | .x0F =>
    enc.opcode == 0x00 || enc.opcode == 0x01 ||
    enc.opcode == 0x05 || enc.opcode == 0x06 || enc.opcode == 0x07 ||
    enc.opcode == 0x08 || enc.opcode == 0x09 ||
    (0x20 ≤ enc.opcode && enc.opcode ≤ 0x23) ||
    (0x30 ≤ enc.opcode && enc.opcode ≤ 0x35)
  | .legacy =>
    (0x6C ≤ enc.opcode && enc.opcode ≤ 0x6F) ||
    (0xE4 ≤ enc.opcode && enc.opcode ≤ 0xE7) ||
    (0xEC ≤ enc.opcode && enc.opcode ≤ 0xEF) ||
    enc.opcode == 0xCC || enc.opcode == 0xCD || enc.opcode == 0xCE || enc.opcode == 0xCF ||
    enc.opcode == 0xF4 || enc.opcode == 0xFA || enc.opcode == 0xFB

/-- Predicate on an instruction-table row `Op` checking that:
1. Its mnemonic is in the unprivileged vocabulary (`o.mn.isUnprivileged`),
2. Its concrete opcode descriptor `(X86.desc o).enc` is not any x86-64 privileged,
   system, interrupt, or I/O opcode (`!(X86.desc o).enc.isPrivilegedOrSystemOpcode`), and
3. Every control-flow row uses either a direct PC-relative 32-bit immediate
   displacement (`o.form == .D32` for `call`, `jmp`, `jcc`) or zero operands
   (`o.form == .ZO` for `ret`), ruling out all register/memory-indirect jump
   and call rows (`jmp r/m64`, `call r/m64`). -/
def Op.isDirectControlOrData (o : Op) : Bool :=
  o.mn.isUnprivileged &&
  !(X86.desc o).enc.isPrivilegedOrSystemOpcode &&
  match o.mn with
  | .call | .jmp | .jcc _ => o.form == .D32
  | .ret => o.form == .ZO
  | _ => !o.control

namespace Driver

/-- Executable decision procedure for `Driver.Ok textSize` (`A3-9`). -/
def checkOk (D : Driver) (textSize : Nat) : Bool :=
  decide (D.region.toNat % 8 = 0) &&
  decide (4096 ≤ D.size.toNat) &&
  decide (D.region.toNat + D.size.toNat < 2 ^ 63) &&
  decide (D.sp.toNat % 16 = 8) &&
  decide (D.sp.toNat + 8 ≤ 2 ^ 64) &&
  decide (64 ≤ D.budget.toNat) &&
  decide (2 ^ 20 + 64 + D.budget.toNat + 56 ≤ D.sp.toNat) &&
  decide (D.sp.toNat + 8 ≤ D.region.toNat ∨
    D.region.toNat + D.size.toNat + 56 + D.budget.toNat ≤ D.sp.toNat) &&
  decide (textSize ≤ (D.ret - D.base).toNat)

/-- Executable decision procedure for `Driver.CanonicalOk textSize` (`A3-9`). -/
def checkCanonical (D : Driver) (textSize : Nat) : Bool :=
  D.checkOk textSize &&
  decide ((D.base.toNat + textSize ≤ D.region.toNat ∨ D.region.toNat + D.size.toNat ≤ D.base.toNat) ∧
          (D.base.toNat + textSize ≤ D.sp.toNat - 56 - D.budget.toNat ∨ D.sp.toNat + 8 ≤ D.base.toNat)) &&
  decide (D.region.toNat + D.size.toNat + 56 + D.budget.toNat < 2 ^ 47 ∧
          D.sp.toNat + 8 ≤ 2 ^ 47 ∧
          D.base.toNat + textSize < 2 ^ 47) &&
  decide (D.ret.toNat < 2 ^ 47)

theorem checkOk_iff (D : Driver) (textSize : Nat) :
    D.checkOk textSize = true ↔ D.Ok textSize := by
  unfold checkOk
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩

theorem checkCanonical_iff (D : Driver) (textSize : Nat) :
    D.checkCanonical textSize = true ↔ D.CanonicalOk textSize := by
  unfold checkCanonical
  simp only [Bool.and_eq_true, decide_eq_true_eq, checkOk_iff]
  constructor
  · rintro ⟨⟨⟨hok, hta⟩, hb47⟩, hret47⟩
    exact ⟨hok, hta, hb47, hret47⟩
  · rintro ⟨hok, hta, hb47, hret47⟩
    exact ⟨⟨⟨hok, hta⟩, hb47⟩, hret47⟩

end Driver

end IxCC.X86

namespace IxCC.Ring0

open IxCC.Sem (Result Obs Lang)
open IxCC.X86 (Word GPR Width Memory Core Registers Op Mnemonic Arg Slot Implicit)

/-! ## 1. Instruction-Table Opcode Privilege Absence & Control-Flow Encoding -/

set_option maxRecDepth 32768 in
/-- No row in the 243-row x86-64 instruction table `X86.Op.rows` has an opcode
descriptor matching any privileged, system-control, interrupt, or I/O instruction
(`S9`, `A3-4`, `A6-9`). -/
theorem op_rows_no_privileged_opcode :
    X86.Op.rows.all (fun o => !(X86.desc o).enc.isPrivilegedOrSystemOpcode) = true := by
  decide

set_option maxRecDepth 32768 in
/-- Every instruction row in the compiler/decoder table `X86.Op.rows` has a
non-privileged opcode descriptor and uses only direct `D32` or `ZO` control-flow
encodings (no `jmp r/m64` or `call r/m64`). -/
theorem op_rows_direct_control_and_unprivileged :
    X86.Op.rows.all X86.Op.isDirectControlOrData = true := by
  decide

/-- Any row `o ∈ X86.Op.rows` satisfies `isDirectControlOrData`. -/
theorem op_row_isDirectControlOrData {o : X86.Op} (ho : o ∈ X86.Op.rows) :
    o.isDirectControlOrData = true :=
  List.all_eq_true.mp op_rows_direct_control_and_unprivileged o ho

/-- Explicit decomposition of `op_row_isDirectControlOrData`: every row in
`X86.Op.rows` has an unprivileged mnemonic and non-privileged opcode bytes
(`(X86.desc o).enc.isPrivilegedOrSystemOpcode = false`), every `call`/`jmp`/`jcc`
row has encoding form `.D32` (no indirect register/memory target), and every
`ret` row has encoding form `.ZO`. -/
theorem op_row_no_indirect_branch {o : X86.Op} (ho : o ∈ X86.Op.rows) :
    o.mn.isUnprivileged = true ∧
    (X86.desc o).enc.isPrivilegedOrSystemOpcode = false ∧
    ((o.mn = .call ∨ o.mn = .jmp ∨ ∃ c, o.mn = .jcc c) → o.form = .D32) ∧
    (o.mn = .ret → o.form = .ZO) := by
  have h := op_row_isDirectControlOrData ho
  simp only [X86.Op.isDirectControlOrData, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨⟨hmn, hpriv⟩, hform⟩
  refine ⟨hmn, hpriv, ?_, ?_⟩
  · rintro (hcall | hjmp | ⟨c, hjcc⟩)
    · rw [hcall] at hform; exact eq_of_beq hform
    · rw [hjmp] at hform; exact eq_of_beq hform
    · rw [hjcc] at hform; exact eq_of_beq hform
  · intro hret
    rw [hret] at hform; exact eq_of_beq hform

set_option maxRecDepth 32768 in
/-- Every entry in the byte decoder's lookup index `X86.Table.index` comes from
`X86.Op.rows` and therefore satisfies `isDirectControlOrData` (including
non-privileged opcode bytes). -/
theorem table_index_direct_control_and_unprivileged :
    X86.Table.index.all (fun entry => entry.2.isDirectControlOrData) = true := by
  decide

/-- Any instruction `o` returned by the byte decoder's `X86.Table.lookup` is
non-privileged at the opcode level and free of indirect `jmp`/`call` encodings. -/
theorem table_lookup_isDirectControlOrData {k : Nat} {o : X86.Op}
    (hlookup : X86.Table.lookup k = some o) :
    o.isDirectControlOrData = true := by
  unfold X86.Table.lookup at hlookup
  rcases Option.map_eq_some_iff.mp hlookup with ⟨entry, hfind, rfl⟩
  have hmem := List.mem_of_find?_eq_some hfind
  exact List.all_eq_true.mp table_index_direct_control_and_unprivileged entry hmem

/-- Any internal branch/call target validated by `X86.Stream.targets` points to
a valid block index `< program.blocks.size` and decodes at `offset` to the
exact PC-relative `Imm32` displacement of `blockOffset program target.toNat`. -/
theorem stream_targets_valid_block {program : X86.Program} {text : ByteArray}
    {offset : Nat} {op : X86.Imm32 → X86.Decode.Operation} {length : Nat} {target : X86.BlockId}
    (ht : X86.Stream.targets program text offset op length target = true) :
    target.toNat < program.blocks.size ∧
    X86.Decode.decodeAt text offset =
      some ⟨op (X86.Stream.displacement (offset + length) (X86.Stream.blockOffset program target.toNat)), length⟩ := by
  simp only [X86.Stream.targets, X86.Stream.decodes, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ht
  exact ⟨ht.1.1, ht.2⟩

/-- Any fall-through target validated by `X86.Stream.falls` points to a valid
block index `< program.blocks.size` at the exact byte offset `offset`. -/
theorem stream_falls_valid_block {program : X86.Program} {offset : Nat} {target : X86.BlockId}
    (hf : X86.Stream.falls program offset target = true) :
    target.toNat < program.blocks.size ∧ X86.Stream.blockOffset program target.toNat = offset := by
  simp only [X86.Stream.falls, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hf
  exact hf

/-! ## 2. Frame Preservation & Disjoint Region Layout Structures -/

/-- Memory frame preservation: read/write permission maps are unchanged, and
every byte at a non-writable address (`before.writable addr = false`) is
preserved bit-for-bit (`after.bytes addr = before.bytes addr`). -/
structure FramePreserved (before after : Memory) : Prop where
  readable : after.readable = before.readable
  writable : after.writable = before.writable
  unwritable : ∀ addr, before.writable addr = false → after.bytes addr = before.bytes addr

namespace FramePreserved

@[simp] theorem refl (m : Memory) : FramePreserved m m :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

theorem trans {m₁ m₂ m₃ : Memory} (h₁ : FramePreserved m₁ m₂) (h₂ : FramePreserved m₂ m₃) :
    FramePreserved m₁ m₃ where
  readable := h₂.readable.trans h₁.readable
  writable := h₂.writable.trans h₁.writable
  unwritable addr hw := by
    have hw₂ : m₂.writable addr = false := by rw [h₁.writable]; exact hw
    rw [h₂.unwritable addr hw₂, h₁.unwritable addr hw]

theorem readByte_eq {before after : Memory} (h : FramePreserved before after)
    {addr : Word} (hw : before.writable addr = false) :
    after.readByte addr = before.readByte addr :=
  h.unwritable addr hw

theorem permissions {before after : Core} (h : FramePreserved before.memory after.memory) :
    X86.Stream.Permissions before after :=
  ⟨h.readable, h.writable⟩

end FramePreserved

/-- An aligned 64-bit word region (`WordRegion.Layout`) is disjoint from `D.mapped`. -/
def ExternalDisjoint (D : X86.Driver) (layout : X86.WordRegion.Layout) : Prop :=
  ∀ addr, layout.allowed addr = true → D.mapped addr = false

/-- Four aligned 64-bit word regions (`pml4`, `pdpt`, `pd`, `pt`) representing
protected kernel table memory (such as a `CR3` 4-level page-table hierarchy)
disjoint from a SIP's `D.mapped` region (`A3-5`).
Note: `X86.Memory` models permissions directly via `readable`/`writable` maps
rather than walking hardware PTE bits; `KernelRegionLayout.Preserved` proves
that any execution confined to `D.mapped` leaves all bytes and 64-bit slots of
these four regions unchanged. -/
structure KernelRegionLayout where
  cr3  : Word
  pml4 : X86.WordRegion.Layout
  pdpt : X86.WordRegion.Layout
  pd   : X86.WordRegion.Layout
  pt   : X86.WordRegion.Layout
  cr3_eq : cr3 = pml4.base

/-- Backwards-compatible alias for `KernelRegionLayout` (`A3-5`). -/
abbrev KernelPageTables := KernelRegionLayout

namespace KernelRegionLayout

/-- Whether `addr` lies in any of the 4 kernel table regions (`pml4`, `pdpt`, `pd`, `pt`). -/
def inTables (kpt : KernelRegionLayout) (addr : Word) : Bool :=
  kpt.pml4.allowed addr || kpt.pdpt.allowed addr || kpt.pd.allowed addr || kpt.pt.allowed addr

/-- All four kernel table regions are disjoint from `D.mapped`. -/
def DisjointFromDriver (kpt : KernelRegionLayout) (D : X86.Driver) : Prop :=
  ∀ addr, kpt.inTables addr = true → D.mapped addr = false

/-- Every byte and every 64-bit word slot across `pml4`, `pdpt`, `pd`, and `pt`
is preserved bit-for-bit between `before` and `after`. -/
structure Preserved (kpt : KernelRegionLayout) (before after : Word → UInt8) : Prop where
  bytes_eq : ∀ addr, kpt.inTables addr = true → after addr = before addr
  pml4_entries_eq : ∀ slot < kpt.pml4.slots,
    (⟨after, fun _ => true, fun _ => false⟩ : Memory).read64 (kpt.pml4.address slot) =
    (⟨before, fun _ => true, fun _ => false⟩ : Memory).read64 (kpt.pml4.address slot)
  pdpt_entries_eq : ∀ slot < kpt.pdpt.slots,
    (⟨after, fun _ => true, fun _ => false⟩ : Memory).read64 (kpt.pdpt.address slot) =
    (⟨before, fun _ => true, fun _ => false⟩ : Memory).read64 (kpt.pdpt.address slot)
  pd_entries_eq : ∀ slot < kpt.pd.slots,
    (⟨after, fun _ => true, fun _ => false⟩ : Memory).read64 (kpt.pd.address slot) =
    (⟨before, fun _ => true, fun _ => false⟩ : Memory).read64 (kpt.pd.address slot)
  pt_entries_eq : ∀ slot < kpt.pt.slots,
    (⟨after, fun _ => true, fun _ => false⟩ : Memory).read64 (kpt.pt.address slot) =
    (⟨before, fun _ => true, fun _ => false⟩ : Memory).read64 (kpt.pt.address slot)

end KernelRegionLayout

namespace KernelPageTables

export KernelRegionLayout (inTables DisjointFromDriver Preserved)

end KernelPageTables

/-! ## 3. Ring-0 SIP Bundle & Executable Admission Checkers -/

/-- A Ring-0 Software-Isolated Process (SIP) bundle combining compiler configuration,
certified `CompileClaim`, proof certificate text, and Ring-0 `X86.Driver` layout. -/
structure Ring0Sip where
  cfg      : Recheck.Config
  claim    : CompileClaim
  certText : String
  driver   : X86.Driver

namespace Ring0Sip

/-- Extract the verified `.text` byte size from `sip`'s certificate and program,
returning `none` if certificate parsing or replay fails. -/
def verifiedTextSize? (sip : Ring0Sip) (P : Src.Program) : Option Nat :=
  match sip.claim.policy with
  | .immortal =>
    match Recheck.Cert.ofText sip.certText with
    | .ok cert =>
      match Recheck.run sip.cfg P cert with
      | .ok a => some a.backend.encoded.text.size
      | .error _ => none
    | .error _ => none
  | .zeroRc =>
    match Recheck.Cert.ofText sip.certText with
    | .ok cert =>
      match Recheck.runWithContracts sip.cfg P cert with
      | .ok a => some a.backend.encoded.text.size
      | .error _ => none
    | .error _ => none
  | .plainRc =>
    match Recheck.RcReplay.Cert.ofText sip.certText with
    | .ok cert =>
      match Recheck.RcReplay.run sip.cfg P cert with
      | .ok a => some a.backend.encoded.text.size
      | .error _ => none
    | .error _ => none

/-- Verify `sip.claim` against `P` and `sip.certText` in a single certificate
replay pass and return `some a.backend.encoded.text.size` on success, or `none`
on failure (`N11`). -/
def verifyProgramWithTextSize? (sip : Ring0Sip) (P : Src.Program) : Option Nat :=
  if sip.claim.checkWellFormed then
    match P.roots.head? with
    | some (rootAddr, _) =>
      if rootAddr == sip.claim.target then
        match sip.claim.policy with
        | .immortal =>
          match Recheck.Cert.ofText sip.certText with
          | .ok cert =>
            match Recheck.run sip.cfg P cert with
            | .ok a =>
              match a.roots.head? with
              | some root =>
                if CompileClaim.checkImmortalRoot a.src root &&
                    (root.params == sip.claim.abiArity) &&
                    (Ixon.Address.blake3Pure a.object == sip.claim.elfHash) then
                  some a.backend.encoded.text.size
                else none
              | none => none
            | .error _ => none
          | .error _ => none
        | .zeroRc =>
          match Recheck.Cert.ofText sip.certText with
          | .ok cert =>
            match Recheck.runWithContracts sip.cfg P cert with
            | .ok a =>
              match a.roots.head? with
              | some root =>
                if CompileClaim.checkImmortalRoot a.src root &&
                    (Own.Plain.selectRcPolicyForSrc a.src a.front.fir == .zeroRc) &&
                    (root.params == sip.claim.abiArity) &&
                    (Ixon.Address.blake3Pure a.object == sip.claim.elfHash) then
                  some a.backend.encoded.text.size
                else none
              | none => none
            | .error _ => none
          | .error _ => none
        | .plainRc =>
          match Recheck.RcReplay.Cert.ofText sip.certText with
          | .ok cert =>
            match Recheck.RcReplay.run sip.cfg P cert with
            | .ok a =>
              match a.roots.head? with
              | some root =>
                if CompileClaim.checkPlainRcRoot a.front.src root &&
                    (root.params == sip.claim.abiArity) &&
                    (Ixon.Address.blake3Pure a.backend.object == sip.claim.elfHash) then
                  some a.backend.encoded.text.size
                else none
              | none => none
            | .error _ => none
          | .error _ => none
      else none
    | none => none
  else none

/-- Verify a `Ring0Sip`'s compilation claim AND its canonical driver contract
(`sip.driver.checkCanonical textSize`) against an ingested `Src.Program` in a
single certificate replay pass (`A3-9`, `N11`). -/
def verifyProgram (sip : Ring0Sip) (P : Src.Program) : Bool :=
  match sip.verifyProgramWithTextSize? P with
  | some textSize => sip.driver.checkCanonical textSize
  | none => false

/-- Verify a `Ring0Sip`'s compilation claim and canonical driver contract from
raw `.ixe` environment bytes and sidecar equations JSON.
Defaults `typecheck := true` (`S4`, `A3-2`) and enforces canonical relevance (`Stage A`). -/
def verifyBytes (sip : Ring0Sip) (envBytes : ByteArray) (equations : Lean.Json)
    (typecheck : Bool := true) : Bool :=
  match Recheck.ingress envBytes equations
      (CompileClaim.selectTargetRoots sip.cfg equations sip.claim.target) typecheck with
  | .error _ => false
  | .ok input =>
    (input.env.root == sip.claim.env) &&
    CompileClaim.checkCertCanonicalRelevance sip.cfg input sip.claim.policy sip.certText &&
    sip.verifyProgram input.program

end Ring0Sip

/-! ## 4. Multi-SIP Disjointness Predicates -/

/-- Two `X86.Driver` instances have pairwise-disjoint writable mapped regions
(`inRegion` and `inStack`). -/
def DisjointDrivers (D₁ D₂ : X86.Driver) : Prop :=
  ∀ addr, D₁.mapped addr = true → D₂.mapped addr = false

theorem DisjointDrivers.symm {D₁ D₂ : X86.Driver} (h : DisjointDrivers D₁ D₂) :
    DisjointDrivers D₂ D₁ := by
  intro addr h₂
  cases h₁ : D₁.mapped addr with
  | false => rfl
  | true =>
    have := h addr h₁
    rw [this] at h₂
    cases h₂

/-- A driver's mapped region (`inRegion` and `inStack`) is disjoint from a
kernel memory region `kernelRegion : Word → Bool`. -/
def DisjointFromKernel (D : X86.Driver) (kernelRegion : Word → Bool) : Prop :=
  ∀ addr, kernelRegion addr = true → D.mapped addr = false

/-- Two coexisting Ring-0 SIP drivers `D₁` and `D₂` sharing a single address
space alongside a kernel region predicate `kernelPageTables`. -/
structure CoexistingSipPair (D₁ D₂ : X86.Driver) (kernelPageTables : Word → Bool)
    (textSize₁ textSize₂ : Nat) : Prop where
  ok₁      : D₁.CanonicalOk textSize₁
  ok₂      : D₂.CanonicalOk textSize₂
  disjoint : DisjointDrivers D₁ D₂
  kernel₁  : DisjointFromKernel D₁ kernelPageTables
  kernel₂  : DisjointFromKernel D₂ kernelPageTables

/-- Pairwise disjointness for an arbitrary finite family of $N$ Ring-0 SIP drivers
and a kernel memory region `kernelPageTables`. -/
def PairwiseDisjointSips (sips : List X86.Driver) (kernelPageTables : Word → Bool) : Prop :=
  (∀ (i j : Nat) (hi : i < sips.length) (hj : j < sips.length),
    i ≠ j → DisjointDrivers sips[i] sips[j]) ∧
  (∀ d ∈ sips, DisjointFromKernel d kernelPageTables)

end IxCC.Ring0
