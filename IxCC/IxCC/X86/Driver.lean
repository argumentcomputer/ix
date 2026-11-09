import IxCC.X86.ObjectCall

/-!
# The runtime driver's calls, as a model

What `fixtures/x86/runtime_driver.c` sets up for the object's calls (04 §6),
as data and a contract (`Driver.Ok`) on it, so that the object's execution
from an input is a definite function (`X86.Linked`, the object's `Lang`):

- the object's text is loaded at `base`;
- one region of `size` bytes from `region` (the driver's `mmap`); `cx_init`
  gets `rdi = region`, `rsi = size`, `rdx = budget`; a root gets
  `rdi = region` and its arguments in `rsi`…`r9`;
- every call runs with `rsp = sp`, the caller's return address `ret` in the
  word at `sp` (the driver's `call` pushes it), on the stack below it; the
  other registers hold any values (`other`; the wrappers save and restore
  what they use);
- the process's mapping: the region and the call stack (the `budget + 56`
  bytes below `sp` and the return slot) are readable and writable, nothing
  else is. The program cannot change permissions, so each call starts from
  this mapping (`Driver.mem`) with the bytes the previous call left;
- before `cx_init`, the bytes are `init` with the stack budget at
  `region + 16` (`ctx − 48`, where every wrapper reads it, 04 §6);
- Lir's memory (`Driver.lirMem`) is the region from `region + 16`: the
  first 16 bytes (`entrySp`, `stackLimit`) are the wrappers'.

`Driver.Ok` is the contract, in numbers: the region `cx_init` accepts
(8-aligned, at least 4 KiB, below 2^63), a 16-byte-aligned call
(`sp ≡ 8 mod 16`), a budget of at least 64 bytes with room for the largest
frame below the stack (`2^20 + 64 + budget + 56 ≤ sp`), the stack apart
from the region, and the return address outside the text.
-/

namespace IxCC.X86

/-- The driver's setup of the object's calls (see the module note). -/
structure Driver where
  /-- Where the object's text is loaded. -/
  base : Word
  /-- The region's first byte (the driver's `region`). -/
  region : Word
  /-- The region's size, `cx_init`'s second argument. -/
  size : Word
  /-- The stack budget, `cx_init`'s third argument. -/
  budget : Word
  /-- The stack pointer at each call's entry. -/
  sp : Word
  /-- The caller's return address, in the word at `sp`. -/
  ret : Word
  /-- The memory's bytes before the first call. -/
  init : Word → UInt8
  /-- The flags at each call's entry. -/
  flags : ByteEval.Flags
  /-- The caller's other registers at each call's entry. -/
  other : Registers

namespace Driver

variable (D : Driver)

/-- The context pointer the wrappers set (`r15 = region + 64`). -/
def ctx : Word := D.region + 64

/-- The region's bytes. -/
def inRegion (a : Word) : Bool := decide (D.region.toNat ≤ a.toNat) && decide (a.toNat < D.region.toNat + D.size.toNat)

/-- The part of the region Lir uses: from `region + 16`. -/
def inLir (a : Word) : Bool :=
  decide (D.region.toNat + 16 ≤ a.toNat) && decide (a.toNat < D.region.toNat + D.size.toNat)

/-- The call stack: the `budget + 56` bytes below `sp`, and the return slot. -/
def inStack (a : Word) : Bool :=
  decide (D.sp.toNat - 56 - D.budget.toNat ≤ a.toNat) && decide (a.toNat < D.sp.toNat + 8)

/-- The loaded `.text` bytes `[base, base + textSize)`. -/
def inText (textSize : Nat) (a : Word) : Bool :=
  decide (D.base.toNat ≤ a.toNat) && decide (a.toNat < D.base.toNat + textSize)

/-- The process's mapping: the region and the call stack. -/
def mapped (a : Word) : Bool := D.inRegion a || D.inStack a

/-- A call's memory: the given bytes in the process's mapping, with the
return address in the word at `sp`. -/
def mem (bytes : Word → UInt8) : Memory :=
  (⟨bytes, D.mapped, D.mapped⟩ : Memory).write .w64 D.sp D.ret

/-- A call's registers: `rdi` the region, the arguments in `rsi`, `rdx`,
`rcx`, `r8`, `r9` (zero where there are fewer), `rsp` the stack pointer,
the others the caller's (`other`). -/
def regs (args : List Word) : Registers
  | .rdi => D.region
  | .rsp => D.sp
  | .rsi => args.getD 0 0
  | .rdx => args.getD 1 0
  | .rcx => args.getD 2 0
  | .r8 => args.getD 3 0
  | .r9 => args.getD 4 0
  | r => D.other r

/-- A call's machine. -/
def core (args : List Word) (bytes : Word → UInt8) : Core := ⟨D.regs args, D.mem bytes⟩

/-- The bytes before `cx_init`: `init`, with the stack budget at `ctx − 48`. -/
def initBytes : Word → UInt8 :=
  ((⟨D.init, fun _ => true, fun _ => true⟩ : Memory).write .w64 (D.ctx - 48) D.budget).bytes

/-- Lir's memory before `cx_init`: the same bytes, the part of the region
Lir uses readable and writable. -/
def lirMem : Memory := ⟨D.initBytes, D.inLir, D.inLir⟩

/-- A memory as Lir sees it: only the part of the region Lir uses readable
and writable. -/
def lirView (m : Memory) : Memory := ⟨m.bytes, D.inLir, D.inLir⟩

/-- **The driver's contract** (ledgered), for an object whose text has
`textSize` bytes. -/
structure Ok (textSize : Nat) : Prop where
  /-- `cx_init`'s checks: 8-aligned, at least 4 KiB, below 2^63. -/
  aligned : D.region.toNat % 8 = 0
  minSize : 4096 ≤ D.size.toNat
  below : D.region.toNat + D.size.toNat < 2 ^ 63
  /-- A SysV call: `rsp + 8` is 16-aligned, and the return slot fits. -/
  spAlign : D.sp.toNat % 16 = 8
  spTop : D.sp.toNat + 8 ≤ 2 ^ 64
  /-- The stack budget: at least the slack of the largest frameless leaf
  (64 bytes), with room for the largest frame (2^20) below the stack. -/
  budgetMin : 64 ≤ D.budget.toNat
  spLow : 2 ^ 20 + 64 + D.budget.toNat + 56 ≤ D.sp.toNat
  /-- The call stack is apart from the region. -/
  apart : D.sp.toNat + 8 ≤ D.region.toNat ∨ D.region.toNat + D.size.toNat + 56 + D.budget.toNat ≤ D.sp.toNat
  /-- The caller returns outside the text. -/
  retOut : textSize ≤ (D.ret - D.base).toNat

/-- **The canonical user-space driver contract**: extends `Driver.Ok` with
`.text` disjointness from the writable `inRegion` and `inStack` windows (W^X
under unified instruction/data memory) and canonical lower-half user-space
bounds (`< 2 ^ 47`) for the region, call stack, loaded `.text` and caller
return address. -/
structure CanonicalOk (textSize : Nat) : Prop extends D.Ok textSize where
  /-- The loaded `.text` segment `[base, base + textSize)` is disjoint from
  both `inRegion` and `inStack`. -/
  textApart :
    (D.base.toNat + textSize ≤ D.region.toNat ∨ D.region.toNat + D.size.toNat ≤ D.base.toNat) ∧
    (D.base.toNat + textSize ≤ D.sp.toNat - 56 - D.budget.toNat ∨ D.sp.toNat + 8 ≤ D.base.toNat)
  /-- Canonical 48-bit lower-half user-space bounds (`< 2 ^ 47`). -/
  below47 :
    D.region.toNat + D.size.toNat + 56 + D.budget.toNat < 2 ^ 47 ∧
    D.sp.toNat + 8 ≤ 2 ^ 47 ∧
    D.base.toNat + textSize < 2 ^ 47
  /-- The caller return address is in canonical lower-half user space. -/
  retBelow47 : D.ret.toNat < 2 ^ 47

theorem CanonicalOk.text_disjoint_mapped {textSize : Nat} (hD : D.CanonicalOk textSize)
    (a : Word) (ht : D.inText textSize a = true) : D.mapped a = false := by
  have hta := hD.textApart
  simp only [inText, Bool.and_eq_true, decide_eq_true_eq] at ht
  simp only [mapped, inRegion, inStack, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

theorem CanonicalOk.mapped_below47 {textSize : Nat} (hD : D.CanonicalOk textSize)
    (a : Word) (hm : D.mapped a = true) : a.toNat < 2 ^ 47 := by
  have hb := hD.below47
  simp only [mapped, inRegion, inStack, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hm
  omega

theorem CanonicalOk.text_below47 {textSize : Nat} (hD : D.CanonicalOk textSize)
    (a : Word) (ht : D.inText textSize a = true) : a.toNat < 2 ^ 47 := by
  have hb := hD.below47
  simp only [inText, Bool.and_eq_true, decide_eq_true_eq] at ht
  omega

/-- **The canonical user-space contract can be kept**: for any object whose
`.text` fits in 32-bit displacement range (`textSize ≤ 2 ^ 32`), a driver
with `.text` at `0`, a 64 MiB region at `2 ^ 32`, an 8 MiB stack budget,
`rsp = 2 ^ 40 + 8` and caller return address `2 ^ 46` satisfies `CanonicalOk`. -/
theorem exists_canonicalOk {textSize : Nat} (hn : textSize ≤ 2 ^ 32) :
    ∃ D : Driver, D.CanonicalOk textSize := by
  refine ⟨{ base := 0, region := 2 ^ 32, size := 2 ^ 26, budget := 2 ^ 23, sp := 2 ^ 40 + 8,
            ret := 2 ^ 46,
            init := fun _ => 0, flags := {}, other := fun _ => 0 }, ?_⟩
  have hbase : (0 : Word).toNat = 0 := rfl
  have hreg : (2 ^ 32 : Word).toNat = 2 ^ 32 := by decide
  have hsize : (2 ^ 26 : Word).toNat = 2 ^ 26 := by decide
  have hbud : (2 ^ 23 : Word).toNat = 2 ^ 23 := by decide
  have hsp : (2 ^ 40 + 8 : Word).toNat = 2 ^ 40 + 8 := by decide
  have hret : (2 ^ 46 - 0 : Word).toNat = 2 ^ 46 := by decide
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, .inr (by decide), ?_⟩,
    ⟨.inl ?_, .inl ?_⟩, ⟨by decide, by decide, ?_⟩, by decide⟩
  · show textSize ≤ (2 ^ 46 - 0 : Word).toNat
    omega
  · show (0 : Word).toNat + textSize ≤ (2 ^ 32 : Word).toNat
    omega
  · show (0 : Word).toNat + textSize ≤ (2 ^ 40 + 8 : Word).toNat - 56 - (2 ^ 23 : Word).toNat
    omega
  · show (0 : Word).toNat + textSize < 2 ^ 47
    omega

end Driver

end IxCC.X86
