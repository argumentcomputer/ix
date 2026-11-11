import IxCC.X86.Driver

/-!
# The standalone executable's memory layout, and the driver contract it gives

A standalone executable is one static ELF file mapped at `fileBase` (read and
execute: the headers, the object's text, the shell's read-only data and the
shell), and one zero-filled segment at `dataBase` (read and write) that no
file bytes back. The zero-filled segment holds the program stack at its
bottom, `[dataBase, dataBase + stack)`, and the region above it,
`[dataBase + stack, dataBase + stack + region)`. Nothing below `dataBase`
down to the end of the file is mapped, so a stack that ran past its bottom
would fault rather than reach other memory. The loader sets all of this up;
the shell makes no system call for memory.

**What the shell is meant to establish** (the instance of `X86.Driver` that
`Layout.driver` builds): the object's text at `fileBase + textOffset`; the
region at `regionStart` of `region` bytes; the stack budget `stack − 4096`
(as `fixtures/x86/runtime_driver.c` passes it), stored by the shell at
`region + 16` before `cx_init`; each call entered with `rsp = stackTop − 8`
(the shell sets `rsp` to `stackTop`, 16-aligned, and `call` pushes the
return address); the region's bytes before `cx_init` are the loader's zeros
with that one word stored (`init` is zero, and `Driver.initBytes` adds the
budget). `driver_canonicalOk` proves that for every layout `check` accepts,
the arithmetic clauses of the contract (`Driver.Ok` and the canonical
user-space extension `Driver.CanonicalOk`) hold, whatever the return address
as long as it lies after the object's text and below the zero-filled segment,
which is where the shell's call sites are. That the shell's code realises
this driver (that it really enters each call in `Driver.core`'s state and
does not touch the region between the calls) is not proved here; the shell is
trusted code (`docs/trusted-extern-ledger.md`).

**Where the model and a real caller differ.** `X86.Linked` runs `cx_init`
and the root from one `Driver`, so with one return address `ret`, one flags
value and one register file `other` for both calls. A real caller does not
behave that way: the shell calls `cx_init` and the root from two call sites
(so two return addresses, `driver` at each), and enters them with different
caller-saved registers; `runtime_driver.c` also enters them with different
`rax` (its trampoline calls through `rax`). The object's theorems hold for
every return address and register file, so this costs nothing semantically,
but the model states one where a caller supplies two. The model is left as it
is; a proof that the shell realises the contract will have to take one
`Driver` per call.
-/

namespace IxCC.X86.Exe

/-- Where the file is mapped. -/
def fileBase : Nat := 0x400000

/-- Where the zero-filled segment (the stack, then the region) starts. -/
def dataBase : Nat := 0x10000000

/-- The part of the stack the budget leaves for the export wrapper's frame and
the largest frameless leaf's slack, as the C driver leaves it. -/
def stackReserve : Nat := 4096

/-- The largest stack plus region the writer accepts (1 TiB), which keeps every
address below `2^47`. -/
def maxDataBytes : Nat := 2 ^ 40

/-- The sizes of the stack and the region, in bytes. The defaults are the C
driver's. -/
structure Layout where
  stack : Nat := 8 * 2 ^ 20
  region : Nat := 64 * 2 ^ 20
  deriving BEq, Repr, Inhabited

namespace Layout

def stackTop (L : Layout) : Nat := dataBase + L.stack
def regionStart (L : Layout) : Nat := dataBase + L.stack
def budget (L : Layout) : Nat := L.stack - stackReserve
def dataSize (L : Layout) : Nat := L.stack + L.region

/-- The sizes the writer accepts: a stack that is a multiple of 16 and at least
8 KiB (as the C driver requires), a region of at least `cx_init`'s 4 KiB, and
together at most `maxDataBytes`. -/
def check (L : Layout) : Bool :=
  L.stack % 16 == 0 && decide (8192 ≤ L.stack) && decide (4096 ≤ L.region) &&
    decide (L.stack + L.region ≤ maxDataBytes)

/-- The driver the shell gives a call whose return address is `ret`, for
object text at file offset `textOffset`. -/
def driver (L : Layout) (textOffset ret : Nat) : Driver where
  base := UInt64.ofNat (fileBase + textOffset)
  region := UInt64.ofNat L.regionStart
  size := UInt64.ofNat L.region
  budget := UInt64.ofNat L.budget
  sp := UInt64.ofNat (L.stackTop - 8)
  ret := UInt64.ofNat ret
  init := fun _ => 0
  flags := {}
  other := fun _ => 0

private theorem toNat_small {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n :=
  UInt64.toNat_ofNat_of_lt' (by show n < 18446744073709551616; omega)

/-- **The layout keeps the driver contract**: for a layout `check` accepts,
object text below the return address and a return address below the
zero-filled segment, the driver satisfies every clause of
`Driver.CanonicalOk`. -/
theorem driver_canonicalOk (L : Layout) (hL : L.check = true) {textOffset textSize ret : Nat}
    (hText : fileBase + textOffset + textSize ≤ ret) (hRet : ret < dataBase) :
    (L.driver textOffset ret).CanonicalOk textSize := by
  simp only [check, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hL
  obtain ⟨⟨⟨h16, hs⟩, hr⟩, hmax⟩ := hL
  simp only [maxDataBytes] at hmax
  have hd : dataBase = 268435456 := rfl
  have hf : fileBase = 4194304 := rfl
  have hbase : (UInt64.ofNat (fileBase + textOffset)).toNat = fileBase + textOffset :=
    toNat_small (by omega)
  have hreg : (UInt64.ofNat (dataBase + L.stack)).toNat = dataBase + L.stack := toNat_small (by omega)
  have hsize : (UInt64.ofNat L.region).toNat = L.region := toNat_small (by omega)
  have hbud : (UInt64.ofNat (L.stack - 4096)).toNat = L.stack - 4096 := toNat_small (by omega)
  have hsp : (UInt64.ofNat (dataBase + L.stack - 8)).toNat = dataBase + L.stack - 8 :=
    toNat_small (by omega)
  have hret : (UInt64.ofNat ret).toNat = ret := toNat_small (by omega)
  have hsub : (UInt64.ofNat ret - UInt64.ofNat (fileBase + textOffset)).toNat =
      ret - (fileBase + textOffset) := by
    rw [UInt64.toNat_sub_of_le]
    · rw [hret, hbase]
    · rw [UInt64.le_iff_toNat_le, hret, hbase]; omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩ <;>
    simp only [driver, regionStart, stackTop, budget, stackReserve, hbase, hreg, hsize, hbud, hsp,
      hret, hsub] <;>
    omega

/-- The default layout (an 8 MiB stack and a 64 MiB region) is accepted. -/
theorem default_check : ({} : Layout).check = true := by decide

end Layout

end IxCC.X86.Exe
