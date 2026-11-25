import IxCC.X86.Exe.Process
import IxCC.X86.Exe.Read
import IxCC.X86.Exe.Cert

/-!
# The process of a shipped file (`IxCCCorrect.Process`)

The existing executable theorems start from `X86.Exe.Process.Loaded c args s`, for
a checked core `c : X86.Exe.Checked f object`: an image the compiler holds, with
its plan. A consumer holds a file. This module restates the loader's post-state
over the bytes of any ELF64 file, read off the file's own headers, and adds the
vocabulary the tiers need that the existing trace specifications do not have:
what a trace wrote to standard output, its exit status, the memory and
system-call envelope, and the three notions termination needs.

The processor and the system calls are the existing specifications, unchanged
(`X86.Exe.Process.Step`, `Syscall`, `Run`, `Trace`).

* `LoadedFile file args s` is `Loaded` with the entry point and the mapped bytes
  taken from `file`'s ELF header and `PT_LOAD` program headers. On a checked
  core it implies `Loaded` (`LoadedFile.toLoaded`, proved in `IxCCCorrect.Today`).
* `execImage file` is what the processor can fetch: the file's first `PT_LOAD`
  to the end of its last page. For a shipped file that is the core and the `int3`
  page tail, and not the certificate payload behind it, which the loader does not
  map.
-/

set_option autoImplicit false

namespace IxCC.Correct

open IxCC.X86
open IxCC.X86.Exe
open IxCC.X86.Exe.Process

/-! ## The loader -/

/-- Outside the memory range of every loadable segment of the file (the initial
stack lies outside the file's mappings: the kernel's mappings do not overlap). -/
def OutsideLoads (programs : List Read.ProgramHeader) (a : Word) : Prop :=
  ∀ ph ∈ programs, ph.kind = 1 → a.toNat < ph.address ∨ ph.address + ph.memorySize ≤ a.toNat

/-- **The loader's post-state for a file** (System V gABI, "Program Loading"; x86-64
psABI §3.4.1), read off the file: `rip` is `e_entry`; each `PT_LOAD` holds the
file's bytes at its offset, at its virtual address; the argument block is at
`rsp`, at canonical user addresses outside the loadable segments. As in
`Process.Loaded`, nothing is assumed of permissions, the other registers, the
flags or the zero fill (`Mapped` adds those, for termination). -/
def LoadedFile (file : ByteArray) (args : List (List Nat)) (s : ByteEval.State) : Prop :=
  ∃ view, Read.parse file = some view ∧
    s.rip = UInt64.ofNat view.header.entry ∧
    (∀ ph ∈ view.programs, ph.kind = 1 → ∀ i < ph.fileSize,
      s.core.memory.bytes (UInt64.ofNat (ph.address + i)) = file[ph.offset + i]!) ∧
    ArgBlock s.core.memory (s.core.readReg .rsp) args
      (fun a => OutsideLoads view.programs a ∧ CanonicalUser a)

/-- **What the loader maps with the access the headers ask for** (needed for
termination only: a store the mapping refuses ends the process). Every byte of a
loadable segment is readable or writable as its flags say (`PF_R` is 4, `PF_W` is
2), a byte past the segment's file size is zero, and the argument block can be
read. -/
def Mapped (file : ByteArray) (args : List (List Nat)) (s : ByteEval.State) : Prop :=
  (∃ view, Read.parse file = some view ∧
    ∀ ph ∈ view.programs, ph.kind = 1 → ∀ i < ph.memorySize,
      (ph.flags / 4 % 2 = 1 → s.core.memory.readable (UInt64.ofNat (ph.address + i)) = true) ∧
      (ph.flags / 2 % 2 = 1 → s.core.memory.writable (UInt64.ofNat (ph.address + i)) = true) ∧
      (ph.fileSize ≤ i → s.core.memory.bytes (UInt64.ofNat (ph.address + i)) = 0)) ∧
  ArgBlock s.core.memory (s.core.readReg .rsp) args (fun a => s.core.memory.readable a = true)

/-- **The bytes the processor can fetch**: the file's first `PT_LOAD` (file offset 0,
mapped at `fileBase`, where `Process.Step` fetches), to the end of its last page.
Linux maps whole pages, so the tail of the last page holds whatever the file has
there. A file whose first program header is not that segment has no executable
image; from its loader state `Process.Step` promises nothing, so no tier holds of
it. -/
def execImage (file : ByteArray) : ByteArray :=
  match Read.parse file with
  | some view =>
    match view.programs[0]? with
    | some ph =>
      if ph.kind = 1 ∧ ph.offset = 0 ∧ ph.address = fileBase then
        file.extract 0 (X86.Exe.alignUp ph.fileSize 0x1000)
      else ByteArray.empty
    | none => ByteArray.empty
  | none => ByteArray.empty

/-- The finite traces of the process of a file, from a state. -/
def FileTrace (file : ByteArray) (s : ByteEval.State) (σ : List Sys) : Prop :=
  Trace (execImage file) s σ

/-- The finite runs of the process of a file. -/
def FileRun (file : ByteArray) (s : ByteEval.State) (σ : List Sys) (s' : ByteEval.State) : Prop :=
  Run (execImage file) s σ s'

/-! ## What a trace shows -/

/-- The bytes of one `write` the platform took: the first `result` of them when the
result is a count, none when it is an error. -/
def accepted (bytes : List UInt8) (result : Word) : List UInt8 :=
  if result.toNat < 2 ^ 63 then bytes.take result.toNat else []

/-- The bytes a trace wrote to file descriptor `fd`, in order. -/
def written (fd : Word) : List Sys → List UInt8
  | [] => []
  | .write fd' bytes result :: σ => (if fd' = fd then accepted bytes result else []) ++ written fd σ
  | _ :: σ => written fd σ

/-- Standard output. -/
def stdout (σ : List Sys) : List UInt8 := written 1 σ

/-- The exit status of a trace whose last system call is `exit`. -/
def exitStatus (σ : List Sys) : Option Word :=
  match σ.getLast? with
  | some (.exit status) => some status
  | _ => none

/-- The environment refused a call: `prctl` or `seccomp` returned nonzero, or a
`write` of at least one byte returned zero or an error. -/
def EnvRefused (σ : List Sys) : Prop :=
  ∃ e ∈ σ, match e with
    | .prctl _ _ result => result ≠ 0
    | .seccomp _ _ _ result => result ≠ 0
    | .write _ bytes result => bytes ≠ [] ∧ (result.toNat = 0 ∨ 2 ^ 63 ≤ result.toNat)
    | _ => False

/-! ## The envelope -/

/-- **The system-call envelope** of the `argvDecimal` convention: the two
confinement calls with the arguments the shell passes, `write` to standard output
or standard error, and `exit`. -/
def SysAllowed : Sys → Prop
  | .prctl option arg2 _ => option = prSetNoNewPrivs ∧ arg2 = 1
  | .seccomp operation flags _ _ => operation = seccompSetModeFilter ∧ flags = 0
  | .write fd _ _ => fd = 1 ∨ fd = 2
  | .exit _ => True
  | .other _ => False

/-- **The writable part of the address space**: the file's zero-filled loadable
segments (the stack and the region). -/
def Writable (file : ByteArray) (a : Word) : Prop :=
  ∃ view, Read.parse file = some view ∧ ∃ ph ∈ view.programs,
    ph.kind = 1 ∧ ph.fileSize = 0 ∧ ph.address ≤ a.toNat ∧ a.toNat < ph.address + ph.memorySize

/-- **The memory envelope**: no byte outside the writable segments has changed since
the loader's state. In particular the mapped file, so the code that runs is the
file's. -/
def Kept (file : ByteArray) (s₀ s : ByteEval.State) : Prop :=
  ∀ a : Word, ¬ Writable file a → s.core.memory.bytes a = s₀.core.memory.bytes a

/-- The bytes at addresses `[lo, hi)` are as the loader left them. -/
def Untouched (lo hi : Nat) (s₀ s : ByteEval.State) : Prop :=
  ∀ a : Word, lo ≤ a.toNat → a.toNat < hi → s.core.memory.bytes a = s₀.core.memory.bytes a

/-! ## Termination -/

/-- `s'` is a successor of `s`. -/
def Next (image : ByteArray) (s' s : ByteEval.State) : Prop := ∃ e, Step image s e (some s')

/-- The process can take a step from `s` (possibly its last). A state with no step
is one where the byte machine faults: the process dies with no system call. -/
def CanStep (image : ByteArray) (s : ByteEval.State) : Prop := ∃ e after, Step image s e after

/-- A trace of a run that ended the process. Every prefix of a trace is a trace
(`Process.Trace`), so only these are maximal. -/
def Ended (image : ByteArray) (s₀ : ByteEval.State) (σ : List Sys) : Prop :=
  ∃ σ₀ s ev, σ = σ₀ ++ [ev] ∧ Run image s₀ σ₀ s ∧ Step image s (some ev) none

end IxCC.Correct
