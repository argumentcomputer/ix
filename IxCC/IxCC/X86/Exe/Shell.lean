import IxCC.X86.Encode

/-!
# Platform code: the program instructions, the system call, calls of exports

A standalone executable runs a compiled object under a small piece of
platform code, its *shell*, which IxCC writes as typed x86 like the
compiler's own output. The shell needs two things the program instruction
table deliberately lacks:

* the `syscall` instruction (`0F 05`). Compiled program text must never
  contain it: the instruction table has no system-call row (`Form.syscall` is
  outside `Form.InV0`), and Ring-0 admission refuses the opcode. So the
  system call is not a table row here either; it is a constructor of this
  separate instruction type, with its own two-byte encoding, and the table,
  its laws and its hardware-differential gate are untouched;
* direct calls of the object's exports (`cx_init`, a root's `cx_<root>`),
  which live outside the shell's own blocks. A `callExport` is a `call rel32`
  whose displacement the executable writer fills in once it has placed the
  shell and the object's text in one image. There is no indirect call.

Every other operation is an ordinary typed instruction (`X86.Instr`), checked
with the table's own validity test and encoded by the compiler's encoder
(`Encode.encodeInstr`, `Encode.encodeTerminator`), so the shell inherits the
per-row encoding laws. Runtime intrinsics (`callRuntime`) are refused: the
shell links nothing.
-/

namespace IxCC.X86.Exe.Shell

open IxCC.X86

/-- A shell operation. -/
inductive Instr where
  /-- A typed instruction of the program table (`Instr.wellFormed`; a `call`
  targets a shell block). -/
  | instr (instruction : X86.Instr)
  /-- `syscall` (`0F 05`): the kernel reads `rax` and the argument registers
  and writes `rax`, `rcx` and `r11`. -/
  | syscall
  /-- `call rel32` to the object's export named `symbol`. -/
  | callExport (symbol : String)
  deriving BEq, Repr, Inhabited

structure Block where
  instructions : Array Instr
  terminator : Terminator
  deriving BEq, Repr, Inhabited

/-- A shell: its blocks, entered at block 0. -/
structure Program where
  blocks : Array Block
  deriving BEq, Repr, Inhabited

def Program.hasBlock (p : Program) (b : BlockId) : Bool := decide (b.toNat < p.blocks.size)

/-- A shell operation is valid: a well-formed table instruction whose call
targets a shell block (no runtime intrinsic), or a named export. -/
def Instr.valid (p : Program) : Instr → Bool
  | .instr (.callRuntime _) => false
  | .instr (.call target) => p.hasBlock target
  | .instr i => i.wellFormed
  | .syscall => true
  | .callExport symbol => !symbol.isEmpty

def terminatorTargets (p : Program) : Terminator → Bool
  | .jump target | .tailCall target => p.hasBlock target
  | .branch _ _ _ ifTrue ifFalse _ => p.hasBlock ifTrue && p.hasBlock ifFalse
  | .ret => true

def Program.valid (p : Program) : Bool :=
  !p.blocks.isEmpty && decide (p.blocks.size < 2 ^ 32) &&
    p.blocks.all fun b => b.instructions.all (Instr.valid p) && b.terminator.wellFormed &&
      terminatorTargets p b.terminator

/-! ## Encoding -/

inductive Target where
  | block (target : BlockId)
  | export (symbol : String)
  deriving BEq, Repr, Inhabited

structure Fixup where
  /-- The offset of the four-byte displacement field. -/
  offset : Nat
  target : Target
  deriving BEq, Repr, Inhabited

structure Chunk where
  bytes : ByteArray
  fixups : Array Fixup
  deriving Inhabited

def Chunk.append (left right : Chunk) : Chunk :=
  { bytes := left.bytes ++ right.bytes
    fixups := left.fixups ++ right.fixups.map fun f => { f with offset := left.bytes.size + f.offset } }

/-- The compiler's chunk, with its block fixups (an intrinsic fixup cannot
occur: `Instr.valid` refuses `callRuntime`). -/
def ofEncode (c : Encode.Chunk) : Chunk :=
  { bytes := c.bytes
    fixups := c.fixups.filterMap fun f =>
      match f.target with
      | .block b => some { offset := f.offset, target := .block b }
      | .intrinsic _ => none }

/-- The bytes of `syscall`. -/
def syscallBytes : ByteArray := ⟨#[0x0f, 0x05]⟩

def encodeInstr : Instr → Chunk
  | .instr i => ofEncode (Encode.encodeInstr i)
  | .syscall => { bytes := syscallBytes, fixups := #[] }
  | .callExport symbol =>
    let bytes := Encode.encodeOp Op.callRel32 [.imm 0]
    { bytes, fixups := #[{ offset := bytes.size - 4, target := .export symbol }] }

def encodeBlock (b : Block) : Chunk :=
  (b.instructions.foldl (fun (c : Chunk) i => c.append (encodeInstr i)) ({ bytes := .empty, fixups := #[] } : Chunk)).append
    (ofEncode (Encode.encodeTerminator b.terminator))

/-- An encoded shell: its bytes with every internal displacement filled in,
the offset of each block, and the export calls still to resolve (the offset
of each call's displacement field and the export's name). -/
structure Encoded where
  text : ByteArray
  blockOffsets : Array Nat
  exportCalls : Array (Nat × String)
  deriving Inhabited

inductive Error where
  | invalid
  | displacement (offset : Nat)
  deriving BEq, Repr, Inhabited

/-- Encode a valid shell. Block displacements are filled in here; export
calls keep a zero displacement and are listed. -/
def encode (p : Program) : Except Error Encoded := do
  unless p.valid do throw .invalid
  let chunks := p.blocks.map encodeBlock
  let offsets := (chunks.foldl (fun (acc : Array Nat × Nat) c => (acc.1.push acc.2, acc.2 + c.bytes.size)) (#[], 0)).1
  let mut text := chunks.foldl (fun out c => out ++ c.bytes) ByteArray.empty
  let mut calls := #[]
  for (c, base) in chunks.zip offsets do
    for f in c.fixups do
      let pos := base + f.offset
      match f.target with
      | .export symbol => calls := calls.push (pos, symbol)
      | .block b =>
        let some target := offsets[b.toNat]? | throw .invalid
        let displacement := Int.ofNat target - Int.ofNat (pos + 4)
        unless Encode.fitsSigned32 displacement do throw (.displacement pos)
        text ← (Encode.patchSigned32 text pos displacement).mapError fun _ => .displacement pos
  return { text, blockOffsets := offsets, exportCalls := calls }

/-- The offsets of the system calls in an encoded shell, found by walking its
blocks (each `syscall` at its chunk position). -/
def syscallOffsets (p : Program) (e : Encoded) : List Nat := Id.run do
  let mut out := []
  for (b, base) in p.blocks.toList.zip e.blockOffsets.toList do
    let mut pos := base
    for i in b.instructions do
      if i == .syscall then out := out ++ [pos]
      pos := pos + (encodeInstr i).bytes.size
  return out

end IxCC.X86.Exe.Shell
