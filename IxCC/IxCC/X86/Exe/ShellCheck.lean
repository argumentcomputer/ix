import IxCC.X86.Exe.Shell
import IxCC.X86.StreamSpec

/-!
# The shell's text, checked in the written file

A shell (`Shell.Program`) is encoded by the compiler's encoder and laid out
in an executable by the writer (`X86/Exe/Write.lean`). `Shell.check` reads
the written file back with the independent byte decoder (`Decode.decodeAt`)
and accepts only if, at each instruction's offset (the sum of the encoded
sizes before it, from the shell's file offset `origin`):

- a table instruction is a linear row (`Encode.linearInstruction`: no call,
  fused pair or unwind) and the file decodes to its operation, with its
  encoded length;
- an internal `call` decodes to `call rel32` whose displacement reaches the
  target block's offset;
- `syscall` is `0F 05` where the decoder decodes nothing, so no decodable
  instruction is taken for a system call;
- a call of an export decodes to `call rel32` reaching `exportAt symbol` (the
  export's file offset);
- each terminator decodes to its producer and its `jcc rel32` and `jmp rel32`
  (or `jmp`, or `ret`), every displacement reaching its block; a branch whose
  false edge falls through is refused.

It is fail closed: a file it refuses is not written (`Machine.writeChecked`).
`check_sound` gives `Valid`, the facts the shell proof executes the shell's
blocks from: with the per-row laws (`row_execution`, `execute_branch`,
`execute_jump`, `execute_call`, `execute_ret`) each instruction's effect on
the byte machine follows, for any bytes around it.
-/

set_option autoImplicit false

namespace IxCC.X86.Exe.Shell

/-- An instruction's encoded size. -/
def Instr.size : Instr → Nat
  | .instr i => (Encode.encodeInstr i).bytes.size
  | .syscall => 2
  | .callExport _ => 5

/-- A block's encoded size: its instructions and its terminator. -/
def Block.size (b : Block) : Nat :=
  (b.instructions.toList.map Instr.size).sum + (Encode.encodeTerminator b.terminator).bytes.size

/-- Where block `i` starts in the encoded shell. -/
def blockOffset (p : Program) (i : Nat) : Nat := ((p.blocks.toList.take i).map Block.size).sum

/-- Where instruction `j` starts in a block. -/
def instrOffset (b : Block) (j : Nat) : Nat := ((b.instructions.toList.take j).map Instr.size).sum

/-- A rel32 control operation at `pos` (length `len`) reaching block `t` of
the shell at `origin`. -/
def targets (p : Program) (image : ByteArray) (origin pos : Nat) (op : Imm32 → Decode.Operation)
    (len : Nat) (t : BlockId) : Bool :=
  decide (t.toNat < p.blocks.size) &&
    Encode.fitsSigned32 ((origin + blockOffset p t.toNat : Int) - (pos + len)) &&
    Stream.decodes image pos (op (Stream.displacement (pos + len) (origin + blockOffset p t.toNat))) len

/-- The file at `pos` holds the instruction. -/
def instrMatches (p : Program) (image : ByteArray) (origin : Nat) (exportAt : String → Option Nat)
    (pos : Nat) : Instr → Bool
  | .instr (.call t) => targets p image origin pos .call 5 t
  | .instr i => Encode.linearInstruction i && Stream.decodes image pos (Encode.instructionOperation i) (Instr.size (.instr i))
  | .syscall => Decode.decodeAt image pos == none && image[pos]? == some 0x0f && image[pos + 1]? == some 0x05
  | .callExport s =>
    match exportAt s with
    | some t => Encode.fitsSigned32 ((t : Int) - (pos + 5)) && Stream.decodes image pos (.call (Stream.displacement (pos + 5) t)) 5
    | none => false

/-- The file at `pos` holds the terminator. -/
def terminatorMatches (p : Program) (image : ByteArray) (origin pos : Nat) : Terminator → Bool
  | .jump t | .tailCall t => targets p image origin pos .jump 5 t
  | .ret => Stream.decodes image pos .ret 1
  | .branch producer args condition yes no .rel32 =>
    let size := (Encode.encodeOp producer args).size
    Stream.decodes image pos (.op producer args) size && targets p image origin (pos + size) (.branch condition) 6 yes &&
      targets p image origin (pos + size + 6) .jump 5 no
  | .branch _ _ _ _ _ .fall => false

/-- **The shell's text check** (fail closed; see the module note): at each
instruction of `p`, placed at file offset `origin`, the file decodes the
instruction's operation; every block target resolves; a `syscall` is `0F 05`
where the byte decoder decodes nothing; an export call lands on its export
(`exportAt`, a file offset). -/
def check (p : Program) (image : ByteArray) (origin : Nat) (exportAt : String → Option Nat) : Bool :=
  (List.range p.blocks.size).all fun b =>
    match p.blocks[b]? with
    | none => false
    | some blk =>
      (List.range blk.instructions.size).all (fun j =>
        match blk.instructions[j]? with
        | none => false
        | some i => instrMatches p image origin exportAt (origin + blockOffset p b + instrOffset blk j) i) &&
      terminatorMatches p image origin (origin + blockOffset p b + instrOffset blk blk.instructions.size) blk.terminator

/-- What the check establishes: every instruction and terminator of every
block is in the file where the encoder put it. -/
structure Valid (p : Program) (image : ByteArray) (origin : Nat) (exportAt : String → Option Nat) : Prop where
  instr : ∀ b blk, p.blocks[b]? = some blk → ∀ j i, blk.instructions[j]? = some i →
    instrMatches p image origin exportAt (origin + blockOffset p b + instrOffset blk j) i = true
  term : ∀ b blk, p.blocks[b]? = some blk →
    terminatorMatches p image origin (origin + blockOffset p b + instrOffset blk blk.instructions.size) blk.terminator = true

/-- **The check is sound**: what it accepts is `Valid`. -/
theorem check_sound {p : Program} {image : ByteArray} {origin : Nat} {exportAt : String → Option Nat}
    (h : check p image origin exportAt = true) : Valid p image origin exportAt := by
  unfold check at h
  rw [List.all_eq_true] at h
  constructor
  · intro b blk hb j i hi
    have hb' := h b (List.mem_range.2 (Array.getElem?_eq_some_iff.1 hb).1)
    simp only [hb, Bool.and_eq_true, List.all_eq_true] at hb'
    have hj := hb'.1 j (List.mem_range.2 (Array.getElem?_eq_some_iff.1 hi).1)
    simp only [hi] at hj
    exact hj
  · intro b blk hb
    have hb' := h b (List.mem_range.2 (Array.getElem?_eq_some_iff.1 hb).1)
    simp only [hb, Bool.and_eq_true] at hb'
    exact hb'.2

end IxCC.X86.Exe.Shell
