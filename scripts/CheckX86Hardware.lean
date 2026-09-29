import Compilatrix.Tools.Check
import Compilatrix.X86.ByteEval
import Compilatrix.X86.Encode

/-! Hardware-differential gate for the local x86 byte model.

Every case is real encoder output. The native harness
(`fixtures/x86/hw_diff_harness.c`) runs it on the host CPU from fixed
registers, flags and pattern-filled pages; `ByteEval` runs the same bytes from
the same state. The gate compares:
- the exit (fall-through or taken);
- all sixteen registers;
- every flag the model defines;
- every changed page byte;
- memory faults.

This tests, rather than proves, that the local model agrees with the
processor; the trust ledger records it as such. -/

open Compilatrix Compilatrix.X86 Compilatrix.Tools.Check

namespace CheckX86Hardware

def testAddress : Word := 0x40000800
def takenAddress : Word := 0x40000c00
def dataPage : Word := 0x40100000
def stackPage : Word := 0x40200000
def pageSize : Word := 4096
def stackTop : Word := stackPage + 0x800

/-- The harness's deterministic page contents. -/
def pattern (seed address : Word) : UInt8 :=
  let x := seed ^^^ (address * 0x9e3779b97f4a7c15)
  let x := x ^^^ (x >>> 29)
  let x := x * 0xbf58476d1ce4e5b9
  let x := x ^^^ (x >>> 32)
  x.toUInt8

def mapped (address : Word) : Bool :=
  (dataPage ≤ address && address < dataPage + pageSize) ||
    (stackPage ≤ address && address < stackPage + pageSize)

def registerOrder : Array GPR :=
  #[.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
    .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

structure Case where
  id : String
  code : ByteArray
  registers : Array Word
  /-- Input flags as the harness bits: 0 CF, 6 ZF, 7 SF, 11 OF. -/
  flags : Word
  seed : Word
  /-- Whether the case can write memory, so the model scans both pages. -/
  writes : Bool := false

def Case.line (c : Case) : String :=
  let hexWord (w : Word) := hexNat w.toNat
  let code := c.code.data.foldl (fun s b => s ++ (if b.toNat < 16 then "0" else "") ++ hexNat b.toNat) ""
  " ".intercalate ([c.id, code] ++ c.registers.toList.map hexWord ++ [hexWord c.flags, hexWord c.seed])

def bit (flags : Word) (index : Nat) : Bool := (flags >>> UInt64.ofNat index) &&& 1 == 1

def Case.initial (c : Case) : ByteEval.State :=
  { core := {
      registers := fun register =>
        match registerOrder.findIdx? (· == register) with
        | some i => c.registers[i]!
        | none => 0
      memory := {
        bytes := pattern c.seed
        readable := mapped
        writable := mapped } }
    rip := testAddress
    flags := {
      carry := some (bit c.flags 0), zero := some (bit c.flags 6),
      sign := some (bit c.flags 7), overflow := some (bit c.flags 11) } }

/-- Observations: `none` for a memory fault; otherwise exit, registers,
the four modeled flags, and changed bytes (address, value). -/
structure Observed where
  exit : Nat
  registers : Array Word
  flags : ByteEval.Flags
  changed : Array (Word × UInt8)

def pageBytes : Array Word :=
  (Array.range pageSize.toNat).map (dataPage + ·.toUInt64) ++
    (Array.range pageSize.toNat).map (stackPage + ·.toUInt64)

/-- Run the model over the case bytes until control leaves them. -/
def model (c : Case) : Except String (Option Observed) := do
  let finish := testAddress + c.code.size.toUInt64
  let rec loop : Nat → ByteEval.State → Except String (Option Observed)
    | 0, _ => throw "model did not leave the case bytes"
    | fuel + 1, state =>
      if state.rip == finish || state.rip == takenAddress then
        let changed := if c.writes then
            pageBytes.filterMap fun a =>
              let v := state.core.memory.bytes a
              if v != pattern c.seed a then some (a, v) else none
          else #[]
        pure (some {
          exit := if state.rip == takenAddress then 1 else 0
          registers := registerOrder.map state.core.readReg
          flags := state.flags
          changed })
      else if state.rip < testAddress || finish < state.rip then
        throw s!"model left the case window at {hexNat state.rip.toNat}"
      else
        match ByteEval.step c.code testAddress state with
        | .ok next => loop fuel next
        | .error (.memory _) => pure none
        | .error fault => throw s!"model fault {repr fault}"
  loop 8 c.initial

/-- Parse one harness output line. -/
def parseNative (line : String) : Except String (String × Option (Nat × Array Word × Word × Array (Word × UInt8))) := do
  let parts := line.splitOn " " |>.filter (· != "")
  match parts with
  | id :: "fault" :: _ => return (id, none)
  | id :: "ok" :: exit :: rest =>
    let hex (s : String) : Except String Word := do
      let bytes ← unhex (if s.length % 2 == 1 then "0" ++ s else s)
      return bytes.data.foldl (fun acc b => (acc <<< 8) ||| b.toUInt64) 0
    let registers ← (rest.take 16).mapM hex
    let flags ← hex (rest.getD 16 "0")
    let changed ← (rest.drop 18).mapM fun pair => do
      let [address, value] := pair.splitOn "=" | throw s!"bad byte {pair}"
      return (← hex address, (← hex value).toUInt8)
    return (id, some (exit.toNat!, registers.toArray, flags, changed.toArray))
  | _ => throw s!"unparsed harness line: {line}"

/-- Compare one case; the result is the list of differences. -/
def compare (c : Case) (native : Option (Nat × Array Word × Word × Array (Word × UInt8))) :
    Except String (List String) := do
  let expected ← model c
  match expected, native with
  | none, none => return []
  | none, some _ => return ["model faults, processor does not"]
  | some _, none => return ["processor faults, model does not"]
  | some m, some (exit, registers, flags, changed) =>
    let mut errors := []
    if m.exit != exit then errors := s!"exit model {m.exit} native {exit}" :: errors
    for i in [:16] do
      if m.registers[i]! != registers[i]! then
        errors := s!"{repr registerOrder[i]!}: model {hexNat m.registers[i]!.toNat} native {hexNat registers[i]!.toNat}" :: errors
    let check (label : String) (value : Option Bool) (index : Nat) : List String :=
      match value with
      | some v => if v != bit flags index then [s!"flag {label}: model {v}"] else []
      | none => []
    errors := errors ++ check "CF" m.flags.carry 0 ++ check "ZF" m.flags.zero 6 ++
      check "SF" m.flags.sign 7 ++ check "OF" m.flags.overflow 11
    if c.writes && m.changed != changed then
      errors := s!"memory: model {m.changed.size} changed bytes, native {changed.size}" :: errors
    if !c.writes && !changed.isEmpty then
      errors := s!"unexpected native memory writes: {changed.size}" :: errors
    return errors

/-! ## Case generation: every table row

Cases enumerate `Op.rows` (note 05 §8.7). For each linear row, every
operand slot runs through its kinds: registers (low, extended, and the
byte-register REX codes SPL–DIL), addresses covering the SIB holes
(`rsp`/`r12` bases), the displacement holes (`rbp`/`r13`), absolute
addressing, no/disp8/disp32 displacements and indexed forms, and immediates
at the edges of their kind. Other slots rotate through their choices. Each
row also gets an unmapped-address fault case per memory slot. Control rows
run natively as `cmp`/`jcc`, `jmp`, `call` and `push`/`ret` recipes. -/

def edges : Array Word :=
  #[0, 1, 2, 0x7f, 0x80, 0xff, 0x100, 0x7fff, 0x8000, 0xffff, 0x7fffffff, 0x80000000,
    0xffffffff, 0x100000000, 0x7fffffffffffffff, 0x8000000000000000,
    0xfffffffffffffffe, 0xffffffffffffffff]

/-- Deterministic xorshift stream. -/
def next (state : Word) : Word :=
  let x := state ^^^ (state <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

def gprs : Array GPR := registerOrder

/-- Registers for case `n`: edge or random values, `rsp` inside the stack page. -/
def registersFor (n : Nat) : Array Word := Id.run do
  let mut state : Word := 0x243f6a8885a308d3 + n.toUInt64 * 0x13198a2e03707344
  let mut out := #[]
  for i in [:16] do
    state := next state
    let value := if state % 3 == 0 then edges[(state >>> 8).toNat % edges.size]! else next state
    out := out.push (if i == 4 then stackTop else value)
  return out

def conditions : Array Condition := Condition.all.toArray

def registerIndex (register : GPR) : Nat := (registerOrder.findIdx? (· == register)).getD 0

/-- Register-slot choices: low and extended registers, and codes 4–7, which
are SPL–DIL (with REX) in byte rows. -/
def registerChoices : Array GPR :=
  #[.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r12, .r13, .r15]

/-- Displacements: none, ±1, the disp8 edges (127, −128), the first disp32
values (128, −129, 256) and the disp32 extremes (2³¹ − 1, −2³¹). -/
def displacements : Array Imm32 :=
  #[0, 1, 0xffffffff, 0x7f, 0xffffff80, 0x80, 0xffffff7f, 0x100, 0x7fffffff, 0x80000000]

/-- The disp32 extremes, which only a compensating base can bring back into
the mapped window. -/
def extremeDisplacement (displacement : Imm32) : Bool :=
  displacement == 0x7fffffff || displacement == 0x80000000

/-- A disp32 sign-extended to 64 bits, as address generation uses it. -/
def signExtend32 (displacement : Imm32) : Word :=
  (displacement.toUInt64 ^^^ 0x80000000) - 0x80000000

def bases : Array (Option GPR) :=
  #[none, some .rax, some .rbx, some .rbp, some .rsp, some .r12, some .r13, some .r15]

def indexChoices : Array (Option IndexReg) := #[none, some .rcx, some .r14]

def scales : Array Scale := #[.one, .two, .four, .eight]

/-- Where a based address points: the data page, or the stack page for `rsp`. -/
def baseValue (base : GPR) : Word := if base == .rsp then stackTop else dataPage + 0x400

/-- Every address shape, pointing into a mapped page once its registers are
placed. An absolute address carries the data page in its displacement, so it
skips the disp32 extremes. -/
def addresses : Array MemAddr := Id.run do
  let mut out := #[]
  for base in bases do
    for index in indexChoices do
      for displacement in displacements do
        if base.isNone && extremeDisplacement displacement then continue
        let scale := scales[out.size % scales.size]!
        let displacement := if base.isNone then (dataPage + 0x400).toUInt32 + displacement else displacement
        out := out.push ({ base, index, scale, displacement } : MemAddr).normalize
  return out

/-- Point the address's registers into the mapped window. A base under a
disp32 extreme is offset by the displacement, except `rsp`, which stays the
stack pointer, so those cases fault on both machines. -/
def placeAddress (registers : Array Word) (address : MemAddr) (n : Nat) : Array Word :=
  let registers := match address.base with
    | some base =>
      let value := if extremeDisplacement address.displacement && base != .rsp
        then baseValue base - signExtend32 address.displacement else baseValue base
      registers.set! (registerIndex base) value
    | none => registers
  match address.index with
  | some index => registers.set! (registerIndex index.gpr) (n.toUInt64 % 16)
  | none => registers

def normFor : ArgKind → Word → Word
  | .imm8 => ImmKind.imm8.norm
  | .imm16 => ImmKind.imm16.norm
  | .imm32 | .rel32 => ImmKind.imm32.norm
  | _ => id

/-- Immediates at the edges of the slot's kind, in canonical form. -/
def immediates (kind : ArgKind) : Array Word :=
  let raw : List Word := [0, 1, 0xffffffffffffffff, 0x7f, 0x80, 0xffffffffffffff80, 0xff, 0x7fff,
    0x8000, 0x7fffffff, 0xffffffff80000000, 0xffffffff, 0x100000000, 0x12345678, 0xfedcba9876543210]
  (raw.map (normFor kind)).eraseDups.toArray

def slotChoices (slot : Slot) : Array Arg :=
  slot.kinds.foldl (init := #[]) fun out kind =>
    out ++ match kind with
      | .reg => registerChoices.map Arg.reg
      | .mem => addresses.map Arg.mem
      | kind => (immediates kind).map Arg.imm

/-- Operand lists for a row: the longest slot runs through all its choices,
the others rotate through theirs. -/
def argumentSets (slots : List Slot) : Array (List Arg) := Id.run do
  let choices := slots.map slotChoices
  let count := choices.foldl (fun best c => max best c.size) 0
  let mut out := #[]
  for i in [:count] do
    let (args, _) := choices.foldl (init := (([] : List Arg), 0)) fun (args, k) c =>
      (args ++ [c[(i * (2 * k + 1) + 3 * k) % c.size]!], k + 1)
    out := out.push args
  return out

def rel32 (opcode : List UInt8) (after : Word) : ByteArray :=
  Encode.bytes opcode ++ Encode.imm32Bytes (takenAddress - after).toUInt32

/-- A case for one row applied to its operands. Its memory footprint (from
the table) decides whether the model scans the pages for writes. -/
def rowCase (id : String) (n : Nat) (o : Op) (args : List Arg) (base : Array Word) (place : Bool := true) : Case :=
  let registers := args.foldl (fun registers arg =>
    match arg with
    | .mem address => if place then placeAddress registers address n else registers
    | _ => registers) base
  let c : Case :=
    { id := s!"{id}.{n}"
      code := Encode.encodeOp o args
      registers
      -- Input flags: all clear, all set (OF, SF, ZF, CF), or random.
      flags := match n % 4 with
        | 0 => 0
        | 1 => 0x8c1
        | _ => (next (n.toUInt64 + 7)) &&& 0x8c1
      seed := n.toUInt64 * 0x9e37 + 11 }
  { c with writes := !(o.writes args c.initial.core).isEmpty }

def controlCase (id : String) (n : Nat) (code : ByteArray) (flags : Word) (writes : Bool) : Case :=
  { id
    code
    registers := registersFor n
    flags
    seed := n.toUInt64
    writes }

def formName : OpEn → String
  | .MR => "MR" | .RM => "RM" | .MI => "MI" | .MI8 => "MI8" | .OI => "OI" | .O => "O"
  | .RMI => "RMI" | .RMI8 => "RMI8" | .D32 => "D32" | .ZO => "ZO"

def rowName (o : Op) : String :=
  s!"{(desc o).mnemonic}-{formName o.form}-{o.w.bits}" ++ (if o.src != o.w then s!"-{o.src.bits}" else "")

/-- All generated cases. -/
def cases : Array Case := Id.run do
  let mut out : Array Case := #[]
  let mut n := 0
  for o in Op.rows.filter (·.linear) do
    let slots := (desc o).slots
    for args in argumentSets slots do
      if o.argsOk args then
        n := n + 1
        out := out.push (rowCase (rowName o) n o args (registersFor n))
    -- An unmapped address in each memory-capable slot faults on both machines.
    for position in [:slots.length] do
      if (slots[position]!.kinds.contains .mem) then
        n := n + 1
        let unmapped : MemAddr := { base := some .rbx }
        let args := (argumentSets slots)[0]!.set position (.mem unmapped)
        if o.argsOk args then
          let registers := (registersFor n).set! (registerIndex .rbx) 0x40300000
          out := out.push (rowCase (rowName o ++ "-fault") n o args registers (place := false))
  -- Compare-and-branch: every condition after every register/immediate `cmp` row.
  let compareRows := Op.rows.filter fun o => o.mn == .cmp
  for c in conditions do
    for o in compareRows do
      for args in (argumentSets (desc o).slots).toList.take 6 do
        let isMemory := args.any fun | .mem _ => true | _ => false
        if o.argsOk args && !isMemory then
          n := n + 1
          let producer := Encode.encodeOp o args
          let after := testAddress + producer.size.toUInt64 + 6
          let compared := rowCase (s!"cmp-j{c.suffix}-" ++ rowName o) n o args (registersFor n)
          out := out.push { compared with
            code := producer ++ rel32 [0x0f, (desc (Op.jccRel32 c)).enc.opcode] after }
  -- Unconditional control rows.
  n := n + 1
  out := out.push (controlCase s!"jmp.{n}" n (rel32 [(desc Op.jmpRel32).enc.opcode] (testAddress + 5)) 0x8c1 false)
  n := n + 1
  out := out.push (controlCase s!"call.{n}" n (rel32 [(desc Op.callRel32).enc.opcode] (testAddress + 5)) 0 true)
  n := n + 1
  let returning := (Encode.encodeInstr (.mov .w64 .r11 (.imm takenAddress))).bytes ++
    (Encode.encodeInstr (.push .r11)).bytes ++ Encode.encodeOp Op.retZO []
  out := out.push (controlCase s!"ret.{n}" n returning 0x41 true)
  return out

/-! ## Independent decoding with LLVM

Every case is decoded by `llvm-mc --show-encoding`, with a `ud2` separator
between cases. Each case must produce exactly the instruction sequence the
local decoder sees: the same number of instructions, the same bytes for
each (so lengths and boundaries agree), each row's `desc` mnemonic, and no
invalid encodings. -/

/-- LLVM prints a relative branch's rel32 field as a zero fixup, so control
rows compare their length and opcode bytes; every other row compares all
its bytes. -/
def sameEncoding (operation : Decode.Operation) (bytes llvmBytes : List UInt8) : Bool :=
  match operation with
  | .op o _ =>
      if (desc o).slots.any (·.kinds.contains .rel32) then
        bytes.length == llvmBytes.length && bytes.take (bytes.length - 4) == llvmBytes.take (bytes.length - 4)
      else bytes == llvmBytes

/-- The mnemonic LLVM prints for a decoded row. -/
def mnemonic : Decode.Operation → String
  | .op o _ => (desc o).mnemonic

/-- The local decoder's operations and their bytes for a case. -/
def localOperations (code : ByteArray) : Except String (List (Decode.Operation × List UInt8)) := do
  let rec go : Nat → List UInt8 → Except String (List (Decode.Operation × List UInt8))
    | _, [] => pure []
    | 0, _ => throw "too many operations"
    | fuel + 1, input => do
      let some (operation, rest) := Decode.one input | throw "local decoder rejected case bytes"
      return (operation, input.take (input.length - rest.length)) :: (← go fuel rest)
  go 8 code.data.toList

def llvmInput (c : Case) : String :=
  " ".intercalate (c.code.data.toList.map fun b => s!"0x{hexNat b.toNat}") ++ "\n0x0f 0x0b\n"

/-- One disassembled instruction: its mnemonic and encoding bytes. -/
def llvmLine (line : String) : Option (String × List UInt8) := do
  let text := line.trimAscii.toString
  if text.isEmpty || text.startsWith "." then none
  let name ← ((text.splitOn "\t").filter (· != "")).head?
  let name := (name.splitOn " ").headD name
  let [_, encoded] := text.splitOn "encoding: [" | none
  let encoded := (encoded.splitOn "]").headD ""
  let bytes := (encoded.splitOn ",").filterMap fun field =>
    let digits := (field.trimAscii.toString.drop 2).toString
    (digits.toList.foldl (fun acc c => acc.bind fun value =>
      if c.isDigit then some (value * 16 + (c.toNat - '0'.toNat))
      else if 'a' ≤ c && c ≤ 'f' then some (value * 16 + (c.toNat - 'a'.toNat + 10))
      else none) (some 0)).map UInt8.ofNat
  return (name, bytes)

/-- Decode every case with `llvm-mc` and compare mnemonics and encodings. -/
def checkLlvm (llvmMc : String) : IO Nat := do
  let input := String.join (cases.toList.map llvmInput)
  let output ← IO.FS.withTempFile fun handle path => do
    handle.putStr input
    handle.flush
    IO.Process.output { cmd := llvmMc, args := #["--disassemble", "-triple=x86_64",
      "-output-asm-variant=1", "--show-encoding", path.toString] }
  need (output.exitCode == 0 && !output.stderr.contains "invalid")
    s!"llvm-mc rejected an encoding: {output.stderr.take 400}"
  let decoded := (output.stdout.splitOn "\n").filterMap llvmLine
  let groups := (decoded.foldl (init := (([] : List (List (String × List UInt8))), ([] : List (String × List UInt8))))
    fun (done, current) instruction =>
      if instruction.1 == "ud2" then (current.reverse :: done, []) else (done, instruction :: current)).1.reverse
    |>.filter (!·.isEmpty)
  need (groups.length == cases.size) s!"llvm-mc produced {groups.length} of {cases.size} cases"
  for (c, group) in cases.toList.zip groups do
    let expected ← checked (localOperations c.code)
    need (expected.length == group.length &&
        (expected.zip group).all fun ((operation, bytes), (name, llvmBytes)) =>
          mnemonic operation == name && sameEncoding operation bytes llvmBytes)
      s!"{c.id}: llvm-mc decodes {group}, local decoder {expected.map fun (operation, bytes) => (mnemonic operation, bytes)}"
  return cases.size

end CheckX86Hardware

open CheckX86Hardware in
def main (args : List String) : IO UInt32 := cli "x86 hardware-differential check failed" do
  let args ← checked (parseArgs ["--harness", "--llvm-mc"] args)
  let some harness := optional args "--harness"
    | throw (IO.userError "usage: check-x86-hardware --harness PATH (a compiled hw_diff_harness)")
  let input := String.intercalate "\n" (cases.toList.map Case.line) ++ "\n"
  let output ← IO.FS.withTempFile fun handle path => do
    handle.putStr input
    handle.flush
    IO.Process.output { cmd := "sh", args := #["-c", "exec \"$0\" < \"$1\"", harness, path.toString] }
  need (output.exitCode == 0) s!"harness exited with {output.exitCode}: {output.stderr}"
  let text := output.stdout
  let lines := (text.splitOn "\n").filter (· != "")
  need (lines.headD "" == "layout 40000800 40000c00 40100000 40200000")
    s!"harness layout differs: {lines.headD ""}"
  let results := lines.drop 1
  need (results.length == cases.size) s!"harness returned {results.length} of {cases.size} cases"
  let mut failures := 0
  let mut faults := 0
  for (c, line) in cases.toList.zip results do
    let (id, native) ← checked (parseNative line)
    need (id == c.id) s!"harness order: expected {c.id}, got {id}"
    if native.isNone then faults := faults + 1
    let errors ← checked (compare c native)
    unless errors.isEmpty do
      failures := failures + 1
      if failures ≤ 20 then IO.eprintln s!"{c.id} [{c.line}]: {errors}"
  need (failures == 0) s!"{failures} of {cases.size} cases disagree with the processor"
  let decoded ← match optional args "--llvm-mc" with
    | some llvmMc => pure s!"; llvm-mc decodes all {← checkLlvm llvmMc} identically"
    | none => pure ""
  IO.println s!"x86 hardware-differential check ok: {cases.size} cases ({faults} expected faults) agree with the host processor{decoded}"
