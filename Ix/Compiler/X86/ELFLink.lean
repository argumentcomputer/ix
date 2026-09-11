import Ix.Compiler.X86.ELFValidate

/-! PC32 relocation application and complete-text revalidation. Symbols are
mathematical positions relative to the text base, so negative positions are
allowed. The system linker/loader remains responsible for realizing these
positions and mapping the immutable executable text. -/

namespace Ix.Compiler.X86.ELFLink

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

abbrev Symbols := String → Option Int

def pc32 (symbol addend : Int) (position : Nat) : Int := symbol + addend - position

theorem pc32_absolute (base symbol addend : Int) (position : Nat) :
    (base + symbol) + addend - (base + position) = pc32 symbol addend position := by
  unfold pc32
  omega

theorem pc32_call (symbol : Int) (instructionOffset : Nat) :
    pc32 symbol (-4) (instructionOffset + 1) = symbol - (instructionOffset + 5 : Nat) := by
  unfold pc32
  omega

/-- A concrete trace of the actual four-byte patcher, using ELF's S+A-P
rule and rejecting signed overflow. Surrounding-byte preservation follows
from the existing `Encode.patchSigned32_splice` law at each application. -/
inductive Applied (symbols : Symbols) : List ELFRead.Relocation → ByteArray → ByteArray → Prop where
  | nil (text : ByteArray) : Applied symbols [] text text
  | cons {relocation : ELFRead.Relocation} {rest : List ELFRead.Relocation} {before middle after : ByteArray}
      (name : String) (nameBytes : name.toUTF8 = relocation.symbolName) (target : Int)
      (resolved : symbols name = some target) (kind : relocation.relocationType = 2)
      (fits : Encode.fitsSigned32 (pc32 target relocation.addend relocation.offset) = true)
      (patched : Encode.patchSigned32 before relocation.offset (pc32 target relocation.addend relocation.offset) = .ok middle)
      (remaining : Applied symbols rest middle after) : Applied symbols (relocation :: rest) before after

structure Application (symbols : Symbols) (relocations : List ELFRead.Relocation) (before : ByteArray) where
  text : ByteArray
  applied : Applied symbols relocations before text

inductive Error where
  | invalidSymbolEncoding
  | missingSymbol (name : String)
  | unsupportedRelocation (kind : Nat)
  | overflow (offset : Nat) (value : Int)
  | patch (error : Encode.Error)
  | invalidObject
  | invalidLinkedStream
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def symbolName (bytes : ByteArray) : Option String := String.fromUTF8? bytes

/-- UTF-8 decoding is checked by round trip before its name is used for
resolution. Thus no malformed byte string can alias a replacement character. -/
def apply (symbols : Symbols) (relocations : List ELFRead.Relocation) (before : ByteArray) :
    Except Error (Application symbols relocations before) :=
  match relocations with
  | [] => .ok ⟨before, .nil before⟩
  | relocation :: rest => do
      let some name := symbolName relocation.symbolName | throw .invalidSymbolEncoding
      if nameBytes : name.toUTF8 = relocation.symbolName then
        if kind : relocation.relocationType = 2 then
          match resolved : symbols name with
          | none => throw (.missingSymbol name)
          | some target =>
              let value := pc32 target relocation.addend relocation.offset
              if fits : Encode.fitsSigned32 value = true then
                match patched : Encode.patchSigned32 before relocation.offset value with
                | .error error => throw (.patch error)
                | .ok middle =>
                    let after ← apply symbols rest middle
                    return ⟨after.text, .cons name nameBytes target resolved kind fits patched after.applied⟩
              else throw (.overflow relocation.offset value)
        else throw (.unsupportedRelocation relocation.relocationType)
      else throw .invalidSymbolEncoding

def targets (symbols : Symbols) : Stream.ExternalTargets := fun intrinsic => symbols (Encode.intrinsicSymbol intrinsic)

theorem _root_.Ix.Compiler.X86.ELF.Valid.fields_of_parse {input : ELF.Input} {bytes : ByteArray}
    (valid : ELF.Valid input bytes) {view : ELFRead.View} (parsed : ELFRead.parse bytes = some view) :
    ELF.Fields input bytes view := by
  obtain ⟨original, originalParse, fields⟩ := valid
  rw [parsed] at originalParse
  cases Option.some.inj originalParse
  exact fields

structure Linked (checked : Checked) (input : ELF.Input) (bytes : ByteArray) (symbols : Symbols) where
  view : ELFRead.View
  parsed : ELFRead.parse bytes = some view
  fields : ELF.Fields input bytes view
  output : Encode.Output
  valid : Stream.Valid checked.program output (targets symbols)
  applied : Applied symbols view.relocations.toList input.encoded.text output.text

def resolve (checked : Checked) (input : ELF.Input) (object : ELF.Certified input) (symbols : Symbols) :
    Except Error (Linked checked input object.bytes symbols) := do
  match parsed : ELFRead.parse object.bytes with
  | none => throw .invalidObject
  | some view =>
      let linked ← apply symbols view.relocations.toList input.encoded.text
      let output := { input.encoded with text := linked.text }
      if accepted : Stream.check checked.program output (targets symbols) = true then
        return ⟨view, parsed, object.valid.fields_of_parse parsed, output, Stream.check_sound accepted, linked.applied⟩
      else throw .invalidLinkedStream

theorem Applied.resolves {symbols : Symbols} {relocations : List ELFRead.Relocation} {before after : ByteArray}
    (applied : Applied symbols relocations before after) :
    ∀ relocation ∈ relocations, ∃ name target, name.toUTF8 = relocation.symbolName ∧ symbols name = some target := by
  induction applied with
  | nil => simp
  | cons name nameBytes target resolved kind fits patched remaining ih =>
      intro relocation member
      rcases List.mem_cons.mp member with equal | member
      · subst relocation
        exact ⟨name, target, nameBytes, resolved⟩
      · exact ih relocation member

def address (base : Word) (relative : Int) : Word := base + ⟨BitVec.ofInt 64 relative⟩

theorem external_resolves (base : Word) (next : Nat) (target : Int)
    (fits : Encode.fitsSigned32 (target - next) = true) :
    ByteEval.relative (base + UInt64.ofNat next) (Stream.externalDisplacement next target) = address base target := by
  apply UInt64.toBitVec_inj.mp
  simp only [ByteEval.relative, Stream.externalDisplacement, UInt64.toBitVec_add,
    UInt64.toBitVec_ofNat', Encode.signExtend32_ofInt _ fits]
  change (base.toBitVec + BitVec.ofInt 64 (next : Int)) + BitVec.ofInt 64 (target - next) =
    base.toBitVec + BitVec.ofInt 64 target
  rw [BitVec.add_assoc, ← BitVec.ofInt_add]
  congr 2
  omega

/-- A resolved runtime CALL transfers to the named external address and
stores the actual continuation RIP. Execution of that external procedure
still requires the separately ledgered runtime-body/ABI contract. -/
theorem runtime_call_transfer {checked : Checked} {output : Encode.Output} {symbols : Symbols}
    (valid : Stream.Valid checked.program output (targets symbols)) (base : Word) (state : ByteEval.State) (pc : PC)
    (atPC : Stream.AtPC checked.program base pc state.rip) {block : Block} {intrinsic : Intrinsic} {target : Int}
    (found : checked.program.blocks[pc.block.toNat]? = some block)
    (foundInstruction : block.instructions[pc.offset.toNat]? = some (.callRuntime intrinsic))
    (resolved : symbols (Encode.intrinsicSymbol intrinsic) = some target) :
    ByteEval.step output.text base state =
      match state.core.memory.write64? (state.core.readReg .rsp - 8) (state.rip + 5) with
      | .error fault => .error (.memory fault)
      | .ok memory => .ok {
          core := { state.core.setReg .rsp (state.core.readReg .rsp - 8) with memory }
          rip := address base target, flags := state.flags } := by
  have accepted := valid.instruction _ _ found _ _ foundInstruction
  simp only [Stream.instructionMatches, targets, resolved, Bool.and_eq_true, Stream.decodes, beq_iff_eq] at accepted
  have indexBound := (Array.getElem?_eq_some_iff.mp foundInstruction).1
  have rip := atPC.offset found (by omega)
  have mapped : Stream.pcOffset? checked.program pc =
      some (Stream.blockOffset checked.program pc.block.toNat + Stream.instructionOffset block pc.offset.toNat) := by
    simp [Stream.pcOffset?, found, show pc.offset.toNat ≤ block.instructions.size by omega]
  rw [Stream.step_decoded rip (Stream.AtPC.small valid.textBound mapped) accepted.2]
  have nextAddress : state.rip + 5 = base + UInt64.ofNat
      (Stream.blockOffset checked.program pc.block.toNat + Stream.instructionOffset block pc.offset.toNat + 5) := by
    simp [rip, UInt64.ofNat_add, UInt64.add_assoc]
  have resolves := external_resolves base _ target accepted.1
  have effect : ByteEval.relative (state.rip + 5)
      (Stream.externalDisplacement (Stream.blockOffset checked.program pc.block.toNat + Stream.instructionOffset block pc.offset.toNat + 5) target) =
      address base target := by rw [nextAddress]; exact resolves
  simp only [ByteEval.execute]
  cases state.core.memory.write64? (state.core.readReg .rsp - 8) (state.rip + 5) <;>
    simp [Except.mapError, effect]

end Ix.Compiler.X86.ELFLink
