import Compilatrix.X86.Eval
import Compilatrix.X86.ByteEval

/-!
# Running typed x86 and the byte machine on long programs

`X86.Memory` is a closure: every byte write wraps the previous memory, so
reading after `n` writes costs `n` calls and a run of `n` steps costs
`O(n²)`. The runners here keep the written bytes in a hash map instead:
before each step they compute the step's write footprint from the
instruction about to run (`Op.writes`, a call's return slot), and after it
they copy those bytes out of the new memory, which is only a few closures
deep, and rebuild the memory over the map. The permissions never change.
This is test code: the steps themselves are `X86.step` and
`ByteEval.step`, unchanged.
-/

namespace CompilatrixTests.Backend

open Compilatrix

abbrev Word := X86.Word

/-- A base memory overlaid with the bytes written so far. -/
structure Shadow where
  base : X86.Memory
  written : Std.HashMap Word UInt8 := {}

def Shadow.memory (s : Shadow) : X86.Memory :=
  let written := s.written
  let base := s.base
  { base with bytes := fun a => (written.get? a).getD (base.bytes a) }

/-- Copy the bytes `accesses` cover out of `after`. -/
def Shadow.absorb (s : Shadow) (after : X86.Memory) (accesses : List X86.Access) : Shadow :=
  { s with written := accesses.foldl (init := s.written) fun w a =>
      (List.range a.bytes).foldl (init := w) fun w j =>
        let address := a.address + UInt64.ofNat j
        w.insert address (after.bytes address) }

def Shadow.read64 (s : Shadow) (address : Word) : Word := s.memory.read64 address

/-- The bytes the typed machine's next step may write. -/
def typedWrites (checked : X86.Checked) (m : X86.Machine) : List X86.Access :=
  match checked.program.blocks[m.pc.block.toNat]? with
  | none => []
  | some b =>
      match b.instructions[m.pc.offset.toNat]? with
      | some (.op o args) => o.writes args m.core
      | some (.fused p pargs c cargs) => p.writes pargs m.core ++ c.writes cargs m.core
      | some (.call _) => [⟨m.core.readReg .rsp - 8, 8⟩]
      | some _ => []
      | none =>
          match b.terminator with
          | .branch p args .. => p.writes args m.core
          | _ => []

structure TypedRun where
  machine : X86.Machine
  steps : Nat
  shadow : Shadow

/-- Run the typed machine from `core` (whose memory is `shadow.memory`) for
at most `fuel` steps. -/
def runTyped (checked : X86.Checked) (core : X86.Core) (shadow : Shadow) (fuel : Nat) : TypedRun :=
  go fuel (X86.Machine.initial checked { core with memory := shadow.memory }) shadow 0
where
  go : Nat → X86.Machine → Shadow → Nat → TypedRun
    | 0, m, s, n => ⟨m, n, s⟩
    | fuel + 1, m, s, n =>
        if m.status != .running then ⟨m, n, s⟩
        else
          let writes := typedWrites checked m
          let m' := X86.step X86.Runtime.rejecting checked m
          let s := s.absorb m'.core.memory writes
          go fuel { m' with core := { m'.core with memory := s.memory } } s (n + 1)

/-- The bytes the byte machine's next step may write. -/
def byteWrites (text : ByteArray) (base : Word) (st : X86.ByteEval.State) : List X86.Access :=
  match X86.Decode.decodeAt text (st.rip - base).toNat with
  | some ⟨.op o args, _⟩ =>
      match o.mn with
      | .call => [⟨st.core.readReg .rsp - 8, 8⟩]
      | .jmp | .jcc _ | .ret => []
      | _ => o.writes args st.core
  | none => []

structure ByteRun where
  /-- The final state, or the fault. -/
  result : Except X86.ByteEval.Fault X86.ByteEval.State
  steps : Nat
  shadow : Shadow

/-- Run the byte machine from `rip` until it reaches `stop`, faults, or
runs out of fuel. -/
def runBytes (text : ByteArray) (base : Word) (st : X86.ByteEval.State) (shadow : Shadow) (stop : Word)
    (fuel : Nat) : ByteRun :=
  go fuel { st with core := { st.core with memory := shadow.memory } } shadow 0
where
  go : Nat → X86.ByteEval.State → Shadow → Nat → ByteRun
    | 0, st, s, n => ⟨.ok st, n, s⟩
    | fuel + 1, st, s, n =>
        if st.rip == stop then ⟨.ok st, n, s⟩
        else
          let writes := byteWrites text base st
          match X86.ByteEval.step text base st with
          | .error e => ⟨.error e, n, s⟩
          | .ok st' =>
              let s := s.absorb st'.core.memory writes
              go fuel { st' with core := { st'.core with memory := s.memory } } s (n + 1)

end CompilatrixTests.Backend
